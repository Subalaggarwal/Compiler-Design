import sys
from collections import OrderedDict

try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass

EPS = "ε"
EPS_ALIASES = {"#", "eps", "epsilon", "ε", "@"}


# ----------------------------------------------------------------------------
# Grammar input / output helpers
# ----------------------------------------------------------------------------
def split_symbols(text, nts):
    """Split one alternative (right-hand side) into grammar symbols."""
    syms = []
    for chunk in text.split():
        if chunk in EPS_ALIASES:
            continue
        i = 0
        while i < len(chunk):
            match = max((n for n in nts if chunk.startswith(n, i)), key=len, default=None)
            if match:
                syms.append(match)
                i += len(match)
            elif chunk.startswith("id", i):
                syms.append("id")
                i += 2
            else:
                syms.append(chunk[i])
                i += 1
    return syms


def collect_terms(prods, nts):
    terms = []
    for _, rhs in prods:
        for s in rhs:
            if s not in nts and s not in terms:
                terms.append(s)
    return terms


def parse_grammar(lines):
    raw = []
    for line in lines:
        line = line.replace("→", "->")
        if "->" not in line:
            raise ValueError(f"missing '->' in: {line}")
        lhs, rhs = line.split("->", 1)
        lhs = lhs.strip()
        if not lhs or " " in lhs:
            raise ValueError(f"bad left-hand side in: {line}")
        raw.append((lhs, rhs))
    if not raw:
        raise ValueError("empty grammar")
    nts = []
    for lhs, _ in raw:
        if lhs not in nts:
            nts.append(lhs)
    prods = []
    for lhs, rhs in raw:
        for alt in rhs.split("|"):
            p = (lhs, tuple(split_symbols(alt, nts)))
            if p not in prods:
                prods.append(p)
    return nts, collect_terms(prods, nts), prods, nts[0]


def read_grammar():
    print("Enter the grammar, one production per line (blank line to finish).")
    print("  Example :  E -> E + T | T        (use # for epsilon)")
    print("  First production's LHS = start symbol.")
    lines = []
    while True:
        try:
            line = input("  ").strip()
        except EOFError:
            break
        if not line:
            if lines:
                break
            continue
        lines.append(line)
    return parse_grammar(lines)


def rhs_str(rhs):
    return " ".join(rhs) if rhs else EPS


def show_grammar(prods):
    for i, (lhs, rhs) in enumerate(prods):
        print(f"  ({i}) {lhs} -> {rhs_str(rhs)}")


def fmt_set(s):
    return "{ " + ", ".join(sorted(s)) + " }"


# ----------------------------------------------------------------------------
# FIRST / FOLLOW
# ----------------------------------------------------------------------------
def first_of_seq(seq, first):
    res = set()
    for s in seq:
        if s in first:                       # non-terminal
            res |= first[s] - {EPS}
            if EPS not in first[s]:
                return res
        else:                                # terminal
            res.add(s)
            return res
    res.add(EPS)
    return res


def compute_first(nts, prods):
    first = {n: set() for n in nts}
    changed = True
    while changed:
        changed = False
        for lhs, rhs in prods:
            f = first_of_seq(rhs, first)
            if not f <= first[lhs]:
                first[lhs] |= f
                changed = True
    return first


def compute_follow(nts, prods, first, start):
    follow = {n: set() for n in nts}
    follow[start].add("$")
    changed = True
    while changed:
        changed = False
        for lhs, rhs in prods:
            for i, s in enumerate(rhs):
                if s in follow:
                    f = first_of_seq(rhs[i + 1:], first)
                    add = f - {EPS}
                    if EPS in f:
                        add |= follow[lhs]
                    if not add <= follow[s]:
                        follow[s] |= add
                        changed = True
    return follow


# ----------------------------------------------------------------------------
# Printing helpers
# ----------------------------------------------------------------------------
def print_table(rows, cols, cell, corner=""):
    grid = {(r, c): cell(r, c) for r in rows for c in cols}
    w0 = max([len(corner)] + [len(str(r)) for r in rows])
    w = {c: max([len(str(c))] + [len(grid[(r, c)]) for r in rows]) for c in cols}
    header = corner.ljust(w0) + " | " + " | ".join(str(c).center(w[c]) for c in cols)
    print(header)
    print("-" * len(header))
    for r in rows:
        print(str(r).ljust(w0) + " | " + " | ".join(grid[(r, c)].center(w[c]) for c in cols))


def print_trace(rows, headers=("Stack", "Input", "Action")):
    w = [max(len(h), max(len(r[i]) for r in rows)) for i, h in enumerate(headers)]
    line = " | ".join(h.ljust(w[i]) for i, h in enumerate(headers))
    print(line)
    print("-" * len(line))
    for r in rows:
        print(" | ".join(r[i].ljust(w[i]) for i in range(len(headers))))


def tokenize_input(s, terms):
    toks, i = [], 0
    ordered = sorted(terms, key=len, reverse=True)
    while i < len(s):
        if s[i].isspace():
            i += 1
            continue
        for t in ordered:
            if s.startswith(t, i):
                toks.append(t)
                i += len(t)
                break
        else:
            raise ValueError(f"unknown symbol '{s[i]}' at position {i} (not a terminal of the grammar)")
    return toks + ["$"]


def input_loop(terms, parse_fn):
    while True:
        try:
            s = input("\nEnter input string (q to quit): ")
        except EOFError:
            break
        if s.strip().lower() in ("q", "quit", "exit"):
            break
        try:
            tokens = tokenize_input(s, terms)
        except ValueError as e:
            print("  Error:", e)
            continue
        parse_fn(tokens)


# ----------------------------------------------------------------------------
# Grammar transformations
# ----------------------------------------------------------------------------
def fresh_name(name, existing):
    n = name + "'"
    while n in existing:
        n += "'"
    return n


def left_recursive_nts(nts, prods, first):
    edges = {n: set() for n in nts}
    for lhs, rhs in prods:
        for s in rhs:
            if s in edges:
                edges[lhs].add(s)
                if EPS in first[s]:
                    continue
            break
    rec = []
    for a in nts:
        seen, stack = set(), list(edges[a])
        while stack:
            x = stack.pop()
            if x == a:
                rec.append(a)
                break
            if x not in seen:
                seen.add(x)
                stack.extend(edges[x])
    return rec


def needs_left_factoring(prods, nts):
    for n in nts:
        seen = set()
        for lhs, rhs in prods:
            if lhs == n and rhs:
                if rhs[0] in seen:
                    return True
                seen.add(rhs[0])
    return False


def eliminate_left_recursion(nts, prods):
    P = OrderedDict((n, [list(r) for l, r in prods if l == n]) for n in nts)
    order = []
    for i, Ai in enumerate(nts):
        for Aj in nts[:i]:
            new = []
            for rhs in P[Ai]:
                if rhs and rhs[0] == Aj:
                    for g in P[Aj]:
                        new.append(g + rhs[1:])
                else:
                    new.append(rhs)
            P[Ai] = new
        rec = [r[1:] for r in P[Ai] if r and r[0] == Ai]
        non = [r for r in P[Ai] if not (r and r[0] == Ai)]
        order.append(Ai)
        if rec and non:
            Anew = fresh_name(Ai, P)
            P[Ai] = [b + [Anew] for b in non]
            P[Anew] = [a + [Anew] for a in rec] + [[]]
            order.append(Anew)
    return order, [(n, tuple(r)) for n in order for r in P[n]]


def left_factor(nts, prods):
    P = {n: [list(r) for l, r in prods if l == n] for n in nts}
    order = list(nts)
    changed = True
    while changed:
        changed = False
        for A in list(order):
            groups = OrderedDict()
            for r in P[A]:
                groups.setdefault(r[0] if r else None, []).append(r)
            for key, g in groups.items():
                if key is not None and len(g) > 1:
                    pre = g[0]
                    for r in g[1:]:
                        k = 0
                        while k < len(pre) and k < len(r) and pre[k] == r[k]:
                            k += 1
                        pre = pre[:k]
                    Anew = fresh_name(A, P)
                    P[A] = [r for r in P[A] if r not in g] + [pre + [Anew]]
                    P[Anew] = [r[len(pre):] for r in g]
                    order.insert(order.index(A) + 1, Anew)
                    changed = True
                    break
            if changed:
                break
    return order, [(n, tuple(r)) for n in order for r in P[n]]




# ----------------------------------------------------------------------------
# Recursive descent
# ----------------------------------------------------------------------------
def choose_table(nts, prods, first, follow):
    """For each non-terminal and lookahead, the list of applicable alternatives."""
    sel, conflicts = {}, []
    for idx, (lhs, rhs) in enumerate(prods):
        f = first_of_seq(rhs, first)
        targets = f - {EPS}
        if EPS in f:
            targets |= follow[lhs]
        for t in targets:
            cell = sel.setdefault((lhs, t), [])
            cell.append(idx)
            if len(cell) == 2:
                conflicts.append((lhs, t))
    return sel, conflicts


def show_procedures(nts, prods, start):
    print("\nGenerated procedures:")
    for n in nts:
        alts = [(i, r) for i, (l, r) in enumerate(prods) if l == n]
        print(f"\n  procedure {n}():")
        for k, (i, rhs) in enumerate(alts):
            kw = "if" if k == 0 else "else if"
            body = []
            for s in rhs:
                body.append(f"{s}()" if s in nts else f"match('{s}')")
            print(f"    {kw} (lookahead selects alternative {n} -> {rhs_str(rhs)}):")
            print("        " + ("; ".join(body) if body else "/* epsilon: do nothing */"))
        print("    else: error()")
    print(f"\n  main: {start}(); if lookahead == '$' then ACCEPT else error")


class ParseError(Exception):
    pass


def rd_parse(tokens, sel, prods, nts, start):
    pos = [0]
    depth = [0]
    log = []

    def note(msg):
        log.append("  " * depth[0] + msg)

    def match(t):
        if tokens[pos[0]] == t:
            note(f"match '{t}'")
            pos[0] += 1
        else:
            raise ParseError(f"expected '{t}' but found '{tokens[pos[0]]}'")

    def call(A):
        a = tokens[pos[0]]
        cell = sel.get((A, a))
        if not cell:
            raise ParseError(f"{A}() cannot start with '{a}'")
        lhs, rhs = prods[cell[0]]
        note(f"{A}()  uses  {A} -> {rhs_str(rhs)}   [lookahead '{a}']")
        depth[0] += 1
        for s in rhs:
            if s in nts:
                call(s)
            else:
                match(s)
        depth[0] -= 1

    ok, err = False, None
    try:
        call(start)
        if tokens[pos[0]] != "$":
            raise ParseError(f"extra input '{tokens[pos[0]]}' after a complete {start}")
        ok = True
    except ParseError as e:
        err = str(e)
    print()
    for l in log:
        print(l)
    if ok:
        print("\n>>> String ACCEPTED")
    else:
        print(f"  ERROR: {err}")
        print("\n>>> String REJECTED")


def ask_yes_no(msg):
    try:
        return input(msg).strip().lower().startswith("y")
    except EOFError:
        return False


def main():
    print("=== Recursive Descent Parser ===\n")
    try:
        nts, terms, prods, start = read_grammar()
    except ValueError as e:
        print("Invalid grammar:", e)
        return
    print("\nGrammar:")
    show_grammar(prods)
    first = compute_first(nts, prods)
    follow = compute_follow(nts, prods, first, start)
    rec = left_recursive_nts(nts, prods, first)
    lf = needs_left_factoring(prods, nts)
    sel, conflicts = choose_table(nts, prods, first, follow)

    if rec or lf or conflicts:
        print("\n>>> Not directly usable for (non-backtracking) recursive descent:")
        if rec:
            print("   - left recursion in:", ", ".join(rec), "(would loop forever)")
        if lf:
            print("   - alternatives with a common prefix (need left factoring)")
        for A, t in conflicts:
            print(f"   - cannot choose between alternatives of {A} on lookahead '{t}'")
        if (rec or lf) and ask_yes_no("\nEliminate left recursion / left-factor automatically? (y/n): "):
            nts, prods = eliminate_left_recursion(nts, prods)
            nts, prods = left_factor(nts, prods)
            terms = collect_terms(prods, nts)
            print("\nTransformed grammar:")
            show_grammar(prods)
            first = compute_first(nts, prods)
            follow = compute_follow(nts, prods, first, start)
            sel, conflicts = choose_table(nts, prods, first, follow)
            if conflicts:
                print("\n>>> Still not predictive:")
                for A, t in conflicts:
                    print(f"   - cannot choose between alternatives of {A} on lookahead '{t}'")
                print("    Use the backtracking parser for this grammar.")
                return
        else:
            return
    print("\n>>> The grammar is suitable for recursive descent (one-token lookahead).")
    show_procedures(nts, prods, start)
    input_loop(terms, lambda toks: rd_parse(toks, sel, prods, nts, start))


if __name__ == "__main__":
    main()
