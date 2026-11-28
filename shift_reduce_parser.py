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
# Shift-reduce with backtracking over the moves
# ----------------------------------------------------------------------------
def sr_parse(tokens, prods, nts, start):
    sys.setrecursionlimit(20000)
    toks = tokens[:-1]
    n = len(toks)
    seen = set()
    stats = {"conflicts": 0, "dead": 0}

    def reductions(stack):
        out = []
        for idx, (lhs, rhs) in enumerate(prods):
            k = len(rhs)
            if k <= len(stack) and tuple(stack[len(stack) - k:]) == rhs:
                out.append((idx, k))
        out.sort(key=lambda x: -x[1])                    # longest handle first
        return out

    def search(stack, pos):
        if stack == (start,) and pos == n:
            return []
        key = (stack, pos)
        if key in seen:
            return None
        seen.add(key)
        moves = [("reduce", i, k) for i, k in reductions(stack)]
        if pos < n:
            moves.append(("shift", None, None))
        if len(moves) > 1:
            stats["conflicts"] += 1
        for kind, idx, k in moves:
            if kind == "shift":
                ns, np = stack + (toks[pos],), pos + 1
                label = f"Shift {toks[pos]}"
            else:
                lhs, rhs = prods[idx]
                ns, np = stack[:len(stack) - k] + (lhs,), pos
                label = f"Reduce {lhs} -> {rhs_str(rhs)}"
            rest = search(ns, np)
            if rest is not None:
                row = (" ".join(("$",) + stack), " ".join(toks[pos:] + ["$"]),
                       label + ("   [choice]" if len(moves) > 1 else ""))
                return [row] + rest
        stats["dead"] += 1
        return None

    path = search((), 0)
    print()
    if path is not None:
        path.append(("$ " + start, "$", "Accept"))
        print_trace(path)
        print(f"\nDecision points (shift/reduce choices): {stats['conflicts']}, dead ends backtracked: {stats['dead']}")
        print("\n>>> String ACCEPTED")
    else:
        print(f"No sequence of shift/reduce moves reduces the input to '{start}'.")
        print("\n>>> String REJECTED")


def main():
    print("=== Shift-Reduce Parser ===\n")
    try:
        nts, terms, prods, start = read_grammar()
    except ValueError as e:
        print("Invalid grammar:", e)
        return
    if any(not rhs for _, rhs in prods):
        print("Epsilon productions are not supported by this parser. Remove them and try again.")
        return
    print("\nGrammar:")
    show_grammar(prods)
    input_loop(terms, lambda toks: sr_parse(toks, prods, nts, start))


if __name__ == "__main__":
    main()
