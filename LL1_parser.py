import sys
from collections import OrderedDict

try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass

EPS = "ε"
EPS_ALIASES = {"#", "eps", "epsilon", "ε", "@"}

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

def first_of_seq(seq, first):
    res = set()
    for s in seq:
        if s in first:                       
            res |= first[s] - {EPS}
            if EPS not in first[s]:
                return res
        else:                                
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


def build_ll1_table(prods, first, follow):
    table, conflicts = {}, []
    for idx, (lhs, rhs) in enumerate(prods):
        f = first_of_seq(rhs, first)
        targets = f - {EPS}
        if EPS in f:
            targets |= follow[lhs]
        for t in sorted(targets):
            key = (lhs, t)
            if key in table and table[key] != idx:
                conflicts.append((key, table[key], idx))
            else:
                table[key] = idx
    return table, conflicts


def analyse(nts, prods, start):
    first = compute_first(nts, prods)
    follow = compute_follow(nts, prods, first, start)
    print("\nFIRST sets:")
    for n in nts:
        print(f"  FIRST({n}) = {fmt_set(first[n])}")
    print("\nFOLLOW sets:")
    for n in nts:
        print(f"  FOLLOW({n}) = {fmt_set(follow[n])}")
    table, conflicts = build_ll1_table(prods, first, follow)
    return first, follow, table, conflicts


def show_conflicts(conflicts, prods):
    for (nt, t), i, j in conflicts:
        print(f"  M[{nt}, {t}] has two entries: ({i}) {prods[i][0]} -> {rhs_str(prods[i][1])}"
              f"   and   ({j}) {prods[j][0]} -> {rhs_str(prods[j][1])}")


def ll1_parse(tokens, table, prods, start, nts):
    stack, i, rows, ok = ["$", start], 0, [], False
    while True:
        top, a = stack[-1], tokens[i]
        stk, inp = " ".join(stack), " ".join(tokens[i:])
        if top == "$" and a == "$":
            rows.append((stk, inp, "Accept"))
            ok = True
            break
        if top not in nts:
            if top == a:
                rows.append((stk, inp, f"Match '{a}'"))
                stack.pop()
                i += 1
            else:
                rows.append((stk, inp, f"Error: expected '{top}', found '{a}'"))
                break
        else:
            idx = table.get((top, a))
            if idx is None:
                rows.append((stk, inp, f"Error: no entry M[{top}, {a}]"))
                break
            lhs, rhs = prods[idx]
            rows.append((stk, inp, f"{lhs} -> {rhs_str(rhs)}"))
            stack.pop()
            stack.extend(reversed(rhs))
    print()
    print_trace(rows)
    print("\n>>> String ACCEPTED" if ok else "\n>>> String REJECTED")


def ask_yes_no(msg):
    try:
        return input(msg).strip().lower().startswith("y")
    except EOFError:
        return False


def main():
    print("=== LL(1) Predictive Parser ===\n")
    try:
        nts, terms, prods, start = read_grammar()
    except ValueError as e:
        print("Invalid grammar:", e)
        return
    print("\nGrammar:")
    show_grammar(prods)

    first, follow, table, conflicts = analyse(nts, prods, start)
    rec = left_recursive_nts(nts, prods, first)
    lf = needs_left_factoring(prods, nts)

    if conflicts:
        print("\n>>> The grammar is NOT LL(1).")
        if rec:
            print("   - left recursion in:", ", ".join(rec))
        if lf:
            print("   - common left prefixes (needs left factoring)")
        show_conflicts(conflicts, prods)
        if (rec or lf) and ask_yes_no("\nEliminate left recursion / left-factor the grammar automatically? (y/n): "):
            nts, prods = eliminate_left_recursion(nts, prods)
            nts, prods = left_factor(nts, prods)
            terms = collect_terms(prods, nts)
            print("\nTransformed grammar:")
            show_grammar(prods)
            first, follow, table, conflicts = analyse(nts, prods, start)
            if conflicts:
                print("\n>>> Still NOT LL(1) after transformation (the grammar is ambiguous or needs more rewriting).")
                show_conflicts(conflicts, prods)
                return
        else:
            return

    print("\n>>> The grammar IS LL(1).")
    print("\nLL(1) parsing table:")
    cols = terms + ["$"]

    def cell(r, c):
        idx = table.get((r, c))
        return "" if idx is None else f"{prods[idx][0]} -> {rhs_str(prods[idx][1])}"

    print_table(nts, cols, cell, "M")
    input_loop(terms, lambda toks: ll1_parse(toks, table, prods, start, nts))


if __name__ == "__main__":
    main()
