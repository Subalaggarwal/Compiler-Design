import sys

try:
    sys.stdout.reconfigure(encoding="utf-8")
except Exception:
    pass

EPS = "ε"
EPS_ALIASES = {"#", "eps", "epsilon", "ε", "@"}

def split_symbols(text, nts):
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
    print("  Example :  E -> E + T | T")
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

def check_operator_grammar(prods, nts):
    for lhs, rhs in prods:
        if not rhs:
            return f"epsilon production: {lhs} -> {EPS}"
        for x, y in zip(rhs, rhs[1:]):
            if x in nts and y in nts:
                return f"two adjacent non-terminals in: {lhs} -> {rhs_str(rhs)}"
    return None


def leading_or_trailing(nts, prods, lead=True):
    S = {n: set() for n in nts}
    changed = True
    while changed:
        changed = False
        for lhs, rhs in prods:
            r = rhs if lead else rhs[::-1]
            new = set()
            if r[0] not in nts:
                new.add(r[0])
            else:
                new |= S[r[0]]
                if len(r) > 1 and r[1] not in nts:
                    new.add(r[1])
            if not new <= S[lhs]:
                S[lhs] |= new
                changed = True
    return S


def build_precedence_table(nts, prods, start, L, T):
    rel, conflicts = {}, []

    def put(a, b, r):
        old = rel.get((a, b))
        if old is None:
            rel[(a, b)] = r
        elif old != r:
            conflicts.append((a, b, old, r))

    for lhs, rhs in prods:
        for i in range(len(rhs) - 1):
            x, y = rhs[i], rhs[i + 1]
            if x not in nts and y not in nts:
                put(x, y, "=")
            elif x not in nts and y in nts:
                for b in L[y]:
                    put(x, b, "<")
            elif x in nts and y not in nts:
                for a in T[x]:
                    put(a, y, ">")
            if i + 2 < len(rhs) and x not in nts and y in nts and rhs[i + 2] not in nts:
                put(x, rhs[i + 2], "=")
    for b in L[start]:
        put("$", b, "<")
    for a in T[start]:
        put(a, "$", ">")
    return rel, conflicts

def op_parse(tokens, rel, prods, nts):
    stack, i, rows, ok = ["$"], 0, [], False

    def top_terminal():
        for s in reversed(stack):
            if s not in nts:
                return s

    def match_production(handle):
        for idx, (lhs, rhs) in enumerate(prods):
            if len(rhs) == len(handle) and all(
                    (x in nts) == (h in nts) and (x in nts or x == h) for x, h in zip(rhs, handle)):
                return idx
        return None

    while True:
        a, b = top_terminal(), tokens[i]
        stk, inp = " ".join(stack), " ".join(tokens[i:])
        if a == "$" and b == "$":
            if len(stack) == 2 and stack[1] in nts:
                rows.append((stk, "", inp, "Accept"))
                ok = True
            else:
                rows.append((stk, "", inp, "Error: input finished but stack is not a single non-terminal"))
            break
        r = rel.get((a, b))
        if r is None:
            rows.append((stk, "-", inp, f"Error: no precedence relation between '{a}' and '{b}'"))
            break
        if r in ("<", "="):
            rows.append((stk, r, inp, f"Shift {b}"))
            stack.append(b)
            i += 1
            continue
          
        handle, last, bad = [], None, None
        while True:
            if len(stack) <= 1:
                bad = "stack underflow while looking for the handle"
                break
            x = stack.pop()
            handle.insert(0, x)
            if x not in nts:
                last = x
            if last is None:
                continue
            rr = rel.get((top_terminal(), last))
            if rr == "<":
                break
            if rr != "=":
                bad = "could not find the start of the handle"
                break
        if bad:
            rows.append((stk, ">", inp, "Error: " + bad))
            break
        if stack[-1] in nts:
            handle.insert(0, stack.pop())
        idx = match_production(handle)
        if idx is None:
            rows.append((stk, ">", inp, "Error: handle '" + " ".join(handle) + "' matches no production"))
            break
        lhs, rhs = prods[idx]
        rows.append((stk, ">", inp, f"Reduce {lhs} -> {rhs_str(rhs)}"))
        stack.append(lhs)

    print()
    print_trace(rows, ("Stack", "Rel", "Input", "Action"))
    print("\n>>> String ACCEPTED" if ok else "\n>>> String REJECTED")


def main():
    print("=== Operator Precedence Parser ===\n")
    try:
        nts, terms, prods, start = read_grammar()
    except ValueError as e:
        print("Invalid grammar:", e)
        return
    print("\nGrammar:")
    show_grammar(prods)

    problem = check_operator_grammar(prods, nts)
    if problem:
        print("\n>>> NOT an operator grammar -> operator precedence parsing is not applicable.")
        print("    Reason:", problem)
        return
    print("\n>>> The grammar is an operator grammar.")

    L = leading_or_trailing(nts, prods, True)
    T = leading_or_trailing(nts, prods, False)
    print("\nLEADING sets:")
    for n in nts:
        print(f"  LEADING({n}) = {fmt_set(L[n])}")
    print("\nTRAILING sets:")
    for n in nts:
        print(f"  TRAILING({n}) = {fmt_set(T[n])}")

    rel, conflicts = build_precedence_table(nts, prods, start, L, T)
    if conflicts:
        print("\n>>> The grammar is NOT an operator precedence grammar (conflicting relations):")
        for a, b, old, new in conflicts:
            print(f"    between '{a}' and '{b}': both '{old}' and '{new}'")
        print("    (ambiguous grammars such as E -> E+E | E*E | id usually fail; use an unambiguous one)")
        return
    print("\n>>> The grammar IS an operator precedence grammar.")

    print("\nPrecedence relation table  ( < yields, = equal, > takes precedence, blank = error ):")
    syms = terms + ["$"]
    print_table(syms, syms, lambda r, c: rel.get((r, c), ""), "")
    input_loop(terms, lambda toks: op_parse(toks, rel, prods, nts))


if __name__ == "__main__":
    main()
