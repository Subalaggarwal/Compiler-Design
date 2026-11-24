"""
SLR(1) Parser  (Compiler Design practical)

What it does
  1. Reads a grammar and augments it (S' -> S).
  2. Computes FIRST and FOLLOW sets.
  3. Builds the canonical collection of LR(0) item sets.
  4. Builds the SLR(1) ACTION / GOTO table: a completed item A -> alpha.
     reduces only on terminals in FOLLOW(A). If a cell gets two actions the
     grammar is reported as NOT SLR(1).
  5. Parses any number of input strings and prints a step-by-step trace.

Grammar format (one production per line, blank line to finish)
      E -> E + T | T
      T -> T * F | F
      F -> ( E ) | id
  * The LHS of the first production is the start symbol.
  * Every symbol that appears on a LHS is a non-terminal; the rest are
    terminals. Separate symbols with spaces or write single characters
    together. The word `id` is read as one terminal. Use # for epsilon.

Run:  python slr1_parser.py
"""
import sys

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
# LR(0) automaton (SLR(1) uses the same item sets)
# ----------------------------------------------------------------------------
def fmt_item(prods, pi, d):
    lhs, rhs = prods[pi]
    return f"{lhs} -> " + " ".join(list(rhs[:d]) + ["."] + list(rhs[d:]))


def build_lr0_automaton(nts, terms, prods):
    def closure(items):
        result, work = set(items), list(items)
        while work:
            pi, d = work.pop()
            rhs = prods[pi][1]
            if d < len(rhs) and rhs[d] in nts:
                for pj, (lhs, _) in enumerate(prods):
                    if lhs == rhs[d] and (pj, 0) not in result:
                        result.add((pj, 0))
                        work.append((pj, 0))
        return frozenset(result)

    def goto(I, X):
        moved = {(pi, d + 1) for pi, d in I if d < len(prods[pi][1]) and prods[pi][1][d] == X}
        return closure(moved) if moved else None

    symbols = nts + terms
    states = [closure({(0, 0)})]
    index = {states[0]: 0}
    trans = {}
    i = 0
    while i < len(states):
        for X in symbols:
            J = goto(states[i], X)
            if J is not None:
                if J not in index:
                    index[J] = len(states)
                    states.append(J)
                trans[(i, X)] = index[J]
        i += 1
    return states, trans


def show_states(states, trans, prods):
    for i, I in enumerate(states):
        print(f"I{i}:")
        for pi, d in sorted(I):
            print("    " + fmt_item(prods, pi, d))
        moves = [f"{X} -> I{j}" for (s, X), j in trans.items() if s == i]
        if moves:
            print("    transitions: " + ", ".join(moves))


def build_tables(states, trans, prods, nts, follow):
    action, goto_t = {}, {}

    def add(s, t, a):
        cell = action.setdefault((s, t), [])
        if a not in cell:
            cell.append(a)

    for (s, X), t in trans.items():
        if X in nts:
            goto_t[(s, X)] = t
        else:
            add(s, X, f"s{t}")
    for s, I in enumerate(states):
        for pi, d in sorted(I):
            lhs, rhs = prods[pi]
            if d == len(rhs):
                if pi == 0:
                    add(s, "$", "acc")
                else:
                    for a in sorted(follow[lhs]):      # SLR(1): reduce only on FOLLOW(lhs)
                        add(s, a, f"r{pi}")
    return action, goto_t


def find_conflicts(action):
    out = []
    for (s, t), acts in sorted(action.items()):
        if len(acts) > 1:
            kind = "Shift/Reduce" if any(a[0] == "s" for a in acts) else "Reduce/Reduce"
            out.append((s, t, acts, kind))
    return out


def show_tables(nstates, terms, nts, action, goto_t):
    cols = terms + ["$"] + nts[1:]

    def cell(s, c):
        if c in nts:
            return str(goto_t.get((s, c), ""))
        return "/".join(action.get((s, c), []))

    print_table(list(range(nstates)), cols, cell, "State")


def lr_parse(tokens, action, goto_t, prods):
    st, sy, i, rows, ok = [0], [], 0, [], False
    while True:
        s, a = st[-1], tokens[i]
        stk = str(st[0]) + "".join(f" {x} {n}" for x, n in zip(sy, st[1:]))
        inp = " ".join(tokens[i:])
        acts = action.get((s, a))
        if not acts:
            rows.append((stk, inp, f"Error: no action in state {s} on '{a}'"))
            break
        act = acts[0]
        if act == "acc":
            rows.append((stk, inp, "Accept"))
            ok = True
            break
        if act[0] == "s":
            rows.append((stk, inp, f"Shift {a}, go to state {act[1:]}"))
            sy.append(a)
            st.append(int(act[1:]))
            i += 1
        else:
            pi = int(act[1:])
            lhs, rhs = prods[pi]
            rows.append((stk, inp, f"Reduce by ({pi}) {lhs} -> {rhs_str(rhs)}"))
            n = len(rhs)
            if n:
                del st[-n:]
                del sy[-n:]
            nxt = goto_t.get((st[-1], lhs))
            if nxt is None:
                rows.append((stk, inp, "Error: missing GOTO entry"))
                break
            sy.append(lhs)
            st.append(nxt)
    print()
    print_trace(rows)
    print("\n>>> String ACCEPTED" if ok else "\n>>> String REJECTED")


def main():
    print("=== SLR(1) Parser ===\n")
    try:
        nts, terms, prods, start = read_grammar()
    except ValueError as e:
        print("Invalid grammar:", e)
        return
    aug = start + "'"
    while aug in nts:
        aug += "'"
    prods = [(aug, (start,))] + prods
    nts = [aug] + nts

    print("\nAugmented grammar:")
    show_grammar(prods)

    first = compute_first(nts, prods)
    follow = compute_follow(nts, prods, first, aug)
    print("\nFIRST sets:")
    for n in nts[1:]:
        print(f"  FIRST({n}) = {fmt_set(first[n])}")
    print("\nFOLLOW sets:")
    for n in nts[1:]:
        print(f"  FOLLOW({n}) = {fmt_set(follow[n])}")

    states, trans = build_lr0_automaton(nts, terms, prods)
    print(f"\nCanonical collection of LR(0) items ({len(states)} states):")
    show_states(states, trans, prods)

    action, goto_t = build_tables(states, trans, prods, nts, follow)
    print("\nSLR(1) ACTION / GOTO table  (sN = shift to N, rN = reduce by production N):")
    show_tables(len(states), terms, nts, action, goto_t)

    conflicts = find_conflicts(action)
    if conflicts:
        print("\n>>> The grammar is NOT SLR(1). Conflicts:")
        for s, t, acts, kind in conflicts:
            print(f"    state {s}, symbol '{t}': {kind} conflict ({' / '.join(acts)})")
        print("    (it may still be LALR(1) or CLR(1))")
        return
    print("\n>>> The grammar IS SLR(1).")
    input_loop(terms, lambda toks: lr_parse(toks, action, goto_t, prods))


if __name__ == "__main__":
    main()
