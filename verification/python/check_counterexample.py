"""check_counterexample.py -- every claim of the paper about the graphs, from their definitions.

The graphs are built as edge sets, independently of the Lean files and of the C program:

  * K_{2,2,2}: vertices 0, ..., 5, with i and i + 3 the only non-adjacent pairs;
  * H_N: vertices 0, ..., N - 1, with u and v adjacent when |u - v| is congruent to 2 modulo 3;
  * the strong product, from its definition: distinct (g, h) and (g', h') are adjacent when g = g' or
    gg' is an edge, and h = h' or hh' is an edge.

Checked here:
  1. gamma_gr(K_{2,2,2}) = 2, by trying every sequence of distinct vertices;
  2. the sequence 0, 3, 6, 9, 12, 19, 14, 2, 15, 1 is a legal dominating sequence of H_21;
  3. gamma_gr(H_N) = floor((N + 1) / 3) + 3 for 6 <= N <= 24, by a memoised depth-first search over
     dominated sets (a different algorithm from the breadth-first layers used in Lean and in C);
  4. for 21 <= N <= 36 the sequence (j mod 3, j), j = 0, ..., N - 1, is a legal dominating sequence of
     K_{2,2,2} x H_N (strong product), of length N;
  5. the description of H_{3n} in Proposition 2.1: in the cyclic order a_0, ..., a_{n-1}, c_0, ...,
     c_{n-1}, b_0, ..., b_{n-1} (a_i = 3i, b_i = 3i + 1, c_i = 3i + 2), two vertices are adjacent
     exactly when their cyclic distance lies between n + 1 and 2n - 1, or they are a_i and c_i;
     checked for 2 <= n <= 30;
  6. gamma_gr of the circular clique K_{3n/(n+1)} (cyclic distance at least n + 1) is n + 4 for
     3 <= n <= 11, by the same depth-first search; it satisfies the hypothesis of Proposition 3.1, so
     it is a counterexample too for 9 <= n <= 11.

Usage: python3 -I check_counterexample.py
"""
import itertools
import sys
from functools import lru_cache

failures = 0


def report(ok, what):
    global failures
    print(("ok    " if ok else "FAIL  ") + what)
    failures += not ok


def graph_oct():
    V = list(range(6))
    E = {frozenset((u, v)) for u in V for v in V if u != v and abs(u - v) != 3}
    return V, E


def graph_h(N):
    V = list(range(N))
    E = {frozenset((u, v)) for u in V for v in V if u < v and (v - u) % 3 == 2}
    return V, E


def strong(G, H):
    (VG, EG), (VH, EH) = G, H
    V = [(g, h) for g in VG for h in VH]
    E = set()
    for x, y in itertools.combinations(V, 2):
        if (x[0] == y[0] or frozenset((x[0], y[0])) in EG) and (x[1] == y[1] or frozenset((x[1], y[1])) in EH):
            E.add(frozenset((x, y)))
    return V, E


def closed(G):
    V, E = G
    return {v: frozenset([v] + [w for w in V if frozenset((v, w)) in E]) for v in V}


def legal_dominating(G, seq):
    N = closed(G)
    if len(set(seq)) != len(seq):
        return False, False
    seen = set()
    for v in seq:
        if not N[v] - seen:
            return False, False
        seen |= N[v]
    return True, seen == set(G[0])


def grundy_brute(G):
    """Longest legal sequence by trying every sequence of distinct vertices."""
    N = closed(G)
    best = 0

    def go(seq, seen):
        nonlocal best
        best = max(best, len(seq))
        for v in G[0]:
            if v not in seq and N[v] - seen:
                go(seq + [v], seen | N[v])

    go([], frozenset())
    return best


def grundy_dfs(G):
    """Longest legal sequence by memoised depth-first search over dominated sets."""
    V = G[0]
    idx = {v: i for i, v in enumerate(V)}
    masks = [sum(1 << idx[w] for w in nb) for nb in (closed(G)[v] for v in V)]

    @lru_cache(maxsize=None)
    def longest(D):
        return max((1 + longest(D | m) for m in masks if D | m != D), default=0)

    return longest(0)


# 1. the octahedron
OCT = graph_oct()
report(len(OCT[1]) == 12 and all(len(OCT[1] & {frozenset((v, w)) for w in range(6)}) == 4 for v in range(6)),
       "K_{2,2,2}: 12 edges, 4-regular")
report(grundy_brute(OCT) == 2, "gamma_gr(K_{2,2,2}) = 2 (every sequence tried)")

# 2. a Grundy dominating sequence of H_21
H21 = graph_h(21)
report(legal_dominating(H21, [0, 3, 6, 9, 12, 19, 14, 2, 15, 1]) == (True, True),
       "0, 3, 6, 9, 12, 19, 14, 2, 15, 1 is legal and dominating in H_21")

# 3. gamma_gr(H_N) for 6 <= N <= 24
values = {N: grundy_dfs(graph_h(N)) for N in range(6, 25)}
print("      gamma_gr(H_N), N = 6..24:", " ".join(f"{N}:{g}" for N, g in values.items()))
report(all(g == (N + 1) // 3 + 3 for N, g in values.items()), "gamma_gr(H_N) = floor((N+1)/3) + 3 for 6 <= N <= 24")
report(values[21] == 10, "gamma_gr(H_21) = 10")

# 4. the product sequence
for N in range(21, 37):
    P = strong(OCT, graph_h(N))
    seq = [(j % 3, j) for j in range(N)]
    report(legal_dominating(P, seq) == (True, True),
           f"N = {N}: (j mod 3, j), j < {N}, is legal and dominating in K_222 x H_{N} ({len(P[0])} vertices, {len(P[1])} edges)")

# 5. the circular description of H_{3n}
ok = True
for n in range(2, 31):
    N = 3 * n
    _, E = graph_h(N)
    order = [3 * i for i in range(n)] + [3 * i + 2 for i in range(n)] + [3 * i + 1 for i in range(n)]
    pos = {v: p for p, v in enumerate(order)}
    for u in range(N):
        for v in range(u + 1, N):
            d = (pos[v] - pos[u]) % N
            d = min(d, N - d)
            matched = {u % 3, v % 3} == {0, 2} and u // 3 == v // 3
            ok &= (frozenset((u, v)) in E) == (n + 1 <= d <= 2 * n - 1 or matched)
report(ok, "Proposition 2.1: H_{3n} is the circular graph (distance n+1..2n-1) plus the matching a_i c_i, 2 <= n <= 30")

# 6. the circular cliques K_{3n/(n+1)}
for n in range(3, 12):
    N = 3 * n
    V = list(range(N))
    E = {frozenset((u, v)) for u in V for v in V if u < v and min((v - u) % N, (u - v) % N) >= n + 1}
    g = grundy_dfs((V, E))
    # the hypothesis of Proposition 3.1, in the order a_0, b_0, c_0, a_1, ... of H_{3n}:
    # position p holds a_i, c_i or b_i for p = i, n + i, 2n + i
    vid = {p: 3 * (p % n) + (0, 2, 1)[p // n] for p in V}
    hyp = all((vid[u] - vid[v]) % 3 == 1 if vid[u] < vid[v] else (vid[v] - vid[u]) % 3 == 1
              for u, v in map(tuple, E))
    report(g == n + 4 and hyp and (N > 2 * g) == (n >= 9),
           f"K_{{{N}/{n + 1}}}: gamma_gr = {g} = n + 4; Proposition 3.1 applies; counterexample: {N > 2 * g}")

print("check_counterexample:", "all checks passed" if not failures else f"{failures} failures")
sys.exit(1 if failures else 0)
