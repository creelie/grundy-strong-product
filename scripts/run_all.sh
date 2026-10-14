#!/usr/bin/env bash
# run_all.sh -- every check outside Lean; outputs go to build/.
#   C:       grundy_bfs (breadth-first search over dominated sets): gamma_gr(K_{2,2,2}) = 2, and
#            gamma_gr(H_N) = floor((N + 1) / 3) + 3 for 6 <= N <= 45, with the layer sizes of H_21
#   Python:  check_counterexample.py (everything from the edge sets: gamma_gr of the octahedron by
#            trying every sequence, gamma_gr(H_N) for N <= 24 by memoised depth-first search, the
#            product sequences for 21 <= N <= 36, the circular description of H_{3n});
#            check_lean_data.py (the masks, layers and sequences written into the Lean files)
#   Lean:    gen_layers.py must reproduce lean/GrundyStrong/Layers.lean exactly
# Needs a C compiler and Python 3.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
B="$ROOT/build"
mkdir -p "$B"
cd "$ROOT"

echo "== C: breadth-first search"
cc -O2 -Wall -Wextra -o "$B/grundy_bfs" verification/c/grundy_bfs.c
"$B/grundy_bfs" oct | tee "$B/bfs.txt"
grep -q "K_{2,2,2}: 8 dominated sets in all; Grundy domination number 2" "$B/bfs.txt"
for N in $(seq 6 45); do
  "$B/grundy_bfs" "$N" | tee -a "$B/bfs.txt" | tail -1
  want=$(( (N + 1) / 3 + 3 ))
  grep -q "^$N: .*Grundy domination number $want\$" "$B/bfs.txt" || { echo "run_all.sh: H_$N is not $want" >&2; exit 1; }
done
grep -q "^21: layer sizes 1, 21, 210, 1023, 1482, 1302, 848, 419, 150, 22, 1$" "$B/bfs.txt"

echo "== Python: the counterexample from its definitions"
python3 -I verification/python/check_counterexample.py | tee "$B/check_counterexample.txt"

echo "== Python: the data in the Lean files"
python3 -I verification/python/check_lean_data.py lean/GrundyStrong | tee "$B/check_lean_data.txt"

echo "== the Lean layers are the generator's output"
python3 -I scripts/gen_layers.py > "$B/Layers.lean"
cmp "$B/Layers.lean" lean/GrundyStrong/Layers.lean
echo "all checks passed"
