"""check_lean_data.py -- the data written into the Lean files is what the paper says it is.

  * octMask and hMask in lean/GrundyStrong/Counterexample.lean are the closed neighbourhoods of
    K_{2,2,2} and H_21 (bit w of mask v is set iff w = v or vw is an edge);
  * every tree in lean/GrundyStrong/Layers.lean is a binary search tree (its keys, read in order,
    increase strictly), and layer k holds exactly the vertex sets dominated by the legal sequences of
    length k, recomputed here from the edge sets; the layer sizes match the paper;
  * the sequences hSeq and prodSeq in Counterexample.lean are the ones in the paper.

Usage: python3 -I check_lean_data.py lean/GrundyStrong
"""
import re
import sys

D = sys.argv[1]
CE = open(f"{D}/Counterexample.lean").read()
LY = open(f"{D}/Layers.lean").read()
failures = 0


def report(ok, what):
    global failures
    print(("ok    " if ok else "FAIL  ") + what)
    failures += not ok


def closed_masks(n, adj):
    return [sum(1 << w for w in range(n) if w == v or adj(v, w)) for v in range(n)]


def layers(masks):
    L = [{0}]
    while True:
        nxt = {D | m for D in L[-1] for m in masks if D | m != D}
        if not nxt:
            return L
        L.append(nxt)


def lean_list(name):
    body = re.search(rf"def {name} \(v : Nat\) : Nat :=\s*\[([^\]]*)\]\.getD v 0", CE).group(1)
    return [int(x) for x in body.replace("\n", " ").split(",")]


OCT = closed_masks(6, lambda u, w: u != w and abs(u - w) != 3)
H21 = closed_masks(21, lambda u, w: u != w and abs(u - w) % 3 == 2)
report(lean_list("octMask") == OCT, "octMask = closed neighbourhoods of K_{2,2,2}")
report(lean_list("hMask") == H21, "hMask = closed neighbourhoods of H_21")


def lean_layers(name):
    defs = dict(re.findall(rf"def ({name}\d+) : Tree :=\s*(.*?)\n\n", LY, re.S))
    order = re.search(rf"def {name} : List Tree := \[([^\]]*)\]", LY).group(1).replace(" ", "").split(",")
    out = []
    for d in order:
        keys = [int(x) for x in re.findall(r"\d+", defs[d])]
        out.append(keys)
    return out


for name, masks, sizes in (("octLayers", OCT, [1, 6, 1]),
                           ("hLayers", H21, [1, 21, 210, 1023, 1482, 1302, 848, 419, 150, 22, 1])):
    got = lean_layers(name)
    want = layers(masks)
    report(all(all(a < b for a, b in zip(k, k[1:])) for k in got), f"{name}: every tree is a binary search tree")
    report([set(k) for k in got] == want, f"{name}: the trees hold exactly the reachable dominated sets")
    report([len(k) for k in got] == sizes, f"{name}: layer sizes {sizes}")

report("def hSeq : List Nat := [0, 3, 6, 9, 12, 19, 14, 2, 15, 1]" in CE, "hSeq is the sequence of the paper")
report("(List.range 21).map fun j => (j % 3) * 21 + j" in CE, "prodSeq is (j mod 3, j), j < 21, with (g, h) = 21 g + h")
print("check_lean_data:", "all checks passed" if not failures else f"{failures} failures")
sys.exit(1 if failures else 0)
