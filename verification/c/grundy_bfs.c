/* grundy_bfs.c -- exact Grundy domination number by breadth-first search over dominated sets.
 *
 *   grundy_bfs N      the graph H_N on 0, ..., N - 1 (N <= 63): u and v adjacent when |u - v| = 2 (mod 3)
 *   grundy_bfs oct    the octahedron K_{2,2,2} on 0, ..., 5: i and i + 3 are the non-adjacent pairs
 *
 * Layer k is the set of vertex sets dominated by the legal sequences of length k: layer 0 is {empty},
 * and layer k + 1 holds D | N[v] for D in layer k and every v with N[v] not inside D. A legal
 * sequence of length k exists iff layer k is nonempty, so the Grundy domination number is the index
 * of the last nonempty layer. The program prints every layer size; for H_21 these are the sizes of
 * the layers written into lean/GrundyStrong/Layers.lean. Written independently of the Python checks.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint64_t *tab;
static uint64_t cap;

static int insert(uint64_t x) { /* 1 if x is new; open addressing, keys stored as x + 1 */
  uint64_t h = ((x * 0x9E3779B97F4A7C15ULL) >> 20) & (cap - 1);
  while (tab[h]) {
    if (tab[h] == x + 1) return 0;
    h = (h + 1) & (cap - 1);
  }
  tab[h] = x + 1;
  return 1;
}

int main(int argc, char **argv) {
  if (argc != 2) { fprintf(stderr, "usage: grundy_bfs N | oct\n"); return 2; }
  int oct = strcmp(argv[1], "oct") == 0, N = oct ? 6 : atoi(argv[1]);
  if (N < 1 || N > 63) { fprintf(stderr, "N must be between 1 and 63\n"); return 2; }
  uint64_t nb[64];
  for (int v = 0; v < N; v++) {
    nb[v] = 1ULL << v;
    for (int u = 0; u < N; u++) {
      int d = u > v ? u - v : v - u;
      if (u != v && (oct ? d != 3 : d % 3 == 2)) nb[v] |= 1ULL << u;
    }
  }
  cap = N <= 45 ? 1ULL << 24 : N <= 55 ? 1ULL << 26 : 1ULL << 28; /* at most half full below */
  tab = calloc(cap, sizeof *tab);
  size_t room = 1 << 20;
  uint64_t *cur = malloc(room * sizeof *cur), *nxt = malloc(room * sizeof *nxt);
  if (!tab || !cur || !nxt) { fprintf(stderr, "out of memory\n"); return 1; }
  size_t nc = 1, nn, total = 1;
  cur[0] = 0;
  int layer = 0;
  printf("%s: layer sizes 1", oct ? "K_{2,2,2}" : argv[1]);
  for (;;) {
    nn = 0;
    memset(tab, 0, cap * sizeof *tab);
    for (size_t i = 0; i < nc; i++)
      for (int v = 0; v < N; v++)
        if (nb[v] & ~cur[i]) {
          uint64_t y = cur[i] | nb[v];
          if (insert(y)) {
            if (nn == room) { /* grow both buffers */
              room *= 2;
              cur = realloc(cur, room * sizeof *cur);
              nxt = realloc(nxt, room * sizeof *nxt);
              if (!cur || !nxt) { fprintf(stderr, "out of memory\n"); return 1; }
            }
            if (2 * (nn + 1) > cap) { fprintf(stderr, "hash table too small\n"); return 1; }
            nxt[nn++] = y;
          }
        }
    if (!nn) break;
    layer++;
    total += nn;
    printf(", %zu", nn);
    uint64_t *t = cur; cur = nxt; nxt = t; nc = nn;
  }
  printf("\n%s: %zu dominated sets in all; Grundy domination number %d\n", oct ? "K_{2,2,2}" : argv[1], total, layer);
  return 0;
}
