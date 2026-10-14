/-!
# Graphs, legal sequences and the strong product

A finite graph has vertices `0, …, n-1` and a Boolean adjacency test. `G.cl u w` says that `w` lies in
the closed neighbourhood `N[u]`. Following Brešar, Gologranc, Milanič, Rall and Rizzi, a sequence
`(v₁, …, v_k)` is *legal* if every `vᵢ` dominates a vertex that no earlier `vⱼ` dominates; the Grundy
domination number is the largest length of a legal sequence (a legal sequence of largest length is
automatically dominating). `LegalFrom G pre l` says that the vertices of `l`, chosen in order after
those of `pre`, satisfy this condition.
-/

namespace GrundyStrong

structure FinGraph where
  n : Nat
  adj : Nat → Nat → Bool

/-- `w ∈ N[u]`. -/
def FinGraph.cl (G : FinGraph) (u w : Nat) : Bool := u == w || G.adj u w

/-- The vertices of `l`, chosen after those of `pre`, form a legal continuation. -/
def FinGraph.LegalFrom (G : FinGraph) : List Nat → List Nat → Prop
  | _, [] => True
  | pre, v :: l =>
      v < G.n ∧ (∃ w, w < G.n ∧ (G.cl v w = true ∧ ∀ u ∈ pre, G.cl u w = false)) ∧
        G.LegalFrom (pre ++ [v]) l

/-- A legal sequence. -/
def FinGraph.Legal (G : FinGraph) (l : List Nat) : Prop := G.LegalFrom [] l

/-- Every vertex is dominated by some vertex of `l`. -/
def FinGraph.Dominating (G : FinGraph) (l : List Nat) : Prop :=
  ∀ w, w < G.n → ∃ u ∈ l, G.cl u w = true

/-- No loops, and the adjacency is symmetric. -/
def FinGraph.Simple (G : FinGraph) : Prop :=
  ∀ u, u < G.n → ∀ v, v < G.n → G.adj u u = false ∧ G.adj u v = G.adj v u

instance decLegalFrom (G : FinGraph) : (pre l : List Nat) → Decidable (G.LegalFrom pre l)
  | _, [] => isTrue trivial
  | pre, v :: l =>
    have := decLegalFrom G (pre ++ [v]) l
    inferInstanceAs (Decidable (v < G.n ∧ (∃ w, w < G.n ∧ (G.cl v w = true ∧ ∀ u ∈ pre, G.cl u w = false)) ∧
        G.LegalFrom (pre ++ [v]) l))

instance (G : FinGraph) (l : List Nat) : Decidable (G.Legal l) := decLegalFrom G [] l

instance (G : FinGraph) : Decidable G.Simple :=
  inferInstanceAs (Decidable (∀ u, u < G.n → ∀ v, v < G.n → G.adj u u = false ∧ G.adj u v = G.adj v u))

instance (G : FinGraph) (l : List Nat) : Decidable (G.Dominating l) :=
  inferInstanceAs (Decidable (∀ w, w < G.n → ∃ u ∈ l, G.cl u w = true))

/-- The strong product `G ⊠ H`; the vertex `(g, h)` is the number `g * H.n + h`. Two distinct
vertices are adjacent when their coordinates are equal or adjacent in each factor. -/
def strong (G H : FinGraph) : FinGraph where
  n := G.n * H.n
  adj x y := x != y && G.cl (x / H.n) (y / H.n) && H.cl (x % H.n) (y % H.n)

/-- The octahedron `K_{2,2,2}`: each vertex `u` is adjacent to all but itself and `u ± 3`. -/
def oct : FinGraph where
  n := 6
  adj u v := u != v && u + 3 != v && v + 3 != u

/-- The graph `H_N` on `0, …, N-1`: `i < j` are adjacent when `j - i ≡ 2 (mod 3)`. -/
def hgraph (N : Nat) : FinGraph where
  n := N
  adj u v := u != v && (if u < v then v - u else u - v) % 3 == 2

end GrundyStrong
