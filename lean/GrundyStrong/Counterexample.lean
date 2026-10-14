import GrundyStrong.Layers

/-!
# The counterexample

`oct` is the octahedron `K_{2,2,2}` and `H := hgraph 21` is the graph on `0, …, 20` in which
`i < j` are adjacent when `j - i ≡ 2 (mod 3)`. We prove

* `γ_gr(oct) = 2` and `γ_gr(H) = 10` (a legal sequence of that length, and an exhaustive search
  showing that no legal sequence is longer), and
* `oct ⊠ H` has a dominating legal sequence of length `21 > 2 · 10`,

so `γ_gr(oct ⊠ H) ≥ 21 > γ_gr(oct) γ_gr(H)`, against the conjecture of Brešar, Bujtás, Gologranc,
Klavžar, Košmrlj, Patkós, Tuza and Vizer (Electron. J. Combin. 23(4) (2016), P4.34, Conjecture 22; Conjecture 6.2 in arXiv:1607.00248).
-/

namespace GrundyStrong

/-- The graph `H_21`. -/
abbrev H : FinGraph := hgraph 21

/-- Bit masks of the closed neighbourhoods of `oct`. -/
def octMask (v : Nat) : Nat := [55, 47, 31, 62, 61, 59].getD v 0

/-- Bit masks of the closed neighbourhoods of `H`. -/
def hMask (v : Nat) : Nat :=
  [1198373, 299594, 599189, 1198378, 299604, 599209, 1198418, 299684, 599369, 1198738, 300324,
    600649, 1201298, 305444, 610889, 1221778, 346404, 692809, 1385618, 674084, 1348169].getD v 0

theorem oct_simple : oct.Simple := by decide

theorem H_simple : H.Simple := by decide +kernel

theorem octMask_spec : ∀ v, v < oct.n → ∀ w, w < oct.n → (octMask v).testBit w = oct.cl v w := by
  decide

theorem hMask_spec : ∀ v, v < H.n → ∀ w, w < H.n → (hMask v).testBit w = H.cl v w := by
  decide +kernel

theorem oct_certified : certified oct.n octMask octLayers = true := by decide +kernel

theorem H_certified : certified H.n hMask hLayers = true := by decide +kernel

theorem oct_legal_le (l : List Nat) (hl : oct.Legal l) : l.length ≤ 2 :=
  Nat.le_of_succ_le_succ (legal_length_le oct octMask octMask_spec octLayers oct_certified l hl)

theorem H_legal_le (l : List Nat) (hl : H.Legal l) : l.length ≤ 10 :=
  Nat.le_of_succ_le_succ (legal_length_le H hMask hMask_spec hLayers H_certified l hl)

/-- `γ_gr(oct) = 2`. -/
theorem oct_grundy : oct.Legal [0, 3] ∧ oct.Dominating [0, 3] ∧ ∀ l, oct.Legal l → l.length ≤ 2 :=
  ⟨by decide, by decide, oct_legal_le⟩

/-- A Grundy dominating sequence of `H`: `a₀ a₁ a₂ a₃ a₄ b₆ c₄ c₀ a₅ b₀`, where `aᵢ = 3i`,
`bᵢ = 3i + 1`, `cᵢ = 3i + 2`. -/
def hSeq : List Nat := [0, 3, 6, 9, 12, 19, 14, 2, 15, 1]

/-- `γ_gr(H) = 10`. -/
theorem H_grundy : H.Legal hSeq ∧ H.Dominating hSeq ∧ hSeq.length = 10 ∧
    ∀ l, H.Legal l → l.length ≤ 10 :=
  ⟨by decide +kernel, by decide +kernel, rfl, H_legal_le⟩

/-- The sequence `((j mod 3), j)`, `j = 0, …, 20`, in `oct ⊠ H`; the vertex `(g, h)` is `21 g + h`. -/
def prodSeq : List Nat := (List.range 21).map fun j => (j % 3) * 21 + j

theorem prodSeq_legal : (strong oct H).Legal prodSeq := by decide +kernel

theorem prodSeq_dominating : (strong oct H).Dominating prodSeq := by decide +kernel

theorem prodSeq_nodup : prodSeq.Nodup := by decide +kernel

theorem prodSeq_length : prodSeq.length = 21 := rfl

/-- The strong product conjecture fails for `oct` and `H`: the product has a dominating legal
sequence of length 21, while every legal sequence of `oct` has at most 2 vertices and every legal
sequence of `H` at most 10. -/
theorem strong_product_counterexample :
    (∃ l, (strong oct H).Legal l ∧ (strong oct H).Dominating l ∧ l.length = 21) ∧
    (∀ l, oct.Legal l → l.length ≤ 2) ∧ (∀ l, H.Legal l → l.length ≤ 10) ∧ 2 * 10 < 21 :=
  ⟨⟨prodSeq, prodSeq_legal, prodSeq_dominating, prodSeq_length⟩, oct_legal_le, H_legal_le, by decide⟩

end GrundyStrong
