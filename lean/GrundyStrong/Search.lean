import GrundyStrong.Basic

/-!
# Upper bounds from a layered certificate

A set of dominated vertices is a bit mask: `mask v` is the mask of `N[v]`, and `dom mask pre` is the
union of the masks of the vertices of `pre`. A certificate is a list of layers `L₀, …, L_m`, each a
binary search tree of masks, such that `0 ∈ L₀`, and for every `D ∈ L_k` and every vertex `v` the
mask `D ||| mask v` either equals `D` or lies in `L_{k+1}` (with `L_{m+1}` empty). The kernel checks
a certificate by evaluation; `legal_length_le` shows that it bounds every legal sequence by `m`.
-/

namespace GrundyStrong

inductive Tree where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree

namespace Tree

/-- `x` occurs somewhere in the tree. -/
def Occ : Tree → Nat → Prop
  | leaf, _ => False
  | node l k r, x => l.Occ x ∨ x = k ∨ r.Occ x

/-- Binary search for `x`. -/
def mem : Tree → Nat → Bool
  | leaf, _ => false
  | node l k r, x => if x < k then l.mem x else if k < x then r.mem x else true

/-- `p` holds at every key. -/
def all : Tree → (Nat → Bool) → Bool
  | leaf, _ => true
  | node l k r, p => l.all p && p k && r.all p

theorem occ_of_mem : ∀ {t : Tree} {x : Nat}, t.mem x = true → t.Occ x
  | leaf, _, h => Bool.false_ne_true h
  | node l k r, x, h => by
    unfold mem at h
    by_cases h1 : x < k
    · rw [ite_eq_left h1] at h
      exact Or.inl (occ_of_mem h)
    · rw [ite_eq_right h1] at h
      by_cases h2 : k < x
      · rw [ite_eq_left h2] at h
        exact Or.inr (Or.inr (occ_of_mem h))
      · exact Or.inr (Or.inl (by omega))

theorem all_spec : ∀ {t : Tree} {p : Nat → Bool} {x : Nat}, t.all p = true → t.Occ x → p x = true
  | leaf, _, _, _, h => absurd h id
  | node l k r, p, x, h, hx => by
    simp only [all, Bool.and_eq_true] at h
    rcases hx with hx | hx | hx
    · exact all_spec h.1.1 hx
    · rw [hx]; exact h.1.2
    · exact all_spec h.2 hx

end Tree

/-- The union of the masks of the vertices of `pre`. -/
def dom (mask : Nat → Nat) (pre : List Nat) : Nat := pre.foldl (fun D u => D ||| mask u) 0

theorem dom_append_single (mask : Nat → Nat) (pre : List Nat) (v : Nat) :
    dom mask (pre ++ [v]) = dom mask pre ||| mask v := by
  simp [dom, List.foldl_append]

theorem testBit_foldl_or (mask : Nat → Nat) (pre : List Nat) (D w : Nat) :
    (pre.foldl (fun D u => D ||| mask u) D).testBit w =
      (D.testBit w || pre.any fun u => (mask u).testBit w) := by
  induction pre generalizing D with
  | nil => simp
  | cons u pre ih => simp [List.foldl_cons, ih, Nat.testBit_or, Bool.or_assoc]

theorem testBit_dom (mask : Nat → Nat) (pre : List Nat) (w : Nat) :
    (dom mask pre).testBit w = pre.any fun u => (mask u).testBit w := by
  simp [dom, testBit_foldl_or, Nat.zero_testBit]

/-- A legal step adds a new bit to the dominated mask. -/
theorem new_bit (G : FinGraph) (mask : Nat → Nat)
    (hmask : ∀ v, v < G.n → ∀ w, w < G.n → (mask v).testBit w = G.cl v w)
    (pre : List Nat) (hpre : ∀ u ∈ pre, u < G.n) (v : Nat) (hv : v < G.n)
    (h : ∃ w, w < G.n ∧ (G.cl v w = true ∧ ∀ u ∈ pre, G.cl u w = false)) :
    (dom mask pre ||| mask v) ≠ dom mask pre := by
  obtain ⟨w, hw, hvw, hpw⟩ := h
  intro heq
  have h1 : (dom mask pre ||| mask v).testBit w = true := by
    rw [Nat.testBit_or, hmask v hv w hw, hvw, Bool.or_true]
  have h2 : (dom mask pre).testBit w = false := by
    rw [testBit_dom, List.any_eq_false]
    intro u hu
    rw [hmask u (hpre u hu) w hw, hpw u hu]
    simp
  rw [heq, h2] at h1
  exact Bool.false_ne_true h1

/-- Every successor of a mask in `t` that dominates something new lies in `t'`. -/
def closedInto (n : Nat) (mask : Nat → Nat) (t t' : Tree) : Bool :=
  t.all fun D => (List.range n).all fun v => (D ||| mask v) == D || t'.mem (D ||| mask v)

/-- The certificate condition for layers `Ls = [L₀, …, L_m]`. -/
def certified (n : Nat) (mask : Nat → Nat) (Ls : List Tree) : Bool :=
  (Ls.getD 0 .leaf).mem 0 &&
    (List.range Ls.length).all fun k => closedInto n mask (Ls.getD k .leaf) (Ls.getD (k + 1) .leaf)

theorem layer_lt_length {Ls : List Tree} {k D : Nat} (h : (Ls.getD k .leaf).Occ D) : k < Ls.length := by
  apply Nat.lt_of_not_le
  intro hk
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hk] at h
  exact h

theorem occ_succ (G : FinGraph) (mask : Nat → Nat) (Ls : List Tree)
    (hc : certified G.n mask Ls = true) (k D v : Nat) (hD : (Ls.getD k .leaf).Occ D)
    (hv : v < G.n) (hnew : (D ||| mask v) ≠ D) : (Ls.getD (k + 1) .leaf).Occ (D ||| mask v) := by
  simp only [certified, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  have hk := hc.2 k (layer_lt_length hD)
  have h1 := Tree.all_spec hk hD
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, beq_iff_eq] at h1
  rcases h1 v hv with h | h
  · exact absurd h hnew
  · exact Tree.occ_of_mem h

/-- Every legal continuation stays inside the layers. -/
theorem occ_layers (G : FinGraph) (mask : Nat → Nat)
    (hmask : ∀ v, v < G.n → ∀ w, w < G.n → (mask v).testBit w = G.cl v w)
    (Ls : List Tree) (hc : certified G.n mask Ls = true) :
    ∀ (l pre : List Nat) (k : Nat), G.LegalFrom pre l → (∀ u ∈ pre, u < G.n) →
      (Ls.getD k .leaf).Occ (dom mask pre) →
      (Ls.getD (k + l.length) .leaf).Occ (dom mask (pre ++ l))
  | [], pre, k, _, _, hocc => by simpa using hocc
  | v :: l, pre, k, ⟨hv, hnew, hl⟩, hpre, hocc => by
    have hpre' : ∀ u ∈ pre ++ [v], u < G.n := by
      intro u hu
      rcases List.mem_append.1 hu with hu | hu
      · exact hpre u hu
      · rw [List.mem_singleton.1 hu]; exact hv
    have hocc' : (Ls.getD (k + 1) .leaf).Occ (dom mask (pre ++ [v])) := by
      rw [dom_append_single]
      exact occ_succ G mask Ls hc k _ v hocc hv (new_bit G mask hmask pre hpre v hv hnew)
    have := occ_layers G mask hmask Ls hc l (pre ++ [v]) (k + 1) hl hpre' hocc'
    simpa [Nat.add_assoc, Nat.add_comm 1, List.append_assoc] using this

/-- A certificate with layers `L₀, …, L_m` bounds every legal sequence by `m`. -/
theorem legal_length_le (G : FinGraph) (mask : Nat → Nat)
    (hmask : ∀ v, v < G.n → ∀ w, w < G.n → (mask v).testBit w = G.cl v w)
    (Ls : List Tree) (hc : certified G.n mask Ls = true) (l : List Nat) (hl : G.Legal l) :
    l.length + 1 ≤ Ls.length := by
  have h0 : (Ls.getD 0 .leaf).Occ (dom mask []) := by
    simp only [certified, Bool.and_eq_true] at hc
    exact Tree.occ_of_mem hc.1
  have := occ_layers G mask hmask Ls hc l [] 0 hl (by simp) h0
  rw [Nat.zero_add] at this
  exact layer_lt_length this

end GrundyStrong
