module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.GhostTruncatedKernel
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.MemPerm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The truncated ghost row of `Graph/` as a sum over terminated sets and batches

Source: `verification/stage7-sources/S-02.tex`, lines 456–475 (`[S-02:0456–0475]`),
(eq:ghost-row).

`Graph.finiteGhostTruncatedRow` is a sum over the target degree `m` and the number `k` of
survivors of the sector rows `Graph.finiteGhostSectorRow`, in which the survivors are enumerated
through `Graph.retrievalCoordinates` and the degrees are transported by `Graph.memoryDegreeEquiv`.
This file rewrites it, for a test function which only depends on the list of the particles up to
permutation, in the form of (eq:ghost-row):

`∑_{s ⊆ {1, …, n}} ∑_{b ≤ N} 1[n - |s| + b ≤ N] · ghostListTerm s b`,

where `ghostListTerm s b = D^{|s|} A^{|Z| - |s|} C^b / b! ∑_{q ∈ P^b} ∏ ν(q_h) · G(𝐳 ∖ s, (q, 0))` if
all positions of `s` are pending zeros, and `0` otherwise (`truncatedRow_list`). The survivors
`𝐳 ∖ s` are listed in the order of their indices (`ghostSurvList`).

* `retrieval_survivors_perm` — the survivors of `Graph.retrievalCoordinates` are a permutation of
  `ghostSurvList`.
* `subsetCoefficient_list`, `sectorRow_list`, `degreeRow_list` — the three layers of `Graph/`.
* `ghostLattice_sum` — the change of variables `(m, k) ↦ (a, b) = (n - k, m - k)`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### Lists of survivors -/

/-- The survivors of the tuple `x` after deleting the positions of `s`, in the order of their
indices. -/
def ghostSurvList {Z : Type*} {n : ℕ} (x : Fin n → Z) (s : Finset (Fin n)) : List Z :=
  ((List.finRange n).filter fun i => decide (i ∉ s)).map x

theorem ghostSurvList_length {Z : Type*} {n : ℕ} (x : Fin n → Z) (s : Finset (Fin n)) :
    (ghostSurvList x s).length = n - s.card := by
  unfold ghostSurvList
  rw [List.length_map]
  have hnd : ((List.finRange n).filter fun i => decide (i ∉ s)).Nodup :=
    (List.nodup_finRange n).filter _
  have htf : ((List.finRange n).filter fun i => decide (i ∉ s)).toFinset = sᶜ := by
    ext i
    simp
  rw [← List.toFinset_card_of_nodup hnd, htf, Finset.card_compl, Fintype.card_fin]

/-- The list of a concatenation of two tuples. -/
theorem ofFn_memoryJoin {Z : Type*} {k a : ℕ} (u : Fin k → Z) (p : Fin a → Z) :
    List.ofFn (Graph.memoryJoin u p) = List.ofFn u ++ List.ofFn p := by
  have h : Graph.memoryJoin u p = Fin.append u p := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [Graph.memoryJoin]
    · simp [Graph.memoryJoin]
  rw [h, List.ofFn_fin_append]

/-- The survivors of `Graph.retrievalCoordinates` (an arbitrary enumeration of the complement of
the selected positions) are a permutation of the survivors in the order of their indices. -/
theorem retrieval_survivors_perm {Z : Type*} {k a : ℕ} (e : Fin a ↪ Fin (k + a))
    (s : Finset (Fin (k + a))) (hs : Set.range e = (s : Set (Fin (k + a))))
    (x : Fin (k + a) → Z) :
    (List.ofFn (Graph.retrievalCoordinates e x).1).Perm (ghostSurvList x s) := by
  have h1 : List.ofFn (Graph.retrievalCoordinates e x).1 =
      (List.ofFn fun i : Fin k => ((Graph.retrievalComplementEquiv e).symm i).1).map x := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext fun i => Graph.retrievalCoordinates_survivor e x i)
  rw [h1]
  unfold ghostSurvList
  refine List.Perm.map x ((List.perm_ext_iff_of_nodup ?_ ?_).mpr fun i => ?_)
  · exact List.nodup_ofFn.mpr fun i j hij =>
      (Graph.retrievalComplementEquiv e).symm.injective (Subtype.ext hij)
  · exact (List.nodup_finRange _).filter _
  · rw [List.mem_ofFn', List.mem_filter]
    constructor
    · rintro ⟨j, rfl⟩
      refine ⟨List.mem_finRange _, decide_eq_true ?_⟩
      intro hmem
      have h2 : (((Graph.retrievalComplementEquiv e).symm j).1 : Fin (k + a)) ∈ Set.range e :=
        (Set.ext_iff.mp hs _).mpr hmem
      exact ((Graph.retrievalComplementEquiv e).symm j).2 h2
    · rintro ⟨_, hi⟩
      have hi' : i ∉ s := of_decide_eq_true hi
      have hmem : i ∈ (Set.range e)ᶜ := fun h => hi' ((Set.ext_iff.mp hs i).mp h)
      refine ⟨Graph.retrievalComplementEquiv e ⟨i, hmem⟩, ?_⟩
      show ((Graph.retrievalComplementEquiv e).symm (Graph.retrievalComplementEquiv e ⟨i, hmem⟩)).1 = i
      rw [Equiv.symm_apply_apply]

/-! ### The terms of (eq:ghost-row) -/

open _root_.Classical in
/-- **One term of the row (eq:ghost-row)** for a test function `G` of the list of particles: the
positions of `s` terminate and `b` particles are born at residue zero.
`D^{|s|} A^{|Z| - |s|} C^b / b! ∑_{q ∈ P^b} ∏_h ν(q_h) G(𝐳 ∖ s, (q_1, 0), …, (q_b, 0))` if every
position of `s` is a pending zero, and `0` otherwise. -/
def ghostListTerm {P K : Type*} {R : P → Type*} [Field K] [Fintype P] [∀ p, Zero (R p)]
    (ν : P → K) (A D C : K) (G : List (Σ p, R p) → K) {n : ℕ} (x : Fin n → Σ p, R p)
    (s : Finset (Fin n)) (b : ℕ) : K :=
  if ∀ i ∈ s, (x i).2 = 0 then
    D ^ s.card * A ^ (Graph.ghostZeroCount x - s.card) * (C ^ b / (b.factorial : K)) *
      ∑ q : Fin b → P, (∏ j, ν (q j)) *
        G (ghostSurvList x s ++ List.ofFn fun j => (⟨q j, 0⟩ : Σ p, R p))
  else 0

theorem ghostListTerm_of_zero {P K : Type*} {R : P → Type*} [Field K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A D C : K) (G : List (Σ p, R p) → K) {n : ℕ}
    (x : Fin n → Σ p, R p) (s : Finset (Fin n)) (b : ℕ) (hz : ∀ i ∈ s, (x i).2 = 0) :
    ghostListTerm ν A D C G x s b =
      D ^ s.card * A ^ (Graph.ghostZeroCount x - s.card) * (C ^ b / (b.factorial : K)) *
        ∑ q : Fin b → P, (∏ j, ν (q j)) *
          G (ghostSurvList x s ++ List.ofFn fun j => (⟨q j, 0⟩ : Σ p, R p)) := by
  unfold ghostListTerm
  exact if_pos hz

theorem ghostListTerm_of_not_zero {P K : Type*} {R : P → Type*} [Field K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A D C : K) (G : List (Σ p, R p) → K) {n : ℕ}
    (x : Fin n → Σ p, R p) (s : Finset (Fin n)) (b : ℕ) (hz : ¬∀ i ∈ s, (x i).2 = 0) :
    ghostListTerm ν A D C G x s b = 0 := by
  unfold ghostListTerm
  exact if_neg hz

/-! ### The three layers of `Graph/` -/

open _root_.Classical in
/-- The deletion coefficient of `Graph/` for a test function of the list of particles. -/
theorem subsetCoefficient_list {P K : Type*} {R : P → Type*} [Field K] [Fintype P]
    [∀ p, Zero (R p)] {k a b : ℕ} (ν : P → K) (A : K) (G : List (Σ p, R p) → K)
    (hG : ∀ l₁ l₂ : List (Σ p, R p), l₁.Perm l₂ → G l₁ = G l₂)
    (s : Finset (Fin (k + a))) (x : Fin (k + a) → Σ p, R p) :
    Graph.finiteGhostSubsetCoefficient (b := b) ν A
        (fun _ (y : Fin (k + b) → Σ p, R p) => G (List.ofFn y)) s x =
      if s.card = a ∧ ∀ i ∈ s, (x i).2 = 0 then
        A ^ (Graph.ghostZeroCount x - a) *
          ∑ q : Fin b → P, (∏ j, ν (q j)) *
            G (ghostSurvList x s ++ List.ofFn fun j => (⟨q j, 0⟩ : Σ p, R p))
      else 0 := by
  unfold Graph.finiteGhostSubsetCoefficient
  by_cases hs : s.card = a
  · rw [dif_pos hs]
    by_cases hz : ∀ i ∈ s, (x i).2 = 0
    · rw [if_pos hz, if_pos (And.intro hs hz)]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      congr 1
      show G (List.ofFn (Graph.memoryJoin _ _)) = _
      rw [ofFn_memoryJoin]
      exact hG _ _ ((retrieval_survivors_perm (Graph.subsetRetrieval s hs) s
        (Graph.subsetRetrieval_set_range s hs) x).append_right _)
    · rw [if_neg hz, if_neg (fun h => hz h.2)]
  · rw [dif_neg hs, if_neg (fun h => hs h.1)]

open _root_.Classical in
/-- The sector row of `Graph/` for a test function of the list of particles. -/
theorem sectorRow_list {P K : Type*} {R : P → Type*} [Field K] [CharZero K] [Fintype P]
    [∀ p, Zero (R p)] {k a b : ℕ} (ν : P → K) (A D C : K) (G : List (Σ p, R p) → K)
    (hG : ∀ l₁ l₂ : List (Σ p, R p), l₁.Perm l₂ → G l₁ = G l₂)
    (x : Fin (k + a) → Σ p, R p) :
    Graph.finiteGhostSectorRow (b := b) ν A D C
        (fun y : Fin (k + b) → Σ p, R p => G (List.ofFn y)) x =
      (D ^ a * C ^ b) / (b.factorial : K) *
        ∑ s : Finset (Fin (k + a)),
          if s.card = a ∧ ∀ i ∈ s, (x i).2 = 0 then
            A ^ (Graph.ghostZeroCount x - a) *
              ∑ q : Fin b → P, (∏ j, ν (q j)) *
                G (ghostSurvList x s ++ List.ofFn fun j => (⟨q j, 0⟩ : Σ p, R p))
          else 0 := by
  unfold Graph.finiteGhostSectorRow
  congr 1
  exact Finset.sum_congr rfl fun s _ => subsetCoefficient_list ν A G hG s x

open _root_.Classical in
/-- The degree row of `Graph/` for a test function of the list of particles: the degree casts
disappear. -/
theorem degreeRow_list {P K : Type*} {R : P → Type*} [Field K] [CharZero K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A D C : K) (G : List (Σ p, R p) → K)
    (hG : ∀ l₁ l₂ : List (Σ p, R p), l₁.Perm l₂ → G l₁ = G l₂) (k n m : ℕ)
    (hk : k ≤ n ∧ k ≤ m) (x : Fin n → Σ p, R p) :
    Graph.finiteGhostDegreeRow ν A D C k n m
        (fun y : Fin m → Σ p, R p => G (List.ofFn y)) x =
      (D ^ (n - k) * C ^ (m - k)) / ((m - k).factorial : K) *
        ∑ s : Finset (Fin n),
          if s.card = n - k ∧ ∀ i ∈ s, (x i).2 = 0 then
            A ^ (Graph.ghostZeroCount x - (n - k)) *
              ∑ q : Fin (m - k) → P, (∏ j, ν (q j)) *
                G (ghostSurvList x s ++ List.ofFn fun j => (⟨q j, 0⟩ : Σ p, R p))
          else 0 := by
  have key : ∀ (a b : ℕ) (ha : k + a = n) (hb : k + b = m),
      Graph.finiteGhostSectorRow (k := k) (a := a) (b := b) ν A D C
          (fun z => (fun y : Fin m → Σ p, R p => G (List.ofFn y)) (Graph.memoryDegreeEquiv hb z))
          ((Graph.memoryDegreeEquiv ha).symm x) =
        (D ^ a * C ^ b) / (b.factorial : K) *
          ∑ s : Finset (Fin n),
            if s.card = a ∧ ∀ i ∈ s, (x i).2 = 0 then
              A ^ (Graph.ghostZeroCount x - a) *
                ∑ q : Fin b → P, (∏ j, ν (q j)) *
                  G (ghostSurvList x s ++ List.ofFn fun j => (⟨q j, 0⟩ : Σ p, R p))
            else 0 := by
    intro a b ha hb
    subst ha
    subst hb
    exact sectorRow_list ν A D C G hG x
  unfold Graph.finiteGhostDegreeRow
  rw [dif_pos hk]
  exact key (n - k) (m - k) _ _

/-! ### The change of variables `(m, k) ↦ (a, b) = (n - k, m - k)` -/

/-- The sum over the target degrees `m ≤ N` and the survivor numbers `k ≤ min n m` with
`n - k = a` is the sum over the numbers `b = m - k` of births with `n - a + b ≤ N`. -/
theorem ghostLattice_sum {M : Type*} [AddCommMonoid M] (N n a : ℕ) (ha : a ≤ n) (f : ℕ → M) :
    (∑ m : Fin (N + 1), ∑ k ∈ Finset.range (min n m.val + 1),
        if a = n - k then f (m.val - k) else 0) =
      ∑ b : Fin (N + 1), if n - a + b.val ≤ N then f b.val else 0 := by
  have inner : ∀ m : ℕ,
      (∑ k ∈ Finset.range (min n m + 1), if a = n - k then f (m - k) else 0) =
        if n - a ≤ m then f (m - (n - a)) else 0 := by
    intro m
    by_cases hm : n - a ≤ m
    · rw [if_pos hm, Finset.sum_eq_single_of_mem (n - a)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le (le_min (Nat.sub_le n a) hm)))]
      · exact if_pos (by omega)
      · intro k hk hne
        obtain ⟨hk1, _⟩ := le_min_iff.mp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
        exact if_neg (by omega)
    · rw [if_neg hm]
      refine Finset.sum_eq_zero fun k hk => ?_
      obtain ⟨_, hk2⟩ := le_min_iff.mp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
      exact if_neg (by omega)
  have e0 : (∑ m : Fin (N + 1), ∑ k ∈ Finset.range (min n m.val + 1),
        if a = n - k then f (m.val - k) else 0) =
      ∑ m : Fin (N + 1), if n - a ≤ m.val then f (m.val - (n - a)) else 0 :=
    Finset.sum_congr rfl fun m _ => inner m.val
  have e1 : (∑ m : Fin (N + 1), if n - a ≤ m.val then f (m.val - (n - a)) else 0) =
      ∑ m ∈ Finset.range (N + 1), if n - a ≤ m then f (m - (n - a)) else 0 :=
    (Finset.sum_range fun m => if n - a ≤ m then f (m - (n - a)) else 0).symm
  have e2 : (∑ b : Fin (N + 1), if n - a + b.val ≤ N then f b.val else 0) =
      ∑ b ∈ Finset.range (N + 1), if n - a + b ≤ N then f b else 0 :=
    (Finset.sum_range fun b => if n - a + b ≤ N then f b else 0).symm
  rw [e0, e1, e2, ← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun m => m - (n - a)) (fun b => b + (n - a)) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    have h1 := Finset.mem_filter.mp hm
    have h2 : m < N + 1 := Finset.mem_range.mp h1.1
    have h3 : n - a ≤ m := h1.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega : m - (n - a) < N + 1),
        (by omega : n - a + (m - (n - a)) ≤ N)⟩
  · intro b hb
    have h1 := Finset.mem_filter.mp hb
    have h2 : b < N + 1 := Finset.mem_range.mp h1.1
    have h3 : n - a + b ≤ N := h1.2
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega : b + (n - a) < N + 1), (by omega : n - a ≤ b + (n - a))⟩
  · intro m hm
    have h3 : n - a ≤ m := (Finset.mem_filter.mp hm).2
    show m - (n - a) + (n - a) = m
    omega
  · intro b _
    show b + (n - a) - (n - a) = b
    omega
  · intro m _
    rfl

/-! ### The truncated row -/

/-- **The truncated ghost row of `Graph/` in the form (eq:ghost-row)**: for a test function `H`
which is a function `G` of the list of the particles up to permutation,
`Graph.finiteGhostTruncatedRow` is the sum over the terminated sets `s` and the numbers `b ≤ N` of
births with `n - |s| + b ≤ N` of the terms `ghostListTerm`. -/
theorem truncatedRow_list {P K : Type*} {R : P → Type*} [Field K] [CharZero K] [Fintype P]
    [∀ p, Zero (R p)] (ν : P → K) (A D C : K) (G : List (Σ p, R p) → K)
    (hG : ∀ l₁ l₂ : List (Σ p, R p), l₁.Perm l₂ → G l₁ = G l₂) (N : ℕ)
    (H : Graph.FiniteMemory N (Σ p, R p) → K)
    (hH : ∀ (m : Fin (N + 1)) (y : Fin m.val → Σ p, R p), H ⟨m, y⟩ = G (List.ofFn y))
    (x : Graph.FiniteMemory N (Σ p, R p)) :
    Graph.finiteGhostTruncatedRow ν A D C N H x =
      ∑ s : Finset (Fin x.1.val), ∑ b : Fin (N + 1),
        if x.1.val - s.card + b.val ≤ N then ghostListTerm ν A D C G x.2 s b.val else 0 := by
  have h1 : ∀ (m : Fin (N + 1)) (k : ℕ), k ∈ Finset.range (min x.1.val m.val + 1) →
      Graph.finiteGhostDegreeRow ν A D C k x.1.val m.val (fun y => H ⟨m, y⟩) x.2 =
        ∑ s : Finset (Fin x.1.val),
          if s.card = x.1.val - k then ghostListTerm ν A D C G x.2 s (m.val - k) else 0 := by
    intro m k hk
    have hk' : k ≤ x.1.val ∧ k ≤ m.val :=
      le_min_iff.mp (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
    have hfun : (fun y : Fin m.val → Σ p, R p => H ⟨m, y⟩) = fun y => G (List.ofFn y) :=
      funext fun y => hH m y
    rw [hfun, degreeRow_list ν A D C G hG k x.1.val m.val hk' x.2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hs : s.card = x.1.val - k
    · rw [if_pos hs]
      by_cases hz : ∀ i ∈ s, (x.2 i).2 = 0
      · rw [if_pos (And.intro hs hz), ghostListTerm_of_zero ν A D C G x.2 s _ hz, hs]
        ring
      · rw [if_neg (fun h => hz h.2), ghostListTerm_of_not_zero ν A D C G x.2 s _ hz,
          mul_zero]
    · rw [if_neg hs, if_neg (fun h => hs h.1), mul_zero]
  calc Graph.finiteGhostTruncatedRow ν A D C N H x
      = ∑ m : Fin (N + 1), ∑ k ∈ Finset.range (min x.1.val m.val + 1),
          Graph.finiteGhostDegreeRow ν A D C k x.1.val m.val (fun y => H ⟨m, y⟩) x.2 := rfl
    _ = ∑ m : Fin (N + 1), ∑ k ∈ Finset.range (min x.1.val m.val + 1),
          ∑ s : Finset (Fin x.1.val),
            if s.card = x.1.val - k then ghostListTerm ν A D C G x.2 s (m.val - k) else 0 :=
        Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k hk => h1 m k hk
    _ = ∑ m : Fin (N + 1), ∑ s : Finset (Fin x.1.val),
          ∑ k ∈ Finset.range (min x.1.val m.val + 1),
            if s.card = x.1.val - k then ghostListTerm ν A D C G x.2 s (m.val - k) else 0 :=
        Finset.sum_congr rfl fun m _ => Finset.sum_comm
    _ = ∑ s : Finset (Fin x.1.val), ∑ m : Fin (N + 1),
          ∑ k ∈ Finset.range (min x.1.val m.val + 1),
            if s.card = x.1.val - k then ghostListTerm ν A D C G x.2 s (m.val - k) else 0 :=
        Finset.sum_comm
    _ = ∑ s : Finset (Fin x.1.val), ∑ b : Fin (N + 1),
          if x.1.val - s.card + b.val ≤ N then ghostListTerm ν A D C G x.2 s b.val else 0 :=
        Finset.sum_congr rfl fun s _ =>
          ghostLattice_sum N x.1.val s.card
            ((Finset.card_le_univ s).trans_eq (Fintype.card_fin _))
            (fun b => ghostListTerm ν A D C G x.2 s b)

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
