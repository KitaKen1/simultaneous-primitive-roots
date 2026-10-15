module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.GhostRowList
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Operators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The one-group ghost row of `Operators.lean` is the truncated ghost row of `Graph/`

Source: `verification/stage7-sources/S-02.tex`, lines 456–475 (`[S-02:0456–0475]`),
(eq:ghost-row).

`ghostRowCompat : GhostRowCompat` — for a function `H` of one group memory which is symmetric in
the particle indices, `ghostRowG` (`Operators.lean`) is `Graph.finiteGhostTruncatedRow`.

The identity only uses the shape of the coefficient, so it is proved for arbitrary weights `ν` and
coefficients `A, D, C` in a field of characteristic zero (`ghostRowGen`,
`ghostRowGen_eq_truncatedRow`); `GhostAbsoluteProof.lean` uses it for the real coefficients
`A, |D|, 2|C|` of the absolute kernel with doubled births.

## The comparison

Both rows are sums over a set of terminated positions, a number `b` of births and a batch of `b`
primes, with the same coefficient:

* here the terminated set is a subset `A ⊆ Z(𝐳)` of the `Bc` indices, and the new memory is
  `(𝐳 ∖ A, (p'_1, 0), …, (p'_b, 0))` with the survivors in the order of their indices;
* `Graph/` sums over the new degree `m` and the number `k` of survivors (`a = n - k` terminations,
  `b = m - k` births), the terminated set is a subset of the `n = k + a` indices of the memory, and
  the survivors are enumerated by `Graph.retrievalCoordinates`.

`GhostRowList.lean` brings the row of `Graph/` to the first form (`truncatedRow_list`);
`ghostRowGen_list` does the same for the row of this directory. A symmetric `H` does not see the
order of the survivors (`H_memOfList_perm`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-- A `filterMap` which keeps the elements outside `p` is a `filter` followed by a `map`. -/
theorem filterMap_ite_eq_map_filter {α β : Type*} (p : α → Prop) [DecidablePred p] (f : α → β)
    (l : List α) :
    l.filterMap (fun a => if p a then none else some (f a)) =
      (l.filter fun a => decide (¬p a)).map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    by_cases h : p a
    · rw [List.filterMap_cons_none (f := fun a => if p a then none else some (f a)) (a := a)
          (l := l) (if_pos h),
        List.filter_cons_of_neg (p := fun a => decide (¬p a)) (a := a) (l := l)
          (fun hd => of_decide_eq_true hd h), ih]
    · rw [List.filterMap_cons_some (f := fun a => if p a then none else some (f a)) (a := a)
          (l := l) (b := f a) (if_neg h),
        List.filter_cons_of_pos (p := fun a => decide (¬p a)) (a := a) (l := l)
          (decide_eq_true h), List.map_cons, ih]

section OneGroup

variable {S B : Type} {𝒢 : GroupFamily S B} {Bc : ℕ} {g : B}

/-! ### The general row -/

open _root_.Classical in
/-- The term of the general one-group row for the terminated set `A'` and the batch `β`:
`D^{|A'|} A^{|Z(𝐳)| - |A'|} C^b / b! ∏_h ν(p'_h) · H(𝐳 ∖ A', (p'_1, 0), …, (p'_b, 0))` if
`A' ⊆ Z(𝐳)` and the new memory has at most `Bc` particles, and `0` otherwise. -/
def ghostGenTerm {K : Type*} [Field K] (ν : {p : ℕ // p ∈ 𝒢.big g} → K) (A D C : K)
    (H : Mem 𝒢 Bc g → K) (z : Mem 𝒢 Bc g) (A' : Finset (Fin Bc)) (β : Batch 𝒢 Bc g) : K :=
  if ghostNewSize z (A', β) ≤ Bc then
    (if GhostValid z A' then
      D ^ A'.card * A ^ (memZeroCount z - A'.card) *
        (C ^ β.1.val / (β.1.val.factorial : K)) * ∏ j, ν (β.2 j)
    else 0) * H (ghostNewMem z (A', β))
  else 0

/-- **The row (eq:ghost-row) of one big group with arbitrary weights and coefficients**
[S-02:0460–0472]: `ghostRowG` is the case `ν = μ̃_g`, `A = q_i/ρ²`, `D = -η_i/ρ`, `C = V_g D`. -/
def ghostRowGen {K : Type*} [Field K] (ν : {p : ℕ // p ∈ 𝒢.big g} → K) (A D C : K)
    (H : Mem 𝒢 Bc g → K) (z : Mem 𝒢 Bc g) : K :=
  ∑ c : Finset (Fin Bc) × Batch 𝒢 Bc g, ghostGenTerm ν A D C H z c.1 c.2

/-! ### Symmetric functions and lists -/

/-- A function of a memory which is symmetric in the particle indices takes the same value on the
memories of two lists which are permutations of each other. -/
theorem H_memOfList_perm {K : Type*} (H : Mem 𝒢 Bc g → K)
    (hH : ∀ (m : Fin (Bc + 1)) (σ : Equiv.Perm (Fin m.val)) (y : Fin m.val → Particle 𝒢 g),
      H ⟨m, y ∘ σ⟩ = H ⟨m, y⟩) {l₁ l₂ : List (Particle 𝒢 g)} (h : l₁.Perm l₂) :
    H (memOfList l₁) = H (memOfList l₂) := by
  obtain ⟨σ, hσ⟩ := exists_perm_mem (memOfList_perm (Bc := Bc) h)
  rw [hσ]
  exact hH _ σ _

/-- A memory is the memory of the list of its particles. -/
theorem H_mk_eq {K : Type*} (H : Mem 𝒢 Bc g → K) (m : Fin (Bc + 1))
    (y : Fin m.val → Particle 𝒢 g) : H ⟨m, y⟩ = H (memOfList (List.ofFn y)) := by
  have hlen : (List.ofFn y).length ≤ Bc := by
    rw [List.length_ofFn]
    exact Nat.le_of_lt_succ m.isLt
  exact congrArg H (mem_ext_ofFn _ _ (ofFn_memOfList hlen).symm)

/-! ### Subsets of the first `n` indices -/

/-- The subsets of the first `n` indices, as subsets of all `Bc` indices. -/
def liftSetEmb {n Bc : ℕ} (h : n ≤ Bc) : Finset (Fin n) ↪ Finset (Fin Bc) :=
  ⟨fun s => s.map (Fin.castLEEmb h), Finset.map_injective (Fin.castLEEmb h)⟩

theorem memAt_castLE {n : ℕ} (hn : n < Bc + 1) (hnB : n ≤ Bc) (x : Fin n → Particle 𝒢 g)
    (j : Fin n) :
    memAt (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) (Fin.castLEEmb hnB j) = some (x j) := by
  unfold memAt
  exact dif_pos j.isLt

/-- A set of indices of pending zeros is a set of indices of the memory. -/
theorem ghostValid_mem_lift {n : ℕ} (hn : n < Bc + 1) (hnB : n ≤ Bc) (x : Fin n → Particle 𝒢 g)
    {A' : Finset (Fin Bc)} (hv : GhostValid (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) A') :
    A' ∈ Finset.univ.map (liftSetEmb hnB) := by
  refine Finset.mem_map.mpr
    ⟨Finset.univ.filter (fun j : Fin n => Fin.castLEEmb hnB j ∈ A'), Finset.mem_univ _, ?_⟩
  show (Finset.univ.filter fun j : Fin n => Fin.castLEEmb hnB j ∈ A').map (Fin.castLEEmb hnB) = A'
  ext i
  rw [Finset.mem_map]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact (Finset.mem_filter.mp hj).2
  · intro hi
    obtain ⟨pr, hpr, _⟩ := hv i hi
    have hlt : i.val < n := by
      by_contra hcon
      have h4 : memAt (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) i = none := by
        unfold memAt
        exact dif_neg hcon
      rw [h4] at hpr
      cases hpr
    exact ⟨⟨i.val, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, Fin.ext rfl⟩

theorem ghostValid_lift {n : ℕ} (hn : n < Bc + 1) (hnB : n ≤ Bc) (x : Fin n → Particle 𝒢 g)
    (s : Finset (Fin n)) :
    GhostValid (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) (s.map (Fin.castLEEmb hnB)) ↔
      ∀ i ∈ s, (x i).2 = 0 := by
  unfold GhostValid
  constructor
  · intro h i hi
    obtain ⟨pr, hpr, h0⟩ := h (Fin.castLEEmb hnB i) (Finset.mem_map_of_mem _ hi)
    have e : x i = pr := Option.some.inj ((memAt_castLE hn hnB x i).symm.trans hpr)
    subst e
    exact h0
  · intro h j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    exact ⟨x i, memAt_castLE hn hnB x i, h i hi⟩

/-- The surviving particles, in the order of their indices. -/
theorem ghostSurvivors_lift_perm {n : ℕ} (hn : n < Bc + 1) (hnB : n ≤ Bc)
    (x : Fin n → Particle 𝒢 g) (s : Finset (Fin n)) :
    (ghostSurvivors (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) (s.map (Fin.castLEEmb hnB))).Perm
      (ghostSurvList x s) := by
  have hperm : (List.finRange Bc).Perm
      ((List.finRange n).map (Fin.castLEEmb hnB) ++
        (List.finRange Bc).filter fun i => decide (n ≤ i.val)) := by
    refine (List.perm_ext_iff_of_nodup (List.nodup_finRange Bc) ?_).mpr fun i => ?_
    · refine List.Nodup.append ((List.nodup_finRange n).map (Fin.castLEEmb hnB).injective)
        ((List.nodup_finRange Bc).filter _) (List.disjoint_left.mpr fun i hi1 hi2 => ?_)
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi1
      have h3 : n ≤ (Fin.castLEEmb hnB j).val := of_decide_eq_true (List.mem_filter.mp hi2).2
      exact absurd j.isLt (not_lt.mpr h3)
    · refine iff_of_true (List.mem_finRange i) (List.mem_append.mpr ?_)
      by_cases hi : i.val < n
      · exact Or.inl (List.mem_map.mpr ⟨⟨i.val, hi⟩, List.mem_finRange _, Fin.ext rfl⟩)
      · exact Or.inr (List.mem_filter.mpr ⟨List.mem_finRange i, decide_eq_true (not_lt.mp hi)⟩)
  have hnone : ((List.finRange Bc).filter fun i => decide (n ≤ i.val)).filterMap
      (fun i => if i ∈ s.map (Fin.castLEEmb hnB) then none
        else memAt (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) i) = [] := by
    refine List.filterMap_eq_nil_iff.mpr fun i hi => ?_
    have h3 : n ≤ i.val := of_decide_eq_true (List.mem_filter.mp hi).2
    have h4 : memAt (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) i = none := by
      unfold memAt
      exact dif_neg (not_lt.mpr h3)
    show (if i ∈ s.map (Fin.castLEEmb hnB) then none
      else memAt (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) i) = none
    rw [h4]
    exact ite_self _
  have hcomp : ((fun i => if i ∈ s.map (Fin.castLEEmb hnB) then none
        else memAt (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) i) ∘ ⇑(Fin.castLEEmb hnB)) =
      fun j => if j ∈ s then none else some (x j) := by
    funext j
    show (if Fin.castLEEmb hnB j ∈ s.map (Fin.castLEEmb hnB) then none
      else memAt (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) (Fin.castLEEmb hnB j)) =
        if j ∈ s then none else some (x j)
    rw [memAt_castLE hn hnB x j]
    exact ite_congr_of_iff (Finset.mem_map' (Fin.castLEEmb hnB)) rfl rfl
  unfold ghostSurvivors
  refine (hperm.filterMap _).trans ?_
  rw [List.filterMap_append, hnone, List.append_nil, List.filterMap_map, hcomp,
    filterMap_ite_eq_map_filter]
  exact List.Perm.refl _

/-! ### The row in the form of `truncatedRow_list` -/

open _root_.Classical in
/-- The term of the general row for a set of indices of the memory. -/
theorem ghostGenTerm_lift {K : Type*} [Field K] (ν : {p : ℕ // p ∈ 𝒢.big g} → K) (A D C : K)
    (H : Mem 𝒢 Bc g → K)
    (hH : ∀ (m : Fin (Bc + 1)) (σ : Equiv.Perm (Fin m.val)) (y : Fin m.val → Particle 𝒢 g),
      H ⟨m, y ∘ σ⟩ = H ⟨m, y⟩)
    {n : ℕ} (hn : n < Bc + 1) (hnB : n ≤ Bc) (x : Fin n → Particle 𝒢 g) (s : Finset (Fin n))
    (b : Fin (Bc + 1)) (p' : Fin b.val → {p : ℕ // p ∈ 𝒢.big g}) :
    ghostGenTerm ν A D C H (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) (s.map (Fin.castLEEmb hnB)) ⟨b, p'⟩ =
      if n - s.card + b.val ≤ Bc then
        (if ∀ i ∈ s, (x i).2 = 0 then
          D ^ s.card * A ^ (Graph.ghostZeroCount x - s.card) *
            (C ^ b.val / (b.val.factorial : K)) * ∏ j, ν (p' j)
        else 0) *
          H (memOfList (ghostSurvList x s ++ List.ofFn fun j => (⟨p' j, 0⟩ : Particle 𝒢 g)))
      else 0 := by
  have hperm := ghostSurvivors_lift_perm (𝒢 := 𝒢) (g := g) hn hnB x s
  have hsz : ghostNewSize (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) (s.map (Fin.castLEEmb hnB), ⟨b, p'⟩) =
      n - s.card + b.val := by
    show (ghostSurvivors (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) (s.map (Fin.castLEEmb hnB))).length +
      b.val = _
    rw [hperm.length_eq, ghostSurvList_length]
  have hH' : H (ghostNewMem (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) (s.map (Fin.castLEEmb hnB), ⟨b, p'⟩)) =
      H (memOfList (ghostSurvList x s ++ List.ofFn fun j => (⟨p' j, 0⟩ : Particle 𝒢 g))) :=
    H_memOfList_perm H hH (hperm.append_right _)
  unfold ghostGenTerm
  rw [hsz, hH', Finset.card_map]
  by_cases hsize : n - s.card + b.val ≤ Bc
  · rw [if_pos hsize, if_pos hsize]
    congr 1
    exact ite_congr_of_iff (ghostValid_lift hn hnB x s) rfl rfl
  · rw [if_neg hsize, if_neg hsize]

/-- **The general row as a sum over the subsets of the indices of the memory and the numbers of
births**, with the terms `ghostListTerm` of `GhostRowList.lean`. -/
theorem ghostRowGen_list {K : Type*} [Field K] (ν : {p : ℕ // p ∈ 𝒢.big g} → K) (A D C : K)
    (H : Mem 𝒢 Bc g → K)
    (hH : ∀ (m : Fin (Bc + 1)) (σ : Equiv.Perm (Fin m.val)) (y : Fin m.val → Particle 𝒢 g),
      H ⟨m, y ∘ σ⟩ = H ⟨m, y⟩)
    {n : ℕ} (hn : n < Bc + 1) (x : Fin n → Particle 𝒢 g) :
    ghostRowGen ν A D C H (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) =
      ∑ s : Finset (Fin n), ∑ b : Fin (Bc + 1),
        if n - s.card + b.val ≤ Bc then
          ghostListTerm ν A D C (fun l => H (memOfList l)) x s b.val
        else 0 := by
  have hnB : n ≤ Bc := Nat.le_of_lt_succ hn
  have h1 : ghostRowGen ν A D C H (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) =
      ∑ A' : Finset (Fin Bc), ∑ b : Fin (Bc + 1), ∑ p' : Fin b.val → {p : ℕ // p ∈ 𝒢.big g},
        ghostGenTerm ν A D C H (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) A' ⟨b, p'⟩ := by
    unfold ghostRowGen
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun A' _ => ?_
    exact Fintype.sum_sigma fun β : Batch 𝒢 Bc g =>
      ghostGenTerm ν A D C H (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) A' β
  have h2 : ∀ A' ∈ (Finset.univ : Finset (Finset (Fin Bc))),
      A' ∉ Finset.univ.map (liftSetEmb hnB) →
      (∑ b : Fin (Bc + 1), ∑ p' : Fin b.val → {p : ℕ // p ∈ 𝒢.big g},
        ghostGenTerm ν A D C H (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) A' ⟨b, p'⟩) = 0 := by
    intro A' _ hA'
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun p' _ => ?_
    have hnv : ¬GhostValid (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) A' :=
      fun hv => hA' (ghostValid_mem_lift hn hnB x hv)
    unfold ghostGenTerm
    rw [if_neg hnv, zero_mul]
    exact ite_self _
  rw [h1, ← Finset.sum_subset (Finset.subset_univ _) h2, Finset.sum_map]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun b _ => ?_
  show (∑ p' : Fin b.val → {p : ℕ // p ∈ 𝒢.big g},
      ghostGenTerm ν A D C H (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) (s.map (Fin.castLEEmb hnB)) ⟨b, p'⟩) = _
  by_cases hsize : n - s.card + b.val ≤ Bc
  · rw [if_pos hsize]
    by_cases hz : ∀ i ∈ s, (x i).2 = 0
    · rw [ghostListTerm_of_zero ν A D C _ x s b.val hz, Finset.mul_sum]
      refine Finset.sum_congr rfl fun p' _ => ?_
      rw [ghostGenTerm_lift ν A D C H hH hn hnB x s b p', if_pos hsize, if_pos hz]
      exact mul_assoc _ _ _
    · rw [ghostListTerm_of_not_zero ν A D C _ x s b.val hz]
      refine Finset.sum_eq_zero fun p' _ => ?_
      rw [ghostGenTerm_lift ν A D C H hH hn hnB x s b p', if_pos hsize, if_neg hz,
        zero_mul]
  · rw [if_neg hsize]
    refine Finset.sum_eq_zero fun p' _ => ?_
    rw [ghostGenTerm_lift ν A D C H hH hn hnB x s b p', if_neg hsize]

/-- **The general one-group row is the truncated ghost row of `Graph/`**, for arbitrary weights
and coefficients in a field of characteristic zero and every function which is symmetric in the
particle indices. -/
theorem ghostRowGen_eq_truncatedRow {K : Type*} [Field K] [CharZero K]
    (ν : {p : ℕ // p ∈ 𝒢.big g} → K) (A D C : K) (H : Mem 𝒢 Bc g → K)
    (hH : ∀ (m : Fin (Bc + 1)) (σ : Equiv.Perm (Fin m.val)) (y : Fin m.val → Particle 𝒢 g),
      H ⟨m, y ∘ σ⟩ = H ⟨m, y⟩) (z : Mem 𝒢 Bc g) :
    ghostRowGen ν A D C H z = Graph.finiteGhostTruncatedRow ν A D C Bc H z := by
  obtain ⟨⟨n, hn⟩, x⟩ := z
  exact (ghostRowGen_list ν A D C H hH hn x).trans
    (truncatedRow_list ν A D C (fun l => H (memOfList l))
      (fun _ _ h => H_memOfList_perm H hH h) Bc H (fun m y => H_mk_eq H m y)
      ⟨⟨n, hn⟩, x⟩).symm

/-! ### The row of `Operators.lean` -/

open _root_.Classical in
/-- The coefficient (eq:ghost-row) as a complex number. -/
theorem ghostCoefG_cast (𝒢 : GroupFamily S B) (q ρ : ℝ) (n i : ℕ) (g : B) (z : Mem 𝒢 Bc g)
    (A' : Finset (Fin Bc)) (β : Batch 𝒢 Bc g) :
    ((ghostCoefG 𝒢 q ρ n i g z (A', β) : ℝ) : ℂ) =
      if GhostValid z A' then
        ((Graph.sourceGhostD (visitQ q n i) ρ : ℝ) : ℂ) ^ A'.card *
          ((Graph.sourceGhostA (visitQ q n i) ρ : ℝ) : ℂ) ^ (memZeroCount z - A'.card) *
          (((Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ q n i) ρ :
            ℝ) : ℂ) ^ β.1.val / (β.1.val.factorial : ℂ)) *
          ∏ j, ((tiltLaw (𝒢.big g) q n (β.2 j) : ℝ) : ℂ)
      else 0 := by
  by_cases hv : GhostValid z A'
  · have h : ghostCoefG 𝒢 q ρ n i g z (A', β) =
        Graph.sourceGhostD (visitQ q n i) ρ ^ A'.card *
          Graph.sourceGhostA (visitQ q n i) ρ ^ (memZeroCount z - A'.card) *
          (Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ q n i) ρ ^
            β.1.val / (β.1.val.factorial : ℝ)) *
          ∏ j, tiltLaw (𝒢.big g) q n (β.2 j) := by
      unfold ghostCoefG
      exact if_pos hv
    rw [if_pos hv, h]
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_div,
      Complex.ofReal_natCast, Complex.ofReal_prod]
  · have h : ghostCoefG 𝒢 q ρ n i g z (A', β) = 0 := by
      unfold ghostCoefG
      exact if_neg hv
    rw [if_neg hv, h, Complex.ofReal_zero]

end OneGroup

/-- **`GhostRowCompat`** [S-02:0456–0475]: the ghost row of `Operators.lean` for one big group is
the truncated ghost row of `Graph/` on the functions which are symmetric in the particle
indices. -/
theorem ghostRowCompat : GhostRowCompat := by
  unfold GhostRowCompat
  intro S B _ _ _ _ 𝒢 q ρ n i Bc g H hH z
  rw [← ghostRowGen_eq_truncatedRow _ _ _ _ H hH z]
  unfold ghostRowG ghostRowGen
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨A', β⟩ := c
  show (if ghostNewSize z (A', β) ≤ Bc then
      ((ghostCoefG 𝒢 q ρ n i g z (A', β) : ℝ) : ℂ) * H (ghostNewMem z (A', β)) else 0) =
    ghostGenTerm _ _ _ _ H z A' β
  unfold ghostGenTerm
  refine ite_congr_of_iff Iff.rfl ?_ rfl
  refine congrArg (fun t => t * H (ghostNewMem z (A', β))) ?_
  exact (ghostCoefG_cast 𝒢 q ρ n i g z A' β).trans (ite_congr_of_iff Iff.rfl rfl rfl)

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
