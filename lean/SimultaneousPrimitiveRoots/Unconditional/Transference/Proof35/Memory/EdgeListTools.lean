module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.ChainSteps
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.GhostGroupEval
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.EdgeAbsCoef
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The new memory of one big group after an edge: products and members

Source: `verification/stage7-sources/S-02.tex`, lines 487–502 (`[S-02:0487–0502]`).

Tools for the proof of (M3) `EdgeStepFactor` (`Memory/EdgeStepFactorProof.lean`), for one big
group. The new memory of the group after an edge is the list `edgeAbsNewList Δ z x st pm`
(`Proof35/EdgeAbsCoef.lean`): the old particles which are not promoted, translated by `Δ`, then the
stored particles.

* `edg_prod_by_key` — a product over a list is the product over the keys `k` of the products of
  the entries with key `k`;
* `edg_prod_filterMap`, `edg_prod_stored`, `edg_prod_kept`, `edg_prod_newList` — a product over
  the new memory is a product over the old particles which are kept times a product over the
  stored slots;
* `edg_exists_newList` — the primes of the new memory;
* `edg_memAt_castLE`, `edg_memAt_eq_some` — the particles of a memory by index;
* `edg_rho_pow_countP`, `edg_rho_pow_memZeroCount`, `edg_rho_pow_memZeroCount_memOfList` — the
  factor `ρ^{#zeros}` as a product over the particles;
* `edg_size_le` — pending and active primes are distinct primes of the group.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### Lists -/

/-- A product over a list is the product over the keys `k` of the products of the entries with
key `k`. -/
theorem edg_prod_by_key {α κ : Type*} [Fintype κ] (key : α → κ) (f : α → ℝ) (l : List α)
    {inst : ∀ (a : α) (k : κ), Decidable (key a = k)} :
    (l.map f).prod = ∏ k : κ, (l.map fun a => @ite ℝ (key a = k) (inst a k) (f a) 1).prod := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have h : ∀ k : κ, ((a :: t).map fun a => @ite ℝ (key a = k) (inst a k) (f a) 1).prod =
        @ite ℝ (key a = k) (inst a k) (f a) 1 *
          (t.map fun a => @ite ℝ (key a = k) (inst a k) (f a) 1).prod :=
      fun k => by rw [List.map_cons, List.prod_cons]
    have h1 : ∏ k : κ, @ite ℝ (key a = k) (inst a k) (f a) 1 = f a := by
      refine (Fintype.prod_eq_single (key a) fun k hk => ?_).trans ?_
      · exact if_neg fun h => hk h.symm
      · exact if_pos rfl
    rw [List.map_cons, List.prod_cons, ih, Finset.prod_congr rfl fun k _ => h k,
      Finset.prod_mul_distrib, h1]

/-- The product over the values of a partial map on a list. -/
theorem edg_prod_filterMap {α β : Type*} (g : α → Option β) (f : β → ℝ) (l : List α) :
    ((l.filterMap g).map f).prod = (l.map fun a => (g a).elim 1 f).prod := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases h : g a with
    | none => simp [List.filterMap_cons_none h, h, ih]
    | some b => simp [List.filterMap_cons_some h, h, ih]

/-- A product over the slots of a set, in their canonical order. -/
theorem edg_prod_stored {J ℓ : ℕ} (st : Finset (Slot J ℓ)) (F : Slot J ℓ → ℝ) :
    (((slotList J ℓ).filter fun sl => decide (sl ∈ st)).map F).prod = ∏ sl ∈ st, F sl := by
  have hnd : ((slotList J ℓ).filter fun sl => decide (sl ∈ st)).Nodup :=
    (l38_slotList_nodup J ℓ).filter _
  have htf : ((slotList J ℓ).filter fun sl => decide (sl ∈ st)).toFinset = st := by
    ext sl
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨fun h => of_decide_eq_true h.2, fun h => ⟨l38_mem_slotList sl, decide_eq_true h⟩⟩
  rw [← List.prod_toFinset F hnd, htf]

variable {S B : Type} {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {g : B}

/-- `ρ^{#zeros}` as a product over the particles. -/
theorem edg_rho_pow_countP (ρ : ℝ) (l : List (Particle 𝒢 g)) :
    ρ ^ l.countP (fun w => decide (w.2 = 0)) = (l.map fun w => chnPow ρ (w.2 = 0)).prod := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.countP_cons, pow_add, ih, List.map_cons, List.prod_cons]
    by_cases ha : a.2 = 0
    · rw [if_pos (decide_eq_true ha), pow_one, chnPow_pos ha]
      exact mul_comm _ _
    · rw [if_neg (fun h => ha (of_decide_eq_true h)), pow_zero, chnPow_neg ha, mul_one,
        one_mul]

/-! ### The particles of a memory -/

/-- The particle with an index below the size. -/
theorem edg_memAt_castLE {n : ℕ} (hn : n < Bc + 1) (hnB : n ≤ Bc) (zf : Fin n → Particle 𝒢 g)
    (j : Fin n) : memAt (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) (Fin.castLE hnB j) = some (zf j) := by
  unfold memAt
  exact dif_pos j.isLt

/-- The particle with a given index. -/
theorem edg_memAt_eq_some {n : ℕ} (hn : n < Bc + 1) (zf : Fin n → Particle 𝒢 g) (j' : Fin Bc)
    (w : Particle 𝒢 g) :
    memAt (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) j' = some w ↔ ∃ h : j'.val < n, zf ⟨j'.val, h⟩ = w := by
  constructor
  · intro hm
    by_cases h : j'.val < n
    · have h1 : memAt (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) j' = some (zf ⟨j'.val, h⟩) := by
        unfold memAt
        exact dif_pos h
      exact ⟨h, Option.some.inj (h1.symm.trans hm)⟩
    · have h1 : memAt (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) j' = none := by
        unfold memAt
        exact dif_neg h
      rw [h1] at hm
      cases hm
  · rintro ⟨h, rfl⟩
    unfold memAt
    exact dif_pos h

/-- `ρ^{#zeros}` of a memory as a product over its particles. -/
theorem edg_rho_pow_memZeroCount (ρ : ℝ) (z : Mem 𝒢 Bc g) :
    ρ ^ memZeroCount z = ∏ j : Fin z.1.val, chnPow ρ ((z.2 j).2 = 0) := by
  rw [l38_memZeroCount_eq, edg_rho_pow_countP]
  exact ghStep_prod_map_ofFn z.2 fun w => chnPow ρ (w.2 = 0)

/-- `ρ^{#zeros}` of the memory of a list as a product over the list. -/
theorem edg_rho_pow_memZeroCount_memOfList (ρ : ℝ) {l : List (Particle 𝒢 g)}
    (h : l.length ≤ Bc) :
    ρ ^ memZeroCount (memOfList (Bc := Bc) l) = (l.map fun w => chnPow ρ (w.2 = 0)).prod := by
  rw [l38_memZeroCount_memOfList h, edg_rho_pow_countP]

/-! ### The new memory -/

/-- A product over the old particles which are kept, read through `memAt`. -/
theorem edg_prod_kept {n : ℕ} (hn : n < Bc + 1) (hnB : n ≤ Bc) (zf : Fin n → Particle 𝒢 g)
    (c : Fin Bc → Prop) [DecidablePred c] (sh : Particle 𝒢 g → Particle 𝒢 g)
    (f : Particle 𝒢 g → ℝ) :
    (((List.finRange Bc).filterMap fun j =>
        if c j then none else (memAt (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) j).map sh).map f).prod =
      ∏ j : Fin n, if c (Fin.castLE hnB j) then 1 else f (sh (zf j)) := by
  rw [edg_prod_filterMap, ← List.ofFn_eq_map, List.prod_ofFn]
  refine (Fintype.prod_of_injective (Fin.castLE hnB) (Fin.castLE_injective hnB) _ _ ?_ ?_).symm
  · intro j' hj'
    by_cases hc : c j'
    · rw [if_pos hc]
      rfl
    · have hlt : ¬j'.val < n := fun h => hj' (Set.mem_range.mpr ⟨⟨j'.val, h⟩, Fin.ext rfl⟩)
      have hm : memAt (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) j' = none := by
        unfold memAt
        exact dif_neg hlt
      rw [if_neg hc, hm]
      rfl
  · intro j
    by_cases hc : c (Fin.castLE hnB j)
    · rw [if_pos hc, if_pos hc]
      rfl
    · rw [if_neg hc, if_neg hc, edg_memAt_castLE hn hnB zf j]
      rfl

/-- **A product over the new memory of a group after an edge**: over the old particles which are
not promoted, translated, and over the stored slots. -/
theorem edg_prod_newList {n : ℕ} (hn : n < Bc + 1) (hnB : n ≤ Bc) (zf : Fin n → Particle 𝒢 g)
    (Δ : ℤ) (x : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (st : Finset (Slot J ℓ))
    (pm : Slot J ℓ → Option (Fin Bc)) (f : Particle 𝒢 g → ℝ) :
    ((edgeAbsNewList Δ (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) x st pm).map f).prod =
      (∏ j : Fin n, if ∃ sl, pm sl = some (Fin.castLE hnB j) then 1
        else f (shiftParticle Δ (zf j))) *
        ∏ sl ∈ st, f (shiftParticle Δ ⟨x sl, 0⟩) := by
  unfold edgeAbsNewList
  rw [List.map_append, List.prod_append,
    edg_prod_kept hn hnB zf (fun j => ∃ sl, pm sl = some j) (shiftParticle Δ) f, List.map_map]
  exact congrArg (fun t => (∏ j : Fin n, if ∃ sl, pm sl = some (Fin.castLE hnB j) then 1
    else f (shiftParticle Δ (zf j))) * t)
    (edg_prod_stored st fun sl => f (shiftParticle Δ ⟨x sl, 0⟩))

/-- **The primes of the new memory of a group after an edge**: the primes of the old particles
which are not promoted and the labels of the stored slots. -/
theorem edg_exists_newList {n : ℕ} (hn : n < Bc + 1) (hnB : n ≤ Bc)
    (zf : Fin n → Particle 𝒢 g) (Δ : ℤ) (x : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g})
    (st : Finset (Slot J ℓ)) (pm : Slot J ℓ → Option (Fin Bc)) (p : {p : ℕ // p ∈ 𝒢.big g}) :
    (∃ w ∈ edgeAbsNewList Δ (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) x st pm, w.1 = p) ↔
      (∃ j : Fin n, (¬∃ sl, pm sl = some (Fin.castLE hnB j)) ∧ (zf j).1 = p) ∨
        ∃ sl ∈ st, x sl = p := by
  unfold edgeAbsNewList
  constructor
  · rintro ⟨w, hw, hp⟩
    rcases List.mem_append.mp hw with h | h
    · obtain ⟨j', -, hj'⟩ := List.mem_filterMap.mp h
      by_cases hc : ∃ sl, pm sl = some j'
      · rw [if_pos hc] at hj'
        cases hj'
      · rw [if_neg hc] at hj'
        obtain ⟨w₀, hw₀, hsh⟩ := Option.map_eq_some_iff.mp hj'
        obtain ⟨hlt, hz⟩ := (edg_memAt_eq_some hn zf j' w₀).mp hw₀
        have hcast : Fin.castLE hnB (⟨j'.val, hlt⟩ : Fin n) = j' := Fin.ext rfl
        refine Or.inl ⟨⟨j'.val, hlt⟩, ?_, ?_⟩
        · rw [hcast]
          exact hc
        · rw [hz, ← hp, ← hsh]
          rfl
    · obtain ⟨sl, hsl, hsw⟩ := List.mem_map.mp h
      refine Or.inr ⟨sl, of_decide_eq_true (List.mem_filter.mp hsl).2, ?_⟩
      rw [← hp, ← hsw]
      rfl
  · rintro (⟨j, hj, hp⟩ | ⟨sl, hsl, hp⟩)
    · refine ⟨shiftParticle Δ (zf j), List.mem_append.mpr (Or.inl ?_), hp⟩
      refine List.mem_filterMap.mpr ⟨Fin.castLE hnB j, List.mem_finRange _, ?_⟩
      rw [if_neg hj, edg_memAt_castLE hn hnB zf j]
      rfl
    · refine ⟨shiftParticle Δ ⟨x sl, 0⟩, List.mem_append.mpr (Or.inr ?_), hp⟩
      exact List.mem_map.mpr ⟨sl, List.mem_filter.mpr ⟨l38_mem_slotList sl, decide_eq_true hsl⟩,
        rfl⟩

/-- **The truncation is not active**: the pending primes and the active primes of a group in which
every prime occurs at most once are distinct primes of the group. -/
theorem edg_size_le {n : ℕ} (zf : Fin n → Particle 𝒢 g)
    (x : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (hx : Function.Injective x)
    (hz : Function.Injective fun j : Fin n => (zf j).1) (hne : ∀ sl (j : Fin n), x sl ≠ (zf j).1) :
    n + (J + ℓ) ≤ (𝒢.big g).card := by
  have hf : Function.Injective (Sum.elim (fun j : Fin n => (zf j).1) x) := by
    rintro (a | a) (c | c) h
    · exact congrArg Sum.inl (hz h)
    · exact absurd (Eq.symm h) (hne c a)
    · exact absurd h (hne a c)
    · exact congrArg Sum.inr (hx h)
  have h := Fintype.card_le_of_injective _ hf
  rw [Fintype.card_sum, Fintype.card_fin, card_slot, Fintype.card_coe] at h
  exact h

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
