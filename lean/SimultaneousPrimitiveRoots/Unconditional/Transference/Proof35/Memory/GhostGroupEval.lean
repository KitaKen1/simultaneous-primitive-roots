module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.GhostBatchCount
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.GhostCompat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# One big group: the product of the values of its primes and the new memory of a visit operation

Source: `verification/stage7-sources/S-02.tex`, lines 456–475 and 569–581
(`[S-02:0456–0475, 0569–0581]`).

Tools for `GhostStepFactorProof.lean` (part (M2) of the proof of [S] Lemma 3.7), for one big group.

* `PrimeVals.thirdL`, `PrimeVals.evalL` — the factor of one big group in `PrimeVals.eval`, as a
  function of the list of the pending particles; it is invariant under permutations of the list
  (`PrimeVals.evalL_perm`) and only depends on the born primes of the group
  (`PrimeVals.evalL_congr_U`).
* `BatchNew`, `batchSet` — a batch of pairwise distinct primes which were not born, and the set of
  its primes.
* `ghostNewMem_ofFn`, `ghostNewSize_lift`, `ghostNewMem_perm_lift` — the particles of the new
  memory `(𝐳 ∖ A, (p'_1, 0), …, (p'_b, 0))`: the survivors and the batch.
* `ghStep_size_le` — the pending primes and a batch of new primes are distinct primes of the
  group, so `n + b ≤ #𝒫_g`: "the truncations are not active".
* `ghStep_new_consistent`, `ghostNew_facts` — after a visit operation with new births every prime
  of the group still occurs at most once.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### Lists -/

/-- The product of a function over the list of a tuple. -/
theorem ghStep_prod_map_ofFn {α : Type*} {n : ℕ} (x : Fin n → α) (f : α → ℝ) :
    ((List.ofFn x).map f).prod = ∏ j, f (x j) :=
  (congrArg List.prod List.map_ofFn).trans List.prod_ofFn

/-- The product of a function over the survivors. -/
theorem ghStep_prod_survList {Z : Type*} {n : ℕ} (x : Fin n → Z) (s : Finset (Fin n))
    (f : Z → ℝ) : ((ghostSurvList x s).map f).prod = ∏ h ∈ sᶜ, f (x h) := by
  have hnd : ((List.finRange n).filter fun i => decide (i ∉ s)).Nodup :=
    (List.nodup_finRange n).filter _
  have htf : ((List.finRange n).filter fun i => decide (i ∉ s)).toFinset = sᶜ := by
    ext i
    simp
  have h1 : ((ghostSurvList x s).map f).prod =
      (((List.finRange n).filter fun i => decide (i ∉ s)).map fun h => f (x h)).prod :=
    congrArg List.prod List.map_map
  exact h1.trans ((List.prod_toFinset (fun h => f (x h)) hnd).symm.trans
    (congrArg (fun t => ∏ h ∈ t, f (x h)) htf))

/-- The survivors are the entries of the positions which are not deleted. -/
theorem ghStep_mem_survList {Z : Type*} {n : ℕ} (x : Fin n → Z) (s : Finset (Fin n)) (w : Z) :
    w ∈ ghostSurvList x s ↔ ∃ h, h ∉ s ∧ x h = w := by
  unfold ghostSurvList
  rw [List.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h, of_decide_eq_true (List.mem_filter.mp hh).2, rfl⟩
  · rintro ⟨h, hs, rfl⟩
    exact ⟨h, List.mem_filter.mpr ⟨List.mem_finRange h, decide_eq_true hs⟩, rfl⟩

variable {S B : Type} {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ}

/-- A prime of the list of a tuple of particles is the prime of one of its entries. -/
theorem ghStep_exists_ofFn {g : B} {n : ℕ} (x : Fin n → Particle 𝒢 g)
    (p : {p : ℕ // p ∈ 𝒢.big g}) : (∃ w ∈ List.ofFn x, w.1 = p) ↔ ∃ j, (x j).1 = p := by
  constructor
  · rintro ⟨w, hw, hp⟩
    obtain ⟨j, hj⟩ := (List.mem_ofFn' x w).mp hw
    exact ⟨j, by rw [hj]; exact hp⟩
  · rintro ⟨j, hj⟩
    exact ⟨x j, (List.mem_ofFn' x (x j)).mpr (Set.mem_range_self j), hj⟩

/-! ### The product of the values of the primes of one group -/

open _root_.Classical in
/-- The factor of the prime `p` of the big group `g` which is neither counted as active nor as
pending: `dead` if it was born and is not present, `unborn` if it was not born, and `1` if it is
present. -/
def PrimeVals.thirdL (v : PrimeVals 𝒢) (g : B) (xbg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g})
    (l : List (Particle 𝒢 g)) (U : Finset ℕ) (p : {p : ℕ // p ∈ 𝒢.big g}) : ℝ :=
  if (p : ℕ) ∈ U then (if (∃ sl, xbg sl = p) ∨ (∃ w ∈ l, w.1 = p) then 1 else v.dead g p)
  else v.unborn g p

/-- **The factor of the big group `g` in the product of the values** (`PrimeVals.eval`), for the
active list `xbg` of the group, the list `l` of its pending particles and the set `U` of the
primes born so far. -/
def PrimeVals.evalL (v : PrimeVals 𝒢) (g : B) (xbg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g})
    (l : List (Particle 𝒢 g)) (U : Finset ℕ) : ℝ :=
  (∏ sl : Slot J ℓ, v.act g (xbg sl)) * (l.map (v.pend g)).prod *
    ∏ p : {p : ℕ // p ∈ 𝒢.big g}, v.thirdL g xbg l U p

theorem PrimeVals.thirdL_congr (v : PrimeVals 𝒢) (g : B)
    (xbg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) {l₁ l₂ : List (Particle 𝒢 g)} {U₁ U₂ : Finset ℕ}
    (p : {p : ℕ // p ∈ 𝒢.big g}) (hl : (∃ w ∈ l₁, w.1 = p) ↔ ∃ w ∈ l₂, w.1 = p)
    (hU : (p : ℕ) ∈ U₁ ↔ (p : ℕ) ∈ U₂) :
    v.thirdL g xbg l₁ U₁ p = v.thirdL g xbg l₂ U₂ p := by
  unfold PrimeVals.thirdL
  exact bigRes_ite_congr hU (bigRes_ite_congr (or_congr Iff.rfl hl) rfl rfl) rfl

/-- The factor of a group does not depend on the order of the pending particles. -/
theorem PrimeVals.evalL_perm (v : PrimeVals 𝒢) (g : B)
    (xbg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) {l₁ l₂ : List (Particle 𝒢 g)} (h : l₁.Perm l₂)
    (U : Finset ℕ) : v.evalL g xbg l₁ U = v.evalL g xbg l₂ U := by
  unfold PrimeVals.evalL
  rw [(h.map (v.pend g)).prod_eq]
  exact congrArg
    (fun t => (∏ sl : Slot J ℓ, v.act g (xbg sl)) * (l₂.map (v.pend g)).prod * t)
    (Finset.prod_congr rfl fun p _ => v.thirdL_congr g xbg p
      ⟨fun ⟨w, hw, hp⟩ => ⟨w, h.mem_iff.mp hw, hp⟩, fun ⟨w, hw, hp⟩ => ⟨w, h.mem_iff.mpr hw, hp⟩⟩
      Iff.rfl)

/-- The factor of a group only depends on which primes of the group were born. -/
theorem PrimeVals.evalL_congr_U (v : PrimeVals 𝒢) (g : B)
    (xbg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (l : List (Particle 𝒢 g)) {U₁ U₂ : Finset ℕ}
    (h : ∀ p : {p : ℕ // p ∈ 𝒢.big g}, (p : ℕ) ∈ U₁ ↔ (p : ℕ) ∈ U₂) :
    v.evalL g xbg l U₁ = v.evalL g xbg l U₂ := by
  unfold PrimeVals.evalL
  exact congrArg
    (fun t => (∏ sl : Slot J ℓ, v.act g (xbg sl)) * (l.map (v.pend g)).prod * t)
    (Finset.prod_congr rfl fun p _ => v.thirdL_congr g xbg p Iff.rfl (h p))

/-! ### Batches of new primes -/

/-- **A batch of new births**: its primes are pairwise distinct and none of them was born. -/
def BatchNew {g : B} (U : Finset ℕ) (β : Batch 𝒢 Bc g) : Prop :=
  Function.Injective β.2 ∧ ∀ j, ((β.2 j : {p : ℕ // p ∈ 𝒢.big g}) : ℕ) ∉ U

/-- The set of the primes of a batch. -/
def batchSet {g : B} (β : Batch 𝒢 Bc g) : Finset ℕ :=
  Finset.univ.image fun j : Fin β.1.val => ((β.2 j : {p : ℕ // p ∈ 𝒢.big g}) : ℕ)

theorem mem_batchSet {g : B} (β : Batch 𝒢 Bc g) (z : ℕ) :
    z ∈ batchSet β ↔ ∃ j, ((β.2 j : {p : ℕ // p ∈ 𝒢.big g}) : ℕ) = z := by
  unfold batchSet
  rw [Finset.mem_image]
  exact ⟨fun ⟨j, _, hj⟩ => ⟨j, hj⟩, fun ⟨j, hj⟩ => ⟨j, Finset.mem_univ j, hj⟩⟩

/-- **The truncation is not active**: the primes of the pending particles (pairwise distinct,
born) and the primes of a batch of new births are distinct primes of the group. -/
theorem ghStep_size_le {g : B} {n b : ℕ} (x : Fin n → Particle 𝒢 g)
    (p' : Fin b → {p : ℕ // p ∈ 𝒢.big g}) (U : Finset ℕ)
    (hinj : Function.Injective fun j : Fin n => (x j).1) (hU : ∀ j, ((x j).1 : ℕ) ∈ U)
    (hp : Function.Injective p')
    (hbad : ∀ j, ((p' j : {p : ℕ // p ∈ 𝒢.big g}) : ℕ) ∉ U) : n + b ≤ (𝒢.big g).card := by
  have hf : Function.Injective (Sum.elim (fun j : Fin n => (x j).1) p') := by
    rintro (a | a) (c | c) h
    · exact congrArg Sum.inl (hinj h)
    · have h' : (x a).1 = p' c := h
      have h1 := hU a
      rw [h'] at h1
      exact absurd h1 (hbad c)
    · have h' : p' a = (x c).1 := h
      have h1 := hU c
      rw [← h'] at h1
      exact absurd h1 (hbad a)
    · exact congrArg Sum.inr (hp h)
  have h := Fintype.card_le_of_injective _ hf
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Fintype.card_coe] at h
  exact h

/-! ### The new memory -/

/-- The particles of the new memory of a visit operation, when its size is at most the cutoff:
the survivors and the batch. -/
theorem ghostNewMem_ofFn {g : B} (z : Mem 𝒢 Bc g) (c : Finset (Fin Bc) × Batch 𝒢 Bc g)
    (h : ghostNewSize z c ≤ Bc) :
    List.ofFn (ghostNewMem z c).2 = ghostSurvivors z c.1 ++ batchParticles c.2 := by
  have hl : (ghostSurvivors z c.1 ++ batchParticles c.2).length = ghostNewSize z c := by
    rw [List.length_append]
    unfold batchParticles ghostNewSize
    rw [List.length_ofFn]
  exact ofFn_memOfList (hl.le.trans h)

/-- The size of the new memory for a set of terminated positions of the memory. -/
theorem ghostNewSize_lift {g : B} {n : ℕ} (hn : n < Bc + 1) (hnB : n ≤ Bc)
    (x : Fin n → Particle 𝒢 g) (s : Finset (Fin n)) (β : Batch 𝒢 Bc g) :
    ghostNewSize (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) (s.map (Fin.castLEEmb hnB), β) =
      n - s.card + β.1.val := by
  show (ghostSurvivors (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) (s.map (Fin.castLEEmb hnB))).length +
    β.1.val = _
  rw [(ghostSurvivors_lift_perm hn hnB x s).length_eq, ghostSurvList_length]

/-- The particles of the new memory for a set of terminated positions of the memory: a
permutation of the survivors followed by the batch. -/
theorem ghostNewMem_perm_lift {g : B} {n : ℕ} (hn : n < Bc + 1) (hnB : n ≤ Bc)
    (x : Fin n → Particle 𝒢 g) (s : Finset (Fin n)) (β : Batch 𝒢 Bc g)
    (h : n - s.card + β.1.val ≤ Bc) :
    (List.ofFn (ghostNewMem (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) (s.map (Fin.castLEEmb hnB), β)).2).Perm
      (ghostSurvList x s ++ batchParticles β) := by
  have hsz := ghostNewSize_lift hn hnB x s β
  rw [ghostNewMem_ofFn _ _ (hsz.le.trans h)]
  exact (ghostSurvivors_lift_perm hn hnB x s).append_right _

/-- **After a visit operation with new births every prime of the group occurs at most once**
[S-02:0577–0578]: for a memory whose particles are the survivors and a batch of new births, the
primes of the particles are pairwise distinct, none of them is active, and all of them are born
(they are in `U` or in the batch). -/
theorem ghStep_new_consistent {g : B} (xbg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (U : Finset ℕ)
    {n : ℕ} (x : Fin n → Particle 𝒢 g) (s : Finset (Fin n)) (β : Batch 𝒢 Bc g)
    (m : Mem 𝒢 Bc g) (hperm : (List.ofFn m.2).Perm (ghostSurvList x s ++ batchParticles β))
    (hinj : Function.Injective fun j : Fin n => (x j).1)
    (hne : ∀ sl (j : Fin n), xbg sl ≠ (x j).1) (hU : ∀ j : Fin n, ((x j).1 : ℕ) ∈ U)
    (hxU : ∀ sl, (xbg sl : ℕ) ∈ U) (hgood : BatchNew U β) :
    (Function.Injective fun j : Fin m.1.val => (m.2 j).1) ∧
      (∀ sl (j : Fin m.1.val), xbg sl ≠ (m.2 j).1) ∧
      ∀ j : Fin m.1.val, ((m.2 j).1 : ℕ) ∈ U ∪ batchSet β := by
  have hcases : ∀ j : Fin m.1.val,
      (∃ h, x h = m.2 j) ∨ ∃ k, (⟨β.2 k, 0⟩ : Particle 𝒢 g) = m.2 j := by
    intro j
    have h1 : m.2 j ∈ ghostSurvList x s ++ batchParticles β :=
      hperm.mem_iff.mp ((List.mem_ofFn' m.2 (m.2 j)).mpr (Set.mem_range_self j))
    rcases List.mem_append.mp h1 with h2 | h2
    · obtain ⟨h, -, hh⟩ := (ghStep_mem_survList x s (m.2 j)).mp h2
      exact Or.inl ⟨h, hh⟩
    · have h3 : m.2 j ∈ List.ofFn fun k : Fin β.1.val => (⟨β.2 k, 0⟩ : Particle 𝒢 g) := h2
      obtain ⟨k, hk⟩ := (List.mem_ofFn' _ _).mp h3
      exact Or.inr ⟨k, hk⟩
  refine ⟨?_, ?_, ?_⟩
  · have hS : ((ghostSurvList x s).map fun w : Particle 𝒢 g => w.1).Nodup := by
      have e : (ghostSurvList x s).map (fun w : Particle 𝒢 g => w.1) =
          ((List.finRange n).filter fun i => decide (i ∉ s)).map fun h => (x h).1 :=
        List.map_map
      rw [e]
      exact List.Nodup.map hinj ((List.nodup_finRange n).filter _)
    have hB : ((batchParticles β).map fun w : Particle 𝒢 g => w.1).Nodup := by
      have e : (batchParticles β).map (fun w : Particle 𝒢 g => w.1) = List.ofFn β.2 :=
        List.map_ofFn
      rw [e]
      exact List.nodup_ofFn.mpr hgood.1
    have hD : List.Disjoint ((ghostSurvList x s).map fun w : Particle 𝒢 g => w.1)
        ((batchParticles β).map fun w : Particle 𝒢 g => w.1) := by
      refine List.disjoint_left.mpr fun a ha hb => ?_
      obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ha
      obtain ⟨h, -, rfl⟩ := (ghStep_mem_survList x s w).mp hw
      obtain ⟨w', hw', hww⟩ := List.mem_map.mp hb
      have h3 : w' ∈ List.ofFn fun k : Fin β.1.val => (⟨β.2 k, 0⟩ : Particle 𝒢 g) := hw'
      obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).mp h3
      have h4 : β.2 k = (x h).1 := hww
      have h5 := hU h
      rw [← h4] at h5
      exact hgood.2 k h5
    have hnd : ((ghostSurvList x s ++ batchParticles β).map
        fun w : Particle 𝒢 g => w.1).Nodup := by
      rw [List.map_append]
      exact List.Nodup.append hS hB hD
    have hnd' : ((List.ofFn m.2).map fun w : Particle 𝒢 g => w.1).Nodup :=
      (hperm.map _).nodup_iff.mpr hnd
    have e : (List.ofFn m.2).map (fun w : Particle 𝒢 g => w.1) =
        List.ofFn fun j : Fin m.1.val => (m.2 j).1 := List.map_ofFn
    rw [e] at hnd'
    exact List.nodup_ofFn.mp hnd'
  · intro sl j
    rcases hcases j with ⟨h, hh⟩ | ⟨k, hk⟩
    · rw [← hh]
      exact hne sl h
    · rw [← hk]
      intro heq
      have h5 := hxU sl
      rw [heq] at h5
      exact hgood.2 k h5
  · intro j
    rcases hcases j with ⟨h, hh⟩ | ⟨k, hk⟩
    · rw [← hh]
      exact Finset.mem_union_left _ (hU h)
    · rw [← hk]
      exact Finset.mem_union_right _ ((mem_batchSet β _).mpr ⟨k, rfl⟩)

/-- **The new memory of a visit operation with new births** for a group in which every prime
occurs at most once: its size and the size of the old memory are at most `#𝒫_g`, and in the new
state every prime of the group still occurs at most once. -/
theorem ghostNew_facts {g : B} (xbg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (U : Finset ℕ)
    (z : Mem 𝒢 Bc g) (A : Finset (Fin Bc)) (β : Batch 𝒢 Bc g)
    (hinj : Function.Injective fun j : Fin z.1.val => (z.2 j).1)
    (hne : ∀ sl (j : Fin z.1.val), xbg sl ≠ (z.2 j).1)
    (hU : ∀ j : Fin z.1.val, ((z.2 j).1 : ℕ) ∈ U) (hxU : ∀ sl, (xbg sl : ℕ) ∈ U)
    (hcard : (𝒢.big g).card ≤ Bc) (hv : GhostValid z A) (hgood : BatchNew U β) :
    ghostNewSize z (A, β) ≤ (𝒢.big g).card ∧ z.1.val ≤ (𝒢.big g).card ∧
      (Function.Injective fun j : Fin (ghostNewMem z (A, β)).1.val =>
        ((ghostNewMem z (A, β)).2 j).1) ∧
      (∀ sl (j : Fin (ghostNewMem z (A, β)).1.val), xbg sl ≠ ((ghostNewMem z (A, β)).2 j).1) ∧
      ∀ j : Fin (ghostNewMem z (A, β)).1.val,
        (((ghostNewMem z (A, β)).2 j).1 : ℕ) ∈ U ∪ batchSet β := by
  obtain ⟨⟨n, hn⟩, x⟩ := z
  have hnB : n ≤ Bc := Nat.le_of_lt_succ hn
  obtain ⟨s, -, rfl⟩ := Finset.mem_map.mp (ghostValid_mem_lift hn hnB x hv)
  have hnb : n + β.1.val ≤ (𝒢.big g).card :=
    ghStep_size_le x β.2 U hinj hU hgood.1 hgood.2
  have hsz : ghostNewSize (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) (s.map (Fin.castLEEmb hnB), β) =
      n - s.card + β.1.val := ghostNewSize_lift hn hnB x s β
  have hle : n - s.card + β.1.val ≤ n + β.1.val :=
    Nat.add_le_add_right (Nat.sub_le n s.card) _
  have hperm := ghostNewMem_perm_lift hn hnB x s β ((hle.trans hnb).trans hcard)
  refine ⟨?_, ?_, ghStep_new_consistent xbg U x s β _ hperm hinj hne hU hxU hgood⟩
  · exact (hsz.le.trans hle).trans hnb
  · exact (Nat.le_add_right n β.1.val).trans hnb

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
