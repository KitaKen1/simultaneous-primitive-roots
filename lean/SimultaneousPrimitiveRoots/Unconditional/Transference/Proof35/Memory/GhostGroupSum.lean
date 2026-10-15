module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.GhostGroupEval
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# A visit operation acts prime by prime: one big group

Source: `verification/stage7-sources/S-02.tex`, lines 456–475 and 569–581
(`[S-02:0456–0475, 0569–0581]`), (eq:ghost-row).

`ghostT_sum` is the statement (M2) of the proof of [S] Lemma 3.7 for one big group `g`: for a
memory `𝐳` of the group in which every prime occurs at most once, is born and is not active, the
sum over the local choices of the group (the set `A` of terminated pending zeros and the ordered
batch `(p'_1, …, p'_b)` of births, pairwise distinct and not born before) of

`(coefficient (eq:ghost-row)) × (product of the values at the new state)`

is the product of the values `ghostStepVals` at the old state.

* `ghostT` — the term of a choice of the group.
* `ghStep_thirdL_new`, `ghStep_prod_factS` — the factors of the primes which are neither active nor
  pending, at the new state: a terminated prime is dead, a born prime is pending.
* `ghostT_lift` — the term of a set `s` of terminated positions of the memory and a batch is the
  product of a term of `s` (`ghStep_subsetTerm`) and a term of the batch (`ghStep_batchTerm`).
* `ghostT_sum` — the sum over the choices, by `ghStep_sum_subsetTerm` and `ghStep_sum_batchTerm`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

variable {S B : Type} {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {N : Type}

/-! ### The factors of one prime -/

/-- The weight of a ghost birth of the prime `p` at the visit `i`, times the value of the new
pending zero: `(-η_i V_g/ρ) μ̃_g(p) · pend(p, 0)`. -/
def ghStep_bornW (D : MemData 𝒢 J ℓ N) (i : ℕ) (v : PrimeVals 𝒢) (g : B)
    (p : {p : ℕ // p ∈ 𝒢.big g}) : ℝ :=
  Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ D.q D.n i) D.ρ *
    tiltLaw (𝒢.big g) D.q D.n p * v.pend g ⟨p, 0⟩

open _root_.Classical in
/-- The factor of a prime whose pending zero terminates: it is dead afterwards. -/
def ghStep_factS (v : PrimeVals 𝒢) (g : B) {n : ℕ} (x : Fin n → Particle 𝒢 g)
    (s : Finset (Fin n)) (p : {p : ℕ // p ∈ 𝒢.big g}) : ℝ :=
  if ∃ h ∈ s, (x h).1 = p then v.dead g p else 1

open _root_.Classical in
/-- The factor of a born prime before the visit operation: `dead` if it is not present. -/
def ghStep_factD (v : PrimeVals 𝒢) (g : B) (xbg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) {n : ℕ}
    (x : Fin n → Particle 𝒢 g) (U : Finset ℕ) (p : {p : ℕ // p ∈ 𝒢.big g}) : ℝ :=
  if (p : ℕ) ∈ U then (if (∃ sl, xbg sl = p) ∨ (∃ h, (x h).1 = p) then 1 else v.dead g p)
  else 1

/-- **The factor of one prime at the new state** [S-02:0569–0581]: for the particles
`(𝐳 ∖ s, (p'_1, 0), …, (p'_b, 0))` and the born set `U ∪ {p'_1, …, p'_b}`, the factor of a prime
which is neither counted as active nor as pending is the product of the factor of a terminated
prime, of the factor of a born prime at the old state, and of the factor of an unborn prime which
is not in the batch. -/
theorem ghStep_thirdL_new (v : PrimeVals 𝒢) (g : B) (xbg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g})
    (U : Finset ℕ) {n : ℕ} (x : Fin n → Particle 𝒢 g)
    (hinj : Function.Injective fun j : Fin n => (x j).1)
    (hne : ∀ sl (j : Fin n), xbg sl ≠ (x j).1) (hU : ∀ j : Fin n, ((x j).1 : ℕ) ∈ U)
    (s : Finset (Fin n)) (β : Batch 𝒢 Bc g)
    (hbad : ∀ j, ((β.2 j : {p : ℕ // p ∈ 𝒢.big g}) : ℕ) ∉ U) (p : {p : ℕ // p ∈ 𝒢.big g}) :
    v.thirdL g xbg (ghostSurvList x s ++ batchParticles β) (U ∪ batchSet β) p =
      ghStep_factS v g x s p * ghStep_factD v g xbg x U p *
        ghStep_unbornFactor (fun p : {p : ℕ // p ∈ 𝒢.big g} => (p : ℕ) ∈ U) (v.unborn g)
          β.2 p := by
  have hcond : (p : ℕ) ∈ U ∪ batchSet β ↔ ((p : ℕ) ∈ U ∨ ∃ j, β.2 j = p) := by
    rw [Finset.mem_union, mem_batchSet]
    exact or_congr Iff.rfl
      ⟨fun ⟨j, hj⟩ => ⟨j, Subtype.ext hj⟩, fun ⟨j, hj⟩ => ⟨j, congrArg Subtype.val hj⟩⟩
  have hmem : (∃ w ∈ ghostSurvList x s ++ batchParticles β, w.1 = p) ↔
      ((∃ h, h ∉ s ∧ (x h).1 = p) ∨ ∃ j, β.2 j = p) := by
    constructor
    · rintro ⟨w, hw, hp⟩
      rcases List.mem_append.mp hw with h2 | h2
      · obtain ⟨h, hs, rfl⟩ := (ghStep_mem_survList x s w).mp h2
        exact Or.inl ⟨h, hs, hp⟩
      · have h3 : w ∈ List.ofFn fun k : Fin β.1.val => (⟨β.2 k, 0⟩ : Particle 𝒢 g) := h2
        obtain ⟨k, rfl⟩ := (List.mem_ofFn' _ _).mp h3
        exact Or.inr ⟨k, hp⟩
    · rintro (⟨h, hs, hp⟩ | ⟨k, hp⟩)
      · exact ⟨x h, List.mem_append.mpr
          (Or.inl ((ghStep_mem_survList x s (x h)).mpr ⟨h, hs, rfl⟩)), hp⟩
      · refine ⟨⟨β.2 k, 0⟩, List.mem_append.mpr (Or.inr ?_), hp⟩
        exact (List.mem_ofFn' (fun k : Fin β.1.val => (⟨β.2 k, 0⟩ : Particle 𝒢 g)) _).mpr
          (Set.mem_range_self k)
  have hM : (∃ h, (x h).1 = p) ↔ ((∃ h ∈ s, (x h).1 = p) ∨ ∃ h, h ∉ s ∧ (x h).1 = p) := by
    constructor
    · rintro ⟨h, hp⟩
      by_cases hs : h ∈ s
      · exact Or.inl ⟨h, hs, hp⟩
      · exact Or.inr ⟨h, hs, hp⟩
    · rintro (⟨h, -, hp⟩ | ⟨h, -, hp⟩)
      · exact ⟨h, hp⟩
      · exact ⟨h, hp⟩
  have hSS : (∃ h ∈ s, (x h).1 = p) → ¬∃ h, h ∉ s ∧ (x h).1 = p := by
    rintro ⟨h, hs, hp⟩ ⟨h', hs', hp'⟩
    have e : h = h' := hinj (hp.trans hp'.symm)
    rw [e] at hs
    exact hs' hs
  have hMU : (∃ h, (x h).1 = p) → (p : ℕ) ∈ U := by
    rintro ⟨h, hp⟩
    have h1 := hU h
    rw [hp] at h1
    exact h1
  have hMa : (∃ h, (x h).1 = p) → ¬∃ sl, xbg sl = p := by
    rintro ⟨h, hp⟩ ⟨sl, hsl⟩
    exact hne sl h (hsl.trans hp.symm)
  have hBU : (∃ j, β.2 j = p) → ¬(p : ℕ) ∈ U := by
    rintro ⟨j, hj⟩ hpU
    have h1 := hbad j
    rw [hj] at h1
    exact h1 hpU
  unfold PrimeVals.thirdL ghStep_factS ghStep_factD ghStep_unbornFactor
  exact ((bigRes_ite_congr (hQ := _root_.Classical.propDecidable _) hcond
      (bigRes_ite_congr (hQ := _root_.Classical.propDecidable _) (or_congr Iff.rfl hmem) rfl rfl)
      rfl).trans
    (ghStep_ite_third (v.dead g p) (v.unborn g p) hM hSS hMU hMa hBU)).trans
    (congrArg₂ (fun a b : ℝ => a * b) rfl (bigRes_ite_congr Iff.rfl rfl rfl))

/-- The product of the factors of the terminated primes: one factor `dead` for every terminated
position (the primes of the pending particles are pairwise distinct). -/
theorem ghStep_prod_factS (v : PrimeVals 𝒢) (g : B) {n : ℕ} (x : Fin n → Particle 𝒢 g)
    (hinj : Function.Injective fun j : Fin n => (x j).1) (s : Finset (Fin n)) :
    ∏ p : {p : ℕ // p ∈ 𝒢.big g}, ghStep_factS v g x s p = ∏ h ∈ s, v.dead g (x h).1 := by
  have h1 : ∀ p : {p : ℕ // p ∈ 𝒢.big g}, ghStep_factS v g x s p =
      if p ∈ s.image (fun h => (x h).1) then v.dead g p else 1 := by
    intro p
    unfold ghStep_factS
    exact bigRes_ite_congr Finset.mem_image.symm rfl rfl
  have himg : ∏ p ∈ s.image (fun h => (x h).1), v.dead g p = ∏ h ∈ s, v.dead g (x h).1 :=
    Finset.prod_image fun a _ b _ h => hinj h
  refine (Finset.prod_congr rfl fun p _ => h1 p).trans ?_
  rw [Finset.prod_ite_mem, Finset.univ_inter, himg]

/-- The factor of one prime at the old state, for the values after the visit operation. -/
theorem ghStep_thirdL_step (D : MemData 𝒢 J ℓ N) (i : ℕ) (v : PrimeVals 𝒢) (g : B)
    (xbg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) {n : ℕ} (x : Fin n → Particle 𝒢 g) (U : Finset ℕ)
    (p : {p : ℕ // p ∈ 𝒢.big g}) :
    ghStep_factD v g xbg x U p *
        ghStep_bornFactor (fun p : {p : ℕ // p ∈ 𝒢.big g} => (p : ℕ) ∈ U) (v.unborn g)
          (ghStep_bornW D i v g) p =
      (ghostStepVals D i v).thirdL g xbg (List.ofFn x) U p := by
  have e : v.unborn g p + ghStep_bornW D i v g p = (ghostStepVals D i v).unborn g p := rfl
  unfold ghStep_factD ghStep_bornFactor PrimeVals.thirdL
  by_cases hU : (p : ℕ) ∈ U
  · rw [if_pos hU, if_pos hU, if_pos hU, mul_one]
    exact bigRes_ite_congr (or_congr Iff.rfl (ghStep_exists_ofFn x p).symm) rfl rfl
  · rw [if_neg hU, if_neg hU, if_neg hU, one_mul, e]

/-! ### The term of a choice of one group -/

/-- The coefficient (eq:ghost-row) of a group for a set of terminated pending zeros. -/
theorem ghStep_coefG_of_valid (q ρ : ℝ) (n i : ℕ) {g : B} (z : Mem 𝒢 Bc g)
    (A : Finset (Fin Bc)) (b : Fin (Bc + 1)) (p' : Fin b.val → {p : ℕ // p ∈ 𝒢.big g})
    (hv : GhostValid z A) :
    ghostCoefG 𝒢 q ρ n i g z (A, ⟨b, p'⟩) =
      Graph.sourceGhostD (visitQ q n i) ρ ^ A.card *
          Graph.sourceGhostA (visitQ q n i) ρ ^ (memZeroCount z - A.card) *
          (Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ q n i) ρ ^
            b.val / (b.val.factorial : ℝ)) *
        ∏ j, tiltLaw (𝒢.big g) q n (p' j) := by
  unfold ghostCoefG
  exact if_pos hv

open _root_.Classical in
/-- **The term of a local choice of the big group `g`** in the sum over the choices of a visit
operation with new births: zero unless the batch consists of pairwise distinct primes which were
not born; otherwise the coefficient (eq:ghost-row) of the group times the factor of the group in
the product of the values at the new state. -/
def ghostT (D : MemData 𝒢 J ℓ N) (i : ℕ) (v : PrimeVals 𝒢) (g : B)
    (xbg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (z : Mem 𝒢 Bc g) (U : Finset ℕ)
    (c : Finset (Fin Bc) × Batch 𝒢 Bc g) : ℝ :=
  if BatchNew U c.2 then
    ghostCoefG 𝒢 D.q D.ρ D.n i g z c *
      v.evalL g xbg (List.ofFn (ghostNewMem z c).2) (U ∪ batchSet c.2)
  else 0

theorem ghostT_eq_zero_of_not_valid (D : MemData 𝒢 J ℓ N) (i : ℕ) (v : PrimeVals 𝒢) (g : B)
    (xbg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (z : Mem 𝒢 Bc g) (U : Finset ℕ)
    (c : Finset (Fin Bc) × Batch 𝒢 Bc g) (h : ¬GhostValid z c.1) :
    ghostT D i v g xbg z U c = 0 := by
  have h0 : ghostCoefG 𝒢 D.q D.ρ D.n i g z c = 0 := by
    unfold ghostCoefG
    exact if_neg h
  unfold ghostT
  rw [h0, zero_mul]
  exact ite_self _

/-- **The term of a set of terminated positions and a batch** [S-02:0456–0475]: for a memory in
which every prime of the group occurs at most once, is born and is not active, the term of the
set `s` of terminated positions and of the batch `p'` is the product of the values of the active
primes, of the factors of the born primes at the old state, of the term of `s` and of the term of
the batch. -/
theorem ghostT_lift (D : MemData 𝒢 J ℓ N) (i : ℕ) (v : PrimeVals 𝒢) (g : B)
    (xbg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (U : Finset ℕ) {n : ℕ} (hn : n < Bc + 1)
    (hnB : n ≤ Bc) (x : Fin n → Particle 𝒢 g)
    (hinj : Function.Injective fun j : Fin n => (x j).1)
    (hne : ∀ sl (j : Fin n), xbg sl ≠ (x j).1) (hU : ∀ j : Fin n, ((x j).1 : ℕ) ∈ U)
    (hcard : (𝒢.big g).card ≤ Bc) (s : Finset (Fin n)) (b : Fin (Bc + 1))
    (p' : Fin b.val → {p : ℕ // p ∈ 𝒢.big g}) :
    ghostT D i v g xbg (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) U (s.map (Fin.castLEEmb hnB), ⟨b, p'⟩) =
      (∏ sl : Slot J ℓ, v.act g (xbg sl)) *
          (∏ p : {p : ℕ // p ∈ 𝒢.big g}, ghStep_factD v g xbg x U p) *
          ghStep_subsetTerm (fun h : Fin n => (x h).2 = 0)
            (Graph.sourceGhostD (visitQ D.q D.n i) D.ρ)
            (Graph.sourceGhostA (visitQ D.q D.n i) D.ρ) (fun h => v.pend g (x h))
            (fun h => v.dead g (x h).1) s *
        ghStep_batchTerm (fun p : {p : ℕ // p ∈ 𝒢.big g} => (p : ℕ) ∈ U) (v.unborn g)
          (ghStep_bornW D i v g) b.val p' := by
  have alg : ∀ (dc ac cg nu K PS PB Pd FD FU F : ℝ),
      dc * ac * (cg / F) * nu * (K * (PS * PB) * (Pd * FD * FU)) =
        K * FD * (dc * ac * PS * Pd) * (F⁻¹ * (cg * nu * PB) * FU) := by
    intro dc ac cg nu K PS PB Pd FD FU F
    ring
  have hgood_iff : BatchNew U (⟨b, p'⟩ : Batch 𝒢 Bc g) ↔
      (Function.Injective p' ∧ ∀ j, ¬((p' j : {p : ℕ // p ∈ 𝒢.big g}) : ℕ) ∈ U) := Iff.rfl
  by_cases hgood : BatchNew U (⟨b, p'⟩ : Batch 𝒢 Bc g)
  · have eT : ghostT D i v g xbg (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) U
          (s.map (Fin.castLEEmb hnB), ⟨b, p'⟩) =
        ghostCoefG 𝒢 D.q D.ρ D.n i g (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g)
            (s.map (Fin.castLEEmb hnB), ⟨b, p'⟩) *
          v.evalL g xbg
            (List.ofFn (ghostNewMem (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g)
              (s.map (Fin.castLEEmb hnB), ⟨b, p'⟩)).2)
            (U ∪ batchSet (⟨b, p'⟩ : Batch 𝒢 Bc g)) := by
      unfold ghostT
      exact if_pos hgood
    have eB : ghStep_batchTerm (fun p : {p : ℕ // p ∈ 𝒢.big g} => (p : ℕ) ∈ U) (v.unborn g)
          (ghStep_bornW D i v g) b.val p' =
        ((b.val.factorial : ℝ))⁻¹ * (∏ j, ghStep_bornW D i v g (p' j)) *
          ∏ p : {p : ℕ // p ∈ 𝒢.big g},
            ghStep_unbornFactor (fun p : {p : ℕ // p ∈ 𝒢.big g} => (p : ℕ) ∈ U) (v.unborn g)
              p' p := by
      unfold ghStep_batchTerm
      exact if_pos (hgood_iff.mp hgood)
    rw [eT, eB]
    by_cases hz : ∀ i ∈ s, (x i).2 = 0
    · have eS : ghStep_subsetTerm (fun h : Fin n => (x h).2 = 0)
            (Graph.sourceGhostD (visitQ D.q D.n i) D.ρ)
            (Graph.sourceGhostA (visitQ D.q D.n i) D.ρ) (fun h => v.pend g (x h))
            (fun h => v.dead g (x h).1) s =
          Graph.sourceGhostD (visitQ D.q D.n i) D.ρ ^ s.card *
              Graph.sourceGhostA (visitQ D.q D.n i) D.ρ ^
                ((Finset.univ.filter fun h : Fin n => (x h).2 = 0).card - s.card) *
              (∏ h ∈ sᶜ, v.pend g (x h)) *
            ∏ h ∈ s, v.dead g (x h).1 := by
        unfold ghStep_subsetTerm
        exact if_pos hz
      rw [eS]
      have hsize : n - s.card + b.val ≤ Bc :=
        (Nat.add_le_add_right (Nat.sub_le n s.card) b.val).trans
          ((ghStep_size_le x p' U hinj hU hgood.1 hgood.2).trans hcard)
      have hZ : memZeroCount (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) =
          (Finset.univ.filter fun h : Fin n => (x h).2 = 0).card := by
        unfold memZeroCount Graph.ghostZeroCount
        exact congrArg Finset.card (Finset.filter_congr_decidable _ _ _)
      have hcoef : ghostCoefG 𝒢 D.q D.ρ D.n i g (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g)
          (s.map (Fin.castLEEmb hnB), ⟨b, p'⟩) =
          Graph.sourceGhostD (visitQ D.q D.n i) D.ρ ^ s.card *
              Graph.sourceGhostA (visitQ D.q D.n i) D.ρ ^
                ((Finset.univ.filter fun h : Fin n => (x h).2 = 0).card - s.card) *
              (Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g))
                (visitQ D.q D.n i) D.ρ ^ b.val / (b.val.factorial : ℝ)) *
            ∏ j, tiltLaw (𝒢.big g) D.q D.n (p' j) :=
        (ghStep_coefG_of_valid D.q D.ρ D.n i _ _ b p'
          ((ghostValid_lift hn hnB x s).mpr hz)).trans (by rw [hZ, Finset.card_map])
      have hperm := ghostNewMem_perm_lift hn hnB x s (⟨b, p'⟩ : Batch 𝒢 Bc g) hsize
      have hl : ((ghostSurvList x s ++ batchParticles (⟨b, p'⟩ : Batch 𝒢 Bc g)).map
          (v.pend g)).prod = (∏ h ∈ sᶜ, v.pend g (x h)) * ∏ j, v.pend g ⟨p' j, 0⟩ := by
        rw [List.map_append, List.prod_append, ghStep_prod_survList]
        exact congrArg (fun t => (∏ h ∈ sᶜ, v.pend g (x h)) * t)
          (ghStep_prod_map_ofFn (fun j : Fin b.val => (⟨p' j, 0⟩ : Particle 𝒢 g)) (v.pend g))
      have h3 : ∏ p : {p : ℕ // p ∈ 𝒢.big g},
            v.thirdL g xbg (ghostSurvList x s ++ batchParticles (⟨b, p'⟩ : Batch 𝒢 Bc g))
              (U ∪ batchSet (⟨b, p'⟩ : Batch 𝒢 Bc g)) p =
          (∏ h ∈ s, v.dead g (x h).1) *
              (∏ p : {p : ℕ // p ∈ 𝒢.big g}, ghStep_factD v g xbg x U p) *
            ∏ p : {p : ℕ // p ∈ 𝒢.big g},
              ghStep_unbornFactor (fun p : {p : ℕ // p ∈ 𝒢.big g} => (p : ℕ) ∈ U) (v.unborn g)
                p' p := by
        rw [← ghStep_prod_factS v g x hinj s, ← Finset.prod_mul_distrib,
          ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun p _ =>
          ghStep_thirdL_new v g xbg U x hinj hne hU s (⟨b, p'⟩ : Batch 𝒢 Bc g) hgood.2 p
      have hev : v.evalL g xbg
            (List.ofFn (ghostNewMem (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g)
              (s.map (Fin.castLEEmb hnB), ⟨b, p'⟩)).2)
            (U ∪ batchSet (⟨b, p'⟩ : Batch 𝒢 Bc g)) =
          (∏ sl : Slot J ℓ, v.act g (xbg sl)) *
              ((∏ h ∈ sᶜ, v.pend g (x h)) * ∏ j, v.pend g ⟨p' j, 0⟩) *
            ((∏ h ∈ s, v.dead g (x h).1) *
                (∏ p : {p : ℕ // p ∈ 𝒢.big g}, ghStep_factD v g xbg x U p) *
              ∏ p : {p : ℕ // p ∈ 𝒢.big g},
                ghStep_unbornFactor (fun p : {p : ℕ // p ∈ 𝒢.big g} => (p : ℕ) ∈ U)
                  (v.unborn g) p' p) := by
        rw [v.evalL_perm g xbg hperm]
        unfold PrimeVals.evalL
        rw [hl, h3]
      have hw : ∏ j, ghStep_bornW D i v g (p' j) =
          Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ D.q D.n i)
              D.ρ ^ b.val * (∏ j, tiltLaw (𝒢.big g) D.q D.n (p' j)) *
            ∏ j, v.pend g ⟨p' j, 0⟩ := by
        unfold ghStep_bornW
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin]
      rw [hcoef, hev, hw]
      exact alg _ _ _ _ _ _ _ _ _ _ _
    · have eS : ghStep_subsetTerm (fun h : Fin n => (x h).2 = 0)
            (Graph.sourceGhostD (visitQ D.q D.n i) D.ρ)
            (Graph.sourceGhostA (visitQ D.q D.n i) D.ρ) (fun h => v.pend g (x h))
            (fun h => v.dead g (x h).1) s = 0 := by
        unfold ghStep_subsetTerm
        exact if_neg hz
      have h0 : ghostCoefG 𝒢 D.q D.ρ D.n i g (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g)
          (s.map (Fin.castLEEmb hnB), ⟨b, p'⟩) = 0 := by
        unfold ghostCoefG
        exact if_neg fun hv => hz ((ghostValid_lift hn hnB x s).mp hv)
      rw [h0, eS, zero_mul, mul_zero, zero_mul]
  · have eT : ghostT D i v g xbg (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) U
        (s.map (Fin.castLEEmb hnB), ⟨b, p'⟩) = 0 := by
      unfold ghostT
      exact if_neg hgood
    have eB : ghStep_batchTerm (fun p : {p : ℕ // p ∈ 𝒢.big g} => (p : ℕ) ∈ U) (v.unborn g)
        (ghStep_bornW D i v g) b.val p' = 0 := by
      unfold ghStep_batchTerm
      exact if_neg fun h => hgood (hgood_iff.mpr h)
    rw [eT, eB, mul_zero]

/-! ### The sum over the choices of one group -/

/-- A triple sum of products `C · F(s) · G(b, p')` is a product of sums. -/
theorem ghStep_sum_factor {n m : ℕ} {P : Type*} [Fintype P] (C : ℝ) (F : Finset (Fin n) → ℝ)
    (G : (b : ℕ) → (Fin b → P) → ℝ) :
    ∑ s : Finset (Fin n), ∑ b : Fin (m + 1), ∑ p' : Fin b.val → P, C * F s * G b.val p' =
      C * (∑ s : Finset (Fin n), F s) * ∑ b : Fin (m + 1), ∑ p' : Fin b.val → P, G b.val p' := by
  have h1 : ∀ s : Finset (Fin n),
      ∑ b : Fin (m + 1), ∑ p' : Fin b.val → P, C * F s * G b.val p' =
        C * F s * ∑ b : Fin (m + 1), ∑ p' : Fin b.val → P, G b.val p' := by
    intro s
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun s _ => h1 s, ← Finset.sum_mul, ← Finset.mul_sum]

/-- The value of a pending particle after a visit operation: a zero terminates or continues. -/
theorem ghStep_pend_step (D : MemData 𝒢 J ℓ N) (i : ℕ) (v : PrimeVals 𝒢) (g : B) {n : ℕ}
    (x : Fin n → Particle 𝒢 g) (h : Fin n) :
    ghStep_pendFactor (fun h : Fin n => (x h).2 = 0)
        (Graph.sourceGhostD (visitQ D.q D.n i) D.ρ) (Graph.sourceGhostA (visitQ D.q D.n i) D.ρ)
        (fun h => v.pend g (x h)) (fun h => v.dead g (x h).1) h =
      (ghostStepVals D i v).pend g (x h) := by
  have e : (ghostStepVals D i v).pend g (x h) =
      if (x h).2 = 0 then
        Graph.sourceGhostD (visitQ D.q D.n i) D.ρ * v.dead g (x h).1 +
          Graph.sourceGhostA (visitQ D.q D.n i) D.ρ * v.pend g (x h)
      else v.pend g (x h) := rfl
  rw [e]
  unfold ghStep_pendFactor
  exact bigRes_ite_congr Iff.rfl rfl rfl

/-- **The factor of a group in the product of the values after a visit operation**, at the old
state: the active primes, the born primes which are not present, the pending particles and the
unborn primes. -/
theorem ghStep_evalL_step (D : MemData 𝒢 J ℓ N) (i : ℕ) (v : PrimeVals 𝒢) (g : B)
    (xbg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) {n : ℕ} (x : Fin n → Particle 𝒢 g)
    (U : Finset ℕ) :
    (ghostStepVals D i v).evalL g xbg (List.ofFn x) U =
      (∏ sl : Slot J ℓ, v.act g (xbg sl)) *
            (∏ p : {p : ℕ // p ∈ 𝒢.big g}, ghStep_factD v g xbg x U p) *
          (∏ h : Fin n, ghStep_pendFactor (fun h : Fin n => (x h).2 = 0)
            (Graph.sourceGhostD (visitQ D.q D.n i) D.ρ)
            (Graph.sourceGhostA (visitQ D.q D.n i) D.ρ) (fun h => v.pend g (x h))
            (fun h => v.dead g (x h).1) h) *
        ∏ p : {p : ℕ // p ∈ 𝒢.big g},
          ghStep_bornFactor (fun p : {p : ℕ // p ∈ 𝒢.big g} => (p : ℕ) ∈ U) (v.unborn g)
            (ghStep_bornW D i v g) p := by
  have alg : ∀ K PF FD BF : ℝ, K * PF * (FD * BF) = K * FD * PF * BF := by
    intro K PF FD BF
    ring
  have hE : (ghostStepVals D i v).evalL g xbg (List.ofFn x) U =
      (∏ sl : Slot J ℓ, v.act g (xbg sl)) *
          ((List.ofFn x).map ((ghostStepVals D i v).pend g)).prod *
        ∏ p : {p : ℕ // p ∈ 𝒢.big g}, (ghostStepVals D i v).thirdL g xbg (List.ofFn x) U p :=
    rfl
  have hP : ((List.ofFn x).map ((ghostStepVals D i v).pend g)).prod =
      ∏ h : Fin n, ghStep_pendFactor (fun h : Fin n => (x h).2 = 0)
        (Graph.sourceGhostD (visitQ D.q D.n i) D.ρ) (Graph.sourceGhostA (visitQ D.q D.n i) D.ρ)
        (fun h => v.pend g (x h)) (fun h => v.dead g (x h).1) h :=
    Eq.trans (ghStep_prod_map_ofFn x ((ghostStepVals D i v).pend g))
      (Finset.prod_congr rfl fun h _ => (ghStep_pend_step D i v g x h).symm)
  have hT : ∏ p : {p : ℕ // p ∈ 𝒢.big g},
        (ghostStepVals D i v).thirdL g xbg (List.ofFn x) U p =
      (∏ p : {p : ℕ // p ∈ 𝒢.big g}, ghStep_factD v g xbg x U p) *
        ∏ p : {p : ℕ // p ∈ 𝒢.big g},
          ghStep_bornFactor (fun p : {p : ℕ // p ∈ 𝒢.big g} => (p : ℕ) ∈ U) (v.unborn g)
            (ghStep_bornW D i v g) p :=
    Eq.trans (Finset.prod_congr rfl fun p _ => (ghStep_thirdL_step D i v g xbg x U p).symm)
      Finset.prod_mul_distrib
  rw [hE, hP, hT]
  exact alg _ _ _ _

/-- **Only the sets of positions of the memory contribute**: the sum over the local choices of a
group is a sum over the sets of positions of its memory and over the batches. -/
theorem ghostT_sum_lift (D : MemData 𝒢 J ℓ N) (i : ℕ) (v : PrimeVals 𝒢) (g : B)
    (xbg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (U : Finset ℕ) {n : ℕ} (hn : n < Bc + 1)
    (hnB : n ≤ Bc) (x : Fin n → Particle 𝒢 g) :
    ∑ c : Finset (Fin Bc) × Batch 𝒢 Bc g,
        ghostT D i v g xbg (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) U c =
      ∑ s : Finset (Fin n), ∑ b : Fin (Bc + 1), ∑ p' : Fin b.val → {p : ℕ // p ∈ 𝒢.big g},
        ghostT D i v g xbg (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) U
          (s.map (Fin.castLEEmb hnB), ⟨b, p'⟩) := by
  -- the choices: a set of indices and a batch
  have h1 : ∑ c : Finset (Fin Bc) × Batch 𝒢 Bc g,
        ghostT D i v g xbg (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) U c =
      ∑ A' : Finset (Fin Bc), ∑ b : Fin (Bc + 1), ∑ p' : Fin b.val → {p : ℕ // p ∈ 𝒢.big g},
        ghostT D i v g xbg (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) U (A', ⟨b, p'⟩) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun A' _ => ?_
    exact Fintype.sum_sigma fun β : Batch 𝒢 Bc g =>
      ghostT D i v g xbg (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) U (A', β)
  -- only sets of positions of the memory contribute
  have h2 : ∀ A' ∈ (Finset.univ : Finset (Finset (Fin Bc))),
      A' ∉ Finset.univ.map (liftSetEmb hnB) →
      (∑ b : Fin (Bc + 1), ∑ p' : Fin b.val → {p : ℕ // p ∈ 𝒢.big g},
        ghostT D i v g xbg (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) U (A', ⟨b, p'⟩)) = 0 := by
    intro A' _ hA'
    refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun p' _ => ?_
    have hnv : ¬GhostValid (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) A' :=
      fun hv => hA' (ghostValid_mem_lift hn hnB x hv)
    exact ghostT_eq_zero_of_not_valid D i v g xbg (⟨⟨n, hn⟩, x⟩ : Mem 𝒢 Bc g) U (A', ⟨b, p'⟩) hnv
  rw [h1, ← Finset.sum_subset (Finset.subset_univ _) h2]
  exact Finset.sum_map _ _ _

/-- **A visit operation acts prime by prime, in one big group** (eq:ghost-row)
[S-02:0456–0475, 0569–0581]: for a memory of the group in which every prime occurs at most once,
is born and is not active, and a cutoff `Bc ≥ #𝒫_g`, the sum over the local choices of the group
of the coefficient times the factor of the group in the product of the values at the new state is
the factor of the group in the product of the values `ghostStepVals` at the old state. -/
theorem ghostT_sum (D : MemData 𝒢 J ℓ N) (i : ℕ) (v : PrimeVals 𝒢) (g : B)
    (xbg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (z : Mem 𝒢 Bc g) (U : Finset ℕ)
    (hinj : Function.Injective fun j : Fin z.1.val => (z.2 j).1)
    (hne : ∀ sl (j : Fin z.1.val), xbg sl ≠ (z.2 j).1)
    (hU : ∀ j : Fin z.1.val, ((z.2 j).1 : ℕ) ∈ U) (hcard : (𝒢.big g).card ≤ Bc) :
    ∑ c : Finset (Fin Bc) × Batch 𝒢 Bc g, ghostT D i v g xbg z U c =
      (ghostStepVals D i v).evalL g xbg (List.ofFn z.2) U := by
  obtain ⟨⟨n, hn⟩, x⟩ := z
  have hnB : n ≤ Bc := Nat.le_of_lt_succ hn
  have hinj' : Function.Injective fun j : Fin n => (x j).1 := hinj
  have hne' : ∀ sl (j : Fin n), xbg sl ≠ (x j).1 := hne
  have hU' : ∀ j : Fin n, ((x j).1 : ℕ) ∈ U := hU
  have hcardP : Fintype.card {p : ℕ // p ∈ 𝒢.big g} ≤ Bc := by
    rw [Fintype.card_coe]
    exact hcard
  -- the sets of positions of the memory and the batches
  refine Eq.trans (ghostT_sum_lift D i v g xbg U hn hnB x) ?_
  -- the term of a set of positions and a batch
  refine Eq.trans (Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun b _ =>
    Finset.sum_congr rfl fun p' _ =>
      ghostT_lift D i v g xbg U hn hnB x hinj' hne' hU' hcard s b p') ?_
  -- the sums over the sets of positions and over the batches
  refine Eq.trans (ghStep_sum_factor _ _
    (fun (b : ℕ) (p' : Fin b → {p : ℕ // p ∈ 𝒢.big g}) =>
      ghStep_batchTerm (fun p : {p : ℕ // p ∈ 𝒢.big g} => (p : ℕ) ∈ U) (v.unborn g)
        (ghStep_bornW D i v g) b p')) ?_
  rw [ghStep_sum_subsetTerm, ghStep_sum_batchTerm _ _ _ Bc hcardP]
  -- the product of the values after the visit operation
  exact (ghStep_evalL_step D i v g xbg x U).symm

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
