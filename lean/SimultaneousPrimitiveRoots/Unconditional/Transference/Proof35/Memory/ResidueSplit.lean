module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.HistorySkeleton
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The residues at the small and at the big primes are independent coordinates

Source: `verification/stage7-sources/S-02.tex`, lines 226–240 and 293–296
(`[S-02:0226–0240, 0293–0296]`): "independent uniform residues at all group primes".

Tools for `PhaseSkeletonProof.lean` (part (A) of the proof of [S] Lemma 3.7). Nothing here
involves a skeleton.

* `resRestrict`, `resSplitEquiv`, `resSplit_sum`, `resSplit_card` — a residue vector on a disjoint
  union `Q₁ ⊔ Q₂` is a pair of residue vectors on `Q₁` and on `Q₂`; restriction commutes with
  translation (`resRestrict_shift`) and preserves divisibility (`resRestrict_hit`).
* `resS`, `resB` — the small and the big part of a residue vector at all group primes.
* `tagPos` — the position `(h, y)` of `tagModel`.
* `isPhys_tagPos_iff`, `damping_tagPos`, `stateMass_eq_small_mul_big`,
  `targetNorm_eq_small_mul_big` — `IsPhys`, `damping`, `stateMass`, `targetNorm` are products of
  a small and a big half.
* `isPhys_permuteLists_of` — physical states are stable under slot permutations.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ### Restriction of residue vectors -/

/-- The restriction of a residue vector to a subset of the primes. -/
def resRestrict {Q Q' : Finset ℕ} (h : Q' ⊆ Q) (y : ResVec Q) : ResVec Q' :=
  fun p => y ⟨p.1, h p.2⟩

/-- Restriction commutes with translation. -/
theorem resRestrict_shift {Q Q' : Finset ℕ} (h : Q' ⊆ Q) (a : ℤ) (y : ResVec Q) :
    resRestrict h ((resModel Q).shift a y) = (resModel Q').shift a (resRestrict h y) := rfl

/-- A prime of the subset divides a residue vector if and only if it divides its restriction. -/
theorem resRestrict_hit {Q Q' : Finset ℕ} (h : Q' ⊆ Q) (y : ResVec Q) {q : ℕ} (hq : q ∈ Q') :
    (resModel Q).hit q y ↔ (resModel Q').hit q (resRestrict h y) := by
  constructor
  · intro hh
    obtain ⟨_, hz⟩ : ∃ h' : q ∈ Q, y ⟨q, h'⟩ = 0 := hh
    exact (⟨hq, hz⟩ : ∃ h' : q ∈ Q', resRestrict h y ⟨q, h'⟩ = 0)
  · intro hh
    obtain ⟨h', hz⟩ : ∃ h' : q ∈ Q', resRestrict h y ⟨q, h'⟩ = 0 := hh
    exact (⟨h h', hz⟩ : ∃ h'' : q ∈ Q, y ⟨q, h''⟩ = 0)

/-- The residue vector on `Q` with the coordinates of `a` on `Q₁` and of `b` elsewhere. -/
def resGlue {Q Q₁ Q₂ : Finset ℕ} (hcov : ∀ p ∈ Q, p ∈ Q₁ ∨ p ∈ Q₂) (a : ResVec Q₁)
    (b : ResVec Q₂) : ResVec Q :=
  fun p => if h : p.1 ∈ Q₁ then a ⟨p.1, h⟩ else b ⟨p.1, (hcov p.1 p.2).resolve_left h⟩

theorem resGlue_of_mem {Q Q₁ Q₂ : Finset ℕ} (hcov : ∀ p ∈ Q, p ∈ Q₁ ∨ p ∈ Q₂) (a : ResVec Q₁)
    (b : ResVec Q₂) (p : {p : ℕ // p ∈ Q}) (h : p.1 ∈ Q₁) :
    resGlue hcov a b p = a ⟨p.1, h⟩ :=
  dif_pos h

theorem resGlue_of_not_mem {Q Q₁ Q₂ : Finset ℕ} (hcov : ∀ p ∈ Q, p ∈ Q₁ ∨ p ∈ Q₂)
    (a : ResVec Q₁) (b : ResVec Q₂) (p : {p : ℕ // p ∈ Q}) (h : p.1 ∉ Q₁) :
    resGlue hcov a b p = b ⟨p.1, (hcov p.1 p.2).resolve_left h⟩ :=
  dif_neg h

/-- **A residue vector on a disjoint union is a pair of residue vectors.** -/
def resSplitEquiv {Q Q₁ Q₂ : Finset ℕ} (h₁ : Q₁ ⊆ Q) (h₂ : Q₂ ⊆ Q)
    (hcov : ∀ p ∈ Q, p ∈ Q₁ ∨ p ∈ Q₂) (hd : Disjoint Q₁ Q₂) :
    ResVec Q ≃ ResVec Q₁ × ResVec Q₂ where
  toFun y := (resRestrict h₁ y, resRestrict h₂ y)
  invFun t := resGlue hcov t.1 t.2
  left_inv y := by
    funext p
    by_cases h : p.1 ∈ Q₁
    · exact resGlue_of_mem hcov _ _ p h
    · exact resGlue_of_not_mem hcov _ _ p h
  right_inv t := by
    obtain ⟨a, b⟩ := t
    refine Prod.ext (funext fun p => ?_) (funext fun p => ?_)
    · exact resGlue_of_mem hcov a b ⟨p.1, h₁ p.2⟩ p.2
    · exact resGlue_of_not_mem hcov a b ⟨p.1, h₂ p.2⟩
        (fun h => Finset.disjoint_left.mp hd h p.2)

/-- A sum over the residue vectors on a disjoint union is a double sum. -/
theorem resSplit_sum {Q Q₁ Q₂ : Finset ℕ} (h₁ : Q₁ ⊆ Q) (h₂ : Q₂ ⊆ Q)
    (hcov : ∀ p ∈ Q, p ∈ Q₁ ∨ p ∈ Q₂) (hd : Disjoint Q₁ Q₂) (F : ResVec Q₁ → ResVec Q₂ → ℂ) :
    ∑ y : ResVec Q, F (resRestrict h₁ y) (resRestrict h₂ y) =
      ∑ a : ResVec Q₁, ∑ b : ResVec Q₂, F a b :=
  (Equiv.sum_comp (resSplitEquiv h₁ h₂ hcov hd)
    (fun t : ResVec Q₁ × ResVec Q₂ => F t.1 t.2)).trans
    (Fintype.sum_prod_type fun t : ResVec Q₁ × ResVec Q₂ => F t.1 t.2)

/-- The number of residue vectors on a disjoint union. -/
theorem resSplit_card {Q Q₁ Q₂ : Finset ℕ} (h₁ : Q₁ ⊆ Q) (h₂ : Q₂ ⊆ Q)
    (hcov : ∀ p ∈ Q, p ∈ Q₁ ∨ p ∈ Q₂) (hd : Disjoint Q₁ Q₂) :
    Fintype.card (ResVec Q) = Fintype.card (ResVec Q₁) * Fintype.card (ResVec Q₂) :=
  (Fintype.card_congr (resSplitEquiv h₁ h₂ hcov hd)).trans (Fintype.card_prod _ _)

/-! ### Positions with offset -/

/-- The position `(h, y)` of `tagModel Q`: the integer offset `h` and the residues `y`. -/
def tagPos {Q : Finset ℕ} (a : ℤ) (y : ResVec Q) : (tagModel Q).Pos := (a, y)

/-- `hit` only counts the hits of a group. -/
theorem phSkel_countHits_congr {hit hit' : ℕ → Prop} {s : Finset ℕ}
    (h : ∀ p ∈ s, hit p ↔ hit' p) : countHits hit s = countHits hit' s := by
  classical
  unfold countHits
  exact congrArg Finset.card (Finset.filter_congr h)

/-! ### The small and the big primes of a family -/

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ}

omit [DecidableEq S] [DecidableEq B] in
theorem smallPrimes_subset_all (𝒢 : GroupFamily S B) : smallPrimes 𝒢 ⊆ 𝒢.allPrimes := by
  rw [allPrimes_eq]
  exact Finset.subset_union_left

omit [DecidableEq S] [DecidableEq B] in
theorem bigPrimes_subset_all (𝒢 : GroupFamily S B) : bigPrimes 𝒢 ⊆ 𝒢.allPrimes := by
  rw [allPrimes_eq]
  exact Finset.subset_union_right

omit [DecidableEq S] [DecidableEq B] in
theorem allPrimes_cover (𝒢 : GroupFamily S B) :
    ∀ p ∈ 𝒢.allPrimes, p ∈ smallPrimes 𝒢 ∨ p ∈ bigPrimes 𝒢 := by
  intro p hp
  rw [allPrimes_eq] at hp
  exact Finset.mem_union.mp hp

omit [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem mem_smallPrimes_of {g : S} {p : ℕ} (hp : p ∈ 𝒢.small g) : p ∈ smallPrimes 𝒢 := by
  unfold smallPrimes
  exact Finset.mem_biUnion.mpr ⟨g, Finset.mem_univ g, hp⟩

/-- The residues at the small primes. -/
def resS (𝒢 : GroupFamily S B) (y : ResVec 𝒢.allPrimes) : ResVec (smallPrimes 𝒢) :=
  resRestrict (smallPrimes_subset_all 𝒢) y

/-- The residues at the big primes. -/
def resB (𝒢 : GroupFamily S B) (y : ResVec 𝒢.allPrimes) : ResVec (bigPrimes 𝒢) :=
  resRestrict (bigPrimes_subset_all 𝒢) y

omit [DecidableEq S] [DecidableEq B] in
/-- **`IsPhys` is the conjunction of its small and its big half**: a physical state at the
position `(h, y)` is a small state at the small residues and a big state at the big residues. -/
theorem isPhys_tagPos_iff (a : ℤ) (y : ResVec 𝒢.allPrimes) (x : Lists 𝒢 J ℓ) :
    IsPhys (tagModel 𝒢.allPrimes) (tagPos a y) x ↔
      IsSmallState 𝒢 (resS 𝒢 y) x.1 ∧ IsBigState 𝒢 (resB 𝒢 y) x.2 := by
  have hS : ∀ g i, (tagModel 𝒢.allPrimes).hit (x.1 g i) (tagPos a y) ↔
      (resModel (smallPrimes 𝒢)).hit (x.1 g i) (resS 𝒢 y) := fun g i =>
    resRestrict_hit (smallPrimes_subset_all 𝒢) y (mem_smallPrimes_of (x.1 g i).2)
  have hB : ∀ g i, (tagModel 𝒢.allPrimes).hit (x.2 g i) (tagPos a y) ↔
      (resModel (bigPrimes 𝒢)).hit (x.2 g i) (resB 𝒢 y) := fun g i =>
    resRestrict_hit (bigPrimes_subset_all 𝒢) y (mem_bigPrimes.mpr ⟨g, (x.2 g i).2⟩)
  unfold IsPhys IsSmallState IsBigState
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨h1, fun g i => (hS g i).mp (h3 g i)⟩, ⟨h2, fun g i => (hB g i).mp (h4 g i)⟩⟩
  · rintro ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
    exact ⟨h1, h2, fun g i => (hS g i).mpr (h3 g i), fun g i => (hB g i).mpr (h4 g i)⟩

omit [DecidableEq S] [DecidableEq B] in
/-- **`damping` is the product of its small and its big half** (for `q > 0`):
`q^{(ω - Ms)/2} = ∏_{g ∈ 𝒮} q^{(ω_g - M)/2} · ∏_{g ∈ ℬ} q^{(ω_g - M)/2}`. -/
theorem damping_tagPos {q : ℝ} (hq : 0 < q) (a : ℤ) (y : ResVec 𝒢.allPrimes) :
    damping (tagModel 𝒢.allPrimes) 𝒢 J ℓ q (tagPos a y) =
      smallDamping 𝒢 J ℓ q (resS 𝒢 y) * bigDamping 𝒢 J ℓ q (resB 𝒢 y) := by
  have hS : ∀ g : S,
      countHits (fun p => (tagModel 𝒢.allPrimes).hit p (tagPos a y)) (𝒢.small g) =
        countHits (fun p => (resModel (smallPrimes 𝒢)).hit p (resS 𝒢 y)) (𝒢.small g) :=
    fun g => phSkel_countHits_congr fun p hp =>
      resRestrict_hit (smallPrimes_subset_all 𝒢) y (mem_smallPrimes_of hp)
  have hB : ∀ g : B,
      countHits (fun p => (tagModel 𝒢.allPrimes).hit p (tagPos a y)) (𝒢.big g) =
        countHits (fun p => (resModel (bigPrimes 𝒢)).hit p (resB 𝒢 y)) (𝒢.big g) :=
    fun g => phSkel_countHits_congr fun p hp =>
      resRestrict_hit (bigPrimes_subset_all 𝒢) y (mem_bigPrimes.mpr ⟨g, hp⟩)
  have hexp : (((𝒢.omegaOf (fun p => (tagModel 𝒢.allPrimes).hit p (tagPos a y)) : ℕ) : ℝ) -
        ((J + ℓ : ℕ) : ℝ) * ((groupCount S B : ℕ) : ℝ)) / 2 =
      (((∑ g, countHits (fun p => (resModel (smallPrimes 𝒢)).hit p (resS 𝒢 y))
            (𝒢.small g) : ℕ) : ℝ) - ((J + ℓ : ℕ) : ℝ) * (Fintype.card S : ℝ)) / 2 +
        (((∑ g, countHits (fun p => (resModel (bigPrimes 𝒢)).hit p (resB 𝒢 y))
            (𝒢.big g) : ℕ) : ℝ) - ((J + ℓ : ℕ) : ℝ) * (Fintype.card B : ℝ)) / 2 := by
    unfold GroupFamily.omegaOf groupCount
    rw [Finset.sum_congr rfl fun g _ => hS g, Finset.sum_congr rfl fun g _ => hB g]
    push_cast
    ring
  have h1 : damping (tagModel 𝒢.allPrimes) 𝒢 J ℓ q (tagPos a y) =
      q ^ ((((∑ g, countHits (fun p => (resModel (smallPrimes 𝒢)).hit p (resS 𝒢 y))
            (𝒢.small g) : ℕ) : ℝ) - ((J + ℓ : ℕ) : ℝ) * (Fintype.card S : ℝ)) / 2 +
        (((∑ g, countHits (fun p => (resModel (bigPrimes 𝒢)).hit p (resB 𝒢 y))
            (𝒢.big g) : ℕ) : ℝ) - ((J + ℓ : ℕ) : ℝ) * (Fintype.card B : ℝ)) / 2) :=
    congrArg (fun t : ℝ => q ^ t) hexp
  exact h1.trans (Real.rpow_add hq _ _)

omit [DecidableEq S] [DecidableEq B] in
/-- `stateMass` is the product of its small and its big half. -/
theorem stateMass_eq_small_mul_big (𝒢 : GroupFamily S B) (J ℓ : ℕ) :
    stateMass 𝒢 J ℓ = smallListMass 𝒢 J ℓ * bigListNorm 𝒢 J ℓ := rfl

omit [DecidableEq S] [DecidableEq B] in
/-- `targetNorm` is the product of its small and its big half. -/
theorem targetNorm_eq_small_mul_big (𝒢 : GroupFamily S B) (ℓ : ℕ) (C : B → Finset (Fin J)) :
    targetNorm 𝒢 ℓ C =
      (∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) * bigTargetNorm 𝒢 ℓ C :=
  rfl

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- Physical states are stable under slot permutations. -/
theorem isPhys_permuteLists_of (𝔭 : PosModel) (π : SlotPerms S J ℓ × SlotPerms B J ℓ)
    {n : 𝔭.Pos} {x : Lists 𝒢 J ℓ} (h : IsPhys 𝔭 n x) : IsPhys 𝔭 n (permuteLists π x) :=
  ⟨fun g _ _ hab => (π.1 g).injective (h.1 g hab),
    fun g _ _ hab => (π.2 g).injective (h.2.1 g hab),
    fun g i => h.2.2.1 g (π.1 g i), fun g i => h.2.2.2 g (π.2 g i)⟩

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
