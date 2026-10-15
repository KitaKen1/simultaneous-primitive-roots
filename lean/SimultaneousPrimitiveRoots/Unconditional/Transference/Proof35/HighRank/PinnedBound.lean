module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.HighRank.PinnedPath
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.BoundaryMass
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Large rank: the absolute contribution of a collection of equality blocks

Source: `verification/stage7-sources/S-02.tex`, lines 1107–1155 (`[S-02:1107–1155]`).

This file puts the pieces together for an arbitrary family of groups with explicit hypotheses.

* `hrAddrGroup`, `hrAddrMass`, `History.hr_birth_mem` — the big group of a birth address; the
  point mass of `μ̃_g` at an address; a performed birth value is a prime of the group of its
  address.
* `hr_init_le` — "initial active slots satisfy the same product estimate" [S-02:1135–1136]: the
  mass of the initial states whose big list realizes prescribed values is at most the product of
  the point masses times `∏_{g ∈ ℬ} max(1, M_max)^M` (the small part has mass at most one,
  (eq:initial-factorial-mass)).
* `hrPathConst`, `hr_pinned_le` — **the absolute path sum with prescribed birth values**: for every
  partial assignment `pv` of prime values to the birth addresses,
  `∑_{h realizing pv} |weight(h)| ≤ K₀ R_g^{N+1} R_e^N · ∏_{a pinned} μ̃_{g(a)}(pv a)`, where `R_g`,
  `R_e` are the row constants of `ghost_rowBound` and `edgeAbs_rowBound`.
* `hr_absRankPart_le` — **(eq:high-rank-path-bound) for a general family**: for every collection
  `π` of disjoint blocks of at least two addresses,
  `absRankPart π ≤ K₀ R_g^{N+1} R_e^N · (max(1, M_max) · μ_max)^{r(π)}`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### The group of an address -/

section HrAddr

variable {S B : Type} {J ℓ Bc n : ℕ}

/-- The big group of a birth address. -/
def hrAddrGroup : BirthAddr B J ℓ Bc n → B
  | Sum.inl a => a.1
  | Sum.inr (Sum.inl a) => a.2.1
  | Sum.inr (Sum.inr a) => a.2.1

/-- The point mass of the tilted law of the group of the address `a` at the natural number `z`. -/
def hrAddrMass (𝒢 : GroupFamily S B) (q : ℝ) (n' : ℕ) (a : BirthAddr B J ℓ Bc n) (z : ℕ) : ℝ :=
  hrPtMass 𝒢 q n' (hrAddrGroup a) z

end HrAddr

/-- A scalar identity: the product of the row constants of the `N` double steps and of the last
visit operation. -/
theorem hr_scalar_prod (Rg Re : ℝ) (gW eW : ℕ → ℝ) (n : ℕ) :
    (∏ i ∈ Finset.range n, ((Rg * gW i) * (Re * eW i))) * (Rg * gW n) =
      (Rg ^ (n + 1) * Re ^ n) *
        ((∏ i ∈ Finset.range n, eW i) * ∏ i ∈ Finset.range (n + 1), gW i) := by
  have h1 : ∏ i ∈ Finset.range n, ((Rg * gW i) * (Re * eW i)) =
      Rg ^ n * (∏ i ∈ Finset.range n, gW i) * (Re ^ n * ∏ i ∈ Finset.range n, eW i) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.prod_const, Finset.card_range]
  rw [h1, Finset.prod_range_succ, pow_succ]
  ring

/-- A product over the birth addresses is the product over the initial slots, the target slots of
the edges and the batch indices of the visits. -/
theorem hr_prod_addr (B : Type) [Fintype B] (J ℓ Bc n : ℕ) (f : BirthAddr B J ℓ Bc n → ℝ) :
    ∏ a, f a = (∏ g, ∏ sl, f (Sum.inl (g, sl))) *
      ((∏ i : Fin n, ∏ g, ∏ sl, f (Sum.inr (Sum.inl (i, g, sl)))) *
        ∏ i : Fin (n + 1), ∏ g, ∏ j, f (Sum.inr (Sum.inr (i, g, j)))) := by
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type]

/-! ### The initial boundary -/

section HrInit

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] {J ℓ : ℕ}

open _root_.Classical in
/-- **The initial boundary with prescribed values** [S-02:1135–1136, 1148–1150]: "initial active
slots satisfy the same product estimate"; "at the initial boundary `w = 1`, and the remaining
integrated boundary mass is bounded". The mass of the initial states whose big active list
realizes the prescribed values is at most the product of the point masses of these values times
`∏_{g ∈ ℬ} max(1, M_max)^M`. -/
theorem hr_init_le (𝒢 : GroupFamily S B) {q : ℝ} {n : ℕ} {Mmax : ℝ} (Bc : ℕ)
    (hposS : ∀ g, ∀ p ∈ 𝒢.small g, 0 < p)
    (hdisjS : ∀ g g', g ≠ g' → Disjoint (𝒢.small g) (𝒢.small g'))
    (hVS : ∀ g, 0 < Graph.primeGroupReciprocalMass (𝒢.small g))
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p)
    (hM : ∀ g, ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) q n p ≤ Mmax)
    (pv : (g : B) → Slot J ℓ → Option ℕ) :
    ∑ a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
        hrIndI pv a.2.2 * memWeight 𝒢 q n (initState a Bc) ≤
      (∏ g, ∏ sl, hrW (hrPtMass 𝒢 q n g) (pv g sl)) * ∏ _g : B, (max 1 Mmax) ^ (J + ℓ) := by
  have hM1 : (1 : ℝ) ≤ max 1 Mmax := le_max_left _ _
  have hM0 : (0 : ℝ) ≤ max 1 Mmax := zero_le_one.trans hM1
  have hRHS : 0 ≤ (∏ g, ∏ sl, hrW (hrPtMass 𝒢 q n g) (pv g sl)) *
      ∏ _g : B, (max 1 Mmax) ^ (J + ℓ) :=
    mul_nonneg
      (Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun sl _ =>
        hrW_nonneg (hrPtMass_nonneg (hν g)) _)
      (Finset.prod_nonneg fun _ _ => pow_nonneg hM0 _)
  have hbig0 : ∀ xb : LabelList 𝒢.big J ℓ, 0 ≤ hrIndI pv xb * bigListMass 𝒢 q n xb := fun xb =>
    mul_nonneg (hrIndI_nonneg _ _)
      (Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun i _ => hν g _ (xb g i).2)
  -- the big active list
  have hbig : ∑ xb : LabelList 𝒢.big J ℓ, hrIndI pv xb * bigListMass 𝒢 q n xb ≤
      (∏ g, ∏ sl, hrW (hrPtMass 𝒢 q n g) (pv g sl)) * ∏ _g : B, (max 1 Mmax) ^ (J + ℓ) := by
    rcases isEmpty_or_nonempty (LabelList 𝒢.big J ℓ) with hE | ⟨⟨x₀⟩⟩
    · rw [Finset.univ_eq_empty, Finset.sum_empty]
      exact hRHS
    · have hlist := hr_sum_labelList_le 𝒢 hν (fun g => (hM g).trans (le_max_right _ _)) hM1
        (fun _ => (Finset.univ : Finset (Slot J ℓ))) x₀ pv
      have hcard : ∏ _g : B, (max 1 Mmax) ^ (Finset.univ : Finset (Slot J ℓ)).card =
          ∏ _g : B, (max 1 Mmax) ^ (J + ℓ) := by
        rw [Finset.card_univ, card_slot]
      rw [hcard] at hlist
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun xb _ => ?_)) hlist
      by_cases hc : ∀ g sl z, pv g sl = some z → (xb g sl : ℕ) = z
      · rw [hrIndI_of hc, one_mul]
        exact (if_pos (And.intro (fun g sl hsl => absurd (Finset.mem_univ sl) hsl)
          (fun g sl z hz => And.intro (Finset.mem_univ sl) (hc g sl z hz)))).symm
      · have hz : hrIndI pv xb = 0 := by
          unfold hrIndI
          exact if_neg hc
        rw [hz, zero_mul]
        exact (if_neg fun h => hc fun g sl z hz => (h.2 g sl z hz).2).symm
  -- the measure of an initial state
  have hmem1 : memMass 𝒢 q n (fun g => emptyMem 𝒢 Bc g) = 1 :=
    Finset.prod_eq_one fun g _ => boundary_pointMass_zero _ _
  have hterm : ∀ a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
      hrIndI pv a.2.2 * memWeight 𝒢 q n (initState a Bc) =
        (if IsSmallState 𝒢 a.1 a.2.1 then haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ
          else 0) * (hrIndI pv a.2.2 * bigListMass 𝒢 q n a.2.2) := by
    intro a
    have h1 : memWeight 𝒢 q n (initState a Bc) =
        (if IsSmallState 𝒢 a.1 a.2.1 then haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ
          else 0) * bigListMass 𝒢 q n a.2.2 * memMass 𝒢 q n (fun g => emptyMem 𝒢 Bc g) :=
      boundary_memWeight_factor 𝒢 q n a.1 a.2.1 a.2.2 _
    rw [h1, hmem1]
    ring
  have hsplit : ∑ a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
        (if IsSmallState 𝒢 a.1 a.2.1 then haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ
          else 0) * (hrIndI pv a.2.2 * bigListMass 𝒢 q n a.2.2) =
      ∑ y : ResVec (smallPrimes 𝒢), ∑ xs : LabelList 𝒢.small J ℓ,
        ∑ xb : LabelList 𝒢.big J ℓ,
          (if IsSmallState 𝒢 y xs then haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ
            else 0) * (hrIndI pv xb * bigListMass 𝒢 q n xb) :=
    sum_equiv_triple_real (Equiv.refl _) (fun y xs xb =>
      (if IsSmallState 𝒢 y xs then haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ
        else 0) * (hrIndI pv xb * bigListMass 𝒢 q n xb))
  calc ∑ a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
        hrIndI pv a.2.2 * memWeight 𝒢 q n (initState a Bc)
      = ∑ a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
          (if IsSmallState 𝒢 a.1 a.2.1 then haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ
            else 0) * (hrIndI pv a.2.2 * bigListMass 𝒢 q n a.2.2) :=
        Finset.sum_congr rfl fun a _ => hterm a
    _ = ∑ y : ResVec (smallPrimes 𝒢), ∑ xs : LabelList 𝒢.small J ℓ,
          ∑ xb : LabelList 𝒢.big J ℓ,
            (if IsSmallState 𝒢 y xs then haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ
              else 0) * (hrIndI pv xb * bigListMass 𝒢 q n xb) := hsplit
    _ = (∑ y : ResVec (smallPrimes 𝒢), ∑ xs : LabelList 𝒢.small J ℓ,
          (if IsSmallState 𝒢 y xs then haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ
            else 0)) * ∑ xb : LabelList 𝒢.big J ℓ, hrIndI pv xb * bigListMass 𝒢 q n xb := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun xs _ => ?_
        rw [Finset.mul_sum]
    _ ≤ 1 * ((∏ g, ∏ sl, hrW (hrPtMass 𝒢 q n g) (pv g sl)) *
          ∏ _g : B, (max 1 Mmax) ^ (J + ℓ)) :=
        mul_le_mul (boundary_smallPart_le_one 𝒢 hposS hdisjS hVS J ℓ) hbig
          (Finset.sum_nonneg fun xb _ => hbig0 xb) zero_le_one
    _ = (∏ g, ∏ sl, hrW (hrPtMass 𝒢 q n g) (pv g sl)) * ∏ _g : B, (max 1 Mmax) ^ (J + ℓ) :=
        one_mul _

end HrInit

/-! ### The absolute path sum -/

section HrBound

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N]

omit [Fintype B] [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- **A performed birth value is a prime of the big group of its address.** -/
theorem History.hr_birth_mem {D : MemData 𝒢 J ℓ N} {Bc : ℕ} (h : History D Bc)
    (a : BirthAddr B J ℓ Bc D.n) (z : ℕ) (hz : h.birth a = some z) :
    z ∈ 𝒢.big (hrAddrGroup a) := by
  rcases a with a | a | a
  · have h1 : (h.xb₀ a.1 a.2 : ℕ) = z := Option.some.inj hz
    rw [← h1]
    exact (h.xb₀ a.1 a.2).2
  · by_cases hf : Fresh (h.edge a.1).2.1 a.2.1 a.2.2
    · have h2 : h.birth (Sum.inr (Sum.inl a)) =
          some (((h.edge a.1).2.1.xbT a.2.1 a.2.2 : {p : ℕ // p ∈ 𝒢.big a.2.1}) : ℕ) :=
        if_pos hf
      rw [h2] at hz
      rw [← Option.some.inj hz]
      exact ((h.edge a.1).2.1.xbT a.2.1 a.2.2).2
    · have h2 : h.birth (Sum.inr (Sum.inl a)) = none := if_neg hf
      rw [h2] at hz
      exact absurd hz (Option.some_ne_none z).symm
  · by_cases hj : a.2.2.val < (h.ghost a.1 a.2.1).2.1.val
    · have h2 : h.birth (Sum.inr (Sum.inr a)) =
          some (((h.ghost a.1 a.2.1).2.2 ⟨a.2.2.val, hj⟩ : {p : ℕ // p ∈ 𝒢.big a.2.1}) : ℕ) :=
        dif_pos hj
      rw [h2] at hz
      rw [← Option.some.inj hz]
      exact ((h.ghost a.1 a.2.1).2.2 ⟨a.2.2.val, hj⟩).2
    · have h2 : h.birth (Sum.inr (Sum.inr a)) = none := dif_neg hj
      rw [h2] at hz
      exact absurd hz (Option.some_ne_none z).symm

/-- **The constant of the absolute path sum**: `K₀ R_g^{N+1} R_e^N`, where
`K₀ = ∏_{g ∈ ℬ} max(1, M_max)^M` bounds the initial boundary mass,
`R_g = ∏_{g ∈ ℬ} e^{c_max v M_max}` is the row constant of the absolute visit operations
(`ghost_rowBound`) and `R_e = (∑_ν sup |K_ν|) (∏_{g ∈ 𝒮} C_𝒮) (∏_{g ∈ ℬ} C_ℬ max(1, M_max)^T)` the
row constant of the absolute edges (`edgeAbs_rowBound`). -/
def hrPathConst (D : MemData 𝒢 J ℓ N) (v vMinus Mmax cmax : ℝ) (T : ℕ) : ℝ :=
  (∏ _g : B, (max 1 Mmax) ^ (J + ℓ)) *
    ((∏ _g : B, Real.exp (cmax * v * Mmax)) ^ (D.n + 1) *
      (patternMass D.fam *
        ((∏ _g : S, Schur.groupConst vMinus D.q T) *
          (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * ∏ _g : B, (max 1 Mmax) ^ T)) ^ D.n)

omit [DecidableEq S] in
theorem hrPathConst_nonneg (D : MemData 𝒢 J ℓ N) {v vMinus Mmax cmax : ℝ} (T : ℕ)
    (hρ0 : 0 < D.ρ) (hρ1 : D.ρ < 1) (hv : 0 ≤ v) : 0 ≤ hrPathConst D v vMinus Mmax cmax T := by
  have hrowC0 : 0 ≤ edgeAbsRowConst vMinus D.ρ v T := by
    unfold edgeAbsRowConst
    exact mul_nonneg (pow_nonneg (mul_nonneg zero_le_two hv) _)
      (mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
        (l38_countSup_nonneg _ hρ0 hρ1))
  have hRe0 : 0 ≤ patternMass D.fam *
      ((∏ _g : S, Schur.groupConst vMinus D.q T) *
        (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * ∏ _g : B, (max 1 Mmax) ^ T) :=
    mul_nonneg (patternMass_nonneg D.fam)
      (mul_nonneg
        (mul_nonneg
          (Finset.prod_nonneg fun _ _ => zero_le_one.trans (Schur.one_le_groupConst _ _ _))
          (Finset.prod_nonneg fun _ _ => hrowC0))
        (Finset.prod_nonneg fun _ _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _))
  unfold hrPathConst
  exact mul_nonneg
    (Finset.prod_nonneg fun _ _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
    (mul_nonneg (pow_nonneg (Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le) _)
      (pow_nonneg hRe0 _))

open _root_.Classical in
/-- **The absolute path sum with prescribed birth values** [S-02:1121–1151]. For a family of
groups with `0 < q < 1`, `0 < ρ < 1`, `v ≥ 1`, `V_g ≥ v₋ > 0`, `μ̃_g ≥ 0`,
`1 ≤ μ̃_g(𝒫_g) ≤ M_max`, at most `T` unshared slots, and the conditions (eq:memory-weight-choice)
on `v` at every visit: for every partial assignment `pv` of prime values to the birth addresses,

`∑_{h realizing pv} |weight(h)| ≤ K₀ R_g^{N+1} R_e^N · ∏_{a : pv a = some z} μ̃_{g(a)}(z)`.

Every address with a prescribed value contributes the point mass of its tilted law at that value
in the place of the total mass. -/
theorem hr_pinned_le (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ) {v vMinus Mmax cmax : ℝ} {T : ℕ}
    (hq0 : 0 < D.q) (hq1 : D.q < 1) (hρ0 : 0 < D.ρ) (hρ1 : D.ρ < 1) (hv : 1 ≤ v)
    (hvm : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hposS : ∀ g, ∀ p ∈ 𝒢.small g, 0 < p)
    (hdisjS : ∀ g g', g ≠ g' → Disjoint (𝒢.small g) (𝒢.small g'))
    (hlaw : ∀ g, ∑ p ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) p = 1)
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p)
    (h1 : ∀ g, 1 ≤ ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) D.q D.n p)
    (hM : ∀ g, ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax)
    (hT : 0 < T) (hℓT : ℓ ≤ T) (hC : ∀ ν g, ℓ + ((D.fam ν).C g).card ≤ T)
    (hA : ∀ i, i ≤ D.n → 0 ≤ Graph.sourceGhostA (visitQ D.q D.n i) D.ρ)
    (hbase : ∀ i, i ≤ D.n → Graph.sourceGhostA (visitQ D.q D.n i) D.ρ +
      |Graph.sourceGhostD (visitQ D.q D.n i) D.ρ| / v ≤ 1)
    (hCg : ∀ i, i ≤ D.n → ∀ g,
      |2 * Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g))
        (visitQ D.q D.n i) D.ρ| ≤ cmax)
    (pv : BirthAddr B J ℓ Bc D.n → Option ℕ) :
    ∑ h : History D Bc, (if HrPinned pv h.birth then ‖h.weight θ‖ else 0) ≤
      hrPathConst D v vMinus Mmax cmax T * ∏ a, hrW (hrAddrMass 𝒢 D.q D.n a) (pv a) := by
  have hv0 : 0 < v := lt_of_lt_of_le zero_lt_one hv
  have hm : ∀ s : MState 𝒢 J ℓ Bc, 0 ≤ memWeight 𝒢 D.q D.n s :=
    memWeight_nonneg 𝒢 D.q D.n hν
  have hMsub : ∀ g : B, ∑ p : {p : ℕ // p ∈ 𝒢.big g}, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax :=
    fun g => (Finset.sum_coe_sort (𝒢.big g)
      (fun p => tiltLaw (𝒢.big g) D.q D.n p)).trans_le (hM g)
  -- the constants
  obtain ⟨Rg, hRg⟩ : ∃ Rg : ℝ, Rg = ∏ _g : B, Real.exp (cmax * v * Mmax) := ⟨_, rfl⟩
  obtain ⟨Re, hRe⟩ : ∃ Re : ℝ, Re = patternMass D.fam *
      ((∏ _g : S, Schur.groupConst vMinus D.q T) *
        (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * ∏ _g : B, (max 1 Mmax) ^ T) := ⟨_, rfl⟩
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = ∏ _g : B, (max 1 Mmax) ^ (J + ℓ) := ⟨_, rfl⟩
  obtain ⟨gW, hgW⟩ : ∃ gW : ℕ → ℝ, ∀ i,
      gW i = ∏ g, ∏ j, hrW (hrPtMass 𝒢 D.q D.n g) (hrPinG pv i g j) := ⟨_, fun _ => rfl⟩
  obtain ⟨eW, heW⟩ : ∃ eW : ℕ → ℝ, ∀ i,
      eW i = ∏ g, ∏ sl, hrW (hrPtMass 𝒢 D.q D.n g) (hrPinE pv i g sl) := ⟨_, fun _ => rfl⟩
  obtain ⟨iW, hiW⟩ : ∃ iW : ℝ,
      iW = ∏ g, ∏ sl, hrW (hrPtMass 𝒢 D.q D.n g) (hrPinI pv g sl) := ⟨_, rfl⟩
  have hW0 : ∀ (g : B) (o : Option ℕ), 0 ≤ hrW (hrPtMass 𝒢 D.q D.n g) o := fun g o =>
    hrW_nonneg (hrPtMass_nonneg (hν g)) o
  have hgW0 : ∀ i, 0 ≤ gW i := fun i => by
    rw [hgW]
    exact Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun j _ => hW0 g _
  have heW0 : ∀ i, 0 ≤ eW i := fun i => by
    rw [heW]
    exact Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun sl _ => hW0 g _
  have hRg0 : 0 ≤ Rg := by
    rw [hRg]
    exact Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le
  have hrowC0 : 0 ≤ edgeAbsRowConst vMinus D.ρ v T := by
    unfold edgeAbsRowConst
    exact mul_nonneg (pow_nonneg (mul_nonneg zero_le_two hv0.le) _)
      (mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
        (l38_countSup_nonneg _ hρ0 hρ1))
  have hRe0 : 0 ≤ Re := by
    rw [hRe]
    exact mul_nonneg (patternMass_nonneg D.fam)
      (mul_nonneg
        (mul_nonneg
          (Finset.prod_nonneg fun _ _ => zero_le_one.trans (Schur.one_le_groupConst _ _ _))
          (Finset.prod_nonneg fun _ _ => hrowC0))
        (Finset.prod_nonneg fun _ _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _))
  -- the three kinds of operations
  have hG : ∀ i, i ≤ D.n → ∀ s : MState 𝒢 J ℓ Bc,
      ∑ c : GhostChoice 𝒢 Bc,
          hrIndG (hrPinG pv i) c * |ghostCoef D i s c| * schurWeight v (ghostTgt s c) ≤
        Rg * gW i * schurWeight v s := by
    intro i hi s
    rw [hRg, hgW]
    exact hr_ghost_row_pinned D Bc i hν h1 (hA i hi) hv0 (hbase i hi) (hCg i hi) hMsub
      (hrPinG pv i) s
  have hE : ∀ i, i < D.n → ∀ s : MState 𝒢 J ℓ Bc,
      ∑ ξ : EdgeFullChoice D Bc,
          ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ * hrIndE (hrPinE pv i) (edgeBirths ξ.2.1) *
            schurWeight v (edgeFullTgt D i s ξ) ≤
        Re * eW i * schurWeight v s := by
    intro i _ s
    rw [hRe, heW]
    exact hr_edge_row_pinned D θ i hq0 hq1 hρ0 hρ1 hv hvm hVS hVB hlaw hν hM hT hℓT hC
      (hrPinE pv i) s
  have hI : ∑ a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
      hrIndI (hrPinI pv) a.2.2 * memWeight 𝒢 D.q D.n (initState a Bc) ≤ iW * K₀ := by
    rw [hiW, hK₀]
    exact hr_init_le 𝒢 Bc hposS hdisjS (fun g => lt_of_lt_of_le hvm (hVS g)) hν hM (hrPinI pv)
  have hpath := hr_pinnedPath_le D Bc θ pv hv hm (fun i => Rg * gW i) (fun i => Re * eW i)
    (fun i => mul_nonneg hRg0 (hgW0 i)) (fun i => mul_nonneg hRe0 (heW0 i)) hG hE hI
  -- the product of the weights is the product over the addresses
  have hprodE : ∏ i ∈ Finset.range D.n, eW i =
      ∏ i : Fin D.n, ∏ g, ∏ sl,
        hrW (hrPtMass 𝒢 D.q D.n g) (pv (Sum.inr (Sum.inl (i, g, sl)))) := by
    rw [Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [heW]
    exact Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun sl _ => by
      rw [hrPinE_fin]
  have hprodG : ∏ i ∈ Finset.range (D.n + 1), gW i =
      ∏ i : Fin (D.n + 1), ∏ g, ∏ j,
        hrW (hrPtMass 𝒢 D.q D.n g) (pv (Sum.inr (Sum.inr (i, g, j)))) := by
    rw [Finset.prod_range]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hgW]
    exact Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun j _ => by
      rw [hrPinG_fin]
  have hprod : ∏ a, hrW (hrAddrMass 𝒢 D.q D.n a) (pv a) =
      iW * ((∏ i ∈ Finset.range D.n, eW i) * ∏ i ∈ Finset.range (D.n + 1), gW i) := by
    rw [hr_prod_addr B J ℓ Bc D.n (fun a => hrW (hrAddrMass 𝒢 D.q D.n a) (pv a)), hprodE,
      hprodG, hiW]
    rfl
  refine hpath.trans (le_of_eq ?_)
  rw [hprod, hr_scalar_prod Rg Re gW eW D.n]
  unfold hrPathConst
  rw [← hRg, ← hRe, ← hK₀]
  ring

open _root_.Classical in
/-- **(eq:high-rank-path-bound) for a general family** [S-02:1107–1155]: under the hypotheses of
`hr_pinned_le` and `μ̃_g(p) ≤ μ_max` (eq:tilted-point-mass), for every collection `π` of disjoint
blocks of at least two birth addresses

`absRankPart π ≤ K₀ R_g^{N+1} R_e^N · (max(1, M_max) · μ_max)^{r(π)}`:

"the total absolute contribution for this fixed collection is at most
`L^{C_h(N+1)} (C/P_*)^{r(π)}`". -/
theorem hr_absRankPart_le (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ)
    {v vMinus Mmax cmax μmax : ℝ} {T : ℕ}
    (hq0 : 0 < D.q) (hq1 : D.q < 1) (hρ0 : 0 < D.ρ) (hρ1 : D.ρ < 1) (hv : 1 ≤ v)
    (hvm : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hposS : ∀ g, ∀ p ∈ 𝒢.small g, 0 < p)
    (hdisjS : ∀ g g', g ≠ g' → Disjoint (𝒢.small g) (𝒢.small g'))
    (hlaw : ∀ g, ∑ p ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) p = 1)
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p)
    (h1 : ∀ g, 1 ≤ ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) D.q D.n p)
    (hM : ∀ g, ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax)
    (hμ : ∀ g, ∀ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) D.q D.n p ≤ μmax) (hμ0 : 0 ≤ μmax)
    (hT : 0 < T) (hℓT : ℓ ≤ T) (hC : ∀ ν g, ℓ + ((D.fam ν).C g).card ≤ T)
    (hA : ∀ i, i ≤ D.n → 0 ≤ Graph.sourceGhostA (visitQ D.q D.n i) D.ρ)
    (hbase : ∀ i, i ≤ D.n → Graph.sourceGhostA (visitQ D.q D.n i) D.ρ +
      |Graph.sourceGhostD (visitQ D.q D.n i) D.ρ| / v ≤ 1)
    (hCg : ∀ i, i ≤ D.n → ∀ g,
      |2 * Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g))
        (visitQ D.q D.n i) D.ρ| ≤ cmax)
    {π : Finset (Finset (BirthAddr B J ℓ Bc D.n))}
    (hπ : π ∈ blockCollections (BirthAddr B J ℓ Bc D.n)) :
    absRankPart D Bc θ π ≤
      hrPathConst D v vMinus Mmax cmax T * (max 1 Mmax * μmax) ^ blockRank π := by
  have hM1 : (1 : ℝ) ≤ max 1 Mmax := le_max_left _ _
  have hM0 : (0 : ℝ) ≤ max 1 Mmax := zero_le_one.trans hM1
  have hK : 0 ≤ hrPathConst D v vMinus Mmax cmax T :=
    hrPathConst_nonneg D T hρ0 hρ1 (zero_le_one.trans hv)
  obtain ⟨hcard, hdisj⟩ := mem_blockCollections.mp hπ
  have hne : ∀ b ∈ π, b.Nonempty := fun b hb =>
    Finset.card_pos.mp (lt_of_lt_of_le zero_lt_two (hcard b hb))
  have hblock := hr_block_sum_le (I := BirthAddr B J ℓ Bc D.n) (H := History D Bc)
    (fun h => ‖h.weight θ‖) (fun h => norm_nonneg _) (fun h => h.birth) (bigPrimes 𝒢)
    (fun h a z hz => mem_bigPrimes.mpr ⟨hrAddrGroup a, History.hr_birth_mem h a z hz⟩)
    (fun a => hrAddrMass 𝒢 D.q D.n a)
    (fun a z => hrPtMass_nonneg (hν (hrAddrGroup a)) z) hμ0 hM0 hK
    (fun a z => hrPtMass_le (hμ (hrAddrGroup a)) hμ0 z)
    (fun a => by
      have hsub : 𝒢.big (hrAddrGroup a) ⊆ bigPrimes 𝒢 := fun p hp =>
        mem_bigPrimes.mpr ⟨hrAddrGroup a, hp⟩
      have e : ∑ z ∈ bigPrimes 𝒢, hrAddrMass 𝒢 D.q D.n a z =
          ∑ p ∈ 𝒢.big (hrAddrGroup a), tiltLaw (𝒢.big (hrAddrGroup a)) D.q D.n p :=
        hr_sum_ptMass D.q D.n (hrAddrGroup a) hsub
      rw [e]
      exact (hM (hrAddrGroup a)).trans (le_max_right _ _))
    (fun pv => hr_pinned_le D Bc θ hq0 hq1 hρ0 hρ1 hv hvm hVS hVB hposS hdisjS hlaw hν h1 hM hT
      hℓT hC hA hbase hCg pv)
    π hne hdisj
  exact hblock.trans (mul_le_mul_of_nonneg_left (hr_prod_block_le hμ0 hM1 hπ) hK)

end HrBound

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
