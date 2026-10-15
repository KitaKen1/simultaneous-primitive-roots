module

public import SimultaneousPrimitiveRoots.GaussianPrimePowers
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField Filter Asymptotics
open scoped Topology

noncomputable section
open Classical

/-- The remainder after removing just the degree-one first powers. For
residue degree one, shift the exponent; otherwise retain the entire row. -/
def gaussianHigherPrimePowerTerm (K : Type*) [Field K] [NumberField K]
    (x : ℝ) (p j : ℕ) : ℝ :=
  if rationalPrimeResidueDegree K p = 1 then gaussianPrimePowerTerm K x p (j + 1)
  else gaussianPrimePowerTerm K x p j

def gaussianHigherPrimePowerTrace (K : Type*) [Field K] [NumberField K] (x : ℝ) : ℝ :=
  ∑' p : ℕ, ∑' j : ℕ, gaussianHigherPrimePowerTerm K x p j

/-- Explicit finite constant for every σ>1/2. Using the integer p-series
is intentionally coarser than a prime-power counting asymptotic. -/
def gaussianHigherPrimePowerConstant (σ : ℝ) : ℝ :=
  Real.exp ((Real.log 2) ^ 2 + σ ^ 2 / 4) * (σ - 1 / 2)⁻¹ *
    (1 - (2 : ℝ) ^ (-σ))⁻¹ * (∑' p : ℕ, (p : ℝ) ^ (-σ - 1 / 2))

theorem artinGaussianWeight_natPower_le_fractional {t x : ℝ}
    (ht : 0 < t) (hx : 0 < x) (σ : ℝ) (m : ℕ) :
    artinGaussianWeight (t ^ m / x) ≤
      Real.exp ((Real.log 2) ^ 2 + σ ^ 2 / 4) * x ^ σ * (t ^ (-σ)) ^ m := by
  have hw := artinGaussianWeight_le_rpow (div_pos (pow_pos ht m) hx) σ
  have heq : (t ^ m / x) ^ (-σ) = x ^ σ * (t ^ (-σ)) ^ m := by
    rw [Real.div_rpow (pow_pos ht m).le hx.le, ← Real.rpow_pow_comm ht.le,
      Real.rpow_neg hx.le]
    have hxpow : x ^ σ ≠ 0 := (Real.rpow_pos_of_pos hx σ).ne'
    field_simp
  simpa only [heq, mul_assoc] using hw

theorem gaussianHigher_ratio_lt_one {σ : ℝ} (hσ : 1 / 2 < σ) :
    (2 : ℝ) ^ (-σ) < 1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)

theorem gaussianPrimePowerTerm_le_fractional_majorant (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {σ x : ℝ} (hσ : 1 / 2 < σ) (hx : 0 < x) (p j k : ℕ)
    (hm : p.Prime → j + 2 ≤ (k + 1) * rationalPrimeResidueDegree K p) :
    gaussianPrimePowerTerm K x p k ≤
      ((Module.finrank ℚ K : ℝ) * Real.exp ((Real.log 2) ^ 2 + σ ^ 2 / 4) *
        (σ - 1 / 2)⁻¹ * x ^ σ) * (p : ℝ) ^ (-σ - 1 / 2) * ((2 : ℝ) ^ (-σ)) ^ j := by
  unfold gaussianPrimePowerTerm
  split_ifs with hp
  · let : Fact p.Prime := ⟨hp⟩
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hc : (rationalPrimeIdealCount K p : ℝ) * (rationalPrimeResidueDegree K p : ℝ) ≤
        (Module.finrank ℚ K : ℝ) := by exact_mod_cast rationalPrimeIdealCount_mul_degree_le K
    have hε : 0 < σ - 1 / 2 := by linarith
    have hl : Real.log (p : ℝ) ≤ (σ - 1 / 2)⁻¹ * (p : ℝ) ^ (σ - 1 / 2) := by
      simpa only [div_eq_mul_inv, mul_comm] using Real.log_le_rpow_div hp0.le hε
    let r : ℝ := (p : ℝ) ^ (-σ)
    have hr0 : 0 ≤ r := (Real.rpow_pos_of_pos hp0 _).le
    have hr : r ≤ (2 : ℝ) ^ (-σ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
    have hr1 : r ≤ 1 := hr.trans (gaussianHigher_ratio_lt_one hσ).le
    have hw := artinGaussianWeight_natPower_le_fractional hp0 hx σ
      ((k + 1) * rationalPrimeResidueDegree K p)
    have hpw : r ^ ((k + 1) * rationalPrimeResidueDegree K p) ≤ r ^ (j + 2) :=
      pow_le_pow_of_le_one hr0 hr1 (hm hp)
    have hj : r ^ j ≤ ((2 : ℝ) ^ (-σ)) ^ j := pow_le_pow_left₀ hr0 hr j
    have heq : (p : ℝ) ^ (σ - 1 / 2) * r ^ 2 = (p : ℝ) ^ (-σ - 1 / 2) := by
      dsimp [r]
      rw [← Real.rpow_mul_natCast hp0.le (-σ) 2, ← Real.rpow_add hp0]
      congr 1
      ring
    calc
      _ ≤ (Module.finrank ℚ K : ℝ) * ((σ - 1 / 2)⁻¹ * (p : ℝ) ^ (σ - 1 / 2)) *
          (Real.exp ((Real.log 2) ^ 2 + σ ^ 2 / 4) * x ^ σ * r ^ (j + 2)) := by
        apply mul_le_mul (mul_le_mul hc hl (Real.log_natCast_nonneg _) (Nat.cast_nonneg _))
          (hw.trans (mul_le_mul_of_nonneg_left hpw (by positivity)))
          (artinGaussianWeight_pos _).le (by positivity)
      _ = ((Module.finrank ℚ K : ℝ) * Real.exp ((Real.log 2) ^ 2 + σ ^ 2 / 4) *
          (σ - 1 / 2)⁻¹ * x ^ σ) * (p : ℝ) ^ (-σ - 1 / 2) * r ^ j := by
        rw [pow_add r j 2]
        calc
          _ = ((Module.finrank ℚ K : ℝ) * Real.exp ((Real.log 2) ^ 2 + σ ^ 2 / 4) *
              (σ - 1 / 2)⁻¹ * x ^ σ) * ((p : ℝ) ^ (σ - 1 / 2) * r ^ 2) * r ^ j := by ring
          _ = _ := by rw [heq]
      _ ≤ _ := mul_le_mul_of_nonneg_left hj (by positivity)
  · have hε : 0 ≤ σ - 1 / 2 := by linarith
    positivity

theorem gaussianHigherPrimePowerTerm_nonneg (K : Type*) [Field K] [NumberField K]
    (x : ℝ) (p j : ℕ) : 0 ≤ gaussianHigherPrimePowerTerm K x p j := by
  unfold gaussianHigherPrimePowerTerm
  split_ifs <;> exact gaussianPrimePowerTerm_nonneg K x p _

theorem gaussianHigherPrimePowerTerm_le_majorant (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {σ x : ℝ} (hσ : 1 / 2 < σ) (hx : 0 < x) (p j : ℕ) :
    gaussianHigherPrimePowerTerm K x p j ≤
      ((Module.finrank ℚ K : ℝ) * Real.exp ((Real.log 2) ^ 2 + σ ^ 2 / 4) *
        (σ - 1 / 2)⁻¹ * x ^ σ) * (p : ℝ) ^ (-σ - 1 / 2) * ((2 : ℝ) ^ (-σ)) ^ j := by
  unfold gaussianHigherPrimePowerTerm
  split_ifs with hf
  · apply gaussianPrimePowerTerm_le_fractional_majorant K hσ hx p j (j + 1)
    intro _
    simp only [hf, mul_one]
    omega
  · apply gaussianPrimePowerTerm_le_fractional_majorant K hσ hx p j j
    intro hp
    let : Fact p.Prime := ⟨hp⟩
    have hfpos := rationalPrimeResidueDegree_pos K (p := p)
    have hf2 : 2 ≤ rationalPrimeResidueDegree K p := by omega
    have h := Nat.mul_le_mul_left (j + 1) hf2
    omega

theorem gaussianHigherPrimePowerTerm_summable (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {σ x : ℝ} (hσ : 1 / 2 < σ) (hx : 0 < x) (p : ℕ) :
    Summable (gaussianHigherPrimePowerTerm K x p) := by
  have hr0 : 0 ≤ (2 : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
  apply ((summable_geometric_of_lt_one hr0 (gaussianHigher_ratio_lt_one hσ)).mul_left
    (((Module.finrank ℚ K : ℝ) * Real.exp ((Real.log 2) ^ 2 + σ ^ 2 / 4) *
      (σ - 1 / 2)⁻¹ * x ^ σ) * (p : ℝ) ^ (-σ - 1 / 2))).of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (gaussianHigherPrimePowerTerm_nonneg K x p j)]
  exact gaussianHigherPrimePowerTerm_le_majorant K hσ hx p j

theorem gaussianHigherPrimePower_sum_le (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {σ x : ℝ} (hσ : 1 / 2 < σ) (hx : 0 < x) (p : ℕ) :
    (∑' j : ℕ, gaussianHigherPrimePowerTerm K x p j) ≤
      ((Module.finrank ℚ K : ℝ) * Real.exp ((Real.log 2) ^ 2 + σ ^ 2 / 4) *
        (σ - 1 / 2)⁻¹ * x ^ σ * (1 - (2 : ℝ) ^ (-σ))⁻¹) * (p : ℝ) ^ (-σ - 1 / 2) := by
  have hr0 : 0 ≤ (2 : ℝ) ^ (-σ) := Real.rpow_nonneg (by norm_num) _
  have hg := summable_geometric_of_lt_one hr0 (gaussianHigher_ratio_lt_one hσ)
  have h := (gaussianHigherPrimePowerTerm_summable K hσ hx p).tsum_le_tsum
    (gaussianHigherPrimePowerTerm_le_majorant K hσ hx p)
    (hg.mul_left (((Module.finrank ℚ K : ℝ) * Real.exp ((Real.log 2) ^ 2 + σ ^ 2 / 4) *
      (σ - 1 / 2)⁻¹ * x ^ σ) * (p : ℝ) ^ (-σ - 1 / 2)))
  rw [hg.tsum_mul_left, tsum_geometric_of_lt_one hr0 (gaussianHigher_ratio_lt_one hσ)] at h
  convert h using 1 <;> first | rfl | ring

theorem gaussianHigherPrimePowerTrace_summable (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {σ x : ℝ} (hσ : 1 / 2 < σ) (hx : 0 < x) :
    Summable (fun p : ℕ => ∑' j : ℕ, gaussianHigherPrimePowerTerm K x p j) := by
  have hs : Summable (fun p : ℕ => (p : ℝ) ^ (-σ - 1 / 2)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hε : 0 ≤ σ - 1 / 2 := by linarith
  have hden : 0 ≤ 1 - (2 : ℝ) ^ (-σ) := (sub_pos.mpr (gaussianHigher_ratio_lt_one hσ)).le
  apply (hs.mul_left ((Module.finrank ℚ K : ℝ) * Real.exp ((Real.log 2) ^ 2 + σ ^ 2 / 4) *
    (σ - 1 / 2)⁻¹ * x ^ σ * (1 - (2 : ℝ) ^ (-σ))⁻¹)).of_norm_bounded
  intro p
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun j => gaussianHigherPrimePowerTerm_nonneg K x p j))]
  exact gaussianHigherPrimePower_sum_le K hσ hx p

theorem gaussianHigherPrimePowerConstant_nonneg {σ : ℝ} (hσ : 1 / 2 < σ) :
    0 ≤ gaussianHigherPrimePowerConstant σ := by
  have hε : 0 ≤ σ - 1 / 2 := by linarith
  have hden : 0 ≤ 1 - (2 : ℝ) ^ (-σ) := (sub_pos.mpr (gaussianHigher_ratio_lt_one hσ)).le
  unfold gaussianHigherPrimePowerConstant
  exact mul_nonneg (by positivity)
    (tsum_nonneg (fun p => Real.rpow_nonneg (Nat.cast_nonneg p) _))

theorem gaussianHigherPrimePowerTrace_le (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {σ x : ℝ} (hσ : 1 / 2 < σ) (hx : 0 < x) :
    gaussianHigherPrimePowerTrace K x ≤
      (Module.finrank ℚ K : ℝ) * gaussianHigherPrimePowerConstant σ * x ^ σ := by
  have hs : Summable (fun p : ℕ => (p : ℝ) ^ (-σ - 1 / 2)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have h := (gaussianHigherPrimePowerTrace_summable K hσ hx).tsum_le_tsum
    (gaussianHigherPrimePower_sum_le K hσ hx)
    (hs.mul_left ((Module.finrank ℚ K : ℝ) * Real.exp ((Real.log 2) ^ 2 + σ ^ 2 / 4) *
      (σ - 1 / 2)⁻¹ * x ^ σ * (1 - (2 : ℝ) ^ (-σ))⁻¹))
  rw [hs.tsum_mul_left] at h
  unfold gaussianHigherPrimePowerTrace gaussianHigherPrimePowerConstant
  convert h using 1 <;> first | rfl | ring

theorem gaussianPrimePowerRow_eq_degreeOne_add_higher (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {x : ℝ} (hx : 0 < x) (p : ℕ) :
    (∑' j : ℕ, gaussianPrimePowerTerm K x p j) = gaussianDegreeOnePrimeTerm K x p +
      (∑' j : ℕ, gaussianHigherPrimePowerTerm K x p j) := by
  by_cases hf : rationalPrimeResidueDegree K p = 1
  · have hfirst : gaussianPrimePowerTerm K x p 0 = gaussianDegreeOnePrimeTerm K x p := by
      unfold gaussianPrimePowerTerm gaussianDegreeOnePrimeTerm
      split_ifs with hp
      · let : Fact p.Prime := ⟨hp⟩
        rw [degreeOnePrimeIdealCount_eq_galois K]
        simp only [hf, if_pos, Nat.cast_one, mul_one, zero_add, pow_one]
      · rfl
    have h := (gaussianPrimePowerTerm_summable K hx p).sum_add_tsum_nat_add 1
    simp only [Finset.sum_range_one, hfirst] at h
    simpa only [gaussianHigherPrimePowerTerm, hf, if_pos] using h.symm
  · have hzero : gaussianDegreeOnePrimeTerm K x p = 0 := by
      unfold gaussianDegreeOnePrimeTerm
      split_ifs with hp
      · let : Fact p.Prime := ⟨hp⟩
        rw [degreeOnePrimeIdealCount_eq_galois K, if_neg hf]
        simp only [Nat.cast_zero, zero_mul]
      · rfl
    simp only [hzero, zero_add, gaussianHigherPrimePowerTerm, if_neg hf]

theorem gaussianPrimePowerTrace_eq_degreeOne_add_higher (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {x : ℝ} (hx : 0 < x) :
    gaussianPrimePowerTrace K x = gaussianDegreeOnePrimeTrace K x +
      gaussianHigherPrimePowerTrace K x := by
  unfold gaussianPrimePowerTrace gaussianDegreeOnePrimeTrace gaussianHigherPrimePowerTrace
  simp_rw [gaussianPrimePowerRow_eq_degreeOne_add_higher K hx]
  exact (gaussianDegreeOnePrimeTerm_summable K hx).tsum_add
    (gaussianHigherPrimePowerTrace_summable K (by norm_num : (1 / 2 : ℝ) < 3 / 4) hx)

theorem gaussianPrimePowerTrace_sub_degreeOne_le (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {σ x : ℝ} (hσ : 1 / 2 < σ) (hx : 0 < x) :
    gaussianPrimePowerTrace K x - gaussianDegreeOnePrimeTrace K x ≤
      (Module.finrank ℚ K : ℝ) * gaussianHigherPrimePowerConstant σ * x ^ σ := by
  rw [gaussianPrimePowerTrace_eq_degreeOne_add_higher K hx, add_sub_cancel_left]
  exact gaussianHigherPrimePowerTrace_le K hσ hx

/-- Choose the answer first: σ sits strictly between 1/2 and 1-η. -/
def gaussianHigherExponent (η : ℝ) : ℝ := 3 / 4 - η / 2

def gaussianMovingHigherEnvelope (η x : ℝ) : ℝ :=
  2 * gaussianHigherPrimePowerConstant (gaussianHigherExponent η) * x ^ (η + gaussianHigherExponent η)

theorem gaussianHigherExponent_conditions {η : ℝ} (hη : η < 1 / 2) :
    1 / 2 < gaussianHigherExponent η ∧ η + gaussianHigherExponent η < 1 := by
  unfold gaussianHigherExponent
  constructor <;> linarith

theorem gaussianHigherPrimePowerTrace_le_moving_envelope (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {η x : ℝ} (hη : η < 1 / 2) (hx : 0 < x)
    (hn : (Module.finrank ℚ K : ℝ) ≤ 2 * x ^ η) :
    gaussianHigherPrimePowerTrace K x ≤ gaussianMovingHigherEnvelope η x := by
  have hσ := (gaussianHigherExponent_conditions hη).1
  apply (gaussianHigherPrimePowerTrace_le K hσ hx).trans
  calc
    _ ≤ (2 * x ^ η) * gaussianHigherPrimePowerConstant (gaussianHigherExponent η) *
        x ^ gaussianHigherExponent η := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx.le _)
      exact mul_le_mul_of_nonneg_right hn (gaussianHigherPrimePowerConstant_nonneg hσ)
    _ = _ := by unfold gaussianMovingHigherEnvelope; rw [Real.rpow_add hx]; ring

theorem sublinear_power_isLittleO_id (C : ℝ) {α : ℝ} (hα : α < 1) :
    (fun x : ℝ => C * x ^ α) =o[atTop] (fun x : ℝ => x) := by
  have hC : Tendsto (fun x : ℝ => C * x ^ (-(1 - α))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := C)).mul (tendsto_rpow_neg_atTop (sub_pos.mpr hα))
  have hratio : Tendsto (fun x : ℝ => (C * x ^ α) / x) atTop (𝓝 0) := by
    refine Tendsto.congr' ?_ hC
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [show -(1 - α) = α - 1 by ring, Real.rpow_sub_one hx.ne']
    ring
  apply isLittleO_of_tendsto' ?_ hratio
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact fun hz => (hx.ne' hz).elim

theorem gaussianMovingHigherEnvelope_isLittleO {η : ℝ} (hη : η < 1 / 2) :
    gaussianMovingHigherEnvelope η =o[atTop] (fun x : ℝ => x) :=
  sublinear_power_isLittleO_id _ (gaussianHigherExponent_conditions hη).2

end

end SimultaneousPrimitiveRoots
