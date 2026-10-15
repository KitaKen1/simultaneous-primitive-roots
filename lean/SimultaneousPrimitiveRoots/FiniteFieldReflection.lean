module

public import SimultaneousPrimitiveRoots.FiniteFieldGaussMask

@[expose] public section

namespace SimultaneousPrimitiveRoots

open scoped Classical
noncomputable section
variable {F : Type*} [Field F] [Fintype F]

/-- Inversion of the digit exchanges a character with its inverse in the Gauss sum. -/
theorem finiteGaussSum_inverse_argument (φ : MulChar F ℂ) (ψ : AddChar F ℂ)
    {t : F} (ht : t ≠ 0) :
    (∑ v : F, φ v * ψ (t / v)) = φ t * gaussSum φ⁻¹ ψ := by
  classical
  let u : Fˣ := (isUnit_iff_ne_zero.mpr ht).unit
  calc
    _ = ∑ x : F, φ⁻¹ x * ψ (t * x) := by
      refine Fintype.sum_bijective Inv.inv inv_bijective _ _ ?_
      intro v
      simp only [MulChar.inv_apply', inv_inv, div_eq_mul_inv]
    _ = _ := by
      simpa [gaussSum, AddChar.mulShift_apply, u] using gaussSum_mulShift_eq φ⁻¹ ψ u

/-- The finite-field factor at reflected valuation zero. The metaplectic
Whittaker identity producing this factor is a separate, still open input. -/
def finiteReflectedMask (χ φ : MulChar F ℂ) (ψ : AddChar F ℂ) (t : F) : ℂ :=
  χ t ^ 4 * ∑ v : F, finiteGaussMask φ ψ v * χ v ^ 4 * ψ (t / v)

theorem finiteReflectedMask_eq (χ φ : MulChar F ℂ) (ψ : AddChar F ℂ)
    {t : F} (ht : t ≠ 0) :
    finiteReflectedMask χ φ ψ t =
      χ t ^ 4 * (φ⁻¹ * χ ^ 4) t *
        (gaussSum (φ⁻¹ * χ ^ 4)⁻¹ ψ / gaussSum φ⁻¹ ψ) := by
  have hs : (∑ v : F, finiteGaussMask φ ψ v * χ v ^ 4 * ψ (t / v)) =
      (φ⁻¹ * χ ^ 4) t * gaussSum (φ⁻¹ * χ ^ 4)⁻¹ ψ / gaussSum φ⁻¹ ψ := by
    simp only [finiteGaussMask, div_mul_eq_mul_div, ← Finset.sum_div,
      ← χ.pow_apply' (by decide : 4 ≠ 0), ← MulChar.mul_apply]
    rw [finiteGaussSum_inverse_argument _ _ ht]
  rw [finiteReflectedMask, hs]
  ring

/-- All nonprincipal masks satisfy the valuation-zero size bound. -/
theorem finiteReflectedMask_norm_le (χ : MulChar F ℂ) {φ : MulChar F ℂ}
    (hφ : φ ≠ 1) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {t : F} (ht : t ≠ 0) :
    ‖finiteReflectedMask χ φ ψ t‖ ≤ 1 := by
  rw [finiteReflectedMask_eq χ φ ψ ht, norm_mul, norm_mul, norm_pow,
    finiteMulChar_norm ht, finiteMulChar_norm ht, one_pow, one_mul, one_mul,
    norm_div, finiteGaussSum_norm (inv_ne_one.mpr hφ) hψ]
  exact (div_le_one (Real.sqrt_pos.2 (by exact_mod_cast Fintype.card_pos))).2
    (finiteGaussSum_norm_le_sqrt _ hψ)

/-- Positive reflected valuation makes the additive argument trivial. -/
theorem finiteGaussMask_orthogonality {χ φ : MulChar F ℂ}
    (hne : φ⁻¹ * χ ^ 4 ≠ 1) (ψ : AddChar F ℂ) :
    (∑ v : F, finiteGaussMask φ ψ v * χ v ^ 4) = 0 := by
  simp only [finiteGaussMask, div_mul_eq_mul_div, ← Finset.sum_div,
    ← χ.pow_apply' (by decide : 4 ≠ 0), ← MulChar.mul_apply]
  rw [MulChar.sum_eq_zero_of_ne_one hne, zero_div]

/-- The only surviving positive-valuation mask is the fourth power. -/
theorem finiteGaussMask_positive_eq (χ φ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    (∑ v : F, finiteGaussMask φ ψ v * χ v ^ 4) =
      if φ = χ ^ 4 then (Fintype.card Fˣ : ℂ) / gaussSum φ⁻¹ ψ else 0 := by
  classical
  by_cases h : φ = χ ^ 4
  · rw [if_pos h]
    simp only [finiteGaussMask, div_mul_eq_mul_div, ← Finset.sum_div,
      ← χ.pow_apply' (by decide : 4 ≠ 0), ← MulChar.mul_apply]
    rw [← h, inv_mul_cancel, MulChar.sum_one_eq_card_units]
  · rw [if_neg h]
    apply finiteGaussMask_orthogonality
    intro he
    apply h
    have he' := congrArg (fun x => φ * x) he
    simpa only [← mul_assoc, mul_inv_cancel, one_mul, mul_one] using he'.symm

theorem finiteGaussMask_positive_norm_le (χ : MulChar F ℂ) {φ : MulChar F ℂ}
    (hφ : φ ≠ 1) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖∑ v : F, finiteGaussMask φ ψ v * χ v ^ 4‖ ≤ Real.sqrt (Fintype.card F) := by
  classical
  rw [finiteGaussMask_positive_eq]
  split_ifs
  · rw [norm_div, norm_natCast, finiteGaussSum_norm (inv_ne_one.mpr hφ) hψ]
    apply (div_le_iff₀ (Real.sqrt_pos.2 (by exact_mod_cast Fintype.card_pos))).2
    rw [← pow_two, Real.sq_sqrt (by positivity)]
    exact_mod_cast (show Fintype.card Fˣ ≤ Fintype.card F by
      rw [Fintype.card_units]
      exact Nat.sub_le _ _)
  · simp only [norm_zero]
    exact Real.sqrt_nonneg _

/-- The finite factor after the additive character becomes trivial,
with the spherical coefficient W kept explicit. -/
def finitePositiveReflectedMask (χ φ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (e : ℕ) (W : ℂ) (t : F) : ℂ :=
  W * χ t ^ (4 + 2 * e) * ∑ v : F, finiteGaussMask φ ψ v * χ v ^ 4

theorem finitePositiveReflectedMask_norm_le (χ : MulChar F ℂ) {φ : MulChar F ℂ}
    (hφ : φ ≠ 1) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (e : ℕ) (W : ℂ)
    {t : F} (ht : t ≠ 0) :
    ‖finitePositiveReflectedMask χ φ ψ e W t‖ ≤ Real.sqrt (Fintype.card F) * ‖W‖ := by
  rw [finitePositiveReflectedMask, norm_mul, norm_mul, norm_pow,
    finiteMulChar_norm ht, one_pow, mul_one, mul_comm (Real.sqrt _) ‖W‖]
  exact mul_le_mul_of_nonneg_left (finiteGaussMask_positive_norm_le χ hφ hψ)
    (norm_nonneg W)

omit [Fintype F] in
theorem finiteMulChar_six_pow_injective {χ : MulChar F ℂ} (hχ : orderOf χ = 6)
    {i j : ℕ} (hi : i < 6) (hj : j < 6) (h : χ ^ i = χ ^ j) : i = j := by
  exact pow_injOn_Iio_orderOf (by rwa [hχ]) (by rwa [hχ]) h

theorem finiteGaussMask_six_positive_vanish {χ : MulChar F ℂ} (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) {j : ℕ} (hj : j < 6) (hj4 : j ≠ 4) :
    (∑ v : F, finiteGaussMask (χ ^ j) ψ v * χ v ^ 4) = 0 := by
  rw [finiteGaussMask_positive_eq, if_neg]
  intro h
  exact hj4 (finiteMulChar_six_pow_injective hχ hj (by decide) h)

omit [Fintype F] in
theorem finiteMulChar_cube_inv {χ : MulChar F ℂ} (hχ : orderOf χ = 6) :
    (χ ^ 3)⁻¹ = χ ^ 3 := by
  apply inv_eq_of_mul_eq_one_right
  rw [← pow_add]
  change χ ^ 6 = 1
  rw [← hχ, pow_orderOf_eq_one]

/-- The actual ratio defining the order-six valuation-one phase. -/
def finiteReflectionPhase (χ : MulChar F ℂ) (ψ : AddChar F ℂ) : ℂ :=
  gaussSum (χ ^ 3) ψ / gaussSum χ⁻¹ ψ

theorem finiteReflectionPhase_norm {χ : MulChar F ℂ} (hχ : orderOf χ = 6)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖finiteReflectionPhase χ ψ‖ = 1 := by
  apply finiteGaussSum_ratio_norm
  · exact finiteMulChar_six_pow_ne_one hχ (by decide) (by decide)
  · apply inv_ne_one.mpr
    simpa using finiteMulChar_six_pow_ne_one hχ (j := 1) (by decide) (by decide)
  · exact hψ

omit [Fintype F] in
theorem finiteMulChar_cube_quadratic {χ : MulChar F ℂ} (hχ : orderOf χ = 6) :
    (χ ^ 3).IsQuadratic := by
  apply MulChar.isQuadratic_iff_sq_eq_one.mpr
  rw [← pow_mul]
  change χ ^ 6 = 1
  rw [← hχ, pow_orderOf_eq_one]

/-- The reflected j=1 factor is a unit phase times the original sextic character. -/
theorem finiteReflectedMask_six_one {χ : MulChar F ℂ} (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) {t : F} (ht : t ≠ 0) :
    finiteReflectedMask χ χ ψ t = finiteReflectionPhase χ ψ * χ t := by
  have hrel : χ⁻¹ * χ ^ 4 = χ ^ 3 := by
    rw [show (4 : ℕ) = 1 + 3 from rfl, pow_add, pow_one, ← mul_assoc, inv_mul_cancel,
      one_mul]
  rw [finiteReflectedMask_eq χ χ ψ ht, hrel, finiteMulChar_cube_inv hχ,
    χ.pow_apply' (by decide : 3 ≠ 0), ← pow_add]
  have hseven : χ t ^ (4 + 3) = χ t := by
    rw [show (4 + 3 : ℕ) = 6 + 1 from rfl, pow_add, finiteMulChar_six_value_pow hχ ht,
      one_mul, pow_one]
  rw [hseven, finiteReflectionPhase, mul_comm]

theorem finiteReflectedMask_six_one_norm {χ : MulChar F ℂ} (hχ : orderOf χ = 6)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {t : F} (ht : t ≠ 0) :
    ‖finiteReflectedMask χ χ ψ t‖ = 1 := by
  rw [finiteReflectedMask_six_one hχ ψ ht, norm_mul,
    finiteReflectionPhase_norm hχ hψ, finiteMulChar_norm ht, one_mul]

/-- The fourth-power zero-valuation mask is smaller by sqrt(#F). -/
theorem finiteReflectedMask_six_four_norm {χ : MulChar F ℂ} (hχ : orderOf χ = 6)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {t : F} (ht : t ≠ 0) :
    ‖finiteReflectedMask χ (χ ^ 4) ψ t‖ = (Real.sqrt (Fintype.card F))⁻¹ := by
  have hne : ψ ≠ 1 := by simpa using hψ one_ne_zero
  have hp := finiteMulChar_six_pow_ne_one hχ (j := 4) (by decide) (by decide)
  rw [finiteReflectedMask_eq χ (χ ^ 4) ψ ht, inv_mul_cancel, inv_one,
    MulChar.one_apply (isUnit_iff_ne_zero.mpr ht), mul_one, norm_mul, norm_pow,
    finiteMulChar_norm ht, one_pow, one_mul, norm_div, gaussSum_one_left hne,
    norm_neg, norm_one, finiteGaussSum_norm (inv_ne_one.mpr hp) hψ, one_div]

theorem finiteGaussMask_six_one_positive {χ : MulChar F ℂ} (hχ : orderOf χ = 6)
    (ψ : AddChar F ℂ) : (∑ v : F, finiteGaussMask χ ψ v * χ v ^ 4) = 0 := by
  apply finiteGaussMask_orthogonality
  rw [show χ⁻¹ * χ ^ 4 = χ ^ 3 by
    rw [show (4 : ℕ) = 1 + 3 from rfl, pow_add, pow_one, ← mul_assoc, inv_mul_cancel,
      one_mul]]
  exact finiteMulChar_six_pow_ne_one hχ (by decide) (by decide)

end
end SimultaneousPrimitiveRoots
