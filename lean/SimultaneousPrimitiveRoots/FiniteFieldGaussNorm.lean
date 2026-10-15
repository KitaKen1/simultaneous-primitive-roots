module

public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

namespace SimultaneousPrimitiveRoots

noncomputable section
variable {F : Type*} [Field F] [Fintype F]

/-- Nonzero values of an actual finite-field character have modulus one. -/
theorem finiteMulChar_norm {χ : MulChar F ℂ} {t : F} (ht : t ≠ 0) :
    ‖χ t‖ = 1 := by
  classical
  let u : Fˣ := (isUnit_iff_ne_zero.mpr ht).unit
  have h := Complex.norm_eq_one_of_mem_rootsOfUnity (χ.apply_mem_rootsOfUnity u)
  simpa [u, MulChar.coe_equivToUnitHom] using h

/-- The square of the modulus of a nonprincipal Gauss sum is the field size. -/
theorem finiteGaussSum_norm_sq {χ : MulChar F ℂ} (hχ : χ ≠ 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by
  have h := gaussSum_mul_gaussSum_eq_card hχ hψ
  rw [← star_gaussSum_eq, RCLike.star_def, Complex.mul_conj'] at h
  exact_mod_cast h

theorem finiteGaussSum_norm {χ : MulChar F ℂ} (hχ : χ ≠ 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ = Real.sqrt (Fintype.card F) := by
  rw [← finiteGaussSum_norm_sq hχ hψ, Real.sqrt_sq (norm_nonneg _)]

theorem finiteGaussSum_ne_zero {χ : MulChar F ℂ} (hχ : χ ≠ 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) : gaussSum χ ψ ≠ 0 := by
  exact gaussSum_ne_zero_of_nontrivial (by exact_mod_cast (Fintype.card_pos.ne')) hχ hψ

/-- The principal Gauss sum has size one, hence every Gauss sum is at
most sqrt(#F) for a primitive additive character. -/
theorem finiteGaussSum_norm_le_sqrt (χ : MulChar F ℂ)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ≤ Real.sqrt (Fintype.card F) := by
  rcases eq_or_ne χ 1 with rfl | hχ
  · have hne : ψ ≠ 1 := by simpa using hψ one_ne_zero
    rw [gaussSum_one_left hne, norm_neg, norm_one]
    have hc : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
    simpa using Real.sqrt_le_sqrt hc
  · exact (finiteGaussSum_norm hχ hψ).le

/-- Equal field sizes make a ratio of two nonprincipal Gauss sums a unit phase. -/
theorem finiteGaussSum_ratio_norm {χ φ : MulChar F ℂ} (hχ : χ ≠ 1) (hφ : φ ≠ 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ / gaussSum φ ψ‖ = 1 := by
  rw [norm_div, finiteGaussSum_norm hχ hψ, finiteGaussSum_norm hφ hψ,
    div_self (Real.sqrt_pos.2 (by exact_mod_cast Fintype.card_pos)).ne']

/-- Characters of order six exist whenever the field size is one modulo six. -/
theorem exists_finiteMulChar_order_six (h : 6 ∣ Fintype.card F - 1) :
    ∃ χ : MulChar F ℂ, orderOf χ = 6 := by
  exact MulChar.exists_mulChar_orderOf F h (Complex.isPrimitiveRoot_exp 6 (by decide))

omit [Fintype F] in
theorem finiteMulChar_six_pow_ne_one {χ : MulChar F ℂ} (hχ : orderOf χ = 6)
    {j : ℕ} (hj : 0 < j) (hj6 : j < 6) : χ ^ j ≠ 1 := by
  intro h
  have hd := orderOf_dvd_of_pow_eq_one h
  rw [hχ] at hd
  exact (Nat.le_of_dvd hj hd).not_gt hj6

omit [Fintype F] in
theorem finiteMulChar_six_value_pow {χ : MulChar F ℂ} (hχ : orderOf χ = 6)
    {t : F} (ht : t ≠ 0) : χ t ^ 6 = 1 := by
  rw [← χ.pow_apply' (by decide : 6 ≠ 0), ← hχ, pow_orderOf_eq_one,
    MulChar.one_apply (isUnit_iff_ne_zero.mpr ht)]

end
end SimultaneousPrimitiveRoots
