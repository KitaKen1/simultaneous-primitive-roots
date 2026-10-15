module

public import SimultaneousPrimitiveRoots.FiniteFieldReflection
public import Mathlib.NumberTheory.LegendreSymbol.Complex

@[expose] public section

namespace SimultaneousPrimitiveRoots

noncomputable section
variable {F : Type*} [Field F] [Fintype F]

/-- The local characters required by the finite mask formulas exist over
every finite field whose cardinality is one modulo six. -/
theorem exists_finiteReflection_characters (h : 6 ∣ Fintype.card F - 1) :
    ∃ (χ : MulChar F ℂ) (ψ : AddChar F ℂ), orderOf χ = 6 ∧ ψ.IsPrimitive := by
  obtain ⟨χ, hχ⟩ := exists_finiteMulChar_order_six h
  exact ⟨χ, AddChar.FiniteField.primitiveChar_to_Complex F, hχ,
    AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive F⟩

/-- The zero digit contributes nothing to this fourth-power finite sum. -/
theorem finitePrincipalMask_weighted_sum (χ : MulChar F ℂ) (g : F → ℂ) :
    (∑ v : F, finitePrincipalMask v * χ v ^ 4 * g v) =
      -(Fintype.card F : ℂ)⁻¹ * ∑ v : F, (χ ^ 4) v * g v := by
  classical
  have hv (v : F) : finitePrincipalMask v * χ v ^ 4 * g v =
      -(Fintype.card F : ℂ)⁻¹ * ((χ ^ 4) v * g v) := by
    rcases eq_or_ne v 0 with rfl | hv
    · simp [MulChar.map_zero]
    · rw [finitePrincipalMask_nonzero hv, χ.pow_apply' (by decide : 4 ≠ 0)]
      ring
  simp_rw [hv]
  rw [Finset.mul_sum]

def finitePrincipalReflectedMask (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (t : F) : ℂ :=
  χ t ^ 4 * ∑ v : F, finitePrincipalMask v * χ v ^ 4 * ψ (t / v)

theorem finitePrincipalReflectedMask_eq (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    {t : F} (ht : t ≠ 0) :
    finitePrincipalReflectedMask χ ψ t =
      (-gaussSum (χ ^ 4)⁻¹ ψ / (Fintype.card F : ℂ)) * χ t ^ 8 := by
  rw [finitePrincipalReflectedMask, finitePrincipalMask_weighted_sum,
    finiteGaussSum_inverse_argument _ _ ht, χ.pow_apply' (by decide : 4 ≠ 0)]
  ring

theorem finitePrincipalReflectedMask_six_norm {χ : MulChar F ℂ}
    (hχ : orderOf χ = 6) {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    {t : F} (ht : t ≠ 0) :
    ‖finitePrincipalReflectedMask χ ψ t‖ = (Real.sqrt (Fintype.card F))⁻¹ := by
  have hp := finiteMulChar_six_pow_ne_one hχ (j := 4) (by decide) (by decide)
  rw [finitePrincipalReflectedMask_eq χ ψ ht, norm_mul, norm_pow,
    finiteMulChar_norm ht, one_pow, mul_one, norm_div, norm_neg, norm_natCast,
    finiteGaussSum_norm (inv_ne_one.mpr hp) hψ]
  have hcard : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  apply eq_inv_of_mul_eq_one_left
  rw [div_mul_eq_mul_div, ← pow_two, Real.sq_sqrt (by positivity), div_self hcard]

theorem finitePrincipalMask_six_positive {χ : MulChar F ℂ} (hχ : orderOf χ = 6) :
    (∑ v : F, finitePrincipalMask v * χ v ^ 4) = 0 := by
  have h := finitePrincipalMask_weighted_sum χ (fun _ => 1)
  simpa [MulChar.sum_eq_zero_of_ne_one
    (finiteMulChar_six_pow_ne_one hχ (j := 4) (by decide) (by decide))] using h

end
end SimultaneousPrimitiveRoots
