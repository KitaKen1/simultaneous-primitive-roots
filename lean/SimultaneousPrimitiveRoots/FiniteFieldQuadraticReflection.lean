module

public import SimultaneousPrimitiveRoots.FiniteFieldReflection
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

@[expose] public section

namespace SimultaneousPrimitiveRoots

open scoped Classical
noncomputable section
variable {F : Type*} [Field F] [Fintype F]

/-- A cyclic finite field has only one nonprincipal complex quadratic character. -/
theorem finiteMulChar_quadratic_unique {χ φ : MulChar F ℂ}
    (hχ : χ.IsQuadratic) (hφ : φ.IsQuadratic) (hχ1 : χ ≠ 1) (hφ1 : φ ≠ 1) :
    χ = φ := by
  classical
  let _ := Fintype.ofFinite Fˣ
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hneg (ρ : MulChar F ℂ) (hρ : ρ.IsQuadratic) (hρ1 : ρ ≠ 1) :
      ρ (g : F) = -1 := by
    rcases hρ (g : F) with h0 | h1 | hm
    · have hn := finiteMulChar_norm (χ := ρ) g.ne_zero
      rw [h0, norm_zero] at hn
      norm_num at hn
    · exact (hρ1 ((MulChar.eq_iff hg ρ 1).mpr (by simpa using h1))).elim
    · exact hm
  exact (MulChar.eq_iff hg χ φ).mpr ((hneg χ hχ hχ1).trans (hneg φ hφ hφ1).symm)

/-- The order-six hypothesis itself rules out characteristic two. -/
theorem finiteMulChar_six_char_ne_two {χ : MulChar F ℂ} (hχ : orderOf χ = 6) :
    ringChar F ≠ 2 := by
  intro hF
  apply finiteMulChar_six_pow_ne_one hχ (j := 3) (by decide) (by decide)
  apply MulChar.eq_one_iff.mpr
  intro u
  obtain ⟨v, hv⟩ := FiniteField.isSquare_of_char_two hF (u : F)
  have hv0 : v ≠ 0 := by
    intro h0
    simp only [h0, zero_mul] at hv
    exact u.ne_zero hv
  rw [hv, map_mul]
  have hs := congrArg (fun ρ : MulChar F ℂ => ρ v)
    (finiteMulChar_cube_quadratic hχ).sq_eq_one
  simpa only [pow_two, MulChar.mul_apply,
    MulChar.one_apply (isUnit_iff_ne_zero.mpr hv0)] using hs

/-- The cube is the actual finite-field quadratic character, including at zero. -/
theorem finiteMulChar_six_cube_eq_quadraticChar {χ : MulChar F ℂ}
    (hχ : orderOf χ = 6) :
    χ ^ 3 = (quadraticChar F).ringHomComp (Int.castRingHom ℂ) := by
  classical
  apply finiteMulChar_quadratic_unique
  · exact finiteMulChar_cube_quadratic hχ
  · exact (quadraticChar_isQuadratic F).comp _
  · exact finiteMulChar_six_pow_ne_one hχ (by decide) (by decide)
  · apply (MulChar.ringHomComp_ne_one_iff Int.cast_injective).mpr
    exact quadraticChar_ne_one (finiteMulChar_six_char_ne_two hχ)

theorem finiteMulChar_six_cube_value {χ : MulChar F ℂ} (hχ : orderOf χ = 6) (t : F) :
    χ t ^ 3 = (quadraticChar F t : ℂ) := by
  have h := congrArg (fun ρ : MulChar F ℂ => ρ t)
    (finiteMulChar_six_cube_eq_quadraticChar hχ)
  simpa only [χ.pow_apply' (by decide : 3 ≠ 0), MulChar.ringHomComp_apply,
    Int.coe_castRingHom] using h

/-- Multiplying the j=1 factor by the inverse fourth-power row produces
the quadratic character. Global reciprocity producing that row is still separate. -/
theorem finiteReflectedMask_six_quadratic_row {χ : MulChar F ℂ}
    (hχ : orderOf χ = 6) (ψ : AddChar F ℂ) {t : F} (ht : t ≠ 0) :
    finiteReflectedMask χ χ ψ t * (χ t ^ 4)⁻¹ =
      finiteReflectionPhase χ ψ * (quadraticChar F t : ℂ) := by
  rw [finiteReflectedMask_six_one hχ ψ ht]
  have hn : χ t ≠ 0 := by
    intro h0
    have hnorm := finiteMulChar_norm (χ := χ) ht
    simp [h0] at hnorm
  have h6 := finiteMulChar_six_value_pow hχ ht
  have hrow : χ t * (χ t ^ 4)⁻¹ = χ t ^ 3 := by
    apply (mul_right_cancel₀ (pow_ne_zero 4 hn))
    rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero 4 hn), mul_one, ← pow_add]
    rw [show (3 + 4 : ℕ) = 6 + 1 from rfl, pow_add, h6, one_mul, pow_one]
  rw [mul_assoc, hrow, finiteMulChar_six_cube_value hχ]

end
end SimultaneousPrimitiveRoots
