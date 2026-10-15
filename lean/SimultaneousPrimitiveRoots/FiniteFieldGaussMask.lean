module

public import SimultaneousPrimitiveRoots.FiniteFieldGaussNorm

@[expose] public section

namespace SimultaneousPrimitiveRoots

noncomputable section
variable {F : Type*} [Field F] [Fintype F]

/-- The nonprincipal reflection mask, extended by zero at zero. -/
def finiteGaussMask (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (v : F) : ℂ :=
  χ⁻¹ v / gaussSum χ⁻¹ ψ

theorem finiteGaussMask_zero (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    finiteGaussMask χ ψ 0 = 0 := by
  simp [finiteGaussMask, MulChar.map_zero]

/-- This Fourier identity includes the nonunit argument t=0. -/
theorem finiteGaussMask_fourier {χ : MulChar F ℂ} (hχ : χ ≠ 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (t : F) :
    ∑ v : F, finiteGaussMask χ ψ v * ψ (t * v) = χ t := by
  classical
  have hden := finiteGaussSum_ne_zero (inv_ne_one.mpr hχ) hψ
  simp only [finiteGaussMask, div_mul_eq_mul_div, ← Finset.sum_div]
  rcases eq_or_ne t 0 with rfl | ht
  · simp [MulChar.map_zero, MulChar.sum_eq_zero_of_ne_one (inv_ne_one.mpr hχ)]
  · let u : Fˣ := (isUnit_iff_ne_zero.mpr ht).unit
    have hs : (∑ v : F, χ⁻¹ v * ψ (t * v)) = χ t * gaussSum χ⁻¹ ψ := by
      simpa [gaussSum, AddChar.mulShift_apply, u] using gaussSum_mulShift_eq χ⁻¹ ψ u
    rw [hs, mul_div_cancel_right₀ _ hden]

theorem finiteGaussMask_norm {χ : MulChar F ℂ} (hχ : χ ≠ 1)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) {v : F} (hv : v ≠ 0) :
    ‖finiteGaussMask χ ψ v‖ = (Real.sqrt (Fintype.card F))⁻¹ := by
  rw [finiteGaussMask, norm_div, finiteMulChar_norm hv,
    finiteGaussSum_norm (inv_ne_one.mpr hχ) hψ, one_div]

/-- The principal mask is the zero digit minus the constant 1/#F. -/
def finitePrincipalMask (v : F) : ℂ := by
  classical
  exact (if v = 0 then 1 else 0) - (Fintype.card F : ℂ)⁻¹

theorem finitePrincipalMask_zero :
    finitePrincipalMask (0 : F) = 1 - (Fintype.card F : ℂ)⁻¹ := by
  simp [finitePrincipalMask]

theorem finitePrincipalMask_nonzero {v : F} (hv : v ≠ 0) :
    finitePrincipalMask v = -(Fintype.card F : ℂ)⁻¹ := by
  simp [finitePrincipalMask, hv]

/-- At exponent zero the Fourier output is the unit indicator,
not the pointwise zeroth power at zero. -/
theorem finitePrincipalMask_fourier {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (t : F) :
    ∑ v : F, finitePrincipalMask v * ψ (t * v) = (1 : MulChar F ℂ) t := by
  classical
  have hcard : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
  have hs : (∑ v : F, ψ (t * v)) =
      if t = 0 then (Fintype.card F : ℂ) else 0 := by
    simpa [mul_comm] using AddChar.sum_mulShift t hψ
  simp only [finitePrincipalMask, sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hdelta : (∑ v : F, (if v = 0 then (1 : ℂ) else 0) * ψ (t * v)) = 1 := by
    simp [ite_mul]
  rw [hdelta, hs]
  rcases eq_or_ne t 0 with rfl | ht
  · simp [hcard, MulChar.map_zero]
  · simp [ht, MulChar.one_apply (isUnit_iff_ne_zero.mpr ht)]

end
end SimultaneousPrimitiveRoots
