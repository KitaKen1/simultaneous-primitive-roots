module

public import SimultaneousPrimitiveRoots.MultiplicativeMellinConvolution
public import Mathlib.MeasureTheory.Group.Prod

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
open scoped Topology
noncomputable section

/-- Norm-sheet coordinates: the log norm is w=x+y and the free coordinate is x. -/
def artinLogNormSheetEquiv : (ℝ × ℝ) ≃ᵐ (ℝ × ℝ) where
  toFun p := (p.2, p.1 - p.2)
  invFun p := (p.1 + p.2, p.1)
  left_inv p := by ext <;> simp
  right_inv p := by ext <;> simp
  measurable_toFun := by
    change Measurable (fun p : ℝ × ℝ => (p.2, p.1 - p.2))
    fun_prop
  measurable_invFun := by
    change Measurable (fun p : ℝ × ℝ => (p.1 + p.2, p.1))
    fun_prop

theorem artinLogNormSheet_measurePreserving :
    MeasurePreserving artinLogNormSheetEquiv (volume.prod volume) (volume.prod volume) :=
  measurePreserving_prod_sub_swap volume volume

/-- The actual integral on the affine sheet x+y=w with the transported Haar measure. -/
def artinLogNormSheetProfile (f : ℝ × ℝ → ℂ) (w : ℝ) : ℂ :=
  ∫ v : ℝ, f (v, w - v)

theorem artinLogNormSheet_joint_integrable {f : ℝ × ℝ → ℂ}
    (hf : Integrable f (volume.prod volume)) :
    Integrable (fun p : ℝ × ℝ => f (p.2, p.1 - p.2)) (volume.prod volume) :=
  artinLogNormSheet_measurePreserving.integrable_comp_of_integrable hf

theorem artinLogNormSheetProfile_integrable {f : ℝ × ℝ → ℂ}
    (hf : Integrable f (volume.prod volume)) : Integrable (artinLogNormSheetProfile f) :=
  (artinLogNormSheet_joint_integrable hf).integral_prod_left

/-- Actual disintegration, including the Fubini integrability hypothesis. -/
theorem artinLogNormSheet_disintegration {f : ℝ × ℝ → ℂ}
    (hf : Integrable f (volume.prod volume)) :
    (∫ w, artinLogNormSheetProfile f w) = ∫ p, f p ∂(volume.prod volume) := by
  unfold artinLogNormSheetProfile
  rw [← integral_prod _ (artinLogNormSheet_joint_integrable hf)]
  exact artinLogNormSheet_measurePreserving.integral_comp' f

theorem artinLogNormSheet_weighted_profile (f : ℝ × ℝ → ℂ) (s : ℂ) (w : ℝ) :
    artinLogNormSheetProfile
      (fun p => Complex.exp (s * ((p.1 + p.2 : ℝ) : ℂ)) * f p) w =
      Complex.exp (s * w) * artinLogNormSheetProfile f w := by
  simp only [artinLogNormSheetProfile, add_sub_cancel, ← integral_const_mul]

theorem artinLogNormSheet_weighted_integrable {f : ℝ × ℝ → ℂ} {s : ℂ}
    (hf : Integrable (fun p => Complex.exp (s * ((p.1 + p.2 : ℝ) : ℂ)) * f p)
      (volume.prod volume)) :
    Integrable (fun w : ℝ => Complex.exp (s * w) * artinLogNormSheetProfile f w) := by
  have he := funext (artinLogNormSheet_weighted_profile f s)
  rw [← he]
  exact artinLogNormSheetProfile_integrable hf

theorem artinLogNormSheet_weighted_disintegration {f : ℝ × ℝ → ℂ} {s : ℂ}
    (hf : Integrable (fun p => Complex.exp (s * ((p.1 + p.2 : ℝ) : ℂ)) * f p)
      (volume.prod volume)) :
    (∫ w : ℝ, Complex.exp (s * w) * artinLogNormSheetProfile f w) =
      ∫ p, Complex.exp (s * ((p.1 + p.2 : ℝ) : ℂ)) * f p ∂(volume.prod volume) := by
  have he := funext (artinLogNormSheet_weighted_profile f s)
  rw [← he]
  exact artinLogNormSheet_disintegration hf

def artinPositiveNormSheetProfile (f : ℝ × ℝ → ℂ) (u : ℝ) : ℂ :=
  artinLogNormSheetProfile f (Real.log u)

theorem artinMellin_positive_exp_power (s : ℂ) (w : ℝ) :
    (Real.exp w : ℂ) ^ s = Complex.exp (s * w) := by
  simpa only [neg_neg, Complex.ofReal_neg, mul_neg, neg_mul, neg_neg]
    using artinMellin_exp_power s (-w)

theorem artinPositiveNormSheetProfile_mellin_convergent {f : ℝ × ℝ → ℂ} {s : ℂ}
    (hf : Integrable (fun p => Complex.exp (s * ((p.1 + p.2 : ℝ) : ℂ)) * f p)
      (volume.prod volume)) : MellinConvergent (artinPositiveNormSheetProfile f) s := by
  rw [artinMellin_convergent_iff_multiplicative,
    artinPositiveMultiplicative_integrable_exp_iff]
  simpa only [artinPositiveNormSheetProfile, Real.log_exp, artinMellin_positive_exp_power]
    using artinLogNormSheet_weighted_integrable hf

theorem artinPositiveNormSheetProfile_mellin {f : ℝ × ℝ → ℂ} {s : ℂ}
    (hf : Integrable (fun p => Complex.exp (s * ((p.1 + p.2 : ℝ) : ℂ)) * f p)
      (volume.prod volume)) :
    mellin (artinPositiveNormSheetProfile f) s =
      ∫ p, Complex.exp (s * ((p.1 + p.2 : ℝ) : ℂ)) * f p ∂(volume.prod volume) := by
  rw [artinMellin_eq_multiplicative, artinPositiveMultiplicative_integral_exp]
  simp only [artinPositiveNormSheetProfile, Real.log_exp, artinMellin_positive_exp_power]
  exact artinLogNormSheet_weighted_disintegration hf

/-- For product radial factors the sheet integral is the actual dt/t convolution,
at every positive u. No Mellin uniqueness assertion is used here. -/
theorem artinPositiveNormSheetProfile_product (f g : ℝ → ℂ) {u : ℝ} (hu : 0 < u) :
    artinPositiveNormSheetProfile (fun p => f (Real.exp p.1) * g (Real.exp p.2)) u =
      artinMultiplicativeConvolution f g u := by
  rw [artinPositiveNormSheetProfile, artinLogNormSheetProfile,
    artinMultiplicativeConvolution, artinPositiveMultiplicative_integral_exp]
  apply integral_congr_ae
  apply ae_of_all
  intro v
  change f (Real.exp v) * g (Real.exp (Real.log u - v)) =
    f (Real.exp v) * g (u / Real.exp v)
  rw [Real.exp_sub, Real.exp_log hu]

end
end SimultaneousPrimitiveRoots
