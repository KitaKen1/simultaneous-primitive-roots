module

public import SimultaneousPrimitiveRoots.MultiplicativeMellinConvolution
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
open scoped Topology
noncomputable section

def artinGammaDensity (a : ℝ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (a : ℂ) * (Real.exp (-t) : ℂ)

theorem artinGammaDensity_mellin_convergent (a : ℝ) {s : ℂ}
    (hs : -a < s.re) : MellinConvergent (artinGammaDensity a) s := by
  change MellinConvergent (fun t : ℝ => (t : ℂ) ^ (a : ℂ) •
    (Real.exp (-t) : ℂ)) s
  rw [MellinConvergent.cpow_smul]
  have hp : 0 < (s + (a : ℂ)).re := by simp only [add_re, ofReal_re]; linarith
  simpa only [MellinConvergent, smul_eq_mul, mul_comm] using
    Complex.GammaIntegral_convergent hp

theorem artinGammaDensity_mellin (a : ℝ) {s : ℂ} (hs : -a < s.re) :
    mellin (artinGammaDensity a) s = Complex.Gamma (s + a) := by
  change mellin (fun t : ℝ => (t : ℂ) ^ (a : ℂ) • (Real.exp (-t) : ℂ)) s = _
  rw [mellin_cpow_smul, ← Complex.GammaIntegral_eq_mellin,
    ← Complex.Gamma_eq_integral]
  simp only [add_re, ofReal_re]
  linarith

theorem artinGammaDensity_eq_ofReal (a : ℝ) {t : ℝ} (ht : 0 < t) :
    artinGammaDensity a t = (t ^ a * Real.exp (-t) : ℝ) := by
  rw [artinGammaDensity, ← Complex.ofReal_cpow ht.le, Complex.ofReal_mul]

theorem artinGammaDensity_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (artinGammaDensity a) artinPositiveMultiplicativeMeasure := by
  have h := (artinMellin_convergent_iff_multiplicative _ 0).mp
    (artinGammaDensity_mellin_convergent a (s := 0) (by simpa using ha))
  simpa only [Complex.cpow_zero, one_mul] using h

def artinGammaPairIntegrand (a b u t : ℝ) : ℂ :=
  (t ^ (a - b) * Real.exp (-(t + u / t)) : ℝ)

theorem artinGammaPair_integrand_eq (a b : ℝ) {u t : ℝ} (hu : 0 < u) (ht : 0 < t) :
    artinGammaDensity a t * artinGammaDensity b (u / t) =
      (u ^ b : ℝ) * artinGammaPairIntegrand a b u t := by
  rw [artinGammaDensity_eq_ofReal a ht,
    artinGammaDensity_eq_ofReal b (div_pos hu ht)]
  unfold artinGammaPairIntegrand
  norm_cast
  rw [Real.div_rpow hu.le ht.le, Real.rpow_sub ht, neg_add, Real.exp_add]
  ring

theorem artinGammaPairIntegrand_integrable {a b : ℝ} (hab : 0 < a - b)
    {u : ℝ} (hu : 0 < u) :
    Integrable (artinGammaPairIntegrand a b u) artinPositiveMultiplicativeMeasure := by
  apply (artinGammaDensity_integrable hab).norm.mono' (by
    unfold artinGammaPairIntegrand
    fun_prop)
  filter_upwards [artinPositiveMultiplicative_ae_pos] with t ht
  rw [artinGammaPairIntegrand, artinGammaDensity_eq_ofReal _ ht,
    Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg ht.le _)
  apply Real.exp_le_exp.mpr
  linarith [div_pos hu ht]

theorem artinGammaPair_convolution_integrand_integrable {a b : ℝ} (hab : 0 < a - b)
    {u : ℝ} (hu : 0 < u) :
    Integrable (fun t => artinGammaDensity a t * artinGammaDensity b (u / t))
      artinPositiveMultiplicativeMeasure := by
  apply ((artinGammaPairIntegrand_integrable hab hu).const_mul ((u ^ b : ℝ) : ℂ)).congr
  filter_upwards [artinPositiveMultiplicative_ae_pos] with t ht
  exact (artinGammaPair_integrand_eq a b hu ht).symm

/-- The actual multiplicative convolution of the two Euler gamma densities. -/
def artinGammaPairProfile (a b : ℝ) : ℝ → ℂ :=
  artinMultiplicativeConvolution (artinGammaDensity a) (artinGammaDensity b)

theorem artinGammaPairProfile_integral (a b : ℝ) {u : ℝ} (hu : 0 < u) :
    artinGammaPairProfile a b u =
      (u ^ b : ℝ) * ∫ t, artinGammaPairIntegrand a b u t
        ∂artinPositiveMultiplicativeMeasure := by
  rw [artinGammaPairProfile, artinMultiplicativeConvolution, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [artinPositiveMultiplicative_ae_pos] with t ht
  exact artinGammaPair_integrand_eq a b hu ht

theorem artinGammaPairProfile_mellin_convergent (a b : ℝ) {s : ℂ}
    (ha : -a < s.re) (hb : -b < s.re) :
    MellinConvergent (artinGammaPairProfile a b) s :=
  artinMultiplicativeConvolution_mellin_convergent
    (artinGammaDensity_mellin_convergent a ha) (artinGammaDensity_mellin_convergent b hb)

theorem artinGammaPairProfile_mellin (a b : ℝ) {s : ℂ}
    (ha : -a < s.re) (hb : -b < s.re) :
    mellin (artinGammaPairProfile a b) s =
      Complex.Gamma (s + a) * Complex.Gamma (s + b) := by
  rw [artinGammaPairProfile, artinMultiplicativeConvolution_mellin
    (artinGammaDensity_mellin_convergent a ha) (artinGammaDensity_mellin_convergent b hb),
    artinGammaDensity_mellin a ha, artinGammaDensity_mellin b hb]

def artinLocalGammaProfile : ℝ → ℂ := artinGammaPairProfile (7 / 6) (5 / 6)

theorem artinLocalGammaProfile_mellin_convergent {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    MellinConvergent artinLocalGammaProfile s := by
  exact artinGammaPairProfile_mellin_convergent _ _ (by linarith) hs

theorem artinLocalGammaProfile_mellin {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    mellin artinLocalGammaProfile s =
      Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6) := by
  rw [artinLocalGammaProfile, artinGammaPairProfile_mellin _ _ (by linarith) hs]
  push_cast
  ring

end
end SimultaneousPrimitiveRoots
