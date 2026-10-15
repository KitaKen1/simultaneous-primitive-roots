module

public import SimultaneousPrimitiveRoots.GammaPairProfile

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
open scoped Topology
noncomputable section

/-- The usual positive-axis integral representation of the modified Bessel K.
Its agreement with the paper's Whittaker/Haar profile is a separate task. -/
def artinBesselKIntegrand (ν x t : ℝ) : ℂ :=
  (t ^ ν * Real.exp (-(x / 2) * (t + t⁻¹)) : ℝ)

def artinBesselKIntegral (ν x : ℝ) : ℂ :=
  (1 / 2) * ∫ t, artinBesselKIntegrand ν x t ∂artinPositiveMultiplicativeMeasure

theorem artinBesselK_scaled_integrand (a b : ℝ) {x t : ℝ}
    (hx : 0 < x) (ht : 0 < t) :
    artinGammaPairIntegrand a b ((x / 2) ^ 2) ((x / 2) * t) =
      ((x / 2) ^ (a - b) : ℝ) * artinBesselKIntegrand (a - b) x t := by
  have ha : 0 < x / 2 := by positivity
  have heq : (x / 2) * t + (x / 2) ^ 2 / ((x / 2) * t) =
      (x / 2) * (t + t⁻¹) := by
    field_simp
  unfold artinGammaPairIntegrand artinBesselKIntegrand
  rw [Real.mul_rpow ha.le ht.le, heq]
  simp only [neg_mul, Complex.ofReal_mul, mul_assoc]

theorem artinBesselKIntegrand_integrable {ν x : ℝ} (hν : 0 < ν) (hx : 0 < x) :
    Integrable (artinBesselKIntegrand ν x) artinPositiveMultiplicativeMeasure := by
  have ha : 0 < x / 2 := by positivity
  have hc : (((x / 2) ^ ν : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.rpow_pos_of_pos ha _))
  have hg := (artinMultiplicative_integrable_comp_mul_iff
    (artinGammaPairIntegrand ν 0 ((x / 2) ^ 2)) ha).mpr
      (artinGammaPairIntegrand_integrable (by simpa using hν) (by positivity))
  have he : Integrable (fun t => ((x / 2) ^ ν : ℝ) * artinBesselKIntegrand ν x t)
      artinPositiveMultiplicativeMeasure := by
    apply hg.congr
    filter_upwards [artinPositiveMultiplicative_ae_pos] with t ht
    simpa only [sub_zero] using artinBesselK_scaled_integrand ν 0 hx ht
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc) _).mp he

/-- Scaling the actual convergent integral identifies the gamma convolution
with the Bessel integral, including its exact factor 2. -/
theorem artinGammaPairProfile_bessel_integral (a b : ℝ) {x : ℝ} (hx : 0 < x) :
    artinGammaPairProfile a b ((x / 2) ^ 2) =
      (2 * (x / 2) ^ (a + b) : ℝ) * artinBesselKIntegral (a - b) x := by
  have ha : 0 < x / 2 := by positivity
  rw [artinGammaPairProfile_integral a b (by positivity),
    ← artinMultiplicative_integral_comp_mul (artinGammaPairIntegrand a b ((x / 2) ^ 2)) ha]
  have hid : (∫ t, artinGammaPairIntegrand a b ((x / 2) ^ 2) ((x / 2) * t)
      ∂artinPositiveMultiplicativeMeasure) =
      ((x / 2) ^ (a - b) : ℝ) * ∫ t, artinBesselKIntegrand (a - b) x t
        ∂artinPositiveMultiplicativeMeasure := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [artinPositiveMultiplicative_ae_pos] with t ht
    exact artinBesselK_scaled_integrand a b hx ht
  rw [hid]
  have hp : ((x / 2) ^ 2) ^ b * (x / 2) ^ (a - b) = (x / 2) ^ (a + b) := by
    rw [← Real.rpow_two (x / 2), ← Real.rpow_mul ha.le, ← Real.rpow_add ha]
    congr 1
    ring
  unfold artinBesselKIntegral
  rw [← mul_assoc, ← Complex.ofReal_mul, hp]
  push_cast
  ring

theorem artinLocalGammaProfile_bessel_integral {x : ℝ} (hx : 0 < x) :
    artinLocalGammaProfile ((x / 2) ^ 2) =
      (x ^ 2 / 2 : ℝ) * artinBesselKIntegral (1 / 3) x := by
  rw [artinLocalGammaProfile, artinGammaPairProfile_bessel_integral _ _ hx]
  rw [show (7 / 6 + 5 / 6 : ℝ) = 2 by norm_num,
    show (7 / 6 - 5 / 6 : ℝ) = 1 / 3 by norm_num, Real.rpow_two]
  push_cast
  ring

def artinBesselLocalProfile (c t : ℝ) : ℂ :=
  (t : ℂ) * artinBesselKIntegral (1 / 3) (c * Real.sqrt t)

theorem artinBesselLocalProfile_eq_gammaPair {c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    artinBesselLocalProfile c t =
      ((2 / c ^ 2 : ℝ) : ℂ) * artinLocalGammaProfile ((c ^ 2 / 4) * t) := by
  have hx : 0 < c * Real.sqrt t := mul_pos hc (Real.sqrt_pos.mpr ht)
  have hx2 : (c * Real.sqrt t) ^ 2 = c ^ 2 * t := by
    rw [mul_pow, Real.sq_sqrt ht.le]
  have hu : (c * Real.sqrt t / 2) ^ 2 = (c ^ 2 / 4) * t := by
    rw [div_pow, hx2]
    ring
  rw [artinBesselLocalProfile, ← hu, artinLocalGammaProfile_bessel_integral hx, hx2]
  push_cast
  field_simp [ne_of_gt hc]

theorem artinBesselLocalProfile_mellin_convergent {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : -(5 / 6 : ℝ) < s.re) : MellinConvergent (artinBesselLocalProfile c) s := by
  have he : MellinConvergent (fun t => ((2 / c ^ 2 : ℝ) : ℂ) *
      artinLocalGammaProfile ((c ^ 2 / 4) * t)) s :=
    ((MellinConvergent.comp_mul_left (by positivity : 0 < c ^ 2 / 4)).mpr
      (artinLocalGammaProfile_mellin_convergent hs)).const_smul ((2 / c ^ 2 : ℝ) : ℂ)
  apply (integrableOn_congr_fun (fun t ht => ?_) measurableSet_Ioi).mpr he
  change (t : ℂ) ^ (s - 1) * artinBesselLocalProfile c t = _
  rw [artinBesselLocalProfile_eq_gammaPair hc ht]
  rfl

/-- Exact local Mellin normalization for the actual K integral. The coefficient
is (2/c^2)*(c^2/4)^(-s), before any optional complex-power simplification. -/
theorem artinBesselLocalProfile_mellin {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : -(5 / 6 : ℝ) < s.re) :
    mellin (artinBesselLocalProfile c) s =
      ((2 / c ^ 2 : ℝ) : ℂ) * ((c ^ 2 / 4 : ℝ) : ℂ) ^ (-s) *
        (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) := by
  have he : mellin (artinBesselLocalProfile c) s =
      mellin (fun t => ((2 / c ^ 2 : ℝ) : ℂ) •
        artinLocalGammaProfile ((c ^ 2 / 4) * t)) s := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change (t : ℂ) ^ (s - 1) * artinBesselLocalProfile c t = _
    rw [artinBesselLocalProfile_eq_gammaPair hc ht]
    rfl
  rw [he, mellin_const_smul, mellin_comp_mul_left artinLocalGammaProfile s (by positivity),
    artinLocalGammaProfile_mellin hs]
  simp only [smul_eq_mul]
  ring

theorem artinBesselLocalProfile_mellin_gammaForm {c : ℝ} (hc : 0 < c) {s : ℂ}
    (hs : -(5 / 6 : ℝ) < s.re) :
    mellin (artinBesselLocalProfile c) s =
      ((2 / c ^ 2 : ℝ) : ℂ) * ((4 / c ^ 2 : ℝ) : ℂ) ^ s *
        (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) := by
  rw [artinBesselLocalProfile_mellin hc hs, Complex.cpow_neg,
    ← Complex.inv_cpow_ofReal_nonneg (by positivity : 0 ≤ c ^ 2 / 4),
    ← Complex.ofReal_inv]
  have he : (c ^ 2 / 4 : ℝ)⁻¹ = 4 / c ^ 2 := by simp [inv_div]
  rw [he]

theorem artinBesselLocalProfile_constants_pos {c : ℝ} (hc : 0 < c) :
    0 < 2 / c ^ 2 ∧ 0 < 4 / c ^ 2 := by
  constructor <;> positivity

end
end SimultaneousPrimitiveRoots
