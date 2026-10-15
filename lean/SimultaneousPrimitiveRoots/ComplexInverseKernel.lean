module

public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Metric MeasureTheory Set
noncomputable section

/-- The value at the pole is zero under Lean's total inverse. Integrability
and the integral bound below treat the actual singularity off that point. -/
def complexInverseDistanceKernel (ρ z : ℂ) : ℝ := ‖z - ρ‖⁻¹

theorem complexInverseDistanceKernel_nonneg (ρ z : ℂ) :
    0 ≤ complexInverseDistanceKernel ρ z := by unfold complexInverseDistanceKernel; positivity

theorem complexInverseDistanceKernel_measurable (ρ : ℂ) :
    Measurable (complexInverseDistanceKernel ρ) := by
  unfold complexInverseDistanceKernel
  fun_prop

/-- The radial Jacobian cancels the singularity: r * r^(-1) = 1 a.e. -/
theorem complex_inverse_norm_integrableOn_ball (r : ℝ) :
    IntegrableOn (fun z : ℂ => ‖z‖⁻¹) (ball 0 r) := by
  rw [integrableOn_fun_norm_addHaar (volume : Measure ℂ), Complex.finrank_real_complex]
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioo 0 r) := integrableOn_const (by simp)
  apply hconst.congr_fun _ measurableSet_Ioo
  intro y hy
  simp [hy.1.ne']

theorem complex_integral_inverse_norm_ball {r : ℝ} (hr : 0 < r) :
    (∫ z : ℂ in ball 0 r, ‖z‖⁻¹) = 2 * Real.pi * r := by
  rw [← integral_indicator measurableSet_ball]
  have hrad : (ball (0 : ℂ) r).indicator (fun z : ℂ => ‖z‖⁻¹) =
      fun z : ℂ => (Iio r).indicator (fun t : ℝ => t⁻¹) ‖z‖ := by
    funext z
    simp [indicator, mem_ball_zero_iff]
  rw [hrad, integral_fun_norm_addHaar (volume : Measure ℂ)]
  simp only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul, nsmul_eq_mul]
  have heq : (∫ y : ℝ in Ioi 0, y * (Iio r).indicator (fun t : ℝ => t⁻¹) y) =
      ∫ y : ℝ in Ioi 0, (Iio r).indicator (fun _ : ℝ => (1 : ℝ)) y := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    by_cases hyr : y < r
    · simp [hyr, (Set.mem_Ioi.mp hy).ne']
    · simp [hyr]
  rw [heq, integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  have hset : Iio r ∩ Ioi (0 : ℝ) = Ioo 0 r := by ext y; simp; tauto
  rw [hset, integral_const]
  have hball : (volume : Measure ℂ).real (ball 0 1) = Real.pi := by
    simp [Measure.real]
  have hvol : (volume (Ioo (0 : ℝ) r)).toReal = r := by
    simp [Real.volume_Ioo, hr.le]
  rw [hball]
  simp only [Measure.real, Measure.restrict_apply_univ, smul_eq_mul, mul_one]
  rw [hvol]
  norm_num
  ring

/-- Translation does not change either integrability or the radial integral. -/
theorem complexInverseDistanceKernel_integrableOn_ball (ρ : ℂ) (r : ℝ) :
    IntegrableOn (complexInverseDistanceKernel ρ) (ball ρ r) := by
  have hm := measurePreserving_sub_right (volume : Measure ℂ) ρ
  have he : MeasurableEmbedding (fun z : ℂ => z - ρ) :=
    (Homeomorph.addRight (-ρ)).measurableEmbedding
  have hi := (hm.integrableOn_comp_preimage he).mpr (complex_inverse_norm_integrableOn_ball r)
  have hs : (fun z : ℂ => z - ρ) ⁻¹' ball 0 r = ball ρ r := by
    ext z; simp [mem_ball, dist_eq_norm]
  change IntegrableOn (fun z : ℂ => ‖z - ρ‖⁻¹) (ball ρ r)
  simpa only [hs, Function.comp_def] using hi

theorem complexInverseDistanceKernel_integral_ball (ρ : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ z : ℂ in ball ρ r, complexInverseDistanceKernel ρ z) = 2 * Real.pi * r := by
  have hm := measurePreserving_sub_right (volume : Measure ℂ) ρ
  have he : MeasurableEmbedding (fun z : ℂ => z - ρ) :=
    (Homeomorph.addRight (-ρ)).measurableEmbedding
  have hi := hm.setIntegral_preimage_emb he (fun z : ℂ => ‖z‖⁻¹) (ball 0 r)
  have hs : (fun z : ℂ => z - ρ) ⁻¹' ball 0 r = ball ρ r := by
    ext z; simp [mem_ball, dist_eq_norm]
  simpa only [hs, complexInverseDistanceKernel, complex_integral_inverse_norm_ball hr] using hi

/-- A finite-volume region has a pole-location-independent bound. Split at
radius one; outside that ball the inverse-distance kernel is at most one. -/
theorem complexInverseDistanceKernel_integral_le {S : Set ℂ}
    (hS : MeasurableSet S) (hvol : volume S ≠ ⊤) (ρ : ℂ) :
    IntegrableOn (complexInverseDistanceKernel ρ) S ∧
      (∫ z : ℂ in S, complexInverseDistanceKernel ρ z) ≤
        2 * Real.pi + (volume S).toReal := by
  let k := complexInverseDistanceKernel ρ
  let g := (ball ρ 1).indicator k
  have hi : Integrable g :=
    (complexInverseDistanceKernel_integrableOn_ball ρ 1).integrable_indicator measurableSet_ball
  have hc : IntegrableOn (fun _ : ℂ => (1 : ℝ)) S := integrableOn_const hvol
  have hg : IntegrableOn (fun z : ℂ => g z + 1) S := hi.integrableOn.add hc
  have hp : ∀ z : ℂ, k z ≤ g z + 1 := by
    intro z
    by_cases hz : z ∈ ball ρ 1
    · simp only [g, indicator_of_mem hz]; linarith
    · have hd : 1 ≤ ‖z - ρ‖ := by simpa [mem_ball, dist_eq_norm, not_lt] using hz
      have hk : k z ≤ 1 := by
        dsimp [k, complexInverseDistanceKernel]
        exact inv_le_one_of_one_le₀ hd
      simpa only [g, indicator_of_notMem hz, zero_add] using hk
  have hk : IntegrableOn k S := hg.mono'
    (complexInverseDistanceKernel_measurable ρ).aestronglyMeasurable.restrict
    (Filter.Eventually.of_forall (fun z => by
      rw [Real.norm_of_nonneg (complexInverseDistanceKernel_nonneg ρ z)]; exact hp z))
  refine ⟨hk, ?_⟩
  have hmono := setIntegral_mono_on hk hg hS (fun z _ => hp z)
  rw [integral_add hi.integrableOn hc, integral_const, smul_eq_mul, mul_one] at hmono
  have hn : 0 ≤ᵐ[volume] g := Filter.Eventually.of_forall (fun z => by
    dsimp [g]; exact indicator_nonneg (fun w _ => complexInverseDistanceKernel_nonneg ρ w) z)
  have hnear := setIntegral_le_integral (s := S) hi hn
  have hnearval : (∫ z : ℂ, g z) = 2 * Real.pi := by
    dsimp [g, k]
    rw [integral_indicator measurableSet_ball,
      complexInverseDistanceKernel_integral_ball ρ (by norm_num)]
    simp
  rw [hnearval] at hnear
  change (∫ z : ℂ in S, k z) ≤ 2 * Real.pi + (volume S).toReal
  simp only [Measure.real, Measure.restrict_apply_univ] at hmono
  exact hmono.trans (add_le_add hnear le_rfl)

end
end SimultaneousPrimitiveRoots
