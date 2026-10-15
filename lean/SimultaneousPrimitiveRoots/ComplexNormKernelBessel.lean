module

public import SimultaneousPrimitiveRoots.ComplexNormKernelHaar
public import SimultaneousPrimitiveRoots.HaarCutoffMass

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
noncomputable section

/-- The Bessel profile integrated over an actual transported complex norm sheet. -/
def artinComplexNormBesselProfile {n : ℕ} (μ : Measure (artinComplexNormKernel n))
    (c : Fin (n + 1) → ℝ) (u : ℝ) : ℂ :=
  ∫ z, ∏ i, artinBesselLocalProfile (c i) (‖(z i : ℂ)‖ ^ 2)
    ∂artinComplexNormSheetMeasure μ u

def artinComplexNormBesselC {n : ℕ} (μ : Measure (artinComplexNormKernel n))
    [μ.IsHaarMeasure] (c : Fin (n + 1) → ℝ) : ℝ :=
  (Measure.haarScalarFactor μ (artinComplexNormKernelHaar n) : ℝ) *
    artinFiniteBesselSheetC c

/-- Angular mass is one; actual norm-sheet Haar leaves exactly the free log integral. -/
theorem artinComplexNormBesselProfile_factor {n : ℕ}
    (μ : Measure (artinComplexNormKernel n)) [μ.IsHaarMeasure]
    (c : Fin (n + 1) → ℝ) (u : ℝ) :
    artinComplexNormBesselProfile μ c u =
      (Measure.haarScalarFactor μ (artinComplexNormKernelHaar n) : ℂ) *
        artinFiniteBesselSheetProfile c u := by
  rw [artinComplexNormBesselProfile, artinComplexNormSheetMeasure_integral_normalized]
  simp_rw [artinComplexNormPoint_norm_sq]
  rw [integral_fun_fst (fun x : Multiplicative (Fin n → ℝ) =>
    ∏ i, artinBesselLocalProfile (c i)
      (Real.exp (artinFiniteLogNormSheetEquiv n (Real.log u, Multiplicative.toAdd x) i)))]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  rfl

theorem artinComplexNormBesselC_pos {n : ℕ}
    (μ : Measure (artinComplexNormKernel n)) [μ.IsHaarMeasure]
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) :
    0 < artinComplexNormBesselC μ c :=
  mul_pos (artinComplexNormKernelHaar_normalization_pos μ)
    (artinFiniteBesselSheet_constants_pos hc).1

theorem artinComplexNormBesselProfile_mellin_convergent {n : ℕ}
    (μ : Measure (artinComplexNormKernel n)) [μ.IsHaarMeasure]
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    MellinConvergent (artinComplexNormBesselProfile μ c) s := by
  rw [funext (artinComplexNormBesselProfile_factor μ c)]
  exact (artinFiniteBesselSheetProfile_mellin_convergent hc hs).const_smul
    (Measure.haarScalarFactor μ (artinComplexNormKernelHaar n) : ℂ)

theorem artinComplexNormBesselProfile_mellin {n : ℕ}
    (μ : Measure (artinComplexNormKernel n)) [μ.IsHaarMeasure]
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    mellin (artinComplexNormBesselProfile μ c) s =
      (artinComplexNormBesselC μ c : ℂ) * (artinFiniteBesselSheetA c : ℂ) ^ s *
        (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ (n + 1) := by
  rw [funext (artinComplexNormBesselProfile_factor μ c)]
  change mellin (fun u =>
    (Measure.haarScalarFactor μ (artinComplexNormKernelHaar n) : ℂ) •
      artinFiniteBesselSheetProfile c u) s = _
  rw [mellin_const_smul, artinFiniteBesselSheetProfile_mellin hc hs]
  simp only [artinComplexNormBesselC, Complex.ofReal_mul, smul_eq_mul]
  ring

/-- Every positive scale has the Gaussian identity on actual complex norm sheets. -/
theorem artinComplexNormBesselProfile_gaussian {n : ℕ}
    (μ : Measure (artinComplexNormKernel n)) [μ.IsHaarMeasure]
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) {u : ℝ} (hu : 0 < u) :
    (∫ T, reflectionKernel (artinComplexNormBesselC μ c) (artinFiniteBesselSheetA c)
      (n + 1) T * artinComplexNormBesselProfile μ c (u * T)
        ∂artinPositiveMultiplicativeMeasure) = reflectionLogGaussian u := by
  apply reflectionProfile_gaussian_of_mellin_zero
    (ne_of_gt (artinComplexNormBesselC_pos μ hc))
    (artinFiniteBesselSheet_constants_pos hc).2 (n + 1)
    (artinComplexNormBesselProfile_mellin_convergent μ hc (by norm_num)) _ hu
  intro y
  exact artinComplexNormBesselProfile_mellin μ hc (by norm_num)

/-- Actual finite-cutoff integration coupled to the transported archimedean sheet.
The paper's finite local-unit topology and product norm still have to be connected. -/
def artinComplexNormCutoffBesselProfile {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (ν : Measure Ω) (U : Set Ω) (μ : Measure (artinComplexNormKernel n))
    (c : Fin (n + 1) → ℝ) (u : ℝ) : ℂ :=
  ∫ _ in U, artinComplexNormBesselProfile μ c u ∂ν

theorem artinComplexNormCutoffBesselProfile_factor {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (ν : Measure Ω) (U : Set Ω) (μ : Measure (artinComplexNormKernel n))
    (c : Fin (n + 1) → ℝ) (u : ℝ) :
    artinComplexNormCutoffBesselProfile ν U μ c u =
      (artinFiniteSheetMass ν U : ℂ) * artinComplexNormBesselProfile μ c u := by
  simp [artinComplexNormCutoffBesselProfile, artinFiniteSheetMass, integral_const,
    Measure.real, Complex.real_smul]

theorem artinComplexNormCutoffBesselProfile_mellin_convergent {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (ν : Measure Ω) (U : Set Ω)
    (μ : Measure (artinComplexNormKernel n)) [μ.IsHaarMeasure]
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    MellinConvergent (artinComplexNormCutoffBesselProfile ν U μ c) s := by
  rw [funext (artinComplexNormCutoffBesselProfile_factor ν U μ c)]
  exact (artinComplexNormBesselProfile_mellin_convergent μ hc hs).const_smul
    (artinFiniteSheetMass ν U : ℂ)

theorem artinComplexNormCutoffBesselProfile_mellin {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (ν : Measure Ω) (U : Set Ω) (μ : Measure (artinComplexNormKernel n))
    [μ.IsHaarMeasure] {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i)
    {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    mellin (artinComplexNormCutoffBesselProfile ν U μ c) s =
      ((artinFiniteSheetMass ν U * artinComplexNormBesselC μ c : ℝ) : ℂ) *
        (artinFiniteBesselSheetA c : ℂ) ^ s *
        (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ (n + 1) := by
  rw [funext (artinComplexNormCutoffBesselProfile_factor ν U μ c)]
  change mellin (fun u => (artinFiniteSheetMass ν U : ℂ) •
    artinComplexNormBesselProfile μ c u) s = _
  rw [mellin_const_smul, artinComplexNormBesselProfile_mellin μ hc hs]
  simp only [smul_eq_mul, Complex.ofReal_mul]
  ring

theorem artinComplexNormCutoffBesselProfile_gaussian {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} {ν : Measure Ω} {U : Set Ω} (h0 : ν U ≠ 0) (hfin : ν U ≠ ⊤)
    (μ : Measure (artinComplexNormKernel n)) [μ.IsHaarMeasure]
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) {u : ℝ} (hu : 0 < u) :
    (∫ T, reflectionKernel (artinFiniteSheetMass ν U * artinComplexNormBesselC μ c)
      (artinFiniteBesselSheetA c) (n + 1) T *
        artinComplexNormCutoffBesselProfile ν U μ c (u * T)
          ∂artinPositiveMultiplicativeMeasure) = reflectionLogGaussian u := by
  apply reflectionProfile_gaussian_of_mellin_zero
    (ne_of_gt (mul_pos (artinFiniteSheetMass_pos h0 hfin) (artinComplexNormBesselC_pos μ hc)))
    (artinFiniteBesselSheet_constants_pos hc).2 (n + 1)
    (artinComplexNormCutoffBesselProfile_mellin_convergent ν U μ hc (by norm_num)) _ hu
  intro y
  exact artinComplexNormCutoffBesselProfile_mellin ν U μ hc (by norm_num)

theorem artinComplexNormCutoffBesselProfile_gaussian_compact_open
    {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω] {ν : Measure Ω}
    [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν] {U : Set Ω}
    (hUc : IsCompact U) (hUo : IsOpen U) (hne : U.Nonempty)
    {n : ℕ} (μ : Measure (artinComplexNormKernel n)) [μ.IsHaarMeasure]
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) {u : ℝ} (hu : 0 < u) :
    (∫ T, reflectionKernel (artinFiniteSheetMass ν U * artinComplexNormBesselC μ c)
      (artinFiniteBesselSheetA c) (n + 1) T *
        artinComplexNormCutoffBesselProfile ν U μ c (u * T)
          ∂artinPositiveMultiplicativeMeasure) = reflectionLogGaussian u :=
  artinComplexNormCutoffBesselProfile_gaussian
    (hUo.measure_ne_zero ν hne) hUc.measure_ne_top μ hc hu

end
end SimultaneousPrimitiveRoots
