module

public import SimultaneousPrimitiveRoots.FiniteNormCutoffHaar
public import SimultaneousPrimitiveRoots.ComplexNormKernelBessel

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Set Complex
noncomputable section

variable {G : Type*} [Group G]

/-- Transport in the full finite-and-complex group, leaving its finite component fixed. -/
def artinFiniteComplexNormSheetTransport (χ : G →* Multiplicative ℝ) (n : ℕ)
    (u : ℝ) (z : artinFiniteComplexNormKernel χ n) : G × (Fin (n + 1) → ℂˣ) :=
  (z.1.1, artinComplexNormSection n u * z.1.2)

theorem artinFiniteComplexNormSheetTransport_norm (χ : G →* Multiplicative ℝ)
    (n : ℕ) {u : ℝ} (hu : 0 < u) (z : artinFiniteComplexNormKernel χ n) :
    Real.exp (Multiplicative.toAdd (artinFiniteComplexNorm χ n
      (artinFiniteComplexNormSheetTransport χ n u z))) = u := by
  have hz : Real.exp (Multiplicative.toAdd (χ z.1.1)) *
      (∏ i, ‖(z.1.2 i : ℂ)‖ ^ 2) = 1 := by
    rw [← artinFiniteComplexNorm_exp]
    have h : artinFiniteComplexNorm χ n z.1 = 1 := z.2
    rw [h]
    exact Real.exp_zero
  rw [artinFiniteComplexNorm_exp]
  simp only [artinFiniteComplexNormSheetTransport, Pi.mul_apply, Units.val_mul,
    norm_mul, mul_pow, Finset.prod_mul_distrib]
  rw [artinComplexNormSection_product n hu]
  calc
    _ = u * (Real.exp (Multiplicative.toAdd (χ z.1.1)) *
      (∏ i, ‖(z.1.2 i : ℂ)‖ ^ 2)) := by ring
    _ = u := by rw [hz, mul_one]

variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace G] [SecondCountableTopology G]
  (χ : G →* Multiplicative ℝ) (U : Subgroup G) (n : ℕ)
  (hU : ∀ g ∈ U, χ g = 1)

/-- Integrate the transported local Bessel product against actual full-kernel Haar.
The finite cutoff is imposed on the full kernel, not on a separately chosen product measure. -/
def artinFiniteNormCutoffBesselProfile
    (μ : Measure (artinFiniteComplexNormKernel χ n)) (c : Fin (n + 1) → ℝ)
    (u : ℝ) : ℂ :=
  ∫ z in {z | z.1.1 ∈ U},
    ∏ i, artinBesselLocalProfile (c i)
      (‖((artinFiniteComplexNormSheetTransport χ n u z).2 i : ℂ)‖ ^ 2) ∂μ

def artinFiniteNormCutoffBesselC
    (μ : Measure (artinFiniteComplexNormKernel χ n)) [μ.IsHaarMeasure]
    (ν : Measure G) [ν.IsHaarMeasure]
    (hUo : IsOpen (U : Set G)) (c : Fin (n + 1) → ℝ) : ℝ :=
  (artinFiniteNormCutoffHaarFactor χ U n hU μ ν hUo : ℝ) *
    artinFiniteSheetMass ν U * artinFiniteBesselSheetC c

/-- Open-subgroup Haar pullback removes the need for full ambient Haar disintegration. -/
theorem artinFiniteNormCutoffBesselProfile_factor
    (μ : Measure (artinFiniteComplexNormKernel χ n)) [μ.IsHaarMeasure]
    (ν : Measure G) [ν.IsHaarMeasure]
    (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G))
    (c : Fin (n + 1) → ℝ) (u : ℝ) :
    artinFiniteNormCutoffBesselProfile χ U n μ c u =
      ((artinFiniteNormCutoffHaarFactor χ U n hU μ ν hUo : ℝ) *
        artinFiniteSheetMass ν U : ℂ) * artinFiniteBesselSheetProfile c u := by
  letI := artinFiniteUnitCutoffHaar_finite ν U hUc hUo
  rw [artinFiniteNormCutoffBesselProfile, artinFiniteNormCutoffHaar_integral χ U n hU μ ν hUo]
  change (artinFiniteNormCutoffHaarFactor χ U n hU μ ν hUo : ℂ) *
    (∫ p : U × artinComplexNormKernel n,
      ∏ i, artinBesselLocalProfile (c i)
        (‖(artinComplexNormSheetTransport n u p.2 i : ℂ)‖ ^ 2)
      ∂(artinFiniteUnitCutoffHaar ν U).prod (artinComplexNormKernelHaar n)) = _
  rw [integral_fun_snd (fun z : artinComplexNormKernel n =>
    ∏ i, artinBesselLocalProfile (c i) (‖(artinComplexNormSheetTransport n u z i : ℂ)‖ ^ 2))]
  rw [← artinComplexNormSheetMeasure_integral (artinComplexNormKernelHaar n) u
    (fun z => ∏ i, artinBesselLocalProfile (c i) (‖(z i : ℂ)‖ ^ 2))]
  change (artinFiniteNormCutoffHaarFactor χ U n hU μ ν hUo : ℂ) *
    ((artinFiniteUnitCutoffHaar ν U).real Set.univ •
      artinComplexNormBesselProfile (artinComplexNormKernelHaar n) c u) = _
  rw [artinComplexNormBesselProfile_factor, Measure.haarScalarFactor_self,
    show (artinFiniteUnitCutoffHaar ν U).real Set.univ = artinFiniteSheetMass ν U by
      rw [Measure.real, artinFiniteUnitCutoffHaar_mass ν U hUo]; rfl]
  simp only [NNReal.coe_one, Complex.ofReal_one, one_mul, Complex.real_smul, mul_assoc]

theorem artinFiniteNormCutoffBesselC_pos
    (μ : Measure (artinFiniteComplexNormKernel χ n)) [μ.IsHaarMeasure]
    (ν : Measure G) [ν.IsHaarMeasure]
    (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G))
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) :
    0 < artinFiniteNormCutoffBesselC χ U n hU μ ν hUo c := by
  exact mul_pos (mul_pos (artinFiniteNormCutoffHaarFactor_pos χ U n hU μ ν hUo)
    (artinFiniteSheetMass_pos (hUo.measure_ne_zero ν ⟨1, U.one_mem⟩) hUc.measure_ne_top))
    (artinFiniteBesselSheet_constants_pos hc).1

include hU in
theorem artinFiniteNormCutoffBesselProfile_mellin_convergent
    (μ : Measure (artinFiniteComplexNormKernel χ n)) [μ.IsHaarMeasure]
    (ν : Measure G) [ν.IsHaarMeasure]
    (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G))
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i)
    {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    MellinConvergent (artinFiniteNormCutoffBesselProfile χ U n μ c) s := by
  rw [funext (artinFiniteNormCutoffBesselProfile_factor χ U n hU μ ν hUc hUo c)]
  exact (artinFiniteBesselSheetProfile_mellin_convergent hc hs).const_smul
    (((artinFiniteNormCutoffHaarFactor χ U n hU μ ν hUo : ℝ) * artinFiniteSheetMass ν U) : ℂ)

theorem artinFiniteNormCutoffBesselProfile_mellin
    (μ : Measure (artinFiniteComplexNormKernel χ n)) [μ.IsHaarMeasure]
    (ν : Measure G) [ν.IsHaarMeasure]
    (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G))
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i)
    {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    mellin (artinFiniteNormCutoffBesselProfile χ U n μ c) s =
      (artinFiniteNormCutoffBesselC χ U n hU μ ν hUo c : ℂ) *
        (artinFiniteBesselSheetA c : ℂ) ^ s *
        (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ (n + 1) := by
  rw [funext (artinFiniteNormCutoffBesselProfile_factor χ U n hU μ ν hUc hUo c)]
  change mellin (fun u =>
    (((artinFiniteNormCutoffHaarFactor χ U n hU μ ν hUo : ℝ) * artinFiniteSheetMass ν U) : ℂ) •
      artinFiniteBesselSheetProfile c u) s = _
  rw [mellin_const_smul, artinFiniteBesselSheetProfile_mellin hc hs]
  simp only [artinFiniteNormCutoffBesselC, Complex.ofReal_mul, smul_eq_mul]
  ring

theorem artinFiniteNormCutoffBesselProfile_gaussian
    (μ : Measure (artinFiniteComplexNormKernel χ n)) [μ.IsHaarMeasure]
    (ν : Measure G) [ν.IsHaarMeasure]
    (hUc : IsCompact (U : Set G)) (hUo : IsOpen (U : Set G))
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) {u : ℝ} (hu : 0 < u) :
    (∫ T, reflectionKernel (artinFiniteNormCutoffBesselC χ U n hU μ ν hUo c)
      (artinFiniteBesselSheetA c) (n + 1) T *
        artinFiniteNormCutoffBesselProfile χ U n μ c (u * T)
      ∂artinPositiveMultiplicativeMeasure) = reflectionLogGaussian u := by
  apply reflectionProfile_gaussian_of_mellin_zero
    (ne_of_gt (artinFiniteNormCutoffBesselC_pos χ U n hU μ ν hUc hUo hc))
    (artinFiniteBesselSheet_constants_pos hc).2 (n + 1)
    (artinFiniteNormCutoffBesselProfile_mellin_convergent χ U n hU μ ν hUc hUo hc
      (by norm_num)) _ hu
  intro y
  exact artinFiniteNormCutoffBesselProfile_mellin χ U n hU μ ν hUc hUo hc (by norm_num)

end
end SimultaneousPrimitiveRoots
