module

public import SimultaneousPrimitiveRoots.LogNormSheetDisintegration
public import SimultaneousPrimitiveRoots.MellinProfileTransport

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Filter Set Complex
open scoped Topology
noncomputable section

/-- The actual mass of the finite-place/angular cutoff, not an unspecified constant. -/
def artinFiniteSheetMass {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (U : Set Ω) : ℝ :=
  (ν U).toReal

/-- Actual cutoff integration of the two-coordinate radial norm-sheet integral. -/
def artinFiniteMassNormSheetProfile {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (U : Set Ω) (f : ℝ × ℝ → ℂ) (u : ℝ) : ℂ :=
  ∫ _θ in U, artinPositiveNormSheetProfile f u ∂ν

theorem artinFiniteSheetMass_pos {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {U : Set Ω} (h0 : ν U ≠ 0) (hfin : ν U ≠ ⊤) :
    0 < artinFiniteSheetMass ν U := ENNReal.toReal_pos h0 hfin

theorem artinFiniteMassNormSheetProfile_factor {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (U : Set Ω) (f : ℝ × ℝ → ℂ) (u : ℝ) :
    artinFiniteMassNormSheetProfile ν U f u =
      (artinFiniteSheetMass ν U : ℂ) * artinPositiveNormSheetProfile f u := by
  simp [artinFiniteMassNormSheetProfile, artinFiniteSheetMass, integral_const,
    Measure.real, Complex.real_smul]

theorem artinFiniteMassNormSheetProfile_mellin_convergent {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (U : Set Ω) {f : ℝ × ℝ → ℂ} {s : ℂ}
    (hf : Integrable (fun p => Complex.exp (s * ((p.1 + p.2 : ℝ) : ℂ)) * f p)
      (volume.prod volume)) : MellinConvergent (artinFiniteMassNormSheetProfile ν U f) s := by
  have he := funext (artinFiniteMassNormSheetProfile_factor ν U f)
  rw [he]
  exact (artinPositiveNormSheetProfile_mellin_convergent hf).const_smul
    (artinFiniteSheetMass ν U : ℂ)

theorem artinFiniteMassNormSheetProfile_mellin {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (U : Set Ω) {f : ℝ × ℝ → ℂ} {s : ℂ}
    (hf : Integrable (fun p => Complex.exp (s * ((p.1 + p.2 : ℝ) : ℂ)) * f p)
      (volume.prod volume)) :
    mellin (artinFiniteMassNormSheetProfile ν U f) s =
      (artinFiniteSheetMass ν U : ℂ) *
        ∫ p, Complex.exp (s * ((p.1 + p.2 : ℝ) : ℂ)) * f p ∂(volume.prod volume) := by
  have he := funext (artinFiniteMassNormSheetProfile_factor ν U f)
  rw [he]
  change mellin (fun u => (artinFiniteSheetMass ν U : ℂ) •
    artinPositiveNormSheetProfile f u) s = _
  rw [mellin_const_smul, artinPositiveNormSheetProfile_mellin hf, smul_eq_mul]

/-- Two actual local K factors on the norm sheet, with mass determined by ν(U).
Identification of ν and this coordinate model with the paper Haar measure remains open. -/
def artinFiniteMassBesselSheetProfile {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (U : Set Ω) (c d : ℝ) : ℝ → ℂ :=
  artinFiniteMassNormSheetProfile ν U
    (fun p => artinBesselLocalProfile d (Real.exp p.1) *
      artinBesselLocalProfile c (Real.exp p.2))

theorem artinFiniteMassBesselSheetProfile_eq_finite {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (U : Set Ω) (c d : ℝ) {u : ℝ} (hu : 0 < u) :
    artinFiniteMassBesselSheetProfile ν U c d u =
      artinBesselFiniteProfile (artinFiniteSheetMass ν U) c [d] u := by
  rw [artinFiniteMassBesselSheetProfile, artinFiniteMassNormSheetProfile_factor,
    artinPositiveNormSheetProfile_product _ _ hu]
  rfl

theorem artinFiniteMassBesselSheetProfile_ae_finite {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (U : Set Ω) (c d : ℝ) :
    artinFiniteMassBesselSheetProfile ν U c d =ᵐ[artinPositiveMultiplicativeMeasure]
      artinBesselFiniteProfile (artinFiniteSheetMass ν U) c [d] := by
  filter_upwards [artinPositiveMultiplicative_ae_pos] with u hu
  exact artinFiniteMassBesselSheetProfile_eq_finite ν U c d hu

theorem artinFiniteMassBesselSheetProfile_mellin_convergent {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (U : Set Ω) {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    MellinConvergent (artinFiniteMassBesselSheetProfile ν U c d) s :=
  (artinMellin_convergent_congr_ae
    (artinFiniteMassBesselSheetProfile_ae_finite ν U c d) s).mpr
    (artinBesselFiniteProfile_mellin_convergent _ hc (by simpa) hs)

theorem artinFiniteMassBesselSheetProfile_mellin {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (U : Set Ω) {c d : ℝ} (hc : 0 < c) (hd : 0 < d)
    {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    mellin (artinFiniteMassBesselSheetProfile ν U c d) s =
      ((artinFiniteSheetMass ν U * artinBesselProductC c [d] : ℝ) : ℂ) *
        (artinBesselProductA c [d] : ℂ) ^ s *
        (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ 2 := by
  rw [artinMellin_congr_ae (artinFiniteMassBesselSheetProfile_ae_finite ν U c d) s,
    artinBesselFiniteProfile_mellin _ hc (by simpa) hs]
  rfl

theorem artinFiniteMassBesselSheetProfile_gaussian_smoothing {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {U : Set Ω} (h0 : ν U ≠ 0) (hfin : ν U ≠ ⊤)
    {c d : ℝ} (hc : 0 < c) (hd : 0 < d) {u : ℝ} (hu : 0 < u) :
    (∫ T, reflectionKernel (artinFiniteSheetMass ν U * artinBesselProductC c [d])
      (artinBesselProductA c [d]) 2 T * artinFiniteMassBesselSheetProfile ν U c d (u * T)
        ∂artinPositiveMultiplicativeMeasure) = reflectionLogGaussian u := by
  exact artinHaarProfile_gaussian_of_ae_finiteProfile
    (artinFiniteSheetMass_pos h0 hfin) hc (by simpa)
    (artinFiniteMassBesselSheetProfile_ae_finite ν U c d) hu

end
end SimultaneousPrimitiveRoots
