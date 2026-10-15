module

public import SimultaneousPrimitiveRoots.FiniteLogNormSheet
public import SimultaneousPrimitiveRoots.FiniteMassNormSheet

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open MeasureTheory Filter Set Complex
open scoped Topology
noncomputable section

theorem artinFinitePositiveProduct_cpow {ι : Type*} [Fintype ι]
    (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (s : ℂ) :
    ((∏ i, a i : ℝ) : ℂ) ^ s = ∏ i, (a i : ℂ) ^ s := by
  classical
  have h : ∀ S : Finset ι, ((∏ i ∈ S, a i : ℝ) : ℂ) ^ s = ∏ i ∈ S, (a i : ℂ) ^ s := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (ha i) (Finset.prod_nonneg (fun j _ => ha j)), ih]
  exact h Finset.univ

def artinFiniteBesselSheetC {n : ℕ} (c : Fin (n + 1) → ℝ) : ℝ :=
  ∏ i, 2 / (c i) ^ 2

def artinFiniteBesselSheetA {n : ℕ} (c : Fin (n + 1) → ℝ) : ℝ :=
  ∏ i, 4 / (c i) ^ 2

theorem artinFiniteBesselSheet_constants_pos {n : ℕ} {c : Fin (n + 1) → ℝ}
    (hc : ∀ i, 0 < c i) :
    0 < artinFiniteBesselSheetC c ∧ 0 < artinFiniteBesselSheetA c := by
  constructor <;> apply Finset.prod_pos <;> intro i _ <;>
    have h := hc i <;> positivity

/-- This is an actual (r-1)-dimensional norm-sheet integral of r local K integrals.
No recursive-convolution or transform-defined profile is used. -/
def artinFiniteBesselSheetProfile {n : ℕ} (c : Fin (n + 1) → ℝ) : ℝ → ℂ :=
  artinFinitePositiveNormSheetProfile n
    (fun p => ∏ i, artinBesselLocalProfile (c i) (Real.exp (p i)))

theorem artinFiniteBesselSheetProfile_weighted_integrable {n : ℕ}
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    Integrable (fun p : Fin (n + 1) → ℝ =>
      Complex.exp (s * ((∑ i, p i : ℝ) : ℂ)) *
        ∏ i, artinBesselLocalProfile (c i) (Real.exp (p i))) :=
  artinFiniteRadialProduct_weighted_integrable
    (fun i => artinBesselLocalProfile_mellin_convergent (hc i) hs)

theorem artinFiniteBesselSheetProfile_mellin_convergent {n : ℕ}
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    MellinConvergent (artinFiniteBesselSheetProfile c) s :=
  artinFiniteRadialProduct_mellin_convergent
    (fun i => artinBesselLocalProfile_mellin_convergent (hc i) hs)

theorem artinFiniteBesselSheetProfile_mellin_product {n : ℕ}
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    mellin (artinFiniteBesselSheetProfile c) s =
      ∏ i, mellin (artinBesselLocalProfile (c i)) s :=
  artinFiniteRadialProduct_mellin
    (fun i => artinBesselLocalProfile_mellin_convergent (hc i) hs)

theorem artinFiniteBesselSheetProfile_mellin {n : ℕ}
    {c : Fin (n + 1) → ℝ} (hc : ∀ i, 0 < c i) {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    mellin (artinFiniteBesselSheetProfile c) s =
      (artinFiniteBesselSheetC c : ℂ) * (artinFiniteBesselSheetA c : ℂ) ^ s *
        (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ (n + 1) := by
  rw [artinFiniteBesselSheetProfile_mellin_product hc hs]
  simp_rw [artinBesselLocalProfile_mellin_gammaForm (hc _) hs]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← Complex.ofReal_prod, ← artinFinitePositiveProduct_cpow
    (fun i => 4 / (c i) ^ 2) (fun _ => by positivity) s]
  rfl

/-- Actual cutoff integration on the finite-dimensional radial sheet.
Identification of the cutoff and radial coordinates with F_S Haar data remains open. -/
def artinFiniteHaarBesselSheetProfile {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (ν : Measure Ω) (U : Set Ω) (c : Fin (n + 1) → ℝ) (u : ℝ) : ℂ :=
  ∫ _θ in U, artinFiniteBesselSheetProfile c u ∂ν

theorem artinFiniteHaarBesselSheetProfile_factor {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (ν : Measure Ω) (U : Set Ω) (c : Fin (n + 1) → ℝ) (u : ℝ) :
    artinFiniteHaarBesselSheetProfile ν U c u =
      (artinFiniteSheetMass ν U : ℂ) * artinFiniteBesselSheetProfile c u := by
  simp [artinFiniteHaarBesselSheetProfile, artinFiniteSheetMass, integral_const,
    Measure.real, Complex.real_smul]

theorem artinFiniteHaarBesselSheetProfile_mellin_convergent {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (ν : Measure Ω) (U : Set Ω) {c : Fin (n + 1) → ℝ}
    (hc : ∀ i, 0 < c i) {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    MellinConvergent (artinFiniteHaarBesselSheetProfile ν U c) s := by
  have he := funext (artinFiniteHaarBesselSheetProfile_factor ν U c)
  rw [he]
  exact (artinFiniteBesselSheetProfile_mellin_convergent hc hs).const_smul
    (artinFiniteSheetMass ν U : ℂ)

theorem artinFiniteHaarBesselSheetProfile_mellin {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (ν : Measure Ω) (U : Set Ω) {c : Fin (n + 1) → ℝ}
    (hc : ∀ i, 0 < c i) {s : ℂ} (hs : -(5 / 6 : ℝ) < s.re) :
    mellin (artinFiniteHaarBesselSheetProfile ν U c) s =
      ((artinFiniteSheetMass ν U * artinFiniteBesselSheetC c : ℝ) : ℂ) *
        (artinFiniteBesselSheetA c : ℂ) ^ s *
        (Complex.Gamma (s + 5 / 6) * Complex.Gamma (s + 7 / 6)) ^ (n + 1) := by
  have he := funext (artinFiniteHaarBesselSheetProfile_factor ν U c)
  rw [he]
  change mellin (fun u => (artinFiniteSheetMass ν U : ℂ) •
    artinFiniteBesselSheetProfile c u) s = _
  rw [mellin_const_smul, artinFiniteBesselSheetProfile_mellin hc hs]
  simp only [smul_eq_mul, Complex.ofReal_mul]
  ring

/-- Every-point Gaussian smoothing follows directly from the actual sheet Mellin
formula. No identification of individual fibers with finite convolutions is needed. -/
theorem artinFiniteHaarBesselSheetProfile_gaussian_smoothing
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} {ν : Measure Ω} {U : Set Ω}
    (h0 : ν U ≠ 0) (hfin : ν U ≠ ⊤) {c : Fin (n + 1) → ℝ}
    (hc : ∀ i, 0 < c i) {u : ℝ} (hu : 0 < u) :
    (∫ T, reflectionKernel (artinFiniteSheetMass ν U * artinFiniteBesselSheetC c)
      (artinFiniteBesselSheetA c) (n + 1) T *
        artinFiniteHaarBesselSheetProfile ν U c (u * T)
          ∂artinPositiveMultiplicativeMeasure) = reflectionLogGaussian u := by
  have hD := artinFiniteSheetMass_pos h0 hfin
  have hC := (artinFiniteBesselSheet_constants_pos hc).1
  have hA := (artinFiniteBesselSheet_constants_pos hc).2
  apply reflectionProfile_gaussian_of_mellin_zero (ne_of_gt (mul_pos hD hC)) hA (n + 1)
    (artinFiniteHaarBesselSheetProfile_mellin_convergent ν U hc (by norm_num))
    _ hu
  intro y
  exact artinFiniteHaarBesselSheetProfile_mellin ν U hc (by norm_num)

end
end SimultaneousPrimitiveRoots
