module

public import SimultaneousPrimitiveRoots.KummerFiniteContourMain
public import SimultaneousPrimitiveRoots.Explicit.EntireZeroData
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientMultiplicity
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientCenter
public import SimultaneousPrimitiveRoots.Explicit.KummerUniformDeletionBridge
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientZeroInputs
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientCenter
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientZeroCount
public import SimultaneousPrimitiveRoots.Explicit.GaussianZeroCounting
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientZeroCounting
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientLogResidue
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientContourChoice
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientRectangle
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientLeftZeroCount
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientFiniteFormula
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientLeftZeroCounting
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientLeftRectangle
public import SimultaneousPrimitiveRoots.Explicit.KummerQuotientFiniteUpper
public import SimultaneousPrimitiveRoots.Explicit.KummerFiniteContourBound

/-! Generalization of `SimultaneousPrimitiveRoots.KummerFiniteContourMain` from the entire zeta quotient
to abstract `EntireZeroData` (machine-copied; only declarations depending on the quotient
hypothesis are restated). -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Explicit

open NumberField Metric Filter
noncomputable section
open Classical


/-- Actual entire continuation, uniform growth and gap, and one finite contour.
Existence of these analytic data is not asserted by this definition. -/
def KummerFiniteContourUpperInputs (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] (x δ C R : ℝ) : Prop :=
  ∃ H : ℂ → ℂ,
    EntireZeroData (PrimeKummerField a q) (CyclotomicField q ℚ) H ∧
    (∀ U : ℝ, 0 ≤ U → ∀ z ∈ sphere (2 : ℂ) (2 * (U + 2)),
      ‖H z‖ ≤ Real.exp
        (C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) * (U + 3) ^ 2)) ∧
    (∀ i : fullQuotientZeroIndex H, (fullQuotientIndexedZero H i).im ≠ 0 →
      |(fullQuotientIndexedZero H i).im| ≤ 2 * (q : ℝ) ^ 2 →
        (fullQuotientIndexedZero H i).re ≤ 1 - δ) ∧
    ∃ σ T : ℝ, -1 ≤ σ ∧ σ ≤ 0 ∧ 0 ≤ T ∧
      (∀ s ∈ PNTAnd.RectangleBorder ((σ : ℂ) - Complex.I * T)
        ((2 : ℂ) + Complex.I * T), H s ≠ 0) ∧
      (gaussianFiniteContourRemainder H ((q : ℂ) - 1) x σ T).re ≤
        R * (q : ℝ) * Real.log (2 * (q : ℝ))

def UniformKummerFiniteContourUpperInputs (A : Finset ℕ) (δ η C R : ℝ) (B : Set ℕ) : Prop :=
  ∀ᶠ x : ℝ in atTop, ∀ a ∈ A, ∀ q : ℕ, ∀ ha : 2 ≤ a, ∀ hq : q.Prime,
    ∀ haq : a < q, q ∉ B → q ≤ Nat.floor (2 * x ^ η) →
    letI : Fact (2 ≤ a) := ⟨ha⟩
    letI : Fact q.Prime := ⟨hq⟩
    letI : Fact (a < q) := ⟨haq⟩
    KummerFiniteContourUpperInputs a q x δ C R

/-- **The Kummer trace bound from one finite contour for `F_K`.** Compared with the quotient
version, the cyclotomic trace `Θ_{ℚ(ζ_q)}` is replaced by the main term
`M(x) = ∫_{t > 1} w(t/x) dt ≤ ŵ(1) x` of the pole of `ζ_K`; the hypothesis `hbase` now only
asks `ŵ(1) ≤ CE`. -/
theorem primeKummerGaussianTrace_bound_of_finite_contour
    {a q : ℕ} [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    {x δ CE C R : ℝ} (hx : 1 ≤ x) (hδ : δ ≤ 1)
    (hCE : 0 ≤ CE) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hi : KummerFiniteContourUpperInputs a q x δ C R)
    (hbase : Hecke.gaussianMainConstant ≤ CE) :
    gaussianPrimePowerTrace (PrimeKummerField a q) x ≤
      gaussianFiniteContourCountingConstant CE C R * x +
      gaussianFiniteContourCountingConstant CE C R *
        ((q : ℝ) * ((q : ℝ) - 1)) * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) := by
  obtain ⟨H, hH, hb, hg, σ, T, hσ, hσ0, hT, hborder, hrem⟩ := hi
  have hs := kummerFullQuotient_finite_contour_trace_le
    hH hC hx hδ hR hσ hσ0 hT hb hg hborder hrem
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
  have hd : 0 < (q : ℝ) - 1 := by linarith
  have hlog : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith)
  have hM := kummerGaussianZeroMassConstant_nonneg hC
  have hAC := artinGaussianConstant_pos.le
  have hmain : (∫ t in Set.Ioi (1 : ℝ), artinGaussianWeight (t / x)) ≤ CE * x := by
    have h1 := Hecke.gaussianMainTerm_le (by linarith : (0 : ℝ) < x)
    have h2 : x * Hecke.gaussianMainConstant ≤ CE * x := by nlinarith
    linarith
  have hfactor : gaussianPrimePowerTrace (PrimeKummerField a q) x =
      (∫ t in Set.Ioi (1 : ℝ), artinGaussianWeight (t / x)) +
        ((q : ℝ) - 1) * primeKummerGaussianFullSignedTrace a q x := by
    unfold primeKummerGaussianFullSignedTrace
    field_simp
    ring
  have ht := gaussian_q_height_tail_le (q := (q : ℝ)) (by linarith : (1 : ℝ) ≤ q)
  have hhigh : ((q : ℝ) - 1) *
      (artinGaussianConstant * kummerGaussianZeroMassConstant C * x * (q : ℝ) *
        Real.log (2 * (q : ℝ)) * Real.exp (-(q : ℝ) ^ 4 / 2)) ≤
      4 * artinGaussianConstant * kummerGaussianZeroMassConstant C * x := by
    calc
      _ = (artinGaussianConstant * kummerGaussianZeroMassConstant C * x) *
        (((q : ℝ) - 1) * (q : ℝ) * Real.log (2 * (q : ℝ)) *
          Real.exp (-(q : ℝ) ^ 4 / 2)) := by ring
      _ ≤ (artinGaussianConstant * kummerGaussianZeroMassConstant C * x) *
        ((q : ℝ) ^ 2 * Real.log (2 * (q : ℝ)) * Real.exp (-(q : ℝ) ^ 4 / 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        gcongr
        nlinarith
      _ ≤ (artinGaussianConstant * kummerGaussianZeroMassConstant C * x) * 4 :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by ring
  have htrace : gaussianPrimePowerTrace (PrimeKummerField a q) x ≤
      (CE + 4 * artinGaussianConstant * kummerGaussianZeroMassConstant C) * x +
      (3 * artinGaussianConstant * kummerGaussianZeroMassConstant C + R) *
        ((q : ℝ) * ((q : ℝ) - 1)) * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) := by
    rw [hfactor]
    have hh := add_le_add hmain (mul_le_mul_of_nonneg_left hs hd.le)
    nlinarith [hhigh]
  apply htrace.trans
  unfold gaussianFiniteContourCountingConstant
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ (by linarith : 0 ≤ x)
    nlinarith [mul_nonneg hAC hM]
  · apply mul_le_mul_of_nonneg_right _ hlog
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith : 0 ≤ x) _)
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Nat.cast_nonneg q) hd.le)
    nlinarith [mul_nonneg hAC hM]

/-- The large-good trace bound from finite contours for `F_K`; no cyclotomic input is needed
(`η < 1/5` is kept for compatibility with the quotient version). -/
theorem exists_gaussianFullLargeGoodTraceBound_of_finite_contours
    (A : Finset ℕ) {δ η C R : ℝ} {B : Set ℕ}
    (_hη : η < 1 / 5) (hδ : δ ≤ 1) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hi : UniformKummerFiniteContourUpperInputs A δ η C R B) :
    ∃ D : ℝ, 0 ≤ D ∧ GaussianFullLargeGoodTraceBound A δ η D B (fun _ => 0) := by
  refine ⟨gaussianFiniteContourCountingConstant Hecke.gaussianMainConstant C R,
    gaussianFiniteContourCountingConstant_nonneg Hecke.gaussianMainConstant_pos.le hC hR, ?_⟩
  filter_upwards [hi, eventually_ge_atTop (1 : ℝ)] with x hix hx
  intro a ha q ha2 hq haq _hlarge hgood hcut
  let : Fact (2 ≤ a) := ⟨ha2⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (a < q) := ⟨haq⟩
  exact primeKummerGaussianTrace_bound_of_finite_contour hx hδ
    Hecke.gaussianMainConstant_pos.le hC hR (hix a ha q ha2 hq haq hgood hcut) le_rfl

/-- This is a conditional closing theorem. The genuine finite-contour analytic
construction, actual KR and candidate supply are still required. -/
theorem mainClaim_of_finite_contour_inputs {δ η : ℝ}
    (hη : 0 ≤ η) (hηδ : η < δ) (hηfifth : η < 1 / 5) (hδ : δ ≤ 1)
    (hsupply : ∀ A : Finset ℕ, Admissible A →
      ∃ θ : ℝ, 0 < θ ∧ CandidateSupplyBound A η θ)
    (hi : ∀ A : Finset ℕ, Admissible A → ∃ C R : ℝ, ∃ B : Set ℕ,
      0 ≤ C ∧ 0 ≤ R ∧ Summable (badReciprocalWeight B) ∧
        UniformKummerFiniteContourUpperInputs A δ η C R B) : MainClaim := by
  apply mainClaim_of_all_good_gaussian_bounds hη hηδ hηfifth hsupply
  intro A hA
  obtain ⟨C, R, B, hC, hR, hB, hiA⟩ := hi A hA
  obtain ⟨D, hD, hg⟩ := exists_gaussianFullLargeGoodTraceBound_of_finite_contours
    A hηfifth hδ hC hR hiA
  exact ⟨D, B, hD, hB, hg⟩

end
end SimultaneousPrimitiveRoots.Explicit
