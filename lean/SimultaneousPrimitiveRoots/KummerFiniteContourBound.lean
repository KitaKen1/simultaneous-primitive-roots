module

public import SimultaneousPrimitiveRoots.KummerQuotientFiniteUpper

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField Metric Classical
noncomputable section

/-- Exact splitting of a finite actual zero set by the sign of the real part. -/
theorem finiteZeroResidueSum_split (P Q : ℂ → Prop)
    (hf : {s : ℂ | P s ∧ Q s}.Finite) (f : ℂ → ℂ) :
    (∑' s : {s : ℂ // P s ∧ Q s}, f s) =
      (∑' s : {s : ℂ // P s ∧ Q s ∧ s.re < 0}, f s) +
      ∑' s : {s : ℂ // P s ∧ Q s ∧ 0 ≤ s.re}, f s := by
  let J := {s : ℂ // P s ∧ Q s}
  let : Fintype J := hf.fintype
  let : Fintype {s : ℂ // P s ∧ Q s ∧ s.re < 0} :=
    (hf.subset (fun _ hs => ⟨hs.1, hs.2.1⟩)).fintype
  let : Fintype {s : ℂ // P s ∧ Q s ∧ 0 ≤ s.re} :=
    (hf.subset (fun _ hs => ⟨hs.1, hs.2.1⟩)).fintype
  let eL : {s : J // s.val.re < 0} ≃ {s : ℂ // P s ∧ Q s ∧ s.re < 0} :=
    { toFun := fun s => ⟨s.val.val, s.val.property.1, s.val.property.2, s.property⟩
      invFun := fun s => ⟨⟨s.val, s.property.1, s.property.2.1⟩, s.property.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let eR : {s : J // ¬s.val.re < 0} ≃ {s : ℂ // P s ∧ Q s ∧ 0 ≤ s.re} :=
    { toFun := fun s => ⟨s.val.val, s.val.property.1, s.val.property.2, not_lt.mp s.property⟩
      invFun := fun s => ⟨⟨s.val, s.property.1, s.property.2.1⟩, not_lt.mpr s.property.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h := Fintype.sum_subtype_add_sum_subtype (fun s : J => s.val.re < 0) (fun s : J => f s.val)
  have hL := Fintype.sum_equiv eL (fun s => f s.val.val) (fun s => f s.val) (fun _ => rfl)
  have hR := Fintype.sum_equiv eR (fun s => f s.val.val) (fun s => f s.val) (fun _ => rfl)
  rw [hL, hR] at h
  simpa only [tsum_fintype] using h.symm

/-- A single finite contour with a one-sided remainder bound suffices for the
actual full trace upper bound. No infinite-height signed formula is required. -/
theorem kummerFullQuotient_finite_contour_trace_le
    {a q : ℕ} [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation
      (PrimeKummerField a q) (CyclotomicField q ℚ) H)
    {C x δ σ T R : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x) (hδ : δ ≤ 1) (hR : 0 ≤ R)
    (hσ : -1 ≤ σ) (hσ0 : σ ≤ 0) (hT : 0 ≤ T)
    (hb : ∀ U : ℝ, 0 ≤ U → ∀ z ∈ sphere (2 : ℂ) (2 * (U + 2)),
      ‖H z‖ ≤ Real.exp
        (C * (q : ℝ) * ((q : ℝ) - 1) * Real.log (2 * (q : ℝ)) * (U + 3) ^ 2))
    (hg : ∀ i : fullQuotientZeroIndex H, (fullQuotientIndexedZero H i).im ≠ 0 →
      |(fullQuotientIndexedZero H i).im| ≤ 2 * (q : ℝ) ^ 2 →
        (fullQuotientIndexedZero H i).re ≤ 1 - δ)
    (hborder : ∀ s ∈ PNTAnd.RectangleBorder ((σ : ℂ) - Complex.I * T)
      ((2 : ℂ) + Complex.I * T), H s ≠ 0)
    (hrem : (gaussianFiniteContourRemainder H ((q : ℂ) - 1) x σ T).re ≤
      R * (q : ℝ) * Real.log (2 * (q : ℝ))) :
    primeKummerGaussianFullSignedTrace a q x ≤
      (3 * artinGaussianConstant * kummerGaussianZeroMassConstant C + R) *
        x ^ (1 - δ) * (q : ℝ) * Real.log (2 * (q : ℝ)) +
      artinGaussianConstant * kummerGaussianZeroMassConstant C *
        x * (q : ℝ) * Real.log (2 * (q : ℝ)) * Real.exp (-(q : ℝ) ^ 4 / 2) := by
  have hr := kummerFullQuotient_finite_gaussian_formula hH
    (by linarith : 0 < x) (by linarith : σ ≤ 2) hT hborder
  have hc : IsCompact (Complex.Rectangle ((σ : ℂ) - Complex.I * T)
      ((2 : ℂ) + Complex.I * T)) :=
    (isCompact_uIcc : IsCompact (Set.uIcc _ _)).reProdIm isCompact_uIcc
  have hf := numberFieldEntireFullQuotientContinuation_finite_zeros_compact
    (PrimeKummerField a q) (CyclotomicField q ℚ) hH hc
  have hsplit := finiteZeroResidueSum_split
    (fun s => s ∈ Complex.Rectangle ((σ : ℂ) - Complex.I * T) ((2 : ℂ) + Complex.I * T))
    (fun s => H s = 0) hf
    (fun s => (-(fullQuotientZeroMultiplicity H s : ℂ) / ((q : ℂ) - 1)) *
      ((x : ℂ) ^ s * artinGaussianMellin s))
  change (primeKummerGaussianFullSignedTrace a q x : ℂ) =
    (∑' s : {s : ℂ // s ∈ Complex.Rectangle ((σ : ℂ) - Complex.I * T)
        ((2 : ℂ) + Complex.I * T) ∧ H s = 0},
      (-(fullQuotientZeroMultiplicity H s : ℂ) / ((q : ℂ) - 1)) *
        ((x : ℂ) ^ (s : ℂ) * artinGaussianMellin s)) +
      gaussianFiniteContourRemainder H ((q : ℂ) - 1) x σ T at hr
  rw [hsplit] at hr
  have hr' := congrArg Complex.re hr
  simp only [Complex.ofReal_re, Complex.add_re] at hr'
  have hl := kummerEntireFullQuotientContinuation_leftRectangleSignedSum_le
    hH hC hx hσ (by linarith : σ ≤ 2) hT hb
  have hu := kummerEntireFullQuotientContinuation_criticalRectangleSignedSum_le
    hH hC hx (σ := σ) (T := T) hb hg
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
  have hlog : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by linarith)
  have hM := kummerGaussianZeroMassConstant_nonneg hC
  have hpos := artinGaussianConstant_pos.le
  have hp : 1 ≤ x ^ (1 - δ) := Real.one_le_rpow hx (by linarith)
  have hsmall := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (2 * artinGaussianConstant * kummerGaussianZeroMassConstant C + R) *
      (q : ℝ) * Real.log (2 * (q : ℝ)) by positivity)
  change primeKummerGaussianFullSignedTrace a q x = _ at hr'
  have htotal := hr'.le.trans (add_le_add (add_le_add hl hu) hrem)
  nlinarith only [htotal, hsmall]

end
end SimultaneousPrimitiveRoots
