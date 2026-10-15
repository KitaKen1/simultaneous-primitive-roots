module

public import SimultaneousPrimitiveRoots.QuotientDiskLogDerivative
public import SimultaneousPrimitiveRoots.Explicit.EntireZeroData
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientMultiplicity
public import SimultaneousPrimitiveRoots.Explicit.ZetaQuotientCenter

/-! Generalization of `SimultaneousPrimitiveRoots.QuotientDiskLogDerivative` from the entire zeta quotient
to abstract `EntireZeroData` (machine-copied; only declarations depending on the quotient
hypothesis are restated). -/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Explicit

open Metric Classical
noncomputable section

theorem fullQuotientDiskNormalization_zero (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H) (D : ℝ) :
    fullQuotientDiskNormalization H D 0 = 1 := by
  simp [fullQuotientDiskNormalization,
    numberFieldFullQuotientContinuation_ne_zero_two K L
      (numberFieldEntireFullQuotientContinuation_positive K L hH)]

theorem fullQuotientDiskNormalization_analytic (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H) (D : ℝ) :
    AnalyticOnNhd ℂ (fullQuotientDiskNormalization H D) Set.univ := by
  intro z _
  exact ((hH.1 _ (Set.mem_univ _)).comp
    ((analyticAt_const.add (analyticAt_const.mul analyticAt_id)))).div_const

theorem fullQuotientDiskNormalization_finite_zeros (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H)
    {D : ℝ} (hD : 0 < D) :
    (PNTAnd.DiskLogDerivative.SetOfZeros 1 (fullQuotientDiskNormalization H D)).Finite := by
  have hn := numberFieldFullQuotientContinuation_ne_zero_two K L
    (numberFieldEntireFullQuotientContinuation_positive K L hH)
  have hc := numberFieldEntireFullQuotientContinuation_finite_zeros_compact K L hH
    (isCompact_closedBall (2 : ℂ) D)
  have hi : Function.Injective (fun z : ℂ => 2 + (D : ℂ) * z) := by
    intro z w heq
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hD.ne') (add_left_cancel heq)
  apply (Set.Finite.preimage hi.injOn hc).subset
  intro z hz
  refine ⟨?_, (div_eq_zero_iff.mp hz.2).resolve_right hn⟩
  rw [mem_closedBall, dist_eq_norm]
  simp only [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hD.le]
  exact mul_le_of_le_one_right hD.le hz.1

/-- Normalize using the proved lower center bound; no residue at one is used. -/
theorem fullQuotientDiskNormalization_norm_bound (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H)
    {D M : ℝ} (hD : 0 < D)
    (hb : ∀ z ∈ sphere (2 : ℂ) D, ‖H z‖ ≤ Real.exp M)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖fullQuotientDiskNormalization H D z‖ ≤
      Real.exp (M + 4 * (Module.finrank ℚ L : ℝ)) := by
  have hc : 2 + (D : ℂ) * z ∈ closedBall (2 : ℂ) D := by
    rw [mem_closedBall, dist_eq_norm]
    simp only [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hD.le]
    exact mul_le_of_le_one_right hD.le hz
  have hp := numberFieldFullQuotientContinuation_norm_two_lower K L
    (numberFieldEntireFullQuotientContinuation_positive K L hH)
  rw [fullQuotientDiskNormalization, norm_div]
  calc ‖H (2 + (D : ℂ) * z)‖ / ‖H 2‖
      ≤ Real.exp M / Real.exp (-(4 * (Module.finrank ℚ L : ℝ))) :=
        div_le_div₀ (Real.exp_pos _).le
          (entire_norm_le_of_sphere_bound hH.1 hb hc) (Real.exp_pos _) hp
    _ = Real.exp (M + 4 * (Module.finrank ℚ L : ℝ)) := by
      rw [← Real.exp_sub]; congr 1; ring

/-- The general PNTAnd disk estimate, specialized to fixed radii. The finite
principal parts are retained; no zero-free strip or separation is assumed here. -/
theorem fullQuotientDiskNormalization_logDeriv_principal_parts_le (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H)
    {D M : ℝ} (hD : 0 < D) (hM : 0 ≤ M)
    (hb : ∀ z ∈ sphere (2 : ℂ) D, ‖H z‖ ≤ Real.exp M)
    {z : ℂ} (hz : ‖z‖ ≤ 1 / 4)
    (hn : fullQuotientDiskNormalization H D z ≠ 0) :
    let g := fullQuotientDiskNormalization H D
    let hf := fullQuotientDiskNormalization_finite_zeros K L hH hD
    ‖deriv g z / g z - ∑ ρ ∈
      (PNTAnd.DiskLogDerivative.finiteSetOfZeros_mono (by norm_num : (1 / 2 : ℝ) < 1) hf).toFinset,
      (analyticOrderNatAt g ρ : ℂ) / (z - ρ)‖ ≤
        diskLogDerivativeConstant * (1 + M + 4 * (Module.finrank ℚ L : ℝ)) := by
  let g := fullQuotientDiskNormalization H D
  let A : ℝ := 1 + M + 4 * (Module.finrank ℚ L : ℝ)
  have hA : 0 < A := by dsimp [A]; positivity
  have hbound : ∀ w : ℂ, ‖w‖ ≤ (3 / 4 : ℝ) → ‖g w‖ ≤ Real.exp A := by
    intro w hw
    apply (fullQuotientDiskNormalization_norm_bound K L hH hD hb (by linarith)).trans
    apply Real.exp_le_exp.mpr
    dsimp [A]; linarith
  have hh := PNTAnd.DiskLogDerivative.FinalBound
    (B := Real.exp A) (r' := 1 / 4) (r := 1 / 2) (R' := 5 / 8) (R := 3 / 4)
    (f := g) (z := z) (by simpa using Real.one_lt_exp_iff.mpr hA)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ((fullQuotientDiskNormalization_analytic K L hH D).mono (Set.subset_univ _))
    (fullQuotientDiskNormalization_zero K L hH D)
    (fullQuotientDiskNormalization_finite_zeros K L hH hD) hbound
    ⟨by simpa only [mem_closedBall, dist_zero_right] using hz, fun h => hn h.2⟩
  simpa only [Real.log_exp, diskLogDerivativeConstant, show (16 * (1 / 2 : ℝ) ^ 2 /
    (1 / 2 - 1 / 4) ^ 3 + 1 / (((3 / 4 : ℝ) ^ 2 / (5 / 8) - 5 / 8) *
    Real.log ((3 / 4) / (5 / 8)))) = diskLogDerivativeConstant by
      norm_num [diskLogDerivativeConstant]; ring, A, g] using hh

/-- Quantitative zero separation turns the principal-part decomposition into
an actual norm bound. The separation is an input, not inferred from nonvanishing. -/
theorem fullQuotientDiskNormalization_logDeriv_le (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H)
    {D M ε : ℝ} (hD : 0 < D) (hM : 0 ≤ M) (hε : 0 < ε)
    (hb : ∀ z ∈ sphere (2 : ℂ) D, ‖H z‖ ≤ Real.exp M)
    {z : ℂ} (hz : ‖z‖ ≤ 1 / 4)
    (hsep : ∀ ρ ∈ PNTAnd.DiskLogDerivative.SetOfZeros (1 / 2)
      (fullQuotientDiskNormalization H D), ε ≤ ‖z - ρ‖) :
    ‖deriv (fullQuotientDiskNormalization H D) z /
      fullQuotientDiskNormalization H D z‖ ≤
      (diskLogDerivativeConstant + 1 / (ε * Real.log (3 / 2))) *
        (1 + M + 4 * (Module.finrank ℚ L : ℝ)) := by
  let g := fullQuotientDiskNormalization H D
  let A : ℝ := 1 + M + 4 * (Module.finrank ℚ L : ℝ)
  let hf := fullQuotientDiskNormalization_finite_zeros K L hH hD
  let S := (PNTAnd.DiskLogDerivative.finiteSetOfZeros_mono
    (by norm_num : (1 / 2 : ℝ) < 1) hf).toFinset
  have hn : g z ≠ 0 := by
    intro hn
    have hh := hsep z ⟨by linarith, hn⟩
    exact (not_le_of_gt hε) (by simpa using hh)
  have hA : 0 < A := by dsimp [A]; positivity
  have hb' : ∀ w : ℂ, ‖w‖ ≤ (3 / 4 : ℝ) → ‖g w‖ ≤ Real.exp A := by
    intro w hw
    apply (fullQuotientDiskNormalization_norm_bound K L hH hD hb (by linarith)).trans
    apply Real.exp_le_exp.mpr
    dsimp [A]; linarith
  have hcount := PNTAnd.DiskLogDerivative.ZerosBound
    (B := Real.exp A) (r := 1 / 2) (R := 3 / 4) (f := g)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ((fullQuotientDiskNormalization_analytic K L hH D).mono (Set.subset_univ _))
    (fullQuotientDiskNormalization_zero K L hH D) hf hb'
  have hsum : ‖∑ ρ ∈ S, (analyticOrderNatAt g ρ : ℂ) / (z - ρ)‖ ≤
      A / (ε * Real.log (3 / 2)) := by
    calc ‖∑ ρ ∈ S, (analyticOrderNatAt g ρ : ℂ) / (z - ρ)‖
        ≤ ∑ ρ ∈ S, ‖(analyticOrderNatAt g ρ : ℂ) / (z - ρ)‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ S, (analyticOrderNatAt g ρ : ℝ) / ε := by
        apply Finset.sum_le_sum
        intro ρ hρ
        rw [norm_div, Complex.norm_natCast]
        exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) hε
          (hsep ρ ((PNTAnd.DiskLogDerivative.finiteSetOfZeros_mono
            (by norm_num : (1 / 2 : ℝ) < 1) hf).mem_toFinset.mp hρ))
      _ = (∑ ρ ∈ S, (analyticOrderNatAt g ρ : ℝ)) / ε := by rw [Finset.sum_div]
      _ ≤ (1 / Real.log (3 / 2) * A) / ε := by
        apply div_le_div_of_nonneg_right _ hε.le
        simpa only [Real.log_exp, show ((3 / 4 : ℝ) / (1 / 2)) = 3 / 2 by norm_num,
          Nat.cast_sum] using hcount
      _ = A / (ε * Real.log (3 / 2)) := by ring
  have hp := fullQuotientDiskNormalization_logDeriv_principal_parts_le K L hH hD hM hb hz hn
  change ‖deriv g z / g z - ∑ ρ ∈ S, (analyticOrderNatAt g ρ : ℂ) / (z - ρ)‖ ≤
    diskLogDerivativeConstant * A at hp
  calc ‖deriv g z / g z‖
      ≤ ‖deriv g z / g z - ∑ ρ ∈ S, (analyticOrderNatAt g ρ : ℂ) / (z - ρ)‖ +
        ‖∑ ρ ∈ S, (analyticOrderNatAt g ρ : ℂ) / (z - ρ)‖ := norm_le_norm_sub_add _ _
    _ ≤ diskLogDerivativeConstant * A + A / (ε * Real.log (3 / 2)) := add_le_add hp hsum
    _ = (diskLogDerivativeConstant + 1 / (ε * Real.log (3 / 2))) * A := by ring

theorem fullQuotientDiskNormalization_logDeriv_scale (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H)
    (D : ℝ) {z : ℂ} (hn : H (2 + D * z) ≠ 0) :
    deriv (fullQuotientDiskNormalization H D) z /
      fullQuotientDiskNormalization H D z =
        (D : ℂ) * (deriv H (2 + D * z) / H (2 + D * z)) := by
  have htwo := numberFieldFullQuotientContinuation_ne_zero_two K L
    (numberFieldEntireFullQuotientContinuation_positive K L hH)
  have hd := ((hH.1 _ (Set.mem_univ _)).differentiableAt.hasDerivAt.comp z
    (((hasDerivAt_id z).const_mul (D : ℂ)).const_add (2 : ℂ))).div_const (H 2)
  rw [show deriv (fullQuotientDiskNormalization H D) z =
    deriv H (2 + D * z) * D / H 2 from by
      change deriv (fun w : ℂ => H (2 + D * w) / H 2) z = _
      simpa only [fullQuotientDiskNormalization, Function.comp_def, id_eq, mul_one] using hd.deriv]
  dsimp only [fullQuotientDiskNormalization]
  field_simp [htwo, hn]

/-- A bound on the actual logarithmic derivative from disk growth and
quantitative separation from actual zeros. No artificial zero list is used. -/
theorem numberFieldEntireFullQuotientContinuation_logDeriv_le_of_separation (K L : Type*)
    [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : EntireZeroData K L H)
    {D M ε : ℝ} (hD : 0 < D) (hM : 0 ≤ M) (hε : 0 < ε)
    (hb : ∀ z ∈ sphere (2 : ℂ) D, ‖H z‖ ≤ Real.exp M)
    {s : ℂ} (hs : ‖s - 2‖ ≤ D / 4)
    (hsep : ∀ ρ ∈ closedBall (2 : ℂ) (D / 2), H ρ = 0 → ε * D ≤ ‖s - ρ‖) :
    ‖deriv H s / H s‖ ≤
      (diskLogDerivativeConstant + 1 / (ε * Real.log (3 / 2))) *
        (1 + M + 4 * (Module.finrank ℚ L : ℝ)) / D := by
  let z : ℂ := (s - 2) / D
  have hDc : (D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD.ne'
  have hz : ‖z‖ ≤ 1 / 4 := by
    dsimp [z]
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hD.le, div_le_iff₀ hD]
    linarith
  have hs_eq : 2 + (D : ℂ) * z = s := by dsimp [z]; field_simp; ring
  have hsep' : ∀ ρ ∈ PNTAnd.DiskLogDerivative.SetOfZeros (1 / 2)
      (fullQuotientDiskNormalization H D), ε ≤ ‖z - ρ‖ := by
    intro ρ hρ
    have hρball : 2 + (D : ℂ) * ρ ∈ closedBall (2 : ℂ) (D / 2) := by
      rw [mem_closedBall, dist_eq_norm]
      simp only [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg hD.le]
      nlinarith [hρ.1]
    have hnρ : H (2 + (D : ℂ) * ρ) = 0 := by
      have htwo := numberFieldFullQuotientContinuation_ne_zero_two K L
        (numberFieldEntireFullQuotientContinuation_positive K L hH)
      exact (div_eq_zero_iff.mp hρ.2).resolve_right htwo
    have hh := hsep (2 + (D : ℂ) * ρ) hρball hnρ
    have heq : s - (2 + (D : ℂ) * ρ) = (D : ℂ) * (z - ρ) := by rw [← hs_eq]; ring
    rw [heq, norm_mul, Complex.norm_real, Real.norm_of_nonneg hD.le] at hh
    nlinarith
  have hn : H s ≠ 0 := by
    intro hn
    have hh := hsep s (by rw [mem_closedBall, dist_eq_norm]; linarith) hn
    simp only [sub_self, norm_zero] at hh
    have := mul_pos hε hD
    linarith
  have hh := fullQuotientDiskNormalization_logDeriv_le K L hH hD hM hε hb hz hsep'
  rw [fullQuotientDiskNormalization_logDeriv_scale K L hH D (by rwa [hs_eq]), hs_eq,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg hD.le] at hh
  exact (le_div_iff₀ hD).mpr (by simpa only [mul_comm] using hh)

end
end SimultaneousPrimitiveRoots.Explicit
