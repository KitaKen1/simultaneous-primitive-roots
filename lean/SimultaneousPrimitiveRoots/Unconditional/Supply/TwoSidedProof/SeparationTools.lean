module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.CircleTools
public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Tools for the separation of the comparison correlations

The analytic and combinatorial parts of the proof of `SeparationLink d H 𝔅`
(`[P-06:0391–0415]`, `[PUB-tex:0487–0495]`, `TwoSidedProof/SeparationProof.lean`).

* `Separation.phase v s = e^{ivs}`: `t^{iv} = phase v (log t)` for `t > 0` (`cpow_eq_phase`).
* `norm_sum_integral_phase_le`: for a density `wd` with `|wd(v)| (1 + |v|)^{N+2} ≤ C_wd` and a
  finite combination `Φ(v) = ∑_i c_i e^{iv s_i}` with `|Φ| ≤ B₁` on `|v| ≤ L` and `|Φ| ≤ B₂`
  everywhere, `|∑_i c_i ∫ wd(v) e^{iv s_i} dv| ≤ (B₁ + B₂ L^{-N}) C_wd π`: "These estimates also
  bound the separated Fourier tails absolutely … Smooth Fourier decay can therefore give any
  required precision."
* `norm_twisted_le`: the separation of `Ψ(w/(x D_A D_B))/w` by the Mellin density: the phases
  `x^{-iv}`, `D_A^{-iv}`, `D_B^{-iv}` go to the two tests and `w^{iv}` to the first endpoint.
* `norm_bilinear_le`: the trivial bound of a bilinear sum by the two square sums (Parseval).
* `exists_cutoffs`: "Insert fixed smooth cutoffs at scale `Y` at both endpoints": smooth `ψ₁`,
  `ψ₂` supported in `[c₁/2, c₂ + 1]` with `ψ₁(u) = 1/u` and `ψ₂(u) = 1` on `[c₁, c₂]`, and bounds
  for all their derivatives; `le_rpow_max_log`: such bounds are powers of `L` for `L ≥ e`.
* `cut_range`: where the two cutoffs are evaluated.
* `sum_addChar_range`, `exists_char_coeff`: a function on `ℤ/H` with values in `[-1, 1]` is a
  combination of the `H` characters `e(jw/H)` with coefficients of modulus at most one
  (`[PUB-tex:0492–0494]`); `residue_expansion`, `norm_residue_sum_le`: "Partition each free tuple
  by its residue modulo `H`."
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open MeasureTheory
open scoped ContDiff SchwartzMap

noncomputable section

namespace Separation

/-! ### The phase -/

/-- The phase `e^{ivs}`. -/
def phase (v s : ℝ) : ℂ := Complex.exp (((v * s : ℝ) : ℂ) * Complex.I)

theorem norm_phase (v s : ℝ) : ‖phase v s‖ = 1 := by
  unfold phase
  exact Complex.norm_exp_ofReal_mul_I _

theorem phase_add (v s s' : ℝ) : phase v (s + s') = phase v s * phase v s' := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem continuous_phase (s : ℝ) : Continuous fun v : ℝ => phase v s := by
  unfold phase
  fun_prop

/-- `t^{iv} = e^{iv log t}` for `t > 0`. -/
theorem cpow_eq_phase {t : ℝ} (ht : 0 < t) (v : ℝ) :
    (t : ℂ) ^ ((v : ℂ) * Complex.I) = phase v (Real.log t) := by
  unfold phase
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'), ← Complex.ofReal_log ht.le]
  congr 1
  push_cast
  ring

/-- `w^{iv} = e^{iv log w}` for a positive integer `w`. -/
theorem natCast_cpow_eq_phase {w : ℕ} (hw : 0 < w) (v : ℝ) :
    (w : ℂ) ^ ((v : ℂ) * Complex.I) = phase v (Real.log w) := by
  rw [← Complex.ofReal_natCast]
  exact cpow_eq_phase (Nat.cast_pos.mpr hw) v

/-! ### A Mellin integral with a tail -/

/-- **A Mellin integral with a tail**: if `|wd(v)| (1 + |v|)^{N+2} ≤ C_wd`, and the combination
`Φ(v) = ∑_i c_i e^{iv s_i}` satisfies `|Φ| ≤ B₁` on `|v| ≤ L` and `|Φ| ≤ B₂` everywhere, then
`|∑_i c_i ∫ wd(v) e^{iv s_i} dv| ≤ (B₁ + B₂ L^{-N}) C_wd π`. -/
theorem norm_sum_integral_phase_le {ι : Type*} (T : Finset ι) (cf : ι → ℂ) (c : ι → ℝ)
    {wd : ℝ → ℂ} (hwd : Continuous wd) {N : ℕ} {Cwd : ℝ}
    (hdecay : ∀ v, ‖wd v‖ * (1 + |v|) ^ (N + 2) ≤ Cwd) {L B₁ B₂ : ℝ} (hL : 1 ≤ L)
    (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hlow : ∀ v, |v| ≤ L → ‖∑ i ∈ T, cf i * phase v (c i)‖ ≤ B₁)
    (hall : ∀ v, ‖∑ i ∈ T, cf i * phase v (c i)‖ ≤ B₂) :
    ‖∑ i ∈ T, cf i * ∫ v, wd v * phase v (c i)‖ ≤ (B₁ + B₂ * (L ^ N)⁻¹) * (Cwd * Real.pi) := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hLN : 0 < L ^ N := pow_pos hL0 N
  have hLi0 : 0 ≤ (L ^ N)⁻¹ := inv_nonneg.mpr hLN.le
  have hCwd0 : 0 ≤ Cwd := by
    have h0 := hdecay 0
    rw [abs_zero, add_zero, one_pow, mul_one] at h0
    exact (norm_nonneg _).trans h0
  -- the decay of the density
  have hsq : ∀ v : ℝ, 1 + v ^ 2 ≤ (1 + |v|) ^ 2 := fun v => by
    nlinarith [sq_abs v, abs_nonneg v]
  have hwd1 : ∀ v, ‖wd v‖ ≤ Cwd * (1 + v ^ 2)⁻¹ := by
    intro v
    have hv : (0 : ℝ) ≤ |v| := abs_nonneg v
    have h1 : (1 : ℝ) ≤ (1 + |v|) ^ N := one_le_pow₀ (by linarith)
    have h3 : 1 + v ^ 2 ≤ (1 + |v|) ^ (N + 2) := by
      rw [pow_add]
      calc 1 + v ^ 2 ≤ (1 + |v|) ^ 2 := hsq v
        _ = 1 * (1 + |v|) ^ 2 := (one_mul _).symm
        _ ≤ (1 + |v|) ^ N * (1 + |v|) ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    have hpos : 0 < 1 + v ^ 2 := by positivity
    have h4 : ‖wd v‖ * (1 + v ^ 2) ≤ Cwd :=
      (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)).trans (hdecay v)
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    exact h4
  have hwd2 : ∀ v, L < |v| → ‖wd v‖ ≤ Cwd * (L ^ N)⁻¹ * (1 + v ^ 2)⁻¹ := by
    intro v hv
    have h1 : L ^ N ≤ (1 + |v|) ^ N := pow_le_pow_left₀ hL0.le (by linarith) N
    have hp2 : (0 : ℝ) ≤ 1 + v ^ 2 := by positivity
    have h3 : L ^ N * (1 + v ^ 2) ≤ (1 + |v|) ^ (N + 2) := by
      rw [pow_add]
      exact mul_le_mul h1 (hsq v) hp2 (pow_nonneg (by linarith) N)
    have hpos : 0 < L ^ N * (1 + v ^ 2) := mul_pos hLN (by positivity)
    have h4 : ‖wd v‖ * (L ^ N * (1 + v ^ 2)) ≤ Cwd :=
      (mul_le_mul_of_nonneg_left h3 (norm_nonneg _)).trans (hdecay v)
    have h5 : Cwd * (L ^ N)⁻¹ * (1 + v ^ 2)⁻¹ = Cwd / (L ^ N * (1 + v ^ 2)) := by
      rw [div_eq_mul_inv, mul_inv, mul_assoc]
    rw [h5, le_div_iff₀ hpos]
    exact h4
  -- integrability
  have hwdint : ∀ s : ℝ, Integrable (fun v => wd v * phase v s) := fun s =>
    Integrable.mono' (integrable_inv_one_add_sq.const_mul Cwd)
      (hwd.mul (continuous_phase s)).aestronglyMeasurable
      (ae_of_all _ fun v => by
        show ‖wd v * phase v s‖ ≤ Cwd * (1 + v ^ 2)⁻¹
        rw [norm_mul, norm_phase, mul_one]
        exact hwd1 v)
  -- the combination under the integral
  have hkey : ∑ i ∈ T, cf i * ∫ v, wd v * phase v (c i) =
      ∫ v, wd v * ∑ i ∈ T, cf i * phase v (c i) := by
    have h1 : ∀ i ∈ T, cf i * ∫ v, wd v * phase v (c i) =
        ∫ v, cf i * (wd v * phase v (c i)) := fun i _ => by rw [integral_const_mul]
    rw [Finset.sum_congr rfl h1,
      ← integral_finsetSum T fun i _ => (hwdint (c i)).const_mul (cf i)]
    refine integral_congr_ae (ae_of_all _ fun v => ?_)
    show ∑ i ∈ T, cf i * (wd v * phase v (c i)) = wd v * ∑ i ∈ T, cf i * phase v (c i)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hkey]
  have hbound : ∀ v, ‖wd v * ∑ i ∈ T, cf i * phase v (c i)‖ ≤
      (B₁ + B₂ * (L ^ N)⁻¹) * Cwd * (1 + v ^ 2)⁻¹ := by
    intro v
    have hinv0 : 0 ≤ (1 + v ^ 2)⁻¹ := inv_nonneg.mpr (by positivity)
    rw [norm_mul]
    rcases le_or_gt |v| L with hv | hv
    · have h : 0 ≤ B₂ * (L ^ N)⁻¹ * Cwd * (1 + v ^ 2)⁻¹ :=
        mul_nonneg (mul_nonneg (mul_nonneg hB₂ hLi0) hCwd0) hinv0
      calc ‖wd v‖ * ‖∑ i ∈ T, cf i * phase v (c i)‖ ≤ Cwd * (1 + v ^ 2)⁻¹ * B₁ :=
            mul_le_mul (hwd1 v) (hlow v hv) (norm_nonneg _) (mul_nonneg hCwd0 hinv0)
        _ ≤ (B₁ + B₂ * (L ^ N)⁻¹) * Cwd * (1 + v ^ 2)⁻¹ := by linarith
    · have h : 0 ≤ B₁ * Cwd * (1 + v ^ 2)⁻¹ := mul_nonneg (mul_nonneg hB₁ hCwd0) hinv0
      calc ‖wd v‖ * ‖∑ i ∈ T, cf i * phase v (c i)‖ ≤ Cwd * (L ^ N)⁻¹ * (1 + v ^ 2)⁻¹ * B₂ :=
            mul_le_mul (hwd2 v hv) (hall v) (norm_nonneg _)
              (mul_nonneg (mul_nonneg hCwd0 hLi0) hinv0)
        _ ≤ (B₁ + B₂ * (L ^ N)⁻¹) * Cwd * (1 + v ^ 2)⁻¹ := by linarith
  have hgint : Integrable (fun v : ℝ => (B₁ + B₂ * (L ^ N)⁻¹) * Cwd * (1 + v ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul _
  calc ‖∫ v, wd v * ∑ i ∈ T, cf i * phase v (c i)‖
      ≤ ∫ v, (B₁ + B₂ * (L ^ N)⁻¹) * Cwd * (1 + v ^ 2)⁻¹ :=
        norm_integral_le_of_norm_le hgint (ae_of_all _ hbound)
    _ = (B₁ + B₂ * (L ^ N)⁻¹) * (Cwd * Real.pi) := by
        rw [integral_const_mul, integral_univ_inv_one_add_sq, mul_assoc]

/-- **The separation of the cutoff** (`[P-06:0391–0396]`): "Fourier inversion in logarithmic size
separates `Ψ(w/(x D_A D_B))/w` as in (cor:insertion-separation). After a factor `1/Y`, it is
enough to estimate combinations of (cor:comparison-sum)".

`Uv v` is the first sequence with the twist `w^{iv}` (`hU`), `tgt` the terms of the correlation
(`htgt`: the two cutoffs are `Y/w` and `1` where `Ψ(w/(xD))` and the tests do not vanish). The
hypotheses `hlow`, `hall` bound the bilinear sums with the tests `β₁ D_A^{-iv}`, `β₂ D_B^{-iv}`
for `|v| ≤ L` and for all `v`. -/
theorem norm_twisted_le {R : Type*} [Fintype R] (wt : R → ℝ) (β₁ β₂ : R → ℂ)
    (DA DB Dr : R → ℕ) (hDA : ∀ r, 0 < DA r) (hDB : ∀ r, 0 < DB r)
    (hD : ∀ r, Dr r = DA r * DB r) (sw : Finset ℕ) (hsw : ∀ w ∈ sw, 0 < w) {x Y : ℝ}
    (hx : 0 < x) (hY : 0 < Y) {Ψ wd : ℝ → ℂ} (hwd : Continuous wd) {N : ℕ} {Cwd : ℝ}
    (hdecay : ∀ v, ‖wd v‖ * (1 + |v|) ^ (N + 2) ≤ Cwd)
    (hinv : ∀ t : ℝ, 0 < t → Ψ t = ∫ v, wd v * (t : ℂ) ^ ((v : ℂ) * Complex.I))
    (Uv : ℝ → ℕ → ℂ) (pre V : ℕ → ℂ) (tgt : R → ℕ → ℂ)
    (hU : ∀ v, ∀ w ∈ sw, Uv v w = pre w * (w : ℂ) ^ ((v : ℂ) * Complex.I))
    (htgt : ∀ r, ∀ w ∈ sw, β₁ r * β₂ r * (pre w * V (w + Dr r)) *
        Ψ ((w : ℝ) / (x * (Dr r : ℝ))) = (Y : ℂ) * (β₁ r * β₂ r * tgt r w))
    {L B₁ B₂ : ℝ} (hL : 1 ≤ L) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hlow : ∀ v, |v| ≤ L → ‖∑ r, ((wt r : ℝ) : ℂ) *
        (β₁ r * phase v (-Real.log (DA r)) * (β₂ r * phase v (-Real.log (DB r)))) *
        ∑ w ∈ sw, Uv v w * V (w + Dr r)‖ ≤ B₁)
    (hall : ∀ v, ‖∑ r, ((wt r : ℝ) : ℂ) *
        (β₁ r * phase v (-Real.log (DA r)) * (β₂ r * phase v (-Real.log (DB r)))) *
        ∑ w ∈ sw, Uv v w * V (w + Dr r)‖ ≤ B₂) :
    ‖∑ r, ((wt r : ℝ) : ℂ) * (β₁ r * β₂ r) * ∑ w ∈ sw, tgt r w‖ ≤
      Y⁻¹ * ((B₁ + B₂ * (L ^ N)⁻¹) * (Cwd * Real.pi)) := by
  -- the positions and the coefficients
  have hpos : ∀ r, ∀ w ∈ sw, 0 < (w : ℝ) / (x * (Dr r : ℝ)) := fun r w hw =>
    div_pos (Nat.cast_pos.mpr (hsw w hw))
      (mul_pos hx (Nat.cast_pos.mpr (by rw [hD r]; exact Nat.mul_pos (hDA r) (hDB r))))
  have hphase : ∀ (v : ℝ) (r : R), ∀ w ∈ sw,
      phase v (Real.log ((w : ℝ) / (x * (Dr r : ℝ)))) =
        phase v (-Real.log x) * phase v (-Real.log (DA r)) * phase v (-Real.log (DB r)) *
          phase v (Real.log w) := by
    intro v r w hw
    have hw0 : (w : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hsw w hw)).ne'
    have hA0 : (DA r : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hDA r)).ne'
    have hB0 : (DB r : ℝ) ≠ 0 := (Nat.cast_pos.mpr (hDB r)).ne'
    have e : Real.log ((w : ℝ) / (x * (Dr r : ℝ))) =
        -Real.log x + -Real.log (DA r) + -Real.log (DB r) + Real.log w := by
      rw [hD r, Nat.cast_mul, Real.log_div hw0 (mul_ne_zero hx.ne' (mul_ne_zero hA0 hB0)),
        Real.log_mul hx.ne' (mul_ne_zero hA0 hB0), Real.log_mul hA0 hB0]
      ring
    rw [e, phase_add, phase_add, phase_add]
  have hstep : ∀ v : ℝ, phase v (-Real.log x) * ∑ r, ((wt r : ℝ) : ℂ) *
        (β₁ r * phase v (-Real.log (DA r)) * (β₂ r * phase v (-Real.log (DB r)))) *
        ∑ w ∈ sw, Uv v w * V (w + Dr r) =
      ∑ i ∈ (Finset.univ : Finset R) ×ˢ sw,
        ((wt i.1 : ℝ) : ℂ) * (β₁ i.1 * β₂ i.1) * (pre i.2 * V (i.2 + Dr i.1)) *
          phase v (Real.log ((i.2 : ℝ) / (x * (Dr i.1 : ℝ)))) := by
    intro v
    have hterm : ∀ r, ∀ w ∈ sw, phase v (-Real.log x) * (((wt r : ℝ) : ℂ) *
          (β₁ r * phase v (-Real.log (DA r)) * (β₂ r * phase v (-Real.log (DB r)))) *
          (Uv v w * V (w + Dr r))) =
        ((wt r : ℝ) : ℂ) * (β₁ r * β₂ r) * (pre w * V (w + Dr r)) *
          phase v (Real.log ((w : ℝ) / (x * (Dr r : ℝ)))) := by
      intro r w hw
      rw [hU v w hw, natCast_cpow_eq_phase (hsw w hw) v, hphase v r w hw]
      ring
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w hw => hterm r w hw
  have hlow' : ∀ v, |v| ≤ L → ‖∑ i ∈ (Finset.univ : Finset R) ×ˢ sw,
      ((wt i.1 : ℝ) : ℂ) * (β₁ i.1 * β₂ i.1) * (pre i.2 * V (i.2 + Dr i.1)) *
        phase v (Real.log ((i.2 : ℝ) / (x * (Dr i.1 : ℝ))))‖ ≤ B₁ := fun v hv => by
    rw [← hstep v, norm_mul, norm_phase, one_mul]
    exact hlow v hv
  have hall' : ∀ v, ‖∑ i ∈ (Finset.univ : Finset R) ×ˢ sw,
      ((wt i.1 : ℝ) : ℂ) * (β₁ i.1 * β₂ i.1) * (pre i.2 * V (i.2 + Dr i.1)) *
        phase v (Real.log ((i.2 : ℝ) / (x * (Dr i.1 : ℝ))))‖ ≤ B₂ := fun v => by
    rw [← hstep v, norm_mul, norm_phase, one_mul]
    exact hall v
  have hmain : ‖∑ i ∈ (Finset.univ : Finset R) ×ˢ sw,
        ((wt i.1 : ℝ) : ℂ) * (β₁ i.1 * β₂ i.1) * (pre i.2 * V (i.2 + Dr i.1)) *
          ∫ v, wd v * phase v (Real.log ((i.2 : ℝ) / (x * (Dr i.1 : ℝ))))‖ ≤
      (B₁ + B₂ * (L ^ N)⁻¹) * (Cwd * Real.pi) :=
    norm_sum_integral_phase_le ((Finset.univ : Finset R) ×ˢ sw)
      (fun i => ((wt i.1 : ℝ) : ℂ) * (β₁ i.1 * β₂ i.1) * (pre i.2 * V (i.2 + Dr i.1)))
      (fun i => Real.log ((i.2 : ℝ) / (x * (Dr i.1 : ℝ)))) hwd hdecay hL hB₁ hB₂ hlow' hall'
  -- the Mellin inversion
  have hsum : ∑ i ∈ (Finset.univ : Finset R) ×ˢ sw,
        ((wt i.1 : ℝ) : ℂ) * (β₁ i.1 * β₂ i.1) * (pre i.2 * V (i.2 + Dr i.1)) *
          ∫ v, wd v * phase v (Real.log ((i.2 : ℝ) / (x * (Dr i.1 : ℝ)))) =
      (Y : ℂ) * ∑ r, ((wt r : ℝ) : ℂ) * (β₁ r * β₂ r) * ∑ w ∈ sw, tgt r w := by
    have hterm : ∀ r, ∀ w ∈ sw, ((wt r : ℝ) : ℂ) * (β₁ r * β₂ r) * (pre w * V (w + Dr r)) *
          ∫ v, wd v * phase v (Real.log ((w : ℝ) / (x * (Dr r : ℝ)))) =
        (Y : ℂ) * (((wt r : ℝ) : ℂ) * (β₁ r * β₂ r) * tgt r w) := by
      intro r w hw
      have hfun : (fun v : ℝ => wd v * phase v (Real.log ((w : ℝ) / (x * (Dr r : ℝ))))) =
          fun v : ℝ => wd v * (((w : ℝ) / (x * (Dr r : ℝ)) : ℝ) : ℂ) ^ ((v : ℂ) * Complex.I) :=
        funext fun v => by rw [cpow_eq_phase (hpos r w hw) v]
      have hΨ : ∫ v, wd v * phase v (Real.log ((w : ℝ) / (x * (Dr r : ℝ)))) =
          Ψ ((w : ℝ) / (x * (Dr r : ℝ))) := by
        rw [hfun]
        exact (hinv _ (hpos r w hw)).symm
      rw [hΨ]
      linear_combination ((wt r : ℝ) : ℂ) * htgt r w hw
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w hw => hterm r w hw
  rw [hsum, norm_mul, Complex.norm_real, Real.norm_of_nonneg hY.le] at hmain
  exact (le_inv_mul_iff₀ hY).mpr hmain

/-! ### The trivial bound -/

/-- **The trivial bound of a bilinear sum** by the two square sums (Parseval and Cauchy). -/
theorem norm_bilinear_le {R : Type*} [Fintype R] (wt : R → ℝ) (hwt0 : ∀ r, 0 ≤ wt r)
    (hwt1 : ∑ r, wt r ≤ 1) (β : R → ℂ) (hβ : ∀ r, ‖β r‖ ≤ 1) (Dr : R → ℕ) (s : Finset ℕ)
    {U V : ℕ → ℂ} (hU : ∀ w, U w ≠ 0 → w ∈ s) (hV : ∀ v, V v ≠ 0 → v ∈ s) {EU EV : ℝ}
    (hEU : ∑ᶠ w : ℕ, ‖U w‖ ^ 2 ≤ EU) (hEV : ∑ᶠ v : ℕ, ‖V v‖ ^ 2 ≤ EV) :
    ‖∑ r, ((wt r : ℝ) : ℂ) * β r * ∑ᶠ w : ℕ, U w * V (w + Dr r)‖ ≤ (EU + EV) / 2 := by
  have key : ∑ r, ((wt r : ℝ) : ℂ) * β r * ∑ᶠ w : ℕ, U w * V (w + Dr r) =
      ∫ θ in (0 : ℝ)..1, CircleMethod.trigSum s U θ * CircleMethod.trigSum s V (-θ) *
        ∑ r, ((wt r : ℝ) : ℂ) * β r * addChar (θ * (Dr r : ℝ)) :=
    CircleMethod.sum_mul_finsum_eq_integral s s hU hV (fun r => ((wt r : ℝ) : ℂ) * β r) Dr
  rw [key]
  have hm1 : ∀ θ : ℝ, ‖∑ r, ((wt r : ℝ) : ℂ) * β r * addChar (θ * (Dr r : ℝ))‖ ≤ 1 := by
    intro θ
    refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun r _ => ?_) hwt1)
    rw [norm_mul, norm_mul, EndpointProof.norm_addChar, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (hwt0 r)]
    exact mul_le_of_le_one_right (hwt0 r) (hβ r)
  have hmc : Continuous fun θ : ℝ => ∑ r, ((wt r : ℝ) : ℂ) * β r * addChar (θ * (Dr r : ℝ)) :=
    continuous_finsetSum _ fun r _ =>
      continuous_const.mul (CircleMethod.continuous_addChar_mul _)
  have hEP : ∫ θ in (0 : ℝ)..1, ‖CircleMethod.trigSum s U θ‖ ^ 2 ≤ EU := by
    have h := CircleMethod.integral_normSq_trigSum s U 0
    rw [zero_add] at h
    rw [h, CircleMethod.sum_normSq_eq_finsum hU]
    exact hEU
  have hEQ : ∀ a : ℝ, ∫ θ in a..(a + 1), ‖CircleMethod.trigSum s V (-θ)‖ ^ 2 ≤ EV := fun a => by
    rw [CircleMethod.integral_normSq_trigSum_neg s V a, CircleMethod.sum_normSq_eq_finsum hV]
    exact hEV
  have h := CircleMethod.norm_integral_circle_le (∅ : Finset Unit) (fun _ => (0 : ℝ))
    (δ := 0) (ε := 1) (lam := 1) (EA := 0) le_rfl (by norm_num) zero_le_one one_pos
    (CircleMethod.continuous_trigSum s U) (CircleMethod.continuous_trigSum_neg s V) hmc hm1
    (fun θ _ => Or.inl (hm1 θ)) hEP hEQ (fun i hi => absurd hi (Finset.notMem_empty i))
  rw [Finset.card_empty, Nat.cast_zero, zero_mul, add_zero, one_mul] at h
  exact h

/-! ### The cutoffs -/

/-- The real cutoff: `1` on `[c₁, c₂]` and `0` outside `(c₁/2, c₂ + 1)`. -/
def bump (c₁ c₂ : ℝ) (u : ℝ) : ℝ :=
  Real.smoothTransition ((u - c₁ / 2) / (c₁ / 2)) * Real.smoothTransition (c₂ + 1 - u)

theorem contDiff_bump (c₁ c₂ : ℝ) : ContDiff ℝ ∞ (bump c₁ c₂) := by
  have h1 : ContDiff ℝ ∞ (fun u : ℝ => (u - c₁ / 2) / (c₁ / 2)) :=
    (contDiff_id.sub contDiff_const).div_const _
  have h2 : ContDiff ℝ ∞ (fun u : ℝ => c₂ + 1 - u) := contDiff_const.sub contDiff_id
  exact (Real.smoothTransition.contDiff.comp h1).mul (Real.smoothTransition.contDiff.comp h2)

theorem bump_eq_zero_of_le {c₁ c₂ u : ℝ} (hc₁ : 0 < c₁) (hu : u ≤ c₁ / 2) :
    bump c₁ c₂ u = 0 := by
  have ha : (u - c₁ / 2) / (c₁ / 2) ≤ 0 := by
    rw [div_le_iff₀ (by linarith), zero_mul]
    linarith
  unfold bump
  rw [Real.smoothTransition.zero_of_nonpos ha, zero_mul]

theorem bump_eq_zero_of_ge {c₁ c₂ u : ℝ} (hu : c₂ + 1 ≤ u) : bump c₁ c₂ u = 0 := by
  have ha : c₂ + 1 - u ≤ 0 := by linarith
  unfold bump
  rw [Real.smoothTransition.zero_of_nonpos ha, mul_zero]

theorem bump_eq_one {c₁ c₂ u : ℝ} (hc₁ : 0 < c₁) (h1 : c₁ ≤ u) (h2 : u ≤ c₂) :
    bump c₁ c₂ u = 1 := by
  have ha : 1 ≤ (u - c₁ / 2) / (c₁ / 2) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hb : 1 ≤ c₂ + 1 - u := by linarith
  unfold bump
  rw [Real.smoothTransition.one_of_one_le ha, Real.smoothTransition.one_of_one_le hb, mul_one]

/-- The derivatives of a smooth compactly supported function are bounded. -/
theorem exists_iteratedDeriv_bound {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) :
    ∃ B : ℕ → ℝ, ∀ (j : ℕ) (u : ℝ), ‖iteratedDeriv j ψ u‖ ≤ B j := by
  refine ⟨fun j => SchwartzMap.seminorm ℝ 0 j (hc.toSchwartzMap hψ), fun j u => ?_⟩
  have h := SchwartzMap.le_seminorm' ℝ 0 j (hc.toSchwartzMap hψ) u
  rw [pow_zero, one_mul] at h
  exact h

/-- **The two cutoffs** (`[P-06:0391–0392]`): "Insert fixed smooth cutoffs at scale `Y` at both
endpoints." `ψ₁(u) = 1/u` and `ψ₂(u) = 1` on `[c₁, c₂]`; both are smooth, supported in
`[c₁/2, c₂ + 1]`, with bounded derivatives of every order. -/
theorem exists_cutoffs {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) :
    ∃ (ψ₁ ψ₂ : ℝ → ℂ) (B : ℕ → ℝ), ContDiff ℝ ∞ ψ₁ ∧ ContDiff ℝ ∞ ψ₂ ∧
      Function.support ψ₁ ⊆ Set.Icc (c₁ / 2) (c₂ + 1) ∧
      Function.support ψ₂ ⊆ Set.Icc (c₁ / 2) (c₂ + 1) ∧
      (∀ (j : ℕ) (u : ℝ), ‖iteratedDeriv j ψ₁ u‖ ≤ B j) ∧
      (∀ (j : ℕ) (u : ℝ), ‖iteratedDeriv j ψ₂ u‖ ≤ B j) ∧
      ∀ u : ℝ, c₁ ≤ u → u ≤ c₂ → ψ₁ u = ((u⁻¹ : ℝ) : ℂ) ∧ ψ₂ u = 1 := by
  have hb : ContDiff ℝ ∞ (bump c₁ c₂) := contDiff_bump c₁ c₂
  have hzero : ∀ u : ℝ, u ∉ Set.Icc (c₁ / 2) (c₂ + 1) → bump c₁ c₂ u = 0 := by
    intro u hu
    by_cases h1 : u ≤ c₁ / 2
    · exact bump_eq_zero_of_le hc₁ h1
    · by_cases h2 : c₂ + 1 ≤ u
      · exact bump_eq_zero_of_ge h2
      · exact absurd ⟨le_of_lt (not_le.mp h1), le_of_lt (not_le.mp h2)⟩ hu
  have hq : ContDiff ℝ ∞ (fun u : ℝ => bump c₁ c₂ u / u) := by
    rw [contDiff_iff_contDiffAt]
    intro u
    by_cases hu : u < c₁ / 2
    · have h : (fun u : ℝ => bump c₁ c₂ u / u) =ᶠ[nhds u] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds hu] with y hy
        show bump c₁ c₂ y / y = 0
        rw [bump_eq_zero_of_le hc₁ (le_of_lt hy), zero_div]
      exact contDiffAt_const.congr_of_eventuallyEq h
    · have hu0 : u ≠ 0 := by
        rw [not_lt] at hu
        have hpos : 0 < u := lt_of_lt_of_le (by linarith) hu
        exact hpos.ne'
      exact hb.contDiffAt.div contDiffAt_id hu0
  -- the complex cutoffs
  have hψ₁' : ContDiff ℝ ∞ (fun u : ℝ => Complex.ofRealCLM (bump c₁ c₂ u / u)) :=
    Complex.ofRealCLM.contDiff.comp hq
  have hψ₂' : ContDiff ℝ ∞ (fun u : ℝ => Complex.ofRealCLM (bump c₁ c₂ u)) :=
    Complex.ofRealCLM.contDiff.comp hb
  have hψ₁ : ContDiff ℝ ∞ (fun u : ℝ => ((bump c₁ c₂ u / u : ℝ) : ℂ)) := by
    simpa only [Complex.ofRealCLM_apply] using hψ₁'
  have hψ₂ : ContDiff ℝ ∞ (fun u : ℝ => ((bump c₁ c₂ u : ℝ) : ℂ)) := by
    simpa only [Complex.ofRealCLM_apply] using hψ₂'
  have hz₁ : ∀ u : ℝ, u ∉ Set.Icc (c₁ / 2) (c₂ + 1) → ((bump c₁ c₂ u / u : ℝ) : ℂ) = 0 :=
    fun u hu => by rw [hzero u hu, zero_div, Complex.ofReal_zero]
  have hz₂ : ∀ u : ℝ, u ∉ Set.Icc (c₁ / 2) (c₂ + 1) → ((bump c₁ c₂ u : ℝ) : ℂ) = 0 :=
    fun u hu => by rw [hzero u hu, Complex.ofReal_zero]
  have hcs₁ : HasCompactSupport (fun u : ℝ => ((bump c₁ c₂ u / u : ℝ) : ℂ)) :=
    HasCompactSupport.intro isCompact_Icc hz₁
  have hcs₂ : HasCompactSupport (fun u : ℝ => ((bump c₁ c₂ u : ℝ) : ℂ)) :=
    HasCompactSupport.intro isCompact_Icc hz₂
  obtain ⟨B₁, hB₁⟩ := exists_iteratedDeriv_bound hψ₁ hcs₁
  obtain ⟨B₂, hB₂⟩ := exists_iteratedDeriv_bound hψ₂ hcs₂
  refine ⟨fun u : ℝ => ((bump c₁ c₂ u / u : ℝ) : ℂ), fun u : ℝ => ((bump c₁ c₂ u : ℝ) : ℂ),
    fun j => max (B₁ j) (B₂ j), hψ₁, hψ₂, ?_, ?_, fun j u => (hB₁ j u).trans (le_max_left _ _),
    fun j u => (hB₂ j u).trans (le_max_right _ _), fun u h1 h2 => ?_⟩
  · intro u hu
    by_contra hmem
    exact hu (hz₁ u hmem)
  · intro u hu
    by_contra hmem
    exact hu (hz₂ u hmem)
  · constructor
    · show ((bump c₁ c₂ u / u : ℝ) : ℂ) = ((u⁻¹ : ℝ) : ℂ)
      rw [bump_eq_one hc₁ h1 h2, one_div]
    · show ((bump c₁ c₂ u : ℝ) : ℂ) = 1
      rw [bump_eq_one hc₁ h1 h2, Complex.ofReal_one]

/-- A bound `B` is a power of `L` for `L ≥ e`: `b ≤ B` gives `b ≤ L^{max(log B, 0)}`. -/
theorem le_rpow_max_log {L b B : ℝ} (hL : Real.exp 1 ≤ L) (hb : b ≤ B) :
    b ≤ L ^ max (Real.log B) 0 := by
  have hL1 : 1 ≤ L := (Real.one_le_exp zero_le_one).trans hL
  by_cases hB : B ≤ 1
  · calc b ≤ B := hb
      _ ≤ 1 := hB
      _ ≤ L ^ max (Real.log B) 0 := Real.one_le_rpow hL1 (le_max_right _ _)
  · have hB1 : 1 < B := not_le.mp hB
    have hB0 : 0 < B := by linarith
    calc b ≤ B := hb
      _ = Real.exp (Real.log B) := (Real.exp_log hB0).symm
      _ = Real.exp 1 ^ Real.log B := (Real.exp_one_rpow _).symm
      _ ≤ L ^ Real.log B := Real.rpow_le_rpow (Real.exp_pos 1).le hL (Real.log_nonneg hB1.le)
      _ ≤ L ^ max (Real.log B) 0 := Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _)

/-- **Where the cutoffs are evaluated**: if `D_A ∈ [U₁, eU₁]`, `D_B ∈ [U₂, eU₂]` and
`c₁ ≤ w/(x D_A D_B) ≤ c₂`, then `w/Y` and `(w + D_A D_B)/Y` lie in `[c₁, (c₂ + 1) e²]`,
`Y = x U₁ U₂`. -/
theorem cut_range {x U₁ U₂ DA DB w c₁ c₂ : ℝ} (hx : 1 ≤ x) (hU₁ : 1 ≤ U₁) (hU₂ : 1 ≤ U₂)
    (hA1 : U₁ ≤ DA) (hA2 : DA ≤ Real.exp 1 * U₁) (hB1 : U₂ ≤ DB) (hB2 : DB ≤ Real.exp 1 * U₂)
    (hc₁ : 0 < c₁) (h1 : c₁ ≤ w / (x * (DA * DB))) (h2 : w / (x * (DA * DB)) ≤ c₂) :
    c₁ ≤ w / (x * U₁ * U₂) ∧ w / (x * U₁ * U₂) ≤ (c₂ + 1) * (Real.exp 1 * Real.exp 1) ∧
      c₁ ≤ (w + DA * DB) / (x * U₁ * U₂) ∧
        (w + DA * DB) / (x * U₁ * U₂) ≤ (c₂ + 1) * (Real.exp 1 * Real.exp 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hQ1 : 1 ≤ U₁ * U₂ := one_le_mul_of_one_le_of_one_le hU₁ hU₂
  have hQ0 : 0 < U₁ * U₂ := lt_of_lt_of_le one_pos hQ1
  have hQP : U₁ * U₂ ≤ DA * DB := mul_le_mul hA1 hB1 (by linarith) (by linarith)
  have hPQ : DA * DB ≤ Real.exp 1 * Real.exp 1 * (U₁ * U₂) := by
    have h := mul_le_mul hA2 hB2 (by linarith) (mul_nonneg he.le (by linarith))
    calc DA * DB ≤ Real.exp 1 * U₁ * (Real.exp 1 * U₂) := h
      _ = Real.exp 1 * Real.exp 1 * (U₁ * U₂) := by ring
  have hP0 : 0 < DA * DB := lt_of_lt_of_le hQ0 hQP
  have hxP : 0 < x * (DA * DB) := mul_pos hx0 hP0
  have hY : 0 < x * U₁ * U₂ := by
    rw [mul_assoc]
    exact mul_pos hx0 hQ0
  have hc₂ : 0 < c₂ := lt_of_lt_of_le hc₁ (h1.trans h2)
  have hw1 : c₁ * (x * (DA * DB)) ≤ w := (le_div_iff₀ hxP).mp h1
  have hw2 : w ≤ c₂ * (x * (DA * DB)) := (div_le_iff₀ hxP).mp h2
  have hlow : c₁ * (x * U₁ * U₂) ≤ w := by
    have h : c₁ * (x * (U₁ * U₂)) ≤ c₁ * (x * (DA * DB)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hQP hx0.le) hc₁.le
    calc c₁ * (x * U₁ * U₂) = c₁ * (x * (U₁ * U₂)) := by ring
      _ ≤ c₁ * (x * (DA * DB)) := h
      _ ≤ w := hw1
  have hup : w ≤ c₂ * (Real.exp 1 * Real.exp 1) * (x * U₁ * U₂) := by
    have h : c₂ * (x * (DA * DB)) ≤ c₂ * (x * (Real.exp 1 * Real.exp 1 * (U₁ * U₂))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hPQ hx0.le) hc₂.le
    calc w ≤ c₂ * (x * (DA * DB)) := hw2
      _ ≤ c₂ * (x * (Real.exp 1 * Real.exp 1 * (U₁ * U₂))) := h
      _ = c₂ * (Real.exp 1 * Real.exp 1) * (x * U₁ * U₂) := by ring
  have hPY : DA * DB ≤ Real.exp 1 * Real.exp 1 * (x * U₁ * U₂) := by
    have h : Real.exp 1 * Real.exp 1 * (U₁ * U₂) ≤ Real.exp 1 * Real.exp 1 * (x * (U₁ * U₂)) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hQ0.le hx) (mul_pos he he).le
    calc DA * DB ≤ Real.exp 1 * Real.exp 1 * (U₁ * U₂) := hPQ
      _ ≤ Real.exp 1 * Real.exp 1 * (x * (U₁ * U₂)) := h
      _ = Real.exp 1 * Real.exp 1 * (x * U₁ * U₂) := by ring
  have hee : 0 ≤ Real.exp 1 * Real.exp 1 * (x * U₁ * U₂) :=
    mul_nonneg (mul_pos he he).le hY.le
  refine ⟨(le_div_iff₀ hY).mpr hlow, (div_le_iff₀ hY).mpr ?_, (le_div_iff₀ hY).mpr ?_,
    (div_le_iff₀ hY).mpr ?_⟩
  · have e : (c₂ + 1) * (Real.exp 1 * Real.exp 1) * (x * U₁ * U₂) =
        c₂ * (Real.exp 1 * Real.exp 1) * (x * U₁ * U₂) +
          Real.exp 1 * Real.exp 1 * (x * U₁ * U₂) := by ring
    linarith
  · linarith
  · have e : (c₂ + 1) * (Real.exp 1 * Real.exp 1) * (x * U₁ * U₂) =
        c₂ * (Real.exp 1 * Real.exp 1) * (x * U₁ * U₂) +
          Real.exp 1 * Real.exp 1 * (x * U₁ * U₂) := by ring
    linarith

/-! ### Additive characters modulo `H` -/

/-- `e(n) = 1` for an integer `n`. -/
theorem addChar_intCast (n : ℤ) : addChar (n : ℝ) = 1 := by
  unfold addChar
  have e : 2 * (Real.pi : ℂ) * ((n : ℝ) : ℂ) * Complex.I =
      (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [e]
  exact Complex.exp_int_mul_two_pi_mul_I n

/-- **Orthogonality of the additive characters modulo `H`**:
`∑_{j < H} e(jm/H) = H · 1_{H ∣ m}`. -/
theorem sum_addChar_range {H : ℕ} (hH : 0 < H) (m : ℤ) :
    ∑ j ∈ Finset.range H, addChar ((j : ℝ) * (m : ℝ) / (H : ℝ)) =
      if (H : ℤ) ∣ m then (H : ℂ) else 0 := by
  have hH0 : (H : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hH.ne'
  have hpow : ∀ j : ℕ, addChar ((j : ℝ) * (m : ℝ) / (H : ℝ)) =
      addChar ((m : ℝ) / (H : ℝ)) ^ j := by
    intro j
    induction j with
    | zero => rw [Nat.cast_zero, zero_mul, zero_div, CircleMethod.addChar_zero, pow_zero]
    | succ j ih =>
      have e : ((j + 1 : ℕ) : ℝ) * (m : ℝ) / (H : ℝ) =
          (j : ℝ) * (m : ℝ) / (H : ℝ) + (m : ℝ) / (H : ℝ) := by
        push_cast
        ring
      rw [e, addChar_add, ih, pow_succ]
  have hzH : addChar ((m : ℝ) / (H : ℝ)) ^ H = 1 := by
    rw [← hpow H, mul_div_cancel_left₀ _ hH0, addChar_intCast]
  rw [Finset.sum_congr rfl fun j _ => hpow j]
  by_cases hdvd : (H : ℤ) ∣ m
  · rw [if_pos hdvd]
    obtain ⟨k, hk⟩ := hdvd
    have hz : addChar ((m : ℝ) / (H : ℝ)) = 1 := by
      rw [hk, Int.cast_mul, Int.cast_natCast, mul_div_cancel_left₀ _ hH0, addChar_intCast]
    rw [hz]
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · rw [if_neg hdvd]
    have hz : addChar ((m : ℝ) / (H : ℝ)) ≠ 1 := by
      intro h1
      apply hdvd
      unfold addChar at h1
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h1
      have h2πI : 2 * (Real.pi : ℂ) * Complex.I ≠ 0 :=
        mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
          Complex.I_ne_zero
      have h2 : (((m : ℝ) / (H : ℝ) : ℝ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) =
          (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        rw [← hn]
        ring
      have h3 : (((m : ℝ) / (H : ℝ) : ℝ) : ℂ) = (n : ℂ) := mul_right_cancel₀ h2πI h2
      have h4 : (m : ℝ) / (H : ℝ) = (n : ℝ) := by exact_mod_cast h3
      have h5 : (m : ℝ) = (n : ℝ) * (H : ℝ) := (div_eq_iff hH0).mp h4
      have h6 : m = n * (H : ℤ) := by exact_mod_cast h5
      exact Dvd.intro_left n h6.symm
    rw [geom_sum_eq hz, hzH, sub_self, zero_div]

/-- **A function on `ℤ/H` with values in `[-1, 1]` is a combination of the `H` additive characters
with coefficients of modulus at most one** (`[PUB-tex:0492–0494]`):
`1_{n ≡ c (H)} = (1/H) ∑_{j=0}^{H-1} e(j(n-c)/H)`. -/
theorem exists_char_coeff {H : ℕ} (hH : 0 < H) (f : ZMod H → ℝ) (hf : ∀ a, |f a| ≤ 1) :
    ∃ c : ℕ → ℂ, (∀ j, ‖c j‖ ≤ 1) ∧ ∀ w : ℕ, ((f (w : ZMod H) : ℝ) : ℂ) =
      ∑ j ∈ Finset.range H, c j * addChar ((j : ℝ) * (w : ℝ) / (H : ℝ)) := by
  have hHpos : (0 : ℝ) < (H : ℝ) := Nat.cast_pos.mpr hH
  have hHC : (H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hH.ne'
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℂ, ∀ j, c j = (H : ℂ)⁻¹ * ∑ n ∈ Finset.range H,
      ((f (n : ZMod H) : ℝ) : ℂ) * addChar (-((j : ℝ) * (n : ℝ) / (H : ℝ))) := ⟨_, fun _ => rfl⟩
  refine ⟨c, fun j => ?_, fun w => ?_⟩
  · -- the size of the coefficients
    have h1 : ‖∑ n ∈ Finset.range H, ((f (n : ZMod H) : ℝ) : ℂ) *
        addChar (-((j : ℝ) * (n : ℝ) / (H : ℝ)))‖ ≤ (H : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ n ∈ Finset.range H, ‖((f (n : ZMod H) : ℝ) : ℂ) *
            addChar (-((j : ℝ) * (n : ℝ) / (H : ℝ)))‖ ≤ ∑ _n ∈ Finset.range H, (1 : ℝ) :=
            Finset.sum_le_sum fun n _ => by
              rw [norm_mul, EndpointProof.norm_addChar, mul_one, Complex.norm_real,
                Real.norm_eq_abs]
              exact hf _
        _ = (H : ℝ) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [hc j, norm_mul, norm_inv, Complex.norm_natCast]
    calc (H : ℝ)⁻¹ * ‖∑ n ∈ Finset.range H, ((f (n : ZMod H) : ℝ) : ℂ) *
          addChar (-((j : ℝ) * (n : ℝ) / (H : ℝ)))‖ ≤ (H : ℝ)⁻¹ * (H : ℝ) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hHpos.le)
      _ = 1 := inv_mul_cancel₀ hHpos.ne'
  · -- the inversion
    have hterm : ∀ j ∈ Finset.range H, c j * addChar ((j : ℝ) * (w : ℝ) / (H : ℝ)) =
        (H : ℂ)⁻¹ * ∑ n ∈ Finset.range H, ((f (n : ZMod H) : ℝ) : ℂ) *
          addChar ((j : ℝ) * (((w : ℤ) - (n : ℤ) : ℤ) : ℝ) / (H : ℝ)) := by
      intro j _
      rw [hc j, mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      have e : (j : ℝ) * (((w : ℤ) - (n : ℤ) : ℤ) : ℝ) / (H : ℝ) =
          -((j : ℝ) * (n : ℝ) / (H : ℝ)) + (j : ℝ) * (w : ℝ) / (H : ℝ) := by
        push_cast
        ring
      rw [e, addChar_add, mul_assoc]
    have hiff : ∀ n : ℕ, ((H : ℤ) ∣ (w : ℤ) - (n : ℤ)) ↔ (n : ZMod H) = (w : ZMod H) :=
      fun n => by
        rw [← ZMod.intCast_eq_intCast_iff_dvd_sub, Int.cast_natCast, Int.cast_natCast]
    have hinner : ∀ n ∈ Finset.range H, ∑ j ∈ Finset.range H, ((f (n : ZMod H) : ℝ) : ℂ) *
          addChar ((j : ℝ) * (((w : ℤ) - (n : ℤ) : ℤ) : ℝ) / (H : ℝ)) =
        if n = w % H then (H : ℂ) * ((f (w : ZMod H) : ℝ) : ℂ) else 0 := by
      intro n hn
      have hnH : n < H := Finset.mem_range.mp hn
      rw [← Finset.mul_sum, sum_addChar_range hH]
      by_cases hnw : n = w % H
      · have hcast : (n : ZMod H) = (w : ZMod H) := by rw [hnw, ZMod.natCast_mod]
        rw [if_pos hnw, if_pos ((hiff n).mpr hcast), hcast, mul_comm]
      · have hcast : ¬(n : ZMod H) = (w : ZMod H) := by
          intro h
          apply hnw
          have h' := (ZMod.natCast_eq_natCast_iff' n w H).mp h
          rwa [Nat.mod_eq_of_lt hnH] at h'
        rw [if_neg hnw, if_neg (fun h => hcast ((hiff n).mp h)), mul_zero]
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_comm,
      Finset.sum_congr rfl hinner, Finset.sum_ite_eq' (Finset.range H) (w % H),
      if_pos (Finset.mem_range.mpr (Nat.mod_lt w hH)), ← mul_assoc, inv_mul_cancel₀ hHC,
      one_mul]

/-- **The partition of the free tuples by their residues modulo `H`** (`[PUB-tex:0487–0495]`):
if the weight at `(r, w)` is the combination `∑_j cf(a₁(r) a₂(r), j) · (j-th twist)`, the sum
with the weight is the combination over the residues `a = (a₁, a₂)` and the characters `j` of the
sums with the tests restricted to `D_A ≡ a₁`, `D_B ≡ a₂` and the `j`-th twist. -/
theorem residue_expansion {R : Type*} [Fintype R] {H : ℕ} [NeZero H] (wt b₁ b₂ : R → ℂ)
    (a₁ a₂ : R → ZMod H) (sw : Finset ℕ) (cf : ZMod H → ℕ → ℂ) (term : R → ℕ → ℂ)
    (tg : ℕ → R → ℕ → ℂ)
    (hexp : ∀ r, ∀ w ∈ sw, term r w = ∑ j ∈ Finset.range H, cf (a₁ r * a₂ r) j * tg j r w) :
    ∑ r, wt r * (b₁ r * b₂ r) * ∑ w ∈ sw, term r w =
      ∑ a : ZMod H × ZMod H, ∑ j ∈ Finset.range H, cf (a.1 * a.2) j *
        ∑ r, wt r * (b₁ r * (if a₁ r = a.1 then 1 else 0) *
          (b₂ r * (if a₂ r = a.2 then 1 else 0))) * ∑ w ∈ sw, tg j r w := by
  have hrhs : ∀ a : ZMod H × ZMod H, ∑ j ∈ Finset.range H, cf (a.1 * a.2) j *
        ∑ r, wt r * (b₁ r * (if a₁ r = a.1 then 1 else 0) *
          (b₂ r * (if a₂ r = a.2 then 1 else 0))) * ∑ w ∈ sw, tg j r w =
      ∑ r, ∑ j ∈ Finset.range H, cf (a.1 * a.2) j *
        (wt r * (b₁ r * (if a₁ r = a.1 then 1 else 0) *
          (b₂ r * (if a₂ r = a.2 then 1 else 0))) * ∑ w ∈ sw, tg j r w) := by
    intro a
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
  rw [Finset.sum_congr rfl fun a _ => hrhs a, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hsingle : ∑ a : ZMod H × ZMod H, ∑ j ∈ Finset.range H, cf (a.1 * a.2) j *
        (wt r * (b₁ r * (if a₁ r = a.1 then 1 else 0) *
          (b₂ r * (if a₂ r = a.2 then 1 else 0))) * ∑ w ∈ sw, tg j r w) =
      ∑ j ∈ Finset.range H, cf (a₁ r * a₂ r) j *
        (wt r * (b₁ r * b₂ r) * ∑ w ∈ sw, tg j r w) := by
    rw [Fintype.sum_eq_single (a₁ r, a₂ r)]
    · refine Finset.sum_congr rfl fun j _ => ?_
      show cf (a₁ r * a₂ r) j * (wt r * (b₁ r * (if a₁ r = a₁ r then 1 else 0) *
          (b₂ r * (if a₂ r = a₂ r then 1 else 0))) * ∑ w ∈ sw, tg j r w) =
        cf (a₁ r * a₂ r) j * (wt r * (b₁ r * b₂ r) * ∑ w ∈ sw, tg j r w)
      rw [if_pos rfl, if_pos rfl, mul_one, mul_one]
    · intro a ha
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases h1 : a₁ r = a.1
      · have h2 : ¬a₂ r = a.2 := fun h2 => ha (Prod.ext h1.symm h2.symm)
        rw [if_neg h2, mul_zero, mul_zero, mul_zero, zero_mul, mul_zero]
      · rw [if_neg h1, mul_zero, zero_mul, mul_zero, zero_mul, mul_zero]
  rw [hsingle, Finset.mul_sum]
  have hw : ∀ w ∈ sw, wt r * (b₁ r * b₂ r) * term r w =
      ∑ j ∈ Finset.range H, cf (a₁ r * a₂ r) j * (wt r * (b₁ r * b₂ r) * tg j r w) := by
    intro w hw
    rw [hexp r w hw, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl hw, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 : cf (a₁ r * a₂ r) j * (wt r * (b₁ r * b₂ r) * ∑ w ∈ sw, tg j r w) =
      ∑ w ∈ sw, cf (a₁ r * a₂ r) j * (wt r * (b₁ r * b₂ r) * tg j r w) := by
    rw [Finset.mul_sum, Finset.mul_sum]
  exact h2.symm

/-- The size of a combination over the residues and the characters. -/
theorem norm_residue_sum_le {H : ℕ} [NeZero H] (cf : ZMod H → ℕ → ℂ)
    (hcf : ∀ c j, ‖cf c j‖ ≤ 1) (X : ZMod H × ZMod H → ℕ → ℂ) {Bd : ℝ}
    (hX : ∀ a j, ‖X a j‖ ≤ Bd) :
    ‖∑ a : ZMod H × ZMod H, ∑ j ∈ Finset.range H, cf (a.1 * a.2) j * X a j‖ ≤
      (H : ℝ) ^ 3 * Bd := by
  have hBd : 0 ≤ Bd := (norm_nonneg _).trans (hX (0, 0) 0)
  have hterm : ∀ (a : ZMod H × ZMod H) (j : ℕ), ‖cf (a.1 * a.2) j * X a j‖ ≤ Bd := by
    intro a j
    rw [norm_mul]
    have h := mul_le_mul (hcf (a.1 * a.2) j) (hX a j) (norm_nonneg _) zero_le_one
    rwa [one_mul] at h
  calc ‖∑ a : ZMod H × ZMod H, ∑ j ∈ Finset.range H, cf (a.1 * a.2) j * X a j‖
      ≤ ∑ a : ZMod H × ZMod H, ∑ j ∈ Finset.range H, ‖cf (a.1 * a.2) j * X a j‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => norm_sum_le _ _)
    _ ≤ ∑ _a : ZMod H × ZMod H, ∑ _j ∈ Finset.range H, Bd :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun j _ => hterm a j
    _ = (H : ℝ) ^ 3 * Bd := by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_range, Finset.card_univ,
          Fintype.card_prod, ZMod.card, nsmul_eq_mul, nsmul_eq_mul]
        push_cast
        ring

end Separation

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
