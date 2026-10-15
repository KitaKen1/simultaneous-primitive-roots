module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.CleanNorm.Sym
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.CleanNorm.FibreBound
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Bridge
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Scalars
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# [S] Lemma 3.10 (clean norm), proved

Source: `verification/stage7-sources/S-02.tex`, lines 896–1041 (`[S-02:0896–1041]`).

"There is `C_s`, depending only on the fixed data in Definition 3.1, such that the clean part of
every edge satisfies `‖ℰ_{i,clean}‖ ≤ 2 L^{-E_id + C_s}` for all sufficiently large `x`, under
(eq:ideal-norm-hypothesis). In particular `C_s` is independent of `m, C₁, J`." [S-02:0898–0909]

## The constant

`C_s = C₀ log C_𝒮`, `C_𝒮 = groupConst v₋ q ℓ`, the constant of (eq:small-map-norm)
[S-02:0943–0951] ("a constant depending only on `q, ℓ, v₋`; over `O(T)` small groups this is
`L^{O(1)}`"). It depends on the fixed data of Definition 3.1 only.

## The proof

* `Coef.lean`, `Sym.lean`: `ℰ_{i,clean}(θ) = Sym ∘ (u · 𝒯_{d'}(θ)(P_𝐝 ·)) ∘ Sym`
  (eq:clean-conditioned-form), and `‖ℰ_{i,clean}(θ)‖ ≤ K_𝒮 · sup_{d', Θ} ‖fibre operator‖`
  (`edgeClean_bound`: conditioning on the shared small labels `Cond.lean`, Fourier reduction
  `Transfer.lean`).
* `Fibre.lean`, `FibreBound.lean`, `Ban.lean`, `ShRow.lean`: the fibre operator at the frequency
  `Θ` is a unimodular multiple of the ideal operator at the frequency `Θ k d'` (or of its
  adjoint, on backward edges) after "two changes" [S-02:0986–1012]: the fresh target labels have
  the law `μ̃_g` instead of `μ_g`, and the auxiliary labels are banned from both lists. The first
  costs `(1 + δ)^{M|ℬ|} - 1`, the second `2 √ε₂` (in units of `∑_ν sup |K_ν|`), where
  `δ = 4N/P_*` and `ε₂ = m |ℬ|² M / (v₋ P_*)`; the comparison of `L²(⊗ μ̃_g)` with `ℋ_id` costs
  the factors `(1 ± δ)^{M|ℬ|}` (`clean_fibre_bound`).
* This file: for large `x` all these errors are at most `L^{-E_id}/4` times the appropriate
  constants (`clean_scalar_main`: "`o(L^{-A})` for every fixed `A`", because `P_* = exp(L^c)`
  dominates every power of `L`), so that every fibre operator has norm at most `2 L^{-E_id}`;
  and `K_𝒮 ≤ L^{C_s}`. The factor `2` of the statement is the room for the two changes.

The bound is proved for all functions on the memory states, not only for the functions which are
symmetric in the particle indices; the hypothesis `i < N` is not used either.

## The threshold

It depends on `P, E_id, m, C₁, J` (not on `C₂`): `log x ≥ 16`,
`log x ≥ 160 M C₀`, `log x ≥ 256 m C₀² M / v₋`, `log x ≥ C₀ M / v₋`, the thresholds of
`eventually_big_tilt` and `eventually_tiltLaw_relative_error`, and
`L³ L^K ≤ exp(L^c)` for `K ∈ {0, E_id + C₁, 2 (E_id + C₁)}`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

open Filter

noncomputable section

/-! ### Scalars -/

/-- **The scalar condition of `clean_fibre_bound`**: if `n δ ≤ 1/5` and the two errors are at most
`E/4`, then `(1 + δ)^n (E + pm · ((1 + δ)^n - 1 + 2 √ε₂))² ≤ (2E)² (1 - δ)^n`. -/
theorem clean_hsc {δ E pm ε₂ : ℝ} {n₀ : ℕ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (ht : (n₀ : ℝ) * δ ≤ 1 / 5) (hE : 0 ≤ E) (hpm : 0 ≤ pm)
    (hsmall : pm * (5 / 4 * ((n₀ : ℝ) * δ) + 2 * Real.sqrt ε₂) ≤ E / 4) :
    (1 + δ) ^ n₀ * (E + pm * ((1 + δ) ^ n₀ - 1 + 2 * Real.sqrt ε₂)) ^ 2 ≤
      (2 * E) ^ 2 * (1 - δ) ^ n₀ := by
  have ht0 : 0 ≤ (n₀ : ℝ) * δ := mul_nonneg (Nat.cast_nonneg _) hδ0
  have hA1 : (1 : ℝ) ≤ (1 + δ) ^ n₀ := one_le_pow₀ (by linarith)
  have ha : 1 - (n₀ : ℝ) * δ ≤ (1 - δ) ^ n₀ := by
    have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ -δ by linarith) n₀
    have e1 : (1 : ℝ) + (n₀ : ℝ) * -δ = 1 - (n₀ : ℝ) * δ := by ring
    have e2 : (1 : ℝ) + -δ = 1 - δ := by ring
    rw [e1, e2] at h
    exact h
  have hAa : (1 + δ) ^ n₀ * (1 - δ) ^ n₀ ≤ 1 := by
    have e : (1 + δ) * (1 - δ) = 1 - δ ^ 2 := by ring
    rw [← mul_pow]
    refine pow_le_one₀ (mul_nonneg (by linarith) (by linarith)) ?_
    rw [e]
    linarith [sq_nonneg δ]
  have h45 : (4 : ℝ) / 5 ≤ (1 - δ) ^ n₀ := by linarith
  have hA0 : (0 : ℝ) ≤ (1 + δ) ^ n₀ := by linarith
  have hA54 : (1 + δ) ^ n₀ ≤ 5 / 4 := by
    have h := mul_le_mul_of_nonneg_left h45 hA0
    linarith
  have hAm1 : (1 + δ) ^ n₀ - 1 ≤ 5 / 4 * ((n₀ : ℝ) * δ) := by
    have h1 := mul_le_mul_of_nonneg_left ha hA0
    have h2 := mul_le_mul_of_nonneg_right hA54 ht0
    have e : (1 + δ) ^ n₀ * (1 - (n₀ : ℝ) * δ) =
        (1 + δ) ^ n₀ - (1 + δ) ^ n₀ * ((n₀ : ℝ) * δ) := by ring
    rw [e] at h1
    linarith
  have hsq0 : 0 ≤ Real.sqrt ε₂ := Real.sqrt_nonneg _
  have hη0 : 0 ≤ (1 + δ) ^ n₀ - 1 + 2 * Real.sqrt ε₂ := by linarith
  have hη : (1 + δ) ^ n₀ - 1 + 2 * Real.sqrt ε₂ ≤
      5 / 4 * ((n₀ : ℝ) * δ) + 2 * Real.sqrt ε₂ := by linarith
  have hX0 : 0 ≤ pm * ((1 + δ) ^ n₀ - 1 + 2 * Real.sqrt ε₂) := mul_nonneg hpm hη0
  have hX : pm * ((1 + δ) ^ n₀ - 1 + 2 * Real.sqrt ε₂) ≤ E / 4 :=
    (mul_le_mul_of_nonneg_left hη hpm).trans hsmall
  have hsq : (E + pm * ((1 + δ) ^ n₀ - 1 + 2 * Real.sqrt ε₂)) ^ 2 ≤ (5 / 4 * E) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  calc (1 + δ) ^ n₀ * (E + pm * ((1 + δ) ^ n₀ - 1 + 2 * Real.sqrt ε₂)) ^ 2
      ≤ 5 / 4 * (5 / 4 * E) ^ 2 := mul_le_mul hA54 hsq (sq_nonneg _) (by norm_num)
    _ = 125 / 64 * E ^ 2 := by ring
    _ ≤ 16 / 5 * E ^ 2 := mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg E)
    _ = (2 * E) ^ 2 * (4 / 5) := by ring
    _ ≤ (2 * E) ^ 2 * (1 - δ) ^ n₀ := mul_le_mul_of_nonneg_left h45 (sq_nonneg _)

/-- The sizes of the two changes in terms of `L³/P_*`: for `ι = 1/P_*`, `|ℬ| ≤ C₀ L`, `N ≤ 4L`
and `L` larger than the constants of the fixed data. -/
theorem clean_scalar_bounds {L ι vi C₀ Mr mr br Nr w' : ℝ}
    (hL16 : 16 ≤ L) (hι : 0 ≤ ι) (hvi : 0 ≤ vi) (hC₀ : 0 ≤ C₀) (hMr : 0 ≤ Mr) (hmr : 0 ≤ mr)
    (hb0 : 0 ≤ br) (hbL : br ≤ C₀ * L) (hN0 : 0 ≤ Nr) (hNL : Nr ≤ 4 * L)
    (hc2 : 160 * (Mr * C₀) ≤ L) (hc3 : 256 * (mr * (C₀ * C₀ * Mr) * vi) ≤ L)
    (hc4 : C₀ * Mr * vi ≤ L)
    (hQ0 : L * (L * L * ι) ≤ 1) (hQ1 : L * (L * L * ι) ≤ w')
    (hQ2 : L * (L * L * ι) ≤ w' * w') :
    4 * Nr * ι ≤ 1 ∧ br * (Mr * (vi * ι)) ≤ 1 ∧
      Mr * br * (4 * Nr * ι) ≤ 1 / 5 ∧ Mr * br * (4 * Nr * ι) ≤ w' / 10 ∧
      mr * br * (br * (Mr * (vi * ι))) ≤ w' / 16 * (w' / 16) := by
  have hL0 : 0 ≤ L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hLι0 : 0 ≤ L * ι := mul_nonneg hL0 hι
  have hZ0 : 0 ≤ L * L * ι := mul_nonneg (mul_nonneg hL0 hL0) hι
  have hZ : L * (L * ι) ≤ L * (L * L * ι) := by
    have h := mul_le_mul_of_nonneg_right hL1 hZ0
    have e : L * (L * ι) = 1 * (L * L * ι) := by ring
    rw [e]
    exact h
  -- the relative error `δ = 4N/P_*`
  have h1a : 4 * Nr * ι ≤ 4 * (4 * L) * ι :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNL (by norm_num)) hι
  have h1b : 16 * (L * ι) ≤ L * (L * ι) := mul_le_mul_of_nonneg_right hL16 hLι0
  have e1 : 4 * (4 * L) * ι = 16 * (L * ι) := by ring
  have r1 : 4 * Nr * ι ≤ 1 := by
    rw [e1] at h1a
    linarith
  -- the probability that one auxiliary label hits one list
  have h2a : br * (Mr * (vi * ι)) ≤ C₀ * L * (Mr * (vi * ι)) :=
    mul_le_mul_of_nonneg_right hbL (mul_nonneg hMr (mul_nonneg hvi hι))
  have e2 : C₀ * L * (Mr * (vi * ι)) = C₀ * Mr * vi * (L * ι) := by ring
  have h2b : C₀ * Mr * vi * (L * ι) ≤ L * (L * ι) := mul_le_mul_of_nonneg_right hc4 hLι0
  have r2 : br * (Mr * (vi * ι)) ≤ 1 := by
    rw [e2] at h2a
    linarith
  -- `M |ℬ| δ`
  have h3a : Mr * br * (4 * Nr * ι) ≤ Mr * (C₀ * L) * (4 * (4 * L) * ι) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hbL hMr) h1a
      (mul_nonneg (mul_nonneg (by norm_num) hN0) hι) (mul_nonneg hMr (mul_nonneg hC₀ hL0))
  have e3 : Mr * (C₀ * L) * (4 * (4 * L) * ι) = 160 * (Mr * C₀) * (L * L * ι) / 10 := by ring
  have h3b : 160 * (Mr * C₀) * (L * L * ι) ≤ L * (L * L * ι) :=
    mul_le_mul_of_nonneg_right hc2 hZ0
  have r3 : Mr * br * (4 * Nr * ι) ≤ L * (L * L * ι) / 10 := by
    rw [e3] at h3a
    linarith
  -- `ε₂`
  have hbb0 : 0 ≤ br * (Mr * (vi * ι)) := mul_nonneg hb0 (mul_nonneg hMr (mul_nonneg hvi hι))
  have h5a : mr * br * (br * (Mr * (vi * ι))) ≤ mr * (C₀ * L) * (C₀ * L * (Mr * (vi * ι))) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hbL hmr) h2a hbb0
      (mul_nonneg hmr (mul_nonneg hC₀ hL0))
  have e5 : mr * (C₀ * L) * (C₀ * L * (Mr * (vi * ι))) =
      256 * (mr * (C₀ * C₀ * Mr) * vi) * (L * L * ι) / 256 := by ring
  have h5b : 256 * (mr * (C₀ * C₀ * Mr) * vi) * (L * L * ι) ≤ L * (L * L * ι) :=
    mul_le_mul_of_nonneg_right hc3 hZ0
  have r5 : mr * br * (br * (Mr * (vi * ι))) ≤ L * (L * L * ι) / 256 := by
    rw [e5] at h5a
    linarith
  have e6 : w' / 16 * (w' / 16) = w' * w' / 256 := by ring
  refine ⟨r1, r2, by linarith, by linarith, ?_⟩
  rw [e6]
  linarith

/-- `L³/P_*` is at most `1`, `L^{-K}` and `L^{-2K}`, if `P_*` is at least `L³`, `L^{3+K}` and
`L^{3+2K}`. -/
theorem clean_rpow_bounds {L Pst K : ℝ} (hL : 0 < L) (hP : 0 < Pst)
    (h0 : L ^ 3 * L ^ (0 : ℝ) ≤ Pst) (h1 : L ^ 3 * L ^ K ≤ Pst)
    (h2 : L ^ 3 * L ^ (K + K) ≤ Pst) :
    L * (L * L * Pst⁻¹) ≤ 1 ∧ L * (L * L * Pst⁻¹) ≤ L ^ (-K) ∧
      L * (L * L * Pst⁻¹) ≤ L ^ (-K) * L ^ (-K) := by
  have hι : 0 < Pst⁻¹ := inv_pos.mpr hP
  have hPι : Pst * Pst⁻¹ = 1 := mul_inv_cancel₀ hP.ne'
  have hw'0 : 0 ≤ L ^ (-K) := Real.rpow_nonneg hL.le _
  have hww' : L ^ K * L ^ (-K) = 1 := by
    rw [← Real.rpow_add hL, add_neg_cancel, Real.rpow_zero]
  refine ⟨?_, ?_, ?_⟩
  · have h0' : L ^ 3 ≤ Pst := by
      rw [Real.rpow_zero, mul_one] at h0
      exact h0
    have h : L ^ 3 * Pst⁻¹ ≤ Pst * Pst⁻¹ := mul_le_mul_of_nonneg_right h0' hι.le
    have e : L * (L * L * Pst⁻¹) = L ^ 3 * Pst⁻¹ := by ring
    rw [e]
    exact h.trans (le_of_eq hPι)
  · have h : L ^ 3 * L ^ K * Pst⁻¹ * L ^ (-K) ≤ Pst * Pst⁻¹ * L ^ (-K) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hι.le) hw'0
    have e : L ^ 3 * L ^ K * Pst⁻¹ * L ^ (-K) =
        L * (L * L * Pst⁻¹) * (L ^ K * L ^ (-K)) := by ring
    rw [e, hww', mul_one, hPι, one_mul] at h
    exact h
  · have h : L ^ 3 * (L ^ K * L ^ K) * Pst⁻¹ * (L ^ (-K) * L ^ (-K)) ≤
        Pst * Pst⁻¹ * (L ^ (-K) * L ^ (-K)) := by
      rw [Real.rpow_add hL] at h2
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hι.le)
        (mul_nonneg hw'0 hw'0)
    have e : L ^ 3 * (L ^ K * L ^ K) * Pst⁻¹ * (L ^ (-K) * L ^ (-K)) =
        L * (L * L * Pst⁻¹) * (L ^ K * L ^ (-K) * (L ^ K * L ^ (-K))) := by ring
    rw [e, hww', mul_one, mul_one, hPι, one_mul] at h
    exact h

/-- **`P_* = exp(L^c)` dominates every power of `L`** [S-02:0999–1001, 1011–1012]: for every real
`K`, `L³ · L^K ≤ exp(L^c)` for all sufficiently large `x`. -/
theorem clean_log_pow_le (c : ℝ) (hc : 0 < c) (K : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      Real.log x ^ 3 * Real.log x ^ K ≤ Graph.sourcePrimeLowerBound c (Real.log x) := by
  have hpos : (0 : ℝ) < 3 + |K| := by linarith [abs_nonneg K]
  filter_upwards [eventually_loglog_le c (3 + |K|)⁻¹ hc (inv_pos.mpr hpos),
    eventually_log_ge 1] with x hx h1
  have hL0 : 0 < Real.log x := lt_of_lt_of_le zero_lt_one h1
  have hT0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg h1
  have h2 : (3 + |K|) * Real.log (Real.log x) ≤ Real.log x ^ c := by
    have h := mul_le_mul_of_nonneg_left hx hpos.le
    rw [mul_inv_cancel_left₀ hpos.ne'] at h
    exact h
  have h3 : Real.log (Real.log x) * K ≤ Real.log (Real.log x) * |K| :=
    mul_le_mul_of_nonneg_left (le_abs_self K) hT0
  have e1 : Real.log x ^ 3 = Real.exp (((3 : ℕ) : ℝ) * Real.log (Real.log x)) := by
    rw [Real.exp_nat_mul, Real.exp_log hL0]
  have e2 : Real.log x ^ K = Real.exp (Real.log (Real.log x) * K) :=
    Real.rpow_def_of_pos hL0 K
  have h3' : ((3 : ℕ) : ℝ) = 3 := by norm_num
  rw [e1, e2, ← Real.exp_add, h3']
  unfold Graph.sourcePrimeLowerBound
  refine Real.exp_le_exp.mpr ?_
  calc 3 * Real.log (Real.log x) + Real.log (Real.log x) * K
      ≤ 3 * Real.log (Real.log x) + Real.log (Real.log x) * |K| := by linarith
    _ = (3 + |K|) * Real.log (Real.log x) := by ring
    _ ≤ Real.log x ^ c := h2

/-- **The scalar conditions of Lemma 3.10** [S-02:0986–1012]: for `L` larger than the constants
of the fixed data and `P_* ≥ L³ L^K` for `K ∈ {0, E_id + C₁, 2(E_id + C₁)}`, with `|ℬ| ≤ C₀ L`,
`N ≤ 4L` and `∑_ν sup |K_ν| ≤ L^{C₁}`: `δ = 4N/P_* ≤ 1`, `|ℬ| M /(v₋ P_*) ≤ 1`, and the scalar
condition of `clean_fibre_bound` with `E = L^{-E_id}` and `C_T = 2 L^{-E_id}`. -/
theorem clean_scalar_main {L Pst v C₀ Eid C₁ pm : ℝ} {M m b n : ℕ}
    (hL16 : 16 ≤ L) (hPst : 0 < Pst) (hv : 0 < v) (hC₀ : 0 ≤ C₀)
    (hbL : (b : ℝ) ≤ C₀ * L) (hNL : (n : ℝ) ≤ 4 * L)
    (hc2 : 160 * ((M : ℝ) * C₀) ≤ L)
    (hc3 : 256 * ((m : ℝ) * (C₀ * C₀ * (M : ℝ)) * v⁻¹) ≤ L)
    (hc4 : C₀ * (M : ℝ) * v⁻¹ ≤ L)
    (hP0 : L ^ 3 * L ^ (0 : ℝ) ≤ Pst) (hP1 : L ^ 3 * L ^ (Eid + C₁) ≤ Pst)
    (hP2 : L ^ 3 * L ^ (Eid + C₁ + (Eid + C₁)) ≤ Pst)
    (hpm0 : 0 ≤ pm) (hpm : pm ≤ L ^ C₁) :
    4 * (n : ℝ) / Pst ≤ 1 ∧ (b : ℝ) * ((M : ℝ) * (v⁻¹ * Pst⁻¹)) ≤ 1 ∧
      (1 + 4 * (n : ℝ) / Pst) ^ (M * b) *
          (L ^ (-Eid) + pm * ((1 + 4 * (n : ℝ) / Pst) ^ (M * b) - 1 +
            2 * Real.sqrt (((m * b : ℕ) : ℝ) * ((b : ℝ) * ((M : ℝ) * (v⁻¹ * Pst⁻¹)))))) ^ 2 ≤
        (2 * L ^ (-Eid)) ^ 2 * (1 - 4 * (n : ℝ) / Pst) ^ (M * b) := by
  have hL0 : 0 < L := by linarith
  have hι : 0 < Pst⁻¹ := inv_pos.mpr hPst
  have hvi : 0 < v⁻¹ := inv_pos.mpr hv
  have hw'0 : 0 ≤ L ^ (-(Eid + C₁)) := Real.rpow_nonneg hL0.le _
  have hw16 : 0 ≤ L ^ (-(Eid + C₁)) / 16 := by linarith
  obtain ⟨hQ0, hQ1, hQ2⟩ := clean_rpow_bounds hL0 hPst hP0 hP1 hP2
  obtain ⟨hs1, hs2, hs3, hs4, hs5⟩ := clean_scalar_bounds (w' := L ^ (-(Eid + C₁)))
    hL16 hι.le hvi.le hC₀ (Nat.cast_nonneg M) (Nat.cast_nonneg m) (Nat.cast_nonneg b) hbL
    (Nat.cast_nonneg n) hNL hc2 hc3 hc4 hQ0 hQ1 hQ2
  have hδeq : 4 * (n : ℝ) / Pst = 4 * (n : ℝ) * Pst⁻¹ := div_eq_mul_inv _ _
  have hδ0 : 0 ≤ 4 * (n : ℝ) / Pst :=
    div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) hPst.le
  have hδ1 : 4 * (n : ℝ) / Pst ≤ 1 := by
    rw [hδeq]
    exact hs1
  have hMb : ((M * b : ℕ) : ℝ) = (M : ℝ) * (b : ℝ) := Nat.cast_mul M b
  have hmb : ((m * b : ℕ) : ℝ) = (m : ℝ) * (b : ℝ) := Nat.cast_mul m b
  have ht : ((M * b : ℕ) : ℝ) * (4 * (n : ℝ) / Pst) ≤ 1 / 5 := by
    rw [hMb, hδeq]
    exact hs3
  have ht' : ((M * b : ℕ) : ℝ) * (4 * (n : ℝ) / Pst) ≤ L ^ (-(Eid + C₁)) / 10 := by
    rw [hMb, hδeq]
    exact hs4
  have ht0 : 0 ≤ ((M * b : ℕ) : ℝ) * (4 * (n : ℝ) / Pst) :=
    mul_nonneg (Nat.cast_nonneg _) hδ0
  have hε : ((m * b : ℕ) : ℝ) * ((b : ℝ) * ((M : ℝ) * (v⁻¹ * Pst⁻¹))) ≤
      L ^ (-(Eid + C₁)) / 16 * (L ^ (-(Eid + C₁)) / 16) := by
    rw [hmb]
    exact hs5
  have hsqrt : Real.sqrt (((m * b : ℕ) : ℝ) * ((b : ℝ) * ((M : ℝ) * (v⁻¹ * Pst⁻¹)))) ≤
      L ^ (-(Eid + C₁)) / 16 :=
    (Real.sqrt_le_sqrt hε).trans (le_of_eq (Real.sqrt_mul_self hw16))
  have hs0 : 0 ≤ Real.sqrt (((m * b : ℕ) : ℝ) * ((b : ℝ) * ((M : ℝ) * (v⁻¹ * Pst⁻¹)))) :=
    Real.sqrt_nonneg _
  have hcw : L ^ C₁ * L ^ (-(Eid + C₁)) = L ^ (-Eid) := by
    have e : C₁ + -(Eid + C₁) = -Eid := by ring
    rw [← Real.rpow_add hL0, e]
  have hE0 : 0 ≤ L ^ (-Eid) := Real.rpow_nonneg hL0.le _
  have hsmall : pm * (5 / 4 * (((M * b : ℕ) : ℝ) * (4 * (n : ℝ) / Pst)) +
      2 * Real.sqrt (((m * b : ℕ) : ℝ) * ((b : ℝ) * ((M : ℝ) * (v⁻¹ * Pst⁻¹))))) ≤
      L ^ (-Eid) / 4 := by
    have h1 : 5 / 4 * (((M * b : ℕ) : ℝ) * (4 * (n : ℝ) / Pst)) +
        2 * Real.sqrt (((m * b : ℕ) : ℝ) * ((b : ℝ) * ((M : ℝ) * (v⁻¹ * Pst⁻¹)))) ≤
        L ^ (-(Eid + C₁)) / 4 := by linarith
    have h0 : 0 ≤ 5 / 4 * (((M * b : ℕ) : ℝ) * (4 * (n : ℝ) / Pst)) +
        2 * Real.sqrt (((m * b : ℕ) : ℝ) * ((b : ℝ) * ((M : ℝ) * (v⁻¹ * Pst⁻¹)))) := by
      linarith
    have h2 := mul_le_mul hpm h1 h0 (Real.rpow_nonneg hL0.le C₁)
    have e : L ^ C₁ * (L ^ (-(Eid + C₁)) / 4) = L ^ (-Eid) / 4 := by
      rw [← hcw]
      ring
    rw [e] at h2
    exact h2
  exact ⟨hδ1, hs2, clean_hsc hδ0 hδ1 ht hE0 hpm0 hsmall⟩

/-! ### Lemma 3.10 -/

/-- **Lemma 3.10 for fixed constants**, with the exponent `C_s = C₀ log C_𝒮`,
`C_𝒮 = groupConst v₋ q ℓ`, which depends on the fixed data of Definition 3.1 only. -/
theorem cleanNorm_bound (P : GroupParams) (Eid : ℝ) (m : ℕ) (C₁ : ℝ) (J : ℕ) (C₂ : ℝ) :
    CleanNormBound P (Real.log (Schur.groupConst P.vMinus P.q P.ℓ) * P.C₀) Eid m C₁ J C₂ := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    ((eventually_big_tilt P one_pos).and ((eventually_tiltLaw_relative_error P).and
      ((eventually_log_ge 16).and
        ((eventually_log_ge (160 * (((J + P.ℓ : ℕ) : ℝ) * P.C₀))).and
          ((eventually_log_ge
              (256 * ((m : ℝ) * (P.C₀ * P.C₀ * ((J + P.ℓ : ℕ) : ℝ)) * P.vMinus⁻¹))).and
            ((eventually_log_ge (P.C₀ * ((J + P.ℓ : ℕ) : ℝ) * P.vMinus⁻¹)).and
              ((clean_log_pow_le P.c P.c_pos 0).and
                ((clean_log_pow_le P.c P.c_pos (Eid + C₁)).and
                  (clean_log_pow_le P.c P.c_pos (Eid + C₁ + (Eid + C₁)))))))))))
  refine ⟨x₀, fun x hx S B _ _ _ _ 𝔊 N _ 𝔉 ζ k hadm hid θ i _ => ?_⟩
  obtain ⟨htilt, hrel, hL16, hc2, hc3, hc4, hP0, hP1, hP2⟩ := hx₀ x hx
  intro F _
  have hL1 : (1 : ℝ) ≤ Real.log x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hPst : 0 < Graph.sourcePrimeLowerBound P.c (Real.log x) :=
    Graph.source_prime_lower_bound_pos _ _
  have hι : 0 < (Graph.sourcePrimeLowerBound P.c (Real.log x))⁻¹ := inv_pos.mpr hPst
  have hvi : 0 < P.vMinus⁻¹ := inv_pos.mpr P.vMinus_pos
  -- the sizes of `|ℬ|` and `N`
  have hTL : Real.log (Real.log x) ≤ Real.log x := by
    have h := Real.log_le_sub_one_of_pos hL0
    linarith
  have hbL : (Fintype.card B : ℝ) ≤ P.C₀ * Real.log x :=
    𝔊.card_big_le.trans (mul_le_mul_of_nonneg_left hTL P.C₀_pos.le)
  have hNL : (Graph.sourceMemoryLength (Real.log x) : ℝ) ≤ 4 * Real.log x := by
    have hn := Graph.source_memory_length_upper (Real.log x) hL0.le
    have hpow : Real.log x ^ ((13 : ℝ) / 25) ≤ Real.log x :=
      (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (13 : ℝ) / 25 ≤ 1)).trans
        (le_of_eq (Real.rpow_one _))
    linarith
  -- the scalars
  obtain ⟨hδ1, hδ', hsc⟩ := clean_scalar_main (L := Real.log x)
    (Pst := Graph.sourcePrimeLowerBound P.c (Real.log x)) (v := P.vMinus) (C₀ := P.C₀)
    (Eid := Eid) (C₁ := C₁) (pm := patternMass 𝔉) (M := J + P.ℓ) (m := m)
    (b := Fintype.card B) (n := Graph.sourceMemoryLength (Real.log x))
    hL16 hPst P.vMinus_pos P.C₀_pos.le hbL hNL hc2 hc3 hc4 hP0 hP1 hP2
    (patternMass_nonneg 𝔉) hadm.2.1
  have hδ0 : 0 ≤ 4 * (Graph.sourceMemoryLength (Real.log x) : ℝ) /
      Graph.sourcePrimeLowerBound P.c (Real.log x) :=
    div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hPst.le
  have hE0 : 0 ≤ Real.log x ^ (-Eid) := Real.rpow_nonneg hL0.le _
  have hCT : (0 : ℝ) ≤ 2 * Real.log x ^ (-Eid) := mul_nonneg (by norm_num) hE0
  -- the laws of the big groups
  have hν : ∀ g, ∀ p ∈ 𝔊.big g,
      0 ≤ tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p :=
    fun g p hp => (htilt S B 𝔊 g p hp).2.1.le
  have hμ : ∀ g, ∀ p ∈ 𝔊.big g, Graph.primeGroupLaw (𝔊.big g) p ≤
      P.vMinus⁻¹ * (Graph.sourcePrimeLowerBound P.c (Real.log x))⁻¹ := by
    intro g p hp
    have hden : 0 < P.vMinus * Graph.sourcePrimeLowerBound P.c (Real.log x) :=
      mul_pos P.vMinus_pos hPst
    have hle : P.vMinus * Graph.sourcePrimeLowerBound P.c (Real.log x) ≤
        Graph.primeGroupReciprocalMass (𝔊.big g) * (p : ℝ) :=
      mul_le_mul (𝔊.mass_big_ge g) (𝔊.big_ge g p hp) hPst.le
        (PrimeGroups.mass_pos_of_ge (𝔊.mass_big_ge g)).le
    have h1 : Graph.primeGroupLaw (𝔊.big g) p ≤
        1 / (P.vMinus * Graph.sourcePrimeLowerBound P.c (Real.log x)) := by
      unfold Graph.primeGroupLaw
      exact one_div_le_one_div_of_le hden hle
    rw [one_div, mul_inv] at h1
    exact h1
  -- the ideal estimate
  have hid' : ∀ (Θ : ℝ) (g : LabelList 𝔊.big J P.ℓ → ℂ),
      wNorm (idealWeight 𝔊.big J P.ℓ) (idealOp 𝔉 ζ Θ g) ≤
        Real.log x ^ (-Eid) * wNorm (idealWeight 𝔊.big J P.ℓ) g :=
    fun Θ g => (idealOpNorm_le_iff 𝔊.big_law_pos 𝔉 ζ Θ hE0).mp (hid Θ) g
  -- the fibre operators
  have hfib : ∀ (d : ℕ) (Θ : ℝ) (g : LabelList 𝔊.big J P.ℓ → ℂ),
      wNorm (bigListMass 𝔊.toGroupFamily P.q (Graph.sourceMemoryLength (Real.log x)))
          (bigSym 𝔊.big J P.ℓ (cleanFibOp (cleanKappa (memData 𝔊 𝔉 k ζ) i d)
            (cleanStep (memData 𝔊 𝔉 k ζ) i d) (cleanTau (memData 𝔊 𝔉 k ζ)) Θ
            (bigSym 𝔊.big J P.ℓ g))) ≤
        2 * Real.log x ^ (-Eid) *
          wNorm (bigListMass 𝔊.toGroupFamily P.q (Graph.sourceMemoryLength (Real.log x))) g :=
    fun d Θ g => clean_fibre_bound 𝔊.big_law_sum (fun g p hp => 𝔊.big_law_pos g p hp)
      (mul_nonneg hvi.le hι.le) hμ (memData 𝔊 𝔉 k ζ) hadm.1 hδ' hδ0 hδ1
      (fun g p hp => hrel S B 𝔊 g p hp) hE0 hCT hid' hsc i d Θ g
  -- the small groups
  have hG1 : 1 ≤ Schur.groupConst P.vMinus P.q P.ℓ := Schur.one_le_groupConst _ _ _
  have hGpos : 0 < Schur.groupConst P.vMinus P.q P.ℓ := lt_of_lt_of_le zero_lt_one hG1
  have hprodS : ∏ _g : S, Schur.groupConst P.vMinus P.q P.ℓ ≤
      Real.log x ^ (Real.log (Schur.groupConst P.vMinus P.q P.ℓ) * P.C₀) :=
    𝔊.prod_small_le_rpow hL0 (fun _ => Schur.groupConst P.vMinus P.q P.ℓ)
      (Real.log (Schur.groupConst P.vMinus P.q P.ℓ)) (Real.log_nonneg hG1)
      (fun _ => hGpos.le) (fun _ => (Real.exp_log hGpos).ge)
  have hKS0 : 0 ≤ ∏ _g : S, Schur.groupConst P.vMinus P.q P.ℓ :=
    Finset.prod_nonneg fun _ _ => hGpos.le
  have hKS : ∀ (a : CleanShared 𝔊.toGroupFamily J) (y : ResVec (smallPrimes 𝔊.toGroupFamily)),
      ∑ xs : LabelList 𝔊.small J P.ℓ, cleanSmallW P.q a y xs ≤
        ∏ _g : S, Schur.groupConst P.vMinus P.q P.ℓ :=
    fun a y => clean_sum_smallW_le P.q_pos P.q_lt_one P.vMinus_pos 𝔊.mass_small_ge P.ℓ_pos
      le_rfl a y
  -- the clean bound
  have hmain := edgeClean_bound (Bc := memCutoff (Real.log x)) 𝔊.disjoint_small_big
    (memData 𝔊 𝔉 k ζ) P.q_pos P.q_lt_one (memRho_pos P) (memRho_lt_one P).le hν hKS0 hKS hCT i
    hfib θ F
  have hKC : (∏ _g : S, Schur.groupConst P.vMinus P.q P.ℓ) * (2 * Real.log x ^ (-Eid)) ≤
      2 * Real.log x ^ (-Eid + Real.log (Schur.groupConst P.vMinus P.q P.ℓ) * P.C₀) := by
    rw [Real.rpow_add hL0]
    calc (∏ _g : S, Schur.groupConst P.vMinus P.q P.ℓ) * (2 * Real.log x ^ (-Eid))
        ≤ Real.log x ^ (Real.log (Schur.groupConst P.vMinus P.q P.ℓ) * P.C₀) *
            (2 * Real.log x ^ (-Eid)) := mul_le_mul_of_nonneg_right hprodS hCT
      _ = 2 * (Real.log x ^ (-Eid) *
            Real.log x ^ (Real.log (Schur.groupConst P.vMinus P.q P.ℓ) * P.C₀)) := by ring
  exact hmain.trans (mul_le_mul_of_nonneg_right hKC (wNorm_nonneg _ _))

/-- **[S] Lemma 3.10 (clean norm, `lem:clean-norm`)** [S-02:0898–0909], proved: there is `C_s`,
depending only on the fixed data of Definition 3.1, such that under the ideal estimate
`sup_Θ ‖𝒯(Θ)‖ ≤ L^{-E_id}` the clean part of every edge at the truncation `B = ⌈L²⌉` has norm at
most `2 L^{-E_id + C_s}` on `ℋ`, for all sufficiently large `x` and every phase `θ`. -/
theorem cleanNorm : CleanNorm :=
  fun P => ⟨Real.log (Schur.groupConst P.vMinus P.q P.ℓ) * P.C₀,
    fun Eid m C₁ J C₂ => cleanNorm_bound P Eid m C₁ J C₂⟩

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
