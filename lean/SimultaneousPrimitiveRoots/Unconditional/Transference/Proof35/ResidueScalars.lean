module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Scalars
public import SimultaneousPrimitiveRoots.Unconditional.Transference.PrimeGroups
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The proof of [S] Lemma 3.6, part 5: the scalar estimates

Source: `verification/stage7-sources/S-02.tex`, lines 244–289 (`[S-02:0244–0289]`).

Everything here is about real numbers. `L = log x`, `T = log L`, `N = sourceMemoryLength L`
(`N + 1 ≤ 5 L^{0.52}`), `D = L^d`, `U = (N + 1) T`.

* `residue_scalar_eventually` — "for all sufficiently large `x`": the facts which the proof of
  Lemma 3.6 uses, among them (eq:active-crt-size) and "`0.52 + d < 1`" [S-02:0247–0249, 0285] in
  the form `C · U · L^d ≤ γ L - 4` for the constant `C = scalarConst P J A`.
* `residue_scalar_lam` — `λ ≤ γ L` (in particular `λ ≤ exp(L^d)`).
* `residue_scalar_final` — the relative error of `ResRepl.abs_avg_sub_le`, with `t = e`,
  `Z = exp(2 L^d)` and `K + 1 ≥ 5λ + A N T + 1`, is at most `exp(-A N T)`: "choose `h` of order
  `NT`, with its fixed constant sufficiently large after `A`" and "the total counting error is
  `exp(-γ L + o(L))`" [S-02:0271–0286].
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResRepl

open Filter

noncomputable section

/-- The constant in `C · (N + 1) T · L^d ≤ γ L - 4`. With `M = J + ℓ`:
`C = 12 · 2 C₀ v₊ + 2 C₀ M + 3 A + 6`. -/
def scalarConst (P : GroupParams) (J : ℕ) (A : ℝ) : ℝ :=
  12 * (2 * P.C₀ * P.vPlus) + 2 * P.C₀ * ((J : ℝ) + P.ℓ) + 3 * A + 6

theorem scalarConst_pos (P : GroupParams) (J : ℕ) {A : ℝ} (hA : 0 < A) :
    0 < scalarConst P J A := by
  have h1 : 0 < P.C₀ * P.vPlus := mul_pos P.C₀_pos P.vPlus_pos
  have h2 : 0 ≤ P.C₀ * ((J : ℝ) + P.ℓ) :=
    mul_nonneg P.C₀_pos.le (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  unfold scalarConst
  linarith

/-- **The facts for large `x`** used in the proof of Lemma 3.6. -/
theorem residue_scalar_eventually (P : GroupParams) (J : ℕ) {γ A : ℝ} (hγ : 0 < γ)
    (hA : 0 < A) :
    ∀ᶠ x : ℝ in atTop,
      0 < x ∧ 1 ≤ Real.log x ∧ 1 ≤ Real.log (Real.log x) ∧
      2 * ((Graph.sourceMemoryLength (Real.log x) : ℝ) + 1) ≤ Real.exp (Real.log x ^ P.a) ∧
      γ * Real.log x ≤ Real.exp (Real.log x ^ P.d) ∧
      2 ≤ Real.exp (γ * Real.log x) ∧
      scalarConst P J A *
          (((Graph.sourceMemoryLength (Real.log x) : ℝ) + 1) * Real.log (Real.log x)) *
            Real.log x ^ P.d ≤ γ * Real.log x - 4 := by
  have hC := scalarConst_pos P J hA
  have hCne : scalarConst P J A ≠ 0 := hC.ne'
  have hd : 0 < P.d := P.a_pos.trans (P.a_lt_b.trans (P.b_lt_c.trans P.c_lt_d))
  have hc' : (0 : ℝ) < 12 / 25 - P.d := by linarith [P.d_lt]
  have hε : 0 < γ / (10 * scalarConst P J A) := div_pos hγ (mul_pos (by norm_num) hC)
  have hE1 := eventually_log_ge (Real.exp 1)
  have hE2 := eventually_log_ge (8 / γ)
  have hE3 : ∀ᶠ x : ℝ in atTop, 2 * ((Graph.sourceMemoryLength (Real.log x) : ℝ) + 1) ≤
      Graph.sourcePrimeLowerBound P.a (Real.log x) :=
    Real.tendsto_log_atTop.eventually
      (Graph.source_prime_eventually_dominates_visits P.a P.a_pos)
  have hE4 : ∀ᶠ x : ℝ in atTop,
      Real.log x ^ (1 : ℝ) / Graph.sourcePrimeLowerBound P.d (Real.log x) < 1 / γ :=
    Real.tendsto_log_atTop.eventually
      ((Graph.source_rpow_div_prime_lower_bound_tendsto 1 P.d hd).eventually
        (gt_mem_nhds (one_div_pos.mpr hγ)))
  have hE5 := eventually_loglog_le (12 / 25 - P.d) (γ / (10 * scalarConst P J A)) hc' hε
  filter_upwards [hE1, hE2, hE3, hE4, hE5, eventually_gt_atTop (0 : ℝ)] with x h1 h2 h3 h4 h5 h6
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hL1 : 1 ≤ Real.log x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hT1 : 1 ≤ Real.log (Real.log x) := by
    have h := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at h
  have hγL : 8 ≤ γ * Real.log x := by
    have h := (div_le_iff₀ hγ).mp h2
    linarith
  refine ⟨h6, hL1, hT1, h3, ?_, ?_, ?_⟩
  · have hpos : 0 < Graph.sourcePrimeLowerBound P.d (Real.log x) :=
      Graph.source_prime_lower_bound_pos _ _
    rw [Real.rpow_one, div_lt_iff₀ hpos] at h4
    have h4' := mul_lt_mul_of_pos_left h4 hγ
    rw [← mul_assoc, mul_one_div_cancel hγ.ne', one_mul] at h4'
    exact h4'.le
  · exact he.trans (Real.exp_le_exp.mpr (by linarith))
  · have hN1 : (Graph.sourceMemoryLength (Real.log x) : ℝ) + 1 ≤
        5 * Real.log x ^ ((13 : ℝ) / 25) := by
      have hup := Graph.source_memory_length_upper (Real.log x) hL0.le
      have hone : (1 : ℝ) ≤ Real.log x ^ ((13 : ℝ) / 25) := Real.one_le_rpow hL1 (by norm_num)
      linarith
    have hD0 : 0 ≤ Real.log x ^ P.d := Real.rpow_nonneg hL0.le _
    have hT0 : 0 ≤ Real.log (Real.log x) := by linarith
    have h13 : 0 ≤ 5 * Real.log x ^ ((13 : ℝ) / 25) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg hL0.le _)
    have hpow : Real.log x ^ ((13 : ℝ) / 25) * Real.log x ^ ((12 : ℝ) / 25 - P.d) *
        Real.log x ^ P.d = Real.log x := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
      have hsum : (13 : ℝ) / 25 + (12 / 25 - P.d) + P.d = 1 := by ring
      rw [hsum, Real.rpow_one]
    have hprod : ((Graph.sourceMemoryLength (Real.log x) : ℝ) + 1) * Real.log (Real.log x) *
        Real.log x ^ P.d ≤ 5 * (γ / (10 * scalarConst P J A)) * Real.log x := by
      calc ((Graph.sourceMemoryLength (Real.log x) : ℝ) + 1) * Real.log (Real.log x) *
            Real.log x ^ P.d
          ≤ (5 * Real.log x ^ ((13 : ℝ) / 25)) *
              (γ / (10 * scalarConst P J A) * Real.log x ^ ((12 : ℝ) / 25 - P.d)) *
                Real.log x ^ P.d :=
            mul_le_mul_of_nonneg_right (mul_le_mul hN1 h5 hT0 h13) hD0
        _ = 5 * (γ / (10 * scalarConst P J A)) *
              (Real.log x ^ ((13 : ℝ) / 25) * Real.log x ^ ((12 : ℝ) / 25 - P.d) *
                Real.log x ^ P.d) := by ring
        _ = 5 * (γ / (10 * scalarConst P J A)) * Real.log x := by rw [hpow]
    have hfin : scalarConst P J A *
        (((Graph.sourceMemoryLength (Real.log x) : ℝ) + 1) * Real.log (Real.log x)) *
          Real.log x ^ P.d ≤ γ * Real.log x / 2 := by
      calc scalarConst P J A *
            (((Graph.sourceMemoryLength (Real.log x) : ℝ) + 1) * Real.log (Real.log x)) *
              Real.log x ^ P.d
          = scalarConst P J A *
              (((Graph.sourceMemoryLength (Real.log x) : ℝ) + 1) * Real.log (Real.log x) *
                Real.log x ^ P.d) := by ring
        _ ≤ scalarConst P J A * (5 * (γ / (10 * scalarConst P J A)) * Real.log x) :=
            mul_le_mul_of_nonneg_left hprod hC.le
        _ = γ * Real.log x / 2 := by
            field_simp
            ring
    linarith

section Final

variable {L T D Nn s γ A C₀ vp Mm : ℝ}

/-- `λ = (N + 1) s v₊ ≤ γ L`. -/
theorem residue_scalar_lam (hD : 1 ≤ D) (hT : 1 ≤ T) (hn : 0 ≤ Nn) (hs : s ≤ 2 * C₀ * T)
    (hC₀ : 0 < C₀) (hvp : 0 < vp) (hM : 0 ≤ Mm) (hA : 0 < A)
    (hmain : (12 * (2 * C₀ * vp) + 2 * C₀ * Mm + 3 * A + 6) * ((Nn + 1) * T) * D ≤
      γ * L - 4) : (Nn + 1) * s * vp ≤ γ * L := by
  have hU0 : 0 ≤ (Nn + 1) * T := mul_nonneg (by linarith) (by linarith)
  have hUD : (Nn + 1) * T ≤ (Nn + 1) * T * D := le_mul_of_one_le_right hU0 hD
  have hc1 : 0 ≤ 2 * C₀ * vp := mul_nonneg (mul_nonneg (by norm_num) hC₀.le) hvp.le
  have h1 : (Nn + 1) * s * vp ≤ (Nn + 1) * (2 * C₀ * T) * vp :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs (by linarith)) hvp.le
  have h2 : 2 * C₀ * vp * ((Nn + 1) * T) ≤ 2 * C₀ * vp * ((Nn + 1) * T * D) :=
    mul_le_mul_of_nonneg_left hUD hc1
  have h3 : 0 ≤ (22 * (C₀ * vp) + 2 * C₀ * Mm + 3 * A + 6) * ((Nn + 1) * T * D) := by
    refine mul_nonneg ?_ (hU0.trans hUD)
    have h4 : 0 ≤ C₀ * vp := mul_nonneg hC₀.le hvp.le
    have h5 : 0 ≤ C₀ * Mm := mul_nonneg hC₀.le hM
    linarith
  nlinarith [h1, h2, h3, hmain]

/-- **The relative error is at most `exp(-A N T)`** [S-02:0271–0286]. -/
theorem residue_scalar_final {QA w : ℝ} {K : ℕ} (hD : 1 ≤ D) (hT : 1 ≤ T) (hn : 0 ≤ Nn)
    (hs0 : 0 ≤ s) (hs : s ≤ 2 * C₀ * T) (hC₀ : 0 < C₀) (hvp : 0 < vp) (hM : 0 ≤ Mm)
    (hA : 0 < A)
    (hK1 : 5 * ((Nn + 1) * s * vp) + A * Nn * T + 1 ≤ (K : ℝ))
    (hK2 : (K : ℝ) ≤ 5 * ((Nn + 1) * s * vp) + A * Nn * T + 2)
    (hQA : QA ≤ Real.exp ((Nn + 1) * Mm * s * D))
    (hw : Real.exp (γ * L) - 1 ≤ w) (h2 : 2 ≤ Real.exp (γ * L))
    (hmain : (12 * (2 * C₀ * vp) + 2 * C₀ * Mm + 3 * A + 6) * ((Nn + 1) * T) * D ≤
      γ * L - 4) :
    Real.exp (2 * ((Nn + 1) * s * vp)) *
        (Real.exp (Real.exp 1 * ((Nn + 1) * s * vp)) / Real.exp 1 ^ (K + 1) +
          QA / w * (Real.exp (2 * D) ^ (K + 1) * Real.exp 1)) ≤
      Real.exp (-(A * Nn * T)) := by
  have hN1 : 0 ≤ Nn + 1 := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hD0 : 0 ≤ D := by linarith
  have hlam0 : 0 ≤ (Nn + 1) * s * vp := mul_nonneg (mul_nonneg hN1 hs0) hvp.le
  have hU1 : 1 ≤ (Nn + 1) * T := one_le_mul_of_one_le_of_one_le (by linarith) hT
  have hU0 : 0 ≤ (Nn + 1) * T := by linarith
  have hUD : (Nn + 1) * T ≤ (Nn + 1) * T * D := le_mul_of_one_le_right hU0 hD
  have hc1 : 0 ≤ 2 * C₀ * vp := mul_nonneg (mul_nonneg (by norm_num) hC₀.le) hvp.le
  have hlamU : (Nn + 1) * s * vp ≤ 2 * C₀ * vp * ((Nn + 1) * T) := by
    have h1 : (Nn + 1) * s * vp ≤ (Nn + 1) * (2 * C₀ * T) * vp :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hN1) hvp.le
    calc (Nn + 1) * s * vp ≤ (Nn + 1) * (2 * C₀ * T) * vp := h1
      _ = 2 * C₀ * vp * ((Nn + 1) * T) := by ring
  have hANT : A * Nn * T ≤ A * ((Nn + 1) * T) := by
    have h1 : Nn * T ≤ (Nn + 1) * T := mul_le_mul_of_nonneg_right (by linarith) hT0
    calc A * Nn * T = A * (Nn * T) := by ring
      _ ≤ A * ((Nn + 1) * T) := mul_le_mul_of_nonneg_left h1 hA.le
  -- the four monomial inequalities
  have m1 : 2 * ((Nn + 1) * s * vp) ≤ 2 * (2 * C₀ * vp) * ((Nn + 1) * T * D) := by
    have h1 := mul_le_mul_of_nonneg_left hUD hc1
    linarith
  have m2 : (Nn + 1) * Mm * s * D ≤ 2 * C₀ * Mm * ((Nn + 1) * T * D) := by
    have h1 : (Nn + 1) * Mm * s ≤ (Nn + 1) * Mm * (2 * C₀ * T) :=
      mul_le_mul_of_nonneg_left hs (mul_nonneg hN1 hM)
    calc (Nn + 1) * Mm * s * D ≤ (Nn + 1) * Mm * (2 * C₀ * T) * D :=
          mul_le_mul_of_nonneg_right h1 hD0
      _ = 2 * C₀ * Mm * ((Nn + 1) * T * D) := by ring
  have hKU : (K : ℝ) + 1 ≤ (10 * (C₀ * vp) + A + 3) * ((Nn + 1) * T) := by
    calc (K : ℝ) + 1 ≤ 5 * ((Nn + 1) * s * vp) + A * Nn * T + 3 := by linarith
      _ ≤ 5 * (2 * C₀ * vp * ((Nn + 1) * T)) + A * ((Nn + 1) * T) + 3 * ((Nn + 1) * T) := by
          linarith
      _ = (10 * (C₀ * vp) + A + 3) * ((Nn + 1) * T) := by ring
  have m3 : ((K : ℝ) + 1) * (2 * D) ≤
      2 * (10 * (C₀ * vp) + A + 3) * ((Nn + 1) * T * D) := by
    calc ((K : ℝ) + 1) * (2 * D) ≤ ((10 * (C₀ * vp) + A + 3) * ((Nn + 1) * T)) * (2 * D) :=
          mul_le_mul_of_nonneg_right hKU (by linarith)
      _ = 2 * (10 * (C₀ * vp) + A + 3) * ((Nn + 1) * T * D) := by ring
  have m4 : A * Nn * T ≤ A * ((Nn + 1) * T * D) :=
    hANT.trans (mul_le_mul_of_nonneg_left hUD hA.le)
  have hmain' : (12 * (2 * C₀ * vp) + 2 * C₀ * Mm + 3 * A + 6) * ((Nn + 1) * T * D) ≤
      γ * L - 4 := by
    calc (12 * (2 * C₀ * vp) + 2 * C₀ * Mm + 3 * A + 6) * ((Nn + 1) * T * D)
        = (12 * (2 * C₀ * vp) + 2 * C₀ * Mm + 3 * A + 6) * ((Nn + 1) * T) * D := by ring
      _ ≤ γ * L - 4 := hmain
  -- numerical constants
  have he3 : Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
  have hexp2 : Real.exp (-2) ≤ 1 / 2 := by
    have h3 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) h3
  have hexp3 : Real.exp (-3) ≤ 1 / 4 := by
    have h3 : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by norm_num) h3
  -- part 1: the Bonferroni remainder
  have hpow1 : Real.exp 1 ^ (K + 1) = Real.exp ((K : ℝ) + 1) := by
    rw [← Real.exp_nat_mul, Nat.cast_add_one, mul_one]
  have hpart1 : Real.exp (2 * ((Nn + 1) * s * vp)) *
      (Real.exp (Real.exp 1 * ((Nn + 1) * s * vp)) / Real.exp 1 ^ (K + 1)) ≤
        Real.exp (-(A * Nn * T)) / 2 := by
    rw [hpow1, ← Real.exp_sub, ← Real.exp_add]
    have hexp : 2 * ((Nn + 1) * s * vp) + (Real.exp 1 * ((Nn + 1) * s * vp) - ((K : ℝ) + 1)) ≤
        -(A * Nn * T) + -2 := by
      have h1 : Real.exp 1 * ((Nn + 1) * s * vp) ≤ 3 * ((Nn + 1) * s * vp) :=
        mul_le_mul_of_nonneg_right he3 hlam0
      linarith
    calc Real.exp (2 * ((Nn + 1) * s * vp) +
            (Real.exp 1 * ((Nn + 1) * s * vp) - ((K : ℝ) + 1)))
        ≤ Real.exp (-(A * Nn * T) + -2) := Real.exp_le_exp.mpr hexp
      _ = Real.exp (-(A * Nn * T)) * Real.exp (-2) := Real.exp_add _ _
      _ ≤ Real.exp (-(A * Nn * T)) * (1 / 2) :=
          mul_le_mul_of_nonneg_left hexp2 (Real.exp_pos _).le
      _ = Real.exp (-(A * Nn * T)) / 2 := by ring
  -- part 2: the counting error
  have hw' : Real.exp (γ * L) / 2 ≤ w := by linarith
  have hpow2 : Real.exp (2 * D) ^ (K + 1) = Real.exp (((K : ℝ) + 1) * (2 * D)) := by
    rw [← Real.exp_nat_mul, Nat.cast_add_one]
  have hQw : QA / w ≤ 2 * Real.exp ((Nn + 1) * Mm * s * D - γ * L) := by
    rw [Real.exp_sub]
    calc QA / w ≤ Real.exp ((Nn + 1) * Mm * s * D) / (Real.exp (γ * L) / 2) :=
          div_le_div₀ (Real.exp_pos _).le hQA (half_pos (Real.exp_pos _)) hw'
      _ = 2 * (Real.exp ((Nn + 1) * Mm * s * D) / Real.exp (γ * L)) := by
          field_simp
  have hpart2 : Real.exp (2 * ((Nn + 1) * s * vp)) *
      (QA / w * (Real.exp (2 * D) ^ (K + 1) * Real.exp 1)) ≤ Real.exp (-(A * Nn * T)) / 2 := by
    rw [hpow2]
    have hstep : Real.exp (2 * ((Nn + 1) * s * vp)) *
        (QA / w * (Real.exp (((K : ℝ) + 1) * (2 * D)) * Real.exp 1)) ≤
        Real.exp (2 * ((Nn + 1) * s * vp)) *
          (2 * Real.exp ((Nn + 1) * Mm * s * D - γ * L) *
            (Real.exp (((K : ℝ) + 1) * (2 * D)) * Real.exp 1)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hQw
          (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)) (Real.exp_pos _).le
    have hcomb : Real.exp (2 * ((Nn + 1) * s * vp)) *
        (2 * Real.exp ((Nn + 1) * Mm * s * D - γ * L) *
          (Real.exp (((K : ℝ) + 1) * (2 * D)) * Real.exp 1)) =
        2 * Real.exp (2 * ((Nn + 1) * s * vp) + ((Nn + 1) * Mm * s * D - γ * L) +
          ((K : ℝ) + 1) * (2 * D) + 1) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_add]
      ring
    have hexp : 2 * ((Nn + 1) * s * vp) + ((Nn + 1) * Mm * s * D - γ * L) +
        ((K : ℝ) + 1) * (2 * D) + 1 ≤ -(A * Nn * T) + -3 := by
      linarith [m1, m2, m3, m4, hmain']
    calc Real.exp (2 * ((Nn + 1) * s * vp)) *
          (QA / w * (Real.exp (((K : ℝ) + 1) * (2 * D)) * Real.exp 1))
        ≤ Real.exp (2 * ((Nn + 1) * s * vp)) *
          (2 * Real.exp ((Nn + 1) * Mm * s * D - γ * L) *
            (Real.exp (((K : ℝ) + 1) * (2 * D)) * Real.exp 1)) := hstep
      _ = 2 * Real.exp (2 * ((Nn + 1) * s * vp) + ((Nn + 1) * Mm * s * D - γ * L) +
          ((K : ℝ) + 1) * (2 * D) + 1) := hcomb
      _ ≤ 2 * Real.exp (-(A * Nn * T) + -3) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by norm_num)
      _ = 2 * (Real.exp (-(A * Nn * T)) * Real.exp (-3)) := by rw [Real.exp_add]
      _ ≤ 2 * (Real.exp (-(A * Nn * T)) * (1 / 4)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp3 (Real.exp_pos _).le)
            (by norm_num)
      _ = Real.exp (-(A * Nn * T)) / 2 := by ring
  rw [mul_add]
  linarith

end Final

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResRepl
