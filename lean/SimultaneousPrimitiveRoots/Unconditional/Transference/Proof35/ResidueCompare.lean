module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResidueBonferroni
public import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The proof of [S] Lemma 3.6, part 3: the integer average against the independent model

Source: `verification/stage7-sources/S-02.tex`, lines 255–289 (`[S-02:0255–0289]`).

The abstract setting of `ResidueBonferroni.lean`: pairwise coprime moduli `m i ≠ 0`, functions
`φ i : ZMod (m i) → ℝ`, `φ i ≥ 0` on `A` and `0 ≤ φ i ≤ 1` on `R`.

* `one_sided` — for every `K`, with the sign `(-1)^K`: the sum over `[a, b)` of
  `∏_{i ∈ A ∪ R} φ_i(n)` is at most `(b - a) ∏_A (rsum/m) ∏_R (1 - defect/m)` plus the Bonferroni
  remainder `exp(tλ)/t^{K+1}` (relative to the active part) plus the counting error
  `∏_A rsum · Z^K exp(ζ/Z)`.
* `abs_avg_sub_le` — **the relative estimate** used for Lemma 3.6.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResRepl

open scoped BigOperators

noncomputable section

variable {ι : Type*}

/-- `c · ∑_{|T| ≤ K} ∏_T (-μ_i)` with the signs written out. -/
theorem mul_truncSum_neg (c : ℝ) (μ : ι → ℝ) (K : ℕ) (R : Finset ι) :
    c * truncSum K R (fun i => -μ i) =
      ∑ T ∈ R.powerset, if T.card ≤ K then (-1 : ℝ) ^ T.card * (c * ∏ i ∈ T, μ i) else 0 := by
  rw [truncSum_neg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hT : T.card ≤ K
  · simp only [hT, ↓reduceIte]
    ring
  · simp only [hT, ↓reduceIte, mul_zero]

/-- A weighted sum of truncated expansions, term by term. -/
theorem sum_mul_truncSum_neg {α : Type*} (s : Finset α) (c : α → ℝ) (x : α → ι → ℝ) (K : ℕ)
    (R : Finset ι) :
    ∑ n ∈ s, c n * truncSum K R (fun i => -x n i) =
      ∑ T ∈ R.powerset,
        if T.card ≤ K then (-1 : ℝ) ^ T.card * ∑ n ∈ s, c n * ∏ i ∈ T, x n i else 0 := by
  rw [Finset.sum_congr rfl fun n _ => mul_truncSum_neg (c n) (x n) K R, Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  by_cases hT : T.card ≤ K
  · simp only [hT, ↓reduceIte]
    rw [Finset.mul_sum]
  · simp only [hT, ↓reduceIte, Finset.sum_const_zero]

variable [DecidableEq ι] (m : ι → ℕ) [∀ i, NeZero (m i)]

/-- **The integer sum against the independent model, one side** [S-02:0268–0289]. For every `K`,
with the sign `(-1)^K` (Bonferroni: upper bound for even `K`, lower bound for odd `K`). -/
theorem one_sided (hm : Pairwise (Function.onFun Nat.Coprime m))
    (φ : (i : ι) → ZMod (m i) → ℝ) {A R : Finset ι} (hAR : Disjoint A R)
    (hA : ∀ i ∈ A, ∀ u, 0 ≤ φ i u) (hR0 : ∀ i ∈ R, ∀ u, 0 ≤ φ i u)
    (hR1 : ∀ i ∈ R, ∀ u, φ i u ≤ 1) {a b : ℤ} (hab : a ≤ b) {t Z : ℝ} (ht : 0 < t)
    (hZ : 1 ≤ Z) (K : ℕ) :
    (-1 : ℝ) ^ K * (∑ n ∈ Finset.Ico a b, ∏ i ∈ A ∪ R, φ i (n : ZMod (m i)) -
        ((b : ℝ) - a) * ((∏ i ∈ A, (rsum m φ i / (m i : ℝ))) *
          ∏ i ∈ R, (1 - defect m φ i / (m i : ℝ)))) ≤
      ((b : ℝ) - a) * (∏ i ∈ A, (rsum m φ i / (m i : ℝ))) *
          (Real.exp (t * ∑ i ∈ R, defect m φ i / (m i : ℝ)) / t ^ (K + 1)) +
        (∏ i ∈ A, rsum m φ i) * (Z ^ K * Real.exp ((∑ i ∈ R, defect m φ i) / Z)) := by
  have hw0 : (0 : ℝ) ≤ (b : ℝ) - a := sub_nonneg.mpr (by exact_mod_cast hab)
  have hMA0 : 0 ≤ ∏ i ∈ A, (rsum m φ i / (m i : ℝ)) :=
    Finset.prod_nonneg fun i hi => div_nonneg (rsum_nonneg m φ (hA i hi)) (Nat.cast_nonneg _)
  have hSA0 : 0 ≤ ∏ i ∈ A, rsum m φ i :=
    Finset.prod_nonneg fun i hi => rsum_nonneg m φ (hA i hi)
  have hμ0 : ∀ i ∈ R, 0 ≤ defect m φ i / (m i : ℝ) := fun i hi =>
    div_nonneg (defect_nonneg m φ (hR1 i hi)) (Nat.cast_nonneg _)
  have hμ1 : ∀ i ∈ R, defect m φ i / (m i : ℝ) ≤ 1 := fun i hi => by
    have hpos : (0 : ℝ) < (m i : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne (m i)))
    rw [div_le_one hpos]
    exact defect_le m φ (hR0 i hi)
  have hPA0 : ∀ n : ℤ, 0 ≤ ∏ i ∈ A, φ i (n : ZMod (m i)) := fun n =>
    Finset.prod_nonneg fun i hi => hA i hi _
  -- Step 1: Bonferroni at every integer, weighted by the active part
  have hstep1 : 0 ≤ (-1 : ℝ) ^ K *
      (∑ n ∈ Finset.Ico a b, (∏ i ∈ A, φ i (n : ZMod (m i))) *
            truncSum K R (fun i => -(1 - φ i (n : ZMod (m i)))) -
        ∑ n ∈ Finset.Ico a b, ∏ i ∈ A ∪ R, φ i (n : ZMod (m i))) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_nonneg fun n _ => ?_
    have hb := (bonferroni_aux (fun i => 1 - φ i (n : ZMod (m i))) one_pos R
      (fun i hi => sub_nonneg.mpr (hR1 i hi _))
      (fun i hi => by linarith [hR0 i hi (n : ZMod (m i))]) K).1
    have hprod : ∏ i ∈ R, (1 - (1 - φ i (n : ZMod (m i)))) = ∏ i ∈ R, φ i (n : ZMod (m i)) :=
      Finset.prod_congr rfl fun i _ => sub_sub_cancel _ _
    rw [hprod] at hb
    have heq : (-1 : ℝ) ^ K * ((∏ i ∈ A, φ i (n : ZMod (m i))) *
          truncSum K R (fun i => -(1 - φ i (n : ZMod (m i)))) -
            ∏ i ∈ A ∪ R, φ i (n : ZMod (m i))) =
        (∏ i ∈ A, φ i (n : ZMod (m i))) * ((-1 : ℝ) ^ K *
          (truncSum K R (fun i => -(1 - φ i (n : ZMod (m i)))) -
            ∏ i ∈ R, φ i (n : ZMod (m i)))) := by
      rw [Finset.prod_union hAR]
      ring
    rw [heq]
    exact mul_nonneg (hPA0 n) hb
  -- Step 2: the CRT count of every truncated term
  have hstep2 : |∑ n ∈ Finset.Ico a b, (∏ i ∈ A, φ i (n : ZMod (m i))) *
          truncSum K R (fun i => -(1 - φ i (n : ZMod (m i)))) -
        ((b : ℝ) - a) * (∏ i ∈ A, (rsum m φ i / (m i : ℝ))) *
          truncSum K R (fun i => -(defect m φ i / (m i : ℝ)))| ≤
      (∏ i ∈ A, rsum m φ i) * truncSum K R (defect m φ) := by
    rw [sum_mul_truncSum_neg (Finset.Ico a b) (fun n : ℤ => ∏ i ∈ A, φ i (n : ZMod (m i)))
        (fun (n : ℤ) i => 1 - φ i (n : ZMod (m i))) K R,
      mul_truncSum_neg (((b : ℝ) - a) * ∏ i ∈ A, (rsum m φ i / (m i : ℝ)))
        (fun i => defect m φ i / (m i : ℝ)) K R, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    unfold truncSum
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun T hT => ?_
    by_cases hTK : T.card ≤ K
    · simp only [hTK, ↓reduceIte]
      rw [← mul_sub, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, mul_assoc]
      have hTR : T ⊆ R := Finset.mem_powerset.mp hT
      exact mixed_count m hm φ (Finset.disjoint_of_subset_right hTR hAR) hA
        (fun i hi => hR1 i (hTR hi)) hab
    · simp only [hTK, ↓reduceIte, sub_self, abs_zero, mul_zero, le_refl]
  -- Step 3: Bonferroni for the means, with the Rankin bound
  have hstep3 := (bonferroni_aux (fun i => defect m φ i / (m i : ℝ)) ht R hμ0 hμ1 K).2
  -- Step 4: the number of truncated terms
  have hstep4 := truncSum_le (defect m φ) hZ R (fun i hi => defect_nonneg m φ (hR1 i hi)) K
  have hσ : |(-1 : ℝ) ^ K| = 1 := by rw [abs_pow, abs_neg, abs_one, one_pow]
  have h5 : (-1 : ℝ) ^ K * (∑ n ∈ Finset.Ico a b, (∏ i ∈ A, φ i (n : ZMod (m i))) *
          truncSum K R (fun i => -(1 - φ i (n : ZMod (m i)))) -
        ((b : ℝ) - a) * (∏ i ∈ A, (rsum m φ i / (m i : ℝ))) *
          truncSum K R (fun i => -(defect m φ i / (m i : ℝ)))) ≤
      (∏ i ∈ A, rsum m φ i) * (Z ^ K * Real.exp ((∑ i ∈ R, defect m φ i) / Z)) := by
    refine (le_abs_self _).trans ?_
    rw [abs_mul, hσ, one_mul]
    exact hstep2.trans (mul_le_mul_of_nonneg_left hstep4 hSA0)
  have h6 : ((b : ℝ) - a) * (∏ i ∈ A, (rsum m φ i / (m i : ℝ))) *
        ((-1 : ℝ) ^ K * (truncSum K R (fun i => -(defect m φ i / (m i : ℝ))) -
          ∏ i ∈ R, (1 - defect m φ i / (m i : ℝ)))) ≤
      ((b : ℝ) - a) * (∏ i ∈ A, (rsum m φ i / (m i : ℝ))) *
        (Real.exp (t * ∑ i ∈ R, defect m φ i / (m i : ℝ)) / t ^ (K + 1)) :=
    mul_le_mul_of_nonneg_left hstep3 (mul_nonneg hw0 hMA0)
  have h7 : (-1 : ℝ) ^ K * (∑ n ∈ Finset.Ico a b, ∏ i ∈ A ∪ R, φ i (n : ZMod (m i)) -
        ((b : ℝ) - a) * ((∏ i ∈ A, (rsum m φ i / (m i : ℝ))) *
          ∏ i ∈ R, (1 - defect m φ i / (m i : ℝ)))) =
      -((-1 : ℝ) ^ K *
          (∑ n ∈ Finset.Ico a b, (∏ i ∈ A, φ i (n : ZMod (m i))) *
              truncSum K R (fun i => -(1 - φ i (n : ZMod (m i)))) -
            ∑ n ∈ Finset.Ico a b, ∏ i ∈ A ∪ R, φ i (n : ZMod (m i)))) +
        (-1 : ℝ) ^ K * (∑ n ∈ Finset.Ico a b, (∏ i ∈ A, φ i (n : ZMod (m i))) *
            truncSum K R (fun i => -(1 - φ i (n : ZMod (m i)))) -
          ((b : ℝ) - a) * (∏ i ∈ A, (rsum m φ i / (m i : ℝ))) *
            truncSum K R (fun i => -(defect m φ i / (m i : ℝ)))) +
        ((b : ℝ) - a) * (∏ i ∈ A, (rsum m φ i / (m i : ℝ))) *
          ((-1 : ℝ) ^ K * (truncSum K R (fun i => -(defect m φ i / (m i : ℝ))) -
            ∏ i ∈ R, (1 - defect m φ i / (m i : ℝ)))) := by
    ring
  rw [h7]
  linarith

/-- **The relative estimate** [S-02:0255–0289]: the average over the integers of `[a, b)` of
`∏_{i ∈ A ∪ R} φ_i(n)` equals the product of the means `∏_{i ∈ A ∪ R} rsum φ i / m i`, with a
relative error `exp(2λ)(exp(tλ)/t^{K+1} + (∏_{i ∈ A} m_i/(b - a)) Z^{K+1} e)`, where `λ` bounds
the sum over `R` of `defect/m` and `Z` bounds the sum over `R` of `defect`. If some active mean
vanishes, both sides are `0`. -/
theorem abs_avg_sub_le (hm : Pairwise (Function.onFun Nat.Coprime m))
    (φ : (i : ι) → ZMod (m i) → ℝ) {A R : Finset ι} (hAR : Disjoint A R)
    (hA : ∀ i ∈ A, ∀ u, 0 ≤ φ i u) (hR0 : ∀ i ∈ R, ∀ u, 0 ≤ φ i u)
    (hR1 : ∀ i ∈ R, ∀ u, φ i u ≤ 1) {a b : ℤ} (hab : a < b)
    (hhalf : ∀ i ∈ R, defect m φ i / (m i : ℝ) ≤ 1 / 2) {lam t Z : ℝ} (ht : 1 ≤ t)
    (hZ : 1 ≤ Z) (hlam : ∑ i ∈ R, defect m φ i / (m i : ℝ) ≤ lam)
    (hζ : ∑ i ∈ R, defect m φ i ≤ Z) (K : ℕ) :
    |((b : ℝ) - a)⁻¹ * ∑ n ∈ Finset.Ico a b, ∏ i ∈ A ∪ R, φ i (n : ZMod (m i)) -
        ∏ i ∈ A ∪ R, (rsum m φ i / (m i : ℝ))| ≤
      Real.exp (2 * lam) * (Real.exp (t * lam) / t ^ (K + 1) +
          (∏ i ∈ A, (m i : ℝ)) / ((b : ℝ) - a) * (Z ^ (K + 1) * Real.exp 1)) *
        ∏ i ∈ A ∪ R, (rsum m φ i / (m i : ℝ)) := by
  have hw : (0 : ℝ) < (b : ℝ) - a := sub_pos.mpr (by exact_mod_cast hab)
  have ht0 : 0 < t := by linarith
  have hZ0 : 0 < Z := by linarith
  have hMA0 : 0 ≤ ∏ i ∈ A, (rsum m φ i / (m i : ℝ)) :=
    Finset.prod_nonneg fun i hi => div_nonneg (rsum_nonneg m φ (hA i hi)) (Nat.cast_nonneg _)
  have hSA0 : 0 ≤ ∏ i ∈ A, rsum m φ i :=
    Finset.prod_nonneg fun i hi => rsum_nonneg m φ (hA i hi)
  have hQA : 0 < ∏ i ∈ A, (m i : ℝ) :=
    Finset.prod_pos fun i _ => Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne (m i)))
  have hSA : ∏ i ∈ A, rsum m φ i =
      (∏ i ∈ A, (rsum m φ i / (m i : ℝ))) * ∏ i ∈ A, (m i : ℝ) := by
    rw [Finset.prod_div_distrib, div_mul_cancel₀ _ hQA.ne']
  have hμ0 : ∀ i ∈ R, 0 ≤ defect m φ i / (m i : ℝ) := fun i hi =>
    div_nonneg (defect_nonneg m φ (hR1 i hi)) (Nat.cast_nonneg _)
  have hE : ∏ i ∈ A ∪ R, (rsum m φ i / (m i : ℝ)) =
      (∏ i ∈ A, (rsum m φ i / (m i : ℝ))) * ∏ i ∈ R, (1 - defect m φ i / (m i : ℝ)) := by
    rw [Finset.prod_union hAR]
    congr 1
    exact Finset.prod_congr rfl fun i _ => rsum_div_eq m φ i
  have hP : Real.exp (-(2 * lam)) ≤ ∏ i ∈ R, (1 - defect m φ i / (m i : ℝ)) :=
    (Real.exp_le_exp.mpr (by linarith)).trans (exp_neg_le_prod_one_sub R _ hμ0 hhalf)
  have h1 := one_sided m hm φ hAR hA hR0 hR1 hab.le ht0 hZ K
  have h2 := one_sided m hm φ hAR hA hR0 hR1 hab.le ht0 hZ (K + 1)
  have hexp1 : Real.exp (t * ∑ i ∈ R, defect m φ i / (m i : ℝ)) ≤ Real.exp (t * lam) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlam ht0.le)
  have hexp2 : Real.exp ((∑ i ∈ R, defect m φ i) / Z) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr ((div_le_one hZ0).mpr hζ)
  have hU1 : ((b : ℝ) - a) * (∏ i ∈ A, (rsum m φ i / (m i : ℝ))) *
        (Real.exp (t * ∑ i ∈ R, defect m φ i / (m i : ℝ)) / t ^ (K + 1)) +
      (∏ i ∈ A, rsum m φ i) * (Z ^ K * Real.exp ((∑ i ∈ R, defect m φ i) / Z)) ≤
      ((b : ℝ) - a) * (∏ i ∈ A, (rsum m φ i / (m i : ℝ))) *
        (Real.exp (t * lam) / t ^ (K + 1)) +
      (∏ i ∈ A, rsum m φ i) * (Z ^ (K + 1) * Real.exp 1) := by
    refine add_le_add ?_ ?_
    · exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hexp1 (by positivity))
        (mul_nonneg hw.le hMA0)
    · exact mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_right₀ hZ (Nat.le_succ K)) hexp2
        (Real.exp_pos _).le (by positivity)) hSA0
  have hU2 : ((b : ℝ) - a) * (∏ i ∈ A, (rsum m φ i / (m i : ℝ))) *
        (Real.exp (t * ∑ i ∈ R, defect m φ i / (m i : ℝ)) / t ^ (K + 1 + 1)) +
      (∏ i ∈ A, rsum m φ i) * (Z ^ (K + 1) * Real.exp ((∑ i ∈ R, defect m φ i) / Z)) ≤
      ((b : ℝ) - a) * (∏ i ∈ A, (rsum m φ i / (m i : ℝ))) *
        (Real.exp (t * lam) / t ^ (K + 1)) +
      (∏ i ∈ A, rsum m φ i) * (Z ^ (K + 1) * Real.exp 1) := by
    refine add_le_add ?_ ?_
    · exact mul_le_mul_of_nonneg_left (div_le_div₀ (Real.exp_pos _).le hexp1 (by positivity)
        (pow_le_pow_right₀ ht (Nat.le_succ (K + 1)))) (mul_nonneg hw.le hMA0)
    · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp2 (by positivity)) hSA0
  have habs : |∑ n ∈ Finset.Ico a b, ∏ i ∈ A ∪ R, φ i (n : ZMod (m i)) -
        ((b : ℝ) - a) * ((∏ i ∈ A, (rsum m φ i / (m i : ℝ))) *
          ∏ i ∈ R, (1 - defect m φ i / (m i : ℝ)))| ≤
      ((b : ℝ) - a) * (∏ i ∈ A, (rsum m φ i / (m i : ℝ))) *
        (Real.exp (t * lam) / t ^ (K + 1)) +
      (∏ i ∈ A, rsum m φ i) * (Z ^ (K + 1) * Real.exp 1) := by
    rcases Nat.even_or_odd K with hK | hK
    · rw [hK.neg_one_pow, one_mul] at h1
      rw [hK.add_one.neg_one_pow, neg_one_mul] at h2
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · rw [hK.neg_one_pow, neg_one_mul] at h1
      rw [hK.add_one.neg_one_pow, one_mul] at h2
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hG0 : 0 ≤ Real.exp (t * lam) / t ^ (K + 1) +
      (∏ i ∈ A, (m i : ℝ)) / ((b : ℝ) - a) * (Z ^ (K + 1) * Real.exp 1) := by positivity
  have hMAE : ∏ i ∈ A, (rsum m φ i / (m i : ℝ)) ≤
      Real.exp (2 * lam) * ∏ i ∈ A ∪ R, (rsum m φ i / (m i : ℝ)) := by
    rw [hE]
    have h3 : (∏ i ∈ A, (rsum m φ i / (m i : ℝ))) *
          (Real.exp (2 * lam) * Real.exp (-(2 * lam))) ≤
        Real.exp (2 * lam) * ((∏ i ∈ A, (rsum m φ i / (m i : ℝ))) *
          ∏ i ∈ R, (1 - defect m φ i / (m i : ℝ))) := by
      calc (∏ i ∈ A, (rsum m φ i / (m i : ℝ))) * (Real.exp (2 * lam) * Real.exp (-(2 * lam)))
          = Real.exp (2 * lam) *
              ((∏ i ∈ A, (rsum m φ i / (m i : ℝ))) * Real.exp (-(2 * lam))) := by ring
        _ ≤ Real.exp (2 * lam) * ((∏ i ∈ A, (rsum m φ i / (m i : ℝ))) *
              ∏ i ∈ R, (1 - defect m φ i / (m i : ℝ))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP hMA0) (Real.exp_pos _).le
    rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at h3
  have hfin : ((b : ℝ) - a)⁻¹ * ∑ n ∈ Finset.Ico a b, ∏ i ∈ A ∪ R, φ i (n : ZMod (m i)) -
        ∏ i ∈ A ∪ R, (rsum m φ i / (m i : ℝ)) =
      ((b : ℝ) - a)⁻¹ * (∑ n ∈ Finset.Ico a b, ∏ i ∈ A ∪ R, φ i (n : ZMod (m i)) -
        ((b : ℝ) - a) * ((∏ i ∈ A, (rsum m φ i / (m i : ℝ))) *
          ∏ i ∈ R, (1 - defect m φ i / (m i : ℝ)))) := by
    rw [hE]
    field_simp
  rw [hfin, abs_mul, abs_of_pos (inv_pos.mpr hw)]
  calc ((b : ℝ) - a)⁻¹ * |∑ n ∈ Finset.Ico a b, ∏ i ∈ A ∪ R, φ i (n : ZMod (m i)) -
          ((b : ℝ) - a) * ((∏ i ∈ A, (rsum m φ i / (m i : ℝ))) *
            ∏ i ∈ R, (1 - defect m φ i / (m i : ℝ)))|
      ≤ ((b : ℝ) - a)⁻¹ * (((b : ℝ) - a) * (∏ i ∈ A, (rsum m φ i / (m i : ℝ))) *
            (Real.exp (t * lam) / t ^ (K + 1)) +
          (∏ i ∈ A, rsum m φ i) * (Z ^ (K + 1) * Real.exp 1)) :=
        mul_le_mul_of_nonneg_left habs (inv_pos.mpr hw).le
    _ = (∏ i ∈ A, (rsum m φ i / (m i : ℝ))) * (Real.exp (t * lam) / t ^ (K + 1) +
          (∏ i ∈ A, (m i : ℝ)) / ((b : ℝ) - a) * (Z ^ (K + 1) * Real.exp 1)) := by
        rw [hSA]
        field_simp
    _ ≤ (Real.exp (2 * lam) * ∏ i ∈ A ∪ R, (rsum m φ i / (m i : ℝ))) *
          (Real.exp (t * lam) / t ^ (K + 1) +
            (∏ i ∈ A, (m i : ℝ)) / ((b : ℝ) - a) * (Z ^ (K + 1) * Real.exp 1)) :=
        mul_le_mul_of_nonneg_right hMAE hG0
    _ = Real.exp (2 * lam) * (Real.exp (t * lam) / t ^ (K + 1) +
          (∏ i ∈ A, (m i : ℝ)) / ((b : ℝ) - a) * (Z ^ (K + 1) * Real.exp 1)) *
        ∏ i ∈ A ∪ R, (rsum m φ i / (m i : ℝ)) := by ring

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResRepl
