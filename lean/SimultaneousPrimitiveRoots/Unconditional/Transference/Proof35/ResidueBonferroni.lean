module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResidueCRT
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The proof of [S] Lemma 3.6, part 2: Bonferroni and the comparison of the two models

Source: `verification/stage7-sources/S-02.tex`, lines 255–289 (`[S-02:0255–0289]`).

The setting is abstract: pairwise coprime moduli `m i ≠ 0`, functions `φ i : ZMod (m i) → ℝ`, a
finite set `A` of indices where only `φ i ≥ 0` is known (the active primes) and a finite set `R`
where `0 ≤ φ i ≤ 1` (the remaining primes; `X_i = 1 - φ_i` is the function `X_p` of the
manuscript). `rsum φ i = ∑_u φ_i(u)`, `defect φ i = ∑_u (1 - φ_i(u))`, so that the mean of `φ_i` is
`rsum/m = 1 - defect/m`.

* `truncSum K R y = ∑_{T ⊆ R, |T| ≤ K} ∏_{i ∈ T} y_i`, the truncation at degree `K` of the
  elementary-symmetric expansion of `∏_{i ∈ R} (1 + y_i)`.
* `bonferroni_aux` — "Bonferroni inequalities for numbers in `[0,1]` bracket `∏_p (1 - X_p)` by
  consecutive truncations of its elementary-symmetric expansion" [S-02:0268–0270], together with
  the bound for the difference. The manuscript bounds the difference by `λ^h/h!` and uses
  Stirling; here the bound is `exp(tλ)/t^{K+1}` for every `t > 0` (Rankin's trick), which is
  proved by the same induction and needs no factorial.
* `truncSum_le` — `∑_{T ⊆ R, |T| ≤ K} ∏_{i ∈ T} z_i ≤ Z^K exp(∑ z_i / Z)`, the bound for the
  total counting error ("the number of such terms is at most …" [S-02:0280–0284]).
* `mixed_count` — the weighted CRT count for `∏_{i ∈ A} φ_i · ∏_{i ∈ T} (1 - φ_i)`.
* `one_sided` — the integer sum against the independent model, with the sign `(-1)^K`.
* `abs_avg_sub_le` — **the relative estimate**: the average over `[a, b)` of
  `∏_{i ∈ A ∪ R} φ_i(n)` equals `∏_{i ∈ A ∪ R} (rsum φ i / m i)` up to the relative error
  `exp(2λ) (exp(tλ)/t^{K+1} + (∏_{i ∈ A} m_i/(b - a)) Z^{K+1} e)`. No compatibility hypothesis is
  needed: if the active congruences are incompatible, some mean vanishes and both sides are `0`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResRepl

open scoped BigOperators

noncomputable section

variable {ι : Type*}

/-! ### Truncated expansions -/

/-- `∑_{T ⊆ R, |T| ≤ K} ∏_{i ∈ T} y_i`. -/
def truncSum (K : ℕ) (R : Finset ι) (y : ι → ℝ) : ℝ :=
  ∑ T ∈ R.powerset, if T.card ≤ K then ∏ i ∈ T, y i else 0

theorem truncSum_empty (K : ℕ) (y : ι → ℝ) : truncSum K ∅ y = 1 := by
  simp [truncSum]

theorem truncSum_zero (R : Finset ι) (y : ι → ℝ) : truncSum 0 R y = 1 := by
  unfold truncSum
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro T _ hT
    have h : ¬T.card ≤ 0 := by
      rw [Nat.le_zero, Finset.card_eq_zero]
      exact hT
    simp [h]
  · intro h
    exact absurd (Finset.empty_mem_powerset R) h

theorem truncSum_succ_insert [DecidableEq ι] {a : ι} {R : Finset ι} (ha : a ∉ R) (K : ℕ) (y : ι → ℝ) :
    truncSum (K + 1) (insert a R) y = truncSum (K + 1) R y + y a * truncSum K R y := by
  unfold truncSum
  rw [Finset.sum_powerset_insert ha, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun T hT => ?_
  have haT : a ∉ T := fun h => ha (Finset.mem_powerset.mp hT h)
  rw [Finset.card_insert_of_notMem haT, Finset.prod_insert haT]
  by_cases h : T.card ≤ K
  · simp [h]
  · simp [h]

/-- The truncated expansion at `-x`, with the signs written out. -/
theorem truncSum_neg (K : ℕ) (R : Finset ι) (x : ι → ℝ) :
    truncSum K R (fun i => -x i) =
      ∑ T ∈ R.powerset, if T.card ≤ K then (-1 : ℝ) ^ T.card * ∏ i ∈ T, x i else 0 := by
  unfold truncSum
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.prod_neg]

/-- **Bonferroni's inequalities** for numbers in `[0,1]` [S-02:0268–0273]: the truncation at
degree `K` of the expansion of `∏ (1 - x_i)` is an upper bound for even `K` and a lower bound for
odd `K`, and it differs from the product by at most `exp(t ∑ x_i)/t^{K+1}`, for every `t > 0`. -/
theorem bonferroni_aux [DecidableEq ι] (x : ι → ℝ) {t : ℝ} (ht : 0 < t) (R : Finset ι)
    (hx0 : ∀ i ∈ R, 0 ≤ x i) (hx1 : ∀ i ∈ R, x i ≤ 1) :
    ∀ K : ℕ, 0 ≤ (-1 : ℝ) ^ K * (truncSum K R (fun i => -x i) - ∏ i ∈ R, (1 - x i)) ∧
      (-1 : ℝ) ^ K * (truncSum K R (fun i => -x i) - ∏ i ∈ R, (1 - x i)) ≤
        Real.exp (t * ∑ i ∈ R, x i) / t ^ (K + 1) := by
  induction R using Finset.induction_on with
  | empty =>
    intro K
    rw [truncSum_empty, Finset.prod_empty, sub_self, mul_zero]
    exact ⟨le_rfl, by positivity⟩
  | insert a R ha ih =>
    have hx0' : ∀ i ∈ R, 0 ≤ x i := fun i hi => hx0 i (Finset.mem_insert_of_mem hi)
    have hx1' : ∀ i ∈ R, x i ≤ 1 := fun i hi => hx1 i (Finset.mem_insert_of_mem hi)
    have ih' := ih hx0' hx1'
    have ha0 : 0 ≤ x a := hx0 a (Finset.mem_insert_self a R)
    have ha1 : x a ≤ 1 := hx1 a (Finset.mem_insert_self a R)
    have hP0 : 0 ≤ ∏ i ∈ R, (1 - x i) :=
      Finset.prod_nonneg fun i hi => sub_nonneg.mpr (hx1' i hi)
    have hP1 : ∏ i ∈ R, (1 - x i) ≤ 1 :=
      Finset.prod_le_one (fun i hi => sub_nonneg.mpr (hx1' i hi)) fun i hi => by
        linarith [hx0' i hi]
    have hexp : Real.exp (t * ∑ i ∈ insert a R, x i) =
        Real.exp (t * x a) * Real.exp (t * ∑ i ∈ R, x i) := by
      rw [Finset.sum_insert ha, mul_add, Real.exp_add]
    have h1 : 1 + t * x a ≤ Real.exp (t * x a) := by linarith [Real.add_one_le_exp (t * x a)]
    have hE : 0 < Real.exp (t * ∑ i ∈ R, x i) := Real.exp_pos _
    have hE1 : 1 ≤ Real.exp (t * ∑ i ∈ R, x i) :=
      Real.one_le_exp (mul_nonneg ht.le (Finset.sum_nonneg hx0'))
    intro K
    rw [Finset.prod_insert ha, hexp]
    cases K with
    | zero =>
      obtain ⟨-, hub⟩ := ih' 0
      rw [truncSum_zero] at hub
      rw [truncSum_zero]
      simp only [pow_zero, one_mul, zero_add, pow_one] at hub ⊢
      have h5 : x a * ∏ i ∈ R, (1 - x i) ≤ x a := mul_le_of_le_one_right ha0 hP1
      have h6 : 0 ≤ x a * ∏ i ∈ R, (1 - x i) := mul_nonneg ha0 hP0
      constructor
      · linarith
      · have h2 : (1 + t * x a) * Real.exp (t * ∑ i ∈ R, x i) / t ≤
            Real.exp (t * x a) * Real.exp (t * ∑ i ∈ R, x i) / t :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hE.le) ht.le
        have h3 : (1 + t * x a) * Real.exp (t * ∑ i ∈ R, x i) / t =
            Real.exp (t * ∑ i ∈ R, x i) / t + x a * Real.exp (t * ∑ i ∈ R, x i) := by
          field_simp
        have h4 : x a ≤ x a * Real.exp (t * ∑ i ∈ R, x i) := le_mul_of_one_le_right ha0 hE1
        linarith
    | succ K =>
      obtain ⟨h0K, hubK⟩ := ih' K
      obtain ⟨h0K1, hubK1⟩ := ih' (K + 1)
      rw [truncSum_succ_insert ha]
      have key : (-1 : ℝ) ^ (K + 1) * (truncSum (K + 1) R (fun i => -x i) +
            -x a * truncSum K R (fun i => -x i) - (1 - x a) * ∏ i ∈ R, (1 - x i)) =
          (-1 : ℝ) ^ (K + 1) * (truncSum (K + 1) R (fun i => -x i) - ∏ i ∈ R, (1 - x i)) +
            x a * ((-1 : ℝ) ^ K * (truncSum K R (fun i => -x i) - ∏ i ∈ R, (1 - x i))) := by
        rw [pow_succ]
        ring
      rw [key]
      constructor
      · exact add_nonneg h0K1 (mul_nonneg ha0 h0K)
      · have h2 : (1 + t * x a) * Real.exp (t * ∑ i ∈ R, x i) / t ^ (K + 1 + 1) ≤
            Real.exp (t * x a) * Real.exp (t * ∑ i ∈ R, x i) / t ^ (K + 1 + 1) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hE.le) (by positivity)
        have h3 : (1 + t * x a) * Real.exp (t * ∑ i ∈ R, x i) / t ^ (K + 1 + 1) =
            Real.exp (t * ∑ i ∈ R, x i) / t ^ (K + 1 + 1) +
              x a * (Real.exp (t * ∑ i ∈ R, x i) / t ^ (K + 1)) := by
          rw [pow_succ t (K + 1)]
          field_simp
        have h4 : x a * ((-1 : ℝ) ^ K * (truncSum K R (fun i => -x i) - ∏ i ∈ R, (1 - x i))) ≤
            x a * (Real.exp (t * ∑ i ∈ R, x i) / t ^ (K + 1)) :=
          mul_le_mul_of_nonneg_left hubK ha0
        linarith

/-- The truncated expansion with nonnegative entries: `∑_{T ⊆ R, |T| ≤ K} ∏_{i ∈ T} z_i ≤
Z^K exp(∑ z_i / Z)` for `Z ≥ 1`. -/
theorem truncSum_le [DecidableEq ι] (z : ι → ℝ) {Z : ℝ} (hZ : 1 ≤ Z) (R : Finset ι) (hz : ∀ i ∈ R, 0 ≤ z i) :
    ∀ K : ℕ, truncSum K R z ≤ Z ^ K * Real.exp ((∑ i ∈ R, z i) / Z) := by
  have hZ0 : 0 < Z := by linarith
  induction R using Finset.induction_on with
  | empty =>
    intro K
    rw [truncSum_empty, Finset.sum_empty, zero_div, Real.exp_zero, mul_one]
    exact one_le_pow₀ hZ
  | insert a R ha ih =>
    have hz' : ∀ i ∈ R, 0 ≤ z i := fun i hi => hz i (Finset.mem_insert_of_mem hi)
    have ih' := ih hz'
    have ha0 : 0 ≤ z a := hz a (Finset.mem_insert_self a R)
    have hexp : Real.exp ((∑ i ∈ insert a R, z i) / Z) =
        Real.exp (z a / Z) * Real.exp ((∑ i ∈ R, z i) / Z) := by
      rw [Finset.sum_insert ha, add_div, Real.exp_add]
    have h1 : 1 + z a / Z ≤ Real.exp (z a / Z) := by linarith [Real.add_one_le_exp (z a / Z)]
    have hEa : 1 ≤ Real.exp (z a / Z) := Real.one_le_exp (div_nonneg ha0 hZ0.le)
    have hER : 1 ≤ Real.exp ((∑ i ∈ R, z i) / Z) :=
      Real.one_le_exp (div_nonneg (Finset.sum_nonneg hz') hZ0.le)
    intro K
    rw [hexp]
    cases K with
    | zero =>
      rw [truncSum_zero, pow_zero, one_mul]
      exact one_le_mul_of_one_le_of_one_le hEa hER
    | succ K =>
      rw [truncSum_succ_insert ha]
      have hK := ih' K
      have hK1 := ih' (K + 1)
      have h2 : z a * truncSum K R z ≤ z a * (Z ^ K * Real.exp ((∑ i ∈ R, z i) / Z)) :=
        mul_le_mul_of_nonneg_left hK ha0
      have h3 : Z ^ (K + 1) * Real.exp ((∑ i ∈ R, z i) / Z) +
          z a * (Z ^ K * Real.exp ((∑ i ∈ R, z i) / Z)) =
            Z ^ (K + 1) * ((1 + z a / Z) * Real.exp ((∑ i ∈ R, z i) / Z)) := by
        rw [pow_succ]
        field_simp
      have h4 : Z ^ (K + 1) * ((1 + z a / Z) * Real.exp ((∑ i ∈ R, z i) / Z)) ≤
          Z ^ (K + 1) * (Real.exp (z a / Z) * Real.exp ((∑ i ∈ R, z i) / Z)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le)
          (by positivity)
      linarith

/-- `exp(-2u) ≤ 1 - u` for `0 ≤ u ≤ 1/2`. -/
theorem exp_neg_two_mul_le {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) :
    Real.exp (-(2 * u)) ≤ 1 - u := by
  have h1 : 1 + 2 * u ≤ Real.exp (2 * u) := by linarith [Real.add_one_le_exp (2 * u)]
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ (Real.exp_pos _)]
  nlinarith [mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 1 - u),
    mul_nonneg hu0 (by linarith : (0 : ℝ) ≤ 1 - 2 * u)]

/-- `∏ (1 - μ_i) ≥ exp(-2 ∑ μ_i)` when `0 ≤ μ_i ≤ 1/2` [S-02:0265–0267]. -/
theorem exp_neg_le_prod_one_sub (R : Finset ι) (μ : ι → ℝ) (h0 : ∀ i ∈ R, 0 ≤ μ i)
    (h1 : ∀ i ∈ R, μ i ≤ 1 / 2) : Real.exp (-(2 * ∑ i ∈ R, μ i)) ≤ ∏ i ∈ R, (1 - μ i) := by
  have h : -(2 * ∑ i ∈ R, μ i) = ∑ i ∈ R, -(2 * μ i) := by
    rw [Finset.mul_sum, Finset.sum_neg_distrib]
  rw [h, Real.exp_sum]
  exact Finset.prod_le_prod (fun i _ => (Real.exp_pos _).le) fun i hi =>
    exp_neg_two_mul_le (h0 i hi) (h1 i hi)

/-! ### The two models -/

variable (m : ι → ℕ) [∀ i, NeZero (m i)]

/-- `∑_u φ_i(u)`, the sum over all residues modulo `m i`. -/
def rsum (φ : (i : ι) → ZMod (m i) → ℝ) (i : ι) : ℝ := ∑ u : ZMod (m i), φ i u

/-- `∑_u (1 - φ_i(u))`; for a remaining prime this is `∑_r c_{p,r}` [S-02:0258–0262]. -/
def defect (φ : (i : ι) → ZMod (m i) → ℝ) (i : ι) : ℝ := ∑ u : ZMod (m i), (1 - φ i u)

theorem rsum_add_defect (φ : (i : ι) → ZMod (m i) → ℝ) (i : ι) :
    rsum m φ i + defect m φ i = (m i : ℝ) := by
  unfold rsum defect
  rw [← Finset.sum_add_distrib]
  simp [ZMod.card]

theorem rsum_div_eq (φ : (i : ι) → ZMod (m i) → ℝ) (i : ι) :
    rsum m φ i / (m i : ℝ) = 1 - defect m φ i / (m i : ℝ) := by
  have hne : (m i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne (m i))
  have h := rsum_add_defect m φ i
  field_simp
  linarith

theorem rsum_nonneg (φ : (i : ι) → ZMod (m i) → ℝ) {i : ι} (h : ∀ u, 0 ≤ φ i u) :
    0 ≤ rsum m φ i := Finset.sum_nonneg fun u _ => h u

theorem defect_nonneg (φ : (i : ι) → ZMod (m i) → ℝ) {i : ι} (h : ∀ u, φ i u ≤ 1) :
    0 ≤ defect m φ i := Finset.sum_nonneg fun u _ => sub_nonneg.mpr (h u)

theorem defect_le (φ : (i : ι) → ZMod (m i) → ℝ) {i : ι} (h : ∀ u, 0 ≤ φ i u) :
    defect m φ i ≤ (m i : ℝ) := by
  have h1 := rsum_add_defect m φ i
  have h2 := rsum_nonneg m φ h
  linarith

/-- The weighted CRT count for `∏_{i ∈ A} φ_i · ∏_{i ∈ T} (1 - φ_i)`. -/
theorem mixed_count [DecidableEq ι] (hm : Pairwise (Function.onFun Nat.Coprime m))
    (φ : (i : ι) → ZMod (m i) → ℝ) {A T : Finset ι} (hAT : Disjoint A T)
    (hA : ∀ i ∈ A, ∀ u, 0 ≤ φ i u) (hT : ∀ i ∈ T, ∀ u, φ i u ≤ 1) {a b : ℤ} (hab : a ≤ b) :
    |∑ n ∈ Finset.Ico a b,
          (∏ i ∈ A, φ i (n : ZMod (m i))) * ∏ i ∈ T, (1 - φ i (n : ZMod (m i))) -
        ((b : ℝ) - a) * ((∏ i ∈ A, (rsum m φ i / (m i : ℝ))) *
          ∏ i ∈ T, (defect m φ i / (m i : ℝ)))| ≤
      (∏ i ∈ A, rsum m φ i) * ∏ i ∈ T, defect m φ i := by
  set g : (i : ι) → ZMod (m i) → ℝ := fun i u => if i ∈ T then 1 - φ i u else φ i u with hg
  have hgA : ∀ i ∈ A, ∀ u, g i u = φ i u := fun i hi u => by
    have hiT : i ∉ T := Finset.disjoint_left.mp hAT hi
    simp only [hg, hiT, ↓reduceIte]
  have hgT : ∀ i ∈ T, ∀ u, g i u = 1 - φ i u := fun i hi u => by
    simp only [hg, hi, ↓reduceIte]
  have hg0 : ∀ i ∈ A ∪ T, ∀ u, 0 ≤ g i u := by
    intro i hi u
    rcases Finset.mem_union.mp hi with h | h
    · rw [hgA i h]
      exact hA i h u
    · rw [hgT i h]
      exact sub_nonneg.mpr (hT i h u)
  have h := abs_sum_Ico_prod_sub_le m hm (A ∪ T) g hg0 hab
  have e1 : ∀ n : ℤ, ∏ i ∈ A ∪ T, g i (n : ZMod (m i)) =
      (∏ i ∈ A, φ i (n : ZMod (m i))) * ∏ i ∈ T, (1 - φ i (n : ZMod (m i))) := by
    intro n
    rw [Finset.prod_union hAT]
    congr 1
    · exact Finset.prod_congr rfl fun i hi => hgA i hi _
    · exact Finset.prod_congr rfl fun i hi => hgT i hi _
  have e2 : ∏ i ∈ A ∪ T, ((∑ u, g i u) / (m i : ℝ)) =
      (∏ i ∈ A, (rsum m φ i / (m i : ℝ))) * ∏ i ∈ T, (defect m φ i / (m i : ℝ)) := by
    rw [Finset.prod_union hAT]
    congr 1
    · refine Finset.prod_congr rfl fun i hi => ?_
      unfold rsum
      rw [Finset.sum_congr rfl fun u _ => hgA i hi u]
    · refine Finset.prod_congr rfl fun i hi => ?_
      unfold defect
      rw [Finset.sum_congr rfl fun u _ => hgT i hi u]
  have e3 : ∏ i ∈ A ∪ T, ∑ u, g i u = (∏ i ∈ A, rsum m φ i) * ∏ i ∈ T, defect m φ i := by
    rw [Finset.prod_union hAT]
    congr 1
    · refine Finset.prod_congr rfl fun i hi => ?_
      unfold rsum
      rw [Finset.sum_congr rfl fun u _ => hgA i hi u]
    · refine Finset.prod_congr rfl fun i hi => ?_
      unfold defect
      rw [Finset.sum_congr rfl fun u _ => hgT i hi u]
  rw [Finset.sum_congr rfl fun n _ => e1 n, e2, e3] at h
  exact h

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResRepl
