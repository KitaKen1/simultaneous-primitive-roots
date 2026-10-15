module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.BilinearBlocks
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The integer bilinear estimate ([S] Lemma 4.2)

Source: `verification/stage7-sources/S-03.tex`, lines 110–161 (`[S-03:0110–0161]`).

`integerBilinear : IntegerBilinear` (`Comparison/Leaves.lean`), with the explicit constant
`K = √(2 (1 + 2C)(C + 3))`.

Proof, following the paper.

* "Extend the coefficients by zero to their containing intervals. Cauchy–Schwarz in `n`"
  (`Bilinear.norm_sum_mul_sq_le`, then the sum over `n ∈ s` is enlarged to the full interval
  `[N, N + ⌊CU⌋]`),
* "followed by expansion of the square" (`Bilinear.sum_norm_sq_eq`): the mean square of
  `∑_k b_k e(αnk)` over the interval is the quadratic form of the Gram matrix
  `E(k, k') = ∑_n e(α n (k' - k))`, which is bounded by its largest row sum
  (`Bilinear.schur_symm`, `Bilinear.sum_norm_sq_le_of_rows`; this is the step
  `∑_t |b_t b_{t+h}| ≤ ‖b‖²` of the paper);
* "and the geometric-sum bound on the full interval of `n`": the rows are sums of the geometric
  kernel (`Bilinear.gram_eq_geomKernel`), bounded block by block in
  `Bilinear.sum_geomKernel_le` (`Comparison/BilinearBlocks.lean`);
* the constants (`Bilinear.block_const_le`): `1 + 2CV/r` blocks, each contributing at most
  `2 ((C + 1) U + r (1 + log(2r)))`, and `1 + log(2r) ≤ 3 log(2r)`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

namespace Bilinear

/-! ### Cauchy–Schwarz and the Schur test -/

/-- Cauchy–Schwarz for a finite linear combination of complex numbers. -/
theorem norm_sum_mul_sq_le {ι : Type*} (s : Finset ι) (c z : ι → ℂ) :
    ‖∑ i ∈ s, c i * z i‖ ^ 2 ≤ (∑ i ∈ s, ‖c i‖ ^ 2) * ∑ i ∈ s, ‖z i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, c i * z i‖ ≤ ∑ i ∈ s, ‖c i‖ * ‖z i‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => norm_mul _ _))
  have h2 : (∑ i ∈ s, ‖c i‖ * ‖z i‖) ^ 2 ≤ (∑ i ∈ s, ‖c i‖ ^ 2) * ∑ i ∈ s, ‖z i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq s _ _
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

/-- **The Schur test** for a symmetric nonnegative kernel: the quadratic form is bounded by the
largest row sum. -/
theorem schur_symm {κ : Type*} (t : Finset κ) (β : κ → ℝ) (M : κ → κ → ℝ)
    (hM0 : ∀ k k', 0 ≤ M k k') (hsymm : ∀ k k', M k k' = M k' k) {Λ : ℝ}
    (hrow : ∀ k ∈ t, ∑ k' ∈ t, M k k' ≤ Λ) :
    ∑ k ∈ t, ∑ k' ∈ t, β k * β k' * M k k' ≤ Λ * ∑ k ∈ t, β k ^ 2 := by
  have hpt : ∀ k k', 2 * (β k * β k' * M k k') ≤ β k ^ 2 * M k k' + β k' ^ 2 * M k' k := by
    intro k k'
    have h1 : 2 * (β k * β k') ≤ β k ^ 2 + β k' ^ 2 := by nlinarith [sq_nonneg (β k - β k')]
    have h2 := mul_le_mul_of_nonneg_right h1 (hM0 k k')
    rw [hsymm k' k]
    linarith
  have h1 : ∑ k ∈ t, ∑ k' ∈ t, β k ^ 2 * M k k' ≤ Λ * ∑ k ∈ t, β k ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [← Finset.mul_sum, mul_comm]
    exact mul_le_mul_of_nonneg_right (hrow k hk) (sq_nonneg _)
  have h2 : ∑ k ∈ t, ∑ k' ∈ t, β k' ^ 2 * M k' k = ∑ k ∈ t, ∑ k' ∈ t, β k ^ 2 * M k k' :=
    Finset.sum_comm
  have hsum : 2 * ∑ k ∈ t, ∑ k' ∈ t, β k * β k' * M k k' ≤
      ∑ k ∈ t, ∑ k' ∈ t, β k ^ 2 * M k k' + ∑ k ∈ t, ∑ k' ∈ t, β k' ^ 2 * M k' k := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun k' _ => hpt k k'
  rw [h2] at hsum
  linarith

/-! ### Expansion of the square -/

/-- The Gram matrix `E(k, k') = ∑_n conj(v_n(k)) v_n(k')` is Hermitian. -/
theorem norm_gram_symm (I : Finset ℕ) (v : ℕ → ℕ → ℂ) (k k' : ℕ) :
    ‖∑ n ∈ I, conj (v n k') * v n k‖ = ‖∑ n ∈ I, conj (v n k) * v n k'‖ := by
  have h : ∑ n ∈ I, conj (v n k') * v n k = conj (∑ n ∈ I, conj (v n k) * v n k') := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun n _ => by
      rw [map_mul, starRingEnd_self_apply, mul_comm]
  rw [h, Complex.norm_conj]

/-- **Expansion of the square**:
`∑_n |∑_k b_k v_n(k)|² = ∑_{k,k'} conj(b_k) b_{k'} ∑_n conj(v_n(k)) v_n(k')`. -/
theorem sum_norm_sq_eq (I t : Finset ℕ) (b : ℕ → ℂ) (v : ℕ → ℕ → ℂ) :
    ((∑ n ∈ I, ‖∑ k ∈ t, b k * v n k‖ ^ 2 : ℝ) : ℂ) =
      ∑ k ∈ t, ∑ k' ∈ t, (conj (b k) * b k') * ∑ n ∈ I, conj (v n k) * v n k' := by
  have h1 : ∀ n : ℕ, ((‖∑ k ∈ t, b k * v n k‖ ^ 2 : ℝ) : ℂ) =
      ∑ k ∈ t, ∑ k' ∈ t, (conj (b k) * b k') * (conj (v n k) * v n k') := by
    intro n
    rw [Complex.ofReal_pow, ← Complex.conj_mul', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
    rw [map_mul]
    ring
  rw [Complex.ofReal_sum, Finset.sum_congr rfl fun n _ => h1 n, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k' _ => (Finset.mul_sum _ _ _).symm

/-- The mean square of `∑_k b_k v_n(k)` over `n ∈ I` is at most the largest row sum of the Gram
matrix times `‖b‖²`. -/
theorem sum_norm_sq_le_of_rows (I t : Finset ℕ) (b : ℕ → ℂ) (v : ℕ → ℕ → ℂ) {Λ : ℝ}
    (hrow : ∀ k ∈ t, ∑ k' ∈ t, ‖∑ n ∈ I, conj (v n k) * v n k'‖ ≤ Λ) :
    ∑ n ∈ I, ‖∑ k ∈ t, b k * v n k‖ ^ 2 ≤ Λ * ∑ k ∈ t, ‖b k‖ ^ 2 := by
  have h0 : 0 ≤ ∑ n ∈ I, ‖∑ k ∈ t, b k * v n k‖ ^ 2 :=
    Finset.sum_nonneg fun n _ => sq_nonneg _
  have h1 : ∑ n ∈ I, ‖∑ k ∈ t, b k * v n k‖ ^ 2 =
      ‖∑ k ∈ t, ∑ k' ∈ t, (conj (b k) * b k') * ∑ n ∈ I, conj (v n k) * v n k'‖ := by
    rw [← sum_norm_sq_eq I t b v, Complex.norm_of_nonneg h0]
  have h2 : ‖∑ k ∈ t, ∑ k' ∈ t, (conj (b k) * b k') * ∑ n ∈ I, conj (v n k) * v n k'‖ ≤
      ∑ k ∈ t, ∑ k' ∈ t, ‖b k‖ * ‖b k'‖ * ‖∑ n ∈ I, conj (v n k) * v n k'‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k' _ => ?_))
    rw [norm_mul, norm_mul, Complex.norm_conj]
  rw [h1]
  exact h2.trans (schur_symm t (fun k => ‖b k‖)
    (fun k k' => ‖∑ n ∈ I, conj (v n k) * v n k'‖) (fun k k' => norm_nonneg _)
    (fun k k' => norm_gram_symm I v k' k) hrow)

/-- The Gram matrix of the phases `v_n(k) = e(αnk)` over an interval is the geometric kernel. -/
theorem gram_eq_geomKernel (α : ℝ) (N L k k' : ℕ) :
    ‖∑ n ∈ Finset.Ico N (N + L), conj (expUnit (α * (n : ℝ) * (k : ℝ))) *
        expUnit (α * (n : ℝ) * (k' : ℝ))‖ = geomKernel N L (α * ((k' : ℝ) - (k : ℝ))) := by
  unfold geomKernel
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← expUnit_neg, ← expUnit_add]
  congr 1
  ring

/-! ### The constants -/

/-- The number of blocks times the contribution of a block is at most
`2 (1 + 2C)(C + 3) [U + (1 + V/r)(U + r log(2r))]`. -/
theorem block_const_le {C U V : ℝ} (hC : 0 < C) (hU : 1 ≤ U) (hV : 1 ≤ V) {r Ln D q : ℕ}
    (hr : 0 < r) (hLn : (Ln : ℝ) ≤ C * U + 1) (hD : (D : ℝ) ≤ C * V) (hq : r ≤ 2 * q) :
    ((D / q + 1 : ℕ) : ℝ) * (2 * ∑ m ∈ Finset.range (2 * r), binWeight (Ln : ℝ) r m) ≤
      2 * (1 + 2 * C) * (C + 3) *
        (U + (1 + V / (r : ℝ)) * (U + (r : ℝ) * Real.log (2 * (r : ℝ)))) := by
  have hrpos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hU0 : (0 : ℝ) ≤ U := by linarith
  have hV0 : (0 : ℝ) ≤ V := by linarith
  -- `log(2r) ≥ log 2 > 1/2`
  have hlog2 : (1 : ℝ) / 2 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have hlog : Real.log 2 ≤ Real.log (2 * (r : ℝ)) := Real.log_le_log two_pos (by linarith)
  have hW : 0 ≤ (r : ℝ) * Real.log (2 * (r : ℝ)) := mul_nonneg hrpos.le (by linarith)
  -- the sum of the arc weights
  have hG0 : 0 ≤ ∑ m ∈ Finset.range (2 * r), binWeight (Ln : ℝ) r m :=
    Finset.sum_nonneg fun m _ => binWeight_nonneg (Nat.cast_nonneg Ln) r m
  have hG1 := sum_binWeight_le (L := (Ln : ℝ)) hr
  have hG2 : (r : ℝ) * 1 ≤ (r : ℝ) * (2 * Real.log (2 * (r : ℝ))) :=
    mul_le_mul_of_nonneg_left (by linarith) hrpos.le
  have hCW : 0 ≤ C * ((r : ℝ) * Real.log (2 * (r : ℝ))) := mul_nonneg hC.le hW
  have hG : ∑ m ∈ Finset.range (2 * r), binWeight (Ln : ℝ) r m ≤
      (C + 3) * (U + (r : ℝ) * Real.log (2 * (r : ℝ))) := by linarith
  -- the number of blocks
  have h1 : ((D / q : ℕ) : ℝ) * (q : ℝ) ≤ (D : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self D q
  have h2 : (r : ℝ) ≤ 2 * (q : ℝ) := by exact_mod_cast hq
  have h3 : (0 : ℝ) ≤ ((D / q : ℕ) : ℝ) := Nat.cast_nonneg _
  have h4 : ((D / q : ℕ) : ℝ) * (r : ℝ) ≤ ((D / q : ℕ) : ℝ) * (2 * (q : ℝ)) :=
    mul_le_mul_of_nonneg_left h2 h3
  have h5 : ((D / q : ℕ) : ℝ) ≤ 2 * C * V / (r : ℝ) := by
    rw [le_div_iff₀ hrpos]
    linarith
  have h6 : 2 * C * V / (r : ℝ) = 2 * C * (V / (r : ℝ)) := mul_div_assoc _ _ _
  have hρ : 0 ≤ V / (r : ℝ) := div_nonneg hV0 hrpos.le
  have hJ : ((D / q + 1 : ℕ) : ℝ) ≤ (1 + 2 * C) * (1 + V / (r : ℝ)) := by
    rw [Nat.cast_add_one]
    linarith
  have hK : 0 ≤ (1 + 2 * C) * (1 + V / (r : ℝ)) :=
    mul_nonneg (by linarith) (by linarith)
  have hKU : 0 ≤ 2 * (1 + 2 * C) * (C + 3) * U :=
    mul_nonneg (mul_nonneg (mul_nonneg zero_le_two (by linarith)) (by linarith)) hU0
  calc ((D / q + 1 : ℕ) : ℝ) * (2 * ∑ m ∈ Finset.range (2 * r), binWeight (Ln : ℝ) r m)
      ≤ (1 + 2 * C) * (1 + V / (r : ℝ)) *
          (2 * ((C + 3) * (U + (r : ℝ) * Real.log (2 * (r : ℝ))))) :=
        mul_le_mul hJ (by linarith) (by linarith) hK
    _ ≤ 2 * (1 + 2 * C) * (C + 3) *
          (U + (1 + V / (r : ℝ)) * (U + (r : ℝ) * Real.log (2 * (r : ℝ)))) := by
        linarith

/-! ### The estimate -/

/-- **[S] Lemma 4.2, squared form**, with the explicit constant `2 (1 + 2C)(C + 3)`. -/
theorem bilinear_sq_le {C : ℝ} (hC : 0 < C) {U V : ℝ} (hU : 1 ≤ U) (hV : 1 ≤ V)
    (s t : Finset ℕ) (N T : ℕ)
    (hs : ∀ n ∈ s, N ≤ n ∧ (n : ℝ) ≤ N + C * U) (ht : ∀ k ∈ t, T ≤ k ∧ (k : ℝ) ≤ T + C * V)
    (a b : ℕ → ℂ) {α β : ℝ} {u : ℤ} {r : ℕ} (hr : 0 < r) (hcop : IsCoprime u (r : ℤ))
    (hα : α = (u : ℝ) / (r : ℝ) + β) (hβ : |β| ≤ ((r : ℝ) ^ 2)⁻¹) :
    ‖∑ n ∈ s, ∑ k ∈ t, a n * b k * expUnit (α * (n : ℝ) * (k : ℝ))‖ ^ 2 ≤
      2 * (1 + 2 * C) * (C + 3) * (∑ n ∈ s, ‖a n‖ ^ 2) * (∑ k ∈ t, ‖b k‖ ^ 2) *
        (U + (1 + V / (r : ℝ)) * (U + (r : ℝ) * Real.log (2 * (r : ℝ)))) := by
  have hCU : 0 ≤ C * U := mul_nonneg hC.le (by linarith)
  have hCV : 0 ≤ C * V := mul_nonneg hC.le (by linarith)
  -- the containing intervals `[N, N + ⌊CU⌋]` and `[T, T + ⌊CV⌋]`
  obtain ⟨Ln, hLn⟩ : ∃ Ln : ℕ, Ln = ⌊C * U⌋₊ + 1 := ⟨_, rfl⟩
  obtain ⟨D, hD⟩ : ∃ D : ℕ, D = ⌊C * V⌋₊ := ⟨_, rfl⟩
  have hLnR : (Ln : ℝ) ≤ C * U + 1 := by
    rw [hLn, Nat.cast_add_one]
    linarith [Nat.floor_le hCU]
  have hDR : (D : ℝ) ≤ C * V := by
    rw [hD]
    exact Nat.floor_le hCV
  have hsI : s ⊆ Finset.Ico N (N + Ln) := by
    intro n hn
    obtain ⟨h1, h2⟩ := hs n hn
    have h3 : ((n - N : ℕ) : ℝ) ≤ C * U := by
      rw [Nat.cast_sub h1]
      linarith
    have h4 : n - N ≤ ⌊C * U⌋₊ := Nat.le_floor h3
    rw [Finset.mem_Ico]
    omega
  have htD : ∀ k ∈ t, T ≤ k ∧ k ≤ T + D := by
    intro k hk
    obtain ⟨h1, h2⟩ := ht k hk
    have h3 : ((k - T : ℕ) : ℝ) ≤ C * V := by
      rw [Nat.cast_sub h1]
      linarith
    have h4 : k - T ≤ ⌊C * V⌋₊ := Nat.le_floor h3
    exact ⟨h1, by omega⟩
  -- blocks of `⌊r/2⌋ + 1` consecutive integers
  have hq0 : 0 < r / 2 + 1 := by omega
  have hqr : 2 * (r / 2 + 1 - 1) ≤ r := by omega
  have hq2 : r ≤ 2 * (r / 2 + 1) := by omega
  -- the row sums of the Gram matrix of the phases
  have hrow : ∀ k ∈ t, ∑ k' ∈ t,
      ‖∑ n ∈ Finset.Ico N (N + Ln), conj (expUnit (α * (n : ℝ) * (k : ℝ))) *
        expUnit (α * (n : ℝ) * (k' : ℝ))‖ ≤
      ((D / (r / 2 + 1) + 1 : ℕ) : ℝ) *
        (2 * ∑ m ∈ Finset.range (2 * r), binWeight (Ln : ℝ) r m) := by
    intro k _
    rw [Finset.sum_congr rfl fun k' _ => gram_eq_geomKernel α N Ln k k']
    exact sum_geomKernel_le hr hcop hα hβ hq0 hqr N Ln T D t htD (k : ℝ)
  have hms := sum_norm_sq_le_of_rows (Finset.Ico N (N + Ln)) t b
    (fun n k => expUnit (α * (n : ℝ) * (k : ℝ))) hrow
  have hΛ := block_const_le hC hU hV hr hLnR hDR hq2
  -- Cauchy–Schwarz in `n`
  have hsplit : ∑ n ∈ s, ∑ k ∈ t, a n * b k * expUnit (α * (n : ℝ) * (k : ℝ)) =
      ∑ n ∈ s, a n * ∑ k ∈ t, b k * expUnit (α * (n : ℝ) * (k : ℝ)) :=
    Finset.sum_congr rfl fun n _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => mul_assoc _ _ _
  have hCS := norm_sum_mul_sq_le s a
    (fun n => ∑ k ∈ t, b k * expUnit (α * (n : ℝ) * (k : ℝ)))
  have hsub : ∑ n ∈ s, ‖∑ k ∈ t, b k * expUnit (α * (n : ℝ) * (k : ℝ))‖ ^ 2 ≤
      ∑ n ∈ Finset.Ico N (N + Ln), ‖∑ k ∈ t, b k * expUnit (α * (n : ℝ) * (k : ℝ))‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hsI fun n _ _ => sq_nonneg _
  have hA0 : 0 ≤ ∑ n ∈ s, ‖a n‖ ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hB0 : 0 ≤ ∑ k ∈ t, ‖b k‖ ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  rw [hsplit]
  calc ‖∑ n ∈ s, a n * ∑ k ∈ t, b k * expUnit (α * (n : ℝ) * (k : ℝ))‖ ^ 2
      ≤ (∑ n ∈ s, ‖a n‖ ^ 2) *
          ∑ n ∈ s, ‖∑ k ∈ t, b k * expUnit (α * (n : ℝ) * (k : ℝ))‖ ^ 2 := hCS
    _ ≤ (∑ n ∈ s, ‖a n‖ ^ 2) *
          (((D / (r / 2 + 1) + 1 : ℕ) : ℝ) *
            (2 * ∑ m ∈ Finset.range (2 * r), binWeight (Ln : ℝ) r m) *
              ∑ k ∈ t, ‖b k‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (hsub.trans hms) hA0
    _ ≤ (∑ n ∈ s, ‖a n‖ ^ 2) *
          (2 * (1 + 2 * C) * (C + 3) *
            (U + (1 + V / (r : ℝ)) * (U + (r : ℝ) * Real.log (2 * (r : ℝ)))) *
              ∑ k ∈ t, ‖b k‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hΛ hB0) hA0
    _ = 2 * (1 + 2 * C) * (C + 3) * (∑ n ∈ s, ‖a n‖ ^ 2) * (∑ k ∈ t, ‖b k‖ ^ 2) *
          (U + (1 + V / (r : ℝ)) * (U + (r : ℝ) * Real.log (2 * (r : ℝ)))) := by ring

end Bilinear

/-- **[S] Lemma 4.2 (integer bilinear estimate)** [S-03:0110–0161], with
`K = √(2 (1 + 2C)(C + 3))`. -/
theorem integerBilinear : IntegerBilinear := by
  intro C hC
  have hK2 : 0 < 2 * (1 + 2 * C) * (C + 3) :=
    mul_pos (mul_pos two_pos (by linarith)) (by linarith)
  refine ⟨Real.sqrt (2 * (1 + 2 * C) * (C + 3)), Real.sqrt_pos.mpr hK2, ?_⟩
  intro U V hU hV s t N T hs ht a b α β u r hr hcop hα hβ
  have hsq := Bilinear.bilinear_sq_le hC hU hV s t N T hs ht a b hr hcop hα hβ
  have hA0 : 0 ≤ ∑ n ∈ s, ‖a n‖ ^ 2 := Finset.sum_nonneg fun n _ => sq_nonneg _
  have hB0 : 0 ≤ ∑ k ∈ t, ‖b k‖ ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have h := (le_abs_self _).trans (Real.abs_le_sqrt hsq)
  rw [Real.sqrt_mul (mul_nonneg (mul_nonneg hK2.le hA0) hB0),
    Real.sqrt_mul (mul_nonneg hK2.le hA0), Real.sqrt_mul hK2.le] at h
  exact h

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
