module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import SimultaneousPrimitiveRoots.Unconditional.Classical.DivisorMoments

/-!
# Mean squares of Dirichlet polynomials

The coefficient-independent mean-value estimates of `lem:moment-bounds`
(`verification/stage7-sources/P-02.tex`, lines 73--93, `eq:dirichlet-mean` and
`eq:dirichlet-spaced`) and `lem:dirichlet-mean` (`verification/stage7-sources/S-01.tex`,
lines 194--209). For complex coefficients `c : ℕ → ℂ` and real `Y ≥ 1` let

`P(t) = ∑_{1 ≤ n ≤ Y} c_n n^{it}`,

in Lean `∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, c n * (n : ℂ) ^ (Complex.I * t)`.

* `integral_normSq_dirichletPolynomial_le`: there is an absolute `C > 0` with
  `∫_a^b |P(t)|² dt ≤ C (b - a + Y log (2Y)) ∑_n |c_n|²` for all `a ≤ b`
  (`setIntegral_normSq_dirichletPolynomial_le`: the same for the integral over any subset of
  `[a, b]`, in particular over the open, closed and half-open intervals with endpoints `a`, `b`).
* `sum_normSq_dirichletPolynomial_le_of_separated`: there is an absolute `C > 0` with
  `∑_{t ∈ 𝒯} |P(t)|² ≤ C (b - a + 1 + Y log (2Y)) (log (2Y))² ∑_n |c_n|²` for every finite set
  `𝒯 ⊆ [a, b]` of reals with pairwise distances at least `1`.

Both are deduced from versions with explicit constants for the polynomial
`dirichletPolynomial c N t = ∑_{1 ≤ n ≤ N} c_n n^{it}` with a natural cutoff `N`:

* `integral_normSq_dirichletPolynomial_le_nat`:
  `∫_a^b |P|² ≤ (b - a + 4 N (1 + log N)) ∑ |c_n|²`;
* `sum_normSq_dirichletPolynomial_le_nat`:
  `∑_{t ∈ 𝒯} |P(t)|² ≤ (b - a + 1 + 4 N (1 + log N)) (2 + (log N)²) ∑ |c_n|²`.

The shape `T + Y log (2Y)` of the papers follows from `1 + log Y ≤ 2 log (2Y)` for `Y ≥ 1`; the
final constants are `C = 8` and `C = 48`.

## Proofs

These are the classical elementary arguments indicated in the papers.

*Mean square.* Since `n^{it} = e^{it log n}` (`natCast_cpow_I_mul`), expanding the square gives
`∫_a^b |P|² = ∑_{m,n} c_m \bar c_n ∫_a^b e^{it(log m - log n)} dt`
(`ofReal_integral_normSq_sum_exp_log`). The diagonal integrals are `b - a`; for `m ≠ n` the
integral is at most `2 / |log m - log n|` (`norm_integral_exp_mul_I_le`), and
`|log m - log n| ≥ |m - n| / N` (`sub_div_le_log_sub_log`). Then `2 |c_m c_n| ≤ |c_m|² + |c_n|²`
(`sum_sum_mul_mul_le_of_row_sum_le`) and `∑_{n ≠ m, n ≤ N} 1 / |m - n| ≤ 2 (1 + log N)`
(`sum_Icc_inv_natSub_add_le`).

*Well-spaced points.* For continuously differentiable `f` the one-dimensional Sobolev inequality
(Gallagher) `|f(t)|² ≤ ∫_{t-1/2}^{t+1/2} (|f|² + 2 |f f'|) ≤ ∫_{t-1/2}^{t+1/2} (2 |f|² + |f'|²)`
holds (`le_integral_add_abs_deriv`, `normSq_le_integral_of_hasDerivAt`). The unit intervals
centred at the points of `𝒯` are pairwise disjoint and lie in `[a - 1/2, b + 1/2]`
(`sum_integral_unit_interval_le`). Finally `P'` is the Dirichlet polynomial with coefficients
`i c_n log n` (`hasDerivAt_dirichletPolynomial`), so the mean-square bound applies to `P` and to
`P'`, the latter with an extra factor `(log N)²`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Classical

/-! ### Elementary inequalities -/

/-- A Schur-type bound: if the kernel `K` is nonnegative and symmetric on `s` with row sums at
most `B`, then `∑_{m,n} x_m x_n K(m,n) ≤ B ∑_m x_m²`. This is the step
`2 |c_m c_n| ≤ |c_m|² + |c_n|²`. -/
theorem sum_sum_mul_mul_le_of_row_sum_le (s : Finset ℕ) (x : ℕ → ℝ) (K : ℕ → ℕ → ℝ) (B : ℝ)
    (hK0 : ∀ m ∈ s, ∀ n ∈ s, 0 ≤ K m n) (hKsymm : ∀ m ∈ s, ∀ n ∈ s, K m n = K n m)
    (hrow : ∀ m ∈ s, ∑ n ∈ s, K m n ≤ B) :
    ∑ m ∈ s, ∑ n ∈ s, x m * x n * K m n ≤ B * ∑ m ∈ s, x m ^ 2 := by
  have h1 : ∀ m ∈ s, ∀ n ∈ s,
      x m * x n * K m n ≤ x m ^ 2 * K m n / 2 + x n ^ 2 * K n m / 2 := by
    intro m hm n hn
    rw [← hKsymm m hm n hn]
    nlinarith [mul_nonneg (sq_nonneg (x m - x n)) (hK0 m hm n hn)]
  have h2 : ∑ m ∈ s, ∑ n ∈ s, x m * x n * K m n ≤
      ∑ m ∈ s, ∑ n ∈ s, (x m ^ 2 * K m n / 2 + x n ^ 2 * K n m / 2) :=
    Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun n hn => h1 m hm n hn
  have h3 : ∑ m ∈ s, ∑ n ∈ s, (x m ^ 2 * K m n / 2 + x n ^ 2 * K n m / 2) =
      (∑ m ∈ s, ∑ n ∈ s, x m ^ 2 * K m n) / 2 + (∑ m ∈ s, ∑ n ∈ s, x n ^ 2 * K n m) / 2 := by
    simp only [Finset.sum_add_distrib, Finset.sum_div]
  have hsymm : ∑ m ∈ s, ∑ n ∈ s, x n ^ 2 * K n m = ∑ m ∈ s, ∑ n ∈ s, x m ^ 2 * K m n :=
    Finset.sum_comm
  have hS1 : ∑ m ∈ s, ∑ n ∈ s, x m ^ 2 * K m n ≤ B * ∑ m ∈ s, x m ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun m hm => ?_
    rw [← Finset.mul_sum, mul_comm B]
    exact mul_le_mul_of_nonneg_left (hrow m hm) (sq_nonneg _)
  rw [h3, hsymm] at h2
  linarith

/-- Comparison of a sum of reciprocals along a map `φ` that is injective where it does not
vanish (recall `(0 : ℝ)⁻¹ = 0`). -/
theorem sum_inv_natCast_comp_le (s t : Finset ℕ) (φ : ℕ → ℕ)
    (hφ : ∀ n ∈ s, φ n ≠ 0 → φ n ∈ t)
    (hinj : ∀ x ∈ s, ∀ y ∈ s, φ x ≠ 0 → φ x = φ y → x = y) :
    ∑ n ∈ s, ((φ n : ℕ) : ℝ)⁻¹ ≤ ∑ j ∈ t, (j : ℝ)⁻¹ := by
  have h1 : ∑ n ∈ s.filter (fun n => φ n ≠ 0), ((φ n : ℕ) : ℝ)⁻¹ =
      ∑ n ∈ s, ((φ n : ℕ) : ℝ)⁻¹ := by
    refine Finset.sum_filter_of_ne fun n _ hn h0 => hn ?_
    rw [h0, Nat.cast_zero, inv_zero]
  have h2 : ∑ j ∈ (s.filter (fun n => φ n ≠ 0)).image φ, (j : ℝ)⁻¹ =
      ∑ n ∈ s.filter (fun n => φ n ≠ 0), ((φ n : ℕ) : ℝ)⁻¹ := by
    refine Finset.sum_image ?_
    intro x hx y hy hxy
    have hx' := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
    have hy' := Finset.mem_filter.mp (Finset.mem_coe.mp hy)
    exact hinj x hx'.1 y hy'.1 hx'.2 hxy
  rw [← h1, ← h2]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun j _ _ => by positivity)
  intro j hj
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hj
  have hn' := Finset.mem_filter.mp hn
  exact hφ n hn'.1 hn'.2

/-- The harmonic sum over the distances to a fixed point:
`∑_{n ≤ N, n ≠ m} 1 / |m - n| ≤ 2 (1 + log N)`. The summand is written with truncated
subtraction: `(m - n)⁻¹ + (n - m)⁻¹` is `1 / |m - n|` for `m ≠ n` and `0` for `m = n`. -/
theorem sum_Icc_inv_natSub_add_le (N m : ℕ) (hm : m ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, (((m - n : ℕ) : ℝ)⁻¹ + ((n - m : ℕ) : ℝ)⁻¹) ≤
      2 * (1 + Real.log N) := by
  rw [Finset.sum_add_distrib]
  have h1 : ∑ n ∈ Finset.Icc 1 N, ((m - n : ℕ) : ℝ)⁻¹ ≤ ∑ j ∈ Finset.Icc 1 N, (j : ℝ)⁻¹ := by
    refine sum_inv_natCast_comp_le _ _ (fun n => m - n) ?_ ?_
    · intro n hn h0
      have h0' : m - n ≠ 0 := h0
      have hn' := Finset.mem_Icc.mp hn
      show m - n ∈ Finset.Icc 1 N
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro x _ y _ h0 hxy
      have h0' : m - x ≠ 0 := h0
      have hxy' : m - x = m - y := hxy
      omega
  have h2 : ∑ n ∈ Finset.Icc 1 N, ((n - m : ℕ) : ℝ)⁻¹ ≤ ∑ j ∈ Finset.Icc 1 N, (j : ℝ)⁻¹ := by
    refine sum_inv_natCast_comp_le _ _ (fun n => n - m) ?_ ?_
    · intro n hn h0
      have h0' : n - m ≠ 0 := h0
      have hn' := Finset.mem_Icc.mp hn
      show n - m ∈ Finset.Icc 1 N
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro x _ y _ h0 hxy
      have h0' : x - m ≠ 0 := h0
      have hxy' : x - m = y - m := hxy
      omega
  linarith [sum_Icc_inv_le_one_add_log N]

/-- `(x - y) / M ≤ log x - log y` for `0 < y ≤ x ≤ M`. -/
theorem sub_div_le_log_sub_log {x y M : ℝ} (hy : 0 < y) (hyx : y ≤ x) (hxM : x ≤ M) :
    (x - y) / M ≤ Real.log x - Real.log y := by
  have hx : 0 < x := hy.trans_le hyx
  have h1 : 1 - (x / y)⁻¹ ≤ Real.log (x / y) :=
    Real.one_sub_inv_le_log_of_pos (div_pos hx hy)
  rw [Real.log_div hx.ne' hy.ne', inv_div, one_sub_div hx.ne'] at h1
  exact (div_le_div_of_nonneg_left (sub_nonneg.mpr hyx) hx hxM).trans h1

/-- `2 / |log m - log n| ≤ 2 N / (n - m)` for `1 ≤ m < n ≤ N`. -/
theorem two_div_abs_log_sub_log_le_of_lt {N m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) (hn : n ≤ N) :
    2 / |Real.log m - Real.log n| ≤ 2 * N * ((n - m : ℕ) : ℝ)⁻¹ := by
  have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hlt : (m : ℝ) < n := Nat.cast_lt.mpr hmn
  have hnN : (n : ℝ) ≤ N := Nat.cast_le.mpr hn
  have hpos : (0 : ℝ) < (n : ℝ) - m := sub_pos.mpr hlt
  have hlog : ((n : ℝ) - m) / N ≤ Real.log n - Real.log m :=
    sub_div_le_log_sub_log hm0 hlt.le hnN
  have hlogpos : 0 < Real.log n - Real.log m := lt_of_lt_of_le (div_pos hpos hN) hlog
  rw [Nat.cast_sub hmn.le, abs_sub_comm, abs_of_pos hlogpos]
  calc 2 / (Real.log n - Real.log m) ≤ 2 / (((n : ℝ) - m) / N) :=
        div_le_div_of_nonneg_left zero_le_two (div_pos hpos hN) hlog
    _ = 2 * N * ((n : ℝ) - m)⁻¹ := by
        rw [div_div_eq_mul_div, div_eq_mul_inv]

/-- `2 / |log m - log n| ≤ 2 N / |m - n|` for distinct `m, n ∈ [1, N]`, with `1 / |m - n|`
written as `(m - n)⁻¹ + (n - m)⁻¹` in truncated subtraction. -/
theorem two_div_abs_log_sub_log_le {N m n : ℕ} (hm : m ∈ Finset.Icc 1 N)
    (hn : n ∈ Finset.Icc 1 N) (hmn : m ≠ n) :
    2 / |Real.log m - Real.log n| ≤
      2 * N * (((m - n : ℕ) : ℝ)⁻¹ + ((n - m : ℕ) : ℝ)⁻¹) := by
  rw [Finset.mem_Icc] at hm hn
  rcases lt_or_gt_of_ne hmn with h | h
  · have key := two_div_abs_log_sub_log_le_of_lt hm.1 h hn.2
    rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero, inv_zero, zero_add]
    exact key
  · have key := two_div_abs_log_sub_log_le_of_lt hn.1 h hm.2
    rw [Nat.sub_eq_zero_of_le h.le, Nat.cast_zero, inv_zero, add_zero, abs_sub_comm]
    exact key

/-! ### The kernel bounding the integrals of `(m/n)^{it}` -/

/-- The kernel `K(m, n)` bounding `|∫_I (m/n)^{it} dt|` on an interval of length `T`, for
`1 ≤ m, n ≤ N`: it is `T` on the diagonal and `2 N / |m - n|` off the diagonal (the latter
written with truncated subtraction, which vanishes on the diagonal). -/
noncomputable def meanSquareKernel (N : ℕ) (T : ℝ) (m n : ℕ) : ℝ :=
  (if m = n then T else 0) + 2 * N * (((m - n : ℕ) : ℝ)⁻¹ + ((n - m : ℕ) : ℝ)⁻¹)

/-- The kernel is nonnegative for `T ≥ 0`. -/
theorem meanSquareKernel_nonneg (N : ℕ) {T : ℝ} (hT : 0 ≤ T) (m n : ℕ) :
    0 ≤ meanSquareKernel N T m n := by
  unfold meanSquareKernel
  have h1 : 0 ≤ (if m = n then T else 0) := by
    split_ifs
    · exact hT
    · exact le_rfl
  have h2 : (0 : ℝ) ≤ 2 * N * (((m - n : ℕ) : ℝ)⁻¹ + ((n - m : ℕ) : ℝ)⁻¹) := by positivity
  exact add_nonneg h1 h2

/-- The kernel is symmetric. -/
theorem meanSquareKernel_comm (N : ℕ) (T : ℝ) (m n : ℕ) :
    meanSquareKernel N T m n = meanSquareKernel N T n m := by
  unfold meanSquareKernel
  rw [add_comm (((m - n : ℕ) : ℝ)⁻¹)]
  congr 1
  by_cases h : m = n
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h)]

/-- The row sums of the kernel: `∑_{n ≤ N} K(m, n) ≤ T + 4 N (1 + log N)`. -/
theorem sum_meanSquareKernel_le {N : ℕ} (T : ℝ) {m : ℕ} (hm : m ∈ Finset.Icc 1 N) :
    ∑ n ∈ Finset.Icc 1 N, meanSquareKernel N T m n ≤ T + 4 * N * (1 + Real.log N) := by
  unfold meanSquareKernel
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos hm, ← Finset.mul_sum]
  have h := sum_Icc_inv_natSub_add_le N m (Finset.mem_Icc.mp hm).2
  have hN : (0 : ℝ) ≤ 2 * N := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h hN]

/-! ### Integrals of exponentials -/

/-- The trivial bound `|∫_a^b e^{iμt} dt| ≤ b - a`. -/
theorem norm_integral_exp_mul_I_le_sub {a b : ℝ} (hab : a ≤ b) (μ : ℝ) :
    ‖∫ t in a..b, Complex.exp (((μ * t : ℝ) : ℂ) * Complex.I)‖ ≤ b - a := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (C := 1)
    (f := fun t : ℝ => Complex.exp (((μ * t : ℝ) : ℂ) * Complex.I))
    (fun t _ => (Complex.norm_exp_ofReal_mul_I _).le)
  rwa [one_mul, abs_of_nonneg (sub_nonneg.mpr hab)] at h

/-- `|∫_a^b e^{iμt} dt| ≤ 2 / |μ|` for `μ ≠ 0`. -/
theorem norm_integral_exp_mul_I_le {μ : ℝ} (hμ : μ ≠ 0) (a b : ℝ) :
    ‖∫ t in a..b, Complex.exp (((μ * t : ℝ) : ℂ) * Complex.I)‖ ≤ 2 / |μ| := by
  have hc : (μ : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hμ) Complex.I_ne_zero
  have heq : ∀ t : ℝ, Complex.exp (((μ * t : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((μ : ℂ) * Complex.I * (t : ℂ)) := by
    intro t
    congr 1
    push_cast
    ring
  have hnorm : ∀ t : ℝ, ‖Complex.exp ((μ : ℂ) * Complex.I * (t : ℂ))‖ = 1 := by
    intro t
    rw [← heq t]
    exact Complex.norm_exp_ofReal_mul_I _
  have hden : ‖(μ : ℂ) * Complex.I‖ = |μ| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  simp_rw [heq]
  rw [integral_exp_mul_complex hc, norm_div, hden]
  refine div_le_div_of_nonneg_right ?_ (abs_nonneg μ)
  calc ‖Complex.exp ((μ : ℂ) * Complex.I * (b : ℂ)) -
        Complex.exp ((μ : ℂ) * Complex.I * (a : ℂ))‖
      ≤ ‖Complex.exp ((μ : ℂ) * Complex.I * (b : ℂ))‖ +
          ‖Complex.exp ((μ : ℂ) * Complex.I * (a : ℂ))‖ := norm_sub_le _ _
    _ = 2 := by
        rw [hnorm, hnorm]
        norm_num

/-- The integral of `(m/n)^{it}` over an interval of length `b - a` is bounded by the kernel
`meanSquareKernel N (b - a) m n`, for `1 ≤ m, n ≤ N`. -/
theorem norm_integral_exp_log_sub_le {N : ℕ} {a b : ℝ} (hab : a ≤ b) {m n : ℕ}
    (hm : m ∈ Finset.Icc 1 N) (hn : n ∈ Finset.Icc 1 N) :
    ‖∫ t in a..b, Complex.exp ((((Real.log m - Real.log n) * t : ℝ) : ℂ) * Complex.I)‖ ≤
      meanSquareKernel N (b - a) m n := by
  unfold meanSquareKernel
  by_cases hmn : m = n
  · subst hmn
    rw [if_pos rfl]
    have h := norm_integral_exp_mul_I_le_sub hab (Real.log m - Real.log m)
    have h2 : (0 : ℝ) ≤ 2 * N * (((m - m : ℕ) : ℝ)⁻¹ + ((m - m : ℕ) : ℝ)⁻¹) := by positivity
    linarith
  · rw [if_neg hmn, zero_add]
    have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (Finset.mem_Icc.mp hm).1
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Finset.mem_Icc.mp hn).1
    have hne : Real.log m - Real.log n ≠ 0 := by
      refine sub_ne_zero.mpr fun h => hmn ?_
      exact Nat.cast_injective (Real.log_injOn_pos (Set.mem_Ioi.mpr hm0) (Set.mem_Ioi.mpr hn0) h)
    exact (norm_integral_exp_mul_I_le hne a b).trans (two_div_abs_log_sub_log_le hm hn hmn)

/-! ### The mean square of an exponential sum with frequencies `log n` -/

/-- Expansion of the square: `∫_a^b |∑_n c_n e^{it log n}|² dt` is the double sum of
`c_m \bar c_n ∫_a^b e^{it (log m - log n)} dt`. -/
theorem ofReal_integral_normSq_sum_exp_log (s : Finset ℕ) (c : ℕ → ℂ) (a b : ℝ) :
    ((∫ t in a..b,
        ‖∑ n ∈ s, c n * Complex.exp (((Real.log n * t : ℝ) : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ s, ∑ n ∈ s, c m * (starRingEnd ℂ) (c n) *
        ∫ t in a..b, Complex.exp ((((Real.log m - Real.log n) * t : ℝ) : ℂ) * Complex.I) := by
  have hsq : ∀ t : ℝ,
      ((‖∑ n ∈ s, c n * Complex.exp (((Real.log n * t : ℝ) : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ) =
        ∑ m ∈ s, ∑ n ∈ s, c m * (starRingEnd ℂ) (c n) *
          Complex.exp ((((Real.log m - Real.log n) * t : ℝ) : ℂ) * Complex.I) := by
    intro t
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
    have hexp : ((Real.log m * t : ℝ) : ℂ) * Complex.I + ((Real.log n * t : ℝ) : ℂ) * -Complex.I =
        (((Real.log m - Real.log n) * t : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
      mul_mul_mul_comm, ← Complex.exp_add, hexp]
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [hsq]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [intervalIntegral.integral_const_mul]
    · intro n _
      exact Continuous.intervalIntegrable (by fun_prop) _ _
  · intro m _
    exact Continuous.intervalIntegrable (by fun_prop) _ _

/-- The mean-value estimate for the exponential sum `∑_{n ≤ N} c_n e^{it log n}`. -/
theorem integral_normSq_sum_exp_log_le (N : ℕ) (c : ℕ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b,
        ‖∑ n ∈ Finset.Icc 1 N, c n * Complex.exp (((Real.log n * t : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
      ((b - a) + 4 * N * (1 + Real.log N)) * ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 := by
  have h0 : 0 ≤ ∫ t in a..b,
      ‖∑ n ∈ Finset.Icc 1 N, c n * Complex.exp (((Real.log n * t : ℝ) : ℂ) * Complex.I)‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab fun t _ => sq_nonneg _
  have h2 : ∫ t in a..b,
      ‖∑ n ∈ Finset.Icc 1 N, c n * Complex.exp (((Real.log n * t : ℝ) : ℂ) * Complex.I)‖ ^ 2 ≤
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 N,
        ‖c m‖ * ‖c n‖ * meanSquareKernel N (b - a) m n := by
    rw [← Real.norm_of_nonneg h0, ← Complex.norm_real, ofReal_integral_normSq_sum_exp_log]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    rw [norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left (norm_integral_exp_log_sub_le hab hm hn) (by positivity)
  refine h2.trans ?_
  exact sum_sum_mul_mul_le_of_row_sum_le (Finset.Icc 1 N) (fun n => ‖c n‖)
    (meanSquareKernel N (b - a)) _
    (fun m _ n _ => meanSquareKernel_nonneg N (sub_nonneg.mpr hab) m n)
    (fun m _ n _ => meanSquareKernel_comm N (b - a) m n)
    (fun m hm => sum_meanSquareKernel_le (b - a) hm)

/-! ### Dirichlet polynomials -/

/-- The Dirichlet polynomial `P(t) = ∑_{1 ≤ n ≤ N} c_n n^{it}`. -/
noncomputable def dirichletPolynomial (c : ℕ → ℂ) (N : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, c n * (n : ℂ) ^ (Complex.I * (t : ℂ))

/-- The coefficients `i c_n log n` of the derivative of a Dirichlet polynomial. -/
noncomputable def dirichletDerivCoeff (c : ℕ → ℂ) (n : ℕ) : ℂ :=
  c n * (Complex.I * (Real.log n : ℂ))

/-- `n^{it} = e^{it log n}` for a positive integer `n`. -/
theorem natCast_cpow_I_mul {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    (n : ℂ) ^ (Complex.I * (t : ℂ)) = Complex.exp (((Real.log n * t : ℝ) : ℂ) * Complex.I) := by
  rw [Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn), ← Complex.natCast_log]
  congr 1
  push_cast
  ring

/-- A Dirichlet polynomial as an exponential sum with frequencies `log n`:
`∑_{n ≤ N} c_n n^{it} = ∑_{n ≤ N} c_n e^{it log n}`. -/
theorem dirichletPolynomial_eq_sum_exp (c : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    dirichletPolynomial c N t =
      ∑ n ∈ Finset.Icc 1 N, c n * Complex.exp (((Real.log n * t : ℝ) : ℂ) * Complex.I) := by
  unfold dirichletPolynomial
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := by
    have := (Finset.mem_Icc.mp hn).1
    omega
  rw [natCast_cpow_I_mul hn0 t]

/-- **Mean square of a Dirichlet polynomial**, explicit form with a natural cutoff:
`∫_a^b |∑_{n ≤ N} c_n n^{it}|² dt ≤ (b - a + 4 N (1 + log N)) ∑_{n ≤ N} |c_n|²`. -/
theorem integral_normSq_dirichletPolynomial_le_nat (c : ℕ → ℂ) (N : ℕ) {a b : ℝ}
    (hab : a ≤ b) :
    ∫ t in a..b, ‖dirichletPolynomial c N t‖ ^ 2 ≤
      ((b - a) + 4 * N * (1 + Real.log N)) * ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 := by
  simp_rw [dirichletPolynomial_eq_sum_exp]
  exact integral_normSq_sum_exp_log_le N c hab

/-- The derivative of `t ↦ e^{iωt}`. -/
theorem hasDerivAt_exp_ofReal_mul_I (ω t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (((ω * u : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((ω * t : ℝ) : ℂ) * Complex.I) * ((ω : ℂ) * Complex.I)) t := by
  have h1 : HasDerivAt (fun u : ℝ => ω * u) ω t := by
    simpa using (hasDerivAt_id t).const_mul ω
  have h2 : HasDerivAt (fun u : ℝ => ((ω * u : ℝ) : ℂ) * Complex.I) ((ω : ℂ) * Complex.I) t :=
    h1.ofReal_comp.mul_const Complex.I
  exact h2.cexp

/-- The derivative of a Dirichlet polynomial is the Dirichlet polynomial with coefficients
`i c_n log n`. -/
theorem hasDerivAt_dirichletPolynomial (c : ℕ → ℂ) (N : ℕ) (t : ℝ) :
    HasDerivAt (dirichletPolynomial c N) (dirichletPolynomial (dirichletDerivCoeff c) N t) t := by
  have hfun : dirichletPolynomial c N = fun u : ℝ =>
      ∑ n ∈ Finset.Icc 1 N, c n * Complex.exp (((Real.log n * u : ℝ) : ℂ) * Complex.I) :=
    funext fun u => dirichletPolynomial_eq_sum_exp c N u
  have hterm : ∀ n ∈ Finset.Icc 1 N, HasDerivAt
      (fun u : ℝ => c n * Complex.exp (((Real.log n * u : ℝ) : ℂ) * Complex.I))
      (dirichletDerivCoeff c n * Complex.exp (((Real.log n * t : ℝ) : ℂ) * Complex.I)) t := by
    intro n _
    refine ((hasDerivAt_exp_ofReal_mul_I (Real.log n) t).const_mul (c n)).congr_deriv ?_
    unfold dirichletDerivCoeff
    ring
  have hsum := HasDerivAt.fun_sum hterm
  rw [hfun, dirichletPolynomial_eq_sum_exp]
  exact hsum

/-- A Dirichlet polynomial is continuous in `t`. -/
theorem continuous_dirichletPolynomial (c : ℕ → ℂ) (N : ℕ) :
    Continuous (dirichletPolynomial c N) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_dirichletPolynomial c N t).continuousAt

/-- The square sum of the coefficients of the derivative:
`∑_{n ≤ N} |i c_n log n|² ≤ (log N)² ∑_{n ≤ N} |c_n|²`. -/
theorem sum_normSq_dirichletDerivCoeff_le (c : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, ‖dirichletDerivCoeff c n‖ ^ 2 ≤
      Real.log N ^ 2 * ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn' := Finset.mem_Icc.mp hn
  have hlog0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hlog : Real.log n ≤ Real.log N :=
    Real.log_le_log (Nat.cast_pos.mpr hn'.1) (Nat.cast_le.mpr hn'.2)
  have hnorm : ‖dirichletDerivCoeff c n‖ = ‖c n‖ * Real.log n := by
    unfold dirichletDerivCoeff
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg hlog0]
  rw [hnorm, mul_pow, mul_comm]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlog0 hlog 2) (sq_nonneg _)

/-! ### The Sobolev inequality and well-spaced points -/

/-- A one-dimensional Sobolev inequality (Gallagher): for a continuously differentiable real
function, `g(t) ≤ ∫_{t-1/2}^{t+1/2} (g + |g'|)`. -/
theorem le_integral_add_abs_deriv {g g' : ℝ → ℝ} (hg : ∀ u, HasDerivAt g (g' u) u)
    (hg' : Continuous g') (t : ℝ) :
    g t ≤ ∫ u in (t - 1 / 2)..(t + 1 / 2), (g u + |g' u|) := by
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun u => (hg u).continuousAt
  have hab : t - 1 / 2 ≤ t + 1 / 2 := by linarith
  have hM0 : 0 ≤ ∫ v in (t - 1 / 2)..(t + 1 / 2), |g' v| :=
    intervalIntegral.integral_nonneg hab fun _ _ => abs_nonneg _
  -- `g t ≤ g u + ∫ |g'|` for every `u` in the interval
  have key : ∀ u ∈ Set.Icc (t - 1 / 2) (t + 1 / 2),
      g t - ∫ v in (t - 1 / 2)..(t + 1 / 2), |g' v| ≤ g u := by
    intro u hu
    have h1 : ∫ v in u..t, g' v = g t - g u :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hg v)
        (hg'.intervalIntegrable _ _)
    have h2 : |(∫ v in u..t, g' v)| ≤ |(∫ v in u..t, |g' v|)| := by
      simpa only [Real.norm_eq_abs] using
        intervalIntegral.norm_integral_le_abs_integral_norm (f := g') (a := u) (b := t)
          (μ := MeasureTheory.volume)
    have h3 : |(∫ v in u..t, |g' v|)| ≤ |(∫ v in (t - 1 / 2)..(t + 1 / 2), |g' v|)| := by
      refine intervalIntegral.abs_integral_mono_interval ?_
        (Filter.Eventually.of_forall fun _ => abs_nonneg _) (hg'.abs.intervalIntegrable _ _)
      rw [Set.uIoc_of_le hab]
      exact Set.Ioc_subset_Ioc (le_min hu.1 (by linarith)) (max_le hu.2 (by linarith))
    have h4 : |(∫ v in (t - 1 / 2)..(t + 1 / 2), |g' v|)| =
        ∫ v in (t - 1 / 2)..(t + 1 / 2), |g' v| := abs_of_nonneg hM0
    have h5 := le_abs_self (∫ v in u..t, g' v)
    linarith
  have hconst : ∫ _u in (t - 1 / 2)..(t + 1 / 2),
      (g t - ∫ v in (t - 1 / 2)..(t + 1 / 2), |g' v|) =
      g t - ∫ v in (t - 1 / 2)..(t + 1 / 2), |g' v| := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hmono : ∫ _u in (t - 1 / 2)..(t + 1 / 2),
      (g t - ∫ v in (t - 1 / 2)..(t + 1 / 2), |g' v|) ≤
      ∫ u in (t - 1 / 2)..(t + 1 / 2), g u :=
    intervalIntegral.integral_mono_on hab (continuous_const.intervalIntegrable _ _)
      (hgc.intervalIntegrable _ _) key
  have hi1 : IntervalIntegrable g MeasureTheory.volume (t - 1 / 2) (t + 1 / 2) :=
    hgc.intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun u => |g' u|) MeasureTheory.volume (t - 1 / 2) (t + 1 / 2) :=
    hg'.abs.intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi1 hi2]
  linarith

/-- The Sobolev inequality for a complex-valued function:
`|f(t)|² ≤ ∫_{t-1/2}^{t+1/2} (2 |f|² + |f'|²)`. -/
theorem normSq_le_integral_of_hasDerivAt {f f' : ℝ → ℂ} (hf : ∀ u, HasDerivAt f (f' u) u)
    (hf' : Continuous f') (t : ℝ) :
    ‖f t‖ ^ 2 ≤ ∫ u in (t - 1 / 2)..(t + 1 / 2), (2 * ‖f u‖ ^ 2 + ‖f' u‖ ^ 2) := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun u => (hf u).continuousAt
  have hgd : ∀ u, HasDerivAt (fun v => ‖f v‖ ^ 2) (2 * inner ℝ (f u) (f' u)) u :=
    fun u => (hf u).norm_sq
  have hg'c : Continuous fun u => 2 * inner ℝ (f u) (f' u) :=
    continuous_const.mul (Continuous.inner (𝕜 := ℝ) hfc hf')
  have h1 : ‖f t‖ ^ 2 ≤ ∫ u in (t - 1 / 2)..(t + 1 / 2),
      (‖f u‖ ^ 2 + |2 * inner ℝ (f u) (f' u)|) :=
    le_integral_add_abs_deriv (g := fun v => ‖f v‖ ^ 2) hgd hg'c t
  refine h1.trans ?_
  refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ fun u _ => ?_
  · exact ((hfc.norm.pow 2).add hg'c.abs).intervalIntegrable _ _
  · exact ((continuous_const.mul (hfc.norm.pow 2)).add (hf'.norm.pow 2)).intervalIntegrable _ _
  · have h2 : |inner ℝ (f u) (f' u)| ≤ ‖f u‖ * ‖f' u‖ := abs_real_inner_le_norm _ _
    rw [abs_mul, abs_two]
    nlinarith [sq_nonneg (‖f u‖ - ‖f' u‖)]

/-- The unit intervals centred at `1`-separated points of `[a, b]` are pairwise disjoint and
contained in `[a - 1/2, b + 1/2]`, so the integrals of a nonnegative function over them add up
to at most its integral over `[a - 1/2, b + 1/2]`. -/
theorem sum_integral_unit_interval_le {h : ℝ → ℝ} (hh : Continuous h) (hh0 : ∀ u, 0 ≤ h u)
    {a b : ℝ} (hab : a ≤ b) (𝒯 : Finset ℝ) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc a b)
    (hsep : ∀ t ∈ 𝒯, ∀ t' ∈ 𝒯, t ≠ t' → 1 ≤ |t - t'|) :
    ∑ t ∈ 𝒯, ∫ u in (t - 1 / 2)..(t + 1 / 2), h u ≤ ∫ u in (a - 1 / 2)..(b + 1 / 2), h u := by
  have hab' : a - 1 / 2 ≤ b + 1 / 2 := by linarith
  have h1 : ∀ t ∈ 𝒯, ∫ u in (t - 1 / 2)..(t + 1 / 2), h u =
      ∫ u in Set.Ioc (t - 1 / 2) (t + 1 / 2), h u :=
    fun t _ => intervalIntegral.integral_of_le (by linarith)
  have hdisj : (↑𝒯 : Set ℝ).Pairwise
      (Function.onFun Disjoint fun t => Set.Ioc (t - 1 / 2) (t + 1 / 2)) := by
    intro t ht t' ht' hne
    rw [Function.onFun, Set.disjoint_left]
    intro u hu hu'
    have hsep' := hsep t (Finset.mem_coe.mp ht) t' (Finset.mem_coe.mp ht') hne
    rw [Set.mem_Ioc] at hu hu'
    have hlt : |t - t'| < 1 := by
      rw [abs_lt]
      constructor <;> linarith [hu.1, hu.2, hu'.1, hu'.2]
    linarith
  have hunion : ∫ u in ⋃ t ∈ 𝒯, Set.Ioc (t - 1 / 2) (t + 1 / 2), h u =
      ∑ t ∈ 𝒯, ∫ u in Set.Ioc (t - 1 / 2) (t + 1 / 2), h u :=
    MeasureTheory.integral_biUnion_finset 𝒯 (fun t _ => measurableSet_Ioc) hdisj
      (fun t _ => hh.integrableOn_Ioc)
  have hsubset : (⋃ t ∈ 𝒯, Set.Ioc (t - 1 / 2) (t + 1 / 2)) ⊆
      Set.Ioc (a - 1 / 2) (b + 1 / 2) :=
    Set.iUnion₂_subset fun t ht =>
      Set.Ioc_subset_Ioc (by linarith [(hsub t ht).1]) (by linarith [(hsub t ht).2])
  rw [Finset.sum_congr rfl h1, ← hunion, intervalIntegral.integral_of_le hab']
  exact MeasureTheory.setIntegral_mono_set hh.integrableOn_Ioc
    (Filter.Eventually.of_forall hh0) (Filter.Eventually.of_forall hsubset)

/-- **Dirichlet polynomials at well-spaced points**, explicit form with a natural cutoff: for a
finite set `𝒯 ⊆ [a, b]` of reals with pairwise distances at least `1`,
`∑_{t ∈ 𝒯} |P(t)|² ≤ (b - a + 1 + 4 N (1 + log N)) (2 + (log N)²) ∑_{n ≤ N} |c_n|²`. -/
theorem sum_normSq_dirichletPolynomial_le_nat (c : ℕ → ℂ) (N : ℕ) {a b : ℝ} (hab : a ≤ b)
    (𝒯 : Finset ℝ) (hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc a b)
    (hsep : ∀ t ∈ 𝒯, ∀ t' ∈ 𝒯, t ≠ t' → 1 ≤ |t - t'|) :
    ∑ t ∈ 𝒯, ‖dirichletPolynomial c N t‖ ^ 2 ≤
      ((b - a) + 1 + 4 * N * (1 + Real.log N)) * (2 + Real.log N ^ 2) *
        ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 := by
  have hPc : Continuous (dirichletPolynomial c N) := continuous_dirichletPolynomial c N
  have hP'c : Continuous (dirichletPolynomial (dirichletDerivCoeff c) N) :=
    continuous_dirichletPolynomial _ N
  -- the Sobolev inequality at each point
  have h1 : ∀ t ∈ 𝒯, ‖dirichletPolynomial c N t‖ ^ 2 ≤
      ∫ u in (t - 1 / 2)..(t + 1 / 2), (2 * ‖dirichletPolynomial c N u‖ ^ 2 +
        ‖dirichletPolynomial (dirichletDerivCoeff c) N u‖ ^ 2) :=
    fun t _ => normSq_le_integral_of_hasDerivAt
      (fun u => hasDerivAt_dirichletPolynomial c N u) hP'c t
  -- summing over the well-spaced points
  have hcont : Continuous fun u => 2 * ‖dirichletPolynomial c N u‖ ^ 2 +
      ‖dirichletPolynomial (dirichletDerivCoeff c) N u‖ ^ 2 :=
    (continuous_const.mul (hPc.norm.pow 2)).add (hP'c.norm.pow 2)
  have h2 : ∑ t ∈ 𝒯, ∫ u in (t - 1 / 2)..(t + 1 / 2), (2 * ‖dirichletPolynomial c N u‖ ^ 2 +
        ‖dirichletPolynomial (dirichletDerivCoeff c) N u‖ ^ 2) ≤
      ∫ u in (a - 1 / 2)..(b + 1 / 2), (2 * ‖dirichletPolynomial c N u‖ ^ 2 +
        ‖dirichletPolynomial (dirichletDerivCoeff c) N u‖ ^ 2) :=
    sum_integral_unit_interval_le hcont (fun u => by positivity) hab 𝒯 hsub hsep
  -- the mean square of `P` and of `P'` over `[a - 1/2, b + 1/2]`
  have hab' : a - 1 / 2 ≤ b + 1 / 2 := by linarith
  have h3 : ∫ u in (a - 1 / 2)..(b + 1 / 2), (2 * ‖dirichletPolynomial c N u‖ ^ 2 +
        ‖dirichletPolynomial (dirichletDerivCoeff c) N u‖ ^ 2) =
      2 * (∫ u in (a - 1 / 2)..(b + 1 / 2), ‖dirichletPolynomial c N u‖ ^ 2) +
        ∫ u in (a - 1 / 2)..(b + 1 / 2),
          ‖dirichletPolynomial (dirichletDerivCoeff c) N u‖ ^ 2 := by
    have hi1 : IntervalIntegrable (fun u => 2 * ‖dirichletPolynomial c N u‖ ^ 2)
        MeasureTheory.volume (a - 1 / 2) (b + 1 / 2) :=
      (continuous_const.mul (hPc.norm.pow 2)).intervalIntegrable _ _
    have hi2 : IntervalIntegrable
        (fun u => ‖dirichletPolynomial (dirichletDerivCoeff c) N u‖ ^ 2)
        MeasureTheory.volume (a - 1 / 2) (b + 1 / 2) :=
      (hP'c.norm.pow 2).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul]
  have h4 := integral_normSq_dirichletPolynomial_le_nat c N hab'
  have h5 := integral_normSq_dirichletPolynomial_le_nat (dirichletDerivCoeff c) N hab'
  have h6 := sum_normSq_dirichletDerivCoeff_le c N
  have hlen : b + 1 / 2 - (a - 1 / 2) + 4 * (N : ℝ) * (1 + Real.log N) =
      (b - a) + 1 + 4 * N * (1 + Real.log N) := by ring
  have hB0 : 0 ≤ (b - a) + 1 + 4 * (N : ℝ) * (1 + Real.log N) :=
    add_nonneg (add_nonneg (sub_nonneg.mpr hab) zero_le_one) (by positivity)
  rw [hlen] at h4 h5
  have h7 := mul_le_mul_of_nonneg_left h6 hB0
  calc ∑ t ∈ 𝒯, ‖dirichletPolynomial c N t‖ ^ 2
      ≤ ∑ t ∈ 𝒯, ∫ u in (t - 1 / 2)..(t + 1 / 2), (2 * ‖dirichletPolynomial c N u‖ ^ 2 +
          ‖dirichletPolynomial (dirichletDerivCoeff c) N u‖ ^ 2) := Finset.sum_le_sum h1
    _ ≤ ∫ u in (a - 1 / 2)..(b + 1 / 2), (2 * ‖dirichletPolynomial c N u‖ ^ 2 +
          ‖dirichletPolynomial (dirichletDerivCoeff c) N u‖ ^ 2) := h2
    _ = 2 * (∫ u in (a - 1 / 2)..(b + 1 / 2), ‖dirichletPolynomial c N u‖ ^ 2) +
          ∫ u in (a - 1 / 2)..(b + 1 / 2),
            ‖dirichletPolynomial (dirichletDerivCoeff c) N u‖ ^ 2 := h3
    _ ≤ ((b - a) + 1 + 4 * N * (1 + Real.log N)) * (2 + Real.log N ^ 2) *
          ∑ n ∈ Finset.Icc 1 N, ‖c n‖ ^ 2 := by
        linarith

/-! ### Real cutoffs: the statements of the papers -/

/-- `4 N (1 + log N) ≤ 8 Y log (2Y)` for `N = ⌊Y⌋₊`, `Y ≥ 1`. -/
theorem four_mul_floor_mul_one_add_log_le {Y : ℝ} (hY : 1 ≤ Y) :
    4 * ((⌊Y⌋₊ : ℕ) : ℝ) * (1 + Real.log ((⌊Y⌋₊ : ℕ) : ℝ)) ≤ 8 * (Y * Real.log (2 * Y)) := by
  have hY0 : 0 ≤ Y := zero_le_one.trans hY
  have hN : ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Y := Nat.floor_le hY0
  have hN0 : (0 : ℝ) < ((⌊Y⌋₊ : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.floor_pos.mpr hY)
  have hlog : Real.log ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Real.log Y := Real.log_le_log hN0 hN
  have h0 : 0 ≤ Real.log ((⌊Y⌋₊ : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have h1 : 1 + Real.log Y ≤ 2 * Real.log (2 * Y) := one_add_log_le_two_mul_log_two_mul hY
  calc 4 * ((⌊Y⌋₊ : ℕ) : ℝ) * (1 + Real.log ((⌊Y⌋₊ : ℕ) : ℝ))
      ≤ 4 * Y * (2 * Real.log (2 * Y)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hN (by norm_num)) (by linarith) (by linarith)
          (mul_nonneg (by norm_num) hY0)
    _ = 8 * (Y * Real.log (2 * Y)) := by ring

/-- `2 + (log N)² ≤ 6 (log (2Y))²` for `N = ⌊Y⌋₊`, `Y ≥ 1`. -/
theorem two_add_log_floor_sq_le {Y : ℝ} (hY : 1 ≤ Y) :
    2 + Real.log ((⌊Y⌋₊ : ℕ) : ℝ) ^ 2 ≤ 6 * Real.log (2 * Y) ^ 2 := by
  have hY0 : 0 ≤ Y := zero_le_one.trans hY
  have hN : ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Y := Nat.floor_le hY0
  have hN0 : (0 : ℝ) < ((⌊Y⌋₊ : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.floor_pos.mpr hY)
  have hlog : Real.log ((⌊Y⌋₊ : ℕ) : ℝ) ≤ Real.log Y := Real.log_le_log hN0 hN
  have h0 : 0 ≤ Real.log ((⌊Y⌋₊ : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg hY
  have h2 : (69 : ℝ) / 100 < Real.log 2 := lt_trans (by norm_num) Real.log_two_gt_d9
  have h3 : (47 : ℝ) / 100 ≤ Real.log 2 ^ 2 := by nlinarith
  have h4 : 0 ≤ Real.log 2 * Real.log Y := mul_nonneg (by linarith) hlogY
  have h5 : Real.log ((⌊Y⌋₊ : ℕ) : ℝ) ^ 2 ≤ Real.log Y ^ 2 := pow_le_pow_left₀ h0 hlog 2
  rw [Real.log_mul two_ne_zero (zero_lt_one.trans_le hY).ne']
  nlinarith

/-- **Mean squares of Dirichlet polynomials** (`eq:dirichlet-mean` of `lem:moment-bounds` in
P-02, first part of `lem:dirichlet-mean` in S-01): there is an absolute constant `C > 0` such
that for `P(t) = ∑_{1 ≤ n ≤ Y} c_n n^{it}` with `Y ≥ 1` and every interval `[a, b]`,
`∫_a^b |P(t)|² dt ≤ C (b - a + Y log (2Y)) ∑_n |c_n|²`. One may take `C = 8`. -/
theorem integral_normSq_dirichletPolynomial_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y : ℝ) (c : ℕ → ℂ) (a b : ℝ), 1 ≤ Y → a ≤ b →
      ∫ t in a..b, ‖∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, c n * (n : ℂ) ^ (Complex.I * (t : ℂ))‖ ^ 2 ≤
        C * ((b - a) + Y * Real.log (2 * Y)) * ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, ‖c n‖ ^ 2 := by
  refine ⟨8, by norm_num, fun Y c a b hY hab => ?_⟩
  refine (integral_normSq_dirichletPolynomial_le_nat c ⌊Y⌋₊ hab).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  linarith [four_mul_floor_mul_one_add_log_le hY, sub_nonneg.mpr hab]

/-- The mean-square bound for the integral over an arbitrary subset `I` of `[a, b]`, in
particular over any interval with endpoints `a ≤ b` (open, closed or half-open). -/
theorem setIntegral_normSq_dirichletPolynomial_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y : ℝ) (c : ℕ → ℂ) (a b : ℝ) (I : Set ℝ), 1 ≤ Y → a ≤ b →
      I ⊆ Set.Icc a b →
      ∫ t in I, ‖∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, c n * (n : ℂ) ^ (Complex.I * (t : ℂ))‖ ^ 2 ≤
        C * ((b - a) + Y * Real.log (2 * Y)) * ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, ‖c n‖ ^ 2 := by
  obtain ⟨C, hC, h⟩ := integral_normSq_dirichletPolynomial_le
  refine ⟨C, hC, fun Y c a b I hY hab hI => ?_⟩
  have hcont : Continuous fun t : ℝ =>
      ‖∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, c n * (n : ℂ) ^ (Complex.I * (t : ℂ))‖ ^ 2 :=
    (continuous_dirichletPolynomial c ⌊Y⌋₊).norm.pow 2
  calc ∫ t in I, ‖∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, c n * (n : ℂ) ^ (Complex.I * (t : ℂ))‖ ^ 2
      ≤ ∫ t in Set.Icc a b,
          ‖∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, c n * (n : ℂ) ^ (Complex.I * (t : ℂ))‖ ^ 2 :=
        MeasureTheory.setIntegral_mono_set hcont.integrableOn_Icc
          (Filter.Eventually.of_forall fun t => sq_nonneg _) (Filter.Eventually.of_forall hI)
    _ = ∫ t in a..b,
          ‖∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, c n * (n : ℂ) ^ (Complex.I * (t : ℂ))‖ ^ 2 := by
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hab]
    _ ≤ C * ((b - a) + Y * Real.log (2 * Y)) * ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, ‖c n‖ ^ 2 :=
        h Y c a b hY hab

/-- **Dirichlet polynomials at well-spaced points** (`eq:dirichlet-spaced` of
`lem:moment-bounds` in P-02, `eq:discrete-mean` of `lem:dirichlet-mean` in S-01): there is an
absolute constant `C > 0` such that for `P(t) = ∑_{1 ≤ n ≤ Y} c_n n^{it}` with `Y ≥ 1` and
every finite set `𝒯` of reals contained in an interval `[a, b]` with pairwise distances at
least `1`,
`∑_{t ∈ 𝒯} |P(t)|² ≤ C (b - a + 1 + Y log (2Y)) (log (2Y))² ∑_n |c_n|²`. One may take
`C = 48`. -/
theorem sum_normSq_dirichletPolynomial_le_of_separated :
    ∃ C : ℝ, 0 < C ∧ ∀ (Y : ℝ) (c : ℕ → ℂ) (a b : ℝ) (𝒯 : Finset ℝ), 1 ≤ Y → a ≤ b →
      (∀ t ∈ 𝒯, t ∈ Set.Icc a b) → (∀ t ∈ 𝒯, ∀ t' ∈ 𝒯, t ≠ t' → 1 ≤ |t - t'|) →
      ∑ t ∈ 𝒯, ‖∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, c n * (n : ℂ) ^ (Complex.I * (t : ℂ))‖ ^ 2 ≤
        C * ((b - a) + 1 + Y * Real.log (2 * Y)) * Real.log (2 * Y) ^ 2 *
          ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, ‖c n‖ ^ 2 := by
  refine ⟨48, by norm_num, fun Y c a b 𝒯 hY hab hsub hsep => ?_⟩
  refine (sum_normSq_dirichletPolynomial_le_nat c ⌊Y⌋₊ hab 𝒯 hsub hsep).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hA : (b - a) + 1 + 4 * ((⌊Y⌋₊ : ℕ) : ℝ) * (1 + Real.log ((⌊Y⌋₊ : ℕ) : ℝ)) ≤
      8 * ((b - a) + 1 + Y * Real.log (2 * Y)) := by
    linarith [four_mul_floor_mul_one_add_log_le hY, sub_nonneg.mpr hab]
  have hB : 2 + Real.log ((⌊Y⌋₊ : ℕ) : ℝ) ^ 2 ≤ 6 * Real.log (2 * Y) ^ 2 :=
    two_add_log_floor_sq_le hY
  have hA0 : 0 ≤ 8 * ((b - a) + 1 + Y * Real.log (2 * Y)) :=
    le_trans (add_nonneg (add_nonneg (sub_nonneg.mpr hab) zero_le_one) (by positivity)) hA
  calc ((b - a) + 1 + 4 * ((⌊Y⌋₊ : ℕ) : ℝ) * (1 + Real.log ((⌊Y⌋₊ : ℕ) : ℝ))) *
        (2 + Real.log ((⌊Y⌋₊ : ℕ) : ℝ) ^ 2)
      ≤ 8 * ((b - a) + 1 + Y * Real.log (2 * Y)) * (6 * Real.log (2 * Y) ^ 2) :=
        mul_le_mul hA hB (by positivity) hA0
    _ = 48 * ((b - a) + 1 + Y * Real.log (2 * Y)) * Real.log (2 * Y) ^ 2 := by ring

end SimultaneousPrimitiveRoots.Unconditional.Classical
