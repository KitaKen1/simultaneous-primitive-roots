module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ExceptionalCells
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.LowFrequencyTools
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ExtractionErrorProof
public import SimultaneousPrimitiveRoots.Unconditional.Classical.DirichletMeanSquare
public import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Tools for the products of normalized polynomials at high times

Common tools of the tuple products and of the constant products (`[P-06:0763–0772, 0834–0925]`).

* `continuous_normPoly`, `norm_normPoly_le`: continuity in the time and the trivial bound.
* `integral_normSq_normPoly_le`: the mean-value theorem (eq:dirichlet-mean) for a normalized
  polynomial supported on `1 ≤ n ≤ W`.
* `collapseCoeff`, `normPoly_mul_normPoly`, `norm_collapseCoeff_le`: "collapse all remaining
  factors": the product of two normalized polynomials is the normalized polynomial of the
  convolution of the coefficients, and a convolution with a set of primes with weights of modulus
  `≤ 1` costs the number of primes of the set dividing the index.
* `abs_mem_of_highRange`, `sub_le_of_highRange`: the times of an interval of
  `{lo ≤ |t| ≤ hi}`.
* `rpow_neg_sq_mul_le`: `(L^{-s})² L^n (L^c)² ≤ L^{-A}` when `A + n + 2c ≤ 2s`.
* `eventually_productScale`: (cor:length-dominates-time) and the sizes of the scales: for
  `x exp(2 L^{.39} - c₁) ≤ Y ≤ x exp(c₂ L^{.46} log L)` and `exp(L^{.27})/2 ≤ P ≤ exp(L^{.36})`,
  `2T_0 ≤ a₁ Y / (4P)`, `4 a₂ Y ≤ x²` and `2T_0 ≤ x²` for large `x`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open Filter
open scoped Topology

noncomputable section

/-! ### Normalized polynomials -/

/-- A normalized polynomial without the index `0` is continuous in the time. -/
theorem continuous_normPoly (R : ℝ) {s : Finset ℕ} (hs : ∀ n ∈ s, n ≠ 0) (c : ℕ → ℂ) :
    Continuous (normPoly R s c) := by
  have h : normPoly R s c =
      fun t : ℝ => (R : ℂ)⁻¹ * ∑ n ∈ s, c n * (n : ℂ) ^ ((t : ℂ) * Complex.I) := rfl
  rw [h]
  refine continuous_const.mul (continuous_finsetSum _ fun n hn => ?_)
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hs n hn)
  exact continuous_const.mul
    ((Complex.continuous_ofReal.mul continuous_const).const_cpow (Or.inl hn0))

/-- The trivial bound `|R^{-1} ∑_{n ∈ s} c_n n^{it}| ≤ R^{-1} #s · B` for `|c_n| ≤ B`. -/
theorem norm_normPoly_le {R B : ℝ} (hR : 0 < R) {s : Finset ℕ} {c : ℕ → ℂ}
    (hs : ∀ n ∈ s, 0 < n) (hc : ∀ n ∈ s, ‖c n‖ ≤ B) (t : ℝ) :
    ‖normPoly R s c t‖ ≤ R⁻¹ * ((s.card : ℝ) * B) := by
  have hnp : normPoly R s c t =
      (R : ℂ)⁻¹ * ∑ n ∈ s, c n * (n : ℂ) ^ ((t : ℂ) * Complex.I) := rfl
  rw [hnp, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR.le]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hR.le)
  calc ‖∑ n ∈ s, c n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖
      ≤ ∑ n ∈ s, ‖c n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ s, B := Finset.sum_le_sum fun n hn => by
        rw [norm_mul, norm_natCast_cpow_mul_I (hs n hn), mul_one]
        exact hc n hn
    _ = (s.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **The mean-value theorem for a normalized polynomial** supported on `1 ≤ n ≤ W`:
`∫_a^b |R^{-1} ∑_{n ∈ s} c_n n^{it}|² dt ≤ R^{-2} (b - a + 4W(1 + log W)) ∑_{n ∈ s} |c_n|²`. -/
theorem integral_normSq_normPoly_le {R : ℝ} {s : Finset ℕ} {W : ℕ} (hs : s ⊆ Finset.Icc 1 W)
    (c : ℕ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in a..b, ‖normPoly R s c t‖ ^ 2 ≤
      (R ^ 2)⁻¹ * (((b - a) + 4 * (W : ℝ) * (1 + Real.log (W : ℝ))) *
        ∑ n ∈ s, ‖c n‖ ^ 2) := by
  classical
  obtain ⟨c', hc'⟩ : ∃ c' : ℕ → ℂ, ∀ n, c' n = if n ∈ s then c n else 0 :=
    ⟨fun n => if n ∈ s then c n else 0, fun _ => rfl⟩
  have hpoly : ∀ t : ℝ, normPoly R s c t = (R : ℂ)⁻¹ *
      SimultaneousPrimitiveRoots.Unconditional.Classical.dirichletPolynomial c' W t := by
    intro t
    have hnp : normPoly R s c t =
        (R : ℂ)⁻¹ * ∑ n ∈ s, c n * (n : ℂ) ^ ((t : ℂ) * Complex.I) := rfl
    have hdp : SimultaneousPrimitiveRoots.Unconditional.Classical.dirichletPolynomial c' W t =
        ∑ n ∈ Finset.Icc 1 W, c' n * (n : ℂ) ^ (Complex.I * (t : ℂ)) := rfl
    have h1 : ∑ n ∈ s, c n * (n : ℂ) ^ ((t : ℂ) * Complex.I) =
        ∑ n ∈ s, c' n * (n : ℂ) ^ (Complex.I * (t : ℂ)) :=
      Finset.sum_congr rfl fun n hn => by
        rw [hc' n, if_pos hn, mul_comm Complex.I (t : ℂ)]
    have h2 : ∑ n ∈ s, c' n * (n : ℂ) ^ (Complex.I * (t : ℂ)) =
        ∑ n ∈ Finset.Icc 1 W, c' n * (n : ℂ) ^ (Complex.I * (t : ℂ)) :=
      Finset.sum_subset hs fun n _ hn => by rw [hc' n, if_neg hn, zero_mul]
    rw [hnp, hdp, h1, h2]
  have hnorm : ∀ t : ℝ, ‖normPoly R s c t‖ ^ 2 = (R ^ 2)⁻¹ *
      ‖SimultaneousPrimitiveRoots.Unconditional.Classical.dirichletPolynomial c' W t‖ ^ 2 := by
    intro t
    rw [hpoly t, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, mul_pow, inv_pow,
      sq_abs]
  have hcoef : ∑ n ∈ Finset.Icc 1 W, ‖c' n‖ ^ 2 = ∑ n ∈ s, ‖c n‖ ^ 2 := by
    have h1 : ∑ n ∈ s, ‖c n‖ ^ 2 = ∑ n ∈ s, ‖c' n‖ ^ 2 :=
      Finset.sum_congr rfl fun n hn => by rw [hc' n, if_pos hn]
    have h2 : ∑ n ∈ s, ‖c' n‖ ^ 2 = ∑ n ∈ Finset.Icc 1 W, ‖c' n‖ ^ 2 :=
      Finset.sum_subset hs fun n _ hn => by
        rw [hc' n, if_neg hn, norm_zero]
        exact zero_pow two_ne_zero
    rw [h1, h2]
  have hmv :=
    SimultaneousPrimitiveRoots.Unconditional.Classical.integral_normSq_dirichletPolynomial_le_nat
      c' W hab
  rw [hcoef] at hmv
  have hfun : (fun t : ℝ => ‖normPoly R s c t‖ ^ 2) = fun t : ℝ => (R ^ 2)⁻¹ *
      ‖SimultaneousPrimitiveRoots.Unconditional.Classical.dirichletPolynomial c' W t‖ ^ 2 :=
    funext hnorm
  calc ∫ t in a..b, ‖normPoly R s c t‖ ^ 2
      = ∫ t in a..b, (R ^ 2)⁻¹ *
          ‖SimultaneousPrimitiveRoots.Unconditional.Classical.dirichletPolynomial c' W t‖ ^ 2 :=
        congrArg (fun g : ℝ → ℝ => ∫ t in a..b, g t) hfun
    _ = (R ^ 2)⁻¹ * ∫ t in a..b,
          ‖SimultaneousPrimitiveRoots.Unconditional.Classical.dirichletPolynomial c' W t‖ ^ 2 :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ (R ^ 2)⁻¹ * (((b - a) + 4 * (W : ℝ) * (1 + Real.log (W : ℝ))) *
          ∑ n ∈ s, ‖c n‖ ^ 2) := mul_le_mul_of_nonneg_left hmv (inv_nonneg.mpr (sq_nonneg R))

/-! ### Collapsing two factors -/

/-- The coefficients of the product of two Dirichlet polynomials:
`d_w = ∑_{l ∈ J, u ∈ U, l u = w} α_l c_u`. -/
def collapseCoeff (J U : Finset ℕ) (α c : ℕ → ℂ) (w : ℕ) : ℂ :=
  ∑ x ∈ (J ×ˢ U).filter (fun x : ℕ × ℕ => x.1 * x.2 = w), α x.1 * c x.2

/-- `(∑_{l ∈ J} α_l l^z)(∑_{u ∈ U} c_u u^z) = ∑_{w ≤ W} d_w w^z` when all products `l u` lie in
`[1, W]`. -/
theorem sum_mul_sum_eq_sum_collapseCoeff (J U : Finset ℕ) (α c : ℕ → ℂ) (z : ℂ) {W : ℕ}
    (hW : ∀ x ∈ J ×ˢ U, x.1 * x.2 ∈ Finset.Icc 1 W) :
    (∑ l ∈ J, α l * (l : ℂ) ^ z) * (∑ u ∈ U, c u * (u : ℂ) ^ z) =
      ∑ w ∈ Finset.Icc 1 W, collapseCoeff J U α c w * (w : ℂ) ^ z := by
  have h1 : (∑ l ∈ J, α l * (l : ℂ) ^ z) * (∑ u ∈ U, c u * (u : ℂ) ^ z) =
      ∑ x ∈ J ×ˢ U, α x.1 * c x.2 * ((x.1 * x.2 : ℕ) : ℂ) ^ z := by
    rw [Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun u _ => ?_
    show α l * (l : ℂ) ^ z * (c u * (u : ℂ) ^ z) = α l * c u * ((l * u : ℕ) : ℂ) ^ z
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
    ring
  have h2 : ∑ x ∈ J ×ˢ U, α x.1 * c x.2 * ((x.1 * x.2 : ℕ) : ℂ) ^ z =
      ∑ w ∈ Finset.Icc 1 W,
        ∑ x ∈ (J ×ˢ U).filter (fun x : ℕ × ℕ => x.1 * x.2 = w),
          α x.1 * c x.2 * ((x.1 * x.2 : ℕ) : ℂ) ^ z :=
    (Finset.sum_fiberwise_of_maps_to hW _).symm
  rw [h1, h2]
  refine Finset.sum_congr rfl fun w _ => ?_
  unfold collapseCoeff
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.mp hx).2]

/-- **Collapsing two normalized polynomials** (`[P-06:0763–0764]`: "collapse all remaining
factors"). -/
theorem normPoly_mul_normPoly (R₁ R₂ : ℝ) (J U : Finset ℕ) (α c : ℕ → ℂ) {W : ℕ}
    (hW : ∀ x ∈ J ×ˢ U, x.1 * x.2 ∈ Finset.Icc 1 W) (t : ℝ) :
    normPoly R₁ J α t * normPoly R₂ U c t =
      normPoly (R₁ * R₂) (Finset.Icc 1 W) (collapseCoeff J U α c) t := by
  have h1 : normPoly R₁ J α t =
      (R₁ : ℂ)⁻¹ * ∑ l ∈ J, α l * (l : ℂ) ^ ((t : ℂ) * Complex.I) := rfl
  have h2 : normPoly R₂ U c t =
      (R₂ : ℂ)⁻¹ * ∑ u ∈ U, c u * (u : ℂ) ^ ((t : ℂ) * Complex.I) := rfl
  have h3 : normPoly (R₁ * R₂) (Finset.Icc 1 W) (collapseCoeff J U α c) t =
      ((R₁ * R₂ : ℝ) : ℂ)⁻¹ * ∑ w ∈ Finset.Icc 1 W,
        collapseCoeff J U α c w * (w : ℂ) ^ ((t : ℂ) * Complex.I) := rfl
  rw [h1, h2, h3, ← sum_mul_sum_eq_sum_collapseCoeff J U α c _ hW, Complex.ofReal_mul, mul_inv]
  ring

/-- A collapsed coefficient with weights `|α_l| ≤ 1` on a set of positive integers `J` and
`|c_u| ≤ B_c`: `|d_w| ≤ #{l ∈ J : l ∣ w} · B_c`. -/
theorem norm_collapseCoeff_le {J U : Finset ℕ} (hJ : ∀ l ∈ J, 0 < l) {α c : ℕ → ℂ} {Bc : ℝ}
    (hα : ∀ l ∈ J, ‖α l‖ ≤ 1) (hc : ∀ u ∈ U, ‖c u‖ ≤ Bc) (hBc : 0 ≤ Bc) (w : ℕ) :
    ‖collapseCoeff J U α c w‖ ≤ ((J.filter fun l => l ∣ w).card : ℝ) * Bc := by
  have hcard : ((J ×ˢ U).filter (fun x : ℕ × ℕ => x.1 * x.2 = w)).card ≤
      (J.filter fun l => l ∣ w).card := by
    refine Finset.card_le_card_of_injOn (fun x : ℕ × ℕ => x.1) ?_ ?_
    · intro x hx
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
      exact Finset.mem_coe.mpr
        (Finset.mem_filter.mpr ⟨(Finset.mem_product.mp h1).1, Dvd.intro _ h2⟩)
    · intro x hx y hy hxy
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hx)
      obtain ⟨_, h4⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hy)
      have hx1 : x.1 = y.1 := hxy
      have hpos : 0 < x.1 := hJ _ (Finset.mem_product.mp h1).1
      have h5 : x.1 * x.2 = x.1 * y.2 := by
        rw [h2]
        rw [hx1]
        exact h4.symm
      exact Prod.ext hx1 (Nat.eq_of_mul_eq_mul_left hpos h5)
  unfold collapseCoeff
  calc ‖∑ x ∈ (J ×ˢ U).filter (fun x : ℕ × ℕ => x.1 * x.2 = w), α x.1 * c x.2‖
      ≤ ∑ x ∈ (J ×ˢ U).filter (fun x : ℕ × ℕ => x.1 * x.2 = w), ‖α x.1 * c x.2‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _x ∈ (J ×ˢ U).filter (fun x : ℕ × ℕ => x.1 * x.2 = w), Bc :=
        Finset.sum_le_sum fun x hx => by
          have h1 := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
          rw [norm_mul]
          calc ‖α x.1‖ * ‖c x.2‖ ≤ 1 * Bc :=
                mul_le_mul (hα _ h1.1) (hc _ h1.2) (norm_nonneg _) zero_le_one
            _ = Bc := one_mul _
    _ = (((J ×ˢ U).filter (fun x : ℕ × ℕ => x.1 * x.2 = w)).card : ℝ) * Bc := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((J.filter fun l => l ∣ w).card : ℝ) * Bc :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hBc

/-! ### The range of times -/

/-- The times of an interval `[a, b]` of `{lo ≤ |t| ≤ hi}`. -/
theorem abs_mem_of_highRange {lo hi a b : ℝ} (hlo : 0 ≤ lo)
    (hr : (lo ≤ a ∧ b ≤ hi) ∨ (-hi ≤ a ∧ b ≤ -lo)) {t : ℝ} (ht : t ∈ Set.Icc a b) :
    lo ≤ |t| ∧ |t| ≤ hi := by
  rcases hr with h | h
  · have h0 : 0 ≤ t := by linarith [ht.1, h.1]
    rw [abs_of_nonneg h0]
    exact ⟨by linarith [ht.1, h.1], by linarith [ht.2, h.2]⟩
  · have h0 : t ≤ 0 := by linarith [ht.2, h.2]
    rw [abs_of_nonpos h0]
    exact ⟨by linarith [ht.2, h.2], by linarith [ht.1, h.1]⟩

/-- An interval of `{lo ≤ |t| ≤ hi}` has length at most `hi`. -/
theorem sub_le_of_highRange {lo hi a b : ℝ} (hlo : 0 ≤ lo)
    (hr : (lo ≤ a ∧ b ≤ hi) ∨ (-hi ≤ a ∧ b ≤ -lo)) : b - a ≤ hi := by
  rcases hr with h | h
  · linarith [h.1, h.2]
  · linarith [h.1, h.2]

/-! ### Powers of `L` -/

/-- `(L^{-s})² L^n (L^c)² ≤ L^{-A}` when `A + n + 2c ≤ 2s` and `L ≥ 1`. -/
theorem rpow_neg_sq_mul_le {L s c A : ℝ} (hL : 1 ≤ L) (n : ℕ)
    (h : A + (n : ℝ) + 2 * c ≤ 2 * s) :
    (L ^ (-s)) ^ 2 * (L ^ n * (L ^ c) ^ 2) ≤ L ^ (-A) := by
  have hL0 : 0 < L := by linarith
  have e : (L ^ (-s)) ^ 2 * (L ^ n * (L ^ c) ^ 2) = L ^ (-s + -s + ((n : ℝ) + (c + c))) := by
    rw [Real.rpow_add hL0 (-s + -s), Real.rpow_add hL0 (-s) (-s), Real.rpow_add hL0 (n : ℝ),
      Real.rpow_add hL0 c c, Real.rpow_natCast]
    ring
  rw [e]
  exact Real.rpow_le_rpow_of_exponent_le hL (by linarith)

/-! ### The scales -/

/-- **The scales of the products** (`[P-06:0765–0769]`, (cor:length-dominates-time): "`(Y/P) /
(2T_0) = H/(2LP) → ∞`, because `H ≥ exp(2L^{.39} - O(log L))` and `P ≤ exp(L^{.36})`"): for
large `x`, every scale `Y` and every `P` in their ranges satisfy `Y > 0`, `P ≥ 1/2`,
`4 a₂ Y ≤ x²`, `2T_0 ≤ a₁ Y / (4P)` and `2T_0 ≤ x²`, with `T_0 = x L^{C₆ + 1}`. -/
theorem eventually_productScale (a₁ a₂ c₁ c₂ C₆ : ℝ) (ha₁ : 0 < a₁) :
    ∀ᶠ x : ℝ in atTop, 1 < x ∧ 1 ≤ Real.log x ∧
      ∀ Y : ℝ, x * Real.exp (2 * Real.log x ^ (0.39 : ℝ) - c₁) ≤ Y →
        Y ≤ x * Real.exp (c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x)) →
      ∀ P : ℝ, Real.exp (Real.log x ^ (0.27 : ℝ)) / 2 ≤ P →
        P ≤ Real.exp (Real.log x ^ (0.36 : ℝ)) →
        0 < Y ∧ 1 / 2 ≤ P ∧ 4 * a₂ * Y ≤ x ^ (2 : ℝ) ∧
          2 * (x * Real.log x ^ (C₆ + 1)) ≤ a₁ * Y / (4 * P) ∧
          2 * (x * Real.log x ^ (C₆ + 1)) ≤ x ^ (2 : ℝ) := by
  have hae : 0 < a₁ * Real.exp (-c₁) := mul_pos ha₁ (Real.exp_pos _)
  have hc2 : 0 < 1 / (2 * (|c₂| + 1)) := by
    have h := abs_nonneg c₂
    exact one_div_pos.mpr (by linarith)
  have hLLo : ∀ᶠ x : ℝ in atTop, ‖Real.log (Real.log x)‖ ≤
      1 / (2 * (|c₂| + 1)) * ‖Real.log x ^ (0.54 : ℝ)‖ :=
    Real.tendsto_log_atTop.eventually
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.54)).def hc2)
  have h4a : ∀ᶠ x : ℝ in atTop, 4 * a₂ ≤ x ^ (1 / 2 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).eventually_ge_atTop _
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (max 2 (8 / (a₁ * Real.exp (-c₁)))),
    eventually_rpow_mul_exp_neg_le_one (C₆ + 2), hLLo, h4a] with x hx1 hLmax hexp hLLn h4ax
  have hx0 : 0 < x := by linarith
  have hL2 : 2 ≤ Real.log x := (le_max_left _ _).trans hLmax
  have hL8 : 8 / (a₁ * Real.exp (-c₁)) ≤ Real.log x := (le_max_right _ _).trans hLmax
  have hL1 : 1 ≤ Real.log x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hLL0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL1
  refine ⟨hx1, hL1, ?_⟩
  intro Y hY1 hY2 P hP1 hP2
  have h27 : 0 ≤ Real.log x ^ (0.27 : ℝ) := Real.rpow_nonneg hL0.le _
  have h39 : 0 ≤ Real.log x ^ (0.39 : ℝ) := Real.rpow_nonneg hL0.le _
  have h46 : 0 ≤ Real.log x ^ (0.46 : ℝ) := Real.rpow_nonneg hL0.le _
  have h54 : 0 ≤ Real.log x ^ (0.54 : ℝ) := Real.rpow_nonneg hL0.le _
  have hYpos : 0 < Y := lt_of_lt_of_le (mul_pos hx0 (Real.exp_pos _)) hY1
  have hPhalf : 1 / 2 ≤ P := by
    have h1 : (1 : ℝ) ≤ Real.exp (Real.log x ^ (0.27 : ℝ)) := Real.one_le_exp h27
    linarith
  have hP0 : 0 < P := by linarith
  -- `L^{C₆+2} ≤ exp(L^{.27})`
  have hpow : Real.log x ^ (C₆ + 2) ≤ Real.exp (Real.log x ^ (0.27 : ℝ)) := by
    have h1 := mul_le_mul_of_nonneg_right hexp (Real.exp_pos (Real.log x ^ (0.27 : ℝ))).le
    rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one, one_mul] at h1
    exact h1
  have hLC : Real.log x ^ (C₆ + 2) = Real.log x * Real.log x ^ (C₆ + 1) := by
    have e : C₆ + 2 = 1 + (C₆ + 1) := by ring
    rw [e, Real.rpow_add hL0, Real.rpow_one]
  have hLC0 : 0 ≤ Real.log x ^ (C₆ + 1) := Real.rpow_nonneg hL0.le _
  -- `exp(c₂ L^{.46} log L) ≤ x^{1/2}`
  have hYup : Y ≤ x * x ^ (1 / 2 : ℝ) := by
    refine hY2.trans (mul_le_mul_of_nonneg_left ?_ hx0.le)
    rw [Real.rpow_def_of_pos hx0]
    refine Real.exp_le_exp.mpr ?_
    have h5 := hLLn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hLL0, abs_of_nonneg h54] at h5
    have hc0 := abs_nonneg c₂
    have hpos : 0 < 2 * (|c₂| + 1) := by linarith
    have h7 : Real.log (Real.log x) ≤ Real.log x ^ (0.54 : ℝ) / (2 * (|c₂| + 1)) := by
      rw [← one_div_mul_eq_div]
      exact h5
    have h6 : Real.log (Real.log x) * (2 * (|c₂| + 1)) ≤ Real.log x ^ (0.54 : ℝ) :=
      (le_div_iff₀ hpos).mp h7
    have h8 : |c₂| * Real.log (Real.log x) ≤ Real.log x ^ (0.54 : ℝ) / 2 := by linarith
    have hsplit : Real.log x ^ (0.54 : ℝ) * Real.log x ^ (0.46 : ℝ) = Real.log x := by
      have e : (0.54 : ℝ) + 0.46 = 1 := by norm_num
      rw [← Real.rpow_add hL0, e, Real.rpow_one]
    have h9 : c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x) ≤
        |c₂| * Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ) := by
      have h10 : c₂ * (Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x)) ≤
          |c₂| * (Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x)) :=
        mul_le_mul_of_nonneg_right (le_abs_self c₂) (mul_nonneg h46 hLL0)
      linarith
    have h11 : |c₂| * Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ) ≤
        Real.log x ^ (0.54 : ℝ) / 2 * Real.log x ^ (0.46 : ℝ) :=
      mul_le_mul_of_nonneg_right h8 h46
    have h12 : Real.log x ^ (0.54 : ℝ) / 2 * Real.log x ^ (0.46 : ℝ) = Real.log x * (1 / 2) :=
      calc Real.log x ^ (0.54 : ℝ) / 2 * Real.log x ^ (0.46 : ℝ)
          = Real.log x ^ (0.54 : ℝ) * Real.log x ^ (0.46 : ℝ) * (1 / 2) := by ring
        _ = Real.log x * (1 / 2) := by rw [hsplit]
    linarith
  have hsq : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
    have e : (1 / 2 : ℝ) + 1 / 2 = 1 := by norm_num
    rw [← Real.rpow_add hx0, e, Real.rpow_one]
  have hx2 : x ^ (2 : ℝ) = x * x := by rw [Real.rpow_two, pow_two]
  have hxh0 : 0 ≤ x ^ (1 / 2 : ℝ) := Real.rpow_nonneg hx0.le _
  refine ⟨hYpos, hPhalf, ?_, ?_, ?_⟩
  · -- `4 a₂ Y ≤ x²`
    rw [hx2]
    calc 4 * a₂ * Y ≤ x ^ (1 / 2 : ℝ) * (x * x ^ (1 / 2 : ℝ)) :=
          mul_le_mul h4ax hYup hYpos.le hxh0
      _ = x * (x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ)) := by ring
      _ = x * x := by rw [hsq]
  · -- `2T₀ ≤ a₁ Y / (4P)`
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 4 * P)]
    have h1 : 8 ≤ a₁ * Real.exp (-c₁) * Real.log x := by
      have h2 := (div_le_iff₀ hae).mp hL8
      linarith
    have h3 : 8 * Real.log x ^ (C₆ + 1) ≤
        a₁ * Real.exp (-c₁) * Real.exp (Real.log x ^ (0.27 : ℝ)) := by
      calc 8 * Real.log x ^ (C₆ + 1)
          ≤ a₁ * Real.exp (-c₁) * Real.log x * Real.log x ^ (C₆ + 1) :=
            mul_le_mul_of_nonneg_right h1 hLC0
        _ = a₁ * Real.exp (-c₁) * (Real.log x * Real.log x ^ (C₆ + 1)) := by ring
        _ ≤ a₁ * Real.exp (-c₁) * Real.exp (Real.log x ^ (0.27 : ℝ)) := by
            rw [← hLC]
            exact mul_le_mul_of_nonneg_left hpow hae.le
    have h36 : Real.log x ^ (0.36 : ℝ) ≤ Real.log x ^ (0.39 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have h27' : Real.log x ^ (0.27 : ℝ) ≤ Real.log x ^ (0.39 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have hexp2 : Real.exp (Real.log x ^ (0.27 : ℝ)) * Real.exp (Real.log x ^ (0.36 : ℝ)) ≤
        Real.exp (2 * Real.log x ^ (0.39 : ℝ)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    have hY3 : a₁ * (x * (Real.exp (-c₁) * Real.exp (2 * Real.log x ^ (0.39 : ℝ)))) ≤ a₁ * Y := by
      have e : -c₁ + 2 * Real.log x ^ (0.39 : ℝ) = 2 * Real.log x ^ (0.39 : ℝ) - c₁ := by ring
      refine mul_le_mul_of_nonneg_left (le_trans (le_of_eq ?_) hY1) ha₁.le
      rw [← Real.exp_add, e]
    have hE36 : 0 < Real.exp (Real.log x ^ (0.36 : ℝ)) := Real.exp_pos _
    calc 2 * (x * Real.log x ^ (C₆ + 1)) * (4 * P)
        ≤ 2 * (x * Real.log x ^ (C₆ + 1)) * (4 * Real.exp (Real.log x ^ (0.36 : ℝ))) :=
          mul_le_mul_of_nonneg_left (by linarith)
            (mul_nonneg zero_le_two (mul_nonneg hx0.le hLC0))
      _ = x * (8 * Real.log x ^ (C₆ + 1)) * Real.exp (Real.log x ^ (0.36 : ℝ)) := by ring
      _ ≤ x * (a₁ * Real.exp (-c₁) * Real.exp (Real.log x ^ (0.27 : ℝ))) *
            Real.exp (Real.log x ^ (0.36 : ℝ)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hx0.le) hE36.le
      _ = a₁ * (x * (Real.exp (-c₁) *
            (Real.exp (Real.log x ^ (0.27 : ℝ)) * Real.exp (Real.log x ^ (0.36 : ℝ))))) := by
          ring
      _ ≤ a₁ * (x * (Real.exp (-c₁) * Real.exp (2 * Real.log x ^ (0.39 : ℝ)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hexp2 (Real.exp_pos _).le) hx0.le) ha₁.le
      _ ≤ a₁ * Y := hY3
  · -- `2T₀ ≤ x²`
    rw [hx2]
    have h1 : 2 * Real.log x ^ (C₆ + 1) ≤ Real.log x ^ (C₆ + 2) := by
      rw [hLC]
      exact mul_le_mul_of_nonneg_right hL2 hLC0
    have h2 : Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ x := by
      have h3 : Real.log x ^ (0.27 : ℝ) ≤ Real.log x := by
        have h4 := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (0.27 : ℝ) ≤ 1)
        rw [Real.rpow_one] at h4
        exact h4
      calc Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr h3
        _ = x := Real.exp_log hx0
    calc 2 * (x * Real.log x ^ (C₆ + 1)) = x * (2 * Real.log x ^ (C₆ + 1)) := by ring
      _ ≤ x * x := mul_le_mul_of_nonneg_left (by linarith) hx0.le

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
