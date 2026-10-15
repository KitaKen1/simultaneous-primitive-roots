module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.Statements
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The exceptional times: powers of the small-prime polynomial

The algebra and the final numerical inequality of (cor:exceptional-count) (`[P-06:0774–0801]`); the
statement is proved in `EndpointProof/ExceptionalCountProof.lean`.

* `natCast_prod_cpow`, `pow_sum_cpow_eq`: `(∑_{p ∈ G} b_p p^z)^j = ∑_{(p_1, …, p_j) ∈ G^j}
  (∏ b_{p_i}) (p_1 ⋯ p_j)^z`.
* `powCoeff G b j n`: the coefficient of `n` in `(∑_{p ∈ G} b_p p^{it})^j` (the inner sum of
  `PrimePowerNorm`); `pow_sum_eq_sum_powCoeff`: the power is the Dirichlet polynomial
  `∑_{1 ≤ n ≤ N} powCoeff(n) n^z` once all products of `j` elements of `G` are `≤ N`;
  `sum_normSq_powCoeff_le`: "Unique factorization gives squared coefficient norm for `P_s^{j_0}`
  at most `j_0! (∑ |b_s(p_s)|²)^{j_0}`" (from `PrimePowerNorm`).
* `card_le_of_power_bound`: from `#𝒯 (P Λ^{-1})^{2j} ≤ C₁ X · j! (2P)^j` and `X ≤ (2P)^{j+1}` to
  `#𝒯 ≤ C₁ · 2P · 4^j · j! · Λ^{2j}` ("Since `Z P^{-j_0} ≤ 2P 2^{j_0}`").
* `exceptional_final_le`: `15L(2 + 4L²) · 2P · 4^j · j! · L^{2 A_s j} ≤ exp(L^{.9})` for
  `P ≤ exp(L^{.36})`, `j ≤ 2 L^{.73}` and large `L` ("`j_0 = O(L^{.73})`, taking logarithms").
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

noncomputable section

/-! ### Powers of a prime polynomial -/

/-- `(∏ n_i)^z = ∏ n_i^z` for natural numbers `n_i`. -/
theorem natCast_prod_cpow {ι : Type*} (s : Finset ι) (f : ι → ℕ) (z : ℂ) :
    ((∏ i ∈ s, f i : ℕ) : ℂ) ^ z = ∏ i ∈ s, (f i : ℂ) ^ z := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.prod_empty, Nat.cast_one, Complex.one_cpow]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow, ih]

/-- `(∑_{p ∈ G} b_p p^z)^j = ∑_{(p_1, …, p_j) ∈ G^j} (∏_i b_{p_i}) (p_1 ⋯ p_j)^z`. -/
theorem pow_sum_cpow_eq (G : Finset ℕ) (b : ℕ → ℂ) (z : ℂ) (j : ℕ) :
    (∑ p ∈ G, b p * (p : ℂ) ^ z) ^ j =
      ∑ f ∈ Fintype.piFinset fun _ : Fin j => G,
        (∏ i, b (f i)) * ((∏ i, f i : ℕ) : ℂ) ^ z := by
  rw [Finset.sum_pow']
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.prod_mul_distrib, natCast_prod_cpow]

/-- The coefficient of `n` in `(∑_{p ∈ G} b_p p^{it})^j`: the sum of `∏_i b_{p_i}` over the
ordered `j`-tuples of elements of `G` with product `n` (`[P-06:0784–0789]`). -/
def powCoeff (G : Finset ℕ) (b : ℕ → ℂ) (j n : ℕ) : ℂ :=
  ∑ f ∈ (Fintype.piFinset fun _ : Fin j => G).filter (fun f => ∏ i, f i = n), ∏ i, b (f i)

/-- The `j`-th power of `∑_{p ∈ G} b_p p^z` is the Dirichlet polynomial with coefficients
`powCoeff G b j`, on `1 ≤ n ≤ N` when all products of `j` elements of `G` lie there. -/
theorem pow_sum_eq_sum_powCoeff (G : Finset ℕ) (b : ℕ → ℂ) (z : ℂ) (j N : ℕ)
    (hN : ∀ f ∈ Fintype.piFinset fun _ : Fin j => G, (∏ i, f i) ∈ Finset.Icc 1 N) :
    (∑ p ∈ G, b p * (p : ℂ) ^ z) ^ j =
      ∑ n ∈ Finset.Icc 1 N, powCoeff G b j n * (n : ℂ) ^ z := by
  have h1 : ∑ f ∈ Fintype.piFinset fun _ : Fin j => G,
        (∏ i, b (f i)) * ((∏ i, f i : ℕ) : ℂ) ^ z =
      ∑ n ∈ Finset.Icc 1 N,
        ∑ f ∈ (Fintype.piFinset fun _ : Fin j => G).filter (fun f => ∏ i, f i = n),
          (∏ i, b (f i)) * ((∏ i, f i : ℕ) : ℂ) ^ z :=
    (Finset.sum_fiberwise_of_maps_to hN _).symm
  rw [pow_sum_cpow_eq, h1]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold powCoeff
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun f hf => ?_
  rw [(Finset.mem_filter.mp hf).2]

/-- **The factorial coefficient estimate** for the coefficients of the power
(`[P-06:0781–0789]`), from `PrimePowerNorm`. -/
theorem sum_normSq_powCoeff_le (hPPN : PrimePowerNorm) {G : Finset ℕ} (hG : ∀ p ∈ G, p.Prime)
    (b : ℕ → ℂ) (j N : ℕ)
    (hN : ∀ f ∈ Fintype.piFinset fun _ : Fin j => G, (∏ i, f i) ∈ Finset.Icc 1 N) :
    ∑ n ∈ Finset.Icc 1 N, ‖powCoeff G b j n‖ ^ 2 ≤
      (j.factorial : ℝ) * (∑ p ∈ G, ‖b p‖ ^ 2) ^ j := by
  have h : ∑ n ∈ (Fintype.piFinset fun _ : Fin j => G).image (fun f => ∏ i, f i),
      ‖powCoeff G b j n‖ ^ 2 ≤ (j.factorial : ℝ) * (∑ p ∈ G, ‖b p‖ ^ 2) ^ j := hPPN G hG b j
  refine le_trans (le_of_eq ?_) h
  symm
  refine Finset.sum_subset ?_ ?_
  · intro n hn
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hn
    exact hN f hf
  · intro n _ hn
    have hempty : (Fintype.piFinset fun _ : Fin j => G).filter (fun f => ∏ i, f i = n) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun f hf hprod => hn ?_
      exact Finset.mem_image.mpr ⟨f, hf, hprod⟩
    unfold powCoeff
    rw [hempty, Finset.sum_empty, norm_zero]
    exact zero_pow two_ne_zero

/-! ### From the mean value to the count -/

/-- "Since `Z P^{-j_0} ≤ 2P 2^{j_0}`" (`[P-06:0799]`): from
`c (P Λ^{-1})^{2j} ≤ C₁ X · F (2P)^j` and `X ≤ (2P)^{j+1}` to `c ≤ C₁ · 2P · 2^{2j} · F · Λ^{2j}`. -/
theorem card_le_of_power_bound {c C₁ P Λ X F : ℝ} {j : ℕ} (hP : 0 < P) (hΛ : 0 < Λ)
    (hC₁ : 0 ≤ C₁) (hF : 0 ≤ F)
    (h : c * ((P * Λ⁻¹) ^ j) ^ 2 ≤ C₁ * X * (F * (2 * P) ^ j)) (hX : X ≤ (2 * P) ^ (j + 1)) :
    c ≤ C₁ * (2 * P) * 2 ^ (2 * j) * F * Λ ^ (2 * j) := by
  have hD : 0 < ((P * Λ⁻¹) ^ j) ^ 2 := pow_pos (pow_pos (mul_pos hP (inv_pos.mpr hΛ)) _) _
  have h2P : 0 ≤ 2 * P := by linarith
  have hkey : Λ ^ (2 * j) * ((P * Λ⁻¹) ^ j) ^ 2 = P ^ (2 * j) := by
    rw [← pow_mul, mul_comm j 2, ← mul_pow]
    congr 1
    rw [mul_comm P, ← mul_assoc, mul_inv_cancel₀ hΛ.ne', one_mul]
  have e1 : (2 * P) ^ (j + 1) * (2 * P) ^ j = 2 * P * (2 ^ (2 * j) * P ^ (2 * j)) := by
    rw [pow_succ, ← mul_pow 2 P (2 * j), two_mul j, pow_add]
    ring
  have hchain : c * ((P * Λ⁻¹) ^ j) ^ 2 ≤
      C₁ * (2 * P) * 2 ^ (2 * j) * F * Λ ^ (2 * j) * ((P * Λ⁻¹) ^ j) ^ 2 :=
    calc c * ((P * Λ⁻¹) ^ j) ^ 2 ≤ C₁ * X * (F * (2 * P) ^ j) := h
      _ ≤ C₁ * (2 * P) ^ (j + 1) * (F * (2 * P) ^ j) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hX hC₁)
            (mul_nonneg hF (pow_nonneg h2P _))
      _ = C₁ * F * ((2 * P) ^ (j + 1) * (2 * P) ^ j) := by ring
      _ = C₁ * F * (2 * P * (2 ^ (2 * j) * P ^ (2 * j))) := by rw [e1]
      _ = C₁ * (2 * P) * 2 ^ (2 * j) * F * (Λ ^ (2 * j) * ((P * Λ⁻¹) ^ j) ^ 2) := by
          rw [hkey]
          ring
      _ = C₁ * (2 * P) * 2 ^ (2 * j) * F * Λ ^ (2 * j) * ((P * Λ⁻¹) ^ j) ^ 2 := by ring
  exact le_of_mul_le_mul_right hchain hD

/-! ### The final inequality -/

/-- "`j_0 = O(L^{.73})`, taking logarithms proves (cor:exceptional-count)" (`[P-06:0800–0801]`):
`15L(2 + 4L²) · 2P · 2^{2j} · j! · L^{2 A_s j} ≤ exp(L^{.9})` for `P ≤ exp(L^{.36})`,
`j ≤ 2 L^{.73}` and `L` large (`L ≥ 90`, `L^{.27} ≥ 2`, `log L ≤ L^{.07}`,
`L^{.1} ≥ 10 + 4 A_s`): the logarithm of the left side is at most
`4 log L + 1 + L^{.36} + (2 + 2 A_s) j log L ≤ (10 + 4 A_s) L^{.8}`. -/
theorem exceptional_final_le {L As P : ℝ} {j : ℕ} (hL90 : 90 ≤ L) (hAs : 0 < As) (hP0 : 0 < P)
    (hP : P ≤ Real.exp (L ^ (0.36 : ℝ))) (hj : (j : ℝ) ≤ 2 * L ^ (0.73 : ℝ))
    (h27 : 2 ≤ L ^ (0.27 : ℝ)) (hll : Real.log L ≤ L ^ (0.07 : ℝ))
    (h10 : 10 + 4 * As ≤ L ^ (0.1 : ℝ)) :
    15 * L * (2 + 4 * L ^ 2) * (2 * P) * 2 ^ (2 * j) * (j.factorial : ℝ) * (L ^ As) ^ (2 * j) ≤
      Real.exp (L ^ (0.9 : ℝ)) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hexp : Real.exp (Real.log L) = L := Real.exp_log hL0
  have hll0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  -- `15L(2 + 4L²) ≤ L⁴`
  have f1 : 15 * L * (2 + 4 * L ^ 2) ≤
      Real.exp (Real.log L + Real.log L + Real.log L + Real.log L) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, hexp]
    have hLL : 1 ≤ L * L :=
      calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
        _ ≤ L * L := mul_le_mul hL1 hL1 zero_le_one hL0.le
    have h1 : 2 + 4 * L ^ 2 ≤ 6 * (L * L) := by
      rw [pow_two]
      linarith
    have h2 : 15 * L * (2 + 4 * L ^ 2) ≤ 15 * L * (6 * (L * L)) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have h3 : 90 * (L * L * L) ≤ L * (L * L * L) :=
      mul_le_mul_of_nonneg_right hL90 (mul_nonneg (mul_nonneg hL0.le hL0.le) hL0.le)
    calc 15 * L * (2 + 4 * L ^ 2) ≤ 15 * L * (6 * (L * L)) := h2
      _ = 90 * (L * L * L) := by ring
      _ ≤ L * (L * L * L) := h3
      _ = L * L * L * L := by ring
  -- `2P ≤ e · exp(L^{.36})`
  have f2 : 2 * P ≤ Real.exp (1 + L ^ (0.36 : ℝ)) := by
    rw [Real.exp_add]
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      have h := Real.add_one_le_exp (1 : ℝ)
      linarith
    exact mul_le_mul he hP hP0.le (Real.exp_pos 1).le
  -- `j ≤ L`
  have hjL : (j : ℝ) ≤ L := by
    have e : L ^ (0.27 : ℝ) * L ^ (0.73 : ℝ) = L := by
      rw [← Real.rpow_add hL0]
      have e1 : (0.27 : ℝ) + 0.73 = 1 := by norm_num
      rw [e1, Real.rpow_one]
    have h : 2 * L ^ (0.73 : ℝ) ≤ L ^ (0.27 : ℝ) * L ^ (0.73 : ℝ) :=
      mul_le_mul_of_nonneg_right h27 (Real.rpow_nonneg hL0.le _)
    rw [e] at h
    linarith
  have hpowj : Real.exp ((j : ℝ) * Real.log L) = L ^ j := by
    rw [Real.exp_nat_mul, hexp]
  -- `4^j ≤ L^j` and `j! ≤ j^j ≤ L^j`
  have f3 : (2 : ℝ) ^ (2 * j) ≤ Real.exp ((j : ℝ) * Real.log L) := by
    rw [hpowj, pow_mul]
    have h4 : (2 : ℝ) ^ 2 ≤ L := by
      have e : (2 : ℝ) ^ 2 = 4 := by norm_num
      rw [e]
      linarith
    exact pow_le_pow_left₀ (by norm_num) h4 j
  have f4 : (j.factorial : ℝ) ≤ Real.exp ((j : ℝ) * Real.log L) := by
    rw [hpowj]
    have h1 : (j.factorial : ℝ) ≤ ((j ^ j : ℕ) : ℝ) := Nat.cast_le.mpr (Nat.factorial_le_pow j)
    rw [Nat.cast_pow] at h1
    exact h1.trans (pow_le_pow_left₀ (Nat.cast_nonneg j) hjL j)
  -- `L^{2 A_s j}`
  have f5 : (L ^ As) ^ (2 * j) = Real.exp (2 * ((j : ℝ) * (Real.log L * As))) := by
    rw [Real.rpow_def_of_pos hL0, ← Real.exp_nat_mul]
    congr 1
    rw [Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hprod : 15 * L * (2 + 4 * L ^ 2) * (2 * P) * 2 ^ (2 * j) * (j.factorial : ℝ) *
        (L ^ As) ^ (2 * j) ≤
      Real.exp (Real.log L + Real.log L + Real.log L + Real.log L) *
        Real.exp (1 + L ^ (0.36 : ℝ)) * Real.exp ((j : ℝ) * Real.log L) *
          Real.exp ((j : ℝ) * Real.log L) * Real.exp (2 * ((j : ℝ) * (Real.log L * As))) := by
    rw [f5]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul
        (mul_le_mul (mul_le_mul f1 f2 (by linarith) (Real.exp_pos _).le) f3
          (pow_nonneg zero_le_two _) (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le)
        f4 (Nat.cast_nonneg _)
        (mul_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)) (Real.exp_pos _)).le)
      (Real.exp_pos _).le
  refine hprod.trans ?_
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  -- the exponent is at most `(10 + 4 A_s) L^{.8} ≤ L^{.9}`
  obtain ⟨V, hV⟩ : ∃ V : ℝ, V = L ^ (0.8 : ℝ) := ⟨_, rfl⟩
  have hV0 : 0 ≤ V := by
    rw [hV]
    exact Real.rpow_nonneg hL0.le _
  have v1 : Real.log L ≤ V := by
    rw [hV]
    exact hll.trans (Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num))
  have v2 : 1 ≤ V := by
    rw [hV]
    exact Real.one_le_rpow hL1 (by norm_num)
  have v3 : L ^ (0.36 : ℝ) ≤ V := by
    rw [hV]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have v4 : (j : ℝ) * Real.log L ≤ 2 * V := by
    have h1 : (j : ℝ) * Real.log L ≤ 2 * L ^ (0.73 : ℝ) * L ^ (0.07 : ℝ) :=
      mul_le_mul hj hll hll0 (mul_nonneg zero_le_two (Real.rpow_nonneg hL0.le _))
    have e : L ^ (0.73 : ℝ) * L ^ (0.07 : ℝ) = L ^ (0.8 : ℝ) := by
      rw [← Real.rpow_add hL0]
      congr 1
      norm_num
    rw [mul_assoc, e, ← hV] at h1
    exact h1
  have v5 : (10 + 4 * As) * V ≤ L ^ (0.9 : ℝ) := by
    have h1 : (10 + 4 * As) * V ≤ L ^ (0.1 : ℝ) * V := mul_le_mul_of_nonneg_right h10 hV0
    have e : L ^ (0.1 : ℝ) * L ^ (0.8 : ℝ) = L ^ (0.9 : ℝ) := by
      rw [← Real.rpow_add hL0]
      congr 1
      norm_num
    rw [← e, ← hV]
    exact h1
  have v6 : As * ((j : ℝ) * Real.log L) ≤ As * (2 * V) := mul_le_mul_of_nonneg_left v4 hAs.le
  linarith

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
