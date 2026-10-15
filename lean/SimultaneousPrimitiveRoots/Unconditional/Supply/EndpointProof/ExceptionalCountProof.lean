module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ExceptionalCountAlgebra
public import SimultaneousPrimitiveRoots.Unconditional.Classical.DirichletMeanSquare

/-!
# (cor:exceptional-count)

`exceptionalCount : PrimePowerNorm → ExceptionalCount` (`[P-06:0774–0801]`): for every `A_s > 0`
and all large `x`, a set `𝒯` of reals `|t| ≤ x²` with pairwise distances `≥ 1` at which
`|P_s(t)| > L^{-A_s}`, `P_s(t) = P^{-1} ∑_{p ∈ G, P ≤ p ≤ 2P} b_p p^{it}`, has at most
`exp(L^{.9})` elements.

With `G' = G ∩ [P, 2P]`, `Q(t) = ∑_{p ∈ G'} b_p p^{it} = P · P_s(t)`, `ℓ = log(2P) ≥ L^{.27}` and
`j = ⌊2L / ℓ⌋` (so `(2P)^j ≤ x² ≤ (2P)^{j+1}` and `j ≤ 2 L^{.73}`):

* `Q^j` is a Dirichlet polynomial of length `N = ⌊(2P)^j⌋ ≤ x²` with coefficients `powCoeff`, of
  square sum `≤ j! (#G')^j ≤ j! (2P)^j` (`PrimePowerNorm`; "Unique factorization gives squared
  coefficient norm …").
* "The separated-point mean-square bound of Lemma `lem:moment-bounds`"
  (`sum_normSq_dirichletPolynomial_le_nat` on `[-x², x²]`):
  `#𝒯 (P L^{-A_s})^{2j} ≤ ∑_{t ∈ 𝒯} |Q(t)^j|² ≤ (2x² + 1 + 4N(1 + log N))(2 + (log N)²) j! (2P)^j
    ≤ 15L (2 + 4L²) x² · j! (2P)^j`.
* Hence `#𝒯 ≤ 15L(2 + 4L²) · 2P · 4^j · j! · L^{2 A_s j}` (`card_le_of_power_bound`), which is
  `≤ exp(L^{.9})` for large `x` (`exceptional_final_le`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open Filter
open scoped Topology

noncomputable section

/-- **(cor:exceptional-count)** (`[P-06:0774–0801]`), from the factorial coefficient estimate and
the mean value at well-spaced points. -/
theorem exceptionalCount : PrimePowerNorm → ExceptionalCount := by
  intro hPPN As hAs
  -- the thresholds
  have hpowL : ∀ r : ℝ, 0 < r → ∀ c : ℝ, ∀ᶠ x : ℝ in atTop, c ≤ Real.log x ^ r :=
    fun r hr c => ((tendsto_rpow_atTop hr).comp Real.tendsto_log_atTop).eventually_ge_atTop c
  have hLLo : ∀ᶠ x : ℝ in atTop, ‖Real.log (Real.log x)‖ ≤ 1 * ‖Real.log x ^ (0.07 : ℝ)‖ :=
    Real.tendsto_log_atTop.eventually
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.07)).def one_pos)
  have hev : ∀ᶠ x : ℝ in atTop, 90 ≤ Real.log x ∧ 2 ≤ Real.log x ^ (0.27 : ℝ) ∧
      ‖Real.log (Real.log x)‖ ≤ 1 * ‖Real.log x ^ (0.07 : ℝ)‖ ∧
      10 + 4 * As ≤ Real.log x ^ (0.1 : ℝ) ∧ 1 < x := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 90, hpowL 0.27 (by norm_num) 2,
      hLLo, hpowL 0.1 (by norm_num) (10 + 4 * As), eventually_gt_atTop (1 : ℝ)]
      with x h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨x₀, ?_⟩
  intro x hx G hG P hP1 hP2 b hb 𝒯 hT1 hT2 hT3
  obtain ⟨hL90, h27, hLLn, h10, hx1⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hL1 : 1 ≤ Real.log x := by linarith
  have hLL0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL1
  have hp07 : 0 ≤ Real.log x ^ (0.07 : ℝ) := Real.rpow_nonneg hL0.le _
  have hLL : Real.log (Real.log x) ≤ Real.log x ^ (0.07 : ℝ) := by
    have h := hLLn
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hLL0, abs_of_nonneg hp07] at h
    exact h
  -- the scale `P`
  have h27pos : 0 < Real.log x ^ (0.27 : ℝ) := by linarith
  have h2P : Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ 2 * P := by linarith
  have hP0 : 0 < P := by
    have h := Real.exp_pos (Real.log x ^ (0.27 : ℝ))
    linarith
  have h2P0 : 0 < 2 * P := by linarith
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log (2 * P) := ⟨_, rfl⟩
  have hℓexp : Real.exp ℓ = 2 * P := by
    rw [hℓ]
    exact Real.exp_log h2P0
  have hℓge : Real.log x ^ (0.27 : ℝ) ≤ ℓ := by
    have h := Real.log_le_log (Real.exp_pos _) h2P
    rw [Real.log_exp] at h
    rw [hℓ]
    exact h
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le h27pos hℓge
  -- the power `j`: `(2P)^j ≤ x² ≤ (2P)^{j+1}` and `j ≤ 2 L^{.73}`
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j = ⌊2 * Real.log x / ℓ⌋₊ := ⟨_, rfl⟩
  have hjle : (j : ℝ) * ℓ ≤ 2 * Real.log x := by
    have h : (j : ℝ) ≤ 2 * Real.log x / ℓ := by
      rw [hj]
      exact Nat.floor_le (div_nonneg (by linarith) hℓ0.le)
    exact (le_div_iff₀ hℓ0).mp h
  have hjlt : 2 * Real.log x < ((j : ℝ) + 1) * ℓ := by
    have h : 2 * Real.log x / ℓ < (j : ℝ) + 1 := by
      rw [hj]
      exact Nat.lt_floor_add_one _
    exact (div_lt_iff₀ hℓ0).mp h
  have hpow2P : ∀ n : ℕ, (2 * P) ^ n = Real.exp ((n : ℝ) * ℓ) := fun n => by
    rw [Real.exp_nat_mul, hℓexp]
  have hX : x ^ (2 : ℝ) = Real.exp (2 * Real.log x) := by
    rw [Real.rpow_def_of_pos hx0, mul_comm (Real.log x) 2]
  have hpowle : (2 * P) ^ j ≤ x ^ (2 : ℝ) := by
    rw [hpow2P, hX]
    exact Real.exp_le_exp.mpr hjle
  have hpowgt : x ^ (2 : ℝ) ≤ (2 * P) ^ (j + 1) := by
    rw [hpow2P, hX, Nat.cast_add, Nat.cast_one]
    exact Real.exp_le_exp.mpr hjlt.le
  have hj73 : (j : ℝ) ≤ 2 * Real.log x ^ (0.73 : ℝ) := by
    have e : Real.log x ^ (0.73 : ℝ) * Real.log x ^ (0.27 : ℝ) = Real.log x := by
      rw [← Real.rpow_add hL0]
      have e1 : (0.73 : ℝ) + 0.27 = 1 := by norm_num
      rw [e1, Real.rpow_one]
    have h1 : (j : ℝ) * Real.log x ^ (0.27 : ℝ) ≤ (j : ℝ) * ℓ :=
      mul_le_mul_of_nonneg_left hℓge (Nat.cast_nonneg j)
    have h2 : (j : ℝ) * Real.log x ^ (0.27 : ℝ) ≤
        2 * Real.log x ^ (0.73 : ℝ) * Real.log x ^ (0.27 : ℝ) := by
      rw [mul_assoc, e]
      linarith
    exact le_of_mul_le_mul_right h2 h27pos
  -- the primes of `[P, 2P]` and the length `N`
  obtain ⟨G', hG'⟩ : ∃ G' : Finset ℕ, G' = G ∩ natIcc P (2 * P) := ⟨_, rfl⟩
  have hG'mem : ∀ p ∈ G', p.Prime ∧ (p : ℝ) ≤ 2 * P := by
    intro p hp
    rw [hG'] at hp
    obtain ⟨hpG, hpI⟩ := Finset.mem_inter.mp hp
    exact ⟨hG p hpG, ((mem_natIcc h2P0.le).mp hpI).2⟩
  have hcardG' : (G'.card : ℝ) ≤ 2 * P := by
    have h1 : G'.card ≤ (natIcc P (2 * P)).card := by
      rw [hG']
      exact Finset.card_le_card Finset.inter_subset_right
    have h2 : (natIcc P (2 * P)).card ≤ ⌊2 * P⌋₊ := by
      unfold natIcc
      rw [Nat.card_Icc]
      have h3 : 0 < ⌈P⌉₊ := Nat.ceil_pos.mpr hP0
      omega
    calc (G'.card : ℝ) ≤ (⌊2 * P⌋₊ : ℝ) := Nat.cast_le.mpr (h1.trans h2)
      _ ≤ 2 * P := Nat.floor_le h2P0.le
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌊(2 * P) ^ j⌋₊ := ⟨_, rfl⟩
  have hprodN : ∀ f ∈ Fintype.piFinset fun _ : Fin j => G', (∏ i, f i) ∈ Finset.Icc 1 N := by
    intro f hf
    have hfmem : ∀ i, f i ∈ G' := Fintype.mem_piFinset.mp hf
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · exact Nat.succ_le_of_lt (Finset.prod_pos fun i _ => (hG'mem (f i) (hfmem i)).1.pos)
    · rw [hN]
      refine Nat.le_floor ?_
      rw [Nat.cast_prod]
      calc ∏ i, ((f i : ℕ) : ℝ) ≤ ∏ _i : Fin j, (2 * P) :=
            Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _)
              (fun i _ => (hG'mem (f i) (hfmem i)).2)
        _ = (2 * P) ^ j := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hNle : (N : ℝ) ≤ x ^ (2 : ℝ) := by
    have h : (N : ℝ) ≤ (2 * P) ^ j := by
      rw [hN]
      exact Nat.floor_le (pow_nonneg h2P0.le _)
    exact h.trans hpowle
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hlogN : Real.log (N : ℝ) ≤ 2 * Real.log x := by
    by_cases hN0 : N = 0
    · rw [hN0, Nat.cast_zero, Real.log_zero]
      linarith
    · have hNpos : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN0)
      have h1 := Real.log_le_log hNpos hNle
      rw [Real.log_rpow hx0] at h1
      exact h1
  have hXpos : 0 ≤ x ^ (2 : ℝ) := Real.rpow_nonneg hx0.le _
  have hX1 : 1 ≤ x ^ (2 : ℝ) := Real.one_le_rpow hx1.le (by norm_num)
  -- `Q^j` as a Dirichlet polynomial
  have hpoly : ∀ t : ℝ, (∑ p ∈ G', b p * (p : ℂ) ^ ((t : ℂ) * Complex.I)) ^ j =
      SimultaneousPrimitiveRoots.Unconditional.Classical.dirichletPolynomial
        (powCoeff G' b j) N t := by
    intro t
    rw [pow_sum_eq_sum_powCoeff G' b ((t : ℂ) * Complex.I) j N hprodN]
    unfold SimultaneousPrimitiveRoots.Unconditional.Classical.dirichletPolynomial
    exact Finset.sum_congr rfl fun n _ => by rw [mul_comm Complex.I (t : ℂ)]
  -- the coefficients
  have hcoef : ∑ n ∈ Finset.Icc 1 N, ‖powCoeff G' b j n‖ ^ 2 ≤
      (j.factorial : ℝ) * (2 * P) ^ j := by
    have h1 := sum_normSq_powCoeff_le hPPN (fun p hp => (hG'mem p hp).1) b j N hprodN
    have h2 : ∑ p ∈ G', ‖b p‖ ^ 2 ≤ 2 * P :=
      calc ∑ p ∈ G', ‖b p‖ ^ 2 ≤ ∑ _p ∈ G', (1 : ℝ) :=
            Finset.sum_le_sum fun p _ => pow_le_one₀ (norm_nonneg _) (hb p)
        _ = (G'.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ 2 * P := hcardG'
    exact h1.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Finset.sum_nonneg fun p _ => sq_nonneg _) h2 j) (Nat.cast_nonneg _))
  -- the mean value at the points of `𝒯`
  have hsub : ∀ t ∈ 𝒯, t ∈ Set.Icc (-(x ^ (2 : ℝ))) (x ^ (2 : ℝ)) := fun t ht =>
    ⟨(abs_le.mp (hT1 t ht)).1, (abs_le.mp (hT1 t ht)).2⟩
  have hmv :=
    SimultaneousPrimitiveRoots.Unconditional.Classical.sum_normSq_dirichletPolynomial_le_nat
      (powCoeff G' b j) N (a := -(x ^ (2 : ℝ))) (b := x ^ (2 : ℝ)) (by linarith) 𝒯 hsub hT2
  -- the lower bound at each point
  have hΛ : 0 < Real.log x ^ As := Real.rpow_pos_of_pos hL0 _
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = P * (Real.log x ^ As)⁻¹ := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by
    rw [hθ]
    exact mul_pos hP0 (inv_pos.mpr hΛ)
  have hlower : ∀ t ∈ 𝒯, (θ ^ j) ^ 2 ≤
      ‖SimultaneousPrimitiveRoots.Unconditional.Classical.dirichletPolynomial
        (powCoeff G' b j) N t‖ ^ 2 := by
    intro t ht
    have h1 := hT3 t ht
    rw [← hG'] at h1
    have hnp : normPoly P G' b t =
        (P : ℂ)⁻¹ * ∑ p ∈ G', b p * (p : ℂ) ^ ((t : ℂ) * Complex.I) := rfl
    rw [hnp, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hP0.le,
      Real.rpow_neg hL0.le] at h1
    have h2 : θ < ‖∑ p ∈ G', b p * (p : ℂ) ^ ((t : ℂ) * Complex.I)‖ := by
      have h3 := mul_lt_mul_of_pos_left h1 hP0
      rw [← mul_assoc, mul_inv_cancel₀ hP0.ne', one_mul] at h3
      rw [hθ]
      exact h3
    rw [← hpoly t, norm_pow]
    exact pow_le_pow_left₀ (pow_nonneg hθ0.le _) (pow_le_pow_left₀ hθ0.le h2.le j) 2
  -- the length and the logarithmic factor
  have hlen : (x ^ (2 : ℝ) - -(x ^ (2 : ℝ))) + 1 + 4 * (N : ℝ) * (1 + Real.log (N : ℝ)) ≤
      15 * Real.log x * x ^ (2 : ℝ) := by
    have h1 : 4 * (N : ℝ) * (1 + Real.log (N : ℝ)) ≤
        4 * x ^ (2 : ℝ) * (1 + 2 * Real.log x) :=
      mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have h2 : x ^ (2 : ℝ) ≤ x ^ (2 : ℝ) * Real.log x := le_mul_of_one_le_right hXpos hL1
    have h3 : 4 * x ^ (2 : ℝ) * (1 + 2 * Real.log x) =
        4 * x ^ (2 : ℝ) + 8 * (x ^ (2 : ℝ) * Real.log x) := by ring
    have h4 : 15 * Real.log x * x ^ (2 : ℝ) = 15 * (x ^ (2 : ℝ) * Real.log x) := by ring
    rw [h4]
    linarith
  have hlog2 : 2 + Real.log (N : ℝ) ^ 2 ≤ 2 + 4 * Real.log x ^ 2 := by
    have h := pow_le_pow_left₀ hlogN0 hlogN 2
    have e : (2 * Real.log x) ^ 2 = 4 * Real.log x ^ 2 := by ring
    rw [e] at h
    linarith
  have hC₁0 : 0 ≤ 15 * Real.log x * (2 + 4 * Real.log x ^ 2) :=
    mul_nonneg (mul_nonneg (by norm_num) hL0.le)
      (add_nonneg zero_le_two (mul_nonneg (by norm_num) (sq_nonneg _)))
  have hF0 : (0 : ℝ) ≤ (j.factorial : ℝ) := Nat.cast_nonneg _
  have hmain : (𝒯.card : ℝ) * (θ ^ j) ^ 2 ≤
      15 * Real.log x * (2 + 4 * Real.log x ^ 2) * x ^ (2 : ℝ) *
        ((j.factorial : ℝ) * (2 * P) ^ j) :=
    calc (𝒯.card : ℝ) * (θ ^ j) ^ 2 = ∑ _t ∈ 𝒯, (θ ^ j) ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ t ∈ 𝒯,
            ‖SimultaneousPrimitiveRoots.Unconditional.Classical.dirichletPolynomial
              (powCoeff G' b j) N t‖ ^ 2 := Finset.sum_le_sum hlower
      _ ≤ ((x ^ (2 : ℝ) - -(x ^ (2 : ℝ))) + 1 + 4 * (N : ℝ) * (1 + Real.log (N : ℝ))) *
            (2 + Real.log (N : ℝ) ^ 2) * ∑ n ∈ Finset.Icc 1 N, ‖powCoeff G' b j n‖ ^ 2 := hmv
      _ ≤ 15 * Real.log x * x ^ (2 : ℝ) * (2 + 4 * Real.log x ^ 2) *
            ((j.factorial : ℝ) * (2 * P) ^ j) :=
          mul_le_mul
            (mul_le_mul hlen hlog2 (add_nonneg zero_le_two (sq_nonneg _))
              (mul_nonneg (mul_nonneg (by norm_num) hL0.le) hXpos))
            hcoef (Finset.sum_nonneg fun n _ => sq_nonneg _)
            (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL0.le) hXpos)
              (add_nonneg zero_le_two (mul_nonneg (by norm_num) (sq_nonneg _))))
      _ = 15 * Real.log x * (2 + 4 * Real.log x ^ 2) * x ^ (2 : ℝ) *
            ((j.factorial : ℝ) * (2 * P) ^ j) := by ring
  rw [hθ] at hmain
  exact (card_le_of_power_bound hP0 hΛ hC₁0 hF0 hmain hpowgt).trans
    (exceptional_final_le hL90 hAs hP0 hP2 hj73 h27 hLL h10)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
