import OAI.NumberTheory.PrimeGaps.Main

/-!
# The Siegel–Walfisz theorem for primes in arithmetic progressions (prime-counting form)

The vendored library `OAI` proves the Siegel–Walfisz theorem in character form
(`OAI.LargePrimeGaps.siegelWalfisz`): for a primitive Dirichlet character `χ` modulo
`d ≤ (log x)^B`, the twisted von Mangoldt sum `∑_{n ≤ x} χ(n) Λ(n)` is
`[χ = 1] x + O(x (log x)^{-A})`.
This file deduces the prime-counting form used in [S, Theorem `thm:sw`] and
[P, Lemma `lem:prime-estimates`]: for fixed `A, C > 0`, uniformly for `gcd(a, r) = 1` and
`1 ≤ r ≤ (log y)^C`,

  `#{p ≤ y : p prime, p ≡ a (mod r)} = Li(y) / φ(r) + O_{A,C}(y / (log y)^A)`.

## Main definitions and results

* `Li`: the logarithmic integral `Li y = ∫₂^y dt / log t`.
* `siegelWalfisz_vonMangoldt`: Siegel–Walfisz for `ψ(x; q, c) = ∑_{n ≤ x, n ≡ c (q)} Λ(n)`.
  Every character modulo `q` is replaced by its primitive inducing character (conductor `≤ q`),
  at the cost `O(log x · log q)`, and the characters are then summed by orthogonality (both steps
  are already in `OAI.NumberTheory.PrimeGaps.CharacterErrors`).
* `siegelWalfisz_theta`: the same for `θ(x; q, c) = ∑_{p ≤ x, p ≡ c (q)} log p`; the prime powers
  cost `O(√x log x)`.
* `primeCount_sub_Li_eq`: partial summation,
  `π(y; q, c) - Li(y)/φ(q) = (θ(y; q, c) - y/φ(q)) / log y + 2 / (φ(q) log 2)
    + ∫₂^y (θ(t; q, c) - t/φ(q)) / (t log² t) dt`.
* `siegelWalfisz_primeCounting`: the prime-counting form. The integral is split at `√y`: on
  `[2, √y]` the trivial (Chebyshev) bound is used, on `[√y, y]` the bound for `θ(t; q, c)` with
  the exponent `2C` (because `log y ≤ (log t)²` there).
* `siegelWalfisz_primeCounting_of_two_le`: the same statement for all `y ≥ 2`, without a threshold
  (the range `2 ≤ y < y₀` is covered by trivial bounds, at the cost of a larger constant).

The constants are ineffective (they come from Siegel's theorem); in `siegelWalfisz_primeCounting`
the threshold `y₀` depends on `A` and `C`.

This file is not a `module`: it imports the vendored library `OAI`.
-/

namespace SimultaneousPrimitiveRoots.Classical

open OAI.LargePrimeGaps

/-- The logarithmic integral `Li y = ∫₂^y dt / log t`. -/
noncomputable def Li (y : ℝ) : ℝ := ∫ t in (2 : ℝ)..y, 1 / Real.log t

/-! ### From primitive characters to residue classes -/

/-- **Siegel–Walfisz for `ψ(x; q, c)`.** For fixed `A, B > 0`, uniformly for `q ≤ (log x)^B` and
`gcd(c, q) = 1`, `ψ(x; q, c) = x / φ(q) + O(x (log x)^{-A})`. -/
theorem siegelWalfisz_vonMangoldt (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ Real.log x ^ B → ∀ c : ℕ, c < q → Nat.Coprime c q →
        |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c - x / (q.totient : ℝ)| ≤
          M * x * Real.log x ^ (-A) := by
  obtain ⟨M, hM, x₀, hx₀, hSW⟩ := siegelWalfisz A B hA hB
  have hev : ∀ᶠ x : ℝ in Filter.atTop, Real.exp 1 ≤ x ∧ Real.log x ^ (A + B + 1) ≤ x := by
    filter_upwards [Filter.eventually_ge_atTop (Real.exp 1),
      eventually_log_rpow_le_rpow (A + B + 1) (by norm_num : (0 : ℝ) < 1)] with x h1 h2
    exact ⟨h1, by simpa only [Real.rpow_one] using h2⟩
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp hev
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨M + 1 / Real.log 2, add_pos hM (one_div_pos.mpr hlog2pos), max x₀ x₁,
    lt_of_lt_of_le hx₀ (le_max_left _ _), ?_⟩
  intro x hx q hq hqB c hc hcop
  obtain ⟨hxe, hpow⟩ := hx₁ x ((le_max_right _ _).trans hx)
  have hxx₀ : x₀ ≤ x := (le_max_left _ _).trans hx
  have hx2 : 2 ≤ x := by
    have := Real.add_one_le_exp 1
    linarith
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hxe
  have hL0 : 0 < Real.log x := by linarith
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hphi : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have : NeZero q := ⟨hq.ne'⟩
  -- every primitive inducing character has conductor at most `q`
  have hprim : ∀ χ : DirichletCharacter ℂ q,
      ‖primeCharacterError x χ.primitiveCharacter‖ ≤ M * x * Real.log x ^ (-A) := by
    intro χ
    have hdvd : χ.conductor ∣ q := χ.conductor_dvd_level
    have hpos : 0 < χ.conductor := Nat.pos_of_dvd_of_pos hdvd hq
    have hle : (χ.conductor : ℝ) ≤ q := by exact_mod_cast Nat.le_of_dvd hq hdvd
    exact hSW x hxx₀ χ.conductor hpos (hle.trans hqB) χ.primitiveCharacter
      χ.primitiveCharacter_isPrimitive
  -- the cost of passing from `χ` to its primitive inducing character
  have hfloor1 : 1 ≤ ⌊x⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hfloorle : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hnatlog : (Nat.log 2 ⌊x⌋₊ : ℝ) ≤ Real.log x / Real.log 2 := by
    have h1 := Real.natLog_le_logb ⌊x⌋₊ 2
    rw [← Real.log_div_log, Nat.cast_ofNat] at h1
    exact h1.trans (div_le_div_of_nonneg_right
      (Real.log_le_log (by exact_mod_cast hfloor1) hfloorle) hlog2pos.le)
  have hlogq0 : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hlogq : Real.log (q : ℝ) ≤ Real.log x ^ B := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < q by linarith)
    linarith
  have hcorr : (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log (q : ℝ) ≤
      1 / Real.log 2 * x * Real.log x ^ (-A) := by
    have hsplit : Real.log x ^ (A + B + 1) * Real.log x ^ (-A) =
        Real.log x * Real.log x ^ B := by
      rw [← Real.rpow_add hL0, show A + B + 1 + -A = 1 + B by ring, Real.rpow_add hL0,
        Real.rpow_one]
    have hnn : 0 ≤ Real.log x ^ (-A) := (Real.rpow_pos_of_pos hL0 _).le
    calc (Nat.log 2 ⌊x⌋₊ : ℝ) * Real.log (q : ℝ)
        ≤ Real.log x / Real.log 2 * Real.log x ^ B :=
          mul_le_mul hnatlog hlogq hlogq0 (div_nonneg hL0.le hlog2pos.le)
      _ = 1 / Real.log 2 * (Real.log x ^ (A + B + 1) * Real.log x ^ (-A)) := by
          rw [hsplit]
          ring
      _ ≤ 1 / Real.log 2 * (x * Real.log x ^ (-A)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hnn)
            (div_nonneg zero_le_one hlog2pos.le)
      _ = 1 / Real.log 2 * x * Real.log x ^ (-A) := by ring
  refine (endpointClassError_le_character_sum x hq hc hcop).trans ?_
  refine (characterMeanError_le_primitive_average x hq).trans ?_
  rw [show (M + 1 / Real.log 2) * x * Real.log x ^ (-A) =
    M * x * Real.log x ^ (-A) + 1 / Real.log 2 * x * Real.log x ^ (-A) by ring]
  refine add_le_add ?_ hcorr
  rw [div_le_iff₀ hphi]
  refine (Finset.sum_le_sum fun χ _ => hprim χ).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q, nsmul_eq_mul]
  ring

/-! ### Removing the prime powers -/

/-- **Siegel–Walfisz for `θ(x; q, c)`.** For fixed `A, B > 0`, uniformly for `q ≤ (log x)^B` and
`gcd(c, q) = 1`, `θ(x; q, c) = ∑_{p ≤ x, p ≡ c (q)} log p = x / φ(q) + O(x (log x)^{-A})`. -/
theorem siegelWalfisz_theta (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∃ M : ℝ, 0 < M ∧ ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ Real.log x ^ B → ∀ c : ℕ, c < q → Nat.Coprime c q →
        |residuePrefix theta ⌊x⌋₊ q c - x / (q.totient : ℝ)| ≤ M * x * Real.log x ^ (-A) := by
  obtain ⟨M, hM, x₀, hx₀, hψ⟩ := siegelWalfisz_vonMangoldt A B hA hB
  have hev : ∀ᶠ x : ℝ in Filter.atTop,
      Real.exp 2 ≤ x ∧ Real.log x ^ (A + 2) ≤ x ^ (1 / 2 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop (Real.exp 2),
      eventually_log_rpow_le_rpow (A + 2) (by norm_num : (0 : ℝ) < 1 / 2)] with x h1 h2
    exact ⟨h1, h2⟩
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp hev
  refine ⟨M + 1, by linarith, max x₀ x₁, lt_of_lt_of_le hx₀ (le_max_left _ _), ?_⟩
  intro x hx q hq hqB c hc hcop
  obtain ⟨hxe, hpow⟩ := hx₁ x ((le_max_right _ _).trans hx)
  have hxx₀ : x₀ ≤ x := (le_max_left _ _).trans hx
  have hx3 : 3 ≤ x := by
    have := Real.add_one_le_exp 2
    linarith
  have hx0 : 0 < x := by linarith
  have hL2 : 2 ≤ Real.log x := by
    rw [← Real.log_exp 2]
    exact Real.log_le_log (Real.exp_pos 2) hxe
  have hL0 : 0 < Real.log x := by linarith
  have hU : 1 ≤ ⌊x⌋₊ := Nat.floor_pos.mpr (by linarith)
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hfl1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hU
  -- the prime powers
  have hpp : |residuePrefix theta ⌊x⌋₊ q c -
      residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c| ≤
        2 * Real.sqrt (⌊x⌋₊ : ℝ) * Real.log (⌊x⌋₊ : ℝ) := by
    rw [abs_sub_comm]
    exact residueSlice_primepower_error hU 0 q c
  have h1 : 2 * Real.sqrt (⌊x⌋₊ : ℝ) * Real.log (⌊x⌋₊ : ℝ) ≤
      2 * Real.sqrt x * Real.log x :=
    mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hfl) (by norm_num))
      (Real.log_le_log (by linarith) hfl) (Real.log_nonneg hfl1)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg x))
  have h2 : 2 * Real.sqrt x * Real.log x ≤ x * Real.log x ^ (-A) := by
    have hLA : 0 < Real.log x ^ A := Real.rpow_pos_of_pos hL0 A
    have hA2 : Real.log x ^ (A + 2) = Real.log x ^ A * (Real.log x * Real.log x) := by
      rw [Real.rpow_add hL0, Real.rpow_two]
      ring
    have h3 : 2 * Real.log x ≤ Real.sqrt x * Real.log x ^ (-A) := by
      rw [Real.rpow_neg hL0.le, ← div_eq_mul_inv, le_div_iff₀ hLA, Real.sqrt_eq_rpow]
      calc 2 * Real.log x * Real.log x ^ A
          ≤ Real.log x * Real.log x * Real.log x ^ A :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL2 hL0.le) hLA.le
        _ = Real.log x ^ (A + 2) := by
            rw [hA2]
            ring
        _ ≤ x ^ (1 / 2 : ℝ) := hpow
    calc 2 * Real.sqrt x * Real.log x = Real.sqrt x * (2 * Real.log x) := by ring
      _ ≤ Real.sqrt x * (Real.sqrt x * Real.log x ^ (-A)) :=
          mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg x)
      _ = Real.sqrt x * Real.sqrt x * Real.log x ^ (-A) := by ring
      _ = x * Real.log x ^ (-A) := by rw [Real.mul_self_sqrt hx0.le]
  calc |residuePrefix theta ⌊x⌋₊ q c - x / (q.totient : ℝ)|
      ≤ |residuePrefix theta ⌊x⌋₊ q c -
            residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c| +
          |residuePrefix ArithmeticFunction.vonMangoldt ⌊x⌋₊ q c - x / (q.totient : ℝ)| :=
        abs_sub_le _ _ _
    _ ≤ x * Real.log x ^ (-A) + M * x * Real.log x ^ (-A) :=
        add_le_add (hpp.trans (h1.trans h2)) (hψ x hxx₀ q hq hqB c hc hcop)
    _ = (M + 1) * x * Real.log x ^ (-A) := by ring

/-- The trivial (Chebyshev) bound `θ(t; q, c) ≤ θ(t) ≤ 3t`. -/
theorem residuePrefix_theta_le (q c : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    residuePrefix theta ⌊t⌋₊ q c ≤ 3 * t := by
  have h1 : residuePrefix theta ⌊t⌋₊ q c ≤ ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, theta n := by
    unfold residuePrefix residueSlice
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n _ _ => theta_nonneg n)
  have h2 : ∑ n ∈ Finset.Ioc 0 ⌊t⌋₊, theta n = Chebyshev.theta t := by
    simp only [Chebyshev.theta, theta, Finset.sum_filter]
  have h3 : Chebyshev.theta t ≤ Real.log 4 * t := Chebyshev.theta_le_log4_mul_x ht
  have h4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  calc residuePrefix theta ⌊t⌋₊ q c ≤ Chebyshev.theta t := h1.trans_eq h2
    _ ≤ Real.log 4 * t := h3
    _ ≤ 3 * t := mul_le_mul_of_nonneg_right h4 ht

/-! ### Partial summation -/

/-- The sequence `n ↦ log n` on the primes `n ≡ c (mod q)` (more precisely `n % q = c`), and `0`
elsewhere. Its partial sums are `θ(t; q, c)`. -/
noncomputable def thetaSeq (q c n : ℕ) : ℝ := if n % q = c then theta n else 0

theorem thetaSeq_zero (q c : ℕ) : thetaSeq q c 0 = 0 := by
  simp [thetaSeq, theta]

theorem thetaSeq_one (q c : ℕ) : thetaSeq q c 1 = 0 := by
  simp [thetaSeq, theta, Nat.not_prime_one]

theorem residuePrefix_theta_eq_sum (Y q c : ℕ) :
    residuePrefix theta Y q c = ∑ k ∈ Finset.Icc 0 Y, thetaSeq q c k := by
  rw [← Finset.add_sum_Ioc_eq_sum_Icc (Nat.zero_le Y), thetaSeq_zero, zero_add, residuePrefix,
    residueSlice, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : n % q = c <;> simp [thetaSeq, h]

/-- Abel summation: `π(y; q, c) = θ(y; q, c) / log y + ∫₂^y θ(t; q, c) / (t log² t) dt`. -/
theorem primeCount_residue_eq (q c : ℕ) {y : ℝ} (hy : 2 ≤ y) :
    (((Finset.Iic ⌊y⌋₊).filter (fun p => p.Prime ∧ p % q = c)).card : ℝ) =
      residuePrefix theta ⌊y⌋₊ q c / Real.log y +
        ∫ t in (2 : ℝ)..y, residuePrefix theta ⌊t⌋₊ q c / (t * Real.log t ^ 2) := by
  have hIic : Finset.Iic ⌊y⌋₊ = Finset.Icc 0 ⌊y⌋₊ := by
    ext n
    simp
  have hcount : (((Finset.Iic ⌊y⌋₊).filter (fun p => p.Prime ∧ p % q = c)).card : ℝ) =
      ∑ k ∈ Finset.Icc 0 ⌊y⌋₊, (Real.log (k : ℝ))⁻¹ * thetaSeq q c k := by
    rw [hIic, Finset.natCast_card_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hp : n.Prime
    · by_cases hc : n % q = c
      · have hlog : Real.log (n : ℝ) ≠ 0 :=
          (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
        simp [thetaSeq, theta, hp, hc, hlog]
      · simp [thetaSeq, hp, hc]
    · simp [thetaSeq, theta, hp]
  have hdiff : ∀ t ∈ Set.Icc (2 : ℝ) y,
      DifferentiableAt ℝ (fun x : ℝ => (Real.log x)⁻¹) t := by
    intro t ht
    exact Real.differentiableAt_inv_log (by linarith [ht.1]) (by linarith [ht.1])
      (by linarith [ht.1])
  have hint : MeasureTheory.IntegrableOn (deriv fun x : ℝ => (Real.log x)⁻¹)
      (Set.Icc (2 : ℝ) y) := by
    rw [Real.deriv_inv_log]
    refine ContinuousOn.integrableOn_Icc fun t ht => ContinuousAt.continuousWithinAt ?_
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : Real.log t ^ 2 ≠ 0 := pow_ne_zero 2 (Real.log_pos (by linarith [ht.1])).ne'
    fun_prop
  have habel : ∑ k ∈ Finset.Icc 0 ⌊y⌋₊, (Real.log (k : ℝ))⁻¹ * thetaSeq q c k =
      (Real.log y)⁻¹ * ∑ k ∈ Finset.Icc 0 ⌊y⌋₊, thetaSeq q c k -
        ∫ t in Set.Ioc (2 : ℝ) y, deriv (fun x : ℝ => (Real.log x)⁻¹) t *
          ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, thetaSeq q c k :=
    sum_mul_eq_sub_integral_mul₁ (thetaSeq q c) (f := fun x : ℝ => (Real.log x)⁻¹)
      (thetaSeq_zero q c) (thetaSeq_one q c) y hdiff hint
  rw [← intervalIntegral.integral_of_le hy] at habel
  have hI : ∫ t in (2 : ℝ)..y, deriv (fun x : ℝ => (Real.log x)⁻¹) t *
      ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, thetaSeq q c k =
        -∫ t in (2 : ℝ)..y, residuePrefix theta ⌊t⌋₊ q c / (t * Real.log t ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [Real.deriv_inv_log_apply, residuePrefix_theta_eq_sum]
    ring
  rw [hcount, habel, hI, residuePrefix_theta_eq_sum]
  ring

/-- `Li y = y / log y - 2 / log 2 + ∫₂^y dt / log² t`. -/
theorem Li_eq_div_log_add_integral {y : ℝ} (hy : 2 ≤ y) :
    Li y = y / Real.log y - 2 / Real.log 2 + ∫ t in (2 : ℝ)..y, 1 / Real.log t ^ 2 := by
  have hderiv : ∀ t ∈ Set.uIcc (2 : ℝ) y,
      HasDerivAt (fun t : ℝ => t / Real.log t) (1 / Real.log t - 1 / Real.log t ^ 2) t := by
    intro t ht
    rw [Set.uIcc_of_le hy] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have h : HasDerivAt (fun t : ℝ => t / Real.log t)
        ((1 * Real.log t - t * t⁻¹) / Real.log t ^ 2) t :=
      (hasDerivAt_id' t).div (Real.hasDerivAt_log ht0) hl
    have hval : (1 * Real.log t - t * t⁻¹) / Real.log t ^ 2 =
        1 / Real.log t - 1 / Real.log t ^ 2 := by
      field_simp
    rwa [hval] at h
  have hi1 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t) MeasureTheory.volume 2 y := by
    refine ContinuousOn.intervalIntegrable fun t ht => ContinuousAt.continuousWithinAt ?_
    rw [Set.uIcc_of_le hy] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    fun_prop
  have hi2 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) MeasureTheory.volume 2 y :=
    Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hi1.sub hi2)
  rw [intervalIntegral.integral_sub hi1 hi2] at h
  unfold Li
  linarith

/-- The integrand of the error term in the partial summation; for `t > 1` it equals
`(θ(t; q, c) - t / φ(q)) / (t log² t)` (`errIntegrand_eq`). -/
noncomputable def errIntegrand (q c : ℕ) (t : ℝ) : ℝ :=
  residuePrefix theta ⌊t⌋₊ q c / (t * Real.log t ^ 2) -
    1 / (q.totient : ℝ) * (1 / Real.log t ^ 2)

theorem errIntegrand_eq {q : ℕ} (hq : 0 < q) (c : ℕ) {t : ℝ} (ht : 1 < t) :
    errIntegrand q c t =
      (residuePrefix theta ⌊t⌋₊ q c - t / (q.totient : ℝ)) / (t * Real.log t ^ 2) := by
  have ht0 : t ≠ 0 := by linarith
  have hl : Real.log t ≠ 0 := (Real.log_pos ht).ne'
  have hphi : (q.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hq).ne'
  unfold errIntegrand
  field_simp

theorem intervalIntegrable_theta_residue (q c : ℕ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => residuePrefix theta ⌊t⌋₊ q c / (t * Real.log t ^ 2))
      MeasureTheory.volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  have hg : MeasureTheory.IntegrableOn (fun t : ℝ => 1 / (t * Real.log t ^ 2))
      (Set.Icc a b) := by
    refine ContinuousOn.integrableOn_Icc fun t ht => ContinuousAt.continuousWithinAt ?_
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have hne : t * Real.log t ^ 2 ≠ 0 := mul_ne_zero ht0 (pow_ne_zero 2 hl)
    fun_prop
  have h := integrableOn_mul_sum_Icc (thetaSeq q c) (m := 0) (by linarith : (0 : ℝ) ≤ a) hg
  refine h.congr_fun (fun t _ => ?_) measurableSet_Icc
  simp only [residuePrefix_theta_eq_sum]
  ring

theorem intervalIntegrable_errIntegrand (q c : ℕ) {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (errIntegrand q c) MeasureTheory.volume a b :=
  (intervalIntegrable_theta_residue q c ha hab).sub
    ((Chebyshev.intervalIntegrable_one_div_log_sq ha (lt_of_lt_of_le ha hab)).const_mul
      (1 / (q.totient : ℝ)))

/-- Partial summation for the error term:
`π(y; q, c) - Li(y)/φ(q) = (θ(y; q, c) - y/φ(q)) / log y + 2 / (φ(q) log 2)
  + ∫₂^y (θ(t; q, c) - t/φ(q)) / (t log² t) dt`. -/
theorem primeCount_sub_Li_eq (q c : ℕ) {y : ℝ} (hy : 2 ≤ y) :
    (((Finset.Iic ⌊y⌋₊).filter (fun p => p.Prime ∧ p % q = c)).card : ℝ) -
        Li y / (q.totient : ℝ) =
      (residuePrefix theta ⌊y⌋₊ q c - y / (q.totient : ℝ)) / Real.log y +
        2 / Real.log 2 / (q.totient : ℝ) + ∫ t in (2 : ℝ)..y, errIntegrand q c t := by
  have hI1 := intervalIntegrable_theta_residue q c (by norm_num : (1 : ℝ) < 2) hy
  have hI2 : IntervalIntegrable (fun t : ℝ => 1 / (q.totient : ℝ) * (1 / Real.log t ^ 2))
      MeasureTheory.volume 2 y :=
    (Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)).const_mul _
  have hsub : ∫ t in (2 : ℝ)..y, errIntegrand q c t =
      (∫ t in (2 : ℝ)..y, residuePrefix theta ⌊t⌋₊ q c / (t * Real.log t ^ 2)) -
        1 / (q.totient : ℝ) * ∫ t in (2 : ℝ)..y, 1 / Real.log t ^ 2 := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hI1 hI2]
    rfl
  rw [primeCount_residue_eq q c hy, Li_eq_div_log_add_integral hy, hsub]
  ring

/-- The trivial bound for the integrand of the error term. -/
theorem abs_errIntegrand_le {q : ℕ} (hq : 0 < q) (c : ℕ) {t : ℝ} (ht : 2 ≤ t) :
    |errIntegrand q c t| ≤ 3 / Real.log 2 ^ 2 := by
  have ht0 : 0 < t := by linarith
  have ht1 : 1 < t := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hlt0 : 0 < Real.log t := lt_of_lt_of_le hlog2 hlt
  have hden : 0 < t * Real.log t ^ 2 := mul_pos ht0 (pow_pos hlt0 2)
  have hφ1 : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hΘ0 : 0 ≤ residuePrefix theta ⌊t⌋₊ q c :=
    residueSlice_nonneg theta theta_nonneg 0 ⌊t⌋₊ q c
  have hΘ3 : residuePrefix theta ⌊t⌋₊ q c ≤ 3 * t := residuePrefix_theta_le q c ht0.le
  have hdiv : t / (q.totient : ℝ) ≤ t := div_le_self ht0.le hφ1
  have hdiv0 : 0 ≤ t / (q.totient : ℝ) := div_nonneg ht0.le (by linarith)
  have hE : |residuePrefix theta ⌊t⌋₊ q c - t / (q.totient : ℝ)| ≤ 3 * t := by
    rw [abs_le]
    constructor <;> linarith
  have hsq : Real.log 2 ^ 2 ≤ Real.log t ^ 2 := pow_le_pow_left₀ hlog2.le hlt 2
  rw [errIntegrand_eq hq c ht1, abs_div, abs_of_pos hden,
    div_le_div_iff₀ hden (pow_pos hlog2 2)]
  calc |residuePrefix theta ⌊t⌋₊ q c - t / (q.totient : ℝ)| * Real.log 2 ^ 2
      ≤ 3 * t * Real.log t ^ 2 := mul_le_mul hE hsq (pow_pos hlog2 2).le (by linarith)
    _ = 3 * (t * Real.log t ^ 2) := by ring

/-! ### The prime-counting form -/

/-- Consequences of `e⁴ ≤ y` for the splitting point `√y`. -/
theorem sqrt_facts_of_exp_four_le {y : ℝ} (hy : Real.exp 4 ≤ y) :
    0 < y ∧ 4 ≤ Real.log y ∧ 2 ≤ Real.sqrt y ∧ Real.sqrt y ≤ y ∧
      Real.log (Real.sqrt y) = Real.log y / 2 := by
  have hy5 : 5 ≤ y := by
    have := Real.add_one_le_exp 4
    linarith
  have hy0 : 0 < y := by linarith
  have hL4 : 4 ≤ Real.log y := by
    rw [← Real.log_exp 4]
    exact Real.log_le_log (Real.exp_pos 4) hy
  have hss : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0.le
  have hs2 : 2 ≤ Real.sqrt y := (Real.le_sqrt' (by norm_num)).mpr (by norm_num; linarith)
  have hsy : Real.sqrt y ≤ y := by
    have : Real.sqrt y * 1 ≤ Real.sqrt y * Real.sqrt y :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  exact ⟨hy0, hL4, hs2, hsy, Real.log_sqrt hy0.le⟩

/-- The integral of the error integrand over `[2, s]`, by the trivial bound. -/
theorem abs_integral_errIntegrand_le {q : ℕ} (hq : 0 < q) (c : ℕ) {s : ℝ} (hs : 2 ≤ s) :
    |∫ t in (2 : ℝ)..s, errIntegrand q c t| ≤ 3 / Real.log 2 ^ 2 * s := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk3 : 0 ≤ 3 / Real.log 2 ^ 2 := div_nonneg (by norm_num) (pow_pos hlog2 2).le
  have hpt : ∀ t ∈ Set.uIoc (2 : ℝ) s, ‖errIntegrand q c t‖ ≤ 3 / Real.log 2 ^ 2 := by
    intro t ht
    rw [Set.uIoc_of_le hs] at ht
    rw [Real.norm_eq_abs]
    exact abs_errIntegrand_le hq c ht.1.le
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hs)] at h
  exact h.trans (mul_le_mul_of_nonneg_left (sub_le_self s (by norm_num)) hk3)

/-- The pointwise bound for the error integrand at a point `t` with `log t ≥ L / 2`, from a
Siegel–Walfisz bound for `θ(t; q, c)`. -/
theorem abs_errIntegrand_le_of_theta {q : ℕ} (hq : 0 < q) (c : ℕ) {M A L t : ℝ} (hM : 0 ≤ M)
    (hA : 0 < A) (hL : 0 < L) (hLt : L / 2 ≤ Real.log t) (hlogt : 1 ≤ Real.log t) (ht : 1 < t)
    (h : |residuePrefix theta ⌊t⌋₊ q c - t / (q.totient : ℝ)| ≤ M * t * Real.log t ^ (-A)) :
    |errIntegrand q c t| ≤ M * 2 ^ A * L ^ (-A) := by
  have ht0 : 0 < t := lt_trans zero_lt_one ht
  have hlogt0 : 0 < Real.log t := lt_of_lt_of_le zero_lt_one hlogt
  have hden : 0 < t * Real.log t ^ 2 := mul_pos ht0 (pow_pos hlogt0 2)
  have hP : 0 < (2 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) A
  have hR0 : 0 < L ^ (-A) := Real.rpow_pos_of_pos hL _
  have hK : 0 ≤ M * 2 ^ A * L ^ (-A) := mul_nonneg (mul_nonneg hM hP.le) hR0.le
  have hrp : Real.log t ^ (-A) ≤ 2 ^ A * L ^ (-A) := by
    calc Real.log t ^ (-A) ≤ (L / 2) ^ (-A) :=
          Real.rpow_le_rpow_of_nonpos (half_pos hL) hLt (neg_nonpos.mpr hA.le)
      _ = 2 ^ A * L ^ (-A) := by
          rw [Real.div_rpow hL.le (by norm_num : (0 : ℝ) ≤ 2),
            Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2) A, div_inv_eq_mul]
          ring
  have hsq1 : 1 ≤ Real.log t ^ 2 := one_le_pow₀ hlogt
  rw [errIntegrand_eq hq c ht, abs_div, abs_of_pos hden, div_le_iff₀ hden]
  calc |residuePrefix theta ⌊t⌋₊ q c - t / (q.totient : ℝ)|
      ≤ M * t * Real.log t ^ (-A) := h
    _ ≤ M * t * (2 ^ A * L ^ (-A)) := mul_le_mul_of_nonneg_left hrp (mul_nonneg hM ht0.le)
    _ = M * 2 ^ A * L ^ (-A) * (t * 1) := by ring
    _ ≤ M * 2 ^ A * L ^ (-A) * (t * Real.log t ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq1 ht0.le) hK

/-- If `q ≤ L^C`, `L ≤ 2u` and `u ≥ 2`, then `q ≤ u^{2C}` (used with `L = log y`, `u = log t`,
`√y ≤ t`). -/
theorem natCast_le_rpow_two_mul {q : ℕ} {C L u : ℝ} (hC : 0 < C) (hL : 0 < L) (hu : 2 ≤ u)
    (hLu : L ≤ 2 * u) (hq : (q : ℝ) ≤ L ^ C) : (q : ℝ) ≤ u ^ (2 * C) := by
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_two hu
  have hLu2 : L ≤ u ^ 2 := by nlinarith [mul_nonneg hu0.le (sub_nonneg.mpr hu)]
  calc (q : ℝ) ≤ L ^ C := hq
    _ ≤ (u ^ (2 : ℝ)) ^ C := by
        refine Real.rpow_le_rpow hL.le ?_ hC.le
        rw [Real.rpow_two]
        exact hLu2
    _ = u ^ (2 * C) := (Real.rpow_mul hu0.le 2 C).symm

/-- The integral of the error integrand over `[√y, y]`, from a Siegel–Walfisz bound for
`θ(t; q, c)` on that range. -/
theorem abs_integral_errIntegrand_le_of_theta {q : ℕ} (hq : 0 < q) (c : ℕ) {M A y : ℝ}
    (hM : 0 ≤ M) (hA : 0 < A) (hy : Real.exp 4 ≤ y)
    (h : ∀ t : ℝ, Real.sqrt y ≤ t → t ≤ y →
      |residuePrefix theta ⌊t⌋₊ q c - t / (q.totient : ℝ)| ≤ M * t * Real.log t ^ (-A)) :
    |∫ t in Real.sqrt y..y, errIntegrand q c t| ≤ M * 2 ^ A * Real.log y ^ (-A) * y := by
  obtain ⟨hy0, hL4, hs2, hsy, hlogs⟩ := sqrt_facts_of_exp_four_le hy
  have hL0 : 0 < Real.log y := lt_of_lt_of_le (by norm_num) hL4
  have hP : 0 < (2 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) A
  have hR0 : 0 < Real.log y ^ (-A) := Real.rpow_pos_of_pos hL0 _
  have hK : 0 ≤ M * 2 ^ A * Real.log y ^ (-A) := mul_nonneg (mul_nonneg hM hP.le) hR0.le
  have hpt : ∀ t ∈ Set.uIoc (Real.sqrt y) y,
      ‖errIntegrand q c t‖ ≤ M * 2 ^ A * Real.log y ^ (-A) := by
    intro t ht
    rw [Set.uIoc_of_le hsy] at ht
    obtain ⟨hst, hty⟩ := ht
    have hlogt : Real.log y / 2 ≤ Real.log t := by
      rw [← hlogs]
      exact Real.log_le_log (lt_of_lt_of_le zero_lt_two hs2) hst.le
    have hlogt1 : 1 ≤ Real.log t := by linarith only [hlogt, hL4]
    have ht1 : 1 < t := by linarith only [hst, hs2]
    rw [Real.norm_eq_abs]
    exact abs_errIntegrand_le_of_theta hq c hM hA hL0 hlogt hlogt1 ht1 (h t hst.le hty)
  have h' := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hsy)] at h'
  exact h'.trans (mul_le_mul_of_nonneg_left (sub_le_self y (Real.sqrt_nonneg y)) hK)

/-- The prime-counting estimate at a point `y`, from a Siegel–Walfisz bound for `θ(t; q, c)` on
`[√y, y]`. -/
theorem abs_primeCount_sub_Li_le_of_theta {q : ℕ} (hq : 0 < q) (c : ℕ) {M A y : ℝ}
    (hM : 0 ≤ M) (hA : 0 < A) (hy : Real.exp 4 ≤ y)
    (hpow : Real.log y ^ A ≤ y ^ (1 / 2 : ℝ))
    (h : ∀ t : ℝ, Real.sqrt y ≤ t → t ≤ y →
      |residuePrefix theta ⌊t⌋₊ q c - t / (q.totient : ℝ)| ≤ M * t * Real.log t ^ (-A)) :
    |(((Finset.Iic ⌊y⌋₊).filter (fun p => p.Prime ∧ p % q = c)).card : ℝ) -
        Li y / (q.totient : ℝ)| ≤
      (M + 2 / Real.log 2 + 3 / Real.log 2 ^ 2 + M * 2 ^ A) * y * Real.log y ^ (-A) := by
  obtain ⟨hy0, hL4, hs2, hsy, hlogs⟩ := sqrt_facts_of_exp_four_le hy
  have hL0 : 0 < Real.log y := lt_of_lt_of_le (by norm_num) hL4
  have hL1 : 1 ≤ Real.log y := le_trans (by norm_num) hL4
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk2 : 0 ≤ 2 / Real.log 2 := div_nonneg (by norm_num) hlog2.le
  have hk3 : 0 ≤ 3 / Real.log 2 ^ 2 := div_nonneg (by norm_num) (pow_pos hlog2 2).le
  have hφ1 : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hφ0 : (0 : ℝ) ≤ q.totient := le_trans zero_le_one hφ1
  have hsT : Real.sqrt y ≤ y * Real.log y ^ (-A) := by
    have hLA : 0 < Real.log y ^ A := Real.rpow_pos_of_pos hL0 A
    have hpow' : Real.log y ^ A ≤ Real.sqrt y := by
      rw [Real.sqrt_eq_rpow]
      exact hpow
    rw [Real.rpow_neg hL0.le, ← div_eq_mul_inv, le_div_iff₀ hLA]
    calc Real.sqrt y * Real.log y ^ A ≤ Real.sqrt y * Real.sqrt y :=
          mul_le_mul_of_nonneg_left hpow' (Real.sqrt_nonneg y)
      _ = y := Real.mul_self_sqrt hy0.le
  have hT1 : 1 ≤ y * Real.log y ^ (-A) := le_trans (le_trans one_le_two hs2) hsT
  -- the partial summation identity and the splitting of the integral at `√y`
  have hE := primeCount_sub_Li_eq q c (hs2.trans hsy)
  have hsplit : ∫ t in (2 : ℝ)..y, errIntegrand q c t =
      (∫ t in (2 : ℝ)..Real.sqrt y, errIntegrand q c t) +
        ∫ t in Real.sqrt y..y, errIntegrand q c t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_errIntegrand q c one_lt_two hs2)
      (intervalIntegrable_errIntegrand q c (lt_of_lt_of_le one_lt_two hs2) hsy)).symm
  -- the endpoint term
  have hb0 : |(residuePrefix theta ⌊y⌋₊ q c - y / (q.totient : ℝ)) / Real.log y| ≤
      M * y * Real.log y ^ (-A) := by
    rw [abs_div, abs_of_pos hL0]
    exact (div_le_self (abs_nonneg _) hL1).trans (h y hsy le_rfl)
  -- the constant term
  have hbc : |2 / Real.log 2 / (q.totient : ℝ)| ≤ 2 / Real.log 2 := by
    rw [abs_of_nonneg (div_nonneg hk2 hφ0)]
    exact div_le_self hk2 hφ1
  -- the two integrals
  have hb1 := abs_integral_errIntegrand_le hq c hs2
  have hb2 := abs_integral_errIntegrand_le_of_theta hq c hM hA hy h
  -- assembling
  have e1 : 2 / Real.log 2 ≤ 2 / Real.log 2 * (y * Real.log y ^ (-A)) :=
    le_mul_of_one_le_right hk2 hT1
  have e2 : 3 / Real.log 2 ^ 2 * Real.sqrt y ≤
      3 / Real.log 2 ^ 2 * (y * Real.log y ^ (-A)) :=
    mul_le_mul_of_nonneg_left hsT hk3
  rw [hE, hsplit]
  calc |(residuePrefix theta ⌊y⌋₊ q c - y / (q.totient : ℝ)) / Real.log y +
          2 / Real.log 2 / (q.totient : ℝ) +
          ((∫ t in (2 : ℝ)..Real.sqrt y, errIntegrand q c t) +
            ∫ t in Real.sqrt y..y, errIntegrand q c t)|
      ≤ |(residuePrefix theta ⌊y⌋₊ q c - y / (q.totient : ℝ)) / Real.log y| +
          |2 / Real.log 2 / (q.totient : ℝ)| +
          (|∫ t in (2 : ℝ)..Real.sqrt y, errIntegrand q c t| +
            |∫ t in Real.sqrt y..y, errIntegrand q c t|) :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (abs_add_le _ _))
    _ ≤ M * y * Real.log y ^ (-A) + 2 / Real.log 2 +
          (3 / Real.log 2 ^ 2 * Real.sqrt y + M * 2 ^ A * Real.log y ^ (-A) * y) :=
        add_le_add (add_le_add hb0 hbc) (add_le_add hb1 hb2)
    _ ≤ M * y * Real.log y ^ (-A) + 2 / Real.log 2 * (y * Real.log y ^ (-A)) +
          (3 / Real.log 2 ^ 2 * (y * Real.log y ^ (-A)) +
            M * 2 ^ A * Real.log y ^ (-A) * y) :=
        add_le_add (add_le_add le_rfl e1) (add_le_add e2 le_rfl)
    _ = (M + 2 / Real.log 2 + 3 / Real.log 2 ^ 2 + M * 2 ^ A) * y * Real.log y ^ (-A) := by
        ring

/-- The prime-counting form of Siegel–Walfisz, for a residue `c < q` (`p % q = c`). -/
theorem siegelWalfisz_primeCounting_mod (A C : ℝ) (hA : 0 < A) (hC : 0 < C) :
    ∃ M : ℝ, 0 < M ∧ ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ q : ℕ, 0 < q →
      (q : ℝ) ≤ Real.log y ^ C → ∀ c : ℕ, c < q → Nat.Coprime c q →
        |(((Finset.Iic ⌊y⌋₊).filter (fun p => p.Prime ∧ p % q = c)).card : ℝ) -
            Li y / (q.totient : ℝ)| ≤ M * y * Real.log y ^ (-A) := by
  obtain ⟨M, hM, x₀, hx₀, hθ⟩ := siegelWalfisz_theta A (2 * C) hA (mul_pos zero_lt_two hC)
  have hev : ∀ᶠ y : ℝ in Filter.atTop,
      Real.exp 4 ≤ y ∧ x₀ ^ 2 ≤ y ∧ Real.log y ^ A ≤ y ^ (1 / 2 : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop (Real.exp 4),
      Filter.eventually_ge_atTop (x₀ ^ 2),
      eventually_log_rpow_le_rpow A (by norm_num : (0 : ℝ) < 1 / 2)] with y h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨y₀, hy₀⟩ := Filter.eventually_atTop.mp hev
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hk2 : 0 ≤ 2 / Real.log 2 := div_nonneg (by norm_num) hlog2.le
  have hk3 : 0 ≤ 3 / Real.log 2 ^ 2 := div_nonneg (by norm_num) (pow_pos hlog2 2).le
  have hMP : 0 < M * (2 : ℝ) ^ A := mul_pos hM (Real.rpow_pos_of_pos (by norm_num) A)
  refine ⟨M + 2 / Real.log 2 + 3 / Real.log 2 ^ 2 + M * 2 ^ A,
    by linarith only [hM, hk2, hk3, hMP], y₀, ?_⟩
  intro y hy q hq hqC c hc hcop
  obtain ⟨hye, hyx, hpow⟩ := hy₀ y hy
  obtain ⟨hy0, hL4, hs2, hsy, hlogs⟩ := sqrt_facts_of_exp_four_le hye
  have hx₀s : x₀ ≤ Real.sqrt y := (Real.le_sqrt' (lt_trans zero_lt_one hx₀)).mpr hyx
  refine abs_primeCount_sub_Li_le_of_theta hq c hM.le hA hye hpow ?_
  intro t hst hty
  have hlogt : Real.log y / 2 ≤ Real.log t := by
    rw [← hlogs]
    exact Real.log_le_log (lt_of_lt_of_le zero_lt_two hs2) hst
  have hqt : (q : ℝ) ≤ Real.log t ^ (2 * C) :=
    natCast_le_rpow_two_mul hC (lt_of_lt_of_le (by norm_num) hL4)
      (by linarith only [hlogt, hL4]) (by linarith only [hlogt]) hqC
  exact hθ t (hx₀s.trans hst) q hq hqt c hc hcop

/-- **The Siegel–Walfisz theorem, prime-counting form** ([S, Theorem `thm:sw`],
[P, Lemma `lem:prime-estimates`]). For fixed `A, C > 0`, uniformly for `gcd(a, r) = 1` and
`1 ≤ r ≤ (log y)^C`,

  `#{p ≤ y : p prime, p ≡ a (mod r)} = Li(y) / φ(r) + O_{A,C}(y / (log y)^A)`.

The constant `M` and the threshold `y₀` depend only on `A` and `C` (ineffectively). -/
theorem siegelWalfisz_primeCounting :
    ∀ A C : ℝ, 0 < A → 0 < C → ∃ M : ℝ, 0 < M ∧ ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
      ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ Real.log y ^ C → ∀ a : ℕ, Nat.Coprime a r →
        |(((Finset.Iic ⌊y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD r])).card : ℝ) -
            Li y / (r.totient : ℝ)| ≤ M * y * Real.log y ^ (-A) := by
  intro A C hA hC
  obtain ⟨M, hM, y₀, hy₀⟩ := siegelWalfisz_primeCounting_mod A C hA hC
  refine ⟨M, hM, y₀, ?_⟩
  intro y hy r hr hrC a ha
  have hc : a % r < r := Nat.mod_lt a hr
  have hcop : Nat.Coprime (a % r) r := (Nat.gcd_rec r a).symm.trans ha.symm
  have hfilter : (Finset.Iic ⌊y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD r]) =
      (Finset.Iic ⌊y⌋₊).filter (fun p => p.Prime ∧ p % r = a % r) :=
    Finset.filter_congr fun p _ => Iff.rfl
  rw [hfilter]
  exact hy₀ y hy r hr hrC (a % r) hc hcop

/-! ### The range `2 ≤ y ≤ y₀` -/

/-- The trivial bound `|Li y| ≤ y / log 2` for `y ≥ 2`. -/
theorem abs_Li_le {y : ℝ} (hy : 2 ≤ y) : |Li y| ≤ y / Real.log 2 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpt : ∀ t ∈ Set.uIoc (2 : ℝ) y, ‖1 / Real.log t‖ ≤ 1 / Real.log 2 := by
    intro t ht
    rw [Set.uIoc_of_le hy] at ht
    have hlt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht.1.le
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg zero_le_one (hlog2.le.trans hlt))]
    exact one_div_le_one_div_of_le hlog2 hlt
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hy)] at h
  calc |Li y| ≤ 1 / Real.log 2 * (y - 2) := h
    _ ≤ 1 / Real.log 2 * y :=
        mul_le_mul_of_nonneg_left (sub_le_self y (by norm_num))
          (div_nonneg zero_le_one hlog2.le)
    _ = y / Real.log 2 := by ring

/-- **The Siegel–Walfisz theorem, prime-counting form, for all `y ≥ 2`.** The statement of
`siegelWalfisz_primeCounting` without a threshold: the range `2 ≤ y < y₀` is covered by the
trivial bounds `π(y; r, a) ≤ y + 1` and `Li y ≤ y / log 2`, at the cost of a larger constant. -/
theorem siegelWalfisz_primeCounting_of_two_le :
    ∀ A C : ℝ, 0 < A → 0 < C → ∃ M : ℝ, 0 < M ∧ ∀ y : ℝ, 2 ≤ y →
      ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ Real.log y ^ C → ∀ a : ℕ, Nat.Coprime a r →
        |(((Finset.Iic ⌊y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD r])).card : ℝ) -
            Li y / (r.totient : ℝ)| ≤ M * y * Real.log y ^ (-A) := by
  intro A C hA hC
  obtain ⟨M, hM, y₀, hy₀⟩ := siegelWalfisz_primeCounting A C hA hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨Y, hYdef⟩ : ∃ Y : ℝ, Y = max y₀ 2 := ⟨_, rfl⟩
  have hY2 : 2 ≤ Y := by
    rw [hYdef]
    exact le_max_right _ _
  have hYy₀ : y₀ ≤ Y := by
    rw [hYdef]
    exact le_max_left _ _
  have hLY : 0 < Real.log Y := Real.log_pos (lt_of_lt_of_le one_lt_two hY2)
  have hLYA : 0 < Real.log Y ^ A := Real.rpow_pos_of_pos hLY A
  have hYdiv0 : 0 ≤ Y / Real.log 2 := div_nonneg (le_trans zero_le_two hY2) hlog2.le
  have hK₀ : 0 < Y + 1 + Y / Real.log 2 := by linarith only [hY2, hYdiv0]
  refine ⟨M + (Y + 1 + Y / Real.log 2) * Real.log Y ^ A, add_pos hM (mul_pos hK₀ hLYA), ?_⟩
  intro y hy r hr hrC a ha
  have hy0 : 0 < y := lt_of_lt_of_le zero_lt_two hy
  have hLy : 0 < Real.log y := Real.log_pos (lt_of_lt_of_le one_lt_two hy)
  have hT0 : 0 ≤ y * Real.log y ^ (-A) := mul_nonneg hy0.le (Real.rpow_nonneg hLy.le _)
  rcases le_or_gt y₀ y with hyy | hyy
  · -- `y ≥ y₀`: the theorem with a threshold
    refine (hy₀ y hyy r hr hrC a ha).trans ?_
    calc M * y * Real.log y ^ (-A)
        ≤ M * y * Real.log y ^ (-A) +
            (Y + 1 + Y / Real.log 2) * Real.log Y ^ A * (y * Real.log y ^ (-A)) :=
          le_add_of_nonneg_right (mul_nonneg (mul_nonneg hK₀.le hLYA.le) hT0)
      _ = (M + (Y + 1 + Y / Real.log 2) * Real.log Y ^ A) * y * Real.log y ^ (-A) := by ring
  · -- `2 ≤ y < y₀`: the trivial bounds
    have hyY : y ≤ Y := (le_of_lt hyy).trans hYy₀
    have hcount0 : (0 : ℝ) ≤
        ((Finset.Iic ⌊y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD r])).card := Nat.cast_nonneg _
    have hcount : (((Finset.Iic ⌊y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD r])).card : ℝ) ≤
        y + 1 := by
      have h1 : ((Finset.Iic ⌊y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD r])).card ≤
          ⌊y⌋₊ + 1 := (Finset.card_filter_le _ _).trans (by simp)
      have h2 : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le hy0.le
      have h3 : (((Finset.Iic ⌊y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD r])).card : ℝ) ≤
          (⌊y⌋₊ : ℝ) + 1 := by exact_mod_cast h1
      linarith only [h2, h3]
    have hφ1 : (1 : ℝ) ≤ r.totient := by exact_mod_cast Nat.totient_pos.mpr hr
    have hLi : |Li y / (r.totient : ℝ)| ≤ y / Real.log 2 := by
      rw [abs_div, abs_of_pos (lt_of_lt_of_le zero_lt_one hφ1)]
      exact (div_le_self (abs_nonneg _) hφ1).trans (abs_Li_le hy)
    obtain ⟨hLi1, hLi2⟩ := abs_le.mp hLi
    have hydiv : y / Real.log 2 ≤ Y / Real.log 2 := div_le_div_of_nonneg_right hyY hlog2.le
    have hlhs : |(((Finset.Iic ⌊y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD r])).card : ℝ) -
        Li y / (r.totient : ℝ)| ≤ Y + 1 + Y / Real.log 2 := by
      rw [abs_le]
      constructor <;> linarith only [hLi1, hLi2, hcount0, hcount, hydiv, hyY, hy]
    -- the right-hand side is at least `Y + 1 + Y / log 2`
    have hrpow : Real.log Y ^ (-A) ≤ Real.log y ^ (-A) :=
      Real.rpow_le_rpow_of_nonpos hLy (Real.log_le_log hy0 hyY) (neg_nonpos.mpr hA.le)
    have hone : 1 ≤ Real.log Y ^ A * (y * Real.log y ^ (-A)) := by
      have h1 : Real.log Y ^ A * Real.log Y ^ (-A) = 1 := by
        rw [← Real.rpow_add hLY, add_neg_cancel, Real.rpow_zero]
      have h2 : 1 * Real.log Y ^ (-A) ≤ y * Real.log y ^ (-A) :=
        mul_le_mul (le_trans one_le_two hy) hrpow (Real.rpow_nonneg hLY.le _) hy0.le
      calc (1 : ℝ) = Real.log Y ^ A * (1 * Real.log Y ^ (-A)) := by rw [one_mul, h1]
        _ ≤ Real.log Y ^ A * (y * Real.log y ^ (-A)) := mul_le_mul_of_nonneg_left h2 hLYA.le
    refine hlhs.trans ?_
    calc Y + 1 + Y / Real.log 2
        ≤ (Y + 1 + Y / Real.log 2) * (Real.log Y ^ A * (y * Real.log y ^ (-A))) :=
          le_mul_of_one_le_right hK₀.le hone
      _ ≤ M * (y * Real.log y ^ (-A)) +
            (Y + 1 + Y / Real.log 2) * (Real.log Y ^ A * (y * Real.log y ^ (-A))) :=
          le_add_of_nonneg_left (mul_nonneg hM.le hT0)
      _ = (M + (Y + 1 + Y / Real.log 2) * Real.log Y ^ A) * y * Real.log y ^ (-A) := by ring

end SimultaneousPrimitiveRoots.Classical
