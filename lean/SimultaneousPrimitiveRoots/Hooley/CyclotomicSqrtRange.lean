module

public import SimultaneousPrimitiveRoots.Hooley.GRHMain
public import SimultaneousPrimitiveRoots.ProgressionSieveConsequences
public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The Gaussian trace of `ℚ(ζ_q)` up to `q ≈ √x`

The existing uniform bound `Θ_{ℚ(ζ_q)}(x) ≪ x` covered `q ≤ x^η` with `η < 1/5`. Here it is
extended to the whole range `q ≤ √x / log⁴ x` needed by Hooley's method:

* the degree-one primes are split at `p = q²`; below `q²` the progression is counted
  trivially, above `q²` the Brun–Titchmarsh-type sieve bound holds without error term;
* the higher prime powers are bounded by the Rankin trick `σ = 1/2 + 1/log x` in the existing
  majorant, which costs only `log² x`;
* the ramified prime contributes `O(q² / x)`.

Everything here is unconditional.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Filter Asymptotics Finset NumberField
open scoped Topology
noncomputable section
open Classical

/-- **The `p`-series near exponent one.** For `s > 1`, `∑ n^(-s) ≤ 1 + 1/(s-1)`. -/
theorem tsum_nat_rpow_neg_le {s : ℝ} (hs : 1 < s) :
    ∑' n : ℕ, (n : ℝ) ^ (-s) ≤ 1 + 1 / (s - 1) := by
  have hnonneg : ∀ n : ℕ, 0 ≤ (n : ℝ) ^ (-s) := fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hs1 : 0 < s - 1 := by linarith
  apply Real.tsum_le_of_sum_range_le hnonneg
  intro N
  set f : ℝ → ℝ := fun t => t ^ (-s) with hf
  have hanti : ∀ M : ℕ, AntitoneOn f (Set.Icc ((1 : ℕ) : ℝ) (M : ℝ)) := by
    intro M a ha b hb hab
    have ha1 : (1 : ℝ) ≤ a := by simpa using ha.1
    exact Real.rpow_le_rpow_of_nonpos (by linarith) hab (by linarith)
  have hint : ∑ i ∈ Finset.Ico 1 (N + 1), f ((i + 1 : ℕ) : ℝ) ≤ 1 / (s - 1) := by
    have h := (hanti (N + 1)).sum_le_integral_Ico (by omega : 1 ≤ N + 1)
    refine h.trans ?_
    have hzero : (0 : ℝ) ∉ Set.uIcc ((1 : ℕ) : ℝ) ((N + 1 : ℕ) : ℝ) := by
      rw [Set.uIcc_of_le (by exact_mod_cast (by omega : 1 ≤ N + 1))]
      intro hmem
      have := hmem.1
      norm_num at this
    have hI : ∫ t in ((1 : ℕ) : ℝ)..((N + 1 : ℕ) : ℝ), f t =
        (((N + 1 : ℕ) : ℝ) ^ (-s + 1) - ((1 : ℕ) : ℝ) ^ (-s + 1)) / (-s + 1) := by
      simp only [hf]
      exact integral_rpow (Or.inr ⟨by linarith, hzero⟩)
    rw [hI]
    set P := ((N + 1 : ℕ) : ℝ) ^ (-s + 1) with hP
    have hP0 : 0 ≤ P := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have h1 : ((1 : ℕ) : ℝ) ^ (-s + 1) = 1 := by rw [Nat.cast_one, Real.one_rpow]
    rw [h1]
    have hne1 : -s + 1 ≠ 0 := (by linarith : -s + 1 < 0).ne
    have hne2 : s - 1 ≠ 0 := hs1.ne'
    have key : (P - 1) / (-s + 1) = (1 - P) / (s - 1) := by
      rw [div_eq_div_iff hne1 hne2]
      ring
    rw [key]
    exact div_le_div_of_nonneg_right (by linarith) hs1.le
  have hsplit : ∑ n ∈ range (N + 1 + 1), f n = f 0 + f 1 +
      ∑ i ∈ Finset.Ico 1 (N + 1), f ((i + 1 : ℕ) : ℝ) := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_Ico_eq_sum_range,
      Nat.add_sub_cancel]
    have hcongr : ∑ k ∈ range N, f ((1 + k + 1 : ℕ) : ℝ) =
        ∑ k ∈ range N, f ((k + 1 + 1 : ℕ) : ℝ) :=
      Finset.sum_congr rfl (fun k _ => by rw [add_comm 1 k])
    rw [hcongr]
    simp only [zero_add, Nat.cast_zero, Nat.cast_one]
    ring
  have hf0 : f 0 = 0 := by
    simp only [hf]
    exact Real.zero_rpow (by linarith)
  have hf1 : f 1 = 1 := by simp only [hf, Real.one_rpow]
  calc ∑ n ∈ range N, (n : ℝ) ^ (-s) ≤ ∑ n ∈ range (N + 1 + 1), (n : ℝ) ^ (-s) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
          (fun n _ _ => hnonneg n)
    _ = ∑ n ∈ range (N + 1 + 1), f n := rfl
    _ = f 0 + f 1 + ∑ i ∈ Finset.Ico 1 (N + 1), f ((i + 1 : ℕ) : ℝ) := hsplit
    _ ≤ 0 + 1 + 1 / (s - 1) := by rw [hf0, hf1]; linarith
    _ = 1 + 1 / (s - 1) := by ring

/-- `2^(-σ) ≤ 3/4` for `σ ≥ 1/2`. -/
theorem two_rpow_neg_le_three_quarters {σ : ℝ} (hσ : 1 / 2 ≤ σ) :
    (2 : ℝ) ^ (-σ) ≤ 3 / 4 := by
  have hsqrt : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have h1 : Real.sqrt 2 ≤ (2 : ℝ) ^ σ := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hσ
  have h2 : (4 / 3 : ℝ) ≤ (2 : ℝ) ^ σ := hsqrt.trans h1
  rw [Real.rpow_neg (by norm_num)]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ σ := Real.rpow_pos_of_pos (by norm_num) σ
  rw [inv_le_comm₀ hpos (by norm_num)]
  linarith

/-- The higher-prime-power constant at `σ = 1/2 + ε` grows like `ε⁻²`. -/
theorem gaussianHigherPrimePowerConstant_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    gaussianHigherPrimePowerConstant (1 / 2 + ε) ≤
      8 * Real.exp ((Real.log 2) ^ 2 + 9 / 16) / ε ^ 2 := by
  unfold gaussianHigherPrimePowerConstant
  set σ : ℝ := 1 / 2 + ε with hσ
  have hexp : Real.exp ((Real.log 2) ^ 2 + σ ^ 2 / 4) ≤ Real.exp ((Real.log 2) ^ 2 + 9 / 16) := by
    apply Real.exp_le_exp.mpr
    have : σ ^ 2 ≤ 9 / 4 := by nlinarith
    linarith
  have hinv : (σ - 1 / 2)⁻¹ = ε⁻¹ := by rw [hσ]; ring_nf
  have h2 : (2 : ℝ) ^ (-σ) ≤ 3 / 4 := two_rpow_neg_le_three_quarters (by linarith)
  have hden : (1 - (2 : ℝ) ^ (-σ))⁻¹ ≤ 4 := by
    have hpos : (1 / 4 : ℝ) ≤ 1 - (2 : ℝ) ^ (-σ) := by linarith
    calc (1 - (2 : ℝ) ^ (-σ))⁻¹ ≤ (1 / 4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hpos
      _ = 4 := by norm_num
  have hseries : ∑' p : ℕ, (p : ℝ) ^ (-σ - 1 / 2) ≤ 1 + 1 / ε := by
    have h := tsum_nat_rpow_neg_le (s := 1 + ε) (by linarith)
    have hexp' : -σ - 1 / 2 = -(1 + ε) := by rw [hσ]; ring
    rw [hexp']
    simpa using h
  have hden0 : 0 ≤ (1 - (2 : ℝ) ^ (-σ))⁻¹ := by
    apply inv_nonneg.mpr
    linarith
  have hser0 : 0 ≤ ∑' p : ℕ, (p : ℝ) ^ (-σ - 1 / 2) :=
    tsum_nonneg fun p => Real.rpow_nonneg (Nat.cast_nonneg p) _
  have hE0 : 0 < Real.exp ((Real.log 2) ^ 2 + 9 / 16) := Real.exp_pos _
  rw [hinv]
  calc Real.exp ((Real.log 2) ^ 2 + σ ^ 2 / 4) * ε⁻¹ * (1 - (2 : ℝ) ^ (-σ))⁻¹ *
        (∑' p : ℕ, (p : ℝ) ^ (-σ - 1 / 2))
      ≤ Real.exp ((Real.log 2) ^ 2 + 9 / 16) * ε⁻¹ * 4 * (1 + 1 / ε) := by
        apply mul_le_mul _ hseries hser0 (by positivity)
        apply mul_le_mul _ hden hden0 (by positivity)
        exact mul_le_mul_of_nonneg_right hexp (by positivity)
    _ ≤ 8 * Real.exp ((Real.log 2) ^ 2 + 9 / 16) / ε ^ 2 := by
        have hεinv : ε⁻¹ ≤ (ε ^ 2)⁻¹ := by
          apply inv_anti₀ (by positivity)
          nlinarith
        have hexpand : Real.exp ((Real.log 2) ^ 2 + 9 / 16) * ε⁻¹ * 4 * (1 + 1 / ε) =
            4 * Real.exp ((Real.log 2) ^ 2 + 9 / 16) * (ε⁻¹ + (ε ^ 2)⁻¹) := by
          ring
        have hgoal : 8 * Real.exp ((Real.log 2) ^ 2 + 9 / 16) / ε ^ 2 =
            4 * Real.exp ((Real.log 2) ^ 2 + 9 / 16) * (2 * (ε ^ 2)⁻¹) := by
          ring
        rw [hexpand, hgoal]
        have : ε⁻¹ + (ε ^ 2)⁻¹ ≤ 2 * (ε ^ 2)⁻¹ := by linarith
        exact mul_le_mul_of_nonneg_left this (by positivity)

/-- **Rankin's trick for higher prime powers.** Taking `σ = 1/2 + 1/log x`, the higher
prime powers of any Galois field contribute at most `[K:ℚ] · c · log² x · √x`. -/
theorem gaussianHigherPrimePowerTrace_le_rankin (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {x : ℝ} (hx : Real.exp 1 ≤ x) :
    gaussianHigherPrimePowerTrace K x ≤
      (Module.finrank ℚ K : ℝ) *
        (8 * Real.exp ((Real.log 2) ^ 2 + 9 / 16) * Real.exp 1) *
          (Real.log x ^ 2 * Real.sqrt x) := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hx
  have hL1 : 1 ≤ Real.log x := one_le_log_of_exp_one_le hx
  have hL : 0 < Real.log x := by linarith
  set ε : ℝ := 1 / Real.log x with hεdef
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    rw [hεdef, div_le_one hL]
    exact hL1
  have hσ : 1 / 2 < 1 / 2 + ε := by linarith
  have hLne : Real.log x ≠ 0 := hL.ne'
  have hmain := gaussianHigherPrimePowerTrace_le K hσ hx0
  have hconst := gaussianHigherPrimePowerConstant_le hε0 hε1
  have hpow : x ^ (1 / 2 + ε) = Real.sqrt x * Real.exp 1 := by
    rw [Real.rpow_add hx0, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx0 ε, hεdef]
    congr 1
    congr 1
    field_simp
  have hεsq : 8 * Real.exp ((Real.log 2) ^ 2 + 9 / 16) / ε ^ 2 =
      8 * Real.exp ((Real.log 2) ^ 2 + 9 / 16) * Real.log x ^ 2 := by
    rw [hεdef, div_pow, one_pow, div_div_eq_mul_div, div_one]
  have hn : (0 : ℝ) ≤ Module.finrank ℚ K := Nat.cast_nonneg _
  calc gaussianHigherPrimePowerTrace K x
      ≤ (Module.finrank ℚ K : ℝ) * gaussianHigherPrimePowerConstant (1 / 2 + ε) *
          x ^ (1 / 2 + ε) := hmain
    _ ≤ (Module.finrank ℚ K : ℝ) * (8 * Real.exp ((Real.log 2) ^ 2 + 9 / 16) / ε ^ 2) *
          x ^ (1 / 2 + ε) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hx0.le _)
        exact mul_le_mul_of_nonneg_left hconst hn
    _ = (Module.finrank ℚ K : ℝ) *
          (8 * Real.exp ((Real.log 2) ^ 2 + 9 / 16) * Real.exp 1) *
            (Real.log x ^ 2 * Real.sqrt x) := by
        rw [hεsq, hpow]
        ring

/-- The Gaussian weight never exceeds `exp((log 2)²)`. -/
theorem artinGaussianWeight_le_max (t : ℝ) :
    artinGaussianWeight t ≤ Real.exp ((Real.log 2) ^ 2) := by
  unfold artinGaussianWeight
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (Real.log t)]

/-- **Degree-one primes with the split at `q²`.** Below `q²` the progression is counted
trivially; above `q²` the sieve bound has no additive error. -/
theorem progressionTrace_le_split {C : ℝ} (hC : 0 ≤ C)
    (hAP : ProgressionChebyshevUpperBound C) {q : ℕ} (hq : q.Prime) {x : ℝ} (hx : 1 ≤ x) :
    ((q : ℝ) - 1) * gaussianProgressionPrimeTrace q x ≤
      gaussianAbelConstant * C * x +
        2 * Real.exp ((Real.log 2) ^ 2) * (q : ℝ) ^ 2 * Real.log q := by
  have hx0 : 0 < x := by linarith
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hq1 : 0 < (q : ℝ) - 1 := by linarith
  have hq1ne : (q : ℝ) - 1 ≠ 0 := hq1.ne'
  set W : ℝ := Real.exp ((Real.log 2) ^ 2) with hW
  have hW0 : 0 < W := Real.exp_pos _
  set b : ℕ → ℝ := fun p => if q ^ 2 ≤ p then progressionChebyshevTerm q p else 0 with hb
  have hb0 : ∀ p, 0 ≤ b p := by
    intro p
    simp only [hb]
    split_ifs
    · exact progressionChebyshevTerm_nonneg q p
    · exact le_rfl
  have hbprefix : ∀ N, ∑ p ∈ range N, b p ≤ (C / ((q : ℝ) - 1)) * N + 0 := by
    intro N
    rw [add_zero]
    by_cases hN : q ^ 2 ≤ N
    · calc ∑ p ∈ range N, b p ≤ ∑ p ∈ range N, progressionChebyshevTerm q p := by
            apply sum_le_sum
            intro p _
            simp only [hb]
            split_ifs
            · exact le_rfl
            · exact progressionChebyshevTerm_nonneg q p
        _ = progressionChebyshevPrefix q N := rfl
        _ ≤ C * (N : ℝ) / ((q : ℝ) - 1) := hAP q hq N hN
        _ = (C / ((q : ℝ) - 1)) * N := by ring
    · have hzero : ∑ p ∈ range N, b p = 0 := by
        apply sum_eq_zero
        intro p hp
        have hpN := mem_range.mp hp
        simp only [hb]
        rw [if_neg (fun h => hN (h.trans hpN.le))]
      rw [hzero]
      positivity
  have hsmall : progressionChebyshevPrefix q (q ^ 2) ≤ ((q : ℝ) + 1) * (2 * Real.log q) := by
    have h1 := progressionChebyshevPrefix_le_card_log q (q ^ 2)
    have h2 := progressionPrefixPrimes_card_le_mass_add_one hq (q ^ 2)
    have hlog : Real.log ((q ^ 2 : ℕ) : ℝ) = 2 * Real.log q := by
      push_cast
      rw [Real.log_pow]
      push_cast
      ring
    have hmass : ((q ^ 2 : ℕ) : ℝ) / q + 1 = (q : ℝ) + 1 := by
      push_cast
      field_simp
    rw [hlog] at h1
    rw [hmass] at h2
    have hlogq : 0 ≤ 2 * Real.log q := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ q)
      linarith
    calc progressionChebyshevPrefix q (q ^ 2)
        ≤ ((progressionPrefixPrimes q (q ^ 2)).card : ℝ) * (2 * Real.log q) := h1
      _ ≤ ((q : ℝ) + 1) * (2 * Real.log q) := mul_le_mul_of_nonneg_right h2 hlogq
  have hterm : ∀ p, gaussianProgressionPrimeTerm q x p ≤
      W * (if p < q ^ 2 then progressionChebyshevTerm q p else 0) +
        gaussianAbelConstant * (b p * rationalSmoothingKernel x p) := by
    intro p
    rw [gaussianProgressionPrimeTerm_eq_chebyshev]
    have hc0 := progressionChebyshevTerm_nonneg q p
    by_cases hp : p < q ^ 2
    · have hbp : b p = 0 := by
        simp only [hb]
        rw [if_neg (not_le.mpr hp)]
      rw [if_pos hp, hbp, zero_mul, mul_zero, add_zero]
      calc progressionChebyshevTerm q p * artinGaussianWeight ((p : ℝ) / x)
          ≤ progressionChebyshevTerm q p * W :=
            mul_le_mul_of_nonneg_left (artinGaussianWeight_le_max _) hc0
        _ = W * progressionChebyshevTerm q p := by ring
    · have hbp : b p = progressionChebyshevTerm q p := by
        simp only [hb]
        rw [if_pos (not_lt.mp hp)]
      rw [if_neg hp, mul_zero, zero_add, hbp]
      have hk := artinGaussianWeight_le_rationalKernel hx p
      calc progressionChebyshevTerm q p * artinGaussianWeight ((p : ℝ) / x)
          ≤ progressionChebyshevTerm q p *
              (gaussianAbelConstant * rationalSmoothingKernel x p) :=
            mul_le_mul_of_nonneg_left hk hc0
        _ = gaussianAbelConstant * (progressionChebyshevTerm q p *
              rationalSmoothingKernel x p) := by ring
  have hrange : ∀ N, ∑ p ∈ range N, gaussianProgressionPrimeTerm q x p ≤
      W * (((q : ℝ) + 1) * (2 * Real.log q)) +
        gaussianAbelConstant * ((C / ((q : ℝ) - 1)) * x + 0) := by
    intro N
    have hA : 0 ≤ C / ((q : ℝ) - 1) := div_nonneg hC hq1.le
    have hsmooth := rationalSmoothing_sum_range_le hx0 hA le_rfl b hbprefix N
    have hind : ∑ p ∈ range N, (if p < q ^ 2 then progressionChebyshevTerm q p else 0) ≤
        progressionChebyshevPrefix q (q ^ 2) := by
      calc ∑ p ∈ range N, (if p < q ^ 2 then progressionChebyshevTerm q p else 0)
          ≤ ∑ p ∈ range (q ^ 2), progressionChebyshevTerm q p := by
            rw [← Finset.sum_filter]
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro p hp
              exact mem_range.mpr (mem_filter.mp hp).2
            · intro p _ _
              exact progressionChebyshevTerm_nonneg q p
        _ = progressionChebyshevPrefix q (q ^ 2) := rfl
    calc ∑ p ∈ range N, gaussianProgressionPrimeTerm q x p
        ≤ ∑ p ∈ range N, (W * (if p < q ^ 2 then progressionChebyshevTerm q p else 0) +
            gaussianAbelConstant * (b p * rationalSmoothingKernel x p)) :=
          sum_le_sum fun p _ => hterm p
      _ = W * ∑ p ∈ range N, (if p < q ^ 2 then progressionChebyshevTerm q p else 0) +
            gaussianAbelConstant * ∑ p ∈ range N, b p * rationalSmoothingKernel x p := by
          rw [sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ W * (((q : ℝ) + 1) * (2 * Real.log q)) +
            gaussianAbelConstant * ((C / ((q : ℝ) - 1)) * x + 0) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_left (hind.trans hsmall) hW0.le
          · exact mul_le_mul_of_nonneg_left hsmooth gaussianAbelConstant_pos.le
  have htsum := Real.tsum_le_of_sum_range_le (gaussianProgressionPrimeTerm_nonneg q x) hrange
  change gaussianProgressionPrimeTrace q x ≤ _ at htsum
  calc ((q : ℝ) - 1) * gaussianProgressionPrimeTrace q x
      ≤ ((q : ℝ) - 1) * (W * (((q : ℝ) + 1) * (2 * Real.log q)) +
          gaussianAbelConstant * ((C / ((q : ℝ) - 1)) * x + 0)) :=
        mul_le_mul_of_nonneg_left htsum hq1.le
    _ = gaussianAbelConstant * C * x + W * (((q : ℝ) ^ 2 - 1) * (2 * Real.log q)) := by
        have e : ((q : ℝ) - 1) * (C / ((q : ℝ) - 1)) = C := by
          field_simp
        rw [show ((q : ℝ) - 1) * (W * (((q : ℝ) + 1) * (2 * Real.log q)) +
            gaussianAbelConstant * ((C / ((q : ℝ) - 1)) * x + 0)) =
            gaussianAbelConstant * (((q : ℝ) - 1) * (C / ((q : ℝ) - 1))) * x +
              W * (((q : ℝ) ^ 2 - 1) * (2 * Real.log q)) by ring, e]
    _ ≤ gaussianAbelConstant * C * x + 2 * W * (q : ℝ) ^ 2 * Real.log q := by
        have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
        nlinarith [mul_nonneg hW0.le hlogq]

/-- **The cyclotomic trace up to `√x / log⁴ x`.** There is one constant `CE` such that, for
all large `x` and all primes `q ≤ √x / log⁴ x`, `Θ_{ℚ(ζ_q)}(x) ≤ CE x`. -/
theorem exists_cyclotomicGaussian_le_sqrtRange : ∃ CE : ℝ, 0 ≤ CE ∧
    ∀ᶠ x : ℝ in atTop, ∀ q : ℕ, ∀ hq : q.Prime, q ≤ grhCutoff x →
      letI : Fact q.Prime := ⟨hq⟩
      letI : NeZero q := ⟨hq.ne_zero⟩
      gaussianPrimePowerTrace (CyclotomicField q ℚ) x ≤ CE * x := by
  obtain ⟨C, hC, hAP⟩ := exists_progressionChebyshevUpperBound
  refine ⟨gaussianAbelConstant * C + 3, by nlinarith [gaussianAbelConstant_pos], ?_⟩
  set W : ℝ := Real.exp ((Real.log 2) ^ 2) with hW
  set E0 : ℝ := 8 * Real.exp ((Real.log 2) ^ 2 + 9 / 16) * Real.exp 1 with hE0
  -- Each error term is eventually at most `x`.
  have hL7 : Tendsto (fun x : ℝ => Real.log x ^ 7) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (7 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop
  have hL2 : Tendsto (fun x : ℝ => Real.log x ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop
  filter_upwards [hL7.eventually_ge_atTop (2 * W), hL2.eventually_ge_atTop E0,
    eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (2 : ℝ)] with x hx7 hx2 hxe hx2'
  intro q hq hcut
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  let : IsGalois ℚ (CyclotomicField q ℚ) := IsCyclotomicExtension.isGalois {q} ℚ _
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ Real.log x := one_le_log_of_exp_one_le hxe
  have hL : 0 < Real.log x := by linarith
  have hLne : Real.log x ≠ 0 := hL.ne'
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.two_le
  have hsqrt0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  have hqcut : (q : ℝ) ≤ Real.sqrt x / Real.log x ^ 4 :=
    (by exact_mod_cast hcut : (q : ℝ) ≤ grhCutoff x).trans (Nat.floor_le (by positivity))
  have hL4 : 0 < Real.log x ^ 4 := by positivity
  have hqsqrt : (q : ℝ) ≤ Real.sqrt x := by
    refine hqcut.trans ?_
    apply div_le_self hsqrt0
    exact one_le_pow₀ hL1
  have hq2x : (q : ℝ) ^ 2 ≤ x / Real.log x ^ 8 := by
    have h := pow_le_pow_left₀ (by positivity) hqcut 2
    calc (q : ℝ) ^ 2 ≤ (Real.sqrt x / Real.log x ^ 4) ^ 2 := h
      _ = x / Real.log x ^ 8 := by
          rw [div_pow, sq (Real.sqrt x), hsq]
          ring
  have hlogq : Real.log q ≤ Real.log x := by
    calc Real.log q ≤ Real.log (Real.sqrt x) := Real.log_le_log (by linarith) hqsqrt
      _ = Real.log x / 2 := Real.log_sqrt hx0.le
      _ ≤ Real.log x := by linarith
  have hlogq0 : 0 ≤ Real.log q := Real.log_nonneg (by linarith)
  -- degree-one part
  have hprog := progressionTrace_le_split hC hAP hq (by linarith : (1 : ℝ) ≤ x)
  have hprog_err : 2 * W * (q : ℝ) ^ 2 * Real.log q ≤ x := by
    have hW0 : 0 < W := Real.exp_pos _
    calc 2 * W * (q : ℝ) ^ 2 * Real.log q ≤ 2 * W * (x / Real.log x ^ 8) * Real.log x := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hq2x (by positivity)) hlogq hlogq0
            (by positivity)
      _ = x * (2 * W / Real.log x ^ 7) := by
          field_simp
      _ ≤ x * 1 := by
          apply mul_le_mul_of_nonneg_left _ hx0.le
          rw [div_le_one (by positivity)]
          exact hx7
      _ = x := mul_one x
  -- ramified prime
  have hram := gaussianRamifiedTerm_le (q := q) hx0
  have hram_err : Real.exp ((Real.log 2) ^ 2 + 1 / 4) * (q : ℝ) ^ (2 : ℕ) / x ≤ x := by
    have hq2x' : (q : ℝ) ^ 2 ≤ x := hq2x.trans (div_le_self hx0.le (one_le_pow₀ hL1))
    have hc : Real.exp ((Real.log 2) ^ 2 + 1 / 4) ≤ x := by
      have : (Real.log 2) ^ 2 + 1 / 4 ≤ 1 := by
        have h2 := Real.log_two_lt_d9
        have h3 := Real.log_two_gt_d9
        nlinarith
      exact (Real.exp_le_exp.mpr this).trans hxe
    calc Real.exp ((Real.log 2) ^ 2 + 1 / 4) * (q : ℝ) ^ (2 : ℕ) / x
        ≤ Real.exp ((Real.log 2) ^ 2 + 1 / 4) * x / x := by
          apply div_le_div_of_nonneg_right _ hx0.le
          exact mul_le_mul_of_nonneg_left hq2x' (Real.exp_pos _).le
      _ = Real.exp ((Real.log 2) ^ 2 + 1 / 4) := by field_simp
      _ ≤ x := hc
  -- higher prime powers by Rankin
  have hhigh := gaussianHigherPrimePowerTrace_le_rankin (CyclotomicField q ℚ) hxe
  have hdeg : (Module.finrank ℚ (CyclotomicField q ℚ) : ℝ) ≤ Real.sqrt x / Real.log x ^ 4 := by
    rw [prime_cyclotomic_degree hq]
    have hsub : ((q - 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast Nat.sub_le q 1
    exact hsub.trans hqcut
  have hhigh_err : (Module.finrank ℚ (CyclotomicField q ℚ) : ℝ) * E0 *
      (Real.log x ^ 2 * Real.sqrt x) ≤ x := by
    have hE0pos : 0 ≤ E0 := by positivity
    calc (Module.finrank ℚ (CyclotomicField q ℚ) : ℝ) * E0 * (Real.log x ^ 2 * Real.sqrt x)
        ≤ (Real.sqrt x / Real.log x ^ 4) * E0 * (Real.log x ^ 2 * Real.sqrt x) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right hdeg hE0pos
      _ = x * (E0 / Real.log x ^ 2) := by
          rw [show (Real.sqrt x / Real.log x ^ 4) * E0 * (Real.log x ^ 2 * Real.sqrt x) =
            (Real.sqrt x * Real.sqrt x) * E0 / Real.log x ^ 2 by field_simp]
          rw [hsq]
          ring
      _ ≤ x * 1 := by
          apply mul_le_mul_of_nonneg_left _ hx0.le
          rw [div_le_one (by positivity)]
          exact hx2
      _ = x := mul_one x
  rw [gaussianCyclotomicFullTrace_eq q hx0]
  have h1 : ((q : ℝ) - 1) * gaussianProgressionPrimeTrace q x ≤
      gaussianAbelConstant * C * x + x := by linarith
  have h2 : Real.log q * artinGaussianWeight ((q : ℝ) / x) ≤ x := hram.trans hram_err
  have h3 : gaussianHigherPrimePowerTrace (CyclotomicField q ℚ) x ≤ x := hhigh.trans hhigh_err
  linarith

end
end SimultaneousPrimitiveRoots
