module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.Statements
public import SimultaneousPrimitiveRoots.Unconditional.Classical.DirichletMeanSquare

/-!
# The proved chain of the endpoint estimate (cor:SM)

This file proves, from the statements of `EndpointProof/Statements.lean`:

* `endpointEnergyPaper_of_bundled`: `EndpointEnergyBundled d → EndpointEnergyPaper d` (the bundled
  data are those of `EndpointEnergyAt`);
* `endpointEnergyBundled_of` (`[P-06:0555–0562, 0678–0679]`):
  `LowFrequencyBound d ∧ HighFrequencyBound d → EndpointEnergyBundled d`. The integral over
  `|τ| ≤ T₀` is split at `L^{B'}`; the low part is `≤ 2 L^{B'} (M L^{-N})²` with
  `N = (A + B')/2` ("Choosing `N` after `B'`");
* `highFrequencyBound_of` (`[P-06:0692–0715]`):
  `SlotMassBounded ∧ ScaleFacts ∧ ExtractionErrorBound ∧ TupleEnergy ∧ ConstantEnergy
    → HighFrequencyBound (d + 1)`. With `𝒰 = 𝒰_tuple - C_x 𝒰_const + 𝒰_err`,
  `|E|² ≤ 3 |E_tuple|² + 3 C_x² |E_const|² + 3 |E_err|²`; the error polynomial is integrated with
  the mean-value theorem `integral_normSq_dirichletPolynomial_le_nat`
  ("Lemma `lem:moment-bounds`, applied to these coefficient errors, makes their normalized
  integrated square over `|t| ≤ T_0` smaller than every negative log power", with
  `T_0 / Y = o(1)`);
* `endpointEnergy_succ_of_leaves`: `EndpointClassicalInputs → EndpointLeaves d →
  EndpointEnergy (d + 1)`, through `endpointEnergy_of_endpointEnergyPaper`.

The order of choices in `highFrequencyBound_of`: the saving `A`; the low-time exponents of the
tuple and constant parts, and `B'` their maximum; the precision `A + 1` of the extraction error;
the bound for `C_x`; the scale facts; `x` last.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open Filter
open scoped Topology ContDiff

noncomputable section

/-! ### Elementary inequalities -/

/-- `|a - C b + e|² ≤ 3|a|² + 3C²|b|² + 3|e|²` for `C ≥ 0`. -/
theorem norm_sq_le_three {z a b e : ℂ} {C : ℝ} (hC : 0 ≤ C) (hz : z = a - (C : ℂ) * b + e) :
    ‖z‖ ^ 2 ≤ 3 * ‖a‖ ^ 2 + 3 * C ^ 2 * ‖b‖ ^ 2 + 3 * ‖e‖ ^ 2 := by
  have hCb : ‖(C : ℂ) * b‖ = C * ‖b‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hC]
  have h1 : ‖z‖ ≤ ‖a‖ + C * ‖b‖ + ‖e‖ := by
    have h2 : ‖a - (C : ℂ) * b + e‖ ≤ ‖a - (C : ℂ) * b‖ + ‖e‖ := norm_add_le _ _
    have h3 : ‖a - (C : ℂ) * b‖ ≤ ‖a‖ + ‖(C : ℂ) * b‖ := norm_sub_le _ _
    rw [hCb] at h3
    rw [hz]
    linarith
  have h2 : ‖z‖ ^ 2 ≤ (‖a‖ + C * ‖b‖ + ‖e‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖a‖ - C * ‖b‖), sq_nonneg (‖a‖ - ‖e‖), sq_nonneg (C * ‖b‖ - ‖e‖)]

/-- The integral of `f` over `[-T, T]`, from a pointwise bound `m` on `|τ| ≤ b` and a bound `H`
for the integral over every interval of `{b ≤ |τ| ≤ T}`. No relation between `b` and `T` is
assumed. -/
theorem integral_le_of_low_high {f : ℝ → ℝ} (hf : Continuous f) {T b m H : ℝ} (hT : 0 ≤ T)
    (hb : 0 ≤ b) (hlow : ∀ τ : ℝ, |τ| ≤ b → f τ ≤ m) (hm : 0 ≤ m)
    (hhigh : ∀ a a' : ℝ, a ≤ a' → ((b ≤ a ∧ a' ≤ T) ∨ (-T ≤ a ∧ a' ≤ -b)) →
      ∫ τ in a..a', f τ ≤ H) :
    ∫ τ in (-T)..T, f τ ≤ 2 * |H| + 2 * b * m := by
  have hint : ∀ a a' : ℝ, IntervalIntegrable f MeasureTheory.volume a a' :=
    fun a a' => hf.intervalIntegrable a a'
  have hcm : ∀ a a' : ℝ, IntervalIntegrable (fun _ : ℝ => m) MeasureTheory.volume a a' :=
    fun a a' => continuous_const.intervalIntegrable a a'
  have hH : H ≤ |H| := le_abs_self H
  have hH0 : 0 ≤ |H| := abs_nonneg H
  by_cases hbT : b ≤ T
  · have h1 : ∫ τ in (-T)..(-b), f τ ≤ H :=
      hhigh (-T) (-b) (neg_le_neg hbT) (Or.inr ⟨le_refl _, le_refl _⟩)
    have h3 : ∫ τ in b..T, f τ ≤ H := hhigh b T hbT (Or.inl ⟨le_refl _, le_refl _⟩)
    have h2 : ∫ τ in (-b)..b, f τ ≤ 2 * b * m := by
      have hle : ∫ τ in (-b)..b, f τ ≤ ∫ _τ in (-b)..b, m :=
        intervalIntegral.integral_mono_on (by linarith) (hint _ _) (hcm _ _)
          (fun τ hτ => hlow τ (abs_le.mpr ⟨hτ.1, hτ.2⟩))
      rw [intervalIntegral.integral_const, smul_eq_mul] at hle
      have e : (b - -b) * m = 2 * b * m := by ring
      rw [e] at hle
      exact hle
    have hsplit : ∫ τ in (-T)..T, f τ =
        (∫ τ in (-T)..(-b), f τ) + (∫ τ in (-b)..b, f τ) + ∫ τ in b..T, f τ := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
        intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
    rw [hsplit]
    linarith
  · have hTb : T ≤ b := (not_le.mp hbT).le
    have hle : ∫ τ in (-T)..T, f τ ≤ ∫ _τ in (-T)..T, m :=
      intervalIntegral.integral_mono_on (by linarith) (hint _ _) (hcm _ _)
        (fun τ hτ => hlow τ (abs_le.mpr ⟨by linarith [hτ.1], by linarith [hτ.2]⟩))
    rw [intervalIntegral.integral_const, smul_eq_mul] at hle
    have e : (T - -T) * m = 2 * T * m := by ring
    rw [e] at hle
    have h4 : 2 * T * m ≤ 2 * b * m := mul_le_mul_of_nonneg_right (by linarith) hm
    linarith

/-- Integration of a pointwise bound by three terms. -/
theorem integral_three_le {f g₁ g₂ g₃ : ℝ → ℝ} (hf : Continuous f) (h₁ : Continuous g₁)
    (h₂ : Continuous g₂) (h₃ : Continuous g₃) {a b : ℝ} (hab : a ≤ b) {c₂ : ℝ}
    (hle : ∀ τ : ℝ, f τ ≤ 3 * g₁ τ + c₂ * g₂ τ + 3 * g₃ τ) :
    ∫ τ in a..b, f τ ≤
      3 * (∫ τ in a..b, g₁ τ) + c₂ * (∫ τ in a..b, g₂ τ) + 3 * ∫ τ in a..b, g₃ τ := by
  have hi₁ : IntervalIntegrable (fun τ => 3 * g₁ τ) MeasureTheory.volume a b :=
    (continuous_const.mul h₁).intervalIntegrable a b
  have hi₂ : IntervalIntegrable (fun τ => c₂ * g₂ τ) MeasureTheory.volume a b :=
    (continuous_const.mul h₂).intervalIntegrable a b
  have hi₃ : IntervalIntegrable (fun τ => 3 * g₃ τ) MeasureTheory.volume a b :=
    (continuous_const.mul h₃).intervalIntegrable a b
  have hi₁₂ : IntervalIntegrable (fun τ => 3 * g₁ τ + c₂ * g₂ τ) MeasureTheory.volume a b :=
    hi₁.add hi₂
  have hi : IntervalIntegrable (fun τ => 3 * g₁ τ + c₂ * g₂ τ + 3 * g₃ τ)
      MeasureTheory.volume a b := hi₁₂.add hi₃
  have e₁ : ∫ τ in a..b, (3 * g₁ τ + c₂ * g₂ τ + 3 * g₃ τ) =
      (∫ τ in a..b, (3 * g₁ τ + c₂ * g₂ τ)) + ∫ τ in a..b, 3 * g₃ τ :=
    intervalIntegral.integral_add hi₁₂ hi₃
  have e₂ : ∫ τ in a..b, (3 * g₁ τ + c₂ * g₂ τ) =
      (∫ τ in a..b, 3 * g₁ τ) + ∫ τ in a..b, c₂ * g₂ τ :=
    intervalIntegral.integral_add hi₁ hi₂
  have e₃ : ∫ τ in a..b, 3 * g₁ τ = 3 * ∫ τ in a..b, g₁ τ :=
    intervalIntegral.integral_const_mul 3 g₁
  have e₄ : ∫ τ in a..b, c₂ * g₂ τ = c₂ * ∫ τ in a..b, g₂ τ :=
    intervalIntegral.integral_const_mul c₂ g₂
  have e₅ : ∫ τ in a..b, 3 * g₃ τ = 3 * ∫ τ in a..b, g₃ τ :=
    intervalIntegral.integral_const_mul 3 g₃
  have hmono : ∫ τ in a..b, f τ ≤ ∫ τ in a..b, (3 * g₁ τ + c₂ * g₂ τ + 3 * g₃ τ) :=
    intervalIntegral.integral_mono_on hab (hf.intervalIntegrable a b) hi (fun τ _ => hle τ)
  rw [e₁, e₂, e₃, e₄, e₅] at hmono
  exact hmono

/-! ### The endpoint polynomial as a finite Dirichlet polynomial -/

/-- `|e(θ)| = 1`. -/
theorem norm_addChar (θ : ℝ) : ‖addChar θ‖ = 1 := by
  unfold addChar
  have h : 2 * (Real.pi : ℂ) * (θ : ℂ) * Complex.I =
      ((2 * Real.pi * θ : ℝ) : ℂ) * Complex.I := by
    rw [Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_ofNat]
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- The endpoint polynomial of a sequence supported in a finite set is a finite sum. -/
theorem endpointPolynomial_eq_sum {U : ℕ → ℂ} {s : Finset ℕ} (hs : ∀ w, U w ≠ 0 → w ∈ s)
    (Y : ℝ) (h : ℤ) (k : ℕ) (τ : ℝ) :
    endpointPolynomial U Y h k τ = (Y : ℂ)⁻¹ *
      ∑ w ∈ s, U w * addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) * (w : ℂ) ^ ((τ : ℂ) * Complex.I) := by
  have hsub : Function.support (fun w : ℕ => U w * addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) *
      (w : ℂ) ^ ((τ : ℂ) * Complex.I)) ⊆ ↑s := by
    intro w hw
    rw [Function.mem_support] at hw
    have hU : U w ≠ 0 := fun h' => hw (by rw [h', zero_mul, zero_mul])
    exact Finset.mem_coe.mpr (hs w hU)
  unfold endpointPolynomial
  rw [finsum_eq_sum_of_support_subset _ hsub]

/-- Continuity in the time of the squared modulus of an endpoint polynomial. -/
theorem continuous_normSq_endpointPolynomial {U : ℕ → ℂ} {N : ℕ}
    (hU : ∀ w, U w ≠ 0 → w ∈ Finset.Icc 1 N) (Y : ℝ) (h : ℤ) (k : ℕ) :
    Continuous fun τ : ℝ => ‖endpointPolynomial U Y h k τ‖ ^ 2 := by
  have h0 : U 0 = 0 := by
    by_contra h'
    have h1 := (Finset.mem_Icc.mp (hU 0 h')).1
    omega
  exact (continuous_endpointPolynomial hU h0 Y h k).norm.pow 2

/-- Linearity of the endpoint polynomial in the sequence, in the form used for
`𝒰 = 𝒰_tuple - C_x 𝒰_const + 𝒰_err`. -/
theorem endpointPolynomial_decomp {U T Kc E : ℕ → ℂ} {s : Finset ℕ} {C : ℂ}
    (hU : ∀ w, U w ≠ 0 → w ∈ s) (hT : ∀ w, T w ≠ 0 → w ∈ s) (hK : ∀ w, Kc w ≠ 0 → w ∈ s)
    (hE : ∀ w, E w ≠ 0 → w ∈ s) (hUeq : ∀ w, U w = T w - C * Kc w + E w)
    (Y : ℝ) (h : ℤ) (k : ℕ) (τ : ℝ) :
    endpointPolynomial U Y h k τ = endpointPolynomial T Y h k τ -
      C * endpointPolynomial Kc Y h k τ + endpointPolynomial E Y h k τ := by
  rw [endpointPolynomial_eq_sum hU, endpointPolynomial_eq_sum hT, endpointPolynomial_eq_sum hK,
    endpointPolynomial_eq_sum hE]
  have hsum : ∑ w ∈ s, U w * addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) *
        (w : ℂ) ^ ((τ : ℂ) * Complex.I) =
      (∑ w ∈ s, T w * addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) * (w : ℂ) ^ ((τ : ℂ) * Complex.I) -
        C * ∑ w ∈ s, Kc w * addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) *
          (w : ℂ) ^ ((τ : ℂ) * Complex.I)) +
        ∑ w ∈ s, E w * addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) *
          (w : ℂ) ^ ((τ : ℂ) * Complex.I) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hUeq w]
    ring
  rw [hsum]
  ring

/-- **The mean-value theorem for an endpoint polynomial** (eq:dirichlet-mean of
`lem:moment-bounds`, `[P-02:0081–0085]`, in the explicit form
`integral_normSq_dirichletPolynomial_le_nat`): for a sequence supported on `1 ≤ w ≤ N`,
`∫_a^b |Y^{-1} ∑_w U(w) e(hw/k) w^{iτ}|² dτ ≤ Y^{-2} (b - a + 4N(1 + log N)) ∑_w |U(w)|²`. -/
theorem endpointPolynomial_energy_le {U : ℕ → ℂ} {N : ℕ}
    (hU : ∀ w, U w ≠ 0 → w ∈ Finset.Icc 1 N) (Y : ℝ) (h : ℤ) (k : ℕ) {a b : ℝ} (hab : a ≤ b) :
    ∫ τ in a..b, ‖endpointPolynomial U Y h k τ‖ ^ 2 ≤
      (Y ^ 2)⁻¹ * (((b - a) + 4 * (N : ℝ) * (1 + Real.log (N : ℝ))) *
        ∑ n ∈ Finset.Icc 1 N, ‖U n‖ ^ 2) := by
  have hnorm : ∀ τ : ℝ, ‖endpointPolynomial U Y h k τ‖ ^ 2 = (Y ^ 2)⁻¹ *
      ‖SimultaneousPrimitiveRoots.Unconditional.Classical.dirichletPolynomial
        (fun n => U n * addChar ((h : ℝ) * (n : ℝ) / (k : ℝ))) N τ‖ ^ 2 := by
    intro τ
    have hpoly : endpointPolynomial U Y h k τ = (Y : ℂ)⁻¹ *
        SimultaneousPrimitiveRoots.Unconditional.Classical.dirichletPolynomial
          (fun n => U n * addChar ((h : ℝ) * (n : ℝ) / (k : ℝ))) N τ := by
      rw [endpointPolynomial_eq_sum hU Y h k τ]
      unfold SimultaneousPrimitiveRoots.Unconditional.Classical.dirichletPolynomial
      congr 1
      exact Finset.sum_congr rfl fun n _ => by rw [mul_comm Complex.I (τ : ℂ)]
    rw [hpoly, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, mul_pow, inv_pow, sq_abs]
  have hcoef : ∑ n ∈ Finset.Icc 1 N, ‖U n * addChar ((h : ℝ) * (n : ℝ) / (k : ℝ))‖ ^ 2 =
      ∑ n ∈ Finset.Icc 1 N, ‖U n‖ ^ 2 :=
    Finset.sum_congr rfl fun n _ => by rw [norm_mul, norm_addChar, mul_one]
  have hmv : ∫ τ in a..b,
      ‖SimultaneousPrimitiveRoots.Unconditional.Classical.dirichletPolynomial
        (fun n => U n * addChar ((h : ℝ) * (n : ℝ) / (k : ℝ))) N τ‖ ^ 2 ≤
      ((b - a) + 4 * (N : ℝ) * (1 + Real.log (N : ℝ))) *
        ∑ n ∈ Finset.Icc 1 N, ‖U n * addChar ((h : ℝ) * (n : ℝ) / (k : ℝ))‖ ^ 2 :=
    SimultaneousPrimitiveRoots.Unconditional.Classical.integral_normSq_dirichletPolynomial_le_nat
      _ N hab
  rw [hcoef] at hmv
  have hfun : (fun τ : ℝ => ‖endpointPolynomial U Y h k τ‖ ^ 2) = fun τ : ℝ => (Y ^ 2)⁻¹ *
      ‖SimultaneousPrimitiveRoots.Unconditional.Classical.dirichletPolynomial
        (fun n => U n * addChar ((h : ℝ) * (n : ℝ) / (k : ℝ))) N τ‖ ^ 2 := funext hnorm
  calc ∫ τ in a..b, ‖endpointPolynomial U Y h k τ‖ ^ 2
      = ∫ τ in a..b, (Y ^ 2)⁻¹ *
          ‖SimultaneousPrimitiveRoots.Unconditional.Classical.dirichletPolynomial
            (fun n => U n * addChar ((h : ℝ) * (n : ℝ) / (k : ℝ))) N τ‖ ^ 2 :=
        congrArg (fun g : ℝ → ℝ => ∫ τ in a..b, g τ) hfun
    _ = (Y ^ 2)⁻¹ * ∫ τ in a..b,
          ‖SimultaneousPrimitiveRoots.Unconditional.Classical.dirichletPolynomial
            (fun n => U n * addChar ((h : ℝ) * (n : ℝ) / (k : ℝ))) N τ‖ ^ 2 :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ (Y ^ 2)⁻¹ * (((b - a) + 4 * (N : ℝ) * (1 + Real.log (N : ℝ))) *
          ∑ n ∈ Finset.Icc 1 N, ‖U n‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hmv (inv_nonneg.mpr (sq_nonneg Y))

/-- `HighEnergyLe` is monotone in the lower limit. -/
theorem HighEnergyLe.mono_lo {E : ℝ → ℂ} {lo lo' hi bound : ℝ} (h : HighEnergyLe E lo hi bound)
    (hlo : lo ≤ lo') : HighEnergyLe E lo' hi bound := by
  intro a b hab hr
  refine h a b hab ?_
  rcases hr with hr | hr
  · exact Or.inl ⟨hlo.trans hr.1, hr.2⟩
  · exact Or.inr ⟨hr.1, hr.2.trans (neg_le_neg hlo)⟩

/-! ### The bundled statement -/

/-- **The bundled (cor:SM) is [P]'s (cor:SM)**: `EndpointEnergyBundled d` is
`∀ C₆ > 0, EndpointEnergyAt d C₆ (C₆ + 1)` with the fixed data collected in `EndpointData` and
the varying data in `EndpointConfig`. -/
theorem endpointEnergyPaper_of_bundled {d : ℕ} (hB : EndpointEnergyBundled d) :
    EndpointEnergyPaper d := by
  intro C₆ hC₆ ε hε q q₀ hq hq1 hq₀ hq₀1 K 𝔞 P m' a₁ a₂ ha₁ ha₁₂ Dψ Cσ c₁ c₂ A hA
  obtain ⟨M, x₀, hM⟩ := hB
    { ε := ε, q := q, q₀ := q₀, K := K, 𝔞 := 𝔞, P := P, m' := m', a₁ := a₁, a₂ := a₂, Dψ := Dψ,
      Cσ := Cσ, c₁ := c₁, c₂ := c₂, C₆ := C₆, ε_pos := hε, q_pos := hq, q_lt_one := hq1,
      q₀_pos := hq₀, q₀_lt_one := hq₀1, a₁_pos := ha₁, a₁_le_a₂ := ha₁₂, C₆_pos := hC₆ } A hA
  refine ⟨M, x₀, ?_⟩
  intro x hx 𝔊 h𝔊 S hS Y hY1 hY2 t ht ht1 test htest hbig σ hσ ψ₁ hψ hsupp hder k hk hkL h
  exact hM x hx ⟨𝔊, S, Y, t, test, σ, ψ₁⟩
    { groups := h𝔊, slots := hS, scale_ge := hY1, scale_le := hY2, marks := ht,
      smallMarks := ht1, test_le := htest, test_big := hbig, twist := hσ, cutoff_smooth := hψ,
      cutoff_support := hsupp, cutoff_deriv := hder } k hk hkL h

/-! ### Low and high frequencies -/

/-- **(cor:SM) from the two ranges of times** (`[P-06:0555–0562, 0678–0679]`). -/
theorem endpointEnergyBundled_of {d : ℕ} (hLow : LowFrequencyBound d)
    (hHigh : HighFrequencyBound d) : EndpointEnergyBundled d := by
  intro D A hA
  obtain ⟨B', hB', M₂, x₂, hM₂⟩ := hHigh D A hA
  obtain ⟨M₁, x₁, hM₁⟩ := hLow D B' ((A + B') / 2) hB' (by linarith)
  refine ⟨2 * |M₂| + 2 * M₁ ^ 2, max (max x₁ x₂) (Real.exp 1), ?_⟩
  intro x hx c hc k hk hkL h
  have hx₁ : x₁ ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hx₂ : x₂ ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hxe : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hxe
  have hL1 : 1 ≤ Real.log x := by
    have h1 := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at h1
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  have hY : 0 < c.Y := lt_of_lt_of_le (mul_pos hx0 (Real.exp_pos _)) hc.scale_ge
  have hsE : ∀ w, c.endpoint D x w ≠ 0 → w ∈ Finset.Icc 1 ⌊D.a₂ * c.Y⌋₊ :=
    fun w hw => cutoff_mem D.a₁_pos hc.cutoff_support hY (fun h' => hw (c.endpoint_eq_zero D x h'))
  have hcont : Continuous fun τ : ℝ => ‖endpointPolynomial (c.endpoint D x) c.Y h k τ‖ ^ 2 :=
    continuous_normSq_endpointPolynomial hsE c.Y h k
  have hT0 : 0 ≤ timeBound D x := mul_nonneg hx0.le (Real.rpow_nonneg hL0.le _)
  have hb0 : 0 ≤ Real.log x ^ B' := Real.rpow_nonneg hL0.le _
  have hLA0 : 0 ≤ Real.log x ^ (-A) := Real.rpow_nonneg hL0.le _
  have hlow : ∀ τ : ℝ, |τ| ≤ Real.log x ^ B' →
      ‖endpointPolynomial (c.endpoint D x) c.Y h k τ‖ ^ 2 ≤
        (M₁ * Real.log x ^ (-((A + B') / 2))) ^ 2 :=
    fun τ hτ => pow_le_pow_left₀ (norm_nonneg _) (hM₁ x hx₁ c hc k hk hkL h τ hτ) 2
  have hhigh : ∀ a a' : ℝ, a ≤ a' →
      ((Real.log x ^ B' ≤ a ∧ a' ≤ timeBound D x) ∨
        (-timeBound D x ≤ a ∧ a' ≤ -Real.log x ^ B')) →
      ∫ τ in a..a', ‖endpointPolynomial (c.endpoint D x) c.Y h k τ‖ ^ 2 ≤
        M₂ * Real.log x ^ (-A) :=
    fun a a' haa hr => hM₂ x hx₂ c hc k hk hkL h a a' haa hr
  have hmain : ∫ τ in (-(timeBound D x))..(timeBound D x),
      ‖endpointPolynomial (c.endpoint D x) c.Y h k τ‖ ^ 2 ≤
        2 * |M₂ * Real.log x ^ (-A)| +
          2 * Real.log x ^ B' * (M₁ * Real.log x ^ (-((A + B') / 2))) ^ 2 :=
    integral_le_of_low_high hcont hT0 hb0 hlow (sq_nonneg _) hhigh
  have hpow : Real.log x ^ B' * (Real.log x ^ (-((A + B') / 2))) ^ 2 = Real.log x ^ (-A) := by
    rw [pow_two, ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    congr 1
    ring
  calc ∫ τ in (-(timeBound D x))..(timeBound D x),
        ‖endpointPolynomial (c.endpoint D x) c.Y h k τ‖ ^ 2
      ≤ 2 * |M₂ * Real.log x ^ (-A)| +
          2 * Real.log x ^ B' * (M₁ * Real.log x ^ (-((A + B') / 2))) ^ 2 := hmain
    _ = 2 * (|M₂| * Real.log x ^ (-A)) +
          2 * M₁ ^ 2 * (Real.log x ^ B' * (Real.log x ^ (-((A + B') / 2))) ^ 2) := by
        rw [abs_mul, abs_of_nonneg hLA0, mul_pow]
        ring
    _ = (2 * |M₂| + 2 * M₁ ^ 2) * Real.log x ^ (-A) := by
        rw [hpow]
        ring

/-- **The high frequencies from the extraction** (`[P-06:0692–0715]`): the endpoint is the tuple
part minus `C_x` times the constant part plus the coefficient error; the error is integrated with
the mean-value theorem. -/
theorem highFrequencyBound_of {d : ℕ} (hS : SlotMassBounded (d + 1)) (hSc : ScaleFacts)
    (hErr : ExtractionErrorBound d) (hT : TupleEnergy d) (hC : ConstantEnergy d) :
    HighFrequencyBound (d + 1) := by
  intro D A hA
  obtain ⟨Bt, hBt, Mt, xt, hMt⟩ := hT D A hA
  obtain ⟨Bc, _, Mc, xc, hMc⟩ := hC D A hA
  obtain ⟨Me, xe, hMe⟩ := hErr D (A + 1) (by linarith)
  obtain ⟨Bs, xs, hBs⟩ := hS D.ε D.ε_pos
  obtain ⟨Cs, xz, hCs⟩ := hSc D
  refine ⟨max Bt Bc, lt_max_of_lt_left hBt,
    3 * Mt + 3 * Bs ^ 2 * Mc + 3 * ((2 + |Cs|) * |Me|),
    max (max xt xc) (max (max xe xs) xz), ?_⟩
  intro x hx c hc k hk hkL h a b hab hrange
  have hxt : xt ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxc : xc ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hxe : xe ≤ x :=
    (((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hx
  have hxs : xs ≤ x :=
    (((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)).trans hx
  have hxz : xz ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  obtain ⟨hL1, hY, hTY, hN⟩ := hCs x hxz c.Y hc.scale_ge hc.scale_le
  have hL0 : 0 < Real.log x := lt_trans one_pos hL1
  have hLle : 1 ≤ Real.log x := hL1.le
  -- a small group exists
  have hsmall : 0 < c.𝔊.numSmall := by
    have h1 : 0 < D.P.c₀ * Real.log (Real.log x) := mul_pos D.P.c₀_pos (Real.log_pos hL1)
    have h2 : (0 : ℝ) < (c.𝔊.numSmall : ℝ) := lt_of_lt_of_le h1 hc.groups.numSmall_ge
    exact Nat.cast_pos.mp h2
  obtain ⟨i₀⟩ : Nonempty (Fin c.𝔊.numSmall) := ⟨⟨0, hsmall⟩⟩
  -- supports
  have hmem : ∀ w : ℕ, c.ψ₁ ((w : ℝ) / c.Y) ≠ 0 → w ∈ Finset.Icc 1 ⌊D.a₂ * c.Y⌋₊ :=
    fun w hw => cutoff_mem D.a₁_pos hc.cutoff_support hY hw
  have hsE : ∀ w, c.endpoint D x w ≠ 0 → w ∈ Finset.Icc 1 ⌊D.a₂ * c.Y⌋₊ :=
    fun w hw => hmem w (fun h' => hw (c.endpoint_eq_zero D x h'))
  have hsT : ∀ w, c.tupleEndpoint D x i₀ w ≠ 0 → w ∈ Finset.Icc 1 ⌊D.a₂ * c.Y⌋₊ :=
    fun w hw => hmem w (fun h' => hw (c.tupleEndpoint_eq_zero D x i₀ h'))
  have hsC : ∀ w, c.constEndpoint D x i₀ w ≠ 0 → w ∈ Finset.Icc 1 ⌊D.a₂ * c.Y⌋₊ :=
    fun w hw => hmem w (fun h' => hw (c.constEndpoint_eq_zero D x i₀ h'))
  have hsR : ∀ w, c.errEndpoint D x i₀ w ≠ 0 → w ∈ Finset.Icc 1 ⌊D.a₂ * c.Y⌋₊ :=
    fun w hw => hmem w (fun h' => hw (c.errEndpoint_eq_zero D x i₀ h'))
  -- the decomposition of the polynomial and its square
  have hCx0 : 0 ≤ slotMass c.S := slotMass_nonneg c.S
  have hCxB : slotMass c.S ≤ Bs := hBs x hxs c.S hc.slots
  have hpt : ∀ τ : ℝ, ‖endpointPolynomial (c.endpoint D x) c.Y h k τ‖ ^ 2 ≤
      3 * ‖endpointPolynomial (c.tupleEndpoint D x i₀) c.Y h k τ‖ ^ 2 +
        3 * slotMass c.S ^ 2 * ‖endpointPolynomial (c.constEndpoint D x i₀) c.Y h k τ‖ ^ 2 +
        3 * ‖endpointPolynomial (c.errEndpoint D x i₀) c.Y h k τ‖ ^ 2 :=
    fun τ => norm_sq_le_three hCx0
      (endpointPolynomial_decomp hsE hsT hsC hsR (fun w => c.endpoint_eq D x i₀ w) c.Y h k τ)
  have hint : ∫ τ in a..b, ‖endpointPolynomial (c.endpoint D x) c.Y h k τ‖ ^ 2 ≤
      3 * (∫ τ in a..b, ‖endpointPolynomial (c.tupleEndpoint D x i₀) c.Y h k τ‖ ^ 2) +
        3 * slotMass c.S ^ 2 *
          (∫ τ in a..b, ‖endpointPolynomial (c.constEndpoint D x i₀) c.Y h k τ‖ ^ 2) +
        3 * ∫ τ in a..b, ‖endpointPolynomial (c.errEndpoint D x i₀) c.Y h k τ‖ ^ 2 :=
    integral_three_le (continuous_normSq_endpointPolynomial hsE c.Y h k)
      (continuous_normSq_endpointPolynomial hsT c.Y h k)
      (continuous_normSq_endpointPolynomial hsC c.Y h k)
      (continuous_normSq_endpointPolynomial hsR c.Y h k) hab hpt
  -- the ranges of times
  have hlo0 : 0 ≤ Real.log x ^ max Bt Bc := Real.rpow_nonneg hL0.le _
  have hlet : Real.log x ^ Bt ≤ Real.log x ^ max Bt Bc :=
    Real.rpow_le_rpow_of_exponent_le hLle (le_max_left _ _)
  have hlec : Real.log x ^ Bc ≤ Real.log x ^ max Bt Bc :=
    Real.rpow_le_rpow_of_exponent_le hLle (le_max_right _ _)
  have hrt : (Real.log x ^ Bt ≤ a ∧ b ≤ timeBound D x) ∨
      (-timeBound D x ≤ a ∧ b ≤ -Real.log x ^ Bt) := by
    rcases hrange with hr | hr
    · exact Or.inl ⟨hlet.trans hr.1, hr.2⟩
    · exact Or.inr ⟨hr.1, hr.2.trans (neg_le_neg hlet)⟩
  have hrc : (Real.log x ^ Bc ≤ a ∧ b ≤ timeBound D x) ∨
      (-timeBound D x ≤ a ∧ b ≤ -Real.log x ^ Bc) := by
    rcases hrange with hr | hr
    · exact Or.inl ⟨hlec.trans hr.1, hr.2⟩
    · exact Or.inr ⟨hr.1, hr.2.trans (neg_le_neg hlec)⟩
  -- the tuple and constant parts
  have hIt : ∫ τ in a..b, ‖endpointPolynomial (c.tupleEndpoint D x i₀) c.Y h k τ‖ ^ 2 ≤
      Mt * Real.log x ^ (-A) := hMt x hxt c hc i₀ k hk hkL h a b hab hrt
  have hIc : ∫ τ in a..b, ‖endpointPolynomial (c.constEndpoint D x i₀) c.Y h k τ‖ ^ 2 ≤
      Mc * Real.log x ^ (-A) := hMc x hxc c hc i₀ k hk hkL h a b hab hrc
  have hIc0 : 0 ≤ ∫ τ in a..b, ‖endpointPolynomial (c.constEndpoint D x i₀) c.Y h k τ‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab fun τ _ => sq_nonneg _
  -- the coefficient error, by the mean-value theorem
  have hIe : ∫ τ in a..b, ‖endpointPolynomial (c.errEndpoint D x i₀) c.Y h k τ‖ ^ 2 ≤
      (2 + |Cs|) * |Me| * Real.log x ^ (-A) := by
    have h1 : ∫ τ in a..b, ‖endpointPolynomial (c.errEndpoint D x i₀) c.Y h k τ‖ ^ 2 ≤
        (c.Y ^ 2)⁻¹ * (((b - a) + 4 * (⌊D.a₂ * c.Y⌋₊ : ℝ) *
          (1 + Real.log (⌊D.a₂ * c.Y⌋₊ : ℝ))) *
            ∑ w ∈ Finset.Icc 1 ⌊D.a₂ * c.Y⌋₊, ‖c.errEndpoint D x i₀ w‖ ^ 2) :=
      endpointPolynomial_energy_le hsR c.Y h k hab
    have hSig : ∑ w ∈ Finset.Icc 1 ⌊D.a₂ * c.Y⌋₊, ‖c.errEndpoint D x i₀ w‖ ^ 2 ≤
        Me * c.Y * Real.log x ^ (-(A + 1)) := hMe x hxe c hc i₀
    have hSig0 : 0 ≤ ∑ w ∈ Finset.Icc 1 ⌊D.a₂ * c.Y⌋₊, ‖c.errEndpoint D x i₀ w‖ ^ 2 :=
      Finset.sum_nonneg fun w _ => sq_nonneg _
    have hr0 : 0 ≤ Real.log x ^ (-(A + 1)) := Real.rpow_nonneg hL0.le _
    have hSig' : ∑ w ∈ Finset.Icc 1 ⌊D.a₂ * c.Y⌋₊, ‖c.errEndpoint D x i₀ w‖ ^ 2 ≤
        |Me| * c.Y * Real.log x ^ (-(A + 1)) :=
      hSig.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self Me) hY.le) hr0)
    have hba : b - a ≤ c.Y := by
      rcases hrange with hr | hr
      · linarith [hr.1, hr.2, hlo0, hTY]
      · linarith [hr.1, hr.2, hlo0, hTY]
    have hYL : c.Y ≤ c.Y * Real.log x := le_mul_of_one_le_right hY.le hLle
    have hYL0 : 0 ≤ c.Y * Real.log x := mul_nonneg hY.le hL0.le
    have hCsY : Cs * c.Y * Real.log x ≤ |Cs| * c.Y * Real.log x :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Cs) hY.le) hL0.le
    have hlen : (b - a) + 4 * (⌊D.a₂ * c.Y⌋₊ : ℝ) * (1 + Real.log (⌊D.a₂ * c.Y⌋₊ : ℝ)) ≤
        (2 + |Cs|) * c.Y * Real.log x := by
      have e1 : (2 + |Cs|) * c.Y * Real.log x =
          2 * (c.Y * Real.log x) + |Cs| * c.Y * Real.log x := by ring
      rw [e1]
      linarith
    have hbound0 : 0 ≤ (2 + |Cs|) * c.Y * Real.log x :=
      mul_nonneg (mul_nonneg (add_nonneg zero_le_two (abs_nonneg Cs)) hY.le) hL0.le
    have hprod : ((b - a) + 4 * (⌊D.a₂ * c.Y⌋₊ : ℝ) * (1 + Real.log (⌊D.a₂ * c.Y⌋₊ : ℝ))) *
          ∑ w ∈ Finset.Icc 1 ⌊D.a₂ * c.Y⌋₊, ‖c.errEndpoint D x i₀ w‖ ^ 2 ≤
        ((2 + |Cs|) * c.Y * Real.log x) * (|Me| * c.Y * Real.log x ^ (-(A + 1))) :=
      mul_le_mul hlen hSig' hSig0 hbound0
    have hYY : (c.Y ^ 2)⁻¹ * c.Y ^ 2 = 1 := inv_mul_cancel₀ (pow_ne_zero 2 hY.ne')
    have hLr : Real.log x * Real.log x ^ (-(A + 1)) = Real.log x ^ (-A) := by
      have e : (-A : ℝ) = 1 + -(A + 1) := by ring
      rw [e, Real.rpow_add hL0, Real.rpow_one]
    calc ∫ τ in a..b, ‖endpointPolynomial (c.errEndpoint D x i₀) c.Y h k τ‖ ^ 2
        ≤ (c.Y ^ 2)⁻¹ * (((b - a) + 4 * (⌊D.a₂ * c.Y⌋₊ : ℝ) *
            (1 + Real.log (⌊D.a₂ * c.Y⌋₊ : ℝ))) *
              ∑ w ∈ Finset.Icc 1 ⌊D.a₂ * c.Y⌋₊, ‖c.errEndpoint D x i₀ w‖ ^ 2) := h1
      _ ≤ (c.Y ^ 2)⁻¹ *
            (((2 + |Cs|) * c.Y * Real.log x) * (|Me| * c.Y * Real.log x ^ (-(A + 1)))) :=
          mul_le_mul_of_nonneg_left hprod (inv_nonneg.mpr (sq_nonneg _))
      _ = (2 + |Cs|) * |Me| * (Real.log x * Real.log x ^ (-(A + 1))) *
            ((c.Y ^ 2)⁻¹ * c.Y ^ 2) := by ring
      _ = (2 + |Cs|) * |Me| * Real.log x ^ (-A) := by rw [hYY, hLr, mul_one]
  -- the three parts together
  have hCx2 : slotMass c.S ^ 2 ≤ Bs ^ 2 := pow_le_pow_left₀ hCx0 hCxB 2
  have hBs2 : 0 ≤ 3 * Bs ^ 2 := mul_nonneg (by norm_num) (sq_nonneg Bs)
  have h2 : 3 * slotMass c.S ^ 2 *
        (∫ τ in a..b, ‖endpointPolynomial (c.constEndpoint D x i₀) c.Y h k τ‖ ^ 2) ≤
      3 * Bs ^ 2 * (Mc * Real.log x ^ (-A)) :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCx2 (by norm_num)) hIc0).trans
      (mul_le_mul_of_nonneg_left hIc hBs2)
  calc ∫ τ in a..b, ‖endpointPolynomial (c.endpoint D x) c.Y h k τ‖ ^ 2
      ≤ 3 * (∫ τ in a..b, ‖endpointPolynomial (c.tupleEndpoint D x i₀) c.Y h k τ‖ ^ 2) +
          3 * slotMass c.S ^ 2 *
            (∫ τ in a..b, ‖endpointPolynomial (c.constEndpoint D x i₀) c.Y h k τ‖ ^ 2) +
          3 * ∫ τ in a..b, ‖endpointPolynomial (c.errEndpoint D x i₀) c.Y h k τ‖ ^ 2 := hint
    _ ≤ 3 * (Mt * Real.log x ^ (-A)) + 3 * Bs ^ 2 * (Mc * Real.log x ^ (-A)) +
          3 * ((2 + |Cs|) * |Me| * Real.log x ^ (-A)) := by linarith
    _ = (3 * Mt + 3 * Bs ^ 2 * Mc + 3 * ((2 + |Cs|) * |Me|)) * Real.log x ^ (-A) := by ring

/-! ### The chain -/

/-- **(cor:SM) for `d + 1` slots from the classical inputs and the leaves**: the low frequencies
(`lowFrequency`), the extraction and the three energies at high frequencies
(`highFrequencyBound_of`), the split of the time integral (`endpointEnergyBundled_of`), and the
passage from [P]'s form to the form with independent exponents
(`endpointEnergy_of_endpointEnergyPaper`). -/
theorem endpointEnergy_succ_of_leaves {d : ℕ} (I : EndpointClassicalInputs)
    (L : EndpointLeaves d) : EndpointEnergy (d + 1) := by
  have hΩ : OmegaMoment := L.omegaMoment I.mertens
  have hDM : DivisorModel := L.divisorModel I.mertens hΩ
  have hLM : LowMainTerm := L.lowMainTerm I.smoothSum
  have hSM : SlotMassBounded (d + 1) := L.slotMass I.mertens
  have hLow : LowFrequencyBound (d + 1) := L.lowFrequency hDM hLM hSM
  have hMB : PartialMarkedBound := L.markedBound
  have hCB : CoefficientBound d := L.coefficientBound I.mertens hMB
  have hEI : ExtractedCoefficientIdentity d := L.extractedCoefficient L.extractSmall
  have hEE : ExtractionErrorBound d := L.extractionError hEI I.mertens hMB
  have hEC : ExceptionalCount := L.exceptionalCount L.primePowerNorm
  have hSB : SparseBound := L.sparseBound I.logPhase I.moderatePhase
  have hLP : LongPrimeSaving := L.longPrimeSaving I.longPrime
  have hTP : TupleProductBound := L.tupleProduct hEC hSB hLP
  have hTE : TupleEnergy d := L.tupleSeparation hCB hTP
  have hMM : ModelPolynomialMedium := L.modelMedium I.moderatePhase
  have hMH : ModelPolynomialHigh := L.modelHigh I.logPhase
  have hCP : ConstantProductBound d := L.constantProduct hCB hEC hDM hMM hMH
  have hCE : ConstantEnergy d := L.constantSeparation hCB hCP
  have hHigh : HighFrequencyBound (d + 1) := highFrequencyBound_of hSM L.scaleFacts hEE hTE hCE
  exact endpointEnergy_of_endpointEnergyPaper
    (endpointEnergyPaper_of_bundled (endpointEnergyBundled_of hLow hHigh))

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
