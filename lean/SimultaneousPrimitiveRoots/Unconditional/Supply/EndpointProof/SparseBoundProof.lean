module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.SparseGram
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ModelPolynomialsProof

/-!
# (cor:sparse-bound)

`sparseBound : LogPhase → ModeratePhase → SparseBound` (`[P-06:0803–0832]`): for
`x^δ ≤ R_0 ≤ x²`, arbitrary coefficients on `R_0 ≤ n ≤ ρ R_0`, and a set `𝒯` of reals
`|t| ≤ 2x³` with pairwise distances `≥ 1` and at most `2 exp(L^{.9})` elements,
`∑_{t ∈ 𝒯} |R(t)|² ≤ M L · R_0^{-1} ∑_n |c_n|²` for `R(t) = R_0^{-1} ∑ c_n n^{it}`.

"The Gram matrix of the vectors `(n^{it_i})_{n ≍ R_0}` consequently has absolute row sum
`≪ R_0 (1 + log(2T_0) + |𝒥| {x^{-c_ε} + exp(-L/(log L)^{C_{16}})}) ≪ R_0 L`. … The Gram operator
bound multiplied by `∑ |c_n|²` proves (cor:sparse-bound)."

* The Gram entry of `t ≠ t'` is the phase sum `∑_{R_0 ≤ n ≤ ρ R_0} n^{iΔ}`, `Δ = t - t'`,
  `1 ≤ |Δ| ≤ 4x³`. It is `R_0` times the normalized polynomial of the divisor model `A = 1_{e=1}`
  with the trivial progression (`k = 1`), so (cor:constant-medium) and (cor:constant-high)
  (`modelMedium`, `modelHigh`, with `Csupp = C₈ = 0`) give
  `≤ R_0 C (|Δ|^{-1} + x^{-c'} + exp(-L/(log L)^{C₃}))`.
* The diagonal entry is the number of integers of `[R_0, ρ R_0]`, at most `ρ R_0`.
* `∑_{t' ≠ t} 1/|t - t'| ≤ 2 (1 + log ⌈4x³⌉) ≤ 16 + 6L` (`sum_erase_inv_abs_sub_le`).
* `#𝒯 ≤ 2 exp(L^{.9})` absorbs the two small errors: `exp(L^{.9}) x^{-c'} ≤ 1` and
  `exp(L^{.9} - L/(log L)^{C₃}) ≤ 1` for large `x`. (This hypothesis is essential.)
* The Gram operator bound `sum_normSq_le_of_gram_row_sum_le` with row sum
  `R_0 (ρ + 26 C) L`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open Filter
open scoped Topology

noncomputable section

/-! ### The divisor model `1` -/

/-- The coefficients of the divisor model of the constant `1`: `A_1 = 1`, `A_e = 0` otherwise. -/
def unitModel (e : ℕ) : ℂ := if e = 1 then 1 else 0

theorem divisorSum_unitModel {n : ℕ} (hn : n ≠ 0) : divisorSum unitModel n = 1 := by
  unfold divisorSum unitModel
  exact Finset.sum_ite_eq_of_mem' n.divisors 1 (fun _ => (1 : ℂ)) (Nat.one_mem_divisors.mpr hn)

/-- The support condition of `ModelPolynomialMedium`/`High` with `Csupp = 0`. -/
theorem unitModel_support (x : ℝ) (k e : ℕ) (he : unitModel e ≠ 0) :
    0 < e ∧ (e : ℝ) ≤ Real.exp (0 * Real.log x ^ (0.47 : ℝ)) ∧ e.Coprime k := by
  have h1 : e = 1 := by
    by_contra h
    have h0 : unitModel e = 0 := by
      unfold unitModel
      exact if_neg h
    exact he h0
  rw [h1]
  refine ⟨Nat.one_pos, le_of_eq ?_, Nat.coprime_one_left k⟩
  rw [zero_mul, Real.exp_zero, Nat.cast_one]

/-- The mass condition of `ModelPolynomialMedium`/`High` with `Csupp = 0`, `C₈ = 0`. -/
theorem unitModel_mass (x : ℝ) :
    ∑ e ∈ Finset.Icc 1 ⌊Real.exp (0 * Real.log x ^ (0.47 : ℝ))⌋₊, ‖unitModel e‖ / (e : ℝ) ≤
      Real.log x ^ (0 : ℝ) := by
  have e1 : ⌊Real.exp (0 * Real.log x ^ (0.47 : ℝ))⌋₊ = 1 := by
    rw [zero_mul, Real.exp_zero, Nat.floor_one]
  have e2 : ‖unitModel 1‖ = 1 := by
    unfold unitModel
    rw [if_pos (rfl : (1 : ℕ) = 1), norm_one]
  refine le_of_eq ?_
  rw [e1, Finset.Icc_self, Finset.sum_singleton, Real.rpow_zero, e2, Nat.cast_one, div_one]

/-- The normalized phase sum is the polynomial of the divisor model `1` with the trivial
progression. -/
theorem normPoly_unitModel {R₀ R₁ : ℝ} (hR₀ : 0 < R₀) (t : ℝ) :
    normPoly R₀ (natIcc R₀ R₁)
        (fun n => if n ≡ 0 [MOD 1] then divisorSum unitModel n else 0) t =
      (R₀ : ℂ)⁻¹ * ∑ n ∈ natIcc R₀ R₁, (n : ℂ) ^ ((t : ℂ) * Complex.I) := by
  have hpoly : normPoly R₀ (natIcc R₀ R₁)
        (fun n => if n ≡ 0 [MOD 1] then divisorSum unitModel n else 0) t =
      (R₀ : ℂ)⁻¹ * ∑ n ∈ natIcc R₀ R₁,
        (if n ≡ 0 [MOD 1] then divisorSum unitModel n else 0) *
          (n : ℂ) ^ ((t : ℂ) * Complex.I) := rfl
  rw [hpoly]
  refine congrArg (fun y : ℂ => (R₀ : ℂ)⁻¹ * y) (Finset.sum_congr rfl fun n hn => ?_)
  have hn0 : n ≠ 0 := by
    intro h0
    have h := ((mem_natIcc_of_pos hR₀).mp hn).1
    rw [h0, Nat.cast_zero] at h
    exact absurd h (not_le.mpr hR₀)
  rw [if_pos (Nat.modEq_one : n ≡ 0 [MOD 1]), divisorSum_unitModel hn0, one_mul]

/-! ### The sparse bound -/

/-- **(cor:sparse-bound)** (`[P-06:0803–0832]`), from Lemma `lem:log-phase` and
(eq:moderate-phase) through the Gram operator bound. -/
theorem sparseBound : LogPhase → ModeratePhase → SparseBound := by
  intro hLP hMP δ ρ hδ hρ
  obtain ⟨c', M₁, x₁, hc', hmed⟩ := modelMedium hMP δ ρ 1 0 0 hδ hρ one_pos
  obtain ⟨C₁₉, M₂, x₂, hC₁₉, hhigh⟩ := modelHigh hLP δ ρ 1 0 0 hδ hρ one_pos
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = |M₁| + |M₂| := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  have hM₁C : M₁ ≤ C := by
    rw [hCdef]
    exact (le_abs_self M₁).trans (le_add_of_nonneg_right (abs_nonneg M₂))
  have hM₂C : M₂ ≤ C := by
    rw [hCdef]
    exact (le_abs_self M₂).trans (le_add_of_nonneg_left (abs_nonneg M₁))
  -- the thresholds
  have hpowL : ∀ r : ℝ, 0 < r → ∀ c : ℝ, ∀ᶠ x : ℝ in atTop, c ≤ Real.log x ^ r :=
    fun r hr c => ((tendsto_rpow_atTop hr).comp Real.tendsto_log_atTop).eventually_ge_atTop c
  have hr : (0 : ℝ) < 0.1 / C₁₉ := div_pos (by norm_num) hC₁₉
  have hLLo : ∀ᶠ x : ℝ in atTop,
      ‖Real.log (Real.log x)‖ ≤ 1 * ‖Real.log x ^ ((0.1 : ℝ) / C₁₉)‖ :=
    Real.tendsto_log_atTop.eventually ((isLittleO_log_rpow_atTop hr).def one_pos)
  have hev : ∀ᶠ x : ℝ in atTop, 3 ≤ Real.log x ∧ 1 / c' ≤ Real.log x ^ (0.1 : ℝ) ∧
      ‖Real.log (Real.log x)‖ ≤ 1 * ‖Real.log x ^ ((0.1 : ℝ) / C₁₉)‖ ∧ 1 < x := by
    filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 3,
      hpowL 0.1 (by norm_num) (1 / c'), hLLo, eventually_gt_atTop (1 : ℝ)] with x h1 h2 h3 h4
    exact ⟨h1, h2, h3, h4⟩
  obtain ⟨x₃, hx₃⟩ := Filter.eventually_atTop.mp hev
  refine ⟨ρ + 26 * C, max (max x₁ x₂) x₃, ?_⟩
  intro x hx R₀ hR₀ hR₀2 c 𝒯 hT hsep hcard𝒯
  have hxx₁ : x₁ ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxx₂ : x₂ ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hxx₃ : x₃ ≤ x := (le_max_right _ _).trans hx
  obtain ⟨hL3, h01, hLLn, hx1⟩ := hx₃ x hxx₃
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hL1 : 1 ≤ Real.log x := by linarith
  have hLL0 : 0 < Real.log (Real.log x) := Real.log_pos (by linarith)
  have hR₀pos : 0 < R₀ := lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 δ) hR₀
  have hρ0 : 0 < ρ := by linarith
  have hρR₀ : 0 < ρ * R₀ := mul_pos hρ0 hR₀pos
  have hk1 : ((1 : ℕ) : ℝ) ≤ Real.log x ^ (1 : ℝ) := by
    rw [Nat.cast_one, Real.rpow_one]
    exact hL1
  -- the two small errors and the bound for the cardinality
  obtain ⟨η₁, hη₁⟩ : ∃ η₁ : ℝ, η₁ = x ^ (-c') := ⟨_, rfl⟩
  obtain ⟨η₂, hη₂⟩ : ∃ η₂ : ℝ,
      η₂ = Real.exp (-Real.log x / Real.log (Real.log x) ^ C₁₉) := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = Real.exp (Real.log x ^ (0.9 : ℝ)) := ⟨_, rfl⟩
  have hη₁0 : 0 ≤ η₁ := by
    rw [hη₁]
    exact Real.rpow_nonneg hx0.le _
  have hη₂0 : 0 ≤ η₂ := by
    rw [hη₂]
    exact (Real.exp_pos _).le
  have hsplit : Real.log x ^ (0.9 : ℝ) * Real.log x ^ (0.1 : ℝ) = Real.log x := by
    rw [← Real.rpow_add hL0]
    have e : (0.9 : ℝ) + 0.1 = 1 := by norm_num
    rw [e, Real.rpow_one]
  have h9 : 0 ≤ Real.log x ^ (0.9 : ℝ) := Real.rpow_nonneg hL0.le _
  have hEη₁ : E * η₁ ≤ 1 := by
    rw [hE, hη₁, Real.rpow_def_of_pos hx0, ← Real.exp_add]
    refine (Real.exp_le_exp.mpr ?_).trans_eq Real.exp_zero
    have h1 : 1 ≤ Real.log x ^ (0.1 : ℝ) * c' := (div_le_iff₀ hc').mp h01
    have h2 : Real.log x ^ (0.9 : ℝ) * 1 ≤
        Real.log x ^ (0.9 : ℝ) * (Real.log x ^ (0.1 : ℝ) * c') :=
      mul_le_mul_of_nonneg_left h1 h9
    have h3 : Real.log x ^ (0.9 : ℝ) * (Real.log x ^ (0.1 : ℝ) * c') = Real.log x * c' := by
      rw [← mul_assoc, hsplit]
    linarith
  have hD : Real.log (Real.log x) ^ C₁₉ ≤ Real.log x ^ (0.1 : ℝ) := by
    have hp : 0 ≤ Real.log x ^ ((0.1 : ℝ) / C₁₉) := Real.rpow_nonneg hL0.le _
    have h1 : Real.log (Real.log x) ≤ Real.log x ^ ((0.1 : ℝ) / C₁₉) := by
      have h := hLLn
      rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hLL0, abs_of_nonneg hp] at h
      exact h
    have e : (0.1 : ℝ) / C₁₉ * C₁₉ = 0.1 := div_mul_cancel₀ _ hC₁₉.ne'
    calc Real.log (Real.log x) ^ C₁₉ ≤ (Real.log x ^ ((0.1 : ℝ) / C₁₉)) ^ C₁₉ :=
          Real.rpow_le_rpow hLL0.le h1 hC₁₉.le
      _ = Real.log x ^ ((0.1 : ℝ) / C₁₉ * C₁₉) := (Real.rpow_mul hL0.le _ _).symm
      _ = Real.log x ^ (0.1 : ℝ) := by rw [e]
  have hDpos : 0 < Real.log (Real.log x) ^ C₁₉ := Real.rpow_pos_of_pos hLL0 _
  have hEη₂ : E * η₂ ≤ 1 := by
    rw [hE, hη₂, ← Real.exp_add]
    refine (Real.exp_le_exp.mpr ?_).trans_eq Real.exp_zero
    have h1 : Real.log x ^ (0.9 : ℝ) ≤ Real.log x / Real.log (Real.log x) ^ C₁₉ := by
      rw [le_div_iff₀ hDpos]
      calc Real.log x ^ (0.9 : ℝ) * Real.log (Real.log x) ^ C₁₉
          ≤ Real.log x ^ (0.9 : ℝ) * Real.log x ^ (0.1 : ℝ) :=
            mul_le_mul_of_nonneg_left hD h9
        _ = Real.log x := hsplit
    have e : -Real.log x / Real.log (Real.log x) ^ C₁₉ =
        -(Real.log x / Real.log (Real.log x) ^ C₁₉) := neg_div _ _
    rw [e]
    linarith
  have hcardE : (𝒯.card : ℝ) ≤ 2 * E := by
    rw [hE]
    exact hcard𝒯
  -- the bound `N` for the differences
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈4 * x ^ (3 : ℝ)⌉₊ := ⟨_, rfl⟩
  have hx3 : 1 ≤ x ^ (3 : ℝ) := Real.one_le_rpow hx1.le (by norm_num)
  have hNge : 4 * x ^ (3 : ℝ) ≤ (N : ℝ) := by
    rw [hN]
    exact Nat.le_ceil _
  have hNle : (N : ℝ) ≤ 8 * x ^ (3 : ℝ) := by
    have h := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 4 * x ^ (3 : ℝ))
    rw [← hN] at h
    linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hlogN : Real.log (N : ℝ) ≤ 7 + 3 * Real.log x := by
    have h1 := Real.log_le_log hNpos hNle
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (Real.rpow_pos_of_pos hx0 (3 : ℝ)).ne',
      Real.log_rpow hx0] at h1
    have h2 : Real.log 8 ≤ 8 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hdiff : ∀ t ∈ 𝒯, ∀ t' ∈ 𝒯, |t - t'| ≤ 4 * x ^ (3 : ℝ) := by
    intro t ht t' ht'
    have h1 := abs_le.mp (hT t ht)
    have h2 := abs_le.mp (hT t' ht')
    exact abs_le.mpr ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩
  -- the trivial bound for the phase sums
  have hcard : ((natIcc R₀ (ρ * R₀)).card : ℝ) ≤ ρ * R₀ := by
    have h2 : (natIcc R₀ (ρ * R₀)).card ≤ ⌊ρ * R₀⌋₊ := by
      unfold natIcc
      rw [Nat.card_Icc]
      have h3 : 0 < ⌈R₀⌉₊ := Nat.ceil_pos.mpr hR₀pos
      omega
    calc ((natIcc R₀ (ρ * R₀)).card : ℝ) ≤ (⌊ρ * R₀⌋₊ : ℝ) := Nat.cast_le.mpr h2
      _ ≤ ρ * R₀ := Nat.floor_le hρR₀.le
  have hmempos : ∀ n ∈ natIcc R₀ (ρ * R₀), 0 < n := by
    intro n hn
    have h := ((mem_natIcc_of_pos hR₀pos).mp hn).1
    have h' : (0 : ℝ) < (n : ℝ) := hR₀pos.trans_le h
    exact Nat.cast_pos.mp h'
  have htriv : ∀ Δ : ℝ,
      ‖∑ n ∈ natIcc R₀ (ρ * R₀), (n : ℂ) ^ ((Δ : ℂ) * Complex.I)‖ ≤ ρ * R₀ := by
    intro Δ
    calc ‖∑ n ∈ natIcc R₀ (ρ * R₀), (n : ℂ) ^ ((Δ : ℂ) * Complex.I)‖
        ≤ ∑ n ∈ natIcc R₀ (ρ * R₀), ‖(n : ℂ) ^ ((Δ : ℂ) * Complex.I)‖ := norm_sum_le _ _
      _ = ∑ _n ∈ natIcc R₀ (ρ * R₀), (1 : ℝ) :=
          Finset.sum_congr rfl fun n hn => norm_natCast_cpow_mul_I (hmempos n hn) Δ
      _ = ((natIcc R₀ (ρ * R₀)).card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ρ * R₀ := hcard
  -- the off-diagonal Gram entries
  have hentry : ∀ Δ : ℝ, 1 ≤ |Δ| → |Δ| ≤ 4 * x ^ (3 : ℝ) →
      ‖∑ n ∈ natIcc R₀ (ρ * R₀), (n : ℂ) ^ ((Δ : ℂ) * Complex.I)‖ ≤
        R₀ * (C * (|Δ|⁻¹ + (η₁ + η₂))) := by
    intro Δ hΔ1 hΔ2
    have hΔinv : 0 ≤ |Δ|⁻¹ := inv_nonneg.mpr (abs_nonneg Δ)
    have hnorm : ‖∑ n ∈ natIcc R₀ (ρ * R₀), (n : ℂ) ^ ((Δ : ℂ) * Complex.I)‖ =
        R₀ * ‖normPoly R₀ (natIcc R₀ (ρ * R₀))
          (fun n => if n ≡ 0 [MOD 1] then divisorSum unitModel n else 0) Δ‖ := by
      rw [normPoly_unitModel hR₀pos Δ, norm_mul, norm_inv, Complex.norm_real,
        Real.norm_of_nonneg hR₀pos.le, ← mul_assoc, mul_inv_cancel₀ hR₀pos.ne', one_mul]
    rw [hnorm]
    refine mul_le_mul_of_nonneg_left ?_ hR₀pos.le
    rcases le_total |Δ| (Real.exp (Real.log x / Real.log (Real.log x) ^ 2)) with hle | hge
    · have h := hmed x hxx₁ R₀ hR₀ 1 Nat.one_pos hk1 0 unitModel (unitModel_support x 1)
        (unitModel_mass x) Δ hΔ1 hle
      rw [Real.rpow_zero, mul_one, ← hη₁] at h
      have h2 : M₁ * (|Δ|⁻¹ + η₁) ≤ C * (|Δ|⁻¹ + (η₁ + η₂)) :=
        calc M₁ * (|Δ|⁻¹ + η₁) ≤ C * (|Δ|⁻¹ + η₁) :=
              mul_le_mul_of_nonneg_right hM₁C (add_nonneg hΔinv hη₁0)
          _ ≤ C * (|Δ|⁻¹ + (η₁ + η₂)) := mul_le_mul_of_nonneg_left (by linarith) hC0
      exact h.trans h2
    · have h := hhigh x hxx₂ R₀ hR₀ hR₀2 1 Nat.one_pos hk1 0 unitModel (unitModel_support x 1)
        (unitModel_mass x) Δ hge hΔ2
      rw [Real.rpow_zero, mul_one, ← hη₂] at h
      have h2 : M₂ * η₂ ≤ C * (|Δ|⁻¹ + (η₁ + η₂)) :=
        calc M₂ * η₂ ≤ C * η₂ := mul_le_mul_of_nonneg_right hM₂C hη₂0
          _ ≤ C * (|Δ|⁻¹ + (η₁ + η₂)) := mul_le_mul_of_nonneg_left (by linarith) hC0
      exact h.trans h2
  -- the row sums of the Gram matrix
  have hrow : ∀ t ∈ 𝒯, ∑ t' ∈ 𝒯, ‖∑ n ∈ natIcc R₀ (ρ * R₀),
      (n : ℂ) ^ ((t : ℂ) * Complex.I) *
        (starRingEnd ℂ) ((n : ℂ) ^ ((t' : ℂ) * Complex.I))‖ ≤
      R₀ * ((ρ + 26 * C) * Real.log x) := by
    intro t ht
    obtain ⟨g, hg⟩ : ∃ g : ℝ → ℝ, ∀ t' : ℝ, g t' =
        ‖∑ n ∈ natIcc R₀ (ρ * R₀), (n : ℂ) ^ (((t - t' : ℝ) : ℂ) * Complex.I)‖ :=
      ⟨fun t' => ‖∑ n ∈ natIcc R₀ (ρ * R₀), (n : ℂ) ^ (((t - t' : ℝ) : ℂ) * Complex.I)‖,
        fun _ => rfl⟩
    have hdiag : g t ≤ ρ * R₀ := by
      rw [hg t]
      exact htriv (t - t)
    have hoff : ∀ t' ∈ 𝒯.erase t, g t' ≤ R₀ * (C * (|t - t'|⁻¹ + (η₁ + η₂))) := by
      intro t' ht'
      obtain ⟨hne, ht'T⟩ := Finset.mem_erase.mp ht'
      rw [hg t']
      exact hentry (t - t') (hsep t ht t' ht'T (Ne.symm hne)) (hdiff t ht t' ht'T)
    have hharm := sum_erase_inv_abs_sub_le 𝒯 t N hsep ht
      (fun a ha => (hdiff t ht a ha).trans hNge)
    have hcard' : ((𝒯.erase t).card : ℝ) ≤ 2 * E :=
      (Nat.cast_le.mpr (Finset.card_le_card (Finset.erase_subset t 𝒯))).trans hcardE
    have hsmall : ((𝒯.erase t).card : ℝ) * (η₁ + η₂) ≤ 4 :=
      calc ((𝒯.erase t).card : ℝ) * (η₁ + η₂) ≤ 2 * E * (η₁ + η₂) :=
            mul_le_mul_of_nonneg_right hcard' (add_nonneg hη₁0 hη₂0)
        _ = 2 * (E * η₁) + 2 * (E * η₂) := by ring
        _ ≤ 4 := by linarith
    have hinner : ∑ t' ∈ 𝒯.erase t, |t - t'|⁻¹ + ((𝒯.erase t).card : ℝ) * (η₁ + η₂) ≤
        2 * (1 + Real.log (N : ℝ)) + 4 := add_le_add hharm hsmall
    have hfinal : ρ + C * (2 * (1 + Real.log (N : ℝ)) + 4) ≤
        ρ * Real.log x + C * (26 * Real.log x) :=
      add_le_add (le_mul_of_one_le_right hρ0.le hL1)
        (mul_le_mul_of_nonneg_left (by linarith) hC0)
    calc ∑ t' ∈ 𝒯, ‖∑ n ∈ natIcc R₀ (ρ * R₀), (n : ℂ) ^ ((t : ℂ) * Complex.I) *
          (starRingEnd ℂ) ((n : ℂ) ^ ((t' : ℂ) * Complex.I))‖
        = ∑ t' ∈ 𝒯, g t' := Finset.sum_congr rfl fun t' _ => by
          rw [hg t', gram_natIcc_eq hR₀pos t t']
      _ = g t + ∑ t' ∈ 𝒯.erase t, g t' := (Finset.add_sum_erase 𝒯 g ht).symm
      _ ≤ ρ * R₀ + ∑ t' ∈ 𝒯.erase t, R₀ * (C * (|t - t'|⁻¹ + (η₁ + η₂))) :=
          add_le_add hdiag (Finset.sum_le_sum hoff)
      _ = ρ * R₀ + R₀ * (C * (∑ t' ∈ 𝒯.erase t, |t - t'|⁻¹ +
            ((𝒯.erase t).card : ℝ) * (η₁ + η₂))) := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
            nsmul_eq_mul]
      _ ≤ ρ * R₀ + R₀ * (C * (2 * (1 + Real.log (N : ℝ)) + 4)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hinner hC0) hR₀pos.le)
      _ = R₀ * (ρ + C * (2 * (1 + Real.log (N : ℝ)) + 4)) := by ring
      _ ≤ R₀ * (ρ * Real.log x + C * (26 * Real.log x)) :=
          mul_le_mul_of_nonneg_left hfinal hR₀pos.le
      _ = R₀ * ((ρ + 26 * C) * Real.log x) := by ring
  -- the Gram operator bound
  have hB0 : 0 ≤ R₀ * ((ρ + 26 * C) * Real.log x) :=
    mul_nonneg hR₀pos.le (mul_nonneg (add_nonneg hρ0.le (mul_nonneg (by norm_num) hC0)) hL0.le)
  have hmain : ∑ t ∈ 𝒯,
      ‖∑ n ∈ natIcc R₀ (ρ * R₀), c n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤
      R₀ * ((ρ + 26 * C) * Real.log x) * ∑ n ∈ natIcc R₀ (ρ * R₀), ‖c n‖ ^ 2 :=
    sum_normSq_le_of_gram_row_sum_le (natIcc R₀ (ρ * R₀)) 𝒯
      (fun (n : ℕ) (t : ℝ) => (n : ℂ) ^ ((t : ℂ) * Complex.I)) c hB0 hrow
  have hsq : ∀ t : ℝ, ‖normPoly R₀ (natIcc R₀ (ρ * R₀)) c t‖ ^ 2 =
      R₀⁻¹ ^ 2 * ‖∑ n ∈ natIcc R₀ (ρ * R₀), c n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 := by
    intro t
    have hnp : normPoly R₀ (natIcc R₀ (ρ * R₀)) c t =
        (R₀ : ℂ)⁻¹ * ∑ n ∈ natIcc R₀ (ρ * R₀), c n * (n : ℂ) ^ ((t : ℂ) * Complex.I) := rfl
    rw [hnp, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hR₀pos.le, mul_pow]
  have hinv : R₀⁻¹ ^ 2 * R₀ = R₀⁻¹ := by
    rw [pow_two, mul_assoc, inv_mul_cancel₀ hR₀pos.ne', mul_one]
  calc ∑ t ∈ 𝒯, ‖normPoly R₀ (natIcc R₀ (ρ * R₀)) c t‖ ^ 2
      = R₀⁻¹ ^ 2 * ∑ t ∈ 𝒯,
          ‖∑ n ∈ natIcc R₀ (ρ * R₀), c n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => hsq t
    _ ≤ R₀⁻¹ ^ 2 * (R₀ * ((ρ + 26 * C) * Real.log x) *
          ∑ n ∈ natIcc R₀ (ρ * R₀), ‖c n‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hmain (sq_nonneg _)
    _ = R₀⁻¹ ^ 2 * R₀ * ((ρ + 26 * C) * Real.log x) *
          ∑ n ∈ natIcc R₀ (ρ * R₀), ‖c n‖ ^ 2 := by ring
    _ = (ρ + 26 * C) * Real.log x * (R₀⁻¹ * ∑ n ∈ natIcc R₀ (ρ * R₀), ‖c n‖ ^ 2) := by
        rw [hinv]
        ring

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
