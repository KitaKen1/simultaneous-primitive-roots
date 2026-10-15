module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.CoreGrowth
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.StripStructure
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.StripInputs

/-!
# The stripping step: `StripLink`

`[P-07:0317–0386]`: replacing the proxy coefficient `a` by the stripped coefficient `ã` changes
the smooth shifted sum of the `j`-fold convolution by `o(x/L)`.

With `L = log x`, `V = V(W)`, `Λ₀ = L^{.45}`, `Λ = Λ₀² = L^{.9}`, `κ₀ = 1/(V γ L)` and
`N = ⌊R x⌋ + 1`:

* Lemma 2.5 (`RoughCounts`, `δ = γ`, `C = 3`, `A = 1`) and `V ≫ L^{-.24}` (Mertens' product)
  give at most `2 V H` rough integers in `[H, 2H]`, `x^γ ≤ H ≤ x^3`;
* the integers that are not good have density `≤ 2 C_v L^{.1}/L^{.45}` (`bad_density_le`; the
  candidate primes have reciprocal mass `O(log L)`, from Mertens' sum, and are `≥ L^{.45}`);
* hence `∑ ρ ≤ 4 V t`, `∑ ρ/m ≤ 10 V L` and `∑ θ/m ≤ E V Λ` (`strip_inputs`,
  `strip_theta_arith`), and by `strip_sum_le` the sum is
  `≤ ‖Φ‖_∞ j κ₀^j (4 V N) (E V Λ) (10 V L)^{j-2} ≪ x L^{.9}/L²` (`strip_final_arith`).

The declarations other than `stripLink` are in the namespace `Extraction.Strip`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

open Filter

noncomputable section

namespace Strip

/-- The relations between the powers of `L` used below. -/
theorem strip_rpow_facts {L : ℝ} (hL : 1 ≤ L) :
    L ^ (0.76 : ℝ) * L ^ (0.24 : ℝ) = L ∧
      L ^ (0.45 : ℝ) * L ^ (0.45 : ℝ) * L ^ (0.1 : ℝ) = L ∧
      (L ^ (0.45 : ℝ)) ^ ((2 : ℝ) / 9) = L ^ (0.1 : ℝ) ∧
      L ^ (0.24 : ℝ) * L ^ (0.1 : ℝ) * L ≤
        L ^ (0.45 : ℝ) * L ^ (0.45 : ℝ) * L ^ (0.45 : ℝ) ∧
      L ^ (0.28 : ℝ) * L ^ (0.28 : ℝ) = L ^ (0.45 : ℝ) * L ^ (0.11 : ℝ) := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have e1 : (0.76 : ℝ) + 0.24 = 1 := by norm_num
  have e2 : (0.45 : ℝ) + 0.45 + 0.1 = 1 := by norm_num
  have e3 : (0.45 : ℝ) * (2 / 9) = 0.1 := by norm_num
  have e4 : (0.24 : ℝ) + 0.1 + 1 ≤ 0.45 + 0.45 + 0.45 := by norm_num
  have e5 : (0.28 : ℝ) + 0.28 = 0.45 + 0.11 := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← Real.rpow_add hL0, e1, Real.rpow_one]
  · rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, e2, Real.rpow_one]
  · rw [← Real.rpow_mul hL0.le, e3]
  · have h1 : L ^ (0.24 : ℝ) * L ^ (0.1 : ℝ) * L = L ^ ((0.24 : ℝ) + 0.1 + 1) := by
      rw [Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_one]
    have h2 : L ^ (0.45 : ℝ) * L ^ (0.45 : ℝ) * L ^ (0.45 : ℝ) =
        L ^ ((0.45 : ℝ) + 0.45 + 0.45) := by
      rw [Real.rpow_add hL0, Real.rpow_add hL0]
    rw [h1, h2]
    exact Real.rpow_le_rpow_of_exponent_le hL e4
  · rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, e5]

/-- `L^{.45} ≤ exp(L^{.28})` once `L^{.11} ≥ 4`. -/
theorem rpow_le_exp_rpow {L : ℝ} (hL : 1 ≤ L) (h11 : 4 ≤ L ^ (0.11 : ℝ)) :
    L ^ (0.45 : ℝ) ≤ Real.exp (L ^ (0.28 : ℝ)) := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = L ^ (0.28 : ℝ) := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by
    rw [hy]
    exact Real.rpow_nonneg hL0.le _
  have hyy : y * y = L ^ (0.45 : ℝ) * L ^ (0.11 : ℝ) := by
    rw [hy]
    exact (strip_rpow_facts hL).2.2.2.2
  have hT0 : 0 ≤ L ^ (0.45 : ℝ) := Real.rpow_nonneg hL0.le _
  have h1 : y / 2 + 1 ≤ Real.exp (y / 2) := Real.add_one_le_exp _
  have h2 : Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) := by
    rw [← Real.exp_add, add_halves]
  have h3 : (y / 2 + 1) * (y / 2 + 1) ≤ Real.exp (y / 2) * Real.exp (y / 2) :=
    mul_le_mul h1 h1 (by linarith) (Real.exp_pos _).le
  have h4 := mul_le_mul_of_nonneg_left h11 hT0
  rw [← hy, h2]
  nlinarith

/-- **The integers that are not good are rare** (`[P-07:0352–0361]`): their density is at most
`2 C_v L^{.1}/L^{.45}`, `C_v = 9/2 + 2C`, when the candidate primes have reciprocal mass
`≤ log(L^{.45}) + 2C` and `L^{.11} ≥ 4`. -/
theorem bad_density_le {x Cw : ℝ} (hL1 : 1 ≤ Real.log x)
    (hmass : reciprocalMass (candidatePrimes x) ≤
      Real.log (Real.log x ^ (0.45 : ℝ)) + 2 * Cw) (hCw : 0 ≤ Cw)
    (h11 : 4 ≤ Real.log x ^ (0.11 : ℝ)) :
    0 ≤ ∑ p ∈ candidatePrimes x, 1 / (p : ℝ) ^ 2 +
        reciprocalMass (candidatePrimes x) / Real.log x ^ (0.45 : ℝ) ∧
      ∑ p ∈ candidatePrimes x, 1 / (p : ℝ) ^ 2 +
          reciprocalMass (candidatePrimes x) / Real.log x ^ (0.45 : ℝ) ≤
        2 * ((9 / 2 + 2 * Cw) * Real.log x ^ (0.1 : ℝ)) / Real.log x ^ (0.45 : ℝ) := by
  have hT1 : 1 ≤ Real.log x ^ (0.45 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hT0 : 0 < Real.log x ^ (0.45 : ℝ) := lt_of_lt_of_le one_pos hT1
  have h011 : 1 ≤ Real.log x ^ (0.1 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hTexp := rpow_le_exp_rpow hL1 h11
  have hmass0 : 0 ≤ reciprocalMass (candidatePrimes x) := by
    unfold reciprocalMass
    exact Finset.sum_nonneg fun p _ => by positivity
  -- the multiples of the squares
  have hsq : ∑ p ∈ candidatePrimes x, 1 / (p : ℝ) ^ 2 ≤
      reciprocalMass (candidatePrimes x) / Real.log x ^ (0.45 : ℝ) := by
    unfold reciprocalMass
    rw [Finset.sum_div]
    refine Finset.sum_le_sum fun p hp => ?_
    obtain ⟨-, hlo, -⟩ := candidatePrimes_facts hL1 hp
    have hpT : Real.log x ^ (0.45 : ℝ) ≤ (p : ℝ) := hTexp.trans hlo
    calc 1 / (p : ℝ) ^ 2 = 1 / (p : ℝ) * (1 / (p : ℝ)) := by ring
      _ ≤ 1 / (p : ℝ) * (1 / Real.log x ^ (0.45 : ℝ)) :=
          mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hT0 hpT) (by positivity)
      _ = 1 / (p : ℝ) / Real.log x ^ (0.45 : ℝ) := (div_eq_mul_one_div _ _).symm
  -- the mass of the candidate primes
  have hlogT : Real.log (Real.log x ^ (0.45 : ℝ)) ≤ 9 / 2 * Real.log x ^ (0.1 : ℝ) := by
    have h := Real.log_le_rpow_div hT0.le (by norm_num : (0 : ℝ) < 2 / 9)
    rw [(strip_rpow_facts hL1).2.2.1] at h
    calc Real.log (Real.log x ^ (0.45 : ℝ)) ≤ Real.log x ^ (0.1 : ℝ) / (2 / 9) := h
      _ = 9 / 2 * Real.log x ^ (0.1 : ℝ) := by ring
  have hVc : reciprocalMass (candidatePrimes x) ≤
      (9 / 2 + 2 * Cw) * Real.log x ^ (0.1 : ℝ) := by
    have h1 : 2 * Cw ≤ 2 * Cw * Real.log x ^ (0.1 : ℝ) :=
      le_mul_of_one_le_right (mul_nonneg two_pos.le hCw) h011
    linarith
  refine ⟨add_nonneg (Finset.sum_nonneg fun p _ => by positivity)
    (div_nonneg hmass0 hT0.le), ?_⟩
  calc ∑ p ∈ candidatePrimes x, 1 / (p : ℝ) ^ 2 +
        reciprocalMass (candidatePrimes x) / Real.log x ^ (0.45 : ℝ)
      ≤ reciprocalMass (candidatePrimes x) / Real.log x ^ (0.45 : ℝ) +
        reciprocalMass (candidatePrimes x) / Real.log x ^ (0.45 : ℝ) := add_le_add hsq le_rfl
    _ = 2 * reciprocalMass (candidatePrimes x) / Real.log x ^ (0.45 : ℝ) := by ring
    _ ≤ 2 * ((9 / 2 + 2 * Cw) * Real.log x ^ (0.1 : ℝ)) / Real.log x ^ (0.45 : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hVc two_pos.le) hT0.le

/-- The reciprocal sum of `θ` is `≤ E V Λ₀²`, `E = 20 C_v/c₁ + 6 + 10/γ`. -/
theorem strip_theta_arith {cβ Cv L01 Λ₀ L24 L V c₁ γ : ℝ} (hΛ₀ : 0 < Λ₀) (hc₁ : 0 < c₁)
    (hCv : 0 ≤ Cv) (hV : 0 < V) (hL : 0 < L) (hγ : 0 < γ) (hL01 : 0 ≤ L01)
    (hcβ : cβ ≤ 2 * (Cv * L01) / Λ₀) (hVc : c₁ < L24 * V)
    (hp4 : L24 * L01 * L ≤ Λ₀ * Λ₀ * Λ₀) :
    2 * cβ * (5 * L) + 2 * V * (3 * (Λ₀ * Λ₀)) +
        Λ₀ * Λ₀ / (γ * L) * (2 * V * (5 * L)) ≤
      (20 * Cv / c₁ + 6 + 10 / γ) * V * (Λ₀ * Λ₀) := by
  have h3 : L01 * L / Λ₀ ≤ V * (Λ₀ * Λ₀) / c₁ := by
    rw [div_le_iff₀ hΛ₀, div_mul_eq_mul_div, le_div_iff₀ hc₁]
    have h4 : c₁ * (L01 * L) ≤ L24 * V * (L01 * L) :=
      mul_le_mul_of_nonneg_right hVc.le (mul_nonneg hL01 hL.le)
    have h5 : V * (L24 * L01 * L) ≤ V * (Λ₀ * Λ₀ * Λ₀) :=
      mul_le_mul_of_nonneg_left hp4 hV.le
    linarith
  have t1 : 2 * cβ * (5 * L) ≤ 20 * Cv / c₁ * V * (Λ₀ * Λ₀) := by
    calc 2 * cβ * (5 * L) ≤ 2 * (2 * (Cv * L01) / Λ₀) * (5 * L) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcβ two_pos.le)
            (mul_nonneg (by norm_num) hL.le)
      _ = 20 * Cv * (L01 * L / Λ₀) := by ring
      _ ≤ 20 * Cv * (V * (Λ₀ * Λ₀) / c₁) :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg (by norm_num) hCv)
      _ = 20 * Cv / c₁ * V * (Λ₀ * Λ₀) := by ring
  have e1 : Λ₀ * Λ₀ / (γ * L) * (γ * L) = Λ₀ * Λ₀ :=
    div_mul_cancel₀ _ (mul_pos hγ hL).ne'
  have e2 : 10 / γ * γ = 10 := div_mul_cancel₀ _ hγ.ne'
  have t3 : Λ₀ * Λ₀ / (γ * L) * (2 * V * (5 * L)) = 10 / γ * V * (Λ₀ * Λ₀) := by
    linear_combination (10 / γ * V) * e1 - (Λ₀ * Λ₀ / (γ * L) * V * L) * e2
  rw [t3]
  linarith

/-- The final arithmetic: `‖Φ‖_∞ j κ₀^j (4 V N) (E V Λ) (10 V L)^{j-2} ≤ η x/L` when
`κ₀ = 1/(V γ L)`, `Λ L^{.1} = L`, `N ≤ (R + 1) x` and `L^{.1}` is large. -/
theorem strip_final_arith {Bφ η R x L V γ Λ L01 Eθ κ₀ : ℝ} {j N : ℕ} (hj : 2 ≤ j)
    (hB0 : 0 ≤ Bφ) (hx : 0 < x) (hL : 0 < L) (hV : 0 < V) (hγ : 0 < γ) (hΛ : 0 ≤ Λ)
    (hE : 0 ≤ Eθ) (hκ : κ₀ = 1 / (V * (γ * L))) (hΛL : Λ * L01 = L)
    (hN : (N : ℝ) ≤ (R + 1) * x)
    (hD : Bφ * ((j : ℝ) * ((10 / γ) ^ (j - 2) * (4 * Eθ))) * (R + 1) / γ ^ 2 ≤ η * L01) :
    Bφ * ((j : ℝ) * (κ₀ ^ j *
      (2 * (2 * V) * (N : ℝ) * (Eθ * V * Λ * (10 * V * L) ^ (j - 2))))) ≤ η * (x / L) := by
  obtain ⟨k, rfl⟩ : ∃ k, j = 2 + k := ⟨j - 2, by omega⟩
  have hk : 2 + k - 2 = k := by omega
  rw [hk] at hD ⊢
  have hκ1 : κ₀ * (V * (γ * L)) = 1 := by
    rw [hκ]
    exact one_div_mul_cancel (mul_pos hV (mul_pos hγ hL)).ne'
  have hκ0 : 0 ≤ κ₀ := by
    rw [hκ]
    exact (one_div_pos.mpr (mul_pos hV (mul_pos hγ hL))).le
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = κ₀ * (10 * V * L) := ⟨_, rfl⟩
  have huγ : u = 10 / γ := by
    rw [eq_div_iff hγ.ne', hu]
    linear_combination 10 * hκ1
  obtain ⟨v, hv⟩ : ∃ v : ℝ, v = κ₀ * V * γ := ⟨_, rfl⟩
  have hvL : v * L = 1 := by
    rw [hv]
    linear_combination hκ1
  have hv1 : v = 1 / L := eq_one_div_of_mul_eq_one_left hvL
  obtain ⟨G, hG⟩ :
      ∃ G : ℝ, G = Bφ * (((2 + k : ℕ) : ℝ) * ((10 / γ) ^ k * (4 * Eθ))) := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := by
    rw [hG]
    exact mul_nonneg hB0 (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (pow_nonneg (div_nonneg (by norm_num) hγ.le) k)
        (mul_nonneg (by norm_num) hE)))
  have hGR : G * (R + 1) ≤ η * L01 * γ ^ 2 := by
    rw [← hG] at hD
    exact (div_le_iff₀ (pow_pos hγ 2)).mp hD
  have hid : Bφ * (((2 + k : ℕ) : ℝ) * (κ₀ ^ (2 + k) *
      (2 * (2 * V) * (N : ℝ) * (Eθ * V * Λ * (10 * V * L) ^ k)))) * γ ^ 2 =
      G * (v ^ 2 * (Λ * (N : ℝ))) := by
    rw [hG, hv, ← huγ, hu]
    ring
  refine le_of_mul_le_mul_right ?_ (pow_pos hγ 2)
  rw [hid]
  calc G * (v ^ 2 * (Λ * (N : ℝ))) ≤ G * (v ^ 2 * (Λ * ((R + 1) * x))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hN hΛ) (sq_nonneg v)) hG0
    _ = G * (R + 1) * (v ^ 2 * Λ * x) := by ring
    _ ≤ η * L01 * γ ^ 2 * (v ^ 2 * Λ * x) :=
        mul_le_mul_of_nonneg_right hGR (mul_nonneg (mul_nonneg (sq_nonneg v) hΛ) hx.le)
    _ = η * (x / L) * γ ^ 2 := by
        rw [div_eq_mul_one_div, ← hv1]
        linear_combination (η * γ ^ 2 * v ^ 2 * x) * hΛL + (η * γ ^ 2 * x * v) * hvL

end Strip

open Strip in
open _root_.Classical in
/-- **The stripping step** (`[P-07:0317–0386]`): `StripLink`. From Lemma 2.5 (rough counts),
Mertens' product and Mertens' sum, the smooth shifted sum of
`∑_{e_1 ⋯ e_j = u + 1} |∏_i a(e_i) - ∏_i ã(e_i)|` is `o(x/L)`. -/
theorem stripLink : StripLink := by
  intro hRC hMP hMR Φ hΦ γ hγ hγ1 j hj η hη
  obtain ⟨R, hR0, hR⟩ := hΦ.exists_upper
  obtain ⟨Bφ, hB0, hB⟩ := hΦ.exists_bound
  obtain ⟨Mr, xr, hrough⟩ :=
    hRC γ 3 (1 / 2) 1 hγ (by norm_num) (by norm_num) (by norm_num) one_pos
  obtain ⟨Cw, hCw, hmass⟩ := reciprocalMass_candidatePrimes_le hMR
  obtain ⟨c₁, hc₁def⟩ :
      ∃ c₁ : ℝ, c₁ = Real.exp (-Real.eulerMascheroniConstant) / 2 := ⟨_, rfl⟩
  have hc₁ : 0 < c₁ := by
    rw [hc₁def]
    exact div_pos (Real.exp_pos _) two_pos
  have hCv : (0 : ℝ) ≤ 9 / 2 + 2 * Cw := by linarith
  obtain ⟨Eθ, hEdef⟩ : ∃ Eθ : ℝ, Eθ = 20 * (9 / 2 + 2 * Cw) / c₁ + 6 + 10 / γ := ⟨_, rfl⟩
  have hE : 0 ≤ Eθ := by
    have h1 : 0 ≤ 20 * (9 / 2 + 2 * Cw) / c₁ :=
      div_nonneg (mul_nonneg (by norm_num) hCv) hc₁.le
    have h2 : 0 ≤ 10 / γ := div_nonneg (by norm_num) hγ.le
    rw [hEdef]
    linarith
  have hpow : ∀ a : ℝ, 0 < a → ∀ C : ℝ, ∀ᶠ x : ℝ in atTop, C ≤ Real.log x ^ a :=
    fun a ha C =>
      ((tendsto_rpow_atTop ha).comp Real.tendsto_log_atTop).eventually_ge_atTop C
  filter_upwards [eventually_mertensProduct_roughCutoff_ge hMP, eventually_ge_atTop xr,
    eventually_ge_atTop (2 * (R + 1)), eventually_ge_atTop (Real.exp 2),
    hpow 0.76 (by norm_num) (|Mr| / c₁), hpow 0.11 (by norm_num) 4,
    hpow 0.1 (by norm_num)
      (Bφ * ((j : ℝ) * ((10 / γ) ^ (j - 2) * (4 * Eθ))) * (R + 1) / γ ^ 2 / η)]
    with x hV hxr hxR hxe h76 h11 h01
  rw [← hc₁def] at hV
  have hx0 : 0 < x := by linarith
  have hL2 : 2 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hxe
  have hL1 : 1 ≤ Real.log x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  obtain ⟨hp1, hp2, -, hp4, -⟩ := strip_rpow_facts hL1
  have hVpos := mertensProduct_pos (roughCutoff x)
  have hT1 : 1 ≤ Real.log x ^ (0.45 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hT0 : 0 < Real.log x ^ (0.45 : ℝ) := lt_of_lt_of_le one_pos hT1
  have h011 : 1 ≤ Real.log x ^ (0.1 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hΛ1 : 1 ≤ Real.log x ^ (0.45 : ℝ) * Real.log x ^ (0.45 : ℝ) :=
    one_le_mul_of_one_le_of_one_le hT1 hT1
  have hΛ0 : 0 ≤ Real.log x ^ (0.45 : ℝ) * Real.log x ^ (0.45 : ℝ) := by linarith
  have hΛL : Real.log x ^ (0.45 : ℝ) * Real.log x ^ (0.45 : ℝ) ≤ Real.log x := by
    have h := le_mul_of_one_le_right hΛ0 h011
    rwa [hp2] at h
  -- Lemma 2.5: at most `2 V H` rough integers in `[H, 2H]`
  have hMrV : |Mr| ≤ mertensProduct (roughCutoff x) * Real.log x := by
    have h1 : |Mr| ≤ c₁ * Real.log x ^ (0.76 : ℝ) := by
      rwa [div_le_iff₀' hc₁] at h76
    have h2 : c₁ * Real.log x ^ (0.76 : ℝ) ≤
        Real.log x ^ (0.24 : ℝ) * mertensProduct (roughCutoff x) *
          Real.log x ^ (0.76 : ℝ) :=
      mul_le_mul_of_nonneg_right hV.le (Real.rpow_nonneg hL0.le _)
    calc |Mr| ≤ Real.log x ^ (0.24 : ℝ) * mertensProduct (roughCutoff x) *
          Real.log x ^ (0.76 : ℝ) := h1.trans h2
      _ = mertensProduct (roughCutoff x) *
          (Real.log x ^ (0.76 : ℝ) * Real.log x ^ (0.24 : ℝ)) := by ring
      _ = mertensProduct (roughCutoff x) * Real.log x := by rw [hp1]
  have hblock : ∀ H : ℝ, x ^ γ ≤ H → H ≤ x ^ (3 : ℝ) →
      (((Finset.Icc ⌈H⌉₊ ⌊2 * H⌋₊).filter fun n => IsRough (roughCutoff x) n).card : ℝ) ≤
        2 * mertensProduct (roughCutoff x) * H := by
    intro H hH1 hH2
    have hH0 : 0 ≤ H := (Real.rpow_nonneg hx0.le γ).trans hH1
    have h := (abs_le.mp
      (hrough x hxr H hH1 hH2 H (2 * H) le_rfl (by linarith) le_rfl).1).2
    rw [Real.rpow_neg_one] at h
    have h2 : Mr * H ≤ mertensProduct (roughCutoff x) * H * Real.log x := by
      calc Mr * H ≤ |Mr| * H := mul_le_mul_of_nonneg_right (le_abs_self Mr) hH0
        _ ≤ mertensProduct (roughCutoff x) * Real.log x * H :=
            mul_le_mul_of_nonneg_right hMrV hH0
        _ = mertensProduct (roughCutoff x) * H * Real.log x := by ring
    have h1 : Mr * H * (Real.log x)⁻¹ ≤ mertensProduct (roughCutoff x) * H := by
      rw [← div_eq_mul_inv, div_le_iff₀ hL0]
      exact h2
    linarith
  -- good integers have a small candidate part; the others are rare
  have hgood : ∀ m : ℕ, m ≠ 0 → Good (candidatePrimes x) (Real.log x ^ (0.45 : ℝ)) m →
      (m : ℝ) ≤ (freePart (candidatePrimes x) m : ℝ) *
        Real.exp (Real.log x ^ (0.45 : ℝ) * Real.log x ^ (0.45 : ℝ)) := fun m hm hg =>
    good_le hT0.le (fun p hp => ⟨(candidatePrimes_facts hL1 hp).1,
      (candidatePrimes_facts hL1 hp).2.2⟩) hm hg
  obtain ⟨hcβ0, hcβ⟩ := bad_density_le hL1 (hmass x (by linarith)) hCw h11
  obtain ⟨hN, hcount, hrρ, hrσ, hrβ⟩ := strip_inputs (P := candidatePrimes x)
    (Λ₀ := Real.log x ^ (0.45 : ℝ)) hR0 hγ hγ1 hxR hL2 (mul_pos two_pos hVpos).le hblock
    hΛ1 hΛL hcβ0 fun t => bad_count_le hT0 t
  -- the reciprocal sum of `θ`
  have hε0 : 0 ≤ Real.log x ^ (0.45 : ℝ) * Real.log x ^ (0.45 : ℝ) / (γ * Real.log x) :=
    div_nonneg hΛ0 (mul_pos hγ hL0).le
  have hrθ : ∑ m ∈ Finset.Icc 1 (⌊R * x⌋₊ + 1),
      thetaW x γ (candidatePrimes x) (Real.log x ^ (0.45 : ℝ))
        (Real.log x ^ (0.45 : ℝ) * Real.log x ^ (0.45 : ℝ))
        (Real.log x ^ (0.45 : ℝ) * Real.log x ^ (0.45 : ℝ) / (γ * Real.log x)) m /
          (m : ℝ) ≤
      Eθ * mertensProduct (roughCutoff x) *
        (Real.log x ^ (0.45 : ℝ) * Real.log x ^ (0.45 : ℝ)) := by
    refine (sum_thetaW_div_le x γ _ _ _ _ _).trans ?_
    refine (add_le_add (add_le_add hrβ hrσ) (mul_le_mul_of_nonneg_left hrρ hε0)).trans ?_
    rw [hEdef]
    exact strip_theta_arith hT0 hc₁ hCv hVpos hL0 hγ (by linarith) hcβ hV hp4
  -- assembly
  have hA1 : 1 ≤ x ^ γ := Real.one_le_rpow (by linarith) hγ.le
  have hrρ' : ∑ m ∈ Finset.Icc 1 (⌊R * x⌋₊ + 1), rhoW x γ m / (m : ℝ) ≤
      10 * mertensProduct (roughCutoff x) * Real.log x := hrρ.trans_eq (by ring)
  have hmain := strip_sum_le hR hB hB0 hj hx0 hA1 (mul_pos hγ hL0) (Real.log_rpow hx0 γ) hΛ0
    rfl hgood (mul_nonneg two_pos.le (mul_pos two_pos hVpos).le) hcount hrρ' hrθ
  refine hmain.trans ?_
  have hD : Bφ * ((j : ℝ) * ((10 / γ) ^ (j - 2) * (4 * Eθ))) * (R + 1) / γ ^ 2 ≤
      η * Real.log x ^ (0.1 : ℝ) := by
    rw [div_le_iff₀ hη] at h01
    linarith
  exact strip_final_arith hj hB0 hx0 hL0 hVpos hγ hΛ0 hE rfl hp2 hN hD

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
