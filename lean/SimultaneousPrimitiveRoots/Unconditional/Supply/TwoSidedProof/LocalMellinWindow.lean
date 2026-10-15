module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.LocalMellinGauss

/-!
# Window comparison for the lemma (local Mellin energy)

Real-variable estimates for `LocalMellin` (`[P-06:0488–0528]`): "On the union of the relevant
supports, replace `K((w-v)/H)` by `K(v log(w/v)/H)`: their arguments differ by `O(H/Y)`. Cauchy over
the `O(H)` available `w`, and integration over the `O(H)` centers for each `w`, give normalized
squared error `O((H/Y)² ∑|a_w|²)`."

With the Gaussian `K(x) = e^{-x²}` the replacement is the pointwise inequality `window_in`: for
`w ∈ [a₁Y, a₂Y]` and a centre `v ∈ [a₁Y/2, 2a₂Y]`,
`|e^{-(w-v)²/H²} - e^{-(v/H)² log²(w/v)}| ≤ C (H/Y) e^{-(w-v)²/(2ρ²H²)}`, `ρ = 2a₂/a₁`;
outside this range of centres the additive window itself is that small (`window_out`: "Only
`v ≍ Y` contributes").

* `window_normalized`: the comparison in the variables `N = v/H`, `r = w/v`;
* `gauss_sum_le`: `∑_w e^{-g(w-v)²} ≤ e^{g/4} √(2π/g)` over distinct integers `w` ("the `O(H)`
  available `w`");
* `sq_sum_mul_le`: the Cauchy step;
* `exp_weight_le`: `e^{-u²/(16a²)} ≤ e^{4a²j²} (1+u)^{-j}`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open MeasureTheory

noncomputable section

namespace LocalMellinAux

/-! ### Elementary inequalities -/

/-- `|e^{-A} - e^{-B}| ≤ |A - B| e^{-m}` when `m ≤ A, B`. -/
theorem abs_exp_neg_sub_le {A B m : ℝ} (hA : m ≤ A) (hB : m ≤ B) :
    |Real.exp (-A) - Real.exp (-B)| ≤ |A - B| * Real.exp (-m) := by
  have key : ∀ {A B : ℝ}, m ≤ A → A ≤ B →
      Real.exp (-A) - Real.exp (-B) ≤ (B - A) * Real.exp (-m) := by
    intro A B hA hAB
    have h1 : -(B - A) + 1 ≤ Real.exp (-(B - A)) := Real.add_one_le_exp _
    have h2 : Real.exp (-B) = Real.exp (-A) * Real.exp (-(B - A)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have h3 : Real.exp (-A) ≤ Real.exp (-m) := Real.exp_le_exp.mpr (by linarith)
    rw [h2]
    calc Real.exp (-A) - Real.exp (-A) * Real.exp (-(B - A))
        = Real.exp (-A) * (1 - Real.exp (-(B - A))) := by ring
      _ ≤ Real.exp (-A) * (B - A) :=
          mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      _ ≤ Real.exp (-m) * (B - A) := mul_le_mul_of_nonneg_right h3 (by linarith)
      _ = (B - A) * Real.exp (-m) := mul_comm _ _
  rcases le_total A B with h | h
  · have h5 : Real.exp (-B) ≤ Real.exp (-A) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (sub_nonneg.mpr h5), abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    exact key hA h
  · have h5 : Real.exp (-A) ≤ Real.exp (-B) := Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonpos (sub_nonpos.mpr h5), abs_of_nonneg (sub_nonneg.mpr h), neg_sub]
    exact key hB h

/-- `s³ e^{-s²/(2ρ²)} ≤ 8ρ⁴`. -/
theorem cube_mul_exp_le {s ρ : ℝ} (hs : 0 ≤ s) (hρ : 1 ≤ ρ) :
    s ^ 3 * Real.exp (-(s ^ 2 / (2 * ρ ^ 2))) ≤ 8 * ρ ^ 4 := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ
  obtain ⟨u, hu⟩ : ∃ u : ℝ, u = s ^ 2 / (2 * ρ ^ 2) := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by
    rw [hu]
    positivity
  have hsu : u * (2 * ρ ^ 2) = s ^ 2 := by
    rw [hu]
    exact div_mul_cancel₀ _ (by positivity)
  have h1 : 1 + u + u ^ 2 / 2 ≤ Real.exp u := Real.quadratic_le_exp_of_nonneg hu0
  have h2 : s ^ 3 ≤ 1 + s ^ 4 := by
    rcases le_total s 1 with h | h
    · have h3 : s ^ 3 ≤ 1 := pow_le_one₀ hs h
      have h4 : 0 ≤ s ^ 4 := pow_nonneg hs 4
      linarith
    · have h3 : s ^ 3 * 1 ≤ s ^ 3 * s := mul_le_mul_of_nonneg_left h (pow_nonneg hs 3)
      have h4 : s ^ 3 * s = s ^ 4 := by ring
      linarith
  have h5 : s ^ 4 = 4 * ρ ^ 4 * u ^ 2 := by
    have e : s ^ 4 = (s ^ 2) ^ 2 := by ring
    rw [e, ← hsu]
    ring
  have h6 : (1 : ℝ) ≤ ρ ^ 4 := one_le_pow₀ hρ
  have h7 : 0 ≤ ρ ^ 4 * u := mul_nonneg (pow_nonneg hρ0.le 4) hu0
  rw [← hu, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  calc s ^ 3 ≤ 1 + s ^ 4 := h2
    _ ≤ 8 * ρ ^ 4 * (1 + u + u ^ 2 / 2) := by
        rw [h5]
        linarith
    _ ≤ 8 * ρ ^ 4 * Real.exp u := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- `e^{-x²/2} ≤ 1/x` for `x > 0`. -/
theorem exp_neg_sq_half_le {x : ℝ} (hx : 0 < x) : Real.exp (-(x ^ 2 / 2)) ≤ 1 / x := by
  have h1 : x ^ 2 / 2 + 1 ≤ Real.exp (x ^ 2 / 2) := Real.add_one_le_exp _
  have h2 : x ≤ Real.exp (x ^ 2 / 2) := by nlinarith [sq_nonneg (x - 1)]
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ hx h2

/-- A Gaussian is dominated by every negative power:
`e^{-u²/(16a²)} ≤ e^{4a²j²} (1+u)^{-j}` for `u ≥ 0`. -/
theorem exp_weight_le {a₂ u : ℝ} (ha₂ : 0 < a₂) (hu : 0 ≤ u) (j : ℕ) :
    Real.exp (-(u ^ 2 / (16 * a₂ ^ 2))) ≤
      Real.exp (4 * a₂ ^ 2 * (j : ℝ) ^ 2) * (1 + u) ^ (-(j : ℝ)) := by
  have h1u : 0 < 1 + u := by linarith
  have ha : a₂ * a₂⁻¹ = 1 := mul_inv_cancel₀ ha₂.ne'
  have e : (u / (4 * a₂) - 2 * a₂ * (j : ℝ)) ^ 2 =
      u ^ 2 / (16 * a₂ ^ 2) - (j : ℝ) * u + 4 * a₂ ^ 2 * (j : ℝ) ^ 2 := by
    linear_combination (-(u * (j : ℝ))) * ha
  have h2 : (j : ℝ) * u - u ^ 2 / (16 * a₂ ^ 2) ≤ 4 * a₂ ^ 2 * (j : ℝ) ^ 2 := by
    have h := sq_nonneg (u / (4 * a₂) - 2 * a₂ * (j : ℝ))
    rw [e] at h
    linarith
  have h3 : (1 + u) ^ j ≤ Real.exp ((j : ℝ) * u) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ h1u.le (by linarith [Real.add_one_le_exp u]) j
  rw [Real.rpow_neg h1u.le, Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (pow_pos h1u j)]
  calc Real.exp (-(u ^ 2 / (16 * a₂ ^ 2))) * (1 + u) ^ j
      ≤ Real.exp (-(u ^ 2 / (16 * a₂ ^ 2))) * Real.exp ((j : ℝ) * u) :=
        mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
    _ = Real.exp ((j : ℝ) * u - u ^ 2 / (16 * a₂ ^ 2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (4 * a₂ ^ 2 * (j : ℝ) ^ 2) := Real.exp_le_exp.mpr h2

/-- The Cauchy step: `(∑ x_w E_w)² ≤ (∑ x_w² E_w)(∑ E_w)` for weights `E_w ≥ 0`. -/
theorem sq_sum_mul_le (s : Finset ℕ) (x E : ℕ → ℝ) (hE : ∀ w ∈ s, 0 ≤ E w) :
    (∑ w ∈ s, x w * E w) ^ 2 ≤ (∑ w ∈ s, x w ^ 2 * E w) * ∑ w ∈ s, E w :=
  Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (fun w hw => mul_nonneg (sq_nonneg _) (hE w hw)) hE (fun w _ => le_of_eq (by ring))

/-! ### The additive and the logarithmic Gaussian windows -/

/-- **Window comparison, normalized.** For `N > 0` and `1/ρ ≤ r ≤ ρ`,
`|e^{-(N(r-1))²} - e^{-(N log r)²}| ≤ (8ρ⁵(1+ρ)/N) e^{-(N(r-1))²/(2ρ²)}`. -/
theorem window_normalized {N r ρ : ℝ} (hN : 0 < N) (hr : 0 < r) (hρ : 1 ≤ ρ) (hr1 : r⁻¹ ≤ ρ)
    (hr2 : r ≤ ρ) :
    |Real.exp (-(N * (r - 1)) ^ 2) - Real.exp (-(N * Real.log r) ^ 2)| ≤
      8 * ρ ^ 5 * (1 + ρ) / N * Real.exp (-((N * (r - 1)) ^ 2 / (2 * ρ ^ 2))) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ
  have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  have hrinv : 0 < r⁻¹ := inv_pos.mpr hr
  have hρr : ρ⁻¹ ≤ r⁻¹ := inv_anti₀ hr hr2
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = r - 1 := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = Real.log r := ⟨_, rfl⟩
  rw [← hd, ← hl]
  have h1 : l ≤ d := by
    rw [hl, hd]
    exact Real.log_le_sub_one_of_pos hr
  have h2 : d * r⁻¹ ≤ l := by
    have e : d * r⁻¹ = 1 - r⁻¹ := by
      rw [hd]
      linear_combination hrr
    rw [e, hl]
    exact Real.one_sub_inv_le_log_of_pos hr
  -- `0 ≤ d - l ≤ ρ d²`
  have h3 : d - l ≤ ρ * d ^ 2 := by
    have e : d - d * r⁻¹ = d ^ 2 * r⁻¹ := by
      rw [hd]
      linear_combination (1 - r) * hrr
    have h : d ^ 2 * r⁻¹ ≤ d ^ 2 * ρ := mul_le_mul_of_nonneg_left hr1 (sq_nonneg d)
    linarith
  have h6 : 0 ≤ d - l := sub_nonneg.mpr h1
  -- `d² ≤ ρ² l²`
  have h4 : d ^ 2 ≤ ρ ^ 2 * l ^ 2 := by
    rcases le_total 0 d with hd0 | hd0
    · have hl0 : d * ρ⁻¹ ≤ l := (mul_le_mul_of_nonneg_left hρr hd0).trans h2
      have hdl : d ≤ ρ * l := by
        have h := mul_le_mul_of_nonneg_left hl0 hρ0.le
        rwa [mul_comm d, ← mul_assoc, mul_inv_cancel₀ hρ0.ne', one_mul] at h
      calc d ^ 2 ≤ (ρ * l) ^ 2 := pow_le_pow_left₀ hd0 hdl 2
        _ = ρ ^ 2 * l ^ 2 := mul_pow _ _ _
    · have hl0 : l ≤ 0 := h1.trans hd0
      have h : 0 ≤ (l - d) * (l + d) :=
        mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h1) (add_nonpos hl0 hd0)
      have h' : d ^ 2 ≤ l ^ 2 := by nlinarith
      exact h'.trans (le_mul_of_one_le_left (sq_nonneg l) (one_le_pow₀ hρ))
  -- `|d + l| ≤ (1 + ρ) |d|`
  have h5 : |d + l| ≤ (1 + ρ) * |d| := by
    rcases le_total 0 d with hd0 | hd0
    · have hl0 : 0 ≤ l := (mul_nonneg hd0 hrinv.le).trans h2
      rw [abs_of_nonneg (add_nonneg hd0 hl0), abs_of_nonneg hd0]
      have h := mul_nonneg (sub_nonneg.mpr hρ) hd0
      nlinarith
    · have hl0 : l ≤ 0 := h1.trans hd0
      rw [abs_of_nonpos (add_nonpos hd0 hl0), abs_of_nonpos hd0]
      have h : d * ρ ≤ d * r⁻¹ := mul_le_mul_of_nonpos_left hr1 hd0
      nlinarith
  have h7 : |d ^ 2 - l ^ 2| ≤ ρ * (1 + ρ) * |d| ^ 3 := by
    have e : d ^ 2 - l ^ 2 = (d - l) * (d + l) := by ring
    rw [e, abs_mul, abs_of_nonneg h6]
    calc (d - l) * |d + l| ≤ ρ * d ^ 2 * ((1 + ρ) * |d|) :=
          mul_le_mul h3 h5 (abs_nonneg _) (by positivity)
      _ = ρ * (1 + ρ) * |d| ^ 3 := by
          rw [← sq_abs d]
          ring
  -- `s = N |d|`
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = N * |d| := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by
    rw [hs]
    positivity
  have hs2 : s ^ 2 = (N * d) ^ 2 := by rw [hs, mul_pow, sq_abs, mul_pow]
  have hm1 : s ^ 2 / ρ ^ 2 ≤ (N * d) ^ 2 := by
    rw [← hs2]
    exact div_le_self (sq_nonneg s) (one_le_pow₀ hρ)
  have hm2 : s ^ 2 / ρ ^ 2 ≤ (N * l) ^ 2 := by
    rw [hs2, div_le_iff₀ (by positivity), mul_pow, mul_pow]
    nlinarith [mul_le_mul_of_nonneg_left h4 (sq_nonneg N)]
  have hE := abs_exp_neg_sub_le hm1 hm2
  have hAB : |(N * d) ^ 2 - (N * l) ^ 2| ≤ ρ * (1 + ρ) * (s ^ 3 / N) := by
    have e : (N * d) ^ 2 - (N * l) ^ 2 = N ^ 2 * (d ^ 2 - l ^ 2) := by ring
    have e3 : s ^ 3 / N = N ^ 2 * |d| ^ 3 := by
      rw [hs, div_eq_iff hN.ne']
      ring
    rw [e, abs_mul, abs_of_nonneg (sq_nonneg N), e3]
    calc N ^ 2 * |d ^ 2 - l ^ 2| ≤ N ^ 2 * (ρ * (1 + ρ) * |d| ^ 3) :=
          mul_le_mul_of_nonneg_left h7 (sq_nonneg N)
      _ = ρ * (1 + ρ) * (N ^ 2 * |d| ^ 3) := by ring
  have hP := cube_mul_exp_le hs0 hρ
  have hsplit : Real.exp (-(s ^ 2 / ρ ^ 2)) =
      Real.exp (-(s ^ 2 / (2 * ρ ^ 2))) * Real.exp (-(s ^ 2 / (2 * ρ ^ 2))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc |Real.exp (-(N * d) ^ 2) - Real.exp (-(N * l) ^ 2)|
      ≤ |(N * d) ^ 2 - (N * l) ^ 2| * Real.exp (-(s ^ 2 / ρ ^ 2)) := hE
    _ ≤ ρ * (1 + ρ) * (s ^ 3 / N) * Real.exp (-(s ^ 2 / ρ ^ 2)) :=
        mul_le_mul_of_nonneg_right hAB (Real.exp_pos _).le
    _ = ρ * (1 + ρ) / N * (s ^ 3 * Real.exp (-(s ^ 2 / (2 * ρ ^ 2)))) *
          Real.exp (-(s ^ 2 / (2 * ρ ^ 2))) := by
        rw [hsplit]
        ring
    _ ≤ ρ * (1 + ρ) / N * (8 * ρ ^ 4) * Real.exp (-(s ^ 2 / (2 * ρ ^ 2))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP (by positivity))
          (Real.exp_pos _).le
    _ = 8 * ρ ^ 5 * (1 + ρ) / N * Real.exp (-((N * d) ^ 2 / (2 * ρ ^ 2))) := by
        rw [hs2]
        ring

/-- **Window comparison** in the variables `v` (centre), `w` (point) and `H` (width). -/
theorem window_compare {H v w ρ : ℝ} (hH : 0 < H) (hv : 0 < v) (hw : 0 < w) (hρ : 1 ≤ ρ)
    (h1 : v ≤ ρ * w) (h2 : w ≤ ρ * v) :
    |Real.exp (-(1 / H ^ 2) * (w - v) ^ 2) -
        Real.exp (-(v / H) ^ 2 * (Real.log w - Real.log v) ^ 2)| ≤
      8 * ρ ^ 5 * (1 + ρ) * (H / v) *
        Real.exp (-(1 / (2 * ρ ^ 2 * H ^ 2)) * (w - v) ^ 2) := by
  have hr1 : (w / v)⁻¹ ≤ ρ := by
    rw [inv_div, div_le_iff₀ hw]
    exact h1
  have hr2 : w / v ≤ ρ := by
    rw [div_le_iff₀ hv]
    exact h2
  have key := window_normalized (div_pos hv hH) (div_pos hw hv) hρ hr1 hr2
  have hv' : v * v⁻¹ = 1 := mul_inv_cancel₀ hv.ne'
  have e1 : v / H * (w / v - 1) = (w - v) / H := by
    linear_combination (H⁻¹ * w) * hv'
  have e2 : -((w - v) / H) ^ 2 = -(1 / H ^ 2) * (w - v) ^ 2 := by ring
  have e3 : -(v / H * Real.log (w / v)) ^ 2 =
      -(v / H) ^ 2 * (Real.log w - Real.log v) ^ 2 := by
    rw [Real.log_div hw.ne' hv.ne']
    ring
  have e4 : 8 * ρ ^ 5 * (1 + ρ) / (v / H) = 8 * ρ ^ 5 * (1 + ρ) * (H / v) := by
    rw [div_div_eq_mul_div, mul_div_assoc]
  have e5 : -(((w - v) / H) ^ 2 / (2 * ρ ^ 2)) =
      -(1 / (2 * ρ ^ 2 * H ^ 2)) * (w - v) ^ 2 := by ring
  rw [e1, e2, e3, e4, e5] at key
  exact key

/-- The additive window far from its centre: if `|D| ≥ a₁Y/2` then
`e^{-D²/H²} ≤ (2/a₁)(H/Y) e^{-D²/(2ρ²H²)}`. -/
theorem window_tail {H Y a₁ ρ D : ℝ} (hH : 0 < H) (hY : 0 < Y) (ha₁ : 0 < a₁) (hρ : 1 ≤ ρ)
    (hD : a₁ * Y / 2 ≤ |D|) :
    Real.exp (-(1 / H ^ 2) * D ^ 2) ≤
      2 / a₁ * (H / Y) * Real.exp (-(1 / (2 * ρ ^ 2 * H ^ 2)) * D ^ 2) := by
  have hlo : 0 < a₁ * Y / 2 := by positivity
  have hD0 : 0 < |D| := lt_of_lt_of_le hlo hD
  have hx : 0 < |D| / H := div_pos hD0 hH
  have h1 : Real.exp (-((|D| / H) ^ 2 / 2)) ≤ 2 / a₁ * (H / Y) := by
    calc Real.exp (-((|D| / H) ^ 2 / 2)) ≤ 1 / (|D| / H) := exp_neg_sq_half_le hx
      _ = H / |D| := one_div_div _ _
      _ ≤ H / (a₁ * Y / 2) := div_le_div_of_nonneg_left hH.le hlo hD
      _ = 2 / a₁ * (H / Y) := by
          rw [div_div_eq_mul_div, div_mul_div_comm, mul_comm H 2]
  have h2 : Real.exp (-((|D| / H) ^ 2 / 2)) ≤
      Real.exp (-(1 / (2 * ρ ^ 2 * H ^ 2)) * D ^ 2) := by
    refine Real.exp_le_exp.mpr ?_
    have e : (|D| / H) ^ 2 / 2 = D ^ 2 / (2 * H ^ 2) := by
      rw [div_pow, sq_abs]
      ring
    have h : D ^ 2 / (2 * ρ ^ 2 * H ^ 2) ≤ D ^ 2 / (2 * H ^ 2) := by
      refine div_le_div_of_nonneg_left (sq_nonneg D) (by positivity) ?_
      have h3 := mul_le_mul_of_nonneg_right (one_le_pow₀ hρ (n := 2)) (sq_nonneg H)
      linarith
    have e' : -(1 / (2 * ρ ^ 2 * H ^ 2)) * D ^ 2 = -(D ^ 2 / (2 * ρ ^ 2 * H ^ 2)) := by ring
    rw [e, e']
    exact neg_le_neg h
  have hsplit : Real.exp (-(1 / H ^ 2) * D ^ 2) =
      Real.exp (-((|D| / H) ^ 2 / 2)) * Real.exp (-((|D| / H) ^ 2 / 2)) := by
    rw [← Real.exp_add, div_pow, sq_abs]
    congr 1
    ring
  rw [hsplit]
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)

/-- The constant of the window comparison (`ρ = 2a₂/a₁`). -/
def winConst (a₁ a₂ : ℝ) : ℝ :=
  16 * (2 * a₂ / a₁) ^ 5 * (1 + 2 * a₂ / a₁) / a₁ + 2 / a₁

theorem winConst_nonneg {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₁₂ : a₁ ≤ a₂) : 0 ≤ winConst a₁ a₂ := by
  have ha₂ : 0 < a₂ := lt_of_lt_of_le ha₁ ha₁₂
  unfold winConst
  positivity

theorem one_le_ratio {a₁ a₂ : ℝ} (ha₁ : 0 < a₁) (ha₁₂ : a₁ ≤ a₂) : 1 ≤ 2 * a₂ / a₁ := by
  rw [le_div_iff₀ ha₁]
  linarith

/-- **The two windows agree up to `O(H/Y)` on the relevant centres**: for `w ∈ [a₁Y, a₂Y]` and
`v ∈ [a₁Y/2, 2a₂Y]`. -/
theorem window_in {a₁ a₂ H Y v w : ℝ} (ha₁ : 0 < a₁) (ha₁₂ : a₁ ≤ a₂) (hH : 0 < H) (hY : 0 < Y)
    (hw : a₁ * Y ≤ w ∧ w ≤ a₂ * Y) (hv : a₁ * Y / 2 ≤ v ∧ v ≤ 2 * a₂ * Y) :
    |Real.exp (-(1 / H ^ 2) * (w - v) ^ 2) -
        Real.exp (-(v / H) ^ 2 * (Real.log w - Real.log v) ^ 2)| ≤
      winConst a₁ a₂ * (H / Y) *
        Real.exp (-(1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2)) * (w - v) ^ 2) := by
  have ha₂ : 0 < a₂ := lt_of_lt_of_le ha₁ ha₁₂
  have hρ := one_le_ratio ha₁ ha₁₂
  have hρ0 : (0 : ℝ) ≤ 2 * a₂ / a₁ := by positivity
  have hlo : 0 < a₁ * Y / 2 := by positivity
  have hv0 : 0 < v := lt_of_lt_of_le hlo hv.1
  have hw0 : 0 < w := lt_of_lt_of_le (by positivity) hw.1
  have ha : a₁ * a₁⁻¹ = 1 := mul_inv_cancel₀ ha₁.ne'
  have e1 : 2 * a₂ / a₁ * (a₁ * Y) = 2 * a₂ * Y := by
    linear_combination (2 * a₂ * Y) * ha
  have e2 : 2 * a₂ / a₁ * (a₁ * Y / 2) = a₂ * Y := by
    linear_combination (a₂ * Y) * ha
  have h1 : v ≤ 2 * a₂ / a₁ * w := by
    have h := mul_le_mul_of_nonneg_left hw.1 hρ0
    rw [e1] at h
    exact hv.2.trans h
  have h2 : w ≤ 2 * a₂ / a₁ * v := by
    have h := mul_le_mul_of_nonneg_left hv.1 hρ0
    rw [e2] at h
    exact hw.2.trans h
  have key := window_compare hH hv0 hw0 hρ h1 h2
  have hHv : H / v ≤ 2 / a₁ * (H / Y) := by
    calc H / v ≤ H / (a₁ * Y / 2) := div_le_div_of_nonneg_left hH.le hlo hv.1
      _ = 2 / a₁ * (H / Y) := by rw [div_div_eq_mul_div, div_mul_div_comm, mul_comm H 2]
  have hE : 0 ≤ Real.exp (-(1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2)) * (w - v) ^ 2) :=
    (Real.exp_pos _).le
  refine key.trans (mul_le_mul_of_nonneg_right ?_ hE)
  have hc : 0 ≤ 8 * (2 * a₂ / a₁) ^ 5 * (1 + 2 * a₂ / a₁) := by positivity
  have hHY : 0 ≤ H / Y := by positivity
  calc 8 * (2 * a₂ / a₁) ^ 5 * (1 + 2 * a₂ / a₁) * (H / v)
      ≤ 8 * (2 * a₂ / a₁) ^ 5 * (1 + 2 * a₂ / a₁) * (2 / a₁ * (H / Y)) :=
        mul_le_mul_of_nonneg_left hHv hc
    _ = 16 * (2 * a₂ / a₁) ^ 5 * (1 + 2 * a₂ / a₁) / a₁ * (H / Y) := by ring
    _ ≤ winConst a₁ a₂ * (H / Y) := by
        refine mul_le_mul_of_nonneg_right ?_ hHY
        unfold winConst
        have h : 0 ≤ 2 / a₁ := by positivity
        linarith

/-- **Only `v ≍ Y` contributes**: for a centre `v ∉ [a₁Y/2, 2a₂Y]` the additive window at
`w ∈ [a₁Y, a₂Y]` is `O(H/Y)` times a wider Gaussian. -/
theorem window_out {a₁ a₂ H Y v w : ℝ} (ha₁ : 0 < a₁) (ha₁₂ : a₁ ≤ a₂) (hH : 0 < H) (hY : 0 < Y)
    (hw : a₁ * Y ≤ w ∧ w ≤ a₂ * Y) (hv : v < a₁ * Y / 2 ∨ 2 * a₂ * Y < v) :
    Real.exp (-(1 / H ^ 2) * (w - v) ^ 2) ≤
      winConst a₁ a₂ * (H / Y) *
        Real.exp (-(1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2)) * (w - v) ^ 2) := by
  have ha₂ : 0 < a₂ := lt_of_lt_of_le ha₁ ha₁₂
  have hρ := one_le_ratio ha₁ ha₁₂
  have h0 : 0 ≤ a₁ * Y := by positivity
  have hD : a₁ * Y / 2 ≤ |w - v| := by
    rcases hv with hv | hv
    · exact le_trans (by linarith [hw.1]) (le_abs_self _)
    · have h := mul_le_mul_of_nonneg_right ha₁₂ hY.le
      rw [abs_sub_comm]
      exact le_trans (by linarith [hw.2]) (le_abs_self _)
  have key := window_tail hH hY ha₁ hρ hD
  have hE : 0 ≤ Real.exp (-(1 / (2 * (2 * a₂ / a₁) ^ 2 * H ^ 2)) * (w - v) ^ 2) :=
    (Real.exp_pos _).le
  have hHY : 0 ≤ H / Y := by positivity
  refine key.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hHY) hE)
  unfold winConst
  have h : 0 ≤ 16 * (2 * a₂ / a₁) ^ 5 * (1 + 2 * a₂ / a₁) / a₁ := by positivity
  linarith

/-! ### Gaussian sums over integers -/

/-- **The `O(H)` available `w`**: a Gaussian sum over distinct integers is at most the Gaussian
integral, `∑_w e^{-g(w-v)²} ≤ e^{g/4} √(π/(g/2))`. -/
theorem gauss_sum_le (s : Finset ℕ) {g lo hi : ℝ} (hg : 0 < g) (hlohi : lo ≤ hi)
    (hs : ∀ w ∈ s, lo ≤ (w : ℝ) ∧ (w : ℝ) ≤ hi) (v : ℝ) :
    ∑ w ∈ s, Real.exp (-g * ((w : ℝ) - v) ^ 2) ≤
      Real.exp (g / 4) * Real.sqrt (Real.pi / (g / 2)) := by
  have hg2 : 0 < g / 2 := half_pos hg
  have hcont : Continuous fun x : ℝ => Real.exp (-(g / 2) * (v - x) ^ 2) := by fun_prop
  have hh0 : ∀ x : ℝ, 0 ≤ Real.exp (-(g / 2) * (v - x) ^ 2) := fun x => (Real.exp_pos _).le
  -- each term against the integral over the unit interval around `w`
  have hterm : ∀ w : ℕ, Real.exp (-g * ((w : ℝ) - v) ^ 2) ≤ Real.exp (g / 4) *
      ∫ x in ((w : ℝ) - 1 / 2)..((w : ℝ) + 1 / 2), Real.exp (-(g / 2) * (v - x) ^ 2) := by
    intro w
    have hle : (w : ℝ) - 1 / 2 ≤ (w : ℝ) + 1 / 2 := by linarith
    have hmono : (∫ _ in ((w : ℝ) - 1 / 2)..((w : ℝ) + 1 / 2),
          Real.exp (-g * ((w : ℝ) - v) ^ 2 - g / 4)) ≤
        ∫ x in ((w : ℝ) - 1 / 2)..((w : ℝ) + 1 / 2), Real.exp (-(g / 2) * (v - x) ^ 2) := by
      refine intervalIntegral.integral_mono_on hle intervalIntegrable_const
        (hcont.intervalIntegrable _ _) fun x hx => ?_
      refine Real.exp_le_exp.mpr ?_
      have h1 : (x - (w : ℝ)) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
        sq_le_sq' (by linarith [hx.1]) (by linarith [hx.2])
      have h1' : ((1 : ℝ) / 2) ^ 2 = 1 / 4 := by norm_num
      have h3 : (v - x) ^ 2 ≤ 2 * ((w : ℝ) - v) ^ 2 + 2 * (x - (w : ℝ)) ^ 2 := by
        nlinarith [sq_nonneg ((w : ℝ) - v - (x - (w : ℝ)))]
      have h4 : (v - x) ^ 2 ≤ 2 * ((w : ℝ) - v) ^ 2 + 1 / 2 := by linarith
      have h5 := mul_le_mul_of_nonneg_left h4 hg2.le
      linarith
    have hconst : (∫ _ in ((w : ℝ) - 1 / 2)..((w : ℝ) + 1 / 2),
        Real.exp (-g * ((w : ℝ) - v) ^ 2 - g / 4)) =
        Real.exp (-g * ((w : ℝ) - v) ^ 2 - g / 4) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      have e : (w : ℝ) + 1 / 2 - ((w : ℝ) - 1 / 2) = 1 := by ring
      rw [e, one_mul]
    rw [hconst] at hmono
    calc Real.exp (-g * ((w : ℝ) - v) ^ 2)
        = Real.exp (g / 4) * Real.exp (-g * ((w : ℝ) - v) ^ 2 - g / 4) := by
          rw [← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (g / 4) *
          ∫ x in ((w : ℝ) - 1 / 2)..((w : ℝ) + 1 / 2), Real.exp (-(g / 2) * (v - x) ^ 2) :=
          mul_le_mul_of_nonneg_left hmono (Real.exp_pos _).le
  -- the unit intervals around distinct integers are disjoint
  have hsum : ∑ w ∈ s, ∫ x in ((w : ℝ) - 1 / 2)..((w : ℝ) + 1 / 2),
        Real.exp (-(g / 2) * (v - x) ^ 2) ≤
      ∫ x in (lo - 1 / 2)..(hi + 1 / 2), Real.exp (-(g / 2) * (v - x) ^ 2) := by
    have h := Classical.sum_integral_unit_interval_le hcont hh0 hlohi
      (s.image fun w : ℕ => (w : ℝ))
      (by
        intro t ht
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ht
        exact ⟨(hs w hw).1, (hs w hw).2⟩)
      (by
        intro t ht t' ht' hne
        obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp ht
        obtain ⟨w', -, rfl⟩ := Finset.mem_image.mp ht'
        have hww' : (w : ℤ) - (w' : ℤ) ≠ 0 := by
          intro h0
          apply hne
          have h1 : (w : ℤ) = (w' : ℤ) := sub_eq_zero.mp h0
          exact_mod_cast h1
        have h1 : (1 : ℤ) ≤ |(w : ℤ) - (w' : ℤ)| := Int.one_le_abs hww'
        have h2 : ((1 : ℤ) : ℝ) ≤ ((|(w : ℤ) - (w' : ℤ)| : ℤ) : ℝ) := Int.cast_le.mpr h1
        rw [Int.cast_one, Int.cast_abs, Int.cast_sub, Int.cast_natCast, Int.cast_natCast] at h2
        exact h2)
    rw [Finset.sum_image (Nat.cast_injective (R := ℝ)).injOn] at h
    exact h
  have htotal : ∫ x in (lo - 1 / 2)..(hi + 1 / 2), Real.exp (-(g / 2) * (v - x) ^ 2) ≤
      Real.sqrt (Real.pi / (g / 2)) := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_gauss (g := g / 2) v]
    exact setIntegral_le_integral (integrable_gauss hg2 v) (ae_of_all _ hh0)
  calc ∑ w ∈ s, Real.exp (-g * ((w : ℝ) - v) ^ 2)
      ≤ ∑ w ∈ s, Real.exp (g / 4) *
          ∫ x in ((w : ℝ) - 1 / 2)..((w : ℝ) + 1 / 2), Real.exp (-(g / 2) * (v - x) ^ 2) :=
        Finset.sum_le_sum fun w _ => hterm w
    _ = Real.exp (g / 4) * ∑ w ∈ s,
          ∫ x in ((w : ℝ) - 1 / 2)..((w : ℝ) + 1 / 2), Real.exp (-(g / 2) * (v - x) ^ 2) := by
        rw [Finset.mul_sum]
    _ ≤ Real.exp (g / 4) * Real.sqrt (Real.pi / (g / 2)) :=
        mul_le_mul_of_nonneg_left (hsum.trans htotal) (Real.exp_pos _).le

end LocalMellinAux

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
