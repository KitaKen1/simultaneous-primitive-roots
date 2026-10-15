module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ModelInterchange

/-!
# Tools for the low-frequency step

The rearrangements of `[P-06:0646–0679]`, for an arbitrary weight `Φ` on the integers of
`[a₁ Y, a₂ Y]` (in the application `Φ(w) = ψ_1(w/Y) w^{i(t+σ)} e(hw/k)`).

* `sum_filter_dvd_natIcc_eq`: the change of variables `w = m n` on the multiples of `m`.
* `sum_normSq_natIcc_le_of_dyadic`, `sum_norm_le_of_sum_normSq`, `norm_sum_mul_le_of_dyadic`:
  "Cauchy and (cor:model-error)": from `∑_{n ≍ R'} |E(n)|² ≤ B_E R'` on every dyad,
  `|∑_{a₁ Y/m ≤ n ≤ a₂ Y/m} Φ(m n) E(n)| ≤ (1/m) · P_b (λ 2^{J+1} B_E a₁ Y + a₂ Y / λ) / 2`
  (with `2|E| ≤ λ |E|² + 1/λ` in place of Cauchy's inequality).
* `scaleSum Φ H a₁ a₂ Y m = ∑_{a₁ Y/m ≤ n ≤ a₂ Y/m} Φ(m n) H(n)`: "In a tuple term put
  `w = l n`"; `scaleSum_divisorSum`: for a divisor sum `H_0 = ∑_{e ∣ n} A_e`,
  `scaleSum Φ H_0 … m = ∑_e A_e ∑_v Φ(m e v)`; `norm_scaleSum_sub_main_le`: one scale, from the
  main terms `∑_v Φ(m e v) = (Y/(m e)) G + O(Err_L)` and the model error.
* `sum_card_filter_dvd_mul`: `∑_w #{𝔩 : l_𝔩 ∣ w} g(w) = ∑_𝔩 ∑_n g(l_𝔩 n)`.
* `norm_sum_scale_sub_le`: "The main term depends on `l` only through `1/l`. Its tuple sum is
  exactly `C_x` times the main term for the subtracted constant. They cancel."
* `eventually_rpow_neg_mul_exp_mul_rpow_le_one`: `x^{-δ} exp(c L^{.47}) L^b ≤ 1` for large `x`
  ("The summed errors in (cor:low-main-term) are therefore `O(x^{-ε+o(1)})`").
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open Filter
open scoped Topology

noncomputable section

/-! ### Integer ranges -/

theorem natIcc_subset_natIcc {a a' b b' : ℝ} (ha : a' ≤ a) (hb : b ≤ b') :
    natIcc a b ⊆ natIcc a' b' := by
  unfold natIcc
  exact Finset.Icc_subset_Icc (Nat.ceil_mono ha) (Nat.floor_mono hb)

/-- `[a, b]` contains at most `b` integers when `a > 0`. -/
theorem card_natIcc_le {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) : ((natIcc a b).card : ℝ) ≤ b := by
  have h2 : (natIcc a b).card ≤ ⌊b⌋₊ := by
    unfold natIcc
    rw [Nat.card_Icc]
    have h3 : 0 < ⌈a⌉₊ := Nat.ceil_pos.mpr ha
    omega
  exact (Nat.cast_le.mpr h2).trans (Nat.floor_le hb)

theorem ne_zero_of_mem_natIcc {a b : ℝ} (ha : 0 < a) {n : ℕ} (hn : n ∈ natIcc a b) : n ≠ 0 := by
  intro h0
  have h := ((mem_natIcc_of_pos ha).mp hn).1
  rw [h0, Nat.cast_zero] at h
  exact absurd h (not_le.mpr ha)

/-- The change of variables `w = m n` on the multiples of `m` in `[R₁, R₂]`. -/
theorem sum_filter_dvd_natIcc_eq {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) {m : ℕ} (hm : 0 < m) (g : ℕ → ℂ) :
    ∑ w ∈ (natIcc R₁ R₂).filter (fun w => m ∣ w), g w =
      ∑ n ∈ natIcc (R₁ / (m : ℝ)) (R₂ / (m : ℝ)), g (m * n) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hR₁m : 0 < R₁ / (m : ℝ) := div_pos hR₁ hm'
  refine Finset.sum_nbij' (fun w => w / m) (fun n => m * n) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    obtain ⟨hw1, hdvd⟩ := Finset.mem_filter.mp hw
    obtain ⟨c, rfl⟩ := hdvd
    obtain ⟨h1, h2⟩ := (mem_natIcc_of_pos hR₁).mp hw1
    rw [Nat.cast_mul] at h1 h2
    have hc : m * c / m = c := Nat.mul_div_cancel_left c hm
    show m * c / m ∈ _
    rw [hc]
    refine (mem_natIcc_of_pos hR₁m).mpr ⟨?_, ?_⟩
    · rw [div_le_iff₀ hm']
      linarith
    · rw [le_div_iff₀ hm']
      linarith
  · intro n hn
    obtain ⟨h1, h2⟩ := (mem_natIcc_of_pos hR₁m).mp hn
    rw [div_le_iff₀ hm'] at h1
    rw [le_div_iff₀ hm'] at h2
    show m * n ∈ _
    refine Finset.mem_filter.mpr ⟨(mem_natIcc_of_pos hR₁).mpr ⟨?_, ?_⟩, dvd_mul_right m n⟩
    · rw [Nat.cast_mul]
      linarith
    · rw [Nat.cast_mul]
      linarith
  · intro w hw
    exact Nat.mul_div_cancel' (Finset.mem_filter.mp hw).2
  · intro n _
    exact Nat.mul_div_cancel_left n hm
  · intro w hw
    show g w = g (m * (w / m))
    rw [Nat.mul_div_cancel' (Finset.mem_filter.mp hw).2]

/-! ### From mean squares on dyads to a sum -/

/-- A sum of squares over the integers of `[R, r]`, `r ≤ 2^J R`, from bounds on the dyads
`[2^j R, 2^{j+1} R]`, `j ≤ J`. -/
theorem sum_normSq_natIcc_le_of_dyadic (E : ℕ → ℂ) {R B : ℝ} (hR : 0 < R) (hB : 0 ≤ B) (J : ℕ)
    (h : ∀ j : ℕ, j ≤ J →
      ∑ n ∈ natIcc (2 ^ j * R) (2 * (2 ^ j * R)), ‖E n‖ ^ 2 ≤ 2 ^ j * B)
    {r : ℝ} (hr : r ≤ 2 ^ J * R) :
    ∑ n ∈ natIcc R r, ‖E n‖ ^ 2 ≤ 2 ^ (J + 1) * B := by
  have hnorm : ∀ l r' : ℝ, ‖∑ n ∈ natIcc l r', ((‖E n‖ ^ 2 : ℝ) : ℂ)‖ =
      ∑ n ∈ natIcc l r', ‖E n‖ ^ 2 := by
    intro l r'
    rw [← Complex.ofReal_sum, Complex.norm_real]
    exact Real.norm_of_nonneg (Finset.sum_nonneg fun n _ => sq_nonneg _)
  have hdy : ∀ j : ℕ, j ≤ J → ∀ l r' : ℝ, 2 ^ j * R ≤ l → l ≤ r' → r' ≤ 2 * (2 ^ j * R) →
      ‖∑ n ∈ natIcc l r', ((‖E n‖ ^ 2 : ℝ) : ℂ)‖ ≤ 2 ^ j * B := by
    intro j hj l r' hl _ hr'
    rw [hnorm]
    exact (Finset.sum_le_sum_of_subset_of_nonneg (natIcc_subset_natIcc hl hr')
      fun n _ _ => sq_nonneg _).trans (h j hj)
  have hmain : ‖∑ n ∈ natIcc R r, ((‖E n‖ ^ 2 : ℝ) : ℂ)‖ ≤ 2 ^ (J + 1) * B :=
    norm_sum_natIcc_le_of_dyadic (fun n => ((‖E n‖ ^ 2 : ℝ) : ℂ)) hR hB J hdy R r le_rfl hr
  rw [hnorm] at hmain
  exact hmain

/-- `2a ≤ λ a² + 1/λ` for `λ > 0`. -/
theorem two_mul_le_mul_sq_add_inv {lam : ℝ} (hlam : 0 < lam) (a : ℝ) :
    2 * a ≤ lam * a ^ 2 + lam⁻¹ := by
  have h := mul_nonneg hlam.le (sq_nonneg (a - lam⁻¹))
  have e : lam * (a - lam⁻¹) ^ 2 =
      lam * a ^ 2 - 2 * a * (lam * lam⁻¹) + lam * lam⁻¹ * lam⁻¹ := by ring
  rw [e, mul_inv_cancel₀ hlam.ne', mul_one, one_mul] at h
  linarith

/-- `2 ∑ |E(n)| ≤ λ ∑ |E(n)|² + #s / λ`. -/
theorem sum_norm_le_of_sum_normSq (s : Finset ℕ) (E : ℕ → ℂ) {lam : ℝ} (hlam : 0 < lam) :
    2 * ∑ n ∈ s, ‖E n‖ ≤ lam * ∑ n ∈ s, ‖E n‖ ^ 2 + (s.card : ℝ) * lam⁻¹ := by
  have h1 : ∑ n ∈ s, 2 * ‖E n‖ ≤ ∑ n ∈ s, (lam * ‖E n‖ ^ 2 + lam⁻¹) :=
    Finset.sum_le_sum fun n _ => two_mul_le_mul_sq_add_inv hlam ‖E n‖
  have h2 : ∑ n ∈ s, (lam * ‖E n‖ ^ 2 + lam⁻¹) =
      lam * ∑ n ∈ s, ‖E n‖ ^ 2 + (s.card : ℝ) * lam⁻¹ := by
    rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  rw [Finset.mul_sum]
  exact h1.trans (le_of_eq h2)

/-- **The model error at one scale** ("Cauchy and (cor:model-error)"): if
`∑_{R' ≤ n ≤ 2R'} |E(n)|² ≤ B_E R'` for every `R' ≥ 1` and `|Φ| ≤ P_b`, then for `m ≤ a₁ Y` and
`λ > 0`,
`|∑_{a₁ Y/m ≤ n ≤ a₂ Y/m} Φ(m n) E(n)| ≤ (1/m) P_b (λ 2^{J+1} B_E a₁ Y + a₂ Y/λ)/2`,
`J = ⌈a₂/a₁⌉`. -/
theorem norm_sum_mul_le_of_dyadic {Φ E : ℕ → ℂ} {a₁ a₂ Y BE Pb lam : ℝ} {m : ℕ}
    (ha₁ : 0 < a₁) (ha₂ : a₁ ≤ a₂) (hY : 0 < Y) (hm : 0 < m) (hmY : (m : ℝ) ≤ a₁ * Y)
    (hBE : 0 ≤ BE) (hPb : 0 ≤ Pb) (hlam : 0 < lam)
    (hdy : ∀ R' : ℝ, 1 ≤ R' → ∑ n ∈ natIcc R' (2 * R'), ‖E n‖ ^ 2 ≤ BE * R')
    (hΦ : ∀ w : ℕ, 0 < w → ‖Φ w‖ ≤ Pb) :
    ‖∑ n ∈ natIcc (a₁ * Y / (m : ℝ)) (a₂ * Y / (m : ℝ)), Φ (m * n) * E n‖ ≤
      Pb * (lam * (2 ^ (⌈a₂ / a₁⌉₊ + 1) * (BE * (a₁ * Y))) + a₂ * Y * lam⁻¹) / 2 /
        (m : ℝ) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have ha₂0 : 0 < a₂ := lt_of_lt_of_le ha₁ ha₂
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = a₁ * Y / (m : ℝ) := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = a₂ * Y / (m : ℝ) := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by
    rw [hRdef, le_div_iff₀ hm', one_mul]
    exact hmY
  have hR0 : 0 < R := by linarith
  have hr0 : 0 ≤ r := by
    rw [hrdef]
    exact div_nonneg (mul_nonneg ha₂0.le hY.le) hm'.le
  -- `r ≤ 2^J R`
  have hrR : r ≤ 2 ^ ⌈a₂ / a₁⌉₊ * R := by
    have h1 : a₂ / a₁ ≤ (⌈a₂ / a₁⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈a₂ / a₁⌉₊ : ℝ) ≤ (2 : ℝ) ^ ⌈a₂ / a₁⌉₊ := by
      exact_mod_cast (Nat.lt_two_pow_self : ⌈a₂ / a₁⌉₊ < 2 ^ ⌈a₂ / a₁⌉₊).le
    have e : r = a₂ / a₁ * R := by
      have e1 : a₂ / a₁ * (a₁ * Y / (m : ℝ)) = a₂ / a₁ * a₁ * Y / (m : ℝ) := by ring
      rw [hrdef, hRdef, e1, div_mul_cancel₀ _ ha₁.ne']
    rw [e]
    exact mul_le_mul_of_nonneg_right (h1.trans h2) hR0.le
  -- the mean square
  have hsq : ∑ n ∈ natIcc R r, ‖E n‖ ^ 2 ≤ 2 ^ (⌈a₂ / a₁⌉₊ + 1) * (BE * R) :=
    sum_normSq_natIcc_le_of_dyadic E hR0 (mul_nonneg hBE hR0.le) _ (fun j _ => by
      have hj1 : (1 : ℝ) ≤ 2 ^ j * R :=
        calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
          _ ≤ 2 ^ j * R :=
              mul_le_mul (one_le_pow₀ one_le_two) hR1 zero_le_one (pow_nonneg zero_le_two j)
      calc ∑ n ∈ natIcc (2 ^ j * R) (2 * (2 ^ j * R)), ‖E n‖ ^ 2
          ≤ BE * (2 ^ j * R) := hdy _ hj1
        _ = 2 ^ j * (BE * R) := by ring) hrR
  have hcard : ((natIcc R r).card : ℝ) ≤ r := card_natIcc_le hR0 hr0
  have hsum : 2 * ∑ n ∈ natIcc R r, ‖E n‖ ≤
      lam * (2 ^ (⌈a₂ / a₁⌉₊ + 1) * (BE * R)) + r * lam⁻¹ := by
    have h1 := sum_norm_le_of_sum_normSq (natIcc R r) E hlam
    have h2 : lam * ∑ n ∈ natIcc R r, ‖E n‖ ^ 2 ≤
        lam * (2 ^ (⌈a₂ / a₁⌉₊ + 1) * (BE * R)) := mul_le_mul_of_nonneg_left hsq hlam.le
    have h3 : ((natIcc R r).card : ℝ) * lam⁻¹ ≤ r * lam⁻¹ :=
      mul_le_mul_of_nonneg_right hcard (inv_nonneg.mpr hlam.le)
    linarith
  have hΦE : ‖∑ n ∈ natIcc R r, Φ (m * n) * E n‖ ≤ Pb * ∑ n ∈ natIcc R r, ‖E n‖ :=
    calc ‖∑ n ∈ natIcc R r, Φ (m * n) * E n‖
        ≤ ∑ n ∈ natIcc R r, ‖Φ (m * n) * E n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ natIcc R r, Pb * ‖E n‖ := Finset.sum_le_sum fun n hn => by
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right
            (hΦ (m * n) (Nat.mul_pos hm (Nat.pos_of_ne_zero (ne_zero_of_mem_natIcc hR0 hn))))
            (norm_nonneg _)
      _ = Pb * ∑ n ∈ natIcc R r, ‖E n‖ := (Finset.mul_sum _ _ _).symm
  have e : Pb * (lam * (2 ^ (⌈a₂ / a₁⌉₊ + 1) * (BE * (a₁ * Y))) + a₂ * Y * lam⁻¹) / 2 /
        (m : ℝ) =
      Pb * ((lam * (2 ^ (⌈a₂ / a₁⌉₊ + 1) * (BE * R)) + r * lam⁻¹) / 2) := by
    rw [hRdef, hrdef]
    ring
  rw [e, ← hRdef, ← hrdef]
  refine hΦE.trans (mul_le_mul_of_nonneg_left ?_ hPb)
  linarith

/-! ### One scale -/

/-- `T(m) = ∑_{a₁ Y/m ≤ n ≤ a₂ Y/m} Φ(m n) H(n)`: the sum over `w = m n` of `Φ(w) H(w/m)`. -/
def scaleSum (Φ H : ℕ → ℂ) (a₁ a₂ Y : ℝ) (m : ℕ) : ℂ :=
  ∑ n ∈ natIcc (a₁ * Y / (m : ℝ)) (a₂ * Y / (m : ℝ)), Φ (m * n) * H n

/-- For a divisor sum `H_0(n) = ∑_{e ∣ n} A_e` and a weight supported on `[a₁ Y, a₂ Y]`:
`T(m) = ∑_e A_e ∑_v Φ(m e v)`. -/
theorem scaleSum_divisorSum {Φ : ℕ → ℂ} {a₁ a₂ Y : ℝ} (ha₁ : 0 < a₁) (hY : 0 < Y)
    (hΦ : ∀ w : ℕ, Φ w ≠ 0 → a₁ * Y ≤ (w : ℝ) ∧ (w : ℝ) ≤ a₂ * Y)
    (A : ℕ → ℂ) {E : ℕ} (hA : ∀ e : ℕ, A e ≠ 0 → e ∈ Finset.Icc 1 E) {m : ℕ} (hm : 0 < m) :
    scaleSum Φ (divisorSum A) a₁ a₂ Y m =
      ∑ e ∈ Finset.Icc 1 E, A e * ∑ᶠ v : ℕ, Φ (m * e * v) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm
  have hR₁ : 0 < a₁ * Y / (m : ℝ) := div_pos (mul_pos ha₁ hY) hm'
  have h1 : ∀ n ∈ natIcc (a₁ * Y / (m : ℝ)) (a₂ * Y / (m : ℝ)),
      Φ (m * n) * divisorSum A n =
        ∑ e ∈ Finset.Icc 1 E, if e ∣ n then A e * Φ (m * n) else 0 := by
    intro n hn
    rw [divisorSum_eq_sum_Icc hA (ne_zero_of_mem_natIcc hR₁ hn), Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases hd : e ∣ n
    · rw [if_pos hd, if_pos hd]
      exact mul_comm _ _
    · rw [if_neg hd, if_neg hd, mul_zero]
  have h2 : ∀ e ∈ Finset.Icc 1 E,
      ∑ n ∈ natIcc (a₁ * Y / (m : ℝ)) (a₂ * Y / (m : ℝ)),
          (if e ∣ n then A e * Φ (m * n) else 0) =
        A e * ∑ᶠ v : ℕ, Φ (m * e * v) := by
    intro e he
    have he0 : 0 < e := by
      have h := (Finset.mem_Icc.mp he).1
      omega
    have he' : (0 : ℝ) < (e : ℝ) := Nat.cast_pos.mpr he0
    have hsupp : Function.support (fun v : ℕ => Φ (m * e * v)) ⊆
        ↑(natIcc (a₁ * Y / (m : ℝ) / (e : ℝ)) (a₂ * Y / (m : ℝ) / (e : ℝ))) := by
      intro v hv
      obtain ⟨h3, h4⟩ := hΦ (m * e * v) (Function.mem_support.mp hv)
      rw [Nat.cast_mul, Nat.cast_mul] at h3 h4
      refine Finset.mem_coe.mpr ((mem_natIcc_of_pos (div_pos hR₁ he')).mpr ⟨?_, ?_⟩)
      · rw [div_le_iff₀ he', div_le_iff₀ hm']
        linarith
      · rw [le_div_iff₀ he', le_div_iff₀ hm']
        linarith
    calc ∑ n ∈ natIcc (a₁ * Y / (m : ℝ)) (a₂ * Y / (m : ℝ)),
          (if e ∣ n then A e * Φ (m * n) else 0)
        = ∑ n ∈ (natIcc (a₁ * Y / (m : ℝ)) (a₂ * Y / (m : ℝ))).filter (fun n => e ∣ n),
            A e * Φ (m * n) := (Finset.sum_filter _ _).symm
      _ = ∑ v ∈ natIcc (a₁ * Y / (m : ℝ) / (e : ℝ)) (a₂ * Y / (m : ℝ) / (e : ℝ)),
            A e * Φ (m * (e * v)) :=
          sum_filter_dvd_natIcc_eq hR₁ he0 (fun n => A e * Φ (m * n))
      _ = A e * ∑ v ∈ natIcc (a₁ * Y / (m : ℝ) / (e : ℝ)) (a₂ * Y / (m : ℝ) / (e : ℝ)),
            Φ (m * e * v) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun v _ => by rw [mul_assoc]
      _ = A e * ∑ᶠ v : ℕ, Φ (m * e * v) := by
          rw [finsum_eq_sum_of_support_subset _ hsupp]
  unfold scaleSum
  calc ∑ n ∈ natIcc (a₁ * Y / (m : ℝ)) (a₂ * Y / (m : ℝ)), Φ (m * n) * divisorSum A n
      = ∑ n ∈ natIcc (a₁ * Y / (m : ℝ)) (a₂ * Y / (m : ℝ)), ∑ e ∈ Finset.Icc 1 E,
          (if e ∣ n then A e * Φ (m * n) else 0) := Finset.sum_congr rfl h1
    _ = ∑ e ∈ Finset.Icc 1 E, ∑ n ∈ natIcc (a₁ * Y / (m : ℝ)) (a₂ * Y / (m : ℝ)),
          (if e ∣ n then A e * Φ (m * n) else 0) := Finset.sum_comm
    _ = ∑ e ∈ Finset.Icc 1 E, A e * ∑ᶠ v : ℕ, Φ (m * e * v) := Finset.sum_congr rfl h2

/-- **One scale**: the main terms of the progressions `m e v` and the model error give
`T(m) = (Y/m) G ∑_e A_e/e + O(Err_L ∑_e |A_e| + Err_E)`. -/
theorem norm_scaleSum_sub_main_le {Φ H : ℕ → ℂ} {a₁ a₂ Y : ℝ} (ha₁ : 0 < a₁) (hY : 0 < Y)
    (hΦ : ∀ w : ℕ, Φ w ≠ 0 → a₁ * Y ≤ (w : ℝ) ∧ (w : ℝ) ≤ a₂ * Y)
    (A : ℕ → ℂ) {E : ℕ} (hA : ∀ e : ℕ, A e ≠ 0 → e ∈ Finset.Icc 1 E) {m : ℕ} (hm : 0 < m)
    {G : ℂ} {ErrL ErrE : ℝ}
    (hmain : ∀ e ∈ Finset.Icc 1 E, A e ≠ 0 →
      ‖(∑ᶠ v : ℕ, Φ (m * e * v)) - (Y : ℂ) / ((m * e : ℕ) : ℂ) * G‖ ≤ ErrL)
    (herr : ‖∑ n ∈ natIcc (a₁ * Y / (m : ℝ)) (a₂ * Y / (m : ℝ)),
      Φ (m * n) * (H n - divisorSum A n)‖ ≤ ErrE) :
    ‖scaleSum Φ H a₁ a₂ Y m -
        (Y : ℂ) / (m : ℂ) * (G * ∑ e ∈ Finset.Icc 1 E, A e / (e : ℂ))‖ ≤
      (∑ e ∈ Finset.Icc 1 E, ‖A e‖) * ErrL + ErrE := by
  have hsplit : scaleSum Φ H a₁ a₂ Y m = scaleSum Φ (divisorSum A) a₁ a₂ Y m +
      ∑ n ∈ natIcc (a₁ * Y / (m : ℝ)) (a₂ * Y / (m : ℝ)),
        Φ (m * n) * (H n - divisorSum A n) := by
    unfold scaleSum
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hmainsum : (Y : ℂ) / (m : ℂ) * (G * ∑ e ∈ Finset.Icc 1 E, A e / (e : ℂ)) =
      ∑ e ∈ Finset.Icc 1 E, A e * ((Y : ℂ) / ((m * e : ℕ) : ℂ) * G) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Nat.cast_mul]
    ring
  have hterm : ∀ e ∈ Finset.Icc 1 E,
      ‖A e * ((∑ᶠ v : ℕ, Φ (m * e * v)) - (Y : ℂ) / ((m * e : ℕ) : ℂ) * G)‖ ≤
        ‖A e‖ * ErrL := by
    intro e he
    rw [norm_mul]
    by_cases hAe : A e = 0
    · rw [hAe, norm_zero, zero_mul, zero_mul]
    · exact mul_le_mul_of_nonneg_left (hmain e he hAe) (norm_nonneg _)
  have h1 : ∑ e ∈ Finset.Icc 1 E,
        A e * ((∑ᶠ v : ℕ, Φ (m * e * v)) - (Y : ℂ) / ((m * e : ℕ) : ℂ) * G) =
      (∑ e ∈ Finset.Icc 1 E, A e * ∑ᶠ v : ℕ, Φ (m * e * v)) -
        ∑ e ∈ Finset.Icc 1 E, A e * ((Y : ℂ) / ((m * e : ℕ) : ℂ) * G) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun e _ => mul_sub _ _ _
  have hre : scaleSum Φ H a₁ a₂ Y m -
        (Y : ℂ) / (m : ℂ) * (G * ∑ e ∈ Finset.Icc 1 E, A e / (e : ℂ)) =
      (∑ e ∈ Finset.Icc 1 E,
        A e * ((∑ᶠ v : ℕ, Φ (m * e * v)) - (Y : ℂ) / ((m * e : ℕ) : ℂ) * G)) +
      ∑ n ∈ natIcc (a₁ * Y / (m : ℝ)) (a₂ * Y / (m : ℝ)),
        Φ (m * n) * (H n - divisorSum A n) := by
    rw [hsplit, scaleSum_divisorSum ha₁ hY hΦ A hA hm, hmainsum, h1]
    ring
  rw [hre]
  calc ‖(∑ e ∈ Finset.Icc 1 E,
          A e * ((∑ᶠ v : ℕ, Φ (m * e * v)) - (Y : ℂ) / ((m * e : ℕ) : ℂ) * G)) +
        ∑ n ∈ natIcc (a₁ * Y / (m : ℝ)) (a₂ * Y / (m : ℝ)),
          Φ (m * n) * (H n - divisorSum A n)‖
      ≤ ‖∑ e ∈ Finset.Icc 1 E,
          A e * ((∑ᶠ v : ℕ, Φ (m * e * v)) - (Y : ℂ) / ((m * e : ℕ) : ℂ) * G)‖ +
        ‖∑ n ∈ natIcc (a₁ * Y / (m : ℝ)) (a₂ * Y / (m : ℝ)),
          Φ (m * n) * (H n - divisorSum A n)‖ := norm_add_le _ _
    _ ≤ ∑ e ∈ Finset.Icc 1 E, ‖A e‖ * ErrL + ErrE :=
        add_le_add ((norm_sum_le _ _).trans (Finset.sum_le_sum hterm)) herr
    _ = (∑ e ∈ Finset.Icc 1 E, ‖A e‖) * ErrL + ErrE := by rw [Finset.sum_mul]

/-! ### The tuples -/

/-- `∑_w #{𝔩 ∈ 𝔏 : l_𝔩 ∣ w} g(w) = ∑_{𝔩 ∈ 𝔏} ∑_n g(l_𝔩 n)` on integer ranges. -/
theorem sum_card_filter_dvd_mul {ι : Type*} (𝔏 : Finset ι) (l : ι → ℕ)
    (hl : ∀ 𝔩 ∈ 𝔏, 0 < l 𝔩) {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (g : ℕ → ℂ) :
    ∑ w ∈ natIcc R₁ R₂, ((𝔏.filter fun 𝔩 => l 𝔩 ∣ w).card : ℂ) * g w =
      ∑ 𝔩 ∈ 𝔏, ∑ n ∈ natIcc (R₁ / (l 𝔩 : ℝ)) (R₂ / (l 𝔩 : ℝ)), g (l 𝔩 * n) := by
  have h1 : ∀ w ∈ natIcc R₁ R₂, ((𝔏.filter fun 𝔩 => l 𝔩 ∣ w).card : ℂ) * g w =
      ∑ 𝔩 ∈ 𝔏, if l 𝔩 ∣ w then g w else 0 := by
    intro w _
    rw [Finset.natCast_card_filter, Finset.sum_mul]
    refine Finset.sum_congr rfl fun 𝔩 _ => ?_
    by_cases hd : l 𝔩 ∣ w
    · rw [if_pos hd, if_pos hd, one_mul]
    · rw [if_neg hd, if_neg hd, zero_mul]
  calc ∑ w ∈ natIcc R₁ R₂, ((𝔏.filter fun 𝔩 => l 𝔩 ∣ w).card : ℂ) * g w
      = ∑ w ∈ natIcc R₁ R₂, ∑ 𝔩 ∈ 𝔏, (if l 𝔩 ∣ w then g w else 0) := Finset.sum_congr rfl h1
    _ = ∑ 𝔩 ∈ 𝔏, ∑ w ∈ natIcc R₁ R₂, (if l 𝔩 ∣ w then g w else 0) := Finset.sum_comm
    _ = ∑ 𝔩 ∈ 𝔏, ∑ n ∈ natIcc (R₁ / (l 𝔩 : ℝ)) (R₂ / (l 𝔩 : ℝ)), g (l 𝔩 * n) :=
        Finset.sum_congr rfl fun 𝔩 h𝔩 => by
          rw [← Finset.sum_filter]
          exact sum_filter_dvd_natIcc_eq hR₁ (hl 𝔩 h𝔩) g

/-- **The cancellation of the main terms**: if `T(m) = (Y/m) G + O(ρ₀ + ρ₁/m)` for `m = 1` and
for `m = l_𝔩`, and `C_x = ∑_𝔩 1/l_𝔩`, then
`|∑_𝔩 T(l_𝔩) - C_x T(1)| ≤ (#𝔏 + C_x) ρ₀ + 2 C_x ρ₁`. -/
theorem norm_sum_scale_sub_le {ι : Type*} (𝔏 : Finset ι) (l : ι → ℕ) (T : ℕ → ℂ) (Y : ℝ)
    (G : ℂ) {Cx ρ₀ ρ₁ : ℝ} (hCx : Cx = ∑ 𝔩 ∈ 𝔏, 1 / ((l 𝔩 : ℕ) : ℝ)) (hCx0 : 0 ≤ Cx)
    (hT1 : ‖T 1 - (Y : ℂ) / ((1 : ℕ) : ℂ) * G‖ ≤ ρ₀ + ρ₁ / ((1 : ℕ) : ℝ))
    (hT : ∀ 𝔩 ∈ 𝔏, ‖T (l 𝔩) - (Y : ℂ) / ((l 𝔩 : ℕ) : ℂ) * G‖ ≤
      ρ₀ + ρ₁ / ((l 𝔩 : ℕ) : ℝ)) :
    ‖∑ 𝔩 ∈ 𝔏, T (l 𝔩) - (Cx : ℂ) * T 1‖ ≤ ((𝔏.card : ℝ) + Cx) * ρ₀ + 2 * Cx * ρ₁ := by
  have hCxC : (Cx : ℂ) = ∑ 𝔩 ∈ 𝔏, 1 / ((l 𝔩 : ℕ) : ℂ) := by
    rw [hCx, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun 𝔩 _ => by
      rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
  have hzero : ∑ 𝔩 ∈ 𝔏, (Y : ℂ) / ((l 𝔩 : ℕ) : ℂ) * G -
      (Cx : ℂ) * ((Y : ℂ) / ((1 : ℕ) : ℂ) * G) = 0 := by
    rw [hCxC, Finset.sum_mul, Nat.cast_one, div_one, sub_eq_zero]
    exact Finset.sum_congr rfl fun 𝔩 _ => by ring
  have hsub : ∑ 𝔩 ∈ 𝔏, (T (l 𝔩) - (Y : ℂ) / ((l 𝔩 : ℕ) : ℂ) * G) =
      ∑ 𝔩 ∈ 𝔏, T (l 𝔩) - ∑ 𝔩 ∈ 𝔏, (Y : ℂ) / ((l 𝔩 : ℕ) : ℂ) * G :=
    Finset.sum_sub_distrib _ _
  have hdecomp : ∑ 𝔩 ∈ 𝔏, T (l 𝔩) - (Cx : ℂ) * T 1 =
      ∑ 𝔩 ∈ 𝔏, (T (l 𝔩) - (Y : ℂ) / ((l 𝔩 : ℕ) : ℂ) * G) -
        (Cx : ℂ) * (T 1 - (Y : ℂ) / ((1 : ℕ) : ℂ) * G) := by
    rw [hsub]
    linear_combination hzero
  have hsum : ‖∑ 𝔩 ∈ 𝔏, (T (l 𝔩) - (Y : ℂ) / ((l 𝔩 : ℕ) : ℂ) * G)‖ ≤
      (𝔏.card : ℝ) * ρ₀ + ρ₁ * Cx := by
    have e : ∑ 𝔩 ∈ 𝔏, (ρ₀ + ρ₁ / ((l 𝔩 : ℕ) : ℝ)) = (𝔏.card : ℝ) * ρ₀ + ρ₁ * Cx := by
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hCx, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun 𝔩 _ => by ring
    calc ‖∑ 𝔩 ∈ 𝔏, (T (l 𝔩) - (Y : ℂ) / ((l 𝔩 : ℕ) : ℂ) * G)‖
        ≤ ∑ 𝔩 ∈ 𝔏, ‖T (l 𝔩) - (Y : ℂ) / ((l 𝔩 : ℕ) : ℂ) * G‖ := norm_sum_le _ _
      _ ≤ ∑ 𝔩 ∈ 𝔏, (ρ₀ + ρ₁ / ((l 𝔩 : ℕ) : ℝ)) := Finset.sum_le_sum hT
      _ = (𝔏.card : ℝ) * ρ₀ + ρ₁ * Cx := e
  have hone : ‖(Cx : ℂ) * (T 1 - (Y : ℂ) / ((1 : ℕ) : ℂ) * G)‖ ≤ Cx * (ρ₀ + ρ₁) := by
    have e : ρ₁ / ((1 : ℕ) : ℝ) = ρ₁ := by rw [Nat.cast_one, div_one]
    have h := hT1
    rw [e] at h
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hCx0]
    exact mul_le_mul_of_nonneg_left h hCx0
  rw [hdecomp]
  calc ‖∑ 𝔩 ∈ 𝔏, (T (l 𝔩) - (Y : ℂ) / ((l 𝔩 : ℕ) : ℂ) * G) -
        (Cx : ℂ) * (T 1 - (Y : ℂ) / ((1 : ℕ) : ℂ) * G)‖
      ≤ ‖∑ 𝔩 ∈ 𝔏, (T (l 𝔩) - (Y : ℂ) / ((l 𝔩 : ℕ) : ℂ) * G)‖ +
        ‖(Cx : ℂ) * (T 1 - (Y : ℂ) / ((1 : ℕ) : ℂ) * G)‖ := norm_sub_le _ _
    _ ≤ ((𝔏.card : ℝ) * ρ₀ + ρ₁ * Cx) + Cx * (ρ₀ + ρ₁) := add_le_add hsum hone
    _ = ((𝔏.card : ℝ) + Cx) * ρ₀ + 2 * Cx * ρ₁ := by ring

/-! ### A threshold -/

/-- For `δ > 0`: `x^{-δ} exp(c L^{.47}) L^b ≤ 1` for all large `x`. -/
theorem eventually_rpow_neg_mul_exp_mul_rpow_le_one {δ : ℝ} (hδ : 0 < δ) (c b : ℝ) :
    ∀ᶠ x : ℝ in atTop,
      x ^ (-δ) * Real.exp (c * Real.log x ^ (0.47 : ℝ)) * Real.log x ^ b ≤ 1 := by
  have hb0 : 0 ≤ |b| := abs_nonneg b
  have hpos : 0 < 2 * (|b| + 1) := by linarith
  have hε : 0 < δ / (2 * (|b| + 1)) := div_pos hδ hpos
  have h1 : ∀ᶠ x : ℝ in atTop, 2 * |c| / δ ≤ Real.log x ^ (0.53 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.53)).comp
      Real.tendsto_log_atTop).eventually_ge_atTop _
  have h2 : ∀ᶠ x : ℝ in atTop,
      ‖Real.log (Real.log x)‖ ≤ δ / (2 * (|b| + 1)) * ‖Real.log x‖ :=
    Real.tendsto_log_atTop.eventually (Real.isLittleO_log_id_atTop.def hε)
  filter_upwards [h1, h2, Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with x a1 a2 a3 a4
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hLL0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg a3
  have h47 : 0 ≤ Real.log x ^ (0.47 : ℝ) := Real.rpow_nonneg hL0.le _
  have hsplit : Real.log x ^ (0.53 : ℝ) * Real.log x ^ (0.47 : ℝ) = Real.log x := by
    have e : (0.53 : ℝ) + 0.47 = 1 := by norm_num
    rw [← Real.rpow_add hL0, e, Real.rpow_one]
  -- `|c| L^{.47} ≤ (δ/2) L`
  have hc1 : |c| * Real.log x ^ (0.47 : ℝ) ≤ δ / 2 * Real.log x := by
    have h3 : 2 * |c| ≤ Real.log x ^ (0.53 : ℝ) * δ := (div_le_iff₀ hδ).mp a1
    have h4 := mul_le_mul_of_nonneg_right h3 h47
    have e : Real.log x ^ (0.53 : ℝ) * δ * Real.log x ^ (0.47 : ℝ) = δ * Real.log x :=
      calc Real.log x ^ (0.53 : ℝ) * δ * Real.log x ^ (0.47 : ℝ)
          = δ * (Real.log x ^ (0.53 : ℝ) * Real.log x ^ (0.47 : ℝ)) := by ring
        _ = δ * Real.log x := by rw [hsplit]
    rw [e] at h4
    linarith
  -- `|b| log L ≤ (δ/2) L`
  have hb1 : Real.log (Real.log x) * |b| ≤ δ / 2 * Real.log x := by
    have h5 := a2
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hLL0, abs_of_pos hL0] at h5
    have h6 : Real.log (Real.log x) * (2 * (|b| + 1)) ≤ δ * Real.log x := by
      have h7 := mul_le_mul_of_nonneg_right h5 hpos.le
      have e : δ / (2 * (|b| + 1)) * Real.log x * (2 * (|b| + 1)) = δ * Real.log x := by
        rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hpos.ne']
      rw [e] at h7
      exact h7
    linarith
  have hc2 : c * Real.log x ^ (0.47 : ℝ) ≤ |c| * Real.log x ^ (0.47 : ℝ) :=
    mul_le_mul_of_nonneg_right (le_abs_self c) h47
  have hb2 : Real.log (Real.log x) * b ≤ Real.log (Real.log x) * |b| :=
    mul_le_mul_of_nonneg_left (le_abs_self b) hLL0
  rw [Real.rpow_def_of_pos hx0 (-δ), Real.rpow_def_of_pos hL0 b, ← Real.exp_add,
    ← Real.exp_add]
  refine (Real.exp_le_exp.mpr ?_).trans_eq Real.exp_zero
  linarith

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
