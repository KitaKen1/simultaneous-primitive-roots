module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.ProgressionCore

/-!
# The sum over the moduli of Lemma 7.2

`sum_abs_shiftSum_family_sub_le`: the sum over `1 ≤ r ≤ N₀` of the estimates
`abs_shiftSum_family_sub_model_le` for one modulus (`Extraction/ProgressionCore.lean`), with
explicit error terms and no asymptotics (`[P-07:0165–0190]`).

* For `(r, H) > 1` the progression sum is empty and the main term is absent
  (`shiftSum_eq_zero_of_not_coprime`; this is where `(b, H) = 1` is used).
* For `(r, H) = 1` the three error terms of one modulus are bounded uniformly in `r`: `T₁` bounds
  the number of terms of the truncated expansion and of its envelope, `T₂` the reciprocal mass of
  the envelope (ext:bonferroni-tail), `B` the reciprocal mass `∑_{p ∈ 𝒬, p ∣ r} 1/p` of the forced
  absences.
* `∑_{r ≤ N₀} 1/r ≤ 1 + log N₀`.

The result is `N₀ · H_b · #I · C_Φ · T₁ + (x/H) (∫Φ) C (1 + log N₀) · 2 H_b (T₂ + B)`: "the sum of
all rounding errors over tuples and `r ≤ x^{c₀}`" (ext:rounding-sum) and "the principal Bonferroni
errors" with the coupling error.

`sum_two_pow_card_family_le`, `sum_powersetCard_prod_family_le`: the bounds `T₁`, `T₂` for a set
`𝒬` of primes `≤ P_max` of reciprocal mass `≤ V`:
`T₁ = 2 P_max^k e^{2V}` ("every divisor in the truncation or the error envelope satisfies
`d' ≤ exp(O_K((h_0 + 1) L^{.2}))`", (ext:model-divisor-size)) and `T₂ = e^{-k} e^{2eV}`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Progression

open MeasureTheory

noncomputable section

/-- The arithmetic of the three error terms of one modulus. -/
theorem progression_term_arith {Hb c Xr S1 S2 S3 T₁ T₂ B : ℝ} (hHb : 0 ≤ Hb) (hc : 0 ≤ c)
    (hXr : 0 ≤ Xr) (h1 : S1 ≤ T₁) (h2 : S2 ≤ T₂) (h3 : S3 ≤ B) :
    Hb * (c * S1 + 2 * Xr * S2) + Xr * (2 * Hb * S3) ≤
      Hb * (c * T₁) + Xr * (2 * Hb * (T₂ + B)) := by
  have e1 : c * S1 ≤ c * T₁ := mul_le_mul_of_nonneg_left h1 hc
  have e2 : 2 * Xr * S2 ≤ 2 * Xr * T₂ :=
    mul_le_mul_of_nonneg_left h2 (mul_nonneg zero_le_two hXr)
  have e3 : 2 * Hb * S3 ≤ 2 * Hb * B :=
    mul_le_mul_of_nonneg_left h3 (mul_nonneg zero_le_two hHb)
  have e4 := mul_le_mul_of_nonneg_left (add_le_add e1 e2) hHb
  have e5 := mul_le_mul_of_nonneg_left e3 hXr
  calc Hb * (c * S1 + 2 * Xr * S2) + Xr * (2 * Hb * S3)
      ≤ Hb * (c * T₁ + 2 * Xr * T₂) + Xr * (2 * Hb * B) := add_le_add e4 e5
    _ = Hb * (c * T₁) + Xr * (2 * Hb * (T₂ + B)) := by ring

/-- **The sum over the moduli `1 ≤ r ≤ N₀`**, with explicit error terms. -/
theorem sum_abs_shiftSum_family_sub_le
    {Φ : ℝ → ℝ} {R CΦ : ℝ} (hR : ∀ t, R < t → Φ t = 0) (hΦ0 : ∀ t, 0 ≤ Φ t)
    (hC : ∀ x : ℝ, 0 < x → ∀ ℓ m a : ℕ, 0 < ℓ → 0 < m →
      |(∑ᶠ y : ℕ, if y ≡ a [MOD m] then Φ ((ℓ : ℝ) * (y : ℝ) / x) else 0) -
        x / ((ℓ : ℝ) * (m : ℝ)) * ∫ t, Φ t| ≤ CΦ) (hCΦ0 : 0 ≤ CΦ)
    {x : ℝ} (hx : 0 < x) {H b : ℕ} (hH : 0 < H) (hb : b.Coprime H) (N₀ : ℕ)
    {𝒬 : Finset ℕ} (h𝒬 : ∀ p ∈ 𝒬, p.Prime) (h𝒬H : ∀ p ∈ 𝒬, ¬ p ∣ H)
    {G : ℕ → ℝ} {Hb : ℝ} (hG : ∀ u, |G u| ≤ Hb)
    (hGinv : ∀ u u' : ℕ, (∀ p ∈ 𝒬, (p ∣ u ↔ p ∣ u')) → G u = G u')
    {ι : Type*} (I : Finset ι) (ℓ : ι → ℕ) (hℓ0 : ∀ i ∈ I, 0 < ℓ i)
    (hℓr : ∀ r ∈ Finset.Icc 1 N₀, ∀ i ∈ I, (ℓ i).Coprime r)
    (hℓH : ∀ i ∈ I, (ℓ i).Coprime H) (hℓ𝒬 : ∀ i ∈ I, ∀ p ∈ 𝒬, (ℓ i).Coprime p) (k : ℕ)
    {T₁ T₂ B : ℝ}
    (hT₁ : ∀ P ⊆ 𝒬, ∑ D ∈ P.powerset.filter (fun D => D.card < k), (2 : ℝ) ^ D.card +
      ∑ E ∈ P.powersetCard k, (2 : ℝ) ^ E.card ≤ T₁)
    (hT₂ : ∀ P ⊆ 𝒬, ∑ E ∈ P.powersetCard k, ∏ p ∈ E, (2 / (p : ℝ)) ≤ T₂)
    (hB : ∀ r ∈ Finset.Icc 1 N₀, ∑ p ∈ 𝒬.filter (fun p => p ∣ r), 1 / (p : ℝ) ≤ B)
    (hB0 : 0 ≤ B) :
    ∑ r ∈ Finset.Icc 1 N₀,
        |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H])
            (fun u => (∑ i ∈ I, if ℓ i ∣ u then (1 : ℝ) else 0) * G u) -
          (if r.Coprime H then x / ((H : ℝ) * (r : ℝ)) * (∫ t, Φ t) *
            (∑ i ∈ I, 1 / (ℓ i : ℝ)) * modelMean 𝒬 G else 0)| ≤
      (N₀ : ℝ) * (Hb * ((I.card : ℝ) * CΦ * T₁)) +
        x / (H : ℝ) * (∫ t, Φ t) * (∑ i ∈ I, 1 / (ℓ i : ℝ)) * (1 + Real.log N₀) *
          (2 * Hb * (T₂ + B)) := by
  have hHb : 0 ≤ Hb := (abs_nonneg _).trans (hG 0)
  have hint : 0 ≤ ∫ t, Φ t := MeasureTheory.integral_nonneg fun t => hΦ0 t
  have hCI : 0 ≤ ∑ i ∈ I, 1 / (ℓ i : ℝ) := Finset.sum_nonneg fun i _ => by positivity
  have hT₁0 : 0 ≤ T₁ :=
    le_trans (add_nonneg (Finset.sum_nonneg fun D _ => pow_nonneg zero_le_two _)
      (Finset.sum_nonneg fun E _ => pow_nonneg zero_le_two _)) (hT₁ ∅ (Finset.empty_subset _))
  have hT₂0 : 0 ≤ T₂ :=
    le_trans (Finset.sum_nonneg fun E _ => Finset.prod_nonneg fun p _ => by positivity)
      (hT₂ ∅ (Finset.empty_subset _))
  obtain ⟨Xc, hXc⟩ : ∃ Xc : ℝ,
      Xc = x / (H : ℝ) * (∫ t, Φ t) * (∑ i ∈ I, 1 / (ℓ i : ℝ)) := ⟨_, rfl⟩
  have hXc0 : 0 ≤ Xc := by
    rw [hXc]
    exact mul_nonneg (mul_nonneg (div_nonneg hx.le (Nat.cast_nonneg H)) hint) hCI
  have hc0 : 0 ≤ (I.card : ℝ) * CΦ := mul_nonneg (Nat.cast_nonneg _) hCΦ0
  have hE0 : 0 ≤ Xc * (2 * Hb * (T₂ + B)) :=
    mul_nonneg hXc0 (mul_nonneg (mul_nonneg zero_le_two hHb) (add_nonneg hT₂0 hB0))
  have hterm : ∀ r ∈ Finset.Icc 1 N₀,
      |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H])
          (fun u => (∑ i ∈ I, if ℓ i ∣ u then (1 : ℝ) else 0) * G u) -
        (if r.Coprime H then x / ((H : ℝ) * (r : ℝ)) * (∫ t, Φ t) *
          (∑ i ∈ I, 1 / (ℓ i : ℝ)) * modelMean 𝒬 G else 0)| ≤
      Hb * ((I.card : ℝ) * CΦ * T₁) + Xc * (2 * Hb * (T₂ + B)) * (r : ℝ)⁻¹ := by
    intro r hr
    have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrR : (0 : ℝ) ≤ (r : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg r)
    have hXr0 : 0 ≤ Xc * (r : ℝ)⁻¹ := mul_nonneg hXc0 hrR
    by_cases hrH : r.Coprime H
    · have h := abs_shiftSum_family_sub_model_le hR hΦ0 hC hx hH hr1 hrH b h𝒬 h𝒬H hG hGinv I ℓ
        hℓ0 (hℓr r hr) hℓH hℓ𝒬 k
      have hP : 𝒬.filter (fun p => ¬ p ∣ r) ⊆ 𝒬 := Finset.filter_subset _ _
      have hXr : x / ((H : ℝ) * (r : ℝ)) * (∫ t, Φ t) * (∑ i ∈ I, 1 / (ℓ i : ℝ)) =
          Xc * (r : ℝ)⁻¹ := by
        rw [hXc]
        ring
      rw [hXr] at h
      rw [if_pos hrH, hXr]
      refine h.trans ((progression_term_arith hHb hc0 hXr0 (hT₁ _ hP) (hT₂ _ hP)
        (hB r hr)).trans (le_of_eq ?_))
      ring
    · rw [if_neg hrH, shiftSum_eq_zero_of_not_coprime hb hrH, sub_zero, abs_zero]
      exact add_nonneg (mul_nonneg hHb (mul_nonneg hc0 hT₁0)) (mul_nonneg hE0 hrR)
  calc _ ≤ ∑ r ∈ Finset.Icc 1 N₀,
          (Hb * ((I.card : ℝ) * CΦ * T₁) + Xc * (2 * Hb * (T₂ + B)) * (r : ℝ)⁻¹) :=
        Finset.sum_le_sum hterm
    _ = (N₀ : ℝ) * (Hb * ((I.card : ℝ) * CΦ * T₁)) +
          Xc * (2 * Hb * (T₂ + B)) * ∑ r ∈ Finset.Icc 1 N₀, (r : ℝ)⁻¹ := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
          nsmul_eq_mul, Finset.mul_sum]
    _ ≤ (N₀ : ℝ) * (Hb * ((I.card : ℝ) * CΦ * T₁)) +
          Xc * (2 * Hb * (T₂ + B)) * (1 + Real.log N₀) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left
          (SimultaneousPrimitiveRoots.Unconditional.Classical.sum_Icc_inv_le_one_add_log N₀) hE0)
    _ = (N₀ : ℝ) * (Hb * ((I.card : ℝ) * CΦ * T₁)) +
          x / (H : ℝ) * (∫ t, Φ t) * (∑ i ∈ I, 1 / (ℓ i : ℝ)) * (1 + Real.log N₀) *
            (2 * Hb * (T₂ + B)) := by
        rw [hXc]
        ring

/-! ### The error terms for a set of primes of bounded size and mass -/

/-- **The number of terms** (ext:model-divisor-size): for a set `𝒬` of positive integers
`≤ P_max` of reciprocal mass `≤ V` and `P ⊆ 𝒬`,
`∑_{D ⊆ P, |D| < k} 2^{|D|} + ∑_{E ⊆ P, |E| = k} 2^{|E|} ≤ 2 P_max^k e^{2V}`. -/
theorem sum_two_pow_card_family_le {𝒬 P : Finset ℕ} (hP : P ⊆ 𝒬) {Pm V : ℝ} (hPm : 1 ≤ Pm)
    (h𝒬 : ∀ p ∈ 𝒬, 0 < p ∧ (p : ℝ) ≤ Pm) (hV : reciprocalMass 𝒬 ≤ V) (k : ℕ) :
    ∑ D ∈ P.powerset.filter (fun D => D.card < k), (2 : ℝ) ^ D.card +
        ∑ E ∈ P.powersetCard k, (2 : ℝ) ^ E.card ≤ 2 * (Pm ^ k * Real.exp (2 * V)) := by
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (h𝒬 p (hP hp)).1
  have hsize : ∀ D ⊆ P, D.card ≤ k → ((∏ p ∈ D, p : ℕ) : ℝ) ≤ Pm ^ k := by
    intro D hD hcard
    rw [Nat.cast_prod]
    calc ∏ p ∈ D, (p : ℝ) ≤ ∏ _p ∈ D, Pm :=
          Finset.prod_le_prod (fun p _ => Nat.cast_nonneg p)
            (fun p hp => (h𝒬 p (hP (hD hp))).2)
      _ = Pm ^ D.card := Finset.prod_const _
      _ ≤ Pm ^ k := pow_le_pow_right₀ hPm hcard
  have hYk : 0 ≤ Pm ^ k := pow_nonneg (zero_le_one.trans hPm) k
  have hprod : ∏ p ∈ P, (1 + 2 / (p : ℝ)) ≤ Real.exp (2 * V) :=
    (prod_one_add_div_le_exp_mul P zero_le_two).trans
      (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left ((reciprocalMass_mono hP).trans hV) zero_le_two))
  have h1 := sum_two_pow_card_le hpos
    (𝒟 := P.powerset.filter (fun D => D.card < k)) (Finset.filter_subset _ _) hYk
    (fun D hD => hsize D (Finset.mem_powerset.mp (Finset.mem_filter.mp hD).1)
      (Finset.mem_filter.mp hD).2.le)
  have h2 := sum_two_pow_card_le hpos (𝒟 := P.powersetCard k)
    (fun E hE => Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp hE).1) hYk
    (fun E hE => hsize E (Finset.mem_powersetCard.mp hE).1
      (Finset.mem_powersetCard.mp hE).2.le)
  have h3 := mul_le_mul_of_nonneg_left hprod hYk
  linarith

/-- **The tail** (ext:bonferroni-tail): for a set `𝒬` of reciprocal mass `≤ V` and `P ⊆ 𝒬`,
`∑_{E ⊆ P, |E| = k} ∏_{p ∈ E} 2/p ≤ e^{-k} e^{2eV}`. -/
theorem sum_powersetCard_prod_family_le {𝒬 P : Finset ℕ} (hP : P ⊆ 𝒬) {V : ℝ}
    (hV : reciprocalMass 𝒬 ≤ V) (k : ℕ) :
    ∑ E ∈ P.powersetCard k, ∏ p ∈ E, (2 / (p : ℝ)) ≤
      (Real.exp 1 ^ k)⁻¹ * Real.exp (2 * Real.exp 1 * V) := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have h2e : 0 ≤ 2 * Real.exp 1 := mul_nonneg zero_le_two he.le
  have h1 := sum_powersetCard_prod_le P k he
  have h2 : ∏ p ∈ P, (1 + 2 * Real.exp 1 / (p : ℝ)) ≤ Real.exp (2 * Real.exp 1 * V) :=
    (prod_one_add_div_le_exp_mul P h2e).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ((reciprocalMass_mono hP).trans hV) h2e))
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (inv_nonneg.mpr (pow_pos he k).le))

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Progression
