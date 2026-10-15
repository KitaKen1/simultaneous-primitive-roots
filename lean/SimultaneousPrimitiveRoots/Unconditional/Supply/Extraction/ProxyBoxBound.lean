module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.ProxyBox

/-!
# The bound of one dyadic box in powers of `L`

For the Type II step (`[P-07:0249–0315]`, `Extraction/ProxyProof.lean`): the estimate
`Proxy.abs_box_concrete_le` of one box `[A₀, 2A₀) × [C₀, 2C₀)` with `A₀ C₀ ≤ κ x`, evaluated with

* the truncation level `T = L^B`, `B = A + 4`, where `A` bounds the exponent of the divisor moment
  (`[P-07:0269–0281]`: "taking `B` large enough");
* blocks of length `ℓ = ⌊A₀ L^{-(B+4)}⌋ + 1`, so that there are at most `3 L^{B+4}` blocks and
  `ℓ ≤ 2 A₀ L^{-(B+4)}`;
* the Type II bound `M · A₀ C₀ · L^{-(B+8)}` with coefficients bounded by `L^{B+1}`
  (`[P-07:0300]`: "Choose its log-saving target after all the fixed dyadic, Fourier, and
  truncation losses").

Each of the three contributions is at most a constant times `x L^{-4}`
(`Proxy.term_one_le`, `Proxy.term_two_le`, `Proxy.term_three_le`, `Proxy.box_relevant_le`); a box
with `A₀ C₀ ∉ [x/κ, κx]` does not meet the support of the cutoff
(`Proxy.cutoff_eq_zero_of_irrelevant`); and `O(L²)` boxes cost `x L^{-2} = o(x/L)`
(`Proxy.final_sum_arith`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

noncomputable section

namespace Proxy

/-! ### Arithmetic of the three contributions -/

/-- The blocks: at most `3 L^E` Type II sums, each `≤ Bs M' A₀C₀ L^{-(E+4)}`. -/
theorem term_one_le {cK Bs M' Hm Hn κ x L : ℝ} {E : ℕ} (hBs : 0 ≤ Bs) (hM : 0 ≤ M')
    (hL : 1 ≤ L) (hx : 0 ≤ x) (hcK0 : 0 ≤ cK) (hcK : cK ≤ 3 * L ^ E) (hH : Hm * Hn ≤ κ * x)
    (hκ : 0 ≤ κ) :
    cK * (Bs * (M' * (Hm * Hn) * (L ^ (E + 4))⁻¹)) ≤ 3 * Bs * M' * κ * (x * (L ^ 4)⁻¹) := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hLE : 0 < L ^ E := pow_pos hL0 E
  have hinvnn : 0 ≤ (L ^ (E + 4))⁻¹ := inv_nonneg.mpr (pow_nonneg hL0.le _)
  have hinv : (L ^ (E + 4))⁻¹ = (L ^ E)⁻¹ * (L ^ 4)⁻¹ := by rw [pow_add, mul_inv]
  have h1 : Bs * (M' * (Hm * Hn) * (L ^ (E + 4))⁻¹) ≤ Bs * (M' * (κ * x) * (L ^ (E + 4))⁻¹) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hH hM) hinvnn) hBs
  have h2 : 0 ≤ Bs * (M' * (κ * x) * (L ^ (E + 4))⁻¹) :=
    mul_nonneg hBs (mul_nonneg (mul_nonneg hM (mul_nonneg hκ hx)) hinvnn)
  calc cK * (Bs * (M' * (Hm * Hn) * (L ^ (E + 4))⁻¹))
      ≤ cK * (Bs * (M' * (κ * x) * (L ^ (E + 4))⁻¹)) := mul_le_mul_of_nonneg_left h1 hcK0
    _ ≤ 3 * L ^ E * (Bs * (M' * (κ * x) * (L ^ (E + 4))⁻¹)) :=
        mul_le_mul_of_nonneg_right hcK h2
    _ = 3 * Bs * M' * κ * (x * (L ^ 4)⁻¹) * (L ^ E * (L ^ E)⁻¹) := by
        rw [hinv]
        ring
    _ = 3 * Bs * M' * κ * (x * (L ^ 4)⁻¹) := by rw [mul_inv_cancel₀ hLE.ne', mul_one]

/-- The cutoff on the blocks: `|I| |J| · Lip ℓ (2C₀)/x · BF · L^B` with `ℓ ≤ 2 A₀ L^{-(B+4)}`. -/
theorem term_two_le {Hm Hn κ x L Lip BF lr : ℝ} {B : ℕ} (hL : 1 ≤ L) (hx : 0 < x)
    (hLip : 0 ≤ Lip) (hBF : 0 ≤ BF) (hHm : 0 ≤ Hm) (hHn : 0 ≤ Hn) (hH : Hm * Hn ≤ κ * x)
    (hl : lr ≤ 2 * Hm * (L ^ (B + 4))⁻¹) :
    Hm * Hn * (Lip * (lr * (2 * Hn) / x) * BF * L ^ B) ≤
      4 * Lip * BF * κ ^ 2 * (x * (L ^ 4)⁻¹) := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hinv : L ^ B * (L ^ (B + 4))⁻¹ = (L ^ 4)⁻¹ := by
    rw [pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ (pow_pos hL0 B).ne', one_mul]
  have h1 : lr * (2 * Hn) / x ≤ 2 * Hm * (L ^ (B + 4))⁻¹ * (2 * Hn) / x :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hl (mul_nonneg zero_le_two hHn)) hx.le
  have hsq : (Hm * Hn) ^ 2 ≤ (κ * x) ^ 2 := pow_le_pow_left₀ (mul_nonneg hHm hHn) hH 2
  have hx2 : (κ * x) ^ 2 / x = κ ^ 2 * x := by
    rw [div_eq_iff hx.ne']
    ring
  calc Hm * Hn * (Lip * (lr * (2 * Hn) / x) * BF * L ^ B)
      ≤ Hm * Hn * (Lip * (2 * Hm * (L ^ (B + 4))⁻¹ * (2 * Hn) / x) * BF * L ^ B) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hLip) hBF)
            (pow_nonneg hL0.le B)) (mul_nonneg hHm hHn)
    _ = 4 * Lip * BF * ((Hm * Hn) ^ 2 / x) * (L ^ B * (L ^ (B + 4))⁻¹) := by ring
    _ = 4 * Lip * BF * ((Hm * Hn) ^ 2 / x) * (L ^ 4)⁻¹ := by rw [hinv]
    _ ≤ 4 * Lip * BF * ((κ * x) ^ 2 / x) * (L ^ 4)⁻¹ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hsq hx.le)
            (mul_nonneg (mul_nonneg (by norm_num) hLip) hBF))
          (inv_nonneg.mpr (pow_nonneg hL0.le 4))
    _ = 4 * Lip * BF * κ ^ 2 * (x * (L ^ 4)⁻¹) := by
        rw [hx2]
        ring

/-- The truncation: `|I| · BΦ BF · ∑ βhi` with `∑ βhi ≤ J² L^{-(A+4)} Cτ (2C₀) (2L)^A`. -/
theorem term_three_le {Hm Hn κ x L BΦ BF J2 Cτ Sg lg : ℝ} {An : ℕ} (hL : 1 ≤ L)
    (hBΦ : 0 ≤ BΦ) (hBF : 0 ≤ BF) (hJ2 : 0 ≤ J2) (hCτ : 0 ≤ Cτ) (hHm : 0 ≤ Hm) (hHn : 0 ≤ Hn)
    (hH : Hm * Hn ≤ κ * x) (hlg : lg ≤ 2 ^ An * L ^ An)
    (hSg : Sg ≤ J2 / L ^ (An + 4) * (Cτ * (2 * Hn) * lg)) :
    Hm * (BΦ * BF * Sg) ≤ 2 * BΦ * BF * J2 * Cτ * 2 ^ An * κ * (x * (L ^ 4)⁻¹) := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hLA : 0 < L ^ An := pow_pos hL0 An
  have hJL : 0 ≤ J2 / L ^ (An + 4) := div_nonneg hJ2 (pow_nonneg hL0.le _)
  have hinv : L ^ An / L ^ (An + 4) = (L ^ 4)⁻¹ := by
    rw [div_eq_mul_inv, pow_add, mul_inv, ← mul_assoc, mul_inv_cancel₀ hLA.ne', one_mul]
  have h1 : Sg ≤ J2 / L ^ (An + 4) * (Cτ * (2 * Hn) * (2 ^ An * L ^ An)) :=
    hSg.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hlg (mul_nonneg hCτ (mul_nonneg zero_le_two hHn))) hJL)
  have hc0 : 0 ≤ 2 * BΦ * BF * J2 * Cτ * 2 ^ An :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hBΦ) hBF) hJ2) hCτ)
      (pow_nonneg zero_le_two An)
  calc Hm * (BΦ * BF * Sg)
      ≤ Hm * (BΦ * BF * (J2 / L ^ (An + 4) * (Cτ * (2 * Hn) * (2 ^ An * L ^ An)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (mul_nonneg hBΦ hBF)) hHm
    _ = 2 * BΦ * BF * J2 * Cτ * 2 ^ An * (Hm * Hn) * (L ^ An / L ^ (An + 4)) := by ring
    _ = 2 * BΦ * BF * J2 * Cτ * 2 ^ An * (Hm * Hn) * (L ^ 4)⁻¹ := by rw [hinv]
    _ ≤ 2 * BΦ * BF * J2 * Cτ * 2 ^ An * (κ * x) * (L ^ 4)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hH hc0)
          (inv_nonneg.mpr (pow_nonneg hL0.le 4))
    _ = 2 * BΦ * BF * J2 * Cτ * 2 ^ An * κ * (x * (L ^ 4)⁻¹) := by ring

/-- `A₁² ≤ 16 L²` boxes, each `≤ Cbox · x L^{-4}`, give `≤ η x/L` once `L ≥ 16 Cbox/η`. -/
theorem final_sum_arith {A₁r Cbox x L η : ℝ} (hA0 : 0 ≤ A₁r) (hA : A₁r ≤ 4 * L) (hC : 0 ≤ Cbox)
    (hx : 0 ≤ x) (hL : 1 ≤ L) (hη : 0 < η) (hLη : 16 * Cbox / η ≤ L) :
    A₁r * A₁r * (Cbox * (x * (L ^ 4)⁻¹)) ≤ η * (x / L) := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hL4 : 0 < L ^ 4 := pow_pos hL0 4
  have h1 : A₁r * A₁r ≤ 4 * L * (4 * L) := mul_le_mul hA hA hA0 (by linarith)
  have h2 : 16 * Cbox ≤ η * L := by
    have h := (div_le_iff₀ hη).mp hLη
    linarith
  have hXnn : 0 ≤ Cbox * (x * (L ^ 4)⁻¹) :=
    mul_nonneg hC (mul_nonneg hx (inv_nonneg.mpr hL4.le))
  have hYnn : 0 ≤ x * (L ^ 2 * (L ^ 4)⁻¹) :=
    mul_nonneg hx (mul_nonneg (pow_nonneg hL0.le 2) (inv_nonneg.mpr hL4.le))
  have h3 : L * (L ^ 2 * (L ^ 4)⁻¹) = L⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    have e : L * (L ^ 2 * (L ^ 4)⁻¹) * L = L ^ 4 * (L ^ 4)⁻¹ := by ring
    rw [e, mul_inv_cancel₀ hL4.ne']
  calc A₁r * A₁r * (Cbox * (x * (L ^ 4)⁻¹))
      ≤ 4 * L * (4 * L) * (Cbox * (x * (L ^ 4)⁻¹)) := mul_le_mul_of_nonneg_right h1 hXnn
    _ = 16 * Cbox * (x * (L ^ 2 * (L ^ 4)⁻¹)) := by ring
    _ ≤ η * L * (x * (L ^ 2 * (L ^ 4)⁻¹)) := mul_le_mul_of_nonneg_right h2 hYnn
    _ = η * x * (L * (L ^ 2 * (L ^ 4)⁻¹)) := by ring
    _ = η * (x / L) := by rw [h3, div_eq_mul_inv, mul_assoc]

/-! ### Boxes away from the support of the cutoff -/

/-- A box with `A₀ C₀ ∉ [x/κ, κx]`, `κ ≥ max(R + 1, 4/r)`, does not meet the support of
`Φ((mn-1)/x)` ("there are `O(L²)` boxes, with `H_m H_n ≍ x`", `[P-07:0260–0261]`). -/
theorem cutoff_eq_zero_of_irrelevant {Φ : ℝ → ℝ} {r R κ x : ℝ} (hr0 : 0 < r)
    (hr : ∀ t, t < r → Φ t = 0) (hR : ∀ t, R < t → Φ t = 0) (hκR : R + 1 ≤ κ)
    (hκr : 4 / r ≤ κ) (hx1 : 1 ≤ x) {A₀ C₀ : ℕ} (hA₀ : 1 ≤ A₀) (hC₀ : 1 ≤ C₀)
    (hrel : ¬(x / κ ≤ (A₀ : ℝ) * (C₀ : ℝ) ∧ (A₀ : ℝ) * (C₀ : ℝ) ≤ κ * x)) {m n : ℕ}
    (hm : m ∈ Finset.Ico A₀ (2 * A₀)) (hn : n ∈ Finset.Ico C₀ (2 * C₀)) :
    Φ (((m * n - 1 : ℕ) : ℝ) / x) = 0 := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hκ0 : 0 < κ := lt_of_lt_of_le (div_pos (by norm_num) hr0) hκr
  obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.mp hm
  obtain ⟨hn1, hn2⟩ := Finset.mem_Ico.mp hn
  have hmn : 0 < m * n := Nat.mul_pos (hA₀.trans hm1) (hC₀.trans hn1)
  have hcast : ((m * n - 1 : ℕ) : ℝ) = (m : ℝ) * (n : ℝ) - 1 := by
    rw [Nat.cast_pred hmn, Nat.cast_mul]
  have hmR : (A₀ : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm1
  have hnR : (C₀ : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn1
  have hmR2 : (m : ℝ) ≤ 2 * (A₀ : ℝ) := by exact_mod_cast hm2.le
  have hnR2 : (n : ℝ) ≤ 2 * (C₀ : ℝ) := by exact_mod_cast hn2.le
  have hA0 : (0 : ℝ) ≤ (A₀ : ℝ) := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ (C₀ : ℝ) := Nat.cast_nonneg _
  rw [hcast]
  by_cases hup : (A₀ : ℝ) * (C₀ : ℝ) ≤ κ * x
  · have hlow : (A₀ : ℝ) * (C₀ : ℝ) < x / κ := by
      by_contra hcon
      exact hrel ⟨not_lt.mp hcon, hup⟩
    apply hr
    rw [div_lt_iff₀ hx0]
    have h1 : (m : ℝ) * (n : ℝ) ≤ 2 * (A₀ : ℝ) * (2 * (C₀ : ℝ)) :=
      mul_le_mul hmR2 hnR2 (Nat.cast_nonneg n) (mul_nonneg zero_le_two hA0)
    have h2 : 4 * (x / κ) ≤ r * x := by
      have h3 : 4 ≤ κ * r := (div_le_iff₀ hr0).mp hκr
      have h4 : 4 * x ≤ κ * r * x := mul_le_mul_of_nonneg_right h3 hx0.le
      rw [← mul_div_assoc, div_le_iff₀ hκ0]
      linarith
    linarith
  · apply hR
    rw [lt_div_iff₀ hx0]
    have h1 : (A₀ : ℝ) * (C₀ : ℝ) ≤ (m : ℝ) * (n : ℝ) :=
      mul_le_mul hmR hnR hC0 (Nat.cast_nonneg m)
    have h2 : κ * x < (A₀ : ℝ) * (C₀ : ℝ) := not_le.mp hup
    have h3 : (R + 1) * x ≤ κ * x := mul_le_mul_of_nonneg_right hκR hx0.le
    linarith

/-! ### A box at the scales of Theorem 3.1 -/

/-- **A box with `A₀ C₀ ≤ κ x`** (`[P-07:0256–0304]`): with `B = An + 4`, coefficients bounded by
`L^{B+1}` and the Type II saving `L^{-(B+8)}`, the box is at most
`(3 Bs |M| κ + 4 Lip BF κ² + 2 BΦ BF J² Cτ 2^{An} κ) · x L^{-4}`. -/
theorem box_relevant_le {H b : ℕ} (hH : 0 < H) (hb : b.Coprime H) {q : ℝ} {K : ℕ}
    (𝔞 : MarkingArray K) {d : ℕ} (S : Fin d → Finset ℕ)
    {x γ κ Bs BF BΦ Lip M Cτ Aτ : ℝ} (Φ : ℝ → ℝ) (hF : CoeffFacts x γ) (hx1 : 1 ≤ x)
    (hL : 1 ≤ Real.log x) (hκ : 1 ≤ κ) {j J An B A₀ C₀ : ℕ} (hjJ : j ≤ J) (hB : B = An + 4)
    (hA₀ : x ^ γ < (A₀ : ℝ)) (hC₀ : x ^ γ < (C₀ : ℝ)) (hrel : (A₀ : ℝ) * (C₀ : ℝ) ≤ κ * x)
    (hBs : 0 < Bs) (hBF0 : 0 ≤ BF)
    (hslot : ∀ u : ℕ, 1 ≤ u → (u : ℝ) ≤ 4 * κ * x → |(slotCount S u : ℝ) - slotMass S| ≤ Bs)
    (hcoreb : ∀ u : ℕ, 1 ≤ u → (u : ℝ) ≤ 4 * κ * x → |centeredCore q 𝔞 x S u| ≤ BF)
    (hBΦ : ∀ t, |Φ t| ≤ BΦ) (hBΦL : BΦ ≤ Real.log x) (hLip0 : 0 ≤ Lip)
    (hLip : ∀ s t : ℝ, |Φ s - Φ t| ≤ Lip * |s - t|)
    (hAL : Real.log x ^ (B + 4) ≤ x ^ γ) (hγL : 1 ≤ γ * Real.log x) (h4κ : 4 * κ ≤ x)
    (hCτ : 0 ≤ Cτ) (hAτ : Aτ ≤ (An : ℝ))
    (hτ : ∀ Y : ℝ, 1 ≤ Y → ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n.divisors.card : ℝ) ^ (J * 2) ≤
      Cτ * Y * Real.log (2 * Y) ^ Aτ)
    (hTII : ∀ lo hi : ℝ, (A₀ : ℝ) ≤ lo → hi ≤ 2 * (A₀ : ℝ) →
      ∀ (lam : DirichletCharacter ℂ H) (β : ℕ → ℂ),
        RoughDyadCoefficient x ((B + 1 : ℕ) : ℝ) (C₀ : ℝ) β →
          ‖markedBilinearSum q 𝔞 x (A₀ : ℝ) (C₀ : ℝ)
            (fun m => primeMinusRough x 0 lo hi m * lam (m : ZMod H)) β
            (fun h => ((clipCore Bs S h : ℝ) : ℂ))‖ ≤
            M * ((A₀ : ℝ) * (C₀ : ℝ)) * Real.log x ^ (-((B + 4 + 4 : ℕ) : ℝ))) :
    |∑ m ∈ Finset.Ico A₀ (2 * A₀), ∑ n ∈ Finset.Ico C₀ (2 * C₀),
        Φ (((m * n - 1 : ℕ) : ℝ) / x) *
          (clsInd H b (m * n) * centeredCore q 𝔞 x S (m * n - 1) * diffCoeff x γ m) *
            beta x γ j n| ≤
      (3 * Bs * |M| * κ + 4 * Lip * BF * κ ^ 2 + 2 * BΦ * BF * (J : ℝ) ^ 2 * Cτ * 2 ^ An * κ) *
        (x * (Real.log x ^ 4)⁻¹) := by
  subst hB
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL
  have hκ0 : 0 ≤ κ := le_trans zero_le_one hκ
  have hBΦ0 : 0 ≤ BΦ := (abs_nonneg _).trans (hBΦ 0)
  have hA₀r : (1 : ℝ) < (A₀ : ℝ) := lt_of_le_of_lt hF.one_le hA₀
  have hC₀r : (1 : ℝ) < (C₀ : ℝ) := lt_of_le_of_lt hF.one_le hC₀
  have hA₀2 : 2 ≤ A₀ := by exact_mod_cast hA₀r
  have hC₀2 : 2 ≤ C₀ := by exact_mod_cast hC₀r
  have hC₀1 : 1 ≤ C₀ := by omega
  have hA0 : (0 : ℝ) ≤ (A₀ : ℝ) := Nat.cast_nonneg _
  have hC0 : (0 : ℝ) ≤ (C₀ : ℝ) := Nat.cast_nonneg _
  -- the range of `u = mn - 1` on the box
  have hu : ∀ m ∈ Finset.Ico A₀ (2 * A₀), ∀ n ∈ Finset.Ico C₀ (2 * C₀),
      1 ≤ m * n - 1 ∧ ((m * n - 1 : ℕ) : ℝ) ≤ 4 * κ * x := by
    intro m hm n hn
    obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.mp hm
    obtain ⟨hn1, hn2⟩ := Finset.mem_Ico.mp hn
    have h1 : 2 * 1 ≤ m * n := Nat.mul_le_mul (hA₀2.trans hm1) (hC₀1.trans hn1)
    refine ⟨by omega, ?_⟩
    have h2 : m * n ≤ 2 * A₀ * (2 * C₀) := Nat.mul_le_mul hm2.le hn2.le
    have h3 : ((m * n - 1 : ℕ) : ℝ) ≤ ((2 * A₀ * (2 * C₀) : ℕ) : ℝ) := Nat.cast_le.mpr (by omega)
    have h4 : ((2 * A₀ * (2 * C₀) : ℕ) : ℝ) = 4 * ((A₀ : ℝ) * (C₀ : ℝ)) := by
      push_cast
      ring
    rw [h4] at h3
    linarith
  -- the block length
  obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℕ, ℓ = ⌊(A₀ : ℝ) * (Real.log x ^ (An + 4 + 4))⁻¹⌋₊ + 1 := ⟨_, rfl⟩
  have hℓpos : 0 < ℓ := by
    rw [hℓdef]
    exact Nat.succ_pos _
  have hLE : 0 < Real.log x ^ (An + 4 + 4) := pow_pos hL0 _
  have hq0 : 0 ≤ (A₀ : ℝ) * (Real.log x ^ (An + 4 + 4))⁻¹ :=
    mul_nonneg hA0 (inv_nonneg.mpr hLE.le)
  have hℓlo : (A₀ : ℝ) * (Real.log x ^ (An + 4 + 4))⁻¹ < (ℓ : ℝ) := by
    rw [hℓdef]
    push_cast
    exact Nat.lt_floor_add_one _
  have hq1 : 1 ≤ (A₀ : ℝ) * (Real.log x ^ (An + 4 + 4))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hLE, one_mul]
    exact hAL.trans hA₀.le
  have hℓhi : (ℓ : ℝ) ≤ 2 * (A₀ : ℝ) * (Real.log x ^ (An + 4 + 4))⁻¹ := by
    have h : (ℓ : ℝ) ≤ (A₀ : ℝ) * (Real.log x ^ (An + 4 + 4))⁻¹ + 1 := by
      rw [hℓdef]
      push_cast
      linarith [Nat.floor_le hq0]
    linarith
  -- the number of blocks
  have hcK : ((Finset.Icc (A₀ / ℓ) (2 * A₀ / ℓ)).card : ℝ) ≤ 3 * Real.log x ^ (An + 4 + 4) := by
    rw [Nat.card_Icc]
    have h1 : 2 * A₀ / ℓ + 1 - A₀ / ℓ ≤ 2 * A₀ / ℓ + 1 := Nat.sub_le _ _
    have h2 : ((2 * A₀ / ℓ : ℕ) : ℝ) ≤ ((2 * A₀ : ℕ) : ℝ) / (ℓ : ℝ) := Nat.cast_div_le
    have h4 : (A₀ : ℝ) ≤ Real.log x ^ (An + 4 + 4) * (ℓ : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hℓlo.le hLE.le
      rwa [mul_comm (A₀ : ℝ), mul_inv_cancel_left₀ hLE.ne'] at h
    have h3 : ((2 * A₀ : ℕ) : ℝ) / (ℓ : ℝ) ≤ 2 * Real.log x ^ (An + 4 + 4) := by
      rw [div_le_iff₀ (Nat.cast_pos.mpr hℓpos)]
      push_cast
      linarith
    have h5 : (1 : ℝ) ≤ Real.log x ^ (An + 4 + 4) := one_le_pow₀ hL
    have h6 : ((2 * A₀ / ℓ + 1 - A₀ / ℓ : ℕ) : ℝ) ≤ ((2 * A₀ / ℓ + 1 : ℕ) : ℝ) :=
      Nat.cast_le.mpr h1
    have h7 : ((2 * A₀ / ℓ + 1 : ℕ) : ℝ) = ((2 * A₀ / ℓ : ℕ) : ℝ) + 1 := Nat.cast_succ _
    linarith
  -- the truncation level and the bound of the coefficients
  have hT0 : 0 < Real.log x ^ (An + 4) := pow_pos hL0 _
  have hC : Real.log x ^ (An + 4) * BΦ ≤ Real.log x ^ ((An + 4 + 1 : ℕ) : ℝ) := by
    rw [Real.rpow_natCast, pow_succ]
    exact mul_le_mul_of_nonneg_left hBΦL hT0.le
  have hBox := abs_box_concrete_le hH hb 𝔞 S Φ hF hx0 (j := j) hA₀ hC₀1 hℓpos hBs hBF0
    (fun m hm n hn => hslot _ (hu m hm n hn).1 (hu m hm n hn).2)
    (fun m hm n hn => hcoreb _ (hu m hm n hn).1 (hu m hm n hn).2)
    hT0.le hBΦ hLip0 hLip hC hTII
  -- the three contributions
  have hMb : M * ((A₀ : ℝ) * (C₀ : ℝ)) * Real.log x ^ (-((An + 4 + 4 + 4 : ℕ) : ℝ)) ≤
      |M| * ((A₀ : ℝ) * (C₀ : ℝ)) * (Real.log x ^ (An + 4 + 4 + 4))⁻¹ := by
    rw [Real.rpow_neg hL0.le, Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_abs_self M) (mul_nonneg hA0 hC0))
      (inv_nonneg.mpr (pow_nonneg hL0.le _))
  have h1 : ((Finset.Icc (A₀ / ℓ) (2 * A₀ / ℓ)).card : ℝ) *
      (Bs * (M * ((A₀ : ℝ) * (C₀ : ℝ)) * Real.log x ^ (-((An + 4 + 4 + 4 : ℕ) : ℝ)))) ≤
      3 * Bs * |M| * κ * (x * (Real.log x ^ 4)⁻¹) :=
    (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hMb hBs.le) (Nat.cast_nonneg _)).trans
      (term_one_le hBs.le (abs_nonneg M) hL hx0.le (Nat.cast_nonneg _) hcK hrel hκ0)
  have h2 : (A₀ : ℝ) * (C₀ : ℝ) *
      (Lip * ((ℓ : ℝ) * ((2 * C₀ : ℕ) : ℝ) / x) * BF * Real.log x ^ (An + 4)) ≤
      4 * Lip * BF * κ ^ 2 * (x * (Real.log x ^ 4)⁻¹) := by
    have e : ((2 * C₀ : ℕ) : ℝ) = 2 * (C₀ : ℝ) := by
      push_cast
      ring
    rw [e]
    exact term_two_le hL hx0 hLip0 hBF0 hA0 hC0 hrel hℓhi
  have h3 : (A₀ : ℝ) * (BΦ * BF *
      ∑ n ∈ Finset.Ico C₀ (2 * C₀), betaHi (Real.log x ^ (An + 4)) x γ j n) ≤
      2 * BΦ * BF * (J : ℝ) ^ 2 * Cτ * 2 ^ An * κ * (x * (Real.log x ^ 4)⁻¹) := by
    have hsum := sum_betaHi_le hF hT0 hjJ hτ hC₀1 (show 1 ≤ 2 * C₀ by omega)
    have e : ((2 * C₀ : ℕ) : ℝ) = 2 * (C₀ : ℝ) := by
      push_cast
      ring
    rw [e] at hsum
    have hC₀le : (C₀ : ℝ) ≤ κ * x := by
      have h : (C₀ : ℝ) ≤ (A₀ : ℝ) * (C₀ : ℝ) := le_mul_of_one_le_left hC0 hA₀r.le
      linarith
    have ht1 : 1 ≤ Real.log (2 * (2 * (C₀ : ℝ))) := by
      have h : x ^ γ ≤ 2 * (2 * (C₀ : ℝ)) := by linarith
      have h' := Real.log_le_log (Real.rpow_pos_of_pos hx0 γ) h
      rw [Real.log_rpow hx0] at h'
      linarith
    have ht2 : Real.log (2 * (2 * (C₀ : ℝ))) ≤ 2 * Real.log x := by
      have h : 2 * (2 * (C₀ : ℝ)) ≤ x * x := by nlinarith
      have h' := Real.log_le_log (by linarith) h
      rw [Real.log_mul hx0.ne' hx0.ne'] at h'
      linarith
    have hlg : Real.log (2 * (2 * (C₀ : ℝ))) ^ Aτ ≤ 2 ^ An * Real.log x ^ An :=
      calc Real.log (2 * (2 * (C₀ : ℝ))) ^ Aτ
          ≤ Real.log (2 * (2 * (C₀ : ℝ))) ^ ((An : ℕ) : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le ht1 hAτ
        _ = Real.log (2 * (2 * (C₀ : ℝ))) ^ An := Real.rpow_natCast _ _
        _ ≤ (2 * Real.log x) ^ An := pow_le_pow_left₀ (le_trans zero_le_one ht1) ht2 An
        _ = 2 ^ An * Real.log x ^ An := mul_pow _ _ _
    exact term_three_le hL hBΦ0 hBF0 (sq_nonneg _) hCτ hA0 hC0 hrel hlg hsum
  exact hBox.trans ((add_le_add (add_le_add h1 h2) h3).trans (le_of_eq (by ring)))

end Proxy

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
