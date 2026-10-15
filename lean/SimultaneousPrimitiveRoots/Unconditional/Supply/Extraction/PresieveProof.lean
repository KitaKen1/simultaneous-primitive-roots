module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.PresieveTools
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Assembly
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Sanity

/-!
# The presieve step (ext:presift)

`presieveLink d H b hH hq : PresieveLink d H b q` (`[P-07:0196–0228]`, with the class of
`[PUB-tex:0360–0383, 0523–0525]`), for `0 < H` and `0 ≤ q`, for every number of slots: the field
`presieve` of `ExtractionOpenLeaves d H b q q₀`.

With `γ = c₀/(4h+3)`, `z = x^γ` and the block sieve for shifted sums (`Presieve.shiftSum_sieve`):

* the two weights `Φ(u/x) 1_{u+1 ≡ b} 𝒲(u) f_x(u)` and `Φ(u/x) 1_{u+1 ≡ b} 𝒲(u)` are nonnegative
  (`0 ≤ q`), with main terms `X₁ = (x/H)(∫Φ) C_x m_𝒲` and `X₂ = (x/H)(∫Φ) m_𝒲`;
* "the sieve remainder is bounded by the sum in Lemma 7.2, because `z^{4h+2} < x^{c₀}`"
  (`Presieve.sum_Icc_le_progressionRemainder`); the two forms of Lemma 7.2 are the hypotheses
  `ProgressionSlots`, `ProgressionUnit` for the family of the single array and the monomial `𝒲`
  (`arraysDisjoint_single`, `pairWeight_some_none`, `familyPrimes_single`), with `A = 2`;
* "subtract the second sieve formula times `C_x` from the first; their main terms cancel, while
  each relative sieve error is `O(e^{-h})`" (`X₁ = C_x X₂`);
* `∏_{r' ≤ z} (1 - g(r')) ≤ 2^{ω(H)} (e^{-γ_E} + 1)/(γ L)` (`Presieve.eventually_sieveProduct_le`,
  Mertens' product) and `C_x ≤ B` (`SlotBounded d`);
* `m_𝒲 ≥ c_K > 0` (`ModelBounds`) absorbs the remainders `O(x L^{-2})` into `η m_𝒲 x/L`.

The constant is `C₁ = 2 M_s |B| (∫Φ) 2^{ω(H)} (e^{-γ_E} + 1)`, where `M_s` is the constant of the
block sieve: it does not depend on `h`, `K` or the array, as the statement requires. `h₀` is the
depth of the block sieve.

The hypotheses `b.Coprime H` and `q < 1` are not needed for the link: the class enters only through
the density `g` and the hypotheses `ProgressionSlots d H b q`, `ProgressionUnit H b q`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

open Filter
open scoped Topology

noncomputable section

namespace Presieve

/-- The arithmetic of the presieve step: the two sieve formulas with main terms `X₁ = C_x X₂`, the
size of the sieve product, and the remainders. -/
theorem presieve_arith
    {S₁ S₂ X₁ X₂ V Cx Ms Eh RS₁ RS₂ M₁ M₂ Bs I CV γ L x m cK η : ℝ} {H : ℕ}
    (hH : 0 < H) (hx : 0 < x) (hL : 0 < L) (hγ : 0 < γ) (hMs : 0 ≤ Ms) (hEh : 0 ≤ Eh)
    (hI : 0 ≤ I) (hCx0 : 0 ≤ Cx) (hCx : Cx ≤ Bs) (hcK : 0 < cK) (hm : cK ≤ m) (hη : 0 < η)
    (hV0 : 0 ≤ V) (hV : V * (γ * L) ≤ CV)
    (hX₁ : X₁ = x / (H : ℝ) * I * Cx * m) (hX₂ : X₂ = x / (H : ℝ) * I * 1 * m)
    (e1 : |S₁ - X₁ * V| ≤ Ms * Eh * (X₁ * V) + Ms * RS₁)
    (e2 : |S₂ - X₂ * V| ≤ Ms * Eh * (X₂ * V) + Ms * RS₂)
    (hRS₁ : RS₁ ≤ M₁ * x * L ^ (-(2 : ℝ))) (hRS₂0 : 0 ≤ RS₂)
    (hRS₂ : RS₂ ≤ M₂ * x * L ^ (-(2 : ℝ)))
    (hE : Ms * (|M₁| + |Bs| * |M₂|) / (η * cK) ≤ L) :
    |S₁ - Cx * S₂| ≤ (2 * Ms * |Bs| * I * CV * Eh * (1 / γ) + η) * m * (x / L) := by
  have hm0 : 0 < m := lt_of_lt_of_le hcK hm
  have hBs : Cx ≤ |Bs| := hCx.trans (le_abs_self Bs)
  have hH1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
  have hLne : L ≠ 0 := hL.ne'
  have hX₁₂ : X₁ = Cx * X₂ := by
    rw [hX₁, hX₂]
    ring
  -- the two sieve formulas
  have hsplit : S₁ - Cx * S₂ = (S₁ - X₁ * V) - Cx * (S₂ - X₂ * V) := by
    rw [hX₁₂]
    ring
  have hA : |S₁ - Cx * S₂| ≤ 2 * (Ms * Eh * (X₁ * V)) + Ms * (RS₁ + Cx * RS₂) := by
    have h1 : |Cx * (S₂ - X₂ * V)| ≤ Cx * (Ms * Eh * (X₂ * V) + Ms * RS₂) := by
      rw [abs_mul, abs_of_nonneg hCx0]
      exact mul_le_mul_of_nonneg_left e2 hCx0
    calc |S₁ - Cx * S₂| = |(S₁ - X₁ * V) - Cx * (S₂ - X₂ * V)| := by rw [hsplit]
      _ ≤ |S₁ - X₁ * V| + |Cx * (S₂ - X₂ * V)| := abs_sub _ _
      _ ≤ (Ms * Eh * (X₁ * V) + Ms * RS₁) + Cx * (Ms * Eh * (X₂ * V) + Ms * RS₂) :=
          add_le_add e1 h1
      _ = 2 * (Ms * Eh * (X₁ * V)) + Ms * (RS₁ + Cx * RS₂) := by
          rw [hX₁₂]
          ring
  -- the main term
  have hγL : 0 < γ * L := mul_pos hγ hL
  have hVle : V ≤ CV / (γ * L) := (le_div_iff₀ hγL).mpr hV
  have hxH : x / (H : ℝ) ≤ x := div_le_self hx.le hH1
  have hxI : 0 ≤ x * I := mul_nonneg hx.le hI
  have hB : X₁ * V ≤ x * I * |Bs| * m * (CV / (γ * L)) := by
    rw [hX₁]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right
        (mul_le_mul (mul_le_mul_of_nonneg_right hxH hI) hBs hCx0 hxI) hm0.le)
      hVle hV0 (mul_nonneg (mul_nonneg hxI (abs_nonneg _)) hm0.le)
  -- the remainders
  have hL2 : L ^ (-(2 : ℝ)) = (L ^ 2)⁻¹ := by rw [Real.rpow_neg hL.le, Real.rpow_two]
  have hxL2 : 0 ≤ x * (L ^ 2)⁻¹ := mul_nonneg hx.le (inv_pos.mpr (pow_pos hL 2)).le
  rw [hL2] at hRS₁ hRS₂
  have h1 : RS₁ ≤ |M₁| * (x * (L ^ 2)⁻¹) :=
    hRS₁.trans (by
      calc M₁ * x * (L ^ 2)⁻¹ = M₁ * (x * (L ^ 2)⁻¹) := by ring
        _ ≤ |M₁| * (x * (L ^ 2)⁻¹) := mul_le_mul_of_nonneg_right (le_abs_self M₁) hxL2)
  have h2 : Cx * RS₂ ≤ |Bs| * |M₂| * (x * (L ^ 2)⁻¹) := by
    have h3 : RS₂ ≤ |M₂| * (x * (L ^ 2)⁻¹) :=
      hRS₂.trans (by
        calc M₂ * x * (L ^ 2)⁻¹ = M₂ * (x * (L ^ 2)⁻¹) := by ring
          _ ≤ |M₂| * (x * (L ^ 2)⁻¹) := mul_le_mul_of_nonneg_right (le_abs_self M₂) hxL2)
    calc Cx * RS₂ ≤ |Bs| * (|M₂| * (x * (L ^ 2)⁻¹)) := mul_le_mul hBs h3 hRS₂0 (abs_nonneg _)
      _ = |Bs| * |M₂| * (x * (L ^ 2)⁻¹) := by ring
  have hηc : 0 < η * cK := mul_pos hη hcK
  have h4 : Ms * (|M₁| + |Bs| * |M₂|) ≤ L * (η * cK) := (div_le_iff₀ hηc).mp hE
  have hC : Ms * (RS₁ + Cx * RS₂) ≤ η * m * (x / L) :=
    calc Ms * (RS₁ + Cx * RS₂)
        ≤ Ms * (|M₁| * (x * (L ^ 2)⁻¹) + |Bs| * |M₂| * (x * (L ^ 2)⁻¹)) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 h2) hMs
      _ = Ms * (|M₁| + |Bs| * |M₂|) * (x * (L ^ 2)⁻¹) := by ring
      _ ≤ L * (η * cK) * (x * (L ^ 2)⁻¹) := mul_le_mul_of_nonneg_right h4 hxL2
      _ = η * cK * (x / L) := by
          rw [div_eq_mul_inv, sq, mul_inv]
          calc L * (η * cK) * (x * (L⁻¹ * L⁻¹)) = η * cK * (x * L⁻¹) * (L * L⁻¹) := by ring
            _ = η * cK * (x * L⁻¹) := by rw [mul_inv_cancel₀ hLne, mul_one]
      _ ≤ η * m * (x / L) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hη.le)
            (div_nonneg hx.le hL.le)
  calc |S₁ - Cx * S₂| ≤ 2 * (Ms * Eh * (X₁ * V)) + Ms * (RS₁ + Cx * RS₂) := hA
    _ ≤ 2 * (Ms * Eh * (x * I * |Bs| * m * (CV / (γ * L)))) + η * m * (x / L) :=
        add_le_add (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hB (mul_nonneg hMs hEh)) zero_le_two) hC
    _ = (2 * Ms * |Bs| * I * CV * Eh * (1 / γ) + η) * m * (x / L) := by ring

end Presieve

/-- **The presieve step** (`[P-07:0196–0228]`, (ext:presift) with the class), for every number of
slots: the field `presieve` of `ExtractionOpenLeaves d H b q q₀`. -/
theorem presieveLink (d H b : ℕ) (hH : 0 < H) {q : ℝ} (hq : 0 ≤ q) : PresieveLink d H b q := by
  intro hPS hPU hMB hSB hBS hMP hM ε hε c₀ hc₀ hc₀ε hc₀4 Φ hΦ
  obtain ⟨R, hR0, hR⟩ := hΦ.exists_upper
  obtain ⟨Ms, hMs0, h₀, hsieve⟩ := Presieve.shiftSum_sieve hBS hM
  obtain ⟨Bs, hBs⟩ := hSB ε hε R hR0
  have hint : 0 ≤ ∫ t, Φ t := MeasureTheory.integral_nonneg fun t => hΦ.nonneg t
  obtain ⟨CV, hCV⟩ : ∃ CV : ℝ, CV = 2 ^ H.primeFactors.card *
      (Real.exp (-Real.eulerMascheroniConstant) + 1) := ⟨_, rfl⟩
  have hCV0 : 0 ≤ CV := by
    rw [hCV]
    exact mul_nonneg (pow_nonneg zero_le_two _) (add_nonneg (Real.exp_pos _).le zero_le_one)
  refine ⟨2 * Ms * |Bs| * (∫ t, Φ t) * CV,
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hMs0) (abs_nonneg _)) hint) hCV0,
    h₀, ?_⟩
  intro h hh heven K 𝔞 η hη
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = c₀ / (4 * (h : ℝ) + 3) := ⟨_, rfl⟩
  have h43 : (0 : ℝ) < 4 * (h : ℝ) + 3 := by positivity
  have hγ0 : 0 < γ := by
    rw [hγ]
    exact div_pos hc₀ h43
  -- Lemma 7.2 for the family of the single array
  obtain ⟨M₁, x₁, hrem₁⟩ := hPS ε hε c₀ hc₀ hc₀ε Φ hΦ 1 K (fun _ => 𝔞)
    (arraysDisjoint_single 𝔞) 2 two_pos
  obtain ⟨M₂, x₂, hrem₂⟩ := hPU c₀ hc₀ hc₀4 Φ hΦ 1 K (fun _ => 𝔞)
    (arraysDisjoint_single 𝔞) 2 two_pos
  obtain ⟨cK, CK, hcK, hmodel⟩ := hMB K
  have hVev : ∀ᶠ x : ℝ in atTop,
      (∏ p ∈ Presieve.sievePrimes (x ^ γ), (1 - Presieve.sieveDensity H p)) *
        Real.log (x ^ γ) ≤ CV := by
    rw [hCV]
    exact (tendsto_rpow_atTop hγ0).eventually (Presieve.eventually_sieveProduct_le hMP hH)
  filter_upwards [hBs, hmodel 𝔞, eventually_ge_atTop x₁, eventually_ge_atTop x₂,
    eventually_gt_atTop (1 : ℝ), hVev,
    Real.tendsto_log_atTop.eventually_ge_atTop
      (max (Ms * (|M₁| + |Bs| * |M₂|) / (η * cK)) 1)]
    with x hslot hm hx₁ hx₂ hx1 hV hLE S hS
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ Real.log x := (le_max_right _ _).trans hLE
  have hL0 : 0 < Real.log x := by linarith
  have hEL : Ms * (|M₁| + |Bs| * |M₂|) / (η * cK) ≤ Real.log x := (le_max_left _ _).trans hLE
  have hCx : slotMass S ≤ Bs := (hslot S hS).1
  have hmlo : cK ≤ arrayMean q 𝔞 x := hm.1
  have hm0 : 0 ≤ arrayMean q 𝔞 x := hcK.le.trans hmlo
  have hCx0 : 0 ≤ slotMass S := by
    unfold slotMass
    exact Finset.sum_nonneg fun 𝔩 _ => by positivity
  -- the level of the sieve
  have hz1 : 1 ≤ x ^ γ := Real.one_le_rpow hx1.le hγ0.le
  have hz0 : 0 ≤ x ^ γ := zero_le_one.trans hz1
  have hlevel : (x ^ γ) ^ (4 * h + 2) ≤ x ^ c₀ := by
    have hcast : ((4 * h + 2 : ℕ) : ℝ) = 4 * (h : ℝ) + 2 := by
      push_cast
      ring
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, hcast]
    refine Real.rpow_le_rpow_of_exponent_le hx1.le ?_
    rw [hγ, div_mul_eq_mul_div, div_le_iff₀ h43]
    exact mul_le_mul_of_nonneg_left (by linarith) hc₀.le
  -- the two nonnegative weights
  have hWnn : ∀ u, 0 ≤ markedWeight q 𝔞 x u := fun u => markedWeight_nonneg hq 𝔞 x u
  have hF₁0 : ∀ u : ℕ, 0 ≤ (slotCount S u : ℝ) * markedWeight q 𝔞 x u := fun u =>
    mul_nonneg (Nat.cast_nonneg _) (hWnn u)
  have hF₂0 : ∀ u : ℕ, 0 ≤ (1 : ℝ) * markedWeight q 𝔞 x u := fun u =>
    mul_nonneg zero_le_one (hWnn u)
  have hxH0 : 0 ≤ x / (H : ℝ) * (∫ t, Φ t) :=
    mul_nonneg (div_nonneg hx0.le (Nat.cast_nonneg H)) hint
  have hX₁0 : 0 ≤ x / (H : ℝ) * (∫ t, Φ t) * slotMass S * arrayMean q 𝔞 x :=
    mul_nonneg (mul_nonneg hxH0 hCx0) hm0
  have hX₂0 : 0 ≤ x / (H : ℝ) * (∫ t, Φ t) * 1 * arrayMean q 𝔞 x :=
    mul_nonneg (mul_nonneg hxH0 zero_le_one) hm0
  obtain ⟨hs1, -⟩ := hsieve Φ R hR hΦ.nonneg x hx0 H b
    (fun u => (slotCount S u : ℝ) * markedWeight q 𝔞 x u) hF₁0 (x ^ γ) hz1 _ hX₁0
  obtain ⟨hs2, -⟩ := hsieve Φ R hR hΦ.nonneg x hx0 H b
    (fun u => (1 : ℝ) * markedWeight q 𝔞 x u) hF₂0 (x ^ γ) hz1 _ hX₂0
  have e1 := hs1 h hh heven
  have e2 := hs2 h hh heven
  -- the remainders are those of Lemma 7.2 for the monomial `𝒲`
  have hW : pairWeight q (fun _ : Fin 1 => 𝔞) x (some 0) none = markedWeight q 𝔞 x :=
    funext fun u => pairWeight_some_none q _ x 0 u
  have hPR₁ := hrem₁ x hx₁ (some 0) none S hS
  have hPR₂ := hrem₂ x hx₂ (some 0) none
  rw [hW, familyPrimes_single] at hPR₁ hPR₂
  have hRS₁ := (Presieve.sum_Icc_le_progressionRemainder (H := H) (b := b) (Φ := Φ) hlevel
    (fun u => (slotCount S u : ℝ)) (slotMass S) (markedWeight q 𝔞 x) (arrayMean q 𝔞 x)
    (X := x / (H : ℝ) * (∫ t, Φ t) * slotMass S * arrayMean q 𝔞 x) rfl
    (F := fun u => (slotCount S u : ℝ) * markedWeight q 𝔞 x u) (fun _ => rfl)).trans hPR₁
  have hRS₂ := (Presieve.sum_Icc_le_progressionRemainder (H := H) (b := b) (Φ := Φ) hlevel
    (fun _ => (1 : ℝ)) 1 (markedWeight q 𝔞 x) (arrayMean q 𝔞 x)
    (X := x / (H : ℝ) * (∫ t, Φ t) * 1 * arrayMean q 𝔞 x) rfl
    (F := fun u => (1 : ℝ) * markedWeight q 𝔞 x u) (fun _ => rfl)).trans hPR₂
  have hRS₂0 : 0 ≤ ∑ r ∈ Finset.Icc 1 ⌊(x ^ γ) ^ (4 * h + 2)⌋₊,
      |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H]) (fun u => (1 : ℝ) * markedWeight q 𝔞 x u) -
        (if r.Coprime H then x / (H : ℝ) * (∫ t, Φ t) * 1 * arrayMean q 𝔞 x / (r : ℝ)
          else 0)| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  -- the sieve product
  rw [Real.log_rpow hx0 γ] at hV
  have hV0 : 0 ≤ ∏ p ∈ Presieve.sievePrimes (x ^ γ), (1 - Presieve.sieveDensity H p) := by
    refine Finset.prod_nonneg fun p hp => ?_
    have h3 := Presieve.sieveDensity_le_half H ((Presieve.mem_sievePrimes hz0).mp hp).1
    linarith
  -- the centered core is the difference of the two weights
  have hcore : ∀ u, centeredCore q 𝔞 x S u =
      (slotCount S u : ℝ) * markedWeight q 𝔞 x u -
        slotMass S * ((1 : ℝ) * markedWeight q 𝔞 x u) := fun u => by
    unfold centeredCore
    ring
  have hLHS : shiftSum Φ x (fun v => IsRough (x ^ γ) v ∧ v ≡ b [MOD H])
      (centeredCore q 𝔞 x S) =
      shiftSum Φ x (fun v => IsRough (x ^ γ) v ∧ v ≡ b [MOD H])
          (fun u => (slotCount S u : ℝ) * markedWeight q 𝔞 x u) -
        slotMass S * shiftSum Φ x (fun v => IsRough (x ^ γ) v ∧ v ≡ b [MOD H])
          (fun u => (1 : ℝ) * markedWeight q 𝔞 x u) := by
    rw [shiftSum_congr Φ x _ hcore, shiftSum_sub hR hx0, shiftSum_const_mul hR hx0]
  have key := Presieve.presieve_arith hH hx0 hL0 hγ0 hMs0 (Real.exp_pos (-(h : ℝ))).le hint
    hCx0 hCx hcK hmlo hη hV0 hV rfl rfl e1 e2 hRS₁ hRS₂0 hRS₂ hEL
  rw [← hγ, hLHS]
  refine key.trans (le_of_eq ?_)
  rw [hγ, one_div_div]

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
