module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction.Expansion
public import SimultaneousPrimitiveRoots.Unconditional.Transference.KernelCosts
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The part of the proof of [S] Theorem 4.1 after Lemma 4.3: `IdealConstructionOfContract`

Source: `verification/stage7-sources/S-03.tex`, lines 441–645 (`[S-03:0441–0645]`).

`idealConstructionOfContract : IdealConstructionOfContract`: for `E_id > 0` and `C₄ ≥ 0` there
are `m`, `J₀` and a precision `A₀'` such that, for all kernel exponents with the comparison
contract of precision `A₀'`, the residual family satisfies the conclusion of Theorem 4.1 with a
suitable `C₁` for every `J ≥ J₀`, and has at most `L^{C₁}` patterns.

## The constants

* `m`: any integer with `log (m + 1) ≥ 6 (E_id + 3) / c₀`. With `θ = 1/(m + 1)` this is the
  paper's "`-(c₀/6) log θ_m > E_id + 3`" [S-03:0535–0536]; the fraction `θ` here is the one of
  `single_group_bound` (one of the last `ℓ ≥ 1` slots is kept), not `θ_m = 2 ℓ^ℓ m^{-ℓ}`.
* `J₀ = m` ("require `J ≥ m`", [S-03:0640]). The second requirement
  `J + ℓ ≥ (m + ℓ)(m + ℓ - 1)` of [S-03:0641] belongs to the bound (eq:ideal-hoeffding-bound)
  for `θ_m`, which is not used.
* `A₀' = E_id + m C₀ log 3 + 10` [S-03:0609–0612].
* `C₁ = m C₀ log 2 + 4 q_* + 2 x_* + 1` [S-03:0619–0627].
* `x₀`: the threshold of the contract, and `log log x ≥ max 1 (3/c₀)` ("for sufficiently large
  `x` each size is at least `c₀ T / 3`", [S-03:0443–0444]).

## The steps

`core_bound` gives, for symmetric `G`, `H`,
`|⟨G, (raw + comparisons) H⟩| ≤ (δ₁ + δ₂ + δ₁ δ₂ + #comparisons · L^{-A₀'}) ‖G‖ ‖H‖`; here
`δ_i ≤ L^{-E_id-3}` (`delta_le`) and `#comparisons · L^{-A₀'} ≤ L^{-E_id-3}`
(`card_comparison_le_rpow`), so the bracket is at most `L^{-E_id}` (`final_numeric`). Since the
operator has the symmetrizing projection on both sides, this is the operator norm
(`idealOpNorm_le_of_core`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction

open scoped BigOperators ComplexConjugate NNReal

noncomputable section

/-! ### Elementary inequalities -/

theorem two_pow_le_rpow {L : ℝ} (hL : 0 < L) {n : ℕ} {c : ℝ}
    (h : (n : ℝ) * Real.log 2 ≤ Real.log L * c) : (2 : ℝ) ^ n ≤ L ^ c := by
  have h2 : (2 : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log two_pos]
  rw [h2, Real.rpow_def_of_pos hL]
  exact Real.exp_le_exp.mpr h

theorem one_add_rpow_le {L a c : ℝ} (hL : 2 ≤ L) (ha : 0 ≤ a) (hc : a + 1 ≤ c) :
    1 + L ^ a ≤ L ^ c := by
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  have h1 : (1 : ℝ) ≤ L ^ a := Real.one_le_rpow hL1 ha
  have h2 : L ^ (a + 1) ≤ L ^ c := Real.rpow_le_rpow_of_exponent_le hL1 hc
  have h3 : L ^ (a + 1) = L ^ a * L := Real.rpow_add_one hL0.ne' a
  have h4 : L ^ a * 2 ≤ L ^ a * L := mul_le_mul_of_nonneg_left hL (le_trans zero_le_one h1)
  rw [h3] at h2
  linarith

theorem sqrt_inv_pow_le {u : ℝ} (hu : 0 < u) (s : ℕ) (t : ℝ)
    (h : 2 * t ≤ (s : ℝ) * Real.log u) : Real.sqrt ((1 / u) ^ s) ≤ Real.exp (-t) := by
  have hpow : u ^ s = Real.exp ((s : ℝ) * Real.log u) := by
    rw [Real.exp_nat_mul, Real.exp_log hu]
  have h1 : (1 / u) ^ s = Real.exp (-((s : ℝ) * Real.log u)) := by
    rw [one_div, inv_pow, hpow, Real.exp_neg]
  have h2 : Real.exp (-((s : ℝ) * Real.log u)) ≤ Real.exp (-t) ^ 2 := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    push_cast
    linarith
  have h3 : (1 / u) ^ s ≤ Real.exp (-t) ^ 2 := by
    rw [h1]
    exact h2
  calc Real.sqrt ((1 / u) ^ s) ≤ Real.sqrt (Real.exp (-t) ^ 2) := Real.sqrt_le_sqrt h3
    _ = Real.exp (-t) := Real.sqrt_sq (Real.exp_pos _).le

theorem log_facts {c₀ x : ℝ} (hx : Real.exp (Real.exp (max 1 (3 / c₀))) ≤ x) :
    2 ≤ Real.log x ∧ 1 ≤ Real.log (Real.log x) ∧ 3 / c₀ ≤ Real.log (Real.log x) := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : Real.exp (max 1 (3 / c₀)) ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos _) hL
  have hT : max 1 (3 / c₀) ≤ Real.log (Real.log x) := (Real.le_log_iff_exp_le hL0).mpr hL
  have hT1 : 1 ≤ Real.log (Real.log x) := le_trans (le_max_left _ _) hT
  have hT3 : 3 / c₀ ≤ Real.log (Real.log x) := le_trans (le_max_right _ _) hT
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hL2 : 2 ≤ Real.log x :=
    le_trans h2 (le_trans (Real.exp_le_exp.mpr (le_max_left _ _)) hL)
  exact ⟨hL2, hT1, hT3⟩

/-- `δ₁ + δ₂ + δ₁ δ₂ + e ≤ L^{-E}` when each of `δ₁, δ₂, e` is at most `L^{-E-3}`. -/
theorem final_numeric {L E d1 d2 e : ℝ} (hL : 0 < L) (hT : 1 ≤ Real.log L) (hE : 0 < E)
    (h1 : d1 ≤ L ^ (-(E + 3))) (h2 : d2 ≤ L ^ (-(E + 3))) (h3 : e ≤ L ^ (-(E + 3)))
    (hd2 : 0 ≤ d2) : d1 + d2 + d1 * d2 + e ≤ L ^ (-E) := by
  have hy : L ^ (-(E + 3)) = Real.exp (Real.log L * (-(E + 3))) := Real.rpow_def_of_pos hL _
  have hz : L ^ (-E) = Real.exp (Real.log L * (-E)) := Real.rpow_def_of_pos hL _
  have hsplit : Real.exp (Real.log L * (-E)) =
      Real.exp (Real.log L * (-(E + 3))) * Real.exp (3 * Real.log L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h4 : (4 : ℝ) ≤ Real.exp (3 * Real.log L) := by
    have h := Real.add_one_le_exp (3 * Real.log L)
    linarith
  have hy0 : 0 < Real.exp (Real.log L * (-(E + 3))) := Real.exp_pos _
  have hneg : Real.log L * (-(E + 3)) ≤ 0 := by
    have hp : 0 < Real.log L * (E + 3) := mul_pos (lt_of_lt_of_le one_pos hT) (by linarith)
    linarith
  have hy1 : Real.exp (Real.log L * (-(E + 3))) ≤ 1 :=
    calc Real.exp (Real.log L * (-(E + 3))) ≤ Real.exp 0 := Real.exp_le_exp.mpr hneg
      _ = 1 := Real.exp_zero
  rw [hy] at h1 h2 h3
  rw [hz, hsplit]
  have p1 : d1 * d2 ≤ Real.exp (Real.log L * (-(E + 3))) * Real.exp (Real.log L * (-(E + 3))) :=
    mul_le_mul h1 h2 hd2 hy0.le
  have p2 : Real.exp (Real.log L * (-(E + 3))) * 4 ≤
      Real.exp (Real.log L * (-(E + 3))) * Real.exp (3 * Real.log L) :=
    mul_le_mul_of_nonneg_left h4 hy0.le
  have p3 : Real.exp (Real.log L * (-(E + 3))) * Real.exp (Real.log L * (-(E + 3))) ≤
      Real.exp (Real.log L * (-(E + 3))) * 1 := mul_le_mul_of_nonneg_left hy1 hy0.le
  linarith

/-! ### The two blocks -/

section Blocks

variable {B : Type} [Fintype B]

/-- Each block of a balanced split has at least `(|ℬ| - 1)/2` groups. -/
theorem two_mul_blockSet_card {blk : B → Bool} (hbal : BalancedSplit blk) (b : Bool) :
    Fintype.card B ≤ 2 * (blockSet blk b).card + 1 := by
  have hsum : (blockSet blk true).card + (blockSet blk false).card = Fintype.card B := by
    unfold blockSet
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib, ← Finset.card_univ,
      Finset.card_eq_sum_ones]
    refine Finset.sum_congr rfl fun g _ => ?_
    cases blk g <;> simp
  have h1 : (blockSet blk true).card ≤ (blockSet blk false).card + 1 := hbal.1
  have h2 : (blockSet blk false).card ≤ (blockSet blk true).card + 1 := hbal.2
  cases b <;> omega

end Blocks

section Asymptotics

variable {P : GroupParams} {x : ℝ} {S B : Type} [Fintype S] [Fintype B] [DecidableEq B]

/-- "The number of comparisons is at most `2^P ≤ L^{m C₀ log 2}`" [S-03:0619–0620]. -/
theorem card_comparison_le_rpow (𝔊 : PrimeGroups P x S B) (hL : 0 < Real.log x)
    (blk : B → Bool) (J m : ℕ) :
    (Fintype.card {C : B → Finset (Fin J) // IsComparison blk m C} : ℝ) ≤
      Real.log x ^ ((m : ℝ) * P.C₀ * Real.log 2) := by
  have h1 : (Fintype.card {C : B → Finset (Fin J) // IsComparison blk m C} : ℝ) ≤
      (2 : ℝ) ^ (m * Fintype.card B) := by
    exact_mod_cast card_comparison_le (J := J) blk m
  refine h1.trans (two_pow_le_rpow hL ?_)
  have hB := 𝔊.card_big_le
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h3 := mul_le_mul_of_nonneg_left hB (mul_nonneg hm h2)
  push_cast
  linarith

omit [DecidableEq B] in
/-- (eq:ideal-full-component) in terms of `L` [S-03:0535–0539]: `θ^{s_i/2} ≤ L^{-E_id-3}`. -/
theorem delta_le (𝔊 : PrimeGroups P x S B) {E : ℝ} (hE : 0 < E) {m : ℕ}
    (hm : 6 * (E + 3) / P.c₀ ≤ Real.log ((m : ℝ) + 1)) (hL0 : 0 < Real.log x)
    (hT3 : 3 / P.c₀ ≤ Real.log (Real.log x)) {blk : B → Bool} (hbal : BalancedSplit blk)
    (b : Bool) :
    Real.sqrt ((1 / ((m : ℝ) + 1)) ^ (blockSet blk b).card) ≤ Real.log x ^ (-(E + 3)) := by
  have hu : (0 : ℝ) < (m : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hc0 : P.c₀ ≠ 0 := P.c₀_pos.ne'
  have hcard : (Fintype.card B : ℝ) ≤ 2 * ((blockSet blk b).card : ℝ) + 1 := by
    exact_mod_cast two_mul_blockSet_card hbal b
  have hge := 𝔊.card_big_ge
  have hc3 : 3 ≤ Real.log (Real.log x) * P.c₀ := (div_le_iff₀ P.c₀_pos).mp hT3
  have hs : P.c₀ * Real.log (Real.log x) / 3 ≤ ((blockSet blk b).card : ℝ) := by linarith
  have hκ0 : 0 ≤ 6 * (E + 3) / P.c₀ := div_nonneg (by linarith) P.c₀_pos.le
  have hkey : 2 * (Real.log (Real.log x) * (E + 3)) ≤
      ((blockSet blk b).card : ℝ) * Real.log ((m : ℝ) + 1) := by
    have h1 : P.c₀ * Real.log (Real.log x) / 3 * (6 * (E + 3) / P.c₀) ≤
        ((blockSet blk b).card : ℝ) * Real.log ((m : ℝ) + 1) :=
      mul_le_mul hs hm hκ0 (Nat.cast_nonneg _)
    have h2 : P.c₀ * Real.log (Real.log x) / 3 * (6 * (E + 3) / P.c₀) =
        (P.c₀ / P.c₀) * (2 * (Real.log (Real.log x) * (E + 3))) := by ring
    rw [h2, div_self hc0, one_mul] at h1
    exact h1
  have h := sqrt_inv_pow_le hu (blockSet blk b).card (Real.log (Real.log x) * (E + 3)) hkey
  have e : Real.log (Real.log x) * (-(E + 3)) = -(Real.log (Real.log x) * (E + 3)) := by ring
  rw [Real.rpow_def_of_pos hL0, e]
  exact h

end Asymptotics

/-! ### The pattern mass -/

section Mass

variable {B : Type} [Fintype B] [DecidableEq B]

/-- "(eq:ideal-cell-costs) bounds each coefficient by `Q⁴ ξ⁻²`" [S-03:0621–0622]. -/
theorem patternMass_comparisonFamily_le (big : B → Finset ℕ) (J ℓ m : ℕ) (blk : B → Bool)
    (Q h ξ : ℝ) (hQ : 0 ≤ Q) (hξ : 0 < ξ) :
    patternMass (comparisonFamily big J ℓ m blk Q h ξ) ≤
      1 + (Fintype.card {C : B → Finset (Fin J) // IsComparison blk m C} : ℝ) *
        ((Q ^ 2 * ξ⁻¹) * (Q ^ 2 * ξ⁻¹)) := by
  have hk : ∀ (Λ : B → Finset (Fin J)) (D X : ℕ),
      ‖cellKernel big Λ Q h ξ D X‖ ≤ Q ^ 2 * ξ⁻¹ := fun Λ D X =>
    (norm_cellKernel_le big Λ Q h ξ hξ D X).trans
      (mul_le_mul_of_nonneg_right (primitiveCharCount_le_sq Q hQ) (inv_nonneg.mpr hξ.le))
  have hκ : 0 ≤ Q ^ 2 * ξ⁻¹ := mul_nonneg (sq_nonneg Q) (inv_nonneg.mpr hξ.le)
  have hκ0 : 0 ≤ (Q ^ 2 * ξ⁻¹) * (Q ^ 2 * ξ⁻¹) := mul_nonneg hκ hκ
  have hraw : ((comparisonFamily big J ℓ m blk Q h ξ none).supNorm : ℝ) ≤ 1 := by
    have h0 : (Pattern.raw big J ℓ).supNorm ≤ 1 := Pattern.supNorm_raw_le
    exact_mod_cast h0
  have hcomp : ∀ C : {C : B → Finset (Fin J) // IsComparison blk m C},
      ((comparisonFamily big J ℓ m blk Q h ξ (some C)).supNorm : ℝ) ≤
        (Q ^ 2 * ξ⁻¹) * (Q ^ 2 * ξ⁻¹) := by
    intro C
    have hle : (comparisonFamily big J ℓ m blk Q h ξ (some C)).supNorm ≤
        Real.toNNReal ((Q ^ 2 * ξ⁻¹) * (Q ^ 2 * ξ⁻¹)) := by
      unfold Pattern.supNorm
      refine Finset.sup_le fun a _ => ?_
      refine NNReal.coe_le_coe.mp ?_
      rw [coe_nnnorm, Real.coe_toNNReal _ hκ0]
      show ‖-((-1 : ℂ) ^ (∑ g, (C.1 g).card)) *
        (cellKernel big _ Q h ξ _ _ * cellKernel big _ Q h ξ _ _)‖ ≤ _
      rw [norm_mul, norm_neg, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_mul]
      exact mul_le_mul (hk _ _ _) (hk _ _ _) (norm_nonneg _) hκ
    exact (NNReal.coe_le_coe.mpr hle).trans (le_of_eq (Real.coe_toNNReal _ hκ0))
  unfold patternMass
  rw [Fintype.sum_option]
  calc ((comparisonFamily big J ℓ m blk Q h ξ none).supNorm : ℝ) +
        ∑ C : {C : B → Finset (Fin J) // IsComparison blk m C},
          ((comparisonFamily big J ℓ m blk Q h ξ (some C)).supNorm : ℝ)
      ≤ 1 + ∑ _C : {C : B → Finset (Fin J) // IsComparison blk m C},
          (Q ^ 2 * ξ⁻¹) * (Q ^ 2 * ξ⁻¹) :=
        add_le_add hraw (Finset.sum_le_sum fun C _ => hcomp C)
    _ = 1 + (Fintype.card {C : B → Finset (Fin J) // IsComparison blk m C} : ℝ) *
          ((Q ^ 2 * ξ⁻¹) * (Q ^ 2 * ξ⁻¹)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Mass

/-! ### From the pairing of symmetric vectors to the operator norm -/

section Norm

variable {B : Type} [Fintype B] [DecidableEq B] {big : B → Finset ℕ} {J ℓ : ℕ}

/-- "It suffices to bound pairings against symmetric vectors `F, H`, since the operator has the
orthogonal symmetrizing projection on both sides" [S-03:0456–0458]. -/
theorem idealOpNorm_le_of_core
    (hpos : ∀ (g : B) (q : ℕ), q ∈ big g → 0 < Graph.primeGroupLaw (big g) q) {m : ℕ}
    (blk : B → Bool) (Q h ξ ζ Θ c : ℝ) (hc : 0 ≤ c)
    (hcore : ∀ G H : LabelList big J ℓ → ℂ, IsSym G → IsSym H →
      ‖wInner (idealWeight big J ℓ) G
          ((∑ ν, idealRow (comparisonFamily big J ℓ m blk Q h ξ ν) ζ Θ) H)‖ ≤
        c * (wNorm (idealWeight big J ℓ) G * wNorm (idealWeight big J ℓ) H)) :
    idealOpNorm (comparisonFamily big J ℓ m blk Q h ξ) ζ Θ ≤ c := by
  have hnn : ∀ p : LabelList big J ℓ, 0 ≤ idealWeight big J ℓ p := fun p =>
    (idealWeight_pos hpos p).le
  rw [idealOpNorm_le_iff hpos _ ζ Θ hc]
  intro F
  obtain ⟨Y, hY⟩ : ∃ Y : LabelList big J ℓ → ℂ, Y =
      (∑ ν, idealRow (comparisonFamily big J ℓ m blk Q h ξ ν) ζ Θ) (bigSym big J ℓ F) :=
    ⟨_, rfl⟩
  have hop : idealOp (comparisonFamily big J ℓ m blk Q h ξ) ζ Θ F = bigSym big J ℓ Y := by
    rw [hY]
    rfl
  have hsa : IsSA (idealWeight big J ℓ) (bigSym big J ℓ) := fun F G => wInner_bigSym F G
  have hid : bigSym big J ℓ * bigSym big J ℓ = bigSym big J ℓ :=
    LinearMap.ext fun F => bigSym_idem F
  have hHs : wNorm (idealWeight big J ℓ) (bigSym big J ℓ F) ≤ wNorm (idealWeight big J ℓ) F :=
    wNorm_apply_le_of_proj hnn hsa hid F
  have h1 : wInner (idealWeight big J ℓ) (bigSym big J ℓ Y) (bigSym big J ℓ Y) =
      wInner (idealWeight big J ℓ) (bigSym big J ℓ Y) Y := by
    have e := wInner_bigSym (bigSym big J ℓ Y) Y
    rw [bigSym_idem] at e
    exact e
  have h4 := hcore (bigSym big J ℓ Y) (bigSym big J ℓ F) (isSym_bigSym Y) (isSym_bigSym F)
  rw [← hY, ← h1, wInner_self, Complex.norm_real, Real.norm_of_nonneg (wNormSq_nonneg hnn _),
    ← wNorm_sq hnn] at h4
  rw [hop]
  have hz0 : 0 ≤ wNorm (idealWeight big J ℓ) (bigSym big J ℓ Y) := wNorm_nonneg _ _
  have hf0 : 0 ≤ wNorm (idealWeight big J ℓ) F := wNorm_nonneg _ _
  by_contra hcon
  have hlt : c * wNorm (idealWeight big J ℓ) F <
      wNorm (idealWeight big J ℓ) (bigSym big J ℓ Y) := not_le.mp hcon
  have hzpos : 0 < wNorm (idealWeight big J ℓ) (bigSym big J ℓ Y) :=
    lt_of_le_of_lt (mul_nonneg hc hf0) hlt
  nlinarith [mul_pos (sub_pos.mpr hlt) hzpos,
    mul_le_mul_of_nonneg_left hHs (mul_nonneg hc hz0)]

end Norm

/-! ### The two conclusions for one `x` -/

section Fixed

variable {P : GroupParams} {x : ℝ} {S B : Type} [Fintype S] [Fintype B] [DecidableEq B]

/-- (eq:ideal-small-norm) for one `x`, from the comparison estimate for this `x`. -/
theorem idealFamily_norm_le (𝔊 : PrimeGroups P x S B) {E : ℝ} (hE : 0 < E) {m J : ℕ}
    (hJ : m ≤ J) (hm : 6 * (E + 3) / P.c₀ ≤ Real.log ((m : ℝ) + 1))
    (hx : Real.exp (Real.exp (max 1 (3 / P.c₀))) ≤ x) {blk : B → Bool}
    (hbal : BalancedSplit blk) (Q h ξ ζ Θ : ℝ)
    (hdef : ∀ C : B → Finset (Fin J), IsComparison blk m C →
      ∀ (f : AuxList 𝔊.big (restrictBlock blk false C) → ℂ)
        (g : AuxList 𝔊.big (restrictBlock blk true C) → ℂ) (α : ℝ),
        ‖comparisonDefect 𝔊.big (restrictBlock blk true C) (restrictBlock blk false C) Q h ξ
            f g α ζ‖ ≤
          Real.log x ^ (-(E + (m : ℝ) * P.C₀ * Real.log 3 + 10)) *
            (tupleNorm 𝔊.big (restrictBlock blk false C) f *
              tupleNorm 𝔊.big (restrictBlock blk true C) g)) :
    idealOpNorm (comparisonFamily 𝔊.big J P.ℓ m blk Q h ξ) ζ Θ ≤ Real.log x ^ (-E) := by
  obtain ⟨hL2, hT1, hT3⟩ := log_facts hx
  have hL0 : 0 < Real.log x := by linarith
  have hL1 : (1 : ℝ) ≤ Real.log x := by linarith
  have hnn : ∀ p : LabelList 𝔊.big J P.ℓ, 0 ≤ idealWeight 𝔊.big J P.ℓ p := fun p =>
    (idealWeight_pos 𝔊.big_law_pos p).le
  have hε : 0 ≤ Real.log x ^ (-(E + (m : ℝ) * P.C₀ * Real.log 3 + 10)) :=
    Real.rpow_nonneg hL0.le _
  have hN := card_comparison_le_rpow 𝔊 hL0 blk J m
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hlog23 : Real.log 2 ≤ Real.log 3 := Real.log_le_log (by norm_num) (by norm_num)
  have hNε : (Fintype.card {C : B → Finset (Fin J) // IsComparison blk m C} : ℝ) *
      Real.log x ^ (-(E + (m : ℝ) * P.C₀ * Real.log 3 + 10)) ≤ Real.log x ^ (-(E + 3)) := by
    have h3 := mul_le_mul_of_nonneg_left hlog23 (mul_nonneg hm0 P.C₀_pos.le)
    calc (Fintype.card {C : B → Finset (Fin J) // IsComparison blk m C} : ℝ) *
          Real.log x ^ (-(E + (m : ℝ) * P.C₀ * Real.log 3 + 10))
        ≤ Real.log x ^ ((m : ℝ) * P.C₀ * Real.log 2) *
            Real.log x ^ (-(E + (m : ℝ) * P.C₀ * Real.log 3 + 10)) :=
          mul_le_mul_of_nonneg_right hN hε
      _ = Real.log x ^ ((m : ℝ) * P.C₀ * Real.log 2 +
            -(E + (m : ℝ) * P.C₀ * Real.log 3 + 10)) := (Real.rpow_add hL0 _ _).symm
      _ ≤ Real.log x ^ (-(E + 3)) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hfinal := final_numeric hL0 hT1 hE (delta_le 𝔊 hE hm hL0 hT3 hbal true)
    (delta_le 𝔊 hE hm hL0 hT3 hbal false) hNε (Real.sqrt_nonneg _)
  refine idealOpNorm_le_of_core 𝔊.big_law_pos blk Q h ξ ζ Θ _ (Real.rpow_nonneg hL0.le _)
    fun G H hG hH => ?_
  exact (core_bound 𝔊.big_law_sum hnn hJ P.ℓ_pos blk Q h ξ ζ Θ _ hε hdef G H hG hH).trans
    (mul_le_mul_of_nonneg_right hfinal (mul_nonneg (wNorm_nonneg _ _) (wNorm_nonneg _ _)))

/-- The pattern mass of the residual family for one `x` [S-03:0619–0627]. -/
theorem idealFamily_mass_le (𝔊 : PrimeGroups P x S B) (m J : ℕ)
    (hx : Real.exp (Real.exp (max 1 (3 / P.c₀))) ≤ x) (blk : B → Bool) {qs xs : ℝ}
    (hqs : 0 ≤ qs) (hxs : 0 ≤ xs) (h : ℝ) :
    patternMass (comparisonFamily 𝔊.big J P.ℓ m blk (Real.log x ^ qs) h
        (Real.log x ^ (-xs))) ≤
      Real.log x ^ ((m : ℝ) * P.C₀ * Real.log 2 + 4 * qs + 2 * xs + 1) := by
  obtain ⟨hL2, -, -⟩ := log_facts hx
  have hL0 : 0 < Real.log x := by linarith
  have hN := card_comparison_le_rpow 𝔊 hL0 blk J m
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hLpow : ∀ a : ℝ, Real.log x ^ a = Real.exp (Real.log (Real.log x) * a) := fun a =>
    Real.rpow_def_of_pos hL0 a
  have hκ : (Real.log x ^ qs) ^ 2 * (Real.log x ^ (-xs))⁻¹ = Real.log x ^ (2 * qs + xs) := by
    rw [hLpow qs, hLpow (-xs), hLpow (2 * qs + xs), ← Real.exp_nat_mul, ← Real.exp_neg,
      ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hmass := patternMass_comparisonFamily_le 𝔊.big J P.ℓ m blk (Real.log x ^ qs) h
    (Real.log x ^ (-xs)) (Real.rpow_nonneg hL0.le _) (Real.rpow_pos_of_pos hL0 _)
  rw [hκ] at hmass
  have e : Real.log x ^ ((m : ℝ) * P.C₀ * Real.log 2 + 4 * qs + 2 * xs) =
      Real.log x ^ ((m : ℝ) * P.C₀ * Real.log 2) *
        (Real.log x ^ (2 * qs + xs) * Real.log x ^ (2 * qs + xs)) := by
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
    congr 1
    ring
  have hmass2 : (Fintype.card {C : B → Finset (Fin J) // IsComparison blk m C} : ℝ) *
      (Real.log x ^ (2 * qs + xs) * Real.log x ^ (2 * qs + xs)) ≤
      Real.log x ^ ((m : ℝ) * P.C₀ * Real.log 2 + 4 * qs + 2 * xs) := by
    rw [e]
    exact mul_le_mul_of_nonneg_right hN
      (mul_nonneg (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hL0.le _))
  have ha : 0 ≤ (m : ℝ) * P.C₀ * Real.log 2 + 4 * qs + 2 * xs := by
    have h3 : 0 ≤ (m : ℝ) * P.C₀ * Real.log 2 := mul_nonneg (mul_nonneg hm0 P.C₀_pos.le) h2
    linarith
  have hone := one_add_rpow_le hL2 ha (le_refl _)
  linarith

/-- The number of patterns of the residual family for one `x` [S-03:0619–0620]. -/
theorem comparisonIndex_card_le (𝔊 : PrimeGroups P x S B) (m J : ℕ)
    (hx : Real.exp (Real.exp (max 1 (3 / P.c₀))) ≤ x) (blk : B → Bool) {qs xs : ℝ}
    (hqs : 0 ≤ qs) (hxs : 0 ≤ xs) :
    (Fintype.card (ComparisonIndex B blk J m) : ℝ) ≤
      Real.log x ^ ((m : ℝ) * P.C₀ * Real.log 2 + 4 * qs + 2 * xs + 1) := by
  obtain ⟨hL2, -, -⟩ := log_facts hx
  have hL0 : 0 < Real.log x := by linarith
  have hN := card_comparison_le_rpow 𝔊 hL0 blk J m
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have ha : 0 ≤ (m : ℝ) * P.C₀ * Real.log 2 := mul_nonneg (mul_nonneg hm0 P.C₀_pos.le) h2
  have hone := one_add_rpow_le (c := (m : ℝ) * P.C₀ * Real.log 2 + 4 * qs + 2 * xs + 1) hL2 ha
    (by linarith)
  have hcard : (Fintype.card (ComparisonIndex B blk J m) : ℝ) =
      (Fintype.card {C : B → Finset (Fin J) // IsComparison blk m C} : ℝ) + 1 := by
    rw [Fintype.card_option]
    push_cast
    rfl
  rw [hcard]
  linarith

end Fixed

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction

namespace SimultaneousPrimitiveRoots.Unconditional.Transference

open IdealConstruction

/-- **The part of the proof of [S] Theorem 4.1 after Lemma 4.3** [S-03:0441–0645]: with
`log (m + 1) ≥ 6 (E_id + 3)/c₀`, `J₀ = m`, `A₀' = E_id + m C₀ log 3 + 10` and
`C₁ = m C₀ log 2 + 4 q_* + 2 x_* + 1`, the comparison contract of precision `A₀'` implies the
conclusion of Theorem 4.1 for the residual family and the bound for the number of its
patterns. -/
theorem idealConstructionOfContract : IdealConstructionOfContract := by
  intro P Eid C₄ hEid hC₄
  obtain ⟨m, hm⟩ : ∃ m : ℕ, 6 * (Eid + 3) / P.c₀ ≤ Real.log ((m : ℝ) + 1) := by
    obtain ⟨m, hm⟩ := exists_nat_ge (Real.exp (6 * (Eid + 3) / P.c₀))
    refine ⟨m, ?_⟩
    have hpos : 0 < Real.exp (6 * (Eid + 3) / P.c₀) := Real.exp_pos _
    have h1 : Real.exp (6 * (Eid + 3) / P.c₀) ≤ (m : ℝ) + 1 := by linarith
    have h2 := Real.log_le_log hpos h1
    rwa [Real.log_exp] at h2
  refine ⟨m, m, Eid + (m : ℝ) * P.C₀ * Real.log 3 + 10, ?_, ?_⟩
  · have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    have h4 : 0 ≤ (m : ℝ) * P.C₀ * Real.log 3 :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg m) P.C₀_pos.le) h3
    linarith
  intro qs hs xs hqs _ hxs hcon
  obtain ⟨x₀, hx₀⟩ := hcon
  refine ⟨(m : ℝ) * P.C₀ * Real.log 2 + 4 * qs + 2 * xs + 1, fun J hJ => ⟨?_, ?_⟩⟩
  · refine ⟨max x₀ (Real.exp (Real.exp (max 1 (3 / P.c₀)))), ?_⟩
    intro x hx S B _ _ _ _ 𝔊 hint blk hbal
    have hx0 : x₀ ≤ x := le_trans (le_max_left _ _) hx
    have hx1 : Real.exp (Real.exp (max 1 (3 / P.c₀))) ≤ x := le_trans (le_max_right _ _) hx
    refine ⟨idealFamily_mass_le 𝔊 m J hx1 blk hqs hxs _, fun Θ ζ hζ => ?_⟩
    refine idealFamily_norm_le 𝔊 hEid hJ hm hx1 hbal _ _ _ ζ Θ fun C hC f g α => ?_
    have hA : ∃ g, (restrictBlock blk true C g).Nonempty := by
      obtain ⟨g, hg, hne⟩ := hC.2.1
      exact ⟨g, by rw [restrictBlock_of_eq C hg]; exact hne⟩
    have hB : ∃ g, (restrictBlock blk false C g).Nonempty := by
      obtain ⟨g, hg, hne⟩ := hC.2.2
      exact ⟨g, by rw [restrictBlock_of_eq C hg]; exact hne⟩
    have hcard : ∀ (b : Bool) (g : B), (restrictBlock blk b C g).card ≤ m := fun b g =>
      (Finset.card_le_card fun i hi => hC.1 g (mem_of_mem_restrictBlock hi)).trans
        (card_probeSlots_le J m)
    exact hx₀ x hx0 S B 𝔊 hint J (restrictBlock blk true C) (restrictBlock blk false C) hA hB
      (hcard true) (hcard false) f g α ζ hζ
  · refine ⟨Real.exp (Real.exp (max 1 (3 / P.c₀))), ?_⟩
    intro x hx S B _ _ _ _ 𝔊 blk
    exact comparisonIndex_card_le 𝔊 m J hx blk hqs hxs

end SimultaneousPrimitiveRoots.Unconditional.Transference
