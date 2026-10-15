module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction.Contract
public import SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction.Comparisons
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The expansion of the residual operator and the exact cancellation

Source: `verification/stage7-sources/S-03.tex`, lines 456–469 and 542–617.

For symmetric `G` (source) and `H` (target), with `G' = E_last G`, `H' = E_last H`, the raw phase
`M`, and `D₁ = ∏_{i ∈ ℐ₁} (1 - E_i)`, `D₂ = ∏_{i ∈ ℐ₂} (1 - E_i)`:

`⟨G, (raw + comparisons) H⟩ = ⟨D₁ G', M H'⟩ + ⟨G', M D₂ H'⟩ - ⟨D₁ G', M D₂ H'⟩ + (errors)`.

The first three terms are "all these exceptional raw component pairs"
`R(F_full, H') + R(F' - F_full, H_full)` of [S-03:0593–0599] (`D₁ G' = F_full`,
`D₂ H' = H_full`); each error is one application of the comparison estimate
(`norm_wInner_comp_le`). The cancellation (eq:ideal-inclusion-exclusion) is the identity
`∑_{∅ ≠ A ⊆ ℐ₁} (-1)^{|A|} E_A = D₁ - 1` (`AvgSystem.D_sub_apply`), used on both sides.

* `core_bound` — the resulting bound
  `|⟨G, (raw + comparisons) H⟩| ≤ (δ₁ + δ₂ + δ₁ δ₂ + #comparisons · ε) ‖G‖ ‖H‖`,
  `δ_i = (m + 1)^{-s_i/2}`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction

open scoped BigOperators ComplexConjugate

noncomputable section

section General

variable {X : Type*} [Fintype X]

theorem wInner_const_mul_right (w : X → ℝ) (c : ℂ) (F G : X → ℂ) :
    wInner w F (fun x => c * G x) = c * wInner w F G := by
  show ∑ x, (w x : ℂ) * (conj (F x) * (c * G x)) = c * ∑ x, (w x : ℂ) * (conj (F x) * G x)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem wNorm_le_of_wNormSq_le {w : X → ℝ} {F G : X → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (h : wNormSq w F ≤ c * wNormSq w G) : wNorm w F ≤ Real.sqrt c * wNorm w G := by
  unfold wNorm
  rw [← Real.sqrt_mul hc]
  exact Real.sqrt_le_sqrt h

/-- The pairing of two finite combinations, the second one multiplied by a function. -/
theorem wInner_sum_mul_sum {ι κ : Type*} (w : X → ℝ) (s : Finset ι) (t : Finset κ)
    (a : ι → ℂ) (b : κ → ℂ) (F : ι → X → ℂ) (K : κ → X → ℂ) (φ : X → ℂ)
    (ha : ∀ i, conj (a i) = a i) :
    wInner w (fun x => ∑ i ∈ s, a i * F i x) (fun x => φ x * ∑ j ∈ t, b j * K j x) =
      ∑ i ∈ s, ∑ j ∈ t, a i * (b j * wInner w (F i) (fun x => φ x * K j x)) := by
  have hL : ∀ x, (w x : ℂ) * (conj (∑ i ∈ s, a i * F i x) * (φ x * ∑ j ∈ t, b j * K j x)) =
      ∑ i ∈ s, ∑ j ∈ t, a i * (b j * ((w x : ℂ) * (conj (F i x) * (φ x * K j x)))) := by
    intro x
    rw [map_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, ha i]
    ring
  show ∑ x, (w x : ℂ) * (conj (∑ i ∈ s, a i * F i x) * (φ x * ∑ j ∈ t, b j * K j x)) =
    ∑ i ∈ s, ∑ j ∈ t, a i * (b j * ∑ x, (w x : ℂ) * (conj (F i x) * (φ x * K j x)))
  rw [Finset.sum_congr rfl fun x _ => hL x, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]

/-- **The inclusion–exclusion identity** (eq:ideal-inclusion-exclusion) [S-03:0582–0590]:
`(∏_{k ∈ U} (1 - E_k) - 1) F = ∑_{∅ ≠ T ⊆ U} (-1)^{|T|} E_T F`. -/
theorem AvgSystem.D_sub_apply {K : Type*} [DecidableEq K] {w : X → ℝ} (S : AvgSystem K w)
    (U : Finset K) (F : X → ℂ) (x : X) :
    S.D U F x - F x = ∑ T ∈ U.powerset.erase ∅, (-1 : ℂ) ^ T.card * S.E T F x := by
  have h := Finset.add_sum_erase U.powerset (fun T => (-1 : ℂ) ^ T.card * S.E T F x)
    (Finset.empty_mem_powerset U)
  have h0 : (-1 : ℂ) ^ (∅ : Finset K).card * S.E ∅ F x = F x := by
    rw [Finset.card_empty, pow_zero, one_mul, S.E_empty]
    rfl
  rw [S.D_apply, ← h, h0]
  ring

end General

section Core

variable {B : Type} [Fintype B] [DecidableEq B] {big : B → Finset ℕ} {J ℓ : ℕ}

/-- **One comparison term**: the pairing of the row operation of the comparison freeing
`C = A ∪ B` is `-(-1)^{|C|}` times the raw pairing of `E_A G'` and `E_B H'`, up to the difference
estimated by the comparison lemma. -/
theorem wInner_comparison_row (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (blk : B → Bool) (Q h ξ : ℝ) (C : B → Finset (Fin J)) (ζ Θ : ℝ)
    (G H : LabelList big J ℓ → ℂ) :
    wInner (idealWeight big J ℓ) G (idealRow (comparisonPattern big J ℓ blk Q h ξ C) ζ Θ H) =
      -((-1 : ℂ) ^ (∑ g, (C g).card)) *
        (wInner (idealWeight big J ℓ)
            (avg big J ℓ (slotSet ℓ (restrictBlock blk true C)) (avg big J ℓ (lastSet B J ℓ) G))
            (rawMul big J ℓ ζ Θ (avg big J ℓ (slotSet ℓ (restrictBlock blk false C))
              (avg big J ℓ (lastSet B J ℓ) H))) -
          wInner (idealWeight big J ℓ)
            (avg big J ℓ (slotSet ℓ (restrictBlock blk true C)) (avg big J ℓ (lastSet B J ℓ) G))
            (fun p => avg big J ℓ (slotSet ℓ (restrictBlock blk true C))
                (rawMul big J ℓ ζ Θ (avg big J ℓ (slotSet ℓ (restrictBlock blk false C))
                  (avg big J ℓ (lastSet B J ℓ) H))) p -
              compOp big J ℓ blk Q h ξ C ζ Θ (avg big J ℓ (slotSet ℓ (restrictBlock blk false C))
                (avg big J ℓ (lastSet B J ℓ) H)) p)) := by
  have hrow : idealRow (comparisonPattern big J ℓ blk Q h ξ C) ζ Θ H = fun p =>
      -((-1 : ℂ) ^ (∑ g, (C g).card)) * compOp big J ℓ blk Q h ξ C ζ Θ
        (avg big J ℓ (slotSet ℓ (restrictBlock blk false C) ∪ lastSet B J ℓ) H) p :=
    funext fun p => idealRow_comparison_eq hlaw blk Q h ξ C ζ Θ H p
  have hH₁ : avg big J ℓ (slotSet ℓ (restrictBlock blk false C) ∪ lastSet B J ℓ) H =
      avg big J ℓ (slotSet ℓ (restrictBlock blk false C)) (avg big J ℓ (lastSet B J ℓ) H) :=
    (LinearMap.congr_fun (avg_mul hlaw (slotSet ℓ (restrictBlock blk false C))
      (lastSet B J ℓ)) H).symm
  have hG₁ : avg big J ℓ (slotSet ℓ (restrictBlock blk true C) ∪ lastSet B J ℓ) G =
      avg big J ℓ (slotSet ℓ (restrictBlock blk true C)) (avg big J ℓ (lastSet B J ℓ) G) :=
    (LinearMap.congr_fun (avg_mul hlaw (slotSet ℓ (restrictBlock blk true C))
      (lastSet B J ℓ)) G).symm
  obtain ⟨H₁, hH₁def⟩ : ∃ H₁ : LabelList big J ℓ → ℂ, H₁ =
      avg big J ℓ (slotSet ℓ (restrictBlock blk false C)) (avg big J ℓ (lastSet B J ℓ) H) :=
    ⟨_, rfl⟩
  obtain ⟨G₁, hG₁def⟩ : ∃ G₁ : LabelList big J ℓ → ℂ, G₁ =
      avg big J ℓ (slotSet ℓ (restrictBlock blk true C)) (avg big J ℓ (lastSet B J ℓ) G) :=
    ⟨_, rfl⟩
  have hlast : Indep (lastSet B J ℓ) H₁ := by
    rw [hH₁def]
    exact indep_avg_of_indep (indep_avg (lastSet B J ℓ) H)
  have hind : Indep (slotSet ℓ (restrictBlock blk true C) ∪ lastSet B J ℓ)
      (compOp big J ℓ blk Q h ξ C ζ Θ H₁) :=
    (indep_compOp_left blk Q h ξ C ζ Θ H₁).union (indep_compOp_last blk Q h ξ C ζ Θ hlast)
  have h1 : wInner (idealWeight big J ℓ) G (compOp big J ℓ blk Q h ξ C ζ Θ H₁) =
      wInner (idealWeight big J ℓ)
        (avg big J ℓ (slotSet ℓ (restrictBlock blk true C) ∪ lastSet B J ℓ) G)
        (compOp big J ℓ blk Q h ξ C ζ Θ H₁) := wInner_avg_left_of_indep hlaw G hind
  have h2 : wInner (idealWeight big J ℓ) G₁
        (avg big J ℓ (slotSet ℓ (restrictBlock blk true C)) (rawMul big J ℓ ζ Θ H₁)) =
      wInner (idealWeight big J ℓ) G₁ (rawMul big J ℓ ζ Θ H₁) := by
    have e := avg_sa (big := big) (slotSet ℓ (restrictBlock blk true C)) G₁
      (rawMul big J ℓ ζ Θ H₁)
    have e' : avg big J ℓ (slotSet ℓ (restrictBlock blk true C)) G₁ = G₁ := by
      rw [hG₁def]
      exact avg_of_indep hlaw (indep_avg _ _)
    rw [e'] at e
    exact e
  have h3 : wInner (idealWeight big J ℓ) G₁ (compOp big J ℓ blk Q h ξ C ζ Θ H₁) =
      wInner (idealWeight big J ℓ) G₁
          (avg big J ℓ (slotSet ℓ (restrictBlock blk true C)) (rawMul big J ℓ ζ Θ H₁)) -
        wInner (idealWeight big J ℓ) G₁
          (fun p => avg big J ℓ (slotSet ℓ (restrictBlock blk true C))
              (rawMul big J ℓ ζ Θ H₁) p - compOp big J ℓ blk Q h ξ C ζ Θ H₁ p) := by
    have e : (fun p => avg big J ℓ (slotSet ℓ (restrictBlock blk true C))
          (rawMul big J ℓ ζ Θ H₁) p - compOp big J ℓ blk Q h ξ C ζ Θ H₁ p) =
        avg big J ℓ (slotSet ℓ (restrictBlock blk true C)) (rawMul big J ℓ ζ Θ H₁) -
          compOp big J ℓ blk Q h ξ C ζ Θ H₁ := rfl
    rw [e, wInner_sub_right]
    ring
  rw [← hH₁def, ← hG₁def, hrow, hH₁, ← hH₁def, wInner_const_mul_right]
  congr 1
  rw [h1, hG₁, ← hG₁def, h3, h2]

/-- **The residual pairing** [S-03:0456–0617]: for symmetric `G`, `H`, if every comparison
defect is at most `ε ‖f‖₂ ‖g‖₂`, then
`|⟨G, (raw + comparisons) H⟩| ≤ (δ₁ + δ₂ + δ₁ δ₂ + #comparisons · ε) ‖G‖ ‖H‖`, where
`δ_i = (m + 1)^{-s_i/2}` and `s_i` is the number of big groups of the block `i`. -/
theorem core_bound (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (hnn : ∀ p : LabelList big J ℓ, 0 ≤ idealWeight big J ℓ p) {m : ℕ} (hJ : m ≤ J)
    (hℓ : 0 < ℓ) (blk : B → Bool) (Q h ξ ζ Θ ε : ℝ) (hε : 0 ≤ ε)
    (hdef : ∀ C : B → Finset (Fin J), IsComparison blk m C →
      ∀ (f : AuxList big (restrictBlock blk false C) → ℂ)
        (g : AuxList big (restrictBlock blk true C) → ℂ) (α : ℝ),
        ‖comparisonDefect big (restrictBlock blk true C) (restrictBlock blk false C) Q h ξ f g
            α ζ‖ ≤
          ε * (tupleNorm big (restrictBlock blk false C) f *
            tupleNorm big (restrictBlock blk true C) g))
    (G H : LabelList big J ℓ → ℂ) (hG : IsSym G) (hH : IsSym H) :
    ‖wInner (idealWeight big J ℓ) G
        ((∑ ν, idealRow (comparisonFamily big J ℓ m blk Q h ξ ν) ζ Θ) H)‖ ≤
      (Real.sqrt ((1 / ((m : ℝ) + 1)) ^ (blockSet blk true).card) +
        Real.sqrt ((1 / ((m : ℝ) + 1)) ^ (blockSet blk false).card) +
        Real.sqrt ((1 / ((m : ℝ) + 1)) ^ (blockSet blk true).card) *
          Real.sqrt ((1 / ((m : ℝ) + 1)) ^ (blockSet blk false).card) +
        (Fintype.card {C : B → Finset (Fin J) // IsComparison blk m C} : ℝ) * ε) *
      (wNorm (idealWeight big J ℓ) G * wNorm (idealWeight big J ℓ) H) := by
  have hθ0 : (0 : ℝ) ≤ 1 / ((m : ℝ) + 1) := by
    have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    exact div_nonneg zero_le_one (by linarith)
  obtain ⟨G', hG'⟩ : ∃ G' : LabelList big J ℓ → ℂ, G' = avg big J ℓ (lastSet B J ℓ) G :=
    ⟨_, rfl⟩
  obtain ⟨H', hH'⟩ : ∃ H' : LabelList big J ℓ → ℂ, H' = avg big J ℓ (lastSet B J ℓ) H :=
    ⟨_, rfl⟩
  have hGn : wNorm (idealWeight big J ℓ) G' ≤ wNorm (idealWeight big J ℓ) G := by
    rw [hG']
    exact (labelAvg hlaw).wNorm_E_le hnn _ G
  have hHn : wNorm (idealWeight big J ℓ) H' ≤ wNorm (idealWeight big J ℓ) H := by
    rw [hH']
    exact (labelAvg hlaw).wNorm_E_le hnn _ H
  have hD₁ : wNorm (idealWeight big J ℓ)
        ((labelAvg hlaw).D (probeSet J ℓ m (blockSet blk true)) G') ≤
      Real.sqrt ((1 / ((m : ℝ) + 1)) ^ (blockSet blk true).card) *
        wNorm (idealWeight big J ℓ) G := by
    rw [hG']
    exact wNorm_le_of_wNormSq_le (pow_nonneg hθ0 _)
      (probe_bound hlaw hnn hJ hℓ G hG (blockSet blk true))
  have hD₂ : wNorm (idealWeight big J ℓ)
        ((labelAvg hlaw).D (probeSet J ℓ m (blockSet blk false)) H') ≤
      Real.sqrt ((1 / ((m : ℝ) + 1)) ^ (blockSet blk false).card) *
        wNorm (idealWeight big J ℓ) H := by
    rw [hH']
    exact wNorm_le_of_wNormSq_le (pow_nonneg hθ0 _)
      (probe_bound hlaw hnn hJ hℓ H hH (blockSet blk false))
  -- the sum over the patterns
  have hsum : wInner (idealWeight big J ℓ) G
        ((∑ ν, idealRow (comparisonFamily big J ℓ m blk Q h ξ ν) ζ Θ) H) =
      wInner (idealWeight big J ℓ) G (idealRow (Pattern.raw big J ℓ) ζ Θ H) +
        ∑ C : {C : B → Finset (Fin J) // IsComparison blk m C},
          wInner (idealWeight big J ℓ) G
            (idealRow (comparisonPattern big J ℓ blk Q h ξ C.1) ζ Θ H) := by
    rw [LinearMap.sum_apply, wInner_sum_right, Fintype.sum_option]
    rfl
  have hraw : wInner (idealWeight big J ℓ) G (idealRow (Pattern.raw big J ℓ) ζ Θ H) =
      wInner (idealWeight big J ℓ) G' (rawMul big J ℓ ζ Θ H') := by
    rw [idealRow_raw_eq hlaw ζ Θ H, hG', hH']
    exact wInner_avg_left_of_indep hlaw G (indep_rawMul_last ζ Θ (indep_avg _ H))
  have hcomp : ∀ C : {C : B → Finset (Fin J) // IsComparison blk m C},
      wInner (idealWeight big J ℓ) G
          (idealRow (comparisonPattern big J ℓ blk Q h ξ C.1) ζ Θ H) =
        -((-1 : ℂ) ^ (∑ g, (C.1 g).card) *
            wInner (idealWeight big J ℓ)
              (avg big J ℓ (slotSet ℓ (restrictBlock blk true C.1)) G')
              (rawMul big J ℓ ζ Θ (avg big J ℓ (slotSet ℓ (restrictBlock blk false C.1)) H'))) +
          (-1 : ℂ) ^ (∑ g, (C.1 g).card) *
            wInner (idealWeight big J ℓ)
              (avg big J ℓ (slotSet ℓ (restrictBlock blk true C.1)) G')
              (fun p => avg big J ℓ (slotSet ℓ (restrictBlock blk true C.1))
                  (rawMul big J ℓ ζ Θ
                    (avg big J ℓ (slotSet ℓ (restrictBlock blk false C.1)) H')) p -
                compOp big J ℓ blk Q h ξ C.1 ζ Θ
                  (avg big J ℓ (slotSet ℓ (restrictBlock blk false C.1)) H') p) := by
    intro C
    rw [wInner_comparison_row hlaw blk Q h ξ C.1 ζ Θ G H, hG', hH']
    ring
  have hC : ∑ C : {C : B → Finset (Fin J) // IsComparison blk m C},
        wInner (idealWeight big J ℓ) G
          (idealRow (comparisonPattern big J ℓ blk Q h ξ C.1) ζ Θ H) =
      -(∑ C : {C : B → Finset (Fin J) // IsComparison blk m C},
          (-1 : ℂ) ^ (∑ g, (C.1 g).card) *
            wInner (idealWeight big J ℓ)
              (avg big J ℓ (slotSet ℓ (restrictBlock blk true C.1)) G')
              (rawMul big J ℓ ζ Θ
                (avg big J ℓ (slotSet ℓ (restrictBlock blk false C.1)) H'))) +
        ∑ C : {C : B → Finset (Fin J) // IsComparison blk m C},
          (-1 : ℂ) ^ (∑ g, (C.1 g).card) *
            wInner (idealWeight big J ℓ)
              (avg big J ℓ (slotSet ℓ (restrictBlock blk true C.1)) G')
              (fun p => avg big J ℓ (slotSet ℓ (restrictBlock blk true C.1))
                  (rawMul big J ℓ ζ Θ
                    (avg big J ℓ (slotSet ℓ (restrictBlock blk false C.1)) H')) p -
                compOp big J ℓ blk Q h ξ C.1 ζ Θ
                  (avg big J ℓ (slotSet ℓ (restrictBlock blk false C.1)) H') p) := by
    rw [Finset.sum_congr rfl fun C _ => hcomp C, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  -- the exact cancellation
  have hmain : ∑ C : {C : B → Finset (Fin J) // IsComparison blk m C},
        (-1 : ℂ) ^ (∑ g, (C.1 g).card) *
          wInner (idealWeight big J ℓ)
            (avg big J ℓ (slotSet ℓ (restrictBlock blk true C.1)) G')
            (rawMul big J ℓ ζ Θ (avg big J ℓ (slotSet ℓ (restrictBlock blk false C.1)) H')) =
      wInner (idealWeight big J ℓ)
        ((labelAvg hlaw).D (probeSet J ℓ m (blockSet blk true)) G' - G')
        (rawMul big J ℓ ζ Θ
          ((labelAvg hlaw).D (probeSet J ℓ m (blockSet blk false)) H' - H')) := by
    have hA : (labelAvg hlaw).D (probeSet J ℓ m (blockSet blk true)) G' - G' = fun x =>
        ∑ A ∈ (probeSet J ℓ m (blockSet blk true)).powerset.erase ∅,
          (-1 : ℂ) ^ A.card * avg big J ℓ A G' x :=
      funext fun x => (labelAvg hlaw).D_sub_apply (probeSet J ℓ m (blockSet blk true)) G' x
    have hB : rawMul big J ℓ ζ Θ
          ((labelAvg hlaw).D (probeSet J ℓ m (blockSet blk false)) H' - H') = fun x =>
        dilPhase ζ Θ (fullProd x) *
          ∑ Bc ∈ (probeSet J ℓ m (blockSet blk false)).powerset.erase ∅,
            (-1 : ℂ) ^ Bc.card * avg big J ℓ Bc H' x :=
      funext fun x => congrArg (fun z : ℂ => dilPhase ζ Θ (fullProd x) * z)
        ((labelAvg hlaw).D_sub_apply (probeSet J ℓ m (blockSet blk false)) H' x)
    have hpair := wInner_sum_mul_sum (idealWeight big J ℓ)
      ((probeSet J ℓ m (blockSet blk true)).powerset.erase ∅)
      ((probeSet J ℓ m (blockSet blk false)).powerset.erase ∅)
      (fun A => (-1 : ℂ) ^ A.card) (fun Bc => (-1 : ℂ) ^ Bc.card)
      (fun A => avg big J ℓ A G') (fun Bc => avg big J ℓ Bc H')
      (fun x => dilPhase ζ Θ (fullProd x))
      (fun A => by rw [map_pow, map_neg, map_one])
    rw [sum_comparison_eq (ℓ := ℓ) blk m (fun A Bc => wInner (idealWeight big J ℓ)
      (avg big J ℓ A G') (rawMul big J ℓ ζ Θ (avg big J ℓ Bc H'))), hA, hB]
    exact hpair.symm
  have e1 : rawMul big J ℓ ζ Θ
        ((labelAvg hlaw).D (probeSet J ℓ m (blockSet blk false)) H' - H') =
      rawMul big J ℓ ζ Θ ((labelAvg hlaw).D (probeSet J ℓ m (blockSet blk false)) H') -
        rawMul big J ℓ ζ Θ H' := by
    funext x
    show dilPhase ζ Θ (fullProd x) *
        ((labelAvg hlaw).D (probeSet J ℓ m (blockSet blk false)) H' x - H' x) =
      dilPhase ζ Θ (fullProd x) * (labelAvg hlaw).D (probeSet J ℓ m (blockSet blk false)) H' x -
        dilPhase ζ Θ (fullProd x) * H' x
    ring
  have htotal : wInner (idealWeight big J ℓ) G
        ((∑ ν, idealRow (comparisonFamily big J ℓ m blk Q h ξ ν) ζ Θ) H) =
      wInner (idealWeight big J ℓ)
          ((labelAvg hlaw).D (probeSet J ℓ m (blockSet blk true)) G') (rawMul big J ℓ ζ Θ H') +
        wInner (idealWeight big J ℓ) G'
          (rawMul big J ℓ ζ Θ ((labelAvg hlaw).D (probeSet J ℓ m (blockSet blk false)) H')) -
        wInner (idealWeight big J ℓ)
          ((labelAvg hlaw).D (probeSet J ℓ m (blockSet blk true)) G')
          (rawMul big J ℓ ζ Θ ((labelAvg hlaw).D (probeSet J ℓ m (blockSet blk false)) H')) +
        ∑ C : {C : B → Finset (Fin J) // IsComparison blk m C},
          (-1 : ℂ) ^ (∑ g, (C.1 g).card) *
            wInner (idealWeight big J ℓ)
              (avg big J ℓ (slotSet ℓ (restrictBlock blk true C.1)) G')
              (fun p => avg big J ℓ (slotSet ℓ (restrictBlock blk true C.1))
                  (rawMul big J ℓ ζ Θ
                    (avg big J ℓ (slotSet ℓ (restrictBlock blk false C.1)) H')) p -
                compOp big J ℓ blk Q h ξ C.1 ζ Θ
                  (avg big J ℓ (slotSet ℓ (restrictBlock blk false C.1)) H') p) := by
    rw [hsum, hraw, hC, hmain, e1, wInner_sub_left, wInner_sub_right, wInner_sub_right]
    ring
  -- the bounds
  have b1 : ‖wInner (idealWeight big J ℓ)
        ((labelAvg hlaw).D (probeSet J ℓ m (blockSet blk true)) G')
        (rawMul big J ℓ ζ Θ H')‖ ≤
      Real.sqrt ((1 / ((m : ℝ) + 1)) ^ (blockSet blk true).card) *
        wNorm (idealWeight big J ℓ) G * wNorm (idealWeight big J ℓ) H :=
    (norm_wInner_le hnn _ _).trans
      (mul_le_mul hD₁ ((wNorm_rawMul_le hnn ζ Θ H').trans hHn) (wNorm_nonneg _ _)
        (mul_nonneg (Real.sqrt_nonneg _) (wNorm_nonneg _ _)))
  have b2 : ‖wInner (idealWeight big J ℓ) G'
        (rawMul big J ℓ ζ Θ
          ((labelAvg hlaw).D (probeSet J ℓ m (blockSet blk false)) H'))‖ ≤
      wNorm (idealWeight big J ℓ) G *
        (Real.sqrt ((1 / ((m : ℝ) + 1)) ^ (blockSet blk false).card) *
          wNorm (idealWeight big J ℓ) H) :=
    (norm_wInner_le hnn _ _).trans
      (mul_le_mul hGn ((wNorm_rawMul_le hnn ζ Θ _).trans hD₂) (wNorm_nonneg _ _)
        (wNorm_nonneg _ _))
  have b3 : ‖wInner (idealWeight big J ℓ)
        ((labelAvg hlaw).D (probeSet J ℓ m (blockSet blk true)) G')
        (rawMul big J ℓ ζ Θ
          ((labelAvg hlaw).D (probeSet J ℓ m (blockSet blk false)) H'))‖ ≤
      Real.sqrt ((1 / ((m : ℝ) + 1)) ^ (blockSet blk true).card) *
          wNorm (idealWeight big J ℓ) G *
        (Real.sqrt ((1 / ((m : ℝ) + 1)) ^ (blockSet blk false).card) *
          wNorm (idealWeight big J ℓ) H) :=
    (norm_wInner_le hnn _ _).trans
      (mul_le_mul hD₁ ((wNorm_rawMul_le hnn ζ Θ _).trans hD₂) (wNorm_nonneg _ _)
        (mul_nonneg (Real.sqrt_nonneg _) (wNorm_nonneg _ _)))
  have b4 : ‖∑ C : {C : B → Finset (Fin J) // IsComparison blk m C},
        (-1 : ℂ) ^ (∑ g, (C.1 g).card) *
          wInner (idealWeight big J ℓ)
            (avg big J ℓ (slotSet ℓ (restrictBlock blk true C.1)) G')
            (fun p => avg big J ℓ (slotSet ℓ (restrictBlock blk true C.1))
                (rawMul big J ℓ ζ Θ
                  (avg big J ℓ (slotSet ℓ (restrictBlock blk false C.1)) H')) p -
              compOp big J ℓ blk Q h ξ C.1 ζ Θ
                (avg big J ℓ (slotSet ℓ (restrictBlock blk false C.1)) H') p)‖ ≤
      (Fintype.card {C : B → Finset (Fin J) // IsComparison blk m C} : ℝ) *
        (ε * (wNorm (idealWeight big J ℓ) G * wNorm (idealWeight big J ℓ) H)) := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ C : {C : B → Finset (Fin J) // IsComparison blk m C},
        ‖(-1 : ℂ) ^ (∑ g, (C.1 g).card) *
          wInner (idealWeight big J ℓ)
            (avg big J ℓ (slotSet ℓ (restrictBlock blk true C.1)) G')
            (fun p => avg big J ℓ (slotSet ℓ (restrictBlock blk true C.1))
                (rawMul big J ℓ ζ Θ
                  (avg big J ℓ (slotSet ℓ (restrictBlock blk false C.1)) H')) p -
              compOp big J ℓ blk Q h ξ C.1 ζ Θ
                (avg big J ℓ (slotSet ℓ (restrictBlock blk false C.1)) H') p)‖ ≤
          ε * (wNorm (idealWeight big J ℓ) G * wNorm (idealWeight big J ℓ) H) := by
      intro C
      rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      refine (norm_wInner_comp_le hlaw hnn blk Q h ξ C.1 ζ Θ ε hε (hdef C.1 C.2) _ _
        (indep_avg _ H')).trans ?_
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (((labelAvg hlaw).wNorm_E_le hnn _ G').trans hGn)
          (((labelAvg hlaw).wNorm_E_le hnn _ H').trans hHn) (wNorm_nonneg _ _)
          (wNorm_nonneg _ _)) hε
    calc ∑ C : {C : B → Finset (Fin J) // IsComparison blk m C},
          ‖(-1 : ℂ) ^ (∑ g, (C.1 g).card) *
            wInner (idealWeight big J ℓ)
              (avg big J ℓ (slotSet ℓ (restrictBlock blk true C.1)) G')
              (fun p => avg big J ℓ (slotSet ℓ (restrictBlock blk true C.1))
                  (rawMul big J ℓ ζ Θ
                    (avg big J ℓ (slotSet ℓ (restrictBlock blk false C.1)) H')) p -
                compOp big J ℓ blk Q h ξ C.1 ζ Θ
                  (avg big J ℓ (slotSet ℓ (restrictBlock blk false C.1)) H') p)‖
        ≤ ∑ _C : {C : B → Finset (Fin J) // IsComparison blk m C},
            ε * (wNorm (idealWeight big J ℓ) G * wNorm (idealWeight big J ℓ) H) :=
          Finset.sum_le_sum fun C _ => hterm C
      _ = (Fintype.card {C : B → Finset (Fin J) // IsComparison blk m C} : ℝ) *
            (ε * (wNorm (idealWeight big J ℓ) G * wNorm (idealWeight big J ℓ) H)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [htotal]
  refine ((norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
    (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)).trans ?_
  refine (add_le_add (add_le_add (add_le_add b1 b2) b3) b4).trans (le_of_eq ?_)
  ring

end Core

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction
