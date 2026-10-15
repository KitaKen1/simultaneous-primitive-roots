module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.HighRank.Pins
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.EdgeAbsRow
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Large rank: the weighted row bound of an absolute edge with prescribed fresh births

Source: `verification/stage7-sources/S-02.tex`, lines 1122–1129 (`[S-02:1122–1129]`).

"At an edge choose stores, promotions, and the step first, and then fill fresh target slots in
canonical order. The step, promotion count, and memory weight do not depend on these new prime
values; the coefficient is bounded by its supremum and exclusions may be discarded. In the proof of
Lemma 3.8, replace the total fresh mass in each constrained slot by its single-point bound."

* `hrIndE pv b` — the indicator that the fresh births `b` of an edge realize the prescribed values
  `pv`: every target slot with a prescribed value is a fresh birth with that value.
* `hr_freshIntegral_le` — the fresh integral (`edgeAbsFreshIntegral`) of this indicator is at most
  the product of the point masses of the prescribed values times `∏_g max(1, M_max)^T`. Compared
  with `edgeAbsFreshIntegral_pinned_le` the point masses are exact (`hrPtMass`), not replaced by
  their supremum: the sum over the common value of a block is taken afterwards (`Blocks.lean`).
* `hr_edge_row_pinned` — the row bound of the absolute edge operation with this indicator
  inserted: the constant of `edgeAbs_rowBound` times the product of the point masses. It is
  `edgeAbs_row_full` (Lemma 3.8 with a weight of the fresh births) for the weight `hrIndE pv`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

section HrEdgeInd

variable {B : Type} {J ℓ : ℕ}

open _root_.Classical in
/-- **The fresh births of an edge realize the prescribed values**: every target slot with a
prescribed value is a fresh birth with that value (an indicator, as a real number). -/
def hrIndE (pv b : (g : B) → Slot J ℓ → Option ℕ) : ℝ :=
  if ∀ g sl z, pv g sl = some z → b g sl = some z then 1 else 0

theorem hrIndE_nonneg (pv b : (g : B) → Slot J ℓ → Option ℕ) : 0 ≤ hrIndE pv b := by
  unfold hrIndE
  split_ifs
  · exact zero_le_one
  · exact le_rfl

theorem hrIndE_of {pv b : (g : B) → Slot J ℓ → Option ℕ}
    (h : ∀ g sl z, pv g sl = some z → b g sl = some z) : hrIndE pv b = 1 := by
  unfold hrIndE
  exact if_pos h

end HrEdgeInd

section HrFresh

variable {S B : Type} [Fintype B] [DecidableEq B] {J ℓ : ℕ}

open _root_.Classical in
/-- **The fresh integral with prescribed values** [S-02:1127–1129]: "replace the total fresh mass
in each constrained slot by its single-point bound". For a family `F` of sets of unshared target
slots, the fresh integral of the indicator `hrIndE pv` is at most the product of the point masses
`μ̃_g(z)` of the prescribed values times `∏_{g ∈ ℬ} max(1, M_max)^T`, where
`μ̃_g(𝒫_g) ≤ M_max`. -/
theorem hr_freshIntegral_le (𝒢 : GroupFamily S B) {q : ℝ} {n : ℕ} {Mmax : ℝ}
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p)
    (hM : ∀ g, ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) q n p ≤ Mmax)
    (C : B → Finset (Fin J)) {T : ℕ} (hC : ∀ g, ℓ + (C g).card ≤ T)
    (F : (g : B) → Finset (Slot J ℓ)) (x₀ : LabelList 𝒢.big J ℓ)
    (hF : ∀ g, ∀ sl ∈ F g, Unshared (C g) sl) (pv : (g : B) → Slot J ℓ → Option ℕ) :
    edgeAbsFreshIntegral 𝒢 q n F x₀ (hrIndE pv) ≤
      (∏ g, ∏ sl, hrW (hrPtMass 𝒢 q n g) (pv g sl)) * ∏ _g : B, (max 1 Mmax) ^ T := by
  have hM1 : (1 : ℝ) ≤ max 1 Mmax := le_max_left _ _
  have hM0 : (0 : ℝ) ≤ max 1 Mmax := zero_le_one.trans hM1
  have hW0 : 0 ≤ ∏ g, ∏ sl, hrW (hrPtMass 𝒢 q n g) (pv g sl) :=
    Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun sl _ =>
      hrW_nonneg (hrPtMass_nonneg (hν g)) _
  have hlist := hr_sum_labelList_le 𝒢 hν (fun g => (hM g).trans (le_max_right _ _)) hM1 F x₀ pv
  have hcard : ∀ g, (F g).card ≤ T := by
    intro g
    have h1 : F g ⊆ Finset.univ.filter fun sl : Slot J ℓ => Unshared (C g) sl := fun sl hsl =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ sl, hF g sl hsl⟩
    have h2 : (Finset.univ.filter fun sl : Slot J ℓ => Unshared (C g) sl).card =
        ℓ + (C g).card := l38_card_unshared (C g)
    exact (Finset.card_le_card h1).trans (h2.le.trans (hC g))
  have hpow : ∏ g, (max 1 Mmax) ^ (F g).card ≤ ∏ _g : B, (max 1 Mmax) ^ T :=
    Finset.prod_le_prod (fun g _ => pow_nonneg hM0 _)
      (fun g _ => pow_le_pow_right₀ hM1 (hcard g))
  unfold edgeAbsFreshIntegral
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
    (hlist.trans (mul_le_mul_of_nonneg_left hpow hW0))
  -- one term: the indicator of the births is the condition on the list
  have hiff : (∀ g sl z, pv g sl = some z →
        (if sl ∈ F g then some (x g sl : ℕ) else none) = some z) ↔
      (∀ g sl z, pv g sl = some z → sl ∈ F g ∧ (x g sl : ℕ) = z) := by
    refine forall_congr' fun g => forall_congr' fun sl => forall_congr' fun z =>
      imp_congr_right fun _ => ?_
    by_cases hsl : sl ∈ F g
    · rw [if_pos hsl]
      exact ⟨fun h => ⟨hsl, Option.some.inj h⟩, fun h => congrArg some h.2⟩
    · rw [if_neg hsl]
      exact ⟨fun h => absurd h (Option.some_ne_none z).symm, fun h => absurd h.1 hsl⟩
  by_cases hA : ∀ g sl, sl ∉ F g → x g sl = x₀ g sl
  · rw [if_pos hA]
    by_cases hB : ∀ g sl z, pv g sl = some z → sl ∈ F g ∧ (x g sl : ℕ) = z
    · rw [hrIndE_of (hiff.mpr hB), mul_one, if_pos (And.intro hA hB)]
    · have hz : hrIndE pv (fun g sl => if sl ∈ F g then some (x g sl : ℕ) else none) = 0 := by
        unfold hrIndE
        exact if_neg fun h => hB (hiff.mp h)
      rw [hz, mul_zero, if_neg fun h => hB h.2]
  · rw [if_neg hA, if_neg fun h => hA h.1]

end HrFresh

section HrEdgeRow

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {N : Type} [Fintype N]

/-- **The weighted row bound of the absolute edge with prescribed fresh births**
[S-02:1122–1129]: the row sum over the local transition choices in which every target slot with a
prescribed value is a fresh birth with that value is at most

`(∑_ν sup |K_ν|) (∏_{g ∈ 𝒮} C_𝒮) (∏_{g ∈ ℬ} C_ℬ max(1, M_max)^T) · ∏ μ̃_g(z) · v^{j_tot}`,

the last product being over the prescribed values: the constant of `edgeAbs_rowBound` times the
point masses. -/
theorem hr_edge_row_pinned (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) {v vMinus Mmax : ℝ} {T : ℕ}
    (hq0 : 0 < D.q) (hq1 : D.q < 1) (hρ0 : 0 < D.ρ) (hρ1 : D.ρ < 1) (hv : 1 ≤ v)
    (hvm : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hlaw : ∀ g, ∑ p ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) p = 1)
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p)
    (hM : ∀ g, ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax)
    (hT : 0 < T) (hℓT : ℓ ≤ T) (hC : ∀ ν g, ℓ + ((D.fam ν).C g).card ≤ T)
    (pv : (g : B) → Slot J ℓ → Option ℕ) (s : MState 𝒢 J ℓ Bc) :
    ∑ ξ : EdgeFullChoice D Bc,
        ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ * hrIndE pv (edgeBirths ξ.2.1) *
          schurWeight v (edgeFullTgt D i s ξ) ≤
      patternMass D.fam *
          ((∏ _g : S, Schur.groupConst vMinus D.q T) *
            (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * ∏ _g : B, (max 1 Mmax) ^ T) *
        (∏ g, ∏ sl, hrW (hrPtMass 𝒢 D.q D.n g) (pv g sl)) * schurWeight v s := by
  have hMf : 0 ≤ (∏ g, ∏ sl, hrW (hrPtMass 𝒢 D.q D.n g) (pv g sl)) *
      ∏ _g : B, (max 1 Mmax) ^ T :=
    mul_nonneg
      (Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun sl _ =>
        hrW_nonneg (hrPtMass_nonneg (hν g)) _)
      (Finset.prod_nonneg fun _ _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
  have h := edgeAbs_row_full D θ i hq0 hq1 hρ0 hρ1 hv hvm hVS hVB hlaw hν hT hℓT hC
    (hrIndE pv) (hrIndE_nonneg pv) hMf
    (fun ν F x₀ hF => hr_freshIntegral_le 𝒢 hν hM (D.fam ν).C (hC ν) F x₀ hF pv) s
  refine h.trans (le_of_eq ?_)
  ring

end HrEdgeRow

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
