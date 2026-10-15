module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction.Bridge
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The row operations of the raw pattern and of the comparison patterns

Source: `verification/stage7-sources/S-03.tex`, lines 38–49 and 456–469, 542–566.

* `idealRow_apply_mix` — the ideal row operation of any pattern, with the unshared target labels
  and the auxiliary labels written as independent label lists.
* `idealRow_raw` — the raw row operation is `D_ℬ^{iζ} e(Θ D_ℬ)` times the average over the last
  `ℓ` target slots ("average out the last `ℓ` input and target slots … no multiplier uses these
  coordinates", [S-03:0458–0460]); `rawMul` is the multiplication by the raw phase.
* `idealRow_comparison_eq` — the row operation of the comparison freeing `C = A ∪ B` is
  `-(-1)^{|A|+|B|}` times `compOp` applied to the target function averaged over the last slots
  and over the slots of `B`: "the unused … target `B` labels integrate out" [S-03:0564–0566].
  `compOp H₁ p` only uses the values of `H₁` at the lists with the shared labels of `p` and fresh
  labels in `A`; it does not depend on the labels of `p` in `A` (`indep_compOp_left`), which is
  why "the unused input `A` labels" integrate out as well.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction

open scoped BigOperators ComplexConjugate

noncomputable section

section Blocks

variable {B : Type} [Fintype B] [DecidableEq B] {big : B → Finset ℕ} {J ℓ : ℕ}

omit [Fintype B] [DecidableEq B] in
theorem restrictBlock_of_eq {blk : B → Bool} {b : Bool} (C : B → Finset (Fin J)) {g : B}
    (h : blk g = b) : restrictBlock blk b C g = C g := if_pos h

omit [Fintype B] [DecidableEq B] in
theorem restrictBlock_of_ne {blk : B → Bool} {b : Bool} (C : B → Finset (Fin J)) {g : B}
    (h : ¬ blk g = b) : restrictBlock blk b C g = ∅ := if_neg h

omit [Fintype B] [DecidableEq B] in
theorem mem_of_mem_restrictBlock {blk : B → Bool} {b : Bool} {C : B → Finset (Fin J)} {g : B}
    {i : Fin J} (h : i ∈ restrictBlock blk b C g) : i ∈ C g := by
  by_cases hb : blk g = b
  · rw [restrictBlock_of_eq C hb] at h
    exact h
  · rw [restrictBlock_of_ne C hb] at h
    exact absurd h (Finset.notMem_empty i)

omit [DecidableEq B] in
theorem disjoint_slotSet_restrict (blk : B → Bool) (C : B → Finset (Fin J)) :
    Disjoint (slotSet ℓ (restrictBlock blk true C)) (slotSet ℓ (restrictBlock blk false C)) := by
  refine disjoint_slotSet fun g => ?_
  cases hb : blk g
  · rw [restrictBlock_of_ne C (by simp [hb] : ¬ blk g = true)]
    exact Finset.disjoint_empty_left _
  · rw [restrictBlock_of_ne C (by simp [hb] : ¬ blk g = false)]
    exact Finset.disjoint_empty_right _

theorem slotSet_split (blk : B → Bool) (C : B → Finset (Fin J)) :
    slotSet ℓ C =
      slotSet ℓ (restrictBlock blk true C) ∪ slotSet ℓ (restrictBlock blk false C) := by
  ext ⟨g, s⟩
  cases s with
  | inl i =>
    rw [Finset.mem_union, inl_mem_slotSet, inl_mem_slotSet, inl_mem_slotSet]
    cases hb : blk g
    · rw [restrictBlock_of_ne C (by simp [hb] : ¬ blk g = true), restrictBlock_of_eq C hb]
      simp
    · rw [restrictBlock_of_eq C hb, restrictBlock_of_ne C (by simp [hb] : ¬ blk g = false)]
      simp
  | inr j =>
    exact ⟨fun h => absurd h inr_notMem_slotSet,
      fun h => (Finset.mem_union.mp h).elim (fun h => absurd h inr_notMem_slotSet)
        (fun h => absurd h inr_notMem_slotSet)⟩

theorem freeSet_eq (blk : B → Bool) (C : B → Finset (Fin J)) :
    freeSet ℓ C = slotSet ℓ (restrictBlock blk true C) ∪
      (slotSet ℓ (restrictBlock blk false C) ∪ lastSet B J ℓ) := by
  unfold freeSet
  rw [slotSet_split blk C, Finset.union_assoc]

theorem slotSet_restrict_subset_freeSet (blk : B → Bool) (b : Bool) (C : B → Finset (Fin J)) :
    slotSet ℓ (restrictBlock blk b C) ⊆ freeSet ℓ C := by
  rintro ⟨g, s⟩ hk
  obtain ⟨i, hi, rfl⟩ := mem_slotSet.mp hk
  exact inl_mem_freeSet.mpr (mem_of_mem_restrictBlock hi)

omit [DecidableEq B] in
theorem slotSet_empty : slotSet ℓ (fun _ : B => (∅ : Finset (Fin J))) = ∅ :=
  Finset.subset_empty.mp (by
    rintro ⟨g, s⟩ h
    obtain ⟨i, hi, _⟩ := mem_slotSet.mp h
    exact absurd hi (Finset.notMem_empty i))

omit [DecidableEq B] in
theorem blockAuxProd_restr (blk : B → Bool) (b : Bool) (C : B → Finset (Fin J))
    (d : LabelList big J ℓ) :
    blockAuxProd blk b C (restr C d) = sp (restrictBlock blk b C) d := by
  unfold blockAuxProd sp
  refine Finset.prod_congr rfl fun g _ => ?_
  by_cases hb : blk g = b
  · rw [if_pos hb, restrictBlock_of_eq C hb]
    exact Finset.prod_coe_sort (C g) (fun i => (d g (Sum.inl i) : ℕ))
  · rw [if_neg hb, restrictBlock_of_ne C hb, Finset.prod_empty]

omit [DecidableEq B] in
theorem blockListProd_eq (blk : B → Bool) (b : Bool) (C : B → Finset (Fin J))
    (p : LabelList big J ℓ) :
    blockListProd blk b C p = sp (restrictBlock blk b C) p := by
  unfold blockListProd sp
  refine Finset.prod_congr rfl fun g _ => ?_
  by_cases hb : blk g = b
  · rw [if_pos hb, restrictBlock_of_eq C hb]
  · rw [if_neg hb, restrictBlock_of_ne C hb, Finset.prod_empty]

omit [DecidableEq B] in
theorem sp_split (blk : B → Bool) (C : B → Finset (Fin J)) (d : LabelList big J ℓ) :
    sp C d = sp (restrictBlock blk true C) d * sp (restrictBlock blk false C) d := by
  unfold sp
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun g _ => ?_
  cases hb : blk g
  · rw [restrictBlock_of_ne C (by simp [hb] : ¬ blk g = true), restrictBlock_of_eq C hb,
      Finset.prod_empty, one_mul]
  · rw [restrictBlock_of_eq C hb, restrictBlock_of_ne C (by simp [hb] : ¬ blk g = false),
      Finset.prod_empty, mul_one]

end Blocks

section Rows

variable {B : Type} [Fintype B] [DecidableEq B] {big : B → Finset ℕ} {J ℓ : ℕ}

/-- **The ideal row operation of a pattern** [S-02:0086–0093], with the unshared target labels
(`q`) and the auxiliary labels (`d`) written as independent label lists. -/
theorem idealRow_apply_mix (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (ν : Pattern big J ℓ) (ζ Θ : ℝ) (H : LabelList big J ℓ → ℂ) (p : LabelList big J ℓ) :
    idealRow ν ζ Θ H p =
      ∑ d : LabelList big J ℓ, (idealWeight big J ℓ d : ℂ) *
        ∑ q : LabelList big J ℓ, (idealWeight big J ℓ q : ℂ) *
          (ν.K p (mix (freeSet ℓ ν.C) p q) (restr ν.C d) *
            dilPhase ζ Θ (bigDil ν.C p (restr ν.C d)) * H (mix (freeSet ℓ ν.C) p q)) := by
  classical
  have hr : ∀ r : AuxList big ν.C,
      ∑ p' : LabelList big J ℓ, idealCoef ν ζ Θ p r p' * H p' =
        (auxWeight big ν.C r : ℂ) * ∑ q : LabelList big J ℓ, (idealWeight big J ℓ q : ℂ) *
          (ν.K p (mix (freeSet ℓ ν.C) p q) r * dilPhase ζ Θ (bigDil ν.C p r) *
            H (mix (freeSet ℓ ν.C) p q)) := by
    intro r
    have hterm : ∀ p' : LabelList big J ℓ, idealCoef ν ζ Θ p r p' * H p' =
        (if SharedBig ν.C p p' then ((unsharedWeight big ν.C p' : ℝ) : ℂ) *
          ((auxWeight big ν.C r : ℂ) * (ν.K p p' r * dilPhase ζ Θ (bigDil ν.C p r) * H p'))
        else 0) := by
      intro p'
      unfold idealCoef
      by_cases hs : SharedBig ν.C p p'
      · rw [if_pos hs, if_pos hs]
        push_cast
        ring
      · rw [if_neg hs, if_neg hs, zero_mul]
    calc ∑ p' : LabelList big J ℓ, idealCoef ν ζ Θ p r p' * H p'
        = ∑ p' : LabelList big J ℓ, (if SharedBig ν.C p p' then
            ((unsharedWeight big ν.C p' : ℝ) : ℂ) * ((auxWeight big ν.C r : ℂ) *
              (ν.K p p' r * dilPhase ζ Θ (bigDil ν.C p r) * H p')) else 0) :=
          Finset.sum_congr rfl fun p' _ => hterm p'
      _ = ∑ q : LabelList big J ℓ, (idealWeight big J ℓ q : ℂ) *
            ((auxWeight big ν.C r : ℂ) * (ν.K p (mix (freeSet ℓ ν.C) p q) r *
              dilPhase ζ Θ (bigDil ν.C p r) * H (mix (freeSet ℓ ν.C) p q))) :=
          sum_shared_eq hlaw ν.C p (fun p' => (auxWeight big ν.C r : ℂ) *
            (ν.K p p' r * dilPhase ζ Θ (bigDil ν.C p r) * H p'))
      _ = (auxWeight big ν.C r : ℂ) * ∑ q : LabelList big J ℓ, (idealWeight big J ℓ q : ℂ) *
            (ν.K p (mix (freeSet ℓ ν.C) p q) r * dilPhase ζ Θ (bigDil ν.C p r) *
              H (mix (freeSet ℓ ν.C) p q)) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun q _ => by ring
  have h0 : idealRow ν ζ Θ H p =
      ∑ r : AuxList big ν.C, ∑ p' : LabelList big J ℓ, idealCoef ν ζ Θ p r p' * H p' :=
    Fintype.sum_prod_type (fun ξ : AuxList big ν.C × LabelList big J ℓ =>
      idealCoef ν ζ Θ p ξ.1 ξ.2 * H ξ.2)
  rw [h0, Finset.sum_congr rfl fun r _ => hr r]
  exact sum_aux_eq hlaw ν.C (fun r => ∑ q : LabelList big J ℓ, (idealWeight big J ℓ q : ℂ) *
    (ν.K p (mix (freeSet ℓ ν.C) p q) r * dilPhase ζ Θ (bigDil ν.C p r) *
      H (mix (freeSet ℓ ν.C) p q)))

/-- **The raw row operation** [S-03:0456–0469]: the raw phase times the average over the last
`ℓ` target slots. -/
theorem idealRow_raw (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1) (ζ Θ : ℝ)
    (H : LabelList big J ℓ → ℂ) (p : LabelList big J ℓ) :
    idealRow (Pattern.raw big J ℓ) ζ Θ H p =
      dilPhase ζ Θ (fullProd p) * avg big J ℓ (lastSet B J ℓ) H p := by
  have hfree : freeSet ℓ (Pattern.raw big J ℓ).C = lastSet B J ℓ := by
    show slotSet ℓ (fun _ : B => (∅ : Finset (Fin J))) ∪ lastSet B J ℓ = lastSet B J ℓ
    rw [slotSet_empty, Finset.empty_union]
  have hdil : ∀ d : LabelList big J ℓ,
      bigDil (Pattern.raw big J ℓ).C p (restr (Pattern.raw big J ℓ).C d) = fullProd p := by
    intro d
    rw [bigDil_restr]
    show sharedProd (fun _ : B => (∅ : Finset (Fin J))) p *
      sp (fun _ : B => (∅ : Finset (Fin J))) d = fullProd p
    unfold sharedProd sp fullProd
    simp
  have hsum : ∀ d : LabelList big J ℓ,
      ∑ q : LabelList big J ℓ, (idealWeight big J ℓ q : ℂ) *
        ((Pattern.raw big J ℓ).K p (mix (freeSet ℓ (Pattern.raw big J ℓ).C) p q)
            (restr (Pattern.raw big J ℓ).C d) *
          dilPhase ζ Θ (bigDil (Pattern.raw big J ℓ).C p (restr (Pattern.raw big J ℓ).C d)) *
          H (mix (freeSet ℓ (Pattern.raw big J ℓ).C) p q)) =
        dilPhase ζ Θ (fullProd p) * avg big J ℓ (lastSet B J ℓ) H p := by
    intro d
    rw [hdil d, hfree, avg_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    show (idealWeight big J ℓ q : ℂ) *
        ((1 : ℂ) * dilPhase ζ Θ (fullProd p) * H (mix (lastSet B J ℓ) p q)) =
      dilPhase ζ Θ (fullProd p) * ((idealWeight big J ℓ q : ℂ) * H (mix (lastSet B J ℓ) p q))
    ring
  rw [idealRow_apply_mix hlaw]
  simp only [hsum]
  rw [← Finset.sum_mul, sum_idealWeight_cast hlaw, one_mul]

/-- The row operation of the comparison pattern freeing `C`, with its coefficient
(eq:ideal-comparison-coefficient) written out. -/
theorem idealRow_comparison (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (blk : B → Bool) (Q h ξ : ℝ) (C : B → Finset (Fin J)) (ζ Θ : ℝ)
    (H : LabelList big J ℓ → ℂ) (p : LabelList big J ℓ) :
    idealRow (comparisonPattern big J ℓ blk Q h ξ C) ζ Θ H p =
      -((-1 : ℂ) ^ (∑ g, (C g).card)) *
        ∑ d : LabelList big J ℓ, (idealWeight big J ℓ d : ℂ) *
          ∑ q : LabelList big J ℓ, (idealWeight big J ℓ q : ℂ) *
            (cellKernel big (restrictBlock blk true C) Q h ξ (sp (restrictBlock blk true C) d)
                (sp (restrictBlock blk true C) q) *
              cellKernel big (restrictBlock blk false C) Q h ξ (sp (restrictBlock blk false C) d)
                (sp (restrictBlock blk false C) p) *
              dilPhase ζ Θ (sharedProd C p *
                (sp (restrictBlock blk true C) d * sp (restrictBlock blk false C) d)) *
              H (mix (freeSet ℓ C) p q)) := by
  have e : ∀ d q : LabelList big J ℓ,
      (comparisonPattern big J ℓ blk Q h ξ C).K p (mix (freeSet ℓ C) p q) (restr C d) *
          dilPhase ζ Θ (bigDil C p (restr C d)) * H (mix (freeSet ℓ C) p q) =
        -((-1 : ℂ) ^ (∑ g, (C g).card)) *
          (cellKernel big (restrictBlock blk true C) Q h ξ (sp (restrictBlock blk true C) d)
              (sp (restrictBlock blk true C) q) *
            cellKernel big (restrictBlock blk false C) Q h ξ (sp (restrictBlock blk false C) d)
              (sp (restrictBlock blk false C) p) *
            dilPhase ζ Θ (sharedProd C p *
              (sp (restrictBlock blk true C) d * sp (restrictBlock blk false C) d)) *
            H (mix (freeSet ℓ C) p q)) := by
    intro d q
    show -((-1 : ℂ) ^ (∑ g, (C g).card)) *
        (cellKernel big (restrictBlock blk true C) Q h ξ (blockAuxProd blk true C (restr C d))
            (blockListProd blk true C (mix (freeSet ℓ C) p q)) *
          cellKernel big (restrictBlock blk false C) Q h ξ (blockAuxProd blk false C (restr C d))
            (blockListProd blk false C p)) *
        dilPhase ζ Θ (bigDil C p (restr C d)) * H (mix (freeSet ℓ C) p q) = _
    rw [blockAuxProd_restr, blockAuxProd_restr, blockListProd_eq, blockListProd_eq, bigDil_restr,
      sp_split blk C d, sp_mix_of_subset (slotSet_restrict_subset_freeSet blk true C) p q]
    ring
  calc idealRow (comparisonPattern big J ℓ blk Q h ξ C) ζ Θ H p
      = ∑ d : LabelList big J ℓ, (idealWeight big J ℓ d : ℂ) *
          ∑ q : LabelList big J ℓ, (idealWeight big J ℓ q : ℂ) *
            ((comparisonPattern big J ℓ blk Q h ξ C).K p (mix (freeSet ℓ C) p q) (restr C d) *
              dilPhase ζ Θ (bigDil C p (restr C d)) * H (mix (freeSet ℓ C) p q)) :=
        idealRow_apply_mix hlaw _ ζ Θ H p
    _ = ∑ d : LabelList big J ℓ, (idealWeight big J ℓ d : ℂ) *
          ∑ q : LabelList big J ℓ, (idealWeight big J ℓ q : ℂ) *
            (-((-1 : ℂ) ^ (∑ g, (C g).card)) *
              (cellKernel big (restrictBlock blk true C) Q h ξ (sp (restrictBlock blk true C) d)
                  (sp (restrictBlock blk true C) q) *
                cellKernel big (restrictBlock blk false C) Q h ξ
                  (sp (restrictBlock blk false C) d) (sp (restrictBlock blk false C) p) *
                dilPhase ζ Θ (sharedProd C p *
                  (sp (restrictBlock blk true C) d * sp (restrictBlock blk false C) d)) *
                H (mix (freeSet ℓ C) p q))) :=
        Finset.sum_congr rfl fun d _ => congrArg (fun z : ℂ => (idealWeight big J ℓ d : ℂ) * z)
          (Finset.sum_congr rfl fun q _ =>
            congrArg (fun z : ℂ => (idealWeight big J ℓ q : ℂ) * z) (e d q))
    _ = -((-1 : ℂ) ^ (∑ g, (C g).card)) *
          ∑ d : LabelList big J ℓ, (idealWeight big J ℓ d : ℂ) *
            ∑ q : LabelList big J ℓ, (idealWeight big J ℓ q : ℂ) *
              (cellKernel big (restrictBlock blk true C) Q h ξ (sp (restrictBlock blk true C) d)
                  (sp (restrictBlock blk true C) q) *
                cellKernel big (restrictBlock blk false C) Q h ξ
                  (sp (restrictBlock blk false C) d) (sp (restrictBlock blk false C) p) *
                dilPhase ζ Θ (sharedProd C p *
                  (sp (restrictBlock blk true C) d * sp (restrictBlock blk false C) d)) *
                H (mix (freeSet ℓ C) p q)) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun q _ => by ring

/-- **Integrating out unused target labels**: if the multiplier only uses the labels in the slots
of `Λ ⊆ U`, the fresh labels in the coordinates of `V` (disjoint from `Λ`) average the target
function. -/
theorem sum_mix_union_eq (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    {Λ : B → Finset (Fin J)} {U V : Finset (B × Slot J ℓ)} (hU : slotSet ℓ Λ ⊆ U)
    (hV : Disjoint (slotSet ℓ Λ) V) (k : ℕ → ℂ) (H : LabelList big J ℓ → ℂ)
    (p : LabelList big J ℓ) :
    ∑ q : LabelList big J ℓ, (idealWeight big J ℓ q : ℂ) *
        (k (sp Λ q) * H (mix (U ∪ V) p q)) =
      ∑ q : LabelList big J ℓ, (idealWeight big J ℓ q : ℂ) *
        (k (sp Λ q) * avg big J ℓ V H (mix U p q)) := by
  have hkV : Indep V (fun p' : LabelList big J ℓ => k (sp Λ p')) := by
    intro p' q'
    show k (sp Λ (mix V p' q')) = k (sp Λ p')
    rw [sp_mix_of_disjoint hV p' q']
  have h1 : ∑ q : LabelList big J ℓ, (idealWeight big J ℓ q : ℂ) *
        (k (sp Λ q) * H (mix (U ∪ V) p q)) =
      avg big J ℓ (U ∪ V) (fun p' => k (sp Λ p') * H p') p := by
    rw [avg_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    show (idealWeight big J ℓ q : ℂ) * (k (sp Λ q) * H (mix (U ∪ V) p q)) =
      (idealWeight big J ℓ q : ℂ) * (k (sp Λ (mix (U ∪ V) p q)) * H (mix (U ∪ V) p q))
    rw [sp_mix_of_subset (hU.trans Finset.subset_union_left) p q]
  have h2 : avg big J ℓ (U ∪ V) (fun p' => k (sp Λ p') * H p') =
      avg big J ℓ U (fun p' => k (sp Λ p') * avg big J ℓ V H p') := by
    rw [← avg_mul hlaw U V]
    show avg big J ℓ U (avg big J ℓ V (fun p' => k (sp Λ p') * H p')) = _
    rw [avg_mul_left_of_indep hkV H]
  rw [h1, h2, avg_apply]
  refine Finset.sum_congr rfl fun q _ => ?_
  show (idealWeight big J ℓ q : ℂ) * (k (sp Λ (mix U p q)) * avg big J ℓ V H (mix U p q)) =
    (idealWeight big J ℓ q : ℂ) * (k (sp Λ q) * avg big J ℓ V H (mix U p q))
  rw [sp_mix_of_subset hU p q]

/-- `E_D 𝒦_A(D_A, X) 𝒦_B(D_B, Y) (D_A D_B)^{iζ} e(α D_A D_B)`, where `D_A`, `D_B` are the
products of the labels of one random list in the slots of `A` and of `B`. -/
def kk (big : B → Finset ℕ) (J ℓ : ℕ) (A Bs : B → Finset (Fin J)) (Q h ξ ζ α : ℝ)
    (X Y : ℕ) : ℂ :=
  ∑ d : LabelList big J ℓ, (idealWeight big J ℓ d : ℂ) *
    (cellKernel big A Q h ξ (sp A d) X * cellKernel big Bs Q h ξ (sp Bs d) Y *
      dilPhase ζ α (sp A d * sp Bs d))

/-- **The comparison operator of the freed set `C = A ∪ B`**: at the source list `p`, with `S`
the product of the shared labels, `X_B` the product of the source labels in `B` and fresh target
labels `X_A` in `A`:
`S^{iζ} E_{X_A} H₁(target) E_D 𝒦_A(D_A, X_A) 𝒦_B(D_B, X_B) (D_A D_B)^{iζ} e(Θ S D_A D_B)`. -/
def compOp (big : B → Finset ℕ) (J ℓ : ℕ) (blk : B → Bool) (Q h ξ : ℝ)
    (C : B → Finset (Fin J)) (ζ Θ : ℝ) (H₁ : LabelList big J ℓ → ℂ)
    (p : LabelList big J ℓ) : ℂ :=
  ((sharedProd C p : ℕ) : ℂ) ^ ((ζ : ℂ) * Complex.I) *
    ∑ q : LabelList big J ℓ, (idealWeight big J ℓ q : ℂ) *
      (H₁ (mix (slotSet ℓ (restrictBlock blk true C)) p q) *
        kk big J ℓ (restrictBlock blk true C) (restrictBlock blk false C) Q h ξ ζ
          (Θ * ((sharedProd C p : ℕ) : ℝ)) (sp (restrictBlock blk true C) q)
          (sp (restrictBlock blk false C) p))

/-- **The row operation of a comparison** [S-03:0542–0566]: `-(-1)^{|A|+|B|}` times the
comparison operator, applied to the target function averaged over the slots of `B` and the last
`ℓ` slots. -/
theorem idealRow_comparison_eq (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (blk : B → Bool) (Q h ξ : ℝ) (C : B → Finset (Fin J)) (ζ Θ : ℝ)
    (H : LabelList big J ℓ → ℂ) (p : LabelList big J ℓ) :
    idealRow (comparisonPattern big J ℓ blk Q h ξ C) ζ Θ H p =
      -((-1 : ℂ) ^ (∑ g, (C g).card)) *
        compOp big J ℓ blk Q h ξ C ζ Θ
          (avg big J ℓ (slotSet ℓ (restrictBlock blk false C) ∪ lastSet B J ℓ) H) p := by
  have hV : Disjoint (slotSet ℓ (restrictBlock blk true C))
      (slotSet ℓ (restrictBlock blk false C) ∪ lastSet B J ℓ) :=
    Finset.disjoint_union_right.mpr
      ⟨disjoint_slotSet_restrict blk C, disjoint_slotSet_lastSet _⟩
  have step1 : ∀ d : LabelList big J ℓ,
      ∑ q : LabelList big J ℓ, (idealWeight big J ℓ q : ℂ) *
        (cellKernel big (restrictBlock blk true C) Q h ξ (sp (restrictBlock blk true C) d)
            (sp (restrictBlock blk true C) q) *
          cellKernel big (restrictBlock blk false C) Q h ξ (sp (restrictBlock blk false C) d)
            (sp (restrictBlock blk false C) p) *
          dilPhase ζ Θ (sharedProd C p *
            (sp (restrictBlock blk true C) d * sp (restrictBlock blk false C) d)) *
          H (mix (freeSet ℓ C) p q)) =
      ∑ q : LabelList big J ℓ, (idealWeight big J ℓ q : ℂ) *
        (cellKernel big (restrictBlock blk true C) Q h ξ (sp (restrictBlock blk true C) d)
            (sp (restrictBlock blk true C) q) *
          cellKernel big (restrictBlock blk false C) Q h ξ (sp (restrictBlock blk false C) d)
            (sp (restrictBlock blk false C) p) *
          dilPhase ζ Θ (sharedProd C p *
            (sp (restrictBlock blk true C) d * sp (restrictBlock blk false C) d)) *
          avg big J ℓ (slotSet ℓ (restrictBlock blk false C) ∪ lastSet B J ℓ) H
            (mix (slotSet ℓ (restrictBlock blk true C)) p q)) := by
    intro d
    rw [freeSet_eq blk C]
    exact sum_mix_union_eq hlaw (Finset.Subset.refl _) hV
      (fun X => cellKernel big (restrictBlock blk true C) Q h ξ (sp (restrictBlock blk true C) d) X *
        cellKernel big (restrictBlock blk false C) Q h ξ (sp (restrictBlock blk false C) d)
          (sp (restrictBlock blk false C) p) *
        dilPhase ζ Θ (sharedProd C p *
          (sp (restrictBlock blk true C) d * sp (restrictBlock blk false C) d))) H p
  rw [idealRow_comparison hlaw]
  congr 1
  calc ∑ d : LabelList big J ℓ, (idealWeight big J ℓ d : ℂ) *
        ∑ q : LabelList big J ℓ, (idealWeight big J ℓ q : ℂ) *
          (cellKernel big (restrictBlock blk true C) Q h ξ (sp (restrictBlock blk true C) d)
              (sp (restrictBlock blk true C) q) *
            cellKernel big (restrictBlock blk false C) Q h ξ (sp (restrictBlock blk false C) d)
              (sp (restrictBlock blk false C) p) *
            dilPhase ζ Θ (sharedProd C p *
              (sp (restrictBlock blk true C) d * sp (restrictBlock blk false C) d)) *
            H (mix (freeSet ℓ C) p q))
      = ∑ d : LabelList big J ℓ, (idealWeight big J ℓ d : ℂ) *
          ∑ q : LabelList big J ℓ, (idealWeight big J ℓ q : ℂ) *
            (cellKernel big (restrictBlock blk true C) Q h ξ (sp (restrictBlock blk true C) d)
                (sp (restrictBlock blk true C) q) *
              cellKernel big (restrictBlock blk false C) Q h ξ
                (sp (restrictBlock blk false C) d) (sp (restrictBlock blk false C) p) *
              dilPhase ζ Θ (sharedProd C p *
                (sp (restrictBlock blk true C) d * sp (restrictBlock blk false C) d)) *
              avg big J ℓ (slotSet ℓ (restrictBlock blk false C) ∪ lastSet B J ℓ) H
                (mix (slotSet ℓ (restrictBlock blk true C)) p q)) :=
        Finset.sum_congr rfl fun d _ =>
          congrArg (fun z : ℂ => (idealWeight big J ℓ d : ℂ) * z) (step1 d)
    _ = ∑ d : LabelList big J ℓ, ∑ q : LabelList big J ℓ, (idealWeight big J ℓ d : ℂ) *
          ((idealWeight big J ℓ q : ℂ) *
            (cellKernel big (restrictBlock blk true C) Q h ξ (sp (restrictBlock blk true C) d)
                (sp (restrictBlock blk true C) q) *
              cellKernel big (restrictBlock blk false C) Q h ξ
                (sp (restrictBlock blk false C) d) (sp (restrictBlock blk false C) p) *
              dilPhase ζ Θ (sharedProd C p *
                (sp (restrictBlock blk true C) d * sp (restrictBlock blk false C) d)) *
              avg big J ℓ (slotSet ℓ (restrictBlock blk false C) ∪ lastSet B J ℓ) H
                (mix (slotSet ℓ (restrictBlock blk true C)) p q))) :=
        Finset.sum_congr rfl fun d _ => by rw [Finset.mul_sum]
    _ = ∑ q : LabelList big J ℓ, ∑ d : LabelList big J ℓ, (idealWeight big J ℓ d : ℂ) *
          ((idealWeight big J ℓ q : ℂ) *
            (cellKernel big (restrictBlock blk true C) Q h ξ (sp (restrictBlock blk true C) d)
                (sp (restrictBlock blk true C) q) *
              cellKernel big (restrictBlock blk false C) Q h ξ
                (sp (restrictBlock blk false C) d) (sp (restrictBlock blk false C) p) *
              dilPhase ζ Θ (sharedProd C p *
                (sp (restrictBlock blk true C) d * sp (restrictBlock blk false C) d)) *
              avg big J ℓ (slotSet ℓ (restrictBlock blk false C) ∪ lastSet B J ℓ) H
                (mix (slotSet ℓ (restrictBlock blk true C)) p q))) := Finset.sum_comm
    _ = compOp big J ℓ blk Q h ξ C ζ Θ
          (avg big J ℓ (slotSet ℓ (restrictBlock blk false C) ∪ lastSet B J ℓ) H) p := by
        unfold compOp kk
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [dilPhase_mul]
        ring

/-- The comparison operator does not use the source labels in the slots of `A`. -/
theorem indep_compOp_left (blk : B → Bool) (Q h ξ : ℝ) (C : B → Finset (Fin J)) (ζ Θ : ℝ)
    (H₁ : LabelList big J ℓ → ℂ) :
    Indep (slotSet ℓ (restrictBlock blk true C)) (compOp big J ℓ blk Q h ξ C ζ Θ H₁) := by
  intro p q'
  have hsh : ∀ (g : B) (i : Fin J),
      (g, (Sum.inl i : Slot J ℓ)) ∈ slotSet ℓ (restrictBlock blk true C) → i ∈ C g :=
    fun g i hh => mem_of_mem_restrictBlock (inl_mem_slotSet.mp hh)
  unfold compOp
  rw [sharedProd_mix hsh p q', sp_mix_of_disjoint (disjoint_slotSet_restrict blk C).symm p q']
  simp only [mix_mix_same]

/-- If `H₁` does not depend on the last `ℓ` slots, neither does its image under the comparison
operator. -/
theorem indep_compOp_last (blk : B → Bool) (Q h ξ : ℝ) (C : B → Finset (Fin J)) (ζ Θ : ℝ)
    {H₁ : LabelList big J ℓ → ℂ} (hH : Indep (lastSet B J ℓ) H₁) :
    Indep (lastSet B J ℓ) (compOp big J ℓ blk Q h ξ C ζ Θ H₁) := by
  intro p q'
  have hsh : ∀ (g : B) (i : Fin J),
      (g, (Sum.inl i : Slot J ℓ)) ∈ lastSet B J ℓ → i ∈ C g :=
    fun g i hh => absurd hh (inl_notMem_lastSet g i)
  unfold compOp
  rw [sharedProd_mix hsh p q', sp_mix_of_disjoint (disjoint_slotSet_lastSet _) p q']
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [mix_mix_comm (disjoint_slotSet_lastSet (restrictBlock blk true C)) p q' q,
    hH (mix (slotSet ℓ (restrictBlock blk true C)) p q) q']

/-! ### The raw phase -/

/-- Multiplication by the raw phase `D_ℬ^{iζ} e(Θ D_ℬ)`, `D_ℬ` the product of the labels in the
first `J` slots. -/
def rawMul (big : B → Finset ℕ) (J ℓ : ℕ) (ζ Θ : ℝ) :
    Module.End ℂ (LabelList big J ℓ → ℂ) where
  toFun F := fun p => dilPhase ζ Θ (fullProd p) * F p
  map_add' F G := by
    funext p
    simp only [Pi.add_apply, mul_add]
  map_smul' c F := by
    funext p
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

omit [DecidableEq B] in
theorem rawMul_apply (ζ Θ : ℝ) (F : LabelList big J ℓ → ℂ) (p : LabelList big J ℓ) :
    rawMul big J ℓ ζ Θ F p = dilPhase ζ Θ (fullProd p) * F p := rfl

/-- The raw row operation is the raw phase times the average over the last `ℓ` slots. -/
theorem idealRow_raw_eq (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (ζ Θ : ℝ) (H : LabelList big J ℓ → ℂ) :
    idealRow (Pattern.raw big J ℓ) ζ Θ H =
      rawMul big J ℓ ζ Θ (avg big J ℓ (lastSet B J ℓ) H) :=
  funext fun p => idealRow_raw hlaw ζ Θ H p

theorem fullProd_mix_last (p q : LabelList big J ℓ) :
    fullProd (mix (lastSet B J ℓ) p q) = fullProd p := by
  unfold fullProd
  refine Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun i _ => ?_
  rw [mix_of_notMem p q (inl_notMem_lastSet g i)]

/-- The raw phase does not use the last `ℓ` slots. -/
theorem indep_rawMul_last (ζ Θ : ℝ) {F : LabelList big J ℓ → ℂ}
    (hF : Indep (lastSet B J ℓ) F) : Indep (lastSet B J ℓ) (rawMul big J ℓ ζ Θ F) := by
  intro p q
  show dilPhase ζ Θ (fullProd (mix (lastSet B J ℓ) p q)) * F (mix (lastSet B J ℓ) p q) =
    dilPhase ζ Θ (fullProd p) * F p
  rw [fullProd_mix_last, hF p q]

theorem wNorm_rawMul_le (hnn : ∀ p : LabelList big J ℓ, 0 ≤ idealWeight big J ℓ p) (ζ Θ : ℝ)
    (F : LabelList big J ℓ → ℂ) :
    wNorm (idealWeight big J ℓ) (rawMul big J ℓ ζ Θ F) ≤ wNorm (idealWeight big J ℓ) F :=
  wNorm_mul_le hnn (fun p => dilPhase ζ Θ (fullProd p)) F fun _ => norm_dilPhase_le ζ Θ _

end Rows

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction
