module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.BilinearFourierProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.KernelExpansionProof
public import SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction.Rows
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Statements

/-!
# The additive multiplier as a probability-space bilinear form

`[P-06:0417–0430]`: "The additive multiplier for (cor:comparison-sum) is
`𝔪(θ) := E b₁(D_A) b₂(D_B) e(θ D_A D_B)`", where `D_A`, `D_B` are the products of the free labels
of the two blocks; "the two nonempty free products are independent" (`[P-06:0383–0384]`).

`multiplier_eq_phaseForm`: for tests `b₁`, `b₂` on the free labels that depend only on the labels
of the first, respectively the second, block,

`𝔪(θ) = E_{X_A, X_B} b₂(X_B) b₁(X_A) e(θ P_A P_B)`,

the bilinear form `Comparison.phaseForm` of [S] (eq:ideal-probability-bilinear) for two independent
label tuples on the slots of the two blocks (with `ζ = 0`).

The proof writes both sides as integrals over one random label list (`multiplier_eq_sum`,
`phaseForm_eq_sum`): a tuple on a slot set is the restriction of a random list
(`IdealConstruction.sum_aux_eq`), and two independent lists restricted to disjoint slot sets are
one list restricted to both (`IdealConstruction.sum_avg`, the swap of the labels of the second
slot set being measure preserving).

* `blockRestrict`: a test depending only on the labels of one block, as a test on the tuples of
  that block; its support and its norm (`blockRestrict_cell`, `tupleNorm_le_one`).
* `label_le_blockAuxProd`, `blockAuxProd_le_tupleProd`: sizes of the block products.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference
open SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction
open SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

noncomputable section

/-- The phase `D^{iζ} e(θ D)` at `ζ = 0` is `e(θ D)`. -/
theorem dilPhase_zero_eq_addChar (θ : ℝ) (D : ℕ) : dilPhase 0 θ D = addChar (θ * (D : ℝ)) := by
  unfold dilPhase
  rw [Complex.ofReal_zero, zero_mul, Complex.cpow_zero, one_mul, addChar_eq_expUnit]

section Collapse

variable {B : Type} [Fintype B] [DecidableEq B] {big : B → Finset ℕ} {J : ℕ}

omit [Fintype B] [DecidableEq B] in
/-- The labels of `ins Λ p t` in the slots of `Λ` are those of `t`. -/
theorem restr_ins (Λ : B → Finset (Fin J)) (p : LabelList big J 0) (t : AuxList big Λ) :
    restr Λ (ins Λ p t) = t := by
  funext g i
  show (if h : (i : Fin J) ∈ Λ g then t g ⟨i, h⟩ else p g (Sum.inl i)) = t g i
  exact dif_pos i.2

/-- A test on the free labels, read on the tuples of the block `b`: the other labels are those of
a fixed list `p₀`. -/
def blockRestrict (blk : B → Bool) (b : Bool) (C : B → Finset (Fin J)) (p₀ : LabelList big J 0)
    (β : AuxList big C → ℂ) : AuxList big (restrictBlock blk b C) → ℂ :=
  fun t => β (restr C (ins (restrictBlock blk b C) p₀ t))

omit [Fintype B] [DecidableEq B] in
/-- A test that depends only on the labels of the block `b` is a function of the restriction of
the list to the slots of the block. -/
theorem blockRestrict_restr {blk : B → Bool} {b : Bool} {C : B → Finset (Fin J)}
    (p₀ : LabelList big J 0) {β : AuxList big C → ℂ}
    (hdep : ∀ r r' : AuxList big C, (∀ g, blk g = b → r g = r' g) → β r = β r')
    (q : LabelList big J 0) :
    blockRestrict blk b C p₀ β (restr (restrictBlock blk b C) q) = β (restr C q) := by
  refine hdep _ _ fun g hg => funext fun i => ?_
  have hi : (i : Fin J) ∈ restrictBlock blk b C g := by
    rw [restrictBlock_of_eq C hg]
    exact i.2
  show (if h : (i : Fin J) ∈ restrictBlock blk b C g then
      restr (restrictBlock blk b C) q g ⟨i, h⟩ else p₀ g (Sum.inl i)) = q g (Sum.inl i)
  exact dif_pos hi

/-- The support of the restricted test: the product of the tuple lies in the log cell. -/
theorem blockRestrict_cell {blk : B → Bool} {b : Bool} {C : B → Finset (Fin J)}
    (p₀ : LabelList big J 0) {β : AuxList big C → ℂ} {U : ℝ} (hβ : BlockTest blk b C β U)
    (t : AuxList big (restrictBlock blk b C)) (ht : blockRestrict blk b C p₀ β t ≠ 0) :
    U ≤ ((tupleProd (restrictBlock blk b C) t : ℕ) : ℝ) ∧
      ((tupleProd (restrictBlock blk b C) t : ℕ) : ℝ) ≤ Real.exp 1 * U := by
  have h := hβ.cell (restr C (ins (restrictBlock blk b C) p₀ t)) ht
  have e : blockAuxProd blk b C (restr C (ins (restrictBlock blk b C) p₀ t)) =
      tupleProd (restrictBlock blk b C) t := by
    rw [blockAuxProd_restr, ← tupleProd_restr, restr_ins]
  rw [e] at h
  exact h

/-- A test of modulus at most one has norm at most one in the probability space of the tuples. -/
theorem tupleNorm_le_one (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (Λ : B → Finset (Fin J)) {F : AuxList big Λ → ℂ} (hF : ∀ t, ‖F t‖ ≤ 1) :
    tupleNorm big Λ F ≤ 1 := by
  have h1 : ∑ t : AuxList big Λ, auxWeight big Λ t * ‖F t‖ ^ 2 ≤ 1 :=
    calc ∑ t : AuxList big Λ, auxWeight big Λ t * ‖F t‖ ^ 2
        ≤ ∑ t : AuxList big Λ, auxWeight big Λ t * 1 :=
          Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left
            (pow_le_one₀ (norm_nonneg _) (hF t)) (Schur.auxWeight_nonneg big Λ t)
      _ = ∑ t : AuxList big Λ, auxWeight big Λ t :=
          Finset.sum_congr rfl fun t _ => mul_one _
      _ = 1 := sum_auxWeight hlaw Λ
  unfold tupleNorm wNorm wNormSq
  calc Real.sqrt (∑ t : AuxList big Λ, auxWeight big Λ t * ‖F t‖ ^ 2)
      ≤ Real.sqrt 1 := Real.sqrt_le_sqrt h1
    _ = 1 := Real.sqrt_one

/-- The multiplier of a test that vanishes identically is zero. -/
theorem multiplier_eq_zero (C : B → Finset (Fin J)) {b : AuxList big C → ℂ} (h : ∀ r, b r = 0)
    (θ : ℝ) : multiplier big C b θ = 0 := by
  unfold multiplier
  exact Finset.sum_eq_zero fun r _ => by rw [h r, mul_zero, zero_mul]

/-- **The multiplier as an integral over one random label list.** -/
theorem multiplier_eq_sum (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (C : B → Finset (Fin J)) (b : AuxList big C → ℂ) (θ : ℝ) :
    multiplier big C b θ =
      ∑ p : LabelList big J 0, (idealWeight big J 0 p : ℂ) *
        (b (restr C p) * addChar (θ * (sp C p : ℝ))) := by
  have h : ∑ r : AuxList big C,
        (auxWeight big C r : ℂ) * (b r * addChar (θ * (tupleProd C r : ℝ))) =
      ∑ q : LabelList big J 0, (idealWeight big J 0 q : ℂ) *
        (b (restr C q) * addChar (θ * (tupleProd C (restr C q) : ℝ))) :=
    sum_aux_eq hlaw C (fun r => b r * addChar (θ * (tupleProd C r : ℝ)))
  unfold multiplier
  calc ∑ r : AuxList big C,
        ((auxWeight big C r : ℝ) : ℂ) * b r * addChar (θ * (tupleProd C r : ℝ))
      = ∑ r : AuxList big C,
          (auxWeight big C r : ℂ) * (b r * addChar (θ * (tupleProd C r : ℝ))) :=
        Finset.sum_congr rfl fun r _ => mul_assoc _ _ _
    _ = ∑ q : LabelList big J 0, (idealWeight big J 0 q : ℂ) *
          (b (restr C q) * addChar (θ * (tupleProd C (restr C q) : ℝ))) := h
    _ = ∑ p : LabelList big J 0, (idealWeight big J 0 p : ℂ) *
          (b (restr C p) * addChar (θ * (sp C p : ℝ))) :=
        Finset.sum_congr rfl fun p _ => by rw [tupleProd_restr]

/-- **The bilinear form of two independent tuples on disjoint slot sets as an integral over one
random label list.** -/
theorem phaseForm_eq_sum (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    {A Bs : B → Finset (Fin J)} (hdisj : Disjoint (slotSet 0 A) (slotSet 0 Bs))
    (F : AuxList big Bs → ℂ) (G : AuxList big A → ℂ) (α ζ : ℝ) :
    phaseForm big A Bs F G α ζ =
      ∑ p : LabelList big J 0, (idealWeight big J 0 p : ℂ) *
        (F (restr Bs p) * G (restr A p) * dilPhase ζ α (sp A p * sp Bs p)) := by
  -- the two tuples as restrictions of two independent lists
  have h1 : phaseForm big A Bs F G α ζ =
      ∑ xA : AuxList big A, (auxWeight big A xA : ℂ) *
        ∑ xB : AuxList big Bs, (auxWeight big Bs xB : ℂ) *
          (F xB * G xA * dilPhase ζ α (tupleProd A xA * tupleProd Bs xB)) := by
    unfold phaseForm
    refine Finset.sum_congr rfl fun xA _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun xB _ => ?_
    rw [Complex.ofReal_mul]
    ring
  have h2 : ∀ xA : AuxList big A,
      ∑ xB : AuxList big Bs, (auxWeight big Bs xB : ℂ) *
          (F xB * G xA * dilPhase ζ α (tupleProd A xA * tupleProd Bs xB)) =
        ∑ q' : LabelList big J 0, (idealWeight big J 0 q' : ℂ) *
          (F (restr Bs q') * G xA * dilPhase ζ α (tupleProd A xA * sp Bs q')) := by
    intro xA
    have h : ∑ xB : AuxList big Bs, (auxWeight big Bs xB : ℂ) *
          (F xB * G xA * dilPhase ζ α (tupleProd A xA * tupleProd Bs xB)) =
        ∑ q' : LabelList big J 0, (idealWeight big J 0 q' : ℂ) *
          (F (restr Bs q') * G xA *
            dilPhase ζ α (tupleProd A xA * tupleProd Bs (restr Bs q'))) :=
      sum_aux_eq hlaw Bs
        (fun xB => F xB * G xA * dilPhase ζ α (tupleProd A xA * tupleProd Bs xB))
    refine h.trans (Finset.sum_congr rfl fun q' _ => ?_)
    rw [tupleProd_restr]
  have h3 : ∑ xA : AuxList big A, (auxWeight big A xA : ℂ) *
        ∑ q' : LabelList big J 0, (idealWeight big J 0 q' : ℂ) *
          (F (restr Bs q') * G xA * dilPhase ζ α (tupleProd A xA * sp Bs q')) =
      ∑ q : LabelList big J 0, (idealWeight big J 0 q : ℂ) *
        ∑ q' : LabelList big J 0, (idealWeight big J 0 q' : ℂ) *
          (F (restr Bs q') * G (restr A q) * dilPhase ζ α (sp A q * sp Bs q')) := by
    have h : ∑ xA : AuxList big A, (auxWeight big A xA : ℂ) *
          ∑ q' : LabelList big J 0, (idealWeight big J 0 q' : ℂ) *
            (F (restr Bs q') * G xA * dilPhase ζ α (tupleProd A xA * sp Bs q')) =
        ∑ q : LabelList big J 0, (idealWeight big J 0 q : ℂ) *
          ∑ q' : LabelList big J 0, (idealWeight big J 0 q' : ℂ) *
            (F (restr Bs q') * G (restr A q) *
              dilPhase ζ α (tupleProd A (restr A q) * sp Bs q')) :=
      sum_aux_eq hlaw A
        (fun xA => ∑ q' : LabelList big J 0, (idealWeight big J 0 q' : ℂ) *
          (F (restr Bs q') * G xA * dilPhase ζ α (tupleProd A xA * sp Bs q')))
    refine h.trans (Finset.sum_congr rfl fun q _ => ?_)
    rw [tupleProd_restr]
  -- the two lists are one list
  have hmix : ∀ q q' : LabelList big J 0,
      F (restr Bs q') * G (restr A q) * dilPhase ζ α (sp A q * sp Bs q') =
        F (restr Bs (mix (slotSet 0 Bs) q q')) * G (restr A (mix (slotSet 0 Bs) q q')) *
          dilPhase ζ α (sp A (mix (slotSet 0 Bs) q q') * sp Bs (mix (slotSet 0 Bs) q q')) := by
    intro q q'
    have e1 : restr Bs (mix (slotSet 0 Bs) q q') = restr Bs q' := by
      funext g i
      exact mix_of_mem q q' (inl_mem_slotSet.mpr i.2)
    have e2 : restr A (mix (slotSet 0 Bs) q q') = restr A q := by
      funext g i
      exact mix_of_notMem q q' (Finset.disjoint_left.mp hdisj (inl_mem_slotSet.mpr i.2))
    rw [e1, e2, sp_mix_of_disjoint hdisj q q', sp_mix_of_subset (Finset.Subset.refl _) q q']
  have havg : ∑ q : LabelList big J 0, (idealWeight big J 0 q : ℂ) *
        avg big J 0 (slotSet 0 Bs)
          (fun p => F (restr Bs p) * G (restr A p) * dilPhase ζ α (sp A p * sp Bs p)) q =
      ∑ p : LabelList big J 0, (idealWeight big J 0 p : ℂ) *
        (F (restr Bs p) * G (restr A p) * dilPhase ζ α (sp A p * sp Bs p)) :=
    sum_avg hlaw (slotSet 0 Bs)
      (fun p => F (restr Bs p) * G (restr A p) * dilPhase ζ α (sp A p * sp Bs p))
  calc phaseForm big A Bs F G α ζ
      = ∑ xA : AuxList big A, (auxWeight big A xA : ℂ) *
          ∑ xB : AuxList big Bs, (auxWeight big Bs xB : ℂ) *
            (F xB * G xA * dilPhase ζ α (tupleProd A xA * tupleProd Bs xB)) := h1
    _ = ∑ xA : AuxList big A, (auxWeight big A xA : ℂ) *
          ∑ q' : LabelList big J 0, (idealWeight big J 0 q' : ℂ) *
            (F (restr Bs q') * G xA * dilPhase ζ α (tupleProd A xA * sp Bs q')) :=
        Finset.sum_congr rfl fun xA _ => by rw [h2 xA]
    _ = ∑ q : LabelList big J 0, (idealWeight big J 0 q : ℂ) *
          ∑ q' : LabelList big J 0, (idealWeight big J 0 q' : ℂ) *
            (F (restr Bs q') * G (restr A q) * dilPhase ζ α (sp A q * sp Bs q')) := h3
    _ = ∑ q : LabelList big J 0, (idealWeight big J 0 q : ℂ) *
          avg big J 0 (slotSet 0 Bs)
            (fun p => F (restr Bs p) * G (restr A p) * dilPhase ζ α (sp A p * sp Bs p)) q := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [avg_apply]
        refine congrArg (fun t => (idealWeight big J 0 q : ℂ) * t) ?_
        exact Finset.sum_congr rfl fun q' _ => by rw [hmix q q']
    _ = ∑ p : LabelList big J 0, (idealWeight big J 0 p : ℂ) *
          (F (restr Bs p) * G (restr A p) * dilPhase ζ α (sp A p * sp Bs p)) := havg

/-- **The additive multiplier is the bilinear form of the two blocks** (`[P-06:0417–0422]`): for
tests `b₁`, `b₂` on the free labels depending only on the labels of the first and of the second
block, `𝔪(θ) = E b₂(X_B) b₁(X_A) e(θ P_A P_B)` for independent tuples `X_A`, `X_B` on the slots
of the two blocks. -/
theorem multiplier_eq_phaseForm (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (p₀ : LabelList big J 0) (blk : B → Bool) (C : B → Finset (Fin J))
    {b₁ b₂ : AuxList big C → ℂ}
    (h₁ : ∀ r r' : AuxList big C, (∀ g, blk g = true → r g = r' g) → b₁ r = b₁ r')
    (h₂ : ∀ r r' : AuxList big C, (∀ g, blk g = false → r g = r' g) → b₂ r = b₂ r') (θ : ℝ) :
    multiplier big C (fun r => b₁ r * b₂ r) θ =
      phaseForm big (restrictBlock blk true C) (restrictBlock blk false C)
        (blockRestrict blk false C p₀ b₂) (blockRestrict blk true C p₀ b₁) θ 0 := by
  rw [multiplier_eq_sum hlaw, phaseForm_eq_sum hlaw (disjoint_slotSet_restrict blk C)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [blockRestrict_restr p₀ h₂ p, blockRestrict_restr p₀ h₁ p, ← sp_split blk C p,
    dilPhase_zero_eq_addChar]
  ring

/-! ### Sizes of the block products -/

omit [DecidableEq B] in
/-- A free label of the block `b` is at most the product of the free labels of the block. -/
theorem label_le_blockAuxProd (hbig : ∀ g, ∀ p ∈ big g, 0 < p) (blk : B → Bool) {b : Bool}
    (C : B → Finset (Fin J)) (r : AuxList big C) {g : B} (hg : blk g = b)
    (i : {i : Fin J // i ∈ C g}) : (r g i : ℕ) ≤ blockAuxProd blk b C r := by
  have hpos : 0 < blockAuxProd blk b C r := by
    unfold blockAuxProd
    refine Finset.prod_pos fun g' _ => ?_
    by_cases hg' : blk g' = b
    · rw [if_pos hg']
      exact Finset.prod_pos fun i' _ => hbig g' (r g' i') (r g' i').2
    · rw [if_neg hg']
      exact Nat.one_pos
  refine Nat.le_of_dvd hpos ?_
  have h1 : (r g i : ℕ) ∣ ∏ i' : {i : Fin J // i ∈ C g}, (r g i' : ℕ) :=
    Finset.dvd_prod_of_mem (fun i' : {i : Fin J // i ∈ C g} => (r g i' : ℕ)) (Finset.mem_univ i)
  have h2 : (if blk g = b then ∏ i' : {i : Fin J // i ∈ C g}, (r g i' : ℕ) else 1) ∣
      blockAuxProd blk b C r :=
    Finset.dvd_prod_of_mem
      (fun g' : B => if blk g' = b then ∏ i' : {i : Fin J // i ∈ C g'}, (r g' i' : ℕ) else 1)
      (Finset.mem_univ g)
  rw [if_pos hg] at h2
  exact h1.trans h2

omit [DecidableEq B] in
/-- The product of all the free labels is the product of the two block products. -/
theorem tupleProd_eq_blockAuxProd_mul (blk : B → Bool) (C : B → Finset (Fin J))
    (r : AuxList big C) :
    tupleProd C r = blockAuxProd blk true C r * blockAuxProd blk false C r := by
  unfold tupleProd blockAuxProd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun g _ => ?_
  by_cases hb : blk g = true
  · have hb' : ¬ blk g = false := by
      rw [hb]
      decide
    rw [if_pos hb, if_neg hb', mul_one]
  · have hb' : blk g = false := Bool.eq_false_of_not_eq_true hb
    rw [if_neg hb, if_pos hb', one_mul]

end Collapse

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
