module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction.Rows
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The comparison estimate applied to one comparison term

Source: `verification/stage7-sources/S-03.tex`, lines 557–580 (`[S-03:0557–0580]`).

"Condition on all shared first-`J` labels outside `A ∪ B`, and write `C` for their product. …
The fixed shared product contributes `C^{iζ}`, of modulus one, and changes the additive frequency
to `α = Θ C`. Lemma 4.3 therefore matches the comparison term before its sign to `R(F_S, H_{T'})`
with error at most `L^{-A₀} ‖F_S‖₂ ‖H_{T'}‖₂`. To justify this bound after conditioning, apply the
lemma to the two conditional tests, average its error over the shared labels, and use
Cauchy–Schwarz."

* `comparisonDefect_eq` — the left side of (eq:ideal-comparison) for the conditional tests
  `x_B ↦ G₁(p with x_B)`, `x_A ↦ H₁(p with x_A)`, written with sums over label lists;
* `norm_wInner_comp_le` — for a target function `H₁` which does not depend on the labels in the
  slots of `B`, and any source function `G₁`:
  `|⟨G₁, E_A (raw phase · H₁) - (comparison operator) H₁⟩| ≤ ε ‖G₁‖ ‖H₁‖`, if the comparison
  defect of the pair `(A, B)` is at most `ε ‖f‖₂ ‖g‖₂` for all tests and all `α`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction

open scoped BigOperators ComplexConjugate

noncomputable section

variable {B : Type} [Fintype B] [DecidableEq B] {big : B → Finset ℕ} {J ℓ : ℕ}

/-- Two products of labels in disjoint sets of slots are independent. -/
theorem sum_split (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    {A Bs : B → Finset (Fin J)} (hAB : Disjoint (slotSet ℓ A) (slotSet ℓ Bs))
    (Ψ : ℕ → ℕ → ℂ) :
    ∑ d : LabelList big J ℓ, (idealWeight big J ℓ d : ℂ) * Ψ (sp A d) (sp Bs d) =
      ∑ dA : LabelList big J ℓ, (idealWeight big J ℓ dA : ℂ) *
        ∑ dB : LabelList big J ℓ, (idealWeight big J ℓ dB : ℂ) * Ψ (sp A dA) (sp Bs dB) := by
  have h := sum_swap (slotSet ℓ A)
    (fun (a : LabelList big J ℓ) (_ : LabelList big J ℓ) => Ψ (sp A a) (sp Bs a))
  simp only [sp_mix_of_subset (Finset.Subset.refl (slotSet ℓ A)),
    sp_mix_of_disjoint hAB.symm] at h
  calc ∑ d : LabelList big J ℓ, (idealWeight big J ℓ d : ℂ) * Ψ (sp A d) (sp Bs d)
      = ∑ a : LabelList big J ℓ, ∑ b : LabelList big J ℓ, (idealWeight big J ℓ a : ℂ) *
          ((idealWeight big J ℓ b : ℂ) * Ψ (sp A a) (sp Bs a)) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.mul_sum, ← Finset.sum_mul, sum_idealWeight_cast hlaw, one_mul]
    _ = ∑ a : LabelList big J ℓ, ∑ b : LabelList big J ℓ, (idealWeight big J ℓ a : ℂ) *
          ((idealWeight big J ℓ b : ℂ) * Ψ (sp A b) (sp Bs a)) := h.symm
    _ = ∑ b : LabelList big J ℓ, ∑ a : LabelList big J ℓ, (idealWeight big J ℓ a : ℂ) *
          ((idealWeight big J ℓ b : ℂ) * Ψ (sp A b) (sp Bs a)) := Finset.sum_comm
    _ = ∑ dA : LabelList big J ℓ, (idealWeight big J ℓ dA : ℂ) *
          ∑ dB : LabelList big J ℓ, (idealWeight big J ℓ dB : ℂ) * Ψ (sp A dA) (sp Bs dB) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        ring

/-- Four independent tuples, as four independent label lists. -/
theorem sum_aux4_eq (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (Λ₁ Λ₂ Λ₃ Λ₄ : B → Finset (Fin J))
    (T : AuxList big Λ₁ → AuxList big Λ₂ → AuxList big Λ₃ → AuxList big Λ₄ → ℂ) :
    ∑ t₁ : AuxList big Λ₁, ∑ t₂ : AuxList big Λ₂, ∑ t₃ : AuxList big Λ₃,
        ∑ t₄ : AuxList big Λ₄,
          ((auxWeight big Λ₁ t₁ * auxWeight big Λ₂ t₂ * auxWeight big Λ₃ t₃ *
            auxWeight big Λ₄ t₄ : ℝ) : ℂ) * T t₁ t₂ t₃ t₄ =
      ∑ q₁ : LabelList big J ℓ, (idealWeight big J ℓ q₁ : ℂ) *
        ∑ q₂ : LabelList big J ℓ, (idealWeight big J ℓ q₂ : ℂ) *
          ∑ q₃ : LabelList big J ℓ, (idealWeight big J ℓ q₃ : ℂ) *
            ∑ q₄ : LabelList big J ℓ, (idealWeight big J ℓ q₄ : ℂ) *
              T (restr Λ₁ q₁) (restr Λ₂ q₂) (restr Λ₃ q₃) (restr Λ₄ q₄) := by
  have h4 : ∀ (t₁ : AuxList big Λ₁) (t₂ : AuxList big Λ₂) (t₃ : AuxList big Λ₃),
      ∑ t₄ : AuxList big Λ₄, (auxWeight big Λ₄ t₄ : ℂ) * T t₁ t₂ t₃ t₄ =
        ∑ q₄ : LabelList big J ℓ, (idealWeight big J ℓ q₄ : ℂ) * T t₁ t₂ t₃ (restr Λ₄ q₄) :=
    fun t₁ t₂ t₃ => sum_aux_eq hlaw Λ₄ (fun t₄ => T t₁ t₂ t₃ t₄)
  have h3 : ∀ (t₁ : AuxList big Λ₁) (t₂ : AuxList big Λ₂),
      ∑ t₃ : AuxList big Λ₃, (auxWeight big Λ₃ t₃ : ℂ) *
          ∑ q₄ : LabelList big J ℓ, (idealWeight big J ℓ q₄ : ℂ) * T t₁ t₂ t₃ (restr Λ₄ q₄) =
        ∑ q₃ : LabelList big J ℓ, (idealWeight big J ℓ q₃ : ℂ) *
          ∑ q₄ : LabelList big J ℓ, (idealWeight big J ℓ q₄ : ℂ) *
            T t₁ t₂ (restr Λ₃ q₃) (restr Λ₄ q₄) :=
    fun t₁ t₂ => sum_aux_eq hlaw Λ₃ (fun t₃ =>
      ∑ q₄ : LabelList big J ℓ, (idealWeight big J ℓ q₄ : ℂ) * T t₁ t₂ t₃ (restr Λ₄ q₄))
  have h2 : ∀ t₁ : AuxList big Λ₁,
      ∑ t₂ : AuxList big Λ₂, (auxWeight big Λ₂ t₂ : ℂ) *
          ∑ q₃ : LabelList big J ℓ, (idealWeight big J ℓ q₃ : ℂ) *
            ∑ q₄ : LabelList big J ℓ, (idealWeight big J ℓ q₄ : ℂ) *
              T t₁ t₂ (restr Λ₃ q₃) (restr Λ₄ q₄) =
        ∑ q₂ : LabelList big J ℓ, (idealWeight big J ℓ q₂ : ℂ) *
          ∑ q₃ : LabelList big J ℓ, (idealWeight big J ℓ q₃ : ℂ) *
            ∑ q₄ : LabelList big J ℓ, (idealWeight big J ℓ q₄ : ℂ) *
              T t₁ (restr Λ₂ q₂) (restr Λ₃ q₃) (restr Λ₄ q₄) :=
    fun t₁ => sum_aux_eq hlaw Λ₂ (fun t₂ =>
      ∑ q₃ : LabelList big J ℓ, (idealWeight big J ℓ q₃ : ℂ) *
        ∑ q₄ : LabelList big J ℓ, (idealWeight big J ℓ q₄ : ℂ) *
          T t₁ t₂ (restr Λ₃ q₃) (restr Λ₄ q₄))
  have h1 := sum_aux_eq (ℓ := ℓ) hlaw Λ₁ (fun t₁ =>
    ∑ q₂ : LabelList big J ℓ, (idealWeight big J ℓ q₂ : ℂ) *
      ∑ q₃ : LabelList big J ℓ, (idealWeight big J ℓ q₃ : ℂ) *
        ∑ q₄ : LabelList big J ℓ, (idealWeight big J ℓ q₄ : ℂ) *
          T t₁ (restr Λ₂ q₂) (restr Λ₃ q₃) (restr Λ₄ q₄))
  calc ∑ t₁ : AuxList big Λ₁, ∑ t₂ : AuxList big Λ₂, ∑ t₃ : AuxList big Λ₃,
        ∑ t₄ : AuxList big Λ₄,
          ((auxWeight big Λ₁ t₁ * auxWeight big Λ₂ t₂ * auxWeight big Λ₃ t₃ *
            auxWeight big Λ₄ t₄ : ℝ) : ℂ) * T t₁ t₂ t₃ t₄
      = ∑ t₁ : AuxList big Λ₁, (auxWeight big Λ₁ t₁ : ℂ) *
          ∑ t₂ : AuxList big Λ₂, (auxWeight big Λ₂ t₂ : ℂ) *
            ∑ t₃ : AuxList big Λ₃, (auxWeight big Λ₃ t₃ : ℂ) *
              ∑ t₄ : AuxList big Λ₄, (auxWeight big Λ₄ t₄ : ℂ) * T t₁ t₂ t₃ t₄ := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun t₁ _ => Finset.sum_congr rfl fun t₂ _ =>
          Finset.sum_congr rfl fun t₃ _ => Finset.sum_congr rfl fun t₄ _ => ?_
        push_cast
        ring
    _ = ∑ t₁ : AuxList big Λ₁, (auxWeight big Λ₁ t₁ : ℂ) *
          ∑ t₂ : AuxList big Λ₂, (auxWeight big Λ₂ t₂ : ℂ) *
            ∑ t₃ : AuxList big Λ₃, (auxWeight big Λ₃ t₃ : ℂ) *
              ∑ q₄ : LabelList big J ℓ, (idealWeight big J ℓ q₄ : ℂ) *
                T t₁ t₂ t₃ (restr Λ₄ q₄) := by
        simp only [h4]
    _ = ∑ t₁ : AuxList big Λ₁, (auxWeight big Λ₁ t₁ : ℂ) *
          ∑ t₂ : AuxList big Λ₂, (auxWeight big Λ₂ t₂ : ℂ) *
            ∑ q₃ : LabelList big J ℓ, (idealWeight big J ℓ q₃ : ℂ) *
              ∑ q₄ : LabelList big J ℓ, (idealWeight big J ℓ q₄ : ℂ) *
                T t₁ t₂ (restr Λ₃ q₃) (restr Λ₄ q₄) := by
        simp only [h3]
    _ = ∑ t₁ : AuxList big Λ₁, (auxWeight big Λ₁ t₁ : ℂ) *
          ∑ q₂ : LabelList big J ℓ, (idealWeight big J ℓ q₂ : ℂ) *
            ∑ q₃ : LabelList big J ℓ, (idealWeight big J ℓ q₃ : ℂ) *
              ∑ q₄ : LabelList big J ℓ, (idealWeight big J ℓ q₄ : ℂ) *
                T t₁ (restr Λ₂ q₂) (restr Λ₃ q₃) (restr Λ₄ q₄) := by
        simp only [h2]
    _ = _ := h1

/-- `E_{D_A} E_{D_B} c (φ - K(D_A, D_B)) = c (φ - E_{D_A} E_{D_B} K(D_A, D_B))`. -/
theorem sum_two_sub (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1) (c φ : ℂ)
    (K : LabelList big J ℓ → LabelList big J ℓ → ℂ) :
    ∑ dA : LabelList big J ℓ, (idealWeight big J ℓ dA : ℂ) *
        ∑ dB : LabelList big J ℓ, (idealWeight big J ℓ dB : ℂ) * (c * (φ - K dA dB)) =
      c * (φ - ∑ dA : LabelList big J ℓ, (idealWeight big J ℓ dA : ℂ) *
        ∑ dB : LabelList big J ℓ, (idealWeight big J ℓ dB : ℂ) * K dA dB) := by
  have h1 : ∀ dA : LabelList big J ℓ,
      ∑ dB : LabelList big J ℓ, (idealWeight big J ℓ dB : ℂ) * (c * (φ - K dA dB)) =
        c * φ - c * ∑ dB : LabelList big J ℓ, (idealWeight big J ℓ dB : ℂ) * K dA dB := by
    intro dA
    have h0 : ∀ dB : LabelList big J ℓ,
        (idealWeight big J ℓ dB : ℂ) * (c * (φ - K dA dB)) =
          (idealWeight big J ℓ dB : ℂ) * (c * φ) - c * ((idealWeight big J ℓ dB : ℂ) * K dA dB) :=
      fun dB => by ring
    rw [Finset.sum_congr rfl fun dB _ => h0 dB, Finset.sum_sub_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, sum_idealWeight_cast hlaw, one_mul]
  calc ∑ dA : LabelList big J ℓ, (idealWeight big J ℓ dA : ℂ) *
        ∑ dB : LabelList big J ℓ, (idealWeight big J ℓ dB : ℂ) * (c * (φ - K dA dB))
      = ∑ dA : LabelList big J ℓ, ((idealWeight big J ℓ dA : ℂ) * (c * φ) -
          c * ((idealWeight big J ℓ dA : ℂ) *
            ∑ dB : LabelList big J ℓ, (idealWeight big J ℓ dB : ℂ) * K dA dB)) := by
        refine Finset.sum_congr rfl fun dA _ => ?_
        rw [h1 dA]
        ring
    _ = (∑ dA : LabelList big J ℓ, (idealWeight big J ℓ dA : ℂ)) * (c * φ) -
          c * ∑ dA : LabelList big J ℓ, (idealWeight big J ℓ dA : ℂ) *
            ∑ dB : LabelList big J ℓ, (idealWeight big J ℓ dB : ℂ) * K dA dB := by
        rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    _ = c * (φ - ∑ dA : LabelList big J ℓ, (idealWeight big J ℓ dA : ℂ) *
          ∑ dB : LabelList big J ℓ, (idealWeight big J ℓ dB : ℂ) * K dA dB) := by
        rw [sum_idealWeight_cast hlaw, one_mul]
        ring

/-- **The left side of (eq:ideal-comparison) for conditional tests**, with sums over label
lists: the tests are `x_B ↦ G₁(p with x_B in the slots of B)` and
`x_A ↦ H₁(p with x_A in the slots of A)`. -/
theorem comparisonDefect_eq (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    {A Bs : B → Finset (Fin J)} (hAB : Disjoint (slotSet ℓ A) (slotSet ℓ Bs)) (Q h ξ : ℝ)
    (G₁ H₁ : LabelList big J ℓ → ℂ) (p : LabelList big J ℓ) (α ζ : ℝ) :
    comparisonDefect big A Bs Q h ξ (fun xB => G₁ (ins Bs p xB)) (fun xA => H₁ (ins A p xA))
        α ζ =
      ∑ qA : LabelList big J ℓ, (idealWeight big J ℓ qA : ℂ) *
        ∑ qB : LabelList big J ℓ, (idealWeight big J ℓ qB : ℂ) *
          ((conj (G₁ (mix (slotSet ℓ Bs) p qB)) * H₁ (mix (slotSet ℓ A) p qA)) *
            (dilPhase ζ α (sp A qA * sp Bs qB) -
              kk big J ℓ A Bs Q h ξ ζ α (sp A qA) (sp Bs qB))) := by
  have h0 : comparisonDefect big A Bs Q h ξ (fun xB => G₁ (ins Bs p xB))
        (fun xA => H₁ (ins A p xA)) α ζ =
      ∑ xA : AuxList big A, ∑ xB : AuxList big Bs, ∑ dA : AuxList big A,
        ∑ dB : AuxList big Bs,
          ((auxWeight big A xA * auxWeight big Bs xB * auxWeight big A dA *
            auxWeight big Bs dB : ℝ) : ℂ) *
            ((conj (G₁ (ins Bs p xB)) * H₁ (ins A p xA)) *
              (dilPhase ζ α (tupleProd A xA * tupleProd Bs xB) -
                cellKernel big A Q h ξ (tupleProd A dA) (tupleProd A xA) *
                  cellKernel big Bs Q h ξ (tupleProd Bs dB) (tupleProd Bs xB) *
                  dilPhase ζ α (tupleProd A dA * tupleProd Bs dB))) :=
    Finset.sum_congr rfl fun xA _ => Finset.sum_congr rfl fun xB _ =>
      Finset.sum_congr rfl fun dA _ => Finset.sum_congr rfl fun dB _ => mul_assoc _ _ _
  have h1 := sum_aux4_eq (ℓ := ℓ) hlaw A Bs A Bs
    (fun xA xB dA dB => (conj (G₁ (ins Bs p xB)) * H₁ (ins A p xA)) *
      (dilPhase ζ α (tupleProd A xA * tupleProd Bs xB) -
        cellKernel big A Q h ξ (tupleProd A dA) (tupleProd A xA) *
          cellKernel big Bs Q h ξ (tupleProd Bs dB) (tupleProd Bs xB) *
          dilPhase ζ α (tupleProd A dA * tupleProd Bs dB)))
  simp only [← mix_slotSet_eq_ins, tupleProd_restr] at h1
  rw [h0, h1]
  refine Finset.sum_congr rfl fun qA _ => congrArg _ (Finset.sum_congr rfl fun qB _ =>
    congrArg _ ?_)
  have hk : kk big J ℓ A Bs Q h ξ ζ α (sp A qA) (sp Bs qB) =
      ∑ dA : LabelList big J ℓ, (idealWeight big J ℓ dA : ℂ) *
        ∑ dB : LabelList big J ℓ, (idealWeight big J ℓ dB : ℂ) *
          (cellKernel big A Q h ξ (sp A dA) (sp A qA) *
            cellKernel big Bs Q h ξ (sp Bs dB) (sp Bs qB) *
            dilPhase ζ α (sp A dA * sp Bs dB)) :=
    sum_split hlaw hAB (fun a b => cellKernel big A Q h ξ a (sp A qA) *
      cellKernel big Bs Q h ξ b (sp Bs qB) * dilPhase ζ α (a * b))
  rw [hk]
  exact sum_two_sub hlaw _ _ (fun dA dB => cellKernel big A Q h ξ (sp A dA) (sp A qA) *
    cellKernel big Bs Q h ξ (sp Bs dB) (sp Bs qB) * dilPhase ζ α (sp A dA * sp Bs dB))

/-- The `L²` norm of a conditional test. -/
theorem tupleNorm_ins (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (Λ : B → Finset (Fin J)) (G : LabelList big J ℓ → ℂ) (p : LabelList big J ℓ) :
    tupleNorm big Λ (fun t => G (ins Λ p t)) =
      Real.sqrt (∑ q : LabelList big J ℓ,
        idealWeight big J ℓ q * ‖G (mix (slotSet ℓ Λ) p q)‖ ^ 2) := by
  have h := sum_aux_eq (ℓ := ℓ) hlaw Λ (fun t => ((‖G (ins Λ p t)‖ ^ 2 : ℝ) : ℂ))
  have h' : ∑ t : AuxList big Λ, auxWeight big Λ t * ‖G (ins Λ p t)‖ ^ 2 =
      ∑ q : LabelList big J ℓ, idealWeight big J ℓ q * ‖G (ins Λ p (restr Λ q))‖ ^ 2 := by
    exact_mod_cast h
  show Real.sqrt (∑ t : AuxList big Λ, auxWeight big Λ t * ‖G (ins Λ p t)‖ ^ 2) = _
  rw [h']
  simp only [mix_slotSet_eq_ins]

/-- Averaging the raw phase times `H₁` over the slots of `A`. -/
theorem avg_rawMul_eq (blk : B → Bool) (C : B → Finset (Fin J)) (ζ Θ : ℝ)
    (H₁ : LabelList big J ℓ → ℂ) (p : LabelList big J ℓ) :
    avg big J ℓ (slotSet ℓ (restrictBlock blk true C)) (rawMul big J ℓ ζ Θ H₁) p =
      ((sharedProd C p : ℕ) : ℂ) ^ ((ζ : ℂ) * Complex.I) *
        ∑ q : LabelList big J ℓ, (idealWeight big J ℓ q : ℂ) *
          (H₁ (mix (slotSet ℓ (restrictBlock blk true C)) p q) *
            dilPhase ζ (Θ * ((sharedProd C p : ℕ) : ℝ))
              (sp (restrictBlock blk true C) q * sp (restrictBlock blk false C) p)) := by
  have hsh : ∀ (g : B) (i : Fin J),
      (g, (Sum.inl i : Slot J ℓ)) ∈ slotSet ℓ (restrictBlock blk true C) → i ∈ C g :=
    fun g i hh => mem_of_mem_restrictBlock (inl_mem_slotSet.mp hh)
  rw [avg_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hfp : fullProd (mix (slotSet ℓ (restrictBlock blk true C)) p q) =
      sharedProd C p * (sp (restrictBlock blk true C) q * sp (restrictBlock blk false C) p) := by
    rw [fullProd_eq C, sharedProd_mix hsh p q, sp_split blk C,
      sp_mix_of_subset (Finset.Subset.refl _) p q,
      sp_mix_of_disjoint (disjoint_slotSet_restrict (ℓ := ℓ) blk C).symm p q]
  show (idealWeight big J ℓ q : ℂ) *
      (dilPhase ζ Θ (fullProd (mix (slotSet ℓ (restrictBlock blk true C)) p q)) *
        H₁ (mix (slotSet ℓ (restrictBlock blk true C)) p q)) = _
  rw [hfp, dilPhase_mul]
  ring

/-- **One comparison term** [S-03:0557–0580]: if the comparison defect of the slot sets
`(A, B)` of `C` is at most `ε ‖f‖₂ ‖g‖₂` for all tests and all `α`, then for every `G₁` and
every `H₁` which does not depend on the labels in the slots of `B`,
`|⟨G₁, E_A (raw phase · H₁) - (comparison operator) H₁⟩| ≤ ε ‖G₁‖ ‖H₁‖`. -/
theorem norm_wInner_comp_le (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (hnn : ∀ p : LabelList big J ℓ, 0 ≤ idealWeight big J ℓ p) (blk : B → Bool) (Q h ξ : ℝ)
    (C : B → Finset (Fin J)) (ζ Θ ε : ℝ) (hε : 0 ≤ ε)
    (hdef : ∀ (f : AuxList big (restrictBlock blk false C) → ℂ)
      (g : AuxList big (restrictBlock blk true C) → ℂ) (α : ℝ),
      ‖comparisonDefect big (restrictBlock blk true C) (restrictBlock blk false C) Q h ξ f g
          α ζ‖ ≤
        ε * (tupleNorm big (restrictBlock blk false C) f *
          tupleNorm big (restrictBlock blk true C) g))
    (G₁ H₁ : LabelList big J ℓ → ℂ)
    (hH : Indep (slotSet ℓ (restrictBlock blk false C)) H₁) :
    ‖wInner (idealWeight big J ℓ) G₁
        (fun p => avg big J ℓ (slotSet ℓ (restrictBlock blk true C)) (rawMul big J ℓ ζ Θ H₁) p -
          compOp big J ℓ blk Q h ξ C ζ Θ H₁ p)‖ ≤
      ε * (wNorm (idealWeight big J ℓ) G₁ * wNorm (idealWeight big J ℓ) H₁) := by
  have hAB : Disjoint (slotSet ℓ (restrictBlock blk true C))
      (slotSet ℓ (restrictBlock blk false C)) := disjoint_slotSet_restrict blk C
  have hshB : ∀ (g : B) (i : Fin J),
      (g, (Sum.inl i : Slot J ℓ)) ∈ slotSet ℓ (restrictBlock blk false C) → i ∈ C g :=
    fun g i hh => mem_of_mem_restrictBlock (inl_mem_slotSet.mp hh)
  obtain ⟨W, hWdef⟩ : ∃ W : LabelList big J ℓ → ℂ, W = fun p =>
      avg big J ℓ (slotSet ℓ (restrictBlock blk true C)) (rawMul big J ℓ ζ Θ H₁) p -
        compOp big J ℓ blk Q h ξ C ζ Θ H₁ p := ⟨_, rfl⟩
  rw [← hWdef]
  -- the difference in closed form
  have hW : ∀ p : LabelList big J ℓ, W p =
      ((sharedProd C p : ℕ) : ℂ) ^ ((ζ : ℂ) * Complex.I) *
        ∑ q : LabelList big J ℓ, (idealWeight big J ℓ q : ℂ) *
          (H₁ (mix (slotSet ℓ (restrictBlock blk true C)) p q) *
            (dilPhase ζ (Θ * ((sharedProd C p : ℕ) : ℝ))
                (sp (restrictBlock blk true C) q * sp (restrictBlock blk false C) p) -
              kk big J ℓ (restrictBlock blk true C) (restrictBlock blk false C) Q h ξ ζ
                (Θ * ((sharedProd C p : ℕ) : ℝ)) (sp (restrictBlock blk true C) q)
                (sp (restrictBlock blk false C) p))) := by
    intro p
    rw [hWdef]
    show avg big J ℓ (slotSet ℓ (restrictBlock blk true C)) (rawMul big J ℓ ζ Θ H₁) p -
      compOp big J ℓ blk Q h ξ C ζ Θ H₁ p = _
    rw [avg_rawMul_eq blk C ζ Θ H₁ p]
    unfold compOp
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  -- resampling the source labels in the slots of `B`
  have hWm : ∀ p qB : LabelList big J ℓ,
      W (mix (slotSet ℓ (restrictBlock blk false C)) p qB) =
        ((sharedProd C p : ℕ) : ℂ) ^ ((ζ : ℂ) * Complex.I) *
          ∑ qA : LabelList big J ℓ, (idealWeight big J ℓ qA : ℂ) *
            (H₁ (mix (slotSet ℓ (restrictBlock blk true C)) p qA) *
              (dilPhase ζ (Θ * ((sharedProd C p : ℕ) : ℝ))
                  (sp (restrictBlock blk true C) qA * sp (restrictBlock blk false C) qB) -
                kk big J ℓ (restrictBlock blk true C) (restrictBlock blk false C) Q h ξ ζ
                  (Θ * ((sharedProd C p : ℕ) : ℝ)) (sp (restrictBlock blk true C) qA)
                  (sp (restrictBlock blk false C) qB))) := by
    intro p qB
    rw [hW (mix (slotSet ℓ (restrictBlock blk false C)) p qB), sharedProd_mix hshB p qB,
      sp_mix_of_subset (Finset.Subset.refl (slotSet ℓ (restrictBlock blk false C))) p qB]
    congr 1
    refine Finset.sum_congr rfl fun qA _ => ?_
    rw [mix_mix_comm hAB p qB qA,
      hH (mix (slotSet ℓ (restrictBlock blk true C)) p qA) qB]
  have hΞ : ∀ p : LabelList big J ℓ,
      avg big J ℓ (slotSet ℓ (restrictBlock blk false C)) (fun p' => conj (G₁ p') * W p') p =
        ((sharedProd C p : ℕ) : ℂ) ^ ((ζ : ℂ) * Complex.I) *
          comparisonDefect big (restrictBlock blk true C) (restrictBlock blk false C) Q h ξ
            (fun xB => G₁ (ins (restrictBlock blk false C) p xB))
            (fun xA => H₁ (ins (restrictBlock blk true C) p xA))
            (Θ * ((sharedProd C p : ℕ) : ℝ)) ζ := by
    intro p
    rw [comparisonDefect_eq hlaw hAB Q h ξ G₁ H₁ p (Θ * ((sharedProd C p : ℕ) : ℝ)) ζ,
      avg_apply]
    simp only [hWm, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun qA _ => Finset.sum_congr rfl fun qB _ => by ring
  have hpair : wInner (idealWeight big J ℓ) G₁ W =
      ∑ p : LabelList big J ℓ, (idealWeight big J ℓ p : ℂ) *
        (((sharedProd C p : ℕ) : ℂ) ^ ((ζ : ℂ) * Complex.I) *
          comparisonDefect big (restrictBlock blk true C) (restrictBlock blk false C) Q h ξ
            (fun xB => G₁ (ins (restrictBlock blk false C) p xB))
            (fun xA => H₁ (ins (restrictBlock blk true C) p xA))
            (Θ * ((sharedProd C p : ℕ) : ℝ)) ζ) := by
    have h1 : wInner (idealWeight big J ℓ) G₁ W =
        ∑ p : LabelList big J ℓ, (idealWeight big J ℓ p : ℂ) *
          avg big J ℓ (slotSet ℓ (restrictBlock blk false C))
            (fun p' => conj (G₁ p') * W p') p :=
      (sum_avg hlaw (slotSet ℓ (restrictBlock blk false C))
        (fun p' => conj (G₁ p') * W p')).symm
    rw [h1]
    exact Finset.sum_congr rfl fun p _ => by rw [hΞ p]
  have ha0 : ∀ p : LabelList big J ℓ, 0 ≤ ∑ q : LabelList big J ℓ,
      idealWeight big J ℓ q * ‖G₁ (mix (slotSet ℓ (restrictBlock blk false C)) p q)‖ ^ 2 :=
    fun p => Finset.sum_nonneg fun q _ => mul_nonneg (hnn q) (sq_nonneg _)
  have hb0 : ∀ p : LabelList big J ℓ, 0 ≤ ∑ q : LabelList big J ℓ,
      idealWeight big J ℓ q * ‖H₁ (mix (slotSet ℓ (restrictBlock blk true C)) p q)‖ ^ 2 :=
    fun p => Finset.sum_nonneg fun q _ => mul_nonneg (hnn q) (sq_nonneg _)
  rw [hpair]
  calc ‖∑ p : LabelList big J ℓ, (idealWeight big J ℓ p : ℂ) *
        (((sharedProd C p : ℕ) : ℂ) ^ ((ζ : ℂ) * Complex.I) *
          comparisonDefect big (restrictBlock blk true C) (restrictBlock blk false C) Q h ξ
            (fun xB => G₁ (ins (restrictBlock blk false C) p xB))
            (fun xA => H₁ (ins (restrictBlock blk true C) p xA))
            (Θ * ((sharedProd C p : ℕ) : ℝ)) ζ)‖
      ≤ ∑ p : LabelList big J ℓ, ‖(idealWeight big J ℓ p : ℂ) *
        (((sharedProd C p : ℕ) : ℂ) ^ ((ζ : ℂ) * Complex.I) *
          comparisonDefect big (restrictBlock blk true C) (restrictBlock blk false C) Q h ξ
            (fun xB => G₁ (ins (restrictBlock blk false C) p xB))
            (fun xA => H₁ (ins (restrictBlock blk true C) p xA))
            (Θ * ((sharedProd C p : ℕ) : ℝ)) ζ)‖ := norm_sum_le _ _
    _ ≤ ∑ p : LabelList big J ℓ, idealWeight big J ℓ p *
          (ε * (Real.sqrt (∑ q : LabelList big J ℓ, idealWeight big J ℓ q *
              ‖G₁ (mix (slotSet ℓ (restrictBlock blk false C)) p q)‖ ^ 2) *
            Real.sqrt (∑ q : LabelList big J ℓ, idealWeight big J ℓ q *
              ‖H₁ (mix (slotSet ℓ (restrictBlock blk true C)) p q)‖ ^ 2))) := by
        refine Finset.sum_le_sum fun p _ => ?_
        have hd := hdef (fun xB => G₁ (ins (restrictBlock blk false C) p xB))
          (fun xA => H₁ (ins (restrictBlock blk true C) p xA)) (Θ * ((sharedProd C p : ℕ) : ℝ))
        rw [tupleNorm_ins hlaw (restrictBlock blk false C) G₁ p,
          tupleNorm_ins hlaw (restrictBlock blk true C) H₁ p] at hd
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hnn p)]
        refine mul_le_mul_of_nonneg_left ?_ (hnn p)
        calc ‖((sharedProd C p : ℕ) : ℂ) ^ ((ζ : ℂ) * Complex.I)‖ *
              ‖comparisonDefect big (restrictBlock blk true C) (restrictBlock blk false C) Q h ξ
                (fun xB => G₁ (ins (restrictBlock blk false C) p xB))
                (fun xA => H₁ (ins (restrictBlock blk true C) p xA))
                (Θ * ((sharedProd C p : ℕ) : ℝ)) ζ‖
            ≤ 1 * (ε * (Real.sqrt (∑ q : LabelList big J ℓ, idealWeight big J ℓ q *
                ‖G₁ (mix (slotSet ℓ (restrictBlock blk false C)) p q)‖ ^ 2) *
              Real.sqrt (∑ q : LabelList big J ℓ, idealWeight big J ℓ q *
                ‖H₁ (mix (slotSet ℓ (restrictBlock blk true C)) p q)‖ ^ 2))) :=
              mul_le_mul (norm_natCast_cpow_le _ ζ) hd (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
    _ = ε * ∑ p : LabelList big J ℓ, idealWeight big J ℓ p *
          (Real.sqrt (∑ q : LabelList big J ℓ, idealWeight big J ℓ q *
              ‖G₁ (mix (slotSet ℓ (restrictBlock blk false C)) p q)‖ ^ 2) *
            Real.sqrt (∑ q : LabelList big J ℓ, idealWeight big J ℓ q *
              ‖H₁ (mix (slotSet ℓ (restrictBlock blk true C)) p q)‖ ^ 2)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun p _ => by ring
    _ ≤ ε * (Real.sqrt (∑ p : LabelList big J ℓ, idealWeight big J ℓ p *
            Real.sqrt (∑ q : LabelList big J ℓ, idealWeight big J ℓ q *
              ‖G₁ (mix (slotSet ℓ (restrictBlock blk false C)) p q)‖ ^ 2) ^ 2) *
          Real.sqrt (∑ p : LabelList big J ℓ, idealWeight big J ℓ p *
            Real.sqrt (∑ q : LabelList big J ℓ, idealWeight big J ℓ q *
              ‖H₁ (mix (slotSet ℓ (restrictBlock blk true C)) p q)‖ ^ 2) ^ 2)) :=
        mul_le_mul_of_nonneg_left
          (sum_weight_mul_le (idealWeight big J ℓ) hnn _ _ (fun _ => Real.sqrt_nonneg _)
            (fun _ => Real.sqrt_nonneg _)) hε
    _ = ε * (wNorm (idealWeight big J ℓ) G₁ * wNorm (idealWeight big J ℓ) H₁) := by
        have ha : ∀ p : LabelList big J ℓ,
            Real.sqrt (∑ q : LabelList big J ℓ, idealWeight big J ℓ q *
              ‖G₁ (mix (slotSet ℓ (restrictBlock blk false C)) p q)‖ ^ 2) ^ 2 =
            ∑ q : LabelList big J ℓ, idealWeight big J ℓ q *
              ‖G₁ (mix (slotSet ℓ (restrictBlock blk false C)) p q)‖ ^ 2 :=
          fun p => Real.sq_sqrt (ha0 p)
        have hb : ∀ p : LabelList big J ℓ,
            Real.sqrt (∑ q : LabelList big J ℓ, idealWeight big J ℓ q *
              ‖H₁ (mix (slotSet ℓ (restrictBlock blk true C)) p q)‖ ^ 2) ^ 2 =
            ∑ q : LabelList big J ℓ, idealWeight big J ℓ q *
              ‖H₁ (mix (slotSet ℓ (restrictBlock blk true C)) p q)‖ ^ 2 :=
          fun p => Real.sq_sqrt (hb0 p)
        simp only [ha, hb]
        rw [sum_cond_sq hlaw (slotSet ℓ (restrictBlock blk false C)) G₁,
          sum_cond_sq hlaw (slotSet ℓ (restrictBlock blk true C)) H₁]
        rfl

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction
