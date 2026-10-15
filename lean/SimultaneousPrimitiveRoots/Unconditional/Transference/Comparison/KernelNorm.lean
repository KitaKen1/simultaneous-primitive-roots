module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Scales
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.FrameCells
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Kernel integration has norm at most `2`

Source: `verification/stage7-sources/S-03.tex`, lines 243–266 (`[S-03:0243–0266]`).

`kernelNorm_of_cell : CharacterCell → GramFrameBound → KernelNorm`.

* `Family.charSet Q` — the set `𝒞_Q` of [S-03:0184] as a finite set of pairs `(r, χ)`;
  `Family.primitiveCharSum_eq`, `Family.card_charSet` relate it to `primitiveCharSum` and
  `primitiveCharCount`.
* `Family.cellKernel_eq_frame`, `Family.cellKernel_eq_frame_conj` — `𝒦_Λ(D, X)` is the cell-wise
  frame kernel (`Frame.kernel`) of the family `χ(P_Λ)`, `χ ∈ 𝒞_Q`, and, with the two variables
  exchanged, of the conjugate family: "the adjoint and transpose have the same bound".
* `Family.gram_entry_le` — the off-diagonal Gram entries on a cell, from
  (eq:ideal-character-cell).
* `kernelNorm_of_cell` — `Frame.wNormSq_op_le` with the character precision `D_* = 2 q_* + x_*`:
  "the Gram matrix therefore has norm at most `1 + O(Q² ξ⁻¹ L^{-D_*}) ≤ 2` once the character
  precision has been chosen sufficiently large."
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

namespace Family

/-! ### The set `𝒞_Q` -/

open _root_.Classical in
/-- `𝒞_Q = {χ : χ primitive, cond χ ≤ Q}` [S-03:0184], as the finite set of the pairs `(r, χ)`,
`1 ≤ r ≤ Q`, `χ` a primitive character modulo `r`. -/
def charSet (Q : ℝ) : Finset (Σ r : ℕ, DirichletCharacter ℂ r) :=
  (Finset.Icc 1 ⌊Q⌋₊).sigma fun r =>
    Finset.univ.filter fun χ : DirichletCharacter ℂ r => χ.IsPrimitive

open _root_.Classical in
theorem mem_charSet {Q : ℝ} {q : Σ r : ℕ, DirichletCharacter ℂ r} :
    q ∈ charSet Q ↔ (1 ≤ q.1 ∧ q.1 ≤ ⌊Q⌋₊) ∧ q.2.IsPrimitive := by
  unfold charSet
  rw [Finset.mem_sigma, Finset.mem_Icc, Finset.mem_filter]
  exact and_congr_right fun _ => and_iff_right (Finset.mem_univ _)

open _root_.Classical in
theorem primitiveCharSum_eq (Q : ℝ) (D X : ℕ) :
    primitiveCharSum Q D X =
      ∑ q ∈ charSet Q, conj (q.2 ((D : ℕ) : ZMod q.1)) * q.2 ((X : ℕ) : ZMod q.1) := by
  unfold primitiveCharSum charSet
  rw [Finset.sum_sigma]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_filter]

open _root_.Classical in
theorem card_charSet (Q : ℝ) : (charSet Q).card = primitiveCharCount Q := by
  unfold charSet primitiveCharCount
  exact Finset.card_sigma _ _

/-- A member of `𝒞_Q` has a positive modulus at most `Q`, and is primitive. -/
theorem of_mem_charSet {Q : ℝ} (hQ : 0 ≤ Q) {q : Σ r : ℕ, DirichletCharacter ℂ r}
    (hq : q ∈ charSet Q) : 0 < q.1 ∧ (q.1 : ℝ) ≤ Q ∧ q.2.IsPrimitive := by
  obtain ⟨⟨h1, h2⟩, hp⟩ := mem_charSet.mp hq
  exact ⟨h1, (Nat.cast_le.mpr h2).trans (Nat.floor_le hQ), hp⟩

/-! ### The characters as functions of a label tuple -/

section Tuples

variable {B : Type} [Fintype B] [DecidableEq B] {J : ℕ} {big : B → Finset ℕ}

omit [DecidableEq B] in
/-- `χ(P_Λ)` for a member `(r, χ)` of `𝒞_Q`. -/
def charFun (Λ : B → Finset (Fin J)) (q : Σ r : ℕ, DirichletCharacter ℂ r)
    (t : AuxList big Λ) : ℂ :=
  q.2 ((tupleProd Λ t : ℕ) : ZMod q.1)

omit [DecidableEq B] in
theorem norm_charFun_le (Λ : B → Finset (Fin J)) (q : Σ r : ℕ, DirichletCharacter ℂ r)
    (t : AuxList big Λ) : ‖charFun Λ q t‖ ≤ 1 := by
  unfold charFun
  exact q.2.norm_le_one _

omit [DecidableEq B] in
theorem sum_charSet_eq (Λ : B → Finset (Fin J)) (Q : ℝ) (d x : AuxList big Λ) :
    ∑ q : charSet Q, conj (charFun Λ q.1 d) * charFun Λ q.1 x =
      primitiveCharSum Q (tupleProd Λ d) (tupleProd Λ x) := by
  rw [Finset.sum_coe_sort (charSet Q) (fun q => conj (charFun Λ q d) * charFun Λ q x),
    primitiveCharSum_eq]
  rfl

/-- **(eq:ideal-cell-kernel) as a cell-wise frame kernel**: `𝒦_Λ(D, X)` for the family
`χ(P_Λ)`. -/
theorem cellKernel_eq_frame (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) (Q h ξ : ℝ)
    (d x : AuxList big Λ) :
    cellKernel big Λ Q h ξ (tupleProd Λ d) (tupleProd Λ x) =
      Frame.kernel (auxWeight big Λ) (fun t : AuxList big Λ => logCell h (tupleProd Λ t)) ξ
        (fun (q : charSet Q) (t : AuxList big Λ) => charFun Λ q.1 t) d x := by
  by_cases hc : logCell h (tupleProd Λ d) = logCell h (tupleProd Λ x) ∧
      ξ ≤ cellMass big Λ h (logCell h (tupleProd Λ d))
  · have e1 : cellKernel big Λ Q h ξ (tupleProd Λ d) (tupleProd Λ x) =
        ((cellMass big Λ h (logCell h (tupleProd Λ d)) : ℝ) : ℂ)⁻¹ *
          primitiveCharSum Q (tupleProd Λ d) (tupleProd Λ x) := by
      unfold cellKernel
      exact if_pos hc
    have e2 : Frame.kernel (auxWeight big Λ)
        (fun t : AuxList big Λ => logCell h (tupleProd Λ t)) ξ
        (fun (q : charSet Q) (t : AuxList big Λ) => charFun Λ q.1 t) d x =
        ((cellMass big Λ h (logCell h (tupleProd Λ d)) : ℝ) : ℂ)⁻¹ *
          ∑ q : charSet Q, conj (charFun Λ q.1 d) * charFun Λ q.1 x := by
      unfold Frame.kernel
      exact if_pos hc
    rw [e1, e2, sum_charSet_eq]
  · have e1 : cellKernel big Λ Q h ξ (tupleProd Λ d) (tupleProd Λ x) = 0 := by
      unfold cellKernel
      exact if_neg hc
    have e2 : Frame.kernel (auxWeight big Λ)
        (fun t : AuxList big Λ => logCell h (tupleProd Λ t)) ξ
        (fun (q : charSet Q) (t : AuxList big Λ) => charFun Λ q.1 t) d x = 0 := by
      unfold Frame.kernel
      exact if_neg hc
    rw [e1, e2]

/-- **The transpose**: `𝒦_Λ(D, X)`, with the two variables exchanged, is the cell-wise frame
kernel of the conjugate family `conj(χ(P_Λ))`. -/
theorem cellKernel_eq_frame_conj (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) (Q h ξ : ℝ)
    (d x : AuxList big Λ) :
    cellKernel big Λ Q h ξ (tupleProd Λ d) (tupleProd Λ x) =
      Frame.kernel (auxWeight big Λ) (fun t : AuxList big Λ => logCell h (tupleProd Λ t)) ξ
        (fun (q : charSet Q) (t : AuxList big Λ) => conj (charFun Λ q.1 t)) x d := by
  by_cases hc : logCell h (tupleProd Λ d) = logCell h (tupleProd Λ x) ∧
      ξ ≤ cellMass big Λ h (logCell h (tupleProd Λ d))
  · have hc' : logCell h (tupleProd Λ x) = logCell h (tupleProd Λ d) ∧
        ξ ≤ cellMass big Λ h (logCell h (tupleProd Λ x)) :=
      ⟨hc.1.symm, by rw [← hc.1]; exact hc.2⟩
    have e1 : cellKernel big Λ Q h ξ (tupleProd Λ d) (tupleProd Λ x) =
        ((cellMass big Λ h (logCell h (tupleProd Λ d)) : ℝ) : ℂ)⁻¹ *
          primitiveCharSum Q (tupleProd Λ d) (tupleProd Λ x) := by
      unfold cellKernel
      exact if_pos hc
    have e2 : Frame.kernel (auxWeight big Λ)
        (fun t : AuxList big Λ => logCell h (tupleProd Λ t)) ξ
        (fun (q : charSet Q) (t : AuxList big Λ) => conj (charFun Λ q.1 t)) x d =
        ((cellMass big Λ h (logCell h (tupleProd Λ x)) : ℝ) : ℂ)⁻¹ *
          ∑ q : charSet Q, conj (conj (charFun Λ q.1 x)) * conj (charFun Λ q.1 d) := by
      unfold Frame.kernel
      exact if_pos hc'
    have e3 : ∑ q : charSet Q, conj (conj (charFun Λ q.1 x)) * conj (charFun Λ q.1 d) =
        ∑ q : charSet Q, conj (charFun Λ q.1 d) * charFun Λ q.1 x :=
      Finset.sum_congr rfl fun q _ => by
        rw [Complex.conj_conj, mul_comm]
    rw [e1, e2, e3, sum_charSet_eq, hc.1]
  · have hc' : ¬(logCell h (tupleProd Λ x) = logCell h (tupleProd Λ d) ∧
        ξ ≤ cellMass big Λ h (logCell h (tupleProd Λ x))) := fun h' =>
      hc ⟨h'.1.symm, by rw [← h'.1]; exact h'.2⟩
    have e1 : cellKernel big Λ Q h ξ (tupleProd Λ d) (tupleProd Λ x) = 0 := by
      unfold cellKernel
      exact if_neg hc
    have e2 : Frame.kernel (auxWeight big Λ)
        (fun t : AuxList big Λ => logCell h (tupleProd Λ t)) ξ
        (fun (q : charSet Q) (t : AuxList big Λ) => conj (charFun Λ q.1 t)) x d = 0 := by
      unfold Frame.kernel
      exact if_neg hc'
    rw [e1, e2]

/-- Kernel integration in `D` is the cell-wise frame operator of the family `χ(P_Λ)`. -/
theorem kernelIntD_eq (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) (Q h ξ : ℝ)
    (F : AuxList big Λ → ℂ) :
    kernelIntD big Λ Q h ξ F =
      Frame.op (auxWeight big Λ) (fun t : AuxList big Λ => logCell h (tupleProd Λ t)) ξ
        (fun (q : charSet Q) (t : AuxList big Λ) => charFun Λ q.1 t) F := by
  funext x
  exact Finset.sum_congr rfl fun d _ =>
    congrArg (fun z => ((auxWeight big Λ d : ℝ) : ℂ) * (z * F d))
      (cellKernel_eq_frame big Λ Q h ξ d x)

/-- Kernel integration in `X` is the cell-wise frame operator of the conjugate family. -/
theorem kernelIntX_eq (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) (Q h ξ : ℝ)
    (G : AuxList big Λ → ℂ) :
    kernelIntX big Λ Q h ξ G =
      Frame.op (auxWeight big Λ) (fun t : AuxList big Λ => logCell h (tupleProd Λ t)) ξ
        (fun (q : charSet Q) (t : AuxList big Λ) => conj (charFun Λ q.1 t)) G := by
  funext d
  exact Finset.sum_congr rfl fun x _ =>
    congrArg (fun z => ((auxWeight big Λ x : ℝ) : ℂ) * (z * G x))
      (cellKernel_eq_frame_conj big Λ Q h ξ d x)

/-- **The off-diagonal Gram entries on a cell** [S-03:0252–0253], from the conclusion of
(eq:ideal-character-cell) for the cell width `h`. -/
theorem gram_entry_le (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) {Q h η : ℝ} (hQ : 0 ≤ Q)
    (hcell : ∀ (j : ℤ) (r₁ r₂ : ℕ) (χ₁ : DirichletCharacter ℂ r₁)
      (χ₂ : DirichletCharacter ℂ r₂), 0 < r₁ → (r₁ : ℝ) ≤ Q → 0 < r₂ → (r₂ : ℝ) ≤ Q →
      χ₁.IsPrimitive → χ₂.IsPrimitive →
      (⟨r₁, χ₁⟩ : Σ r : ℕ, DirichletCharacter ℂ r) ≠ ⟨r₂, χ₂⟩ →
      ‖∑ t : AuxList big Λ, if logCell h (tupleProd Λ t) = j then
          (auxWeight big Λ t : ℂ) *
            (conj (χ₁ ((tupleProd Λ t : ℕ) : ZMod r₁)) * χ₂ ((tupleProd Λ t : ℕ) : ZMod r₂))
        else 0‖ ≤ η)
    (k : ℤ) {q q' : Σ r : ℕ, DirichletCharacter ℂ r} (hq : q ∈ charSet Q)
    (hq' : q' ∈ charSet Q) (hne : q ≠ q') :
    ‖∑ t : AuxList big Λ,
        ((Frame.cellWeight (auxWeight big Λ)
          (fun t : AuxList big Λ => logCell h (tupleProd Λ t)) k t : ℝ) : ℂ) *
          (conj (charFun Λ q t) * charFun Λ q' t)‖ ≤ η := by
  obtain ⟨h1, h2, hp⟩ := of_mem_charSet hQ hq
  obtain ⟨h1', h2', hp'⟩ := of_mem_charSet hQ hq'
  have h3 := hcell k q.1 q'.1 q.2 q'.2 h1 h2 h1' h2' hp hp' hne
  refine le_of_eq_of_le (congrArg norm (Finset.sum_congr rfl fun t _ => ?_)) h3
  by_cases hc : logCell h (tupleProd Λ t) = k
  · rw [Frame.cellWeight_of_eq (w := auxWeight big Λ)
      (c := fun t : AuxList big Λ => logCell h (tupleProd Λ t)) (x := t) hc, if_pos hc]
    rfl
  · rw [Frame.cellWeight_of_ne (w := auxWeight big Λ)
      (c := fun t : AuxList big Λ => logCell h (tupleProd Λ t)) (x := t) hc, if_neg hc,
      Complex.ofReal_zero, zero_mul]

/-- The off-diagonal Gram entries of the conjugate family. -/
theorem gram_entry_conj_le (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) {Q h η : ℝ}
    (hQ : 0 ≤ Q)
    (hcell : ∀ (j : ℤ) (r₁ r₂ : ℕ) (χ₁ : DirichletCharacter ℂ r₁)
      (χ₂ : DirichletCharacter ℂ r₂), 0 < r₁ → (r₁ : ℝ) ≤ Q → 0 < r₂ → (r₂ : ℝ) ≤ Q →
      χ₁.IsPrimitive → χ₂.IsPrimitive →
      (⟨r₁, χ₁⟩ : Σ r : ℕ, DirichletCharacter ℂ r) ≠ ⟨r₂, χ₂⟩ →
      ‖∑ t : AuxList big Λ, if logCell h (tupleProd Λ t) = j then
          (auxWeight big Λ t : ℂ) *
            (conj (χ₁ ((tupleProd Λ t : ℕ) : ZMod r₁)) * χ₂ ((tupleProd Λ t : ℕ) : ZMod r₂))
        else 0‖ ≤ η)
    (k : ℤ) {q q' : Σ r : ℕ, DirichletCharacter ℂ r} (hq : q ∈ charSet Q)
    (hq' : q' ∈ charSet Q) (hne : q ≠ q') :
    ‖∑ t : AuxList big Λ,
        ((Frame.cellWeight (auxWeight big Λ)
          (fun t : AuxList big Λ => logCell h (tupleProd Λ t)) k t : ℝ) : ℂ) *
          (conj (conj (charFun Λ q t)) * conj (charFun Λ q' t))‖ ≤ η := by
  have h1 := gram_entry_le big Λ hQ hcell k hq' hq (Ne.symm hne)
  refine le_of_eq_of_le (congrArg norm (Finset.sum_congr rfl fun t _ => ?_)) h1
  rw [Complex.conj_conj, mul_comm (charFun Λ q t)]

end Tuples

/-- `√(4a) = 2√a`. -/
theorem sqrt_four_mul (a : ℝ) : Real.sqrt (4 * a) = 2 * Real.sqrt a := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), show (4 : ℝ) = 2 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

/-- The number of members of `𝒞_Q`, as the cardinality of the index type of the frame. -/
theorem card_mul_le (Q η ξ : ℝ) (hN : (primitiveCharCount Q : ℝ) * (η / ξ) ≤ 1) :
    (Fintype.card (charSet Q) : ℝ) * (η / ξ) ≤ 1 := by
  rw [Fintype.card_coe, card_charSet]
  exact hN

section Norm

variable {P : GroupParams} {x : ℝ} {S B : Type} [Fintype S] [Fintype B] [DecidableEq B] {J : ℕ}

theorem tupleNorm_le_two (big : B → Finset ℕ) (Λ : B → Finset (Fin J))
    {F G : AuxList big Λ → ℂ}
    (h : wNormSq (auxWeight big Λ) F ≤ 4 * wNormSq (auxWeight big Λ) G) :
    tupleNorm big Λ F ≤ 2 * tupleNorm big Λ G := by
  unfold tupleNorm wNorm
  rw [← sqrt_four_mul]
  exact Real.sqrt_le_sqrt h

/-- Kernel integration in `D`: `‖𝒦F‖² ≤ 4 ‖F‖²`, when the off-diagonal Gram entries on the cells
are at most `η` and `#𝒞_Q · η / ξ ≤ 1`. -/
theorem wNormSq_kernelIntD_le (hgram : GramFrameBound) (𝔊 : PrimeGroups P x S B)
    (Λ : B → Finset (Fin J)) {Q h ξ η : ℝ} (hQ : 0 ≤ Q) (hξ : 0 < ξ) (hη : 0 ≤ η)
    (hcell : ∀ (j : ℤ) (r₁ r₂ : ℕ) (χ₁ : DirichletCharacter ℂ r₁)
      (χ₂ : DirichletCharacter ℂ r₂), 0 < r₁ → (r₁ : ℝ) ≤ Q → 0 < r₂ → (r₂ : ℝ) ≤ Q →
      χ₁.IsPrimitive → χ₂.IsPrimitive →
      (⟨r₁, χ₁⟩ : Σ r : ℕ, DirichletCharacter ℂ r) ≠ ⟨r₂, χ₂⟩ →
      ‖∑ t : AuxList 𝔊.big Λ, if logCell h (tupleProd Λ t) = j then
          (auxWeight 𝔊.big Λ t : ℂ) *
            (conj (χ₁ ((tupleProd Λ t : ℕ) : ZMod r₁)) * χ₂ ((tupleProd Λ t : ℕ) : ZMod r₂))
        else 0‖ ≤ η)
    (hN : (primitiveCharCount Q : ℝ) * (η / ξ) ≤ 1) (G : AuxList 𝔊.big Λ → ℂ) :
    wNormSq (auxWeight 𝔊.big Λ) (kernelIntD 𝔊.big Λ Q h ξ G) ≤
      4 * wNormSq (auxWeight 𝔊.big Λ) G := by
  rw [kernelIntD_eq]
  exact Frame.wNormSq_op_le hgram (tupleWeight_nonneg 𝔊 Λ)
    (fun t : AuxList 𝔊.big Λ => logCell h (tupleProd Λ t)) hξ
    (fun (q : charSet Q) (t : AuxList 𝔊.big Λ) => charFun Λ q.1 t)
    (fun q t => norm_charFun_le Λ q.1 t) hη
    (fun k _ q q' hqq =>
      gram_entry_le 𝔊.big Λ hQ hcell k q.2 q'.2 fun he => hqq (Subtype.ext he))
    (card_mul_le Q η ξ hN) G

/-- Kernel integration in `X` (the transpose): `‖𝒦ᵗG‖² ≤ 4 ‖G‖²`. -/
theorem wNormSq_kernelIntX_le (hgram : GramFrameBound) (𝔊 : PrimeGroups P x S B)
    (Λ : B → Finset (Fin J)) {Q h ξ η : ℝ} (hQ : 0 ≤ Q) (hξ : 0 < ξ) (hη : 0 ≤ η)
    (hcell : ∀ (j : ℤ) (r₁ r₂ : ℕ) (χ₁ : DirichletCharacter ℂ r₁)
      (χ₂ : DirichletCharacter ℂ r₂), 0 < r₁ → (r₁ : ℝ) ≤ Q → 0 < r₂ → (r₂ : ℝ) ≤ Q →
      χ₁.IsPrimitive → χ₂.IsPrimitive →
      (⟨r₁, χ₁⟩ : Σ r : ℕ, DirichletCharacter ℂ r) ≠ ⟨r₂, χ₂⟩ →
      ‖∑ t : AuxList 𝔊.big Λ, if logCell h (tupleProd Λ t) = j then
          (auxWeight 𝔊.big Λ t : ℂ) *
            (conj (χ₁ ((tupleProd Λ t : ℕ) : ZMod r₁)) * χ₂ ((tupleProd Λ t : ℕ) : ZMod r₂))
        else 0‖ ≤ η)
    (hN : (primitiveCharCount Q : ℝ) * (η / ξ) ≤ 1) (G : AuxList 𝔊.big Λ → ℂ) :
    wNormSq (auxWeight 𝔊.big Λ) (kernelIntX 𝔊.big Λ Q h ξ G) ≤
      4 * wNormSq (auxWeight 𝔊.big Λ) G := by
  rw [kernelIntX_eq]
  exact Frame.wNormSq_op_le hgram (tupleWeight_nonneg 𝔊 Λ)
    (fun t : AuxList 𝔊.big Λ => logCell h (tupleProd Λ t)) hξ
    (fun (q : charSet Q) (t : AuxList 𝔊.big Λ) => conj (charFun Λ q.1 t))
    (fun q t => (le_of_eq (Complex.norm_conj _)).trans (norm_charFun_le Λ q.1 t)) hη
    (fun k _ q q' hqq =>
      gram_entry_conj_le 𝔊.big Λ hQ hcell k q.2 q'.2 fun he => hqq (Subtype.ext he))
    (card_mul_le Q η ξ hN) G

end Norm

end Family

/-! ### The norm bound -/

/-- **Kernel integration has norm at most `2`** (eq:ideal-frame), (eq:ideal-gram-bound)
[S-03:0243–0266], from (eq:ideal-character-cell) and the Gram bound. -/
theorem kernelNorm_of_cell (hcellS : CharacterCell) (hgram : GramFrameBound) : KernelNorm := by
  intro P m qs hs xs hqs _ _
  obtain ⟨x₁, hcell⟩ := hcellS P m qs (2 * qs + xs) hqs
  refine ⟨max x₁ (Real.exp 1), ?_⟩
  intro x hx S B _ _ _ _ 𝔊 hint J Λ hne hΛ G
  have hx₁ : x₁ ≤ x := (le_max_left _ _).trans hx
  have hxe : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hL1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hxe
  have hL0 : 0 < Real.log x := by linarith
  have hQ0 : 0 < Real.log x ^ qs := Real.rpow_pos_of_pos hL0 _
  have hh0 : 0 < Real.log x ^ (-hs) := Real.rpow_pos_of_pos hL0 _
  have hξ0 : 0 < Real.log x ^ (-xs) := Real.rpow_pos_of_pos hL0 _
  have hη0 : 0 ≤ Real.log x ^ (-(2 * qs + xs)) := Real.rpow_nonneg hL0.le _
  have hc := hcell x hx₁ S B 𝔊 hint J Λ hne hΛ (Real.log x ^ (-hs)) hh0
  have hN : (primitiveCharCount (Real.log x ^ qs) : ℝ) *
      (Real.log x ^ (-(2 * qs + xs)) / Real.log x ^ (-xs)) ≤ 1 := by
    have h1 : (primitiveCharCount (Real.log x ^ qs) : ℝ) ≤ (Real.log x ^ qs) ^ 2 :=
      primitiveCharCount_le_sq _ hQ0.le
    have h2 : (Real.log x ^ qs) ^ 2 *
        (Real.log x ^ (-(2 * qs + xs)) / Real.log x ^ (-xs)) = 1 := by
      rw [sq, ← Real.rpow_add hL0, ← Real.rpow_sub hL0, ← Real.rpow_add hL0]
      have h3 : qs + qs + (-(2 * qs + xs) - -xs) = 0 := by ring
      rw [h3, Real.rpow_zero]
    have h4 : 0 ≤ Real.log x ^ (-(2 * qs + xs)) / Real.log x ^ (-xs) :=
      div_nonneg hη0 hξ0.le
    exact (mul_le_mul_of_nonneg_right h1 h4).trans (le_of_eq h2)
  exact ⟨Family.tupleNorm_le_two 𝔊.big Λ
      (Family.wNormSq_kernelIntD_le hgram 𝔊 Λ hQ0.le hξ0 hη0 hc hN G),
    Family.tupleNorm_le_two 𝔊.big Λ
      (Family.wNormSq_kernelIntX_le hgram 𝔊 Λ hQ0.le hξ0 hη0 hc hN G)⟩

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
