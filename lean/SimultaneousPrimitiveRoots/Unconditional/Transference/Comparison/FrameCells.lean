module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Leaves
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Frame operators on the cells of a partition

Source: `verification/stage7-sources/S-03.tex`, lines 243–266 (`[S-03:0243–0266]`).

The abstract form of "kernel integration on the full label space has norm at most `2`": a finite
probability space `(X, w)` is partitioned into cells `c x = k`; on every cell of mass at least `ξ`
the kernel is the frame kernel `ν_k⁻¹ ∑_i conj(φ_i(d)) φ_i(x)` of the conditional measure, and it
vanishes elsewhere.

* `Frame.op_eq_frame` — "for a retained cell of mass `ν`, the integral operator is the character
  frame operator on the conditional probability space" (eq:ideal-frame).
* `Frame.cell_bound_retained` — on a retained cell the Gram matrix has diagonal at most `1` and
  off-diagonal entries at most `η/ξ`, so by `GramFrameBound` the frame operator has norm at most
  `1 + N η/ξ ≤ 2` (eq:ideal-gram-bound). "Passing from the conditional to the original measure
  multiplies both squared norms by `ν`, so the operator norm is unchanged."
* `Frame.wNormSq_op_le` — "different cells are orthogonal blocks, and discarded cells have zero
  operator": `‖𝒦F‖² ≤ 4 ‖F‖²`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

namespace Frame

variable {X : Type} [Fintype X] {ι : Type} [Fintype ι]

/-- The restriction of a weight to the cell `k` of the partition `c`. -/
def cellWeight (w : X → ℝ) (c : X → ℤ) (k : ℤ) (x : X) : ℝ := if c x = k then w x else 0

/-- The mass of the cell `k`. -/
def mass (w : X → ℝ) (c : X → ℤ) (k : ℤ) : ℝ := ∑ x, cellWeight w c k x

/-- The kernel: on a cell of mass at least `ξ` the frame kernel of the conditional measure, zero
elsewhere. -/
def kernel (w : X → ℝ) (c : X → ℤ) (ξ : ℝ) (φ : ι → X → ℂ) (d x : X) : ℂ :=
  if c d = c x ∧ ξ ≤ mass w c (c d) then
    ((mass w c (c d) : ℝ) : ℂ)⁻¹ * ∑ i, conj (φ i d) * φ i x
  else 0

/-- Integration of the kernel in its first variable. -/
def op (w : X → ℝ) (c : X → ℤ) (ξ : ℝ) (φ : ι → X → ℂ) (F : X → ℂ) (x : X) : ℂ :=
  ∑ d, (w d : ℂ) * (kernel w c ξ φ d x * F d)

omit [Fintype X] in
theorem cellWeight_of_eq {w : X → ℝ} {c : X → ℤ} {k : ℤ} {x : X} (h : c x = k) :
    cellWeight w c k x = w x := by
  unfold cellWeight
  exact if_pos h

omit [Fintype X] in
theorem cellWeight_of_ne {w : X → ℝ} {c : X → ℤ} {k : ℤ} {x : X} (h : ¬c x = k) :
    cellWeight w c k x = 0 := by
  unfold cellWeight
  exact if_neg h

omit [Fintype X] in
theorem cellWeight_nonneg {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (c : X → ℤ) (k : ℤ) (x : X) :
    0 ≤ cellWeight w c k x := by
  by_cases h : c x = k
  · rw [cellWeight_of_eq h]
    exact hw x
  · exact (cellWeight_of_ne h).ge

/-- A sum over the space is the sum over the cells. -/
theorem sum_weight_eq (w : X → ℝ) (c : X → ℤ) (g : X → ℝ) :
    ∑ x, w x * g x = ∑ k ∈ Finset.univ.image c, ∑ x, cellWeight w c k x * g x := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_mul]
  unfold cellWeight
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_image_of_mem c (Finset.mem_univ x))]

/-- **(eq:ideal-frame)**: on a retained cell the integral operator is the frame operator of the
conditional measure. -/
theorem op_eq_frame (w : X → ℝ) (c : X → ℤ) {ξ : ℝ} (φ : ι → X → ℂ) (F : X → ℂ) {k : ℤ}
    (hk : ξ ≤ mass w c k) {x : X} (hx : c x = k) :
    op w c ξ φ F x =
      ∑ i, φ i x * wInner (fun d => cellWeight w c k d * (mass w c k)⁻¹) (φ i) F := by
  have hin : ∀ i, wInner (fun d => cellWeight w c k d * (mass w c k)⁻¹) (φ i) F =
      ∑ d, ((cellWeight w c k d * (mass w c k)⁻¹ : ℝ) : ℂ) * (conj (φ i d) * F d) :=
    fun _ => rfl
  have hterm : ∀ d : X, (w d : ℂ) * (kernel w c ξ φ d x * F d) =
      ∑ i, φ i x * (((cellWeight w c k d * (mass w c k)⁻¹ : ℝ) : ℂ) * (conj (φ i d) * F d)) := by
    intro d
    by_cases hd : c d = k
    · have hcond : c d = c x ∧ ξ ≤ mass w c (c d) := ⟨hd.trans hx.symm, by rw [hd]; exact hk⟩
      unfold kernel
      rw [if_pos hcond, hd, cellWeight_of_eq hd]
      calc (w d : ℂ) * (((mass w c k : ℝ) : ℂ)⁻¹ * (∑ i, conj (φ i d) * φ i x) * F d)
          = ((w d : ℂ) * ((mass w c k : ℝ) : ℂ)⁻¹ * F d) * ∑ i, conj (φ i d) * φ i x := by ring
        _ = ∑ i, ((w d : ℂ) * ((mass w c k : ℝ) : ℂ)⁻¹ * F d) * (conj (φ i d) * φ i x) :=
            Finset.mul_sum _ _ _
        _ = ∑ i, φ i x * (((w d * (mass w c k)⁻¹ : ℝ) : ℂ) * (conj (φ i d) * F d)) :=
            Finset.sum_congr rfl fun i _ => by
              push_cast
              ring
    · have hcond : ¬(c d = c x ∧ ξ ≤ mass w c (c d)) := fun hc => hd (hc.1.trans hx)
      unfold kernel
      rw [if_neg hcond, zero_mul, mul_zero, cellWeight_of_ne hd]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rw [zero_mul, Complex.ofReal_zero, zero_mul, mul_zero]
  unfold op
  rw [Finset.sum_congr rfl fun d _ => hterm d, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hin i, Finset.mul_sum]

/-- **(eq:ideal-gram-bound) on a retained cell**: the frame operator has norm at most `2` for the
conditional measure, hence for the restriction of the original measure to the cell. -/
theorem cell_bound_retained (hgram : GramFrameBound) {w : X → ℝ} (hw : ∀ x, 0 ≤ w x)
    (c : X → ℤ) {ξ : ℝ} (hξ : 0 < ξ) (φ : ι → X → ℂ) (hφ : ∀ i x, ‖φ i x‖ ≤ 1) {η : ℝ}
    (hη : 0 ≤ η) {k : ℤ} (hk : ξ ≤ mass w c k)
    (hoff : ∀ i j, i ≠ j → ‖∑ x, (cellWeight w c k x : ℂ) * (conj (φ i x) * φ j x)‖ ≤ η)
    (hN : (Fintype.card ι : ℝ) * (η / ξ) ≤ 1) (F : X → ℂ) :
    ∑ x, cellWeight w c k x * ‖op w c ξ φ F x‖ ^ 2 ≤
      4 * ∑ x, cellWeight w c k x * ‖F x‖ ^ 2 := by
  have hν : 0 < mass w c k := lt_of_lt_of_le hξ hk
  have hwt : ∀ d, 0 ≤ cellWeight w c k d * (mass w c k)⁻¹ := fun d =>
    mul_nonneg (cellWeight_nonneg hw c k d) (inv_nonneg.mpr hν.le)
  -- the Gram matrix of the conditional measure
  have hdiag : ∀ i, wNormSq (fun d => cellWeight w c k d * (mass w c k)⁻¹) (φ i) ≤ 1 := by
    intro i
    have h1 : wNormSq (fun d => cellWeight w c k d * (mass w c k)⁻¹) (φ i) ≤
        ∑ x, cellWeight w c k x * (mass w c k)⁻¹ := by
      have hsq : ∀ x, ‖φ i x‖ ^ 2 ≤ 1 := fun x => by
        have h2 := hφ i x
        have h0 := norm_nonneg (φ i x)
        nlinarith [mul_le_mul_of_nonneg_left h2 h0]
      unfold wNormSq
      exact Finset.sum_le_sum fun x _ =>
        (mul_le_mul_of_nonneg_left (hsq x) (hwt x)).trans (le_of_eq (mul_one _))
    have h2 : ∑ x, cellWeight w c k x * (mass w c k)⁻¹ = 1 := by
      rw [← Finset.sum_mul]
      exact mul_inv_cancel₀ hν.ne'
    exact h1.trans (le_of_eq h2)
  have hoffw : ∀ i j, i ≠ j →
      ‖wInner (fun d => cellWeight w c k d * (mass w c k)⁻¹) (φ i) (φ j)‖ ≤ η / ξ := by
    intro i j hij
    have h1 : wInner (fun d => cellWeight w c k d * (mass w c k)⁻¹) (φ i) (φ j) =
        ((mass w c k : ℝ) : ℂ)⁻¹ * ∑ x, (cellWeight w c k x : ℂ) * (conj (φ i x) * φ j x) := by
      have h3 : wInner (fun d => cellWeight w c k d * (mass w c k)⁻¹) (φ i) (φ j) =
          ∑ x, ((cellWeight w c k x * (mass w c k)⁻¹ : ℝ) : ℂ) * (conj (φ i x) * φ j x) := rfl
      rw [h3, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      push_cast
      ring
    rw [h1, norm_mul, norm_inv, Complex.norm_of_nonneg hν.le]
    calc (mass w c k)⁻¹ * ‖∑ x, (cellWeight w c k x : ℂ) * (conj (φ i x) * φ j x)‖
        ≤ ξ⁻¹ * η :=
          mul_le_mul (inv_anti₀ hξ hk) (hoff i j hij) (norm_nonneg _) (inv_nonneg.mpr hξ.le)
      _ = η / ξ := by rw [div_eq_inv_mul]
  have hg := hgram X (fun d => cellWeight w c k d * (mass w c k)⁻¹) hwt ι φ (η / ξ)
    (div_nonneg hη hξ.le) hdiag hoffw F
  have h2 : wNorm (fun d => cellWeight w c k d * (mass w c k)⁻¹)
        (fun x => ∑ i, φ i x * wInner (fun d => cellWeight w c k d * (mass w c k)⁻¹) (φ i) F) ≤
      2 * wNorm (fun d => cellWeight w c k d * (mass w c k)⁻¹) F :=
    hg.trans (mul_le_mul_of_nonneg_right (by linarith) (wNorm_nonneg _ _))
  have h3 : wNormSq (fun d => cellWeight w c k d * (mass w c k)⁻¹)
        (fun x => ∑ i, φ i x * wInner (fun d => cellWeight w c k d * (mass w c k)⁻¹) (φ i) F) ≤
      4 * wNormSq (fun d => cellWeight w c k d * (mass w c k)⁻¹) F := by
    rw [← wNorm_sq hwt, ← wNorm_sq hwt]
    have h4 := pow_le_pow_left₀ (wNorm_nonneg _ _) h2 2
    have h4' : (2 * wNorm (fun d => cellWeight w c k d * (mass w c k)⁻¹) F) ^ 2 =
        4 * wNorm (fun d => cellWeight w c k d * (mass w c k)⁻¹) F ^ 2 := by ring
    exact h4.trans (le_of_eq h4')
  -- from the conditional measure to the cell
  have hscale : ∀ G : X → ℂ, ∑ x, cellWeight w c k x * ‖G x‖ ^ 2 =
      mass w c k * wNormSq (fun d => cellWeight w c k d * (mass w c k)⁻¹) G := by
    intro G
    have h5 : wNormSq (fun d => cellWeight w c k d * (mass w c k)⁻¹) G =
        ∑ x, cellWeight w c k x * (mass w c k)⁻¹ * ‖G x‖ ^ 2 := rfl
    rw [h5, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    calc cellWeight w c k x * ‖G x‖ ^ 2
        = cellWeight w c k x * ‖G x‖ ^ 2 * (mass w c k * (mass w c k)⁻¹) := by
          rw [mul_inv_cancel₀ hν.ne', mul_one]
      _ = mass w c k * (cellWeight w c k x * (mass w c k)⁻¹ * ‖G x‖ ^ 2) := by ring
  have hop : ∑ x, cellWeight w c k x * ‖op w c ξ φ F x‖ ^ 2 =
      ∑ x, cellWeight w c k x *
        ‖∑ i, φ i x * wInner (fun d => cellWeight w c k d * (mass w c k)⁻¹) (φ i) F‖ ^ 2 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : c x = k
    · rw [op_eq_frame w c φ F hk hx]
    · rw [cellWeight_of_ne hx, zero_mul, zero_mul]
  rw [hop, hscale (fun x => ∑ i, φ i x *
    wInner (fun d => cellWeight w c k d * (mass w c k)⁻¹) (φ i) F), hscale F, ← mul_assoc,
    mul_comm 4 (mass w c k), mul_assoc]
  exact mul_le_mul_of_nonneg_left h3 hν.le

/-- "Discarded cells have zero operator." -/
theorem cell_bound_discarded {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (c : X → ℤ) {ξ : ℝ}
    (φ : ι → X → ℂ) {k : ℤ} (hk : ¬ξ ≤ mass w c k) (F : X → ℂ) :
    ∑ x, cellWeight w c k x * ‖op w c ξ φ F x‖ ^ 2 ≤
      4 * ∑ x, cellWeight w c k x * ‖F x‖ ^ 2 := by
  have hz : ∑ x, cellWeight w c k x * ‖op w c ξ φ F x‖ ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    by_cases hx : c x = k
    · have hop : op w c ξ φ F x = 0 := by
        unfold op
        refine Finset.sum_eq_zero fun d _ => ?_
        have hcond : ¬(c d = c x ∧ ξ ≤ mass w c (c d)) := fun hc =>
          hk (by rw [← hx, ← hc.1]; exact hc.2)
        unfold kernel
        rw [if_neg hcond, zero_mul, mul_zero]
      rw [hop, norm_zero, zero_pow two_ne_zero, mul_zero]
    · rw [cellWeight_of_ne hx, zero_mul]
  rw [hz]
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun x _ =>
    mul_nonneg (cellWeight_nonneg hw c k x) (sq_nonneg _))

/-- **Kernel integration has norm at most `2`** [S-03:0254–0263]: `‖𝒦F‖² ≤ 4 ‖F‖²`, when on
every retained cell the off-diagonal Gram entries (for the restricted weight) are at most `η` and
`N η / ξ ≤ 1`. -/
theorem wNormSq_op_le (hgram : GramFrameBound) {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (c : X → ℤ)
    {ξ : ℝ} (hξ : 0 < ξ) (φ : ι → X → ℂ) (hφ : ∀ i x, ‖φ i x‖ ≤ 1) {η : ℝ} (hη : 0 ≤ η)
    (hoff : ∀ k : ℤ, ξ ≤ mass w c k → ∀ i j, i ≠ j →
      ‖∑ x, (cellWeight w c k x : ℂ) * (conj (φ i x) * φ j x)‖ ≤ η)
    (hN : (Fintype.card ι : ℝ) * (η / ξ) ≤ 1) (F : X → ℂ) :
    wNormSq w (op w c ξ φ F) ≤ 4 * wNormSq w F := by
  unfold wNormSq
  rw [sum_weight_eq w c (fun x => ‖op w c ξ φ F x‖ ^ 2),
    sum_weight_eq w c (fun x => ‖F x‖ ^ 2), Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases hk : ξ ≤ mass w c k
  · exact cell_bound_retained hgram hw c hξ φ hφ hη hk (hoff k hk) hN F
  · exact cell_bound_discarded hw c φ hk F

end Frame

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
