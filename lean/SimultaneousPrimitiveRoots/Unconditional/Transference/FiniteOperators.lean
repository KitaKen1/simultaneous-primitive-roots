module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Finite-row operators and weighted `L²` norms on a finite type

Two generic tools for the transference statements of [S] §§3–4
(`verification/stage7-sources/S-02.tex`, `S-03.tex`).

* `rowOp coef tgt` is the operator `(rowOp coef tgt g) s = ∑ ξ, coef s ξ * g (tgt s ξ)`:
  a *row operator* in the sense of [S-02:0076–0077] ("a row operator integrates a function at the
  target and returns a function at the source"). The finite type `Ξ` indexes the transition
  choices of one row. It is a `ℂ`-linear map by construction; all operators of
  Definitions 3.2 and 3.3 are built from it by composition and finite sums.
* `wInner w`, `wNorm w`, `wOpNorm w` are the inner product, the norm and the operator norm of
  `L²(X, w)` for a finite type `X` with point masses `w : X → ℝ`. The operator norm is the
  supremum of `‖T F‖ / ‖F‖`; `wOpNorm_le_iff` proves that, for positive weights, it is the least
  constant `C` with `‖T F‖ ≤ C ‖F‖` for all `F`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ### Finite-row operators -/

/-- The row operator with transition choices `ξ : Ξ`, coefficients `coef s ξ` and targets
`tgt s ξ`: `(rowOp coef tgt g) s = ∑ ξ, coef s ξ * g (tgt s ξ)`. The source type `S` and the
target type `T` may be infinite; every row is a finite sum. -/
def rowOp {S T Ξ : Type*} [Fintype Ξ] (coef : S → Ξ → ℂ) (tgt : S → Ξ → T) :
    (T → ℂ) →ₗ[ℂ] (S → ℂ) where
  toFun g s := ∑ ξ, coef s ξ * g (tgt s ξ)
  map_add' g h := by
    funext s
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c g := by
    funext s
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun ξ _ => by ring

theorem rowOp_apply {S T Ξ : Type*} [Fintype Ξ] (coef : S → Ξ → ℂ) (tgt : S → Ξ → T)
    (g : T → ℂ) (s : S) : rowOp coef tgt g s = ∑ ξ, coef s ξ * g (tgt s ξ) := rfl

/-- The matrix entry of a row operator: its value at `s` on the point mass at `t`. -/
theorem rowOp_single {S T Ξ : Type*} [Fintype Ξ] [DecidableEq T] (coef : S → Ξ → ℂ)
    (tgt : S → Ξ → T) (t : T) (s : S) :
    rowOp coef tgt (Pi.single t 1) s = ∑ ξ, if tgt s ξ = t then coef s ξ else 0 := by
  rw [rowOp_apply]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [Pi.single_apply]
  split_ifs <;> simp

/-! ### Weighted `L²` on a finite type -/

variable {X : Type*} [Fintype X]

/-- `⟨F, G⟩ = ∑ x, w x * conj (F x) * G x`, the inner product of `L²(X, w)` (conjugate-linear in the
first argument). -/
def wInner (w : X → ℝ) (F G : X → ℂ) : ℂ := ∑ x, (w x : ℂ) * (conj (F x) * G x)

/-- `‖F‖² = ∑ x, w x * |F x|²`. -/
def wNormSq (w : X → ℝ) (F : X → ℂ) : ℝ := ∑ x, w x * ‖F x‖ ^ 2

/-- The norm of `L²(X, w)`. -/
def wNorm (w : X → ℝ) (F : X → ℂ) : ℝ := Real.sqrt (wNormSq w F)

/-- The operator norm `‖T‖_{2 → 2}` on `L²(X, w)`: the supremum of `‖T F‖ / ‖F‖` (with `0 / 0 = 0`).
For positive weights it is the least `C` with `‖T F‖ ≤ C ‖F‖` (`wOpNorm_le_iff`). -/
def wOpNorm (w : X → ℝ) (T : (X → ℂ) →ₗ[ℂ] (X → ℂ)) : ℝ :=
  ⨆ F : X → ℂ, wNorm w (T F) / wNorm w F

theorem wInner_self (w : X → ℝ) (F : X → ℂ) : wInner w F F = (wNormSq w F : ℂ) := by
  unfold wInner wNormSq
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.conj_mul', Complex.ofReal_mul, Complex.ofReal_pow]

theorem wNormSq_nonneg {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (F : X → ℂ) : 0 ≤ wNormSq w F :=
  Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (sq_nonneg _)

theorem wNorm_nonneg (w : X → ℝ) (F : X → ℂ) : 0 ≤ wNorm w F := Real.sqrt_nonneg _

theorem wNorm_sq {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (F : X → ℂ) :
    wNorm w F ^ 2 = wNormSq w F := Real.sq_sqrt (wNormSq_nonneg hw F)

theorem wNorm_smul (w : X → ℝ) (c : ℂ) (F : X → ℂ) : wNorm w (c • F) = ‖c‖ * wNorm w F := by
  have h : wNormSq w (c • F) = ‖c‖ ^ 2 * wNormSq w F := by
    unfold wNormSq
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
    ring
  unfold wNorm
  rw [h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg c)]

theorem wOpNorm_nonneg (w : X → ℝ) (T : (X → ℂ) →ₗ[ℂ] (X → ℂ)) : 0 ≤ wOpNorm w T :=
  Real.iSup_nonneg fun _ => div_nonneg (wNorm_nonneg _ _) (wNorm_nonneg _ _)

/-- A point value is controlled by the weighted norm. -/
theorem norm_sq_le_wNormSq_div {w : X → ℝ} (hw : ∀ x, 0 < w x) (F : X → ℂ) (y : X) :
    ‖F y‖ ^ 2 ≤ wNormSq w F / w y := by
  rw [le_div_iff₀ (hw y)]
  have h := Finset.single_le_sum (f := fun x => w x * ‖F x‖ ^ 2)
    (fun x _ => mul_nonneg (hw x).le (sq_nonneg _)) (Finset.mem_univ y)
  calc ‖F y‖ ^ 2 * w y = w y * ‖F y‖ ^ 2 := mul_comm _ _
    _ ≤ wNormSq w F := h

/-- Every linear map on the finite-dimensional space `L²(X, w)`, `w > 0`, is bounded (a crude
Hilbert–Schmidt bound). -/
theorem exists_wNormSq_apply_le [DecidableEq X] {w : X → ℝ} (hw : ∀ x, 0 < w x)
    (T : (X → ℂ) →ₗ[ℂ] (X → ℂ)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ F : X → ℂ, wNormSq w (T F) ≤ K * wNormSq w F := by
  let e : X → X → ℂ := fun i j => if i = j then 1 else 0
  let K : ℝ := ∑ x, w x * ((Fintype.card X : ℝ) * ∑ y, ‖T (e y) x‖ ^ 2 / w y)
  have hK : 0 ≤ K := by
    refine Finset.sum_nonneg fun x _ => mul_nonneg (hw x).le (mul_nonneg (Nat.cast_nonneg _) ?_)
    exact Finset.sum_nonneg fun y _ => div_nonneg (sq_nonneg _) (hw y).le
  refine ⟨K, hK, fun F => ?_⟩
  have hpt : ∀ x, ‖T F x‖ ^ 2 ≤
      wNormSq w F * ((Fintype.card X : ℝ) * ∑ y, ‖T (e y) x‖ ^ 2 / w y) := by
    intro x
    have h1 : T F x = ∑ y, F y * T (e y) x := by
      have h := congrFun (LinearMap.pi_apply_eq_sum_univ T F) x
      rw [h, Finset.sum_apply]
      rfl
    have h2 : ‖T F x‖ ≤ ∑ y, ‖F y‖ * ‖T (e y) x‖ := by
      rw [h1]
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun y _ => norm_mul _ _
    have h3 : ‖T F x‖ ^ 2 ≤ (∑ y, ‖F y‖ * ‖T (e y) x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h2 2
    have h4 : (∑ y, ‖F y‖ * ‖T (e y) x‖) ^ 2 ≤
        (Fintype.card X : ℝ) * ∑ y, (‖F y‖ * ‖T (e y) x‖) ^ 2 := by
      have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset X))
        (f := fun y => ‖F y‖ * ‖T (e y) x‖)
      rw [Finset.card_univ] at h
      exact h
    have h5 : ∑ y, (‖F y‖ * ‖T (e y) x‖) ^ 2 ≤
        ∑ y, wNormSq w F * (‖T (e y) x‖ ^ 2 / w y) := by
      refine Finset.sum_le_sum fun y _ => ?_
      rw [mul_pow]
      calc ‖F y‖ ^ 2 * ‖T (e y) x‖ ^ 2 ≤ (wNormSq w F / w y) * ‖T (e y) x‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (norm_sq_le_wNormSq_div hw F y) (sq_nonneg _)
        _ = wNormSq w F * (‖T (e y) x‖ ^ 2 / w y) := by ring
    calc ‖T F x‖ ^ 2 ≤ (Fintype.card X : ℝ) * ∑ y, (‖F y‖ * ‖T (e y) x‖) ^ 2 := h3.trans h4
      _ ≤ (Fintype.card X : ℝ) * ∑ y, wNormSq w F * (‖T (e y) x‖ ^ 2 / w y) :=
          mul_le_mul_of_nonneg_left h5 (Nat.cast_nonneg _)
      _ = wNormSq w F * ((Fintype.card X : ℝ) * ∑ y, ‖T (e y) x‖ ^ 2 / w y) := by
          rw [← Finset.mul_sum]
          ring
  calc wNormSq w (T F) = ∑ x, w x * ‖T F x‖ ^ 2 := rfl
    _ ≤ ∑ x, w x * (wNormSq w F * ((Fintype.card X : ℝ) * ∑ y, ‖T (e y) x‖ ^ 2 / w y)) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt x) (hw x).le
    _ = K * wNormSq w F := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by ring

theorem exists_wNorm_apply_le {w : X → ℝ} (hw : ∀ x, 0 < w x) (T : (X → ℂ) →ₗ[ℂ] (X → ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : X → ℂ, wNorm w (T F) ≤ C * wNorm w F := by
  classical
  obtain ⟨K, hK, h⟩ := exists_wNormSq_apply_le hw T
  refine ⟨Real.sqrt K, Real.sqrt_nonneg _, fun F => ?_⟩
  unfold wNorm
  rw [← Real.sqrt_mul hK]
  exact Real.sqrt_le_sqrt (h F)

/-- **The operator norm is the least bound.** For positive weights and `C ≥ 0`:
`‖T‖ ≤ C` if and only if `‖T F‖ ≤ C ‖F‖` for every `F`. -/
theorem wOpNorm_le_iff {w : X → ℝ} (hw : ∀ x, 0 < w x) (T : (X → ℂ) →ₗ[ℂ] (X → ℂ)) {C : ℝ}
    (hC : 0 ≤ C) : wOpNorm w T ≤ C ↔ ∀ F : X → ℂ, wNorm w (T F) ≤ C * wNorm w F := by
  obtain ⟨C₀, hC₀, hbd⟩ := exists_wNorm_apply_le hw T
  have hratio : ∀ F : X → ℂ, wNorm w (T F) / wNorm w F ≤ C₀ := by
    intro F
    rcases (wNorm_nonneg w F).eq_or_lt with h0 | hpos
    · rw [← h0, div_zero]
      exact hC₀
    · exact (div_le_iff₀ hpos).mpr (hbd F)
  have hbdd : BddAbove (Set.range fun F : X → ℂ => wNorm w (T F) / wNorm w F) :=
    ⟨C₀, by rintro _ ⟨F, rfl⟩; exact hratio F⟩
  constructor
  · intro h F
    have h1 : wNorm w (T F) / wNorm w F ≤ C := (le_ciSup hbdd F).trans h
    rcases (wNorm_nonneg w F).eq_or_lt with h0 | hpos
    · have h2 := hbd F
      rw [← h0, mul_zero] at h2 ⊢
      exact h2
    · exact (div_le_iff₀ hpos).mp h1
  · intro h
    unfold wOpNorm
    refine Real.iSup_le (fun F => ?_) hC
    rcases (wNorm_nonneg w F).eq_or_lt with h0 | hpos
    · rw [← h0, div_zero]
      exact hC
    · exact (div_le_iff₀ hpos).mpr (h F)

/-- `‖T F‖ ≤ ‖T‖ ‖F‖` for positive weights. -/
theorem wNorm_apply_le {w : X → ℝ} (hw : ∀ x, 0 < w x) (T : (X → ℂ) →ₗ[ℂ] (X → ℂ))
    (F : X → ℂ) : wNorm w (T F) ≤ wOpNorm w T * wNorm w F :=
  (wOpNorm_le_iff hw T (wOpNorm_nonneg w T)).mp le_rfl F

/-- The operator norm of a scalar operator is the modulus of the scalar. -/
theorem wOpNorm_smul_id [Nonempty X] {w : X → ℝ} (hw : ∀ x, 0 < w x) (c : ℂ) :
    wOpNorm w (c • (LinearMap.id : (X → ℂ) →ₗ[ℂ] (X → ℂ))) = ‖c‖ := by
  have happ : ∀ F : X → ℂ, (c • (LinearMap.id : (X → ℂ) →ₗ[ℂ] (X → ℂ))) F = c • F :=
    fun F => rfl
  apply le_antisymm
  · rw [wOpNorm_le_iff hw _ (norm_nonneg c)]
    intro F
    rw [happ, wNorm_smul]
  · have h := wNorm_apply_le hw (c • (LinearMap.id : (X → ℂ) →ₗ[ℂ] (X → ℂ))) (fun _ => 1)
    rw [happ, wNorm_smul] at h
    have hpos : 0 < wNorm w (fun _ : X => (1 : ℂ)) := by
      unfold wNorm wNormSq
      apply Real.sqrt_pos.mpr
      refine Finset.sum_pos (fun x _ => ?_) Finset.univ_nonempty
      simpa using hw x
    exact le_of_mul_le_mul_right h hpos

end

end SimultaneousPrimitiveRoots.Unconditional.Transference
