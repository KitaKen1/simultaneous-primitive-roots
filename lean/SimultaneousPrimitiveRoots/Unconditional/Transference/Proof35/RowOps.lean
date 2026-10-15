module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.FiniteOperators
public import SimultaneousPrimitiveRoots.Unconditional.Graph.FiniteWeightedSchur
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# Row operators: compositions, walks and Schur's test

Generic tools for the proof of [S] Theorem 3.5 (`verification/stage7-sources/S-02.tex`). Every
operator of that proof is a *row operator* `rowOp coef tgt` ("a row operator integrates a function
at the target and returns a function at the source", [S-02:0076–0077]); its *local transition
choices* [S-02:0763–0764, 1185] are the elements of the finite type `Ξ`.

* `rowOp_comp_apply` — a composition of row operators is a row operator whose choices are pairs.
* `walkEnd`, `walkCoef`, `rowOp_pow_apply` — the expansion of a power of a row operator "into
  paths" [S-02:0212–0213]: the sum over all words of choices of the product of the coefficients
  along the walk.
* `sum_weight_mul_le`, `wNorm_add_le`, `norm_wInner_le` — Cauchy's inequality and the triangle
  inequality for the weighted norm `wNorm` (nonnegative weights).
* `OpBound`, `RowBound`, `ColBound` — an operator bound on a class of functions, and the weighted
  row and column conditions "`K w ≤ R w` and `K* w ≤ C w`" of (eq:weighted-schur)
  [S-02:0631–0635] for a row operator. The column condition is stated without forming the adjoint:
  `∫ w · K f ≤ C ∫ w · f` for all nonnegative `f` of the class.
* `rowOp_wNormSq_le`, `opBound_of_row_col` — **Schur's test (eq:weighted-schur) for row
  operators**: `‖K‖_{2→2} ≤ √(RC)`. The proof is the one of [S-02:0636–0638] ("Cauchy's inequality
  in each row bounds `|Kf|²` by `(Kw) K(|f|²/w)`; integration and the column inequality"), with
  `Graph.weighted_kernel_row_sq` for the row step.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ### Compositions and powers -/

/-- A composition of two row operators is the row operator whose transition choices are the pairs
of choices, whose coefficients are the products and whose targets are the composed targets. -/
theorem rowOp_comp_apply {X Y Z Ξ₁ Ξ₂ : Type*} [Fintype Ξ₁] [Fintype Ξ₂]
    (c₁ : X → Ξ₁ → ℂ) (t₁ : X → Ξ₁ → Y) (c₂ : Y → Ξ₂ → ℂ) (t₂ : Y → Ξ₂ → Z) (g : Z → ℂ)
    (s : X) :
    rowOp c₁ t₁ (rowOp c₂ t₂ g) s =
      rowOp (Ξ := Ξ₁ × Ξ₂) (fun s ξ => c₁ s ξ.1 * c₂ (t₁ s ξ.1) ξ.2)
        (fun s ξ => t₂ (t₁ s ξ.1) ξ.2) g s := by
  simp only [rowOp_apply, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

/-- The end of the walk which starts at `s` and makes the choices of the word `w` in turn. -/
def walkEnd {X Ξ : Type*} (tgt : X → Ξ → X) : X → List Ξ → X
  | s, [] => s
  | s, ξ :: w => walkEnd tgt (tgt s ξ) w

/-- The product of the coefficients along the walk which starts at `s` and makes the choices of
the word `w` in turn. -/
def walkCoef {X Ξ : Type*} (coef : X → Ξ → ℂ) (tgt : X → Ξ → X) : X → List Ξ → ℂ
  | _, [] => 1
  | s, ξ :: w => coef s ξ * walkCoef coef tgt (tgt s ξ) w

/-- A word of `n + 1` choices is a first choice and a word of `n` choices. -/
def wordConsEquiv (n : ℕ) (Ξ : Type*) : Ξ × (Fin n → Ξ) ≃ (Fin (n + 1) → Ξ) where
  toFun p := Fin.cons (α := fun _ => Ξ) p.1 p.2
  invFun f := (f 0, fun i => f i.succ)
  left_inv p := by
    rcases p with ⟨a, f⟩
    simp
  right_inv f := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- **Path expansion of a power of a row operator**: `(T^n g)(s)` is the sum over all words of
`n` choices of the product of the coefficients along the walk times the value of `g` at its
end. -/
theorem rowOp_pow_apply {X Ξ : Type*} [Fintype Ξ] (coef : X → Ξ → ℂ) (tgt : X → Ξ → X) (n : ℕ)
    (g : X → ℂ) (s : X) :
    ((rowOp coef tgt : Module.End ℂ (X → ℂ)) ^ n) g s =
      ∑ w : Fin n → Ξ, walkCoef coef tgt s (List.ofFn w) * g (walkEnd tgt s (List.ofFn w)) := by
  induction n generalizing s with
  | zero =>
    rw [pow_zero, Fintype.sum_unique]
    simp [walkCoef, walkEnd]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, rowOp_apply,
      ← (wordConsEquiv n Ξ).sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    have h0 : wordConsEquiv n Ξ (ξ, w) 0 = ξ := by simp [wordConsEquiv]
    have hs : (fun i : Fin n => wordConsEquiv n Ξ (ξ, w) i.succ) = w := by
      funext i
      simp [wordConsEquiv]
    have hl : List.ofFn (wordConsEquiv n Ξ (ξ, w)) = ξ :: List.ofFn w := by
      rw [List.ofFn_succ, h0, hs]
    rw [hl]
    simp only [walkCoef, walkEnd, mul_assoc]

/-! ### The weighted norm -/

section Norms

variable {X : Type*} [Fintype X]

/-- Cauchy's inequality for a nonnegative weight. -/
theorem sum_weight_mul_le (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (a b : X → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hb : ∀ x, 0 ≤ b x) :
    ∑ x, w x * (a x * b x) ≤
      Real.sqrt (∑ x, w x * a x ^ 2) * Real.sqrt (∑ x, w x * b x ^ 2) := by
  have hsq : (∑ x, w x * (a x * b x)) ^ 2 ≤ (∑ x, w x * a x ^ 2) * ∑ x, w x * b x ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun x _ => mul_nonneg (hw x) (sq_nonneg _)) (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
    intro x _
    apply le_of_eq
    ring
  have h0 : 0 ≤ ∑ x, w x * (a x * b x) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (mul_nonneg (ha x) (hb x))
  calc ∑ x, w x * (a x * b x) = Real.sqrt ((∑ x, w x * (a x * b x)) ^ 2) :=
        (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt ((∑ x, w x * a x ^ 2) * ∑ x, w x * b x ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∑ x, w x * a x ^ 2) * Real.sqrt (∑ x, w x * b x ^ 2) :=
        Real.sqrt_mul (Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (sq_nonneg _)) _

/-- The triangle inequality for the weighted norm. -/
theorem wNorm_add_le {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (F G : X → ℂ) :
    wNorm w (F + G) ≤ wNorm w F + wNorm w G := by
  have hcs : ∑ x, w x * (‖F x‖ * ‖G x‖) ≤ wNorm w F * wNorm w G :=
    sum_weight_mul_le w hw (fun x => ‖F x‖) (fun x => ‖G x‖) (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _)
  have e1 : wNorm w F ^ 2 = wNormSq w F := wNorm_sq hw F
  have e2 : wNorm w G ^ 2 = wNormSq w G := wNorm_sq hw G
  have h1 : wNormSq w (F + G) ≤
      wNormSq w F + 2 * (∑ x, w x * (‖F x‖ * ‖G x‖)) + wNormSq w G := by
    unfold wNormSq
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun x _ => ?_
    have hn : ‖(F + G) x‖ ≤ ‖F x‖ + ‖G x‖ := norm_add_le _ _
    have hn2 : ‖(F + G) x‖ ^ 2 ≤ (‖F x‖ + ‖G x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    calc w x * ‖(F + G) x‖ ^ 2 ≤ w x * (‖F x‖ + ‖G x‖) ^ 2 :=
          mul_le_mul_of_nonneg_left hn2 (hw x)
      _ = w x * ‖F x‖ ^ 2 + 2 * (w x * (‖F x‖ * ‖G x‖)) + w x * ‖G x‖ ^ 2 := by ring
  have hsq : wNormSq w (F + G) ≤ (wNorm w F + wNorm w G) ^ 2 := by nlinarith
  have hnn : 0 ≤ wNorm w F + wNorm w G := add_nonneg (wNorm_nonneg _ _) (wNorm_nonneg _ _)
  calc wNorm w (F + G) = Real.sqrt (wNormSq w (F + G)) := rfl
    _ ≤ Real.sqrt ((wNorm w F + wNorm w G) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = wNorm w F + wNorm w G := Real.sqrt_sq hnn

/-- Cauchy's inequality for the weighted inner product. -/
theorem norm_wInner_le {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (F G : X → ℂ) :
    ‖wInner w F G‖ ≤ wNorm w F * wNorm w G := by
  have hcs : ∑ x, w x * (‖F x‖ * ‖G x‖) ≤ wNorm w F * wNorm w G :=
    sum_weight_mul_le w hw (fun x => ‖F x‖) (fun x => ‖G x‖) (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _)
  refine le_trans ?_ hcs
  unfold wInner
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw x), RCLike.norm_conj]

/-- A bound for the squares gives a bound for the norms. -/
theorem wNorm_le_of_wNormSq_le {w : X → ℝ} {F G : X → ℂ} {K : ℝ} (hK : 0 ≤ K)
    (h : wNormSq w F ≤ K ^ 2 * wNormSq w G) : wNorm w F ≤ K * wNorm w G := by
  unfold wNorm
  calc Real.sqrt (wNormSq w F) ≤ Real.sqrt (K ^ 2 * wNormSq w G) := Real.sqrt_le_sqrt h
    _ = K * Real.sqrt (wNormSq w G) := by
        rw [Real.sqrt_mul (sq_nonneg K), Real.sqrt_sq hK]

end Norms

/-! ### Operator bounds and Schur's test for row operators -/

section Schur

variable {X Ξ : Type*} [Fintype X] [Fintype Ξ]

/-- **An operator bound on a class of functions**: `‖T F‖ ≤ C ‖F‖` in `L²(X, m)` for every `F` of
the class `Sy`. With `Sy` the functions which are symmetric in the particle indices of the memory,
this is the operator norm on the Hilbert space `ℋ` of (eq:memory-hilbert-space). No supremum is
taken, so the statement does not depend on a convention for unbounded sets. -/
def OpBound (m : X → ℝ) (Sy : (X → ℂ) → Prop) (T : (X → ℂ) →ₗ[ℂ] (X → ℂ)) (C : ℝ) : Prop :=
  ∀ F : X → ℂ, Sy F → wNorm m (T F) ≤ C * wNorm m F

/-- **The weighted row condition `K w ≤ R w`** of (eq:weighted-schur) [S-02:0631–0633] for the
nonnegative row kernel with coefficients `κ s ξ` and targets `tgt s ξ`. -/
def RowBound (w : X → ℝ) (κ : X → Ξ → ℝ) (tgt : X → Ξ → X) (R : ℝ) : Prop :=
  ∀ s : X, ∑ ξ, κ s ξ * w (tgt s ξ) ≤ R * w s

/-- **The weighted column condition `K* w ≤ C w`** of (eq:weighted-schur) [S-02:0631–0633] for the
nonnegative row kernel `κ`, in the measure `m` and on the class `Sy` of real functions: for every
nonnegative `f` of the class, `∫ w · (K f) dm ≤ C ∫ w · f dm`. For the class of all functions and
`m > 0` this is `K* w ≤ C w` pointwise, with `K*` the adjoint in `L²(m)`; for the class of
functions symmetric in the particle indices it is the same inequality for the adjoint on the
symmetric space, which is how the paper uses "the factorial adjoint measures"
[S-02:0626–0629]. -/
def ColBound (m w : X → ℝ) (Sy : (X → ℝ) → Prop) (κ : X → Ξ → ℝ) (tgt : X → Ξ → X) (C : ℝ) :
    Prop :=
  ∀ f : X → ℝ, (∀ s, 0 ≤ f s) → Sy f →
    ∑ s, m s * w s * ∑ ξ, κ s ξ * f (tgt s ξ) ≤ C * ∑ s, m s * w s * f s

omit [Fintype X] in
theorem RowBound.mono {w : X → ℝ} {κ : X → Ξ → ℝ} {tgt : X → Ξ → X} {R R' : ℝ}
    (h : RowBound w κ tgt R) (hw : ∀ s, 0 ≤ w s) (hR : R ≤ R') : RowBound w κ tgt R' :=
  fun s => (h s).trans (mul_le_mul_of_nonneg_right hR (hw s))

/-- **Schur's test (eq:weighted-schur) for one function** [S-02:0631–0638]: if the nonnegative row
kernel `κ` dominates the coefficients, satisfies the row condition with the weight `w > 0`, and
satisfies the column inequality for the function `|F|²/w`, then
`‖rowOp coef tgt F‖² ≤ R C ‖F‖²` in `L²(m)`. -/
theorem rowOp_wNormSq_le (m w : X → ℝ) (hm : ∀ s, 0 ≤ m s) (hw : ∀ s, 0 < w s)
    (coef : X → Ξ → ℂ) (tgt : X → Ξ → X) (κ : X → Ξ → ℝ) (hκ : ∀ s ξ, ‖coef s ξ‖ ≤ κ s ξ)
    (R C : ℝ) (hR : 0 ≤ R) (hrow : RowBound w κ tgt R) (F : X → ℂ)
    (hcol : ∑ s, m s * w s * ∑ ξ, κ s ξ * (‖F (tgt s ξ)‖ ^ 2 / w (tgt s ξ)) ≤
      C * ∑ s, m s * w s * (‖F s‖ ^ 2 / w s)) :
    wNormSq m (rowOp coef tgt F) ≤ R * C * wNormSq m F := by
  have hκ0 : ∀ s ξ, 0 ≤ κ s ξ := fun s ξ => (norm_nonneg _).trans (hκ s ξ)
  have hpt : ∀ s, ‖rowOp coef tgt F s‖ ^ 2 ≤
      R * w s * ∑ ξ, κ s ξ * (‖F (tgt s ξ)‖ ^ 2 / w (tgt s ξ)) := by
    intro s
    have h1 : ‖rowOp coef tgt F s‖ ≤ ∑ ξ, κ s ξ * ‖F (tgt s ξ)‖ := by
      rw [rowOp_apply]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ξ _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hκ s ξ) (norm_nonneg _)
    have h2 := Graph.weighted_kernel_row_sq (fun ξ => κ s ξ) (fun ξ => w (tgt s ξ))
      (fun ξ => ‖F (tgt s ξ)‖) (fun ξ => hκ0 s ξ) (fun ξ => hw _)
    have h3 : (∑ ξ, κ s ξ * ‖F (tgt s ξ)‖ ^ 2 / w (tgt s ξ)) =
        ∑ ξ, κ s ξ * (‖F (tgt s ξ)‖ ^ 2 / w (tgt s ξ)) :=
      Finset.sum_congr rfl fun ξ _ => mul_div_assoc _ _ _
    have h4 : 0 ≤ ∑ ξ, κ s ξ * (‖F (tgt s ξ)‖ ^ 2 / w (tgt s ξ)) :=
      Finset.sum_nonneg fun ξ _ =>
        mul_nonneg (hκ0 s ξ) (div_nonneg (sq_nonneg _) (hw _).le)
    calc ‖rowOp coef tgt F s‖ ^ 2 ≤ (∑ ξ, κ s ξ * ‖F (tgt s ξ)‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ (∑ ξ, κ s ξ * w (tgt s ξ)) * ∑ ξ, κ s ξ * ‖F (tgt s ξ)‖ ^ 2 / w (tgt s ξ) := h2
      _ = (∑ ξ, κ s ξ * w (tgt s ξ)) * ∑ ξ, κ s ξ * (‖F (tgt s ξ)‖ ^ 2 / w (tgt s ξ)) := by
          rw [h3]
      _ ≤ R * w s * ∑ ξ, κ s ξ * (‖F (tgt s ξ)‖ ^ 2 / w (tgt s ξ)) :=
          mul_le_mul_of_nonneg_right (hrow s) h4
  calc wNormSq m (rowOp coef tgt F) = ∑ s, m s * ‖rowOp coef tgt F s‖ ^ 2 := rfl
    _ ≤ ∑ s, m s * (R * w s * ∑ ξ, κ s ξ * (‖F (tgt s ξ)‖ ^ 2 / w (tgt s ξ))) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hpt s) (hm s)
    _ = R * ∑ s, m s * w s * ∑ ξ, κ s ξ * (‖F (tgt s ξ)‖ ^ 2 / w (tgt s ξ)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
    _ ≤ R * (C * ∑ s, m s * w s * (‖F s‖ ^ 2 / w s)) := mul_le_mul_of_nonneg_left hcol hR
    _ = R * C * wNormSq m F := by
        unfold wNormSq
        rw [mul_assoc]
        congr 2
        refine Finset.sum_congr rfl fun s _ => ?_
        have hne := (hw s).ne'
        field_simp

/-- **Schur's test (eq:weighted-schur) for row operators** [S-02:0631–0638]: if a nonnegative row
kernel `κ` dominates the coefficients of `rowOp coef tgt` and satisfies the weighted row condition
with constant `R` and the weighted column condition with constant `C` on a class `SyR` of real
functions, then `‖rowOp coef tgt F‖ ≤ √(RC) ‖F‖` for every `F` whose function `|F|²/w` belongs to
that class. -/
theorem opBound_of_row_col (m w : X → ℝ) (hm : ∀ s, 0 ≤ m s) (hw : ∀ s, 0 < w s)
    (Sy : (X → ℂ) → Prop) (SyR : (X → ℝ) → Prop)
    (hSy : ∀ F, Sy F → SyR fun s => ‖F s‖ ^ 2 / w s)
    (coef : X → Ξ → ℂ) (tgt : X → Ξ → X) (κ : X → Ξ → ℝ) (hκ : ∀ s ξ, ‖coef s ξ‖ ≤ κ s ξ)
    (R C : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hrow : RowBound w κ tgt R)
    (hcol : ColBound m w SyR κ tgt C) :
    OpBound m Sy (rowOp coef tgt) (Real.sqrt (R * C)) := by
  intro F hF
  have h := rowOp_wNormSq_le m w hm hw coef tgt κ hκ R C hR hrow F
    (hcol (fun s => ‖F s‖ ^ 2 / w s) (fun s => div_nonneg (sq_nonneg _) (hw s).le) (hSy F hF))
  refine wNorm_le_of_wNormSq_le (Real.sqrt_nonneg _) ?_
  rwa [Real.sq_sqrt (mul_nonneg hR hC)]

end Schur

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
