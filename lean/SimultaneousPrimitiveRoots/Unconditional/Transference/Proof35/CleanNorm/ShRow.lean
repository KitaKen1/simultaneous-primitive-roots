module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.IdealSanity
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Schur.Pointwise
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.RowOps
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Lemma 3.10: row operations with the ideal transition law, Schur's test and adjoints

Source: `verification/stage7-sources/S-02.tex`, lines 981–999 (`[S-02:0981–0999]`).

"The ideal absolute row and column sums are at most `L^{C₁}` before these changes, since all its
unrestricted fresh laws are probabilities. Schur's test therefore bounds the density
perturbation …"

* `cleanShRow C Φ` — the row operation on the big label lists with the transition law of the
  ideal operator (shared labels retained, auxiliary labels and unshared target labels independent
  with the laws `μ_g`) and an arbitrary multiplier `Φ(source, auxiliary labels, target)`. The
  ideal row operation is the case `Φ = K_ν D_ℬ^{iζ} e(Θ D_ℬ)` (`clean_idealRow_eq`).
* `clean_detailed_balance` — "the shared product … unchanged on reversal": the measure of `ℋ_id`
  times the transition law is symmetric in source and target.
* `cleanShRow_opBound` — Schur's test in `L²(ℋ_id)` for a multiplier bounded by
  `c₀ α(source, aux) β(aux, target)`: the norm is at most `c₀ √(R R')`, where `R`, `R'` bound the
  expectations of `α` and of `β` over the auxiliary labels.
* `cleanShRow_adjoint` — the adjoint in `ℋ_id` has the multiplier `conj Φ(target, aux, source)`.
* `clean_wNorm_avg_le`, `clean_adjoint_bound`, `clean_wNorm_sum_le` — an average of
  measure-preserving substitutions is a contraction; an adjoint has the same bound; the triangle
  inequality for finite sums.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ### Generic lemmas on weighted norms -/

section Generic

variable {X : Type*} [Fintype X]

/-- A triple sum in the opposite order. -/
theorem clean_sum_comm3 {α β γ M : Type*} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M]
    (F : α → β → γ → M) : ∑ a, ∑ b, ∑ c, F a b c = ∑ c, ∑ b, ∑ a, F a b c := by
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans ?_
  exact Finset.sum_comm

/-- **An average of measure-preserving substitutions is a contraction** of `L²(X, m)`. -/
theorem clean_wNorm_avg_le {Pm : Type*} [Fintype Pm] [Nonempty Pm] {m : X → ℝ}
    (hm : ∀ x, 0 ≤ m x) (e : Pm → X ≃ X) (he : ∀ π x, m (e π x) = m x) (H : X → ℂ) :
    wNorm m (fun x => (Fintype.card Pm : ℂ)⁻¹ * ∑ π, H (e π x)) ≤ wNorm m H := by
  have hN : (0 : ℝ) < (Fintype.card Pm : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  have hpt : ∀ x, ‖(Fintype.card Pm : ℂ)⁻¹ * ∑ π, H (e π x)‖ ^ 2 ≤
      (Fintype.card Pm : ℝ)⁻¹ * ∑ π, ‖H (e π x)‖ ^ 2 := by
    intro x
    have h1 : ‖∑ π, H (e π x)‖ ≤ ∑ π, ‖H (e π x)‖ := norm_sum_le _ _
    have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset Pm))
      (f := fun π => ‖H (e π x)‖)
    rw [Finset.card_univ] at h2
    have h3 : ‖∑ π, H (e π x)‖ ^ 2 ≤ (Fintype.card Pm : ℝ) * ∑ π, ‖H (e π x)‖ ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
    rw [norm_mul, mul_pow, norm_inv, Complex.norm_natCast]
    calc ((Fintype.card Pm : ℝ)⁻¹) ^ 2 * ‖∑ π, H (e π x)‖ ^ 2
        ≤ ((Fintype.card Pm : ℝ)⁻¹) ^ 2 * ((Fintype.card Pm : ℝ) * ∑ π, ‖H (e π x)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
      _ = (Fintype.card Pm : ℝ)⁻¹ * ((Fintype.card Pm : ℝ)⁻¹ * (Fintype.card Pm : ℝ)) *
            ∑ π, ‖H (e π x)‖ ^ 2 := by ring
      _ = (Fintype.card Pm : ℝ)⁻¹ * ∑ π, ‖H (e π x)‖ ^ 2 := by
          rw [inv_mul_cancel₀ hN.ne', mul_one]
  have hπ : ∀ π : Pm, ∑ x, m x * ‖H (e π x)‖ ^ 2 = wNormSq m H := by
    intro π
    refine (Finset.sum_congr rfl fun x _ => ?_).trans
      (Equiv.sum_comp (e π) (fun x => m x * ‖H x‖ ^ 2))
    show m x * ‖H (e π x)‖ ^ 2 = m (e π x) * ‖H (e π x)‖ ^ 2
    rw [he]
  refine Real.sqrt_le_sqrt ?_
  calc wNormSq m (fun x => (Fintype.card Pm : ℂ)⁻¹ * ∑ π, H (e π x))
      = ∑ x, m x * ‖(Fintype.card Pm : ℂ)⁻¹ * ∑ π, H (e π x)‖ ^ 2 := rfl
    _ ≤ ∑ x, m x * ((Fintype.card Pm : ℝ)⁻¹ * ∑ π, ‖H (e π x)‖ ^ 2) :=
        Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hpt x) (hm x)
    _ = (Fintype.card Pm : ℝ)⁻¹ * ∑ π, ∑ x, m x * ‖H (e π x)‖ ^ 2 := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun x _ => ?_
        ring
    _ = (Fintype.card Pm : ℝ)⁻¹ * ∑ _π : Pm, wNormSq m H := by
        rw [Finset.sum_congr rfl fun π _ => hπ π]
    _ = wNormSq m H := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          inv_mul_cancel₀ hN.ne', one_mul]

/-- **An adjoint has the same bound.** -/
theorem clean_adjoint_bound {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (T T' : (X → ℂ) → (X → ℂ)) {C : ℝ}
    (hC : 0 ≤ C) (hadj : ∀ f g, wInner w (T' f) g = wInner w f (T g))
    (hT : ∀ g, wNorm w (T g) ≤ C * wNorm w g) (f : X → ℂ) :
    wNorm w (T' f) ≤ C * wNorm w f := by
  have h1 : ((wNormSq w (T' f) : ℝ) : ℂ) = wInner w f (T (T' f)) := by
    rw [← wInner_self, hadj]
  have h2 : wNormSq w (T' f) ≤ wNorm w f * wNorm w (T (T' f)) := by
    have h3 := norm_wInner_le hw f (T (T' f))
    rw [← h1, Complex.norm_real, Real.norm_of_nonneg (wNormSq_nonneg hw _)] at h3
    exact h3
  have h4 : wNorm w (T' f) * wNorm w (T' f) ≤ (C * wNorm w f) * wNorm w (T' f) := by
    rw [← sq, wNorm_sq hw]
    calc wNormSq w (T' f) ≤ wNorm w f * wNorm w (T (T' f)) := h2
      _ ≤ wNorm w f * (C * wNorm w (T' f)) :=
          mul_le_mul_of_nonneg_left (hT _) (wNorm_nonneg _ _)
      _ = (C * wNorm w f) * wNorm w (T' f) := by ring
  rcases (wNorm_nonneg w (T' f)).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact mul_nonneg hC (wNorm_nonneg _ _)
  · exact le_of_mul_le_mul_right h4 hpos

/-- The triangle inequality for a finite sum. -/
theorem clean_wNorm_sum_le {ι : Type*} {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (s : Finset ι)
    (F : ι → X → ℂ) : wNorm w (∑ i ∈ s, F i) ≤ ∑ i ∈ s, wNorm w (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h0 : wNorm w (0 : X → ℂ) = 0 := by
      unfold wNorm wNormSq
      simp
    rw [Finset.sum_empty, Finset.sum_empty]
    exact le_of_eq h0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (wNorm_add_le hw _ _).trans (add_le_add (le_refl _) ih)

end Generic

/-! ### Row operations with the ideal transition law -/

section ShRow

variable {B : Type} [Fintype B] [DecidableEq B] {big : B → Finset ℕ} {J ℓ : ℕ}

open _root_.Classical in
/-- **The row operation with the ideal transition law and the multiplier `Φ`**: from the source
list `x`, with auxiliary labels `r` of law `⊗ μ_g`, to the target lists `x'` which retain the
shared labels of `x` and have independent unshared labels of law `μ_g`. -/
def cleanShRow (C : B → Finset (Fin J))
    (Φ : LabelList big J ℓ → AuxList big C → LabelList big J ℓ → ℂ) :
    (LabelList big J ℓ → ℂ) →ₗ[ℂ] (LabelList big J ℓ → ℂ) :=
  rowOp (Ξ := AuxList big C × LabelList big J ℓ)
    (fun x ξ => if SharedBig C x ξ.2 then
      ((auxWeight big C ξ.1 * unsharedWeight big C ξ.2 : ℝ) : ℂ) * Φ x ξ.1 ξ.2 else 0)
    (fun _ ξ => ξ.2)

open _root_.Classical in
theorem cleanShRow_apply (C : B → Finset (Fin J))
    (Φ : LabelList big J ℓ → AuxList big C → LabelList big J ℓ → ℂ)
    (g : LabelList big J ℓ → ℂ) (x : LabelList big J ℓ) :
    cleanShRow C Φ g x = ∑ r : AuxList big C, ∑ x' : LabelList big J ℓ,
      (if SharedBig C x x' then
        ((auxWeight big C r * unsharedWeight big C x' : ℝ) : ℂ) * Φ x r x' else 0) * g x' := by
  unfold cleanShRow
  rw [rowOp_apply]
  exact Fintype.sum_prod_type _

/-- The ideal row operation of a pattern is `cleanShRow` with the ideal multiplier. -/
theorem clean_idealRow_eq (ν : Pattern big J ℓ) (ζ Θ : ℝ) :
    idealRow ν ζ Θ =
      cleanShRow ν.C (fun x r x' => ν.K x x' r * dilPhase ζ Θ (bigDil ν.C x r)) := rfl

open _root_.Classical in
/-- The row operation is additive in the multiplier. -/
theorem cleanShRow_add (C : B → Finset (Fin J))
    (Φ₁ Φ₂ : LabelList big J ℓ → AuxList big C → LabelList big J ℓ → ℂ) :
    cleanShRow C (fun x r x' => Φ₁ x r x' + Φ₂ x r x') = cleanShRow C Φ₁ + cleanShRow C Φ₂ := by
  refine LinearMap.ext fun g => funext fun x => ?_
  rw [LinearMap.add_apply, Pi.add_apply, cleanShRow_apply, cleanShRow_apply, cleanShRow_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x' _ => ?_
  split_ifs
  · ring
  · ring

open _root_.Classical in
/-- The row operation is homogeneous in the multiplier. -/
theorem cleanShRow_smul (C : B → Finset (Fin J)) (c : ℂ)
    (Φ : LabelList big J ℓ → AuxList big C → LabelList big J ℓ → ℂ) :
    cleanShRow C (fun x r x' => c * Φ x r x') = c • cleanShRow C Φ := by
  refine LinearMap.ext fun g => funext fun x => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, cleanShRow_apply, cleanShRow_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x' _ => ?_
  split_ifs
  · ring
  · ring

omit [Fintype B] [DecidableEq B] in
theorem clean_sharedBig_symm {C : B → Finset (Fin J)} {x x' : LabelList big J ℓ}
    (h : SharedBig C x x') : SharedBig C x' x := fun g i hi => (h g i hi).symm

omit [DecidableEq B] in
theorem clean_unsharedWeight_nonneg (C : B → Finset (Fin J)) (x' : LabelList big J ℓ) :
    0 ≤ unsharedWeight big C x' := by
  unfold unsharedWeight
  refine Finset.prod_nonneg fun g _ => mul_nonneg (Finset.prod_nonneg fun i _ => ?_)
    (Finset.prod_nonneg fun j _ => Schur.primeGroupLaw_nonneg _ _)
  split_ifs
  · exact Schur.primeGroupLaw_nonneg _ _
  · exact zero_le_one

omit [DecidableEq B] in
theorem clean_idealWeight_nonneg (x : LabelList big J ℓ) : 0 ≤ idealWeight big J ℓ x := by
  unfold idealWeight
  exact Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun i _ =>
    Schur.primeGroupLaw_nonneg _ _

omit [DecidableEq B] in
/-- **Detailed balance of the ideal transition law** ("the shared product … unchanged on
reversal", [S-02:0122–0127]): for lists with the same shared labels, the measure of the source
times the law of the unshared labels of the target is symmetric. -/
theorem clean_detailed_balance (C : B → Finset (Fin J)) {x x' : LabelList big J ℓ}
    (h : SharedBig C x x') :
    idealWeight big J ℓ x * unsharedWeight big C x' =
      idealWeight big J ℓ x' * unsharedWeight big C x := by
  unfold idealWeight unsharedWeight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  have hi : (∏ i : Fin J, Graph.primeGroupLaw (big g) (x g (Sum.inl i))) *
        (∏ i : Fin J, if i ∈ C g then Graph.primeGroupLaw (big g) (x' g (Sum.inl i)) else 1) =
      (∏ i : Fin J, Graph.primeGroupLaw (big g) (x' g (Sum.inl i))) *
        ∏ i : Fin J, if i ∈ C g then Graph.primeGroupLaw (big g) (x g (Sum.inl i)) else 1 := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hc : i ∈ C g
    · rw [if_pos hc, if_pos hc, mul_comm]
    · rw [if_neg hc, if_neg hc, h g i hc]
  linear_combination
    ((∏ j : Fin ℓ, Graph.primeGroupLaw (big g) (x g (Sum.inr j))) *
      ∏ j : Fin ℓ, Graph.primeGroupLaw (big g) (x' g (Sum.inr j))) * hi

open _root_.Classical in
/-- Given the target list, the source lists with the same shared labels and independent unshared
labels have total probability one. -/
theorem clean_sum_shared_col (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (C : B → Finset (Fin J)) (x' : LabelList big J ℓ) :
    ∑ x : LabelList big J ℓ, (if SharedBig C x x' then unsharedWeight big C x else 0) = 1 := by
  rw [← sum_shared_unsharedWeight hlaw C x']
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : SharedBig C x x'
  · rw [if_pos h, if_pos (clean_sharedBig_symm h)]
  · rw [if_neg h, if_neg fun h' => h (clean_sharedBig_symm h')]

open _root_.Classical in
/-- **Schur's test for a row operation with the ideal transition law** [S-02:0993–0996]: if the
multiplier is bounded by `c₀ α(x, r) β(r, x')` with `0 ≤ α, β ≤ 1`, and the expectations of `α`
and of `β` over the auxiliary labels are at most `R` and `R'`, then the row operation has norm at
most `c₀ √(R R')` on `ℋ_id`. -/
theorem cleanShRow_opBound (hlaw : ∀ g, ∑ q ∈ big g, Graph.primeGroupLaw (big g) q = 1)
    (C : B → Finset (Fin J))
    (Φ : LabelList big J ℓ → AuxList big C → LabelList big J ℓ → ℂ)
    (α : LabelList big J ℓ → AuxList big C → ℝ) (β : AuxList big C → LabelList big J ℓ → ℝ)
    {c₀ R R' : ℝ} (hc₀ : 0 ≤ c₀) (hα0 : ∀ x r, 0 ≤ α x r) (hα1 : ∀ x r, α x r ≤ 1)
    (hβ0 : ∀ r x, 0 ≤ β r x) (hβ1 : ∀ r x, β r x ≤ 1)
    (hΦ : ∀ x r x', ‖Φ x r x'‖ ≤ c₀ * (α x r * β r x'))
    (hR0 : 0 ≤ R) (hR : ∀ x, ∑ r, auxWeight big C r * α x r ≤ R)
    (hR'0 : 0 ≤ R') (hR' : ∀ x', ∑ r, auxWeight big C r * β r x' ≤ R')
    (g : LabelList big J ℓ → ℂ) :
    wNorm (idealWeight big J ℓ) (cleanShRow C Φ g) ≤
      c₀ * Real.sqrt (R * R') * wNorm (idealWeight big J ℓ) g := by
  obtain ⟨κ, hκdef⟩ : ∃ κ : LabelList big J ℓ → AuxList big C × LabelList big J ℓ → ℝ,
      κ = fun x ξ => if SharedBig C x ξ.2 then
        auxWeight big C ξ.1 * unsharedWeight big C ξ.2 * (c₀ * (α x ξ.1 * β ξ.1 ξ.2))
        else 0 := ⟨_, rfl⟩
  have hκv : ∀ (x : LabelList big J ℓ) (r : AuxList big C) (x' : LabelList big J ℓ),
      κ x (r, x') = if SharedBig C x x' then
        auxWeight big C r * unsharedWeight big C x' * (c₀ * (α x r * β r x')) else 0 := by
    intro x r x'
    rw [hκdef]
  have haux0 : ∀ r : AuxList big C, 0 ≤ auxWeight big C r := fun r =>
    Schur.auxWeight_nonneg big C r
  have hun0 : ∀ x' : LabelList big J ℓ, 0 ≤ unsharedWeight big C x' := fun x' =>
    clean_unsharedWeight_nonneg C x'
  have hm0 : ∀ x : LabelList big J ℓ, 0 ≤ idealWeight big J ℓ x := fun x =>
    clean_idealWeight_nonneg x
  have hκ : ∀ (x : LabelList big J ℓ) (ξ : AuxList big C × LabelList big J ℓ),
      ‖(if SharedBig C x ξ.2 then
        ((auxWeight big C ξ.1 * unsharedWeight big C ξ.2 : ℝ) : ℂ) * Φ x ξ.1 ξ.2 else 0)‖ ≤
        κ x ξ := by
    intro x ξ
    obtain ⟨r, x'⟩ := ξ
    rw [hκv]
    show ‖(if SharedBig C x x' then
        ((auxWeight big C r * unsharedWeight big C x' : ℝ) : ℂ) * Φ x r x' else 0)‖ ≤ _
    split_ifs with h
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (haux0 r) (hun0 x'))]
      exact mul_le_mul_of_nonneg_left (hΦ x r x') (mul_nonneg (haux0 r) (hun0 x'))
    · exact le_of_eq norm_zero
  have hrow : RowBound (fun _ : LabelList big J ℓ => (1 : ℝ)) κ (fun _ ξ => ξ.2) (c₀ * R) := by
    intro x
    have h1 : ∀ r : AuxList big C,
        ∑ x' : LabelList big J ℓ, κ x (r, x') * 1 ≤ c₀ * (auxWeight big C r * α x r) := by
      intro r
      calc ∑ x' : LabelList big J ℓ, κ x (r, x') * 1
          ≤ ∑ x' : LabelList big J ℓ,
              (if SharedBig C x x' then unsharedWeight big C x' else 0) *
                (c₀ * (auxWeight big C r * α x r)) := by
            refine Finset.sum_le_sum fun x' _ => ?_
            rw [hκv, mul_one]
            split_ifs with h
            · have h2 : α x r * β r x' ≤ α x r :=
                mul_le_of_le_one_right (hα0 x r) (hβ1 r x')
              calc auxWeight big C r * unsharedWeight big C x' * (c₀ * (α x r * β r x'))
                  = unsharedWeight big C x' *
                      (c₀ * (auxWeight big C r * (α x r * β r x'))) := by ring
                _ ≤ unsharedWeight big C x' * (c₀ * (auxWeight big C r * α x r)) :=
                    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_left h2 (haux0 r)) hc₀) (hun0 x')
            · exact le_of_eq (zero_mul _).symm
        _ = c₀ * (auxWeight big C r * α x r) := by
            rw [← Finset.sum_mul, sum_shared_unsharedWeight hlaw C x, one_mul]
    show ∑ ξ : AuxList big C × LabelList big J ℓ, κ x ξ * 1 ≤ c₀ * R * 1
    rw [Fintype.sum_prod_type, mul_one]
    calc ∑ r : AuxList big C, ∑ x' : LabelList big J ℓ, κ x (r, x') * 1
        ≤ ∑ r : AuxList big C, c₀ * (auxWeight big C r * α x r) :=
          Finset.sum_le_sum fun r _ => h1 r
      _ = c₀ * ∑ r : AuxList big C, auxWeight big C r * α x r := (Finset.mul_sum _ _ _).symm
      _ ≤ c₀ * R := mul_le_mul_of_nonneg_left (hR x) hc₀
  have hcol : ColBound (idealWeight big J ℓ) (fun _ : LabelList big J ℓ => (1 : ℝ))
      (fun _ => True) κ (fun _ ξ => ξ.2) (c₀ * R') := by
    intro f hf0 _
    have hT : ∀ (x : LabelList big J ℓ) (r : AuxList big C) (x' : LabelList big J ℓ),
        idealWeight big J ℓ x * (κ x (r, x') * f x') ≤
          (if SharedBig C x x' then unsharedWeight big C x else 0) *
            (idealWeight big J ℓ x' * f x' * (c₀ * (auxWeight big C r * β r x'))) := by
      intro x r x'
      rw [hκv]
      split_ifs with h
      · have hdb := clean_detailed_balance C h
        have h2 : α x r * β r x' ≤ β r x' := mul_le_of_le_one_left (hβ0 r x') (hα1 x r)
        calc idealWeight big J ℓ x *
              (auxWeight big C r * unsharedWeight big C x' * (c₀ * (α x r * β r x')) * f x')
            = (idealWeight big J ℓ x * unsharedWeight big C x') *
                (f x' * (c₀ * (auxWeight big C r * (α x r * β r x')))) := by ring
          _ = (idealWeight big J ℓ x' * unsharedWeight big C x) *
                (f x' * (c₀ * (auxWeight big C r * (α x r * β r x')))) := by rw [hdb]
          _ ≤ (idealWeight big J ℓ x' * unsharedWeight big C x) *
                (f x' * (c₀ * (auxWeight big C r * β r x'))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left h2 (haux0 r)) hc₀) (hf0 x'))
                (mul_nonneg (hm0 x') (hun0 x))
          _ = unsharedWeight big C x *
                (idealWeight big J ℓ x' * f x' * (c₀ * (auxWeight big C r * β r x'))) := by ring
      · simp
    have hL : ∑ x : LabelList big J ℓ, idealWeight big J ℓ x * 1 *
          ∑ ξ : AuxList big C × LabelList big J ℓ, κ x ξ * f ξ.2 =
        ∑ x : LabelList big J ℓ, ∑ r : AuxList big C, ∑ x' : LabelList big J ℓ,
          idealWeight big J ℓ x * (κ x (r, x') * f x') := by
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_one, Fintype.sum_prod_type, Finset.mul_sum]
      exact Finset.sum_congr rfl fun r _ => Finset.mul_sum _ _ _
    have hM : ∑ x : LabelList big J ℓ, ∑ r : AuxList big C, ∑ x' : LabelList big J ℓ,
          (if SharedBig C x x' then unsharedWeight big C x else 0) *
            (idealWeight big J ℓ x' * f x' * (c₀ * (auxWeight big C r * β r x'))) =
        ∑ x' : LabelList big J ℓ, ∑ r : AuxList big C,
          idealWeight big J ℓ x' * f x' * (c₀ * (auxWeight big C r * β r x')) := by
      refine (clean_sum_comm3 (fun (x : LabelList big J ℓ) (r : AuxList big C)
        (x' : LabelList big J ℓ) =>
          (if SharedBig C x x' then unsharedWeight big C x else 0) *
            (idealWeight big J ℓ x' * f x' * (c₀ * (auxWeight big C r * β r x'))))).trans ?_
      refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun r _ => ?_
      show ∑ x : LabelList big J ℓ, (if SharedBig C x x' then unsharedWeight big C x else 0) *
          (idealWeight big J ℓ x' * f x' * (c₀ * (auxWeight big C r * β r x'))) =
        idealWeight big J ℓ x' * f x' * (c₀ * (auxWeight big C r * β r x'))
      rw [← Finset.sum_mul, clean_sum_shared_col hlaw C x', one_mul]
    show ∑ x : LabelList big J ℓ, idealWeight big J ℓ x * 1 *
        ∑ ξ : AuxList big C × LabelList big J ℓ, κ x ξ * f ξ.2 ≤
      c₀ * R' * ∑ x : LabelList big J ℓ, idealWeight big J ℓ x * 1 * f x
    calc ∑ x : LabelList big J ℓ, idealWeight big J ℓ x * 1 *
          ∑ ξ : AuxList big C × LabelList big J ℓ, κ x ξ * f ξ.2
        = ∑ x : LabelList big J ℓ, ∑ r : AuxList big C, ∑ x' : LabelList big J ℓ,
            idealWeight big J ℓ x * (κ x (r, x') * f x') := hL
      _ ≤ ∑ x : LabelList big J ℓ, ∑ r : AuxList big C, ∑ x' : LabelList big J ℓ,
            (if SharedBig C x x' then unsharedWeight big C x else 0) *
              (idealWeight big J ℓ x' * f x' * (c₀ * (auxWeight big C r * β r x'))) :=
          Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun r _ =>
            Finset.sum_le_sum fun x' _ => hT x r x'
      _ = ∑ x' : LabelList big J ℓ, ∑ r : AuxList big C,
            idealWeight big J ℓ x' * f x' * (c₀ * (auxWeight big C r * β r x')) := hM
      _ ≤ ∑ x' : LabelList big J ℓ, c₀ * R' * (idealWeight big J ℓ x' * 1 * f x') := by
          refine Finset.sum_le_sum fun x' _ => ?_
          rw [← Finset.mul_sum, ← Finset.mul_sum, mul_one]
          calc idealWeight big J ℓ x' * f x' * (c₀ * ∑ r : AuxList big C,
                auxWeight big C r * β r x')
              ≤ idealWeight big J ℓ x' * f x' * (c₀ * R') :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hR' x') hc₀)
                  (mul_nonneg (hm0 x') (hf0 x'))
            _ = c₀ * R' * (idealWeight big J ℓ x' * f x') := by ring
      _ = c₀ * R' * ∑ x : LabelList big J ℓ, idealWeight big J ℓ x * 1 * f x :=
          (Finset.mul_sum _ _ _).symm
  have hop := opBound_of_row_col (idealWeight big J ℓ) (fun _ => (1 : ℝ)) hm0
    (fun _ => one_pos) (fun _ : LabelList big J ℓ → ℂ => True)
    (fun _ : LabelList big J ℓ → ℝ => True) (fun _ _ => trivial)
    (fun x ξ => if SharedBig C x ξ.2 then
      ((auxWeight big C ξ.1 * unsharedWeight big C ξ.2 : ℝ) : ℂ) * Φ x ξ.1 ξ.2 else 0)
    (fun _ ξ => ξ.2) κ hκ (c₀ * R) (c₀ * R') (mul_nonneg hc₀ hR0) (mul_nonneg hc₀ hR'0)
    hrow hcol g trivial
  have hsqrt : Real.sqrt (c₀ * R * (c₀ * R')) = c₀ * Real.sqrt (R * R') := by
    have e : c₀ * R * (c₀ * R') = c₀ ^ 2 * (R * R') := by ring
    rw [e, Real.sqrt_mul (sq_nonneg c₀), Real.sqrt_sq hc₀]
  rw [hsqrt] at hop
  exact hop

open _root_.Classical in
/-- **The adjoint in `ℋ_id` of a row operation with the ideal transition law**: its multiplier is
the conjugate of the multiplier with source and target interchanged ("the adjoint … interchanges
source and target labels in the coefficient, and conjugates the multiplier", [S-02:0120–0122]). -/
theorem cleanShRow_adjoint (C : B → Finset (Fin J))
    (Φ : LabelList big J ℓ → AuxList big C → LabelList big J ℓ → ℂ)
    (f g : LabelList big J ℓ → ℂ) :
    wInner (idealWeight big J ℓ) (cleanShRow C (fun x r x' => conj (Φ x' r x)) f) g =
      wInner (idealWeight big J ℓ) f (cleanShRow C Φ g) := by
  have hL : wInner (idealWeight big J ℓ) (cleanShRow C (fun x r x' => conj (Φ x' r x)) f) g =
      ∑ x : LabelList big J ℓ, ∑ r : AuxList big C, ∑ x' : LabelList big J ℓ,
        (if SharedBig C x x' then
          ((idealWeight big J ℓ x * (auxWeight big C r * unsharedWeight big C x') : ℝ) : ℂ) *
            (Φ x' r x * (conj (f x') * g x)) else 0) := by
    unfold wInner
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [cleanShRow_apply, map_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x' _ => ?_
    split_ifs with h
    · simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
      push_cast
      ring
    · simp
  have hR : wInner (idealWeight big J ℓ) f (cleanShRow C Φ g) =
      ∑ x' : LabelList big J ℓ, ∑ r : AuxList big C, ∑ x : LabelList big J ℓ,
        (if SharedBig C x' x then
          ((idealWeight big J ℓ x' * (auxWeight big C r * unsharedWeight big C x) : ℝ) : ℂ) *
            (Φ x' r x * (conj (f x') * g x)) else 0) := by
    unfold wInner
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [cleanShRow_apply, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with h
    · push_cast
      ring
    · simp
  rw [hL, hR]
  refine Eq.trans ?_ (clean_sum_comm3 (fun (x' : LabelList big J ℓ) (r : AuxList big C)
    (x : LabelList big J ℓ) =>
      (if SharedBig C x' x then
        ((idealWeight big J ℓ x' * (auxWeight big C r * unsharedWeight big C x) : ℝ) : ℂ) *
          (Φ x' r x * (conj (f x') * g x)) else 0))).symm
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun r _ =>
    Finset.sum_congr rfl fun x' _ => ?_
  show (if SharedBig C x x' then
      ((idealWeight big J ℓ x * (auxWeight big C r * unsharedWeight big C x') : ℝ) : ℂ) *
        (Φ x' r x * (conj (f x') * g x)) else 0) =
    (if SharedBig C x' x then
      ((idealWeight big J ℓ x' * (auxWeight big C r * unsharedWeight big C x) : ℝ) : ℂ) *
        (Φ x' r x * (conj (f x') * g x)) else 0)
  by_cases h : SharedBig C x x'
  · have h' := clean_sharedBig_symm h
    have hdb := clean_detailed_balance C h
    have e : idealWeight big J ℓ x * (auxWeight big C r * unsharedWeight big C x') =
        idealWeight big J ℓ x' * (auxWeight big C r * unsharedWeight big C x) := by
      linear_combination (auxWeight big C r) * hdb
    rw [if_pos h, if_pos h', e]
  · have h' : ¬SharedBig C x' x := fun h'' => h (clean_sharedBig_symm h'')
    rw [if_neg h, if_neg h']

end ShRow

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
