module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.RowOps
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Products of row actions over the big groups

Source: `verification/stage7-sources/S-02.tex`, lines 456–459 (`[S-02:0456–0459]`): "the ghost
operation `G_i` is the product over big groups of the following row action, leaving every other
coordinate fixed".

Finite, purely algebraic statements about functions on a product `∏_g X_g` of finite types (in the
application `X_g` is the set of the memories of the big group `g`).

* `tensor_rows` — if, in every coordinate `g`, the weighted family of targets `(a_g, t_g)` and the
  kernel `k_g` act in the same way on the functions `u ↦ F(x with u in the coordinate g)`, then
  `∑_i ∏_g a_g(i_g) F(t_g(i_g))_g = ∑_x ∏_g k_g(x_g) F(x)`. The function `F` need not be a product;
  this is how the one-group identity `GhostRowCompat`, which holds on symmetric functions only, is
  used for a function of all memories which is symmetric in each of them.
* `tensor_col_le` — the product of the one-coordinate column inequalities
  `∑_u M_g(u) K_g(u, y) ≤ C_g M_g(y)`.

The proof of `tensor_rows` replaces one coordinate at a time (`sum_replace_coord`); a coordinate is
isolated in a sum over `∏_g X_g` by the involution `(x, u) ↦ (x[a ↦ u], x_a)` (`updateSwap`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-- The involution `(x, u) ↦ (x[a ↦ u], x_a)` of `(∏_g X_g) × X_a`. -/
def updateSwap {B : Type*} [DecidableEq B] {X : B → Type*} (a : B) :
    ((∀ g, X g) × X a) ≃ ((∀ g, X g) × X a) where
  toFun p := (Function.update p.1 a p.2, p.1 a)
  invFun p := (Function.update p.1 a p.2, p.1 a)
  left_inv p := by
    refine Prod.ext ?_ ?_
    · show Function.update (Function.update p.1 a p.2) a (p.1 a) = p.1
      rw [Function.update_idem, Function.update_eq_self]
    · show Function.update p.1 a p.2 a = p.2
      rw [Function.update_self]
  right_inv p := by
    refine Prod.ext ?_ ?_
    · show Function.update (Function.update p.1 a p.2) a (p.1 a) = p.1
      rw [Function.update_idem, Function.update_eq_self]
    · show Function.update p.1 a p.2 a = p.2
      rw [Function.update_self]

/-- A sum over `∏_g X_g` with the coordinate `a` isolated: for `R` independent of that
coordinate, `|X_a| ∑_x m(x_a) R(x) F(x) = ∑_x R(x) ∑_u m(u) F(x[a ↦ u])`. -/
theorem sum_coord_swap {B : Type*} [Fintype B] [DecidableEq B] {X : B → Type*}
    [∀ g, Fintype (X g)] (a : B) (m : X a → ℝ) (R F : (∀ g, X g) → ℝ)
    (hR : ∀ (x : ∀ g, X g) (u : X a), R (Function.update x a u) = R x) :
    (Fintype.card (X a) : ℝ) * ∑ x : ∀ g, X g, m (x a) * R x * F x =
      ∑ x : ∀ g, X g, R x * ∑ u : X a, m u * F (Function.update x a u) := by
  have h1 : (Fintype.card (X a) : ℝ) * ∑ x : ∀ g, X g, m (x a) * R x * F x =
      ∑ p : (∀ g, X g) × X a, m (p.1 a) * R p.1 * F p.1 := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    show _ = ∑ _u : X a, m (x a) * R x * F x
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h2 : ∑ p : (∀ g, X g) × X a, m (p.1 a) * R p.1 * F p.1 =
      ∑ q : (∀ g, X g) × X a, m q.2 * R q.1 * F (Function.update q.1 a q.2) := by
    refine Fintype.sum_equiv (updateSwap a) _ _ fun p => ?_
    show m (p.1 a) * R p.1 * F p.1 =
      m (p.1 a) * R (Function.update p.1 a p.2) *
        F (Function.update (Function.update p.1 a p.2) a (p.1 a))
    rw [hR, Function.update_idem, Function.update_eq_self]
  rw [h1, h2, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  show m u * R x * F (Function.update x a u) = R x * (m u * F (Function.update x a u))
  ring

/-- **Replacement of one coordinate**: if `m` and `m'` integrate the functions
`u ↦ F(x[a ↦ u])` in the same way, they may be exchanged in a sum over `∏_g X_g` against a
factor `R` which does not depend on the coordinate `a`. -/
theorem sum_replace_coord {B : Type*} [Fintype B] [DecidableEq B] {X : B → Type*}
    [∀ g, Fintype (X g)] [∀ g, Nonempty (X g)] (a : B) (m m' : X a → ℝ)
    (R F : (∀ g, X g) → ℝ)
    (hR : ∀ (x : ∀ g, X g) (u : X a), R (Function.update x a u) = R x)
    (h : ∀ x : ∀ g, X g, ∑ u : X a, m u * F (Function.update x a u) =
      ∑ u : X a, m' u * F (Function.update x a u)) :
    ∑ x : ∀ g, X g, m (x a) * R x * F x = ∑ x : ∀ g, X g, m' (x a) * R x * F x := by
  have hN : (Fintype.card (X a) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have e : (Fintype.card (X a) : ℝ) * ∑ x : ∀ g, X g, m (x a) * R x * F x =
      (Fintype.card (X a) : ℝ) * ∑ x : ∀ g, X g, m' (x a) * R x * F x := by
    rw [sum_coord_swap a m R F hR, sum_coord_swap a m' R F hR]
    exact Finset.sum_congr rfl fun x _ => congrArg (fun t => R x * t) (h x)
  exact mul_left_cancel₀ hN e

/-- **Replacement of all coordinates**: if for every coordinate `g` the weights `μ_g` and `k_g`
integrate the functions `u ↦ F(x[g ↦ u])` in the same way, then
`∑_x ∏_g μ_g(x_g) F(x) = ∑_x ∏_g k_g(x_g) F(x)`. -/
theorem tensor_replace {B : Type*} [Fintype B] [DecidableEq B] {X : B → Type*}
    [∀ g, Fintype (X g)] [∀ g, Nonempty (X g)] (μ k : ∀ g, X g → ℝ) (F : (∀ g, X g) → ℝ)
    (h : ∀ (g : B) (x : ∀ g, X g), ∑ u : X g, μ g u * F (Function.update x g u) =
      ∑ u : X g, k g u * F (Function.update x g u)) :
    ∑ x : ∀ g, X g, (∏ g, μ g (x g)) * F x = ∑ x : ∀ g, X g, (∏ g, k g (x g)) * F x := by
  have key : ∀ T : Finset B,
      ∑ x : ∀ g, X g, (∏ g, (if g ∈ T then k g (x g) else μ g (x g))) * F x =
        ∑ x : ∀ g, X g, (∏ g, μ g (x g)) * F x := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      refine Finset.sum_congr rfl fun x _ => congrArg (fun t => t * F x) ?_
      exact Finset.prod_congr rfl fun g _ => if_neg (Finset.notMem_empty g)
    | insert a T ha ih =>
      obtain ⟨R, hRdef⟩ : ∃ R : (∀ g, X g) → ℝ, ∀ x, R x =
          ∏ g ∈ Finset.univ.erase a, (if g ∈ T then k g (x g) else μ g (x g)) :=
        ⟨_, fun _ => rfl⟩
      have hR : ∀ (x : ∀ g, X g) (u : X a), R (Function.update x a u) = R x := by
        intro x u
        rw [hRdef, hRdef]
        refine Finset.prod_congr rfl fun g hg => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hg)]
      have h1 : ∀ x : ∀ g, X g,
          (∏ g, (if g ∈ insert a T then k g (x g) else μ g (x g))) = k a (x a) * R x := by
        intro x
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a),
          if_pos (Finset.mem_insert_self a T), hRdef]
        refine congrArg (fun t => k a (x a) * t) (Finset.prod_congr rfl fun g hg => ?_)
        have hga : g ≠ a := Finset.ne_of_mem_erase hg
        by_cases hgT : g ∈ T
        · rw [if_pos hgT, if_pos (Finset.mem_insert_of_mem hgT)]
        · rw [if_neg hgT, if_neg fun h => (Finset.mem_insert.mp h).elim hga hgT]
      have h2 : ∀ x : ∀ g, X g,
          (∏ g, (if g ∈ T then k g (x g) else μ g (x g))) = μ a (x a) * R x := by
        intro x
        rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ a), if_neg ha, hRdef]
      calc ∑ x : ∀ g, X g, (∏ g, (if g ∈ insert a T then k g (x g) else μ g (x g))) * F x
          = ∑ x : ∀ g, X g, k a (x a) * R x * F x :=
            Finset.sum_congr rfl fun x _ => congrArg (fun t => t * F x) (h1 x)
        _ = ∑ x : ∀ g, X g, μ a (x a) * R x * F x :=
            sum_replace_coord a (k a) (μ a) R F hR fun x => (h a x).symm
        _ = ∑ x : ∀ g, X g, (∏ g, (if g ∈ T then k g (x g) else μ g (x g))) * F x :=
            Finset.sum_congr rfl fun x _ => congrArg (fun t => t * F x) (h2 x).symm
        _ = ∑ x : ∀ g, X g, (∏ g, μ g (x g)) * F x := ih
  have h3 : ∑ x : ∀ g, X g, (∏ g, k g (x g)) * F x =
      ∑ x : ∀ g, X g,
        (∏ g, (if g ∈ (Finset.univ : Finset B) then k g (x g) else μ g (x g))) * F x :=
    Finset.sum_congr rfl fun x _ => congrArg (fun t => t * F x)
      (Finset.prod_congr rfl fun g _ => (if_pos (Finset.mem_univ g)).symm)
  exact (h3.trans (key Finset.univ)).symm

open _root_.Classical in
/-- **The product of row actions**: let `(a_g, t_g)` be, for every coordinate `g`, a finite
weighted family of points of `X_g`, and `k_g` a weight on `X_g`, such that
`∑_i a_g(i) F(x[g ↦ t_g(i)]) = ∑_u k_g(u) F(x[g ↦ u])` for all `x`. Then
`∑_{(i_g)} ∏_g a_g(i_g) F((t_g(i_g))_g) = ∑_x ∏_g k_g(x_g) F(x)`. -/
theorem tensor_rows {B : Type*} [Fintype B] [DecidableEq B] {X : B → Type*}
    [∀ g, Fintype (X g)] [∀ g, Nonempty (X g)] {I : B → Type*} [∀ g, Fintype (I g)]
    (a : ∀ g, I g → ℝ) (t : ∀ g, I g → X g) (k : ∀ g, X g → ℝ) (F : (∀ g, X g) → ℝ)
    (h : ∀ (g : B) (x : ∀ g, X g), ∑ i : I g, a g i * F (Function.update x g (t g i)) =
      ∑ u : X g, k g u * F (Function.update x g u)) :
    ∑ i : ∀ g, I g, (∏ g, a g (i g)) * F (fun g => t g (i g)) =
      ∑ x : ∀ g, X g, (∏ g, k g (x g)) * F x := by
  -- the push-forward weights
  obtain ⟨μ, hμ⟩ : ∃ μ : ∀ g, X g → ℝ, ∀ g u, μ g u = ∑ i : I g, if t g i = u then a g i else 0 :=
    ⟨_, fun _ _ => rfl⟩
  have hpush : ∀ (g : B) (Φ : X g → ℝ), ∑ u : X g, μ g u * Φ u = ∑ i : I g, a g i * Φ (t g i) := by
    intro g Φ
    have e1 : ∀ u : X g, μ g u * Φ u = ∑ i : I g, if t g i = u then a g i * Φ u else 0 := by
      intro u
      rw [hμ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : t g i = u
      · rw [if_pos hi, if_pos hi]
      · rw [if_neg hi, if_neg hi, zero_mul]
    rw [Finset.sum_congr rfl fun u _ => e1 u, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e4 : (∑ u : X g, if t g i = u then a g i * Φ u else 0) =
        if t g i = t g i then a g i * Φ (t g i) else 0 :=
      Finset.sum_eq_single_of_mem (t g i) (Finset.mem_univ _) fun u _ hu =>
        if_neg (Ne.symm hu)
    exact e4.trans (if_pos rfl)
  -- the sum over the choices is the sum over the points with the push-forward weights
  have hsum : ∑ i : ∀ g, I g, (∏ g, a g (i g)) * F (fun g => t g (i g)) =
      ∑ x : ∀ g, X g, (∏ g, μ g (x g)) * F x := by
    have e2 : ∀ x : ∀ g, X g, (∏ g, μ g (x g)) * F x =
        ∑ i : ∀ g, I g, (∏ g, (if t g (i g) = x g then a g (i g) else 0)) * F x := by
      intro x
      have e3 : (∏ g, μ g (x g)) = ∏ g, ∑ i : I g, if t g i = x g then a g i else 0 :=
        Finset.prod_congr rfl fun g _ => hμ g (x g)
      rw [e3, Fintype.prod_sum, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun x _ => e2 x, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single_of_mem (fun g => t g (i g)) (Finset.mem_univ _)]
    · refine congrArg (fun s => s * F fun g => t g (i g)) ?_
      exact (Finset.prod_congr rfl fun g _ => (if_pos rfl).symm)
    · intro x _ hx
      have hne : ∃ g, t g (i g) ≠ x g := by
        by_contra hcon
        exact hx (funext fun g => (not_not.mp fun hg => hcon ⟨g, hg⟩).symm)
      obtain ⟨g, hg⟩ := hne
      have hz : (∏ g, (if t g (i g) = x g then a g (i g) else 0)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ g) (if_neg hg)
      show (∏ g, (if t g (i g) = x g then a g (i g) else 0)) * F x = 0
      rw [hz, zero_mul]
  rw [hsum]
  exact tensor_replace μ k F fun g x =>
    (hpush g fun u => F (Function.update x g u)).trans (h g x)

/-- **The product of the one-coordinate column inequalities**: if
`∑_u M_g(u) K_g(u, y) ≤ C_g M_g(y)` in every coordinate, then for nonnegative `Φ`
`∑_x ∏_g M_g(x_g) ∑_y ∏_g K_g(x_g, y_g) Φ(y) ≤ (∏_g C_g) ∑_y ∏_g M_g(y_g) Φ(y)`. -/
theorem tensor_col_le {B : Type*} [Fintype B] [DecidableEq B] {X : B → Type*}
    [∀ g, Fintype (X g)] (M : ∀ g, X g → ℝ) (K : ∀ g, X g → X g → ℝ) (C : B → ℝ)
    (Φ : (∀ g, X g) → ℝ) (hM : ∀ g u, 0 ≤ M g u) (hK : ∀ g u y, 0 ≤ K g u y)
    (hΦ : ∀ x, 0 ≤ Φ x) (h : ∀ (g : B) (y : X g), ∑ u : X g, M g u * K g u y ≤ C g * M g y) :
    ∑ x : ∀ g, X g, (∏ g, M g (x g)) * ∑ y : ∀ g, X g, (∏ g, K g (x g) (y g)) * Φ y ≤
      (∏ g, C g) * ∑ y : ∀ g, X g, (∏ g, M g (y g)) * Φ y := by
  have ha : ∑ x : ∀ g, X g, (∏ g, M g (x g)) * ∑ y : ∀ g, X g, (∏ g, K g (x g) (y g)) * Φ y =
      ∑ y : ∀ g, X g, (∑ x : ∀ g, X g, ∏ g, (M g (x g) * K g (x g) (y g))) * Φ y := by
    have h1 : ∀ x : ∀ g, X g,
        (∏ g, M g (x g)) * ∑ y : ∀ g, X g, (∏ g, K g (x g) (y g)) * Φ y =
          ∑ y : ∀ g, X g, (∏ g, (M g (x g) * K g (x g) (y g))) * Φ y := by
      intro x
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [Finset.prod_mul_distrib]
      ring
    rw [Finset.sum_congr rfl fun x _ => h1 x, Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.sum_mul]
  have hb : ∀ y : ∀ g, X g, (∑ x : ∀ g, X g, ∏ g, (M g (x g) * K g (x g) (y g))) =
      ∏ g, ∑ u : X g, M g u * K g u (y g) :=
    fun y => (Fintype.prod_sum fun g (u : X g) => M g u * K g u (y g)).symm
  have hc : ∀ y : ∀ g, X g, (∏ g, ∑ u : X g, M g u * K g u (y g)) ≤ ∏ g, C g * M g (y g) :=
    fun y => Finset.prod_le_prod
      (fun g _ => Finset.sum_nonneg fun u _ => mul_nonneg (hM g u) (hK g u (y g)))
      (fun g _ => h g (y g))
  calc ∑ x : ∀ g, X g, (∏ g, M g (x g)) * ∑ y : ∀ g, X g, (∏ g, K g (x g) (y g)) * Φ y
      = ∑ y : ∀ g, X g, (∑ x : ∀ g, X g, ∏ g, (M g (x g) * K g (x g) (y g))) * Φ y := ha
    _ ≤ ∑ y : ∀ g, X g, (∏ g, C g * M g (y g)) * Φ y :=
        Finset.sum_le_sum fun y _ => by
          rw [hb y]
          exact mul_le_mul_of_nonneg_right (hc y) (hΦ y)
    _ = (∏ g, C g) * ∑ y : ∀ g, X g, (∏ g, M g (y g)) * Φ y := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.prod_mul_distrib]
        ring

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
