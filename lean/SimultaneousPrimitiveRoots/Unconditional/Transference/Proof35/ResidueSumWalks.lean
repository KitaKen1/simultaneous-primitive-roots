module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.RowOps
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The summation over paths, part 1: generic facts about walks

Source: `verification/stage7-sources/S-02.tex`, lines 212–234 and 293–307
(`[S-02:0212–0234, 0293–0307]`).

Generic lemmas about `walkCoef`, `walkEnd` (`RowOps.lean`); no prime groups occur.

* `flatWord`, `altTgt`, `altCoef`, `walkCoef_round_eq`, `walkEnd_round_eq` — a walk of rounds
  (a forward edge followed by a backward edge) is a walk of edges with a direction flag: "paths
  with `N` alternating forward and backward edges" [S-02:0212–0213].
* `walkEnd_map`, `walkCoef_map` — walks are transported by maps which commute with the
  transitions.
* `walkCoef_eq_weights` — if every coefficient is `W(s) · W(target) · κ`, the coefficient of a walk
  is the product of the `κ` times `∏_e W(s_e) W(s_{e+1})` over its edges.
* `prod_adjacent` — `∏_{e ≤ m} a_e a_{e+1} = a_0 · (∏_{0 < i ≤ m} a_i²) · a_{m+1}`: the end visits
  occur once and the interior visits twice ("`q_0 = q_N = √q` and `q_i = q` for `0 < i < N`",
  [S-02:0223–0224]).
* `sum_norm_walkCoef_le` — the absolute mass of all walks of `n` steps is at most `ρ^n` when
  every row sum is at most `ρ` [S-02:0303–0304].
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResSum

open scoped BigOperators

noncomputable section

variable {X Y Ξ : Type*}

/-! ### Rounds and edges -/

/-- A word of rounds as a word of edges. -/
def flatWord : List (Ξ × Ξ) → List Ξ
  | [] => []
  | ξ :: w => ξ.1 :: ξ.2 :: flatWord w

theorem length_flatWord (w : List (Ξ × Ξ)) : (flatWord w).length = 2 * w.length := by
  induction w with
  | nil => rfl
  | cons ξ w ih =>
    show (flatWord w).length + 1 + 1 = 2 * (w.length + 1)
    rw [ih]
    ring

/-- The target of an edge for states with a direction flag: `false` — the next edge is a forward
edge, `true` — a backward edge. -/
def altTgt (tF tB : X → Ξ → X) (s : Bool × X) (ξ : Ξ) : Bool × X :=
  (!s.1, if s.1 then tB s.2 ξ else tF s.2 ξ)

/-- The coefficient of an edge for states with a direction flag. -/
def altCoef (cF cB : X → Ξ → ℂ) (s : Bool × X) (ξ : Ξ) : ℂ :=
  if s.1 then cB s.2 ξ else cF s.2 ξ

/-- The coefficient of a walk of rounds is the coefficient of the walk of its edges. -/
theorem walkCoef_round_eq (cF cB : X → Ξ → ℂ) (tF tB : X → Ξ → X) (s : X)
    (w : List (Ξ × Ξ)) :
    walkCoef (fun s ξ => cF s ξ.1 * cB (tF s ξ.1) ξ.2) (fun s ξ => tB (tF s ξ.1) ξ.2) s w =
      walkCoef (altCoef cF cB) (altTgt tF tB) (false, s) (flatWord w) := by
  induction w generalizing s with
  | nil => rfl
  | cons ξ w ih =>
    show cF s ξ.1 * cB (tF s ξ.1) ξ.2 *
        walkCoef (fun s ξ => cF s ξ.1 * cB (tF s ξ.1) ξ.2) (fun s ξ => tB (tF s ξ.1) ξ.2)
          (tB (tF s ξ.1) ξ.2) w =
      cF s ξ.1 * (cB (tF s ξ.1) ξ.2 *
        walkCoef (altCoef cF cB) (altTgt tF tB) (false, tB (tF s ξ.1) ξ.2) (flatWord w))
    rw [ih, mul_assoc]

/-- The end of a walk of rounds is the end of the walk of its edges. -/
theorem walkEnd_round_eq (tF tB : X → Ξ → X) (s : X) (w : List (Ξ × Ξ)) :
    walkEnd (altTgt tF tB) (false, s) (flatWord w) =
      (false, walkEnd (fun s ξ => tB (tF s ξ.1) ξ.2) s w) := by
  induction w generalizing s with
  | nil => rfl
  | cons ξ w ih => exact ih (tB (tF s ξ.1) ξ.2)

/-! ### Transport of walks -/

theorem walkEnd_map (φ : X → Y) (tgt : X → Ξ → X) (tgt' : Y → Ξ → Y)
    (h : ∀ s ξ, tgt' (φ s) ξ = φ (tgt s ξ)) (s : X) (w : List Ξ) :
    walkEnd tgt' (φ s) w = φ (walkEnd tgt s w) := by
  induction w generalizing s with
  | nil => rfl
  | cons ξ w ih =>
    show walkEnd tgt' (tgt' (φ s) ξ) w = φ (walkEnd tgt (tgt s ξ) w)
    rw [h, ih]

theorem walkCoef_map (φ : X → Y) (tgt : X → Ξ → X) (tgt' : Y → Ξ → Y) (c : X → Ξ → ℂ)
    (c' : Y → Ξ → ℂ) (h : ∀ s ξ, tgt' (φ s) ξ = φ (tgt s ξ)) (hc : ∀ s ξ, c' (φ s) ξ = c s ξ)
    (s : X) (w : List Ξ) : walkCoef c' tgt' (φ s) w = walkCoef c tgt s w := by
  induction w generalizing s with
  | nil => rfl
  | cons ξ w ih =>
    show c' (φ s) ξ * walkCoef c' tgt' (tgt' (φ s) ξ) w = c s ξ * walkCoef c tgt (tgt s ξ) w
    rw [hc, h, ih]

/-! ### Coefficients with weights at both ends -/

/-- If every coefficient is `W(s) · W(target) · κ`, then the coefficient of a walk is the product
of the `κ` along the walk times the product over its edges of the weights of the two ends. -/
theorem walkCoef_eq_weights (coef : X → Ξ → ℂ) (tgt : X → Ξ → X) (W : X → ℝ) (κ : X → Ξ → ℂ)
    (h : ∀ s ξ, coef s ξ = (W s : ℂ) * (W (tgt s ξ) : ℂ) * κ s ξ) (s : X) (w : List Ξ) :
    walkCoef coef tgt s w =
      walkCoef κ tgt s w *
        ((∏ e ∈ Finset.range w.length,
          W (walkEnd tgt s (w.take e)) * W (walkEnd tgt s (w.take (e + 1))) : ℝ) : ℂ) := by
  induction w generalizing s with
  | nil => simp [walkCoef]
  | cons ξ w ih =>
    have hprod : ∏ e ∈ Finset.range (ξ :: w).length,
        W (walkEnd tgt s ((ξ :: w).take e)) * W (walkEnd tgt s ((ξ :: w).take (e + 1))) =
        (∏ e ∈ Finset.range w.length,
          W (walkEnd tgt (tgt s ξ) (w.take e)) * W (walkEnd tgt (tgt s ξ) (w.take (e + 1)))) *
          (W s * W (tgt s ξ)) := by
      rw [List.length_cons, Finset.prod_range_succ']
      rfl
    rw [hprod]
    show coef s ξ * walkCoef coef tgt (tgt s ξ) w =
      κ s ξ * walkCoef κ tgt (tgt s ξ) w * _
    rw [h, ih]
    push_cast
    ring

/-- The end visits of a walk occur in one edge and the interior visits in two. -/
theorem prod_adjacent (a : ℕ → ℝ) (m : ℕ) :
    ∏ e ∈ Finset.range (m + 1), a e * a (e + 1) =
      ∏ i ∈ Finset.range (m + 1 + 1), (if i = 0 ∨ i = m + 1 then a i else a i ^ 2) := by
  have hL : ∏ e ∈ Finset.range (m + 1), a e * a (e + 1) =
      a 0 * (∏ e ∈ Finset.range m, a (e + 1)) ^ 2 * a (m + 1) := by
    rw [Finset.prod_mul_distrib, Finset.prod_range_succ', Finset.prod_range_succ]
    ring
  have hR : ∏ i ∈ Finset.range (m + 1 + 1), (if i = 0 ∨ i = m + 1 then a i else a i ^ 2) =
      a 0 * (∏ e ∈ Finset.range m, a (e + 1)) ^ 2 * a (m + 1) := by
    rw [Finset.prod_range_succ', Finset.prod_range_succ]
    have h1 : ∀ i ∈ Finset.range m,
        (if i + 1 = 0 ∨ i + 1 = m + 1 then a (i + 1) else a (i + 1) ^ 2) = a (i + 1) ^ 2 := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have h2 : ¬(i + 1 = 0 ∨ i + 1 = m + 1) := by omega
      rw [if_neg h2]
    have h3 : (if m + 1 = 0 ∨ m + 1 = m + 1 then a (m + 1) else a (m + 1) ^ 2) = a (m + 1) :=
      if_pos (Or.inr rfl)
    have h4 : (if (0 : ℕ) = 0 ∨ 0 = m + 1 then a 0 else a 0 ^ 2) = a 0 :=
      if_pos (Or.inl rfl)
    rw [Finset.prod_congr rfl h1, Finset.prod_pow, h3, h4]
    ring
  rw [hL, hR]

/-! ### The absolute mass of all walks -/

/-- If every row sum of the moduli of the coefficients is at most `ρ`, the moduli of the
coefficients of all walks of `n` steps from a state sum to at most `ρ^n`. -/
theorem sum_norm_walkCoef_le [Fintype Ξ] (coef : X → Ξ → ℂ) (tgt : X → Ξ → X) {ρ : ℝ}
    (hρ : ∀ s, ∑ ξ, ‖coef s ξ‖ ≤ ρ) (n : ℕ) (s : X) :
    ∑ w : Fin n → Ξ, ‖walkCoef coef tgt s (List.ofFn w)‖ ≤ ρ ^ n := by
  have hρ0 : 0 ≤ ρ := (Finset.sum_nonneg fun ξ _ => norm_nonneg _).trans (hρ s)
  induction n generalizing s with
  | zero =>
    rw [Fintype.sum_unique, pow_zero]
    simp [walkCoef]
  | succ n ih =>
    rw [← (wordConsEquiv n Ξ).sum_comp, Fintype.sum_prod_type]
    have hstep : ∀ (ξ : Ξ) (w : Fin n → Ξ),
        ‖walkCoef coef tgt s (List.ofFn (wordConsEquiv n Ξ (ξ, w)))‖ =
          ‖coef s ξ‖ * ‖walkCoef coef tgt (tgt s ξ) (List.ofFn w)‖ := by
      intro ξ w
      have h0 : wordConsEquiv n Ξ (ξ, w) 0 = ξ := by simp [wordConsEquiv]
      have hs : (fun i : Fin n => wordConsEquiv n Ξ (ξ, w) i.succ) = w := by
        funext i
        simp [wordConsEquiv]
      have hl : List.ofFn (wordConsEquiv n Ξ (ξ, w)) = ξ :: List.ofFn w := by
        rw [List.ofFn_succ, h0, hs]
      rw [hl]
      show ‖coef s ξ * walkCoef coef tgt (tgt s ξ) (List.ofFn w)‖ = _
      rw [norm_mul]
    calc ∑ ξ, ∑ w : Fin n → Ξ, ‖walkCoef coef tgt s (List.ofFn (wordConsEquiv n Ξ (ξ, w)))‖
        = ∑ ξ, ‖coef s ξ‖ * ∑ w : Fin n → Ξ, ‖walkCoef coef tgt (tgt s ξ) (List.ofFn w)‖ := by
          refine Finset.sum_congr rfl fun ξ _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun w _ => hstep ξ w
      _ ≤ ∑ ξ, ‖coef s ξ‖ * ρ ^ n :=
          Finset.sum_le_sum fun ξ _ => mul_le_mul_of_nonneg_left (ih (tgt s ξ)) (norm_nonneg _)
      _ = (∑ ξ, ‖coef s ξ‖) * ρ ^ n := by rw [Finset.sum_mul]
      _ ≤ ρ * ρ ^ n := mul_le_mul_of_nonneg_right (hρ s) (pow_nonneg hρ0 n)
      _ = ρ ^ (n + 1) := by rw [pow_succ']

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResSum
