module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.MajorArcTools
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.PhaseBilinear
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Denominators at most `Q`: the pointwise defect on retained cells

Source: `verification/stage7-sources/S-03.tex`, lines 372–412 (`[S-03:0372–0412]`).

* `Major.dilPhase_eq_slow` — `n^{iζ} e(αn) = M(log n) e(un/r)` for `α = u/r + β`.
* `Major.abstract_gap` — the algebra of [S-03:0379–0410]: if the multiplier `M` varies by at most
  `δ` on the support of the two kernels, the kernels have `L¹` cost at most `N`
  (eq:ideal-cell-costs), the rational phase is `∑_ψ c_ψ ψ ⊗ ψ` (eq:ideal-rational-expansion) and
  the kernels reproduce every `ψ` up to `ε_r ≤ 1` (eq:ideal-character-reproduction), then the
  pointwise defect is at most `δ N² + 3 ε_r ∑|c_ψ|`: (eq:ideal-log-error) and
  (eq:ideal-major-character-error).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

namespace Major

theorem expUnit_add (s t : ℝ) : expUnit (s + t) = expUnit s * expUnit t := by
  unfold expUnit
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `n^{iζ} e(αn) = M(log n) e(un/r)` for `α = u/r + β`. -/
theorem dilPhase_eq_slow {α β : ℝ} {u : ℤ} {r : ℕ} (hα : α = (u : ℝ) / (r : ℝ) + β) (ζ : ℝ)
    (n : ℕ) :
    dilPhase ζ α n = slowPhase ζ β n * expUnit ((u : ℝ) * (n : ℝ) / (r : ℝ)) := by
  have h1 : α * (n : ℝ) = β * (n : ℝ) + (u : ℝ) * (n : ℝ) / (r : ℝ) := by
    rw [hα]
    ring
  unfold dilPhase slowPhase
  rw [h1, expUnit_add, mul_assoc]

theorem norm_slowPhase_le (ζ β : ℝ) (n : ℕ) : ‖slowPhase ζ β n‖ ≤ 1 := by
  unfold slowPhase
  rw [norm_mul, norm_expUnit, mul_one]
  exact Phase.norm_natCast_cpow_le_one n ζ

/-- **The pointwise defect on a retained pair**, in abstract form. -/
theorem abstract_gap {X Y : Type} [Fintype X] [Fintype Y] {ι : Type} [Fintype ι] (wA : X → ℝ)
    (wB : Y → ℝ) (hwA : ∀ x, 0 ≤ wA x) (hwB : ∀ y, 0 ≤ wB y) (KA : X → ℂ) (KB : Y → ℂ)
    (m : X → Y → ℂ) (m₀ : ℂ) (e : X → Y → ℂ) (e₀ : ℂ) (c : ι → ℂ) (ψA : ι → X → ℂ)
    (ψB : ι → Y → ℂ) (ψA₀ ψB₀ : ι → ℂ) {C₁ N δ εr : ℝ}
    (he : ∀ x y, e x y = ∑ i, c i * (ψA i x * ψB i y))
    (he₀ : e₀ = ∑ i, c i * (ψA₀ i * ψB₀ i)) (hen : ∀ x y, ‖e x y‖ ≤ 1) (hm₀ : ‖m₀‖ ≤ 1)
    (hc : ∑ i, ‖c i‖ ≤ C₁) (hψA₀ : ∀ i, ‖ψA₀ i‖ ≤ 1) (hψB₀ : ∀ i, ‖ψB₀ i‖ ≤ 1)
    (hεr0 : 0 ≤ εr) (hεr1 : εr ≤ 1) (hδ : 0 ≤ δ) (hN : 0 ≤ N)
    (hcostA : ∑ x, wA x * ‖KA x‖ ≤ N) (hcostB : ∑ y, wB y * ‖KB y‖ ≤ N)
    (hM : ∀ x y, KA x ≠ 0 → KB y ≠ 0 → ‖m x y - m₀‖ ≤ δ)
    (hrepA : ∀ i, ‖(∑ x, (wA x : ℂ) * (KA x * ψA i x)) - ψA₀ i‖ ≤ εr)
    (hrepB : ∀ i, ‖(∑ y, (wB y : ℂ) * (KB y * ψB i y)) - ψB₀ i‖ ≤ εr) :
    ‖m₀ * e₀ - ∑ x, ∑ y, ((wA x * wB y : ℝ) : ℂ) * (KA x * KB y * (m x y * e x y))‖ ≤
      δ * (N * N) + C₁ * (3 * εr) := by
  -- the rational part: `T₂ = ∑_i c_i R_A(i) R_B(i)`
  have h1 : ∀ i, c i * ((∑ x, (wA x : ℂ) * (KA x * ψA i x)) *
        (∑ y, (wB y : ℂ) * (KB y * ψB i y))) =
      ∑ x, ∑ y, ((wA x * wB y : ℝ) : ℂ) * (KA x * KB y * (c i * (ψA i x * ψB i y))) := by
    intro i
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    push_cast
    ring
  have hT2 : ∑ x, ∑ y, ((wA x * wB y : ℝ) : ℂ) * (KA x * KB y * e x y) =
      ∑ i, c i * ((∑ x, (wA x : ℂ) * (KA x * ψA i x)) *
        (∑ y, (wB y : ℂ) * (KB y * ψB i y))) := by
    calc ∑ x, ∑ y, ((wA x * wB y : ℝ) : ℂ) * (KA x * KB y * e x y)
        = ∑ x, ∑ y, ∑ i, ((wA x * wB y : ℝ) : ℂ) *
            (KA x * KB y * (c i * (ψA i x * ψB i y))) := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
          rw [he x y, Finset.mul_sum, Finset.mul_sum]
      _ = ∑ x, ∑ i, ∑ y, ((wA x * wB y : ℝ) : ℂ) *
            (KA x * KB y * (c i * (ψA i x * ψB i y))) :=
          Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = ∑ i, ∑ x, ∑ y, ((wA x * wB y : ℝ) : ℂ) *
            (KA x * KB y * (c i * (ψA i x * ψB i y))) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun i _ => (h1 i).symm
  -- the decomposition of the comparison term
  have hsplit : ∑ x, ∑ y, ((wA x * wB y : ℝ) : ℂ) * (KA x * KB y * (m x y * e x y)) =
      (∑ x, ∑ y, ((wA x * wB y : ℝ) : ℂ) * (KA x * KB y * ((m x y - m₀) * e x y))) +
        m₀ * ∑ x, ∑ y, ((wA x * wB y : ℝ) : ℂ) * (KA x * KB y * e x y) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  have hmain : m₀ * e₀ - ∑ x, ∑ y, ((wA x * wB y : ℝ) : ℂ) *
        (KA x * KB y * (m x y * e x y)) =
      m₀ * (∑ i, c i * (ψA₀ i * ψB₀ i -
        (∑ x, (wA x : ℂ) * (KA x * ψA i x)) * (∑ y, (wB y : ℂ) * (KB y * ψB i y)))) -
      ∑ x, ∑ y, ((wA x * wB y : ℝ) : ℂ) * (KA x * KB y * ((m x y - m₀) * e x y)) := by
    have h2 : ∑ i, c i * (ψA₀ i * ψB₀ i -
        (∑ x, (wA x : ℂ) * (KA x * ψA i x)) * (∑ y, (wB y : ℂ) * (KB y * ψB i y))) =
        e₀ - ∑ x, ∑ y, ((wA x * wB y : ℝ) : ℂ) * (KA x * KB y * e x y) := by
      rw [hT2, he₀, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit, h2]
    ring
  -- the two errors
  have hrat : ‖∑ i, c i * (ψA₀ i * ψB₀ i -
      (∑ x, (wA x : ℂ) * (KA x * ψA i x)) * (∑ y, (wB y : ℂ) * (KB y * ψB i y)))‖ ≤
      C₁ * (3 * εr) := by
    have h3 : ∀ i, ‖ψA₀ i * ψB₀ i -
        (∑ x, (wA x : ℂ) * (KA x * ψA i x)) * (∑ y, (wB y : ℂ) * (KB y * ψB i y))‖ ≤
        3 * εr := by
      intro i
      have h4 : ψA₀ i * ψB₀ i -
          (∑ x, (wA x : ℂ) * (KA x * ψA i x)) * (∑ y, (wB y : ℂ) * (KB y * ψB i y)) =
          -(((∑ x, (wA x : ℂ) * (KA x * ψA i x)) - ψA₀ i) *
              (∑ y, (wB y : ℂ) * (KB y * ψB i y))) -
            ψA₀ i * ((∑ y, (wB y : ℂ) * (KB y * ψB i y)) - ψB₀ i) := by ring
      have h5 : ‖∑ y, (wB y : ℂ) * (KB y * ψB i y)‖ ≤ 2 := by
        have h6 : (∑ y, (wB y : ℂ) * (KB y * ψB i y)) =
            ((∑ y, (wB y : ℂ) * (KB y * ψB i y)) - ψB₀ i) + ψB₀ i := by ring
        rw [h6]
        exact (norm_add_le _ _).trans (by linarith [hrepB i, hψB₀ i])
      rw [h4]
      refine (norm_sub_le _ _).trans ?_
      rw [norm_neg, norm_mul, norm_mul]
      have h7 : ‖(∑ x, (wA x : ℂ) * (KA x * ψA i x)) - ψA₀ i‖ *
          ‖∑ y, (wB y : ℂ) * (KB y * ψB i y)‖ ≤ εr * 2 :=
        mul_le_mul (hrepA i) h5 (norm_nonneg _) hεr0
      have h8 : ‖ψA₀ i‖ * ‖(∑ y, (wB y : ℂ) * (KB y * ψB i y)) - ψB₀ i‖ ≤ 1 * εr :=
        mul_le_mul (hψA₀ i) (hrepB i) (norm_nonneg _) zero_le_one
      linarith
    refine (norm_sum_le _ _).trans ?_
    have h9 : ∀ i ∈ (Finset.univ : Finset ι), ‖c i * (ψA₀ i * ψB₀ i -
        (∑ x, (wA x : ℂ) * (KA x * ψA i x)) * (∑ y, (wB y : ℂ) * (KB y * ψB i y)))‖ ≤
        ‖c i‖ * (3 * εr) := fun i _ => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (h3 i) (norm_nonneg _)
    refine (Finset.sum_le_sum h9).trans ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hc (by linarith)
  have hlog : ‖∑ x, ∑ y, ((wA x * wB y : ℝ) : ℂ) *
      (KA x * KB y * ((m x y - m₀) * e x y))‖ ≤ δ * (N * N) := by
    have h3 : ∀ x y, ‖((wA x * wB y : ℝ) : ℂ) * (KA x * KB y * ((m x y - m₀) * e x y))‖ ≤
        wA x * ‖KA x‖ * (wB y * ‖KB y‖) * δ := by
      intro x y
      have hw0 : 0 ≤ wA x * ‖KA x‖ * (wB y * ‖KB y‖) :=
        mul_nonneg (mul_nonneg (hwA x) (norm_nonneg _)) (mul_nonneg (hwB y) (norm_nonneg _))
      by_cases hx : KA x = 0
      · have hz : ((wA x * wB y : ℝ) : ℂ) * (KA x * KB y * ((m x y - m₀) * e x y)) = 0 := by
          rw [hx]
          ring
        rw [hz, norm_zero]
        exact mul_nonneg hw0 hδ
      by_cases hy : KB y = 0
      · have hz : ((wA x * wB y : ℝ) : ℂ) * (KA x * KB y * ((m x y - m₀) * e x y)) = 0 := by
          rw [hy]
          ring
        rw [hz, norm_zero]
        exact mul_nonneg hw0 hδ
      rw [norm_mul, norm_mul, norm_mul, norm_mul,
        Complex.norm_of_nonneg (mul_nonneg (hwA x) (hwB y))]
      have h4 : ‖m x y - m₀‖ * ‖e x y‖ ≤ δ * 1 :=
        mul_le_mul (hM x y hx hy) (hen x y) (norm_nonneg _) hδ
      have h5 : wA x * wB y * (‖KA x‖ * ‖KB y‖ * (‖m x y - m₀‖ * ‖e x y‖)) ≤
          wA x * wB y * (‖KA x‖ * ‖KB y‖ * (δ * 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (mul_nonneg (hwA x) (hwB y))
      have h6 : wA x * wB y * (‖KA x‖ * ‖KB y‖ * (δ * 1)) =
          wA x * ‖KA x‖ * (wB y * ‖KB y‖) * δ := by ring
      linarith
    have h7 : ∑ x, ∑ y, wA x * ‖KA x‖ * (wB y * ‖KB y‖) * δ =
        (∑ x, wA x * ‖KA x‖) * (∑ y, wB y * ‖KB y‖) * δ := by
      rw [Finset.sum_mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun x _ => (Finset.sum_mul _ _ _).symm
    have h0A : 0 ≤ ∑ x, wA x * ‖KA x‖ :=
      Finset.sum_nonneg fun x _ => mul_nonneg (hwA x) (norm_nonneg _)
    have h0B : 0 ≤ ∑ y, wB y * ‖KB y‖ :=
      Finset.sum_nonneg fun y _ => mul_nonneg (hwB y) (norm_nonneg _)
    have h8 : (∑ x, wA x * ‖KA x‖) * (∑ y, wB y * ‖KB y‖) ≤ N * N :=
      mul_le_mul hcostA hcostB h0B hN
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun x _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun y _ => h3 x y)).trans ?_
    rw [h7, mul_comm]
    exact mul_le_mul_of_nonneg_left h8 hδ
  rw [hmain]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul]
  have h10 : ‖m₀‖ * ‖∑ i, c i * (ψA₀ i * ψB₀ i -
      (∑ x, (wA x : ℂ) * (KA x * ψA i x)) * (∑ y, (wB y : ℂ) * (KB y * ψB i y)))‖ ≤
      1 * (C₁ * (3 * εr)) :=
    mul_le_mul hm₀ hrat (norm_nonneg _) zero_le_one
  linarith

end Major

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
