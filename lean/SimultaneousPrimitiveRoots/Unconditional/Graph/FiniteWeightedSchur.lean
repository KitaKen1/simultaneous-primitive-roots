module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Data.Real.Basic
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Weighted Schur inequality on finite measured sets

Row and column conditions are stated with their actual endpoint masses and
strictly positive auxiliary weights. The conclusion is the squared weighted
L2 bound R*C. Establishing these conditions for the memory kernels, and the
extension to unbounded memory, are separate analytic obligations.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators

variable {I J : Type*}

/-- Weighted row Cauchy-Schwarz, allowing zero kernel entries. -/
theorem weighted_kernel_row_sq [Fintype J] (κ v f : J → ℝ)
    (hκ : ∀ j, 0 ≤ κ j) (hv : ∀ j, 0 < v j) :
    (∑ j, κ j * f j) ^ 2 ≤
      (∑ j, κ j * v j) * ∑ j, κ j * f j ^ 2 / v j := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (fun j _ => mul_nonneg (hκ j) (hv j).le)
    (fun j _ => div_nonneg (mul_nonneg (hκ j) (sq_nonneg _)) (hv j).le)
  intro j _
  apply le_of_eq
  field_simp [(hv j).ne']

/-- Finite weighted Schur: the row and transposed-column bounds give an L2 bound.
Endpoint counting/prime masses need only be nonnegative; auxiliary weights are positive. -/
theorem finite_weighted_schur [Fintype I] [Fintype J]
    (κ : I → J → ℝ) (μ : I → ℝ) (ν : J → ℝ) (u : I → ℝ) (v : J → ℝ)
    (R C : ℝ) (hκ : ∀ i j, 0 ≤ κ i j) (hμ : ∀ i, 0 ≤ μ i)
    (hν : ∀ j, 0 ≤ ν j) (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j)
    (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : ∀ i, ∑ j, κ i j * ν j * v j ≤ R * u i)
    (hcol : ∀ j, ∑ i, κ i j * μ i * u i ≤ C * v j) (f : J → ℝ) :
    (∑ i, μ i * (∑ j, κ i j * ν j * f j) ^ 2) ≤
      R * C * ∑ j, ν j * f j ^ 2 := by
  classical
  have hg (i : I) : 0 ≤ ∑ j, κ i j * ν j * f j ^ 2 / v j := by
    apply Finset.sum_nonneg
    intro j _
    exact div_nonneg (mul_nonneg (mul_nonneg (hκ i j) (hν j)) (sq_nonneg _)) (hv j).le
  have hr (i : I) : (∑ j, κ i j * ν j * f j) ^ 2 ≤
      (R * u i) * ∑ j, κ i j * ν j * f j ^ 2 / v j :=
    (weighted_kernel_row_sq (fun j => κ i j * ν j) v f
      (fun j => mul_nonneg (hκ i j) (hν j)) hv).trans
        (mul_le_mul (hrow i) (le_refl _) (hg i) (mul_nonneg hR (hu i).le))
  calc
    _ ≤ ∑ i, μ i * ((R * u i) * ∑ j, κ i j * ν j * f j ^ 2 / v j) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hr i) (hμ i)
    _ = R * ∑ j, (ν j * f j ^ 2 / v j) * ∑ i, κ i j * μ i * u i := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ R * ∑ j, (ν j * f j ^ 2 / v j) * (C * v j) := by
      apply mul_le_mul_of_nonneg_left _ hR
      apply Finset.sum_le_sum
      intro j _
      have hh := mul_le_mul (hcol j) (le_refl (ν j * f j ^ 2 / v j))
        (div_nonneg (mul_nonneg (hν j) (sq_nonneg _)) (hv j).le)
        (mul_nonneg hC (hv j).le)
      simpa only [mul_comm] using hh
    _ = R * C * ∑ j, ν j * f j ^ 2 := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      field_simp [(hv j).ne']

/-- Absolute positive row kernels dominate complex phases and signed coefficients. -/
theorem complex_kernel_row_domination [Fintype J]
    (B f : J → ℂ) (κ ν : J → ℝ) (hB : ∀ j, ‖B j‖ ≤ κ j)
    (hν : ∀ j, 0 ≤ ν j) :
    ‖∑ j, B j * (ν j : ℂ) * f j‖ ≤ ∑ j, κ j * ν j * ‖f j‖ := by
  classical
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hν j)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hB j) (hν j)) (norm_nonneg _)

/-- Schur's squared L2 bound also holds for a complex kernel dominated by κ. -/
theorem finite_complex_weighted_schur [Fintype I] [Fintype J]
    (B : I → J → ℂ) (κ : I → J → ℝ) (μ : I → ℝ) (ν : J → ℝ)
    (u : I → ℝ) (v : J → ℝ) (R C : ℝ)
    (hB : ∀ i j, ‖B i j‖ ≤ κ i j) (hκ : ∀ i j, 0 ≤ κ i j)
    (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ j, 0 ≤ ν j)
    (hu : ∀ i, 0 < u i) (hv : ∀ j, 0 < v j) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : ∀ i, ∑ j, κ i j * ν j * v j ≤ R * u i)
    (hcol : ∀ j, ∑ i, κ i j * μ i * u i ≤ C * v j) (f : J → ℂ) :
    (∑ i, μ i * ‖∑ j, B i j * (ν j : ℂ) * f j‖ ^ 2) ≤
      R * C * ∑ j, ν j * ‖f j‖ ^ 2 := by
  classical
  calc
    _ ≤ ∑ i, μ i * (∑ j, κ i j * ν j * ‖f j‖) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hμ i)
      exact pow_le_pow_left₀ (norm_nonneg _)
        (complex_kernel_row_domination (B i) f (κ i) ν (hB i) hν) 2
    _ ≤ _ := finite_weighted_schur κ μ ν u v R C hκ hμ hν hu hv hR hC hrow hcol
      (fun j => ‖f j‖)

end SimultaneousPrimitiveRoots.Unconditional.Graph
