module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Absolutely convergent rows of bounded operators on counting ell-two

The adjoint applied to a coordinate vector represents a row. Cauchy-Schwarz
gives absolute convergence, and the Hilbert inner-product identity identifies
the operator coordinate with the actual matrix series, without a double-sum
interchange.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators ComplexInnerProductSpace Classical

variable {I : Type*}

noncomputable def lpCoordinateVector (x : I) : lp (fun _ : I => ℂ) 2 :=
  lp.single 2 x 1

theorem lp_operator_adjoint_single_coordinates
    (T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2) (x y : I) :
    T.adjoint (lpCoordinateVector x) y = star (T (lpCoordinateVector y) x) := by
  have h := T.adjoint_inner_right (lpCoordinateVector y) (lpCoordinateVector x)
  simpa only [lpCoordinateVector, lp.inner_single_left, lp.inner_single_right, RCLike.inner_apply',
    starRingEnd_apply, star_one, one_mul, mul_one] using h

theorem lp_operator_row_norm_summable
    (T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2)
    (f : lp (fun _ : I => ℂ) 2) (x : I) :
    Summable (fun y => ‖T (lpCoordinateVector y) x * f y‖) := by
  have h := lp.summable_mul (by rw [Real.holderConjugate_iff]; norm_num)
    (T.adjoint (lpCoordinateVector x)) f
  simpa only [lp_operator_adjoint_single_coordinates, norm_star, norm_mul] using h

theorem lp_operator_row_summable
    (T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2)
    (f : lp (fun _ : I => ℂ) 2) (x : I) :
    Summable (fun y => T (lpCoordinateVector y) x * f y) :=
  (lp_operator_row_norm_summable T f x).of_norm

theorem lp_operator_apply_eq_tsum
    (T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2)
    (f : lp (fun _ : I => ℂ) 2) (x : I) :
    T f x = ∑' y, T (lpCoordinateVector y) x * f y := by
  have h := T.adjoint_inner_left f (lpCoordinateVector x)
  have hr : inner ℂ (lpCoordinateVector x) (T f) = T f x := by
    simp only [lpCoordinateVector, lp.inner_single_left, RCLike.inner_apply',
      starRingEnd_apply, star_one, one_mul]
  rw [hr] at h
  simpa only [lp.inner_eq_tsum, lp_operator_adjoint_single_coordinates,
    RCLike.inner_apply', starRingEnd_apply, star_star, star_one, one_mul] using h.symm

theorem lp_operator_eq_of_matrix
    (T U : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2)
    (h : ∀ x y, T (lpCoordinateVector y) x = U (lpCoordinateVector y) x) : T = U := by
  apply ContinuousLinearMap.ext
  intro f
  apply lp.ext
  funext x
  rw [lp_operator_apply_eq_tsum, lp_operator_apply_eq_tsum]
  exact tsum_congr (fun y => congrArg (fun a : ℂ => a * f y) (h x y))

end SimultaneousPrimitiveRoots.Unconditional.Graph
