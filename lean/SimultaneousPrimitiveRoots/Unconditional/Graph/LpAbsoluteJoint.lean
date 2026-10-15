module

public import SimultaneousPrimitiveRoots.Unconditional.Graph.LpMagnitude
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Absolute matrix-pair summability from a bounded positive majorant

A bounded operator whose matrix real parts dominate the coefficient norms
controls absolute rows on magnitude inputs. Cauchy-Schwarz then controls the
outer absolute row totals. Nonnegative Tonelli proves summability over pairs,
so the flattened kernel sum is legitimately the Hilbert inner product.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

open scoped BigOperators ComplexInnerProductSpace

variable {I : Type*}

theorem lp_operator_magnitude_real_row_summable
    (U : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2)
    (f : lp (fun _ : I => ℂ) 2) (x : I) :
    Summable (fun y => (U (lpCoordinateVector y) x).re * ‖f y‖) := by
  have h := Complex.reCLM.summable (lp_operator_row_summable U (lpCoordinateMagnitude f) x)
  simpa only [Complex.reCLM_apply, lp_coordinate_magnitude_apply, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using h

theorem lp_operator_magnitude_real_row
    (U : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2)
    (f : lp (fun _ : I => ℂ) 2) (x : I) :
    (U (lpCoordinateMagnitude f) x).re =
      ∑' y, (U (lpCoordinateVector y) x).re * ‖f y‖ := by
  rw [lp_operator_apply_eq_tsum]
  have h := Complex.reCLM.map_tsum (lp_operator_row_summable U (lpCoordinateMagnitude f) x)
  simpa only [Complex.reCLM_apply, lp_coordinate_magnitude_apply, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] using h

theorem lp_operator_absolute_row_le_majorant
    (T U : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2)
    (hTU : ∀ x y, ‖T (lpCoordinateVector y) x‖ ≤ (U (lpCoordinateVector y) x).re)
    (f : lp (fun _ : I => ℂ) 2) (x : I) :
    (∑' y, ‖T (lpCoordinateVector y) x * f y‖) ≤ (U (lpCoordinateMagnitude f) x).re := by
  rw [lp_operator_magnitude_real_row]
  exact (lp_operator_row_norm_summable T f x).tsum_le_tsum (fun y => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hTU x y) (norm_nonneg _))
    (lp_operator_magnitude_real_row_summable U f x)

theorem lp_operator_joint_row_norm_summable
    (T : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2)
    (f g : lp (fun _ : I => ℂ) 2) (x : I) :
    Summable (fun y => ‖star (g x) * T (lpCoordinateVector y) x * f y‖) := by
  have he (y : I) : ‖star (g x) * T (lpCoordinateVector y) x * f y‖ =
      ‖g x‖ * ‖T (lpCoordinateVector y) x * f y‖ := by
    rw [mul_assoc, norm_mul, norm_star]
  simpa only [he] using (lp_operator_row_norm_summable T f x).mul_left ‖g x‖

theorem lp_operator_joint_row_total_le
    (T U : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2)
    (hTU : ∀ x y, ‖T (lpCoordinateVector y) x‖ ≤ (U (lpCoordinateVector y) x).re)
    (f g : lp (fun _ : I => ℂ) 2) (x : I) :
    (∑' y, ‖star (g x) * T (lpCoordinateVector y) x * f y‖) ≤
      ‖g x‖ * ‖U (lpCoordinateMagnitude f) x‖ := by
  have he (y : I) : ‖star (g x) * T (lpCoordinateVector y) x * f y‖ =
      ‖g x‖ * ‖T (lpCoordinateVector y) x * f y‖ := by
    rw [mul_assoc, norm_mul, norm_star]
  simp_rw [he]
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left
    ((lp_operator_absolute_row_le_majorant T U hTU f x).trans (Complex.re_le_norm _))
    (norm_nonneg _)

theorem lp_operator_absolute_joint_outer_summable
    (T U : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2)
    (hTU : ∀ x y, ‖T (lpCoordinateVector y) x‖ ≤ (U (lpCoordinateVector y) x).re)
    (f g : lp (fun _ : I => ℂ) 2) :
    Summable (fun x => ∑' y, ‖star (g x) * T (lpCoordinateVector y) x * f y‖) :=
  Summable.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => norm_nonneg _))
    (lp_operator_joint_row_total_le T U hTU f g)
    (lp.summable_mul (by rw [Real.holderConjugate_iff]; norm_num) g
      (U (lpCoordinateMagnitude f)))

theorem lp_operator_absolute_joint_summable
    (T U : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2)
    (hTU : ∀ x y, ‖T (lpCoordinateVector y) x‖ ≤ (U (lpCoordinateVector y) x).re)
    (f g : lp (fun _ : I => ℂ) 2) :
    Summable (fun z : I × I => ‖star (g z.1) * T (lpCoordinateVector z.2) z.1 * f z.2‖) :=
  (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
    ⟨lp_operator_joint_row_norm_summable T f g,
      lp_operator_absolute_joint_outer_summable T U hTU f g⟩

theorem lp_operator_flat_joint_pairing
    (T U : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2)
    (hTU : ∀ x y, ‖T (lpCoordinateVector y) x‖ ≤ (U (lpCoordinateVector y) x).re)
    (f g : lp (fun _ : I => ℂ) 2) :
    (∑' z : I × I, star (g z.1) * T (lpCoordinateVector z.2) z.1 * f z.2) = inner ℂ g (T f) := by
  rw [(lp_operator_absolute_joint_summable T U hTU f g).of_norm.tsum_prod]
  rw [lp.inner_eq_tsum]
  apply tsum_congr
  intro x
  rw [lp_operator_apply_eq_tsum]
  simp only [RCLike.inner_apply', starRingEnd_apply, mul_assoc, tsum_mul_left]

theorem lp_operator_absolute_joint_norm_bound
    (T U : lp (fun _ : I => ℂ) 2 →L[ℂ] lp (fun _ : I => ℂ) 2)
    (hTU : ∀ x y, ‖T (lpCoordinateVector y) x‖ ≤ (U (lpCoordinateVector y) x).re)
    (f g : lp (fun _ : I => ℂ) 2) :
    (∑' z : I × I, ‖star (g z.1) * T (lpCoordinateVector z.2) z.1 * f z.2‖) ≤
      ‖g‖ * ‖U‖ * ‖f‖ := by
  rw [(lp_operator_absolute_joint_summable T U hTU f g).tsum_prod]
  calc
    _ ≤ ∑' x, ‖g x‖ * ‖U (lpCoordinateMagnitude f) x‖ :=
      (lp_operator_absolute_joint_outer_summable T U hTU f g).tsum_le_tsum
        (lp_operator_joint_row_total_le T U hTU f g)
        (lp.summable_mul (by rw [Real.holderConjugate_iff]; norm_num) g
          (U (lpCoordinateMagnitude f)))
    _ ≤ ‖g‖ * ‖U (lpCoordinateMagnitude f)‖ :=
      lp.tsum_mul_le_mul_norm' (by rw [Real.holderConjugate_iff]; norm_num) g
        (U (lpCoordinateMagnitude f))
    _ ≤ ‖g‖ * (‖U‖ * ‖lpCoordinateMagnitude f‖) :=
      mul_le_mul_of_nonneg_left (U.le_opNorm _) (norm_nonneg _)
    _ = _ := by rw [lp_coordinate_magnitude_norm]; ring

end SimultaneousPrimitiveRoots.Unconditional.Graph
