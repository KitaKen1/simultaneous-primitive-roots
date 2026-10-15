module

public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring

/-!
# Factorial weights of indexed memory choices

The scalar accounting in [P, §4, `mem:ghost-factorial`, `mem:edge-factorial`]
and [S, §2, `eq:edge-factorial-reversal`]. Choices are choices of indices;
no distinctness assumption on the numerical values of the particles occurs.
These equalities are a prerequisite for the full measure-theoretic adjoint
identification, not a proof of that identification or of its norm bounds.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Graph

variable {K : Type*} [Field K] [CharZero K]

/-- An unordered deletion batch leaves exactly its birth factorial weight. -/
theorem ghost_deletion_factorial (k a : ℕ) :
    ((k + a).choose a : K) / ((k + a).factorial : K) =
      1 / ((k.factorial : K) * (a.factorial : K)) := by
  have ht : ((k + a).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hp : (k.factorial : K) * (a.factorial : K) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  apply (div_eq_div_iff ht hp).mpr
  rw [one_mul]
  have h : (k + a).choose a * a.factorial * k.factorial = (k + a).factorial := by
    simpa only [Nat.add_sub_cancel_right] using
      Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left a k)
  have h' : (k + a).choose a * (k.factorial * a.factorial) = (k + a).factorial := by
    rw [← h]
    ring
  exact_mod_cast h'

/-- Selecting old indices into prescribed ordered slots removes their factorial. -/
theorem ordered_retrieval_factorial {j a : ℕ} (ha : a ≤ j) :
    (j.descFactorial a : K) / (j.factorial : K) =
      1 / ((j - a).factorial : K) := by
  have hj : (j.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hr : ((j - a).factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  apply (div_eq_div_iff hj hr).mpr
  rw [one_mul]
  have h := Nat.factorial_mul_descFactorial ha
  have h' : j.descFactorial a * (j - a).factorial = j.factorial := by
    rw [Nat.mul_comm, h]
  exact_mod_cast h'

/-- The binomial-times-factorial version for a prescribed ordered active batch. -/
theorem ordered_binomial_retrieval (k a : ℕ) :
    (((k + a).choose a : K) * (a.factorial : K)) / ((k + a).factorial : K) =
      1 / (k.factorial : K) := by
  have h := ordered_retrieval_factorial (K := K) (Nat.le_add_left a k)
  simpa only [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul,
    Nat.add_sub_cancel_right, mul_comm] using h

/-- Forward promotions and reversed stores have the same surviving factorial. -/
theorem edge_factorial_reversal {j a : ℕ} (ha : a ≤ j) (b : ℕ) :
    (j.descFactorial a : K) / (j.factorial : K) =
      ((j - a + b).descFactorial b : K) / ((j - a + b).factorial : K) := by
  rw [ordered_retrieval_factorial ha,
    ordered_retrieval_factorial (Nat.le_add_left b (j - a)), Nat.add_sub_cancel_right]

end SimultaneousPrimitiveRoots.Unconditional.Graph
