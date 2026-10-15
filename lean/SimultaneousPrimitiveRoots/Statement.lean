module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

/-! The target statement, with no analytic hypotheses built into its definitions. -/

noncomputable section

namespace SimultaneousPrimitiveRoots

def SquareCondition (A : Finset ℕ) : Prop :=
  ∀ B : Finset ℕ, B ⊆ A → Odd B.card → ¬ IsSquare (∏ a ∈ B, a)

def Admissible (A : Finset ℕ) : Prop :=
  A.Nonempty ∧ (∀ a ∈ A, 2 ≤ a) ∧ SquareCondition A

def PrimitiveRootMod (a p : ℕ) : Prop :=
  ¬ p ∣ a ∧ orderOf (a : ZMod p) = p - 1

def SimultaneousAt (A : Finset ℕ) (p : ℕ) : Prop :=
  p.Prime ∧ ∀ a ∈ A, PrimitiveRootMod a p

def goodPrimes (A : Finset ℕ) (x : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊2 * x⌋₊ + 1)).filter fun p =>
    x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧ SimultaneousAt A p

def primeCount (A : Finset ℕ) (x : ℝ) : ℝ := (goodPrimes A x).card

def PositiveDyadicLowerBound (A : Finset ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ x₀ : ℝ, 2 ≤ x₀ ∧
    ∀ x : ℝ, x₀ ≤ x → c * (x / Real.log x) ≤ primeCount A x

def MainClaim : Prop :=
  ∀ A : Finset ℕ, Admissible A → PositiveDyadicLowerBound A

end SimultaneousPrimitiveRoots
