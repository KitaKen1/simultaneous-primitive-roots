module

public import SimultaneousPrimitiveRoots.Statement
public import SimultaneousPrimitiveRoots.LinearCompatibility
public import Compat4331.NatSquares
public import Mathlib.Tactic

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots

def squareVector (a : ℕ) : ℕ → ZMod 2 := fun p => (a.factorization p : ZMod 2)

theorem squareVector_prod {B : Finset ℕ} (hne : ∀ a ∈ B, a ≠ 0) :
    squareVector (∏ a ∈ B, a) = ∑ a ∈ B, squareVector a := by
  ext p
  simp only [squareVector, Nat.factorization_prod hne, Finsupp.finsetSum_apply,
    Nat.cast_sum, Finset.sum_apply]

theorem isSquare_of_squareVector_eq_zero {a : ℕ} (ha : squareVector a = 0) :
    IsSquare a := by
  apply Nat.isSquare_iff_even_factorization.mpr
  intro p _
  apply ZMod.natCast_eq_zero_iff_even.mp
  exact congrFun ha p

theorem binary_eq_one_of_ne_zero {z : ZMod 2} (hz : z ≠ 0) : z = 1 := by
  have h : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide +kernel
  exact (h z).resolve_left hz

/-- SQ gives a linear functional taking the value 1 on every square-class vector. -/
theorem exists_squareClass_functional {A : Finset ℕ}
    (hpos : ∀ a ∈ A, 2 ≤ a) (hSQ : SquareCondition A) :
    ∃ f : (ℕ → ZMod 2) →ₗ[ZMod 2] ZMod 2, ∀ a ∈ A, f (squareVector a) = 1 := by
  classical
  have hrel : ∀ c : A →₀ ZMod 2,
      Finsupp.linearCombination (ZMod 2) (fun a : A => squareVector a.val) c = 0 →
      Finsupp.linearCombination (ZMod 2) (fun _ : A => (1 : ZMod 2)) c = 0 := by
    intro c hc
    have hcoef (i : A) (hi : i ∈ c.support) : c i = 1 :=
      binary_eq_one_of_ne_zero (Finsupp.mem_support_iff.mp hi)
    have hsum : (∑ i ∈ c.support, squareVector i.val) = 0 := by
      calc
        (∑ i ∈ c.support, squareVector i.val) =
            ∑ i ∈ c.support, c i • squareVector i.val := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [hcoef i hi, one_smul]
        _ = 0 := hc
    let B : Finset ℕ := c.support.image Subtype.val
    have hBA : B ⊆ A := by
      intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact i.property
    have hBvec : squareVector (∏ a ∈ B, a) = 0 := by
      rw [squareVector_prod (fun a ha => by have := hpos a (hBA ha); omega)]
      change (∑ a ∈ c.support.image Subtype.val, squareVector a) = 0
      rw [Finset.sum_image (fun _ _ _ _ heq => Subtype.ext heq)]
      exact hsum
    have hnotodd : ¬ Odd B.card := fun ho =>
      hSQ B hBA ho (isSquare_of_squareVector_eq_zero hBvec)
    have heven : Even B.card := Nat.not_odd_iff_even.mp hnotodd
    have hcard : B.card = c.support.card := Finset.card_image_of_injective _ Subtype.val_injective
    have hzero : (c.support.card : ZMod 2) = 0 := by
      apply ZMod.natCast_eq_zero_iff_even.mpr
      rwa [hcard] at heven
    change (∑ i ∈ c.support, c i • (1 : ZMod 2)) = 0
    calc
      (∑ i ∈ c.support, c i • (1 : ZMod 2)) = ∑ _i ∈ c.support, (1 : ZMod 2) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hcoef i hi, one_smul]
      _ = (c.support.card : ZMod 2) := by simp
      _ = 0 := hzero
  obtain ⟨f, hf⟩ := exists_binary_functional (fun a : A => squareVector a.val) hrel
  exact ⟨f, fun a ha => hf ⟨a, ha⟩⟩

end SimultaneousPrimitiveRoots
