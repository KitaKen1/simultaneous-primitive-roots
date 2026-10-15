module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod

@[expose] public section

namespace SimultaneousPrimitiveRoots

/-- A compatible assignment on vectors extends to a linear functional.
For the square-class application, K is ZMod 2 and every assigned value is 1. -/
theorem exists_functional_of_relations
    {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (v : ι → V) (w : ι → K)
    (hrel : ∀ c : ι →₀ K,
      Finsupp.linearCombination K v c = 0 → Finsupp.linearCombination K w c = 0) :
    ∃ f : V →ₗ[K] K, ∀ i, f (v i) = w i := by
  let L := Finsupp.linearCombination K v
  let b := Finsupp.linearCombination K w
  have hk : LinearMap.ker L.rangeRestrict ≤ LinearMap.ker b := by
    rw [LinearMap.ker_rangeRestrict]
    exact hrel
  have hsurj : Function.Surjective L.rangeRestrict := by
    rintro ⟨y, c, rfl⟩
    exact ⟨c, rfl⟩
  let l : LinearMap.range L →ₗ[K] K :=
    (LinearMap.ker L.rangeRestrict).liftQ b hk |>.comp
      (L.rangeRestrict.quotKerEquivOfSurjective hsurj).symm.toLinearMap
  obtain ⟨f, hf⟩ := l.exists_extend
  have he (c : ι →₀ K) : f (L c) = b c := by
    have h := LinearMap.congr_fun hf (L.rangeRestrict c)
    have h' : l (L.rangeRestrict c) = b c := by
      dsimp [l]
      rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
      rfl
    exact h.trans h'
  refine ⟨f, fun i => ?_⟩
  simpa [L, b] using he (Finsupp.single i 1)

theorem exists_binary_functional
    {V ι : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (v : ι → V)
    (hrel : ∀ c : ι →₀ ZMod 2,
      Finsupp.linearCombination (ZMod 2) v c = 0 →
      Finsupp.linearCombination (ZMod 2) (fun _ : ι => (1 : ZMod 2)) c = 0) :
    ∃ f : V →ₗ[ZMod 2] ZMod 2, ∀ i, f (v i) = 1 :=
  by
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact exists_functional_of_relations (K := ZMod 2) v (fun _ => 1) hrel

end SimultaneousPrimitiveRoots
