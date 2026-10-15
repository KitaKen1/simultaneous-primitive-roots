module

public import SimultaneousPrimitiveRoots.Hecke.HeckeFE
public import Mathlib.RingTheory.DedekindDomain.Different

/-!
# The trace dual lattice of an ideal is the dual fractional ideal

For a `ℚ`-basis `b` of `K`, the lattice `ℤ b^∨` of the trace-dual basis is the set of `x` with
`Tr(x a) ∈ ℤ` for all `a ∈ ℤ b` (`latticeSet_traceDual_eq`). For the lattice of an integral ideal
`J` this is Mathlib's dual fractional ideal `FractionalIdeal.dual ℤ ℚ J = (J 𝔡)⁻¹`.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField Ideal Module
open scoped nonZeroDivisors

variable {K : Type*} [Field K] [NumberField K]

/-- The trace dual of a subset of `K`. -/
def traceDualSet (L : Set K) : Set K :=
  {x | ∀ a ∈ L, ∃ k : ℤ, Algebra.trace ℚ K (x * a) = k}

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The lattice of the trace-dual basis is the trace dual of the lattice.** -/
theorem latticeSet_traceDual_eq (b : Module.Basis ι ℚ K) :
    latticeSet (b.traceDual : ι → K) = traceDualSet (latticeSet (b : ι → K)) := by
  ext x
  rw [mem_latticeSet_traceDual_iff]
  constructor
  · intro h a ha
    obtain ⟨m, rfl⟩ := ha
    choose k hk using h
    refine ⟨∑ j, m j * k j, ?_⟩
    unfold latticePt
    rw [Finset.mul_sum, map_sum]
    push_cast
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_smul_comm, map_zsmul, hk j, zsmul_eq_mul]
  · intro h j
    exact h (b j) ⟨fun i => if i = j then 1 else 0, by
      unfold latticePt
      simp⟩

/-- The trace dual of an integral ideal, as a set, is Mathlib's dual fractional ideal. -/
theorem traceDualSet_idealInK (J : (Ideal (𝓞 K))⁰) :
    traceDualSet (idealInK (J : Ideal (𝓞 K))) =
      ((FractionalIdeal.dual ℤ ℚ ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :
        FractionalIdeal (𝓞 K)⁰ K) : Set K) := by
  have hJ0 : ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    rw [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
    exact nonZeroDivisors.coe_ne_zero J
  ext x
  rw [SetLike.mem_coe, FractionalIdeal.mem_dual hJ0]
  constructor
  · intro h a ha
    rw [FractionalIdeal.mem_coeIdeal] at ha
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨k, hk⟩ := h _ ⟨a', ha', rfl⟩
    exact ⟨k, by rw [Algebra.traceForm_apply, hk]; rfl⟩
  · intro h a ha
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨k, hk⟩ := h (algebraMap (𝓞 K) K a') (FractionalIdeal.mem_coeIdeal_of_mem _ ha')
    refine ⟨k, ?_⟩
    rw [Algebra.traceForm_apply] at hk
    rw [← hk]
    rfl

/-- The dual of `J` is `(J 𝔡)⁻¹`. -/
theorem dual_eq_inv_mul_different (J : (Ideal (𝓞 K))⁰) :
    FractionalIdeal.dual ℤ ℚ ((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) =
      (((J : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) *
        ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
  rw [FractionalIdeal.dual_eq_mul_inv, coeIdeal_differentIdeal ℤ ℚ, mul_inv, inv_inv, mul_comm]

end SimultaneousPrimitiveRoots.Hecke

end
