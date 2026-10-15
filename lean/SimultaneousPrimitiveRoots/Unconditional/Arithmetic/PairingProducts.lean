module

public import SimultaneousPrimitiveRoots.Unconditional.Arithmetic.PairingComplement
public import Mathlib.Algebra.BigOperators.Pi

/-!
# The product pairing over a finite set of places

Nondegeneracy follows by testing at a single coordinate, rather than computing
a matrix determinant. Local alternation passes to the product. The subgroup E
is allowed to couple the coordinates, as the S-unit image does; only its global
isotropy and cardinality are hypotheses of the complement theorem.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Arithmetic

open scoped BigOperators

variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, CommGroup (V i)]
    {μ : Type*} [CommGroup μ]

/-- Multiply the local pairings with values in a common group of roots of unity. -/
def piPairing (H : ∀ i, V i →* V i →* μ) : (∀ i, V i) →* (∀ i, V i) →* μ where
  toFun x :=
    { toFun := fun y => ∏ i, H i (x i) (y i)
      map_one' := by simp
      map_mul' := fun y z => by simp [map_mul, Finset.prod_mul_distrib] }
  map_one' := by ext y; simp
  map_mul' x z := by ext y; simp [map_mul, MonoidHom.mul_apply, Finset.prod_mul_distrib]

@[simp]
theorem piPairing_apply (H : ∀ i, V i →* V i →* μ) (x y : ∀ i, V i) :
    piPairing H x y = ∏ i, H i (x i) (y i) := rfl

/-- A test supported at a single place isolates that local pairing. -/
theorem piPairing_mulSingle_right [DecidableEq ι] (H : ∀ i, V i →* V i →* μ)
    (x : ∀ i, V i) (i : ι) (a : V i) :
    piPairing H x (Pi.mulSingle i a) = H i (x i) a := by
  rw [piPairing_apply, Fintype.prod_eq_single i]
  · simp
  · intro j hji
    simp [Pi.mulSingle_eq_of_ne hji]

/-- **Local nondegeneracy implies nondegeneracy on the finite product.** -/
theorem piPairing_nondegenerate (H : ∀ i, V i →* V i →* μ)
    (hnd : ∀ i x, (∀ y, H i x y = 1) → x = 1) :
    ∀ x, (∀ y, piPairing H x y = 1) → x = 1 := by
  classical
  intro x hx
  funext i
  exact hnd i (x i) (fun a => by
    simpa only [piPairing_mulSingle_right] using hx (Pi.mulSingle i a))

theorem piPairing_alternating (H : ∀ i, V i →* V i →* μ)
    (halt : ∀ i x, H i x x = 1) : ∀ x, piPairing H x x = 1 := by
  intro x
  simp [piPairing_apply, halt]

/-- **An isotropic complement for the global subgroup in a product of local spaces.** -/
theorem exists_piPairing_isotropic_compl {ℓ : ℕ} [Fact ℓ.Prime] [∀ i, Finite (V i)]
    (hV : ∀ i x, (x : V i) ^ ℓ = 1) (e : μ ≃* Multiplicative (ZMod ℓ))
    (H : ∀ i, V i →* V i →* μ)
    (hnd : ∀ i x, (∀ y, H i x y = 1) → x = 1)
    (halt : ∀ i x, H i x x = 1) {E : Subgroup (∀ i, V i)}
    (hE : ∀ x ∈ E, ∀ y ∈ E, piPairing H x y = 1)
    (hcard : Nat.card E ^ 2 = Nat.card (∀ i, V i)) :
    (∀ x, (∀ y ∈ E, piPairing H x y = 1) → x ∈ E) ∧
      ∃ C : Subgroup (∀ i, V i), IsCompl E C ∧
        ∀ x ∈ C, ∀ y ∈ C, piPairing H x y = 1 :=
  exists_isotropic_compl (fun x => funext fun i => hV i (x i)) e (piPairing H)
    (piPairing_nondegenerate H hnd) (piPairing_alternating H halt) hE hcard

end SimultaneousPrimitiveRoots.Unconditional.Arithmetic
