module

public import SimultaneousPrimitiveRoots.Unconditional.Arithmetic.PowerClasses
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Data.Fintype.Pi

/-!
# Power classes of a product of local multiplicative groups

Taking power classes commutes with products, even before imposing finiteness.
This identifies the local product quotient used in [A] with the product of the
local power-class groups. The unit map is natural under this identification.
Its image is a joint image, not the product of the separate local unit images.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Unconditional.Arithmetic

variable {ι : Type*} (G : ι → Type*) [∀ i, CommGroup (G i)]

/-- Apply the canonical power-class reduction at every coordinate. -/
def powerClassPiMap (n : ℕ) : PowerClass (∀ i, G i) n →* ∀ i, PowerClass (G i) n :=
  MonoidHom.pi fun i => powerClassMap (Pi.evalMonoidHom G i) n

@[simp]
theorem powerClassPiMap_mk (n : ℕ) (a : ∀ i, G i) :
    powerClassPiMap G n (powerClassMk (∀ i, G i) n a) =
      fun i => powerClassMk (G i) n (a i) := rfl

theorem powerClassPiMap_injective (n : ℕ) : Function.Injective (powerClassPiMap G n) := by
  classical
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨a, rfl⟩ := powerClassMk_surjective (∀ i, G i) n x
  have h := MonoidHom.mem_ker.mp hx
  have hi : ∀ i, ∃ b : G i, b ^ n = a i := fun i =>
    (powerClassMk_eq_one_iff (G i) n (a i)).mp (congrFun h i)
  choose b hb using hi
  change powerClassMk (∀ i, G i) n a = 1
  exact (powerClassMk_eq_one_iff (∀ i, G i) n a).mpr ⟨b, funext hb⟩

theorem powerClassPiMap_surjective (n : ℕ) : Function.Surjective (powerClassPiMap G n) := by
  intro x
  choose a ha using fun i => powerClassMk_surjective (G i) n (x i)
  exact ⟨powerClassMk (∀ i, G i) n a, funext ha⟩

/-- **The quotient of a product is the product of the power-class quotients.** -/
def powerClassPiEquiv (n : ℕ) :
    PowerClass (∀ i, G i) n ≃* ∀ i, PowerClass (G i) n :=
  MulEquiv.ofBijective (powerClassPiMap G n)
    ⟨powerClassPiMap_injective G n, powerClassPiMap_surjective G n⟩

@[simp]
theorem powerClassPiEquiv_mk (n : ℕ) (a : ∀ i, G i) :
    powerClassPiEquiv G n (powerClassMk (∀ i, G i) n a) =
      fun i => powerClassMk (G i) n (a i) := rfl

/-- The global unit map retains the same unit at all local coordinates. -/
theorem powerClassPiEquiv_natural {U : Type*} [CommGroup U]
    (f : U →* ∀ i, G i) (n : ℕ) (u : PowerClass U n) :
    powerClassPiEquiv G n (powerClassMap f n u) =
      fun i => powerClassMap ((Pi.evalMonoidHom G i).comp f) n u := by
  obtain ⟨a, rfl⟩ := powerClassMk_surjective U n u
  rfl

/-- A finite family of finite local power-class groups gives a finite global quotient. -/
theorem powerClassPi_finite [Finite ι] (n : ℕ) [∀ i, Finite (PowerClass (G i) n)] :
    Finite (PowerClass (∀ i, G i) n) := by
  classical
  let : Fintype ι := Fintype.ofFinite _
  let : ∀ i, Fintype (PowerClass (G i) n) := fun i => Fintype.ofFinite _
  exact Finite.of_equiv (∀ i, PowerClass (G i) n) (powerClassPiEquiv G n).symm.toEquiv

end SimultaneousPrimitiveRoots.Unconditional.Arithmetic
