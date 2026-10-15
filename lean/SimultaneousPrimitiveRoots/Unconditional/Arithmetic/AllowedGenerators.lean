module

public import SimultaneousPrimitiveRoots.Unconditional.Arithmetic.PowerClasses

/-!
# Adjusting generators to an allowed power class

The algebraic argument of [A, `lem:balanced-generators`, A-02:0209–0213]. If
the image of the units is complementary to `B`, every generator can be
multiplied by a unit so that its class belongs to `B`. Two such unit-related
generators differ by a power of a unit when the power-class unit map is injective.

These are group-theoretic statements. The actual S-unit embedding, the existence
of exterior ideal generators and the compact set of balanced representatives
are separate arithmetic/topological inputs.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Arithmetic

variable {U A V : Type*} [CommGroup U] [CommGroup A] [CommGroup V]

/-- **Every class can be adjusted into the chosen complement by a unit.** -/
theorem exists_unit_adjusted_allowed (f : U →* A) (q : A →* V) {B : Subgroup V}
    (hB : IsCompl (q.comp f).range B) (a : A) :
    ∃ u : U, q (f u * a) ∈ B := by
  have ha : q a ∈ (q.comp f).range ⊔ B := by rw [hB.sup_eq_top]; trivial
  obtain ⟨e, he, b, hb, hab⟩ := Subgroup.mem_sup.mp ha
  obtain ⟨u, rfl⟩ := he
  refine ⟨u⁻¹, ?_⟩
  have hqa : q a = q (f u) * b := hab.symm
  simpa only [map_mul, map_inv, hqa, inv_mul_cancel_left] using hb

/-- A unit which takes one allowed generator to another has trivial class. -/
theorem unit_class_eq_one_of_allowed (f : U →* A) (q : A →* V) {B : Subgroup V}
    (hB : IsCompl (q.comp f).range B) {a : A} {u : U}
    (ha : q a ∈ B) (hua : q (f u * a) ∈ B) : q (f u) = 1 := by
  have huE : q (f u) ∈ (q.comp f).range := ⟨u, rfl⟩
  have huB : q (f u) ∈ B := by
    have h := B.mul_mem hua (B.inv_mem ha)
    simpa only [map_mul, mul_inv_cancel_right] using h
  exact Subgroup.disjoint_def.mp hB.disjoint huE huB

/-- **Injectivity on power classes identifies the kernel on units with unit powers.** -/
theorem unit_powerClass_eq_one_iff {G : Type*} [CommGroup G] (f : U →* G) (n : ℕ)
    (hf : Function.Injective (powerClassMap f n)) (u : U) :
    powerClassMk G n (f u) = 1 ↔ ∃ t : U, t ^ n = u := by
  rw [← powerClassMk_eq_one_iff U n u]
  constructor
  · intro h
    apply hf
    simpa only [powerClassMap_mk, map_one] using h
  · intro h
    have hm := congrArg (powerClassMap f n) h
    simpa only [powerClassMap_mk, map_one] using hm

/-- **Allowed unit-related generators differ by an `n`th power of a unit.** -/
theorem exists_unit_power_of_allowed {G : Type*} [CommGroup G] (f : U →* G) (n : ℕ)
    (hf : Function.Injective (powerClassMap f n)) {B : Subgroup (PowerClass G n)}
    (hB : IsCompl ((powerClassMk G n).comp f).range B) {a : G} {u : U}
    (ha : powerClassMk G n a ∈ B) (hua : powerClassMk G n (f u * a) ∈ B) :
    ∃ t : U, t ^ n = u :=
  (unit_powerClass_eq_one_iff f n hf u).mp
    (unit_class_eq_one_of_allowed f (powerClassMk G n) hB ha hua)

/-- In exponent six it is enough to know injectivity on square and cube classes. -/
theorem exists_unit_sixth_power_of_allowed {G : Type*} [CommGroup G] (f : U →* G)
    (h₂ : Function.Injective (powerClassMap f 2))
    (h₃ : Function.Injective (powerClassMap f 3)) {B : Subgroup (PowerClass G 6)}
    (hB : IsCompl ((powerClassMk G 6).comp f).range B) {a : G} {u : U}
    (ha : powerClassMk G 6 a ∈ B) (hua : powerClassMk G 6 (f u * a) ∈ B) :
    ∃ t : U, t ^ 6 = u :=
  exists_unit_power_of_allowed f 6 (powerClassMap_injective_six f h₂ h₃) hB ha hua

/-- **The complete algebraic normalization step for sixth-power classes.**
The complement can be supplied by `exists_sextic_isotropic_compl`.
-/
theorem allowed_sextic_normalization {G : Type*} [CommGroup G] (f : U →* G)
    (h₂ : Function.Injective (powerClassMap f 2))
    (h₃ : Function.Injective (powerClassMap f 3)) {B : Subgroup (PowerClass G 6)}
    (hB : IsCompl (powerClassMap f 6).range B) :
    (∀ a : G, ∃ u : U, powerClassMk G 6 (f u * a) ∈ B) ∧
      (∀ (a : G) (u : U), powerClassMk G 6 a ∈ B →
        powerClassMk G 6 (f u * a) ∈ B → ∃ t : U, t ^ 6 = u) := by
  rw [powerClassMap_range] at hB
  exact ⟨exists_unit_adjusted_allowed f (powerClassMk G 6) hB,
    fun _ _ ha hua => exists_unit_sixth_power_of_allowed f h₂ h₃ hB ha hua⟩

end SimultaneousPrimitiveRoots.Unconditional.Arithmetic
