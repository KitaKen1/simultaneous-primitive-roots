module

public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
public import Mathlib.NumberTheory.MulChar.Basic

/-!
# Lifting characters of a finite field to a finite extension

Let `K / k` be an extension of finite fields. A multiplicative character `χ` of `k` lifts to the
multiplicative character `χ ∘ N_{K/k}` of `K`, and an additive character `ψ` of `k` lifts to the
additive character `ψ ∘ Tr_{K/k}` of `K`. These are the characters appearing in the
Hasse--Davenport lifting relation.

## Main definitions and results

* `normLift K χ : MulChar K R`, the lift `χ ∘ Algebra.norm k` of `χ : MulChar k R`. It is a genuine
  multiplicative character (with the value `0` at `0`) because the norm of `0` is `0`.
* `normLift_one`, `normLift_mul`, `normLift_pow`, `normLift_inv`, `normLiftHom`: the lift is a
  homomorphism of groups of multiplicative characters.
* `normLift_ne_one`: the lift of a nontrivial multiplicative character is nontrivial, because the
  norm of an extension of finite fields is surjective (`FiniteField.unitsMap_norm_surjective`).
  Consequently the lift is injective (`normLift_injective`, `normLift_eq_one_iff`).
* `normLift_ringHomComp`: the lift commutes with a change of the target ring.
* `traceLift K ψ : AddChar K R`, the lift `ψ ∘ Algebra.trace k K` of `ψ : AddChar k R`.
* `traceLift_ne_one`, `traceLift_isPrimitive`: the lift of a nontrivial (equivalently, primitive)
  additive character is nontrivial (primitive), because the trace is surjective
  (`Algebra.trace_surjective`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Arithmetic

/-! ### The norm lift of a multiplicative character -/

section NormLift

variable {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K] [Finite K]
  {R : Type*} [CommMonoidWithZero R]

/-- The lift `χ ∘ N_{K/k}` of a multiplicative character `χ` of a field `k` to a finite field
`K` containing `k`. -/
noncomputable def normLift (χ : MulChar k R) : MulChar K R where
  toMonoidHom := χ.toMonoidHom.comp (Algebra.norm k)
  map_nonunit' x hx := by
    have hx0 : x = 0 := by simpa [isUnit_iff_ne_zero] using hx
    change χ (Algebra.norm k x) = 0
    rw [hx0, Algebra.norm_zero, χ.map_zero]

@[simp]
theorem normLift_apply (χ : MulChar k R) (x : K) :
    normLift K χ x = χ (Algebra.norm k x) :=
  rfl

/-- The lift of the trivial multiplicative character is trivial. -/
@[simp]
theorem normLift_one : normLift K (1 : MulChar k R) = 1 := by
  ext x
  rw [normLift_apply, MulChar.one_apply_coe, MulChar.one_apply]
  exact x.isUnit.map (Algebra.norm k)

/-- The lift is multiplicative in the character. -/
theorem normLift_mul (χ φ : MulChar k R) :
    normLift K (χ * φ) = normLift K χ * normLift K φ := by
  ext x
  simp only [normLift_apply, MulChar.mul_apply]

/-- The lift `χ ↦ χ ∘ N_{K/k}` as a homomorphism of groups of multiplicative characters. -/
noncomputable def normLiftHom : MulChar k R →* MulChar K R where
  toFun := normLift K
  map_one' := normLift_one K
  map_mul' := normLift_mul K

@[simp]
theorem normLiftHom_apply (χ : MulChar k R) : normLiftHom K χ = normLift K χ :=
  rfl

theorem normLift_pow (χ : MulChar k R) (n : ℕ) : normLift K (χ ^ n) = normLift K χ ^ n :=
  map_pow (normLiftHom K) χ n

theorem normLift_inv (χ : MulChar k R) : normLift K χ⁻¹ = (normLift K χ)⁻¹ :=
  map_inv (normLiftHom K) χ

/-- The lift of a nontrivial multiplicative character is nontrivial, because the norm of an
extension of finite fields is surjective. -/
theorem normLift_ne_one {χ : MulChar k R} (hχ : χ ≠ 1) : normLift K χ ≠ 1 := by
  obtain ⟨a, ha⟩ := MulChar.ne_one_iff.mp hχ
  obtain ⟨x, rfl⟩ := FiniteField.unitsMap_norm_surjective k K a
  exact MulChar.ne_one_iff.mpr ⟨x, ha⟩

@[simp]
theorem normLift_eq_one_iff {χ : MulChar k R} : normLift K χ = 1 ↔ χ = 1 :=
  ⟨fun h => by_contra fun hχ => normLift_ne_one K hχ h, fun h => h ▸ normLift_one K⟩

/-- The lift `χ ↦ χ ∘ N_{K/k}` is injective. -/
theorem normLift_injective : Function.Injective (normLift K : MulChar k R → MulChar K R) :=
  (injective_iff_map_eq_one (normLiftHom K)).mpr fun _ h => (normLift_eq_one_iff K).mp h

end NormLift

/-- The lift commutes with composing a multiplicative character with a ring homomorphism of the
targets. -/
theorem normLift_ringHomComp {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K] [Finite K]
    {R R' : Type*} [CommRing R] [CommRing R'] (χ : MulChar k R) (f : R →+* R') :
    normLift K (χ.ringHomComp f) = (normLift K χ).ringHomComp f :=
  MulChar.ext' fun _ => rfl

/-! ### The trace lift of an additive character -/

section TraceLift

variable {k : Type*} [Field k] (K : Type*) [Field K] [Algebra k K] {R : Type*} [CommMonoid R]

/-- The lift `ψ ∘ Tr_{K/k}` of an additive character `ψ` of a field `k` to an extension `K`. -/
noncomputable def traceLift (ψ : AddChar k R) : AddChar K R :=
  ψ.compAddMonoidHom (Algebra.trace k K).toAddMonoidHom

@[simp]
theorem traceLift_apply (ψ : AddChar k R) (x : K) :
    traceLift K ψ x = ψ (Algebra.trace k K x) :=
  rfl

/-- The lift of the trivial additive character is trivial. -/
@[simp]
theorem traceLift_one : traceLift K (1 : AddChar k R) = 1 := by
  ext x
  rw [traceLift_apply, AddChar.one_apply, AddChar.one_apply]

variable [Finite K]

/-- The lift of a nontrivial additive character is nontrivial, because the trace of an extension
of finite fields is surjective. -/
theorem traceLift_ne_one {ψ : AddChar k R} (hψ : ψ ≠ 1) : traceLift K ψ ≠ 1 := by
  obtain ⟨a, ha⟩ := AddChar.ne_one_iff.mp hψ
  obtain ⟨x, rfl⟩ := Algebra.trace_surjective k K a
  exact AddChar.ne_one_iff.mpr ⟨x, ha⟩

@[simp]
theorem traceLift_eq_one_iff {ψ : AddChar k R} : traceLift K ψ = 1 ↔ ψ = 1 :=
  ⟨fun h => by_contra fun hψ => traceLift_ne_one K hψ h, fun h => h ▸ traceLift_one K⟩

/-- The lift of a primitive additive character is primitive. -/
theorem traceLift_isPrimitive {ψ : AddChar k R} (hψ : ψ.IsPrimitive) :
    (traceLift K ψ).IsPrimitive := by
  refine AddChar.IsPrimitive.of_ne_one (traceLift_ne_one K fun h => ?_)
  exact hψ one_ne_zero (by rw [AddChar.mulShift_one, h])

end TraceLift

end SimultaneousPrimitiveRoots.Unconditional.Arithmetic
