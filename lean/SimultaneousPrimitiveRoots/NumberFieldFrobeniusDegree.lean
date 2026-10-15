module

public import SimultaneousPrimitiveRoots.NumberFieldFrobenius
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.Ideal.GoingUp

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
noncomputable section

variable {E K : Type*} [Field E] [Field K] [NumberField E] [NumberField K]
  [Algebra E K] [IsGalois E K]

/-- The actual Frobenius is the identity exactly when every residue is
fixed by the base-cardinality power, provided the prime is unramified. -/
theorem numberFieldFrobenius_eq_one_iff_residue_fixed
    (P : HeightOneSpectrum (𝓞 K))
    [Algebra.IsUnramifiedAt (𝓞 E) P.asIdeal] :
    numberFieldFrobenius (E := E) P = 1 ↔
      ∀ x : 𝓞 K ⧸ P.asIdeal,
        x ^ Nat.card (𝓞 E ⧸ P.asIdeal.under (𝓞 E)) = x := by
  constructor
  · intro h x
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hz := numberFieldFrobenius_condition (E := E) P z
    rw [h] at hz
    change z - z ^ (P.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K))).absNorm ∈ P.asIdeal at hz
    have he := (Ideal.Quotient.eq).mpr hz
    simpa only [map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply, Ideal.under_def] using he.symm
  · intro h
    apply numberField_frobenius_unique P _ 1 (numberFieldFrobenius_condition P)
    intro z
    change z - z ^ (P.asIdeal.comap (algebraMap (𝓞 E) (𝓞 K))).absNorm ∈ P.asIdeal
    apply Ideal.Quotient.eq.mp
    simpa only [map_pow, Ideal.absNorm_apply, Submodule.cardQuot_apply, Ideal.under_def] using
      (h (Ideal.Quotient.mk P.asIdeal z)).symm

/-- Reuse the finite-field Frobenius order theorem; its root-count proof
already contains the polynomial argument needed for degree one. -/
theorem finiteField_card_power_fixed_iff_finrank_one
    (F L : Type*) [Field F] [Field L] [Fintype F] [Finite L] [Algebra F L] :
    (∀ x : L, x ^ Nat.card F = x) ↔ Module.finrank F L = 1 := by
  rw [← FiniteField.orderOf_frobeniusAlgHom F L, orderOf_eq_one_iff]
  constructor
  · intro h
    ext x
    simpa only [FiniteField.coe_frobeniusAlgHom, AlgHom.one_apply,
      Fintype.card_eq_nat_card] using h x
  · intro h x
    have hx := DFunLike.congr_fun h x
    simpa only [FiniteField.coe_frobeniusAlgHom, AlgHom.one_apply,
      Fintype.card_eq_nat_card] using hx

/-- The identity test for the actual arithmetic Frobenius is the actual
relative residue-degree-one test. No decomposition-group construction
or full Frobenius-order theorem over number fields is required. -/
theorem numberFieldFrobenius_eq_one_iff_inertiaDeg_one
    (P : HeightOneSpectrum (𝓞 K))
    [Algebra.IsUnramifiedAt (𝓞 E) P.asIdeal] :
    numberFieldFrobenius (E := E) P = 1 ↔ P.asIdeal.inertiaDeg (𝓞 E) = 1 := by
  let : Field (𝓞 K ⧸ P.asIdeal) := Ideal.Quotient.field _
  let : (P.asIdeal.under (𝓞 E)).IsMaximal := Ideal.IsMaximal.under (𝓞 E) P.asIdeal
  let : Field (𝓞 E ⧸ P.asIdeal.under (𝓞 E)) := Ideal.Quotient.field _
  let := Ideal.Quotient.algebraOfLiesOver P.asIdeal (P.asIdeal.under (𝓞 E))
  let : Finite (𝓞 E ⧸ P.asIdeal.under (𝓞 E)) :=
    (IsArithFrobAt.arithFrobAt (𝓞 E) Gal(K/E) P.asIdeal).finite_quotient
  let := Fintype.ofFinite (𝓞 E ⧸ P.asIdeal.under (𝓞 E))
  rw [numberFieldFrobenius_eq_one_iff_residue_fixed,
    Ideal.inertiaDeg_eq_of_isMaximal (P.asIdeal.under (𝓞 E)) P.asIdeal]
  exact finiteField_card_power_fixed_iff_finrank_one _ _

end
end SimultaneousPrimitiveRoots
