/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Copyright (c) 2024 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot, Yongle Hu, Jiedong Jiang
-/
/- Backport from Mathlib f6090c7095e1e56b3464c1daba5f24631f1290d2:
RingTheory/LocalRing/ResidueField/Separable.lean and
NumberTheory/RamificationInertia/Galois.lean. -/
module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.NumberTheory.RamificationInertia.Galois

public section

namespace Algebra

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] (p : Ideal A) [p.IsPrime]

/-- Every residue field extension above `p` is separable, with its canonical localization
algebra structure. This is the later Mathlib predicate with its original assumptions. -/
class HasSeparableResidueFieldsAt : Prop where
  isSeparable' (q : Ideal B) [q.IsPrime] [q.LiesOver p] :
    letI := Localization.AtPrime.algebraOfLiesOver p q
    Algebra.IsSeparable p.ResidueField q.ResidueField

instance [Algebra.IsIntegral A B] [PerfectField p.ResidueField] :
    HasSeparableResidueFieldsAt A B p where
  isSeparable' q _ _ :=
    let := Localization.AtPrime.algebraOfLiesOver p q
    IsAlgebraic.isSeparable_of_perfectField

end Algebra

namespace Compat4331

open Ideal Algebra Module
open scoped Pointwise

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [IsGaloisGroup G R S] [Finite G]

attribute [local instance] Ideal.Quotient.field in
private theorem card_stabilizer_eq_card_inertia_mul_finrank (p : Ideal R) [p.IsPrime]
    (P : Ideal S) [P.LiesOver p] [P.IsPrime] [Algebra.HasSeparableResidueFieldsAt R S p] :
    Nat.card (MulAction.stabilizer G P) = Nat.card (inertia G P) * P.inertiaDeg R := by
  let := Localization.AtPrime.algebraOfLiesOver p P
  let : Algebra.IsSeparable p.ResidueField P.ResidueField :=
    Algebra.HasSeparableResidueFieldsAt.isSeparable' P
  have heq : (algebraMap (S ⧸ P) P.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ P)) =
      (algebraMap p.ResidueField P.ResidueField).comp (algebraMap (R ⧸ p) p.ResidueField) := by
    ext
    simp [← IsScalarTower.algebraMap_apply]
  let := ((algebraMap (S ⧸ P) P.ResidueField).comp (algebraMap (R ⧸ p) (S ⧸ P))).toAlgebra
  have : IsScalarTower (R ⧸ p) (S ⧸ P) P.ResidueField := .of_algebraMap_eq' rfl
  have : IsScalarTower (R ⧸ p) p.ResidueField P.ResidueField := .of_algebraMap_eq' heq
  have : IsGalois p.ResidueField P.ResidueField :=
    { __ := Ideal.IsFractionRing.normal G p P p.ResidueField P.ResidueField }
  have : Module.Finite p.ResidueField P.ResidueField :=
    Ideal.IsFractionRing.finite_of_isInvariant G p P p.ResidueField P.ResidueField
  have : Subgroup.index _ = _ := Nat.card_congr
    (IsFractionRing.stabilizerQuotientInertiaEquiv G p P
      p.ResidueField P.ResidueField).toEquiv
  rw [inertiaDeg_eq p P, ← IsGalois.card_aut_eq_finrank p.ResidueField P.ResidueField, ← this,
    ← ((inertia G P).subgroupOf (MulAction.stabilizer G P)).card_mul_index,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inertia_le_stabilizer (M := G) P)).toEquiv,
    AddSubgroup.subgroupOf_inertia]

private theorem ncard_primesOver_mul_card_inertia_mul_finrank (p : Ideal R) [p.IsPrime]
    (P : Ideal S) [P.LiesOver p] [P.IsPrime] [Algebra.HasSeparableResidueFieldsAt R S p] :
    (p.primesOver S).ncard * Nat.card (P.inertia G) * P.inertiaDeg R = Nat.card G := by
  rw [mul_assoc, ← card_stabilizer_eq_card_inertia_mul_finrank p P,
    ← Algebra.IsInvariant.orbit_eq_primesOver R S G p P]
  simpa using Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G P)

/-- The inertia count under residue separability, retaining the later Mathlib generality. -/
theorem card_inertia_eq_ramificationIdxIn [IsDomain R] [IsDomain S]
    [Module.Finite R S] [Module.Flat R S] (p : Ideal R) (P : Ideal S)
    [P.LiesOver p] [p.IsPrime] [P.IsPrime] [Algebra.HasSeparableResidueFieldsAt R S p] :
    Nat.card (P.inertia G) = Ideal.ramificationIdxIn p S := by
  have H := ncard_primesOver_mul_card_inertia_mul_finrank (G := G) p P
  rw [← inertiaDegIn_eq_inertiaDeg p P G] at H
  have h1 : (p.primesOver S).ncard ≠ 0 := by grind [Nat.card_pos]
  have h2 : p.inertiaDegIn S ≠ 0 := by grind [Nat.card_pos]
  rwa [← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p S G,
    mul_assoc, mul_right_inj' h1, mul_left_inj' h2] at H

end Compat4331
