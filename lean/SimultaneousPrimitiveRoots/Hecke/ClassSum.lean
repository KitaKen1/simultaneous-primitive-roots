module

public import SimultaneousPrimitiveRoots.Hecke.ConeIdeals
public import Mathlib.NumberTheory.NumberField.ClassNumber

/-!
# Partial zeta functions of ideal classes

Let `J` be a nonzero integral ideal in the class `c⁻¹`. Then `I' ↦ J I'` is a bijection from the
integral ideals in the class `c` onto the principal ideals divisible by `J`
(`classIdealEquiv`, the argument of Mathlib's private
`Ideal.tendsto_norm_le_and_mk_eq_div_atTop_aux₁`). With `tsum_coneSet_eq`,

`∑_{x ∈ J ∩ cone} g(|N x|) = w · ∑_{I' ∈ c} g(N J · N I')`.

We also identify the lattice of Mathlib's `basisOfFractionalIdeal` with `J`.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField NumberField.Units Ideal Submodule
open scoped nonZeroDivisors ENNReal

variable {K : Type*} [Field K] [NumberField K]

/-- `{I' ∈ c} ≃ {principal ideals divisible by J}` when `[J] = c⁻¹`. -/
def classIdealEquiv (J : (Ideal (𝓞 K))⁰) {c : ClassGroup (𝓞 K)}
    (hJ : ClassGroup.mk0 J = c⁻¹) :
    {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = c} ≃
      {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.val} // (J : Ideal (𝓞 K)) ∣ I.1.1} :=
  ((Equiv.dvd J).subtypeEquiv (q := fun I : {I : (Ideal (𝓞 K))⁰ // J ∣ I} =>
      IsPrincipal (I.1 : Ideal (𝓞 K))) fun I => by
    rw [← ClassGroup.mk0_eq_one_iff (SetLike.coe_mem _)]
    simp_rw [Equiv.dvd_apply, Submonoid.coe_mul, ← Submonoid.mul_def, _root_.map_mul, hJ,
      inv_mul_eq_one, eq_comm]).trans <|
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : (Ideal (𝓞 K))⁰ => J ∣ I)
      (fun I => IsPrincipal (I : Ideal (𝓞 K)))).trans <|
      (Equiv.subtypeEquivRight fun I => by
        rw [nonZeroDivisors_dvd_iff_dvd_coe, and_comm]).trans <|
        (Equiv.subtypeSubtypeEquivSubtypeInter (fun I : (Ideal (𝓞 K))⁰ =>
          IsPrincipal (I : Ideal (𝓞 K))) (fun I => (J : Ideal (𝓞 K)) ∣ I)).symm

theorem classIdealEquiv_apply (J : (Ideal (𝓞 K))⁰) {c : ClassGroup (𝓞 K)}
    (hJ : ClassGroup.mk0 J = c⁻¹) (I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = c}) :
    ((classIdealEquiv J hJ I).1.1 : (Ideal (𝓞 K))⁰) = J * I.1 := rfl

theorem absNorm_classIdealEquiv (J : (Ideal (𝓞 K))⁰) {c : ClassGroup (𝓞 K)}
    (hJ : ClassGroup.mk0 J = c⁻¹) (I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = c}) :
    absNorm ((classIdealEquiv J hJ I).1.1.1 : Ideal (𝓞 K)) =
      absNorm (J : Ideal (𝓞 K)) * absNorm (I.1 : Ideal (𝓞 K)) := by
  rw [classIdealEquiv_apply, Submonoid.coe_mul, _root_.map_mul]

/-- **Cone sums of `J` as sums over the class `c`.** -/
theorem tsum_coneSet_eq_class (J : (Ideal (𝓞 K))⁰) {c : ClassGroup (𝓞 K)}
    (hJ : ClassGroup.mk0 J = c⁻¹) (g : ℝ → ℝ≥0∞) :
    ∑' x : coneSet (idealInK (J : Ideal (𝓞 K))), g |((Algebra.norm ℚ (x : K) : ℚ) : ℝ)| =
      (torsionOrder K : ℝ≥0∞) * ∑' I : {I : (Ideal (𝓞 K))⁰ // ClassGroup.mk0 I = c},
        g ((absNorm (J : Ideal (𝓞 K)) : ℝ) * absNorm (I.1 : Ideal (𝓞 K))) := by
  rw [tsum_coneSet_eq, ← (classIdealEquiv J hJ).tsum_eq]
  congr 1
  apply tsum_congr
  intro I
  rw [absNorm_classIdealEquiv]
  push_cast
  rfl

/-- The `ℤ`-span of `basisOfFractionalIdeal` of `J` is `J`. -/
theorem latticeSet_basisOfFractionalIdeal (J : (Ideal (𝓞 K))⁰) :
    latticeSet (basisOfFractionalIdeal K (FractionalIdeal.mk0 K J) :
      Module.Free.ChooseBasisIndex ℤ (FractionalIdeal.mk0 K J) → K) =
      idealInK (J : Ideal (𝓞 K)) := by
  ext x
  have h1 : x ∈ latticeSet (basisOfFractionalIdeal K (FractionalIdeal.mk0 K J) :
      Module.Free.ChooseBasisIndex ℤ (FractionalIdeal.mk0 K J) → K) ↔
      x ∈ Submodule.span ℤ (Set.range (basisOfFractionalIdeal K (FractionalIdeal.mk0 K J))) := by
    rw [Submodule.mem_span_range_iff_exists_fun]
    rfl
  rw [h1, mem_span_basisOfFractionalIdeal]
  simp only [FractionalIdeal.coe_mk0, SetLike.mem_coe, FractionalIdeal.mem_coeIdeal]
  rfl

end SimultaneousPrimitiveRoots.Hecke

end
