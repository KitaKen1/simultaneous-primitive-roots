module

public import SimultaneousPrimitiveRoots.Hecke.ShiftedHecke
public import SimultaneousPrimitiveRoots.Hecke.DedekindHecke
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Integral
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

/-!
# The cone points of a ray class

Let `𝔪₀` be a nonzero ideal of `𝓞 K`, `𝔟` a nonzero ideal and

`S = raySet 𝔪₀ 𝔟 = {x ∈ 𝔟 : u x ≡ 1 (mod 𝔪₀) for some unit u}`.

* `S` is stable under units, and avoids `0` when `𝔪₀ ≠ 𝓞` (`raySet_unit_mul`,
  `zero_notMem_raySet`).
* Its cone points are, up to the `w` roots of unity, the generators of the principal ideals
  divisible by `𝔟` with a generator `≡ 1 (mod 𝔪₀)` (`coneRayEquiv`, `tsum_coneSet_raySet_eq`).
* For a modulus `𝔪` without infinite part, a ray class `C` and `𝔟` prime to `𝔪` in `C⁻¹`, those
  ideals are the `𝔟 𝔞` with `𝔞 ∈ C` (`rayClassDvdEquiv`), so

  `∑_{x ∈ S ∩ cone} g(|N x|) = w ∑_{𝔞 ∈ C} g(N𝔟 · N𝔞)`   (`tsum_coneSet_raySet_eq_class`).
* If `𝔟 + 𝔪₀ = 𝓞` and `ξ ∈ 𝔟`, `ξ ≡ 1 (mod 𝔪₀)`, then `S` is the disjoint union of the cosets
  `u ξ + 𝔟𝔪₀`, `u` running over representatives of the image of the units in `𝓞/𝔪₀`
  (`cosetSet_rayShift_eq`, `rayShift_injective`, `rayShift_notMem`).

With `sum_heckeShiftedFEPair_ofReal` this makes the partial zeta function of a ray class a finite
sum of Hecke's coset `Λ`s (step Z2 of `docs/unconditional-roadmap.md`).
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField NumberField.Units NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  Ideal Submodule Module
open TauCeti.GlobalNumberFields
open scoped nonZeroDivisors ENNReal

variable {K : Type*} [Field K] [NumberField K]

/-! ### The elements of `𝔟` congruent to a unit -/

/-- `S = {x ∈ 𝔟 : u x ≡ 1 (mod 𝔪₀) for some unit u}`. -/
def raySet (𝔪₀ 𝔟 : Ideal (𝓞 K)) : Set K :=
  {x | ∃ α : 𝓞 K, algebraMap (𝓞 K) K α = x ∧ α ∈ 𝔟 ∧ ∃ u : (𝓞 K)ˣ, (u : 𝓞 K) * α - 1 ∈ 𝔪₀}

/-- An ideal with a generator congruent to one modulo `𝔪₀`. -/
def HasGenOne (𝔪₀ I : Ideal (𝓞 K)) : Prop := ∃ β : 𝓞 K, I = span {β} ∧ β - 1 ∈ 𝔪₀

omit [NumberField K] in
/-- Membership in `idealInK`, without unfolding the ideal. -/
theorem mem_idealInK {J : Ideal (𝓞 K)} {x : K} :
    x ∈ idealInK J ↔ ∃ a ∈ J, algebraMap (𝓞 K) K a = x := Iff.rfl

omit [NumberField K] in
theorem raySet_subset (𝔪₀ 𝔟 : Ideal (𝓞 K)) : raySet 𝔪₀ 𝔟 ⊆ idealInK 𝔟 := by
  rintro x ⟨α, rfl, hα, -⟩
  exact ⟨α, hα, rfl⟩

omit [NumberField K] in
theorem raySet_unit_mul (𝔪₀ 𝔟 : Ideal (𝓞 K)) (v : (𝓞 K)ˣ) (x : K) (hx : x ∈ raySet 𝔪₀ 𝔟) :
    (v : K) * x ∈ raySet 𝔪₀ 𝔟 := by
  obtain ⟨α, rfl, hα, u, hu⟩ := hx
  refine ⟨(v : 𝓞 K) * α, by rw [map_mul], 𝔟.mul_mem_left _ hα, u * v⁻¹, ?_⟩
  have h : ((u * v⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * ((v : 𝓞 K) * α) = (u : 𝓞 K) * α := by
    rw [Units.val_mul, mul_assoc, ← mul_assoc ((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K), Units.inv_mul, one_mul]
  rw [h]
  exact hu

omit [NumberField K] in
theorem zero_notMem_raySet {𝔪₀ : Ideal (𝓞 K)} (h𝔪 : 𝔪₀ ≠ ⊤) (𝔟 : Ideal (𝓞 K)) :
    (0 : K) ∉ raySet 𝔪₀ 𝔟 := by
  rintro ⟨α, hα0, -, u, hu⟩
  have h : α = 0 := RingOfIntegers.coe_injective (hα0.trans (map_zero _).symm)
  rw [h, mul_zero, zero_sub, neg_mem_iff] at hu
  exact h𝔪 ((eq_top_iff_one _).mpr hu)

omit [NumberField K] in
theorem mem_raySet_iff {𝔪₀ 𝔟 : Ideal (𝓞 K)} {α : 𝓞 K} (hα : α ∈ 𝔟) :
    algebraMap (𝓞 K) K α ∈ raySet 𝔪₀ 𝔟 ↔ HasGenOne 𝔪₀ (span {α}) := by
  constructor
  · rintro ⟨α', hα', -, u, hu⟩
    have h : α' = α := RingOfIntegers.coe_injective hα'
    subst h
    exact ⟨(u : 𝓞 K) * α', (span_singleton_mul_left_unit u.isUnit α').symm, hu⟩
  · rintro ⟨β, hβ, hβ1⟩
    obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hβ
    refine ⟨α, rfl, hα, u, ?_⟩
    rw [mul_comm, hu]
    exact hβ1

/-! ### Cone points -/

/-- The principal ideal attached to a cone point of `J`, with its generator. -/
theorem exists_coneIdealEquiv_fst_eq_span (J : (Ideal (𝓞 K))⁰)
    (x : coneSet (idealInK (J : Ideal (𝓞 K)))) :
    ∃ α : 𝓞 K, algebraMap (𝓞 K) K α = (x : K) ∧
      ((coneIdealEquiv J x).1.1.1 : Ideal (𝓞 K)) = span {α} := by
  set a := (idealSetEquiv K J (Equiv.ofBijective _ (coneToIdealSet_bijective J) x)).1 with ha
  have h1 : ((coneIdealEquiv J x).1.1.1 : Ideal (𝓞 K)) =
      span {(preimageOfMemIntegerSet a : 𝓞 K)} := by
    rw [← integerSetEquiv_apply_fst]
    rfl
  have h2 : mixedEmbedding K ((preimageOfMemIntegerSet a : 𝓞 K) : K) =
      mixedEmbedding K (x : K) := by
    rw [mixedEmbedding_preimageOfMemIntegerSet]
    rfl
  exact ⟨_, mixedEmbedding_injective K h2, h1⟩

theorem mem_coneSet_raySet_iff {𝔪₀ : Ideal (𝓞 K)} {J : (Ideal (𝓞 K))⁰} (x : K) :
    x ∈ coneSet (raySet 𝔪₀ (J : Ideal (𝓞 K))) ↔
      x ∈ coneSet (idealInK (J : Ideal (𝓞 K))) ∧ x ∈ raySet 𝔪₀ (J : Ideal (𝓞 K)) := by
  simp only [mem_coneSet]
  constructor
  · rintro ⟨hx, h0, hc⟩
    exact ⟨⟨raySet_subset _ _ hx, h0, hc⟩, hx⟩
  · rintro ⟨⟨-, h0, hc⟩, hx⟩
    exact ⟨hx, h0, hc⟩

theorem mem_raySet_iff_hasGenOne {𝔪₀ : Ideal (𝓞 K)} (J : (Ideal (𝓞 K))⁰)
    (x : coneSet (idealInK (J : Ideal (𝓞 K)))) :
    (x : K) ∈ raySet 𝔪₀ (J : Ideal (𝓞 K)) ↔
      HasGenOne 𝔪₀ ((coneIdealEquiv J x).1.1.1 : Ideal (𝓞 K)) := by
  obtain ⟨α, hαx, hspan⟩ := exists_coneIdealEquiv_fst_eq_span J x
  have hαJ : α ∈ (J : Ideal (𝓞 K)) := by
    obtain ⟨a, ha, hax⟩ := x.2.1
    have h : a = α := RingOfIntegers.coe_injective (hax.trans hαx.symm)
    rw [← h]
    exact ha
  rw [hspan, ← hαx]
  exact mem_raySet_iff hαJ

/-- `S ∩ cone ≃ {principal multiples of J with a generator ≡ 1} × μ_K`. -/
def coneRayEquiv {𝔪₀ : Ideal (𝓞 K)} (J : (Ideal (𝓞 K))⁰) :
    coneSet (raySet 𝔪₀ (J : Ideal (𝓞 K))) ≃
      {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.val} //
        (J : Ideal (𝓞 K)) ∣ I.1.1 ∧ HasGenOne 𝔪₀ I.1.1} × torsion K :=
  ((Equiv.subtypeEquivRight (mem_coneSet_raySet_iff (𝔪₀ := 𝔪₀) (J := J))).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ coneSet (idealInK (J : Ideal (𝓞 K))))
      (· ∈ raySet 𝔪₀ (J : Ideal (𝓞 K)))).symm).trans <|
  ((coneIdealEquiv J).subtypeEquiv (mem_raySet_iff_hasGenOne J)).trans <|
  Equiv.prodSubtypeFstEquivSubtypeProd.trans <|
  Equiv.prodCongr (Equiv.subtypeSubtypeEquivSubtypeInter
    (fun I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.val} => (J : Ideal (𝓞 K)) ∣ I.1.1)
    (fun I => HasGenOne 𝔪₀ I.1.1)) (Equiv.refl _)

theorem coneRayEquiv_norm {𝔪₀ : Ideal (𝓞 K)} (J : (Ideal (𝓞 K))⁰)
    (x : coneSet (raySet 𝔪₀ (J : Ideal (𝓞 K)))) :
    (absNorm ((coneRayEquiv J x).1.1.1 : Ideal (𝓞 K)) : ℝ) =
      |((Algebra.norm ℚ (x : K) : ℚ) : ℝ)| :=
  coneIdealEquiv_norm J ⟨x, ((mem_coneSet_raySet_iff (x : K)).mp x.2).1⟩

/-- **Cone sums of the ray set as sums over principal ideals.** -/
theorem tsum_coneSet_raySet_eq {𝔪₀ : Ideal (𝓞 K)} (J : (Ideal (𝓞 K))⁰) (g : ℝ → ℝ≥0∞) :
    ∑' x : coneSet (raySet 𝔪₀ (J : Ideal (𝓞 K))), g |((Algebra.norm ℚ (x : K) : ℚ) : ℝ)| =
      (torsionOrder K : ℝ≥0∞) * ∑' I : {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.val} //
          (J : Ideal (𝓞 K)) ∣ I.1.1 ∧ HasGenOne 𝔪₀ I.1.1},
        g (absNorm (I.1.1 : Ideal (𝓞 K)) : ℝ) := by
  let := Fintype.ofFinite (torsion K)
  rw [← (coneRayEquiv J).symm.tsum_eq, ENNReal.tsum_prod', ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro I
  have hconst : ∀ ζ : torsion K,
      g |((Algebra.norm ℚ ((coneRayEquiv J).symm (I, ζ) : K) : ℚ) : ℝ)| =
        g (absNorm (I.1.1 : Ideal (𝓞 K)) : ℝ) := fun ζ => by
    rw [← coneRayEquiv_norm, Equiv.apply_symm_apply]
  simp_rw [hconst]
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, torsionOrder,
    Nat.card_eq_fintype_card]

/-! ### The ideals of a ray class -/

section RayClass

variable (𝔪 : Modulus K)

theorem idealClass_eq_one_iff_hasGenOne (hinf : 𝔪.infinitePart = ∅) (I : integralIdealsPrimeTo 𝔪) :
    idealClass 𝔪 I = 1 ↔ HasGenOne 𝔪.finitePart (I : Ideal (𝓞 K)) := by
  rw [idealClass_eq_one_iff_exists_generator, hinf]
  constructor
  · rintro ⟨α, hα1, -, hI⟩
    exact ⟨α, hI, hα1⟩
  · rintro ⟨α, hI, hα1⟩
    exact ⟨α, hα1, fun w hw => absurd hw (Finset.notMem_empty w), hI⟩

omit [NumberField K] in
theorem isPrincipal_of_hasGenOne {𝔪₀ I : Ideal (𝓞 K)} (h : HasGenOne 𝔪₀ I) : IsPrincipal I := by
  obtain ⟨β, hI, -⟩ := h
  exact ⟨⟨β, hI⟩⟩

theorem mem_integralIdealsPrimeTo_of_hasGenOne {I : Ideal (𝓞 K)} (hI0 : I ≠ ⊥)
    (h : HasGenOne 𝔪.finitePart I) : I ∈ integralIdealsPrimeTo 𝔪 := by
  obtain ⟨β, hIβ, hβ1⟩ := h
  refine Modulus.mem_integralIdealsPrimeTo.mpr
    (Modulus.isCoprimeTo_iff_sup_eq_top.mpr ⟨hI0, (eq_top_iff_one _).mpr ?_⟩)
  have hβ : β ∈ I := hIβ ▸ Ideal.mem_span_singleton_self β
  have := Submodule.sub_mem _ (Ideal.mem_sup_left hβ : β ∈ I ⊔ 𝔪.finitePart)
    (Ideal.mem_sup_right hβ1 : β - 1 ∈ I ⊔ 𝔪.finitePart)
  simpa using this

theorem coe_ne_bot_of_mem (I : integralIdealsPrimeTo 𝔪) : (I : Ideal (𝓞 K)) ≠ ⊥ :=
  (TauCeti.NumberFieldArithmetic.mem_integralIdealsAway_iff.mp I.prop).1

/-- The multiples of `𝔟` of trivial ray class, as principal ideals with a generator `≡ 1`. -/
def dvdClassOneEquiv (hinf : 𝔪.infinitePart = ∅) (𝔟 : integralIdealsPrimeTo 𝔪) :
    {I : integralIdealsPrimeTo 𝔪 // 𝔟 ∣ I ∧ idealClass 𝔪 I = 1} ≃
      {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.val} //
        (𝔟 : Ideal (𝓞 K)) ∣ I.1.1 ∧ HasGenOne 𝔪.finitePart I.1.1} where
  toFun I := ⟨⟨⟨(I.1 : Ideal (𝓞 K)), mem_nonZeroDivisors_of_ne_zero (coe_ne_bot_of_mem 𝔪 I.1)⟩,
      isPrincipal_of_hasGenOne ((idealClass_eq_one_iff_hasGenOne 𝔪 hinf I.1).mp I.2.2)⟩,
    TauCeti.NumberFieldArithmetic.integralIdealsAway_dvd_iff_dvd_coe.mp I.2.1,
    (idealClass_eq_one_iff_hasGenOne 𝔪 hinf I.1).mp I.2.2⟩
  invFun I := ⟨⟨I.1.1.1, mem_integralIdealsPrimeTo_of_hasGenOne 𝔪
      (nonZeroDivisors.coe_ne_zero I.1.1) I.2.2⟩,
    TauCeti.NumberFieldArithmetic.integralIdealsAway_dvd_iff_dvd_coe.mpr I.2.1,
    (idealClass_eq_one_iff_hasGenOne 𝔪 hinf _).mpr I.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The ideals of a ray class `C` and the principal multiples of `𝔟 ∈ C⁻¹`**: `𝔞 ↦ 𝔟 𝔞`. -/
def rayClassDvdEquiv (hinf : 𝔪.infinitePart = ∅) {c : RayClassGroup 𝔪}
    (𝔟 : integralIdealsPrimeTo 𝔪) (h𝔟 : idealClass 𝔪 𝔟 = c⁻¹) :
    {𝔞 : integralIdealsPrimeTo 𝔪 // idealClass 𝔪 𝔞 = c} ≃
      {I : {I : (Ideal (𝓞 K))⁰ // IsPrincipal I.val} //
        (𝔟 : Ideal (𝓞 K)) ∣ I.1.1 ∧ HasGenOne 𝔪.finitePart I.1.1} :=
  (((Equiv.dvd 𝔟).subtypeEquiv
      (q := fun I : {I : integralIdealsPrimeTo 𝔪 // 𝔟 ∣ I} => idealClass 𝔪 I.1 = 1)
      fun 𝔞 => by
        simp only [Equiv.dvd_apply, map_mul, h𝔟]
        exact (inv_mul_eq_one.trans eq_comm).symm).trans
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun I => 𝔟 ∣ I)
      (fun I => idealClass 𝔪 I = 1))).trans (dvdClassOneEquiv 𝔪 hinf 𝔟)

theorem rayClassDvdEquiv_apply (hinf : 𝔪.infinitePart = ∅) {c : RayClassGroup 𝔪}
    (𝔟 : integralIdealsPrimeTo 𝔪) (h𝔟 : idealClass 𝔪 𝔟 = c⁻¹)
    (𝔞 : {𝔞 : integralIdealsPrimeTo 𝔪 // idealClass 𝔪 𝔞 = c}) :
    ((rayClassDvdEquiv 𝔪 hinf 𝔟 h𝔟 𝔞).1.1 : Ideal (𝓞 K)) =
      (𝔟 : Ideal (𝓞 K)) * (𝔞.1 : Ideal (𝓞 K)) := rfl

/-- **Cone sums of the ray set as sums over the ray class.** -/
theorem tsum_coneSet_raySet_eq_class (hinf : 𝔪.infinitePart = ∅) {c : RayClassGroup 𝔪}
    (𝔟 : integralIdealsPrimeTo 𝔪) (h𝔟 : idealClass 𝔪 𝔟 = c⁻¹) (g : ℝ → ℝ≥0∞) :
    ∑' x : coneSet (raySet 𝔪.finitePart (𝔟 : Ideal (𝓞 K))),
        g |((Algebra.norm ℚ (x : K) : ℚ) : ℝ)| =
      (torsionOrder K : ℝ≥0∞) * ∑' 𝔞 : {𝔞 : integralIdealsPrimeTo 𝔪 // idealClass 𝔪 𝔞 = c},
        g ((absNorm (𝔟 : Ideal (𝓞 K)) : ℝ) * absNorm (𝔞.1 : Ideal (𝓞 K))) := by
  set J : (Ideal (𝓞 K))⁰ := ⟨(𝔟 : Ideal (𝓞 K)),
    mem_nonZeroDivisors_of_ne_zero (coe_ne_bot_of_mem 𝔪 𝔟)⟩
  refine (tsum_coneSet_raySet_eq (𝔪₀ := 𝔪.finitePart) J g).trans ?_
  rw [← (rayClassDvdEquiv 𝔪 hinf 𝔟 h𝔟).tsum_eq]
  congr 1
  apply tsum_congr
  intro 𝔞
  rw [rayClassDvdEquiv_apply, map_mul]
  push_cast
  rfl

end RayClass

/-! ### The ray set as a union of cosets -/

section Cosets

variable (𝔪₀ : Ideal (𝓞 K))

/-- The image of the units in `𝓞/𝔪₀`. -/
def unitResidues : Set (𝓞 K ⧸ 𝔪₀) :=
  Set.range fun u : (𝓞 K)ˣ => Ideal.Quotient.mk 𝔪₀ (u : 𝓞 K)

/-- A unit representing a residue in `unitResidues`. -/
def unitRep (ρ : unitResidues 𝔪₀) : (𝓞 K)ˣ := ρ.2.choose

omit [NumberField K] in
theorem mk_unitRep (ρ : unitResidues 𝔪₀) :
    Ideal.Quotient.mk 𝔪₀ (unitRep 𝔪₀ ρ : 𝓞 K) = ρ := ρ.2.choose_spec

theorem finite_unitResidues (h0 : 𝔪₀ ≠ ⊥) : Finite (unitResidues 𝔪₀) := by
  have : Finite (𝓞 K ⧸ 𝔪₀) := Ideal.finiteQuotientOfFreeOfNeBot 𝔪₀ h0
  infer_instance

/-- The coset shift `u_ρ ξ`. -/
def rayShift (ξ : 𝓞 K) (ρ : unitResidues 𝔪₀) : K :=
  algebraMap (𝓞 K) K ((unitRep 𝔪₀ ρ : 𝓞 K) * ξ)

variable {𝔪₀}

omit [NumberField K] in
theorem latticePt_sub {ι : Type*} [Fintype ι] (b : ι → K) (m m' : ι → ℤ) :
    latticePt b m - latticePt b m' = latticePt b (m - m') := by
  unfold latticePt
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Pi.sub_apply, sub_smul]

variable {𝔟 : Ideal (𝓞 K)} {ι : Type*} [Fintype ι] {b : Module.Basis ι ℚ K}

theorem rayShift_notMem (h𝔪 : 𝔪₀ ≠ ⊤) (hb : latticeSet (b : ι → K) = idealInK (𝔟 * 𝔪₀))
    {ξ : 𝓞 K} (hξ1 : ξ - 1 ∈ 𝔪₀) (ρ : unitResidues 𝔪₀) :
    rayShift 𝔪₀ ξ ρ ∉ latticeSet (b : ι → K) := by
  rw [hb]
  intro hmem
  obtain ⟨a, ha, hax⟩ := mem_idealInK.mp hmem
  have h1 : a = (unitRep 𝔪₀ ρ : 𝓞 K) * ξ := RingOfIntegers.coe_injective hax
  have h2 : (unitRep 𝔪₀ ρ : 𝓞 K) * ξ ∈ 𝔪₀ := by
    rw [← h1]
    exact (Ideal.mul_le_right : 𝔟 * 𝔪₀ ≤ 𝔪₀) ha
  have h3 : ξ ∈ 𝔪₀ := by
    have := 𝔪₀.mul_mem_left ((unitRep 𝔪₀ ρ)⁻¹ : (𝓞 K)ˣ) h2
    rwa [← mul_assoc, Units.inv_mul, one_mul] at this
  apply h𝔪
  rw [eq_top_iff_one]
  have := 𝔪₀.sub_mem h3 hξ1
  simpa using this

theorem rayShift_injective (hb : latticeSet (b : ι → K) = idealInK (𝔟 * 𝔪₀))
    {ξ : 𝓞 K} (hξ1 : ξ - 1 ∈ 𝔪₀) :
    Function.Injective fun z : unitResidues 𝔪₀ × (ι → ℤ) =>
      latticePt (b : ι → K) z.2 + rayShift 𝔪₀ ξ z.1 := by
  rintro ⟨ρ, m⟩ ⟨ρ', m'⟩ h
  simp only at h
  -- the difference of the shifts lies in the lattice `𝔟 𝔪₀`
  have hd : rayShift 𝔪₀ ξ ρ - rayShift 𝔪₀ ξ ρ' ∈ latticeSet (b : ι → K) :=
    ⟨m' - m, by rw [← latticePt_sub]; linear_combination -h⟩
  rw [hb] at hd
  obtain ⟨a, ha, hax⟩ := mem_idealInK.mp hd
  set u := (unitRep 𝔪₀ ρ : 𝓞 K)
  set u' := (unitRep 𝔪₀ ρ' : 𝓞 K)
  have h1 : a = (u - u') * ξ := by
    apply RingOfIntegers.coe_injective
    rw [hax]
    simp only [rayShift, map_mul, map_sub]
    ring
  have h2 : (u - u') * ξ ∈ 𝔪₀ := by
    rw [← h1]
    exact (Ideal.mul_le_right : 𝔟 * 𝔪₀ ≤ 𝔪₀) ha
  have h3 : u - u' ∈ 𝔪₀ := by
    have := 𝔪₀.sub_mem h2 (𝔪₀.mul_mem_left (u - u') hξ1)
    have e : (u - u') * ξ - (u - u') * (ξ - 1) = u - u' := by ring
    rwa [e] at this
  have hρ : ρ = ρ' := by
    apply Subtype.ext
    rw [← mk_unitRep 𝔪₀ ρ, ← mk_unitRep 𝔪₀ ρ']
    exact Ideal.Quotient.eq.mpr h3
  subst hρ
  have hm : latticePt (b : ι → K) m = latticePt b m' := by simpa using h
  rw [latticePt_injective b hm]

theorem cosetSet_rayShift_eq (h𝔟 : 𝔟 ⊔ 𝔪₀ = ⊤)
    (hb : latticeSet (b : ι → K) = idealInK (𝔟 * 𝔪₀)) {ξ : 𝓞 K} (hξ𝔟 : ξ ∈ 𝔟)
    (hξ1 : ξ - 1 ∈ 𝔪₀) :
    cosetSet (b : ι → K) (rayShift 𝔪₀ ξ) = raySet 𝔪₀ 𝔟 := by
  ext x
  constructor
  · rintro ⟨⟨ρ, m⟩, rfl⟩
    have hm : latticePt (b : ι → K) m ∈ idealInK (𝔟 * 𝔪₀) := by
      rw [← hb]
      exact ⟨m, rfl⟩
    obtain ⟨a, ha, hax⟩ := mem_idealInK.mp hm
    set u := unitRep 𝔪₀ ρ
    refine ⟨a + (u : 𝓞 K) * ξ, ?_, 𝔟.add_mem ((Ideal.mul_le_left : 𝔟 * 𝔪₀ ≤ 𝔟) ha) (𝔟.mul_mem_left _ hξ𝔟), u⁻¹, ?_⟩
    · simp only [map_add, hax, rayShift]
      rfl
    · have e : ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (a + (u : 𝓞 K) * ξ) - 1 =
          ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * a + (ξ - 1) := by
        rw [mul_add, ← mul_assoc, Units.inv_mul, one_mul]
        ring
      rw [e]
      exact 𝔪₀.add_mem (𝔪₀.mul_mem_left _ ((Ideal.mul_le_right : 𝔟 * 𝔪₀ ≤ 𝔪₀) ha)) hξ1
  · rintro ⟨α, rfl, hα, v, hv⟩
    set ρ : unitResidues 𝔪₀ := ⟨Ideal.Quotient.mk 𝔪₀ ((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K), v⁻¹, rfl⟩
    set u := (unitRep 𝔪₀ ρ : 𝓞 K)
    have hu : u - ((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K) ∈ 𝔪₀ := Ideal.Quotient.eq.mp (mk_unitRep 𝔪₀ ρ)
    -- `α - u ξ ∈ 𝔟 ∩ 𝔪₀ = 𝔟 𝔪₀`
    have h1 : α - u * ξ ∈ 𝔪₀ := by
      have e : α - u * ξ = ((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * ((v : 𝓞 K) * α - 1) -
          (u - ((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) - u * (ξ - 1) := by
        have hvv : ((v⁻¹ : (𝓞 K)ˣ) : 𝓞 K) * (v : 𝓞 K) = 1 := Units.inv_mul v
        linear_combination (-α) * hvv
      rw [e]
      exact 𝔪₀.sub_mem (𝔪₀.sub_mem (𝔪₀.mul_mem_left _ hv) hu) (𝔪₀.mul_mem_left _ hξ1)
    have h2 : α - u * ξ ∈ 𝔟 := 𝔟.sub_mem hα (𝔟.mul_mem_left _ hξ𝔟)
    have h3 : α - u * ξ ∈ 𝔟 * 𝔪₀ := by
      rw [mul_eq_inf_of_coprime h𝔟]
      exact ⟨h2, h1⟩
    have h4 : algebraMap (𝓞 K) K (α - u * ξ) ∈ latticeSet (b : ι → K) := by
      rw [hb]
      exact mem_idealInK.mpr ⟨_, h3, rfl⟩
    obtain ⟨m, hm⟩ := h4
    refine ⟨⟨ρ, m⟩, ?_⟩
    simp only [hm, rayShift, map_sub, map_mul]
    ring

end Cosets

end SimultaneousPrimitiveRoots.Hecke

end
