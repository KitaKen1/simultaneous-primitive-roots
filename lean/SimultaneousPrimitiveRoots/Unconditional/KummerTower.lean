module

public import SimultaneousPrimitiveRoots.PrimeKummerSplitting
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
public import Mathlib.FieldTheory.Galois.Abelian

/-!
# The Kummer tower `K̃ = ℚ(ζ_M, a^{1/q})`, `M = lcm(12, q)`

[A]'s proof of `spl:field-bounds` (the input `KummerZetaZeroFree a q δ` of `KummerZeroFree.lean`)
factors `ζ_{K̃}` over two subfields of one top field `K̃`:

* `F = ℚ(ζ_M)`, a cyclotomic field containing `μ₁₂`, with `K̃ / F` abelian (Hecke ascent,
  `HeckeAscent.lean`);
* `K_q = PrimeKummerField a q = ℚ(ζ_q, a^{1/q})`, with `K̃ = K_q(ζ_M)` (cyclotomic descent,
  `CyclotomicDescent.lean`).

This file builds `K̃` and both towers.

* `kummerLevel q = lcm(12, q)`: `12 ∣ M`, `q ∣ M`, and `M ≠ 0` for `q ≠ 0`.
* `KummerTop a q`: the splitting field of `(X^M - 1)(X^q - a)` over `ℚ`, a Galois number field.
* `Algebra (CyclotomicField (kummerLevel q) ℚ) (KummerTop a q)`: the lift of the splitting field of
  `Φ_M ∣ X^M - 1` (`kummerTopCyclotomicHom`).
* `Algebra (PrimeKummerField a q) (KummerTop a q)`: `ℚ(ζ_q) → K̃` (`q ∣ M`), extended to
  `K_q = ℚ(ζ_q)[X]/(X^q - a)` by sending the root to a root of `X^q - a` in `K̃`
  (`kummerTopFieldHom`).
* Both extensions are finite, Galois and abelian:
  - over `F`: the `M`-th roots of unity of `K̃` lie in `F`, and `σ(α)/α` is a `q`-th root of unity
    for a root `α` of `X^q - a`, so two `F`-automorphisms commute on the generators of `K̃ / ℚ`;
  - over `K_q`: the roots of `X^q - a` in `K̃` lie in `K_q`, so `K̃ / K_q` is the `M`-th cyclotomic
    extension (`kummerTop_isCyclotomicExtension`), abelian by Mathlib.
* `K_q`, `F` and `K̃` are totally complex.

On instances: instance search finds `DivisionRing.toRatAlgebra` as the `ℚ`-algebra structure of
`KummerTop a q`, `CyclotomicField n ℚ` and `PrimeKummerField a q`. The towers
`IsScalarTower ℚ F K̃` and `IsScalarTower ℚ K_q K̃` hold for any `ℚ`-module structures
(`IsScalarTower.rat`). Mathlib's `IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ)` is stated for
`CyclotomicField.algebra n ℚ` and is found only under `backward.isDefEq.respectTransparency false`;
`kummerCyclotomic_isCyclotomicExtension` restates it for `n = kummerLevel q`.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace SimultaneousPrimitiveRoots.Unconditional

open Polynomial NumberField

/-! ### The level `M = lcm(12, q)` -/

/-- The cyclotomic level of the Kummer tower, `M = lcm(12, q)`. -/
def kummerLevel (q : ℕ) : ℕ := Nat.lcm 12 q

theorem twelve_dvd_kummerLevel (q : ℕ) : 12 ∣ kummerLevel q := Nat.dvd_lcm_left 12 q

theorem dvd_kummerLevel (q : ℕ) : q ∣ kummerLevel q := Nat.dvd_lcm_right 12 q

theorem kummerLevel_ne_zero (q : ℕ) [NeZero q] : kummerLevel q ≠ 0 :=
  Nat.lcm_ne_zero (by norm_num) (NeZero.ne q)

/-- `M ≠ 0`; with `[Fact q.Prime]`, `NeZero q` is found by `NeZero.of_gt'`. -/
instance kummerLevel_neZero (q : ℕ) [NeZero q] : NeZero (kummerLevel q) :=
  ⟨kummerLevel_ne_zero q⟩

theorem two_lt_kummerLevel (q : ℕ) [NeZero q] : 2 < kummerLevel q :=
  lt_of_lt_of_le (by norm_num)
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (kummerLevel_ne_zero q)) (twelve_dvd_kummerLevel q))

/-- `ℚ(ζ_M)` is the `M`-th cyclotomic extension of `ℚ`, for the `ℚ`-algebra structure that
instance search finds on it (`DivisionRing.toRatAlgebra`). Mathlib's instance is stated for
`CyclotomicField.algebra`; the two agree only after unfolding, so without
`backward.isDefEq.respectTransparency false` Mathlib's instance is not found here. -/
instance kummerCyclotomic_isCyclotomicExtension (q : ℕ) :
    IsCyclotomicExtension {kummerLevel q} ℚ (CyclotomicField (kummerLevel q) ℚ) :=
  inferInstance

/-! ### The top field -/

/-- The top field `K̃ = ℚ(ζ_M, a^{1/q})`, `M = lcm(12, q)`: the splitting field of
`(X^M - 1)(X^q - a)` over `ℚ`. Its `Field` and `CharZero` instances are those of
`Polynomial.SplittingField`. -/
abbrev KummerTop (a q : ℕ) : Type :=
  SplittingField (((X : ℚ[X]) ^ kummerLevel q - 1) * (X ^ q - C (a : ℚ)))

/-- `K̃` is a number field. -/
instance kummerTop_numberField (a q : ℕ) : NumberField (KummerTop a q) :=
  NumberField.of_module_finite ℚ _

/-- `K̃ / ℚ` is Galois: a splitting field (normal) in characteristic zero (separable). -/
instance kummerTop_isGalois (a q : ℕ) : IsGalois ℚ (KummerTop a q) := IsGalois.mk

/-- `K̃` is generated over `ℚ` by the roots of `(X^M - 1)(X^q - a)`. -/
theorem kummerTop_adjoin_rootSet (a q : ℕ) :
    Algebra.adjoin ℚ ((((X : ℚ[X]) ^ kummerLevel q - 1) * (X ^ q - C (a : ℚ))).rootSet
      (KummerTop a q)) = ⊤ :=
  SplittingField.adjoin_rootSet _

theorem kummerTop_mem_adjoin_rootSet (a q : ℕ) (x : KummerTop a q) :
    x ∈ Algebra.adjoin ℚ ((((X : ℚ[X]) ^ kummerLevel q - 1) * (X ^ q - C (a : ℚ))).rootSet
      (KummerTop a q)) := by
  rw [kummerTop_adjoin_rootSet]
  exact Algebra.mem_top

/-- The generators of `K̃` over `ℚ` are `M`-th roots of unity or `q`-th roots of `a`. -/
theorem kummerTop_root_cases (a q : ℕ) {x : KummerTop a q}
    (hx : x ∈ (((X : ℚ[X]) ^ kummerLevel q - 1) * (X ^ q - C (a : ℚ))).rootSet
      (KummerTop a q)) :
    x ^ kummerLevel q = 1 ∨ x ^ q = a := by
  have h := aeval_eq_zero_of_mem_rootSet hx
  simpa [sub_eq_zero] using h

/-! ### The cyclotomic subfield `F = ℚ(ζ_M)` -/

section Cyclotomic

variable (a q : ℕ) [NeZero q]

theorem kummerTopPolynomial_ne_zero :
    ((X : ℚ[X]) ^ kummerLevel q - 1) * (X ^ q - C (a : ℚ)) ≠ 0 := by
  refine mul_ne_zero ?_ (X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero (NeZero.ne q)) _)
  simpa using X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero (kummerLevel_ne_zero q)) (1 : ℚ)

theorem kummerTop_splits_X_pow_sub_one :
    Splits (((X : ℚ[X]) ^ kummerLevel q - 1).map (algebraMap ℚ (KummerTop a q))) :=
  (SplittingField.splits _).of_dvd (map_ne_zero (kummerTopPolynomial_ne_zero a q))
    (Polynomial.map_dvd _ (dvd_mul_right _ _))

theorem kummerTop_splits_X_pow_sub_C :
    Splits (((X : ℚ[X]) ^ q - C (a : ℚ)).map (algebraMap ℚ (KummerTop a q))) :=
  (SplittingField.splits _).of_dvd (map_ne_zero (kummerTopPolynomial_ne_zero a q))
    (Polynomial.map_dvd _ (dvd_mul_left _ _))

theorem kummerTop_splits_cyclotomic {n : ℕ} (hn : n ∣ kummerLevel q) :
    Splits ((cyclotomic n ℚ).map (algebraMap ℚ (KummerTop a q))) := by
  have h0 : ((X : ℚ[X]) ^ kummerLevel q - 1) ≠ 0 := by
    simpa using X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero (kummerLevel_ne_zero q)) (1 : ℚ)
  obtain ⟨k, hk⟩ := hn
  have hdvd : cyclotomic n ℚ ∣ (X : ℚ[X]) ^ kummerLevel q - 1 :=
    hk ▸ (cyclotomic.dvd_X_pow_sub_one n ℚ).trans (pow_one_sub_dvd_pow_mul_sub_one X n k)
  exact (kummerTop_splits_X_pow_sub_one a q).of_dvd (map_ne_zero h0) (Polynomial.map_dvd _ hdvd)

/-- The embedding `ℚ(ζ_M) → K̃`, the lift of the splitting field of `Φ_M`. -/
def kummerTopCyclotomicHom : CyclotomicField (kummerLevel q) ℚ →+* KummerTop a q :=
  haveI := IsCyclotomicExtension.splitting_field_cyclotomic (kummerLevel q) ℚ
    (CyclotomicField (kummerLevel q) ℚ)
  (IsSplittingField.lift (CyclotomicField (kummerLevel q) ℚ) (cyclotomic (kummerLevel q) ℚ)
    (kummerTop_splits_cyclotomic a q dvd_rfl)).toRingHom

/-- `K̃` as an algebra over `F = ℚ(ζ_M)`. -/
instance kummerTop_algebraCyclotomic :
    Algebra (CyclotomicField (kummerLevel q) ℚ) (KummerTop a q) :=
  (kummerTopCyclotomicHom a q).toAlgebra

theorem kummerTop_algebraMap_cyclotomic :
    algebraMap (CyclotomicField (kummerLevel q) ℚ) (KummerTop a q) =
      kummerTopCyclotomicHom a q :=
  rfl

/-- The tower `ℚ ⊆ F ⊆ K̃` (any two `ℚ`-module structures are compatible). -/
instance kummerTop_isScalarTower_cyclotomic :
    IsScalarTower ℚ (CyclotomicField (kummerLevel q) ℚ) (KummerTop a q) :=
  IsScalarTower.rat

instance kummerTop_isGalois_cyclotomic :
    IsGalois (CyclotomicField (kummerLevel q) ℚ) (KummerTop a q) :=
  IsGalois.tower_top_of_isGalois ℚ _ _

instance kummerTop_finiteDimensional_cyclotomic :
    FiniteDimensional (CyclotomicField (kummerLevel q) ℚ) (KummerTop a q) :=
  FiniteDimensional.right ℚ _ _

/-- The image of `ζ_M` is a primitive `M`-th root of unity in `K̃`. -/
theorem kummerTop_zeta_spec :
    IsPrimitiveRoot (algebraMap (CyclotomicField (kummerLevel q) ℚ) (KummerTop a q)
      (IsCyclotomicExtension.zeta (kummerLevel q) ℚ (CyclotomicField (kummerLevel q) ℚ)))
      (kummerLevel q) :=
  (IsCyclotomicExtension.zeta_spec _ _ _).map_of_injective
    (algebraMap (CyclotomicField (kummerLevel q) ℚ) (KummerTop a q)).injective

/-- Every `M`-th root of unity of `K̃` lies in `F = ℚ(ζ_M)`. -/
theorem kummerTop_exists_cyclotomic_eq {x : KummerTop a q} (hx : x ^ kummerLevel q = 1) :
    ∃ y : CyclotomicField (kummerLevel q) ℚ,
      algebraMap (CyclotomicField (kummerLevel q) ℚ) (KummerTop a q) y = x := by
  obtain ⟨i, -, hi⟩ := (kummerTop_zeta_spec a q).eq_pow_of_pow_eq_one hx
  exact ⟨_ ^ i, by rw [map_pow, hi]⟩

/-- An `F`-automorphism moves a `q`-th root of `a` by a root of unity in `F`. -/
theorem kummerTop_cyclotomicAut_radical
    (σ : KummerTop a q ≃ₐ[CyclotomicField (kummerLevel q) ℚ] KummerTop a q)
    {x : KummerTop a q} (hx : x ^ q = a) :
    ∃ y : CyclotomicField (kummerLevel q) ℚ,
      σ x = algebraMap (CyclotomicField (kummerLevel q) ℚ) (KummerTop a q) y * x := by
  by_cases hx0 : x = 0
  · exact ⟨0, by simp [hx0]⟩
  have ha : (a : KummerTop a q) ≠ 0 := hx ▸ pow_ne_zero _ hx0
  have hσa : σ (a : KummerTop a q) = a := map_natCast σ a
  have hu : (σ x / x) ^ kummerLevel q = 1 := by
    obtain ⟨k, hk⟩ := dvd_kummerLevel q
    have h : (σ x / x) ^ (q * k) = 1 := by
      rw [pow_mul, div_pow, ← map_pow, hx, hσa, div_self ha, one_pow]
    rwa [← hk] at h
  obtain ⟨y, hy⟩ := kummerTop_exists_cyclotomic_eq a q hu
  exact ⟨y, by rw [hy, div_mul_cancel₀ _ hx0]⟩

/-- **`K̃ / ℚ(ζ_M)` is abelian.** Two `F`-automorphisms agree on the generators of `K̃ / ℚ`:
they fix the `M`-th roots of unity (which lie in `F`) and multiply a root of `X^q - a` by roots
of unity in `F`. -/
instance kummerTop_isMulCommutative_cyclotomic :
    IsMulCommutative (KummerTop a q ≃ₐ[CyclotomicField (kummerLevel q) ℚ] KummerTop a q) := by
  refine IsMulCommutative.of_comm fun σ τ => AlgEquiv.ext fun x => ?_
  have hx := kummerTop_mem_adjoin_rootSet a q x
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rcases kummerTop_root_cases a q hy with hy | hy
    · obtain ⟨z, rfl⟩ := kummerTop_exists_cyclotomic_eq a q hy
      simp only [AlgEquiv.commutes]
    · obtain ⟨u, hu⟩ := kummerTop_cyclotomicAut_radical a q σ hy
      obtain ⟨v, hv⟩ := kummerTop_cyclotomicAut_radical a q τ hy
      simp only [AlgEquiv.mul_apply, hu, hv, map_mul, AlgEquiv.commutes]
      ring
  | algebraMap r =>
    simp only [AlgEquiv.mul_apply]
    rw [IsScalarTower.algebraMap_apply ℚ (CyclotomicField (kummerLevel q) ℚ) (KummerTop a q),
      AlgEquiv.commutes, AlgEquiv.commutes, AlgEquiv.commutes]
  | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
  | mul y z _ _ hy hz => rw [map_mul, map_mul, hy, hz]

instance kummerTop_isAbelianGalois_cyclotomic :
    IsAbelianGalois (CyclotomicField (kummerLevel q) ℚ) (KummerTop a q) where

/-- `ℚ(ζ_M)` is totally complex (`M ≥ 12 > 2`). -/
instance kummerCyclotomic_isTotallyComplex :
    IsTotallyComplex (CyclotomicField (kummerLevel q) ℚ) :=
  IsCyclotomicExtension.Rat.isTotallyComplex (n := kummerLevel q) _ (two_lt_kummerLevel q)

/-- `K̃ ⊇ ℚ(ζ_M)` is totally complex. -/
instance kummerTop_isTotallyComplex : IsTotallyComplex (KummerTop a q) :=
  isTotallyComplex_of_algebra (CyclotomicField (kummerLevel q) ℚ) _

/-- The embedding `ℚ(ζ_q) → K̃` (`q ∣ M`). -/
def kummerTopBaseHom : CyclotomicField q ℚ →+* KummerTop a q :=
  haveI := IsCyclotomicExtension.splitting_field_cyclotomic q ℚ (CyclotomicField q ℚ)
  (IsSplittingField.lift (CyclotomicField q ℚ) (cyclotomic q ℚ)
    (kummerTop_splits_cyclotomic a q (dvd_kummerLevel q))).toRingHom

/-- A `q`-th root of `a` in `K̃`. -/
def kummerTopRadical : KummerTop a q :=
  rootOfSplits (kummerTop_splits_X_pow_sub_C a q) (by
    rw [degree_map, degree_X_pow_sub_C (Nat.pos_of_ne_zero (NeZero.ne q))]
    exact_mod_cast NeZero.ne q)

theorem kummerTopRadical_pow : kummerTopRadical a q ^ q = a := by
  have h : eval (kummerTopRadical a q)
      (((X : ℚ[X]) ^ q - C (a : ℚ)).map (algebraMap ℚ (KummerTop a q))) = 0 :=
    eval_rootOfSplits _ _
  simpa [sub_eq_zero] using h

end Cyclotomic

/-! ### The Kummer subfield `K_q = ℚ(ζ_q, a^{1/q})` -/

section Kummer

variable (a q : ℕ) [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)]

/-- The embedding `K_q = ℚ(ζ_q)[X]/(X^q - a) → K̃`: `kummerTopBaseHom` on `ℚ(ζ_q)`, and the root
goes to `kummerTopRadical`. -/
def kummerTopFieldHom : PrimeKummerField a q →+* KummerTop a q :=
  AdjoinRoot.lift (kummerTopBaseHom a q) (kummerTopRadical a q) (by
    simp [primeRadicalPolynomial, kummerTopRadical_pow])

/-- `K̃` as an algebra over `K_q = PrimeKummerField a q`. -/
instance kummerTop_algebraKummer : Algebra (PrimeKummerField a q) (KummerTop a q) :=
  (kummerTopFieldHom a q).toAlgebra

theorem kummerTop_algebraMap_kummer :
    algebraMap (PrimeKummerField a q) (KummerTop a q) = kummerTopFieldHom a q :=
  rfl

theorem kummerTop_algebraMap_root :
    algebraMap (PrimeKummerField a q) (KummerTop a q)
      (AdjoinRoot.root (primeRadicalPolynomial a q)) = kummerTopRadical a q := by
  rw [kummerTop_algebraMap_kummer, kummerTopFieldHom, AdjoinRoot.lift_root]

theorem kummerTop_algebraMap_of (z : CyclotomicField q ℚ) :
    algebraMap (PrimeKummerField a q) (KummerTop a q)
      (AdjoinRoot.of (primeRadicalPolynomial a q) z) = kummerTopBaseHom a q z := by
  rw [kummerTop_algebraMap_kummer, kummerTopFieldHom, AdjoinRoot.lift_of]

/-- The tower `ℚ ⊆ K_q ⊆ K̃` (any two `ℚ`-module structures are compatible). -/
instance kummerTop_isScalarTower_kummer :
    IsScalarTower ℚ (PrimeKummerField a q) (KummerTop a q) :=
  IsScalarTower.rat

instance kummerTop_isGalois_kummer : IsGalois (PrimeKummerField a q) (KummerTop a q) :=
  IsGalois.tower_top_of_isGalois ℚ _ _

instance kummerTop_finiteDimensional_kummer :
    FiniteDimensional (PrimeKummerField a q) (KummerTop a q) :=
  FiniteDimensional.right ℚ _ _

/-- The image of `ζ_q ∈ K_q` is a primitive `q`-th root of unity in `K̃`. -/
theorem kummerTop_zetaPrime_spec :
    IsPrimitiveRoot (algebraMap (PrimeKummerField a q) (KummerTop a q)
      (AdjoinRoot.of (primeRadicalPolynomial a q)
        (IsCyclotomicExtension.zeta q ℚ (CyclotomicField q ℚ)))) q :=
  ((IsCyclotomicExtension.zeta_spec q ℚ (CyclotomicField q ℚ)).map_of_injective
    (AdjoinRoot.of (primeRadicalPolynomial a q)).injective).map_of_injective
    (algebraMap (PrimeKummerField a q) (KummerTop a q)).injective

/-- Every `q`-th root of `a` in `K̃` lies in `K_q`: it is `ζ_q^i` times the image of the root. -/
theorem kummerTop_exists_kummer_eq {x : KummerTop a q} (hx : x ^ q = a) :
    ∃ y : PrimeKummerField a q, algebraMap (PrimeKummerField a q) (KummerTop a q) y = x := by
  have hα : kummerTopRadical a q ^ q = a := kummerTopRadical_pow a q
  have ha0 : (a : KummerTop a q) ≠ 0 := Nat.cast_ne_zero.mpr (by have := ha.out; omega)
  have hα0 : kummerTopRadical a q ≠ 0 := by
    intro h
    rw [h, zero_pow hq.out.ne_zero] at hα
    exact ha0 hα.symm
  have h1 : (x / kummerTopRadical a q) ^ q = 1 := by rw [div_pow, hx, hα, div_self ha0]
  obtain ⟨i, -, hi⟩ := (kummerTop_zetaPrime_spec a q).eq_pow_of_pow_eq_one h1
  refine ⟨AdjoinRoot.of (primeRadicalPolynomial a q)
      (IsCyclotomicExtension.zeta q ℚ (CyclotomicField q ℚ)) ^ i *
        AdjoinRoot.root (primeRadicalPolynomial a q), ?_⟩
  rw [map_mul, map_pow, hi, kummerTop_algebraMap_root, div_mul_cancel₀ _ hα0]

/-- `K̃` is generated over `K_q` by the `M`-th roots of unity. -/
theorem kummerTop_adjoin_kummer_eq_top :
    Algebra.adjoin (PrimeKummerField a q) {b : KummerTop a q | b ^ kummerLevel q = 1} = ⊤ := by
  refine Algebra.eq_top_iff.mpr fun x => ?_
  have hx := kummerTop_mem_adjoin_rootSet a q x
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rcases kummerTop_root_cases a q hy with hy | hy
    · exact Algebra.subset_adjoin hy
    · obtain ⟨z, rfl⟩ := kummerTop_exists_kummer_eq a q hy
      exact Subalgebra.algebraMap_mem _ z
  | algebraMap r =>
    rw [IsScalarTower.algebraMap_apply ℚ (PrimeKummerField a q) (KummerTop a q)]
    exact Subalgebra.algebraMap_mem _ _
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

/-- **`K̃ = K_q(ζ_M)`**: `K̃ / K_q` is the `M`-th cyclotomic extension. -/
instance kummerTop_isCyclotomicExtension :
    IsCyclotomicExtension {kummerLevel q} (PrimeKummerField a q) (KummerTop a q) :=
  (IsCyclotomicExtension.iff_singleton _ _ _).mpr
    ⟨⟨_, kummerTop_zeta_spec a q⟩, fun x => by
      rw [kummerTop_adjoin_kummer_eq_top]
      exact Algebra.mem_top⟩

/-- **`K̃ / K_q` is abelian**, as a cyclotomic extension. -/
instance kummerTop_isMulCommutative_kummer :
    IsMulCommutative (KummerTop a q ≃ₐ[PrimeKummerField a q] KummerTop a q) :=
  IsCyclotomicExtension.isMulCommutative {kummerLevel q} _ _

instance kummerTop_isAbelianGalois_kummer :
    IsAbelianGalois (PrimeKummerField a q) (KummerTop a q) where

/-- `K_q` is totally complex: it contains `ζ_q` with `q > a ≥ 2`. (Same statement as
`SimultaneousPrimitiveRoots.primeKummerField_isTotallyComplex` of `PrimeKummerComplexPlaces.lean`,
whose imports are much heavier.) -/
instance isTotallyComplex_primeKummerField : IsTotallyComplex (PrimeKummerField a q) :=
  haveI : IsTotallyComplex (CyclotomicField q ℚ) :=
    IsCyclotomicExtension.Rat.isTotallyComplex (n := q) (CyclotomicField q ℚ)
      (by have := ha.out; have := haq.out; omega)
  isTotallyComplex_of_algebra (CyclotomicField q ℚ) (PrimeKummerField a q)

end Kummer

end SimultaneousPrimitiveRoots.Unconditional

end
