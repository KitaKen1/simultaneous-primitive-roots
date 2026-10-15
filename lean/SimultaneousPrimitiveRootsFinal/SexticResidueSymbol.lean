import SimultaneousPrimitiveRootsFinal.SexticReciprocity
import ClassFieldTheory.AlgebraicNumberTheory.Completion.IntegerRingComparison
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Construction
import ClassFieldTheory.LocalClassFieldTheory.Kummer.PowerResidueTameFormula

/-!
# The sextic residue symbol and the tame formula

[A] §2 (`A-02:0111–0125`, `A-02:0237–0283`). `SexticReciprocity.lean` proves the reciprocity law
for the exterior Hilbert symbols of the canonical family. This file identifies those symbols with
the power residue symbol.

* `powerResidueSymbol F n hmu v hn a ha` (`sexticResidueSymbol` for `n = 6`) is the `n`-th power
  residue symbol `χ_v(a) ∈ μ_n(F)` at a finite place `v` prime to `n`, for `a ∈ Fˣ` a unit at `v`:
  CFT's `localTamePowerResidueSymbol` of the completion, read in `μ_n(F)`. It is multiplicative
  (`powerResidueSymbol_mul`, bundled as `powerResidueHom`).
* **Tame formula** (`canonicalHilbertFamily_finiteFactor_eq_powerResidueSymbol_zpow`): if `a` is a
  unit at `v` and `v.valuation F b = WithZero.exp (-m)`, i.e. `ord_v b = m`, then the canonical
  symbol is `(a, b)_v = χ_v(a) ^ m`.
* **Residue field** (`powerResidueSymbol_congruence`, `powerResidueSymbol_eq_iff`,
  `powerResidueSymbol_eq_one_iff_exists_pow`, `powerResidueSymbol_eq_one_iff_pow_sub_one`,
  `powerResidueSymbol_eq_one_iff`): `χ_v(a)` is the unique `ζ ∈ μ_n(F)` with
  `ζ ≡ a ^ ((N v - 1) / n) (mod v)`, and `χ_v(a) = 1` exactly when `a` is an `n`-th power modulo
  `v`.
* **[A] `eq:sextic-reciprocity`** (`sexticResidueSymbol_reciprocity`): `χ_𝔭(p') = χ_𝔭'(p)` for
  allowed generators of two distinct exterior primes.

## Conventions

The completion is `(NumberField.HeightOneSpectrum.adicAbv F v).Completion`, with the valuation
relation CFT registers on it (`chosenFinitePlaceBaseValuativeRel`, definitionally the
`finitePlaceLocalArtinCompletionValuativeRel` used by the local Artin map).

CFT's normalized valuation is `valuationMap = -ord_v` (`valuationMap_completionUnit`), its local
Artin map is `x ↦ Frob ^ valuationMap x` with `Frob` the arithmetic Frobenius, and its Hilbert
symbol is `(a, b) = Art(a)(β) / β` with `β ^ n = b`. [A] uses `Art(ϖ) = Frob` and
`(a, b) = Art(b)(α) / α` with `α ^ n = a`. The two inversions cancel by skew-symmetry. The
theorems below confirm it in the tame case: for a unit `u` and a uniformizer `ϖ`,
`(u, ϖ)_v = χ_v(u) ≡ u ^ ((N v - 1) / n) (mod v)`, which is the normalization of
`A-02:0120–0124` with no inversion.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Unconditional.CFTBridge

open ClassFieldTheory Arithmetic NumberField IsDedekindDomain
open GlobalClassFieldTheory.GlobalClassFields
open LocalFieldTheory LocalFieldTheory.IsNonarchimedeanLocalField
open scoped NumberField ValuativeRel NNReal

section LocalUnits

/-- A field unit of valuation one, as a unit of the valuation ring. -/
def integerUnitOfValuationEqOne (K : Type*) [Field K] [ValuativeRel K] (x : Kˣ)
    (hx : ValuativeRel.valuation K (x : K) = 1) : 𝒪[K]ˣ where
  val := ⟨(x : K), hx.le⟩
  inv := ⟨((x⁻¹ : Kˣ) : K), by
    rw [Valuation.mem_integer_iff, Units.val_inv_eq_inv_val, map_inv₀, hx, inv_one]⟩
  val_inv := Subtype.ext (by simp)
  inv_val := Subtype.ext (by simp)

@[simp]
theorem integerUnitsToFieldUnits_integerUnitOfValuationEqOne (K : Type*) [Field K]
    [ValuativeRel K] (x : Kˣ) (hx : ValuativeRel.valuation K (x : K) = 1) :
    integerUnitsToFieldUnits K (integerUnitOfValuationEqOne K x hx) = x :=
  Units.ext rfl

end LocalUnits

section Completion

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

local notation "Cv" => AbsoluteValue.Completion (NumberField.HeightOneSpectrum.adicAbv F v)

/-- The norm of a global element in the absolute-value completion at `v`. -/
theorem norm_algebraMap_adicAbvCompletion (a : F) :
    ‖algebraMap F Cv a‖ = NumberField.HeightOneSpectrum.adicAbv F v a := by
  change ‖((WithAbs.toAbs (NumberField.HeightOneSpectrum.adicAbv F v) a :
    WithAbs (NumberField.HeightOneSpectrum.adicAbv F v)) : Cv)‖ = _
  rw [UniformSpace.Completion.norm_coe, WithAbs.norm_toAbs_eq]

/-- The valuation of the completion used by the local Artin map orders elements by their
norms. -/
theorem adicAbvCompletion_valuation_le_iff (x y : Cv) :
    ValuativeRel.valuation Cv x ≤ ValuativeRel.valuation Cv y ↔ ‖x‖ ≤ ‖y‖ := by
  change ValuativeRel.ValueGroupWithZero.mk x 1 ≤ ValuativeRel.ValueGroupWithZero.mk y 1 ↔ _
  rw [ValuativeRel.ValueGroupWithZero.mk_le_mk]
  simp only [Submonoid.coe_one, mul_one]
  change NormedField.valuation x ≤ NormedField.valuation y ↔ _
  simp only [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm]

theorem adicAbvCompletion_valuation_eq_one_iff (x : Cv) :
    ValuativeRel.valuation Cv x = 1 ↔ ‖x‖ = 1 := by
  have h1 := adicAbvCompletion_valuation_le_iff F v x 1
  have h2 := adicAbvCompletion_valuation_le_iff F v 1 x
  rw [map_one, norm_one] at h1 h2
  rw [le_antisymm_iff, le_antisymm_iff, h1, h2]

theorem adicAbvCompletion_valuation_lt_one_iff (x : Cv) :
    ValuativeRel.valuation Cv x < 1 ↔ ‖x‖ < 1 := by
  have h2 := adicAbvCompletion_valuation_le_iff F v 1 x
  rw [map_one, norm_one] at h2
  rw [lt_iff_not_ge, lt_iff_not_ge, h2]

/-- A global element is a unit of the completion exactly when it is a unit at `v`. -/
theorem adicAbvCompletion_valuation_algebraMap_eq_one_iff (a : F) :
    ValuativeRel.valuation Cv (algebraMap F Cv a) = 1 ↔ v.valuation F a = 1 := by
  rw [adicAbvCompletion_valuation_eq_one_iff, norm_algebraMap_adicAbvCompletion,
    HeightOneSpectrum.adicAbv_def, NNReal.coe_eq_one]
  exact WithZeroMulInt.toNNReal_eq_one_iff _ (HeightOneSpectrum.absNorm_ne_zero v)
    (HeightOneSpectrum.one_lt_absNorm_nnreal v).ne'

/-- A global element lies in the maximal ideal of the completion exactly when it does at `v`. -/
theorem adicAbvCompletion_valuation_algebraMap_lt_one_iff (a : F) :
    ValuativeRel.valuation Cv (algebraMap F Cv a) < 1 ↔ v.valuation F a < 1 := by
  rw [adicAbvCompletion_valuation_lt_one_iff, norm_algebraMap_adicAbvCompletion,
    HeightOneSpectrum.adicAbv_def, ← NNReal.coe_one, NNReal.coe_lt_coe]
  exact WithZeroMulInt.toNNReal_lt_one_iff (HeightOneSpectrum.one_lt_absNorm_nnreal v)

/-- A unit of the completion of norm one has normalized valuation zero. -/
theorem adicAbvCompletion_valuationMap_eq_zero (x : Cvˣ) (hx : ‖(x : Cv)‖ = 1) :
    valuationMap Cv (Additive.ofMul x) = 0 := by
  have h := v_integerUnitsToFieldUnits Cv (integerUnitOfValuationEqOne Cv x
    ((adicAbvCompletion_valuation_eq_one_iff F v _).mpr hx))
  rw [integerUnitsToFieldUnits_integerUnitOfValuationEqOne] at h
  rw [valuationMap_apply]
  exact h

/-- The norm of the element of normalized valuation `-1` used by CFT. -/
theorem norm_chosenLocalOrderSection :
    ‖((GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinInput v
      (FiniteIdeleGroup.chosenLocalOrderSection v 1) : Cvˣ) : Cv)‖ =
      ((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ) ^ (-1 : ℤ) := by
  let a : (v.adicCompletion F)ˣ := FiniteIdeleGroup.chosenLocalOrderSection v 1
  let x : Cvˣ := GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinInput v a
  let f := finitePlaceCompletionRingHom v
  have hfx : f (x : Cv) = (a : v.adicCompletion F) :=
    congrArg Units.val ((finitePlaceCompletionUnitsContinuousMulEquiv v).apply_symm_apply a)
  have hva : Valued.v (a : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
    change Valued.v (Classical.choose
      (HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-1 : ℤ)))) = _
    exact Classical.choose_spec
      (HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-1 : ℤ)))
  have hnorm : ‖(x : Cv)‖ = ‖(a : v.adicCompletion F)‖ := by
    rw [← hfx]
    exact ((finitePlaceCompletionRingHom_isometry v).norm_map_of_map_zero
      (map_zero f) (x : Cv)).symm
  change ‖(x : Cv)‖ = _
  rw [hnorm, FinitePlace.norm_def, hva,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.log_exp, NNReal.coe_zpow]

/-- The norm of a global element of `v`-adic order `m`. -/
theorem norm_algebraMap_adicAbvCompletion_of_valuation {b : F} {m : ℤ}
    (hb : v.valuation F b = WithZero.exp (-m)) :
    ‖algebraMap F Cv b‖ = ((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ) ^ (-m) := by
  rw [norm_algebraMap_adicAbvCompletion, HeightOneSpectrum.adicAbv_def, hb,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.log_exp, NNReal.coe_zpow]

/-- **The normalized valuation of CFT on the completion is minus the `v`-adic order.** -/
theorem valuationMap_completionUnit (b : Fˣ) (m : ℤ)
    (hb : v.valuation F (b : F) = WithZero.exp (-m)) :
    valuationMap Cv (Additive.ofMul
      (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_completionUnit F v b)) = -m := by
  let x₀ : Cvˣ := GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinInput v
    (FiniteIdeleGroup.chosenLocalOrderSection v 1)
  let bC : Cvˣ := GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_completionUnit F v b
  have hx₀ : valuationMap Cv (Additive.ofMul x₀) = -1 :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceLocalArtinInput_chosenLocalOrderSection_valuationMap
      v
  have hq : ((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ) ≠ 0 :=
    NNReal.coe_ne_zero.mpr (HeightOneSpectrum.absNorm_ne_zero v)
  have hnorm : ‖((bC / x₀ ^ m : Cvˣ) : Cv)‖ = 1 := by
    have hb' : ‖(bC : Cv)‖ = ((Ideal.absNorm v.asIdeal : ℝ≥0) : ℝ) ^ (-m) :=
      norm_algebraMap_adicAbvCompletion_of_valuation F v hb
    rw [Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val, norm_div, norm_zpow, hb',
      norm_chosenLocalOrderSection F v, ← zpow_mul, neg_one_mul]
    exact div_self (zpow_ne_zero _ hq)
  have hzero := adicAbvCompletion_valuationMap_eq_zero F v _ hnorm
  rw [valuationMap_ofMul_div, valuationMap_ofMul_zpow, hx₀] at hzero
  change valuationMap Cv (Additive.ofMul bC) = -m
  linarith

end Completion

section LocalTame

/-- CFT's tame power-residue symbol is multiplicative. -/
theorem localTamePowerResidueSymbol_mul (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (n : ℕ+) (hn : ValuativeRel.valuation K ((n : ℕ) : K) = 1)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (u u' : 𝒪[K]ˣ) :
    LocalClassFieldTheory.Kummer.localTamePowerResidueSymbol K n hn hmu (u * u') =
      LocalClassFieldTheory.Kummer.localTamePowerResidueSymbol K n hn hmu u *
        LocalClassFieldTheory.Kummer.localTamePowerResidueSymbol K n hn hmu u' := by
  unfold LocalClassFieldTheory.Kummer.localTamePowerResidueSymbol
  simp only [map_mul]

/-- The reduction of CFT's tame symbol of `u` is the residue of `u` to the power `(q - 1) / n`. -/
theorem integerUnitsToResidueUnits_localTamePowerResidueSymbol (K : Type) [Field K]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : ℕ+)
    (hn : ValuativeRel.valuation K ((n : ℕ) : K) = 1)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (u : 𝒪[K]ˣ) :
    integerUnitsToResidueUnits K (LocalClassFieldTheory.Kummer.nthRootIntegerUnit K n
        (LocalClassFieldTheory.Kummer.localTamePowerResidueSymbol K n hn hmu u)) =
      integerUnitsToResidueUnits K u ^ ((Nat.card 𝓀[K] - 1) / (n : ℕ)) := by
  let : Fintype 𝓀[K] := Fintype.ofFinite _
  have h := congrArg Subtype.val
    (LocalClassFieldTheory.Kummer.localNthRootsReductionEquiv_localTamePowerResidueSymbol
      K n hn hmu u)
  rw [Nat.card_eq_fintype_card]
  exact h

/-- Two units of a valuation ring have the same residue exactly when their difference lies in
the maximal ideal. -/
theorem integerUnitsToResidueUnits_eq_iff_valuation_sub_lt_one (K : Type*) [Field K]
    [ValuativeRel K] (x y : 𝒪[K]ˣ) :
    integerUnitsToResidueUnits K x = integerUnitsToResidueUnits K y ↔
      ValuativeRel.valuation K
        ((((x : 𝒪[K]ˣ) : 𝒪[K]) : K) - (((y : 𝒪[K]ˣ) : 𝒪[K]) : K)) < 1 := by
  have h1 : integerUnitsToResidueUnits K x = integerUnitsToResidueUnits K y ↔
      IsLocalRing.residue 𝒪[K] (x : 𝒪[K]) = IsLocalRing.residue 𝒪[K] (y : 𝒪[K]) :=
    ⟨fun h => congrArg (fun z : 𝓀[K]ˣ => (z : 𝓀[K])) h, fun h => Units.ext h⟩
  rw [h1]
  change Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[K]) (x : 𝒪[K]) =
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[K]) (y : 𝒪[K]) ↔ _
  rw [Ideal.Quotient.eq, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

end LocalTame

section PowerResidue

variable (F : Type) [Field F] [NumberField F] (n : ℕ+)
  (hmu : (primitiveRoots (n : ℕ) F).Nonempty) (v : HeightOneSpectrum (𝓞 F))

local notation "Cv" => AbsoluteValue.Completion (NumberField.HeightOneSpectrum.adicAbv F v)

/-- The image, in the valuation ring of the completion, of an element of `Fˣ` which is a unit
at `v`. -/
def completionIntegerUnit (a : Fˣ) (ha : v.valuation F (a : F) = 1) : 𝒪[Cv]ˣ :=
  integerUnitOfValuationEqOne Cv
    (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_completionUnit F v a)
    ((adicAbvCompletion_valuation_algebraMap_eq_one_iff F v (a : F)).mpr ha)

@[simp]
theorem integerUnitsToFieldUnits_completionIntegerUnit (a : Fˣ)
    (ha : v.valuation F (a : F) = 1) :
    integerUnitsToFieldUnits Cv (completionIntegerUnit F v a ha) =
      GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_completionUnit F v a :=
  integerUnitsToFieldUnits_integerUnitOfValuationEqOne Cv _ _

theorem completionIntegerUnit_mul {a a' : Fˣ} (ha : v.valuation F (a : F) = 1)
    (ha' : v.valuation F (a' : F) = 1) (haa' : v.valuation F ((a * a' : Fˣ) : F) = 1) :
    completionIntegerUnit F v (a * a') haa' =
      completionIntegerUnit F v a ha * completionIntegerUnit F v a' ha' := by
  apply integerUnitsToFieldUnits_injective Cv
  rw [map_mul, integerUnitsToFieldUnits_completionIntegerUnit,
    integerUnitsToFieldUnits_completionIntegerUnit,
    integerUnitsToFieldUnits_completionIntegerUnit]
  exact map_mul (Units.map (algebraMap F Cv).toMonoidHom) a a'

/-- The exponent is a unit of the completion when it is a unit at `v`. -/
theorem adicAbvCompletion_valuation_natCast_eq_one (hn : v.valuation F ((n : ℕ) : F) = 1) :
    ValuativeRel.valuation Cv ((n : ℕ) : Cv) = 1 := by
  have h := (adicAbvCompletion_valuation_algebraMap_eq_one_iff F v ((n : ℕ) : F)).mpr hn
  rwa [map_natCast] at h

/-- **The `n`-th power residue symbol at a finite place `v` prime to `n`**, on the elements of
`Fˣ` which are units at `v`: CFT's tame symbol of the completion, read in `μ_n(F)`. -/
def powerResidueSymbol (hn : v.valuation F ((n : ℕ) : F) = 1) (a : Fˣ)
    (ha : v.valuation F (a : F) = 1) : rootsOfUnity (n : ℕ) F :=
  KummerTheory.nthRootsSubgroupEquivRootsOfUnity F (n : ℕ)
    ((KummerTheory.nthRootsSubgroupEquivOfPrimitiveRoots F Cv n hmu).symm
      (LocalClassFieldTheory.Kummer.localTamePowerResidueSymbol Cv n
        (adicAbvCompletion_valuation_natCast_eq_one F n v hn)
        (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_primitiveRoots_nonempty F n hmu v)
        (completionIntegerUnit F v a ha)))

/-- The power residue symbol is multiplicative. -/
theorem powerResidueSymbol_mul (hn : v.valuation F ((n : ℕ) : F) = 1) {a a' : Fˣ}
    (ha : v.valuation F (a : F) = 1) (ha' : v.valuation F (a' : F) = 1)
    (haa' : v.valuation F ((a * a' : Fˣ) : F) = 1) :
    powerResidueSymbol F n hmu v hn (a * a') haa' =
      powerResidueSymbol F n hmu v hn a ha * powerResidueSymbol F n hmu v hn a' ha' := by
  unfold powerResidueSymbol
  rw [completionIntegerUnit_mul F v ha ha' haa', localTamePowerResidueSymbol_mul, map_mul,
    map_mul]

/-- **The tame formula for the canonical family.** If `a` is a unit at `v`, `v` is prime to `n`,
and `b` has `v`-adic order `m`, then the canonical Hilbert symbol of `(a, b)` at `v` is the `m`-th
power of the power residue symbol of `a`. -/
theorem canonicalHilbertFamily_finiteFactor_eq_powerResidueSymbol_zpow
    (hn : v.valuation F ((n : ℕ) : F) = 1) (a : Fˣ) (ha : v.valuation F (a : F) = 1)
    (b : Fˣ) (m : ℤ) (hb : v.valuation F (b : F) = WithZero.exp (-m)) :
    GlobalHilbertPairingFamily.finiteFactor F (canonicalHilbertFamily F n hmu) hmu v a b =
      powerResidueSymbol F n hmu v hn a ha ^ m := by
  have hnF : ((n : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.mpr n.ne_zero
  have hlocal : GlobalClassFieldTheory.Reciprocity.finitePlaceLocalHilbertSymbol F n hnF hmu v a b =
      LocalClassFieldTheory.Kummer.localTamePowerResidueSymbol Cv n
        (adicAbvCompletion_valuation_natCast_eq_one F n v hn)
        (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_primitiveRoots_nonempty F n hmu v)
        (completionIntegerUnit F v a ha) ^ m := by
    have h := LocalClassFieldTheory.Kummer.localHilbertSymbol_tame_formula Cv n
      (adicAbvCompletion_valuation_natCast_eq_one F n v hn)
      (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_primitiveRoots_nonempty F n hmu v)
      (completionIntegerUnit F v a ha)
      (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_completionUnit F v b)
    rw [integerUnitsToFieldUnits_completionIntegerUnit, valuationMap_completionUnit F v b m hb,
      neg_neg] at h
    exact h
  rw [canonicalHilbertFamily_finiteFactor F n hnF hmu v a b]
  change KummerTheory.nthRootsSubgroupEquivRootsOfUnity F (n : ℕ)
      ((KummerTheory.nthRootsSubgroupEquivOfPrimitiveRoots F Cv n hmu).symm
        (GlobalClassFieldTheory.Reciprocity.finitePlaceLocalHilbertSymbol F n hnF hmu v a b)) = _
  rw [hlocal, map_zpow, map_zpow]
  rfl

/-- The tame formula, with the `v`-adic order of `b` written as `-log (v.valuation F b)`. -/
theorem canonicalHilbertFamily_finiteFactor_eq_powerResidueSymbol_zpow_log
    (hn : v.valuation F ((n : ℕ) : F) = 1) (a : Fˣ) (ha : v.valuation F (a : F) = 1) (b : Fˣ) :
    GlobalHilbertPairingFamily.finiteFactor F (canonicalHilbertFamily F n hmu) hmu v a b =
      powerResidueSymbol F n hmu v hn a ha ^ (-WithZero.log (v.valuation F (b : F))) := by
  refine canonicalHilbertFamily_finiteFactor_eq_powerResidueSymbol_zpow F n hmu v hn a ha b _ ?_
  rw [neg_neg, WithZero.exp_log ((Valuation.ne_zero_iff _).mpr b.ne_zero)]

/-- **The power residue symbol is trivial exactly on the `n`-th powers of the residue field** of
the completion. -/
theorem powerResidueSymbol_eq_one_iff (hn : v.valuation F ((n : ℕ) : F) = 1) (a : Fˣ)
    (ha : v.valuation F (a : F) = 1) :
    powerResidueSymbol F n hmu v hn a ha = 1 ↔
      ∃ w : 𝓀[Cv]ˣ, w ^ (n : ℕ) =
        integerUnitsToResidueUnits Cv (completionIntegerUnit F v a ha) := by
  let : Fintype 𝓀[Cv] := Fintype.ofFinite _
  have hnC := adicAbvCompletion_valuation_natCast_eq_one F n v hn
  have hmuC :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_primitiveRoots_nonempty F n hmu v
  have hdvd : (n : ℕ) ∣ Fintype.card 𝓀[Cv] - 1 := by
    rw [← Nat.card_eq_fintype_card]
    exact LocalClassFieldTheory.Kummer.dvd_residueCard_sub_one_of_primitiveRoots Cv n hnC hmuC
  have hred : LocalClassFieldTheory.Kummer.localNthRootsReductionEquiv Cv n hnC hmuC
      (LocalClassFieldTheory.Kummer.localTamePowerResidueSymbol Cv n hnC hmuC
        (completionIntegerUnit F v a ha)) =
      AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol 𝓀[Cv] n hdvd
        (integerUnitsToResidueUnits Cv (completionIntegerUnit F v a ha)) :=
    LocalClassFieldTheory.Kummer.localNthRootsReductionEquiv_localTamePowerResidueSymbol
      Cv n hnC hmuC (completionIntegerUnit F v a ha)
  unfold powerResidueSymbol
  rw [EmbeddingLike.map_eq_one_iff, EmbeddingLike.map_eq_one_iff,
    ← EmbeddingLike.map_eq_one_iff
      (f := LocalClassFieldTheory.Kummer.localNthRootsReductionEquiv Cv n hnC hmuC), hred]
  exact AlgebraicNumberTheory.PowerResidueSymbols.finiteFieldPowerResidueSymbol_eq_one_iff
    𝓀[Cv] n hdvd _

/-- The residue field of the completion has `N v` elements. -/
theorem adicAbvCompletion_residueField_card : Nat.card 𝓀[Cv] = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact finitePlaceCompletion_residueField_card v

/-- In the completion, the power residue symbol is CFT's tame symbol. -/
theorem algebraMap_powerResidueSymbol (hn : v.valuation F ((n : ℕ) : F) = 1) (a : Fˣ)
    (ha : v.valuation F (a : F) = 1) :
    algebraMap F Cv (((powerResidueSymbol F n hmu v hn a ha : rootsOfUnity (n : ℕ) F) : Fˣ) : F) =
      (((LocalClassFieldTheory.Kummer.localTamePowerResidueSymbol Cv n
        (adicAbvCompletion_valuation_natCast_eq_one F n v hn)
        (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_primitiveRoots_nonempty F n hmu v)
        (completionIntegerUnit F v a ha) : KummerTheory.nthRootsSubgroup Cv (n : ℕ)) : Cvˣ) :
          Cv) := by
  have hE := (KummerTheory.nthRootsSubgroupEquivOfPrimitiveRoots F Cv n hmu).apply_symm_apply
    (LocalClassFieldTheory.Kummer.localTamePowerResidueSymbol Cv n
      (adicAbvCompletion_valuation_natCast_eq_one F n v hn)
      (GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_primitiveRoots_nonempty F n hmu v)
      (completionIntegerUnit F v a ha))
  exact congrArg (fun z : KummerTheory.nthRootsSubgroup Cv (n : ℕ) => ((z : Cvˣ) : Cv)) hE

/-- **The power residue symbol is the `(N v - 1) / n`-th power modulo `v`**:
`χ_v(a) ≡ a ^ ((N v - 1) / n) (mod v)`. -/
theorem powerResidueSymbol_congruence (hn : v.valuation F ((n : ℕ) : F) = 1) (a : Fˣ)
    (ha : v.valuation F (a : F) = 1) :
    v.valuation F ((((powerResidueSymbol F n hmu v hn a ha : rootsOfUnity (n : ℕ) F) : Fˣ) : F) -
      (a : F) ^ ((Ideal.absNorm v.asIdeal - 1) / (n : ℕ))) < 1 := by
  have hnC := adicAbvCompletion_valuation_natCast_eq_one F n v hn
  have hmuC :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_primitiveRoots_nonempty F n hmu v
  have hres := integerUnitsToResidueUnits_localTamePowerResidueSymbol Cv n hnC hmuC
    (completionIntegerUnit F v a ha)
  rw [← map_pow] at hres
  have hval := (integerUnitsToResidueUnits_eq_iff_valuation_sub_lt_one Cv _ _).mp hres
  rw [← adicAbvCompletion_valuation_algebraMap_lt_one_iff, map_sub (algebraMap F Cv),
    map_pow (algebraMap F Cv), algebraMap_powerResidueSymbol,
    ← adicAbvCompletion_residueField_card]
  exact hval

/-- Reduction modulo `v` is injective on `μ_n(F)` when `v` is prime to `n`
([A] `A-02:0237–0238`). -/
theorem rootsOfUnity_eq_of_valuation_sub_lt_one (hn : v.valuation F ((n : ℕ) : F) = 1)
    {ζ ζ' : rootsOfUnity (n : ℕ) F}
    (h : v.valuation F (((ζ : Fˣ) : F) - ((ζ' : Fˣ) : F)) < 1) : ζ = ζ' := by
  have hnC := adicAbvCompletion_valuation_natCast_eq_one F n v hn
  let E := KummerTheory.nthRootsSubgroupEquivRootsOfUnity F (n : ℕ)
  let z := KummerTheory.nthRootsSubgroupMap F Cv (n : ℕ) (E.symm ζ)
  let z' := KummerTheory.nthRootsSubgroupMap F Cv (n : ℕ) (E.symm ζ')
  have hres : integerUnitsToResidueUnits Cv
      (LocalClassFieldTheory.Kummer.nthRootIntegerUnit Cv n z) =
      integerUnitsToResidueUnits Cv (LocalClassFieldTheory.Kummer.nthRootIntegerUnit Cv n z') := by
    rw [integerUnitsToResidueUnits_eq_iff_valuation_sub_lt_one]
    rw [← adicAbvCompletion_valuation_algebraMap_lt_one_iff, map_sub (algebraMap F Cv)] at h
    exact h
  have hz : z = z' :=
    LocalClassFieldTheory.Kummer.localNthRootsReduction_injective Cv n hnC (Subtype.ext hres)
  exact E.symm.injective (KummerTheory.nthRootsSubgroupMap_injective F Cv (n : ℕ) hz)

/-- **The power residue symbol is characterized by its congruence** ([A] `A-02:0237–0244`):
`χ_v(a)` is the unique `ζ ∈ μ_n(F)` with `ζ ≡ a ^ ((N v - 1) / n) (mod v)`. -/
theorem powerResidueSymbol_eq_iff (hn : v.valuation F ((n : ℕ) : F) = 1) (a : Fˣ)
    (ha : v.valuation F (a : F) = 1) (ζ : rootsOfUnity (n : ℕ) F) :
    powerResidueSymbol F n hmu v hn a ha = ζ ↔
      v.valuation F
        (((ζ : Fˣ) : F) - (a : F) ^ ((Ideal.absNorm v.asIdeal - 1) / (n : ℕ))) < 1 := by
  constructor
  · rintro rfl
    exact powerResidueSymbol_congruence F n hmu v hn a ha
  · intro h
    apply rootsOfUnity_eq_of_valuation_sub_lt_one F n v hn
    have h' := Valuation.map_sub_lt (v.valuation F)
      (powerResidueSymbol_congruence F n hmu v hn a ha) h
    rwa [sub_sub_sub_cancel_right] at h'

/-- **Euler's criterion**: the power residue symbol of `a` is trivial exactly when
`a ^ ((N v - 1) / n) ≡ 1 (mod v)`. -/
theorem powerResidueSymbol_eq_one_iff_pow_sub_one (hn : v.valuation F ((n : ℕ) : F) = 1)
    (a : Fˣ) (ha : v.valuation F (a : F) = 1) :
    powerResidueSymbol F n hmu v hn a ha = 1 ↔
      v.valuation F ((a : F) ^ ((Ideal.absNorm v.asIdeal - 1) / (n : ℕ)) - 1) < 1 := by
  have hnC := adicAbvCompletion_valuation_natCast_eq_one F n v hn
  have hmuC :=
    GlobalClassFieldTheory.Reciprocity.finitePlaceHilbert_primitiveRoots_nonempty F n hmu v
  have hres := integerUnitsToResidueUnits_localTamePowerResidueSymbol Cv n hnC hmuC
    (completionIntegerUnit F v a ha)
  have h1 : powerResidueSymbol F n hmu v hn a ha = 1 ↔
      integerUnitsToResidueUnits Cv (completionIntegerUnit F v a ha) ^
        ((Nat.card 𝓀[Cv] - 1) / (n : ℕ)) = 1 := by
    unfold powerResidueSymbol
    rw [EmbeddingLike.map_eq_one_iff, EmbeddingLike.map_eq_one_iff,
      ← EmbeddingLike.map_eq_one_iff
        (f := LocalClassFieldTheory.Kummer.localNthRootsReductionEquiv Cv n hnC hmuC), ← hres]
    exact Subtype.ext_iff
  have h2 := integerUnitsToResidueUnits_eq_iff_valuation_sub_lt_one Cv
    (completionIntegerUnit F v a ha ^ ((Nat.card 𝓀[Cv] - 1) / (n : ℕ))) 1
  rw [map_pow, map_one] at h2
  rw [h1, h2, ← adicAbvCompletion_valuation_algebraMap_lt_one_iff, map_sub (algebraMap F Cv),
    map_pow (algebraMap F Cv), map_one (algebraMap F Cv), ← adicAbvCompletion_residueField_card]
  exact Iff.rfl

/-- **The power residue symbol of `a` is trivial exactly when `a` is an `n`-th power modulo
`v`.** -/
theorem powerResidueSymbol_eq_one_iff_exists_pow (hn : v.valuation F ((n : ℕ) : F) = 1)
    (a : Fˣ) (ha : v.valuation F (a : F) = 1) :
    powerResidueSymbol F n hmu v hn a ha = 1 ↔
      ∃ c : F, v.valuation F (c ^ (n : ℕ) - (a : F)) < 1 := by
  rw [powerResidueSymbol_eq_one_iff]
  constructor
  · rintro ⟨w, hw⟩
    obtain ⟨wO, rfl⟩ := integerUnitsToResidueUnits_surjective Cv w
    obtain ⟨c', hc'⟩ := UniformSpace.Completion.denseRange_coe.exists_dist_lt
      (((wO : 𝒪[Cv]ˣ) : 𝒪[Cv]) : Cv) one_pos
    let c : F := c'.ofAbs
    have hcw : ValuativeRel.valuation Cv ((((wO : 𝒪[Cv]ˣ) : 𝒪[Cv]) : Cv) - algebraMap F Cv c) <
        1 := by
      rw [adicAbvCompletion_valuation_lt_one_iff, ← dist_eq_norm]
      exact hc'
    have hwO : ValuativeRel.valuation Cv (((wO : 𝒪[Cv]ˣ) : 𝒪[Cv]) : Cv) = 1 :=
      (Valuation.integer.integers (ValuativeRel.valuation Cv)).valuation_unit wO
    have hcC : ValuativeRel.valuation Cv (algebraMap F Cv c) = 1 := by
      have h := Valuation.map_sub_eq_of_lt_left (ValuativeRel.valuation Cv)
        (x := (((wO : 𝒪[Cv]ˣ) : 𝒪[Cv]) : Cv))
        (y := (((wO : 𝒪[Cv]ˣ) : 𝒪[Cv]) : Cv) - algebraMap F Cv c) (by rw [hwO]; exact hcw)
      rw [sub_sub_cancel, hwO] at h
      exact h
    have hc : v.valuation F c = 1 :=
      (adicAbvCompletion_valuation_algebraMap_eq_one_iff F v c).mp hcC
    have hc0 : c ≠ 0 := by
      rintro h0
      rw [h0, map_zero] at hc
      exact zero_ne_one hc
    have hc' : v.valuation F ((Units.mk0 c hc0 : Fˣ) : F) = 1 := hc
    have hres : integerUnitsToResidueUnits Cv (completionIntegerUnit F v (Units.mk0 c hc0) hc') =
        integerUnitsToResidueUnits Cv wO := by
      rw [integerUnitsToResidueUnits_eq_iff_valuation_sub_lt_one,
        ← Valuation.map_sub_swap]
      exact hcw
    have hw' : integerUnitsToResidueUnits Cv
        (completionIntegerUnit F v (Units.mk0 c hc0) hc' ^ (n : ℕ)) =
        integerUnitsToResidueUnits Cv (completionIntegerUnit F v a ha) := by
      rw [map_pow, hres]
      exact hw
    rw [integerUnitsToResidueUnits_eq_iff_valuation_sub_lt_one] at hw'
    refine ⟨c, ?_⟩
    rw [← adicAbvCompletion_valuation_algebraMap_lt_one_iff, map_sub (algebraMap F Cv),
      map_pow (algebraMap F Cv)]
    exact hw'
  · rintro ⟨c, hc⟩
    have hcn : v.valuation F (c ^ (n : ℕ)) = 1 := by
      have h := Valuation.map_add_eq_of_lt_left (v.valuation F) (x := (a : F))
        (y := c ^ (n : ℕ) - (a : F)) (by rw [ha]; exact hc)
      rw [add_sub_cancel, ha] at h
      exact h
    have hc1 : v.valuation F c = 1 := by
      rw [map_pow] at hcn
      exact (pow_eq_one_iff_of_nonneg zero_le n.ne_zero).mp hcn
    have hc0 : c ≠ 0 := by
      rintro h0
      rw [h0, map_zero] at hc1
      exact zero_ne_one hc1
    have hc1' : v.valuation F ((Units.mk0 c hc0 : Fˣ) : F) = 1 := hc1
    have h : integerUnitsToResidueUnits Cv
        (completionIntegerUnit F v (Units.mk0 c hc0) hc1' ^ (n : ℕ)) =
        integerUnitsToResidueUnits Cv (completionIntegerUnit F v a ha) := by
      rw [integerUnitsToResidueUnits_eq_iff_valuation_sub_lt_one]
      rw [← adicAbvCompletion_valuation_algebraMap_lt_one_iff, map_sub (algebraMap F Cv),
        map_pow (algebraMap F Cv)] at hc
      exact hc
    rw [map_pow] at h
    exact ⟨integerUnitsToResidueUnits Cv (completionIntegerUnit F v (Units.mk0 c hc0) hc1'), h⟩

/-- The power residue symbol of `1` is `1`. -/
theorem powerResidueSymbol_one (hn : v.valuation F ((n : ℕ) : F) = 1)
    (h1 : v.valuation F ((1 : Fˣ) : F) = 1) : powerResidueSymbol F n hmu v hn 1 h1 = 1 := by
  rw [powerResidueSymbol_eq_one_iff_exists_pow]
  exact ⟨1, by simp⟩

/-- The subgroup of the elements of `Fˣ` which are units at `v`. -/
def placeUnitSubgroup : Subgroup Fˣ where
  carrier := {a | v.valuation F (a : F) = 1}
  mul_mem' := by
    intro a b ha hb
    have ha' : v.valuation F (a : F) = 1 := ha
    have hb' : v.valuation F (b : F) = 1 := hb
    change v.valuation F ((a * b : Fˣ) : F) = 1
    rw [Units.val_mul, map_mul, ha', hb', one_mul]
  one_mem' := by
    change v.valuation F ((1 : Fˣ) : F) = 1
    rw [Units.val_one, map_one]
  inv_mem' := by
    intro a ha
    have ha' : v.valuation F (a : F) = 1 := ha
    change v.valuation F ((a⁻¹ : Fˣ) : F) = 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, ha', inv_one]

theorem mem_placeUnitSubgroup {a : Fˣ} :
    a ∈ placeUnitSubgroup F v ↔ v.valuation F (a : F) = 1 :=
  Iff.rfl

/-- The power residue symbol, as a homomorphism on the units at `v`. -/
def powerResidueHom (hn : v.valuation F ((n : ℕ) : F) = 1) :
    placeUnitSubgroup F v →* rootsOfUnity (n : ℕ) F :=
  MonoidHom.mk'
    (fun a => powerResidueSymbol F n hmu v hn a ((mem_placeUnitSubgroup F v).mp a.2))
    (fun a b => powerResidueSymbol_mul F n hmu v hn ((mem_placeUnitSubgroup F v).mp a.2)
      ((mem_placeUnitSubgroup F v).mp b.2) ((mem_placeUnitSubgroup F v).mp (a * b).2))

@[simp]
theorem powerResidueHom_apply (hn : v.valuation F ((n : ℕ) : F) = 1)
    (a : placeUnitSubgroup F v) :
    powerResidueHom F n hmu v hn a =
      powerResidueSymbol F n hmu v hn a ((mem_placeUnitSubgroup F v).mp a.2) :=
  rfl

end PowerResidue

section Sextic

variable (F : Type) [Field F] [NumberField F] (hmu6 : (primitiveRoots 6 F).Nonempty)
  (v : HeightOneSpectrum (𝓞 F))

local notation "Cv" => AbsoluteValue.Completion (NumberField.HeightOneSpectrum.adicAbv F v)

/-- **The sextic residue symbol** `χ_v` of [A] §2 at a finite place `v` prime to `6`, on the
elements of `Fˣ` which are units at `v`, with values in `μ_6(F)`. -/
def sexticResidueSymbol (h6 : v.valuation F ((6 : ℕ) : F) = 1) (a : Fˣ)
    (ha : v.valuation F (a : F) = 1) : rootsOfUnity ((6 : ℕ+) : ℕ) F :=
  powerResidueSymbol F 6 hmu6 v h6 a ha

/-- The sextic residue symbol is multiplicative. -/
theorem sexticResidueSymbol_mul (h6 : v.valuation F ((6 : ℕ) : F) = 1) {a a' : Fˣ}
    (ha : v.valuation F (a : F) = 1) (ha' : v.valuation F (a' : F) = 1)
    (haa' : v.valuation F ((a * a' : Fˣ) : F) = 1) :
    sexticResidueSymbol F hmu6 v h6 (a * a') haa' =
      sexticResidueSymbol F hmu6 v h6 a ha * sexticResidueSymbol F hmu6 v h6 a' ha' :=
  powerResidueSymbol_mul F 6 hmu6 v h6 ha ha' haa'

/-- The sextic residue symbol of `1` is `1`. -/
theorem sexticResidueSymbol_one (h6 : v.valuation F ((6 : ℕ) : F) = 1)
    (h1 : v.valuation F ((1 : Fˣ) : F) = 1) : sexticResidueSymbol F hmu6 v h6 1 h1 = 1 :=
  powerResidueSymbol_one F 6 hmu6 v h6 h1

/-- The sextic residue symbol, as a homomorphism on the units at `v`. -/
def sexticResidueHom (h6 : v.valuation F ((6 : ℕ) : F) = 1) :
    placeUnitSubgroup F v →* rootsOfUnity ((6 : ℕ+) : ℕ) F :=
  powerResidueHom F 6 hmu6 v h6

@[simp]
theorem sexticResidueHom_apply (h6 : v.valuation F ((6 : ℕ) : F) = 1)
    (a : placeUnitSubgroup F v) :
    sexticResidueHom F hmu6 v h6 a =
      sexticResidueSymbol F hmu6 v h6 a ((mem_placeUnitSubgroup F v).mp a.2) :=
  rfl

/-- **The tame formula for the canonical sextic family.** If `a` is a unit at the place `v` prime
to `6` and `b` has `v`-adic order `m`, then `(a, b)_{6,v} = χ_v(a) ^ m`. -/
theorem canonicalHilbertFamily_finiteFactor_eq_sexticResidueSymbol_zpow
    (h6 : v.valuation F ((6 : ℕ) : F) = 1) (a : Fˣ) (ha : v.valuation F (a : F) = 1) (b : Fˣ)
    (m : ℤ) (hb : v.valuation F (b : F) = WithZero.exp (-m)) :
    GlobalHilbertPairingFamily.finiteFactor F (canonicalHilbertFamily F 6 hmu6) hmu6 v a b =
      sexticResidueSymbol F hmu6 v h6 a ha ^ m :=
  canonicalHilbertFamily_finiteFactor_eq_powerResidueSymbol_zpow F 6 hmu6 v h6 a ha b m hb

/-- The sextic tame formula, with the `v`-adic order of `b` written as
`-log (v.valuation F b)`. -/
theorem canonicalHilbertFamily_finiteFactor_eq_sexticResidueSymbol_zpow_log
    (h6 : v.valuation F ((6 : ℕ) : F) = 1) (a : Fˣ) (ha : v.valuation F (a : F) = 1) (b : Fˣ) :
    GlobalHilbertPairingFamily.finiteFactor F (canonicalHilbertFamily F 6 hmu6) hmu6 v a b =
      sexticResidueSymbol F hmu6 v h6 a ha ^ (-WithZero.log (v.valuation F (b : F))) :=
  canonicalHilbertFamily_finiteFactor_eq_powerResidueSymbol_zpow_log F 6 hmu6 v h6 a ha b

/-- **The sextic residue symbol is trivial exactly on the sixth powers of the residue field** of
the completion (the form given by CFT's `finiteFieldPowerResidueSymbol_eq_one_iff`). -/
theorem sexticResidueSymbol_eq_one_iff (h6 : v.valuation F ((6 : ℕ) : F) = 1) (a : Fˣ)
    (ha : v.valuation F (a : F) = 1) :
    sexticResidueSymbol F hmu6 v h6 a ha = 1 ↔
      ∃ w : 𝓀[Cv]ˣ, w ^ 6 = integerUnitsToResidueUnits Cv (completionIntegerUnit F v a ha) :=
  powerResidueSymbol_eq_one_iff F 6 hmu6 v h6 a ha

/-- **The sextic residue symbol of `a` is trivial exactly when `a` is a sixth power modulo
`v`.** -/
theorem sexticResidueSymbol_eq_one_iff_exists_pow (h6 : v.valuation F ((6 : ℕ) : F) = 1)
    (a : Fˣ) (ha : v.valuation F (a : F) = 1) :
    sexticResidueSymbol F hmu6 v h6 a ha = 1 ↔ ∃ c : F, v.valuation F (c ^ 6 - (a : F)) < 1 :=
  powerResidueSymbol_eq_one_iff_exists_pow F 6 hmu6 v h6 a ha

/-- **Euler's criterion** for the sextic residue symbol. -/
theorem sexticResidueSymbol_eq_one_iff_pow_sub_one (h6 : v.valuation F ((6 : ℕ) : F) = 1)
    (a : Fˣ) (ha : v.valuation F (a : F) = 1) :
    sexticResidueSymbol F hmu6 v h6 a ha = 1 ↔
      v.valuation F ((a : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6) - 1) < 1 :=
  powerResidueSymbol_eq_one_iff_pow_sub_one F 6 hmu6 v h6 a ha

/-- **[A] `A-02:0237–0244`**: `χ_v(a) ≡ a ^ ((N v - 1) / 6) (mod v)`. -/
theorem sexticResidueSymbol_congruence (h6 : v.valuation F ((6 : ℕ) : F) = 1) (a : Fˣ)
    (ha : v.valuation F (a : F) = 1) :
    v.valuation F
      ((((sexticResidueSymbol F hmu6 v h6 a ha : rootsOfUnity ((6 : ℕ+) : ℕ) F) : Fˣ) : F) -
        (a : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6)) < 1 :=
  powerResidueSymbol_congruence F 6 hmu6 v h6 a ha

/-- **[A] `A-02:0237–0244`**: `χ_v(a)` is the unique sixth root of unity `ζ` of `F` with
`ζ ≡ a ^ ((N v - 1) / 6) (mod v)`. -/
theorem sexticResidueSymbol_eq_iff (h6 : v.valuation F ((6 : ℕ) : F) = 1) (a : Fˣ)
    (ha : v.valuation F (a : F) = 1) (ζ : rootsOfUnity ((6 : ℕ+) : ℕ) F) :
    sexticResidueSymbol F hmu6 v h6 a ha = ζ ↔
      v.valuation F (((ζ : Fˣ) : F) - (a : F) ^ ((Ideal.absNorm v.asIdeal - 1) / 6)) < 1 :=
  powerResidueSymbol_eq_iff F 6 hmu6 v h6 a ha ζ

end Sextic

section Exterior

variable {F : Type} [Field F] [NumberField F] (hmu6 : (primitiveRoots 6 F).Nonempty)
  {seed : Finset (HeightOneSpectrum (𝓞 F))}

/-- Outside the support, `6` is a unit. -/
theorem valuation_six_eq_one_of_notMem_sUnitSexticSupport {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ sUnitSexticSupport F seed) : v.valuation F ((6 : ℕ) : F) = 1 :=
  valuation_natCast_eq_one_of_not_mem_sUnitKummerNormSupport 6 _ hv

/-- **The tame formula for the exterior symbols**: at an exterior place `v`, if `a` is a unit at
`v` and `b` has `v`-adic order `m`, then the exterior symbol of `(a, b)` is `χ_v(a) ^ m`. -/
theorem exteriorSymbol_eq_sexticResidueSymbol_zpow {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ sUnitSexticSupport F seed) (a : Fˣ) (ha : v.valuation F (a : F) = 1) (b : Fˣ)
    (m : ℤ) (hb : v.valuation F (b : F) = WithZero.exp (-m)) :
    exteriorSymbol F seed hmu6 v a b =
      sexticResidueSymbol F hmu6 v (valuation_six_eq_one_of_notMem_sUnitSexticSupport hv) a ha ^
        m := by
  rw [exteriorSymbol_of_notMem hmu6 hv]
  exact canonicalHilbertFamily_finiteFactor_eq_sexticResidueSymbol_zpow F hmu6 v _ a ha b m hb

/-- **[A] `eq:sextic-reciprocity`**: `χ_𝔭(p') = χ_𝔭'(p)` for allowed generators `p`, `p'` of two
distinct exterior primes `𝔭`, `𝔭'`. Here `a` is `p` and `b` is `p'`: each is allowed, a unit at
the other exterior places, and of order one at its own prime. -/
theorem sexticResidueSymbol_reciprocity [IsTotallyComplex F] (A : AllowedClasses F seed hmu6)
    {a b : Fˣ} (ha : A.IsAllowed a) (hb : A.IsAllowed b) {p p' : HeightOneSpectrum (𝓞 F)}
    (hpp' : p ≠ p') (hp : p ∉ sUnitSexticSupport F seed) (hp' : p' ∉ sUnitSexticSupport F seed)
    (hap : ∀ v ∉ sUnitSexticSupport F seed, v ≠ p → v.valuation F (a : F) = 1)
    (hbp : ∀ v ∉ sUnitSexticSupport F seed, v ≠ p' → v.valuation F (b : F) = 1)
    (hpa : p.valuation F (a : F) = WithZero.exp (-1 : ℤ))
    (hp'b : p'.valuation F (b : F) = WithZero.exp (-1 : ℤ)) :
    sexticResidueSymbol F hmu6 p (valuation_six_eq_one_of_notMem_sUnitSexticSupport hp) b
        (hbp p hp hpp') =
      sexticResidueSymbol F hmu6 p' (valuation_six_eq_one_of_notMem_sUnitSexticSupport hp') a
        (hap p' hp' hpp'.symm) := by
  have h := exteriorSymbol_reciprocity hmu6 A ha hb hpp' hap hbp
  rw [exteriorSymbol_swap hmu6 p a b, exteriorSymbol_swap hmu6 p' b a,
    exteriorSymbol_eq_sexticResidueSymbol_zpow hmu6 hp b (hbp p hp hpp') a 1 hpa,
    exteriorSymbol_eq_sexticResidueSymbol_zpow hmu6 hp' a (hap p' hp' hpp'.symm) b 1 hp'b,
    zpow_one, zpow_one, inv_inj] at h
  exact h

end Exterior

end SimultaneousPrimitiveRoots.Unconditional.CFTBridge
