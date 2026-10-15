import SimultaneousPrimitiveRootsFinal.SUnitSexticPreparation
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceAdicHilbertProductFormula

/-!
# Sextic reciprocity with no supplementary factor

[A] §2 (`A-02:0229–0283`): for allowed generators the sextic Hilbert symbols at the places of `S`
multiply to one, so the global product formula leaves only the symbols at the exterior primes.

`SUnitSexticPreparation.lean` constructs an isotropic complement for *some* coherent family of
local Hilbert pairings. Two such families may differ at each place by a unit of `ℤ/6`, and the
isotropy of a subgroup is a statement about a product over the places of `S`, so isotropy for one
family does not give isotropy for another. An explicit reciprocity law needs the family normalized
by the local Artin maps, for which the tame formula holds. This file therefore

* fixes that canonical family (`canonicalHilbertFamily`, CFT's
  `finitePlaceAdicHilbertPairingFamily`, whose finite factors are CFT's
  `globalFinitePlaceHilbertSymbol`);
* reruns the construction of the isotropic complement for it (`AllowedClasses`,
  `nonempty_allowedClasses`), with existence and uniqueness modulo `U_S^6` of allowed generators;
* proves the product formula split at `S` (`sProd_mul_finprod_exteriorSymbol`), its consequence
  for allowed generators (`finprod_exteriorSymbol_eq_one`), the reciprocity law for generators
  supported at two distinct exterior primes (`exteriorSymbol_reciprocity`,
  [A] `eq:sextic-reciprocity` before the tame evaluation), and the unit symbol
  (`finprod_exteriorSymbol_sUnit`, [A] `eq:unit-symbol`).

The identification of the exterior symbol with the residue symbol `u ↦ u ^ ((N𝔭 - 1)/6)` is CFT's
`localHilbertSymbol_tame_formula`; that translation is not in this file.
-/

noncomputable section
-- As in `SUnitSexticPreparation.lean`: CFT's power-class abbreviation and the generic quotient
-- expose definitionally equal group instances through different paths.
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Unconditional.CFTBridge

open ClassFieldTheory Arithmetic NumberField IsDedekindDomain
open GlobalClassFieldTheory.GlobalClassFields
open scoped NumberField

section Canonical

variable (F : Type) [Field F] [NumberField F]

/-- CFT's local Hilbert pairings, normalized by the local Artin maps. -/
def canonicalHilbertFamily (n : ℕ+) (hmu : (primitiveRoots (n : ℕ) F).Nonempty) :
    GlobalHilbertPairingFamily F n :=
  finitePlaceAdicHilbertPairingFamily F n hmu

/-- The canonical family is locally Hilbert, finitely supported, and satisfies the product
formula. -/
theorem canonicalHilbertFamily_isCoherent (n : ℕ+)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty) :
    IsCoherentHilbertFamily F n hmu (canonicalHilbertFamily F n hmu) :=
  finitePlaceAdicHilbertPairingFamily_productFormula F n hmu

/-- The finite factors of the canonical family are CFT's finite-place Hilbert symbols. -/
theorem canonicalHilbertFamily_finiteFactor (n : ℕ+) (hnF : ((n : ℕ) : F) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) F).Nonempty) (v : HeightOneSpectrum (𝓞 F)) (a b : Fˣ) :
    GlobalHilbertPairingFamily.finiteFactor F (canonicalHilbertFamily F n hmu) hmu v a b =
      globalFinitePlaceHilbertSymbol F n hnF hmu v a b :=
  finitePlaceAdicHilbertPairingFamily_finiteFactor F n hnF hmu v a b

end Canonical

section FiniteFactor

variable {F : Type} [Field F] [NumberField F] {n : ℕ+}
  (H : GlobalHilbertPairingFamily F n) (hmu : (primitiveRoots (n : ℕ) F).Nonempty)
  (v : HeightOneSpectrum (𝓞 F))

/-- The finite factor is multiplicative in its first argument. -/
theorem finiteFactor_mul_left (a a' b : Fˣ) :
    GlobalHilbertPairingFamily.finiteFactor F H hmu v (a * a') b =
      GlobalHilbertPairingFamily.finiteFactor F H hmu v a b *
        GlobalHilbertPairingFamily.finiteFactor F H hmu v a' b := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let e : rootsOfUnity (n : ℕ) F ≃* rootsOfUnity (n : ℕ) (v.adicCompletion F) :=
    rootsOfUnityEquivOfPrimitiveRoots (algebraMap F (v.adicCompletion F)).injective hmu
  let ι : Fˣ →* (v.adicCompletion F)ˣ :=
    Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom
  change e.symm (H v (powerClass _ n (ι (a * a'))) (powerClass _ n (ι b))) =
    e.symm (H v (powerClass _ n (ι a)) (powerClass _ n (ι b))) *
      e.symm (H v (powerClass _ n (ι a')) (powerClass _ n (ι b)))
  rw [map_mul, map_mul, map_mul, MonoidHom.mul_apply, map_mul]

/-- The finite factor is multiplicative in its second argument. -/
theorem finiteFactor_mul_right (a b b' : Fˣ) :
    GlobalHilbertPairingFamily.finiteFactor F H hmu v a (b * b') =
      GlobalHilbertPairingFamily.finiteFactor F H hmu v a b *
        GlobalHilbertPairingFamily.finiteFactor F H hmu v a b' := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let e : rootsOfUnity (n : ℕ) F ≃* rootsOfUnity (n : ℕ) (v.adicCompletion F) :=
    rootsOfUnityEquivOfPrimitiveRoots (algebraMap F (v.adicCompletion F)).injective hmu
  let ι : Fˣ →* (v.adicCompletion F)ˣ :=
    Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom
  change e.symm (H v (powerClass _ n (ι a)) (powerClass _ n (ι (b * b')))) =
    e.symm (H v (powerClass _ n (ι a)) (powerClass _ n (ι b))) *
      e.symm (H v (powerClass _ n (ι a)) (powerClass _ n (ι b')))
  rw [map_mul, map_mul, map_mul, map_mul]

/-- A skew-symmetric local pairing has skew-symmetric finite factors. -/
theorem finiteFactor_swap (hH : (H v).IsSkewSymmetric) (a b : Fˣ) :
    GlobalHilbertPairingFamily.finiteFactor F H hmu v a b =
      (GlobalHilbertPairingFamily.finiteFactor F H hmu v b a)⁻¹ := by
  let : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  let e : rootsOfUnity (n : ℕ) F ≃* rootsOfUnity (n : ℕ) (v.adicCompletion F) :=
    rootsOfUnityEquivOfPrimitiveRoots (algebraMap F (v.adicCompletion F)).injective hmu
  let ι : Fˣ →* (v.adicCompletion F)ˣ :=
    Units.map (algebraMap F (v.adicCompletion F)).toMonoidHom
  change e.symm (H v (powerClass _ n (ι a)) (powerClass _ n (ι b))) =
    (e.symm (H v (powerClass _ n (ι b)) (powerClass _ n (ι a))))⁻¹
  rw [hH (powerClass _ n (ι a)) (powerClass _ n (ι b)), map_inv]

end FiniteFactor

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]
variable (seed : Finset (HeightOneSpectrum (𝓞 F)))

/-- The stage-6 preparation for a *given* coherent sextic family: the S-unit classes inject, and
they have an isotropic complement for the product of the local pairings of that same family. -/
theorem sUnit_sextic_hilbert_preparation_of_coherent
    (hmu12 : (primitiveRoots 12 F).Nonempty) (hmu6 : (primitiveRoots 6 F).Nonempty)
    (H : GlobalHilbertPairingFamily F 6) (hcoherent : IsCoherentHilbertFamily F 6 hmu6 H) :
    let S := sUnitSexticSupport F seed
    Function.Injective (sUnitPowerLocalization F S 6) ∧
      ∃ C : Subgroup (∀ v : S, PowerClassGroup (v.1.adicCompletion F) 6),
        IsCompl (sUnitPowerLocalization F S 6).range C ∧
        ∀ x ∈ C, ∀ y ∈ C,
          piPairing (fun v : S => finitePlaceGlobalRootPairing F 6 hmu6 H v) x y = 1 := by
  classical
  dsimp only
  let S := sUnitSexticSupport F seed
  have hmu2 := primitiveRoots_nonempty_of_dvd (K := F) 2 (by decide : 0 < 12)
    (by decide : 2 ∣ 12) hmu12
  have hmu3 := primitiveRoots_nonempty_of_dvd (K := F) 3 (by decide : 0 < 12)
    (by decide : 3 ∣ 12) hmu12
  have hiso := sUnitPowerLocalization_isotropic F S 6 hmu6
    (fun v hv => valuation_natCast_eq_one_of_not_mem_sUnitKummerNormSupport 6 _ hv)
    H hcoherent.1 hcoherent.2.2
  let P := piPairing (fun v : S => finitePlaceGlobalRootPairing F 6 hmu6 H v)
  have hnd : ∀ x, (∀ y, P x y = 1) → x = 1 :=
    piPairing_nondegenerate _ (fun v => commonRootPairing_nondegenerate _ (H v.1)
      (hcoherent.1 v.1).2.2.1)
  obtain ⟨u, hu⟩ := minus_one_is_power_of_double_roots (K := F) 6 hmu12
  have halt : ∀ x, P x x = 1 := by
    apply piPairing_alternating
    intro v x
    let w := Units.map (algebraMap F (v.1.adicCompletion F)).toMonoidHom u
    have hw : w ^ (6 : ℕ) = -1 := by
      have hu' : u ^ (6 : ℕ) = -1 := hu
      rw [← map_pow, hu']
      apply Units.ext
      simp
    have hi := hilbertPairing_isAlt_of_minus_one_is_power (H v.1)
      (hcoherent.1 v.1).1 ⟨w, hw⟩ x
    change commonRootPairing _ (H v.1) x x = 1
    rw [commonRootPairing_apply, hi, map_one]
  have hcard2 : Nat.card (sUnitPowerLocalization F S 2).range ^ 2 =
      Nat.card (∀ v : S, PowerClassGroup (v.1.adicCompletion F) 2) := by
    let Q (T : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
      Nat.card (sUnitPowerLocalization F T 2).range ^ 2 =
        Nat.card (∀ v : T, PowerClassGroup (v.1.adicCompletion F) 2)
    have h := sUnitPowerLocalization_card_sq_on_kummerNormSupport F
      (sUnitKummerNormSupport (K := F) 6 (sUnitKummerNormSupport (K := F) 3 seed)) 2 hmu2
    exact (congrArg Q (sUnitSexticSupport_two F seed).symm).mp h
  have hcard3 : Nat.card (sUnitPowerLocalization F S 3).range ^ 2 =
      Nat.card (∀ v : S, PowerClassGroup (v.1.adicCompletion F) 3) := by
    let Q (T : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
      Nat.card (sUnitPowerLocalization F T 3).range ^ 2 =
        Nat.card (∀ v : T, PowerClassGroup (v.1.adicCompletion F) 3)
    have h := sUnitPowerLocalization_card_sq_on_kummerNormSupport F
      (sUnitKummerNormSupport (K := F) 2 (sUnitKummerNormSupport (K := F) 6 seed)) 3 hmu3
    exact (congrArg Q (sUnitSexticSupport_three F seed).symm).mp h
  let : ∀ v : S, ValuativeRel (v.1.adicCompletion F) := fun v =>
    finitePlaceCompletionValuativeRel F v.1
  let : ∀ v : S, IsNonarchimedeanLocalField (v.1.adicCompletion F) := fun v =>
    finitePlaceCompletionIsNonarchimedeanLocalField F v.1
  let : ∀ v : S, Finite (PowerClassGroup (v.1.adicCompletion F) 2) := fun v =>
    powerClassGroup_finite _ 2 (Nat.cast_ne_zero.mpr (by decide : (2 : ℕ) ≠ 0))
  let : ∀ v : S, Finite (PowerClassGroup (v.1.adicCompletion F) 3) := fun v =>
    powerClassGroup_finite _ 3 (Nat.cast_ne_zero.mpr (by decide : (3 : ℕ) ≠ 0))
  obtain ⟨-, C, hC, hCI⟩ := exists_sextic_compl_of_one_pairing (sLocalSexticCrt F S) P
    (fun x => funext fun v => powerClass_pow_eq_one (v.1.adicCompletion F)ˣ 2 (x v))
    (fun x => funext fun v => powerClass_pow_eq_one (v.1.adicCompletion F)ˣ 3 (x v))
    (rootsOfUnityZModEquiv 2 hmu2) (rootsOfUnityZModEquiv 3 hmu3)
    hnd halt (sLocalSexticCrt_map_range F S) hiso hcard2 hcard3
  exact ⟨sUnitPowerLocalization_injective_on_kummerNormSupport F _ 6 hmu6, C, hC, hCI⟩

variable (hmu6 : (primitiveRoots 6 F).Nonempty)

/-- The product over the places of `S` of the canonical sextic Hilbert symbols, on the local power
classes. In [A]'s notation this is `H_S` (up to the orientation convention of the local symbol). -/
def sexticSPairing :
    (∀ v : sUnitSexticSupport F seed, PowerClassGroup (v.1.adicCompletion F) 6) →*
      (∀ v : sUnitSexticSupport F seed, PowerClassGroup (v.1.adicCompletion F) 6) →*
        rootsOfUnity ((6 : ℕ+) : ℕ) F :=
  piPairing fun v : sUnitSexticSupport F seed =>
    finitePlaceGlobalRootPairing F 6 hmu6 (canonicalHilbertFamily F 6 hmu6) v

/-- The class at `S` of a nonzero element of `F`, as a tuple of local sextic power classes. -/
def sexticSClass (a : Fˣ) :
    ∀ v : sUnitSexticSupport F seed, PowerClassGroup (v.1.adicCompletion F) 6 :=
  powerClassPiEquiv (fun v : sUnitSexticSupport F seed => (v.1.adicCompletion F)ˣ) 6
    (powerClassMk _ 6 (fieldToFiniteS F (sUnitSexticSupport F seed) a))

omit [IsTotallyComplex F] in
/-- On field elements the `S`-pairing is the product of the canonical finite factors over `S`. -/
theorem sexticSPairing_sexticSClass (a b : Fˣ) :
    sexticSPairing F seed hmu6 (sexticSClass F seed a) (sexticSClass F seed b) =
      ∏ v ∈ sUnitSexticSupport F seed,
        GlobalHilbertPairingFamily.finiteFactor F (canonicalHilbertFamily F 6 hmu6) hmu6 v a b := by
  change (∏ v : sUnitSexticSupport F seed,
    GlobalHilbertPairingFamily.finiteFactor F (canonicalHilbertFamily F 6 hmu6) hmu6 v a b) = _
  exact Finset.prod_coe_sort (sUnitSexticSupport F seed)
    (fun v : HeightOneSpectrum (𝓞 F) =>
      GlobalHilbertPairingFamily.finiteFactor F (canonicalHilbertFamily F 6 hmu6) hmu6 v a b)

/-- **[A] `lem:balanced-generators`, for the canonical sextic Hilbert symbols**: a subgroup `B` of
the sextic power classes at `S`, complementary to the classes of the S-units and isotropic for
`H_S`. -/
structure AllowedClasses where
  /-- The isotropic complement. -/
  B : Subgroup (PowerClass (∀ v : sUnitSexticSupport F seed, (v.1.adicCompletion F)ˣ) 6)
  isCompl : IsCompl (powerClassMap (sUnitToFiniteS F (sUnitSexticSupport F seed)) 6).range B
  isotropic : ∀ x ∈ B, ∀ y ∈ B,
    sexticSPairing F seed hmu6
      (powerClassPiEquiv (fun v : sUnitSexticSupport F seed => (v.1.adicCompletion F)ˣ) 6 x)
      (powerClassPiEquiv (fun v : sUnitSexticSupport F seed => (v.1.adicCompletion F)ˣ) 6 y) = 1

/-- **Existence of the isotropic complement for the canonical family.** -/
theorem nonempty_allowedClasses (hmu12 : (primitiveRoots 12 F).Nonempty) :
    Nonempty (AllowedClasses F seed hmu6) := by
  classical
  let S := sUnitSexticSupport F seed
  obtain ⟨-, C, hC, hCI⟩ := sUnit_sextic_hilbert_preparation_of_coherent F seed hmu12 hmu6
    (canonicalHilbertFamily F 6 hmu6) (canonicalHilbertFamily_isCoherent F 6 hmu6)
  let e := powerClassPiEquiv (fun v : S => (v.1.adicCompletion F)ˣ) 6
  refine ⟨⟨e.comapSubgroup C, ?_, fun x hx y hy => hCI _ hx _ hy⟩⟩
  have h := e.comapSubgroup.isCompl hC
  have he : e.comapSubgroup (sUnitPowerLocalization F S 6).range =
      (powerClassMap (sUnitToFiniteS F S) 6).range :=
    sUnitToFiniteS_range_comap F S 6
  exact (congrArg (fun E => IsCompl E (e.comapSubgroup C)) he).mp h

namespace AllowedClasses

variable {F seed hmu6}
variable (A : AllowedClasses F seed hmu6)

/-- An allowed generator: its class at `S` lies in `B`. -/
def IsAllowed (a : Fˣ) : Prop :=
  powerClassMk _ 6 (fieldToFiniteS F (sUnitSexticSupport F seed) a) ∈ A.B

omit [IsTotallyComplex F] in
/-- Products of allowed elements are allowed. -/
theorem IsAllowed.mul {a b : Fˣ} (ha : A.IsAllowed a) (hb : A.IsAllowed b) :
    A.IsAllowed (a * b) := by
  unfold IsAllowed at ha hb ⊢
  rw [map_mul, map_mul]
  exact A.B.mul_mem ha hb

omit [IsTotallyComplex F] in
/-- Every nonzero element becomes allowed after multiplication by an S-unit. -/
theorem exists_sUnit_mul_isAllowed (a : Fˣ) :
    ∃ u : SUnitGroup (K := F) (sUnitSexticSupport F seed), A.IsAllowed ((u : Fˣ) * a) := by
  let S := sUnitSexticSupport F seed
  have hB : IsCompl ((powerClassMk _ 6).comp (sUnitToFiniteS F S)).range A.B := by
    rw [← powerClassMap_range]
    exact A.isCompl
  obtain ⟨u, hu⟩ := exists_unit_adjusted_allowed (sUnitToFiniteS F S) (powerClassMk _ 6)
    hB (fieldToFiniteS F S a)
  exact ⟨u, by
    simpa only [IsAllowed, sUnitToFiniteS, MonoidHom.comp_apply, Subgroup.subtype_apply,
      map_mul] using hu⟩

/-- Two allowed elements which differ by an S-unit differ by the sixth power of an S-unit. -/
theorem exists_sUnit_pow_six_of_isAllowed {a : Fˣ}
    {u : SUnitGroup (K := F) (sUnitSexticSupport F seed)}
    (ha : A.IsAllowed a) (hua : A.IsAllowed ((u : Fˣ) * a)) :
    ∃ t : SUnitGroup (K := F) (sUnitSexticSupport F seed), t ^ 6 = u := by
  let S := sUnitSexticSupport F seed
  have hinj := sUnitToFiniteS_powerClass_injective F S 6
    (sUnitPowerLocalization_injective_on_kummerNormSupport F _ 6 hmu6)
  have hB : IsCompl ((powerClassMk _ 6).comp (sUnitToFiniteS F S)).range A.B := by
    rw [← powerClassMap_range]
    exact A.isCompl
  apply exists_unit_power_of_allowed (sUnitToFiniteS F S) 6 hinj hB ha
  simpa only [IsAllowed, sUnitToFiniteS, MonoidHom.comp_apply, Subgroup.subtype_apply,
    map_mul] using hua

end AllowedClasses

/-- The canonical sextic Hilbert symbol at a place outside `S`, and `1` at the places of `S`. -/
def exteriorSymbol (v : HeightOneSpectrum (𝓞 F)) (a b : Fˣ) : rootsOfUnity ((6 : ℕ+) : ℕ) F :=
  open Classical in
  if v ∈ sUnitSexticSupport F seed then 1
  else GlobalHilbertPairingFamily.finiteFactor F (canonicalHilbertFamily F 6 hmu6) hmu6 v a b

variable {F seed}

omit [IsTotallyComplex F] in
theorem exteriorSymbol_of_mem {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ sUnitSexticSupport F seed)
    (a b : Fˣ) : exteriorSymbol F seed hmu6 v a b = 1 := by
  simp [exteriorSymbol, hv]

omit [IsTotallyComplex F] in
theorem exteriorSymbol_of_notMem {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ sUnitSexticSupport F seed) (a b : Fˣ) :
    exteriorSymbol F seed hmu6 v a b =
      GlobalHilbertPairingFamily.finiteFactor F (canonicalHilbertFamily F 6 hmu6) hmu6 v a b := by
  simp [exteriorSymbol, hv]

omit [IsTotallyComplex F] in
/-- The exterior symbol is multiplicative in its first argument. -/
theorem exteriorSymbol_mul_left (v : HeightOneSpectrum (𝓞 F)) (a a' b : Fˣ) :
    exteriorSymbol F seed hmu6 v (a * a') b =
      exteriorSymbol F seed hmu6 v a b * exteriorSymbol F seed hmu6 v a' b := by
  by_cases hv : v ∈ sUnitSexticSupport F seed
  · simp [exteriorSymbol_of_mem hmu6 hv]
  · simp only [exteriorSymbol_of_notMem hmu6 hv, finiteFactor_mul_left]

omit [IsTotallyComplex F] in
/-- The exterior symbol is multiplicative in its second argument. -/
theorem exteriorSymbol_mul_right (v : HeightOneSpectrum (𝓞 F)) (a b b' : Fˣ) :
    exteriorSymbol F seed hmu6 v a (b * b') =
      exteriorSymbol F seed hmu6 v a b * exteriorSymbol F seed hmu6 v a b' := by
  by_cases hv : v ∈ sUnitSexticSupport F seed
  · simp [exteriorSymbol_of_mem hmu6 hv]
  · simp only [exteriorSymbol_of_notMem hmu6 hv, finiteFactor_mul_right]

omit [IsTotallyComplex F] in
/-- The exterior symbol is skew-symmetric. -/
theorem exteriorSymbol_swap (v : HeightOneSpectrum (𝓞 F)) (a b : Fˣ) :
    exteriorSymbol F seed hmu6 v a b = (exteriorSymbol F seed hmu6 v b a)⁻¹ := by
  by_cases hv : v ∈ sUnitSexticSupport F seed
  · simp [exteriorSymbol_of_mem hmu6 hv]
  · rw [exteriorSymbol_of_notMem hmu6 hv, exteriorSymbol_of_notMem hmu6 hv]
    exact finiteFactor_swap (canonicalHilbertFamily F 6 hmu6) hmu6 v
      ((canonicalHilbertFamily_isCoherent F 6 hmu6).1 v).2.1 a b

omit [IsTotallyComplex F] in
/-- The exterior symbol of two elements which are units at the place is one. -/
theorem exteriorSymbol_eq_one_of_valuation_eq_one (v : HeightOneSpectrum (𝓞 F)) {a b : Fˣ}
    (ha : v.valuation F (a : F) = 1) (hb : v.valuation F (b : F) = 1) :
    exteriorSymbol F seed hmu6 v a b = 1 := by
  by_cases hv : v ∈ sUnitSexticSupport F seed
  · exact exteriorSymbol_of_mem hmu6 hv a b
  · rw [exteriorSymbol_of_notMem hmu6 hv]
    exact hilbertFiniteFactor_eq_one_of_valuation_eq_one F 6 hmu6 _
      (canonicalHilbertFamily_isCoherent F 6 hmu6).1 v a b
      (valuation_natCast_eq_one_of_not_mem_sUnitKummerNormSupport 6 _ hv) ha hb

omit [IsTotallyComplex F] in
/-- The exterior symbols of two nonzero elements are one at all but finitely many places. -/
theorem hasFiniteMulSupport_exteriorSymbol (a b : Fˣ) :
    Function.HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      exteriorSymbol F seed hmu6 v a b := by
  have h := (canonicalHilbertFamily_isCoherent F 6 hmu6).2.1 a b
  refine Set.Finite.subset h fun v hv => ?_
  by_cases hvS : v ∈ sUnitSexticSupport F seed
  · exact absurd (exteriorSymbol_of_mem hmu6 hvS a b) hv
  · rwa [Function.mem_mulSupport, exteriorSymbol_of_notMem hmu6 hvS] at hv

/-- **The Hilbert product formula, split at `S`**: the product of the canonical symbols at the
places of `S` times the product of the exterior symbols is one. -/
theorem sProd_mul_finprod_exteriorSymbol (a b : Fˣ) :
    (∏ v ∈ sUnitSexticSupport F seed,
        GlobalHilbertPairingFamily.finiteFactor F (canonicalHilbertFamily F 6 hmu6) hmu6 v a b) *
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), exteriorSymbol F seed hmu6 v a b = 1 := by
  classical
  let S := sUnitSexticSupport F seed
  let f : HeightOneSpectrum (𝓞 F) → rootsOfUnity ((6 : ℕ+) : ℕ) F := fun v =>
    GlobalHilbertPairingFamily.finiteFactor F (canonicalHilbertFamily F 6 hmu6) hmu6 v a b
  let g : HeightOneSpectrum (𝓞 F) → rootsOfUnity ((6 : ℕ+) : ℕ) F := fun v =>
    if v ∈ S then f v else 1
  have hcoh := canonicalHilbertFamily_isCoherent F 6 hmu6
  have hformula := hcoh.2.2 a b
  simp only [hilbertInfiniteFactor_eq_one, Finset.prod_const_one, one_mul] at hformula
  have hgS : Function.mulSupport g ⊆ (S : Set (HeightOneSpectrum (𝓞 F))) := by
    intro v hv
    by_contra hvS
    have hvS' : v ∉ S := fun h => hvS (Finset.mem_coe.mpr h)
    exact hv (by simp [g, hvS'])
  have hg : Function.HasFiniteMulSupport g := S.finite_toSet.subset hgS
  have hsplit : ∀ v, f v = g v * exteriorSymbol F seed hmu6 v a b := by
    intro v
    by_cases hv : v ∈ S
    · simp [g, hv, exteriorSymbol_of_mem hmu6 hv]
    · simp [g, hv, f, exteriorSymbol_of_notMem hmu6 hv]
  have hprod : ∏ᶠ v, g v = ∏ v ∈ S, f v := by
    rw [finprod_eq_prod_of_mulSupport_subset g hgS]
    exact Finset.prod_congr rfl fun v hv => by simp [g, hv]
  have hmain : ∏ᶠ v, g v * exteriorSymbol F seed hmu6 v a b =
      (∏ v ∈ S, f v) * ∏ᶠ v, exteriorSymbol F seed hmu6 v a b := by
    rw [finprod_mul_distrib hg (hasFiniteMulSupport_exteriorSymbol hmu6 a b), hprod]
  have hfg : ∏ᶠ v, f v = ∏ᶠ v, g v * exteriorSymbol F seed hmu6 v a b :=
    finprod_congr hsplit
  rw [← hmain, ← hfg]
  exact hformula

/-- **The exterior product formula for allowed generators** ([A] `A-02:0263–0267`): the symbols at
`S` multiply to one because `B` is isotropic, so the exterior symbols multiply to one. -/
theorem finprod_exteriorSymbol_eq_one (A : AllowedClasses F seed hmu6) {a b : Fˣ}
    (ha : A.IsAllowed a) (hb : A.IsAllowed b) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), exteriorSymbol F seed hmu6 v a b = 1 := by
  have h := sProd_mul_finprod_exteriorSymbol hmu6 (seed := seed) a b
  have hS := A.isotropic _ ha _ hb
  change sexticSPairing F seed hmu6 (sexticSClass F seed a) (sexticSClass F seed b) = 1 at hS
  rw [sexticSPairing_sexticSClass] at hS
  rwa [hS, one_mul] at h

/-- **[A] `eq:unit-symbol`**: for any two nonzero elements, the exterior symbols multiply to the
inverse of the `S`-pairing of their classes. For an S-unit `ε` and a generator `a`, the left side
is the residue character of `ε` at the ideal of `a`. -/
theorem finprod_exteriorSymbol_eq_inv_sexticSPairing (a b : Fˣ) :
    ∏ᶠ v : HeightOneSpectrum (𝓞 F), exteriorSymbol F seed hmu6 v a b =
      (sexticSPairing F seed hmu6 (sexticSClass F seed a) (sexticSClass F seed b))⁻¹ := by
  have h := sProd_mul_finprod_exteriorSymbol hmu6 (seed := seed) a b
  rw [← sexticSPairing_sexticSClass] at h
  exact eq_inv_of_mul_eq_one_right h

/-- **Sextic reciprocity with no supplementary factor** ([A] `eq:sextic-reciprocity`, in terms of
the exterior Hilbert symbols). Let `a`, `b` be allowed, with `a` a unit at every exterior place
other than `p` and `b` a unit at every exterior place other than `p'`, where `p ≠ p'`. Then the
symbol of `(a, b)` at `p` equals the symbol of `(b, a)` at `p'`. -/
theorem exteriorSymbol_reciprocity (A : AllowedClasses F seed hmu6) {a b : Fˣ}
    (ha : A.IsAllowed a) (hb : A.IsAllowed b) {p p' : HeightOneSpectrum (𝓞 F)} (hpp' : p ≠ p')
    (hap : ∀ v ∉ sUnitSexticSupport F seed, v ≠ p → v.valuation F (a : F) = 1)
    (hbp : ∀ v ∉ sUnitSexticSupport F seed, v ≠ p' → v.valuation F (b : F) = 1) :
    exteriorSymbol F seed hmu6 p a b = exteriorSymbol F seed hmu6 p' b a := by
  classical
  have h := finprod_exteriorSymbol_eq_one hmu6 A ha hb
  have hsupp : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) =>
      exteriorSymbol F seed hmu6 v a b) ⊆ (({p, p'} : Finset (HeightOneSpectrum (𝓞 F))) : Set _) := by
    intro v hv
    by_contra hvpp
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff, not_or] at hvpp
    by_cases hvS : v ∈ sUnitSexticSupport F seed
    · exact hv (exteriorSymbol_of_mem hmu6 hvS a b)
    · exact hv (exteriorSymbol_eq_one_of_valuation_eq_one hmu6 v
        (hap v hvS hvpp.1) (hbp v hvS hvpp.2))
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp, Finset.prod_pair hpp'] at h
  rw [exteriorSymbol_swap hmu6 p' b a]
  exact eq_inv_of_mul_eq_one_left h

end SimultaneousPrimitiveRoots.Unconditional.CFTBridge
