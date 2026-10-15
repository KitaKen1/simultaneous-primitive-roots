import SimultaneousPrimitiveRootsFinal.SUnitCommonSupport
import SimultaneousPrimitiveRoots.Unconditional.Arithmetic.SexticPairingRestriction
import SimultaneousPrimitiveRoots.Unconditional.Arithmetic.AllowedGenerators

/-!
# Sextic Hilbert preparation on one actual support

One coherent sextic Hilbert family supplies both prime components, so their
normalizations agree by construction. CFT supplies all cardinality, isotropy
and localization-injectivity inputs. The only field hypothesis is the presence
of twelfth roots of unity (and total complexity, as required by the route).
-/

noncomputable section
-- CFT's power-class abbreviation and the generic quotient expose definitionally
-- equal group instances through different paths. Let elaboration unfold those
-- paths; every resulting proof is still checked by the Lean kernel.
set_option backward.isDefEq.respectTransparency false
namespace SimultaneousPrimitiveRoots.Unconditional.CFTBridge
open ClassFieldTheory Arithmetic NumberField IsDedekindDomain
open GlobalClassFieldTheory.GlobalClassFields
open scoped NumberField

variable (F : Type) [Field F] [NumberField F] [IsTotallyComplex F]

/-- One support contains the sufficient supports for exponents six, two, and three. -/
def sUnitSexticSupport (seed : Finset (HeightOneSpectrum (𝓞 F))) :=
  sUnitKummerNormSupport (K := F) 6
    (sUnitKummerNormSupport (K := F) 2 (sUnitKummerNormSupport (K := F) 3 seed))

theorem sUnitSexticSupport_two (seed : Finset (HeightOneSpectrum (𝓞 F))) :
    sUnitSexticSupport F seed = sUnitKummerNormSupport (K := F) 2
      (sUnitKummerNormSupport (K := F) 6 (sUnitKummerNormSupport (K := F) 3 seed)) :=
  sUnitKummerNormSupport_comm F _ 6 2

theorem sUnitSexticSupport_three (seed : Finset (HeightOneSpectrum (𝓞 F))) :
    sUnitSexticSupport F seed = sUnitKummerNormSupport (K := F) 3
      (sUnitKummerNormSupport (K := F) 2 (sUnitKummerNormSupport (K := F) 6 seed)) := by
  unfold sUnitSexticSupport
  rw [sUnitKummerNormSupport_comm F seed 2 3,
    sUnitKummerNormSupport_comm F _ 6 3,
    sUnitKummerNormSupport_comm F seed 6 2]

/-- Every idele has an actual field generator for its valuations outside the support. -/
theorem exists_exterior_field_generator (seed : Finset (HeightOneSpectrum (𝓞 F)))
    (c : IdeleGroup F) :
    ∃ a : Fˣ, c / IdeleGroup.principalIdele F a ∈
      IdeleGroup.supportedAt (K := F) (sUnitSexticSupport F seed : Set _) := by
  have hc : c ∈ IdeleGroup.supportedAt (K := F) (sUnitSexticSupport F seed : Set _) ⊔
      IdeleGroup.principalSubgroup F := by
    rw [sUnitSexticSupport, supportedAt_sUnitKummerNormSupport_sup_principalSubgroup_eq_top]
    trivial
  obtain ⟨b, hb, p, hp, hbp⟩ := Subgroup.mem_sup.mp hc
  obtain ⟨a, rfl⟩ := hp
  exact ⟨a, by simpa only [← hbp, mul_div_cancel_right] using hb⟩

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

/-- The actual principal idele is supported on S precisely for an S-unit. -/
theorem principal_mem_supportedAt_iff_sUnit (a : Fˣ) :
    IdeleGroup.principalIdele F a ∈ IdeleGroup.supportedAt (K := F) (S : Set _) ↔
      a ∈ SUnitGroup (K := F) S := by
  rw [IdeleGroup.mem_supportedAt_iff, mem_SUnitGroup_iff]
  constructor <;> intro h v hv
  · have h := h v hv
    change IdeleGroup.finiteComponent v (IdeleGroup.principalIdele F a) ∈
      (v.adicCompletionIntegers F).units at h
    rwa [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
      IdeleGroup.finiteComponent_principalIdele,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  · change IdeleGroup.finiteComponent v (IdeleGroup.principalIdele F a) ∈
      (v.adicCompletionIntegers F).units
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one,
      IdeleGroup.finiteComponent_principalIdele,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact h v hv

/-- Multiplication by an actual S-unit keeps the exterior valuation data. -/
theorem sUnit_principal_mem_supportedAt (u : SUnitGroup (K := F) S) :
    IdeleGroup.principalIdele F (u : Fˣ) ∈ IdeleGroup.supportedAt (K := F) (S : Set _) :=
  (principal_mem_supportedAt_iff_sUnit F S (u : Fˣ)).mpr u.property

/-- Two generators of the same exterior valuation data differ by an actual S-unit. -/
theorem exterior_generator_ratio_mem_sUnit (c : IdeleGroup F) (a b : Fˣ)
    (ha : c / IdeleGroup.principalIdele F a ∈ IdeleGroup.supportedAt (K := F) (S : Set _))
    (hb : c / IdeleGroup.principalIdele F b ∈ IdeleGroup.supportedAt (K := F) (S : Set _)) :
    a / b ∈ SUnitGroup (K := F) S := by
  apply (principal_mem_supportedAt_iff_sUnit F S (a / b)).mp
  have h := (IdeleGroup.supportedAt (K := F) (S : Set _)).div_mem hb ha
  convert h using 1
  rw [map_div]
  exact (div_div_div_cancel_left _ _ _).symm

/-- CRT of the actual product of local power-class groups. -/
def sLocalSexticCrt :
    (∀ v : S, PowerClassGroup (v.1.adicCompletion F) 6) ≃*
      (∀ v : S, PowerClassGroup (v.1.adicCompletion F) 2) ×
      (∀ v : S, PowerClassGroup (v.1.adicCompletion F) 3) :=
  (powerClassPiEquiv (fun v : S => (v.1.adicCompletion F)ˣ) 6).symm.trans
    ((sexticClassEquiv (∀ v : S, (v.1.adicCompletion F)ˣ)).trans
      ((powerClassPiEquiv (fun v : S => (v.1.adicCompletion F)ˣ) 2).prodCongr
        (powerClassPiEquiv (fun v : S => (v.1.adicCompletion F)ˣ) 3)))

theorem sLocalSexticCrt_localization (u : PowerClass (SUnitGroup (K := F) S) 6) :
    sLocalSexticCrt F S (sUnitPowerLocalization F S 6 u) =
      (sUnitPowerLocalization F S 2 (sexticClassEquiv (SUnitGroup (K := F) S) u).1,
        sUnitPowerLocalization F S 3 (sexticClassEquiv (SUnitGroup (K := F) S) u).2) := by
  obtain ⟨a, rfl⟩ := powerClassMk_surjective _ 6 u
  let t : ∀ v : S, (v.1.adicCompletion F)ˣ := fun v =>
    Units.map (algebraMap F (v.1.adicCompletion F)).toMonoidHom (a : Fˣ)
  have hpi : sUnitPowerLocalization F S 6 (powerClassMk _ 6 a) =
      powerClassPiEquiv (fun v : S => (v.1.adicCompletion F)ˣ) 6
        (powerClassMk _ 6 t) := rfl
  rw [hpi]
  dsimp only [sLocalSexticCrt, MulEquiv.trans_apply]
  erw [MulEquiv.symm_apply_apply, sexticClassEquiv_mk]
  rfl

/-- The image uses the same S-units at all places and becomes a product only after CRT. -/
theorem sLocalSexticCrt_map_range :
    (sUnitPowerLocalization F S 6).range.map (sLocalSexticCrt F S).toMonoidHom =
      (sUnitPowerLocalization F S 2).range.prod (sUnitPowerLocalization F S 3).range := by
  ext x
  constructor
  · rintro ⟨a, ⟨u, rfl⟩, rfl⟩
    change sLocalSexticCrt F S (sUnitPowerLocalization F S 6 u) ∈ _
    rw [sLocalSexticCrt_localization F S u]
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · rintro ⟨⟨u₂, hu₂⟩, ⟨u₃, hu₃⟩⟩
    obtain ⟨u, hu⟩ := (sexticClassEquiv (SUnitGroup (K := F) S)).surjective (u₂, u₃)
    refine ⟨sUnitPowerLocalization F S 6 u, ⟨u, rfl⟩, ?_⟩
    change sLocalSexticCrt F S (sUnitPowerLocalization F S 6 u) = x
    rw [sLocalSexticCrt_localization F S u, hu]
    exact Prod.ext hu₂ hu₃

/-- All prime-component hypotheses are discharged for one coherent sextic family. -/
theorem exists_sUnit_sextic_hilbert_preparation
    (seed : Finset (HeightOneSpectrum (𝓞 F)))
    (hmu12 : (primitiveRoots 12 F).Nonempty) :
    let S := sUnitSexticSupport F seed
    ∃ hmu6 : (primitiveRoots 6 F).Nonempty,
      ∃ B : GlobalHilbertPairingFamily F 6,
        IsCoherentHilbertFamily F 6 hmu6 B ∧
        Function.Injective (sUnitPowerLocalization F S 6) ∧
        (∀ x, (∀ y ∈ (sUnitPowerLocalization F S 6).range,
          piPairing (fun v : S => finitePlaceGlobalRootPairing F 6 hmu6 B v) x y = 1) →
          x ∈ (sUnitPowerLocalization F S 6).range) ∧
        ∃ C : Subgroup (∀ v : S, PowerClassGroup (v.1.adicCompletion F) 6),
          IsCompl (sUnitPowerLocalization F S 6).range C ∧
          ∀ x ∈ C, ∀ y ∈ C,
            piPairing (fun v : S => finitePlaceGlobalRootPairing F 6 hmu6 B v) x y = 1 := by
  classical
  dsimp only
  let S := sUnitSexticSupport F seed
  have hmu6 := primitiveRoots_nonempty_of_dvd (K := F) 6 (by decide : 0 < 12)
    (by decide : 6 ∣ 12) hmu12
  have hmu2 := primitiveRoots_nonempty_of_dvd (K := F) 2 (by decide : 0 < 12)
    (by decide : 2 ∣ 12) hmu12
  have hmu3 := primitiveRoots_nonempty_of_dvd (K := F) 3 (by decide : 0 < 12)
    (by decide : 3 ∣ 12) hmu12
  obtain ⟨B, hcoherent, hiso⟩ := exists_sUnit_hilbert_isotropic F S 6 hmu6
    (fun v hv => valuation_natCast_eq_one_of_not_mem_sUnitKummerNormSupport 6 _ hv)
  let H := piPairing (fun v : S => finitePlaceGlobalRootPairing F 6 hmu6 B v)
  have hnd : ∀ x, (∀ y, H x y = 1) → x = 1 :=
    piPairing_nondegenerate _ (fun v => commonRootPairing_nondegenerate _ (B v.1)
      (hcoherent.1 v.1).2.2.1)
  obtain ⟨u, hu⟩ := minus_one_is_power_of_double_roots (K := F) 6 hmu12
  have halt : ∀ x, H x x = 1 := by
    apply piPairing_alternating
    intro v x
    let w := Units.map (algebraMap F (v.1.adicCompletion F)).toMonoidHom u
    have hw : w ^ (6 : ℕ) = -1 := by
      have hu' : u ^ (6 : ℕ) = -1 := hu
      rw [← map_pow, hu']
      apply Units.ext
      simp
    have hi := hilbertPairing_isAlt_of_minus_one_is_power (B v.1)
      (hcoherent.1 v.1).1 ⟨w, hw⟩ x
    change commonRootPairing _ (B v.1) x x = 1
    rw [commonRootPairing_apply, hi, map_one]
  have hcard2 : Nat.card (sUnitPowerLocalization F S 2).range ^ 2 =
      Nat.card (∀ v : S, PowerClassGroup (v.1.adicCompletion F) 2) := by
    let P (T : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
      Nat.card (sUnitPowerLocalization F T 2).range ^ 2 =
        Nat.card (∀ v : T, PowerClassGroup (v.1.adicCompletion F) 2)
    have h := sUnitPowerLocalization_card_sq_on_kummerNormSupport F
      (sUnitKummerNormSupport (K := F) 6 (sUnitKummerNormSupport (K := F) 3 seed)) 2 hmu2
    exact (congrArg P (sUnitSexticSupport_two F seed).symm).mp h
  have hcard3 : Nat.card (sUnitPowerLocalization F S 3).range ^ 2 =
      Nat.card (∀ v : S, PowerClassGroup (v.1.adicCompletion F) 3) := by
    let P (T : Finset (HeightOneSpectrum (𝓞 F))) : Prop :=
      Nat.card (sUnitPowerLocalization F T 3).range ^ 2 =
        Nat.card (∀ v : T, PowerClassGroup (v.1.adicCompletion F) 3)
    have h := sUnitPowerLocalization_card_sq_on_kummerNormSupport F
      (sUnitKummerNormSupport (K := F) 2 (sUnitKummerNormSupport (K := F) 6 seed)) 3 hmu3
    exact (congrArg P (sUnitSexticSupport_three F seed).symm).mp h
  let : ∀ v : S, ValuativeRel (v.1.adicCompletion F) := fun v =>
    finitePlaceCompletionValuativeRel F v.1
  let : ∀ v : S, IsNonarchimedeanLocalField (v.1.adicCompletion F) := fun v =>
    finitePlaceCompletionIsNonarchimedeanLocalField F v.1
  let : ∀ v : S, Finite (PowerClassGroup (v.1.adicCompletion F) 2) := fun v =>
    powerClassGroup_finite _ 2 (Nat.cast_ne_zero.mpr (by decide : (2 : ℕ) ≠ 0))
  let : ∀ v : S, Finite (PowerClassGroup (v.1.adicCompletion F) 3) := fun v =>
    powerClassGroup_finite _ 3 (Nat.cast_ne_zero.mpr (by decide : (3 : ℕ) ≠ 0))
  obtain ⟨hself, C, hC, hCI⟩ := exists_sextic_compl_of_one_pairing (sLocalSexticCrt F S) H
    (fun x => funext fun v => powerClass_pow_eq_one (v.1.adicCompletion F)ˣ 2 (x v))
    (fun x => funext fun v => powerClass_pow_eq_one (v.1.adicCompletion F)ˣ 3 (x v))
    (rootsOfUnityZModEquiv 2 hmu2) (rootsOfUnityZModEquiv 3 hmu3)
    hnd halt (sLocalSexticCrt_map_range F S) hiso hcard2 hcard3
  exact ⟨hmu6, B, hcoherent,
    sUnitPowerLocalization_injective_on_kummerNormSupport F _ 6 hmu6,
    hself, C, hC, hCI⟩

/-- The finite part of a field element, as a joint tuple of local units. -/
def fieldToFiniteS : Fˣ →* ∀ v : S, (v.1.adicCompletion F)ˣ :=
  MonoidHom.pi fun v : S => Units.map (algebraMap F (v.1.adicCompletion F)).toMonoidHom

def sUnitToFiniteS : SUnitGroup (K := F) S →* ∀ v : S, (v.1.adicCompletion F)ˣ :=
  (fieldToFiniteS F S).comp (SUnitGroup (K := F) S).subtype

theorem powerClassPiEquiv_sUnitToFiniteS (n : ℕ+) (q : PowerClass (SUnitGroup (K := F) S) n) :
    powerClassPiEquiv (fun v : S => (v.1.adicCompletion F)ˣ) n
      (powerClassMap (sUnitToFiniteS F S) n q) = sUnitPowerLocalization F S n q := by
  obtain ⟨u, rfl⟩ := powerClassMk_surjective _ n q
  rfl

theorem sUnitToFiniteS_powerClass_injective (n : ℕ+)
    (hinj : Function.Injective (sUnitPowerLocalization F S n)) :
    Function.Injective (powerClassMap (sUnitToFiniteS F S) n) := by
  intro x y h
  apply hinj
  rw [← powerClassPiEquiv_sUnitToFiniteS, ← powerClassPiEquiv_sUnitToFiniteS, h]

theorem sUnitToFiniteS_range_comap (n : ℕ+) :
    (powerClassPiEquiv (fun v : S => (v.1.adicCompletion F)ˣ) n).comapSubgroup
      (sUnitPowerLocalization F S n).range =
      (powerClassMap (sUnitToFiniteS F S) n).range := by
  ext q
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u, ?_⟩
    apply (powerClassPiEquiv (fun v : S => (v.1.adicCompletion F)ˣ) n).injective
    rw [powerClassPiEquiv_sUnitToFiniteS]
    exact hu
  · rintro ⟨u, rfl⟩
    exact ⟨u, powerClassPiEquiv_sUnitToFiniteS F S n u |>.symm⟩

/-- **Actual generators can be adjusted to an isotropic allowed class, uniquely modulo U_S^6.** -/
theorem exists_allowed_sextic_generators
    (seed : Finset (HeightOneSpectrum (𝓞 F)))
    (hmu12 : (primitiveRoots 12 F).Nonempty) :
    let S := sUnitSexticSupport F seed
    ∃ hmu6 : (primitiveRoots 6 F).Nonempty,
      ∃ H : GlobalHilbertPairingFamily F 6,
        IsCoherentHilbertFamily F 6 hmu6 H ∧
        ∃ B : Subgroup (PowerClass (∀ v : S, (v.1.adicCompletion F)ˣ) 6),
          IsCompl (powerClassMap (sUnitToFiniteS F S) 6).range B ∧
          (∀ x ∈ B, ∀ y ∈ B,
            piPairing (fun v : S => finitePlaceGlobalRootPairing F 6 hmu6 H v)
              (powerClassPiEquiv (fun v : S => (v.1.adicCompletion F)ˣ) 6 x)
              (powerClassPiEquiv (fun v : S => (v.1.adicCompletion F)ˣ) 6 y) = 1) ∧
          (∀ a : Fˣ, ∃ u : SUnitGroup (K := F) S,
            powerClassMk _ 6 (fieldToFiniteS F S ((u : Fˣ) * a)) ∈ B) ∧
          (∀ (a : Fˣ) (u : SUnitGroup (K := F) S),
            powerClassMk _ 6 (fieldToFiniteS F S a) ∈ B →
            powerClassMk _ 6 (fieldToFiniteS F S ((u : Fˣ) * a)) ∈ B →
            ∃ t : SUnitGroup (K := F) S, t ^ 6 = u) := by
  classical
  dsimp only
  let S := sUnitSexticSupport F seed
  obtain ⟨hmu6, H, hcoherent, hinj, hself, C, hC, hCI⟩ :=
    exists_sUnit_sextic_hilbert_preparation F seed hmu12
  let e := powerClassPiEquiv (fun v : S => (v.1.adicCompletion F)ˣ) 6
  let B := e.comapSubgroup C
  have hB : IsCompl (powerClassMap (sUnitToFiniteS F S) 6).range B := by
    have h := e.comapSubgroup.isCompl hC
    have he : e.comapSubgroup (sUnitPowerLocalization F S 6).range =
        (powerClassMap (sUnitToFiniteS F S) 6).range :=
      sUnitToFiniteS_range_comap F S 6
    exact (congrArg (fun E => IsCompl E B) he).mp h
  have hinj6 := sUnitToFiniteS_powerClass_injective F S 6 hinj
  have hnorm := exists_unit_adjusted_allowed (sUnitToFiniteS F S)
    (powerClassMk _ 6) (B := B) (by rwa [← powerClassMap_range])
  refine ⟨hmu6, H, hcoherent, B, hB, fun x hx y hy => hCI _ hx _ hy, ?_, ?_⟩
  · intro a
    obtain ⟨u, hu⟩ := hnorm (fieldToFiniteS F S a)
    exact ⟨u, by simpa only [sUnitToFiniteS, MonoidHom.comp_apply, Subgroup.subtype_apply,
      map_mul] using hu⟩
  · intro a u ha hua
    apply exists_unit_power_of_allowed (sUnitToFiniteS F S) 6 hinj6
      (by rwa [← powerClassMap_range]) ha
    simpa only [sUnitToFiniteS, MonoidHom.comp_apply, Subgroup.subtype_apply, map_mul] using hua

/-- The allowed normalization applies to arbitrary exterior idele valuation data. -/
theorem exists_allowed_exterior_generator
    (seed : Finset (HeightOneSpectrum (𝓞 F)))
    {B : Subgroup (PowerClass (∀ v : sUnitSexticSupport F seed,
      (v.1.adicCompletion F)ˣ) 6)}
    (hB : IsCompl (powerClassMap (sUnitToFiniteS F (sUnitSexticSupport F seed)) 6).range B)
    (c : IdeleGroup F) :
    ∃ a : Fˣ, c / IdeleGroup.principalIdele F a ∈
      IdeleGroup.supportedAt (K := F) (sUnitSexticSupport F seed : Set _) ∧
      powerClassMk _ 6 (fieldToFiniteS F (sUnitSexticSupport F seed) a) ∈ B := by
  let S := sUnitSexticSupport F seed
  obtain ⟨a, ha⟩ := exists_exterior_field_generator F seed c
  obtain ⟨u, hu⟩ := exists_unit_adjusted_allowed (sUnitToFiniteS F S) (powerClassMk _ 6)
    (B := B) (by rwa [← powerClassMap_range]) (fieldToFiniteS F S a)
  refine ⟨(u : Fˣ) * a, ?_, ?_⟩
  · have h := (IdeleGroup.supportedAt (K := F) (S : Set _)).mul_mem ha
      ((IdeleGroup.supportedAt (K := F) (S : Set _)).inv_mem
        (sUnit_principal_mem_supportedAt F S u))
    convert h using 1
    rw [map_mul]
    simp only [div_eq_mul_inv, mul_inv_rev, mul_assoc]
  · simpa only [sUnitToFiniteS, MonoidHom.comp_apply, Subgroup.subtype_apply, map_mul] using hu

/-- Allowed generators of the same exterior data are unique modulo actual U_S^6. -/
theorem allowed_exterior_generators_unique_mod_six
    (seed : Finset (HeightOneSpectrum (𝓞 F))) (hmu6 : (primitiveRoots 6 F).Nonempty)
    {B : Subgroup (PowerClass (∀ v : sUnitSexticSupport F seed,
      (v.1.adicCompletion F)ˣ) 6)}
    (hB : IsCompl (powerClassMap (sUnitToFiniteS F (sUnitSexticSupport F seed)) 6).range B)
    (c : IdeleGroup F) (a b : Fˣ)
    (ha : c / IdeleGroup.principalIdele F a ∈
      IdeleGroup.supportedAt (K := F) (sUnitSexticSupport F seed : Set _))
    (hb : c / IdeleGroup.principalIdele F b ∈
      IdeleGroup.supportedAt (K := F) (sUnitSexticSupport F seed : Set _))
    (haB : powerClassMk _ 6 (fieldToFiniteS F (sUnitSexticSupport F seed) a) ∈ B)
    (hbB : powerClassMk _ 6 (fieldToFiniteS F (sUnitSexticSupport F seed) b) ∈ B) :
    ∃ t : SUnitGroup (K := F) (sUnitSexticSupport F seed), (t : Fˣ) ^ 6 * b = a := by
  let S := sUnitSexticSupport F seed
  let u : SUnitGroup (K := F) S := ⟨a / b, exterior_generator_ratio_mem_sUnit F S c a b ha hb⟩
  have hinj := sUnitToFiniteS_powerClass_injective F S 6
    (sUnitPowerLocalization_injective_on_kummerNormSupport F _ 6 hmu6)
  have hua : (u : Fˣ) * b = a := div_mul_cancel a b
  have huB : powerClassMk _ 6 (sUnitToFiniteS F S u * fieldToFiniteS F S b) ∈ B := by
    change powerClassMk _ 6 (fieldToFiniteS F S (u : Fˣ) * fieldToFiniteS F S b) ∈ B
    rw [← map_mul, hua]
    exact haB
  obtain ⟨t, ht⟩ := exists_unit_power_of_allowed (sUnitToFiniteS F S) 6 hinj
    (by rwa [← powerClassMap_range]) hbB huB
  refine ⟨t, ?_⟩
  have htf : (t : Fˣ) ^ 6 = (u : Fˣ) := congrArg (fun v : SUnitGroup (K := F) S => (v : Fˣ)) ht
  rw [htf, hua]

end SimultaneousPrimitiveRoots.Unconditional.CFTBridge

