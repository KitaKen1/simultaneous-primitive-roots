import ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianReciprocityData
import SimultaneousPrimitiveRoots.Unconditional.ArtinDescent

/-!
# Class field theory gives Artin data through a TauCeti ray class group (step Z3)

ClassFieldTheory's `FiniteAbelianReciprocityData K L` carries a ray modulus `m` and an Artin map
`RayClassGroup m →* Gal(L/K)` sending the class of a prime `v ∤ m` to an arithmetic Frobenius
above `v`. Its ray class group lives on the same carrier `(FractionalIdeal (𝓞 K)⁰ K)ˣ` as
TauCeti's, but with its own modulus type and its own congruence condition (local higher units in
the completions).

Here we pass to TauCeti's ray class group of the dominating modulus `domModulus m`, with finite
part `(2) ∏_{v ∣ m} v ^ m(v)` and the same real places (`rayArtinDataOfReciprocity`):

* the ideals prime to `domModulus m` are prime to `m` (`mem_rayClassPrimeToIdeals`);
* an element congruent to one modulo `domModulus m` satisfies `m`'s ray congruence
  (`isRayCongruent_of_isCongrOne`), via the valuation criterion for local higher units
  (`finitePlaceUnitEmbedding_mem_rayLocalHigherUnitGroup`);
* so the Artin map descends to TauCeti's ray class group (`tauArtin`), sends the class of a prime
  `v ∤ domModulus m` to the Frobenius above `v` (`tauArtin_idealClass_prime`), and the Galois
  weights become ray class characters (`galoisCharacterWeight_eq_onIdeals_tauArtin`).

The factor `(2)` only keeps the finite part proper (`domModulus_finitePart_ne_top`), which the
analytic continuation of the ray class `L`-functions needs.

This file is not a `module`: ClassFieldTheory is not, and a module cannot import it.
-/

noncomputable section

namespace SimultaneousPrimitiveRoots.Unconditional.CFTBridge

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum TauCeti
  TauCeti.GlobalNumberFields
open scoped nonZeroDivisors IsMulCommutative

variable {K : Type*} [Field K] [NumberField K]

/-! ### Local higher units from valuations -/

/-- An integer of `K_v` of valuation at most `exp (-n)` lies in the `n`-th power of the maximal
ideal. -/
theorem mem_maximalIdeal_pow_of_valued_le (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (y : v.adicCompletionIntegers K)
    (hy : Valued.v (y : v.adicCompletion K) ≤ WithZero.exp (-(n : ℤ))) :
    y ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hϖv : Valued.v (π : v.adicCompletion K) = WithZero.exp (-1 : ℤ) := by
    rw [valuedAdicCompletion_eq_valuation', hπ]
  have hlt : WithZero.exp (-1 : ℤ) < 1 := by
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hϖmem : (π : v.adicCompletion K) ∈ v.adicCompletionIntegers K := by
    rw [mem_adicCompletionIntegers, hϖv]
    exact hlt.le
  let ϖ : v.adicCompletionIntegers K := ⟨_, hϖmem⟩
  have hϖ0 : (π : v.adicCompletion K) ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖv
    exact WithZero.exp_ne_zero hϖv.symm
  have hmax : ϖ ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      adicCompletionIntegers.isUnit_iff_valued_eq_one]
    show Valued.v (π : v.adicCompletion K) ≠ 1
    rw [hϖv]
    exact hlt.ne
  have hz : (y : v.adicCompletion K) * ((π : v.adicCompletion K) ^ n)⁻¹ ∈
      v.adicCompletionIntegers K := by
    rw [mem_adicCompletionIntegers, map_mul, map_inv₀, map_pow, hϖv, ← WithZero.exp_nsmul,
      ← WithZero.exp_neg]
    calc Valued.v (y : v.adicCompletion K) * WithZero.exp (-(n • (-1 : ℤ)))
        ≤ WithZero.exp (-(n : ℤ)) * WithZero.exp (-(n • (-1 : ℤ))) := mul_le_mul_left hy _
      _ = 1 := by
        rw [← WithZero.exp_add, ← WithZero.exp_zero]
        congr 1
        simp
  have hy' : y = ϖ ^ n * ⟨_, hz⟩ := by
    apply Subtype.ext
    simp only [ϖ, SubmonoidClass.coe_pow, MulMemClass.coe_mul]
    field_simp
  rw [hy']
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hmax n)

/-- **A global element congruent to one modulo `v ^ n` is a local higher unit of depth `n`**, for
`n > 0`. -/
theorem finitePlaceUnitEmbedding_mem_rayLocalHigherUnitGroup (v : HeightOneSpectrum (𝓞 K))
    {n : ℕ} (hn : 0 < n) (x : Kˣ)
    (hx : v.valuation K ((x : K) - 1) ≤ WithZero.exp (-(n : ℤ))) :
    ClassFieldTheory.finitePlaceUnitEmbedding v x ∈
      ClassFieldTheory.rayLocalHigherUnitGroup v n := by
  set y : (v.adicCompletion K)ˣ := ClassFieldTheory.finitePlaceUnitEmbedding v x with hydef
  have hsub : Valued.v ((y : v.adicCompletion K) - 1) ≤ WithZero.exp (-(n : ℤ)) := by
    have h : (y : v.adicCompletion K) - 1 = algebraMap K (v.adicCompletion K) ((x : K) - 1) := by
      rw [map_sub, map_one]
      rfl
    rw [h]
    exact (valuedAdicCompletion_eq_valuation' v ((x : K) - 1)).trans_le hx
  have hlt : Valued.v ((y : v.adicCompletion K) - 1) < 1 := by
    refine hsub.trans_lt ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  have hunit : Valued.v (y : v.adicCompletion K) = 1 := by
    have h := Valuation.map_one_add_of_lt Valued.v hlt
    rwa [add_sub_cancel] at h
  have hmem : y ∈ (v.adicCompletionIntegers K).units :=
    adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr hunit
  refine Subgroup.mem_map.mpr ⟨⟨y, hmem⟩, ?_, rfl⟩
  rw [MonoidHom.mem_ker, Units.ext_iff]
  show Ideal.Quotient.mk _ (⟨(y : v.adicCompletion K), hmem.1⟩ : v.adicCompletionIntegers K) =
    Ideal.Quotient.mk _ 1
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact mem_maximalIdeal_pow_of_valued_le v n _ hsub

/-! ### The dominating TauCeti modulus -/

/-- **The TauCeti modulus dominating a ray modulus `m` of ClassFieldTheory**: finite part
`(2) ∏_{v ∣ m} v ^ m(v)`, real places those of `m`. -/
def domModulus (m : ClassFieldTheory.RayClassModulus K) : Modulus K where
  finitePart := Ideal.span {((2 : ℕ) : 𝓞 K)} *
    ∏ v ∈ m.finitePart.support, v.asIdeal ^ m.finitePart v
  finitePart_ne_bot := by
    rw [ne_eq, ← Ideal.zero_eq_bot, mul_eq_zero, not_or]
    refine ⟨?_, Finset.prod_ne_zero_iff.mpr fun v _ => pow_ne_zero _ ?_⟩
    · rw [Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.mpr two_ne_zero
    · rw [Ideal.zero_eq_bot]
      exact v.ne_bot
  infinitePart := m.infinitePart

variable {m : ClassFieldTheory.RayClassModulus K}

/-- The finite part of the dominating modulus is proper. -/
theorem domModulus_finitePart_ne_top (m : ClassFieldTheory.RayClassModulus K) :
    (domModulus m).finitePart ≠ ⊤ := by
  intro h
  have h2 : Ideal.span {((2 : ℕ) : 𝓞 K)} = ⊤ := top_unique (h ▸ Ideal.mul_le_left)
  exact absurd (Ideal.span_singleton_natCast_eq_top_iff.mp h2) (by norm_num)

theorem domModulus_infinitePart (m : ClassFieldTheory.RayClassModulus K) :
    (domModulus m).infinitePart = m.infinitePart := rfl

theorem pow_dvd_domModulus {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ m.finitePart.support) :
    v.asIdeal ^ m.finitePart v ∣ (domModulus m).finitePart :=
  Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hv) _

theorem dvd_domModulus {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ m.finitePart.support) :
    v.asIdeal ∣ (domModulus m).finitePart :=
  (dvd_pow_self _ (Finsupp.mem_support_iff.mp hv)).trans (pow_dvd_domModulus hv)

theorem le_exponent_domModulus {v : HeightOneSpectrum (𝓞 K)} (hv : v ∈ m.finitePart.support) :
    m.finitePart v ≤ (domModulus m).exponent v :=
  (Modulus.pow_dvd_finitePart_iff_le_exponent _ v).mp (pow_dvd_domModulus hv)

theorem notMem_support_of_notMem_domModulus {v : HeightOneSpectrum (𝓞 K)}
    (hv : v ∉ (domModulus m).support) : v ∉ m.finitePart.support := fun h =>
  hv ((Modulus.mem_support_iff _ v).mpr (dvd_domModulus h))

theorem notMem_support_of_mem_integralIdealsPrimeTo {v : HeightOneSpectrum (𝓞 K)}
    (hv : v.asIdeal ∈ integralIdealsPrimeTo (domModulus m)) : v ∉ m.finitePart.support := by
  refine notMem_support_of_notMem_domModulus ?_
  have h := NumberFieldArithmetic.mem_integralIdealsAway_iff_isPrimeTo.mp hv
  simpa using Ideal.isPrimeTo_asIdeal_iff.mp h

/-- **Ideals prime to the dominating modulus are prime to `m`.** -/
theorem mem_rayClassPrimeToIdeals {I : (FractionalIdeal (𝓞 K)⁰ K)ˣ}
    (hI : I ∈ idealsPrimeTo (domModulus m)) : I ∈ ClassFieldTheory.rayClassPrimeToIdeals m :=
  fun v hv => NumberFieldArithmetic.mem_idealsAway_iff.mp hI v
    ((Modulus.mem_support_iff _ v).mpr (dvd_domModulus hv))

/-- **Congruence to one modulo the dominating modulus implies `m`'s ray congruence.** -/
theorem isRayCongruent_of_isCongrOne {x : Kˣ} (hx : IsCongrOne (domModulus m) x) :
    ClassFieldTheory.IsRayCongruent m x := by
  refine ⟨fun v hv => ?_, fun w hw => hx.pos hw⟩
  have hpos : 0 < m.finitePart v := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hv)
  refine finitePlaceUnitEmbedding_mem_rayLocalHigherUnitGroup v hpos x ?_
  refine (hx.valuation_sub_one_le (dvd_domModulus hv)).trans (WithZero.exp_le_exp.mpr ?_)
  exact neg_le_neg (Int.ofNat_le.mpr (le_exponent_domModulus hv))

/-! ### The Artin map on TauCeti's ray class group -/

variable (m) in
/-- The inclusion of the ideals prime to the dominating modulus into those prime to `m`. -/
def primeToInclusion :
    idealsPrimeTo (domModulus m) →* ClassFieldTheory.rayClassPrimeToIdeals m :=
  Subgroup.inclusion fun _ hI => mem_rayClassPrimeToIdeals hI

variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsAbelianGalois K L]

/-- The Artin map of the reciprocity data on the ideals prime to the dominating modulus. -/
def tauArtinHom (D : ClassFieldTheory.FiniteAbelianReciprocityData K L) :
    idealsPrimeTo (domModulus D.modulus) →* (L ≃ₐ[K] L) :=
  D.artin.comp ((QuotientGroup.mk' (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo
    D.modulus)).comp (primeToInclusion D.modulus))

theorem ray_le_ker_tauArtinHom (D : ClassFieldTheory.FiniteAbelianReciprocityData K L) :
    ray (domModulus D.modulus) ≤ (tauArtinHom D).ker := by
  intro I hI
  obtain ⟨x, hx, hxI⟩ := mem_ray_iff.mp hI
  have hmem : primeToInclusion D.modulus I ∈
      ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo D.modulus :=
    Subgroup.subset_closure ⟨x, isRayCongruent_of_isCongrOne hx, hxI⟩
  have h1 : QuotientGroup.mk' (ClassFieldTheory.rayPrincipalIdealSubgroupInPrimeTo D.modulus)
      (primeToInclusion D.modulus I) = 1 := (QuotientGroup.eq_one_iff _).mpr hmem
  rw [MonoidHom.mem_ker, tauArtinHom, MonoidHom.comp_apply, MonoidHom.comp_apply, h1, map_one]

/-- **The Artin map of the reciprocity data on TauCeti's ray class group** of the dominating
modulus. -/
def tauArtin (D : ClassFieldTheory.FiniteAbelianReciprocityData K L) :
    RayClassGroup (domModulus D.modulus) →* (L ≃ₐ[K] L) :=
  rayClassLift (tauArtinHom D) (ray_le_ker_tauArtinHom D)

/-- **`tauArtin` sends the ray class of a prime to the arithmetic Frobenius above it.** -/
theorem tauArtin_idealClass_prime (D : ClassFieldTheory.FiniteAbelianReciprocityData K L)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v.asIdeal ∈ integralIdealsPrimeTo (domModulus D.modulus))
    (w : HeightOneSpectrum (𝓞 L)) (hw : w.asIdeal.LiesOver v.asIdeal) :
    tauArtin D (idealClass _ ⟨v.asIdeal, hv⟩) = ClassFieldTheory.arithmeticFrobeniusAt w := by
  have hv' : v ∉ D.modulus.finitePart.support := notMem_support_of_mem_integralIdealsPrimeTo hv
  rw [← D.artin_frobenius v hv' w hw, idealClass_apply, tauArtin, rayClassLift_rayClassMk,
    tauArtinHom, MonoidHom.comp_apply, MonoidHom.comp_apply]
  -- both sides are the class of `v` as a fractional ideal prime to `m`
  congr 1

/-- At a prime `v ∤ domModulus m`, the Galois weight of `χ` is `χ` of the Artin image of the ray
class of `v`. -/
theorem galoisCharacterWeight_asIdeal_eq_tauArtin
    (D : ClassFieldTheory.FiniteAbelianReciprocityData K L) (χ : (L ≃ₐ[K] L) →* ℂˣ)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v.asIdeal ∈ integralIdealsPrimeTo (domModulus D.modulus)) :
    MonoidHom.galoisCharacterWeight (L := L) χ v.asIdeal =
      (χ (tauArtin D (idealClass _ ⟨v.asIdeal, hv⟩)) : ℂ) := by
  have hv' : v ∉ D.modulus.finitePart.support := notMem_support_of_mem_integralIdealsPrimeTo hv
  have hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q := fun Q hQ hlo =>
    D.unramifiedOutsideModulus.1 v hv' Q hQ hlo
  have : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨Q, hQp, hQlo, hQne⟩ := Chebotarev.exists_prime_liesOver K L v.asIdeal v.ne_bot
  have := hQp
  have := hQlo
  have : Finite (𝓞 L ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQne
  let w : HeightOneSpectrum (𝓞 L) := ⟨Q, hQp, hQne⟩
  have hσ := IsArithFrobAt.arithFrobAt (𝓞 K) (L ≃ₐ[K] L) Q
  have hout : Quotient.out (artinSymbol (L := L) v.asIdeal hur) =
      arithFrobAt (𝓞 K) (L ≃ₐ[K] L) Q :=
    isConj_iff_eq.mp (ConjClasses.mk_eq_mk_iff_isConj.mp ((Quotient.out_eq _).trans
      (artinSymbol_eq_mk_of_isArithFrobAt v.asIdeal hur Q _ hσ)))
  rw [MonoidHom.galoisCharacterWeight_apply_of_unramified χ v hur,
    tauArtin_idealClass_prime D v hv w hQlo]
  exact congrArg (fun σ => ((χ σ : ℂˣ) : ℂ)) hout

/-- **The Galois weights are ray class characters through `tauArtin`.** -/
theorem galoisCharacterWeight_eq_onIdeals_tauArtin
    (D : ClassFieldTheory.FiniteAbelianReciprocityData K L) (χ : (L ≃ₐ[K] L) →* ℂˣ)
    (I : integralIdealsPrimeTo (domModulus D.modulus)) :
    MonoidHom.galoisCharacterWeight (L := L) χ (I : Ideal (𝓞 K)) =
      (RayClassCharacter.onIdeals (χ.comp (tauArtin D)) I : ℂ) := by
  let f : integralIdealsPrimeTo (domModulus D.modulus) →* ℂ :=
    (MonoidHom.galoisCharacterWeight (L := L) χ).toMonoidWithZeroHom.toMonoidHom.comp
      (integralIdealsPrimeTo (domModulus D.modulus)).subtype
  let g : integralIdealsPrimeTo (domModulus D.modulus) →* ℂ :=
    (Units.coeHom ℂ).comp (RayClassCharacter.onIdeals (χ.comp (tauArtin D)))
  have hfg : f = g := NumberFieldArithmetic.integralIdealsAway_hom_ext fun v hv ↦ by
    simpa [f, g] using galoisCharacterWeight_asIdeal_eq_tauArtin D χ v hv
  exact DFunLike.congr_fun hfg I

/-- **Class field theory gives Artin data** through TauCeti's ray class group of the dominating
modulus. -/
def rayArtinDataOfReciprocity (D : ClassFieldTheory.FiniteAbelianReciprocityData K L) :
    RayArtinData K L (domModulus D.modulus) where
  artin := tauArtin D
  weight_eq := galoisCharacterWeight_eq_onIdeals_tauArtin D

end SimultaneousPrimitiveRoots.Unconditional.CFTBridge

end

