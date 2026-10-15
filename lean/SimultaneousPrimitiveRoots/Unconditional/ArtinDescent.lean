module

public import CebotarevDensity.ZetaProduct
public import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Cyclotomic.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Restrict
public import SimultaneousPrimitiveRoots.Unconditional.RayLSeries
public import SimultaneousPrimitiveRoots.Hecke.DirichletBound
public import Mathlib.Analysis.Normed.Module.Connected
public import TauCeti.RingTheory.Norm.Congruence

/-!
# Zeros move along an abelian extension with an Artin map (steps Z4 and Z5)

Let `L/K` be an abelian extension of number fields and `𝔪` a modulus of `K` with no infinite part
and finite part `≠ 𝓞`, together with an Artin map `RayClassGroup 𝔪 →* Gal(L/K)` that matches the
Galois weights on the ideals prime to `𝔪` (`RayArtinData`). For `Re s > 1`, AINTLIB's abelian
factorization `Chebotarev.dedekindZeta_eq_prod_artinDirichletSeries` writes `ζ_L` as the product
over the characters `χ` of `Gal(L/K)` of the Artin series `A_χ`, times finitely many Euler factors
at the primes of `L` above the ramified primes of `K`. We identify (`Re s > 1`):

* `A_χ` with TauCeti's `L`-series of the ideal weight `galoisCharacterWeight χ`
  (`artinDirichletSeries_eq_LSeries`; on primes both are `χ` of the Frobenius class);
* for `χ = 1`, that `L`-series with `ζ_K` times the deleted Euler factors at the ramified primes
  (`artinDirichletSeries_one`);
* for every `χ`, the weight deleted at the primes dividing `𝔪` with the ray class coefficients of
  `χ ∘ artin` (`rayCoeff_comp_artin`), so
  `rayClassLSeries (χ ∘ artin) = A_χ · ∏_{𝔭 | 𝔪} (1 - χ(𝔭) N𝔭^{-s})`.

So `ζ_L · D = ζ_K · N` on `Re s > 1`, with `D` a finite product of factors `1 - c N^{-s}`
(`|c| ≤ 1`, `N ≥ 2`: nonzero on `Re s > 0`) and `N` built from Hecke's continuations
`rayLHecke (χ ∘ artin)` (step Z2, holomorphic on `ℂ \ {1}`). Multiplying by `s - 1` and using
the identity theorem on the connected set `ℂ \ {1}` (`dedekindZetaEntire_mul_descentD`):

* every zero of `(s - 1) ζ_K` with `Re s > 0` is a zero of `(s - 1) ζ_L`
  (`dedekindZetaEntire_ne_zero_of_descent`);
* every zero of `(s - 1) ζ_L` with `Re s > 0`, `s ≠ 1`, is a zero of `(s - 1) ζ_K` or of some
  `rayLHecke (χ ∘ artin)`, `χ ≠ 1` (`dedekindZetaEntire_eq_zero_or`).

For `L = K(μ_m)` the Artin map is TauCeti's `cyclotomicArtin` (`CyclotomicDescent.lean`); for the
Kummer extension `ℚ(ζ_{12q}, a^{1/q}) / ℚ(ζ_{12q})` it comes from class field theory (step Z3).
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Unconditional

open NumberField TauCeti TauCeti.GlobalNumberFields IsDedekindDomain NumberField.Chebotarev
open scoped nonZeroDivisors

/-! ### AINTLIB's Artin series is TauCeti's `L`-series of the Galois weight -/

section Bridge

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

omit [NumberField K] in
theorem unramifiedIn_iff (v : HeightOneSpectrum (𝓞 K)) :
    Chebotarev.UnramifiedIn K L v.asIdeal ↔
      ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal], Algebra.IsUnramifiedAt (𝓞 K) Q := by
  constructor
  · rintro ⟨-, h⟩ Q _ _
    have hQ : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
    exact h Q (Ring.DimensionLEOne.maximalOfPrime hQ inferInstance) inferInstance
  · intro h
    refine ⟨v.ne_bot, fun Q hQ hlo => ?_⟩
    have := hQ.isPrime
    exact h Q

/-- AINTLIB's Frobenius class and TauCeti's Artin symbol agree: both are the class of an
arithmetic Frobenius at a prime above. -/
theorem frobeniusClass_eq_artinSymbol (v : HeightOneSpectrum (𝓞 K))
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) :
    haveI : v.asIdeal.IsMaximal := v.isMaximal
    Chebotarev.frobeniusClass K L v.asIdeal = artinSymbol (L := L) v.asIdeal hur := by
  have : v.asIdeal.IsMaximal := v.isMaximal
  obtain ⟨Q, hQp, hQlo, hQne⟩ := Chebotarev.exists_prime_liesOver K L v.asIdeal v.ne_bot
  have := hQp
  have := hQlo
  have : Algebra.IsUnramifiedAt (𝓞 K) Q := hur Q
  have : Finite (𝓞 L ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQne
  have hσ := IsArithFrobAt.arithFrobAt (𝓞 K) (L ≃ₐ[K] L) Q
  rw [Chebotarev.frobeniusClass_eq_mk_of_isArithFrobAt K L v.asIdeal ((unramifiedIn_iff v).mpr hur)
    _ Q hσ hQlo, artinSymbol_eq_mk_of_isArithFrobAt v.asIdeal hur Q _ hσ]

theorem galoisCharacterOnIdeal_heightOne (χ : (L ≃ₐ[K] L) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    Chebotarev.galoisCharacterOnIdeal K L χ v.asIdeal =
      MonoidHom.galoisCharacterWeight (L := L) χ v.asIdeal := by
  classical
  have : v.asIdeal.IsPrime := v.isPrime
  rw [Chebotarev.galoisCharacterOnIdeal_apply_prime K L χ v.asIdeal v.ne_bot]
  by_cases h : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q
  · rw [if_pos ((unramifiedIn_iff v).mpr h),
      MonoidHom.galoisCharacterWeight_apply_of_unramified χ v h, frobeniusClass_eq_artinSymbol v h]
  · rw [if_neg (mt (unramifiedIn_iff v).mp h)]
    exact ((MonoidHom.galoisCharacterWeight_apply_eq_zero_iff χ v).mpr
      ((mem_ramifiedPrimes_iff v).mpr h)).symm

/-- AINTLIB's ideal character agrees with TauCeti's Galois weight on nonzero ideals. -/
theorem galoisCharacterOnIdeal_eq_weight (χ : (L ≃ₐ[K] L) →* ℂˣ) {𝔞 : Ideal (𝓞 K)}
    (h𝔞 : 𝔞 ≠ ⊥) :
    Chebotarev.galoisCharacterOnIdeal K L χ 𝔞 =
      MonoidHom.galoisCharacterWeight (L := L) χ 𝔞 := by
  induction 𝔞 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl h𝔞
  | h₂ u hu =>
    rw [Ideal.isUnit_iff.mp hu, Chebotarev.galoisCharacterOnIdeal_one, ← Ideal.one_eq_top,
      map_one]
  | h₃ a p ha hp ih =>
    have hp0 : p ≠ ⊥ := hp.ne_zero
    have : p.IsPrime := (Ideal.prime_iff_isPrime hp0).mp hp
    let v : HeightOneSpectrum (𝓞 K) := ⟨p, inferInstance, hp0⟩
    rw [Chebotarev.galoisCharacterOnIdeal_mul K L χ hp0 ha, map_mul, ih ha,
      show p = v.asIdeal from rfl, galoisCharacterOnIdeal_heightOne χ v]

/-- **AINTLIB's Artin series is the `L`-series of the Galois weight**, for `Re s > 1`. -/
theorem artinDirichletSeries_eq_LSeries (χ : (L ≃ₐ[K] L) →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    Chebotarev.artinDirichletSeries K L χ s =
      LSeries (normCoeff K (MonoidHom.galoisCharacterWeight (L := L) χ).toIdealArithmeticFunction)
        s := by
  rw [LSeries_normCoeff K (MonoidHom.summable_idealTerm_galoisCharacterWeight χ hs),
    Chebotarev.artinDirichletSeries]
  let e : {𝔞 : Ideal (𝓞 K) // 𝔞 ≠ ⊥} ≃ (Ideal (𝓞 K))⁰ :=
    { toFun := fun 𝔞 => ⟨𝔞.1, mem_nonZeroDivisors_of_ne_zero 𝔞.2⟩
      invFun := fun I => ⟨I.1, nonZeroDivisors.coe_ne_zero I⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← e.tsum_eq]
  apply tsum_congr
  intro 𝔞
  rw [idealTerm_def, MultiplicativeIdealWeight.toIdealArithmeticFunction_apply]
  show Chebotarev.galoisCharacterOnIdeal K L χ 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s) =
    MonoidHom.galoisCharacterWeight (L := L) χ 𝔞.1 / (Ideal.absNorm 𝔞.1 : ℂ) ^ s
  rw [galoisCharacterOnIdeal_eq_weight χ 𝔞.2, Complex.cpow_neg, div_eq_mul_inv]

end Bridge

/-! ### An Artin map through a ray class group -/

section Artin

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- **An Artin map through a ray class group.** A homomorphism from the ray class group of `𝔪` to
`Gal(L/K)` under which the Galois weight of every character `χ` is the ray class character
`χ ∘ artin` on the ideals prime to `𝔪`; equivalently, the ray class of every prime `𝔭 ∤ 𝔪` (all
unramified) goes to the Frobenius at `𝔭`. -/
structure RayArtinData (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (𝔪 : Modulus K) where
  /-- The Artin map. -/
  artin : RayClassGroup 𝔪 →* (L ≃ₐ[K] L)
  /-- The Galois weights are ray class characters through `artin`. -/
  weight_eq : ∀ (χ : (L ≃ₐ[K] L) →* ℂˣ) (I : integralIdealsPrimeTo 𝔪),
    MonoidHom.galoisCharacterWeight (L := L) χ (I : Ideal (𝓞 K)) =
      (RayClassCharacter.onIdeals (χ.comp artin) I : ℂ)

variable {𝔪 : Modulus K} (D : RayArtinData K L 𝔪)

/-- The ray class coefficients of `χ ∘ artin` are the Galois weight of `χ` with the Euler factors
at the primes dividing `𝔪` deleted. -/
theorem rayCoeff_comp_artin (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    rayCoeff (χ.comp D.artin) =
      ((MonoidHom.galoisCharacterWeight (L := L) χ).restrict
        (𝔪.support : Set (HeightOneSpectrum (𝓞 K)))
        𝔪.support.finite_toSet).toIdealArithmeticFunction := by
  classical
  funext I
  rw [MultiplicativeIdealWeight.toIdealArithmeticFunction_apply,
    MultiplicativeIdealWeight.restrict_apply]
  unfold rayCoeff
  by_cases h : (I : Ideal (𝓞 K)) ∈ integralIdealsPrimeTo 𝔪
  · have h' : Ideal.IsPrimeTo (I : Ideal (𝓞 K)) (𝔪.support : Set (HeightOneSpectrum (𝓞 K))) :=
      NumberFieldArithmetic.mem_integralIdealsAway_iff_isPrimeTo.mp h
    rw [dif_pos h, if_pos h', ← D.weight_eq χ ⟨I, h⟩]
  · have h' : ¬ Ideal.IsPrimeTo (I : Ideal (𝓞 K)) (𝔪.support : Set (HeightOneSpectrum (𝓞 K))) :=
      mt NumberFieldArithmetic.mem_integralIdealsAway_iff_isPrimeTo.mpr h
    rw [dif_neg h, if_neg h']

/-- `rayClassLSeries (χ ∘ artin) = A_χ · ∏_{𝔭 | 𝔪} (1 - χ(𝔭) N𝔭^{-s})` on `Re s > 1`. -/
theorem rayClassLSeries_comp_artin (χ : (L ≃ₐ[K] L) →* ℂˣ) {s : ℂ} (hs : 1 < s.re) :
    rayClassLSeries (χ.comp D.artin) s =
      Chebotarev.artinDirichletSeries K L χ s *
        ∏ P ∈ 𝔪.support,
          (1 - MonoidHom.galoisCharacterWeight (L := L) χ P.asIdeal /
            (Ideal.absNorm P.asIdeal : ℂ) ^ s) := by
  rw [rayClassLSeries, rayCoeff_comp_artin D, artinDirichletSeries_eq_LSeries χ hs,
    MultiplicativeIdealWeight.LSeries_restrict _ _
      (MonoidHom.summable_idealTerm_galoisCharacterWeight χ hs)]

omit [IsGalois K L] in
/-- The trivial character: `A_1 = ζ_K · ∏_{𝔭 ramified} (1 - N𝔭^{-s})` on `Re s > 1`. -/
theorem artinDirichletSeries_one [IsGalois K L] {s : ℂ} (hs : 1 < s.re) :
    Chebotarev.artinDirichletSeries K L 1 s =
      NumberField.dedekindZeta K s *
        ∏ P ∈ ramifiedPrimes K L, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) := by
  rw [artinDirichletSeries_eq_LSeries (1 : (L ≃ₐ[K] L) →* ℂˣ) hs,
    MonoidHom.galoisCharacterWeight_one, LSeries_ofBadPrimes _ hs]

end Artin

/-! ### Euler factors that do not vanish on `Re s > 0` -/

theorem one_sub_div_absNorm_cpow_ne_zero {F : Type*} [Field F] [NumberField F]
    (P : HeightOneSpectrum (𝓞 F)) {c : ℂ} (hc : ‖c‖ ≤ 1) {s : ℂ} (hs : 0 < s.re) :
    1 - c / (Ideal.absNorm P.asIdeal : ℂ) ^ s ≠ 0 := by
  intro h
  have h1 : c / (Ideal.absNorm P.asIdeal : ℂ) ^ s = 1 := (sub_eq_zero.mp h).symm
  have h2 := P.one_lt_norm_absNorm_cpow hs
  have h3 : ‖c / (Ideal.absNorm P.asIdeal : ℂ) ^ s‖ < 1 := by
    rw [norm_div, div_lt_one (by linarith)]
    linarith
  rw [h1, norm_one] at h3
  exact lt_irrefl _ h3

theorem one_sub_absNorm_cpow_neg_ne_zero {F : Type*} [Field F] [NumberField F]
    (P : HeightOneSpectrum (𝓞 F)) {s : ℂ} (hs : 0 < s.re) :
    1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s) ≠ 0 := by
  have h := one_sub_div_absNorm_cpow_ne_zero P (c := 1) (by simp) hs
  rwa [one_div, ← Complex.cpow_neg] at h

theorem differentiable_one_sub_div_absNorm_cpow {F : Type*} [Field F] [NumberField F]
    (P : HeightOneSpectrum (𝓞 F)) (c : ℂ) :
    Differentiable ℂ fun s : ℂ => 1 - c / (Ideal.absNorm P.asIdeal : ℂ) ^ s := by
  have hN := P.natCast_absNorm_ne_zero
  have h : (fun s : ℂ => 1 - c / (Ideal.absNorm P.asIdeal : ℂ) ^ s) =
      fun s : ℂ => 1 - c * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s) := by
    funext s
    rw [Complex.cpow_neg, div_eq_mul_inv]
  rw [h]
  exact (differentiable_const _).sub
    ((differentiable_const _).mul (differentiable_id.neg.const_cpow (Or.inl hN)))

/-! ### The primes of `L` over the ramified primes of `K` -/

section Ramified

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- The primes of `L` over the primes of `K` ramified in `L`: AINTLIB's correction factors. -/
abbrev RamAbove : Type _ :=
  {𝔓 : Ideal (𝓞 L) // 𝔓.IsPrime ∧ 𝔓 ≠ ⊥ ∧ ¬ Chebotarev.UnramifiedIn K L (𝔓.under (𝓞 K))}

/-- Only finitely many primes of `K` ramify, and each has finitely many primes above it (the
argument of AINTLIB's private `finite_ramifiedAbove`). -/
instance finite_ramAbove : Finite (RamAbove K L) := by
  classical
  have : Finite {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ Chebotarev.UnramifiedIn K L 𝔭} :=
    (Chebotarev.finite_ramifiedIn K L).to_subtype
  have : ∀ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ Chebotarev.UnramifiedIn K L 𝔭},
      Finite (𝔭.1.primesOver (𝓞 L)) := fun 𝔭 => by
    have : 𝔭.1.IsPrime := 𝔭.2.1
    have : 𝔭.1.IsMaximal := 𝔭.2.1.isMaximal 𝔭.2.2.1
    exact (IsDedekindDomain.primesOver_finite 𝔭.1 (𝓞 L)).to_subtype
  refine Finite.of_injective
    (fun 𝔓 : RamAbove K L =>
      (show Σ 𝔭 : {𝔭 : Ideal (𝓞 K) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ Chebotarev.UnramifiedIn K L 𝔭},
          𝔭.1.primesOver (𝓞 L) by
        have := 𝔓.2.1
        exact ⟨⟨𝔓.1.under (𝓞 K), inferInstance, Ideal.under_ne_bot (A := 𝓞 K) 𝔓.2.2.1,
          𝔓.2.2.2⟩, ⟨𝔓.1, 𝔓.2.1, Ideal.over_under (A := 𝓞 K) (P := 𝔓.1)⟩⟩))
    (fun a b hab => Subtype.ext (by simpa using congrArg (fun x => (x.2 : Ideal (𝓞 L))) hab))

/-- A prime of `RamAbove K L`, as a height-one prime of `𝓞 L`. -/
def RamAbove.toHeightOne (𝔓 : RamAbove K L) : HeightOneSpectrum (𝓞 L) :=
  ⟨𝔓.1, 𝔓.2.1, 𝔓.2.2.1⟩

end Ramified

/-! ### The factorization `ζ_L · D = ζ_K · N` and the descent of zeros -/

section Descent

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] [FiniteDimensional K L] [IsMulCommutative (L ≃ₐ[K] L)] {𝔪 : Modulus K}
  (D : RayArtinData K L 𝔪)

open Classical in
/-- The correction `D(s)`: the Euler factors at the primes dividing `m` of the nontrivial
characters, and the Euler factors of `ζ_L` at the primes above the ramified primes. -/
def descentD (𝔪 : Modulus K) (s : ℂ) : ℂ :=
  letI : Fintype ((L ≃ₐ[K] L) →* ℂˣ) := Fintype.ofFinite _
  letI : Fintype (RamAbove K L) := Fintype.ofFinite _
  (∏ χ ∈ (Finset.univ : Finset ((L ≃ₐ[K] L) →* ℂˣ)).erase 1,
      ∏ P ∈ 𝔪.support,
        (1 - MonoidHom.galoisCharacterWeight (L := L) χ P.asIdeal /
          (Ideal.absNorm P.asIdeal : ℂ) ^ s)) *
    ∏ 𝔓 : RamAbove K L,
      (1 - 1 / (Ideal.absNorm (RamAbove.toHeightOne K L 𝔓).asIdeal : ℂ) ^ s)

open Classical in
/-- The numerator `N(s)`: `ζ_K`'s deleted Euler factors at the ramified primes, times the
continued `L`-functions of the nontrivial characters. -/
def descentN (hnt : 𝔪.finitePart ≠ ⊤) (s : ℂ) : ℂ :=
  letI : Fintype ((L ≃ₐ[K] L) →* ℂˣ) := Fintype.ofFinite _
  (∏ P ∈ ramifiedPrimes K L, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))) *
    ∏ χ ∈ (Finset.univ : Finset ((L ≃ₐ[K] L) →* ℂˣ)).erase 1,
      rayLHecke hnt (χ.comp D.artin) s

omit [IsMulCommutative (L ≃ₐ[K] L)] in
theorem differentiable_descentD : Differentiable ℂ (descentD (K := K) (L := L) 𝔪) := by
  classical
  intro s
  unfold descentD
  refine DifferentiableAt.mul ?_ ?_
  · refine DifferentiableAt.fun_finsetProd fun χ _ => ?_
    exact DifferentiableAt.fun_finsetProd fun P _ =>
      differentiable_one_sub_div_absNorm_cpow P _ s
  · exact DifferentiableAt.fun_finsetProd fun 𝔓 _ =>
      differentiable_one_sub_div_absNorm_cpow (RamAbove.toHeightOne K L 𝔓) 1 s

omit [IsMulCommutative (L ≃ₐ[K] L)] in
theorem descentD_ne_zero {s : ℂ} (hs : 0 < s.re) : descentD (K := K) (L := L) 𝔪 s ≠ 0 := by
  classical
  unfold descentD
  refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun χ _ =>
    Finset.prod_ne_zero_iff.mpr fun P _ => ?_) (Finset.prod_ne_zero_iff.mpr fun 𝔓 _ => ?_)
  · exact one_sub_div_absNorm_cpow_ne_zero P
      (MonoidHom.norm_galoisCharacterWeight_le_one χ P.asIdeal) hs
  · exact one_sub_div_absNorm_cpow_ne_zero _ (by simp) hs

omit [IsMulCommutative (L ≃ₐ[K] L)] in
theorem differentiableAt_descentN (hnt : 𝔪.finitePart ≠ ⊤) {s : ℂ}
    (hs : s ≠ 1) :
    DifferentiableAt ℂ (descentN D hnt) s := by
  classical
  unfold descentN
  refine DifferentiableAt.mul ?_ ?_
  · refine DifferentiableAt.fun_finsetProd fun P _ => ?_
    have hN := P.natCast_absNorm_ne_zero
    exact (differentiableAt_const _).sub (differentiableAt_id.neg.const_cpow (Or.inl hN))
  · exact DifferentiableAt.fun_finsetProd fun χ _ => differentiableAt_rayLHecke hnt _ hs

set_option linter.style.haveILetI false in
/-- **`ζ_L · D = ζ_K · N` on `Re s > 1`.** -/
theorem dedekindZeta_mul_descentD (hinf : 𝔪.infinitePart = ∅)
    (hnt : 𝔪.finitePart ≠ ⊤) {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s * descentD (K := K) (L := L) 𝔪 s =
      NumberField.dedekindZeta K s * descentN D hnt s := by
  classical
  letI : Fintype ((L ≃ₐ[K] L) →* ℂˣ) := Fintype.ofFinite _
  letI : Fintype (RamAbove K L) := Fintype.ofFinite _
  have hs0 : 0 < s.re := by linarith
  rw [Chebotarev.dedekindZeta_eq_prod_artinDirichletSeries K L hs, tprod_fintype, tprod_fintype]
  unfold descentD descentN
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ 1), artinDirichletSeries_one hs]
  -- the nontrivial characters
  have hchar : ∀ χ ∈ (Finset.univ : Finset ((L ≃ₐ[K] L) →* ℂˣ)).erase 1,
      Chebotarev.artinDirichletSeries K L χ s *
        ∏ P ∈ 𝔪.support,
          (1 - MonoidHom.galoisCharacterWeight (L := L) χ P.asIdeal /
            (Ideal.absNorm P.asIdeal : ℂ) ^ s) =
        rayLHecke hnt (χ.comp D.artin) s := fun χ _ => by
    rw [rayLHecke_eq hinf hnt _ hs, rayClassLSeries_comp_artin D χ hs]
  -- the ramified Euler factors of `ζ_L` cancel
  have hram : ∀ 𝔓 : RamAbove K L,
      (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ *
        (1 - 1 / (Ideal.absNorm (RamAbove.toHeightOne K L 𝔓).asIdeal : ℂ) ^ s) = 1 := fun 𝔓 => by
    have h := one_sub_absNorm_cpow_neg_ne_zero (RamAbove.toHeightOne K L 𝔓) hs0
    rw [one_div, ← Complex.cpow_neg]
    exact inv_mul_cancel₀ h
  calc NumberField.dedekindZeta K s *
        (∏ P ∈ ramifiedPrimes K L, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))) *
        (∏ χ ∈ (Finset.univ : Finset ((L ≃ₐ[K] L) →* ℂˣ)).erase 1,
          Chebotarev.artinDirichletSeries K L χ s) *
        (∏ 𝔓 : RamAbove K L, (1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹) *
        ((∏ χ ∈ (Finset.univ : Finset ((L ≃ₐ[K] L) →* ℂˣ)).erase 1,
            ∏ P ∈ 𝔪.support,
              (1 - MonoidHom.galoisCharacterWeight (L := L) χ P.asIdeal /
                (Ideal.absNorm P.asIdeal : ℂ) ^ s)) *
          ∏ 𝔓 : RamAbove K L,
            (1 - 1 / (Ideal.absNorm (RamAbove.toHeightOne K L 𝔓).asIdeal : ℂ) ^ s))
      = NumberField.dedekindZeta K s *
        (∏ P ∈ ramifiedPrimes K L, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s))) *
        (∏ χ ∈ (Finset.univ : Finset ((L ≃ₐ[K] L) →* ℂˣ)).erase 1,
          (Chebotarev.artinDirichletSeries K L χ s *
            ∏ P ∈ 𝔪.support,
              (1 - MonoidHom.galoisCharacterWeight (L := L) χ P.asIdeal /
                (Ideal.absNorm P.asIdeal : ℂ) ^ s))) *
        (∏ 𝔓 : RamAbove K L, ((1 - (Ideal.absNorm 𝔓.1 : ℂ) ^ (-s))⁻¹ *
          (1 - 1 / (Ideal.absNorm (RamAbove.toHeightOne K L 𝔓).asIdeal : ℂ) ^ s))) := by
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
        ring
    _ = _ := by
        rw [Finset.prod_congr rfl hchar, Finset.prod_congr rfl fun 𝔓 _ => hram 𝔓,
          Finset.prod_const_one, mul_one]
        ring

/-- **The identity `(s - 1) ζ_L · D = (s - 1) ζ_K · N` on `ℂ \ {1}`.** -/
theorem dedekindZetaEntire_mul_descentD (hinf : 𝔪.infinitePart = ∅)
    (hnt : 𝔪.finitePart ≠ ⊤) {s : ℂ} (hs : s ≠ 1) :
    Hecke.dedekindZetaEntire L s * descentD (K := K) (L := L) 𝔪 s =
      Hecke.dedekindZetaEntire K s * descentN D hnt s := by
  set U : Set ℂ := {1}ᶜ with hU
  have hUopen : IsOpen U := isOpen_compl_singleton
  have hl : AnalyticOnNhd ℂ (fun z => Hecke.dedekindZetaEntire L z *
      descentD (K := K) (L := L) 𝔪 z) U :=
    DifferentiableOn.analyticOnNhd (fun z _ =>
      ((Hecke.differentiable_dedekindZetaEntire L z).mul
        (differentiable_descentD z)).differentiableWithinAt) hUopen
  have hr : AnalyticOnNhd ℂ (fun z => Hecke.dedekindZetaEntire K z *
      descentN D hnt z) U :=
    DifferentiableOn.analyticOnNhd (fun z hz =>
      ((Hecke.differentiable_dedekindZetaEntire K z).mul
        (differentiableAt_descentN D hnt hz)).differentiableWithinAt) hUopen
  have hpre : IsPreconnected U :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have h2 : (2 : ℂ) ∈ U := by
    show (2 : ℂ) ≠ 1
    norm_num
  have hfreq : ∃ᶠ z in nhdsWithin (2 : ℂ) {2}ᶜ, Hecke.dedekindZetaEntire L z *
      descentD (K := K) (L := L) 𝔪 z =
        Hecke.dedekindZetaEntire K z * descentN D hnt z := by
    have hev : ∀ᶠ z in nhds (2 : ℂ), Hecke.dedekindZetaEntire L z *
        descentD (K := K) (L := L) 𝔪 z =
          Hecke.dedekindZetaEntire K z * descentN D hnt z := by
      have hopen : IsOpen {z : ℂ | 1 < z.re} := Complex.isOpen_re_gt 1
      filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
      have hz' : 1 < z.re := hz
      rw [Hecke.dedekindZetaEntire_eq_mul L hz', Hecke.dedekindZetaEntire_eq_mul K hz', mul_assoc,
        dedekindZeta_mul_descentD D hinf hnt hz', mul_assoc]
    exact (hev.filter_mono nhdsWithin_le_nhds).frequently
  exact hl.eqOn_of_preconnected_of_frequently_eq hr hpre h2 hfreq hs

include D in
/-- **Zeros descend from `L` to `K`.** If `(s - 1) ζ_L` has no zeros in `{Re s > 1 - δ} \ {1}`
(`δ ≤ 1`), then `(s - 1) ζ_K` has no zeros in `Re s > 1 - δ`. -/
theorem dedekindZetaEntire_ne_zero_of_descent (hinf : 𝔪.infinitePart = ∅)
    (hnt : 𝔪.finitePart ≠ ⊤) {δ : ℝ} (hδ : δ ≤ 1)
    (hL : ∀ s : ℂ, 1 - δ < s.re → s ≠ 1 → Hecke.dedekindZetaEntire L s ≠ 0) :
    ∀ s : ℂ, 1 - δ < s.re → Hecke.dedekindZetaEntire K s ≠ 0 := by
  intro s hs
  by_cases hs1 : s = 1
  · rw [hs1]
    exact Hecke.dedekindZetaEntire_one_ne_zero K
  intro hK
  have hs0 : 0 < s.re := by linarith
  have h := dedekindZetaEntire_mul_descentD D hinf hnt hs1
  rw [hK, zero_mul] at h
  exact hL s hs hs1 ((mul_eq_zero.mp h).resolve_right (descentD_ne_zero hs0))

/-- **Zeros of `ζ_L` come from `ζ_K` or from the nontrivial ray class `L`-functions.** If
`(s - 1) ζ_L` vanishes at `ρ`, `Re ρ > 0`, `ρ ≠ 1`, then `(s - 1) ζ_K` vanishes at `ρ` or Hecke's
continuation of `L(s, χ ∘ artin)` does for some `χ ≠ 1`. -/
theorem dedekindZetaEntire_eq_zero_or (hinf : 𝔪.infinitePart = ∅) (hnt : 𝔪.finitePart ≠ ⊤)
    {ρ : ℂ} (hρ : 0 < ρ.re) (hρ1 : ρ ≠ 1) (hL : Hecke.dedekindZetaEntire L ρ = 0) :
    Hecke.dedekindZetaEntire K ρ = 0 ∨
      ∃ χ : (L ≃ₐ[K] L) →* ℂˣ, χ ≠ 1 ∧ rayLHecke hnt (χ.comp D.artin) ρ = 0 := by
  classical
  have h := dedekindZetaEntire_mul_descentD D hinf hnt hρ1
  rw [hL, zero_mul] at h
  rcases mul_eq_zero.mp h.symm with hK | hN
  · exact Or.inl hK
  · right
    unfold descentN at hN
    rcases mul_eq_zero.mp hN with hP | hX
    · exact absurd hP (prod_one_sub_absNorm_cpow_neg_ne_zero _ hρ)
    · obtain ⟨χ, hχ, h0⟩ := Finset.prod_eq_zero_iff.mp hX
      exact ⟨χ, Finset.ne_of_mem_erase hχ, h0⟩

end Descent

end SimultaneousPrimitiveRoots.Unconditional

end
