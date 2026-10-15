module

public import SimultaneousPrimitiveRoots.Unconditional.ArtinDescent
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

/-!
# From the Hecke zero-free strip to `ζ_L` of an abelian `L/F` (second half of step Z5)

Let `F` be an `m`-th cyclotomic field with `12 ∣ m`, and `L/F` abelian with an Artin map through
the ray class group of a modulus `𝔪` with finite part `≠ 𝓞` (`RayArtinData`). Under
`HeckeZeroFreeStrip δ` ([A] Thm 1.2), `(s - 1) ζ_L` has no zeros in `{Re s > 1 - δ} \ {1}`
(`dedekindZetaEntire_ne_zero_of_hecke`):

* a zero of `(s - 1) ζ_L` there is a zero of `(s - 1) ζ_F` or of some `L(s, χ ∘ artin)`, `χ ≠ 1`
  (`dedekindZetaEntire_eq_zero_or`);
* `(s - 1) L(s, 1_𝔪) = (s - 1) ζ_F(s) · ∏_{𝔭 | 𝔪} (1 - N𝔭^{-s})` on `ℂ \ {1}`
  (`sub_one_mul_rayLHecke_one`), and the product does not vanish on `Re s > 0`, so a zero of `ζ_F`
  is a zero of the `L`-function of the trivial character of `𝔪`;
* both contradict `RayClassLZeroFree`.

With `L = ℚ(ζ_{12q}, a^{1/q})` over `F = ℚ(ζ_{12q})` (Artin map from class field theory, step Z3)
and the descent of `CyclotomicDescent.lean` from `L = K_q(ζ₁₂)` to `K_q`, this gives [A]'s
`spl:field-bounds`.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Unconditional

open NumberField TauCeti TauCeti.GlobalNumberFields
open scoped nonZeroDivisors

section Trivial

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- The ray class coefficients of the trivial character: the indicator of the ideals prime to
`𝔪`. -/
theorem rayCoeff_one :
    rayCoeff (1 : RayClassCharacter 𝔪) =
      (MultiplicativeIdealWeight.ofBadPrimes (𝔪.support : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
        𝔪.support.finite_toSet).toIdealArithmeticFunction := by
  classical
  funext I
  rw [MultiplicativeIdealWeight.toIdealArithmeticFunction_apply,
    MultiplicativeIdealWeight.ofBadPrimes_apply]
  unfold rayCoeff
  by_cases h : (I : Ideal (𝓞 K)) ∈ integralIdealsPrimeTo 𝔪
  · have h' : Ideal.IsPrimeTo (I : Ideal (𝓞 K))
        (𝔪.support : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :=
      NumberFieldArithmetic.mem_integralIdealsAway_iff_isPrimeTo.mp h
    rw [dif_pos h, if_pos h', RayClassCharacter.onIdeals_apply, MonoidHom.one_apply,
      Units.val_one]
  · have h' : ¬ Ideal.IsPrimeTo (I : Ideal (𝓞 K))
        (𝔪.support : Set (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :=
      mt NumberFieldArithmetic.mem_integralIdealsAway_iff_isPrimeTo.mpr h
    rw [dif_neg h, if_neg h']

/-- `L(s, 1_𝔪) = ζ_K(s) ∏_{𝔭 | 𝔪} (1 - N𝔭^{-s})` on `Re s > 1`. -/
theorem rayClassLSeries_one {s : ℂ} (hs : 1 < s.re) :
    rayClassLSeries (1 : RayClassCharacter 𝔪) s =
      NumberField.dedekindZeta K s *
        ∏ P ∈ 𝔪.support, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) := by
  rw [rayClassLSeries, rayCoeff_one, LSeries_ofBadPrimes _ hs]

/-- **`(s - 1) L(s, 1_𝔪) = (s - 1) ζ_K(s) ∏_{𝔭 | 𝔪} (1 - N𝔭^{-s})` on `ℂ \ {1}`.** -/
theorem sub_one_mul_rayLHecke_one (hinf : 𝔪.infinitePart = ∅) (hnt : 𝔪.finitePart ≠ ⊤)
    {s : ℂ} (hs : s ≠ 1) :
    (s - 1) * rayLHecke hnt (1 : RayClassCharacter 𝔪) s =
      Hecke.dedekindZetaEntire K s *
        ∏ P ∈ 𝔪.support, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)) := by
  set U : Set ℂ := {1}ᶜ with hU
  have hUopen : IsOpen U := isOpen_compl_singleton
  have hprod : Differentiable ℂ fun z : ℂ =>
      ∏ P ∈ 𝔪.support, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-z)) := by
    intro z
    refine DifferentiableAt.fun_finsetProd fun P _ => ?_
    have hN := P.natCast_absNorm_ne_zero
    exact (differentiableAt_const _).sub (differentiableAt_id.neg.const_cpow (Or.inl hN))
  have hl : AnalyticOnNhd ℂ (fun z => (z - 1) * rayLHecke hnt (1 : RayClassCharacter 𝔪) z) U :=
    DifferentiableOn.analyticOnNhd (fun z hz =>
      ((differentiableAt_id.sub_const 1).mul
        (differentiableAt_rayLHecke hnt _ hz)).differentiableWithinAt) hUopen
  have hr : AnalyticOnNhd ℂ (fun z => Hecke.dedekindZetaEntire K z *
      ∏ P ∈ 𝔪.support, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-z))) U :=
    DifferentiableOn.analyticOnNhd (fun z _ =>
      ((Hecke.differentiable_dedekindZetaEntire K z).mul (hprod z)).differentiableWithinAt)
      hUopen
  have hpre : IsPreconnected U :=
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
  have h2 : (2 : ℂ) ∈ U := by
    show (2 : ℂ) ≠ 1
    norm_num
  have hfreq : ∃ᶠ z in nhdsWithin (2 : ℂ) {2}ᶜ,
      (z - 1) * rayLHecke hnt (1 : RayClassCharacter 𝔪) z =
        Hecke.dedekindZetaEntire K z *
          ∏ P ∈ 𝔪.support, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-z)) := by
    have hev : ∀ᶠ z in nhds (2 : ℂ), (z - 1) * rayLHecke hnt (1 : RayClassCharacter 𝔪) z =
        Hecke.dedekindZetaEntire K z *
          ∏ P ∈ 𝔪.support, (1 - (Ideal.absNorm P.asIdeal : ℂ) ^ (-z)) := by
      have hopen : IsOpen {z : ℂ | 1 < z.re} := Complex.isOpen_re_gt 1
      filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
      have hz' : 1 < z.re := hz
      rw [rayLHecke_eq hinf hnt _ hz', rayClassLSeries_one hz',
        Hecke.dedekindZetaEntire_eq_mul K hz', mul_assoc]
    exact (hev.filter_mono nhdsWithin_le_nhds).frequently
  exact hl.eqOn_of_preconnected_of_frequently_eq hr hpre h2 hfreq hs

end Trivial

/-- **[A] Thm 1.2 bounds the zeros of `ζ_L` for every abelian `L` over a cyclotomic field
`F ⊇ μ₁₂` with an Artin map.** -/
theorem dedekindZetaEntire_ne_zero_of_hecke {δ : ℝ} (hδ : δ ≤ 1) (hA : HeckeZeroFreeStrip δ)
    {m : ℕ} [NeZero m] (h12 : 12 ∣ m) {F : Type} [Field F] [NumberField F]
    [IsCyclotomicExtension {m} ℚ F] {L : Type*} [Field L] [NumberField L] [Algebra F L]
    [IsGalois F L] [FiniteDimensional F L] [IsMulCommutative (L ≃ₐ[F] L)] {𝔪 : Modulus F}
    (D : RayArtinData F L 𝔪) (hnt : 𝔪.finitePart ≠ ⊤) :
    ∀ s : ℂ, 1 - δ < s.re → s ≠ 1 → Hecke.dedekindZetaEntire L s ≠ 0 := by
  intro ρ hρ hρ1 hL
  have hm2 : 2 < m := lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd (NeZero.pos m) h12)
  have : NumberField.IsTotallyComplex F := IsCyclotomicExtension.Rat.isTotallyComplex F hm2
  have hinf : 𝔪.infinitePart = ∅ := Modulus.infinitePart_eq_empty 𝔪
  have hρ0 : 0 < ρ.re := by linarith
  rcases dedekindZetaEntire_eq_zero_or D hinf hnt hρ0 hρ1 hL with hF | ⟨χ, -, hχ⟩
  · have h1 := sub_one_mul_rayLHecke_one hinf hnt hρ1
    rw [hF, zero_mul] at h1
    have h2 : rayLHecke hnt (1 : RayClassCharacter 𝔪) ρ = 0 :=
      (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hρ1)
    exact rayLHecke_ne_zero hinf hnt (hA m h12 F 𝔪 1) hρ hρ1 h2
  · exact rayLHecke_ne_zero hinf hnt (hA m h12 F 𝔪 _) hρ hρ1 hχ

end SimultaneousPrimitiveRoots.Unconditional

end
