module

public import SimultaneousPrimitiveRoots.Unconditional.ArtinDescent
public import TauCeti.RingTheory.Norm.Congruence

/-!
# Zeros descend from `K(μ_m)` to `K` (step Z4(a) and the first half of Z5)

TauCeti's `cyclotomicArtin` is an Artin map for `L = K(μ_m)` over `K` through the ray class group
of the cyclotomic modulus, matching the Galois weights on the ideals prime to `m`
(`cyclotomicArtinData`). So the descent of `ArtinDescent.lean` applies with no class field
theory: for a totally complex `K` and `m ≠ 1`, if `(s - 1) ζ_L` has no zeros in
`{Re s > 1 - δ} \ {1}` (`δ ≤ 1`), then `(s - 1) ζ_K` has none in `Re s > 1 - δ`
(`dedekindZetaEntire_ne_zero_of_cyclotomic'`).

For `K = ℚ(ζ_q, a^{1/q})` and `m = 12` this moves the zero-free region of `ζ_{K(ζ₁₂)}` down to
`ζ_K`, the first half of [A]'s `spl:field-bounds`.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Unconditional

open NumberField TauCeti TauCeti.GlobalNumberFields NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] {m : ℕ} [NeZero m] [IsCyclotomicExtension {m} K L]

variable (K L m) in
/-- TauCeti's cyclotomic Artin map, as Artin data through the cyclotomic modulus. -/
def cyclotomicArtinData : RayArtinData K L (cyclotomicModulus K m) where
  artin := cyclotomicArtin K L m
  weight_eq χ I := MonoidHom.galoisCharacterWeight_eq_onIdeals_cyclotomicArtin χ I

/-- **Zeros descend from `K(μ_m)` to a totally complex `K`**, for `m ≠ 1`. -/
theorem dedekindZetaEntire_ne_zero_of_cyclotomic' [FiniteDimensional K L]
    [NumberField.IsTotallyComplex K] (hm : m ≠ 1) {δ : ℝ} (hδ : δ ≤ 1)
    (hL : ∀ s : ℂ, 1 - δ < s.re → s ≠ 1 → Hecke.dedekindZetaEntire L s ≠ 0) :
    ∀ s : ℂ, 1 - δ < s.re → Hecke.dedekindZetaEntire K s ≠ 0 := by
  have : IsMulCommutative (L ≃ₐ[K] L) := IsCyclotomicExtension.isMulCommutative {m} K L
  exact dedekindZetaEntire_ne_zero_of_descent (cyclotomicArtinData K L m)
    (Modulus.infinitePart_eq_empty (cyclotomicModulus K m))
    (by
      rw [cyclotomicModulus_finitePart]
      exact fun h => hm (Ideal.span_singleton_natCast_eq_top_iff.mp h)) hδ hL

end SimultaneousPrimitiveRoots.Unconditional

end
