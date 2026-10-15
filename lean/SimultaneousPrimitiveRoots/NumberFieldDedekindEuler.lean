module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Restrict

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
noncomputable section

/-- The actual ideal-counting Dedekind LSeries is the unrestricted
Euler product over actual nonzero prime ideals. -/
theorem numberField_dedekindZeta_hasProd (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun P : HeightOneSpectrum (𝓞 K) =>
      (1 - (P.asIdeal.absNorm : ℂ) ^ (-s))⁻¹) (dedekindZeta K s) :=
  TauCeti.dedekindZeta_eulerProduct_hasProd hs

/-- Pointwise nonvanishing only in the absolute-convergence half-plane. -/
theorem numberField_dedekindZeta_ne_zero (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) : dedekindZeta K s ≠ 0 :=
  TauCeti.dedekindZeta_ne_zero_of_one_lt_re hs

/-- Deleting any finite set of actual prime Euler factors has the
corresponding exact ideal-counting LSeries expression. No continuation
or uniform zero estimate is asserted. -/
theorem numberField_dedekindZeta_delete_factors (K : Type*) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) {s : ℂ} (hs : 1 < s.re) :
    LSeries (TauCeti.normCoeff K
      (TauCeti.MultiplicativeIdealWeight.ofBadPrimes (S : Set (HeightOneSpectrum (𝓞 K)))
        S.finite_toSet).toIdealArithmeticFunction) s =
      dedekindZeta K s * ∏ P ∈ S, (1 - (P.asIdeal.absNorm : ℂ) ^ (-s)) :=
  TauCeti.LSeries_ofBadPrimes S hs

end
end SimultaneousPrimitiveRoots
