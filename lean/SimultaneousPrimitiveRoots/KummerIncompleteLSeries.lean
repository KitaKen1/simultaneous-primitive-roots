module

public import SimultaneousPrimitiveRoots.KummerPrimeSupport

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
open Filter
noncomputable section

/-- The grouped actual Kummer product is the actual ideal-counting
LSeries with precisely the prime factors over a*q deleted. -/
theorem primeKummerIncompleteDedekindEulerL_eq_LSeries (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    {s : ℂ} (hs : 1 < s.re) :
    primeKummerIncompleteDedekindEulerL a q s =
      numberFieldIncompleteZeta (PrimeKummerField a q) (primeKummerTopBadPrimes a q) s := by
  classical
  have h := (primeKummerGoodPrimeFiberEquiv a q).hasProd_iff.mpr
    (numberFieldIncompleteZeta_hasProd (PrimeKummerField a q) (primeKummerTopBadPrimes a q) hs)
  have hraw : HasProd (fun P : Σ v : PrimeKummerEulerPrime a q,
      v.val.asIdeal.primesOver (𝓞 (PrimeKummerField a q)) =>
      (1 - (P.2.val.absNorm : ℂ) ^ (-s))⁻¹)
        (numberFieldIncompleteZeta (PrimeKummerField a q) (primeKummerTopBadPrimes a q) s) :=
    h.congr_fun (fun P => by
      simp only [Function.comp_apply, primeKummerGoodPrimeFiberEquiv_asIdeal])
  exact (hraw.sigma (fun v => hasProd_fintype _)).tprod_eq

/-- The principal character factor is the actual deleted Dedekind
LSeries of the cyclotomic base. -/
theorem primeKummerIncompleteEulerL_principal_eq_LSeries (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    {s : ℂ} (hs : 1 < s.re) :
    primeKummerIncompleteEulerL a q 1 s =
      numberFieldIncompleteZeta (CyclotomicField q ℚ) (primeKummerBaseBadPrimes a q) s := by
  let e : PrimeKummerEulerPrime a q ≃
      {v : HeightOneSpectrum (𝓞 (CyclotomicField q ℚ)) //
        v ∉ primeKummerBaseBadPrimes a q} :=
    Equiv.subtypeEquivRight (primeKummerEulerGood_iff_notMem a q)
  have h := e.hasProd_iff.mpr (numberFieldIncompleteZeta_hasProd (CyclotomicField q ℚ)
    (primeKummerBaseBadPrimes a q) hs)
  have hprincipal := primeKummerIncompleteEulerL_hasProd a q 1 hs
  have hsame : HasProd (fun v : PrimeKummerEulerPrime a q =>
      (1 - (v.val.asIdeal.absNorm : ℂ) ^ (-s))⁻¹)
        (primeKummerIncompleteEulerL a q 1 s) := by
    simpa only [primeKummerEulerTerm, MonoidHom.one_apply, Units.val_one, one_mul]
      using hprincipal
  exact hsame.unique h

/-- Actual ideal-counting factorization on the half-plane of absolute
convergence. This is not an assertion of Hecke continuation. -/
theorem primeKummerIncompleteZeta_factorization (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ : PrimeKummerCharacter a q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    numberFieldIncompleteZeta (PrimeKummerField a q) (primeKummerTopBadPrimes a q) s =
      numberFieldIncompleteZeta (CyclotomicField q ℚ) (primeKummerBaseBadPrimes a q) s *
        (primeKummerIncompleteEulerL a q χ s) ^ (q - 1) := by
  rw [← primeKummerIncompleteDedekindEulerL_eq_LSeries a q hs,
    primeKummerIncompleteDedekindEulerL_factorization a q χ hχ hs,
    primeKummerIncompleteEulerL_principal_eq_LSeries a q hs]

/-- The full Dedekind LSeries occur with their exact finite corrections. -/
theorem primeKummer_dedekindZeta_corrected_factorization (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ : PrimeKummerCharacter a q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta (PrimeKummerField a q) s *
        (∏ P ∈ primeKummerTopBadPrimes a q, (1 - (P.asIdeal.absNorm : ℂ) ^ (-s))) =
      (dedekindZeta (CyclotomicField q ℚ) s *
        (∏ v ∈ primeKummerBaseBadPrimes a q, (1 - (v.asIdeal.absNorm : ℂ) ^ (-s)))) *
          (primeKummerIncompleteEulerL a q χ s) ^ (q - 1) := by
  simpa only [numberFieldIncompleteZeta_eq _ _ hs]
    using primeKummerIncompleteZeta_factorization a q χ hχ hs

/-- The power of the common nonprincipal factor is the exact quotient
of the two deleted ideal-counting LSeries. -/
theorem primeKummerIncompleteEulerL_pow_eq_zeta_quotient (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ : PrimeKummerCharacter a q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    (primeKummerIncompleteEulerL a q χ s) ^ (q - 1) =
      numberFieldIncompleteZeta (PrimeKummerField a q) (primeKummerTopBadPrimes a q) s /
        numberFieldIncompleteZeta (CyclotomicField q ℚ) (primeKummerBaseBadPrimes a q) s := by
  apply (eq_div_iff (numberFieldIncompleteZeta_ne_zero (CyclotomicField q ℚ)
    (primeKummerBaseBadPrimes a q) hs)).mpr
  simpa only [mul_comm] using (primeKummerIncompleteZeta_factorization a q χ hχ hs).symm

/-- The power has a nonzero real right-hand limit at one, obtained
directly from the two actual Dedekind residues. No root branch or
continuation of the individual character factor is constructed. -/
theorem primeKummerIncompleteEulerL_pow_tendsto_residue_quotient (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ : PrimeKummerCharacter a q) (hχ : χ ≠ 1) :
    Tendsto (fun x : ℝ => (primeKummerIncompleteEulerL a q χ x) ^ (q - 1))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds (numberFieldIncompleteZetaResidue (PrimeKummerField a q)
        (primeKummerTopBadPrimes a q) /
          numberFieldIncompleteZetaResidue (CyclotomicField q ℚ)
            (primeKummerBaseBadPrimes a q))) := by
  have h := (numberFieldIncompleteZeta_tendsto_residue (PrimeKummerField a q)
    (primeKummerTopBadPrimes a q)).div
      (numberFieldIncompleteZeta_tendsto_residue (CyclotomicField q ℚ)
        (primeKummerBaseBadPrimes a q))
      (numberFieldIncompleteZetaResidue_ne_zero (CyclotomicField q ℚ)
        (primeKummerBaseBadPrimes a q))
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 1 < x)
  rw [primeKummerIncompleteEulerL_pow_eq_zeta_quotient a q χ hχ (by simpa using hx)]
  exact mul_div_mul_left _ _ (by exact_mod_cast sub_ne_zero.mpr hx.ne')

end
end SimultaneousPrimitiveRoots
