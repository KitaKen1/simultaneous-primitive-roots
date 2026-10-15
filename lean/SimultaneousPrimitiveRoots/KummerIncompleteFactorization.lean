module

public import SimultaneousPrimitiveRoots.KummerEulerLocalFactor

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
noncomputable section

/-- The reciprocal local Dedekind factor, over actual primes above v. -/
def primeKummerGoodDedekindFactor (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (s : ℂ) (v : PrimeKummerEulerPrime a q) : ℂ :=
  ∏ P : v.val.asIdeal.primesOver (𝓞 (PrimeKummerField a q)),
    (1 - (P.val.absNorm : ℂ) ^ (-s))⁻¹

/-- The grouped actual Dedekind Euler product away from a*q.
This definition does not identify the product with a Dedekind L-series. -/
def primeKummerIncompleteDedekindEulerL (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] (s : ℂ) : ℂ :=
  ∏' v : PrimeKummerEulerPrime a q, primeKummerGoodDedekindFactor a q s v

theorem primeKummer_goodPrime_dedekind_reciprocalFactor (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (v : PrimeKummerEulerPrime a q) (s : ℂ) :
    primeKummerGoodDedekindFactor a q s v =
      ∏ χ : PrimeKummerCharacter a q, (1 - primeKummerEulerTerm a q χ s v)⁻¹ := by
  classical
  rw [primeKummerGoodDedekindFactor, Finset.prod_inv_distrib,
    primeKummer_goodPrime_dedekind_eulerFactor, ← Finset.prod_inv_distrib]

/-- A genuine limit of the actual grouped Dedekind factors in Re(s)>1. -/
theorem primeKummerIncompleteDedekindEulerL_hasProd (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (primeKummerGoodDedekindFactor a q s)
      (∏ χ : PrimeKummerCharacter a q, primeKummerIncompleteEulerL a q χ s) := by
  have h := hasProd_prod (s := (Finset.univ : Finset (PrimeKummerCharacter a q)))
    (fun χ _ => primeKummerIncompleteEulerL_hasProd a q χ hs)
  have hf : primeKummerGoodDedekindFactor a q s =
      (fun v => ∏ χ : PrimeKummerCharacter a q, (1 - primeKummerEulerTerm a q χ s v)⁻¹) := by
    funext v
    exact primeKummer_goodPrime_dedekind_reciprocalFactor a q v s
  rw [hf]
  exact h

/-- The incomplete actual Dedekind Euler product factors into the
convergent character Euler products. Ramified factors are still omitted. -/
theorem primeKummerIncompleteDedekindEulerL_eq_product (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    {s : ℂ} (hs : 1 < s.re) :
    primeKummerIncompleteDedekindEulerL a q s =
      ∏ χ : PrimeKummerCharacter a q, primeKummerIncompleteEulerL a q χ s :=
  (primeKummerIncompleteDedekindEulerL_hasProd a q hs).tprod_eq

theorem primeKummerIncompleteDedekindEulerL_ne_zero (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    {s : ℂ} (hs : 1 < s.re) :
    primeKummerIncompleteDedekindEulerL a q s ≠ 0 := by
  rw [primeKummerIncompleteDedekindEulerL_eq_product a q hs]
  exact Finset.prod_ne_zero_iff.mpr (fun χ _ => primeKummerIncompleteEulerL_ne_zero a q χ hs)

/-- The principal part and one nonprincipal factor suffice for the
entire convergent incomplete actual Dedekind Euler product. -/
theorem primeKummerIncompleteDedekindEulerL_factorization (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (χ : PrimeKummerCharacter a q) (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    primeKummerIncompleteDedekindEulerL a q s =
      primeKummerIncompleteEulerL a q 1 s *
        (primeKummerIncompleteEulerL a q χ s) ^ (q - 1) := by
  classical
  rw [primeKummerIncompleteDedekindEulerL_eq_product a q hs]
  have he := Finset.prod_subtype (p := fun ψ : PrimeKummerCharacter a q => ψ ≠ 1)
    (F := primeKummerNonprincipalCharacter_fintype a q)
    (Finset.univ.erase 1) (fun _ => by simp)
    (fun ψ => primeKummerIncompleteEulerL a q ψ s)
  rw [← primeKummer_nonprincipal_incompleteEulerL_product a q χ hχ hs, ← he]
  exact (Finset.mul_prod_erase (Finset.univ : Finset (PrimeKummerCharacter a q))
    (fun ψ => primeKummerIncompleteEulerL a q ψ s) (Finset.mem_univ 1)).symm

end
end SimultaneousPrimitiveRoots
