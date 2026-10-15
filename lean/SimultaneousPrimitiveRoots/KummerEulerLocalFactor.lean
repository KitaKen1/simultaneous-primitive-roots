module

public import SimultaneousPrimitiveRoots.KummerFrobeniusLocal
public import SimultaneousPrimitiveRoots.KummerCharacterEuler

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

/-- Reverse the already proved character polynomial to obtain the local
Euler denominator, without constructing a representation or its determinant. -/
theorem primeKummer_character_eulerFactor (a q : ℕ)
    [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    (σ : Gal(PrimeKummerField a q/CyclotomicField q ℚ)) (z : ℂ) :
    (∏ χ : PrimeKummerCharacter a q, (1 - (χ σ : ℂ) * z)) =
      if σ = 1 then (1 - z) ^ q else 1 - z ^ q := by
  classical
  by_cases hz : z = 0
  · subst z
    simp [hq.out.ne_zero]
  have hpoly := congrArg (Polynomial.eval z⁻¹) (primeKummer_character_polynomial a q σ)
  have hprod : (∏ χ : PrimeKummerCharacter a q, (1 - (χ σ : ℂ) * z)) =
      z ^ q * ∏ χ : PrimeKummerCharacter a q, (z⁻¹ - (χ σ : ℂ)) := by
    calc
      _ = ∏ χ : PrimeKummerCharacter a q, z * (z⁻¹ - (χ σ : ℂ)) := by
        apply Finset.prod_congr rfl
        intro χ _
        rw [mul_sub, mul_inv_cancel₀ hz]
        ring
      _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
          ← Nat.card_eq_fintype_card, primeKummerCharacter_card]
  rw [hprod]
  split_ifs with hσ
  · rw [if_pos hσ] at hpoly
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_one] at hpoly
    rw [hpoly, ← mul_pow]
    congr 1
    rw [mul_sub, mul_inv_cancel₀ hz, mul_one]
  · rw [if_neg hσ] at hpoly
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_one] at hpoly
    rw [hpoly, mul_sub, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hz), mul_one]

/-- Character factors agree with the splitting data of an actual good
prime, using only the degree-one criterion and the fundamental identity. -/
theorem primeKummer_goodPrime_characterFactor (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (v : PrimeKummerEulerPrime a q) (z : ℂ) :
    (∏ χ : PrimeKummerCharacter a q,
      (1 - (χ (primeKummerBaseFrobenius a q v.val) : ℂ) * z)) =
    (1 - z ^ (primeKummerPrimeAbove a q v.val).asIdeal.inertiaDeg
      (𝓞 (CyclotomicField q ℚ))) ^
      (v.val.asIdeal.primesOver (𝓞 (PrimeKummerField a q))).ncard := by
  classical
  rw [primeKummer_character_eulerFactor,
    primeKummer_goodPrime_inertiaDeg a q v _ (primeKummerPrimeAbove_contraction a q v.val),
    primeKummer_goodPrime_count]
  split_ifs <;> simp only [pow_one]

/-- All actual primes above a base prime have the same norm, expressed
using the relative residue degree of the chosen prime above it. -/
theorem primeKummer_primeOver_absNorm (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (v : HeightOneSpectrum (𝓞 (CyclotomicField q ℚ)))
    (P : v.asIdeal.primesOver (𝓞 (PrimeKummerField a q))) :
    P.val.absNorm = v.asIdeal.absNorm ^
      (primeKummerPrimeAbove a q v).asIdeal.inertiaDeg (𝓞 (CyclotomicField q ℚ)) := by
  let := primeKummer_relative_galois a q
  let : P.val.IsPrime := P.property.1
  let : P.val.LiesOver v.asIdeal := P.property.2
  let : (primeKummerPrimeAbove a q v).asIdeal.LiesOver v.asIdeal :=
    ⟨(primeKummerPrimeAbove_contraction a q v).symm⟩
  rw [← Ideal.absNorm_pow_inertiaDeg v.asIdeal P.val,
    Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal P.val
      (primeKummerPrimeAbove a q v).asIdeal Gal(PrimeKummerField a q/CyclotomicField q ℚ)]

/-- The genuine local Dedekind denominator equals the product of the
actual Frobenius-character denominators at every prime away from a*q. -/
theorem primeKummer_goodPrime_dedekind_eulerFactor (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (v : PrimeKummerEulerPrime a q) (s : ℂ) :
    (∏ P : v.val.asIdeal.primesOver (𝓞 (PrimeKummerField a q)),
      (1 - (P.val.absNorm : ℂ) ^ (-s))) =
    ∏ χ : PrimeKummerCharacter a q, (1 - primeKummerEulerTerm a q χ s v) := by
  classical
  simp only [primeKummerEulerTerm]
  rw [primeKummer_goodPrime_characterFactor]
  have hterm (P : v.val.asIdeal.primesOver (𝓞 (PrimeKummerField a q))) :
      (P.val.absNorm : ℂ) ^ (-s) =
        ((v.val.asIdeal.absNorm : ℂ) ^ (-s)) ^
          (primeKummerPrimeAbove a q v.val).asIdeal.inertiaDeg
            (𝓞 (CyclotomicField q ℚ)) := by
    rw [primeKummer_primeOver_absNorm, Nat.cast_pow,
      ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
  calc
    _ = ∏ _P : v.val.asIdeal.primesOver (𝓞 (PrimeKummerField a q)),
        (1 - ((v.val.asIdeal.absNorm : ℂ) ^ (-s)) ^
          (primeKummerPrimeAbove a q v.val).asIdeal.inertiaDeg
            (𝓞 (CyclotomicField q ℚ))) := by
      apply Finset.prod_congr rfl
      intro P _
      rw [hterm]
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, Set.fintypeCard_eq_ncard]

end
end SimultaneousPrimitiveRoots
