module

public import SimultaneousPrimitiveRoots.NumberFieldIncompleteZeta
public import SimultaneousPrimitiveRoots.KummerIncompleteFactorization

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
noncomputable section

/-- The witness-prime definition is exactly exclusion of the prime
ideals over a*q; it omits no other actual primes. -/
theorem primeKummerEulerGood_iff (a q : ℕ) [Fact q.Prime]
    (v : HeightOneSpectrum (𝓞 (CyclotomicField q ℚ))) :
    PrimeKummerEulerGood a q v ↔ (a * q : 𝓞 (CyclotomicField q ℚ)) ∉ v.asIdeal := by
  obtain ⟨p, hp, hmem⟩ := numberField_exists_rational_prime_support (CyclotomicField q ℚ) v
  constructor
  · rintro ⟨r, hr, hra, hrq, hrv⟩ hbad
    have hpr : p ∣ r := (hmem r).mp hrv
    have hpe : p = r := ((Nat.dvd_prime hr).mp hpr).resolve_left hp.ne_one
    subst r
    have hmul : p ∣ a * q := (hmem (a * q)).mp (by simpa only [Nat.cast_mul] using hbad)
    exact (hp.dvd_mul.mp hmul).elim hra hrq
  · intro hbad
    have hmul : ¬ p ∣ a * q := fun h => hbad (by
      simpa only [Nat.cast_mul] using (hmem (a * q)).mpr h)
    exact ⟨p, hp, fun h => hmul (dvd_mul_of_dvd_left h q),
      fun h => hmul (dvd_mul_of_dvd_right h a), (hmem p).mpr (dvd_refl p)⟩

def primeKummerBaseBadPrimes (a q : ℕ) [Fact (2 ≤ a)] [hq : Fact q.Prime] :
    Finset (HeightOneSpectrum (𝓞 (CyclotomicField q ℚ))) :=
  numberFieldBadPrimes (CyclotomicField q ℚ) (a * q)
    (mul_ne_zero (by have h := Fact.out (p := 2 ≤ a); omega) hq.out.ne_zero)

def primeKummerTopBadPrimes (a q : ℕ)
    [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)] :
    Finset (HeightOneSpectrum (𝓞 (PrimeKummerField a q))) :=
  numberFieldBadPrimes (PrimeKummerField a q) (a * q)
    (mul_ne_zero (by have h := Fact.out (p := 2 ≤ a); omega) hq.out.ne_zero)

theorem primeKummerEulerGood_iff_notMem (a q : ℕ) [Fact (2 ≤ a)] [Fact q.Prime]
    (v : HeightOneSpectrum (𝓞 (CyclotomicField q ℚ))) :
    PrimeKummerEulerGood a q v ↔ v ∉ primeKummerBaseBadPrimes a q := by
  rw [primeKummerEulerGood_iff, primeKummerBaseBadPrimes, numberFieldBadPrimes_mem,
    Nat.cast_mul]

theorem primeKummerTopBadPrimes_mem (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (P : HeightOneSpectrum (𝓞 (PrimeKummerField a q))) :
    P ∈ primeKummerTopBadPrimes a q ↔
      (a * q : 𝓞 (PrimeKummerField a q)) ∈ P.asIdeal := by
  rw [primeKummerTopBadPrimes, numberFieldBadPrimes_mem, Nat.cast_mul]

/-- Actual primes above v, as a fiber of contraction. -/
def numberFieldPrimesOverEquiv (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal.primesOver (𝓞 L) ≃
      {P : HeightOneSpectrum (𝓞 L) // HeightOneSpectrum.under (𝓞 K) P = v} where
  toFun Q := ⟨⟨Q.val, Q.property.1, Ideal.ne_bot_of_mem_primesOver v.ne_bot Q.property⟩,
    HeightOneSpectrum.ext Q.property.2.over.symm⟩
  invFun P := ⟨P.val.asIdeal, P.val.isPrime,
    ⟨congrArg HeightOneSpectrum.asIdeal P.property.symm⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (HeightOneSpectrum.ext rfl)

theorem numberFieldPrimesOverEquiv_asIdeal (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K))
    (Q : v.asIdeal.primesOver (𝓞 L)) :
    (numberFieldPrimesOverEquiv K L v Q).val.asIdeal = Q.val := rfl

theorem primeKummer_under_good_iff (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (P : HeightOneSpectrum (𝓞 (PrimeKummerField a q))) :
    P ∉ primeKummerTopBadPrimes a q ↔
      PrimeKummerEulerGood a q (HeightOneSpectrum.under (𝓞 (CyclotomicField q ℚ)) P) := by
  rw [primeKummerTopBadPrimes_mem, primeKummerEulerGood_iff,
    ← Nat.cast_mul, ← Nat.cast_mul,
    numberField_under_natCast_mem (CyclotomicField q ℚ) (PrimeKummerField a q)]

/-- Regrouping by actual contraction is a bijection on precisely the
primes retained in the incomplete Dedekind product. -/
def primeKummerGoodPrimeFiberEquiv (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] :
    (Σ v : PrimeKummerEulerPrime a q, v.val.asIdeal.primesOver (𝓞 (PrimeKummerField a q))) ≃
      {P : HeightOneSpectrum (𝓞 (PrimeKummerField a q)) //
        P ∉ primeKummerTopBadPrimes a q} :=
  (Equiv.sigmaCongrRight fun v : PrimeKummerEulerPrime a q =>
    numberFieldPrimesOverEquiv (CyclotomicField q ℚ) (PrimeKummerField a q) v.val).trans
      (Equiv.sigmaSubtypeFiberEquivSubtype
        (HeightOneSpectrum.under (𝓞 (CyclotomicField q ℚ)))
        (primeKummer_under_good_iff a q))

theorem primeKummerGoodPrimeFiberEquiv_asIdeal (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (P : Σ v : PrimeKummerEulerPrime a q,
      v.val.asIdeal.primesOver (𝓞 (PrimeKummerField a q))) :
    (primeKummerGoodPrimeFiberEquiv a q P).val.asIdeal = P.2.val := rfl

end
end SimultaneousPrimitiveRoots
