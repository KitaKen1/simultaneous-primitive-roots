module

public import SimultaneousPrimitiveRoots.NumberFieldFrobeniusDegree
public import SimultaneousPrimitiveRoots.KummerEulerTransport
public import Mathlib.NumberTheory.RamificationInertia.Galois

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
open scoped Classical
noncomputable section

/-- Every prime above a good base prime is actually unramified. -/
theorem primeKummer_goodPrime_unramified (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (v : PrimeKummerEulerPrime a q)
    (P : HeightOneSpectrum (𝓞 (PrimeKummerField a q)))
    (hPv : P.asIdeal.comap
      (algebraMap (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q))) = v.val.asIdeal) :
    Algebra.IsUnramifiedAt (𝓞 (CyclotomicField q ℚ)) P.asIdeal := by
  obtain ⟨p, hp, hpa, hpq, hpv⟩ := v.property
  have hpP : (p : 𝓞 (PrimeKummerField a q)) ∈ P.asIdeal := by
    rw [← hPv, Ideal.mem_comap, map_natCast] at hpv
    exact hpv
  exact primeKummer_relative_unramified_away hp hpa hpq P hpP

/-- Identity of the actual base Frobenius is the residue-degree-one test
at any prime above it. -/
theorem primeKummerBaseFrobenius_eq_one_iff_inertiaDeg_one (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (v : PrimeKummerEulerPrime a q)
    (P : HeightOneSpectrum (𝓞 (PrimeKummerField a q)))
    (hPv : P.asIdeal.comap
      (algebraMap (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q))) = v.val.asIdeal) :
    primeKummerBaseFrobenius a q v.val = 1 ↔
      P.asIdeal.inertiaDeg (𝓞 (CyclotomicField q ℚ)) = 1 := by
  let := primeKummer_relative_galois a q
  let := primeKummer_goodPrime_unramified a q v P hPv
  rw [primeKummerBaseFrobenius_eq a q v.val P hPv]
  exact numberFieldFrobenius_eq_one_iff_inertiaDeg_one P

/-- The fundamental identity specialized to the actual unramified
prime-degree Kummer extension. -/
theorem primeKummer_goodPrime_count_mul_inertiaDeg (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (v : PrimeKummerEulerPrime a q)
    (P : HeightOneSpectrum (𝓞 (PrimeKummerField a q)))
    (hPv : P.asIdeal.comap
      (algebraMap (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q))) = v.val.asIdeal) :
    (v.val.asIdeal.primesOver (𝓞 (PrimeKummerField a q))).ncard *
      P.asIdeal.inertiaDeg (𝓞 (CyclotomicField q ℚ)) = q := by
  let := primeKummer_relative_galois a q
  let : P.asIdeal.LiesOver v.val.asIdeal := ⟨hPv.symm⟩
  let := primeKummer_goodPrime_unramified a q v P hPv
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    v.val.asIdeal (𝓞 (PrimeKummerField a q))
      Gal(PrimeKummerField a q/CyclotomicField q ℚ)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx v.val.asIdeal P.asIdeal
      Gal(PrimeKummerField a q/CyclotomicField q ℚ),
    Ideal.inertiaDegIn_eq_inertiaDeg v.val.asIdeal P.asIdeal
      Gal(PrimeKummerField a q/CyclotomicField q ℚ),
    Ideal.ramificationIdx_eq_one P.asIdeal (𝓞 (CyclotomicField q ℚ)),
    one_mul, primeKummer_relative_galois_card] at h
  exact h

/-- The two possible residue degrees are determined by actual Frobenius. -/
theorem primeKummer_goodPrime_inertiaDeg (a q : ℕ)
    [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    (v : PrimeKummerEulerPrime a q)
    (P : HeightOneSpectrum (𝓞 (PrimeKummerField a q)))
    (hPv : P.asIdeal.comap
      (algebraMap (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q))) = v.val.asIdeal) :
    P.asIdeal.inertiaDeg (𝓞 (CyclotomicField q ℚ)) =
      if primeKummerBaseFrobenius a q v.val = 1 then 1 else q := by
  classical
  have hcount := primeKummer_goodPrime_count_mul_inertiaDeg a q v P hPv
  have hdvd : P.asIdeal.inertiaDeg (𝓞 (CyclotomicField q ℚ)) ∣ q :=
    ⟨(v.val.asIdeal.primesOver (𝓞 (PrimeKummerField a q))).ncard,
      by simpa only [mul_comm] using hcount.symm⟩
  have hiff := primeKummerBaseFrobenius_eq_one_iff_inertiaDeg_one a q v P hPv
  split_ifs with hσ
  · exact hiff.mp hσ
  · exact (hq.out.eq_one_or_self_of_dvd _ hdvd).resolve_left (mt hiff.mpr hσ)

/-- Split or inert: the actual number of primes is q or one. -/
theorem primeKummer_goodPrime_count (a q : ℕ)
    [Fact (2 ≤ a)] [hq : Fact q.Prime] [Fact (a < q)]
    (v : PrimeKummerEulerPrime a q) :
    (v.val.asIdeal.primesOver (𝓞 (PrimeKummerField a q))).ncard =
      if primeKummerBaseFrobenius a q v.val = 1 then q else 1 := by
  classical
  have h := primeKummer_goodPrime_count_mul_inertiaDeg a q v
    (primeKummerPrimeAbove a q v.val) (primeKummerPrimeAbove_contraction a q v.val)
  rw [primeKummer_goodPrime_inertiaDeg a q v _
    (primeKummerPrimeAbove_contraction a q v.val)] at h
  split_ifs at h ⊢ with hσ
  · simpa only [mul_one] using h
  · nlinarith [hq.out.pos]

/-- Actual prime norms have exactly the two corresponding shapes. -/
theorem primeKummer_goodPrime_absNorm (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)]
    (v : PrimeKummerEulerPrime a q)
    (P : HeightOneSpectrum (𝓞 (PrimeKummerField a q)))
    (hPv : P.asIdeal.comap
      (algebraMap (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q))) = v.val.asIdeal) :
    P.asIdeal.absNorm = if primeKummerBaseFrobenius a q v.val = 1
      then v.val.asIdeal.absNorm else v.val.asIdeal.absNorm ^ q := by
  classical
  let : P.asIdeal.LiesOver v.val.asIdeal := ⟨hPv.symm⟩
  rw [← Ideal.absNorm_pow_inertiaDeg v.val.asIdeal P.asIdeal,
    primeKummer_goodPrime_inertiaDeg a q v P hPv]
  split_ifs <;> simp only [pow_one]

end
end SimultaneousPrimitiveRoots
