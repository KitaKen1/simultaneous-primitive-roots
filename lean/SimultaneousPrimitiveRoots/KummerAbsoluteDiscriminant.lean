module

public import SimultaneousPrimitiveRoots.KummerDiscriminant
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Norm

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Polynomial NumberField Algebra Ideal
noncomputable section

theorem primeKummer_root_absolute_norm (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    norm ℚ (AdjoinRoot.root (primeRadicalPolynomial a q)) = (a : ℚ) ^ (q - 1) := by
  rw [← Algebra.norm_norm (S := CyclotomicField q ℚ), primeKummerField_root_norm,
    Algebra.norm_natCast, prime_cyclotomic_degree hq.out]

theorem primeKummerInteger_absolute_norm (a q : ℕ)
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] :
    norm ℤ (primeKummerInteger a q) = (a : ℤ) ^ (q - 1) := by
  apply Int.cast_injective (α := ℚ)
  rw [Algebra.coe_norm_int]
  change norm ℚ (AdjoinRoot.root (primeRadicalPolynomial a q)) = ((a : ℤ) ^ (q - 1) : ℤ)
  simpa only [Int.cast_pow, Int.cast_natCast] using primeKummer_root_absolute_norm a q

/-- The derivative belongs to the actual relative different, without a
monogenicity assertion about the full ring of integers. -/
theorem primeKummer_derivative_mem_different (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    (q : 𝓞 (PrimeKummerField a q)) * (primeKummerInteger a q) ^ (q - 1) ∈
      differentIdeal (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q)) := by
  have hgen : Algebra.adjoin (CyclotomicField q ℚ)
      {algebraMap (𝓞 (PrimeKummerField a q)) (PrimeKummerField a q) (primeKummerInteger a q)} = ⊤ := by
    exact AdjoinRoot.adjoinRoot_eq_top
  have h := aeval_derivative_mem_differentIdeal (𝓞 (CyclotomicField q ℚ))
    (CyclotomicField q ℚ) (L := PrimeKummerField a q) (primeKummerInteger a q) hgen
  rw [primeKummerInteger_relative_minpoly] at h
  simpa only [derivative_sub, derivative_C, derivative_natCast, sub_zero, derivative_X_pow,
    map_mul, map_natCast, map_pow, aeval_X] using h

theorem primeKummer_derivative_absolute_norm (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    norm ℤ ((q : 𝓞 (PrimeKummerField a q)) * (primeKummerInteger a q) ^ (q - 1)) =
      (q : ℤ) ^ (q * (q - 1)) * (a : ℤ) ^ ((q - 1) * (q - 1)) := by
  apply Int.cast_injective (α := ℚ)
  rw [Algebra.coe_norm_int]
  simp only [map_mul, map_natCast, map_pow]
  rw [Algebra.norm_natCast, primeKummerField_absolute_degree ha.out hq.out haq.out]
  change (q : ℚ) ^ (q * (q - 1)) *
    (norm ℚ (AdjoinRoot.root (primeRadicalPolynomial a q))) ^ (q - 1) = _
  rw [primeKummer_root_absolute_norm, ← pow_mul]
  simp

theorem primeKummer_relative_different_norm_dvd (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    (differentIdeal (𝓞 (CyclotomicField q ℚ)) (𝓞 (PrimeKummerField a q))).absNorm ∣
      q ^ (q * (q - 1)) * a ^ ((q - 1) * (q - 1)) := by
  have h := absNorm_dvd_norm_of_mem (primeKummer_derivative_mem_different a q)
  rw [primeKummer_derivative_absolute_norm] at h
  exact_mod_cast h

theorem prime_cyclotomic_discriminant_natAbs (q : ℕ) [hq : Fact q.Prime] :
    (NumberField.discr (CyclotomicField q ℚ)).natAbs = q ^ (q - 2) := by
  let : NeZero q := ⟨hq.out.ne_zero⟩
  rw [IsCyclotomicExtension.Rat.discr_prime q (CyclotomicField q ℚ)]
  simp [Int.natAbs_mul, Int.natAbs_pow]

theorem primeKummer_absolute_discriminant_dvd (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    (NumberField.discr (PrimeKummerField a q)).natAbs ∣
      q ^ (q * (2 * q - 3)) * a ^ ((q - 1) * (q - 1)) := by
  rw [NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow
    (CyclotomicField q ℚ) (𝓞 (CyclotomicField q ℚ))
    (PrimeKummerField a q) (𝓞 (PrimeKummerField a q)),
    primeKummerField_relative_degree ha.out hq.out haq.out,
    prime_cyclotomic_discriminant_natAbs]
  have hd := Nat.mul_dvd_mul_right (primeKummer_relative_different_norm_dvd a q) ((q ^ (q - 2)) ^ q)
  have hexp : q * (q - 1) + (q - 2) * q = q * (2 * q - 3) := by
    have heq : q - 1 + (q - 2) = 2 * q - 3 := by
      have := hq.out.two_le
      omega
    calc
      _ = q * (q - 1 + (q - 2)) := by ring
      _ = _ := by rw [heq]
  have heq : (q ^ (q * (q - 1)) * a ^ ((q - 1) * (q - 1))) *
      (q ^ (q - 2)) ^ q = q ^ (q * (2 * q - 3)) * a ^ ((q - 1) * (q - 1)) := by
    rw [← pow_mul, mul_right_comm, ← pow_add, hexp]
  rw [heq] at hd
  exact hd

theorem primeKummer_absolute_discriminant_le (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    (NumberField.discr (PrimeKummerField a q)).natAbs ≤
      q ^ (q * (2 * q - 3)) * a ^ ((q - 1) * (q - 1)) := by
  exact Nat.le_of_dvd (by have := ha.out; have := hq.out.pos; positivity)
    (primeKummer_absolute_discriminant_dvd a q)

/-- Explicit fixed-base constant for log of the actual absolute field
discriminant. No polynomial discriminant is substituted for the field one. -/
theorem primeKummer_log_discriminant_le (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    Real.log ((NumberField.discr (PrimeKummerField a q)).natAbs : ℝ) ≤
      (2 + Real.log a / Real.log 2) * ((q : ℝ) * ((q : ℝ) - 1)) * Real.log (2 * (q : ℝ)) := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq.out.pos
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.out.one_le
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast (by have := ha.out; omega : 0 < a)
  have hD0 : 0 < ((NumberField.discr (PrimeKummerField a q)).natAbs : ℝ) := by
    exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero (PrimeKummerField a q))
  have hbound := primeKummer_absolute_discriminant_le a q
  have hlogq : 0 ≤ Real.log q := Real.log_natCast_nonneg q
  have hloga : 0 ≤ Real.log a := Real.log_natCast_nonneg a
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2q : Real.log (2 : ℝ) ≤ Real.log (2 * (q : ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlogq2q : Real.log q ≤ Real.log (2 * (q : ℝ)) :=
    Real.log_le_log hq0 (by linarith)
  have he1 : (q * (2 * q - 3) : ℕ) ≤ q * (2 * (q - 1)) := by
    apply Nat.mul_le_mul_left
    have := hq.out.two_le
    omega
  have he2 : (q - 1) * (q - 1) ≤ q * (q - 1) :=
    Nat.mul_le_mul_right (q - 1) (Nat.sub_le q 1)
  have he1R : ((q * (2 * q - 3) : ℕ) : ℝ) ≤ 2 * ((q : ℝ) * ((q : ℝ) - 1)) := by
    have h : ((q * (2 * q - 3) : ℕ) : ℝ) ≤ ((q * (2 * (q - 1)) : ℕ) : ℝ) := by exact_mod_cast he1
    simpa only [Nat.cast_mul, Nat.cast_sub hq.out.one_le, Nat.cast_ofNat, Nat.cast_one,
      mul_left_comm] using h
  have he2R : (((q - 1) * (q - 1) : ℕ) : ℝ) ≤ (q : ℝ) * ((q : ℝ) - 1) := by
    have h : (((q - 1) * (q - 1) : ℕ) : ℝ) ≤ ((q * (q - 1) : ℕ) : ℝ) := by exact_mod_cast he2
    simpa only [Nat.cast_mul, Nat.cast_sub hq.out.one_le, Nat.cast_one] using h
  have hd : 0 ≤ (q : ℝ) * ((q : ℝ) - 1) := mul_nonneg hq0.le (by linarith)
  have hratio : Real.log a ≤ (Real.log a / Real.log 2) * Real.log (2 * (q : ℝ)) := by
    calc
      _ = (Real.log a / Real.log 2) * Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog2q (div_nonneg hloga hlog2.le)
  calc
    _ ≤ Real.log ((q : ℝ) ^ (q * (2 * q - 3)) * (a : ℝ) ^ ((q - 1) * (q - 1))) :=
      Real.log_le_log hD0 (by exact_mod_cast hbound)
    _ = ((q * (2 * q - 3) : ℕ) : ℝ) * Real.log q +
        (((q - 1) * (q - 1) : ℕ) : ℝ) * Real.log a := by
      rw [Real.log_mul (pow_ne_zero _ hq0.ne') (pow_ne_zero _ ha0.ne'), Real.log_pow, Real.log_pow]
    _ ≤ 2 * ((q : ℝ) * ((q : ℝ) - 1)) * Real.log q +
        ((q : ℝ) * ((q : ℝ) - 1)) * Real.log a := by gcongr
    _ ≤ 2 * ((q : ℝ) * ((q : ℝ) - 1)) * Real.log (2 * (q : ℝ)) +
        ((q : ℝ) * ((q : ℝ) - 1)) * ((Real.log a / Real.log 2) * Real.log (2 * (q : ℝ))) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hlogq2q (by positivity))
        (mul_le_mul_of_nonneg_left hratio hd)
    _ = _ := by ring

theorem primeKummer_log_discriminant_normalized_le (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    Real.log ((NumberField.discr (PrimeKummerField a q)).natAbs : ℝ) / ((q : ℝ) - 1) ≤
      (2 + Real.log a / Real.log 2) * (q : ℝ) * Real.log (2 * (q : ℝ)) := by
  have hq1 : 0 < (q : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
    linarith
  apply (div_le_iff₀ hq1).mpr
  convert primeKummer_log_discriminant_le a q using 1 <;> first | rfl | ring

/-- A single explicit constant for every base in the finite set. -/
def kummerDiscriminantConstant (A : Finset ℕ) : ℝ :=
  2 + Real.log (A.sup id + 2 : ℕ) / Real.log 2

theorem kummerDiscriminantConstant_nonneg (A : Finset ℕ) :
    0 ≤ kummerDiscriminantConstant A := by
  unfold kummerDiscriminantConstant
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog : 0 ≤ Real.log (A.sup id + 2 : ℕ) := Real.log_natCast_nonneg _
  positivity

theorem primeKummer_log_discriminant_uniform (A : Finset ℕ) {a q : ℕ} (haA : a ∈ A)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    Real.log ((NumberField.discr (PrimeKummerField a q)).natAbs : ℝ) ≤
      kummerDiscriminantConstant A * ((q : ℝ) * ((q : ℝ) - 1)) * Real.log (2 * (q : ℝ)) := by
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast (by have := ha.out; omega : 0 < a)
  have hsup : (a : ℝ) ≤ (A.sup id + 2 : ℕ) := by
    exact_mod_cast (Finset.le_sup (f := id) haA).trans (Nat.le_add_right (A.sup id) 2)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hc : 2 + Real.log a / Real.log 2 ≤ kummerDiscriminantConstant A := by
    unfold kummerDiscriminantConstant
    gcongr
  have hq1 : 0 ≤ (q : ℝ) - 1 := by
    have h : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
    linarith
  have hlogq : 0 ≤ Real.log (2 * (q : ℝ)) := by
    have h : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
    exact Real.log_nonneg (by linarith)
  exact (primeKummer_log_discriminant_le a q).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (mul_nonneg (Nat.cast_nonneg _) hq1)) hlogq)

/-- The normalized field complexity has the q log q scale needed after
compression. This is an arithmetic bound, not a zero-counting theorem. -/
theorem primeKummer_normalized_complexity_uniform (A : Finset ℕ) {a q : ℕ} (haA : a ∈ A)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] :
    (Real.log ((NumberField.discr (PrimeKummerField a q)).natAbs : ℝ) +
      (Module.finrank ℚ (PrimeKummerField a q) : ℝ)) / ((q : ℝ) - 1) ≤
        (kummerDiscriminantConstant A + 1 / Real.log 2) * (q : ℝ) * Real.log (2 * (q : ℝ)) := by
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
  have hq1 : 0 < (q : ℝ) - 1 := by linarith
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog2q : Real.log (2 : ℝ) ≤ Real.log (2 * (q : ℝ)) :=
    Real.log_le_log (by norm_num) (by linarith)
  have hlog : Real.log ((NumberField.discr (PrimeKummerField a q)).natAbs : ℝ) /
      ((q : ℝ) - 1) ≤ kummerDiscriminantConstant A * (q : ℝ) * Real.log (2 * (q : ℝ)) := by
    apply (div_le_iff₀ hq1).mpr
    convert primeKummer_log_discriminant_uniform A (q := q) haA using 1 <;>
      first | rfl | ring
  have hn : (Module.finrank ℚ (PrimeKummerField a q) : ℝ) / ((q : ℝ) - 1) = q := by
    rw [primeKummerField_absolute_degree ha.out hq.out haq.out,
      Nat.cast_mul, Nat.cast_sub hq.out.one_le, Nat.cast_one]
    field_simp
  have hqlog : (q : ℝ) ≤ (1 / Real.log 2) * (q : ℝ) * Real.log (2 * (q : ℝ)) := by
    calc
      _ = (1 / Real.log 2) * (q : ℝ) * Real.log 2 := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hlog2q (by positivity)
  rw [add_div, hn]
  calc
    _ ≤ kummerDiscriminantConstant A * (q : ℝ) * Real.log (2 * (q : ℝ)) +
        (1 / Real.log 2) * (q : ℝ) * Real.log (2 * (q : ℝ)) := add_le_add hlog hqlog
    _ = _ := by ring

theorem primeKummer_not_dvd_discriminant {a p q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] (hp : p.Prime)
    (hpa : ¬ p ∣ a) (hpq : ¬ p ∣ q) :
    ¬ (p : ℤ) ∣ NumberField.discr (PrimeKummerField a q) := by
  intro h
  have hd : p ∣ (NumberField.discr (PrimeKummerField a q)).natAbs := by
    exact_mod_cast (Int.natAbs_dvd_natAbs.mpr h)
  have hb := hd.trans (primeKummer_absolute_discriminant_dvd a q)
  rcases hp.dvd_mul.mp hb with hq | ha
  · exact hpq (hp.dvd_of_dvd_pow hq)
  · exact hpa (hp.dvd_of_dvd_pow ha)

theorem primeKummer_unramified_away {a p q : ℕ}
    [Fact (2 ≤ a)] [Fact q.Prime] [Fact (a < q)] (hp : p.Prime)
    (hpa : ¬ p ∣ a) (hpq : ¬ p ∣ q) :
    Algebra.IsUnramifiedIn (𝓞 (PrimeKummerField a q)) (Ideal.span {(p : ℤ)}) := by
  exact (NumberField.not_dvd_discr_iff_isUnramifiedIn (PrimeKummerField a q)
    (𝓞 (PrimeKummerField a q)) (Nat.prime_iff_prime_int.mp hp)).mp
      (primeKummer_not_dvd_discriminant hp hpa hpq)

end
end SimultaneousPrimitiveRoots
