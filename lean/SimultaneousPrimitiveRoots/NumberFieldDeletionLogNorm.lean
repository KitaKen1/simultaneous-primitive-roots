module

public import SimultaneousPrimitiveRoots.NumberFieldDeletionCardinality

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
noncomputable section
open Classical

/-- Keep the full product of the distinct prime norms, rather than replacing
each norm by two as in the earlier cardinality estimate. -/
theorem numberFieldBadPrimes_prod_norm_le (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : n ≠ 0) :
    (∏ P ∈ numberFieldBadPrimes K n hn, P.asIdeal.absNorm) ≤ n ^ Module.finrank ℚ K := by
  let S := numberFieldBadPrimes K n hn
  let I := Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K))
  have hI : I ≠ 0 := by
    simpa [I, Ideal.span_singleton_eq_bot] using (Nat.cast_ne_zero.mpr hn : (n : 𝓞 K) ≠ 0)
  have hprod : (∏ P ∈ S.image (fun P => P.asIdeal), P) ∣ I := by
    apply Finset.prod_primes_dvd
    · intro P hP
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hP
      exact Ideal.prime_of_isPrime v.ne_bot v.isPrime
    · intro P hP
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hP
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact (numberFieldBadPrimes_mem K n hn v).mp hv
  have hi : Set.InjOn (fun P : HeightOneSpectrum (𝓞 K) => P.asIdeal) S :=
    fun _ _ _ _ h => HeightOneSpectrum.ext h
  calc
    _ = ∏ P ∈ S.image (fun P => P.asIdeal), Ideal.absNorm P := (Finset.prod_image hi).symm
    _ = Ideal.absNorm (∏ P ∈ S.image (fun P => P.asIdeal), P) := (map_prod Ideal.absNorm _ _).symm
    _ ≤ Ideal.absNorm I := Nat.le_of_dvd
      (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)) (map_dvd Ideal.absNorm hprod)
    _ = _ := by
      dsimp [I]
      rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]

theorem numberFieldBadPrimes_sum_log_norm_le (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : n ≠ 0) :
    (∑ P ∈ numberFieldBadPrimes K n hn, Real.log (P.asIdeal.absNorm : ℝ)) ≤
      (Module.finrank ℚ K : ℝ) * Real.log n := by
  have hp : 0 < (∏ P ∈ numberFieldBadPrimes K n hn, (P.asIdeal.absNorm : ℝ)) :=
    Finset.prod_pos fun P _ => by
      have hh : 2 ≤ P.asIdeal.absNorm := NumberField.HeightOneSpectrum.one_lt_absNorm P
      exact_mod_cast (Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hh)
  have hle : (∏ P ∈ numberFieldBadPrimes K n hn, (P.asIdeal.absNorm : ℝ)) ≤
      (n : ℝ) ^ Module.finrank ℚ K := by
    exact_mod_cast numberFieldBadPrimes_prod_norm_le K n hn
  have h := Real.log_le_log hp hle
  rw [Real.log_prod (fun P _ => by
    have hh : 2 ≤ P.asIdeal.absNorm := NumberField.HeightOneSpectrum.one_lt_absNorm P
    exact_mod_cast (Nat.ne_of_gt (Nat.lt_of_lt_of_le (by norm_num : 0 < 2) hh))), Real.log_pow] at h
  exact h

end
end SimultaneousPrimitiveRoots
