module

public import SimultaneousPrimitiveRoots.NumberFieldPrimeSupport
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.HigherPrimePowers

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
noncomputable section
open Classical

/-- A deliberately coarse bound, sufficient after choosing a small smoothing exponent. -/
theorem numberFieldBadPrimes_card_le (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : n ≠ 0) :
    (numberFieldBadPrimes K n hn).card ≤ n * Module.finrank ℚ K := by
  let S := numberFieldBadPrimes K n hn
  have hspan : Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)) ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using (Nat.cast_ne_zero.mpr hn : (n : 𝓞 K) ≠ 0)
  have himg : (S.image (fun P => P.asIdeal)).card = S.card :=
    Finset.card_image_of_injective _ fun _ _ h => HeightOneSpectrum.ext h
  have hpow : 2 ^ S.card ≤ n ^ Module.finrank ℚ K := by
    rw [← himg, ← RingOfIntegers.rank, ← Ideal.absNorm_span_natCast]
    apply TauCeti.two_pow_card_le_absNorm hspan
    · intro P hP
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hP
      exact Ideal.prime_of_isPrime v.ne_bot v.isPrime
    · intro P hP
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hP
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact (numberFieldBadPrimes_mem K n hn v).mp hv
  have hu : n ^ Module.finrank ℚ K ≤ 2 ^ (n * Module.finrank ℚ K) := by
    rw [pow_mul]
    exact Nat.pow_le_pow_left (Nat.lt_two_pow_self.le) (Module.finrank ℚ K)
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp (hpow.trans hu)

end
end SimultaneousPrimitiveRoots
