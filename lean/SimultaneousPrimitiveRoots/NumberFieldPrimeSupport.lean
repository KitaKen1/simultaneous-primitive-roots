module

public import SimultaneousPrimitiveRoots.NumberFieldDedekindEuler
public import TauCeti.RingTheory.DedekindDomain.PrimesAbove
public import Mathlib.RingTheory.Ideal.NatInt

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
noncomputable section

/-- Every actual prime ideal has one rational-prime support, with an
exact divisibility criterion for natural numbers. -/
theorem numberField_exists_rational_prime_support (K : Type*) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    ∃ p : ℕ, p.Prime ∧ ∀ n : ℕ, (n : 𝓞 K) ∈ v.asIdeal ↔ p ∣ n := by
  let w := HeightOneSpectrum.under ℤ v
  obtain ⟨p, hp, hw⟩ := (Ideal.isPrime_int_iff.mp w.isPrime).resolve_left w.ne_bot
  refine ⟨p, hp, fun n => ?_⟩
  have hmem : (n : ℤ) ∈ w.asIdeal ↔ (n : 𝓞 K) ∈ v.asIdeal := by
    simp only [w, HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, map_natCast]
  rw [← hmem, hw, Ideal.mem_span_singleton]
  exact Int.natCast_dvd_natCast

/-- Only finitely many prime ideals contain a given nonzero integer. -/
theorem numberField_finite_prime_support (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : n ≠ 0) :
    {v : HeightOneSpectrum (𝓞 K) | (n : 𝓞 K) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span ({(n : 𝓞 K)} : Set (𝓞 K)) ≠ 0 := by
    simpa using (Nat.cast_ne_zero.mpr hn : (n : 𝓞 K) ≠ 0)
  exact (Ideal.finite_factors hI).subset fun v hv =>
    Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hv))

/-- The actual finite set of Euler factors over the prime divisors of n. -/
def numberFieldBadPrimes (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : n ≠ 0) : Finset (HeightOneSpectrum (𝓞 K)) :=
  (numberField_finite_prime_support K n hn).toFinset

theorem numberFieldBadPrimes_mem (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : n ≠ 0) (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ numberFieldBadPrimes K n hn ↔ (n : 𝓞 K) ∈ v.asIdeal :=
  Set.Finite.mem_toFinset _

/-- Contraction preserves membership of every rational integer. -/
theorem numberField_under_natCast_mem (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 L)) (n : ℕ) :
    (n : 𝓞 K) ∈ (HeightOneSpectrum.under (𝓞 K) v).asIdeal ↔
      (n : 𝓞 L) ∈ v.asIdeal := by
  simp only [HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, map_natCast]

end
end SimultaneousPrimitiveRoots
