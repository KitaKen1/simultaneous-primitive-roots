module

public import SimultaneousPrimitiveRoots.NumberFieldPrimeSupport
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
noncomputable section
open Classical

/-- The unique rational prime below an actual prime ideal, selected from
its already-proved exact integer divisibility criterion. -/
def numberFieldPrimeBelow (K : Type*) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) : Nat.Primes :=
  ⟨(numberField_exists_rational_prime_support K P).choose,
    (numberField_exists_rational_prime_support K P).choose_spec.1⟩

theorem numberFieldPrimeBelow_mem_iff (K : Type*) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (n : 𝓞 K) ∈ P.asIdeal ↔ (numberFieldPrimeBelow K P).1 ∣ n :=
  (numberField_exists_rational_prime_support K P).choose_spec.2 n

theorem numberFieldPrimeBelow_eq_iff_mem (K : Type*) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) (p : Nat.Primes) :
    numberFieldPrimeBelow K P = p ↔ (p.1 : 𝓞 K) ∈ P.asIdeal := by
  rw [numberFieldPrimeBelow_mem_iff]
  constructor
  · intro h
    rw [h]
  · intro h
    apply Subtype.ext
    exact (Nat.prime_dvd_prime_iff_eq (numberFieldPrimeBelow K P).2 p.2).mp h

theorem numberFieldPrimeBelow_eq_iff_liesOver (K : Type*) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) (p : Nat.Primes) :
    numberFieldPrimeBelow K P = p ↔ P.asIdeal.LiesOver (Ideal.span {(p.1 : ℤ)}) := by
  letI : Fact p.1.Prime := ⟨p.2⟩
  letI : (Ideal.span {(p.1 : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p.1
  rw [Ideal.liesOver_iff_dvd_map P.isPrime.ne_top, Ideal.dvd_iff_le]
  simp only [Ideal.map_span, Set.image_singleton, map_natCast, Ideal.span_singleton_le_iff_mem]
  exact numberFieldPrimeBelow_eq_iff_mem K P p

/-- The fiber over a rational prime is exactly the actual ideal set
primesOver, with no norm or ramification condition added. -/
def numberFieldPrimeFiberEquiv (K : Type*) [Field K] [NumberField K]
    (p : Nat.Primes) : {P : HeightOneSpectrum (𝓞 K) // numberFieldPrimeBelow K P = p} ≃
      (Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 K) where
  toFun P := ⟨P.1.asIdeal, P.1.isPrime,
    (numberFieldPrimeBelow_eq_iff_liesOver K P.1 p).mp P.2⟩
  invFun Q :=
    let hp0 : Ideal.span ({(p.1 : ℤ)} : Set ℤ) ≠ ⊥ := by simp [p.2.ne_zero]
    let P : HeightOneSpectrum (𝓞 K) :=
      ⟨Q.1, Q.2.1, Ideal.ne_bot_of_mem_primesOver hp0 Q.2⟩
    ⟨P, (numberFieldPrimeBelow_eq_iff_liesOver K P p).mpr Q.2.2⟩
  left_inv P := by apply Subtype.ext; rfl
  right_inv Q := by apply Subtype.ext; rfl

/-- Reindex all actual prime ideals by their rational prime and the
finite fiber of ideals above it. -/
def numberFieldPrimeIdealSigmaEquiv (K : Type*) [Field K] [NumberField K] :
    (Σ p : Nat.Primes, (Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 K)) ≃
      HeightOneSpectrum (𝓞 K) :=
  (Equiv.sigmaCongrRight fun p => (numberFieldPrimeFiberEquiv K p).symm).trans
    (Equiv.sigmaFiberEquiv (numberFieldPrimeBelow K))

theorem numberFieldPrimeIdealSigmaEquiv_asIdeal (K : Type*) [Field K] [NumberField K]
    (v : Σ p : Nat.Primes, (Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 K)) :
    (numberFieldPrimeIdealSigmaEquiv K v).asIdeal = v.2.1 := rfl

/-- A convenient order for prime-power sums: (rational prime, exponent),
then a finite fiber of actual prime ideals. -/
def numberFieldPrimePowerSigmaEquiv (K : Type*) [Field K] [NumberField K] :
    (Σ pe : Nat.Primes × ℕ, (Ideal.span {(pe.1.1 : ℤ)}).primesOver (𝓞 K)) ≃
      HeightOneSpectrum (𝓞 K) × ℕ :=
  let reorder :
      (Σ pe : Nat.Primes × ℕ, (Ideal.span {(pe.1.1 : ℤ)}).primesOver (𝓞 K)) ≃
        (Σ p : Nat.Primes, (Ideal.span {(p.1 : ℤ)}).primesOver (𝓞 K)) × ℕ :=
    { toFun := fun v => (⟨v.1.1, v.2⟩, v.1.2)
      invFun := fun v => ⟨(v.1.1, v.2), v.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  reorder.trans (Equiv.prodCongr (numberFieldPrimeIdealSigmaEquiv K) (Equiv.refl ℕ))

theorem numberFieldPrimePowerSigmaEquiv_asIdeal (K : Type*) [Field K] [NumberField K]
    (v : Σ pe : Nat.Primes × ℕ, (Ideal.span {(pe.1.1 : ℤ)}).primesOver (𝓞 K)) :
    (numberFieldPrimePowerSigmaEquiv K v).1.asIdeal = v.2.1 := rfl

theorem numberFieldPrimePowerSigmaEquiv_exponent (K : Type*) [Field K] [NumberField K]
    (v : Σ pe : Nat.Primes × ℕ, (Ideal.span {(pe.1.1 : ℤ)}).primesOver (𝓞 K)) :
    (numberFieldPrimePowerSigmaEquiv K v).2 = v.1.2 := rfl

end
end SimultaneousPrimitiveRoots
