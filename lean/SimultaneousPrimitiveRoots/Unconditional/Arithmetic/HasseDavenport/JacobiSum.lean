module

public import Mathlib.NumberTheory.JacobiSum.Basic
public import SimultaneousPrimitiveRoots.Unconditional.Arithmetic.HasseDavenport.GaussSum

/-!
# The Hasse--Davenport lifting relation for Jacobi sums

Let `K / k` be an extension of finite fields of degree `n` and let `χ`, `φ` be multiplicative
characters of `k` such that `χ`, `φ` and `χ * φ` are nontrivial. Then the Jacobi sum of the lifted
characters `χ ∘ N_{K/k}` and `φ ∘ N_{K/k}` is

`J(χ ∘ N, φ ∘ N) = (-1) ^ (n - 1) * J(χ, φ) ^ n`.

This is the Davenport--Hasse Jacobi lifting formula used in
`verification/stage7-sources/A-02.tex`, lines 501--516, with `χ = φ = ρ` a character such that
`ρ` and `ρ²` are nontrivial.

It follows from the Hasse--Davenport relation for Gauss sums (`hasseDavenport_gaussSum`) and the
relation `g(χ * φ) * J(χ, φ) = g(χ) * g(φ)` (`jacobiSum_mul_nontrivial`), applied over `k` and
over `K`, by cancelling the nonzero Gauss sum `g(χ * φ) ^ n`.

## Main results

* `hasseDavenport_jacobiSum_of_isPrimitive`: the formula for characters with values in a
  commutative domain `R` that carries a primitive additive character of `k` (and in which the
  cardinality of `k` is not zero).
* `hasseDavenport_jacobiSum_of_ringChar_ne`: the formula for characters with values in a
  commutative domain whose characteristic is different from that of `k`. The additive character
  is found in a cyclotomic extension of the fraction field.
* `hasseDavenport_jacobiSum`: the formula for characters with values in a commutative domain of
  characteristic zero, for instance `ℂ`.
* `hasseDavenport_jacobiSum_self`: the case `χ = φ = ρ` with `ρ` and `ρ ^ 2` nontrivial, in the
  form in which the paper uses the formula.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Arithmetic

/-- The cancellation step in the proof of the Hasse--Davenport relation for Jacobi sums: here `e`
is the sign `(-1) ^ (n - 1)`, `G`, `A`, `B` are the Gauss sums of `χ * φ`, `χ`, `φ`, and `J`, `J'`
are the Jacobi sum and its lift. -/
theorem hasseDavenport_jacobiSum_aux {R : Type*} [CommRing R] {e G A B J J' : R} {n : ℕ}
    (he : e * e = 1) (hJ : G * J = A * B)
    (hJ' : e * G ^ n * J' = e * A ^ n * (e * B ^ n)) :
    G ^ n * J' = G ^ n * (e * J ^ n) := by
  have hJn : G ^ n * J ^ n = A ^ n * B ^ n := by rw [← mul_pow, hJ, mul_pow]
  linear_combination e * hJ' - G ^ n * J' * he - e * hJn + e * A ^ n * B ^ n * he

section JacobiSum

variable {k : Type*} [Field k] [Fintype k] (K : Type*) [Field K] [Fintype K] [Algebra k K]
  {R : Type*} [CommRing R] [IsDomain R]

/-- **The Hasse--Davenport lifting relation for Jacobi sums**, for characters with values in a
commutative domain `R` in which the cardinality of `k` is not zero and which carries a primitive
additive character `ψ` of `k`. -/
theorem hasseDavenport_jacobiSum_of_isPrimitive (hcard : (Fintype.card k : R) ≠ 0)
    {χ φ : MulChar k R} (hχ : χ ≠ 1) (hφ : φ ≠ 1) (hχφ : χ * φ ≠ 1) {ψ : AddChar k R}
    (hψ : ψ.IsPrimitive) :
    jacobiSum (normLift K χ) (normLift K φ) =
      (-1) ^ (Module.finrank k K - 1) * jacobiSum χ φ ^ Module.finrank k K := by
  have he : (-1 : R) ^ (Module.finrank k K - 1) * (-1) ^ (Module.finrank k K - 1) = 1 := by
    rw [← mul_pow, neg_mul_neg, one_mul, one_pow]
  have hg : gaussSum (χ * φ) ψ ^ Module.finrank k K ≠ 0 :=
    pow_ne_zero _ (gaussSum_ne_zero_of_nontrivial hcard hχφ hψ)
  have hJ : gaussSum (χ * φ) ψ * jacobiSum χ φ = gaussSum χ ψ * gaussSum φ ψ :=
    jacobiSum_mul_nontrivial hχφ ψ
  have hJ' : gaussSum (normLift K (χ * φ)) (traceLift K ψ) *
      jacobiSum (normLift K χ) (normLift K φ) =
        gaussSum (normLift K χ) (traceLift K ψ) * gaussSum (normLift K φ) (traceLift K ψ) := by
    rw [normLift_mul]
    exact jacobiSum_mul_nontrivial (by rw [← normLift_mul]; exact normLift_ne_one K hχφ) _
  rw [hasseDavenport_gaussSum' K hχ ψ, hasseDavenport_gaussSum' K hφ ψ,
    hasseDavenport_gaussSum' K hχφ ψ] at hJ'
  exact mul_left_cancel₀ hg (hasseDavenport_jacobiSum_aux he hJ hJ')

/-- **The Hasse--Davenport lifting relation for Jacobi sums**, for characters with values in a
commutative domain `R` whose characteristic is different from the characteristic of `k`. -/
theorem hasseDavenport_jacobiSum_of_ringChar_ne (h : ringChar R ≠ ringChar k) {χ φ : MulChar k R}
    (hχ : χ ≠ 1) (hφ : φ ≠ 1) (hχφ : χ * φ ≠ 1) :
    jacobiSum (normLift K χ) (normLift K φ) =
      (-1) ^ (Module.finrank k K - 1) * jacobiSum χ φ ^ Module.finrank k K := by
  have hF : ringChar (FractionRing R) ≠ ringChar k := by
    have : CharP (FractionRing R) (ringChar R) :=
      charP_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R)) (ringChar R)
    rwa [ringChar.eq (FractionRing R) (ringChar R)]
  obtain ⟨n, hp, hc⟩ := FiniteField.card k (ringChar k)
  -- A primitive additive character of `k` with values in a cyclotomic extension `FF` of the
  -- fraction field of `R`.
  let ψ := AddChar.FiniteField.primitiveChar k (FractionRing R) hF
  let FF := CyclotomicField ψ.n (FractionRing R)
  let f : R →+* FF := (algebraMap (FractionRing R) FF).comp (algebraMap R (FractionRing R))
  have hinj : Function.Injective f :=
    (algebraMap (FractionRing R) FF).injective.comp (IsFractionRing.injective R (FractionRing R))
  have hcard : (Fintype.card k : FF) ≠ 0 := by
    intro H
    simp only [hc, Nat.cast_pow, ne_eq, PNat.ne_zero, not_false_eq_true, pow_eq_zero_iff] at H
    exact hF <| (Algebra.ringChar_eq (FractionRing R) FF).trans <|
      CharP.ringChar_of_prime_eq_zero hp H
  apply hinj
  rw [← jacobiSum_ringHomComp, map_mul, map_pow, map_pow, map_neg, map_one,
    ← jacobiSum_ringHomComp, ← normLift_ringHomComp, ← normLift_ringHomComp]
  exact hasseDavenport_jacobiSum_of_isPrimitive K hcard
    ((MulChar.ringHomComp_ne_one_iff hinj).mpr hχ) ((MulChar.ringHomComp_ne_one_iff hinj).mpr hφ)
    (by rw [← MulChar.ringHomComp_mul]; exact (MulChar.ringHomComp_ne_one_iff hinj).mpr hχφ)
    ψ.prim

/-- **The Hasse--Davenport lifting relation for Jacobi sums.** Let `K / k` be an extension of
finite fields of degree `n` and let `χ`, `φ` be multiplicative characters of `k` with values in a
commutative domain of characteristic zero (for instance `ℂ`) such that `χ`, `φ` and `χ * φ` are
nontrivial. Then `J(χ ∘ N_{K/k}, φ ∘ N_{K/k}) = (-1) ^ (n - 1) * J(χ, φ) ^ n`. -/
theorem hasseDavenport_jacobiSum [CharZero R] {χ φ : MulChar k R} (hχ : χ ≠ 1) (hφ : φ ≠ 1)
    (hχφ : χ * φ ≠ 1) :
    jacobiSum (normLift K χ) (normLift K φ) =
      (-1) ^ (Module.finrank k K - 1) * jacobiSum χ φ ^ Module.finrank k K :=
  hasseDavenport_jacobiSum_of_ringChar_ne K
    (by rw [ringChar.eq_zero]; exact (CharP.ringChar_ne_zero_of_finite k).symm) hχ hφ hχφ

/-- The case `χ = φ = ρ` of the Hasse--Davenport lifting relation for Jacobi sums, as used in
`verification/stage7-sources/A-02.tex`, lines 506--511: if `ρ` and `ρ ^ 2` are nontrivial, then
`J(ρ ∘ N_{K/k}, ρ ∘ N_{K/k}) = (-1) ^ (n - 1) * J(ρ, ρ) ^ n`. -/
theorem hasseDavenport_jacobiSum_self [CharZero R] {ρ : MulChar k R} (hρ : ρ ≠ 1)
    (hρ2 : ρ ^ 2 ≠ 1) :
    jacobiSum (normLift K ρ) (normLift K ρ) =
      (-1) ^ (Module.finrank k K - 1) * jacobiSum ρ ρ ^ Module.finrank k K :=
  hasseDavenport_jacobiSum K hρ hρ (by rwa [← sq])

end JacobiSum

end SimultaneousPrimitiveRoots.Unconditional.Arithmetic
