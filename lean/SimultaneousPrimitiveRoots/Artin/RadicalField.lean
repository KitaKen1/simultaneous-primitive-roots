module

public import SimultaneousPrimitiveRoots.Artin.FrobeniusRoots
public import SimultaneousPrimitiveRoots.FiniteFieldKummer
public import Mathlib.FieldTheory.AbelRuffini
public import Mathlib.Algebra.Algebra.Rat

/-!
# The splitting field of `∏_{q ∈ S} (X^q - a)` and Frobenius at power residues

For a finite set `S` of primes, `RadicalField a S` is the splitting field over `ℚ` of
`∏_{q ∈ S} (X^q - a)`. For a rational prime `p ∤ a` not in `S`, an arithmetic Frobenius `σ` at a
prime above `p` fixes the roots of `X^q - a` (`q ∈ S`) exactly when

`q ∣ p - 1` and `a^((p-1)/q) = 1 (mod p)`,

i.e. when `p` is an exceptional prime for `a` at `q` (`fixesRadical_iff_powerResidue`).
The condition "`σ` fixes the roots of `X^q - a`" is invariant under conjugation
(`fixesRadical_conj_iff`), so the primes at which `a` is not a `q`-th power residue for any
`q ∈ S` are the primes whose Frobenius class lies in a union of conjugacy classes.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Artin

open Polynomial NumberField IsDedekindDomain

/-! ### Finite fields -/

/-- Over `𝔽_p` (`p ∤ qa`, `q` prime), `X^q - a` splits iff `q ∣ p - 1` and
`a^((p-1)/q) = 1`. -/
theorem radical_splits_iff {a p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (ha : ¬ p ∣ a) :
    (X ^ q - C (a : ZMod p)).Splits ↔ (q ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / q) = 1) := by
  have : Fact p.Prime := ⟨hp⟩
  constructor
  · intro hs
    have ha0 : (a : ZMod p) ≠ 0 := fun h => ha ((ZMod.natCast_eq_zero_iff a p).mp h)
    have h1 : (X ^ q - 1 : (ZMod p)[X]).Splits := by
      have h := splits_X_pow_sub_one_of_X_pow_sub_C (RingHom.id (ZMod p)) q ha0
        (by rwa [Polynomial.map_id])
      rwa [Polynomial.map_id] at h
    have hne1 : (X ^ q - 1 : (ZMod p)[X]) ≠ 0 := by
      have h := X_pow_sub_C_ne_zero hq.pos (1 : ZMod p)
      rwa [C_1] at h
    have hcyc : (cyclotomic q (ZMod p)).Splits :=
      h1.of_dvd hne1 (cyclotomic.dvd_X_pow_sub_one q (ZMod p))
    have hqp : q ∣ p - 1 := (cyclotomic_mod_splits_iff hp hq hpq).mp hcyc
    exact ⟨hqp, (powerResidue_iff_radical_splits hp hq.pos hqp ha).mpr hs⟩
  · rintro ⟨hqp, hpow⟩
    exact (powerResidue_iff_radical_splits hp hq.pos hqp ha).mp hpow

/-! ### The field -/

/-- `∏_{q ∈ S} (X^q - a)` over `ℤ`. -/
def radicalProduct (a : ℕ) (S : Finset ℕ) : ℤ[X] := ∏ q ∈ S, (X ^ q - C (a : ℤ))

/-- The splitting field over `ℚ` of `∏_{q ∈ S} (X^q - a)`. -/
abbrev RadicalField (a : ℕ) (S : Finset ℕ) : Type :=
  ((radicalProduct a S).map (Int.castRingHom ℚ)).SplittingField

instance (a : ℕ) (S : Finset ℕ) : NumberField (RadicalField a S) :=
  NumberField.of_module_finite ℚ (RadicalField a S)

instance (a : ℕ) (S : Finset ℕ) : IsGalois ℚ (RadicalField a S) where
  to_isSeparable := inferInstance
  to_normal := by
    have hn := Polynomial.SplittingField.instNormal
      ((radicalProduct a S).map (Int.castRingHom ℚ))
    convert hn using 1
    rfl

theorem radicalProduct_map_ne_zero (a : ℕ) {S : Finset ℕ} (hS : ∀ q ∈ S, 0 < q)
    (K : Type*) [Field K] : (radicalProduct a S).map (algebraMap ℤ K) ≠ 0 := by
  unfold radicalProduct
  rw [Polynomial.map_prod, Finset.prod_ne_zero_iff]
  intro q' hq'
  rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
  exact X_pow_sub_C_ne_zero (hS q' hq') _

theorem radical_dvd_radicalProduct (a : ℕ) {S : Finset ℕ} {q : ℕ} (hqS : q ∈ S) :
    (X ^ q - C (a : ℤ) : ℤ[X]) ∣ radicalProduct a S :=
  Finset.dvd_prod_of_mem _ hqS

/-- Each `X^q - a` (`q ∈ S`) splits in `RadicalField a S`. -/
theorem radical_splits_radicalField (a : ℕ) {S : Finset ℕ} (hS : ∀ q ∈ S, 0 < q)
    {q : ℕ} (hqS : q ∈ S) :
    ((X ^ q - C (a : ℤ) : ℤ[X]).map (algebraMap ℤ (RadicalField a S))).Splits := by
  set f := (radicalProduct a S).map (Int.castRingHom ℚ)
  have hspl : (f.map (algebraMap ℚ (RadicalField a S))).Splits := SplittingField.splits f
  have hf : f.map (algebraMap ℚ (RadicalField a S)) =
      (radicalProduct a S).map (algebraMap ℤ (RadicalField a S)) := by
    rw [Polynomial.map_map]
    congr 1
  rw [hf] at hspl
  exact hspl.of_dvd (radicalProduct_map_ne_zero a hS _)
    (Polynomial.map_dvd _ (radical_dvd_radicalProduct a hqS))

/-! ### Fixing the roots of `X^q - a` -/

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- `σ` fixes every root of `X^q - a` in `L`. -/
def FixesRadical (a q : ℕ) (σ : L ≃ₐ[ℚ] L) : Prop :=
  ∀ β ∈ ((X ^ q - C (a : ℤ) : ℤ[X]).map (algebraMap ℤ L)).roots, σ β = β

/-- Automorphisms permute the roots of an integer polynomial. -/
theorem apply_mem_roots_of_mem_roots {g : ℤ[X]} (hg : g.map (algebraMap ℤ L) ≠ 0)
    (τ : L ≃ₐ[ℚ] L) {β : L} (hβ : β ∈ (g.map (algebraMap ℤ L)).roots) :
    τ β ∈ (g.map (algebraMap ℤ L)).roots := by
  rw [mem_roots hg, IsRoot, eval_map_algebraMap] at hβ ⊢
  have h := Polynomial.aeval_algHom_apply ((τ : L →ₐ[ℚ] L).restrictScalars ℤ) β g
  rw [hβ, map_zero] at h
  exact h

omit [Algebra ℚ L] in
theorem radical_map_ne_zero (a : ℕ) {q : ℕ} (hq : 0 < q) :
    ((X ^ q - C (a : ℤ) : ℤ[X]).map (algebraMap ℤ L)) ≠ 0 := by
  rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
  exact X_pow_sub_C_ne_zero hq _

/-- Fixing the roots of `X^q - a` is invariant under conjugation. -/
theorem fixesRadical_conj_iff (a : ℕ) {q : ℕ} (hq : 0 < q) (σ τ : L ≃ₐ[ℚ] L) :
    FixesRadical a q (τ * σ * τ⁻¹) ↔ FixesRadical a q σ := by
  have hne := radical_map_ne_zero (L := L) a hq
  constructor
  · intro h β hβ
    have h1 := h (τ β) (apply_mem_roots_of_mem_roots hne τ hβ)
    have h2 : τ (σ β) = τ β := by simpa [AlgEquiv.mul_apply] using h1
    exact τ.injective h2
  · intro h β hβ
    have h1 := h _ (apply_mem_roots_of_mem_roots hne τ⁻¹ hβ)
    simp only [AlgEquiv.mul_apply, h1]
    simp

/-- **Frobenius at a power residue.** For `L = RadicalField a S`, a prime `𝔭` of `ℚ` with
`p = N𝔭 ∤ a`, `p ∉ S`, `q ∈ S` prime and an arithmetic Frobenius `σ` at a prime `Q` above `𝔭`:
`σ` fixes the roots of `X^q - a` iff `q ∣ p - 1` and `a^((p-1)/q) = 1` in `𝔽_p`. -/
theorem fixesRadical_iff_powerResidue (a : ℕ) {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    {q : ℕ} (hqS : q ∈ S)
    (𝔭 : HeightOneSpectrum (𝓞 ℚ)) (Q : Ideal (𝓞 (RadicalField a S))) [Q.IsPrime]
    [Q.LiesOver 𝔭.asIdeal] {σ : RadicalField a S ≃ₐ[ℚ] RadicalField a S}
    (hσ : IsArithFrobAt (𝓞 ℚ) σ Q)
    (hpa : ¬ Ideal.absNorm 𝔭.asIdeal ∣ a) (hpq : Ideal.absNorm 𝔭.asIdeal ≠ q) :
    FixesRadical a q σ ↔
      (q ∣ Ideal.absNorm 𝔭.asIdeal - 1 ∧
        (a : ZMod (Ideal.absNorm 𝔭.asIdeal)) ^ ((Ideal.absNorm 𝔭.asIdeal - 1) / q) = 1) := by
  set p := Ideal.absNorm 𝔭.asIdeal with hpdef
  have hp : p.Prime := by
    rw [hpdef, Rat.HeightOneSpectrum.absNorm_asIdeal]
    exact Rat.HeightOneSpectrum.prime_natGenerator 𝔭
  have : Fact p.Prime := ⟨hp⟩
  have hq := hS q hqS
  have hmonic : (X ^ q - C (a : ℤ) : ℤ[X]).Monic := monic_X_pow_sub_C _ hq.ne_zero
  have hmodp : (X ^ q - C (a : ℤ) : ℤ[X]).map (Int.castRingHom (ZMod p)) =
      X ^ q - C (a : ZMod p) := by
    simp [Polynomial.map_sub, Polynomial.map_pow]
  have hsep : ((X ^ q - C (a : ℤ) : ℤ[X]).map (Int.castRingHom (ZMod p))).Separable := by
    rw [hmodp]
    have hpq' : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
    exact separable_X_pow_sub_C' p q (a : ZMod p) hpq'
      (fun hz => hpa ((ZMod.natCast_eq_zero_iff a p).mp hz))
  have key := frobenius_fixes_roots_iff_splits 𝔭 Q hσ hmonic
    (radical_splits_radicalField a (fun q' hq' => (hS q' hq').pos) hqS) hsep
  rw [hmodp] at key
  unfold FixesRadical
  rw [key]
  exact radical_splits_iff hp hq hpq hpa

end SimultaneousPrimitiveRoots.Artin

end
