module

public import SimultaneousPrimitiveRoots.Artin.RadicalField

/-!
# The splitting field of `∏_{q ∈ S} (X^q - a)` for an integer `a`

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

/-- Over `𝔽_p` (`p ≠ q`, `q` prime), `X^q - c` (`c ≠ 0`) splits iff `q ∣ p - 1` and
`c^((p-1)/q) = 1`. -/
theorem radical_splits_iff_of_ne_zero {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {c : ZMod p} (hc : c ≠ 0) :
    (X ^ q - C c).Splits ↔ (q ∣ p - 1 ∧ c ^ ((p - 1) / q) = 1) := by
  have : Fact p.Prime := ⟨hp⟩
  constructor
  · intro hs
    have h1 : (X ^ q - 1 : (ZMod p)[X]).Splits := by
      have h := splits_X_pow_sub_one_of_X_pow_sub_C (RingHom.id (ZMod p)) q hc
        (by rwa [Polynomial.map_id])
      rwa [Polynomial.map_id] at h
    have hne1 : (X ^ q - 1 : (ZMod p)[X]) ≠ 0 := by
      have h := X_pow_sub_C_ne_zero hq.pos (1 : ZMod p)
      rwa [C_1] at h
    have hcyc : (cyclotomic q (ZMod p)).Splits :=
      h1.of_dvd hne1 (cyclotomic.dvd_X_pow_sub_one q (ZMod p))
    have hqp : q ∣ p - 1 := (cyclotomic_mod_splits_iff hp hq hpq).mp hcyc
    refine ⟨hqp, ?_⟩
    obtain ⟨β, hβ⟩ := hs.exists_eval_eq_zero (by
      rw [degree_X_pow_sub_C hq.pos]
      exact_mod_cast hq.ne_zero)
    have hβq : β ^ q = c := by
      simpa only [eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] using hβ
    have hβne : β ≠ 0 := by
      intro h0
      rw [h0, zero_pow hq.ne_zero] at hβq
      exact hc hβq.symm
    rw [← hβq, ← pow_mul, Nat.mul_div_cancel' hqp]
    exact ZMod.pow_card_sub_one_eq_one hβne
  · rintro ⟨hqp, hpow⟩
    have hf : (X ^ p - X : (ZMod p)[X]).Splits := by
      simpa only [Nat.card_eq_fintype_card, ZMod.card] using
        (splits_X_pow_nat_card_sub_X (K := ZMod p))
    exact hf.of_dvd (FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) hp.one_lt)
      (radical_dvd_frobeniusPolynomial hp.pos hqp hpow)

/-! ### The field -/

/-- `∏_{q ∈ S} (X^q - a)` over `ℤ`, for `a : ℤ`. -/
def radicalProductInt (a : ℤ) (S : Finset ℕ) : ℤ[X] := ∏ q ∈ S, (X ^ q - C a)

/-- The splitting field over `ℚ` of `∏_{q ∈ S} (X^q - a)`. -/
abbrev RadicalFieldInt (a : ℤ) (S : Finset ℕ) : Type :=
  ((radicalProductInt a S).map (Int.castRingHom ℚ)).SplittingField

instance (a : ℤ) (S : Finset ℕ) : NumberField (RadicalFieldInt a S) :=
  NumberField.of_module_finite ℚ (RadicalFieldInt a S)

instance (a : ℤ) (S : Finset ℕ) : IsGalois ℚ (RadicalFieldInt a S) where
  to_isSeparable := inferInstance
  to_normal := inferInstance

theorem radicalProductInt_map_ne_zero (a : ℤ) {S : Finset ℕ} (hS : ∀ q ∈ S, 0 < q)
    (K : Type*) [Field K] : (radicalProductInt a S).map (algebraMap ℤ K) ≠ 0 := by
  unfold radicalProductInt
  rw [Polynomial.map_prod, Finset.prod_ne_zero_iff]
  intro q' hq'
  rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
  exact X_pow_sub_C_ne_zero (hS q' hq') _

theorem radical_dvd_radicalProductInt (a : ℤ) {S : Finset ℕ} {q : ℕ} (hqS : q ∈ S) :
    (X ^ q - C a : ℤ[X]) ∣ radicalProductInt a S :=
  Finset.dvd_prod_of_mem _ hqS

/-- Each `X^q - a` (`q ∈ S`) splits in `RadicalField a S`. -/
theorem radical_splits_radicalFieldInt (a : ℤ) {S : Finset ℕ} (hS : ∀ q ∈ S, 0 < q)
    {q : ℕ} (hqS : q ∈ S) :
    ((X ^ q - C a : ℤ[X]).map (algebraMap ℤ (RadicalFieldInt a S))).Splits := by
  set f := (radicalProductInt a S).map (Int.castRingHom ℚ)
  have hspl : (f.map (algebraMap ℚ (RadicalFieldInt a S))).Splits := SplittingField.splits f
  have hf : f.map (algebraMap ℚ (RadicalFieldInt a S)) =
      (radicalProductInt a S).map (algebraMap ℤ (RadicalFieldInt a S)) := by
    rw [Polynomial.map_map]
    congr 1
  rw [hf] at hspl
  exact hspl.of_dvd (radicalProductInt_map_ne_zero a hS _)
    (Polynomial.map_dvd _ (radical_dvd_radicalProductInt a hqS))

/-! ### Fixing the roots of `X^q - a` -/

variable {L : Type*} [Field L] [Algebra ℚ L]

/-- `σ` fixes every root of `X^q - a` in `L` (`a : ℤ`). -/
def FixesRadicalInt (a : ℤ) (q : ℕ) (σ : L ≃ₐ[ℚ] L) : Prop :=
  ∀ β ∈ ((X ^ q - C a : ℤ[X]).map (algebraMap ℤ L)).roots, σ β = β

omit [Algebra ℚ L] in
theorem radicalInt_map_ne_zero (a : ℤ) {q : ℕ} (hq : 0 < q) :
    ((X ^ q - C a : ℤ[X]).map (algebraMap ℤ L)) ≠ 0 := by
  rw [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C]
  exact X_pow_sub_C_ne_zero hq _

/-- Fixing the roots of `X^q - a` is invariant under conjugation. -/
theorem fixesRadicalInt_conj_iff (a : ℤ) {q : ℕ} (hq : 0 < q) (σ τ : L ≃ₐ[ℚ] L) :
    FixesRadicalInt a q (τ * σ * τ⁻¹) ↔ FixesRadicalInt a q σ := by
  have hne := radicalInt_map_ne_zero (L := L) a hq
  constructor
  · intro h β hβ
    have h1 := h (τ β) (apply_mem_roots_of_mem_roots hne τ hβ)
    have h2 : τ (σ β) = τ β := by simpa [AlgEquiv.mul_apply] using h1
    exact τ.injective h2
  · intro h β hβ
    have h1 := h _ (apply_mem_roots_of_mem_roots hne τ⁻¹ hβ)
    simp only [AlgEquiv.mul_apply, h1]
    simp

/-- **Frobenius at a power residue** (integer `a`). -/
theorem fixesRadicalInt_iff_powerResidue (a : ℤ) {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    {q : ℕ} (hqS : q ∈ S)
    (𝔭 : HeightOneSpectrum (𝓞 ℚ)) (Q : Ideal (𝓞 (RadicalFieldInt a S))) [Q.IsPrime]
    [Q.LiesOver 𝔭.asIdeal] {σ : RadicalFieldInt a S ≃ₐ[ℚ] RadicalFieldInt a S}
    (hσ : IsArithFrobAt (𝓞 ℚ) σ Q)
    (hpa : (a : ZMod (Ideal.absNorm 𝔭.asIdeal)) ≠ 0) (hpq : Ideal.absNorm 𝔭.asIdeal ≠ q) :
    FixesRadicalInt a q σ ↔
      (q ∣ Ideal.absNorm 𝔭.asIdeal - 1 ∧
        (a : ZMod (Ideal.absNorm 𝔭.asIdeal)) ^ ((Ideal.absNorm 𝔭.asIdeal - 1) / q) = 1) := by
  set p := Ideal.absNorm 𝔭.asIdeal with hpdef
  have hp : p.Prime := by
    rw [hpdef, Rat.HeightOneSpectrum.absNorm_asIdeal]
    exact Rat.HeightOneSpectrum.prime_natGenerator 𝔭
  have : Fact p.Prime := ⟨hp⟩
  have hq := hS q hqS
  have hmonic : (X ^ q - C a : ℤ[X]).Monic := monic_X_pow_sub_C _ hq.ne_zero
  have hmodp : (X ^ q - C a : ℤ[X]).map (Int.castRingHom (ZMod p)) =
      X ^ q - C (a : ZMod p) := by
    simp [Polynomial.map_sub, Polynomial.map_pow]
  have hsep : ((X ^ q - C a : ℤ[X]).map (Int.castRingHom (ZMod p))).Separable := by
    rw [hmodp]
    have hpq' : ¬ p ∣ q := fun h => hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h)
    exact separable_X_pow_sub_C' p q (a : ZMod p) hpq' hpa
  have key := frobenius_fixes_roots_iff_splits 𝔭 Q hσ hmonic
    (radical_splits_radicalFieldInt a (fun q' hq' => (hS q' hq').pos) hqS) hsep
  rw [hmodp] at key
  unfold FixesRadicalInt
  rw [key]
  exact radical_splits_iff_of_ne_zero hp hq hpq hpa

end SimultaneousPrimitiveRoots.Artin

end
