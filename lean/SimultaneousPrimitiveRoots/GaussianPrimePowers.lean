module

public import SimultaneousPrimitiveRoots.GaussianPrimeCounting
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField Ideal

attribute [local instance] Int.ideal_span_isMaximal_of_prime Ideal.Quotient.field

noncomputable section
open Classical

/-- Actual residue degree above the rational prime, common to all primes in
a Galois number field. -/
def rationalPrimeResidueDegree (K : Type*) [Field K] [NumberField K] (p : ℕ) : ℕ :=
  (span {(p : ℤ)}).inertiaDegIn (𝓞 K)

def rationalPrimeIdealCount (K : Type*) [Field K] [NumberField K] (p : ℕ) : ℕ :=
  ((span {(p : ℤ)}).primesOver (𝓞 K)).ncard

theorem rationalPrimeResidueDegree_pos (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {p : ℕ} [Fact p.Prime] : 0 < rationalPrimeResidueDegree K p := by
  exact Nat.pos_of_ne_zero (Ideal.inertiaDegIn_ne_zero (B := 𝓞 K) (p := span {(p : ℤ)}) Gal(K/ℚ))

theorem rationalPrimeIdealCount_mul_degree_le (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {p : ℕ} [Fact p.Prime] :
    rationalPrimeIdealCount K p * rationalPrimeResidueDegree K p ≤ Module.finrank ℚ K := by
  have hf := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (span {(p : ℤ)}) (𝓞 K) Gal(K/ℚ)
  rw [IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K] at hf
  have hr : 1 ≤ (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) :=
    Nat.one_le_iff_ne_zero.mpr (Ideal.ramificationIdxIn_ne_zero (B := 𝓞 K) (p := span {(p : ℤ)}) Gal(K/ℚ))
  have h := Nat.mul_le_mul_left (((span {(p : ℤ)}).primesOver (𝓞 K)).ncard)
    (Nat.mul_le_mul_right ((span {(p : ℤ)}).inertiaDegIn (𝓞 K)) hr)
  simpa only [Nat.one_mul, hf, rationalPrimeIdealCount, rationalPrimeResidueDegree] using h

theorem galois_prime_absNorm_eq_power {K : Type*} [Field K] [NumberField K]
    [IsGalois ℚ K] {p : ℕ} [Fact p.Prime]
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    P.absNorm = p ^ rationalPrimeResidueDegree K p := by
  rw [rationalPrimeResidueDegree, Ideal.inertiaDegIn_eq_inertiaDeg
    (span {(p : ℤ)}) P Gal(K/ℚ)]
  exact (Ideal.pow_inertiaDeg p P).symm

theorem degreeOnePrimeIdealCount_eq_galois (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {p : ℕ} [hp : Fact p.Prime] :
    degreeOnePrimeIdealCount K p =
      if rationalPrimeResidueDegree K p = 1 then rationalPrimeIdealCount K p else 0 := by
  have hnorm : ∀ P ∈ (span {(p : ℤ)}).primesOver (𝓞 K),
      P.absNorm = p ↔ rationalPrimeResidueDegree K p = 1 := by
    intro P hP
    let : P.IsPrime := hP.1
    let : P.LiesOver (span {(p : ℤ)}) := hP.2
    rw [galois_prime_absNorm_eq_power (p := p) P]
    constructor
    · intro h
      exact pow_right_injective₀ hp.out.pos (by have := hp.out.two_le; omega)
        (h.trans (pow_one p).symm)
    · intro h
      rw [h, pow_one]
  unfold degreeOnePrimeIdealCount
  split_ifs with hf
  · have hset : {P : Ideal (𝓞 K) | P ∈ (span {(p : ℤ)}).primesOver (𝓞 K) ∧ P.absNorm = p} =
        (span {(p : ℤ)}).primesOver (𝓞 K) := by
      ext P
      exact ⟨fun h => h.1, fun h => ⟨h, (hnorm P h).mpr hf⟩⟩
    rw [hset]
    rfl
  · have hset : {P : Ideal (𝓞 K) | P ∈ (span {(p : ℤ)}).primesOver (𝓞 K) ∧ P.absNorm = p} =
        ∅ := by
      ext P
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => hf ((hnorm P h.1).mp h.2)
    rw [hset, Set.ncard_empty]

/-- j=0 is the first prime-ideal power; higher j retain every higher power,
including contributions above ramified rational primes. -/
def gaussianPrimePowerTerm (K : Type*) [Field K] [NumberField K] (x : ℝ) (p j : ℕ) : ℝ :=
  if p.Prime then (rationalPrimeIdealCount K p : ℝ) *
    (rationalPrimeResidueDegree K p : ℝ) * Real.log p *
    artinGaussianWeight (((p : ℝ) ^ ((j + 1) * rationalPrimeResidueDegree K p)) / x) else 0

def gaussianPrimePowerTrace (K : Type*) [Field K] [NumberField K] (x : ℝ) : ℝ :=
  ∑' p : ℕ, ∑' j : ℕ, gaussianPrimePowerTerm K x p j

theorem gaussianPrimePowerTerm_nonneg (K : Type*) [Field K] [NumberField K]
    (x : ℝ) (p j : ℕ) : 0 ≤ gaussianPrimePowerTerm K x p j := by
  unfold gaussianPrimePowerTerm
  split_ifs
  · exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Real.log_natCast_nonneg _)) (artinGaussianWeight_pos _).le
  · exact le_rfl

theorem artinGaussianWeight_natPower_le {t x : ℝ} (ht : 0 < t) (hx : 0 < x) (m : ℕ) :
    artinGaussianWeight (t ^ m / x) ≤
      Real.exp ((Real.log 2) ^ 2 + 9 / 4) * x ^ (3 : ℕ) * (t ^ (3 : ℕ))⁻¹ ^ m := by
  have hw := artinGaussianWeight_le_rpow (div_pos (pow_pos ht m) hx) (3 : ℝ)
  have heq : (t ^ m / x) ^ (-3 : ℝ) = x ^ (3 : ℕ) * (t ^ (3 : ℕ))⁻¹ ^ m := by
    rw [Real.div_rpow (pow_pos ht m).le hx.le, Real.rpow_neg (pow_pos ht m).le,
      Real.rpow_neg hx.le]
    norm_num only [Real.rpow_ofNat]
    rw [← pow_mul, Nat.mul_comm m 3, pow_mul, inv_pow]
    field_simp
  norm_num only [show (3 : ℝ) ^ 2 = 9 by norm_num] at hw
  simpa only [heq, mul_assoc] using hw

/-- Grouping the actual finite set of prime ideals gives the term used in
the trace. No zeta or Hecke identity is assumed. -/
theorem gaussianPrimePowerTerm_eq_primeIdeal_sum (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] (x : ℝ) {p : ℕ} [hp : Fact p.Prime] (j : ℕ) :
    gaussianPrimePowerTerm K x p j =
      ∑ P ∈ (Algebra.QuasiFinite.finite_primesOver (span {(p : ℤ)}) (S := 𝓞 K)).toFinset,
        Real.log (P.absNorm : ℝ) * artinGaussianWeight ((P.absNorm : ℝ) ^ (j + 1) / x) := by
  have hterm : ∀ P ∈ (Algebra.QuasiFinite.finite_primesOver
      (span {(p : ℤ)}) (S := 𝓞 K)).toFinset,
      Real.log (P.absNorm : ℝ) * artinGaussianWeight ((P.absNorm : ℝ) ^ (j + 1) / x) =
        (rationalPrimeResidueDegree K p : ℝ) * Real.log p *
          artinGaussianWeight (((p : ℝ) ^ ((j + 1) * rationalPrimeResidueDegree K p)) / x) := by
    intro P hP
    have hP' : P ∈ (span {(p : ℤ)}).primesOver (𝓞 K) := by simpa using hP
    let : P.IsPrime := hP'.1
    let : P.LiesOver (span {(p : ℤ)}) := hP'.2
    rw [galois_prime_absNorm_eq_power (p := p) P, Nat.cast_pow, Real.log_pow, ← pow_mul,
      Nat.mul_comm (rationalPrimeResidueDegree K p) (j + 1)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
  rw [gaussianPrimePowerTerm, if_pos hp.out]
  rw [rationalPrimeIdealCount, Set.ncard_eq_toFinset_card _
    (Algebra.QuasiFinite.finite_primesOver _)]
  ring

/-- A separable inverse-square/geometric majorant proves convergence of
all prime powers without a prime number theorem. -/
theorem gaussianPrimePowerTerm_le_majorant (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {x : ℝ} (hx : 0 < x) (p j : ℕ) :
    gaussianPrimePowerTerm K x p j ≤
      ((Module.finrank ℚ K : ℝ) * Real.exp ((Real.log 2) ^ 2 + 9 / 4) * x ^ (3 : ℕ)) *
        (p : ℝ) ^ (-2 : ℝ) * (1 / 2 : ℝ) ^ j := by
  unfold gaussianPrimePowerTerm
  split_ifs with hp
  · let : Fact p.Prime := ⟨hp⟩
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hf : 1 ≤ rationalPrimeResidueDegree K p := rationalPrimeResidueDegree_pos K
    have hc : (rationalPrimeIdealCount K p : ℝ) * (rationalPrimeResidueDegree K p : ℝ) ≤
        (Module.finrank ℚ K : ℝ) := by exact_mod_cast rationalPrimeIdealCount_mul_degree_le K
    have hl : Real.log (p : ℝ) ≤ (p : ℝ) := (Real.log_le_sub_one_of_pos hp0).trans (by linarith)
    let r : ℝ := ((p : ℝ) ^ (3 : ℕ))⁻¹
    have hr0 : 0 ≤ r := by positivity
    have hrhalf : r ≤ 1 / 2 := by
      have hp3 : (2 : ℝ) ≤ (p : ℝ) ^ (3 : ℕ) := by
        have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hp2 3
        norm_num at h3
        linarith
      simpa only [r, one_div] using
        (inv_le_inv₀ (pow_pos hp0 3) (by norm_num : (0 : ℝ) < 2)).mpr hp3
    have hw := artinGaussianWeight_natPower_le hp0 hx
      ((j + 1) * rationalPrimeResidueDegree K p)
    have hpw : r ^ ((j + 1) * rationalPrimeResidueDegree K p) ≤ r ^ (j + 1) :=
      pow_le_pow_of_le_one hr0 (by linarith) (Nat.le_mul_of_pos_right _ (by omega))
    have hj : r ^ j ≤ (1 / 2 : ℝ) ^ j := pow_le_pow_left₀ hr0 hrhalf j
    have heq : (p : ℝ) * r = (p : ℝ) ^ (-2 : ℝ) := by
      rw [Real.rpow_neg hp0.le]
      norm_num only [Real.rpow_ofNat]
      dsimp [r]
      field_simp
    calc
      _ ≤ (Module.finrank ℚ K : ℝ) * (p : ℝ) *
          (Real.exp ((Real.log 2) ^ 2 + 9 / 4) * x ^ (3 : ℕ) * r ^ (j + 1)) := by
        apply mul_le_mul (mul_le_mul hc hl (Real.log_natCast_nonneg _) (Nat.cast_nonneg _))
          (hw.trans (mul_le_mul_of_nonneg_left hpw (by positivity)))
          (artinGaussianWeight_pos _).le (by positivity)
      _ = ((Module.finrank ℚ K : ℝ) * Real.exp ((Real.log 2) ^ 2 + 9 / 4) * x ^ (3 : ℕ)) *
          (p : ℝ) ^ (-2 : ℝ) * r ^ j := by
        rw [pow_succ r j]
        calc
          _ = ((Module.finrank ℚ K : ℝ) * Real.exp ((Real.log 2) ^ 2 + 9 / 4) * x ^ (3 : ℕ)) *
              ((p : ℝ) * r) * r ^ j := by ring
          _ = _ := by rw [heq]
      _ ≤ _ := mul_le_mul_of_nonneg_left hj (by positivity)
  · positivity

theorem gaussianPrimePowerTerm_summable (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {x : ℝ} (hx : 0 < x) (p : ℕ) :
    Summable (gaussianPrimePowerTerm K x p) := by
  apply ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).mul_left
      (((Module.finrank ℚ K : ℝ) * Real.exp ((Real.log 2) ^ 2 + 9 / 4) * x ^ (3 : ℕ)) *
        (p : ℝ) ^ (-2 : ℝ))).of_norm_bounded
  intro j
  rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPrimePowerTerm_nonneg K x p j)]
  exact gaussianPrimePowerTerm_le_majorant K hx p j

theorem gaussianPrimePower_sum_le_majorant (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {x : ℝ} (hx : 0 < x) (p : ℕ) :
    (∑' j : ℕ, gaussianPrimePowerTerm K x p j) ≤
      (2 * (Module.finrank ℚ K : ℝ) * Real.exp ((Real.log 2) ^ 2 + 9 / 4) * x ^ (3 : ℕ)) *
        (p : ℝ) ^ (-2 : ℝ) := by
  have hg := summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  have h := (gaussianPrimePowerTerm_summable K hx p).tsum_le_tsum
    (gaussianPrimePowerTerm_le_majorant K hx p) (hg.mul_left
      (((Module.finrank ℚ K : ℝ) * Real.exp ((Real.log 2) ^ 2 + 9 / 4) * x ^ (3 : ℕ)) *
        (p : ℝ) ^ (-2 : ℝ)))
  rw [hg.tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)] at h
  norm_num only [show (1 - (1 / 2 : ℝ))⁻¹ = 2 by norm_num] at h
  convert h using 1 <;> first | rfl | ring

theorem gaussianPrimePowerTrace_summable (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {x : ℝ} (hx : 0 < x) :
    Summable (fun p : ℕ => ∑' j : ℕ, gaussianPrimePowerTerm K x p j) := by
  have hs : Summable (fun p : ℕ => (p : ℝ) ^ (-2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  apply (hs.mul_left (2 * (Module.finrank ℚ K : ℝ) *
    Real.exp ((Real.log 2) ^ 2 + 9 / 4) * x ^ (3 : ℕ))).of_norm_bounded
  intro p
  rw [Real.norm_eq_abs, abs_of_nonneg (tsum_nonneg (fun j => gaussianPrimePowerTerm_nonneg K x p j))]
  exact gaussianPrimePower_sum_le_majorant K hx p

theorem gaussianPrimePowerPair_summable (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {x : ℝ} (hx : 0 < x) :
    Summable (fun pj : ℕ × ℕ => gaussianPrimePowerTerm K x pj.1 pj.2) :=
  (summable_prod_of_nonneg (fun pj => gaussianPrimePowerTerm_nonneg K x pj.1 pj.2)).mpr
    ⟨gaussianPrimePowerTerm_summable K hx, gaussianPrimePowerTrace_summable K hx⟩

theorem gaussianPrimePowerTrace_eq_pair_sum (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {x : ℝ} (hx : 0 < x) :
    gaussianPrimePowerTrace K x = ∑' pj : ℕ × ℕ, gaussianPrimePowerTerm K x pj.1 pj.2 :=
  (gaussianPrimePowerPair_summable K hx).tsum_prod.symm

theorem gaussianDegreeOnePrimeTerm_le_firstPower (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] (x : ℝ) (p : ℕ) :
    gaussianDegreeOnePrimeTerm K x p ≤ gaussianPrimePowerTerm K x p 0 := by
  unfold gaussianDegreeOnePrimeTerm gaussianPrimePowerTerm
  split_ifs with hp
  · let : Fact p.Prime := ⟨hp⟩
    rw [degreeOnePrimeIdealCount_eq_galois K]
    split_ifs with hf
    · simp only [hf, Nat.cast_one, mul_one, zero_add, pow_one]
      exact le_rfl
    · simp only [Nat.cast_zero, zero_mul]
      exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (Real.log_natCast_nonneg _)) (artinGaussianWeight_pos _).le
  · exact le_rfl

theorem gaussianDegreeOnePrimeTrace_le_primePowerTrace (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {x : ℝ} (hx : 0 < x) :
    gaussianDegreeOnePrimeTrace K x ≤ gaussianPrimePowerTrace K x := by
  apply (gaussianDegreeOnePrimeTerm_summable K hx).tsum_le_tsum _
    (gaussianPrimePowerTrace_summable K hx)
  intro p
  exact (gaussianDegreeOnePrimeTerm_le_firstPower K x p).trans
    ((gaussianPrimePowerTerm_summable K hx p).le_tsum 0
      (fun j _ => gaussianPrimePowerTerm_nonneg K x p j))

end

end SimultaneousPrimitiveRoots
