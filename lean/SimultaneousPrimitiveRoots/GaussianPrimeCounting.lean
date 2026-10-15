module

public import SimultaneousPrimitiveRoots.GaussianWeight
public import SimultaneousPrimitiveRoots.KummerCounting
public import Mathlib.Analysis.PSeries
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField Ideal

attribute [local instance] Int.ideal_span_isMaximal_of_prime Ideal.Quotient.field

noncomputable section
open Classical

/-- Actual prime ideals over p whose norm is p. This definition does not use
an analytic count or a conjectural Hecke factorization. -/
def degreeOnePrimeIdealCount (K : Type*) [Field K] [NumberField K] (p : ℕ) : ℕ :=
  {P : Ideal (𝓞 K) | P ∈ (span {(p : ℤ)}).primesOver (𝓞 K) ∧ P.absNorm = p}.ncard

theorem completelySplit_prime_inertia_degree_one {K : Type*} [Field K] [NumberField K]
    [IsGalois ℚ K] {p : ℕ} [hp : Fact p.Prime]
    (hs : ((span {(p : ℤ)}).primesOver (𝓞 K)).ncard = Module.finrank ℚ K)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] : P.inertiaDeg ℤ = 1 := by
  have hf := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (span {(p : ℤ)}) (𝓞 K) Gal(K/ℚ)
  rw [hs, IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K] at hf
  have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
  have he : (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) *
      (span {(p : ℤ)}).inertiaDegIn (𝓞 K) = 1 := by
    apply (Nat.mul_left_cancel_iff hn).mp
    simpa only [Nat.mul_one, Nat.mul_assoc] using hf
  have hi : (span {(p : ℤ)}).inertiaDegIn (𝓞 K) = 1 := by
    apply Nat.eq_one_of_dvd_one
    exact ⟨(span {(p : ℤ)}).ramificationIdxIn (𝓞 K), by simpa only [Nat.mul_comm] using he.symm⟩
  rw [← Ideal.inertiaDegIn_eq_inertiaDeg (span {(p : ℤ)}) P Gal(K/ℚ)]
  exact hi

theorem completelySplit_prime_absNorm {K : Type*} [Field K] [NumberField K]
    [IsGalois ℚ K] {p : ℕ} [Fact p.Prime]
    (hs : ((span {(p : ℤ)}).primesOver (𝓞 K)).ncard = Module.finrank ℚ K)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] : P.absNorm = p := by
  have h := Ideal.pow_inertiaDeg p P
  rw [completelySplit_prime_inertia_degree_one hs P, pow_one] at h
  exact h.symm

theorem degreeOnePrimeIdealCount_eq_finrank {K : Type*} [Field K] [NumberField K]
    [IsGalois ℚ K] {p : ℕ} [Fact p.Prime]
    (hs : ((span {(p : ℤ)}).primesOver (𝓞 K)).ncard = Module.finrank ℚ K) :
    degreeOnePrimeIdealCount K p = Module.finrank ℚ K := by
  have hset : {P : Ideal (𝓞 K) | P ∈ (span {(p : ℤ)}).primesOver (𝓞 K) ∧ P.absNorm = p} =
      (span {(p : ℤ)}).primesOver (𝓞 K) := by
    ext P
    constructor
    · exact fun h => h.1
    · intro h
      let : P.IsPrime := h.1
      let : P.LiesOver (span {(p : ℤ)}) := h.2
      exact ⟨h, completelySplit_prime_absNorm hs P⟩
  unfold degreeOnePrimeIdealCount
  rw [hset, hs]

theorem degreeOnePrimeIdealCount_le_finrank (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {p : ℕ} [Fact p.Prime] :
    degreeOnePrimeIdealCount K p ≤ Module.finrank ℚ K := by
  have hsub : {P : Ideal (𝓞 K) | P ∈ (span {(p : ℤ)}).primesOver (𝓞 K) ∧ P.absNorm = p} ⊆
      (span {(p : ℤ)}).primesOver (𝓞 K) := fun _ h => h.1
  have hf := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (span {(p : ℤ)}) (𝓞 K) Gal(K/ℚ)
  rw [IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K] at hf
  have hrf : 1 ≤ (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) *
      (span {(p : ℤ)}).inertiaDegIn (𝓞 K) := by
    have hn : 0 < Module.finrank ℚ K := Module.finrank_pos
    by_contra h
    have hz : (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) *
        (span {(p : ℤ)}).inertiaDegIn (𝓞 K) = 0 := by omega
    rw [hz, Nat.mul_zero] at hf
    omega
  calc
    degreeOnePrimeIdealCount K p ≤ ((span {(p : ℤ)}).primesOver (𝓞 K)).ncard :=
      Set.ncard_le_ncard hsub (Algebra.QuasiFinite.finite_primesOver _)
    _ ≤ _ := by
      have hm := Nat.mul_le_mul_left (((span {(p : ℤ)}).primesOver (𝓞 K)).ncard) hrf
      simpa only [Nat.mul_one, ← Nat.mul_assoc, hf] using hm

/-- Completing a square gives any polynomial majorant of the Gaussian. -/
theorem artinGaussianWeight_le_rpow {t : ℝ} (ht : 0 < t) (r : ℝ) :
    artinGaussianWeight t ≤ Real.exp ((Real.log 2) ^ 2 + r ^ 2 / 4) * t ^ (-r) := by
  rw [artinGaussianWeight, Real.rpow_def_of_pos ht, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (Real.log t - r / 2)]

def gaussianDegreeOnePrimeTerm (K : Type*) [Field K] [NumberField K] (x : ℝ) (p : ℕ) : ℝ :=
  if p.Prime then (degreeOnePrimeIdealCount K p : ℝ) * Real.log p *
    artinGaussianWeight ((p : ℝ) / x) else 0

/-- The convergent contribution of degree-one prime ideals only, not the
full prime-power trace of the Dedekind zeta function. -/
def gaussianDegreeOnePrimeTrace (K : Type*) [Field K] [NumberField K] (x : ℝ) : ℝ :=
  ∑' p : ℕ, gaussianDegreeOnePrimeTerm K x p

theorem gaussianDegreeOnePrimeTerm_nonneg (K : Type*) [Field K] [NumberField K]
    (x : ℝ) (p : ℕ) : 0 ≤ gaussianDegreeOnePrimeTerm K x p := by
  unfold gaussianDegreeOnePrimeTerm
  split_ifs
  · exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg _))
      (artinGaussianWeight_pos _).le
  · exact le_rfl

theorem gaussianDegreeOnePrimeTerm_le_inverse_square (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {x : ℝ} (hx : 0 < x) (p : ℕ) :
    gaussianDegreeOnePrimeTerm K x p ≤
      ((Module.finrank ℚ K : ℝ) * Real.exp ((Real.log 2) ^ 2 + 9 / 4) * x ^ (3 : ℕ)) *
        (p : ℝ) ^ (-2 : ℝ) := by
  unfold gaussianDegreeOnePrimeTerm
  split_ifs with hp
  · let : Fact p.Prime := ⟨hp⟩
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    have hc : (degreeOnePrimeIdealCount K p : ℝ) ≤ (Module.finrank ℚ K : ℝ) :=
      by exact_mod_cast degreeOnePrimeIdealCount_le_finrank K
    have hl : Real.log (p : ℝ) ≤ (p : ℝ) := (Real.log_le_sub_one_of_pos hp0).trans (by linarith)
    have hw := artinGaussianWeight_le_rpow (div_pos hp0 hx) (3 : ℝ)
    have heq : (p : ℝ) * ((p : ℝ) / x) ^ (-3 : ℝ) =
        x ^ (3 : ℕ) * (p : ℝ) ^ (-2 : ℝ) := by
      rw [Real.div_rpow hp0.le hx.le, Real.rpow_neg hp0.le, Real.rpow_neg hx.le,
        Real.rpow_neg hp0.le]
      norm_num only [Real.rpow_ofNat]
      field_simp
    calc
      _ ≤ (Module.finrank ℚ K : ℝ) * (p : ℝ) *
          (Real.exp ((Real.log 2) ^ 2 + 9 / 4) * ((p : ℝ) / x) ^ (-3 : ℝ)) := by
        apply mul_le_mul (mul_le_mul hc hl (Real.log_natCast_nonneg _) (Nat.cast_nonneg _))
          (by norm_num only [show (3 : ℝ) ^ 2 = 9 by norm_num] at hw; exact hw)
          (artinGaussianWeight_pos _).le (by positivity)
      _ = _ := by rw [mul_assoc, mul_left_comm (p : ℝ), ← mul_assoc, heq]; ring
  · positivity

theorem gaussianDegreeOnePrimeTerm_summable (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {x : ℝ} (hx : 0 < x) : Summable (gaussianDegreeOnePrimeTerm K x) := by
  have hs : Summable (fun p : ℕ => (p : ℝ) ^ (-2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  apply (hs.mul_left ((Module.finrank ℚ K : ℝ) *
    Real.exp ((Real.log 2) ^ 2 + 9 / 4) * x ^ (3 : ℕ))).of_norm_bounded
  intro p
  rw [Real.norm_eq_abs, abs_of_nonneg (gaussianDegreeOnePrimeTerm_nonneg K x p)]
  exact gaussianDegreeOnePrimeTerm_le_inverse_square K hx p

theorem completelySplit_count_mul_log_le_gaussianTrace (K : Type*) [Field K] [NumberField K]
    [IsGalois ℚ K] {x : ℝ} (hx : 1 < x) :
    ((dyadicCompletelySplitPrimes K x).card : ℝ) * (Module.finrank ℚ K : ℝ) * Real.log x ≤
      gaussianDegreeOnePrimeTrace K x := by
  have hpoint : ∀ p ∈ dyadicCompletelySplitPrimes K x,
      (Module.finrank ℚ K : ℝ) * Real.log x ≤ gaussianDegreeOnePrimeTerm K x p := by
    intro p hpS
    obtain ⟨_, hp, hpx, hp2x, hs⟩ := Finset.mem_filter.mp hpS
    let : Fact p.Prime := ⟨hp⟩
    rw [gaussianDegreeOnePrimeTerm, if_pos hp, degreeOnePrimeIdealCount_eq_finrank hs]
    have hlog : Real.log x ≤ Real.log p := Real.log_le_log (by linarith) hpx.le
    have hw : 1 ≤ artinGaussianWeight ((p : ℝ) / x) :=
      artinGaussianWeight_ge_one ((le_div_iff₀ (by linarith)).mpr (by linarith))
        ((div_le_iff₀ (by linarith)).mpr (by linarith))
    calc
      _ ≤ (Module.finrank ℚ K : ℝ) * Real.log p :=
        mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg _)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hw
  calc
    _ = ∑ _p ∈ dyadicCompletelySplitPrimes K x,
        (Module.finrank ℚ K : ℝ) * Real.log x := by simp only [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ p ∈ dyadicCompletelySplitPrimes K x, gaussianDegreeOnePrimeTerm K x p :=
      Finset.sum_le_sum hpoint
    _ ≤ _ := (gaussianDegreeOnePrimeTerm_summable K (by linarith)).sum_le_tsum _
      (fun p _ => gaussianDegreeOnePrimeTerm_nonneg K x p)

theorem powerResidueException_count_mul_log_le_gaussianTrace {a q : ℕ}
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] {x : ℝ} (hx : 1 < x) :
    ((powerResidueExceptionPrimes a q x).card : ℝ) *
      ((q : ℝ) * ((q : ℝ) - 1)) * Real.log x ≤
        gaussianDegreeOnePrimeTrace (PrimeKummerField a q) x := by
  let : IsGalois ℚ (PrimeKummerField a q) := primeKummerField_galois a q
  have hd : (Module.finrank ℚ (PrimeKummerField a q) : ℝ) = (q : ℝ) * ((q : ℝ) - 1) := by
    rw [primeKummerField_absolute_degree ha.out hq.out haq.out]
    push_cast [hq.out.one_le]
    rfl
  rw [← hd]
  apply le_trans ?_ (completelySplit_count_mul_log_le_gaussianTrace (PrimeKummerField a q) hx)
  apply mul_le_mul_of_nonneg_right _ (Real.log_pos hx).le
  apply mul_le_mul_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast powerResidueExceptionPrimes_card_le_kummerSplit (a := a) (q := q) x

theorem powerResidueException_count_bound_of_gaussianTrace {a q : ℕ}
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)] {x δ C : ℝ}
    (hx : 1 < x)
    (htrace : gaussianDegreeOnePrimeTrace (PrimeKummerField a q) x ≤
      C * x + C * ((q : ℝ) * ((q : ℝ) - 1)) * x ^ (1 - δ) * Real.log (2 * (q : ℝ))) :
    ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
      C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
        C * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) / Real.log x := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq.out.pos
  have hq1 : 0 < (q : ℝ) - 1 := by
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
    linarith
  have hn : 0 < (q : ℝ) * ((q : ℝ) - 1) := mul_pos hq0 hq1
  have hl : 0 < Real.log x := Real.log_pos hx
  have h := (powerResidueException_count_mul_log_le_gaussianTrace (a := a) (q := q) hx).trans htrace
  have hdiv : ((powerResidueExceptionPrimes a q x).card : ℝ) ≤
      (C * x + C * ((q : ℝ) * ((q : ℝ) - 1)) * x ^ (1 - δ) * Real.log (2 * (q : ℝ))) /
        (((q : ℝ) * ((q : ℝ) - 1)) * Real.log x) :=
    (le_div_iff₀ (mul_pos hn hl)).mpr (by simpa only [mul_assoc] using h)
  have heq : (C * x + C * ((q : ℝ) * ((q : ℝ) - 1)) * x ^ (1 - δ) *
      Real.log (2 * (q : ℝ))) / (((q : ℝ) * ((q : ℝ) - 1)) * Real.log x) =
      C * (x / Real.log x) * (1 / ((q : ℝ) * ((q : ℝ) - 1))) +
        C * x ^ (1 - δ) * Real.log (2 * (q : ℝ)) / Real.log x := by
    field_simp
  exact hdiv.trans_eq heq

end

end SimultaneousPrimitiveRoots
