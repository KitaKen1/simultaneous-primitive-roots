module

public import SimultaneousPrimitiveRoots.GaussianHigherPrimePowers
public import SimultaneousPrimitiveRoots.CyclotomicPrimeSplitting
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField Ideal Filter Asymptotics
open scoped Topology

attribute [local instance] Int.ideal_span_isMaximal_of_prime Ideal.Quotient.field

noncomputable section
open Classical

def gaussianProgressionPrimeTerm (q : ℕ) (x : ℝ) (p : ℕ) : ℝ :=
  if p.Prime ∧ q ∣ p - 1 then Real.log p * artinGaussianWeight ((p : ℝ) / x) else 0

def gaussianProgressionPrimeTrace (q : ℕ) (x : ℝ) : ℝ :=
  ∑' p : ℕ, gaussianProgressionPrimeTerm q x p

theorem cyclotomic_degreeOne_count_ramified (q : ℕ) [hq : Fact q.Prime] [NeZero q] :
    degreeOnePrimeIdealCount (CyclotomicField q ℚ) q = 1 := by
  let : IsGalois ℚ (CyclotomicField q ℚ) := IsCyclotomicExtension.isGalois {q} ℚ _
  rw [degreeOnePrimeIdealCount_eq_galois, rationalPrimeResidueDegree,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_prime q (CyclotomicField q ℚ), if_pos rfl,
    rationalPrimeIdealCount]
  exact IsCyclotomicExtension.Rat.ncard_primesOver_of_prime q (CyclotomicField q ℚ)

theorem cyclotomic_degreeOne_count_unramified {p q : ℕ}
    [hp : Fact p.Prime] [hq : Fact q.Prime] [NeZero q] (hpq : p ≠ q) :
    degreeOnePrimeIdealCount (CyclotomicField q ℚ) p = if q ∣ p - 1 then q - 1 else 0 := by
  let : IsGalois ℚ (CyclotomicField q ℚ) := IsCyclotomicExtension.isGalois {q} ℚ _
  have hnd : ¬ p ∣ q := by
    intro h
    rcases (Nat.dvd_prime hq.out).mp h with h | h
    · exact hp.out.ne_one h
    · exact hpq h
  have hf : rationalPrimeResidueDegree (CyclotomicField q ℚ) p = 1 ↔ q ∣ p - 1 := by
    rw [rationalPrimeResidueDegree,
      IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p (CyclotomicField q ℚ) hnd,
      orderOf_eq_one_iff]
    constructor
    · intro hz
      apply (ZMod.natCast_eq_zero_iff (p - 1) q).mp
      rw [Nat.cast_sub hp.out.one_le, Nat.cast_one, hz, sub_self]
    · intro hd
      have hz := (ZMod.natCast_eq_zero_iff (p - 1) q).mpr hd
      rwa [Nat.cast_sub hp.out.one_le, Nat.cast_one, sub_eq_zero] at hz
  rw [degreeOnePrimeIdealCount_eq_galois]
  by_cases hd : q ∣ p - 1
  · rw [if_pos (hf.mpr hd), if_pos hd]
    change ((span {(p : ℤ)}).primesOver (𝓞 (CyclotomicField q ℚ))).ncard = q - 1
    rw [← prime_cyclotomic_degree (E := CyclotomicField q ℚ) hq.out]
    exact (cyclotomic_prime_splitsCompletely_iff hp.out hq.out hpq).mpr hd
  · rw [if_neg (fun h => hd (hf.mp h)), if_neg hd]

theorem gaussianCyclotomicDegreeOneTerm_eq (q : ℕ) [hq : Fact q.Prime] [NeZero q]
    (x : ℝ) (p : ℕ) :
    gaussianDegreeOnePrimeTerm (CyclotomicField q ℚ) x p =
      ((q : ℝ) - 1) * gaussianProgressionPrimeTerm q x p +
        if p = q then Real.log q * artinGaussianWeight ((q : ℝ) / x) else 0 := by
  by_cases hpq : p = q
  · subst p
    have hq2 := hq.out.two_le
    have hnd : ¬ q ∣ q - 1 := Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    simp [gaussianDegreeOnePrimeTerm, hq.out, cyclotomic_degreeOne_count_ramified,
      gaussianProgressionPrimeTerm, hnd]
  · unfold gaussianDegreeOnePrimeTerm gaussianProgressionPrimeTerm
    rw [if_neg hpq]
    split_ifs with hp hd
    · let : Fact p.Prime := ⟨hp⟩
      rw [cyclotomic_degreeOne_count_unramified hpq, if_pos hd.2]
      push_cast [hq.out.one_le]
      ring
    · let : Fact p.Prime := ⟨hp⟩
      rw [cyclotomic_degreeOne_count_unramified hpq, if_neg (fun h => hd ⟨hp, h⟩)]
      simp
    · simp_all
    · simp_all

theorem gaussianProgressionPrimeTerm_nonneg (q : ℕ) (x : ℝ) (p : ℕ) :
    0 ≤ gaussianProgressionPrimeTerm q x p := by
  unfold gaussianProgressionPrimeTerm
  split_ifs
  · exact mul_nonneg (Real.log_natCast_nonneg _) (artinGaussianWeight_pos _).le
  · exact le_rfl

theorem gaussianProgressionPrimeTerm_le_cyclotomic (q : ℕ) [hq : Fact q.Prime] [NeZero q]
    (x : ℝ) (p : ℕ) :
    gaussianProgressionPrimeTerm q x p ≤ gaussianDegreeOnePrimeTerm (CyclotomicField q ℚ) x p := by
  rw [gaussianCyclotomicDegreeOneTerm_eq]
  have hn : 1 ≤ (q : ℝ) - 1 := by
    have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
    linarith
  apply (le_mul_of_one_le_left (gaussianProgressionPrimeTerm_nonneg q x p) hn).trans
  apply le_add_of_nonneg_right
  split_ifs
  · exact mul_nonneg (Real.log_natCast_nonneg _) (artinGaussianWeight_pos _).le
  · exact le_rfl

theorem gaussianProgressionPrimeTerm_summable (q : ℕ) [Fact q.Prime] [NeZero q]
    {x : ℝ} (hx : 0 < x) : Summable (gaussianProgressionPrimeTerm q x) := by
  let : IsGalois ℚ (CyclotomicField q ℚ) := IsCyclotomicExtension.isGalois {q} ℚ _
  apply (gaussianDegreeOnePrimeTerm_summable (CyclotomicField q ℚ) hx).of_norm_bounded
  intro p
  rw [Real.norm_eq_abs, abs_of_nonneg (gaussianProgressionPrimeTerm_nonneg q x p)]
  exact gaussianProgressionPrimeTerm_le_cyclotomic q x p

theorem gaussianCyclotomicDegreeOneTrace_eq (q : ℕ) [Fact q.Prime] [NeZero q]
    {x : ℝ} (hx : 0 < x) :
    gaussianDegreeOnePrimeTrace (CyclotomicField q ℚ) x =
      ((q : ℝ) - 1) * gaussianProgressionPrimeTrace q x +
        Real.log q * artinGaussianWeight ((q : ℝ) / x) := by
  unfold gaussianDegreeOnePrimeTrace gaussianProgressionPrimeTrace
  simp_rw [gaussianCyclotomicDegreeOneTerm_eq]
  have hs := (gaussianProgressionPrimeTerm_summable q hx).mul_left ((q : ℝ) - 1)
  rw [hs.tsum_add (hasSum_ite_eq q _).summable, (gaussianProgressionPrimeTerm_summable q hx).tsum_mul_left,
    tsum_ite_eq]

theorem gaussianCyclotomicFullTrace_eq (q : ℕ) [Fact q.Prime] [NeZero q]
    {x : ℝ} (hx : 0 < x) :
    gaussianPrimePowerTrace (CyclotomicField q ℚ) x =
      ((q : ℝ) - 1) * gaussianProgressionPrimeTrace q x +
        Real.log q * artinGaussianWeight ((q : ℝ) / x) +
          gaussianHigherPrimePowerTrace (CyclotomicField q ℚ) x := by
  let : IsGalois ℚ (CyclotomicField q ℚ) := IsCyclotomicExtension.isGalois {q} ℚ _
  rw [gaussianPrimePowerTrace_eq_degreeOne_add_higher _ hx, gaussianCyclotomicDegreeOneTrace_eq q hx]

def gaussianRamifiedEnvelope (η x : ℝ) : ℝ :=
  (4 * Real.exp ((Real.log 2) ^ 2 + 1 / 4)) * x ^ (2 * η - 1)

theorem gaussianRamifiedTerm_le {q : ℕ} [hq : Fact q.Prime] {x : ℝ} (hx : 0 < x) :
    Real.log q * artinGaussianWeight ((q : ℝ) / x) ≤
      Real.exp ((Real.log 2) ^ 2 + 1 / 4) * (q : ℝ) ^ (2 : ℕ) / x := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq.out.pos
  have hl : Real.log (q : ℝ) ≤ (q : ℝ) := (Real.log_le_sub_one_of_pos hq0).trans (by linarith)
  have hw := artinGaussianWeight_le_rpow (div_pos hq0 hx) (-1 : ℝ)
  norm_num only [neg_neg, Real.rpow_one, show (-1 : ℝ) ^ 2 = 1 by norm_num] at hw
  calc
    _ ≤ (q : ℝ) * (Real.exp ((Real.log 2) ^ 2 + 1 / 4) * ((q : ℝ) / x)) :=
      mul_le_mul hl hw (artinGaussianWeight_pos _).le hq0.le
    _ = _ := by ring

theorem gaussianRamifiedTerm_le_moving_envelope {q : ℕ} [Fact q.Prime] {η x : ℝ}
    (hx : 0 < x) (hq : (q : ℝ) ≤ 2 * x ^ η) :
    Real.log q * artinGaussianWeight ((q : ℝ) / x) ≤ gaussianRamifiedEnvelope η x := by
  apply (gaussianRamifiedTerm_le hx).trans
  have hqpow : (q : ℝ) ^ (2 : ℕ) ≤ (2 * x ^ η) ^ (2 : ℕ) :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hq 2
  calc
    _ ≤ Real.exp ((Real.log 2) ^ 2 + 1 / 4) * (2 * x ^ η) ^ (2 : ℕ) / x :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hqpow (Real.exp_pos _).le) hx.le
    _ = _ := by
      unfold gaussianRamifiedEnvelope
      have heq : x ^ (2 * η) = (x ^ η) ^ (2 : ℕ) := by
        rw [mul_comm (2 : ℝ) η, Real.rpow_mul hx.le, Real.rpow_two]
      rw [Real.rpow_sub_one hx.ne', heq]
      ring

theorem gaussianRamifiedEnvelope_isLittleO {η : ℝ} (hη : η < 1 / 2) :
    gaussianRamifiedEnvelope η =o[atTop] (fun x : ℝ => x) :=
  sublinear_power_isLittleO_id _ (by linarith)

/-- Unproved weighted progression input; a moving-modulus sieve estimate
and smoothing must still be connected to this exact prime series. -/
def UniformGaussianProgressionUpperBound (η C : ℝ) : Prop :=
  ∀ᶠ x : ℝ in atTop, ∀ q : ℕ, ∀ hq : q.Prime, q ≤ Nat.floor (2 * x ^ η) →
    letI : Fact q.Prime := ⟨hq⟩
    letI : NeZero q := ⟨hq.ne_zero⟩
    ((q : ℝ) - 1) * gaussianProgressionPrimeTrace q x ≤ C * x

def UniformCyclotomicGaussianUpperBound (η C : ℝ) : Prop :=
  ∀ᶠ x : ℝ in atTop, ∀ q : ℕ, ∀ hq : q.Prime, q ≤ Nat.floor (2 * x ^ η) →
    letI : Fact q.Prime := ⟨hq⟩
    letI : NeZero q := ⟨hq.ne_zero⟩
    gaussianPrimePowerTrace (CyclotomicField q ℚ) x ≤ C * x

theorem uniformCyclotomicGaussianUpperBound_of_progression {η C : ℝ} (hη : η < 1 / 2)
    (hAP : UniformGaussianProgressionUpperBound η C) :
    UniformCyclotomicGaussianUpperBound η (C + 2) := by
  have hH := (gaussianMovingHigherEnvelope_isLittleO hη).bound (by norm_num : (0 : ℝ) < 1)
  have hR := (gaussianRamifiedEnvelope_isLittleO hη).bound (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hAP, hH, hR, eventually_gt_atTop (0 : ℝ)] with x hAPx hHx hRx hx
  intro q hq hcut
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  let : IsGalois ℚ (CyclotomicField q ℚ) := IsCyclotomicExtension.isGalois {q} ℚ _
  have hqx : (q : ℝ) ≤ 2 * x ^ η := (by exact_mod_cast hcut : (q : ℝ) ≤ Nat.floor (2 * x ^ η)).trans
    (Nat.floor_le (by positivity))
  have hn : (Module.finrank ℚ (CyclotomicField q ℚ) : ℝ) ≤ 2 * x ^ η := by
    rw [prime_cyclotomic_degree hq]
    have hsub : ((q - 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast Nat.sub_le q 1
    exact hsub.trans hqx
  have hHle : gaussianMovingHigherEnvelope η x ≤ x := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx, one_mul] at hHx
    exact (le_abs_self _).trans hHx
  have hRle : gaussianRamifiedEnvelope η x ≤ x := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx, one_mul] at hRx
    exact (le_abs_self _).trans hRx
  rw [gaussianCyclotomicFullTrace_eq q hx]
  calc
    _ ≤ C * x + gaussianRamifiedEnvelope η x + gaussianMovingHigherEnvelope η x :=
      add_le_add (add_le_add (hAPx q hq hcut) (gaussianRamifiedTerm_le_moving_envelope hx hqx))
        (gaussianHigherPrimePowerTrace_le_moving_envelope _ hη hx hn)
    _ ≤ C * x + x + x := add_le_add (add_le_add le_rfl hRle) hHle
    _ = _ := by ring

end

end SimultaneousPrimitiveRoots
