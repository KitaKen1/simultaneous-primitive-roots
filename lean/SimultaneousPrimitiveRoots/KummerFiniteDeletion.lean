module

public import SimultaneousPrimitiveRoots.GaussianFiniteDeletion
public import SimultaneousPrimitiveRoots.NumberFieldDeletionCardinality
public import SimultaneousPrimitiveRoots.KummerGaussianMellin
public import SimultaneousPrimitiveRoots.PrimeKummerSplitting
public import SimultaneousPrimitiveRoots.ProgressionSieveConsequences

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain Filter Asymptotics
open scoped Topology
noncomputable section
open Classical

theorem gaussianRemovedBadPrimesTrace_le (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : n ≠ 0) {x r : ℝ} (hx : 0 < x) (hr : 0 < r) :
    gaussianRemovedPrimeIdealTrace K (numberFieldBadPrimes K n hn) x ≤
      (n : ℝ) * Module.finrank ℚ K * gaussianFiniteDeletionConstant r * x ^ r := by
  apply (gaussianRemovedPrimeIdealTrace_le_card K _ hx hr).trans
  have hc : ((numberFieldBadPrimes K n hn).card : ℝ) ≤
      (n : ℝ) * Module.finrank ℚ K := by exact_mod_cast numberFieldBadPrimes_card_le K n hn
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (gaussianFiniteDeletionConstant_pos hr).le)
    (Real.rpow_nonneg hx.le _)

/-- The extra q in the deliberately coarse deletion count is harmless. -/
theorem primeKummerRemovedTrace_le (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)]
    {x r η : ℝ} (hx : 0 < x) (hr : 0 < r) (hqx : (q : ℝ) ≤ 2 * x ^ η) :
    gaussianRemovedPrimeIdealTrace (PrimeKummerField a q) (primeKummerTopBadPrimes a q) x ≤
      8 * a * gaussianFiniteDeletionConstant r * x ^ (3 * η + r) := by
  have hdegree : (Module.finrank ℚ (PrimeKummerField a q) : ℝ) ≤ (q : ℝ) ^ 2 := by
    rw [primeKummerField_absolute_degree ha.out hq.out haq.out, Nat.cast_mul]
    have hsub : ((q - 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast Nat.sub_le q 1
    nlinarith [show (0 : ℝ) ≤ q from Nat.cast_nonneg q]
  have hqpow : (q : ℝ) ^ 3 ≤ (2 * x ^ η) ^ 3 :=
    pow_le_pow_left₀ (Nat.cast_nonneg q) hqx 3
  have hxp : (x ^ η) ^ 3 = x ^ (3 * η) := by
    rw [← Real.rpow_mul_natCast hx.le η 3]
    congr 1
    ring
  have hC : 0 ≤ gaussianFiniteDeletionConstant r := (gaussianFiniteDeletionConstant_pos hr).le
  have h := gaussianRemovedBadPrimesTrace_le (PrimeKummerField a q) (a * q)
    (mul_ne_zero (by have ht := ha.out; omega) hq.out.ne_zero) hx hr
  change gaussianRemovedPrimeIdealTrace (PrimeKummerField a q) (primeKummerTopBadPrimes a q) x ≤ _ at h
  calc
    _ ≤ ((a * q : ℕ) : ℝ) * Module.finrank ℚ (PrimeKummerField a q) *
        gaussianFiniteDeletionConstant r * x ^ r := h
    _ ≤ (a : ℝ) * q * (q : ℝ) ^ 2 * gaussianFiniteDeletionConstant r * x ^ r := by
      rw [Nat.cast_mul]
      gcongr
    _ = (a : ℝ) * gaussianFiniteDeletionConstant r * (q : ℝ) ^ 3 * x ^ r := by ring
    _ ≤ (a : ℝ) * gaussianFiniteDeletionConstant r * (2 * x ^ η) ^ 3 * x ^ r := by
      gcongr
    _ = _ := by rw [mul_pow, hxp, Real.rpow_add hx]; ring

def gaussianKummerDeletionEnvelope (a : ℕ) (η x : ℝ) : ℝ :=
  8 * a * gaussianFiniteDeletionConstant (1 / 4) * x ^ (3 * η + 1 / 4)

theorem gaussianKummerDeletionEnvelope_isLittleO (a : ℕ) {η : ℝ} (hη : η < 1 / 4) :
    gaussianKummerDeletionEnvelope a η =o[atTop] (fun x : ℝ => x) :=
  sublinear_power_isLittleO_id _ (by linarith)

/-- The actual signed trace restores the top field with only a positive finite deletion error. -/
theorem primeKummer_fullTrace_le_base_signed_removed (a q : ℕ)
    [ha : Fact (2 ≤ a)] [hq : Fact q.Prime] [haq : Fact (a < q)]
    {x : ℝ} (hx : 0 < x) :
    gaussianPrimePowerTrace (PrimeKummerField a q) x ≤
      gaussianPrimePowerTrace (CyclotomicField q ℚ) x +
        ((q : ℝ) - 1) * primeKummerGaussianSignedTrace a q x +
          gaussianRemovedPrimeIdealTrace (PrimeKummerField a q) (primeKummerTopBadPrimes a q) x := by
  let : IsGalois ℚ (PrimeKummerField a q) := primeKummerField_galois a q
  let : IsGalois ℚ (CyclotomicField q ℚ) := IsCyclotomicExtension.isGalois {q} ℚ _
  have hb := gaussianDeletedPrimeIdealTrace_le_full (CyclotomicField q ℚ)
    (primeKummerBaseBadPrimes a q) hx
  have hq1 : 1 ≤ q := hq.out.one_le
  have hd : (q : ℝ) - 1 ≠ 0 := by
    have hh : (2 : ℝ) ≤ q := by exact_mod_cast hq.out.two_le
    linarith
  have hGamma : ((q : ℝ) - 1) * primeKummerGaussianSignedTrace a q x =
      gaussianDeletedPrimeIdealTrace (PrimeKummerField a q) (primeKummerTopBadPrimes a q) x -
        gaussianDeletedPrimeIdealTrace (CyclotomicField q ℚ) (primeKummerBaseBadPrimes a q) x := by
    rw [primeKummerGaussianSignedTrace, Nat.cast_sub hq1, Nat.cast_one]
    field_simp
  rw [gaussianPrimePowerTrace_eq_deleted_add_removed (PrimeKummerField a q)
    (primeKummerTopBadPrimes a q) hx]
  linarith

def UniformKummerGaussianTraceDecomposition (A : Finset ℕ) (η CE : ℝ) : Prop :=
  ∀ᶠ x : ℝ in atTop, ∀ a ∈ A, ∀ ha : 2 ≤ a, ∀ q : ℕ, ∀ hq : q.Prime,
    ∀ haq : a < q, q ≤ Nat.floor (2 * x ^ η) →
    letI : Fact (2 ≤ a) := ⟨ha⟩
    letI : Fact q.Prime := ⟨hq⟩
    letI : Fact (a < q) := ⟨haq⟩
    gaussianPrimePowerTrace (PrimeKummerField a q) x ≤
      CE * x + ((q : ℝ) - 1) * primeKummerGaussianSignedTrace a q x

/-- No analytic hypothesis is needed for the deterministic trace decomposition. -/
theorem exists_uniformKummerGaussianTraceDecomposition (A : Finset ℕ) {η : ℝ}
    (hη : η < 1 / 5) :
    ∃ CE : ℝ, 0 ≤ CE ∧ UniformKummerGaussianTraceDecomposition A η CE := by
  obtain ⟨C, hC, hcyc⟩ := exists_uniformCyclotomicGaussianUpperBound hη
  let D := 8 * ((A.sup id : ℕ) : ℝ) * gaussianFiniteDeletionConstant (1 / 4)
  have hlo := (sublinear_power_isLittleO_id D (by linarith : 3 * η + 1 / 4 < 1)).bound
    (by norm_num : (0 : ℝ) < 1)
  refine ⟨C + 1, by linarith, ?_⟩
  filter_upwards [hcyc, hlo, eventually_gt_atTop (0 : ℝ)] with x hcycx hlox hx
  intro a ha ha2 q hq haq hcut
  let : Fact (2 ≤ a) := ⟨ha2⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact (a < q) := ⟨haq⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  have hqx : (q : ℝ) ≤ 2 * x ^ η :=
    (by exact_mod_cast hcut : (q : ℝ) ≤ Nat.floor (2 * x ^ η)).trans (Nat.floor_le (by positivity))
  have hasup : (a : ℝ) ≤ ((A.sup id : ℕ) : ℝ) := by
    exact_mod_cast Finset.le_sup (f := id) ha
  have hremoved := primeKummerRemovedTrace_le a q hx (by norm_num : (0 : ℝ) < 1 / 4) hqx
  have henv : 8 * (a : ℝ) * gaussianFiniteDeletionConstant (1 / 4) * x ^ (3 * η + 1 / 4) ≤
      D * x ^ (3 * η + 1 / 4) := by
    dsimp [D]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hasup (by norm_num))
        (gaussianFiniteDeletionConstant_pos (by norm_num : (0 : ℝ) < 1 / 4)).le)
      (Real.rpow_nonneg hx.le _)
  have hsmall : D * x ^ (3 * η + 1 / 4) ≤ x := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx, one_mul] at hlox
    exact (le_abs_self _).trans hlox
  have hf := primeKummer_fullTrace_le_base_signed_removed a q hx
  have hb := hcycx q hq hcut
  linarith [hremoved.trans (henv.trans hsmall)]

end
end SimultaneousPrimitiveRoots
