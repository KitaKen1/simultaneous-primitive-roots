module

public import SimultaneousPrimitiveRoots.ZetaQuotientZeroCount
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Algebra.Order.Floor.Semiring

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField Metric Classical
noncomputable section

def gaussianZeroCountingSeries (n : ℕ) : ℝ :=
  ((n : ℝ) + 4) ^ 2 * Real.exp (-(n : ℝ) ^ 2 / 8)

def gaussianZeroCountingConstant : ℝ := ∑' n : ℕ, gaussianZeroCountingSeries n

theorem gaussianZeroCountingSeries_nonneg (n : ℕ) :
    0 ≤ gaussianZeroCountingSeries n := by unfold gaussianZeroCountingSeries; positivity

theorem gaussianZeroCountingSeries_summable : Summable gaussianZeroCountingSeries := by
  let r : ℝ := Real.exp (-(1 : ℝ) / 8)
  have hr : ‖r‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_lt_one_iff.mpr (by norm_num)
  have hs0 : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_norm_lt_one hr
  have hs1 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 hr
  have hs2 := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 2 hr
  have hp : Summable (fun n : ℕ => ((n : ℝ) + 4) ^ 2 * r ^ n) := by
    convert (hs2.add (hs1.mul_left 8)).add (hs0.mul_left 16) using 1 <;>
      first | rfl | (funext n; ring)
  apply hp.of_nonneg_of_le gaussianZeroCountingSeries_nonneg
  intro n
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  change Real.exp (-(n : ℝ) ^ 2 / 8) ≤ Real.exp (-(1 : ℝ) / 8) ^ n
  rw [← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    have hnat : n ≤ n ^ 2 := by simpa only [pow_two] using Nat.le_mul_self n
    exact_mod_cast hnat
  nlinarith

theorem gaussianZeroCountingConstant_nonneg : 0 ≤ gaussianZeroCountingConstant :=
  tsum_nonneg gaussianZeroCountingSeries_nonneg

theorem gaussianZeroCountingConstant_pos : 0 < gaussianZeroCountingConstant := by
  have h := gaussianZeroCountingSeries_summable.le_tsum 0
    (fun n _ => gaussianZeroCountingSeries_nonneg n)
  norm_num [gaussianZeroCountingSeries] at h
  exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 16) h

/-- A polynomial bound for every finite-height multiplicity carrier implies
summability and an absolute linear bound for the Gaussian height mass. -/
theorem gaussianHeightMass_of_quadratic_count {ι : Type*} (ρ : ι → ℂ)
    {C : ℝ} (_hC : 0 ≤ C)
    (hfinite : ∀ n : ℕ, Finite {i : ι // |(ρ i).im| ≤ (n : ℝ) + 1})
    (hcount : ∀ n : ℕ,
      (Nat.card {i : ι // |(ρ i).im| ≤ (n : ℝ) + 1} : ℝ) ≤
        C * ((n : ℝ) + 4) ^ 2) :
    Summable (fun i : ι => Real.exp (-(ρ i).im ^ 2 / 8)) ∧
      (∑' i : ι, Real.exp (-(ρ i).im ^ 2 / 8)) ≤ C * gaussianZeroCountingConstant := by
  let band : ι → ℕ := fun i => ⌊|(ρ i).im|⌋₊
  let fiber : ℕ → Type _ := fun n => {i : ι // band i = n}
  let f : ∀ n : ℕ, fiber n → {i : ι // |(ρ i).im| ≤ (n : ℝ) + 1} :=
    fun n i => ⟨i.1, by
      have h := (Nat.lt_floor_add_one |(ρ i.1).im|).le
      change |(ρ i.1).im| ≤ (band i.1 : ℝ) + 1 at h
      rw [i.2] at h
      exact h⟩
  have hinj (n : ℕ) : Function.Injective (f n) := by
    intro i j h
    apply Subtype.ext
    exact congrArg (fun x : {i : ι // |(ρ i).im| ≤ (n : ℝ) + 1} => x.val) h
  let : ∀ n : ℕ, Finite {i : ι // |(ρ i).im| ≤ (n : ℝ) + 1} := hfinite
  let : ∀ n : ℕ, Finite (fiber n) := fun n => Finite.of_injective (f n) (hinj n)
  let : ∀ n : ℕ, Fintype (fiber n) := fun n => Fintype.ofFinite _
  have hcard (n : ℕ) : (Nat.card (fiber n) : ℝ) ≤ C * ((n : ℝ) + 4) ^ 2 := by
    apply le_trans _ (hcount n)
    exact_mod_cast Nat.card_le_card_of_injective (f n) (hinj n)
  have hterm (n : ℕ) (i : fiber n) :
      Real.exp (-(ρ i.1).im ^ 2 / 8) ≤ Real.exp (-(n : ℝ) ^ 2 / 8) := by
    have hlo := Nat.floor_le (abs_nonneg (ρ i.1).im)
    change (band i.1 : ℝ) ≤ |(ρ i.1).im| at hlo
    rw [i.2] at hlo
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    have hs : (n : ℝ) ^ 2 ≤ (ρ i.1).im ^ 2 := by nlinarith [sq_abs (ρ i.1).im]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hband (n : ℕ) :
      (∑' i : fiber n, Real.exp (-(ρ i.1).im ^ 2 / 8)) ≤ C * gaussianZeroCountingSeries n := by
    rw [tsum_fintype]
    calc
      (∑ i : fiber n, Real.exp (-(ρ i.1).im ^ 2 / 8)) ≤
          ∑ _i : fiber n, Real.exp (-(n : ℝ) ^ 2 / 8) :=
        Finset.sum_le_sum (fun i _ => hterm n i)
      _ = (Nat.card (fiber n) : ℝ) * Real.exp (-(n : ℝ) ^ 2 / 8) := by
        simp [Nat.card_eq_fintype_card]
      _ ≤ (C * ((n : ℝ) + 4) ^ 2) * Real.exp (-(n : ℝ) ^ 2 / 8) :=
        mul_le_mul_of_nonneg_right (hcard n) (Real.exp_pos _).le
      _ = C * gaussianZeroCountingSeries n := by unfold gaussianZeroCountingSeries; ring
  have hfib (n : ℕ) : Summable (fun i : fiber n => Real.exp (-(ρ i.1).im ^ 2 / 8)) :=
    (hasSum_fintype _).summable
  have hmajor := gaussianZeroCountingSeries_summable.mul_left C
  have houter : Summable (fun n : ℕ => ∑' i : fiber n, Real.exp (-(ρ i.1).im ^ 2 / 8)) :=
    hmajor.of_nonneg_of_le (fun n => tsum_nonneg (fun _ => (Real.exp_pos _).le)) hband
  have hsig : Summable (fun i : Sigma fiber => Real.exp (-(ρ i.2.1).im ^ 2 / 8)) :=
    (summable_sigma_of_nonneg (fun _ => (Real.exp_pos _).le)).mpr ⟨hfib, houter⟩
  have hs : Summable (fun i : ι => Real.exp (-(ρ i).im ^ 2 / 8)) :=
    (Equiv.sigmaFiberEquiv band).summable_iff.mp hsig
  refine ⟨hs, ?_⟩
  have heq : (∑' i : ι, Real.exp (-(ρ i).im ^ 2 / 8)) =
      ∑' n : ℕ, ∑' i : fiber n, Real.exp (-(ρ i.1).im ^ 2 / 8) :=
    ((Equiv.sigmaFiberEquiv band).tsum_eq (fun i : ι => Real.exp (-(ρ i).im ^ 2 / 8))).symm.trans
      hsig.tsum_sigma
  rw [heq]
  apply (houter.tsum_le_tsum hband hmajor).trans_eq
  exact tsum_mul_left

theorem numberFieldEntireFullQuotientContinuation_gaussianMass_of_quadratic_count
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H)
    {C : ℝ} (hC : 0 ≤ C)
    (hcount : ∀ n : ℕ, (fullQuotientZeroCount H ((n : ℝ) + 1) : ℝ) ≤
      C * ((n : ℝ) + 4) ^ 2) :
    Summable (fun i : fullQuotientZeroIndex H =>
      Real.exp (-(fullQuotientIndexedZero H i).im ^ 2 / 8)) ∧
      (∑' i : fullQuotientZeroIndex H,
        Real.exp (-(fullQuotientIndexedZero H i).im ^ 2 / 8)) ≤ C * gaussianZeroCountingConstant := by
  exact gaussianHeightMass_of_quadratic_count (fullQuotientIndexedZero H) hC
    (fun n => numberFieldEntireFullQuotientContinuation_finite_heightZeroIndex K L hH _)
    hcount

/-- A quantified boundary growth estimate supplies the actual Gaussian zero
mass. No separate zero-mass summability assumption is required. -/
theorem numberFieldEntireFullQuotientContinuation_gaussianMass_of_boundary_growth
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L]
    {H : ℂ → ℂ} (hH : NumberFieldEntireFullQuotientContinuation K L H)
    {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ T : ℝ, 0 ≤ T → ∀ z ∈ sphere (2 : ℂ) (2 * (T + 2)),
      ‖H z‖ ≤ Real.exp (B * (T + 3) ^ 2)) :
    Summable (fun i : fullQuotientZeroIndex H =>
      Real.exp (-(fullQuotientIndexedZero H i).im ^ 2 / 8)) ∧
      (∑' i : fullQuotientZeroIndex H,
        Real.exp (-(fullQuotientIndexedZero H i).im ^ 2 / 8)) ≤
          ((B + 4 * (Module.finrank ℚ L : ℝ)) / Real.log 2) * gaussianZeroCountingConstant := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : 0 ≤ (Module.finrank ℚ L : ℝ) := Nat.cast_nonneg _
  have hC : 0 ≤ (B + 4 * (Module.finrank ℚ L : ℝ)) / Real.log 2 := by positivity
  apply numberFieldEntireFullQuotientContinuation_gaussianMass_of_quadratic_count K L hH hC
  intro n
  have ht : 0 ≤ (n : ℝ) + 1 := by positivity
  have hm : 1 ≤ Real.exp (B * ((n : ℝ) + 1 + 3) ^ 2) := by
    simpa using Real.exp_le_exp.mpr (mul_nonneg hB (sq_nonneg ((n : ℝ) + 1 + 3)))
  have h := numberFieldEntireFullQuotientContinuation_zeroCount_jensen_le K L hH ht hm
    (hb ((n : ℝ) + 1) ht)
  rw [Real.log_exp, show (n : ℝ) + 1 + 3 = (n : ℝ) + 4 by ring] at h
  apply h.trans
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ hlog.le
  have hp : 1 ≤ ((n : ℝ) + 4) ^ 2 := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  nlinarith

end
end SimultaneousPrimitiveRoots
