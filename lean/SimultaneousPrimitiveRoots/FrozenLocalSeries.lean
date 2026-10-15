module

public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Tactic

@[expose] public section

namespace SimultaneousPrimitiveRoots

noncomputable section

/-- The explicit majorant for frozen exponents in the reflected expansion.
Its comparison with actual metaplectic coefficients remains a separate input. -/
def frozenLocalMajorant (Q : ℝ) (e : ℕ) : ℝ :=
  if e = 0 then 1 else
  if e % 3 = 1 then (Q⁻¹) ^ (e / 3) else
  if e % 3 = 0 then Real.sqrt Q * (Q⁻¹) ^ (e / 3) else 0

theorem frozenLocalMajorant_zero (Q : ℝ) : frozenLocalMajorant Q 0 = 1 := by
  simp [frozenLocalMajorant]

theorem frozenLocalMajorant_three_mul_add_one (Q : ℝ) (k : ℕ) :
    frozenLocalMajorant Q (k * 3 + 1) = (Q⁻¹) ^ k := by
  simp [frozenLocalMajorant, show (k * 3 + 1) / 3 = k by omega]

theorem frozenLocalMajorant_three_mul_succ (Q : ℝ) (k : ℕ) :
    frozenLocalMajorant Q ((k + 1) * 3) = Real.sqrt Q * (Q⁻¹) ^ (k + 1) := by
  simp [frozenLocalMajorant, show (k + 1) * 3 ≠ 0 by omega]

theorem frozenLocalMajorant_three_mul_add_two (Q : ℝ) (k : ℕ) :
    frozenLocalMajorant Q (k * 3 + 2) = 0 := by
  simp [frozenLocalMajorant]

theorem frozenLocalMajorant_nonneg {Q : ℝ} (hQ : 0 ≤ Q) (e : ℕ) :
    0 ≤ frozenLocalMajorant Q e := by
  unfold frozenLocalMajorant
  split_ifs <;> positivity

/-- The Dirichlet weight is written as u^e, with u=Q^(-sigma). -/
def frozenLocalSeries (Q u : ℝ) : ℝ :=
  ∑' e : ℕ, frozenLocalMajorant Q e * u ^ e

theorem frozenLocalSeries_ratio {Q u : ℝ} (hQ : 2 ≤ Q) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    ‖Q⁻¹ * u ^ 3‖ < 1 := by
  have hQ0 : 0 < Q := by linarith
  have hi : Q⁻¹ < 1 := (inv_lt_one₀ hQ0).mpr (by linarith)
  have hu3 : u ^ 3 ≤ 1 := pow_le_one₀ hu hu1
  rw [Real.norm_of_nonneg (by positivity)]
  exact (mul_le_of_le_one_right (by positivity) hu3).trans_lt hi

theorem frozenLocalSeries_residue_one {Q u : ℝ}
    (hQ : 2 ≤ Q) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    Summable (fun k : ℕ => frozenLocalMajorant Q (k * 3 + 1) * u ^ (k * 3 + 1)) ∧
    (∑' k : ℕ, frozenLocalMajorant Q (k * 3 + 1) * u ^ (k * 3 + 1)) =
      u / (1 - Q⁻¹ * u ^ 3) := by
  have hr := frozenLocalSeries_ratio hQ hu hu1
  have he (k : ℕ) : frozenLocalMajorant Q (k * 3 + 1) * u ^ (k * 3 + 1) =
      u * (Q⁻¹ * u ^ 3) ^ k := by
    rw [frozenLocalMajorant_three_mul_add_one, pow_add, pow_one, mul_pow,
      ← pow_mul, Nat.mul_comm k 3, pow_mul]
    ring
  simp_rw [he]
  refine ⟨(summable_geometric_of_norm_lt_one hr).mul_left u, ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hr, div_eq_mul_inv]

set_option maxHeartbeats 1000000 in
theorem frozenLocalSeries_residue_zero {Q u : ℝ}
    (hQ : 2 ≤ Q) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    Summable (fun k : ℕ => frozenLocalMajorant Q (k * 3) * u ^ (k * 3)) ∧
    (∑' k : ℕ, frozenLocalMajorant Q (k * 3) * u ^ (k * 3)) =
      1 + Real.sqrt Q * Q⁻¹ * u ^ 3 / (1 - Q⁻¹ * u ^ 3) := by
  have hr := frozenLocalSeries_ratio hQ hu hu1
  have he (k : ℕ) : frozenLocalMajorant Q ((k + 1) * 3) * u ^ ((k + 1) * 3) =
      (Real.sqrt Q * Q⁻¹ * u ^ 3) * (Q⁻¹ * u ^ 3) ^ k := by
    rw [frozenLocalMajorant_three_mul_succ, pow_add, pow_one, Nat.add_mul,
      pow_add, one_mul, mul_pow, Nat.mul_comm k 3, pow_mul]
    ring
  have ht : Summable (fun k : ℕ => frozenLocalMajorant Q ((k + 1) * 3) *
      u ^ ((k + 1) * 3)) := by
    simp_rw [he]
    exact (summable_geometric_of_norm_lt_one hr).mul_left _
  have hs : Summable (fun k : ℕ => frozenLocalMajorant Q (k * 3) * u ^ (k * 3)) :=
    (summable_nat_add_iff 1).mp ht
  refine ⟨hs, ?_⟩
  rw [hs.tsum_eq_zero_add]
  simp only [zero_mul, frozenLocalMajorant_zero, pow_zero, mul_one]
  simp_rw [he]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hr, div_eq_mul_inv]

/-- Summability is proved by the actual residue-class bijection, not assumed. -/
theorem frozenLocalSeries_summable {Q u : ℝ}
    (hQ : 2 ≤ Q) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    Summable (fun e : ℕ => frozenLocalMajorant Q e * u ^ e) := by
  let e : Fin 3 × ℕ ≃ ℕ := (Equiv.prodComm (Fin 3) ℕ).trans (Nat.divModEquiv 3).symm
  apply e.summable_iff.mp
  change Summable (fun p : Fin 3 × ℕ =>
    frozenLocalMajorant Q (p.2 * 3 + p.1.val) * u ^ (p.2 * 3 + p.1.val))
  apply (summable_prod_of_nonneg (by
    intro p
    exact mul_nonneg (frozenLocalMajorant_nonneg (by linarith) _) (pow_nonneg hu _))).mpr
  refine ⟨?_, (hasSum_fintype _).summable⟩
  intro r
  fin_cases r
  · simpa using (frozenLocalSeries_residue_zero hQ hu hu1).1
  · exact (frozenLocalSeries_residue_one hQ hu hu1).1
  · simp only [frozenLocalMajorant_three_mul_add_two, zero_mul]
    exact summable_zero

theorem frozenLocalSeries_eq {Q u : ℝ} (hQ : 2 ≤ Q) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    frozenLocalSeries Q u =
      1 + (u + Real.sqrt Q * Q⁻¹ * u ^ 3) / (1 - Q⁻¹ * u ^ 3) := by
  let e : Fin 3 × ℕ ≃ ℕ := (Equiv.prodComm (Fin 3) ℕ).trans (Nat.divModEquiv 3).symm
  have hs := e.summable_iff.mpr (frozenLocalSeries_summable hQ hu hu1)
  change Summable (fun p : Fin 3 × ℕ =>
    frozenLocalMajorant Q (p.2 * 3 + p.1.val) * u ^ (p.2 * 3 + p.1.val)) at hs
  rw [frozenLocalSeries, ← e.tsum_eq]
  change (∑' p : Fin 3 × ℕ,
    frozenLocalMajorant Q (p.2 * 3 + p.1.val) * u ^ (p.2 * 3 + p.1.val)) = _
  rw [hs.tsum_prod, tsum_fintype, Fin.sum_univ_three]
  change (∑' k : ℕ, frozenLocalMajorant Q (k * 3 + 0) * u ^ (k * 3 + 0)) +
      (∑' k : ℕ, frozenLocalMajorant Q (k * 3 + 1) * u ^ (k * 3 + 1)) +
      (∑' k : ℕ, frozenLocalMajorant Q (k * 3 + 2) * u ^ (k * 3 + 2)) = _
  simp only [(frozenLocalSeries_residue_zero hQ hu hu1).2,
    (frozenLocalSeries_residue_one hQ hu hu1).2,
    frozenLocalMajorant_three_mul_add_two, zero_mul, tsum_zero, add_zero]
  ring

theorem frozenLocalSeries_nonneg {Q u : ℝ} (hQ : 0 ≤ Q) (hu : 0 ≤ u) :
    0 ≤ frozenLocalSeries Q u :=
  tsum_nonneg fun e => mul_nonneg (frozenLocalMajorant_nonneg hQ e) (pow_nonneg hu e)

theorem frozenLocalSeries_le_at_one {Q u : ℝ}
    (hQ : 2 ≤ Q) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    frozenLocalSeries Q u ≤ frozenLocalSeries Q 1 := by
  apply Summable.tsum_le_tsum
    (fun e => mul_le_mul_of_nonneg_left (by simpa using pow_le_one₀ hu hu1 (n := e))
      (frozenLocalMajorant_nonneg (by linarith) e))
    (frozenLocalSeries_summable hQ hu hu1)
    (frozenLocalSeries_summable hQ zero_le_one le_rfl)

/-- The paper's absolute local constant, uniform down to sigma=0. -/
theorem frozenLocalSeries_le {Q u : ℝ}
    (hQ : 2 ≤ Q) (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    frozenLocalSeries Q u ≤ 3 + Real.sqrt 2 := by
  apply (frozenLocalSeries_le_at_one hQ hu hu1).trans
  rw [frozenLocalSeries_eq hQ zero_le_one le_rfl]
  simp only [one_pow, mul_one]
  have hQ0 : 0 < Q := by linarith
  have hinv : Q⁻¹ ≤ (1 / 2 : ℝ) := by
    rw [← one_div, div_le_iff₀ hQ0]
    linarith
  have hsQ : (Real.sqrt Q) ^ 2 = Q := Real.sq_sqrt (by positivity)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hmono : Real.sqrt 2 ≤ Real.sqrt Q := Real.sqrt_le_sqrt hQ
  have hnum : Real.sqrt Q * Q⁻¹ ≤ Real.sqrt 2 / 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hQ0]
    have hmul : 2 ≤ Real.sqrt 2 * Real.sqrt Q := by
      nlinarith [mul_nonneg (Real.sqrt_nonneg 2) (sub_nonneg.mpr hmono)]
    nlinarith [mul_nonneg (Real.sqrt_nonneg Q) (sub_nonneg.mpr hmul),
      congrArg (fun t : ℝ => Real.sqrt 2 * t) hsQ]
  have hden : 0 < 1 - Q⁻¹ := by linarith
  have hb : (1 + Real.sqrt Q * Q⁻¹) / (1 - Q⁻¹) ≤ 2 + Real.sqrt 2 := by
    rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg (by positivity : 0 ≤ 2 + Real.sqrt 2)
      (show 0 ≤ 1 / 2 - Q⁻¹ by linarith)]
  linarith

/-- The actual real-exponent Dirichlet series, rather than a formal rational expression. -/
def frozenLocalDirichlet (Q σ : ℝ) : ℝ :=
  ∑' e : ℕ, frozenLocalMajorant Q e * Q ^ (-σ * (e : ℝ))

theorem frozenLocalDirichlet_eq_series {Q : ℝ} (hQ : 0 ≤ Q) (σ : ℝ) :
    frozenLocalDirichlet Q σ = frozenLocalSeries Q (Q ^ (-σ)) := by
  unfold frozenLocalDirichlet frozenLocalSeries
  apply tsum_congr
  intro e
  rw [Real.rpow_mul_natCast hQ]

theorem frozenLocalDirichlet_summable {Q σ : ℝ} (hQ : 2 ≤ Q) (hσ : 0 ≤ σ) :
    Summable (fun e : ℕ => frozenLocalMajorant Q e * Q ^ (-σ * (e : ℝ))) := by
  have hu : Q ^ (-σ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  simpa only [Real.rpow_mul_natCast (show 0 ≤ Q by linarith)] using
    frozenLocalSeries_summable hQ (Real.rpow_nonneg (by linarith) _) hu

theorem frozenLocalDirichlet_le {Q σ : ℝ} (hQ : 2 ≤ Q) (hσ : 0 ≤ σ) :
    frozenLocalDirichlet Q σ ≤ 3 + Real.sqrt 2 := by
  rw [frozenLocalDirichlet_eq_series (by linarith)]
  exact frozenLocalSeries_le hQ (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith))

theorem frozenLocalDirichlet_eq {Q σ : ℝ} (hQ : 2 ≤ Q) (hσ : 0 ≤ σ) :
    frozenLocalDirichlet Q σ =
      1 + (Q ^ (-σ) + Q ^ (-(1 / 2 : ℝ) - 3 * σ)) /
        (1 - Q ^ (-(1 : ℝ) - 3 * σ)) := by
  have hQ0 : 0 < Q := by linarith
  rw [frozenLocalDirichlet_eq_series hQ0.le,
    frozenLocalSeries_eq hQ (Real.rpow_nonneg hQ0.le _)
      (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith))]
  have hp : (Q ^ (-σ)) ^ (3 : ℕ) = Q ^ (-3 * σ) := by
    rw [← Real.rpow_mul_natCast hQ0.le]
    congr 1
    ring
  have hr : Q⁻¹ * (Q ^ (-σ)) ^ (3 : ℕ) = Q ^ (-(1 : ℝ) - 3 * σ) := by
    rw [hp, ← Real.rpow_neg_one, ← Real.rpow_add hQ0]
    congr 1
    ring
  have hn : Real.sqrt Q * Q⁻¹ * (Q ^ (-σ)) ^ (3 : ℕ) =
      Q ^ (-(1 / 2 : ℝ) - 3 * σ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg_one, hp,
      ← Real.rpow_add hQ0, ← Real.rpow_add hQ0]
    congr 1
    ring
  rw [hr, hn]

end
end SimultaneousPrimitiveRoots
