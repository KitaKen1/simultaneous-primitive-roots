module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Statements
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Scalars
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

/-!
# (eq:birth-address-count): the number of potential birth addresses

Source: `verification/stage7-sources/S-02.tex`, lines 1063–1068 (`[S-02:1063–1068]`).

`birthAddressCount : BirthAddressCount` — "`A_* ≤ M|ℬ|(N+1) + (N+1)|ℬ|B = L^{O(1)}`. The implied
exponent can be taken independent of `J` once `x` is sufficiently large for fixed `J`": here
`A_* ≤ L³`. The proof uses `|ℬ| ≤ C₀ T` (Definition 3.1), `N + 1 ≤ 3 L^{0.52}`,
`M + B ≤ 2 L²` and `C₀ T ≤ L^{0.4}/6` for large `x`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

open Filter

noncomputable section

/-- **(eq:birth-address-count)** [S-02:1063–1068], proved: `A_* ≤ L³` for `x ≥ x₀(P, J)`. -/
theorem birthAddressCount : BirthAddressCount := by
  intro P J
  have hC₀ := P.C₀_pos
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp
    ((eventually_log_ge (max 1 ((J : ℝ) + P.ℓ + 1))).and
      ((eventually_rpow_ge ((13 : ℝ) / 25) 3 (by norm_num)).and
        (eventually_loglog_le ((2 : ℝ) / 5) (1 / (6 * P.C₀)) (by norm_num)
          (one_div_pos.mpr (mul_pos (by norm_num) hC₀)))))
  refine ⟨x₀, fun x hx S B _ _ _ _ 𝔊 => ?_⟩
  obtain ⟨hL, h13, hT⟩ := hx₀ x hx
  have hL1 : 1 ≤ Real.log x := le_trans (le_max_left _ _) hL
  have hLJ : (J : ℝ) + P.ℓ + 1 ≤ Real.log x := le_trans (le_max_right _ _) hL
  have hL0 : 0 < Real.log x := by linarith
  have hN : (Graph.sourceMemoryLength (Real.log x) : ℝ) + 1 ≤
      3 * Real.log x ^ ((13 : ℝ) / 25) := by
    have := Graph.source_memory_length_upper (Real.log x) hL0.le
    linarith
  have hB : (Fintype.card B : ℝ) ≤ Real.log x ^ ((2 : ℝ) / 5) / 6 := by
    have h1 := 𝔊.card_big_le
    have h2 : P.C₀ * Real.log (Real.log x) ≤
        P.C₀ * (1 / (6 * P.C₀) * Real.log x ^ ((2 : ℝ) / 5)) :=
      mul_le_mul_of_nonneg_left hT hC₀.le
    have h3 : P.C₀ * (1 / (6 * P.C₀) * Real.log x ^ ((2 : ℝ) / 5)) =
        Real.log x ^ ((2 : ℝ) / 5) / 6 := by
      have hne := hC₀.ne'
      field_simp
    linarith
  have hBc : (J : ℝ) + P.ℓ + (memCutoff (Real.log x) : ℝ) ≤ 2 * Real.log x ^ (2 : ℝ) := by
    have h1 : (memCutoff (Real.log x) : ℝ) < Real.log x ^ 2 + 1 :=
      Nat.ceil_lt_add_one (sq_nonneg _)
    have h2 : Real.log x ^ (2 : ℝ) = Real.log x ^ 2 := Real.rpow_two _
    have h3 : Real.log x ≤ Real.log x ^ 2 := by nlinarith
    rw [h2]
    linarith
  have hN0 : (0 : ℝ) ≤ (Graph.sourceMemoryLength (Real.log x) : ℝ) + 1 := by positivity
  have hB0 : (0 : ℝ) ≤ (Fintype.card B : ℝ) := Nat.cast_nonneg _
  have hBc0 : (0 : ℝ) ≤ (J : ℝ) + P.ℓ + (memCutoff (Real.log x) : ℝ) := by positivity
  have h13' : 0 ≤ 3 * Real.log x ^ ((13 : ℝ) / 25) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg hL0.le _)
  have h25' : 0 ≤ Real.log x ^ ((2 : ℝ) / 5) / 6 :=
    div_nonneg (Real.rpow_nonneg hL0.le _) (by norm_num)
  have hprod : ((Graph.sourceMemoryLength (Real.log x) : ℝ) + 1) * (Fintype.card B : ℝ) *
        ((J : ℝ) + P.ℓ + (memCutoff (Real.log x) : ℝ)) ≤
      3 * Real.log x ^ ((13 : ℝ) / 25) * (Real.log x ^ ((2 : ℝ) / 5) / 6) *
        (2 * Real.log x ^ (2 : ℝ)) :=
    mul_le_mul (mul_le_mul hN hB hB0 h13') hBc hBc0 (mul_nonneg h13' h25')
  have hpow : 3 * Real.log x ^ ((13 : ℝ) / 25) * (Real.log x ^ ((2 : ℝ) / 5) / 6) *
        (2 * Real.log x ^ (2 : ℝ)) = Real.log x ^ ((13 : ℝ) / 25 + 2 / 5 + 2) := by
    rw [Real.rpow_add hL0, Real.rpow_add hL0]
    ring
  have hle : Real.log x ^ ((13 : ℝ) / 25 + 2 / 5 + 2) ≤ Real.log x ^ (3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  rw [birthAddr_card]
  push_cast
  calc ((J : ℝ) + P.ℓ) * (Fintype.card B : ℝ) *
          ((Graph.sourceMemoryLength (Real.log x) : ℝ) + 1) +
        ((Graph.sourceMemoryLength (Real.log x) : ℝ) + 1) * (Fintype.card B : ℝ) *
          (memCutoff (Real.log x) : ℝ)
      = ((Graph.sourceMemoryLength (Real.log x) : ℝ) + 1) * (Fintype.card B : ℝ) *
          ((J : ℝ) + P.ℓ + (memCutoff (Real.log x) : ℝ)) := by ring
    _ ≤ 3 * Real.log x ^ ((13 : ℝ) / 25) * (Real.log x ^ ((2 : ℝ) / 5) / 6) *
          (2 * Real.log x ^ (2 : ℝ)) := hprod
    _ = Real.log x ^ ((13 : ℝ) / 25 + 2 / 5 + 2) := hpow
    _ ≤ Real.log x ^ (3 : ℝ) := hle

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
