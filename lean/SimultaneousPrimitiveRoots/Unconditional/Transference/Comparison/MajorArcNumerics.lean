module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.MajorArcKernel
public import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Denominators at most `Q`: discarded cells, log localization and the arithmetic

Source: `verification/stage7-sources/S-03.tex`, lines 352–437 (`[S-03:0352–0437]`).

* `Major.cellKernel_eq_zero_of_discarded`, `Major.gap_eq_of_left_zero`,
  `Major.gap_eq_of_right_zero` — "the comparison term is zero on this event" [S-03:0359].
* `Major.abs_log_sub_lt` — "both matched log products differ by less than `h`" [S-03:0379].
* `Major.slow_bound` — (eq:ideal-log-error) before the kernel costs:
  `|ζ| · 2h + 2π |β| X · 4h ≤ 258 h L^{max(s_*, C₄)}` when `X ≤ 4Z` and `|β| Z ≤ 2S/r`.
* `Major.discarded_sqrt_le`, `Major.log_error_le`, `Major.char_error_le` — the three lines of
  (eq:ideal-parameter-order) for `r ≤ Q`: each error is at most `L^{-B₀}/4`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

namespace Major

theorem norm_dilPhase_le_one (ζ α : ℝ) (n : ℕ) : ‖dilPhase ζ α n‖ ≤ 1 := by
  unfold dilPhase
  rw [norm_mul, norm_expUnit, mul_one]
  exact Phase.norm_natCast_cpow_le_one n ζ

/-- "Both matched log products differ by less than `h`" [S-03:0379]. -/
theorem abs_log_sub_lt {h : ℝ} (hh : 0 < h) {D X : ℕ} (hc : logCell h D = logCell h X) :
    |Real.log (D : ℝ) - Real.log (X : ℝ)| < h := by
  unfold logCell at hc
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor hc
  rwa [← sub_div, abs_div, abs_of_pos hh, div_lt_one hh] at h1

section Kernel

variable {B : Type} [Fintype B] [DecidableEq B] {J : ℕ}

/-- "The comparison term is zero on this event" [S-03:0359]: the kernel vanishes when `X` lies
in a discarded cell. -/
theorem cellKernel_eq_zero_of_discarded {big : B → Finset ℕ} {Λ : B → Finset (Fin J)}
    {Q h ξ : ℝ} {D X : ℕ} (hX : cellMass big Λ h (logCell h X) < ξ) :
    cellKernel big Λ Q h ξ D X = 0 := by
  unfold cellKernel
  refine if_neg fun hc => ?_
  have h2 : ξ ≤ cellMass big Λ h (logCell h X) := by
    rw [← hc.1]
    exact hc.2
  exact absurd h2 (not_le.mpr hX)

theorem gap_eq_of_left_zero (big : B → Finset ℕ) (A Bs : B → Finset (Fin J)) (Q h ξ α ζ : ℝ)
    (xA : AuxList big A) (xB : AuxList big Bs)
    (hz : ∀ dA : AuxList big A,
      cellKernel big A Q h ξ (tupleProd A dA) (tupleProd A xA) = 0) :
    gap big A Bs Q h ξ α ζ xA xB = dilPhase ζ α (tupleProd A xA * tupleProd Bs xB) := by
  have hsum : ∑ dA : AuxList big A, ∑ dB : AuxList big Bs,
      ((auxWeight big A dA * auxWeight big Bs dB : ℝ) : ℂ) *
        (cellKernel big A Q h ξ (tupleProd A dA) (tupleProd A xA) *
          cellKernel big Bs Q h ξ (tupleProd Bs dB) (tupleProd Bs xB) *
          dilPhase ζ α (tupleProd A dA * tupleProd Bs dB)) = 0 :=
    Finset.sum_eq_zero fun dA _ => Finset.sum_eq_zero fun dB _ => by
      rw [hz dA, zero_mul, zero_mul, mul_zero]
  unfold gap
  rw [hsum, sub_zero]

theorem gap_eq_of_right_zero (big : B → Finset ℕ) (A Bs : B → Finset (Fin J)) (Q h ξ α ζ : ℝ)
    (xA : AuxList big A) (xB : AuxList big Bs)
    (hz : ∀ dB : AuxList big Bs,
      cellKernel big Bs Q h ξ (tupleProd Bs dB) (tupleProd Bs xB) = 0) :
    gap big A Bs Q h ξ α ζ xA xB = dilPhase ζ α (tupleProd A xA * tupleProd Bs xB) := by
  have hsum : ∑ dA : AuxList big A, ∑ dB : AuxList big Bs,
      ((auxWeight big A dA * auxWeight big Bs dB : ℝ) : ℂ) *
        (cellKernel big A Q h ξ (tupleProd A dA) (tupleProd A xA) *
          cellKernel big Bs Q h ξ (tupleProd Bs dB) (tupleProd Bs xB) *
          dilPhase ζ α (tupleProd A dA * tupleProd Bs dB)) = 0 :=
    Finset.sum_eq_zero fun dA _ => Finset.sum_eq_zero fun dB _ => by
      rw [hz dB, mul_zero, zero_mul, mul_zero]
  unfold gap
  rw [hsum, sub_zero]

end Kernel

/-! ### The arithmetic -/

/-- **(eq:ideal-log-error)**, the variation of the multiplier: `τ = 2h`, `X ≤ 4Z`,
`|β| Z ≤ 2S/r`, `|ζ|, S ≤ L^{max(s_*, C₄)}`. -/
theorem slow_bound {ζ β τh Lm Z S Xr : ℝ} {r : ℕ} (hr : 0 < r) (hh : 0 ≤ τh) (hζ : |ζ| ≤ Lm)
    (hS : S ≤ Lm) (hS0 : 0 ≤ S) (hLm : 0 ≤ Lm) (hβZ : |β| * Z ≤ 2 * S / (r : ℝ))
    (hXZ : Xr ≤ 4 * Z) :
    |ζ| * (2 * τh) + 2 * Real.pi * (|β| * (Xr * (2 * (2 * τh)))) ≤ 258 * τh * Lm := by
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := Nat.one_le_cast.mpr hr
  have h1 : 2 * S / (r : ℝ) ≤ 2 * S := div_le_self (by linarith) hr1
  have h3 : |β| * Xr ≤ |β| * (4 * Z) := mul_le_mul_of_nonneg_left hXZ (abs_nonneg _)
  have h2 : |β| * Xr ≤ 8 * Lm := by linarith
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have h4 : |ζ| * (2 * τh) ≤ Lm * (2 * τh) := mul_le_mul_of_nonneg_right hζ (by linarith)
  have h5 : |β| * (Xr * (2 * (2 * τh))) = |β| * Xr * (4 * τh) := by ring
  have h6 : |β| * Xr * (4 * τh) ≤ 8 * Lm * (4 * τh) :=
    mul_le_mul_of_nonneg_right h2 (by linarith)
  have h0 : 0 ≤ 8 * Lm * (4 * τh) :=
    mul_nonneg (mul_nonneg (by norm_num) hLm) (mul_nonneg (by norm_num) hh)
  have h7 : 2 * Real.pi * (8 * Lm * (4 * τh)) ≤ 2 * 4 * (8 * Lm * (4 * τh)) :=
    mul_le_mul_of_nonneg_right (by linarith) h0
  have h8 : 2 * Real.pi * (|β| * Xr * (4 * τh)) ≤ 2 * Real.pi * (8 * Lm * (4 * τh)) :=
    mul_le_mul_of_nonneg_left h6 (by linarith)
  have h9 : Lm * (2 * τh) + 2 * 4 * (8 * Lm * (4 * τh)) = 258 * τh * Lm := by ring
  rw [h5]
  exact (add_le_add h4 (h8.trans h7)).trans (le_of_eq h9)

/-- The square root of the discarded mass (eq:ideal-discarded-mass) is at most `L^{-B₀}/4`:
"`N_A, N_B ≤ L^{d+1+h_*}` for large `x`" and `x_* > 2B₀ + d + 1 + h_* + 10`. -/
theorem discarded_sqrt_le {L B₀ d hs xs C₂ cnt : ℝ} (hL : 32 * C₂ ≤ L) (hC₂ : 1 ≤ C₂)
    (hd : 0 < d) (hhs : 0 ≤ hs) (hxs : 2 * B₀ + d + 1 + hs + 10 < xs)
    (hcnt : cnt ≤ C₂ * (1 + L ^ d * Real.log L / L ^ (-hs))) :
    Real.sqrt (cnt * L ^ (-xs)) ≤ L ^ (-B₀) / 4 := by
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hT : Real.log L ≤ L := by
    have h := Real.log_le_sub_one_of_pos hL0
    linarith
  have hLd : 0 < L ^ d := Real.rpow_pos_of_pos hL0 _
  have hLh : 0 < L ^ hs := Real.rpow_pos_of_pos hL0 _
  have e1 : L ^ d * Real.log L / L ^ (-hs) = L ^ d * Real.log L * L ^ hs := by
    rw [Real.rpow_neg hL0.le, div_inv_eq_mul]
  have hW : L ^ (d + 1 + hs) = L ^ d * L * L ^ hs := by
    rw [Real.rpow_add hL0, Real.rpow_add_one hL0.ne']
  have h1 : L ^ d * Real.log L * L ^ hs ≤ L ^ (d + 1 + hs) := by
    rw [hW]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT hLd.le) hLh.le
  have hW1 : 1 ≤ L ^ (d + 1 + hs) := Real.one_le_rpow hL1 (by linarith)
  have h2 : cnt ≤ 2 * C₂ * L ^ (d + 1 + hs) := by
    rw [e1] at hcnt
    have h3 : C₂ * (1 + L ^ d * Real.log L * L ^ hs) ≤ C₂ * (2 * L ^ (d + 1 + hs)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  have hx0 : 0 < L ^ (-xs) := Real.rpow_pos_of_pos hL0 _
  have h4 : cnt * L ^ (-xs) ≤ 2 * C₂ * L ^ (-(2 * B₀ + 10)) := by
    have h5 : cnt * L ^ (-xs) ≤ 2 * C₂ * L ^ (d + 1 + hs) * L ^ (-xs) :=
      mul_le_mul_of_nonneg_right h2 hx0.le
    have h6 : L ^ (d + 1 + hs) * L ^ (-xs) ≤ L ^ (-(2 * B₀ + 10)) := by
      rw [← Real.rpow_add hL0]
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have h7 : 2 * C₂ * (L ^ (d + 1 + hs) * L ^ (-xs)) ≤ 2 * C₂ * L ^ (-(2 * B₀ + 10)) :=
      mul_le_mul_of_nonneg_left h6 (by linarith)
    linarith
  have h8 : 2 * C₂ * L ^ (-(2 * B₀ + 10)) ≤ (L ^ (-B₀) / 4) ^ 2 := by
    have h9 : L ^ (-(2 * B₀ + 10)) = L ^ (-B₀) * L ^ (-B₀) * L ^ (-(10 : ℝ)) := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0]
      congr 1
      ring
    have h10 : L ^ (-(10 : ℝ)) ≤ L ^ (-(1 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have h11 : L ^ (-(1 : ℝ)) = L⁻¹ := Real.rpow_neg_one L
    have h12 : 2 * C₂ * L⁻¹ ≤ 1 / 16 := by
      rw [← div_eq_mul_inv, div_le_iff₀ hL0]
      linarith
    have hB : 0 ≤ L ^ (-B₀) * L ^ (-B₀) :=
      mul_nonneg (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hL0.le _)
    have h13 : 2 * C₂ * L ^ (-(10 : ℝ)) ≤ 1 / 16 := by
      have h : 2 * C₂ * L ^ (-(10 : ℝ)) ≤ 2 * C₂ * L⁻¹ := by
        rw [← h11]
        exact mul_le_mul_of_nonneg_left h10 (by linarith)
      linarith
    have h14 : (L ^ (-B₀) / 4) ^ 2 = L ^ (-B₀) * L ^ (-B₀) * (1 / 16) := by ring
    have h15 : 2 * C₂ * (L ^ (-B₀) * L ^ (-B₀) * L ^ (-(10 : ℝ))) =
        L ^ (-B₀) * L ^ (-B₀) * (2 * C₂ * L ^ (-(10 : ℝ))) := by ring
    rw [h9, h14, h15]
    exact mul_le_mul_of_nonneg_left h13 hB
  have h16 : 0 ≤ L ^ (-B₀) / 4 := div_nonneg (Real.rpow_nonneg hL0.le _) (by norm_num)
  exact (Real.sqrt_le_sqrt (h4.trans h8)).trans (le_of_eq (Real.sqrt_sq h16))

/-- (eq:ideal-log-error) is at most `L^{-B₀}/4`: `h_* > 4 q_* + max(s_*, C₄) + B₀ + 10`. -/
theorem log_error_le {L qs ss C₄ hs B₀ : ℝ} (hL : 1032 ≤ L)
    (hhs : 4 * qs + max ss C₄ + B₀ + 10 < hs) :
    258 * L ^ (-hs) * L ^ (max ss C₄) * ((L ^ qs) ^ 2 * (L ^ qs) ^ 2) ≤ L ^ (-B₀) / 4 := by
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have e1 : L ^ (-hs) * L ^ (max ss C₄) * ((L ^ qs) ^ 2 * (L ^ qs) ^ 2) =
      L ^ (-hs + max ss C₄ + (qs + qs + (qs + qs))) := by
    rw [sq, ← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0,
      ← Real.rpow_add hL0]
  have e2 : L ^ (-hs + max ss C₄ + (qs + qs + (qs + qs))) ≤ L ^ (-B₀ + -(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have e3 : L ^ (-B₀ + -(1 : ℝ)) = L ^ (-B₀) * L⁻¹ := by
    rw [Real.rpow_add hL0, Real.rpow_neg_one]
  have hB : 0 ≤ L ^ (-B₀) := Real.rpow_nonneg hL0.le _
  have h1 : 258 * L⁻¹ ≤ 1 / 4 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hL0]
    linarith
  have h2 : 258 * L ^ (-hs) * L ^ (max ss C₄) * ((L ^ qs) ^ 2 * (L ^ qs) ^ 2) =
      258 * (L ^ (-hs) * L ^ (max ss C₄) * ((L ^ qs) ^ 2 * (L ^ qs) ^ 2)) := by ring
  have h3 : 258 * L ^ (-hs + max ss C₄ + (qs + qs + (qs + qs))) ≤
      258 * (L ^ (-B₀) * L⁻¹) := by
    rw [← e3]
    exact mul_le_mul_of_nonneg_left e2 (by norm_num)
  have h4 : 258 * (L ^ (-B₀) * L⁻¹) = L ^ (-B₀) * (258 * L⁻¹) := by ring
  have h5 : L ^ (-B₀) * (258 * L⁻¹) ≤ L ^ (-B₀) * (1 / 4) := mul_le_mul_of_nonneg_left h1 hB
  have h6 : L ^ (-B₀) * (1 / 4) = L ^ (-B₀) / 4 := by ring
  rw [h2, e1]
  exact h3.trans ((le_of_eq h4).trans (h5.trans (le_of_eq h6)))

/-- (eq:ideal-major-character-error) is at most `L^{-B₀}/4`, for the reproduction precision
`L^{-(B₀ + q_*/2 + 1)}`. -/
theorem char_error_le {L qs B₀ : ℝ} (hL : 12 ≤ L) :
    L ^ (qs / 2) * (3 * L ^ (-(B₀ + qs / 2 + 1))) ≤ L ^ (-B₀) / 4 := by
  have hL0 : 0 < L := by linarith
  have e1 : L ^ (qs / 2) * L ^ (-(B₀ + qs / 2 + 1)) = L ^ (-B₀) * L⁻¹ := by
    rw [← Real.rpow_add hL0, ← Real.rpow_neg_one L, ← Real.rpow_add hL0]
    congr 1
    ring
  have hB : 0 ≤ L ^ (-B₀) := Real.rpow_nonneg hL0.le _
  have h1 : 3 * L⁻¹ ≤ 1 / 4 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hL0]
    linarith
  have h2 : L ^ (qs / 2) * (3 * L ^ (-(B₀ + qs / 2 + 1))) =
      3 * (L ^ (qs / 2) * L ^ (-(B₀ + qs / 2 + 1))) := by ring
  have h3 : 3 * (L ^ (-B₀) * L⁻¹) = L ^ (-B₀) * (3 * L⁻¹) := by ring
  have h4 : L ^ (-B₀) * (3 * L⁻¹) ≤ L ^ (-B₀) * (1 / 4) := mul_le_mul_of_nonneg_left h1 hB
  have h5 : L ^ (-B₀) * (1 / 4) = L ^ (-B₀) / 4 := by ring
  rw [h2, e1]
  exact (le_of_eq h3).trans (h4.trans (le_of_eq h5))

end Major

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
