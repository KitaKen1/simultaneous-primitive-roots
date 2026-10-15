module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Sanity
import Mathlib.Tactic.Ring

/-!
# Sanity check for Lemma 3.4: `physAbsAdj` is the transpose of `physAbsOp`

`PhysicalSchur` bounds the row sums of two operators which are defined separately in
`PhysicalOperator.lean`: `physAbsOp` (the operator `𝒜` with absolute coefficients) and
`physAbsAdj` ("its adjoint"). This file proves that the matrix entry of `physAbsAdj` from `t` to
`s` is the matrix entry of `physAbsOp` from `s` to `t` (`physAbsAdj_transpose_entry`). The entries
are real and nonnegative and all physical states have the same mass, so `physAbsAdj` is the
adjoint of `physAbsOp` in `ℋ_ph`, and `physAbsColSum` is the column sum of `physAbsOp`.

The proof is the proof of `physAdj_adjoint_entry` (`Sanity.lean`) with moduli in the place of
complex conjugates. It is not used in the proof of `physicalSchur`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Schur

open scoped BigOperators

noncomputable section

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝔭 : PosModel} {𝒢 : GroupFamily S B} {q : ℝ} {J ℓ : ℕ}

/-- The matrix entry of the absolute row operation of `ν` from the state `s` to the state `t`. -/
theorem physRowAbs_single [DecidableEq 𝔭.Pos] (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    (s t : PState 𝔭 𝒢 J ℓ) :
    physRowAbs 𝔭 𝒢 q ν k ζ (Pi.single t 1) s =
      ∑ r : AuxList 𝒢.big ν.C, if 𝔭.shift (k * dil ν.C s.2 r) s.1 = t.1 then
        ((‖physCoef 𝔭 𝒢 q ν k ζ s.1 s.2 r t.2‖ : ℝ) : ℂ) else 0 := by
  unfold physRowAbs
  rw [rowOp_single]
  exact sum_prod_ite_mk_eq (fun r => 𝔭.shift (k * dil ν.C s.2 r) s.1) t
    (fun r x' => ((‖physCoef 𝔭 𝒢 q ν k ζ s.1 s.2 r x'‖ : ℝ) : ℂ))

/-- The matrix entry of the absolute adjoint row operation of `ν` from the state `t` to the state
`s`. -/
theorem physRowAdjAbs_single [DecidableEq 𝔭.Pos] (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    (s t : PState 𝔭 𝒢 J ℓ) :
    physRowAdjAbs 𝔭 𝒢 q ν k ζ (Pi.single s 1) t =
      ∑ r : AuxList 𝒢.big ν.C, if 𝔭.shift (-(k * dil ν.C t.2 r)) t.1 = s.1 then
        ((‖physCoef 𝔭 𝒢 q ν k ζ (𝔭.shift (-(k * dil ν.C t.2 r)) t.1) s.2 r t.2‖ : ℝ) : ℂ)
      else 0 := by
  unfold physRowAdjAbs
  rw [rowOp_single]
  exact sum_prod_ite_mk_eq (fun r => 𝔭.shift (-(k * dil ν.C t.2 r)) t.1) s
    (fun r x =>
      ((‖physCoef 𝔭 𝒢 q ν k ζ (𝔭.shift (-(k * dil ν.C t.2 r)) t.1) x r t.2‖ : ℝ) : ℂ))

/-- Before symmetrization, the absolute adjoint row operation is the transpose of the absolute row
operation. -/
theorem physRowAbs_transpose_entry [DecidableEq 𝔭.Pos] (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    (s t : PState 𝔭 𝒢 J ℓ) :
    physRowAdjAbs 𝔭 𝒢 q ν k ζ (Pi.single s 1) t =
      physRowAbs 𝔭 𝒢 q ν k ζ (Pi.single t 1) s := by
  rw [physRowAdjAbs_single, physRowAbs_single]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hD : dil ν.C t.2 r = dil ν.C s.2 r
  · rw [hD]
    by_cases h1 : 𝔭.shift (-(k * (dil ν.C s.2 r : ℤ))) t.1 = s.1
    · have h2 : 𝔭.shift (k * (dil ν.C s.2 r : ℤ)) s.1 = t.1 := by
        rw [← h1]
        exact 𝔭.shift_shift_neg _ _
      rw [if_pos h1, if_pos h2, h1]
    · have h2 : ¬𝔭.shift (k * (dil ν.C s.2 r : ℤ)) s.1 = t.1 := by
        intro h2
        apply h1
        rw [← h2]
        exact 𝔭.shift_neg_shift _ _
      rw [if_neg h1, if_neg h2]
  · have hz : ∀ n : 𝔭.Pos, physCoef 𝔭 𝒢 q ν k ζ n s.2 r t.2 = 0 := by
      intro n
      by_contra hne
      exact hD (dil_eq_of_physCoef_ne_zero hne)
    simp only [hz, norm_zero, Complex.ofReal_zero, ite_self]

variable {N : Type} [Fintype N]

/-- The transpose relation for the sum over patterns, before symmetrization. -/
theorem physRowAbsSum_transpose_entry [DecidableEq 𝔭.Pos] (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ)
    (ζ : ℝ) (a b : PState 𝔭 𝒢 J ℓ) :
    (∑ ν, physRowAdjAbs 𝔭 𝒢 q (𝔉 ν) k ζ) (Pi.single a 1) b =
      (∑ ν, physRowAbs 𝔭 𝒢 q (𝔉 ν) k ζ) (Pi.single b 1) a := by
  simp only [LinearMap.sum_apply, Finset.sum_apply]
  exact Finset.sum_congr rfl fun ν _ => physRowAbs_transpose_entry (𝔉 ν) k ζ a b

/-- **`physAbsAdj` is the transpose of `physAbsOp`**: the matrix entry of `physAbsAdj` from `t` to
`s` is the matrix entry of `physAbsOp` from `s` to `t`. Hence `physAbsColSum` is the column sum of
the operator with absolute coefficients, as in Lemma 3.4. -/
theorem physAbsAdj_transpose_entry [DecidableEq 𝔭.Pos] (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ)
    (ζ : ℝ) (s t : PState 𝔭 𝒢 J ℓ) :
    physAbsAdj 𝔭 𝒢 q 𝔉 k ζ (Pi.single s 1) t = physAbsOp 𝔭 𝒢 q 𝔉 k ζ (Pi.single t 1) s := by
  unfold physAbsAdj physAbsOp
  rw [sym_comp_sym_single, sym_comp_sym_single, Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  refine Finset.sum_congr rfl fun y' _ => ?_
  rw [symKernel_symm t.2 y', symKernel_symm y s.2, physRowAbsSum_transpose_entry]
  ring

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Schur
