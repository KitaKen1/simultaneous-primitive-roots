module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.IdealSanity
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Schur.Pointwise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Lemma 3.4: the row sums of `𝒜` and `𝒜*` with absolute coefficients

Source: `verification/stage7-sources/S-02.tex`, lines 132–158 (`[S-02:0132–0158]`).

* `rowAbsMass`, `colAbsMass` — the sums over patterns, auxiliary labels and lists of the moduli of
  the coefficients of the row operations and of the adjoint row operations at a state, before
  symmetrization. They are what `∑_ν physRowAbs` and `∑_ν physRowAdjAbs` produce from the constant
  function `1` (`sum_physRowAbs_one`, `sum_physRowAdjAbs_one`).
* `rowAbsMass_le`, `colAbsMass_le` — "free-label probabilities have total mass one … taking the
  product over `s = O(T)` groups and using (eq:pattern-mass) gives the row bound":
  both are at most `(∑_ν sup |K_ν|) ∏_g C`, `C = groupConst v₋ q T`.
* `physAbsRowSum_le`, `physAbsColSum_le` — symmetrization fixes the constant function and is an
  average, so the row sums `physAbsRowSum`, `physAbsColSum` of Lemma 3.4 are at most the supremum
  over the states of `rowAbsMass`, `colAbsMass`.

All of this is for an arbitrary position model and an arbitrary family of groups.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Schur

open scoped BigOperators

noncomputable section

/-! ### One pattern: the sum over auxiliary labels and lists -/

/-- **Rows**, one pattern: the moduli of the coefficients of all row transitions from the state
`(n, x)` have sum at most `sup |K_ν| ∏_g C`. -/
theorem sum_physCoef_row_le {S B : Type} [Fintype S] [Fintype B] [DecidableEq S]
    [DecidableEq B] (𝔭 : PosModel) (𝒢 : GroupFamily S B) {q vMinus : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) (hv : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hlaw : ∀ g, ∑ p ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) p = 1) {J ℓ T : ℕ}
    (hT : 0 < T) (hℓT : ℓ ≤ T) (ν : Pattern 𝒢.big J ℓ) (hC : ∀ g, ℓ + (ν.C g).card ≤ T)
    (k : ℤ) (ζ : ℝ) (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ) :
    ∑ ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ, ‖physCoef 𝔭 𝒢 q ν k ζ n x ξ.1 ξ.2‖ ≤
      (ν.supNorm : ℝ) *
        ((∏ _g : S, groupConst vMinus q T) * ∏ _g : B, groupConst vMinus q T) := by
  rw [Fintype.sum_prod_type]
  calc ∑ r : AuxList 𝒢.big ν.C, ∑ x' : Lists 𝒢 J ℓ, ‖physCoef 𝔭 𝒢 q ν k ζ n x r x'‖
      ≤ ∑ r : AuxList 𝒢.big ν.C, auxWeight 𝒢.big ν.C r * ((ν.supNorm : ℝ) *
          ((∏ _g : S, groupConst vMinus q T) * ∏ _g : B, groupConst vMinus q T)) :=
        Finset.sum_le_sum fun r _ =>
          sum_norm_physCoef_row_le 𝔭 𝒢 hq0 hq1 hv hVS hVB hT hℓT ν hC k ζ n x r
    _ = (∑ r : AuxList 𝒢.big ν.C, auxWeight 𝒢.big ν.C r) * ((ν.supNorm : ℝ) *
          ((∏ _g : S, groupConst vMinus q T) * ∏ _g : B, groupConst vMinus q T)) :=
        (Finset.sum_mul _ _ _).symm
    _ = (ν.supNorm : ℝ) *
          ((∏ _g : S, groupConst vMinus q T) * ∏ _g : B, groupConst vMinus q T) := by
        rw [sum_auxWeight hlaw ν.C, one_mul]

/-- **Columns**, one pattern: the moduli of the coefficients of all adjoint row transitions from
the state `(n', x')` have sum at most `sup |K_ν| ∏_g C`. -/
theorem sum_physCoef_col_le {S B : Type} [Fintype S] [Fintype B] [DecidableEq S]
    [DecidableEq B] (𝔭 : PosModel) (𝒢 : GroupFamily S B) {q vMinus : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) (hv : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hlaw : ∀ g, ∑ p ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) p = 1) {J ℓ T : ℕ}
    (hT : 0 < T) (hℓT : ℓ ≤ T) (ν : Pattern 𝒢.big J ℓ) (hC : ∀ g, ℓ + (ν.C g).card ≤ T)
    (k : ℤ) (ζ : ℝ) (n' : 𝔭.Pos) (x' : Lists 𝒢 J ℓ) :
    ∑ ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ,
        ‖physCoef 𝔭 𝒢 q ν k ζ (𝔭.shift (-(k * dil ν.C x' ξ.1)) n') ξ.2 ξ.1 x'‖ ≤
      (ν.supNorm : ℝ) *
        ((∏ _g : S, groupConst vMinus q T) * ∏ _g : B, groupConst vMinus q T) := by
  rw [Fintype.sum_prod_type]
  calc ∑ r : AuxList 𝒢.big ν.C, ∑ x : Lists 𝒢 J ℓ,
        ‖physCoef 𝔭 𝒢 q ν k ζ (𝔭.shift (-(k * dil ν.C x' r)) n') x r x'‖
      ≤ ∑ r : AuxList 𝒢.big ν.C, auxWeight 𝒢.big ν.C r * ((ν.supNorm : ℝ) *
          ((∏ _g : S, groupConst vMinus q T) * ∏ _g : B, groupConst vMinus q T)) :=
        Finset.sum_le_sum fun r _ =>
          sum_norm_physCoef_col_le 𝔭 𝒢 hq0 hq1 hv hVS hVB hT hℓT ν hC k ζ
            (𝔭.shift (-(k * dil ν.C x' r)) n') x' r
    _ = (∑ r : AuxList 𝒢.big ν.C, auxWeight 𝒢.big ν.C r) * ((ν.supNorm : ℝ) *
          ((∏ _g : S, groupConst vMinus q T) * ∏ _g : B, groupConst vMinus q T)) :=
        (Finset.sum_mul _ _ _).symm
    _ = (ν.supNorm : ℝ) *
          ((∏ _g : S, groupConst vMinus q T) * ∏ _g : B, groupConst vMinus q T) := by
        rw [sum_auxWeight hlaw ν.C, one_mul]

/-! ### All patterns -/

/-- The sum over patterns, auxiliary labels and target lists of the moduli of the coefficients of
the row transitions from the state `t`. -/
def rowAbsMass {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ} {N : Type} [Fintype N]
    (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (t : PState 𝔭 𝒢 J ℓ) : ℝ :=
  ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
    ‖physCoef 𝔭 𝒢 q (𝔉 ν) k ζ t.1 t.2 ξ.1 ξ.2‖

/-- The sum over patterns, auxiliary labels and source lists of the moduli of the coefficients of
the adjoint row transitions from the state `t`. -/
def colAbsMass {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ} {N : Type} [Fintype N]
    (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (t : PState 𝔭 𝒢 J ℓ) : ℝ :=
  ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
    ‖physCoef 𝔭 𝒢 q (𝔉 ν) k ζ (𝔭.shift (-(k * dil (𝔉 ν).C t.2 ξ.1)) t.1) ξ.2 ξ.1 t.2‖

/-- **The row bound before symmetrization** [S-02:0150–0154]. -/
theorem rowAbsMass_le {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (𝔭 : PosModel) (𝒢 : GroupFamily S B) {q vMinus : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hv : 0 < vMinus) (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hlaw : ∀ g, ∑ p ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) p = 1) {J ℓ T : ℕ}
    (hT : 0 < T) (hℓT : ℓ ≤ T) {N : Type} [Fintype N] (𝔉 : N → Pattern 𝒢.big J ℓ)
    (hC : ∀ ν g, ℓ + ((𝔉 ν).C g).card ≤ T) (k : ℤ) (ζ : ℝ) (t : PState 𝔭 𝒢 J ℓ) :
    rowAbsMass 𝔭 𝒢 q 𝔉 k ζ t ≤
      patternMass 𝔉 *
        ((∏ _g : S, groupConst vMinus q T) * ∏ _g : B, groupConst vMinus q T) := by
  unfold rowAbsMass patternMass
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun ν _ =>
    sum_physCoef_row_le 𝔭 𝒢 hq0 hq1 hv hVS hVB hlaw hT hℓT (𝔉 ν) (hC ν) k ζ t.1 t.2

/-- **The column bound before symmetrization** [S-02:0154–0156]. -/
theorem colAbsMass_le {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (𝔭 : PosModel) (𝒢 : GroupFamily S B) {q vMinus : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (hv : 0 < vMinus) (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hlaw : ∀ g, ∑ p ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) p = 1) {J ℓ T : ℕ}
    (hT : 0 < T) (hℓT : ℓ ≤ T) {N : Type} [Fintype N] (𝔉 : N → Pattern 𝒢.big J ℓ)
    (hC : ∀ ν g, ℓ + ((𝔉 ν).C g).card ≤ T) (k : ℤ) (ζ : ℝ) (t : PState 𝔭 𝒢 J ℓ) :
    colAbsMass 𝔭 𝒢 q 𝔉 k ζ t ≤
      patternMass 𝔉 *
        ((∏ _g : S, groupConst vMinus q T) * ∏ _g : B, groupConst vMinus q T) := by
  unfold colAbsMass patternMass
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun ν _ =>
    sum_physCoef_col_le 𝔭 𝒢 hq0 hq1 hv hVS hVB hlaw hT hℓT (𝔉 ν) (hC ν) k ζ t.1 t.2

/-! ### Symmetrization -/

/-- Symmetrization fixes every constant function. -/
theorem physSym_const {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (𝔭 : PosModel) (𝒢 : GroupFamily S B) (J ℓ : ℕ) (c : ℂ) :
    physSym 𝔭 𝒢 J ℓ (fun _ => c) = fun _ => c := by
  funext s
  have hne : (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold physSym
  rw [rowOp_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hne, one_mul]

/-- Symmetrization is an average: applied to a real function bounded by `Bd`, it gives a function
bounded by `Bd`. -/
theorem physSym_ofReal_re_le {S B : Type} [Fintype S] [Fintype B] [DecidableEq S]
    [DecidableEq B] (𝔭 : PosModel) (𝒢 : GroupFamily S B) (J ℓ : ℕ)
    (G : PState 𝔭 𝒢 J ℓ → ℝ) (Bd : ℝ) (hG : ∀ t, G t ≤ Bd) (s : PState 𝔭 𝒢 J ℓ) :
    (physSym 𝔭 𝒢 J ℓ (fun t => ((G t : ℝ) : ℂ)) s).re ≤ Bd := by
  have hcard : (0 : ℝ) < (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have h1 : physSym 𝔭 𝒢 J ℓ (fun t => ((G t : ℝ) : ℂ)) s =
      ((∑ π : SlotPerms S J ℓ × SlotPerms B J ℓ,
        (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℝ)⁻¹ *
          G (s.1, permuteLists π s.2) : ℝ) : ℂ) := by
    unfold physSym
    rw [rowOp_apply, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
  rw [h1, Complex.ofReal_re]
  calc ∑ π : SlotPerms S J ℓ × SlotPerms B J ℓ,
        (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℝ)⁻¹ *
          G (s.1, permuteLists π s.2)
      ≤ ∑ _π : SlotPerms S J ℓ × SlotPerms B J ℓ,
        (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℝ)⁻¹ * Bd :=
        Finset.sum_le_sum fun π _ =>
          mul_le_mul_of_nonneg_left (hG _) (inv_nonneg.mpr hcard.le)
    _ = Bd := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          mul_inv_cancel₀ hcard.ne', one_mul]

/-! ### The row sums of Lemma 3.4 -/

/-- The sum over patterns of the absolute row operations, applied to the constant function `1`. -/
theorem sum_physRowAbs_one {S B : Type} [Fintype S] [Fintype B] [DecidableEq S]
    [DecidableEq B] (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ} {N : Type}
    [Fintype N] (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) :
    (∑ ν, physRowAbs 𝔭 𝒢 q (𝔉 ν) k ζ) (fun _ => 1) =
      fun t => ((rowAbsMass 𝔭 𝒢 q 𝔉 k ζ t : ℝ) : ℂ) := by
  funext t
  show (∑ ν, physRowAbs 𝔭 𝒢 q (𝔉 ν) k ζ) (fun _ => 1) t =
    ((rowAbsMass 𝔭 𝒢 q 𝔉 k ζ t : ℝ) : ℂ)
  rw [LinearMap.sum_apply, Finset.sum_apply]
  unfold rowAbsMass
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  unfold physRowAbs
  rw [rowOp_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  exact mul_one _

/-- The sum over patterns of the absolute adjoint row operations, applied to the constant
function `1`. -/
theorem sum_physRowAdjAbs_one {S B : Type} [Fintype S] [Fintype B] [DecidableEq S]
    [DecidableEq B] (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ} {N : Type}
    [Fintype N] (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) :
    (∑ ν, physRowAdjAbs 𝔭 𝒢 q (𝔉 ν) k ζ) (fun _ => 1) =
      fun t => ((colAbsMass 𝔭 𝒢 q 𝔉 k ζ t : ℝ) : ℂ) := by
  funext t
  show (∑ ν, physRowAdjAbs 𝔭 𝒢 q (𝔉 ν) k ζ) (fun _ => 1) t =
    ((colAbsMass 𝔭 𝒢 q 𝔉 k ζ t : ℝ) : ℂ)
  rw [LinearMap.sum_apply, Finset.sum_apply]
  unfold colAbsMass
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  unfold physRowAdjAbs
  rw [rowOp_apply, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  exact mul_one _

/-- The row sum of the operator with absolute coefficients is at most the supremum over the
states of the unsymmetrized row sums. -/
theorem physAbsRowSum_le {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ} {N : Type} [Fintype N]
    (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (Bd : ℝ)
    (h : ∀ t, rowAbsMass 𝔭 𝒢 q 𝔉 k ζ t ≤ Bd) (s : PState 𝔭 𝒢 J ℓ) :
    physAbsRowSum 𝔭 𝒢 q 𝔉 k ζ s ≤ Bd := by
  unfold physAbsRowSum physAbsOp
  rw [LinearMap.comp_apply, LinearMap.comp_apply, physSym_const 𝔭 𝒢 J ℓ 1,
    sum_physRowAbs_one]
  exact physSym_ofReal_re_le 𝔭 𝒢 J ℓ (rowAbsMass 𝔭 𝒢 q 𝔉 k ζ) Bd h s

/-- The row sum of the adjoint of the operator with absolute coefficients is at most the supremum
over the states of the unsymmetrized column sums. -/
theorem physAbsColSum_le {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ} {N : Type} [Fintype N]
    (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (Bd : ℝ)
    (h : ∀ t, colAbsMass 𝔭 𝒢 q 𝔉 k ζ t ≤ Bd) (s : PState 𝔭 𝒢 J ℓ) :
    physAbsColSum 𝔭 𝒢 q 𝔉 k ζ s ≤ Bd := by
  unfold physAbsColSum physAbsAdj
  rw [LinearMap.comp_apply, LinearMap.comp_apply, physSym_const 𝔭 𝒢 J ℓ 1,
    sum_physRowAdjAbs_one]
  exact physSym_ofReal_re_le 𝔭 𝒢 J ℓ (colAbsMass 𝔭 𝒢 q 𝔉 k ζ) Bd h s

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Schur
