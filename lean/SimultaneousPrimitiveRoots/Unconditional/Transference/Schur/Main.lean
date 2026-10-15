module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Statements
public import SimultaneousPrimitiveRoots.Unconditional.Transference.GraphBridge
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Schur.RowSums
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# [S] Lemma 3.4 (absolute physical bounds): `physicalSchur : PhysicalSchur`

Source: `verification/stage7-sources/S-02.tex`, lines 132–158 (`[S-02:0132–0158]`).

The exponent is

`schurExponent P m C₁ = C₁ + 2 · C₀ · log (groupConst v₋ q (ℓ + m))`,

`groupConst v₋ q T = max(1, 1/v₋)^T · max(1, sup_{z ≥ 0} (z + T)^T q^{z/2})`.

It depends on `m`, `C₁` and the constants `C₀, v₋, q, ℓ` of Definition 3.1, and on nothing else; in
particular not on `J` and not on `C₂`. The bound holds for every `x > 1` (the threshold used is
`x₀ = 2`), for every position model, hence for integer positions (`IntSchurBound`) and for
residue positions (`ResidueSchurBound`).

* `C₁` comes from (eq:pattern-mass), `∑_ν sup |K_ν| ≤ L^{C₁}`;
* each of the two factors `C₀ · log (groupConst …)` comes from the product of the group constants
  over the small, respectively the big, groups, whose number is at most `C₀ log L`
  (`PrimeGroups.prod_small_le_rpow`, `PrimeGroups.prod_big_le_rpow`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference

open scoped BigOperators

noncomputable section

/-- **The exponent `C_abs` of Lemma 3.4**: `C₁ + 2 C₀ log C`, where `C = groupConst v₋ q (ℓ + m)`
is the constant of (eq:physical-count-bound). It depends only on `m`, `C₁` and the fixed data of
Definition 3.1. -/
def schurExponent (P : GroupParams) (m : ℕ) (C₁ : ℝ) : ℝ :=
  C₁ + (Real.log (Schur.groupConst P.vMinus P.q (P.ℓ + m)) * P.C₀ +
    Real.log (Schur.groupConst P.vMinus P.q (P.ℓ + m)) * P.C₀)

/-- **Lemma 3.4 for an arbitrary position model**, for every `x` with `log x > 0`: the operator
with absolute coefficients and its adjoint have row sums at most `L^{C_abs}` at every state. -/
theorem schur_bound (P : GroupParams) (m : ℕ) (C₁ : ℝ) {J : ℕ} {C₂ : ℝ} {x : ℝ}
    (hx : 0 < Real.log x) {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (𝔊 : PrimeGroups P x S B) (𝔭 : PosModel) {N : Type} [Fintype N]
    (𝔉 : N → Pattern 𝔊.big J P.ℓ) (ζ : ℝ) (k : ℤ)
    (hadm : Admissible (Real.log x) m C₁ C₂ 𝔉 k) (s : PState 𝔭 𝔊.toGroupFamily J P.ℓ) :
    physAbsRowSum 𝔭 𝔊.toGroupFamily P.q 𝔉 k ζ s ≤ Real.log x ^ schurExponent P m C₁ ∧
      physAbsColSum 𝔭 𝔊.toGroupFamily P.q 𝔉 k ζ s ≤ Real.log x ^ schurExponent P m C₁ := by
  have hT : 0 < P.ℓ + m := Nat.add_pos_left P.ℓ_pos m
  have hℓT : P.ℓ ≤ P.ℓ + m := Nat.le_add_right P.ℓ m
  have hC : ∀ ν g, P.ℓ + ((𝔉 ν).C g).card ≤ P.ℓ + m := fun ν g =>
    Nat.add_le_add_left (hadm.1 ν g) P.ℓ
  have hG1 : 1 ≤ Schur.groupConst P.vMinus P.q (P.ℓ + m) :=
    Schur.one_le_groupConst P.vMinus P.q (P.ℓ + m)
  have hGpos : 0 < Schur.groupConst P.vMinus P.q (P.ℓ + m) := lt_of_lt_of_le zero_lt_one hG1
  have hprodS : ∏ _g : S, Schur.groupConst P.vMinus P.q (P.ℓ + m) ≤
      Real.log x ^ (Real.log (Schur.groupConst P.vMinus P.q (P.ℓ + m)) * P.C₀) :=
    𝔊.prod_small_le_rpow hx (fun _ => Schur.groupConst P.vMinus P.q (P.ℓ + m))
      (Real.log (Schur.groupConst P.vMinus P.q (P.ℓ + m))) (Real.log_nonneg hG1)
      (fun _ => hGpos.le) (fun _ => (Real.exp_log hGpos).ge)
  have hprodB : ∏ _g : B, Schur.groupConst P.vMinus P.q (P.ℓ + m) ≤
      Real.log x ^ (Real.log (Schur.groupConst P.vMinus P.q (P.ℓ + m)) * P.C₀) :=
    𝔊.prod_big_le_rpow hx (fun _ => Schur.groupConst P.vMinus P.q (P.ℓ + m))
      (Real.log (Schur.groupConst P.vMinus P.q (P.ℓ + m))) (Real.log_nonneg hG1)
      (fun _ => hGpos.le) (fun _ => (Real.exp_log hGpos).ge)
  have hbound : patternMass 𝔉 *
        ((∏ _g : S, Schur.groupConst P.vMinus P.q (P.ℓ + m)) *
          ∏ _g : B, Schur.groupConst P.vMinus P.q (P.ℓ + m)) ≤
      Real.log x ^ schurExponent P m C₁ := by
    unfold schurExponent
    rw [Real.rpow_add hx, Real.rpow_add hx]
    exact mul_le_mul hadm.2.1
      (mul_le_mul hprodS hprodB (Finset.prod_nonneg fun _ _ => hGpos.le)
        (Real.rpow_nonneg hx.le _))
      (mul_nonneg (Finset.prod_nonneg fun _ _ => hGpos.le)
        (Finset.prod_nonneg fun _ _ => hGpos.le))
      (Real.rpow_nonneg hx.le _)
  constructor
  · exact Schur.physAbsRowSum_le 𝔭 𝔊.toGroupFamily P.q 𝔉 k ζ _
      (fun t => (Schur.rowAbsMass_le 𝔭 𝔊.toGroupFamily P.q_pos P.q_lt_one P.vMinus_pos
        𝔊.mass_small_ge 𝔊.mass_big_ge 𝔊.big_law_sum hT hℓT 𝔉 hC k ζ t).trans hbound) s
  · exact Schur.physAbsColSum_le 𝔭 𝔊.toGroupFamily P.q 𝔉 k ζ _
      (fun t => (Schur.colAbsMass_le 𝔭 𝔊.toGroupFamily P.q_pos P.q_lt_one P.vMinus_pos
        𝔊.mass_small_ge 𝔊.mass_big_ge 𝔊.big_law_sum hT hℓT 𝔉 hC k ζ t).trans hbound) s

/-- Lemma 3.4 for integer positions, with the exponent `schurExponent P m C₁` and the threshold
`x₀ = 2`. -/
theorem intSchurBound (P : GroupParams) (m : ℕ) (C₁ : ℝ) (J : ℕ) (C₂ : ℝ) :
    IntSchurBound P m C₁ (schurExponent P m C₁) J C₂ := by
  refine ⟨2, ?_⟩
  intro x hx S B _ _ _ _ 𝔊 N _ 𝔉 ζ k hadm s
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  exact schur_bound P m C₁ hlog 𝔊 intPos 𝔉 ζ k hadm s

/-- Lemma 3.4 for residue positions, with the same exponent and threshold. -/
theorem residueSchurBound (P : GroupParams) (m : ℕ) (C₁ : ℝ) (J : ℕ) (C₂ : ℝ) :
    ResidueSchurBound P m C₁ (schurExponent P m C₁) J C₂ := by
  refine ⟨2, ?_⟩
  intro x hx S B _ _ _ _ 𝔊 N _ 𝔉 ζ k hadm s
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  exact schur_bound P m C₁ hlog 𝔊 (residuePos 𝔊.toGroupFamily) 𝔉 ζ k hadm s

/-- **[S] Lemma 3.4 (absolute physical bounds)** [S-02:0132–0158]: with
`C_abs = schurExponent P m C₁`, chosen after `(P, m, C₁)` and before `J` and `C₂`. -/
theorem physicalSchur : PhysicalSchur := fun P m C₁ =>
  ⟨schurExponent P m C₁, fun J C₂ =>
    ⟨intSchurBound P m C₁ J C₂, residueSchurBound P m C₁ J C₂⟩⟩

end

end SimultaneousPrimitiveRoots.Unconditional.Transference
