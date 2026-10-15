module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Bridge
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Scalars
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The assembly of [S] Theorem 3.5

Source: `verification/stage7-sources/S-02.tex`, lines 1020–1258 (`[S-02:1020–1258]`).

`localTransference_of` proves `LocalTransference` (Theorem 3.5, `Transference/Statements.lean`)
from the intermediate statements of this directory. The proved links, in the order of the paper:

* `ghostOpWith_opBound`, `edgeOpWith_opBound` — the operator bounds "`‖G_i‖ ≤ L^{C_v}`"
  [S-02:0699] and "Lemma 3.8 bounds its new norm by `L^{C_a}`" [S-02:1192–1194], with multipliers
  of modulus at most one on the births, from the weighted row and column bounds by Schur's test
  (eq:weighted-schur).
* `edgeContraction_of` — (eq:whole-edge-contraction) `‖ℰ_i‖ ≤ L^{-G}` from Lemmas 3.9 and 3.10
  with (eq:transference-parameter-choice) and the choice of `J` [S-02:1021–1037].
* `sum_abs_blockMu_mul_le` — the sum over the collections `π`, grouped by rank, with
  (eq:rank-coefficient-count) [S-02:1095–1100].
* `distinct_core`, `distinctBirthBound_of` — the large- and small-rank sums with the threshold
  (eq:rank-threshold) [S-02:1157–1170, 1219–1240].
* `localTransference_of_distinct` — the completion [S-02:1242–1258]: memory identity, tail,
  baseline, return condition, residue replacement.
* `localTransference_of` — all links together.

## The constants

For `P` and `E > 0`: `C_v` (`GhostAbsolute`) and `C_s` (`CleanNorm`) depend on `P` only;
`G = E + 2 max(C_v, 0) + 9` and `E_id = G + max(C_s, 0) + 2`
(the paper takes `G > E + C_v + 3`, `E_id > G + C_s + 2`; any larger `G` serves). For `m, C₁`:
`C_a` (`MemoryAbsolute`) and `C_d` (`RareTransfer`), then `J₀` with
`(c₀/2) log C(J + ℓ, ℓ) ≥ C_d + G + 3` for `J ≥ J₀`. After `J` and `C₂`: `C_h, C` (`HighRank`),
`C'' = 2(2 max(C_h, 0) + E + 7)` and `r₀ = ⌈C'' N T / log P_*⌉` (eq:rank-threshold). So `E_id`
depends on `(P, E)` only, and `J₀` on `(P, E, m, C₁)`, as Theorem 3.5 requires.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

open Filter

noncomputable section

/-! ### Operator bounds from the weighted row and column bounds -/

theorem OpBound.mono {X : Type*} [Fintype X] {m : X → ℝ} {Sy : (X → ℂ) → Prop}
    {T : (X → ℂ) →ₗ[ℂ] (X → ℂ)} {C C' : ℝ} (h : OpBound m Sy T C) (hC : C ≤ C') :
    OpBound m Sy T C' :=
  fun F hF => (h F hF).trans (mul_le_mul_of_nonneg_right hC (wNorm_nonneg _ _))

section OpBounds

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N]

omit [Fintype N] in
/-- **`‖G_i‖ ≤ C` on `ℋ`, with a multiplier of modulus at most one on the births**
[S-02:0697–0702, 1198–1214], from the weighted row and column bounds of the absolute visit
operation by Schur's test (eq:weighted-schur). -/
theorem ghostOpWith_opBound (D : MemData 𝒢 J ℓ N) (Bc : ℕ) {v C : ℝ} (hv : 0 < v) (hC : 0 ≤ C)
    (hm : ∀ s : MState 𝒢 J ℓ Bc, 0 ≤ memWeight 𝒢 D.q D.n s) (h : GhostRowCol D Bc v C)
    {i : ℕ} (hi : i ≤ D.n) (φ : ((g : B) → Batch 𝒢 Bc g) → ℂ) (hφ : ∀ b, ‖φ b‖ ≤ 1) :
    OpBound (memWeight 𝒢 D.q D.n) (fun F => MemSymmetric F) (ghostOpWith D Bc φ i) C := by
  have hκ : ∀ (s : MState 𝒢 J ℓ Bc) (c : GhostChoice 𝒢 Bc),
      ‖φ (ghostBirths c) * ((ghostCoef D i s c : ℝ) : ℂ)‖ ≤
        (2 : ℝ) ^ ghostBirthCount c * |ghostCoef D i s c| := by
    intro s c
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc ‖φ (ghostBirths c)‖ * |ghostCoef D i s c| ≤ 1 * |ghostCoef D i s c| :=
          mul_le_mul_of_nonneg_right (hφ _) (abs_nonneg _)
      _ ≤ (2 : ℝ) ^ ghostBirthCount c * |ghostCoef D i s c| :=
          mul_le_mul_of_nonneg_right (one_le_pow₀ (by norm_num)) (abs_nonneg _)
  have hb := opBound_of_row_col (memWeight 𝒢 D.q D.n) (schurWeight v) hm
    (fun s => schurWeight_pos hv s) (fun F => MemSymmetric F) (fun f => MemSymmetric f)
    (fun F hF => MemSymmetric.normSq_div hF v)
    (fun s c => φ (ghostBirths c) * ((ghostCoef D i s c : ℝ) : ℂ)) ghostTgt
    (fun s c => (2 : ℝ) ^ ghostBirthCount c * |ghostCoef D i s c|) hκ C C hC hC
    (h i hi).1 (h i hi).2
  rw [Real.sqrt_mul_self hC] at hb
  exact hb

/-- **`‖ℰ_i‖ ≤ C` on `ℋ`, with a multiplier of modulus at most one on the fresh births**
[S-02:0762–0764, 1192–1194], from the weighted row and column bounds of the absolute edge
(Lemma 3.8) by Schur's test (eq:weighted-schur). -/
theorem edgeOpWith_opBound (D : MemData 𝒢 J ℓ N) (Bc : ℕ) {v C : ℝ} (hv : 0 < v) (hC : 0 ≤ C)
    (hm : ∀ s : MState 𝒢 J ℓ Bc, 0 ≤ memWeight 𝒢 D.q D.n s) (h : EdgeRowCol D Bc v C)
    (θ : ℝ) {i : ℕ} (hi : i < D.n) (ψ : ((g : B) → Slot J ℓ → Option ℕ) → ℂ)
    (hψ : ∀ b, ‖ψ b‖ ≤ 1) :
    OpBound (memWeight 𝒢 D.q D.n) (fun F => MemSymmetric F) (edgeOpWith D Bc ψ θ i) C := by
  have hκ : ∀ (s : MState 𝒢 J ℓ Bc) (ξ : EdgeFullChoice D Bc),
      ‖edgeFullCoef D ψ θ i s ξ‖ ≤ ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ := by
    intro s ξ
    have e : edgeFullCoef D ψ θ i s ξ =
        ψ (edgeBirths ξ.2.1) * edgeFullCoef D (fun _ => 1) θ i s ξ := by
      simp only [edgeFullCoef]
      ring
    rw [e, norm_mul]
    calc ‖ψ (edgeBirths ξ.2.1)‖ * ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖
        ≤ 1 * ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ :=
          mul_le_mul_of_nonneg_right (hψ _) (norm_nonneg _)
      _ = ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ := one_mul _
  have hb := opBound_of_row_col (memWeight 𝒢 D.q D.n) (schurWeight v) hm
    (fun s => schurWeight_pos hv s) (fun F => MemSymmetric F) (fun f => MemSymmetric f)
    (fun F hF => MemSymmetric.normSq_div hF v)
    (edgeFullCoef D ψ θ i) (edgeFullTgt D i)
    (fun s ξ => ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖) hκ C C hC hC
    (h θ i hi).1 (h θ i hi).2
  rw [Real.sqrt_mul_self hC] at hb
  exact hb

end OpBounds

/-! ### The whole edge (eq:whole-edge-contraction) -/

theorem memCutoff_le {L : ℝ} (hL : 4 ≤ L) : (memCutoff L : ℝ) ≤ 2 * L ^ 2 := by
  have h1 : (memCutoff L : ℝ) < L ^ 2 + 1 := Nat.ceil_lt_add_one (sq_nonneg L)
  nlinarith

/-- **(eq:whole-edge-contraction)** [S-02:1021–1037]: "Choose, in this order, `G > E + C_v + 3`,
`E_id > G + C_s + 2`, and finally choose the fixed integer `J` so large that (eq:dirty-J-gain) is
smaller than `½ L^{-G}` for large `x`. For example it suffices that
`(c₀/2) log C(J + ℓ, ℓ) > C_a + G + 3`. The clean estimate supplies the other half. Hence the
whole signed truncated edge, with birth distinctness still omitted, satisfies `‖ℰ_i‖ ≤ L^{-G}`."

From the conclusions of Lemma 3.10 (constant `C_s`, exponent `E_id ≥ G + C_s + 2`) and of
Lemma 3.9 (constant `C_d`, with `(c₀/2) log C(J + ℓ, ℓ) ≥ C_d + G + 3`). -/
theorem edgeContraction_of {P : GroupParams} {G Cs Cd Eid : ℝ} {m : ℕ} {C₁ : ℝ} {J : ℕ}
    {C₂ : ℝ} (hclean : CleanNormBound P Cs Eid m C₁ J C₂)
    (hdirty : RareTransferBound P m C₁ Cd J C₂) (hEid : G + Cs + 2 ≤ Eid)
    (hJ : Cd + G + 3 ≤ P.c₀ / 2 * Real.log (((J + P.ℓ).choose P.ℓ : ℕ) : ℝ)) :
    EdgeContractionBound P G Eid m C₁ J C₂ := by
  obtain ⟨x₁, h₁⟩ := hclean
  obtain ⟨x₂, h₂⟩ := hdirty
  obtain ⟨x₃, h₃⟩ := eventually_atTop.mp
    ((eventually_log_ge 4).and (eventually_memMeasure_nonneg P))
  refine ⟨max (max x₁ x₂) x₃,
    fun x hx S B _ _ _ _ 𝔊 N _ 𝔉 ζ k hadm hideal θ i hi F hF => ?_⟩
  have hx₁ : x₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx₂ : x₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  obtain ⟨hL, hmeas⟩ := h₃ x (le_trans (le_max_right _ _) hx)
  have hc := h₁ x hx₁ S B 𝔊 N 𝔉 ζ k hadm hideal θ i hi F hF
  have hd := h₂ x hx₂ S B 𝔊 N 𝔉 ζ k hadm θ i hi F hF
  have hnn : ∀ s, 0 ≤ memMeasure 𝔊 J (memCutoff (Real.log x)) s := hmeas S B 𝔊 J _
  have hw := wNorm_nonneg (memMeasure 𝔊 J (memCutoff (Real.log x))) F
  have hc' : 2 * Real.log x ^ (-Eid + Cs) ≤ 1 / 2 * Real.log x ^ (-G) := clean_half hL hEid
  have hd' : 2 * Real.log x ^ Cd *
      Real.sqrt ((memCutoff (Real.log x) : ℝ) / (omissionNumber S J P.ℓ : ℝ)) ≤
      1 / 2 * Real.log x ^ (-G) :=
    dirty_half hL (memCutoff_le hL) (Nat.choose_pos (Nat.le_add_left _ _)) 𝔊.card_small_ge hJ
  have e : edgeOp (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) θ i F =
      edgeClean (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) θ i F +
        edgeDirty (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) θ i F := by
    rw [edgeOp_eq_clean_add_dirty]
    rfl
  rw [e]
  calc wNorm (memMeasure 𝔊 J (memCutoff (Real.log x)))
        (edgeClean (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) θ i F +
          edgeDirty (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) θ i F)
      ≤ wNorm (memMeasure 𝔊 J (memCutoff (Real.log x)))
            (edgeClean (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) θ i F) +
          wNorm (memMeasure 𝔊 J (memCutoff (Real.log x)))
            (edgeDirty (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) θ i F) :=
        wNorm_add_le hnn _ _
    _ ≤ 2 * Real.log x ^ (-Eid + Cs) * wNorm (memMeasure 𝔊 J (memCutoff (Real.log x))) F +
          2 * Real.log x ^ Cd *
            Real.sqrt ((memCutoff (Real.log x) : ℝ) / (omissionNumber S J P.ℓ : ℝ)) *
            wNorm (memMeasure 𝔊 J (memCutoff (Real.log x))) F := add_le_add hc hd
    _ ≤ 1 / 2 * Real.log x ^ (-G) * wNorm (memMeasure 𝔊 J (memCutoff (Real.log x))) F +
          1 / 2 * Real.log x ^ (-G) * wNorm (memMeasure 𝔊 J (memCutoff (Real.log x))) F :=
        add_le_add (mul_le_mul_of_nonneg_right hc' hw) (mul_le_mul_of_nonneg_right hd' hw)
    _ = Real.log x ^ (-G) * wNorm (memMeasure 𝔊 J (memCutoff (Real.log x))) F := by ring

/-! ### The sum over the collections of blocks -/

open _root_.Classical in
/-- **The sum over the collections `π`, grouped by rank, with (eq:rank-coefficient-count)**
[S-02:1095–1100, 1162–1167, 1230–1233]: if `f(π) ≤ V(r(π))` for every collection and
`A_*^{2r} V(r) ≤ W` for every rank `r ≤ A_*`, then `∑_π |μ(π)| f(π) ≤ (A_* + 1) W`. -/
theorem sum_abs_blockMu_mul_le (hcount : RankCoefficientCount) (I : Type) [Fintype I]
    [DecidableEq I] (f : Finset (Finset I) → ℝ) (V : ℕ → ℝ) (W : ℝ) (hV : ∀ r, 0 ≤ V r)
    (hf : ∀ π ∈ blockCollections I, f π ≤ V (blockRank π))
    (hW : ∀ r, r ≤ Fintype.card I → (Fintype.card I : ℝ) ^ (2 * r) * V r ≤ W) :
    ∑ π ∈ blockCollections I, |((blockMu π : ℤ) : ℝ)| * f π ≤
      ((Fintype.card I : ℝ) + 1) * W := by
  have h1 : ∑ π ∈ blockCollections I, |((blockMu π : ℤ) : ℝ)| * f π ≤
      ∑ π ∈ blockCollections I, |((blockMu π : ℤ) : ℝ)| * V (blockRank π) :=
    Finset.sum_le_sum fun π hπ => mul_le_mul_of_nonneg_left (hf π hπ) (abs_nonneg _)
  have h2 : ∑ π ∈ blockCollections I, |((blockMu π : ℤ) : ℝ)| * V (blockRank π) =
      ∑ r ∈ Finset.range (Fintype.card I + 1),
        ∑ π ∈ (blockCollections I).filter (fun π => blockRank π = r),
          |((blockMu π : ℤ) : ℝ)| * V (blockRank π) :=
    (Finset.sum_fiberwise_of_maps_to
      (fun π hπ => Finset.mem_range.mpr (Nat.lt_succ_of_le (blockRank_le_card hπ))) _).symm
  have h3 : ∀ r ∈ Finset.range (Fintype.card I + 1),
      ∑ π ∈ (blockCollections I).filter (fun π => blockRank π = r),
        |((blockMu π : ℤ) : ℝ)| * V (blockRank π) ≤ W := by
    intro r hr
    have hr' : r ≤ Fintype.card I := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have e : ∑ π ∈ (blockCollections I).filter (fun π => blockRank π = r),
        |((blockMu π : ℤ) : ℝ)| * V (blockRank π) =
        (∑ π ∈ (blockCollections I).filter (fun π => blockRank π = r),
          |((blockMu π : ℤ) : ℝ)|) * V r := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun π hπ => ?_
      rw [(Finset.mem_filter.mp hπ).2]
    have hc' : (∑ π ∈ (blockCollections I).filter (fun π => blockRank π = r),
        |((blockMu π : ℤ) : ℝ)|) ≤ (Fintype.card I : ℝ) ^ (2 * r) := by
      have hc := (Int.cast_le (R := ℝ)).mpr (hcount I r)
      push_cast at hc
      exact hc
    rw [e]
    exact (mul_le_mul_of_nonneg_right hc' (hV r)).trans (hW r hr')
  calc ∑ π ∈ blockCollections I, |((blockMu π : ℤ) : ℝ)| * f π
      ≤ ∑ r ∈ Finset.range (Fintype.card I + 1),
          ∑ π ∈ (blockCollections I).filter (fun π => blockRank π = r),
            |((blockMu π : ℤ) : ℝ)| * V (blockRank π) := h1.trans (le_of_eq h2)
    _ ≤ ∑ _r ∈ Finset.range (Fintype.card I + 1), W := Finset.sum_le_sum h3
    _ = ((Fintype.card I : ℝ) + 1) * W := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        push_cast
        ring

/-! ### Restoring distinct births -/

/-- "For all sufficiently large `x`": the scalar conditions of the rank argument. -/
theorem eventually_rank_scalars (P : GroupParams) (C'' κ' Cp : ℝ) (hC'' : 0 < C'')
    (hκ' : 0 < κ') (hCp : 0 < Cp) :
    ∀ᶠ x : ℝ in atTop,
      4 ≤ Real.log x ∧ (1 : ℝ) ≤ (Graph.sourceMemoryLength (Real.log x) : ℝ) ∧
        C'' * κ' * Real.log (Real.log x) ≤ Real.log x ^ P.c ∧
        Real.log x ^ (6 : ℝ) * Cp ≤ Real.exp (Real.log x ^ P.c / 2) := by
  have hc := P.c_pos
  have hpos : 0 < C'' * κ' := mul_pos hC'' hκ'
  filter_upwards [eventually_log_ge 4, eventually_memLength_ge 1,
    eventually_loglog_le P.c (1 / (C'' * κ')) hc (one_div_pos.mpr hpos),
    eventually_loglog_le P.c (1 / 24) hc (by norm_num),
    eventually_rpow_ge P.c (4 * Real.log Cp) hc] with x h1 h2 h3 h4 h5
  refine ⟨h1, h2, ?_, ?_⟩
  · calc C'' * κ' * Real.log (Real.log x)
        ≤ C'' * κ' * (1 / (C'' * κ') * Real.log x ^ P.c) :=
          mul_le_mul_of_nonneg_left h3 hpos.le
      _ = Real.log x ^ P.c := by
          field_simp
  · have hL0 : 0 < Real.log x := by linarith
    have e : Real.log x ^ (6 : ℝ) * Cp =
        Real.exp (Real.log (Real.log x) * 6 + Real.log Cp) := by
      rw [Real.exp_add, Real.exp_log hCp, ← Real.rpow_def_of_pos hL0]
    rw [e]
    refine Real.exp_le_exp.mpr ?_
    linarith

section Core

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N]

open _root_.Classical in
/-- **The large- and small-rank estimates together** [S-02:1157–1170, 1219–1245], for one value
of `x`: an exact statement about the path integral with the distinct-birth rule, for constants
which satisfy the scalar conditions of the paper. The collections of rank `r < r₀` are estimated
by `LowRankStep`, the collections of rank `r ≥ r₀` by the large-rank bound `hhigh`,
`r₀ = ⌈C'' N T / log P_*⌉` (eq:rank-threshold); the number of collections of each rank is
(eq:rank-coefficient-count). -/
theorem distinct_core (hI : DistinctIndicatorExpansion) (hK : RankCoefficientCount)
    (hLow : LowRankStep) (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ)
    {L E Cv Ca G Ch Cp c C'' κ : ℝ} (hL : 2 ≤ L) (hn : 1 ≤ D.n) (hE : 0 ≤ E) (hCv : 0 ≤ Cv)
    (hCa : 0 ≤ Ca) (hG : G = E + 2 * Cv + 9) (hC'' : C'' = 2 * (2 * max Ch 0 + E + 7))
    (hκ : κ = 6 + 2 * G + 2 * Ca) (hCp : 0 < Cp)
    (hA : (Fintype.card (BirthAddr B J ℓ Bc D.n) : ℝ) ≤ L ^ (3 : ℝ))
    (hT : C'' * (κ + 1) * Real.log L ≤ L ^ c)
    (hϱ : L ^ (6 : ℝ) * Cp ≤ Real.exp (L ^ c / 2))
    (hm : ∀ s : MState 𝒢 J ℓ Bc, 0 ≤ memWeight 𝒢 D.q D.n s)
    (hghost : ∀ i : ℕ, i ≤ D.n → ∀ φ : ((g : B) → Batch 𝒢 Bc g) → ℂ, (∀ b, ‖φ b‖ ≤ 1) →
      OpBound (memWeight 𝒢 D.q D.n) (fun F => MemSymmetric F) (ghostOpWith D Bc φ i) (L ^ Cv))
    (hedge : ∀ i : ℕ, i < D.n → ∀ ψ : ((g : B) → Slot J ℓ → Option ℕ) → ℂ,
      (∀ b, ‖ψ b‖ ≤ 1) →
      OpBound (memWeight 𝒢 D.q D.n) (fun F => MemSymmetric F) (edgeOpWith D Bc ψ θ i) (L ^ Ca))
    (hwhole : ∀ i : ℕ, i < D.n →
      OpBound (memWeight 𝒢 D.q D.n) (fun F => MemSymmetric F) (edgeOp D Bc θ i) (L ^ (-G)))
    (hbd : wNormSq (memWeight 𝒢 D.q D.n) (emptyVec 𝒢 J ℓ Bc) ≤ 2)
    (hhigh : ∀ π ∈ blockCollections (BirthAddr B J ℓ Bc D.n),
      absRankPart D Bc θ π ≤
        L ^ (Ch * ((D.n : ℝ) + 1)) * (Cp / Real.exp (L ^ c)) ^ blockRank π) :
    ‖distinctSum D Bc θ‖ ≤ 1 / 2 * L ^ (-(E * (D.n : ℝ))) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hLc : 0 < L ^ c := Real.rpow_pos_of_pos hL0 c
  have hG0 : 0 ≤ G := by rw [hG]; linarith
  have hκ0 : 0 ≤ κ := by rw [hκ]; linarith
  -- the rank threshold (eq:rank-threshold)
  obtain ⟨r₀, hr₀def⟩ : ∃ r₀ : ℕ, r₀ = Nat.ceil (C'' * (D.n : ℝ) * Real.log L / L ^ c) :=
    ⟨_, rfl⟩
  have hr₀ : C'' * (D.n : ℝ) * Real.log L ≤ L ^ c * (r₀ : ℝ) := by
    have h1 : C'' * (D.n : ℝ) * Real.log L / L ^ c ≤ (r₀ : ℝ) := by
      rw [hr₀def]
      exact Nat.le_ceil _
    have h2 := (div_le_iff₀ hLc).mp h1
    linarith
  -- small rank
  have hlow := hLow S B 𝒢 J ℓ N D Bc θ (L ^ Cv) (L ^ Ca) (L ^ (-G)) 2
    (Real.rpow_nonneg hL0.le _) (Real.rpow_nonneg hL0.le _)
    (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) hm hghost hedge hwhole hbd
  -- the bound as a function of the rank
  obtain ⟨V, hVdef⟩ : ∃ V : ℕ → ℝ, V = fun r => if r < r₀ then
      2 * (L ^ Cv) ^ (D.n + 1) * (L ^ (-G)) ^ (D.n - min D.n (2 * r)) *
        (L ^ Ca) ^ min D.n (2 * r)
    else L ^ (Ch * ((D.n : ℝ) + 1)) * (Cp / Real.exp (L ^ c)) ^ r := ⟨_, rfl⟩
  have hV : ∀ r, 0 ≤ V r := by
    intro r
    rw [hVdef]
    show 0 ≤ (if r < r₀ then _ else _)
    split_ifs
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
        (pow_nonneg (Real.rpow_nonneg hL0.le _) _)) (pow_nonneg (Real.rpow_nonneg hL0.le _) _))
        (pow_nonneg (Real.rpow_nonneg hL0.le _) _)
    · exact mul_nonneg (Real.rpow_nonneg hL0.le _)
        (pow_nonneg (div_nonneg hCp.le (Real.exp_pos _).le) _)
  have hf : ∀ π ∈ blockCollections (BirthAddr B J ℓ Bc D.n),
      ‖rankPart D Bc θ π‖ ≤ V (blockRank π) := by
    intro π hπ
    rw [hVdef]
    show _ ≤ (if blockRank π < r₀ then _ else _)
    split_ifs with hr
    · exact hlow π hπ
    · exact (norm_rankPart_le D Bc θ π).trans (hhigh π hπ)
  have hAn : (0 : ℝ) ≤ (Fintype.card (BirthAddr B J ℓ Bc D.n) : ℝ) := Nat.cast_nonneg _
  have hW : ∀ r, r ≤ Fintype.card (BirthAddr B J ℓ Bc D.n) →
      (Fintype.card (BirthAddr B J ℓ Bc D.n) : ℝ) ^ (2 * r) * V r ≤
        L ^ (-((E + 7) * (D.n : ℝ))) := by
    intro r _
    rw [hVdef]
    show _ * (if r < r₀ then _ else _) ≤ _
    split_ifs with hr
    · refine scalar_low hL hCv hCa hE hG hn hAn hA ?_
      have h1 : (r : ℝ) < C'' * (D.n : ℝ) * Real.log L / L ^ c := by
        rw [hr₀def] at hr
        exact Nat.lt_ceil.mp hr
      have h2 : (r : ℝ) * L ^ c < C'' * (D.n : ℝ) * Real.log L := (lt_div_iff₀ hLc).mp h1
      have hn0 : (0 : ℝ) ≤ (D.n : ℝ) := Nat.cast_nonneg _
      have hr0 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
      have h3 : (r : ℝ) * L ^ c * (κ + 1) ≤ C'' * (D.n : ℝ) * Real.log L * (κ + 1) :=
        mul_le_mul_of_nonneg_right h2.le (by linarith)
      have h4 : (D.n : ℝ) * (C'' * (κ + 1) * Real.log L) ≤ (D.n : ℝ) * L ^ c :=
        mul_le_mul_of_nonneg_left hT hn0
      have h5 : (r : ℝ) * (κ + 1) * L ^ c ≤ (D.n : ℝ) * L ^ c := by nlinarith
      have h6 : (r : ℝ) * (κ + 1) ≤ (D.n : ℝ) := le_of_mul_le_mul_right h5 hLc
      rw [← hκ]
      nlinarith
    · exact scalar_high hL hn hAn hA hCp hϱ hr₀ hC'' (not_lt.mp hr)
  have hsum := sum_abs_blockMu_mul_le hK (BirthAddr B J ℓ Bc D.n)
    (fun π => ‖rankPart D Bc θ π‖) V _ hV hf hW
  have hnorm : ‖distinctSum D Bc θ‖ ≤
      ∑ π ∈ blockCollections (BirthAddr B J ℓ Bc D.n),
        |((blockMu π : ℤ) : ℝ)| * ‖rankPart D Bc θ π‖ := by
    rw [distinctSum_eq_sum_rankPart hI D Bc θ]
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun π _ => ?_))
    rw [norm_mul, Complex.norm_intCast]
  exact (hnorm.trans hsum).trans (scalar_total hL hn hAn hA)

end Core

/-- **The expansion with distinct births is `o(L^{-EN})`** [S-02:1043–1245]: `DistinctBirthBound`
follows from the absolute bounds (`GhostAbsolute`, `MemoryAbsolute`, `BoundaryNorm`), the rare
transfer and clean norm lemmas (Lemmas 3.9, 3.10), the two combinatorial statements
(eq:distinct-indicator) and (eq:rank-coefficient-count), (eq:birth-address-count), and the large-
and small-rank estimates (`HighRank`, `LowRankStep`). The constants are chosen as in
(eq:transference-parameter-choice) and (eq:rank-threshold); see the file header. -/
theorem distinctBirthBound_of (hG : GhostAbsolute) (hE : MemoryAbsolute) (hB : BoundaryNorm)
    (hR : RareTransfer) (hC : CleanNorm) (hI : DistinctIndicatorExpansion)
    (hK : RankCoefficientCount) (hA : BirthAddressCount) (hH : HighRank) (hLow : LowRankStep) :
    DistinctBirthBound := by
  intro P E hEpos
  obtain ⟨Cv₀, hGv⟩ := hG P
  obtain ⟨Cs, hCs⟩ := hC P
  obtain ⟨Cv, hCv⟩ : ∃ Cv : ℝ, Cv = max Cv₀ 0 := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = E + 2 * Cv + 9 := ⟨_, rfl⟩
  obtain ⟨Eid, hEid⟩ : ∃ Eid : ℝ, Eid = G + max Cs 0 + 2 := ⟨_, rfl⟩
  have hCv0 : 0 ≤ Cv := by rw [hCv]; exact le_max_right _ _
  have hCvle : Cv₀ ≤ Cv := by rw [hCv]; exact le_max_left _ _
  have hG0 : 0 ≤ G := by rw [hGdef]; linarith
  have hEidpos : 0 < Eid := by
    have := le_max_right Cs 0
    rw [hEid]
    linarith
  have hEidge : G + Cs + 2 ≤ Eid := by
    have := le_max_left Cs 0
    rw [hEid]
    linarith
  refine ⟨Eid, hEidpos, fun m C₁ => ?_⟩
  obtain ⟨Ca₀, hEa⟩ := hE P m C₁
  obtain ⟨Cd, hRd⟩ := hR P m C₁
  obtain ⟨Ca, hCa⟩ : ∃ Ca : ℝ, Ca = max Ca₀ 0 := ⟨_, rfl⟩
  have hCa0 : 0 ≤ Ca := by rw [hCa]; exact le_max_right _ _
  have hCale : Ca₀ ≤ Ca := by rw [hCa]; exact le_max_left _ _
  obtain ⟨J₀, hJ₀⟩ := exists_slot_threshold P.c₀ (Cd + G + 3) P.c₀_pos P.ℓ P.ℓ_pos
  refine ⟨J₀, fun J hJ C₂ => ?_⟩
  obtain ⟨Ch, Cp, hCp, hHigh⟩ := hH P m C₁ J C₂
  obtain ⟨C'', hC''⟩ : ∃ C'' : ℝ, C'' = 2 * (2 * max Ch 0 + E + 7) := ⟨_, rfl⟩
  have hC''pos : 0 < C'' := by
    have := le_max_right Ch 0
    rw [hC'']
    linarith
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = 6 + 2 * G + 2 * Ca := ⟨_, rfl⟩
  have hκ0 : 0 ≤ κ := by rw [hκ]; linarith
  obtain ⟨x₁, h₁⟩ := hGv J
  obtain ⟨x₂, h₂⟩ := hEa J C₂
  obtain ⟨x₃, h₃⟩ := hB P J
  obtain ⟨x₄, h₄⟩ := edgeContraction_of (hCs Eid m C₁ J C₂) (hRd J C₂) hEidge (hJ₀ J hJ)
  obtain ⟨x₅, h₅⟩ := hA P J
  obtain ⟨x₆, h₆⟩ := hHigh
  obtain ⟨x₇, h₇⟩ := eventually_atTop.mp
    ((eventually_rank_scalars P C'' (κ + 1) Cp hC''pos (by linarith) hCp).and
      (eventually_memMeasure_nonneg P))
  refine ⟨max (max (max x₁ x₂) (max x₃ x₄)) (max (max x₅ x₆) x₇),
    fun x hx S B _ _ _ _ 𝔊 N _ 𝔉 ζ k hadm hideal θ => ?_⟩
  have hx1 : x₁ ≤ x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hx2 : x₂ ≤ x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hx3 : x₃ ≤ x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have hx4 : x₄ ≤ x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have hx5 : x₅ ≤ x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have hx6 : x₆ ≤ x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have hx7 : x₇ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨⟨hL4, hn1, hT, hϱ⟩, hmeas⟩ := h₇ x hx7
  have hL0 : 0 < Real.log x := by linarith
  have hL1 : 1 ≤ Real.log x := by linarith
  have hv : 0 < memV P := lt_trans zero_lt_one (one_lt_memV P)
  have hm : ∀ s : MState 𝔊.toGroupFamily J P.ℓ (memCutoff (Real.log x)),
      0 ≤ memWeight 𝔊.toGroupFamily (memData 𝔊 𝔉 k ζ).q (memData 𝔊 𝔉 k ζ).n s :=
    hmeas S B 𝔊 J (memCutoff (Real.log x))
  have hn : 1 ≤ (memData 𝔊 𝔉 k ζ).n := by
    show 1 ≤ Graph.sourceMemoryLength (Real.log x)
    exact_mod_cast hn1
  have hghost : ∀ i : ℕ, i ≤ (memData 𝔊 𝔉 k ζ).n →
      ∀ φ : ((g : B) → Batch 𝔊.toGroupFamily (memCutoff (Real.log x)) g) → ℂ,
      (∀ b, ‖φ b‖ ≤ 1) →
      OpBound (memWeight 𝔊.toGroupFamily (memData 𝔊 𝔉 k ζ).q (memData 𝔊 𝔉 k ζ).n)
        (fun F => MemSymmetric F)
        (ghostOpWith (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) φ i) (Real.log x ^ Cv) :=
    fun i hi φ hφ =>
      (ghostOpWith_opBound (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) hv
        (Real.rpow_nonneg hL0.le _) hm (h₁ x hx1 S B 𝔊 N 𝔉 ζ k (memCutoff (Real.log x)))
        hi φ hφ).mono (Real.rpow_le_rpow_of_exponent_le hL1 hCvle)
  have hedge : ∀ i : ℕ, i < (memData 𝔊 𝔉 k ζ).n →
      ∀ ψ : ((g : B) → Slot J P.ℓ → Option ℕ) → ℂ, (∀ b, ‖ψ b‖ ≤ 1) →
      OpBound (memWeight 𝔊.toGroupFamily (memData 𝔊 𝔉 k ζ).q (memData 𝔊 𝔉 k ζ).n)
        (fun F => MemSymmetric F)
        (edgeOpWith (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) ψ θ i) (Real.log x ^ Ca) :=
    fun i hi ψ hψ =>
      (edgeOpWith_opBound (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) hv
        (Real.rpow_nonneg hL0.le _) hm
        (h₂ x hx2 S B 𝔊 N 𝔉 ζ k hadm (memCutoff (Real.log x))) θ hi ψ hψ).mono
        (Real.rpow_le_rpow_of_exponent_le hL1 hCale)
  exact distinct_core hI hK hLow (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) θ
    (by linarith) hn hEpos.le hCv0 hCa0 hGdef hC'' hκ hCp (h₅ x hx5 S B 𝔊) hT hϱ hm hghost hedge
    (fun i hi => h₄ x hx4 S B 𝔊 N 𝔉 ζ k hadm hideal θ i hi) (h₃ x hx3 S B 𝔊 _)
    (h₆ x hx6 S B 𝔊 N 𝔉 ζ k hadm θ)

/-! ### The completion of the proof -/

/-- **Completion of Theorem 3.5** [S-02:1242–1258]: "Apply (eq:distinct-indicator) in the
truncated memory identity. The large- and small-rank estimates bound it by `o(L^{-EN})`,
uniformly in `θ`. Restore the tail (eq:memory-tail); multiply by the baseline, which is at most
one; and integrate (eq:return-fourier). Finally restore the uniform residue-replacement error,
choosing its precision after the absolute path bound."

`LocalTransference` follows from the reduction to the residue model, the return condition, the
memory identity, the truncation estimate and the bound for the expansion with distinct births.
The exponent `E_id` and the bound `J₀` are those of `DistinctBirthBound`. -/
theorem localTransference_of_distinct (h₁ : ResidueReduction) (h₂ : ReturnFourier)
    (h₃ : MemoryIdentity) (h₄ : MemoryTail) (h₅ : DistinctBirthBound) : LocalTransference := by
  intro P E hE
  obtain ⟨Eid, hEid, h5⟩ := h₅ P E hE
  refine ⟨Eid, hEid, fun m C₁ => ?_⟩
  obtain ⟨J₀, h5'⟩ := h5 m C₁
  refine ⟨J₀, fun J hJ C₂ γ hγ => ?_⟩
  obtain ⟨x₁, hx₁⟩ := h₁ P m C₁ J C₂ γ (E + 1) hγ
  obtain ⟨x₂, hx₂⟩ := h₃ P m C₁ J C₂
  obtain ⟨x₃, hx₃⟩ := h₄ P m C₁ J C₂ (E + 1)
  obtain ⟨x₄, hx₄⟩ := h5' J hJ C₂
  obtain ⟨x₅, hx₅⟩ := eventually_atTop.mp
    ((eventually_log_ge 4).and ((eventually_memLength_ge 1).and (eventually_baselineProd P)))
  refine ⟨max (max (max x₁ x₂) (max x₃ x₄)) x₅,
    fun x hx S B _ _ _ _ 𝔊 N _ 𝔉 ζ k hadm hideal X hX₁ hX₂ => ?_⟩
  have hx1 : x₁ ≤ x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hx2 : x₂ ≤ x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hx
  have hx3 : x₃ ≤ x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  have hx4 : x₄ ≤ x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_left _ _)) hx
  obtain ⟨hL, hn1, hbase⟩ := hx₅ x (le_trans (le_max_right _ _) hx)
  obtain ⟨hb0, hb1⟩ := hbase S B 𝔊
  have hn : 1 ≤ Graph.sourceMemoryLength (Real.log x) := by exact_mod_cast hn1
  have hcrt := hx₁ x hx1 S B 𝔊 N 𝔉 ζ k hadm X hX₁ hX₂
  -- the unrestricted signed path expression, uniformly in `θ`
  have hphase : ∀ θ : ℝ,
      ‖phaseSum 𝔊.toGroupFamily P.q 𝔉 k ζ (transferR (Real.log x)) θ‖ ≤
        1 / 2 * Real.log x ^ (-(E * (Graph.sourceMemoryLength (Real.log x) : ℝ))) +
          Real.log x ^ (-((E + 1) * (Graph.sourceMemoryLength (Real.log x) : ℝ))) := by
    intro θ
    have hid := hx₂ x hx2 S B 𝔊 N 𝔉 ζ k hadm θ
      (max (bigPrimes 𝔊.toGroupFamily).card (memCutoff (Real.log x))) (le_max_left _ _)
    have htail := hx₃ x hx3 S B 𝔊 N 𝔉 ζ k hadm θ
      (max (bigPrimes 𝔊.toGroupFamily).card (memCutoff (Real.log x))) (le_max_right _ _)
    have hdist := hx₄ x hx4 S B 𝔊 N 𝔉 ζ k hadm hideal θ
    have e : distinctSum (memData 𝔊 𝔉 k ζ)
          (max (bigPrimes 𝔊.toGroupFamily).card (memCutoff (Real.log x))) θ =
        distinctSum (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) θ +
          (distinctSum (memData 𝔊 𝔉 k ζ)
              (max (bigPrimes 𝔊.toGroupFamily).card (memCutoff (Real.log x))) θ -
            distinctSum (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) θ) := by
      ring
    have htri : ‖distinctSum (memData 𝔊 𝔉 k ζ)
          (max (bigPrimes 𝔊.toGroupFamily).card (memCutoff (Real.log x))) θ‖ ≤
        ‖distinctSum (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) θ‖ +
          ‖distinctSum (memData 𝔊 𝔉 k ζ)
              (max (bigPrimes 𝔊.toGroupFamily).card (memCutoff (Real.log x))) θ -
            distinctSum (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) θ‖ :=
      (le_of_eq (congrArg (fun z : ℂ => ‖z‖) e)).trans (norm_add_le _ _)
    rw [hid, norm_mul, Complex.norm_real, Real.norm_of_nonneg hb0]
    have hmul := mul_le_mul_of_nonneg_right hb1 (norm_nonneg (distinctSum (memData 𝔊 𝔉 k ζ)
      (max (bigPrimes 𝔊.toGroupFamily).card (memCutoff (Real.log x))) θ))
    linarith
  have hres := h₂ S B 𝔊.toGroupFamily P.q J P.ℓ N 𝔉 k ζ (transferR (Real.log x)) _ hphase
  have hres' := (le_abs_self _).trans hres
  have hcrt' := (abs_le.mp hcrt).2
  have hfin := moment_scalar (L := Real.log x) (E := E) hL hn
  linarith

/-- **[S] Theorem 3.5 from the intermediate statements** [S-02:0188–1258].

The hypotheses are, in the order of the paper: Lemma 3.6 and the summation over paths
(§ "Replacing the root by independent residues"), the return condition (eq:return-fourier),
Lemma 3.7, the absolute bounds (eq:ghost-absolute-bound) and Lemma 3.8, the norm of the boundary
vector, the truncation estimate (eq:memory-tail), Lemmas 3.9 and 3.10, the identity
(eq:distinct-indicator), the counts (eq:rank-coefficient-count) and (eq:birth-address-count), and
the large- and small-rank estimates. Lemma 3.4 is used inside `ResidueSummation` and is proved
(`schur_bound`). -/
theorem localTransference_of (h1 : UniformResidueReplacement) (h2 : ResidueSummation)
    (h3 : ReturnFourier) (h4 : MemoryIdentity) (h5 : GhostAbsolute) (h6 : MemoryAbsolute)
    (h7 : BoundaryNorm) (h8 : MemoryTail) (h9 : RareTransfer) (h10 : CleanNorm)
    (h11 : DistinctIndicatorExpansion) (h12 : RankCoefficientCount) (h13 : BirthAddressCount)
    (h14 : HighRank) (h15 : LowRankStep) : LocalTransference :=
  localTransference_of_distinct (h2 h1) h3 h4 h8
    (distinctBirthBound_of h5 h6 h7 h9 h10 h11 h12 h13 h14 h15)

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
