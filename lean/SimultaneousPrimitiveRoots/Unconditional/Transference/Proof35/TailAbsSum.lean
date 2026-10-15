module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.MemoryAbsoluteProof
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.HistoryExpansionProof
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The absolute path sum with doubled ghost births

Source: `verification/stage7-sources/S-02.tex`, lines 803–811 (`[S-02:0803–0811]`), the estimate
behind (eq:memory-tail):

"Multiply every ghost birth by two in the absolute path sum and use the preceding bounds."

`tail_absSum_le`: for every cutoff, if the absolute visit operations with doubled births have the
weighted row bound `R_g` and the absolute edges the weighted row bound `R_e` (for the Schur weight
`w = v^{j_tot}`, `v ≥ 1`), then

`∑_h 2^{#ghost births of h} · |weight(h)| ≤ ‖𝟏_∅‖² · R_g^{N+1} · R_e^N`,

the sum being over all histories (the terms of the expanded path integral). Only the row bounds
are used: the walk starts at an empty memory, where `w = 1`, and `𝟏_∅ ≤ w` at its end.

* `rCoef`, `rCoef_ofFn`, `rWalk_sum_le` — walks with real nonnegative coefficients: the sum over
  all words of the product of the coefficients along the walk, times a terminal function, is at
  most a potential `V` which satisfies the row inequality `K V ≤ V` along the walk.
* `History.ghostBirthTotal`, `tailK`, `tailLast`, `History.absWeight_eq` — the modulus of the
  weight of a history, with every ghost birth doubled, as the term of its word.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### Walks with real coefficients -/

section Walks

variable {Y Ξ : Type*}

/-- The product of the real coefficients `κ` along the walk which starts at `y` and makes the
choices of the word `l` in turn (`walkCoef` for real coefficients). -/
def rCoef (κ : Y → Ξ → ℝ) (tgt : Y → Ξ → Y) (y : Y) (l : List Ξ) : ℝ :=
  (walkCoef (fun y ξ => ((κ y ξ : ℝ) : ℂ)) tgt y l).re

theorem rCoef_nil (κ : Y → Ξ → ℝ) (tgt : Y → Ξ → Y) (y : Y) : rCoef κ tgt y [] = 1 :=
  Complex.one_re

theorem rCoef_cons (κ : Y → Ξ → ℝ) (tgt : Y → Ξ → Y) (y : Y) (ξ : Ξ) (l : List Ξ) :
    rCoef κ tgt y (ξ :: l) = κ y ξ * rCoef κ tgt (tgt y ξ) l := by
  show (((κ y ξ : ℝ) : ℂ) * walkCoef (fun y ξ => ((κ y ξ : ℝ) : ℂ)) tgt (tgt y ξ) l).re =
    κ y ξ * rCoef κ tgt (tgt y ξ) l
  exact Complex.re_ofReal_mul _ _

/-- The walk along a word, from a sequence of states (`walk_ofFn` for real coefficients). -/
theorem rCoef_ofFn (κ : Y → Ξ → ℝ) (tgt : Y → Ξ → Y) (σ : ℕ → Y) (k : ℕ) (w : Fin k → Ξ)
    (hσ : ∀ i : Fin k, σ (i.val + 1) = tgt (σ i.val) (w i)) :
    walkEnd tgt (σ 0) (List.ofFn w) = σ k ∧
      rCoef κ tgt (σ 0) (List.ofFn w) = ∏ i : Fin k, κ (σ i.val) (w i) := by
  obtain ⟨h1, h2⟩ := walk_ofFn (fun y ξ => ((κ y ξ : ℝ) : ℂ)) tgt σ k w hσ
  refine ⟨h1, ?_⟩
  have h3 : walkCoef (fun y ξ => ((κ y ξ : ℝ) : ℂ)) tgt (σ 0) (List.ofFn w) =
      ((∏ i : Fin k, κ (σ i.val) (w i) : ℝ) : ℂ) := by
    rw [h2, Complex.ofReal_prod]
  unfold rCoef
  rw [h3, Complex.ofReal_re]

/-- **The sum over all words of a walk with nonnegative coefficients is at most a potential which
satisfies the row inequality.** The states carry a time `tm`, which every step increases by one;
if `∑_ξ κ(y, ξ) V(y·ξ) ≤ V(y)` at the times before `n` and the terminal function `φ` is at most
`V` at the time `n`, then for a walk which starts at `y` and has `k = n - tm(y)` steps
`∑_u (∏ κ along u) · φ(end of u) ≤ V(y)`. -/
theorem rWalk_sum_le [Fintype Ξ] (κ : Y → Ξ → ℝ) (tgt : Y → Ξ → Y) (φ V : Y → ℝ)
    (tm : Y → ℕ) (n : ℕ) (hκ : ∀ y ξ, 0 ≤ κ y ξ) (htm : ∀ y ξ, tm (tgt y ξ) = tm y + 1)
    (hV : ∀ y, tm y < n → ∑ ξ, κ y ξ * V (tgt y ξ) ≤ V y)
    (hφ : ∀ y, tm y = n → φ y ≤ V y) :
    ∀ (k : ℕ) (y : Y), tm y + k = n →
      ∑ u : Fin k → Ξ, rCoef κ tgt y (List.ofFn u) * φ (walkEnd tgt y (List.ofFn u)) ≤
        V y := by
  intro k
  induction k with
  | zero =>
    intro y hy
    rw [Fintype.sum_unique, List.ofFn_zero, rCoef_nil, one_mul]
    exact hφ y (by omega)
  | succ k ih =>
    intro y hy
    have hR : ∑ u : Fin (k + 1) → Ξ,
          rCoef κ tgt y (List.ofFn u) * φ (walkEnd tgt y (List.ofFn u)) =
        ∑ ξ : Ξ, ∑ u : Fin k → Ξ,
          rCoef κ tgt y (List.ofFn (wordConsEquiv k Ξ (ξ, u))) *
            φ (walkEnd tgt y (List.ofFn (wordConsEquiv k Ξ (ξ, u)))) :=
      (Equiv.sum_comp (wordConsEquiv k Ξ)
        (fun u => rCoef κ tgt y (List.ofFn u) * φ (walkEnd tgt y (List.ofFn u)))).symm.trans
        (Fintype.sum_prod_type _)
    rw [hR]
    refine le_trans (Finset.sum_le_sum fun ξ _ => ?_) (hV y (by omega))
    have hl : ∀ u : Fin k → Ξ, List.ofFn (wordConsEquiv k Ξ (ξ, u)) = ξ :: List.ofFn u := by
      intro u
      have h0 : wordConsEquiv k Ξ (ξ, u) 0 = ξ := by simp [wordConsEquiv]
      have hs : (fun i : Fin k => wordConsEquiv k Ξ (ξ, u) i.succ) = u := by
        funext i
        simp [wordConsEquiv]
      rw [List.ofFn_succ, h0, hs]
    have hterm : ∀ u : Fin k → Ξ,
        rCoef κ tgt y (List.ofFn (wordConsEquiv k Ξ (ξ, u))) *
            φ (walkEnd tgt y (List.ofFn (wordConsEquiv k Ξ (ξ, u)))) =
          κ y ξ * (rCoef κ tgt (tgt y ξ) (List.ofFn u) *
            φ (walkEnd tgt (tgt y ξ) (List.ofFn u))) := by
      intro u
      rw [hl u, rCoef_cons, mul_assoc]
      rfl
    rw [Finset.sum_congr rfl fun u _ => hterm u, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (ih (tgt y ξ) (by rw [htm]; omega)) (hκ y ξ)

/-- A real sum over a type which is in bijection with a triple product. -/
theorem sum_equiv_triple_real {H A W C : Type*} [Fintype H] [Fintype A] [Fintype W] [Fintype C]
    (ε : H ≃ A × W × C) (F : A → W → C → ℝ) :
    ∑ h, F (ε h).1 (ε h).2.1 (ε h).2.2 = ∑ a, ∑ w, ∑ c, F a w c := by
  have h1 : ∑ h, F (ε h).1 (ε h).2.1 (ε h).2.2 = ∑ t : A × W × C, F t.1 t.2.1 t.2.2 :=
    Equiv.sum_comp ε (fun t : A × W × C => F t.1 t.2.1 t.2.2)
  rw [h1]
  simp only [Fintype.sum_prod_type]

end Walks

/-! ### Histories -/

section Concrete

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N]

/-- **The number of ghost births of a history** [S-02:0803–0805]: the sum of the sizes of the
batches of all visit operations. -/
def History.ghostBirthTotal {D : MemData 𝒢 J ℓ N} {Bc : ℕ} (h : History D Bc) : ℕ :=
  ∑ i : Fin (D.n + 1), ghostBirthCount (h.ghost i)

/-- The absolute coefficient of the double step `G_j ℰ_j`, with doubled ghost births. -/
def tailK (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ) (y : ℕ × MState 𝒢 J ℓ Bc)
    (ξ : GhostChoice 𝒢 Bc × EdgeFullChoice D Bc) : ℝ :=
  (2 : ℝ) ^ ghostBirthCount ξ.1 * |ghostCoef D y.1 y.2 ξ.1| *
    ‖edgeFullCoef D (fun _ => 1) θ y.1 (ghostTgt y.2 ξ.1) ξ.2‖

/-- The absolute last factor `G_j 𝟏_∅` for the choice `c`, with doubled ghost births. -/
def tailLast (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (c : GhostChoice 𝒢 Bc)
    (y : ℕ × MState 𝒢 J ℓ Bc) : ℝ :=
  (2 : ℝ) ^ ghostBirthCount c * |ghostCoef D y.1 y.2 c| *
    ‖emptyVec 𝒢 J ℓ Bc (ghostTgt y.2 c)‖

omit [Fintype N] in
/-- The modulus of the weight of a history with every ghost birth doubled, as a product over its
operations. -/
theorem History.pow_mul_norm_weight (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ)
    (h : History D Bc) :
    (2 : ℝ) ^ h.ghostBirthTotal * ‖h.weight θ‖ =
      |memWeight 𝒢 D.q D.n h.init| *
        ((∏ i : Fin D.n,
            tailK D Bc θ (i.val, h.visitState i.val) (h.ghost i.castSucc, h.edge i)) *
          tailLast D Bc (h.ghost (Fin.last D.n)) (D.n, h.visitState D.n)) := by
  have hG : (2 : ℝ) ^ h.ghostBirthTotal =
      (∏ i : Fin D.n, (2 : ℝ) ^ ghostBirthCount (h.ghost i.castSucc)) *
        (2 : ℝ) ^ ghostBirthCount (h.ghost (Fin.last D.n)) := by
    unfold History.ghostBirthTotal
    rw [Fin.sum_univ_castSucc, pow_add, Finset.prod_pow_eq_pow_sum]
  have hP : ∏ i : Fin D.n,
        ‖((ghostCoef D i.val (h.visitState i.val) (h.ghost i.castSucc) : ℝ) : ℂ) *
          edgeFullCoef D (fun _ => 1) θ i.val (h.afterGhost i.castSucc) (h.edge i)‖ =
      ∏ i : Fin D.n, (|ghostCoef D i.val (h.visitState i.val) (h.ghost i.castSucc)| *
        ‖edgeFullCoef D (fun _ => 1) θ i.val (h.afterGhost i.castSucc) (h.edge i)‖) :=
    Finset.prod_congr rfl fun i _ => by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hW : ‖h.weight θ‖ = |memWeight 𝒢 D.q D.n h.init| *
      (∏ i : Fin D.n, (|ghostCoef D i.val (h.visitState i.val) (h.ghost i.castSucc)| *
        ‖edgeFullCoef D (fun _ => 1) θ i.val (h.afterGhost i.castSucc) (h.edge i)‖)) *
      (|ghostCoef D D.n (h.visitState D.n) (h.ghost (Fin.last D.n))| *
        ‖emptyVec 𝒢 J ℓ Bc (h.afterGhost (Fin.last D.n))‖) := by
    unfold History.weight
    rw [norm_mul, norm_mul, norm_mul, norm_prod, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, hP]
  have hK : ∏ i : Fin D.n,
        tailK D Bc θ (i.val, h.visitState i.val) (h.ghost i.castSucc, h.edge i) =
      (∏ i : Fin D.n, (2 : ℝ) ^ ghostBirthCount (h.ghost i.castSucc)) *
        ∏ i : Fin D.n, (|ghostCoef D i.val (h.visitState i.val) (h.ghost i.castSucc)| *
          ‖edgeFullCoef D (fun _ => 1) θ i.val (h.afterGhost i.castSucc) (h.edge i)‖) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => mul_assoc _ _ _
  have key : ∀ (P2 Pn m PW gn ev : ℝ),
      P2 * Pn * (m * PW * (gn * ev)) = m * (P2 * PW * (Pn * gn * ev)) := by
    intro P2 Pn m PW gn ev
    ring
  rw [hG, hW, hK]
  unfold tailLast
  exact key _ _ _ _ _ _

omit [Fintype N] in
/-- **The modulus of the weight of a history with every ghost birth doubled is the term of its
word**: the measure of the initial state, the absolute coefficients along the walk of its `N`
double steps, and the absolute last factor. -/
theorem History.absWeight_eq (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ) (h : History D Bc) :
    (2 : ℝ) ^ h.ghostBirthTotal * ‖h.weight θ‖ =
      |memWeight 𝒢 D.q D.n h.init| *
        (rCoef (tailK D Bc θ) (stepTgt D Bc) ((0 : ℕ), h.init)
            (List.ofFn fun i : Fin D.n => (h.ghost i.castSucc, h.edge i)) *
          tailLast D Bc (h.ghost (Fin.last D.n))
            (walkEnd (stepTgt D Bc) ((0 : ℕ), h.init)
              (List.ofFn fun i : Fin D.n => (h.ghost i.castSucc, h.edge i)))) := by
  obtain ⟨hend, hcoef⟩ := rCoef_ofFn (tailK D Bc θ) (stepTgt D Bc)
    (fun i => ((i : ℕ), h.visitState i)) D.n (fun i => (h.ghost i.castSucc, h.edge i))
    (fun i => congrArg (fun t => (i.val + 1, t)) (History.visitState_succ h i))
  have hend' : walkEnd (stepTgt D Bc) ((0 : ℕ), h.init)
      (List.ofFn fun i : Fin D.n => (h.ghost i.castSucc, h.edge i)) =
      (D.n, h.visitState D.n) := hend
  have hcoef' : rCoef (tailK D Bc θ) (stepTgt D Bc) ((0 : ℕ), h.init)
      (List.ofFn fun i : Fin D.n => (h.ghost i.castSucc, h.edge i)) =
      ∏ i : Fin D.n, tailK D Bc θ (i.val, h.visitState i.val)
        (h.ghost i.castSucc, h.edge i) := hcoef
  rw [hend', hcoef']
  exact History.pow_mul_norm_weight D Bc θ h

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- `|𝟏_∅| ≤ w` for the Schur weight `w = v^{j_tot}`, `v ≥ 1`. -/
theorem tail_emptyVec_le {v : ℝ} (hv : 1 ≤ v) {Bc : ℕ} (s : MState 𝒢 J ℓ Bc) :
    ‖emptyVec 𝒢 J ℓ Bc s‖ ≤ schurWeight v s := by
  have h1 : (1 : ℝ) ≤ schurWeight v s := one_le_pow₀ hv
  unfold emptyVec
  split_ifs
  · rw [norm_one]
    exact h1
  · rw [norm_zero]
    exact zero_le_one.trans h1

/-- The total mass of the initial states is at most `‖𝟏_∅‖²`. -/
theorem tail_sum_init_le {q : ℝ} {n Bc : ℕ} (hm : ∀ s : MState 𝒢 J ℓ Bc, 0 ≤ memWeight 𝒢 q n s) :
    ∑ a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
        memWeight 𝒢 q n (initState a Bc) ≤
      wNormSq (memWeight 𝒢 q n) (emptyVec 𝒢 J ℓ Bc) := by
  classical
  have hinj : Function.Injective
      fun a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ =>
        initState (𝒢 := 𝒢) a Bc := by
    intro a a' h
    have h1 : a.1 = a'.1 := congrArg MState.y h
    have h2 : a.2.1 = a'.2.1 := congrArg MState.xs h
    have h3 : a.2.2 = a'.2.2 := congrArg MState.xb h
    exact Prod.ext h1 (Prod.ext h2 h3)
  have hterm : ∀ a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
      memWeight 𝒢 q n (initState a Bc) =
        memWeight 𝒢 q n (initState a Bc) * ‖emptyVec 𝒢 J ℓ Bc (initState a Bc)‖ ^ 2 := by
    intro a
    rw [emptyVec_initState, norm_one, one_pow, mul_one]
  calc ∑ a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
        memWeight 𝒢 q n (initState a Bc)
      = ∑ a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
          memWeight 𝒢 q n (initState a Bc) * ‖emptyVec 𝒢 J ℓ Bc (initState a Bc)‖ ^ 2 :=
        Finset.sum_congr rfl fun a _ => hterm a
    _ = ∑ s ∈ Finset.univ.image
          (fun a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ =>
            initState (𝒢 := 𝒢) a Bc),
          memWeight 𝒢 q n s * ‖emptyVec 𝒢 J ℓ Bc s‖ ^ 2 :=
        (Finset.sum_image (s := Finset.univ)
          (f := fun s => memWeight 𝒢 q n s * ‖emptyVec 𝒢 J ℓ Bc s‖ ^ 2)
          (g := fun a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ ×
            LabelList 𝒢.big J ℓ => initState (𝒢 := 𝒢) a Bc)
          (fun a _ a' _ h => hinj h)).symm
    _ ≤ ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 q n s * ‖emptyVec 𝒢 J ℓ Bc s‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          fun s _ _ => mul_nonneg (hm s) (sq_nonneg _)

/-- One double step of the absolute path sum: the row bound of the visit operation with doubled
births and the row bound of the edge. -/
theorem tail_step_le (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ) {v Rg Re C : ℝ} (hRe : 0 ≤ Re)
    (hC : 0 ≤ C)
    (hG : ∀ i, i ≤ D.n → RowBound (schurWeight v)
      (fun (s : MState 𝒢 J ℓ Bc) (c : GhostChoice 𝒢 Bc) =>
        (2 : ℝ) ^ ghostBirthCount c * |ghostCoef D i s c|) ghostTgt Rg)
    (hE : ∀ i, i < D.n → RowBound (schurWeight v)
      (fun (s : MState 𝒢 J ℓ Bc) (ξ : EdgeFullChoice D Bc) =>
        ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖) (edgeFullTgt D i) Re)
    (y : ℕ × MState 𝒢 J ℓ Bc) (hy : y.1 < D.n) :
    ∑ ξ : GhostChoice 𝒢 Bc × EdgeFullChoice D Bc,
        tailK D Bc θ y ξ * (C * schurWeight v (edgeFullTgt D y.1 (ghostTgt y.2 ξ.1) ξ.2)) ≤
      Rg * (Re * C) * schurWeight v y.2 := by
  calc ∑ ξ : GhostChoice 𝒢 Bc × EdgeFullChoice D Bc,
        tailK D Bc θ y ξ * (C * schurWeight v (edgeFullTgt D y.1 (ghostTgt y.2 ξ.1) ξ.2))
      = ∑ c : GhostChoice 𝒢 Bc, ((2 : ℝ) ^ ghostBirthCount c * |ghostCoef D y.1 y.2 c|) *
          (C * ∑ ξ : EdgeFullChoice D Bc,
            ‖edgeFullCoef D (fun _ => 1) θ y.1 (ghostTgt y.2 c) ξ‖ *
              schurWeight v (edgeFullTgt D y.1 (ghostTgt y.2 c) ξ)) := by
        refine (Fintype.sum_prod_type _).trans (Finset.sum_congr rfl fun c _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun ξ _ => ?_
        show (2 : ℝ) ^ ghostBirthCount c * |ghostCoef D y.1 y.2 c| *
            ‖edgeFullCoef D (fun _ => 1) θ y.1 (ghostTgt y.2 c) ξ‖ *
            (C * schurWeight v (edgeFullTgt D y.1 (ghostTgt y.2 c) ξ)) =
          (2 : ℝ) ^ ghostBirthCount c * |ghostCoef D y.1 y.2 c| *
            (C * (‖edgeFullCoef D (fun _ => 1) θ y.1 (ghostTgt y.2 c) ξ‖ *
              schurWeight v (edgeFullTgt D y.1 (ghostTgt y.2 c) ξ)))
        ring
    _ ≤ ∑ c : GhostChoice 𝒢 Bc, ((2 : ℝ) ^ ghostBirthCount c * |ghostCoef D y.1 y.2 c|) *
          (C * (Re * schurWeight v (ghostTgt y.2 c))) :=
        Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hE y.1 hy (ghostTgt y.2 c)) hC)
          (mul_nonneg (pow_nonneg zero_le_two _) (abs_nonneg _))
    _ = C * Re * ∑ c : GhostChoice 𝒢 Bc,
          ((2 : ℝ) ^ ghostBirthCount c * |ghostCoef D y.1 y.2 c|) *
            schurWeight v (ghostTgt y.2 c) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring
    _ ≤ C * Re * (Rg * schurWeight v y.2) :=
        mul_le_mul_of_nonneg_left (hG y.1 hy.le y.2) (mul_nonneg hC hRe)
    _ = Rg * (Re * C) * schurWeight v y.2 := by ring

/-- **The absolute path sum with doubled ghost births** [S-02:0803–0811]: "multiply every ghost
birth by two in the absolute path sum and use the preceding bounds". If the absolute visit
operations with doubled births have the weighted row bound `R_g` and the absolute edges the
weighted row bound `R_e`, then
`∑_h 2^{#ghost births} |weight(h)| ≤ ‖𝟏_∅‖² R_g^{N+1} R_e^N`. -/
theorem tail_absSum_le (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ) {v Rg Re : ℝ} (hv : 1 ≤ v)
    (hm : ∀ s : MState 𝒢 J ℓ Bc, 0 ≤ memWeight 𝒢 D.q D.n s) (hRg : 0 ≤ Rg) (hRe : 0 ≤ Re)
    (hG : ∀ i, i ≤ D.n → RowBound (schurWeight v)
      (fun (s : MState 𝒢 J ℓ Bc) (c : GhostChoice 𝒢 Bc) =>
        (2 : ℝ) ^ ghostBirthCount c * |ghostCoef D i s c|) ghostTgt Rg)
    (hE : ∀ i, i < D.n → RowBound (schurWeight v)
      (fun (s : MState 𝒢 J ℓ Bc) (ξ : EdgeFullChoice D Bc) =>
        ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖) (edgeFullTgt D i) Re) :
    ∑ h : History D Bc, (2 : ℝ) ^ h.ghostBirthTotal * ‖h.weight θ‖ ≤
      wNormSq (memWeight 𝒢 D.q D.n) (emptyVec 𝒢 J ℓ Bc) * (Rg ^ (D.n + 1) * Re ^ D.n) := by
  obtain ⟨V, hV⟩ : ∃ V : ℕ × MState 𝒢 J ℓ Bc → ℝ, ∀ y,
      V y = Rg ^ (D.n + 1 - y.1) * Re ^ (D.n - y.1) * schurWeight v y.2 := ⟨_, fun _ => rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : ℕ × MState 𝒢 J ℓ Bc → ℝ, ∀ y,
      φ y = ∑ c : GhostChoice 𝒢 Bc, tailLast D Bc c y := ⟨_, fun _ => rfl⟩
  have hκ0 : ∀ (y : ℕ × MState 𝒢 J ℓ Bc) (ξ : GhostChoice 𝒢 Bc × EdgeFullChoice D Bc),
      0 ≤ tailK D Bc θ y ξ := fun y ξ =>
    mul_nonneg (mul_nonneg (pow_nonneg zero_le_two _) (abs_nonneg _)) (norm_nonneg _)
  -- the row inequality of the potential
  have hrow : ∀ y : ℕ × MState 𝒢 J ℓ Bc, y.1 < D.n →
      ∑ ξ : GhostChoice 𝒢 Bc × EdgeFullChoice D Bc,
        tailK D Bc θ y ξ * V (stepTgt D Bc y ξ) ≤ V y := by
    intro y hy
    obtain ⟨r, hr⟩ : ∃ r, D.n = y.1 + 1 + r := ⟨D.n - y.1 - 1, by omega⟩
    have e1 : D.n + 1 - y.1 = r + 1 + 1 := by omega
    have e2 : D.n - y.1 = r + 1 := by omega
    have e3 : D.n + 1 - (y.1 + 1) = r + 1 := by omega
    have e4 : D.n - (y.1 + 1) = r := by omega
    have hstep := tail_step_le D Bc θ (Rg := Rg) (C := Rg ^ (r + 1) * Re ^ r) hRe
      (mul_nonneg (pow_nonneg hRg _) (pow_nonneg hRe _)) hG hE y hy
    have hL : ∀ ξ : GhostChoice 𝒢 Bc × EdgeFullChoice D Bc,
        tailK D Bc θ y ξ * V (stepTgt D Bc y ξ) =
          tailK D Bc θ y ξ * (Rg ^ (r + 1) * Re ^ r *
            schurWeight v (edgeFullTgt D y.1 (ghostTgt y.2 ξ.1) ξ.2)) := by
      intro ξ
      have hVt : V (stepTgt D Bc y ξ) = Rg ^ (D.n + 1 - (y.1 + 1)) * Re ^ (D.n - (y.1 + 1)) *
          schurWeight v (edgeFullTgt D y.1 (ghostTgt y.2 ξ.1) ξ.2) := hV _
      rw [hVt, e3, e4]
    have hRV : Rg * (Re * (Rg ^ (r + 1) * Re ^ r)) * schurWeight v y.2 = V y := by
      rw [hV y, e1, e2]
      ring
    rw [Finset.sum_congr rfl fun ξ _ => hL ξ, ← hRV]
    exact hstep
  -- the last visit operation
  have hlast : ∀ y : ℕ × MState 𝒢 J ℓ Bc, y.1 = D.n → φ y ≤ V y := by
    intro y hy
    have e1 : D.n + 1 - y.1 = 1 := by omega
    have e2 : D.n - y.1 = 0 := by omega
    rw [hφ y, hV y, e1, e2, pow_one, pow_zero, mul_one]
    refine le_trans (Finset.sum_le_sum fun c _ => ?_) (hG y.1 (by omega) y.2)
    show (2 : ℝ) ^ ghostBirthCount c * |ghostCoef D y.1 y.2 c| *
        ‖emptyVec 𝒢 J ℓ Bc (ghostTgt y.2 c)‖ ≤
      (2 : ℝ) ^ ghostBirthCount c * |ghostCoef D y.1 y.2 c| * schurWeight v (ghostTgt y.2 c)
    exact mul_le_mul_of_nonneg_left (tail_emptyVec_le hv _)
      (mul_nonneg (pow_nonneg zero_le_two _) (abs_nonneg _))
  have hwalk := rWalk_sum_le (tailK D Bc θ) (stepTgt D Bc) φ V (fun y => y.1) D.n hκ0
    (fun _ _ => rfl) hrow hlast D.n
  -- one initial datum
  have hinit : ∀ a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
      ∑ w : Fin D.n → GhostChoice 𝒢 Bc × EdgeFullChoice D Bc, ∑ c : GhostChoice 𝒢 Bc,
          |memWeight 𝒢 D.q D.n (initState a Bc)| *
            (rCoef (tailK D Bc θ) (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w) *
              tailLast D Bc c
                (walkEnd (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w))) ≤
        memWeight 𝒢 D.q D.n (initState a Bc) * (Rg ^ (D.n + 1) * Re ^ D.n) := by
    intro a
    have h0 := hwalk ((0 : ℕ), initState a Bc) (Nat.zero_add _)
    have hw : schurWeight v (initState (𝒢 := 𝒢) (J := J) (ℓ := ℓ) a Bc) = 1 := by
      have h00 : memTotal (initState (𝒢 := 𝒢) (J := J) (ℓ := ℓ) a Bc) = 0 :=
        Finset.sum_eq_zero fun g _ => rfl
      unfold schurWeight
      rw [h00, pow_zero]
    have hV0 : V ((0 : ℕ), initState a Bc) = Rg ^ (D.n + 1) * Re ^ D.n := by
      have h1 : V ((0 : ℕ), initState a Bc) = Rg ^ (D.n + 1 - 0) * Re ^ (D.n - 0) *
          schurWeight v (initState (𝒢 := 𝒢) (J := J) (ℓ := ℓ) a Bc) := hV _
      rw [h1, hw, mul_one, Nat.sub_zero, Nat.sub_zero]
    rw [abs_of_nonneg (hm _)]
    calc ∑ w : Fin D.n → GhostChoice 𝒢 Bc × EdgeFullChoice D Bc, ∑ c : GhostChoice 𝒢 Bc,
          memWeight 𝒢 D.q D.n (initState a Bc) *
            (rCoef (tailK D Bc θ) (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w) *
              tailLast D Bc c
                (walkEnd (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w)))
        = memWeight 𝒢 D.q D.n (initState a Bc) *
            ∑ w : Fin D.n → GhostChoice 𝒢 Bc × EdgeFullChoice D Bc,
              rCoef (tailK D Bc θ) (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w) *
                φ (walkEnd (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [hφ, Finset.mul_sum, Finset.mul_sum]
      _ ≤ memWeight 𝒢 D.q D.n (initState a Bc) * V ((0 : ℕ), initState a Bc) :=
          mul_le_mul_of_nonneg_left h0 (hm _)
      _ = memWeight 𝒢 D.q D.n (initState a Bc) * (Rg ^ (D.n + 1) * Re ^ D.n) := by rw [hV0]
  have hsum : ∑ h : History D Bc, (2 : ℝ) ^ h.ghostBirthTotal * ‖h.weight θ‖ =
      ∑ a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
        ∑ w : Fin D.n → GhostChoice 𝒢 Bc × EdgeFullChoice D Bc, ∑ c : GhostChoice 𝒢 Bc,
          |memWeight 𝒢 D.q D.n (initState a Bc)| *
            (rCoef (tailK D Bc θ) (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w) *
              tailLast D Bc c
                (walkEnd (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w))) :=
    (Finset.sum_congr rfl fun h _ => History.absWeight_eq D Bc θ h).trans
      (sum_equiv_triple_real (histWalkEquiv D Bc) (fun a w c =>
        |memWeight 𝒢 D.q D.n (initState a Bc)| *
          (rCoef (tailK D Bc θ) (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w) *
            tailLast D Bc c
              (walkEnd (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w)))))
  rw [hsum]
  calc ∑ a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
        ∑ w : Fin D.n → GhostChoice 𝒢 Bc × EdgeFullChoice D Bc, ∑ c : GhostChoice 𝒢 Bc,
          |memWeight 𝒢 D.q D.n (initState a Bc)| *
            (rCoef (tailK D Bc θ) (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w) *
              tailLast D Bc c
                (walkEnd (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w)))
      ≤ ∑ a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
          memWeight 𝒢 D.q D.n (initState a Bc) * (Rg ^ (D.n + 1) * Re ^ D.n) :=
        Finset.sum_le_sum fun a _ => hinit a
    _ = (∑ a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
          memWeight 𝒢 D.q D.n (initState a Bc)) * (Rg ^ (D.n + 1) * Re ^ D.n) :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ wNormSq (memWeight 𝒢 D.q D.n) (emptyVec 𝒢 J ℓ Bc) * (Rg ^ (D.n + 1) * Re ^ D.n) :=
        mul_le_mul_of_nonneg_right (tail_sum_init_le hm)
          (mul_nonneg (pow_nonneg hRg _) (pow_nonneg hRe _))

end Concrete

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
