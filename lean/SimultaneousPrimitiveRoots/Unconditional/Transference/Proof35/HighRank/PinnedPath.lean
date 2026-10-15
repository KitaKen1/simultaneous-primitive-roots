module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.HighRank.EdgePinned
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.HighRank.GhostPinned
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.TailAbsSum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Large rank: the absolute path sum with prescribed birth values

Source: `verification/stage7-sources/S-02.tex`, lines 1140–1151 (`[S-02:1140–1151]`).

"For completeness, these conditional row bounds can be iterated although a pivot may have died
before its dependent birth. Retain all pivot values in the conditioning. Bound the remaining
terminal sum by backward induction using the uniform weighted row bounds for every possible
conditioning, beginning with `𝟏_∅ ≤ w`. … At the initial boundary `w = 1`, and the remaining
integrated boundary mass is bounded."

Here the conditioning is a partial assignment `pv` of prime values to the birth addresses (in the
application: a common value for every block, `Blocks.lean`), fixed along the whole path. The
indicator that a history realizes `pv` is the product of the indicators of its operations
(`hrIndI`, `hrIndG`, `hrIndE`), because "these are conditions on the choices made in their single
local operation" [S-02:1061–1062]. The absolute path sum with these indicators is bounded by
backward induction (`rWalk_sum_le` of `TailAbsSum.lean`, the induction of the truncation estimate)
with the potential `V(i, state) = Cst(i) · v^{j_tot}`:

`hr_pinnedPath_le`: if the visit operation `G_i` and the edge `ℰ_i` with the indicators of `pv`
have the weighted row bounds `R_G(i)` and `R_E(i)`, and the initial mass with the indicator is at
most `K₀`, then

`∑_{h realizing pv} |weight(h)| ≤ K₀ · ∏_{i < N} R_G(i) R_E(i) · R_G(N)`.

* `hrPinI`, `hrPinE`, `hrPinG` — the prescribed values of the initial slots, of the target slots
  of the edge `i`, and of the batch indices of the visit `i`.
* `hrIndI` — the indicator that the initial big list realizes its prescribed values.
* `hrK`, `hrLast` — the absolute coefficient of the double step `G_i ℰ_i` and the absolute last
  factor `G_N 𝟏_∅`, with the indicators.
* `History.hr_term_le` — the modulus of the weight of a history which realizes `pv` is the term of
  its word.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### The prescribed values of one operation -/

section HrPinsOfAddr

variable {B : Type} {J ℓ Bc n : ℕ}

/-- The prescribed values of the initial big slots. -/
def hrPinI (pv : BirthAddr B J ℓ Bc n → Option ℕ) : (g : B) → Slot J ℓ → Option ℕ :=
  fun g sl => pv (Sum.inl (g, sl))

/-- The prescribed values of the big target slots of the edge `i`. -/
def hrPinE (pv : BirthAddr B J ℓ Bc n → Option ℕ) (i : ℕ) : (g : B) → Slot J ℓ → Option ℕ :=
  fun g sl => if h : i < n then pv (Sum.inr (Sum.inl (⟨i, h⟩, g, sl))) else none

/-- The prescribed values of the indices of the ghost batches of the visit `i`. -/
def hrPinG (pv : BirthAddr B J ℓ Bc n → Option ℕ) (i : ℕ) : (g : B) → Fin Bc → Option ℕ :=
  fun g j => if h : i < n + 1 then pv (Sum.inr (Sum.inr (⟨i, h⟩, g, j))) else none

theorem hrPinE_fin (pv : BirthAddr B J ℓ Bc n → Option ℕ) (i : Fin n) (g : B) (sl : Slot J ℓ) :
    hrPinE pv i.val g sl = pv (Sum.inr (Sum.inl (i, g, sl))) :=
  dif_pos i.isLt

theorem hrPinG_fin (pv : BirthAddr B J ℓ Bc n → Option ℕ) (i : Fin (n + 1)) (g : B)
    (j : Fin Bc) : hrPinG pv i.val g j = pv (Sum.inr (Sum.inr (i, g, j))) :=
  dif_pos i.isLt

end HrPinsOfAddr

section HrIndInit

variable {S B : Type} {𝒢 : GroupFamily S B} {J ℓ : ℕ}

open _root_.Classical in
/-- **The initial big list realizes the prescribed values** (an indicator, as a real number);
every initial big slot is a performed birth address. -/
def hrIndI (pv : (g : B) → Slot J ℓ → Option ℕ) (xb : LabelList 𝒢.big J ℓ) : ℝ :=
  if ∀ g sl z, pv g sl = some z → (xb g sl : ℕ) = z then 1 else 0

theorem hrIndI_nonneg (pv : (g : B) → Slot J ℓ → Option ℕ) (xb : LabelList 𝒢.big J ℓ) :
    0 ≤ hrIndI pv xb := by
  unfold hrIndI
  split_ifs
  · exact zero_le_one
  · exact le_rfl

theorem hrIndI_of {pv : (g : B) → Slot J ℓ → Option ℕ} {xb : LabelList 𝒢.big J ℓ}
    (h : ∀ g sl z, pv g sl = some z → (xb g sl : ℕ) = z) : hrIndI pv xb = 1 := by
  unfold hrIndI
  exact if_pos h

end HrIndInit

/-- A product of nonnegative real coefficients along a walk is nonnegative. -/
theorem hr_rCoef_nonneg {Y Ξ : Type*} (κ : Y → Ξ → ℝ) (tgt : Y → Ξ → Y)
    (hκ : ∀ y ξ, 0 ≤ κ y ξ) (l : List Ξ) : ∀ y : Y, 0 ≤ rCoef κ tgt y l := by
  induction l with
  | nil =>
    intro y
    rw [rCoef_nil]
    exact zero_le_one
  | cons ξ l ih =>
    intro y
    rw [rCoef_cons]
    exact mul_nonneg (hκ y ξ) (ih _)

/-! ### Histories -/

section HrPath

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N]

/-- The absolute coefficient of the double step `G_j ℰ_j` with the indicators of the prescribed
values `pv`. -/
def hrK (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ) (pv : BirthAddr B J ℓ Bc D.n → Option ℕ)
    (y : ℕ × MState 𝒢 J ℓ Bc) (ξ : GhostChoice 𝒢 Bc × EdgeFullChoice D Bc) : ℝ :=
  hrIndG (hrPinG pv y.1) ξ.1 * |ghostCoef D y.1 y.2 ξ.1| *
    (‖edgeFullCoef D (fun _ => 1) θ y.1 (ghostTgt y.2 ξ.1) ξ.2‖ *
      hrIndE (hrPinE pv y.1) (edgeBirths ξ.2.2.1))

/-- The absolute last factor `G_j 𝟏_∅` for the choice `c`, with the indicator of the prescribed
values `pv`. -/
def hrLast (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (pv : BirthAddr B J ℓ Bc D.n → Option ℕ)
    (c : GhostChoice 𝒢 Bc) (y : ℕ × MState 𝒢 J ℓ Bc) : ℝ :=
  hrIndG (hrPinG pv y.1) c * |ghostCoef D y.1 y.2 c| *
    ‖emptyVec 𝒢 J ℓ Bc (ghostTgt y.2 c)‖

omit [Fintype N] in
theorem hrK_nonneg (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ)
    (pv : BirthAddr B J ℓ Bc D.n → Option ℕ) (y : ℕ × MState 𝒢 J ℓ Bc)
    (ξ : GhostChoice 𝒢 Bc × EdgeFullChoice D Bc) : 0 ≤ hrK D Bc θ pv y ξ :=
  mul_nonneg (mul_nonneg (hrIndG_nonneg _ _) (abs_nonneg _))
    (mul_nonneg (norm_nonneg _) (hrIndE_nonneg _ _))

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
theorem hrLast_nonneg (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (pv : BirthAddr B J ℓ Bc D.n → Option ℕ)
    (c : GhostChoice 𝒢 Bc) (y : ℕ × MState 𝒢 J ℓ Bc) : 0 ≤ hrLast D Bc pv c y :=
  mul_nonneg (mul_nonneg (hrIndG_nonneg _ _) (abs_nonneg _)) (norm_nonneg _)

variable {D : MemData 𝒢 J ℓ N} {Bc : ℕ}

omit [Fintype B] [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- A history which realizes `pv` has an initial big list which realizes the prescribed values of
the initial slots. -/
theorem History.hr_indI (h : History D Bc) {pv : BirthAddr B J ℓ Bc D.n → Option ℕ}
    (hp : HrPinned pv h.birth) : hrIndI (hrPinI pv) h.xb₀ = 1 := by
  refine hrIndI_of fun g sl z hz => ?_
  have h1 : h.birth (Sum.inl (g, sl)) = some z := hp _ z hz
  exact Option.some.inj h1

omit [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- A history which realizes `pv` has, at every visit, batches which realize the prescribed values
of that visit. -/
theorem History.hr_indG (h : History D Bc) {pv : BirthAddr B J ℓ Bc D.n → Option ℕ}
    (hp : HrPinned pv h.birth) (k : Fin (D.n + 1)) :
    hrIndG (hrPinG pv k.val) (h.ghost k) = 1 := by
  refine hrIndG_of fun g j z hz => ?_
  rw [hrPinG_fin] at hz
  exact hp _ z hz

omit [Fintype B] [DecidableEq S] [DecidableEq B] [Fintype N] in
/-- A history which realizes `pv` has, at every edge, fresh births which realize the prescribed
values of that edge. -/
theorem History.hr_indE (h : History D Bc) {pv : BirthAddr B J ℓ Bc D.n → Option ℕ}
    (hp : HrPinned pv h.birth) (k : Fin D.n) :
    hrIndE (hrPinE pv k.val) (edgeBirths (h.edge k).2.1) = 1 := by
  refine hrIndE_of fun g sl z hz => ?_
  rw [hrPinE_fin] at hz
  exact hp _ z hz

omit [Fintype N] in
/-- The modulus of the weight of a history, as a product over its operations. -/
theorem History.hr_norm_weight (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ) (h : History D Bc) :
    ‖h.weight θ‖ = |memWeight 𝒢 D.q D.n h.init| *
      (∏ i : Fin D.n, (|ghostCoef D i.val (h.visitState i.val) (h.ghost i.castSucc)| *
        ‖edgeFullCoef D (fun _ => 1) θ i.val (h.afterGhost i.castSucc) (h.edge i)‖)) *
      (|ghostCoef D D.n (h.visitState D.n) (h.ghost (Fin.last D.n))| *
        ‖emptyVec 𝒢 J ℓ Bc (h.afterGhost (Fin.last D.n))‖) := by
  have hP : ∏ i : Fin D.n,
        ‖((ghostCoef D i.val (h.visitState i.val) (h.ghost i.castSucc) : ℝ) : ℂ) *
          edgeFullCoef D (fun _ => 1) θ i.val (h.afterGhost i.castSucc) (h.edge i)‖ =
      ∏ i : Fin D.n, (|ghostCoef D i.val (h.visitState i.val) (h.ghost i.castSucc)| *
        ‖edgeFullCoef D (fun _ => 1) θ i.val (h.afterGhost i.castSucc) (h.edge i)‖) :=
    Finset.prod_congr rfl fun i _ => by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  unfold History.weight
  rw [norm_mul, norm_mul, norm_mul, norm_prod, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, hP]

open _root_.Classical in
omit [Fintype N] in
/-- **The modulus of the weight of a history which realizes `pv` is at most the term of its
word**: the indicator and the measure of the initial state, the absolute coefficients with the
indicators along the walk of its `N` double steps, and the absolute last factor. (Equality holds;
only this inequality is used.) -/
theorem History.hr_term_le (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ)
    (pv : BirthAddr B J ℓ Bc D.n → Option ℕ) (h : History D Bc) :
    (if HrPinned pv h.birth then ‖h.weight θ‖ else 0) ≤
      hrIndI (hrPinI pv) h.xb₀ * |memWeight 𝒢 D.q D.n h.init| *
        (rCoef (hrK D Bc θ pv) (stepTgt D Bc) ((0 : ℕ), h.init)
            (List.ofFn fun i : Fin D.n => (h.ghost i.castSucc, h.edge i)) *
          hrLast D Bc pv (h.ghost (Fin.last D.n))
            (walkEnd (stepTgt D Bc) ((0 : ℕ), h.init)
              (List.ofFn fun i : Fin D.n => (h.ghost i.castSucc, h.edge i)))) := by
  by_cases hp : HrPinned pv h.birth
  · rw [if_pos hp]
    obtain ⟨hend, hcoef⟩ := rCoef_ofFn (hrK D Bc θ pv) (stepTgt D Bc)
      (fun i => ((i : ℕ), h.visitState i)) D.n (fun i => (h.ghost i.castSucc, h.edge i))
      (fun i => congrArg (fun t => (i.val + 1, t)) (History.visitState_succ h i))
    have hend' : walkEnd (stepTgt D Bc) ((0 : ℕ), h.init)
        (List.ofFn fun i : Fin D.n => (h.ghost i.castSucc, h.edge i)) =
        (D.n, h.visitState D.n) := hend
    have hcoef' : rCoef (hrK D Bc θ pv) (stepTgt D Bc) ((0 : ℕ), h.init)
        (List.ofFn fun i : Fin D.n => (h.ghost i.castSucc, h.edge i)) =
        ∏ i : Fin D.n, hrK D Bc θ pv (i.val, h.visitState i.val)
          (h.ghost i.castSucc, h.edge i) := hcoef
    have hK : ∀ i : Fin D.n,
        hrK D Bc θ pv (i.val, h.visitState i.val) (h.ghost i.castSucc, h.edge i) =
          |ghostCoef D i.val (h.visitState i.val) (h.ghost i.castSucc)| *
            ‖edgeFullCoef D (fun _ => 1) θ i.val (h.afterGhost i.castSucc) (h.edge i)‖ := by
      intro i
      have e1 : hrIndG (hrPinG pv i.val) (h.ghost i.castSucc) = 1 :=
        History.hr_indG h hp i.castSucc
      have e2 : hrIndE (hrPinE pv i.val) (edgeBirths (h.edge i).2.1) = 1 :=
        History.hr_indE h hp i
      show hrIndG (hrPinG pv i.val) (h.ghost i.castSucc) *
          |ghostCoef D i.val (h.visitState i.val) (h.ghost i.castSucc)| *
          (‖edgeFullCoef D (fun _ => 1) θ i.val
              (ghostTgt (h.visitState i.val) (h.ghost i.castSucc)) (h.edge i)‖ *
            hrIndE (hrPinE pv i.val) (edgeBirths (h.edge i).2.1)) = _
      rw [e1, e2, one_mul, mul_one]
      rfl
    have hL : hrLast D Bc pv (h.ghost (Fin.last D.n)) (D.n, h.visitState D.n) =
        |ghostCoef D D.n (h.visitState D.n) (h.ghost (Fin.last D.n))| *
          ‖emptyVec 𝒢 J ℓ Bc (h.afterGhost (Fin.last D.n))‖ := by
      have e1 : hrIndG (hrPinG pv D.n) (h.ghost (Fin.last D.n)) = 1 :=
        History.hr_indG h hp (Fin.last D.n)
      show hrIndG (hrPinG pv D.n) (h.ghost (Fin.last D.n)) *
          |ghostCoef D D.n (h.visitState D.n) (h.ghost (Fin.last D.n))| *
          ‖emptyVec 𝒢 J ℓ Bc (ghostTgt (h.visitState D.n) (h.ghost (Fin.last D.n)))‖ = _
      rw [e1, one_mul]
      rfl
    rw [hend', hcoef', Finset.prod_congr rfl fun i _ => hK i, hL, History.hr_indI h hp, one_mul,
      History.hr_norm_weight D Bc θ h]
    exact le_of_eq (mul_assoc _ _ _)
  · rw [if_neg hp]
    exact mul_nonneg (mul_nonneg (hrIndI_nonneg _ _) (abs_nonneg _))
      (mul_nonneg (hr_rCoef_nonneg _ _ (hrK_nonneg D Bc θ pv) _ _) (hrLast_nonneg D Bc pv _ _))

open _root_.Classical in
/-- **The absolute path sum with prescribed birth values** [S-02:1140–1151]: "bound the remaining
terminal sum by backward induction using the uniform weighted row bounds for every possible
conditioning, beginning with `𝟏_∅ ≤ w`. … At the initial boundary `w = 1`, and the remaining
integrated boundary mass is bounded."

Let `pv` be a partial assignment of prime values to the birth addresses. If, for the Schur weight
`w = v^{j_tot}` (`v ≥ 1`), the absolute visit operation `G_i` restricted to the choices which
realize the values prescribed at the visit `i` has the row bound `R_G(i)`, the absolute edge `ℰ_i`
restricted to the choices which realize the values prescribed at the edge `i` has the row bound
`R_E(i)`, and the mass of the initial states which realize the values prescribed at the initial
slots is at most `K₀`, then

`∑_{h realizing pv} |weight(h)| ≤ K₀ · ∏_{i < N} R_G(i) R_E(i) · R_G(N)`. -/
theorem hr_pinnedPath_le (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ)
    (pv : BirthAddr B J ℓ Bc D.n → Option ℕ) {v K₀ : ℝ} (hv : 1 ≤ v)
    (hm : ∀ s : MState 𝒢 J ℓ Bc, 0 ≤ memWeight 𝒢 D.q D.n s) (RG RE : ℕ → ℝ)
    (hRG : ∀ i, 0 ≤ RG i) (hRE : ∀ i, 0 ≤ RE i)
    (hG : ∀ i, i ≤ D.n → ∀ s : MState 𝒢 J ℓ Bc,
      ∑ c : GhostChoice 𝒢 Bc,
          hrIndG (hrPinG pv i) c * |ghostCoef D i s c| * schurWeight v (ghostTgt s c) ≤
        RG i * schurWeight v s)
    (hE : ∀ i, i < D.n → ∀ s : MState 𝒢 J ℓ Bc,
      ∑ ξ : EdgeFullChoice D Bc,
          ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ * hrIndE (hrPinE pv i) (edgeBirths ξ.2.1) *
            schurWeight v (edgeFullTgt D i s ξ) ≤
        RE i * schurWeight v s)
    (hI : ∑ a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
        hrIndI (hrPinI pv) a.2.2 * memWeight 𝒢 D.q D.n (initState a Bc) ≤ K₀) :
    ∑ h : History D Bc, (if HrPinned pv h.birth then ‖h.weight θ‖ else 0) ≤
      K₀ * ((∏ i ∈ Finset.range D.n, (RG i * RE i)) * RG D.n) := by
  -- the constants of the potential
  obtain ⟨Cst, hCst⟩ : ∃ Cst : ℕ → ℝ, ∀ i,
      Cst i = (∏ k ∈ Finset.Ico i D.n, (RG k * RE k)) * RG D.n := ⟨_, fun _ => rfl⟩
  have hCst0 : ∀ i, 0 ≤ Cst i := by
    intro i
    rw [hCst]
    exact mul_nonneg (Finset.prod_nonneg fun k _ => mul_nonneg (hRG k) (hRE k)) (hRG _)
  have hCstStep : ∀ i, i < D.n → Cst i = RG i * (RE i * Cst (i + 1)) := by
    intro i hi
    rw [hCst i, hCst (i + 1), Finset.prod_eq_prod_Ico_succ_bot hi]
    ring
  have hCstLast : Cst D.n = RG D.n := by
    rw [hCst, Finset.Ico_self, Finset.prod_empty, one_mul]
  obtain ⟨V, hV⟩ : ∃ V : ℕ × MState 𝒢 J ℓ Bc → ℝ, ∀ y,
      V y = Cst y.1 * schurWeight v y.2 := ⟨_, fun _ => rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : ℕ × MState 𝒢 J ℓ Bc → ℝ, ∀ y,
      φ y = ∑ c : GhostChoice 𝒢 Bc, hrLast D Bc pv c y := ⟨_, fun _ => rfl⟩
  -- the row inequality of the potential: one double step
  have hrow : ∀ y : ℕ × MState 𝒢 J ℓ Bc, y.1 < D.n →
      ∑ ξ : GhostChoice 𝒢 Bc × EdgeFullChoice D Bc,
        hrK D Bc θ pv y ξ * V (stepTgt D Bc y ξ) ≤ V y := by
    intro y hy
    have hC0 : 0 ≤ Cst (y.1 + 1) := hCst0 _
    calc ∑ ξ : GhostChoice 𝒢 Bc × EdgeFullChoice D Bc,
          hrK D Bc θ pv y ξ * V (stepTgt D Bc y ξ)
        = ∑ c : GhostChoice 𝒢 Bc, (hrIndG (hrPinG pv y.1) c * |ghostCoef D y.1 y.2 c|) *
            (Cst (y.1 + 1) * ∑ ξ : EdgeFullChoice D Bc,
              ‖edgeFullCoef D (fun _ => 1) θ y.1 (ghostTgt y.2 c) ξ‖ *
                hrIndE (hrPinE pv y.1) (edgeBirths ξ.2.1) *
                schurWeight v (edgeFullTgt D y.1 (ghostTgt y.2 c) ξ)) := by
          refine (Fintype.sum_prod_type _).trans (Finset.sum_congr rfl fun c _ => ?_)
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun ξ _ => ?_
          have hVt : V (stepTgt D Bc y (c, ξ)) =
              Cst (y.1 + 1) * schurWeight v (edgeFullTgt D y.1 (ghostTgt y.2 c) ξ) := hV _
          rw [hVt]
          show hrIndG (hrPinG pv y.1) c * |ghostCoef D y.1 y.2 c| *
              (‖edgeFullCoef D (fun _ => 1) θ y.1 (ghostTgt y.2 c) ξ‖ *
                hrIndE (hrPinE pv y.1) (edgeBirths ξ.2.1)) *
              (Cst (y.1 + 1) * schurWeight v (edgeFullTgt D y.1 (ghostTgt y.2 c) ξ)) =
            hrIndG (hrPinG pv y.1) c * |ghostCoef D y.1 y.2 c| *
              (Cst (y.1 + 1) * (‖edgeFullCoef D (fun _ => 1) θ y.1 (ghostTgt y.2 c) ξ‖ *
                hrIndE (hrPinE pv y.1) (edgeBirths ξ.2.1) *
                schurWeight v (edgeFullTgt D y.1 (ghostTgt y.2 c) ξ)))
          ring
      _ ≤ ∑ c : GhostChoice 𝒢 Bc, (hrIndG (hrPinG pv y.1) c * |ghostCoef D y.1 y.2 c|) *
            (Cst (y.1 + 1) * (RE y.1 * schurWeight v (ghostTgt y.2 c))) :=
          Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hE y.1 hy (ghostTgt y.2 c)) hC0)
            (mul_nonneg (hrIndG_nonneg _ _) (abs_nonneg _))
      _ = Cst (y.1 + 1) * RE y.1 * ∑ c : GhostChoice 𝒢 Bc,
            hrIndG (hrPinG pv y.1) c * |ghostCoef D y.1 y.2 c| *
              schurWeight v (ghostTgt y.2 c) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => by ring
      _ ≤ Cst (y.1 + 1) * RE y.1 * (RG y.1 * schurWeight v y.2) :=
          mul_le_mul_of_nonneg_left (hG y.1 hy.le y.2) (mul_nonneg hC0 (hRE _))
      _ = V y := by
          rw [hV y, hCstStep y.1 hy]
          ring
  -- the last visit operation
  have hlast : ∀ y : ℕ × MState 𝒢 J ℓ Bc, y.1 = D.n → φ y ≤ V y := by
    rintro ⟨i, s⟩ hy
    have hi : i = D.n := hy
    subst hi
    have e1 : V (D.n, s) = RG D.n * schurWeight v s := by
      have h1 : V (D.n, s) = Cst D.n * schurWeight v s := hV _
      rw [h1, hCstLast]
    rw [hφ, e1]
    refine le_trans (Finset.sum_le_sum fun c _ => ?_) (hG D.n le_rfl s)
    show hrIndG (hrPinG pv D.n) c * |ghostCoef D D.n s c| *
        ‖emptyVec 𝒢 J ℓ Bc (ghostTgt s c)‖ ≤
      hrIndG (hrPinG pv D.n) c * |ghostCoef D D.n s c| * schurWeight v (ghostTgt s c)
    exact mul_le_mul_of_nonneg_left (tail_emptyVec_le hv _)
      (mul_nonneg (hrIndG_nonneg _ _) (abs_nonneg _))
  have hwalk := rWalk_sum_le (hrK D Bc θ pv) (stepTgt D Bc) φ V (fun y => y.1) D.n
    (hrK_nonneg D Bc θ pv) (fun _ _ => rfl) hrow hlast D.n
  -- one initial datum
  have hinit : ∀ a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
      ∑ w : Fin D.n → GhostChoice 𝒢 Bc × EdgeFullChoice D Bc, ∑ c : GhostChoice 𝒢 Bc,
          hrIndI (hrPinI pv) a.2.2 * |memWeight 𝒢 D.q D.n (initState a Bc)| *
            (rCoef (hrK D Bc θ pv) (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w) *
              hrLast D Bc pv c
                (walkEnd (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w))) ≤
        hrIndI (hrPinI pv) a.2.2 * memWeight 𝒢 D.q D.n (initState a Bc) * Cst 0 := by
    intro a
    have h0 := hwalk ((0 : ℕ), initState a Bc) (Nat.zero_add _)
    have hw : schurWeight v (initState (𝒢 := 𝒢) (J := J) (ℓ := ℓ) a Bc) = 1 := by
      have h00 : memTotal (initState (𝒢 := 𝒢) (J := J) (ℓ := ℓ) a Bc) = 0 :=
        Finset.sum_eq_zero fun g _ => rfl
      unfold schurWeight
      rw [h00, pow_zero]
    have hV0 : V ((0 : ℕ), initState a Bc) = Cst 0 := by
      have h1 : V ((0 : ℕ), initState a Bc) =
          Cst 0 * schurWeight v (initState (𝒢 := 𝒢) (J := J) (ℓ := ℓ) a Bc) := hV _
      rw [h1, hw, mul_one]
    rw [abs_of_nonneg (hm _)]
    calc ∑ w : Fin D.n → GhostChoice 𝒢 Bc × EdgeFullChoice D Bc, ∑ c : GhostChoice 𝒢 Bc,
          hrIndI (hrPinI pv) a.2.2 * memWeight 𝒢 D.q D.n (initState a Bc) *
            (rCoef (hrK D Bc θ pv) (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w) *
              hrLast D Bc pv c
                (walkEnd (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w)))
        = hrIndI (hrPinI pv) a.2.2 * memWeight 𝒢 D.q D.n (initState a Bc) *
            ∑ w : Fin D.n → GhostChoice 𝒢 Bc × EdgeFullChoice D Bc,
              rCoef (hrK D Bc θ pv) (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w) *
                φ (walkEnd (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [hφ, Finset.mul_sum, Finset.mul_sum]
      _ ≤ hrIndI (hrPinI pv) a.2.2 * memWeight 𝒢 D.q D.n (initState a Bc) *
            V ((0 : ℕ), initState a Bc) :=
          mul_le_mul_of_nonneg_left h0 (mul_nonneg (hrIndI_nonneg _ _) (hm _))
      _ = hrIndI (hrPinI pv) a.2.2 * memWeight 𝒢 D.q D.n (initState a Bc) * Cst 0 := by
          rw [hV0]
  -- the histories are the initial data, the words and the last choices
  have hsum : ∑ h : History D Bc,
        hrIndI (hrPinI pv) h.xb₀ * |memWeight 𝒢 D.q D.n h.init| *
          (rCoef (hrK D Bc θ pv) (stepTgt D Bc) ((0 : ℕ), h.init)
              (List.ofFn fun i : Fin D.n => (h.ghost i.castSucc, h.edge i)) *
            hrLast D Bc pv (h.ghost (Fin.last D.n))
              (walkEnd (stepTgt D Bc) ((0 : ℕ), h.init)
                (List.ofFn fun i : Fin D.n => (h.ghost i.castSucc, h.edge i)))) =
      ∑ a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
        ∑ w : Fin D.n → GhostChoice 𝒢 Bc × EdgeFullChoice D Bc, ∑ c : GhostChoice 𝒢 Bc,
          hrIndI (hrPinI pv) a.2.2 * |memWeight 𝒢 D.q D.n (initState a Bc)| *
            (rCoef (hrK D Bc θ pv) (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w) *
              hrLast D Bc pv c
                (walkEnd (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w))) :=
    sum_equiv_triple_real (histWalkEquiv D Bc) (fun a w c =>
      hrIndI (hrPinI pv) a.2.2 * |memWeight 𝒢 D.q D.n (initState a Bc)| *
        (rCoef (hrK D Bc θ pv) (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w) *
          hrLast D Bc pv c
            (walkEnd (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w))))
  calc ∑ h : History D Bc, (if HrPinned pv h.birth then ‖h.weight θ‖ else 0)
      ≤ ∑ h : History D Bc,
          hrIndI (hrPinI pv) h.xb₀ * |memWeight 𝒢 D.q D.n h.init| *
            (rCoef (hrK D Bc θ pv) (stepTgt D Bc) ((0 : ℕ), h.init)
                (List.ofFn fun i : Fin D.n => (h.ghost i.castSucc, h.edge i)) *
              hrLast D Bc pv (h.ghost (Fin.last D.n))
                (walkEnd (stepTgt D Bc) ((0 : ℕ), h.init)
                  (List.ofFn fun i : Fin D.n => (h.ghost i.castSucc, h.edge i)))) :=
        Finset.sum_le_sum fun h _ => History.hr_term_le D Bc θ pv h
    _ = ∑ a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
          ∑ w : Fin D.n → GhostChoice 𝒢 Bc × EdgeFullChoice D Bc, ∑ c : GhostChoice 𝒢 Bc,
            hrIndI (hrPinI pv) a.2.2 * |memWeight 𝒢 D.q D.n (initState a Bc)| *
              (rCoef (hrK D Bc θ pv) (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w) *
                hrLast D Bc pv c
                  (walkEnd (stepTgt D Bc) ((0 : ℕ), initState a Bc) (List.ofFn w))) := hsum
    _ ≤ ∑ a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
          hrIndI (hrPinI pv) a.2.2 * memWeight 𝒢 D.q D.n (initState a Bc) * Cst 0 :=
        Finset.sum_le_sum fun a _ => hinit a
    _ = (∑ a : ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
          hrIndI (hrPinI pv) a.2.2 * memWeight 𝒢 D.q D.n (initState a Bc)) * Cst 0 :=
        (Finset.sum_mul _ _ _).symm
    _ ≤ K₀ * Cst 0 := mul_le_mul_of_nonneg_right hI (hCst0 0)
    _ = K₀ * ((∏ i ∈ Finset.range D.n, (RG i * RE i)) * RG D.n) := by
        rw [hCst 0, Finset.range_eq_Ico]

end HrPath

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
