module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.EdgeAbsColMaj
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The weighted column bounds of the absolute edge

Source: `verification/stage7-sources/S-02.tex`, lines 704–756 and 788–794
(`[S-02:0704–0756, 0788–0794]`): the column half of [S] Lemma 3.8.

"Multiplying over groups, averaging permutations and free labels, and summing (eq:pattern-mass)
proves the row bound. For the column, use (eq:edge-joint-memory), (eq:edge-factorial-reversal) in
reverse. … This proves the column bound." [S-02:0784–0793]

The column condition is `∫ w · (|ℰ_i| f) dm ≤ C ∫ w · f dm` for nonnegative `f` which are
symmetric in the particle indices (`ColBound`), `m` the measure of `ℋ` and `w = v^{j_tot}`.

* `edgeAbs_col_fixed_pattern` — **fixed pattern `ν` and fixed free labels `r`**: the column
  inequality for the row transitions with these `ν`, `r`, with the constant
  `P(r) · sup |K_ν| · (∏_{g ∈ 𝒮} C_𝒮)(∏_{g ∈ ℬ} C_ℬ)`. The sources are reorganized by their target
  lists (`edgeAbs_sum_coord`), and each fibre is `edgeAbs_col_fiber`.
* `edgeAbs_col_choice` — the row transition between the two symmetrizations: the sum over the
  free labels (total probability one) and the patterns ((eq:pattern-mass)).
* `l38_memWeight_permLists`, `l38_permListsEquiv` — the measure of `ℋ` is invariant under the
  permutations of the slots of the active lists.
* `edgeAbs_colBound` — **the column half of `EdgeRowCol`**: the two averages over the slot
  permutations.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-- A weighted sum of double sums, with the double sum outside. -/
theorem l38_sum_swap3 {α β : Type*} {γ : β → Type*} [Fintype α] [Fintype β]
    [∀ b, Fintype (γ b)] (W : α → ℝ) (X : α → (b : β) → γ b → ℝ) :
    ∑ a, W a * ∑ b, ∑ c : γ b, X a b c = ∑ b, ∑ c : γ b, ∑ a, W a * X a b c := by
  have h1 : ∀ a, W a * ∑ b, ∑ c : γ b, X a b c = ∑ b, ∑ c : γ b, W a * X a b c := by
    intro a
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => Finset.mul_sum _ _ _
  rw [Finset.sum_congr rfl fun a _ => h1 a, Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_comm

section Edge

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {N : Type}

/-! ### Sources and targets by their target lists -/

/-- The coordinates of a pair (source state, components of a choice other than the pattern and the
free labels): the target lists, the residues, the small source list, and the source data of the
big groups. -/
abbrev EdgeAbsCoord (𝒢 : GroupFamily S B) (J ℓ Bc : ℕ) : Type :=
  (LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ) × ResVec (smallPrimes 𝒢) ×
    LabelList 𝒢.small J ℓ × ((g : B) → EdgeAbsSrc 𝒢 J ℓ Bc g)

/-- A source state and the components of a choice, by their coordinates. -/
def edgeAbsCoordEquiv :
    MState 𝒢 J ℓ Bc × EdgeAbsTail 𝒢 J ℓ Bc ≃ EdgeAbsCoord 𝒢 J ℓ Bc where
  toFun p := ((p.2.2.2.1, p.2.2.2.2), p.1.y, p.1.xs,
    fun g => (p.2.1 g, p.1.xb g, p.1.mem g, p.2.2.1 g))
  invFun w := (⟨w.2.1, w.2.2.1, fun g => (w.2.2.2 g).2.1, fun g => (w.2.2.2 g).2.2.1⟩,
    (fun g => (w.2.2.2 g).1, fun g => (w.2.2.2 g).2.2.2, w.1.1, w.1.2))
  left_inv p := by
    obtain ⟨⟨y, xs, xb, mem⟩, st, pm, a, b⟩ := p
    rfl
  right_inv w := by
    obtain ⟨⟨a, b⟩, y, xs, X⟩ := w
    rfl

/-- A memory state by its lists, its residues and its memories. -/
def edgeAbsTgtEquiv : MState 𝒢 J ℓ Bc ≃
    (LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ) × ResVec (smallPrimes 𝒢) ×
      ((g : B) → Mem 𝒢 Bc g) where
  toFun s := ((s.xs, s.xb), s.y, s.mem)
  invFun w := ⟨w.2.1, w.1.1, w.1.2, w.2.2⟩
  left_inv s := by
    obtain ⟨y, xs, xb, mem⟩ := s
    rfl
  right_inv w := by
    obtain ⟨⟨a, b⟩, y, mem⟩ := w
    rfl

/-- **The sources and the choices, organized by the target lists**: a sum over the source states
and the components of a choice is a sum over the target lists, the residues, the small source
lists and the source data of the big groups. -/
theorem edgeAbs_sum_coord (G : MState 𝒢 J ℓ Bc → EdgeAbsTail 𝒢 J ℓ Bc → ℝ) :
    ∑ s, ∑ t, G s t =
      ∑ ab : LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ, ∑ y : ResVec (smallPrimes 𝒢),
        ∑ xs : LabelList 𝒢.small J ℓ, ∑ X : (g : B) → EdgeAbsSrc 𝒢 J ℓ Bc g,
          G ⟨y, xs, fun g => (X g).2.1, fun g => (X g).2.2.1⟩
            (fun g => (X g).1, fun g => (X g).2.2.2, ab.1, ab.2) := by
  let i1 : Fintype (LabelList 𝒢.small J ℓ) := inferInstance
  let i2 : Fintype (LabelList 𝒢.big J ℓ) := inferInstance
  let i3 : Fintype (ResVec (smallPrimes 𝒢)) := inferInstance
  let i4 : Fintype ((g : B) → EdgeAbsSrc 𝒢 J ℓ Bc g) := inferInstance
  have h1 : ∑ s, ∑ t, G s t =
      ∑ p : MState 𝒢 J ℓ Bc × EdgeAbsTail 𝒢 J ℓ Bc, G p.1 p.2 :=
    (Fintype.sum_prod_type' G).symm
  have h2 : ∑ p : MState 𝒢 J ℓ Bc × EdgeAbsTail 𝒢 J ℓ Bc, G p.1 p.2 =
      ∑ w : EdgeAbsCoord 𝒢 J ℓ Bc,
        G (edgeAbsCoordEquiv.symm w).1 (edgeAbsCoordEquiv.symm w).2 :=
    (Equiv.sum_comp edgeAbsCoordEquiv.symm
      (fun p : MState 𝒢 J ℓ Bc × EdgeAbsTail 𝒢 J ℓ Bc => G p.1 p.2)).symm
  rw [h1, h2]
  refine (Fintype.sum_prod_type _).trans (Finset.sum_congr rfl fun ab _ => ?_)
  refine (Fintype.sum_prod_type _).trans (Finset.sum_congr rfl fun y _ => ?_)
  exact Fintype.sum_prod_type _

/-- A sum over the target lists, the residues and the memories is a sum over the memory
states. -/
theorem edgeAbs_sum_tgt (φ : MState 𝒢 J ℓ Bc → ℝ) :
    ∑ ab : LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ, ∑ y : ResVec (smallPrimes 𝒢),
        ∑ mem : (g : B) → Mem 𝒢 Bc g, φ ⟨y, ab.1, ab.2, mem⟩ = ∑ s, φ s := by
  have h1 : ∑ w : (LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ) × ResVec (smallPrimes 𝒢) ×
        ((g : B) → Mem 𝒢 Bc g), φ (edgeAbsTgtEquiv.symm w) =
      ∑ ab : LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ, ∑ y : ResVec (smallPrimes 𝒢),
        ∑ mem : (g : B) → Mem 𝒢 Bc g, φ ⟨y, ab.1, ab.2, mem⟩ := by
    refine (Fintype.sum_prod_type _).trans (Finset.sum_congr rfl fun ab _ => ?_)
    exact Fintype.sum_prod_type _
  exact h1.symm.trans (Equiv.sum_comp edgeAbsTgtEquiv.symm φ)

/-! ### Fixed pattern and free labels -/

/-- **The weighted column bound of the absolute edge for a fixed pattern and fixed free labels**
[S-02:0704–0756, 0788–0794]: for every nonnegative `f` which is symmetric in the particle
indices,

`∫ w(s) ∑_{stores, promotions, target lists} |coef(s → t)| f(t) dm(s)
  ≤ P(r) · sup |K_ν| · (∏_{g ∈ 𝒮} C_𝒮)(∏_{g ∈ ℬ} C_ℬ) · ∫ w f dm`,

`m` the measure of `ℋ`, `w = v^{j_tot}`. -/
theorem edgeAbs_col_fixed_pattern (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) {v vMinus Mmax : ℝ}
    {T : ℕ} (hq0 : 0 < D.q) (hq1 : D.q < 1) (hρ0 : 0 < D.ρ) (hρ1 : D.ρ < 1) (hv : 1 ≤ v)
    (hvm : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p)
    (hM : ∀ g, ∑ p : {p : ℕ // p ∈ 𝒢.big g}, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax)
    (hT : 0 < T) (hℓT : ℓ ≤ T) (ν : N) (hC : ∀ g, ℓ + ((D.fam ν).C g).card ≤ T)
    (r : AuxList 𝒢.big (D.fam ν).C) (f : MState 𝒢 J ℓ Bc → ℝ) (hf0 : ∀ s, 0 ≤ f s)
    (hfsym : MemSymmetric f) :
    ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
        ∑ t : EdgeAbsTail 𝒢 J ℓ Bc,
          ‖edgeCoef D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t)‖ *
            f (edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t)) ≤
      auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) *
          ((∏ _g : S, Schur.groupConst vMinus D.q T) *
            (∏ _g : B, edgeAbsColConst vMinus D.ρ v Mmax T)) *
        ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s * f s := by
  have hv0 : 0 ≤ v := zero_le_one.trans hv
  have haux : 0 ≤ auxWeight 𝒢.big (D.fam ν).C r := Schur.auxWeight_nonneg _ _ _
  have hsup : (0 : ℝ) ≤ ((D.fam ν).supNorm : ℝ) := NNReal.coe_nonneg _
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (∏ _g : S, Schur.groupConst vMinus D.q T) *
      (∏ _g : B, edgeAbsColConst vMinus D.ρ v Mmax T) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ,
      A = auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact mul_nonneg haux hsup
  rw [← hK, ← hA]
  obtain ⟨Mj, hMj⟩ : ∃ Mj : MState 𝒢 J ℓ Bc → EdgeAbsTail 𝒢 J ℓ Bc → ℝ, ∀ s t, Mj s t =
      edgeAbsColMaj 𝒢 D.q D.ρ v D.n (D.fam ν).C f (edgeAbsStepT D i ν r t.2.2.1 t.2.2.2)
        t.2.2.1 t.2.2.2 s.y s.xs (fun g => (t.1 g, s.xb g, s.mem g, t.2.1 g)) :=
    ⟨_, fun _ _ => rfl⟩
  -- every coefficient is at most its majorant
  have h1 : ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
        ∑ t : EdgeAbsTail 𝒢 J ℓ Bc,
          ‖edgeCoef D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t)‖ *
            f (edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t)) ≤
      ∑ s : MState 𝒢 J ℓ Bc, ∑ t : EdgeAbsTail 𝒢 J ℓ Bc, A * Mj s t := by
    refine Finset.sum_le_sum fun s _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun t _ => ?_
    rw [hMj, hA]
    exact edgeAbs_col_pointwise D θ i hq0 hρ0 hρ1.le hv0 hν f hf0 s ν r t
  -- the sources by their target lists
  have h2 : ∑ s : MState 𝒢 J ℓ Bc, ∑ t : EdgeAbsTail 𝒢 J ℓ Bc, A * Mj s t =
      A * ∑ ab : LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
        ∑ y : ResVec (smallPrimes 𝒢), ∑ xs : LabelList 𝒢.small J ℓ,
          ∑ X : (g : B) → EdgeAbsSrc 𝒢 J ℓ Bc g,
            edgeAbsColMaj 𝒢 D.q D.ρ v D.n (D.fam ν).C f (edgeAbsStepT D i ν r ab.1 ab.2)
              ab.1 ab.2 y xs X := by
    have ha : ∑ s : MState 𝒢 J ℓ Bc, ∑ t : EdgeAbsTail 𝒢 J ℓ Bc, A * Mj s t =
        A * ∑ s : MState 𝒢 J ℓ Bc, ∑ t : EdgeAbsTail 𝒢 J ℓ Bc, Mj s t := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => (Finset.mul_sum _ _ _).symm
    rw [ha, edgeAbs_sum_coord Mj]
    refine congrArg (fun t => A * t) (Finset.sum_congr rfl fun ab _ =>
      Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun xs _ =>
        Finset.sum_congr rfl fun X _ => ?_)
    exact hMj _ _
  -- every fibre
  have h3 : ∀ ab : LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
      ∑ y : ResVec (smallPrimes 𝒢), ∑ xs : LabelList 𝒢.small J ℓ,
          ∑ X : (g : B) → EdgeAbsSrc 𝒢 J ℓ Bc g,
            edgeAbsColMaj 𝒢 D.q D.ρ v D.n (D.fam ν).C f (edgeAbsStepT D i ν r ab.1 ab.2)
              ab.1 ab.2 y xs X ≤
        K * ∑ y' : ResVec (smallPrimes 𝒢), ∑ mem' : (g : B) → Mem 𝒢 Bc g,
          memWeight 𝒢 D.q D.n (⟨y', ab.1, ab.2, mem'⟩ : MState 𝒢 J ℓ Bc) *
            schurWeight v (⟨y', ab.1, ab.2, mem'⟩ : MState 𝒢 J ℓ Bc) *
            f ⟨y', ab.1, ab.2, mem'⟩ := by
    intro ab
    rw [hK]
    exact edgeAbs_col_fiber 𝒢 D.n hq0 hq1 hρ0 hρ1 hv hvm hVS hVB hν hM hT hℓT (D.fam ν).C hC f
      hf0 hfsym _ ab.1 ab.2
  have h4 : ∑ ab : LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
        K * ∑ y' : ResVec (smallPrimes 𝒢), ∑ mem' : (g : B) → Mem 𝒢 Bc g,
          memWeight 𝒢 D.q D.n (⟨y', ab.1, ab.2, mem'⟩ : MState 𝒢 J ℓ Bc) *
            schurWeight v (⟨y', ab.1, ab.2, mem'⟩ : MState 𝒢 J ℓ Bc) *
            f ⟨y', ab.1, ab.2, mem'⟩ =
      K * ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s * f s := by
    rw [← Finset.mul_sum]
    exact congrArg (fun t => K * t)
      (edgeAbs_sum_tgt (fun s => memWeight 𝒢 D.q D.n s * schurWeight v s * f s))
  calc ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
        ∑ t : EdgeAbsTail 𝒢 J ℓ Bc,
          ‖edgeCoef D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t)‖ *
            f (edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t))
      ≤ ∑ s : MState 𝒢 J ℓ Bc, ∑ t : EdgeAbsTail 𝒢 J ℓ Bc, A * Mj s t := h1
    _ = A * ∑ ab : LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
          ∑ y : ResVec (smallPrimes 𝒢), ∑ xs : LabelList 𝒢.small J ℓ,
            ∑ X : (g : B) → EdgeAbsSrc 𝒢 J ℓ Bc g,
              edgeAbsColMaj 𝒢 D.q D.ρ v D.n (D.fam ν).C f (edgeAbsStepT D i ν r ab.1 ab.2)
                ab.1 ab.2 y xs X := h2
    _ ≤ A * ∑ ab : LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ,
          K * ∑ y' : ResVec (smallPrimes 𝒢), ∑ mem' : (g : B) → Mem 𝒢 Bc g,
            memWeight 𝒢 D.q D.n (⟨y', ab.1, ab.2, mem'⟩ : MState 𝒢 J ℓ Bc) *
              schurWeight v (⟨y', ab.1, ab.2, mem'⟩ : MState 𝒢 J ℓ Bc) *
              f ⟨y', ab.1, ab.2, mem'⟩ :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ab _ => h3 ab) hA0
    _ = A * (K * ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s * f s) := by
        rw [h4]
    _ = A * K * ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s * f s :=
        (mul_assoc _ _ _).symm

/-! ### The row transition between the two symmetrizations -/

/-- **The weighted column bound of the row transition of an edge between the two
symmetrizations**: "averaging permutations and free labels, and summing (eq:pattern-mass)"
[S-02:0784–0786], here for the column. -/
theorem edgeAbs_col_choice [Fintype N] (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ)
    {v vMinus Mmax : ℝ} {T : ℕ} (hq0 : 0 < D.q) (hq1 : D.q < 1) (hρ0 : 0 < D.ρ)
    (hρ1 : D.ρ < 1) (hv : 1 ≤ v) (hvm : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hlaw : ∀ g, ∑ p ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) p = 1)
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p)
    (hM : ∀ g, ∑ p : {p : ℕ // p ∈ 𝒢.big g}, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax)
    (hT : 0 < T) (hℓT : ℓ ≤ T) (hC : ∀ ν g, ℓ + ((D.fam ν).C g).card ≤ T)
    (f : MState 𝒢 J ℓ Bc → ℝ) (hf0 : ∀ s, 0 ≤ f s) (hfsym : MemSymmetric f) :
    ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
        ∑ c : EdgeChoice 𝒢 D.fam Bc, ‖edgeCoef D θ i s c‖ * f (edgeTgt D i s c) ≤
      patternMass D.fam *
          ((∏ _g : S, Schur.groupConst vMinus D.q T) *
            (∏ _g : B, edgeAbsColConst vMinus D.ρ v Mmax T)) *
        ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s * f s := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (∏ _g : S, Schur.groupConst vMinus D.q T) *
      (∏ _g : B, edgeAbsColConst vMinus D.ρ v Mmax T) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ,
      R = ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s * f s := ⟨_, rfl⟩
  rw [← hK, ← hR]
  have e1 : ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
        ∑ c : EdgeChoice 𝒢 D.fam Bc, ‖edgeCoef D θ i s c‖ * f (edgeTgt D i s c) =
      ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C, ∑ s : MState 𝒢 J ℓ Bc,
        memWeight 𝒢 D.q D.n s * schurWeight v s *
          ∑ t : EdgeAbsTail 𝒢 J ℓ Bc,
            ‖edgeCoef D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t)‖ *
              f (edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t)) :=
    (Finset.sum_congr rfl fun s _ => congrArg
      (fun t => memWeight 𝒢 D.q D.n s * schurWeight v s * t)
      (edgeAbs_sum_choice (𝔉 := D.fam) (Bc := Bc)
        (fun c => ‖edgeCoef D θ i s c‖ * f (edgeTgt D i s c)))).trans
      (l38_sum_swap3 (γ := fun ν : N => AuxList 𝒢.big (D.fam ν).C)
        (fun s : MState 𝒢 J ℓ Bc => memWeight 𝒢 D.q D.n s * schurWeight v s)
        (fun (s : MState 𝒢 J ℓ Bc) (ν : N) (r : AuxList 𝒢.big (D.fam ν).C) =>
          ∑ t : EdgeAbsTail 𝒢 J ℓ Bc,
            ‖edgeCoef D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t)‖ *
              f (edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t))))
  rw [e1]
  calc ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C, ∑ s : MState 𝒢 J ℓ Bc,
        memWeight 𝒢 D.q D.n s * schurWeight v s *
          ∑ t : EdgeAbsTail 𝒢 J ℓ Bc,
            ‖edgeCoef D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t)‖ *
              f (edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t))
      ≤ ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C,
          auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) * K * R :=
        Finset.sum_le_sum fun ν _ => Finset.sum_le_sum fun r _ => by
          rw [hK, hR]
          exact edgeAbs_col_fixed_pattern D θ i hq0 hq1 hρ0 hρ1 hv hvm hVS hVB hν hM hT hℓT ν
            (hC ν) r f hf0 hfsym
    _ = ∑ ν : N, ((D.fam ν).supNorm : ℝ) * (K * R) := by
        refine Finset.sum_congr rfl fun ν _ => ?_
        have h1 : ∑ r : AuxList 𝒢.big (D.fam ν).C,
              auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) * K * R =
            (∑ r : AuxList 𝒢.big (D.fam ν).C, auxWeight 𝒢.big (D.fam ν).C r) *
              (((D.fam ν).supNorm : ℝ) * (K * R)) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun r _ => by ring
        rw [h1, sum_auxWeight hlaw (D.fam ν).C, one_mul]
    _ = patternMass D.fam * K * R := by
        unfold patternMass
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun ν _ => by ring

/-! ### The permutations of the slots -/

omit [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- Small states are permuted by the permutations of the slots. -/
theorem l38_isSmallState_permute (σ : SlotPerms S J ℓ) (y : ResVec (smallPrimes 𝒢))
    (xs : LabelList 𝒢.small J ℓ) :
    IsSmallState 𝒢 y (permuteSlots σ xs) ↔ IsSmallState 𝒢 y xs := by
  unfold IsSmallState
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun g => (Equiv.injective_comp (σ g) (xs g)).mp (h1 g), fun g i => ?_⟩
    have h : (resModel (smallPrimes 𝒢)).hit (xs g (σ g ((σ g).symm i)) : ℕ) y :=
      h2 g ((σ g).symm i)
    rw [(σ g).apply_symm_apply i] at h
    exact h
  · rintro ⟨h1, h2⟩
    exact ⟨fun g => (Equiv.injective_comp (σ g) (xs g)).mpr (h1 g), fun g i => h2 g (σ g i)⟩

omit [Fintype S] [DecidableEq S] [DecidableEq B] in
/-- The measure of the big active lists is invariant under the permutations of the slots. -/
theorem l38_bigListMass_permute (q : ℝ) (n : ℕ) (σ : SlotPerms B J ℓ)
    (xb : LabelList 𝒢.big J ℓ) :
    bigListMass 𝒢 q n (permuteSlots σ xb) = bigListMass 𝒢 q n xb := by
  unfold bigListMass
  refine Finset.prod_congr rfl fun g _ => ?_
  exact Equiv.prod_comp (σ g) (fun i => tiltLaw (𝒢.big g) q n (xb g i))

omit [DecidableEq S] [DecidableEq B] in
/-- **The measure of `ℋ` is invariant under the permutations of the slots of the active
lists.** -/
theorem l38_memWeight_permLists (q : ℝ) (n : ℕ) (π : ListPerms S B J ℓ)
    (s : MState 𝒢 J ℓ Bc) : memWeight 𝒢 q n (s.permLists π) = memWeight 𝒢 q n s := by
  have h1 : IsSmallState 𝒢 (s.permLists π).y (s.permLists π).xs ↔ IsSmallState 𝒢 s.y s.xs :=
    l38_isSmallState_permute π.1 s.y s.xs
  have h2 : bigListMass 𝒢 q n (s.permLists π).xb = bigListMass 𝒢 q n s.xb :=
    l38_bigListMass_permute q n π.2 s.xb
  unfold memWeight
  exact ite_congr_of_iff h1
    (congrArg (fun b => haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ * b *
      memMass 𝒢 q n s.mem) h2) rfl

/-- The permutation of the slots of the active lists, as a bijection of the memory states. -/
def l38_permListsEquiv (π : ListPerms S B J ℓ) : MState 𝒢 J ℓ Bc ≃ MState 𝒢 J ℓ Bc where
  toFun s := s.permLists π
  invFun s := { s with xs := permuteSlots π.1⁻¹ s.xs, xb := permuteSlots π.2⁻¹ s.xb }
  left_inv s := by
    obtain ⟨y, xs, xb, mem⟩ := s
    have h1 : permuteSlots π.1⁻¹ (permuteSlots π.1 xs) = xs := permuteSlots_inv_cancel π.1 xs
    have h2 : permuteSlots π.2⁻¹ (permuteSlots π.2 xb) = xb := permuteSlots_inv_cancel π.2 xb
    show (⟨y, permuteSlots π.1⁻¹ (permuteSlots π.1 xs),
      permuteSlots π.2⁻¹ (permuteSlots π.2 xb), mem⟩ : MState 𝒢 J ℓ Bc) = ⟨y, xs, xb, mem⟩
    rw [h1, h2]
  right_inv s := by
    obtain ⟨y, xs, xb, mem⟩ := s
    have h1 : permuteSlots π.1 (permuteSlots π.1⁻¹ xs) = xs := permuteSlots_cancel_inv π.1 xs
    have h2 : permuteSlots π.2 (permuteSlots π.2⁻¹ xb) = xb := permuteSlots_cancel_inv π.2 xb
    show (⟨y, permuteSlots π.1 (permuteSlots π.1⁻¹ xs),
      permuteSlots π.2 (permuteSlots π.2⁻¹ xb), mem⟩ : MState 𝒢 J ℓ Bc) = ⟨y, xs, xb, mem⟩
    rw [h1, h2]

omit [Fintype B] [DecidableEq S] in
/-- A function which is symmetric in the particle indices remains so after a permutation of the
slots of the active lists. -/
theorem l38_memSymmetric_permLists {f : MState 𝒢 J ℓ Bc → ℝ} (hf : MemSymmetric f)
    (π : ListPerms S B J ℓ) : MemSymmetric fun s => f (s.permLists π) :=
  fun s g σ => hf (s.permLists π) g σ

/-- An integral against the measure of `ℋ` and the Schur weight is invariant under a permutation
of the slots of the active lists. -/
theorem l38_sum_permLists (q : ℝ) (n : ℕ) (v : ℝ) (π : ListPerms S B J ℓ)
    (G : MState 𝒢 J ℓ Bc → ℝ) :
    ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 q n s * schurWeight v s * G (s.permLists π) =
      ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 q n s * schurWeight v s * G s := by
  refine (Finset.sum_congr rfl fun s _ => ?_).trans
    (Equiv.sum_comp (l38_permListsEquiv π)
      (fun s : MState 𝒢 J ℓ Bc => memWeight 𝒢 q n s * schurWeight v s * G s))
  have hsw : schurWeight v (s.permLists π) = schurWeight v s := rfl
  show _ = memWeight 𝒢 q n (s.permLists π) * schurWeight v (s.permLists π) * G (s.permLists π)
  rw [l38_memWeight_permLists, hsw]

/-! ### The edge operation -/

/-- **The weighted column bound of the absolute edges** [S-02:0758–0762, 0788–0794], the column
half of `EdgeRowCol`: `|ℰ_i|* w ≤ C w` for `w = v^{j_tot}` on the functions which are symmetric
in the particle indices, with
`C = (∑_ν sup |K_ν|) (∏_{g ∈ 𝒮} C_𝒮) (∏_{g ∈ ℬ} C_ℬ)`. -/
theorem edgeAbs_colBound [Fintype N] (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) {v vMinus Mmax : ℝ}
    {T : ℕ} (hq0 : 0 < D.q) (hq1 : D.q < 1) (hρ0 : 0 < D.ρ) (hρ1 : D.ρ < 1) (hv : 1 ≤ v)
    (hvm : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hlaw : ∀ g, ∑ p ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) p = 1)
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p)
    (hM : ∀ g, ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax)
    (hT : 0 < T) (hℓT : ℓ ≤ T) (hC : ∀ ν g, ℓ + ((D.fam ν).C g).card ≤ T) :
    ColBound (memWeight 𝒢 D.q D.n) (schurWeight v) (fun f => MemSymmetric f)
      (fun (s : MState 𝒢 J ℓ Bc) (ξ : EdgeFullChoice D Bc) =>
        ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖) (edgeFullTgt D i)
      (patternMass D.fam *
        ((∏ _g : S, Schur.groupConst vMinus D.q T) *
          (∏ _g : B, edgeAbsColConst vMinus D.ρ v Mmax T))) := by
  intro f hf0 hfsym
  have hM' : ∀ g, ∑ p : {p : ℕ // p ∈ 𝒢.big g}, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax :=
    fun g => (le_of_eq (Finset.sum_coe_sort (𝒢.big g)
      (fun p => tiltLaw (𝒢.big g) D.q D.n p))).trans (hM g)
  obtain ⟨cd, hcd⟩ : ∃ cd : ℝ, cd = (Fintype.card (ListPerms S B J ℓ) : ℝ) := ⟨_, rfl⟩
  have hcdpos : 0 < cd := by
    rw [hcd]
    exact Nat.cast_pos.mpr Fintype.card_pos
  have hci0 : 0 ≤ cd⁻¹ := inv_nonneg.mpr hcdpos.le
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = patternMass D.fam *
      ((∏ _g : S, Schur.groupConst vMinus D.q T) *
        (∏ _g : B, edgeAbsColConst vMinus D.ρ v Mmax T)) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ,
      R = ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s * f s := ⟨_, rfl⟩
  -- fixed slot permutations
  have hπ : ∀ π₁ π₂ : ListPerms S B J ℓ,
      ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
          ∑ c : EdgeChoice 𝒢 D.fam Bc, ‖edgeCoef D θ i (s.permLists π₁) c‖ *
            f ((edgeTgt D i (s.permLists π₁) c).permLists π₂) ≤ K * R := by
    intro π₁ π₂
    have hcol : ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
          ∑ c : EdgeChoice 𝒢 D.fam Bc, ‖edgeCoef D θ i s c‖ *
            f ((edgeTgt D i s c).permLists π₂) ≤
        patternMass D.fam *
            ((∏ _g : S, Schur.groupConst vMinus D.q T) *
              (∏ _g : B, edgeAbsColConst vMinus D.ρ v Mmax T)) *
          ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
            f (s.permLists π₂) :=
      edgeAbs_col_choice D θ i hq0 hq1 hρ0 hρ1 hv hvm hVS hVB hlaw hν hM' hT hℓT hC
        (fun s => f (s.permLists π₂)) (fun s => hf0 _) (l38_memSymmetric_permLists hfsym π₂)
    have e1 := l38_sum_permLists D.q D.n v π₁
      (fun s : MState 𝒢 J ℓ Bc => ∑ c : EdgeChoice 𝒢 D.fam Bc, ‖edgeCoef D θ i s c‖ *
        f ((edgeTgt D i s c).permLists π₂))
    have e2 : ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
        f (s.permLists π₂) = R := by
      rw [hR]
      exact l38_sum_permLists D.q D.n v π₂ f
    rw [hK, ← e2]
    exact (le_of_eq e1).trans hcol
  -- one term of the edge operation
  have hterm : ∀ (s : MState 𝒢 J ℓ Bc) (π₁ : ListPerms S B J ℓ) (c : EdgeChoice 𝒢 D.fam Bc)
      (π₂ : ListPerms S B J ℓ),
      ‖edgeFullCoef D (fun _ => 1) θ i s (π₁, c, π₂)‖ * f (edgeFullTgt D i s (π₁, c, π₂)) =
        cd⁻¹ * (cd⁻¹ * (‖edgeCoef D θ i (s.permLists π₁) c‖ *
          f ((edgeTgt D i (s.permLists π₁) c).permLists π₂))) := by
    intro s π₁ c π₂
    have ht : edgeFullTgt D i s (π₁, c, π₂) = (edgeTgt D i (s.permLists π₁) c).permLists π₂ :=
      rfl
    have hn : ‖edgeFullCoef D (fun _ => 1) θ i s (π₁, c, π₂)‖ =
        cd⁻¹ * ‖edgeCoef D θ i (s.permLists π₁) c‖ * cd⁻¹ := by
      rw [hcd]
      exact norm_edgeFullCoef_one D θ i s (π₁, c, π₂)
    rw [hn, ht]
    ring
  have hξ : ∀ s : MState 𝒢 J ℓ Bc,
      ∑ ξ : EdgeFullChoice D Bc,
          ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ * f (edgeFullTgt D i s ξ) =
        ∑ π₁ : ListPerms S B J ℓ, ∑ π₂ : ListPerms S B J ℓ,
          cd⁻¹ * (cd⁻¹ * ∑ c : EdgeChoice 𝒢 D.fam Bc,
            ‖edgeCoef D θ i (s.permLists π₁) c‖ *
              f ((edgeTgt D i (s.permLists π₁) c).permLists π₂)) := by
    intro s
    refine (Fintype.sum_prod_type _).trans (Finset.sum_congr rfl fun π₁ _ => ?_)
    refine (Fintype.sum_prod_type _).trans ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun π₂ _ => ?_
    rw [Finset.sum_congr rfl fun c _ => hterm s π₁ c π₂, ← Finset.mul_sum, ← Finset.mul_sum]
  have hconst : ∑ _π₁ : ListPerms S B J ℓ, ∑ _π₂ : ListPerms S B J ℓ,
      cd⁻¹ * (cd⁻¹ * (K * R)) = K * R := by
    have hc : cd * cd⁻¹ = 1 := mul_inv_cancel₀ hcdpos.ne'
    rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, nsmul_eq_mul,
      ← hcd]
    calc cd * (cd * (cd⁻¹ * (cd⁻¹ * (K * R)))) = cd * cd⁻¹ * (cd * cd⁻¹ * (K * R)) := by ring
      _ = K * R := by rw [hc, one_mul, one_mul]
  show ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
      ∑ ξ : EdgeFullChoice D Bc,
        ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ * f (edgeFullTgt D i s ξ) ≤
    patternMass D.fam *
        ((∏ _g : S, Schur.groupConst vMinus D.q T) *
          (∏ _g : B, edgeAbsColConst vMinus D.ρ v Mmax T)) *
      ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s * f s
  rw [← hK, ← hR]
  calc ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
        ∑ ξ : EdgeFullChoice D Bc,
          ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ * f (edgeFullTgt D i s ξ)
      = ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
          ∑ π₁ : ListPerms S B J ℓ, ∑ π₂ : ListPerms S B J ℓ,
            cd⁻¹ * (cd⁻¹ * ∑ c : EdgeChoice 𝒢 D.fam Bc,
              ‖edgeCoef D θ i (s.permLists π₁) c‖ *
                f ((edgeTgt D i (s.permLists π₁) c).permLists π₂)) :=
        Finset.sum_congr rfl fun s _ =>
          congrArg (fun t => memWeight 𝒢 D.q D.n s * schurWeight v s * t) (hξ s)
    _ = ∑ π₁ : ListPerms S B J ℓ, ∑ π₂ : ListPerms S B J ℓ,
          cd⁻¹ * (cd⁻¹ * ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
            ∑ c : EdgeChoice 𝒢 D.fam Bc, ‖edgeCoef D θ i (s.permLists π₁) c‖ *
              f ((edgeTgt D i (s.permLists π₁) c).permLists π₂)) := by
        refine (l38_sum_swap3 (γ := fun _ : ListPerms S B J ℓ => ListPerms S B J ℓ)
          (fun s : MState 𝒢 J ℓ Bc => memWeight 𝒢 D.q D.n s * schurWeight v s)
          (fun (s : MState 𝒢 J ℓ Bc) (π₁ π₂ : ListPerms S B J ℓ) =>
            cd⁻¹ * (cd⁻¹ * ∑ c : EdgeChoice 𝒢 D.fam Bc,
              ‖edgeCoef D θ i (s.permLists π₁) c‖ *
                f ((edgeTgt D i (s.permLists π₁) c).permLists π₂)))).trans
          (Finset.sum_congr rfl fun π₁ _ => Finset.sum_congr rfl fun π₂ _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
    _ ≤ ∑ _π₁ : ListPerms S B J ℓ, ∑ _π₂ : ListPerms S B J ℓ, cd⁻¹ * (cd⁻¹ * (K * R)) :=
        Finset.sum_le_sum fun π₁ _ => Finset.sum_le_sum fun π₂ _ =>
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hπ π₁ π₂) hci0) hci0
    _ = K * R := hconst

end Edge

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
