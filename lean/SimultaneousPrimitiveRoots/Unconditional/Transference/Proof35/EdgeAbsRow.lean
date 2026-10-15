module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.EdgeAbsRowSums
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The weighted row bounds of the absolute edge, per configuration

Source: `verification/stage7-sources/S-02.tex`, lines 767–786 (`[S-02:0767–0786]`): the row half of
[S] Lemma 3.8, in the pointwise forms which the later statements use.

All bounds are for the kernel of the moduli of the coefficients, with an arbitrary nonnegative
weight `Φ` of the fresh births of the edge inserted, and they are stated for an arbitrary family
of groups with explicit hypotheses (`0 < q < 1`, `0 < ρ < 1`, `v ≥ 1`, `V_g ≥ v₋ > 0`, `μ̃_g ≥ 0`,
at most `T` unshared slots).

* `edgeAbs_row_fixed_pattern` — **fixed source state, fixed pattern `ν`, fixed free labels `r`**:
  the sum over the stores, the promotions and the two target lists is at most
  `P(r) · sup |K_ν| · (∏_{g ∈ 𝒮} C_𝒮) (∏_{g ∈ ℬ} C_ℬ) · M_f · v^{j_tot}`, where `M_f` bounds the
  fresh integral of `Φ`.
* `edgeAbs_row_fixed_perm` — **fixed source state** (in the edge operation: a fixed source slot
  permutation, `s = s₀.permLists π₁`): the sum over all local transition choices between the two
  symmetrizations is at most `(∑_ν sup |K_ν|) · (…) · M_f · v^{j_tot}`. This is what
  [S] Lemma 3.9 uses "conditional on every omission choice" [S-02:0873–0875].
* `edgeAbs_row_full` — the same for the whole edge operation (the two averages over the slot
  permutations).
* `edgeAbsFreshIntegral_pinned_le`, `edgeAbs_row_pinned` — **prescribed fresh target coordinates
  fixed to given values**: every pinned coordinate contributes a point mass `μ̃_g(p) ≤ μ_max` in
  the place of the total mass `μ̃_g(𝒫_g)` ("replace the total fresh mass in each constrained slot
  by its single-point bound", [S-02:1127–1129]); the constant is otherwise unchanged. The general
  form with a weight `Φ` covers values which depend on other births of the same edge ("pivots and
  dependents within one operation", [S-02:1136–1138]).
* `edgeAbs_rowBound` — the row half of `EdgeRowCol` (`Φ = 1`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

section Row

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {N : Type}

/-! ### The choices with a fixed pattern and fixed free labels -/

/-- The components of a local transition choice of an edge other than the pattern and the free
labels: the stores, the promotions, the small and the big target list. -/
abbrev EdgeAbsTail (𝒢 : GroupFamily S B) (J ℓ Bc : ℕ) : Type :=
  ((g : B) → Finset (Slot J ℓ)) × ((g : B) → Slot J ℓ → Option (Fin Bc)) ×
    LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ

/-- The local transition choice with the pattern `ν`, the free labels `r` and the other
components `t`. -/
def edgeAbsChoice {𝔉 : N → Pattern 𝒢.big J ℓ} (ν : N) (r : AuxList 𝒢.big (𝔉 ν).C)
    (t : EdgeAbsTail 𝒢 J ℓ Bc) : EdgeChoice 𝒢 𝔉 Bc :=
  ⟨ν, r, t.1, t.2.1, t.2.2.1, t.2.2.2⟩

/-- A sum over the local transition choices is a sum over the patterns, the free labels and the
other components. -/
theorem edgeAbs_sum_choice [Fintype N] {𝔉 : N → Pattern 𝒢.big J ℓ}
    (F : EdgeChoice 𝒢 𝔉 Bc → ℝ) :
    ∑ c, F c =
      ∑ ν : N, ∑ r : AuxList 𝒢.big (𝔉 ν).C, ∑ t : EdgeAbsTail 𝒢 J ℓ Bc,
        F (edgeAbsChoice ν r t) := by
  let h1 : Fintype (LabelList 𝒢.small J ℓ) := inferInstance
  let h2 : Fintype (LabelList 𝒢.big J ℓ) := inferInstance
  let h3 : Fintype ((g : B) → Slot J ℓ → Option (Fin Bc)) := inferInstance
  let h4 : Fintype ((g : B) → Finset (Slot J ℓ)) := inferInstance
  let h5 : ∀ ν : N, Fintype (AuxList 𝒢.big (𝔉 ν).C) := fun ν => inferInstance
  refine (Fintype.sum_equiv EdgeChoice.equivSigma F
    (fun t => F (EdgeChoice.equivSigma.symm t))
    (fun c => by rw [Equiv.symm_apply_apply])).trans ?_
  refine (Fintype.sum_sigma _).trans (Finset.sum_congr rfl fun ν _ => ?_)
  exact Fintype.sum_prod_type _

/-- **The step `Δ = σ_i k D` of an edge for the pattern `ν` and the free labels `r`**: it does not
depend on the other components of the choice ("fixing shared and free `D`-labels fixes `Δ`",
[S-02:0744–0746]). -/
def edgeAbsStep (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc) (ν : N)
    (r : AuxList 𝒢.big (D.fam ν).C) : ℤ :=
  edgeSign i * D.k * ((dil (D.fam ν).C ((s.xs, s.xb) : Lists 𝒢 J ℓ) r : ℕ) : ℤ)

omit [DecidableEq S] [DecidableEq B] in
theorem edgeStep_edgeAbsChoice (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc) (ν : N)
    (r : AuxList 𝒢.big (D.fam ν).C) (t : EdgeAbsTail 𝒢 J ℓ Bc) :
    edgeStep D i s (edgeAbsChoice (𝔉 := D.fam) ν r t) = edgeAbsStep D i s ν r := rfl

/-- **The constant of the row bound for one big group**:
`(2v)^T · max(1, (v₋ ρ)^{-1})^T · sup_{z ≥ 0} (z + T)^T ρ^z` (stores; promotions and output
damping, (eq:promotion-count)). It depends on `v₋`, `ρ`, `v` and the bound `T` for the number of
unshared slots only. -/
def edgeAbsRowConst (vMinus ρ v : ℝ) (T : ℕ) : ℝ :=
  (2 * v) ^ T * ((max 1 (vMinus * ρ)⁻¹) ^ T * Schur.countSup T ρ)

/-! ### Fixed pattern and free labels -/

/-- **The weighted row bound of the absolute edge for a fixed source state, a fixed pattern and
fixed free labels** [S-02:0767–0786]. For every nonnegative weight `Φ` of the fresh births whose
fresh integrals over the unshared target slots are at most `M_f`:

`∑_{stores, promotions, target lists} |coef| · Φ(births) · v^{j'_tot}
  ≤ P(r) · sup |K_ν| · (∏_{g ∈ 𝒮} C_𝒮) (∏_{g ∈ ℬ} C_ℬ) · M_f · v^{j_tot}`.

The step `Δ` is fixed by `ν` and `r`, so the sum factors: small target lists
((eq:physical-count-bound)), stores, promotions ((eq:promotion-count)), and the fresh labels,
whose factors `μ̃_g` are integrated against `Φ`. -/
theorem edgeAbs_row_fixed_pattern (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) {v vMinus : ℝ} {T : ℕ}
    (hq0 : 0 < D.q) (hq1 : D.q < 1) (hρ0 : 0 < D.ρ) (hρ1 : D.ρ < 1) (hv : 1 ≤ v)
    (hvm : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p) (hT : 0 < T) (hℓT : ℓ ≤ T)
    (ν : N) (hC : ∀ g, ℓ + ((D.fam ν).C g).card ≤ T)
    (Φ : ((g : B) → Slot J ℓ → Option ℕ) → ℝ) (hΦ0 : ∀ b, 0 ≤ Φ b) {Mf : ℝ} (hMf : 0 ≤ Mf)
    (hΦ : ∀ (F : (g : B) → Finset (Slot J ℓ)) (x₀ : LabelList 𝒢.big J ℓ),
      (∀ g, ∀ sl ∈ F g, Unshared ((D.fam ν).C g) sl) →
        edgeAbsFreshIntegral 𝒢 D.q D.n F x₀ Φ ≤ Mf)
    (s : MState 𝒢 J ℓ Bc) (r : AuxList 𝒢.big (D.fam ν).C) :
    ∑ t : EdgeAbsTail 𝒢 J ℓ Bc,
        ‖edgeCoef D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t)‖ *
          Φ (edgeBirths (edgeAbsChoice (𝔉 := D.fam) ν r t)) *
          schurWeight v (edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t)) ≤
      auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) *
        ((∏ _g : S, Schur.groupConst vMinus D.q T) *
          (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * Mf) *
        schurWeight v s := by
  have hv0 : 0 ≤ v := zero_le_one.trans hv
  have haux : 0 ≤ auxWeight 𝒢.big (D.fam ν).C r := Schur.auxWeight_nonneg _ _ _
  have hsup : (0 : ℝ) ≤ ((D.fam ν).supNorm : ℝ) := NNReal.coe_nonneg _
  have hws : 0 ≤ schurWeight v s := pow_nonneg hv0 _
  have hA0 : 0 ≤ auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) * schurWeight v s :=
    mul_nonneg (mul_nonneg haux hsup) hws
  have hMc : 0 ≤ ∏ _g : S, Schur.groupConst vMinus D.q T :=
    Finset.prod_nonneg fun _ _ => zero_le_one.trans (Schur.one_le_groupConst _ _ _)
  -- one term
  have hpt : ∀ t : EdgeAbsTail 𝒢 J ℓ Bc,
      ‖edgeCoef D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t)‖ *
          Φ (edgeBirths (edgeAbsChoice (𝔉 := D.fam) ν r t)) *
          schurWeight v (edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t)) ≤
        (auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) * schurWeight v s) *
          (edgeAbsStoreP v (D.fam ν).C t.1 *
            edgeAbsPromoP 𝒢 D.ρ (D.fam ν).C (edgeAbsStep D i s ν r) s.mem t.2.1 *
            edgeAbsSmallW 𝒢 D.q
              ((resModel (smallPrimes 𝒢)).shift (edgeAbsStep D i s ν r) s.y) s.xs t.2.2.1 *
            (edgeAbsFreshW 𝒢 D.q D.n (D.fam ν).C s.mem s.xb t.2.1 t.2.2.2 *
              Φ (edgeAbsBirths (D.fam ν).C t.2.1 t.2.2.2))) := by
    intro t
    have h1 : ‖edgeCoef D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t)‖ *
          schurWeight v (edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t)) ≤
        auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) *
          (edgeAbsSmallW 𝒢 D.q
              ((resModel (smallPrimes 𝒢)).shift (edgeAbsStep D i s ν r) s.y) s.xs t.2.2.1 *
            edgeAbsStoreP v (D.fam ν).C t.1 *
            edgeAbsPromoP 𝒢 D.ρ (D.fam ν).C (edgeAbsStep D i s ν r) s.mem t.2.1 *
            edgeAbsFreshW 𝒢 D.q D.n (D.fam ν).C s.mem s.xb t.2.1 t.2.2.2) *
          schurWeight v s :=
      edgeCoef_row_le D θ i hq0 hq1.le hρ0 hρ1.le hv hν s (edgeAbsChoice (𝔉 := D.fam) ν r t)
    have h2 : Φ (edgeBirths (edgeAbsChoice (𝔉 := D.fam) ν r t)) =
        Φ (edgeAbsBirths (D.fam ν).C t.2.1 t.2.2.2) :=
      congrArg Φ (edgeBirths_eq_abs (edgeAbsChoice (𝔉 := D.fam) ν r t))
    rw [h2]
    calc ‖edgeCoef D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t)‖ *
          Φ (edgeAbsBirths (D.fam ν).C t.2.1 t.2.2.2) *
          schurWeight v (edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t))
        = (‖edgeCoef D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t)‖ *
            schurWeight v (edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t))) *
          Φ (edgeAbsBirths (D.fam ν).C t.2.1 t.2.2.2) := by ring
      _ ≤ (auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) *
            (edgeAbsSmallW 𝒢 D.q
                ((resModel (smallPrimes 𝒢)).shift (edgeAbsStep D i s ν r) s.y) s.xs t.2.2.1 *
              edgeAbsStoreP v (D.fam ν).C t.1 *
              edgeAbsPromoP 𝒢 D.ρ (D.fam ν).C (edgeAbsStep D i s ν r) s.mem t.2.1 *
              edgeAbsFreshW 𝒢 D.q D.n (D.fam ν).C s.mem s.xb t.2.1 t.2.2.2) *
            schurWeight v s) * Φ (edgeAbsBirths (D.fam ν).C t.2.1 t.2.2.2) :=
          mul_le_mul_of_nonneg_right h1 (hΦ0 _)
      _ = _ := by ring
  -- the fresh labels
  have hd : ∀ pm : (g : B) → Slot J ℓ → Option (Fin Bc),
      ∑ xbT : LabelList 𝒢.big J ℓ,
        edgeAbsFreshW 𝒢 D.q D.n (D.fam ν).C s.mem s.xb pm xbT *
          Φ (edgeAbsBirths (D.fam ν).C pm xbT) ≤ Mf := by
    intro pm
    refine (sum_edgeAbsFreshW_le hν (D.fam ν).C s.mem s.xb pm Φ hΦ0).trans (hΦ _ _ ?_)
    intro g sl hsl
    classical
    exact (Finset.mem_filter.mp hsl).2.1
  -- the four sums
  have hsum := l38_sum_four
    (fun st : (g : B) → Finset (Slot J ℓ) => edgeAbsStoreP v (D.fam ν).C st)
    (fun pm : (g : B) → Slot J ℓ → Option (Fin Bc) =>
      edgeAbsPromoP 𝒢 D.ρ (D.fam ν).C (edgeAbsStep D i s ν r) s.mem pm)
    (fun xsT : LabelList 𝒢.small J ℓ =>
      edgeAbsSmallW 𝒢 D.q ((resModel (smallPrimes 𝒢)).shift (edgeAbsStep D i s ν r) s.y) s.xs
        xsT)
    (fun (pm : (g : B) → Slot J ℓ → Option (Fin Bc)) (xbT : LabelList 𝒢.big J ℓ) =>
      edgeAbsFreshW 𝒢 D.q D.n (D.fam ν).C s.mem s.xb pm xbT *
        Φ (edgeAbsBirths (D.fam ν).C pm xbT))
    (fun st => edgeAbsStoreP_nonneg hv0 _ st)
    (fun pm => edgeAbsPromoP_nonneg hρ0.le _ _ _ pm)
    (fun xsT => edgeAbsSmallW_nonneg hq0 _ _ xsT)
    hMc hMf
    (sum_edgeAbsStoreP_le hv (D.fam ν).C hC)
    (sum_edgeAbsPromoP_le 𝒢 hρ0 hρ1 hvm hVB (D.fam ν).C hT hC _ s.mem)
    (sum_edgeAbsSmallW_le 𝒢 hq0 hq1 hvm hVS hT hℓT _ s.xs)
    hd
  have hprod : (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) =
      (∏ _g : B, (2 * v) ^ T) *
        ∏ _g : B, ((max 1 (vMinus * D.ρ)⁻¹) ^ T * Schur.countSup T D.ρ) :=
    Finset.prod_mul_distrib
  calc ∑ t : EdgeAbsTail 𝒢 J ℓ Bc,
        ‖edgeCoef D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t)‖ *
          Φ (edgeBirths (edgeAbsChoice (𝔉 := D.fam) ν r t)) *
          schurWeight v (edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t))
      ≤ ∑ t : EdgeAbsTail 𝒢 J ℓ Bc,
          (auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) * schurWeight v s) *
            (edgeAbsStoreP v (D.fam ν).C t.1 *
              edgeAbsPromoP 𝒢 D.ρ (D.fam ν).C (edgeAbsStep D i s ν r) s.mem t.2.1 *
              edgeAbsSmallW 𝒢 D.q
                ((resModel (smallPrimes 𝒢)).shift (edgeAbsStep D i s ν r) s.y) s.xs t.2.2.1 *
              (edgeAbsFreshW 𝒢 D.q D.n (D.fam ν).C s.mem s.xb t.2.1 t.2.2.2 *
                Φ (edgeAbsBirths (D.fam ν).C t.2.1 t.2.2.2))) :=
        Finset.sum_le_sum fun t _ => hpt t
    _ = (auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) * schurWeight v s) *
          ∑ t : EdgeAbsTail 𝒢 J ℓ Bc,
            (edgeAbsStoreP v (D.fam ν).C t.1 *
              edgeAbsPromoP 𝒢 D.ρ (D.fam ν).C (edgeAbsStep D i s ν r) s.mem t.2.1 *
              edgeAbsSmallW 𝒢 D.q
                ((resModel (smallPrimes 𝒢)).shift (edgeAbsStep D i s ν r) s.y) s.xs t.2.2.1 *
              (edgeAbsFreshW 𝒢 D.q D.n (D.fam ν).C s.mem s.xb t.2.1 t.2.2.2 *
                Φ (edgeAbsBirths (D.fam ν).C t.2.1 t.2.2.2))) := (Finset.mul_sum _ _ _).symm
    _ ≤ (auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) * schurWeight v s) *
          ((∏ _g : B, (2 * v) ^ T) *
            (∏ _g : B, ((max 1 (vMinus * D.ρ)⁻¹) ^ T * Schur.countSup T D.ρ)) *
            (∏ _g : S, Schur.groupConst vMinus D.q T) * Mf) :=
        mul_le_mul_of_nonneg_left hsum hA0
    _ = auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) *
          ((∏ _g : S, Schur.groupConst vMinus D.q T) *
            (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * Mf) *
          schurWeight v s := by
        rw [hprod]
        ring

/-! ### Fixed source state -/

variable [Fintype N]

/-- **The weighted row bound of the absolute edge for a fixed source state** — in the edge
operation: for a fixed source slot permutation [S-02:0767–0786, 0873–0875]. For every
nonnegative weight `Φ` of the fresh births whose fresh integrals over the unshared target slots
of every pattern are at most `M_f`:

`∑_c |edgeCoef s c| · Φ(births c) · v^{j_tot(target)}
  ≤ (∑_ν sup |K_ν|) · (∏_{g ∈ 𝒮} C_𝒮) (∏_{g ∈ ℬ} C_ℬ) · M_f · v^{j_tot(s)}`,

the sum being over all local transition choices `c` between the two symmetrizations. "Free-label
probabilities have total mass one", and (eq:pattern-mass) is summed. -/
theorem edgeAbs_row_fixed_perm (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) {v vMinus : ℝ} {T : ℕ}
    (hq0 : 0 < D.q) (hq1 : D.q < 1) (hρ0 : 0 < D.ρ) (hρ1 : D.ρ < 1) (hv : 1 ≤ v)
    (hvm : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hlaw : ∀ g, ∑ p ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) p = 1)
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p) (hT : 0 < T) (hℓT : ℓ ≤ T)
    (hC : ∀ ν g, ℓ + ((D.fam ν).C g).card ≤ T)
    (Φ : ((g : B) → Slot J ℓ → Option ℕ) → ℝ) (hΦ0 : ∀ b, 0 ≤ Φ b) {Mf : ℝ} (hMf : 0 ≤ Mf)
    (hΦ : ∀ (ν : N) (F : (g : B) → Finset (Slot J ℓ)) (x₀ : LabelList 𝒢.big J ℓ),
      (∀ g, ∀ sl ∈ F g, Unshared ((D.fam ν).C g) sl) →
        edgeAbsFreshIntegral 𝒢 D.q D.n F x₀ Φ ≤ Mf)
    (s : MState 𝒢 J ℓ Bc) :
    ∑ c : EdgeChoice 𝒢 D.fam Bc,
        ‖edgeCoef D θ i s c‖ * Φ (edgeBirths c) * schurWeight v (edgeTgt D i s c) ≤
      patternMass D.fam *
        ((∏ _g : S, Schur.groupConst vMinus D.q T) *
          (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * Mf) *
        schurWeight v s := by
  have e := edgeAbs_sum_choice (𝔉 := D.fam) (Bc := Bc)
    (fun c => ‖edgeCoef D θ i s c‖ * Φ (edgeBirths c) * schurWeight v (edgeTgt D i s c))
  refine (le_of_eq e).trans ?_
  calc ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C, ∑ t : EdgeAbsTail 𝒢 J ℓ Bc,
        ‖edgeCoef D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t)‖ *
          Φ (edgeBirths (edgeAbsChoice (𝔉 := D.fam) ν r t)) *
          schurWeight v (edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t))
      ≤ ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C,
          auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) *
            ((∏ _g : S, Schur.groupConst vMinus D.q T) *
              (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * Mf) *
            schurWeight v s :=
        Finset.sum_le_sum fun ν _ => Finset.sum_le_sum fun r _ =>
          edgeAbs_row_fixed_pattern D θ i hq0 hq1 hρ0 hρ1 hv hvm hVS hVB hν hT hℓT ν (hC ν) Φ hΦ0
            hMf (hΦ ν) s r
    _ = ∑ ν : N, ((D.fam ν).supNorm : ℝ) *
          (((∏ _g : S, Schur.groupConst vMinus D.q T) *
            (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * Mf) *
          schurWeight v s) := by
        refine Finset.sum_congr rfl fun ν _ => ?_
        have h1 : ∑ r : AuxList 𝒢.big (D.fam ν).C,
              auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) *
                ((∏ _g : S, Schur.groupConst vMinus D.q T) *
                  (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * Mf) *
                schurWeight v s =
            (∑ r : AuxList 𝒢.big (D.fam ν).C, auxWeight 𝒢.big (D.fam ν).C r) *
              (((D.fam ν).supNorm : ℝ) *
                (((∏ _g : S, Schur.groupConst vMinus D.q T) *
                  (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * Mf) *
                schurWeight v s)) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun r _ => by ring
        rw [h1, sum_auxWeight hlaw (D.fam ν).C, one_mul]
    _ = patternMass D.fam *
          ((∏ _g : S, Schur.groupConst vMinus D.q T) *
            (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * Mf) *
          schurWeight v s := by
        unfold patternMass
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun ν _ => by ring

/-! ### The whole edge operation -/

omit [Fintype N] in
/-- The modulus of the coefficient of the edge operation: the two averages over the slot
permutations and the modulus of the coefficient at the permuted source. -/
theorem norm_edgeFullCoef_one (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (ξ : EdgeFullChoice D Bc) :
    ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ =
      (Fintype.card (ListPerms S B J ℓ) : ℝ)⁻¹ *
          ‖edgeCoef D θ i (s.permLists ξ.1) ξ.2.1‖ *
        (Fintype.card (ListPerms S B J ℓ) : ℝ)⁻¹ := by
  unfold edgeFullCoef
  rw [norm_mul, norm_mul, norm_mul, norm_inv, Complex.norm_natCast, norm_one, one_mul]

/-- **The weighted row bound of the absolute edge operation** [S-02:0767–0786] ("averaging
permutations"), with a nonnegative weight `Φ` of the fresh births:

`∑_ξ |edgeFullCoef s ξ| · Φ(births ξ) · v^{j_tot(target)}
  ≤ (∑_ν sup |K_ν|) · (∏_{g ∈ 𝒮} C_𝒮) (∏_{g ∈ ℬ} C_ℬ) · M_f · v^{j_tot(s)}`. -/
theorem edgeAbs_row_full (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) {v vMinus : ℝ} {T : ℕ}
    (hq0 : 0 < D.q) (hq1 : D.q < 1) (hρ0 : 0 < D.ρ) (hρ1 : D.ρ < 1) (hv : 1 ≤ v)
    (hvm : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hlaw : ∀ g, ∑ p ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) p = 1)
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p) (hT : 0 < T) (hℓT : ℓ ≤ T)
    (hC : ∀ ν g, ℓ + ((D.fam ν).C g).card ≤ T)
    (Φ : ((g : B) → Slot J ℓ → Option ℕ) → ℝ) (hΦ0 : ∀ b, 0 ≤ Φ b) {Mf : ℝ} (hMf : 0 ≤ Mf)
    (hΦ : ∀ (ν : N) (F : (g : B) → Finset (Slot J ℓ)) (x₀ : LabelList 𝒢.big J ℓ),
      (∀ g, ∀ sl ∈ F g, Unshared ((D.fam ν).C g) sl) →
        edgeAbsFreshIntegral 𝒢 D.q D.n F x₀ Φ ≤ Mf)
    (s : MState 𝒢 J ℓ Bc) :
    ∑ ξ : EdgeFullChoice D Bc,
        ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ * Φ (edgeBirths ξ.2.1) *
          schurWeight v (edgeFullTgt D i s ξ) ≤
      patternMass D.fam *
        ((∏ _g : S, Schur.groupConst vMinus D.q T) *
          (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * Mf) *
        schurWeight v s := by
  obtain ⟨cd, hcd⟩ : ∃ cd : ℝ, cd = (Fintype.card (ListPerms S B J ℓ) : ℝ) := ⟨_, rfl⟩
  have hcdpos : 0 < cd := by
    rw [hcd]
    exact Nat.cast_pos.mpr Fintype.card_pos
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = patternMass D.fam *
      ((∏ _g : S, Schur.groupConst vMinus D.q T) *
        (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * Mf) := ⟨_, rfl⟩
  rw [← hR]
  have hterm : ∀ ξ : EdgeFullChoice D Bc,
      ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ * Φ (edgeBirths ξ.2.1) *
          schurWeight v (edgeFullTgt D i s ξ) =
        cd⁻¹ * (cd⁻¹ * (‖edgeCoef D θ i (s.permLists ξ.1) ξ.2.1‖ * Φ (edgeBirths ξ.2.1) *
          schurWeight v (edgeTgt D i (s.permLists ξ.1) ξ.2.1))) := by
    intro ξ
    have hw : schurWeight v (edgeFullTgt D i s ξ) =
        schurWeight v (edgeTgt D i (s.permLists ξ.1) ξ.2.1) := rfl
    rw [norm_edgeFullCoef_one, hw, ← hcd]
    ring
  have hrow : ∀ π₁ : ListPerms S B J ℓ,
      ∑ c : EdgeChoice 𝒢 D.fam Bc,
          ‖edgeCoef D θ i (s.permLists π₁) c‖ * Φ (edgeBirths c) *
            schurWeight v (edgeTgt D i (s.permLists π₁) c) ≤
        R * schurWeight v s := by
    intro π₁
    rw [hR]
    exact edgeAbs_row_fixed_perm D θ i hq0 hq1 hρ0 hρ1 hv hvm hVS hVB hlaw hν hT hℓT hC Φ hΦ0
      hMf hΦ (s.permLists π₁)
  calc ∑ ξ : EdgeFullChoice D Bc,
        ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ * Φ (edgeBirths ξ.2.1) *
          schurWeight v (edgeFullTgt D i s ξ)
      = ∑ ξ : EdgeFullChoice D Bc,
          cd⁻¹ * (cd⁻¹ * (‖edgeCoef D θ i (s.permLists ξ.1) ξ.2.1‖ * Φ (edgeBirths ξ.2.1) *
            schurWeight v (edgeTgt D i (s.permLists ξ.1) ξ.2.1))) :=
        Finset.sum_congr rfl fun ξ _ => hterm ξ
    _ = ∑ π₁ : ListPerms S B J ℓ, ∑ c : EdgeChoice 𝒢 D.fam Bc, ∑ _π₂ : ListPerms S B J ℓ,
          cd⁻¹ * (cd⁻¹ * (‖edgeCoef D θ i (s.permLists π₁) c‖ * Φ (edgeBirths c) *
            schurWeight v (edgeTgt D i (s.permLists π₁) c))) := by
        refine (Fintype.sum_prod_type _).trans (Finset.sum_congr rfl fun π₁ _ => ?_)
        exact Fintype.sum_prod_type _
    _ = ∑ π₁ : ListPerms S B J ℓ, cd⁻¹ * ∑ c : EdgeChoice 𝒢 D.fam Bc,
          ‖edgeCoef D θ i (s.permLists π₁) c‖ * Φ (edgeBirths c) *
            schurWeight v (edgeTgt D i (s.permLists π₁) c) := by
        refine Finset.sum_congr rfl fun π₁ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hcd, ← mul_assoc,
          mul_inv_cancel₀ hcdpos.ne', one_mul]
    _ ≤ ∑ _π₁ : ListPerms S B J ℓ, cd⁻¹ * (R * schurWeight v s) :=
        Finset.sum_le_sum fun π₁ _ =>
          mul_le_mul_of_nonneg_left (hrow π₁) (inv_nonneg.mpr hcdpos.le)
    _ = R * schurWeight v s := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hcd, ← mul_assoc,
          mul_inv_cancel₀ hcdpos.ne', one_mul]

end Row

/-! ### Fresh integrals with pinned coordinates -/

section Pinned

variable {S B : Type} [Fintype B] [DecidableEq B] {𝒢 : GroupFamily S B} {J ℓ : ℕ}

open _root_.Classical in
/-- **The fresh integral with prescribed coordinates pinned** [S-02:1121–1133]: let `Φ ≤ 1` be a
nonnegative weight of the births which vanishes unless every slot of `Pin g` is a fresh birth
with the value `pv g sl` (`g ∈ ℬ`). Then its fresh integral over a family `F` of sets of unshared
slots is at most `μ_max^{#pinned} · ∏_{g ∈ ℬ} max(1, M_max)^T`: "constraining indicated fresh
coordinates replaces their mass factors by the same single-point bound". Here
`μ̃_g(p) ≤ μ_max` (eq:tilted-point-mass) and `μ̃_g(𝒫_g) ≤ M_max`. (No sign condition on `Φ` is
needed.) -/
theorem edgeAbsFreshIntegral_pinned_le (𝒢 : GroupFamily S B) {q : ℝ} {n : ℕ} {Mmax μmax : ℝ}
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p)
    (hM : ∀ g, ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) q n p ≤ Mmax)
    (hμ : ∀ g, ∀ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) q n p ≤ μmax) (hμ0 : 0 ≤ μmax)
    (C : B → Finset (Fin J)) {T : ℕ} (hC : ∀ g, ℓ + (C g).card ≤ T)
    (F : (g : B) → Finset (Slot J ℓ)) (x₀ : LabelList 𝒢.big J ℓ)
    (hF : ∀ g, ∀ sl ∈ F g, Unshared (C g) sl)
    (Pin : (g : B) → Finset (Slot J ℓ)) (pv : (g : B) → Slot J ℓ → ℕ)
    (Φ : ((g : B) → Slot J ℓ → Option ℕ) → ℝ) (hΦ1 : ∀ b, Φ b ≤ 1)
    (hΦpin : ∀ b, (∃ g, ∃ sl ∈ Pin g, b g sl ≠ some (pv g sl)) → Φ b = 0) :
    edgeAbsFreshIntegral 𝒢 q n F x₀ Φ ≤
      μmax ^ (∑ g, (Pin g).card) * ∏ _g : B, (max 1 Mmax) ^ T := by
  have hM1 : (1 : ℝ) ≤ max 1 Mmax := le_max_left _ _
  have hM0 : (0 : ℝ) ≤ max 1 Mmax := zero_le_one.trans hM1
  have hRHS : 0 ≤ μmax ^ (∑ g, (Pin g).card) * ∏ _g : B, (max 1 Mmax) ^ T :=
    mul_nonneg (pow_nonneg hμ0 _) (Finset.prod_nonneg fun _ _ => pow_nonneg hM0 _)
  by_cases hsub : ∀ g, Pin g ⊆ F g
  · -- the weights of the labels of one slot
    obtain ⟨ω, hω⟩ : ∃ ω : (g : B) → Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g} → ℝ, ∀ g sl p,
        ω g sl p = if sl ∈ F g then
          (if sl ∈ Pin g then (if (p : ℕ) = pv g sl then tiltLaw (𝒢.big g) q n p else 0)
            else tiltLaw (𝒢.big g) q n p)
          else (if p = x₀ g sl then 1 else 0) := ⟨_, fun _ _ _ => rfl⟩
    have hω0 : ∀ g sl p, 0 ≤ ω g sl p := by
      intro g sl p
      rw [hω]
      split_ifs
      · exact hν g _ p.2
      · exact le_rfl
      · exact hν g _ p.2
      · exact zero_le_one
      · exact le_rfl
    -- one term of the integral
    have hterm : ∀ x : LabelList 𝒢.big J ℓ,
        (if ∀ g sl, sl ∉ F g → x g sl = x₀ g sl then
          (∏ g, ∏ sl ∈ F g, tiltLaw (𝒢.big g) q n (x g sl)) *
            Φ (fun g sl => if sl ∈ F g then some (x g sl : ℕ) else none)
        else 0) ≤ ∏ g, ∏ sl, ω g sl (x g sl) := by
      intro x
      have hnn : 0 ≤ ∏ g, ∏ sl, ω g sl (x g sl) :=
        Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun sl _ => hω0 g sl _
      by_cases hag : ∀ g sl, sl ∉ F g → x g sl = x₀ g sl
      · rw [if_pos hag]
        by_cases hpin : ∀ g, ∀ sl ∈ Pin g, (x g sl : ℕ) = pv g sl
        · have hprod : ∏ g, ∏ sl, ω g sl (x g sl) =
              ∏ g, ∏ sl ∈ F g, tiltLaw (𝒢.big g) q n (x g sl) := by
            refine Finset.prod_congr rfl fun g _ => ?_
            have h1 : ∀ sl : Slot J ℓ, ω g sl (x g sl) =
                if sl ∈ F g then tiltLaw (𝒢.big g) q n (x g sl) else 1 := by
              intro sl
              rw [hω]
              by_cases hsl : sl ∈ F g
              · rw [if_pos hsl, if_pos hsl]
                by_cases hp : sl ∈ Pin g
                · rw [if_pos hp, if_pos (hpin g sl hp)]
                · rw [if_neg hp]
              · rw [if_neg hsl, if_neg hsl, if_pos (hag g sl hsl)]
            rw [Finset.prod_congr rfl fun sl _ => h1 sl, Finset.prod_ite_mem, Finset.univ_inter]
          rw [hprod]
          calc (∏ g, ∏ sl ∈ F g, tiltLaw (𝒢.big g) q n (x g sl)) *
                Φ (fun g sl => if sl ∈ F g then some (x g sl : ℕ) else none)
              ≤ (∏ g, ∏ sl ∈ F g, tiltLaw (𝒢.big g) q n (x g sl)) * 1 :=
                mul_le_mul_of_nonneg_left (hΦ1 _)
                  (Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun sl _ =>
                    hν g _ (x g sl).2)
            _ = ∏ g, ∏ sl ∈ F g, tiltLaw (𝒢.big g) q n (x g sl) := mul_one _
        · have hz : Φ (fun g sl => if sl ∈ F g then some (x g sl : ℕ) else none) = 0 := by
            refine hΦpin _ ?_
            by_contra hcon
            refine hpin fun g sl hsl => ?_
            by_contra hne
            refine hcon ⟨g, sl, hsl, ?_⟩
            show (if sl ∈ F g then some ((x g sl : ℕ)) else none) ≠ some (pv g sl)
            rw [if_pos (hsub g hsl)]
            exact fun h => hne (Option.some.inj h)
          rw [hz, mul_zero]
          exact hnn
      · rw [if_neg hag]
        exact hnn
    -- the sum of the weights of the labels of one slot
    have hslot : ∀ g sl, ∑ p : {p : ℕ // p ∈ 𝒢.big g}, ω g sl p ≤
        (if sl ∈ Pin g then μmax else 1) * (if sl ∈ F g then max 1 Mmax else 1) := by
      intro g sl
      have hMg : ∑ p : {p : ℕ // p ∈ 𝒢.big g}, tiltLaw (𝒢.big g) q n p ≤ max 1 Mmax :=
        ((Finset.sum_coe_sort (𝒢.big g) fun p => tiltLaw (𝒢.big g) q n p).trans_le (hM g)).trans
          (le_max_right _ _)
      by_cases hsl : sl ∈ F g
      · rw [if_pos hsl]
        by_cases hp : sl ∈ Pin g
        · rw [if_pos hp]
          have h1 : ∑ p : {p : ℕ // p ∈ 𝒢.big g}, ω g sl p =
              ∑ p : {p : ℕ // p ∈ 𝒢.big g},
                (if (p : ℕ) = pv g sl then tiltLaw (𝒢.big g) q n p else 0) := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [hω, if_pos hsl, if_pos hp]
          have h2 : ∑ p : {p : ℕ // p ∈ 𝒢.big g},
              (if (p : ℕ) = pv g sl then tiltLaw (𝒢.big g) q n p else 0) ≤ μmax := by
            by_cases hex : ∃ p₀ : {p : ℕ // p ∈ 𝒢.big g}, (p₀ : ℕ) = pv g sl
            · obtain ⟨p₀, hp₀⟩ := hex
              have h3 : ∑ p : {p : ℕ // p ∈ 𝒢.big g},
                  (if (p : ℕ) = pv g sl then tiltLaw (𝒢.big g) q n p else 0) =
                  if (p₀ : ℕ) = pv g sl then tiltLaw (𝒢.big g) q n p₀ else 0 :=
                Finset.sum_eq_single_of_mem
                  (f := fun p : {p : ℕ // p ∈ 𝒢.big g} =>
                    if (p : ℕ) = pv g sl then tiltLaw (𝒢.big g) q n p else 0)
                  p₀ (Finset.mem_univ _)
                  (fun p _ hp' => if_neg fun h => hp' (Subtype.ext (h.trans hp₀.symm)))
              rw [h3, if_pos hp₀]
              exact hμ g _ p₀.2
            · have h3 : ∑ p : {p : ℕ // p ∈ 𝒢.big g},
                  (if (p : ℕ) = pv g sl then tiltLaw (𝒢.big g) q n p else 0) = 0 :=
                Finset.sum_eq_zero fun p _ => if_neg fun h => hex ⟨p, h⟩
              rw [h3]
              exact hμ0
          rw [h1]
          calc ∑ p : {p : ℕ // p ∈ 𝒢.big g},
                (if (p : ℕ) = pv g sl then tiltLaw (𝒢.big g) q n p else 0) ≤ μmax := h2
            _ = μmax * 1 := (mul_one _).symm
            _ ≤ μmax * max 1 Mmax := mul_le_mul_of_nonneg_left hM1 hμ0
        · rw [if_neg hp, one_mul]
          have h1 : ∑ p : {p : ℕ // p ∈ 𝒢.big g}, ω g sl p =
              ∑ p : {p : ℕ // p ∈ 𝒢.big g}, tiltLaw (𝒢.big g) q n p := by
            refine Finset.sum_congr rfl fun p _ => ?_
            rw [hω, if_pos hsl, if_neg hp]
          rw [h1]
          exact hMg
      · have hp : sl ∉ Pin g := fun h => hsl (hsub g h)
        rw [if_neg hsl, if_neg hp, one_mul]
        have h1 : ∑ p : {p : ℕ // p ∈ 𝒢.big g}, ω g sl p =
            ∑ p : {p : ℕ // p ∈ 𝒢.big g}, (if p = x₀ g sl then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hω, if_neg hsl]
        have h2 : ∑ p : {p : ℕ // p ∈ 𝒢.big g}, (if p = x₀ g sl then (1 : ℝ) else 0) = 1 :=
          (Finset.sum_eq_single_of_mem
            (f := fun p : {p : ℕ // p ∈ 𝒢.big g} => if p = x₀ g sl then (1 : ℝ) else 0)
            (x₀ g sl) (Finset.mem_univ _) (fun p _ hp' => if_neg hp')).trans
              (if_pos rfl)
        exact (h1.trans h2).le
    -- the product over the slots of one group
    have hgroup : ∀ g, ∏ sl : Slot J ℓ,
        ((if sl ∈ Pin g then μmax else 1) * (if sl ∈ F g then max 1 Mmax else 1)) ≤
          μmax ^ (Pin g).card * (max 1 Mmax) ^ T := by
      intro g
      have hFcard : (F g).card ≤ T := by
        have h1 : F g ⊆ Finset.univ.filter fun sl : Slot J ℓ => Unshared (C g) sl := fun sl hsl =>
          Finset.mem_filter.mpr ⟨Finset.mem_univ sl, hF g sl hsl⟩
        have h2 : (Finset.univ.filter fun sl : Slot J ℓ => Unshared (C g) sl).card =
            ℓ + (C g).card := l38_card_unshared (C g)
        exact (Finset.card_le_card h1).trans (h2.le.trans (hC g))
      rw [Finset.prod_mul_distrib, Finset.prod_ite_mem, Finset.prod_ite_mem, Finset.univ_inter,
        Finset.univ_inter, Finset.prod_const, Finset.prod_const]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM1 hFcard) (pow_nonneg hμ0 _)
    have hpin0 : ∀ (g : B) (sl : Slot J ℓ), (0 : ℝ) ≤ (if sl ∈ Pin g then μmax else 1) := by
      intro g sl
      split_ifs
      · exact hμ0
      · exact zero_le_one
    have hF0 : ∀ (g : B) (sl : Slot J ℓ), (0 : ℝ) ≤ (if sl ∈ F g then max 1 Mmax else 1) := by
      intro g sl
      split_ifs
      · exact hM0
      · exact zero_le_one
    -- the integral
    have hsum : ∑ x : LabelList 𝒢.big J ℓ, ∏ g, ∏ sl, ω g sl (x g sl) =
        ∏ g : B, ∏ sl : Slot J ℓ, ∑ p : {p : ℕ // p ∈ 𝒢.big g}, ω g sl p := by
      have h1 : ∑ x : LabelList 𝒢.big J ℓ, ∏ g, ∏ sl, ω g sl (x g sl) =
          ∏ g : B, ∑ w : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}, ∏ sl, ω g sl (w sl) :=
        (Fintype.prod_sum fun (g : B) (w : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) =>
          ∏ sl, ω g sl (w sl)).symm
      rw [h1]
      refine Finset.prod_congr rfl fun g _ => ?_
      exact (Fintype.prod_sum fun (sl : Slot J ℓ) (p : {p : ℕ // p ∈ 𝒢.big g}) =>
        ω g sl p).symm
    unfold edgeAbsFreshIntegral
    calc ∑ x : LabelList 𝒢.big J ℓ,
          (if ∀ g sl, sl ∉ F g → x g sl = x₀ g sl then
            (∏ g, ∏ sl ∈ F g, tiltLaw (𝒢.big g) q n (x g sl)) *
              Φ (fun g sl => if sl ∈ F g then some (x g sl : ℕ) else none)
          else 0)
        ≤ ∑ x : LabelList 𝒢.big J ℓ, ∏ g, ∏ sl, ω g sl (x g sl) :=
          Finset.sum_le_sum fun x _ => hterm x
      _ = ∏ g : B, ∏ sl : Slot J ℓ, ∑ p : {p : ℕ // p ∈ 𝒢.big g}, ω g sl p := hsum
      _ ≤ ∏ g : B, ∏ sl : Slot J ℓ,
            ((if sl ∈ Pin g then μmax else 1) * (if sl ∈ F g then max 1 Mmax else 1)) :=
          Finset.prod_le_prod
            (fun g _ => Finset.prod_nonneg fun sl _ => Finset.sum_nonneg fun p _ => hω0 g sl p)
            (fun g _ => Finset.prod_le_prod
              (fun sl _ => Finset.sum_nonneg fun p _ => hω0 g sl p) (fun sl _ => hslot g sl))
      _ ≤ ∏ g : B, (μmax ^ (Pin g).card * (max 1 Mmax) ^ T) :=
          Finset.prod_le_prod
            (fun g _ => Finset.prod_nonneg fun sl _ => mul_nonneg (hpin0 g sl) (hF0 g sl))
            (fun g _ => hgroup g)
      _ = μmax ^ (∑ g, (Pin g).card) * ∏ _g : B, (max 1 Mmax) ^ T := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  · -- a pinned slot is not fresh: the weight vanishes identically
    have hz : edgeAbsFreshIntegral 𝒢 q n F x₀ Φ = 0 := by
      unfold edgeAbsFreshIntegral
      refine Finset.sum_eq_zero fun x _ => ?_
      have hΦz : Φ (fun g sl => if sl ∈ F g then some (x g sl : ℕ) else none) = 0 := by
        refine hΦpin _ ?_
        by_contra hcon
        refine hsub fun g sl hsl => ?_
        by_contra hnF
        refine hcon ⟨g, sl, hsl, ?_⟩
        show (if sl ∈ F g then some ((x g sl : ℕ)) else none) ≠ some (pv g sl)
        rw [if_neg hnF]
        exact fun h => Option.some_ne_none _ h.symm
      rw [hΦz, mul_zero]
      exact ite_self 0
    rw [hz]
    exact hRHS

/-- The fresh integral of the weight `1` is at most `∏_{g ∈ ℬ} max(1, M_max)^T`: "fresh
integrations have mass `μ̃_g(𝒫_g)^{t_g - a_g} ≤ 2^{t_g}`" [S-02:0779–0781]. -/
theorem edgeAbsFreshIntegral_one_le (𝒢 : GroupFamily S B) {q : ℝ} {n : ℕ} {Mmax : ℝ}
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p)
    (hM : ∀ g, ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) q n p ≤ Mmax)
    (C : B → Finset (Fin J)) {T : ℕ} (hC : ∀ g, ℓ + (C g).card ≤ T)
    (F : (g : B) → Finset (Slot J ℓ)) (x₀ : LabelList 𝒢.big J ℓ)
    (hF : ∀ g, ∀ sl ∈ F g, Unshared (C g) sl) :
    edgeAbsFreshIntegral 𝒢 q n F x₀ (fun _ => 1) ≤ ∏ _g : B, (max 1 Mmax) ^ T := by
  have hμ : ∀ g, ∀ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) q n p ≤ max 1 Mmax := fun g p hp =>
    ((Finset.single_le_sum (f := fun p => tiltLaw (𝒢.big g) q n p) (fun p hp' => hν g p hp')
      hp).trans (hM g)).trans (le_max_right _ _)
  have h := edgeAbsFreshIntegral_pinned_le 𝒢 hν hM hμ (zero_le_one.trans (le_max_left _ _)) C hC
    F x₀ hF (fun _ => ∅) (fun _ _ => 0) (fun _ => 1) (fun _ => le_rfl)
    (fun b hb => by
      obtain ⟨g, sl, hsl, _⟩ := hb
      exact absurd hsl (Finset.notMem_empty sl))
  have h0 : (∑ _g : B, (∅ : Finset (Slot J ℓ)).card) = 0 :=
    Finset.sum_eq_zero fun g _ => Finset.card_empty
  rw [h0, pow_zero, one_mul] at h
  exact h

end Pinned

/-! ### The row bound of Lemma 3.8 and the row bound with pinned fresh coordinates -/

section RowBound

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {N : Type} [Fintype N]

open _root_.Classical in
/-- **The weighted row bound of the absolute edge with prescribed fresh target coordinates fixed
to given values** [S-02:1121–1133]: the row sum over the local transition choices in which every
target slot of `Pin g` is a fresh birth with the prime value `pv g sl` is at most

`(∑_ν sup |K_ν|) · (∏_{g ∈ 𝒮} C_𝒮) (∏_{g ∈ ℬ} C_ℬ max(1, M_max)^T) · μ_max^{#pinned} · v^{j_tot}`:

each pinned coordinate replaces the total mass `μ̃_g(𝒫_g)` of its fresh integration by the point
mass bound `μ_max ≥ sup μ̃_g` of (eq:tilted-point-mass). -/
theorem edgeAbs_row_pinned (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) {v vMinus Mmax μmax : ℝ} {T : ℕ}
    (hq0 : 0 < D.q) (hq1 : D.q < 1) (hρ0 : 0 < D.ρ) (hρ1 : D.ρ < 1) (hv : 1 ≤ v)
    (hvm : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hlaw : ∀ g, ∑ p ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) p = 1)
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p)
    (hM : ∀ g, ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax)
    (hμ : ∀ g, ∀ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) D.q D.n p ≤ μmax) (hμ0 : 0 ≤ μmax)
    (hT : 0 < T) (hℓT : ℓ ≤ T) (hC : ∀ ν g, ℓ + ((D.fam ν).C g).card ≤ T)
    (Pin : (g : B) → Finset (Slot J ℓ)) (pv : (g : B) → Slot J ℓ → ℕ) (s : MState 𝒢 J ℓ Bc) :
    ∑ ξ : EdgeFullChoice D Bc,
        ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ *
          (if ∀ g, ∀ sl ∈ Pin g, edgeBirths ξ.2.1 g sl = some (pv g sl) then 1 else 0) *
          schurWeight v (edgeFullTgt D i s ξ) ≤
      patternMass D.fam *
        ((∏ _g : S, Schur.groupConst vMinus D.q T) *
          (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) *
          (μmax ^ (∑ g, (Pin g).card) * ∏ _g : B, (max 1 Mmax) ^ T)) *
        schurWeight v s := by
  have hMf : 0 ≤ μmax ^ (∑ g, (Pin g).card) * ∏ _g : B, (max 1 Mmax) ^ T :=
    mul_nonneg (pow_nonneg hμ0 _)
      (Finset.prod_nonneg fun _ _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
  have h0 : ∀ b : (g : B) → Slot J ℓ → Option ℕ,
      (0 : ℝ) ≤ (if ∀ g, ∀ sl ∈ Pin g, b g sl = some (pv g sl) then 1 else 0) := by
    intro b
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  have h1 : ∀ b : (g : B) → Slot J ℓ → Option ℕ,
      (if ∀ g, ∀ sl ∈ Pin g, b g sl = some (pv g sl) then 1 else 0) ≤ (1 : ℝ) := by
    intro b
    split_ifs
    · exact le_rfl
    · exact zero_le_one
  have hpin : ∀ b : (g : B) → Slot J ℓ → Option ℕ,
      (∃ g, ∃ sl ∈ Pin g, b g sl ≠ some (pv g sl)) →
        (if ∀ g, ∀ sl ∈ Pin g, b g sl = some (pv g sl) then (1 : ℝ) else 0) = 0 := by
    intro b hb
    obtain ⟨g, sl, hsl, hne⟩ := hb
    exact if_neg fun h => hne (h g sl hsl)
  exact edgeAbs_row_full D θ i hq0 hq1 hρ0 hρ1 hv hvm hVS hVB hlaw hν hT hℓT hC
    (fun b => if ∀ g, ∀ sl ∈ Pin g, b g sl = some (pv g sl) then 1 else 0) h0 hMf
    (fun ν F x₀ hF => edgeAbsFreshIntegral_pinned_le 𝒢 hν hM hμ hμ0 (D.fam ν).C (hC ν) F x₀ hF
      Pin pv _ h1 hpin) s

/-- **The weighted row bound of the absolute edges** [S-02:0758–0762, 0767–0786], the row half of
`EdgeRowCol`: `|ℰ_i| w ≤ R w` for `w = v^{j_tot}`, with
`R = (∑_ν sup |K_ν|) (∏_{g ∈ 𝒮} C_𝒮) (∏_{g ∈ ℬ} C_ℬ max(1, M_max)^T)`. -/
theorem edgeAbs_rowBound (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) {v vMinus Mmax : ℝ} {T : ℕ}
    (hq0 : 0 < D.q) (hq1 : D.q < 1) (hρ0 : 0 < D.ρ) (hρ1 : D.ρ < 1) (hv : 1 ≤ v)
    (hvm : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hlaw : ∀ g, ∑ p ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) p = 1)
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p)
    (hM : ∀ g, ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax)
    (hT : 0 < T) (hℓT : ℓ ≤ T) (hC : ∀ ν g, ℓ + ((D.fam ν).C g).card ≤ T) :
    RowBound (schurWeight v)
      (fun (s : MState 𝒢 J ℓ Bc) (ξ : EdgeFullChoice D Bc) =>
        ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖) (edgeFullTgt D i)
      (patternMass D.fam *
        ((∏ _g : S, Schur.groupConst vMinus D.q T) *
          (∏ _g : B, edgeAbsRowConst vMinus D.ρ v T) * ∏ _g : B, (max 1 Mmax) ^ T)) := by
  intro s
  have hMf : 0 ≤ ∏ _g : B, (max 1 Mmax) ^ T :=
    Finset.prod_nonneg fun _ _ => pow_nonneg (zero_le_one.trans (le_max_left _ _)) _
  have h := edgeAbs_row_full D θ i hq0 hq1 hρ0 hρ1 hv hvm hVS hVB hlaw hν hT hℓT hC (fun _ => 1)
    (fun _ => zero_le_one) hMf
    (fun ν F x₀ hF => edgeAbsFreshIntegral_one_le 𝒢 hν hM (D.fam ν).C (hC ν) F x₀ hF) s
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun ξ _ => ?_)) h
  rw [mul_one]

end RowBound

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
