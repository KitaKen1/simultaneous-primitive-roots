module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.RowOps
public import SimultaneousPrimitiveRoots.Unconditional.Transference.PhysicalOperator
import Mathlib.Tactic.Ring

/-!
# The path expansion of the moment `⟨u_n, (𝒜 𝒜*)^R u_n⟩`

Source: `verification/stage7-sources/S-02.tex`, lines 212–222 (`[S-02:0212–0222]`): "expand the
left side of (eq:transference-moment) into paths with `N` alternating forward and backward edges.
Fix the patterns, all endpoint permutations, the auxiliary labels, and the active lists at visits
`0, …, N`."

* `PhysChoice` — the choices of one edge: the source permutation, the pattern, the auxiliary
  labels, the lists at the next visit, the target permutation.
* `physFwdCoef`, `physFwdTgt` and `physBwdCoef`, `physBwdTgt` — the coefficient and the next state
  of a forward edge (a row transition of `𝒜`) and of a backward edge (of `𝒜*`).
* `physOp_eq_rowOp`, `physAdj_eq_rowOp` — the reviewed operators `physOp`, `physAdj` are the row
  operators with these choices.
* `physRound_eq_rowOp` — `𝒜 𝒜*` is the row operator whose choices are pairs (a forward edge, then
  a backward edge).
* `pairUnit_pow_eq_sum_walks`, `physMoment_eq_sum_walks` — **the path expansion equals the
  definition used in `physMoment`**: the moment is the real part of the sum, over the physical
  lists at the start and over all words of `R` rounds, of the mass of the start, the product of
  the coefficients along the walk, and the value of `u_n` at its end ("only return to the position
  is imposed; the last ordered list need not be the first one", [S-02:0221–0222]). The first
  lemma is the same expansion with an arbitrary final vector in place of `u_n`.
* `pairUnit_pow_congr`, `pairUnit_sum`, `pairUnit_smul` — `⟨u_n, (𝒜 𝒜*)^R G⟩` only depends on the
  values of `G` at the ends of the walks, and is linear in `G`.

Everything is for an arbitrary position model, so it applies to integer positions and to the
residue model with offsets (`tagModel`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators ComplexConjugate

noncomputable section

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

/-- **The choices of one edge of a path** [S-02:0213–0215]: the source permutation, the pattern
with its auxiliary labels and the lists at the next visit, the target permutation. -/
abbrev PhysChoice (𝒢 : GroupFamily S B) {J ℓ : ℕ} {N : Type} (𝔉 : N → Pattern 𝒢.big J ℓ) :
    Type :=
  (SlotPerms S J ℓ × SlotPerms B J ℓ) ×
    (Σ ν : N, AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ) × (SlotPerms S J ℓ × SlotPerms B J ℓ)

/-- The choices of one edge form a finite type. (A named instance: the instance found by
unfolding the nested products is larger than the default `synthInstance.maxSize`.) -/
instance physChoiceFintype (𝒢 : GroupFamily S B) {J ℓ : ℕ} {N : Type} [Fintype N]
    (𝔉 : N → Pattern 𝒢.big J ℓ) : Fintype (PhysChoice 𝒢 𝔉) := by
  haveI h1 : Fintype (SlotPerms S J ℓ × SlotPerms B J ℓ) := inferInstance
  haveI h2 : ∀ ν : N, Fintype (AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ) := fun ν => inferInstance
  haveI h3 : Fintype (Σ ν : N, AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ) := inferInstance
  exact instFintypeProd _ _

variable (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ} {N : Type} [Fintype N]

/-- The coefficient of a forward edge: the two averages over the slot permutations and the
coefficient `physCoef` of the row transition at the permuted source lists. -/
def physFwdCoef (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (s : PState 𝔭 𝒢 J ℓ)
    (ξ : PhysChoice 𝒢 𝔉) : ℂ :=
  (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℂ)⁻¹ *
    physCoef 𝔭 𝒢 q (𝔉 ξ.2.1.1) k ζ s.1 (permuteLists ξ.1 s.2) ξ.2.1.2.1 ξ.2.1.2.2 *
    (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℂ)⁻¹

/-- The state after a forward edge: the position moves by `k D`, the lists are the permuted
target lists. -/
def physFwdTgt (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (s : PState 𝔭 𝒢 J ℓ)
    (ξ : PhysChoice 𝒢 𝔉) : PState 𝔭 𝒢 J ℓ :=
  (𝔭.shift (k * dil (𝔉 ξ.2.1.1).C (permuteLists ξ.1 s.2) ξ.2.1.2.1) s.1,
    permuteLists ξ.2.2 ξ.2.1.2.2)

/-- The coefficient of a backward edge: "the adjoint moves by `-kD`, interchanges source and
target labels in the coefficient, and conjugates the multiplier" [S-02:0120–0121]. -/
def physBwdCoef (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (s : PState 𝔭 𝒢 J ℓ)
    (ξ : PhysChoice 𝒢 𝔉) : ℂ :=
  (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℂ)⁻¹ *
    conj (physCoef 𝔭 𝒢 q (𝔉 ξ.2.1.1) k ζ
      (𝔭.shift (-(k * dil (𝔉 ξ.2.1.1).C (permuteLists ξ.1 s.2) ξ.2.1.2.1)) s.1)
      ξ.2.1.2.2 ξ.2.1.2.1 (permuteLists ξ.1 s.2)) *
    (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℂ)⁻¹

/-- The state after a backward edge: the position moves by `-k D`. -/
def physBwdTgt (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (s : PState 𝔭 𝒢 J ℓ)
    (ξ : PhysChoice 𝒢 𝔉) : PState 𝔭 𝒢 J ℓ :=
  (𝔭.shift (-(k * dil (𝔉 ξ.2.1.1).C (permuteLists ξ.1 s.2) ξ.2.1.2.1)) s.1,
    permuteLists ξ.2.2 ξ.2.1.2.2)

/-- `𝒜` is the row operator of the forward edges. -/
theorem physOp_eq_rowOp (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) :
    physOp 𝔭 𝒢 q 𝔉 k ζ = rowOp (physFwdCoef 𝔭 𝒢 q 𝔉 k ζ) (physFwdTgt 𝔭 𝒢 𝔉 k) := by
  refine LinearMap.ext fun G => funext fun s => ?_
  simp only [physOp, physSym, physRow, physFwdCoef, physFwdTgt, LinearMap.comp_apply,
    LinearMap.sum_apply, Finset.sum_apply, rowOp_apply, Fintype.sum_prod_type,
    Fintype.sum_sigma, Finset.mul_sum]
  refine Finset.sum_congr rfl fun π₁ _ => Finset.sum_congr rfl fun π₂ _ =>
    Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun r _ =>
    Finset.sum_congr rfl fun x₁ _ => Finset.sum_congr rfl fun x₂ _ =>
    Finset.sum_congr rfl fun π₁' _ => Finset.sum_congr rfl fun π₂' _ => ?_
  ring_nf

/-- `𝒜*` is the row operator of the backward edges. -/
theorem physAdj_eq_rowOp (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) :
    physAdj 𝔭 𝒢 q 𝔉 k ζ = rowOp (physBwdCoef 𝔭 𝒢 q 𝔉 k ζ) (physBwdTgt 𝔭 𝒢 𝔉 k) := by
  refine LinearMap.ext fun G => funext fun s => ?_
  simp only [physAdj, physSym, physRowAdj, physBwdCoef, physBwdTgt, LinearMap.comp_apply,
    LinearMap.sum_apply, Finset.sum_apply, rowOp_apply, Fintype.sum_prod_type,
    Fintype.sum_sigma, Finset.mul_sum]
  refine Finset.sum_congr rfl fun π₁ _ => Finset.sum_congr rfl fun π₂ _ =>
    Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun r _ =>
    Finset.sum_congr rfl fun x₁ _ => Finset.sum_congr rfl fun x₂ _ =>
    Finset.sum_congr rfl fun π₁' _ => Finset.sum_congr rfl fun π₂' _ => ?_
  ring_nf

/-- The coefficient of a round: a forward edge followed by a backward edge. -/
def physRoundCoef (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (s : PState 𝔭 𝒢 J ℓ)
    (ξ : PhysChoice 𝒢 𝔉 × PhysChoice 𝒢 𝔉) : ℂ :=
  physFwdCoef 𝔭 𝒢 q 𝔉 k ζ s ξ.1 * physBwdCoef 𝔭 𝒢 q 𝔉 k ζ (physFwdTgt 𝔭 𝒢 𝔉 k s ξ.1) ξ.2

/-- The state after a round. -/
def physRoundTgt (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (s : PState 𝔭 𝒢 J ℓ)
    (ξ : PhysChoice 𝒢 𝔉 × PhysChoice 𝒢 𝔉) : PState 𝔭 𝒢 J ℓ :=
  physBwdTgt 𝔭 𝒢 𝔉 k (physFwdTgt 𝔭 𝒢 𝔉 k s ξ.1) ξ.2

/-- `𝒜 𝒜*` is the row operator of the rounds. -/
theorem physRound_eq_rowOp (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) :
    physOp 𝔭 𝒢 q 𝔉 k ζ * physAdj 𝔭 𝒢 q 𝔉 k ζ =
      rowOp (physRoundCoef 𝔭 𝒢 q 𝔉 k ζ) (physRoundTgt 𝔭 𝒢 𝔉 k) := by
  refine LinearMap.ext fun G => funext fun s => ?_
  rw [Module.End.mul_apply, physOp_eq_rowOp, physAdj_eq_rowOp, rowOp_comp_apply]
  rfl

open _root_.Classical in
/-- **The path expansion of `⟨u_n, (𝒜 𝒜*)^R G⟩`** for an arbitrary final vector `G`
[S-02:0212–0222]: the sum over the physical lists `x` at the position `n` and over all words `w`
of `R` rounds of `mass · (product of the coefficients along the walk from (n, x)) · G(end)`. -/
theorem pairUnit_pow_eq_sum_walks (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (R : ℕ)
    (n : 𝔭.Pos) (G : PState 𝔭 𝒢 J ℓ → ℂ) :
    pairUnit 𝔭 𝒢 J ℓ n (((physOp 𝔭 𝒢 q 𝔉 k ζ * physAdj 𝔭 𝒢 q 𝔉 k ζ) ^ R) G) =
      ∑ x : Lists 𝒢 J ℓ, if IsPhys 𝔭 n x then
        (stateMass 𝒢 J ℓ : ℂ) *
          ∑ w : Fin R → PhysChoice 𝒢 𝔉 × PhysChoice 𝒢 𝔉,
            walkCoef (physRoundCoef 𝔭 𝒢 q 𝔉 k ζ) (physRoundTgt 𝔭 𝒢 𝔉 k) (n, x) (List.ofFn w) *
              G (walkEnd (physRoundTgt 𝔭 𝒢 𝔉 k) (n, x) (List.ofFn w))
      else 0 := by
  unfold pairUnit
  rw [physRound_eq_rowOp]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [rowOp_pow_apply]

open _root_.Classical in
/-- **The path expansion of the moment** [S-02:0212–0222]: `⟨u_n, (𝒜 𝒜*)^R u_n⟩` is the real part
of the sum over the physical lists `x` at the position `n` and over all words `w` of `R` rounds of
`mass · (product of the coefficients along the walk from (n, x)) · u_n(end of the walk)`. This is
the definition used in `physMoment`, expanded. -/
theorem physMoment_eq_sum_walks (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (R : ℕ)
    (n : 𝔭.Pos) :
    physMoment 𝔭 𝒢 q 𝔉 k ζ R n =
      (∑ x : Lists 𝒢 J ℓ, if IsPhys 𝔭 n x then
        (stateMass 𝒢 J ℓ : ℂ) *
          ∑ w : Fin R → PhysChoice 𝒢 𝔉 × PhysChoice 𝒢 𝔉,
            walkCoef (physRoundCoef 𝔭 𝒢 q 𝔉 k ζ) (physRoundTgt 𝔭 𝒢 𝔉 k) (n, x) (List.ofFn w) *
              physUnit 𝔭 𝒢 J ℓ n
                (walkEnd (physRoundTgt 𝔭 𝒢 𝔉 k) (n, x) (List.ofFn w))
      else 0).re := by
  unfold physMoment
  rw [pairUnit_pow_eq_sum_walks]

/-- `⟨u_n, (𝒜 𝒜*)^R G⟩` only depends on the values of `G` at the ends of the walks which start at
the position `n`. -/
theorem pairUnit_pow_congr (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (R : ℕ) (n : 𝔭.Pos)
    (G G' : PState 𝔭 𝒢 J ℓ → ℂ)
    (h : ∀ (x : Lists 𝒢 J ℓ) (w : Fin R → PhysChoice 𝒢 𝔉 × PhysChoice 𝒢 𝔉),
      G (walkEnd (physRoundTgt 𝔭 𝒢 𝔉 k) (n, x) (List.ofFn w)) =
        G' (walkEnd (physRoundTgt 𝔭 𝒢 𝔉 k) (n, x) (List.ofFn w))) :
    pairUnit 𝔭 𝒢 J ℓ n (((physOp 𝔭 𝒢 q 𝔉 k ζ * physAdj 𝔭 𝒢 q 𝔉 k ζ) ^ R) G) =
      pairUnit 𝔭 𝒢 J ℓ n (((physOp 𝔭 𝒢 q 𝔉 k ζ * physAdj 𝔭 𝒢 q 𝔉 k ζ) ^ R) G') := by
  rw [pairUnit_pow_eq_sum_walks, pairUnit_pow_eq_sum_walks]
  refine Finset.sum_congr rfl fun x _ => ?_
  have e : (∑ w : Fin R → PhysChoice 𝒢 𝔉 × PhysChoice 𝒢 𝔉,
        walkCoef (physRoundCoef 𝔭 𝒢 q 𝔉 k ζ) (physRoundTgt 𝔭 𝒢 𝔉 k) (n, x) (List.ofFn w) *
          G (walkEnd (physRoundTgt 𝔭 𝒢 𝔉 k) (n, x) (List.ofFn w))) =
      ∑ w : Fin R → PhysChoice 𝒢 𝔉 × PhysChoice 𝒢 𝔉,
        walkCoef (physRoundCoef 𝔭 𝒢 q 𝔉 k ζ) (physRoundTgt 𝔭 𝒢 𝔉 k) (n, x) (List.ofFn w) *
          G' (walkEnd (physRoundTgt 𝔭 𝒢 𝔉 k) (n, x) (List.ofFn w)) :=
    Finset.sum_congr rfl fun w _ => by rw [h x w]
  rw [e]

omit [Fintype N] in
/-- `⟨u_n, ·⟩` is additive. -/
theorem pairUnit_sum {ι : Type*} (t : Finset ι) (n : 𝔭.Pos) (G : ι → PState 𝔭 𝒢 J ℓ → ℂ) :
    pairUnit 𝔭 𝒢 J ℓ n (∑ j ∈ t, G j) = ∑ j ∈ t, pairUnit 𝔭 𝒢 J ℓ n (G j) := by
  unfold pairUnit
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · rw [Finset.sum_apply, Finset.mul_sum]
  · rw [Finset.sum_const_zero]

omit [Fintype N] in
/-- `⟨u_n, ·⟩` is homogeneous. -/
theorem pairUnit_smul (n : 𝔭.Pos) (c : ℂ) (G : PState 𝔭 𝒢 J ℓ → ℂ) :
    pairUnit 𝔭 𝒢 J ℓ n (c • G) = c * pairUnit 𝔭 𝒢 J ℓ n G := by
  unfold pairUnit
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs
  · rw [Pi.smul_apply, smul_eq_mul]
    ring
  · rw [mul_zero]

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
