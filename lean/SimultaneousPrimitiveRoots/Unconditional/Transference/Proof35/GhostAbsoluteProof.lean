module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.GhostOneGroup
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.GhostTensor
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Bridge
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# (eq:ghost-absolute-bound): the weighted row and column bounds of the absolute visit operations

Source: `verification/stage7-sources/S-02.tex`, lines 646–702 (`[S-02:0646–0702]`).

`ghostAbsolute : GhostAbsolute` — "for some fixed `C_v`, `|G_i| w ≤ L^{C_v} w`,
`|G_i|* w ≤ L^{C_v} w` … The exponent `C_v` is independent of `m, C₁, J`. All these assertions
include the version with doubled ghost births."

## The argument

The absolute kernel with doubled births is dominated by the product over the big groups of the
one-group absolute kernels `ghostAbsG` with the truncation of each single new memory
(`ghostCoef_abs_le`); the truncation of the total memory is kept in the test function
(`truncTotal`, `ghost_term_le`).

* **Row** (`ghost_rowBound`). The weight `v^{j_tot}` is a product, so the row sum is the product
  of the one-group row sums (`Fintype.prod_sum`); each is the row of the kernel `ghostAbsKernel`
  on the symmetric function `v^j` (`ghostAbs_row_eq_kernel`) and at most `e^{c_max v μ̃_g(𝒫_g)}`
  times `v^j` (`ghostAbsKernel_row_le`).
* **Column** (`ghost_colBound`). For a nonnegative `f` which is symmetric in the particle indices,
  the action of the product of the one-group rows on `f` is the action of the product of the
  kernels (`tensor_rows`); the measure and the weight are products over the big groups (apart from
  the factor of the other coordinates, `exists_memWeight_factor`), so the one-group column bounds
  `ghostAbsKernel_col_le` multiply (`tensor_col_le`).

With `μ̃_g(𝒫_g) ≤ 2` (`eventually_tiltLaw_sum_le`), the constants of (eq:memory-weight-choice)
(`memV_spec`: `A_i + |D_i|/v < 1`, `A_i + |2 C_i|/v < 1`, `|D_i| ≤ 1/ρ`,
`|2 C_i| ≤ 2 max(1, v₊)/ρ`) and at most `C₀ T` big groups (`PrimeGroups.prod_big_le_rpow`), both
constants are at most `L^{C_v}` with `C_v = 4 max(1, v₊) v C₀ / ρ`, which depends on `P` only.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

open Filter

noncomputable section

/-- A column bound with a larger constant. -/
theorem colBound_mono_of_nonneg {X Ξ : Type*} [Fintype X] [Fintype Ξ] {m w : X → ℝ}
    {Sy : (X → ℝ) → Prop} {κ : X → Ξ → ℝ} {tgt : X → Ξ → X} {C C' : ℝ}
    (h : ColBound m w Sy κ tgt C) (hm : ∀ s, 0 ≤ m s) (hw : ∀ s, 0 ≤ w s) (hC : C ≤ C') :
    ColBound m w Sy κ tgt C' :=
  fun f hf0 hfS => (h f hf0 hfS).trans (mul_le_mul_of_nonneg_right hC
    (Finset.sum_nonneg fun s _ => mul_nonneg (mul_nonneg (hm s) (hw s)) (hf0 s)))

section Multi

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {N : Type}

/-! ### Sums over the memory states -/

/-- An inequality between two sums over the memory states follows from the inequalities between
the sums over the memories, for fixed residues and active lists. -/
theorem sum_MState_le {L Rr : MState 𝒢 J ℓ Bc → ℝ} {C : ℝ}
    (h : ∀ (y : ResVec (smallPrimes 𝒢)) (xs : LabelList 𝒢.small J ℓ) (xb : LabelList 𝒢.big J ℓ),
      ∑ mem : (g : B) → Mem 𝒢 Bc g, L ⟨y, xs, xb, mem⟩ ≤
        C * ∑ mem : (g : B) → Mem 𝒢 Bc g, Rr ⟨y, xs, xb, mem⟩) :
    ∑ s, L s ≤ C * ∑ s, Rr s := by
  have e : ∀ φ : MState 𝒢 J ℓ Bc → ℝ,
      ∑ s, φ s = ∑ y, ∑ xs, ∑ xb, ∑ mem, φ ⟨y, xs, xb, mem⟩ := by
    intro φ
    refine (Fintype.sum_equiv MState.equivProd φ
      (fun t => φ ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩) (fun s => rfl)).trans ?_
    refine (Fintype.sum_prod_type _).trans (Finset.sum_congr rfl fun y _ => ?_)
    refine (Fintype.sum_prod_type _).trans (Finset.sum_congr rfl fun xs _ => ?_)
    exact Fintype.sum_prod_type _
  rw [e L, e Rr, Finset.mul_sum]
  refine Finset.sum_le_sum fun y _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun xs _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun xb _ => h y xs xb

omit [DecidableEq S] [DecidableEq B] in
/-- The measure of `ℋ` is the product of a nonnegative factor of the residues and the active
lists and of the measure of the memories. -/
theorem exists_memWeight_factor (𝒢 : GroupFamily S B) (q : ℝ) (n : ℕ)
    (hpos : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p) (y : ResVec (smallPrimes 𝒢))
    (xs : LabelList 𝒢.small J ℓ) (xb : LabelList 𝒢.big J ℓ) :
    ∃ base : ℝ, 0 ≤ base ∧ ∀ mem : (g : B) → Mem 𝒢 Bc g,
      memWeight 𝒢 q n (⟨y, xs, xb, mem⟩ : MState 𝒢 J ℓ Bc) = base * memMass 𝒢 q n mem := by
  by_cases h : IsSmallState 𝒢 y xs
  · refine ⟨haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ * bigListMass 𝒢 q n xb, ?_,
      fun mem => ?_⟩
    · have h1 : 0 ≤ haarMass (smallPrimes 𝒢) := inv_nonneg.mpr (Nat.cast_nonneg _)
      have h2 : 0 ≤ smallListMass 𝒢 J ℓ :=
        Finset.prod_nonneg fun g _ =>
          inv_nonneg.mpr (pow_nonneg (Schur.reciprocalMass_nonneg _) _)
      have h3 : 0 ≤ bigListMass 𝒢 q n xb :=
        Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun i _ => hpos g _ (xb g i).2
      exact mul_nonneg (mul_nonneg h1 h2) h3
    · unfold memWeight
      exact if_pos h
  · refine ⟨0, le_rfl, fun mem => ?_⟩
    unfold memWeight
    rw [zero_mul]
    exact if_neg h

/-! ### The truncation of the total memory -/

/-- A function of the memory states, restricted to total memory size at most `Bc`. -/
def truncTotal (f : MState 𝒢 J ℓ Bc → ℝ) : MState 𝒢 J ℓ Bc → ℝ :=
  fun s => if memTotal s ≤ Bc then f s else 0

omit [DecidableEq S] [DecidableEq B] in
theorem truncTotal_nonneg {f : MState 𝒢 J ℓ Bc → ℝ} (hf : ∀ s, 0 ≤ f s) (s : MState 𝒢 J ℓ Bc) :
    0 ≤ truncTotal f s := by
  unfold truncTotal
  split_ifs
  · exact hf s
  · exact le_rfl

omit [DecidableEq S] [DecidableEq B] in
theorem truncTotal_le {f : MState 𝒢 J ℓ Bc → ℝ} (hf : ∀ s, 0 ≤ f s) (s : MState 𝒢 J ℓ Bc) :
    truncTotal f s ≤ f s := by
  unfold truncTotal
  split_ifs
  · exact le_rfl
  · exact hf s

omit [DecidableEq S] in
theorem truncTotal_memSymmetric {f : MState 𝒢 J ℓ Bc → ℝ} (hf : MemSymmetric f) :
    MemSymmetric (truncTotal f) := by
  intro s g σ
  show (if memTotal (s.permMem g σ) ≤ Bc then f (s.permMem g σ) else 0) =
    if memTotal s ≤ Bc then f s else 0
  rw [memTotal_permMem, hf s g σ]

omit [Fintype B] [DecidableEq S] in
/-- A function which is symmetric in the particle indices is symmetric as a function of the
memory of one group, the other coordinates being fixed. -/
theorem memSymmetric_update {f : MState 𝒢 J ℓ Bc → ℝ} (hf : MemSymmetric f)
    (y : ResVec (smallPrimes 𝒢)) (xs : LabelList 𝒢.small J ℓ) (xb : LabelList 𝒢.big J ℓ)
    (x : (g : B) → Mem 𝒢 Bc g) (g : B) (m : Fin (Bc + 1)) (σ : Equiv.Perm (Fin m.val))
    (y₀ : Fin m.val → Particle 𝒢 g) :
    f ⟨y, xs, xb, Function.update x g (⟨m, y₀ ∘ σ⟩ : Mem 𝒢 Bc g)⟩ =
      f ⟨y, xs, xb, Function.update x g (⟨m, y₀⟩ : Mem 𝒢 Bc g)⟩ := by
  have h1 := MemSymmetric.update_perm hf
    (⟨y, xs, xb, Function.update x g (⟨m, y₀⟩ : Mem 𝒢 Bc g)⟩ : MState 𝒢 J ℓ Bc) g
    (⟨m, y₀⟩ : Mem 𝒢 Bc g) (Function.update_self g _ x) σ
  have h2 : Function.update (Function.update x g (⟨m, y₀⟩ : Mem 𝒢 Bc g)) g
      (⟨m, y₀ ∘ σ⟩ : Mem 𝒢 Bc g) = Function.update x g (⟨m, y₀ ∘ σ⟩ : Mem 𝒢 Bc g) :=
    Function.update_idem _ _ _
  exact (congrArg (fun mm => f ⟨y, xs, xb, mm⟩) h2).symm.trans h1

/-! ### Domination by the product of the one-group kernels -/

omit [DecidableEq S] [DecidableEq B] in
/-- **The absolute coefficient of the visit operation with doubled births is at most the product
over the big groups of the one-group absolute coefficients** (with equality when the coefficient
does not vanish). -/
theorem ghostCoef_abs_le (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (c : GhostChoice 𝒢 Bc) :
    (2 : ℝ) ^ ghostBirthCount c * |ghostCoef D i s c| ≤
      ∏ g, ghostAbsG 𝒢 D.q D.ρ D.n i g (s.mem g) (c g) := by
  by_cases hcond : memTotal s ≤ Bc ∧ (∑ g, ghostNewSize (s.mem g) (c g)) ≤ Bc
  · have h1 : ghostCoef D i s c = ∏ g, ghostCoefG 𝒢 D.q D.ρ D.n i g (s.mem g) (c g) := by
      unfold ghostCoef
      exact if_pos hcond
    have h2 : ∀ g, ghostAbsG 𝒢 D.q D.ρ D.n i g (s.mem g) (c g) =
        (2 : ℝ) ^ (c g).2.1.val * |ghostCoefG 𝒢 D.q D.ρ D.n i g (s.mem g) (c g)| := by
      intro g
      unfold ghostAbsG
      exact if_pos ((Finset.single_le_sum (f := fun g => ghostNewSize (s.mem g) (c g))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)).trans hcond.2)
    rw [h1, Finset.abs_prod]
    unfold ghostBirthCount
    rw [← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact le_of_eq (Finset.prod_congr rfl fun g _ => (h2 g).symm)
  · have h1 : ghostCoef D i s c = 0 := by
      unfold ghostCoef
      exact if_neg hcond
    rw [h1, abs_zero, mul_zero]
    exact Finset.prod_nonneg fun g _ => ghostAbsG_nonneg 𝒢 D.q D.ρ D.n i g (s.mem g) (c g)

omit [DecidableEq S] [DecidableEq B] in
/-- A nonvanishing coefficient of the visit operation leads to a state of total memory size at
most `Bc`. -/
theorem memTotal_ghostTgt_le (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (c : GhostChoice 𝒢 Bc) (h : ghostCoef D i s c ≠ 0) : memTotal (ghostTgt s c) ≤ Bc := by
  have hcond : memTotal s ≤ Bc ∧ (∑ g, ghostNewSize (s.mem g) (c g)) ≤ Bc := by
    by_contra hcon
    refine h ?_
    unfold ghostCoef
    exact if_neg hcon
  have hg : ∀ g, ghostNewSize (s.mem g) (c g) ≤ Bc := fun g =>
    (Finset.single_le_sum (f := fun g => ghostNewSize (s.mem g) (c g))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ g)).trans hcond.2
  calc memTotal (ghostTgt s c) = ∑ g, (ghostNewMem (s.mem g) (c g)).1.val := rfl
    _ = ∑ g, ghostNewSize (s.mem g) (c g) :=
        Finset.sum_congr rfl fun g _ => ghostNewMem_size _ _ (hg g)
    _ ≤ Bc := hcond.2

omit [DecidableEq S] [DecidableEq B] in
/-- One term of the absolute visit operation, applied to a nonnegative function. -/
theorem ghost_term_le (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (c : GhostChoice 𝒢 Bc) (f : MState 𝒢 J ℓ Bc → ℝ) (hf0 : ∀ s, 0 ≤ f s) :
    (2 : ℝ) ^ ghostBirthCount c * |ghostCoef D i s c| * f (ghostTgt s c) ≤
      (∏ g, ghostAbsG 𝒢 D.q D.ρ D.n i g (s.mem g) (c g)) * truncTotal f (ghostTgt s c) := by
  by_cases h0 : ghostCoef D i s c = 0
  · rw [h0, abs_zero, mul_zero, zero_mul]
    exact mul_nonneg
      (Finset.prod_nonneg fun g _ => ghostAbsG_nonneg 𝒢 D.q D.ρ D.n i g (s.mem g) (c g))
      (truncTotal_nonneg hf0 _)
  · have e : truncTotal f (ghostTgt s c) = f (ghostTgt s c) := by
      unfold truncTotal
      exact if_pos (memTotal_ghostTgt_le D i s c h0)
    rw [e]
    exact mul_le_mul_of_nonneg_right (ghostCoef_abs_le D i s c) (hf0 _)

/-! ### The row bound -/

omit [DecidableEq S] in
/-- **The weighted row bound of the absolute visit operation with doubled births**: the product
over the big groups of the one-group constants. -/
theorem ghost_rowBound (D : MemData 𝒢 J ℓ N) (Bc i : ℕ) {v cmax Mmax : ℝ}
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p)
    (hA : 0 ≤ Graph.sourceGhostA (visitQ D.q D.n i) D.ρ) (hv : 0 < v)
    (hbase : Graph.sourceGhostA (visitQ D.q D.n i) D.ρ +
      |Graph.sourceGhostD (visitQ D.q D.n i) D.ρ| / v ≤ 1)
    (hC : ∀ g, |2 * Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g))
      (visitQ D.q D.n i) D.ρ| ≤ cmax)
    (hM : ∀ g, ∑ p : {p : ℕ // p ∈ 𝒢.big g}, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax) :
    RowBound (schurWeight v)
      (fun (s : MState 𝒢 J ℓ Bc) (c : GhostChoice 𝒢 Bc) =>
        (2 : ℝ) ^ ghostBirthCount c * |ghostCoef D i s c|)
      ghostTgt (∏ _g : B, Real.exp (cmax * v * Mmax)) := by
  intro s
  have hone : ∀ g : B, ∑ cg : Finset (Fin Bc) × Batch 𝒢 Bc g,
      ghostAbsG 𝒢 D.q D.ρ D.n i g (s.mem g) cg * v ^ (ghostNewMem (s.mem g) cg).1.val ≤
        Real.exp (cmax * v * Mmax) * v ^ (s.mem g).1.val := by
    intro g
    have e := ghostAbs_row_eq_kernel 𝒢 D.q D.ρ D.n i g hA (hν g)
      (fun y : Mem 𝒢 Bc g => v ^ y.1.val) (fun _ _ _ => rfl) (s.mem g)
    exact e.le.trans
      (ghostAbsKernel_row_le 𝒢 D.q D.ρ D.n i g (hν g) hA hv hbase (hC g) (hM g) (s.mem g))
  have hterm : ∀ c : GhostChoice 𝒢 Bc,
      (2 : ℝ) ^ ghostBirthCount c * |ghostCoef D i s c| * schurWeight v (ghostTgt s c) ≤
        ∏ g, (ghostAbsG 𝒢 D.q D.ρ D.n i g (s.mem g) (c g) *
          v ^ (ghostNewMem (s.mem g) (c g)).1.val) := by
    intro c
    have h2 : schurWeight v (ghostTgt s c) = ∏ g, v ^ (ghostNewMem (s.mem g) (c g)).1.val :=
      (Finset.prod_pow_eq_pow_sum Finset.univ
        (fun g => (ghostNewMem (s.mem g) (c g)).1.val) v).symm
    rw [h2, Finset.prod_mul_distrib]
    exact mul_le_mul_of_nonneg_right (ghostCoef_abs_le D i s c)
      (Finset.prod_nonneg fun g _ => (pow_pos hv _).le)
  calc ∑ c : GhostChoice 𝒢 Bc,
        (2 : ℝ) ^ ghostBirthCount c * |ghostCoef D i s c| * schurWeight v (ghostTgt s c)
      ≤ ∑ c : GhostChoice 𝒢 Bc, ∏ g, (ghostAbsG 𝒢 D.q D.ρ D.n i g (s.mem g) (c g) *
          v ^ (ghostNewMem (s.mem g) (c g)).1.val) := Finset.sum_le_sum fun c _ => hterm c
    _ = ∏ g, ∑ cg : Finset (Fin Bc) × Batch 𝒢 Bc g,
          ghostAbsG 𝒢 D.q D.ρ D.n i g (s.mem g) cg * v ^ (ghostNewMem (s.mem g) cg).1.val :=
        (Fintype.prod_sum fun g (cg : Finset (Fin Bc) × Batch 𝒢 Bc g) =>
          ghostAbsG 𝒢 D.q D.ρ D.n i g (s.mem g) cg *
            v ^ (ghostNewMem (s.mem g) cg).1.val).symm
    _ ≤ ∏ g, (Real.exp (cmax * v * Mmax) * v ^ (s.mem g).1.val) :=
        Finset.prod_le_prod
          (fun g _ => Finset.sum_nonneg fun cg _ =>
            mul_nonneg (ghostAbsG_nonneg 𝒢 D.q D.ρ D.n i g (s.mem g) cg) (pow_pos hv _).le)
          (fun g _ => hone g)
    _ = (∏ _g : B, Real.exp (cmax * v * Mmax)) * schurWeight v s := by
        rw [Finset.prod_mul_distrib]
        exact congrArg (fun t => (∏ _g : B, Real.exp (cmax * v * Mmax)) * t)
          (Finset.prod_pow_eq_pow_sum Finset.univ (fun g => (s.mem g).1.val) v)

/-! ### The column bound -/

omit [DecidableEq S] in
/-- The column inequality for fixed residues and active lists. -/
theorem ghost_col_fiber (D : MemData 𝒢 J ℓ N) (Bc i : ℕ) {v dmax Mmax : ℝ}
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p)
    (hA : 0 ≤ Graph.sourceGhostA (visitQ D.q D.n i) D.ρ) (hv : 0 < v)
    (hbase : ∀ g, Graph.sourceGhostA (visitQ D.q D.n i) D.ρ +
      |2 * Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g))
        (visitQ D.q D.n i) D.ρ| / v ≤ 1)
    (hD : |Graph.sourceGhostD (visitQ D.q D.n i) D.ρ| ≤ dmax)
    (hM : ∀ g, ∑ p : {p : ℕ // p ∈ 𝒢.big g}, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax)
    (f : MState 𝒢 J ℓ Bc → ℝ) (hf0 : ∀ s, 0 ≤ f s) (hfsym : MemSymmetric f)
    (y : ResVec (smallPrimes 𝒢)) (xs : LabelList 𝒢.small J ℓ) (xb : LabelList 𝒢.big J ℓ) :
    ∑ mem : (g : B) → Mem 𝒢 Bc g,
        memWeight 𝒢 D.q D.n (⟨y, xs, xb, mem⟩ : MState 𝒢 J ℓ Bc) *
          schurWeight v (⟨y, xs, xb, mem⟩ : MState 𝒢 J ℓ Bc) *
          ∑ c : GhostChoice 𝒢 Bc,
            (2 : ℝ) ^ ghostBirthCount c * |ghostCoef D i ⟨y, xs, xb, mem⟩ c| *
              f (ghostTgt ⟨y, xs, xb, mem⟩ c) ≤
      (∏ _g : B, Real.exp (dmax * v * Mmax)) *
        ∑ mem : (g : B) → Mem 𝒢 Bc g,
          memWeight 𝒢 D.q D.n (⟨y, xs, xb, mem⟩ : MState 𝒢 J ℓ Bc) *
            schurWeight v (⟨y, xs, xb, mem⟩ : MState 𝒢 J ℓ Bc) * f ⟨y, xs, xb, mem⟩ := by
  have hne : ∀ g : B, Nonempty (Mem 𝒢 Bc g) := fun g => ⟨emptyMem 𝒢 Bc g⟩
  obtain ⟨base, hbase0, hw⟩ := exists_memWeight_factor (J := J) (ℓ := ℓ) (Bc := Bc) 𝒢 D.q D.n hν
    y xs xb
  -- the measure and the weight of the memories are products over the big groups
  have hW : ∀ mem : (g : B) → Mem 𝒢 Bc g,
      memWeight 𝒢 D.q D.n (⟨y, xs, xb, mem⟩ : MState 𝒢 J ℓ Bc) *
          schurWeight v (⟨y, xs, xb, mem⟩ : MState 𝒢 J ℓ Bc) =
        base * ∏ g, (Graph.finiteMemoryPointMass
          (fun z : Particle 𝒢 g => tiltLaw (𝒢.big g) D.q D.n z.1) (mem g) *
            v ^ (mem g).1.val) := by
    intro mem
    have e1 : schurWeight v (⟨y, xs, xb, mem⟩ : MState 𝒢 J ℓ Bc) = ∏ g, v ^ (mem g).1.val :=
      (Finset.prod_pow_eq_pow_sum Finset.univ (fun g => (mem g).1.val) v).symm
    have e2 : memMass 𝒢 D.q D.n mem = ∏ g, Graph.finiteMemoryPointMass
        (fun z : Particle 𝒢 g => tiltLaw (𝒢.big g) D.q D.n z.1) (mem g) := rfl
    rw [hw mem, e1, e2, Finset.prod_mul_distrib, mul_assoc]
  have hMg : ∀ (g : B) (u : Mem 𝒢 Bc g), 0 ≤ Graph.finiteMemoryPointMass
      (fun z : Particle 𝒢 g => tiltLaw (𝒢.big g) D.q D.n z.1) u * v ^ u.1.val :=
    fun g u => mul_nonneg (memPointMass_nonneg D.q D.n (hν g) u) (pow_pos hv _).le
  have hf'sym : MemSymmetric (truncTotal f) := truncTotal_memSymmetric hfsym
  -- the action of the absolute kernel is dominated by the action of the product kernel
  have hstep : ∀ mem : (g : B) → Mem 𝒢 Bc g,
      ∑ c : GhostChoice 𝒢 Bc,
          (2 : ℝ) ^ ghostBirthCount c * |ghostCoef D i ⟨y, xs, xb, mem⟩ c| *
            f (ghostTgt ⟨y, xs, xb, mem⟩ c) ≤
        ∑ y' : (g : B) → Mem 𝒢 Bc g,
          (∏ g, ghostAbsKernel 𝒢 D.q D.ρ D.n i g Bc (mem g) (y' g)) *
            truncTotal f ⟨y, xs, xb, y'⟩ := by
    intro mem
    have ht := tensor_rows (X := fun g : B => Mem 𝒢 Bc g)
      (I := fun g : B => Finset (Fin Bc) × Batch 𝒢 Bc g)
      (fun g cg => ghostAbsG 𝒢 D.q D.ρ D.n i g (mem g) cg)
      (fun g cg => ghostNewMem (mem g) cg)
      (fun g u => ghostAbsKernel 𝒢 D.q D.ρ D.n i g Bc (mem g) u)
      (fun m' => truncTotal f ⟨y, xs, xb, m'⟩)
      (fun g x => ghostAbs_row_eq_kernel 𝒢 D.q D.ρ D.n i g hA (hν g)
        (fun u => truncTotal f ⟨y, xs, xb, Function.update x g u⟩)
        (fun m σ y₀ => memSymmetric_update hf'sym y xs xb x g m σ y₀) (mem g))
    refine le_trans (Finset.sum_le_sum fun c _ => ?_) ht.le
    exact ghost_term_le D i ⟨y, xs, xb, mem⟩ c f hf0
  -- the product of the one-group column bounds
  have hcol := tensor_col_le (X := fun g : B => Mem 𝒢 Bc g)
    (fun g u => Graph.finiteMemoryPointMass
      (fun z : Particle 𝒢 g => tiltLaw (𝒢.big g) D.q D.n z.1) u * v ^ u.1.val)
    (fun g => ghostAbsKernel 𝒢 D.q D.ρ D.n i g Bc)
    (fun _ => Real.exp (dmax * v * Mmax))
    (fun m' => truncTotal f ⟨y, xs, xb, m'⟩) hMg
    (fun g u y' => ghostAbsKernel_nonneg 𝒢 D.q D.ρ D.n i g hA (hν g) u y')
    (fun m' => truncTotal_nonneg hf0 _)
    (fun g y' => ghostAbsKernel_col_le 𝒢 D.q D.ρ D.n i g (hν g) hA hv (hbase g) hD (hM g) y')
  have hCnn : 0 ≤ ∏ _g : B, Real.exp (dmax * v * Mmax) :=
    Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le
  have hend : ∑ mem : (g : B) → Mem 𝒢 Bc g,
        memWeight 𝒢 D.q D.n (⟨y, xs, xb, mem⟩ : MState 𝒢 J ℓ Bc) *
          schurWeight v (⟨y, xs, xb, mem⟩ : MState 𝒢 J ℓ Bc) * f ⟨y, xs, xb, mem⟩ =
      base * ∑ mem : (g : B) → Mem 𝒢 Bc g,
        (∏ g, (Graph.finiteMemoryPointMass
          (fun z : Particle 𝒢 g => tiltLaw (𝒢.big g) D.q D.n z.1) (mem g) *
            v ^ (mem g).1.val)) * f ⟨y, xs, xb, mem⟩ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun mem _ => by rw [hW mem, mul_assoc]
  calc ∑ mem : (g : B) → Mem 𝒢 Bc g,
        memWeight 𝒢 D.q D.n (⟨y, xs, xb, mem⟩ : MState 𝒢 J ℓ Bc) *
          schurWeight v (⟨y, xs, xb, mem⟩ : MState 𝒢 J ℓ Bc) *
          ∑ c : GhostChoice 𝒢 Bc,
            (2 : ℝ) ^ ghostBirthCount c * |ghostCoef D i ⟨y, xs, xb, mem⟩ c| *
              f (ghostTgt ⟨y, xs, xb, mem⟩ c)
      ≤ ∑ mem : (g : B) → Mem 𝒢 Bc g,
          base * ((∏ g, (Graph.finiteMemoryPointMass
            (fun z : Particle 𝒢 g => tiltLaw (𝒢.big g) D.q D.n z.1) (mem g) *
              v ^ (mem g).1.val)) *
            ∑ y' : (g : B) → Mem 𝒢 Bc g,
              (∏ g, ghostAbsKernel 𝒢 D.q D.ρ D.n i g Bc (mem g) (y' g)) *
                truncTotal f ⟨y, xs, xb, y'⟩) := by
        refine Finset.sum_le_sum fun mem _ => ?_
        rw [hW mem, mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hstep mem) (Finset.prod_nonneg fun g _ => hMg g (mem g)))
          hbase0
    _ = base * ∑ mem : (g : B) → Mem 𝒢 Bc g,
          (∏ g, (Graph.finiteMemoryPointMass
            (fun z : Particle 𝒢 g => tiltLaw (𝒢.big g) D.q D.n z.1) (mem g) *
              v ^ (mem g).1.val)) *
            ∑ y' : (g : B) → Mem 𝒢 Bc g,
              (∏ g, ghostAbsKernel 𝒢 D.q D.ρ D.n i g Bc (mem g) (y' g)) *
                truncTotal f ⟨y, xs, xb, y'⟩ := (Finset.mul_sum _ _ _).symm
    _ ≤ base * ((∏ _g : B, Real.exp (dmax * v * Mmax)) *
          ∑ y' : (g : B) → Mem 𝒢 Bc g,
            (∏ g, (Graph.finiteMemoryPointMass
              (fun z : Particle 𝒢 g => tiltLaw (𝒢.big g) D.q D.n z.1) (y' g) *
                v ^ (y' g).1.val)) * truncTotal f ⟨y, xs, xb, y'⟩) :=
        mul_le_mul_of_nonneg_left hcol hbase0
    _ ≤ base * ((∏ _g : B, Real.exp (dmax * v * Mmax)) *
          ∑ y' : (g : B) → Mem 𝒢 Bc g,
            (∏ g, (Graph.finiteMemoryPointMass
              (fun z : Particle 𝒢 g => tiltLaw (𝒢.big g) D.q D.n z.1) (y' g) *
                v ^ (y' g).1.val)) * f ⟨y, xs, xb, y'⟩) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun y' _ => mul_le_mul_of_nonneg_left (truncTotal_le hf0 _)
            (Finset.prod_nonneg fun g _ => hMg g (y' g))) hCnn) hbase0
    _ = (∏ _g : B, Real.exp (dmax * v * Mmax)) *
        ∑ mem : (g : B) → Mem 𝒢 Bc g,
          memWeight 𝒢 D.q D.n (⟨y, xs, xb, mem⟩ : MState 𝒢 J ℓ Bc) *
            schurWeight v (⟨y, xs, xb, mem⟩ : MState 𝒢 J ℓ Bc) * f ⟨y, xs, xb, mem⟩ := by
        rw [hend]
        ring

/-- **The weighted column bound of the absolute visit operation with doubled births**, in the
measure of `ℋ` and on the functions which are symmetric in the particle indices: the product over
the big groups of the one-group constants. -/
theorem ghost_colBound (D : MemData 𝒢 J ℓ N) (Bc i : ℕ) {v dmax Mmax : ℝ}
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p)
    (hA : 0 ≤ Graph.sourceGhostA (visitQ D.q D.n i) D.ρ) (hv : 0 < v)
    (hbase : ∀ g, Graph.sourceGhostA (visitQ D.q D.n i) D.ρ +
      |2 * Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g))
        (visitQ D.q D.n i) D.ρ| / v ≤ 1)
    (hD : |Graph.sourceGhostD (visitQ D.q D.n i) D.ρ| ≤ dmax)
    (hM : ∀ g, ∑ p : {p : ℕ // p ∈ 𝒢.big g}, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax) :
    ColBound (memWeight 𝒢 D.q D.n) (schurWeight v) (fun f => MemSymmetric f)
      (fun (s : MState 𝒢 J ℓ Bc) (c : GhostChoice 𝒢 Bc) =>
        (2 : ℝ) ^ ghostBirthCount c * |ghostCoef D i s c|)
      ghostTgt (∏ _g : B, Real.exp (dmax * v * Mmax)) :=
  fun f hf0 hfsym => sum_MState_le fun y xs xb =>
    ghost_col_fiber D Bc i hν hA hv hbase hD hM f hf0 hfsym y xs xb

end Multi

/-! ### (eq:ghost-absolute-bound) -/

/-- **(eq:ghost-absolute-bound)** [S-02:0681–0702], proved: the weighted row and column bounds
`L^{C_v}` of the absolute visit operations with doubled births, with
`C_v = (2 max(1, v₊)/ρ · v · 2) · C₀` depending on `P` only, for every cutoff. -/
theorem ghostAbsolute : GhostAbsolute := by
  intro P
  have hρ := memRho_pos P
  have hv : 0 < memV P := lt_trans zero_lt_one (one_lt_memV P)
  have hmax : (1 : ℝ) ≤ max 1 P.vPlus := le_max_left _ _
  have hb0 : 0 ≤ 2 * max 1 P.vPlus / memRho P * memV P * 2 :=
    mul_nonneg (mul_nonneg (div_nonneg (by linarith) hρ.le) hv.le) (by norm_num)
  have hdb : 1 / memRho P * memV P * 2 ≤ 2 * max 1 P.vPlus / memRho P * memV P * 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (by linarith) hρ.le) hv.le) (by norm_num)
  refine ⟨2 * max 1 P.vPlus / memRho P * memV P * 2 * P.C₀, fun J => ?_⟩
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp ((eventually_big_tilt P one_pos).and
    ((eventually_tiltLaw_sum_le P).and (Real.tendsto_log_atTop.eventually_ge_atTop 1)))
  refine ⟨x₀, fun x hx S B _ _ _ _ 𝔊 N _ 𝔉 ζ k Bc => ?_⟩
  obtain ⟨htilt, hsum, hL1⟩ := hx₀ x hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hL1
  intro i _
  have hν : ∀ g, ∀ p ∈ 𝔊.big g,
      0 ≤ tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p :=
    fun g p hp => (htilt S B 𝔊 g p hp).2.1.le
  have hM : ∀ g : B, ∑ p : {p : ℕ // p ∈ 𝔊.big g},
      tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p ≤ 2 :=
    fun g => (Finset.sum_coe_sort (𝔊.big g)
      (fun p => tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p)).trans_le
        (hsum S B 𝔊 g)
  have hspec := fun (V : ℝ) (hV0 : 0 ≤ V) (hV : V ≤ P.vPlus) =>
    (memV_spec P).2 (visitQ P.q (Graph.sourceMemoryLength (Real.log x)) i) V 2
      (visitQ_eq _ _ _) hV0 hV (by norm_num) le_rfl
  have h0 := hspec 0 le_rfl P.vPlus_pos.le
  have hg : ∀ g : B, _ := fun g => hspec (Graph.primeGroupReciprocalMass (𝔊.big g))
    (PrimeGroups.mass_pos_of_ge (𝔊.mass_big_ge g)).le (𝔊.mass_big_le g)
  have hrow := ghost_rowBound (memData 𝔊 𝔉 k ζ) Bc i (v := memV P)
    (cmax := 2 * max 1 P.vPlus / memRho P) (Mmax := 2) hν h0.1 hv h0.2.1.le
    (fun g => (hg g).2.2.2.2) hM
  have hcol := ghost_colBound (memData 𝔊 𝔉 k ζ) Bc i (v := memV P)
    (dmax := 1 / memRho P) (Mmax := 2) hν h0.1 hv (fun g => (hg g).2.2.1.le) h0.2.2.2.1 hM
  have hprodRow : ∏ _g : B, Real.exp (2 * max 1 P.vPlus / memRho P * memV P * 2) ≤
      Real.log x ^ (2 * max 1 P.vPlus / memRho P * memV P * 2 * P.C₀) :=
    𝔊.prod_big_le_rpow hL0 (fun _ => Real.exp (2 * max 1 P.vPlus / memRho P * memV P * 2))
      _ hb0 (fun _ => (Real.exp_pos _).le) (fun _ => le_rfl)
  have hprodCol : ∏ _g : B, Real.exp (1 / memRho P * memV P * 2) ≤
      Real.log x ^ (2 * max 1 P.vPlus / memRho P * memV P * 2 * P.C₀) :=
    𝔊.prod_big_le_rpow hL0 (fun _ => Real.exp (1 / memRho P * memV P * 2))
      _ hb0 (fun _ => (Real.exp_pos _).le) (fun _ => Real.exp_le_exp.mpr hdb)
  exact ⟨hrow.mono (fun s => (schurWeight_pos hv s).le) hprodRow,
    colBound_mono_of_nonneg hcol
      (fun s => memWeight_nonneg 𝔊.toGroupFamily P.q _ hν s)
      (fun s => (schurWeight_pos hv s).le) hprodCol⟩

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
