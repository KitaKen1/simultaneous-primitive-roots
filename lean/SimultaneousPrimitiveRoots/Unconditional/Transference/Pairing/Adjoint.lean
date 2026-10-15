module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Pairing.Fiber
public import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Corollary 3.11: `𝒜*` is the adjoint of `𝒜` for the inner product of `ℋ_ph`

Source: `verification/stage7-sources/S-02.tex`, lines 120–130 (`[S-02:0120–0130]`).

The physical operators act on functions on the infinite type (position, lists). The inner product
of `ℋ_ph` is used here only when one of its arguments vanishes outside finitely many positions
(`PosSupp u Q` with `Q` finite); then it is a finite sum, written as the `finsum` over the
positions of the inner products `fib n` at one position:

* `gp u v = ∑ᶠ n, fib n u v`, `gsq u = ∑ᶠ n, fibSq n u` — the inner product and the square of the
  norm.
* `gp_physRow` — the paper's argument "before symmetrization": for fixed lists `x`, `x'` and
  auxiliary labels `r`, the transitions `(n, x) → (n + kD, x')` and the adjoint transitions
  `(n', x') → (n' - kD, x)` correspond under the translation `n' = n + kD` of the position
  ("the shared product and hence `D` are unchanged on reversal"), and both endpoints of a
  transition with nonzero coefficient are physical, hence have the same mass.
* `gp_physOp` — **`⟨u, 𝒜 v⟩ = ⟨𝒜* u, v⟩`** for `u` vanishing outside finitely many positions and
  an arbitrary `v`; `gp_physOp_left` is the same identity read from the other side.

No boundedness of the operators is used: every row and every column of `𝒜` is finite, and one of
the two vectors has finite support in the position.

Everything here is for an arbitrary position model (integer positions or residue positions).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Pairing

open scoped BigOperators ComplexConjugate

noncomputable section

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

/-! ### Functions vanishing outside a set of positions -/

section Support

variable (𝔭 : PosModel) (𝒢 : GroupFamily S B) (J ℓ : ℕ)

/-- `u` vanishes at every state whose position is outside `Q`. -/
def PosSupp (u : PState 𝔭 𝒢 J ℓ → ℂ) (Q : Set 𝔭.Pos) : Prop :=
  ∀ (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ), n ∉ Q → u (n, x) = 0

variable {𝔭 𝒢 J ℓ}

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem posSupp_mono {u : PState 𝔭 𝒢 J ℓ → ℂ} {Q Q' : Set 𝔭.Pos} (h : PosSupp 𝔭 𝒢 J ℓ u Q)
    (hQ : Q ⊆ Q') : PosSupp 𝔭 𝒢 J ℓ u Q' := fun n x hn => h n x fun hn' => hn (hQ hn')

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem posSupp_sum {ι : Type*} (s : Finset ι) {w : ι → PState 𝔭 𝒢 J ℓ → ℂ} {Q : Set 𝔭.Pos}
    (h : ∀ i ∈ s, PosSupp 𝔭 𝒢 J ℓ (w i) Q) : PosSupp 𝔭 𝒢 J ℓ (∑ i ∈ s, w i) Q := by
  intro n x hn
  rw [Finset.sum_apply]
  exact Finset.sum_eq_zero fun i hi => h i hi n x hn

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem posSupp_smul (c : ℂ) {u : PState 𝔭 𝒢 J ℓ → ℂ} {Q : Set 𝔭.Pos}
    (h : PosSupp 𝔭 𝒢 J ℓ u Q) : PosSupp 𝔭 𝒢 J ℓ (c • u) Q := by
  intro n x hn
  rw [Pi.smul_apply, h n x hn, smul_zero]

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- `u_n` vanishes outside the position `n`. -/
theorem posSupp_physUnit (n : 𝔭.Pos) : PosSupp 𝔭 𝒢 J ℓ (physUnit 𝔭 𝒢 J ℓ n) {n} :=
  fun _ x hm => physUnit_apply_of_ne hm x

theorem posSupp_fib_left {u : PState 𝔭 𝒢 J ℓ → ℂ} {Q : Set 𝔭.Pos} (h : PosSupp 𝔭 𝒢 J ℓ u Q)
    {n : 𝔭.Pos} (hn : n ∉ Q) (v : PState 𝔭 𝒢 J ℓ → ℂ) : fib 𝔭 𝒢 J ℓ n u v = 0 := by
  unfold fib
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [h n x hn, map_zero, zero_mul, mul_zero]

theorem posSupp_fib_right {v : PState 𝔭 𝒢 J ℓ → ℂ} {Q : Set 𝔭.Pos} (h : PosSupp 𝔭 𝒢 J ℓ v Q)
    {n : 𝔭.Pos} (hn : n ∉ Q) (u : PState 𝔭 𝒢 J ℓ → ℂ) : fib 𝔭 𝒢 J ℓ n u v = 0 := by
  unfold fib
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [h n x hn, mul_zero, mul_zero]

theorem posSupp_fibSq {u : PState 𝔭 𝒢 J ℓ → ℂ} {Q : Set 𝔭.Pos} (h : PosSupp 𝔭 𝒢 J ℓ u Q)
    {n : 𝔭.Pos} (hn : n ∉ Q) : fibSq 𝔭 𝒢 J ℓ n u = 0 := by
  unfold fibSq
  refine Finset.sum_eq_zero fun x _ => ?_
  rw [h n x hn, norm_zero, zero_pow two_ne_zero, mul_zero]

/-- Symmetrization does not move the position. -/
theorem posSupp_physSym {u : PState 𝔭 𝒢 J ℓ → ℂ} {Q : Set 𝔭.Pos} (h : PosSupp 𝔭 𝒢 J ℓ u Q) :
    PosSupp 𝔭 𝒢 J ℓ (physSym 𝔭 𝒢 J ℓ u) Q := by
  intro n x hn
  rw [physSym_apply_mk]
  exact Finset.sum_eq_zero fun y _ => by rw [h n y hn, mul_zero]

end Support

/-! ### The row operations at a state, and the support of their images -/

section Rows

variable {𝔭 : PosModel} {𝒢 : GroupFamily S B} {q : ℝ} {J ℓ : ℕ}

/-- The row operation of `ν` at the state `(n, x)`. -/
theorem physRow_apply_mk (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (G : PState 𝔭 𝒢 J ℓ → ℂ)
    (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ) :
    physRow 𝔭 𝒢 q ν k ζ G (n, x) =
      ∑ ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ,
        physCoef 𝔭 𝒢 q ν k ζ n x ξ.1 ξ.2 * G (𝔭.shift (k * dil ν.C x ξ.1) n, ξ.2) := rfl

/-- The adjoint row operation of `ν` at the state `(n, x)`. -/
theorem physRowAdj_apply_mk (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (G : PState 𝔭 𝒢 J ℓ → ℂ)
    (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ) :
    physRowAdj 𝔭 𝒢 q ν k ζ G (n, x) =
      ∑ ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ,
        conj (physCoef 𝔭 𝒢 q ν k ζ (𝔭.shift (-(k * dil ν.C x ξ.1)) n) ξ.2 ξ.1 x) *
          G (𝔭.shift (-(k * dil ν.C x ξ.1)) n, ξ.2) := rfl

/-- If `u` vanishes outside `Q`, the row operation of `ν` applied to `u` vanishes outside every
set `Q'` containing the positions from which a transition reaches `Q`. -/
theorem posSupp_physRow (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) {u : PState 𝔭 𝒢 J ℓ → ℂ}
    {Q Q' : Set 𝔭.Pos} (h : PosSupp 𝔭 𝒢 J ℓ u Q)
    (hQ : ∀ (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ) (r : AuxList 𝒢.big ν.C),
      𝔭.shift (k * dil ν.C x r) n ∈ Q → n ∈ Q') :
    PosSupp 𝔭 𝒢 J ℓ (physRow 𝔭 𝒢 q ν k ζ u) Q' := by
  intro n x hn
  rw [physRow_apply_mk]
  refine Finset.sum_eq_zero fun ξ _ => ?_
  rw [h _ ξ.2 fun hmem => hn (hQ n x ξ.1 hmem), mul_zero]

/-- The same for the adjoint row operation, which moves by `-kD`. -/
theorem posSupp_physRowAdj (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) {u : PState 𝔭 𝒢 J ℓ → ℂ}
    {Q Q' : Set 𝔭.Pos} (h : PosSupp 𝔭 𝒢 J ℓ u Q)
    (hQ : ∀ (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ) (r : AuxList 𝒢.big ν.C),
      𝔭.shift (-(k * dil ν.C x r)) n ∈ Q → n ∈ Q') :
    PosSupp 𝔭 𝒢 J ℓ (physRowAdj 𝔭 𝒢 q ν k ζ u) Q' := by
  intro n x hn
  rw [physRowAdj_apply_mk]
  refine Finset.sum_eq_zero fun ξ _ => ?_
  rw [h _ ξ.2 fun hmem => hn (hQ n x ξ.1 hmem), mul_zero]

variable {N : Type} [Fintype N]

/-- `𝒜` as symmetrization, sum of the row operations, symmetrization. -/
theorem physOp_apply (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (v : PState 𝔭 𝒢 J ℓ → ℂ) :
    physOp 𝔭 𝒢 q 𝔉 k ζ v =
      physSym 𝔭 𝒢 J ℓ (∑ ν, physRow 𝔭 𝒢 q (𝔉 ν) k ζ (physSym 𝔭 𝒢 J ℓ v)) := by
  unfold physOp
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.sum_apply]

/-- `𝒜*` as symmetrization, sum of the adjoint row operations, symmetrization. -/
theorem physAdj_apply (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (v : PState 𝔭 𝒢 J ℓ → ℂ) :
    physAdj 𝔭 𝒢 q 𝔉 k ζ v =
      physSym 𝔭 𝒢 J ℓ (∑ ν, physRowAdj 𝔭 𝒢 q (𝔉 ν) k ζ (physSym 𝔭 𝒢 J ℓ v)) := by
  unfold physAdj
  rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.sum_apply]

/-- If `u` vanishes outside `Q`, then `𝒜 u` vanishes outside every set containing the positions
from which a transition reaches `Q`. -/
theorem posSupp_physOp (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) {u : PState 𝔭 𝒢 J ℓ → ℂ}
    {Q Q' : Set 𝔭.Pos} (h : PosSupp 𝔭 𝒢 J ℓ u Q)
    (hQ : ∀ (ν : N) (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ) (r : AuxList 𝒢.big (𝔉 ν).C),
      𝔭.shift (k * dil (𝔉 ν).C x r) n ∈ Q → n ∈ Q') :
    PosSupp 𝔭 𝒢 J ℓ (physOp 𝔭 𝒢 q 𝔉 k ζ u) Q' := by
  rw [physOp_apply]
  exact posSupp_physSym (posSupp_sum _ fun ν _ =>
    posSupp_physRow (𝔉 ν) k ζ (posSupp_physSym h) (hQ ν))

/-- If `u` vanishes outside `Q`, then `𝒜* u` vanishes outside every set containing the positions
from which an adjoint transition reaches `Q`. -/
theorem posSupp_physAdj (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) {u : PState 𝔭 𝒢 J ℓ → ℂ}
    {Q Q' : Set 𝔭.Pos} (h : PosSupp 𝔭 𝒢 J ℓ u Q)
    (hQ : ∀ (ν : N) (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ) (r : AuxList 𝒢.big (𝔉 ν).C),
      𝔭.shift (-(k * dil (𝔉 ν).C x r)) n ∈ Q → n ∈ Q') :
    PosSupp 𝔭 𝒢 J ℓ (physAdj 𝔭 𝒢 q 𝔉 k ζ u) Q' := by
  rw [physAdj_apply]
  exact posSupp_physSym (posSupp_sum _ fun ν _ =>
    posSupp_physRowAdj (𝔉 ν) k ζ (posSupp_physSym h) (hQ ν))

variable (𝔭 𝒢)

/-- The positions from which a transition of `𝒜` reaches `Q`. -/
def fwdReach (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (Q : Set 𝔭.Pos) : Set 𝔭.Pos :=
  {n | ∃ (ν : N) (x : Lists 𝒢 J ℓ) (r : AuxList 𝒢.big (𝔉 ν).C),
    𝔭.shift (k * dil (𝔉 ν).C x r) n ∈ Q}

/-- The positions from which a transition of `𝒜*` reaches `Q`. -/
def adjReach (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (Q : Set 𝔭.Pos) : Set 𝔭.Pos :=
  {n | ∃ (ν : N) (x : Lists 𝒢 J ℓ) (r : AuxList 𝒢.big (𝔉 ν).C),
    𝔭.shift (-(k * dil (𝔉 ν).C x r)) n ∈ Q}

variable {𝔭 𝒢}

omit [DecidableEq S] [DecidableEq B] in
/-- Finitely many positions are reached from finitely many positions: every row of `𝒜` is
finite. -/
theorem fwdReach_finite (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) {Q : Set 𝔭.Pos} (hQ : Q.Finite) :
    (fwdReach 𝔭 𝒢 𝔉 k Q).Finite := by
  have h : fwdReach 𝔭 𝒢 𝔉 k Q ⊆
      ⋃ (ν : N), ⋃ (x : Lists 𝒢 J ℓ), ⋃ (r : AuxList 𝒢.big (𝔉 ν).C),
        (𝔭.shift (-(k * dil (𝔉 ν).C x r))) '' Q := by
    rintro n ⟨ν, x, r, hmem⟩
    exact Set.mem_iUnion.mpr ⟨ν, Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr
      ⟨r, _, hmem, 𝔭.shift_neg_shift _ _⟩⟩⟩
  exact (Set.finite_iUnion fun ν => Set.finite_iUnion fun x => Set.finite_iUnion fun r =>
    hQ.image _).subset h

omit [DecidableEq S] [DecidableEq B] in
/-- Every column of `𝒜` is finite. -/
theorem adjReach_finite (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) {Q : Set 𝔭.Pos} (hQ : Q.Finite) :
    (adjReach 𝔭 𝒢 𝔉 k Q).Finite := by
  have h : adjReach 𝔭 𝒢 𝔉 k Q ⊆
      ⋃ (ν : N), ⋃ (x : Lists 𝒢 J ℓ), ⋃ (r : AuxList 𝒢.big (𝔉 ν).C),
        (𝔭.shift (k * dil (𝔉 ν).C x r)) '' Q := by
    rintro n ⟨ν, x, r, hmem⟩
    exact Set.mem_iUnion.mpr ⟨ν, Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr
      ⟨r, _, hmem, 𝔭.shift_shift_neg _ _⟩⟩⟩
  exact (Set.finite_iUnion fun ν => Set.finite_iUnion fun x => Set.finite_iUnion fun r =>
    hQ.image _).subset h

theorem posSupp_physOp_fwdReach (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    {u : PState 𝔭 𝒢 J ℓ → ℂ} {Q : Set 𝔭.Pos} (h : PosSupp 𝔭 𝒢 J ℓ u Q) :
    PosSupp 𝔭 𝒢 J ℓ (physOp 𝔭 𝒢 q 𝔉 k ζ u) (fwdReach 𝔭 𝒢 𝔉 k Q) :=
  posSupp_physOp 𝔉 k ζ h fun ν _ x r hmem => ⟨ν, x, r, hmem⟩

theorem posSupp_physAdj_adjReach (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    {u : PState 𝔭 𝒢 J ℓ → ℂ} {Q : Set 𝔭.Pos} (h : PosSupp 𝔭 𝒢 J ℓ u Q) :
    PosSupp 𝔭 𝒢 J ℓ (physAdj 𝔭 𝒢 q 𝔉 k ζ u) (adjReach 𝔭 𝒢 𝔉 k Q) :=
  posSupp_physAdj 𝔉 k ζ h fun ν _ x r hmem => ⟨ν, x, r, hmem⟩

end Rows

/-! ### The inner product of `ℋ_ph` -/

section Global

variable (𝔭 : PosModel) (𝒢 : GroupFamily S B) (J ℓ : ℕ)

/-- **The inner product `⟨u, v⟩` of `ℋ_ph`**, as the finite sum over the positions of the inner
products at one position. It is meaningful when `u` or `v` vanishes outside finitely many
positions (`gp_eq_sum_left`, `gp_eq_sum_right`). -/
def gp (u v : PState 𝔭 𝒢 J ℓ → ℂ) : ℂ := ∑ᶠ n : 𝔭.Pos, fib 𝔭 𝒢 J ℓ n u v

/-- **The square of the norm `‖u‖²` of `ℋ_ph`** for `u` vanishing outside finitely many
positions. -/
def gsq (u : PState 𝔭 𝒢 J ℓ → ℂ) : ℝ := ∑ᶠ n : 𝔭.Pos, fibSq 𝔭 𝒢 J ℓ n u

variable {𝔭 𝒢 J ℓ}

theorem gp_eq_sum_left {u : PState 𝔭 𝒢 J ℓ → ℂ} (T : Finset 𝔭.Pos)
    (h : PosSupp 𝔭 𝒢 J ℓ u ↑T) (v : PState 𝔭 𝒢 J ℓ → ℂ) :
    gp 𝔭 𝒢 J ℓ u v = ∑ n ∈ T, fib 𝔭 𝒢 J ℓ n u v :=
  finsum_eq_sum_of_support_subset _ fun n hn => by
    by_contra hnT
    exact hn (posSupp_fib_left h hnT v)

theorem gp_eq_sum_right {v : PState 𝔭 𝒢 J ℓ → ℂ} (T : Finset 𝔭.Pos)
    (h : PosSupp 𝔭 𝒢 J ℓ v ↑T) (u : PState 𝔭 𝒢 J ℓ → ℂ) :
    gp 𝔭 𝒢 J ℓ u v = ∑ n ∈ T, fib 𝔭 𝒢 J ℓ n u v :=
  finsum_eq_sum_of_support_subset _ fun n hn => by
    by_contra hnT
    exact hn (posSupp_fib_right h hnT u)

theorem gsq_eq_sum {u : PState 𝔭 𝒢 J ℓ → ℂ} (T : Finset 𝔭.Pos) (h : PosSupp 𝔭 𝒢 J ℓ u ↑T) :
    gsq 𝔭 𝒢 J ℓ u = ∑ n ∈ T, fibSq 𝔭 𝒢 J ℓ n u :=
  finsum_eq_sum_of_support_subset _ fun n hn => by
    by_contra hnT
    exact hn (posSupp_fibSq h hnT)

theorem gsq_nonneg {u : PState 𝔭 𝒢 J ℓ → ℂ} (T : Finset 𝔭.Pos) (h : PosSupp 𝔭 𝒢 J ℓ u ↑T) :
    0 ≤ gsq 𝔭 𝒢 J ℓ u := by
  rw [gsq_eq_sum T h]
  exact Finset.sum_nonneg fun n _ => fibSq_nonneg n u

/-- `⟨u, u⟩ = ‖u‖²`. -/
theorem gp_self {u : PState 𝔭 𝒢 J ℓ → ℂ} (T : Finset 𝔭.Pos) (h : PosSupp 𝔭 𝒢 J ℓ u ↑T) :
    gp 𝔭 𝒢 J ℓ u u = (gsq 𝔭 𝒢 J ℓ u : ℂ) := by
  rw [gp_eq_sum_left T h, gsq_eq_sum T h, Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun n _ => fib_self n u

/-- `conj ⟨u, v⟩ = ⟨v, u⟩`. -/
theorem gp_conj {u : PState 𝔭 𝒢 J ℓ → ℂ} (T : Finset 𝔭.Pos) (h : PosSupp 𝔭 𝒢 J ℓ u ↑T)
    (v : PState 𝔭 𝒢 J ℓ → ℂ) : conj (gp 𝔭 𝒢 J ℓ u v) = gp 𝔭 𝒢 J ℓ v u := by
  rw [gp_eq_sum_left T h, gp_eq_sum_right T h, map_sum]
  exact Finset.sum_congr rfl fun n _ => fib_conj n u v

theorem gp_sum_right {ι : Type*} (s : Finset ι) {u : PState 𝔭 𝒢 J ℓ → ℂ} {Q : Set 𝔭.Pos}
    (hQ : Q.Finite) (hu : PosSupp 𝔭 𝒢 J ℓ u Q) (w : ι → PState 𝔭 𝒢 J ℓ → ℂ) :
    gp 𝔭 𝒢 J ℓ u (∑ i ∈ s, w i) = ∑ i ∈ s, gp 𝔭 𝒢 J ℓ u (w i) :=
  calc gp 𝔭 𝒢 J ℓ u (∑ i ∈ s, w i)
      = ∑ᶠ n : 𝔭.Pos, ∑ i ∈ s, fib 𝔭 𝒢 J ℓ n u (w i) :=
        finsum_congr fun n => fib_sum_right s n u w
    _ = ∑ i ∈ s, ∑ᶠ n : 𝔭.Pos, fib 𝔭 𝒢 J ℓ n u (w i) :=
        finsum_sum_comm s _ fun i _ => hQ.subset fun n hn => by
          by_contra hnQ
          exact hn (posSupp_fib_left hu hnQ (w i))

theorem gp_sum_left {ι : Type*} (s : Finset ι) {w : ι → PState 𝔭 𝒢 J ℓ → ℂ} {Q : Set 𝔭.Pos}
    (hQ : Q.Finite) (hw : ∀ i ∈ s, PosSupp 𝔭 𝒢 J ℓ (w i) Q) (v : PState 𝔭 𝒢 J ℓ → ℂ) :
    gp 𝔭 𝒢 J ℓ (∑ i ∈ s, w i) v = ∑ i ∈ s, gp 𝔭 𝒢 J ℓ (w i) v :=
  calc gp 𝔭 𝒢 J ℓ (∑ i ∈ s, w i) v
      = ∑ᶠ n : 𝔭.Pos, ∑ i ∈ s, fib 𝔭 𝒢 J ℓ n (w i) v :=
        finsum_congr fun n => fib_sum_left s n w v
    _ = ∑ i ∈ s, ∑ᶠ n : 𝔭.Pos, fib 𝔭 𝒢 J ℓ n (w i) v :=
        finsum_sum_comm s _ fun i hi => hQ.subset fun n hn => by
          by_contra hnQ
          exact hn (posSupp_fib_left (hw i hi) hnQ v)

/-- **The symmetrizing projection is self-adjoint** [S-02:0129–0130]. -/
theorem gp_physSym (u v : PState 𝔭 𝒢 J ℓ → ℂ) :
    gp 𝔭 𝒢 J ℓ u (physSym 𝔭 𝒢 J ℓ v) = gp 𝔭 𝒢 J ℓ (physSym 𝔭 𝒢 J ℓ u) v :=
  finsum_congr fun n => fib_physSym n u v

/-- `⟨u_n, G⟩` is the inner product of `u_n` and `G`. -/
theorem gp_physUnit_left (n : 𝔭.Pos) (G : PState 𝔭 𝒢 J ℓ → ℂ) :
    gp 𝔭 𝒢 J ℓ (physUnit 𝔭 𝒢 J ℓ n) G = pairUnit 𝔭 𝒢 J ℓ n G := by
  have h : PosSupp 𝔭 𝒢 J ℓ (physUnit 𝔭 𝒢 J ℓ n) ↑({n} : Finset 𝔭.Pos) := by
    rw [Finset.coe_singleton]
    exact posSupp_physUnit n
  rw [gp_eq_sum_left {n} h, Finset.sum_singleton, fib_physUnit_self]

theorem fibSq_eq_sum_physDensity (n : 𝔭.Pos) (g : PState 𝔭 𝒢 J ℓ → ℂ) :
    fibSq 𝔭 𝒢 J ℓ n g = ∑ x : Lists 𝒢 J ℓ, physDensity 𝔭 𝒢 J ℓ g (n, x) := by
  unfold fibSq
  exact Finset.sum_congr rfl fun x _ => (physDensity_eq 𝔭 𝒢 J ℓ g (n, x)).symm

omit [DecidableEq S] [DecidableEq B] in
theorem physDensity_nonneg (g : PState 𝔭 𝒢 J ℓ → ℂ) (s : PState 𝔭 𝒢 J ℓ) :
    0 ≤ physDensity 𝔭 𝒢 J ℓ g s := by
  rw [physDensity_eq]
  exact mul_nonneg (physWeight_nonneg 𝔭 𝒢 J ℓ s) (sq_nonneg _)

omit [DecidableEq S] [DecidableEq B] in
theorem physNormSq_nonneg (g : PState 𝔭 𝒢 J ℓ → ℂ) : 0 ≤ physNormSq 𝔭 𝒢 J ℓ g :=
  tsum_nonneg fun s => physDensity_nonneg g s

/-- For `g ∈ ℋ_ph`, the part of `‖g‖²` on finitely many positions is at most `‖g‖²`. -/
theorem sum_fibSq_le_physNormSq {g : PState 𝔭 𝒢 J ℓ → ℂ} (hg : MemPhysL2 𝔭 𝒢 J ℓ g)
    (U : Finset 𝔭.Pos) : ∑ n ∈ U, fibSq 𝔭 𝒢 J ℓ n g ≤ physNormSq 𝔭 𝒢 J ℓ g := by
  have h1 : ∑ n ∈ U, fibSq 𝔭 𝒢 J ℓ n g =
      ∑ s ∈ U ×ˢ (Finset.univ : Finset (Lists 𝒢 J ℓ)), physDensity 𝔭 𝒢 J ℓ g s := by
    rw [Finset.sum_product]
    exact Finset.sum_congr rfl fun n _ => fibSq_eq_sum_physDensity n g
  rw [h1]
  exact Summable.sum_le_tsum _ (fun s _ => physDensity_nonneg g s) hg

end Global

/-! ### Adjointness before symmetrization -/

section RowAdjoint

variable (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ}

/-- Translation by `h` as a bijection of the positions. -/
def shiftEquiv (h : ℤ) : 𝔭.Pos ≃ 𝔭.Pos where
  toFun := 𝔭.shift h
  invFun := 𝔭.shift (-h)
  left_inv := 𝔭.shift_neg_shift h
  right_inv := 𝔭.shift_shift_neg h

/-- The contribution to `⟨u, R_ν v⟩` of the transition from `(n, x)` with auxiliary labels `ξ.1`
to the list `ξ.2`. -/
def fwdTerm (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (u v : PState 𝔭 𝒢 J ℓ → ℂ) (n : 𝔭.Pos)
    (x : Lists 𝒢 J ℓ) (ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ) : ℂ :=
  (physWeight 𝔭 𝒢 J ℓ (n, x) : ℂ) * (conj (u (n, x)) *
    (physCoef 𝔭 𝒢 q ν k ζ n x ξ.1 ξ.2 * v (𝔭.shift (k * dil ν.C x ξ.1) n, ξ.2)))

/-- The contribution to `⟨R_ν* u, v⟩` of the adjoint transition from `(n, x)` with auxiliary
labels `ξ.1` to the list `ξ.2`. -/
def bwdTerm (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (u v : PState 𝔭 𝒢 J ℓ → ℂ) (n : 𝔭.Pos)
    (x : Lists 𝒢 J ℓ) (ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ) : ℂ :=
  (physWeight 𝔭 𝒢 J ℓ (n, x) : ℂ) *
    ((physCoef 𝔭 𝒢 q ν k ζ (𝔭.shift (-(k * dil ν.C x ξ.1)) n) ξ.2 ξ.1 x *
      conj (u (𝔭.shift (-(k * dil ν.C x ξ.1)) n, ξ.2))) * v (n, x))

variable {𝔭 𝒢 q}

theorem fib_physRow_eq (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (u v : PState 𝔭 𝒢 J ℓ → ℂ)
    (n : 𝔭.Pos) :
    fib 𝔭 𝒢 J ℓ n u (physRow 𝔭 𝒢 q ν k ζ v) =
      ∑ x : Lists 𝒢 J ℓ, ∑ ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ,
        fwdTerm 𝔭 𝒢 q ν k ζ u v n x ξ := by
  unfold fib fwdTerm
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [physRow_apply_mk, Finset.mul_sum, Finset.mul_sum]

theorem fib_physRowAdj_eq (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (u v : PState 𝔭 𝒢 J ℓ → ℂ)
    (n : 𝔭.Pos) :
    fib 𝔭 𝒢 J ℓ n (physRowAdj 𝔭 𝒢 q ν k ζ u) v =
      ∑ x : Lists 𝒢 J ℓ, ∑ ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ,
        bwdTerm 𝔭 𝒢 q ν k ζ u v n x ξ := by
  unfold fib bwdTerm
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [physRowAdj_apply_mk, map_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  rw [map_mul, starRingEnd_self_apply]

omit [DecidableEq S] [DecidableEq B] in
theorem fwdTerm_eq_zero (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) {u : PState 𝔭 𝒢 J ℓ → ℂ}
    (v : PState 𝔭 𝒢 J ℓ → ℂ) {n : 𝔭.Pos} {x : Lists 𝒢 J ℓ}
    (ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ) (h : u (n, x) = 0) :
    fwdTerm 𝔭 𝒢 q ν k ζ u v n x ξ = 0 := by
  unfold fwdTerm
  rw [h, map_zero, zero_mul, mul_zero]

omit [DecidableEq S] [DecidableEq B] in
theorem bwdTerm_eq_zero (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) {u : PState 𝔭 𝒢 J ℓ → ℂ}
    (v : PState 𝔭 𝒢 J ℓ → ℂ) {n : 𝔭.Pos} {x : Lists 𝒢 J ℓ}
    {ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ}
    (h : u (𝔭.shift (-(k * dil ν.C x ξ.1)) n, ξ.2) = 0) :
    bwdTerm 𝔭 𝒢 q ν k ζ u v n x ξ = 0 := by
  unfold bwdTerm
  rw [h, map_zero, mul_zero, zero_mul, mul_zero]

omit [DecidableEq S] [DecidableEq B] in
/-- Both endpoints of a transition with nonzero coefficient are physical. -/
theorem isPhys_of_physCoef_ne_zero {ν : Pattern 𝒢.big J ℓ} {k : ℤ} {ζ : ℝ} {n : 𝔭.Pos}
    {x x' : Lists 𝒢 J ℓ} {r : AuxList 𝒢.big ν.C} (h : physCoef 𝔭 𝒢 q ν k ζ n x r x' ≠ 0) :
    IsPhys 𝔭 n x ∧ IsPhys 𝔭 (𝔭.shift (k * dil ν.C x r) n) x' := by
  by_contra hc
  exact h (Schur.physCoef_eq_zero_of_not fun hcond => hc ⟨hcond.1, hcond.2.1⟩)

omit [DecidableEq S] [DecidableEq B] in
/-- **A transition and its reversal** [S-02:0120–0127]: when the dilation computed from the target
list equals the dilation computed from the source list, the contribution of the transition
`(n, x) → (n + kD, x')` to `⟨u, R_ν v⟩` is the contribution of the adjoint transition
`(n + kD, x') → (n, x)` to `⟨R_ν* u, v⟩`. -/
theorem fwdTerm_eq_bwdTerm_shift (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    (u v : PState 𝔭 𝒢 J ℓ → ℂ) (x x' : Lists 𝒢 J ℓ) (r : AuxList 𝒢.big ν.C)
    (hD : dil ν.C x' r = dil ν.C x r) (n : 𝔭.Pos) :
    fwdTerm 𝔭 𝒢 q ν k ζ u v n x (r, x') =
      bwdTerm 𝔭 𝒢 q ν k ζ u v (𝔭.shift (k * dil ν.C x r) n) x' (r, x) := by
  show (physWeight 𝔭 𝒢 J ℓ (n, x) : ℂ) * (conj (u (n, x)) *
        (physCoef 𝔭 𝒢 q ν k ζ n x r x' * v (𝔭.shift (k * dil ν.C x r) n, x'))) =
      (physWeight 𝔭 𝒢 J ℓ (𝔭.shift (k * dil ν.C x r) n, x') : ℂ) *
        ((physCoef 𝔭 𝒢 q ν k ζ
            (𝔭.shift (-(k * dil ν.C x' r)) (𝔭.shift (k * dil ν.C x r) n)) x r x' *
          conj (u (𝔭.shift (-(k * dil ν.C x' r)) (𝔭.shift (k * dil ν.C x r) n), x))) *
            v (𝔭.shift (k * dil ν.C x r) n, x'))
  rw [hD, 𝔭.shift_neg_shift]
  by_cases hc : physCoef 𝔭 𝒢 q ν k ζ n x r x' = 0
  · rw [hc]
    ring
  · obtain ⟨h1, h2⟩ := isPhys_of_physCoef_ne_zero hc
    rw [physWeight_of_isPhys h1, physWeight_of_isPhys h2]
    ring

omit [DecidableEq S] [DecidableEq B] in
/-- The sums over the positions of the two contributions agree. -/
theorem finsum_fwdTerm_eq (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (u v : PState 𝔭 𝒢 J ℓ → ℂ)
    (x x' : Lists 𝒢 J ℓ) (r : AuxList 𝒢.big ν.C) :
    ∑ᶠ n : 𝔭.Pos, fwdTerm 𝔭 𝒢 q ν k ζ u v n x (r, x') =
      ∑ᶠ n : 𝔭.Pos, bwdTerm 𝔭 𝒢 q ν k ζ u v n x' (r, x) := by
  by_cases hD : dil ν.C x' r = dil ν.C x r
  · rw [finsum_congr (fwdTerm_eq_bwdTerm_shift ν k ζ u v x x' r hD)]
    exact finsum_comp_equiv (shiftEquiv 𝔭 (k * dil ν.C x r))
      (f := fun n => bwdTerm 𝔭 𝒢 q ν k ζ u v n x' (r, x))
  · have hz : ∀ n : 𝔭.Pos, physCoef 𝔭 𝒢 q ν k ζ n x r x' = 0 := by
      intro n
      by_contra hne
      exact hD (dil_eq_of_physCoef_ne_zero hne)
    have h1 : ∀ n : 𝔭.Pos, fwdTerm 𝔭 𝒢 q ν k ζ u v n x (r, x') = 0 := by
      intro n
      show (physWeight 𝔭 𝒢 J ℓ (n, x) : ℂ) * (conj (u (n, x)) *
        (physCoef 𝔭 𝒢 q ν k ζ n x r x' * v (𝔭.shift (k * dil ν.C x r) n, x'))) = 0
      rw [hz]
      ring
    have h2 : ∀ n : 𝔭.Pos, bwdTerm 𝔭 𝒢 q ν k ζ u v n x' (r, x) = 0 := by
      intro n
      show (physWeight 𝔭 𝒢 J ℓ (n, x') : ℂ) *
        ((physCoef 𝔭 𝒢 q ν k ζ (𝔭.shift (-(k * dil ν.C x' r)) n) x r x' *
          conj (u (𝔭.shift (-(k * dil ν.C x' r)) n, x))) * v (n, x')) = 0
      rw [hz]
      ring
    rw [finsum_congr h1, finsum_congr h2]

/-- **Adjointness before symmetrization** [S-02:0120–0129]: `⟨u, R_ν v⟩ = ⟨R_ν* u, v⟩` for the row
operation `R_ν` of a pattern, when `u` vanishes outside finitely many positions. -/
theorem gp_physRow (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) {u : PState 𝔭 𝒢 J ℓ → ℂ}
    {Q : Set 𝔭.Pos} (hQ : Q.Finite) (hu : PosSupp 𝔭 𝒢 J ℓ u Q) (v : PState 𝔭 𝒢 J ℓ → ℂ) :
    gp 𝔭 𝒢 J ℓ u (physRow 𝔭 𝒢 q ν k ζ v) = gp 𝔭 𝒢 J ℓ (physRowAdj 𝔭 𝒢 q ν k ζ u) v := by
  have hsL : ∀ (x : Lists 𝒢 J ℓ) (ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ),
      (Function.support fun n : 𝔭.Pos => fwdTerm 𝔭 𝒢 q ν k ζ u v n x ξ) ⊆ Q := by
    intro x ξ n hn
    by_contra hnQ
    exact hn (fwdTerm_eq_zero ν k ζ v ξ (hu n x hnQ))
  have hsL' : ∀ x : Lists 𝒢 J ℓ,
      (Function.support fun n : 𝔭.Pos =>
        ∑ ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ, fwdTerm 𝔭 𝒢 q ν k ζ u v n x ξ) ⊆ Q := by
    intro x n hn
    by_contra hnQ
    exact hn (Finset.sum_eq_zero fun ξ _ => fwdTerm_eq_zero ν k ζ v ξ (hu n x hnQ))
  have hsR : ∀ (x : Lists 𝒢 J ℓ) (ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ),
      (Function.support fun n : 𝔭.Pos => bwdTerm 𝔭 𝒢 q ν k ζ u v n x ξ) ⊆
        (𝔭.shift (k * dil ν.C x ξ.1)) '' Q := by
    intro x ξ n hn
    by_contra hnQ
    exact hn (bwdTerm_eq_zero ν k ζ v
      (hu _ ξ.2 fun hmem => hnQ ⟨_, hmem, 𝔭.shift_shift_neg _ _⟩))
  have hsR' : ∀ x : Lists 𝒢 J ℓ,
      (Function.support fun n : 𝔭.Pos =>
        ∑ ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ, bwdTerm 𝔭 𝒢 q ν k ζ u v n x ξ) ⊆
        ⋃ ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ, (𝔭.shift (k * dil ν.C x ξ.1)) '' Q := by
    intro x n hn
    by_contra hnQ
    exact hn (Finset.sum_eq_zero fun ξ _ => bwdTerm_eq_zero ν k ζ v
      (hu _ ξ.2 fun hmem => hnQ (Set.mem_iUnion.mpr ⟨ξ, _, hmem, 𝔭.shift_shift_neg _ _⟩)))
  have e1 : gp 𝔭 𝒢 J ℓ u (physRow 𝔭 𝒢 q ν k ζ v) =
      ∑ x : Lists 𝒢 J ℓ, ∑ ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ,
        ∑ᶠ n : 𝔭.Pos, fwdTerm 𝔭 𝒢 q ν k ζ u v n x ξ :=
    calc gp 𝔭 𝒢 J ℓ u (physRow 𝔭 𝒢 q ν k ζ v)
        = ∑ᶠ n : 𝔭.Pos, ∑ x : Lists 𝒢 J ℓ, ∑ ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ,
            fwdTerm 𝔭 𝒢 q ν k ζ u v n x ξ :=
          finsum_congr fun n => fib_physRow_eq ν k ζ u v n
      _ = ∑ x : Lists 𝒢 J ℓ, ∑ᶠ n : 𝔭.Pos, ∑ ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ,
            fwdTerm 𝔭 𝒢 q ν k ζ u v n x ξ :=
          finsum_sum_comm Finset.univ _ fun x _ => hQ.subset (hsL' x)
      _ = ∑ x : Lists 𝒢 J ℓ, ∑ ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ,
            ∑ᶠ n : 𝔭.Pos, fwdTerm 𝔭 𝒢 q ν k ζ u v n x ξ :=
          Finset.sum_congr rfl fun x _ =>
            finsum_sum_comm Finset.univ _ fun ξ _ => hQ.subset (hsL x ξ)
  have e2 : gp 𝔭 𝒢 J ℓ (physRowAdj 𝔭 𝒢 q ν k ζ u) v =
      ∑ x : Lists 𝒢 J ℓ, ∑ ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ,
        ∑ᶠ n : 𝔭.Pos, bwdTerm 𝔭 𝒢 q ν k ζ u v n x ξ :=
    calc gp 𝔭 𝒢 J ℓ (physRowAdj 𝔭 𝒢 q ν k ζ u) v
        = ∑ᶠ n : 𝔭.Pos, ∑ x : Lists 𝒢 J ℓ, ∑ ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ,
            bwdTerm 𝔭 𝒢 q ν k ζ u v n x ξ :=
          finsum_congr fun n => fib_physRowAdj_eq ν k ζ u v n
      _ = ∑ x : Lists 𝒢 J ℓ, ∑ᶠ n : 𝔭.Pos, ∑ ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ,
            bwdTerm 𝔭 𝒢 q ν k ζ u v n x ξ :=
          finsum_sum_comm Finset.univ _ fun x _ =>
            (Set.finite_iUnion fun ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ =>
              hQ.image (𝔭.shift (k * dil ν.C x ξ.1))).subset (hsR' x)
      _ = ∑ x : Lists 𝒢 J ℓ, ∑ ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ,
            ∑ᶠ n : 𝔭.Pos, bwdTerm 𝔭 𝒢 q ν k ζ u v n x ξ :=
          Finset.sum_congr rfl fun x _ =>
            finsum_sum_comm Finset.univ _ fun ξ _ => (hQ.image _).subset (hsR x ξ)
  let σ : Lists 𝒢 J ℓ × (AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ) ≃
      Lists 𝒢 J ℓ × (AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ) :=
    ⟨fun p => (p.2.2, (p.2.1, p.1)), fun p => (p.2.2, (p.2.1, p.1)), fun _ => rfl, fun _ => rfl⟩
  rw [e1, e2]
  calc ∑ x : Lists 𝒢 J ℓ, ∑ ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ,
        ∑ᶠ n : 𝔭.Pos, fwdTerm 𝔭 𝒢 q ν k ζ u v n x ξ
      = ∑ p : Lists 𝒢 J ℓ × (AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ),
          ∑ᶠ n : 𝔭.Pos, fwdTerm 𝔭 𝒢 q ν k ζ u v n p.1 p.2 :=
        (Fintype.sum_prod_type' fun (x : Lists 𝒢 J ℓ)
          (ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ) =>
            ∑ᶠ n : 𝔭.Pos, fwdTerm 𝔭 𝒢 q ν k ζ u v n x ξ).symm
    _ = ∑ p : Lists 𝒢 J ℓ × (AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ),
          ∑ᶠ n : 𝔭.Pos, bwdTerm 𝔭 𝒢 q ν k ζ u v n p.1 p.2 :=
        Fintype.sum_equiv σ _ _ fun p => finsum_fwdTerm_eq ν k ζ u v p.1 p.2.2 p.2.1
    _ = ∑ x : Lists 𝒢 J ℓ, ∑ ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ,
          ∑ᶠ n : 𝔭.Pos, bwdTerm 𝔭 𝒢 q ν k ζ u v n x ξ :=
        Fintype.sum_prod_type' fun (x : Lists 𝒢 J ℓ)
          (ξ : AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ) =>
            ∑ᶠ n : 𝔭.Pos, bwdTerm 𝔭 𝒢 q ν k ζ u v n x ξ

end RowAdjoint

/-! ### `𝒜*` is the adjoint of `𝒜` -/

section Adjoint

variable {𝔭 : PosModel} {𝒢 : GroupFamily S B} {q : ℝ} {J ℓ : ℕ} {N : Type} [Fintype N]

/-- **`⟨u, 𝒜 v⟩ = ⟨𝒜* u, v⟩`** [S-02:0120–0130], for `u` vanishing outside finitely many positions
and an arbitrary function `v` on the states. -/
theorem gp_physOp (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) {u : PState 𝔭 𝒢 J ℓ → ℂ}
    {Q : Set 𝔭.Pos} (hQ : Q.Finite) (hu : PosSupp 𝔭 𝒢 J ℓ u Q) (v : PState 𝔭 𝒢 J ℓ → ℂ) :
    gp 𝔭 𝒢 J ℓ u (physOp 𝔭 𝒢 q 𝔉 k ζ v) = gp 𝔭 𝒢 J ℓ (physAdj 𝔭 𝒢 q 𝔉 k ζ u) v := by
  have hsu : PosSupp 𝔭 𝒢 J ℓ (physSym 𝔭 𝒢 J ℓ u) Q := posSupp_physSym hu
  have hQ' : (adjReach 𝔭 𝒢 𝔉 k Q).Finite := adjReach_finite 𝔉 k hQ
  have hrow : ∀ ν ∈ (Finset.univ : Finset N),
      PosSupp 𝔭 𝒢 J ℓ (physRowAdj 𝔭 𝒢 q (𝔉 ν) k ζ (physSym 𝔭 𝒢 J ℓ u))
        (adjReach 𝔭 𝒢 𝔉 k Q) :=
    fun ν _ => posSupp_physRowAdj (𝔉 ν) k ζ hsu fun _ x r hmem => ⟨ν, x, r, hmem⟩
  calc gp 𝔭 𝒢 J ℓ u (physOp 𝔭 𝒢 q 𝔉 k ζ v)
      = gp 𝔭 𝒢 J ℓ u
          (physSym 𝔭 𝒢 J ℓ (∑ ν, physRow 𝔭 𝒢 q (𝔉 ν) k ζ (physSym 𝔭 𝒢 J ℓ v))) := by
        rw [physOp_apply]
    _ = gp 𝔭 𝒢 J ℓ (physSym 𝔭 𝒢 J ℓ u)
          (∑ ν, physRow 𝔭 𝒢 q (𝔉 ν) k ζ (physSym 𝔭 𝒢 J ℓ v)) := gp_physSym _ _
    _ = ∑ ν, gp 𝔭 𝒢 J ℓ (physSym 𝔭 𝒢 J ℓ u)
          (physRow 𝔭 𝒢 q (𝔉 ν) k ζ (physSym 𝔭 𝒢 J ℓ v)) :=
        gp_sum_right Finset.univ hQ hsu _
    _ = ∑ ν, gp 𝔭 𝒢 J ℓ (physRowAdj 𝔭 𝒢 q (𝔉 ν) k ζ (physSym 𝔭 𝒢 J ℓ u))
          (physSym 𝔭 𝒢 J ℓ v) :=
        Finset.sum_congr rfl fun ν _ => gp_physRow (𝔉 ν) k ζ hQ hsu _
    _ = gp 𝔭 𝒢 J ℓ (∑ ν, physRowAdj 𝔭 𝒢 q (𝔉 ν) k ζ (physSym 𝔭 𝒢 J ℓ u))
          (physSym 𝔭 𝒢 J ℓ v) := (gp_sum_left Finset.univ hQ' hrow _).symm
    _ = gp 𝔭 𝒢 J ℓ
          (physSym 𝔭 𝒢 J ℓ (∑ ν, physRowAdj 𝔭 𝒢 q (𝔉 ν) k ζ (physSym 𝔭 𝒢 J ℓ u))) v :=
        gp_physSym _ _
    _ = gp 𝔭 𝒢 J ℓ (physAdj 𝔭 𝒢 q 𝔉 k ζ u) v := by rw [physAdj_apply]

/-- **`⟨𝒜 a, b⟩ = ⟨a, 𝒜* b⟩`**, for `b` vanishing outside finitely many positions. -/
theorem gp_physOp_left (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) {b : PState 𝔭 𝒢 J ℓ → ℂ}
    {Q : Set 𝔭.Pos} (hQ : Q.Finite) (hb : PosSupp 𝔭 𝒢 J ℓ b Q) (a : PState 𝔭 𝒢 J ℓ → ℂ) :
    gp 𝔭 𝒢 J ℓ (physOp 𝔭 𝒢 q 𝔉 k ζ a) b = gp 𝔭 𝒢 J ℓ a (physAdj 𝔭 𝒢 q 𝔉 k ζ b) := by
  have hb' : PosSupp 𝔭 𝒢 J ℓ b ↑hQ.toFinset := by rwa [Set.Finite.coe_toFinset]
  have hQ' : (adjReach 𝔭 𝒢 𝔉 k Q).Finite := adjReach_finite 𝔉 k hQ
  have hAb : PosSupp 𝔭 𝒢 J ℓ (physAdj 𝔭 𝒢 q 𝔉 k ζ b) ↑hQ'.toFinset := by
    rw [Set.Finite.coe_toFinset]
    exact posSupp_physAdj_adjReach 𝔉 k ζ hb
  rw [← gp_conj hQ.toFinset hb', gp_physOp 𝔉 k ζ hQ hb a, gp_conj hQ'.toFinset hAb]

end Adjoint

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Pairing
