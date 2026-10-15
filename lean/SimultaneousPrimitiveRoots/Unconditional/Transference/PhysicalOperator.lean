module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.FiniteOperators
public import SimultaneousPrimitiveRoots.Unconditional.Transference.PrimeGroups
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.Ring

/-!
# The physical operator `𝒜`, its adjoint and the moment ([S] Definition 3.3)

Source: `verification/stage7-sources/S-02.tex`, lines 98–130 (`[S-02:0098–0130]`), and the moment
(eq:transference-moment), lines 175–183.

A *physical state* `(n, 𝐩)` consists of a position `n` and an ordered list `𝐩 = (p_{g,i})` with
`M` slots in every (small and big) group, the labels of one group being distinct and dividing `n`.
Every state has mass `∏_g V_g^{-M}`; positions carry counting measure. This is `ℋ_ph`.

* `PosModel`, `intPos`, `residuePos` — the position. The paper uses `n ∈ ℤ` (`intPos`). The
  second assertion of Lemma 3.4 ("the position is replaced by independent uniform residues at all
  group primes") and the proof of Theorem 3.5 use the residue model (`residuePos`). All
  definitions below take a position model, since they use "no property of integer positions
  beyond divisibility and translation" [S-02:0156–0157].
* `IsPhys`, `stateMass`, `physUnit`, `pairUnit` — physical states, their mass, the vector `u_n`
  and the inner product `⟨u_n, ·⟩` of `ℋ_ph`.
* `physCoef`, `physRow`, `physSym`, `physOp` — the row transition of a pattern, symmetrization in
  all groups, and `𝒜`.
* `physRowAdj`, `physAdj` — the adjoint `𝒜*` as described in [S-02:0120–0130]: it "moves by
  `-kD`, interchanges source and target labels in the coefficient, and conjugates the multiplier".
* `physMoment` — `⟨u_n, (𝒜 𝒜*)^R u_n⟩` of (eq:transference-moment), a finite sum.
* `physAbsRowSum`, `physAbsColSum` — the row sums of Lemma 3.4 [S-02:0132–0140].
* `pairMarkFree`, `markFreeNormSq`, `physNormSq`, `MemPhysL2` — the pairing `⟨f, 𝒜 g⟩` and the
  norms of Corollary 3.11 [S-02:1266–1283].

Functions on states are functions on *all* pairs `PState = Pos × Lists`; the operators only read
and produce values at physical states (their coefficients vanish otherwise).

The sanity lemma `physRow_adjoint_entry` proves that, before symmetrization, the matrix entries of
the adjoint row operation are the complex conjugates of the transposed entries of the row
operation. Since all states have the same mass `∏_g V_g^{-M}`, this is the adjoint in `ℋ_ph`;
it is the first assertion of [S-02:0120–0130].
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ### Two finite-sum lemmas for matrix entries -/

theorem sum_ite_prod_mk_eq {Z X M : Type*} [Fintype X] [DecidableEq Z] [DecidableEq X]
    [AddCommMonoid M] (a : Z) (t : Z × X) (f : X → M) :
    (∑ x, if (a, x) = t then f x else 0) = if a = t.1 then f t.2 else 0 := by
  obtain ⟨z, x₀⟩ := t
  by_cases h : a = z
  · subst h
    simp
  · simp [h]

theorem sum_prod_ite_mk_eq {A Z X M : Type*} [Fintype A] [Fintype X] [DecidableEq Z]
    [DecidableEq X] [AddCommMonoid M] (a : A → Z) (t : Z × X) (f : A → X → M) :
    (∑ ξ : A × X, if (a ξ.1, ξ.2) = t then f ξ.1 ξ.2 else 0) =
      ∑ r, if a r = t.1 then f r t.2 else 0 := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun r _ => sum_ite_prod_mk_eq (a r) t (f r)

/-! ### Positions -/

/-- A model of the position coordinate: a type of positions with a divisibility relation
`hit p n` ("`p ∣ n`") and translations `shift h n` ("`n + h`"). -/
structure PosModel where
  /-- the positions -/
  Pos : Type
  /-- `hit p n`: the prime `p` divides the position `n` -/
  hit : ℕ → Pos → Prop
  /-- `shift h n`: the position `n + h` -/
  shift : ℤ → Pos → Pos
  /-- translation by `-h` undoes translation by `h` -/
  shift_neg_shift : ∀ (h : ℤ) (n : Pos), shift (-h) (shift h n) = n

theorem PosModel.shift_shift_neg (𝔭 : PosModel) (h : ℤ) (n : 𝔭.Pos) :
    𝔭.shift h (𝔭.shift (-h) n) = n := by
  have h1 := 𝔭.shift_neg_shift (-h) n
  rwa [neg_neg] at h1

/-- **Integer positions** `n ∈ ℤ` with ordinary divisibility [S-02:0099–0103]. -/
def intPos : PosModel where
  Pos := ℤ
  hit p n := (p : ℤ) ∣ n
  shift h n := n + h
  shift_neg_shift h n := add_neg_cancel_right n h

section Family

variable {S B : Type} [Fintype S] [Fintype B]

/-- All group primes `⋃_g 𝒫_g` [S-02:0047–0048]. -/
def GroupFamily.allPrimes (𝒢 : GroupFamily S B) : Finset ℕ :=
  (Finset.univ.biUnion 𝒢.small) ∪ (Finset.univ.biUnion 𝒢.big)

/-- **Residue positions**: one residue `y_p ∈ ℤ/pℤ` at every group prime `p`
[S-02:0138–0139, 0293–0296]. The prime `p` "divides" `y` when `y_p = 0`; translation by `h`
translates every residue. -/
def residuePos (𝒢 : GroupFamily S B) : PosModel where
  Pos := (p : {p : ℕ // p ∈ 𝒢.allPrimes}) → ZMod p.1
  hit q y := ∃ h : q ∈ 𝒢.allPrimes, y ⟨q, h⟩ = 0
  shift h y := fun p => y p + (h : ZMod p.1)
  shift_neg_shift h y := by
    funext p
    simp

end Family

/-! ### Physical states -/

section Physical

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

/-- The ordered label lists of all groups: `M` slots in every small and every big group. -/
abbrev Lists (𝒢 : GroupFamily S B) (J ℓ : ℕ) : Type :=
  LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ

/-- Decidable equality of the lists, as one named instance: the instance found by unfolding the
nested products and function types is larger than the default `synthInstance.maxSize` once a
position coordinate is added. -/
instance listsDecidableEq (𝒢 : GroupFamily S B) (J ℓ : ℕ) : DecidableEq (Lists 𝒢 J ℓ) :=
  inferInstance

/-- Pairs (position, lists); the physical states are those with `IsPhys`. -/
abbrev PState (𝔭 : PosModel) (𝒢 : GroupFamily S B) (J ℓ : ℕ) : Type := 𝔭.Pos × Lists 𝒢 J ℓ

/-- **Physical state** [S-02:0099–0101]: "within each group, the labels are distinct and divide
`n`". -/
def IsPhys (𝔭 : PosModel) {𝒢 : GroupFamily S B} {J ℓ : ℕ} (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ) : Prop :=
  (∀ g, Function.Injective (x.1 g)) ∧ (∀ g, Function.Injective (x.2 g)) ∧
    (∀ g i, 𝔭.hit (x.1 g i) n) ∧ ∀ g i, 𝔭.hit (x.2 g i) n

/-- The mass `∏_g V_g^{-M}` of every physical state [S-02:0102]; the product is over all small and
big groups and `M = J + ℓ`. -/
def stateMass (𝒢 : GroupFamily S B) (J ℓ : ℕ) : ℝ :=
  (∏ g, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ (J + ℓ))⁻¹) *
    ∏ g, (Graph.primeGroupReciprocalMass (𝒢.big g) ^ (J + ℓ))⁻¹

/-- The coefficient `∏_g V_g^{-t_g}` of every target of a row transition [S-02:0108–0109]:
`t_g = ℓ` for a small group and `t_g = ℓ + |C_g|` for a big group. -/
def targetNorm (𝒢 : GroupFamily S B) {J : ℕ} (ℓ : ℕ) (C : B → Finset (Fin J)) : ℝ :=
  (∏ g, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
    ∏ g, (Graph.primeGroupReciprocalMass (𝒢.big g) ^ (ℓ + (C g).card))⁻¹

omit [DecidableEq S] [DecidableEq B] in
/-- **(eq:physical-joint-measure)** [S-02:0124–0127]: the mass of a state times the coefficient of
a target is `∏_g V_g^{-M-t_g}`, "in either direction". -/
theorem stateMass_mul_targetNorm (𝒢 : GroupFamily S B) (J ℓ : ℕ) (C : B → Finset (Fin J)) :
    stateMass 𝒢 J ℓ * targetNorm 𝒢 ℓ C =
      (∏ g, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ (J + ℓ + ℓ))⁻¹) *
        ∏ g, (Graph.primeGroupReciprocalMass (𝒢.big g) ^ (J + ℓ + (ℓ + (C g).card)))⁻¹ := by
  unfold stateMass targetNorm
  rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  congr 1
  · exact Finset.prod_congr rfl fun g _ => by rw [← mul_inv, ← pow_add]
  · exact Finset.prod_congr rfl fun g _ => by rw [← mul_inv, ← pow_add]

/-- The endpoint damping `q^{(ω(n) - Ms)/2}` of (eq:physical-multiplier) [S-02:0112–0115]. -/
def damping (𝔭 : PosModel) (𝒢 : GroupFamily S B) (J ℓ : ℕ) (q : ℝ) (n : 𝔭.Pos) : ℝ :=
  q ^ ((((𝒢.omegaOf (fun p => 𝔭.hit p n) : ℕ) : ℝ) -
    ((J + ℓ : ℕ) : ℝ) * ((groupCount S B : ℕ) : ℝ)) / 2)

section Coef

variable {𝒢 : GroupFamily S B} {J ℓ : ℕ}

/-- Permute the slots of the small and of the big lists, independently in every group. -/
def permuteLists (π : SlotPerms S J ℓ × SlotPerms B J ℓ) (x : Lists 𝒢 J ℓ) : Lists 𝒢 J ℓ :=
  (permuteSlots π.1 x.1, permuteSlots π.2 x.2)

/-- The dilation `D = D_𝒮 D_ℬ` formed from the shared labels of the lists `x` and the auxiliary
free labels `r` [S-02:0060–0063]. -/
def dil (C : B → Finset (Fin J)) (x : Lists 𝒢 J ℓ) (r : AuxList 𝒢.big C) : ℕ :=
  smallDil x.1 * bigDil C x.2 r

/-- No auxiliary free label of `D` occurs in the lists `x`: the ban of [S-02:0109–0111]
("forbid every auxiliary free label of `D` from both endpoint lists"; it is imposed on the source
and on the target list). Auxiliary free labels may equal one another. -/
def AuxAvoids (C : B → Finset (Fin J)) (r : AuxList 𝒢.big C) (x : Lists 𝒢 J ℓ) : Prop :=
  ∀ (g : B) (i : {i : Fin J // i ∈ C g}),
    (∀ (g' : S) (s : Slot J ℓ), (x.1 g' s : ℕ) ≠ (r g i : ℕ)) ∧
      ∀ (g' : B) (s : Slot J ℓ), (x.2 g' s : ℕ) ≠ (r g i : ℕ)

/-! ### The row transition of a pattern -/

open Classical in
/-- **The coefficient of one row transition of the pattern `ν`** [S-02:0105–0115]: from the
physical source state `(n, x)`, with auxiliary free labels `r`, to the target `(n + kD, x')`,
`D = dil ν.C x r`. It is zero unless both states are physical, the target has the prescribed
shared labels, and no auxiliary label occurs in either list. Otherwise it is the product of

* the probability `auxWeight` of the auxiliary labels,
* the target coefficient `∏_g V_g^{-t_g}` (`targetNorm`),
* the two damping factors `q^{(ω(n) - Ms)/2} q^{(ω(n') - Ms)/2}`,
* the multiplier `K_ν D^{iζ}` (`K_ν` evaluated at the big source labels, the big target labels
  and the auxiliary labels). -/
def physCoef (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ) (r : AuxList 𝒢.big ν.C) (x' : Lists 𝒢 J ℓ) : ℂ :=
  if IsPhys 𝔭 n x ∧ IsPhys 𝔭 (𝔭.shift (k * dil ν.C x r) n) x' ∧
      SharedSmall x.1 x'.1 ∧ SharedBig ν.C x.2 x'.2 ∧
      AuxAvoids ν.C r x ∧ AuxAvoids ν.C r x' then
    ((auxWeight 𝒢.big ν.C r * targetNorm 𝒢 ℓ ν.C *
        (damping 𝔭 𝒢 J ℓ q n * damping 𝔭 𝒢 J ℓ q (𝔭.shift (k * dil ν.C x r) n)) : ℝ) : ℂ) *
      (ν.K x.2 x'.2 r * ((dil ν.C x r : ℕ) : ℂ) ^ ((ζ : ℂ) * Complex.I))
  else 0

omit [DecidableEq S] [DecidableEq B] in
/-- "The shared product and hence `D` are unchanged on reversal" [S-02:0122–0123]: where the
coefficient does not vanish, the dilation computed from the target list equals the dilation
computed from the source list. -/
theorem dil_eq_of_physCoef_ne_zero {𝔭 : PosModel} {q : ℝ} {ν : Pattern 𝒢.big J ℓ} {k : ℤ}
    {ζ : ℝ} {n : 𝔭.Pos} {x x' : Lists 𝒢 J ℓ} {r : AuxList 𝒢.big ν.C}
    (h : physCoef 𝔭 𝒢 q ν k ζ n x r x' ≠ 0) : dil ν.C x' r = dil ν.C x r := by
  unfold physCoef at h
  split_ifs at h with hc
  · unfold dil
    rw [smallDil_eq_of_shared hc.2.2.1, bigDil_eq_of_shared hc.2.2.2.1]
  · exact absurd rfl h

end Coef

section Ops

variable (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ}

/-- **The unsymmetrized row operation of the pattern `ν`** [S-02:0105–0115]:
`(physRow ν g)(n, x) = ∑_{r, x'} physCoef n x r x' * g (n + k D, x')`, `D = dil ν.C x r`. -/
def physRow (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) :
    (PState 𝔭 𝒢 J ℓ → ℂ) →ₗ[ℂ] (PState 𝔭 𝒢 J ℓ → ℂ) :=
  rowOp (Ξ := AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ)
    (fun s ξ => physCoef 𝔭 𝒢 q ν k ζ s.1 s.2 ξ.1 ξ.2)
    (fun s ξ => (𝔭.shift (k * dil ν.C s.2 ξ.1) s.1, ξ.2))

/-- **The adjoint of the unsymmetrized row operation** [S-02:0120–0130]: "the adjoint moves by
`-kD`, interchanges source and target labels in the coefficient, and conjugates the multiplier".
From the state `(n', x')` with auxiliary labels `r` it forms `D = dil ν.C x' r` from its own
shared labels, moves to `n = n' - kD`, and sums over the lists `x` with the conjugate of the
coefficient of the transition `(n, x) → (n', x')`. -/
def physRowAdj (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) :
    (PState 𝔭 𝒢 J ℓ → ℂ) →ₗ[ℂ] (PState 𝔭 𝒢 J ℓ → ℂ) :=
  rowOp (Ξ := AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ)
    (fun s ξ => conj (physCoef 𝔭 𝒢 q ν k ζ (𝔭.shift (-(k * dil ν.C s.2 ξ.1)) s.1) ξ.2 ξ.1 s.2))
    (fun s ξ => (𝔭.shift (-(k * dil ν.C s.2 ξ.1)) s.1, ξ.2))

/-- The row operation of `ν` with its coefficients replaced by their absolute values
(Lemma 3.4, [S-02:0133–0135]). -/
def physRowAbs (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) :
    (PState 𝔭 𝒢 J ℓ → ℂ) →ₗ[ℂ] (PState 𝔭 𝒢 J ℓ → ℂ) :=
  rowOp (Ξ := AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ)
    (fun s ξ => ((‖physCoef 𝔭 𝒢 q ν k ζ s.1 s.2 ξ.1 ξ.2‖ : ℝ) : ℂ))
    (fun s ξ => (𝔭.shift (k * dil ν.C s.2 ξ.1) s.1, ξ.2))

/-- The adjoint row operation of `ν` with its coefficients replaced by their absolute values. -/
def physRowAdjAbs (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) :
    (PState 𝔭 𝒢 J ℓ → ℂ) →ₗ[ℂ] (PState 𝔭 𝒢 J ℓ → ℂ) :=
  rowOp (Ξ := AuxList 𝒢.big ν.C × Lists 𝒢 J ℓ)
    (fun s ξ =>
      ((‖physCoef 𝔭 𝒢 q ν k ζ (𝔭.shift (-(k * dil ν.C s.2 ξ.1)) s.1) ξ.2 ξ.1 s.2‖ : ℝ) : ℂ))
    (fun s ξ => (𝔭.shift (-(k * dil ν.C s.2 ξ.1)) s.1, ξ.2))

/-! ### Symmetrization and the operators `𝒜`, `𝒜*` -/

/-- **Symmetrization in all groups** [S-02:0072–0075, 0116–0117]: the average over all `M!` slot
permutations, independently in every small and every big group. -/
def physSym (J ℓ : ℕ) : (PState 𝔭 𝒢 J ℓ → ℂ) →ₗ[ℂ] (PState 𝔭 𝒢 J ℓ → ℂ) :=
  rowOp (Ξ := SlotPerms S J ℓ × SlotPerms B J ℓ)
    (fun _ _ => (Fintype.card (SlotPerms S J ℓ × SlotPerms B J ℓ) : ℂ)⁻¹)
    (fun s π => (s.1, permuteLists π s.2))

variable {N : Type} [Fintype N]

/-- **The physical operator `𝒜` of Definition 3.3** [S-02:0098–0118]: "the sum over patterns,
symmetrized in all groups on both sides". Parameters: the damping base `q`, the pattern family
`𝔉`, the integer `k ≠ 0` and the real `ζ`. -/
def physOp (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) : Module.End ℂ (PState 𝔭 𝒢 J ℓ → ℂ) :=
  physSym 𝔭 𝒢 J ℓ ∘ₗ (∑ ν, physRow 𝔭 𝒢 q (𝔉 ν) k ζ) ∘ₗ physSym 𝔭 𝒢 J ℓ

/-- **The adjoint `𝒜*`** [S-02:0120–0130]: the sum over patterns of the adjoint row operations,
symmetrized on both sides ("the symmetrizing projections are self-adjoint"). -/
def physAdj (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) : Module.End ℂ (PState 𝔭 𝒢 J ℓ → ℂ) :=
  physSym 𝔭 𝒢 J ℓ ∘ₗ (∑ ν, physRowAdj 𝔭 𝒢 q (𝔉 ν) k ζ) ∘ₗ physSym 𝔭 𝒢 J ℓ

/-- `𝒜` with the coefficients of each row transition replaced by their absolute values "before
adding patterns or averaging permutations" [S-02:0133–0135]. -/
def physAbsOp (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) :
    Module.End ℂ (PState 𝔭 𝒢 J ℓ → ℂ) :=
  physSym 𝔭 𝒢 J ℓ ∘ₗ (∑ ν, physRowAbs 𝔭 𝒢 q (𝔉 ν) k ζ) ∘ₗ physSym 𝔭 𝒢 J ℓ

/-- The adjoint of `physAbsOp`. -/
def physAbsAdj (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) :
    Module.End ℂ (PState 𝔭 𝒢 J ℓ → ℂ) :=
  physSym 𝔭 𝒢 J ℓ ∘ₗ (∑ ν, physRowAdjAbs 𝔭 𝒢 q (𝔉 ν) k ζ) ∘ₗ physSym 𝔭 𝒢 J ℓ

/-- The row sum at the state `s` of the operator `𝒜` with absolute coefficients (Lemma 3.4). -/
def physAbsRowSum (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (s : PState 𝔭 𝒢 J ℓ) : ℝ :=
  (physAbsOp 𝔭 𝒢 q 𝔉 k ζ (fun _ => 1) s).re

/-- The row sum at the state `s` of the adjoint of the operator with absolute coefficients, i.e.
the column sum of that operator (Lemma 3.4). -/
def physAbsColSum (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (s : PState 𝔭 𝒢 J ℓ) : ℝ :=
  (physAbsAdj 𝔭 𝒢 q 𝔉 k ζ (fun _ => 1) s).re

/-! ### The vectors `u_n`, the moment and the pairing -/

open Classical in
/-- **The vector `u_n`** [S-02:0182–0183]: "one on every physical state at position `n` and zero
elsewhere". -/
def physUnit (J ℓ : ℕ) (n : 𝔭.Pos) : PState 𝔭 𝒢 J ℓ → ℂ :=
  fun s => if s.1 = n ∧ IsPhys 𝔭 s.1 s.2 then 1 else 0

open Classical in
/-- `⟨u_n, G⟩` in `ℋ_ph`: the sum of `mass * G (n, x)` over the physical states `(n, x)` at
position `n`, each of mass `∏_g V_g^{-M}`. -/
def pairUnit (J ℓ : ℕ) (n : 𝔭.Pos) (G : PState 𝔭 𝒢 J ℓ → ℂ) : ℂ :=
  ∑ x : Lists 𝒢 J ℓ, if IsPhys 𝔭 n x then (stateMass 𝒢 J ℓ : ℂ) * G (n, x) else 0

open Classical in
/-- `‖u_n‖² = ∏_g V_g^{-M} · #{physical states at n}`. The `u_n` are not normalized
[S-02:0190–0191]. -/
def unitNormSq (J ℓ : ℕ) (n : 𝔭.Pos) : ℝ :=
  stateMass 𝒢 J ℓ * ((Finset.univ.filter fun x : Lists 𝒢 J ℓ => IsPhys 𝔭 n x).card : ℝ)

/-- **The moment `⟨u_n, (𝒜 𝒜*)^R u_n⟩` of (eq:transference-moment)** [S-02:0177–0183]. It is a
finite sum: the sum over all closed walks of `2R` alternating adjoint and forward transitions
which return to the position `n`, with arbitrary initial and final lists [S-02:0190–0193].

In the paper this number is real and nonnegative (`𝒜 𝒜* ≥ 0`); here it is defined as the real part
of the complex finite sum. -/
def physMoment (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (R : ℕ) (n : 𝔭.Pos) : ℝ :=
  (pairUnit 𝔭 𝒢 J ℓ n
    (((physOp 𝔭 𝒢 q 𝔉 k ζ * physAdj 𝔭 𝒢 q 𝔉 k ζ) ^ R) (physUnit 𝔭 𝒢 J ℓ n))).re

/-- **The pairing `⟨f, G⟩` for a first endpoint independent of the marks**
[S-02:1268–1270]: `f` is supported on the positions `n ∈ I` and takes the value `f_n` at every
physical state at `n`, i.e. `f = ∑_{n ∈ I} f_n u_n`. With `G = 𝒜 g` this is `⟨f, 𝒜 g⟩`. -/
def pairMarkFree (J ℓ : ℕ) (I : Finset 𝔭.Pos) (fn : 𝔭.Pos → ℂ) (G : PState 𝔭 𝒢 J ℓ → ℂ) : ℂ :=
  ∑ n ∈ I, conj (fn n) * pairUnit 𝔭 𝒢 J ℓ n G

/-- `‖f‖²` for `f = ∑_{n ∈ I} f_n u_n`: `∑_{n ∈ I} |f_n|² ‖u_n‖²`. -/
def markFreeNormSq (J ℓ : ℕ) (I : Finset 𝔭.Pos) (fn : 𝔭.Pos → ℂ) : ℝ :=
  ∑ n ∈ I, ‖fn n‖ ^ 2 * unitNormSq 𝔭 𝒢 J ℓ n

open Classical in
/-- The summand of `‖g‖²` in `ℋ_ph`: `mass * |g|²` at physical states, `0` elsewhere. -/
def physDensity (J ℓ : ℕ) (g : PState 𝔭 𝒢 J ℓ → ℂ) (s : PState 𝔭 𝒢 J ℓ) : ℝ :=
  if IsPhys 𝔭 s.1 s.2 then stateMass 𝒢 J ℓ * ‖g s‖ ^ 2 else 0

/-- `g ∈ ℋ_ph`: the restriction of `g` to the physical states is square summable. -/
def MemPhysL2 (J ℓ : ℕ) (g : PState 𝔭 𝒢 J ℓ → ℂ) : Prop :=
  Summable (physDensity 𝔭 𝒢 J ℓ g)

/-- `‖g‖²` in `ℋ_ph` (for `g` with `MemPhysL2`). -/
def physNormSq (J ℓ : ℕ) (g : PState 𝔭 𝒢 J ℓ → ℂ) : ℝ :=
  ∑' s, physDensity 𝔭 𝒢 J ℓ g s

/-! ### The adjoint before symmetrization -/

variable {𝔭 𝒢 q}

/-- The matrix entry of the row operation of `ν` from the state `s` to the state `t`. -/
theorem physRow_single [DecidableEq 𝔭.Pos] (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    (s t : PState 𝔭 𝒢 J ℓ) :
    physRow 𝔭 𝒢 q ν k ζ (Pi.single t 1) s =
      ∑ r : AuxList 𝒢.big ν.C, if 𝔭.shift (k * dil ν.C s.2 r) s.1 = t.1 then
        physCoef 𝔭 𝒢 q ν k ζ s.1 s.2 r t.2 else 0 := by
  unfold physRow
  rw [rowOp_single]
  exact sum_prod_ite_mk_eq (fun r => 𝔭.shift (k * dil ν.C s.2 r) s.1) t
    (fun r x' => physCoef 𝔭 𝒢 q ν k ζ s.1 s.2 r x')

/-- The matrix entry of the adjoint row operation of `ν` from the state `t` to the state `s`. -/
theorem physRowAdj_single [DecidableEq 𝔭.Pos] (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    (s t : PState 𝔭 𝒢 J ℓ) :
    physRowAdj 𝔭 𝒢 q ν k ζ (Pi.single s 1) t =
      ∑ r : AuxList 𝒢.big ν.C, if 𝔭.shift (-(k * dil ν.C t.2 r)) t.1 = s.1 then
        conj (physCoef 𝔭 𝒢 q ν k ζ (𝔭.shift (-(k * dil ν.C t.2 r)) t.1) s.2 r t.2) else 0 := by
  unfold physRowAdj
  rw [rowOp_single]
  exact sum_prod_ite_mk_eq (fun r => 𝔭.shift (-(k * dil ν.C t.2 r)) t.1) s
    (fun r x => conj (physCoef 𝔭 𝒢 q ν k ζ (𝔭.shift (-(k * dil ν.C t.2 r)) t.1) x r t.2))

/-- **The adjoint row operation is the adjoint** [S-02:0120–0129]: its matrix entry from `t` to
`s` is the complex conjugate of the matrix entry of the row operation from `s` to `t`. All
physical states have the same mass, so this is adjointness for the inner product of `ℋ_ph`
"before symmetrization". -/
theorem physRow_adjoint_entry [DecidableEq 𝔭.Pos] (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    (s t : PState 𝔭 𝒢 J ℓ) :
    physRowAdj 𝔭 𝒢 q ν k ζ (Pi.single s 1) t =
      conj (physRow 𝔭 𝒢 q ν k ζ (Pi.single t 1) s) := by
  rw [physRowAdj_single, physRow_single, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hD : dil ν.C t.2 r = dil ν.C s.2 r
  · rw [hD]
    by_cases h1 : 𝔭.shift (-(k * (dil ν.C s.2 r : ℤ))) t.1 = s.1
    · have h2 : 𝔭.shift (k * (dil ν.C s.2 r : ℤ)) s.1 = t.1 := by
        rw [← h1]
        exact 𝔭.shift_shift_neg _ _
      rw [if_pos h1, if_pos h2, h1]
    · have h2 : ¬𝔭.shift (k * (dil ν.C s.2 r : ℤ)) s.1 = t.1 := by
        intro h2
        apply h1
        rw [← h2]
        exact 𝔭.shift_neg_shift _ _
      rw [if_neg h1, if_neg h2, map_zero]
  · have hz : ∀ n : 𝔭.Pos, physCoef 𝔭 𝒢 q ν k ζ n s.2 r t.2 = 0 := by
      intro n
      by_contra hne
      exact hD (dil_eq_of_physCoef_ne_zero hne)
    simp only [hz, map_zero, ite_self]

end Ops

end Physical

end

end SimultaneousPrimitiveRoots.Unconditional.Transference
