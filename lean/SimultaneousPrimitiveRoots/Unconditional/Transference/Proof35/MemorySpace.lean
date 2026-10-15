module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Basic
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.RowOps
public import SimultaneousPrimitiveRoots.Unconditional.Graph.PrimeGroupGhostNorm
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The memory Hilbert space `ℋ` of the proof of [S] Theorem 3.5

Source: `verification/stage7-sources/S-02.tex`, lines 395–426 (`[S-02:0395–0426]`),
(eq:memory-hilbert-space):

`ℋ = ℋ_𝒮 ⊗ L²(∏_{g ∈ ℬ} 𝒫_g^M, ⊗ μ̃_g^{⊗M}) ⊗ ⊗_{g ∈ ℬ} ℱ_g`,
`ℱ_g = ⊕_{j ≥ 0} L²_sym(𝒵_g^j, λ_g^{⊗j} / j!)`,
`𝒵_g = {(p, r) : p ∈ 𝒫_g, r ∈ ℤ/pℤ}`, `dλ_g(p, r) = μ̃_g(p) d count(r)`.

## The state space

A point of the underlying measure space, a *memory state* `MState`, consists of

* `y ∈ Y_𝒮 = ∏_{p small} ℤ/pℤ` (`ResVec (smallPrimes 𝒢)`);
* an ordered list `xs` of `M` labels in each small group; it is a *small state at `y`*
  (`IsSmallState`) when the labels of one group are distinct zero coordinates of `y`;
* an ordered list `xb` of `M` labels in each big group (the big active list; no distinctness);
* for every big group `g`, an indexed tuple of at most `Bc` *pending particles* `(p, r)`,
  `p ∈ 𝒫_g`, `r ∈ ℤ/pℤ`. This is `Graph.FiniteMemory Bc (Σ p, Res p)`, the one-group memory of
  `Graph/` (`Graph/GhostTruncatedKernel.lean`) with the particle alphabet of `Graph/AnchorMemory`.

The cutoff `Bc` makes the state space a finite type. The paper restricts "the total memory size
before and after every operation" [S-02:0797–0802]; the operators of `Operators.lean` contain the
projections onto `memTotal ≤ Bc`, so the bound `Bc` on the size of each single group memory is
never active.

## The measure, symmetric functions, the boundary vector

* `memWeight` — the point masses: Haar probability in `y`; `∏_{g ∈ 𝒮} V_g^{-M}` on the small
  states at `y` and `0` on the other small lists; `∏ μ̃_g` on the big active list;
  `λ_g^{⊗j} / j!` on each memory (`Graph.finiteMemoryPointMass`, "the residue measure in `λ_g` is
  counting measure" [S-02:0422–0423]). Inner products and norms of `ℋ` are `wInner`, `wNorm` for
  this weight.
* `MemSymmetric` — "invariant under permutations of the `j` particle indices, including when
  their numerical values coincide" [S-02:0418–0420]. `ℋ` is the space of the `MemSymmetric`
  functions; operator bounds on `ℋ` are `OpBound (memWeight …) MemSymmetric`.
* `emptyVec` — the boundary vector `𝟏_∅`, "one when every memory is empty and zero otherwise; it
  is independent of all other coordinates" [S-02:0424–0426].
* `schurWeight` — the Schur weight `w(state) = v^{j_tot}` [S-02:0638–0644].
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

section Family

variable {S B : Type} [Fintype S] [Fintype B]

/-- The primes of the small groups. -/
def smallPrimes (𝒢 : GroupFamily S B) : Finset ℕ := Finset.univ.biUnion 𝒢.small

/-- The primes of the big groups ("`p` big"). -/
def bigPrimes (𝒢 : GroupFamily S B) : Finset ℕ := Finset.univ.biUnion 𝒢.big

omit [Fintype S] in
theorem mem_bigPrimes {𝒢 : GroupFamily S B} {p : ℕ} : p ∈ bigPrimes 𝒢 ↔ ∃ g, p ∈ 𝒢.big g := by
  simp [bigPrimes]

theorem allPrimes_eq (𝒢 : GroupFamily S B) : 𝒢.allPrimes = smallPrimes 𝒢 ∪ bigPrimes 𝒢 := rfl

/-- **Small state at `y`** [S-02:0398–0400]: "an ordered list of `M` distinct zero coordinates in
each small group". -/
def IsSmallState (𝒢 : GroupFamily S B) {J ℓ : ℕ} (y : ResVec (smallPrimes 𝒢))
    (xs : LabelList 𝒢.small J ℓ) : Prop :=
  (∀ g, Function.Injective (xs g)) ∧ ∀ g i, (resModel (smallPrimes 𝒢)).hit (xs g i) y

/-- The small endpoint factor `∏_{g ∈ 𝒮} q^{(ω_g(y) - M)/2}` of an edge [S-02:0504–0507]:
`ω_g(y)` is the number of zero coordinates of `y` at the primes of the small group `g`. -/
def smallDamping (𝒢 : GroupFamily S B) (J ℓ : ℕ) (q : ℝ) (y : ResVec (smallPrimes 𝒢)) : ℝ :=
  q ^ ((((∑ g, countHits (fun p => (resModel (smallPrimes 𝒢)).hit p y) (𝒢.small g) : ℕ) : ℝ) -
    ((J + ℓ : ℕ) : ℝ) * (Fintype.card S : ℝ)) / 2)

end Family

/-! ### Particles and memories -/

section Memory

variable {S B : Type}

/-- A pending particle `(p, r)` of the big group `g`: `p ∈ 𝒫_g`, `r ∈ ℤ/pℤ`; the alphabet `𝒵_g`
[S-02:0402–0406]. "A pending particle `(p, r)` records displacement from its required hit, modulo
`p`" [S-02:0420–0421]. -/
abbrev Particle (𝒢 : GroupFamily S B) (g : B) : Type := Σ p : {p : ℕ // p ∈ 𝒢.big g}, Res p.1

/-- A group memory `𝐳 = ((p_h, r_h))_{h=1}^{j}` with `j ≤ Bc` [S-02:0456]: the one-group memory
`Graph.FiniteMemory` on the particle alphabet. -/
abbrev Mem (𝒢 : GroupFamily S B) (Bc : ℕ) (g : B) : Type :=
  Graph.FiniteMemory Bc (Particle 𝒢 g)

variable {𝒢 : GroupFamily S B} {Bc : ℕ} {g : B}

/-- The empty memory. -/
def emptyMem (𝒢 : GroupFamily S B) (Bc : ℕ) (g : B) : Mem 𝒢 Bc g :=
  ⟨⟨0, Nat.succ_pos Bc⟩, Fin.elim0⟩

/-- The particle with index `i` of a memory, if `i` is smaller than its size. -/
def memAt (z : Mem 𝒢 Bc g) (i : Fin Bc) : Option (Particle 𝒢 g) :=
  if h : i.val < z.1.val then some (z.2 ⟨i.val, h⟩) else none

/-- The memory with the particles of a list, in the order of the list (the empty memory if the
list is longer than the cutoff; the operators give such transitions the coefficient `0`). -/
def memOfList (l : List (Particle 𝒢 g)) : Mem 𝒢 Bc g :=
  if h : l.length ≤ Bc then ⟨⟨l.length, Nat.lt_succ_of_le h⟩, l.get⟩ else emptyMem 𝒢 Bc g

/-- `|Z(𝐳)|`, the number of pending particles with residue zero, `Z(𝐳) = {h : r_h = 0}`
[S-02:0456–0457]; positions are counted, not values (`Graph.ghostZeroCount`). -/
def memZeroCount (z : Mem 𝒢 Bc g) : ℕ := Graph.ghostZeroCount z.2

theorem memOfList_size {l : List (Particle 𝒢 g)} (h : l.length ≤ Bc) :
    (memOfList (Bc := Bc) l).1.val = l.length := by
  unfold memOfList
  rw [dif_pos h]

theorem emptyMem_size (𝒢 : GroupFamily S B) (Bc : ℕ) (g : B) : (emptyMem 𝒢 Bc g).1.val = 0 := rfl

end Memory

/-! ### Memory states -/

section States

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

/-- **A point of the measure space of `ℋ`** (eq:memory-hilbert-space) [S-02:0397–0417]: the small
residues `y`, the small list `xs`, the big active list `xb`, and one memory for every big
group. -/
structure MState (𝒢 : GroupFamily S B) (J ℓ Bc : ℕ) where
  /-- `y ∈ Y_𝒮 = ∏_{p small} ℤ/pℤ` -/
  y : ResVec (smallPrimes 𝒢)
  /-- the ordered small labels -/
  xs : LabelList 𝒢.small J ℓ
  /-- the ordered big active labels -/
  xb : LabelList 𝒢.big J ℓ
  /-- the memories of the big groups -/
  mem : (g : B) → Mem 𝒢 Bc g

variable {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ}

/-- A memory state is the quadruple of its coordinates. -/
def MState.equivProd : MState 𝒢 J ℓ Bc ≃
    ResVec (smallPrimes 𝒢) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ ×
      ((g : B) → Mem 𝒢 Bc g) where
  toFun s := (s.y, s.xs, s.xb, s.mem)
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2⟩
  left_inv s := by
    cases s
    rfl
  right_inv t := by
    rcases t with ⟨a, b, c, d⟩
    rfl

instance MState.instFintype : Fintype (MState 𝒢 J ℓ Bc) :=
  Fintype.ofEquiv _ MState.equivProd.symm

/-- `j_tot = ∑_{g ∈ ℬ} j_g`, the total memory size [S-02:0641–0643]. -/
def memTotal (s : MState 𝒢 J ℓ Bc) : ℕ := ∑ g, (s.mem g).1.val

/-- The number of pending zeros in all memories. -/
def memZeros (s : MState 𝒢 J ℓ Bc) : ℕ := ∑ g, memZeroCount (s.mem g)

/-- Permute the particle indices of the memory of the group `g`. -/
def MState.permMem (s : MState 𝒢 J ℓ Bc) (g : B) (σ : Equiv.Perm (Fin (s.mem g).1.val)) :
    MState 𝒢 J ℓ Bc :=
  { s with mem := Function.update s.mem g ⟨(s.mem g).1, (s.mem g).2 ∘ σ⟩ }

/-- **Symmetric in the particle indices** [S-02:0418–0420]: "invariant under permutations of the
`j` particle indices, including when their numerical values coincide", in every group memory. The
Hilbert space `ℋ` consists of the functions with this property. -/
def MemSymmetric {α : Type*} (F : MState 𝒢 J ℓ Bc → α) : Prop :=
  ∀ (s : MState 𝒢 J ℓ Bc) (g : B) (σ : Equiv.Perm (Fin (s.mem g).1.val)),
    F (s.permMem g σ) = F s

/-- Permute the slots of the small and of the big active lists, independently in every group. -/
def MState.permLists (π : SlotPerms S J ℓ × SlotPerms B J ℓ) (s : MState 𝒢 J ℓ Bc) :
    MState 𝒢 J ℓ Bc :=
  { s with xs := permuteSlots π.1 s.xs, xb := permuteSlots π.2 s.xb }

omit [DecidableEq S] in
theorem memTotal_permMem (s : MState 𝒢 J ℓ Bc) (g : B) (σ : Equiv.Perm (Fin (s.mem g).1.val)) :
    memTotal (s.permMem g σ) = memTotal s := by
  unfold memTotal MState.permMem
  refine Finset.sum_congr rfl fun g' _ => ?_
  by_cases h : g' = g
  · subst h
    simp
  · simp [Function.update_of_ne h]

omit [DecidableEq S] [DecidableEq B] in
theorem memTotal_permLists (π : SlotPerms S J ℓ × SlotPerms B J ℓ) (s : MState 𝒢 J ℓ Bc) :
    memTotal (s.permLists π) = memTotal s := rfl

/-! ### The measure of `ℋ` -/

/-- The point mass of the Haar probability measure of `∏_{p ∈ Q} ℤ/pℤ`. -/
def haarMass (Q : Finset ℕ) : ℝ := (Fintype.card (ResVec Q) : ℝ)⁻¹

/-- The mass `∏_{g ∈ 𝒮} V_g^{-M}` of a small state [S-02:0398–0400]. -/
def smallListMass (𝒢 : GroupFamily S B) (J ℓ : ℕ) : ℝ :=
  ∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ (J + ℓ))⁻¹

/-- The measure `⊗_{g ∈ ℬ} μ̃_g^{⊗M}` of the big active lists (eq:memory-hilbert-space). -/
def bigListMass (𝒢 : GroupFamily S B) (q : ℝ) (n : ℕ) (xb : LabelList 𝒢.big J ℓ) : ℝ :=
  ∏ g, ∏ i : Slot J ℓ, tiltLaw (𝒢.big g) q n (xb g i)

/-- The measure `⊗_g λ_g^{⊗j_g} / j_g!` of the memories (eq:memory-hilbert-space): the product
over the big groups of `Graph.finiteMemoryPointMass` for the weight `λ_g(p, r) = μ̃_g(p)`. -/
def memMass (𝒢 : GroupFamily S B) (q : ℝ) (n : ℕ) (mem : (g : B) → Mem 𝒢 Bc g) : ℝ :=
  ∏ g, Graph.finiteMemoryPointMass (fun z : Particle 𝒢 g => tiltLaw (𝒢.big g) q n z.1) (mem g)

open _root_.Classical in
/-- **The measure of `ℋ`** (eq:memory-hilbert-space) [S-02:0397–0417]: the point mass of a memory
state. It vanishes when the small list is not a small state at `y`. The parameter `n = N` is the
number of edges; it enters through `μ̃_g`. -/
def memWeight (𝒢 : GroupFamily S B) (q : ℝ) (n : ℕ) (s : MState 𝒢 J ℓ Bc) : ℝ :=
  if IsSmallState 𝒢 s.y s.xs then
    haarMass (smallPrimes 𝒢) * smallListMass 𝒢 J ℓ * bigListMass 𝒢 q n s.xb *
      memMass 𝒢 q n s.mem
  else 0

/-- **The boundary vector `𝟏_∅`** [S-02:0424–0426]: "one when every memory is empty and zero
otherwise; it is independent of all other coordinates". -/
def emptyVec (𝒢 : GroupFamily S B) (J ℓ Bc : ℕ) : MState 𝒢 J ℓ Bc → ℂ :=
  fun s => if memTotal s = 0 then 1 else 0

/-- **The Schur weight `w(state) = v^{j_tot}`** [S-02:0638–0644]. -/
def schurWeight (v : ℝ) (s : MState 𝒢 J ℓ Bc) : ℝ := v ^ memTotal s

omit [DecidableEq S] [DecidableEq B] in
theorem schurWeight_pos {v : ℝ} (hv : 0 < v) (s : MState 𝒢 J ℓ Bc) : 0 < schurWeight v s :=
  pow_pos hv _

omit [DecidableEq S] in
theorem schurWeight_permMem (v : ℝ) (s : MState 𝒢 J ℓ Bc) (g : B)
    (σ : Equiv.Perm (Fin (s.mem g).1.val)) : schurWeight v (s.permMem g σ) = schurWeight v s := by
  unfold schurWeight
  rw [memTotal_permMem]

omit [DecidableEq S] in
/-- The boundary vector is symmetric in the particle indices. -/
theorem emptyVec_memSymmetric : MemSymmetric (emptyVec 𝒢 J ℓ Bc) := by
  intro s g σ
  unfold emptyVec
  rw [memTotal_permMem]

omit [DecidableEq S] in
/-- If `F` is symmetric in the particle indices, so is `|F|² / w` for the Schur weight `w`. -/
theorem MemSymmetric.normSq_div {F : MState 𝒢 J ℓ Bc → ℂ} (hF : MemSymmetric F) (v : ℝ) :
    MemSymmetric fun s => ‖F s‖ ^ 2 / schurWeight v s := by
  intro s g σ
  show ‖F (s.permMem g σ)‖ ^ 2 / schurWeight v (s.permMem g σ) = ‖F s‖ ^ 2 / schurWeight v s
  rw [hF s g σ, schurWeight_permMem]

omit [DecidableEq S] [DecidableEq B] in
/-- The measure of `ℋ` is nonnegative as soon as `μ̃_g ≥ 0` on every big group (which holds when
`b_p > 0`, i.e. for large `x`). -/
theorem memWeight_nonneg (𝒢 : GroupFamily S B) (q : ℝ) (n : ℕ)
    (hpos : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p) (s : MState 𝒢 J ℓ Bc) :
    0 ≤ memWeight 𝒢 q n s := by
  unfold memWeight
  split_ifs
  · have h1 : 0 ≤ haarMass (smallPrimes 𝒢) := inv_nonneg.mpr (Nat.cast_nonneg _)
    have h2 : 0 ≤ smallListMass 𝒢 J ℓ :=
      Finset.prod_nonneg fun g _ =>
        inv_nonneg.mpr (pow_nonneg (Schur.reciprocalMass_nonneg _) _)
    have h3 : 0 ≤ bigListMass 𝒢 q n s.xb :=
      Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun i _ => hpos g _ (s.xb g i).2
    have h4 : 0 ≤ memMass 𝒢 q n s.mem := by
      refine Finset.prod_nonneg fun g _ => ?_
      unfold Graph.finiteMemoryPointMass Graph.factorialMemoryPointMass
      exact div_nonneg (Finset.prod_nonneg fun i _ => hpos g _ ((s.mem g).2 i).1.2)
        (Nat.cast_nonneg _)
    exact mul_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) h4
  · exact le_rfl

end States

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
