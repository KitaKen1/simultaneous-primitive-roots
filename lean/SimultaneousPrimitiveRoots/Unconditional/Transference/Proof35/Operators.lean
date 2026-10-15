module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.MemorySpace
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The memory operators `G_i` and `ℰ_i` of the proof of [S] Theorem 3.5

Source: `verification/stage7-sources/S-02.tex`, lines 428–521 (`[S-02:0428–0521]`).

"Separate the evolution into an operation `G_i` at each visit `0 ≤ i ≤ N` and an operation `ℰ_i`
across the following edge for `i < N`. The visit operation handles ghost endpoints and unmarked
hits. The edge operation moves residues and transfers particles between active lists and memory"
[S-02:0434–0440].

Both are *row operators* (`rowOp`) on the functions on the memory states `MState 𝒢 J ℓ Bc`. Their
*local transition choices* are explicit finite types, because the proof refers to them: the
distinct-birth rule [S-02:0516–0521], the birth addresses [S-02:1053–1062] and the "multipliers of
modulus at most one on individual local transition choices" [S-02:0762–0764, 1183–1190] are
functions of the choices.

## The visit operation `G_i` (eq:ghost-row) [S-02:0456–0475]

A choice (`GhostChoice`) is, in every big group `g`, a set `A ⊆ Z(𝐳)` of indices of pending zeros
which terminate, and an ordered batch `(p'_1, …, p'_b)` of primes of `𝒫_g` which are born at
residue zero. The coefficient of the group `g` (`ghostCoefG`) is
`(-η_i/ρ)^{|A|} (q_i/ρ²)^{|Z(𝐳)| - |A|} (1/b!) (-η_i V_g/ρ)^b ∏_h μ̃_g(p'_h)`,
in the notation of `Graph/SourceGhostCoefficients.lean`:
`D^{|A|} A^{|Z| - |A|} C^b / b! · ∏ μ̃_g`, with `A = sourceGhostA q_i ρ`, `D = sourceGhostD q_i ρ`,
`C = sourceGhostC V_g q_i ρ`. The new memory is `(𝐳 ∖ A, (p'_1, 0), …, (p'_b, 0))`: the surviving
particles in their order, then the batch.

`ghostRowG` is the resulting row of one group, and `GhostRowCompat` states that on symmetric
functions it is the one-group row `Graph.finiteGhostTruncatedRow` (whose survivors are enumerated
in a different order). The multi-group coefficient `ghostCoef` is the product over the big groups,
times the projections onto total memory size at most `Bc`.

## The edge operation `ℰ_i` [S-02:0477–0514]

A choice between the two symmetrizations (`EdgeChoice`) consists of a pattern `ν`, the auxiliary
free labels `r`, for every big group the set of unshared source slots which are stored and a
partial injection of the unshared target slots into the indices of the old memory (the
promotions), and the small and big target lists. The coefficient `edgeCoef` follows steps 1–4 of
the paper; see its docstring. `edgeOpWith` is `ℰ_i` with a multiplier on the fresh births;
`edgeClean`, `edgeDirty` are the two parts of [S-02:0826–0833].

## Parameters

`MemData` collects what the operators depend on: `q`, `ρ`, the number `n = N` of edges, the
pattern family, `k` and `ζ`. The phase parameter `θ` of (eq:return-fourier) and the visit or edge
index `i` are separate arguments.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators ComplexConjugate

noncomputable section

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {N : Type}

/-- **The parameters of the memory operators**: the damping base `q`, the constant `ρ` of
[S-02:0442–0443], the number `n = N` of edges, the pattern family, the integer `k` and the real
`ζ`. -/
structure MemData (𝒢 : GroupFamily S B) (J ℓ : ℕ) (N : Type) where
  /-- the damping base `q` -/
  q : ℝ
  /-- the constant `ρ` -/
  ρ : ℝ
  /-- the number `N` of edges; the visits are `0, …, n` -/
  n : ℕ
  /-- the pattern family -/
  fam : N → Pattern 𝒢.big J ℓ
  /-- the integer `k` of Definition 3.3 -/
  k : ℤ
  /-- the real `ζ` -/
  ζ : ℝ

/-- The slot permutations of all active lists: one permutation of the `M` slots for every small
and every big group. -/
abbrev ListPerms (S B : Type) (J ℓ : ℕ) : Type := SlotPerms S J ℓ × SlotPerms B J ℓ

/-- **Symmetrization in all active lists** [S-02:0477–0479]: the average over the slot permutations
of the small and of the big active lists. The memories are not touched. -/
def memSym (𝒢 : GroupFamily S B) (J ℓ Bc : ℕ) :
    (MState 𝒢 J ℓ Bc → ℂ) →ₗ[ℂ] (MState 𝒢 J ℓ Bc → ℂ) :=
  rowOp (Ξ := ListPerms S B J ℓ) (fun _ _ => (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹)
    (fun s π => s.permLists π)

/-! ### The visit operation `G_i` -/

/-- An ordered batch of ghost births in the big group `g`: its size `b ≤ Bc` and the primes
`p'_1, …, p'_b ∈ 𝒫_g` [S-02:0465–0470]. -/
abbrev Batch (𝒢 : GroupFamily S B) (Bc : ℕ) (g : B) : Type :=
  Σ b : Fin (Bc + 1), Fin b.val → {p : ℕ // p ∈ 𝒢.big g}

/-- **A local transition choice of the visit operation** [S-02:0458–0475]: in every big group `g`,
the set `A` of the indices of the old pending zeros which terminate, and the batch of births. -/
abbrev GhostChoice (𝒢 : GroupFamily S B) (Bc : ℕ) : Type :=
  (g : B) → Finset (Fin Bc) × Batch 𝒢 Bc g

section GhostGroup

variable {g : B}

/-- `A ⊆ Z(𝐳)`: every index of `A` is the index of a pending particle with residue zero. -/
def GhostValid (z : Mem 𝒢 Bc g) (A : Finset (Fin Bc)) : Prop :=
  ∀ i ∈ A, ∃ pr : Particle 𝒢 g, memAt z i = some pr ∧ pr.2 = 0

/-- `𝐳 ∖ A`: the particles whose index is not in `A`, in their order. -/
def ghostSurvivors (z : Mem 𝒢 Bc g) (A : Finset (Fin Bc)) : List (Particle 𝒢 g) :=
  (List.finRange Bc).filterMap fun i => if i ∈ A then none else memAt z i

/-- The particles `(p'_1, 0), …, (p'_b, 0)` of a batch. -/
def batchParticles (b : Batch 𝒢 Bc g) : List (Particle 𝒢 g) :=
  List.ofFn fun j : Fin b.1.val => (⟨b.2 j, 0⟩ : Particle 𝒢 g)

/-- The size of the new memory `(𝐳 ∖ A, (p'_1, 0), …, (p'_b, 0))`. -/
def ghostNewSize (z : Mem 𝒢 Bc g) (c : Finset (Fin Bc) × Batch 𝒢 Bc g) : ℕ :=
  (ghostSurvivors z c.1).length + c.2.1.val

/-- The new memory `(𝐳 ∖ A, (p'_1, 0), …, (p'_b, 0))` of (eq:ghost-row). -/
def ghostNewMem (z : Mem 𝒢 Bc g) (c : Finset (Fin Bc) × Batch 𝒢 Bc g) : Mem 𝒢 Bc g :=
  memOfList (ghostSurvivors z c.1 ++ batchParticles c.2)

open _root_.Classical in
/-- **The coefficient of (eq:ghost-row) in one big group** [S-02:0460–0472], at the visit `i` of a
walk with `n` edges, for the old memory `𝐳`, the terminated set `A` and the batch
`(p'_1, …, p'_b)`:
`(-η_i/ρ)^{|A|} (q_i/ρ²)^{|Z(𝐳)| - |A|} (1/b!) (-η_i V_g/ρ)^b ∏_h μ̃_g(p'_h)` if `A ⊆ Z(𝐳)`, and
`0` otherwise. -/
def ghostCoefG (𝒢 : GroupFamily S B) (q ρ : ℝ) (n i : ℕ) (g : B) (z : Mem 𝒢 Bc g)
    (c : Finset (Fin Bc) × Batch 𝒢 Bc g) : ℝ :=
  if GhostValid z c.1 then
    Graph.sourceGhostD (visitQ q n i) ρ ^ c.1.card *
      Graph.sourceGhostA (visitQ q n i) ρ ^ (memZeroCount z - c.1.card) *
      (Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ q n i) ρ ^
        c.2.1.val / (c.2.1.val.factorial : ℝ)) *
      ∏ j, tiltLaw (𝒢.big g) q n (c.2.2 j)
  else 0

/-- **The row action (eq:ghost-row) of one big group** [S-02:0460–0472] on a function `H` of the
memory of that group, with output memories of size at most `Bc`:
`(G_{i,g} H)(𝐳) = ∑_{A ⊆ Z(𝐳)} ∑_b ∑_{p'} ghostCoefG · H(𝐳 ∖ A, (p'_1,0), …, (p'_b,0))`. -/
def ghostRowG (𝒢 : GroupFamily S B) (q ρ : ℝ) (n i : ℕ) (g : B) (H : Mem 𝒢 Bc g → ℂ)
    (z : Mem 𝒢 Bc g) : ℂ :=
  ∑ c : Finset (Fin Bc) × Batch 𝒢 Bc g,
    if ghostNewSize z c ≤ Bc then (ghostCoefG 𝒢 q ρ n i g z c : ℂ) * H (ghostNewMem z c) else 0

end GhostGroup

/-- **The one-group row is the row of `Graph/`**: for a function `H` of one group memory which is
symmetric in the particle indices, `ghostRowG` is `Graph.finiteGhostTruncatedRow` for the weights
`ν = μ̃_g` and the coefficients `A = q_i/ρ²`, `D = -η_i/ρ`, `C = V_g D`
(`Graph.sourceGhostA/D/C`), with the common cutoff `Bc`.

The two rows differ only in the order in which the surviving particles are listed (`Graph/` uses
`retrievalCoordinates`, here the survivors keep their order), which a symmetric `H` does not see.
With this identity the one-group results of `Graph/` apply to `ghostRowG`: the adjoint
(eq:ghost-joint-integral) (`Graph.finite_ghost_subset_joint_reversal`), the weighted row and column
ratios (eq:ghost-schur-ratios)
(`Graph.finite_ghost_truncated_kernel_weighted_row_le_uniform_exp`, `…_column_…`) and the `L²`
bound (`Graph.tilted_prime_group_ghost_finite_cutoff_sq_bound`). -/
def GhostRowCompat : Prop :=
  ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] (𝒢 : GroupFamily S B)
    (q ρ : ℝ) (n i Bc : ℕ) (g : B) (H : Mem 𝒢 Bc g → ℂ),
    (∀ (m : Fin (Bc + 1)) (σ : Equiv.Perm (Fin m.val)) (y : Fin m.val → Particle 𝒢 g),
      H ⟨m, y ∘ σ⟩ = H ⟨m, y⟩) →
    ∀ z : Mem 𝒢 Bc g,
      ghostRowG 𝒢 q ρ n i g H z =
        Graph.finiteGhostTruncatedRow
          (fun p : {p : ℕ // p ∈ 𝒢.big g} => ((tiltLaw (𝒢.big g) q n p : ℝ) : ℂ))
          ((Graph.sourceGhostA (visitQ q n i) ρ : ℝ) : ℂ)
          ((Graph.sourceGhostD (visitQ q n i) ρ : ℝ) : ℂ)
          ((Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ q n i) ρ : ℝ) : ℂ)
          Bc H z

/-- The state after a visit operation: every memory is replaced by the new memory of its group;
"leaving every other coordinate fixed" [S-02:0458–0459]. -/
def ghostTgt (s : MState 𝒢 J ℓ Bc) (c : GhostChoice 𝒢 Bc) : MState 𝒢 J ℓ Bc :=
  { s with mem := fun g => ghostNewMem (s.mem g) (c g) }

/-- **The coefficient of the visit operation `G_i`** [S-02:0456–0475]: "the product over big
groups" of the coefficients (eq:ghost-row), for memory states of total size at most `Bc` before
and after the operation (the memory truncation [S-02:0797–0802], "writing the projections
implicitly"); `0` otherwise. -/
def ghostCoef (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc) (c : GhostChoice 𝒢 Bc) : ℝ :=
  if memTotal s ≤ Bc ∧ (∑ g, ghostNewSize (s.mem g) (c g)) ≤ Bc then
    ∏ g, ghostCoefG 𝒢 D.q D.ρ D.n i g (s.mem g) (c g)
  else 0

/-- The births of a visit operation: the batches of all big groups. -/
def ghostBirths (c : GhostChoice 𝒢 Bc) : (g : B) → Batch 𝒢 Bc g := fun g => (c g).2

/-- The number of ghost births of a visit operation. -/
def ghostBirthCount (c : GhostChoice 𝒢 Bc) : ℕ := ∑ g, (c g).2.1.val

/-- **The visit operation `G_i` with a multiplier on its births**: the row operator with the
coefficients `φ(births) · ghostCoef` [S-02:1198–1214]. The multiplier is a function of the ordered
batches of the big groups. -/
def ghostOpWith (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (φ : ((g : B) → Batch 𝒢 Bc g) → ℂ) (i : ℕ) :
    (MState 𝒢 J ℓ Bc → ℂ) →ₗ[ℂ] (MState 𝒢 J ℓ Bc → ℂ) :=
  rowOp (fun s c => φ (ghostBirths c) * ((ghostCoef D i s c : ℝ) : ℂ)) ghostTgt

/-- **The visit operation `G_i`** (eq:ghost-row) [S-02:0456–0475], truncated to total memory size
at most `Bc`. -/
def ghostOp (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (i : ℕ) :
    (MState 𝒢 J ℓ Bc → ℂ) →ₗ[ℂ] (MState 𝒢 J ℓ Bc → ℂ) :=
  ghostOpWith D Bc (fun _ => 1) i

/-! ### The edge operation `ℰ_i` -/

/-- The orientation `σ_i` of the edge `i` [S-02:0216–0219]: the edges alternate, the edge `0`
being a forward edge (a row transition of `𝒜`). -/
def edgeSign (i : ℕ) : ℤ := if i % 2 = 0 then 1 else -1

/-- The unshared slots of a big group with set `C_g = C` [S-02:0058–0060]: the slots of `C` and
the last `ℓ` slots. -/
def Unshared {J ℓ : ℕ} (C : Finset (Fin J)) : Slot J ℓ → Prop
  | Sum.inl i => i ∈ C
  | Sum.inr _ => True

/-- The slots in their canonical order [S-02:0510–0511]. -/
def slotList (J ℓ : ℕ) : List (Slot J ℓ) :=
  (List.finRange J).map Sum.inl ++ (List.finRange ℓ).map Sum.inr

/-- **A local transition choice of the edge operation, between the two symmetrizations**
[S-02:0480–0508]. -/
structure EdgeChoice (𝒢 : GroupFamily S B) {J ℓ : ℕ} {N : Type} (𝔉 : N → Pattern 𝒢.big J ℓ)
    (Bc : ℕ) where
  /-- the pattern -/
  ν : N
  /-- the auxiliary free labels forming `D` (step 1) -/
  r : AuxList 𝒢.big (𝔉 ν).C
  /-- for every big group, the unshared source slots which are stored (step 2) -/
  store : (g : B) → Finset (Slot J ℓ)
  /-- for every big group, the promotions: `promo g s = some j` if the target slot `s` receives
  the old pending particle with index `j` (step 3) -/
  promo : (g : B) → Slot J ℓ → Option (Fin Bc)
  /-- the small target list (step 4) -/
  xsT : LabelList 𝒢.small J ℓ
  /-- the big target list: shared, promoted and fresh labels (step 3) -/
  xbT : LabelList 𝒢.big J ℓ

/-- An edge choice is the tuple of its components. -/
def EdgeChoice.equivSigma {𝔉 : N → Pattern 𝒢.big J ℓ} : EdgeChoice 𝒢 𝔉 Bc ≃
    Σ ν : N, AuxList 𝒢.big (𝔉 ν).C × ((g : B) → Finset (Slot J ℓ)) ×
      ((g : B) → Slot J ℓ → Option (Fin Bc)) × LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ where
  toFun c := ⟨c.ν, c.r, c.store, c.promo, c.xsT, c.xbT⟩
  invFun t := ⟨t.1, t.2.1, t.2.2.1, t.2.2.2.1, t.2.2.2.2.1, t.2.2.2.2.2⟩
  left_inv c := by
    cases c
    rfl
  right_inv t := by
    rcases t with ⟨a, b, c, d, e, f⟩
    rfl

instance EdgeChoice.instFintype [Fintype N] {𝔉 : N → Pattern 𝒢.big J ℓ} :
    Fintype (EdgeChoice 𝒢 𝔉 Bc) := by
  haveI h1 : Fintype (LabelList 𝒢.small J ℓ) := inferInstance
  haveI h2 : Fintype (LabelList 𝒢.big J ℓ) := inferInstance
  haveI h3 : Fintype ((g : B) → Slot J ℓ → Option (Fin Bc)) := inferInstance
  haveI h4 : Fintype ((g : B) → Finset (Slot J ℓ)) := inferInstance
  haveI h5 : ∀ ν : N, Fintype (AuxList 𝒢.big (𝔉 ν).C) := fun ν => inferInstance
  exact Fintype.ofEquiv _ EdgeChoice.equivSigma.symm

section Edge

variable (D : MemData 𝒢 J ℓ N)

/-- The dilation `D = D_𝒮 D_ℬ` of an edge: "form `D` from shared source labels and the
independent free draws" (step 1, [S-02:0482–0483]); `dil` of Definition 3.3. -/
def edgeDil (s : MState 𝒢 J ℓ Bc) (c : EdgeChoice 𝒢 D.fam Bc) : ℕ :=
  dil (D.fam c.ν).C ((s.xs, s.xb) : Lists 𝒢 J ℓ) c.r

/-- The step `Δ = σ_i k D` of the edge `i` [S-02:0492–0493]. -/
def edgeStep (i : ℕ) (s : MState 𝒢 J ℓ Bc) (c : EdgeChoice 𝒢 D.fam Bc) : ℤ :=
  edgeSign i * D.k * (edgeDil D s c : ℤ)

/-- Translation of the residue of a pending particle (`Graph.residueTranslation`). -/
def shiftParticle {g : B} (Δ : ℤ) (z : Particle 𝒢 g) : Particle 𝒢 g :=
  Graph.residueTranslation (fun p : {p : ℕ // p ∈ 𝒢.big g} => (Δ : Res p.1)) z

/-- The target slot `sl` of the big group `g` is filled by a fresh integration: it is unshared
and not a promotion [S-02:0501–0502]. These are the fresh births of the edge. -/
def Fresh {𝔉 : N → Pattern 𝒢.big J ℓ} (c : EdgeChoice 𝒢 𝔉 Bc) (g : B) (sl : Slot J ℓ) : Prop :=
  Unshared ((𝔉 c.ν).C g) sl ∧ c.promo g sl = none

open _root_.Classical in
/-- The number of promotions of the big group `g`. -/
def promoCount {𝔉 : N → Pattern 𝒢.big J ℓ} (c : EdgeChoice 𝒢 𝔉 Bc) (g : B) : ℕ :=
  (Finset.univ.filter fun sl : Slot J ℓ => c.promo g sl ≠ none).card

/-- **Stores** (step 2, [S-02:0488–0491, 0500–0501]): "in each big group select any subset of its
`t_g` unshared source slots to store"; "require `p ∤ D` for every stored … particle". -/
def StoreValid (s : MState 𝒢 J ℓ Bc) (c : EdgeChoice 𝒢 D.fam Bc) : Prop :=
  ∀ g, ∀ sl ∈ c.store g,
    Unshared ((D.fam c.ν).C g) sl ∧ ¬((s.xb g sl : ℕ) ∣ edgeDil D s c)

/-- **Promotions** (step 3, [S-02:0494–0501]): "choose any subset of the `t_g` unshared big target
slots and an injection of those ordered slots into distinct old pending particle indices of that
group whose translated residue is zero. Promote the selected particles into those slots …
Require `p ∤ D` for every … promoted particle." -/
def PromoValid (i : ℕ) (s : MState 𝒢 J ℓ Bc) (c : EdgeChoice 𝒢 D.fam Bc) : Prop :=
  ∀ (g : B) (sl : Slot J ℓ) (j : Fin Bc), c.promo g sl = some j →
    Unshared ((D.fam c.ν).C g) sl ∧
      (∀ sl', c.promo g sl' = some j → sl' = sl) ∧
      ∃ pr : Particle 𝒢 g, memAt (s.mem g) j = some pr ∧
        (shiftParticle (edgeStep D i s c) pr).2 = 0 ∧
        ¬((pr.1 : ℕ) ∣ edgeDil D s c) ∧ c.xbT g sl = pr.1

open _root_.Classical in
/-- The new memory of the big group `g` after the edge `i`, as a list: the old particles which
are not promoted, translated by `Δ`, in their order; then the stored particles
`(p, 0 + Δ)`, in the canonical order of their slots ("appending their particles at residue zero",
then "translate … all pending residues, including the newly stored ones", [S-02:0489–0493]). -/
def edgeNewList (i : ℕ) (s : MState 𝒢 J ℓ Bc) (c : EdgeChoice 𝒢 D.fam Bc) (g : B) :
    List (Particle 𝒢 g) :=
  ((List.finRange Bc).filterMap fun j =>
      if ∃ sl, c.promo g sl = some j then none
      else (memAt (s.mem g) j).map (shiftParticle (edgeStep D i s c))) ++
    ((slotList J ℓ).filter fun sl => decide (sl ∈ c.store g)).map fun sl =>
      shiftParticle (edgeStep D i s c) ⟨s.xb g sl, 0⟩

/-- The state after the row transition of the edge `i`: `y` and the memories are translated by
`Δ`, the stored particles are appended, the promoted ones removed, and the lists are replaced by
the target lists. -/
def edgeTgt (i : ℕ) (s : MState 𝒢 J ℓ Bc) (c : EdgeChoice 𝒢 D.fam Bc) : MState 𝒢 J ℓ Bc where
  y := (resModel (smallPrimes 𝒢)).shift (edgeStep D i s c) s.y
  xs := c.xsT
  xb := c.xbT
  mem := fun g => memOfList (edgeNewList D i s c g)

/-- The oriented multiplier of step 1 [S-02:0484–0486]: `K_ν D^{iζ}` on a forward edge, "or its
conjugate with roles interchanged" on a backward edge. -/
def edgeMultiplier (i : ℕ) (s : MState 𝒢 J ℓ Bc) (c : EdgeChoice 𝒢 D.fam Bc) : ℂ :=
  if i % 2 = 0 then
    (D.fam c.ν).K s.xb c.xbT c.r * ((edgeDil D s c : ℕ) : ℂ) ^ ((D.ζ : ℂ) * Complex.I)
  else
    conj ((D.fam c.ν).K c.xbT s.xb c.r * ((edgeDil D s c : ℕ) : ℂ) ^ ((D.ζ : ℂ) * Complex.I))

open _root_.Classical in
/-- **The coefficient of the row action of the edge `i` between the two symmetrizations**
[S-02:0480–0514], from the state `s` with the choice `c`, with total memory size at most `Bc`
before and after. It vanishes unless

* the source and the target small lists are small states at `y` and at `y + Δ`, with the same
  shared labels (step 4: "in the small groups use the physical target sum");
* the big target list has the shared labels of the source (step 2: "shared particles remain
  active");
* no auxiliary free label occurs in the source or in the target lists (step 1: "retain the ban of
  free labels from both endpoint active lists");
* the stores and the promotions are admissible (`StoreValid`, `PromoValid`).

Otherwise it is the product of

* the probability of the free labels (law `μ_g`; "auxiliary free draws of `D` are not particle
  births");
* `ρ` "for every old pending zero, before storing any active particle" (step 2);
* `V_g^{-1}` per promotion (step 3);
* `μ̃_g(p)` for every fresh target label `p` ("independent fresh integrations against `μ̃_g`");
* `ρ` "for every pending zero remaining after promotions" (step 4);
* the small normalization `∏_{g ∈ 𝒮} V_g^{-ℓ}` and "the two small endpoint factors
  `q^{(ω_g - M)/2}`" at `y` and `y + Δ` (step 4);
* "the oriented coefficient `K_ν D^{iζ}`, or its conjugate with roles interchanged, and
  `e(θ σ_i k D)`" (step 1).

"No big endpoint damping is included apart from the pending-particle factors." -/
def edgeCoef (θ : ℝ) (i : ℕ) (s : MState 𝒢 J ℓ Bc) (c : EdgeChoice 𝒢 D.fam Bc) : ℂ :=
  if memTotal s ≤ Bc ∧ (∑ g, (edgeNewList D i s c g).length) ≤ Bc ∧
      IsSmallState 𝒢 s.y s.xs ∧
      IsSmallState 𝒢 ((resModel (smallPrimes 𝒢)).shift (edgeStep D i s c) s.y) c.xsT ∧
      SharedSmall s.xs c.xsT ∧ SharedBig (D.fam c.ν).C s.xb c.xbT ∧
      AuxAvoids (D.fam c.ν).C c.r ((s.xs, s.xb) : Lists 𝒢 J ℓ) ∧
      AuxAvoids (D.fam c.ν).C c.r ((c.xsT, c.xbT) : Lists 𝒢 J ℓ) ∧
      StoreValid D s c ∧ PromoValid D i s c then
    ((auxWeight 𝒢.big (D.fam c.ν).C c.r *
        D.ρ ^ memZeros s *
        (∏ g, (Graph.primeGroupReciprocalMass (𝒢.big g) ^ promoCount c g)⁻¹) *
        (∏ g, ∏ sl : Slot J ℓ, if Fresh c g sl then tiltLaw (𝒢.big g) D.q D.n (c.xbT g sl) else 1) *
        D.ρ ^ memZeros (edgeTgt D i s c) *
        ((∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
          (smallDamping 𝒢 J ℓ D.q s.y *
            smallDamping 𝒢 J ℓ D.q
              ((resModel (smallPrimes 𝒢)).shift (edgeStep D i s c) s.y))) : ℝ) : ℂ) *
      (edgeMultiplier D i s c * expUnit (θ * (edgeStep D i s c : ℝ)))
  else 0

open _root_.Classical in
/-- The fresh births of an edge choice: for every big group and every target slot, the prime of
that slot if the slot is a fresh birth [S-02:1058–1059]. -/
def edgeBirths {𝔉 : N → Pattern 𝒢.big J ℓ} (c : EdgeChoice 𝒢 𝔉 Bc) :
    (g : B) → Slot J ℓ → Option ℕ :=
  fun g sl => if Fresh c g sl then some (c.xbT g sl : ℕ) else none

/-- **Clean choice** [S-02:0829–0830]: no store and no promotion; "a term is dirty if it has at
least one store or promotion, and clean otherwise". -/
def IsClean {𝔉 : N → Pattern 𝒢.big J ℓ} (c : EdgeChoice 𝒢 𝔉 Bc) : Prop :=
  (∀ g, c.store g = ∅) ∧ ∀ g sl, c.promo g sl = none

variable [Fintype N]

/-- A local transition choice of the whole edge operation: the source permutation, the choice
between the permutations, the target permutation [S-02:0477–0480]. -/
abbrev EdgeFullChoice (D : MemData 𝒢 J ℓ N) (Bc : ℕ) : Type :=
  ListPerms S B J ℓ × EdgeChoice 𝒢 D.fam Bc × ListPerms S B J ℓ

/-- The coefficient of the edge operation with a multiplier `ψ` on its fresh births: the two
averages over the slot permutations and the coefficient `edgeCoef` at the permuted source. -/
def edgeFullCoef (ψ : ((g : B) → Slot J ℓ → Option ℕ) → ℂ) (θ : ℝ) (i : ℕ)
    (s : MState 𝒢 J ℓ Bc) (ξ : EdgeFullChoice D Bc) : ℂ :=
  (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ *
    (ψ (edgeBirths ξ.2.1) * edgeCoef D θ i (s.permLists ξ.1) ξ.2.1) *
    (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹

/-- The state after the edge operation: permute the source lists, make the row transition,
permute the target lists. -/
def edgeFullTgt (i : ℕ) (s : MState 𝒢 J ℓ Bc) (ξ : EdgeFullChoice D Bc) : MState 𝒢 J ℓ Bc :=
  (edgeTgt D i (s.permLists ξ.1) ξ.2.1).permLists ξ.2.2

/-- **The edge operation `ℰ_i` with a multiplier on its fresh births** [S-02:1183–1196]: the row
operator of `edgeFullCoef`. It "sums the given patterns in orientation `σ_i`, with independent
source and target symmetrizations in all active lists" [S-02:0477–0479]; see
`edgeOpWith_eq_sym`. -/
def edgeOpWith (Bc : ℕ) (ψ : ((g : B) → Slot J ℓ → Option ℕ) → ℂ) (θ : ℝ) (i : ℕ) :
    (MState 𝒢 J ℓ Bc → ℂ) →ₗ[ℂ] (MState 𝒢 J ℓ Bc → ℂ) :=
  rowOp (edgeFullCoef D ψ θ i) (edgeFullTgt D i)

/-- **The edge operation `ℰ_i`** [S-02:0477–0514], truncated to total memory size at most `Bc`,
with the phase `e(θ σ_i k D)`. -/
def edgeOp (Bc : ℕ) (θ : ℝ) (i : ℕ) : (MState 𝒢 J ℓ Bc → ℂ) →ₗ[ℂ] (MState 𝒢 J ℓ Bc → ℂ) :=
  edgeOpWith D Bc (fun _ => 1) θ i

open _root_.Classical in
/-- **The clean part `ℰ_{i,clean}`** [S-02:0826–0833]: the terms without store and without
promotion. -/
def edgeClean (Bc : ℕ) (θ : ℝ) (i : ℕ) : (MState 𝒢 J ℓ Bc → ℂ) →ₗ[ℂ] (MState 𝒢 J ℓ Bc → ℂ) :=
  rowOp (fun s ξ => if IsClean ξ.2.1 then edgeFullCoef D (fun _ => 1) θ i s ξ else 0)
    (edgeFullTgt D i)

open _root_.Classical in
/-- **The dirty part `ℰ_{i,dirty}`** [S-02:0826–0833]: the terms with at least one store or
promotion. -/
def edgeDirty (Bc : ℕ) (θ : ℝ) (i : ℕ) : (MState 𝒢 J ℓ Bc → ℂ) →ₗ[ℂ] (MState 𝒢 J ℓ Bc → ℂ) :=
  rowOp (fun s ξ => if IsClean ξ.2.1 then 0 else edgeFullCoef D (fun _ => 1) θ i s ξ)
    (edgeFullTgt D i)

/-- `ℰ_i = ℰ_{i,clean} + ℰ_{i,dirty}` [S-02:0827–0828]. -/
theorem edgeOp_eq_clean_add_dirty (Bc : ℕ) (θ : ℝ) (i : ℕ) :
    edgeOp D Bc θ i = edgeClean D Bc θ i + edgeDirty D Bc θ i := by
  refine LinearMap.ext fun F => funext fun s => ?_
  simp only [edgeOp, edgeOpWith, edgeClean, edgeDirty, LinearMap.add_apply, Pi.add_apply,
    rowOp_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ξ _ => ?_
  split_ifs <;> simp

/-- **`ℰ_i` is the row transition between two symmetrizations** [S-02:0477–0480]:
`edgeOpWith ψ = memSym ∘ (row operator of ψ · edgeCoef) ∘ memSym`. -/
theorem edgeOpWith_eq_sym (Bc : ℕ) (ψ : ((g : B) → Slot J ℓ → Option ℕ) → ℂ) (θ : ℝ) (i : ℕ)
    (F : MState 𝒢 J ℓ Bc → ℂ) :
    edgeOpWith D Bc ψ θ i F =
      memSym 𝒢 J ℓ Bc
        (rowOp (fun s c => ψ (edgeBirths c) * edgeCoef D θ i s c) (edgeTgt D i)
          (memSym 𝒢 J ℓ Bc F)) := by
  funext s
  simp only [edgeOpWith, memSym, rowOp_apply, edgeFullCoef, edgeFullTgt, Fintype.sum_prod_type,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun π' _ => ?_
  ring_nf

end Edge

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
