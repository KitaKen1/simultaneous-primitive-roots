module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Statements
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.PathExpansion
public import SimultaneousPrimitiveRoots.Unconditional.Graph.PrimewiseLifespan
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The intermediate statements of the proof of [S] Lemma 3.7 (exact memory identity)

Source: `verification/stage7-sources/S-02.tex`, lines 316–582 (`[S-02:0316–0582]`): the one-prime
expansion [0316–0393], the memory Hilbert space and its operations [0395–0514], the identity and
its proof [0516–0582].

`MemoryIdentity` (`Proof35/Statements.lean`) is `phaseSum θ = (∏_{p big} b_p) · distinctSum Bc θ`
for all large `x`. This file splits it into eight exact statements for raw families of groups;
`Memory/Assembly.lean` proves `MemoryIdentity` from them.

## Skeletons

Both sides are sums over paths. A *skeleton* (`Skel`) is what the two expansions have in common:
the initial lists and, for every edge, the source permutation, the pattern, the auxiliary labels,
the target lists and the target permutation (a `PhysChoice`). The skeleton determines the lists at
every visit (`Skel.lists`), the dilations `D_i` (`Skel.dilAt`) and the offsets `h_i` (`Skel.off`).
A path of the physical expansion is a skeleton and a residue vector; a history of the memory
expansion is a skeleton, the small residues and a *decoration* (`Deco`): the choices of the visit
operations and the stores and promotions of the edges.

The weight of either kind of path is the product of

* `Skel.common` — the factors which the two expansions share literally: the small residues and
  small lists, the bans and the shared labels, the free-label probabilities, the coefficients
  `K_ν D^{iζ}`, the phases `e(θ σ_i k D_i)` and the symmetrization averages;
* a factor for the big primes: `Skel.bigPhysAt` (the conditions on the big residues, with the big
  endpoint damping) on the physical side, `History.memPart` (the coefficients of the visit
  operations and the memory part `edgeMemCoef` of the edge coefficients) on the memory side.

## The statements

```
MemoryIdentity                                    Lemma 3.7                         [S-02:0523–0535]
└─ memoryIdentity_of_parts (Assembly.lean)
   ├─ threshold (proved in Assembly.lean)         "for large x every group prime exceeds |k|", b_p > 0
   └─ MemoryIdentityRaw (proved from the parts)   the identity for raw families
      ├─ PhaseSkeleton        (A)   phaseSum    = E_y Σ_sk common · bigPhys         [0212–0234, 0293–0314]
      ├─ DistinctSkeleton     (B)   distinctSum = E_y Σ_sk common · memSum          [0516–0534]
      ├─ BigResidueProduct    (C1)  bigPhys = norm · 1_inj · ∏_p onePrimeExp        [0226–0234, 0327–0334]
      ├─ OnePrimeLifespan     (C2)  onePrimeExp = b_p · lifeSum                     [0327–0373]
      ├─ BornSetRecursion     (M1)  the distinct-birth rule as a running set        [0516–0521]
      ├─ GhostStepFactor      (M2)  a visit operation acts prime by prime           [0456–0475, 0569–0581]
      ├─ EdgeStepFactor       (M3)  an edge operation acts prime by prime           [0477–0514, 0569–0581]
      └─ ChainLifespan        (M4)  the per-prime transfer chain sums to lifeSum    [0538–0567]
```

(C1), (C2) are "the exact expansion for one big prime"; (M1)–(M4) are the proof of Lemma 3.7:
"these constructions are mutually inverse and preserve all coefficients". The route through
(M1)–(M3) replaces the global bijection between lifespan terms and histories by a recursion over
the operations: the sum over the choices of one operation, for a state in which every big prime
occurs at most once, is a product over the big primes (`PrimeVals`, `PrimeVals.eval`).

All statements were tested in exact arithmetic on small configurations (see the report).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators ComplexConjugate

noncomputable section

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N]

/-! ### Skeletons -/

/-- **The skeleton of a path** [S-02:0212–0215]: "fix the patterns, all endpoint permutations, the
auxiliary labels, and the active lists at visits `0, …, N`". The initial lists and one
`PhysChoice` (source permutation, pattern, auxiliary labels, target lists, target permutation) for
every edge. -/
structure Skel (D : MemData 𝒢 J ℓ N) where
  /-- the initial small list -/
  xs₀ : LabelList 𝒢.small J ℓ
  /-- the initial big list -/
  xb₀ : LabelList 𝒢.big J ℓ
  /-- the choices of the edges `0, …, N - 1` -/
  edge : Fin D.n → PhysChoice 𝒢 D.fam

/-- A skeleton is the triple of its components. -/
def Skel.equivProd (D : MemData 𝒢 J ℓ N) :
    Skel D ≃ LabelList 𝒢.small J ℓ × LabelList 𝒢.big J ℓ × (Fin D.n → PhysChoice 𝒢 D.fam) where
  toFun sk := (sk.xs₀, sk.xb₀, sk.edge)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv sk := by
    cases sk
    rfl
  right_inv t := by
    rcases t with ⟨a, b, c⟩
    rfl

instance Skel.instFintype (D : MemData 𝒢 J ℓ N) : Fintype (Skel D) := by
  haveI h1 : Fintype (LabelList 𝒢.small J ℓ) := inferInstance
  haveI h2 : Fintype (LabelList 𝒢.big J ℓ) := inferInstance
  haveI h3 : Fintype (PhysChoice 𝒢 D.fam) := physChoiceFintype 𝒢 D.fam
  haveI h4 : Fintype (Fin D.n → PhysChoice 𝒢 D.fam) := inferInstance
  exact Fintype.ofEquiv _ (Skel.equivProd D).symm

section SkelDefs

variable {D : MemData 𝒢 J ℓ N}

/-- The pattern of the edge `i`. -/
abbrev Skel.pat (sk : Skel D) (i : Fin D.n) : N := (sk.edge i).2.1.1

/-- The sets `C_g` of the pattern of the edge `i`. -/
abbrev Skel.Cset (sk : Skel D) (i : Fin D.n) : B → Finset (Fin J) := (D.fam (sk.pat i)).C

/-- The auxiliary free labels of the edge `i`. -/
abbrev Skel.aux (sk : Skel D) (i : Fin D.n) : AuxList 𝒢.big (sk.Cset i) := (sk.edge i).2.1.2.1

/-- The target lists of the edge `i`, in their canonical order (before the target permutation). -/
abbrev Skel.tgt (sk : Skel D) (i : Fin D.n) : Lists 𝒢 J ℓ := (sk.edge i).2.1.2.2

/-- **The lists at the visit `i`**: the initial lists at the visit `0`, and the permuted target
lists of the edge `i - 1` at the visit `i ≥ 1` (the initial lists for `i > N`). -/
def Skel.lists (sk : Skel D) : ℕ → Lists 𝒢 J ℓ
  | 0 => (sk.xs₀, sk.xb₀)
  | j + 1 =>
    if hj : j < D.n then permuteLists (sk.edge ⟨j, hj⟩).2.2 (sk.edge ⟨j, hj⟩).2.1.2.2
    else (sk.xs₀, sk.xb₀)

/-- The source lists of the edge `i`, in their canonical order (after the source permutation). -/
def Skel.src (sk : Skel D) (i : Fin D.n) : Lists 𝒢 J ℓ :=
  permuteLists (sk.edge i).1 (sk.lists i.val)

/-- The dilation `D_i` of the edge `i` [S-02:0216–0219]. -/
def Skel.dilAt (sk : Skel D) (i : Fin D.n) : ℕ := dil (sk.Cset i) (sk.src i) (sk.aux i)

/-- The step `σ_i k D_i` of the edge `i` [S-02:0216–0219]. -/
def Skel.step (sk : Skel D) (i : Fin D.n) : ℤ := edgeSign i.val * D.k * (sk.dilAt i : ℤ)

/-- **The offset `h_i`** [S-02:0216–0219]: `h_0 = 0`, `h_{i+1} - h_i = σ_i k D_i`. -/
def Skel.off (sk : Skel D) (i : ℕ) : ℤ := ∑ j : Fin D.n, if j.val < i then sk.step j else 0

/-- **The conditions on a skeleton which involve big labels and no residue**: at every edge the
shared big labels are copied and no auxiliary free label occurs in the source or in the target
lists [S-02:0058–0059, 0109–0110]. The skeletons without this property have `Skel.common = 0`. -/
def Skel.BigValid (sk : Skel D) : Prop :=
  ∀ i : Fin D.n, SharedBig (sk.Cset i) (sk.src i).2 (sk.tgt i).2 ∧
    AuxAvoids (sk.Cset i) (sk.aux i) (sk.src i) ∧ AuxAvoids (sk.Cset i) (sk.aux i) (sk.tgt i)

/-- The big lists are injective at every visit `0, …, N`. -/
def Skel.BigInj (sk : Skel D) : Prop :=
  ∀ i : ℕ, i ≤ D.n → ∀ g : B, Function.Injective ((sk.lists i).2 g)

/-! ### The common part -/

/-- The oriented coefficient of the edge `i`: `K_ν D^{iζ}` on a forward edge, "or its conjugate
with roles interchanged" on a backward edge [S-02:0484–0486]. -/
def Skel.mult (sk : Skel D) (i : Fin D.n) : ℂ :=
  if i.val % 2 = 0 then
    (D.fam (sk.pat i)).K (sk.src i).2 (sk.tgt i).2 (sk.aux i) *
      ((sk.dilAt i : ℕ) : ℂ) ^ ((D.ζ : ℂ) * Complex.I)
  else
    conj ((D.fam (sk.pat i)).K (sk.tgt i).2 (sk.src i).2 (sk.aux i) *
      ((sk.dilAt i : ℕ) : ℂ) ^ ((D.ζ : ℂ) * Complex.I))

open _root_.Classical in
/-- **The common factor of the edge `i`**, for the small residues `y` at the visit `0`: it is zero
unless the small lists are small states at `y + h_i` and `y + h_{i+1}` with the same shared labels,
the big target list has the shared labels of the source, and no auxiliary label occurs in the
lists; otherwise it is the probability of the auxiliary labels, the small normalization
`∏_{g ∈ 𝒮} V_g^{-ℓ}`, the two small endpoint factors, the oriented coefficient and the phase
`e(θ σ_i k D_i)`. -/
def Skel.edgeCommon (sk : Skel D) (θ : ℝ) (y : ResVec (smallPrimes 𝒢)) (i : Fin D.n) : ℂ :=
  if IsSmallState 𝒢 ((resModel (smallPrimes 𝒢)).shift (sk.off i.val) y) (sk.src i).1 ∧
      IsSmallState 𝒢 ((resModel (smallPrimes 𝒢)).shift (sk.off (i.val + 1)) y) (sk.tgt i).1 ∧
      SharedSmall (sk.src i).1 (sk.tgt i).1 ∧
      SharedBig (sk.Cset i) (sk.src i).2 (sk.tgt i).2 ∧
      AuxAvoids (sk.Cset i) (sk.aux i) (sk.src i) ∧
      AuxAvoids (sk.Cset i) (sk.aux i) (sk.tgt i) then
    ((auxWeight 𝒢.big (sk.Cset i) (sk.aux i) *
        ((∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
          (smallDamping 𝒢 J ℓ D.q ((resModel (smallPrimes 𝒢)).shift (sk.off i.val) y) *
            smallDamping 𝒢 J ℓ D.q
              ((resModel (smallPrimes 𝒢)).shift (sk.off (i.val + 1)) y))) : ℝ) : ℂ) *
      (sk.mult i * expUnit (θ * (sk.step i : ℝ)))
  else 0

open _root_.Classical in
/-- **The common part of the weight of a path with skeleton `sk` and small residues `y`**: the
mass `∏_{g ∈ 𝒮} V_g^{-M}` of the initial small state, and for every edge the two symmetrization
averages and the common factor `Skel.edgeCommon`. (The Haar mass of `y` is not included.) -/
def Skel.common (sk : Skel D) (θ : ℝ) (y : ResVec (smallPrimes 𝒢)) : ℂ :=
  (if IsSmallState 𝒢 y sk.xs₀ then ((smallListMass 𝒢 J ℓ : ℝ) : ℂ) else 0) *
    ∏ i : Fin D.n, ((Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ * sk.edgeCommon θ y i *
      (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹)

end SkelDefs

/-! ### The big physical part -/

/-- **Big state at `y`**: an ordered list of `M` distinct zero coordinates of the big residue
vector `y` in each big group (the big half of `IsPhys`). -/
def IsBigState (𝒢 : GroupFamily S B) {J ℓ : ℕ} (y : ResVec (bigPrimes 𝒢))
    (xb : LabelList 𝒢.big J ℓ) : Prop :=
  (∀ g, Function.Injective (xb g)) ∧ ∀ g i, (resModel (bigPrimes 𝒢)).hit (xb g i) y

/-- The big endpoint factor `∏_{g ∈ ℬ} q^{(ω_g(y) - M)/2}` (the big half of `damping`). -/
def bigDamping (𝒢 : GroupFamily S B) (J ℓ : ℕ) (q : ℝ) (y : ResVec (bigPrimes 𝒢)) : ℝ :=
  q ^ ((((∑ g, countHits (fun p => (resModel (bigPrimes 𝒢)).hit p y) (𝒢.big g) : ℕ) : ℝ) -
    ((J + ℓ : ℕ) : ℝ) * (Fintype.card B : ℝ)) / 2)

/-- `∏_{g ∈ ℬ} V_g^{-M}`: the big half of `stateMass`. -/
def bigListNorm (𝒢 : GroupFamily S B) (J ℓ : ℕ) : ℝ :=
  ∏ g : B, (Graph.primeGroupReciprocalMass (𝒢.big g) ^ (J + ℓ))⁻¹

/-- `∏_{g ∈ ℬ} V_g^{-t_g}`, `t_g = ℓ + |C_g|`: the big half of `targetNorm`. -/
def bigTargetNorm (𝒢 : GroupFamily S B) {J : ℕ} (ℓ : ℕ) (C : B → Finset (Fin J)) : ℝ :=
  ∏ g : B, (Graph.primeGroupReciprocalMass (𝒢.big g) ^ (ℓ + (C g).card))⁻¹

section SkelBig

variable {D : MemData 𝒢 J ℓ N}

open _root_.Classical in
/-- **The big part of the physical weight** of a path with skeleton `sk` and big residues `y` at
the visit `0` (the factor (eq:path-residue-factor) [S-02:0226–0234] for the big primes, with the
label normalization): `∏_{g ∈ ℬ} V_g^{-M}` if the initial big list is a big state at `y`, and for
every edge `∏_{g ∈ ℬ} V_g^{-t_g}` and the two big endpoint factors if the source and the target
big lists are big states at `y + h_i` and `y + h_{i+1}`; zero otherwise. -/
def Skel.bigPhysAt (sk : Skel D) (y : ResVec (bigPrimes 𝒢)) : ℝ :=
  (if IsBigState 𝒢 y sk.xb₀ then bigListNorm 𝒢 J ℓ else 0) *
    ∏ i : Fin D.n,
      if IsBigState 𝒢 ((resModel (bigPrimes 𝒢)).shift (sk.off i.val) y) (sk.src i).2 ∧
          IsBigState 𝒢 ((resModel (bigPrimes 𝒢)).shift (sk.off (i.val + 1)) y) (sk.tgt i).2 then
        bigTargetNorm 𝒢 ℓ (sk.Cset i) *
          (bigDamping 𝒢 J ℓ D.q ((resModel (bigPrimes 𝒢)).shift (sk.off i.val) y) *
            bigDamping 𝒢 J ℓ D.q ((resModel (bigPrimes 𝒢)).shift (sk.off (i.val + 1)) y))
      else 0

/-- **The expectation of the big part of the physical weight** under independent uniform residues
at the big primes [S-02:0238–0240, 0293–0296]. -/
def Skel.bigPhys (sk : Skel D) : ℝ :=
  (Fintype.card (ResVec (bigPrimes 𝒢)) : ℝ)⁻¹ * ∑ y : ResVec (bigPrimes 𝒢), sk.bigPhysAt y

/-- The label normalization of the big groups along a skeleton: `∏_{g ∈ ℬ} V_g^{-M}` initially
and `∏_{g ∈ ℬ} V_g^{-t_g}` at each edge [S-02:0232–0233]. -/
def Skel.bigNormAll (sk : Skel D) : ℝ :=
  bigListNorm 𝒢 J ℓ * ∏ i : Fin D.n, bigTargetNorm 𝒢 ℓ (sk.Cset i)

end SkelBig

/-! ### The memory part -/

section MemPart

variable {Bc : ℕ}

open _root_.Classical in
/-- **The memory part of the coefficient `edgeCoef` of an edge**: zero unless the total memory
size is at most `Bc` before and after and the stores and promotions are admissible; otherwise
`ρ` for every old pending zero, `V_g^{-1}` per promotion, `μ̃_g(p)` for every fresh target label
and `ρ` for every pending zero remaining after promotions [S-02:0487–0503]. -/
def edgeMemCoef (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (c : EdgeChoice 𝒢 D.fam Bc) : ℝ :=
  if memTotal s ≤ Bc ∧ (∑ g, (edgeNewList D i s c g).length) ≤ Bc ∧
      StoreValid D s c ∧ PromoValid D i s c then
    D.ρ ^ memZeros s *
      (∏ g, (Graph.primeGroupReciprocalMass (𝒢.big g) ^ promoCount c g)⁻¹) *
      (∏ g, ∏ sl : Slot J ℓ, if Fresh c g sl then tiltLaw (𝒢.big g) D.q D.n (c.xbT g sl) else 1) *
      D.ρ ^ memZeros (edgeTgt D i s c)
  else 0

/-- **A decoration of a skeleton**: what a history contains beyond its skeleton and its small
residues. The choices of the visit operations `G_0, …, G_N` (terminated pending zeros and
batches of ghost births) and, for every edge, the stored source slots and the promotions. -/
structure Deco (𝒢 : GroupFamily S B) (J ℓ Bc n : ℕ) where
  /-- the choices of the visit operations -/
  ghost : Fin (n + 1) → GhostChoice 𝒢 Bc
  /-- the stored source slots of every edge -/
  store : Fin n → (g : B) → Finset (Slot J ℓ)
  /-- the promotions of every edge -/
  promo : Fin n → (g : B) → Slot J ℓ → Option (Fin Bc)

/-- A decoration is the triple of its components. -/
def Deco.equivProd (𝒢 : GroupFamily S B) (J ℓ Bc n : ℕ) :
    Deco 𝒢 J ℓ Bc n ≃ (Fin (n + 1) → GhostChoice 𝒢 Bc) ×
      (Fin n → (g : B) → Finset (Slot J ℓ)) × (Fin n → (g : B) → Slot J ℓ → Option (Fin Bc)) where
  toFun d := (d.ghost, d.store, d.promo)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv d := by
    cases d
    rfl
  right_inv t := by
    rcases t with ⟨a, b, c⟩
    rfl

instance Deco.instFintype (𝒢 : GroupFamily S B) (J ℓ Bc n : ℕ) : Fintype (Deco 𝒢 J ℓ Bc n) := by
  haveI h1 : Fintype (GhostChoice 𝒢 Bc) := inferInstance
  haveI h2 : Fintype ((g : B) → Finset (Slot J ℓ)) := inferInstance
  haveI h3 : Fintype ((g : B) → Slot J ℓ → Option (Fin Bc)) := inferInstance
  exact Fintype.ofEquiv _ (Deco.equivProd 𝒢 J ℓ Bc n).symm

variable {D : MemData 𝒢 J ℓ N}

/-- The row choice of the edge `i` with the stores `st` and the promotions `pr`. -/
def Skel.edgeChoice (sk : Skel D) (i : Fin D.n) (st : (g : B) → Finset (Slot J ℓ))
    (pr : (g : B) → Slot J ℓ → Option (Fin Bc)) : EdgeChoice 𝒢 D.fam Bc :=
  ⟨sk.pat i, sk.aux i, st, pr, (sk.tgt i).1, (sk.tgt i).2⟩

/-- **The history with skeleton `sk`, initial small residues `y` and decoration `d`.** -/
def Skel.hist (sk : Skel D) (y : ResVec (smallPrimes 𝒢)) (d : Deco 𝒢 J ℓ Bc D.n) :
    History D Bc where
  y₀ := y
  xs₀ := sk.xs₀
  xb₀ := sk.xb₀
  ghost := d.ghost
  edge := fun i => ((sk.edge i).1, sk.edgeChoice i (d.store i) (d.promo i), (sk.edge i).2.2)

/-- **The memory part of the weight of a history**: the measure `⊗ μ̃_g^{⊗M}` of the initial big
list, the coefficients of the visit operations, the memory parts of the coefficients of the edges
and `𝟏_∅` at the end. -/
def History.memPart (h : History D Bc) : ℝ :=
  bigListMass 𝒢 D.q D.n h.xb₀ *
    (∏ i : Fin D.n, ghostCoef D i.val (h.visitState i.val) (h.ghost i.castSucc) *
      edgeMemCoef D i.val ((h.afterGhost i.castSucc).permLists (h.edge i).1) (h.edge i).2.1) *
    (ghostCoef D D.n (h.visitState D.n) (h.ghost (Fin.last D.n)) *
      (if memTotal (h.afterGhost (Fin.last D.n)) = 0 then 1 else 0))

open _root_.Classical in
/-- **The memory sum of a skeleton**: the sum over the decorations with pairwise distinct births
of the memory part of the weight of the history ("all prime values assigned at different births
are distinct", [S-02:0516–0521]). The initial small residues do not enter (they are set to `0`). -/
def Skel.memSum (sk : Skel D) (Bc : ℕ) : ℝ :=
  ∑ d : Deco 𝒢 J ℓ Bc D.n,
    if Graph.PerformedBirthsDistinct (sk.hist (fun _ => 0) d).birth then
      (sk.hist (fun _ => 0) d).memPart
    else 0

end MemPart

/-! ### One big prime: the residue expectation and the lifespan sum -/

/-- The four lifespans of a prime which is active at some visit (eq:prefix-ghost)
[S-02:0335–0349], in the form of `Graph.primewise_active_lifespan_expectation`: "the prime either
starts at `a_p` or has an earlier ghost birth at a hit `j < a_p`, with coefficient `-η_j`; it
either ends at `z_p` or has a later ghost termination at a hit `j > z_p`, again with coefficient
`-η_j`. At strictly internal unmarked hits it receives `q_i`." Here `s` is the set of visits, `A`
the set of active visits, `a`, `z` the first and the last active visit, `c₀` the common residue. -/
def activeBracket {C : Type} [Fintype C] [DecidableEq C] (s A : Finset ℕ) (color : ℕ → C)
    (η : ℕ → ℝ) (c₀ : C) (a z : ℕ) : ℝ :=
  Graph.lifespanDamping (s \ A) (fun i => Graph.hitWeight color η i c₀) a z -
    (∑ j ∈ s \ A with j < a, Graph.hitWeight color η j c₀ *
      Graph.lifespanDamping (s \ A) (fun i => Graph.hitWeight color η i c₀) j z) -
    (∑ k ∈ s \ A with z < k, Graph.hitWeight color η k c₀ *
      Graph.lifespanDamping (s \ A) (fun i => Graph.hitWeight color η i c₀) a k) +
    ∑ j ∈ s \ A with j < a, ∑ k ∈ s \ A with z < k,
      Graph.hitWeight color η j c₀ * Graph.hitWeight color η k c₀ *
        Graph.lifespanDamping (s \ A) (fun i => Graph.hitWeight color η i c₀) j k

/-- The orphan intervals of a prime which is never active (eq:orphan-expansion)
[S-02:0351–0365], in the form of `Graph.primewise_orphan_expectation`:
`∑_{j<i} η_j η_i 1_{h_j ≡ h_i (p)} ∏_{j<t<i} (1 - η_t 1_{h_t ≡ h_j (p)})`. -/
def orphanSum {C : Type} [Fintype C] [DecidableEq C] (s : Finset ℕ) (color : ℕ → C)
    (η : ℕ → ℝ) : ℝ :=
  ∑ z ∈ s, ∑ a ∈ s with a < z,
    if color a = color z then
      η a * η z * ∏ j ∈ s with a < j ∧ j < z, (1 - Graph.hitWeight color η j (color a))
    else 0

section OnePrime

variable {D : MemData 𝒢 J ℓ N}

open _root_.Classical in
/-- The visits `0 ≤ i ≤ N` at which the natural number `p` is a label of a big active list. -/
def Skel.activeVisits (sk : Skel D) (p : ℕ) : Finset ℕ :=
  (Finset.range (D.n + 1)).filter fun i => ∃ g sl, ((sk.lists i).2 g sl : ℕ) = p

/-- **The residue expectation of one prime** [S-02:0327–0334]: the mean over the residue
`t ∈ ℤ/pℤ` of the product over the visits `i = 0, …, N` of `1_{t + h_i = 0}` if `p` is active at
the visit `i`, and of `q_i^{1_{t + h_i = 0}}` otherwise ("its residue expectation is
`p⁻¹ ∏_{i : p ∉ Λ_i} (1 - η_i H_i)`"). -/
def Skel.onePrimeExp (sk : Skel D) (p : ℕ) : ℝ :=
  (p : ℝ)⁻¹ * ∑ t : Res p, ∏ i ∈ Finset.range (D.n + 1),
    if i ∈ sk.activeVisits p then
      (if t + ((sk.off i : ℤ) : Res p) = 0 then (1 : ℝ) else 0)
    else (if t + ((sk.off i : ℤ) : Res p) = 0 then visitQ D.q D.n i else 1)

/-- The residue `-h_i` modulo `p`: the residue `t` at the visit `0` for which `p` divides the
position at the visit `i`. -/
def Skel.color (sk : Skel D) (p : ℕ) (i : ℕ) : Res p := -((sk.off i : ℤ) : Res p)

open _root_.Classical in
/-- **The lifespan sum of one prime, relative to the baseline** [S-02:0327–0373]: "each
represented big prime has exactly one lifespan: an interval containing all its active visits,
possibly containing none. Its endpoints and all its active visits have equal offsets modulo `p`.
It pays `(p b_p)⁻¹` once, the ghost endpoint coefficients if present, and `q_i` at each strictly
internal unmarked hit."

* `p` active at some visit, with compatible offsets: the four lifespans `activeBracket` between
  the first and the last active visit, times `(p b_p)⁻¹`;
* `p` active with incompatible offsets: `0` ("incompatible active offsets give zero");
* `p` never active: `1 + (p b_p)⁻¹ · orphanSum` ("relative to the baseline, the prime is either
  absent or has an orphan interval"). -/
def Skel.lifeSum (sk : Skel D) (p : ℕ) : ℝ :=
  if h : (sk.activeVisits p).Nonempty then
    if ∀ i ∈ sk.activeVisits p, sk.color p i = sk.color p ((sk.activeVisits p).min' h) then
      activeBracket (Finset.range (D.n + 1)) (sk.activeVisits p) (sk.color p) (visitEta D.q D.n)
          (sk.color p ((sk.activeVisits p).min' h)) ((sk.activeVisits p).min' h)
          ((sk.activeVisits p).max' h) /
        ((p : ℝ) * lifeBaseline D.q D.n p)
    else 0
  else
    1 + orphanSum (Finset.range (D.n + 1)) (sk.color p) (visitEta D.q D.n) /
      ((p : ℝ) * lifeBaseline D.q D.n p)

end OnePrime

/-! ### Values of the big primes and their product -/

/-- **A value for every big prime in each of its four conditions**: active in a list (`act`),
pending in a memory with a residue (`pend`, a function of the particle), born earlier and no
longer present (`dead`), not yet born (`unborn`). The functions which occur in the proof are the
total weights of the future of a prime. -/
structure PrimeVals (𝒢 : GroupFamily S B) where
  /-- the value of an active prime -/
  act : (g : B) → {p : ℕ // p ∈ 𝒢.big g} → ℝ
  /-- the value of a pending particle -/
  pend : (g : B) → Particle 𝒢 g → ℝ
  /-- the value of a prime which was born and is no longer present -/
  dead : (g : B) → {p : ℕ // p ∈ 𝒢.big g} → ℝ
  /-- the value of a prime which was not born -/
  unborn : (g : B) → {p : ℕ // p ∈ 𝒢.big g} → ℝ

section Eval

variable {Bc : ℕ}

open _root_.Classical in
/-- **The product of the values of the big primes** in the condition in which they are for the big
active list `xb`, the memories `mem` and the set `U` of the primes born so far: one factor `act`
for every slot, one factor `pend` for every pending particle, and for every prime of a big group
which is neither in the list nor in the memory of its group the factor `dead` if it is in `U` and
`unborn` otherwise. -/
def PrimeVals.eval (v : PrimeVals 𝒢) (xb : LabelList 𝒢.big J ℓ) (mem : (g : B) → Mem 𝒢 Bc g)
    (U : Finset ℕ) : ℝ :=
  (∏ g, ∏ sl : Slot J ℓ, v.act g (xb g sl)) *
    (∏ g, ∏ j : Fin (mem g).1.val, v.pend g ((mem g).2 j)) *
    ∏ g, ∏ p : {p : ℕ // p ∈ 𝒢.big g},
      if (p : ℕ) ∈ U then
        (if (∃ sl, xb g sl = p) ∨ (∃ j, ((mem g).2 j).1 = p) then 1 else v.dead g p)
      else v.unborn g p

/-- **Every big prime occurs at most once**: the big lists are injective, the pending particles of
a group have distinct primes, no prime is both active and pending, every prime which is present
was born (is in `U`), and `U` consists of big primes. "A numerical prime occupies at most one
active slot or pending particle, because it has only one birth" [S-02:0577–0578]. -/
def MemConsistent (xb : LabelList 𝒢.big J ℓ) (mem : (g : B) → Mem 𝒢 Bc g) (U : Finset ℕ) :
    Prop :=
  (∀ g, Function.Injective (xb g)) ∧
    (∀ g, Function.Injective fun j : Fin (mem g).1.val => ((mem g).2 j).1) ∧
    (∀ g sl (j : Fin (mem g).1.val), xb g sl ≠ ((mem g).2 j).1) ∧
    (∀ g sl, (xb g sl : ℕ) ∈ U) ∧
    (∀ g (j : Fin (mem g).1.val), (((mem g).2 j).1 : ℕ) ∈ U) ∧ U ⊆ bigPrimes 𝒢

end Eval

/-- The final values: after the last visit operation the memories must be empty
("at visit `N` it must end empty", [S-02:0553–0554]). -/
def finalVals (𝒢 : GroupFamily S B) : PrimeVals 𝒢 where
  act := fun _ _ => 1
  pend := fun _ _ => 0
  dead := fun _ _ => 1
  unborn := fun _ _ => 1

/-- **The action of the visit operation `G_i` on the values of one prime** (eq:ghost-row)
[S-02:0456–0475]: a pending zero terminates (`-η_i/ρ`) or continues (`q_i/ρ²`); a pending
particle with nonzero residue, an active and a dead prime are not touched; an unborn prime stays
unborn or is born at residue zero, with the coefficient `(-η_i V_g/ρ) μ̃_g(p)`. -/
def ghostStepVals (D : MemData 𝒢 J ℓ N) (i : ℕ) (v : PrimeVals 𝒢) : PrimeVals 𝒢 where
  act := v.act
  pend := fun g z =>
    if z.2 = 0 then
      Graph.sourceGhostD (visitQ D.q D.n i) D.ρ * v.dead g z.1 +
        Graph.sourceGhostA (visitQ D.q D.n i) D.ρ * v.pend g z
    else v.pend g z
  dead := v.dead
  unborn := fun g p =>
    v.unborn g p +
      Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ D.q D.n i) D.ρ *
        tiltLaw (𝒢.big g) D.q D.n p * v.pend g ⟨p, 0⟩

section EdgeVals

variable {D : MemData 𝒢 J ℓ N}

open _root_.Classical in
/-- The number of unshared target slots of the big group `g` at the edge `i` whose label is `p`:
the slots through which `p` can enter the active list at this edge (by a promotion or by a fresh
birth). -/
def Skel.entryCount (sk : Skel D) (i : Fin D.n) (g : B) (p : {p : ℕ // p ∈ 𝒢.big g}) : ℕ :=
  (Finset.univ.filter fun sl : Slot J ℓ =>
    Unshared (sk.Cset i g) sl ∧ (sk.tgt i).2 g sl = p).card

open _root_.Classical in
/-- **The action of the edge operation `ℰ_i` on the values of one prime** [S-02:0477–0514], for
the skeleton `sk`; `e` is the number of unshared target slots with the label `p`
(`Skel.entryCount`), `Δ = σ_i k D_i`.

* active in a shared source slot: it stays active (`e = 0`);
* active in an unshared source slot (`e = 0`): it is stored, if `p ∤ D_i`, with residue `Δ`
  (and `ρ` if this residue is zero), or dropped;
* pending with residue `r`: `ρ` if `r = 0`; then it is promoted (`e = 1`, `r + Δ = 0`,
  `p ∤ D_i`; factor `V_g⁻¹`) or stays pending with residue `r + Δ` (`e = 0`; `ρ` if `r + Δ = 0`);
* dead: it stays dead (`e = 0`);
* unborn: it stays unborn (`e = 0`) or is born in an unshared target slot (`e = 1`; factor
  `μ̃_g(p)`).

In all other cases the value is `0`. -/
def Skel.edgeStepVals (sk : Skel D) (i : Fin D.n) (v : PrimeVals 𝒢) : PrimeVals 𝒢 where
  act := fun g p =>
    if ∃ j : Fin J, j ∉ sk.Cset i g ∧ (sk.src i).2 g (Sum.inl j) = p then
      (if sk.entryCount i g p = 0 then v.act g p else 0)
    else if sk.entryCount i g p = 0 then
      (if (p : ℕ) ∣ sk.dilAt i then 0
        else D.ρ ^ (if (shiftParticle (sk.step i) (⟨p, 0⟩ : Particle 𝒢 g)).2 = 0 then 1 else 0) *
          v.pend g (shiftParticle (sk.step i) ⟨p, 0⟩)) + v.dead g p
    else 0
  pend := fun g z =>
    D.ρ ^ (if z.2 = 0 then 1 else 0) *
      ((if sk.entryCount i g z.1 = 1 ∧ (shiftParticle (sk.step i) z).2 = 0 ∧
            ¬((z.1 : ℕ) ∣ sk.dilAt i) then
          (Graph.primeGroupReciprocalMass (𝒢.big g))⁻¹ * v.act g z.1
        else 0) +
        (if sk.entryCount i g z.1 = 0 then
          D.ρ ^ (if (shiftParticle (sk.step i) z).2 = 0 then 1 else 0) *
            v.pend g (shiftParticle (sk.step i) z)
        else 0))
  dead := fun g p => if sk.entryCount i g p = 0 then v.dead g p else 0
  unborn := fun g p =>
    if sk.entryCount i g p = 0 then v.unborn g p
    else if sk.entryCount i g p = 1 then tiltLaw (𝒢.big g) D.q D.n p * v.act g p
    else 0

/-- **The transfer chain of the big primes along a skeleton**: `chain m` is the family of the
total weights of the future of a prime at the visit `N - m`, before the visit operation
`G_{N-m}`. `chain 0 = G_N (final values)`, `chain (m + 1) = G_{N-m-1} ℰ_{N-m-1} (chain m)`. -/
def Skel.chain (sk : Skel D) : ℕ → PrimeVals 𝒢
  | 0 => ghostStepVals D D.n (finalVals 𝒢)
  | m + 1 =>
    if h : m < D.n then
      ghostStepVals D (D.n - (m + 1))
        (sk.edgeStepVals ⟨D.n - (m + 1), Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le m) h)
          (Nat.succ_pos m)⟩ (sk.chain m))
    else sk.chain m

end EdgeVals

/-! ### The sums over the choices of one operation, with the set of the primes born so far -/

/-- The set of the values of an assignment of births to addresses. -/
def birthSet {ι : Type} [Fintype ι] (β : ι → Option ℕ) : Finset ℕ :=
  Finset.univ.biUnion fun i => (β i).elim ∅ fun z => {z}

/-- **New births**: the performed births have pairwise distinct values, none of which is in `U`
(the distinct-birth rule [S-02:0516–0521] for one operation, given the set `U` of the values
born earlier). -/
def NewBirths {ι : Type} (β : ι → Option ℕ) (U : Finset ℕ) : Prop :=
  Graph.PerformedBirthsDistinct β ∧ ∀ i z, β i = some z → z ∉ U

section StepSums

variable {Bc : ℕ}

/-- The ghost births of a visit operation, by address (group and index in the batch), as in
`History.birth`. -/
def ghostAddrBirth (c : GhostChoice 𝒢 Bc) : B × Fin Bc → Option ℕ :=
  fun a =>
    if hj : a.2.val < (c a.1).2.1.val then some ((c a.1).2.2 ⟨a.2.val, hj⟩ : ℕ) else none

/-- The fresh births of an edge, by address (group and target slot), as in `History.birth`. -/
def edgeAddrBirth {𝔉 : N → Pattern 𝒢.big J ℓ} (c : EdgeChoice 𝒢 𝔉 Bc) :
    B × Slot J ℓ → Option ℕ :=
  fun a => edgeBirths c a.1 a.2

variable {D : MemData 𝒢 J ℓ N}

/-- The memory state with the lists of the skeleton at the visit `i` and the memories `mem` (the
small residues are irrelevant for the memory parts of the coefficients; they are set to `0`). -/
def Skel.mstate (sk : Skel D) (i : ℕ) (mem : (g : B) → Mem 𝒢 Bc g) : MState 𝒢 J ℓ Bc :=
  ⟨fun _ => 0, (sk.lists i).1, (sk.lists i).2, mem⟩

open _root_.Classical in
/-- **The sum over the choices of the visit operation `G_i`** with new births, from the memories
`mem` and the set `U` of the primes born so far, of the coefficient times the value of `Ψ` at the
new memories and the enlarged set. -/
def Skel.ghostSum (sk : Skel D) (Bc : ℕ) (i : ℕ)
    (Ψ : ((g : B) → Mem 𝒢 Bc g) → Finset ℕ → ℝ) (mem : (g : B) → Mem 𝒢 Bc g) (U : Finset ℕ) :
    ℝ :=
  ∑ c : GhostChoice 𝒢 Bc,
    if NewBirths (ghostAddrBirth c) U then
      ghostCoef D i (sk.mstate i mem) c *
        Ψ (fun g => ghostNewMem (mem g) (c g)) (U ∪ birthSet (ghostAddrBirth c))
    else 0

open _root_.Classical in
/-- **The sum over the stores and promotions of the edge `i`** with new fresh births, from the
memories `mem` (after `G_i`) and the set `U`, of the memory part of the coefficient times the
value of `Ψ` at the new memories and the enlarged set. -/
def Skel.edgeSum (sk : Skel D) (Bc : ℕ) (i : Fin D.n)
    (Ψ : ((g : B) → Mem 𝒢 Bc g) → Finset ℕ → ℝ) (mem : (g : B) → Mem 𝒢 Bc g) (U : Finset ℕ) :
    ℝ :=
  ∑ st : (g : B) → Finset (Slot J ℓ), ∑ pr : (g : B) → Slot J ℓ → Option (Fin Bc),
    if NewBirths (edgeAddrBirth (sk.edgeChoice i st pr)) U then
      edgeMemCoef D i.val ((sk.mstate i.val mem).permLists (sk.edge i).1)
          (sk.edgeChoice i st pr) *
        Ψ (fun g => memOfList (edgeNewList D i.val
            ((sk.mstate i.val mem).permLists (sk.edge i).1) (sk.edgeChoice i st pr) g))
          (U ∪ birthSet (edgeAddrBirth (sk.edgeChoice i st pr)))
    else 0

/-- **The future of the memory part**: `fut m mem U` is the sum over the choices of the operations
`G_{N-m}, ℰ_{N-m}, …, ℰ_{N-1}, G_N`, with births which are distinct and not in `U`, of the product
of the memory parts of the coefficients and of `𝟏_∅` at the end, starting from the memories `mem`
at the visit `N - m`. -/
def Skel.fut (sk : Skel D) (Bc : ℕ) : ℕ → ((g : B) → Mem 𝒢 Bc g) → Finset ℕ → ℝ
  | 0 => sk.ghostSum Bc D.n fun mem _ => if (∑ g, (mem g).1.val) = 0 then 1 else 0
  | m + 1 =>
    if h : m < D.n then
      sk.ghostSum Bc (D.n - (m + 1))
        (sk.edgeSum Bc ⟨D.n - (m + 1), Nat.sub_lt (Nat.lt_of_le_of_lt (Nat.zero_le m) h)
          (Nat.succ_pos m)⟩ (sk.fut Bc m))
    else fun _ _ => 0

end StepSums

/-! ### The statements -/

/-- **The hypotheses of the exact identity for a raw family of groups**: what the proof of
Lemma 3.7 uses of Definition 3.1 and of the standing hypotheses. -/
structure RawHyp (D : MemData 𝒢 J ℓ N) : Prop where
  /-- the elements of the small groups are primes -/
  prime_small : ∀ g, ∀ p ∈ 𝒢.small g, Nat.Prime p
  /-- the elements of the big groups are primes -/
  prime_big : ∀ g, ∀ p ∈ 𝒢.big g, Nat.Prime p
  /-- the big groups are pairwise disjoint -/
  disjoint_big : ∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g')
  /-- a small group and a big group are disjoint -/
  disjoint_small_big : ∀ g g', Disjoint (𝒢.small g) (𝒢.big g')
  /-- no group prime divides `k` ("for large `x` every group prime exceeds `|k|`", [S-02:0376]) -/
  not_dvd : ∀ p ∈ 𝒢.allPrimes, ¬((p : ℤ) ∣ D.k)
  /-- `b_p ≠ 0` for every big prime (eq:lifespan-baseline) -/
  baseline_ne : ∀ p ∈ bigPrimes 𝒢, lifeBaseline D.q D.n p ≠ 0
  /-- `q > 0` -/
  q_pos : 0 < D.q
  /-- `ρ ≠ 0` -/
  ρ_ne : D.ρ ≠ 0

/-- **The memory identity for raw families** (Lemma 3.7 without threshold): for every family of
groups, all parameters and patterns, `N = 2R` with `R ≥ 1`, under `RawHyp` and for every cutoff
`Bc ≥ #{big primes}`: `phaseSum θ = (∏_{p big} b_p) · distinctSum Bc θ`.

It is proved in `Memory/Assembly.lean` from the eight statements below. `R ≥ 1` is needed: for
`N = 0` the only visit has `q_0 = √q` in `b_p` but no endpoint factor in the moment. -/
def MemoryIdentityRaw : Prop :=
  ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] (𝒢 : GroupFamily S B)
    (J ℓ : ℕ) (N : Type) [Fintype N] (D : MemData 𝒢 J ℓ N) (Bc R : ℕ) (θ : ℝ),
    D.n = 2 * R → 0 < R → RawHyp D → (bigPrimes 𝒢).card ≤ Bc →
    phaseSum 𝒢 D.q D.fam D.k D.ζ R θ =
      ((baselineProd (bigPrimes 𝒢) D.q D.n : ℝ) : ℂ) * distinctSum D Bc θ

/-- **(A) The physical path expansion by skeletons** [S-02:0212–0234, 0293–0314].

"Expand the left side of (eq:transference-moment) into paths with `N` alternating forward and
backward edges. Fix the patterns, all endpoint permutations, the auxiliary labels, and the active
lists at visits `0, …, N`. These choices fix offsets `h_0 = 0, h_1, …, h_N` … The dependence on the
initial integer `n` is precisely the nonnegative factor (eq:path-residue-factor) … The label
normalization is initially `∏_g V_g^{-M}` and at each edge `∏_g V_g^{-t_g}`, in addition to the
free-label probabilities. All remaining factors are independent of `n`."

For `N = 2R`, `q > 0` and disjoint sets of small and big primes: `phaseSum θ` is the mean over the
small residues `y` of the sum over the skeletons of (common part at `y`) × (expectation of the big
part over the big residues). The residues at the small and at the big primes are independent, and
`IsPhys`, `damping`, `stateMass`, `targetNorm` are products of a small and a big half. -/
def PhaseSkeleton : Prop :=
  ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] (𝒢 : GroupFamily S B)
    (J ℓ : ℕ) (N : Type) [Fintype N] (D : MemData 𝒢 J ℓ N) (R : ℕ) (θ : ℝ),
    D.n = 2 * R → 0 < D.q → Disjoint (smallPrimes 𝒢) (bigPrimes 𝒢) →
    phaseSum 𝒢 D.q D.fam D.k D.ζ R θ =
      ((Fintype.card (ResVec (smallPrimes 𝒢)) : ℝ) : ℂ)⁻¹ *
        ∑ y : ResVec (smallPrimes 𝒢), ∑ sk : Skel D,
          sk.common θ y * ((sk.bigPhys : ℝ) : ℂ)

/-- **(B) The memory path integral by skeletons** [S-02:0516–0534].

"The subscript means that the indicator is inserted in the expanded path integral": a history is
its initial small residues, its skeleton and its decoration; its weight is the Haar mass, the
common part of the skeleton and the memory part `History.memPart`; its births, the memory part
and the memories do not depend on the small residues. Hence `distinctSum Bc θ` is the mean over
the small residues `y` of the sum over the skeletons of (common part at `y`) × (memory sum).
No hypothesis. -/
def DistinctSkeleton : Prop :=
  ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] (𝒢 : GroupFamily S B)
    (J ℓ : ℕ) (N : Type) [Fintype N] (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ),
    distinctSum D Bc θ =
      ((Fintype.card (ResVec (smallPrimes 𝒢)) : ℝ) : ℂ)⁻¹ *
        ∑ y : ResVec (smallPrimes 𝒢), ∑ sk : Skel D,
          sk.common θ y * ((sk.memSum Bc : ℝ) : ℂ)

open _root_.Classical in
/-- **(C1) The big residue expectation is a product over the big primes**
[S-02:0226–0234, 0327–0334].

"The dependence on the initial integer `n` is precisely the nonnegative factor
`∏_{i=0}^N (∏_{p ∈ Λ_i} 1_{n + h_i ≡ 0 (p)}) q_i^{#{p ∉ Λ_i : n + h_i ≡ 0 (p)}}`", with
`q_0 = q_N = √q` and `q_i = q` otherwise; under independent uniform residues its expectation is
the product over the primes of the one-prime expectations.

For `N ≥ 1`, `q > 0`, pairwise disjoint big groups of positive integers and every skeleton:
`bigPhys = (label normalization) · 1_{big lists injective at all visits} · ∏_{p big} onePrimeExp p`.
(For `N = 0` there is no endpoint factor and the statement is false.) -/
def BigResidueProduct : Prop :=
  ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] (𝒢 : GroupFamily S B)
    (J ℓ : ℕ) (N : Type) [Fintype N] (D : MemData 𝒢 J ℓ N) (sk : Skel D),
    1 ≤ D.n → 0 < D.q → (∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g')) →
    (∀ p ∈ bigPrimes 𝒢, 0 < p) →
    sk.bigPhys =
      sk.bigNormAll * (if sk.BigInj then 1 else 0) * ∏ p ∈ bigPrimes 𝒢, sk.onePrimeExp p

/-- **(C2) The exact expansion for one big prime** (eq:prefix-ghost), (eq:orphan-expansion)
[S-02:0327–0373].

"Suppose first that `p` is active at some visits. Incompatible active offsets give zero. Otherwise
… the two exact telescoping identities … If `p` is never active, expand its full product and group
each term of degree at least two by its earliest and latest indices. This gives
`b_p + p⁻¹ ∑_{j<i} η_j η_i 1_{h_j ≡ h_i (p)} ∏_{j<t<i} (1 - η_t 1_{h_t ≡ h_j (p)})`."

For every skeleton and every `p ≥ 1` with `b_p ≠ 0`: `onePrimeExp p = b_p · lifeSum p`. This is
`Graph.primewise_active_lifespan_expectation`, `Graph.primewise_active_expectation_eq_zero` and
`Graph.primewise_orphan_expectation` for the visits `0, …, N`, the colours `-h_i mod p` and the
coefficients `η_i`. -/
def OnePrimeLifespan : Prop :=
  ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] (𝒢 : GroupFamily S B)
    (J ℓ : ℕ) (N : Type) [Fintype N] (D : MemData 𝒢 J ℓ N) (sk : Skel D) (p : ℕ),
    0 < p → lifeBaseline D.q D.n p ≠ 0 →
    sk.onePrimeExp p = lifeBaseline D.q D.n p * sk.lifeSum p

open _root_.Classical in
/-- **(M1) The distinct-birth rule as a running set of born primes** [S-02:0516–0521].

"Impose, in the complete path sum, the rule that all prime values assigned at different births are
distinct. Births comprise initial active slots, fresh active target slots, and ghost births. This
is a global rule, even if two births occur far apart."

The global rule holds if and only if the initial labels are pairwise distinct and the births of
each operation are distinct and differ from all earlier ones. So the memory sum of a skeleton is
`⊗ μ̃_g^{⊗M}(initial big list)` times the recursively defined `Skel.fut N`, started with empty
memories and the set of the initial labels; zero if two initial slots have the same label.
No hypothesis. -/
def BornSetRecursion : Prop :=
  ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] (𝒢 : GroupFamily S B)
    (J ℓ : ℕ) (N : Type) [Fintype N] (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (sk : Skel D),
    sk.memSum Bc =
      if Function.Injective (fun a : B × Slot J ℓ => (sk.xb₀ a.1 a.2 : ℕ)) then
        bigListMass 𝒢 D.q D.n sk.xb₀ *
          sk.fut Bc D.n (fun g => emptyMem 𝒢 Bc g)
            (Finset.univ.image fun a : B × Slot J ℓ => (sk.xb₀ a.1 a.2 : ℕ))
      else 0

/-- **(M2) A visit operation acts prime by prime** (eq:ghost-row) [S-02:0456–0475, 0569–0581].

"Thus selected old zeros terminate, continuing zeros are damped, and a new unordered batch is born
at zero." "A numerical prime occupies at most one active slot or pending particle, because it has
only one birth. Distinct ghost births in an unordered batch are counted once by its factorial
divisor."

For pairwise disjoint big groups, a cutoff `Bc ≥ #{big primes}`, a visit `i ≤ N` and a state in
which every big prime occurs at most once (`MemConsistent`): if `Ψ` is the product of the values
`v` on such states, then the sum over the choices of `G_i` with new births (`Skel.ghostSum`) is the
product of the values `ghostStepVals D i v`. The sum over the subsets of terminated zeros is a
product over the pending zeros; the sum over the ordered batches of distinct new primes, with
`1/b!`, is a product over the unborn primes; the truncations are not active. -/
def GhostStepFactor : Prop :=
  ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] (𝒢 : GroupFamily S B)
    (J ℓ : ℕ) (N : Type) [Fintype N] (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (sk : Skel D),
    (∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g')) → (bigPrimes 𝒢).card ≤ Bc →
    ∀ (i : ℕ), i ≤ D.n → ∀ (Ψ : ((g : B) → Mem 𝒢 Bc g) → Finset ℕ → ℝ) (v : PrimeVals 𝒢),
      (∀ mem U, MemConsistent (sk.lists i).2 mem U → Ψ mem U = v.eval (sk.lists i).2 mem U) →
      ∀ mem U, MemConsistent (sk.lists i).2 mem U →
        sk.ghostSum Bc i Ψ mem U = (ghostStepVals D i v).eval (sk.lists i).2 mem U

/-- **(M3) An edge operation acts prime by prime** [S-02:0477–0514, 0569–0581].

"Its active visits determine exactly when it is shared, stored, promoted, or dropped … Between
these uses it must remain pending. … Immediate promotion of a newly stored particle is impossible.
A numerical prime occupies at most one active slot or pending particle, because it has only one
birth."

For pairwise disjoint big groups, a cutoff `Bc ≥ #{big primes}`, an edge `i` of a skeleton whose
shared big labels are copied, and a state after `G_i` in which every big prime occurs at most
once: if `Ψ` is the product of the values `v` on such states at the visit `i + 1`, then the sum
over the stores and promotions with new fresh births (`Skel.edgeSum`) is the product of the values
`sk.edgeStepVals i v`. A stored slot, a promotion (the index of the unique pending particle with
the label of the target slot) and a fresh birth are choices for one prime each. -/
def EdgeStepFactor : Prop :=
  ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] (𝒢 : GroupFamily S B)
    (J ℓ : ℕ) (N : Type) [Fintype N] (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (sk : Skel D),
    (∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g')) → (bigPrimes 𝒢).card ≤ Bc →
    ∀ (i : Fin D.n), SharedBig (sk.Cset i) (sk.src i).2 (sk.tgt i).2 →
      ∀ (Ψ : ((g : B) → Mem 𝒢 Bc g) → Finset ℕ → ℝ) (v : PrimeVals 𝒢),
      (∀ mem U, MemConsistent (sk.lists (i.val + 1)).2 mem U →
        Ψ mem U = v.eval (sk.lists (i.val + 1)).2 mem U) →
      ∀ mem U, MemConsistent (sk.lists i.val).2 mem U →
        sk.edgeSum Bc i Ψ mem U = (sk.edgeStepVals i v).eval (sk.lists i.val).2 mem U

open _root_.Classical in
/-- **(M4) The transfer chain of a prime sums to its lifespan sum** [S-02:0538–0567].

"The `ρ` factors cancel locally. At an internal visit a continuing pending zero pays
`ρ (q_i/ρ²) ρ = q_i`. A ghost birth pays `(-η_i/ρ) ρ = -η_i`, and a ghost termination pays
`ρ (-η_i/ρ) = -η_i`. … For a prime with `r` active runs, a first active birth costs
`1/(V_g p b_p)` and each of its `r - 1` later promotions costs `1/V_g`. A first ghost birth costs
`1/(p b_p)` and its `r` promotions cost `V_g^{-r}`. Both give `V_g^{-r}/(p b_p)`. An orphan has
`r = 0`. These are precisely the baseline-relative costs in (eq:prefix-ghost),
(eq:orphan-expansion), including all original mark normalizations."

For a skeleton with `BigValid`, under `RawHyp`: the measure of the initial big list times the
product of the values `chain N` at the initial state (zero if two initial slots have the same
label) is `1_{big lists injective at all visits} · (label normalization) · ∏_{p big} lifeSum p`.
The physical compatibility ("if a prime is active at both ends of an edge, then it divides `kD`,
hence `D` … it must be a prescribed shared label; conversely, a prime at an unshared entry or exit
cannot divide `D`", [S-02:0375–0383]) enters here. -/
def ChainLifespan : Prop :=
  ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] (𝒢 : GroupFamily S B)
    (J ℓ : ℕ) (N : Type) [Fintype N] (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (sk : Skel D),
    RawHyp D → sk.BigValid →
    (if Function.Injective (fun a : B × Slot J ℓ => (sk.xb₀ a.1 a.2 : ℕ)) then
        bigListMass 𝒢 D.q D.n sk.xb₀ *
          (sk.chain D.n).eval sk.xb₀ (fun g => emptyMem 𝒢 Bc g)
            (Finset.univ.image fun a : B × Slot J ℓ => (sk.xb₀ a.1 a.2 : ℕ))
      else 0) =
      (if sk.BigInj then 1 else 0) * sk.bigNormAll * ∏ p ∈ bigPrimes 𝒢, sk.lifeSum p

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
