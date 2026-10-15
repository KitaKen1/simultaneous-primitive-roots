module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedReduction
public import SimultaneousPrimitiveRoots.Unconditional.Transference.KernelCosts

/-!
# Objects of the proof of [P] Theorem 6.1 with a joint residue weight

Source: `verification/stage7-sources/P-06.tex`, lines 1–562 and 927–935 (`[P-06:…]`), and
`publication_work_2026-10-09/TeX/simultaneous-primitive-roots.tex`, lines 462–501
(`[PUB-tex:…]`). Lines 563–925 of `P-06.tex` prove (cor:SM); here (cor:SM) is the hypothesis
`EndpointEnergy`.

`TwoSidedReduction d H 𝔅` (`Supply/TwoSidedReduction.lean`) says that Propositions 6.2 and 6.3,
(cor:SM) and Mertens' estimate imply Theorem 6.1^{𝔅}. This file defines the objects that the
intermediate statements of `TwoSidedProof/Statements.lean` are about.

## The fixed data and the data that vary with `x`

* `FixedData`: `ε`, the dampings `q, q₀ ∈ (0,1)`, the `K` bands `𝔞`, the active-group constants
  `P`, the growth exponent `C` of the second endpoint and the cutoff `Ψ` — everything that
  Theorem 6.1 fixes before the saving `A` (`[P-06:0055–0077]`).
* `Config d D x`: the active groups, the `d` slots and the second endpoint `G` at `x`, with their
  three hypotheses. Every estimate below is uniform in the configuration.

## The bridge to [S]'s prime groups (`[P-06:0099–0106, 0256–0258]`)

* `groupParams P q₀`: [S]'s constants with the exponents `(0.27, 0.36, 0.39, 0.46)`, `q := q₀`,
  `ℓ = 1`; `groupFamily 𝔊`: the small and the big groups; `primeGroupsOf`: admissible active groups
  are prime groups of [S] Definition 3.1 (all fields are fields of `ActiveGroups.Admissible`).
* `halfSplit n`: the two blocks of big groups of Proposition 6.3; `Config.family`: the residual
  pattern family `comparisonFamily` with kernel parameters `Q = L^{q_*}`, `h = L^{-h_*}`,
  `ξ = L^{-x_*}`.

## The edge sums (`[P-06:0262–0299]`)

* `edgeTerm 𝔊 q₀ ν x Ψ 𝔅 F G`: the physical edge sum of one pattern `ν`, with `Ψ(n/(xD))/n`
  inserted, the joint factor `𝔅(n, n')`, the endpoint values `F(n)`, `G(n')` and one extra
  half-damping at each endpoint. `Config.rawEdge`, `Config.comparisonEdge`, `Config.edgeTotal`.
* `dampedMass 𝔊 J q₀ n`: `q₀^{ω(n) - M s} ∏_g V_g^{-M} #{physical lists at n}`, the measure of the
  two endpoint norms.

## The stripped comparison correlations (`[P-06:0318–0339]`, (cor:stripped))

* `markCount 𝔊 C`: `t_g = 1` on small groups, `|C_g| + 1` on big groups; `markProd`: the product of
  the marks in the freed slots of one block (`X_A`, `X_B`); `strippedKernel`; `strippedSumOf`,
  `Config.strippedSum`.

## Comparison correlations with bounded tests (`[P-06:0381–0421]`)

* `BlockTest`, `MarkTest`, `CutoffAt`: the hypotheses on the tests `b_i`, `𝐛` and on the cutoffs.
* `comparisonCorrelationOf`, `Config.comparisonCorrelation`; `secondEndpoint` (`𝒱`);
  `bilinearSum` ((cor:comparison-sum)); `multiplier` (`𝔪(θ)`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference
open scoped ContDiff

noncomputable section

/-! ### The active groups as prime groups of [S] Definition 3.1 -/

/-- **[S]'s constants for [P] §6** (`[P-06:0101–0106, 0256–0258]`): "We use these two imported
propositions with `ℓ = k = 1` and the exponents in (cor:groups)", i.e.
`(a, b, c, d₀) = (0.27, 0.36, 0.39, 0.46)`; [S]'s parameter `q` is `q₀` (`[P-06:0186]`). -/
def groupParams (P : ActiveGroupConstants) (q₀ : ℝ) (h₀ : 0 < q₀) (h₁ : q₀ < 1) : GroupParams where
  a := 0.27
  b := 0.36
  c := 0.39
  d := 0.46
  c₀ := P.c₀
  C₀ := P.C₀
  vMinus := P.vlo
  vPlus := P.vhi
  q := q₀
  ℓ := 1
  a_pos := by norm_num
  a_lt_b := by norm_num
  b_lt_c := by norm_num
  c_lt_d := by norm_num
  d_lt := by norm_num
  c₀_pos := P.c₀_pos
  C₀_pos := P.C₀_pos
  vMinus_pos := P.vlo_pos
  vPlus_pos := P.vhi_pos
  q_pos := h₀
  q_lt_one := h₁
  ℓ_pos := Nat.one_pos

/-- The small groups (`𝒮 = Fin numSmall`) and the big groups (`ℬ = Fin numBig`) of a system of
active groups, as a `GroupFamily` of [S]. -/
def groupFamily (𝔊 : ActiveGroups) : GroupFamily (Fin 𝔊.numSmall) (Fin 𝔊.numBig) where
  small := fun i => 𝔊.group (Sum.inl i)
  big := fun j => 𝔊.group (Sum.inr j)

/-- **Admissible active groups are prime groups of [S] Definition 3.1** with the constants
`groupParams P q₀`: each field is a field of `ActiveGroups.Admissible` (`[P-06:0010–0023]` against
`[S-02:0020–0049]`). -/
def primeGroupsOf {P : ActiveGroupConstants} {x : ℝ} {𝔊 : ActiveGroups} (h : 𝔊.Admissible P x)
    (q₀ : ℝ) (h₀ : 0 < q₀) (h₁ : q₀ < 1) :
    PrimeGroups (groupParams P q₀ h₀ h₁) x (Fin 𝔊.numSmall) (Fin 𝔊.numBig) where
  toGroupFamily := groupFamily 𝔊
  prime_small := fun g p hp => h.prime (Sum.inl g) p hp
  prime_big := fun g p hp => h.prime (Sum.inr g) p hp
  disjoint_small := fun g g' hgg' =>
    h.disjoint (Sum.inl g) (Sum.inl g') fun e => hgg' (Sum.inl.inj e)
  disjoint_big := fun g g' hgg' =>
    h.disjoint (Sum.inr g) (Sum.inr g') fun e => hgg' (Sum.inr.inj e)
  disjoint_small_big := fun g g' => h.disjoint (Sum.inl g) (Sum.inr g') Sum.inl_ne_inr
  card_small_ge := by
    rw [Fintype.card_fin]
    exact h.numSmall_ge
  card_small_le := by
    rw [Fintype.card_fin]
    exact h.numSmall_le
  card_big_ge := by
    rw [Fintype.card_fin]
    exact h.numBig_ge
  card_big_le := by
    rw [Fintype.card_fin]
    exact h.numBig_le
  small_ge := fun g p hp => (h.small_range g p hp).1
  small_le := fun g p hp => (h.small_range g p hp).2
  big_ge := fun g p hp => (h.big_range g p hp).1
  big_le := fun g p hp => (h.big_range g p hp).2
  mass_small_ge := fun g => h.mass_ge (Sum.inl g)
  mass_small_le := fun g => h.mass_le (Sum.inl g)
  mass_big_ge := fun g => h.mass_ge (Sum.inr g)
  mass_big_le := fun g => h.mass_le (Sum.inr g)

/-- The split of `n` big groups into the blocks `{i : 2i < n}` and `{i : 2i ≥ n}`, of sizes
`⌈n/2⌉` and `⌊n/2⌋`: "Split the big groups into two blocks" (`[P-06:0211]`; [S]'s proof takes
blocks whose sizes differ by at most one, `[S-03:0442–0443]`). -/
def halfSplit (n : ℕ) : Fin n → Bool := fun i => decide (2 * (i : ℕ) < n)

/-! ### The fixed data and a configuration at `x` -/

/-- **The fixed data of Theorem 6.1** (`[P-06:0055–0077]`): `ε`, the dampings `q` (of `𝒲`) and
`q₀` (of the active marks, `[P-06:0007–0008]`), the `K` inert bands, the constants
`c₀, C₀, v₋, v₊` of (cor:groups), the exponent `C` of `|G(n)| ≤ L^C τ(n_*)^C`, and the "fixed
smooth compactly supported `Ψ : (0,∞) → ℂ`". The number of slots `d`, the modulus `H` and the
weight `𝔅` are parameters of the statements. -/
structure FixedData where
  /-- the margin of the slot intervals -/
  ε : ℝ
  /-- the damping of the fixed-band weight `𝒲` -/
  q : ℝ
  /-- the damping of the active marks -/
  q₀ : ℝ
  /-- the number of inert bands -/
  K : ℕ
  /-- the inert bands -/
  𝔞 : MarkingArray K
  /-- the constants `c₀, C₀, v₋, v₊` of the active groups -/
  P : ActiveGroupConstants
  /-- the exponent of the growth of the second endpoint -/
  C : ℝ
  /-- the cutoff -/
  Ψ : ℝ → ℂ
  ε_pos : 0 < ε
  q_pos : 0 < q
  q_lt_one : q < 1
  q₀_pos : 0 < q₀
  q₀_lt_one : q₀ < 1
  smooth : ContDiff ℝ ∞ Ψ
  compact : HasCompactSupport Ψ
  support : tsupport Ψ ⊆ Set.Ioi 0

/-- [S]'s constants for the fixed data. -/
abbrev FixedData.params (D : FixedData) : GroupParams :=
  groupParams D.P D.q₀ D.q₀_pos D.q₀_lt_one

/-- **The data that vary with `x`** in Theorem 6.1: admissible active groups, admissible slots
and a second endpoint with `G(n) = G(n_*)`, `|G(n)| ≤ L^C τ(n_*)^C` (`[P-06:0066–0067]`). "The
estimate is uniform over the active groups and slot intervals satisfying the stated bounds"
(`[P-06:0073–0076]`), and in `G`. -/
structure Config (d : ℕ) (D : FixedData) (x : ℝ) where
  /-- the active groups -/
  𝔊 : ActiveGroups
  /-- the slots -/
  S : Fin d → Finset ℕ
  /-- the second endpoint -/
  G : ℕ → ℂ
  groups : 𝔊.Admissible D.P x
  slots : SlotsAdmissible D.ε x S
  core : CoreAdmissible 𝔊 x D.C G

namespace Config

variable {d : ℕ} {D : FixedData} {x : ℝ}

/-- The active groups of a configuration as prime groups of [S]. -/
abbrev primeGroups (I : Config d D x) :
    PrimeGroups D.params x (Fin I.𝔊.numSmall) (Fin I.𝔊.numBig) :=
  primeGroupsOf I.groups D.q₀ D.q₀_pos D.q₀_lt_one

/-- The two blocks of big groups. -/
abbrev blocks (I : Config d D x) : Fin I.𝔊.numBig → Bool := halfSplit I.𝔊.numBig

/-- **The residual pattern family of Proposition 6.3** for a configuration (`[P-06:0198–0227]`):
the raw pattern and the signed comparison patterns, with `J` first slots, at most `m₀` probes per
big group and kernel parameters `Q = L^{q_*}`, `h = L^{-h_*}`, `ξ = L^{-x_*}`. It is written
exactly as in `Transference.IdealFamilyBound`. -/
abbrev family (I : Config d D x) (J m₀ : ℕ) (qs hs xs : ℝ) :
    ComparisonIndex (Fin I.𝔊.numBig) I.blocks J m₀ → Pattern I.primeGroups.big J D.params.ℓ :=
  comparisonFamily I.primeGroups.big J D.params.ℓ m₀ I.blocks
    (Real.log x ^ qs) (Real.log x ^ (-hs)) (Real.log x ^ (-xs))

end Config

/-! ### The edge sums -/

/-- The target position `n' = n + D` of an edge with source position `n`, source lists `s` and
auxiliary free labels `r`; `D = D_R D_C` is the dilation (`[P-06:0113–0118, 0124–0126]`, `k = 1`).
-/
def edgeTarget {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    {𝒢 : GroupFamily S B} {J ℓ : ℕ} (C : B → Finset (Fin J)) (n : ℤ) (s : Lists 𝒢 J ℓ)
    (r : AuxList 𝒢.big C) : ℤ :=
  n + (dil C s r : ℤ)

/-- **The physical edge sum of one pattern `ν`** (`[P-06:0262–0266, 0287–0288]`): the sum over the
source positions `n`, the source lists `s`, the auxiliary free labels `r` and the target lists
`s'` of

`Ψ(n/(xD))/n · 𝔅(n, n') · F(n) G(n') · ∏_g V_g^{-M} · q₀^{(ω(n)-Ms)/2} q₀^{(ω(n')-Ms)/2} ·
  (row coefficient of ν at ζ = 0)`,

`n' = n + D`. "Use endpoint vectors with values `F_x(n)` and `G(n')`, respectively, and with one
extra half-damping factor at each endpoint" and "Insert `Ψ(n/(xD))/n` into the physical edge
pairing". The row coefficient is `Transference.physCoef` with `k = 1` and `ζ = 0`: it carries the
physical-state conditions, the shared labels, the ban on the free labels, the law of `r`, the
target normalization `∏_g V_g^{-t_g}`, the other two half-dampings and `K_ν`. The state mass
`∏_g V_g^{-M}` comes from the inner product of the physical space.

For `x > 0` and `Ψ` vanishing near `0` and near `∞` this is a finite sum over `n ≥ 1`. The values
`F : ℕ → ℝ`, `G : ℕ → ℂ` are read at `n.toNat`, `n'.toNat`. -/
def edgeTerm (𝔊 : ActiveGroups) (q₀ : ℝ) {J : ℕ} (ν : Pattern (groupFamily 𝔊).big J 1) (x : ℝ)
    (Ψ : ℝ → ℂ) {H : ℕ} (𝔅 : JointResidueWeight H) (F : ℕ → ℝ) (G : ℕ → ℂ) : ℂ :=
  ∑ᶠ n : ℤ, ∑ s : Lists (groupFamily 𝔊) J 1, ∑ r : AuxList (groupFamily 𝔊).big ν.C,
    ∑ s' : Lists (groupFamily 𝔊) J 1,
      Ψ ((n : ℝ) / (x * (dil ν.C s r : ℝ))) / (n : ℂ) *
        ((𝔅.toFun (n : ZMod H) (edgeTarget ν.C n s r : ZMod H) : ℝ) : ℂ) *
        ((F n.toNat : ℝ) : ℂ) * G (edgeTarget ν.C n s r).toNat *
        ((stateMass (groupFamily 𝔊) J 1 *
            (damping intPos (groupFamily 𝔊) J 1 q₀ n *
              damping intPos (groupFamily 𝔊) J 1 q₀ (edgeTarget ν.C n s r)) : ℝ) : ℂ) *
        physCoef intPos (groupFamily 𝔊) q₀ ν 1 0 n s r s'

/-- **The damped physical mass at the position `n`**:
`q₀^{ω(n) - M s} · ∏_g V_g^{-M} · #{physical lists at n}` (`M = J + 1`). The squared norm of an
endpoint vector with values `a(n) q₀^{(ω(n) - Ms)/2}` on a set of positions is
`∑_n |a(n)|² dampedMass(n)` (`[P-06:0262–0285]`). -/
def dampedMass (𝔊 : ActiveGroups) (J : ℕ) (q₀ : ℝ) (n : ℤ) : ℝ :=
  damping intPos (groupFamily 𝔊) J 1 q₀ n ^ 2 * unitNormSq intPos (groupFamily 𝔊) J 1 n

/-- The integers of the enlarged dyad `[X, 4X)`: "Partition `n` into `O(L)` dyads `[X, 2X)`,
restricting `n'` to fixed enlargements" (`[P-06:0288–0289]`). -/
def wideWindow (X : ℝ) : Finset ℤ := Finset.Ico ⌈X⌉ ⌈4 * X⌉

/-! ### The stripped correlations -/

/-- `t_g`: `1` on a small group and `|C_g| + 1` on a big group (`[P-06:0108–0111]` with
`ℓ = 1`). -/
def markCount (𝔊 : ActiveGroups) {J : ℕ} (C : Fin 𝔊.numBig → Finset (Fin J)) : 𝔊.Index → ℕ :=
  Sum.elim (fun _ => 1) (fun j => (C j).card + 1)

/-- The product of the marks of a represented list in the freed slots of the big groups of the
block `b`: with the target list and `b = true` this is `X_A`, with the source list and `b = false`
it is `X_B` (`[P-06:0216–0218]`). The `|C_g|` freed slots of the big group `g` are the first
`|C_g|` of the `t_g = |C_g| + 1` positions of a represented list, the last position being the
final slot ("No shared or final `ℓ` label enters these kernels"). -/
def markProd (𝔊 : ActiveGroups) {J : ℕ} (C : Fin 𝔊.numBig → Finset (Fin J))
    (blk : Fin 𝔊.numBig → Bool) (b : Bool)
    (𝔭 : (g : 𝔊.Index) → Fin (markCount 𝔊 C g) → ℕ) : ℕ :=
  ∏ j : Fin 𝔊.numBig,
    if blk j = b then ∏ i : Fin (C j).card, 𝔭 (Sum.inr j) (Fin.castSucc i) else 1

/-- The scalar factor `q₀^{ω_P(n) - ∑_g t_g} ∏_g V_g^{-t_g}` of the active marked weight
(cor:marked-weight): `ActiveGroups.activeWeight` is this factor times the sum of the test over the
represented lists. -/
def activeCoeff (𝔊 : ActiveGroups) (q₀ : ℝ) (t : 𝔊.Index → ℕ) (n : ℕ) : ℝ :=
  q₀ ^ (𝔊.totalHits n - ∑ g : 𝔊.Index, t g) *
    ∏ g : 𝔊.Index, (reciprocalMass (𝔊.group g) ^ t g)⁻¹

/-- **The comparison coefficient (cor:comparison-kernel) on stripped lists**
(`[P-06:0211–0218]`): `-(-1)^{|A|+|B|} 𝒦_A(D_A, X_A) 𝒦_B(D_B, X_B)` with `D_A, D_B` the products
of the free labels `r` of the two blocks, `X_A` the product of the *target* marks `𝔭'` in the
freed slots of the first block and `X_B` the product of the *source* marks `𝔭` in the freed slots
of the second block. It is `Transference.comparisonPattern` read on the unshared labels. -/
def strippedKernel (𝔊 : ActiveGroups) {J : ℕ} (C : Fin 𝔊.numBig → Finset (Fin J))
    (blk : Fin 𝔊.numBig → Bool) (Q h ξ : ℝ) (r : AuxList (groupFamily 𝔊).big C)
    (𝔭 𝔭' : (g : 𝔊.Index) → Fin (markCount 𝔊 C g) → ℕ) : ℂ :=
  -((-1 : ℂ) ^ (∑ g, (C g).card)) *
    (cellKernel (groupFamily 𝔊).big (restrictBlock blk true C) Q h ξ
        (blockAuxProd blk true C r) (markProd 𝔊 C blk true 𝔭') *
      cellKernel (groupFamily 𝔊).big (restrictBlock blk false C) Q h ξ
        (blockAuxProd blk false C r) (markProd 𝔊 C blk false 𝔭))

/-- **The stripped expression (cor:stripped) of the comparison freeing `C`**
(`[P-06:0330–0339]`):

`E_{D_C} ∑_{w ≥ 1} Ψ(w/(x D_C))/w · 𝔅(w, w + D_C) F_x(w) G(w + D_C) W_𝐭(w) W_𝐭(w + D_C)
   E_{𝐩(w), 𝐩(w + D_C)} K_ν`,

"where the last expectation is uniform on each endpoint's ordered unshared lists". Here it is
written without the two normalizations by the number of lists: the law of the free labels `r`
(`auxWeight`, `D_C = tupleProd C r`), the two scalar factors `activeCoeff`, and the double sum of
the coefficient over the represented lists at `w` and at `w + D_C`. -/
def strippedSumOf (𝔊 : ActiveGroups) (q q₀ : ℝ) {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) {d : ℕ}
    (S : Fin d → Finset ℕ) {H : ℕ} (𝔅 : JointResidueWeight H) (Ψ : ℝ → ℂ) (G : ℕ → ℂ) {J : ℕ}
    (C : Fin 𝔊.numBig → Finset (Fin J)) (blk : Fin 𝔊.numBig → Bool) (Q h ξ : ℝ) : ℂ :=
  ∑ r : AuxList (groupFamily 𝔊).big C, ((auxWeight (groupFamily 𝔊).big C r : ℝ) : ℂ) *
    ∑ᶠ w : ℕ, Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) / (w : ℂ) *
      ((𝔅.toFun (w : ZMod H) ((w + tupleProd C r : ℕ) : ZMod H) : ℝ) : ℂ) *
      ((centeredCore q 𝔞 x S w : ℝ) : ℂ) * G (w + tupleProd C r) *
      ((activeCoeff 𝔊 q₀ (markCount 𝔊 C) w *
          activeCoeff 𝔊 q₀ (markCount 𝔊 C) (w + tupleProd C r) : ℝ) : ℂ) *
      ∑ 𝔭 ∈ 𝔊.representedLists (markCount 𝔊 C) w,
        ∑ 𝔭' ∈ 𝔊.representedLists (markCount 𝔊 C) (w + tupleProd C r),
          strippedKernel 𝔊 C blk Q h ξ r 𝔭 𝔭'

/-! ### Tests and cutoffs -/

/-- **A bounded test on the free labels of the block `b`, supported on one log cell**
(`[P-06:0381–0384, 0390–0391, 0396–0402]`): `|β| ≤ 1`; `β` depends only on the labels of the big
groups of the block `b` ("separate bounded tests on the two free tuples"; "Tuple tests may be used
in place of product tests"); and the free product of the block lies in `[U, eU]` where `β ≠ 0`
("the two nonempty free products … lie in log cells of width at most one, say `D_A ≍ U_1`,
`D_B ≍ U_2`"). -/
structure BlockTest {B : Type} [Fintype B] [DecidableEq B] {J : ℕ} {big : B → Finset ℕ}
    (blk : B → Bool) (b : Bool) (C : B → Finset (Fin J)) (β : AuxList big C → ℂ) (U : ℝ) :
    Prop where
  /-- `|β| ≤ 1` -/
  bound : ∀ r, ‖β r‖ ≤ 1
  /-- `β` depends only on the free labels of the block -/
  depends : ∀ r r' : AuxList big C, (∀ g, blk g = b → r g = r' g) → β r = β r'
  /-- the free product of the block lies in the log cell `[U, eU]` on the support of `β` -/
  cell : ∀ r, β r ≠ 0 →
    U ≤ (blockAuxProd blk b C r : ℝ) ∧ (blockAuxProd blk b C r : ℝ) ≤ Real.exp 1 * U

/-- **A list test of modulus at most one depending only on big-group marks**
(`[P-06:0403–0405]`: "`W_𝐭^𝐛`, with `|𝐛| ≤ 1` depending only on big marks"); the two conditions
on the test in `EndpointEnergyAt`. -/
def MarkTest (𝔊 : ActiveGroups) {t : 𝔊.Index → ℕ}
    (test : ((g : 𝔊.Index) → Fin (t g) → ℕ) → ℂ) : Prop :=
  (∀ 𝔭, ‖test 𝔭‖ ≤ 1) ∧
    ∀ 𝔭 𝔭' : (g : 𝔊.Index) → Fin (t g) → ℕ,
      (∀ j : Fin 𝔊.numBig, 𝔭 (Sum.inr j) = 𝔭' (Sum.inr j)) → test 𝔭 = test 𝔭'

/-- **A smooth cutoff at a scale** (`[P-06:0391–0392, 0641–0642]`): smooth, supported in the fixed
compact set `[a₁, a₂] ⊂ (0, ∞)`, with the derivative of order `j` bounded by `L^{Dψ j}`; the three
conditions on `ψ_1` in `EndpointEnergyAt`. -/
def CutoffAt (a₁ a₂ : ℝ) (Dψ : ℕ → ℝ) (x : ℝ) (ψ : ℝ → ℂ) : Prop :=
  ContDiff ℝ ∞ ψ ∧ Function.support ψ ⊆ Set.Icc a₁ a₂ ∧
    ∀ (j : ℕ) (u : ℝ), ‖iteratedDeriv j ψ u‖ ≤ Real.log x ^ Dψ j

/-! ### Comparison correlations with tests -/

/-- **A comparison correlation with separated tests** (`[P-06:0390–0400]`, before the cutoffs and
the Fourier inversion): for a test `b` on the free labels and tests `𝐛₁, 𝐛₂` on the represented
lists of the two endpoints,

`E_r b(r) ∑_{w ≥ 1} Ψ(w/(x D_C))/w · 𝔅(w, w + D_C) · F_x(w) W_𝐭^{𝐛₁}(w) ·
   G(w + D_C) W_𝐭^{𝐛₂}(w + D_C)`, `D_C = tupleProd C r`.

"The cell and character expansion factors into separate bounded tests on the two free tuples and
on each endpoint's big marks." -/
def comparisonCorrelationOf (𝔊 : ActiveGroups) (q q₀ : ℝ) {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ)
    {d : ℕ} (S : Fin d → Finset ℕ) {H : ℕ} (𝔅 : JointResidueWeight H) (Ψ : ℝ → ℂ) (G : ℕ → ℂ)
    {J : ℕ} (C : Fin 𝔊.numBig → Finset (Fin J)) (b : AuxList (groupFamily 𝔊).big C → ℂ)
    (test₁ test₂ : ((g : 𝔊.Index) → Fin (markCount 𝔊 C g) → ℕ) → ℂ) : ℂ :=
  ∑ r : AuxList (groupFamily 𝔊).big C, ((auxWeight (groupFamily 𝔊).big C r : ℝ) : ℂ) * b r *
    ∑ᶠ w : ℕ, Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) / (w : ℂ) *
      ((𝔅.toFun (w : ZMod H) ((w + tupleProd C r : ℕ) : ZMod H) : ℝ) : ℂ) *
      (((centeredCore q 𝔞 x S w : ℝ) : ℂ) * 𝔊.activeWeight q₀ (markCount 𝔊 C) test₁ w) *
      (G (w + tupleProd C r) * 𝔊.activeWeight q₀ (markCount 𝔊 C) test₂ (w + tupleProd C r))

/-- **The second endpoint of a comparison correlation** (`[P-06:0402–0405]`):
`𝒱(v) = ψ_2(v/Y) G(v) W_𝐭^𝐛(v)`, "a smooth cutoff at `Y`" times the "invariant core times
`W_𝐭^𝐛`". -/
def secondEndpoint (q₀ : ℝ) (𝔊 : ActiveGroups) (t : 𝔊.Index → ℕ)
    (test : ((g : 𝔊.Index) → Fin (t g) → ℕ) → ℂ) (G : ℕ → ℂ) (ψ₂ : ℝ → ℂ) (Y : ℝ) (v : ℕ) : ℂ :=
  ψ₂ ((v : ℝ) / Y) * G v * 𝔊.activeWeight q₀ t test v

/-- **(cor:comparison-sum)** (`[P-06:0396–0400]`):
`E b(D) ∑_w 𝒰(w) 𝒱(w + D_A D_B)`, the expectation over the free labels `r` with their law. -/
def bilinearSum {B : Type} [Fintype B] [DecidableEq B] {J : ℕ} (big : B → Finset ℕ)
    (C : B → Finset (Fin J)) (b : AuxList big C → ℂ) (U V : ℕ → ℂ) : ℂ :=
  ∑ r : AuxList big C, ((auxWeight big C r : ℝ) : ℂ) * b r *
    ∑ᶠ w : ℕ, U w * V (w + tupleProd C r)

/-- **The additive multiplier** `𝔪(θ) = E b(D) e(θ D_A D_B)` of (cor:comparison-sum)
(`[P-06:0417–0422]`). -/
def multiplier {B : Type} [Fintype B] [DecidableEq B] {J : ℕ} (big : B → Finset ℕ)
    (C : B → Finset (Fin J)) (b : AuxList big C → ℂ) (θ : ℝ) : ℂ :=
  ∑ r : AuxList big C, ((auxWeight big C r : ℝ) : ℂ) * b r *
    addChar (θ * (tupleProd C r : ℝ))

/-! ### The sums of a configuration -/

namespace Config

variable {d : ℕ} {D : FixedData} {x : ℝ}

/-- The edge sum of the raw pattern (`C_g = ∅`, `K_0 = 1`) with the centered first endpoint
`F_x` and the joint factor `𝔅`. -/
def rawEdge (I : Config d D x) {H : ℕ} (𝔅 : JointResidueWeight H) (J : ℕ) : ℂ :=
  edgeTerm I.𝔊 D.q₀ (Pattern.raw (groupFamily I.𝔊).big J 1) x D.Ψ 𝔅
    (centeredCore D.q D.𝔞 x I.S) I.G

/-- The edge sum of the comparison pattern freeing `C`. -/
def comparisonEdge (I : Config d D x) {H : ℕ} (𝔅 : JointResidueWeight H) {J : ℕ} (qs hs xs : ℝ)
    (C : Fin I.𝔊.numBig → Finset (Fin J)) : ℂ :=
  edgeTerm I.𝔊 D.q₀
    (comparisonPattern (groupFamily I.𝔊).big J 1 I.blocks
      (Real.log x ^ qs) (Real.log x ^ (-hs)) (Real.log x ^ (-xs)) C) x D.Ψ 𝔅
    (centeredCore D.q D.𝔞 x I.S) I.G

/-- **The total residual edge pairing** (`[P-06:0287–0316]`): the edge sums of all patterns of the
residual family, the raw pattern and every comparison. -/
def edgeTotal (I : Config d D x) {H : ℕ} (𝔅 : JointResidueWeight H) (J m₀ : ℕ) (qs hs xs : ℝ) :
    ℂ :=
  I.rawEdge 𝔅 J +
    ∑ C : {C : Fin I.𝔊.numBig → Finset (Fin J) // IsComparison I.blocks m₀ C},
      I.comparisonEdge 𝔅 qs hs xs C.1

/-- The stripped expression (cor:stripped) of the comparison freeing `C`. -/
def strippedSum (I : Config d D x) {H : ℕ} (𝔅 : JointResidueWeight H) {J : ℕ} (qs hs xs : ℝ)
    (C : Fin I.𝔊.numBig → Finset (Fin J)) : ℂ :=
  strippedSumOf I.𝔊 D.q D.q₀ D.𝔞 x I.S 𝔅 D.Ψ I.G C I.blocks
    (Real.log x ^ qs) (Real.log x ^ (-hs)) (Real.log x ^ (-xs))

/-- A comparison correlation with separated tests. -/
def comparisonCorrelation (I : Config d D x) {H : ℕ} (𝔅 : JointResidueWeight H) {J : ℕ}
    (C : Fin I.𝔊.numBig → Finset (Fin J)) (b : AuxList (groupFamily I.𝔊).big C → ℂ)
    (test₁ test₂ : ((g : I.𝔊.Index) → Fin (markCount I.𝔊 C g) → ℕ) → ℂ) : ℂ :=
  comparisonCorrelationOf I.𝔊 D.q D.q₀ D.𝔞 x I.S 𝔅 D.Ψ I.G C b test₁ test₂

end Config

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
