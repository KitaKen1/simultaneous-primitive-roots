module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.History
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResidueModel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The intermediate results of the proof of [S] Theorem 3.5, memory part

Source: `verification/stage7-sources/S-02.tex`, lines 516–1258 (`[S-02:0516–1258]`).

Every statement is a `def … : Prop`. As in `Transference/Statements.lean`, the body after the
constants is a separate definition whose name ends in `Bound` or `At`, so that the order of the
constants can be read from the last definition of each block. Throughout `L = log x`,
`T = log L`, `N = Graph.sourceMemoryLength L = 2⌈L^{0.52}⌉`, `B = memCutoff L = ⌈L²⌉`,
`P_* = Graph.sourcePrimeLowerBound c L = exp(L^c)`, `ρ = memRho P`, `v = memV P`.

| statement | paper | constants, in the order in which they are chosen |
|---|---|---|
| `MemoryIdentity` | Lemma 3.7 [S-02:0523–0535] | `P, m, C₁, J, C₂ ⟶ x₀` |
| `GhostAbsolute` | (eq:ghost-absolute-bound) [S-02:0681–0702] | `P ⟶ C_v ⟶ J ⟶ x₀` |
| `MemoryAbsolute` | Lemma 3.8 [S-02:0758–0765] | `P, m, C₁ ⟶ C_a ⟶ J, C₂ ⟶ x₀` |
| `BoundaryNorm` | [S-02:0812–0819] | `P, J ⟶ x₀` |
| `MemoryTail` | (eq:memory-tail) [S-02:0797–0811] | `P, m, C₁, J, C₂, A ⟶ x₀` |
| `RareTransfer` | Lemma 3.9 [S-02:0838–0845] | `P, m, C₁ ⟶ C_d ⟶ J, C₂ ⟶ x₀` |
| `CleanNorm` | Lemma 3.10 [S-02:0898–0909] | `P ⟶ C_s ⟶ E_id, m, C₁, J, C₂ ⟶ x₀` |
| `EdgeContractionBound` | (eq:whole-edge-contraction) [S-02:1032–1037] | `P, G, E_id, m, C₁, J, C₂ ⟶ x₀` |
| `BirthAddressCount` | (eq:birth-address-count) [S-02:1063–1068] | `P, J ⟶ x₀` |
| `HighRank` | (eq:high-rank-path-bound) [S-02:1107–1155] | `P, m, C₁, J, C₂ ⟶ C_h, C ⟶ x₀` |
| `LowRankStep` | (eq:low-rank-path-bound) [S-02:1172–1225] | none (exact) |
| `DistinctBirthBound` | [S-02:1237–1245] | `P, E ⟶ E_id ⟶ m, C₁ ⟶ J₀ ⟶ J ≥ J₀ ⟶ C₂ ⟶ x₀` |

The statements of `History.lean` (`DistinctIndicatorExpansion`, `RankCoefficientCount`,
`HistoryExpansion`), of `Operators.lean` (`GhostRowCompat`) and of `ResidueModel.lean`
(`UniformResidueReplacement`, `ResidueSummation`, `ResidueReduction`, `ReturnFourier`) complete the
list. `Assembly.lean` proves `LocalTransference` from them.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### The memory model of the prime groups of Definition 3.1 -/

section Data

variable {P : GroupParams} {x : ℝ} {S B : Type} [Fintype S] [Fintype B] [DecidableEq S]
  [DecidableEq B]

/-- **The parameters of the memory operators for the prime groups of Definition 3.1**: `q` of
Definition 3.1, `ρ = memRho P`, `N = Graph.sourceMemoryLength L` edges, and the pattern family,
`k`, `ζ` of Definition 3.3. -/
def memData (𝔊 : PrimeGroups P x S B) {J : ℕ} {N : Type} (𝔉 : N → Pattern 𝔊.big J P.ℓ) (k : ℤ)
    (ζ : ℝ) : MemData 𝔊.toGroupFamily J P.ℓ N where
  q := P.q
  ρ := memRho P
  n := Graph.sourceMemoryLength (Real.log x)
  fam := 𝔉
  k := k
  ζ := ζ

/-- **The measure of `ℋ` for the prime groups of Definition 3.1** (eq:memory-hilbert-space). -/
def memMeasure (𝔊 : PrimeGroups P x S B) (J Bc : ℕ) : MState 𝔊.toGroupFamily J P.ℓ Bc → ℝ :=
  memWeight 𝔊.toGroupFamily P.q (Graph.sourceMemoryLength (Real.log x))

/-- **An operator bound on `ℋ`**: `‖T F‖ ≤ C ‖F‖` for every function `F` which is symmetric in the
particle indices of the memories. -/
def MemOpBound (𝔊 : PrimeGroups P x S B) {J Bc : ℕ}
    (T : (MState 𝔊.toGroupFamily J P.ℓ Bc → ℂ) →ₗ[ℂ] (MState 𝔊.toGroupFamily J P.ℓ Bc → ℂ))
    (C : ℝ) : Prop :=
  OpBound (memMeasure 𝔊 J Bc) (fun F => MemSymmetric F) T C

end Data

/-! ### Lemma 3.7: the exact memory identity -/

/-- **The memory identity for fixed constants**: for all sufficiently large `x`, every system of
prime groups, every admissible pattern family and `k`, every `ζ`, every real `θ`, and every
cutoff `Bc` which is at least the number of big primes:
`phaseSum θ = (∏_{p big} b_p) · distinctSum Bc θ`. -/
def MemoryIdentityBound (P : GroupParams) (m : ℕ) (C₁ : ℝ) (J : ℕ) (C₂ : ℝ) : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B) (N : Type) [Fintype N] (𝔉 : N → Pattern 𝔊.big J P.ℓ)
      (ζ : ℝ) (k : ℤ), Admissible (Real.log x) m C₁ C₂ 𝔉 k →
      ∀ (θ : ℝ) (Bc : ℕ), (bigPrimes 𝔊.toGroupFamily).card ≤ Bc →
        phaseSum 𝔊.toGroupFamily P.q 𝔉 k ζ (transferR (Real.log x)) θ =
          ((baselineProd (bigPrimes 𝔊.toGroupFamily) P.q
              (Graph.sourceMemoryLength (Real.log x)) : ℝ) : ℂ) *
            distinctSum (memData 𝔊 𝔉 k ζ) Bc θ

/-- **[S] Lemma 3.7 (exact memory identity, `lem:memory-identity`)** [S-02:0523–0535].

"With the distinct-birth rule, the independent-residue path expression with the phase in
(eq:return-fourier) equals
`(∏_{p big} b_p) ⟨𝟏_∅, G_0 ℰ_0 G_1 ⋯ ℰ_{N-1} G_N 𝟏_∅⟩_distinct`.
The subscript means that the indicator is inserted in the expanded path integral, not that each
local operator separately enforces it."

Here the left side is `phaseSum` (built from the reviewed `physOp`, `physAdj`), and the right side
is `distinctSum`, the expanded path integral of `History.lean`.

The identity is stated without memory truncation, as in the paper. With the distinct-birth rule a
big prime is born at most once, and a particle is never duplicated, so the total memory size
never exceeds the number of big primes: for a cutoff `Bc ≥ #{big primes}` the truncation removes
no term, and `distinctSum Bc` is the untruncated expression.

Quantifiers: `P, m, C₁, J, C₂ ⟶ x₀`. The paper's proof uses of the standing hypotheses only
`0 < |k| ≤ L^{C₂}` ("for large `x` every group prime exceeds `|k|`", [S-02:0376]) and
`b_p > 0`; the statement keeps the full hypothesis `Admissible` of Theorem 3.5, which is what the
assembly provides. -/
def MemoryIdentity : Prop :=
  ∀ (P : GroupParams) (m : ℕ) (C₁ : ℝ) (J : ℕ) (C₂ : ℝ), MemoryIdentityBound P m C₁ J C₂

/-! ### Absolute bounds -/

section RowCol

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N]

/-- **The weighted row and column bounds of the absolute visit operations, with doubled ghost
births** (eq:ghost-absolute-bound) [S-02:0697–0702]: `|G_i| w ≤ C w` and `|G_i|* w ≤ C w` for
`w = v^{j_tot}` and every visit `i ≤ N`, where `|G_i|` has the coefficients
`2^{#births} |ghostCoef|` ("all these assertions include the version with doubled ghost
births"). -/
def GhostRowCol (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (v C : ℝ) : Prop :=
  ∀ i : ℕ, i ≤ D.n →
    RowBound (schurWeight v)
        (fun (s : MState 𝒢 J ℓ Bc) (c : GhostChoice 𝒢 Bc) =>
          (2 : ℝ) ^ ghostBirthCount c * |ghostCoef D i s c|) ghostTgt C ∧
      ColBound (memWeight 𝒢 D.q D.n) (schurWeight v) (fun f => MemSymmetric f)
        (fun (s : MState 𝒢 J ℓ Bc) (c : GhostChoice 𝒢 Bc) =>
          (2 : ℝ) ^ ghostBirthCount c * |ghostCoef D i s c|) ghostTgt C

/-- **The weighted row and column bounds of the absolute edges** (Lemma 3.8) [S-02:0758–0762]:
`|ℰ_i| w ≤ C w` and `|ℰ_i|* w ≤ C w` for `w = v^{j_tot}`, every edge `i < N` and every `θ`, where
`|ℰ_i|` has the moduli of the coefficients of all local transition choices (permutations,
pattern, free labels, transfers, target lists). -/
def EdgeRowCol (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (v C : ℝ) : Prop :=
  ∀ (θ : ℝ) (i : ℕ), i < D.n →
    RowBound (schurWeight v)
        (fun (s : MState 𝒢 J ℓ Bc) (ξ : EdgeFullChoice D Bc) =>
          ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖) (edgeFullTgt D i) C ∧
      ColBound (memWeight 𝒢 D.q D.n) (schurWeight v) (fun f => MemSymmetric f)
        (fun (s : MState 𝒢 J ℓ Bc) (ξ : EdgeFullChoice D Bc) =>
          ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖) (edgeFullTgt D i) C

end RowCol

/-- **(eq:ghost-absolute-bound)** [S-02:0681–0702].

"Choose `v` large enough that, for both possible `q_i`,
`q_i/ρ² + 2 max(1, v₊) η_i / (ρ v) < 1`. … Since `ν(𝒫_g) = 1 + o(1)`, the exponential factor in
(eq:ghost-schur-ratios) is bounded by a fixed constant per group. Thus for some fixed `C_v`,
`|G_i| w ≤ L^{C_v} w`, `|G_i|* w ≤ L^{C_v} w`, `‖G_i‖ ≤ L^{C_v}`. The exponent `C_v` is
independent of `m, C₁, J`. All these assertions include the version with doubled ghost births."

Quantifiers: `P ⟶ C_v ⟶ J ⟶ x₀`; the pattern family, `k`, `ζ` and the cutoff are arbitrary (the
visit operations do not depend on them, and the bounds "persist … under memory-size projections",
[S-02:0762–0764]). The weight is `v = memV P`. The third assertion `‖G_i‖ ≤ L^{C_v}`, also with a
multiplier of modulus at most one on the births, follows by Schur's test:
`ghostOpWith_opBound` in `Assembly.lean`.

`Graph/` proves the one-group form: the weighted row and column ratios
(`Graph.finite_ghost_truncated_kernel_weighted_row_le_uniform_exp`, `…_column_…`), the choice of
`v` (`GroupParams.exists_ghost_weight`), `μ̃_g(𝒫_g) ≤ 2`
(`Graph.tilted_prime_group_law_total_le_two`) and the product over `O(T)` groups
(`PrimeGroups.prod_big_le_rpow`). What remains is `GhostRowCompat` and the product over the big
groups with the total truncation. -/
def GhostAbsolute : Prop :=
  ∀ P : GroupParams, ∃ Cv : ℝ, ∀ J : ℕ, ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B) (N : Type) [Fintype N] (𝔉 : N → Pattern 𝔊.big J P.ℓ)
      (ζ : ℝ) (k : ℤ) (Bc : ℕ),
      GhostRowCol (memData 𝔊 𝔉 k ζ) Bc (memV P) (Real.log x ^ Cv)

/-- The conclusion of Lemma 3.8 for fixed constants. -/
def MemoryAbsoluteBound (P : GroupParams) (m : ℕ) (C₁ Ca : ℝ) (J : ℕ) (C₂ : ℝ) : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B) (N : Type) [Fintype N] (𝔉 : N → Pattern 𝔊.big J P.ℓ)
      (ζ : ℝ) (k : ℤ), Admissible (Real.log x) m C₁ C₂ 𝔉 k →
      ∀ Bc : ℕ, EdgeRowCol (memData 𝔊 𝔉 k ζ) Bc (memV P) (Real.log x ^ Ca)

/-- **[S] Lemma 3.8 (absolute memory bounds, `lem:memory-absolute`)** [S-02:0758–0765].

"There is `C_a`, allowed to depend on `m, C₁` but independent of `J`, such that every absolute edge
has weighted row and column bounds `L^{C_a}`. These bounds and (eq:ghost-absolute-bound) persist
under arbitrary multipliers of modulus at most one on individual local transition choices, and
under memory-size projections."

Quantifiers: `P, m, C₁ ⟶ C_a ⟶ J, C₂ ⟶ x₀`. The bounds are for the kernel of the moduli of the
coefficients, for every cutoff `Bc`; a multiplier of modulus at most one only decreases the moduli,
so the persistence under multipliers is the monotonicity of `RowBound` and `ColBound` in the
kernel, and the resulting operator bound is `edgeOpWith_opBound` in `Assembly.lean`.

`Graph/` covers the factorial accounting (eq:edge-factorial-reversal)
(`Graph.edge_factorial_reversal`) and the reversal of the joint measure (eq:edge-joint-memory),
(eq:edge-joint-measure) for one group and one sector (`Graph.residue_edge_joint_reversal`,
`Graph.ordered_anchor_retrieval_joint_sum`). The small groups are the proved Lemma 3.4
(`Schur.sum_norm_physCoef_row_le`, `…_col_le`). -/
def MemoryAbsolute : Prop :=
  ∀ (P : GroupParams) (m : ℕ) (C₁ : ℝ), ∃ Ca : ℝ, ∀ (J : ℕ) (C₂ : ℝ),
    MemoryAbsoluteBound P m C₁ Ca J C₂

/-- **The boundary vector has bounded norm** [S-02:0812–0819]: "the empty-memory boundary vector
has bounded norm: the small part has mass at most one by (eq:initial-factorial-mass), and the big
part has mass `∏_{g ∈ ℬ} μ̃_g(𝒫_g)^M = 1 + O_J(sN/P_*) = 1 + o(1)`."

Stated as `‖𝟏_∅‖² ≤ 2` for `x ≥ x₀(P, J)`, for every cutoff. -/
def BoundaryNorm : Prop :=
  ∀ (P : GroupParams) (J : ℕ), ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B) (Bc : ℕ),
      wNormSq (memMeasure 𝔊 J Bc) (emptyVec 𝔊.toGroupFamily J P.ℓ Bc) ≤ 2

/-! ### Truncation -/

/-- The truncation estimate for fixed constants: for all sufficiently large `x` and every cutoff
`Bc ≥ B = ⌈L²⌉`, the path integrals with the distinct-birth rule at the cutoffs `Bc` and `B`
differ by at most `L^{-AN}`. -/
def MemoryTailBound (P : GroupParams) (m : ℕ) (C₁ : ℝ) (J : ℕ) (C₂ A : ℝ) : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B) (N : Type) [Fintype N] (𝔉 : N → Pattern 𝔊.big J P.ℓ)
      (ζ : ℝ) (k : ℤ), Admissible (Real.log x) m C₁ C₂ 𝔉 k →
      ∀ (θ : ℝ) (Bc : ℕ), memCutoff (Real.log x) ≤ Bc →
        ‖distinctSum (memData 𝔊 𝔉 k ζ) Bc θ -
            distinctSum (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) θ‖ ≤
          Real.log x ^ (-(A * (Graph.sourceMemoryLength (Real.log x) : ℝ)))

/-- **Memory truncation and its tail, (eq:memory-truncation), (eq:memory-tail)**
[S-02:0797–0811].

"We now restrict the total memory size to `B = ⌈L²⌉` before and after every operation … At most
`(ℓ + m)|ℬ|N` particles can be supplied by stores. Thus a path violating this restriction has at
least `B - O((ℓ + m)sN)` ghost births. Multiply every ghost birth by two in the absolute path sum
and use the preceding bounds. The total omitted mass, even with the distinct-birth indicator, is
at most `2^{-B + O((ℓ + m)sN)} L^{O(N)} = exp(-Ω(L²)) = o(L^{-AN})` for every fixed `A`."

The omitted mass is the difference of `distinctSum` at a cutoff `Bc ≥ B` and at `B`: the
histories at the cutoff `B` are the histories at the cutoff `Bc` in which the total memory never
exceeds `B` (with the same weights and births). Quantifiers: `P, m, C₁, J, C₂, A ⟶ x₀`, uniformly
in the cutoff `Bc`.

The inputs are the row bounds of `GhostAbsolute` (with doubled births) and `MemoryAbsolute`, and
`BoundaryNorm`. -/
def MemoryTail : Prop :=
  ∀ (P : GroupParams) (m : ℕ) (C₁ : ℝ) (J : ℕ) (C₂ A : ℝ), MemoryTailBound P m C₁ J C₂ A

/-! ### Rare transfer, clean edges, the whole edge -/

/-- The conclusion of Lemma 3.9 for fixed constants: for all sufficiently large `x` the dirty part
of every edge, at the truncation `B = ⌈L²⌉`, has norm at most `2 L^{C_d} (B/𝒟)^{1/2}` on `ℋ`. -/
def RareTransferBound (P : GroupParams) (m : ℕ) (C₁ Cd : ℝ) (J : ℕ) (C₂ : ℝ) : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B) (N : Type) [Fintype N] (𝔉 : N → Pattern 𝔊.big J P.ℓ)
      (ζ : ℝ) (k : ℤ), Admissible (Real.log x) m C₁ C₂ 𝔉 k →
      ∀ (θ : ℝ) (i : ℕ), i < Graph.sourceMemoryLength (Real.log x) →
        MemOpBound 𝔊 (edgeDirty (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) θ i)
          (2 * Real.log x ^ Cd *
            Real.sqrt ((memCutoff (Real.log x) : ℝ) / (omissionNumber S J P.ℓ : ℝ)))

/-- **[S] Lemma 3.9 (rare transfer, `lem:rare-transfer`)** [S-02:0838–0845].

"With the memory truncation in (eq:memory-truncation), the aggregate of all dirty terms of any
edge has norm at most `2 L^{C_a} (B/𝒟)^{1/2}`, after enlarging `C_a` independently of `J` if
necessary."

Quantifiers: `P, m, C₁ ⟶ C_d ⟶ J, C₂ ⟶ x₀`. The exponent is called `C_d` here; the assembly
takes the maximum of `C_d` and the exponent of Lemma 3.8, which is the paper's "enlarging `C_a`".
The norm is the operator norm on `ℋ` (`MemOpBound`: functions symmetric in the particle indices),
`𝒟 = C(M, ℓ)^{|𝒮|}` (`omissionNumber`). -/
def RareTransfer : Prop :=
  ∀ (P : GroupParams) (m : ℕ) (C₁ : ℝ), ∃ Cd : ℝ, ∀ (J : ℕ) (C₂ : ℝ),
    RareTransferBound P m C₁ Cd J C₂

/-- The conclusion of Lemma 3.10 for fixed constants: for all sufficiently large `x`, under the
ideal estimate `sup_Θ ‖𝒯(Θ)‖ ≤ L^{-E_id}`, the clean part of every edge at the truncation
`B = ⌈L²⌉` has norm at most `2 L^{-E_id + C_s}` on `ℋ`, for every `θ`. -/
def CleanNormBound (P : GroupParams) (Cs Eid : ℝ) (m : ℕ) (C₁ : ℝ) (J : ℕ) (C₂ : ℝ) : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B) (N : Type) [Fintype N] (𝔉 : N → Pattern 𝔊.big J P.ℓ)
      (ζ : ℝ) (k : ℤ), Admissible (Real.log x) m C₁ C₂ 𝔉 k →
      (∀ Θ : ℝ, idealOpNorm 𝔉 ζ Θ ≤ Real.log x ^ (-Eid)) →
      ∀ (θ : ℝ) (i : ℕ), i < Graph.sourceMemoryLength (Real.log x) →
        MemOpBound 𝔊 (edgeClean (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) θ i)
          (2 * Real.log x ^ (-Eid + Cs))

/-- **[S] Lemma 3.10 (clean norm, `lem:clean-norm`)** [S-02:0898–0909].

"There is `C_s`, depending only on the fixed data in Definition 3.1, such that the clean part of
every edge satisfies `‖ℰ_{i,clean}‖ ≤ 2 L^{-E_id + C_s}` for all sufficiently large `x`, under
(eq:ideal-norm-hypothesis). In particular `C_s` is independent of `m, C₁, J`."

Quantifiers: `P ⟶ C_s ⟶ E_id, m, C₁, J, C₂ ⟶ x₀`. The exponent `E_id` is the one of the
hypothesis; the threshold depends on it because the errors of the two changes of [S-02:0986–1012]
("`o(L^{-A})` for every fixed `A`") have to be at most `L^{-E_id}`. The bound is uniform in the
phase parameter `θ` of (eq:return-fourier): the ideal estimate is assumed for all real `Θ`
[S-02:0971–0980].

`Graph/` covers `μ̃_g/μ_g = 1 + O(N/P_*)`: `Graph.eventually_source_lifespan_relative_error`,
instantiated for the big groups of Definition 3.1 in `Bridge.lean`
(`eventually_tiltLaw_relative_error`). -/
def CleanNorm : Prop :=
  ∀ P : GroupParams, ∃ Cs : ℝ, ∀ (Eid : ℝ) (m : ℕ) (C₁ : ℝ) (J : ℕ) (C₂ : ℝ),
    CleanNormBound P Cs Eid m C₁ J C₂

/-- **(eq:whole-edge-contraction) for fixed constants** [S-02:1032–1037]: "the whole signed
truncated edge, with birth distinctness still omitted, satisfies `‖ℰ_i‖ ≤ L^{-G}`", for all
sufficiently large `x`, under the ideal estimate with exponent `E_id`. It is proved from
Lemmas 3.9 and 3.10 and the choice (eq:transference-parameter-choice) of the parameters in
`edgeContraction_of` (`Assembly.lean`). -/
def EdgeContractionBound (P : GroupParams) (G Eid : ℝ) (m : ℕ) (C₁ : ℝ) (J : ℕ) (C₂ : ℝ) :
    Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B) (N : Type) [Fintype N] (𝔉 : N → Pattern 𝔊.big J P.ℓ)
      (ζ : ℝ) (k : ℤ), Admissible (Real.log x) m C₁ C₂ 𝔉 k →
      (∀ Θ : ℝ, idealOpNorm 𝔉 ζ Θ ≤ Real.log x ^ (-Eid)) →
      ∀ (θ : ℝ) (i : ℕ), i < Graph.sourceMemoryLength (Real.log x) →
        MemOpBound 𝔊 (edgeOp (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) θ i)
          (Real.log x ^ (-G))

/-! ### Restoring distinct births -/

/-- **(eq:birth-address-count)** [S-02:1063–1068]:
"`A_* ≤ M|ℬ|(N+1) + (N+1)|ℬ|B = L^{O(1)}`. The implied exponent can be taken independent of `J`
once `x` is sufficiently large for fixed `J`."

Stated with the exponent `3`: `A_* ≤ L³` for `x ≥ x₀(P, J)` (indeed
`A_* = (N+1)|ℬ|(M + B) ≪_J L^{0.52} · T · L²`; `A_*` is computed in `birthAddr_card`). Then
`A_*^{2r} ≤ L^{C'r}` with `C' = 6` in (eq:rank-coefficient-count). -/
def BirthAddressCount : Prop :=
  ∀ (P : GroupParams) (J : ℕ), ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (_𝔊 : PrimeGroups P x S B),
      (Fintype.card (BirthAddr B J P.ℓ (memCutoff (Real.log x))
          (Graph.sourceMemoryLength (Real.log x))) : ℝ) ≤ Real.log x ^ (3 : ℝ)

/-- The large-rank estimate for fixed constants: for all sufficiently large `x` and every
collection `π` of blocks of addresses (at the truncation `B = ⌈L²⌉`), the total absolute
contribution of the histories satisfying `𝒞_π` is at most `L^{C_h (N+1)} (C/P_*)^{r(π)}`. -/
def HighRankBound (P : GroupParams) (m : ℕ) (C₁ : ℝ) (J : ℕ) (C₂ Ch Cp : ℝ) : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B) (N : Type) [Fintype N] (𝔉 : N → Pattern 𝔊.big J P.ℓ)
      (ζ : ℝ) (k : ℤ), Admissible (Real.log x) m C₁ C₂ 𝔉 k →
      ∀ θ : ℝ, ∀ π ∈ blockCollections (BirthAddr B J P.ℓ (memCutoff (Real.log x))
          (Graph.sourceMemoryLength (Real.log x))),
        absRankPart (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) θ π ≤
          Real.log x ^ (Ch * ((Graph.sourceMemoryLength (Real.log x) : ℝ) + 1)) *
            (Cp / Graph.sourcePrimeLowerBound P.c (Real.log x)) ^ blockRank π

/-- **Large rank: (eq:high-rank-path-bound)** [S-02:1107–1155].

"Fix `π`. Order birth addresses chronologically … and call the first address in each block its
pivot. Every other address is a dependent birth. When such an address is performed, its fresh
prime integration is constrained to the already determined pivot value. Since
`sup_{g ∈ ℬ, p ∈ 𝒫_g} μ̃_g(p) ≪ P_*^{-1}` (eq:tilted-point-mass), this improves the weighted
absolute row bound by `O(P_*^{-1})` per dependent birth. … Thus the total absolute contribution
for this fixed collection is at most `L^{C_h(N+1)} (C/P_*)^{r(π)}`, for fixed `C_h, C`; both may
depend on `m, C₁`."

Quantifiers: `P, m, C₁, J, C₂ ⟶ C_h, C > 0 ⟶ x₀ ⟶ x, …, π`. The paper does not say whether
`C_h, C` depend on `J`; the assembly only needs them after `J` (they enter the rank threshold
(eq:rank-threshold), which is chosen after all other constants), so this weakest form is stated.
The bound is uniform in the collection `π`.

(eq:tilted-point-mass) is proved in `Bridge.lean` (`eventually_tiltLaw_le`). -/
def HighRank : Prop :=
  ∀ (P : GroupParams) (m : ℕ) (C₁ : ℝ) (J : ℕ) (C₂ : ℝ), ∃ Ch Cp : ℝ, 0 < Cp ∧
    HighRankBound P m C₁ J C₂ Ch Cp

/-- **Small rank: (eq:low-rank-path-bound), in exact form** [S-02:1172–1225].

For every family of groups, all parameters `D`, every cutoff, every `θ`, and all constants
`C_g, C_e, C_w, K₀`: suppose that on `ℋ` (functions symmetric in the particle indices, measure
`memWeight ≥ 0`)

* every visit operation with a multiplier of modulus at most one on its births has norm at most
  `C_g` ("all `N + 1` ghost operations cost at most `L^{C_v}`");
* every edge operation with a multiplier of modulus at most one on its fresh births has norm at
  most `C_e` ("an affected edge can lose its signed norm saving, but Lemma 3.8 bounds its new norm
  by `L^{C_a}`");
* every edge operation without multiplier has norm at most `C_w ≤ C_e` ("unaffected edges retain
  their complete signed pattern sum and both symmetrizations, so (eq:whole-edge-contraction) still
  applies");
* `‖𝟏_∅‖² ≤ K₀` ("the boundary norms are bounded").

Then for every collection `π` of blocks of addresses, with `a = min(N, 2 r(π))`
("at most `2r` edges are affected by a rank-`r` collection"),
`|path integral with the indicator of 𝒞_π| ≤ K₀ · C_g^{N+1} · C_w^{N-a} · C_e^{a}`.

With `C_g = L^{C_v}`, `C_e = L^{C_a}`, `C_w = L^{-G}`, `K₀ = O(1)` this is
(eq:low-rank-path-bound) `O(L^{(-G + C_v)N + C_v + 2r(G + C_a)})`.

The statement has no threshold and no asymptotic content. Its proof is the argument of
[S-02:1172–1217]: the Fourier representation (eq:birth-equality-fourier) of the equalities of
birth values (the values are natural numbers below a common bound, so a finite Fourier average
serves as well as the integral over `[0,1]^{h-1}`), "collect the factors by their birth
operation", the identity `HistoryExpansion`, the fact that the operations with multipliers on
births map symmetric functions to symmetric functions [S-02:1198–1214], and Cauchy's
inequality. -/
def LowRankStep : Prop :=
  ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] (𝒢 : GroupFamily S B)
    (J ℓ : ℕ) (N : Type) [Fintype N] (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ)
    (Cg Ce Cw K₀ : ℝ), 0 ≤ Cg → 0 ≤ Cw → Cw ≤ Ce →
    (∀ s : MState 𝒢 J ℓ Bc, 0 ≤ memWeight 𝒢 D.q D.n s) →
    (∀ i : ℕ, i ≤ D.n → ∀ φ : ((g : B) → Batch 𝒢 Bc g) → ℂ, (∀ b, ‖φ b‖ ≤ 1) →
      OpBound (memWeight 𝒢 D.q D.n) (fun F => MemSymmetric F) (ghostOpWith D Bc φ i) Cg) →
    (∀ i : ℕ, i < D.n → ∀ ψ : ((g : B) → Slot J ℓ → Option ℕ) → ℂ, (∀ b, ‖ψ b‖ ≤ 1) →
      OpBound (memWeight 𝒢 D.q D.n) (fun F => MemSymmetric F) (edgeOpWith D Bc ψ θ i) Ce) →
    (∀ i : ℕ, i < D.n →
      OpBound (memWeight 𝒢 D.q D.n) (fun F => MemSymmetric F) (edgeOp D Bc θ i) Cw) →
    wNormSq (memWeight 𝒢 D.q D.n) (emptyVec 𝒢 J ℓ Bc) ≤ K₀ →
    ∀ π ∈ blockCollections (BirthAddr B J ℓ Bc D.n),
      ‖rankPart D Bc θ π‖ ≤
        K₀ * Cg ^ (D.n + 1) * Cw ^ (D.n - min D.n (2 * blockRank π)) *
          Ce ^ min D.n (2 * blockRank π)

/-- The bound for the path integral with the distinct-birth rule, for fixed constants: for all
sufficiently large `x`, under the ideal estimate with exponent `E_id`, for every `θ`:
`|⟨𝟏_∅, G_0 ℰ_0 ⋯ G_N 𝟏_∅⟩_distinct| ≤ ½ L^{-EN}` at the truncation `B = ⌈L²⌉`. -/
def DistinctBoundAt (P : GroupParams) (E Eid : ℝ) (m : ℕ) (C₁ : ℝ) (J : ℕ) (C₂ : ℝ) : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B) (N : Type) [Fintype N] (𝔉 : N → Pattern 𝔊.big J P.ℓ)
      (ζ : ℝ) (k : ℤ), Admissible (Real.log x) m C₁ C₂ 𝔉 k →
      (∀ Θ : ℝ, idealOpNorm 𝔉 ζ Θ ≤ Real.log x ^ (-Eid)) →
      ∀ θ : ℝ,
        ‖distinctSum (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) θ‖ ≤
          1 / 2 * Real.log x ^ (-(E * (Graph.sourceMemoryLength (Real.log x) : ℝ)))

/-- **The expansion with distinct births is `o(L^{-EN})`** [S-02:1237–1245]: "the high-rank terms
are controlled by their fresh-label costs, while the low-rank terms retain signed contraction on
`N - o(N)` edges. Together they bound the expansion with distinct births, which is the expression
required by Lemma 3.7. … The large- and small-rank estimates bound it by `o(L^{-EN})`, uniformly
in `θ`."

Quantifiers: those of Theorem 3.5 without `γ`:
`P, E ⟶ E_id ⟶ m, C₁ ⟶ J₀ ⟶ J ≥ J₀ ⟶ C₂ ⟶ x₀`. It is proved in `distinctBirthBound_of`
(`Assembly.lean`) from the statements above, with the choices (eq:transference-parameter-choice)
and (eq:rank-threshold). -/
def DistinctBirthBound : Prop :=
  ∀ (P : GroupParams) (E : ℝ), 0 < E → ∃ Eid : ℝ, 0 < Eid ∧
    ∀ (m : ℕ) (C₁ : ℝ), ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∀ C₂ : ℝ,
      DistinctBoundAt P E Eid m C₁ J C₂

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
