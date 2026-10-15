module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.Objects

/-!
# The intermediate results of [P] §6 with a joint residue weight

`TwoSidedReduction d H 𝔅` (`Supply/TwoSidedReduction.lean`) is the statement that [P] §6
(`verification/stage7-sources/P-06.tex`, lines 260–562 and 927–935) proves Theorem 6.1^{𝔅} from
Propositions 6.2 and 6.3, (cor:SM) and Mertens' estimate, the joint residue weight being carried
as in the public paper (`[PUB-tex:0462–0501]`). This file states the intermediate results of that
proof, one `def … : Prop` each. `TwoSidedProof/Assembly.lean` proves the chain from them to
`TwoSidedReduction d H 𝔅`.

## Nodes and links

A *node* is an estimate. A *link* is a `def XLink : Prop := (inputs and nodes) → node`, the
statement that one step of the manuscript works. Links and the nodes without further
decomposition are the *leaves*; `Leaves d H 𝔅` collects them. Every leaf is a closed proposition
which is claimed to be true as stated: the hypotheses `0 < H`, `0 < q < 1`, `0 < q₀ < 1`, the
ranges of the scales and the positivity of the savings are part of the statements.

## The stages (the order of the manuscript)

1. **Bounded and invariant factors** (`[P-06:0045–0053, 0079–0085]`): `MarkedBound`,
   `CorePowerBounded`, `CoreInvariance`.
2. **The graph inputs for the active groups** (`[P-06:0099–0258]`): `BigIntervals`,
   `HalfSplitBalanced`; `PairingAt`, `SchurAt`, `PatternCountAt`, `TransferData` (the two imported
   propositions at the constants chosen in the manuscript's order; `Assembly.transferData`
   derives `TransferData` from `GraphTransferInput` and `IdealFamilyInput`).
3. **Endpoint bounds and the insertion of the cutoff** (`[P-06:0260–0316]`): `EndpointNorms`,
   `EndpointNormsLink`, `ResidualBoundAt`, `InsertionLink`.
4. **Removal of the shared labels** (`[P-06:0318–0377]`): `RawStrippingAt`,
   `ComparisonStrippingAt`, `RawStrippingLink`, `ComparisonStrippingLink`.
5. **Comparison multipliers and local energy** (`[P-06:0379–0553]`): `StrippedBoundAt`,
   `StrippedComparisonBound`, `KernelExpansionLink`; `ComparisonCorrelationBound`,
   `SeparationLink`; `EndpointSquares`, `EndpointSquaresLink`; `BilinearFourier`,
   `MultiplierMinor`, `MultiplierLink`; `LocalMellin`, `ArcEnergy`, `ArcEnergyLink` (the place
   where (cor:SM) is used); `BilinearBound`, `CircleLink`.
6. **The subtraction** (`[P-06:0927–0935]`) is `Assembly.twoSidedBound_of_stages`.

## The order of the constants

`[P-06:0301–0316]`: "After the desired saving `A` and the original data, fix `C_3`, then a
transfer saving `E` large enough to cover `A`, `2C_3`, and the fixed dyadic costs. Choose `E_id`
from Proposition 6.2, obtain `m_0, J_0, C_1` from Proposition 6.3, and finally choose a fixed `J`
satisfying both lower bounds." Here: `C_3` is the exponent of `EndpointNorms` (it exists before
`J`); `E = A + 2|C_3| + 2`; `TransferData d D E` supplies `m_0, J, C_1`, the kernel exponents and
`C_abs`. `[P-06:0415]`: "All exponents chosen from now on may depend on the fixed ideal family":
`C_5` (`EndpointSquares`), then the minor-arc saving and `C_6` (`MultiplierMinor`), then the
precision of (cor:SM) (`ArcEnergy`); each is an existential constant of the node named, placed
after the data it may depend on. In every node the constant `M` and the threshold `x₀` are chosen
last, and the configuration (active groups, slots, `G`) and all tests after `x`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference
open scoped ContDiff

noncomputable section

/-! ### 1. Bounded and invariant factors -/

/-- **(cor:marked-bound)** (`[P-06:0044–0053]`): "For every fixed `m'`,
`|W_𝐭^𝐛(n)| ≤ W_𝐭(n) ≤ L^{C(m')}` (`t_g ≤ m'`, `|𝐛| ≤ 1`). … Indeed, each factor
`q_0^{u-t} (u)_t / V_g^t`, for `u ≥ t`, is bounded by a constant depending only on `m', q_0, v_-`,
and there are `O(log L)` factors."

Order: `P`, `q₀ ∈ (0,1)`, `m'`; then the exponent `C` and a threshold (`log L ≥ 0` is used); then
`x`, the groups, the vector `𝐭`, the test and `n`. `t_g = 0` and `n = 0` are allowed. -/
def MarkedBound : Prop :=
  ∀ (P : ActiveGroupConstants) (q₀ : ℝ), 0 < q₀ → q₀ < 1 → ∀ m' : ℕ, ∃ C x₀ : ℝ,
    ∀ x : ℝ, x₀ ≤ x → ∀ 𝔊 : ActiveGroups, 𝔊.Admissible P x →
      ∀ t : 𝔊.Index → ℕ, (∀ g, t g ≤ m') →
        ∀ test : ((g : 𝔊.Index) → Fin (t g) → ℕ) → ℂ, (∀ 𝔭, ‖test 𝔭‖ ≤ 1) →
          ∀ n : ℕ, ‖𝔊.activeWeight q₀ t test n‖ ≤ Real.log x ^ C

/-- **The centered core is bounded on every fixed power range** (`[P-06:0079–0082]`): "The
harmonic prime estimates give `C_x = O_ε(1)`. On every fixed positive-power range for `n`, there
are only `O_ε(1)` prime divisors in the slot ranges. Since `𝒲` is bounded for fixed `K, q`, `F_x`
is bounded there."

Order: `q ∈ (0,1)`, `ε`, the power `κ`, `K`; then the bound `B` (it depends on `d, q, ε, κ, K`
only); then the array; then a threshold (it may depend on the array); then the slots and
`1 ≤ u ≤ x^κ`. `u ≥ 1` is needed: every prime divides `0`. The range `u ≤ R x` of
`Extraction.CoreBounded` is not enough here: the positions of §6 are `≍ x D` with
`D = x^{o(1)}`. -/
def CorePowerBounded (d : ℕ) : Prop :=
  ∀ q : ℝ, 0 < q → q < 1 → ∀ ε : ℝ, 0 < ε → ∀ κ : ℝ, 0 < κ → ∀ K : ℕ, ∃ B : ℝ, 0 ≤ B ∧
    ∀ 𝔞 : MarkingArray K, ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
      ∀ S : Fin d → Finset ℕ, SlotsAdmissible ε x S →
        ∀ u : ℕ, 1 ≤ u → (u : ℝ) ≤ x ^ κ → |centeredCore q 𝔞 x S u| ≤ B

/-- **The centered core is invariant under the active primes** (`[P-06:0082–0084]`): "Also
`F_x(pn) = F_x(n)` for every active prime `p`: the active groups are disjoint both from the inert
bands and from the long-prime slots."

The disjointness holds for large `x`: the bands lie below `exp(2 L^{0.2})`, the active primes in
`[exp(L^{0.27}), exp(L^{0.46})]`, the slots above `x^ε = exp(ε L)`. The threshold depends on `ε`
only (not on the array, `q`, `K`, `P`). Exact for every `n`, `n = 0` included. -/
def CoreInvariance (d : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (q : ℝ) (K : ℕ) (𝔞 : MarkingArray K) (P : ActiveGroupConstants) (𝔊 : ActiveGroups),
      𝔊.Admissible P x → ∀ S : Fin d → Finset ℕ, SlotsAdmissible ε x S →
        ∀ p ∈ 𝔊.allPrimes, ∀ n : ℕ,
          centeredCore q 𝔞 x S (p * n) = centeredCore q 𝔞 x S n

/-! ### 2. The graph inputs for the active groups -/

/-- **Every big active group is the set of all primes of an interval** (`[P-06:0023]`), in the
form `Transference.IsPrimeInterval` required by Proposition 6.3 (`[S-03:0004–0009]`). -/
def BigIntervals : Prop :=
  ∀ (P : ActiveGroupConstants) (x : ℝ) (𝔊 : ActiveGroups), 𝔊.Admissible P x →
    ∀ j : Fin 𝔊.numBig, IsPrimeInterval (𝔊.group (Sum.inr j))

/-- The blocks `{i : 2i < n}` and `{i : 2i ≥ n}` of `n` big groups differ in size by at most one
(`[P-06:0211]`, `[S-03:0442–0443]`). -/
def HalfSplitBalanced : Prop := ∀ n : ℕ, BalancedSplit (halfSplit n)

/-- **The number of patterns of the residual family is at most `L^{C₁}`** for the active groups
(`[P-06:0248–0250]`: "Expanding the two kernels, including all patterns, has total coefficient
mass and number of terms bounded by fixed powers of `L`"; `Transference.PatternCountBound`). -/
def PatternCountAt (d : ℕ) (D : FixedData) (m₀ J : ℕ) (C₁ : ℝ) : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ I : Config d D x,
    (Fintype.card (ComparisonIndex (Fin I.𝔊.numBig) I.blocks J m₀) : ℝ) ≤ Real.log x ^ C₁

/-- **The absolute Schur bound of Proposition 6.2 for the residual family** (`[P-06:0177–0180]`):
"Taking absolute values of the individual transition coefficients gives row and column sums at
most `L^{C_abs}`", for every real `ζ`, with `k = 1`. This is `Transference.IntSchurBound` for the
prime groups of a configuration and the family `Config.family`. -/
def SchurAt (d : ℕ) (D : FixedData) (m₀ J : ℕ) (qs hs xs Cabs : ℝ) : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (I : Config d D x) (ζ : ℝ)
    (s : PState intPos I.primeGroups.toGroupFamily J D.params.ℓ),
    physAbsRowSum intPos I.primeGroups.toGroupFamily D.params.q (I.family J m₀ qs hs xs) 1 ζ s ≤
        Real.log x ^ Cabs ∧
      physAbsColSum intPos I.primeGroups.toGroupFamily D.params.q (I.family J m₀ qs hs xs) 1 ζ
          s ≤ Real.log x ^ Cabs

/-- **The transferred pairing (cor:transferred-pairing) for the residual family**
(`[P-06:0163–0174, 0298–0299]`): for `|ζ| ≤ L` ("Fix the cutoff `|ζ| ≤ L` now, so `C_4 = 1`
suffices in Proposition 6.3"), a dyad `[X, 2X)` with `x^{1/2} ≤ X ≤ x²` (`γ = 1/2`), `k = 1`, a
first vector independent of the marks with `sup |f| ≤ exp(√L)` and `‖f‖, ‖g‖ ≤ X^{1/2} L^{C₃}`,

`|⟨f, 𝒜_ζ g⟩| ≤ M X L^{-E + 2C₃}`.

This is `Transference.PairingBound` with its ideal-norm hypothesis discharged by Proposition 6.3,
for the prime groups of a configuration. -/
def PairingAt (d : ℕ) (D : FixedData) (m₀ J : ℕ) (qs hs xs E C₃ : ℝ) : Prop :=
  ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ (I : Config d D x) (ζ : ℝ), |ζ| ≤ Real.log x →
    ∀ X : ℝ, x ^ ((1 : ℝ) / 2) ≤ X → X ≤ x ^ (2 : ℝ) →
    ∀ (fn : ℤ → ℂ) (g : PState intPos I.primeGroups.toGroupFamily J D.params.ℓ → ℂ),
      EndpointHyp I.primeGroups J X C₃ 1 fn g →
      ‖pairMarkFree intPos I.primeGroups.toGroupFamily J D.params.ℓ (intWindow X) fn
          (physOp intPos I.primeGroups.toGroupFamily D.params.q (I.family J m₀ qs hs xs) 1 ζ
            g)‖ ≤ M * X * Real.log x ^ (-E + 2 * C₃)

/-- **The two imported propositions at the constants of [P] §6** (`[P-06:0301–0306]`): for a
transfer saving `E` there are `m₀`, a fixed `J`, `C₁`, kernel exponents `q_*, h_*, x_* ≥ 0` and
`C_abs` such that the residual family has at most `L^{C₁}` patterns, satisfies the absolute Schur
bound, and satisfies the transferred pairing bound with saving `E` for every norm exponent `C₃`.

`Assembly.transferData` proves this from `GraphTransferInput` and `IdealFamilyInput` in the order
`E ⟶ E_id ⟶ (m₀, J₀, C₁, exponents) ⟶ (J₀', C_abs) ⟶ J = max(J₀, J₀')`. -/
def TransferData (d : ℕ) (D : FixedData) (E : ℝ) : Prop :=
  ∃ (m₀ J : ℕ) (C₁ qs hs xs Cabs : ℝ), 0 ≤ qs ∧ 0 ≤ hs ∧ 0 ≤ xs ∧
    PatternCountAt d D m₀ J C₁ ∧ SchurAt d D m₀ J qs hs xs Cabs ∧
    ∀ C₃ : ℝ, PairingAt d D m₀ J qs hs xs E C₃

/-! ### 3. Endpoint bounds and the insertion of the cutoff -/

/-- The two endpoint norms on the enlarged dyads, for a fixed number `J` of first slots and the
exponent `C₃`: for `x^{1/2} ≤ X ≤ x²`,

`∑_{X ≤ n < 4X} |F_x(n)|² dampedMass(n) ≤ X L^{2C₃}`, `∑_{X ≤ n < 4X} |G(n)|² dampedMass(n) ≤
X L^{2C₃}`. -/
def EndpointNormsAt (d : ℕ) (D : FixedData) (J : ℕ) (C₃ : ℝ) : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ I : Config d D x,
    ∀ X : ℝ, x ^ ((1 : ℝ) / 2) ≤ X → X ≤ x ^ (2 : ℝ) →
      (∑ n ∈ wideWindow X,
          centeredCore D.q D.𝔞 x I.S n.toNat ^ 2 * dampedMass I.𝔊 J D.q₀ n ≤
        X * Real.log x ^ (2 * C₃)) ∧
      ∑ n ∈ wideWindow X, ‖I.G n.toNat‖ ^ 2 * dampedMass I.𝔊 J D.q₀ n ≤
        X * Real.log x ^ (2 * C₃)

/-- **The endpoint norms** (`[P-06:0262–0285]`): "For a fixed ordered physical list with
squarefree product `P`, `n_* ∣ n/P`. The divisor moment bound of Lemma 2.2 gives
`∑_{n ≍ X, P ∣ n} |G(n)|² ≤ L^{2C} ∑_{v ≪ X/P} τ(v)^{2C} ≪ (X/P) L^{C_*}`. The same statement
holds for `F_x`, which is bounded. … the normalized list sum satisfies (cor:list-norm)
`∏_g V_g^{-M} ∑_{physical lists} 1/P ≤ ∏_g (∑_{p ∈ 𝒫_g} 1/(V_g p))^M = 1`. Consequently both
endpoint norms on an enlarged dyad are at most `X^{1/2} L^{C_3}`, where `C_3` is independent of
`J` and `m_0`. … It is essential here to keep `q_0^{(ω_P(n) - M s_P)/2} ≤ 1` intact."

Order: the fixed data; then `C₃`; then `J`; then the threshold. -/
def EndpointNorms (d : ℕ) : Prop :=
  ∀ D : FixedData, ∃ C₃ : ℝ, ∀ J : ℕ, EndpointNormsAt d D J C₃

/-- **The step (cor:list-norm)**: the endpoint norms follow from the boundedness of `F_x` on power
ranges; the divisor moments (`divisorMoments`) are a theorem. -/
def EndpointNormsLink (d : ℕ) : Prop := CorePowerBounded d → EndpointNorms d

/-- **The total residual edge pairing is `O_A(L^{-A})`** (`[P-06:0315–0316]`), at given family
parameters. -/
def ResidualBoundAt (d H : ℕ) (𝔅 : JointResidueWeight H) (D : FixedData) (m₀ J : ℕ)
    (qs hs xs A : ℝ) : Prop :=
  ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ I : Config d D x,
    ‖I.edgeTotal 𝔅 J m₀ qs hs xs‖ ≤ M * Real.log x ^ (-A)

/-- **The insertion of the cutoff and the transferred estimate** (`[P-06:0287–0316]`;
the joint factor: `[PUB-tex:0479–0482]`).

"Insert `Ψ(n/(xD))/n` into the physical edge pairing. Its support has `n ≍ n' ≍ xD = x^{1+o(1)}`.
Partition `n` into `O(L)` dyads `[X, 2X)`, restricting `n'` to fixed enlargements. Let
`φ(u) = Ψ(e^u)` … Then (cor:insertion-separation)
`Ψ(n/(xD)) = (1/2π) ∫ φ̂(ζ) (n/x)^{iζ} D^{-iζ} dζ`. Put `X/n` into the first vector and `1/X`
outside. … For the tail of (cor:insertion-separation), the absolute Schur estimate and the endpoint
norms cost at most a fixed power of `L`. Since `∫_{|ζ| > L} |φ̂(ζ)| dζ ≪_N L^{-N}` for every fixed
`N`, its differentiation order can be chosen after the family is fixed. … Thus the total residual
edge pairing is `O_A(L^{-A})`." With the weight: "Write `𝓑` as a sum of at most `H²` products of
residue indicators, one at each endpoint. Insert these into the bilinear graph transfer. The
endpoint norms do not increase, and the same ideal kernel applies to every term."

As an implication, for arbitrary family parameters and exponents with `E ≥ A + 2C₃ + 2`: the
pairing bound with saving `E` for `|ζ| ≤ L`, the Schur bound for all `ζ` and the endpoint norms
give the bound for the edge sum. `CorePowerBounded` gives `sup |f| ≤ exp(√L)`. `0 < H` is needed
(for `H = 0` a weight on `ℤ²` is not a finite combination of products). -/
def InsertionLink (d H : ℕ) (𝔅 : JointResidueWeight H) : Prop :=
  0 < H → CorePowerBounded d → ∀ (D : FixedData) (m₀ J : ℕ) (qs hs xs E C₃ Cabs A : ℝ),
    0 < A → A + 2 * C₃ + 2 ≤ E → PairingAt d D m₀ J qs hs xs E C₃ →
      SchurAt d D m₀ J qs hs xs Cabs → EndpointNormsAt d D J C₃ →
        ResidualBoundAt d H 𝔅 D m₀ J qs hs xs A

/-! ### 4. Removal of the shared labels -/

/-- The edge sum of the raw pattern is the two-sided sum (eq:two-sided) up to `M L^{-A}`. -/
def RawStrippingAt (d H : ℕ) (𝔅 : JointResidueWeight H) (D : FixedData) (J : ℕ) (A : ℝ) : Prop :=
  ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ I : Config d D x,
    ‖I.rawEdge 𝔅 J - twoSidedSum D.q D.q₀ D.𝔞 x I.𝔊 I.S 𝔅 D.Ψ I.G‖ ≤ M * Real.log x ^ (-A)

/-- The edge sum of every comparison pattern is its stripped expression (cor:stripped) up to
`M L^{-A}`, uniformly in the comparison. -/
def ComparisonStrippingAt (d H : ℕ) (𝔅 : JointResidueWeight H) (D : FixedData) (m₀ J : ℕ)
    (qs hs xs A : ℝ) : Prop :=
  ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ I : Config d D x,
    ∀ C : Fin I.𝔊.numBig → Finset (Fin J), IsComparison I.blocks m₀ C →
      ‖I.comparisonEdge 𝔅 qs hs xs C - I.strippedSum 𝔅 qs hs xs C‖ ≤ M * Real.log x ^ (-A)

/-- **Removal of the shared labels, raw pattern** (`[P-06:0318–0370]`; the joint factor:
`[PUB-tex:0482–0485]`).

"For a single pattern put `n = D_R w`, `n' = D_R w'`. The shift becomes `w' = w + D_C`. Away from
shared-label collisions, (cor:stripping-normalization) `ω_g(D_R w) - M = ω_g(w) - t_g`,
`V_g^{-M-t_g} = V_g^{-(M-t_g)} V_g^{-2t_g}`, `1/n = 1/(D_R w)`. The factor `D_R^{-1}` changes each
shared sum into its probability law `μ_g`, and the remaining list factors and damping are exactly
`W_𝐭(w) W_𝐭(w')`. The endpoint cores are invariant under these labels. … Conditional on `w, w'`
and the free labels, the harmonic mass of a shared/shared coincidence, a shared/free coincidence,
or a shared prime dividing `w w'` is therefore (cor:shared-collision)
`O_J(L^{C_J} exp(-L^{.27}))`. … For the raw pattern, `D_C = 1` and `t_g = 1`, so (cor:stripped) is
precisely the left side of (eq:two-sided)." With the weight: "Their product `R` is coprime to `H`
for large `x`, so (eq:B-shared) preserves the joint factor exactly."

Inputs: the invariance and the boundedness of `F_x`, the marked bound. The divisor moments are a
theorem. Order: the fixed data, `J`, the saving; then `M`, `x₀` (they depend on `J`:
"Changing the damping loses at most `q_0^{-2M s_P} = L^{O(J)}`"). `0 < H` is needed for
`(D_R, H) = 1`. -/
def RawStrippingLink (d H : ℕ) (𝔅 : JointResidueWeight H) : Prop :=
  0 < H → CoreInvariance d → CorePowerBounded d → MarkedBound →
    ∀ (D : FixedData) (J : ℕ) (A : ℝ), 0 < A → RawStrippingAt d H 𝔅 D J A

/-- **Removal of the shared labels, comparison patterns** (`[P-06:0318–0370]`), with the free
labels: "If a free prime occurs in either unshared endpoint list, it divides `D_C` and one of
`w, w + D_C`, hence both. It is at least `exp(L^{.39})`. On `w ≍ x D_C` the count of its multiples
is `O(x D_C / p)`; Cauchy and a fixed higher divisor moment bound the corresponding weighted
harmonic mass by `L^{O(1)} p^{-1/2}`. Summing over the `O_{m_0}(log L)` free slots costs
`L^{O(1)} exp(-c L^{.39})`. … All errors remain smaller than every negative log power after the
fixed pattern cost."

For arbitrary kernel exponents `q_*, h_*, x_* ≥ 0` (the pattern cost is
`sup |K_ν| ≤ Q⁴ ξ⁻² = L^{4q_* + 2x_*}`) and uniformly in the comparison. -/
def ComparisonStrippingLink (d H : ℕ) (𝔅 : JointResidueWeight H) : Prop :=
  0 < H → CoreInvariance d → CorePowerBounded d → MarkedBound →
    ∀ (D : FixedData) (m₀ J : ℕ) (qs hs xs : ℝ), 0 ≤ qs → 0 ≤ hs → 0 ≤ xs →
      ∀ A : ℝ, 0 < A → ComparisonStrippingAt d H 𝔅 D m₀ J qs hs xs A

/-! ### 5. Comparison multipliers and local energy -/

/-- Every stripped comparison correlation is at most `M L^{-A}`, uniformly in the comparison. -/
def StrippedBoundAt (d H : ℕ) (𝔅 : JointResidueWeight H) (D : FixedData) (m₀ J : ℕ)
    (qs hs xs A : ℝ) : Prop :=
  ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ I : Config d D x,
    ∀ C : Fin I.𝔊.numBig → Finset (Fin J), IsComparison I.blocks m₀ C →
      ‖I.strippedSum 𝔅 qs hs xs C‖ ≤ M * Real.log x ^ (-A)

/-- **The comparison correlations are negligible** (`[P-06:0372–0377, 0927–0932]`): "It remains to
bound the latter separately", "by an arbitrarily large negative log power", for all kernel
exponents `q_*, h_*, x_* ≥ 0` and every saving. -/
def StrippedComparisonBound (d H : ℕ) (𝔅 : JointResidueWeight H) : Prop :=
  0 < H → ∀ (D : FixedData) (m₀ J : ℕ) (qs hs xs : ℝ), 0 ≤ qs → 0 ≤ hs → 0 ≤ xs →
    ∀ A : ℝ, 0 < A → StrippedBoundAt d H 𝔅 D m₀ J qs hs xs A

/-- **A comparison correlation with separated bounded tests is negligible**
(`[P-06:0390–0400]`): for tests `b₁, b₂` on the free labels of the two blocks, each supported on
one log cell `[U_i, e U_i]`, and list tests `𝐛₁, 𝐛₂` of modulus at most one depending only on big
marks, the correlation `Config.comparisonCorrelation` is at most `M L^{-A}`.

Order: the fixed data, the bound `m₀` for the freed slots, the saving; then `M`, `x₀`; then the
configuration, the number of slots `J` and the comparison (only the numbers `|C_g| ≤ m₀` matter),
the cells and the tests. `1 ≤ U_i` is part of the hypotheses (the cells of free products of
primes). -/
def ComparisonCorrelationBound (d H : ℕ) (𝔅 : JointResidueWeight H) : Prop :=
  0 < H → ∀ (D : FixedData) (m₀ : ℕ) (A : ℝ), 0 < A →
    ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ I : Config d D x,
      ∀ (J : ℕ) (C : Fin I.𝔊.numBig → Finset (Fin J)), IsComparison I.blocks m₀ C →
      ∀ (b₁ b₂ : AuxList (groupFamily I.𝔊).big C → ℂ) (U₁ U₂ : ℝ), 1 ≤ U₁ → 1 ≤ U₂ →
        BlockTest I.blocks true C b₁ U₁ → BlockTest I.blocks false C b₂ U₂ →
      ∀ test₁ test₂ : ((g : I.𝔊.Index) → Fin (markCount I.𝔊 C g) → ℕ) → ℂ,
        MarkTest I.𝔊 test₁ → MarkTest I.𝔊 test₂ →
          ‖I.comparisonCorrelation 𝔅 C (fun r => b₁ r * b₂ r) test₁ test₂‖ ≤
            M * Real.log x ^ (-A)

/-- **The kernel expansion** (`[P-06:0381–0391]`): "Expand the two kernels in
(cor:comparison-kernel). Their contract supplies only a fixed log-power total cost. In each term
the two nonempty free products are independent and lie in log cells of width at most one … The
cell and character expansion factors into separate bounded tests on the two free tuples and on
each endpoint's big marks."

`𝒦_Λ(D, X) = ∑_{j : ν_{Λj} ≥ ξ} ν_{Λj}^{-1} ∑_χ (1_{log D ∈ I_j} conj χ(D)) (1_{log X ∈ I_j} χ(X))`
has at most `(number of cells) · Q²` terms with coefficients at most `ξ⁻¹`
(`Transference.KernelCostsLemma`, a theorem of `Transference/KernelCosts.lean`, which needs the big
groups to be intervals); the cells have width `h = L^{-h_*} ≤ 1`, so each test on a free tuple is
a `BlockTest` with `U = e^{jh} ≥ 1`. -/
def KernelExpansionLink (d H : ℕ) (𝔅 : JointResidueWeight H) : Prop :=
  BigIntervals → KernelCostsLemma → ComparisonCorrelationBound d H 𝔅 →
    StrippedComparisonBound d H 𝔅

/-- **(cor:endpoint-squares)** (`[P-06:0402–0410]`): "The endpoint sequences have smooth cutoffs
at `Y`, fixed log-power twists, and the form of their respective invariant cores times `W_𝐭^𝐛`,
with `|𝐛| ≤ 1` … Fixed divisor moments give `∑_w |𝒰(w)|² + ∑_w |𝒱(w)|² ≪ Y L^{C_5}`."

Order: the fixed data, the bound `m'` for the `t_g`, the support `[a₁, a₂] ⊂ (0, ∞)` of the
cutoff and the exponent `D₀` of its size; then `C₅` and the threshold; then the configuration, the
scale `x ≤ Y ≤ x²`, `𝐭`, the test, the cutoff and the twist. No smoothness of the cutoff and no
restriction on the twist are needed. -/
def EndpointSquares (d : ℕ) : Prop :=
  ∀ (D : FixedData) (m' : ℕ) (a₁ a₂ : ℝ), 0 < a₁ → a₁ ≤ a₂ → ∀ D₀ : ℝ, ∃ C₅ x₀ : ℝ,
    ∀ x : ℝ, x₀ ≤ x → ∀ I : Config d D x, ∀ Y : ℝ, x ≤ Y → Y ≤ x ^ (2 : ℝ) →
    ∀ t : I.𝔊.Index → ℕ, (∀ g, t g ≤ m') →
    ∀ test : ((g : I.𝔊.Index) → Fin (t g) → ℕ) → ℂ, (∀ 𝔭, ‖test 𝔭‖ ≤ 1) →
    ∀ ψ : ℝ → ℂ, Function.support ψ ⊆ Set.Icc a₁ a₂ → (∀ u : ℝ, ‖ψ u‖ ≤ Real.log x ^ D₀) →
      (∀ σ : ℝ, ∑ᶠ w : ℕ, ‖comparisonEndpoint D.q D.q₀ D.𝔞 x I.𝔊 I.S t test ψ σ Y w‖ ^ 2 ≤
        Y * Real.log x ^ C₅) ∧
      ∑ᶠ v : ℕ, ‖secondEndpoint D.q₀ I.𝔊 t test I.G ψ Y v‖ ^ 2 ≤ Y * Real.log x ^ C₅

/-- (cor:endpoint-squares) follows from the marked bound, the boundedness of `F_x` and the divisor
moments (a theorem). -/
def EndpointSquaresLink (d : ℕ) : Prop := MarkedBound → CorePowerBounded d → EndpointSquares d

/-- **The elementary bilinear Fourier estimate** (`[P-06:0431–0453]`): "Cauchy followed by the
spacing estimate for `‖θ u‖⁻¹`": for coefficients on `u ∈ [U₁, eU₁]`, `v ∈ [U₂, eU₂]`, and a
reduced fraction `h/r` with `|θ - h/r| ≤ r⁻²`,

`|∑_{u,v} α_u β_v e(θ u v)|² ≤ C ‖α‖₂² ‖β‖₂² (U₁/r + 1)(U₂ + r log(2r))`,

with an absolute constant `C`. "Cauchy in the variable on the interval of length `O(U_2)`,
expansion, and the geometric-sum bound give an unnormalized square at most
`‖a‖₂² ‖b‖₂² (U_2 + ∑_{1 ≤ v ≪ U_1} min{U_2, ‖θ v‖⁻¹})`. For `r ≥ 2`, split the `v`-range into
`O(1 + U_1/r)` blocks of diameter at most `r/2` … The case `r = 1` is immediate". -/
def BilinearFourier : Prop :=
  ∃ C : ℝ, ∀ U₁ U₂ : ℝ, 1 ≤ U₁ → 1 ≤ U₂ → ∀ (s₁ s₂ : Finset ℕ) (α β : ℕ → ℂ),
    (∀ u ∈ s₁, U₁ ≤ (u : ℝ) ∧ (u : ℝ) ≤ Real.exp 1 * U₁) →
    (∀ v ∈ s₂, U₂ ≤ (v : ℝ) ∧ (v : ℝ) ≤ Real.exp 1 * U₂) →
    ∀ (θ : ℝ) (h : ℤ) (r : ℕ), 0 < r → h.natAbs.Coprime r →
      |θ - (h : ℝ) / (r : ℝ)| ≤ 1 / (r : ℝ) ^ 2 →
        ‖∑ u ∈ s₁, ∑ v ∈ s₂, α u * β v * addChar (θ * ((u : ℝ) * (v : ℝ)))‖ ^ 2 ≤
          C * (∑ u ∈ s₁, ‖α u‖ ^ 2) * (∑ v ∈ s₂, ‖β v‖ ^ 2) *
            (((U₁ / (r : ℝ)) + 1) * (U₂ + (r : ℝ) * Real.log (2 * (r : ℝ))))

/-- **The multiplier is small off the major arcs** (`[P-06:0417–0474]`): (cor:bilinear-multiplier)
and (cor:major-arcs). "Given any required saving, choose `C_6` sufficiently large and set
`H = H'/L^{C_6}`, `𝔐_H = ⋃_{k ≤ L^{C_6}, (h,k)=1} {θ : |θ - h/k| ≤ H⁻¹}`. Dirichlet approximation
with denominator bound `⌊H'/L^{C_6-1}⌋` gives a fraction `h/r` with `|θ - h/r| ≤ r⁻²`. If
`r ≤ L^{C_6}`, this places `θ` in `𝔐_H`. Otherwise … `𝔪` is arbitrarily log-power small off
`𝔐_H`."

Order: `P`, `m₀`, the saving `A`; then `C₆ > 0` and the threshold; then `x`, the groups, the
comparison, the cells `U₁, U₂ ≥ 1`, the tests, `θ`. The conclusion is the dichotomy: `θ` lies in
an arc `|θ - h/k| ≤ L^{C₆}/(U₁U₂)`, `k ≤ L^{C₆}`, or `|𝔪(θ)| ≤ L^{-A}`. The fractions of the arcs
need not be reduced. The product probability bound `ρ(u) ≤ L^{C_7}/u` (`[P-06:0423–0430]`) is
part of the proof. -/
def MultiplierMinor : Prop :=
  ∀ (P : ActiveGroupConstants) (m₀ : ℕ) (A : ℝ), 0 < A → ∃ C₆ x₀ : ℝ, 0 < C₆ ∧
    ∀ x : ℝ, x₀ ≤ x → ∀ 𝔊 : ActiveGroups, 𝔊.Admissible P x →
    ∀ (J : ℕ) (C : Fin 𝔊.numBig → Finset (Fin J)), IsComparison (halfSplit 𝔊.numBig) m₀ C →
    ∀ (b₁ b₂ : AuxList (groupFamily 𝔊).big C → ℂ) (U₁ U₂ : ℝ), 1 ≤ U₁ → 1 ≤ U₂ →
      BlockTest (halfSplit 𝔊.numBig) true C b₁ U₁ →
      BlockTest (halfSplit 𝔊.numBig) false C b₂ U₂ →
    ∀ θ : ℝ,
      (∃ (k : ℕ) (h : ℤ), 0 < k ∧ (k : ℝ) ≤ Real.log x ^ C₆ ∧
        |θ - (h : ℝ) / (k : ℝ)| ≤ Real.log x ^ C₆ / (U₁ * U₂)) ∨
      ‖multiplier (groupFamily 𝔊).big C (fun r => b₁ r * b₂ r) θ‖ ≤ Real.log x ^ (-A)

/-- The multiplier bound follows from the bilinear Fourier estimate (with Dirichlet's
approximation theorem and the product probability bound). -/
def MultiplierLink : Prop := BilinearFourier → MultiplierMinor

/-- **Lemma (Local Mellin energy)** `lem:local-mellin` (`[P-06:0488–0528]`): "Let `a_w` be
supported on `w ≍ Y` … For every fixed integer `j ≥ 1`,
`∫_{|β| ≤ H⁻¹} |â(β)|² dβ ≪_j (1/Y) ∫_ℝ (1 + H|t|/Y)^{-j} |∑_w a_w w^{it}|² dt
  + (H/Y)² ∑_w |a_w|²`", with `â(θ) = ∑_w a_w e(θ w)`.

Stated for `j ≥ 2`, a support `[a₁ Y, a₂ Y]` with fixed `0 < a₁ ≤ a₂`, and all `1 ≤ H ≤ Y`, with
a constant depending on `j, a₁, a₂` only. For `j = 1` the integral over `t` diverges (the
integrand is `≍ ∑ |a_w|² / (1 + H|t|/Y)` on average), so the manuscript's inequality is true but
empty there, while Lean's integral of a non-integrable function is `0`; the manuscript chooses `j`
large ("on choosing `j` last"). The manuscript's `H = x^{o(1)} → ∞`, `Y = x^{1+o(1)}` is the range
of application; the proof gives `H ≤ cY`, and for `cY ≤ H ≤ Y` the bound follows from
`|â|² ≤ (a₂ Y + 1) ∑ |a_w|²`. -/
def LocalMellin : Prop :=
  ∀ j : ℕ, 2 ≤ j → ∀ a₁ a₂ : ℝ, 0 < a₁ → a₁ ≤ a₂ → ∃ C : ℝ, ∀ Y H : ℝ, 1 ≤ H → H ≤ Y →
    ∀ (s : Finset ℕ) (a : ℕ → ℂ), (∀ w ∈ s, a₁ * Y ≤ (w : ℝ) ∧ (w : ℝ) ≤ a₂ * Y) →
      ∫ β in (-(1 / H))..(1 / H), ‖∑ w ∈ s, a w * addChar (β * (w : ℝ))‖ ^ 2 ≤
        C * (Y⁻¹ * (∫ t : ℝ, (1 + H * |t| / Y) ^ (-(j : ℝ)) *
            ‖∑ w ∈ s, a w * (w : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2) +
          (H / Y) ^ 2 * ∑ w ∈ s, ‖a w‖ ^ 2)

/-- **(cor:arc-energy-target) with denominators `k ≤ L^B` and arcs `|β| ≤ L^{C₆}/H'`**
(`[P-06:0479–0486]`): for every fixed `A`,

`∫_{|β| ≤ H⁻¹} |𝒰̂(h/k + β)|² dβ ≤ M Y L^{-A}`, `H = H'/L^{C₆} = Y/(x L^{C₆})`.

The quantifiers are those of `EndpointEnergyAt` (scale, `𝐭`, test, twist, cutoff, `k`, `h`),
with the fixed data and the configuration bundled. In [P], `B = C₆`; the joint residue weight
needs `B = C₆ + 1` (`[PUB-tex:0496–0500]`). -/
def ArcEnergyAt (d : ℕ) (B C₆ : ℝ) : Prop :=
  ∀ (D : FixedData) (m' : ℕ) (a₁ a₂ : ℝ), 0 < a₁ → a₁ ≤ a₂ →
    ∀ (Dψ : ℕ → ℝ) (Cσ c₁ c₂ A : ℝ), 0 < A →
    ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ I : Config d D x,
      ∀ Y : ℝ, x * Real.exp (2 * Real.log x ^ (0.39 : ℝ) - c₁) ≤ Y →
        Y ≤ x * Real.exp (c₂ * Real.log x ^ (0.46 : ℝ) * Real.log (Real.log x)) →
      ∀ t : I.𝔊.Index → ℕ, (∀ g, 1 ≤ t g ∧ t g ≤ m') →
        (∀ i : Fin I.𝔊.numSmall, t (Sum.inl i) = 1) →
      ∀ test : ((g : I.𝔊.Index) → Fin (t g) → ℕ) → ℂ, MarkTest I.𝔊 test →
      ∀ σ : ℝ, |σ| ≤ Real.log x ^ Cσ → ∀ ψ₁ : ℝ → ℂ, CutoffAt a₁ a₂ Dψ x ψ₁ →
      ∀ k : ℕ, 0 < k → (k : ℝ) ≤ Real.log x ^ B → ∀ h : ℤ,
        ∫ β in (-(x * Real.log x ^ C₆ / Y))..(x * Real.log x ^ C₆ / Y),
          ‖∑ᶠ w : ℕ, comparisonEndpoint D.q D.q₀ D.𝔞 x I.𝔊 I.S t test ψ₁ σ Y w *
            addChar (((h : ℝ) / (k : ℝ) + β) * (w : ℝ))‖ ^ 2 ≤
          M * Y * Real.log x ^ (-A)

/-- (cor:arc-energy-target) for all fixed exponents. -/
def ArcEnergy (d : ℕ) : Prop := ∀ B C₆ : ℝ, 0 < B → 0 < C₆ → ArcEnergyAt d B C₆

/-- **The arc energy from (cor:SM)** (`[P-06:0530–0553]`): "Apply the lemma to
`a_w = 𝒰(w) e(hw/k)`. The additive error is negligible by (cor:endpoint-squares). The Dirichlet
mean-square bound in Lemma 2.2 gives, on every dyadic time interval of length `R`,
`Y⁻² ∫_{R ≤ |t| ≤ 2R} |P_a(t)|² dt ≪ L^{C_5+1} (1 + R/Y)`. For `T_0 = LY/H`, the tail in
(cor:local-mellin) is thus at most `Y L^{C_5+1} ∑_{r ≥ 0} (2^r L)^{-j} (1 + 2^r L/H)`, which is as
small as required on choosing `j` last. It remains to prove, for every fixed `A' > 0`, (cor:SM)
… Notice that the first term in (cor:local-mellin) is `Y` times the integral in (cor:SM)".

**This is the place where (cor:SM) is used**: `ArcEnergyAt d B C₆` uses
`EndpointEnergyAt d B (C₆ + 1)` (`T_0 = L Y / H = x L^{C₆ + 1}`). The Dirichlet mean square is
`Classical.integral_normSq_dirichletPolynomial_le`. -/
def ArcEnergyLink (d : ℕ) : Prop :=
  LocalMellin → EndpointSquares d → EndpointEnergy d → ArcEnergy d

/-- **The bound for (cor:comparison-sum)** (`[P-06:0396–0400, 0476–0486]`): for tests `b₁, b₂` on
the free labels of the two blocks in cells `[U_i, eU_i]`, the first endpoint `𝒰` with cutoff
`ψ_1`, twist `|σ| ≤ L^{Cσ}` and the additive character `e(jw/H)` of the residue condition
(`[PUB-tex:0492–0495]`), and the second endpoint `𝒱` with cutoff `ψ_2`, at the scale
`Y = x U₁ U₂`:

`|E b₁(D_A) b₂(D_B) ∑_w 𝒰(w) e(jw/H) 𝒱(w + D_A D_B)| ≤ M Y L^{-A}`.

Order: the fixed data, `m₀`, the support and the derivative exponents of the cutoffs, the exponent
`Cσ`, the saving; then `M`, `x₀`; then everything else. `1 ≤ U_i` makes the right side
nonnegative. -/
def BilinearBound (d H : ℕ) : Prop :=
  0 < H → ∀ (D : FixedData) (m₀ : ℕ) (a₁ a₂ : ℝ), 0 < a₁ → a₁ ≤ a₂ →
    ∀ (Dψ : ℕ → ℝ) (Cσ A : ℝ), 0 < A →
    ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ I : Config d D x,
      ∀ (J : ℕ) (C : Fin I.𝔊.numBig → Finset (Fin J)), IsComparison I.blocks m₀ C →
      ∀ (b₁ b₂ : AuxList (groupFamily I.𝔊).big C → ℂ) (U₁ U₂ : ℝ), 1 ≤ U₁ → 1 ≤ U₂ →
        BlockTest I.blocks true C b₁ U₁ → BlockTest I.blocks false C b₂ U₂ →
      ∀ test₁ test₂ : ((g : I.𝔊.Index) → Fin (markCount I.𝔊 C g) → ℕ) → ℂ,
        MarkTest I.𝔊 test₁ → MarkTest I.𝔊 test₂ →
      ∀ σ : ℝ, |σ| ≤ Real.log x ^ Cσ →
      ∀ ψ₁ ψ₂ : ℝ → ℂ, CutoffAt a₁ a₂ Dψ x ψ₁ → CutoffAt a₁ a₂ Dψ x ψ₂ → ∀ j : ℕ,
        ‖bilinearSum (groupFamily I.𝔊).big C (fun r => b₁ r * b₂ r)
            (fun w => comparisonEndpoint D.q D.q₀ D.𝔞 x I.𝔊 I.S (markCount I.𝔊 C) test₁ ψ₁ σ
              (x * U₁ * U₂) w * addChar ((j : ℝ) * (w : ℝ) / (H : ℝ)))
            (secondEndpoint D.q₀ I.𝔊 (markCount I.𝔊 C) test₂ I.G ψ₂ (x * U₁ * U₂))‖ ≤
          M * (x * U₁ * U₂) * Real.log x ^ (-A)

/-- **Parseval, the minor arcs and the major arcs** (`[P-06:0476–0486]`): "Parseval and
(cor:endpoint-squares) handle the complement of `𝔐_H`. On its `O(L^{2C_6})` arcs, Cauchy and the
global energy of `𝒱` reduce the problem to (cor:arc-energy-target)".

`∑_w 𝒰(w) 𝒱(w + D) = ∫_0^1 𝒰̂(θ) 𝒱̂(-θ) e(θD) dθ`, so the bilinear sum is
`∫_0^1 𝒰̂(θ + j/H) 𝒱̂(-θ) 𝔪(θ) dθ`. Order of the choices inside: the saving `A`; `C₅` from
(cor:endpoint-squares); the minor-arc saving `A + C₅` and `C₆` from `MultiplierMinor`; the
precision `2A + 4C₆ + C₅` of the arc energy, used at the denominators `kH ≤ L^{C₆ + 1}`
(`ArcEnergyAt d (C₆ + 1) C₆`): "The shifted denominators are at most `Hk`"
(`[PUB-tex:0497–0498]`). -/
def CircleLink (d H : ℕ) : Prop :=
  MultiplierMinor → ArcEnergy d → EndpointSquares d → BilinearBound d H

/-- **Cutoffs, the Fourier inversion in logarithmic size and the residue partition**
(`[P-06:0391–0415]`, `[PUB-tex:0487–0495]`): "Insert fixed smooth cutoffs at scale `Y` at both
endpoints. Fourier inversion in logarithmic size separates `Ψ(w/(x D_A D_B))/w` as in
(cor:insertion-separation). After a factor `1/Y`, it is enough to estimate combinations of
(cor:comparison-sum) … These estimates also bound the separated Fourier tails absolutely". With
the weight: "Partition each free tuple by its residue modulo `H`. These bounded tests preserve the
endpoint hypotheses. On each part the shift `d mod H` is fixed, and (eq:B-shift) leaves a fixed
residue condition on the first endpoint. For such a condition,
`1_{n ≡ c (H)} = (1/H) ∑_{j=0}^{H-1} e(j(n-c)/H)`."

For a general joint weight, `w ↦ 𝔅(w, w + d)` is a function on `ℤ/H` with values in `[0,1]`, a
combination of the `H` characters `e(jw/H)` with coefficients of modulus at most one. The tests
`b_i(r) (U_i/D_i) D_i^{-iζ} 1_{D_i ≡ a (H)}` are again `BlockTest`s. -/
def SeparationLink (d H : ℕ) (𝔅 : JointResidueWeight H) : Prop :=
  BilinearBound d H → EndpointSquares d → ComparisonCorrelationBound d H 𝔅

/-! ### What remains to be proved -/

/-- **The leaves of [P] §6 with a joint residue weight**: everything that
`TwoSidedProof/Assembly.lean` assumes, for `d` slots and the weight `𝔅` modulo `H`. Every field is
a closed proposition claimed to be true as stated; `twoSidedReduction_of_leaves` derives
`TwoSidedReduction d H 𝔅` from them for `0 < H`. -/
structure Leaves (d H : ℕ) (𝔅 : JointResidueWeight H) : Prop where
  /-- `[P-06:0079–0082]`: `F_x` is bounded on power ranges (Mertens for `C_x` and `V_i`). -/
  corePower : MertensReciprocal → CorePowerBounded d
  /-- `[P-06:0044–0053]`, (cor:marked-bound). -/
  markedBound : MarkedBound
  /-- `[P-06:0082–0084]`: `F_x(pn) = F_x(n)` for active primes `p`. -/
  coreInvariance : CoreInvariance d
  /-- `[P-06:0023]`: the big groups are prime intervals. -/
  bigIntervals : BigIntervals
  /-- `[P-06:0211]`: two balanced blocks of big groups. -/
  splitBalanced : HalfSplitBalanced
  /-- `[P-06:0262–0285]`, (cor:list-norm). -/
  endpointNorms : EndpointNormsLink d
  /-- `[P-06:0287–0316]`, (cor:insertion-separation) and the transferred estimate. -/
  insertion : InsertionLink d H 𝔅
  /-- `[P-06:0318–0370]`, the raw pattern. -/
  rawStripping : RawStrippingLink d H 𝔅
  /-- `[P-06:0318–0370]`, the comparison patterns. -/
  comparisonStripping : ComparisonStrippingLink d H 𝔅
  /-- `[P-06:0402–0410]`, (cor:endpoint-squares). -/
  endpointSquares : EndpointSquaresLink d
  /-- `[P-06:0431–0453]`, the elementary bilinear Fourier estimate. -/
  bilinearFourier : BilinearFourier
  /-- `[P-06:0417–0474]`, (cor:bilinear-multiplier) and (cor:major-arcs). -/
  multiplier : MultiplierLink
  /-- `[P-06:0488–0528]`, Lemma (local Mellin energy). -/
  localMellin : LocalMellin
  /-- `[P-06:0530–0553]`: (cor:arc-energy-target) from (cor:SM). -/
  arcEnergy : ArcEnergyLink d
  /-- `[P-06:0476–0486]`: Parseval, minor and major arcs. -/
  circle : CircleLink d H
  /-- `[P-06:0391–0415]`, `[PUB-tex:0487–0495]`: cutoffs, Fourier inversion, residues. -/
  separation : SeparationLink d H 𝔅
  /-- `[P-06:0381–0391]`: the expansion of the two kernels. -/
  kernelExpansion : KernelExpansionLink d H 𝔅

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
