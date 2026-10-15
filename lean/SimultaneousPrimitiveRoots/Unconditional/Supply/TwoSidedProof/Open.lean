module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.Assembly
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.Bridge
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.CoreInvariance
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.MarkedBound

/-!
# The open leaves of [P] §6 with a joint residue weight

`Leaves d H 𝔅` (`TwoSidedProof/Statements.lean`) has seventeen fields. Four of them are proved in
this directory:

* `markedBound`, by `markedBound` (`TwoSidedProof/MarkedBound.lean`, (cor:marked-bound));
* `coreInvariance`, by `coreInvariance d` (`TwoSidedProof/CoreInvariance.lean`,
  `F_x(pn) = F_x(n)`);
* `bigIntervals`, by `bigIntervals`, and `splitBalanced`, by `halfSplit_balanced`
  (`TwoSidedProof/Bridge.lean`).

`OpenLeaves d H 𝔅` is the list of the thirteen that remain, and
`twoSidedReductionFixedClass_one_of_open` is the reduction of `TwoSidedReductionFixedClass 1` to
them. Every field is a closed proposition claimed to be true as stated (the hypothesis `0 < H` is
inside the statements that need it).

The exact identity `pairMarkFree_physOp_markFree` of `TwoSidedProof/PairingExpansion.lean` (the
pairing of two mark-free vectors as an edge sum) is proved for the use of `insertion`; it is not a
hypothesis of the chain.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

noncomputable section

/-- **What remains to be proved** for `TwoSidedReduction d H 𝔅`: the thirteen leaves and links of
[P] §6 with a joint residue weight that are not proved in this directory. -/
structure OpenLeaves (d H : ℕ) (𝔅 : JointResidueWeight H) : Prop where
  /-- `[P-06:0079–0082]`: `F_x` is bounded on power ranges (Mertens for `C_x` and `V_i`). -/
  corePower : MertensReciprocal → CorePowerBounded d
  /-- `[P-06:0262–0285]`, (cor:list-norm): the two endpoint norms. -/
  endpointNorms : EndpointNormsLink d
  /-- `[P-06:0287–0316]`, (cor:insertion-separation) and the transferred estimate. -/
  insertion : InsertionLink d H 𝔅
  /-- `[P-06:0318–0370]`: removal of the shared labels, the raw pattern. -/
  rawStripping : RawStrippingLink d H 𝔅
  /-- `[P-06:0318–0370]`: removal of the shared labels, the comparison patterns. -/
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

/-- The open leaves give all the leaves. -/
theorem OpenLeaves.toLeaves {d H : ℕ} {𝔅 : JointResidueWeight H} (L : OpenLeaves d H 𝔅) :
    Leaves d H 𝔅 where
  corePower := L.corePower
  markedBound := markedBound
  coreInvariance := coreInvariance d
  bigIntervals := bigIntervals
  splitBalanced := halfSplit_balanced
  endpointNorms := L.endpointNorms
  insertion := L.insertion
  rawStripping := L.rawStripping
  comparisonStripping := L.comparisonStripping
  endpointSquares := L.endpointSquares
  bilinearFourier := L.bilinearFourier
  multiplier := L.multiplier
  localMellin := L.localMellin
  arcEnergy := L.arcEnergy
  circle := L.circle
  separation := L.separation
  kernelExpansion := L.kernelExpansion

/-- **The reduction for one weight from the open leaves.** -/
theorem twoSidedReduction_of_open {d H : ℕ} {𝔅 : JointResidueWeight H} (hH : 0 < H)
    (L : OpenLeaves d H 𝔅) : TwoSidedReduction d H 𝔅 :=
  twoSidedReduction_of_leaves hH L.toLeaves

/-- **`TwoSidedReductionFixedClass 1` from the thirteen open leaves**, for the class weights
`𝓑_{H,b}` of all moduli `H ≥ 1` and reduced classes `b`. -/
theorem twoSidedReductionFixedClass_one_of_open
    (L : ∀ H b : ℕ, 0 < H → b.Coprime H → OpenLeaves 1 H (classWeight H b)) :
    TwoSidedReductionFixedClass 1 :=
  fun H b hH hb => twoSidedReduction_of_open hH (L H b hH hb)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
