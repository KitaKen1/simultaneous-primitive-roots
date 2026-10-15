module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.Open
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.CorePower
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.EndpointNormsProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.InsertionProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.RawStrippingProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.ComparisonStrippingProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.EndpointSquaresProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.BilinearFourierProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.MultiplierProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.LocalMellinProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.ArcEnergyProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.CircleProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.SeparationProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.KernelExpansionProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.WeightBound

/-!
# The reduction of [P] §6 with a joint residue weight, for one slot

All thirteen fields of `OpenLeaves 1 H 𝔅` (`TwoSidedProof/Open.lean`) are theorems of this
directory:

| field | theorem | file |
|---|---|---|
| `corePower` | `corePowerBounded_one` (with `Extraction.arrayWeightBounded_all`) | `CorePower.lean` |
| `endpointNorms` | `endpointNormsLink` | `EndpointNormsProof.lean` |
| `insertion` | `insertionLink` | `InsertionProof.lean` |
| `rawStripping` | `rawStrippingLink` | `RawStrippingProof.lean` |
| `comparisonStripping` | `comparisonStrippingLink` | `ComparisonStrippingProof.lean` |
| `endpointSquares` | `endpointSquaresLink` | `EndpointSquaresProof.lean` |
| `bilinearFourier` | `bilinearFourier` | `BilinearFourierProof.lean` |
| `multiplier` | `multiplierLink` | `MultiplierProof.lean` |
| `localMellin` | `localMellin` | `LocalMellinProof.lean` |
| `arcEnergy` | `arcEnergyLink` | `ArcEnergyProof.lean` |
| `circle` | `circleLink` | `CircleProof.lean` |
| `separation` | `separationLink` | `SeparationProof.lean` |
| `kernelExpansion` | `kernelExpansionLink` | `KernelExpansionProof.lean` |

Hence `TwoSidedReduction 1 H 𝔅` for every modulus `H ≥ 1` and every joint residue weight `𝔅`
(`twoSidedReduction_one`), and in particular `TwoSidedReductionFixedClass 1`
(`twoSidedReductionFixedClass_one`): Theorem 6.1 of [P] with the class factor follows from
Proposition 6.2, Proposition 6.3, (cor:SM) and Mertens' theorem for reciprocals. Only
`corePower` is restricted to one slot.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

noncomputable section

/-- **All the open leaves of [P] §6 for one slot**, for every modulus and every joint residue
weight. -/
theorem openLeaves_one (H : ℕ) (𝔅 : JointResidueWeight H) : OpenLeaves 1 H 𝔅 where
  corePower := fun hM => corePowerBounded_one (Extraction.arrayWeightBounded_all hM)
  endpointNorms := endpointNormsLink 1
  insertion := insertionLink 1 H 𝔅
  rawStripping := rawStrippingLink 1 H 𝔅
  comparisonStripping := comparisonStrippingLink 1 H 𝔅
  endpointSquares := endpointSquaresLink 1
  bilinearFourier := bilinearFourier
  multiplier := multiplierLink
  localMellin := localMellin
  arcEnergy := arcEnergyLink 1
  circle := circleLink 1 H
  separation := separationLink 1 H 𝔅
  kernelExpansion := kernelExpansionLink 1 H 𝔅

/-- **The reduction of [P] §6 for one slot and one joint residue weight** modulo `H ≥ 1`. -/
theorem twoSidedReduction_one {H : ℕ} (hH : 0 < H) (𝔅 : JointResidueWeight H) :
    TwoSidedReduction 1 H 𝔅 :=
  twoSidedReduction_of_open hH (openLeaves_one H 𝔅)

/-- **`TwoSidedReductionFixedClass 1`**: the reduction of [P] §6 for the class weights
`𝓑_{H,b}` of all moduli `H ≥ 1` and reduced classes `b`, for one slot. -/
theorem twoSidedReductionFixedClass_one : TwoSidedReductionFixedClass 1 :=
  twoSidedReductionFixedClass_one_of_open fun H b _ _ => openLeaves_one H (classWeight H b)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
