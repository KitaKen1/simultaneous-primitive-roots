module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Open
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.SlotBound
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.WeightBound
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.ModelBoundsProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.ModelVarianceProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.ProgressionSlotsProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.PresieveProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.SiftedDecompositionProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.ProxyProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.StripProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.CoinTools
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.CoinProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.CandidateAdmissibleProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.AllocationIdentityProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.SquareExceptionsProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.AllocationProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.VarianceProof

/-!
# The reduction of [P] §7 for one slot

All seventeen fields of `ExtractionOpenLeaves 1 H b q q₀` (`Extraction/Open.lean`) are theorems of
this directory. Sixteen of the seventeen fields of `ExtractionOpenLeaves 1 H b q q₀` (`Extraction/Open.lean`) are
theorems of this directory:

| field | theorem | file |
|---|---|---|
| `slotBounded` | `slotBounded_one` | `SlotBound.lean` |
| `weightBounded` | `arrayWeightBounded_of_mertensReciprocal` | `WeightBound.lean` |
| `modelBounds` | `modelBounds_of_mertensReciprocal` | `ModelBoundsProof.lean` |
| `modelVariance` | `modelVariance` | `ModelVarianceProof.lean` |
| `progressionSlots`, `progressionUnit`, `progressionUnitOne` | `progressionSlots`, `progressionUnit`, `progressionUnitOne` | `ProgressionSlotsProof.lean` |
| `presieve` | `presieveLink` | `PresieveProof.lean` |
| `sifted` | `siftedDecomposition` | `SiftedDecompositionProof.lean` |
| `proxy` | `proxyLink` | `ProxyProof.lean` |
| `strip` | `stripLink` | `StripProof.lean` |
| `candidateAdmissible` | `candidateAdmissible` | `CandidateAdmissibleProof.lean` |
| `allocationIdentity` | `allocationIdentity` | `AllocationIdentityProof.lean` |
| `squareExceptions` | `squareExceptions` | `SquareExceptionsProof.lean` |
| `allocation` | `allocationLink` | `AllocationProof.lean` |
| `variance` | `varianceLink` | `VarianceProof.lean` |

The seventeenth is the coin step `coin : CoinLink q₀` (`[P-07:0388–0514]`): `coinLink`
(`CoinProof.lean`; first clause in `CoinTools.lean`). Hence `primeExtractionReduction_one :
PrimeExtractionReduction 1` with no hypothesis, at the dampings `q = q₀ = 1/2`. The dependence on
the coin step is recorded by:

* `primeExtractionReduction_one_of_coin : CoinLink (1/2) → PrimeExtractionReduction 1`;
* `primeExtractionReduction_one_of_coinMass`: the same from the second clause of the coin estimate
  (`Coin.CoinFailureMass (1/2)`) alone.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

/-- **All the open leaves of [P] §7 for one slot, from the coin step**, for every modulus `H ≥ 1`,
every reduced class `b` and all dampings `q, q₀ ∈ (0, 1)`. -/
theorem extractionOpenLeaves_one_of_coin {H b : ℕ} (hH : 0 < H) (hb : b.Coprime H) {q q₀ : ℝ}
    (hq : 0 < q) (hq1 : q < 1) (hq₀ : 0 < q₀) (hq₀1 : q₀ < 1) (hcoin : CoinLink q₀) :
    ExtractionOpenLeaves 1 H b q q₀ where
  slotBounded := fun _ => slotBounded_one
  weightBounded := arrayWeightBounded_of_mertensReciprocal hq.le hq1
  modelBounds := modelBounds_of_mertensReciprocal hq.le hq1
  modelVariance := modelVariance q
  progressionSlots := progressionSlots 1 H b hH hb hq hq1
  progressionUnit := progressionUnit H b hH hb hq hq1
  progressionUnitOne := progressionUnitOne hq hq1
  presieve := presieveLink 1 H b hH hq.le
  sifted := siftedDecomposition
  proxy := proxyLink 1 H b hH hb hq hq1
  strip := stripLink
  coin := hcoin
  candidateAdmissible := candidateAdmissible
  allocationIdentity := allocationIdentity
  squareExceptions := squareExceptions
  allocation := allocationLink 1 H b hb hq hq1 hq₀ hq₀1
  variance := varianceLink q

/-- **`PrimeExtractionReduction 1` from the coin step** at the dampings `q = q₀ = 1/2`. -/
theorem primeExtractionReduction_one_of_coin (hcoin : CoinLink (1 / 2)) :
    PrimeExtractionReduction 1 :=
  primeExtractionReduction_one_of_open (q := 1 / 2) (q₀ := 1 / 2) fun _ _ hH hb =>
    extractionOpenLeaves_one_of_coin hH hb (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) hcoin

/-- **`PrimeExtractionReduction 1` from the second clause of the coin estimate** at `q₀ = 1/2`. -/
theorem primeExtractionReduction_one_of_coinMass
    (hmass : RoughCounts → MertensReciprocal → MertensProduct → Coin.CoinFailureMass (1 / 2)) :
    PrimeExtractionReduction 1 :=
  primeExtractionReduction_one_of_coin fun hR hM1 hM2 =>
    Coin.coinFailure_of_mass hM1 (by norm_num) (by norm_num) (hmass hR hM1 hM2)

/-- **The reduction of [P] §7 for one slot**, with no hypothesis. -/
theorem primeExtractionReduction_one : PrimeExtractionReduction 1 :=
  primeExtractionReduction_one_of_coin (coinLink (by norm_num) (by norm_num))

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
