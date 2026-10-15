module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Assembly
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Leaves
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.CoreGrowth

/-!
# The open leaves of the prime extraction

`ExtractionLeaves d H b q q₀` (`Extraction/Statements.lean`) has nineteen fields. Two of them are
proved in this directory:

* `primeMass`, by `primeMassBound` (`Extraction/Leaves.lean`, Chebyshev's bound);
* `coreGrowth`, by `coreGrowth_of_mertensProduct` (`Extraction/CoreGrowth.lean`).

`ExtractionOpenLeaves d H b q q₀` is the list of the seventeen that remain, and
`primeExtractionReduction_one_of_open` is the reduction of `PrimeExtractionReduction 1` to them.
For `d = 1` the field `slotBounded` is proved by `slotBounded_one` (`Extraction/SlotBound.lean`),
so sixteen are open.
The statements are claimed for `0 < H`, `b.Coprime H`, `0 < q < 1`, `0 < q₀ < 1`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

noncomputable section

/-- **What remains to be proved** for `PrimeExtractionReductionAt d H b`: the seventeen leaves and
links of [P] §7 with the class that are not proved in this directory. -/
structure ExtractionOpenLeaves (d H b : ℕ) (q q₀ : ℝ) : Prop where
  /-- `[P-07:0016–0019]`: `C_x`, `f_x` bounded. -/
  slotBounded : MertensReciprocal → SlotBounded d
  /-- `[P-07:0043–0045]`: `𝒲` bounded. -/
  weightBounded : MertensReciprocal → ArrayWeightBounded q
  /-- `[P-07:0063–0075]`, (ext:model-bounds). -/
  modelBounds : MertensReciprocal → ModelBounds q
  /-- `[P-07:0641–0648]`, (ext:deweight-model). -/
  modelVariance : ModelBounds q → ModelVariance q
  /-- Lemma 7.2 with the class and the long-prime statistic, `[P-07:0077–0192]`. -/
  progressionSlots : MertensReciprocal → ProgressionSlots d H b q
  /-- Lemma 7.2 with the class, without tuple factors, `[P-07:0090, 0177–0178]`. -/
  progressionUnit : MertensReciprocal → ProgressionUnit H b q
  /-- Lemma 7.2 without class and without tuple factors. -/
  progressionUnitOne : MertensReciprocal → ProgressionUnit 1 1 q
  /-- The presieve step, `[P-07:0196–0228]`. -/
  presieve : PresieveLink d H b q
  /-- `[P-07:0230–0240]`: primes, tuples of primes, and squares. -/
  sifted : SiftedDecomposition
  /-- The Type II step, `[P-07:0249–0315]`. -/
  proxy : ProxyLink d H b q
  /-- The stripping step, `[P-07:0317–0386]`. -/
  strip : StripLink
  /-- The coin step, `[P-07:0388–0514]`. -/
  coin : CoinLink q₀
  /-- `[P-07:0319–0329, 0533–0535]`: candidate groups and active sets. -/
  candidateAdmissible : MertensReciprocal → CandidateAdmissible
  /-- `[P-07:0576–0594]`, (ext:allocation-identity). -/
  allocationIdentity : AllocationIdentity
  /-- `[P-07:0542–0557]`, (ext:candidate-square-count). -/
  squareExceptions : SquareExceptions
  /-- The allocation step, `[P-07:0518–0615]`. -/
  allocation : AllocationLink d H b q q₀
  /-- The variance step, `[P-07:0649–0670]`. -/
  variance : VarianceLink q

/-- The open leaves give all the leaves. -/
theorem ExtractionOpenLeaves.toLeaves {d H b : ℕ} {q q₀ : ℝ}
    (L : ExtractionOpenLeaves d H b q q₀) : ExtractionLeaves d H b q q₀ where
  slotBounded := L.slotBounded
  weightBounded := L.weightBounded
  primeMass := fun _ => primeMassBound
  modelBounds := L.modelBounds
  modelVariance := L.modelVariance
  progressionSlots := L.progressionSlots
  progressionUnit := L.progressionUnit
  progressionUnitOne := L.progressionUnitOne
  presieve := L.presieve
  sifted := L.sifted
  proxy := L.proxy
  strip := L.strip
  coin := L.coin
  candidateAdmissible := L.candidateAdmissible
  coreGrowth := coreGrowth_of_mertensProduct
  allocationIdentity := L.allocationIdentity
  squareExceptions := L.squareExceptions
  allocation := L.allocation
  variance := L.variance

/-- **The reduction for one class from the open leaves.** -/
theorem primeExtractionReductionAt_of_open {d H b : ℕ} {q q₀ : ℝ}
    (L : ExtractionOpenLeaves d H b q q₀) : PrimeExtractionReductionAt d H b :=
  primeExtractionReductionAt_of L.toLeaves

/-- **`PrimeExtractionReduction 1` from the seventeen open leaves**, at one choice of the
dampings `q, q₀` (for example `q = q₀ = 1/2`). -/
theorem primeExtractionReduction_one_of_open {q q₀ : ℝ}
    (L : ∀ H b : ℕ, 0 < H → b.Coprime H → ExtractionOpenLeaves 1 H b q q₀) :
    PrimeExtractionReduction 1 :=
  primeExtractionReduction_one_of fun H b hH hb => (L H b hH hb).toLeaves

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
