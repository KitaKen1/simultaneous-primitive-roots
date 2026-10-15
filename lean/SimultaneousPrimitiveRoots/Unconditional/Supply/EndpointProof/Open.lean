module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.Assembly
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.SlotMass
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ScaleFacts
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ExtractSmall
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.PrimePowerNorm

/-!
# The open leaves of the endpoint estimate (cor:SM)

`EndpointLeaves d` (`EndpointProof/Statements.lean`) has twenty-one fields. Proved in this
directory:

* `scaleFacts`, by `scaleFacts` (`EndpointProof/ScaleFacts.lean`);
* `extractSmall`, by `extractSmallIdentity` (`EndpointProof/ExtractSmall.lean`), the identity
  (cor:extract-small);
* `primePowerNorm`, by `primePowerNorm` (`EndpointProof/PrimePowerNorm.lean`), the factorial
  coefficient estimate;
* `slotMass` for one slot (`d + 1 = 1`), by `slotMassBounded_one` (`EndpointProof/SlotMass.lean`).

`EndpointOpenLeaves d` lists the seventeen fields that remain (for `d + 1 ≥ 2` slots the bound
`SlotMassBounded (d + 1)` for `C_x` is a separate hypothesis of `endpointEnergy_succ_of_open`).

* `endpointEnergy_succ_of_open`: `EndpointEnergy (d + 1)` from the classical inputs, the bound for
  `C_x` and the open leaves;
* `endpointEnergy_one_of_open`: **`EndpointEnergy 1`** from the classical inputs and the seventeen
  open leaves at `d = 0`.

The classical inputs (`EndpointClassicalInputs`, `EndpointProof/ClassicalInputs.lean`) are Mertens'
estimate, the first-order sum–integral comparison on a progression, and [P] Lemmas 2.3, 2.4 and
(eq:moderate-phase); the two mean-value theorems of Lemma 2.2 are theorems of the project
(`Unconditional/Classical/DirichletMeanSquare.lean`), and the first of them is used in the
assembly.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

noncomputable section

/-- **What remains to be proved** for (cor:SM) with `d + 1` slots: the seventeen leaves and links
of `[P-06:0555–0925]` that are not proved in this directory. -/
structure EndpointOpenLeaves (d : ℕ) : Prop where
  /-- (cor:omega-moment), `[P-06:0621–0630]`. -/
  omegaMoment : MertensReciprocal → OmegaMoment
  /-- Lemma `lem:divisor-model`, `[P-06:0565–0633]`. -/
  divisorModel : MertensReciprocal → OmegaMoment → DivisorModel
  /-- (cor:low-main-term), `[P-06:0652–0667]`. -/
  lowMainTerm : SmoothProgressionSum → LowMainTerm
  /-- The low-frequency step, `[P-06:0646–0679]`. -/
  lowFrequency : DivisorModel → LowMainTerm → SlotMassBounded (d + 1) →
    LowFrequencyBound (d + 1)
  /-- (cor:u-coefficient) and the constant coefficient, `[P-06:0692–0715]`. -/
  extractedCoefficient : ExtractSmallIdentity → ExtractedCoefficientIdentity d
  /-- (cor:marked-bound) with marks removed, `[P-06:0044–0053]`. -/
  markedBound : PartialMarkedBound
  /-- `[P-06:0697–0698, 0712–0713]`. -/
  coefficientBound : MertensReciprocal → PartialMarkedBound → CoefficientBound d
  /-- The square exceptions, `[P-06:0692–0703]`. -/
  extractionError : ExtractedCoefficientIdentity d → MertensReciprocal → PartialMarkedBound →
    ExtractionErrorBound d
  /-- (cor:exceptional-count), `[P-06:0774–0801]`. -/
  exceptionalCount : PrimePowerNorm → ExceptionalCount
  /-- (cor:sparse-bound), `[P-06:0803–0832]`. -/
  sparseBound : LogPhase → ModeratePhase → SparseBound
  /-- (cor:long-prime-saving), `[P-06:0836–0847]`. -/
  longPrimeSaving : LongPrimePolynomial → LongPrimeSaving
  /-- The tuple products, `[P-06:0763–0772, 0848–0858]`. -/
  tupleProduct : ExceptionalCount → SparseBound → LongPrimeSaving → TupleProductBound
  /-- The separation of the tuple part, `[P-06:0717–0737]`. -/
  tupleSeparation : CoefficientBound d → TupleProductBound → TupleEnergy d
  /-- (cor:constant-medium), `[P-06:0878–0893]`. -/
  modelMedium : ModeratePhase → ModelPolynomialMedium
  /-- (cor:constant-high), `[P-06:0903–0912]`. -/
  modelHigh : LogPhase → ModelPolynomialHigh
  /-- The constant products, `[P-06:0763–0772, 0860–0925]`. -/
  constantProduct : CoefficientBound d → ExceptionalCount → DivisorModel →
    ModelPolynomialMedium → ModelPolynomialHigh → ConstantProductBound d
  /-- The separation of the constant part, `[P-06:0717–0737]`. -/
  constantSeparation : CoefficientBound d → ConstantProductBound d → ConstantEnergy d

/-- The open leaves, the bound for `C_x` and the proved leaves give all the leaves. -/
theorem EndpointOpenLeaves.toLeaves {d : ℕ} (L : EndpointOpenLeaves d)
    (hS : SlotMassBounded (d + 1)) : EndpointLeaves d where
  omegaMoment := L.omegaMoment
  divisorModel := L.divisorModel
  lowMainTerm := L.lowMainTerm
  slotMass := fun _ => hS
  lowFrequency := L.lowFrequency
  scaleFacts := scaleFacts
  extractSmall := extractSmallIdentity
  extractedCoefficient := L.extractedCoefficient
  markedBound := L.markedBound
  coefficientBound := L.coefficientBound
  extractionError := L.extractionError
  primePowerNorm := primePowerNorm
  exceptionalCount := L.exceptionalCount
  sparseBound := L.sparseBound
  longPrimeSaving := L.longPrimeSaving
  tupleProduct := L.tupleProduct
  tupleSeparation := L.tupleSeparation
  modelMedium := L.modelMedium
  modelHigh := L.modelHigh
  constantProduct := L.constantProduct
  constantSeparation := L.constantSeparation

/-- **(cor:SM) for `d + 1` slots from the open leaves**, the classical inputs and the bound for
`C_x`. -/
theorem endpointEnergy_succ_of_open {d : ℕ} (I : EndpointClassicalInputs)
    (hS : SlotMassBounded (d + 1)) (L : EndpointOpenLeaves d) : EndpointEnergy (d + 1) :=
  endpointEnergy_succ_of_leaves I (L.toLeaves hS)

/-- **`EndpointEnergy 1` from the open leaves** and the classical inputs. -/
theorem endpointEnergy_one_of_open (I : EndpointClassicalInputs) (L : EndpointOpenLeaves 0) :
    EndpointEnergy 1 :=
  endpointEnergy_succ_of_open (d := 0) I slotMassBounded_one L

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
