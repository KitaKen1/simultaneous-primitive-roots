module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.Open
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.OmegaMomentProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.DivisorModelProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.LowMainTermProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.LowFrequencyProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ExtractedCoefficientProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.PartialMarkedBoundProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.CoefficientBoundProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ExtractionErrorProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ExceptionalCountProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.SparseBoundProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.LongPrimeSavingProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.TupleProductProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.TupleSeparationProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ModelPolynomialsProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ConstantProductProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.ConstantSeparationProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.SmoothSum
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.SlotMassAll

/-!
# The endpoint estimate (cor:SM) from the classical inputs of [P] §2

All seventeen fields of `EndpointOpenLeaves d` (`EndpointProof/Open.lean`) are theorems of this
directory, as are the sum–integral comparison `smoothProgressionSum` (`EndpointProof/SmoothSum.lean`)
and the bound `slotMassBounded` for `C_x` with any number of slots
(`EndpointProof/SlotMassAll.lean`). Hence (cor:SM) follows from the four classical inputs that are
not theorems of the module part of the project:

* `endpointOpenLeaves d : EndpointOpenLeaves d`;
* `endpointEnergy_succ_of_classical`: `EndpointEnergy (d + 1)` from Mertens' estimate for `∑ 1/p`
  ([P] Lemma 2.1), the long prime polynomial ([P] Lemma 2.3), the logarithmic phases on
  progressions ([P] Lemma 2.4) and the moderate phases ((eq:moderate-phase));
* `endpointEnergy_one_of_classical`: the case `d + 1 = 1` used by the main theorem.

The four inputs are supplied in the final layer from the vendored libraries
(`OAI.JointDickman.primeReciprocalMertensInput`, `ArtinPrimitiveRoots.TypeII.PP.prime_polynomial`,
`ArtinPrimitiveRoots.TypeII.PP.log_phase`, `ArtinPrimitiveRoots.TypeII.PD.moderate_phase`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

/-- **The seventeen leaves of (cor:SM)** left open in `EndpointProof/Open.lean`, all proved. -/
theorem endpointOpenLeaves (d : ℕ) : EndpointOpenLeaves d where
  omegaMoment := omegaMoment
  divisorModel := divisorModel
  lowMainTerm := lowMainTerm
  lowFrequency := lowFrequency d
  extractedCoefficient := extractedCoefficient d
  markedBound := partialMarkedBound
  coefficientBound := coefficientBound d
  extractionError := extractionError d
  exceptionalCount := exceptionalCount
  sparseBound := sparseBound
  longPrimeSaving := longPrimeSaving
  tupleProduct := tupleProduct
  tupleSeparation := tupleSeparation d
  modelMedium := modelMedium
  modelHigh := modelHigh
  constantProduct := constantProduct d
  constantSeparation := constantSeparation d

/-- **(cor:SM) for `d + 1` slots from the classical inputs** of [P] §2. -/
theorem endpointEnergy_succ_of_classical (d : ℕ) (hM : MertensReciprocal)
    (hLP : LongPrimePolynomial) (hLog : LogPhase) (hMP : ModeratePhase) :
    EndpointEnergy (d + 1) :=
  endpointEnergy_succ_of_open
    { mertens := hM, smoothSum := smoothProgressionSum, longPrime := hLP, logPhase := hLog,
      moderatePhase := hMP }
    (slotMassBounded (d + 1)) (endpointOpenLeaves d)

/-- **`EndpointEnergy 1` from the classical inputs** of [P] §2. -/
theorem endpointEnergy_one_of_classical (hM : MertensReciprocal) (hLP : LongPrimePolynomial)
    (hLog : LogPhase) (hMP : ModeratePhase) : EndpointEnergy 1 :=
  endpointEnergy_succ_of_classical 0 hM hLP hLog hMP

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
