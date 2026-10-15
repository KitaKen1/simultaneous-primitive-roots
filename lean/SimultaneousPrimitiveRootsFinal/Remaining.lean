import SimultaneousPrimitiveRootsFinal.Classical.SiegelWalfiszPrimes
import SimultaneousPrimitiveRootsFinal.Classical.MertensBridge
import SimultaneousPrimitiveRootsFinal.Classical.BlockSieveBridge
import SimultaneousPrimitiveRootsFinal.Classical.RoughCountsBridge
import SimultaneousPrimitiveRootsFinal.Classical.ModeratePhaseBridge
import SimultaneousPrimitiveRootsFinal.Classical.PrimePhaseBridge
import SimultaneousPrimitiveRootsFinal.ExternalHecke
import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.Complete
import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.Complete
import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Complete
import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Complete
import SimultaneousPrimitiveRootsFinal.TypeII.MarkedTransferReduction
import SimultaneousPrimitiveRootsFinal.TypeII.LongCoefficientReduction
import SimultaneousPrimitiveRoots.Unconditional.RemainingInputs

/-!
# `MainClaim` from the open inputs, in the final (non-module) layer

`Unconditional/RemainingInputs.lean` composes everything proved in the module tree into
`mainClaim_of_remainingInputs'`. Some inputs are proved in files that import non-module libraries
(the vendored OpenAI files, class field theory, the vendored formalization of [A]) and so cannot be
discharged there. This file discharges them one by one; `mainClaim_of_openInputs` is the current
statement of what is left. Every remaining hypothesis is a `def … : Prop`; none is an axiom.

Discharged so far (the five classical inputs of [P] §2 on the route):

* `Supply.SiegelWalfiszPrimeCounting`: it is the statement of
  `Classical.siegelWalfisz_primeCounting` (`Classical/SiegelWalfiszPrimes.lean`, from the vendored
  `OAI.LargePrimeGaps.siegelWalfisz`).
* `Supply.MertensReciprocal`, `Supply.MertensProduct`: `Classical/MertensBridge.lean`, from the
  vendored `OAI.JointDickman.primeReciprocalMertensInput`, `primeProductMertensInput`.
* `Supply.RoughCounts`: `Classical/RoughCountsBridge.lean`, from the vendored
  `ArtinPrimitiveRoots.TypeII.PD.rough_counts`.
* `Supply.BlockSieve`: `Classical/BlockSieveBridge.lean`, from the vendored
  `ArtinPrimitiveRoots.Sieve.lem_block`.

Discharged on 2026-10-13: the endpoint energy bound (cor:SM), `Supply.EndpointEnergy 1`. The module
tree proves it from four classical inputs of [P] §2
(`Supply.EndpointProof.endpointEnergy_one_of_classical`, `Supply/EndpointProof/Complete.lean`):
Mertens' estimate (above) and

* `Supply.EndpointProof.ModeratePhase`: `Classical/ModeratePhaseBridge.lean`, from the vendored
  `ArtinPrimitiveRoots.TypeII.PD.moderate_phase`;
* `Supply.EndpointProof.LongPrimePolynomial`, `Supply.EndpointProof.LogPhase`:
  `Classical/PrimePhaseBridge.lean`, from the vendored
  `ArtinPrimitiveRoots.TypeII.PP.prime_polynomial` and `ArtinPrimitiveRoots.TypeII.PP.log_phase`.

Also discharged on 2026-10-13: the reduction of [P] §6 with the fixed class,
`Supply.TwoSidedReductionFixedClass 1`, a theorem of the module tree
(`Supply.TwoSidedProof.twoSidedReductionFixedClass_one`, `Supply/TwoSidedProof/Complete.lean`).

The Hecke side is discharged as well (2026-10-13): the zero-free factorization of `ζ_L`,
`CyclotomicAbelianZetaFactorization (10⁻¹ ^ 6)`, is the theorem `cyclotomicAbelianZetaFactorization`
of `ExternalHecke.lean`, from the vendored formalization of [A]
(`ArtinPrimitiveRoots.HeckeBoundary.thm_hecke_zero_free` and
`ArtinPrimitiveRoots.Splitting.upstairs_rhp_euler_identity`). What is left is on the supply side.

State at the end of 2026-10-13:

* [S] Theorem 3.5 is a theorem of the module tree (`Transference.Proof35.localTransference`,
  `Transference/Proof35/Complete.lean`).
* The reduction of [P] §7 is a theorem of the module tree as well (2026-10-14, after the coin step:
  `Supply.Extraction.primeExtractionReduction_one`, `Supply/Extraction/Complete.lean`).
* The two Type II statements follow from verbatim copies of the statements of three vendored
  theorems (`TypeII/MarkedTransferReduction.lean`, `TypeII/LongCoefficientReduction.lean`); the
  copies are discharged in `TypeII/MarkedTransferBridge.lean` and
  `TypeII/LongCoefficientBridge.lean`, which import the vendored Type II closure.
-/

noncomputable section

namespace SimultaneousPrimitiveRoots.Unconditional

/-- **Siegel–Walfisz in the prime-counting form of [P] Lemma 2.1 / [S] Theorem 2.2** is a theorem:
the supply-side hypothesis `Supply.SiegelWalfiszPrimeCounting` holds. -/
theorem Supply.siegelWalfiszPrimeCounting : Supply.SiegelWalfiszPrimeCounting :=
  SimultaneousPrimitiveRoots.Classical.siegelWalfisz_primeCounting

/-- **The endpoint energy bound (cor:SM)** is a theorem: the supply-side hypothesis
`Supply.EndpointEnergy 1` holds. -/
theorem Supply.endpointEnergy_one : Supply.EndpointEnergy 1 :=
  Supply.EndpointProof.endpointEnergy_one_of_classical Supply.mertensReciprocalEstimate
    Supply.EndpointProof.longPrimePolynomial Supply.EndpointProof.logPhase
    Supply.EndpointProof.moderatePhase

/-- **`MainClaim` from the supply-side statements of the papers that are still hypotheses**: the
reduction of [P] §7 and the two Type II statements. Everything else on the route is a theorem. -/
theorem mainClaim_of_supplyInputs
    (hE : Supply.PrimeExtractionReduction 1)
    (hII : Supply.MarkedTypeIICoefficientForm) (h52 : Supply.PrimeMinusRoughLongCoefficient) :
    MainClaim :=
  mainClaim_of_remainingInputs' hE Supply.TwoSidedProof.twoSidedReductionFixedClass_one hII h52
    Transference.Proof35.localTransference Supply.endpointEnergy_one
    Supply.siegelWalfiszPrimeCounting Supply.mertensReciprocalEstimate Supply.mertensProductEstimate
    Supply.roughCounts Supply.blockSieve cyclotomicAbelianZetaFactorization

/-- **`MainClaim` from what is still open**: no statement of the papers, only the statements of
three theorems of the vendored formalization of [A] (the marked coefficient transfer and the low-
and high-frequency estimates for the rough coefficient). They become theorems here as soon as the
vendored Type II closure is built (`TypeII/MarkedTransferBridge.lean`,
`TypeII/LongCoefficientBridge.lean`). -/
theorem mainClaim_of_openInputs
    (hV₁ : VendoredMarkedCoefficientTransfer) (hV₂ : VendoredRoughLowFrequency)
    (hV₃ : VendoredRoughHighFrequency) : MainClaim :=
  mainClaim_of_supplyInputs Supply.Extraction.primeExtractionReduction_one
    (markedTypeIICoefficientForm_of_vendored hV₁)
    (primeMinusRoughLongCoefficient_of_vendored hV₂ hV₃)

end SimultaneousPrimitiveRoots.Unconditional
