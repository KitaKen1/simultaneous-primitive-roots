module

public import SimultaneousPrimitiveRoots.Unconditional.AbelianFactorization
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedReduction
public import SimultaneousPrimitiveRoots.Unconditional.Transference.KernelCosts
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Schur.Main
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Pairing.Main
public import SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction.Main
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Main

/-!
# `MainClaim` from the list of statements that are still unproved

This file composes what is proved so far into one theorem whose hypotheses are exactly the
statements of the unconditional route that remain open. It is bookkeeping: every hypothesis is a
`def … : Prop` stated elsewhere, none is an axiom, and the proof is a composition of proved
implications.

* Hecke side, one hypothesis: `CyclotomicAbelianZetaFactorization (10⁻⁶)`
  ([A, Theorem 1.2] with the Artin factorization, in Mathlib terms; `AbelianFactorization.lean`).
* Supply side (`Supply/`, `Transference/`): the two reductions ([P] §7 and §6 re-run with the fixed
  class), the marked Type II estimate in coefficient form and [P] Lemma 5.2, the graph inputs, the
  endpoint energy bound (cor:SM), and five classical inputs.

`mainClaim_of_remainingInputs` takes the graph inputs in the form of [P] Props 6.2 and 6.3;
`mainClaim_of_remainingInputs'` takes them in the form of the statements of [S]
(Theorem 3.5, Lemma 4.3 and the construction after it); [S] Lemma 3.4 and Corollary 3.11 are
proved (`Transference.physicalSchur`, `Transference.endpointPairing`) and are no longer hypotheses.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional

/-- **`MainClaim` from the statements that remain open**, with the graph inputs as
[P] Props 6.2 and 6.3. -/
theorem mainClaim_of_remainingInputs
    (hE : Supply.PrimeExtractionReduction 1) (hC : Supply.TwoSidedReductionFixedClass 1)
    (hII : Supply.MarkedTypeIICoefficientForm) (h52 : Supply.PrimeMinusRoughLongCoefficient)
    (h62 : Transference.GraphTransferInput) (h63 : Transference.IdealFamilyInput)
    (hSM : Supply.EndpointEnergy 1)
    (hSW : Supply.SiegelWalfiszPrimeCounting) (hM1 : Supply.MertensReciprocal)
    (hM2 : Supply.MertensProduct) (hR : Supply.RoughCounts) (hB : Supply.BlockSieve)
    (hZ : CyclotomicAbelianZetaFactorization ((10 : ℝ)⁻¹ ^ 6)) : MainClaim :=
  mainClaim_of_paperParameters_and_factorization
    (Supply.fixedClassLongPrimeStatistic_of_inputs hE hC hII h52 h62 h63 hSM hSW hM1 hM2 hR hB
      (by norm_num) (by norm_num))
    hZ

/-- **`MainClaim` from the statements that remain open**, with the graph inputs as the statements
of [S]: Theorem 3.5 (`LocalTransference`) is the only one left. Lemma 3.4, Corollary 3.11,
Lemma 4.3 (from Siegel–Walfisz) and the construction of Theorem 4.1 from Lemma 4.3 are the
theorems `Transference.physicalSchur`, `Transference.endpointPairing`,
`Transference.Comparison.comparisonKernelLemma_of_siegelWalfisz` and
`Transference.idealConstructionOfContract`. -/
theorem mainClaim_of_remainingInputs'
    (hE : Supply.PrimeExtractionReduction 1) (hC : Supply.TwoSidedReductionFixedClass 1)
    (hII : Supply.MarkedTypeIICoefficientForm) (h52 : Supply.PrimeMinusRoughLongCoefficient)
    (h35 : Transference.LocalTransference)
    (hSM : Supply.EndpointEnergy 1)
    (hSW : Supply.SiegelWalfiszPrimeCounting) (hM1 : Supply.MertensReciprocal)
    (hM2 : Supply.MertensProduct) (hR : Supply.RoughCounts) (hB : Supply.BlockSieve)
    (hZ : CyclotomicAbelianZetaFactorization ((10 : ℝ)⁻¹ ^ 6)) : MainClaim :=
  mainClaim_of_remainingInputs hE hC hII h52
    (Transference.graphTransferInput_of h35 Transference.endpointPairing Transference.physicalSchur)
    (Transference.idealFamilyInput_of_contract
      (Transference.Comparison.comparisonKernelLemma_of_siegelWalfisz hSW)
      Transference.idealConstructionOfContract)
    hSM hSW hM1 hM2 hR hB hZ

end SimultaneousPrimitiveRoots.Unconditional
