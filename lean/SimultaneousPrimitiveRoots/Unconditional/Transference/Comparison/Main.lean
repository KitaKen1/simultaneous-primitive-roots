module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Assembly
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Dyadic
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.PhaseBilinear
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.CharacterCell
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.KernelNorm
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Reproduction
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.MinorArc
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.MajorArc
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.PrimeCharacterSums
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.UnitCharacters

/-!
# [S] Lemma 4.3 (comparison kernel) from the Siegel–Walfisz theorem

Source: `verification/stage7-sources/S-03.tex`, lines 270–437.

The intermediate statements of `Comparison/Statements.lean` and their proofs:

| statement | proof | from |
| --- | --- | --- |
| `ScaleLowerBound` | `scaleLowerBound` (`Scales.lean`) | — |
| `DyadicSummation` | `dyadicSummation` (`Dyadic.lean`) | — |
| `ProductAtomBound` | `productAtomBound` (`ProductAtom.lean`) | — |
| `CollapseBound` | `collapseBound` (`Collapse.lean`) | `ProductAtomBound` |
| `ProbabilityBilinear` | `probabilityBilinear` (`PhaseBilinear.lean`) | `CollapseBound`, Lemma 4.2 |
| `CharacterCell` | `characterCell_of_siegelWalfisz` | Siegel–Walfisz |
| `KernelNorm` | `kernelNorm_of_siegelWalfisz` | `CharacterCell`, the Gram bound |
| `CharacterReproduction` | `characterReproduction_of_siegelWalfisz` | `CharacterCell` |
| `MinorArcBound` | `minorArcBound_of_siegelWalfisz` | `ProbabilityBilinear`, `KernelNorm`, `ScaleLowerBound` |
| `MajorArcBound` | `majorArcBound_of_siegelWalfisz` | `CharacterReproduction`, `ScaleLowerBound`, (eq:ideal-cell-costs), (eq:ideal-rational-expansion) |

The assembly is `comparisonKernelLemma_of_statements` (`Assembly.lean`). No intermediate statement
remains open: `comparisonKernelLemma_of_open` has no hypothesis other than the Siegel–Walfisz
theorem, and `comparisonKernelLemma_of_siegelWalfisz` is Lemma 4.3.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

/-- **(eq:ideal-character-cell)** [S-03:0208–0241] from the Siegel–Walfisz theorem. -/
theorem characterCell_of_siegelWalfisz (hSW : Supply.SiegelWalfiszPrimeCounting) :
    CharacterCell :=
  characterCell_of_reciprocal (reciprocalPrimeCharacterSum_of_siegelWalfisz hSW)

/-- **Kernel integration has norm at most `2`** [S-03:0243–0266] from the Siegel–Walfisz
theorem. -/
theorem kernelNorm_of_siegelWalfisz (hSW : Supply.SiegelWalfiszPrimeCounting) : KernelNorm :=
  kernelNorm_of_cell (characterCell_of_siegelWalfisz hSW) gramFrameBound

/-- **(eq:ideal-character-reproduction)** [S-03:0391–0403] from the Siegel–Walfisz theorem. -/
theorem characterReproduction_of_siegelWalfisz (hSW : Supply.SiegelWalfiszPrimeCounting) :
    CharacterReproduction :=
  characterReproduction_of (characterCell_of_siegelWalfisz hSW) primitiveInduction

/-- **Denominators larger than `Q`** [S-03:0316–0337] from the Siegel–Walfisz theorem. -/
theorem minorArcBound_of_siegelWalfisz (hSW : Supply.SiegelWalfiszPrimeCounting) :
    MinorArcBound :=
  minorArcBound_of scaleLowerBound probabilityBilinear (kernelNorm_of_siegelWalfisz hSW)

/-- **Denominators at most `Q`** [S-03:0339–0412] from the Siegel–Walfisz theorem. -/
theorem majorArcBound_of_siegelWalfisz (hSW : Supply.SiegelWalfiszPrimeCounting) :
    MajorArcBound :=
  majorArcBound_of scaleLowerBound (characterReproduction_of_siegelWalfisz hSW) kernelCostsLemma
    rationalPhaseExpansion

/-- **[S] Lemma 4.3 (comparison kernel)** [S-03:0270–0437] from the statements of
`Comparison/Statements.lean` which are not yet proved. That list is empty: the only hypothesis is
the Siegel–Walfisz theorem. -/
theorem comparisonKernelLemma_of_open (hSW : Supply.SiegelWalfiszPrimeCounting) :
    ComparisonKernelLemma :=
  comparisonKernelLemma_of_statements scaleLowerBound dyadicSummation
    (minorArcBound_of_siegelWalfisz hSW) (majorArcBound_of_siegelWalfisz hSW)

/-- **[S] Lemma 4.3 (comparison kernel)** [S-03:0270–0437] from the Siegel–Walfisz theorem. -/
theorem comparisonKernelLemma_of_siegelWalfisz (hSW : Supply.SiegelWalfiszPrimeCounting) :
    ComparisonKernelLemma :=
  comparisonKernelLemma_of_open hSW

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
