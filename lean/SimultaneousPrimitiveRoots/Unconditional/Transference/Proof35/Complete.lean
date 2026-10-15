module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Main
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResidueSummationProof
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.MemoryIdentityProof
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.GhostAbsoluteProof
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.MemoryAbsoluteProof
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.BoundaryNormProof
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.MemoryTailProof
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.RareTransferProof
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.DistinctIndicator
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.RankCount
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.HighRank.Proof
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.LowRank
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.CleanNorm.Main

/-!
# [S] Theorem 3.5

All thirteen intermediate statements of `localTransference_of_open` (`Proof35/Main.lean`) are
theorems of this directory:

| statement | theorem | file |
|---|---|---|
| `UniformResidueReplacement` (Lemma 3.6) | `uniformResidueReplacement` | `ResidueReplacementProof.lean` |
| `ResidueSummation` | `residueSummation` | `ResidueSummationProof.lean` |
| `MemoryIdentity` (Lemma 3.7) | `memoryIdentity` | `Memory/MemoryIdentityProof.lean` |
| `GhostAbsolute` | `ghostAbsolute` | `GhostAbsoluteProof.lean` |
| `MemoryAbsolute` (Lemma 3.8) | `memoryAbsolute` | `MemoryAbsoluteProof.lean` |
| `BoundaryNorm` | `boundaryNorm` | `BoundaryNormProof.lean` |
| `MemoryTail` | `memoryTail` | `MemoryTailProof.lean` |
| `RareTransfer` (Lemma 3.9) | `rareTransfer` | `RareTransferProof.lean` |
| `DistinctIndicatorExpansion` | `distinctIndicatorExpansion` | `DistinctIndicator.lean` |
| `RankCoefficientCount` | `rankCoefficientCount` | `RankCount.lean` |
| `HighRank` | `highRank` | `HighRank/Proof.lean` |
| `LowRankStep` | `lowRankStep` | `LowRank.lean` |
| `CleanNorm` (Lemma 3.10) | `cleanNorm` | `CleanNorm/Main.lean` |

Hence `localTransference : LocalTransference`, [S] Theorem 3.5 (`[S-02:0163–0188]`), with no
hypothesis. (`localTransference_of_cleanNorm` records the dependence on Lemma 3.10.)
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

/-- **[S] Theorem 3.5 from [S] Lemma 3.10.** -/
theorem localTransference_of_cleanNorm (h : CleanNorm) : LocalTransference :=
  localTransference_of_open uniformResidueReplacement residueSummation memoryIdentity
    ghostAbsolute memoryAbsolute boundaryNorm memoryTail rareTransfer h
    distinctIndicatorExpansion rankCoefficientCount highRank lowRankStep

/-- **[S] Theorem 3.5 (local transference)**, with no hypothesis. -/
theorem localTransference : LocalTransference :=
  localTransference_of_cleanNorm cleanNorm

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
