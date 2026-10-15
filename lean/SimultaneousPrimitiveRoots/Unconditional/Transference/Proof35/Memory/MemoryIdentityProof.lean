module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.Main
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.BigResidueProductProof
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.PhaseSkeletonProof
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.GhostStepFactorProof
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.EdgeStepFactorProof
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.ChainLifespanProof

/-!
# [S] Lemma 3.7 (exact memory identity)

Source: `verification/stage7-sources/S-02.tex`, lines 316–582 (`[S-02:0316–0582]`).

`memoryIdentity : MemoryIdentity` (`Proof35/Statements.lean`): "with the distinct-birth rule, the
independent-residue path expression with the phase in (eq:return-fourier) equals
`(∏_{p big} b_p) ⟨𝟏_∅, G_0 ℰ_0 G_1 ⋯ ℰ_{N-1} G_N 𝟏_∅⟩_distinct`".

It is `memoryIdentity_of_open` (`Memory/Main.lean`) applied to the five parts which that file
leaves open, all proved in this directory:

```
MemoryIdentity                                        Lemma 3.7                      [S-02:0523–0535]
└─ memoryIdentity_of_open  (Main.lean)
   ├─ phaseSkeleton      (A)   PhaseSkeletonProof.lean      physical paths by skeletons
   ├─ bigResidueProduct  (C1)  BigResidueProductProof.lean  product over the big primes
   ├─ ghostStepFactor    (M2)  GhostStepFactorProof.lean    a visit operation acts prime by prime
   ├─ edgeStepFactor     (M3)  EdgeStepFactorProof.lean     an edge operation acts prime by prime
   └─ chainLifespan      (M4)  ChainLifespanProof.lean      the per-prime chain sums to lifeSum
```

(The parts (B) `distinctSkeleton`, (C2) `onePrimeLifespan` and (M1) `bornSetRecursion` are inserted
in `Memory/Main.lean`.)
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

/-- **[S] Lemma 3.7 (exact memory identity, `lem:memory-identity`)** [S-02:0523–0535]. -/
theorem memoryIdentity : MemoryIdentity :=
  memoryIdentity_of_open phaseSkeleton bigResidueProduct ghostStepFactor edgeStepFactor
    chainLifespan

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
