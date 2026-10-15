module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.Assembly
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.OnePrime
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.DistinctSkeletonProof
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.BornSetRecursionProof

/-!
# [S] Lemma 3.7 (exact memory identity) as a tree of intermediate results

Source: `verification/stage7-sources/S-02.tex`, lines 316–582 (`[S-02:0316–0582]`).

`memoryIdentity_of_open` proves `MemoryIdentity` (`Proof35/Statements.lean`) from the five
intermediate statements of `Memory/Statements.lean` which are not proved in this directory. Each
of them is a `def … : Prop`; none is assumed anywhere.

## The tree

```
MemoryIdentity                                        Lemma 3.7                      [S-02:0523–0535]
└─ memoryIdentity_of_parts  (proved, Assembly.lean)
   ├─ memoryIdentity_of_raw  (proved)                 threshold: RawHyp for large x  [0318–0325, 0376]
   └─ memoryIdentityRaw_of_parts  (proved)            the identity for raw families
      ├─ PhaseSkeleton        (A)                     physical paths by skeletons    [0212–0234, 0293–0314]
      ├─ distinctSkeleton     (B, proved)             histories by skeletons         [0516–0534]
      │    HistorySkeleton.lean, DistinctSkeletonProof.lean
      └─ Skel.bigPhys_eq  (proved)                    bigPhys = (∏ b_p) · memSum for one skeleton
         ├─ BigResidueProduct (C1)                    product over the big primes    [0226–0234, 0327–0334]
         ├─ onePrimeLifespan  (C2, proved)            (eq:prefix-ghost), (eq:orphan-expansion) [0327–0373]
         │    OnePrime.lean, from `Graph.primewise_*`
         └─ Skel.memSum_eq_lifeSum  (proved)          memSum = 1_inj · norm · ∏_p lifeSum p
            ├─ bornSetRecursion  (M1, proved)         distinct-birth rule as a running set [0516–0521]
            │    BirthStages.lean, BornSetRecursionProof.lean
            ├─ Skel.fut_eq_chain  (proved)            backward induction over the operations
            │  ├─ GhostStepFactor (M2)                a visit operation acts prime by prime [0456–0475]
            │  └─ EdgeStepFactor  (M3)                an edge operation acts prime by prime [0477–0514]
            └─ ChainLifespan      (M4)                the per-prime chain sums to lifeSum [0538–0567]
```
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

/-- **[S] Lemma 3.7 from the open intermediate statements.** `MemoryIdentity` follows from the
physical path expansion by skeletons (A), the product over the big primes of the residue
expectation (C1), the factorization of a visit and of an edge operation over the big primes (M2),
(M3), and the evaluation of the per-prime transfer chain (M4). The memory path integral by
skeletons (B), the one-prime lifespan expansion (C2) and the distinct-birth rule as a running set
(M1) are proved (`distinctSkeleton`, `onePrimeLifespan`, `bornSetRecursion`), as is the assembly. -/
theorem memoryIdentity_of_open (hA : PhaseSkeleton) (hC1 : BigResidueProduct)
    (hM2 : GhostStepFactor) (hM3 : EdgeStepFactor) (hM4 : ChainLifespan) : MemoryIdentity :=
  memoryIdentity_of_parts hA distinctSkeleton hC1 onePrimeLifespan bornSetRecursion hM2 hM3 hM4

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
