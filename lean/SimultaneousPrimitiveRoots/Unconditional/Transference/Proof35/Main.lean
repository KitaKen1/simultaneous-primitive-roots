module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Assembly
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Counts
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ReturnFourier

/-!
# [S] Theorem 3.5 as a tree of intermediate results

Source: `verification/stage7-sources/S-02.tex`, lines 188–1258 (`[S-02:0188–1258]`).

`localTransference_of_open` proves `LocalTransference` (`Transference/Statements.lean`) from the
thirteen intermediate statements of the proof which are not proved in this directory. Each of
them is a `def … : Prop`; none is assumed anywhere.

## The tree

```
LocalTransference                                        Theorem 3.5              [S-02:0163–0188]
└─ localTransference_of_distinct  (proved)               completion               [S-02:1242–1258]
   ├─ ResidueReduction                                   "we may use the residue model" [0293–0307]
   │  └─ ResidueSummation : UniformResidueReplacement → ResidueReduction          [0212–0234, 0293–0307]
   │     ├─ UniformResidueReplacement                    Lemma 3.6                [0236–0291]
   │     ├─ physMoment_eq_sum_walks  (proved)            path expansion           [0212–0222]
   │     └─ schur_bound, tag_schur_bound  (proved)       Lemma 3.4, residue model [0132–0158]
   ├─ returnFourier  (proved)                            (eq:return-fourier)      [0308–0314]
   ├─ MemoryIdentity                                     Lemma 3.7                [0316–0582]
   ├─ MemoryTail                                         (eq:memory-tail)         [0796–0822]
   └─ distinctBirthBound_of  (proved)                    distinct births          [1020–1245]
      ├─ ghostOpWith_opBound  (proved, Schur)  ⇐ GhostAbsolute   (eq:ghost-absolute-bound) [0646–0702]
      │                                           └─ GhostRowCompat  (one-group row = `Graph/` row)
      ├─ edgeOpWith_opBound   (proved, Schur)  ⇐ MemoryAbsolute  Lemma 3.8        [0704–0795]
      ├─ BoundaryNorm                                    ‖𝟏_∅‖ bounded            [0812–0819]
      ├─ edgeContraction_of  (proved)                    (eq:whole-edge-contraction) [1020–1041]
      │  ├─ RareTransfer                                 Lemma 3.9                [0824–0894]
      │  └─ CleanNorm                                    Lemma 3.10               [0896–1019]
      ├─ distinctSum_eq_sum_rankPart  (proved) ⇐ DistinctIndicatorExpansion  (eq:distinct-indicator) [1070–1093]
      ├─ sum_abs_blockMu_mul_le  (proved)      ⇐ RankCoefficientCount  (eq:rank-coefficient-count) [1095–1105]
      ├─ birthAddressCount  (proved)                     (eq:birth-address-count) [1063–1068]
      ├─ HighRank                                        (eq:high-rank-path-bound) [1107–1170]
      └─ LowRankStep                                     (eq:low-rank-path-bound) [1172–1235]
         └─ HistoryExpansion  (path integral = matrix element of the operator product)
```

`GhostRowCompat` and `HistoryExpansion` are not hypotheses of the assembly; they are the exact
statements through which `GhostAbsolute` and `LowRankStep` are meant to be proved.

## Sanity lemmas

* `physMoment_eq_sum_walks` — the path expansion of `(𝒜 𝒜*)^R u_n` equals the definition used in
  `physMoment` (`PathExpansion.lean`).
* `edgeOp_eq_clean_add_dirty`, `edgeOpWith_eq_sym` — `ℰ_i = ℰ_{i,clean} + ℰ_{i,dirty}` and `ℰ_i` is
  a row transition between two symmetrizations (`Operators.lean`).
* `birthAddr_card`, `blockRank_le_card` (`History.lean`); `Res.card`, `Res.intCast_eq_zero_iff`,
  `memRho_pos`, `memRho_lt_one`, `sqrt_lt_memRho_sq`, `memV_spec` (`Basic.lean`); the bridge to
  `Graph/` for `b_p` and `μ̃_g` (`Bridge.lean`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

/-- **[S] Theorem 3.5 from the open intermediate statements.** `LocalTransference` follows from
Lemma 3.6 and the summation over paths, Lemma 3.7, the absolute bounds (eq:ghost-absolute-bound)
and Lemma 3.8, the norm of the boundary vector, the truncation estimate (eq:memory-tail),
Lemmas 3.9 and 3.10, the combinatorial statements (eq:distinct-indicator) and
(eq:rank-coefficient-count), and the large- and small-rank estimates. The return condition
(eq:return-fourier) and the count (eq:birth-address-count) are proved (`returnFourier`,
`birthAddressCount`), as is everything in the assembly [S-02:1020–1258]. -/
theorem localTransference_of_open (h1 : UniformResidueReplacement) (h2 : ResidueSummation)
    (h3 : MemoryIdentity) (h4 : GhostAbsolute) (h5 : MemoryAbsolute) (h6 : BoundaryNorm)
    (h7 : MemoryTail) (h8 : RareTransfer) (h9 : CleanNorm) (h10 : DistinctIndicatorExpansion)
    (h11 : RankCoefficientCount) (h12 : HighRank) (h13 : LowRankStep) : LocalTransference :=
  localTransference_of h1 h2 returnFourier h3 h4 h5 h6 h7 h8 h9 h10 h11 birthAddressCount h12 h13

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
