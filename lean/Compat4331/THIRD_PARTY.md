# Mathlib compatibility modules

These modules provide Lean/Mathlib v4.33.1 equivalents of declarations from
Mathlib commit `f6090c7095e1e56b3464c1daba5f24631f1290d2`. Some proofs are
copied with adjustments; other adapters are proved using the older API.
All twenty-two modules use Apache-2.0; the full license is retained in [LICENSE](LICENSE).

Upstream paths below are relative to Mathlib's `Mathlib/` directory. The
upstream copyright and author notices are retained here alongside the module
headers, including notices from several source files combined into one module.
All listed copyright notices state “All rights reserved” and release the source
under the Apache 2.0 license.

| Compatibility module | Upstream source files | Upstream copyright and authors |
|---|---|---|
| `AbelInequality.lean` | `Algebra/Order/Chebyshev.lean`; `Algebra/BigOperators/Module.lean` | Copyright (c) 2023 Mantas Bakšys, Yaël Dillies; Copyright (c) 2022 Dylan MacKenzie. Authors: the named copyright holders. |
| `AdeleEmbeddings.lean` | `RingTheory/DedekindDomain/FiniteAdeleRing.lean`; `NumberTheory/NumberField/InfiniteAdeleRing.lean`; `NumberTheory/NumberField/AdeleRing.lean` | Copyright (c) 2023 María Inés de Frutos-Fernández; Copyright (c) 2024 Salvatore Mercuri, María Inés de Frutos-Fernández. Authors: the named copyright holders. |
| `CircleMeasure.lean` | `MeasureTheory/Group/Circle.lean` | Copyright (c) 2026 Terence Tao. Author: Terence Tao. |
| `CompactSmoothBounds.lean` | `Analysis/Calculus/ContDiff/Basic.lean` | Copyright (c) 2019 Sébastien Gouëzel. Authors: Sébastien Gouëzel, Floris van Doorn. |
| `ExpSubstitution.lean` | `MeasureTheory/Integral/IntegralEqImproper.lean`; `Analysis/SpecialFunctions/ImproperIntegrals.lean` | Copyright (c) 2021 Anatole Dedecker; Copyright (c) 2023 David Loeffler. Authors: Anatole Dedecker, Bhavik Mehta, David Loeffler. |
| `FiniteQuotients.lean` | `RingTheory/Ideal/Quotient/HasFiniteQuotients/Basic.lean` | Copyright (c) 2026 Xavier Roblot. Author: Xavier Roblot. |
| `GroupClosure.lean` | `Topology/Algebra/Group/Pointwise.lean` | Copyright (c) 2017 Johannes Hölzl. Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot. |
| `IdealInertia.lean` | `RingTheory/Ideal/Pointwise.lean` | Copyright (c) 2024 Eric Wieser. Author: Eric Wieser. |
| `LinearMapIsometryExtension.lean` | `Analysis/Normed/Operator/Extend.lean` | Copyright (c) 2025 Moritz Doll. Authors: Moritz Doll, Zhouhang Zhou. |
| `LogSubstitution.lean` | `MeasureTheory/Integral/IntegralEqImproper.lean` | Copyright (c) 2021 Anatole Dedecker. Authors: Anatole Dedecker, Bhavik Mehta. |
| `MatrixClosed.lean` | `Analysis/Matrix/Order.lean` | Copyright (c) 2025 Monica Omar. Author: Monica Omar. |
| `MultipliableOneSub.lean` | `Analysis/SpecialFunctions/Log/Summable.lean` | Copyright (c) 2024 Chris Birkbeck. Author: Chris Birkbeck. |
| `NatSquares.lean` | `Data/Nat/Factorization/Defs.lean` | Copyright (c) 2021 Stuart Presnell. Author: Stuart Presnell. |
| `OAIElementarySymmetric.lean` | `RingTheory/MvPolynomial/Symmetric/Defs.lean` | Copyright (c) 2020 Hanting Zhang. Authors: Hanting Zhang, Johan Commelin. |
| `PowerSeriesLog.lean` | `RingTheory/PowerSeries/Log.lean`; `RingTheory/PowerSeries/Substitution.lean` | Copyright (c) 2026 Ralf Stephan; Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos Fernández. Authors: the named copyright holders. |
| `RationalSquares.lean` | `Data/Nat/Factorization/Defs.lean`; `NumberTheory/Padics/PadicVal/Basic.lean` | Copyright (c) 2021 Stuart Presnell; Copyright (c) 2018 Robert Y. Lewis. Authors: Stuart Presnell, Robert Y. Lewis, Matthew Robert Ballard. |
| `RestrictedProduct.lean` | `Topology/Algebra/RestrictedProduct/Basic.lean` | Copyright (c) 2025 Anatole Dedecker. Author: Anatole Dedecker. |
| `SeparableResidueInertia.lean` | `RingTheory/LocalRing/ResidueField/Separable.lean`; `NumberTheory/RamificationInertia/Galois.lean` | Copyright (c) 2026 Xavier Roblot; Copyright (c) 2024 Yongle Hu. Authors: Xavier Roblot, Yongle Hu, Jiedong Jiang. |
| `SpecialLinearKernel.lean` | `LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean` | Copyright (c) 2021 Chris Birkbeck. Author: Chris Birkbeck. |
| `SquarefreeDecomposition.lean` | `Algebra/Squarefree/Basic.lean` | Copyright (c) 2020 Aaron Anderson. Author: Aaron Anderson. |
| `TemperatePhase.lean` | `Analysis/Distribution/TemperateGrowth.lean` | Copyright (c) 2025 Moritz Doll. Authors: Moritz Doll, Anatole Dedecker, Sébastien Gouëzel. |
| `TensorInduction.lean` | `LinearAlgebra/TensorProduct/Defs.lean` | Copyright (c) 2018 Kenny Lau. Authors: Kenny Lau, Mario Carneiro. |

The declarations in `GroupClosure` and `TensorInduction` are derived from the
v4.33.1 neighborhood-basis and tensor-induction principles respectively. Their
proofs adapt the corresponding later Mathlib statements. `AdeleEmbeddings`
expresses the later completion embeddings and idele definitions using the
v4.33.1 adele-ring representation. These compatibility proofs and definitions
add no axioms.
`OAIElementarySymmetric` supplies `Multiset.esymm_of_card_lt` with the same
statement and powerset-cardinality proof as the pinned later Mathlib source;
it is shared by the vendored OAI prime-power-sum and diagonal modules.
`SpecialLinearKernel` preserves the later `Matrix.SpecialLinearGroup.toGLKerEquiv`
statement and proof using the v4.33.1 special-linear embedding into the general
linear group; it is shared by the two prime-power root-cardinality proofs.
`CompactSmoothBounds` supplies `HasCompactSupport.exists_bound_iteratedFDeriv`
with the same assumptions and conclusion as the pinned later Mathlib source.
Its proof uses the v4.33.1 compact-support bound for each continuous iterated
derivative and a finite maximum over the requested orders.
`SeparableResidueInertia` retains the later `Algebra.HasSeparableResidueFieldsAt`
predicate and inertia-count proof, so the generic Tau Ceti theorem keeps its
original residue-separability hypothesis. Its proof explicitly selects the
canonical localization algebra using the older API.
`SquarefreeDecomposition` supplies the later generic `exists_sq_mul_squarefree`
with the same assumptions, witness order, conclusion and irreducible-induction
proof, shared by the OAI cube-label and Artin squarefree-decomposition modules.
`MultipliableOneSub` supplies the later generic `multipliable_one_sub_of_summable`
with the same assumptions and conclusion. Its unchanged proof applies the
v4.33.1 convergence theorem for `1 + f` to `-f` using invariance of the norm
under negation, shared by the Hecke Euler-product and principal-input modules.
`RationalSquares` retains the later integer and rational square criteria and
the rational numerator/denominator valuation lemmas. It reuses `NatSquares`
and the v4.33.1 rational-square and valuation APIs; the coprimality proof uses
the older zero-valuation criterion. The statements add no hypotheses.
`TemperatePhase` supplies the later temperate-growth theorems for real sine,
real cosine, and `x ↦ exp (x * I)` with unchanged statements and proofs. The
v4.33.1 iterated-derivative bounds and composition rules provide their
dependencies, preserving the original Fourier phase multiplier.

`LinearMapIsometryExtension` retains the later linear-map isometric extension
definition, including its `toLinearMap := f.extendOfNorm e` field and the
original norm-preservation and restriction proofs.

`LogSubstitution` retains the later generic Bochner integral substitution
theorem and its proof from the same Mathlib commit, without additional
completeness or measurability assumptions.
