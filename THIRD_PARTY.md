# Third-party sources

The original license and copyright notices are retained in the source files
and the compatibility-module attribution record linked below.
The repository license is Apache-2.0; third-party components retain their own
notices and attribution. This publication copies the existing verified
workspace source and then ports it to Lean/Mathlib v4.33.1.

| Component | Source and version record | Included license / notices |
|---|---|---|
| Formal Conjectures utilities (statement checks only) | `79eac378a26b46d30974cdb33962e0752591b79d`, pinned in `tools/fc-style/lake-manifest.json` | Apache-2.0 in the fetched upstream package |
| Mathlib | `0df444a360eaa60ab8c11dca51a86af692955474`, pinned in `lean/lake-manifest.json` | Mathlib package license; copied backports use `lean/Compat4331/LICENSE` |
| Comparator | `3927ad383f208ae977c340a91c48ac9b497d2097` | `tools/comparator/LICENSE` |
| lean4export | `15f6055e299ad5b89345e533cc2192f4cc00f659` | `tools/lean4export/LICENSE` |
| ArtinPrimitiveRoots | `5a36d8670f4b56bf2bb15a3fb65ff4774f6caf27`; `lean/vendor/ARTINPRIMITIVEROOTS_SOURCES.md` | `lean/vendor/ARTINPRIMITIVEROOTS_LICENSE`, `_NOTICE`, `_THIRD_PARTY.md` |
| OAI / openai/math | `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; `lean/vendor/OAI_SOURCES.md` | `lean/vendor/OAI_LICENSE` |
| TauCeti | `vendor/TauCeti` uses `d5a3709`, documented in `lean/vendor/OAI_SOURCES.md`; the ArtinPrimitiveRoots snapshot retains its own provenance notes | `lean/vendor/TAUCETI_LICENSE` |
| LeanPool | Pre-port files are identified by `ci/original-source-sha256.json`; retained copyright notices and the RellichKondrachov source record in `lean/vendor/OAI_SOURCES.md` | `lean/vendor/LEANPOOL_LICENSE` |
| ClassFieldTheory, ValuedFieldTheory, GaloisCohomology, ProCGroups | Vendored closure of ClassFieldTheory `2eb22d6485af45f29c5219de6c49f196a61c4f49`; `lean/vendor/OAI_SOURCES.md` and source notices | `lean/vendor/CLASSFIELDTHEORY_LICENSE` |
| CebotarevDensity / DedekindResidue / AINTLIB | AINTLIB `160e446617a2168c34c95bbe7a76c4105b392434`, with the documented openai/math patches | `lean/vendor/AINTLIB_LICENSE` |
| PrimeNumberTheoremAnd / StrongPNT | Patched upstream source and new Erdos970 files from the pinned openai/math tree | `lean/vendor/PRIMENUMBERTHEOREMAND_LICENSE` |
| RellichKondrachov | Module-system port recorded in `lean/vendor/OAI_SOURCES.md` | `lean/vendor/RELLICHKONDRACHOV_LICENSE` |
| PNTAnd | Existing adapted source under `lean/ported/PNTAnd` | `lean/ported/PNTAnd/LICENSE` |

The compatibility modules under `lean/Compat4331` backport definitions and
theorems from Mathlib `f6090c7095e1e56b3464c1daba5f24631f1290d2`, or prove
equivalent adapters using the v4.33.1 API. Their shared Apache-2.0 license is
`lean/Compat4331/LICENSE`. The [module-by-module source and attribution record](lean/Compat4331/THIRD_PARTY.md)
includes all compatibility modules and the upstream notices for files whose declarations
are combined into one compatibility module. They introduce no additional axioms.

The checking-tool implementation digests are frozen in
[ci/checking-tool-sha256.json](ci/checking-tool-sha256.json). The original
workspace source digests are in
[ci/original-source-sha256.json](ci/original-source-sha256.json).
The publication migration is recorded in
[ci/port-changes.json](ci/port-changes.json) and
[ci/lean4331-port.patch](ci/lean4331-port.patch), including the source/import
changes needed for v4.33.1.
The compiler/interpreter algorithms of the checking tools are not edited.
Their toolchain and package configuration are adapted to the pinned v4.33.1
publication environment, as documented in [ci/toolchain-lock.json](ci/toolchain-lock.json).

The local digamma recurrence proof in
`lean/vendor/ArtinPrimitiveRoots/A2/Proofs/A2-QS-POISSON/P0.lean`
also copies the natural-number induction proof from Mathlib commit
`f6090c7095e1e56b3464c1daba5f24631f1290d2`,
`Analysis/SpecialFunctions/Gamma/Digamma.lean`.
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0; the upstream notice is retained beside the proof.

The local finite valuation support proofs in
`lean/vendor/ArtinPrimitiveRoots/A2/Proofs/A2_RF_LOCAL/Arithmetic.lean`
and `lean/vendor/ArtinPrimitiveRoots/A2/Reflection/Missing.lean`
also adapt the proof from Mathlib commit
`f6090c7095e1e56b3464c1daba5f24631f1290d2`,
`RingTheory/DedekindDomain/FiniteAdeleRing.lean`.
Copyright (c) 2023 María Inés de Frutos-Fernández.
Released under Apache 2.0; the upstream notice is retained beside the proof.
