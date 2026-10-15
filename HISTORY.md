# Historical background and comparison with OpenAI

This document preserves the detailed literature review from the README.
The checked versions and limits are recorded in [ci/prior-art-review.json](ci/prior-art-review.json).
For the main and variant statements, see the [README](README.md).

The historical question is Artin's 1927 primitive-root conjecture: for each fixed
integer $`a\ne-1`$ that is not a square, are there infinitely many primes for which
$`a`$ is a primitive root, and do these primes have the predicted positive density?
The [historical account, §17.2](https://www.mathi.uni-heidelberg.de/~roquette/hasse-artin/hasart-web-080922su43.html)
records both infinitude and a density prediction. The density formula required later
corrections; the exact-density question below refers to its usual corrected form.

| Part of the classical question | OpenAI's single-base Theorem 1.1 | Current Lean targets |
|---|---|---|
| Infinitely many primes for every prescribed admissible base | Claims this for every admissible integer, including negative bases, through a lower bound of $`c_a x/(\log x)^2`$. | Implies this for every nonsquare integer $`a\ge2`$ by taking $`A=\{a\}`$. |
| A positive lower proportion among all primes | The stated lower bound alone does not establish this. | Implies this for every nonsquare integer $`a\ge2`$ through the lower bound $`c_a x/\log x`$. |
| A limiting density equal to the predicted constant | Not established by that theorem. | Not established by the current targets. |

OpenAI's comparison statement is in
[the single-base manuscript, p.2, Theorem 1.1 and the following paragraph](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf#page=2).
This repository's [independent target](FClikelean/SimultaneousPrimitiveRoots.lean)
reduces to the classical positive-base case at $`A=\{a\}`$, when the square condition
is exactly that $`a`$ is not a square. It also extends the subject to finite sets of
simultaneous bases. The lower bound does not prove the existence or the exact value
of a limiting density, so these targets do not constitute a complete resolution of
the density form of Artin's conjecture.

## Prior art and the difference from OpenAI

The 15 October 2026 literature review confirms the differences from OpenAI's two
4 October Theorem 1.1 statements. It does **not** establish that either positive
density or general simultaneous bases is a new problem or a first-ever result.

| Aspect | Earlier research | Difference in the current target |
|---|---|---|
| Single-base positive density | Hooley proved the density asymptotic under GRH; [Fan–Pollack (2025), introduction and Theorem 1.1](https://arxiv.org/html/2505.05601v2#S1) give a uniform GRH version. | Compared with OpenAI's $`x/(\log x)^2`$ bound, the singleton target gives $`x/\log x`$ for every nonsquare $`a\ge2`$, without external analytic hypotheses in its statement. The scale itself was known conditionally. |
| General simultaneous bases | Matthews (1976) treated integer bases under GRH; [Anwar–Pappalardi (2017), p.35](https://www.impan.pl/shop/publication/transaction/download/product/92279#page=1) state the precise obstructions and prove an infinitude criterion under Hypothesis H. | Compared with OpenAI's conditional prime-base theorem, this target allows any nonempty finite positive integer set satisfying SQ, and gives $`x/\log x`$. General simultaneous bases were already studied. |
| Odd-subset square obstruction | [Moree–Stevenhagen, Section 5, equation (5.2), and Theorem 6.2](https://arxiv.org/html/1203.4313v2#S5) explicitly treat the obstruction and further entanglement conditions. | SQ is an existing obstruction, not a new criterion invented by this repository. |
| Formal verification | The [upstream Artin formalization](https://github.com/cadamcat/artin-primitive-roots-lean4/blob/5a36d8670f4b56bf2bb15a3fb65ff4774f6caf27/README.md) already records all-admissible-base infinitude and OpenAI's $`x/(\log x)^2`$ theorem. This repository uses its libraries. | The current formal targets, additional argument, Lean 4.33.1 port and independent comparison are the local verification contribution. This is not a first formalization of single-base infinitude. |

For positive bases, the negative-square obstruction (beta) stated on p.35 of
Anwar–Pappalardi is impossible. Thus, **as an inference from that criterion**, SQ
already implies positive simultaneous density under GRH in the domain considered
here. A positive density asymptotic gives a dyadic $`x/\log x`$ lower bound by
subtracting the counts at $`2x`$ and $`x`$. The relevant candidate advance is therefore
the combined scope and bound **without those external analytic assumptions**.

Earlier unconditional claims also require acknowledgment.
[Carella's 2016 article](https://future-in-tech.net/11.2/R-Carella-PrimesAndPrimitiveRoot.pdf#page=1)
and [2020 addendum, p.717 abstract](https://future-in-tech.net/15.2/R-Carella-AC.pdf#page=1)
claim a cumulative $`X/\log X`$ lower bound for a fixed base.
[Carella (2022), p.2, Theorem 1.1 and Definition 1.1](https://arxiv.org/pdf/2204.02245v1#page=2)
claim a simultaneous positive-density asymptotic for fixed polynomial values and
discuss larger admissible tuples. This review neither validates nor refutes their
complete proofs, and does not identify their scope with the arbitrary SQ target.
A cumulative lower bound alone is also distinct from the target's bound in every
sufficiently large dyadic interval.

Consequently, **the theorem-level strengthening relative to the pinned OpenAI
statements is confirmed; historical priority for a first unconditional proof remains
unestablished**. The review does not certify a full Artin density asymptotic, an
all-negative-base result, or community acceptance of the 2026 manuscripts.
The [structured review record](ci/prior-art-review.json) lists the versions, checked
locations, assumptions, inferences and limits. Hooley's and Matthews's mathematical
content was checked using the later primary papers identified there; this was a
bounded literature review rather than an independent audit of every cited proof.

| Date | Contributor | Contribution |
|---|---|---|
| 1927 | Emil Artin | Proposed the primitive-root conjecture for a single admissible integer base ([historical account, §17.2](https://www.mathi.uni-heidelberg.de/~roquette/hasse-artin/hasart-web-080922su43.html)). |
| 1967 | Christopher Hooley | Proved the predicted single-base density formula assuming GRH for the relevant number fields ([paper](https://doi.org/10.1515/crll.1967.225.209)). |
| 1976 | Keith Matthews | Studied simultaneous primitive-root densities under GRH ([paper](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/all/29/2/100983/a-generalisation-of-artin-s-conjecture-for-primitive-roots)). |
| 2012 preprint; 2014 publication | Pieter Moree and Peter Stevenhagen | Analyzed higher-rank primitive-root densities, including the odd-subset square obstruction in Section 5, equation (5.2) ([paper](https://arxiv.org/abs/1203.4313)). |
| 2016; 2020 addendum | N. A. Carella | Earlier claim of a cumulative $`X/\log X`$ lower bound for fixed bases ([2020 abstract](https://future-in-tech.net/15.2/R-Carella-AC.pdf#page=1)); complete proof validity is not assessed in this review. |
| 2017 | Mohamed Anwar and Francesco Pappalardi | Gave a simultaneous infinitude criterion for general rational bases assuming Hypothesis H ([paper](https://www.impan.pl/shop/publication/transaction/download/product/92279#page=1)). |
| 2022 | N. A. Carella | Earlier claim of a simultaneous positive-density asymptotic for polynomial values ([Theorem 1.1](https://arxiv.org/pdf/2204.02245v1#page=2)); complete proof validity is not assessed here. |
| 2025 | Steve Fan and Paul Pollack | Established a uniform version of the Artin–Hooley density asymptotic under GRH ([Theorem 1.1](https://arxiv.org/html/2505.05601v2#S1)). |
| August 2026 | M. Ram Murty and Sunil Naik | Obtained infinitude and a cumulative $`X/(\log X)^2`$ lower bound for base 2 assuming a non-abelian large-sieve inequality ([Theorem 1](https://arxiv.org/html/2608.21573v1#S1)). |
| 4 October 2026 manuscripts | OpenAI | Presented a single-base lower bound of order $`x/(\log x)^2`$ for every admissible integer base, and a conditional simultaneous bound of that order for fixed distinct prime bases ([single-base Theorem 1.1](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf#page=2); [simultaneous Theorem 1.1](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Simultaneous-primitive-roots-a-conditional-lower-bound-for-prime-bases-October-4-2026/simultaneous-primitive-roots-conditional-lower-bound-prime-bases.pdf#page=1)). |
| 9 October 2026 | Kenta Kitamura | Stated a lower bound of order $`x/\log x`$ for general finite positive integer bases satisfying the square condition, assuming the Section 2 analytic estimates ([Theorem 1.1](PDF/simultaneous-primitive-roots.pdf#page=1)). |
| 15 October 2026 | This repository | Completed local Lean 4.33.1 verification of the sufficient direction without external analytic hypotheses and of the square obstruction: build, axiom checks and complete Comparator replay passed ([record](ci/local-verification.json)). Manuscript correspondence and Linux CI remain pending. |

The OpenAI simultaneous manuscript assumes Inputs 3.1, 4.1, 5.1 and 5.2: Hecke
zero-free estimates, marked Type II estimates, a block sieve and rough-number density
estimates. The current target allows general positive integer bases satisfying the
square condition and strengthens the lower bound to $`x/\log x`$.
This is a positive lower bound, rather than an exact density asymptotic.
The manuscript's analytic assumptions and the closed Lean theorem must still be
reconciled in the human correspondence review.

