# Lean proof of positive lower density of simultaneous primitive roots

OpenAI's conditional simultaneous primitive-root theorem states the following
(see [OpenAI (2026), Theorem 1.1][openai-simultaneous]).

> **Main: simultaneous primitive roots for prime bases.**
> Let $`A`$ be a nonempty finite set of positive primes. Assume the four analytic
> inputs in Sections 3–5 of the paper: Inputs 3.1, 4.1, 5.1 and 5.2.
> For all sufficiently large real $`x`$, the number of primes $`x<p<2x`$ for which
> every $`a\in A`$ is a primitive root modulo $`p`$ is at least
>
> $$c_A\frac{x}{(\log x)^2}$$
>
> for some constant $`c_A>0`$ depending on $`A`$.

This repository presents the following two natural extensions of this result
and provides Lean proofs of both. Variant 1 removes the four analytic hypotheses.
Variant 2 further allows integer bases at least $`2`$ satisfying the square condition
and strengthens the lower bound to $`c_A x/\log x`$.

> **Variant 1: OpenAI's conclusion without the four analytic hypotheses.**
> Let $`A`$ be a nonempty finite set of positive primes. There are constants
> $`c_A>0`$ and $`x_A>1`$ such that, for every real $`x\ge x_A`$, at least
> $`c_A x/(\log x)^2`$ primes $`x<p<2x`$ have every $`a\in A`$ as a primitive root.
> No external analytic hypotheses are assumed.

> **Variant 2: positive lower density for positive integer bases.**
> Let $`A\subset\mathbb Z_{\ge2}`$ be a nonempty finite set satisfying the square condition
>
> $$\prod_{a\in B}a\text{ is not a square whenever }B\subseteq A\text{ has odd cardinality}.$$
>
> Let $`N_A(x)`$ count the primes $`x<p\le2x`$ for which every $`a\in A`$ is a
> primitive root modulo $`p`$. There exist constants $`c_A>0`$ and $`x_A\ge2`$
> such that, for every real $`x\ge x_A`$,
>
> $$N_A(x)\ge c_A\frac{x}{\log x}.$$

**Variant 2 ⇒ Variant 1** is proved in Lean. If Variant 1's conclusion matches
the paper's statement, it also gives OpenAI's conditional conclusion, without
proving the four inputs themselves. The paper-to-Lean correspondence remains
under review; its four-input formalization is kept outside the proposed submission.

| | Main (OpenAI) | Variant 1 (corollary) | Variant 2 (stronger result) |
|---|---|---|---|
| Bases | Positive primes | Positive primes | Integers $`\ge2`$ |
| Square condition | Automatic | Automatic | Required |
| Analytic hypotheses | Four inputs | None external | None external |
| Lower bound | $`c_A x/(\log x)^2`$ | $`c_A x/(\log x)^2`$ | $`c_A x/\log x`$ |
| Prime interval | $`x<p<2x`$ | $`x<p<2x`$ | $`x<p\le2x`$ |

The two main components are:

1. **A Formal Conjectures style statement.**
   [SimultaneousPrimitiveRoots.lean](FClikelean/SimultaneousPrimitiveRoots.lean)
   places the two variants in one self-contained file, without the four analytic definitions.
2. **The full Lean proof.**
   [MainClaim.lean](lean/SimultaneousPrimitiveRootsFinal/MainClaim.lean) combines the
   analytic and arithmetic arguments.
   [Solution.lean](lean/Solution.lean) proves both variants and the square-condition obstruction.
   [OpenAIMain.lean](lean/SimultaneousPrimitiveRootsFinal/OpenAIMain.lean)
   applies Variant 1 to the separate conditional reference statement.

The subcontribution is:

1. **Formalization and Lean proof of the square-condition obstruction.**
   See [Appendix](#appendix-why-the-square-condition-is-needed).

## Formal Conjectures like targets

### FClikelean

[SimultaneousPrimitiveRoots.lean](FClikelean/SimultaneousPrimitiveRoots.lean)
contains only the two statements proposed for FC, in this order:

1. `simultaneous_primitive_roots_unconditional`: the prime-base conclusion without the four inputs.
2. `positive_lower_density`: the stronger positive-integer variant.

The file needs no problem-specific `def`. It uses FC's standard
`public import FormalConjecturesUtil` and marks both
statements `category research solved, AMS 11`, following the
[reference format](https://github.com/KitaKen1/entropic-rogers-shephard/blob/main/FClikelean/EntropicRogersShephard.lean).
The module cites OpenAI's paper as `[OAI26]` and the accompanying Lean formalization
as `[Ki26]`. Each theorem links its Lean proof with `formal_proof using lean4 at "…"`.
It is independent of the proof library and the conditional reference file.

[OpenAIConditional.lean](FClikelean/OpenAIConditional.lean) keeps the four-input
conditional statement and its five definitions as a separate reference.
It is not part of the proposed FC submission. Its exact correspondence with the
paper's analytic inputs remains under review.

The necessary condition, `square_condition_necessary`, is isolated in
[SquareConditionNecessary.lean](FClikelean/SquareConditionNecessary.lean): if the
square condition fails, no odd prime works. It is also outside the two-theorem submission.
The submission file has two intentional `sorry` placeholders; the conditional
reference and square-condition supplement each have one. All three files are
self-contained with the pinned FC utilities in [tools/fc-style/](tools/fc-style/).
See the
[Japanese correspondence guide](FClikelean/README.md).

### Comparator target

[Challenge.lean](lean/Challenge.lean) contains only the two submitted statements,
with `import Mathlib` and no problem-specific definitions. The
[Comparator configuration](lean/comparator.json) uses `Solution` as its solution
module and checks exactly these targets:

- `SimultaneousPrimitiveRootsChallenge.simultaneous_primitive_roots_unconditional`
- `SimultaneousPrimitiveRootsChallenge.positive_lower_density`

Both types match the two-theorem FC submission after removing comments and
whitespace. Comparator compares their dependent definitions, checks permitted
axioms and replays the proof in the builtin Lean kernel.

[OpenAIConditional.lean](FClikelean/OpenAIConditional.lean), its bridge in
[OpenAIMain.lean](lean/SimultaneousPrimitiveRootsFinal/OpenAIMain.lean), and
[SquareConditionNecessary.lean](FClikelean/SquareConditionNecessary.lean) remain
separate reference or supplementary material. They are outside the current
Comparator target list. Variant 1 follows from Variant 2, including the change to
the open interval. This does not prove the four analytic inputs or establish
their equivalence with the paper's wording.

## Mathematical explanation (AI generated)

The [revised manuscript](NewPDF/simultaneous-primitive-roots-unconditional.pdf)
presents the mathematical argument, from the analytic theorems through the
candidate count and order-obstruction estimates to the conclusion.
The [original conditional note](PDF/simultaneous-primitive-roots.pdf) is retained.
The following summarizes the argument.

**1. Arrange the quadratic signs.** Write the prime exponents of each base as a
vector over $`\mathbb F_2`$. The square condition makes the required sign equations
consistent. Quadratic reciprocity and the Chinese remainder theorem produce
residue classes in which every base is a quadratic nonresidue, and small odd
prime divisors of $`p-1`$ are excluded.

**2. Count primes with a long factor of $`p-1`$.** Marked correlation estimates count
primes in these fixed classes for which

```math
p-1=Qr,\qquad x^{1-\eta}<Q\le x^{1-\eta/2},\qquad r<2x^\eta,
```

where $`Q`$ is prime and $`\eta>0`$ is small. Let $`\lambda_{A,Y}`$ be the relative
density of the chosen residue classes after a fixed small-prime cutoff $`Y`$.
The candidate count is a positive multiple of $`\lambda_{A,Y}x/\log x`$.

**3. Bound the splitting exceptions.** If a base $`a`$ fails to be a primitive root,
some prime $`q`$ divides its order index. Uniform estimates for the Kummer fields
$`\mathbb Q(\mu_q,a^{1/q})`$ control the exceptions with $`q\ne Q`$.
Their total contribution is

```math
O_A\!\left(\frac{x}{Y\log x}\right)+o(x/\log x).
```

**4. Remove the long-factor exception.** When $`q=Q`$, the order of $`a`$ is less
than $`2x^\eta`$. Such a prime divides

```math
\prod_{j\le2x^\eta}(a^j-1).
```

The logarithm of this product is $`O_a(x^{2\eta})`$, so these primes contribute only
$`o(x/\log x)`$. Sum over the fixed finite set of bases.

**5. Fix the cutoff and retain a positive lower bound.** For $`Y=2T^2+1`$, the
candidate coefficient is bounded below by a positive multiple of $`1/T`$, while
the exception coefficient is $`O_A(1/T^2)`$. Choose $`T`$ first and then let $`x`$
grow. This leaves the claimed positive multiple of $`x/\log x`$.

## Files

| Directory | Lean version | Purpose |
|---|---|---|
| [lean/](lean/) | `v4.33.1` | Canonical proof, pinned Mathlib, Challenge and Solution. |
| [FClikelean/](FClikelean/) | `v4.33.1` | Two-theorem FC submission; separate conditional reference and square-obstruction supplement. |
| [tools/](tools/) | `v4.33.1` | Pinned Comparator and Lean4export sources. |
| [ci/](ci/) | `v4.33.1` | Source audit, migration records, verification results and reproduction guide. |
| [scripts/](scripts/) | `v4.33.1` | Build, axiom checks, Comparator execution and sandbox preparation. |
| [.github/workflows/](.github/workflows/) | GitHub-hosted Linux | Independent statements, sandboxed proof comparison and kernel replay. |
| [NewPDF/](NewPDF/) | — | Revised mathematical proof in PDF format. |
| [PDF/](PDF/) | — | Original proof note and timestamp evidence. |

[HISTORY.md](HISTORY.md) gives the detailed historical comparison and literature review.
The proof uses OpenAI's libraries and the existing ArtinPrimitiveRoots formalization;
[THIRD_PARTY.md](THIRD_PARTY.md) records source revisions, licenses and the Lean 4.33.1 port.

## Verification

### Lean execution results

The current verification scope is the two submitted variants. Its local checks
and private Linux CI progress are recorded in
[two-variant-review.json](ci/two-variant-review.json). A successful complete CI
run for this configuration is not yet recorded.

Historical local builds used stock Lean 4.33.1 and pinned Mathlib. The previous
four-proof axiom audit reported exactly `[propext, Classical.choice, Quot.sound]`;
its scope is preserved in the
[previous four-target record](ci/four-target-review.json). These results do not
replace verification of the current two-variant configuration.

### Lean Comparator check

The reference, proof, Comparator and Lean4export all use Lean 4.33.1.
The checking tools are pinned to their 4.33 source revisions, with toolchains and
package configuration adapted to this publication. Their checking algorithms are
unchanged. The [toolchain lock](ci/toolchain-lock.json) and
[implementation digests](ci/checking-tool-sha256.json) fix these inputs.

The [original local Comparator run](ci/local-verification.json) passed for the
stronger variant and the square-condition obstruction, with permitted-axiom
checks and builtin Lean-kernel replay. It ended with `Your solution is okay!`.
The [later three-target record](ci/three-theorem-review.json) adds the prime-base
corollary; the [previous four-target record](ci/four-target-review.json) also
tracks the conditional reference. These are historical scopes, distinct from the
current pair of submitted variants.

The current two-target comparison is tracked in
[two-variant-review.json](ci/two-variant-review.json). The macOS development check
uses the upstream sandbox shim. Real Linux sandboxing is tested in
[private CI](https://github.com/KitaKen1/ci-test-sandbox/actions/workflows/lean.yml),
followed by [public CI](https://github.com/KitaKen1/simultaneous-primitive-roots/actions/workflows/lean.yml).

## Appendix: comparison with earlier work

The historical comparisons below use Variant 2. Variant 1 is its prime-base corollary.

### How the earlier results relate to Artin's problem

A number $`a`$ is a **primitive root modulo a prime $`p`$** if its powers give
all nonzero remainders modulo $`p`$. For example, powers of 2 modulo 5 give 2, 4, 3, 1.

> **Artin's problem (1927; modern formulation).**
> Fix an integer $`a`$ that is neither $`-1`$ nor a square.
> Are there infinitely many primes $`p`$ for which $`a`$ is a primitive root?
> The density conjecture further predicts that the fraction of such primes among
> all primes tends to a specified positive constant $`C(a)`$.

See the [modern statement, Section 1](https://arxiv.org/html/2505.05601v2#S1).
Infinitely many primes, a positive lower proportion, and the predicted limiting
proportion are three different conclusions.

The three results below concern several bases at once. Taking $`A=\{a\}`$
returns the single-base question.

| Part of Artin's problem | Anwar–Pappalardi (2017) | OpenAI's simultaneous main | This repo's variant |
|---|---|---|---|
| Infinitude for every nonsquare $`a\ge2`$ | Under Hypothesis H | Only prime $`a`$, assuming four inputs | Yes |
| Infinitude for admissible negative $`a`$ | Under Hypothesis H | Outside its scope | Outside its scope |
| A positive lower proportion for every nonsquare $`a\ge2`$ | Not asserted by this theorem | Not implied by its stated bound | Yes |
| Artin's predicted exact limiting proportion | Not asserted | Not asserted | Not asserted |

Here “OpenAI” means its simultaneous paper. Its separate [single-base theorem][openai-single]
already claims infinitude for every admissible integer, including negative bases.

### How OpenAI and this repo relate to Anwar–Pappalardi

> **Anwar–Pappalardi's theorem (2017).**
> Assume Hypothesis H. Let $`A\subset\mathbb Q\setminus\{0,\pm1\}`$ be finite and nonempty.
> Suppose:
>
> 1. No product of an odd number of distinct elements of $`A`$ is a rational square.
> 2. If an even number of distinct elements multiply to $`-3r^2`$ for some
>    nonzero rational $`r`$, there is a prime $`\ell\equiv1\pmod3`$ modulo which
>    no element of $`A`$ is a cube.
>
> Then infinitely many primes make every element of $`A`$ a primitive root.

Source: [*On simultaneous primitive roots*, p.36, Theorem](https://www.impan.pl/shop/publication/transaction/download/product/92279#page=2).
Hypothesis H predicts that suitable polynomial values are simultaneously prime
infinitely often. It is an assumption here, not a theorem proved in that paper.

For positive bases, condition 2 is automatic: their products cannot equal $`-3r^2`$.
Condition 1 is the square condition used in this repo.

| Feature | 2017 theorem | OpenAI's simultaneous main | This repo's variant |
|---|---|---|---|
| Positive prime bases, e.g. $`\{2,3\}`$ | Covered | Covered | Covered |
| Positive composite bases, e.g. $`\{2,8\}`$ | Covered | Not covered | Covered |
| Fractions or negative bases | Covered when its conditions hold | Not covered | Not covered |
| External analytic assumptions | Hypothesis H | Four inputs | None |
| Conclusion | Infinitely many primes | At least $`c_A x/(\log x)^2`$ in $`(x,2x)`$ | At least $`c_A x/\log x`$ in $`(x,2x]`$ |

Thus the variant gives the positive-integer case without Hypothesis H, with a
quantitative lower bound. It does not cover the full rational-base theorem.

### How this repo strengthens OpenAI's main theorem

| | [OpenAI's main][openai-simultaneous] | Variant 1 | Variant 2 |
|---|---|---|---|
| Bases | Positive primes | Same positive primes | Integers $`\ge2`$ satisfying the square condition |
| External analytic assumptions | Four inputs | None | None |
| Lower bound | $`c_A x/(\log x)^2`$ | Same lower bound | $`c_A x/\log x`$ |
| Interval | $`(x,2x)`$ | Same interval | $`(x,2x]`$ |

Variant 1 is intended to remove only the four hypotheses from OpenAI's statement. It is proved
from Variant 2, which also broadens the allowed bases and strengthens the bound.

For distinct prime bases, the square condition holds automatically. The stronger
lower bound also gives OpenAI's bound after adjusting the constant and starting
point; the endpoint difference is at most one prime. Once the conclusion's
paper-to-Lean correspondence is confirmed, this gives OpenAI's conditional
conclusion. The four analytic inputs themselves are not proved here.

Positive density under GRH and the square condition were already known.
Priority for a first unconditional proof is not established; see [HISTORY.md](HISTORY.md).

## Appendix: why the square condition is needed

We want all numbers in $`A`$ to be primitive roots for the **same prime**.
The square condition says: **choose 1, 3, 5, … distinct numbers from $`A`$;
their product must never be a square.** Choosing just one number counts.

| Chosen numbers $`A`$ | Products of an odd number of elements | Square condition | Result |
|---|---|---|---|
| $`\{2,3\}`$ | 2 and 3: neither is a square | Holds | Many primes work, by the variant |
| $`\{2,8\}`$ | 2 and 8: neither is a square | Holds | Many primes work, by the variant |
| $`\{4\}`$ | $`4=2^2`$ | Fails | No odd prime works, by the supplementary theorem |
| $`\{2,3,6\}`$ | 2, 3, 6, and $`2\cdot3\cdot6=36=6^2`$ | Fails | No odd prime works, by the supplementary theorem |

In $`\{2,8\}`$, the product $`2\cdot8=16`$ causes no problem: it uses **two**
numbers, so the condition does not test it.

> **Supplementary theorem.** If the square condition fails, no odd prime makes
> every element of $`A`$ a primitive root.

Why? Modulo an odd prime, a product of an odd number of primitive roots cannot
be a square. But an integer square, such as 36, remains a square modulo that prime.
These two requirements cannot both hold.

[Lean statement](FClikelean/SquareConditionNecessary.lean) · [Lean proof](lean/Solution.lean).

## Appendix: history (AI generated)

| When | Who | What was proposed or proved? |
|---|---|---|
| 1927 | Artin | **Proposed a conjecture:** a fixed admissible integer should be a primitive root for infinitely many primes, with a predicted density ([history](https://www.mathi.uni-heidelberg.de/~roquette/hasse-artin/hasart-web-080922su43.html)). |
| 1967 | Hooley | **Proved under GRH:** Artin's predicted single-base density formula ([paper](https://doi.org/10.1515/crll.1967.225.209)). |
| 1976 | Matthews | **Proved under GRH:** a criterion for simultaneous integer bases to have infinitely many primes, with positive density ([account in the 2017 paper, p.35](https://www.impan.pl/shop/publication/transaction/download/product/92279#page=1)). |
| 2017 | Anwar–Pappalardi | **Proved under Hypothesis H:** simultaneous infinitude for rational bases satisfying the two conditions above ([Theorem, p.36](https://www.impan.pl/shop/publication/transaction/download/product/92279#page=2)). |
| 4 October 2026 | OpenAI | **Presented proofs:** a [single-base infinitude bound][openai-single] and a [conditional simultaneous bound for prime bases][openai-simultaneous], both of order $`x/(\log x)^2`$. |
| 15 October 2026 | This repo | **Formalized and locally checked in Lean:** the stronger simultaneous $`x/\log x`$ bound for positive integer bases satisfying the square condition, and the necessary-condition theorem ([record](ci/local-verification.json)). |

The 1927 entry is the original conjecture. The later entries are results related
to it; this repo does not prove Artin's predicted exact density.

## Appendix: Verification by Lean Comparator on GitHub CI runner

Comparator checks statements and dependent definitions against the reference,
audits permitted axioms and replays the solution in the builtin Lean kernel.
The prepared [Linux workflow](.github/workflows/lean.yml) checks the two submitted
variants with the pinned Landrun sandbox and uploads logs for the tested commit.
Compilation is staged across jobs for the same commit; the final comparison uses
the independent two-statement Challenge, the permitted-axiom audit and fresh
kernel replay. The reference and supplementary statements are not Comparator
targets in this configuration.

### Certification Within 30 days: CI results

The workflow retains verification logs for 30 days and temporary compilation
artifacts for one day.
Private Linux CI in [`KitaKen1/ci-test-sandbox`](https://github.com/KitaKen1/ci-test-sandbox)
and public Linux CI in
[`KitaKen1/simultaneous-primitive-roots`](https://github.com/KitaKen1/simultaneous-primitive-roots)
are tracked in [private Actions](https://github.com/KitaKen1/ci-test-sandbox/actions/workflows/lean.yml) and [public Actions](https://github.com/KitaKen1/simultaneous-primitive-roots/actions/workflows/lean.yml).
The current two-variant run is tracked in
[two-variant-review.json](ci/two-variant-review.json); earlier runs used different
target lists and do not certify this configuration.
The intended order is human review, private CI, then public CI on the reviewed sources.

### Certification After 30 days: archive

No CI archive exists yet. After successful runs, preserve the original artifact ZIPs,
complete job logs, run metadata, tested commit and SHA-256 checksums.
The current [local verification record](ci/local-verification.json) covers macOS checks only.

### Reproduce the verification

Build the reference and complete proof from the repository root:

```bash
bash scripts/build.sh
```

Check the two-theorem FC submission and the two separate reference files:

```bash
cd lean
lake build FClikelean.SimultaneousPrimitiveRoots FClikelean.OpenAIConditional FClikelean.SquareConditionNecessary
python3 ../scripts/check_fclike_standalone.py
```

From the repository root, run the macOS development comparison:

```bash
bash scripts/compare.sh local-development
```

For the full Linux checks, run the [verification workflow](.github/workflows/lean.yml)
in a repository you control. See the [verification guide](ci/README.md) for the pinned
environment, checking tools and sandbox setup.

[openai-simultaneous]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Simultaneous-primitive-roots-a-conditional-lower-bound-for-prime-bases-October-4-2026/simultaneous-primitive-roots-conditional-lower-bound-prime-bases.pdf#page=1
[openai-single]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Primitive-roots-for-every-admissible-integer-base-October-4-2026/primitive-roots-all-integer-bases.pdf#page=2
