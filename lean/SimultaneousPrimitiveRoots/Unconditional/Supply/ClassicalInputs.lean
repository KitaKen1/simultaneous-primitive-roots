module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Basic
public import SimultaneousPrimitiveRoots.Unconditional.Classical.DivisorMoments
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# The classical inputs of the prime extraction ([P] §2)

[P] §7 (the passage from the two correlation theorems to the prime statistic) uses the following
results of [P] §2 (`verification/stage7-sources/P-02.tex`). They are stated here as propositions
so that the reduction of `Supply/Reduction.lean` can name them as hypotheses.

* Lemma 2.1, Siegel–Walfisz: `SiegelWalfiszPrimeCounting`. Proved by
  `SimultaneousPrimitiveRoots.Classical.siegelWalfisz_primeCounting`
  (`SimultaneousPrimitiveRootsFinal/Classical/SiegelWalfiszPrimes.lean`, not a module).
* Lemma 2.1, Mertens for `∑ 1/p`: `MertensReciprocal`. Proved by
  `OAI.JointDickman.primeReciprocalMertensInput`
  (`vendor/OAI/NumberTheory/JointDickman/Arithmetic/MertensDischarge.lean`, not a module).
* Lemma 2.1, Mertens for `∏ (1 - 1/p)`: `MertensProduct`. Proved by
  `OAI.JointDickman.primeProductMertensInput` (same file).
* Lemma 2.2, divisor moments: `DivisorMoments`. Proved here (`divisorMoments`) from
  `Unconditional/Classical/DivisorMoments.lean`.
* Lemma 2.5, rough integers: `RoughCounts`. Not yet proved in Lean.
* Lemma 2.6, block sieve: `BlockSieve`. Not yet proved in Lean in this form ([S] `lem:sieve`; a
  related vendored statement is `OAI … FundamentalBlockEstimate.fundamental_integer_parameter`).

The first three are copies of the statements of the named theorems (with `logIntegral` for the
`Li` of the first file), because non-module files cannot be imported here.

Not listed: the Dirichlet mean squares of Lemma 2.2 and Lemmas 2.3, 2.4 (long prime polynomials,
logarithmic phases). They are inputs of [P] Lemma 5.2 and of (cor:SM), not of §7 itself.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply

open Filter
open scoped Topology

noncomputable section

/-! ### Lemma 2.1: primes -/

/-- The logarithmic integral `Li y = ∫₂^y dt / log t`
(= `SimultaneousPrimitiveRoots.Classical.Li`). -/
def logIntegral (y : ℝ) : ℝ := ∫ t in (2 : ℝ)..y, 1 / Real.log t

/-- **Siegel–Walfisz, prime-counting form** (`[P-02:0046–0053]`, `lem:prime-estimates`; [S]
`thm:sw`): for fixed `A, C > 0`, uniformly for `r ≤ (log y)^C` and `(a, r) = 1`,
`#{p ≤ y : p ≡ a (mod r)} = Li(y)/φ(r) + O_{A,C}(y / (log y)^A)`. With `r = 1` this is the prime
number theorem with an error term below any fixed power of `1 / log y`.

This is the statement of `SimultaneousPrimitiveRoots.Classical.siegelWalfisz_primeCounting`
(`SimultaneousPrimitiveRootsFinal/Classical/SiegelWalfiszPrimes.lean`, lines 612–617), which
proves it. -/
def SiegelWalfiszPrimeCounting : Prop :=
  ∀ A C : ℝ, 0 < A → 0 < C → ∃ M : ℝ, 0 < M ∧ ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
    ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ Real.log y ^ C → ∀ a : ℕ, Nat.Coprime a r →
      |(((Finset.Iic ⌊y⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD r])).card : ℝ) -
          logIntegral y / (r.totient : ℝ)| ≤ M * y * Real.log y ^ (-A)

/-- **Mertens' estimate for `∑ 1/p`** (`[P-02:0039–0042]`:
`∑_{p ≤ y} 1/p = log log y + c_M + o(1)`), in the classical strength `O(1 / log y)`.

This is the statement `OAI.JointDickman.PublishedInputs.PrimeReciprocalMertensInput`, proved by
`OAI.JointDickman.primeReciprocalMertensInput`
(`vendor/OAI/NumberTheory/JointDickman/Arithmetic/MertensDischarge.lean`). It gives the band
masses `∑_{exp(L^a) ≤ p ≤ exp(2L^a)} 1/p = log 2 + o(1)` of `[P-02:0060–0064]`. -/
def MertensReciprocal : Prop :=
  ∃ M C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
    |(∑ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime, 1 / (p : ℝ)) -
      Real.log (Real.log x) - M| ≤ C / Real.log x

/-- **Mertens' product theorem** (`[P-02:0043–0045]`:
`∏_{p ≤ y} (1 - 1/p) ∼ e^{-γ_E} / log y`).

This is the statement `OAI.JointDickman.PublishedInputs.PrimeProductMertensInput`, proved by
`OAI.JointDickman.primeProductMertensInput` (same file). -/
def MertensProduct : Prop :=
  Tendsto (fun x : ℝ => Real.log x *
    ∏ p ∈ (Finset.Icc 2 ⌊x⌋₊).filter Nat.Prime, (1 - 1 / (p : ℝ)))
    atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant)))

/-! ### Lemma 2.2: divisor moments -/

/-- **Divisor moments** (`[P-02:0073–0080]`, `lem:moment-bounds`): for every fixed `k`,
`∑_{n ≤ Y} τ(n)^k ≪_k Y (log 2Y)^{C_k}` and `∑_{n ≤ Y} τ(n)^k / n ≪_k (log 2Y)^{C_k}`. -/
def DivisorMoments : Prop :=
  ∀ k : ℕ,
    (∃ C A : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y →
      ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n.divisors.card : ℝ) ^ k ≤ C * Y * Real.log (2 * Y) ^ A) ∧
    (∃ C A : ℝ, 0 < C ∧ ∀ Y : ℝ, 1 ≤ Y →
      ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n.divisors.card : ℝ) ^ k / (n : ℝ) ≤ C * Real.log (2 * Y) ^ A)

/-- The divisor moments are proved in `Unconditional/Classical/DivisorMoments.lean`. -/
theorem divisorMoments : DivisorMoments := fun k =>
  ⟨SimultaneousPrimitiveRoots.Unconditional.Classical.sum_divisorCount_pow_le k,
    SimultaneousPrimitiveRoots.Unconditional.Classical.sum_divisorCount_pow_div_le k⟩

/-! ### Lemma 2.5: rough integers -/

open _root_.Classical in
/-- **Rough integers in long intervals** (`[P-02:0177–0196]`, `lem:rough-counts`). Fix `δ > 0`,
`C > 0`, `0 < a < 1` and `A > 0`. For `x^δ ≤ H ≤ x^C` and an interval `I ⊆ [H, 2H]`:

* (eq:rough-count) `#{n ∈ I : P⁻(n) > W} = V(W) |I| + O(H L^{-A})`;
* (eq:rough-off-sieve-progression) if `d ≤ exp(L^a)` and every prime divisor of `d` exceeds `W`,
  then for every residue `b (mod d)`,
  `#{n ∈ I : n ≡ b (mod d), P⁻(n) > W} = V(W) |I| / d + O((H/d) L^{-A})`;
* (eq:rough-character) for every character `χ` modulo `q ≤ L^C`,
  `∑_{n ∈ I, P⁻(n) > W} χ(n) = 1_{χ principal} V(W) |I| + O(H L^{-A})`.

The statements are uniform in the intervals and in the residues; the constant `M` and the
threshold `x₀` depend on `δ, C, a, A`.

Choice: the interval is the closed interval `[lo, hi]` with `H ≤ lo ≤ hi ≤ 2H` and
`|I| = hi - lo`. Open or half-open intervals change each count by at most `2`, which is
`O((H/d) L^{-A})` for large `x` (`H ≥ x^δ`, `d ≤ exp(L^a)`). -/
def RoughCounts : Prop :=
  ∀ δ C a A : ℝ, 0 < δ → 0 < C → 0 < a → a < 1 → 0 < A →
    ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ H : ℝ, x ^ δ ≤ H → H ≤ x ^ C →
      ∀ lo hi : ℝ, H ≤ lo → lo ≤ hi → hi ≤ 2 * H →
        (|(((Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter fun n => IsRough (roughCutoff x) n).card : ℝ) -
            mertensProduct (roughCutoff x) * (hi - lo)| ≤ M * H * Real.log x ^ (-A)) ∧
        (∀ d : ℕ, 0 < d → (d : ℝ) ≤ Real.exp (Real.log x ^ a) →
          IsRough (roughCutoff x) d → ∀ b : ℕ,
            |(((Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter fun n =>
                n ≡ b [MOD d] ∧ IsRough (roughCutoff x) n).card : ℝ) -
              mertensProduct (roughCutoff x) * (hi - lo) / (d : ℝ)| ≤
                M * (H / (d : ℝ)) * Real.log x ^ (-A)) ∧
        (∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.log x ^ C → ∀ χ : DirichletCharacter ℂ q,
          ‖(∑ n ∈ (Finset.Icc ⌈lo⌉₊ ⌊hi⌋₊).filter fun n => IsRough (roughCutoff x) n,
                χ (n : ZMod q)) -
              (if χ = 1 then ((mertensProduct (roughCutoff x) * (hi - lo) : ℝ) : ℂ) else 0)‖ ≤
            M * H * Real.log x ^ (-A))

/-! ### Lemma 2.6: the block sieve -/

open _root_.Classical in
/-- The total weight of the objects of `Ω` on which all the bad conditions at the primes of `D`
hold (`D = ∅`: the total weight). -/
def sieveWeight (Ω : Finset ℕ) (wt : ℕ → ℝ) (bad : ℕ → ℕ → Prop) (D : Finset ℕ) : ℝ :=
  ∑ i ∈ Ω.filter (fun i => ∀ p ∈ D, bad p i), wt i

open _root_.Classical in
/-- The total weight of the objects of `Ω` avoiding all the bad conditions at the primes of
`primes`. -/
def siftedWeight (Ω : Finset ℕ) (wt : ℕ → ℝ) (bad : ℕ → ℕ → Prop) (primes : Finset ℕ) : ℝ :=
  ∑ i ∈ Ω.filter (fun i => ∀ p ∈ primes, ¬ bad p i), wt i

/-- The sieve remainder `r(d) = (weight on which all conditions at `p ∣ d` hold) - X g(d)` for the
squarefree `d = ∏_{p ∈ D} p` and the multiplicative density `g(d) = ∏_{p ∈ D} g(p)`
(`[P-02:0242–0247]`). -/
def sieveRemainder (Ω : Finset ℕ) (wt : ℕ → ℝ) (bad : ℕ → ℕ → Prop) (X : ℝ) (g : ℕ → ℝ)
    (D : Finset ℕ) : ℝ :=
  sieveWeight Ω wt bad D - X * ∏ p ∈ D, g p

/-- `∑_{d ≤ y, d squarefree} |r(d)|` over the products `d` of designated primes
(`[P-02:0257–0260]`). -/
def sieveRemainderSum (Ω : Finset ℕ) (wt : ℕ → ℝ) (bad : ℕ → ℕ → Prop) (X : ℝ) (g : ℕ → ℝ)
    (primes : Finset ℕ) (y : ℝ) : ℝ :=
  ∑ D ∈ primes.powerset.filter (fun D => ((∏ p ∈ D, p : ℕ) : ℝ) ≤ y),
    |sieveRemainder Ω wt bad X g D|

/-- **The block sieve** (`[P-02:0239–0264]`, `lem:block-sieve`; [S] `lem:sieve`). Finitely many
objects `i ∈ Ω` with weights `wt i ≥ 0`, a level `z ≥ 1`, a set `primes` of designated primes
`≤ z`, a bad condition
`bad p i` at each designated prime, `X ≥ 0`, and a density `g` with `0 ≤ g(p) ≤ 1 - η₀` and
`∑_{w < p ≤ w²} g(p) ≤ C₀` for all `w > 1`. Then for every sufficiently large even `h`,

`(weight avoiding all bad conditions) = X ∏_{p ∈ primes} (1 - g(p)) (1 + O(e^{-h}))
  + O(∑_{d ≤ z^{4h+2}, d squarefree} |r(d)|)`,

and for `h = 2` there is the upper bound by a constant times the main term plus the remainder sum
up to `z^{10}`. The constants are determined by the density bounds alone, uniformly in `h`: `M`
and `h₀` depend only on `η₀, C₀`.

Choices: the finitely many objects are indexed by natural numbers; the squarefree `d` composed of
designated primes is the subset `D ⊆ primes` of its prime factors.

The hypothesis `1 ≤ z` is needed: the paper's remainder sums contain `d = 1`
(`[P-02:0247]`), which in this formulation requires `1 ≤ z ^ (4 * h + 2)` and `1 ≤ z ^ 10`. Without
it the statement is false (`z = 0`, no designated primes, one object of weight `1`, `X = 0`); the
independent review of 2026-10-12 proved the negation of the earlier version in Lean. -/
def BlockSieve : Prop :=
  ∀ η₀ C₀ : ℝ, 0 < η₀ → ∃ M : ℝ, ∃ h₀ : ℕ,
    ∀ (Ω : Finset ℕ) (wt : ℕ → ℝ), (∀ i ∈ Ω, 0 ≤ wt i) →
      ∀ (z : ℝ) (primes : Finset ℕ), 1 ≤ z → (∀ p ∈ primes, p.Prime ∧ (p : ℝ) ≤ z) →
        ∀ (bad : ℕ → ℕ → Prop) (X : ℝ), 0 ≤ X →
          ∀ g : ℕ → ℝ, (∀ p ∈ primes, 0 ≤ g p ∧ g p ≤ 1 - η₀) →
            (∀ w : ℝ, 1 < w →
              ∑ p ∈ primes.filter (fun p : ℕ => w < (p : ℝ) ∧ (p : ℝ) ≤ w ^ 2), g p ≤ C₀) →
            (∀ h : ℕ, h₀ ≤ h → Even h →
              |siftedWeight Ω wt bad primes - X * ∏ p ∈ primes, (1 - g p)| ≤
                M * Real.exp (-(h : ℝ)) * (X * ∏ p ∈ primes, (1 - g p)) +
                  M * sieveRemainderSum Ω wt bad X g primes (z ^ (4 * h + 2))) ∧
            siftedWeight Ω wt bad primes ≤
              M * (X * ∏ p ∈ primes, (1 - g p)) +
                M * sieveRemainderSum Ω wt bad X g primes (z ^ 10)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply
