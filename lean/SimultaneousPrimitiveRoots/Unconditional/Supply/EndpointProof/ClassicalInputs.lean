module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.ClassicalInputs

/-!
# The classical inputs of the proof of (cor:SM) ([P] §2)

The proof of the endpoint estimate (cor:SM) (`[P-06:0555–0925]`) quotes the following results of
[P] §2 (`verification/stage7-sources/P-02.tex`).

Already in the project (not restated):

* Lemma 2.1, Mertens for `∑ 1/p` (`[P-02:0039–0042]`): `MertensReciprocal`
  (`Supply/ClassicalInputs.lean`); it gives the band masses `V_i = log 2 + o(1)`
  (`[P-02:0060–0064]`).
* Lemma 2.2, divisor moments (`[P-02:0073–0080]`): `DivisorMoments`, proved (`divisorMoments`).
* Lemma 2.2, the two Dirichlet mean squares (eq:dirichlet-mean), (eq:dirichlet-spaced)
  (`[P-02:0081–0093]`): proved in `Unconditional/Classical/DirichletMeanSquare.lean`
  (`integral_normSq_dirichletPolynomial_le_nat`, `sum_normSq_dirichletPolynomial_le_nat` and the
  forms with real cutoffs); the vendored counterpart is
  `ArtinPrimitiveRoots.TypeII.PD.moment_bounds`.

Stated here, each as a `def … : Prop`:

* `LongPrimePolynomial`: Lemma 2.3 `lem:long-prime` (`[P-02:0124–0142]`).
* `LogPhase`: Lemma 2.4 `lem:log-phase` (`[P-02:0144–0158]`).
* `ModeratePhase`: (eq:moderate-phase) (`[P-02:0160–0173]`).
* `SmoothProgressionSum`: the first-order sum–integral comparison on a progression, the tool of
  (cor:low-main-term) (`[P-06:0653–0667]`: "Smooth sum–integral comparison on the progressions
  modulo `k`", "summing the endpoint and total-variation errors").

The first three are transcriptions of the vendored theorems
`ArtinPrimitiveRoots.TypeII.PP.prime_polynomial`, `ArtinPrimitiveRoots.TypeII.PP.log_phase`
(`vendor/ArtinPrimitiveRoots/TypeII/PP/Results.lean`) and
`ArtinPrimitiveRoots.TypeII.PD.moderate_phase`
(`vendor/ArtinPrimitiveRoots/TypeII/PD/Preliminaries.lean`), which are not modules and cannot be
imported here; the normalizations (ranges of summation, the phase `exp(i t log n)`, the reciprocal
weight `exp((-1 + i t) log p)`, `Real.rpow`) are theirs. Siegel–Walfisz and the rough counts of
Lemma 2.5 are not used in the proof of (cor:SM).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open Filter
open scoped Topology

noncomputable section

/-! ### Lemma 2.3: long prime polynomials -/

/-- **Long prime polynomial** (`[P-02:0124–0142]`, `lem:long-prime`): "Fix `0 < τ < η < 1` and
`C, A > 0`. There is `B_0 = B_0(τ, η, C, A)` such that, uniformly for `x^τ / 2 ≤ N ≤ x^η`,
`q ≤ L^C`, `L^{B_0} ≤ |t| ≤ x^2`, every Dirichlet character `χ` modulo `q` and every interval
`I ⊂ [N, 2N]` satisfy `|∑_{p ∈ I} χ(p) p^{-1+it}| ≪_{τ,η,C,A} L^{-A}`."

Expected supplier: `ArtinPrimitiveRoots.TypeII.PP.prime_polynomial`
(`vendor/ArtinPrimitiveRoots/TypeII/PP/Results.lean`, lines 1659–1671). The statement is the one
of that theorem specialized to the intervals `I = {p : N₁ ≤ p ≤ N₂}` with `N ≤ N₁`, `N₂ ≤ 2N`
(these are `IsNatInterval` sets inside `[N, 2N]`, and every interval of integers in `[N, 2N]` has
this form); the sum is `primeDirichletPolynomial N q χ t I` unfolded. The bridge is the
instantiation `I := {p | N₁ ≤ p ∧ p ≤ N₂}`. -/
def LongPrimePolynomial : Prop :=
  ∀ τ η C A : ℝ, 0 < τ → τ < η → η < 1 → 0 < C → 0 < A →
    ∃ B₀ C₀ x₀ : ℝ, 0 < B₀ ∧ 0 < C₀ ∧ 2 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
      ∀ N : ℝ, x ^ τ / 2 ≤ N → N ≤ x ^ η → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ C →
        ∀ (χ : DirichletCharacter ℂ q) (t : ℝ), Real.log x ^ B₀ ≤ |t| → |t| ≤ x ^ (2 : ℝ) →
          ∀ N₁ N₂ : ℝ, N ≤ N₁ → N₂ ≤ 2 * N →
            ‖∑ p ∈ (Finset.range (⌊2 * N⌋₊ + 1)).filter (fun p : ℕ =>
                  p.Prime ∧ N ≤ (p : ℝ) ∧ (p : ℝ) ≤ 2 * N ∧ N₁ ≤ (p : ℝ) ∧ (p : ℝ) ≤ N₂),
                χ (p : ZMod q) *
                  Complex.exp ((-1 + Complex.I * (t : ℂ)) * (Real.log (p : ℝ) : ℂ))‖ ≤
              C₀ * Real.log x ^ (-A)

/-! ### Lemma 2.4: logarithmic phases on progressions -/

/-- **Logarithmic phases on progressions** (`[P-02:0144–0158]`, `lem:log-phase`): "Fix `C > 0`.
There is an absolute constant `C_3 > 0` such that, for sufficiently large `x` in terms of `C`,
the following holds uniformly: `exp(L / (log L)^2) ≤ N ≤ 2x^5`, `q ≤ L^C`,
`exp(L / (2 (log L)^2)) ≤ |t| ≤ 4x^3`. For every residue `a (mod q)` and every interval
`I ⊂ [N, 2N]`, `|∑_{n ∈ I, n ≡ a (q)} n^{it}| ≪ (N/q) exp(-L / (log L)^{C_3})`." "The estimate
applies to arbitrary residue classes, not only units" (`[P-02:0161–0162]`).

Expected supplier: `ArtinPrimitiveRoots.TypeII.PP.log_phase`
(`vendor/ArtinPrimitiveRoots/TypeII/PP/Results.lean`, lines 37–50). This is that statement with
`residuePhaseSum N' q a v {n | N₁ ≤ n ∧ n ≤ N₂}` unfolded and `Real.rpow` written `^`; the bridge
is `fun … => log_phase …` up to unfolding. -/
def LogPhase : Prop :=
  ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ C : ℝ, 0 < C → ∃ C₀ x₀ : ℝ, 0 < C₀ ∧ 2 < x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
    ∀ N' : ℝ, Real.exp (Real.log x / Real.log (Real.log x) ^ 2) ≤ N' → N' ≤ 2 * x ^ (5 : ℝ) →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ C → ∀ (a : ZMod q) (v : ℝ),
        Real.exp (Real.log x / (2 * Real.log (Real.log x) ^ 2)) ≤ |v| → |v| ≤ 4 * x ^ (3 : ℝ) →
          ∀ N₁ N₂ : ℝ, N' ≤ N₁ → N₂ ≤ 2 * N' →
            ‖∑ n ∈ (Finset.range (⌊2 * N'⌋₊ + 1)).filter (fun n : ℕ =>
                  N' ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N' ∧ (N₁ ≤ (n : ℝ) ∧ (n : ℝ) ≤ N₂) ∧
                    (n : ZMod q) = a),
                Complex.exp (Complex.I * (v : ℂ) * (Real.log (n : ℝ) : ℂ))‖ ≤
              C₀ * (N' / (q : ℝ)) *
                Real.exp (-Real.log x / Real.log (Real.log x) ^ C₃)

/-! ### Moderate frequencies -/

/-- The sum `∑_{l ≤ n ≤ r, n ≡ a (q)} n^{it}`
(= `ArtinPrimitiveRoots.TypeII.PD.integerResiduePhaseSum q a t l r`). -/
def residuePhaseSum (q : ℕ) (a : ZMod q) (t l r : ℝ) : ℂ :=
  ∑ n ∈ (Finset.range (⌊r⌋₊ + 1)).filter (fun n : ℕ =>
      l ≤ (n : ℝ) ∧ (n : ℝ) ≤ r ∧ (n : ZMod q) = a),
    Complex.exp (Complex.I * (t : ℂ) * (Real.log (n : ℝ) : ℂ))

/-- **The elementary sum–integral comparison at moderate frequencies** (`[P-02:0160–0173]`,
(eq:moderate-phase)): "For `N ≥ x^δ`, `q ≤ L^C` and `1 ≤ |t| ≤ exp(L / (log L)^2)`, it gives
`(q/N) |∑_{n ∈ I, n ≡ a (q)} n^{it}| ≪ 1/|t| + x^{-c_δ}`. Indeed the integral is `O(N / (q|t|))`,
and the endpoint/total-variation error is `O(1 + |t|)`."

Expected supplier: `ArtinPrimitiveRoots.TypeII.PD.moderate_phase`
(`vendor/ArtinPrimitiveRoots/TypeII/PD/Preliminaries.lean`, lines 2267–2283). This is that
statement, with its three conclusions (comparison with the integral, the bound for the integral,
and (eq:moderate-phase)), `integerResiduePhaseSum` being `residuePhaseSum` above; the bridge is
`fun δ C hδ hC => moderate_phase δ C hδ hC` up to unfolding. -/
def ModeratePhase : Prop :=
  ∀ δ C : ℝ, 0 < δ → 0 < C → ∃ C₀ cδ x₀ : ℝ, 0 < C₀ ∧ 0 < cδ ∧ 2 ≤ x₀ ∧ ∀ x : ℝ, x₀ ≤ x →
    ∀ N : ℝ, x ^ δ ≤ N → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ C → ∀ (a : ZMod q) (t : ℝ),
      1 ≤ |t| → |t| ≤ Real.exp (Real.log x / Real.log (Real.log x) ^ 2) →
        ∀ l r : ℝ, N ≤ l → l ≤ r → r ≤ 2 * N →
          ‖residuePhaseSum q a t l r - ((1 / (q : ℂ)) *
              ∫ y in l..r, Complex.exp (Complex.I * (t : ℂ) * (Real.log y : ℂ)))‖ ≤
            C₀ * (1 + |t|) ∧
          ‖∫ y in l..r, Complex.exp (Complex.I * (t : ℂ) * (Real.log y : ℂ))‖ ≤ C₀ * N / |t| ∧
          ((q : ℝ) / N) * ‖residuePhaseSum q a t l r‖ ≤ C₀ * (|t|⁻¹ + x ^ (-cδ))

/-! ### Smooth sums over a progression -/

/-- **First-order sum–integral comparison on a progression** (Euler–Maclaurin of order one; the
tool of `[P-06:0653–0667]` and of `[P-02:0169–0173]`: "the endpoint/total-variation error", "The
same estimate holds after partial summation against a smooth factor"). For a continuously
differentiable compactly supported `F` vanishing on `(-∞, 0]`, a modulus `k ≥ 1` and a residue
`a`,

`|∑_{n ≥ 0, n ≡ a (k)} F(n) - (1/k) ∫ F| ≤ ∫ |F'|`.

(With `G(y) = F(a' + k y)`, `a' = a mod k`: `∑_{m ≥ -1} G(m) - ∫_{-1}^∞ G = ∑_m (G(m) -
∫_m^{m+1} G)` and `|G(m) - ∫_m^{m+1} G| ≤ ∫_m^{m+1} |G'|`; the constant `1/2` also holds.)

No vendored theorem has this form; the proof of `ArtinPrimitiveRoots.TypeII.PD.moderate_phase`
(`…/Proofs/pd0/ModeratePhase.lean`) contains the comparison for the phase `y^{it}`, and Mathlib has
Abel summation (`sum_mul_eq_sub_sub_integral_mul`). It is elementary. -/
def SmoothProgressionSum : Prop :=
  ∀ F : ℝ → ℂ, ContDiff ℝ 1 F → HasCompactSupport F → (∀ u : ℝ, u ≤ 0 → F u = 0) →
    ∀ k : ℕ, 0 < k → ∀ a : ℕ,
      ‖(∑ᶠ n : ℕ, if n ≡ a [MOD k] then F (n : ℝ) else 0) - ((k : ℂ)⁻¹ * ∫ u : ℝ, F u)‖ ≤
        ∫ u : ℝ, ‖deriv F u‖

/-! ### The inputs together -/

/-- The classical inputs of the proof of (cor:SM) that are not theorems of the module part of the
project: Mertens' estimate for `∑ 1/p`, the smooth sum over a progression, the long prime
polynomial, and the two phase estimates. -/
structure EndpointClassicalInputs : Prop where
  /-- [P] Lemma 2.1, Mertens (`OAI.JointDickman.primeReciprocalMertensInput`) -/
  mertens : MertensReciprocal
  /-- first-order Euler–Maclaurin on a progression -/
  smoothSum : SmoothProgressionSum
  /-- [P] Lemma 2.3 (`ArtinPrimitiveRoots.TypeII.PP.prime_polynomial`) -/
  longPrime : LongPrimePolynomial
  /-- [P] Lemma 2.4 (`ArtinPrimitiveRoots.TypeII.PP.log_phase`) -/
  logPhase : LogPhase
  /-- (eq:moderate-phase) (`ArtinPrimitiveRoots.TypeII.PD.moderate_phase`) -/
  moderatePhase : ModeratePhase

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
