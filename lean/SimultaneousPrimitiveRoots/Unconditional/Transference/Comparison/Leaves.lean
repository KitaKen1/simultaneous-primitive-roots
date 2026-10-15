module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.IdealFamily

/-!
# The general inputs of the comparison kernel lemma ([S] Lemma 4.3)

Source: `verification/stage7-sources/S-03.tex` (`[S-03:…]`).

The proof of Lemma 4.3 [S-03:0270–0437] uses five facts that do not involve the prime groups.
They are stated here as propositions, so that the proof of the lemma from them
(`Comparison/…`) and their own proofs can be written independently.

* `IntegerBilinear` — Lemma 4.2, the integer bilinear estimate [S-03:0110–0161].
* `ReciprocalPrimeCharacterSum` — the reciprocal sum of a nonprincipal character over the primes
  of an interval, from Siegel–Walfisz [S-03:0218–0237].
* `RationalPhaseExpansion` — the expansion of `v ↦ e(uv/r)` in the characters modulo `r`
  (eq:ideal-rational-expansion) [S-03:0340–0351].
* `PrimitiveInduction` — "the unique primitive character inducing `ψ` has conductor at most `r`"
  [S-03:0349–0351].
* `GramFrameBound` — the norm of a frame operator whose Gram matrix is close to the identity
  (eq:ideal-frame), (eq:ideal-gram-bound) [S-03:0241–0256].
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

/-- **[S] Lemma 4.2 (integer bilinear estimate)** [S-03:0110–0161].

"Let `U, V ≥ 1`. Suppose `a_n, b_t` are supported in integer intervals of lengths at most
`C U, C V`, respectively, where `C` is fixed. If `α = u/r + β`, `(u, r) = 1`, `r ≥ 1`,
`|β| ≤ r⁻²`, then
`|∑_{n,t} a_n b_t e(α n t)| ≪_C ‖a‖ ‖b‖ [U + (1 + V/r){U + r log(2r)}]^{1/2}`.
The containing intervals need not begin at `1`, and the coefficients may vanish on arbitrary
subsets of them."

Here the supports are finite sets `s ⊆ [N, N + C U]`, `t ⊆ [T, T + C V]` of natural numbers. -/
def IntegerBilinear : Prop :=
  ∀ C : ℝ, 0 < C → ∃ K : ℝ, 0 < K ∧
    ∀ U V : ℝ, 1 ≤ U → 1 ≤ V →
    ∀ (s t : Finset ℕ) (N T : ℕ),
      (∀ n ∈ s, N ≤ n ∧ (n : ℝ) ≤ N + C * U) → (∀ k ∈ t, T ≤ k ∧ (k : ℝ) ≤ T + C * V) →
    ∀ (a b : ℕ → ℂ) (α β : ℝ) (u : ℤ) (r : ℕ), 0 < r → IsCoprime u (r : ℤ) →
      α = (u : ℝ) / (r : ℝ) + β → |β| ≤ ((r : ℝ) ^ 2)⁻¹ →
      ‖∑ n ∈ s, ∑ k ∈ t, a n * b k * expUnit (α * (n : ℝ) * (k : ℝ))‖ ≤
        K * Real.sqrt (∑ n ∈ s, ‖a n‖ ^ 2) * Real.sqrt (∑ k ∈ t, ‖b k‖ ^ 2) *
          Real.sqrt (U + (1 + V / (r : ℝ)) * (U + (r : ℝ) * Real.log (2 * (r : ℝ))))

/-- **Reciprocal prime sums of a nonprincipal character** [S-03:0218–0237].

"For every fixed `K`, Theorem `thm:sw`, summed against the character over reduced residue classes
and applied with a larger accuracy exponent, gives `A_ρ(t) := ∑_{p ≤ t} ρ(p) ≪_K t (log t)^{-K}`
for these nonprincipal characters, uniformly for `t ≥ y`. The allowed modulus is a fixed power of
`log y`. Partial summation on any subinterval of `[y, ∞)` bounds its reciprocal-prime sum by
`O_K((log y)^{1-K})`."

For fixed `K, C > 0`: uniformly for `y` large, moduli `q ≤ (log y)^C`, nonprincipal `ρ` modulo `q`
and intervals `[lo, hi]` of natural numbers with `y ≤ lo`,
`|∑_{lo ≤ p ≤ hi} ρ(p)/p| ≤ M (log y)^{-K}`. -/
def ReciprocalPrimeCharacterSum : Prop :=
  ∀ K C : ℝ, 0 < K → 0 < C → ∃ M y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
    ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.log y ^ C → ∀ ρ : DirichletCharacter ℂ q, ρ ≠ 1 →
    ∀ lo hi : ℕ, y ≤ (lo : ℝ) →
      ‖∑ p ∈ (Finset.Icc lo hi).filter Nat.Prime, ρ (p : ZMod q) / (p : ℂ)‖ ≤
        M * Real.log y ^ (-K)

/-- **Fourier expansion on the units modulo `r`** (eq:ideal-rational-expansion) [S-03:0340–0351]:
`e(uv/r) = ∑_{ψ mod r} c_ψ ψ(v)` for `v` prime to `r`, with `∑_ψ |c_ψ| ≤ √φ(r)`.

"In normalized counting measure the left side has squared norm `1`, so Parseval gives
`∑ |c_ψ|² = 1` and Cauchy–Schwarz proves the stated bound." -/
def RationalPhaseExpansion : Prop :=
  ∀ (r : ℕ) (u : ℤ), 0 < r →
    ∃ c : DirichletCharacter ℂ r → ℂ, (∑ ψ, ‖c ψ‖ ≤ Real.sqrt (r.totient : ℝ)) ∧
      ∀ v : ℕ, Nat.Coprime v r →
        expUnit ((u : ℝ) * (v : ℝ) / (r : ℝ)) = ∑ ψ, c ψ * ψ (v : ZMod r)

/-- **Primitive induction** [S-03:0349–0351]: a character `ψ` modulo `r` agrees, on the integers
prime to `r`, with a primitive character whose conductor divides `r`. -/
def PrimitiveInduction : Prop :=
  ∀ (r : ℕ) (ψ : DirichletCharacter ℂ r), 0 < r →
    ∃ (r₀ : ℕ) (χ : DirichletCharacter ℂ r₀), 0 < r₀ ∧ r₀ ∣ r ∧ χ.IsPrimitive ∧
      ∀ v : ℕ, Nat.Coprime v r → ψ (v : ZMod r) = χ (v : ZMod r₀)

/-- **The frame operator of an almost orthonormal family** (eq:ideal-frame),
(eq:ideal-gram-bound) [S-03:0241–0256]: if finitely many functions `φ_i` of `L²(X, w)` have
`‖φ_i‖ ≤ 1` and `|⟨φ_i, φ_j⟩| ≤ ε` for `i ≠ j`, then `f ↦ ∑_i φ_i ⟨φ_i, f⟩` has norm at most
`1 + N ε`, `N` the number of functions. ("Its nonzero eigenvalues are those of the character Gram
matrix.") The weights are only assumed nonnegative, so that `w` may be a conditional measure. -/
def GramFrameBound : Prop :=
  ∀ (X : Type) [Fintype X] (w : X → ℝ), (∀ x, 0 ≤ w x) →
  ∀ (ι : Type) [Fintype ι] (φ : ι → X → ℂ) (ε : ℝ), 0 ≤ ε →
    (∀ i, wNormSq w (φ i) ≤ 1) → (∀ i j, i ≠ j → ‖wInner w (φ i) (φ j)‖ ≤ ε) →
    ∀ f : X → ℂ,
      wNorm w (fun x => ∑ i, φ i x * wInner w (φ i) f) ≤
        (1 + (Fintype.card ι : ℝ) * ε) * wNorm w f

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
