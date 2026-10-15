module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Statements
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Leaves
public import Mathlib.Data.Nat.Log

/-!
# The intermediate statements of the proof of [S] Lemma 4.3 (comparison kernel)

Source: `verification/stage7-sources/S-03.tex` (`[S-03:…]`), lines 76–437: the preparations
[S-03:0076–0268] and the proof of `lem:comparison-kernel` [S-03:0294–0437].

Every statement is a `def … : Prop`; nothing is proved here. `L = log x`, `T = log L`, and every
statement has the shape "constants in the paper's order, then `∃ x₀, ∀ x ≥ x₀`, then everything
that may vary with `x`", as in `Transference/Statements.lean`.

## The statements and how they depend on each other

* `ScaleLowerBound` — "the two scales exceed every fixed power of `L`" [S-03:0327], "all selected
  primes exceed `Q²` for large `x`" [S-03:0251–0252], "`Z/S → ∞`" [S-03:0312].
* `ProductAtomBound` — (eq:ideal-product-atom) [S-03:0079–0096].
* `CollapseBound` — (eq:ideal-collapse) [S-03:0098–0108]; from `ProductAtomBound`.
* `ProbabilityBilinear` — (eq:ideal-probability-bilinear) [S-03:0163–0174]; from `CollapseBound`
  and `IntegerBilinear`.
* `CharacterCell` — (eq:ideal-character-cell) [S-03:0208–0241]; from
  `ReciprocalPrimeCharacterSum` and the uniqueness of primitive induction.
* `KernelNorm` — "kernel integration on the full label space has norm at most `2`"
  [S-03:0243–0266]; from `CharacterCell` and `GramFrameBound`.
* `CharacterReproduction` — (eq:ideal-character-reproduction) [S-03:0391–0403]; from
  `CharacterCell` and `PrimitiveInduction`.
* `MinorArcBound` — one pair of dyads, `r > Q` [S-03:0316–0337]; from `ProbabilityBilinear`,
  `KernelNorm` and `ScaleLowerBound`.
* `MajorArcBound` — one pair of dyads, `r ≤ Q` [S-03:0339–0412]; from `CharacterReproduction`,
  the kernel costs (eq:ideal-cell-costs) and `RationalPhaseExpansion`.
* `DyadicSummation` — the splitting into dyads [S-03:0295–0302].

The assembly (`Comparison/Assembly.lean`) proves `ComparisonKernelLemma` from `ScaleLowerBound`,
`DyadicSummation`, `MinorArcBound` and `MajorArcBound`, with the Dirichlet approximation
(eq:ideal-dirichlet) [S-03:0304–0314] and the choice of the exponents [S-03:0414–0437].

## The order of the constants (the "noncircular choice of parameters", [S-03:0414–0437])

`P, m, A₀, C₄ ⟶ κ ⟶ B₀ ⟶ q_*, s_* ⟶ h_* ⟶ x_* ⟶ D_* ⟶ x₀`. The exponent `κ` is the explicit
`atomExponent P m`. `B₀, q_*, s_*, h_*, x_*` are the explicit `dyadExponent`, `arcExponent` (twice),
`cellExponent`, `massExponent`. The statements `MinorArcBound`, `MajorArcBound` are for all
exponents satisfying the inequalities of (eq:ideal-parameter-order). The character precision `D_*`
is chosen last: `CharacterCell` holds for every `D_*`, and `KernelNorm`, `CharacterReproduction`
hold for all exponents `q_*, h_*, x_* ≥ 0` (their proofs choose `D_*` in terms of these and of the
required precision). None of the constants depends on `J`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ### The exponents -/

/-- **The exponent `κ` of (eq:ideal-product-atom)** [S-03:0089]:
`κ = C₀ (log(m!) + m log max(1, v₋⁻¹))`. "In particular, this exponent does not depend on `J`"
[S-03:0096]. -/
def atomExponent (P : GroupParams) (m : ℕ) : ℝ :=
  P.C₀ * (Real.log (m.factorial : ℝ) + (m : ℝ) * Real.log (max 1 P.vMinus⁻¹))

/-- **`B₀`**, the precision on one pair of dyads: "`B₀ > A₀ + 2(d+1) + 10`" [S-03:0423]. -/
def dyadExponent (P : GroupParams) (A₀ : ℝ) : ℝ := A₀ + 2 * (P.d + 1) + 11

/-- **`q_* = s_*`**, the exponents of `Q = L^{q_*}` and `S = L^{s_*}`:
"`q_*, s_* > 2(B₀ + κ + 10) + d + 1`" [S-03:0424]. -/
def arcExponent (P : GroupParams) (m : ℕ) (A₀ : ℝ) : ℝ :=
  2 * (dyadExponent P A₀ + atomExponent P m + 10) + P.d + 2

/-- **`h_*`**, the exponent of `h = L^{-h_*}`:
"`h_* > 4 q_* + max(s_*, C₄) + B₀ + 10`" [S-03:0425]. -/
def cellExponent (P : GroupParams) (m : ℕ) (A₀ C₄ : ℝ) : ℝ :=
  4 * arcExponent P m A₀ + max (arcExponent P m A₀) C₄ + dyadExponent P A₀ + 11

/-- **`x_*`**, the exponent of `ξ = L^{-x_*}`:
"`x_* > 2 B₀ + d + 1 + h_* + 10`" [S-03:0426]. -/
def massExponent (P : GroupParams) (m : ℕ) (A₀ C₄ : ℝ) : ℝ :=
  2 * dyadExponent P A₀ + P.d + 1 + cellExponent P m A₀ C₄ + 11

/-! ### The objects of [S-03:0076–0268] -/

section Objects

variable {B : Type} [Fintype B] [DecidableEq B] {J : ℕ}

/-- `ρ_Λ(n) = ℙ(P_Λ = n)`, the law of the product of a label tuple of type `Λ` [S-03:0085]. -/
def atomMass (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) (n : ℕ) : ℝ :=
  ∑ t : AuxList big Λ, if tupleProd Λ t = n then auxWeight big Λ t else 0

/-- `a_n = E[f 1_{P_Λ = n}]`, the collapse of a tuple test to the values of the product
[S-03:0099–0101]. -/
def fiberCoeff (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) (F : AuxList big Λ → ℂ) (n : ℕ) : ℂ :=
  ∑ t : AuxList big Λ, if tupleProd Λ t = n then (auxWeight big Λ t : ℂ) * F t else 0

/-- "The probability-space bilinear form with phase `e(α P_A P_B)`", "with the phase multiplied by
`(P_A P_B)^{iζ}`" [S-03:0163–0174]: `E F(X_B) G(X_A) (X_A X_B)^{iζ} e(α X_A X_B)` for independent
tuples `X_A`, `X_B` of types `A`, `B`. It is bilinear (no conjugation). -/
def phaseForm (big : B → Finset ℕ) (A Bs : B → Finset (Fin J)) (F : AuxList big Bs → ℂ)
    (G : AuxList big A → ℂ) (α ζ : ℝ) : ℂ :=
  ∑ xA : AuxList big A, ∑ xB : AuxList big Bs,
    ((auxWeight big A xA * auxWeight big Bs xB : ℝ) : ℂ) * (F xB * G xA) *
      dilPhase ζ α (tupleProd A xA * tupleProd Bs xB)

/-- **Kernel integration in the variable `D`** [S-03:0243–0249]: `(𝒦f)(X) = E_D 𝒦_Λ(D, X) f(D)`,
"the integral operator defined by (eq:ideal-cell-kernel)", on a retained cell "the character frame
operator on the conditional probability space" (eq:ideal-frame). -/
def kernelIntD (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) (Q h ξ : ℝ)
    (F : AuxList big Λ → ℂ) : AuxList big Λ → ℂ := fun x =>
  ∑ d : AuxList big Λ, (auxWeight big Λ d : ℂ) *
    (cellKernel big Λ Q h ξ (tupleProd Λ d) (tupleProd Λ x) * F d)

/-- **Kernel integration in the variable `X`**, the transpose of `kernelIntD` [S-03:0263–0265]:
`(𝒦ᵗg)(D) = E_X 𝒦_Λ(D, X) g(X)`. This is the integration "moved onto the tests" in the comparison
term [S-03:0318–0319]. -/
def kernelIntX (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) (Q h ξ : ℝ)
    (G : AuxList big Λ → ℂ) : AuxList big Λ → ℂ := fun d =>
  ∑ x : AuxList big Λ, (auxWeight big Λ x : ℂ) *
    (cellKernel big Λ Q h ξ (tupleProd Λ d) (tupleProd Λ x) * G x)

/-- The test `F` on the tuples of type `Λ` is supported on the dyad `P_Λ ∈ [2^a, 2^{a+1})`
[S-03:0295–0296]. -/
def DyadSupported (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) (a : ℕ)
    (F : AuxList big Λ → ℂ) : Prop :=
  ∀ t : AuxList big Λ, F t ≠ 0 → Nat.log 2 (tupleProd Λ t) = a

end Objects

/-- **The Dirichlet approximation (eq:ideal-dirichlet)** [S-03:0304–0311]:
"a reduced fraction satisfying `α = u/r + β`, `1 ≤ r ≤ Z/S`, `|β| ≤ r⁻²`, `|β| Z ≤ 2S/r`". -/
def DirichletData (α Z S : ℝ) (u : ℤ) (r : ℕ) (β : ℝ) : Prop :=
  0 < r ∧ IsCoprime u (r : ℤ) ∧ α = (u : ℝ) / (r : ℝ) + β ∧ (r : ℝ) ≤ Z / S ∧
    |β| ≤ ((r : ℝ) ^ 2)⁻¹ ∧ |β| * Z ≤ 2 * S / (r : ℝ)

/-! ### The sizes of the primes and of the products -/

/-- **The big primes and the selected products exceed every fixed power of `L`**: "the two scales
exceed every fixed power of `L`" [S-03:0327]; "all selected primes exceed `Q²` for large `x`"
[S-03:0251–0252]; "`Z/S → ∞`" [S-03:0312]. Every big prime is at least `exp(L^c)`
(eq:prime-group-ranges), and a product over a nonempty slot set is at least one of its labels. -/
def ScaleLowerBound : Prop :=
  ∀ (P : GroupParams) (E : ℝ), ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B),
      (∀ (g : B) (p : ℕ), p ∈ 𝔊.big g → Real.log x ^ E ≤ (p : ℝ)) ∧
      ∀ (J : ℕ) (Λ : B → Finset (Fin J)), (∃ g, (Λ g).Nonempty) →
        ∀ t : AuxList 𝔊.big Λ, Real.log x ^ E ≤ (tupleProd Λ t : ℝ)

/-! ### Products of labels [S-03:0077–0108, 0163–0174] -/

/-- **The product atom bound (eq:ideal-product-atom)** [S-03:0079–0096].

"Let `Λ` be a nonempty set of slots, using `k_g ≤ m` slots from group `g`, and let `P_Λ` denote
the product of its labels. Disjointness of the prime groups and unique factorization give, on the
support of this product, `ρ_Λ(n) := ℙ(P_Λ = n) = (1/n) ∏_g k_g! / (V_g^{k_g} ∏_{p ∈ 𝒫_g} a_p!)
≤ L^κ / n`, `κ = C₀ (log(m!) + m log max(1, v₋⁻¹))` … each factor apart from `1/n` is at most
`m! max(1, v₋⁻¹)^m`, and there are at most `C₀ T` big groups."

Only the inequality is stated. -/
def ProductAtomBound : Prop :=
  ∀ (P : GroupParams) (m : ℕ), ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B) (J : ℕ) (Λ : B → Finset (Fin J)),
      (∃ g, (Λ g).Nonempty) → (∀ g, (Λ g).card ≤ m) →
    ∀ n : ℕ, 0 < n →
      atomMass 𝔊.big Λ n ≤ Real.log x ^ atomExponent P m / (n : ℝ)

/-- **The collapse (eq:ideal-collapse)** [S-03:0098–0108].

"If `f` is any such `L²` test, supported where `c₁ U ≤ P_Λ ≤ c₂ U` for fixed `c₁, c₂ > 0`, put
`a_n = E[f 1_{P_Λ = n}]`. Cauchy–Schwarz on each fiber gives
`∑_n |a_n|² ≤ ∑_n ρ_Λ(n) E[|f|² 1_{P_Λ = n}] ≤ L^κ / (c₁ U) ‖f‖₂²`. No assumption that `f` is a
function of the product has been made."

Here `Y = c₁ U` is the lower bound of the support; the upper bound is not used. The sum is over an
arbitrary finite set of integers. -/
def CollapseBound : Prop :=
  ∀ (P : GroupParams) (m : ℕ), ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B) (J : ℕ) (Λ : B → Finset (Fin J)),
      (∃ g, (Λ g).Nonempty) → (∀ g, (Λ g).card ≤ m) →
    ∀ (Y : ℝ), 0 < Y → ∀ F : AuxList 𝔊.big Λ → ℂ,
      (∀ t, F t ≠ 0 → Y ≤ (tupleProd Λ t : ℝ)) →
    ∀ s : Finset ℕ,
      ∑ n ∈ s, ‖fiberCoeff 𝔊.big Λ F n‖ ^ 2 ≤
        Real.log x ^ atomExponent P m / Y * wNormSq (auxWeight 𝔊.big Λ) F

/-- **The probability-space bilinear bound (eq:ideal-probability-bilinear)** [S-03:0163–0174].

"For two independent selected products of sizes `U, V`, combining (eq:ideal-collapse) and
(eq:integer-bilinear) shows that the probability-space bilinear form with phase `e(α P_A P_B)` has
norm at most `C L^κ (1/V + 1/r + log(2r)/U + r log(2r)/(UV))^{1/2}`. The same assertion holds with
the phase multiplied by `(P_A P_B)^{iζ}` for any real `ζ`, since this factor separates between the
two tests and preserves their norms."

The tests are supported where `c₁ U ≤ P_A ≤ c₂ U` and `c₁ V ≤ P_B ≤ c₂ V` "for fixed
`c₁, c₂ > 0`" [S-03:0099–0100]; `α = u/r + β` is an arbitrary rational approximation as in
Lemma 4.2. The constant `C = K` is chosen after `c₁, c₂`, before `x`. -/
def ProbabilityBilinear : Prop :=
  ∀ (P : GroupParams) (m : ℕ) (c₁ c₂ : ℝ), 0 < c₁ → c₁ ≤ c₂ →
    ∃ K : ℝ, 0 < K ∧ ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B) (J : ℕ) (A Bs : B → Finset (Fin J)),
      (∃ g, (A g).Nonempty) → (∃ g, (Bs g).Nonempty) →
      (∀ g, (A g).card ≤ m) → (∀ g, (Bs g).card ≤ m) →
    ∀ U V : ℝ, 1 ≤ U → 1 ≤ V →
    ∀ (F : AuxList 𝔊.big Bs → ℂ) (G : AuxList 𝔊.big A → ℂ),
      (∀ t, F t ≠ 0 → c₁ * V ≤ (tupleProd Bs t : ℝ) ∧ (tupleProd Bs t : ℝ) ≤ c₂ * V) →
      (∀ t, G t ≠ 0 → c₁ * U ≤ (tupleProd A t : ℝ) ∧ (tupleProd A t : ℝ) ≤ c₂ * U) →
    ∀ (α ζ β : ℝ) (u : ℤ) (r : ℕ), 0 < r → IsCoprime u (r : ℤ) →
      α = (u : ℝ) / (r : ℝ) + β → |β| ≤ ((r : ℝ) ^ 2)⁻¹ →
      ‖phaseForm 𝔊.big A Bs F G α ζ‖ ≤
        K * Real.log x ^ atomExponent P m *
          Real.sqrt (1 / V + 1 / (r : ℝ) + Real.log (2 * (r : ℝ)) / U +
            (r : ℝ) * Real.log (2 * (r : ℝ)) / (U * V)) *
          (tupleNorm 𝔊.big Bs F * tupleNorm 𝔊.big A G)

/-! ### Log cells and conditional character operators [S-03:0176–0266] -/

/-- **The character estimate under a cell restriction (eq:ideal-character-cell)**
[S-03:0208–0241].

"If `Q` is a fixed power of `L` and `χ, χ'` are distinct members of `𝒞_Q`, then, for every fixed
`D_* > 0`, `|E[1_{log D ∈ I_j} conj(χ(D)) χ'(D)]| ≪_{D_*} L^{-D_*}`, uniformly in `j` and in the
nonempty slot set with at most `m` slots per group. … its precision is independent of the width or
location of the interval."

A member of `𝒞_Q` is a pair `(r, χ)` of a modulus `1 ≤ r ≤ Q` and a primitive character modulo
`r`, as in `primitiveCharSum`; "distinct" is distinctness of the pairs. The implied constant is
absorbed by the threshold `x₀` (apply the paper's estimate with `D_* + 1`). The width `h > 0` of
the cells is arbitrary. -/
def CharacterCell : Prop :=
  ∀ (P : GroupParams) (m : ℕ) (qs Dstar : ℝ), 0 ≤ qs → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B), (∀ g, IsPrimeInterval (𝔊.big g)) →
    ∀ (J : ℕ) (Λ : B → Finset (Fin J)), (∃ g, (Λ g).Nonempty) → (∀ g, (Λ g).card ≤ m) →
    ∀ (h : ℝ), 0 < h → ∀ (j : ℤ) (r₁ r₂ : ℕ) (χ₁ : DirichletCharacter ℂ r₁)
      (χ₂ : DirichletCharacter ℂ r₂),
      0 < r₁ → (r₁ : ℝ) ≤ Real.log x ^ qs → 0 < r₂ → (r₂ : ℝ) ≤ Real.log x ^ qs →
      χ₁.IsPrimitive → χ₂.IsPrimitive →
      (⟨r₁, χ₁⟩ : Σ r : ℕ, DirichletCharacter ℂ r) ≠ ⟨r₂, χ₂⟩ →
      ‖∑ t : AuxList 𝔊.big Λ, if logCell h (tupleProd Λ t) = j then
          (auxWeight 𝔊.big Λ t : ℂ) *
            (conj (χ₁ ((tupleProd Λ t : ℕ) : ZMod r₁)) * χ₂ ((tupleProd Λ t : ℕ) : ZMod r₂))
        else 0‖ ≤ Real.log x ^ (-Dstar)

/-- **Kernel integration has norm at most `2`** (eq:ideal-frame), (eq:ideal-gram-bound)
[S-03:0243–0266].

"The Gram matrix therefore has norm at most `1 + O_{D_*}(Q² ξ⁻¹ L^{-D_*}) ≤ 2` once the character
precision has been chosen sufficiently large. … Different cells are orthogonal blocks, and
discarded cells have zero operator. Consequently kernel integration on the full label space has
norm at most `2`. The adjoint and transpose have the same bound, so the integration may be moved
onto either test in a bilinear form. In particular neither a cell-count factor nor a factor `ξ⁻¹`
is lost in this operator norm."

For all exponents `q_*, h_*, x_* ≥ 0`; the operator `kernelIntD` and its transpose `kernelIntX`. -/
def KernelNorm : Prop :=
  ∀ (P : GroupParams) (m : ℕ) (qs hs xs : ℝ), 0 ≤ qs → 0 ≤ hs → 0 ≤ xs →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B), (∀ g, IsPrimeInterval (𝔊.big g)) →
    ∀ (J : ℕ) (Λ : B → Finset (Fin J)), (∃ g, (Λ g).Nonempty) → (∀ g, (Λ g).card ≤ m) →
    ∀ G : AuxList 𝔊.big Λ → ℂ,
      tupleNorm 𝔊.big Λ (kernelIntD 𝔊.big Λ (Real.log x ^ qs) (Real.log x ^ (-hs))
          (Real.log x ^ (-xs)) G) ≤ 2 * tupleNorm 𝔊.big Λ G ∧
        tupleNorm 𝔊.big Λ (kernelIntX 𝔊.big Λ (Real.log x ^ qs) (Real.log x ^ (-hs))
          (Real.log x ^ (-xs)) G) ≤ 2 * tupleNorm 𝔊.big Λ G

/-- **The reproduction formula (eq:ideal-character-reproduction)** [S-03:0391–0403].

"For a character `ψ` in (eq:ideal-rational-expansion), the Gram calculation also gives the
following pointwise reproduction formula for retained `X`:
`E_D 𝒦_Λ(D, X) ψ(D) = ψ(X) + O_{D_*}(Q² ξ⁻¹ L^{-D_*})`. In fact, the summand corresponding to its
inducing primitive character is exactly `ψ(X)`: the diagonal conditional expectation is `1`. Each
other summand is bounded by (eq:ideal-character-cell) divided by the retained-cell mass. There are
at most `Q²` such summands."

Here `ψ` is any character of a modulus `r ≤ Q`, `X` is the product of a tuple of type `Λ` lying in
a retained cell, and the error is at most `L^{-E}` for an arbitrary fixed `E` (the proof chooses
`D_* ≥ E + 2 q_* + x_*`). -/
def CharacterReproduction : Prop :=
  ∀ (P : GroupParams) (m : ℕ) (qs hs xs E : ℝ), 0 ≤ qs → 0 ≤ hs → 0 ≤ xs →
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B), (∀ g, IsPrimeInterval (𝔊.big g)) →
    ∀ (J : ℕ) (Λ : B → Finset (Fin J)), (∃ g, (Λ g).Nonempty) → (∀ g, (Λ g).card ≤ m) →
    ∀ (r : ℕ) (ψ : DirichletCharacter ℂ r), 0 < r → (r : ℝ) ≤ Real.log x ^ qs →
    ∀ X : AuxList 𝔊.big Λ,
      Real.log x ^ (-xs) ≤
        cellMass 𝔊.big Λ (Real.log x ^ (-hs)) (logCell (Real.log x ^ (-hs)) (tupleProd Λ X)) →
      ‖(∑ d : AuxList 𝔊.big Λ, (auxWeight 𝔊.big Λ d : ℂ) *
            (cellKernel 𝔊.big Λ (Real.log x ^ qs) (Real.log x ^ (-hs)) (Real.log x ^ (-xs))
                (tupleProd Λ d) (tupleProd Λ X) * ψ ((tupleProd Λ d : ℕ) : ZMod r))) -
          ψ ((tupleProd Λ X : ℕ) : ZMod r)‖ ≤ Real.log x ^ (-E)

/-! ### One pair of dyads [S-03:0294–0412] -/

/-- **The comparison estimate on one pair of dyads**, with precision `L^{-B₀}`
[S-03:0295–0302]: "Split the tests according to dyads `X_A ∈ [U, 2U)` and `X_B ∈ [V, 2V)`. … We
prove a bound `L^{-B₀}` on each pair of dyads." Here `U = 2^a`, `V = 2^b`. -/
def DyadicContract (P : GroupParams) (m : ℕ) (B₀ C₄ qs hs xs : ℝ) : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B), (∀ g, IsPrimeInterval (𝔊.big g)) →
    ∀ (J : ℕ) (A Bs : B → Finset (Fin J)),
      (∃ g, (A g).Nonempty) → (∃ g, (Bs g).Nonempty) →
      (∀ g, (A g).card ≤ m) → (∀ g, (Bs g).card ≤ m) →
    ∀ (a b : ℕ) (f : AuxList 𝔊.big Bs → ℂ) (g : AuxList 𝔊.big A → ℂ),
      DyadSupported 𝔊.big Bs b f → DyadSupported 𝔊.big A a g →
    ∀ α ζ : ℝ, |ζ| ≤ Real.log x ^ C₄ →
      ‖comparisonDefect 𝔊.big A Bs (Real.log x ^ qs) (Real.log x ^ (-hs)) (Real.log x ^ (-xs))
          f g α ζ‖ ≤
        Real.log x ^ (-B₀) * (tupleNorm 𝔊.big Bs f * tupleNorm 𝔊.big A g)

/-- **The comparison estimate on one pair of dyads when `r > Q`** ("denominators larger than
`Q`", [S-03:0316–0337]), for fixed exponents: `Z = UV = 2^a 2^b`, `S = L^{s_*}`, and
`α = u/r + β` is a Dirichlet approximation (eq:ideal-dirichlet) with `Q = L^{q_*} < r`.
"This part is uniform in all real `ζ`, because the Mellin factor separates." -/
def MinorArcContract (P : GroupParams) (m : ℕ) (B₀ qs ss hs xs : ℝ) : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B), (∀ g, IsPrimeInterval (𝔊.big g)) →
    ∀ (J : ℕ) (A Bs : B → Finset (Fin J)),
      (∃ g, (A g).Nonempty) → (∃ g, (Bs g).Nonempty) →
      (∀ g, (A g).card ≤ m) → (∀ g, (Bs g).card ≤ m) →
    ∀ (a b : ℕ) (f : AuxList 𝔊.big Bs → ℂ) (g : AuxList 𝔊.big A → ℂ),
      DyadSupported 𝔊.big Bs b f → DyadSupported 𝔊.big A a g →
    ∀ (α ζ β : ℝ) (u : ℤ) (r : ℕ),
      DirichletData α ((2 : ℝ) ^ a * (2 : ℝ) ^ b) (Real.log x ^ ss) u r β →
      Real.log x ^ qs < (r : ℝ) →
      ‖comparisonDefect 𝔊.big A Bs (Real.log x ^ qs) (Real.log x ^ (-hs)) (Real.log x ^ (-xs))
          f g α ζ‖ ≤
        Real.log x ^ (-B₀) * (tupleNorm 𝔊.big Bs f * tupleNorm 𝔊.big A g)

/-- **The comparison estimate on one pair of dyads when `r ≤ Q`** ("denominators at most `Q`",
[S-03:0339–0412]), for fixed exponents: `Z = UV = 2^a 2^b`, `S = L^{s_*}`, `|ζ| ≤ L^{C₄}`, and
`α = u/r + β` is a Dirichlet approximation (eq:ideal-dirichlet) with `r ≤ Q = L^{q_*}`. -/
def MajorArcContract (P : GroupParams) (m : ℕ) (B₀ C₄ qs ss hs xs : ℝ) : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B), (∀ g, IsPrimeInterval (𝔊.big g)) →
    ∀ (J : ℕ) (A Bs : B → Finset (Fin J)),
      (∃ g, (A g).Nonempty) → (∃ g, (Bs g).Nonempty) →
      (∀ g, (A g).card ≤ m) → (∀ g, (Bs g).card ≤ m) →
    ∀ (a b : ℕ) (f : AuxList 𝔊.big Bs → ℂ) (g : AuxList 𝔊.big A → ℂ),
      DyadSupported 𝔊.big Bs b f → DyadSupported 𝔊.big A a g →
    ∀ (α ζ β : ℝ) (u : ℤ) (r : ℕ), |ζ| ≤ Real.log x ^ C₄ →
      DirichletData α ((2 : ℝ) ^ a * (2 : ℝ) ^ b) (Real.log x ^ ss) u r β →
      (r : ℝ) ≤ Real.log x ^ qs →
      ‖comparisonDefect 𝔊.big A Bs (Real.log x ^ qs) (Real.log x ^ (-hs)) (Real.log x ^ (-xs))
          f g α ζ‖ ≤
        Real.log x ^ (-B₀) * (tupleNorm 𝔊.big Bs f * tupleNorm 𝔊.big A g)

/-- **Denominators larger than `Q`** [S-03:0316–0337].

"Suppose `r > Q`. Apply (eq:ideal-probability-bilinear) to the raw term. For the comparison term,
move the two separate kernel integrations onto the two tests. Their norms increase by at most `2`
each by (eq:ideal-gram-bound). The resulting tests on `D_A, D_B` are supported in `[U/2, 4U]` and
`[V/2, 4V]` for large `x`, by the log localization. … Since `r > Q` and `r ≤ UV/S`, the bound for
either term, apart from an absolute constant and the two test norms, is
`L^κ (o(L^{-A}) + Q⁻¹ + L^{d+1} S⁻¹)^{1/2}` for every fixed `A`. Choosing `Q, S` sufficiently large
gives the required dyadic precision."

"Sufficiently large" is the second line of (eq:ideal-parameter-order):
`q_*, s_* > 2(B₀ + κ + 10) + d + 1` [S-03:0424]. The exponents `h_*, x_* ≥ 0` are arbitrary. -/
def MinorArcBound : Prop :=
  ∀ (P : GroupParams) (m : ℕ) (B₀ qs ss hs xs : ℝ), 0 < B₀ →
    2 * (B₀ + atomExponent P m + 10) + P.d + 1 < qs →
    2 * (B₀ + atomExponent P m + 10) + P.d + 1 < ss → 0 ≤ hs → 0 ≤ xs →
    MinorArcContract P m B₀ qs ss hs xs

/-- **Denominators at most `Q`** [S-03:0339–0412].

"First remove discarded cells. Their total probability for either product is at most
`ℙ(ℰ) ≤ (N_A + N_B) ξ` … On retained cells, write the remaining scalar multiplier in the log
variable as `M(v) = exp(iζv) e(β e^v)`. On the enlarged product range its derivative has magnitude
`O(L^{C₄} + S)` … (eq:ideal-cell-costs) bounds the error after integration in `D_A, D_B` by
`O(Q⁴ h (S + L^{C₄}))` … Applying the formula on both sides and then
(eq:ideal-rational-expansion) reproduces `e(u X_A X_B / r)` with pointwise error
`O_{D_*}(Q^{5/2} ξ⁻¹ L^{-D_*})`. … Together, (eq:ideal-discarded-mass), (eq:ideal-log-error),
(eq:ideal-major-character-error) establish the desired comparison on a pair of dyads."

The inequalities are the third and fourth lines of (eq:ideal-parameter-order):
`h_* > 4 q_* + max(s_*, C₄) + B₀ + 10`, `x_* > 2 B₀ + d + 1 + h_* + 10` [S-03:0425–0426]. The
character precision `D_*` (fifth line) is inside `CharacterReproduction`. -/
def MajorArcBound : Prop :=
  ∀ (P : GroupParams) (m : ℕ) (B₀ C₄ qs ss hs xs : ℝ), 0 < B₀ → 0 ≤ C₄ → 0 ≤ qs →
    4 * qs + max ss C₄ + B₀ + 10 < hs → 2 * B₀ + P.d + 1 + hs + 10 < xs →
    MajorArcContract P m B₀ C₄ qs ss hs xs

/-- **The dyadic summation** [S-03:0295–0302].

"Split the tests according to dyads `X_A ∈ [U, 2U)` and `X_B ∈ [V, 2V)`. Each selected product
lies between `exp(L^c)` and `exp(m C₀ T L^d)`; thus for sufficiently large `x` there are at most
`L^{d+1}` dyads for each product. We prove a bound `L^{-B₀}` on each pair of dyads, with
`B₀ > A₀ + 2(d+1) + 10`. Summing the bounds proves the lemma, even using the crude bound of the
original test norm for every dyadic restriction." -/
def DyadicSummation : Prop :=
  ∀ (P : GroupParams) (m : ℕ) (A₀ C₄ qs hs xs B₀ : ℝ), A₀ + 2 * (P.d + 1) + 10 < B₀ →
    DyadicContract P m B₀ C₄ qs hs xs → ComparisonContract P m A₀ C₄ qs hs xs

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
