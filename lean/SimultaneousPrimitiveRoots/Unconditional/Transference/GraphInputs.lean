module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Statements

/-!
# The graph inputs of [P] §6: Propositions 6.2 and 6.3

Source: `verification/stage7-sources/P-06.tex`, lines 99–258 (`[P-06:0099–0258]`).

[P] §6.1 restates the objects of [S] §3 "with their exact measures": arbitrary fixed exponents
`0 < a < b < c < d₀ < 0.47`, an integer `ℓ ≥ 1`, `M = J + ℓ`, patterns with `|C_g| ≤ m₀`, the
physical space with masses `∏_g V_g^{-M}`, the operator `𝒜_ζ` with multiplier
(cor:physical-multiplier) and the ideal operator `𝒯_ζ(Θ)` [P-06:0101–0150]. These are literally
Definitions 3.1–3.3 of [S], with [S]'s parameter `q` called `q₀` [P-06:0186]; so the same Lean
objects are used: `GroupParams` (with `q := q₀`), `PrimeGroups`, `Pattern`, `physOp`, `idealOp`.

## Which quantifier form each statement has

* **The slot count `J` is fixed before `x` in both propositions**, exactly as in [S]:
  "the integer `J` used in this section is sufficiently large and *fixed* as `x → ∞`; it is
  different from the growing determinant parameter in the preceding sections" [P-06:0004–0007].
  `GraphTransferInput`: `P, E ⟶ E_id ⟶ m₀, C₁ ⟶ J₀, C_abs ⟶ J ≥ J₀ ⟶ C₂, γ, C₃, C_sup ⟶ M, x₀`.
  `IdealFamilyInput`: `P, E_id, C₄, A₀ ⟶ m₀, J₀, C₁, exponents of Q, h⁻¹, ξ⁻¹ ⟶ J ≥ J₀ ⟶ x₀`.
* The **growing** slot count of [P] is `J = ⌊L^{0.01}⌋`, `M = J + 1`, `R = ⌈L^{0.5}/2⌉`
  [P-03:0173–0177], [P-04:0004–0007]. It belongs to the one-sided determinant argument of
  [P] §§3–4, which does not import [S] Theorem 3.5: "the primewise identity and every operator
  estimate needed here are proved below for the determinant graph" [P-04:0037–0041]. None of the
  statements of this directory can be instantiated with `J = J(x)`, since `J` is quantified before
  `x₀`; a formal counterpart of [P] Proposition 4.1 needs its own statement.
* [P] uses the two propositions with `ℓ = k = 1`, `C₄ = 1` and the exponents
  `(a, b, c, d) = (0.27, 0.36, 0.39, 0.46)` [P-06:0256–0258, 0298–0299]; every big active group of
  [P] is the set of all primes of an interval [P-06:0023].

## What follows from what

* `graphTransferInput_of`: Proposition 6.2 follows by pure logic from [S] Theorem 3.5
  (`LocalTransference`), Corollary 3.11 (`EndpointPairing`) and the integer-position half of
  Lemma 3.4 (`PhysicalSchur`). Nothing differs in content; the residue-model half of Lemma 3.4 is
  not used by [P].
* Proposition 6.3 is [S] Theorem 4.1 together with Lemma 4.3, but it does **not** follow from the
  two *statements* alone: it asserts that the kernel exponents of the family can be taken so that
  the comparison contract holds with any prescribed precision `A₀`, which is in the proof of
  Theorem 4.1 (the choice `A₀ > E_id + m C₀ log 3 + 10` there may be increased,
  [S-03:0606–0612, 0636–0644]), and it adds the cost bounds (eq:ideal-cell-costs)
  [S-03:0196–0206] and the bound on the number of patterns [S-03:0619–0621]. What is needed is
  made explicit in `IdealConstructionOfContract`, and `idealFamilyInput_of` derives
  Proposition 6.3 from it, Lemma 4.3, and the cost bounds.
* `residualMoment_of`: Theorems 3.5 and 4.1 compose in the order `E ⟶ E_id ⟶ (m, J₀, C₁) ⟶ J`
  of [P-06:0301–0306] and [S-03:0642–0644].
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference

open scoped BigOperators

noncomputable section

/-! ### Proposition 6.2 -/

/-- **[P] Proposition 6.2 (general graph transference input)** [P-06:0152–0181].

"Assume `∑_ν sup |K_ν| ≤ L^{C₁}`, where `m₀, C₁` are fixed independently of `J`. For every fixed
`E > 0` there is `E_id > 0`, depending only on `E` and the fixed group data, such that
`sup_Θ ‖𝒯_ζ(Θ)‖ ≤ L^{-E_id}` has the following consequence for all sufficiently large fixed `J`.
Let `I = [X, 2X)`, with `x^γ ≤ X ≤ x^{1/γ}` for fixed `γ > 0`. If `f` is supported on positions in
`I`, is independent of the chosen marks, and satisfies `sup |f| ≤ exp(O(√L))`,
`‖f‖, ‖g‖ ≤ X^{1/2} L^{C₃}`, then `|⟨f, 𝒜_ζ g⟩| ≪ X L^{-E + 2C₃}`. The lower bound on `J` may also
depend on `m₀, C₁`. The threshold for `x` may depend on `J, C₂, γ`. No further restriction on `ζ`
is imposed beyond the ideal norm hypothesis. Taking absolute values of the individual transition
coefficients gives row and column sums at most `L^{C_abs}`, where `C_abs` is independent of `J`."

This is `PairingBound` (Theorem 3.5 with Corollary 3.11) and `IntSchurBound` (Lemma 3.4 for
integer positions) with the constants in [P]'s order. `J` is fixed before `x`. -/
def GraphTransferInput : Prop :=
  ∀ (P : GroupParams) (E : ℝ), 0 < E → ∃ Eid : ℝ, 0 < Eid ∧
    ∀ (m₀ : ℕ) (C₁ : ℝ), ∃ (J₀ : ℕ) (Cabs : ℝ), ∀ J : ℕ, J₀ ≤ J →
      ∀ C₂ γ C₃ Csup : ℝ, 0 < γ →
        PairingBound P E Eid m₀ C₁ J C₂ γ C₃ Csup ∧ IntSchurBound P m₀ C₁ Cabs J C₂

/-- **Proposition 6.2 follows from [S] Theorem 3.5, Corollary 3.11 and Lemma 3.4** (pure logic),
as asserted in [P-06:0183–0185]. -/
theorem graphTransferInput_of (h₁ : LocalTransference) (h₂ : EndpointPairing)
    (h₃ : PhysicalSchur) : GraphTransferInput := by
  intro P E hE
  obtain ⟨Eid, hEid, h⟩ := h₁ P E hE
  refine ⟨Eid, hEid, fun m₀ C₁ => ?_⟩
  obtain ⟨J₀, hJ⟩ := h m₀ C₁
  obtain ⟨Cabs, hS⟩ := h₃ P m₀ C₁
  refine ⟨J₀, Cabs, fun J hJ₀ C₂ γ C₃ Csup hγ => ?_⟩
  exact ⟨h₂ P E Eid m₀ C₁ J C₂ γ hE hγ (hJ J hJ₀ C₂ γ hγ) C₃ Csup, (hS J C₂).1⟩

/-! ### Proposition 6.3 -/

/-- **The kernel costs (eq:ideal-cell-costs)** [S-03:0196–0206], as quoted in [P-06:0228–0235],
for fixed exponents: with `Q = L^{q_*}`, `h = L^{-h_*}`, `ξ = L^{-x_*}` and a constant `C_cell`
depending on `m₀` and the group data, for all sufficiently large `x`, every system of prime groups
with interval big groups and every nonempty slot set `Λ` with at most `m₀` slots per group:

* "there are at most `Q²` characters";
* there are at most `C_cell (1 + L^d log L / h)` nonempty cells;
* `sup |𝒦_Λ| ≤ Q² ξ⁻¹`;
* `sup_X E_D |𝒦_Λ(D, X)| ≤ Q²`. -/
def KernelCosts (P : GroupParams) (m₀ : ℕ) (qs hs xs : ℝ) : Prop :=
  ∃ Ccell x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B), (∀ g, IsPrimeInterval (𝔊.big g)) →
    ∀ (J : ℕ) (Λ : B → Finset (Fin J)), (∃ g, (Λ g).Nonempty) → (∀ g, (Λ g).card ≤ m₀) →
      (primitiveCharCount (Real.log x ^ qs) : ℝ) ≤ (Real.log x ^ qs) ^ 2 ∧
      (cellCount 𝔊.big Λ (Real.log x ^ (-hs)) : ℝ) ≤
        Ccell * (1 + Real.log x ^ P.d * Real.log (Real.log x) / Real.log x ^ (-hs)) ∧
      (∀ D X : ℕ, ‖cellKernel 𝔊.big Λ (Real.log x ^ qs) (Real.log x ^ (-hs))
          (Real.log x ^ (-xs)) D X‖ ≤ (Real.log x ^ qs) ^ 2 * (Real.log x ^ (-xs))⁻¹) ∧
      ∀ X : ℕ, ∑ t : AuxList 𝔊.big Λ, auxWeight 𝔊.big Λ t *
          ‖cellKernel 𝔊.big Λ (Real.log x ^ qs) (Real.log x ^ (-hs)) (Real.log x ^ (-xs))
            (tupleProd Λ t) X‖ ≤ (Real.log x ^ qs) ^ 2

/-- (eq:ideal-cell-costs) for all exponents `q_*, h_*, x_* ≥ 0`: an elementary consequence of the
definition of `𝒦_Λ` and of Definition 3.1 [S-03:0196–0206]; it is not a numbered statement of
[S]. -/
def KernelCostsLemma : Prop :=
  ∀ (P : GroupParams) (m₀ : ℕ) (qs hs xs : ℝ), 0 ≤ qs → 0 ≤ hs → 0 ≤ xs →
    KernelCosts P m₀ qs hs xs

/-- The number of patterns of the residual family is at most `L^{C₁}` for large `x`: "the number
of comparisons is at most `2^P ≤ L^{m C₀ log 2}`" [S-03:0619–0620]. With `KernelCosts` this is
[P]'s "expanding the two kernels, including all patterns, has total coefficient mass and number of
terms bounded by fixed powers of `L`" [P-06:0248–0250]. -/
def PatternCountBound (P : GroupParams) (m₀ : ℕ) (C₁ : ℝ) (J : ℕ) : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (_𝔊 : PrimeGroups P x S B) (blk : B → Bool),
      (Fintype.card (ComparisonIndex B blk J m₀) : ℝ) ≤ Real.log x ^ C₁

/-- **[P] Proposition 6.3 (residual ideal family input)** [P-06:0198–0251].

"For every `E_id > 0` and fixed `C₄ ≥ 0`, there are fixed `m₀, J₀, C₁` such that, for each fixed
`J ≥ J₀`, a family consisting of the raw pattern `C_g = ∅`, `K₀ = 1`, and signed comparison
patterns satisfies `∑_ν sup |K_ν| ≤ L^{C₁}` and
`sup_{Θ ∈ ℝ, |ζ| ≤ L^{C₄}} ‖𝒯_ζ(Θ)‖ ≤ L^{-E_id}`. The family is independent of `Θ, ζ`; its defining
parameters are independent of `J`."

The family is `comparisonFamily` ((cor:comparison-kernel), (cor:cell-kernel), with `Q, h⁻¹, ξ⁻¹`
fixed powers of `L`, `h ≤ 1`); `KernelCosts` and `PatternCountBound` are the cost bounds quoted in
[P-06:0228–0235, 0248–0250]; `ComparisonContract` is (cor:comparison-contract): "for any
prescribed fixed `A₀ > 0`, the parameters may be chosen, independently of `J`, so that …"
[P-06:0236–0246]. The prescribed `A₀` is a constant on which `C₁` and the kernel exponents depend;
`m₀` and `J₀` are stated after it as well (in [S]'s proof they do not depend on it). `J` is fixed
before `x`. -/
def IdealFamilyInput : Prop :=
  ∀ (P : GroupParams) (Eid C₄ A₀ : ℝ), 0 < Eid → 0 ≤ C₄ → 0 < A₀ →
    ∃ (m₀ J₀ : ℕ) (C₁ qs hs xs : ℝ), 0 ≤ qs ∧ 0 ≤ hs ∧ 0 ≤ xs ∧
      ComparisonContract P m₀ A₀ C₄ qs hs xs ∧ KernelCosts P m₀ qs hs xs ∧
      ∀ J : ℕ, J₀ ≤ J →
        IdealFamilyBound P Eid C₄ m₀ C₁ J qs hs xs ∧ PatternCountBound P m₀ C₁ J

/-- **The part of the proof of [S] Theorem 4.1 after Lemma 4.3** [S-03:0441–0645], as a
statement: there are `m`, a precision `A₀*` and `J₀` (from `E_id`, `C₄` and the group data) such
that for all kernel exponents with the comparison contract of precision `A₀*`, the residual family
with these exponents satisfies the conclusion of Theorem 4.1 for a suitable `C₁` and every
`J ≥ J₀`, and has at most `L^{C₁}` patterns.

In the paper: `m` from (eq:ideal-full-component), `A₀* = E_id + m C₀ log 3 + 10`
[S-03:0606–0612], `C₁ > m C₀ log 2 + 4 q_* + 2 x_* + 1` [S-03:0619–0627], and `J₀` from
`J ≥ m`, `J + ℓ ≥ (m + ℓ)(m + ℓ - 1)` [S-03:0640–0642]. This is not a numbered statement of [S];
it records what Proposition 6.3 of [P] uses beyond the statements of Theorem 4.1 and
Lemma 4.3. -/
def IdealConstructionOfContract : Prop :=
  ∀ (P : GroupParams) (Eid C₄ : ℝ), 0 < Eid → 0 ≤ C₄ →
    ∃ (m J₀ : ℕ) (A₀' : ℝ), 0 < A₀' ∧ ∀ qs hs xs : ℝ, 0 ≤ qs → 0 ≤ hs → 0 ≤ xs →
      ComparisonContract P m A₀' C₄ qs hs xs →
      ∃ C₁ : ℝ, ∀ J : ℕ, J₀ ≤ J →
        IdealFamilyBound P Eid C₄ m C₁ J qs hs xs ∧ PatternCountBound P m C₁ J

/-- The comparison contract with a larger precision implies the contract with a smaller one. -/
theorem ComparisonContract.mono {P : GroupParams} {m : ℕ} {A₀ A₀' C₄ qs hs xs : ℝ}
    (hA : A₀ ≤ A₀') (h : ComparisonContract P m A₀' C₄ qs hs xs) :
    ComparisonContract P m A₀ C₄ qs hs xs := by
  obtain ⟨x₀, hx₀⟩ := h
  refine ⟨max x₀ (Real.exp 1), fun x hx S B _ _ _ _ 𝔊 hint J A Bs hA' hB' hAm hBm f g α ζ hζ => ?_⟩
  have hx1 : x₀ ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hL : 1 ≤ Real.log x := by
    have h1 := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at h1
  have hpow : Real.log x ^ (-A₀') ≤ Real.log x ^ (-A₀) :=
    Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg hA)
  have hnn : 0 ≤ tupleNorm 𝔊.big Bs f * tupleNorm 𝔊.big A g :=
    mul_nonneg (wNorm_nonneg _ _) (wNorm_nonneg _ _)
  exact (hx₀ x hx1 S B 𝔊 hint J A Bs hA' hB' hAm hBm f g α ζ hζ).trans
    (mul_le_mul_of_nonneg_right hpow hnn)

/-- **Theorem 4.1 follows from Lemma 4.3 and the part of its proof after Lemma 4.3.** -/
theorem idealConstruction_of (h₁ : ComparisonKernelLemma) (h₂ : IdealConstructionOfContract) :
    IdealConstruction := by
  intro P Eid C₄ hEid hC₄
  obtain ⟨m, J₀, A₀', hA₀', h⟩ := h₂ P Eid C₄ hEid hC₄
  obtain ⟨qs, hs, xs, hqs, hhs, hxs, hc⟩ := h₁ P m A₀' C₄ hA₀' hC₄
  obtain ⟨C₁, hC₁⟩ := h qs hs xs hqs hhs hxs hc
  exact ⟨m, J₀, C₁, qs, hs, xs, hqs, hhs, hxs, fun J hJ => (hC₁ J hJ).1⟩

/-- **Proposition 6.3 follows from Lemma 4.3, the part of the proof of Theorem 4.1 after
Lemma 4.3, and the kernel costs (eq:ideal-cell-costs)** (the latter for all exponents). -/
theorem idealFamilyInput_of (h₁ : ComparisonKernelLemma) (h₂ : IdealConstructionOfContract)
    (h₃ : KernelCostsLemma) : IdealFamilyInput := by
  intro P Eid C₄ A₀ hEid hC₄ hA₀
  obtain ⟨m, J₀, A₀', hA₀', h⟩ := h₂ P Eid C₄ hEid hC₄
  obtain ⟨qs, hs, xs, hqs, hhs, hxs, hc⟩ :=
    h₁ P m (max A₀ A₀') C₄ (lt_max_of_lt_left hA₀) hC₄
  obtain ⟨C₁, hC₁⟩ := h qs hs xs hqs hhs hxs (hc.mono (le_max_right _ _))
  exact ⟨m, J₀, C₁, qs, hs, xs, hqs, hhs, hxs, hc.mono (le_max_left _ _),
    h₃ P m qs hs xs hqs hhs hxs, hC₁⟩

/-! ### The composition used in [P] §6 -/

/-- **Theorems 3.5 and 4.1 composed**: for every `E > 0` and `C₄ ≥ 0` there are `m`, a fixed `J`
and kernel exponents such that, for all sufficiently large `x`, the residual family satisfies the
moment bound (eq:transference-moment) for every `|ζ| ≤ L^{C₄}` and every `0 < |k| ≤ L^{C₂}`,
with no hypothesis on an ideal norm. -/
def ResidualMoment : Prop :=
  ∀ (P : GroupParams) (E C₄ : ℝ), 0 < E → 0 ≤ C₄ →
    ∃ (m J : ℕ) (qs hs xs : ℝ), ∀ C₂ γ : ℝ, 0 < γ →
      ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
        ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
          (𝔊 : PrimeGroups P x S B), (∀ g, IsPrimeInterval (𝔊.big g)) →
        ∀ blk : B → Bool, BalancedSplit blk →
        ∀ (ζ : ℝ) (k : ℤ), |ζ| ≤ Real.log x ^ C₄ → k ≠ 0 → |(k : ℝ)| ≤ Real.log x ^ C₂ →
        ∀ X : ℝ, x ^ γ ≤ X → X ≤ x ^ (1 / γ) →
          averagedMoment 𝔊 (comparisonFamily 𝔊.big J P.ℓ m blk (Real.log x ^ qs)
              (Real.log x ^ (-hs)) (Real.log x ^ (-xs))) k ζ X ≤
            Real.log x ^ (-(E * (Graph.sourceMemoryLength (Real.log x) : ℝ)))

/-- **The quantifier orders of Theorems 3.5 and 4.1 are compatible**: `E ⟶ E_id` (Theorem 3.5),
then `(m, J₀, C₁)` and the kernel exponents (Theorem 4.1 for `E_id`), then the lower bound on `J`
of Theorem 3.5 for `(m, C₁)`, then one fixed `J` above both lower bounds
([S-03:0642–0644], [P-06:0301–0306]). -/
theorem residualMoment_of (h₁ : LocalTransference) (h₂ : IdealConstruction) : ResidualMoment := by
  intro P E C₄ hE hC₄
  obtain ⟨Eid, hEid, h35⟩ := h₁ P E hE
  obtain ⟨m, J₁, C₁, qs, hs, xs, _, _, _, h41⟩ := h₂ P Eid C₄ hEid hC₄
  obtain ⟨J₀, hJ₀⟩ := h35 m C₁
  refine ⟨m, max J₀ J₁, qs, hs, xs, fun C₂ γ hγ => ?_⟩
  obtain ⟨x₁, hx₁⟩ := hJ₀ (max J₀ J₁) (le_max_left _ _) C₂ γ hγ
  obtain ⟨x₂, hx₂⟩ := h41 (max J₀ J₁) (le_max_right _ _)
  refine ⟨max x₁ x₂, fun x hx S B _ _ _ _ 𝔊 hint blk hblk ζ k hζ hk hkb X hX₁ hX₂ => ?_⟩
  obtain ⟨hmass, hnorm⟩ :=
    hx₂ x (le_trans (le_max_right _ _) hx) S B 𝔊 hint blk hblk
  exact hx₁ x (le_trans (le_max_left _ _) hx) S B 𝔊 _ _ ζ k
    ⟨fun ν g => comparisonFamily_card_le _ _ _ _ _ _ _ _ ν g, hmass, hk, hkb⟩
    (fun Θ => hnorm Θ ζ hζ) X hX₁ hX₂

end

end SimultaneousPrimitiveRoots.Unconditional.Transference
