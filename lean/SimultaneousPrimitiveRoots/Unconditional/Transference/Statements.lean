module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.PhysicalOperator
public import SimultaneousPrimitiveRoots.Unconditional.Transference.IdealFamily

/-!
# The statements of [S] §§3–4: Lemma 3.4, Theorem 3.5, Corollary 3.11, Theorem 4.1, Lemma 4.3

Sources: `verification/stage7-sources/S-02.tex` (`[S-02:…]`) and `S-03.tex` (`[S-03:…]`).

Every deep result is a `def … : Prop`; nothing here is proved except the purely logical
combination `localTransferenceWithPairing_of`.

Throughout, `L = log x`, `T = log L`, and every statement has the shape
"constants in the paper's order, then `∃ x₀, ∀ x ≥ x₀`, then all objects that may vary with `x`".
The body after the constants is a separate definition (`MomentBound`, `PairingBound`,
`IntSchurBound`, `ResidueSchurBound`, `ComparisonContract`, `IdealFamilyBound`), so that the
quantifier prefix of each theorem is short and can be compared with the paper.

## Quantifier order (what may depend on what)

* **Lemma 3.4** (`PhysicalSchur`): `P, m, C₁ ⟶ C_abs ⟶ J, C₂ ⟶ x₀ ⟶ x, groups, family, ζ, k`.
  `C_abs` "may depend on `m, C₁` and the fixed data in Definition 3.1, but is independent of `J`"
  [S-02:0136–0138].
* **Theorem 3.5** (`LocalTransference`): `P, E ⟶ E_id ⟶ m, C₁ ⟶ J₀ ⟶ J ≥ J₀ ⟶ C₂, γ ⟶ x₀ ⟶
  x, groups, family, ζ, k, X`. `E_id` depends "only on `E` and the fixed data in Definition 3.1"
  [S-02:0164–0166]; "the lower bound on `J` may also depend on `m, C₁`" [S-02:0170–0171]; "the
  threshold for `x` may depend on all fixed parameters, including `J, C₂, γ`" [S-02:0183–0185].
  The ideal estimate (eq:ideal-norm-hypothesis) is a hypothesis for that `x`, that family and
  that `ζ`; "no bound on `ζ` is needed apart from the assumed ideal estimate" [S-02:0186–0187].
* **Corollary 3.11** (`EndpointPairing`): for every choice of the constants of Theorem 3.5, the
  conclusion of Theorem 3.5 implies the pairing bound, with a constant `M` and a threshold `x₀`
  chosen after the additional constants `C₃` and `C_sup` (the constant in `exp(O(√L))`).
* **Lemma 4.3** (`ComparisonKernelLemma`): `P, m, A₀, C₄ ⟶ exponents of Q, h⁻¹, ξ⁻¹ ⟶ x₀ ⟶
  x, groups, slot sets, tests, α, ζ`.
* **Theorem 4.1** (`IdealConstruction`): `P, E_id, C₄ ⟶ m, J₀, C₁, exponents of Q, h⁻¹, ξ⁻¹ ⟶
  J ≥ J₀ ⟶ x₀ ⟶ x, groups, block split, Θ, ζ`. "The threshold for `x` may depend on `J`"
  [S-03:0036]; the family does not depend on `Θ` or `ζ`; its defining parameters do not depend
  on `J`.

In all of them `J` is fixed before `x`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference

open scoped BigOperators

noncomputable section

/-! ### Common hypotheses -/

/-- The integers of the interval `I = [X, 2X)`: `I ∩ ℤ` [S-02:0175–0178]. -/
def intWindow (X : ℝ) : Finset ℤ := Finset.Ico ⌈X⌉ ⌈2 * X⌉

theorem mem_intWindow {X : ℝ} {n : ℤ} : n ∈ intWindow X ↔ X ≤ n ∧ (n : ℝ) < 2 * X := by
  unfold intWindow
  rw [Finset.mem_Ico, Int.ceil_le, Int.lt_ceil]

/-- **The standing hypotheses on a pattern family and on `k`** in Definition 3.3 and
Theorem 3.5, for `L = log x`:

* `|C_g| ≤ m` for every pattern and every big group [S-02:0055];
* (eq:pattern-mass): `∑_ν sup |K_ν| ≤ L^{C₁}` [S-02:0069–0071];
* `0 < |k| ≤ L^{C₂}` [S-02:0105]. -/
def Admissible {B : Type} [Fintype B] [DecidableEq B] {big : B → Finset ℕ} {J ℓ : ℕ}
    {N : Type} [Fintype N] (L : ℝ) (m : ℕ) (C₁ C₂ : ℝ) (𝔉 : N → Pattern big J ℓ) (k : ℤ) : Prop :=
  (∀ ν g, ((𝔉 ν).C g).card ≤ m) ∧ patternMass 𝔉 ≤ L ^ C₁ ∧ k ≠ 0 ∧ |(k : ℝ)| ≤ L ^ C₂

/-! ### Lemma 3.4 -/

/-- The conclusion of Lemma 3.4 for integer positions and fixed constants: for all sufficiently
large `x`, the operator `𝒜` with absolute coefficients and its adjoint have row sums at most
`L^{C_abs}` at every state. -/
def IntSchurBound (P : GroupParams) (m : ℕ) (C₁ Cabs : ℝ) (J : ℕ) (C₂ : ℝ) : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B) (N : Type) [Fintype N] (𝔉 : N → Pattern 𝔊.big J P.ℓ)
      (ζ : ℝ) (k : ℤ), Admissible (Real.log x) m C₁ C₂ 𝔉 k →
      ∀ s : PState intPos 𝔊.toGroupFamily J P.ℓ,
        physAbsRowSum intPos 𝔊.toGroupFamily P.q 𝔉 k ζ s ≤ Real.log x ^ Cabs ∧
          physAbsColSum intPos 𝔊.toGroupFamily P.q 𝔉 k ζ s ≤ Real.log x ^ Cabs

/-- The conclusion of Lemma 3.4 when "the position is replaced by independent uniform residues at
all group primes" [S-02:0138–0139]. -/
def ResidueSchurBound (P : GroupParams) (m : ℕ) (C₁ Cabs : ℝ) (J : ℕ) (C₂ : ℝ) : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B) (N : Type) [Fintype N] (𝔉 : N → Pattern 𝔊.big J P.ℓ)
      (ζ : ℝ) (k : ℤ), Admissible (Real.log x) m C₁ C₂ 𝔉 k →
      ∀ s : PState (residuePos 𝔊.toGroupFamily) 𝔊.toGroupFamily J P.ℓ,
        physAbsRowSum (residuePos 𝔊.toGroupFamily) 𝔊.toGroupFamily P.q 𝔉 k ζ s ≤
            Real.log x ^ Cabs ∧
          physAbsColSum (residuePos 𝔊.toGroupFamily) 𝔊.toGroupFamily P.q 𝔉 k ζ s ≤
            Real.log x ^ Cabs

/-- **[S] Lemma 3.4 (absolute physical bounds)** [S-02:0132–0140].

"Replace the coefficients of each row transition of `𝒜` by their absolute values before adding
patterns or averaging permutations. The resulting operator and its adjoint have row sums at most
`L^{C_abs}`, where `C_abs` may depend on `m, C₁` and the fixed data in Definition 3.1, but is
independent of `J`. The same assertion holds if the position is replaced by independent uniform
residues at all group primes."

Quantifiers: `C_abs` is chosen after `(P, m, C₁)` and before `J` and `C₂`. The paper states no
threshold for `x`; here one is allowed and may depend on everything fixed. The exponent `C₂` of
the bound on `k` is not used by the paper's proof; it only enters through the standing hypothesis
`0 < |k| ≤ L^{C₂}` of Definition 3.3. -/
def PhysicalSchur : Prop :=
  ∀ (P : GroupParams) (m : ℕ) (C₁ : ℝ), ∃ Cabs : ℝ, ∀ (J : ℕ) (C₂ : ℝ),
    IntSchurBound P m C₁ Cabs J C₂ ∧ ResidueSchurBound P m C₁ Cabs J C₂

/-! ### Theorem 3.5 -/

/-- **The left side of (eq:transference-moment)** [S-02:0177–0181]:
`|I ∩ ℤ|⁻¹ ∑_{n ∈ I ∩ ℤ} ⟨u_n, (𝒜 𝒜*)^R u_n⟩` for `I = [X, 2X)` and `R = ⌈L^{0.52}⌉`, with the
parameter `q` and the exponent `ℓ` of `P`. -/
def averagedMoment {P : GroupParams} {x : ℝ} {S B : Type} [Fintype S] [Fintype B]
    [DecidableEq S] [DecidableEq B] (𝔊 : PrimeGroups P x S B) {J : ℕ} {N : Type} [Fintype N]
    (𝔉 : N → Pattern 𝔊.big J P.ℓ) (k : ℤ) (ζ : ℝ) (X : ℝ) : ℝ :=
  ((intWindow X).card : ℝ)⁻¹ *
    ∑ n ∈ intWindow X,
      physMoment intPos 𝔊.toGroupFamily P.q 𝔉 k ζ (transferR (Real.log x)) n

/-- **The conclusion of Theorem 3.5 for fixed constants** `(P, E, E_id, m, C₁, J, C₂, γ)`: for all
sufficiently large `x`, for every system of prime groups, every admissible pattern family and
`k`, and every real `ζ`: if `sup_Θ ‖𝒯(Θ)‖ ≤ L^{-E_id}` then, for every `X` with
`x^γ ≤ X ≤ x^{1/γ}`, the averaged moment (eq:transference-moment) is at most `L^{-EN}`, `N = 2R`
(`N = Graph.sourceMemoryLength L`). -/
def MomentBound (P : GroupParams) (E Eid : ℝ) (m : ℕ) (C₁ : ℝ) (J : ℕ) (C₂ γ : ℝ) : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B) (N : Type) [Fintype N] (𝔉 : N → Pattern 𝔊.big J P.ℓ)
      (ζ : ℝ) (k : ℤ), Admissible (Real.log x) m C₁ C₂ 𝔉 k →
      (∀ Θ : ℝ, idealOpNorm 𝔉 ζ Θ ≤ Real.log x ^ (-Eid)) →
      ∀ X : ℝ, x ^ γ ≤ X → X ≤ x ^ (1 / γ) →
        averagedMoment 𝔊 𝔉 k ζ X ≤
          Real.log x ^ (-(E * (Graph.sourceMemoryLength (Real.log x) : ℝ)))

/-- **[S] Theorem 3.5 (local transference)** [S-02:0163–0188].

"For every fixed `E > 0` there is `E_id > 0`, depending only on `E` and the fixed data in
Definition 3.1, with the following property. Assume `sup_Θ ‖𝒯(Θ)‖ ≤ L^{-E_id}`. Then, for every
sufficiently large fixed `J`, where the lower bound on `J` may also depend on `m, C₁`, put
`R = ⌈L^{0.52}⌉`, `N = 2R`. For every fixed `γ > 0` and `I = [X, 2X)` with `x^γ ≤ X ≤ x^{1/γ}`,
one has `|I ∩ ℤ|⁻¹ ∑_{n ∈ I ∩ ℤ} ⟨u_n, (𝒜 𝒜*)^R u_n⟩ ≤ L^{-EN}` for all sufficiently large `x`."

Quantifier order: `P, E ⟶ E_id ⟶ m, C₁ ⟶ J₀ ⟶ J ≥ J₀ ⟶ C₂, γ ⟶ x₀ ⟶` everything else
(`MomentBound`). -/
def LocalTransference : Prop :=
  ∀ (P : GroupParams) (E : ℝ), 0 < E → ∃ Eid : ℝ, 0 < Eid ∧
    ∀ (m : ℕ) (C₁ : ℝ), ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J →
      ∀ C₂ γ : ℝ, 0 < γ → MomentBound P E Eid m C₁ J C₂ γ

/-! ### Corollary 3.11 -/

/-- **The hypotheses of Corollary 3.11 on the two endpoints** [S-02:1268–1275], for `I = [X, 2X)`:
`f = ∑_{n ∈ I ∩ ℤ} f_n u_n` is "supported on positions `I` and independent of the chosen marks,
with value `f_n` at position `n`"; `sup_{n ∈ I} |f_n| ≤ exp(C_sup √L)` (the paper writes
`exp(O(√L))`); `‖f‖, ‖g‖ ≤ X^{1/2} L^{C₃}`; and `g ∈ ℋ_ph` is arbitrary. -/
def EndpointHyp {P : GroupParams} {x : ℝ} {S B : Type} [Fintype S] [Fintype B]
    [DecidableEq S] [DecidableEq B] (𝔊 : PrimeGroups P x S B) (J : ℕ) (X C₃ Csup : ℝ)
    (fn : ℤ → ℂ) (g : PState intPos 𝔊.toGroupFamily J P.ℓ → ℂ) : Prop :=
  (∀ n ∈ intWindow X, ‖fn n‖ ≤ Real.exp (Csup * Real.sqrt (Real.log x))) ∧
    Real.sqrt (markFreeNormSq intPos 𝔊.toGroupFamily J P.ℓ (intWindow X) fn) ≤
      Real.sqrt X * Real.log x ^ C₃ ∧
    MemPhysL2 intPos 𝔊.toGroupFamily J P.ℓ g ∧
    Real.sqrt (physNormSq intPos 𝔊.toGroupFamily J P.ℓ g) ≤ Real.sqrt X * Real.log x ^ C₃

/-- **The conclusion of Corollary 3.11 for fixed constants**: there are `M` and `x₀` such that for
`x ≥ x₀`, under the hypotheses of Theorem 3.5 (admissible family and `k`, the ideal estimate
`sup_Θ ‖𝒯(Θ)‖ ≤ L^{-E_id}`, `x^γ ≤ X ≤ x^{1/γ}`) and the endpoint hypotheses,
`|⟨f, 𝒜 g⟩| ≤ M X L^{-E + 2C₃}` (eq:transference-pairing). -/
def PairingBound (P : GroupParams) (E Eid : ℝ) (m : ℕ) (C₁ : ℝ) (J : ℕ)
    (C₂ γ C₃ Csup : ℝ) : Prop :=
  ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B) (N : Type) [Fintype N] (𝔉 : N → Pattern 𝔊.big J P.ℓ)
      (ζ : ℝ) (k : ℤ), Admissible (Real.log x) m C₁ C₂ 𝔉 k →
      (∀ Θ : ℝ, idealOpNorm 𝔉 ζ Θ ≤ Real.log x ^ (-Eid)) →
      ∀ X : ℝ, x ^ γ ≤ X → X ≤ x ^ (1 / γ) →
      ∀ (fn : ℤ → ℂ) (g : PState intPos 𝔊.toGroupFamily J P.ℓ → ℂ),
        EndpointHyp 𝔊 J X C₃ Csup fn g →
        ‖pairMarkFree intPos 𝔊.toGroupFamily J P.ℓ (intWindow X) fn
            (physOp intPos 𝔊.toGroupFamily P.q 𝔉 k ζ g)‖ ≤
          M * X * Real.log x ^ (-E + 2 * C₃)

/-- **[S] Corollary 3.11 (endpoint pairing)** [S-02:1266–1283].

"Under the hypotheses and choices of Theorem 3.5, let `f ∈ ℋ_ph` be supported on positions
`I = [X, 2X)` and independent of the chosen marks, with value `f_n` at position `n`. Suppose
`sup_{n ∈ I} |f_n| ≤ exp(O(√L))`, `‖f‖, ‖g‖ ≤ X^{1/2} L^{C₃}`. Then
`|⟨f, 𝒜 g⟩| ≪ X L^{-E + 2C₃}`. Only the first endpoint must be independent of its mark list."

The corollary is stated here in the form its proof [S-02:1285–1339] gives: for every choice of
the constants `(P, E, E_id, m, C₁, J, C₂, γ)`, the conclusion of Theorem 3.5 for these constants
(`MomentBound`) implies the pairing bound for these constants and every `C₃, C_sup`
(`PairingBound`). "Under the hypotheses and choices of Theorem 3.5" then means: for the `E_id` and
the `J ≥ J₀` supplied by `LocalTransference`; that combination is `LocalTransferenceWithPairing`,
proved from the two statements in `localTransferenceWithPairing_of`. -/
def EndpointPairing : Prop :=
  ∀ (P : GroupParams) (E Eid : ℝ) (m : ℕ) (C₁ : ℝ) (J : ℕ) (C₂ γ : ℝ), 0 < E → 0 < γ →
    MomentBound P E Eid m C₁ J C₂ γ → ∀ C₃ Csup : ℝ, PairingBound P E Eid m C₁ J C₂ γ C₃ Csup

/-- **Theorem 3.5 and Corollary 3.11 with the same choices of `E_id` and `J₀`**: the moment bound
and the pairing bound. -/
def LocalTransferenceWithPairing : Prop :=
  ∀ (P : GroupParams) (E : ℝ), 0 < E → ∃ Eid : ℝ, 0 < Eid ∧
    ∀ (m : ℕ) (C₁ : ℝ), ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J →
      ∀ C₂ γ : ℝ, 0 < γ → MomentBound P E Eid m C₁ J C₂ γ ∧
        ∀ C₃ Csup : ℝ, PairingBound P E Eid m C₁ J C₂ γ C₃ Csup

/-- Theorem 3.5 and Corollary 3.11 give the combined statement (pure logic). -/
theorem localTransferenceWithPairing_of (h₁ : LocalTransference) (h₂ : EndpointPairing) :
    LocalTransferenceWithPairing := by
  intro P E hE
  obtain ⟨Eid, hEid, h⟩ := h₁ P E hE
  refine ⟨Eid, hEid, fun m C₁ => ?_⟩
  obtain ⟨J₀, hJ⟩ := h m C₁
  refine ⟨J₀, fun J hJ₀ C₂ γ hγ => ?_⟩
  have hM := hJ J hJ₀ C₂ γ hγ
  exact ⟨hM, h₂ P E Eid m C₁ J C₂ γ hE hγ hM⟩

/-! ### Lemma 4.3 -/

/-- **The comparison estimate (eq:ideal-comparison) for fixed exponents** [S-03:0274–0288]: with
`Q = L^{q_*}`, `h = L^{-h_*}`, `ξ = L^{-x_*}`, for all sufficiently large `x`, every system of
prime groups whose big groups are intervals of primes [S-03:0004–0006], all nonempty slot sets
`A, B` with at most `m` slots per big group, all tests `f` on the tuples of `X_B` and `g` on the
tuples of `X_A`, every `α ∈ ℝ` and every `|ζ| ≤ L^{C₄}`:
`|E conj(f(X_B)) g(X_A) [(X_A X_B)^{iζ} e(α X_A X_B) - 𝒦_A 𝒦_B (D_A D_B)^{iζ} e(α D_A D_B)]|
≤ L^{-A₀} ‖f‖₂ ‖g‖₂`.

The slot sets live in `{1, …, J}` for an arbitrary `J` chosen after `x₀`; only the numbers of
slots per group matter, so this is the paper's "independent of `J`". -/
def ComparisonContract (P : GroupParams) (m : ℕ) (A₀ C₄ qs hs xs : ℝ) : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B), (∀ g, IsPrimeInterval (𝔊.big g)) →
    ∀ (J : ℕ) (A Bs : B → Finset (Fin J)),
      (∃ g, (A g).Nonempty) → (∃ g, (Bs g).Nonempty) →
      (∀ g, (A g).card ≤ m) → (∀ g, (Bs g).card ≤ m) →
    ∀ (f : AuxList 𝔊.big Bs → ℂ) (g : AuxList 𝔊.big A → ℂ) (α ζ : ℝ),
      |ζ| ≤ Real.log x ^ C₄ →
      ‖comparisonDefect 𝔊.big A Bs (Real.log x ^ qs) (Real.log x ^ (-hs)) (Real.log x ^ (-xs))
          f g α ζ‖ ≤
        Real.log x ^ (-A₀) * (tupleNorm 𝔊.big Bs f * tupleNorm 𝔊.big A g)

/-- **[S] Lemma 4.3 (comparison kernel)** [S-03:0270–0292].

"Fix `m`, `A₀ > 0`, and `C₄ ≥ 0`. There are fixed powers `Q, h⁻¹, ξ⁻¹` of `L`, independent of
`J`, such that the kernels in (eq:ideal-cell-kernel) have the following property. Let `A, B` be
nonempty sets of slots, using at most `m` slots per big group. Take independent label tuples for
`D_A, X_A, D_B, X_B` with the prescribed slot laws. If `f` and `g` are arbitrary `L²` tests on the
tuples making up `X_B` and `X_A`, respectively, then for every `α ∈ ℝ` and `|ζ| ≤ L^{C₄}`,
(eq:ideal-comparison) holds. … The kernels are independent of `α` and `ζ`."

The exponents `q_*, h_*, x_* ≥ 0` (`Q ≥ 1`, `0 < h ≤ 1`, `0 < ξ ≤ 1` as in [S-03:0179–0180]) are
chosen after `(P, m, A₀, C₄)` and before `x`. -/
def ComparisonKernelLemma : Prop :=
  ∀ (P : GroupParams) (m : ℕ) (A₀ C₄ : ℝ), 0 < A₀ → 0 ≤ C₄ →
    ∃ qs hs xs : ℝ, 0 ≤ qs ∧ 0 ≤ hs ∧ 0 ≤ xs ∧ ComparisonContract P m A₀ C₄ qs hs xs

/-! ### Theorem 4.1 -/

/-- **The conclusion of Theorem 4.1 for fixed constants**: for all sufficiently large `x`, every
system of prime groups whose big groups are intervals of primes, and every balanced split of the
big groups into two blocks, the residual family `comparisonFamily` (raw pattern and signed
comparison patterns, with kernel parameters `Q = L^{q_*}`, `h = L^{-h_*}`, `ξ = L^{-x_*}`)
satisfies `∑_ν sup |K_ν| ≤ L^{C₁}` and (eq:ideal-small-norm):
`‖𝒯(Θ)‖ ≤ L^{-E_id}` for every real `Θ` and every `|ζ| ≤ L^{C₄}`. -/
def IdealFamilyBound (P : GroupParams) (Eid C₄ : ℝ) (m : ℕ) (C₁ : ℝ) (J : ℕ)
    (qs hs xs : ℝ) : Prop :=
  ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B), (∀ g, IsPrimeInterval (𝔊.big g)) →
    ∀ blk : B → Bool, BalancedSplit blk →
      patternMass (comparisonFamily 𝔊.big J P.ℓ m blk (Real.log x ^ qs) (Real.log x ^ (-hs))
          (Real.log x ^ (-xs))) ≤ Real.log x ^ C₁ ∧
        ∀ Θ ζ : ℝ, |ζ| ≤ Real.log x ^ C₄ →
          idealOpNorm (comparisonFamily 𝔊.big J P.ℓ m blk (Real.log x ^ qs)
            (Real.log x ^ (-hs)) (Real.log x ^ (-xs))) ζ Θ ≤ Real.log x ^ (-Eid)

/-- **[S] Theorem 4.1 (construction of the residual ideal operator)** [S-03:0011–0052].

"Fix `E_id > 0` and a fixed frequency exponent `C₄ ≥ 0`. There are fixed integers `m, J₀` and a
fixed constant `C₁`, depending only on these parameters, `ℓ`, and the prime-group bounds, with the
following property. For every fixed `J ≥ J₀`, there is a family consisting of the raw pattern
`C_g = ∅` for every `g`, `K₀ = 1`, and signed comparison patterns satisfying `C_g = ∅ (g ∈ 𝒮)`,
`|C_g| ≤ m (g ∈ ℬ)`, `∑_ν sup |K_ν| ≤ L^{C₁}`, such that the symmetrized ideal operator satisfies
`sup_{Θ ∈ ℝ, |ζ| ≤ L^{C₄}} ‖𝒯(Θ)‖_{2 → 2} ≤ L^{-E_id}` for sufficiently large `x`. The
coefficients and the family are independent of `Θ` and of the individual value of `ζ`. Their
defining parameters are independent of `J`; `J` only supplies the available shared slots. The
threshold for `x` may depend on `J`."

The family is the explicit `comparisonFamily` of the "more precisely" part [S-03:0038–0052]; that
`|C_g| ≤ m` holds for it is `comparisonFamily_card_le`. The exponents of the kernel parameters
`Q, h⁻¹, ξ⁻¹` ("each kernel is a finite sum of products of matched log-cell indicators and pairs
of Dirichlet characters of conductor bounded by a fixed power of `L`") are chosen with
`m, J₀, C₁`, before `J`. The big groups are intervals of primes [S-03:0004–0006]. The paper says
"split the big groups into two blocks"; its proof takes blocks whose sizes differ by at most one
[S-03:0442–0443], and the statement here is for every such split. -/
def IdealConstruction : Prop :=
  ∀ (P : GroupParams) (Eid C₄ : ℝ), 0 < Eid → 0 ≤ C₄ →
    ∃ (m J₀ : ℕ) (C₁ qs hs xs : ℝ), 0 ≤ qs ∧ 0 ≤ hs ∧ 0 ≤ xs ∧
      ∀ J : ℕ, J₀ ≤ J → IdealFamilyBound P Eid C₄ m C₁ J qs hs xs

end

end SimultaneousPrimitiveRoots.Unconditional.Transference
