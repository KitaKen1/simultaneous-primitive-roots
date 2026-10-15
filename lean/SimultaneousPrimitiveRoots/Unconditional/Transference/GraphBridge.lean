module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.PrimeGroups
public import SimultaneousPrimitiveRoots.Unconditional.Transference.FiniteOperators
public import SimultaneousPrimitiveRoots.Unconditional.Graph.FiniteWeightedSchur
public import SimultaneousPrimitiveRoots.Unconditional.Graph.SourcePrimeUniformity
public import SimultaneousPrimitiveRoots.Unconditional.Graph.SourceGroupPolynomialLoss
public import SimultaneousPrimitiveRoots.Unconditional.Graph.ProbeShrinkage
import Mathlib.Tactic.Linarith

/-!
# The existing `Graph/` lemmas, stated for the prime groups of Definition 3.1

`Graph/` proves its bottom-up lemmas for one finite set of primes `s : Finset ℕ` with explicit
hypotheses (`s.Nonempty`, primality, `sourcePrimeLowerBound c L ≤ p`,
`primeGroupReciprocalMass s ≤ Vplus`, a bound `C0 * Real.log L` on a number of groups, `0 < ell`).
The fields of `PrimeGroups` and `GroupParams` are exactly these hypotheses, so the lemmas apply to
the groups of Definition 3.1 without change. This file records such instantiations:

| here | `Graph/` declaration | paper |
|---|---|---|
| `PrimeGroups.eventually_big_tilted_law_uniform` | `eventually_source_log_prime_group_law_uniform` | (eq:lifespan-baseline) [S-02:0318–0325] |
| `PrimeGroups.eventually_visits_le_big` | `source_prime_eventually_dominates_visits` | `N ≪ P_*` [S-02:0172–0174, 0318] |
| `PrimeGroups.prod_big_le_rpow`, `PrimeGroups.prod_small_le_rpow` | `source_finite_norm_product_polynomial` | "the product over `s = O(T)` groups" [S-02:0153–0154, 0697–0701] |
| `GroupParams.exists_ghost_weight` | `exists_source_ghost_uniform_weight` | (eq:memory-weight-choice) [S-02:0686–0693] |
| `GroupParams.exists_probe_count` | `exists_uniform_probe_fraction_lt` | the choice of `m`, [S-03:0499–0517, 0535–0540] |
| `wOpNorm_le_of_schur` | `finite_complex_weighted_schur` | (eq:weighted-schur) [S-02:0631–0638], for the norm `wOpNorm` in which Theorems 3.5 and 4.1 are stated |
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference

open scoped BigOperators

open Filter

noncomputable section

/-- **Schur's test (eq:weighted-schur) for the operator norm of `L²(X, w)`** [S-02:0631–0638]:
if a complex kernel `K` (with respect to the measure `w`) is dominated by a nonnegative kernel
`κ` which satisfies `κ u ≤ R u` and `κ* u ≤ C u` for a positive function `u`, then the kernel
operator `F ↦ (i ↦ ∑_j K i j w_j F_j)` has norm at most `√(RC)`. This is
`Graph.finite_complex_weighted_schur`, restated for `wOpNorm`, the norm of `idealOpNorm`. -/
theorem wOpNorm_le_of_schur {X : Type*} [Fintype X] {w : X → ℝ} (hw : ∀ x, 0 < w x)
    (K : X → X → ℂ) (κ : X → X → ℝ) (u : X → ℝ) (R C : ℝ)
    (hK : ∀ i j, ‖K i j‖ ≤ κ i j) (hκ : ∀ i j, 0 ≤ κ i j) (hu : ∀ i, 0 < u i)
    (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hrow : ∀ i, ∑ j, κ i j * w j * u j ≤ R * u i)
    (hcol : ∀ j, ∑ i, κ i j * w i * u i ≤ C * u j) :
    wOpNorm w (rowOp (Ξ := X) (fun i j => K i j * (w j : ℂ)) (fun _ j => j)) ≤
      Real.sqrt (R * C) := by
  rw [wOpNorm_le_iff hw _ (Real.sqrt_nonneg _)]
  intro F
  have h := Graph.finite_complex_weighted_schur K κ w w u u R C hK hκ (fun i => (hw i).le)
    (fun j => (hw j).le) hu hu hR hC hrow hcol F
  unfold wNorm
  rw [← Real.sqrt_mul (mul_nonneg hR hC)]
  exact Real.sqrt_le_sqrt h

theorem GroupParams.c_pos (P : GroupParams) : 0 < P.c := by
  linarith [P.a_pos, P.a_lt_b, P.b_lt_c]

/-- **(eq:lifespan-baseline) for the big groups of Definition 3.1** [S-02:0318–0325]: for every
`ε > 0` and all sufficiently large `x`, uniformly in the system of prime groups, the big group,
the set of at most `N + 1` visits and the coefficients `η_i ∈ [0, 1]`: `b_p > 0` and
`1 ≤ μ̃_g(p) / μ_g(p) ≤ 1 + ε`. This is `Graph.eventually_source_log_prime_group_law_uniform`;
its hypothesis on the size of `p` is the field `PrimeGroups.big_ge`. -/
theorem PrimeGroups.eventually_big_tilted_law_uniform (P : GroupParams) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ (S B : Type) [Fintype S] [Fintype B] (𝔊 : PrimeGroups P x S B)
      (g : B) (I : Type) (visits : Finset I) (η : I → ℝ),
      visits.card ≤ Graph.sourceMemoryLength (Real.log x) + 1 →
      (∀ i ∈ visits, 0 ≤ η i) → (∀ i ∈ visits, η i ≤ 1) →
      ∀ p ∈ 𝔊.big g,
        0 < Graph.primeLifespanBaseline visits η p ∧
          1 ≤ Graph.tiltedPrimeGroupLaw (𝔊.big g) visits η p /
            Graph.primeGroupLaw (𝔊.big g) p ∧
          Graph.tiltedPrimeGroupLaw (𝔊.big g) visits η p /
            Graph.primeGroupLaw (𝔊.big g) p ≤ 1 + ε := by
  filter_upwards [Graph.eventually_source_log_prime_group_law_uniform.{0} P.c ε P.c_pos hε]
    with x hx
  intro S B _ _ 𝔊 g I visits η hcard h0 h1 p hp
  exact hx I (𝔊.big g) (𝔊.big_nonempty g) (𝔊.prime_big g) visits η hcard h0 h1 p hp
    (𝔊.big_ge g p hp)

/-- **`N ≪ P_*`** [S-02:0172–0174, 0318]: for all sufficiently large `x`, every prime of a big
group is at least `2 (N + 1)`, twice the number of visits. This is
`Graph.source_prime_eventually_dominates_visits` with `L = log x`. -/
theorem PrimeGroups.eventually_visits_le_big (P : GroupParams) :
    ∀ᶠ x : ℝ in atTop, ∀ (S B : Type) [Fintype S] [Fintype B] (𝔊 : PrimeGroups P x S B)
      (g : B), ∀ p ∈ 𝔊.big g,
        2 * ((Graph.sourceMemoryLength (Real.log x) : ℝ) + 1) ≤ (p : ℝ) := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (Graph.source_prime_eventually_dominates_visits P.c P.c_pos)] with x hx
  intro S B _ _ 𝔊 g p hp
  exact hx.trans (𝔊.big_ge g p hp)

section Products

variable {P : GroupParams} {x : ℝ} {S B : Type} [Fintype S] [Fintype B]

/-- **A product of bounded factors over the big groups is a power of `L`**: if `0 ≤ F g ≤ e^b`
for every big group then `∏_g F g ≤ L^{b C₀}` ("taking the product over `s = O(T)` groups",
[S-02:0153–0154, 0697–0701]). This is `Graph.source_finite_norm_product_polynomial`; its
hypothesis on the number of groups is the field `PrimeGroups.card_big_le`. -/
theorem PrimeGroups.prod_big_le_rpow (𝔊 : PrimeGroups P x S B) (hx : 0 < Real.log x)
    (F : B → ℝ) (b : ℝ) (hb : 0 ≤ b) (hF0 : ∀ g, 0 ≤ F g) (hF : ∀ g, F g ≤ Real.exp b) :
    ∏ g, F g ≤ Real.log x ^ (b * P.C₀) :=
  Graph.source_finite_norm_product_polynomial Finset.univ F (Real.log x) b P.C₀ hx hb
    (by rw [Finset.card_univ]; exact 𝔊.card_big_le) (fun g _ => hF0 g) (fun g _ => hF g)

/-- The same for the small groups. -/
theorem PrimeGroups.prod_small_le_rpow (𝔊 : PrimeGroups P x S B) (hx : 0 < Real.log x)
    (F : S → ℝ) (b : ℝ) (hb : 0 ≤ b) (hF0 : ∀ g, 0 ≤ F g) (hF : ∀ g, F g ≤ Real.exp b) :
    ∏ g, F g ≤ Real.log x ^ (b * P.C₀) :=
  Graph.source_finite_norm_product_polynomial Finset.univ F (Real.log x) b P.C₀ hx hb
    (by rw [Finset.card_univ]; exact 𝔊.card_small_le) (fun g _ => hF0 g) (fun g _ => hF g)

end Products

/-- **(eq:memory-weight-choice) for the constants of Definition 3.1** [S-02:0686–0693]: for
`0 < ρ` with `ρ² > √q` there is one weight `v > 1` such that, for both values `q_i ∈ {q, √q}`,
every `0 ≤ V ≤ v₊` and every birth multiplier `γ ∈ [0, 2]`, the ghost coefficients
`A = q_i/ρ²`, `D = -(1 - q_i)/ρ`, `C = V D` satisfy `A + |D|/v < 1` and `A + |γ C|/v < 1`. This is
`Graph.exists_source_ghost_uniform_weight` with `q = P.q` and `Vplus = P.vPlus`. -/
theorem GroupParams.exists_ghost_weight (P : GroupParams) {ρ : ℝ} (hρ : 0 < ρ)
    (hgap : Real.sqrt P.q < ρ ^ 2) :
    ∃ v : ℝ, 1 < v ∧ ∀ qi V γ : ℝ,
      (qi = P.q ∨ qi = Real.sqrt P.q) → 0 ≤ V → V ≤ P.vPlus → 0 ≤ γ → γ ≤ 2 →
      0 ≤ Graph.sourceGhostA qi ρ ∧
      Graph.sourceGhostA qi ρ + |Graph.sourceGhostD qi ρ| / v < 1 ∧
      Graph.sourceGhostA qi ρ + |γ * Graph.sourceGhostC V qi ρ| / v < 1 ∧
      |Graph.sourceGhostD qi ρ| ≤ 1 / ρ ∧
      |γ * Graph.sourceGhostC V qi ρ| ≤ 2 * max 1 P.vPlus / ρ :=
  Graph.exists_source_ghost_uniform_weight P.q ρ P.vPlus P.q_pos P.q_lt_one hρ hgap

/-- **The choice of the probe count `m` in Theorem 4.1** [S-03:0499–0517, 0535–0540]: since
`ℓ ≥ 1`, for every `ε > 0` there is `m ≥ 1` such that the Hoeffding fraction
(eq:ideal-hoeffding-fraction) `C(M - m - ℓ, j - m) / C(M, j)` is smaller than `ε` for all slot
counts `M ≥ (m + ℓ)(m + ℓ - 1)` and all degrees `j`. This is
`Graph.exists_uniform_probe_fraction_lt` with `ell = P.ℓ` and `GroupParams.ℓ_pos`. -/
theorem GroupParams.exists_probe_count (P : GroupParams) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ ∀ M j : ℕ, m ≤ j → j ≤ M → P.ℓ ≤ M - j →
      (m + P.ℓ) * (m + P.ℓ - 1) ≤ M →
      ((M - m - P.ℓ).choose (j - m) : ℝ) / (M.choose j : ℝ) < ε := by
  obtain ⟨m, _, hm, h⟩ := Graph.exists_uniform_probe_fraction_lt P.ℓ_pos hε 0
  exact ⟨m, hm, h⟩

end

end SimultaneousPrimitiveRoots.Unconditional.Transference
