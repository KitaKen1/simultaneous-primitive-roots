module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Statements
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# `Graph/` lemmas for the tilted laws of the big groups of Definition 3.1

Source: `verification/stage7-sources/S-02.tex`, (eq:lifespan-baseline) [S-02:0318–0325],
(eq:tilted-point-mass) [S-02:1114–1117].

`Graph/` proves the perturbation estimates for `b_p` and `μ̃_g` for one finite set of primes with
explicit hypotheses; `GraphBridge.lean` instantiates the uniform ratio bound. This file adds the
instantiations for the objects of this directory (`lifeBaseline`, `tiltLaw`, `baselineProd`,
`memMeasure`: the visits `0, …, N` and the coefficients `η_i = 1 - q_i`), all "for sufficiently
large `x`, uniformly in the system of prime groups":

| here | `Graph/` | paper |
|---|---|---|
| `eventually_big_tilt` | `eventually_source_log_prime_group_law_uniform` (via `GraphBridge`) | `b_p > 0`, `μ̃_g > 0`, `μ̃_g ≤ (1 + ε) μ_g` |
| `eventually_tiltLaw_relative_error` | `eventually_source_lifespan_relative_error` | "the ratio `μ̃_g(p)/μ_g(p)` is `1 + O(N/P_*)`, uniformly in big groups" |
| `eventually_tiltLaw_le` | — | (eq:tilted-point-mass) `sup μ̃_g(p) ≪ P_*^{-1}` |
| `eventually_tiltLaw_sum_le` | `tilted_prime_group_law_total_le_two` | `μ̃_g(𝒫_g) ≤ 2` ("`ν(𝒫_g) = 1 + o(1)`") |
| `eventually_baselineProd` | `prime_lifespan_baseline_le_one` | "the common baseline `∏_{p big} b_p ≤ 1`" |
| `eventually_memMeasure_nonneg` | — | the measure of `ℋ` is nonnegative |
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

open Filter

noncomputable section

/-- **(eq:lifespan-baseline) for the big groups of Definition 3.1** [S-02:0318–0325]: for every
`ε > 0` and all sufficiently large `x`, uniformly in the prime groups: `b_p > 0`, `μ̃_g(p) > 0`
and `μ̃_g(p) ≤ (1 + ε) μ_g(p)` for every big prime `p`. -/
theorem eventually_big_tilt (P : GroupParams) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, ∀ (S B : Type) [Fintype S] [Fintype B] (𝔊 : PrimeGroups P x S B)
      (g : B), ∀ p ∈ 𝔊.big g,
        0 < lifeBaseline P.q (Graph.sourceMemoryLength (Real.log x)) p ∧
          0 < tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p ∧
          tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p ≤
            (1 + ε) * Graph.primeGroupLaw (𝔊.big g) p := by
  filter_upwards [PrimeGroups.eventually_big_tilted_law_uniform P hε] with x hx
  intro S B _ _ 𝔊 g p hp
  have hcard : (Finset.range (Graph.sourceMemoryLength (Real.log x) + 1)).card ≤
      Graph.sourceMemoryLength (Real.log x) + 1 := by
    rw [Finset.card_range]
  obtain ⟨hb, _, h2⟩ := hx S B 𝔊 g ℕ
    (Finset.range (Graph.sourceMemoryLength (Real.log x) + 1))
    (visitEta P.q (Graph.sourceMemoryLength (Real.log x))) hcard
    (fun i _ => visitEta_nonneg P.q_pos P.q_lt_one _ i)
    (fun i _ => visitEta_le_one P.q_pos P.q_lt_one _ i) p hp
  have hlaw := 𝔊.big_law_pos g p hp
  refine ⟨hb, ?_, ?_⟩
  · exact Graph.tilted_prime_group_law_pos _ (𝔊.big_nonempty g) (𝔊.prime_big g) _ _ p hp hb
  · exact (div_le_iff₀ hlaw).mp h2

/-- **"The ratio `μ̃_g(p)/μ_g(p)` is `1 + O(N/P_*)`, uniformly in big groups"** [S-02:0323–0324]:
`|μ̃_g(p)/μ_g(p) - 1| ≤ 4N/P_*` for all sufficiently large `x`. This is
`Graph.eventually_source_lifespan_relative_error` for the big groups of Definition 3.1 (the bridge
asked for in the review note of `docs/unconditional-roadmap.md`); Lemma 3.10 uses it
[S-02:0986–0999]. -/
theorem eventually_tiltLaw_relative_error (P : GroupParams) :
    ∀ᶠ x : ℝ in atTop, ∀ (S B : Type) [Fintype S] [Fintype B] (𝔊 : PrimeGroups P x S B)
      (g : B), ∀ p ∈ 𝔊.big g,
        |tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p /
            Graph.primeGroupLaw (𝔊.big g) p - 1| ≤
          4 * (Graph.sourceMemoryLength (Real.log x) : ℝ) /
            Graph.sourcePrimeLowerBound P.c (Real.log x) := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (Graph.eventually_source_lifespan_relative_error.{0} P.c P.c_pos)] with x hx
  intro S B _ _ 𝔊 g p hp
  have hcard : (Finset.range (Graph.sourceMemoryLength (Real.log x) + 1)).card ≤
      Graph.sourceMemoryLength (Real.log x) + 1 := by
    rw [Finset.card_range]
  exact hx ℕ (𝔊.big g) (𝔊.big_nonempty g) (𝔊.prime_big g)
    (Finset.range (Graph.sourceMemoryLength (Real.log x) + 1))
    (visitEta P.q (Graph.sourceMemoryLength (Real.log x))) hcard
    (fun i _ => visitEta_nonneg P.q_pos P.q_lt_one _ i)
    (fun i _ => visitEta_le_one P.q_pos P.q_lt_one _ i) p hp (𝔊.big_ge g p hp)

/-- **(eq:tilted-point-mass)** [S-02:1114–1117]: `sup_{g ∈ ℬ, p ∈ 𝒫_g} μ̃_g(p) ≪ P_*^{-1}`; here
`μ̃_g(p) ≤ 2 / (v₋ P_*)` for all sufficiently large `x`. -/
theorem eventually_tiltLaw_le (P : GroupParams) :
    ∀ᶠ x : ℝ in atTop, ∀ (S B : Type) [Fintype S] [Fintype B] (𝔊 : PrimeGroups P x S B)
      (g : B), ∀ p ∈ 𝔊.big g,
        tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p ≤
          2 / (P.vMinus * Graph.sourcePrimeLowerBound P.c (Real.log x)) := by
  filter_upwards [eventually_big_tilt P one_pos] with x hx
  intro S B _ _ 𝔊 g p hp
  obtain ⟨_, _, h⟩ := hx S B 𝔊 g p hp
  have hPpos : 0 < Graph.sourcePrimeLowerBound P.c (Real.log x) :=
    Graph.source_prime_lower_bound_pos _ _
  have hden : 0 < P.vMinus * Graph.sourcePrimeLowerBound P.c (Real.log x) :=
    mul_pos P.vMinus_pos hPpos
  have hle : P.vMinus * Graph.sourcePrimeLowerBound P.c (Real.log x) ≤
      Graph.primeGroupReciprocalMass (𝔊.big g) * (p : ℝ) :=
    mul_le_mul (𝔊.mass_big_ge g) (𝔊.big_ge g p hp) hPpos.le
      (PrimeGroups.mass_pos_of_ge (𝔊.mass_big_ge g)).le
  have hlaw : Graph.primeGroupLaw (𝔊.big g) p ≤
      1 / (P.vMinus * Graph.sourcePrimeLowerBound P.c (Real.log x)) := by
    unfold Graph.primeGroupLaw
    exact one_div_le_one_div_of_le hden hle
  calc tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p
      ≤ (1 + 1) * Graph.primeGroupLaw (𝔊.big g) p := h
    _ ≤ (1 + 1) * (1 / (P.vMinus * Graph.sourcePrimeLowerBound P.c (Real.log x))) :=
        mul_le_mul_of_nonneg_left hlaw (by norm_num)
    _ = 2 / (P.vMinus * Graph.sourcePrimeLowerBound P.c (Real.log x)) := by ring

/-- **`μ̃_g(𝒫_g) ≤ 2`** for all sufficiently large `x` ("`ν(𝒫_g) = 1 + o(1)`", [S-02:0694];
"fresh integrations have mass `μ̃_g(𝒫_g)^{t_g - a_g} ≤ 2^{t_g}` for large `x`", [S-02:0779–0781]). -/
theorem eventually_tiltLaw_sum_le (P : GroupParams) :
    ∀ᶠ x : ℝ in atTop, ∀ (S B : Type) [Fintype S] [Fintype B] (𝔊 : PrimeGroups P x S B)
      (g : B),
        ∑ p ∈ 𝔊.big g, tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p ≤ 2 := by
  filter_upwards [eventually_big_tilt P one_pos] with x hx
  intro S B _ _ 𝔊 g
  calc ∑ p ∈ 𝔊.big g, tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p
      ≤ ∑ p ∈ 𝔊.big g, (1 + 1) * Graph.primeGroupLaw (𝔊.big g) p :=
        Finset.sum_le_sum fun p hp => (hx S B 𝔊 g p hp).2.2
    _ = 2 := by
        rw [← Finset.mul_sum, 𝔊.big_law_sum g]
        norm_num

/-- **"The common baseline `∏_{p big} b_p ≤ 1`"** [S-02:0324–0325], and it is positive, for all
sufficiently large `x`. -/
theorem eventually_baselineProd (P : GroupParams) :
    ∀ᶠ x : ℝ in atTop, ∀ (S B : Type) [Fintype S] [Fintype B] (𝔊 : PrimeGroups P x S B),
      0 ≤ baselineProd (bigPrimes 𝔊.toGroupFamily) P.q (Graph.sourceMemoryLength (Real.log x)) ∧
        baselineProd (bigPrimes 𝔊.toGroupFamily) P.q (Graph.sourceMemoryLength (Real.log x)) ≤
          1 := by
  filter_upwards [eventually_big_tilt P one_pos] with x hx
  intro S B _ _ 𝔊
  unfold baselineProd
  constructor
  · refine Finset.prod_nonneg fun p hp => ?_
    obtain ⟨g, hg⟩ := mem_bigPrimes.mp hp
    exact (hx S B 𝔊 g p hg).1.le
  · have h0 : ∀ p ∈ bigPrimes 𝔊.toGroupFamily,
        0 ≤ lifeBaseline P.q (Graph.sourceMemoryLength (Real.log x)) p := by
      intro p hp
      obtain ⟨g, hg⟩ := mem_bigPrimes.mp hp
      exact (hx S B 𝔊 g p hg).1.le
    calc ∏ p ∈ bigPrimes 𝔊.toGroupFamily,
          lifeBaseline P.q (Graph.sourceMemoryLength (Real.log x)) p
        ≤ ∏ _p ∈ bigPrimes 𝔊.toGroupFamily, (1 : ℝ) :=
          Finset.prod_le_prod h0 fun p _ => lifeBaseline_le_one P.q_pos P.q_lt_one _ p
      _ = 1 := Finset.prod_const_one

/-- **The measure of `ℋ` is nonnegative** for all sufficiently large `x` (when `b_p > 0` for the
big primes). -/
theorem eventually_memMeasure_nonneg (P : GroupParams) :
    ∀ᶠ x : ℝ in atTop, ∀ (S B : Type) [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
      (𝔊 : PrimeGroups P x S B) (J Bc : ℕ) (s : MState 𝔊.toGroupFamily J P.ℓ Bc),
      0 ≤ memMeasure 𝔊 J Bc s := by
  filter_upwards [eventually_big_tilt P one_pos] with x hx
  intro S B _ _ _ _ 𝔊 J Bc s
  exact memWeight_nonneg 𝔊.toGroupFamily P.q _ (fun g p hp => (hx S B 𝔊 g p hp).2.1.le) s

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
