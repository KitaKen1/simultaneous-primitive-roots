module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.BoundaryMass
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Bridge
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The boundary vector `𝟏_∅` has bounded norm

Source: `verification/stage7-sources/S-02.tex`, lines 296–302 and 812–819
(`[S-02:0296–0302, 0812–0819]`).

`boundaryNorm : BoundaryNorm` — "the empty-memory boundary vector has bounded norm: the small part
has mass at most one by (eq:initial-factorial-mass), and the big part has mass
`∏_{g ∈ ℬ} μ̃_g(𝒫_g)^M = 1 + O_J(sN/P_*) = 1 + o(1)`"; here `‖𝟏_∅‖² ≤ 2` for `x ≥ x₀(P, J)` and
every cutoff.

By `boundary_wNormSq_eq` (`BoundaryMass.lean`), `‖𝟏_∅‖²` is the product of the small part, which
is at most one (`boundary_smallPart_le_one`), and of `∏_{g ∈ ℬ} μ̃_g(𝒫_g)^M`. The ratio
`μ̃_g(p)/μ_g(p)` is `1 + O(N/P_*)` (`eventually_tiltLaw_relative_error`), so
`μ̃_g(𝒫_g) ≤ 1 + 4N/P_* ≤ exp(4N/P_*)`, and the product over the at most `C₀ T` big groups is at
most `L^{4 M N C₀ / P_*} = exp(4 M N C₀ T / P_*) ≤ 2` for large `x`
(`boundary_scalar_eventually`: `N ≪ L^{0.52}`, `T ≤ L`, `P_* = exp(L^c)`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

open Filter

noncomputable section

/-- **`M · (N/P_*) · C₀ · T = o(1)`**: for all sufficiently large `L`,
`log L · (M · 4N/P_* · C₀) ≤ log 2`, with `M = J + ℓ`, `N = Graph.sourceMemoryLength L`,
`P_* = exp(L^c)`. -/
theorem boundary_scalar_eventually (P : GroupParams) (J : ℕ) :
    ∀ᶠ L : ℝ in atTop,
      Real.log L * (((J + P.ℓ : ℕ) : ℝ) *
        (4 * (Graph.sourceMemoryLength L : ℝ) / Graph.sourcePrimeLowerBound P.c L) * P.C₀) ≤
        Real.log 2 := by
  have hM0 : (0 : ℝ) < ((J + P.ℓ : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.add_pos_right J P.ℓ_pos)
  have hK : 0 < 16 * ((J + P.ℓ : ℕ) : ℝ) * P.C₀ :=
    mul_pos (mul_pos (by norm_num) hM0) P.C₀_pos
  have hε : 0 < Real.log 2 / (16 * ((J + P.ℓ : ℕ) : ℝ) * P.C₀) :=
    div_pos (Real.log_pos one_lt_two) hK
  filter_upwards [(Graph.source_rpow_div_prime_lower_bound_tendsto ((38 : ℝ) / 25) P.c
    P.c_pos).eventually (gt_mem_nhds hε), eventually_ge_atTop (1 : ℝ)] with L hL hL1
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hP : 0 < Graph.sourcePrimeLowerBound P.c L := Graph.source_prime_lower_bound_pos _ _
  have ht1 : 1 ≤ L ^ ((13 : ℝ) / 25) := Real.one_le_rpow hL1 (by norm_num)
  have hN : (Graph.sourceMemoryLength L : ℝ) ≤ 4 * L ^ ((13 : ℝ) / 25) := by
    have := Graph.source_memory_length_upper L hL0.le
    linarith
  have hlog : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hL0).trans (by linarith)
  have hu : L ^ ((38 : ℝ) / 25) = L * L ^ ((13 : ℝ) / 25) := by
    rw [show (38 : ℝ) / 25 = 1 + 13 / 25 by norm_num, Real.rpow_add hL0, Real.rpow_one]
  have hX' : ((J + P.ℓ : ℕ) : ℝ) *
        (4 * (Graph.sourceMemoryLength L : ℝ) / Graph.sourcePrimeLowerBound P.c L) * P.C₀ ≤
      ((J + P.ℓ : ℕ) : ℝ) *
        (4 * (4 * L ^ ((13 : ℝ) / 25)) / Graph.sourcePrimeLowerBound P.c L) * P.C₀ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (by linarith) hP.le) hM0.le) P.C₀_pos.le
  have hX0 : 0 ≤ ((J + P.ℓ : ℕ) : ℝ) *
      (4 * (Graph.sourceMemoryLength L : ℝ) / Graph.sourcePrimeLowerBound P.c L) * P.C₀ :=
    mul_nonneg (mul_nonneg hM0.le
      (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hP.le)) P.C₀_pos.le
  calc Real.log L * (((J + P.ℓ : ℕ) : ℝ) *
        (4 * (Graph.sourceMemoryLength L : ℝ) / Graph.sourcePrimeLowerBound P.c L) * P.C₀)
      ≤ L * (((J + P.ℓ : ℕ) : ℝ) *
          (4 * (4 * L ^ ((13 : ℝ) / 25)) / Graph.sourcePrimeLowerBound P.c L) * P.C₀) :=
        mul_le_mul hlog hX' hX0 hL0.le
    _ = 16 * ((J + P.ℓ : ℕ) : ℝ) * P.C₀ *
          (L ^ ((38 : ℝ) / 25) / Graph.sourcePrimeLowerBound P.c L) := by
        rw [hu]
        ring
    _ ≤ 16 * ((J + P.ℓ : ℕ) : ℝ) * P.C₀ *
          (Real.log 2 / (16 * ((J + P.ℓ : ℕ) : ℝ) * P.C₀)) :=
        mul_le_mul_of_nonneg_left hL.le hK.le
    _ = Real.log 2 := by rw [mul_div_assoc', mul_div_cancel_left₀ _ hK.ne']

/-- **The boundary vector has bounded norm** [S-02:0812–0819], proved: `‖𝟏_∅‖² ≤ 2` for
`x ≥ x₀(P, J)`, for every system of prime groups and every cutoff. -/
theorem boundaryNorm : BoundaryNorm := by
  intro P J
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp ((eventually_big_tilt P one_pos).and
    ((eventually_tiltLaw_relative_error P).and
      ((Real.tendsto_log_atTop.eventually (boundary_scalar_eventually P J)).and
        (Real.tendsto_log_atTop.eventually_ge_atTop 1))))
  refine ⟨x₀, fun x hx S B _ _ _ _ 𝔊 Bc => ?_⟩
  obtain ⟨htilt, hrel, hscal, hL1⟩ := hx₀ x hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hL1
  classical
  show wNormSq (memWeight 𝔊.toGroupFamily P.q (Graph.sourceMemoryLength (Real.log x)))
    (emptyVec 𝔊.toGroupFamily J P.ℓ Bc) ≤ 2
  rw [boundary_wNormSq_eq, boundary_sum_bigListMass]
  -- the small part
  have hsmall := boundary_smallPart_le_one 𝔊.toGroupFamily
    (fun g p hp => (𝔊.prime_small g p hp).pos) 𝔊.disjoint_small
    (fun g => PrimeGroups.mass_pos_of_ge (𝔊.mass_small_ge g)) J P.ℓ
  -- the big part
  have hPst : 0 < Graph.sourcePrimeLowerBound P.c (Real.log x) :=
    Graph.source_prime_lower_bound_pos _ _
  have hsum0 : ∀ g : B, 0 ≤ ∑ p ∈ 𝔊.big g,
      tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p :=
    fun g => Finset.sum_nonneg fun p hp => (htilt S B 𝔊 g p hp).2.1.le
  have hsumle : ∀ g : B, ∑ p ∈ 𝔊.big g,
      tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p ≤
        1 + 4 * (Graph.sourceMemoryLength (Real.log x) : ℝ) /
          Graph.sourcePrimeLowerBound P.c (Real.log x) := by
    intro g
    calc ∑ p ∈ 𝔊.big g, tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p
        ≤ ∑ p ∈ 𝔊.big g, (1 + 4 * (Graph.sourceMemoryLength (Real.log x) : ℝ) /
            Graph.sourcePrimeLowerBound P.c (Real.log x)) *
              Graph.primeGroupLaw (𝔊.big g) p := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hlaw := 𝔊.big_law_pos g p hp
          have h1 := (abs_le.mp (hrel S B 𝔊 g p hp)).2
          exact (div_le_iff₀ hlaw).mp (by linarith)
      _ = 1 + 4 * (Graph.sourceMemoryLength (Real.log x) : ℝ) /
            Graph.sourcePrimeLowerBound P.c (Real.log x) := by
          rw [← Finset.mul_sum, 𝔊.big_law_sum g, mul_one]
  have hb0 : 0 ≤ ((J + P.ℓ : ℕ) : ℝ) * (4 * (Graph.sourceMemoryLength (Real.log x) : ℝ) /
      Graph.sourcePrimeLowerBound P.c (Real.log x)) :=
    mul_nonneg (Nat.cast_nonneg _)
      (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hPst.le)
  have hF : ∀ g : B, (∑ p ∈ 𝔊.big g,
      tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p) ^ (J + P.ℓ) ≤
        Real.exp (((J + P.ℓ : ℕ) : ℝ) * (4 * (Graph.sourceMemoryLength (Real.log x) : ℝ) /
          Graph.sourcePrimeLowerBound P.c (Real.log x))) := by
    intro g
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (hsum0 g) ((hsumle g).trans (by
      linarith [Real.add_one_le_exp (4 * (Graph.sourceMemoryLength (Real.log x) : ℝ) /
        Graph.sourcePrimeLowerBound P.c (Real.log x))])) _
  have hprod := 𝔊.prod_big_le_rpow hL0
    (fun g => (∑ p ∈ 𝔊.big g,
      tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p) ^ (J + P.ℓ))
    _ hb0 (fun g => pow_nonneg (hsum0 g) _) hF
  have hbig : ∏ g, (∑ p ∈ 𝔊.big g,
      tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p) ^ (J + P.ℓ) ≤ 2 := by
    refine hprod.trans ?_
    rw [Real.rpow_def_of_pos hL0]
    calc Real.exp (Real.log (Real.log x) * (((J + P.ℓ : ℕ) : ℝ) *
          (4 * (Graph.sourceMemoryLength (Real.log x) : ℝ) /
            Graph.sourcePrimeLowerBound P.c (Real.log x)) * P.C₀))
        ≤ Real.exp (Real.log 2) := Real.exp_le_exp.mpr hscal
      _ = 2 := Real.exp_log two_pos
  have hbig0 : 0 ≤ ∏ g, (∑ p ∈ 𝔊.big g,
      tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p) ^ (J + P.ℓ) :=
    Finset.prod_nonneg fun g _ => pow_nonneg (hsum0 g) _
  calc _ ≤ (1 : ℝ) * 2 := mul_le_mul hsmall hbig hbig0 zero_le_one
    _ = 2 := one_mul 2

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
