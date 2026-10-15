module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.DyadicMass
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.SquareExceptionsProof

/-!
# The candidate groups are admissible active groups

`candidateAdmissible : MertensReciprocal → CandidateAdmissible` (`[P-07:0319–0329, 0533–0535]`):
"there are between positive constant multiples of `log L` groups of each kind; they are disjoint,
their reciprocal sums `V_g` are bounded above and below by positive constants, and they lie in the
allowed small and big ranges of Theorem 6.1; the big groups are full prime intervals; all candidate
primes exceed `W`", and "every active set `P` has between fixed positive multiples of `log L`
groups of each kind and satisfies all the active-group hypotheses".

The groups of `restrictGroups (candidateGroups x) P` are bands
`candidateBand lo x k = {p : exp(2^k L^lo) ≤ p < exp(2^{k+1} L^lo)}` with
`k < candidateCount lo hi x`, `(lo, hi) = (0.28, 0.35)` or `(0.4, 0.45)`
(`restrict_candidate_group`).

* `two_pow_mul_rpow_le`: `2^{k+1} L^lo ≤ L^hi` for `k < candidateCount lo hi x`, so the band lies
  in `[exp(L^lo), exp(L^hi))` (`candidateBand_range`);
* `candidateBand_disjoint`, `candidateBand_small_big_disjoint`: distinct bands are disjoint;
* `candidateBand_mass`: `|V_g - log 2| ≤ δ` from the dyadic band mass (`DyadicPrimeMass`, a
  consequence of Mertens' estimate) at `y = 2^k L^lo ≥ L^{0.28}`;
* `candidateCount_le`: at most `(log L) / log 2` groups of each kind.

The constants are `c₀ = c₂`, `C₀ = 1 / log 2`, `v₋ = (log 2)/2`, `v₊ = 2 log 2`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

open Filter
open scoped Topology

noncomputable section

/-! ### The bands -/

/-- `2^{k+1} L^lo ≤ L^hi` for `k < candidateCount lo hi x`: the doubling stops while
`2y ≤ L^hi`. -/
theorem two_pow_mul_rpow_le {lo hi x : ℝ} (hlh : lo ≤ hi) (hL : 1 ≤ Real.log x) {k : ℕ}
    (hk : k < candidateCount lo hi x) :
    (2 : ℝ) ^ (k + 1) * Real.log x ^ lo ≤ Real.log x ^ hi := by
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL
  have hLL : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnn : 0 ≤ (hi - lo) * Real.log (Real.log x) / Real.log 2 :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hlh) hLL) hlog2.le
  have hk' : k + 1 ≤ ⌊(hi - lo) * Real.log (Real.log x) / Real.log 2⌋₊ := hk
  have h1 : ((k + 1 : ℕ) : ℝ) ≤ (hi - lo) * Real.log (Real.log x) / Real.log 2 :=
    (Nat.cast_le.mpr hk').trans (Nat.floor_le hnn)
  have h2 : ((k + 1 : ℕ) : ℝ) * Real.log 2 ≤ (hi - lo) * Real.log (Real.log x) :=
    (le_div_iff₀ hlog2).mp h1
  have e1 : (2 : ℝ) ^ (k + 1) = Real.exp (((k + 1 : ℕ) : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have e2 : Real.log x ^ (hi - lo) = Real.exp ((hi - lo) * Real.log (Real.log x)) := by
    rw [Real.rpow_def_of_pos hL0, mul_comm]
  have h3 : (2 : ℝ) ^ (k + 1) ≤ Real.log x ^ (hi - lo) := by
    rw [e1, e2]
    exact Real.exp_le_exp.mpr h2
  calc (2 : ℝ) ^ (k + 1) * Real.log x ^ lo ≤ Real.log x ^ (hi - lo) * Real.log x ^ lo :=
        mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hL0.le _)
    _ = Real.log x ^ hi := by rw [← Real.rpow_add hL0, sub_add_cancel]

/-- A prime of the `k`-th band, `k < candidateCount lo hi x`, lies in
`[exp(L^lo), exp(L^hi))`. -/
theorem candidateBand_range {lo hi x : ℝ} (hlh : lo ≤ hi) (hL : 1 ≤ Real.log x) {k : ℕ}
    (hk : k < candidateCount lo hi x) {p : ℕ} (hp : p ∈ candidateBand lo x k) :
    Real.exp (Real.log x ^ lo) ≤ (p : ℝ) ∧ (p : ℝ) < Real.exp (Real.log x ^ hi) := by
  obtain ⟨-, h1, h2⟩ := mem_candidateBand.mp hp
  have hL0 : 0 ≤ Real.log x := by linarith
  have hlo : 0 ≤ Real.log x ^ lo := Real.rpow_nonneg hL0 _
  constructor
  · refine le_trans (Real.exp_le_exp.mpr ?_) h1
    exact le_mul_of_one_le_left hlo (one_le_pow₀ (by norm_num))
  · exact lt_of_lt_of_le h2 (Real.exp_le_exp.mpr (two_pow_mul_rpow_le hlh hL hk))

/-- Two bands of the same sequence with different indices are disjoint. -/
theorem candidateBand_disjoint {lo x : ℝ} (hL : 0 ≤ Real.log x) {k k' : ℕ} (hkk : k ≠ k') :
    Disjoint (candidateBand lo x k) (candidateBand lo x k') := by
  have key : ∀ a b : ℕ, a < b → Disjoint (candidateBand lo x a) (candidateBand lo x b) := by
    intro a b hab
    rw [Finset.disjoint_left]
    intro p hpa hpb
    obtain ⟨-, -, h2⟩ := mem_candidateBand.mp hpa
    obtain ⟨-, h1, -⟩ := mem_candidateBand.mp hpb
    have hpow : (2 : ℝ) ^ (a + 1) ≤ 2 ^ b :=
      pow_le_pow_right₀ (by norm_num) (Nat.succ_le_of_lt hab)
    have hle : (2 : ℝ) ^ (a + 1) * Real.log x ^ lo ≤ 2 ^ b * Real.log x ^ lo :=
      mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hL _)
    have hexp := Real.exp_le_exp.mpr hle
    linarith
  rcases Nat.lt_or_gt_of_ne hkk with h | h
  · exact key k k' h
  · exact (key k' k h).symm

/-- A small band and a big band are disjoint: the small bands end below `exp(L^{0.35})`, the big
bands start at `exp(L^{0.4})`. -/
theorem candidateBand_small_big_disjoint {x : ℝ} (hL : 1 ≤ Real.log x) {k : ℕ}
    (hk : k < candidateCount 0.28 0.35 x) (k' : ℕ) :
    Disjoint (candidateBand 0.28 x k) (candidateBand 0.4 x k') := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  have h1 := (candidateBand_range (by norm_num) hL hk hp).2
  have h2 := (mem_candidateBand.mp hp').2.1
  have hL0 : 0 ≤ Real.log x := by linarith
  have h3 : Real.log x ^ (0.35 : ℝ) ≤ 2 ^ k' * Real.log x ^ (0.4 : ℝ) :=
    (Real.rpow_le_rpow_of_exponent_le hL (by norm_num)).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg hL0 _) (one_le_pow₀ (by norm_num)))
  have h4 := Real.exp_le_exp.mpr h3
  linarith

/-- The mass of a band is within `δ` of `log 2` once `L^lo` is beyond the threshold of the dyadic
band mass. -/
theorem candidateBand_mass {δ Y₀ : ℝ}
    (hY : ∀ y : ℝ, Y₀ ≤ y → ∀ T : Finset ℕ,
      (∀ p ∈ T, p.Prime ∧ Real.exp y ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (2 * y)) →
      (∀ p : ℕ, p.Prime → Real.exp y < (p : ℝ) → (p : ℝ) < Real.exp (2 * y) → p ∈ T) →
        |reciprocalMass T - Real.log 2| ≤ δ)
    {lo x : ℝ} (hL : 0 ≤ Real.log x) (hlo : Y₀ ≤ Real.log x ^ lo) (k : ℕ) :
    |reciprocalMass (candidateBand lo x k) - Real.log 2| ≤ δ := by
  have h0 : 0 ≤ Real.log x ^ lo := Real.rpow_nonneg hL _
  have hy : Y₀ ≤ 2 ^ k * Real.log x ^ lo :=
    hlo.trans (le_mul_of_one_le_left h0 (one_le_pow₀ (by norm_num)))
  have e : 2 * (2 ^ k * Real.log x ^ lo) = 2 ^ (k + 1) * Real.log x ^ lo := by ring
  refine hY _ hy _ (fun p hp => ?_) (fun p hpp h1 h2 => ?_)
  · obtain ⟨hpp, h1, h2⟩ := mem_candidateBand.mp hp
    rw [e]
    exact ⟨hpp, h1, h2.le⟩
  · rw [e] at h2
    exact mem_candidateBand.mpr ⟨hpp, h1.le, h2⟩

/-- There are at most `(log L)/log 2` bands when `hi - lo ≤ 1`. -/
theorem candidateCount_le {lo hi x : ℝ} (hlh : lo ≤ hi) (hh : hi - lo ≤ 1)
    (hL : 1 ≤ Real.log x) :
    (candidateCount lo hi x : ℝ) ≤ 1 / Real.log 2 * Real.log (Real.log x) := by
  have hLL : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnn : 0 ≤ (hi - lo) * Real.log (Real.log x) / Real.log 2 :=
    div_nonneg (mul_nonneg (sub_nonneg.mpr hlh) hLL) hlog2.le
  have h1 : (candidateCount lo hi x : ℝ) ≤ (hi - lo) * Real.log (Real.log x) / Real.log 2 := by
    unfold candidateCount
    exact Nat.floor_le hnn
  calc (candidateCount lo hi x : ℝ) ≤ (hi - lo) * Real.log (Real.log x) / Real.log 2 := h1
    _ ≤ 1 * Real.log (Real.log x) / Real.log 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hh hLL) hlog2.le
    _ = 1 / Real.log 2 * Real.log (Real.log x) := by ring

/-! ### The groups of an active set -/

/-- Every group of a sub-system of the candidate groups is a band, small or big. -/
theorem restrict_candidate_group (x : ℝ) (P : Finset (candidateGroups x).Index)
    (g : (restrictGroups (candidateGroups x) P).Index) :
    (∃ k : ℕ, k < candidateCount 0.28 0.35 x ∧
        (restrictGroups (candidateGroups x) P).group g = candidateBand 0.28 x k) ∨
      ∃ k : ℕ, k < candidateCount 0.4 0.45 x ∧
        (restrictGroups (candidateGroups x) P).group g = candidateBand 0.4 x k := by
  rcases g with i | i
  · exact Or.inl
      ⟨(P.toLeft.orderEmbOfFin rfl i).val, (P.toLeft.orderEmbOfFin rfl i).isLt, rfl⟩
  · exact Or.inr
      ⟨(P.toRight.orderEmbOfFin rfl i).val, (P.toRight.orderEmbOfFin rfl i).isLt, rfl⟩

/-- **An active set of candidate groups is an admissible system of active groups**, for
constants `Pc` compatible with the band masses and the number of bands, at every `x` with `L ≥ 1`
and `L^{0.28}` beyond the threshold of the dyadic band mass. -/
theorem restrictGroups_candidate_admissible (Pc : ActiveGroupConstants) {δ Y₀ : ℝ}
    (hY : ∀ y : ℝ, Y₀ ≤ y → ∀ T : Finset ℕ,
      (∀ p ∈ T, p.Prime ∧ Real.exp y ≤ (p : ℝ) ∧ (p : ℝ) ≤ Real.exp (2 * y)) →
      (∀ p : ℕ, p.Prime → Real.exp y < (p : ℝ) → (p : ℝ) < Real.exp (2 * y) → p ∈ T) →
        |reciprocalMass T - Real.log 2| ≤ δ)
    (hvlo : Pc.vlo ≤ Real.log 2 - δ) (hvhi : Real.log 2 + δ ≤ Pc.vhi)
    (hC₀ : 1 / Real.log 2 ≤ Pc.C₀) {x : ℝ} (hL : 1 ≤ Real.log x)
    (hY1 : Y₀ ≤ Real.log x ^ (0.28 : ℝ)) (P : Finset (candidateGroups x).Index)
    (hPl : Pc.c₀ * Real.log (Real.log x) ≤ (P.toLeft.card : ℝ))
    (hPr : Pc.c₀ * Real.log (Real.log x) ≤ (P.toRight.card : ℝ)) :
    (restrictGroups (candidateGroups x) P).Admissible Pc x := by
  have hL0 : 0 ≤ Real.log x := by linarith
  have hLL : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL
  have hY2 : Y₀ ≤ Real.log x ^ (0.4 : ℝ) :=
    hY1.trans (Real.rpow_le_rpow_of_exponent_le hL (by norm_num))
  have hmass : ∀ g : (restrictGroups (candidateGroups x) P).Index,
      |reciprocalMass ((restrictGroups (candidateGroups x) P).group g) - Real.log 2| ≤ δ := by
    intro g
    rcases restrict_candidate_group x P g with ⟨k, -, hk⟩ | ⟨k, -, hk⟩
    · rw [hk]
      exact candidateBand_mass hY hL0 hY1 k
    · rw [hk]
      exact candidateBand_mass hY hL0 hY2 k
  have hcardL : P.toLeft.card ≤ candidateCount 0.28 0.35 x := by
    have h := Finset.card_le_univ P.toLeft
    rw [Fintype.card_fin] at h
    exact h
  have hcardR : P.toRight.card ≤ candidateCount 0.4 0.45 x := by
    have h := Finset.card_le_univ P.toRight
    rw [Fintype.card_fin] at h
    exact h
  have hcL : (P.toLeft.card : ℝ) ≤ Pc.C₀ * Real.log (Real.log x) :=
    calc (P.toLeft.card : ℝ) ≤ (candidateCount 0.28 0.35 x : ℝ) := Nat.cast_le.mpr hcardL
      _ ≤ 1 / Real.log 2 * Real.log (Real.log x) :=
          candidateCount_le (by norm_num) (by norm_num) hL
      _ ≤ Pc.C₀ * Real.log (Real.log x) := mul_le_mul_of_nonneg_right hC₀ hLL
  have hcR : (P.toRight.card : ℝ) ≤ Pc.C₀ * Real.log (Real.log x) :=
    calc (P.toRight.card : ℝ) ≤ (candidateCount 0.4 0.45 x : ℝ) := Nat.cast_le.mpr hcardR
      _ ≤ 1 / Real.log 2 * Real.log (Real.log x) :=
          candidateCount_le (by norm_num) (by norm_num) hL
      _ ≤ Pc.C₀ * Real.log (Real.log x) := mul_le_mul_of_nonneg_right hC₀ hLL
  refine
    { prime := ?_, disjoint := ?_, numSmall_ge := hPl, numSmall_le := hcL, numBig_ge := hPr,
      numBig_le := hcR, mass_ge := ?_, mass_le := ?_, small_range := ?_, big_range := ?_,
      big_interval := ?_ }
  · -- the groups consist of primes
    intro g p hp
    rcases restrict_candidate_group x P g with ⟨k, -, hk⟩ | ⟨k, -, hk⟩
    · rw [hk] at hp
      exact (mem_candidateBand.mp hp).1
    · rw [hk] at hp
      exact (mem_candidateBand.mp hp).1
  · -- the groups are pairwise disjoint
    intro g g' hgg
    rcases g with i | i <;> rcases g' with i' | i'
    · have hne : (P.toLeft.orderEmbOfFin rfl i).val ≠ (P.toLeft.orderEmbOfFin rfl i').val :=
        fun h => hgg (congrArg Sum.inl ((P.toLeft.orderEmbOfFin rfl).injective (Fin.ext h)))
      show Disjoint (candidateBand 0.28 x (P.toLeft.orderEmbOfFin rfl i).val)
        (candidateBand 0.28 x (P.toLeft.orderEmbOfFin rfl i').val)
      exact candidateBand_disjoint hL0 hne
    · show Disjoint (candidateBand 0.28 x (P.toLeft.orderEmbOfFin rfl i).val)
        (candidateBand 0.4 x (P.toRight.orderEmbOfFin rfl i').val)
      exact candidateBand_small_big_disjoint hL (P.toLeft.orderEmbOfFin rfl i).isLt _
    · show Disjoint (candidateBand 0.4 x (P.toRight.orderEmbOfFin rfl i).val)
        (candidateBand 0.28 x (P.toLeft.orderEmbOfFin rfl i').val)
      exact (candidateBand_small_big_disjoint hL (P.toLeft.orderEmbOfFin rfl i').isLt _).symm
    · have hne : (P.toRight.orderEmbOfFin rfl i).val ≠ (P.toRight.orderEmbOfFin rfl i').val :=
        fun h => hgg (congrArg Sum.inr ((P.toRight.orderEmbOfFin rfl).injective (Fin.ext h)))
      show Disjoint (candidateBand 0.4 x (P.toRight.orderEmbOfFin rfl i).val)
        (candidateBand 0.4 x (P.toRight.orderEmbOfFin rfl i').val)
      exact candidateBand_disjoint hL0 hne
  · -- the masses are at least `v₋`
    intro g
    have h := (abs_le.mp (hmass g)).1
    linarith
  · -- the masses are at most `v₊`
    intro g
    have h := (abs_le.mp (hmass g)).2
    linarith
  · -- the small range
    intro i p hp
    have hk : (P.toLeft.orderEmbOfFin rfl i).val < candidateCount 0.28 0.35 x :=
      (P.toLeft.orderEmbOfFin rfl i).isLt
    have hp' : p ∈ candidateBand 0.28 x (P.toLeft.orderEmbOfFin rfl i).val := hp
    obtain ⟨h1, h2⟩ := candidateBand_range (by norm_num) hL hk hp'
    have h3 : Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ Real.exp (Real.log x ^ (0.28 : ℝ)) :=
      Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hL (by norm_num))
    have h4 : Real.exp (Real.log x ^ (0.35 : ℝ)) ≤ Real.exp (Real.log x ^ (0.36 : ℝ)) :=
      Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hL (by norm_num))
    exact ⟨h3.trans h1, (h2.trans_le h4).le⟩
  · -- the big range
    intro i p hp
    have hk : (P.toRight.orderEmbOfFin rfl i).val < candidateCount 0.4 0.45 x :=
      (P.toRight.orderEmbOfFin rfl i).isLt
    have hp' : p ∈ candidateBand 0.4 x (P.toRight.orderEmbOfFin rfl i).val := hp
    obtain ⟨h1, h2⟩ := candidateBand_range (by norm_num) hL hk hp'
    have h3 : Real.exp (Real.log x ^ (0.39 : ℝ)) ≤ Real.exp (Real.log x ^ (0.4 : ℝ)) :=
      Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hL (by norm_num))
    have h4 : Real.exp (Real.log x ^ (0.45 : ℝ)) ≤ Real.exp (Real.log x ^ (0.46 : ℝ)) :=
      Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hL (by norm_num))
    exact ⟨h3.trans h1, (h2.trans_le h4).le⟩
  · -- the big groups are full prime intervals
    intro j p₁ hp₁ p₂ hp₂ p hp h1 h2
    have hp₁' : p₁ ∈ candidateBand 0.4 x (P.toRight.orderEmbOfFin rfl j).val := hp₁
    have hp₂' : p₂ ∈ candidateBand 0.4 x (P.toRight.orderEmbOfFin rfl j).val := hp₂
    have hmem : p ∈ candidateBand 0.4 x (P.toRight.orderEmbOfFin rfl j).val :=
      mem_candidateBand.mpr ⟨hp, (mem_candidateBand.mp hp₁').2.1.trans (Nat.cast_le.mpr h1),
        lt_of_le_of_lt (Nat.cast_le.mpr h2) (mem_candidateBand.mp hp₂').2.2⟩
    exact hmem

/-! ### The statement -/

/-- The constants of the active sets with at least `c₂ log L` groups of each kind: `c₀ = c₂`,
`C₀ = 1 / log 2`, `v₋ = (log 2)/2`, `v₊ = 2 log 2`. -/
def candidateConstants (c₂ : ℝ) (hc₂ : 0 < c₂) : ActiveGroupConstants where
  c₀ := c₂
  C₀ := 1 / Real.log 2
  vlo := Real.log 2 / 2
  vhi := Real.log 2 * 2
  c₀_pos := hc₂
  C₀_pos := one_div_pos.mpr (Real.log_pos (by norm_num))
  vlo_pos := half_pos (Real.log_pos (by norm_num))
  vhi_pos := mul_pos (Real.log_pos (by norm_num)) two_pos

/-- **The candidate groups and their active sets are admissible** (`[P-07:0319–0329,
0533–0535]`), from Mertens' estimate for `∑ 1/p`. -/
theorem candidateAdmissible (hM : MertensReciprocal) : CandidateAdmissible := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨?_, fun c₂ hc₂ => ?_⟩
  · -- all candidate primes are primes above `W = exp(L^{0.24})`
    filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 1] with x hx p hp
    have hge := candidatePrimes_ge hx.le hp
    refine ⟨?_, ?_⟩
    · obtain ⟨g, -, hg⟩ := Finset.mem_biUnion.mp hp
      rcases g with i | i
      · have hmem : p ∈ candidateBand 0.28 x i.val := hg
        exact (mem_candidateBand.mp hmem).1
      · have hmem : p ∈ candidateBand 0.4 x i.val := hg
        exact (mem_candidateBand.mp hmem).1
    · unfold roughCutoff
      refine lt_of_lt_of_le (Real.exp_lt_exp.mpr ?_) hge
      exact Real.rpow_lt_rpow_of_exponent_lt hx (by norm_num)
  · -- the active sets
    obtain ⟨Y₀, hY⟩ :=
      dyadicPrimeMass_of_mertensReciprocal hM (Real.log 2 / 2) (half_pos hlog2)
    have h1 : ∀ᶠ x : ℝ in atTop, Y₀ ≤ Real.log x ^ (0.28 : ℝ) :=
      ((tendsto_rpow_atTop (show (0 : ℝ) < 0.28 by norm_num)).comp
        Real.tendsto_log_atTop).eventually_ge_atTop Y₀
    refine ⟨candidateConstants c₂ hc₂, ?_⟩
    filter_upwards [h1, Real.tendsto_log_atTop.eventually_ge_atTop 1] with x hY1 hL P hPl hPr
    exact restrictGroups_candidate_admissible (candidateConstants c₂ hc₂) hY
      (show Real.log 2 / 2 ≤ Real.log 2 - Real.log 2 / 2 by linarith)
      (show Real.log 2 + Real.log 2 / 2 ≤ Real.log 2 * 2 by linarith)
      (le_refl (1 / Real.log 2)) hL hY1 P hPl hPr

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
