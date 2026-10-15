module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.HighRank.PinnedBound
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.GhostAbsoluteProof
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.MemoryAbsoluteProof
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Large rank: proof of `HighRank`, (eq:high-rank-path-bound)

Source: `verification/stage7-sources/S-02.tex`, lines 1107–1155 (`[S-02:1107–1155]`).

"Thus the total absolute contribution for this fixed collection is at most
`L^{C_h(N+1)} (C/P_*)^{r(π)}`, for fixed `C_h, C`; both may depend on `m, C₁`."

`highRank : HighRank`, with

* `C = 4 / v₋`: every block `b` of `π` contributes `μ̃_g(𝒫_g) · (sup μ̃)^{|b| - 1}` with
  `μ̃_g(𝒫_g) ≤ 2` (`eventually_tiltLaw_sum_le`) and `sup μ̃ ≤ 2/(v₋ P_*)`
  (`eventually_tiltLaw_le`, (eq:tilted-point-mass)), and `|b| - 1 ≥ 1`;
* `C_h = |(J + ℓ) C₀ log 2| + |C_v| + |C_a|` (`hrExponent`), where `C_v` is the exponent of
  (eq:ghost-absolute-bound) and `C_a = memAbsExponent P m C₁` the exponent of Lemma 3.8: the
  unconstrained iteration of the row bounds costs `K₀ R_g^{N+1} R_e^N` with
  `K₀ ≤ 2^{M|ℬ|} ≤ L^{(J+ℓ) C₀ log 2}`, `R_g ≤ L^{C_v}`, `R_e ≤ L^{C_a}`. It depends on `J` through
  the initial boundary mass only;
* a threshold `x₀` depending on `P` only (`b_p > 0`, `μ̃_g ≤ 2 μ_g`, `log x ≥ 1`).

The bound is uniform in the prime groups, the admissible pattern family, `k`, `ζ`, `θ` and the
collection `π`; the constant `C₂` of the bound on `k` is not used.

## The argument (see `Blocks.lean`, `Pins.lean`, `EdgePinned.lean`, `GhostPinned.lean`,
`PinnedPath.lean`, `PinnedBound.lean`)

1. `1_{𝒞_π} ≤ ∑_ζ ∏_{b ∈ π} ∏_{a ∈ b} 1[birth a = ζ_b]`: the common value of each block is summed
   first (`hr_block_sum_le`).
2. For a fixed assignment of values to addresses, the absolute path sum is bounded by backward
   induction with the row bounds of the operations with pinned births (`hr_pinnedPath_le`,
   `hr_pinned_le`): each pinned address gives the point mass of its tilted law
   (`hr_edge_row_pinned`, `hr_ghost_row_pinned`, `hr_init_le`).
3. `∑_z ∏_{a ∈ b} μ̃_{g(a)}(z) ≤ μ̃(𝒫) (sup μ̃)^{|b| - 1}` (`hr_sum_block_le`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

open Filter

noncomputable section

/-! ### Constants -/

/-- The exponent of the initial boundary mass with prescribed values: `K₀ ≤ 2^{M|ℬ|}` and
`|ℬ| ≤ C₀ T`, so `K₀ ≤ L^{(J + ℓ) log 2 · C₀}`. -/
def hrInitExponent (P : GroupParams) (J : ℕ) : ℝ := ((J + P.ℓ : ℕ) : ℝ) * Real.log 2 * P.C₀

/-- The exponent `C_v` of the row bound of the absolute visit operations (the one of
`ghostAbsolute`). -/
def hrGhostExponent (P : GroupParams) : ℝ := 2 * max 1 P.vPlus / memRho P * memV P * 2 * P.C₀

/-- **The exponent `C_h` of (eq:high-rank-path-bound)**:
`|(J + ℓ) C₀ log 2| + |C_v| + |C_a|`, `C_a = memAbsExponent P m C₁`. -/
def hrExponent (P : GroupParams) (m : ℕ) (C₁ : ℝ) (J : ℕ) : ℝ :=
  |hrInitExponent P J| + |hrGhostExponent P| + |memAbsExponent P m C₁|

/-- The scalar estimate `L^{C_K} (L^{C_v})^{N+1} (L^{C_a})^N ≤ L^{(|C_K| + |C_v| + |C_a|)(N+1)}`
for `L ≥ 1`. -/
theorem hr_scalar_le {L CK Cv Ca : ℝ} (hL : 1 ≤ L) (n : ℕ) :
    L ^ CK * ((L ^ Cv) ^ (n + 1) * (L ^ Ca) ^ n) ≤
      L ^ ((|CK| + |Cv| + |Ca|) * ((n : ℝ) + 1)) := by
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have ht : 0 ≤ Real.log L := Real.log_nonneg hL
  have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have eL : ∀ (y : ℝ) (j : ℕ), (L ^ y) ^ j = Real.exp ((j : ℝ) * (Real.log L * y)) :=
    fun y j => by rw [Real.exp_nat_mul, ← Real.rpow_def_of_pos hL0]
  have h1 : Real.log L * CK ≤ Real.log L * (|CK| * ((n : ℝ) + 1)) :=
    mul_le_mul_of_nonneg_left
      ((le_abs_self CK).trans (le_mul_of_one_le_right (abs_nonneg CK) hn1)) ht
  have h2 : ((n : ℝ) + 1) * (Real.log L * Cv) ≤ Real.log L * (|Cv| * ((n : ℝ) + 1)) := by
    have e : ((n : ℝ) + 1) * (Real.log L * Cv) = Real.log L * (Cv * ((n : ℝ) + 1)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (le_abs_self Cv) (zero_le_one.trans hn1)) ht
  have h3 : (n : ℝ) * (Real.log L * Ca) ≤ Real.log L * (|Ca| * ((n : ℝ) + 1)) := by
    have e : (n : ℝ) * (Real.log L * Ca) = Real.log L * (Ca * (n : ℝ)) := by ring
    rw [e]
    refine mul_le_mul_of_nonneg_left ?_ ht
    calc Ca * (n : ℝ) ≤ |Ca| * (n : ℝ) := mul_le_mul_of_nonneg_right (le_abs_self Ca) hn
      _ ≤ |Ca| * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg Ca)
  have e : Real.log L * ((|CK| + |Cv| + |Ca|) * ((n : ℝ) + 1)) =
      Real.log L * (|CK| * ((n : ℝ) + 1)) + Real.log L * (|Cv| * ((n : ℝ) + 1)) +
        Real.log L * (|Ca| * ((n : ℝ) + 1)) := by ring
  rw [eL Cv (n + 1), eL Ca n, Real.rpow_def_of_pos hL0, Real.rpow_def_of_pos hL0,
    ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp, e]
  push_cast
  linarith

/-! ### The large-rank estimate -/

/-- **(eq:high-rank-path-bound) for fixed constants** [S-02:1107–1155], with
`C_h = hrExponent P m C₁ J`, `C = 4/v₋` and a threshold depending on `P` only. -/
theorem highRankBound (P : GroupParams) (m : ℕ) (C₁ : ℝ) (J : ℕ) (C₂ : ℝ) :
    HighRankBound P m C₁ J C₂ (hrExponent P m C₁ J) (4 / P.vMinus) := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp ((eventually_big_tilt P one_pos).and
    ((eventually_tiltLaw_sum_le P).and ((eventually_tiltLaw_le P).and
      (Real.tendsto_log_atTop.eventually_ge_atTop 1))))
  refine ⟨x₀, fun x hx S B _ _ _ _ 𝔊 N _ 𝔉 ζ k hadm θ π hπ => ?_⟩
  obtain ⟨htilt, hsum, hpt, hL1⟩ := hx₀ x hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hL1
  have hρ0 := memRho_pos P
  have hρ1 := memRho_lt_one P
  have hv1 : 1 ≤ memV P := (one_lt_memV P).le
  have hv0 : 0 < memV P := lt_of_lt_of_le zero_lt_one hv1
  have hT : 0 < P.ℓ + m := Nat.add_pos_left P.ℓ_pos m
  have hℓT : P.ℓ ≤ P.ℓ + m := Nat.le_add_right P.ℓ m
  have hC : ∀ ν g, P.ℓ + ((𝔉 ν).C g).card ≤ P.ℓ + m := fun ν g =>
    Nat.add_le_add_left (hadm.1 ν g) P.ℓ
  have hPpos : 0 < Graph.sourcePrimeLowerBound P.c (Real.log x) :=
    Graph.source_prime_lower_bound_pos _ _
  -- the tilted laws
  have hν : ∀ g, ∀ p ∈ 𝔊.big g,
      0 ≤ tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p :=
    fun g p hp => (htilt S B 𝔊 g p hp).2.1.le
  have hM : ∀ g : B, ∑ p ∈ 𝔊.big g,
      tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p ≤ 2 :=
    fun g => hsum S B 𝔊 g
  have hμ : ∀ g, ∀ p ∈ 𝔊.big g,
      tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p ≤
        2 / (P.vMinus * Graph.sourcePrimeLowerBound P.c (Real.log x)) :=
    fun g p hp => hpt S B 𝔊 g p hp
  have hμ0 : 0 ≤ 2 / (P.vMinus * Graph.sourcePrimeLowerBound P.c (Real.log x)) :=
    div_nonneg zero_le_two (mul_pos P.vMinus_pos hPpos).le
  have h1 : ∀ g : B, 1 ≤ ∑ p ∈ 𝔊.big g,
      tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p := fun g =>
    hr_one_le_tilt_sum (𝔊.big g) P.q _ (PrimeGroups.mass_pos_of_ge (𝔊.mass_big_ge g))
      (fun p hp => (𝔊.prime_big g p hp).pos) (𝔊.big_law_sum g)
      (fun p hp => (htilt S B 𝔊 g p hp).1)
      (fun p _ => lifeBaseline_le_one P.q_pos P.q_lt_one _ p)
  -- the constants of (eq:memory-weight-choice) at every visit
  have hspec := fun (i : ℕ) (V : ℝ) (hV0 : 0 ≤ V) (hV : V ≤ P.vPlus) =>
    (memV_spec P).2 (visitQ P.q (Graph.sourceMemoryLength (Real.log x)) i) V 2
      (visitQ_eq _ _ _) hV0 hV (by norm_num) le_rfl
  -- the bound for a general family
  have hmain := hr_absRankPart_le (memData 𝔊 𝔉 k ζ) (memCutoff (Real.log x)) θ
    (v := memV P) (vMinus := P.vMinus) (Mmax := 2) (cmax := 2 * max 1 P.vPlus / memRho P)
    (μmax := 2 / (P.vMinus * Graph.sourcePrimeLowerBound P.c (Real.log x))) (T := P.ℓ + m)
    P.q_pos P.q_lt_one hρ0 hρ1 hv1 P.vMinus_pos 𝔊.mass_small_ge 𝔊.mass_big_ge
    (fun g p hp => (𝔊.prime_small g p hp).pos) 𝔊.disjoint_small 𝔊.big_law_sum hν h1 hM hμ hμ0
    hT hℓT hC
    (fun i _ => (hspec i 0 le_rfl P.vPlus_pos.le).1)
    (fun i _ => (hspec i 0 le_rfl P.vPlus_pos.le).2.1.le)
    (fun i _ g => (hspec i (Graph.primeGroupReciprocalMass (𝔊.big g))
      (PrimeGroups.mass_pos_of_ge (𝔊.mass_big_ge g)).le (𝔊.mass_big_le g)).2.2.2.2)
    hπ
  -- the initial boundary mass is a power of `L`
  have hmx0 : (0 : ℝ) ≤ max (1 : ℝ) 2 := zero_le_one.trans (le_max_left _ _)
  have hK₀ : ∏ _g : B, (max (1 : ℝ) 2) ^ (J + P.ℓ) ≤ Real.log x ^ hrInitExponent P J := by
    have hb : (0 : ℝ) ≤ ((J + P.ℓ : ℕ) : ℝ) * Real.log 2 :=
      mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg one_le_two)
    have hF : (max (1 : ℝ) 2) ^ (J + P.ℓ) ≤ Real.exp (((J + P.ℓ : ℕ) : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log two_pos, max_eq_right one_le_two]
    exact 𝔊.prod_big_le_rpow hL0 (fun _ => (max (1 : ℝ) 2) ^ (J + P.ℓ)) _ hb
      (fun _ => pow_nonneg hmx0 _) (fun _ => hF)
  -- the row constant of the visit operations is a power of `L`
  have hb0 : 0 ≤ 2 * max 1 P.vPlus / memRho P * memV P * 2 :=
    mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg zero_le_two
      (zero_le_one.trans (le_max_left _ _))) hρ0.le) hv0.le) zero_le_two
  have hRg0 : 0 ≤ ∏ _g : B, Real.exp (2 * max 1 P.vPlus / memRho P * memV P * 2) :=
    Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le
  have hRg : ∏ _g : B, Real.exp (2 * max 1 P.vPlus / memRho P * memV P * 2) ≤
      Real.log x ^ hrGhostExponent P :=
    𝔊.prod_big_le_rpow hL0 (fun _ => Real.exp (2 * max 1 P.vPlus / memRho P * memV P * 2))
      _ hb0 (fun _ => (Real.exp_pos _).le) (fun _ => le_rfl)
  -- the row constant of the edges is a power of `L` (as in `memoryAbsoluteBound`)
  have hG1 : 1 ≤ Schur.groupConst P.vMinus P.q (P.ℓ + m) := Schur.one_le_groupConst _ _ _
  have hGpos : 0 < Schur.groupConst P.vMinus P.q (P.ℓ + m) := lt_of_lt_of_le zero_lt_one hG1
  have hK1 : 1 ≤ memAbsBigConst P m := le_max_left _ _
  have hKpos : 0 < memAbsBigConst P m := lt_of_lt_of_le zero_lt_one hK1
  have hrowC0 : 0 ≤ edgeAbsRowConst P.vMinus (memRho P) (memV P) (P.ℓ + m) := by
    unfold edgeAbsRowConst
    exact mul_nonneg (pow_nonneg (mul_nonneg zero_le_two hv0.le) _)
      (mul_nonneg (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
        (l38_countSup_nonneg _ hρ0 hρ1))
  have hRb0 : 0 ≤ edgeAbsRowConst P.vMinus (memRho P) (memV P) (P.ℓ + m) *
      (max (1 : ℝ) 2) ^ (P.ℓ + m) := mul_nonneg hrowC0 (pow_nonneg hmx0 _)
  have hRbK : edgeAbsRowConst P.vMinus (memRho P) (memV P) (P.ℓ + m) *
      (max (1 : ℝ) 2) ^ (P.ℓ + m) ≤ memAbsBigConst P m :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hprodS : ∏ _g : S, Schur.groupConst P.vMinus P.q (P.ℓ + m) ≤
      Real.log x ^ (Real.log (Schur.groupConst P.vMinus P.q (P.ℓ + m)) * P.C₀) :=
    𝔊.prod_small_le_rpow hL0 (fun _ => Schur.groupConst P.vMinus P.q (P.ℓ + m))
      (Real.log (Schur.groupConst P.vMinus P.q (P.ℓ + m))) (Real.log_nonneg hG1)
      (fun _ => hGpos.le) (fun _ => (Real.exp_log hGpos).ge)
  have hprodRow : (∏ _g : B, edgeAbsRowConst P.vMinus (memRho P) (memV P) (P.ℓ + m)) *
        ∏ _g : B, (max (1 : ℝ) 2) ^ (P.ℓ + m) ≤
      Real.log x ^ (Real.log (memAbsBigConst P m) * P.C₀) := by
    rw [← Finset.prod_mul_distrib]
    exact 𝔊.prod_big_le_rpow hL0
      (fun _ => edgeAbsRowConst P.vMinus (memRho P) (memV P) (P.ℓ + m) *
        (max (1 : ℝ) 2) ^ (P.ℓ + m))
      (Real.log (memAbsBigConst P m)) (Real.log_nonneg hK1) (fun _ => hRb0)
      (fun _ => hRbK.trans (Real.exp_log hKpos).ge)
  have hPS0 : 0 ≤ ∏ _g : S, Schur.groupConst P.vMinus P.q (P.ℓ + m) :=
    Finset.prod_nonneg fun _ _ => hGpos.le
  have hPR0 : 0 ≤ (∏ _g : B, edgeAbsRowConst P.vMinus (memRho P) (memV P) (P.ℓ + m)) *
      ∏ _g : B, (max (1 : ℝ) 2) ^ (P.ℓ + m) :=
    mul_nonneg (Finset.prod_nonneg fun _ _ => hrowC0)
      (Finset.prod_nonneg fun _ _ => pow_nonneg hmx0 _)
  have hRe0 : 0 ≤ patternMass 𝔉 *
      ((∏ _g : S, Schur.groupConst P.vMinus P.q (P.ℓ + m)) *
        (∏ _g : B, edgeAbsRowConst P.vMinus (memRho P) (memV P) (P.ℓ + m)) *
        ∏ _g : B, (max (1 : ℝ) 2) ^ (P.ℓ + m)) := by
    rw [mul_assoc (∏ _g : S, Schur.groupConst P.vMinus P.q (P.ℓ + m))]
    exact mul_nonneg (patternMass_nonneg 𝔉) (mul_nonneg hPS0 hPR0)
  have hRe : patternMass 𝔉 *
        ((∏ _g : S, Schur.groupConst P.vMinus P.q (P.ℓ + m)) *
          (∏ _g : B, edgeAbsRowConst P.vMinus (memRho P) (memV P) (P.ℓ + m)) *
          ∏ _g : B, (max (1 : ℝ) 2) ^ (P.ℓ + m)) ≤
      Real.log x ^ memAbsExponent P m C₁ := by
    unfold memAbsExponent
    rw [Real.rpow_add hL0, Real.rpow_add hL0,
      mul_assoc (∏ _g : S, Schur.groupConst P.vMinus P.q (P.ℓ + m))]
    exact mul_le_mul hadm.2.1
      (mul_le_mul hprodS hprodRow hPR0 (Real.rpow_nonneg hL0.le _))
      (mul_nonneg hPS0 hPR0) (Real.rpow_nonneg hL0.le _)
  -- the constant of the path sum
  have hconst : hrPathConst (memData 𝔊 𝔉 k ζ) (memV P) P.vMinus 2
        (2 * max 1 P.vPlus / memRho P) (P.ℓ + m) ≤
      Real.log x ^ (hrExponent P m C₁ J *
        ((Graph.sourceMemoryLength (Real.log x) : ℝ) + 1)) := by
    have h2 : hrPathConst (memData 𝔊 𝔉 k ζ) (memV P) P.vMinus 2
          (2 * max 1 P.vPlus / memRho P) (P.ℓ + m) ≤
        Real.log x ^ hrInitExponent P J *
          ((Real.log x ^ hrGhostExponent P) ^ (Graph.sourceMemoryLength (Real.log x) + 1) *
            (Real.log x ^ memAbsExponent P m C₁) ^ Graph.sourceMemoryLength (Real.log x)) :=
      mul_le_mul hK₀
        (mul_le_mul (pow_le_pow_left₀ hRg0 hRg _) (pow_le_pow_left₀ hRe0 hRe _)
          (pow_nonneg hRe0 _) (pow_nonneg (Real.rpow_nonneg hL0.le _) _))
        (mul_nonneg (pow_nonneg hRg0 _) (pow_nonneg hRe0 _)) (Real.rpow_nonneg hL0.le _)
    exact h2.trans (hr_scalar_le hL1 _)
  -- the saving of one dependent birth
  have hsave : max (1 : ℝ) 2 * (2 / (P.vMinus * Graph.sourcePrimeLowerBound P.c (Real.log x))) =
      4 / P.vMinus / Graph.sourcePrimeLowerBound P.c (Real.log x) := by
    rw [max_eq_right one_le_two, div_div]
    ring
  have hsave0 : 0 ≤ 4 / P.vMinus / Graph.sourcePrimeLowerBound P.c (Real.log x) :=
    div_nonneg (div_nonneg (by norm_num) P.vMinus_pos.le) hPpos.le
  rw [hsave] at hmain
  exact hmain.trans (mul_le_mul_of_nonneg_right hconst (pow_nonneg hsave0 _))

/-- **Large rank: (eq:high-rank-path-bound)** [S-02:1107–1155], proved: for all sufficiently
large `x` and every collection `π` of blocks of birth addresses (at the truncation `B = ⌈L²⌉`),
the total absolute contribution of the histories satisfying `𝒞_π` is at most
`L^{C_h (N+1)} (C/P_*)^{r(π)}`, with `C_h = hrExponent P m C₁ J` and `C = 4/v₋`, uniformly in the
prime groups, the admissible pattern family, `k`, `ζ`, `θ` and `π`. -/
theorem highRank : HighRank :=
  fun P m C₁ J C₂ => ⟨hrExponent P m C₁ J, 4 / P.vMinus, div_pos (by norm_num) P.vMinus_pos,
    highRankBound P m C₁ J C₂⟩

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
