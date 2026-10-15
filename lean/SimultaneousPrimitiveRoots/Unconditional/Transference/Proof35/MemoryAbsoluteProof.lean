module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.EdgeAbsCol
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# [S] Lemma 3.8 (absolute memory bounds), proved

Source: `verification/stage7-sources/S-02.tex`, lines 704–795 (`[S-02:0704–0795]`).

"There is `C_a`, allowed to depend on `m, C₁` but independent of `J`, such that every absolute
edge has weighted row and column bounds `L^{C_a}`."

`memoryAbsolute : MemoryAbsolute` is assembled from

* the row half `edgeAbs_rowBound` (`EdgeAbsRow.lean`; [S-02:0767–0786]), and
* the column half `edgeAbs_colBound` (`EdgeAbsCol.lean`; [S-02:0704–0756, 0788–0794]),

both for an arbitrary family of groups with explicit hypotheses, with the constants

`(∑_ν sup |K_ν|) · (∏_{g ∈ 𝒮} C_𝒮) · (∏_{g ∈ ℬ} C_ℬ)`,

`C_𝒮 = groupConst v₋ q T` the constant of (eq:physical-count-bound), `T = ℓ + m` the bound for the
number `t_g = ℓ + |C_g|` of unshared slots, and `C_ℬ` one of

* rows: `(2v)^T · max(1, 1/(v₋ρ))^T · sup_z (z+T)^T ρ^z · max(1, 2)^T`
  (stores `2^{t_g} v^{b_g}`; promotions `V_g^{-a_g}` with (eq:promotion-count); fresh mass
  `μ̃_g(𝒫_g)^{t_g - a_g} ≤ 2^{t_g}`);
* columns: `(1 + T v / v₋)^T · 2^T · max(1, 2)^T · ρ^{-T} sup_z (z+T)^T ρ^z`
  (reversed promotions; stores; integrated labels; reversed stores `(Z'')_{b_g} ρ^{Z'' - b_g}`).

Here `v = memV P`, `ρ = memRho P`. The hypotheses are discharged for the prime groups of
Definition 3.1 and `x ≥ x₀(P)`: `μ̃_g > 0` and `μ̃_g(𝒫_g) ≤ 2` for large `x`
(`eventually_big_tilt`, `eventually_tiltLaw_sum_le`), `V_g ≥ v₋`, `|C_g| ≤ m` and
(eq:pattern-mass) from `Admissible`. The products over the `≤ C₀ T` groups are powers of `L`
(`PrimeGroups.prod_small_le_rpow`, `PrimeGroups.prod_big_le_rpow`).

The exponent is `C_a = memAbsExponent P m C₁ = C₁ + C₀ log C_𝒮 + C₀ log C_ℬ`; it does not depend
on `J`, `C₂`, the cutoff `Bc` or `θ`, and the threshold `x₀` depends on `P` only.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

open Filter

noncomputable section

/-- **The constant of one big group in Lemma 3.8**: the maximum of `1`, of the row constant
`(2v)^T max(1, 1/(v₋ρ))^T sup_z (z+T)^T ρ^z · max(1,2)^T` and of the column constant
`(1 + Tv/v₋)^T 2^T max(1,2)^T ρ^{-T} sup_z (z+T)^T ρ^z`, for `T = ℓ + m`, `v = memV P`,
`ρ = memRho P` [S-02:0767–0794]. It depends on `P` and `m` only. -/
def memAbsBigConst (P : GroupParams) (m : ℕ) : ℝ :=
  max 1 (max
    (edgeAbsRowConst P.vMinus (memRho P) (memV P) (P.ℓ + m) * (max (1 : ℝ) 2) ^ (P.ℓ + m))
    (edgeAbsColConst P.vMinus (memRho P) (memV P) 2 (P.ℓ + m)))

/-- **The exponent `C_a` of Lemma 3.8**: `C₁ + C₀ log C_𝒮 + C₀ log C_ℬ`, where
`C_𝒮 = groupConst v₋ q (ℓ + m)` is the constant of (eq:physical-count-bound) and
`C_ℬ = memAbsBigConst P m`: "multiplying over groups, averaging permutations and free labels, and
summing (eq:pattern-mass)" [S-02:0784–0786], with at most `C₀ T` groups. It depends only on `m`,
`C₁` and the fixed data of Definition 3.1; in particular it is independent of `J`. -/
def memAbsExponent (P : GroupParams) (m : ℕ) (C₁ : ℝ) : ℝ :=
  C₁ + (Real.log (Schur.groupConst P.vMinus P.q (P.ℓ + m)) * P.C₀ +
    Real.log (memAbsBigConst P m) * P.C₀)

/-- **Lemma 3.8 for fixed constants**, with the exponent `memAbsExponent P m C₁` and a threshold
depending on `P` only. -/
theorem memoryAbsoluteBound (P : GroupParams) (m : ℕ) (C₁ : ℝ) (J : ℕ) (C₂ : ℝ) :
    MemoryAbsoluteBound P m C₁ (memAbsExponent P m C₁) J C₂ := by
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp ((eventually_big_tilt P one_pos).and
    ((eventually_tiltLaw_sum_le P).and (Real.tendsto_log_atTop.eventually_ge_atTop 1)))
  refine ⟨x₀, fun x hx S B _ _ _ _ 𝔊 N _ 𝔉 ζ k hadm Bc => ?_⟩
  obtain ⟨htilt, hsum, hL1⟩ := hx₀ x hx
  have hL0 : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hL1
  have hρ0 := memRho_pos P
  have hρ1 := memRho_lt_one P
  have hv1 : 1 ≤ memV P := (one_lt_memV P).le
  have hv0 : 0 < memV P := lt_of_lt_of_le zero_lt_one hv1
  have hT : 0 < P.ℓ + m := Nat.add_pos_left P.ℓ_pos m
  have hℓT : P.ℓ ≤ P.ℓ + m := Nat.le_add_right P.ℓ m
  have hC : ∀ ν g, P.ℓ + ((𝔉 ν).C g).card ≤ P.ℓ + m := fun ν g =>
    Nat.add_le_add_left (hadm.1 ν g) P.ℓ
  have hν : ∀ g, ∀ p ∈ 𝔊.big g,
      0 ≤ tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p :=
    fun g p hp => (htilt S B 𝔊 g p hp).2.1.le
  have hM : ∀ g : B, ∑ p ∈ 𝔊.big g,
      tiltLaw (𝔊.big g) P.q (Graph.sourceMemoryLength (Real.log x)) p ≤ 2 :=
    fun g => hsum S B 𝔊 g
  -- the constants of the groups
  have hG1 : 1 ≤ Schur.groupConst P.vMinus P.q (P.ℓ + m) := Schur.one_le_groupConst _ _ _
  have hGpos : 0 < Schur.groupConst P.vMinus P.q (P.ℓ + m) := lt_of_lt_of_le zero_lt_one hG1
  have hK1 : 1 ≤ memAbsBigConst P m := le_max_left _ _
  have hKpos : 0 < memAbsBigConst P m := lt_of_lt_of_le zero_lt_one hK1
  have hmx0 : (0 : ℝ) ≤ max (1 : ℝ) 2 := zero_le_one.trans (le_max_left _ _)
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
  have hCb0 : 0 ≤ edgeAbsColConst P.vMinus (memRho P) (memV P) 2 (P.ℓ + m) :=
    edgeAbsColConst_nonneg P.vMinus_pos hρ0 hρ1 hv0.le _
  have hCbK : edgeAbsColConst P.vMinus (memRho P) (memV P) 2 (P.ℓ + m) ≤ memAbsBigConst P m :=
    (le_max_right _ _).trans (le_max_right _ _)
  -- the products over the groups are powers of `L`
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
  have hprodCol : ∏ _g : B, edgeAbsColConst P.vMinus (memRho P) (memV P) 2 (P.ℓ + m) ≤
      Real.log x ^ (Real.log (memAbsBigConst P m) * P.C₀) :=
    𝔊.prod_big_le_rpow hL0
      (fun _ => edgeAbsColConst P.vMinus (memRho P) (memV P) 2 (P.ℓ + m))
      (Real.log (memAbsBigConst P m)) (Real.log_nonneg hK1) (fun _ => hCb0)
      (fun _ => hCbK.trans (Real.exp_log hKpos).ge)
  have hPS0 : 0 ≤ ∏ _g : S, Schur.groupConst P.vMinus P.q (P.ℓ + m) :=
    Finset.prod_nonneg fun _ _ => hGpos.le
  have hPR0 : 0 ≤ (∏ _g : B, edgeAbsRowConst P.vMinus (memRho P) (memV P) (P.ℓ + m)) *
      ∏ _g : B, (max (1 : ℝ) 2) ^ (P.ℓ + m) :=
    mul_nonneg (Finset.prod_nonneg fun _ _ => hrowC0)
      (Finset.prod_nonneg fun _ _ => pow_nonneg hmx0 _)
  have hPC0 : 0 ≤ ∏ _g : B, edgeAbsColConst P.vMinus (memRho P) (memV P) 2 (P.ℓ + m) :=
    Finset.prod_nonneg fun _ _ => hCb0
  have hRowLe : patternMass 𝔉 *
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
  have hColLe : patternMass 𝔉 *
        ((∏ _g : S, Schur.groupConst P.vMinus P.q (P.ℓ + m)) *
          ∏ _g : B, edgeAbsColConst P.vMinus (memRho P) (memV P) 2 (P.ℓ + m)) ≤
      Real.log x ^ memAbsExponent P m C₁ := by
    unfold memAbsExponent
    rw [Real.rpow_add hL0, Real.rpow_add hL0]
    exact mul_le_mul hadm.2.1
      (mul_le_mul hprodS hprodCol hPC0 (Real.rpow_nonneg hL0.le _))
      (mul_nonneg hPS0 hPC0) (Real.rpow_nonneg hL0.le _)
  intro θ i _
  have hrow := edgeAbs_rowBound (memData 𝔊 𝔉 k ζ) θ i (Bc := Bc) (v := memV P)
    (vMinus := P.vMinus) (Mmax := 2) (T := P.ℓ + m) P.q_pos P.q_lt_one hρ0 hρ1 hv1
    P.vMinus_pos 𝔊.mass_small_ge 𝔊.mass_big_ge 𝔊.big_law_sum hν hM hT hℓT hC
  have hcol := edgeAbs_colBound (memData 𝔊 𝔉 k ζ) θ i (Bc := Bc) (v := memV P)
    (vMinus := P.vMinus) (Mmax := 2) (T := P.ℓ + m) P.q_pos P.q_lt_one hρ0 hρ1 hv1
    P.vMinus_pos 𝔊.mass_small_ge 𝔊.mass_big_ge 𝔊.big_law_sum hν hM hT hℓT hC
  exact ⟨hrow.mono (fun s => (schurWeight_pos hv0 s).le) hRowLe,
    colBound_mono_of_nonneg hcol
      (fun s => memWeight_nonneg 𝔊.toGroupFamily P.q _ hν s)
      (fun s => (schurWeight_pos hv0 s).le) hColLe⟩

/-- **[S] Lemma 3.8 (absolute memory bounds, `lem:memory-absolute`)** [S-02:0758–0795], proved:
the weighted row and column bounds `L^{C_a}` of the absolute edges, with
`C_a = memAbsExponent P m C₁` depending on `P`, `m`, `C₁` only, for every `J`, `C₂`, every cutoff
and every `θ`. -/
theorem memoryAbsolute : MemoryAbsolute :=
  fun P m C₁ => ⟨memAbsExponent P m C₁, fun J C₂ => memoryAbsoluteBound P m C₁ J C₂⟩

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
