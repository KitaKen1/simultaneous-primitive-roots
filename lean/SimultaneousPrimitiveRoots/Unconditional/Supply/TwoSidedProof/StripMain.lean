module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.StripGeneral

/-!
# Removal of the shared labels: one pattern, uniformly

`Strip.general` (`[P-06:0318–0370]`, `[PUB-tex:0482–0485]`): for fixed data `D`, a number `J` of
first slots, a bound `m₀` for the freed slots, an exponent `c_K` for the size of the coefficient
and a saving `A`, there are `M, x₀` such that for `x ≥ x₀`, every configuration, every pattern `ν`
with `|C_g| ≤ m₀`, `|K_ν| ≤ L^{c_K}` whose coefficient is a function `κ` (of size `≤ L^{c_K}`) of
the free labels and of the unshared labels of the two endpoints,

`|edgeTerm ν - genStrip κ| ≤ M L^{-A}`.

Inputs: the invariance of `F_x` under the active primes, its boundedness on `[1, x²]`,
(cor:marked-bound); the divisor moments, the count (eq:physical-count-bound) of [S] and the
compact support of `Ψ` in `(0, ∞)` are theorems.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference
open Filter

noncomputable section

namespace Strip

/-- **Removal of the shared labels for one pattern** (`[P-06:0318–0370]`). -/
theorem general {d H : ℕ} (𝔅 : JointResidueWeight H) (hH : 0 < H) (hCI : CoreInvariance d)
    (hCP : CorePowerBounded d) (hMB : MarkedBound) (D : FixedData) (J m₀ : ℕ) (cK A : ℝ) :
    ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ I : Config d D x,
      ∀ (ν : Pattern (groupFamily I.𝔊).big J 1)
        (κ : AuxList (groupFamily I.𝔊).big ν.C →
          ((g : I.𝔊.Index) → Fin (markCount I.𝔊 ν.C g) → ℕ) →
          ((g : I.𝔊.Index) → Fin (markCount I.𝔊 ν.C g) → ℕ) → ℂ),
        (∀ g, (ν.C g).card ≤ m₀) →
        (∀ (σ : ShT I.𝔊 ν.C) (u u' : UnT I.𝔊 ν.C) (r : AuxList (groupFamily I.𝔊).big ν.C),
          ν.K ((listSplit I.𝔊 ν.C).symm (σ, u)).2 ((listSplit I.𝔊 ν.C).symm (σ, u')).2 r =
            κ r (unVal u) (unVal u')) →
        (∀ p p' r, ‖ν.K p p' r‖ ≤ Real.log x ^ cK) →
        (∀ r 𝔭 𝔭', ‖κ r 𝔭 𝔭'‖ ≤ Real.log x ^ cK) →
        ‖edgeTerm I.𝔊 D.q₀ ν x D.Ψ 𝔅 (centeredCore D.q D.𝔞 x I.S) I.G -
            genStrip D.q₀ x D.Ψ 𝔅 (centeredCore D.q D.𝔞 x I.S) I.G ν.C κ‖ ≤
          M * Real.log x ^ (-A) := by
  obtain ⟨xI, hxI⟩ := hCI D.ε D.ε_pos
  obtain ⟨Bf, hBf0, hBf⟩ := hCP D.q D.q_pos D.q_lt_one D.ε D.ε_pos 2 (by norm_num) D.K
  obtain ⟨xc, hc⟩ := hBf D.𝔞
  obtain ⟨Cm, xm, hm⟩ := hMB D.P D.q₀ D.q₀_pos D.q₀_lt_one (m₀ + 1)
  obtain ⟨c₁, c₂, hc₁, hc₁₂, hsup⟩ := MellinSep.exists_support_bounds D.compact D.support
  obtain ⟨Ψmax, hΨmax⟩ := D.smooth.continuous.bounded_above_of_compact_support D.compact
  obtain ⟨⟨Cτ, Aτ, hCτ, hτ⟩, -⟩ := divisorMoments ⌈D.C⌉₊
  have hc₂ : 0 < c₂ := lt_of_lt_of_le hc₁ hc₁₂
  have hΨ0' : 0 ≤ Ψmax := (norm_nonneg _).trans (hΨmax 0)
  have hC0 : 0 < D.P.C₀ := D.P.C₀_pos
  obtain ⟨E₁, hE₁⟩ : ∃ E₁ : ℝ, E₁ =
      4 * (Real.log (Schur.groupConst D.P.vlo D.q₀ (m₀ + 1)) * D.P.C₀) + 2 * |Cm| := ⟨_, rfl⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = D.C + max Aτ 0 := ⟨_, rfl⟩
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ,
      K₀ = Ψmax * Bf * Cτ * (3 : ℝ) ^ (max Aτ 0) * ((c₂ + 1) / c₁) := ⟨_, rfl⟩
  obtain ⟨cP, hcP⟩ : ∃ cP : ℝ, cP = (2 * ((J : ℝ) + 1) * D.P.C₀) ^ 2 +
      2 * ((J : ℝ) + 1) * D.P.C₀ * ((m₀ : ℝ) * D.P.C₀ + 4) := ⟨_, rfl⟩
  have hK₀0 : 0 ≤ K₀ := by
    rw [hK₀]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hΨ0' hBf0) hCτ.le)
      (Real.rpow_nonneg (by norm_num) _)) (div_nonneg (by linarith) hc₁.le)
  have hJ : (0 : ℝ) ≤ (J : ℝ) + 1 := by positivity
  have hcP0 : 0 ≤ cP := by
    rw [hcP]
    exact add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hJ) hC0.le)
      (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hC0.le) (by norm_num)))
  have hmC0 : 0 ≤ (m₀ : ℝ) * D.P.C₀ := mul_nonneg (Nat.cast_nonneg _) hC0.le
  -- the thresholds
  have hA1 : ∀ᶠ L : ℝ in atTop,
      ‖Real.log L‖ ≤ (|cK + E₁ + c₀ + 2 + A| + 1)⁻¹ * ‖L ^ (0.27 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.27)).def
      (inv_pos.mpr (by positivity))
  have hA2 : ∀ᶠ L : ℝ in atTop, ‖Real.log L‖ ≤ 1 * ‖L ^ (0.19 : ℝ)‖ :=
    (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.19)).def one_pos
  have hD1 : ∀ᶠ L : ℝ in atTop, 2 * ((m₀ : ℝ) * D.P.C₀) ≤ L ^ (0.35 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.35)).eventually_ge_atTop _
  have hH1 : ∀ᶠ L : ℝ in atTop, (H : ℝ) ≤ L ^ (0.27 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.27)).eventually_ge_atTop _
  have hB1 : ∀ᶠ L : ℝ in atTop, max 1 (2 * Real.log (c₂ + 1)) ≤ L := eventually_ge_atTop _
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.mp
    (Real.tendsto_log_atTop.eventually ((((hA1.and hA2).and hD1).and hH1).and hB1))
  refine ⟨2 * K₀ * ((m₀ : ℝ) * D.P.C₀ + cP / D.P.vlo),
    max (max xI xc) (max xm (max x₁ (max 3 c₂⁻¹))), fun x hx I ν κ hC hκ hK hκK => ?_⟩
  have hxI' : xI ≤ x := (le_max_left _ _).trans ((le_max_left _ _).trans hx)
  have hxc : xc ≤ x := (le_max_right _ _).trans ((le_max_left _ _).trans hx)
  have hxa := (le_max_right _ _).trans hx
  have hxm : xm ≤ x := (le_max_left _ _).trans hxa
  have hxb := (le_max_right _ _).trans hxa
  have hxx₁ : x₁ ≤ x := (le_max_left _ _).trans hxb
  have hxd := (le_max_right _ _).trans hxb
  have hx3 : (3 : ℝ) ≤ x := (le_max_left _ _).trans hxd
  have hxc₂ : c₂⁻¹ ≤ x := (le_max_right _ _).trans hxd
  obtain ⟨⟨⟨⟨hlog27, hlog19⟩, hmCL⟩, hHL⟩, hBL⟩ := hx₁ x hxx₁
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hL1 : 1 ≤ Real.log x := (le_max_left _ _).trans hBL
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  have hlogc : 2 * Real.log (c₂ + 1) ≤ Real.log x := (le_max_right _ _).trans hBL
  have hc₂x : 1 ≤ c₂ * x := by
    have h := mul_le_mul_of_nonneg_left hxc₂ hc₂.le
    rwa [mul_inv_cancel₀ hc₂.ne'] at h
  -- the active primes exceed `H`
  have hprime : ∀ p ∈ I.𝔊.allPrimes, H < p := by
    intro p hp
    have h1 := exp_le_active I hL1 hp
    have h2 : (H : ℝ) < Real.exp (Real.log x ^ (0.27 : ℝ)) := by
      have h := Real.add_one_le_exp (Real.log x ^ (0.27 : ℝ))
      linarith
    exact_mod_cast lt_of_lt_of_le h2 h1
  -- the first endpoint
  have hF : ∀ p ∈ I.𝔊.allPrimes, ∀ n : ℕ,
      centeredCore D.q D.𝔞 x I.S (p * n) = centeredCore D.q D.𝔞 x I.S n :=
    hxI x hxI' D.q D.K D.𝔞 D.P I.𝔊 I.groups I.S I.slots
  have hBfx : ∀ u : ℕ, 1 ≤ u → (u : ℝ) ≤ x ^ 2 → |centeredCore D.q D.𝔞 x I.S u| ≤ Bf :=
    fun u hu hle => hc x hxc I.S I.slots u hu (by
      rw [Real.rpow_two]
      exact hle)
  -- (cor:marked-bound)
  have hLm : ∀ n : ℕ,
      ‖I.𝔊.activeWeight D.q₀ (markCount I.𝔊 ν.C) (fun _ => 1) n‖ ≤ Real.log x ^ Cm :=
    fun n => hm x hxm I.𝔊 I.groups (markCount I.𝔊 ν.C) (fun g => by
      rcases g with g | g
      · exact Nat.le_add_left 1 m₀
      · exact Nat.add_le_add_right (hC g) 1) (fun _ => 1) (fun _ => le_of_eq norm_one) n
  -- the positions are at most `x²`
  have hE : Real.log (c₂ + 1) +
      (m₀ : ℝ) * D.P.C₀ * Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ) ≤ Real.log x := by
    have hT0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL1
    have hp19 : 0 ≤ Real.log x ^ (0.19 : ℝ) := Real.rpow_nonneg hL0.le _
    have hp46 : 0 ≤ Real.log x ^ (0.46 : ℝ) := Real.rpow_nonneg hL0.le _
    have hp35 : 0 ≤ Real.log x ^ (0.35 : ℝ) := Real.rpow_nonneg hL0.le _
    have hlog19' : Real.log (Real.log x) ≤ Real.log x ^ (0.19 : ℝ) := by
      have h' : ‖Real.log (Real.log x)‖ ≤ 1 * ‖Real.log x ^ (0.19 : ℝ)‖ := hlog19
      rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hT0,
        abs_of_nonneg hp19] at h'
      exact h'
    have h3 : (m₀ : ℝ) * D.P.C₀ ≤ Real.log x ^ (0.35 : ℝ) * (1 / 2) := by linarith
    have h4 : Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ) ≤
        Real.log x ^ (0.19 : ℝ) * Real.log x ^ (0.46 : ℝ) :=
      mul_le_mul_of_nonneg_right hlog19' hp46
    have h5 := mul_le_mul h3 h4 (mul_nonneg hT0 hp46)
      (mul_nonneg hp35 (by norm_num : (0 : ℝ) ≤ 1 / 2))
    have e : Real.log x ^ (0.35 : ℝ) *
        (Real.log x ^ (0.19 : ℝ) * Real.log x ^ (0.46 : ℝ)) = Real.log x := by
      have e' : (0.35 : ℝ) + (0.19 + 0.46) = 1 := by norm_num
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, e', Real.rpow_one]
    have h6 : (m₀ : ℝ) * D.P.C₀ * Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ) ≤
        Real.log x * (1 / 2) :=
      calc (m₀ : ℝ) * D.P.C₀ * Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ)
          = (m₀ : ℝ) * D.P.C₀ * (Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ)) := by ring
        _ ≤ Real.log x ^ (0.35 : ℝ) * (1 / 2) *
              (Real.log x ^ (0.19 : ℝ) * Real.log x ^ (0.46 : ℝ)) := h5
        _ = Real.log x ^ (0.35 : ℝ) *
              (Real.log x ^ (0.19 : ℝ) * Real.log x ^ (0.46 : ℝ)) * (1 / 2) := by ring
        _ = Real.log x * (1 / 2) := by rw [e]
    linarith
  have hwin : ∀ r : AuxList (groupFamily I.𝔊).big ν.C,
      (c₂ * x + 1) * (tupleProd ν.C r : ℝ) ≤ x ^ 2 :=
    fun r => window_le I hx1 hL1 ν.C hC r hc₂.le hE
  -- the cutoff
  obtain ⟨N, hN⟩ := exists_cutoff_range (big := (groupFamily I.𝔊).big) ν.C D.compact D.support
    hx0
  have hΨ0 : ∀ t : ℝ, t ≤ 0 → D.Ψ t = 0 := fun t ht => by
    by_contra hne
    linarith [(hsup t hne).1]
  have hc₂' : ∀ t : ℝ, c₂ < t → D.Ψ t = 0 := fun t ht => by
    by_contra hne
    linarith [(hsup t hne).2]
  -- the structural inequality
  have hK0 : 0 ≤ Real.log x ^ cK := Real.rpow_nonneg hL0.le _
  have hstruct := norm_edgeTerm_sub_le I.groups (law_sum I) hH hprime 𝔅 hF I.core D.q₀_pos
    D.q₀_lt_one hx0 hΨ0 hc₂.le hc₂' ν κ hκ hK0 hK hκK (Nat.le_add_left 1 m₀)
    (fun g => by
      have h := hC g
      omega) hLm hN
  -- the sum of the errors
  have hF3 : ∀ r : AuxList (groupFamily I.𝔊).big ν.C,
      ∑ w ∈ Finset.Ico 1 N,
        ‖corePart x D.Ψ 𝔅 (centeredCore D.q D.𝔞 x I.S) I.G ν.C r w‖ *
          (freeInd r w + ∑ σ : ShT I.𝔊 ν.C, shWeight σ * badInd σ (forbid r w)) ≤
      K₀ * Real.log x ^ c₀ *
        ((m₀ : ℝ) * D.P.C₀ * Real.log x * Real.exp (-(Real.log x ^ (0.27 : ℝ))) +
          cP * Real.log x ^ 2 * (D.P.vlo * Real.exp (Real.log x ^ (0.27 : ℝ)))⁻¹) := by
    intro r
    rw [hK₀, hc₀, hcP]
    exact sum_core_error_le I hx1 hL1 𝔅 ν.C hC r hc₁ hc₂x hc₂.le hsup hΨmax hBf0 hBfx hCτ hτ
      (hwin r) N
  have hauxsum : ∑ r : AuxList (groupFamily I.𝔊).big ν.C,
      auxWeight (groupFamily I.𝔊).big ν.C r = 1 := Comparison.sum_tupleWeight I.primeGroups ν.C
  have hS : ∑ w ∈ Finset.Ico 1 N, ∑ r : AuxList (groupFamily I.𝔊).big ν.C,
        ‖corePart x D.Ψ 𝔅 (centeredCore D.q D.𝔞 x I.S) I.G ν.C r w‖ *
          (auxWeight (groupFamily I.𝔊).big ν.C r *
            (freeInd r w + ∑ σ : ShT I.𝔊 ν.C, shWeight σ * badInd σ (forbid r w))) ≤
      K₀ * Real.log x ^ c₀ *
        ((m₀ : ℝ) * D.P.C₀ * Real.log x * Real.exp (-(Real.log x ^ (0.27 : ℝ))) +
          cP * Real.log x ^ 2 * (D.P.vlo * Real.exp (Real.log x ^ (0.27 : ℝ)))⁻¹) := by
    refine le_trans (le_of_eq ?_) (sum_weighted_le (Finset.Ico 1 N)
      (fun r : AuxList (groupFamily I.𝔊).big ν.C => auxWeight (groupFamily I.𝔊).big ν.C r)
      (fun r w => ‖corePart x D.Ψ 𝔅 (centeredCore D.q D.𝔞 x I.S) I.G ν.C r w‖ *
        (freeInd r w + ∑ σ : ShT I.𝔊 ν.C, shWeight σ * badInd σ (forbid r w)))
      (fun r => Schur.auxWeight_nonneg _ _ _) hauxsum hF3)
    exact Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun r _ => by ring
  have hS0 : 0 ≤ ∑ w ∈ Finset.Ico 1 N, ∑ r : AuxList (groupFamily I.𝔊).big ν.C,
      ‖corePart x D.Ψ 𝔅 (centeredCore D.q D.𝔞 x I.S) I.G ν.C r w‖ *
        (auxWeight (groupFamily I.𝔊).big ν.C r *
          (freeInd r w + ∑ σ : ShT I.𝔊 ν.C, shWeight σ * badInd σ (forbid r w))) :=
    Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun r _ =>
      mul_nonneg (norm_nonneg _) (mul_nonneg (Schur.auxWeight_nonneg _ _ _)
        (add_nonneg (freeInd_nonneg r w) (Finset.sum_nonneg fun σ _ =>
          mul_nonneg (shWeight_nonneg σ) (badInd_nonneg σ _))))
  -- the list costs
  have hG2 := gamma_le I hL1 (m₀ + 1) Cm
  rw [← hE₁] at hG2
  -- the threshold
  have hth : Real.log x ^ cK * Real.log x ^ E₁ * Real.log x ^ c₀ * Real.log x ^ 2 *
      Real.log x ^ A ≤ Real.exp (Real.log x ^ (0.27 : ℝ)) := by
    have h := exp_threshold hL1 hlog27
    rw [Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_add hL0,
      Real.rpow_two] at h
    exact h
  exact hstruct.trans (final_arith hL1 hK₀0 D.P.vlo_pos hcP0 hmC0 hG2 hS0 hS hth)

end Strip

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
