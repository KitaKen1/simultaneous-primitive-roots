module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.StripBounds
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.MellinSeparationProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.KernelExpansionProof
public import SimultaneousPrimitiveRoots.Unconditional.Transference.GraphBridge

/-!
# Removal of the shared labels: the estimate for one pattern

`[P-06:0318–0370]`, `[PUB-tex:0482–0485]`. `Strip.general`: for a pattern `ν` with at most `m₀`
freed slots in every big group, a coefficient of size at most `L^{c_K}` which is a function
`κ` of the free labels and of the unshared labels of the two endpoints, the edge sum of `ν` is its
stripped expression `Strip.genStrip` up to `M L^{-A}`, uniformly in the configuration and in the
pattern.

"All errors remain smaller than every negative log power after the fixed pattern cost": the
errors are `L^{O(1)} exp(-L^{.27})` (a shared label collides) and `L^{O(1)} exp(-L^{.39})` (a free
label divides `w`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference
open Filter

noncomputable section

namespace Strip

section General

variable {d : ℕ} {D : FixedData} {x : ℝ}

/-! ### The two errors for fixed free labels -/

/-- **The free-label and the collision errors for fixed free labels** (`[P-06:0340–0366]`). -/
theorem sum_core_error_le (I : Config d D x) (hx1 : 1 ≤ x) (hL1 : 1 ≤ Real.log x) {H : ℕ}
    (𝔅 : JointResidueWeight H) {F : ℕ → ℝ} {J m₀ : ℕ} (C : Fin I.𝔊.numBig → Finset (Fin J))
    (hC : ∀ g, (C g).card ≤ m₀) (r : AuxList (groupFamily I.𝔊).big C) {c₁ c₂ Ψmax Bf : ℝ}
    (hc₁ : 0 < c₁) (hc₂x : 1 ≤ c₂ * x) (hc₂ : 0 ≤ c₂)
    (hsup : ∀ t : ℝ, D.Ψ t ≠ 0 → c₁ ≤ t ∧ t ≤ c₂) (hΨmax : ∀ t : ℝ, ‖D.Ψ t‖ ≤ Ψmax)
    (hBf0 : 0 ≤ Bf) (hBf : ∀ u : ℕ, 1 ≤ u → (u : ℝ) ≤ x ^ 2 → |F u| ≤ Bf) {Cτ Aτ : ℝ}
    (hCτ : 0 < Cτ)
    (hτ : ∀ Y : ℝ, 1 ≤ Y → ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n.divisors.card : ℝ) ^ ⌈D.C⌉₊ ≤
      Cτ * Y * Real.log (2 * Y) ^ Aτ)
    (hwin : (c₂ * x + 1) * (tupleProd C r : ℝ) ≤ x ^ 2) (N : ℕ) :
    ∑ w ∈ Finset.Ico 1 N, ‖corePart x D.Ψ 𝔅 F I.G C r w‖ *
        (freeInd r w + ∑ σ : ShT I.𝔊 C, shWeight σ * badInd σ (forbid r w)) ≤
      Ψmax * Bf * Cτ * (3 : ℝ) ^ (max Aτ 0) * ((c₂ + 1) / c₁) *
          Real.log x ^ (D.C + max Aτ 0) *
        ((m₀ : ℝ) * D.P.C₀ * Real.log x * Real.exp (-(Real.log x ^ (0.27 : ℝ))) +
          ((2 * ((J : ℝ) + 1) * D.P.C₀) ^ 2 +
              2 * ((J : ℝ) + 1) * D.P.C₀ * ((m₀ : ℝ) * D.P.C₀ + 4)) * Real.log x ^ 2 *
            (D.P.vlo * Real.exp (Real.log x ^ (0.27 : ℝ)))⁻¹) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  have hDN : 0 < tupleProd C r := Comparison.tupleProd_pos I.primeGroups C r
  have hDpos : (0 : ℝ) < (tupleProd C r : ℝ) := Nat.cast_pos.mpr hDN
  have hxD : 0 < x * (tupleProd C r : ℝ) := mul_pos hx0 hDpos
  have hΨ0 : 0 ≤ Ψmax := (norm_nonneg _).trans (hΨmax 0)
  have hC0 : 0 < D.P.C₀ := D.P.C₀_pos
  have hJ : (0 : ℝ) ≤ (J : ℝ) + 1 := by positivity
  have hcP0 : 0 ≤ (2 * ((J : ℝ) + 1) * D.P.C₀) ^ 2 +
      2 * ((J : ℝ) + 1) * D.P.C₀ * ((m₀ : ℝ) * D.P.C₀ + 4) :=
    add_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hJ) hC0.le)
      (add_nonneg (mul_nonneg (Nat.cast_nonneg _) hC0.le) (by norm_num)))
  have hδ0 : 0 ≤ (D.P.vlo * Real.exp (Real.log x ^ (0.27 : ℝ)))⁻¹ :=
    inv_nonneg.mpr (mul_pos D.P.vlo_pos (Real.exp_pos _)).le
  obtain ⟨KL, hKL⟩ : ∃ KL : ℝ, KL = Ψmax * Bf * Cτ * (3 : ℝ) ^ (max Aτ 0) * ((c₂ + 1) / c₁) *
      Real.log x ^ (D.C + max Aτ 0) := ⟨_, rfl⟩
  have hKL0 : 0 ≤ KL := by
    rw [hKL]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hΨ0 hBf0) hCτ.le)
      (Real.rpow_nonneg (by norm_num) _)) (div_nonneg (by linarith) hc₁.le))
      (Real.rpow_nonneg hL0.le _)
  -- the window
  have hcD : c₂ * x * (tupleProd C r : ℝ) ≤ (c₂ * x + 1) * (tupleProd C r : ℝ) := by
    nlinarith [hDpos]
  have hBf' : ∀ u : ℕ, 1 ≤ u → (u : ℝ) ≤ c₂ * x * (tupleProd C r : ℝ) → |F u| ≤ Bf :=
    fun u hu hle => hBf u hu (hle.trans (hcD.trans hwin))
  have hlogY : Real.log (2 * ((c₂ * x + 1) * (tupleProd C r : ℝ))) ≤ 3 * Real.log x := by
    have hYpos : 0 < (c₂ * x + 1) * (tupleProd C r : ℝ) := mul_pos (by linarith) hDpos
    have h1 : Real.log (2 * ((c₂ * x + 1) * (tupleProd C r : ℝ))) ≤ Real.log (2 * x ^ 2) :=
      Real.log_le_log (by linarith) (by linarith)
    have h2 : Real.log (2 * x ^ 2) = Real.log 2 + 2 * Real.log x := by
      rw [Real.log_mul two_ne_zero (pow_ne_zero 2 hx0.ne'), Real.log_pow, Nat.cast_ofNat]
    have h3 : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2)
      linarith
    linarith
  have hcore : ∀ m : ℕ, 0 < m → m ∣ tupleProd C r →
      (∀ p : ℕ, p.Prime → p ∣ m → p ∈ I.𝔊.allPrimes) →
      ∑ w ∈ Finset.Ico 1 N, (if m ∣ w then ‖corePart x D.Ψ 𝔅 F I.G C r w‖ else 0) ≤
        KL / (m : ℝ) := by
    intro m hm0 hmD hmA
    rw [hKL]
    exact sum_corePart_le I hx1 hL1 𝔅 C r hc₁ hc₂x hc₂ hsup hΨmax hBf0 hBf' hCτ hτ hlogY hm0
      hmD hmA N
  have hall : ∑ w ∈ Finset.Ico 1 N, ‖corePart x D.Ψ 𝔅 F I.G C r w‖ ≤ KL := by
    have h := hcore 1 Nat.one_pos (one_dvd _)
      (fun p hp hd => absurd (Nat.dvd_one.mp hd) hp.ne_one)
    rw [Nat.cast_one, div_one] at h
    exact le_trans (le_of_eq (Finset.sum_congr rfl fun w _ =>
      (if_pos (one_dvd w)).symm)) h
  -- a free label divides `w`
  have hlogL : Real.log (Real.log x) ≤ Real.log x := by
    have h := Real.log_le_sub_one_of_pos hL0
    linarith
  have hnfree : (Fintype.card (Σ g : Fin I.𝔊.numBig, {i : Fin J // i ∈ C g}) : ℝ) ≤
      (m₀ : ℝ) * D.P.C₀ * Real.log x := by
    have h : Fintype.card (Σ g : Fin I.𝔊.numBig, {i : Fin J // i ∈ C g}) ≤
        I.𝔊.numBig * m₀ := by
      rw [Fintype.card_sigma]
      calc ∑ g : Fin I.𝔊.numBig, Fintype.card {i : Fin J // i ∈ C g}
          = ∑ g : Fin I.𝔊.numBig, (C g).card :=
            Finset.sum_congr rfl fun g _ => Fintype.card_coe (C g)
        _ ≤ ∑ _g : Fin I.𝔊.numBig, m₀ := Finset.sum_le_sum fun g _ => hC g
        _ = I.𝔊.numBig * m₀ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    have h' : (Fintype.card (Σ g : Fin I.𝔊.numBig, {i : Fin J // i ∈ C g}) : ℝ) ≤
        (I.𝔊.numBig : ℝ) * (m₀ : ℝ) := by
      exact_mod_cast h
    have h4 : (I.𝔊.numBig : ℝ) ≤ D.P.C₀ * Real.log x :=
      I.groups.numBig_le.trans (mul_le_mul_of_nonneg_left hlogL hC0.le)
    calc (Fintype.card (Σ g : Fin I.𝔊.numBig, {i : Fin J // i ∈ C g}) : ℝ)
        ≤ (I.𝔊.numBig : ℝ) * (m₀ : ℝ) := h'
      _ ≤ (D.P.C₀ * Real.log x) * (m₀ : ℝ) := mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg _)
      _ = (m₀ : ℝ) * D.P.C₀ * Real.log x := by ring
  have he : Real.exp (-(Real.log x ^ (0.27 : ℝ))) = (Real.exp (Real.log x ^ (0.27 : ℝ)))⁻¹ :=
    Real.exp_neg _
  have hfreeterm : ∀ gi : (Σ g : Fin I.𝔊.numBig, {i : Fin J // i ∈ C g}),
      ∑ w ∈ Finset.Ico 1 N,
        (if (r gi.1 gi.2 : ℕ) ∣ w then ‖corePart x D.Ψ 𝔅 F I.G C r w‖ else 0) ≤
      KL * Real.exp (-(Real.log x ^ (0.27 : ℝ))) := by
    intro gi
    have hpmem : (r gi.1 gi.2 : ℕ) ∈ I.𝔊.allPrimes :=
      Finset.mem_biUnion.mpr ⟨Sum.inr gi.1, Finset.mem_univ _, (r gi.1 gi.2).2⟩
    have hpp : (r gi.1 gi.2 : ℕ).Prime := prime_of_mem_allPrimes I.groups hpmem
    have hpge := exp_le_active I hL1 hpmem
    have h := hcore (r gi.1 gi.2) hpp.pos (aux_dvd_tupleProd r gi.1 gi.2) (fun q hq hd => by
      rw [(Nat.prime_dvd_prime_iff_eq hq hpp).mp hd]
      exact hpmem)
    refine h.trans ?_
    rw [div_eq_mul_inv, he]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ (Real.exp_pos _) hpge) hKL0
  have hfree : ∑ w ∈ Finset.Ico 1 N, ‖corePart x D.Ψ 𝔅 F I.G C r w‖ * freeInd r w ≤
      KL * ((m₀ : ℝ) * D.P.C₀ * Real.log x * Real.exp (-(Real.log x ^ (0.27 : ℝ)))) := by
    calc ∑ w ∈ Finset.Ico 1 N, ‖corePart x D.Ψ 𝔅 F I.G C r w‖ * freeInd r w
        ≤ ∑ w ∈ Finset.Ico 1 N, ∑ gi : (Σ g : Fin I.𝔊.numBig, {i : Fin J // i ∈ C g}),
            (if (r gi.1 gi.2 : ℕ) ∣ w then ‖corePart x D.Ψ 𝔅 F I.G C r w‖ else 0) :=
          Finset.sum_le_sum fun w _ => by
            refine (mul_le_mul_of_nonneg_left (freeInd_le r w) (norm_nonneg _)).trans
              (le_of_eq ?_)
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun gi _ => ?_
            split_ifs
            · exact mul_one _
            · exact mul_zero _
      _ = ∑ gi : (Σ g : Fin I.𝔊.numBig, {i : Fin J // i ∈ C g}), ∑ w ∈ Finset.Ico 1 N,
            (if (r gi.1 gi.2 : ℕ) ∣ w then ‖corePart x D.Ψ 𝔅 F I.G C r w‖ else 0) :=
          Finset.sum_comm
      _ ≤ ∑ _gi : (Σ g : Fin I.𝔊.numBig, {i : Fin J // i ∈ C g}),
            KL * Real.exp (-(Real.log x ^ (0.27 : ℝ))) :=
          Finset.sum_le_sum fun gi _ => hfreeterm gi
      _ = (Fintype.card (Σ g : Fin I.𝔊.numBig, {i : Fin J // i ∈ C g}) : ℝ) *
            (KL * Real.exp (-(Real.log x ^ (0.27 : ℝ)))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      _ ≤ ((m₀ : ℝ) * D.P.C₀ * Real.log x) *
            (KL * Real.exp (-(Real.log x ^ (0.27 : ℝ)))) :=
          mul_le_mul_of_nonneg_right hnfree (mul_nonneg hKL0 (Real.exp_pos _).le)
      _ = _ := by ring
  -- a collision of the shared labels
  have hcollterm : ∀ w ∈ Finset.Ico 1 N, ‖corePart x D.Ψ 𝔅 F I.G C r w‖ *
        (∑ σ : ShT I.𝔊 C, shWeight σ * badInd σ (forbid r w)) ≤
      ‖corePart x D.Ψ 𝔅 F I.G C r w‖ *
        (((2 * ((J : ℝ) + 1) * D.P.C₀) ^ 2 +
            2 * ((J : ℝ) + 1) * D.P.C₀ * ((m₀ : ℝ) * D.P.C₀ + 4)) * Real.log x ^ 2 *
          (D.P.vlo * Real.exp (Real.log x ^ (0.27 : ℝ)))⁻¹) := by
    intro w hw
    have hw1 := (Finset.mem_Ico.mp hw).1
    by_cases h0 : D.Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) = 0
    · rw [corePart_eq_zero_of h0, norm_zero, zero_mul, zero_mul]
    · have h2 := (hsup _ h0).2
      have hup : (w : ℝ) ≤ c₂ * x * (tupleProd C r : ℝ) := by
        have h := (div_le_iff₀ hxD).mp h2
        linarith
      have hwx : ((w + tupleProd C r : ℕ) : ℝ) ≤ x ^ 2 := by
        rw [Nat.cast_add]
        linarith
      exact mul_le_mul_of_nonneg_left (collision_le I hL1 C hC r hw1 hwx) (norm_nonneg _)
  have hcoll : ∑ w ∈ Finset.Ico 1 N, ‖corePart x D.Ψ 𝔅 F I.G C r w‖ *
        (∑ σ : ShT I.𝔊 C, shWeight σ * badInd σ (forbid r w)) ≤
      KL * (((2 * ((J : ℝ) + 1) * D.P.C₀) ^ 2 +
          2 * ((J : ℝ) + 1) * D.P.C₀ * ((m₀ : ℝ) * D.P.C₀ + 4)) * Real.log x ^ 2 *
        (D.P.vlo * Real.exp (Real.log x ^ (0.27 : ℝ)))⁻¹) :=
    calc ∑ w ∈ Finset.Ico 1 N, ‖corePart x D.Ψ 𝔅 F I.G C r w‖ *
          (∑ σ : ShT I.𝔊 C, shWeight σ * badInd σ (forbid r w))
        ≤ ∑ w ∈ Finset.Ico 1 N, ‖corePart x D.Ψ 𝔅 F I.G C r w‖ *
            (((2 * ((J : ℝ) + 1) * D.P.C₀) ^ 2 +
                2 * ((J : ℝ) + 1) * D.P.C₀ * ((m₀ : ℝ) * D.P.C₀ + 4)) * Real.log x ^ 2 *
              (D.P.vlo * Real.exp (Real.log x ^ (0.27 : ℝ)))⁻¹) :=
          Finset.sum_le_sum hcollterm
      _ = (∑ w ∈ Finset.Ico 1 N, ‖corePart x D.Ψ 𝔅 F I.G C r w‖) *
            (((2 * ((J : ℝ) + 1) * D.P.C₀) ^ 2 +
                2 * ((J : ℝ) + 1) * D.P.C₀ * ((m₀ : ℝ) * D.P.C₀ + 4)) * Real.log x ^ 2 *
              (D.P.vlo * Real.exp (Real.log x ^ (0.27 : ℝ)))⁻¹) := (Finset.sum_mul _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hall
          (mul_nonneg (mul_nonneg hcP0 (sq_nonneg _)) hδ0)
  rw [← hKL]
  calc ∑ w ∈ Finset.Ico 1 N, ‖corePart x D.Ψ 𝔅 F I.G C r w‖ *
        (freeInd r w + ∑ σ : ShT I.𝔊 C, shWeight σ * badInd σ (forbid r w))
      = ∑ w ∈ Finset.Ico 1 N, ‖corePart x D.Ψ 𝔅 F I.G C r w‖ * freeInd r w +
          ∑ w ∈ Finset.Ico 1 N, ‖corePart x D.Ψ 𝔅 F I.G C r w‖ *
            (∑ σ : ShT I.𝔊 C, shWeight σ * badInd σ (forbid r w)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun w _ => mul_add _ _ _
    _ ≤ KL * ((m₀ : ℝ) * D.P.C₀ * Real.log x * Real.exp (-(Real.log x ^ (0.27 : ℝ)))) +
          KL * (((2 * ((J : ℝ) + 1) * D.P.C₀) ^ 2 +
              2 * ((J : ℝ) + 1) * D.P.C₀ * ((m₀ : ℝ) * D.P.C₀ + 4)) * Real.log x ^ 2 *
            (D.P.vlo * Real.exp (Real.log x ^ (0.27 : ℝ)))⁻¹) := add_le_add hfree hcoll
    _ = _ := (mul_add _ _ _).symm

/-! ### Auxiliary estimates -/

/-- The count of [S] and (cor:marked-bound) are powers of `L`. -/
theorem gamma_le (I : Config d D x) (hL1 : 1 ≤ Real.log x) (T : ℕ) (Cm : ℝ) :
    ((∏ _g : Fin I.𝔊.numSmall, Schur.groupConst D.P.vlo D.q₀ T) *
          ∏ _g : Fin I.𝔊.numBig, Schur.groupConst D.P.vlo D.q₀ T) *
        ((∏ _g : Fin I.𝔊.numSmall, Schur.groupConst D.P.vlo D.q₀ T) *
          ∏ _g : Fin I.𝔊.numBig, Schur.groupConst D.P.vlo D.q₀ T) +
      Real.log x ^ Cm * Real.log x ^ Cm ≤
      2 * Real.log x ^
        (4 * (Real.log (Schur.groupConst D.P.vlo D.q₀ T) * D.P.C₀) + 2 * |Cm|) := by
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  have hg1 : 1 ≤ Schur.groupConst D.P.vlo D.q₀ T := Schur.one_le_groupConst _ _ _
  have hgpos : 0 < Schur.groupConst D.P.vlo D.q₀ T := lt_of_lt_of_le zero_lt_one hg1
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = Real.log (Schur.groupConst D.P.vlo D.q₀ T) * D.P.C₀ :=
    ⟨_, rfl⟩
  have hS : ∏ _g : Fin I.𝔊.numSmall, Schur.groupConst D.P.vlo D.q₀ T ≤ Real.log x ^ a := by
    rw [ha]
    exact I.primeGroups.prod_small_le_rpow hL0 (fun _ => Schur.groupConst D.P.vlo D.q₀ T)
      (Real.log (Schur.groupConst D.P.vlo D.q₀ T)) (Real.log_nonneg hg1) (fun _ => hgpos.le)
      (fun _ => (Real.exp_log hgpos).ge)
  have hB : ∏ _g : Fin I.𝔊.numBig, Schur.groupConst D.P.vlo D.q₀ T ≤ Real.log x ^ a := by
    rw [ha]
    exact I.primeGroups.prod_big_le_rpow hL0 (fun _ => Schur.groupConst D.P.vlo D.q₀ T)
      (Real.log (Schur.groupConst D.P.vlo D.q₀ T)) (Real.log_nonneg hg1) (fun _ => hgpos.le)
      (fun _ => (Real.exp_log hgpos).ge)
  have hS0 : 0 ≤ ∏ _g : Fin I.𝔊.numSmall, Schur.groupConst D.P.vlo D.q₀ T :=
    Finset.prod_nonneg fun _ _ => hgpos.le
  have hB0 : 0 ≤ ∏ _g : Fin I.𝔊.numBig, Schur.groupConst D.P.vlo D.q₀ T :=
    Finset.prod_nonneg fun _ _ => hgpos.le
  have hΓ : (∏ _g : Fin I.𝔊.numSmall, Schur.groupConst D.P.vlo D.q₀ T) *
      ∏ _g : Fin I.𝔊.numBig, Schur.groupConst D.P.vlo D.q₀ T ≤ Real.log x ^ (a + a) := by
    rw [Real.rpow_add hL0]
    exact mul_le_mul hS hB hB0 (Real.rpow_nonneg hL0.le _)
  have hΓ0 : 0 ≤ (∏ _g : Fin I.𝔊.numSmall, Schur.groupConst D.P.vlo D.q₀ T) *
      ∏ _g : Fin I.𝔊.numBig, Schur.groupConst D.P.vlo D.q₀ T := mul_nonneg hS0 hB0
  have h1 : ((∏ _g : Fin I.𝔊.numSmall, Schur.groupConst D.P.vlo D.q₀ T) *
        ∏ _g : Fin I.𝔊.numBig, Schur.groupConst D.P.vlo D.q₀ T) *
      ((∏ _g : Fin I.𝔊.numSmall, Schur.groupConst D.P.vlo D.q₀ T) *
        ∏ _g : Fin I.𝔊.numBig, Schur.groupConst D.P.vlo D.q₀ T) ≤
      Real.log x ^ (4 * a + 2 * |Cm|) :=
    calc ((∏ _g : Fin I.𝔊.numSmall, Schur.groupConst D.P.vlo D.q₀ T) *
          ∏ _g : Fin I.𝔊.numBig, Schur.groupConst D.P.vlo D.q₀ T) *
        ((∏ _g : Fin I.𝔊.numSmall, Schur.groupConst D.P.vlo D.q₀ T) *
          ∏ _g : Fin I.𝔊.numBig, Schur.groupConst D.P.vlo D.q₀ T)
        ≤ Real.log x ^ (a + a) * Real.log x ^ (a + a) :=
          mul_le_mul hΓ hΓ hΓ0 (Real.rpow_nonneg hL0.le _)
      _ = Real.log x ^ ((a + a) + (a + a)) := (Real.rpow_add hL0 _ _).symm
      _ ≤ Real.log x ^ (4 * a + 2 * |Cm|) :=
          Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [abs_nonneg Cm])
  have ha0 : 0 ≤ a := by
    rw [ha]
    exact mul_nonneg (Real.log_nonneg hg1) D.P.C₀_pos.le
  have h2 : Real.log x ^ Cm * Real.log x ^ Cm ≤ Real.log x ^ (4 * a + 2 * |Cm|) := by
    rw [← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith [le_abs_self Cm])
  rw [← ha]
  linarith

/-- The positions of a stripped term are at most `x²`: `(c₂ x + 1) D_C ≤ x²`. -/
theorem window_le (I : Config d D x) (hx1 : 1 ≤ x) (hL1 : 1 ≤ Real.log x) {J m₀ : ℕ}
    (C : Fin I.𝔊.numBig → Finset (Fin J)) (hC : ∀ g, (C g).card ≤ m₀)
    (r : AuxList (groupFamily I.𝔊).big C) {c₂ : ℝ} (hc₂ : 0 ≤ c₂)
    (hlog : Real.log (c₂ + 1) +
      (m₀ : ℝ) * D.P.C₀ * Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ) ≤ Real.log x) :
    (c₂ * x + 1) * (tupleProd C r : ℝ) ≤ x ^ 2 := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  have hDpos : (0 : ℝ) < (tupleProd C r : ℝ) :=
    Nat.cast_pos.mpr (Comparison.tupleProd_pos I.primeGroups C r)
  have hlogD : Real.log ((tupleProd C r : ℕ) : ℝ) ≤
      (m₀ : ℝ) * D.P.C₀ * Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ) :=
    Comparison.log_tupleProd_le_const I.primeGroups hL0.le C hC r
  have h1 : (c₂ + 1) * (tupleProd C r : ℝ) ≤ x := by
    rw [← Real.log_le_log_iff (mul_pos (by linarith) hDpos) hx0,
      Real.log_mul (by linarith) hDpos.ne']
    linarith
  calc (c₂ * x + 1) * (tupleProd C r : ℝ)
      ≤ ((c₂ + 1) * x) * (tupleProd C r : ℝ) :=
        mul_le_mul_of_nonneg_right (by linarith) hDpos.le
    _ = x * ((c₂ + 1) * (tupleProd C r : ℝ)) := by ring
    _ ≤ x * x := mul_le_mul_of_nonneg_left h1 hx0.le
    _ = x ^ 2 := (sq x).symm

/-- Every power of `L` is at most `exp(L^{.27})` once `log L ≤ L^{.27}/(|E| + 1)`. -/
theorem exp_threshold {L E : ℝ} (hL : 1 ≤ L)
    (hlog : ‖Real.log L‖ ≤ (|E| + 1)⁻¹ * ‖L ^ (0.27 : ℝ)‖) :
    L ^ E ≤ Real.exp (L ^ (0.27 : ℝ)) := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have h27 : 0 ≤ L ^ (0.27 : ℝ) := Real.rpow_nonneg hL0.le _
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg hL
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlogL, abs_of_nonneg h27] at hlog
  rw [Real.rpow_def_of_pos hL0]
  refine Real.exp_le_exp.mpr ?_
  have hE1 : 0 < |E| + 1 := by positivity
  calc Real.log L * E ≤ Real.log L * |E| := mul_le_mul_of_nonneg_left (le_abs_self E) hlogL
    _ ≤ ((|E| + 1)⁻¹ * L ^ (0.27 : ℝ)) * |E| := mul_le_mul_of_nonneg_right hlog (abs_nonneg E)
    _ = (|E| / (|E| + 1)) * L ^ (0.27 : ℝ) := by ring
    _ ≤ 1 * L ^ (0.27 : ℝ) :=
        mul_le_mul_of_nonneg_right ((div_le_one hE1).mpr (by linarith)) h27
    _ = L ^ (0.27 : ℝ) := one_mul _

/-- The final arithmetic: the pattern cost, the list costs and the two exponentially small errors
give `M L^{-A}`. -/
theorem final_arith {L cK E₁ c₀ A K₀ a vlo cP mC G2 S : ℝ} (hL : 1 ≤ L) (hK₀ : 0 ≤ K₀)
    (hvlo : 0 < vlo) (hcP : 0 ≤ cP) (hmC : 0 ≤ mC) (hG2 : G2 ≤ 2 * L ^ E₁) (hS0 : 0 ≤ S)
    (hS : S ≤ K₀ * L ^ c₀ * (mC * L * Real.exp (-a) + cP * L ^ 2 * (vlo * Real.exp a)⁻¹))
    (hth : L ^ cK * L ^ E₁ * L ^ c₀ * L ^ 2 * L ^ A ≤ Real.exp a) :
    L ^ cK * G2 * S ≤ 2 * K₀ * (mC + cP / vlo) * L ^ (-A) := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hpK : 0 ≤ L ^ cK := Real.rpow_nonneg hL0.le _
  have hpE : 0 ≤ L ^ E₁ := Real.rpow_nonneg hL0.le _
  have hpc : 0 ≤ L ^ c₀ := Real.rpow_nonneg hL0.le _
  have hpA : 0 < L ^ A := Real.rpow_pos_of_pos hL0 _
  have he : 0 < Real.exp a := Real.exp_pos a
  have heneg : Real.exp (-a) = (Real.exp a)⁻¹ := Real.exp_neg a
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have hS' : S ≤ K₀ * L ^ c₀ * (L ^ 2 * (Real.exp a)⁻¹ * (mC + cP / vlo)) := by
    refine hS.trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hK₀ hpc))
    rw [heneg, mul_inv]
    have h1 : mC * L * (Real.exp a)⁻¹ ≤ mC * L ^ 2 * (Real.exp a)⁻¹ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLsq hmC) (inv_nonneg.mpr he.le)
    calc mC * L * (Real.exp a)⁻¹ + cP * L ^ 2 * (vlo⁻¹ * (Real.exp a)⁻¹)
        ≤ mC * L ^ 2 * (Real.exp a)⁻¹ + cP * L ^ 2 * (vlo⁻¹ * (Real.exp a)⁻¹) := by linarith
      _ = L ^ 2 * (Real.exp a)⁻¹ * (mC + cP / vlo) := by ring
  have hprod : L ^ cK * G2 * S ≤
      L ^ cK * (2 * L ^ E₁) * (K₀ * L ^ c₀ * (L ^ 2 * (Real.exp a)⁻¹ * (mC + cP / vlo))) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hG2 hpK) hS' hS0
      (mul_nonneg hpK (mul_nonneg zero_le_two hpE))
  have hLt : L ^ cK * L ^ E₁ * L ^ c₀ * L ^ 2 * (Real.exp a)⁻¹ ≤ (L ^ A)⁻¹ := by
    have h1 : L ^ cK * L ^ E₁ * L ^ c₀ * L ^ 2 ≤ (L ^ A)⁻¹ * Real.exp a := by
      rw [inv_mul_eq_div, le_div_iff₀ hpA]
      exact hth
    calc L ^ cK * L ^ E₁ * L ^ c₀ * L ^ 2 * (Real.exp a)⁻¹
        ≤ ((L ^ A)⁻¹ * Real.exp a) * (Real.exp a)⁻¹ :=
          mul_le_mul_of_nonneg_right h1 (inv_nonneg.mpr he.le)
      _ = (L ^ A)⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ he.ne', mul_one]
  have hC0 : 0 ≤ 2 * K₀ * (mC + cP / vlo) :=
    mul_nonneg (mul_nonneg zero_le_two hK₀) (add_nonneg hmC (div_nonneg hcP hvlo.le))
  calc L ^ cK * G2 * S
      ≤ L ^ cK * (2 * L ^ E₁) * (K₀ * L ^ c₀ * (L ^ 2 * (Real.exp a)⁻¹ * (mC + cP / vlo))) :=
        hprod
    _ = 2 * K₀ * (mC + cP / vlo) * (L ^ cK * L ^ E₁ * L ^ c₀ * L ^ 2 * (Real.exp a)⁻¹) := by
        ring
    _ ≤ 2 * K₀ * (mC + cP / vlo) * (L ^ A)⁻¹ := mul_le_mul_of_nonneg_left hLt hC0
    _ = 2 * K₀ * (mC + cP / vlo) * L ^ (-A) := by rw [Real.rpow_neg hL0.le]

/-- A weighted average of sums bounded by `Sb` is at most `Sb`. -/
theorem sum_weighted_le {ι : Type*} [Fintype ι] (W : Finset ℕ) (a : ι → ℝ) (f : ι → ℕ → ℝ)
    {Sb : ℝ} (ha : ∀ r, 0 ≤ a r) (hsum : ∑ r, a r = 1) (h : ∀ r, ∑ w ∈ W, f r w ≤ Sb) :
    ∑ w ∈ W, ∑ r, f r w * a r ≤ Sb := by
  calc ∑ w ∈ W, ∑ r, f r w * a r = ∑ r, a r * ∑ w ∈ W, f r w := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun w _ => mul_comm _ _
    _ ≤ ∑ r, a r * Sb := Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_left (h r) (ha r)
    _ = Sb := by rw [← Finset.sum_mul, hsum, one_mul]

end General

end Strip

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
