module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.PrimeTuples
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.SquareExceptionsProof

/-!
# The integers that survive the presieve

`siftedDecomposition : SiftedDecomposition` (`[P-07:0230–0240]`). For `z = x^γ`, `0 < γ < 1`,
`J = ⌊2/γ⌋` and a function `F` bounded by `B` on the support of the cutoff,

`∑_{P⁻(u+1) > z, u+1 ≡ b (H)} Φ(u/x) F(u) = ∑_{u+1 prime, ≡ b} Φ(u/x) F(u)
   + ∑_{2 ≤ j ≤ J} (1/j!) ∑_{u+1 ≡ b} Φ(u/x) F(u) #{(p_1, …, p_j) : p_i > z, ∏ p_i = u + 1} + E`,

`|E| ≤ B · sup Φ · #{u ≤ R x : p² ∣ u + 1 for a prime p > z} ≤ η x / L` for large `x`, uniformly in
`H`, `b` and `F`.

* On the support of `u ↦ Φ(u/x)`, `r x ≤ u ≤ R x`, so `z < u + 1 < z^{J+1}` for large `x`
  (`γ < 1` and `γ (J + 1) > 2`).
* The three sums are finite sums over `u < M = ⌊R x⌋ + 1` (`shiftSum_eq_sum`), and the difference
  is the sum of the pointwise defects, which `sift_term_bound` (`Extraction/PrimeTuples.lean`)
  bounds by `sup Φ · |B|` on the `u` with `u + 1` rough and not squarefree, and by `0` elsewhere.
* The exceptional `u` number at most `(M/z) ∑_{d ≤ M} 1/d` (`card_square_multiples_le`), and
  `∑_{d ≤ M} 1/d ≤ C₀ (log 2M)^{A₀}` (`divisorMoments 0`).
* `K L^{a+1} ≤ η x^γ` for large `x` (`isLittleO_log_rpow_rpow_atTop`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

open Filter
open scoped Topology

noncomputable section

/-- `∑_u A_u - ∑_u B_u - ∑_j w_j ∑_u C_{j,u} = ∑_u (A_u - B_u - ∑_j w_j C_{j,u})`. -/
theorem sum_sub_sub_sum_mul_sum (s t : Finset ℕ) (A B : ℕ → ℝ) (w : ℕ → ℝ) (C : ℕ → ℕ → ℝ) :
    ∑ u ∈ s, A u - ∑ u ∈ s, B u - ∑ j ∈ t, w j * ∑ u ∈ s, C j u =
      ∑ u ∈ s, (A u - B u - ∑ j ∈ t, w j * C j u) := by
  have h : ∑ j ∈ t, w j * ∑ u ∈ s, C j u = ∑ u ∈ s, ∑ j ∈ t, w j * C j u := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
  rw [h, Finset.sum_sub_distrib, Finset.sum_sub_distrib]

/-- **The integers that survive the presieve** (`[P-07:0230–0240]`): primes, tuples of primes with
weight `1/j!`, and an error carried by the integers divisible by the square of a prime `> z`. -/
theorem siftedDecomposition : SiftedDecomposition := by
  intro Φ hΦ γ hγ0 hγ1 B η hη
  obtain ⟨R, hR0, hR⟩ := hΦ.exists_upper
  obtain ⟨r, hr0, hr⟩ := hΦ.exists_lower
  obtain ⟨Bφ, hBφ0, hBφ⟩ := hΦ.exists_bound
  obtain ⟨C₀, A₀, hC₀, hmom₀⟩ := (divisorMoments 0).2
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, J = ⌊2 / γ⌋₊ := ⟨_, rfl⟩
  have hc0 : 0 ≤ Bφ * |B| := mul_nonneg hBφ0 (abs_nonneg B)
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = Bφ * |B| * ((R + 1) * (C₀ * (2 : ℝ) ^ max A₀ 0)) := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg hc0 (mul_nonneg (by linarith)
      (mul_nonneg hC₀.le (Real.rpow_nonneg (by norm_num) _)))
  have hK1 : 0 < K + 1 := by linarith
  -- `K L^{a+1} ≤ η x^γ` for large `x`
  have hlim : ∀ᶠ x : ℝ in atTop, K * Real.log x ^ (max A₀ 0 + 1) ≤ η * x ^ γ := by
    have h := (isLittleO_log_rpow_rpow_atTop (max A₀ 0 + 1) hγ0).def
      (show (0 : ℝ) < η * (1 / (K + 1)) from mul_pos hη (one_div_pos.mpr hK1))
    filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hL0 : 0 ≤ Real.log x := (Real.log_pos hx1).le
    have hx0 : 0 ≤ x := by linarith
    have hx' : ‖Real.log x ^ (max A₀ 0 + 1)‖ ≤ η * (1 / (K + 1)) * ‖x ^ γ‖ := hx
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hL0 _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0 _)] at hx'
    calc K * Real.log x ^ (max A₀ 0 + 1)
        ≤ (K + 1) * Real.log x ^ (max A₀ 0 + 1) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hL0 _)
      _ ≤ (K + 1) * (η * (1 / (K + 1)) * x ^ γ) := mul_le_mul_of_nonneg_left hx' hK1.le
      _ = (K + 1) * (1 / (K + 1)) * (η * x ^ γ) := by ring
      _ = η * x ^ γ := by rw [mul_one_div_cancel hK1.ne', one_mul]
  -- `x^γ ≤ r x` for large `x`
  have hlow : ∀ᶠ x : ℝ in atTop, 1 / r ≤ x ^ (1 - γ) :=
    (tendsto_rpow_atTop (by linarith : (0 : ℝ) < 1 - γ)).eventually_ge_atTop _
  filter_upwards [hlim, hlow, eventually_ge_atTop (Real.exp 1 / R),
    eventually_ge_atTop (Real.exp 1), eventually_ge_atTop (2 * (R + 1))]
    with x hlimx hlowx hx1 hx2 hx3
  intro H b F hF
  -- sizes
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp 1
    linarith
  have hxgt1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hx2
    rwa [Real.log_exp] at h
  have hL0 : 0 < Real.log x := by linarith
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = ⌊R * x⌋₊ + 1 := ⟨_, rfl⟩
  have hRx : 0 ≤ R * x := (mul_pos hR0 hx0).le
  have hRxe : Real.exp 1 ≤ R * x := by
    have h := (div_le_iff₀ hR0).mp hx1
    rwa [mul_comm] at h
  have hMgt : R * x < (M : ℝ) := by
    rw [hM, Nat.cast_add, Nat.cast_one]
    exact Nat.lt_floor_add_one _
  have hMe : Real.exp 1 ≤ (M : ℝ) := hRxe.trans hMgt.le
  have hM1 : (1 : ℝ) ≤ (M : ℝ) := by linarith
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  have hMle : (M : ℝ) ≤ (R + 1) * x := by
    have h := Nat.floor_le hRx
    have e : (R + 1) * x = R * x + x := by ring
    rw [hM, Nat.cast_add, Nat.cast_one, e]
    linarith
  have hfloor : ⌊(M : ℝ)⌋₊ = M := Nat.floor_natCast M
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = Real.log (2 * (M : ℝ)) := ⟨_, rfl⟩
  have hℓ1 : 1 ≤ ℓ := by
    have h := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ 2 * (M : ℝ) by linarith)
    rw [Real.log_exp] at h
    rw [hℓ]
    exact h
  have hℓle : ℓ ≤ 2 * Real.log x := by
    have hpos : 0 < 2 * (R + 1) := by linarith
    have h1 : 2 * (M : ℝ) ≤ 2 * (R + 1) * x :=
      calc 2 * (M : ℝ) ≤ 2 * ((R + 1) * x) := by linarith
        _ = 2 * (R + 1) * x := by ring
    have h2 : Real.log (2 * (M : ℝ)) ≤ Real.log (2 * (R + 1) * x) :=
      Real.log_le_log (by linarith) h1
    rw [Real.log_mul hpos.ne' hx0.ne'] at h2
    have h3 : Real.log (2 * (R + 1)) ≤ Real.log x := Real.log_le_log hpos hx3
    rw [hℓ]
    linarith
  -- the sieve level `z = x^γ`
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = x ^ γ := ⟨_, rfl⟩
  have hz1 : 1 < z := by
    rw [hz]
    exact Real.one_lt_rpow hxgt1 hγ0
  have hz0 : 0 < z := by linarith
  rw [← hz] at hlimx
  have hzr : z ≤ r * x := by
    have e : γ + (1 - γ) = 1 := by ring
    have h1 : x ^ γ * x ^ (1 - γ) = x := by
      rw [← Real.rpow_add hx0, e, Real.rpow_one]
    have h2 : z * (1 / r) ≤ x := by
      rw [hz]
      calc x ^ γ * (1 / r) ≤ x ^ γ * x ^ (1 - γ) :=
            mul_le_mul_of_nonneg_left hlowx (Real.rpow_nonneg hx0.le _)
        _ = x := h1
    have h3 : z * (1 / r) * r = z := by
      rw [mul_assoc, one_div_mul_cancel hr0.ne', mul_one]
    calc z = z * (1 / r) * r := h3.symm
      _ ≤ x * r := mul_le_mul_of_nonneg_right h2 hr0.le
      _ = r * x := mul_comm _ _
  have hJ1 : (2 : ℝ) ≤ γ * ((J + 1 : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one (2 / γ)
    rw [← hJ] at h
    have h' : 2 < ((J : ℝ) + 1) * γ := (div_lt_iff₀ hγ0).mp h
    rw [Nat.cast_add, Nat.cast_one, mul_comm]
    exact h'.le
  have hxsq : R * x + 1 < z ^ (J + 1) := by
    have h1 : x ^ (2 : ℝ) ≤ x ^ (γ * ((J + 1 : ℕ) : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hxgt1.le hJ1
    have h2 : x ^ (γ * ((J + 1 : ℕ) : ℝ)) = z ^ (J + 1) := by
      rw [hz, Real.rpow_mul hx0.le, Real.rpow_natCast]
    rw [Real.rpow_two, h2] at h1
    have h3 := mul_le_mul_of_nonneg_right hx3 hx0.le
    nlinarith [h3, hRx, hxgt1, h1]
  -- the positions in the support of the cutoff
  have hrange : ∀ u : ℕ, Φ ((u : ℝ) / x) ≠ 0 →
      z < ((u + 1 : ℕ) : ℝ) ∧ ((u + 1 : ℕ) : ℝ) < z ^ (J + 1) := by
    intro u hu
    have hu1 : r * x ≤ (u : ℝ) := by
      by_contra hcon
      rw [not_le] at hcon
      exact hu (hr _ (by rwa [div_lt_iff₀ hx0]))
    have hu2 : (u : ℝ) ≤ R * x := (hΦ.range_of_ne_zero hR hx0 hu).2
    rw [Nat.cast_add, Nat.cast_one]
    constructor
    · linarith
    · linarith
  -- the exceptional positions
  classical
  obtain ⟨T, hT⟩ : ∃ T : Finset ℕ,
      T = (Finset.range (M + 1)).filter (fun p : ℕ => p.Prime ∧ z < (p : ℝ)) := ⟨_, rfl⟩
  obtain ⟨U, hU⟩ : ∃ U : Finset ℕ,
      U = (Finset.range M).filter (fun u : ℕ => ∃ p ∈ T, p ^ 2 ∣ u + 1) := ⟨_, rfl⟩
  have hUmem : ∀ u ∈ Finset.range M, IsRough z (u + 1) → ¬Squarefree (u + 1) → u ∈ U := by
    intro u hu hr' hsq
    rw [Nat.squarefree_iff_prime_squarefree] at hsq
    obtain ⟨p, hp⟩ := not_forall.mp hsq
    obtain ⟨hpp, hdvd⟩ := _root_.not_imp.mp hp
    have hdvd' : p * p ∣ u + 1 := not_not.mp hdvd
    have hzp : z < (p : ℝ) := hr' p hpp ((dvd_mul_right p p).trans hdvd')
    have huM : u < M := Finset.mem_range.mp hu
    have hple : p * p ≤ u + 1 := Nat.le_of_dvd (Nat.succ_pos u) hdvd'
    have hpM : p ≤ M := (Nat.le_mul_self p).trans (hple.trans (Nat.succ_le_of_lt huM))
    rw [hU]
    refine Finset.mem_filter.mpr ⟨hu, p, ?_, ?_⟩
    · rw [hT]
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpM), hpp, hzp⟩
    · rw [sq]
      exact hdvd'
  have hUcard : (U.card : ℝ) ≤ (M : ℝ) / z * ∑ d ∈ Finset.Icc 1 M, 1 / (d : ℝ) :=
    card_square_multiples_le (T := T) hz0
      (fun p hp => by
        rw [hT] at hp
        exact (Finset.mem_filter.mp hp).2.2.le) M U
      (fun u hu => by
        rw [hU] at hu
        exact ⟨Finset.mem_range.mp (Finset.mem_filter.mp hu).1, (Finset.mem_filter.mp hu).2⟩)
  have hharm : ∑ d ∈ Finset.Icc 1 M, 1 / (d : ℝ) ≤ C₀ * ℓ ^ A₀ := by
    have h := hmom₀ (M : ℝ) hM1
    rw [hfloor, ← hℓ] at h
    refine le_trans (le_of_eq ?_) h
    exact Finset.sum_congr rfl fun d _ => by rw [pow_zero]
  -- the final inequality
  have hℓA : ℓ ^ A₀ ≤ (2 : ℝ) ^ max A₀ 0 * Real.log x ^ max A₀ 0 :=
    calc ℓ ^ A₀ ≤ ℓ ^ max A₀ 0 := Real.rpow_le_rpow_of_exponent_le hℓ1 (le_max_left _ _)
      _ ≤ (2 * Real.log x) ^ max A₀ 0 :=
          Real.rpow_le_rpow (by linarith) hℓle (le_max_right _ _)
      _ = (2 : ℝ) ^ max A₀ 0 * Real.log x ^ max A₀ 0 := Real.mul_rpow (by norm_num) hL0.le
  have hkey : K * Real.log x ^ max A₀ 0 * z⁻¹ ≤ η * (Real.log x)⁻¹ := by
    have hLpow : Real.log x ^ (max A₀ 0 + 1) = Real.log x ^ max A₀ 0 * Real.log x := by
      rw [Real.rpow_add hL0, Real.rpow_one]
    rw [hLpow] at hlimx
    have h := mul_le_mul_of_nonneg_right hlimx
      (mul_nonneg (inv_nonneg.mpr hz0.le) (inv_nonneg.mpr hL0.le))
    have e1 : K * (Real.log x ^ max A₀ 0 * Real.log x) * (z⁻¹ * (Real.log x)⁻¹) =
        K * Real.log x ^ max A₀ 0 * z⁻¹ * (Real.log x * (Real.log x)⁻¹) := by ring
    have e2 : η * z * (z⁻¹ * (Real.log x)⁻¹) = η * (Real.log x)⁻¹ * (z * z⁻¹) := by ring
    rw [e1, e2, mul_inv_cancel₀ hL0.ne', mul_inv_cancel₀ hz0.ne', mul_one, mul_one] at h
    exact h
  have hMz0 : 0 ≤ (M : ℝ) / z := div_nonneg hMnn hz0.le
  have hfinal : (M : ℝ) / z * (C₀ * ℓ ^ A₀) * (Bφ * |B|) ≤ η * (x / Real.log x) :=
    calc (M : ℝ) / z * (C₀ * ℓ ^ A₀) * (Bφ * |B|)
        ≤ (R + 1) * x / z * (C₀ * ((2 : ℝ) ^ max A₀ 0 * Real.log x ^ max A₀ 0)) *
            (Bφ * |B|) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (div_le_div_of_nonneg_right hMle hz0.le)
              (mul_le_mul_of_nonneg_left hℓA hC₀.le)
              (mul_nonneg hC₀.le (Real.rpow_nonneg (by linarith) _))
              (div_nonneg (mul_nonneg (by linarith) hx0.le) hz0.le)) hc0
      _ = x * (K * Real.log x ^ max A₀ 0 * z⁻¹) := by
          rw [hK, div_eq_mul_inv]
          ring
      _ ≤ x * (η * (Real.log x)⁻¹) := mul_le_mul_of_nonneg_left hkey hx0.le
      _ = η * (x / Real.log x) := by
          rw [div_eq_mul_inv]
          ring
  -- the three sums as finite sums over `u < M`
  rw [← hz, ← hJ]
  simp only [shiftSum_eq_sum hR hx0]
  rw [← hM, sum_sub_sub_sum_mul_sum (Finset.range M) (Finset.Icc 2 J)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum (g := fun u => if u ∈ U then Bφ * |B| else 0)
    fun u hu => ?_).trans ?_
  · -- the pointwise defect
    show _ ≤ (if u ∈ U then Bφ * |B| else 0)
    by_cases hΦu : Φ ((u : ℝ) / x) = 0
    · rw [hΦu]
      simp only [zero_mul, ite_self, mul_zero, Finset.sum_const_zero, sub_zero, abs_zero]
      split_ifs
      · exact hc0
      · exact le_rfl
    · obtain ⟨hzv, hlt⟩ := hrange u hΦu
      have hac : |Φ ((u : ℝ) / x) * F u| ≤ Bφ * |B| := by
        rw [abs_mul, abs_of_nonneg (hΦ.nonneg _)]
        exact mul_le_mul (hBφ _) ((hF u hΦu).trans (le_abs_self B)) (abs_nonneg _) hBφ0
      refine sift_term_bound hz1 hzv hlt (cls := u + 1 ≡ b [MOD H])
        (a := Φ ((u : ℝ) / x) * F u) ?_ ?_
        (fun h => if_pos h) (fun h => if_neg h)
        (fun h => if_pos h) (fun h => if_neg h)
        (fun h j => (if_pos h).trans (mul_assoc _ _ _).symm)
        (fun h j => if_neg h)
      · split_ifs
        · exact hc0
        · exact le_rfl
      · intro hr' hsq
        rw [if_pos (hUmem u hu hr' hsq)]
        exact hac
  · -- the number of exceptional positions
    calc ∑ u ∈ Finset.range M, (if u ∈ U then Bφ * |B| else 0)
        = ∑ _u ∈ Finset.range M ∩ U, Bφ * |B| := Finset.sum_ite_mem _ _ _
      _ = ((Finset.range M ∩ U).card : ℝ) * (Bφ * |B|) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (U.card : ℝ) * (Bφ * |B|) :=
          mul_le_mul_of_nonneg_right
            (Nat.cast_le.mpr (Finset.card_le_card Finset.inter_subset_right)) hc0
      _ ≤ (M : ℝ) / z * (C₀ * ℓ ^ A₀) * (Bφ * |B|) :=
          mul_le_mul_of_nonneg_right
            (hUcard.trans (mul_le_mul_of_nonneg_left hharm hMz0)) hc0
      _ ≤ η * (x / Real.log x) := hfinal

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
