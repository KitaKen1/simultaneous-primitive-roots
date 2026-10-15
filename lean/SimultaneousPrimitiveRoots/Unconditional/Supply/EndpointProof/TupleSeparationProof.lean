module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.TupleUncut

/-!
# The separation of the tuple part

`tupleSeparation : CoefficientBound d → TupleProductBound → TupleEnergy d`
(`[P-06:0717–0737]`): "Separate the rational phase by residue classes modulo `k`. In the tuple
part, `p_s, p_l` are units modulo `k`; on fixed classes for `p_s` and `u`, expand the remaining
test in characters of `p_l` by orthogonality on the units. … Divide all factors into dyads and
Fourier-separate the smooth product cutoff in logarithmic size."

* `first_slot_le`: a prime of the first slot is `≤ x^{1-ε}` when the other slots are nonempty
  (the product of the upper endpoints is `≤ x^{1-ε}`).
* `endpointPolynomial_tupleEndpoint_eq_zero`: if one of the other slots is empty then
  `tupleCoeff = 0` (no tuple `(l_2, …, l_d)`), and the tuple part vanishes.
* `tupleSeparation`: with the uncut coefficient `tupleUncut` of the cut coefficient
  `truncCoeff x tupleCoeff` (bounded by `L^C` everywhere): `TupleProductBound` with the saving
  `A₀ + 4 + 6C₆` for `P = 2^i`, `N_l = 2^j`, the dyad `J` of the first slot (an interval of primes
  in `[N_l, 2N_l]`, `x^ε/2 ≤ N_l ≤ x^{1-ε}`), every character `χ` and the coefficient
  `1_{u ≡ r} c(u)`; the long primes are prime to `k` because `k ≤ L^{C₆} < x^ε`; then
  `tupleUncut_energy`, `tuple_cost_numeric` and `separation_core` with `CF = |C| + 5`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open Filter
open scoped Topology

noncomputable section

/-- A prime of the first slot is at most `x^{1-ε}` when the other slots are nonempty. -/
theorem first_slot_le {d : ℕ} {ε x : ℝ} {S : Fin (d + 1) → Finset ℕ}
    (hS : SlotsAdmissible ε x S) (hne : ∀ i : Fin d, (S i.succ).Nonempty) {l : ℕ}
    (hl : l ∈ S 0) : (l : ℝ) ≤ x ^ (1 - ε) := by
  have hsup1 : ∀ j : Fin d, (1 : ℝ) ≤ (((S j.succ).sup id : ℕ) : ℝ) := by
    intro j
    obtain ⟨ℓ, hℓ⟩ := hne j
    have h3 : 2 ≤ ℓ := (hS.prime j.succ ℓ hℓ).two_le
    have h4 : ℓ ≤ (S j.succ).sup id := Finset.le_sup (f := id) hℓ
    have h5 : 1 ≤ (S j.succ).sup id := by omega
    exact_mod_cast h5
  have h6 : (1 : ℝ) ≤ ∏ j : Fin d, (((S j.succ).sup id : ℕ) : ℝ) :=
    calc (1 : ℝ) = ∏ _j : Fin d, (1 : ℝ) := Finset.prod_const_one.symm
      _ ≤ ∏ j : Fin d, (((S j.succ).sup id : ℕ) : ℝ) :=
          Finset.prod_le_prod (fun _ _ => zero_le_one) (fun j _ => hsup1 j)
  have h4 : l ≤ (S 0).sup id := Finset.le_sup (f := id) hl
  have hup := hS.upper
  rw [Fin.prod_univ_succ] at hup
  calc (l : ℝ) ≤ (((S 0).sup id : ℕ) : ℝ) := Nat.cast_le.mpr h4
    _ ≤ (((S 0).sup id : ℕ) : ℝ) * ∏ j : Fin d, (((S j.succ).sup id : ℕ) : ℝ) :=
        le_mul_of_one_le_right (Nat.cast_nonneg _) h6
    _ ≤ x ^ (1 - ε) := hup

/-- If one of the slots `S_2, …, S_d` is empty, the tuple part vanishes. -/
theorem endpointPolynomial_tupleEndpoint_eq_zero {d : ℕ} (D : EndpointData) (x : ℝ)
    (c : EndpointConfig (d + 1)) (i₀ : Fin c.𝔊.numSmall)
    (hempty : ¬ ∀ i : Fin d, (c.S i.succ).Nonempty) (h : ℤ) (k : ℕ) (τ : ℝ) :
    endpointPolynomial (c.tupleEndpoint D x i₀) c.Y h k τ = 0 := by
  obtain ⟨i, hi⟩ := not_forall.mp hempty
  have hSi : c.S i.succ = ∅ := Finset.not_nonempty_iff_eq_empty.mp hi
  have hcount : ∀ u : ℕ, slotCountRep (tailSlots c.S) u = 0 := by
    intro u
    unfold slotCountRep
    rw [Finset.card_eq_zero]
    refine Finset.eq_empty_of_forall_notMem fun 𝔩 h𝔩 => ?_
    have h1 := Fintype.mem_piFinset.mp (Finset.mem_filter.mp h𝔩).1 i
    have h2 : 𝔩 i ∈ c.S i.succ := h1
    rw [hSi] at h2
    exact absurd h2 (Finset.notMem_empty _)
  have htc : ∀ u : ℕ, c.tupleCoeff D x i₀ u = 0 := by
    intro u
    unfold EndpointConfig.tupleCoeff
    rw [hcount u, Nat.cast_zero, zero_mul]
  have hconv1 : ∀ m : ℕ, primeConv (c.S 0) (c.tupleCoeff D x i₀) m = 0 := by
    intro m
    show ∑ l ∈ (c.S 0).filter (fun l => l ∣ m), c.tupleCoeff D x i₀ (m / l) = 0
    exact Finset.sum_eq_zero fun l _ => htc _
  have hconv2 : ∀ w : ℕ,
      primeConv (c.smallGroup i₀) (primeConv (c.S 0) (c.tupleCoeff D x i₀)) w = 0 := by
    intro w
    show ∑ p ∈ (c.smallGroup i₀).filter (fun p => p ∣ w),
      primeConv (c.S 0) (c.tupleCoeff D x i₀) (w / p) = 0
    exact Finset.sum_eq_zero fun p _ => hconv1 _
  have hU : ∀ w : ℕ, c.tupleEndpoint D x i₀ w = 0 := by
    intro w
    unfold EndpointConfig.tupleEndpoint
    rw [hconv2 w, mul_zero]
  have hsupp : ∀ w, c.tupleEndpoint D x i₀ w ≠ 0 → w ∈ (∅ : Finset ℕ) :=
    fun w hw => absurd (hU w) hw
  rw [endpointPolynomial_eq_sum hsupp, Finset.sum_empty, mul_zero]

/-- **The separation of the tuple part** (`[P-06:0717–0737]`): from the bound for the extracted
coefficients and the tuple products to the energy of the tuple part at high times. -/
theorem tupleSeparation (d : ℕ) :
    CoefficientBound d → TupleProductBound → TupleEnergy d := by
  intro hCB hTP D A hA
  obtain ⟨C, xC, hC⟩ := hCB D
  obtain ⟨A₀, hA₀, hcore⟩ := separation_core D (|C| + 5) A hA
  have hAt : 0 < A₀ + 4 + 6 * D.C₆ := by linarith [D.C₆_pos, hA₀]
  obtain ⟨Bt, -, Mt, xt, hMt⟩ := hTP D.ε D.a₁ D.a₂ D.c₁ D.c₂ D.C₆ C D.ε_pos D.a₁_pos
    D.a₁_le_a₂ D.C₆_pos (A₀ + 4 + 6 * D.C₆) hAt
  obtain ⟨B', hB', M, x₀, hM⟩ := hcore Bt (81 * (D.a₁ / 4) ^ 2 * |Mt|)
  obtain ⟨x₃, hx₃⟩ := Filter.eventually_atTop.mp
    ((eventually_productScale D.a₁ D.a₂ D.c₁ D.c₂ D.C₆ D.a₁_pos).and
      ((Real.tendsto_log_atTop.eventually_ge_atTop 144).and
        (eventually_log_rpow_le (D.C₆ / D.ε + 1))))
  refine ⟨B', hB', |M|, max (max xC xt) (max x₀ x₃), ?_⟩
  intro x hx c hc i₀ k hk hkL h
  have hxC : xC ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxt : xt ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hxx₀ : x₀ ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxx₃ : x₃ ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  obtain ⟨⟨hx1, hL1, hscale⟩, hL144, hLx⟩ := hx₃ x hxx₃
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  by_cases hne : ∀ i : Fin d, (c.S i.succ).Nonempty
  · -- every other slot is nonempty
    have ha₂ : 0 < D.a₂ := lt_of_lt_of_le D.a₁_pos D.a₁_le_a₂
    have h2736 : Real.log x ^ (0.27 : ℝ) ≤ Real.log x ^ (0.36 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    have hPtop : Real.exp (Real.log x ^ (0.27 : ℝ)) / 2 ≤
        Real.exp (Real.log x ^ (0.36 : ℝ)) := by
      have h1 := Real.exp_le_exp.mpr h2736
      have h2 := Real.exp_pos (Real.log x ^ (0.27 : ℝ))
      linarith
    obtain ⟨hY, -, h4aY, -, -⟩ := hscale c.Y hc.scale_ge hc.scale_le _ hPtop le_rfl
    have ha₂Y0 : 0 < D.a₂ * c.Y := mul_pos ha₂ hY
    have ha₁Y0 : 0 < D.a₁ * c.Y := mul_pos D.a₁_pos hY
    have ha₂Yx2 : 2 * (D.a₂ * c.Y) ≤ x ^ (2 : ℝ) := by linarith
    -- the small group
    have hGprime : ∀ p ∈ c.smallGroup i₀, p.Prime := fun p hp =>
      hc.groups.prime (Sum.inl i₀) p hp
    have hG0 : ∀ p ∈ c.smallGroup i₀, p ≠ 0 := fun p hp => (hGprime p hp).ne_zero
    have hGrange : ∀ p ∈ c.smallGroup i₀, Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ (p : ℝ) ∧
        (p : ℝ) ≤ Real.exp (Real.log x ^ (0.36 : ℝ)) := fun p hp =>
      hc.groups.small_range i₀ p hp
    have h36x : Real.exp (Real.log x ^ (0.36 : ℝ)) ≤ x := by
      have h3 : Real.log x ^ (0.36 : ℝ) ≤ Real.log x := by
        have h4 := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num : (0.36 : ℝ) ≤ 1)
        rw [Real.rpow_one] at h4
        exact h4
      calc Real.exp (Real.log x ^ (0.36 : ℝ)) ≤ Real.exp (Real.log x) :=
            Real.exp_le_exp.mpr h3
        _ = x := Real.exp_log hx0
    have hGx : ∀ p ∈ c.smallGroup i₀, (p : ℝ) ≤ x := fun p hp => (hGrange p hp).2.trans h36x
    -- the first slot
    have hSprime : ∀ l ∈ c.S 0, l.Prime := hc.slots.prime 0
    have hS0 : ∀ l ∈ c.S 0, l ≠ 0 := fun l hl => (hSprime l hl).ne_zero
    have hSlow : ∀ l ∈ c.S 0, x ^ D.ε ≤ (l : ℝ) := hc.slots.lower 0
    have hSup : ∀ l ∈ c.S 0, (l : ℝ) ≤ x ^ (1 - D.ε) := fun l hl =>
      first_slot_le hc.slots hne hl
    have h1εx : x ^ (1 - D.ε) ≤ x :=
      calc x ^ (1 - D.ε) ≤ x ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith [D.ε_pos])
        _ = x := Real.rpow_one x
    have hSx : ∀ l ∈ c.S 0, (l : ℝ) ≤ x := fun l hl => (hSup l hl).trans h1εx
    -- the long primes are prime to `k`
    have hLC : Real.log x ^ D.C₆ < x ^ D.ε := by
      have h1 : (Real.log x ^ (D.C₆ / D.ε + 1)) ^ D.ε ≤ x ^ D.ε :=
        Real.rpow_le_rpow (Real.rpow_nonneg hL0.le _) hLx D.ε_pos.le
      rw [← Real.rpow_mul hL0.le] at h1
      have h2 : (D.C₆ / D.ε + 1) * D.ε = D.C₆ + D.ε := by
        rw [add_mul, div_mul_cancel₀ _ D.ε_pos.ne', one_mul]
      rw [h2] at h1
      have h3 : Real.log x ^ D.C₆ < Real.log x ^ (D.C₆ + D.ε) :=
        Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by linarith [D.ε_pos])
      linarith
    have hSk : ∀ l ∈ c.S 0, l.Coprime k := by
      intro l hl
      refine (Nat.Prime.coprime_iff_not_dvd (hSprime l hl)).mpr fun hdvd => ?_
      have h1 : l ≤ k := Nat.le_of_dvd hk hdvd
      have h2 : (l : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr h1
      have h3 := hSlow l hl
      linarith
    -- the coefficient
    have hLC0 : 0 ≤ Real.log x ^ C := Real.rpow_nonneg hL0.le _
    have htc : ∀ u : ℕ, 1 ≤ u → (u : ℝ) ≤ x ^ (2 : ℝ) →
        ‖c.tupleCoeff D x i₀ u‖ ≤ Real.log x ^ C := fun u h1 h2 =>
      (hC x hxC c hc i₀ u h1 h2).2
    have hcc : ∀ u : ℕ, 1 ≤ u → (u : ℝ) ≤ x ^ (2 : ℝ) →
        ‖truncCoeff x (c.tupleCoeff D x i₀) u‖ ≤ Real.log x ^ C := fun u _ _ =>
      norm_truncCoeff_le hLC0 htc u
    -- the reciprocal mass
    have hV : D.P.vlo ≤ reciprocalMass (c.smallGroup i₀) := hc.groups.mass_ge (Sum.inl i₀)
    have hVpos : 0 < reciprocalMass (c.smallGroup i₀) := lt_of_lt_of_le D.P.vlo_pos hV
    have hv : |(reciprocalMass (c.smallGroup i₀))⁻¹| ≤ D.P.vlo⁻¹ := by
      rw [abs_of_nonneg (inv_nonneg.mpr hVpos.le)]
      exact inv_anti₀ D.P.vlo_pos hV
    -- the support of the uncut coefficient
    have hFsupp : ∀ w, tupleUncut (c.smallGroup i₀) (c.S 0)
        (truncCoeff x (c.tupleCoeff D x i₀)) D.a₁ D.a₂ c.Y w ≠ 0 →
        1 ≤ w ∧ D.a₁ / 4 ≤ (w : ℝ) / c.Y ∧ (w : ℝ) / c.Y ≤ 4 * D.a₂ := by
      intro w hw
      obtain ⟨h1, h2, h3⟩ := tupleUncut_support hG0 hS0 _ D.a₁_pos hY hw
      refine ⟨h1, (le_div_iff₀ hY).mpr ?_, (div_le_iff₀ hY).mpr h3⟩
      linarith
    -- its size
    have hFle : ∀ w, ‖tupleUncut (c.smallGroup i₀) (c.S 0)
        (truncCoeff x (c.tupleCoeff D x i₀)) D.a₁ D.a₂ c.Y w‖ ≤ Real.log x ^ (|C| + 5) := by
      intro w
      by_cases hF0 : tupleUncut (c.smallGroup i₀) (c.S 0)
          (truncCoeff x (c.tupleCoeff D x i₀)) D.a₁ D.a₂ c.Y w = 0
      · rw [hF0, norm_zero]
        exact Real.rpow_nonneg hL0.le _
      · obtain ⟨hw1, -, hw3⟩ := tupleUncut_support hG0 hS0 _ D.a₁_pos hY hF0
        have hwx : (w : ℝ) ≤ x ^ (2 : ℝ) := hw3.trans h4aY
        have h1 := norm_tupleUncut_le hGprime hSprime D.a₁_pos hY hx1 hGx hSx hcc hLC0 ha₂Yx2
          hw1 hwx
        have hX : 0 ≤ 4 * Real.log x * (4 * Real.log x * Real.log x ^ C) :=
          mul_nonneg (mul_nonneg (by norm_num) hL0.le)
            (mul_nonneg (mul_nonneg (by norm_num) hL0.le) hLC0)
        have h23 : 2 * Real.log x + 1 ≤ 3 * Real.log x := by linarith
        have h20 : 0 ≤ 2 * Real.log x + 1 := by linarith
        have h30 : 0 ≤ 3 * Real.log x := by linarith
        have h2 : (2 * Real.log x + 1) *
              ((2 * Real.log x + 1) * (4 * Real.log x * (4 * Real.log x * Real.log x ^ C))) ≤
            3 * Real.log x *
              (3 * Real.log x * (4 * Real.log x * (4 * Real.log x * Real.log x ^ C))) :=
          mul_le_mul h23 (mul_le_mul_of_nonneg_right h23 hX) (mul_nonneg h20 hX) h30
        exact (h1.trans h2).trans (box_bound_numeric_three hL144)
    -- it is the double convolution where the cutoff does not vanish
    have hXF : ∀ w : ℕ, c.ψ₁ ((w : ℝ) / c.Y) ≠ 0 →
        primeConv (c.smallGroup i₀) (primeConv (c.S 0) (c.tupleCoeff D x i₀)) w =
          tupleUncut (c.smallGroup i₀) (c.S 0) (truncCoeff x (c.tupleCoeff D x i₀))
            D.a₁ D.a₂ c.Y w := by
      intro w hψ
      have hsup : (w : ℝ) / c.Y ∈ Set.Icc D.a₁ D.a₂ := hc.cutoff_support hψ
      have hw1 : D.a₁ * c.Y ≤ (w : ℝ) := (le_div_iff₀ hY).mp hsup.1
      have hw2 : (w : ℝ) ≤ D.a₂ * c.Y := (div_le_iff₀ hY).mp hsup.2
      have hwpos : (0 : ℝ) < (w : ℝ) := lt_of_lt_of_le ha₁Y0 hw1
      have hw0 : 1 ≤ w := Nat.succ_le_of_lt (Nat.cast_pos.mp hwpos)
      have hwx : (w : ℝ) ≤ x ^ (2 : ℝ) := by linarith
      rw [primeConv_primeConv_truncCoeff (x := x) _ _ _ hw0 hwx]
      exact tupleUncut_eq_primeConv hG0 hS0 _ D.a₁_pos hY hw1 hw2
    -- the uncut polynomial
    have hbd0 : 0 ≤ |Mt| * Real.log x ^ (-(A₀ + 4 + 6 * D.C₆)) :=
      mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hL0.le _)
    have hIrange : ∀ i ∈ (c.smallGroup i₀).image (Nat.log 2),
        Real.exp (Real.log x ^ (0.27 : ℝ)) / 2 ≤ (2 : ℝ) ^ i ∧
          (2 : ℝ) ^ i ≤ Real.exp (Real.log x ^ (0.36 : ℝ)) := by
      intro i hiI
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hiI
      have h1 := two_pow_log_le (hG0 p hp)
      have h2 := lt_two_mul_two_pow_log p
      have h3 := hGrange p hp
      constructor
      · linarith [h3.1]
      · exact h1.trans h3.2
    have hJrange : ∀ j ∈ (c.S 0).image (Nat.log 2),
        x ^ D.ε / 2 ≤ (2 : ℝ) ^ j ∧ (2 : ℝ) ^ j ≤ x ^ (1 - D.ε) := by
      intro j hjJ
      obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hjJ
      have h1 := two_pow_log_le (hS0 l hl)
      have h2 := lt_two_mul_two_pow_log l
      have h3 := hSlow l hl
      constructor
      · linarith
      · exact h1.trans (hSup l hl)
    have hprod : ∀ i ∈ (c.smallGroup i₀).image (Nat.log 2),
        ∀ j ∈ (c.S 0).image (Nat.log 2), ∀ b : ℕ → ℂ, (∀ p, ‖b p‖ ≤ 1) →
        ∀ (χ : DirichletCharacter ℂ k) (r : ℕ),
        HighEnergyLe
          (fun t => normPoly ((2 : ℝ) ^ i)
              (c.smallGroup i₀ ∩ natIcc ((2 : ℝ) ^ i) (2 * (2 : ℝ) ^ i)) b t *
            normPoly ((2 : ℝ) ^ j) ((c.S 0).filter (fun l => Nat.log 2 l = j))
              (fun l => χ (l : ZMod k)) t *
            normPoly (D.a₁ * c.Y / (4 * (2 : ℝ) ^ i * (2 : ℝ) ^ j))
              (tupleRange D.a₁ D.a₂ c.Y i j)
              (fun u => if u ≡ r [MOD k] then truncCoeff x (c.tupleCoeff D x i₀) u else 0) t)
          (Real.log x ^ Bt) (2 * timeBound D x)
          (|Mt| * Real.log x ^ (-(A₀ + 4 + 6 * D.C₆))) := by
      intro i hiI j hjJ b hb χ r
      have hJr : ∀ l ∈ (c.S 0).filter (fun l => Nat.log 2 l = j),
          (2 : ℝ) ^ j ≤ (l : ℝ) ∧ (l : ℝ) ≤ 2 * (2 : ℝ) ^ j := by
        intro l hl
        obtain ⟨hlS, hlog⟩ := Finset.mem_filter.mp hl
        rw [← hlog]
        exact ⟨two_pow_log_le (hS0 l hlS), (lt_two_mul_two_pow_log l).le⟩
      have hcR : ∀ u : ℕ,
          ‖(if u ≡ r [MOD k] then truncCoeff x (c.tupleCoeff D x i₀) u else 0)‖ ≤
            Real.log x ^ C := by
        intro u
        split_ifs
        · exact norm_truncCoeff_le hLC0 htc u
        · rw [norm_zero]
          exact hLC0
      exact (hMt x hxt c.Y hc.scale_ge hc.scale_le (c.smallGroup i₀) hGprime ((2 : ℝ) ^ i)
        (hIrange i hiI).1 (hIrange i hiI).2 b hb ((2 : ℝ) ^ j) (hJrange j hjJ).1
        (hJrange j hjJ).2 ((c.S 0).filter (fun l => Nat.log 2 l = j))
        (isPrimeInterval_filter_log hSprime (hc.slots.interval 0) j) hJr k hk hkL χ
        (fun u => if u ≡ r [MOD k] then truncCoeff x (c.tupleCoeff D x i₀) u else 0) hcR).mono
        le_rfl le_rfl
        (mul_le_mul_of_nonneg_right (le_abs_self Mt) (Real.rpow_nonneg hL0.le _))
    have hE := tupleUncut_energy hk h hG0 hS0 hSk (truncCoeff x (c.tupleCoeff D x i₀))
      D.a₁_pos hY hbd0 hprod
    have hIcard0 : (0 : ℝ) ≤ (((c.smallGroup i₀).image (Nat.log 2)).card : ℝ) :=
      Nat.cast_nonneg _
    have hIcard : (((c.smallGroup i₀).image (Nat.log 2)).card : ℝ) ≤ 3 * Real.log x := by
      have h1 := card_image_log_le (G := c.smallGroup i₀) hx1.le
        fun p hp => ⟨hG0 p hp, hGx p hp⟩
      linarith
    have hJcard0 : (0 : ℝ) ≤ (((c.S 0).image (Nat.log 2)).card : ℝ) := Nat.cast_nonneg _
    have hJcard : (((c.S 0).image (Nat.log 2)).card : ℝ) ≤ 3 * Real.log x := by
      have h1 := card_image_log_le (G := c.S 0) hx1.le fun l hl => ⟨hS0 l hl, hSx l hl⟩
      linarith
    have hQ : HighEnergyLe (endpointPolynomial
        (tupleUncut (c.smallGroup i₀) (c.S 0) (truncCoeff x (c.tupleCoeff D x i₀))
          D.a₁ D.a₂ c.Y) c.Y h k)
        (Real.log x ^ Bt) (2 * timeBound D x)
        (81 * (D.a₁ / 4) ^ 2 * |Mt| * Real.log x ^ (-A₀)) :=
      hE.mono le_rfl le_rfl
        (tuple_cost_numeric hL1 hIcard0 hIcard hJcard0 hJcard (Nat.cast_nonneg k) hkL
          (abs_nonneg Mt))
    have hres := hM x hxx₀ c hc _ hv k h _
      (primeConv (c.smallGroup i₀) (primeConv (c.S 0) (c.tupleCoeff D x i₀)))
      hFsupp hFle hXF hQ
    exact hres.mono le_rfl le_rfl
      (mul_le_mul_of_nonneg_right (le_abs_self M) (Real.rpow_nonneg hL0.le _))
  · -- one of the other slots is empty: the tuple part vanishes
    intro a b hab _
    have h0 : ∀ τ : ℝ,
        ‖endpointPolynomial (c.tupleEndpoint D x i₀) c.Y h k τ‖ ^ 2 = 0 := fun τ => by
      rw [endpointPolynomial_tupleEndpoint_eq_zero D x c i₀ hne h k τ, norm_zero]
      exact zero_pow two_ne_zero
    have hint : ∫ τ in a..b, ‖endpointPolynomial (c.tupleEndpoint D x i₀) c.Y h k τ‖ ^ 2 = 0 :=
      calc ∫ τ in a..b, ‖endpointPolynomial (c.tupleEndpoint D x i₀) c.Y h k τ‖ ^ 2
          = ∫ _τ in a..b, (0 : ℝ) := intervalIntegral.integral_congr fun τ _ => h0 τ
        _ = 0 := intervalIntegral.integral_zero
    rw [hint]
    exact mul_nonneg (abs_nonneg M) (Real.rpow_nonneg hL0.le _)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
