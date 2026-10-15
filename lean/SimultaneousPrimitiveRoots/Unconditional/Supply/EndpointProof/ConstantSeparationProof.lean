module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.SeparationBoxEnergy

/-!
# The separation of the constant part

`constantSeparation : CoefficientBound d → ConstantProductBound d → ConstantEnergy d`
(`[P-06:0717–0737]`): "In the constant part fix classes for `p_s, n`. … Divide all factors into
dyads and Fourier-separate the smooth product cutoff in logarithmic size."

The constant part is `𝒰_const(w) = ψ₁(w/Y) w^{iσ} V⁻¹ ∑_{p ∈ 𝒫_{g_s}, p ∣ w} c(w/p)`,
`c = constCoeff`.

* `constUncut`: the uncut coefficient `F(w) = ∑_i ∑_{p n = w} c(n)`, the sum over the dyads
  `2^i ≤ p < 2^{i+1}` of `𝒫_{g_s}` with `n` in the full range `[a₁Y/(2·2^i), a₂Y/2^i]` of the
  constant products. `constUncut_eq_primeConv`: `F(w) = ∑_{p ∣ w} c(w/p)` for `a₁Y ≤ w ≤ a₂Y`
  (where `ψ₁(w/Y) ≠ 0`); `constUncut_support`: `F` lives on `a₁Y/2 ≤ w ≤ 2a₂Y`;
  `norm_constUncut_le`: `|F(w)| ≤ (2L+1) · 4L · L^C`.
* `constUncut_energy`: the uncut polynomial is the sum over the dyads `i` and the classes `a, b`
  modulo `k` of `(a₁/2) e(hab/k) P_s N`, with `P_s` the polynomial of `1_{dyad i} 1_{p ≡ a}` on
  `𝒫_{g_s} ∩ [2^i, 2·2^i]` and `N` that of `1_{n ≡ b} c(n)`; cost `(#dyads · k²)² (a₁/2)²`.
* `constantSeparation`: `ConstantProductBound` with the saving `A₀ + 2 + 4C₆`
  (`const_cost_numeric`: `#dyads ≤ 3L`, `k ≤ L^{C₆}`), then `separation_core` with
  `CF = |C| + 3`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open Filter
open scoped Topology

noncomputable section

/-- **The uncut coefficient of the constant part**: the sum over the dyads `2^i ≤ p < 2^{i+1}` of
`G` of the box coefficients `∑_{p n = w} c(n)`, `n ∈ [a₁Y/(2·2^i), a₂Y/2^i]`. -/
def constUncut (G : Finset ℕ) (cc : ℕ → ℂ) (a₁ a₂ Y : ℝ) (w : ℕ) : ℂ :=
  ∑ i ∈ G.image (Nat.log 2),
    collapseCoeff (G.filter (fun p => Nat.log 2 p = i))
      (natIcc (a₁ * Y / (2 * (2 : ℝ) ^ i)) (a₂ * Y / (2 : ℝ) ^ i)) (fun _ => 1) cc w

/-- The uncut coefficient lives on `a₁Y/2 ≤ w ≤ 2a₂Y`. -/
theorem constUncut_support {G : Finset ℕ} (hG : ∀ p ∈ G, p ≠ 0) (cc : ℕ → ℂ) {a₁ a₂ Y : ℝ}
    (ha₁ : 0 < a₁) (hY : 0 < Y) {w : ℕ} (hw : constUncut G cc a₁ a₂ Y w ≠ 0) :
    1 ≤ w ∧ a₁ * Y / 2 ≤ (w : ℝ) ∧ (w : ℝ) ≤ 2 * a₂ * Y := by
  unfold constUncut at hw
  obtain ⟨i, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  obtain ⟨y, hy, hyw⟩ := Finset.mem_image.mp (collapseCoeff_ne_zero_mem_image hne)
  have hR : 0 < a₁ * Y / (2 * (2 : ℝ) ^ i) :=
    div_pos (mul_pos ha₁ hY) (mul_pos two_pos (pow_pos two_pos i))
  have h := dyad_box_product hG hR hy
  have hyw' : y.1 * y.2 = w := hyw
  rw [hyw', dyad_scale_lower, dyad_scale_upper] at h
  exact h

/-- **The uncut coefficient is the convolution where the cutoff does not vanish**: for
`a₁Y ≤ w ≤ a₂Y` the cofactor `w/p` of a prime `p` of the dyad `i` lies in the range of the box. -/
theorem constUncut_eq_primeConv {G : Finset ℕ} (hG : ∀ p ∈ G, p ≠ 0) (cc : ℕ → ℂ)
    {a₁ a₂ Y : ℝ} (ha₁ : 0 < a₁) (hY : 0 < Y) {w : ℕ} (hw1 : a₁ * Y ≤ (w : ℝ))
    (hw2 : (w : ℝ) ≤ a₂ * Y) : primeConv G cc w = constUncut G cc a₁ a₂ Y w := by
  have hM : ∀ p ∈ G, p ∣ w → (fun _ : ℕ => cc) (Nat.log 2 p) (w / p) ≠ 0 →
      w / p ∈ (fun i : ℕ => natIcc (a₁ * Y / (2 * (2 : ℝ) ^ i)) (a₂ * Y / (2 : ℝ) ^ i))
        (Nat.log 2 p) := by
    intro p hp hpw _
    exact div_mem_box ha₁ hY (pow_pos two_pos _) hw1 hw2 (two_pow_log_le (hG p hp))
      (lt_two_mul_two_pow_log p).le hpw
  have h1 := sum_boxes_collapse G (fun p hp => Nat.pos_of_ne_zero (hG p hp))
    (fun i : ℕ => natIcc (a₁ * Y / (2 * (2 : ℝ) ^ i)) (a₂ * Y / (2 : ℝ) ^ i))
    (fun _ : ℕ => cc) w hM
  exact h1.symm

/-- The size of the uncut coefficient at `1 ≤ w ≤ x²`. -/
theorem norm_constUncut_le {G : Finset ℕ} (hG : ∀ p ∈ G, p.Prime) {cc : ℕ → ℂ}
    {a₁ a₂ Y x Bc : ℝ} (ha₁ : 0 < a₁) (hY : 0 < Y) (hx : 1 < x) (hGx : ∀ p ∈ G, (p : ℝ) ≤ x)
    (hcc : ∀ u : ℕ, 1 ≤ u → (u : ℝ) ≤ x ^ (2 : ℝ) → ‖cc u‖ ≤ Bc) (hBc : 0 ≤ Bc)
    (ha₂Y : a₂ * Y ≤ x ^ (2 : ℝ)) {w : ℕ} (hw : 1 ≤ w) (hwx : (w : ℝ) ≤ x ^ (2 : ℝ)) :
    ‖constUncut G cc a₁ a₂ Y w‖ ≤ (2 * Real.log x + 1) * (4 * Real.log x * Bc) := by
  have hL0 : 0 < Real.log x := Real.log_pos hx
  have hterm : ∀ i ∈ G.image (Nat.log 2),
      ‖collapseCoeff (G.filter (fun p => Nat.log 2 p = i))
        (natIcc (a₁ * Y / (2 * (2 : ℝ) ^ i)) (a₂ * Y / (2 : ℝ) ^ i)) (fun _ => 1) cc w‖ ≤
        4 * Real.log x * Bc := by
    intro i _
    have hpow0 : (0 : ℝ) < (2 : ℝ) ^ i := pow_pos two_pos i
    have hpow1 : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
    have hR : 0 < a₁ * Y / (2 * (2 : ℝ) ^ i) :=
      div_pos (mul_pos ha₁ hY) (mul_pos two_pos hpow0)
    refine norm_collapseCoeff_one_le (fun l hl => hG l (Finset.mem_filter.mp hl).1)
      (fun u hu => ?_) hBc hw hx hwx
    have hu' := (mem_natIcc_of_pos hR).mp hu
    have hu0 : u ≠ 0 := ne_zero_of_mem_natIcc hR hu
    have hu1 : (u : ℝ) * (2 : ℝ) ^ i ≤ a₂ * Y := (le_div_iff₀ hpow0).mp hu'.2
    have hu2 : (u : ℝ) ≤ (u : ℝ) * (2 : ℝ) ^ i :=
      le_mul_of_one_le_right (Nat.cast_nonneg u) hpow1
    exact hcc u (Nat.one_le_iff_ne_zero.mpr hu0) ((hu2.trans hu1).trans ha₂Y)
  have hcard : ((G.image (Nat.log 2)).card : ℝ) ≤ 2 * Real.log x + 1 :=
    card_image_log_le hx.le fun p hp => ⟨(hG p hp).ne_zero, hGx p hp⟩
  have h0 : 0 ≤ 4 * Real.log x * Bc := mul_nonneg (mul_nonneg (by norm_num) hL0.le) hBc
  unfold constUncut
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hcard h0

/-- **The uncut polynomial of the constant part** from the constant products: cost
`(#dyads · k²)² (a₁/2)²`. -/
theorem constUncut_energy {k : ℕ} (hk : 0 < k) (h : ℤ) {G : Finset ℕ} (hG : ∀ p ∈ G, p ≠ 0)
    (cc : ℕ → ℂ) {a₁ a₂ Y : ℝ} (ha₁ : 0 < a₁) (hY : 0 < Y) {lo hi bd : ℝ} (hbd : 0 ≤ bd)
    (hprod : ∀ i ∈ G.image (Nat.log 2), ∀ b : ℕ → ℂ, (∀ p, ‖b p‖ ≤ 1) → ∀ a : ℕ,
      HighEnergyLe
        (fun t => normPoly ((2 : ℝ) ^ i) (G ∩ natIcc ((2 : ℝ) ^ i) (2 * (2 : ℝ) ^ i)) b t *
          normPoly (a₁ * Y / (2 * (2 : ℝ) ^ i))
            (natIcc (a₁ * Y / (2 * (2 : ℝ) ^ i)) (a₂ * Y / (2 : ℝ) ^ i))
            (fun n => if n ≡ a [MOD k] then cc n else 0) t) lo hi bd) :
    HighEnergyLe (endpointPolynomial (constUncut G cc a₁ a₂ Y) Y h k) lo hi
      (((G.image (Nat.log 2)).card : ℝ) ^ 2 *
        ((k : ℝ) ^ 2 * (((k : ℝ) * (a₁ / 2)) ^ 2 * bd))) := by
  have hpow0 : ∀ i : ℕ, (0 : ℝ) < (2 : ℝ) ^ i := fun i => pow_pos two_pos i
  have hR0 : ∀ i : ℕ, 0 < a₁ * Y / (2 * (2 : ℝ) ^ i) := fun i =>
    div_pos (mul_pos ha₁ hY) (mul_pos two_pos (hpow0 i))
  have hWbox : ∀ i : ℕ, ∀ y ∈ (G.filter (fun p => Nat.log 2 p = i)) ×ˢ
      natIcc (a₁ * Y / (2 * (2 : ℝ) ^ i)) (a₂ * Y / (2 : ℝ) ^ i),
      y.1 * y.2 ∈ Finset.Icc 1 ⌊2 * a₂ * Y⌋₊ := by
    intro i y hy
    have h1 := dyad_box_product hG (hR0 i) hy
    rw [dyad_scale_upper] at h1
    exact Finset.mem_Icc.mpr ⟨h1.1, Nat.le_floor h1.2.2⟩
  have hbox : ∀ i ∈ G.image (Nat.log 2),
      HighEnergyLe (endpointPolynomial (collapseCoeff (G.filter (fun p => Nat.log 2 p = i))
        (natIcc (a₁ * Y / (2 * (2 : ℝ) ^ i)) (a₂ * Y / (2 : ℝ) ^ i)) (fun _ => 1) cc) Y h k)
        lo hi ((k : ℝ) ^ 2 * (((k : ℝ) * (a₁ / 2)) ^ 2 * bd)) := by
    intro i hiI
    have hJ0 : ∀ l ∈ G.filter (fun p => Nat.log 2 p = i), l ≠ 0 := fun l hl =>
      hG l (Finset.mem_filter.mp hl).1
    have hU0 : ∀ u ∈ natIcc (a₁ * Y / (2 * (2 : ℝ) ^ i)) (a₂ * Y / (2 : ℝ) ^ i), u ≠ 0 :=
      fun u hu => ne_zero_of_mem_natIcc (hR0 i) hu
    have hprod' : ∀ a b : ℕ, HighEnergyLe
        (fun t => normPoly ((2 : ℝ) ^ i) (G.filter (fun p => Nat.log 2 p = i))
            (fun l => if l ≡ a [MOD k] then (1 : ℂ) else 0) t *
          normPoly (a₁ * Y / (2 * (2 : ℝ) ^ i))
            (natIcc (a₁ * Y / (2 * (2 : ℝ) ^ i)) (a₂ * Y / (2 : ℝ) ^ i))
            (fun u => if u ≡ b [MOD k] then cc u else 0) t) lo hi bd := by
      intro a b
      have hb1 : ∀ p : ℕ,
          ‖(if Nat.log 2 p = i then (if p ≡ a [MOD k] then (1 : ℂ) else 0) else 0)‖ ≤ 1 := by
        intro p
        split_ifs
        · exact le_of_eq norm_one
        · rw [norm_zero]
          exact zero_le_one
        · rw [norm_zero]
          exact zero_le_one
      have h2 := hprod i hiI
        (fun p => if Nat.log 2 p = i then (if p ≡ a [MOD k] then (1 : ℂ) else 0) else 0) hb1 b
      have hfun : (fun t => normPoly ((2 : ℝ) ^ i) (G.filter (fun p => Nat.log 2 p = i))
            (fun l => if l ≡ a [MOD k] then (1 : ℂ) else 0) t *
          normPoly (a₁ * Y / (2 * (2 : ℝ) ^ i))
            (natIcc (a₁ * Y / (2 * (2 : ℝ) ^ i)) (a₂ * Y / (2 : ℝ) ^ i))
            (fun u => if u ≡ b [MOD k] then cc u else 0) t) =
          fun t => normPoly ((2 : ℝ) ^ i) (G ∩ natIcc ((2 : ℝ) ^ i) (2 * (2 : ℝ) ^ i))
            (fun p => if Nat.log 2 p = i then (if p ≡ a [MOD k] then (1 : ℂ) else 0) else 0) t *
          normPoly (a₁ * Y / (2 * (2 : ℝ) ^ i))
            (natIcc (a₁ * Y / (2 * (2 : ℝ) ^ i)) (a₂ * Y / (2 : ℝ) ^ i))
            (fun u => if u ≡ b [MOD k] then cc u else 0) t :=
        funext fun t => by
          rw [normPoly_dyad_eq G hG i (fun l => if l ≡ a [MOD k] then (1 : ℂ) else 0) t]
      rw [hfun]
      exact h2
    have h1 := box_energy_two hk h hJ0 hU0 (fun _ => 1) cc (hWbox i) Y (hpow0 i).ne'
      (hR0 i).ne' hbd hprod'
    have hscal : (2 : ℝ) ^ i * (a₁ * Y / (2 * (2 : ℝ) ^ i)) / Y = a₁ / 2 := by
      rw [dyad_scale_lower, div_right_comm, mul_div_assoc, div_self hY.ne', mul_one]
    rw [hscal, abs_of_pos (half_pos ha₁)] at h1
    exact h1
  exact sum_boxes_energy (G.image (Nat.log 2))
    (fun i => collapseCoeff (G.filter (fun p => Nat.log 2 p = i))
      (natIcc (a₁ * Y / (2 * (2 : ℝ) ^ i)) (a₂ * Y / (2 : ℝ) ^ i)) (fun _ => 1) cc)
    (fun i _ => collapseCoeff_support _ _ (hWbox i)) Y h k hbox
    (mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) hbd))

/-- The cost of the dyads and of the residue classes:
`(#I)² k² (k a)² M' L^{-(A₀ + 2 + 4C₆)} ≤ 9 a² M' L^{-A₀}` for `#I ≤ 3L`, `k ≤ L^{C₆}`. -/
theorem const_cost_numeric {L C₆ A₀ a M' cI kk : ℝ} (hL : 1 ≤ L) (hcI0 : 0 ≤ cI)
    (hcI : cI ≤ 3 * L) (hk0 : 0 ≤ kk) (hk : kk ≤ L ^ C₆) (hM' : 0 ≤ M') :
    cI ^ 2 * (kk ^ 2 * ((kk * a) ^ 2 * (M' * L ^ (-(A₀ + 2 + 4 * C₆))))) ≤
      9 * a ^ 2 * M' * L ^ (-A₀) := by
  have hL0 : 0 < L := by linarith
  have h1 : cI ^ 2 ≤ 9 * L ^ 2 := by
    have h := pow_le_pow_left₀ hcI0 hcI 2
    calc cI ^ 2 ≤ (3 * L) ^ 2 := h
      _ = 9 * L ^ 2 := by ring
  have h2 : kk ^ 2 ≤ (L ^ C₆) ^ 2 := pow_le_pow_left₀ hk0 hk 2
  have hR0 : 0 ≤ L ^ (-(A₀ + 2 + 4 * C₆)) := Real.rpow_nonneg hL0.le _
  have hk20 : 0 ≤ kk ^ 2 := sq_nonneg _
  have h3 : cI ^ 2 * (kk ^ 2 * kk ^ 2) ≤ 9 * L ^ 2 * ((L ^ C₆) ^ 2 * (L ^ C₆) ^ 2) :=
    mul_le_mul h1 (mul_le_mul h2 h2 hk20 (sq_nonneg _)) (mul_nonneg hk20 hk20)
      (mul_nonneg (by norm_num) (sq_nonneg _))
  have e1 : L ^ 2 * ((L ^ C₆) ^ 2 * (L ^ C₆) ^ 2) * L ^ (-(A₀ + 2 + 4 * C₆)) = L ^ (-A₀) := by
    rw [← Real.rpow_two L, pow_two (L ^ C₆), ← Real.rpow_add hL0, ← Real.rpow_add hL0,
      ← Real.rpow_add hL0, ← Real.rpow_add hL0]
    congr 1
    ring
  have hrest : 0 ≤ a ^ 2 * M' * L ^ (-(A₀ + 2 + 4 * C₆)) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hM') hR0
  calc cI ^ 2 * (kk ^ 2 * ((kk * a) ^ 2 * (M' * L ^ (-(A₀ + 2 + 4 * C₆)))))
      = cI ^ 2 * (kk ^ 2 * kk ^ 2) * (a ^ 2 * M' * L ^ (-(A₀ + 2 + 4 * C₆))) := by ring
    _ ≤ 9 * L ^ 2 * ((L ^ C₆) ^ 2 * (L ^ C₆) ^ 2) *
          (a ^ 2 * M' * L ^ (-(A₀ + 2 + 4 * C₆))) := mul_le_mul_of_nonneg_right h3 hrest
    _ = 9 * a ^ 2 * M' *
          (L ^ 2 * ((L ^ C₆) ^ 2 * (L ^ C₆) ^ 2) * L ^ (-(A₀ + 2 + 4 * C₆))) := by ring
    _ = 9 * a ^ 2 * M' * L ^ (-A₀) := by rw [e1]

/-- **The separation of the constant part** (`[P-06:0717–0737]`): from the bound for the extracted
coefficients and the constant products to the energy of the constant part at high times. -/
theorem constantSeparation (d : ℕ) :
    CoefficientBound d → ConstantProductBound d → ConstantEnergy d := by
  intro hCB hCP D A hA
  obtain ⟨C, xC, hC⟩ := hCB D
  obtain ⟨A₀, hA₀, hcore⟩ := separation_core D (|C| + 3) A hA
  have hAc : 0 < A₀ + 2 + 4 * D.C₆ := by linarith [D.C₆_pos, hA₀]
  obtain ⟨Bc, -, Mc, xc, hMc⟩ := hCP D (A₀ + 2 + 4 * D.C₆) hAc
  obtain ⟨B', hB', M, x₀, hM⟩ := hcore Bc (9 * (D.a₁ / 2) ^ 2 * |Mc|)
  obtain ⟨x₃, hx₃⟩ := Filter.eventually_atTop.mp
    ((eventually_productScale D.a₁ D.a₂ D.c₁ D.c₂ D.C₆ D.a₁_pos).and
      (Real.tendsto_log_atTop.eventually_ge_atTop 12))
  refine ⟨B', hB', M, max (max xC xc) (max x₀ x₃), ?_⟩
  intro x hx c hc i₀ k hk hkL h
  have hxC : xC ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxc : xc ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hxx₀ : x₀ ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxx₃ : x₃ ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  obtain ⟨⟨hx1, hL1, hscale⟩, hL12⟩ := hx₃ x hxx₃
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
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
  have ha₂Yx : D.a₂ * c.Y ≤ x ^ (2 : ℝ) := by linarith
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
    calc Real.exp (Real.log x ^ (0.36 : ℝ)) ≤ Real.exp (Real.log x) := Real.exp_le_exp.mpr h3
      _ = x := Real.exp_log hx0
  have hGx : ∀ p ∈ c.smallGroup i₀, (p : ℝ) ≤ x := fun p hp => (hGrange p hp).2.trans h36x
  have hcc : ∀ u : ℕ, 1 ≤ u → (u : ℝ) ≤ x ^ (2 : ℝ) →
      ‖c.constCoeff D x i₀ u‖ ≤ Real.log x ^ C := fun u h1 h2 =>
    (hC x hxC c hc i₀ u h1 h2).1
  -- the reciprocal mass
  have hV : D.P.vlo ≤ reciprocalMass (c.smallGroup i₀) := hc.groups.mass_ge (Sum.inl i₀)
  have hVpos : 0 < reciprocalMass (c.smallGroup i₀) := lt_of_lt_of_le D.P.vlo_pos hV
  have hv : |(reciprocalMass (c.smallGroup i₀))⁻¹| ≤ D.P.vlo⁻¹ := by
    rw [abs_of_nonneg (inv_nonneg.mpr hVpos.le)]
    exact inv_anti₀ D.P.vlo_pos hV
  -- the support of the uncut coefficient
  have hFsupp : ∀ w, constUncut (c.smallGroup i₀) (c.constCoeff D x i₀) D.a₁ D.a₂ c.Y w ≠ 0 →
      1 ≤ w ∧ D.a₁ / 4 ≤ (w : ℝ) / c.Y ∧ (w : ℝ) / c.Y ≤ 4 * D.a₂ := by
    intro w hw
    obtain ⟨h1, h2, h3⟩ := constUncut_support hG0 _ D.a₁_pos hY hw
    refine ⟨h1, (le_div_iff₀ hY).mpr ?_, (div_le_iff₀ hY).mpr ?_⟩
    · linarith
    · linarith
  -- its size
  have hFle : ∀ w, ‖constUncut (c.smallGroup i₀) (c.constCoeff D x i₀) D.a₁ D.a₂ c.Y w‖ ≤
      Real.log x ^ (|C| + 3) := by
    intro w
    by_cases hF0 : constUncut (c.smallGroup i₀) (c.constCoeff D x i₀) D.a₁ D.a₂ c.Y w = 0
    · rw [hF0, norm_zero]
      exact Real.rpow_nonneg hL0.le _
    · obtain ⟨hw1, -, hw3⟩ := constUncut_support hG0 _ D.a₁_pos hY hF0
      have hwx : (w : ℝ) ≤ x ^ (2 : ℝ) := by linarith
      have h1 := norm_constUncut_le hGprime D.a₁_pos hY hx1 hGx hcc
        (Real.rpow_nonneg hL0.le _) ha₂Yx hw1 hwx
      have h2 : (2 * Real.log x + 1) * (4 * Real.log x * Real.log x ^ C) ≤
          3 * Real.log x * (4 * Real.log x * Real.log x ^ C) :=
        mul_le_mul_of_nonneg_right (by linarith)
          (mul_nonneg (mul_nonneg (by norm_num) hL0.le) (Real.rpow_nonneg hL0.le _))
      exact (h1.trans h2).trans (box_bound_numeric hL12)
  -- it is the convolution where the cutoff does not vanish
  have hXF : ∀ w : ℕ, c.ψ₁ ((w : ℝ) / c.Y) ≠ 0 →
      primeConv (c.smallGroup i₀) (c.constCoeff D x i₀) w =
        constUncut (c.smallGroup i₀) (c.constCoeff D x i₀) D.a₁ D.a₂ c.Y w := by
    intro w hψ
    have hsup : (w : ℝ) / c.Y ∈ Set.Icc D.a₁ D.a₂ := hc.cutoff_support hψ
    exact constUncut_eq_primeConv hG0 _ D.a₁_pos hY ((le_div_iff₀ hY).mp hsup.1)
      ((div_le_iff₀ hY).mp hsup.2)
  -- the uncut polynomial
  have hbd0 : 0 ≤ |Mc| * Real.log x ^ (-(A₀ + 2 + 4 * D.C₆)) :=
    mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hL0.le _)
  have hIrange : ∀ i ∈ (c.smallGroup i₀).image (Nat.log 2),
      Real.exp (Real.log x ^ (0.27 : ℝ)) / 2 ≤ (2 : ℝ) ^ i ∧
        (2 : ℝ) ^ i ≤ Real.exp (Real.log x ^ (0.36 : ℝ)) := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    have h1 := two_pow_log_le (hG0 p hp)
    have h2 := lt_two_mul_two_pow_log p
    have h3 := hGrange p hp
    constructor
    · linarith [h3.1]
    · exact h1.trans h3.2
  have hE := constUncut_energy hk h hG0 (c.constCoeff D x i₀) D.a₁_pos hY hbd0
    (fun i hi b hb a =>
      (hMc x hxc c hc i₀ ((2 : ℝ) ^ i) (hIrange i hi).1 (hIrange i hi).2 b hb k hk hkL a).mono
        le_rfl le_rfl
        (mul_le_mul_of_nonneg_right (le_abs_self Mc) (Real.rpow_nonneg hL0.le _)))
  have hIcard0 : (0 : ℝ) ≤ (((c.smallGroup i₀).image (Nat.log 2)).card : ℝ) :=
    Nat.cast_nonneg _
  have hIcard : (((c.smallGroup i₀).image (Nat.log 2)).card : ℝ) ≤ 3 * Real.log x := by
    have h1 := card_image_log_le (G := c.smallGroup i₀) hx1.le
      fun p hp => ⟨hG0 p hp, hGx p hp⟩
    linarith
  have hQ : HighEnergyLe (endpointPolynomial
      (constUncut (c.smallGroup i₀) (c.constCoeff D x i₀) D.a₁ D.a₂ c.Y) c.Y h k)
      (Real.log x ^ Bc) (2 * timeBound D x)
      (9 * (D.a₁ / 2) ^ 2 * |Mc| * Real.log x ^ (-A₀)) :=
    hE.mono le_rfl le_rfl
      (const_cost_numeric hL1 hIcard0 hIcard (Nat.cast_nonneg k) hkL (abs_nonneg Mc))
  exact hM x hxx₀ c hc _ hv k h _ _ hFsupp hFle hXF hQ

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
