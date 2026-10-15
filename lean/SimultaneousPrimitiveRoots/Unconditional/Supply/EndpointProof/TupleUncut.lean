module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.TupleSeparationTools

/-!
# The uncut coefficient of the tuple part

The tuple part is `𝒰_tuple(w) = ψ₁(w/Y) w^{iσ} V⁻¹ ∑_{p ∈ 𝒫_{g_s}} ∑_{l ∈ S₁, p l ∣ w} c(w/(p l))`,
`c = tupleCoeff` (`[P-06:0705–0712]`). "Divide all factors into dyads" (`[P-06:0723]`):

* `tupleRange a₁ a₂ Y i j = [a₁Y/(4·2^i·2^j), a₂Y/(2^i·2^j)]`: the range of `u` in the box of
  the dyads `2^i ≤ p < 2^{i+1}`, `2^j ≤ l < 2^{j+1}`; it is the range of the polynomial `R` of
  `TupleProductBound` for `P = 2^i`, `N_l = 2^j`.
* `tupleBox`, `tupleUncut`: the box coefficient `∑_{p l u = w} c(u)` and the uncut coefficient
  `F(w) = ∑_{i,j} (box)`.
* `tupleUncut_support`: `F` lives on `a₁Y/4 ≤ w ≤ 4a₂Y`; `tupleUncut_eq_primeConv`: for
  `a₁Y ≤ w ≤ a₂Y` (where `ψ₁(w/Y) ≠ 0`), `F(w) = ∑_{p ∣ w} ∑_{l ∣ w/p} c(w/(pl))`;
  `norm_tupleUncut_le`: `|F(w)| ≤ (2L+1)² (4L)² L^C` on `1 ≤ w ≤ x²`.
* `tupleUncut_energy`: the uncut polynomial from the tuple products; cost
  `(#dyads_p · #dyads_l · k² · k)² (a₁/4)²`.
* `truncCoeff`: the coefficient cut to `1 ≤ u ≤ x²` (so that it is bounded everywhere, as
  `TupleProductBound` requires); `isPrimeInterval_filter_log`: a dyad of a slot is an interval of
  primes.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

noncomputable section

/-! ### The uncut coefficient -/

/-- The range of the third factor in the box of the dyads `i` (small prime) and `j` (long prime):
`[a₁Y/(4·2^i·2^j), a₂Y/(2^i·2^j)]`. -/
def tupleRange (a₁ a₂ Y : ℝ) (i j : ℕ) : Finset ℕ :=
  natIcc (a₁ * Y / (4 * (2 : ℝ) ^ i * (2 : ℝ) ^ j)) (a₂ * Y / ((2 : ℝ) ^ i * (2 : ℝ) ^ j))

/-- The coefficient `∑_{p l u = w} c(u)` of the box with `p` in the dyad `i` of `G`, `l` in the
dyad `j` of `S` and `u ∈ U`. -/
def tupleBox (G S : Finset ℕ) (cc : ℕ → ℂ) (U : Finset ℕ) (i j : ℕ) (w : ℕ) : ℂ :=
  collapseCoeff (G.filter (fun p => Nat.log 2 p = i))
    (((S.filter (fun l => Nat.log 2 l = j)) ×ˢ U).image (fun y : ℕ × ℕ => y.1 * y.2))
    (fun _ => 1) (collapseCoeff (S.filter (fun l => Nat.log 2 l = j)) U (fun _ => 1) cc) w

/-- **The uncut coefficient of the tuple part**: the sum of the box coefficients over the dyads of
`G` and of `S`. -/
def tupleUncut (G S : Finset ℕ) (cc : ℕ → ℂ) (a₁ a₂ Y : ℝ) (w : ℕ) : ℂ :=
  ∑ i ∈ G.image (Nat.log 2), ∑ j ∈ S.image (Nat.log 2),
    tupleBox G S cc (tupleRange a₁ a₂ Y i j) i j w

theorem tupleRange_lower_pos {a₁ Y : ℝ} (ha₁ : 0 < a₁) (hY : 0 < Y) (i j : ℕ) :
    0 < a₁ * Y / (4 * (2 : ℝ) ^ i * (2 : ℝ) ^ j) :=
  div_pos (mul_pos ha₁ hY)
    (mul_pos (mul_pos (by norm_num) (pow_pos two_pos i)) (pow_pos two_pos j))

/-- A box coefficient lives on the products of the box. -/
theorem tupleBox_ne_zero {G S : Finset ℕ} {cc : ℕ → ℂ} {U : Finset ℕ} {i j w : ℕ}
    (hw : tupleBox G S cc U i j w ≠ 0) :
    ∃ p ∈ G.filter (fun p => Nat.log 2 p = i), ∃ l ∈ S.filter (fun l => Nat.log 2 l = j),
      ∃ u ∈ U, p * (l * u) = w := by
  unfold tupleBox at hw
  obtain ⟨x, hx, hxw⟩ := Finset.mem_image.mp (collapseCoeff_ne_zero_mem_image hw)
  obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx
  obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx2
  obtain ⟨hy1, hy2⟩ := Finset.mem_product.mp hy
  have hyx' : y.1 * y.2 = x.2 := hyx
  have hxw' : x.1 * x.2 = w := hxw
  exact ⟨x.1, hx1, y.1, hy1, y.2, hy2, by rw [hyx', hxw']⟩

/-- The uncut coefficient lives on `a₁Y/4 ≤ w ≤ 4a₂Y`. -/
theorem tupleUncut_support {G S : Finset ℕ} (hG : ∀ p ∈ G, p ≠ 0) (hS : ∀ l ∈ S, l ≠ 0)
    (cc : ℕ → ℂ) {a₁ a₂ Y : ℝ} (ha₁ : 0 < a₁) (hY : 0 < Y) {w : ℕ}
    (hw : tupleUncut G S cc a₁ a₂ Y w ≠ 0) :
    1 ≤ w ∧ a₁ * Y / 4 ≤ (w : ℝ) ∧ (w : ℝ) ≤ 4 * a₂ * Y := by
  unfold tupleUncut at hw
  obtain ⟨i, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  obtain ⟨j, -, hne'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  obtain ⟨p, hp, l, hl, u, hu, hplu⟩ := tupleBox_ne_zero hne'
  have h := dyad_box_product_three hG hS (tupleRange_lower_pos ha₁ hY i j) hp hl hu
  rw [hplu, dyad2_scale_lower, dyad2_scale_upper] at h
  exact h

/-- **The uncut coefficient is the double convolution where the cutoff does not vanish**: for
`a₁Y ≤ w ≤ a₂Y`, `p ∣ w` in the dyad `i` and `l ∣ w/p` in the dyad `j`, the cofactor `w/(pl)`
lies in the range of the box. -/
theorem tupleUncut_eq_primeConv {G S : Finset ℕ} (hG : ∀ p ∈ G, p ≠ 0) (hS : ∀ l ∈ S, l ≠ 0)
    (cc : ℕ → ℂ) {a₁ a₂ Y : ℝ} (ha₁ : 0 < a₁) (hY : 0 < Y) {w : ℕ}
    (hw1 : a₁ * Y ≤ (w : ℝ)) (hw2 : (w : ℝ) ≤ a₂ * Y) :
    primeConv G (primeConv S cc) w = tupleUncut G S cc a₁ a₂ Y w := by
  have h1 : ∀ j ∈ S.image (Nat.log 2),
      ∑ i ∈ G.image (Nat.log 2), tupleBox G S cc (tupleRange a₁ a₂ Y i j) i j w =
        ∑ p ∈ G.filter (fun p => p ∣ w),
          collapseCoeff (S.filter (fun l => Nat.log 2 l = j))
            (tupleRange a₁ a₂ Y (Nat.log 2 p) j) (fun _ => 1) cc (w / p) := by
    intro j _
    exact sum_boxes_collapse G (fun p hp => Nat.pos_of_ne_zero (hG p hp))
      (fun i => ((S.filter (fun l => Nat.log 2 l = j)) ×ˢ tupleRange a₁ a₂ Y i j).image
        (fun y : ℕ × ℕ => y.1 * y.2))
      (fun i => collapseCoeff (S.filter (fun l => Nat.log 2 l = j)) (tupleRange a₁ a₂ Y i j)
        (fun _ => 1) cc) w
      (fun p _ _ hne => collapseCoeff_ne_zero_mem_image hne)
  have h2 : ∀ p ∈ G.filter (fun p => p ∣ w),
      ∑ j ∈ S.image (Nat.log 2), collapseCoeff (S.filter (fun l => Nat.log 2 l = j))
        (tupleRange a₁ a₂ Y (Nat.log 2 p) j) (fun _ => 1) cc (w / p) =
        primeConv S cc (w / p) := by
    intro p hp
    obtain ⟨hpG, hpw⟩ := Finset.mem_filter.mp hp
    have hM' : ∀ l ∈ S, l ∣ w / p → (fun _ : ℕ => cc) (Nat.log 2 l) (w / p / l) ≠ 0 →
        w / p / l ∈ (fun j : ℕ => tupleRange a₁ a₂ Y (Nat.log 2 p) j) (Nat.log 2 l) := by
      intro l hl hlw _
      exact div_div_mem_box ha₁ hY (pow_pos two_pos _) (pow_pos two_pos _) hw1 hw2
        (two_pow_log_le (hG p hpG)) (lt_two_mul_two_pow_log p).le hpw
        (two_pow_log_le (hS l hl)) (lt_two_mul_two_pow_log l).le hlw
    exact sum_boxes_collapse S (fun l hl => Nat.pos_of_ne_zero (hS l hl))
      (fun j : ℕ => tupleRange a₁ a₂ Y (Nat.log 2 p) j) (fun _ : ℕ => cc) (w / p) hM'
  unfold tupleUncut
  rw [Finset.sum_comm, Finset.sum_congr rfl h1, Finset.sum_comm, Finset.sum_congr rfl h2]
  rfl

/-! ### Its size -/

/-- The size of a box coefficient at `1 ≤ w ≤ x²`: at most `4L · 4L` times the bound for `c`. -/
theorem norm_tupleBox_le {G S : Finset ℕ} (hG : ∀ p ∈ G, p.Prime) (hS : ∀ l ∈ S, l.Prime)
    {cc : ℕ → ℂ} {U : Finset ℕ} {x Bc : ℝ} (hx : 1 < x) (hBc : 0 ≤ Bc)
    (hcu : ∀ u ∈ U, ‖cc u‖ ≤ Bc) (i j : ℕ)
    (hm : ∀ l ∈ S.filter (fun l => Nat.log 2 l = j), ∀ u ∈ U,
      1 ≤ l * u ∧ ((l * u : ℕ) : ℝ) ≤ x ^ (2 : ℝ)) {w : ℕ} (hw : 1 ≤ w)
    (hwx : (w : ℝ) ≤ x ^ (2 : ℝ)) :
    ‖tupleBox G S cc U i j w‖ ≤ 4 * Real.log x * (4 * Real.log x * Bc) := by
  have hL0 : 0 < Real.log x := Real.log_pos hx
  have hB1 : 0 ≤ 4 * Real.log x * Bc := mul_nonneg (mul_nonneg (by norm_num) hL0.le) hBc
  have hd : ∀ m ∈ ((S.filter (fun l => Nat.log 2 l = j)) ×ˢ U).image
      (fun y : ℕ × ℕ => y.1 * y.2),
      ‖collapseCoeff (S.filter (fun l => Nat.log 2 l = j)) U (fun _ => 1) cc m‖ ≤
        4 * Real.log x * Bc := by
    intro m hm'
    obtain ⟨y, hy, hym⟩ := Finset.mem_image.mp hm'
    obtain ⟨hy1, hy2⟩ := Finset.mem_product.mp hy
    have hym' : y.1 * y.2 = m := hym
    have h1 := hm y.1 hy1 y.2 hy2
    rw [hym'] at h1
    exact norm_collapseCoeff_one_le (fun l hl => hS l (Finset.mem_filter.mp hl).1) hcu hBc h1.1
      hx h1.2
  unfold tupleBox
  exact norm_collapseCoeff_one_le (fun p hp => hG p (Finset.mem_filter.mp hp).1) hd hB1 hw hx hwx

/-- The size of the uncut coefficient at `1 ≤ w ≤ x²`. -/
theorem norm_tupleUncut_le {G S : Finset ℕ} (hG : ∀ p ∈ G, p.Prime) (hS : ∀ l ∈ S, l.Prime)
    {cc : ℕ → ℂ} {a₁ a₂ Y x Bc : ℝ} (ha₁ : 0 < a₁) (hY : 0 < Y) (hx : 1 < x)
    (hGx : ∀ p ∈ G, (p : ℝ) ≤ x) (hSx : ∀ l ∈ S, (l : ℝ) ≤ x)
    (hcc : ∀ u : ℕ, 1 ≤ u → (u : ℝ) ≤ x ^ (2 : ℝ) → ‖cc u‖ ≤ Bc) (hBc : 0 ≤ Bc)
    (ha₂Y : 2 * (a₂ * Y) ≤ x ^ (2 : ℝ)) {w : ℕ} (hw : 1 ≤ w) (hwx : (w : ℝ) ≤ x ^ (2 : ℝ)) :
    ‖tupleUncut G S cc a₁ a₂ Y w‖ ≤
      (2 * Real.log x + 1) *
        ((2 * Real.log x + 1) * (4 * Real.log x * (4 * Real.log x * Bc))) := by
  have hL0 : 0 < Real.log x := Real.log_pos hx
  have hB2 : 0 ≤ 4 * Real.log x * (4 * Real.log x * Bc) :=
    mul_nonneg (mul_nonneg (by norm_num) hL0.le)
      (mul_nonneg (mul_nonneg (by norm_num) hL0.le) hBc)
  have hterm : ∀ i ∈ G.image (Nat.log 2), ∀ j ∈ S.image (Nat.log 2),
      ‖tupleBox G S cc (tupleRange a₁ a₂ Y i j) i j w‖ ≤
        4 * Real.log x * (4 * Real.log x * Bc) := by
    intro i _ j _
    have hpowi : (0 : ℝ) < (2 : ℝ) ^ i := pow_pos two_pos i
    have hpowj : (0 : ℝ) < (2 : ℝ) ^ j := pow_pos two_pos j
    have hpow1i : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
    have hpow1j : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hR := tupleRange_lower_pos ha₁ hY i j
    have hub : ∀ u ∈ tupleRange a₁ a₂ Y i j,
        u ≠ 0 ∧ (u : ℝ) * ((2 : ℝ) ^ i * (2 : ℝ) ^ j) ≤ a₂ * Y := by
      intro u hu
      exact ⟨ne_zero_of_mem_natIcc hR hu,
        (le_div_iff₀ (mul_pos hpowi hpowj)).mp ((mem_natIcc_of_pos hR).mp hu).2⟩
    have hcu : ∀ u ∈ tupleRange a₁ a₂ Y i j, ‖cc u‖ ≤ Bc := by
      intro u hu
      obtain ⟨hu0, hu1⟩ := hub u hu
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ i * (2 : ℝ) ^ j :=
        one_le_mul_of_one_le_of_one_le hpow1i hpow1j
      have h2 : (u : ℝ) ≤ (u : ℝ) * ((2 : ℝ) ^ i * (2 : ℝ) ^ j) :=
        le_mul_of_one_le_right (Nat.cast_nonneg u) h1
      have h3 : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg u
      have h4 : (u : ℝ) ≤ x ^ (2 : ℝ) := by linarith
      exact hcc u (Nat.one_le_iff_ne_zero.mpr hu0) h4
    have hm : ∀ l ∈ S.filter (fun l => Nat.log 2 l = j), ∀ u ∈ tupleRange a₁ a₂ Y i j,
        1 ≤ l * u ∧ ((l * u : ℕ) : ℝ) ≤ x ^ (2 : ℝ) := by
      intro l hl u hu
      obtain ⟨hlS, hlog⟩ := Finset.mem_filter.mp hl
      obtain ⟨hu0, hu1⟩ := hub u hu
      have hl0 : l ≠ 0 := (hS l hlS).ne_zero
      have hl2 : (l : ℝ) ≤ 2 * (2 : ℝ) ^ j := by
        rw [← hlog]
        exact (lt_two_mul_two_pow_log l).le
      have hu00 : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg u
      have h1 : (l : ℝ) * (u : ℝ) ≤ 2 * (2 : ℝ) ^ j * (u : ℝ) :=
        mul_le_mul_of_nonneg_right hl2 hu00
      have h2 : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ i * (2 : ℝ) ^ j :=
        le_mul_of_one_le_left hpowj.le hpow1i
      have h3 : (u : ℝ) * (2 : ℝ) ^ j ≤ (u : ℝ) * ((2 : ℝ) ^ i * (2 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left h2 hu00
      refine ⟨Nat.succ_le_of_lt (Nat.mul_pos (Nat.pos_of_ne_zero hl0)
        (Nat.pos_of_ne_zero hu0)), ?_⟩
      rw [Nat.cast_mul]
      linarith
    exact norm_tupleBox_le hG hS hx hBc hcu i j hm hw hwx
  have hcardG : ((G.image (Nat.log 2)).card : ℝ) ≤ 2 * Real.log x + 1 :=
    card_image_log_le hx.le fun p hp => ⟨(hG p hp).ne_zero, hGx p hp⟩
  have hcardS : ((S.image (Nat.log 2)).card : ℝ) ≤ 2 * Real.log x + 1 :=
    card_image_log_le hx.le fun l hl => ⟨(hS l hl).ne_zero, hSx l hl⟩
  have hinner : ∀ i ∈ G.image (Nat.log 2),
      ‖∑ j ∈ S.image (Nat.log 2), tupleBox G S cc (tupleRange a₁ a₂ Y i j) i j w‖ ≤
        (2 * Real.log x + 1) * (4 * Real.log x * (4 * Real.log x * Bc)) := by
    intro i hiI
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum (hterm i hiI)).trans ?_)
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcardS hB2
  have h2L : 0 ≤ 2 * Real.log x + 1 := by linarith
  unfold tupleUncut
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hinner).trans ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right hcardG (mul_nonneg h2L hB2)

/-! ### Its polynomial -/

/-- **The uncut polynomial of the tuple part** from the tuple products: cost
`(#dyads_p · #dyads_l · k² · k)² (a₁/4)²`. -/
theorem tupleUncut_energy {k : ℕ} (hk : 0 < k) (h : ℤ) {G S : Finset ℕ} (hG : ∀ p ∈ G, p ≠ 0)
    (hS : ∀ l ∈ S, l ≠ 0) (hSk : ∀ l ∈ S, l.Coprime k) (cc : ℕ → ℂ) {a₁ a₂ Y : ℝ}
    (ha₁ : 0 < a₁) (hY : 0 < Y) {lo hi bd : ℝ} (hbd : 0 ≤ bd)
    (hprod : ∀ i ∈ G.image (Nat.log 2), ∀ j ∈ S.image (Nat.log 2), ∀ b : ℕ → ℂ,
      (∀ p, ‖b p‖ ≤ 1) → ∀ (χ : DirichletCharacter ℂ k) (r : ℕ),
      HighEnergyLe
        (fun t => normPoly ((2 : ℝ) ^ i) (G ∩ natIcc ((2 : ℝ) ^ i) (2 * (2 : ℝ) ^ i)) b t *
          normPoly ((2 : ℝ) ^ j) (S.filter (fun l => Nat.log 2 l = j))
            (fun l => χ (l : ZMod k)) t *
          normPoly (a₁ * Y / (4 * (2 : ℝ) ^ i * (2 : ℝ) ^ j)) (tupleRange a₁ a₂ Y i j)
            (fun u => if u ≡ r [MOD k] then cc u else 0) t) lo hi bd) :
    HighEnergyLe (endpointPolynomial (tupleUncut G S cc a₁ a₂ Y) Y h k) lo hi
      (((G.image (Nat.log 2)).card : ℝ) ^ 2 * (((S.image (Nat.log 2)).card : ℝ) ^ 2 *
        ((k : ℝ) ^ 2 * ((k : ℝ) ^ 2 * (((k : ℝ) * (a₁ / 4)) ^ 2 * bd))))) := by
  have hpow0 : ∀ i : ℕ, (0 : ℝ) < (2 : ℝ) ^ i := fun i => pow_pos two_pos i
  have hWbox : ∀ i j : ℕ, ∀ p ∈ G.filter (fun p => Nat.log 2 p = i),
      ∀ l ∈ S.filter (fun l => Nat.log 2 l = j), ∀ u ∈ tupleRange a₁ a₂ Y i j,
      p * (l * u) ∈ Finset.Icc 1 ⌊4 * a₂ * Y⌋₊ := by
    intro i j p hp l hl u hu
    have h1 := dyad_box_product_three hG hS (tupleRange_lower_pos ha₁ hY i j) hp hl hu
    rw [dyad2_scale_upper] at h1
    exact Finset.mem_Icc.mpr ⟨h1.1, Nat.le_floor h1.2.2⟩
  have hsupp : ∀ i j : ℕ, ∀ w, tupleBox G S cc (tupleRange a₁ a₂ Y i j) i j w ≠ 0 →
      w ∈ Finset.Icc 1 ⌊4 * a₂ * Y⌋₊ := by
    intro i j w hw
    obtain ⟨p, hp, l, hl, u, hu, hplu⟩ := tupleBox_ne_zero hw
    rw [← hplu]
    exact hWbox i j p hp l hl u hu
  have hbox : ∀ i ∈ G.image (Nat.log 2), ∀ j ∈ S.image (Nat.log 2),
      HighEnergyLe (endpointPolynomial (tupleBox G S cc (tupleRange a₁ a₂ Y i j) i j) Y h k)
        lo hi ((k : ℝ) ^ 2 * ((k : ℝ) ^ 2 * (((k : ℝ) * (a₁ / 4)) ^ 2 * bd))) := by
    intro i hiI j hjJ
    have hG0 : ∀ p ∈ G.filter (fun p => Nat.log 2 p = i), p ≠ 0 := fun p hp =>
      hG p (Finset.mem_filter.mp hp).1
    have hJ0 : ∀ l ∈ S.filter (fun l => Nat.log 2 l = j), l ≠ 0 := fun l hl =>
      hS l (Finset.mem_filter.mp hl).1
    have hJk : ∀ l ∈ S.filter (fun l => Nat.log 2 l = j), l.Coprime k := fun l hl =>
      hSk l (Finset.mem_filter.mp hl).1
    have hR := tupleRange_lower_pos ha₁ hY i j
    have hU0 : ∀ u ∈ tupleRange a₁ a₂ Y i j, u ≠ 0 := fun u hu => ne_zero_of_mem_natIcc hR hu
    have hprod' : ∀ (a b : ℕ) (χ : DirichletCharacter ℂ k), HighEnergyLe
        (fun t => normPoly ((2 : ℝ) ^ i) (G.filter (fun p => Nat.log 2 p = i))
            (fun p => if p ≡ a [MOD k] then (1 : ℂ) else 0) t *
          normPoly ((2 : ℝ) ^ j) (S.filter (fun l => Nat.log 2 l = j))
            (fun l => χ (l : ZMod k)) t *
          normPoly (a₁ * Y / (4 * (2 : ℝ) ^ i * (2 : ℝ) ^ j)) (tupleRange a₁ a₂ Y i j)
            (fun u => if u ≡ b [MOD k] then cc u else 0) t) lo hi bd := by
      intro a b χ
      have hb1 : ∀ p : ℕ,
          ‖(if Nat.log 2 p = i then (if p ≡ a [MOD k] then (1 : ℂ) else 0) else 0)‖ ≤ 1 := by
        intro p
        split_ifs
        · exact le_of_eq norm_one
        · rw [norm_zero]
          exact zero_le_one
        · rw [norm_zero]
          exact zero_le_one
      have h2 := hprod i hiI j hjJ
        (fun p => if Nat.log 2 p = i then (if p ≡ a [MOD k] then (1 : ℂ) else 0) else 0) hb1 χ b
      have hfun : (fun t => normPoly ((2 : ℝ) ^ i) (G.filter (fun p => Nat.log 2 p = i))
            (fun p => if p ≡ a [MOD k] then (1 : ℂ) else 0) t *
          normPoly ((2 : ℝ) ^ j) (S.filter (fun l => Nat.log 2 l = j))
            (fun l => χ (l : ZMod k)) t *
          normPoly (a₁ * Y / (4 * (2 : ℝ) ^ i * (2 : ℝ) ^ j)) (tupleRange a₁ a₂ Y i j)
            (fun u => if u ≡ b [MOD k] then cc u else 0) t) =
          fun t => normPoly ((2 : ℝ) ^ i) (G ∩ natIcc ((2 : ℝ) ^ i) (2 * (2 : ℝ) ^ i))
            (fun p => if Nat.log 2 p = i then (if p ≡ a [MOD k] then (1 : ℂ) else 0) else 0) t *
          normPoly ((2 : ℝ) ^ j) (S.filter (fun l => Nat.log 2 l = j))
            (fun l => χ (l : ZMod k)) t *
          normPoly (a₁ * Y / (4 * (2 : ℝ) ^ i * (2 : ℝ) ^ j)) (tupleRange a₁ a₂ Y i j)
            (fun u => if u ≡ b [MOD k] then cc u else 0) t :=
        funext fun t => by
          rw [normPoly_dyad_eq G hG i (fun p => if p ≡ a [MOD k] then (1 : ℂ) else 0) t]
      rw [hfun]
      exact h2
    have h1 := box_energy_three hk h hG0 hJ0 hU0 hJk cc (hWbox i j) Y (hpow0 i).ne'
      (hpow0 j).ne' hR.ne' hbd hprod'
    have hscal : (2 : ℝ) ^ i * (2 : ℝ) ^ j * (a₁ * Y / (4 * (2 : ℝ) ^ i * (2 : ℝ) ^ j)) / Y =
        a₁ / 4 := by
      rw [mul_assoc, dyad2_scale_lower, div_right_comm, mul_div_assoc, div_self hY.ne', mul_one]
    have ha4 : (0 : ℝ) < a₁ / 4 := by linarith
    rw [hscal, abs_of_pos ha4] at h1
    exact h1
  have hbd' : 0 ≤ (k : ℝ) ^ 2 * ((k : ℝ) ^ 2 * (((k : ℝ) * (a₁ / 4)) ^ 2 * bd)) :=
    mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _) hbd))
  have hinner : ∀ i ∈ G.image (Nat.log 2),
      HighEnergyLe (endpointPolynomial (fun w => ∑ j ∈ S.image (Nat.log 2),
        tupleBox G S cc (tupleRange a₁ a₂ Y i j) i j w) Y h k) lo hi
        (((S.image (Nat.log 2)).card : ℝ) ^ 2 *
          ((k : ℝ) ^ 2 * ((k : ℝ) ^ 2 * (((k : ℝ) * (a₁ / 4)) ^ 2 * bd)))) :=
    fun i hiI => sum_boxes_energy (S.image (Nat.log 2))
      (fun j => tupleBox G S cc (tupleRange a₁ a₂ Y i j) i j) (fun j _ => hsupp i j) Y h k
      (hbox i hiI) hbd'
  have hsupp' : ∀ i ∈ G.image (Nat.log 2), ∀ w,
      (∑ j ∈ S.image (Nat.log 2), tupleBox G S cc (tupleRange a₁ a₂ Y i j) i j w) ≠ 0 →
        w ∈ Finset.Icc 1 ⌊4 * a₂ * Y⌋₊ := by
    intro i _ w hw
    obtain ⟨j, -, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
    exact hsupp i j w hne
  exact sum_boxes_energy (G.image (Nat.log 2))
    (fun i w => ∑ j ∈ S.image (Nat.log 2), tupleBox G S cc (tupleRange a₁ a₂ Y i j) i j w)
    hsupp' Y h k hinner (mul_nonneg (sq_nonneg _) hbd')

/-! ### The cut coefficient and the dyads of a slot -/

/-- The coefficient cut to `1 ≤ u ≤ x²`. -/
def truncCoeff (x : ℝ) (F : ℕ → ℂ) (u : ℕ) : ℂ :=
  if 1 ≤ u ∧ (u : ℝ) ≤ x ^ (2 : ℝ) then F u else 0

theorem truncCoeff_eq {x : ℝ} (F : ℕ → ℂ) {u : ℕ} (h1 : 1 ≤ u) (h2 : (u : ℝ) ≤ x ^ (2 : ℝ)) :
    truncCoeff x F u = F u := by
  unfold truncCoeff
  exact if_pos ⟨h1, h2⟩

theorem norm_truncCoeff_le {x B : ℝ} {F : ℕ → ℂ} (hB : 0 ≤ B)
    (hF : ∀ u : ℕ, 1 ≤ u → (u : ℝ) ≤ x ^ (2 : ℝ) → ‖F u‖ ≤ B) (u : ℕ) :
    ‖truncCoeff x F u‖ ≤ B := by
  unfold truncCoeff
  split_ifs with hu
  · exact hF u hu.1 hu.2
  · rw [norm_zero]
    exact hB

/-- The double convolution at `1 ≤ w ≤ x²` only uses the coefficient on `1 ≤ u ≤ x²`. -/
theorem primeConv_primeConv_truncCoeff {x : ℝ} (G S : Finset ℕ) (F : ℕ → ℂ) {w : ℕ}
    (hw : 1 ≤ w) (hwx : (w : ℝ) ≤ x ^ (2 : ℝ)) :
    primeConv G (primeConv S F) w = primeConv G (primeConv S (truncCoeff x F)) w := by
  refine primeConv_congr fun p _ hpw => primeConv_congr fun l _ hlm => ?_
  have h1 : 1 ≤ w / p := one_le_div_of_dvd hw hpw
  have h2 : 1 ≤ w / p / l := one_le_div_of_dvd h1 hlm
  have h3 : ((w / p / l : ℕ) : ℝ) ≤ x ^ (2 : ℝ) :=
    (Nat.cast_le.mpr ((Nat.div_le_self _ _).trans (Nat.div_le_self _ _))).trans hwx
  exact (truncCoeff_eq F h2 h3).symm

/-- A dyad of an interval of primes is an interval of primes. -/
theorem isPrimeInterval_filter_log {S : Finset ℕ} (hprime : ∀ l ∈ S, l.Prime)
    (hint : ∀ ℓ₁ ∈ S, ∀ ℓ₂ ∈ S, ∀ ℓ : ℕ, ℓ.Prime → ℓ₁ ≤ ℓ → ℓ ≤ ℓ₂ → ℓ ∈ S) (j : ℕ) :
    IsPrimeInterval (S.filter (fun l => Nat.log 2 l = j)) := by
  refine ⟨fun p hp => hprime p (Finset.mem_filter.mp hp).1, ?_⟩
  intro p₁ hp₁ p₂ hp₂ p hp h1 h2
  obtain ⟨hp₁S, hlog₁⟩ := Finset.mem_filter.mp hp₁
  obtain ⟨hp₂S, hlog₂⟩ := Finset.mem_filter.mp hp₂
  refine Finset.mem_filter.mpr ⟨hint p₁ hp₁S p₂ hp₂S p hp h1 h2, ?_⟩
  have h3 : Nat.log 2 p₁ ≤ Nat.log 2 p := Nat.log_mono_right h1
  have h4 : Nat.log 2 p ≤ Nat.log 2 p₂ := Nat.log_mono_right h2
  omega

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
