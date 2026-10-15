module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.SeparationCore

/-!
# Tools for the separation of the extracted parts: the energy of a box and of a sum of boxes

`[P-06:0723–0726]`: "Divide all factors into dyads … There are only a fixed log-power number of
boxes."

* `HighEnergyLe.sum`, `sum_boxes_energy`: a sum of `n` polynomials with energy `≤ bd` has energy
  `≤ n² bd`; the uncut polynomial of a sum of box coefficients.
* `box_energy_two`: the uncut polynomial of a two-factor box `{(l, u)}` has energy
  `≤ k² (k |R₁R₂/Y|)² bd` when all products of the two normalized polynomials with residue
  restrictions have energy `≤ bd` (`endpointPolynomial_collapseCoeff`).
* `dyad_box_product`, `dyad_scale_lower`, `dyad_scale_upper`, `div_mem_natIcc`, `div_mem_box`:
  the sizes in a dyadic box.
* `box_bound_numeric`: `3L · 4L · L^C ≤ L^{|C| + 3}` for `L ≥ 12`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

noncomputable section

/-! ### Sums of polynomials -/

/-- A sum of `n` functions with energy `≤ bd` has energy `≤ n² bd`. -/
theorem HighEnergyLe.sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) {lo hi bd : ℝ}
    (hc : ∀ i ∈ s, Continuous (f i)) (hE : ∀ i ∈ s, HighEnergyLe (f i) lo hi bd) (hbd : 0 ≤ bd) :
    HighEnergyLe (fun t => ∑ i ∈ s, f i t) lo hi ((s.card : ℝ) ^ 2 * bd) := by
  have hZ : ∑ _i ∈ s, ‖(1 : ℂ)‖ ≤ (s.card : ℝ) :=
    le_of_eq (by rw [Finset.sum_const, nsmul_eq_mul, norm_one, mul_one])
  have h := HighEnergyLe.sum_weighted s (fun _ => (1 : ℂ)) f hc hE hbd hZ
  have heq : (fun t : ℝ => ∑ i ∈ s, (1 : ℂ) * f i t) = fun t : ℝ => ∑ i ∈ s, f i t :=
    funext fun t => Finset.sum_congr rfl fun i _ => one_mul _
  rw [← heq]
  exact h

/-- **The uncut polynomial of a sum of boxes**: `n` boxes cost `n²`. -/
theorem sum_boxes_energy {ι : Type*} (s : Finset ι) (Fi : ι → ℕ → ℂ) {W : ℕ}
    (hsupp : ∀ i ∈ s, ∀ w, Fi i w ≠ 0 → w ∈ Finset.Icc 1 W) (Y : ℝ) (h : ℤ) (k : ℕ)
    {lo hi bd : ℝ} (hE : ∀ i ∈ s, HighEnergyLe (endpointPolynomial (Fi i) Y h k) lo hi bd)
    (hbd : 0 ≤ bd) :
    HighEnergyLe (endpointPolynomial (fun w => ∑ i ∈ s, Fi i w) Y h k) lo hi
      ((s.card : ℝ) ^ 2 * bd) := by
  have heq : endpointPolynomial (fun w => ∑ i ∈ s, Fi i w) Y h k =
      fun t => ∑ i ∈ s, endpointPolynomial (Fi i) Y h k t :=
    funext fun t => endpointPolynomial_finset_sum s Fi hsupp Y h k t
  rw [heq]
  exact HighEnergyLe.sum s (fun i => endpointPolynomial (Fi i) Y h k)
    (fun i hi => continuous_endpointPolynomial_Icc (hsupp i hi) Y h k) hE hbd

/-! ### A two-factor box -/

/-- **The uncut polynomial of a two-factor box**: if every product of the normalized polynomials
of `1_{l ≡ a} α_l` and `1_{u ≡ b} c_u` has energy `≤ bd`, then the uncut polynomial of the box has
energy `≤ k² (k |R₁R₂/Y|)² bd`. -/
theorem box_energy_two {k : ℕ} (hk : 0 < k) (h : ℤ) {J U : Finset ℕ} (hJ0 : ∀ l ∈ J, l ≠ 0)
    (hU0 : ∀ u ∈ U, u ≠ 0) (α c : ℕ → ℂ) {W : ℕ}
    (hW : ∀ x ∈ J ×ˢ U, x.1 * x.2 ∈ Finset.Icc 1 W) (Y : ℝ) {R₁ R₂ : ℝ} (hR₁ : R₁ ≠ 0)
    (hR₂ : R₂ ≠ 0) {lo hi bd : ℝ} (hbd : 0 ≤ bd)
    (hprod : ∀ a b : ℕ, HighEnergyLe
      (fun t => normPoly R₁ J (fun l => if l ≡ a [MOD k] then α l else 0) t *
        normPoly R₂ U (fun u => if u ≡ b [MOD k] then c u else 0) t) lo hi bd) :
    HighEnergyLe (endpointPolynomial (collapseCoeff J U α c) Y h k) lo hi
      ((k : ℝ) ^ 2 * (((k : ℝ) * |R₁ * R₂ / Y|) ^ 2 * bd)) := by
  obtain ⟨z, hzdef⟩ : ∃ z : ℕ → ℕ → ℂ, z = fun a b =>
      addChar ((h : ℝ) * ((a * b : ℕ) : ℝ) / (k : ℝ)) * ((R₁ * R₂ / Y : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨Pr, hPrdef⟩ : ∃ Pr : ℕ → ℕ → ℝ → ℂ, Pr = fun a b t =>
      normPoly R₁ J (fun l => if l ≡ a [MOD k] then α l else 0) t *
        normPoly R₂ U (fun u => if u ≡ b [MOD k] then c u else 0) t := ⟨_, rfl⟩
  have heq : endpointPolynomial (collapseCoeff J U α c) Y h k =
      fun t => ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k, z a b * Pr a b t := by
    funext t
    rw [hzdef, hPrdef]
    exact endpointPolynomial_collapseCoeff hk h α c hW Y hR₁ hR₂ t
  have hPrc : ∀ a b, Continuous (Pr a b) := by
    intro a b
    rw [hPrdef]
    exact (continuous_normPoly R₁ hJ0 _).mul (continuous_normPoly R₂ hU0 _)
  have hPrE : ∀ a b, HighEnergyLe (Pr a b) lo hi bd := by
    intro a b
    rw [hPrdef]
    exact hprod a b
  have hznorm : ∀ a b, ‖z a b‖ = |R₁ * R₂ / Y| := by
    intro a b
    rw [hzdef]
    show ‖addChar ((h : ℝ) * ((a * b : ℕ) : ℝ) / (k : ℝ)) * ((R₁ * R₂ / Y : ℝ) : ℂ)‖ =
      |R₁ * R₂ / Y|
    rw [norm_mul, norm_addChar, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hinner : ∀ a ∈ Finset.range k,
      HighEnergyLe (fun t => ∑ b ∈ Finset.range k, z a b * Pr a b t) lo hi
        (((k : ℝ) * |R₁ * R₂ / Y|) ^ 2 * bd) := by
    intro a _
    refine HighEnergyLe.sum_weighted (Finset.range k) (z a) (Pr a) (fun b _ => hPrc a b)
      (fun b _ => hPrE a b) hbd (le_of_eq ?_)
    rw [Finset.sum_congr rfl fun b _ => hznorm a b, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
  have hinnerc : ∀ a ∈ Finset.range k,
      Continuous (fun t => ∑ b ∈ Finset.range k, z a b * Pr a b t) :=
    fun a _ => continuous_finsetSum _ fun b _ => continuous_const.mul (hPrc a b)
  have houter := HighEnergyLe.sum (Finset.range k)
    (fun a => fun t => ∑ b ∈ Finset.range k, z a b * Pr a b t) hinnerc hinner
    (mul_nonneg (sq_nonneg _) hbd)
  rw [Finset.card_range] at houter
  rw [heq]
  exact houter

/-! ### Sizes in a dyadic box -/

/-- The products of a box with first factor in the dyad `i` of `G` and second factor in
`[R₁, R₂]`. -/
theorem dyad_box_product {G : Finset ℕ} (hG : ∀ p ∈ G, p ≠ 0) {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) {i : ℕ}
    {y : ℕ × ℕ} (hy : y ∈ (G.filter (fun p => Nat.log 2 p = i)) ×ˢ natIcc R₁ R₂) :
    1 ≤ y.1 * y.2 ∧ (2 : ℝ) ^ i * R₁ ≤ ((y.1 * y.2 : ℕ) : ℝ) ∧
      ((y.1 * y.2 : ℕ) : ℝ) ≤ 2 * (2 : ℝ) ^ i * R₂ := by
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hy
  obtain ⟨hpG, hlog⟩ := Finset.mem_filter.mp h1
  have hp0 : y.1 ≠ 0 := hG _ hpG
  have hn := (mem_natIcc_of_pos hR₁).mp h2
  have hn0 : y.2 ≠ 0 := ne_zero_of_mem_natIcc hR₁ h2
  have hp1 : (2 : ℝ) ^ i ≤ (y.1 : ℝ) := by
    rw [← hlog]
    exact two_pow_log_le hp0
  have hp2 : (y.1 : ℝ) ≤ 2 * (2 : ℝ) ^ i := by
    rw [← hlog]
    exact (lt_two_mul_two_pow_log y.1).le
  have hpow0 : (0 : ℝ) < (2 : ℝ) ^ i := pow_pos two_pos i
  refine ⟨Nat.succ_le_of_lt (Nat.mul_pos (Nat.pos_of_ne_zero hp0) (Nat.pos_of_ne_zero hn0)),
    ?_, ?_⟩
  · rw [Nat.cast_mul]
    exact mul_le_mul hp1 hn.1 hR₁.le (Nat.cast_nonneg _)
  · rw [Nat.cast_mul]
    exact mul_le_mul hp2 hn.2 (Nat.cast_nonneg _) (mul_nonneg zero_le_two hpow0.le)

/-- `2^i · aY/(2 · 2^i) = aY/2`. -/
theorem dyad_scale_lower (a Y : ℝ) (i : ℕ) :
    (2 : ℝ) ^ i * (a * Y / (2 * (2 : ℝ) ^ i)) = a * Y / 2 := by
  have hp : (2 : ℝ) * (2 : ℝ) ^ i ≠ 0 := (mul_pos two_pos (pow_pos two_pos i)).ne'
  rw [eq_div_iff two_ne_zero]
  calc (2 : ℝ) ^ i * (a * Y / (2 * (2 : ℝ) ^ i)) * 2
      = a * Y / (2 * (2 : ℝ) ^ i) * (2 * (2 : ℝ) ^ i) := by ring
    _ = a * Y := div_mul_cancel₀ _ hp

/-- `2 · 2^i · aY/2^i = 2aY`. -/
theorem dyad_scale_upper (a Y : ℝ) (i : ℕ) :
    2 * (2 : ℝ) ^ i * (a * Y / (2 : ℝ) ^ i) = 2 * a * Y := by
  have hp : (2 : ℝ) ^ i ≠ 0 := (pow_pos two_pos i).ne'
  calc 2 * (2 : ℝ) ^ i * (a * Y / (2 : ℝ) ^ i) = 2 * (a * Y / (2 : ℝ) ^ i * (2 : ℝ) ^ i) := by
        ring
    _ = 2 * (a * Y) := by rw [div_mul_cancel₀ _ hp]
    _ = 2 * a * Y := by ring

/-- `w / p ∈ [A, B]` for a divisor `p > 0` of `w` with `A p ≤ w ≤ B p`. -/
theorem div_mem_natIcc {A B : ℝ} {w p : ℕ} (hp0 : (0 : ℝ) < (p : ℝ)) (hA : 0 < A) (hpw : p ∣ w)
    (h1 : A * (p : ℝ) ≤ (w : ℝ)) (h2 : (w : ℝ) ≤ B * (p : ℝ)) : w / p ∈ natIcc A B := by
  have hcast : ((w / p : ℕ) : ℝ) = (w : ℝ) / (p : ℝ) := Nat.cast_div hpw hp0.ne'
  rw [mem_natIcc_of_pos hA, hcast]
  exact ⟨(le_div_iff₀ hp0).mpr h1, (div_le_iff₀ hp0).mpr h2⟩

/-- The cofactor range of a dyad is automatic: for `a₁Y ≤ w ≤ a₂Y` and a divisor `p` of `w` with
`P ≤ p ≤ 2P`, `w/p ∈ [a₁Y/(2P), a₂Y/P]`. -/
theorem div_mem_box {a₁ a₂ Y P : ℝ} (ha₁ : 0 < a₁) (hY : 0 < Y) (hP : 0 < P) {w p : ℕ}
    (hw1 : a₁ * Y ≤ (w : ℝ)) (hw2 : (w : ℝ) ≤ a₂ * Y) (hp1 : P ≤ (p : ℝ))
    (hp2 : (p : ℝ) ≤ 2 * P) (hpw : p ∣ w) :
    w / p ∈ natIcc (a₁ * Y / (2 * P)) (a₂ * Y / P) := by
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le hP hp1
  have h2P : (0 : ℝ) < 2 * P := mul_pos two_pos hP
  have ha₁Y : 0 < a₁ * Y := mul_pos ha₁ hY
  have hw0 : (0 : ℝ) ≤ (w : ℝ) := Nat.cast_nonneg w
  refine div_mem_natIcc hp0 (div_pos ha₁Y h2P) hpw ?_ ?_
  · calc a₁ * Y / (2 * P) * (p : ℝ) ≤ a₁ * Y / (2 * P) * (2 * P) :=
          mul_le_mul_of_nonneg_left hp2 (div_pos ha₁Y h2P).le
      _ = a₁ * Y := div_mul_cancel₀ _ h2P.ne'
      _ ≤ (w : ℝ) := hw1
  · calc (w : ℝ) ≤ a₂ * Y := hw2
      _ = a₂ * Y / P * P := (div_mul_cancel₀ _ hP.ne').symm
      _ ≤ a₂ * Y / P * (p : ℝ) :=
          mul_le_mul_of_nonneg_left hp1 (div_nonneg (hw0.trans hw2) hP.le)

/-! ### A power of `L` -/

/-- `3L · (4L · L^C) ≤ L^{|C| + 3}` for `L ≥ 12`. -/
theorem box_bound_numeric {L C : ℝ} (hL : 12 ≤ L) : 3 * L * (4 * L * L ^ C) ≤ L ^ (|C| + 3) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have h1 : L ^ C ≤ L ^ |C| := Real.rpow_le_rpow_of_exponent_le hL1 (le_abs_self C)
  have h0 : 0 ≤ L ^ |C| := Real.rpow_nonneg hL0.le _
  have hLL : 0 ≤ L * L := mul_nonneg hL0.le hL0.le
  have e : L ^ (|C| + 3) = L ^ |C| * (L * L * L) := by
    rw [Real.rpow_add hL0, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  calc 3 * L * (4 * L * L ^ C) = 12 * (L * L) * L ^ C := by ring
    _ ≤ 12 * (L * L) * L ^ |C| :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num) hLL)
    _ ≤ L * (L * L) * L ^ |C| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL hLL) h0
    _ = L ^ (|C| + 3) := by
        rw [e]
        ring

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
