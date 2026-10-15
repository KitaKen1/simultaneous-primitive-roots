module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.SeparationTools

/-!
# Tools for the separation of the extracted parts: residue classes and dyadic boxes

`[P-06:0717–0726]`: "Separate the rational phase by residue classes modulo `k`. … In the constant
part fix classes for `p_s, n`. Both operations have polynomial-in-`k` total cost and do not
require `u` or `n` to be units. Divide all factors into dyads …"

* `addChar_congr_modEq`, `sum_mul_residue`: `e(hm/k)` depends on `m` modulo `k`; a sum
  `∑_l φ(l) f(l mod k)` is `∑_{a < k} f(a) ∑_l 1_{l ≡ a} φ(l)`.
* `sum_collapseCoeff_mul`, `sum_collapseCoeff_addChar`, `endpointPolynomial_collapseCoeff`: the
  uncut polynomial of a box. For the coefficient `d_w = ∑_{l u = w} α_l c_u`
  (`collapseCoeff`), `Y⁻¹ ∑_w d_w e(hw/k) w^{it}` is the sum over the classes `a, b` modulo `k` of
  `e(hab/k) (R₁R₂/Y)` times the product of the normalized polynomials of `1_{l ≡ a} α_l` and
  `1_{u ≡ b} c_u`: cost `k²`.
* `collapseCoeff_eq_sum_dvd`, `sum_boxes_collapse`: the sum over the dyads `2^i ≤ p < 2^{i+1}` of
  the box coefficients is the convolution `∑_{p ∈ G, p ∣ w} d(w/p)`, as soon as the cofactor
  range of each box contains the cofactors that occur.
* `two_pow_log_le`, `lt_two_mul_two_pow_log`, `mem_natIcc_of_log_eq`, `card_image_log_le`,
  `normPoly_dyad_eq`: the dyad of `p` is `i = Nat.log 2 p`; there are at most `2 log X + 1` dyads
  below `X`; the polynomial of a dyad in the form of the product bounds.
* `norm_collapseCoeff_one_le`: a box coefficient at `1 ≤ w ≤ x²` is at most `4 L` times the bound
  for `c`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

noncomputable section

/-! ### Rational phases and residue classes -/

/-- `e(hm/k)` depends only on `m` modulo `k`. -/
theorem addChar_congr_modEq (h : ℤ) {k : ℕ} (hk : 0 < k) {m n : ℕ} (hmn : m ≡ n [MOD k]) :
    addChar ((h : ℝ) * (m : ℝ) / (k : ℝ)) = addChar ((h : ℝ) * (n : ℝ) / (k : ℝ)) := by
  have h' : m % k = n % k := hmn
  rw [addChar_mod h hk m, addChar_mod h hk n, h']

/-- **Residue classes**: `∑_l α_l g_l f(l mod k) = ∑_{a < k} f(a) ∑_l 1_{l ≡ a (k)} α_l g_l`. -/
theorem sum_mul_residue {k : ℕ} (hk : 0 < k) (J : Finset ℕ) (α g f : ℕ → ℂ) :
    ∑ l ∈ J, α l * g l * f (l % k) =
      ∑ a ∈ Finset.range k, f a * ∑ l ∈ J, (if l ≡ a [MOD k] then α l else 0) * g l := by
  have h1 : ∀ l : ℕ, α l * g l * f (l % k) =
      ∑ a ∈ Finset.range k, f a * ((if l ≡ a [MOD k] then α l else 0) * g l) := by
    intro l
    rw [Finset.sum_eq_single (l % k)]
    · rw [if_pos (Nat.mod_modEq l k).symm]
      ring
    · intro a ha hne
      have ha' : a < k := Finset.mem_range.mp ha
      have hne' : ¬ l ≡ a [MOD k] := by
        intro hmod
        have h2 : l % k = a % k := hmod
        rw [Nat.mod_eq_of_lt ha'] at h2
        exact hne h2.symm
      rw [if_neg hne', zero_mul, mul_zero]
    · intro hnot
      exact absurd (Finset.mem_range.mpr (Nat.mod_lt l hk)) hnot
  rw [Finset.sum_congr rfl fun l _ => h1 l, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]

/-! ### The polynomial of a box -/

/-- `∑_w d_w g(w) = ∑_{l ∈ J} ∑_{u ∈ U} α_l c_u g(l u)` for `d = collapseCoeff J U α c`. -/
theorem sum_collapseCoeff_mul (J U : Finset ℕ) (α c g : ℕ → ℂ) {s : Finset ℕ}
    (hW : ∀ x ∈ J ×ˢ U, x.1 * x.2 ∈ s) :
    ∑ w ∈ s, collapseCoeff J U α c w * g w = ∑ l ∈ J, ∑ u ∈ U, α l * c u * g (l * u) := by
  have h1 : ∑ l ∈ J, ∑ u ∈ U, α l * c u * g (l * u) =
      ∑ x ∈ J ×ˢ U, α x.1 * c x.2 * g (x.1 * x.2) :=
    (Finset.sum_product' J U (fun l u => α l * c u * g (l * u))).symm
  have h2 : ∑ x ∈ J ×ˢ U, α x.1 * c x.2 * g (x.1 * x.2) =
      ∑ w ∈ s, ∑ x ∈ (J ×ˢ U).filter (fun x : ℕ × ℕ => x.1 * x.2 = w),
        α x.1 * c x.2 * g (x.1 * x.2) :=
    (Finset.sum_fiberwise_of_maps_to hW _).symm
  rw [h1, h2]
  refine Finset.sum_congr rfl fun w _ => ?_
  unfold collapseCoeff
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [(Finset.mem_filter.mp hx).2]

/-- A box coefficient lives on the products of the box. -/
theorem collapseCoeff_ne_zero_mem_image {J U : Finset ℕ} {α c : ℕ → ℂ} {w : ℕ}
    (hw : collapseCoeff J U α c w ≠ 0) :
    w ∈ (J ×ˢ U).image (fun x : ℕ × ℕ => x.1 * x.2) := by
  unfold collapseCoeff at hw
  obtain ⟨x, hx, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_image.mpr ⟨x, h1, h2⟩

theorem collapseCoeff_support {J U : Finset ℕ} (α c : ℕ → ℂ) {W : ℕ}
    (hW : ∀ x ∈ J ×ˢ U, x.1 * x.2 ∈ Finset.Icc 1 W) :
    ∀ w, collapseCoeff J U α c w ≠ 0 → w ∈ Finset.Icc 1 W := by
  intro w hw
  obtain ⟨x, hx, hxw⟩ := Finset.mem_image.mp (collapseCoeff_ne_zero_mem_image hw)
  rw [← hxw]
  exact hW x hx

/-- **The rational phase on a box, by residue classes**: cost `k²`. -/
theorem sum_collapseCoeff_addChar {k : ℕ} (hk : 0 < k) (h : ℤ) (J U : Finset ℕ) (α c : ℕ → ℂ)
    (z : ℂ) {s : Finset ℕ} (hW : ∀ x ∈ J ×ˢ U, x.1 * x.2 ∈ s) :
    ∑ w ∈ s, collapseCoeff J U α c w * addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) * (w : ℂ) ^ z =
      ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k,
        addChar ((h : ℝ) * ((a * b : ℕ) : ℝ) / (k : ℝ)) *
          ((∑ l ∈ J, (if l ≡ a [MOD k] then α l else 0) * (l : ℂ) ^ z) *
            (∑ u ∈ U, (if u ≡ b [MOD k] then c u else 0) * (u : ℂ) ^ z)) := by
  obtain ⟨Sb, hSb⟩ : ∃ Sb : ℕ → ℂ,
      Sb = fun b => ∑ u ∈ U, (if u ≡ b [MOD k] then c u else 0) * (u : ℂ) ^ z := ⟨_, rfl⟩
  obtain ⟨Fa, hFa⟩ : ∃ Fa : ℕ → ℂ, Fa = fun a => ∑ b ∈ Finset.range k,
      addChar ((h : ℝ) * ((a * b : ℕ) : ℝ) / (k : ℝ)) * Sb b := ⟨_, rfl⟩
  have hstep1 : ∑ w ∈ s, collapseCoeff J U α c w * addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) *
        (w : ℂ) ^ z =
      ∑ l ∈ J, ∑ u ∈ U, α l * c u *
        (addChar ((h : ℝ) * ((l * u : ℕ) : ℝ) / (k : ℝ)) * ((l * u : ℕ) : ℂ) ^ z) := by
    refine (Finset.sum_congr rfl fun w _ => mul_assoc _ _ _).trans ?_
    exact sum_collapseCoeff_mul J U α c
      (fun w => addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) * (w : ℂ) ^ z) hW
  have hpow : ∀ l u : ℕ, ((l * u : ℕ) : ℂ) ^ z = (l : ℂ) ^ z * (u : ℂ) ^ z := by
    intro l u
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  have hinner : ∀ l : ℕ, ∑ u ∈ U, α l * c u *
        (addChar ((h : ℝ) * ((l * u : ℕ) : ℝ) / (k : ℝ)) * ((l * u : ℕ) : ℂ) ^ z) =
      α l * (l : ℂ) ^ z * Fa (l % k) := by
    intro l
    have h1 : ∀ u : ℕ, α l * c u *
          (addChar ((h : ℝ) * ((l * u : ℕ) : ℝ) / (k : ℝ)) * ((l * u : ℕ) : ℂ) ^ z) =
        α l * (l : ℂ) ^ z * (c u * (u : ℂ) ^ z *
          addChar ((h : ℝ) * (((l % k) * (u % k) : ℕ) : ℝ) / (k : ℝ))) := by
      intro u
      rw [addChar_congr_modEq h hk ((Nat.mod_modEq l k).symm.mul (Nat.mod_modEq u k).symm), hpow]
      ring
    have h2 := sum_mul_residue hk U c (fun u => (u : ℂ) ^ z)
      (fun b => addChar ((h : ℝ) * (((l % k) * b : ℕ) : ℝ) / (k : ℝ)))
    rw [Finset.sum_congr rfl fun u _ => h1 u, ← Finset.mul_sum, h2, hFa, hSb]
  rw [hstep1, Finset.sum_congr rfl fun l _ => hinner l,
    sum_mul_residue hk J α (fun l => (l : ℂ) ^ z) Fa]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hFa, hSb, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- The normalization of a product of two sums. -/
theorem normalize_two (e S₁ S₂ : ℂ) {R₁ R₂ : ℝ} (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0) (Y : ℝ) :
    (Y : ℂ)⁻¹ * (e * (S₁ * S₂)) =
      e * ((R₁ * R₂ / Y : ℝ) : ℂ) * ((R₁ : ℂ)⁻¹ * S₁ * ((R₂ : ℂ)⁻¹ * S₂)) := by
  have hR₁' : (R₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR₁
  have hR₂' : (R₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR₂
  have key : e * ((R₁ : ℂ) * (R₂ : ℂ) / (Y : ℂ)) * ((R₁ : ℂ)⁻¹ * S₁ * ((R₂ : ℂ)⁻¹ * S₂)) =
      ((R₁ : ℂ) * (R₁ : ℂ)⁻¹) * ((R₂ : ℂ) * (R₂ : ℂ)⁻¹) * ((Y : ℂ)⁻¹ * (e * (S₁ * S₂))) := by
    ring
  rw [Complex.ofReal_div, Complex.ofReal_mul, key, mul_inv_cancel₀ hR₁', mul_inv_cancel₀ hR₂',
    one_mul, one_mul]

/-- **The uncut polynomial of a box** `{(l, u) : l ∈ J, u ∈ U}` with coefficient `α_l c_u`, as a
combination of `k²` products of two normalized polynomials with residue restrictions. -/
theorem endpointPolynomial_collapseCoeff {k : ℕ} (hk : 0 < k) (h : ℤ) {J U : Finset ℕ}
    (α c : ℕ → ℂ) {W : ℕ} (hW : ∀ x ∈ J ×ˢ U, x.1 * x.2 ∈ Finset.Icc 1 W) (Y : ℝ) {R₁ R₂ : ℝ}
    (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0) (t : ℝ) :
    endpointPolynomial (collapseCoeff J U α c) Y h k t =
      ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k,
        (addChar ((h : ℝ) * ((a * b : ℕ) : ℝ) / (k : ℝ)) * ((R₁ * R₂ / Y : ℝ) : ℂ)) *
          (normPoly R₁ J (fun l => if l ≡ a [MOD k] then α l else 0) t *
            normPoly R₂ U (fun u => if u ≡ b [MOD k] then c u else 0) t) := by
  rw [endpointPolynomial_eq_sum (collapseCoeff_support α c hW) Y h k t,
    sum_collapseCoeff_addChar hk h J U α c ((t : ℂ) * Complex.I) hW, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  exact normalize_two _ _ _ hR₁ hR₂ Y

/-! ### Boxes and convolutions -/

/-- A box coefficient with one factor running over a set `J` of positive integers is a sum over
the elements of `J` dividing `w`, when `U` contains the cofactors at which `c` does not
vanish. -/
theorem collapseCoeff_eq_sum_dvd {J U : Finset ℕ} (hJ : ∀ l ∈ J, 0 < l) (α c : ℕ → ℂ) (w : ℕ)
    (hU : ∀ l ∈ J, l ∣ w → c (w / l) ≠ 0 → w / l ∈ U) :
    collapseCoeff J U α c w = ∑ l ∈ J.filter (fun l => l ∣ w), α l * c (w / l) := by
  unfold collapseCoeff
  refine Finset.sum_bij_ne_zero (fun x _ _ => x.1) ?_ ?_ ?_ ?_
  · intro x hx _
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp h1).1, Dvd.intro _ h2⟩
  · intro x hx _ y hy _ hxy
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hx
    obtain ⟨_, h4⟩ := Finset.mem_filter.mp hy
    have hx1 : x.1 = y.1 := hxy
    have hpos : 0 < x.1 := hJ _ (Finset.mem_product.mp h1).1
    have h5 : x.1 * x.2 = x.1 * y.2 := by
      rw [h2, hx1]
      exact h4.symm
    exact Prod.ext hx1 (Nat.eq_of_mul_eq_mul_left hpos h5)
  · intro l hl hne
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hl
    have hne' : α l * c (w / l) ≠ 0 := hne
    have hc : c (w / l) ≠ 0 := fun h0 => hne' (by rw [h0, mul_zero])
    exact ⟨(l, w / l), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1, hU l h1 h2 hc⟩,
      Nat.mul_div_cancel' h2⟩, hne', rfl⟩
  · intro x hx _
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hx
    have hpos : 0 < x.1 := hJ _ (Finset.mem_product.mp h1).1
    have h3 : w / x.1 = x.2 := by
      rw [← h2]
      exact Nat.mul_div_cancel_left _ hpos
    show α x.1 * c x.2 = α x.1 * c (w / x.1)
    rw [h3]

/-- **The dyads of a convolution**: the sum over the dyads `i` of the box coefficients with
`p ∈ G`, `Nat.log 2 p = i`, cofactor range `M i` and coefficient `d i` is
`∑_{p ∈ G, p ∣ w} d (Nat.log 2 p) (w / p)`. -/
theorem sum_boxes_collapse (G : Finset ℕ) (hG : ∀ p ∈ G, 0 < p) (M : ℕ → Finset ℕ)
    (d : ℕ → ℕ → ℂ) (w : ℕ)
    (hM : ∀ p ∈ G, p ∣ w → d (Nat.log 2 p) (w / p) ≠ 0 → w / p ∈ M (Nat.log 2 p)) :
    ∑ i ∈ G.image (Nat.log 2),
        collapseCoeff (G.filter (fun p => Nat.log 2 p = i)) (M i) (fun _ => 1) (d i) w =
      ∑ p ∈ G.filter (fun p => p ∣ w), d (Nat.log 2 p) (w / p) := by
  have h1 : ∀ i ∈ G.image (Nat.log 2),
      collapseCoeff (G.filter (fun p => Nat.log 2 p = i)) (M i) (fun _ => 1) (d i) w =
        ∑ p ∈ (G.filter (fun p => p ∣ w)).filter (fun p => Nat.log 2 p = i),
          d (Nat.log 2 p) (w / p) := by
    intro i _
    have h2 := collapseCoeff_eq_sum_dvd (J := G.filter (fun p => Nat.log 2 p = i)) (U := M i)
      (fun p hp => hG p (Finset.mem_filter.mp hp).1) (fun _ => 1) (d i) w
      (fun p hp hpw hne => by
        obtain ⟨hpG, hlog⟩ := Finset.mem_filter.mp hp
        rw [← hlog] at hne ⊢
        exact hM p hpG hpw hne)
    rw [h2, Finset.filter_comm]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hlog : Nat.log 2 p = i := (Finset.mem_filter.mp hp).2
    rw [hlog, one_mul]
  rw [Finset.sum_congr rfl h1]
  exact Finset.sum_fiberwise_of_maps_to
    (fun p hp => Finset.mem_image_of_mem _ (Finset.mem_filter.mp hp).1) _

/-! ### Dyads -/

/-- `2^i ≤ p` for `i = Nat.log 2 p`, `p ≥ 1`. -/
theorem two_pow_log_le {p : ℕ} (hp : p ≠ 0) : (2 : ℝ) ^ Nat.log 2 p ≤ (p : ℝ) := by
  exact_mod_cast Nat.pow_log_le_self 2 hp

/-- `p < 2 · 2^i` for `i = Nat.log 2 p`. -/
theorem lt_two_mul_two_pow_log (p : ℕ) : (p : ℝ) < 2 * (2 : ℝ) ^ Nat.log 2 p := by
  have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
  have h' : (p : ℝ) < (2 : ℝ) ^ (Nat.log 2 p + 1) := by exact_mod_cast h
  rw [pow_succ] at h'
  linarith

/-- The dyad of `p`. -/
theorem mem_natIcc_of_log_eq {p i : ℕ} (hp : p ≠ 0) (hi : Nat.log 2 p = i) :
    p ∈ natIcc ((2 : ℝ) ^ i) (2 * (2 : ℝ) ^ i) := by
  have h0 : (0 : ℝ) ≤ 2 * (2 : ℝ) ^ i := mul_nonneg zero_le_two (pow_nonneg zero_le_two i)
  rw [mem_natIcc h0, ← hi]
  exact ⟨two_pow_log_le hp, (lt_two_mul_two_pow_log p).le⟩

/-- There are at most `2 log X + 1` dyads below `X`. -/
theorem card_image_log_le {G : Finset ℕ} {X : ℝ} (hX : 1 ≤ X)
    (hG : ∀ p ∈ G, p ≠ 0 ∧ (p : ℝ) ≤ X) :
    ((G.image (Nat.log 2)).card : ℝ) ≤ 2 * Real.log X + 1 := by
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hsub : G.image (Nat.log 2) ⊆ Finset.range (⌊2 * Real.log X⌋₊ + 1) := by
    intro i hi
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨hp0, hpX⟩ := hG p hp
    have h1 : (2 : ℝ) ^ Nat.log 2 p ≤ X := (two_pow_log_le hp0).trans hpX
    have h2 : Real.log ((2 : ℝ) ^ Nat.log 2 p) ≤ Real.log X :=
      Real.log_le_log (pow_pos two_pos _) h1
    rw [Real.log_pow] at h2
    have h4 : (Nat.log 2 p : ℝ) * (1 / 2) ≤ (Nat.log 2 p : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg _)
    have h3 : (Nat.log 2 p : ℝ) ≤ 2 * Real.log X := by linarith
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor h3))
  calc ((G.image (Nat.log 2)).card : ℝ)
      ≤ ((Finset.range (⌊2 * Real.log X⌋₊ + 1)).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ = (⌊2 * Real.log X⌋₊ : ℝ) + 1 := by
        rw [Finset.card_range, Nat.cast_add_one]
    _ ≤ 2 * Real.log X + 1 := by
        have h := Nat.floor_le (mul_nonneg zero_le_two hlogX)
        linarith

/-- The normalized polynomial of the dyad `i` of `G`, in the form of the product bounds: the range
is `G ∩ [2^i, 2 · 2^i]` and the dyad is part of the coefficient. -/
theorem normPoly_dyad_eq (G : Finset ℕ) (hG : ∀ p ∈ G, p ≠ 0) (i : ℕ) (β : ℕ → ℂ) (t : ℝ) :
    normPoly ((2 : ℝ) ^ i) (G.filter (fun p => Nat.log 2 p = i)) β t =
      normPoly ((2 : ℝ) ^ i) (G ∩ natIcc ((2 : ℝ) ^ i) (2 * (2 : ℝ) ^ i))
        (fun p => if Nat.log 2 p = i then β p else 0) t := by
  have hsub : G.filter (fun p => Nat.log 2 p = i) ⊆
      G ∩ natIcc ((2 : ℝ) ^ i) (2 * (2 : ℝ) ^ i) := by
    intro p hp
    obtain ⟨hpG, hlog⟩ := Finset.mem_filter.mp hp
    exact Finset.mem_inter.mpr ⟨hpG, mem_natIcc_of_log_eq (hG p hpG) hlog⟩
  have h1 : normPoly ((2 : ℝ) ^ i) (G.filter (fun p => Nat.log 2 p = i)) β t =
      (((2 : ℝ) ^ i : ℝ) : ℂ)⁻¹ * ∑ p ∈ G.filter (fun p => Nat.log 2 p = i),
        β p * (p : ℂ) ^ ((t : ℂ) * Complex.I) := rfl
  have h2 : normPoly ((2 : ℝ) ^ i) (G ∩ natIcc ((2 : ℝ) ^ i) (2 * (2 : ℝ) ^ i))
        (fun p => if Nat.log 2 p = i then β p else 0) t =
      (((2 : ℝ) ^ i : ℝ) : ℂ)⁻¹ * ∑ p ∈ G ∩ natIcc ((2 : ℝ) ^ i) (2 * (2 : ℝ) ^ i),
        (if Nat.log 2 p = i then β p else 0) * (p : ℂ) ^ ((t : ℂ) * Complex.I) := rfl
  rw [h1, h2]
  congr 1
  calc ∑ p ∈ G.filter (fun p => Nat.log 2 p = i), β p * (p : ℂ) ^ ((t : ℂ) * Complex.I)
      = ∑ p ∈ G.filter (fun p => Nat.log 2 p = i),
          (if Nat.log 2 p = i then β p else 0) * (p : ℂ) ^ ((t : ℂ) * Complex.I) :=
        Finset.sum_congr rfl fun p hp => by rw [if_pos (Finset.mem_filter.mp hp).2]
    _ = ∑ p ∈ G ∩ natIcc ((2 : ℝ) ^ i) (2 * (2 : ℝ) ^ i),
          (if Nat.log 2 p = i then β p else 0) * (p : ℂ) ^ ((t : ℂ) * Complex.I) :=
        Finset.sum_subset hsub fun p hpbig hnot => by
          have hlog : ¬ Nat.log 2 p = i := fun hl =>
            hnot (Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hpbig).1, hl⟩)
          rw [if_neg hlog, zero_mul]

/-! ### The size of a box coefficient -/

/-- A box coefficient with one factor running over a set of primes with weight `1`, at
`1 ≤ w ≤ x²`: at most `4 log x` terms. -/
theorem norm_collapseCoeff_one_le {J U : Finset ℕ} (hJ : ∀ l ∈ J, l.Prime) {c : ℕ → ℂ} {Bc : ℝ}
    (hc : ∀ u ∈ U, ‖c u‖ ≤ Bc) (hBc : 0 ≤ Bc) {w : ℕ} (hw : 1 ≤ w) {x : ℝ} (hx : 1 < x)
    (hwx : (w : ℝ) ≤ x ^ (2 : ℝ)) :
    ‖collapseCoeff J U (fun _ => 1) c w‖ ≤ 4 * Real.log x * Bc :=
  (norm_collapseCoeff_le (fun l hl => (hJ l hl).pos) (fun _ _ => le_of_eq norm_one) hc hBc w).trans
    (mul_le_mul_of_nonneg_right (card_filter_dvd_le hJ hw hx hwx) hBc)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
