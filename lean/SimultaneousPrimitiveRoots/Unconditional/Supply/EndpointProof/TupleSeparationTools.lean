module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.SeparationBoxEnergy
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.UnitCharacters

/-!
# Tools for the separation of the tuple part: three factors and characters

`[P-06:0718–0722]`: "In the tuple part, `p_s, p_l` are units modulo `k`; on fixed classes for `p_s`
and `u`, expand the remaining test in characters of `p_l` by orthogonality on the units. … Both
operations have polynomial-in-`k` total cost and do not require `u` or `n` to be units."

* `exists_phase_coeff`: for classes `a, b` modulo `k`, `e(h a b l / k) = ∑_χ ĉ_{a,b}(χ) χ(l)` for
  `l` prime to `k`, with `∑_χ |ĉ_{a,b}(χ)| ≤ √φ(k) ≤ k` (`rationalPhaseExpansion`).
* `sum_triple_addChar`: the rational phase on a three-factor box
  `∑_{p,l,u} c_u e(h p l u / k) (p l u)^z` is the sum over `a, b < k` and `χ mod k` of
  `ĉ_{a,b}(χ)` times the product of the three sums with coefficients `1_{p ≡ a}`, `χ(l)`,
  `1_{u ≡ b} c_u`.
* `box_energy_three`: the uncut polynomial of a three-factor box has energy
  `≤ k² · k² · (k |R₁R₂R₃/Y|)² bd` when all such products have energy `≤ bd`.
* `dyad_box_product_three`, `dyad2_scale_lower`, `dyad2_scale_upper`, `div_div_mem_box`: sizes in
  a box of two dyads; `primeConv_congr`; `box_bound_numeric_three`, `tuple_cost_numeric`: powers
  of `L`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

noncomputable section

/-! ### Characters of the long prime -/

/-- **The rational phase in characters of the long prime**: for `a, b` and `l` prime to `k`,
`e(h a l b / k) = ∑_χ ĉ_{a,b}(χ) χ(l)` with `∑_χ |ĉ_{a,b}(χ)| ≤ k`. -/
theorem exists_phase_coeff {k : ℕ} (hk : 0 < k) (h : ℤ) :
    ∃ ĉ : ℕ → ℕ → DirichletCharacter ℂ k → ℂ,
      (∀ a b : ℕ, ∑ χ : DirichletCharacter ℂ k, ‖ĉ a b χ‖ ≤ (k : ℝ)) ∧
        ∀ a b l : ℕ, l.Coprime k →
          addChar ((h : ℝ) * ((a * (l * b) : ℕ) : ℝ) / (k : ℝ)) =
            ∑ χ : DirichletCharacter ℂ k, ĉ a b χ * χ (l : ZMod k) := by
  have H : ∀ a b : ℕ, ∃ c : DirichletCharacter ℂ k → ℂ,
      (∑ ψ, ‖c ψ‖ ≤ Real.sqrt (k.totient : ℝ)) ∧
        ∀ v : ℕ, Nat.Coprime v k →
          SimultaneousPrimitiveRoots.Unconditional.Transference.expUnit
            (((h * a * b : ℤ) : ℝ) * (v : ℝ) / (k : ℝ)) = ∑ ψ, c ψ * ψ (v : ZMod k) :=
    fun a b =>
      SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.rationalPhaseExpansion
        k (h * a * b) hk
  choose ĉ h1 h2 using H
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsqrt : Real.sqrt (k.totient : ℝ) ≤ (k : ℝ) := by
    rw [Real.sqrt_le_iff]
    refine ⟨by linarith, ?_⟩
    have h3 : (k.totient : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.totient_le k
    have h4 : (k : ℝ) ≤ (k : ℝ) ^ 2 := by
      rw [pow_two]
      exact le_mul_of_one_le_left (by linarith) hk1
    exact h3.trans h4
  refine ⟨ĉ, fun a b => (h1 a b).trans hsqrt, fun a b l hl => ?_⟩
  rw [← h2 a b l hl]
  unfold addChar SimultaneousPrimitiveRoots.Unconditional.Transference.expUnit
  congr 1
  push_cast
  ring

/-- **The rational phase on a three-factor box**, by residue classes of the first and third
factors and characters of the second: cost `k² φ(k)`. -/
theorem sum_triple_addChar {k : ℕ} (hk : 0 < k) (h : ℤ) (G J U : Finset ℕ)
    (hJ : ∀ l ∈ J, l.Coprime k) (c : ℕ → ℂ) (z : ℂ)
    (ĉ : ℕ → ℕ → DirichletCharacter ℂ k → ℂ)
    (hĉ : ∀ a b l : ℕ, l.Coprime k →
      addChar ((h : ℝ) * ((a * (l * b) : ℕ) : ℝ) / (k : ℝ)) =
        ∑ χ : DirichletCharacter ℂ k, ĉ a b χ * χ (l : ZMod k)) :
    ∑ p ∈ G, ∑ l ∈ J, ∑ u ∈ U, c u *
        (addChar ((h : ℝ) * ((p * (l * u) : ℕ) : ℝ) / (k : ℝ)) * ((p * (l * u) : ℕ) : ℂ) ^ z) =
      ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k, ∑ χ : DirichletCharacter ℂ k,
        ĉ a b χ * ((∑ p ∈ G, (if p ≡ a [MOD k] then (1 : ℂ) else 0) * (p : ℂ) ^ z) *
          (∑ l ∈ J, χ (l : ZMod k) * (l : ℂ) ^ z) *
          (∑ u ∈ U, (if u ≡ b [MOD k] then c u else 0) * (u : ℂ) ^ z)) := by
  obtain ⟨Pa, hPa⟩ : ∃ Pa : ℕ → ℂ, Pa = fun a =>
      ∑ p ∈ G, (if p ≡ a [MOD k] then (1 : ℂ) else 0) * (p : ℂ) ^ z := ⟨_, rfl⟩
  obtain ⟨Lx, hLx⟩ : ∃ Lx : DirichletCharacter ℂ k → ℂ, Lx = fun χ =>
      ∑ l ∈ J, χ (l : ZMod k) * (l : ℂ) ^ z := ⟨_, rfl⟩
  obtain ⟨Sb, hSb⟩ : ∃ Sb : ℕ → ℂ, Sb = fun b =>
      ∑ u ∈ U, (if u ≡ b [MOD k] then c u else 0) * (u : ℂ) ^ z := ⟨_, rfl⟩
  obtain ⟨Ph, hPh⟩ : ∃ Ph : ℕ → ℂ, Ph = fun a =>
      ∑ b ∈ Finset.range k, Sb b * ∑ χ : DirichletCharacter ℂ k, ĉ a b χ * Lx χ := ⟨_, rfl⟩
  have hgoal : ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k, ∑ χ : DirichletCharacter ℂ k,
        ĉ a b χ * ((∑ p ∈ G, (if p ≡ a [MOD k] then (1 : ℂ) else 0) * (p : ℂ) ^ z) *
          (∑ l ∈ J, χ (l : ZMod k) * (l : ℂ) ^ z) *
          (∑ u ∈ U, (if u ≡ b [MOD k] then c u else 0) * (u : ℂ) ^ z)) =
      ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k, ∑ χ : DirichletCharacter ℂ k,
        ĉ a b χ * (Pa a * Lx χ * Sb b) := by
    rw [hPa, hLx, hSb]
  rw [hgoal]
  have hpow : ∀ p l u : ℕ, ((p * (l * u) : ℕ) : ℂ) ^ z =
      (p : ℂ) ^ z * ((l : ℂ) ^ z * (u : ℂ) ^ z) := by
    intro p l u
    rw [Nat.cast_mul, Complex.natCast_mul_natCast_cpow, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]
  -- the third factor, by residue classes
  have hu : ∀ p l : ℕ, ∑ u ∈ U, c u *
        (addChar ((h : ℝ) * ((p * (l * u) : ℕ) : ℝ) / (k : ℝ)) * ((p * (l * u) : ℕ) : ℂ) ^ z) =
      (p : ℂ) ^ z * ((l : ℂ) ^ z * ∑ b ∈ Finset.range k,
        addChar ((h : ℝ) * (((p % k) * (l * b) : ℕ) : ℝ) / (k : ℝ)) * Sb b) := by
    intro p l
    have h1 : ∀ u : ℕ, c u *
          (addChar ((h : ℝ) * ((p * (l * u) : ℕ) : ℝ) / (k : ℝ)) * ((p * (l * u) : ℕ) : ℂ) ^ z) =
        (p : ℂ) ^ z * ((l : ℂ) ^ z * (c u * (u : ℂ) ^ z *
          addChar ((h : ℝ) * (((p % k) * (l * (u % k)) : ℕ) : ℝ) / (k : ℝ)))) := by
      intro u
      rw [addChar_congr_modEq h hk ((Nat.mod_modEq p k).symm.mul
        ((Nat.ModEq.refl l).mul (Nat.mod_modEq u k).symm)), hpow]
      ring
    have h2 := sum_mul_residue hk U c (fun u => (u : ℂ) ^ z)
      (fun b => addChar ((h : ℝ) * (((p % k) * (l * b) : ℕ) : ℝ) / (k : ℝ)))
    rw [Finset.sum_congr rfl fun u _ => h1 u, ← Finset.mul_sum, ← Finset.mul_sum, h2, hSb]
  -- the second factor, by characters
  have hl : ∀ p : ℕ, ∑ l ∈ J, ∑ u ∈ U, c u *
        (addChar ((h : ℝ) * ((p * (l * u) : ℕ) : ℝ) / (k : ℝ)) * ((p * (l * u) : ℕ) : ℂ) ^ z) =
      (p : ℂ) ^ z * Ph (p % k) := by
    intro p
    have h1 : ∀ l ∈ J, ∑ u ∈ U, c u *
          (addChar ((h : ℝ) * ((p * (l * u) : ℕ) : ℝ) / (k : ℝ)) * ((p * (l * u) : ℕ) : ℂ) ^ z) =
        (p : ℂ) ^ z * ∑ b ∈ Finset.range k, Sb b * ∑ χ : DirichletCharacter ℂ k,
          ĉ (p % k) b χ * (χ (l : ZMod k) * (l : ℂ) ^ z) := by
      intro l hlJ
      rw [hu p l]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      have e : ∑ χ : DirichletCharacter ℂ k, ĉ (p % k) b χ * (χ (l : ZMod k) * (l : ℂ) ^ z) =
          (∑ χ : DirichletCharacter ℂ k, ĉ (p % k) b χ * χ (l : ZMod k)) * (l : ℂ) ^ z := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun χ _ => (mul_assoc _ _ _).symm
      rw [hĉ (p % k) b l (hJ l hlJ), e]
      ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, hPh]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.mul_sum, Finset.sum_comm, hLx]
    congr 1
    exact Finset.sum_congr rfl fun χ _ => (Finset.mul_sum _ _ _).symm
  -- the first factor, by residue classes
  have h3 : ∑ p ∈ G, (p : ℂ) ^ z * Ph (p % k) = ∑ a ∈ Finset.range k, Ph a * Pa a := by
    have h4 := sum_mul_residue hk G (fun _ => (1 : ℂ)) (fun p => (p : ℂ) ^ z) Ph
    rw [hPa]
    refine Eq.trans (Finset.sum_congr rfl fun p _ => ?_) h4
    rw [one_mul]
  rw [Finset.sum_congr rfl fun p _ => hl p, h3]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hPh, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun χ _ => ?_
  ring

/-- The normalization of a product of three sums. -/
theorem normalize_three (e S₁ S₂ S₃ : ℂ) {R₁ R₂ R₃ : ℝ} (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0)
    (hR₃ : R₃ ≠ 0) (Y : ℝ) :
    (Y : ℂ)⁻¹ * (e * (S₁ * S₂ * S₃)) =
      e * ((R₁ * R₂ * R₃ / Y : ℝ) : ℂ) *
        ((R₁ : ℂ)⁻¹ * S₁ * ((R₂ : ℂ)⁻¹ * S₂) * ((R₃ : ℂ)⁻¹ * S₃)) := by
  have hR₁' : (R₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR₁
  have hR₂' : (R₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR₂
  have hR₃' : (R₃ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR₃
  have key : e * ((R₁ : ℂ) * (R₂ : ℂ) * (R₃ : ℂ) / (Y : ℂ)) *
        ((R₁ : ℂ)⁻¹ * S₁ * ((R₂ : ℂ)⁻¹ * S₂) * ((R₃ : ℂ)⁻¹ * S₃)) =
      ((R₁ : ℂ) * (R₁ : ℂ)⁻¹) * ((R₂ : ℂ) * (R₂ : ℂ)⁻¹) * ((R₃ : ℂ) * (R₃ : ℂ)⁻¹) *
        ((Y : ℂ)⁻¹ * (e * (S₁ * S₂ * S₃))) := by
    ring
  rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_mul, key, mul_inv_cancel₀ hR₁',
    mul_inv_cancel₀ hR₂', mul_inv_cancel₀ hR₃', one_mul, one_mul, one_mul]

/-- **The uncut polynomial of a three-factor box** `{(p, l, u)}` with coefficient `c_u`, where the
second factor is prime to `k`: if every product of the three normalized polynomials with
coefficients `1_{p ≡ a}`, `χ(l)`, `1_{u ≡ b} c_u` has energy `≤ bd`, then the uncut polynomial has
energy `≤ k² · k² · (k |R₁R₂R₃/Y|)² bd`. -/
theorem box_energy_three {k : ℕ} (hk : 0 < k) (h : ℤ) {G J U : Finset ℕ} (hG0 : ∀ p ∈ G, p ≠ 0)
    (hJ0 : ∀ l ∈ J, l ≠ 0) (hU0 : ∀ u ∈ U, u ≠ 0) (hJk : ∀ l ∈ J, l.Coprime k) (c : ℕ → ℂ)
    {W : ℕ} (hW : ∀ p ∈ G, ∀ l ∈ J, ∀ u ∈ U, p * (l * u) ∈ Finset.Icc 1 W) (Y : ℝ)
    {R₁ R₂ R₃ : ℝ} (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0) (hR₃ : R₃ ≠ 0) {lo hi bd : ℝ} (hbd : 0 ≤ bd)
    (hprod : ∀ (a b : ℕ) (χ : DirichletCharacter ℂ k), HighEnergyLe
      (fun t => normPoly R₁ G (fun p => if p ≡ a [MOD k] then (1 : ℂ) else 0) t *
        normPoly R₂ J (fun l => χ (l : ZMod k)) t *
        normPoly R₃ U (fun u => if u ≡ b [MOD k] then c u else 0) t) lo hi bd) :
    HighEnergyLe (endpointPolynomial
        (collapseCoeff G ((J ×ˢ U).image (fun y : ℕ × ℕ => y.1 * y.2)) (fun _ => 1)
          (collapseCoeff J U (fun _ => 1) c)) Y h k) lo hi
      ((k : ℝ) ^ 2 * ((k : ℝ) ^ 2 * (((k : ℝ) * |R₁ * R₂ * R₃ / Y|) ^ 2 * bd))) := by
  obtain ⟨ĉ, hĉ1, hĉ2⟩ := exists_phase_coeff hk h
  have hWout : ∀ x ∈ G ×ˢ (J ×ˢ U).image (fun y : ℕ × ℕ => y.1 * y.2),
      x.1 * x.2 ∈ Finset.Icc 1 W := by
    intro x hx
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp h2
    obtain ⟨hy1, hy2⟩ := Finset.mem_product.mp hy
    have h3 := hW x.1 h1 y.1 hy1 y.2 hy2
    have hyx' : y.1 * y.2 = x.2 := hyx
    rw [hyx'] at h3
    exact h3
  obtain ⟨Pr, hPr⟩ : ∃ Pr : ℕ → ℕ → DirichletCharacter ℂ k → ℝ → ℂ, Pr = fun a b χ t =>
      normPoly R₁ G (fun p => if p ≡ a [MOD k] then (1 : ℂ) else 0) t *
        normPoly R₂ J (fun l => χ (l : ZMod k)) t *
        normPoly R₃ U (fun u => if u ≡ b [MOD k] then c u else 0) t := ⟨_, rfl⟩
  have hPrc : ∀ a b χ, Continuous (Pr a b χ) := by
    intro a b χ
    rw [hPr]
    exact ((continuous_normPoly R₁ hG0 _).mul (continuous_normPoly R₂ hJ0 _)).mul
      (continuous_normPoly R₃ hU0 _)
  have hPrE : ∀ a b χ, HighEnergyLe (Pr a b χ) lo hi bd := by
    intro a b χ
    rw [hPr]
    exact hprod a b χ
  -- the polynomial of the box
  have heq : endpointPolynomial
        (collapseCoeff G ((J ×ˢ U).image (fun y : ℕ × ℕ => y.1 * y.2)) (fun _ => 1)
          (collapseCoeff J U (fun _ => 1) c)) Y h k =
      fun t => ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range k, ∑ χ : DirichletCharacter ℂ k,
        (ĉ a b χ * ((R₁ * R₂ * R₃ / Y : ℝ) : ℂ)) * Pr a b χ t := by
    funext t
    have h1 : ∑ w ∈ Finset.Icc 1 W,
          collapseCoeff G ((J ×ˢ U).image (fun y : ℕ × ℕ => y.1 * y.2)) (fun _ => 1)
            (collapseCoeff J U (fun _ => 1) c) w * addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) *
              (w : ℂ) ^ ((t : ℂ) * Complex.I) =
        ∑ p ∈ G, ∑ l ∈ J, ∑ u ∈ U, c u *
          (addChar ((h : ℝ) * ((p * (l * u) : ℕ) : ℝ) / (k : ℝ)) *
            ((p * (l * u) : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I)) := by
      refine (Finset.sum_congr rfl fun w _ => mul_assoc _ _ _).trans ?_
      refine (sum_collapseCoeff_mul G ((J ×ˢ U).image (fun y : ℕ × ℕ => y.1 * y.2))
        (fun _ => 1) (collapseCoeff J U (fun _ => 1) c)
        (fun w => addChar ((h : ℝ) * (w : ℝ) / (k : ℝ)) * (w : ℂ) ^ ((t : ℂ) * Complex.I))
        hWout).trans ?_
      refine Finset.sum_congr rfl fun p _ => ?_
      have h2 := sum_collapseCoeff_mul J U (fun _ => 1) c
        (fun m => addChar ((h : ℝ) * ((p * m : ℕ) : ℝ) / (k : ℝ)) *
          ((p * m : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I))
        (s := (J ×ˢ U).image (fun y : ℕ × ℕ => y.1 * y.2))
        (fun y hy => Finset.mem_image_of_mem _ hy)
      refine (Finset.sum_congr rfl fun m _ => ?_).trans (h2.trans ?_)
      · rw [one_mul]
      · exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun u _ => by rw [one_mul]
    rw [endpointPolynomial_eq_sum (collapseCoeff_support _ _ hWout) Y h k t, h1,
      sum_triple_addChar hk h G J U hJk c _ ĉ hĉ2, Finset.mul_sum, hPr]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ _ => ?_
    exact normalize_three _ _ _ _ hR₁ hR₂ hR₃ Y
  -- characters
  have hχ : ∀ a b : ℕ, HighEnergyLe
      (fun t => ∑ χ : DirichletCharacter ℂ k,
        (ĉ a b χ * ((R₁ * R₂ * R₃ / Y : ℝ) : ℂ)) * Pr a b χ t) lo hi
      (((k : ℝ) * |R₁ * R₂ * R₃ / Y|) ^ 2 * bd) := by
    intro a b
    refine HighEnergyLe.sum_weighted Finset.univ
      (fun χ => ĉ a b χ * ((R₁ * R₂ * R₃ / Y : ℝ) : ℂ)) (Pr a b) (fun χ _ => hPrc a b χ)
      (fun χ _ => hPrE a b χ) hbd ?_
    have h1 : ∀ χ : DirichletCharacter ℂ k, ‖ĉ a b χ * ((R₁ * R₂ * R₃ / Y : ℝ) : ℂ)‖ =
        ‖ĉ a b χ‖ * |R₁ * R₂ * R₃ / Y| := fun χ => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    show ∑ χ : DirichletCharacter ℂ k, ‖ĉ a b χ * ((R₁ * R₂ * R₃ / Y : ℝ) : ℂ)‖ ≤
      (k : ℝ) * |R₁ * R₂ * R₃ / Y|
    rw [Finset.sum_congr rfl fun χ _ => h1 χ, ← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hĉ1 a b) (abs_nonneg _)
  have hχc : ∀ a b : ℕ, Continuous (fun t => ∑ χ : DirichletCharacter ℂ k,
      (ĉ a b χ * ((R₁ * R₂ * R₃ / Y : ℝ) : ℂ)) * Pr a b χ t) := fun a b =>
    continuous_finsetSum _ fun χ _ => continuous_const.mul (hPrc a b χ)
  have hbd1 : 0 ≤ ((k : ℝ) * |R₁ * R₂ * R₃ / Y|) ^ 2 * bd := mul_nonneg (sq_nonneg _) hbd
  -- the classes of the third factor
  have hb : ∀ a : ℕ, HighEnergyLe
      (fun t => ∑ b ∈ Finset.range k, ∑ χ : DirichletCharacter ℂ k,
        (ĉ a b χ * ((R₁ * R₂ * R₃ / Y : ℝ) : ℂ)) * Pr a b χ t) lo hi
      ((k : ℝ) ^ 2 * (((k : ℝ) * |R₁ * R₂ * R₃ / Y|) ^ 2 * bd)) := by
    intro a
    have h1 := HighEnergyLe.sum (Finset.range k)
      (fun b => fun t => ∑ χ : DirichletCharacter ℂ k,
        (ĉ a b χ * ((R₁ * R₂ * R₃ / Y : ℝ) : ℂ)) * Pr a b χ t)
      (fun b _ => hχc a b) (fun b _ => hχ a b) hbd1
    rw [Finset.card_range] at h1
    exact h1
  have hbc : ∀ a : ℕ, Continuous (fun t => ∑ b ∈ Finset.range k,
      ∑ χ : DirichletCharacter ℂ k, (ĉ a b χ * ((R₁ * R₂ * R₃ / Y : ℝ) : ℂ)) * Pr a b χ t) :=
    fun a => continuous_finsetSum _ fun b _ => hχc a b
  -- the classes of the first factor
  have ha := HighEnergyLe.sum (Finset.range k)
    (fun a => fun t => ∑ b ∈ Finset.range k, ∑ χ : DirichletCharacter ℂ k,
      (ĉ a b χ * ((R₁ * R₂ * R₃ / Y : ℝ) : ℂ)) * Pr a b χ t)
    (fun a _ => hbc a) (fun a _ => hb a) (mul_nonneg (sq_nonneg _) hbd1)
  rw [Finset.card_range] at ha
  rw [heq]
  exact ha

/-! ### Sizes in a box of two dyads -/

/-- The products `p l u` of a box with `p` in the dyad `i` of `G`, `l` in the dyad `j` of `S` and
`u ∈ [R₁, R₂]`. -/
theorem dyad_box_product_three {G S : Finset ℕ} (hG : ∀ p ∈ G, p ≠ 0) (hS : ∀ l ∈ S, l ≠ 0)
    {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) {i j p l u : ℕ} (hp : p ∈ G.filter (fun p => Nat.log 2 p = i))
    (hl : l ∈ S.filter (fun l => Nat.log 2 l = j)) (hu : u ∈ natIcc R₁ R₂) :
    1 ≤ p * (l * u) ∧ (2 : ℝ) ^ i * ((2 : ℝ) ^ j * R₁) ≤ ((p * (l * u) : ℕ) : ℝ) ∧
      ((p * (l * u) : ℕ) : ℝ) ≤ 2 * (2 : ℝ) ^ i * (2 * (2 : ℝ) ^ j * R₂) := by
  have hin := dyad_box_product hS hR₁ (y := (l, u)) (Finset.mem_product.mpr ⟨hl, hu⟩)
  have hin1 : 1 ≤ l * u := hin.1
  have hin2 : (2 : ℝ) ^ j * R₁ ≤ ((l * u : ℕ) : ℝ) := hin.2.1
  have hin3 : ((l * u : ℕ) : ℝ) ≤ 2 * (2 : ℝ) ^ j * R₂ := hin.2.2
  obtain ⟨hpG, hlog⟩ := Finset.mem_filter.mp hp
  have hp0 : p ≠ 0 := hG p hpG
  have hp1 : (2 : ℝ) ^ i ≤ (p : ℝ) := by
    rw [← hlog]
    exact two_pow_log_le hp0
  have hp2 : (p : ℝ) ≤ 2 * (2 : ℝ) ^ i := by
    rw [← hlog]
    exact (lt_two_mul_two_pow_log p).le
  have hpowi : (0 : ℝ) < (2 : ℝ) ^ i := pow_pos two_pos i
  have hpowj : (0 : ℝ) < (2 : ℝ) ^ j := pow_pos two_pos j
  refine ⟨Nat.succ_le_of_lt (Nat.mul_pos (Nat.pos_of_ne_zero hp0)
    (Nat.lt_of_lt_of_le Nat.zero_lt_one hin1)), ?_, ?_⟩
  · rw [Nat.cast_mul]
    exact mul_le_mul hp1 hin2 (mul_nonneg hpowj.le hR₁.le) (Nat.cast_nonneg _)
  · rw [Nat.cast_mul]
    exact mul_le_mul hp2 hin3 (Nat.cast_nonneg _) (mul_nonneg zero_le_two hpowi.le)

/-- `2^i · 2^j · aY/(4 · 2^i · 2^j) = aY/4`. -/
theorem dyad2_scale_lower (a Y : ℝ) (i j : ℕ) :
    (2 : ℝ) ^ i * ((2 : ℝ) ^ j * (a * Y / (4 * (2 : ℝ) ^ i * (2 : ℝ) ^ j))) = a * Y / 4 := by
  have hp : (4 : ℝ) * (2 : ℝ) ^ i * (2 : ℝ) ^ j ≠ 0 :=
    (mul_pos (mul_pos (by norm_num) (pow_pos two_pos i)) (pow_pos two_pos j)).ne'
  rw [eq_div_iff four_ne_zero]
  calc (2 : ℝ) ^ i * ((2 : ℝ) ^ j * (a * Y / (4 * (2 : ℝ) ^ i * (2 : ℝ) ^ j))) * 4
      = a * Y / (4 * (2 : ℝ) ^ i * (2 : ℝ) ^ j) * (4 * (2 : ℝ) ^ i * (2 : ℝ) ^ j) := by ring
    _ = a * Y := div_mul_cancel₀ _ hp

/-- `2 · 2^i · 2 · 2^j · aY/(2^i · 2^j) = 4aY`. -/
theorem dyad2_scale_upper (a Y : ℝ) (i j : ℕ) :
    2 * (2 : ℝ) ^ i * (2 * (2 : ℝ) ^ j * (a * Y / ((2 : ℝ) ^ i * (2 : ℝ) ^ j))) = 4 * a * Y := by
  have hp : (2 : ℝ) ^ i * (2 : ℝ) ^ j ≠ 0 :=
    (mul_pos (pow_pos two_pos i) (pow_pos two_pos j)).ne'
  calc 2 * (2 : ℝ) ^ i * (2 * (2 : ℝ) ^ j * (a * Y / ((2 : ℝ) ^ i * (2 : ℝ) ^ j)))
      = 4 * (a * Y / ((2 : ℝ) ^ i * (2 : ℝ) ^ j) * ((2 : ℝ) ^ i * (2 : ℝ) ^ j)) := by ring
    _ = 4 * (a * Y) := by rw [div_mul_cancel₀ _ hp]
    _ = 4 * a * Y := by ring

/-- The cofactor range of a box of two dyads is automatic: for `a₁Y ≤ w ≤ a₂Y`, `p ∣ w` with
`P ≤ p ≤ 2P` and `l ∣ w/p` with `N ≤ l ≤ 2N`, `w/p/l ∈ [a₁Y/(4PN), a₂Y/(PN)]`. -/
theorem div_div_mem_box {a₁ a₂ Y P N : ℝ} (ha₁ : 0 < a₁) (hY : 0 < Y) (hP : 0 < P) (hN : 0 < N)
    {w p l : ℕ} (hw1 : a₁ * Y ≤ (w : ℝ)) (hw2 : (w : ℝ) ≤ a₂ * Y) (hp1 : P ≤ (p : ℝ))
    (hp2 : (p : ℝ) ≤ 2 * P) (hpw : p ∣ w) (hl1 : N ≤ (l : ℝ)) (hl2 : (l : ℝ) ≤ 2 * N)
    (hlw : l ∣ w / p) : w / p / l ∈ natIcc (a₁ * Y / (4 * P * N)) (a₂ * Y / (P * N)) := by
  have h2P : (0 : ℝ) < 2 * P := mul_pos two_pos hP
  have hm := (mem_natIcc_of_pos (div_pos (mul_pos ha₁ hY) h2P)).mp
    (div_mem_box ha₁ hY hP hw1 hw2 hp1 hp2 hpw)
  have hl0 : (0 : ℝ) < (l : ℝ) := lt_of_lt_of_le hN hl1
  have h4PN : (0 : ℝ) < 4 * P * N := mul_pos (mul_pos (by norm_num) hP) hN
  have hPN : 0 < P * N := mul_pos hP hN
  have hA : 0 < a₁ * Y / (4 * P * N) := div_pos (mul_pos ha₁ hY) h4PN
  have hB0 : 0 ≤ a₂ * Y / (P * N) :=
    div_nonneg (le_trans (Nat.cast_nonneg w) hw2) hPN.le
  have e1 : a₁ * Y / (4 * P * N) * (2 * N) = a₁ * Y / (2 * P) := by
    rw [div_mul_eq_mul_div, div_eq_div_iff h4PN.ne' h2P.ne']
    ring
  have e2 : a₂ * Y / P = a₂ * Y / (P * N) * N := by
    rw [div_mul_eq_mul_div, div_eq_div_iff hP.ne' hPN.ne']
    ring
  refine div_mem_natIcc hl0 hA hlw ?_ ?_
  · calc a₁ * Y / (4 * P * N) * (l : ℝ) ≤ a₁ * Y / (4 * P * N) * (2 * N) :=
          mul_le_mul_of_nonneg_left hl2 hA.le
      _ = a₁ * Y / (2 * P) := e1
      _ ≤ ((w / p : ℕ) : ℝ) := hm.1
  · calc ((w / p : ℕ) : ℝ) ≤ a₂ * Y / P := hm.2
      _ = a₂ * Y / (P * N) * N := e2
      _ ≤ a₂ * Y / (P * N) * (l : ℝ) := mul_le_mul_of_nonneg_left hl1 hB0

/-- A convolution depends only on the values of the coefficient at the cofactors. -/
theorem primeConv_congr {G : Finset ℕ} {F F' : ℕ → ℂ} {w : ℕ}
    (h : ∀ p ∈ G, p ∣ w → F (w / p) = F' (w / p)) : primeConv G F w = primeConv G F' w := by
  unfold primeConv
  exact Finset.sum_congr rfl fun p hp =>
    h p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2

/-! ### Powers of `L` -/

/-- `3L · 3L · 4L · 4L · L^C ≤ L^{|C| + 5}` for `L ≥ 144`. -/
theorem box_bound_numeric_three {L C : ℝ} (hL : 144 ≤ L) :
    3 * L * (3 * L * (4 * L * (4 * L * L ^ C))) ≤ L ^ (|C| + 5) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have h1 : L ^ C ≤ L ^ |C| := Real.rpow_le_rpow_of_exponent_le hL1 (le_abs_self C)
  have h0 : 0 ≤ L ^ |C| := Real.rpow_nonneg hL0.le _
  have hL4 : 0 ≤ L * L * (L * L) :=
    mul_nonneg (mul_nonneg hL0.le hL0.le) (mul_nonneg hL0.le hL0.le)
  have e : L ^ (|C| + 5) = L ^ |C| * (L * (L * L * (L * L))) := by
    rw [Real.rpow_add hL0, show (5 : ℝ) = ((5 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  calc 3 * L * (3 * L * (4 * L * (4 * L * L ^ C))) = 144 * (L * L * (L * L)) * L ^ C := by ring
    _ ≤ 144 * (L * L * (L * L)) * L ^ |C| :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg (by norm_num) hL4)
    _ ≤ L * (L * L * (L * L)) * L ^ |C| :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hL hL4) h0
    _ = L ^ (|C| + 5) := by
        rw [e]
        ring

/-- `L² L² (L^{C₆})⁶ L^{-(A₀ + 4 + 6C₆)} = L^{-A₀}`. -/
theorem rpow_merge_tuple {L C₆ A₀ : ℝ} (hL0 : 0 < L) :
    L ^ 2 * L ^ 2 * ((L ^ C₆) ^ 2 * ((L ^ C₆) ^ 2 * (L ^ C₆) ^ 2)) *
      L ^ (-(A₀ + 4 + 6 * C₆)) = L ^ (-A₀) := by
  have h2 : L ^ 2 = L ^ (2 : ℝ) := (Real.rpow_two L).symm
  have hC : (L ^ C₆) ^ 2 = L ^ (C₆ + C₆) := by rw [pow_two, ← Real.rpow_add hL0]
  rw [h2, hC, ← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0,
    ← Real.rpow_add hL0, ← Real.rpow_add hL0]
  congr 1
  ring

/-- The cost of the two families of dyads, of the residue classes and of the characters:
`(#I)² (#J)² k² k² (k a)² M' L^{-(A₀ + 4 + 6C₆)} ≤ 81 a² M' L^{-A₀}` for `#I, #J ≤ 3L`,
`k ≤ L^{C₆}`. -/
theorem tuple_cost_numeric {L C₆ A₀ a M' cI cJ kk : ℝ} (hL : 1 ≤ L) (hcI0 : 0 ≤ cI)
    (hcI : cI ≤ 3 * L) (hcJ0 : 0 ≤ cJ) (hcJ : cJ ≤ 3 * L) (hk0 : 0 ≤ kk) (hk : kk ≤ L ^ C₆)
    (hM' : 0 ≤ M') :
    cI ^ 2 * (cJ ^ 2 * (kk ^ 2 * (kk ^ 2 * ((kk * a) ^ 2 *
        (M' * L ^ (-(A₀ + 4 + 6 * C₆))))))) ≤ 81 * a ^ 2 * M' * L ^ (-A₀) := by
  have hL0 : 0 < L := by linarith
  have h1 : cI ^ 2 ≤ 9 * L ^ 2 := by
    have h := pow_le_pow_left₀ hcI0 hcI 2
    calc cI ^ 2 ≤ (3 * L) ^ 2 := h
      _ = 9 * L ^ 2 := by ring
  have h1' : cJ ^ 2 ≤ 9 * L ^ 2 := by
    have h := pow_le_pow_left₀ hcJ0 hcJ 2
    calc cJ ^ 2 ≤ (3 * L) ^ 2 := h
      _ = 9 * L ^ 2 := by ring
  have h2 : kk ^ 2 ≤ (L ^ C₆) ^ 2 := pow_le_pow_left₀ hk0 hk 2
  have hk20 : 0 ≤ kk ^ 2 := sq_nonneg _
  have hLC20 : 0 ≤ (L ^ C₆) ^ 2 := sq_nonneg _
  have h9L : 0 ≤ 9 * L ^ 2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : kk ^ 2 * (kk ^ 2 * kk ^ 2) ≤ (L ^ C₆) ^ 2 * ((L ^ C₆) ^ 2 * (L ^ C₆) ^ 2) :=
    mul_le_mul h2 (mul_le_mul h2 h2 hk20 hLC20) (mul_nonneg hk20 hk20) hLC20
  have h4 : cI ^ 2 * cJ ^ 2 ≤ 9 * L ^ 2 * (9 * L ^ 2) := mul_le_mul h1 h1' (sq_nonneg _) h9L
  have h5 : cI ^ 2 * cJ ^ 2 * (kk ^ 2 * (kk ^ 2 * kk ^ 2)) ≤
      9 * L ^ 2 * (9 * L ^ 2) * ((L ^ C₆) ^ 2 * ((L ^ C₆) ^ 2 * (L ^ C₆) ^ 2)) :=
    mul_le_mul h4 h3 (mul_nonneg hk20 (mul_nonneg hk20 hk20)) (mul_nonneg h9L h9L)
  have hrest : 0 ≤ a ^ 2 * M' * L ^ (-(A₀ + 4 + 6 * C₆)) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hM') (Real.rpow_nonneg hL0.le _)
  calc cI ^ 2 * (cJ ^ 2 * (kk ^ 2 * (kk ^ 2 * ((kk * a) ^ 2 *
        (M' * L ^ (-(A₀ + 4 + 6 * C₆)))))))
      = cI ^ 2 * cJ ^ 2 * (kk ^ 2 * (kk ^ 2 * kk ^ 2)) *
          (a ^ 2 * M' * L ^ (-(A₀ + 4 + 6 * C₆))) := by ring
    _ ≤ 9 * L ^ 2 * (9 * L ^ 2) * ((L ^ C₆) ^ 2 * ((L ^ C₆) ^ 2 * (L ^ C₆) ^ 2)) *
          (a ^ 2 * M' * L ^ (-(A₀ + 4 + 6 * C₆))) := mul_le_mul_of_nonneg_right h5 hrest
    _ = 81 * a ^ 2 * M' * (L ^ 2 * L ^ 2 * ((L ^ C₆) ^ 2 * ((L ^ C₆) ^ 2 * (L ^ C₆) ^ 2)) *
          L ^ (-(A₀ + 4 + 6 * C₆))) := by ring
    _ = 81 * a ^ 2 * M' * L ^ (-A₀) := by rw [rpow_merge_tuple hL0]

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
