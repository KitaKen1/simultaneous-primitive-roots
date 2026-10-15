module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.StripTuples
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.StripCoeff

/-!
# The stripping step as a sum over tuples

`[P-07:0347–0386]`: the mass of `|∏_i a(m_i) - ∏_i ã(m_i)|` over the tuples with
`m_1 ⋯ m_j ≤ N`.

* `tuple_difference_le`: if `|a|, |b| ≤ κ ρ` and `|a - b| ≤ κ θ` at the positive integers, if
  `∑_{m ≤ t} ρ(m) ≤ c t` for `t ≤ N`, and if the reciprocal sums of `ρ` and `θ` up to `N` are at
  most `r_ρ` and `r_θ`, then
  `∑_{v ≤ N} ∑_{e_1 ⋯ e_j = v} |∏_i a(e_i) - ∏_i b(e_i)| ≤ j κ^j c N r_θ r_ρ^{j-2}`:
  the product difference is telescoped (`abs_prod_sub_prod_le`), one coordinate carries `θ`, a
  second one is counted, and the remaining `j - 2` are summed with weight `1/m`
  (`tupleSum_le`). The manuscript uses product dyads instead of the hyperbola method.
* `shiftSum_le_of_tuples`: the smooth shifted sum is at most `‖Φ‖_∞` times the sum over
  `v ≤ ⌊R x⌋ + 1`.
* `strip_sum_le`: the two combined, for the proxy and the stripped coefficient.

The declarations are in the namespace `Extraction.Strip`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Strip

noncomputable section

/-- **The tuple sum of a product difference.** -/
theorem tuple_difference_le {j : ℕ} (hj : 2 ≤ j) (N : ℕ) (a b ρ θ : ℕ → ℝ) {κ c rρ rθ : ℝ}
    (hκ : 0 ≤ κ) (hρ0 : ∀ m, 0 ≤ ρ m) (hθ0 : ∀ m, 0 ≤ θ m)
    (ha : ∀ m, m ≠ 0 → |a m| ≤ κ * ρ m) (hb : ∀ m, m ≠ 0 → |b m| ≤ κ * ρ m)
    (hd : ∀ m, m ≠ 0 → |a m - b m| ≤ κ * θ m) (hc : 0 ≤ c)
    (hcount : ∀ t : ℕ, t ≤ N → ∑ m ∈ Finset.Icc 1 t, ρ m ≤ c * (t : ℝ))
    (hrρ : ∑ m ∈ Finset.Icc 1 N, ρ m / (m : ℝ) ≤ rρ)
    (hrθ : ∑ m ∈ Finset.Icc 1 N, θ m / (m : ℝ) ≤ rθ) :
    ∑ v ∈ Finset.Icc 1 N, ∑ e ∈ orderedFactorizations j v,
        |∏ i, a (e i) - ∏ i, b (e i)| ≤
      (j : ℝ) * (κ ^ j * (c * (N : ℝ) * (rθ * rρ ^ (j - 2)))) := by
  rw [sum_orderedFactorizations_eq j N fun e => |∏ i, a (e i) - ∏ i, b (e i)|]
  -- the product difference at one tuple
  have hterm : ∀ e ∈ Fintype.piFinset (fun _ : Fin j => Finset.Icc 1 N),
      (if ∏ i, e i ≤ N then |∏ i, a (e i) - ∏ i, b (e i)| else 0) ≤
        ∑ i : Fin j, κ ^ j *
          (if ∏ k, e k ≤ N then ∏ k, (if k = i then θ (e k) else ρ (e k)) else 0) := by
    intro e he
    have he1 : ∀ i, e i ≠ 0 := fun i =>
      Nat.pos_iff_ne_zero.mp (Finset.mem_Icc.mp (Fintype.mem_piFinset.mp he i)).1
    by_cases hp : ∏ i, e i ≤ N
    · rw [if_pos hp]
      have h1 := abs_prod_sub_prod_le Finset.univ (fun i => a (e i)) (fun i => b (e i))
        (fun i => κ * ρ (e i)) (fun i => κ * θ (e i)) (fun i _ => ha _ (he1 i))
        (fun i _ => hb _ (he1 i)) (fun i _ => hd _ (he1 i))
      refine h1.trans (Finset.sum_le_sum fun i _ => ?_)
      rw [if_pos hp]
      have h2 : ∀ k : Fin j, (if k = i then κ * θ (e k) else κ * ρ (e k)) =
          κ * (if k = i then θ (e k) else ρ (e k)) := fun k => (mul_ite _ _ _ _).symm
      rw [Finset.prod_congr rfl fun k _ => h2 k, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.card_univ, Fintype.card_fin]
    · rw [if_neg hp]
      refine Finset.sum_nonneg fun i _ => ?_
      rw [if_neg hp, mul_zero]
  -- one position of `θ`
  have hi : ∀ i : Fin j, ∑ e ∈ Fintype.piFinset (fun _ : Fin j => Finset.Icc 1 N),
      κ ^ j * (if ∏ k, e k ≤ N then ∏ k, (if k = i then θ (e k) else ρ (e k)) else 0) ≤
        κ ^ j * (c * (N : ℝ) * (rθ * rρ ^ (j - 2))) := by
    intro i
    rw [← Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hκ j)
    have : Nontrivial (Fin j) := Fin.nontrivial_iff_two_le.mpr hj
    obtain ⟨i₀, hi₀⟩ := exists_ne i
    have hw0 : ∀ (k : Fin j) (m : ℕ), 0 ≤ (if k = i then θ m else ρ m) := fun k m => by
      by_cases hk : k = i
      · rw [if_pos hk]
        exact hθ0 m
      · rw [if_neg hk]
        exact hρ0 m
    have e1 : ∀ m : ℕ, (if i₀ = i then θ m else ρ m) = ρ m := fun m => if_neg hi₀
    have hcnt : ∀ t : ℕ, t ≤ N →
        ∑ m ∈ Finset.Icc 1 t, (if i₀ = i then θ m else ρ m) ≤ c * (t : ℝ) := fun t ht => by
      rw [Finset.sum_congr rfl fun m _ => e1 m]
      exact hcount t ht
    have hrec : ∀ k : Fin j, k ≠ i₀ →
        ∑ m ∈ Finset.Icc 1 N, (if k = i then θ m else ρ m) / (m : ℝ) ≤
          (if k = i₀ then 1 else if k = i then rθ else rρ) := fun k hk => by
      rw [if_neg hk]
      by_cases hki : k = i
      · have e2 : ∀ m : ℕ, (if k = i then θ m else ρ m) / (m : ℝ) = θ m / (m : ℝ) :=
          fun m => by rw [if_pos hki]
        rw [if_pos hki, Finset.sum_congr rfl fun m _ => e2 m]
        exact hrθ
      · have e2 : ∀ m : ℕ, (if k = i then θ m else ρ m) / (m : ℝ) = ρ m / (m : ℝ) :=
          fun m => by rw [if_neg hki]
        rw [if_neg hki, Finset.sum_congr rfl fun m _ => e2 m]
        exact hrρ
    have hr1 : (1 : ℝ) ≤ (if i₀ = i₀ then 1 else if i₀ = i then rθ else rρ) := by
      rw [if_pos rfl]
    have h := tupleSum_le N j (fun k m => if k = i then θ m else ρ m)
      (fun k => if k = i₀ then 1 else if k = i then rθ else rρ) i₀ c hw0 hc hcnt hrec hr1 N
      le_rfl
    rw [prod_ite_two hi₀ rθ rρ] at h
    exact h
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_le_sum fun i _ => hi i).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The smooth shifted sum of a nonnegative function of `u + 1` is at most `‖Φ‖_∞` times its sum
over `1 ≤ v ≤ ⌊R x⌋ + 1`. -/
theorem shiftSum_le_of_tuples {Φ : ℝ → ℝ} {R Bφ x : ℝ} (hR : ∀ t, R < t → Φ t = 0)
    (hB : ∀ t, Φ t ≤ Bφ) (hx : 0 < x) (G : ℕ → ℝ) (hG : ∀ v, 0 ≤ G v) :
    shiftSum Φ x (fun _ => True) (fun u => G (u + 1)) ≤
      Bφ * ∑ v ∈ Finset.Icc 1 (⌊R * x⌋₊ + 1), G v := by
  rw [shiftSum_eq_sum hR hx, ← sum_range_succ_eq_sum_Icc, Finset.mul_sum]
  refine Finset.sum_le_sum fun u _ => ?_
  refine (le_of_eq (if_pos trivial)).trans ?_
  exact mul_le_mul_of_nonneg_right (hB _) (hG _)

/-- **The stripping step at one `x`** (`[P-07:0347–0386]`), in terms of the count and the
reciprocal sums of the weights `ρ` and `θ`. -/
theorem strip_sum_le {Φ : ℝ → ℝ} {R Bφ : ℝ} (hR : ∀ t, R < t → Φ t = 0) (hB : ∀ t, Φ t ≤ Bφ)
    (hB0 : 0 ≤ Bφ) {x γ ℓ Λ₀ Λ ε₀ c rρ rθ : ℝ} {P : Finset ℕ} {j : ℕ} (hj : 2 ≤ j)
    (hx : 0 < x) (hA : 1 ≤ x ^ γ) (hℓ : 0 < ℓ) (hlog : Real.log (x ^ γ) = ℓ) (hΛ : 0 ≤ Λ)
    (hε : ε₀ = Λ / ℓ)
    (hgood : ∀ m : ℕ, m ≠ 0 → Good P Λ₀ m → (m : ℝ) ≤ (freePart P m : ℝ) * Real.exp Λ)
    (hc : 0 ≤ c)
    (hcount : ∀ t : ℕ, t ≤ ⌊R * x⌋₊ + 1 → ∑ m ∈ Finset.Icc 1 t, rhoW x γ m ≤ c * (t : ℝ))
    (hrρ : ∑ m ∈ Finset.Icc 1 (⌊R * x⌋₊ + 1), rhoW x γ m / (m : ℝ) ≤ rρ)
    (hrθ : ∑ m ∈ Finset.Icc 1 (⌊R * x⌋₊ + 1), thetaW x γ P Λ₀ Λ ε₀ m / (m : ℝ) ≤ rθ) :
    shiftSum Φ x (fun _ => True)
        (fun u => ∑ e ∈ orderedFactorizations j (u + 1),
          |∏ i, proxyCoeff x γ (e i) - ∏ i, strippedCoeff x γ P (e i)|) ≤
      Bφ * ((j : ℝ) * ((1 / (mertensProduct (roughCutoff x) * ℓ)) ^ j *
        (c * ((⌊R * x⌋₊ + 1 : ℕ) : ℝ) * (rθ * rρ ^ (j - 2))))) := by
  have hε0 : 0 ≤ ε₀ := by
    rw [hε]
    exact div_nonneg hΛ hℓ.le
  have hκ : 0 ≤ 1 / (mertensProduct (roughCutoff x) * ℓ) :=
    (one_div_pos.mpr (mul_pos (mertensProduct_pos _) hℓ)).le
  refine (shiftSum_le_of_tuples hR hB hx
    (fun v => ∑ e ∈ orderedFactorizations j v,
      |∏ i, proxyCoeff x γ (e i) - ∏ i, strippedCoeff x γ P (e i)|)
    (fun v => Finset.sum_nonneg fun e _ => abs_nonneg _)).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ hB0
  exact tuple_difference_le hj (⌊R * x⌋₊ + 1) (proxyCoeff x γ) (strippedCoeff x γ P)
    (rhoW x γ) (thetaW x γ P Λ₀ Λ ε₀) hκ (rhoW_nonneg x γ)
    (thetaW_nonneg hε0 x γ P Λ₀ Λ)
    (fun m hm => (coeff_bounds hA hℓ hlog hΛ hε hgood hm).1)
    (fun m hm => (coeff_bounds hA hℓ hlog hΛ hε hgood hm).2.1)
    (fun m hm => (coeff_bounds hA hℓ hlog hΛ hε hgood hm).2.2) hc hcount hrρ hrθ

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Strip
