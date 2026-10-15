module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.CoinLocal

/-!
# The coin step: the model values of the monomials

`[P-07:0441–0449, 0478–0489]`. For a group `g` of primes, with `A_g = ∑_{p ∈ g} a_p` (`sumU`) and
`B_g = ∑_{p ∈ g} b_p` (`sumV`), the model values `mdl j a g` of the monomials `n n'`, `n² n'`,
`n n'²` satisfy

* `mdl_zero_le`, `mdl_zero_ge`: `A_g (B_g - δ) ≤ M(n n') ≤ A_g B_g` when `b_p ≤ δ` on `g`;
* `mdl_one_le`, `mdl_two_le`: `M(n² n') ≤ (1 + A_g) M(n n')`, `M(n n'²) ≤ (1 + B_g) M(n n')`.

Hence the model mean `teeMean` of `T_g = n n' (N₀ + 2 - n - n')` is at least
`(N₀ - A_g - B_g) M(n n')` (`teeMean_ge`), and the sum `teeNorm` of the absolute values of its
terms is at most `(N₀ + 4 + A_g + B_g) M(n n')` (`teeNorm_le`). This replaces the evaluation of
the probability of "exactly one hit of each type" (`[P-07:0478–0486]`).

`dens_union`: the density of the union of two patterns with disjoint supports is the product of
the densities ("distinct groups are independent in the model", `[P-07:0488–0489]`).

The declarations are in the namespace `Extraction.Coin`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Coin

noncomputable section

/-! ### Densities -/

/-- Patterns with disjoint supports are independent in the model. -/
theorem dens_union {j : ℕ} {A A' B B' : Finset ℕ} (h : Disjoint (A ∪ A') (B ∪ B')) :
    dens j (A ∪ B) (A' ∪ B') = dens j A A' * dens j B B' := by
  have hAB : Disjoint A B :=
    Finset.disjoint_of_subset_left Finset.subset_union_left
      (Finset.disjoint_of_subset_right Finset.subset_union_left h)
  have hAB' : Disjoint A B' :=
    Finset.disjoint_of_subset_left Finset.subset_union_left
      (Finset.disjoint_of_subset_right Finset.subset_union_right h)
  have hA'B : Disjoint A' B :=
    Finset.disjoint_of_subset_left Finset.subset_union_right
      (Finset.disjoint_of_subset_right Finset.subset_union_left h)
  have hA'B' : Disjoint A' B' :=
    Finset.disjoint_of_subset_left Finset.subset_union_right
      (Finset.disjoint_of_subset_right Finset.subset_union_right h)
  by_cases h1 : Disjoint A A'
  · by_cases h2 : Disjoint B B'
    · have h3 : Disjoint (A ∪ B) (A' ∪ B') := by
        rw [Finset.disjoint_union_left, Finset.disjoint_union_right,
          Finset.disjoint_union_right]
        exact ⟨⟨h1, hAB'⟩, ⟨hA'B.symm, h2⟩⟩
      rw [dens_of h3, dens_of h1, dens_of h2, Finset.prod_union hAB, Finset.prod_union hA'B']
      ring
    · have h3 : ¬ Disjoint (A ∪ B) (A' ∪ B') := fun hc =>
        h2 (Finset.disjoint_of_subset_left Finset.subset_union_right
          (Finset.disjoint_of_subset_right Finset.subset_union_right hc))
      rw [dens_of_not h3, dens_of_not h2, mul_zero]
  · have h3 : ¬ Disjoint (A ∪ B) (A' ∪ B') := fun hc =>
      h1 (Finset.disjoint_of_subset_left Finset.subset_union_left
        (Finset.disjoint_of_subset_right Finset.subset_union_left hc))
    rw [dens_of_not h3, dens_of_not h1, zero_mul]

/-- The density of `({p}, {q})`. -/
theorem dens_singleton (j p q : ℕ) :
    dens j {p} {q} = if p ≠ q then alphaU j p * alphaV j q else 0 := by
  by_cases h : p = q
  · have hnd : ¬ Disjoint ({p} : Finset ℕ) {q} := fun hc => Finset.disjoint_singleton.mp hc h
    rw [dens_of_not hnd, if_neg (not_not.mpr h)]
  · have hd : Disjoint ({p} : Finset ℕ) {q} := Finset.disjoint_singleton.mpr h
    rw [dens_of hd, if_pos h, Finset.prod_singleton, Finset.prod_singleton]

theorem dens_singleton_le {j : ℕ} (hj : 1 ≤ j) {p q : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) :
    0 ≤ dens j {p} {q} ∧ dens j {p} {q} ≤ alphaU j p * alphaV j q := by
  have hnn : 0 ≤ alphaU j p * alphaV j q := mul_nonneg (alphaU_nonneg hj hp) (alphaV_nonneg hq)
  rw [dens_singleton]
  by_cases h : p ≠ q
  · rw [if_pos h]
    exact ⟨hnn, le_rfl⟩
  · rw [if_neg h]
    exact ⟨le_rfl, hnn⟩

/-- An additional prime on the `u` side costs at most the factor `1_{r = p} + a_r`. -/
theorem dens_pair_left_le {j : ℕ} (hj : 1 ≤ j) {p q r : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hr : 1 ≤ r) :
    dens j {p, r} {q} ≤ ((if r = p then 1 else 0) + alphaU j r) * dens j {p} {q} := by
  have hd0 := (dens_singleton_le hj hp hq).1
  have hr0 := alphaU_nonneg hj hr
  by_cases h : r = p
  · rw [if_pos h, h, Finset.pair_eq_singleton]
    have h1 : (1 : ℝ) ≤ 1 + alphaU j p := by
      rw [h] at hr0
      linarith
    exact le_mul_of_one_le_left hd0 h1
  · rw [if_neg h, zero_add]
    by_cases hd : Disjoint ({p, r} : Finset ℕ) {q}
    · have hq' : q ∉ ({p, r} : Finset ℕ) := Finset.disjoint_singleton_right.mp hd
      have hqp : p ≠ q := fun hc => hq' (by rw [hc]; exact Finset.mem_insert_self q _)
      have hd1 : Disjoint ({p} : Finset ℕ) {q} := Finset.disjoint_singleton.mpr hqp
      rw [dens_of hd, dens_of hd1, Finset.prod_pair (Ne.symm h), Finset.prod_singleton,
        Finset.prod_singleton]
      exact le_of_eq (by ring)
    · rw [dens_of_not hd]
      exact mul_nonneg hr0 hd0

/-- An additional prime on the `u + 1` side costs at most the factor `1_{r = q} + b_r`. -/
theorem dens_pair_right_le {j : ℕ} (hj : 1 ≤ j) {p q r : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hr : 1 ≤ r) :
    dens j {p} {q, r} ≤ ((if r = q then 1 else 0) + alphaV j r) * dens j {p} {q} := by
  have hd0 := (dens_singleton_le hj hp hq).1
  have hr0 := alphaV_nonneg (j := j) hr
  by_cases h : r = q
  · rw [if_pos h, h, Finset.pair_eq_singleton]
    have h1 : (1 : ℝ) ≤ 1 + alphaV j q := by
      rw [h] at hr0
      linarith
    exact le_mul_of_one_le_left hd0 h1
  · rw [if_neg h, zero_add]
    by_cases hd : Disjoint ({p} : Finset ℕ) {q, r}
    · have hp' : p ∉ ({q, r} : Finset ℕ) := Finset.disjoint_singleton_left.mp hd
      have hqp : p ≠ q := fun hc => hp' (by rw [hc]; exact Finset.mem_insert_self q _)
      have hd1 : Disjoint ({p} : Finset ℕ) {q} := Finset.disjoint_singleton.mpr hqp
      rw [dens_of hd, dens_of hd1, Finset.prod_pair (Ne.symm h), Finset.prod_singleton,
        Finset.prod_singleton]
      exact le_of_eq (by ring)
    · rw [dens_of_not hd]
      exact mul_nonneg hr0 hd0

/-! ### The model values of the monomials -/

/-- `A_g = ∑_{p ∈ g} a_p`. -/
def sumU (j : ℕ) (g : Finset ℕ) : ℝ := ∑ p ∈ g, alphaU j p

/-- `B_g = ∑_{p ∈ g} b_p`. -/
def sumV (j : ℕ) (g : Finset ℕ) : ℝ := ∑ p ∈ g, alphaV j p

theorem sumU_nonneg {j : ℕ} (hj : 1 ≤ j) {g : Finset ℕ} (hg : ∀ p ∈ g, 1 ≤ p) :
    0 ≤ sumU j g :=
  Finset.sum_nonneg fun p hp => alphaU_nonneg hj (hg p hp)

theorem sumV_nonneg (j : ℕ) {g : Finset ℕ} (hg : ∀ p ∈ g, 1 ≤ p) : 0 ≤ sumV j g :=
  Finset.sum_nonneg fun p hp => alphaV_nonneg (hg p hp)

theorem mdl_zero_eq (j : ℕ) (g : Finset ℕ) :
    mdl j 0 g = ∑ p ∈ g, ∑ q ∈ g, dens j {p} {q} := by
  have hidx : idx 0 g = g ×ˢ g ×ˢ {0} := by
    unfold idx
    rw [if_pos rfl]
  unfold mdl
  rw [hidx, sum_triple]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  have e1 : patU 0 (p, q, 0) = {p} := if_neg (by decide)
  have e2 : patV 0 (p, q, 0) = {q} := if_neg (by decide)
  rw [Finset.sum_singleton, e1, e2]

theorem mdl_one_eq (j : ℕ) (g : Finset ℕ) :
    mdl j 1 g = ∑ p ∈ g, ∑ q ∈ g, ∑ r ∈ g, dens j {p, r} {q} := by
  have hidx : idx 1 g = g ×ˢ g ×ˢ g := by
    unfold idx
    rw [if_neg (by decide)]
  unfold mdl
  rw [hidx, sum_triple]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun r _ => ?_
  have e1 : patU 1 (p, q, r) = {p, r} := if_pos rfl
  have e2 : patV 1 (p, q, r) = {q} := if_neg (by decide)
  rw [e1, e2]

theorem mdl_two_eq (j : ℕ) (g : Finset ℕ) :
    mdl j 2 g = ∑ p ∈ g, ∑ q ∈ g, ∑ r ∈ g, dens j {p} {q, r} := by
  have hidx : idx 2 g = g ×ˢ g ×ˢ g := by
    unfold idx
    rw [if_neg (by decide)]
  unfold mdl
  rw [hidx, sum_triple]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun r _ => ?_
  have e1 : patU 2 (p, q, r) = {p} := if_neg (by decide)
  have e2 : patV 2 (p, q, r) = {q, r} := if_pos rfl
  rw [e1, e2]

theorem mdl_nonneg {j : ℕ} (hj : 1 ≤ j) (a : Fin 3) {g : Finset ℕ} (hg : ∀ p ∈ g, 1 ≤ p) :
    0 ≤ mdl j a g := by
  unfold mdl
  exact Finset.sum_nonneg fun t ht =>
    dens_nonneg hj (fun p hp => hg p (patU_subset ht hp)) (fun p hp => hg p (patV_subset ht hp))

/-- `M(n n') ≤ A_g B_g`. -/
theorem mdl_zero_le {j : ℕ} (hj : 1 ≤ j) {g : Finset ℕ} (hg : ∀ p ∈ g, 1 ≤ p) :
    mdl j 0 g ≤ sumU j g * sumV j g := by
  rw [mdl_zero_eq]
  unfold sumU sumV
  rw [Finset.sum_mul_sum]
  exact Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun q hq =>
    (dens_singleton_le hj (hg p hp) (hg q hq)).2

/-- `M(n n') ≥ A_g (B_g - δ)` when `b_p ≤ δ` on `g`. -/
theorem mdl_zero_ge {j : ℕ} (hj : 1 ≤ j) {g : Finset ℕ} (hg : ∀ p ∈ g, 1 ≤ p) {δ : ℝ}
    (hδ : ∀ p ∈ g, alphaV j p ≤ δ) : sumU j g * (sumV j g - δ) ≤ mdl j 0 g := by
  rw [mdl_zero_eq]
  have hinner : ∀ p ∈ g, alphaU j p * (sumV j g - δ) ≤ ∑ q ∈ g, dens j {p} {q} := by
    intro p hp
    have e : ∑ q ∈ g, dens j {p} {q} =
        ∑ q ∈ g, (alphaU j p * alphaV j q - if p = q then alphaU j p * alphaV j q else 0) :=
      Finset.sum_congr rfl fun q _ => by
        rw [dens_singleton]
        by_cases h : p = q
        · rw [if_neg (not_not.mpr h), if_pos h, sub_self]
        · rw [if_pos h, if_neg h, sub_zero]
    rw [e, Finset.sum_sub_distrib, Finset.sum_ite_eq, if_pos hp, ← Finset.mul_sum]
    have h1 := mul_le_mul_of_nonneg_left (hδ p hp) (alphaU_nonneg hj (hg p hp))
    have e2 : alphaU j p * (sumV j g - δ) = alphaU j p * sumV j g - alphaU j p * δ := by ring
    rw [e2]
    unfold sumV
    linarith
  unfold sumU
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum hinner

/-- `M(n² n') ≤ (1 + A_g) M(n n')`. -/
theorem mdl_one_le {j : ℕ} (hj : 1 ≤ j) {g : Finset ℕ} (hg : ∀ p ∈ g, 1 ≤ p) :
    mdl j 1 g ≤ (1 + sumU j g) * mdl j 0 g := by
  rw [mdl_one_eq, mdl_zero_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q hq => ?_
  have hsum : ∑ r ∈ g, ((if r = p then (1 : ℝ) else 0) + alphaU j r) = 1 + sumU j g := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hp]
    rfl
  calc ∑ r ∈ g, dens j {p, r} {q}
      ≤ ∑ r ∈ g, ((if r = p then (1 : ℝ) else 0) + alphaU j r) * dens j {p} {q} :=
        Finset.sum_le_sum fun r hr => dens_pair_left_le hj (hg p hp) (hg q hq) (hg r hr)
    _ = (1 + sumU j g) * dens j {p} {q} := by rw [← Finset.sum_mul, hsum]

/-- `M(n n'²) ≤ (1 + B_g) M(n n')`. -/
theorem mdl_two_le {j : ℕ} (hj : 1 ≤ j) {g : Finset ℕ} (hg : ∀ p ∈ g, 1 ≤ p) :
    mdl j 2 g ≤ (1 + sumV j g) * mdl j 0 g := by
  rw [mdl_two_eq, mdl_zero_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun q hq => ?_
  have hsum : ∑ r ∈ g, ((if r = q then (1 : ℝ) else 0) + alphaV j r) = 1 + sumV j g := by
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hq]
    rfl
  calc ∑ r ∈ g, dens j {p} {q, r}
      ≤ ∑ r ∈ g, ((if r = q then (1 : ℝ) else 0) + alphaV j r) * dens j {p} {q} :=
        Finset.sum_le_sum fun r hr => dens_pair_right_le hj (hg p hp) (hg q hq) (hg r hr)
    _ = (1 + sumV j g) * dens j {p} {q} := by rw [← Finset.sum_mul, hsum]

/-! ### The model mean of `T_g` -/

/-- The model mean of `T_g`: `(N₀ + 2) M(n n') - M(n² n') - M(n n'²)`. -/
def teeMean (j : ℕ) (N₀ : ℝ) (g : Finset ℕ) : ℝ := ∑ a, gam N₀ a * mdl j a g

/-- The sum of the absolute values of the terms of the model mean of `T_g`. -/
def teeNorm (j : ℕ) (N₀ : ℝ) (g : Finset ℕ) : ℝ := ∑ a, |gam N₀ a| * mdl j a g

theorem gam_zero (N₀ : ℝ) : gam N₀ 0 = N₀ + 2 := if_pos rfl

theorem gam_one (N₀ : ℝ) : gam N₀ 1 = -1 := if_neg (by decide)

theorem gam_two (N₀ : ℝ) : gam N₀ 2 = -1 := if_neg (by decide)

theorem teeMean_eq (j : ℕ) (N₀ : ℝ) (g : Finset ℕ) :
    teeMean j N₀ g = (N₀ + 2) * mdl j 0 g - mdl j 1 g - mdl j 2 g := by
  unfold teeMean
  rw [Fin.sum_univ_three, gam_zero, gam_one, gam_two]
  ring

theorem teeNorm_eq (j : ℕ) {N₀ : ℝ} (hN₀ : 0 ≤ N₀) (g : Finset ℕ) :
    teeNorm j N₀ g = (N₀ + 2) * mdl j 0 g + mdl j 1 g + mdl j 2 g := by
  unfold teeNorm
  rw [Fin.sum_univ_three, gam_zero, gam_one, gam_two, abs_of_nonneg (by linarith : 0 ≤ N₀ + 2),
    abs_neg, abs_one]
  ring

/-- `M(T_g) ≥ (N₀ - A_g - B_g) M(n n')`. -/
theorem teeMean_ge {j : ℕ} (hj : 1 ≤ j) (N₀ : ℝ) {g : Finset ℕ} (hg : ∀ p ∈ g, 1 ≤ p) :
    (N₀ - sumU j g - sumV j g) * mdl j 0 g ≤ teeMean j N₀ g := by
  rw [teeMean_eq]
  have h1 := mdl_one_le hj hg
  have h2 := mdl_two_le hj hg
  linarith

/-- The terms of `M(T_g)` have total absolute value `≤ (N₀ + 4 + A_g + B_g) M(n n')`. -/
theorem teeNorm_le {j : ℕ} (hj : 1 ≤ j) {N₀ : ℝ} (hN₀ : 0 ≤ N₀) {g : Finset ℕ}
    (hg : ∀ p ∈ g, 1 ≤ p) :
    teeNorm j N₀ g ≤ (N₀ + 4 + sumU j g + sumV j g) * mdl j 0 g := by
  rw [teeNorm_eq j hN₀]
  have h1 := mdl_one_le hj hg
  have h2 := mdl_two_le hj hg
  linarith

theorem teeNorm_nonneg {j : ℕ} (hj : 1 ≤ j) (N₀ : ℝ) {g : Finset ℕ} (hg : ∀ p ∈ g, 1 ≤ p) :
    0 ≤ teeNorm j N₀ g := by
  unfold teeNorm
  exact Finset.sum_nonneg fun a _ => mul_nonneg (abs_nonneg _) (mdl_nonneg hj a hg)

theorem teeMean_le_teeNorm {j : ℕ} (hj : 1 ≤ j) (N₀ : ℝ) {g : Finset ℕ}
    (hg : ∀ p ∈ g, 1 ≤ p) : teeMean j N₀ g ≤ teeNorm j N₀ g := by
  unfold teeMean teeNorm
  exact Finset.sum_le_sum fun a _ =>
    mul_le_mul_of_nonneg_right (le_abs_self _) (mdl_nonneg hj a hg)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Coin
