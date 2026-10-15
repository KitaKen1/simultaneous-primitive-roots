module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.ModelBoundsProof

/-!
# The variance of the normalised array weights (ext:deweight-model)

`modelVariance : ModelBounds q → ModelVariance q` (`[P-07:0641–0648]`), for every real `q`: for
`n ≥ 1` disjoint arrays of `K` bands,

`M_x(Z) = n⁻² ∑_a Var_M(𝒲_a / m_a) ≤ (C_K / c_K²) / n`,

where `Z(u) = ((1/n) ∑_a 𝒲_a(u)/m_a - 1)²` and `c_K ≤ m_a ≤ C_K`, `M_x(𝒲_a²) ≤ C_K` are the
constants of `ModelBounds`. This is the field `modelVariance` of `ExtractionOpenLeaves d H b q q₀`.

* The model on a larger set of primes does not change the mean of a function that does not see
  the new primes (`modelMean_of_subset`, from `modelMean_union_mul` with the second factor `1`).
* The weight of an array does not see a prime outside its bands (`markedWeight_prime_mul`).
* For large `x` the bands of distinct exponents are disjoint (`bandPrimes_disjoint`), so by
  independence (`modelMean_union_mul`) `M_x(𝒲_a) = m_a`, `M_x(𝒲_a 𝒲_{a'}) = m_a m_{a'}` for
  `a ≠ a'`, and `M_x(𝒲_a²)` is the second moment in the model of the array `a`.
* `Z = 1 - (2/n) ∑_a 𝒲_a/m_a + n⁻² ∑_{a,a'} 𝒲_a 𝒲_{a'}/(m_a m_{a'})` (`arrayDeviation_eq`) and the
  linearity of the model give
  `M_x(Z) = 1 - 2 + n⁻² (n(n-1) + ∑_a M_x(𝒲_a²)/m_a²) ≤ (C_K/c_K²)/n`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

open Filter
open scoped Topology

noncomputable section

/-! ### Linearity and restriction of the model -/

/-- The model expectation of a finite sum. -/
theorem modelMean_finset_sum {ι : Type*} (P : Finset ℕ) (s : Finset ι) (f : ι → ℕ → ℝ) :
    modelMean P (fun n => ∑ i ∈ s, f i n) = ∑ i ∈ s, modelMean P (f i) := by
  unfold modelMean
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.mul_sum]

/-- The model expectation of `1 - c₁ F + c₂ G`. -/
theorem modelMean_affine (P : Finset ℕ) (c₁ c₂ : ℝ) (F G : ℕ → ℝ) :
    modelMean P (fun u => 1 - c₁ * F u + c₂ * G u) =
      1 - c₁ * modelMean P F + c₂ * modelMean P G := by
  have e0 : (fun u => 1 - c₁ * F u + c₂ * G u) = fun u => (1 + -c₁ * F u) + c₂ * G u := by
    funext u
    ring
  have e1 : modelMean P (fun u => (1 + -c₁ * F u) + c₂ * G u) =
      modelMean P (fun u => 1 + -c₁ * F u) + modelMean P (fun u => c₂ * G u) :=
    modelMean_add P (fun u => 1 + -c₁ * F u) (fun u => c₂ * G u)
  have e2 : modelMean P (fun u => 1 + -c₁ * F u) =
      modelMean P (fun _ => (1 : ℝ)) + modelMean P (fun u => -c₁ * F u) :=
    modelMean_add P (fun _ => (1 : ℝ)) (fun u => -c₁ * F u)
  have e3 : modelMean P (fun u => -c₁ * F u) = -c₁ * modelMean P F :=
    modelMean_const_mul P (-c₁) F
  have e4 : modelMean P (fun u => c₂ * G u) = c₂ * modelMean P G := modelMean_const_mul P c₂ G
  have e5 : modelMean P (fun _ => (1 : ℝ)) = 1 := modelMean_const P 1
  rw [e0, e1, e2, e3, e4, e5]
  ring

/-- **Restriction**: a function that does not see the primes of `P ∖ A` has the same mean in the
model of `P` as in the model of `A ⊆ P`. -/
theorem modelMean_of_subset {A P : Finset ℕ} (hAP : A ⊆ P) (F : ℕ → ℝ)
    (hF : ∀ p ∈ P \ A, ∀ n, F (p * n) = F n) : modelMean P F = modelMean A F := by
  have hU : A ∪ P \ A = P := Finset.union_sdiff_of_subset hAP
  have h : modelMean (A ∪ P \ A) (fun n => F n * 1) =
      modelMean A F * modelMean (P \ A) (fun _ => (1 : ℝ)) :=
    modelMean_union_mul Finset.disjoint_sdiff (fun _ => (1 : ℝ)) (fun _ _ _ => rfl) F hF
  have hfun : (fun n => F n * 1) = F := funext fun n => mul_one (F n)
  rw [hU, hfun, modelMean_const (P \ A) 1, mul_one] at h
  exact h

/-! ### The weight of an array and the primes of the other arrays -/

/-- The weight of an array does not see a prime outside its bands. -/
theorem markedWeight_prime_mul {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) {p : ℕ} (hp : p.Prime)
    (hpa : p ∉ arrayPrimes 𝔞 x) (q : ℝ) (n : ℕ) :
    markedWeight q 𝔞 x (p * n) = markedWeight q 𝔞 x n := by
  unfold markedWeight
  refine Finset.prod_congr rfl fun i _ => ?_
  refine markFactor_prime_mul (fun ℓ hℓ => (mem_bandPrimes.mp hℓ).1) hp (fun h => hpa ?_) q n
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, h⟩

/-- The primes of the bands of an array are primes. -/
theorem prime_of_mem_arrayPrimes {K : ℕ} {𝔞 : MarkingArray K} {x : ℝ} {p : ℕ}
    (hp : p ∈ arrayPrimes 𝔞 x) : p.Prime := by
  obtain ⟨i, -, hpi⟩ := Finset.mem_biUnion.mp hp
  exact (mem_bandPrimes.mp hpi).1

/-- For a family with distinct exponents, the arrays have disjoint sets of primes once
`2 < L^{a' - a}` for all pairs of exponents `a < a'` of the family. -/
theorem arrayPrimes_disjoint {n K : ℕ} {𝔄 : Fin n → MarkingArray K} (hdisj : ArraysDisjoint 𝔄)
    {x : ℝ} (hL : 0 < Real.log x)
    (hD : ∀ s t : Fin n × Fin K, (𝔄 s.1).exponent s.2 < (𝔄 t.1).exponent t.2 →
      2 < Real.log x ^ ((𝔄 t.1).exponent t.2 - (𝔄 s.1).exponent s.2))
    {a a' : Fin n} (haa' : a ≠ a') :
    Disjoint (arrayPrimes (𝔄 a) x) (arrayPrimes (𝔄 a') x) := by
  have hinj : Function.Injective fun p : Fin n × Fin K => (𝔄 p.1).exponent p.2 := hdisj
  rw [Finset.disjoint_left]
  intro p hp hp'
  obtain ⟨i, -, hpi⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨i', -, hpi'⟩ := Finset.mem_biUnion.mp hp'
  have hne : ((a, i) : Fin n × Fin K) ≠ (a', i') := fun h => haa' (congrArg Prod.fst h)
  have hexp : (𝔄 a).exponent i ≠ (𝔄 a').exponent i' := hinj.ne hne
  rcases lt_or_gt_of_ne hexp with h | h
  · exact Finset.disjoint_left.mp (bandPrimes_disjoint hL (hD (a, i) (a', i') h)) hpi hpi'
  · exact Finset.disjoint_left.mp (bandPrimes_disjoint hL (hD (a', i') (a, i) h)) hpi' hpi

/-! ### The statement -/

/-- **(ext:deweight-model)** (`[P-07:0641–0648]`): the variance of the normalised array weights in
the independent divisor model is at most `(C_K / c_K²) / n`, for every real `q`. This is the field
`modelVariance` of `ExtractionOpenLeaves d H b q q₀`. -/
theorem modelVariance (q : ℝ) (hMB : ModelBounds q) : ModelVariance q := by
  intro K
  obtain ⟨c, C, hc, hbd⟩ := hMB K
  refine ⟨C / c ^ 2, fun n hn 𝔄 hdisj => ?_⟩
  have hevB : ∀ᶠ x : ℝ in atTop, ∀ a : Fin n,
      c ≤ arrayMean q (𝔄 a) x ∧ arrayMean q (𝔄 a) x ≤ C ∧
        modelMean (arrayPrimes (𝔄 a) x) (fun u => markedWeight q (𝔄 a) x u ^ 2) ≤ C :=
    Filter.eventually_all.mpr fun a => hbd (𝔄 a)
  have hevD : ∀ᶠ x : ℝ in atTop, ∀ s t : Fin n × Fin K,
      (𝔄 s.1).exponent s.2 < (𝔄 t.1).exponent t.2 →
        2 < Real.log x ^ ((𝔄 t.1).exponent t.2 - (𝔄 s.1).exponent s.2) := by
    refine Filter.eventually_all.mpr fun s => Filter.eventually_all.mpr fun t => ?_
    by_cases hst : (𝔄 s.1).exponent s.2 < (𝔄 t.1).exponent t.2
    · have hpos : 0 < (𝔄 t.1).exponent t.2 - (𝔄 s.1).exponent s.2 := by linarith
      filter_upwards [((tendsto_rpow_atTop hpos).comp
        Real.tendsto_log_atTop).eventually_gt_atTop 2] with x hx _
      exact hx
    · exact Filter.Eventually.of_forall fun x h => absurd h hst
  filter_upwards [hevB, hevD, Real.tendsto_log_atTop.eventually_gt_atTop 0] with x hB hD hL
  -- the primes of the family
  have hsub : ∀ a : Fin n, arrayPrimes (𝔄 a) x ⊆ familyPrimes 𝔄 x := fun a p hp =>
    Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, hp⟩
  have hPprime : ∀ p ∈ familyPrimes 𝔄 x, p.Prime := by
    intro p hp
    obtain ⟨a, -, hpa⟩ := Finset.mem_biUnion.mp hp
    exact prime_of_mem_arrayPrimes hpa
  have hadisj : ∀ a a' : Fin n, a ≠ a' →
      Disjoint (arrayPrimes (𝔄 a) x) (arrayPrimes (𝔄 a') x) := fun a a' haa' =>
    arrayPrimes_disjoint hdisj hL hD haa'
  -- the three model means
  have hM1 : ∀ a : Fin n, modelMean (familyPrimes 𝔄 x) (markedWeight q (𝔄 a) x) =
      arrayMean q (𝔄 a) x := fun a =>
    modelMean_of_subset (hsub a) (markedWeight q (𝔄 a) x) fun p hp u =>
      markedWeight_prime_mul (𝔄 a) x (hPprime p (Finset.mem_sdiff.mp hp).1)
        (Finset.mem_sdiff.mp hp).2 q u
  have hM2 : ∀ a : Fin n, modelMean (familyPrimes 𝔄 x)
      (fun u => markedWeight q (𝔄 a) x u * markedWeight q (𝔄 a) x u) =
      modelMean (arrayPrimes (𝔄 a) x) (fun u => markedWeight q (𝔄 a) x u ^ 2) := by
    intro a
    have hfun : (fun u => markedWeight q (𝔄 a) x u * markedWeight q (𝔄 a) x u) =
        fun u => markedWeight q (𝔄 a) x u ^ 2 :=
      funext fun u => (sq (markedWeight q (𝔄 a) x u)).symm
    rw [hfun]
    refine modelMean_of_subset (hsub a) (fun u => markedWeight q (𝔄 a) x u ^ 2) fun p hp u => ?_
    have h := markedWeight_prime_mul (𝔄 a) x (hPprime p (Finset.mem_sdiff.mp hp).1)
      (Finset.mem_sdiff.mp hp).2 q u
    show markedWeight q (𝔄 a) x (p * u) ^ 2 = markedWeight q (𝔄 a) x u ^ 2
    rw [h]
  have hM3 : ∀ a a' : Fin n, a ≠ a' → modelMean (familyPrimes 𝔄 x)
      (fun u => markedWeight q (𝔄 a) x u * markedWeight q (𝔄 a') x u) =
      arrayMean q (𝔄 a) x * arrayMean q (𝔄 a') x := by
    intro a a' haa'
    have hd := hadisj a a' haa'
    have hsubU : arrayPrimes (𝔄 a) x ∪ arrayPrimes (𝔄 a') x ⊆ familyPrimes 𝔄 x :=
      Finset.union_subset (hsub a) (hsub a')
    have h1 : modelMean (familyPrimes 𝔄 x)
        (fun u => markedWeight q (𝔄 a) x u * markedWeight q (𝔄 a') x u) =
        modelMean (arrayPrimes (𝔄 a) x ∪ arrayPrimes (𝔄 a') x)
          (fun u => markedWeight q (𝔄 a) x u * markedWeight q (𝔄 a') x u) := by
      refine modelMean_of_subset hsubU
        (fun u => markedWeight q (𝔄 a) x u * markedWeight q (𝔄 a') x u) fun p hp u => ?_
      have hp1 := hPprime p (Finset.mem_sdiff.mp hp).1
      have hp2 := (Finset.mem_sdiff.mp hp).2
      have hpa : p ∉ arrayPrimes (𝔄 a) x := fun h => hp2 (Finset.mem_union_left _ h)
      have hpa' : p ∉ arrayPrimes (𝔄 a') x := fun h => hp2 (Finset.mem_union_right _ h)
      show markedWeight q (𝔄 a) x (p * u) * markedWeight q (𝔄 a') x (p * u) =
        markedWeight q (𝔄 a) x u * markedWeight q (𝔄 a') x u
      rw [markedWeight_prime_mul (𝔄 a) x hp1 hpa q u,
        markedWeight_prime_mul (𝔄 a') x hp1 hpa' q u]
    have h2 : modelMean (arrayPrimes (𝔄 a) x ∪ arrayPrimes (𝔄 a') x)
        (fun u => markedWeight q (𝔄 a) x u * markedWeight q (𝔄 a') x u) =
        modelMean (arrayPrimes (𝔄 a) x) (markedWeight q (𝔄 a) x) *
          modelMean (arrayPrimes (𝔄 a') x) (markedWeight q (𝔄 a') x) :=
      modelMean_union_mul hd (markedWeight q (𝔄 a') x)
        (fun p hp u => markedWeight_prime_mul (𝔄 a') x (prime_of_mem_arrayPrimes hp)
          (Finset.disjoint_left.mp hd hp) q u)
        (markedWeight q (𝔄 a) x)
        (fun p hp u => markedWeight_prime_mul (𝔄 a) x (prime_of_mem_arrayPrimes hp)
          (Finset.disjoint_right.mp hd hp) q u)
    exact h1.trans h2
  -- signs
  have hm0 : ∀ a : Fin n, arrayMean q (𝔄 a) x ≠ 0 := fun a =>
    (lt_of_lt_of_le hc (hB a).1).ne'
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  have hC0 : 0 ≤ C := by
    have h := hB ⟨0, hn⟩
    linarith [h.1, h.2.1]
  have hc2 : 0 < c ^ 2 := pow_pos hc 2
  -- `Z` as a combination of the monomials
  have hZ : arrayDeviation q 𝔄 x = fun u =>
      1 - 2 / (n : ℝ) * (∑ a, 1 / arrayMean q (𝔄 a) x * markedWeight q (𝔄 a) x u) +
        1 / (n : ℝ) ^ 2 * (∑ a, ∑ a', 1 / (arrayMean q (𝔄 a) x * arrayMean q (𝔄 a') x) *
          (markedWeight q (𝔄 a) x u * markedWeight q (𝔄 a') x u)) := by
    funext u
    rw [arrayDeviation_eq]
    simp only [pairWeight_none_none, pairWeight_some_none, pairWeight_some_some]
  -- the linear terms
  have hS1 : modelMean (familyPrimes 𝔄 x)
      (fun u => ∑ a, 1 / arrayMean q (𝔄 a) x * markedWeight q (𝔄 a) x u) = (n : ℝ) := by
    have h : ∀ a ∈ (Finset.univ : Finset (Fin n)), modelMean (familyPrimes 𝔄 x)
        (fun u => 1 / arrayMean q (𝔄 a) x * markedWeight q (𝔄 a) x u) = 1 := fun a _ => by
      rw [modelMean_const_mul, hM1 a]
      exact one_div_mul_cancel (hm0 a)
    rw [modelMean_finset_sum, Finset.sum_congr rfl h, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one]
  -- the quadratic terms
  have hterm : ∀ a a' : Fin n, modelMean (familyPrimes 𝔄 x)
      (fun u => 1 / (arrayMean q (𝔄 a) x * arrayMean q (𝔄 a') x) *
        (markedWeight q (𝔄 a) x u * markedWeight q (𝔄 a') x u)) ≤
      1 + if a = a' then C / c ^ 2 else 0 := by
    intro a a'
    rw [modelMean_const_mul]
    by_cases haa' : a = a'
    · rw [if_pos haa', ← haa', hM2 a]
      have hma := (hB a).1
      have hsq : c ^ 2 ≤ arrayMean q (𝔄 a) x * arrayMean q (𝔄 a) x := by
        rw [sq]
        exact mul_le_mul hma hma hc.le (hc.le.trans hma)
      have hpos : 0 < arrayMean q (𝔄 a) x * arrayMean q (𝔄 a) x := lt_of_lt_of_le hc2 hsq
      calc 1 / (arrayMean q (𝔄 a) x * arrayMean q (𝔄 a) x) *
            modelMean (arrayPrimes (𝔄 a) x) (fun u => markedWeight q (𝔄 a) x u ^ 2)
          ≤ 1 / (arrayMean q (𝔄 a) x * arrayMean q (𝔄 a) x) * C :=
            mul_le_mul_of_nonneg_left (hB a).2.2 (one_div_pos.mpr hpos).le
        _ ≤ 1 / c ^ 2 * C :=
            mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le hc2 hsq) hC0
        _ = C / c ^ 2 := by ring
        _ ≤ 1 + C / c ^ 2 := by linarith
    · rw [if_neg haa', hM3 a a' haa', add_zero]
      exact le_of_eq (one_div_mul_cancel (mul_ne_zero (hm0 a) (hm0 a')))
  have hinner : ∀ a ∈ (Finset.univ : Finset (Fin n)),
      ∑ a' : Fin n, ((1 : ℝ) + if a = a' then C / c ^ 2 else 0) = (n : ℝ) + C / c ^ 2 := by
    intro a _
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos (Finset.mem_univ a),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hS2 : modelMean (familyPrimes 𝔄 x)
      (fun u => ∑ a, ∑ a', 1 / (arrayMean q (𝔄 a) x * arrayMean q (𝔄 a') x) *
        (markedWeight q (𝔄 a) x u * markedWeight q (𝔄 a') x u)) ≤
      (n : ℝ) * ((n : ℝ) + C / c ^ 2) := by
    rw [modelMean_finset_sum]
    calc ∑ a : Fin n, modelMean (familyPrimes 𝔄 x)
          (fun u => ∑ a', 1 / (arrayMean q (𝔄 a) x * arrayMean q (𝔄 a') x) *
            (markedWeight q (𝔄 a) x u * markedWeight q (𝔄 a') x u))
        = ∑ a : Fin n, ∑ a' : Fin n, modelMean (familyPrimes 𝔄 x)
          (fun u => 1 / (arrayMean q (𝔄 a) x * arrayMean q (𝔄 a') x) *
            (markedWeight q (𝔄 a) x u * markedWeight q (𝔄 a') x u)) :=
          Finset.sum_congr rfl fun a _ => modelMean_finset_sum _ _ _
      _ ≤ ∑ a : Fin n, ∑ a' : Fin n, ((1 : ℝ) + if a = a' then C / c ^ 2 else 0) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun a' _ => hterm a a'
      _ = (n : ℝ) * ((n : ℝ) + C / c ^ 2) := by
          rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
  -- conclusion
  rw [hZ, modelMean_affine, hS1]
  have hn2 : 0 ≤ 1 / (n : ℝ) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hS2 hn2
  have hid : 1 - 2 / (n : ℝ) * (n : ℝ) +
      1 / (n : ℝ) ^ 2 * ((n : ℝ) * ((n : ℝ) + C / c ^ 2)) = C / c ^ 2 / (n : ℝ) := by
    have h : (n : ℝ)⁻¹ * (n : ℝ) = 1 := inv_mul_cancel₀ hn0
    generalize C / c ^ 2 = B
    linear_combination ((n : ℝ)⁻¹ * (n : ℝ) - 1 + B * (n : ℝ)⁻¹) * h
  linarith

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
