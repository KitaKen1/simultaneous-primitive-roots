module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.ProgressionExpansion
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.ProgressionCount
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.ProgressionModel

/-!
# One modulus of Lemma 7.2

`abs_shiftSum_family_sub_model_le`: the estimate of [P] Lemma 7.2 (`[P-07:0148–0188]`) for one
modulus `r` coprime to `H`, with explicit error terms and no asymptotics.

Data: a cutoff `Φ` (vanishing beyond `R`, with the constant `C_Φ` of (ext:crt-count)); a finite
set `𝒬` of primes not dividing `H` (the primes of the arrays); a function `G` with `|G| ≤ H_b`
that depends on `u` only through `{p ∈ 𝒬 : p ∣ u}` (a monomial of the array weights); a finite
family of integers `ℓ_i ≥ 1` coprime to `r`, `H` and the primes of `𝒬` (the products of the
long-prime tuples, with `f(u) = #{i : ℓ_i ∣ u}` and `C = ∑_i 1/ℓ_i`; or the single integer `1`);
a truncation degree `k`. With `P = {p ∈ 𝒬 : p ∤ r}` and `X = x/(H r) (∫Φ) C`:

`| ∑_{u, r ∣ u+1, u+1 ≡ b (H)} Φ(u/x) f(u) G(u) - X M_𝒬(G) |
  ≤ H_b (#I · C_Φ · (∑_{D ⊆ P, |D| < k} 2^{|D|} + ∑_{E ⊆ P, |E| = k} 2^{|E|})
        + 2 X ∑_{E ⊆ P, |E| = k} ∏_{p ∈ E} 2/p) + X · 2 H_b ∑_{p ∈ 𝒬, p ∣ r} 1/p`.

The three terms are the rounding errors of (ext:crt-count), the truncation error
(ext:bonferroni-tail) and the forced absence of the primes dividing `r`.

* On the progression `r ∣ u + 1` no prime of `𝒬` dividing `r` divides `u`
  (`not_dvd_of_dvd_succ`), so `G(u) = F(S_u)` with `S_u = {p ∈ P : p ∣ u}` and
  `F(T) = G(∏_{p ∈ T} p)`: "the model in which the band primes dividing `r` are forced absent".
* The weighted counts of `{u : D ⊆ S_u}` are the counts of the multiples of `∏D`
  (`abs_shiftSum_family_dvd_sub_le`), and the truncated expansion with its binomial envelope
  (`abs_weighted_sub_model_le`) compares the sum with `X M_P(G)`.
* `M_P(G)` and `M_𝒬(G)` differ by at most `2 H_b ∑_{p ∈ 𝒬, p ∣ r} 1/p`
  (`abs_modelMean_union_sub_le`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Progression

open MeasureTheory

noncomputable section

/-- A prime dividing `u` does not divide a divisor `r` of `u + 1`. -/
theorem not_dvd_of_dvd_succ {p r u : ℕ} (hp : p.Prime) (hpu : p ∣ u) (hr : r ∣ u + 1) :
    ¬ p ∣ r := by
  intro hpr
  have h1 : p ∣ u + 1 := hpr.trans hr
  have h2 : p ∣ 1 := (Nat.dvd_add_right hpu).mp h1
  exact hp.one_lt.ne' (Nat.dvd_one.mp h2)

/-- **One modulus of Lemma 7.2**, with explicit error terms. -/
theorem abs_shiftSum_family_sub_model_le
    {Φ : ℝ → ℝ} {R CΦ : ℝ} (hR : ∀ t, R < t → Φ t = 0) (hΦ0 : ∀ t, 0 ≤ Φ t)
    (hC : ∀ x : ℝ, 0 < x → ∀ ℓ m a : ℕ, 0 < ℓ → 0 < m →
      |(∑ᶠ y : ℕ, if y ≡ a [MOD m] then Φ ((ℓ : ℝ) * (y : ℝ) / x) else 0) -
        x / ((ℓ : ℝ) * (m : ℝ)) * ∫ t, Φ t| ≤ CΦ)
    {x : ℝ} (hx : 0 < x) {H r : ℕ} (hH : 0 < H) (hr : 0 < r) (hrH : r.Coprime H) (b : ℕ)
    {𝒬 : Finset ℕ} (h𝒬 : ∀ p ∈ 𝒬, p.Prime) (h𝒬H : ∀ p ∈ 𝒬, ¬ p ∣ H)
    {G : ℕ → ℝ} {Hb : ℝ} (hG : ∀ u, |G u| ≤ Hb)
    (hGinv : ∀ u u' : ℕ, (∀ p ∈ 𝒬, (p ∣ u ↔ p ∣ u')) → G u = G u')
    {ι : Type*} (I : Finset ι) (ℓ : ι → ℕ) (hℓ0 : ∀ i ∈ I, 0 < ℓ i)
    (hℓr : ∀ i ∈ I, (ℓ i).Coprime r) (hℓH : ∀ i ∈ I, (ℓ i).Coprime H)
    (hℓ𝒬 : ∀ i ∈ I, ∀ p ∈ 𝒬, (ℓ i).Coprime p) (k : ℕ) :
    |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H])
        (fun u => (∑ i ∈ I, if ℓ i ∣ u then (1 : ℝ) else 0) * G u) -
      x / ((H : ℝ) * (r : ℝ)) * (∫ t, Φ t) * (∑ i ∈ I, 1 / (ℓ i : ℝ)) * modelMean 𝒬 G| ≤
      Hb * ((I.card : ℝ) * CΦ *
          (∑ D ∈ (𝒬.filter fun p => ¬ p ∣ r).powerset.filter (fun D => D.card < k),
              (2 : ℝ) ^ D.card +
            ∑ E ∈ (𝒬.filter fun p => ¬ p ∣ r).powersetCard k, (2 : ℝ) ^ E.card) +
        2 * (x / ((H : ℝ) * (r : ℝ)) * (∫ t, Φ t) * (∑ i ∈ I, 1 / (ℓ i : ℝ))) *
          ∑ E ∈ (𝒬.filter fun p => ¬ p ∣ r).powersetCard k, ∏ p ∈ E, (2 / (p : ℝ))) +
      x / ((H : ℝ) * (r : ℝ)) * (∫ t, Φ t) * (∑ i ∈ I, 1 / (ℓ i : ℝ)) *
        (2 * Hb * ∑ p ∈ 𝒬.filter (fun p => p ∣ r), 1 / (p : ℝ)) := by
  obtain ⟨P, hPdef⟩ : ∃ P : Finset ℕ, P = 𝒬.filter fun p => ¬ p ∣ r := ⟨_, rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ,
      X = x / ((H : ℝ) * (r : ℝ)) * (∫ t, Φ t) * (∑ i ∈ I, 1 / (ℓ i : ℝ)) := ⟨_, rfl⟩
  rw [← hPdef, ← hXdef]
  have hP𝒬 : P ⊆ 𝒬 := by
    rw [hPdef]
    exact Finset.filter_subset _ _
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp => h𝒬 p (hP𝒬 hp)
  have hPr : ∀ p ∈ P, ¬ p ∣ r := fun p hp => by
    rw [hPdef] at hp
    exact (Finset.mem_filter.mp hp).2
  have hint : 0 ≤ ∫ t, Φ t := MeasureTheory.integral_nonneg fun t => hΦ0 t
  have hX : 0 ≤ X := by
    rw [hXdef]
    exact mul_nonneg (mul_nonneg (div_nonneg hx.le (by positivity)) hint)
      (Finset.sum_nonneg fun i _ => by positivity)
  -- the function of the set of marked primes
  obtain ⟨F, hF⟩ : ∃ F : Finset ℕ → ℝ, ∀ T, F T = G (∏ p ∈ T, p) :=
    ⟨fun T => G (∏ p ∈ T, p), fun _ => rfl⟩
  have hFb : ∀ D ⊆ P, |F D| ≤ Hb := fun D _ => by
    rw [hF D]
    exact hG _
  -- `G(u) = F(S_u)` on the progression
  have hGF : ∀ u : ℕ, r ∣ u + 1 → G u = F (P.filter fun p => p ∣ u) := by
    intro u hu
    rw [hF]
    refine hGinv u _ fun p hp => ⟨fun hpu => ?_, fun hpd => ?_⟩
    · have hpP : p ∈ P := by
        rw [hPdef]
        exact Finset.mem_filter.mpr ⟨hp, not_dvd_of_dvd_succ (h𝒬 p hp) hpu hu⟩
      exact Finset.dvd_prod_of_mem (fun p' : ℕ => p') (Finset.mem_filter.mpr ⟨hpP, hpu⟩)
    · have hmem := EndpointProof.mem_of_prime_dvd_prod_primes
        (fun p' hp' => hPprime p' (Finset.mem_filter.mp hp').1) (h𝒬 p hp) hpd
      exact (Finset.mem_filter.mp hmem).2
  -- the weights
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, ∀ u, g u = ∑ i ∈ I, if ℓ i ∣ u then (1 : ℝ) else 0 :=
    ⟨fun u => ∑ i ∈ I, if ℓ i ∣ u then (1 : ℝ) else 0, fun _ => rfl⟩
  have hg0 : ∀ u, 0 ≤ g u := fun u => by
    rw [hg u]
    refine Finset.sum_nonneg fun i _ => ?_
    by_cases h : ℓ i ∣ u
    · rw [if_pos h]
      exact zero_le_one
    · rw [if_neg h]
  obtain ⟨N, w, hw0, hwP, hwsum⟩ :=
    exists_shiftSum_weights hR hx hΦ0 (fun v => r ∣ v ∧ v ≡ b [MOD H]) hg0
  have hA : shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H])
      (fun u => (∑ i ∈ I, if ℓ i ∣ u then (1 : ℝ) else 0) * G u) =
      ∑ u ∈ Finset.range N, w u * F (P.filter fun p => p ∣ u) := by
    have hcongr : ∀ u, (∑ i ∈ I, if ℓ i ∣ u then (1 : ℝ) else 0) * G u = g u * G u :=
      fun u => by rw [hg u]
    rw [shiftSum_congr Φ x _ hcongr, hwsum G]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hwu : w u = 0
    · rw [hwu, zero_mul, zero_mul]
    · rw [hGF u (hwP u hwu).1]
  -- the counts of the supersets
  have hcount : ∀ D ⊆ P, D.card ≤ k →
      |∑ u ∈ Finset.range N, (if D ⊆ (P.filter fun p => p ∣ u) then w u else 0) -
        X * ∏ p ∈ D, (1 / (p : ℝ))| ≤ (I.card : ℝ) * CΦ := by
    intro D hDP _
    have hDprime : ∀ p ∈ D, p.Prime := fun p hp => hPprime p (hDP hp)
    obtain ⟨e, he⟩ : ∃ e : ℕ, e = ∏ p ∈ D, p := ⟨_, rfl⟩
    have he0 : 0 < e := by
      rw [he]
      exact Finset.prod_pos fun p hp => (hDprime p hp).pos
    have her : e.Coprime r := by
      rw [he]
      exact Nat.Coprime.prod_left fun p hp =>
        ((hDprime p hp).coprime_iff_not_dvd).mpr (hPr p (hDP hp))
    have heH : e.Coprime H := by
      rw [he]
      exact Nat.Coprime.prod_left fun p hp =>
        ((hDprime p hp).coprime_iff_not_dvd).mpr (h𝒬H p (hP𝒬 (hDP hp)))
    have hℓe : ∀ i ∈ I, (ℓ i).Coprime e := fun i hi => by
      rw [he]
      exact Nat.Coprime.prod_right fun p hp => hℓ𝒬 i hi p (hP𝒬 (hDP hp))
    have hiff : ∀ u : ℕ, D ⊆ (P.filter fun p => p ∣ u) ↔ e ∣ u := by
      intro u
      rw [he]
      constructor
      · intro h
        exact Finset.prod_primes_dvd u (fun p hp => (hDprime p hp).prime)
          fun p hp => (Finset.mem_filter.mp (h hp)).2
      · intro h p hp
        exact Finset.mem_filter.mpr
          ⟨hDP hp, (Finset.dvd_prod_of_mem (fun p' : ℕ => p') hp).trans h⟩
    have hsum : ∑ u ∈ Finset.range N, (if D ⊆ (P.filter fun p => p ∣ u) then w u else 0) =
        shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H])
          (fun u => (∑ i ∈ I, if ℓ i ∣ u then (1 : ℝ) else 0) *
            (if e ∣ u then (1 : ℝ) else 0)) := by
      have hcongr : ∀ u, (∑ i ∈ I, if ℓ i ∣ u then (1 : ℝ) else 0) *
          (if e ∣ u then (1 : ℝ) else 0) = g u * (if e ∣ u then (1 : ℝ) else 0) :=
        fun u => by rw [hg u]
      rw [shiftSum_congr Φ x _ hcongr, hwsum fun u => if e ∣ u then (1 : ℝ) else 0]
      refine Finset.sum_congr rfl fun u _ => ?_
      by_cases h : e ∣ u
      · rw [if_pos ((hiff u).mpr h), if_pos h, mul_one]
      · have h' : ¬ D ⊆ (P.filter fun p => p ∣ u) := fun h' => h ((hiff u).mp h')
        rw [if_neg h', if_neg h, mul_zero]
    have hprod : X * ∏ p ∈ D, (1 / (p : ℝ)) = X * (1 / (e : ℝ)) := by
      rw [he, Nat.cast_prod, Finset.prod_div_distrib, Finset.prod_const_one]
    rw [hsum, hprod, hXdef]
    exact abs_shiftSum_family_dvd_sub_le hR hC hx hr hH hrH b I ℓ he0 her heH hℓ0 hℓr hℓH hℓe
  -- comparison with the model on `P`
  have hB : |∑ u ∈ Finset.range N, w u * F (P.filter fun p => p ∣ u) - X * modelMean P G| ≤
      Hb * ((I.card : ℝ) * CΦ *
          (∑ D ∈ P.powerset.filter (fun D => D.card < k), (2 : ℝ) ^ D.card +
            ∑ E ∈ P.powersetCard k, (2 : ℝ) ^ E.card) +
        2 * X * ∑ E ∈ P.powersetCard k, ∏ p ∈ E, (2 / (p : ℝ))) := by
    have hmodel : modelMean P G = ∑ T ∈ P.powerset, modelWeight P T * F T := by
      rw [modelMean_eq_sum_modelWeight]
      exact Finset.sum_congr rfl fun T _ => by rw [hF T]
    rw [hmodel]
    exact abs_weighted_sub_model_le (Finset.range N) w (fun u => P.filter fun p => p ∣ u) P k F
      Hb X ((I.card : ℝ) * CΦ) (fun p hp => (hPprime p hp).one_lt.le) (fun u _ => hw0 u)
      (fun u _ => Finset.filter_subset _ _) hFb hX hcount
  -- forced absence of the primes dividing `r`
  have hforce : |modelMean 𝒬 G - modelMean P G| ≤
      2 * Hb * ∑ p ∈ 𝒬.filter (fun p => p ∣ r), 1 / (p : ℝ) := by
    have hU : P ∪ 𝒬.filter (fun p => p ∣ r) = 𝒬 := by
      rw [hPdef]
      ext p
      simp only [Finset.mem_union, Finset.mem_filter]
      constructor
      · rintro (h | h)
        · exact h.1
        · exact h.1
      · intro h
        by_cases hpr : p ∣ r
        · exact Or.inr ⟨h, hpr⟩
        · exact Or.inl ⟨h, hpr⟩
    have hdisj : Disjoint P (𝒬.filter fun p => p ∣ r) := by
      rw [Finset.disjoint_left]
      intro p hp hp'
      exact hPr p hp (Finset.mem_filter.mp hp').2
    have h := abs_modelMean_union_sub_le (fun p hp => (hPprime p hp).one_lt.le) hG
      (𝒬.filter fun p => p ∣ r) hdisj
      (fun p hp => (h𝒬 p (Finset.mem_filter.mp hp).1).one_lt.le)
    rw [hU] at h
    exact h
  have hsplit : ∑ u ∈ Finset.range N, w u * F (P.filter fun p => p ∣ u) - X * modelMean 𝒬 G =
      (∑ u ∈ Finset.range N, w u * F (P.filter fun p => p ∣ u) - X * modelMean P G) -
        X * (modelMean 𝒬 G - modelMean P G) := by ring
  have h3 : |X * (modelMean 𝒬 G - modelMean P G)| ≤
      X * (2 * Hb * ∑ p ∈ 𝒬.filter (fun p => p ∣ r), 1 / (p : ℝ)) := by
    rw [abs_mul, abs_of_nonneg hX]
    exact mul_le_mul_of_nonneg_left hforce hX
  rw [hA, hsplit]
  exact (abs_sub _ _).trans (add_le_add hB h3)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Progression
