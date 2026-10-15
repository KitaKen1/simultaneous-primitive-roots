module

public import SimultaneousPrimitiveRoots.Artin.Density
public import SimultaneousPrimitiveRoots.Explicit.KummerZetaGRH

/-!
# From dyadic to cumulative density: Artin's conjecture with density under GRH

* `tendsto_dyadicPrimes`: the prime number theorem in dyadic form,
  `#{p ∈ (x, 2x]} / (x / log x) → 1` (Tau Ceti's Chebotarev theorem for `ℚ / ℚ`).
* `tendsto_div_of_dyadic`: if two counting functions `A ≤`-grow with dyadic increments in ratio
  `→ δ` and `B → ∞`, then `A(x) / B(x) → δ` (induction along `x ↦ x / 2`).
* `primitiveRoot_density_of_grhSplitting`: for `a ≥ 2` not a square, under the GRH splitting
  estimate,
  `#{p < N : p prime, a primitive root mod p} / #{p < N : p prime} → δ_a > 0`.
* `primitiveRoot_density_of_dedekindZetaGRH`: the same under GRH for the Dedekind zeta functions
  of the Kummer fields `ℚ(ζ_q, a^{1/q})`, `q > a` prime.

This is the positive-integer case of Formal Conjectures'
`conditional_artin_primitive_roots.parts.i` (Hooley 1967), under a weaker hypothesis (prime `q`
only, `q > a`).
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Artin

open Filter NumberField IsDedekindDomain TauCeti
open scoped NumberField Topology
noncomputable section

/-! ### Counting up to `x` -/

/-- `#{n ≤ x : Q n}`. -/
def upCount (Q : ℕ → Prop) [DecidablePred Q] (x : ℝ) : ℕ :=
  ((Finset.range (⌊x⌋₊ + 1)).filter Q).card

theorem upCount_mono (Q : ℕ → Prop) [DecidablePred Q] : Monotone (fun x : ℝ => (upCount Q x : ℝ)) := by
  intro x y hxy
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro n hn
  obtain ⟨hr, hq⟩ := Finset.mem_filter.mp hn
  refine Finset.mem_filter.mpr ⟨?_, hq⟩
  rw [Finset.mem_range] at hr ⊢
  have := Nat.floor_le_floor hxy
  omega

/-- The dyadic increment of `upCount` counts `n ∈ (x, 2x]`. -/
theorem upCount_dyadic (Q : ℕ → Prop) [DecidablePred Q] {x : ℝ} (hx : 0 ≤ x) :
    (upCount Q (2 * x) : ℝ) - upCount Q x =
      (((Finset.range (⌊2 * x⌋₊ + 1)).filter fun n => Q n ∧ x < (n : ℝ)).card : ℝ) := by
  unfold upCount
  set S2 := (Finset.range (⌊2 * x⌋₊ + 1)).filter Q
  set S1 := (Finset.range (⌊x⌋₊ + 1)).filter Q
  have hsub : S1 ⊆ S2 := by
    intro n hn
    obtain ⟨hr, hq⟩ := Finset.mem_filter.mp hn
    refine Finset.mem_filter.mpr ⟨?_, hq⟩
    rw [Finset.mem_range] at hr ⊢
    have := Nat.floor_le_floor (show x ≤ 2 * x by linarith)
    omega
  have hdiff : S2 \ S1 = (Finset.range (⌊2 * x⌋₊ + 1)).filter fun n => Q n ∧ x < (n : ℝ) := by
    ext n
    simp only [S2, S1, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_range, not_and]
    constructor
    · rintro ⟨⟨hr, hq⟩, hn⟩
      refine ⟨hr, hq, ?_⟩
      by_contra hle
      exact hn (Nat.lt_succ_of_le (Nat.le_floor (not_lt.mp hle))) hq
    · rintro ⟨hr, hq, hxn⟩
      refine ⟨⟨hr, hq⟩, fun hn _ => ?_⟩
      have h1 : n ≤ ⌊x⌋₊ := Nat.lt_succ_iff.mp hn
      have h2 : (n : ℝ) ≤ x := (Nat.cast_le.mpr h1).trans (Nat.floor_le hx)
      linarith
  rw [← hdiff, Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]

/-! ### The dyadic prime number theorem -/

open Classical in
/-- **The prime number theorem in dyadic form.** -/
theorem tendsto_dyadicPrimes :
    Tendsto (fun x : ℝ => ((upCount Nat.Prime (2 * x) : ℝ) - upCount Nat.Prime x) /
      (x / Real.log x)) atTop (𝓝 1) := by
  have h := tendsto_frobeniusPrimeCount_dyadic ℚ ℚ (1 : ConjClasses (ℚ ≃ₐ[ℚ] ℚ))
  have hlim : (Nat.card (1 : ConjClasses (ℚ ≃ₐ[ℚ] ℚ)).carrier : ℝ) /
      Nat.card (ℚ ≃ₐ[ℚ] ℚ) = 1 := by
    rw [ConjClasses.one_eq_mk_one, Nat.card_coe_set_eq,
      ConjClasses.ncard_carrier_mk_of_mem_center (Subgroup.one_mem _),
      IsGalois.card_aut_eq_finrank, Module.finrank_self]
    norm_num
  rw [hlim] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  congr 1
  rw [upCount_dyadic Nat.Prime hx, frobeniusPrimeCount_eq_filter_card,
    frobeniusPrimeCount_eq_filter_card]
  simp only [TauCeti.NumberField.Chebotarev.frobeniusPrimeSet_self, Set.mem_univ,
    Finset.filter_true_of_mem fun _ _ => trivial]
  set P2 := primesLE ℚ (2 * x)
  set P1 := primesLE ℚ x
  have hsub : P1 ⊆ P2 := by
    intro v hv
    rw [mem_normLE] at hv ⊢
    linarith
  rw [← Nat.cast_sub (Finset.card_le_card hsub), ← Finset.card_sdiff_of_subset hsub]
  congr 1
  apply Finset.card_nbij (fun 𝔭 : HeightOneSpectrum (𝓞 ℚ) => Ideal.absNorm 𝔭.asIdeal)
  · intro v hv
    obtain ⟨hv2, hv1⟩ := Finset.mem_sdiff.mp (Finset.mem_coe.mp hv)
    rw [mem_normLE] at hv2 hv1
    have hprime : (Ideal.absNorm v.asIdeal).Prime := by
      rw [Rat.HeightOneSpectrum.absNorm_asIdeal]
      exact Rat.HeightOneSpectrum.prime_natGenerator v
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨?_, hprime, not_le.mp hv1⟩)
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_floor hv2))
  · exact absNorm_injective_rat.injOn
  · intro p hp
    obtain ⟨hr, hpp, hxp⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
    obtain ⟨v, hv⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq hpp
    have hp2 : (p : ℝ) ≤ 2 * x := by
      have h1 : p ≤ ⌊2 * x⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
      exact (Nat.cast_le.mpr h1).trans (Nat.floor_le (by linarith))
    refine ⟨v, Finset.mem_coe.mpr (Finset.mem_sdiff.mpr ⟨?_, ?_⟩), hv⟩
    · rw [mem_normLE, hv]
      exact hp2
    · rw [mem_normLE, hv]
      exact not_le.mpr hxp

/-! ### From dyadic increments to cumulative ratios -/

/-- **Dyadic to cumulative.** If `A, B` are monotone and nonnegative, the ratio of their dyadic
increments tends to `δ ≥ 0`, the increments of `B` are eventually positive and `B → ∞`, then
`A(x) / B(x) → δ`. -/
theorem tendsto_div_of_dyadic {A B : ℝ → ℝ} (hAm : Monotone A) (hBm : Monotone B)
    (hA0 : ∀ x, 0 ≤ A x) (hB0 : ∀ x, 0 ≤ B x) {δ : ℝ} (hδ : 0 ≤ δ)
    (hD : Tendsto (fun x => (A (2 * x) - A x) / (B (2 * x) - B x)) atTop (𝓝 δ))
    (hDpos : ∀ᶠ x in atTop, 0 < B (2 * x) - B x) (hB : Tendsto B atTop atTop) :
    Tendsto (fun x => A x / B x) atTop (𝓝 δ) := by
  -- the dyadic induction along `x ↦ x / 2`
  have induct : ∀ (P : ℝ → Prop) (X₀ : ℝ), 0 < X₀ →
      (∀ x, X₀ ≤ x → x ≤ 2 * X₀ → P x) → (∀ x, 2 * X₀ < x → P (x / 2) → P x) →
      ∀ x, X₀ ≤ x → P x := by
    intro P X₀ hX₀ hbase hstep
    have hn : ∀ n : ℕ, ∀ x, X₀ ≤ x → x ≤ 2 ^ (n + 1) * X₀ → P x := by
      intro n
      induction n with
      | zero =>
        intro x hx1 hx2
        exact hbase x hx1 (by simpa using hx2)
      | succ n ih =>
        intro x hx1 hx2
        by_cases hle : x ≤ 2 ^ (n + 1) * X₀
        · exact ih x hx1 hle
        · have hlt : 2 ^ (n + 1) * X₀ < x := not_le.mp hle
          have h2 : 2 * X₀ ≤ 2 ^ (n + 1) * X₀ := by
            have : (2 : ℝ) ≤ 2 ^ (n + 1) := by
              calc (2 : ℝ) = 2 ^ 1 := by norm_num
                _ ≤ 2 ^ (n + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
            nlinarith
          refine hstep x (by linarith) (ih (x / 2) (by linarith) ?_)
          have : x ≤ 2 * (2 ^ (n + 1) * X₀) := by
            rw [show 2 ^ (n + 1 + 1) * X₀ = 2 * (2 ^ (n + 1) * X₀) by ring] at hx2
            exact hx2
          linarith
    intro x hx
    obtain ⟨n, hn'⟩ := pow_unbounded_of_one_lt (x / X₀) (by norm_num : (1 : ℝ) < 2)
    refine hn n x hx ?_
    have h1 : x / X₀ < 2 ^ (n + 1) := hn'.trans (pow_lt_pow_right₀ (by norm_num) (by omega))
    rw [div_lt_iff₀ hX₀] at h1
    exact h1.le
  rw [tendsto_order]
  constructor
  · -- lower bound
    intro l hl
    by_cases hl0 : l < 0
    · filter_upwards with x
      exact lt_of_lt_of_le hl0 (div_nonneg (hA0 x) (hB0 x))
    push Not at hl0
    set ε := (δ - l) / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    have hc0 : 0 ≤ δ - ε := by rw [hε]; linarith
    have hev := hD.eventually (lt_mem_nhds (show δ - ε < δ by linarith))
    obtain ⟨X₁, hX₁⟩ := (hev.and hDpos).exists_forall_of_atTop
    set X₀ := max X₁ 1 with hX₀
    have hX₀pos : 0 < X₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
    set K := B (2 * X₀)
    have hstepD : ∀ y, X₀ ≤ y → (δ - ε) * (B (2 * y) - B y) ≤ A (2 * y) - A y := by
      intro y hy
      obtain ⟨h1, h2⟩ := hX₁ y ((le_max_left _ _).trans hy)
      exact (le_div_iff₀ h2).mp h1.le
    have hmain : ∀ x, X₀ ≤ x → (δ - ε) * (B x - K) ≤ A x := by
      refine induct _ X₀ hX₀pos ?_ ?_
      · intro x _ hx2
        have : B x ≤ K := hBm hx2
        have := mul_le_mul_of_nonneg_left (sub_nonpos.mpr this) hc0
        linarith [hA0 x]
      · intro x hx hhalf
        have h := hstepD (x / 2) (by linarith)
        rw [show 2 * (x / 2) = x by ring] at h
        nlinarith
    -- `(δ - ε)(1 - K / B x) > l` eventually
    have hKB : Tendsto (fun x => K / B x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hB
    have hsmall := hKB.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (δ + 1) by
      have : 0 < δ + 1 := by linarith
      positivity))
    filter_upwards [hsmall, eventually_ge_atTop X₀, hB.eventually (eventually_gt_atTop 0)]
      with x hxs hxX hBx
    have h := hmain x hxX
    rw [lt_div_iff₀ hBx]
    have hKx : K < ε / (δ + 1) * B x := (div_lt_iff₀ hBx).mp hxs
    have hδ1 : 0 < δ + 1 := by linarith
    have hεK : (δ - ε) * K ≤ (δ + 1) * K := by
      have hK0 : 0 ≤ K := hB0 _
      nlinarith
    have : (δ + 1) * K < ε * B x := by
      have := mul_lt_mul_of_pos_left hKx hδ1
      rw [show (δ + 1) * (ε / (δ + 1) * B x) = ε * B x by field_simp] at this
      exact this
    nlinarith
  · -- upper bound
    intro u hu
    set ε := (u - δ) / 2 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    have hev := hD.eventually (gt_mem_nhds (show δ < δ + ε by linarith))
    obtain ⟨X₁, hX₁⟩ := (hev.and hDpos).exists_forall_of_atTop
    set X₀ := max X₁ 1 with hX₀
    have hX₀pos : 0 < X₀ := lt_of_lt_of_le one_pos (le_max_right _ _)
    set K := A (2 * X₀)
    have hc0 : 0 ≤ δ + ε := by linarith
    have hstepD : ∀ y, X₀ ≤ y → A (2 * y) - A y ≤ (δ + ε) * (B (2 * y) - B y) := by
      intro y hy
      obtain ⟨h1, h2⟩ := hX₁ y ((le_max_left _ _).trans hy)
      exact ((div_le_iff₀ h2).mp h1.le)
    have hmain : ∀ x, X₀ ≤ x → A x ≤ (δ + ε) * B x + K := by
      refine induct _ X₀ hX₀pos ?_ ?_
      · intro x _ hx2
        have : A x ≤ K := hAm hx2
        have := mul_nonneg hc0 (hB0 x)
        linarith
      · intro x hx hhalf
        have h := hstepD (x / 2) (by linarith)
        rw [show 2 * (x / 2) = x by ring] at h
        nlinarith
    have hKB : Tendsto (fun x => K / B x) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hB
    have hsmall := hKB.eventually (gt_mem_nhds hε0)
    filter_upwards [hsmall, eventually_ge_atTop X₀, hB.eventually (eventually_gt_atTop 0)]
      with x hxs hxX hBx
    have h := hmain x hxX
    rw [div_lt_iff₀ hBx]
    have hKx : K < ε * B x := (div_lt_iff₀ hBx).mp hxs
    nlinarith

/-! ### Artin's conjecture with density -/

/-- The primes with primitive root `a`. -/
def IsPrimitiveRootPrime (a p : ℕ) : Prop := p.Prime ∧ PrimitiveRootMod a p

instance (a : ℕ) : DecidablePred (IsPrimitiveRootPrime a) := fun p => by
  unfold IsPrimitiveRootPrime PrimitiveRootMod
  infer_instance

theorem primeCount_eq_upCount (a : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    primeCount {a} x =
      (upCount (IsPrimitiveRootPrime a) (2 * x) : ℝ) - upCount (IsPrimitiveRootPrime a) x := by
  rw [upCount_dyadic _ hx]
  have hset : goodPrimes {a} x = (Finset.range (⌊2 * x⌋₊ + 1)).filter
      fun n => IsPrimitiveRootPrime a n ∧ x < (n : ℝ) := by
    ext p
    rw [mem_goodPrimes_singleton, Finset.mem_filter]
    unfold IsPrimitiveRootPrime
    constructor
    · rintro ⟨hr, hx1, _, hpp, hprim⟩
      exact ⟨hr, ⟨hpp, hprim⟩, hx1⟩
    · rintro ⟨hr, ⟨hpp, hprim⟩, hx1⟩
      have hp2 : (p : ℝ) ≤ 2 * x := by
        have h1 : p ≤ ⌊2 * x⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
        exact (Nat.cast_le.mpr h1).trans (Nat.floor_le (by linarith))
      exact ⟨hr, hx1, hp2, hpp, hprim⟩
  unfold primeCount
  rw [hset]

/-- **Artin's conjecture with density for `a`, from the GRH splitting estimate.** For `a ≥ 2` not
a square, `#{p ≤ x : a primitive root mod p} / #{p ≤ x} → δ_a > 0`. -/
theorem primitiveRoot_density_of_grhSplitting {a : ℕ} (ha : 2 ≤ a) (hsq : ¬ IsSquare a)
    {C : ℝ} (hC : 0 ≤ C) (hGRH : GRHSplittingBoundUpTo a C) :
    ∃ δ : ℝ, 0 < δ ∧ Tendsto (fun x : ℝ =>
      (upCount (IsPrimitiveRootPrime a) x : ℝ) / upCount Nat.Prime x) atTop (𝓝 δ) := by
  obtain ⟨δ, hδ, hT⟩ := exists_tendsto_primitiveRoot_density ha hsq hC hGRH
  refine ⟨δ, hδ, tendsto_div_of_dyadic (upCount_mono _) (upCount_mono _)
    (fun _ => Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _) hδ.le ?_ ?_ ?_⟩
  · -- ratio of dyadic increments
    have hP := tendsto_dyadicPrimes
    have h := hT.div hP one_ne_zero
    rw [div_one] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hs : 0 < x / Real.log x := div_pos (by linarith) (Real.log_pos hx)
    simp only [Pi.div_apply]
    rw [primeCount_eq_upCount a (by linarith)]
    have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
    have hx0 : x ≠ 0 := by linarith
    rw [div_div_div_cancel_right₀ (div_ne_zero hx0 hlog)]
  · have hP := tendsto_dyadicPrimes
    have hev := hP.eventually (lt_mem_nhds (show (1 : ℝ) / 2 < 1 by norm_num))
    filter_upwards [hev, eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hs : 0 < x / Real.log x := div_pos (by linarith) (Real.log_pos hx1)
    have := (lt_div_iff₀ hs).mp hx
    nlinarith
  · -- infinitely many primes
    rw [Filter.tendsto_atTop_atTop]
    intro b
    obtain ⟨n, hn⟩ := exists_nat_gt b
    obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S.card = n ∧ ∀ p ∈ S, p.Prime := by
      obtain ⟨S, hSsub, hScard⟩ := Set.Infinite.exists_subset_card_eq Nat.infinite_setOfPred_prime n
      exact ⟨S, hScard, fun p hp => hSsub hp⟩
    set M := S.sup id
    refine ⟨M, fun x hx => ?_⟩
    have hsub : S ⊆ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime := by
      intro p hp
      refine Finset.mem_filter.mpr ⟨?_, hS.2 p hp⟩
      have h1 : p ≤ M := Finset.le_sup (f := id) hp
      have h2 : (M : ℝ) ≤ x := hx
      have h3 : p ≤ ⌊x⌋₊ := Nat.le_floor ((Nat.cast_le.mpr h1).trans h2)
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le h3)
    have hcard : n ≤ upCount Nat.Prime x := by
      unfold upCount
      rw [← hS.1]
      exact Finset.card_le_card hsub
    have hcard' : (n : ℝ) ≤ upCount Nat.Prime x := by exact_mod_cast hcard
    linarith

/-- **Artin's conjecture with density under GRH for the Kummer fields.** -/
theorem primitiveRoot_density_of_dedekindZetaGRH {a : ℕ} (ha : 2 ≤ a) (hsq : ¬ IsSquare a)
    (h : ∀ q : ℕ, ∀ ha : 2 ≤ a, ∀ hq : q.Prime, ∀ haq : a < q,
      letI : Fact (2 ≤ a) := ⟨ha⟩
      letI : Fact q.Prime := ⟨hq⟩
      letI : Fact (a < q) := ⟨haq⟩
      Explicit.DedekindZetaGRH (PrimeKummerField a q)) :
    ∃ δ : ℝ, 0 < δ ∧ Tendsto (fun x : ℝ =>
      (upCount (IsPrimitiveRootPrime a) x : ℝ) / upCount Nat.Prime x) atTop (𝓝 δ) := by
  obtain ⟨D, hD, hGRH⟩ := Explicit.grhSplittingBoundUpTo_of_kummerZetaGRH ha
    (Explicit.kummerZetaGRH_of_dedekindZetaGRH h)
  exact primitiveRoot_density_of_grhSplitting ha hsq hD hGRH

end

end SimultaneousPrimitiveRoots.Artin
