module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.ProgressionSum
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.ProgressionAsymptotics
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.SmoothCount
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.LowFrequencyProof

/-!
# Lemma 7.2 for a family of long divisors

`progression_generic`: [P] Lemma 7.2 with the class (`[P-07:0077–0192]`, `[PUB-tex:0518–0522]`) for
an arbitrary finite family of integers `ℓ_i ≥ 1` all of whose prime factors are `≥ x^θ`, `θ > c₀`,
with the multiplicity `f(u) = #{i : ℓ_i ∣ u}` and the mass `C = ∑_i 1/ℓ_i`:

`∑_{r ≤ x^{c₀}} | ∑_{u, r ∣ u+1, u+1 ≡ b (H)} Φ(u/x) f(u) W(u)
    - 1_{(r,H)=1} x/(H r) (∫Φ) C M_x(W) | ≤ M x L^{-A}`

for `x ≥ x₀`, uniformly in the monomial `W ∈ {1, 𝒲_a, 𝒲_a 𝒲_{a'}}` and in the families with
`#I ≤ B_I x^{1 - c₀ - δ}` and `C ≤ B_I`. The two forms of the lemma are the family of the products
of the long-prime tuples (`θ = ε`, `δ = ε - c₀`) and the family `{1}` (`δ = 1 - c₀`); see
`Extraction/ProgressionSlotsProof.lean`.

The proof assembles, for `x` large:

* the cutoff: its range `R` and the constant `C_Φ` of (ext:crt-count) (`smoothProgressionCount`);
* the monomials: `|W| ≤ H_b = max(1, C_𝒲)²` (`arrayWeightBounded_all`, from Mertens) and `W` depends
  only on the primes of the family dividing `u` (`pairWeight_congr`);
* the primes of the family: they lie in `[exp(L^{.1}), exp(2 L^{.2})]`, they exceed `H`, and their
  reciprocal mass is at most `V₀ = n K (log 2 + 1)` (`dyadicPrimeMass_of_mertensReciprocal`);
* the long divisors: their prime factors exceed `x^{c₀} ≥ r`, `H` and `exp(2 L^{.2})`, so the
  `ℓ_i` are coprime to `r`, to `H` and to the primes of the family;
* the truncation degree `k = ⌊L^{.01}⌋ + 1` and the sum over `r`
  (`sum_abs_shiftSum_family_sub_le`), with `T₁ = 2 exp(2 L^{.2})^k e^{2V₀}`,
  `T₂ = e^{-k} e^{2eV₀}`, `B = exp(-L^{.1}) c₀ L`;
* the sizes (`rounding_bound`, `main_error_bound`).

The constant is `M = 2 H_b B_I (C_Φ e^{2V₀} + (∫Φ)(1 + c₀)(e^{2eV₀} + c₀))`.

The hypothesis `ArraysDisjoint` of the lemma is not used: the model is the independent model on
the union of the bands, and the truncated expansion needs no structure of `W` beyond its
boundedness.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

open Filter MeasureTheory
open scoped Topology
open Progression

noncomputable section

/-- **[P] Lemma 7.2 with the class, for a family of long divisors.** -/
theorem progression_generic (H b : ℕ) (hH : 0 < H) (hb : b.Coprime H) {q : ℝ} (hq : 0 < q)
    (hq1 : q < 1) (hM : MertensReciprocal) {c₀ θ δ : ℝ} (hc₀ : 0 < c₀) (hθ : c₀ < θ)
    (hδ : 0 < δ) {Φ : ℝ → ℝ} (hΦ : IsCutoff Φ) {n K : ℕ} (𝔄 : Fin n → MarkingArray K)
    (A BI : ℝ) :
    ∃ M x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ a a' : Option (Fin n),
      ∀ (ι : Type) (I : Finset ι) (ℓ : ι → ℕ), (∀ i ∈ I, 0 < ℓ i) →
        (∀ i ∈ I, ∀ p : ℕ, p.Prime → p ∣ ℓ i → x ^ θ ≤ (p : ℝ)) →
        (I.card : ℝ) ≤ BI * x ^ (1 - c₀ - δ) → ∑ i ∈ I, 1 / (ℓ i : ℝ) ≤ BI →
        ∑ r ∈ Finset.Icc 1 ⌊x ^ c₀⌋₊,
          |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H])
              (fun u => (∑ i ∈ I, if ℓ i ∣ u then (1 : ℝ) else 0) *
                pairWeight q 𝔄 x a a' u) -
            (if r.Coprime H then x / ((H : ℝ) * (r : ℝ)) * (∫ t, Φ t) *
              (∑ i ∈ I, 1 / (ℓ i : ℝ)) *
                modelMean (familyPrimes 𝔄 x) (pairWeight q 𝔄 x a a') else 0)| ≤
          M * x * Real.log x ^ (-A) := by
  -- the constants
  obtain ⟨R, -, hR⟩ := hΦ.exists_upper
  obtain ⟨CΦ, hC⟩ := smoothProgressionCount Φ hΦ
  have hCΦ0 : 0 ≤ CΦ := (abs_nonneg _).trans (hC 1 one_pos 1 1 0 one_pos one_pos)
  obtain ⟨CW, hCW⟩ := arrayWeightBounded_all hM q hq hq1 K
  obtain ⟨Y₀, hY₀⟩ := dyadicPrimeMass_of_mertensReciprocal hM 1 one_pos
  have hint : 0 ≤ ∫ t, Φ t := MeasureTheory.integral_nonneg fun t => hΦ.nonneg t
  obtain ⟨Hb, hHbdef⟩ : ∃ Hb : ℝ, Hb = max 1 CW * max 1 CW := ⟨_, rfl⟩
  obtain ⟨V₀, hV₀def⟩ : ∃ V₀ : ℝ, V₀ = (n : ℝ) * ((K : ℝ) * (Real.log 2 + 1)) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := hc₀.trans hθ
  have hθne : θ ≠ 0 := hθ0.ne'
  -- the thresholds
  have hεA : 0 < 1 / (2 * (|A + 2| + 1)) := by
    have h := abs_nonneg (A + 2)
    exact one_div_pos.mpr (by linarith)
  have hpowL : ∀ s : ℝ, 0 < s → ∀ B' : ℝ, ∀ᶠ x : ℝ in atTop, B' ≤ Real.log x ^ s :=
    fun s hs B' => ((tendsto_rpow_atTop hs).comp Real.tendsto_log_atTop).eventually_ge_atTop B'
  have hev1 : ∀ᶠ x : ℝ in atTop, 1 < x ∧ 1 ≤ Real.log x ∧ 2 ≤ Real.log x ^ (0.01 : ℝ) ∧
      ‖Real.log (Real.log x)‖ ≤ 1 / (2 * (|A + 2| + 1)) * ‖Real.log x ^ (0.01 : ℝ)‖ := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop 1,
      hpowL 0.01 (by norm_num) 2,
      Real.tendsto_log_atTop.eventually
        ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.01)).def hεA)]
      with x a1 a2 a3 a4
    exact ⟨a1, a2, a3, a4⟩
  have hev2 : ∀ᶠ x : ℝ in atTop,
      (∀ c : Fin n, ∀ i : Fin K, Y₀ ≤ Real.log x ^ (𝔄 c).exponent i) ∧
        ∀ c : Fin n, ∀ u : ℕ, |markedWeight q (𝔄 c) x u| ≤ CW := by
    have h1 : ∀ᶠ x : ℝ in atTop, ∀ c : Fin n, ∀ i : Fin K,
        Y₀ ≤ Real.log x ^ (𝔄 c).exponent i :=
      Filter.eventually_all.mpr fun c => Filter.eventually_all.mpr fun i =>
        hpowL _ (lt_trans (by norm_num) ((𝔄 c).gt_tenth i)) Y₀
    have h2 : ∀ᶠ x : ℝ in atTop, ∀ c : Fin n, ∀ u : ℕ, |markedWeight q (𝔄 c) x u| ≤ CW :=
      Filter.eventually_all.mpr fun c => hCW (𝔄 c)
    exact h1.and h2
  have hev3 : ∀ᶠ x : ℝ in atTop, (H : ℝ) < Real.exp (Real.log x ^ (1 / 10 : ℝ)) ∧
      2 / θ < Real.log x ^ (4 / 5 : ℝ) ∧ (H : ℝ) < x ^ θ ∧
      x ^ (-δ) * Real.exp (4 * Real.log x ^ (0.47 : ℝ)) * Real.log x ^ A ≤ 1 := by
    filter_upwards [(Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop
        (by norm_num : (0 : ℝ) < 1 / 10)).comp Real.tendsto_log_atTop)).eventually_gt_atTop
        (H : ℝ),
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 4 / 5)).comp
        Real.tendsto_log_atTop).eventually_gt_atTop (2 / θ),
      (tendsto_rpow_atTop hθ0).eventually_gt_atTop (H : ℝ),
      EndpointProof.eventually_rpow_neg_mul_exp_mul_rpow_le_one hδ 4 A] with x a1 a2 a3 a4
    exact ⟨a1, a2, a3, a4⟩
  obtain ⟨x₀, hx₀⟩ := Filter.eventually_atTop.mp (hev1.and (hev2.and hev3))
  refine ⟨2 * Hb * BI * CΦ * Real.exp (2 * V₀) +
    2 * Hb * BI * (∫ t, Φ t) * (1 + c₀) * (Real.exp (2 * Real.exp 1 * V₀) + c₀), x₀, ?_⟩
  intro x hx a a' ι I ℓ hℓ0 hℓbig hcard hCI
  obtain ⟨⟨hx1, hL1, h01, hLLn⟩, ⟨hbands, hW⟩, hHexp, h45, hHθ, hround⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hLL0 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hL1
  have hp01 : 0 ≤ Real.log x ^ (0.01 : ℝ) := Real.rpow_nonneg hL0.le _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hLL0, abs_of_nonneg hp01] at hLLn
  -- the primes of the family
  obtain ⟨𝒬, h𝒬def⟩ : ∃ 𝒬 : Finset ℕ, 𝒬 = familyPrimes 𝔄 x := ⟨_, rfl⟩
  have h𝒬f : ∀ p ∈ 𝒬, p.Prime ∧ Real.exp (Real.log x ^ (1 / 10 : ℝ)) ≤ (p : ℝ) ∧
      (p : ℝ) ≤ Real.exp (2 * Real.log x ^ (1 / 5 : ℝ)) := by
    intro p hp
    rw [h𝒬def] at hp
    exact familyPrimes_facts 𝔄 hL1 hp
  have h𝒬prime : ∀ p ∈ 𝒬, p.Prime := fun p hp => (h𝒬f p hp).1
  have h𝒬H : ∀ p ∈ 𝒬, ¬ p ∣ H := by
    intro p hp hdvd
    have h1 : p ≤ H := Nat.le_of_dvd hH hdvd
    have h2 : (p : ℝ) ≤ (H : ℝ) := by exact_mod_cast h1
    have h3 := (h𝒬f p hp).2.1
    linarith
  have hV : reciprocalMass 𝒬 ≤ V₀ := by
    rw [h𝒬def, hV₀def]
    refine reciprocalMass_familyPrimes_le 𝔄 fun c i => ?_
    have h1 := hY₀ (Real.log x ^ (𝔄 c).exponent i) (hbands c i)
      (bandPrimes ((𝔄 c).exponent i) x) (fun p hp => mem_bandPrimes.mp hp)
      (fun p hpp hlo hhi => mem_bandPrimes.mpr ⟨hpp, hlo.le, hhi.le⟩)
    have h2 := (abs_le.mp h1).2
    linarith
  -- the monomial
  obtain ⟨G, hGdef⟩ : ∃ G : ℕ → ℝ, G = pairWeight q 𝔄 x a a' := ⟨_, rfl⟩
  have hG : ∀ u, |G u| ≤ Hb := fun u => by
    rw [hGdef, hHbdef]
    exact abs_pairWeight_le hW a a' u
  have hHb0 : 0 ≤ Hb := (abs_nonneg _).trans (hG 0)
  have hGinv : ∀ u u' : ℕ, (∀ p ∈ 𝒬, (p ∣ u ↔ p ∣ u')) → G u = G u' := by
    intro u u' h
    rw [h𝒬def] at h
    rw [hGdef]
    exact pairWeight_congr q 𝔄 x a a' h
  -- the long divisors are coprime to everything below `x^θ`
  have hPmθ : Real.exp (2 * Real.log x ^ (1 / 5 : ℝ)) < x ^ θ := by
    rw [Real.rpow_def_of_pos hx0 θ]
    refine Real.exp_lt_exp.mpr ?_
    have h15 : 0 < Real.log x ^ (1 / 5 : ℝ) := Real.rpow_pos_of_pos hL0 _
    have hsplit : Real.log x ^ (4 / 5 : ℝ) * Real.log x ^ (1 / 5 : ℝ) = Real.log x := by
      rw [← Real.rpow_add hL0, show (4 / 5 : ℝ) + 1 / 5 = 1 by norm_num, Real.rpow_one]
    have h1 : 2 / θ * (θ * Real.log x ^ (1 / 5 : ℝ)) <
        Real.log x ^ (4 / 5 : ℝ) * (θ * Real.log x ^ (1 / 5 : ℝ)) :=
      mul_lt_mul_of_pos_right h45 (mul_pos hθ0 h15)
    have e1 : 2 / θ * (θ * Real.log x ^ (1 / 5 : ℝ)) = 2 * Real.log x ^ (1 / 5 : ℝ) :=
      calc 2 / θ * (θ * Real.log x ^ (1 / 5 : ℝ))
          = 2 * Real.log x ^ (1 / 5 : ℝ) * (θ / θ) := by ring
        _ = 2 * Real.log x ^ (1 / 5 : ℝ) := by rw [div_self hθne, mul_one]
    have e2 : Real.log x ^ (4 / 5 : ℝ) * (θ * Real.log x ^ (1 / 5 : ℝ)) = Real.log x * θ :=
      calc Real.log x ^ (4 / 5 : ℝ) * (θ * Real.log x ^ (1 / 5 : ℝ))
          = Real.log x ^ (4 / 5 : ℝ) * Real.log x ^ (1 / 5 : ℝ) * θ := by ring
        _ = Real.log x * θ := by rw [hsplit]
    rw [e1, e2] at h1
    exact h1
  have hℓcop : ∀ i ∈ I, ∀ m : ℕ, 0 < m → (m : ℝ) < x ^ θ → (ℓ i).Coprime m := by
    intro i hi m hm hmθ
    refine Nat.coprime_of_dvd fun p hp hpℓ hpm => ?_
    have h1 : p ≤ m := Nat.le_of_dvd hm hpm
    have h2 : (p : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
    have h3 := hℓbig i hi p hp hpℓ
    linarith
  have hN₀ : ((⌊x ^ c₀⌋₊ : ℕ) : ℝ) ≤ x ^ c₀ := Nat.floor_le (Real.rpow_nonneg hx0.le _)
  have hxθ : x ^ c₀ < x ^ θ := Real.rpow_lt_rpow_of_exponent_lt hx1 hθ
  have hrle : ∀ r ∈ Finset.Icc 1 ⌊x ^ c₀⌋₊, (r : ℝ) ≤ x ^ c₀ := fun r hr =>
    (Nat.cast_le.mpr (Finset.mem_Icc.mp hr).2).trans hN₀
  have hℓr : ∀ r ∈ Finset.Icc 1 ⌊x ^ c₀⌋₊, ∀ i ∈ I, (ℓ i).Coprime r := fun r hr i hi =>
    hℓcop i hi r (Finset.mem_Icc.mp hr).1 (lt_of_le_of_lt (hrle r hr) hxθ)
  have hℓH : ∀ i ∈ I, (ℓ i).Coprime H := fun i hi => hℓcop i hi H hH hHθ
  have hℓ𝒬 : ∀ i ∈ I, ∀ p ∈ 𝒬, (ℓ i).Coprime p := fun i hi p hp =>
    hℓcop i hi p (h𝒬prime p hp).pos (lt_of_le_of_lt (h𝒬f p hp).2.2 hPmθ)
  -- the truncation degree and the three error terms
  obtain ⟨h, hhdef⟩ : ∃ h : ℕ, h = ⌊Real.log x ^ (0.01 : ℝ)⌋₊ := ⟨_, rfl⟩
  have hhle : (h : ℝ) ≤ Real.log x ^ (0.01 : ℝ) := by
    rw [hhdef]
    exact Nat.floor_le hp01
  have htail : Real.log x ^ (A + 2) ≤ Real.exp 1 ^ h := by
    rw [hhdef]
    exact EndpointProof.rpow_le_exp_one_pow_floor hL1 h01 hLLn
  obtain ⟨hinv1, hinv2⟩ := tail_bounds hL1 hhle htail
  obtain ⟨Pm, hPmdef⟩ : ∃ Pm : ℝ, Pm = Real.exp (2 * Real.log x ^ (1 / 5 : ℝ)) := ⟨_, rfl⟩
  have hPm1 : 1 ≤ Pm := by
    rw [hPmdef]
    exact Real.one_le_exp (mul_nonneg zero_le_two (Real.rpow_nonneg hL0.le _))
  have hT₁ : ∀ P ⊆ 𝒬, ∑ D ∈ P.powerset.filter (fun D => D.card < h + 1), (2 : ℝ) ^ D.card +
      ∑ E ∈ P.powersetCard (h + 1), (2 : ℝ) ^ E.card ≤
        2 * (Pm ^ (h + 1) * Real.exp (2 * V₀)) := fun P hP =>
    sum_two_pow_card_family_le hP hPm1
      (fun p hp => ⟨(h𝒬prime p hp).pos, by rw [hPmdef]; exact (h𝒬f p hp).2.2⟩) hV (h + 1)
  have hT₂ : ∀ P ⊆ 𝒬, ∑ E ∈ P.powersetCard (h + 1), ∏ p ∈ E, (2 / (p : ℝ)) ≤
      (Real.exp 1 ^ (h + 1))⁻¹ * Real.exp (2 * Real.exp 1 * V₀) := fun P hP =>
    sum_powersetCard_prod_family_le hP hV (h + 1)
  have hy : 0 < Real.exp (Real.log x ^ (1 / 10 : ℝ)) := Real.exp_pos _
  have hB : ∀ r ∈ Finset.Icc 1 ⌊x ^ c₀⌋₊, ∑ p ∈ 𝒬.filter (fun p => p ∣ r), 1 / (p : ℝ) ≤
      (Real.exp (Real.log x ^ (1 / 10 : ℝ)))⁻¹ * (c₀ * Real.log x) := by
    intro r hr
    obtain ⟨h1, h2⟩ := sum_inv_le_of_primes_dvd (B := 𝒬.filter fun p => p ∣ r) hy
      (Finset.mem_Icc.mp hr).1 (fun p hp => h𝒬prime p (Finset.mem_filter.mp hp).1)
      (fun p hp => (Finset.mem_filter.mp hp).2)
      (fun p hp => (h𝒬f p (Finset.mem_filter.mp hp).1).2.1)
    have h3 : Real.log (Real.exp (Real.log x ^ (1 / 10 : ℝ)) ^
        (𝒬.filter fun p => p ∣ r).card) ≤ Real.log (x ^ c₀) :=
      Real.log_le_log (pow_pos hy _) (h2.trans (hrle r hr))
    rw [Real.log_pow, Real.log_exp, Real.log_rpow hx0] at h3
    have h10 : 1 ≤ Real.log x ^ (1 / 10 : ℝ) := Real.one_le_rpow hL1 (by norm_num)
    have h4 : ((𝒬.filter fun p => p ∣ r).card : ℝ) ≤ c₀ * Real.log x :=
      (le_mul_of_one_le_right (Nat.cast_nonneg _) h10).trans h3
    calc ∑ p ∈ 𝒬.filter (fun p => p ∣ r), 1 / (p : ℝ)
        ≤ ((𝒬.filter fun p => p ∣ r).card : ℝ) / Real.exp (Real.log x ^ (1 / 10 : ℝ)) := h1
      _ = (Real.exp (Real.log x ^ (1 / 10 : ℝ)))⁻¹ * ((𝒬.filter fun p => p ∣ r).card : ℝ) := by
          rw [div_eq_mul_inv, mul_comm]
      _ ≤ (Real.exp (Real.log x ^ (1 / 10 : ℝ)))⁻¹ * (c₀ * Real.log x) :=
          mul_le_mul_of_nonneg_left h4 (inv_nonneg.mpr hy.le)
  have hcL : 0 ≤ c₀ * Real.log x := mul_nonneg hc₀.le hL0.le
  have hB0 : 0 ≤ (Real.exp (Real.log x ^ (1 / 10 : ℝ)))⁻¹ * (c₀ * Real.log x) :=
    mul_nonneg (inv_nonneg.mpr hy.le) hcL
  -- the sum over `r`
  have hsum := sum_abs_shiftSum_family_sub_le hR hΦ.nonneg hC hCΦ0 hx0 hH hb ⌊x ^ c₀⌋₊ h𝒬prime
    h𝒬H hG hGinv I ℓ hℓ0 hℓr hℓH hℓ𝒬 (h + 1) hT₁ hT₂ hB hB0
  rw [← hGdef, ← h𝒬def]
  refine hsum.trans ?_
  -- the sizes
  have hCI0 : 0 ≤ ∑ i ∈ I, 1 / (ℓ i : ℝ) := Finset.sum_nonneg fun i _ => by positivity
  have hBI0 : 0 ≤ BI := hCI0.trans hCI
  have hPk : Pm ^ (h + 1) ≤ Real.exp (4 * Real.log x ^ (0.47 : ℝ)) := by
    rw [hPmdef]
    exact pow_le_exp_four hL1 hhle
  have hr1 := rounding_bound hx1 hN₀ (Nat.cast_nonneg I.card) hcard hBI0
    (pow_nonneg (zero_le_one.trans hPm1) (h + 1)) hPk hHb0 hCΦ0 (Real.exp_pos (2 * V₀)).le hround
  have hlogN : Real.log ((⌊x ^ c₀⌋₊ : ℕ) : ℝ) ≤ c₀ * Real.log x := by
    rcases Nat.eq_zero_or_pos ⌊x ^ c₀⌋₊ with h0 | hpos
    · rw [h0, Nat.cast_zero, Real.log_zero]
      exact hcL
    · have h1 : Real.log ((⌊x ^ c₀⌋₊ : ℕ) : ℝ) ≤ Real.log (x ^ c₀) :=
        Real.log_le_log (Nat.cast_pos.mpr hpos) hN₀
      rw [Real.log_rpow hx0] at h1
      exact h1
  have hlogN0 : 0 ≤ 1 + Real.log ((⌊x ^ c₀⌋₊ : ℕ) : ℝ) := by
    have h1 := Real.log_natCast_nonneg ⌊x ^ c₀⌋₊
    linarith
  have hEV2 : 0 ≤ Real.exp (2 * Real.exp 1 * V₀) := (Real.exp_pos _).le
  have hT₂0 : 0 ≤ (Real.exp 1 ^ (h + 1))⁻¹ * Real.exp (2 * Real.exp 1 * V₀) :=
    mul_nonneg (inv_nonneg.mpr (pow_pos (Real.exp_pos 1) _).le) hEV2
  have hr2 := main_error_bound (A := A) hx1 hL1 hc₀.le hH hint hCI0 hCI hHb0 hlogN0 hlogN hT₂0
    hB0 hEV2 (mul_le_mul_of_nonneg_right hinv1 hEV2) (mul_le_mul_of_nonneg_right hinv2 hcL)
  calc _ ≤ 2 * Hb * BI * CΦ * Real.exp (2 * V₀) * (x * Real.log x ^ (-A)) +
          2 * Hb * BI * (∫ t, Φ t) * (1 + c₀) * (Real.exp (2 * Real.exp 1 * V₀) + c₀) *
            (x * Real.log x ^ (-A)) := add_le_add hr1 hr2
    _ = (2 * Hb * BI * CΦ * Real.exp (2 * V₀) +
          2 * Hb * BI * (∫ t, Φ t) * (1 + c₀) * (Real.exp (2 * Real.exp 1 * V₀) + c₀)) * x *
            Real.log x ^ (-A) := by ring

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
