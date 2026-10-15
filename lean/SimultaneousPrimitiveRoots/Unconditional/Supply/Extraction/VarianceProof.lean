module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.PresieveTools
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.ModelVarianceProof

/-!
# The variance step (ext:prime-deweight-square)

`varianceLink q : VarianceLink q` (`[P-07:0649–0670]`), for every real `q`: the field `variance`
of `ExtractionOpenLeaves d H b q q₀`.

For `n ≥ 1` disjoint arrays and `Z(u) = ((1/n) ∑_a 𝒲_a(u)/m_a - 1)²`:

* "Every prime `u + 1` in the support exceeds `z'`": with `z' = x^{1/100}` (the manuscript's
  `x^{c₀/20}` for `c₀ = 1/5`) the primes `u + 1` with `Φ(u/x) ≠ 0` are `z'`-rough for large `x`, so
  `∑_p Φ((p-1)/x) Z(p-1) ≤ ∑_{P⁻(u+1) > z'} Φ(u/x) Z(u)` (`Z ≥ 0`;
  `Presieve.shiftSum_le_shiftSum_of_imp`).
* "Apply the nonnegative upper bound of the block sieve at the fixed depth `h' = 2`": the second
  conclusion of `Presieve.shiftSum_sieve` with `H = 1`, `X = x (∫Φ) M_x(Z)`; "its remainder range
  is `(z')^{10} = x^{c₀/2} < x^{c₀}`".
* "The square and all its cross terms lie within Lemma 7.2": `Z = ∑_j c_j W_j` over the monomials
  `W_j ∈ {1, 𝒲_a, 𝒲_a 𝒲_{a'}}` with coefficients `1, -2/(n m_a), 1/(n² m_a m_{a'})`
  (`arrayDeviation_eq`), which are bounded because `m_a ≥ c_K` (`ModelBounds`); the remainder of
  `Z` is at most `∑_j |c_j|` times the remainders of the monomials
  (`Presieve.progressionRemainder_sum_le`), which are `O(x L^{-2})` by `ProgressionUnit 1 1 q`.
* "The sieve main term is bounded by a fixed constant times `x M_x(Z)/log z'`":
  `∏_{p ≤ z'} (1 - 1/p) ≤ (e^{-γ_E} + 1)/log z'` (Mertens' product) and `M_x(Z) ≤ C_v/n`
  (`ModelVariance`).

The constant is `C = 100 M_s (∫Φ)(e^{-γ_E} + 1) C_v`, where `M_s` is the constant of the block sieve
and `C_v` the constant of `ModelVariance`; it depends on `Φ` and `K` only.

No hypothesis on `q` is needed: the weight `Z` is a square.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

open Filter
open scoped Topology

noncomputable section

namespace Presieve

/-- **The left side of Lemma 7.2 without tuple factors is sublinear in the weight**: for a finite
combination `∑_j c_j W_j` with means `∑_j c_j μ_j`, the summed remainder is at most
`∑_j |c_j|` times the summed remainders of the `W_j` ("bounded linear combinations follow by the
triangle inequality", `[P-07:0190–0191]`). -/
theorem progressionRemainder_sum_le {Φ : ℝ → ℝ} {R x : ℝ} (hR : ∀ t, R < t → Φ t = 0)
    (hx : 0 < x) (H b : ℕ) (c₀ : ℝ) {ι : Type*} (J : Finset ι) (c : ι → ℝ) (W : ι → ℕ → ℝ)
    (μ : ι → ℝ) :
    progressionRemainder H b Φ x c₀ (fun _ => 1) 1 (fun u => ∑ j ∈ J, c j * W j u)
        (∑ j ∈ J, c j * μ j) ≤
      ∑ j ∈ J, |c j| * progressionRemainder H b Φ x c₀ (fun _ => 1) 1 (W j) (μ j) := by
  show ∑ r ∈ Finset.Icc 1 ⌊x ^ c₀⌋₊,
      |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H]) (fun u => 1 * ∑ j ∈ J, c j * W j u) -
        (if r.Coprime H then x / ((H : ℝ) * (r : ℝ)) * (∫ t, Φ t) * 1 * ∑ j ∈ J, c j * μ j
          else 0)| ≤
    ∑ j ∈ J, |c j| * ∑ r ∈ Finset.Icc 1 ⌊x ^ c₀⌋₊,
      |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H]) (fun u => 1 * W j u) -
        (if r.Coprime H then x / ((H : ℝ) * (r : ℝ)) * (∫ t, Φ t) * 1 * μ j else 0)|
  have hswap : ∑ j ∈ J, |c j| * ∑ r ∈ Finset.Icc 1 ⌊x ^ c₀⌋₊,
        |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H]) (fun u => 1 * W j u) -
          (if r.Coprime H then x / ((H : ℝ) * (r : ℝ)) * (∫ t, Φ t) * 1 * μ j else 0)| =
      ∑ r ∈ Finset.Icc 1 ⌊x ^ c₀⌋₊, ∑ j ∈ J, |c j| *
        |shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H]) (fun u => 1 * W j u) -
          (if r.Coprime H then x / ((H : ℝ) * (r : ℝ)) * (∫ t, Φ t) * 1 * μ j else 0)| := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.mul_sum _ _ _
  rw [hswap]
  refine Finset.sum_le_sum fun r _ => ?_
  have hS : shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H])
      (fun u => 1 * ∑ j ∈ J, c j * W j u) =
      ∑ j ∈ J, c j * shiftSum Φ x (fun v => r ∣ v ∧ v ≡ b [MOD H]) (fun u => 1 * W j u) := by
    have hc : ∀ u, (1 : ℝ) * ∑ j ∈ J, c j * W j u = ∑ j ∈ J, c j * (1 * W j u) := fun u => by
      rw [one_mul]
      exact Finset.sum_congr rfl fun j _ => by rw [one_mul]
    rw [shiftSum_congr Φ x _ hc, shiftSum_finset_sum hR hx]
    exact Finset.sum_congr rfl fun j _ =>
      shiftSum_const_mul hR hx _ (c j) (fun u => 1 * W j u)
  have hMn : (if r.Coprime H then
        x / ((H : ℝ) * (r : ℝ)) * (∫ t, Φ t) * 1 * ∑ j ∈ J, c j * μ j else 0) =
      ∑ j ∈ J, c j *
        (if r.Coprime H then x / ((H : ℝ) * (r : ℝ)) * (∫ t, Φ t) * 1 * μ j else 0) := by
    by_cases hco : r.Coprime H
    · rw [if_pos hco, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [if_pos hco]
      ring
    · rw [if_neg hco]
      exact (Finset.sum_eq_zero fun j _ => by rw [if_neg hco, mul_zero]).symm
  rw [hS, hMn, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
  rw [← mul_sub, abs_mul]

/-- The arithmetic of the variance step: the upper-bound sieve with main term `X = x I μ`,
`μ ≤ C_v/n`, the sieve product `V ≤ C_V/(g L)` and the remainder `R_S ≤ D x L^{-2}`. -/
theorem variance_arith {S X V Ms RS D I CV g L x μ Cv η nR : ℝ} (hx : 0 < x) (hL : 0 < L)
    (hg : 0 < g) (hMs : 0 ≤ Ms) (hI : 0 ≤ I) (hη : 0 < η) (hμ0 : 0 ≤ μ) (hμ : μ ≤ Cv / nR)
    (hV0 : 0 ≤ V) (hV : V * (g * L) ≤ CV) (hX : X = x / ((1 : ℕ) : ℝ) * I * 1 * μ)
    (hS : S ≤ Ms * (X * V) + Ms * RS) (hRS : RS ≤ D * (x * L ^ (-(2 : ℝ))))
    (hE : Ms * D / η ≤ L) :
    S ≤ (Ms * I * CV * (1 / g) * Cv / nR + η) * (x / L) := by
  have hLne : L ≠ 0 := hL.ne'
  have hX' : X = x * I * μ := by rw [hX, Nat.cast_one, div_one, mul_one]
  have hgL : 0 < g * L := mul_pos hg hL
  have hVle : V ≤ CV / (g * L) := (le_div_iff₀ hgL).mpr hV
  have hxI : 0 ≤ x * I := mul_nonneg hx.le hI
  have hB : X * V ≤ x * I * (Cv / nR) * (CV / (g * L)) := by
    rw [hX']
    exact mul_le_mul (mul_le_mul_of_nonneg_left hμ hxI) hVle hV0
      (mul_nonneg hxI (hμ0.trans hμ))
  have hL2 : L ^ (-(2 : ℝ)) = (L ^ 2)⁻¹ := by rw [Real.rpow_neg hL.le, Real.rpow_two]
  have hxL2 : 0 ≤ x * (L ^ 2)⁻¹ := mul_nonneg hx.le (inv_pos.mpr (pow_pos hL 2)).le
  rw [hL2] at hRS
  have h4 : Ms * D ≤ L * η := (div_le_iff₀ hη).mp hE
  have hC : Ms * RS ≤ η * (x / L) :=
    calc Ms * RS ≤ Ms * (D * (x * (L ^ 2)⁻¹)) := mul_le_mul_of_nonneg_left hRS hMs
      _ = Ms * D * (x * (L ^ 2)⁻¹) := by ring
      _ ≤ L * η * (x * (L ^ 2)⁻¹) := mul_le_mul_of_nonneg_right h4 hxL2
      _ = η * (x / L) := by
          rw [div_eq_mul_inv, sq, mul_inv]
          calc L * η * (x * (L⁻¹ * L⁻¹)) = η * (x * L⁻¹) * (L * L⁻¹) := by ring
            _ = η * (x * L⁻¹) := by rw [mul_inv_cancel₀ hLne, mul_one]
  calc S ≤ Ms * (X * V) + Ms * RS := hS
    _ ≤ Ms * (x * I * (Cv / nR) * (CV / (g * L))) + η * (x / L) :=
        add_le_add (mul_le_mul_of_nonneg_left hB hMs) hC
    _ = (Ms * I * CV * (1 / g) * Cv / nR + η) * (x / L) := by ring

end Presieve

/-- **The variance step** (`[P-07:0649–0670]`, (ext:prime-deweight-square)), for every real `q`:
the field `variance` of `ExtractionOpenLeaves d H b q q₀`. -/
theorem varianceLink (q : ℝ) : VarianceLink q := by
  intro hPU hMB hMV hBS hMP hM Φ hΦ K
  obtain ⟨R, -, hR⟩ := hΦ.exists_upper
  obtain ⟨rlo, hrlo0, hrlo⟩ := hΦ.exists_lower
  obtain ⟨Ms, hMs0, h₀, hsieve⟩ := Presieve.shiftSum_sieve hBS hM
  obtain ⟨cK, CK, hcK, hmodel⟩ := hMB K
  obtain ⟨Cv, hCv⟩ := hMV K
  have hint : 0 ≤ ∫ t, Φ t := MeasureTheory.integral_nonneg fun t => hΦ.nonneg t
  obtain ⟨CV, hCV⟩ : ∃ CV : ℝ, CV = 2 ^ (1 : ℕ).primeFactors.card *
      (Real.exp (-Real.eulerMascheroniConstant) + 1) := ⟨_, rfl⟩
  obtain ⟨Ac, hAc⟩ : ∃ Ac : ℝ, Ac = 1 + 2 * (1 / cK) + 1 * (1 / (cK * cK)) := ⟨_, rfl⟩
  have hcK1 : 0 ≤ 1 / cK := (one_div_pos.mpr hcK).le
  have hcK2 : 0 ≤ 1 / (cK * cK) := (one_div_pos.mpr (mul_pos hcK hcK)).le
  have hAc0 : 0 ≤ Ac := by
    rw [hAc]
    linarith
  refine ⟨Ms * (∫ t, Φ t) * CV * (1 / (1 / 100)) * Cv, fun n hn 𝔄 hdisj η hη => ?_⟩
  obtain ⟨M₂, x₂, hrem⟩ := hPU (1 / 5) (by norm_num) (by norm_num) Φ hΦ n K 𝔄 hdisj 2 two_pos
  obtain ⟨card, hcard⟩ : ∃ card : ℝ,
      card = ((Finset.univ : Finset (Option (Fin n) × Option (Fin n))).card : ℝ) := ⟨_, rfl⟩
  have hcard0 : 0 ≤ card := by
    rw [hcard]
    exact Nat.cast_nonneg _
  have hmodelAll : ∀ᶠ x : ℝ in atTop, ∀ a : Fin n, cK ≤ arrayMean q (𝔄 a) x :=
    Filter.eventually_all.mpr fun a => (hmodel (𝔄 a)).mono fun x h => h.1
  have hVev : ∀ᶠ x : ℝ in atTop,
      (∏ p ∈ Presieve.sievePrimes (x ^ (1 / 100 : ℝ)), (1 - Presieve.sieveDensity 1 p)) *
        Real.log (x ^ (1 / 100 : ℝ)) ≤ CV := by
    rw [hCV]
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 100)).eventually
      (Presieve.eventually_sieveProduct_le hMP one_pos)
  filter_upwards [hmodelAll, hCv n hn 𝔄 hdisj, eventually_ge_atTop x₂,
    eventually_gt_atTop (1 : ℝ), hVev,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 99 / 100)).eventually_ge_atTop (1 / rlo),
    Real.tendsto_log_atTop.eventually_ge_atTop (max (Ms * (card * Ac * |M₂|) / η) 1)]
    with x hmlo hμle hx₂ hx1 hV hrough hLE
  have hx0 : 0 < x := by linarith
  have hL1 : 1 ≤ Real.log x := (le_max_right _ _).trans hLE
  have hL0 : 0 < Real.log x := by linarith
  have hEL : Ms * (card * Ac * |M₂|) / η ≤ Real.log x := (le_max_left _ _).trans hLE
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  -- the model on the primes of the family
  obtain ⟨P, hP⟩ : ∃ P : Finset ℕ, P = familyPrimes 𝔄 x := ⟨_, rfl⟩
  have hP1 : ∀ p ∈ P, 1 ≤ p := by
    intro p hp
    rw [hP] at hp
    obtain ⟨a, -, hpa⟩ := Finset.mem_biUnion.mp hp
    exact (prime_of_mem_arrayPrimes hpa).one_lt.le
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = modelMean P (arrayDeviation q 𝔄 x) := ⟨_, rfl⟩
  have hμ0 : 0 ≤ μ := by
    rw [hμ]
    exact modelMean_nonneg hP1 (arrayDeviation_nonneg q 𝔄 x)
  have hμle' : μ ≤ Cv / (n : ℝ) := by
    rw [hμ, hP]
    exact hμle
  -- the level `z = x^{1/100}`; the primes in the support are `z`-rough
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = x ^ (1 / 100 : ℝ) := ⟨_, rfl⟩
  have hz1 : 1 ≤ z := by
    rw [hz]
    exact Real.one_le_rpow hx1.le (by norm_num)
  have hz0 : 0 ≤ z := zero_le_one.trans hz1
  have hzx : z ≤ rlo * x := by
    have hsplit : x ^ (1 / 100 : ℝ) * x ^ (99 / 100 : ℝ) = x := by
      rw [← Real.rpow_add hx0, show (1 / 100 : ℝ) + 99 / 100 = 1 by norm_num, Real.rpow_one]
    have h1 : 1 ≤ rlo * x ^ (99 / 100 : ℝ) := by
      have h2 := (div_le_iff₀ hrlo0).mp hrough
      rw [mul_comm] at h2
      exact h2
    calc z = z * 1 := (mul_one z).symm
      _ ≤ z * (rlo * x ^ (99 / 100 : ℝ)) := mul_le_mul_of_nonneg_left h1 hz0
      _ = rlo * (x ^ (1 / 100 : ℝ) * x ^ (99 / 100 : ℝ)) := by
          rw [hz]
          ring
      _ = rlo * x := by rw [hsplit]
  have hstep1 : shiftSum Φ x Nat.Prime (arrayDeviation q 𝔄 x) ≤
      shiftSum Φ x (fun v => IsRough z v ∧ v ≡ 1 [MOD 1]) (arrayDeviation q 𝔄 x) := by
    refine Presieve.shiftSum_le_shiftSum_of_imp hR hx0 hΦ.nonneg
      (arrayDeviation_nonneg q 𝔄 x) fun u hprime hΦu => ⟨?_, Nat.modEq_one⟩
    intro p hp hdvd
    have hpe : p = u + 1 := (Nat.prime_dvd_prime_iff_eq hp hprime).mp hdvd
    have hu : rlo ≤ (u : ℝ) / x := by
      by_contra hcon
      exact hΦu (hrlo _ (not_le.mp hcon))
    have hu' : rlo * x ≤ (u : ℝ) := (le_div_iff₀ hx0).mp hu
    rw [hpe, Nat.cast_add, Nat.cast_one]
    linarith
  -- the upper bound of the block sieve
  have hX0 : 0 ≤ x / ((1 : ℕ) : ℝ) * (∫ t, Φ t) * 1 * μ :=
    mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg hx0.le (Nat.cast_nonneg 1)) hint)
      zero_le_one) hμ0
  obtain ⟨-, hs2⟩ := hsieve Φ R hR hΦ.nonneg x hx0 1 1 (arrayDeviation q 𝔄 x)
    (arrayDeviation_nonneg q 𝔄 x) z hz1 _ hX0
  have hlevel : z ^ 10 ≤ x ^ (1 / 5 : ℝ) := by
    rw [hz, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    exact Real.rpow_le_rpow_of_exponent_le hx1.le (by norm_num)
  have hRS := Presieve.sum_Icc_le_progressionRemainder (H := 1) (b := 1) (Φ := Φ) hlevel
    (fun _ => (1 : ℝ)) 1 (arrayDeviation q 𝔄 x) μ
    (X := x / ((1 : ℕ) : ℝ) * (∫ t, Φ t) * 1 * μ) rfl
    (F := arrayDeviation q 𝔄 x) (fun u => (one_mul _).symm)
  -- `Z` as a combination of the monomials
  obtain ⟨m, hm⟩ : ∃ m : Fin n → ℝ, ∀ a, m a = arrayMean q (𝔄 a) x := ⟨_, fun _ => rfl⟩
  have hmlo' : ∀ a, cK ≤ m a := fun a => by
    rw [hm a]
    exact hmlo a
  have hmpos : ∀ a, 0 < m a := fun a => lt_of_lt_of_le hcK (hmlo' a)
  obtain ⟨c, hc1, hc2, hc3, hc4⟩ : ∃ c : Option (Fin n) × Option (Fin n) → ℝ,
      c (none, none) = 1 ∧ (∀ a', c (none, some a') = 0) ∧
      (∀ a, c (some a, none) = -(2 / (n : ℝ) * (1 / m a))) ∧
      ∀ a a', c (some a, some a') = 1 / (n : ℝ) ^ 2 * (1 / (m a * m a')) :=
    ⟨fun j => match j with
      | (none, none) => 1
      | (none, some _) => 0
      | (some a, none) => -(2 / (n : ℝ) * (1 / m a))
      | (some a, some a') => 1 / (n : ℝ) ^ 2 * (1 / (m a * m a')),
      rfl, fun _ => rfl, fun _ => rfl, fun _ _ => rfl⟩
  obtain ⟨Wj, hWj⟩ : ∃ Wj : Option (Fin n) × Option (Fin n) → ℕ → ℝ,
      ∀ o₁ o₂, Wj (o₁, o₂) = pairWeight q 𝔄 x o₁ o₂ :=
    ⟨fun j => pairWeight q 𝔄 x j.1 j.2, fun _ _ => rfl⟩
  have hZ : ∀ u, arrayDeviation q 𝔄 x u = ∑ j, c j * Wj j u := by
    intro u
    rw [arrayDeviation_eq, Fintype.sum_prod_type, Fintype.sum_option]
    have h1 : ∑ y : Option (Fin n), c (none, y) * Wj (none, y) u =
        pairWeight q 𝔄 x none none u := by
      have h0 : ∑ a' : Fin n, c (none, some a') * Wj (none, some a') u = 0 :=
        Finset.sum_eq_zero fun a' _ => by rw [hc2 a', zero_mul]
      rw [Fintype.sum_option, hc1, one_mul, hWj, h0, add_zero]
    have h2 : ∀ a : Fin n, ∑ y : Option (Fin n), c (some a, y) * Wj (some a, y) u =
        -(2 / (n : ℝ) * (1 / m a)) * pairWeight q 𝔄 x (some a) none u +
          ∑ a' : Fin n, 1 / (n : ℝ) ^ 2 * (1 / (m a * m a')) *
            pairWeight q 𝔄 x (some a) (some a') u := fun a => by
      rw [Fintype.sum_option, hc3 a, hWj]
      exact congrArg _ (Finset.sum_congr rfl fun a' _ => by rw [hc4 a a', hWj])
    have e1 : ∑ a : Fin n, -(2 / (n : ℝ) * (1 / m a)) * pairWeight q 𝔄 x (some a) none u =
        -∑ a : Fin n, 2 / (n : ℝ) *
          (1 / arrayMean q (𝔄 a) x * pairWeight q 𝔄 x (some a) none u) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun a _ => by
        rw [hm a]
        ring
    have e2 : ∑ a : Fin n, ∑ a' : Fin n, 1 / (n : ℝ) ^ 2 * (1 / (m a * m a')) *
          pairWeight q 𝔄 x (some a) (some a') u =
        ∑ a : Fin n, 1 / (n : ℝ) ^ 2 * ∑ a' : Fin n,
          1 / (arrayMean q (𝔄 a) x * arrayMean q (𝔄 a') x) *
            pairWeight q 𝔄 x (some a) (some a') u :=
      Finset.sum_congr rfl fun a _ => by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a' _ => by
          rw [hm a, hm a']
          ring
    rw [h1, Finset.sum_congr rfl (fun a _ => h2 a), Finset.sum_add_distrib, e1, e2,
      Finset.mul_sum, Finset.mul_sum]
    ring
  have hfun : arrayDeviation q 𝔄 x = fun u => ∑ j, c j * Wj j u := funext hZ
  have hμsum : μ = ∑ j, c j * modelMean P (Wj j) := by
    rw [hμ, hfun, modelMean_finset_sum]
    exact Finset.sum_congr rfl fun j _ => modelMean_const_mul P (c j) (Wj j)
  have hsub : progressionRemainder 1 1 Φ x (1 / 5) (fun _ => 1) 1
        (fun u => ∑ j, c j * Wj j u) (∑ j, c j * modelMean P (Wj j)) ≤
      ∑ j, |c j| * progressionRemainder 1 1 Φ x (1 / 5) (fun _ => 1) 1 (Wj j)
        (modelMean P (Wj j)) :=
    Presieve.progressionRemainder_sum_le hR hx0 1 1 (1 / 5) Finset.univ c Wj
      (fun j => modelMean P (Wj j))
  rw [← hfun, ← hμsum] at hsub
  -- the remainders of the monomials, by Lemma 7.2 without tuple factors
  have hρ : ∀ j : Option (Fin n) × Option (Fin n),
      progressionRemainder 1 1 Φ x (1 / 5) (fun _ => 1) 1 (Wj j) (modelMean P (Wj j)) ≤
        M₂ * x * Real.log x ^ (-(2 : ℝ)) := by
    rintro ⟨o₁, o₂⟩
    rw [hWj, hP]
    exact hrem x hx₂ o₁ o₂
  have hρ0 : ∀ j : Option (Fin n) × Option (Fin n),
      0 ≤ progressionRemainder 1 1 Φ x (1 / 5) (fun _ => 1) 1 (Wj j) (modelMean P (Wj j)) :=
    fun j => by
      unfold progressionRemainder
      exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hcabs : ∀ j : Option (Fin n) × Option (Fin n), |c j| ≤ Ac := by
    rintro ⟨_ | a, _ | a'⟩
    · rw [hc1, abs_one, hAc]
      linarith
    · rw [hc2 a', abs_zero]
      exact hAc0
    · have hpos : 0 ≤ 1 / m a := (one_div_pos.mpr (hmpos a)).le
      have h1 : 2 / (n : ℝ) ≤ 2 := div_le_self zero_le_two hn1
      have h2 : 2 / (n : ℝ) * (1 / m a) ≤ 2 * (1 / cK) :=
        mul_le_mul h1 (one_div_le_one_div_of_le hcK (hmlo' a)) hpos zero_le_two
      rw [hc3 a, abs_neg, abs_of_nonneg (mul_nonneg (div_nonneg zero_le_two hn0.le) hpos), hAc]
      linarith
    · have hpos : 0 ≤ 1 / (m a * m a') := (one_div_pos.mpr (mul_pos (hmpos a) (hmpos a'))).le
      have hn2 : 0 ≤ 1 / (n : ℝ) ^ 2 := (one_div_pos.mpr (pow_pos hn0 2)).le
      have h1 : 1 / (n : ℝ) ^ 2 ≤ 1 := div_le_self zero_le_one (one_le_pow₀ hn1)
      have h2 : 1 / (m a * m a') ≤ 1 / (cK * cK) :=
        one_div_le_one_div_of_le (mul_pos hcK hcK)
          (mul_le_mul (hmlo' a) (hmlo' a') hcK.le (hmpos a).le)
      have h3 : 1 / (n : ℝ) ^ 2 * (1 / (m a * m a')) ≤ 1 * (1 / (cK * cK)) :=
        mul_le_mul h1 h2 hpos zero_le_one
      rw [hc4 a a', abs_of_nonneg (mul_nonneg hn2 hpos), hAc]
      linarith
  have hxL : 0 ≤ x * Real.log x ^ (-(2 : ℝ)) :=
    mul_nonneg hx0.le (Real.rpow_nonneg hL0.le _)
  have hPRZ : progressionRemainder 1 1 Φ x (1 / 5) (fun _ => 1) 1 (arrayDeviation q 𝔄 x) μ ≤
      card * Ac * |M₂| * (x * Real.log x ^ (-(2 : ℝ))) :=
    calc progressionRemainder 1 1 Φ x (1 / 5) (fun _ => 1) 1 (arrayDeviation q 𝔄 x) μ
        ≤ ∑ j, |c j| * progressionRemainder 1 1 Φ x (1 / 5) (fun _ => 1) 1 (Wj j)
            (modelMean P (Wj j)) := hsub
      _ ≤ ∑ _j : Option (Fin n) × Option (Fin n),
            Ac * (M₂ * x * Real.log x ^ (-(2 : ℝ))) :=
          Finset.sum_le_sum fun j _ => mul_le_mul (hcabs j) (hρ j) (hρ0 j) hAc0
      _ = card * (Ac * (M₂ * x * Real.log x ^ (-(2 : ℝ)))) := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
      _ = card * Ac * M₂ * (x * Real.log x ^ (-(2 : ℝ))) := by ring
      _ ≤ card * Ac * |M₂| * (x * Real.log x ^ (-(2 : ℝ))) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (le_abs_self M₂) (mul_nonneg hcard0 hAc0)) hxL
  -- the sieve product
  rw [← hz] at hV
  have hlogz : Real.log z = 1 / 100 * Real.log x := by
    rw [hz]
    exact Real.log_rpow hx0 _
  rw [hlogz] at hV
  have hV0 : 0 ≤ ∏ p ∈ Presieve.sievePrimes z, (1 - Presieve.sieveDensity 1 p) := by
    refine Finset.prod_nonneg fun p hp => ?_
    have h3 := Presieve.sieveDensity_le_half 1 ((Presieve.mem_sievePrimes hz0).mp hp).1
    linarith
  exact hstep1.trans (Presieve.variance_arith hx0 hL0 (by norm_num) hMs0 hint hη hμ0 hμle' hV0
    hV rfl hs2 (hRS.trans hPRZ) hEL)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
