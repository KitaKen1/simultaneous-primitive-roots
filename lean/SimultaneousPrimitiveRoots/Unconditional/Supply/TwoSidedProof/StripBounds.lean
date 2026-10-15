module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.StripIdentity
public import SimultaneousPrimitiveRoots.Unconditional.Supply.ClassicalInputs
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Scales
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Removal of the shared labels: the divisor sums and the collisions

`[P-06:0340–0370]`. For a configuration at `x` (`L = log x`):

* `norm_corePart_le`, `sum_corePart_dvd_le`, `sum_corePart_le`: "On `w ≍ x D_C` the count of its
  multiples is `O(x D_C / p)`; … a fixed higher divisor moment": for `m ∣ D_C` with active prime
  factors, `∑_{w, m ∣ w} |Ψ(w/(x D_C))/w · 𝓑 F(w) G(w + D_C)| ≤ K₀ L^{c₀} / m`
  (`G(m v) = G(v_*)`, so the divisor moment is taken over `v = (w + D_C)/m ≤ (c₂ x + 1) D_C / m`).
* `collision_le`: (cor:shared-collision), the probability of a collision of the shared labels is
  at most `c_P L² exp(-L^{.27}) / v₋` for `w + D_C ≤ x²`.
* `sum_core_error_le`: the two errors for fixed free labels.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference

noncomputable section

namespace Strip

section Bounds

variable {d : ℕ} {D : FixedData} {x : ℝ}

/-! ### The active primes of a configuration -/

/-- The laws `μ_g` of the active groups have total mass one. -/
theorem law_sum (I : Config d D x) (g : I.𝔊.Index) :
    ∑ p ∈ I.𝔊.group g, Graph.primeGroupLaw (I.𝔊.group g) p = 1 := by
  rcases g with g | g
  · exact I.primeGroups.small_law_sum g
  · exact I.primeGroups.big_law_sum g

/-- Every active prime is at least `exp(L^{.27})`. -/
theorem exp_le_active (I : Config d D x) (hL : 1 ≤ Real.log x) {p : ℕ}
    (hp : p ∈ I.𝔊.allPrimes) : Real.exp (Real.log x ^ (0.27 : ℝ)) ≤ (p : ℝ) := by
  obtain ⟨g, -, hg⟩ := Finset.mem_biUnion.mp hp
  rcases g with i | j
  · exact (I.groups.small_range i p hg).1
  · refine le_trans (Real.exp_le_exp.mpr ?_) (I.groups.big_range j p hg).1
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num)

/-- An integer `v ≥ 1` has at most `log v` active prime divisors. -/
theorem totalHits_le_log (I : Config d D x) (hL : 1 ≤ Real.log x) {v : ℕ} (hv : 1 ≤ v) :
    (I.𝔊.totalHits v : ℝ) ≤ Real.log (v : ℝ) := by
  rw [totalHits_eq_card I.groups]
  have hprod : ∏ p ∈ (I.𝔊.allPrimes.filter fun p => p ∣ v), p ∣ v :=
    Finset.prod_primes_dvd v
      (fun p hp => (prime_of_mem_allPrimes I.groups (Finset.mem_filter.mp hp).1).prime)
      (fun p hp => (Finset.mem_filter.mp hp).2)
  have hle : ∏ p ∈ (I.𝔊.allPrimes.filter fun p => p ∣ v), p ≤ v := Nat.le_of_dvd hv hprod
  have hlow : ∀ p ∈ (I.𝔊.allPrimes.filter fun p => p ∣ v), Real.exp 1 ≤ (p : ℝ) := fun p hp =>
    (Real.exp_le_exp.mpr (Real.one_le_rpow hL (by norm_num))).trans
      (exp_le_active I hL (Finset.mem_filter.mp hp).1)
  have h1 : Real.exp 1 ^ (I.𝔊.allPrimes.filter fun p => p ∣ v).card ≤ (v : ℝ) :=
    calc Real.exp 1 ^ (I.𝔊.allPrimes.filter fun p => p ∣ v).card
        = ∏ _p ∈ (I.𝔊.allPrimes.filter fun p => p ∣ v), Real.exp 1 :=
          (Finset.prod_const _).symm
      _ ≤ ∏ p ∈ (I.𝔊.allPrimes.filter fun p => p ∣ v), (p : ℝ) :=
          Finset.prod_le_prod (fun _ _ => (Real.exp_pos 1).le) hlow
      _ = ((∏ p ∈ (I.𝔊.allPrimes.filter fun p => p ∣ v), p : ℕ) : ℝ) :=
          (Nat.cast_prod _ _).symm
      _ ≤ (v : ℝ) := Nat.cast_le.mpr hle
  rw [Real.exp_one_pow] at h1
  exact (Real.le_log_iff_exp_le (Nat.cast_pos.mpr hv)).mpr h1

/-! ### The divisor sums -/

/-- **One term**: for `m ∣ w`, `m ∣ D_C` with active prime factors,
`|Ψ(w/(x D_C))/w · 𝓑 F(w) G(w + D_C)| ≤ Ψ_max B_f L^C / (c₁ x D_C) · τ((w + D_C)/m)^k`. -/
theorem norm_corePart_le (I : Config d D x) (hx : 0 < x) (hL : 0 ≤ Real.log x) {H : ℕ}
    (𝔅 : JointResidueWeight H) {F : ℕ → ℝ} {J : ℕ} (C : Fin I.𝔊.numBig → Finset (Fin J))
    (r : AuxList (groupFamily I.𝔊).big C) {c₁ c₂ Ψmax Bf : ℝ} (hc₁ : 0 < c₁)
    (hsup : ∀ t : ℝ, D.Ψ t ≠ 0 → c₁ ≤ t ∧ t ≤ c₂) (hΨmax : ∀ t : ℝ, ‖D.Ψ t‖ ≤ Ψmax)
    (hBf0 : 0 ≤ Bf)
    (hBf : ∀ u : ℕ, 1 ≤ u → (u : ℝ) ≤ c₂ * x * (tupleProd C r : ℝ) → |F u| ≤ Bf)
    {m : ℕ} (hm0 : 0 < m) (hmD : m ∣ tupleProd C r)
    (hmA : ∀ p : ℕ, p.Prime → p ∣ m → p ∈ I.𝔊.allPrimes) {w : ℕ} (hw : 1 ≤ w) (hmw : m ∣ w) :
    ‖corePart x D.Ψ 𝔅 F I.G C r w‖ ≤
      Ψmax * Bf * Real.log x ^ D.C / (c₁ * x * (tupleProd C r : ℝ)) *
        (((w + tupleProd C r) / m).divisors.card : ℝ) ^ ⌈D.C⌉₊ := by
  have hDpos : (0 : ℝ) < (tupleProd C r : ℝ) :=
    Nat.cast_pos.mpr (Comparison.tupleProd_pos I.primeGroups C r)
  have hxD : 0 < x * (tupleProd C r : ℝ) := mul_pos hx hDpos
  have hcD : 0 < c₁ * x * (tupleProd C r : ℝ) := by
    rw [mul_assoc]
    exact mul_pos hc₁ hxD
  have hΨ0 : 0 ≤ Ψmax := (norm_nonneg _).trans (hΨmax 0)
  have hLC : 0 ≤ Real.log x ^ D.C := Real.rpow_nonneg hL _
  have hB0 : 0 ≤ Ψmax * Bf * Real.log x ^ D.C / (c₁ * x * (tupleProd C r : ℝ)) :=
    div_nonneg (mul_nonneg (mul_nonneg hΨ0 hBf0) hLC) hcD.le
  have hτ0 : (0 : ℝ) ≤ (((w + tupleProd C r) / m).divisors.card : ℝ) ^ ⌈D.C⌉₊ :=
    pow_nonneg (Nat.cast_nonneg _) _
  by_cases h0 : D.Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) = 0
  · rw [corePart_eq_zero_of h0, norm_zero]
    exact mul_nonneg hB0 hτ0
  · obtain ⟨h1, h2⟩ := hsup _ h0
    have hlow : c₁ * x * (tupleProd C r : ℝ) ≤ (w : ℝ) := by
      have h := (le_div_iff₀ hxD).mp h1
      linarith
    have hup : (w : ℝ) ≤ c₂ * x * (tupleProd C r : ℝ) := by
      have h := (div_le_iff₀ hxD).mp h2
      linarith
    have hdv : m ∣ w + tupleProd C r := dvd_add hmw hmD
    have hv : m * ((w + tupleProd C r) / m) = w + tupleProd C r := Nat.mul_div_cancel' hdv
    have hvpos : 0 < (w + tupleProd C r) / m :=
      Nat.div_pos (Nat.le_of_dvd (by omega) hdv) hm0
    have hG : ‖I.G (w + tupleProd C r)‖ ≤ Real.log x ^ D.C *
        (((w + tupleProd C r) / m).divisors.card : ℝ) ^ ⌈D.C⌉₊ := by
      have h := norm_core_mul_le I.core hL hm0 hvpos hmA
      rwa [hv] at h
    have hA1 : ‖D.Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ)))‖ * ((w : ℝ))⁻¹ ≤
        Ψmax * (c₁ * x * (tupleProd C r : ℝ))⁻¹ :=
      mul_le_mul (hΨmax _) (inv_anti₀ hcD hlow) (inv_nonneg.mpr (Nat.cast_nonneg w)) hΨ0
    have h𝔅 : |𝔅.toFun (w : ZMod H) ((w + tupleProd C r : ℕ) : ZMod H)| ≤ 1 := by
      rw [abs_of_nonneg (𝔅.nonneg _ _)]
      exact 𝔅.le_one _ _
    have hFw : |F w| ≤ Bf := hBf w hw hup
    have hX1 : 0 ≤ Ψmax * (c₁ * x * (tupleProd C r : ℝ))⁻¹ :=
      mul_nonneg hΨ0 (inv_nonneg.mpr hcD.le)
    have hX2 : 0 ≤ Ψmax * (c₁ * x * (tupleProd C r : ℝ))⁻¹ * 1 := by
      rw [mul_one]
      exact hX1
    unfold corePart
    rw [norm_mul, norm_mul, norm_mul, norm_div, Complex.norm_natCast, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      div_eq_mul_inv (‖D.Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ)))‖) (w : ℝ)]
    calc ‖D.Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ)))‖ * ((w : ℝ))⁻¹ *
          |𝔅.toFun (w : ZMod H) ((w + tupleProd C r : ℕ) : ZMod H)| * |F w| *
          ‖I.G (w + tupleProd C r)‖
        ≤ Ψmax * (c₁ * x * (tupleProd C r : ℝ))⁻¹ * 1 * Bf *
            (Real.log x ^ D.C * (((w + tupleProd C r) / m).divisors.card : ℝ) ^ ⌈D.C⌉₊) :=
          mul_le_mul (mul_le_mul (mul_le_mul hA1 h𝔅 (abs_nonneg _) hX1) hFw (abs_nonneg _) hX2)
            hG (norm_nonneg _) (mul_nonneg hX2 hBf0)
      _ = _ := by ring

/-- **The sum over the multiples of `m`** is a divisor sum over `v = (w + D_C)/m`. -/
theorem sum_corePart_dvd_le (I : Config d D x) (hx : 0 < x) (hL : 0 ≤ Real.log x) {H : ℕ}
    (𝔅 : JointResidueWeight H) {F : ℕ → ℝ} {J : ℕ} (C : Fin I.𝔊.numBig → Finset (Fin J))
    (r : AuxList (groupFamily I.𝔊).big C) {c₁ c₂ Ψmax Bf : ℝ} (hc₁ : 0 < c₁)
    (hsup : ∀ t : ℝ, D.Ψ t ≠ 0 → c₁ ≤ t ∧ t ≤ c₂) (hΨmax : ∀ t : ℝ, ‖D.Ψ t‖ ≤ Ψmax)
    (hBf0 : 0 ≤ Bf)
    (hBf : ∀ u : ℕ, 1 ≤ u → (u : ℝ) ≤ c₂ * x * (tupleProd C r : ℝ) → |F u| ≤ Bf)
    {m : ℕ} (hm0 : 0 < m) (hmD : m ∣ tupleProd C r)
    (hmA : ∀ p : ℕ, p.Prime → p ∣ m → p ∈ I.𝔊.allPrimes) (N : ℕ) :
    ∑ w ∈ Finset.Ico 1 N, (if m ∣ w then ‖corePart x D.Ψ 𝔅 F I.G C r w‖ else 0) ≤
      Ψmax * Bf * Real.log x ^ D.C / (c₁ * x * (tupleProd C r : ℝ)) *
        ∑ v ∈ Finset.Icc 1 ⌊(c₂ * x + 1) * (tupleProd C r : ℝ) / (m : ℝ)⌋₊,
          (v.divisors.card : ℝ) ^ ⌈D.C⌉₊ := by
  have hDpos : (0 : ℝ) < (tupleProd C r : ℝ) :=
    Nat.cast_pos.mpr (Comparison.tupleProd_pos I.primeGroups C r)
  have hxD : 0 < x * (tupleProd C r : ℝ) := mul_pos hx hDpos
  have hcD : 0 < c₁ * x * (tupleProd C r : ℝ) := by
    rw [mul_assoc]
    exact mul_pos hc₁ hxD
  have hmpos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm0
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : ℝ,
      B₀ = Ψmax * Bf * Real.log x ^ D.C / (c₁ * x * (tupleProd C r : ℝ)) := ⟨_, rfl⟩
  have hB₀0 : 0 ≤ B₀ := by
    rw [hB₀]
    exact div_nonneg (mul_nonneg (mul_nonneg ((norm_nonneg _).trans (hΨmax 0)) hBf0)
      (Real.rpow_nonneg hL _)) hcD.le
  have hterm : ∀ w ∈ Finset.Ico 1 N,
      (if m ∣ w then ‖corePart x D.Ψ 𝔅 F I.G C r w‖ else 0) ≤
        (if m ∣ w ∧ (w : ℝ) ≤ c₂ * x * (tupleProd C r : ℝ) then
          B₀ * (((w + tupleProd C r) / m).divisors.card : ℝ) ^ ⌈D.C⌉₊ else 0) := by
    intro w hw
    have hw1 := (Finset.mem_Ico.mp hw).1
    by_cases hmw : m ∣ w
    · rw [if_pos hmw]
      by_cases hup : (w : ℝ) ≤ c₂ * x * (tupleProd C r : ℝ)
      · rw [if_pos ⟨hmw, hup⟩, hB₀]
        exact norm_corePart_le I hx hL 𝔅 C r hc₁ hsup hΨmax hBf0 hBf hm0 hmD hmA hw1 hmw
      · rw [if_neg fun h : m ∣ w ∧ (w : ℝ) ≤ c₂ * x * (tupleProd C r : ℝ) => hup h.2]
        have h0 : D.Ψ ((w : ℝ) / (x * (tupleProd C r : ℝ))) = 0 := by
          by_contra hne
          have h2 := (hsup _ hne).2
          have h := (div_le_iff₀ hxD).mp h2
          exact hup (by linarith)
        rw [corePart_eq_zero_of h0, norm_zero]
    · rw [if_neg hmw,
        if_neg fun h : m ∣ w ∧ (w : ℝ) ≤ c₂ * x * (tupleProd C r : ℝ) => hmw h.1]
  have hinj : Set.InjOn (fun w : ℕ => (w + tupleProd C r) / m)
      ((Finset.Ico 1 N).filter
        fun w => m ∣ w ∧ (w : ℝ) ≤ c₂ * x * (tupleProd C r : ℝ) : Finset ℕ) := by
    intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2.1
    have hb' := (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2.1
    have e1 : m * ((a + tupleProd C r) / m) = a + tupleProd C r :=
      Nat.mul_div_cancel' (dvd_add ha' hmD)
    have e2 : m * ((b + tupleProd C r) / m) = b + tupleProd C r :=
      Nat.mul_div_cancel' (dvd_add hb' hmD)
    have hab' : (a + tupleProd C r) / m = (b + tupleProd C r) / m := hab
    rw [hab'] at e1
    exact Nat.add_right_cancel (e1.symm.trans e2)
  have hsub : ((Finset.Ico 1 N).filter
      fun w => m ∣ w ∧ (w : ℝ) ≤ c₂ * x * (tupleProd C r : ℝ)).image
        (fun w : ℕ => (w + tupleProd C r) / m) ⊆
      Finset.Icc 1 ⌊(c₂ * x + 1) * (tupleProd C r : ℝ) / (m : ℝ)⌋₊ := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hwI, hmw, hup⟩ := Finset.mem_filter.mp hw
    have hw1 := (Finset.mem_Ico.mp hwI).1
    have hdv : m ∣ w + tupleProd C r := dvd_add hmw hmD
    have e1 : m * ((w + tupleProd C r) / m) = w + tupleProd C r := Nat.mul_div_cancel' hdv
    have e1r : (((w + tupleProd C r) / m : ℕ) : ℝ) * (m : ℝ) =
        (w : ℝ) + (tupleProd C r : ℝ) := by
      rw [mul_comm]
      exact_mod_cast e1
    refine Finset.mem_Icc.mpr ⟨Nat.div_pos (Nat.le_of_dvd (by omega) hdv) hm0, ?_⟩
    refine Nat.le_floor ?_
    rw [le_div_iff₀ hmpos, e1r]
    linarith
  rw [← hB₀]
  calc ∑ w ∈ Finset.Ico 1 N, (if m ∣ w then ‖corePart x D.Ψ 𝔅 F I.G C r w‖ else 0)
      ≤ ∑ w ∈ Finset.Ico 1 N,
          (if m ∣ w ∧ (w : ℝ) ≤ c₂ * x * (tupleProd C r : ℝ) then
            B₀ * (((w + tupleProd C r) / m).divisors.card : ℝ) ^ ⌈D.C⌉₊ else 0) :=
        Finset.sum_le_sum hterm
    _ = ∑ w ∈ (Finset.Ico 1 N).filter
          (fun w => m ∣ w ∧ (w : ℝ) ≤ c₂ * x * (tupleProd C r : ℝ)),
          B₀ * (((w + tupleProd C r) / m).divisors.card : ℝ) ^ ⌈D.C⌉₊ :=
        (Finset.sum_filter _ _).symm
    _ = B₀ * ∑ w ∈ (Finset.Ico 1 N).filter
          (fun w => m ∣ w ∧ (w : ℝ) ≤ c₂ * x * (tupleProd C r : ℝ)),
          (((w + tupleProd C r) / m).divisors.card : ℝ) ^ ⌈D.C⌉₊ := (Finset.mul_sum _ _ _).symm
    _ = B₀ * ∑ v ∈ ((Finset.Ico 1 N).filter
          fun w => m ∣ w ∧ (w : ℝ) ≤ c₂ * x * (tupleProd C r : ℝ)).image
            (fun w : ℕ => (w + tupleProd C r) / m), (v.divisors.card : ℝ) ^ ⌈D.C⌉₊ := by
        rw [Finset.sum_image hinj]
    _ ≤ B₀ * ∑ v ∈ Finset.Icc 1 ⌊(c₂ * x + 1) * (tupleProd C r : ℝ) / (m : ℝ)⌋₊,
          (v.divisors.card : ℝ) ^ ⌈D.C⌉₊ :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub fun v _ _ =>
            pow_nonneg (Nat.cast_nonneg _) _) hB₀0

/-- The divisor moment with the logarithm bounded by `3L`, for an exponent of any sign. -/
theorem sum_divisor_le {k : ℕ} {Cτ Aτ : ℝ} (hCτ : 0 < Cτ)
    (hτ : ∀ Y : ℝ, 1 ≤ Y → ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n.divisors.card : ℝ) ^ k ≤
      Cτ * Y * Real.log (2 * Y) ^ Aτ) {L Y' : ℝ} (hY2 : 2 ≤ Y')
    (hlog : Real.log (2 * Y') ≤ 3 * L) :
    ∑ n ∈ Finset.Icc 1 ⌊Y'⌋₊, (n.divisors.card : ℝ) ^ k ≤ Cτ * Y' * (3 * L) ^ (max Aτ 0) := by
  have h1 : 1 ≤ Real.log (2 * Y') :=
    (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith [Real.exp_one_lt_d9])
  have h2 : Real.log (2 * Y') ^ Aτ ≤ (3 * L) ^ (max Aτ 0) :=
    (Real.rpow_le_rpow_of_exponent_le h1 (le_max_left _ _)).trans
      (Real.rpow_le_rpow (by linarith) hlog (le_max_right _ _))
  exact (hτ Y' (by linarith)).trans
    (mul_le_mul_of_nonneg_left h2 (mul_nonneg hCτ.le (by linarith)))

/-- **The divisor sums** (`[P-06:0362–0366]`): for `m ∣ D_C` with active prime factors,
`∑_{w, m ∣ w} |Ψ(w/(x D_C))/w · 𝓑 F(w) G(w + D_C)| ≤ K₀ L^{C + A⁺} / m`. -/
theorem sum_corePart_le (I : Config d D x) (hx1 : 1 ≤ x) (hL1 : 1 ≤ Real.log x) {H : ℕ}
    (𝔅 : JointResidueWeight H) {F : ℕ → ℝ} {J : ℕ} (C : Fin I.𝔊.numBig → Finset (Fin J))
    (r : AuxList (groupFamily I.𝔊).big C) {c₁ c₂ Ψmax Bf : ℝ} (hc₁ : 0 < c₁)
    (hc₂x : 1 ≤ c₂ * x) (hc₂ : 0 ≤ c₂)
    (hsup : ∀ t : ℝ, D.Ψ t ≠ 0 → c₁ ≤ t ∧ t ≤ c₂) (hΨmax : ∀ t : ℝ, ‖D.Ψ t‖ ≤ Ψmax)
    (hBf0 : 0 ≤ Bf)
    (hBf : ∀ u : ℕ, 1 ≤ u → (u : ℝ) ≤ c₂ * x * (tupleProd C r : ℝ) → |F u| ≤ Bf)
    {Cτ Aτ : ℝ} (hCτ : 0 < Cτ)
    (hτ : ∀ Y : ℝ, 1 ≤ Y → ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, (n.divisors.card : ℝ) ^ ⌈D.C⌉₊ ≤
      Cτ * Y * Real.log (2 * Y) ^ Aτ)
    (hlogY : Real.log (2 * ((c₂ * x + 1) * (tupleProd C r : ℝ))) ≤ 3 * Real.log x)
    {m : ℕ} (hm0 : 0 < m) (hmD : m ∣ tupleProd C r)
    (hmA : ∀ p : ℕ, p.Prime → p ∣ m → p ∈ I.𝔊.allPrimes) (N : ℕ) :
    ∑ w ∈ Finset.Ico 1 N, (if m ∣ w then ‖corePart x D.Ψ 𝔅 F I.G C r w‖ else 0) ≤
      Ψmax * Bf * Cτ * (3 : ℝ) ^ (max Aτ 0) * ((c₂ + 1) / c₁) *
        Real.log x ^ (D.C + max Aτ 0) / (m : ℝ) := by
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  have hDN : 0 < tupleProd C r := Comparison.tupleProd_pos I.primeGroups C r
  have hDpos : (0 : ℝ) < (tupleProd C r : ℝ) := Nat.cast_pos.mpr hDN
  have hmpos : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr hm0
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := Nat.one_le_cast.mpr hm0
  have hmle : (m : ℝ) ≤ (tupleProd C r : ℝ) := Nat.cast_le.mpr (Nat.le_of_dvd hDN hmD)
  have hΨ0 : 0 ≤ Ψmax := (norm_nonneg _).trans (hΨmax 0)
  have hY0 : 0 ≤ (c₂ * x + 1) * (tupleProd C r : ℝ) := mul_nonneg (by linarith) hDpos.le
  have hY'2 : 2 ≤ (c₂ * x + 1) * (tupleProd C r : ℝ) / (m : ℝ) := by
    rw [le_div_iff₀ hmpos]
    exact mul_le_mul (by linarith) hmle hmpos.le (by linarith)
  have hlog' : Real.log (2 * ((c₂ * x + 1) * (tupleProd C r : ℝ) / (m : ℝ))) ≤
      3 * Real.log x :=
    le_trans (Real.log_le_log (by linarith)
      (mul_le_mul_of_nonneg_left (div_le_self hY0 hm1) zero_le_two)) hlogY
  have h1 := sum_corePart_dvd_le I hx0 hL0.le 𝔅 C r hc₁ hsup hΨmax hBf0 hBf hm0 hmD hmA N
  have h2 := sum_divisor_le hCτ hτ hY'2 hlog'
  have hB₀0 : 0 ≤ Ψmax * Bf * Real.log x ^ D.C / (c₁ * x * (tupleProd C r : ℝ)) :=
    div_nonneg (mul_nonneg (mul_nonneg hΨ0 hBf0) (Real.rpow_nonneg hL0.le _))
      (mul_nonneg (mul_nonneg hc₁.le hx0.le) hDpos.le)
  have hratio : (c₂ * x + 1) / (c₁ * x) ≤ (c₂ + 1) / c₁ := by
    rw [div_le_div_iff₀ (mul_pos hc₁ hx0) hc₁]
    nlinarith [mul_le_mul_of_nonneg_left hx1 hc₁.le]
  have hP0 : 0 ≤ Ψmax * Bf * Cτ * (3 : ℝ) ^ (max Aτ 0) * Real.log x ^ (D.C + max Aτ 0) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hΨ0 hBf0) hCτ.le)
      (Real.rpow_nonneg (by norm_num) _)) (Real.rpow_nonneg hL0.le _)
  have hD0 : (tupleProd C r : ℝ) ≠ 0 := hDpos.ne'
  have hx0' : x ≠ 0 := hx0.ne'
  have hc₁' : c₁ ≠ 0 := hc₁.ne'
  have hm0' : (m : ℝ) ≠ 0 := hmpos.ne'
  calc ∑ w ∈ Finset.Ico 1 N, (if m ∣ w then ‖corePart x D.Ψ 𝔅 F I.G C r w‖ else 0)
      ≤ Ψmax * Bf * Real.log x ^ D.C / (c₁ * x * (tupleProd C r : ℝ)) *
          ∑ v ∈ Finset.Icc 1 ⌊(c₂ * x + 1) * (tupleProd C r : ℝ) / (m : ℝ)⌋₊,
            (v.divisors.card : ℝ) ^ ⌈D.C⌉₊ := h1
    _ ≤ Ψmax * Bf * Real.log x ^ D.C / (c₁ * x * (tupleProd C r : ℝ)) *
          (Cτ * ((c₂ * x + 1) * (tupleProd C r : ℝ) / (m : ℝ)) *
            (3 * Real.log x) ^ (max Aτ 0)) := mul_le_mul_of_nonneg_left h2 hB₀0
    _ = Ψmax * Bf * Cτ * (3 : ℝ) ^ (max Aτ 0) * Real.log x ^ (D.C + max Aτ 0) *
          ((c₂ * x + 1) / (c₁ * x)) * (m : ℝ)⁻¹ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hL0.le, Real.rpow_add hL0]
        field_simp
    _ ≤ Ψmax * Bf * Cτ * (3 : ℝ) ^ (max Aτ 0) * Real.log x ^ (D.C + max Aτ 0) *
          ((c₂ + 1) / c₁) * (m : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hratio hP0)
          (inv_nonneg.mpr hmpos.le)
    _ = _ := by ring

/-! ### Collisions -/

/-- **(cor:shared-collision) for a configuration** (`[P-06:0340–0346]`): for `w ≥ 1` with
`w + D_C ≤ x²`, the shared labels collide with probability at most
`c_P L² exp(-L^{.27}) / v₋`. -/
theorem collision_le (I : Config d D x) (hL1 : 1 ≤ Real.log x) {J m₀ : ℕ}
    (C : Fin I.𝔊.numBig → Finset (Fin J)) (hC : ∀ g, (C g).card ≤ m₀)
    (r : AuxList (groupFamily I.𝔊).big C) {w : ℕ} (hw : 1 ≤ w)
    (hwx : ((w + tupleProd C r : ℕ) : ℝ) ≤ x ^ 2) :
    ∑ σ : ShT I.𝔊 C, shWeight σ * badInd σ (forbid r w) ≤
      ((2 * ((J : ℝ) + 1) * D.P.C₀) ^ 2 +
          2 * ((J : ℝ) + 1) * D.P.C₀ * ((m₀ : ℝ) * D.P.C₀ + 4)) * Real.log x ^ 2 *
        (D.P.vlo * Real.exp (Real.log x ^ (0.27 : ℝ)))⁻¹ := by
  have hL0 : 0 < Real.log x := lt_of_lt_of_le one_pos hL1
  have hlogL : Real.log (Real.log x) ≤ Real.log x := by
    have h := Real.log_le_sub_one_of_pos hL0
    linarith
  have hC0 : 0 < D.P.C₀ := D.P.C₀_pos
  have hpos : 0 < D.P.vlo * Real.exp (Real.log x ^ (0.27 : ℝ)) :=
    mul_pos D.P.vlo_pos (Real.exp_pos _)
  have hδ : 0 ≤ (D.P.vlo * Real.exp (Real.log x ^ (0.27 : ℝ)))⁻¹ := inv_nonneg.mpr hpos.le
  have hatom : ∀ (k : ShIdx I.𝔊 C) (a : {p : ℕ // p ∈ shGrp I.𝔊 C k}),
      Graph.primeGroupLaw (shGrp I.𝔊 C k) a ≤
        (D.P.vlo * Real.exp (Real.log x ^ (0.27 : ℝ)))⁻¹ := by
    intro k a
    have hV : D.P.vlo ≤ Graph.primeGroupReciprocalMass (shGrp I.𝔊 C k) := by
      rw [shGrp_eq]
      exact I.groups.mass_ge _
    have hmem : (a : ℕ) ∈ I.𝔊.allPrimes := by
      have h : (a : ℕ) ∈ I.𝔊.group (shIndex k) := by
        rw [← shGrp_eq]
        exact a.2
      exact Finset.mem_biUnion.mpr ⟨shIndex k, Finset.mem_univ _, h⟩
    have hp := exp_le_active I hL1 hmem
    unfold Graph.primeGroupLaw
    rw [one_div]
    exact inv_anti₀ hpos (mul_le_mul hV hp (Real.exp_pos _).le (D.P.vlo_pos.le.trans hV))
  have hmain := sum_shWeight_badInd_le (law_sum I) hδ hatom (forbid r w)
  -- the number of shared slots
  have hn : (Fintype.card (ShIdx I.𝔊 C) : ℝ) ≤ 2 * ((J : ℝ) + 1) * D.P.C₀ * Real.log x := by
    have h1 : Fintype.card (ShIdx I.𝔊 C) ≤ (J + 1) * (I.𝔊.numSmall + I.𝔊.numBig) := by
      have h := card_shIdx_add (𝔊 := I.𝔊) C
      omega
    have h2 : (Fintype.card (ShIdx I.𝔊 C) : ℝ) ≤
        ((J : ℝ) + 1) * ((I.𝔊.numSmall : ℝ) + (I.𝔊.numBig : ℝ)) := by
      exact_mod_cast h1
    have h3 : (I.𝔊.numSmall : ℝ) ≤ D.P.C₀ * Real.log x :=
      I.groups.numSmall_le.trans (mul_le_mul_of_nonneg_left hlogL hC0.le)
    have h4 : (I.𝔊.numBig : ℝ) ≤ D.P.C₀ * Real.log x :=
      I.groups.numBig_le.trans (mul_le_mul_of_nonneg_left hlogL hC0.le)
    have hJ : (0 : ℝ) ≤ (J : ℝ) + 1 := by positivity
    calc (Fintype.card (ShIdx I.𝔊 C) : ℝ)
        ≤ ((J : ℝ) + 1) * ((I.𝔊.numSmall : ℝ) + (I.𝔊.numBig : ℝ)) := h2
      _ ≤ ((J : ℝ) + 1) * (D.P.C₀ * Real.log x + D.P.C₀ * Real.log x) :=
          mul_le_mul_of_nonneg_left (add_le_add h3 h4) hJ
      _ = 2 * ((J : ℝ) + 1) * D.P.C₀ * Real.log x := by ring
  -- the number of forbidden primes
  have hf : ((forbid r w).card : ℝ) ≤ ((m₀ : ℝ) * D.P.C₀ + 4) * Real.log x := by
    have h1 : ((forbid r w).card : ℝ) ≤ ((∑ g, (C g).card : ℕ) : ℝ) +
        ((I.𝔊.totalHits w : ℝ) + (I.𝔊.totalHits (w + tupleProd C r) : ℝ)) := by
      exact_mod_cast card_forbid_le I.groups r w
    have h2 : ((∑ g, (C g).card : ℕ) : ℝ) ≤ (m₀ : ℝ) * D.P.C₀ * Real.log x := by
      have h : ∑ g, (C g).card ≤ I.𝔊.numBig * m₀ := by
        calc ∑ g, (C g).card ≤ ∑ _g : Fin I.𝔊.numBig, m₀ := Finset.sum_le_sum fun g _ => hC g
          _ = I.𝔊.numBig * m₀ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      have h' : ((∑ g, (C g).card : ℕ) : ℝ) ≤ (I.𝔊.numBig : ℝ) * (m₀ : ℝ) := by
        exact_mod_cast h
      have h4 : (I.𝔊.numBig : ℝ) ≤ D.P.C₀ * Real.log x :=
        I.groups.numBig_le.trans (mul_le_mul_of_nonneg_left hlogL hC0.le)
      calc ((∑ g, (C g).card : ℕ) : ℝ) ≤ (I.𝔊.numBig : ℝ) * (m₀ : ℝ) := h'
        _ ≤ (D.P.C₀ * Real.log x) * (m₀ : ℝ) :=
            mul_le_mul_of_nonneg_right h4 (Nat.cast_nonneg _)
        _ = (m₀ : ℝ) * D.P.C₀ * Real.log x := by ring
    have hx2 : Real.log (x ^ 2) = 2 * Real.log x := by
      rw [Real.log_pow, Nat.cast_ofNat]
    have hwD : 1 ≤ w + tupleProd C r := by omega
    have hwle : (w : ℝ) ≤ x ^ 2 := by
      have h : (w : ℝ) ≤ ((w + tupleProd C r : ℕ) : ℝ) := Nat.cast_le.mpr (Nat.le_add_right _ _)
      linarith
    have h3 : (I.𝔊.totalHits w : ℝ) ≤ 2 * Real.log x :=
      (totalHits_le_log I hL1 hw).trans
        ((Real.log_le_log (Nat.cast_pos.mpr hw) hwle).trans_eq hx2)
    have h4 : (I.𝔊.totalHits (w + tupleProd C r) : ℝ) ≤ 2 * Real.log x :=
      (totalHits_le_log I hL1 hwD).trans
        ((Real.log_le_log (Nat.cast_pos.mpr hwD) hwx).trans_eq hx2)
    linarith
  have hn0 : (0 : ℝ) ≤ (Fintype.card (ShIdx I.𝔊 C) : ℝ) := Nat.cast_nonneg _
  have hf0 : (0 : ℝ) ≤ ((forbid r w).card : ℝ) := Nat.cast_nonneg _
  have haL : 0 ≤ 2 * ((J : ℝ) + 1) * D.P.C₀ * Real.log x := hn0.trans hn
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ hδ)
  calc (Fintype.card (ShIdx I.𝔊 C) : ℝ) ^ 2 +
        (Fintype.card (ShIdx I.𝔊 C) : ℝ) * ((forbid r w).card : ℝ)
      ≤ (2 * ((J : ℝ) + 1) * D.P.C₀ * Real.log x) ^ 2 +
          (2 * ((J : ℝ) + 1) * D.P.C₀ * Real.log x) *
            (((m₀ : ℝ) * D.P.C₀ + 4) * Real.log x) :=
        add_le_add (pow_le_pow_left₀ hn0 hn 2) (mul_le_mul hn hf hf0 haL)
    _ = _ := by ring

/-- A free label divides `w` only if one of the free slots carries a divisor of `w`. -/
theorem freeInd_le {𝔊 : ActiveGroups} {J : ℕ} {C : Fin 𝔊.numBig → Finset (Fin J)}
    (r : AuxList (groupFamily 𝔊).big C) (w : ℕ) :
    freeInd r w ≤ ∑ gi : (Σ g : Fin 𝔊.numBig, {i : Fin J // i ∈ C g}),
      (if (r gi.1 gi.2 : ℕ) ∣ w then (1 : ℝ) else 0) := by
  have hnn : ∀ gi : (Σ g : Fin 𝔊.numBig, {i : Fin J // i ∈ C g}),
      (0 : ℝ) ≤ (if (r gi.1 gi.2 : ℕ) ∣ w then (1 : ℝ) else 0) := fun gi => by
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  unfold freeInd
  split_ifs with h
  · obtain ⟨g, i, hd⟩ := h
    have hterm : (1 : ℝ) = (if (r g i : ℕ) ∣ w then (1 : ℝ) else 0) := (if_pos hd).symm
    exact hterm.le.trans (Finset.single_le_sum
      (f := fun gi : (Σ g : Fin 𝔊.numBig, {i : Fin J // i ∈ C g}) =>
        (if (r gi.1 gi.2 : ℕ) ∣ w then (1 : ℝ) else 0))
      (fun gi _ => hnn gi) (Finset.mem_univ ⟨g, i⟩))
  · exact Finset.sum_nonneg fun gi _ => hnn gi

end Bounds

end Strip

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
