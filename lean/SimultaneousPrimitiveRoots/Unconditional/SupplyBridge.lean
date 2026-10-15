module

public import SimultaneousPrimitiveRoots.ConditionalMain
public import SimultaneousPrimitiveRoots.Artin.CumulativeDensity
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Candidate supply from the fixed-class long-prime statistic

The public paper (`Positive Lower Density of Simultaneous Primitive Roots`, 9 Oct 2026) derives
from its marked correlation inputs (M1)–(M3) the statistic `prop:ap`:

`∑_p Φ((p-1)/x) 1_{p ≡ b (H)} (f_x(p-1) - C_x) = o(x / log x)`,

where `f_x(n) = #{Q prime : Q ∣ n, x^α < Q ≤ x^β}` and `C_x = ∑_{x^α < Q ≤ x^β} 1/Q`, for fixed
`H ≥ 1`, a reduced class `b`, fixed `1/2 < α < β < 1`, and a fixed smooth compactly supported
`Φ ≥ 0` on `(0, ∞)` (`FixedClassLongPrimeStatistic α β`).

Its corollary `cor:supply` is the candidate supply of the Lean reduction. With `α = 1 - η`:

`candidateSupplyBound_of_fixedClassLongPrimeStatistic`:
`FixedClassLongPrimeStatistic (1 - η) β → ∃ θ > 0, ∀ A, CandidateSupplyBound A η θ`.

`FixedClassLongPrimeStatistic` is a hypothesis of the theorem here, not an axiom.

Ingredients:
* the prime number theorem in `(ax, bx]` for a fixed reduced class (Tau Ceti's Chebotarev
  theorem for `ℚ(ζ_H)`, `eventually_residuePrimesBetween_ge`);
* `C_x ≥ (β - α) / (8 β log 2)` from the dyadic prime number theorem
  (`eventually_longPrimeMass_ge`);
* a fixed smooth bump `Φ`, equal to `1` on `[11/8, 13/8]` and supported in `(5/4, 7/4)`.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Unconditional

open Filter Asymptotics NumberField IsDedekindDomain TauCeti
open scoped Topology ContDiff NumberField
noncomputable section

/-! ### The statistic of `prop:ap` -/

/-- `f_x(n)`: the number of primes `Q ∣ n` with `x^α < Q ≤ x^β`. -/
def longPrimeCount (α β x : ℝ) (n : ℕ) : ℕ :=
  (n.primeFactors.filter fun Q : ℕ => x ^ α < (Q : ℝ) ∧ (Q : ℝ) ≤ x ^ β).card

/-- `C_x = ∑ 1 / Q` over the primes `x^α < Q ≤ x^β`. -/
def longPrimeMass (α β x : ℝ) : ℝ :=
  ∑ Q ∈ (Finset.range (⌊x ^ β⌋₊ + 1)).filter (fun Q : ℕ => Q.Prime ∧ x ^ α < (Q : ℝ)),
    (1 : ℝ) / Q

/-- `∑_p Φ((p - 1)/x) 1_{p ≡ b (H)} (f_x(p - 1) - C_x)`. -/
def fixedClassLongPrimeSum (α β : ℝ) (H b : ℕ) (Φ : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ᶠ p : ℕ, if p.Prime ∧ p ≡ b [MOD H] then
    Φ (((p : ℝ) - 1) / x) * ((longPrimeCount α β x (p - 1) : ℝ) - longPrimeMass α β x) else 0

/-- **The fixed-class long-prime statistic** (`prop:ap` of the public paper): for every fixed
modulus `H`, reduced class `b` and smooth compactly supported `Φ ≥ 0` on `(0, ∞)`,
`∑_p Φ((p-1)/x) 1_{p ≡ b (H)} (f_x(p-1) - C_x) = o(x / log x)`. -/
def FixedClassLongPrimeStatistic (α β : ℝ) : Prop :=
  ∀ H b : ℕ, 0 < H → b.Coprime H → ∀ Φ : ℝ → ℝ, ContDiff ℝ ∞ Φ → HasCompactSupport Φ →
    tsupport Φ ⊆ Set.Ioi 0 → (∀ t, 0 ≤ Φ t) →
      fixedClassLongPrimeSum α β H b Φ =o[atTop] fun x : ℝ => x / Real.log x

/-! ### Primes of a fixed class in `(ax, bx]` -/

/-- Primes `p ∈ (y₁, y₂]` with `p ≡ u (mod n)`. -/
def residuePrimesBetween (n u : ℕ) (y₁ y₂ : ℝ) : Finset ℕ :=
  (Finset.range (⌊y₂⌋₊ + 1)).filter fun p => p.Prime ∧ y₁ < (p : ℝ) ∧ p ≡ u [MOD n]

section Cyclotomic

variable {n : ℕ} [NeZero n] {F : Type*} [Field F] [NumberField F]
  [IsCyclotomicExtension {n} ℚ F] [IsGalois ℚ F]

open Classical in
/-- An increment of the Frobenius count of `ζ ↦ ζ ^ u` is at most the number of primes in
`(y₁, y₂]` congruent to `u`, up to the primes dividing `n`. -/
theorem frobeniusPrimeCount_sub_le {u : ℕ} (hu : u.Coprime n) {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) :
    (Chebotarev.frobeniusPrimeCount ℚ F (ConjClasses.mk (residueAut n F hu)) y₂ : ℝ) -
      Chebotarev.frobeniusPrimeCount ℚ F (ConjClasses.mk (residueAut n F hu)) y₁ ≤
        (residuePrimesBetween n u y₁ y₂).card + n := by
  set C := ConjClasses.mk (residueAut n F hu)
  set S2 := (primesLE ℚ y₂).filter (· ∈ Chebotarev.frobeniusPrimeSet ℚ F C)
  set S1 := (primesLE ℚ y₁).filter (· ∈ Chebotarev.frobeniusPrimeSet ℚ F C)
  have hsub : S1 ⊆ S2 := by
    intro v hv
    obtain ⟨hvle, hvC⟩ := Finset.mem_filter.mp hv
    refine Finset.mem_filter.mpr ⟨?_, hvC⟩
    rw [mem_normLE] at hvle ⊢
    linarith
  rw [frobeniusPrimeCount_eq_filter_card, frobeniusPrimeCount_eq_filter_card]
  change (S2.card : ℝ) - S1.card ≤ _
  have hdiff : (S2.card : ℝ) - S1.card = ((S2 \ S1).card : ℝ) := by
    rw [Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
  rw [hdiff]
  set D := S2 \ S1
  set Dg := D.filter fun v => ¬ Ideal.absNorm v.asIdeal ∣ n
  set Db := D.filter fun v => Ideal.absNorm v.asIdeal ∣ n
  have hsplit : D.card = Db.card + Dg.card :=
    (Finset.card_filter_add_card_filter_not (s := D)
      (p := fun v => Ideal.absNorm v.asIdeal ∣ n)).symm
  have hinj : Set.InjOn (fun v : HeightOneSpectrum (𝓞 ℚ) => Ideal.absNorm v.asIdeal) ↑D :=
    absNorm_injective_rat.injOn
  have hgood : Dg.card ≤ (residuePrimesBetween n u y₁ y₂).card := by
    apply Finset.card_le_card_of_injOn (fun v => Ideal.absNorm v.asIdeal)
    · intro v hv
      have hv' := Finset.mem_filter.mp (Finset.mem_coe.mp hv)
      obtain ⟨hvD, hvn⟩ := hv'
      obtain ⟨hv2, hv1⟩ := Finset.mem_sdiff.mp hvD
      obtain ⟨hvle, hvC⟩ := Finset.mem_filter.mp hv2
      have hvgt : y₁ < (Ideal.absNorm v.asIdeal : ℝ) := by
        by_contra hcon
        exact hv1 (Finset.mem_filter.mpr ⟨by rw [mem_normLE]; linarith, hvC⟩)
      rw [mem_normLE] at hvle
      have hprime : (Ideal.absNorm v.asIdeal).Prime := by
        rw [Rat.HeightOneSpectrum.absNorm_asIdeal]
        exact Rat.HeightOneSpectrum.prime_natGenerator v
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨?_, hprime, hvgt,
        absNorm_modEq_of_mem_frobeniusPrimeSet hu hvC hvn⟩)
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_floor hvle))
    · exact hinj.mono (fun v hv => (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).1)
  have hbad : Db.card ≤ n := by
    have hle : Db.card ≤ n.divisors.card := by
      apply Finset.card_le_card_of_injOn (fun v => Ideal.absNorm v.asIdeal)
      · intro v hv
        have hv' := Finset.mem_filter.mp (Finset.mem_coe.mp hv)
        exact Finset.mem_coe.mpr (Nat.mem_divisors.mpr ⟨hv'.2, NeZero.ne n⟩)
      · exact hinj.mono (fun v hv => (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).1)
    exact hle.trans (Nat.card_divisors_le_self n)
  rw [hsplit]
  push_cast
  have h1 : (Dg.card : ℝ) ≤ (residuePrimesBetween n u y₁ y₂).card := by exact_mod_cast hgood
  have h2 : (Db.card : ℝ) ≤ n := by exact_mod_cast hbad
  linarith

end Cyclotomic

/-- Frobenius counts at `b x`, normalized by `x / log x`, tend to `b` times the Chebotarev
density. -/
theorem tendsto_frobeniusPrimeCount_scaled (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (C : ConjClasses (L ≃ₐ[K] L)) {b : ℝ} (hb : 0 < b) :
    Tendsto (fun x : ℝ => (Chebotarev.frobeniusPrimeCount K L C (b * x) : ℝ) /
      (x / Real.log x)) atTop
      (𝓝 (b * ((Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L)))) := by
  set d : ℝ := (Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L)
  set g : ℝ → ℝ := fun y =>
    (Chebotarev.frobeniusPrimeCount K L C y : ℝ) / (y / Real.log y) with hg
  have h1 : Tendsto g atTop (𝓝 d) := Chebotarev.tendsto_frobeniusPrimeCount K L C
  have h2 : Tendsto (fun x : ℝ => g (b * x)) atTop (𝓝 d) :=
    h1.comp (Tendsto.const_mul_atTop hb tendsto_id)
  have hlog : Tendsto (fun x : ℝ => Real.log b / Real.log x) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds Real.tendsto_log_atTop
  have h3 : Tendsto (fun x : ℝ => b / (1 + Real.log b / Real.log x)) atTop (𝓝 b) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add hlog
    rw [add_zero] at h
    have h' := (tendsto_const_nhds (x := b)).div h (by norm_num : (1 : ℝ) ≠ 0)
    rw [div_one] at h'
    exact h'
  have h4 := h2.mul h3
  rw [show d * b = b * d by ring] at h4
  apply h4.congr'
  filter_upwards [eventually_gt_atTop (max 1 (1 / b))] with x hx
  have hx1 : 1 < x := lt_of_le_of_lt (le_max_left _ _) hx
  have hx0 : 0 < x := by linarith
  have hbx : 1 < b * x := by
    have h' : 1 / b < x := lt_of_le_of_lt (le_max_right _ _) hx
    rw [div_lt_iff₀ hb] at h'
    linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hlbx : Real.log (b * x) = Real.log b + Real.log x := Real.log_mul hb.ne' hx0.ne'
  have hden : 0 < Real.log b + Real.log x := by rw [← hlbx]; exact Real.log_pos hbx
  simp only [hg]
  rw [hlbx]
  have hb0 : b ≠ 0 := hb.ne'
  have hx0' : x ≠ 0 := hx0.ne'
  have hlx' : Real.log x ≠ 0 := hlx.ne'
  have hden' : Real.log b + Real.log x ≠ 0 := hden.ne'
  have e1 : 1 + Real.log b / Real.log x = (Real.log b + Real.log x) / Real.log x := by
    field_simp; ring
  rw [e1]
  field_simp

/-- **Primes of a fixed class in `(ax, bx]`.** For fixed `n ≥ 1`, a unit residue `u`,
`0 < a < b` and `θ < 1`, eventually `#{p ∈ (ax, bx] : p ≡ u (mod n)} ≥ θ (b - a) x / (φ(n) log x)`. -/
theorem eventually_residuePrimesBetween_ge {n u : ℕ} (hn : 0 < n) (hu : u.Coprime n)
    {a b θ : ℝ} (ha : 0 < a) (hab : a < b) (hθ : θ < 1) :
    ∀ᶠ x : ℝ in atTop, θ * ((b - a) / (Nat.totient n : ℝ)) * (x / Real.log x) ≤
      ((residuePrimesBetween n u (a * x) (b * x)).card : ℝ) := by
  have : NeZero n := ⟨hn.ne'⟩
  let F := CyclotomicField n ℚ
  have : IsCyclotomicExtension {n} ℚ F := CyclotomicField.isCyclotomicExtension n ℚ
  have : NumberField F := IsCyclotomicExtension.numberField {n} ℚ F
  have : IsGalois ℚ F := IsCyclotomicExtension.isGalois {n} ℚ F
  set C := ConjClasses.mk (residueAut n F hu)
  have hphi : (0 : ℝ) < Nat.totient n := by exact_mod_cast Nat.totient_pos.mpr hn
  set d : ℝ := 1 / (Nat.totient n : ℝ) with hd
  have hdpos : 0 < d := by positivity
  have hb0 : 0 < b := ha.trans hab
  have htb := tendsto_frobeniusPrimeCount_scaled ℚ F C hb0
  have hta := tendsto_frobeniusPrimeCount_scaled ℚ F C ha
  rw [card_conjClass_residueAut (n := n) (F := F) hu,
    card_gal_cyclotomic (n := n) (F := F), Nat.cast_one] at htb hta
  have hsmall : Tendsto (fun x : ℝ => (n : ℝ) / (x / Real.log x)) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h' := h.const_mul (n : ℝ)
    rw [mul_zero] at h'
    apply h'.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    simp only [pow_one, one_mul, add_zero]
    field_simp
  have hcomb := (htb.sub hta).sub hsmall
  rw [sub_zero] at hcomb
  have hlim : θ * ((b - a) * d) < b * d - a * d := by
    have hpos : 0 < (b - a) * d := mul_pos (by linarith) hdpos
    rcases le_or_gt θ 0 with h0 | h0
    · nlinarith
    · nlinarith
  have hev := hcomb.eventually (lt_mem_nhds hlim)
  filter_upwards [hev, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hscale : 0 < x / Real.log x := div_pos hx0 (Real.log_pos hx1)
  have hcount := frobeniusPrimeCount_sub_le (F := F) hu
    (show a * x ≤ b * x by nlinarith)
  have hx' : θ * ((b - a) * d) <
      (((Chebotarev.frobeniusPrimeCount ℚ F C (b * x) : ℝ) -
        Chebotarev.frobeniusPrimeCount ℚ F C (a * x)) - n) / (x / Real.log x) := by
    rw [sub_div, sub_div]
    exact hx
  have hlt := (lt_div_iff₀ hscale).mp hx'
  have hrw : θ * ((b - a) / (Nat.totient n : ℝ)) = θ * ((b - a) * d) := by
    rw [hd]; ring
  rw [hrw]
  linarith

/-! ### `C_x` is bounded below -/

/-- The dyadic prime number theorem as an eventual lower bound. -/
theorem exists_dyadicPrimes_ge :
    ∃ Y₀ : ℝ, 1 < Y₀ ∧ ∀ y : ℝ, Y₀ ≤ y →
      y / (2 * Real.log y) ≤
        (((Finset.range (⌊2 * y⌋₊ + 1)).filter fun Q : ℕ => Q.Prime ∧ y < (Q : ℝ)).card : ℝ) := by
  have h := Artin.tendsto_dyadicPrimes
  have hev := h.eventually (lt_mem_nhds (show (1 : ℝ) / 2 < 1 by norm_num))
  obtain ⟨Y₁, hY₁⟩ := (hev.and (eventually_gt_atTop (1 : ℝ))).exists_forall_of_atTop
  refine ⟨max Y₁ 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), fun y hy => ?_⟩
  obtain ⟨h1, h2⟩ := hY₁ y ((le_max_left _ _).trans hy)
  have hy0 : 0 < y := by linarith
  have hly : 0 < Real.log y := Real.log_pos h2
  have hscale : 0 < y / Real.log y := div_pos hy0 hly
  rw [Artin.upCount_dyadic Nat.Prime hy0.le] at h1
  have h3 := (lt_div_iff₀ hscale).mp h1
  have hrw : y / (2 * Real.log y) = 1 / 2 * (y / Real.log y) := by
    field_simp
  rw [hrw]
  linarith

/-- **Mertens-type lower bound.** For `0 < α < β`, eventually
`C_x = ∑_{x^α < Q ≤ x^β} 1/Q ≥ (β - α) / (8 β log 2)`. -/
theorem eventually_longPrimeMass_ge {α β : ℝ} (hα : 0 < α) (hαβ : α < β) :
    ∀ᶠ x : ℝ in atTop, (β - α) / (8 * β * Real.log 2) ≤ longPrimeMass α β x := by
  obtain ⟨Y₀, hY₀, hdy⟩ := exists_dyadicPrimes_ge
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hβ : 0 < β := hα.trans hαβ
  have hxα : Tendsto (fun x : ℝ => x ^ α) atTop atTop := tendsto_rpow_atTop hα
  filter_upwards [hxα.eventually (eventually_ge_atTop Y₀), eventually_gt_atTop (1 : ℝ),
    eventually_ge_atTop (Real.exp (2 * Real.log 2 / (β - α)))] with x hxY hx1 hxe
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx1
  set K := ⌊(β - α) * Real.log x / Real.log 2⌋₊ with hK
  set y : ℕ → ℝ := fun k => x ^ α * 2 ^ k with hy
  set B : ℕ → Finset ℕ := fun k =>
    (Finset.range (⌊2 * y k⌋₊ + 1)).filter fun Q : ℕ => Q.Prime ∧ y k < (Q : ℝ) with hB
  have hxαpos : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
  have hy_ge : ∀ k, x ^ α ≤ y k := fun k =>
    le_mul_of_one_le_right hxαpos.le (one_le_pow₀ (by norm_num))
  have h2K : (2 : ℝ) ^ K ≤ x ^ (β - α) := by
    have hKle : (K : ℝ) ≤ (β - α) * Real.log x / Real.log 2 := Nat.floor_le (by positivity)
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.rpow_def_of_pos hx0]
    apply Real.exp_le_exp.mpr
    calc Real.log 2 * K ≤ Real.log 2 * ((β - α) * Real.log x / Real.log 2) := by gcongr
      _ = Real.log x * (β - α) := by field_simp
  have hy_le : ∀ k < K, 2 * y k ≤ x ^ β := by
    intro k hk
    have hk1 : (2 : ℝ) ^ (k + 1) ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hk
    calc 2 * y k = x ^ α * 2 ^ (k + 1) := by simp only [hy]; ring
      _ ≤ x ^ α * x ^ (β - α) := by gcongr; exact hk1.trans h2K
      _ = x ^ β := by rw [← Real.rpow_add hx0]; ring_nf
  have hmemB : ∀ k Q, Q ∈ B k → Q.Prime ∧ y k < (Q : ℝ) ∧ (Q : ℝ) ≤ 2 * y k := by
    intro k Q hQ
    obtain ⟨hr, hp, hlt⟩ := Finset.mem_filter.mp hQ
    have hQle : Q ≤ ⌊2 * y k⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have hy0 : 0 ≤ 2 * y k := by have := hy_ge k; linarith
    exact ⟨hp, hlt, (Nat.cast_le.mpr hQle).trans (Nat.floor_le hy0)⟩
  -- each block contributes at least `1 / (4 β log x)`
  have hblock : ∀ k < K, 1 / (4 * β * Real.log x) ≤ ∑ Q ∈ B k, (1 : ℝ) / Q := by
    intro k hk
    have hyY : Y₀ ≤ y k := hxY.trans (hy_ge k)
    have hy1 : 1 < y k := lt_of_lt_of_le hY₀ hyY
    have hcard := hdy (y k) hyY
    have hrecip : ∀ Q ∈ B k, (1 : ℝ) / (2 * y k) ≤ 1 / Q := by
      intro Q hQ
      obtain ⟨_, hlt, hle⟩ := hmemB k Q hQ
      have hQpos : (0 : ℝ) < Q := by linarith
      exact one_div_le_one_div_of_le hQpos hle
    have hsum : ((B k).card : ℝ) * (1 / (2 * y k)) ≤ ∑ Q ∈ B k, (1 : ℝ) / Q := by
      have := Finset.sum_le_sum hrecip
      rwa [Finset.sum_const, nsmul_eq_mul] at this
    have hlogy : Real.log (y k) ≤ β * Real.log x := by
      have hyk : y k ≤ x ^ β := by have := hy_le k hk; linarith
      calc Real.log (y k) ≤ Real.log (x ^ β) := Real.log_le_log (by linarith) hyk
        _ = β * Real.log x := Real.log_rpow hx0 β
    have hlogy0 : 0 < Real.log (y k) := Real.log_pos hy1
    have hy0 : 0 < y k := by linarith
    calc 1 / (4 * β * Real.log x) ≤ 1 / (4 * Real.log (y k)) := by
          apply one_div_le_one_div_of_le (by positivity)
          linarith
      _ = y k / (2 * Real.log (y k)) * (1 / (2 * y k)) := by field_simp; ring
      _ ≤ ((B k).card : ℝ) * (1 / (2 * y k)) := by gcongr
      _ ≤ _ := hsum
  -- the blocks are disjoint and lie in `(x^α, x^β]`
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range K) : Set ℕ) B := by
    intro k _ k' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro Q hQ hQ'
    obtain ⟨_, h1, h2⟩ := hmemB k Q hQ
    obtain ⟨_, h1', h2'⟩ := hmemB k' Q hQ'
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ k' := pow_le_pow_right₀ (by norm_num) hlt
      have : 2 * y k ≤ y k' := by
        simp only [hy]
        calc 2 * (x ^ α * 2 ^ k) = x ^ α * 2 ^ (k + 1) := by ring
          _ ≤ x ^ α * 2 ^ k' := by gcongr
      linarith
    · have : (2 : ℝ) ^ (k' + 1) ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hlt
      have : 2 * y k' ≤ y k := by
        simp only [hy]
        calc 2 * (x ^ α * 2 ^ k') = x ^ α * 2 ^ (k' + 1) := by ring
          _ ≤ x ^ α * 2 ^ k := by gcongr
      linarith
  have hsubset : (Finset.range K).biUnion B ⊆
      (Finset.range (⌊x ^ β⌋₊ + 1)).filter (fun Q : ℕ => Q.Prime ∧ x ^ α < (Q : ℝ)) := by
    intro Q hQ
    obtain ⟨k, hk, hQk⟩ := Finset.mem_biUnion.mp hQ
    obtain ⟨hp, h1, h2⟩ := hmemB k Q hQk
    have hk' := Finset.mem_range.mp hk
    refine Finset.mem_filter.mpr ⟨?_, hp, lt_of_le_of_lt (hy_ge k) h1⟩
    have hQβ : (Q : ℝ) ≤ x ^ β := h2.trans (hy_le k hk')
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_floor hQβ))
  have hmass : ∑ k ∈ Finset.range K, ∑ Q ∈ B k, (1 : ℝ) / Q ≤ longPrimeMass α β x := by
    rw [← Finset.sum_biUnion hdisj]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun Q _ _ => by positivity)
  have hKsum : (K : ℝ) * (1 / (4 * β * Real.log x)) ≤
      ∑ k ∈ Finset.range K, ∑ Q ∈ B k, (1 : ℝ) / Q := by
    have := Finset.sum_le_sum fun k (hk : k ∈ Finset.range K) =>
      hblock k (Finset.mem_range.mp hk)
    rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
  have hKge : (β - α) * Real.log x / Real.log 2 - 1 ≤ (K : ℝ) :=
    (Nat.sub_one_lt_floor _).le
  have hlog_large : 2 * Real.log 2 / (β - α) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos _) hxe
    rwa [Real.log_exp] at this
  have hhalf : 1 ≤ (β - α) * Real.log x / (2 * Real.log 2) := by
    rw [le_div_iff₀ (by positivity)]
    rw [div_le_iff₀ (by linarith)] at hlog_large
    linarith
  have hK2 : (β - α) * Real.log x / (2 * Real.log 2) ≤ (K : ℝ) := by
    have : (β - α) * Real.log x / Real.log 2 =
        2 * ((β - α) * Real.log x / (2 * Real.log 2)) := by field_simp
    linarith
  have hfinal : (β - α) / (8 * β * Real.log 2) ≤ (K : ℝ) * (1 / (4 * β * Real.log x)) := by
    have hpos : 0 < 4 * β * Real.log x := by positivity
    rw [mul_one_div, le_div_iff₀ hpos]
    calc (β - α) / (8 * β * Real.log 2) * (4 * β * Real.log x)
        = (β - α) * Real.log x / (2 * Real.log 2) := by field_simp; ring
      _ ≤ K := hK2
  linarith

/-! ### `f_x(p - 1) ∈ {0, 1}` and the factorization `p - 1 = Q r` -/

/-- Below `x^(2α)`, at most one prime factor exceeds `x^α`. -/
theorem longPrimeCount_le_one {α β x : ℝ} (hx : 0 < x) {n : ℕ}
    (hn : (n : ℝ) < x ^ (2 * α)) : longPrimeCount α β x n ≤ 1 := by
  unfold longPrimeCount
  apply Finset.card_le_one.mpr
  intro Q hQ Q' hQ'
  by_contra hne
  obtain ⟨hQf, hQlo, _⟩ := Finset.mem_filter.mp hQ
  obtain ⟨hQ'f, hQ'lo, _⟩ := Finset.mem_filter.mp hQ'
  obtain ⟨hQp, hQn, hn0⟩ := Nat.mem_primeFactors.mp hQf
  obtain ⟨hQ'p, hQ'n, _⟩ := Nat.mem_primeFactors.mp hQ'f
  have hdvd : Q * Q' ∣ n :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd ((Nat.coprime_primes hQp hQ'p).mpr hne) hQn hQ'n
  have hle : Q * Q' ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hdvd
  have hxα : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hprod : x ^ (2 * α) < (Q : ℝ) * Q' := by
    rw [show 2 * α = α + α by ring, Real.rpow_add hx]
    exact mul_lt_mul'' hQlo hQ'lo hxα.le hxα.le
  have hcast : ((Q * Q' : ℕ) : ℝ) ≤ n := by exact_mod_cast hle
  push_cast at hcast
  linarith

/-- A prime factor `Q > x^(1-η)` of `n ≤ 2x` leaves a cofactor `r ≤ 2 x^η`. -/
theorem exists_factor_of_longPrimeCount_pos {η β x : ℝ} (hx : 0 < x) {n : ℕ}
    (hn : (n : ℝ) ≤ 2 * x) (h : 0 < longPrimeCount (1 - η) β x n) :
    ∃ Q r : ℕ, Q.Prime ∧ n = Q * r ∧ r ≤ ⌊2 * x ^ η⌋₊ := by
  unfold longPrimeCount at h
  obtain ⟨Q, hQ⟩ := Finset.card_pos.mp h
  obtain ⟨hQf, hQlo, _⟩ := Finset.mem_filter.mp hQ
  obtain ⟨hQp, hQn, _⟩ := Nat.mem_primeFactors.mp hQf
  refine ⟨Q, n / Q, hQp, (Nat.mul_div_cancel' hQn).symm, ?_⟩
  apply Nat.le_floor
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQp.pos
  have h1 : ((n / Q : ℕ) : ℝ) * Q = n := by exact_mod_cast Nat.div_mul_cancel hQn
  have hxη : x ^ η * x ^ (1 - η) = x := by
    rw [← Real.rpow_add hx]; simp
  have hxη0 : 0 ≤ x ^ η := (Real.rpow_pos_of_pos hx η).le
  have hmul : ((n / Q : ℕ) : ℝ) * Q ≤ 2 * x ^ η * Q := by
    rw [h1]
    calc (n : ℝ) ≤ 2 * x := hn
      _ = 2 * x ^ η * x ^ (1 - η) := by rw [mul_assoc, hxη]
      _ ≤ 2 * x ^ η * Q := by gcongr
  exact le_of_mul_le_mul_right hmul hQpos

/-! ### The supply bound -/

theorem factorCandidates_card_ge_sum {η : ℝ} {H : ℕ} {R : Finset ℕ} (hR : ∀ u ∈ R, u < H)
    (x : ℝ) :
    ∑ u ∈ R, (factorCandidates η H {u} x).card ≤ (factorCandidates η H R x).card := by
  classical
  have hdisj : Set.PairwiseDisjoint (↑R : Set ℕ) fun u => factorCandidates η H {u} x := by
    intro u hu u' hu' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro p hp hp'
    obtain ⟨_, _, _, _, ⟨v, hv, hpv⟩, _⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, _, _, _, ⟨v', hv', hpv'⟩, _⟩ := Finset.mem_filter.mp hp'
    rw [Finset.mem_singleton] at hv hv'
    rw [hv] at hpv
    rw [hv'] at hpv'
    apply hne
    have huu : u ≡ u' [MOD H] := hpv.symm.trans hpv'
    unfold Nat.ModEq at huu
    rwa [Nat.mod_eq_of_lt (hR u hu), Nat.mod_eq_of_lt (hR u' hu')] at huu
  rw [← Finset.card_biUnion hdisj]
  apply Finset.card_le_card
  intro p hp
  obtain ⟨u, hu, hpu⟩ := Finset.mem_biUnion.mp hp
  obtain ⟨hr, hpp, hx1, hx2, ⟨v, hv, hpv⟩, hfac⟩ := Finset.mem_filter.mp hpu
  rw [Finset.mem_singleton] at hv
  rw [hv] at hpv
  exact Finset.mem_filter.mpr ⟨hr, hpp, hx1, hx2, ⟨u, hu, hpv⟩, hfac⟩

/-- **Candidate supply from the fixed-class long-prime statistic** (the public paper's
`cor:supply`, in the form of the Lean reduction). With `α = 1 - η > 1/2` and `α < β < 1`,
`prop:ap` gives `CandidateSupplyBound A η θ` for every `A`, with `θ` independent of `A`. -/
theorem candidateSupplyBound_of_fixedClassLongPrimeStatistic {η β : ℝ}
    (hη2 : η < 1 / 2) (hβ : 1 - η < β) (hβ1 : β < 1)
    (h : FixedClassLongPrimeStatistic (1 - η) β) :
    ∃ θ : ℝ, 0 < θ ∧ ∀ A : Finset ℕ, CandidateSupplyBound A η θ := by
  set α := 1 - η with hαdef
  have hα0 : 0 < α := by linarith
  have hαβ : α < β := hβ
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hβ0 : 0 < β := hα0.trans hαβ
  set c₁ : ℝ := (β - α) / (8 * β * Real.log 2) with hc₁
  have hc₁pos : 0 < c₁ := div_pos (by linarith) (by positivity)
  refine ⟨c₁ / 32, by positivity, ?_⟩
  intro A Y H R hH hR _hprog
  -- the bump `Φ`: `1` on `[11/8, 13/8]`, supported in `(5/4, 7/4)`
  let Φ : ContDiffBump (3 / 2 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  have hrIn : Φ.rIn = 1 / 8 := rfl
  have hrOut : Φ.rOut = 1 / 4 := rfl
  have hΦ1 : ∀ t : ℝ, 11 / 8 ≤ t → t ≤ 13 / 8 → Φ t = 1 := by
    intro t h1 h2
    apply Φ.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le, hrIn]
    constructor <;> linarith
  have hΦsupp : ∀ t : ℝ, Φ t ≠ 0 → 5 / 4 < t ∧ t < 7 / 4 := by
    intro t ht
    have hmem : t ∈ Function.support (Φ : ℝ → ℝ) := ht
    rw [Φ.support_eq, Metric.mem_ball, Real.dist_eq, abs_lt, hrOut] at hmem
    constructor <;> linarith [hmem.1, hmem.2]
  have hΦle : ∀ t : ℝ, Φ t ≤ 1 := fun t => Φ.le_one
  have hΦnn : ∀ t : ℝ, 0 ≤ Φ t := fun t => Φ.nonneg
  have hΦstat : ∀ u ∈ R,
      fixedClassLongPrimeSum α β H u Φ =o[atTop] fun x : ℝ => x / Real.log x := by
    intro u hu
    refine h H u hH (hR u hu).2 Φ Φ.contDiff Φ.hasCompactSupport ?_ hΦnn
    rw [Φ.tsupport_eq]
    intro t ht
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le, hrOut] at ht
    rw [Set.mem_Ioi]
    linarith [ht.1]
  have hphi : (0 : ℝ) < Nat.totient H := by exact_mod_cast Nat.totient_pos.mpr hH
  set ε : ℝ := c₁ / (32 * Nat.totient H) with hε
  have hεpos : 0 < ε := by positivity
  -- `2x < x^(2α)` eventually
  have hpow : ∀ᶠ x : ℝ in atTop, 2 * x < x ^ (2 * α) := by
    have ht : Tendsto (fun x : ℝ => x ^ (2 * α - 1)) atTop atTop :=
      tendsto_rpow_atTop (by linarith)
    filter_upwards [ht.eventually (eventually_gt_atTop (2 : ℝ)), eventually_gt_atTop (0 : ℝ)]
      with x hx hx0
    have : x ^ (2 * α) = x * x ^ (2 * α - 1) := by
      rw [← Real.rpow_one_add' hx0.le (by linarith)]
      ring_nf
    rw [this]
    nlinarith
  -- one class at a time
  have hclass : ∀ u ∈ R, ∀ᶠ x : ℝ in atTop,
      c₁ / 32 * (1 / (Nat.totient H : ℝ)) * (x / Real.log x) ≤
        ((factorCandidates η H {u} x).card : ℝ) := by
    intro u hu
    have hsmall := (hΦstat u hu).bound hεpos
    have hcount := eventually_residuePrimesBetween_ge (n := H) (u := u) hH (hR u hu).2
      (a := 23 / 16) (b := 25 / 16) (θ := 1 / 2) (by norm_num) (by norm_num) (by norm_num)
    have hmass := eventually_longPrimeMass_ge hα0 hαβ
    filter_upwards [hsmall, hcount, hmass, hpow, eventually_ge_atTop (16 : ℝ)]
      with x hxS hxc hxm hxp hx16
    have hx0 : 0 < x := by linarith
    have hx1 : 1 < x := by linarith
    have hscale : 0 < x / Real.log x := div_pos hx0 (Real.log_pos hx1)
    set T := (Finset.range (⌊2 * x⌋₊ + 1)).filter fun p => p.Prime ∧ p ≡ u [MOD H] with hT
    set Cx := longPrimeMass α β x with hCx
    set f : ℕ → ℝ := fun p => (longPrimeCount α β x (p - 1) : ℝ) with hf
    set w : ℕ → ℝ := fun p => Φ (((p : ℝ) - 1) / x) with hw
    -- support facts
    have hsuppx : ∀ p : ℕ, w p ≠ 0 → x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧ (p : ℝ) - 1 < 2 * x := by
      intro p hp
      obtain ⟨h1, h2⟩ := hΦsupp _ hp
      rw [lt_div_iff₀ hx0] at h1
      rw [div_lt_iff₀ hx0] at h2
      refine ⟨by linarith, by linarith, by linarith⟩
    -- the finsum is a finite sum over `T`
    have hsum_eq : fixedClassLongPrimeSum α β H u Φ x = ∑ p ∈ T, w p * (f p - Cx) := by
      unfold fixedClassLongPrimeSum
      rw [finsum_eq_sum_of_support_subset _ (s := T)]
      · apply Finset.sum_congr rfl
        intro p hp
        obtain ⟨_, hpp, hpu⟩ := Finset.mem_filter.mp hp
        rw [if_pos ⟨hpp, hpu⟩]
      · intro p hp
        rw [Function.mem_support] at hp
        by_cases hpc : p.Prime ∧ p ≡ u [MOD H]
        · rw [if_pos hpc] at hp
          have hwp : w p ≠ 0 := fun h0 => hp (by simp only [hw] at h0; rw [h0, zero_mul])
          obtain ⟨_, hp2, _⟩ := hsuppx p hwp
          refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨?_, hpc⟩)
          exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_floor hp2))
        · rw [if_neg hpc] at hp
          exact absurd rfl hp
    -- `∑ w f = C_x ∑ w + S`
    have hsplit : ∑ p ∈ T, w p * f p = Cx * ∑ p ∈ T, w p +
        fixedClassLongPrimeSum α β H u Φ x := by
      rw [hsum_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p _
      ring
    -- `∑ w ≥ #{p ∈ (23x/16, 25x/16], p ≡ u}`
    have hwsum : ((residuePrimesBetween H u (23 / 16 * x) (25 / 16 * x)).card : ℝ) ≤
        ∑ p ∈ T, w p := by
      have hsubT : residuePrimesBetween H u (23 / 16 * x) (25 / 16 * x) ⊆ T := by
        intro p hp
        obtain ⟨hr, hpp, _, hpu⟩ := Finset.mem_filter.mp hp
        refine Finset.mem_filter.mpr ⟨?_, hpp, hpu⟩
        have hle : p ≤ ⌊25 / 16 * x⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
        have hfl : ⌊25 / 16 * x⌋₊ ≤ ⌊2 * x⌋₊ := Nat.floor_le_floor (by linarith)
        exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (hle.trans hfl))
      calc ((residuePrimesBetween H u (23 / 16 * x) (25 / 16 * x)).card : ℝ)
          = ∑ p ∈ residuePrimesBetween H u (23 / 16 * x) (25 / 16 * x), w p := by
            rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
            apply Finset.sum_congr rfl
            intro p hp
            obtain ⟨hr, _, hlo, _⟩ := Finset.mem_filter.mp hp
            have hle : p ≤ ⌊25 / 16 * x⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
            have hhi : (p : ℝ) ≤ 25 / 16 * x :=
              (Nat.cast_le.mpr hle).trans (Nat.floor_le (by linarith))
            symm
            apply hΦ1
            · rw [le_div_iff₀ hx0]; nlinarith
            · rw [div_le_iff₀ hx0]; nlinarith
        _ ≤ ∑ p ∈ T, w p :=
            Finset.sum_le_sum_of_subset_of_nonneg hsubT (fun p _ _ => hΦnn _)
    -- `∑ w f ≤ #candidates`
    have hwf : ∑ p ∈ T, w p * f p ≤ ((factorCandidates η H {u} x).card : ℝ) := by
      set G := T.filter fun p => w p ≠ 0 ∧ 0 < longPrimeCount α β x (p - 1)
      have hterm : ∀ p ∈ T, w p * f p ≤ if p ∈ G then 1 else 0 := by
        intro p hp
        by_cases hG : p ∈ G
        · rw [if_pos hG]
          obtain ⟨_, hwp, _⟩ := Finset.mem_filter.mp hG
          obtain ⟨_, _, hlt⟩ := hsuppx p hwp
          have hf1 : f p ≤ 1 := by
            have hpos : 1 ≤ p := by
              obtain ⟨_, hpp, _⟩ := Finset.mem_filter.mp hp
              exact hpp.one_lt.le
            have hcast : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
              rw [Nat.cast_sub hpos, Nat.cast_one]
            have hle := longPrimeCount_le_one (α := α) (β := β) hx0 (n := p - 1)
              (by rw [hcast]; linarith)
            simp only [hf]
            exact_mod_cast hle
          have hf0 : 0 ≤ f p := Nat.cast_nonneg _
          calc w p * f p ≤ 1 * 1 := mul_le_mul (hΦle _) hf1 hf0 zero_le_one
            _ = 1 := by ring
        · rw [if_neg hG]
          by_cases hwp : w p = 0
          · rw [hwp, zero_mul]
          · have hf0 : longPrimeCount α β x (p - 1) = 0 := by
              by_contra hne
              exact hG (Finset.mem_filter.mpr ⟨hp, hwp, Nat.pos_of_ne_zero hne⟩)
            simp only [hf, hf0, Nat.cast_zero, mul_zero, le_refl]
      have hGsub : G ⊆ factorCandidates η H {u} x := by
        intro p hp
        obtain ⟨hpT, hwp, hfpos⟩ := Finset.mem_filter.mp hp
        obtain ⟨hr, hpp, hpu⟩ := Finset.mem_filter.mp hpT
        obtain ⟨hxp, hp2x, _⟩ := hsuppx p hwp
        have hpos : 1 ≤ p := hpp.one_lt.le
        have hn : ((p - 1 : ℕ) : ℝ) ≤ 2 * x := by
          rw [Nat.cast_sub hpos, Nat.cast_one]; linarith
        obtain ⟨Q, r, hQ, hfac, hrle⟩ :=
          exists_factor_of_longPrimeCount_pos (η := η) (β := β) hx0 hn hfpos
        classical
        exact Finset.mem_filter.mpr ⟨hr, hpp, hxp, hp2x, ⟨u, Finset.mem_singleton_self u, hpu⟩,
          Q, r, hQ, hfac, hrle⟩
      calc ∑ p ∈ T, w p * f p ≤ ∑ p ∈ T, (if p ∈ G then (1 : ℝ) else 0) :=
            Finset.sum_le_sum hterm
        _ = (G.card : ℝ) := by
            rw [← Finset.sum_filter]
            have hGT : T.filter (fun p => p ∈ G) = G := by
              ext p
              simp only [Finset.mem_filter]
              constructor
              · exact fun h => h.2
              · intro hp
                exact ⟨(Finset.mem_filter.mp hp).1, hp⟩
            rw [hGT, Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ ((factorCandidates η H {u} x).card : ℝ) := by
            exact_mod_cast Finset.card_le_card hGsub
    -- combine
    have hS : |fixedClassLongPrimeSum α β H u Φ x| ≤ ε * (x / Real.log x) := by
      have := hxS
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hscale] at this
      exact this
    have hcnt : 1 / 2 * ((25 / 16 - 23 / 16) / (Nat.totient H : ℝ)) * (x / Real.log x) ≤
        ((residuePrimesBetween H u (23 / 16 * x) (25 / 16 * x)).card : ℝ) := hxc
    have hwsum0 : 0 ≤ ∑ p ∈ T, w p := Finset.sum_nonneg fun p _ => hΦnn _
    have hmain : c₁ * ((1 / 16) / (Nat.totient H : ℝ) * (x / Real.log x)) ≤ Cx * ∑ p ∈ T, w p := by
      have h1 : (1 / 16) / (Nat.totient H : ℝ) * (x / Real.log x) ≤ ∑ p ∈ T, w p := by
        have : 1 / 2 * ((25 / 16 - 23 / 16) / (Nat.totient H : ℝ)) * (x / Real.log x) =
            (1 / 16) / (Nat.totient H : ℝ) * (x / Real.log x) := by ring
        linarith
      calc c₁ * ((1 / 16) / (Nat.totient H : ℝ) * (x / Real.log x))
          ≤ Cx * ((1 / 16) / (Nat.totient H : ℝ) * (x / Real.log x)) :=
            mul_le_mul_of_nonneg_right hxm (by positivity)
        _ ≤ Cx * ∑ p ∈ T, w p := mul_le_mul_of_nonneg_left h1 (hc₁pos.le.trans hxm)
    have hSlow := neg_abs_le (fixedClassLongPrimeSum α β H u Φ x)
    have hεeq : ε * (x / Real.log x) = c₁ / 32 * (1 / (Nat.totient H : ℝ)) * (x / Real.log x) := by
      rw [hε]; field_simp
    have hc16 : c₁ * ((1 / 16) / (Nat.totient H : ℝ) * (x / Real.log x)) =
        2 * (c₁ / 32 * (1 / (Nat.totient H : ℝ)) * (x / Real.log x)) := by
      field_simp; ring
    linarith
  -- sum over the classes
  filter_upwards [(Filter.eventually_all_finset R).mpr hclass] with x hx
  have hsum := Finset.sum_le_sum hx
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  have hcard := factorCandidates_card_ge_sum (η := η) (fun u hu => (hR u hu).1) x
  have hcard' : (∑ u ∈ R, ((factorCandidates η H {u} x).card : ℝ)) ≤
      ((factorCandidates η H R x).card : ℝ) := by exact_mod_cast hcard
  calc c₁ / 32 * ((R.card : ℝ) / Nat.totient H) * (x / Real.log x)
      = (R.card : ℝ) * (c₁ / 32 * (1 / (Nat.totient H : ℝ)) * (x / Real.log x)) := by ring
    _ ≤ ∑ u ∈ R, ((factorCandidates η H {u} x).card : ℝ) := hsum
    _ ≤ _ := hcard'

end

end SimultaneousPrimitiveRoots.Unconditional
