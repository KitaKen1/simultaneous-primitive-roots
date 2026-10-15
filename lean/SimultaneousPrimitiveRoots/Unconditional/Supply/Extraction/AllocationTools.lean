module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.CandidateAdmissibleProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.AllocationIdentityProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.WeightBound
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.GroupSanity
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Sanity
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.EndpointSquaresProof

/-!
# Tools for the allocation step

Elementary lemmas used in the proof of `AllocationLink d H b q q₀` (`[P-07:0518–0615]`,
`Extraction/AllocationProof.lean`). Nothing here is specific to the candidate groups except the
count of the groups.

* `Allocation.abs_shiftSum_sub_le`: two shifted sums whose terms agree off an exceptional set
  differ by at most the sum of a majorant over the exceptional set. This is how the square
  exceptions are "removed and restored" (`[P-07:0542–0557, 0596–0597]`) in one step.
* `Allocation.mulCutoff Φ`: the cutoff `Ψ(y) = y Φ(y)` of `[P-07:0604]`, and
  `Allocation.twoSidedSum_mulCutoff`: "since `Φ(u/x) = x Ψ(u/x)/u`", the sum of Theorem 6.1^{𝔅}
  with the class weight `𝓑_{H,b}`, the cutoff `Ψ` and a real second endpoint `G` is `1/x` times
  the shifted sum (ext:correlation-to-use) with the class `u + 1 ≡ b (mod H)`.
* `Allocation.abs_allocationCore_le`, `Allocation.abs_convPow_le`: a bound
  `L^C τ(v_*)^C` for the allocation core gives `L^{max(C,0)} τ(v)^{⌈C⌉₊}`; with no active prime the
  core is the convolution power `ã^{*j}(v)` of the stripped coefficient.
* `Allocation.prod_markFactor_le`, `Allocation.prod_markFactor_div_le`: "all active marked factors
  are bounded by fixed log powers" (`[P-07:0554–0556]`): each group factor is at most
  `1/((1-q₀) v₋)`.
* `Allocation.pow_le_rpow_log`, `Allocation.candidateGroups_numGroups_le`: a fixed base to the
  number of candidate groups is a fixed power of `L` (`[P-07:0531–0532]`).
* `Allocation.term_algebra`, `Allocation.final_arith`: the arithmetic of the fixed costs and of the
  choice of `A` (`[P-07:0610–0612]`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

open Filter
open scoped Topology ContDiff

noncomputable section

namespace Allocation

/-! ### Shifted sums that agree off an exceptional set -/

/-- If `g₁ = g₂` at the `u` with `¬E (u + 1)` and `|g₁ - g₂| ≤ Bd g'` at the `u` with
`E (u + 1)` (on the part of the support of the cutoff where `P` holds), then
`|∑_P Φ g₁ - ∑_P Φ g₂| ≤ Bd ∑_E Φ g'`. -/
theorem abs_shiftSum_sub_le {Φ : ℝ → ℝ} {R x : ℝ} (hR : ∀ t, R < t → Φ t = 0) (hx : 0 < x)
    (hΦ0 : ∀ t, 0 ≤ Φ t) {P E : ℕ → Prop} {g₁ g₂ g' : ℕ → ℝ} {Bd : ℝ} (hBd : 0 ≤ Bd)
    (hg' : ∀ u, 0 ≤ g' u)
    (hoff : ∀ u : ℕ, P (u + 1) → Φ ((u : ℝ) / x) ≠ 0 → ¬E (u + 1) → g₁ u = g₂ u)
    (hon : ∀ u : ℕ, P (u + 1) → Φ ((u : ℝ) / x) ≠ 0 → E (u + 1) →
      |g₁ u - g₂ u| ≤ Bd * g' u) :
    |shiftSum Φ x P g₁ - shiftSum Φ x P g₂| ≤ Bd * shiftSum Φ x E g' := by
  classical
  have key : ∀ u : ℕ, |(if P (u + 1) then Φ ((u : ℝ) / x) * (g₁ u - g₂ u) else 0)| ≤
      Bd * (if E (u + 1) then Φ ((u : ℝ) / x) * g' u else 0) := by
    intro u
    have hrhs : 0 ≤ Bd * (if E (u + 1) then Φ ((u : ℝ) / x) * g' u else 0) := by
      refine mul_nonneg hBd ?_
      split_ifs
      · exact mul_nonneg (hΦ0 _) (hg' u)
      · exact le_rfl
    by_cases hP : P (u + 1)
    · rw [if_pos hP]
      by_cases hΦu : Φ ((u : ℝ) / x) = 0
      · have h0 : Φ ((u : ℝ) / x) * (g₁ u - g₂ u) = 0 := by rw [hΦu, zero_mul]
        rw [h0, abs_zero]
        exact hrhs
      · by_cases hE : E (u + 1)
        · rw [if_pos hE, abs_mul, abs_of_nonneg (hΦ0 _)]
          calc Φ ((u : ℝ) / x) * |g₁ u - g₂ u| ≤ Φ ((u : ℝ) / x) * (Bd * g' u) :=
                mul_le_mul_of_nonneg_left (hon u hP hΦu hE) (hΦ0 _)
            _ = Bd * (Φ ((u : ℝ) / x) * g' u) := by ring
        · have h0 : Φ ((u : ℝ) / x) * (g₁ u - g₂ u) = 0 := by
            rw [hoff u hP hΦu hE, sub_self, mul_zero]
          rw [h0, abs_zero]
          exact hrhs
    · rw [if_neg hP, abs_zero]
      exact hrhs
  rw [← shiftSum_sub hR hx, shiftSum_eq_sum hR hx, shiftSum_eq_sum hR hx, Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u _ => key u)

/-! ### The cutoff `Ψ(y) = y Φ(y)` and the sum of Theorem 6.1 -/

/-- `Ψ(y) = y Φ(y)` (`[P-07:0604]`: "Take `Ψ(y) = y Φ(y)`"), as a complex-valued function. -/
def mulCutoff (Φ : ℝ → ℝ) (y : ℝ) : ℂ := ((y * Φ y : ℝ) : ℂ)

theorem mulCutoff_support_subset (Φ : ℝ → ℝ) :
    Function.support (mulCutoff Φ) ⊆ Function.support Φ := by
  intro y hy
  rw [Function.mem_support] at hy ⊢
  intro h0
  apply hy
  unfold mulCutoff
  rw [h0, mul_zero, Complex.ofReal_zero]

theorem mulCutoff_contDiff {Φ : ℝ → ℝ} (hΦ : IsCutoff Φ) : ContDiff ℝ ∞ (mulCutoff Φ) := by
  have h : ContDiff ℝ ∞ (fun y : ℝ => ((y * Φ y : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_id.mul hΦ.smooth)
  exact h

theorem mulCutoff_hasCompactSupport {Φ : ℝ → ℝ} (hΦ : IsCutoff Φ) :
    HasCompactSupport (mulCutoff Φ) :=
  hΦ.compact.mono (mulCutoff_support_subset Φ)

theorem mulCutoff_tsupport_subset {Φ : ℝ → ℝ} (hΦ : IsCutoff Φ) :
    tsupport (mulCutoff Φ) ⊆ Set.Ioi 0 :=
  fun _ hy => hΦ.support (closure_mono (mulCutoff_support_subset Φ) hy)

/-- `Ψ(w/x)/w = Φ(w/x)/x` (`[P-07:0605]`), also at `w = 0`, where both sides vanish. -/
theorem mulCutoff_div {Φ : ℝ → ℝ} (hΦ : IsCutoff Φ) {x : ℝ} (w : ℕ) :
    mulCutoff Φ ((w : ℝ) / x) / (w : ℂ) = ((x⁻¹ * Φ ((w : ℝ) / x) : ℝ) : ℂ) := by
  have hreal : (w : ℝ) / x * Φ ((w : ℝ) / x) / (w : ℝ) = x⁻¹ * Φ ((w : ℝ) / x) := by
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · have hΦ0 : Φ ((w : ℝ) / x) = 0 := by
        rw [h0, Nat.cast_zero, zero_div]
        exact hΦ.apply_zero
      rw [hΦ0, mul_zero, mul_zero, zero_div]
    · have hw : (w : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h0.ne'
      calc (w : ℝ) / x * Φ ((w : ℝ) / x) / (w : ℝ)
          = (w : ℝ) / (w : ℝ) * (x⁻¹ * Φ ((w : ℝ) / x)) := by ring
        _ = x⁻¹ * Φ ((w : ℝ) / x) := by rw [div_self hw, one_mul]
  have hcast : (((w : ℝ) / x * Φ ((w : ℝ) / x) / (w : ℝ) : ℝ) : ℂ) =
      mulCutoff Φ ((w : ℝ) / x) / (w : ℂ) := by
    unfold mulCutoff
    rw [Complex.ofReal_div, Complex.ofReal_natCast]
  rw [← hcast, hreal]

/-- **(ext:correlation-to-use)** (`[P-07:0596–0606]`): with `Ψ(y) = y Φ(y)`, the class weight
`𝓑_{H,b}` and a real second endpoint `G`, the sum of Theorem 6.1^{𝔅} is `1/x` times

`∑_{u ≥ 1, u+1 ≡ b (H)} Φ(u/x) F_x(u) G(u+1) W_{1,q₀}(u) W_{1,q₀}(u+1)`. -/
theorem twoSidedSum_mulCutoff {Φ : ℝ → ℝ} (hΦ : IsCutoff Φ) {R x : ℝ}
    (hR : ∀ t, R < t → Φ t = 0) (hx : 0 < x) (q q₀ : ℝ) {K : ℕ} (𝔞 : MarkingArray K)
    (𝔊 : ActiveGroups) {d : ℕ} (S : Fin d → Finset ℕ) {H b : ℕ} (hb : b.Coprime H)
    (G : ℕ → ℝ) :
    twoSidedSum q q₀ 𝔞 x 𝔊 S (classWeight H b) (mulCutoff Φ) (fun n => ((G n : ℝ) : ℂ)) =
      ((x⁻¹ * shiftSum Φ x (fun v => v ≡ b [MOD H])
        (fun u => centeredCore q 𝔞 x S u * G (u + 1) *
          (∏ g : 𝔊.Index, markFactor q₀ (𝔊.group g) u) *
            ∏ g : 𝔊.Index, markFactor q₀ (𝔊.group g) (u + 1)) : ℝ) : ℂ) := by
  rw [twoSidedSum_classWeight q q₀ 𝔞 x 𝔊 S hb, shiftSum_eq_sum hR hx, Finset.mul_sum,
    Complex.ofReal_sum]
  refine (finsum_eq_sum_of_support_subset _ fun w hw =>
    Finset.mem_coe.mpr (Finset.mem_range.mpr ?_)).trans (Finset.sum_congr rfl fun w _ => ?_)
  · by_contra hcon
    rw [not_lt] at hcon
    have h1 : R * x < (w : ℝ) :=
      lt_of_lt_of_le (Nat.lt_floor_add_one (R * x)) (by exact_mod_cast hcon)
    have h2 : R < (w : ℝ) / x := by rwa [lt_div_iff₀ hx]
    have h3 : mulCutoff Φ ((w : ℝ) / x) = 0 := by
      unfold mulCutoff
      rw [hR _ h2, mul_zero, Complex.ofReal_zero]
    apply Function.mem_support.mp hw
    simp only [h3, zero_div, zero_mul, ite_self]
  · by_cases hc : w + 1 ≡ b [MOD H]
    · rw [if_pos hc, if_pos hc, mulCutoff_div hΦ w, ActiveGroups.oneMark_eq,
        ActiveGroups.oneMark_eq]
      push_cast
      ring
    · rw [if_neg hc, if_neg hc, mul_zero, Complex.ofReal_zero]

/-! ### The growth of the allocation core and of the convolution power -/

/-- `|G_P(v)| ≤ L^C τ(v_*)^C` gives `|G_P(v)| ≤ L^{max(C,0)} τ(v)^{⌈C⌉₊}` for `v ≥ 1` and `L ≥ 1`:
`1 ≤ τ(v_*) ≤ τ(v)`. The exponent `C` may have any sign. -/
theorem abs_allocationCore_le {x γ C : ℝ} {j : ℕ} {candidates active : Finset ℕ}
    (hL : 1 ≤ Real.log x) {v : ℕ} (hv : 0 < v)
    (h : |allocationCore x γ j candidates active v| ≤
      Real.log x ^ C * ((freePart active v).divisors.card : ℝ) ^ C) :
    |allocationCore x γ j candidates active v| ≤
      Real.log x ^ max C 0 * (v.divisors.card : ℝ) ^ ⌈C⌉₊ := by
  have hL0 : 0 ≤ Real.log x := le_trans zero_le_one hL
  have h1 : (1 : ℝ) ≤ ((freePart active v).divisors.card : ℝ) :=
    Nat.one_le_cast.mpr (Finset.one_le_card.mpr
      ⟨1, Nat.one_mem_divisors.mpr (TwoSidedProof.freePart_pos active v).ne'⟩)
  have h2 : ((freePart active v).divisors.card : ℝ) ≤ (v.divisors.card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card
      (Nat.divisors_subset_of_dvd hv.ne' (TwoSidedProof.freePart_dvd active hv.ne')))
  have h3 : ((freePart active v).divisors.card : ℝ) ^ C ≤ (v.divisors.card : ℝ) ^ ⌈C⌉₊ :=
    calc ((freePart active v).divisors.card : ℝ) ^ C
        ≤ ((freePart active v).divisors.card : ℝ) ^ ((⌈C⌉₊ : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil C)
      _ = ((freePart active v).divisors.card : ℝ) ^ ⌈C⌉₊ := Real.rpow_natCast _ _
      _ ≤ (v.divisors.card : ℝ) ^ ⌈C⌉₊ :=
          pow_le_pow_left₀ (le_trans zero_le_one h1) h2 _
  have h4 : Real.log x ^ C ≤ Real.log x ^ max C 0 :=
    Real.rpow_le_rpow_of_exponent_le hL (le_max_left _ _)
  exact h.trans (mul_le_mul h4 h3 (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Real.rpow_nonneg hL0 _))

/-- With no active prime the allocation core is `ã^{*j}(v)`, so (ext:core-bound) bounds the number
of weighted factor tuples of `v`: `|ã^{*j}(v)| ≤ L^{max(C,0)} τ(v)^{⌈C⌉₊}` ("the number of ordered
factor tuples of `v` is at most `τ_j(v)`", `[P-07:0550–0551]`). -/
theorem abs_convPow_le {x γ C : ℝ} {j : ℕ} {candidates : Finset ℕ} (hL : 1 ≤ Real.log x)
    {v : ℕ} (hv : 0 < v)
    (h : |allocationCore x γ j candidates ∅ v| ≤
      Real.log x ^ C * ((freePart ∅ v).divisors.card : ℝ) ^ C) :
    |convPow j (strippedCoeff x γ candidates) v| ≤
      Real.log x ^ max C 0 * (v.divisors.card : ℝ) ^ ⌈C⌉₊ := by
  have h' := abs_allocationCore_le hL hv h
  rwa [allocationCore_eq_convPow, freePart_empty hv.ne'] at h'

/-! ### Products of group factors -/

/-- The index set of a system has `s_P` elements. -/
theorem card_index (𝔊 : ActiveGroups) : Fintype.card 𝔊.Index = 𝔊.numGroups := by
  unfold ActiveGroups.numGroups
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]

theorem prod_markFactor_nonneg (𝔊 : ActiveGroups) {q : ℝ} (hq : 0 ≤ q) (n : ℕ) :
    0 ≤ ∏ g : 𝔊.Index, markFactor q (𝔊.group g) n :=
  Finset.prod_nonneg fun g _ => markFactor_nonneg hq (𝔊.group g) n

/-- `W_{1,q}(n) ≤ (1/((1-q) v₋))^{s_P}` for an admissible system (`[P-06:0045–0053]`,
`[P-07:0554–0556]`). -/
theorem prod_markFactor_le {Pc : ActiveGroupConstants} {x : ℝ} {𝔊 : ActiveGroups}
    (h𝔊 : 𝔊.Admissible Pc x) {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (n : ℕ) :
    ∏ g : 𝔊.Index, markFactor q (𝔊.group g) n ≤ (1 / ((1 - q) * Pc.vlo)) ^ 𝔊.numGroups :=
  calc ∏ g : 𝔊.Index, markFactor q (𝔊.group g) n
      ≤ ∏ _g : 𝔊.Index, 1 / ((1 - q) * Pc.vlo) :=
        Finset.prod_le_prod (fun g _ => markFactor_nonneg hq0 (𝔊.group g) n)
          (fun g _ => markFactor_le_of_mass_ge hq0 hq1 Pc.vlo_pos (h𝔊.mass_ge g) n)
    _ = (1 / ((1 - q) * Pc.vlo)) ^ 𝔊.numGroups := by
        rw [Finset.prod_const, Finset.card_univ, card_index]

/-- The damping `q₀/j` of the product side is smaller than `q₀`. -/
theorem markFactor_div_le {q₀ : ℝ} (hq₀ : 0 ≤ q₀) {j : ℕ} (hj : 1 ≤ j) (T : Finset ℕ) (v : ℕ) :
    markFactor (q₀ / (j : ℝ)) T v ≤ markFactor q₀ T v := by
  rw [markFactor_div]
  exact div_le_self (markFactor_nonneg hq₀ T v) (one_le_pow₀ (Nat.one_le_cast.mpr hj))

/-- The product-side factor `∏_g (q₀/j)^{ω_g(v)-1} ω_g(v)/V_g` has the same bound. -/
theorem prod_markFactor_div_le {Pc : ActiveGroupConstants} {x : ℝ} {𝔊 : ActiveGroups}
    (h𝔊 : 𝔊.Admissible Pc x) {q₀ : ℝ} (hq₀ : 0 ≤ q₀) (hq₀1 : q₀ < 1) {j : ℕ} (hj : 1 ≤ j)
    (n : ℕ) :
    ∏ g : 𝔊.Index, markFactor (q₀ / (j : ℝ)) (𝔊.group g) n ≤
      (1 / ((1 - q₀) * Pc.vlo)) ^ 𝔊.numGroups :=
  (Finset.prod_le_prod
    (fun g _ => markFactor_nonneg (div_nonneg hq₀ (Nat.cast_nonneg j)) (𝔊.group g) n)
    (fun g _ => markFactor_div_le hq₀ hj (𝔊.group g) n)).trans (prod_markFactor_le h𝔊 hq₀ hq₀1 n)

/-! ### Fixed bases to the number of groups -/

theorem pow_le_pow_of_le {c a : ℝ} (hc : 0 ≤ c) (hca : c ≤ a) (ha : 1 ≤ a) {n N : ℕ}
    (hn : n ≤ N) : c ^ n ≤ a ^ N :=
  (pow_le_pow_left₀ hc hca n).trans (pow_le_pow_right₀ ha hn)

/-- `a^N ≤ L^{κ log a}` when `N ≤ κ log L` and `a ≥ 1`: "`3^{|𝒞|} = L^{O(1)}`"
(`[P-07:0531]`). -/
theorem pow_le_rpow_log {a κ L : ℝ} (ha : 1 ≤ a) (hL : 0 < L) {N : ℕ}
    (hN : (N : ℝ) ≤ κ * Real.log L) : a ^ N ≤ L ^ (κ * Real.log a) := by
  have ha0 : 0 < a := lt_of_lt_of_le one_pos ha
  have e : Real.log a * (κ * Real.log L) = Real.log L * (κ * Real.log a) := by ring
  calc a ^ N = a ^ (N : ℝ) := (Real.rpow_natCast a N).symm
    _ ≤ a ^ (κ * Real.log L) := Real.rpow_le_rpow_of_exponent_le ha hN
    _ = Real.exp (Real.log a * (κ * Real.log L)) := Real.rpow_def_of_pos ha0 _
    _ = Real.exp (Real.log L * (κ * Real.log a)) := by rw [e]
    _ = L ^ (κ * Real.log a) := (Real.rpow_def_of_pos hL _).symm

/-- There are at most `(2/log 2) log L` candidate groups (`[P-07:0324–0325]`). -/
theorem candidateGroups_numGroups_le {x : ℝ} (hL : 1 ≤ Real.log x) :
    ((candidateGroups x).numGroups : ℝ) ≤ 2 / Real.log 2 * Real.log (Real.log x) := by
  have h1 : (candidateCount 0.28 0.35 x : ℝ) ≤ 1 / Real.log 2 * Real.log (Real.log x) :=
    candidateCount_le (by norm_num) (by norm_num) hL
  have h2 : (candidateCount 0.4 0.45 x : ℝ) ≤ 1 / Real.log 2 * Real.log (Real.log x) :=
    candidateCount_le (by norm_num) (by norm_num) hL
  have e : (2 : ℝ) / Real.log 2 * Real.log (Real.log x) =
      1 / Real.log 2 * Real.log (Real.log x) + 1 / Real.log 2 * Real.log (Real.log x) := by ring
  have hN : ((candidateGroups x).numGroups : ℝ) =
      (candidateCount 0.28 0.35 x : ℝ) + (candidateCount 0.4 0.45 x : ℝ) := by
    show ((candidateCount 0.28 0.35 x + candidateCount 0.4 0.45 x : ℕ) : ℝ) = _
    exact Nat.cast_add _ _
  rw [hN, e]
  exact add_le_add h1 h2

/-! ### The arithmetic of the fixed costs -/

/-- The fixed costs of one expanded term (`[P-07:0610–0612]`): if the three powers `c₁^n`, `j^n`,
`D^n` are at most `T ≥ 1`, then
`c₁^n (j^n X + B D^n D^n (1 + j^n) Y) ≤ T⁴ (X + 2 B Y)`. -/
theorem term_algebra {cn jn Dn T X Y B : ℝ} (hcn : cn ≤ T) (hjn0 : 0 ≤ jn)
    (hjn : jn ≤ T) (hDn0 : 0 ≤ Dn) (hDn : Dn ≤ T) (hT : 1 ≤ T) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hB : 0 ≤ B) :
    cn * (jn * X + B * Dn * Dn * (1 + jn) * Y) ≤ T ^ 4 * (X + 2 * B * Y) := by
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hT3 : T ≤ T ^ 3 := le_self_pow₀ hT (by norm_num)
  have h1j : 0 ≤ 1 + jn := by linarith
  have h1 : jn * X ≤ T ^ 3 * X := mul_le_mul_of_nonneg_right (hjn.trans hT3) hX
  have h2 : B * Dn * Dn * (1 + jn) * Y ≤ T ^ 3 * (2 * B * Y) := by
    have hDD : Dn * Dn ≤ T * T := mul_le_mul hDn hDn hDn0 hT0
    have hj1 : 1 + jn ≤ 2 * T := by linarith
    calc B * Dn * Dn * (1 + jn) * Y = B * (Dn * Dn) * (1 + jn) * Y := by ring
      _ ≤ B * (T * T) * (2 * T) * Y :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul (mul_le_mul_of_nonneg_left hDD hB) hj1 h1j
              (mul_nonneg hB (mul_nonneg hT0 hT0))) hY
      _ = T ^ 3 * (2 * B * Y) := by ring
  have hinner : jn * X + B * Dn * Dn * (1 + jn) * Y ≤ T ^ 3 * (X + 2 * B * Y) := by
    have e : T ^ 3 * (X + 2 * B * Y) = T ^ 3 * X + T ^ 3 * (2 * B * Y) := by ring
    rw [e]
    exact add_le_add h1 h2
  have hin0 : 0 ≤ jn * X + B * Dn * Dn * (1 + jn) * Y :=
    add_nonneg (mul_nonneg hjn0 hX)
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hB hDn0) hDn0) h1j) hY)
  calc cn * (jn * X + B * Dn * Dn * (1 + jn) * Y) ≤ T * (T ^ 3 * (X + 2 * B * Y)) :=
        mul_le_mul hcn hinner hin0 hT0
    _ = T ^ 4 * (X + 2 * B * Y) := by ring

/-- The choice of `A` (`[P-07:0610–0612]`: "Choose `A` after the fixed costs … They are all
absorbed"): with `A = e₀ + C₊ + 2`, a total cost `T₁ T₂ ≤ L^{e₀}`, a main term `x M L^{-A}` and an
exceptional term `2 B L^{C₊} x L^{-A}`, the total is at most `x (M + 2B) L^{-2} ≤ η x/L` once
`L ≥ (M + 2B)/η`. -/
theorem final_arith {x L η M B Cp e₀ A T₁ T₂ : ℝ} (hx : 0 < x) (hL : 1 ≤ L) (hη : 0 < η)
    (hM : 0 ≤ M) (hB : 0 ≤ B) (hCp : 0 ≤ Cp) (hA : A = e₀ + Cp + 2) (hT : T₁ * T₂ ≤ L ^ e₀)
    (hLη : (M + 2 * B) / η ≤ L) :
    T₁ * (T₂ * (x * (M * L ^ (-A)) + 2 * B * (L ^ Cp * (x * L ^ (-A))))) ≤ η * (x / L) := by
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  have hLA : 0 < L ^ (-A) := Real.rpow_pos_of_pos hL0 _
  have hLC : 1 ≤ L ^ Cp := Real.one_le_rpow hL hCp
  have hinner : x * (M * L ^ (-A)) + 2 * B * (L ^ Cp * (x * L ^ (-A))) ≤
      x * (M + 2 * B) * (L ^ (-A) * L ^ Cp) := by
    have h1 : x * (M * L ^ (-A)) ≤ x * (M * L ^ (-A)) * L ^ Cp :=
      le_mul_of_one_le_right (mul_nonneg hx.le (mul_nonneg hM hLA.le)) hLC
    calc x * (M * L ^ (-A)) + 2 * B * (L ^ Cp * (x * L ^ (-A)))
        ≤ x * (M * L ^ (-A)) * L ^ Cp + 2 * B * (L ^ Cp * (x * L ^ (-A))) := by linarith
      _ = x * (M + 2 * B) * (L ^ (-A) * L ^ Cp) := by ring
  have hc0 : 0 ≤ x * (M * L ^ (-A)) + 2 * B * (L ^ Cp * (x * L ^ (-A))) :=
    add_nonneg (mul_nonneg hx.le (mul_nonneg hM hLA.le))
      (mul_nonneg (mul_nonneg zero_le_two hB)
        (mul_nonneg (le_trans zero_le_one hLC) (mul_nonneg hx.le hLA.le)))
  have hexp : L ^ e₀ * (L ^ (-A) * L ^ Cp) = (L ^ 2)⁻¹ := by
    have e : e₀ + (-A + Cp) = -(2 : ℝ) := by linarith
    rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, e, Real.rpow_neg hL0.le, Real.rpow_two]
  have hMB : M + 2 * B ≤ η * L := by
    have h := (div_le_iff₀ hη).mp hLη
    linarith
  have hinv : L * (L ^ 2)⁻¹ = L⁻¹ := by
    rw [pow_two, mul_inv, ← mul_assoc, mul_inv_cancel₀ hL0.ne', one_mul]
  calc T₁ * (T₂ * (x * (M * L ^ (-A)) + 2 * B * (L ^ Cp * (x * L ^ (-A)))))
      = T₁ * T₂ * (x * (M * L ^ (-A)) + 2 * B * (L ^ Cp * (x * L ^ (-A)))) :=
        (mul_assoc _ _ _).symm
    _ ≤ L ^ e₀ * (x * (M + 2 * B) * (L ^ (-A) * L ^ Cp)) :=
        mul_le_mul hT hinner hc0 (Real.rpow_nonneg hL0.le _)
    _ = x * (M + 2 * B) * (L ^ e₀ * (L ^ (-A) * L ^ Cp)) := by ring
    _ = x * (M + 2 * B) * (L ^ 2)⁻¹ := by rw [hexp]
    _ ≤ x * (η * L) * (L ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMB hx.le)
          (inv_nonneg.mpr (sq_nonneg L))
    _ = η * x * (L * (L ^ 2)⁻¹) := by ring
    _ = η * (x / L) := by rw [hinv, div_eq_mul_inv, mul_assoc]

end Allocation

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
