module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Statements

/-!
# The proved chain of the prime extraction

This file proves, from the statements of `Extraction/Statements.lean`:

* `coreBounded_of`: `SlotBounded d → ArrayWeightBounded q → CoreBounded d q`;
* `compositeVanishing_of` (`[P-07:0241–0247, 0304–0315, 0342–0345, 0404–0407, 0612–0615]`):
  `ProxyReplacement ∧ StripMass ∧ CoinFailure ∧ RetainedBound ∧ CoreBounded → CompositeVanishing`;
* `weightedPrimeBound_of` (`[P-07:0619–0629]`):
  `PresieveBound ∧ CompositeVanishing ∧ SiftedDecomposition ∧ ModelBounds ∧ CoreBounded
    → WeightedPrimeBound`;
* `primeStatisticFixedClassAt_of` (`[P-07:0631–0702]`): the removal of the array weight and the
  order of the limits,
  `WeightedPrimeBound ∧ VarianceBound ∧ SlotBounded ∧ PrimeMassBound
    → PrimeStatisticFixedClassAt d H b`;
* `primeExtractionReductionAt_of`: `ExtractionLeaves d H b q q₀ → PrimeExtractionReductionAt d H b`,
  and `primeExtractionReduction_one_of`, the same for `PrimeExtractionReduction 1`.

The order of choices is the one of `[P-07:0695–0702]`: the interior data and `c₀`; `h`, then `γ`
and the finitely many composite lengths; the Type II precision and `K`; finitely many disjoint
arrays; the limit in `x`; then the number of arrays and `h`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

open Filter
open scoped Topology ContDiff

noncomputable section

/-! ### Elementary inequalities -/

theorem abs_add_four (a b c d : ℝ) : |a + (b + (c + d))| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le a (b + (c + d))
  have h2 := abs_add_le b (c + d)
  have h3 := abs_add_le c d
  linarith

theorem abs_sub_le_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h := abs_add_le a (-b)
  rwa [abs_neg, ← sub_eq_add_neg] at h

theorem slotMass_nonneg {d : ℕ} (S : Fin d → Finset ℕ) : 0 ≤ slotMass S := by
  unfold slotMass
  exact Finset.sum_nonneg fun 𝔩 _ => by positivity

/-- `C₁ e^{-h} (4h+3)/c₀ → 0` along the even integers: the choice of `h` in
`[P-07:0690–0692]`. -/
theorem exists_even_small (C₁ : ℝ) {c₀ δ : ℝ} (hδ : 0 < δ) (h₀ : ℕ) :
    ∃ h : ℕ, h₀ ≤ h ∧ Even h ∧
      C₁ * Real.exp (-(h : ℝ)) * ((4 * (h : ℝ) + 3) / c₀) ≤ δ := by
  have h1 : Tendsto (fun t : ℝ => t ^ 1 * Real.exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
  have h0 : Tendsto (fun t : ℝ => t ^ 0 * Real.exp (-t)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 0
  have h2 : Tendsto (fun t : ℝ =>
      C₁ / c₀ * (4 * (t ^ 1 * Real.exp (-t)) + 3 * (t ^ 0 * Real.exp (-t))))
      atTop (𝓝 (C₁ / c₀ * (4 * 0 + 3 * 0))) :=
    ((h1.const_mul 4).add (h0.const_mul 3)).const_mul (C₁ / c₀)
  have h2' : Tendsto (fun t : ℝ =>
      C₁ / c₀ * (4 * (t ^ 1 * Real.exp (-t)) + 3 * (t ^ 0 * Real.exp (-t))))
      atTop (𝓝 0) := by
    have e : C₁ / c₀ * (4 * 0 + 3 * 0) = (0 : ℝ) := by ring
    rwa [e] at h2
  have h3 : Tendsto (fun k : ℕ => ((2 * k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp
      (tendsto_atTop_mono (fun k => (Nat.le_mul_of_pos_left k two_pos : k ≤ 2 * k)) tendsto_id)
  have hev := (h2'.comp h3).eventually (eventually_lt_nhds hδ)
  obtain ⟨k, hk1, hk2⟩ := (hev.and (eventually_ge_atTop h₀)).exists
  refine ⟨2 * k, by omega, even_two_mul k, ?_⟩
  have e : C₁ * Real.exp (-((2 * k : ℕ) : ℝ)) * ((4 * ((2 * k : ℕ) : ℝ) + 3) / c₀) =
      C₁ / c₀ * (4 * (((2 * k : ℕ) : ℝ) ^ 1 * Real.exp (-((2 * k : ℕ) : ℝ))) +
        3 * (((2 * k : ℕ) : ℝ) ^ 0 * Real.exp (-((2 * k : ℕ) : ℝ)))) := by
    rw [pow_one, pow_zero]
    ring
  rw [e]
  exact hk1.le

/-! ### Disjoint arrays exist -/

/-- The exponent number `t` of a grid of `N` points in `(1/10, 1/5)`. -/
def gridExponent (N t : ℕ) : ℝ := 1 / 10 + ((t : ℝ) + 1) / (10 * ((N : ℝ) + 1))

theorem gridExponent_strictMono (N : ℕ) : StrictMono (gridExponent N) := by
  intro s t hst
  have hden : (0 : ℝ) < 10 * ((N : ℝ) + 1) := by positivity
  have hst' : (s : ℝ) + 1 < (t : ℝ) + 1 := by
    have h : (s : ℝ) < (t : ℝ) := by exact_mod_cast hst
    linarith
  have h := div_lt_div_of_pos_right hst' hden
  unfold gridExponent
  linarith

theorem gridExponent_gt (N t : ℕ) : 1 / 10 < gridExponent N t := by
  unfold gridExponent
  have h : (0 : ℝ) < ((t : ℝ) + 1) / (10 * ((N : ℝ) + 1)) := by positivity
  linarith

theorem gridExponent_lt {N t : ℕ} (h : t < N) : gridExponent N t < 1 / 5 := by
  unfold gridExponent
  have hden : (0 : ℝ) < 10 * ((N : ℝ) + 1) := by positivity
  have h1 : (t : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast h
  have h2 : ((t : ℝ) + 1) / (10 * ((N : ℝ) + 1)) < 1 / 10 := by
    rw [div_lt_iff₀ hden]
    linarith
  linarith

/-- For every `n` and `K` there are `n` disjoint arrays of `K` bands (`[P-07:0631–0635]`: "this is
possible for every finite `b`"). -/
theorem exists_arraysDisjoint (n K : ℕ) : ∃ 𝔄 : Fin n → MarkingArray K, ArraysDisjoint 𝔄 := by
  have hidx : ∀ (a : Fin n) (i : Fin K), (a : ℕ) * K + (i : ℕ) < n * K := by
    intro a i
    have h1 : ((a : ℕ) + 1) * K ≤ n * K := Nat.mul_le_mul_right K (Nat.succ_le_of_lt a.2)
    have h2 : ((a : ℕ) + 1) * K = (a : ℕ) * K + K := Nat.succ_mul _ _
    have hi := i.2
    omega
  refine ⟨fun a =>
    { exponent := fun i => gridExponent (n * K) ((a : ℕ) * K + (i : ℕ))
      strictMono := fun i i' hii' => gridExponent_strictMono _ (by
        have h : (i : ℕ) < (i' : ℕ) := hii'
        omega)
      gt_tenth := fun i => gridExponent_gt _ _
      lt_fifth := fun i => gridExponent_lt (hidx a i) }, ?_⟩
  intro p p' hpp'
  have h : gridExponent (n * K) ((p.1 : ℕ) * K + (p.2 : ℕ)) =
      gridExponent (n * K) ((p'.1 : ℕ) * K + (p'.2 : ℕ)) := hpp'
  have h' := (gridExponent_strictMono (n * K)).injective h
  have hi := p.2.2
  have hi' := p'.2.2
  have key : (p.1 : ℕ) = (p'.1 : ℕ) := by
    rcases lt_trichotomy (p.1 : ℕ) (p'.1 : ℕ) with hlt | heq | hgt
    · exfalso
      have h3 := Nat.mul_le_mul_right K (Nat.succ_le_of_lt hlt)
      rw [Nat.succ_mul] at h3
      omega
    · exact heq
    · exfalso
      have h3 := Nat.mul_le_mul_right K (Nat.succ_le_of_lt hgt)
      rw [Nat.succ_mul] at h3
      omega
  have key2 : (p.2 : ℕ) = (p'.2 : ℕ) := by
    rw [key] at h'
    omega
  exact Prod.ext (Fin.ext key) (Fin.ext key2)

/-- A single array is a disjoint family. -/
theorem arraysDisjoint_single {K : ℕ} (𝔞 : MarkingArray K) :
    ArraysDisjoint (fun _ : Fin 1 => 𝔞) := by
  intro p p' h
  have h2 : p.2 = p'.2 := 𝔞.strictMono.injective h
  exact Prod.ext (Subsingleton.elim _ _) h2

/-! ### The centered core is bounded -/

/-- `SlotBounded` and `ArrayWeightBounded` give `CoreBounded` (`[P-06:0079–0082]`). -/
theorem coreBounded_of {d : ℕ} {q : ℝ} (hS : SlotBounded d) (hW : ArrayWeightBounded q) :
    CoreBounded d q := by
  intro ε hε R hR K
  obtain ⟨BS, hBS⟩ := hS ε hε R hR
  obtain ⟨CW, hCW⟩ := hW K
  refine ⟨max CW 0 * max BS 0, mul_nonneg (le_max_right _ _) (le_max_right _ _), fun 𝔞 => ?_⟩
  filter_upwards [hBS, hCW 𝔞] with x hx1 hx2 S hSadm u hu1 hu2
  obtain ⟨hmass, hcount⟩ := hx1 S hSadm
  have h1 : |markedWeight q 𝔞 x u| ≤ max CW 0 := (hx2 u).trans (le_max_left _ _)
  have hc0 : (0 : ℝ) ≤ (slotCount S u : ℝ) := Nat.cast_nonneg _
  have hm0 : 0 ≤ slotMass S := slotMass_nonneg S
  have hc := hcount u hu1 hu2
  have hB := le_max_left BS 0
  have h2 : |(slotCount S u : ℝ) - slotMass S| ≤ max BS 0 := by
    rw [abs_le]
    constructor <;> linarith
  unfold centeredCore
  rw [abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) (le_max_right _ _)

/-! ### Composite terms: `[P-07:0241–0615]` -/

/-- The bookkeeping of the composite terms for abstract coefficient functions: `Pj`, `Aj`, `At` are
the `j`-fold convolutions of the prime, proxy and stripped coefficients at `u + 1`, and `fl`, `rt`
the failed and retained coin masses. -/
theorem composite_core {Φ : ℝ → ℝ} {R x : ℝ} (hR : ∀ t, R < t → Φ t = 0) (hx : 0 < x)
    (hΦ0 : ∀ t, 0 ≤ Φ t) (cls : ℕ → Prop) (F Pj Aj At fl rt Dabs : ℕ → ℝ) {B δ : ℝ}
    (hB : 0 ≤ B) (hone : ∀ u, rt u + fl u = 1)
    (hF : ∀ u : ℕ, Φ ((u : ℝ) / x) ≠ 0 → |F u| ≤ B)
    (hD : ∀ u, |Aj u - At u| ≤ Dabs u)
    (h1 : |shiftSum Φ x cls (fun u => F u * (Pj u - Aj u))| ≤ δ)
    (h2 : B * shiftSum Φ x (fun _ => True) Dabs ≤ δ)
    (h3 : B * shiftSum Φ x (fun _ => True) (fun u => |At u * fl u|) ≤ δ)
    (h4 : |shiftSum Φ x cls (fun u => F u * At u * rt u)| ≤ δ) :
    |shiftSum Φ x cls (fun u => F u * Pj u)| ≤ 4 * δ := by
  have e1 := shiftSum_add hR hx cls (fun u => F u * (At u * fl u))
    (fun u => F u * At u * rt u)
  have e2 := shiftSum_add hR hx cls (fun u => F u * (Aj u - At u))
    (fun u => F u * (At u * fl u) + F u * At u * rt u)
  have e3 := shiftSum_add hR hx cls (fun u => F u * (Pj u - Aj u))
    (fun u => F u * (Aj u - At u) + (F u * (At u * fl u) + F u * At u * rt u))
  have e0 : shiftSum Φ x cls (fun u => F u * Pj u) =
      shiftSum Φ x cls (fun u => F u * (Pj u - Aj u) +
        (F u * (Aj u - At u) + (F u * (At u * fl u) + F u * At u * rt u))) :=
    shiftSum_congr Φ x cls fun u => by linear_combination (-(F u * At u)) * hone u
  have b2 : |shiftSum Φ x cls (fun u => F u * (Aj u - At u))| ≤
      B * shiftSum Φ x (fun _ => True) Dabs :=
    abs_shiftSum_le hR hx hΦ0 (fun _ _ => trivial) hB
      (fun u => (abs_nonneg _).trans (hD u)) fun u _ hu =>
        calc |F u * (Aj u - At u)| = |F u| * |Aj u - At u| := abs_mul _ _
          _ ≤ B * Dabs u := mul_le_mul (hF u hu) (hD u) (abs_nonneg _) hB
  have b3 : |shiftSum Φ x cls (fun u => F u * (At u * fl u))| ≤
      B * shiftSum Φ x (fun _ => True) (fun u => |At u * fl u|) :=
    abs_shiftSum_le hR hx hΦ0 (fun _ _ => trivial) hB (fun u => abs_nonneg _) fun u _ hu =>
      calc |F u * (At u * fl u)| = |F u| * |At u * fl u| := abs_mul _ _
        _ ≤ B * |At u * fl u| := mul_le_mul_of_nonneg_right (hF u hu) (abs_nonneg _)
  have etot : shiftSum Φ x cls (fun u => F u * Pj u) =
      shiftSum Φ x cls (fun u => F u * (Pj u - Aj u)) +
        (shiftSum Φ x cls (fun u => F u * (Aj u - At u)) +
          (shiftSum Φ x cls (fun u => F u * (At u * fl u)) +
            shiftSum Φ x cls (fun u => F u * At u * rt u))) := by
    rw [e0, e3, e2, e1]
  have hfour := abs_add_four (shiftSum Φ x cls (fun u => F u * (Pj u - Aj u)))
    (shiftSum Φ x cls (fun u => F u * (Aj u - At u)))
    (shiftSum Φ x cls (fun u => F u * (At u * fl u)))
    (shiftSum Φ x cls (fun u => F u * At u * rt u))
  rw [etot]
  linarith

/-- **(ext:composite-vanishing)** from its four parts (`[P-07:0241–0615]`): the tuple sum over
primes is the proxy sum up to `o(x/L)` (`ProxyReplacement`), the proxy sum is the stripped sum up
to `o(x/L)` in absolute mass (`StripMass`), and the stripped sum is the sum over the failed
outcomes, of absolute mass `o(x/L)` (`CoinFailure`), plus the sum over the retained outcomes,
which is `o(x/L)` by Theorem 6.1 (`RetainedBound`). The bounded factor `𝒲 (f_x - C_x)` and the
indicator of the class are applied to the two absolute estimates here. -/
theorem compositeVanishing_of {d H b : ℕ} {q q₀ : ℝ} (hProxy : ProxyReplacement d H b q)
    (hStrip : StripMass) (hCoin : CoinFailure q₀) (hRet : RetainedBound d H b q q₀)
    (hCore : CoreBounded d q) : CompositeVanishing d H b q := by
  intro ε hε Φ hΦ γ hγ hγ1
  obtain ⟨R, hR0, hR⟩ := hΦ.exists_upper
  obtain ⟨K₀, hK₀⟩ := hProxy ε hε Φ hΦ γ hγ hγ1
  refine ⟨K₀, fun K hK 𝔞 j hj2 hjγ η hη => ?_⟩
  obtain ⟨B, hB0, hB⟩ := hCore ε hε R hR0 K
  obtain ⟨c₁, c₂, hc₁, hc₂, -, hfail⟩ := hCoin Φ hΦ γ hγ hγ1 j hj2
  have hB1 : (0 : ℝ) < 4 * (B + 1) := by linarith
  have hη' : 0 < η / (4 * (B + 1)) := div_pos hη hB1
  have hBη : B * (η / (4 * (B + 1))) ≤ η / 4 := by
    rw [mul_div_assoc', div_le_iff₀ hB1]
    have e : η / 4 * (4 * (B + 1)) = B * η + η := by ring
    rw [e]
    linarith
  filter_upwards [hK₀ K hK 𝔞 j hj2 hjγ (η / 4) (by linarith),
    hStrip Φ hΦ γ hγ hγ1 j hj2 (η / (4 * (B + 1))) hη',
    hfail (η / (4 * (B + 1))) hη',
    hRet ε hε Φ hΦ γ hγ hγ1 K 𝔞 j hj2 c₁ c₂ hc₁ hc₂ (η / 4) (by linarith), hB 𝔞,
    eventually_gt_atTop (1 : ℝ)] with x h1 h2 h3 h4 h5 hx1 S hS
  have hx0 : 0 < x := by linarith
  have hX : 0 < x / Real.log x := div_pos hx0 (Real.log_pos hx1)
  have hFb : ∀ u : ℕ, Φ ((u : ℝ) / x) ≠ 0 → |centeredCore q 𝔞 x S u| ≤ B := fun u hu =>
    h5 S hS u (hΦ.range_of_ne_zero hR hx0 hu).1 (hΦ.range_of_ne_zero hR hx0 hu).2
  have hD : ∀ u : ℕ, |convPow j (proxyCoeff x γ) (u + 1) -
      convPow j (strippedCoeff x γ (candidatePrimes x)) (u + 1)| ≤
        ∑ e ∈ orderedFactorizations j (u + 1),
          |∏ i, proxyCoeff x γ (e i) - ∏ i, strippedCoeff x γ (candidatePrimes x) (e i)| := by
    intro u
    unfold convPow
    rw [← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hscale : ∀ t : ℝ, t ≤ η / (4 * (B + 1)) * (x / Real.log x) →
      B * t ≤ η / 4 * (x / Real.log x) := by
    intro t ht
    calc B * t ≤ B * (η / (4 * (B + 1)) * (x / Real.log x)) :=
          mul_le_mul_of_nonneg_left ht hB0
      _ = B * (η / (4 * (B + 1))) * (x / Real.log x) := by ring
      _ ≤ η / 4 * (x / Real.log x) := mul_le_mul_of_nonneg_right hBη hX.le
  have key := composite_core hR hx0 hΦ.nonneg (fun v => v ≡ b [MOD H])
    (centeredCore q 𝔞 x S)
    (fun u => convPow j (primeCoeff (x ^ γ)) (u + 1))
    (fun u => convPow j (proxyCoeff x γ) (u + 1))
    (fun u => convPow j (strippedCoeff x γ (candidatePrimes x)) (u + 1))
    (fun u => failedMass (candidateGroups x) c₁ c₂ q₀ j x u)
    (fun u => retainedMass (candidateGroups x) c₁ c₂ q₀ j x u)
    (fun u => ∑ e ∈ orderedFactorizations j (u + 1),
      |∏ i, proxyCoeff x γ (e i) - ∏ i, strippedCoeff x γ (candidatePrimes x) (e i)|)
    (δ := η / 4 * (x / Real.log x)) hB0
    (fun u => retainedMass_add_failedMass (candidateGroups x) c₁ c₂ q₀ j x u) hFb hD
    (h1 S hS) (hscale _ h2) (hscale _ h3) (h4 S hS)
  refine key.trans (le_of_eq ?_)
  ring

/-! ### The weighted prime sum: `[P-07:0619–0629]` -/

/-- The arithmetic of (ext:weighted-primes): `Sf` is the presifted sum, `P` the prime sum, `Sc` the
composite sums, `m = m_𝒲 ≥ c > 0`. -/
theorem weighted_core {Sf P Sc m X A η c : ℝ} (hm : c ≤ m) (hc : 0 < c) (hX : 0 ≤ X)
    (hη : 0 < η) (hSf : |Sf| ≤ (A + η / 2) * m * X) (hSc : |Sc| ≤ η * c / 4 * X)
    (hD : |Sf - P - Sc| ≤ η * c / 4 * X) : |1 / m * P| ≤ (A + η) * X := by
  have hm0 : 0 < m := lt_of_lt_of_le hc hm
  have hP : |P| ≤ (A + η / 2) * m * X + η * c / 2 * X := by
    have a1 := abs_le.mp hSf
    have a2 := abs_le.mp hSc
    have a3 := abs_le.mp hD
    rw [abs_le]
    constructor <;> linarith
  have hcm : η * c / 2 * X ≤ η * m / 2 * X := by
    refine mul_le_mul_of_nonneg_right ?_ hX
    have h := mul_le_mul_of_nonneg_left hm hη.le
    linarith
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hm0), div_mul_eq_mul_div, one_mul, div_le_iff₀ hm0]
  calc |P| ≤ (A + η / 2) * m * X + η * c / 2 * X := hP
    _ ≤ (A + η / 2) * m * X + η * m / 2 * X := by linarith
    _ = (A + η) * X * m := by ring

/-- **(ext:weighted-primes)** (`[P-07:0619–0629]`): "Subtract the composite contribution from
(ext:presift). All primes in the support exceed `z` for large `x`." The presifted sum is the prime
sum plus the composite tuple sums (`SiftedDecomposition`); the latter are `o(x/L)`
(`CompositeVanishing`), and dividing by `m_𝒲 ≥ c_K > 0` (`ModelBounds`) keeps the constant of
(ext:presift). -/
theorem weightedPrimeBound_of {d H b : ℕ} {q : ℝ} (hPre : PresieveBound d H b q)
    (hComp : CompositeVanishing d H b q) (hDec : SiftedDecomposition) (hMod : ModelBounds q)
    (hCore : CoreBounded d q) : WeightedPrimeBound d H b q := by
  intro ε hε c₀ hc₀ hc₀ε hc₀4 Φ hΦ
  obtain ⟨R, hR0, hR⟩ := hΦ.exists_upper
  obtain ⟨C₁, hC₁, h₀, hpre⟩ := hPre ε hε c₀ hc₀ hc₀ε hc₀4 Φ hΦ
  refine ⟨C₁, hC₁, h₀, fun h hh heven => ?_⟩
  have hden : (0 : ℝ) < 4 * (h : ℝ) + 3 := by positivity
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ, γ = c₀ / (4 * (h : ℝ) + 3) := ⟨_, rfl⟩
  have hγ : 0 < γ := by
    rw [hγdef]
    exact div_pos hc₀ hden
  have hγ1 : γ < 1 := by
    rw [hγdef, div_lt_one hden]
    have h0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg h
    linarith
  obtain ⟨K₀, hK₀⟩ := hComp ε hε Φ hΦ γ hγ hγ1
  refine ⟨K₀, fun K hK 𝔞 η hη => ?_⟩
  obtain ⟨c, C, hc, hmod⟩ := hMod K
  obtain ⟨B, hB0, hB⟩ := hCore ε hε R hR0 K
  have hJ0 : (0 : ℝ) < (⌊2 / γ⌋₊ : ℝ) + 1 := by positivity
  have hJ1 : (0 : ℝ) < 4 * ((⌊2 / γ⌋₊ : ℝ) + 1) := by linarith
  have hη2 : 0 < η * c / (4 * ((⌊2 / γ⌋₊ : ℝ) + 1)) := div_pos (mul_pos hη hc) hJ1
  have hη3 : 0 < η * c / 4 := div_pos (mul_pos hη hc) (by norm_num)
  have hcomp : ∀ᶠ x : ℝ in atTop, ∀ j ∈ Finset.Icc 2 ⌊2 / γ⌋₊,
      ∀ S : Fin d → Finset ℕ, SlotsAdmissible ε x S →
        |shiftSum Φ x (fun v => v ≡ b [MOD H])
            (fun u => centeredCore q 𝔞 x S u * convPow j (primeCoeff (x ^ γ)) (u + 1))| ≤
          η * c / (4 * ((⌊2 / γ⌋₊ : ℝ) + 1)) * (x / Real.log x) := by
    refine (Filter.eventually_all_finset _).mpr fun j hj => ?_
    have hj' := Finset.mem_Icc.mp hj
    have hjle : (j : ℝ) ≤ 2 / γ :=
      ((Nat.cast_le (α := ℝ)).mpr hj'.2).trans (Nat.floor_le (div_nonneg zero_le_two hγ.le))
    exact hK₀ K hK 𝔞 j hj'.1 hjle _ hη2
  filter_upwards [hpre h hh heven K 𝔞 (η / 2) (by linarith), hcomp,
    hDec Φ hΦ γ hγ hγ1 B (η * c / 4) hη3, hmod 𝔞, hB 𝔞, eventually_gt_atTop (1 : ℝ)]
    with x h1 h2 h3 h4 h5 hx1 S hS
  have hx0 : 0 < x := by linarith
  have hX : 0 < x / Real.log x := div_pos hx0 (Real.log_pos hx1)
  obtain ⟨hmc, -, -⟩ := h4
  have hFb : ∀ u : ℕ, Φ ((u : ℝ) / x) ≠ 0 → |centeredCore q 𝔞 x S u| ≤ B := fun u hu =>
    h5 S hS u (hΦ.range_of_ne_zero hR hx0 hu).1 (hΦ.range_of_ne_zero hR hx0 hu).2
  have hD := h3 H b (centeredCore q 𝔞 x S) hFb
  have h1' := h1 S hS
  rw [← hγdef] at h1'
  have hδ0 : 0 ≤ η * c / (4 * ((⌊2 / γ⌋₊ : ℝ) + 1)) * (x / Real.log x) :=
    mul_nonneg hη2.le hX.le
  have hSc : |∑ j ∈ Finset.Icc 2 ⌊2 / γ⌋₊, 1 / (j.factorial : ℝ) *
      shiftSum Φ x (fun v => v ≡ b [MOD H])
        (fun u => centeredCore q 𝔞 x S u * convPow j (primeCoeff (x ^ γ)) (u + 1))| ≤
      η * c / 4 * (x / Real.log x) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ j ∈ Finset.Icc 2 ⌊2 / γ⌋₊, |1 / (j.factorial : ℝ) *
        shiftSum Φ x (fun v => v ≡ b [MOD H])
          (fun u => centeredCore q 𝔞 x S u * convPow j (primeCoeff (x ^ γ)) (u + 1))| ≤
        η * c / (4 * ((⌊2 / γ⌋₊ : ℝ) + 1)) * (x / Real.log x) := by
      intro j hj
      have hfac : (1 : ℝ) ≤ (j.factorial : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.factorial_pos j)
      have h1j : 1 / (j.factorial : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr hfac
      have h0j : 0 ≤ 1 / (j.factorial : ℝ) := by positivity
      rw [abs_mul, abs_of_nonneg h0j]
      exact (mul_le_mul h1j (h2 j hj S hS) (abs_nonneg _) zero_le_one).trans
        (le_of_eq (one_mul _))
    have hcard : ((Finset.Icc 2 ⌊2 / γ⌋₊).card : ℝ) ≤ (⌊2 / γ⌋₊ : ℝ) + 1 := by
      rw [Nat.card_Icc]
      have hle : ⌊2 / γ⌋₊ + 1 - 2 ≤ ⌊2 / γ⌋₊ + 1 := Nat.sub_le _ _
      exact_mod_cast hle
    have hcancel : ((⌊2 / γ⌋₊ : ℝ) + 1) * (η * c / (4 * ((⌊2 / γ⌋₊ : ℝ) + 1))) = η * c / 4 := by
      rw [mul_div_assoc', mul_comm 4 ((⌊2 / γ⌋₊ : ℝ) + 1), mul_div_mul_left _ _ hJ0.ne']
    calc ∑ j ∈ Finset.Icc 2 ⌊2 / γ⌋₊, |1 / (j.factorial : ℝ) *
          shiftSum Φ x (fun v => v ≡ b [MOD H])
            (fun u => centeredCore q 𝔞 x S u * convPow j (primeCoeff (x ^ γ)) (u + 1))|
        ≤ ∑ _j ∈ Finset.Icc 2 ⌊2 / γ⌋₊,
            η * c / (4 * ((⌊2 / γ⌋₊ : ℝ) + 1)) * (x / Real.log x) := Finset.sum_le_sum hterm
      _ = ((Finset.Icc 2 ⌊2 / γ⌋₊).card : ℝ) *
            (η * c / (4 * ((⌊2 / γ⌋₊ : ℝ) + 1)) * (x / Real.log x)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((⌊2 / γ⌋₊ : ℝ) + 1) *
            (η * c / (4 * ((⌊2 / γ⌋₊ : ℝ) + 1)) * (x / Real.log x)) :=
          mul_le_mul_of_nonneg_right hcard hδ0
      _ = ((⌊2 / γ⌋₊ : ℝ) + 1) * (η * c / (4 * ((⌊2 / γ⌋₊ : ℝ) + 1))) *
            (x / Real.log x) := by ring
      _ = η * c / 4 * (x / Real.log x) := by rw [hcancel]
  have htarget : shiftSum Φ x (fun v => v.Prime ∧ v ≡ b [MOD H])
      (fun u => normWeight q 𝔞 x u * ((slotCount S u : ℝ) - slotMass S)) =
      1 / arrayMean q 𝔞 x *
        shiftSum Φ x (fun v => v.Prime ∧ v ≡ b [MOD H]) (centeredCore q 𝔞 x S) := by
    rw [← shiftSum_const_mul hR hx0]
    refine shiftSum_congr Φ x _ fun u => ?_
    unfold normWeight centeredCore
    ring
  rw [htarget]
  exact weighted_core hmc hc hX.le hη h1' hSc hD

/-! ### Removal of the array weight: `[P-07:0631–0693]` -/

/-- The Cauchy–Schwarz step of `[P-07:0672–0686]` for abstract normalized weights `nw a`
(`= 𝒲_a / m_a`) and an abstract centered statistic `g` (`= f_x - C_x`): if each weighted sum is at
most `E`, the sum of the squared deviation over primes at most `V`, the number of primes at most
`Mp` and `|g| ≤ B`, then the unweighted sum is at most `E + √(V B² Mp)`. -/
theorem deweight_core {Φ : ℝ → ℝ} {R x : ℝ} (hR : ∀ t, R < t → Φ t = 0) (hx : 0 < x)
    (hΦ0 : ∀ t, 0 ≤ Φ t) {P : ℕ → Prop} (hP : ∀ v, P v → v.Prime) {n : ℕ} (hn : 0 < n)
    (nw : Fin n → ℕ → ℝ) (g : ℕ → ℝ) {B E V Mp T : ℝ} (hT : 0 ≤ T)
    (hg : ∀ u : ℕ, Φ ((u : ℝ) / x) ≠ 0 → |g u| ≤ B)
    (hE : ∀ a, |shiftSum Φ x P (fun u => nw a u * g u)| ≤ E)
    (hV : shiftSum Φ x Nat.Prime (fun u => ((∑ a, nw a u) / (n : ℝ) - 1) ^ 2) ≤ V)
    (hM : shiftSum Φ x Nat.Prime (fun _ => 1) ≤ Mp)
    (hVT : V * (B ^ 2 * Mp) ≤ T ^ 2) : |shiftSum Φ x P g| ≤ E + T := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := hn'.ne'
  have hinv : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
  -- the averaged weighted sum
  have havg : shiftSum Φ x P (fun u => (∑ a, nw a u) / (n : ℝ) * g u) =
      1 / (n : ℝ) * ∑ a, shiftSum Φ x P (fun u => nw a u * g u) :=
    calc shiftSum Φ x P (fun u => (∑ a, nw a u) / (n : ℝ) * g u)
        = shiftSum Φ x P (fun u => 1 / (n : ℝ) * ∑ a, nw a u * g u) :=
          shiftSum_congr Φ x P fun u => by
            rw [← Finset.sum_mul]
            ring
      _ = 1 / (n : ℝ) * shiftSum Φ x P (fun u => ∑ a, nw a u * g u) :=
          shiftSum_const_mul hR hx P _ _
      _ = 1 / (n : ℝ) * ∑ a, shiftSum Φ x P (fun u => nw a u * g u) :=
          congrArg (fun t => 1 / (n : ℝ) * t)
            (shiftSum_finset_sum hR hx P Finset.univ fun a u => nw a u * g u)
  have h1 : |shiftSum Φ x P (fun u => (∑ a, nw a u) / (n : ℝ) * g u)| ≤ E := by
    rw [havg, abs_mul, abs_of_nonneg hinv]
    calc 1 / (n : ℝ) * |∑ a, shiftSum Φ x P (fun u => nw a u * g u)|
        ≤ 1 / (n : ℝ) * ∑ _a : Fin n, E :=
          mul_le_mul_of_nonneg_left
            ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => hE a)) hinv
      _ = E := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, one_div,
            inv_mul_cancel_left₀ hn0]
  -- Cauchy–Schwarz for the deviation
  have h2 := shiftSum_mul_sq_le hR hx hΦ0 P (fun u => (∑ a, nw a u) / (n : ℝ) - 1) g
  have h3 : shiftSum Φ x P (fun u => ((∑ a, nw a u) / (n : ℝ) - 1) ^ 2) ≤ V := by
    refine le_trans ?_ hV
    have h := abs_shiftSum_le hR hx hΦ0 (P := P) (Q := Nat.Prime) hP (B := 1) zero_le_one
      (g := fun u => ((∑ a, nw a u) / (n : ℝ) - 1) ^ 2)
      (g' := fun u => ((∑ a, nw a u) / (n : ℝ) - 1) ^ 2)
      (fun u => sq_nonneg _) (fun u _ _ => by
        rw [one_mul]
        exact le_of_eq (abs_of_nonneg (sq_nonneg _)))
    rw [one_mul] at h
    exact (le_abs_self _).trans h
  have hB2 : ∀ u : ℕ, Φ ((u : ℝ) / x) ≠ 0 → g u ^ 2 ≤ B ^ 2 := fun u hu =>
    sq_le_sq' (abs_le.mp (hg u hu)).1 (abs_le.mp (hg u hu)).2
  have h4 : shiftSum Φ x P (fun u => g u ^ 2) ≤ B ^ 2 * Mp := by
    have h := abs_shiftSum_le hR hx hΦ0 (P := P) (Q := Nat.Prime) hP (B := B ^ 2)
      (sq_nonneg B) (g := fun u => g u ^ 2) (g' := fun _ => 1) (fun _ => zero_le_one)
      (fun u _ hu => by
        rw [mul_one, abs_of_nonneg (sq_nonneg _)]
        exact hB2 u hu)
    exact (le_abs_self _).trans (h.trans (mul_le_mul_of_nonneg_left hM (sq_nonneg B)))
  have h5 : 0 ≤ shiftSum Φ x P (fun u => ((∑ a, nw a u) / (n : ℝ) - 1) ^ 2) :=
    shiftSum_nonneg hΦ0 P fun u => sq_nonneg _
  have h6 : 0 ≤ shiftSum Φ x P (fun u => g u ^ 2) :=
    shiftSum_nonneg hΦ0 P fun u => sq_nonneg _
  have h7 : shiftSum Φ x P (fun u => ((∑ a, nw a u) / (n : ℝ) - 1) * g u) ^ 2 ≤ T ^ 2 :=
    h2.trans ((mul_le_mul h3 h4 h6 (h5.trans h3)).trans hVT)
  have h8 : |shiftSum Φ x P (fun u => ((∑ a, nw a u) / (n : ℝ) - 1) * g u)| ≤ T :=
    abs_le_of_sq_le_sq h7 hT
  -- the unweighted sum is the difference
  have hs := shiftSum_sub hR hx P (fun u => (∑ a, nw a u) / (n : ℝ) * g u)
    (fun u => ((∑ a, nw a u) / (n : ℝ) - 1) * g u)
  have hsplit : shiftSum Φ x P g =
      shiftSum Φ x P (fun u => (∑ a, nw a u) / (n : ℝ) * g u) -
        shiftSum Φ x P (fun u => ((∑ a, nw a u) / (n : ℝ) - 1) * g u) := by
    rw [← hs]
    exact shiftSum_congr Φ x P fun u => by ring
  rw [hsplit]
  exact (abs_sub_le_add _ _).trans (add_le_add h1 h8)

/-- **Theorem 7.1^{H,b} from the weighted prime bound and the variance bound**
(`[P-07:0631–0702]`). Average (ext:weighted-primes) over `n` disjoint arrays; by Cauchy–Schwarz,
(ext:prime-deweight-square), the boundedness of `f_x - C_x` and the number of primes, the
difference from the unweighted sum is at most `C √(C_K/n) · x/L`; "first let `b` be arbitrarily
large with `h, K` fixed; then let the even integer `h` be arbitrarily large, choosing its new
sufficient fixed `K` each time". -/
theorem primeStatisticFixedClassAt_of {d H b : ℕ} {q : ℝ} (hW : WeightedPrimeBound d H b q)
    (hV : VarianceBound q) (hS : SlotBounded d) (hP : PrimeMassBound) :
    PrimeStatisticFixedClassAt d H b := by
  intro ε hε Φ hΦ1 hΦ2 hΦ3 hΦ4 η hη
  have hΦ : IsCutoff Φ := ⟨hΦ1, hΦ2, hΦ3, hΦ4⟩
  obtain ⟨R, hR0, hR⟩ := hΦ.exists_upper
  obtain ⟨c₀, hc₀def⟩ : ∃ c₀ : ℝ, c₀ = min (ε / 4) (1 / 8) := ⟨_, rfl⟩
  have hc₀ : 0 < c₀ := by
    rw [hc₀def]
    exact lt_min (by linarith) (by norm_num)
  have hc₀ε : c₀ < ε / 2 := by
    rw [hc₀def]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hc₀4 : c₀ < 1 / 4 := by
    rw [hc₀def]
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨C₁, -, h₀, hW'⟩ := hW ε hε c₀ hc₀ hc₀ε hc₀4 Φ hΦ
  obtain ⟨BS, hBS⟩ := hS ε hε R hR0
  obtain ⟨CP, hCP⟩ := hP Φ hΦ
  obtain ⟨h, hh₀, hheven, hhsmall⟩ :=
    exists_even_small C₁ (c₀ := c₀) (show (0 : ℝ) < η / 4 by linarith) h₀
  obtain ⟨K₀, hK₀⟩ := hW' h hh₀ hheven
  obtain ⟨CK, hCK⟩ := hV Φ hΦ K₀
  obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = max BS 0 := ⟨_, rfl⟩
  have hBS' : BS ≤ B := by
    rw [hBdef]
    exact le_max_left _ _
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = B ^ 2 * max CP 0 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    exact mul_nonneg (sq_nonneg _) (le_max_right _ _)
  have h32 : (0 : ℝ) < 32 * (D + 1) := by linarith
  have hη2pos : (0 : ℝ) < η ^ 2 := pow_pos hη 2
  obtain ⟨η₂, hη₂def⟩ : ∃ η₂ : ℝ, η₂ = η ^ 2 / (32 * (D + 1)) := ⟨_, rfl⟩
  have hη₂ : 0 < η₂ := by
    rw [hη₂def]
    exact div_pos hη2pos h32
  obtain ⟨n, hn⟩ : ∃ n : ℕ, 32 * (D + 1) * max CK 0 / η ^ 2 + 1 ≤ (n : ℝ) :=
    ⟨⌈32 * (D + 1) * max CK 0 / η ^ 2 + 1⌉₊, Nat.le_ceil _⟩
  have hquot : (0 : ℝ) ≤ 32 * (D + 1) * max CK 0 / η ^ 2 :=
    div_nonneg (mul_nonneg h32.le (le_max_right _ _)) hη2pos.le
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hn0 : 0 < n := by exact_mod_cast hnpos
  obtain ⟨𝔄, h𝔄⟩ := exists_arraysDisjoint n K₀
  have hev1 : ∀ᶠ x : ℝ in atTop, ∀ a : Fin n, ∀ S : Fin d → Finset ℕ, SlotsAdmissible ε x S →
      |shiftSum Φ x (fun v => v.Prime ∧ v ≡ b [MOD H])
          (fun u => normWeight q (𝔄 a) x u * ((slotCount S u : ℝ) - slotMass S))| ≤
        (C₁ * Real.exp (-(h : ℝ)) * ((4 * (h : ℝ) + 3) / c₀) + η / 4) * (x / Real.log x) :=
    eventually_all.mpr fun a => hK₀ K₀ le_rfl (𝔄 a) (η / 4) (by linarith)
  filter_upwards [hev1, hCK n hn0 𝔄 h𝔄 η₂ hη₂, hBS, hCP, eventually_gt_atTop (1 : ℝ)]
    with x hx1 hx2 hx3 hx4 hx5 S hS
  have hx0 : 0 < x := by linarith
  have hX : 0 < x / Real.log x := div_pos hx0 (Real.log_pos hx5)
  obtain ⟨hmass, hcount⟩ := hx3 S hS
  rw [classPrimeSum_eq_shiftSum]
  have hg : ∀ u : ℕ, Φ ((u : ℝ) / x) ≠ 0 → |(slotCount S u : ℝ) - slotMass S| ≤ B := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hΦ.range_of_ne_zero hR hx0 hu
    have hc := hcount u hu1 hu2
    have hc0 : (0 : ℝ) ≤ (slotCount S u : ℝ) := Nat.cast_nonneg _
    have hm0 : 0 ≤ slotMass S := slotMass_nonneg S
    rw [abs_le]
    constructor <;> linarith
  have hE : ∀ a : Fin n, |shiftSum Φ x (fun v => v.Prime ∧ v ≡ b [MOD H])
      (fun u => normWeight q (𝔄 a) x u * ((slotCount S u : ℝ) - slotMass S))| ≤
        η / 2 * (x / Real.log x) := by
    intro a
    refine (hx1 a S hS).trans (mul_le_mul_of_nonneg_right ?_ hX.le)
    linarith
  -- the arithmetic of the choice of `n`
  have hV0 : 0 ≤ (CK / (n : ℝ) + η₂) * (x / Real.log x) :=
    le_trans (shiftSum_nonneg hΦ.nonneg _ fun u => by
      unfold arrayDeviation
      exact sq_nonneg _) hx2
  have ha0 : 0 ≤ CK / (n : ℝ) + η₂ := by
    have h0 : 0 * (x / Real.log x) ≤ (CK / (n : ℝ) + η₂) * (x / Real.log x) := by
      rw [zero_mul]
      exact hV0
    exact le_of_mul_le_mul_right h0 hX
  have hCKn : max CK 0 / (n : ℝ) ≤ η₂ := by
    have h1 : 32 * (D + 1) * max CK 0 / η ^ 2 ≤ (n : ℝ) := by linarith
    rw [div_le_iff₀ hη2pos] at h1
    rw [hη₂def, div_le_iff₀ hnpos, div_mul_eq_mul_div, le_div_iff₀ h32]
    calc max CK 0 * (32 * (D + 1)) = 32 * (D + 1) * max CK 0 := by ring
      _ ≤ (n : ℝ) * η ^ 2 := h1
      _ = η ^ 2 * (n : ℝ) := by ring
  have hV2 : CK / (n : ℝ) + η₂ ≤ 2 * η₂ := by
    have h1 : CK / (n : ℝ) ≤ max CK 0 / (n : ℝ) :=
      div_le_div_of_nonneg_right (le_max_left _ _) hnpos.le
    linarith
  have hb : B ^ 2 * CP ≤ D := by
    rw [hDdef]
    exact mul_le_mul_of_nonneg_left (le_max_left _ _) (sq_nonneg B)
  have hd : 2 * η₂ * D ≤ η ^ 2 / 16 := by
    have e : 2 * η₂ * D = 2 * η ^ 2 * D / (32 * (D + 1)) := by
      rw [hη₂def]
      ring
    rw [e, div_le_iff₀ h32]
    nlinarith [hη2pos, hD0]
  have key : (CK / (n : ℝ) + η₂) * (B ^ 2 * CP) ≤ η ^ 2 / 16 :=
    calc (CK / (n : ℝ) + η₂) * (B ^ 2 * CP) ≤ (CK / (n : ℝ) + η₂) * D :=
          mul_le_mul_of_nonneg_left hb ha0
      _ ≤ 2 * η₂ * D := mul_le_mul_of_nonneg_right hV2 hD0
      _ ≤ η ^ 2 / 16 := hd
  have hVT : (CK / (n : ℝ) + η₂) * (x / Real.log x) * (B ^ 2 * (CP * (x / Real.log x))) ≤
      (η / 4 * (x / Real.log x)) ^ 2 :=
    calc (CK / (n : ℝ) + η₂) * (x / Real.log x) * (B ^ 2 * (CP * (x / Real.log x)))
        = (CK / (n : ℝ) + η₂) * (B ^ 2 * CP) * (x / Real.log x) ^ 2 := by ring
      _ ≤ η ^ 2 / 16 * (x / Real.log x) ^ 2 := mul_le_mul_of_nonneg_right key (sq_nonneg _)
      _ = (η / 4 * (x / Real.log x)) ^ 2 := by ring
  have hfinal := deweight_core hR hx0 hΦ.nonneg (P := fun v => v.Prime ∧ v ≡ b [MOD H])
    (fun v hv => hv.1) hn0 (fun a => normWeight q (𝔄 a) x)
    (fun u => (slotCount S u : ℝ) - slotMass S) (T := η / 4 * (x / Real.log x))
    (mul_nonneg (by linarith) hX.le) hg hE hx2 hx4 hVT
  refine hfinal.trans ?_
  have e : η / 2 * (x / Real.log x) + η / 4 * (x / Real.log x) =
      3 / 4 * η * (x / Real.log x) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right (by linarith) hX.le

/-! ### The reduction -/

/-- **[P] §7 with a fixed class, assembled**: the leaves of `ExtractionLeaves d H b q q₀` give
`PrimeExtractionReductionAt d H b`. The inputs of the reduction are used as follows: Theorem 3.1
in coefficient form and [P] Lemma 5.2 in the Type II step, Theorem 6.1^{𝔅} in the allocation step,
the rough counts in the stripping and coin steps, the block sieve in the presieve and variance
steps, Mertens' two estimates throughout. Siegel–Walfisz is passed only to the leaf `primeMass`
(a Chebyshev bound for the number of primes); the proved leaf `primeMassBound` does not use it. -/
theorem primeExtractionReductionAt_of {d H b : ℕ} {q q₀ : ℝ}
    (L : ExtractionLeaves d H b q q₀) : PrimeExtractionReductionAt d H b := by
  intro hII h52 h61 hSW hM1 hM2 hR hB
  have hslot := L.slotBounded hM1
  have hcore := coreBounded_of hslot (L.weightBounded hM1)
  have hmodel := L.modelBounds hM1
  have hpre := L.presieve (L.progressionSlots hM1) (L.progressionUnit hM1) hmodel hslot hB hM2
    hM1
  have hret := L.allocation h61 (L.candidateAdmissible hM1) (L.coreGrowth hM2)
    L.allocationIdentity L.squareExceptions hcore
  have hcomp := compositeVanishing_of (L.proxy hII h52 hslot hcore hM2) (L.strip hR hM2 hM1)
    (L.coin hR hM1 hM2) hret hcore
  have hweighted := weightedPrimeBound_of hpre hcomp L.sifted hmodel hcore
  have hvar := L.variance (L.progressionUnitOne hM1) hmodel (L.modelVariance hmodel) hB hM2 hM1
  exact primeStatisticFixedClassAt_of hweighted hvar hslot (L.primeMass hSW)

/-- The reduction for every modulus and every reduced class, for `d` slots. -/
theorem primeExtractionReduction_of {d : ℕ} {q q₀ : ℝ}
    (L : ∀ H b : ℕ, 0 < H → b.Coprime H → ExtractionLeaves d H b q q₀) :
    PrimeExtractionReduction d :=
  fun H b hH hb => primeExtractionReductionAt_of (L H b hH hb)

/-- **The target**: the leaves for one slot, at one choice of the dampings `q, q₀`, give
`PrimeExtractionReduction 1`. -/
theorem primeExtractionReduction_one_of {q q₀ : ℝ}
    (L : ∀ H b : ℕ, 0 < H → b.Coprime H → ExtractionLeaves 1 H b q q₀) :
    PrimeExtractionReduction 1 :=
  primeExtractionReduction_of L

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
