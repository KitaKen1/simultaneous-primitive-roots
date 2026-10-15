module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.DivisorModelTruncation
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.OmegaMomentProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.PartialMarkedBoundProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.WeightBound

/-!
# Lemma `lem:divisor-model`: the truncated divisor model

`divisorModel : MertensReciprocal → OmegaMoment → DivisorModel` (`[P-06:0565–0633]`).

Let `𝒬` be the set of the primes of the inert bands and of the active groups (`markPrimes`) and
`S_n = {p ∈ 𝒬 : p ∣ n}`.

* `hMarks_congr`, `hMarks_eq_prod_filter`: `H_marks(n)` depends on `n` only through `S_n`, so
  `H_marks(n) = F(S_n)` with `F(S) = H_marks(∏_{p ∈ S} p)`.
* The model is `truncatedModel 𝒬 h F` (`EndpointProof/DivisorModelTruncation.lean`) with
  `h = ⌊L^{.01}⌋`: `A_{∏D} = a(D)` for `D ⊆ 𝒬`, `|D| ≤ h`, where `a` is the Möbius inverse of `F`,
  i.e. the full divisor expansion of `H_marks` cut at `h` primes.
* Support: every prime of `𝒬` is `≤ exp(L^{.46})` (`le_exp_of_mem_markPrimes`), so
  `∏D ≤ exp(h L^{.46}) ≤ exp(L^{.47})`: `Csupp = 1`.
* `|H_marks| ≤ H_b = max(1, C_𝒲) L^{C₁}` (`Extraction.arrayWeightBounded_all` from Mertens, and
  `partialMarkedBound`). Mass: `∑ |A_e|/e ≤ H_b ∏_{p ∈ 𝒬} (1 + 2/p) ≤ H_b exp(2 V_𝒬)` and
  `V_𝒬 ≤ K (log 2 + 1) + 2 C₀ v₊ log L`: `C₈ = log(max(1, C_𝒲) e^{2K(log 2 + 1)}) + C₁ + 4 C₀ v₊`.
* Error: `e^h |H_marks(n) - H_0(n)|² ≤ (9e)^{|S_n|} H_b² ≤ (9e)^{ω_tot(n)} H_b²`
  (`card_filter_markPrimes_le`), (cor:omega-moment) with `B = 9e`, and
  `L^{2C₁ + C₂ + N} ≤ e^h` for large `x`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open Filter
open scoped Topology

noncomputable section

/-! ### The marked primes -/

theorem mem_markPrimes_iff {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) (𝔊 : ActiveGroups) {p : ℕ} :
    p ∈ markPrimes 𝔞 x 𝔊 ↔
      (∃ i : Fin K, p ∈ bandPrimes (𝔞.exponent i) x) ∨ ∃ g : 𝔊.Index, p ∈ 𝔊.group g := by
  unfold markPrimes ActiveGroups.allPrimes
  rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion]
  constructor
  · rintro (⟨i, -, hi⟩ | ⟨g, -, hg⟩)
    · exact Or.inl ⟨i, hi⟩
    · exact Or.inr ⟨g, hg⟩
  · rintro (⟨i, hi⟩ | ⟨g, hg⟩)
    · exact Or.inl ⟨i, Finset.mem_univ i, hi⟩
    · exact Or.inr ⟨g, Finset.mem_univ g, hg⟩

/-- The marked primes are primes. -/
theorem prime_of_mem_markPrimes {K : ℕ} (𝔞 : MarkingArray K) {x : ℝ}
    {P : ActiveGroupConstants} {𝔊 : ActiveGroups} (h : 𝔊.Admissible P x) {p : ℕ}
    (hp : p ∈ markPrimes 𝔞 x 𝔊) : p.Prime := by
  rcases (mem_markPrimes_iff 𝔞 x 𝔊).mp hp with ⟨i, hi⟩ | ⟨g, hg⟩
  · exact (mem_bandPrimes.mp hi).1
  · exact h.prime g p hg

/-- The marked primes are at most `exp(L^{.46})` ("all at most `exp(L^{.46})`",
`[P-06:0597–0598]`), once `2 ≤ L^{.26}`. -/
theorem le_exp_of_mem_markPrimes {K : ℕ} (𝔞 : MarkingArray K) {x : ℝ}
    {P : ActiveGroupConstants} {𝔊 : ActiveGroups} (h : 𝔊.Admissible P x)
    (hL1 : 1 ≤ Real.log x) (h26 : 2 ≤ Real.log x ^ (0.26 : ℝ)) {p : ℕ}
    (hp : p ∈ markPrimes 𝔞 x 𝔊) : (p : ℝ) ≤ Real.exp (Real.log x ^ (0.46 : ℝ)) := by
  have hL0 : 0 < Real.log x := by linarith
  rcases (mem_markPrimes_iff 𝔞 x 𝔊).mp hp with ⟨i, hi⟩ | ⟨g, hg⟩
  · have h1 := (mem_bandPrimes.mp hi).2.2
    refine h1.trans (Real.exp_le_exp.mpr ?_)
    have ha : Real.log x ^ 𝔞.exponent i ≤ Real.log x ^ (1 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hL1 (𝔞.lt_fifth i).le
    have h5 : 0 ≤ Real.log x ^ (1 / 5 : ℝ) := Real.rpow_nonneg hL0.le _
    have hsplit : Real.log x ^ (0.26 : ℝ) * Real.log x ^ (1 / 5 : ℝ) =
        Real.log x ^ (0.46 : ℝ) := by
      have e : (0.26 : ℝ) + 1 / 5 = 0.46 := by norm_num
      rw [← Real.rpow_add hL0, e]
    calc 2 * Real.log x ^ 𝔞.exponent i ≤ 2 * Real.log x ^ (1 / 5 : ℝ) := by linarith
      _ ≤ Real.log x ^ (0.26 : ℝ) * Real.log x ^ (1 / 5 : ℝ) :=
          mul_le_mul_of_nonneg_right h26 h5
      _ = Real.log x ^ (0.46 : ℝ) := hsplit
  · rcases g with i | j
    · have h1 := (h.small_range i p hg).2
      refine h1.trans (Real.exp_le_exp.mpr ?_)
      exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    · exact (h.big_range j p hg).2

/-- `|S_n| ≤ ω_tot(n)`: the number of marked primes dividing `n` is at most the number of hits in
all active and inert groups. -/
theorem card_filter_markPrimes_le {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) (𝔊 : ActiveGroups)
    (hdisj : ∀ g g' : 𝔊.Index, g ≠ g' → Disjoint (𝔊.group g) (𝔊.group g')) (n : ℕ) :
    ((markPrimes 𝔞 x 𝔊).filter fun p => p ∣ n).card ≤ totalMarkHits 𝔞 x 𝔊 n := by
  unfold markPrimes totalMarkHits
  rw [Finset.filter_union, Finset.filter_biUnion, totalHits_eq_primeHits_allPrimes 𝔊 hdisj]
  unfold primeHits
  exact (Finset.card_union_le _ _).trans (add_le_add Finset.card_biUnion_le le_rfl)

/-- `V_𝒬 ≤ ∑_i V_i + V_𝒫`. -/
theorem reciprocalMass_markPrimes_le {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) (𝔊 : ActiveGroups) :
    reciprocalMass (markPrimes 𝔞 x 𝔊) ≤
      ∑ i : Fin K, reciprocalMass (bandPrimes (𝔞.exponent i) x) +
        reciprocalMass 𝔊.allPrimes := by
  unfold markPrimes
  exact (reciprocalMass_union_le _ _).trans
    (add_le_add (reciprocalMass_biUnion_le _ _) le_rfl)

/-! ### `H_marks` depends only on the marked primes dividing `n` -/

/-- `H_marks(n) = H_marks(n')` when `n` and `n'` are divisible by the same marked primes. -/
theorem hMarks_congr (q q₀ : ℝ) {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ) (𝔊 : ActiveGroups)
    (t : 𝔊.Index → ℕ) (test : ((g : 𝔊.Index) → Fin (t g) → ℕ) → ℂ) (U : Finset 𝔊.Index)
    {n n' : ℕ} (h : ∀ p ∈ markPrimes 𝔞 x 𝔊, (p ∣ n ↔ p ∣ n')) :
    hMarks q q₀ 𝔞 x 𝔊 t test U n = hMarks q q₀ 𝔞 x 𝔊 t test U n' := by
  have hband : ∀ i : Fin K, (bandPrimes (𝔞.exponent i) x).filter (fun p => p ∣ n) =
      (bandPrimes (𝔞.exponent i) x).filter (fun p => p ∣ n') := fun i =>
    Finset.filter_congr fun p hp => h p ((mem_markPrimes_iff 𝔞 x 𝔊).mpr (Or.inl ⟨i, hp⟩))
  have hgroup : ∀ g : 𝔊.Index, (𝔊.group g).filter (fun p => p ∣ n) =
      (𝔊.group g).filter (fun p => p ∣ n') := fun g =>
    Finset.filter_congr fun p hp => h p ((mem_markPrimes_iff 𝔞 x 𝔊).mpr (Or.inr ⟨g, hp⟩))
  have hW : markedWeight q 𝔞 x n = markedWeight q 𝔞 x n' := by
    unfold markedWeight markFactor primeHits
    exact Finset.prod_congr rfl fun i _ => by rw [hband i]
  have htot : 𝔊.totalHits n = 𝔊.totalHits n' := by
    unfold ActiveGroups.totalHits primeHits
    exact Finset.sum_congr rfl fun g _ => by rw [hgroup g]
  have hlists : partialLists 𝔊 t U n = partialLists 𝔊 t U n' := by
    unfold partialLists
    refine congrArg (fun T : (g : 𝔊.Index) → Finset (Fin (t g) → ℕ) => Fintype.piFinset T) ?_
    funext g
    rw [hgroup g]
  unfold hMarks partialWeight
  rw [hW, htot, hlists]

/-- `H_marks(n) = H_marks(∏_{p ∈ 𝒬, p ∣ n} p)`. -/
theorem hMarks_eq_prod_filter (q q₀ : ℝ) {K : ℕ} (𝔞 : MarkingArray K) (x : ℝ)
    (𝔊 : ActiveGroups) (t : 𝔊.Index → ℕ) (test : ((g : 𝔊.Index) → Fin (t g) → ℕ) → ℂ)
    (U : Finset 𝔊.Index) (hprime : ∀ p ∈ markPrimes 𝔞 x 𝔊, p.Prime) (n : ℕ) :
    hMarks q q₀ 𝔞 x 𝔊 t test U n =
      hMarks q q₀ 𝔞 x 𝔊 t test U (∏ p ∈ (markPrimes 𝔞 x 𝔊).filter (fun p => p ∣ n), p) :=
  hMarks_congr q q₀ 𝔞 x 𝔊 t test U fun _ hp => (dvd_prod_filter_dvd_iff hprime n hp).symm

/-! ### The tail of the truncation -/

/-- `L^c ≤ e^h` for `h = ⌊L^{.01}⌋`, once `L^{.01} ≥ 2` and `log L ≤ L^{.01} / (2(|c| + 1))`. -/
theorem rpow_le_exp_one_pow_floor {L c : ℝ} (hL1 : 1 ≤ L) (h01 : 2 ≤ L ^ (0.01 : ℝ))
    (hLL : Real.log L ≤ 1 / (2 * (|c| + 1)) * L ^ (0.01 : ℝ)) :
    L ^ c ≤ Real.exp 1 ^ ⌊L ^ (0.01 : ℝ)⌋₊ := by
  have hL0 : 0 < L := by linarith
  have hLL0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hc1 : 0 < 2 * (|c| + 1) := by
    have h := abs_nonneg c
    linarith
  have h1 : Real.log L ≤ L ^ (0.01 : ℝ) / (2 * (|c| + 1)) := by
    rw [← one_div_mul_eq_div]
    exact hLL
  have h3 : Real.log L * (2 * (|c| + 1)) ≤ L ^ (0.01 : ℝ) := (le_div_iff₀ hc1).mp h1
  have h2 : Real.log L * |c| ≤ L ^ (0.01 : ℝ) / 2 := by linarith
  have hh : L ^ (0.01 : ℝ) / 2 ≤ (⌊L ^ (0.01 : ℝ)⌋₊ : ℝ) := by
    have h4 : L ^ (0.01 : ℝ) < (⌊L ^ (0.01 : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have h5 : Real.log L * c ≤ Real.log L * |c| :=
    mul_le_mul_of_nonneg_left (le_abs_self c) hLL0
  rw [← Real.exp_nat_mul, Real.rpow_def_of_pos hL0]
  refine Real.exp_le_exp.mpr ?_
  linarith

/-! ### The statement -/

/-- **Lemma `lem:divisor-model`** (`[P-06:0565–0633]`): the truncated divisor model of the marked
weight, from Mertens' estimate (the band masses) and (cor:omega-moment). -/
theorem divisorModel : MertensReciprocal → OmegaMoment → DivisorModel := by
  intro hM hOM q q₀ hq hq1 hq₀ hq₀1 K 𝔞 P m'
  obtain ⟨CW, hCW⟩ := Extraction.arrayWeightBounded_all hM q hq hq1 K
  obtain ⟨xW, hxW⟩ := Filter.eventually_atTop.mp (hCW 𝔞)
  obtain ⟨C₁, x₁, hC₁⟩ := partialMarkedBound P q₀ hq₀ hq₀1 m'
  obtain ⟨Y₀, hY₀⟩ := Extraction.dyadicPrimeMass_of_mertensReciprocal hM 1 one_pos
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hβ : (1 : ℝ) ≤ 9 * Real.exp 1 := by linarith
  obtain ⟨C₂, M₂, x₂, hOM'⟩ := hOM K 𝔞 P (9 * Real.exp 1) hβ
  -- the constants
  have hCW1 : (1 : ℝ) ≤ max 1 CW := le_max_left _ _
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨Bc, hBc⟩ : ∃ Bc : ℝ,
      Bc = max 1 CW * Real.exp (2 * ((K : ℝ) * (Real.log 2 + 1))) := ⟨_, rfl⟩
  have hBc1 : 1 ≤ Bc := by
    rw [hBc]
    have h1 : (1 : ℝ) ≤ Real.exp (2 * ((K : ℝ) * (Real.log 2 + 1))) :=
      Real.one_le_exp (mul_nonneg zero_le_two (mul_nonneg (Nat.cast_nonneg K) (by linarith)))
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ max 1 CW * Real.exp (2 * ((K : ℝ) * (Real.log 2 + 1))) :=
          mul_le_mul hCW1 h1 zero_le_one (zero_le_one.trans hCW1)
  have hBc0 : 0 < Bc := lt_of_lt_of_le one_pos hBc1
  refine ⟨1, Real.log Bc + (C₁ + 4 * P.C₀ * P.vhi), fun N _ => ?_⟩
  -- the thresholds
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = C₁ + C₁ + C₂ + N := ⟨_, rfl⟩
  have hε : 0 < 1 / (2 * (|c| + 1)) := by
    have h := abs_nonneg c
    exact one_div_pos.mpr (by linarith)
  have hpowL : ∀ r : ℝ, 0 < r → ∀ b : ℝ, ∀ᶠ x : ℝ in atTop, b ≤ Real.log x ^ r :=
    fun r hr b => ((tendsto_rpow_atTop hr).comp Real.tendsto_log_atTop).eventually_ge_atTop b
  have hbands : ∀ᶠ x : ℝ in atTop, ∀ i : Fin K, Y₀ ≤ Real.log x ^ 𝔞.exponent i := by
    refine Filter.eventually_all.mpr fun i => ?_
    have hpos : (0 : ℝ) < 𝔞.exponent i := lt_trans (by norm_num) (𝔞.gt_tenth i)
    exact ((tendsto_rpow_atTop hpos).comp Real.tendsto_log_atTop).eventually_ge_atTop Y₀
  have hLLo : ∀ᶠ x : ℝ in atTop, ‖Real.log (Real.log x)‖ ≤
      1 / (2 * (|c| + 1)) * ‖Real.log x ^ (0.01 : ℝ)‖ :=
    Real.tendsto_log_atTop.eventually
      ((isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.01)).def hε)
  have hev : ∀ᶠ x : ℝ in atTop, (∀ i : Fin K, Y₀ ≤ Real.log x ^ 𝔞.exponent i) ∧
      Real.exp 1 ≤ Real.log x ∧ 2 ≤ Real.log x ^ (0.26 : ℝ) ∧ 2 ≤ Real.log x ^ (0.01 : ℝ) ∧
      ‖Real.log (Real.log x)‖ ≤ 1 / (2 * (|c| + 1)) * ‖Real.log x ^ (0.01 : ℝ)‖ := by
    filter_upwards [hbands, Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 1),
      hpowL 0.26 (by norm_num) 2, hpowL 0.01 (by norm_num) 2, hLLo] with x a1 a2 a3 a4 a5
    exact ⟨a1, a2, a3, a4, a5⟩
  obtain ⟨x₃, hx₃⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max 1 CW ^ 2 * |M₂|, max (max xW x₁) (max x₂ x₃),
    fun x hx 𝔊 h𝔊 t ht test htest U => ?_⟩
  have hxW' : xW ≤ x := ((le_max_left _ _).trans (le_max_left _ _)).trans hx
  have hxx₁ : x₁ ≤ x := ((le_max_right _ _).trans (le_max_left _ _)).trans hx
  have hxx₂ : x₂ ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxx₃ : x₃ ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  obtain ⟨hY, hLe, h26, h01, hLLn⟩ := hx₃ x hxx₃
  have hL1 : 1 ≤ Real.log x := by linarith
  have hL0 : 0 < Real.log x := by linarith
  have hLL1 : 1 ≤ Real.log (Real.log x) := (Real.le_log_iff_exp_le hL0).mpr hLe
  have hLL0 : 0 ≤ Real.log (Real.log x) := by linarith
  have hp01 : 0 ≤ Real.log x ^ (0.01 : ℝ) := Real.rpow_nonneg hL0.le _
  have h46 : 0 ≤ Real.log x ^ (0.46 : ℝ) := Real.rpow_nonneg hL0.le _
  have hLC₁ : 0 < Real.log x ^ C₁ := Real.rpow_pos_of_pos hL0 _
  -- the model
  obtain ⟨𝒬, h𝒬def⟩ : ∃ 𝒬 : Finset ℕ, 𝒬 = markPrimes 𝔞 x 𝔊 := ⟨_, rfl⟩
  obtain ⟨h, hhdef⟩ : ∃ h : ℕ, h = ⌊Real.log x ^ (0.01 : ℝ)⌋₊ := ⟨_, rfl⟩
  obtain ⟨F, hFdef⟩ : ∃ F : Finset ℕ → ℂ,
      ∀ S, F S = hMarks q q₀ 𝔞 x 𝔊 t test U (∏ p ∈ S, p) :=
    ⟨fun S => hMarks q q₀ 𝔞 x 𝔊 t test U (∏ p ∈ S, p), fun _ => rfl⟩
  have hprimeM : ∀ p ∈ markPrimes 𝔞 x 𝔊, p.Prime := fun p hp =>
    prime_of_mem_markPrimes 𝔞 h𝔊 hp
  have h𝒬prime : ∀ p ∈ 𝒬, p.Prime := by
    rw [h𝒬def]
    exact hprimeM
  have h𝒬le : ∀ p ∈ 𝒬, (p : ℝ) ≤ Real.exp (Real.log x ^ (0.46 : ℝ)) := by
    rw [h𝒬def]
    exact fun p hp => le_exp_of_mem_markPrimes 𝔞 h𝔊 hL1 h26 hp
  -- the pointwise bound for `H_marks`
  obtain ⟨Hb, hHbdef⟩ : ∃ Hb : ℝ, Hb = max 1 CW * Real.log x ^ C₁ := ⟨_, rfl⟩
  have hHb0 : 0 ≤ Hb := by
    rw [hHbdef]
    exact mul_nonneg (zero_le_one.trans hCW1) hLC₁.le
  have hHM : ∀ n : ℕ, ‖hMarks q q₀ 𝔞 x 𝔊 t test U n‖ ≤ Hb := by
    intro n
    have hW : |markedWeight q 𝔞 x n| ≤ CW := hxW x hxW' n
    have hP : ‖partialWeight 𝔊 q₀ t test U n‖ ≤ Real.log x ^ C₁ :=
      hC₁ x hxx₁ 𝔊 h𝔊 t ht test htest U n
    unfold hMarks
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hHbdef]
    exact mul_le_mul (hW.trans (le_max_right _ _)) hP (norm_nonneg _) (zero_le_one.trans hCW1)
  have hFb : ∀ D ⊆ 𝒬, ‖F D‖ ≤ Hb := fun D _ => by
    rw [hFdef D]
    exact hHM _
  -- the size of the divisors
  have hhle : (h : ℝ) ≤ Real.log x ^ (0.01 : ℝ) := by
    rw [hhdef]
    exact Nat.floor_le hp01
  have hsize : ∀ D ⊆ 𝒬, D.card ≤ h →
      ((∏ p ∈ D, p : ℕ) : ℝ) ≤ Real.exp (Real.log x ^ (0.47 : ℝ)) := by
    intro D hD hcard
    have hexp1 : (1 : ℝ) ≤ Real.exp (Real.log x ^ (0.46 : ℝ)) := Real.one_le_exp h46
    have hsplit : Real.log x ^ (0.01 : ℝ) * Real.log x ^ (0.46 : ℝ) =
        Real.log x ^ (0.47 : ℝ) := by
      have e : (0.01 : ℝ) + 0.46 = 0.47 := by norm_num
      rw [← Real.rpow_add hL0, e]
    rw [Nat.cast_prod]
    calc ∏ p ∈ D, (p : ℝ) ≤ ∏ _p ∈ D, Real.exp (Real.log x ^ (0.46 : ℝ)) :=
          Finset.prod_le_prod (fun p _ => Nat.cast_nonneg p) (fun p hp => h𝒬le p (hD hp))
      _ = Real.exp (Real.log x ^ (0.46 : ℝ)) ^ D.card := Finset.prod_const _
      _ ≤ Real.exp (Real.log x ^ (0.46 : ℝ)) ^ h := pow_le_pow_right₀ hexp1 hcard
      _ = Real.exp ((h : ℝ) * Real.log x ^ (0.46 : ℝ)) := (Real.exp_nat_mul _ h).symm
      _ ≤ Real.exp (Real.log x ^ (0.47 : ℝ)) := by
          refine Real.exp_le_exp.mpr ?_
          rw [← hsplit]
          exact mul_le_mul_of_nonneg_right hhle h46
  -- the reciprocal mass of the marked primes
  have hband : ∀ i : Fin K,
      reciprocalMass (bandPrimes (𝔞.exponent i) x) ≤ Real.log 2 + 1 := by
    intro i
    have h1 := hY₀ (Real.log x ^ 𝔞.exponent i) (hY i) (bandPrimes (𝔞.exponent i) x)
      (fun p hp => mem_bandPrimes.mp hp)
      (fun p hpp hlo hhi => mem_bandPrimes.mpr ⟨hpp, hlo.le, hhi.le⟩)
    have h2 := (abs_le.mp h1).2
    linarith
  have hgroups : ((Finset.univ : Finset (Fin 𝔊.numSmall ⊕ Fin 𝔊.numBig)).card : ℝ) ≤
      2 * P.C₀ * Real.log (Real.log x) := by
    rw [Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Nat.cast_add]
    linarith [h𝔊.numSmall_le, h𝔊.numBig_le]
  have hVP : reciprocalMass 𝔊.allPrimes ≤ 2 * P.C₀ * Real.log (Real.log x) * P.vhi := by
    rw [reciprocalMass_allPrimes 𝔊 h𝔊.disjoint]
    calc ∑ g : 𝔊.Index, reciprocalMass (𝔊.group g) ≤ ∑ _g : 𝔊.Index, P.vhi :=
          Finset.sum_le_sum fun g _ => h𝔊.mass_le g
      _ = ((Finset.univ : Finset 𝔊.Index).card : ℝ) * P.vhi := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * P.C₀ * Real.log (Real.log x) * P.vhi :=
          mul_le_mul_of_nonneg_right hgroups P.vhi_pos.le
  have hVbands : ∑ i : Fin K, reciprocalMass (bandPrimes (𝔞.exponent i) x) ≤
      (K : ℝ) * (Real.log 2 + 1) :=
    calc ∑ i : Fin K, reciprocalMass (bandPrimes (𝔞.exponent i) x)
        ≤ ∑ _i : Fin K, (Real.log 2 + 1) := Finset.sum_le_sum fun i _ => hband i
      _ = (K : ℝ) * (Real.log 2 + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hVQ : reciprocalMass 𝒬 ≤
      (K : ℝ) * (Real.log 2 + 1) + 2 * P.C₀ * Real.log (Real.log x) * P.vhi := by
    rw [h𝒬def]
    exact (reciprocalMass_markPrimes_le 𝔞 x 𝔊).trans (add_le_add hVbands hVP)
  have hmass : Hb * ∏ p ∈ 𝒬, (1 + 2 / (p : ℝ)) ≤
      Real.log x ^ (Real.log Bc + (C₁ + 4 * P.C₀ * P.vhi)) := by
    have hexp : Real.exp (2 * ((K : ℝ) * (Real.log 2 + 1) +
          2 * P.C₀ * Real.log (Real.log x) * P.vhi)) =
        Real.exp (2 * ((K : ℝ) * (Real.log 2 + 1))) * Real.log x ^ (4 * P.C₀ * P.vhi) := by
      rw [Real.rpow_def_of_pos hL0, ← Real.exp_add]
      congr 1
      ring
    have hBcpow : Bc ≤ Real.log x ^ Real.log Bc := by
      rw [Real.rpow_def_of_pos hL0]
      calc Bc = Real.exp (Real.log Bc) := (Real.exp_log hBc0).symm
        _ ≤ Real.exp (Real.log (Real.log x) * Real.log Bc) :=
            Real.exp_le_exp.mpr (le_mul_of_one_le_left (Real.log_nonneg hBc1) hLL1)
    calc Hb * ∏ p ∈ 𝒬, (1 + 2 / (p : ℝ))
        ≤ Hb * Real.exp (2 * reciprocalMass 𝒬) :=
          mul_le_mul_of_nonneg_left (prod_one_add_two_div_le_exp 𝒬) hHb0
      _ ≤ Hb * Real.exp (2 * ((K : ℝ) * (Real.log 2 + 1) +
            2 * P.C₀ * Real.log (Real.log x) * P.vhi)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hHb0
      _ = Bc * (Real.log x ^ C₁ * Real.log x ^ (4 * P.C₀ * P.vhi)) := by
          rw [hexp, hHbdef, hBc]
          ring
      _ ≤ Real.log x ^ Real.log Bc * (Real.log x ^ C₁ * Real.log x ^ (4 * P.C₀ * P.vhi)) :=
          mul_le_mul_of_nonneg_right hBcpow
            (mul_nonneg hLC₁.le (Real.rpow_nonneg hL0.le _))
      _ = Real.log x ^ (Real.log Bc + (C₁ + 4 * P.C₀ * P.vhi)) := by
          rw [Real.rpow_add hL0, Real.rpow_add hL0]
  -- the tail of the truncation
  have htail : Real.log x ^ c ≤ Real.exp 1 ^ h := by
    rw [hhdef]
    refine rpow_le_exp_one_pow_floor hL1 h01 ?_
    have h5 := hLLn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hLL0, abs_of_nonneg hp01] at h5
    exact h5
  refine ⟨truncatedModel 𝒬 h F, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- the size of the support
    intro e he
    obtain ⟨D, hD𝒬, hDcard, hDe⟩ := exists_of_truncatedModel_ne_zero he
    rw [← hDe, one_mul]
    exact ⟨Finset.prod_pos fun p hp => (h𝒬prime p (hD𝒬 hp)).pos, hsize D hD𝒬 hDcard⟩
  · -- the prime divisors
    intro e he p hp hpe
    obtain ⟨D, hD𝒬, -, hDe⟩ := exists_of_truncatedModel_ne_zero he
    rw [← hDe] at hpe
    have hpD : p ∈ D := mem_of_prime_dvd_prod_primes (fun r hr => h𝒬prime r (hD𝒬 hr)) hp hpe
    rw [← h𝒬def]
    exact hD𝒬 hpD
  · -- the mass
    exact (sum_norm_truncatedModel_div_le h hFb _).trans hmass
  · -- the error
    intro R hR
    have hR0 : 0 < R := by linarith
    have hpt : ∀ n ∈ natIcc R (2 * R),
        Real.exp 1 ^ h *
            ‖hMarks q q₀ 𝔞 x 𝔊 t test U n - divisorSum (truncatedModel 𝒬 h F) n‖ ^ 2 ≤
          (9 * Real.exp 1) ^ totalMarkHits 𝔞 x 𝔊 n * Hb ^ 2 := by
      intro n hn
      have hn0 : n ≠ 0 := by
        intro h0
        have h1 := ((mem_natIcc (by linarith : (0 : ℝ) ≤ 2 * R)).mp hn).1
        rw [h0, Nat.cast_zero] at h1
        linarith
      have hH : hMarks q q₀ 𝔞 x 𝔊 t test U n = F (𝒬.filter fun p => p ∣ n) := by
        rw [hFdef, h𝒬def]
        exact hMarks_eq_prod_filter q q₀ 𝔞 x 𝔊 t test U hprimeM n
      have h1 := pow_mul_normSq_sub_divisorSum_truncatedModel_le h𝒬prime h F hHb0
        (by linarith : (1 : ℝ) ≤ Real.exp 1) hFb hn0
      rw [← hH] at h1
      have hcard : (𝒬.filter fun p => p ∣ n).card ≤ totalMarkHits 𝔞 x 𝔊 n := by
        rw [h𝒬def]
        exact card_filter_markPrimes_le 𝔞 x 𝔊 h𝔊.disjoint n
      exact h1.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hβ hcard) (sq_nonneg _))
    obtain ⟨Sg, hSg⟩ : ∃ Sg : ℝ, Sg = ∑ n ∈ natIcc R (2 * R),
        ‖hMarks q q₀ 𝔞 x 𝔊 t test U n - divisorSum (truncatedModel 𝒬 h F) n‖ ^ 2 := ⟨_, rfl⟩
    rw [← hSg]
    have hsum : Real.exp 1 ^ h * Sg ≤ Hb ^ 2 * (M₂ * R * Real.log x ^ C₂) := by
      rw [hSg, Finset.mul_sum]
      calc ∑ n ∈ natIcc R (2 * R), Real.exp 1 ^ h *
            ‖hMarks q q₀ 𝔞 x 𝔊 t test U n - divisorSum (truncatedModel 𝒬 h F) n‖ ^ 2
          ≤ ∑ n ∈ natIcc R (2 * R), (9 * Real.exp 1) ^ totalMarkHits 𝔞 x 𝔊 n * Hb ^ 2 :=
            Finset.sum_le_sum hpt
        _ = (∑ n ∈ natIcc R (2 * R), (9 * Real.exp 1) ^ totalMarkHits 𝔞 x 𝔊 n) * Hb ^ 2 :=
            (Finset.sum_mul _ _ _).symm
        _ ≤ M₂ * R * Real.log x ^ C₂ * Hb ^ 2 :=
            mul_le_mul_of_nonneg_right (hOM' x hxx₂ 𝔊 h𝔊 R hR) (sq_nonneg _)
        _ = Hb ^ 2 * (M₂ * R * Real.log x ^ C₂) := mul_comm _ _
    have hM₂ : M₂ * R * Real.log x ^ C₂ ≤ |M₂| * R * Real.log x ^ C₂ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self M₂) hR0.le)
        (Real.rpow_nonneg hL0.le _)
    have hpowc : Real.log x ^ C₁ * Real.log x ^ C₁ * Real.log x ^ C₂ =
        Real.log x ^ c * Real.log x ^ (-N) := by
      rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_add hL0, hc]
      congr 1
      ring
    have hfin : Real.exp 1 ^ h * Sg ≤
        Real.exp 1 ^ h * (max 1 CW ^ 2 * |M₂| * R * Real.log x ^ (-N)) :=
      calc Real.exp 1 ^ h * Sg ≤ Hb ^ 2 * (M₂ * R * Real.log x ^ C₂) := hsum
        _ ≤ Hb ^ 2 * (|M₂| * R * Real.log x ^ C₂) :=
            mul_le_mul_of_nonneg_left hM₂ (sq_nonneg _)
        _ = max 1 CW ^ 2 * |M₂| * R *
              (Real.log x ^ C₁ * Real.log x ^ C₁ * Real.log x ^ C₂) := by
            rw [hHbdef]
            ring
        _ = max 1 CW ^ 2 * |M₂| * R * (Real.log x ^ c * Real.log x ^ (-N)) := by rw [hpowc]
        _ ≤ max 1 CW ^ 2 * |M₂| * R * (Real.exp 1 ^ h * Real.log x ^ (-N)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right htail (Real.rpow_nonneg hL0.le _))
              (mul_nonneg (mul_nonneg (sq_nonneg _) (abs_nonneg _)) hR0.le)
        _ = Real.exp 1 ^ h * (max 1 CW ^ 2 * |M₂| * R * Real.log x ^ (-N)) := by ring
    exact le_of_mul_le_mul_left hfin (pow_pos (Real.exp_pos 1) h)

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
