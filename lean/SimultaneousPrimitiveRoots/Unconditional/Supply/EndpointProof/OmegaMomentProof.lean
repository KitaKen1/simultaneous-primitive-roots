module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof.Statements
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.DyadicMass

/-!
# (cor:omega-moment)

`omegaMoment : MertensReciprocal → OmegaMoment` (`[P-06:0621–0630]`): "For any fixed `B > 1`,
expanding `B^{ω_tot}` into squarefree divisors and counting their multiples gives
`∑_{n ≍ R} B^{ω_tot(n)} ≪ R ∏_{p in all groups} (1 + (B-1)/p) ≪ R L^{C(B)}`."

* `sum_pow_primeHits_le`: for a finite set `T` of primes and `B ≥ 1`,
  `∑_{1 ≤ n ≤ N} B^{ω_T(n)} ≤ N ∏_{p ∈ T} (1 + (B-1)/p)`. Indeed
  `B^{ω_T(n)} = ∏_{p ∈ T} (1 + (B-1) 1_{p ∣ n}) = ∑_{D ⊆ T} (B-1)^{|D|} 1_{∏D ∣ n}`, and `∏D` has
  `⌊N/∏D⌋ ≤ N/∏D` multiples in `[1, N]`. The product is `≤ exp((B-1) V_T)`
  (`prod_one_add_div_le_exp`).
* The `K` bands and the union `𝒫` of the active groups are `K + 1` sets of primes, and
  `ω_tot = ∑_i ω_i + ω_𝒫` (the active groups are pairwise disjoint,
  `totalHits_eq_primeHits_allPrimes`). No disjointness between the bands, or between the bands
  and `𝒫`, is used: `B^{∑_j f_j} ≤ ∑_j (B^{K+1})^{f_j}` (`pow_add_sum_le`; the largest `f_j` carries
  the sum).
* `V_i ≤ log 2 + 1` for large `x` (Mertens, `Extraction.dyadicPrimeMass_of_mertensReciprocal`)
  and `V_𝒫 = ∑_g V_g ≤ 2 C₀ v₊ log L`.

With `B' = B^{K+1}`: `C = (B' - 1) · 2 C₀ v₊`, `M = 2 (1 + K exp((B' - 1)(log 2 + 1)))`, and the
threshold is the one of the band masses and `x ≥ e`. The sum is over `R ≤ n ≤ 2R`, `R ≥ 1`; only
`1 ≤ n ≤ 2R` is used.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof

open Filter

noncomputable section

/-! ### One set of primes -/

/-- `B^{ω_T(n)} = ∏_{p ∈ T} (1 + (B - 1) 1_{p ∣ n})`. -/
theorem pow_primeHits_eq (T : Finset ℕ) (B : ℝ) (n : ℕ) :
    B ^ primeHits T n = ∏ p ∈ T, (1 + (B - 1) * (if p ∣ n then (1 : ℝ) else 0)) := by
  unfold primeHits
  calc B ^ (T.filter fun p => p ∣ n).card = ∏ _p ∈ T.filter (fun p => p ∣ n), B :=
        (Finset.prod_const B).symm
    _ = ∏ p ∈ T, (if p ∣ n then B else 1) := Finset.prod_filter (fun p => p ∣ n) (fun _ => B)
    _ = ∏ p ∈ T, (1 + (B - 1) * (if p ∣ n then (1 : ℝ) else 0)) :=
        Finset.prod_congr rfl fun p _ => by
          by_cases hp : p ∣ n
          · rw [if_pos hp, if_pos hp]
            ring
          · rw [if_neg hp, if_neg hp]
            ring

/-- For a set `D` of primes and `c ≥ 0`:
`∑_{1 ≤ n ≤ N} ∏_{p ∈ D} c 1_{p ∣ n} ≤ N ∏_{p ∈ D} c/p` (the integers divisible by all the primes
of `D` are the multiples of `∏D`). -/
theorem sum_prod_indicator_le {D : Finset ℕ} (hD : ∀ p ∈ D, p.Prime) {c : ℝ} (hc : 0 ≤ c)
    (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, ∏ p ∈ D, (c * (if p ∣ n then (1 : ℝ) else 0)) ≤
      (N : ℝ) * ∏ p ∈ D, (c / (p : ℝ)) := by
  have hpt : ∀ n ∈ Finset.Ioc 0 N, ∏ p ∈ D, (c * (if p ∣ n then (1 : ℝ) else 0)) ≤
      if (∏ p ∈ D, p) ∣ n then c ^ D.card else 0 := by
    intro n _
    by_cases hall : ∀ p ∈ D, p ∣ n
    · have hdvd : (∏ p ∈ D, p) ∣ n :=
        Finset.prod_primes_dvd n (fun p hp => (hD p hp).prime) hall
      rw [if_pos hdvd]
      refine le_of_eq ?_
      calc ∏ p ∈ D, (c * (if p ∣ n then (1 : ℝ) else 0)) = ∏ _p ∈ D, c :=
            Finset.prod_congr rfl fun p hp => by rw [if_pos (hall p hp), mul_one]
        _ = c ^ D.card := Finset.prod_const c
    · obtain ⟨p, hp'⟩ := not_forall.mp hall
      obtain ⟨hp, hpn⟩ := _root_.not_imp.mp hp'
      have hzero : ∏ p ∈ D, (c * (if p ∣ n then (1 : ℝ) else 0)) = 0 :=
        Finset.prod_eq_zero hp (by rw [if_neg hpn, mul_zero])
      rw [hzero]
      by_cases hdvd : (∏ p ∈ D, p) ∣ n
      · exact (pow_nonneg hc D.card).trans (le_of_eq (if_pos hdvd).symm)
      · exact le_of_eq (if_neg hdvd).symm
  calc ∑ n ∈ Finset.Ioc 0 N, ∏ p ∈ D, (c * (if p ∣ n then (1 : ℝ) else 0))
      ≤ ∑ n ∈ Finset.Ioc 0 N, (if (∏ p ∈ D, p) ∣ n then c ^ D.card else 0) :=
        Finset.sum_le_sum hpt
    _ = ∑ _n ∈ (Finset.Ioc 0 N).filter (fun n => (∏ p ∈ D, p) ∣ n), c ^ D.card :=
        (Finset.sum_filter (fun n => (∏ p ∈ D, p) ∣ n) (fun _ => c ^ D.card)).symm
    _ = (((Finset.Ioc 0 N).filter fun n => (∏ p ∈ D, p) ∣ n).card : ℝ) * c ^ D.card := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = ((N / ∏ p ∈ D, p : ℕ) : ℝ) * c ^ D.card := by
        rw [Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ ((N : ℝ) / ((∏ p ∈ D, p : ℕ) : ℝ)) * c ^ D.card :=
        mul_le_mul_of_nonneg_right Nat.cast_div_le (pow_nonneg hc _)
    _ = (N : ℝ) * ∏ p ∈ D, (c / (p : ℝ)) := by
        rw [Finset.prod_div_distrib, Finset.prod_const, Nat.cast_prod]
        ring

/-- **Expanding `B^{ω_T}` into squarefree divisors and counting their multiples**
(`[P-06:0621–0626]`): `∑_{1 ≤ n ≤ N} B^{ω_T(n)} ≤ N ∏_{p ∈ T} (1 + (B-1)/p)` for a finite set `T`
of primes and `B ≥ 1`. -/
theorem sum_pow_primeHits_le {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) {B : ℝ} (hB : 1 ≤ B)
    (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, B ^ primeHits T n ≤
      (N : ℝ) * ∏ p ∈ T, (1 + (B - 1) / (p : ℝ)) := by
  have hB0 : 0 ≤ B - 1 := by linarith
  have hD : ∀ D ∈ T.powerset,
      ∑ n ∈ Finset.Ioc 0 N, ∏ p ∈ D, ((B - 1) * (if p ∣ n then (1 : ℝ) else 0)) ≤
        (N : ℝ) * ∏ p ∈ D, ((B - 1) / (p : ℝ)) := fun D hD =>
    sum_prod_indicator_le (fun p hp => hT p (Finset.mem_powerset.mp hD hp)) hB0 N
  calc ∑ n ∈ Finset.Ioc 0 N, B ^ primeHits T n
      = ∑ n ∈ Finset.Ioc 0 N, ∑ D ∈ T.powerset,
          ∏ p ∈ D, ((B - 1) * (if p ∣ n then (1 : ℝ) else 0)) :=
        Finset.sum_congr rfl fun n _ => by rw [pow_primeHits_eq, Finset.prod_one_add]
    _ = ∑ D ∈ T.powerset, ∑ n ∈ Finset.Ioc 0 N,
          ∏ p ∈ D, ((B - 1) * (if p ∣ n then (1 : ℝ) else 0)) := Finset.sum_comm
    _ ≤ ∑ D ∈ T.powerset, (N : ℝ) * ∏ p ∈ D, ((B - 1) / (p : ℝ)) := Finset.sum_le_sum hD
    _ = (N : ℝ) * ∏ p ∈ T, (1 + (B - 1) / (p : ℝ)) := by
        rw [← Finset.mul_sum, Finset.prod_one_add]

/-- `∏_{p ∈ T} (1 + (B-1)/p) ≤ exp((B-1) V_T)`. -/
theorem prod_one_add_div_le_exp (T : Finset ℕ) {B : ℝ} (hB : 1 ≤ B) :
    ∏ p ∈ T, (1 + (B - 1) / (p : ℝ)) ≤ Real.exp ((B - 1) * reciprocalMass T) := by
  have hB0 : 0 ≤ B - 1 := by linarith
  unfold reciprocalMass
  rw [Finset.mul_sum, Real.exp_sum]
  refine Finset.prod_le_prod (fun p _ => ?_) (fun p _ => ?_)
  · have h : 0 ≤ (B - 1) / (p : ℝ) := div_nonneg hB0 (Nat.cast_nonneg p)
    linarith
  · calc 1 + (B - 1) / (p : ℝ) = (B - 1) * (1 / (p : ℝ)) + 1 := by ring
      _ ≤ Real.exp ((B - 1) * (1 / (p : ℝ))) := Real.add_one_le_exp _

/-- `∑_{1 ≤ n ≤ N} B^{ω_T(n)} ≤ N exp((B-1) V)` for a set `T` of primes of reciprocal mass
`V_T ≤ V`. -/
theorem sum_pow_primeHits_le_exp {T : Finset ℕ} (hT : ∀ p ∈ T, p.Prime) {B : ℝ} (hB : 1 ≤ B)
    (N : ℕ) {V : ℝ} (hV : reciprocalMass T ≤ V) :
    ∑ n ∈ Finset.Ioc 0 N, B ^ primeHits T n ≤ (N : ℝ) * Real.exp ((B - 1) * V) := by
  have hB0 : 0 ≤ B - 1 := by linarith
  calc ∑ n ∈ Finset.Ioc 0 N, B ^ primeHits T n
      ≤ (N : ℝ) * ∏ p ∈ T, (1 + (B - 1) / (p : ℝ)) := sum_pow_primeHits_le hT hB N
    _ ≤ (N : ℝ) * Real.exp ((B - 1) * reciprocalMass T) :=
        mul_le_mul_of_nonneg_left (prod_one_add_div_le_exp T hB) (Nat.cast_nonneg N)
    _ ≤ (N : ℝ) * Real.exp ((B - 1) * V) :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hV hB0)) (Nat.cast_nonneg N)

/-! ### Several sets of primes -/

/-- `B^{∑_j f_j} ≤ ∑_j (B^{|ι|})^{f_j}` for `B ≥ 1` and a nonempty finite index type: the largest
`f_j` carries the sum. -/
theorem pow_sum_le_sum_pow {ι : Type*} [Fintype ι] [Nonempty ι] {B : ℝ} (hB : 1 ≤ B)
    (f : ι → ℕ) : B ^ (∑ j, f j) ≤ ∑ j, (B ^ Fintype.card ι) ^ f j := by
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_max_image Finset.univ f Finset.univ_nonempty
  have h1 : ∑ j, f j ≤ Fintype.card ι * f j₀ :=
    calc ∑ j, f j ≤ ∑ _j : ι, f j₀ := Finset.sum_le_sum fun j hj => hj₀ j hj
      _ = Fintype.card ι * f j₀ := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
  have hB0 : 0 ≤ B := by linarith
  calc B ^ (∑ j, f j) ≤ B ^ (Fintype.card ι * f j₀) := pow_le_pow_right₀ hB h1
    _ = (B ^ Fintype.card ι) ^ f j₀ := pow_mul B _ _
    _ ≤ ∑ j, (B ^ Fintype.card ι) ^ f j :=
        Finset.single_le_sum (f := fun j => (B ^ Fintype.card ι) ^ f j)
          (fun j _ => pow_nonneg (pow_nonneg hB0 _) _) (Finset.mem_univ j₀)

/-- `B^{∑_{i < K} f_i + a} ≤ (B^{K+1})^a + ∑_{i < K} (B^{K+1})^{f_i}` for `B ≥ 1`. -/
theorem pow_add_sum_le {K : ℕ} {B : ℝ} (hB : 1 ≤ B) (a : ℕ) (f : Fin K → ℕ) :
    B ^ ((∑ i, f i) + a) ≤ (B ^ (K + 1)) ^ a + ∑ i, (B ^ (K + 1)) ^ f i := by
  have hcard : Fintype.card (Option (Fin K)) = K + 1 := by
    rw [Fintype.card_option, Fintype.card_fin]
  have h := pow_sum_le_sum_pow hB (fun j : Option (Fin K) => Option.elim j a f)
  have e1 : ∑ j : Option (Fin K), Option.elim j a f = a + ∑ i, f i :=
    Fintype.sum_option (fun j : Option (Fin K) => Option.elim j a f)
  have e2 : ∑ j : Option (Fin K), (B ^ (K + 1)) ^ Option.elim j a f =
      (B ^ (K + 1)) ^ a + ∑ i, (B ^ (K + 1)) ^ f i :=
    Fintype.sum_option (fun j : Option (Fin K) => (B ^ (K + 1)) ^ Option.elim j a f)
  calc B ^ ((∑ i, f i) + a) = B ^ (∑ j : Option (Fin K), Option.elim j a f) := by
        rw [e1, add_comm a]
    _ ≤ ∑ j : Option (Fin K), (B ^ Fintype.card (Option (Fin K))) ^ Option.elim j a f := h
    _ = ∑ j : Option (Fin K), (B ^ (K + 1)) ^ Option.elim j a f := by rw [hcard]
    _ = (B ^ (K + 1)) ^ a + ∑ i, (B ^ (K + 1)) ^ f i := e2

/-! ### The active groups -/

/-- For pairwise disjoint groups, `ω_P(n) = ∑_g ω_g(n)` is the number of prime divisors of `n` in
`𝒫 = ⋃_g 𝒫_g`. -/
theorem totalHits_eq_primeHits_allPrimes (𝔊 : ActiveGroups)
    (hdisj : ∀ g g' : 𝔊.Index, g ≠ g' → Disjoint (𝔊.group g) (𝔊.group g')) (n : ℕ) :
    𝔊.totalHits n = primeHits 𝔊.allPrimes n := by
  have hpd : ((Finset.univ : Finset 𝔊.Index) : Set 𝔊.Index).PairwiseDisjoint
      (fun g => (𝔊.group g).filter fun p => p ∣ n) :=
    fun g _ g' _ hgg' => Finset.disjoint_filter_filter (hdisj g g' hgg')
  unfold ActiveGroups.totalHits primeHits ActiveGroups.allPrimes
  rw [Finset.filter_biUnion, Finset.card_biUnion hpd]

/-- For pairwise disjoint groups, `V_𝒫 = ∑_g V_g`. -/
theorem reciprocalMass_allPrimes (𝔊 : ActiveGroups)
    (hdisj : ∀ g g' : 𝔊.Index, g ≠ g' → Disjoint (𝔊.group g) (𝔊.group g')) :
    reciprocalMass 𝔊.allPrimes = ∑ g : 𝔊.Index, reciprocalMass (𝔊.group g) := by
  have hpd : ((Finset.univ : Finset 𝔊.Index) : Set 𝔊.Index).PairwiseDisjoint 𝔊.group :=
    fun g _ g' _ hgg' => hdisj g g' hgg'
  unfold reciprocalMass ActiveGroups.allPrimes
  exact Finset.sum_biUnion hpd

/-! ### The statement -/

/-- **(cor:omega-moment)** (`[P-06:0621–0630]`): `∑_{R ≤ n ≤ 2R} B^{ω_tot(n)} ≤ M R L^C` for every
`R ≥ 1`, from Mertens' estimate (the band masses). -/
theorem omegaMoment : MertensReciprocal → OmegaMoment := by
  intro hM K 𝔞 P B hB
  obtain ⟨Y₀, hY₀⟩ := Extraction.dyadicPrimeMass_of_mertensReciprocal hM 1 one_pos
  have hev : ∀ᶠ x : ℝ in atTop, ∀ i : Fin K, Y₀ ≤ Real.log x ^ 𝔞.exponent i := by
    refine Filter.eventually_all.mpr fun i => ?_
    have hpos : (0 : ℝ) < 𝔞.exponent i := lt_trans (by norm_num) (𝔞.gt_tenth i)
    exact ((tendsto_rpow_atTop hpos).comp Real.tendsto_log_atTop).eventually_ge_atTop Y₀
  obtain ⟨xb, hxb⟩ := Filter.eventually_atTop.mp hev
  have hB0 : 0 ≤ B := by linarith
  have hB' : (1 : ℝ) ≤ B ^ (K + 1) := one_le_pow₀ hB
  have hB'0 : 0 ≤ B ^ (K + 1) - 1 := by linarith
  have hcb0 : 0 ≤ Real.exp ((B ^ (K + 1) - 1) * (Real.log 2 + 1)) := (Real.exp_pos _).le
  have hc₂ : 0 ≤ (B ^ (K + 1) - 1) * (2 * P.C₀ * P.vhi) :=
    mul_nonneg hB'0 (mul_nonneg (mul_nonneg zero_le_two P.C₀_pos.le) P.vhi_pos.le)
  refine ⟨(B ^ (K + 1) - 1) * (2 * P.C₀ * P.vhi),
    2 * (1 + (K : ℝ) * Real.exp ((B ^ (K + 1) - 1) * (Real.log 2 + 1))),
    max xb (Real.exp 1), fun x hx 𝔊 h R hR => ?_⟩
  have hxb' : xb ≤ x := (le_max_left _ _).trans hx
  have hxe : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hL1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hxe
  have hL : 0 < Real.log x := by linarith
  have hLc : 1 ≤ Real.log x ^ ((B ^ (K + 1) - 1) * (2 * P.C₀ * P.vhi)) :=
    Real.one_le_rpow hL1 hc₂
  -- the band masses
  have hmass : ∀ i : Fin K,
      reciprocalMass (bandPrimes (𝔞.exponent i) x) ≤ Real.log 2 + 1 := by
    intro i
    have h1 := hY₀ (Real.log x ^ 𝔞.exponent i) (hxb x hxb' i) (bandPrimes (𝔞.exponent i) x)
      (fun p hp => mem_bandPrimes.mp hp)
      (fun p hpp hlo hhi => mem_bandPrimes.mpr ⟨hpp, hlo.le, hhi.le⟩)
    have h2 := (abs_le.mp h1).2
    linarith
  have hband : ∀ i : Fin K, ∑ n ∈ Finset.Ioc 0 ⌊2 * R⌋₊,
      (B ^ (K + 1)) ^ primeHits (bandPrimes (𝔞.exponent i) x) n ≤
        (⌊2 * R⌋₊ : ℝ) * Real.exp ((B ^ (K + 1) - 1) * (Real.log 2 + 1)) := fun i =>
    sum_pow_primeHits_le_exp (fun p hp => (mem_bandPrimes.mp hp).1) hB' _ (hmass i)
  -- the active groups
  have hprimeAll : ∀ p ∈ 𝔊.allPrimes, p.Prime := by
    intro p hp
    unfold ActiveGroups.allPrimes at hp
    obtain ⟨g, -, hpg⟩ := Finset.mem_biUnion.mp hp
    exact h.prime g p hpg
  have hgroups : ((Finset.univ : Finset (Fin 𝔊.numSmall ⊕ Fin 𝔊.numBig)).card : ℝ) ≤
      2 * P.C₀ * Real.log (Real.log x) := by
    rw [Finset.card_univ, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Nat.cast_add]
    linarith [h.numSmall_le, h.numBig_le]
  have hVP : reciprocalMass 𝔊.allPrimes ≤ 2 * P.C₀ * Real.log (Real.log x) * P.vhi := by
    rw [reciprocalMass_allPrimes 𝔊 h.disjoint]
    calc ∑ g : 𝔊.Index, reciprocalMass (𝔊.group g) ≤ ∑ _g : 𝔊.Index, P.vhi :=
          Finset.sum_le_sum fun g _ => h.mass_le g
      _ = ((Finset.univ : Finset 𝔊.Index).card : ℝ) * P.vhi := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 2 * P.C₀ * Real.log (Real.log x) * P.vhi :=
          mul_le_mul_of_nonneg_right hgroups P.vhi_pos.le
  have hexp : Real.exp ((B ^ (K + 1) - 1) * (2 * P.C₀ * Real.log (Real.log x) * P.vhi)) =
      Real.log x ^ ((B ^ (K + 1) - 1) * (2 * P.C₀ * P.vhi)) := by
    rw [Real.rpow_def_of_pos hL]
    congr 1
    ring
  have hact : ∑ n ∈ Finset.Ioc 0 ⌊2 * R⌋₊, (B ^ (K + 1)) ^ primeHits 𝔊.allPrimes n ≤
      (⌊2 * R⌋₊ : ℝ) * Real.log x ^ ((B ^ (K + 1) - 1) * (2 * P.C₀ * P.vhi)) := by
    rw [← hexp]
    exact sum_pow_primeHits_le_exp hprimeAll hB' _ hVP
  -- one integer
  have hpt : ∀ n : ℕ, B ^ totalMarkHits 𝔞 x 𝔊 n ≤
      (B ^ (K + 1)) ^ primeHits 𝔊.allPrimes n +
        ∑ i : Fin K, (B ^ (K + 1)) ^ primeHits (bandPrimes (𝔞.exponent i) x) n := by
    intro n
    unfold totalMarkHits
    rw [totalHits_eq_primeHits_allPrimes 𝔊 h.disjoint]
    exact pow_add_sum_le hB _ _
  -- the range
  have hR0 : 0 < R := by linarith
  have hsub : natIcc R (2 * R) ⊆ Finset.Ioc 0 ⌊2 * R⌋₊ := by
    intro n hn
    unfold natIcc at hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
    have h3 : 0 < ⌈R⌉₊ := Nat.ceil_pos.mpr hR0
    exact Finset.mem_Ioc.mpr ⟨lt_of_lt_of_le h3 h1, h2⟩
  have hN : (⌊2 * R⌋₊ : ℝ) ≤ 2 * R := Nat.floor_le (by linarith)
  have hN0 : (0 : ℝ) ≤ (⌊2 * R⌋₊ : ℝ) := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg K
  have t1 : (⌊2 * R⌋₊ : ℝ) * Real.log x ^ ((B ^ (K + 1) - 1) * (2 * P.C₀ * P.vhi)) ≤
      2 * R * Real.log x ^ ((B ^ (K + 1) - 1) * (2 * P.C₀ * P.vhi)) :=
    mul_le_mul_of_nonneg_right hN (zero_le_one.trans hLc)
  have t2 : (K : ℝ) * ((⌊2 * R⌋₊ : ℝ) * Real.exp ((B ^ (K + 1) - 1) * (Real.log 2 + 1))) ≤
      (K : ℝ) * (2 * R * Real.exp ((B ^ (K + 1) - 1) * (Real.log 2 + 1))) *
        Real.log x ^ ((B ^ (K + 1) - 1) * (2 * P.C₀ * P.vhi)) :=
    calc (K : ℝ) * ((⌊2 * R⌋₊ : ℝ) * Real.exp ((B ^ (K + 1) - 1) * (Real.log 2 + 1)))
        ≤ (K : ℝ) * (2 * R * Real.exp ((B ^ (K + 1) - 1) * (Real.log 2 + 1))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hN hcb0) hK0
      _ ≤ (K : ℝ) * (2 * R * Real.exp ((B ^ (K + 1) - 1) * (Real.log 2 + 1))) *
            Real.log x ^ ((B ^ (K + 1) - 1) * (2 * P.C₀ * P.vhi)) :=
          le_mul_of_one_le_right
            (mul_nonneg hK0 (mul_nonneg (mul_nonneg zero_le_two hR0.le) hcb0)) hLc
  calc ∑ n ∈ natIcc R (2 * R), B ^ totalMarkHits 𝔞 x 𝔊 n
      ≤ ∑ n ∈ Finset.Ioc 0 ⌊2 * R⌋₊, B ^ totalMarkHits 𝔞 x 𝔊 n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => pow_nonneg hB0 _
    _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊2 * R⌋₊, ((B ^ (K + 1)) ^ primeHits 𝔊.allPrimes n +
          ∑ i : Fin K, (B ^ (K + 1)) ^ primeHits (bandPrimes (𝔞.exponent i) x) n) :=
        Finset.sum_le_sum fun n _ => hpt n
    _ = ∑ n ∈ Finset.Ioc 0 ⌊2 * R⌋₊, (B ^ (K + 1)) ^ primeHits 𝔊.allPrimes n +
          ∑ i : Fin K, ∑ n ∈ Finset.Ioc 0 ⌊2 * R⌋₊,
            (B ^ (K + 1)) ^ primeHits (bandPrimes (𝔞.exponent i) x) n := by
        rw [Finset.sum_add_distrib, Finset.sum_comm]
    _ ≤ (⌊2 * R⌋₊ : ℝ) * Real.log x ^ ((B ^ (K + 1) - 1) * (2 * P.C₀ * P.vhi)) +
          ∑ _i : Fin K,
            (⌊2 * R⌋₊ : ℝ) * Real.exp ((B ^ (K + 1) - 1) * (Real.log 2 + 1)) :=
        add_le_add hact (Finset.sum_le_sum fun i _ => hband i)
    _ = (⌊2 * R⌋₊ : ℝ) * Real.log x ^ ((B ^ (K + 1) - 1) * (2 * P.C₀ * P.vhi)) +
          (K : ℝ) * ((⌊2 * R⌋₊ : ℝ) * Real.exp ((B ^ (K + 1) - 1) * (Real.log 2 + 1))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ 2 * R * Real.log x ^ ((B ^ (K + 1) - 1) * (2 * P.C₀ * P.vhi)) +
          (K : ℝ) * (2 * R * Real.exp ((B ^ (K + 1) - 1) * (Real.log 2 + 1))) *
            Real.log x ^ ((B ^ (K + 1) - 1) * (2 * P.C₀ * P.vhi)) := add_le_add t1 t2
    _ = 2 * (1 + (K : ℝ) * Real.exp ((B ^ (K + 1) - 1) * (Real.log 2 + 1))) * R *
          Real.log x ^ ((B ^ (K + 1) - 1) * (2 * P.C₀ * P.vhi)) := by ring

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.EndpointProof
