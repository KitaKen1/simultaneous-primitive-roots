module

public import SimultaneousPrimitiveRoots.Artin.FixedDensity
public import SimultaneousPrimitiveRoots.Hooley.GRHMain

/-!
# Artin's conjecture with density, from the GRH splitting estimate (dyadic form)

For `a ≥ 2` not a square, assume the GRH-strength splitting estimate `GRHSplittingBoundUpTo a C`
(Hooley's input; it follows from GRH for the Kummer fields `ℚ(ζ_q, a^{1/q})`, `q > a` prime).
Then the primes `p ∈ (x, 2x]` with primitive root `a` have a positive density:

`primeCount {a} x / (x / log x) → δ_a > 0`  (`exists_tendsto_primitiveRoot_density`).

The argument fixes `Y` first:

* the primes free of power-residue obstructions at the primes `q ≤ Y` have a density `d(Y)`
  (unconditional Chebotarev, `exists_tendsto_residueFreePrimes`);
* the primitive-root primes lie between these and these minus the exceptions at `q > Y`, which
  number at most `(C / Y + o(1)) x / log x` (Hooley's three ranges, `exists_exception_error`);
* `d(Y)` decreases to `δ_a = inf_Y d(Y)`, and letting `Y → ∞` squeezes the ratio to `δ_a`.

Positivity comes from the lower bound `positiveDyadicLowerBound_of_grhSplittingUpTo` for `{a}`.
Only Kummer fields of prime degree `q > a` enter the hypothesis; the small primes `q ≤ Y` are
handled by Chebotarev for one fixed field.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Artin

open Filter
open scoped Topology
noncomputable section
open Classical

/-- The primes `≤ Y`. -/
def primesUpTo (Y : ℕ) : Finset ℕ := (Finset.range (Y + 1)).filter Nat.Prime

theorem mem_primesUpTo {Y q : ℕ} : q ∈ primesUpTo Y ↔ q.Prime ∧ q ≤ Y := by
  simp only [primesUpTo, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  exact and_comm

theorem mem_goodPrimes_singleton {a p : ℕ} {x : ℝ} :
    p ∈ goodPrimes {a} x ↔ p ∈ Finset.range (⌊2 * x⌋₊ + 1) ∧
      (x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧ p.Prime ∧ PrimitiveRootMod a p) := by
  simp only [goodPrimes, Finset.mem_filter, SimultaneousAt, Finset.mem_singleton, forall_eq]

/-- Primitive-root primes avoid every power-residue obstruction. -/
theorem goodPrimes_subset_residueFree (a : ℕ) {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    (x : ℝ) : goodPrimes {a} x ⊆ residueFreePrimes a S x := by
  intro p hp
  obtain ⟨hr, hx1, hx2, hpp, hprim⟩ := mem_goodPrimes_singleton.mp hp
  obtain ⟨_, htests⟩ := (primitiveRootMod_iff_prime_tests hpp).mp hprim
  exact Finset.mem_filter.mpr ⟨hr, hpp, hx1, hx2, fun q hq ⟨hqp, hpow⟩ =>
    htests q (hS q hq) hqp hpow⟩

/-- A residue-free prime (for the primes `≤ Y`) which is not a primitive-root prime is an
exception in one of Hooley's three ranges. -/
theorem residueFree_subset {a : ℕ} (ha : 2 ≤ a) {Y : ℕ} {x : ℝ} (hx : 3 ≤ x)
    (hax : (a : ℝ) ≤ x) :
    residueFreePrimes a (primesUpTo Y) x ⊆
      goodPrimes {a} x ∪ (smallOrderAt {a} x ∪ grhRangeExceptions {a} Y x ∪
        windowExceptions x) := by
  intro p hp
  obtain ⟨hprange, hpprime, hpx, hp2x, hres⟩ := Finset.mem_filter.mp hp
  by_cases hprim : PrimitiveRootMod a p
  · exact Finset.mem_union_left _
      (mem_goodPrimes_singleton.mpr ⟨hprange, hpx, hp2x, hpprime, hprim⟩)
  apply Finset.mem_union_right
  have hpa_lt : a < p := by exact_mod_cast lt_of_le_of_lt hax hpx
  have hpa : ¬ p ∣ a := Nat.not_dvd_of_pos_of_lt (by omega) hpa_lt
  obtain ⟨q, hq, hqp, hpow⟩ := exists_prime_obstruction hpprime hpa hprim
  have hqY : Y < q := by
    by_contra hle
    exact hres q (mem_primesUpTo.mpr ⟨hq, by omega⟩) ⟨hqp, hpow⟩
  have hp3 : 3 < p := by
    have hcast : (3 : ℝ) < (p : ℝ) := hx.trans_lt hpx
    exact_mod_cast hcast
  by_cases h1 : q ≤ grhCutoff x
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨a, Finset.mem_singleton_self a, Finset.mem_biUnion.mpr ⟨q, ?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hqY, h1⟩, hq⟩
    · exact Finset.mem_filter.mpr ⟨hprange, hpprime, hpx, hp2x, hpa, hqp, hpow⟩
  · by_cases h2 : q ≤ orderCutoff x
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, h2⟩, hq⟩, ?_⟩
      exact Finset.mem_filter.mpr ⟨hprange, hpprime, hqp⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨a, Finset.mem_singleton_self a, Finset.mem_filter.mpr ⟨hprange, hpprime, hpx, ?_⟩⟩
      have hjpos : 1 ≤ (p - 1) / q := Nat.div_pos (Nat.le_of_dvd (by omega) hqp) hq.pos
      have hjle := quotient_le_smallOrderCutoff (by linarith) hp2x (by omega : orderCutoff x < q)
      exact dvd_smallOrderProduct_of_pow_eq_one ha hjpos hjle hpow

theorem admissible_singleton {a : ℕ} (ha : 2 ≤ a) (hsq : ¬ IsSquare a) : Admissible {a} := by
  refine ⟨Finset.singleton_nonempty a, fun b hb => by rw [Finset.mem_singleton.mp hb]; exact ha,
    fun B hB hodd => ?_⟩
  rcases Finset.subset_singleton_iff.mp hB with rfl | rfl
  · simp at hodd
  · simpa using hsq

/-- **The density of primes with primitive root `a` exists and is positive** (dyadic form),
under the GRH-strength splitting estimate for `a`. -/
theorem exists_tendsto_primitiveRoot_density {a : ℕ} (ha : 2 ≤ a) (hsq : ¬ IsSquare a)
    {C : ℝ} (hC : 0 ≤ C) (hGRH : GRHSplittingBoundUpTo a C) :
    ∃ δ : ℝ, 0 < δ ∧
      Tendsto (fun x : ℝ => primeCount {a} x / (x / Real.log x)) atTop (𝓝 δ) := by
  -- the residue-free densities `d Y`
  have hex : ∀ Y : ℕ, ∃ d : ℝ, Tendsto (fun x : ℝ =>
      ((residueFreePrimes a (primesUpTo Y) x).card : ℝ) / (x / Real.log x)) atTop (𝓝 d) :=
    fun Y => exists_tendsto_residueFreePrimes (by omega) fun q hq => (mem_primesUpTo.mp hq).1
  choose d hd using hex
  have hscale : ∀ᶠ x : ℝ in atTop, 0 < x / Real.log x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (by linarith) (Real.log_pos hx)
  have hd0 : ∀ Y, 0 ≤ d Y := fun Y =>
    ge_of_tendsto (hd Y) (by
      filter_upwards [hscale] with x hx
      exact div_nonneg (Nat.cast_nonneg _) hx.le)
  have hanti : Antitone d := by
    intro Y Y' hYY'
    refine le_of_tendsto_of_tendsto (hd Y') (hd Y) ?_
    filter_upwards [hscale] with x hx
    apply div_le_div_of_nonneg_right _ hx.le
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro p hp
    obtain ⟨hr, hpp, hx1, hx2, hres⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨hr, hpp, hx1, hx2, fun q hq => hres q ?_⟩
    obtain ⟨hqp, hqY⟩ := mem_primesUpTo.mp hq
    exact mem_primesUpTo.mpr ⟨hqp, hqY.trans hYY'⟩
  -- `d Y` decreases to `δ = inf d`
  have hbdd : BddBelow (Set.range d) := ⟨0, by rintro _ ⟨Y, rfl⟩; exact hd0 Y⟩
  set δ := ⨅ Y, d Y with hδdef
  have hdδ : Tendsto d atTop (𝓝 δ) := tendsto_atTop_ciInf hanti hbdd
  have hδle : ∀ Y, δ ≤ d Y := fun Y => ciInf_le hbdd Y
  -- positivity from the lower bound for `{a}`
  obtain ⟨c, hc, x₀, hx₀, hlow⟩ :=
    positiveDyadicLowerBound_of_grhSplittingUpTo (admissible_singleton ha hsq) hC
      (fun b hb => by rw [Finset.mem_singleton.mp hb]; exact hGRH)
  have hfc : ∀ᶠ x : ℝ in atTop, c ≤ primeCount {a} x / (x / Real.log x) := by
    filter_upwards [eventually_ge_atTop x₀, hscale] with x hx hxs
    rw [le_div_iff₀ hxs]
    exact hlow x hx
  obtain ⟨ε, hε, hexc⟩ := exists_exception_error ({a} : Finset ℕ) hC
  have hf_tend : Tendsto (fun x : ℝ => primeCount {a} x / (x / Real.log x)) atTop (𝓝 δ) := by
    rw [tendsto_order]
    constructor
    · -- lower bound
      intro l hl
      set η := (δ - l) / 4 with hη
      have hη0 : 0 < η := by rw [hη]; linarith
      obtain ⟨Y, hY⟩ := exists_nat_gt (max (C / η) (a : ℝ))
      have hYa : a ≤ Y := by
        have : (a : ℝ) < Y := (le_max_right _ _).trans_lt hY
        exact_mod_cast this.le
      have hY1 : 1 ≤ Y := by omega
      have hYpos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
      have hCY : C / Y < η := by
        rw [div_lt_iff₀ hYpos]
        have h1 : C / η < Y := (le_max_left _ _).trans_lt hY
        rw [div_lt_iff₀ hη0] at h1
        linarith
      have hexcY := hexc Y hY1 (fun b hb => by rw [Finset.mem_singleton.mp hb]; exact hYa)
        (fun b hb => by rw [Finset.mem_singleton.mp hb]; exact ha)
        (fun b hb => by rw [Finset.mem_singleton.mp hb]; exact hGRH)
      have hratio := (hd Y).eventually (lt_mem_nhds (show d Y - η < d Y by linarith))
      have hεsmall := hε.eventually (gt_mem_nhds hη0)
      filter_upwards [hexcY, hratio, hεsmall, hscale, eventually_ge_atTop (3 : ℝ),
        eventually_ge_atTop (a : ℝ)] with x hxe hxr hxε hxs hx3 hxa
      have hsub := residueFree_subset (Y := Y) ha hx3 hxa
      have hcard : ((residueFreePrimes a (primesUpTo Y) x).card : ℝ) ≤
          (goodPrimes {a} x).card + ((smallOrderAt {a} x).card +
            (grhRangeExceptions {a} Y x).card + (windowExceptions x).card) := by
        have h1 := Finset.card_le_card hsub
        have h2 := Finset.card_union_le (goodPrimes {a} x)
          (smallOrderAt {a} x ∪ grhRangeExceptions {a} Y x ∪ windowExceptions x)
        have h3 := Finset.card_union_le (smallOrderAt {a} x ∪ grhRangeExceptions {a} Y x)
          (windowExceptions x)
        have h4 := Finset.card_union_le (smallOrderAt {a} x) (grhRangeExceptions {a} Y x)
        have hnat : (residueFreePrimes a (primesUpTo Y) x).card ≤ (goodPrimes {a} x).card +
            ((smallOrderAt {a} x).card + (grhRangeExceptions {a} Y x).card +
              (windowExceptions x).card) := by omega
        exact_mod_cast hnat
      have hxe' : ((smallOrderAt {a} x).card : ℝ) + (grhRangeExceptions {a} Y x).card +
          (windowExceptions x).card ≤ (x / Real.log x) * (C / Y + ε x) := by
        simpa using hxe
      have hpc : primeCount {a} x = (goodPrimes {a} x).card := rfl
      rw [hpc, lt_div_iff₀ hxs]
      have hr' := (lt_div_iff₀ hxs).mp hxr
      have hδY := hδle Y
      have hεx : ε x < η := hxε
      nlinarith
    · -- upper bound
      intro u hu
      obtain ⟨Y, hY⟩ := (hdδ.eventually (gt_mem_nhds hu)).exists
      have hratio := (hd Y).eventually (gt_mem_nhds hY)
      filter_upwards [hratio, hscale] with x hxr hxs
      have hpc : primeCount {a} x = (goodPrimes {a} x).card := rfl
      refine lt_of_le_of_lt ?_ hxr
      rw [hpc]
      apply div_le_div_of_nonneg_right _ hxs.le
      exact Nat.cast_le.mpr (Finset.card_le_card (goodPrimes_subset_residueFree a
        (fun q hq => (mem_primesUpTo.mp hq).1) x))
  exact ⟨δ, lt_of_lt_of_le hc (ge_of_tendsto hf_tend hfc), hf_tend⟩

end

end SimultaneousPrimitiveRoots.Artin
