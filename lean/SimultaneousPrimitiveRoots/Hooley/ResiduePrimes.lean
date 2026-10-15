module

public import SimultaneousPrimitiveRoots.FixedChebotarevCounting
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Frobenius

/-!
# Primes in a fixed residue class from Chebotarev for `ℚ(ζ_n)`

For a fixed modulus `n` and a unit residue `u`, the primes `p ∈ (x, 2x]` with
`p ≡ u (mod n)` number at least `θ x / (φ(n) log x)` for each `θ < 1` and all large `x`.

No analytic hypothesis enters. The inputs are the Chebotarev density theorem of Tau Ceti,
applied to `ℚ(ζ_n)/ℚ`, and the Tau Ceti identification of the arithmetic Frobenius at `p`
with `p mod n`.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open Filter NumberField IsDedekindDomain TauCeti
open scoped NumberField Topology
noncomputable section
open Classical

/-- Primes `p ∈ (x, 2x]` with `p ≡ u (mod n)`. -/
def dyadicResiduePrimes (n u : ℕ) (x : ℝ) : Finset ℕ :=
  (Finset.range (⌊2 * x⌋₊ + 1)).filter fun p =>
    p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧ p ≡ u [MOD n]

/-- Primes in `(x, 2x]` lying in one of the residue classes `R` modulo `H`.
Unlike `factorCandidates`, no factorization of `p - 1` is imposed. -/
def progressionCandidates (H : ℕ) (R : Finset ℕ) (x : ℝ) : Finset ℕ :=
  (Finset.range (⌊2 * x⌋₊ + 1)).filter fun p =>
    p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧ ∃ u ∈ R, p ≡ u [MOD H]

/-- The Frobenius prime count is the cardinality of an explicit finite filter. -/
theorem frobeniusPrimeCount_eq_filter_card (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (C : ConjClasses (L ≃ₐ[K] L)) (y : ℝ) :
    Chebotarev.frobeniusPrimeCount K L C y =
      ((primesLE K y).filter (· ∈ Chebotarev.frobeniusPrimeSet K L C)).card := by
  rw [Chebotarev.frobeniusPrimeCount_eq_card]
  change Nat.card (↥{v : HeightOneSpectrum (𝓞 K) |
    v ∈ Chebotarev.frobeniusPrimeSet K L C ∧ (Ideal.absNorm v.asIdeal : ℝ) ≤ y}) = _
  rw [Nat.card_coe_set_eq]
  have hset : {v : HeightOneSpectrum (𝓞 K) |
      v ∈ Chebotarev.frobeniusPrimeSet K L C ∧ (Ideal.absNorm v.asIdeal : ℝ) ≤ y} =
      ↑((primesLE K y).filter (· ∈ Chebotarev.frobeniusPrimeSet K L C)) := by
    ext v
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, mem_normLE]
    tauto
  rw [hset, Set.ncard_coe_finset]

/-- Dyadic increments of a Frobenius count, normalized by `x / log x`, converge to the
Chebotarev density. -/
theorem tendsto_frobeniusPrimeCount_dyadic (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (C : ConjClasses (L ≃ₐ[K] L)) :
    Tendsto (fun x : ℝ =>
      ((Chebotarev.frobeniusPrimeCount K L C (2 * x) : ℝ) -
        Chebotarev.frobeniusPrimeCount K L C x) / (x / Real.log x)) atTop
      (𝓝 ((Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L))) := by
  set d : ℝ := (Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[K] L)
  set g : ℝ → ℝ := fun y =>
    (Chebotarev.frobeniusPrimeCount K L C y : ℝ) / (y / Real.log y) with hg
  have h1 : Tendsto g atTop (𝓝 d) := Chebotarev.tendsto_frobeniusPrimeCount K L C
  have h2 : Tendsto (fun x : ℝ => g (2 * x)) atTop (𝓝 d) :=
    h1.comp (Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) tendsto_id)
  have hlog : Tendsto (fun x : ℝ => Real.log 2 / Real.log x) atTop (𝓝 0) :=
    Tendsto.div_atTop tendsto_const_nhds Real.tendsto_log_atTop
  have h3 : Tendsto (fun x : ℝ => 2 / (1 + Real.log 2 / Real.log x)) atTop (𝓝 2) := by
    have h := (tendsto_const_nhds (x := (1 : ℝ))).add hlog
    rw [add_zero] at h
    have h' := (tendsto_const_nhds (x := (2 : ℝ))).div h (by norm_num : (1 : ℝ) ≠ 0)
    rw [div_one] at h'
    exact h'
  have h4 : Tendsto (fun x : ℝ => g (2 * x) * (2 / (1 + Real.log 2 / Real.log x)) - g x)
      atTop (𝓝 (d * 2 - d)) := (h2.mul h3).sub h1
  rw [show d * 2 - d = d by ring] at h4
  apply h4.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2x : Real.log (2 * x) = Real.log 2 + Real.log x :=
    Real.log_mul (by norm_num) hx0.ne'
  simp only [hg]
  rw [hl2x]
  have hden : 0 < Real.log 2 + Real.log x := by linarith
  field_simp
  ring

section Cyclotomic

variable (n : ℕ) [NeZero n] (F : Type*) [Field F] [NumberField F]
  [IsCyclotomicExtension {n} ℚ F] [IsGalois ℚ F]

/-- The automorphism of `ℚ(ζ_n)` acting by `ζ ↦ ζ ^ u`. -/
def residueAut {u : ℕ} (hu : u.Coprime n) : F ≃ₐ[ℚ] F :=
  (IsCyclotomicExtension.Rat.galEquivZMod n F).symm (ZMod.unitOfCoprime u hu)

variable {n F}

/-- A prime of `ℚ` in the Frobenius fibre of `ζ ↦ ζ ^ u` lies in the class `u mod n`,
provided it does not divide `n`. -/
theorem absNorm_modEq_of_mem_frobeniusPrimeSet {u : ℕ} (hu : u.Coprime n)
    {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : v ∈ Chebotarev.frobeniusPrimeSet ℚ F (ConjClasses.mk (residueAut n F hu)))
    (hvn : ¬ Ideal.absNorm v.asIdeal ∣ n) :
    Ideal.absNorm v.asIdeal ≡ u [MOD n] := by
  obtain ⟨Q, hQ⟩ := Chebotarev.exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk hv
  have hnm : (n : 𝓞 ℚ) ∉ v.asIdeal := by
    rwa [Rat.HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd]
  have h := (TauCeti.NumberField.isArithFrobAt_iff_galEquivZMod_eq_absNorm (F := F) v hnm Q.1
    (residueAut n F hu)).mp hQ
  simp only [residueAut, MulEquiv.apply_symm_apply, ZMod.coe_unitOfCoprime] at h
  exact ((ZMod.natCast_eq_natCast_iff _ _ _).mp h).symm

/-- The rational prime below a height-one prime of `𝓞 ℚ` determines it. -/
theorem absNorm_injective_rat :
    Function.Injective (fun v : HeightOneSpectrum (𝓞 ℚ) => Ideal.absNorm v.asIdeal) := by
  intro v w h
  apply (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective
  apply Subtype.ext
  change Rat.HeightOneSpectrum.natGenerator v = Rat.HeightOneSpectrum.natGenerator w
  simpa only [Rat.HeightOneSpectrum.absNorm_asIdeal] using h

/-- A dyadic increment of the Frobenius count of `ζ ↦ ζ ^ u` is at most the number of
primes in `(x, 2x]` congruent to `u`, up to the primes dividing `n`. -/
theorem frobeniusPrimeCount_dyadic_le {u : ℕ} (hu : u.Coprime n) (x : ℝ) (hx : 0 ≤ x) :
    (Chebotarev.frobeniusPrimeCount ℚ F (ConjClasses.mk (residueAut n F hu)) (2 * x) : ℝ) -
      Chebotarev.frobeniusPrimeCount ℚ F (ConjClasses.mk (residueAut n F hu)) x ≤
        (dyadicResiduePrimes n u x).card + n := by
  set C := ConjClasses.mk (residueAut n F hu)
  set S2 := (primesLE ℚ (2 * x)).filter (· ∈ Chebotarev.frobeniusPrimeSet ℚ F C)
  set S1 := (primesLE ℚ x).filter (· ∈ Chebotarev.frobeniusPrimeSet ℚ F C)
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
  -- Good primes map into the residue-class primes.
  have hgood : Dg.card ≤ (dyadicResiduePrimes n u x).card := by
    apply Finset.card_le_card_of_injOn (fun v => Ideal.absNorm v.asIdeal)
    · intro v hv
      have hv' := Finset.mem_filter.mp (Finset.mem_coe.mp hv)
      obtain ⟨hvD, hvn⟩ := hv'
      obtain ⟨hv2, hv1⟩ := Finset.mem_sdiff.mp hvD
      obtain ⟨hvle, hvC⟩ := Finset.mem_filter.mp hv2
      have hvgt : x < (Ideal.absNorm v.asIdeal : ℝ) := by
        by_contra hcon
        exact hv1 (Finset.mem_filter.mpr ⟨by rw [mem_normLE]; linarith, hvC⟩)
      rw [mem_normLE] at hvle
      have hprime : (Ideal.absNorm v.asIdeal).Prime := by
        rw [Rat.HeightOneSpectrum.absNorm_asIdeal]
        exact Rat.HeightOneSpectrum.prime_natGenerator v
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨?_, hprime, hvgt, hvle,
        absNorm_modEq_of_mem_frobeniusPrimeSet hu hvC hvn⟩)
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_floor hvle))
    · exact hinj.mono (fun v hv => (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).1)
  -- Primes dividing `n` contribute at most `n`.
  have hbad : Db.card ≤ n := by
    have hle : Db.card ≤ n.divisors.card := by
      apply Finset.card_le_card_of_injOn (fun v => Ideal.absNorm v.asIdeal)
      · intro v hv
        have hv' := Finset.mem_filter.mp (Finset.mem_coe.mp hv)
        exact Finset.mem_coe.mpr (Nat.mem_divisors.mpr ⟨hv'.2, NeZero.ne n⟩)
      · exact hinj.mono (fun v hv => (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).1)
    exact hle.trans (Nat.card_divisors_le_self n)
  have hD : (D.card : ℝ) ≤ (dyadicResiduePrimes n u x).card + n := by
    rw [hsplit]
    push_cast
    have h1 : (Dg.card : ℝ) ≤ (dyadicResiduePrimes n u x).card := by exact_mod_cast hgood
    have h2 : (Db.card : ℝ) ≤ n := by exact_mod_cast hbad
    linarith
  exact hD

omit [IsGalois ℚ F] in
/-- In `ℚ(ζ_n)`, every automorphism class is a singleton. -/
theorem card_conjClass_residueAut {u : ℕ} (hu : u.Coprime n) :
    Nat.card (ConjClasses.mk (residueAut n F hu)).carrier = 1 := by
  rw [Nat.card_coe_set_eq]
  apply ConjClasses.ncard_carrier_mk_of_mem_center
  rw [Subgroup.mem_center_iff]
  intro g
  apply (IsCyclotomicExtension.Rat.galEquivZMod n F).injective
  rw [map_mul, map_mul, mul_comm]

omit [IsGalois ℚ F] in
/-- The Galois group of `ℚ(ζ_n)` has `φ(n)` elements. -/
theorem card_gal_cyclotomic : Nat.card (F ≃ₐ[ℚ] F) = n.totient := by
  rw [Nat.card_congr (IsCyclotomicExtension.Rat.galEquivZMod n F).toEquiv,
    Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]

end Cyclotomic

/-- **Primes in a fixed residue class.** For fixed `n ≥ 1`, a unit residue `u` and `θ < 1`,
eventually the primes `p ∈ (x, 2x]` with `p ≡ u (mod n)` number at least
`θ (1 / φ(n)) x / log x`. -/
theorem eventually_dyadicResiduePrimes_ge {n u : ℕ} (hn : 0 < n) (hu : u.Coprime n)
    {θ : ℝ} (hθ : θ < 1) :
    ∀ᶠ x : ℝ in atTop, θ * (1 / (Nat.totient n : ℝ)) * (x / Real.log x) ≤
      ((dyadicResiduePrimes n u x).card : ℝ) := by
  have : NeZero n := ⟨hn.ne'⟩
  let F := CyclotomicField n ℚ
  have : IsCyclotomicExtension {n} ℚ F := CyclotomicField.isCyclotomicExtension n ℚ
  have : NumberField F := IsCyclotomicExtension.numberField {n} ℚ F
  have : IsGalois ℚ F := IsCyclotomicExtension.isGalois {n} ℚ F
  set C := ConjClasses.mk (residueAut n F hu)
  have hphi : (0 : ℝ) < Nat.totient n := by exact_mod_cast Nat.totient_pos.mpr hn
  set d : ℝ := 1 / (Nat.totient n : ℝ)
  have hd : 0 < d := by positivity
  have htend := tendsto_frobeniusPrimeCount_dyadic ℚ F C
  rw [card_conjClass_residueAut (n := n) (F := F) hu,
    card_gal_cyclotomic (n := n) (F := F)] at htend
  -- The finitely many primes dividing `n` are negligible.
  have hsmall : Tendsto (fun x : ℝ => (n : ℝ) / (x / Real.log x)) atTop (𝓝 0) := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have h' := h.const_mul (n : ℝ)
    rw [mul_zero] at h'
    apply h'.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    simp only [pow_one, one_mul, add_zero]
    field_simp
  have hcomb : Tendsto (fun x : ℝ =>
      ((Chebotarev.frobeniusPrimeCount ℚ F C (2 * x) : ℝ) -
        Chebotarev.frobeniusPrimeCount ℚ F C x) / (x / Real.log x) -
          (n : ℝ) / (x / Real.log x)) atTop (𝓝 (d - 0)) := by
    have h := htend.sub hsmall
    simpa [d, Nat.cast_one] using h
  rw [sub_zero] at hcomb
  have hev := hcomb.eventually (lt_mem_nhds (show θ * d < d by
    rcases le_or_gt θ 0 with h0 | h0
    · nlinarith
    · nlinarith))
  filter_upwards [hev, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hscale : 0 < x / Real.log x := div_pos hx0 (Real.log_pos hx1)
  have hcount := frobeniusPrimeCount_dyadic_le (F := F) hu x hx0.le
  have hx' : θ * d < (((Chebotarev.frobeniusPrimeCount ℚ F C (2 * x) : ℝ) -
        Chebotarev.frobeniusPrimeCount ℚ F C x) - n) / (x / Real.log x) := by
    rw [sub_div]
    exact hx
  have hlt := (lt_div_iff₀ hscale).mp hx'
  linarith

theorem progressionCandidates_eq_biUnion (H : ℕ) (R : Finset ℕ) (x : ℝ) :
    progressionCandidates H R x = R.biUnion (fun u => dyadicResiduePrimes H u x) := by
  ext p
  simp only [progressionCandidates, dyadicResiduePrimes, Finset.mem_filter,
    Finset.mem_biUnion]
  constructor
  · rintro ⟨hr, hp, hlo, hhi, u, hu, hpu⟩
    exact ⟨u, hu, hr, hp, hlo, hhi, hpu⟩
  · rintro ⟨u, hu, hr, hp, hlo, hhi, hpu⟩
    exact ⟨hr, hp, hlo, hhi, u, hu, hpu⟩

theorem progressionCandidates_card {H : ℕ} {R : Finset ℕ} (hR : ∀ u ∈ R, u < H)
    (x : ℝ) :
    (progressionCandidates H R x).card = ∑ u ∈ R, (dyadicResiduePrimes H u x).card := by
  rw [progressionCandidates_eq_biUnion, Finset.card_biUnion]
  intro u hu u' hu' hne
  rw [Function.onFun, Finset.disjoint_left]
  intro p hp hp'
  have h1 := (Finset.mem_filter.mp hp).2.2.2.2
  have h2 := (Finset.mem_filter.mp hp').2.2.2.2
  apply hne
  have huu : u ≡ u' [MOD H] := h1.symm.trans h2
  unfold Nat.ModEq at huu
  rwa [Nat.mod_eq_of_lt (hR u hu), Nat.mod_eq_of_lt (hR u' hu')] at huu

/-- **Unconditional candidate supply.** The residue classes `R` modulo a fixed `H` contain
at least `θ (|R| / φ(H)) x / log x` primes of `(x, 2x]` for every `θ < 1` and large `x`. -/
theorem progressionCandidates_supply {H : ℕ} {R : Finset ℕ} (hH : 0 < H)
    (hR : ∀ u ∈ R, u < H ∧ u.Coprime H) {θ : ℝ} (hθ : θ < 1) :
    ∀ᶠ x : ℝ in atTop, θ * ((R.card : ℝ) / Nat.totient H) * (x / Real.log x) ≤
      ((progressionCandidates H R x).card : ℝ) := by
  have hall : ∀ᶠ x : ℝ in atTop, ∀ u ∈ R,
      θ * (1 / (Nat.totient H : ℝ)) * (x / Real.log x) ≤
        ((dyadicResiduePrimes H u x).card : ℝ) :=
    (Filter.eventually_all_finset R).mpr fun u hu =>
      eventually_dyadicResiduePrimes_ge hH (hR u hu).2 hθ
  filter_upwards [hall] with x hx
  rw [progressionCandidates_card (fun u hu => (hR u hu).1)]
  push_cast
  calc θ * ((R.card : ℝ) / Nat.totient H) * (x / Real.log x)
      = ∑ _u ∈ R, θ * (1 / (Nat.totient H : ℝ)) * (x / Real.log x) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ ∑ u ∈ R, ((dyadicResiduePrimes H u x).card : ℝ) := Finset.sum_le_sum hx

end
end SimultaneousPrimitiveRoots
