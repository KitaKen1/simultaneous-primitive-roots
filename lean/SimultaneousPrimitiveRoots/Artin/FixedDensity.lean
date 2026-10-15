module

public import SimultaneousPrimitiveRoots.Artin.RadicalField
public import SimultaneousPrimitiveRoots.Hooley.ResiduePrimes

/-!
# Primes avoiding finitely many power-residue conditions have a density

For `a ≥ 1` and a finite set `S` of primes, let `residueFreePrimes a S x` be the primes
`p ∈ (x, 2x]` such that for no `q ∈ S` both `q ∣ p - 1` and `a^((p-1)/q) ≡ 1 (mod p)`.
Then

`#residueFreePrimes a S x / (x / log x) → δ(a, S)`  (`exists_tendsto_residueFreePrimes`),

unconditionally. Proof: for `p` past a finite exceptional set, `p` is residue-free iff its
Frobenius class in `Gal(RadicalField a S / ℚ)` consists of automorphisms fixing the roots of no
`X^q - a` (`mem_goodClasses_iff`), and Tau Ceti's Chebotarev density theorem counts each class.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Artin

open Filter NumberField IsDedekindDomain TauCeti Polynomial
open scoped NumberField Topology
noncomputable section
open Classical

/-- The primes `p ∈ (x, 2x]` at which `a` is a `q`-th power residue with `q ∣ p - 1` for no
`q ∈ S`. -/
def residueFreePrimes (a : ℕ) (S : Finset ℕ) (x : ℝ) : Finset ℕ :=
  (Finset.range (⌊2 * x⌋₊ + 1)).filter fun p =>
    p.Prime ∧ x < (p : ℝ) ∧ (p : ℝ) ≤ 2 * x ∧
      ∀ q ∈ S, ¬ (q ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / q) = 1)

/-- Automorphisms fixing the roots of no `X^q - a`, `q ∈ S`. -/
def GoodAut (a : ℕ) (S : Finset ℕ) (σ : RadicalField a S ≃ₐ[ℚ] RadicalField a S) : Prop :=
  ∀ q ∈ S, ¬ FixesRadical a q σ

/-- Conjugacy classes consisting of good automorphisms. -/
def goodClasses (a : ℕ) (S : Finset ℕ) :
    Finset (ConjClasses (RadicalField a S ≃ₐ[ℚ] RadicalField a S)) :=
  Finset.univ.filter fun C => ∀ σ ∈ C.carrier, GoodAut a S σ

theorem goodAut_conj {a : ℕ} {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    {σ : RadicalField a S ≃ₐ[ℚ] RadicalField a S} (τ : RadicalField a S ≃ₐ[ℚ] RadicalField a S)
    (h : GoodAut a S σ) : GoodAut a S (τ * σ * τ⁻¹) :=
  fun q hq hfix => h q hq ((fixesRadical_conj_iff a (hS q hq).pos σ τ).mp hfix)

/-- Past this bound, primes are unramified in `RadicalField a S` and prime to `a` and to `S`. -/
def exceptionalBound (a : ℕ) (S : Finset ℕ) : ℕ :=
  a + S.sup id +
    (Chebotarev.ramifiedPrimes ℚ (RadicalField a S)).sup fun 𝔭 => Ideal.absNorm 𝔭.asIdeal

/-- **The Frobenius class decides residue-freeness** (past the exceptional bound). -/
theorem mem_goodClasses_iff {a : ℕ} (ha : 0 < a) {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    (𝔭 : HeightOneSpectrum (𝓞 ℚ)) (h𝔭 : exceptionalBound a S < Ideal.absNorm 𝔭.asIdeal) :
    (∃ C ∈ goodClasses a S, 𝔭 ∈ Chebotarev.frobeniusPrimeSet ℚ (RadicalField a S) C) ↔
      ∀ q ∈ S, ¬ (q ∣ Ideal.absNorm 𝔭.asIdeal - 1 ∧
        (a : ZMod (Ideal.absNorm 𝔭.asIdeal)) ^ ((Ideal.absNorm 𝔭.asIdeal - 1) / q) = 1) := by
  set p := Ideal.absNorm 𝔭.asIdeal with hpdef
  have hunram : 𝔭 ∉ Chebotarev.ramifiedPrimes ℚ (RadicalField a S) := by
    intro hmem
    have := Finset.le_sup (f := fun 𝔭 : HeightOneSpectrum (𝓞 ℚ) => Ideal.absNorm 𝔭.asIdeal) hmem
    unfold exceptionalBound at h𝔭
    omega
  have hpa : ¬ p ∣ a := by
    unfold exceptionalBound at h𝔭
    exact Nat.not_dvd_of_pos_of_lt ha (by omega)
  have hpq : ∀ q ∈ S, p ≠ q := by
    intro q hq hpqe
    have := Finset.le_sup (f := id) hq
    unfold exceptionalBound at h𝔭
    simp only [id_eq] at this
    omega
  obtain ⟨C₀, hC₀, huniq⟩ := Chebotarev.existsUnique_mem_frobeniusPrimeSet hunram
  obtain ⟨σ, rfl⟩ := ConjClasses.mk_surjective C₀
  obtain ⟨Q, hQ⟩ := Chebotarev.exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk hC₀
  have : Q.1.IsPrime := Q.2.1
  have : Q.1.LiesOver 𝔭.asIdeal := Q.2.2
  have hchar : ∀ q ∈ S, FixesRadical a q σ ↔
      (q ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / q) = 1) := fun q hq =>
    fixesRadical_iff_powerResidue a hS hq 𝔭 Q.1 hQ hpa (hpq q hq)
  constructor
  · rintro ⟨C, hC, h𝔭C⟩ q hq hres
    have hCeq : C = ConjClasses.mk σ := huniq C h𝔭C
    have hgood := (Finset.mem_filter.mp hC).2 σ (by rw [hCeq]; exact ConjClasses.mem_carrier_mk)
    exact hgood q hq ((hchar q hq).mpr hres)
  · intro hres
    refine ⟨ConjClasses.mk σ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hC₀⟩
    intro σ' hσ'
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj] at hσ'
    obtain ⟨c, hc⟩ := isConj_iff.mp hσ'.symm
    rw [← hc]
    exact goodAut_conj hS c (fun q hq hfix => hres q hq ((hchar q hq).mp hfix))

/-- For `x` past the exceptional bound, the residue-free primes are counted by the Frobenius
classes of good automorphisms. -/
theorem residueFreePrimes_card_eq {a : ℕ} (ha : 0 < a) {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    {x : ℝ} (hx : (exceptionalBound a S : ℝ) ≤ x) :
    ((residueFreePrimes a S x).card : ℝ) = ∑ C ∈ goodClasses a S,
      ((Chebotarev.frobeniusPrimeCount ℚ (RadicalField a S) C (2 * x) : ℝ) -
        Chebotarev.frobeniusPrimeCount ℚ (RadicalField a S) C x) := by
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg _) hx
  set L := RadicalField a S
  set P := (primesLE ℚ (2 * x)).filter fun 𝔭 : HeightOneSpectrum (𝓞 ℚ) =>
    x < (Ideal.absNorm 𝔭.asIdeal : ℝ) with hP
  -- each class: the dyadic increment is the number of its primes in `P`
  have hclass : ∀ C : ConjClasses (L ≃ₐ[ℚ] L),
      ((Chebotarev.frobeniusPrimeCount ℚ L C (2 * x) : ℝ) -
        Chebotarev.frobeniusPrimeCount ℚ L C x) =
        ((P.filter (· ∈ Chebotarev.frobeniusPrimeSet ℚ L C)).card : ℝ) := by
    intro C
    rw [frobeniusPrimeCount_eq_filter_card, frobeniusPrimeCount_eq_filter_card]
    set S2 := (primesLE ℚ (2 * x)).filter (· ∈ Chebotarev.frobeniusPrimeSet ℚ L C)
    set S1 := (primesLE ℚ x).filter (· ∈ Chebotarev.frobeniusPrimeSet ℚ L C)
    have hsub : S1 ⊆ S2 := by
      intro v hv
      obtain ⟨hvle, hvC⟩ := Finset.mem_filter.mp hv
      refine Finset.mem_filter.mpr ⟨?_, hvC⟩
      rw [mem_normLE] at hvle ⊢
      linarith
    have hdiff : S2 \ S1 = P.filter (· ∈ Chebotarev.frobeniusPrimeSet ℚ L C) := by
      ext v
      simp only [S2, S1, P, Finset.mem_sdiff, Finset.mem_filter, mem_normLE, not_and]
      constructor
      · rintro ⟨⟨h2, hC⟩, h1⟩
        refine ⟨⟨h2, ?_⟩, hC⟩
        by_contra hcon
        exact h1 (not_lt.mp hcon) hC
      · rintro ⟨⟨h2, hx'⟩, hC⟩
        exact ⟨⟨h2, hC⟩, fun hle => absurd hx' (not_lt.mpr hle)⟩
    rw [← hdiff, Finset.card_sdiff_of_subset hsub, Nat.cast_sub (Finset.card_le_card hsub)]
  rw [Finset.sum_congr rfl (fun C _ => hclass C), ← Nat.cast_sum, ← Finset.card_biUnion]
  · congr 1
    -- the union of the good fibres is the set of primes mapping to residue-free primes
    have hunion : (goodClasses a S).biUnion
        (fun C => P.filter (· ∈ Chebotarev.frobeniusPrimeSet ℚ L C)) =
        P.filter fun 𝔭 => ∃ C ∈ goodClasses a S, 𝔭 ∈ Chebotarev.frobeniusPrimeSet ℚ L C := by
      ext v
      simp only [Finset.mem_biUnion, Finset.mem_filter]
      constructor
      · rintro ⟨C, hC, hvP, hvC⟩
        exact ⟨hvP, C, hC, hvC⟩
      · rintro ⟨hvP, C, hC, hvC⟩
        exact ⟨C, hC, hvP, hvC⟩
    rw [hunion]
    symm
    apply Finset.card_nbij (fun 𝔭 : HeightOneSpectrum (𝓞 ℚ) => Ideal.absNorm 𝔭.asIdeal)
    · intro v hv
      have hv' := Finset.mem_filter.mp (Finset.mem_coe.mp hv)
      obtain ⟨hvP, hgood⟩ := hv'
      obtain ⟨hvle, hvgt⟩ := Finset.mem_filter.mp hvP
      rw [mem_normLE] at hvle
      have hprime : (Ideal.absNorm v.asIdeal).Prime := by
        rw [Rat.HeightOneSpectrum.absNorm_asIdeal]
        exact Rat.HeightOneSpectrum.prime_natGenerator v
      have hB : exceptionalBound a S < Ideal.absNorm v.asIdeal := by
        have : (exceptionalBound a S : ℝ) < Ideal.absNorm v.asIdeal := lt_of_le_of_lt hx hvgt
        exact_mod_cast this
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨?_, hprime, hvgt, hvle,
        (mem_goodClasses_iff ha hS v hB).mp hgood⟩)
      exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (Nat.le_floor hvle))
    · exact absNorm_injective_rat.injOn
    · intro p hp
      obtain ⟨_, hpp, hpx, hp2x, hres⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hp)
      obtain ⟨v, hv⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq hpp
      have hB : exceptionalBound a S < Ideal.absNorm v.asIdeal := by
        rw [hv]
        have : (exceptionalBound a S : ℝ) < p := lt_of_le_of_lt hx hpx
        exact_mod_cast this
      refine ⟨v, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨by rw [mem_normLE, hv]; exact hp2x, by rw [hv]; exact hpx⟩, ?_⟩), hv⟩
      exact (mem_goodClasses_iff ha hS v hB).mpr (by rw [hv]; exact hres)
  · intro C _ D _ hCD
    rw [Function.onFun, Finset.disjoint_left]
    intro v hvC hvD
    exact Set.disjoint_left.mp (Chebotarev.disjoint_frobeniusPrimeSet hCD)
      (Finset.mem_filter.mp hvC).2 (Finset.mem_filter.mp hvD).2

/-- **Residue-free primes have a density** (unconditionally, for fixed `a ≥ 1` and a finite set
`S` of primes). -/
theorem exists_tendsto_residueFreePrimes {a : ℕ} (ha : 0 < a) {S : Finset ℕ}
    (hS : ∀ q ∈ S, q.Prime) :
    ∃ δ : ℝ, Tendsto (fun x : ℝ => ((residueFreePrimes a S x).card : ℝ) / (x / Real.log x))
      atTop (𝓝 δ) := by
  set L := RadicalField a S
  refine ⟨∑ C ∈ goodClasses a S, (Nat.card C.carrier : ℝ) / Nat.card (L ≃ₐ[ℚ] L), ?_⟩
  have h := tendsto_finsetSum (goodClasses a S) fun C _ =>
    tendsto_frobeniusPrimeCount_dyadic ℚ L C
  apply h.congr'
  filter_upwards [eventually_ge_atTop (exceptionalBound a S : ℝ)] with x hx
  rw [residueFreePrimes_card_eq ha hS hx, Finset.sum_div]

end

end SimultaneousPrimitiveRoots.Artin
