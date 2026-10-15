module

public import SimultaneousPrimitiveRoots.Artin.FixedDensityInt
public import SimultaneousPrimitiveRoots.Artin.CumulativeDensity

/-!
# Artin's conjecture with density for negative bases

For `b ≥ 2`, assume the GRH-strength splitting estimate `GRHSplittingBoundUpTo b C` for the
positive integer `b`. Then the primes with primitive root `-b` have a positive density among the
primes (`negPrimitiveRoot_density_of_grhSplitting`). Nothing else is assumed of `b`; it may be a
square (`a = -4`) or a perfect power (`a = -8`).

* **Odd obstructions of `-b` are those of `b`.** For odd primes `q ∣ p - 1` (`p` odd) the
  exponent `(p - 1) / q` is even, so `(-b)^((p-1)/q) = b^((p-1)/q)`. Hooley's three exception
  ranges for `{b}` (`exists_exception_error`) bound the exceptions of `-b` at primes `q > Y`
  (`mem_exceptions_of_obstruction`).
* **The lower bound** (`exists_negPrimitiveRoot_lower`) runs Hooley's sieve in the classes
  `p ≡ 23 (mod 24)` in which every prime factor `≥ 5` of `b` is a square
  (`exists_signed_fixed_residue` with all signs `+1`). There `(2/p) = (3/p) = 1` and
  `(-1/p) = -1`, so `-b` is a nonsquare; the selector then removes the odd primes
  `q ≤ 2T² + 1` from `p - 1` exactly as for positive bases.
* **The density** follows from the squeeze of `Density.lean`, written here once abstractly
  (`exists_tendsto_of_squeeze`): the primes free of the obstructions `q ≤ Y` have a density
  `d(Y)` (Chebotarev, `exists_tendsto_residueFreePrimesInt`), and the primitive-root primes lie
  between these and these minus `(C/Y + o(1)) x / log x` exceptions. Positivity is the lower
  bound.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots.Artin

open Filter
open scoped Topology
noncomputable section

/-! ### Primitive roots for integer bases -/

/-- `p` is a prime with primitive root the integer `a` (Formal Conjectures' `S a`). -/
def IsPrimitiveRootPrimeInt (a : ℤ) (p : ℕ) : Prop := p.Prime ∧ orderOf (a : ZMod p) = p - 1

instance (a : ℤ) : DecidablePred (IsPrimitiveRootPrimeInt a) := fun p => by
  unfold IsPrimitiveRootPrimeInt
  infer_instance

/-- The primes `p ∈ (x, 2x]` with primitive root `a`. -/
def goodPrimesInt (a : ℤ) (x : ℝ) : Finset ℕ :=
  (Finset.range (⌊2 * x⌋₊ + 1)).filter fun p => IsPrimitiveRootPrimeInt a p ∧ x < (p : ℝ)

theorem goodPrimesInt_card_eq (a : ℤ) {x : ℝ} (hx : 0 ≤ x) :
    ((goodPrimesInt a x).card : ℝ) =
      (upCount (IsPrimitiveRootPrimeInt a) (2 * x) : ℝ) - upCount (IsPrimitiveRootPrimeInt a) x :=
  (upCount_dyadic _ hx).symm

/-- A unit of `𝔽_p` which is not a primitive root has a prime obstruction `q ∣ p - 1`. -/
theorem exists_prime_obstruction_zmod {p : ℕ} [hp : Fact p.Prime] {c : ZMod p} (hc : c ≠ 0)
    (h : orderOf c ≠ p - 1) : ∃ q : ℕ, q.Prime ∧ q ∣ p - 1 ∧ c ^ ((p - 1) / q) = 1 := by
  by_contra hno
  push Not at hno
  exact h (orderOf_eq_of_pow_and_pow_div_prime (by have := hp.out.two_le; omega)
    (ZMod.pow_card_sub_one_eq_one hc) hno)

/-- A primitive root has no power-residue obstruction. -/
theorem pow_ne_one_of_isPrimitiveRootPrimeInt {a : ℤ} {p q : ℕ}
    (h : IsPrimitiveRootPrimeInt a p) (hq : q.Prime) (hqp : q ∣ p - 1) :
    (a : ZMod p) ^ ((p - 1) / q) ≠ 1 := by
  obtain ⟨hp, ho⟩ := h
  have hpge := hp.two_le
  apply pow_ne_one_of_lt_orderOf
  · have := Nat.div_pos (Nat.le_of_dvd (by omega) hqp) hq.pos
    omega
  · rw [ho]
    exact Nat.div_lt_self (by omega) hq.one_lt

/-- For odd `p` and odd `q ∣ p - 1`, the exponent `(p - 1) / q` is even. -/
theorem even_div_of_odd {p q : ℕ} (hp : Odd p) (hq : Odd q) (hqp : q ∣ p - 1) :
    Even ((p - 1) / q) := by
  have hev : Even (p - 1) := by
    obtain ⟨k, hk⟩ := hp
    exact ⟨k, by omega⟩
  rw [← Nat.mul_div_cancel' hqp] at hev
  rcases Nat.even_mul.mp hev with h | h
  · exact absurd h (Nat.not_even_iff_odd.mpr hq)
  · exact h

/-- At an odd obstruction prime, `-c` and `c` have the same power. -/
theorem neg_pow_div_eq {p q : ℕ} (hp : Odd p) (hq : Odd q) (hqp : q ∣ p - 1) (c : ZMod p) :
    (-c) ^ ((p - 1) / q) = c ^ ((p - 1) / q) :=
  (even_div_of_odd hp hq hqp).neg_pow c

/-! ### Hooley's three ranges for one positive base -/

/-- **Hooley's classification** for one base `b`: an obstruction prime `q > Y` of `b` at
`p ∈ (x, 2x]` puts `p` in one of the three exception ranges. -/
theorem mem_exceptions_of_obstruction {b : ℕ} (hb : 2 ≤ b) {Y p q : ℕ} {x : ℝ} (hx : 3 ≤ x)
    (hprange : p ∈ Finset.range (⌊2 * x⌋₊ + 1)) (hpprime : p.Prime) (hpx : x < (p : ℝ))
    (hp2x : (p : ℝ) ≤ 2 * x) (hpb : ¬ p ∣ b) (hq : q.Prime) (hqY : Y < q) (hqp : q ∣ p - 1)
    (hpow : (b : ZMod p) ^ ((p - 1) / q) = 1) :
    p ∈ smallOrderAt {b} x ∪ grhRangeExceptions {b} Y x ∪ windowExceptions x := by
  have hp3 : 3 < p := by
    have hcast : (3 : ℝ) < (p : ℝ) := hx.trans_lt hpx
    exact_mod_cast hcast
  by_cases h1 : q ≤ grhCutoff x
  · apply Finset.mem_union_left
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨b, Finset.mem_singleton_self b, Finset.mem_biUnion.mpr ⟨q, ?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hqY, h1⟩, hq⟩
    · exact Finset.mem_filter.mpr ⟨hprange, hpprime, hpx, hp2x, hpb, hqp, hpow⟩
  · by_cases h2 : q ≤ orderCutoff x
    · apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by omega, h2⟩, hq⟩, ?_⟩
      exact Finset.mem_filter.mpr ⟨hprange, hpprime, hqp⟩
    · apply Finset.mem_union_left
      apply Finset.mem_union_left
      apply Finset.mem_biUnion.mpr
      refine ⟨b, Finset.mem_singleton_self b, Finset.mem_filter.mpr ⟨hprange, hpprime, hpx, ?_⟩⟩
      have hjpos : 1 ≤ (p - 1) / q := Nat.div_pos (Nat.le_of_dvd (by omega) hqp) hq.pos
      have hjle := quotient_le_smallOrderCutoff (by linarith) hp2x (by omega : orderCutoff x < q)
      exact dvd_smallOrderProduct_of_pow_eq_one hb hjpos hjle hpow

/-! ### Residue-free primes for `-b` -/

theorem goodPrimesInt_subset_residueFree (a : ℤ) {S : Finset ℕ} (hS : ∀ q ∈ S, q.Prime)
    {x : ℝ} (hx : 0 ≤ x) : goodPrimesInt a x ⊆ residueFreePrimesInt a S x := by
  intro p hp
  obtain ⟨hr, hprim, hpx⟩ := Finset.mem_filter.mp hp
  have hp2x : (p : ℝ) ≤ 2 * x := by
    have h1 : p ≤ ⌊2 * x⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    exact (Nat.cast_le.mpr h1).trans (Nat.floor_le (by linarith))
  exact Finset.mem_filter.mpr ⟨hr, hprim.1, hpx, hp2x, fun q hq ⟨hqp, hpow⟩ =>
    pow_ne_one_of_isPrimitiveRootPrimeInt hprim (hS q hq) hqp hpow⟩

theorem residueFreePrimesInt_anti (a : ℤ) {S S' : Finset ℕ} (h : S ⊆ S') (x : ℝ) :
    residueFreePrimesInt a S' x ⊆ residueFreePrimesInt a S x := by
  intro p hp
  obtain ⟨hr, hpp, hx1, hx2, hres⟩ := Finset.mem_filter.mp hp
  exact Finset.mem_filter.mpr ⟨hr, hpp, hx1, hx2, fun q hq => hres q (h hq)⟩

theorem primesUpTo_mono {Y Y' : ℕ} (h : Y ≤ Y') : primesUpTo Y ⊆ primesUpTo Y' := by
  intro q hq
  obtain ⟨hqp, hqY⟩ := mem_primesUpTo.mp hq
  exact mem_primesUpTo.mpr ⟨hqp, hqY.trans h⟩

/-- A residue-free prime (for the primes `≤ Y`) at which `-b` is not a primitive root is an
exception of `b` in one of Hooley's three ranges. -/
theorem residueFreeInt_neg_subset {b : ℕ} (hb : 2 ≤ b) {Y : ℕ} (hY : 2 ≤ Y) {x : ℝ}
    (hx : 3 ≤ x) (hbx : (b : ℝ) ≤ x) :
    residueFreePrimesInt (-(b : ℤ)) (primesUpTo Y) x ⊆
      goodPrimesInt (-(b : ℤ)) x ∪ (smallOrderAt {b} x ∪ grhRangeExceptions {b} Y x ∪
        windowExceptions x) := by
  intro p hp
  obtain ⟨hprange, hpprime, hpx, hp2x, hres⟩ := Finset.mem_filter.mp hp
  by_cases hprim : IsPrimitiveRootPrimeInt (-(b : ℤ)) p
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hprange, hprim, hpx⟩)
  apply Finset.mem_union_right
  haveI : Fact p.Prime := ⟨hpprime⟩
  have hbp : b < p := by exact_mod_cast lt_of_le_of_lt hbx hpx
  have hpb : ¬ p ∣ b := Nat.not_dvd_of_pos_of_lt (by omega) hbp
  have hb0 : ((b : ℕ) : ZMod p) ≠ 0 := fun h => hpb ((ZMod.natCast_eq_zero_iff b p).mp h)
  have hc : (((-(b : ℤ)) : ℤ) : ZMod p) ≠ 0 := by
    push_cast
    exact neg_ne_zero.mpr hb0
  obtain ⟨q, hq, hqp, hpow⟩ := exists_prime_obstruction_zmod hc (fun h => hprim ⟨hpprime, h⟩)
  have hqY : Y < q := by
    by_contra hle
    exact hres q (mem_primesUpTo.mpr ⟨hq, by omega⟩) ⟨hqp, hpow⟩
  have hp3 : 3 < p := by
    have hcast : (3 : ℝ) < (p : ℝ) := hx.trans_lt hpx
    exact_mod_cast hcast
  have hpodd : Odd p := hpprime.odd_of_ne_two (by omega)
  have hqodd : Odd q := hq.odd_of_ne_two (by omega)
  have hbpow : (b : ZMod p) ^ ((p - 1) / q) = 1 := by
    rw [← neg_pow_div_eq hpodd hqodd hqp]
    push_cast at hpow
    exact hpow
  exact mem_exceptions_of_obstruction hb hx hprange hpprime hpx hp2x hpb hq hqY hqp hbpow

/-! ### The progressions for `-b` -/

/-- **The base class for `-b`.** Modulo `H = 24 ∏ q` (`q ≥ 5` the prime factors of `b`), a class
`u ≡ 23 (mod 24)` in which every such `q` is a square: there `-b` is a nonsquare, and no prime
`q ≥ 3` dividing `H` divides `p - 1`. -/
theorem exists_neg_progression_strong {b : ℕ} (hb : 0 < b) :
    ∃ H u : ℕ, 0 < H ∧ u < H ∧ u.Coprime H ∧
      ∀ p : ℕ, p.Prime → 3 < p → p ≡ u [MOD H] →
        ¬ IsSquare (((-(b : ℤ)) : ℤ) : ZMod p) ∧
          ∀ q : ℕ, q.Prime → 3 ≤ q → q ∣ H → ¬ q ∣ p - 1 := by
  classical
  let S := b.factorization.support.filter (fun q => 5 ≤ q)
  have hS : ∀ q ∈ S, q.Prime ∧ 5 ≤ q := by
    intro q hq
    obtain ⟨hmem, hfive⟩ := Finset.mem_filter.mp hq
    exact ⟨Nat.prime_of_mem_primeFactors hmem, hfive⟩
  obtain ⟨u, hu, huc, hub, hclass⟩ := exists_signed_fixed_residue hS (fun _ => 0)
  have hH : 0 < 24 * (∏ q ∈ S, q) := by
    apply Nat.mul_pos (by decide)
    exact Finset.prod_pos fun q hq => (hS q hq).1.pos
  refine ⟨24 * (∏ q ∈ S, q), u, hH, hu, huc, ?_⟩
  intro p hprime hp hpu
  haveI : Fact p.Prime := ⟨hprime⟩
  obtain ⟨h2, h3, hq⟩ := hclass p hp hpu
  have hpbase : p % 24 = 23 := by
    calc p % 24 = u % 24 := hpu.of_dvd (dvd_mul_right 24 _)
         _ = baseResidue 0 0 := hub
         _ = 23 := by decide
  constructor
  · have hcoord : ∀ q ∈ b.factorization.support,
        legendreSym p q = binarySign ((fun _ => (0 : ZMod 2)) q) := by
      intro q hqb
      by_cases hqtwo : q = 2
      · simpa only [hqtwo, Nat.cast_ofNat] using h2
      by_cases hqthree : q = 3
      · simpa only [hqthree, Nat.cast_ofNat] using h3
      have hqprime := Nat.prime_of_mem_primeFactors hqb
      have hfive : 5 ≤ q := by
        have hodd := hqprime.eq_two_or_odd.resolve_left hqtwo
        have := hqprime.two_le
        omega
      exact (hq q (Finset.mem_filter.mpr ⟨hqb, hfive⟩)).1
    have hlegb : legendreSym p b = 1 := by
      rw [legendre_eq_binarySign_of_coordinates (by omega) _ hcoord]
      simp [binarySign]
    have hneg1 : legendreSym p (-1) = -1 := by
      rw [legendreSym.at_neg_one (by omega)]
      exact ZMod.χ₄_nat_three_mod_four (by omega)
    have hleg : legendreSym p (-(b : ℤ)) = -1 := by
      rw [show (-(b : ℤ)) = (-1) * (b : ℤ) by ring, legendreSym.mul, hneg1, hlegb]
      norm_num
    exact (legendreSym.eq_neg_one_iff p).mp hleg
  · intro q hqprime hqthree hqH
    by_cases hthree : q = 3
    · subst hthree
      exact not_dvd_sub_one_of_local_residue (by omega) (by decide) (by decide)
        (by omega : p % 3 = 2)
    · have hfive : 5 ≤ q := by
        have hodd := hqprime.eq_two_or_odd.resolve_left (by omega)
        omega
      apply (hq q ?_).2
      have hn24 : ¬ q ∣ 24 := hqprime.coprime_iff_not_dvd.mp
        (prime_ge_five_coprime_twenty_four hqprime hfive)
      have hqprod := (hqprime.dvd_mul.mp hqH).resolve_left hn24
      obtain ⟨t, ht, hqt⟩ := (hqprime.prime.dvd_finsetProd_iff (fun t : ℕ => t)).mp hqprod
      have heq : q = t := (Nat.dvd_prime (hS t ht).1).mp hqt |>.resolve_left hqprime.ne_one
      simpa only [heq] using ht

/-- **The selector for `-b`.** `M` is fixed before `T`; the allowed extensions remove the odd
primes `q ≤ 2T² + 1` from `p - 1` and keep relative density `≥ 1 / (2 φ(M) T)`. -/
theorem exists_neg_progression_selector {b : ℕ} (hb : 0 < b) :
    ∃ M : ℕ, 0 < M ∧ ∀ T : ℕ, 1 ≤ T → ∃ H : ℕ, ∃ R : Finset ℕ,
      0 < H ∧ R.Nonempty ∧
        1 / (2 * (Nat.totient M : ℝ) * (T : ℝ)) ≤ (R.card : ℝ) / Nat.totient H ∧
          ∀ u ∈ R, u < H ∧ u.Coprime H ∧
            ∀ p : ℕ, p.Prime → 3 < p → p ≡ u [MOD H] →
              ¬ IsSquare (((-(b : ℤ)) : ℤ) : ZMod p) ∧
                ∀ q : ℕ, q.Prime → 3 ≤ q → q ≤ 2 * T ^ 2 + 1 → ¬ q ∣ p - 1 := by
  classical
  obtain ⟨M, r, hM, hr, hrc, hbase⟩ := exists_neg_progression_strong hb
  refine ⟨M, hM, ?_⟩
  intro T hT
  let S := (Finset.range (2 * T ^ 2 + 2)).filter fun q =>
    q.Prime ∧ 3 ≤ q ∧ M.Coprime q
  have hS : ∀ q ∈ S, q.Prime ∧ 3 ≤ q ∧ q ≤ 2 * T ^ 2 + 1 := by
    intro q hq
    obtain ⟨hqr, hprime, hq3, _⟩ := Finset.mem_filter.mp hq
    exact ⟨hprime, hq3, by have := Finset.mem_range.mp hqr; omega⟩
  have hcop : ∀ q ∈ S, M.Coprime q := fun q hq => (Finset.mem_filter.mp hq).2.2.2
  let H := M * (∏ q ∈ S, q)
  let R := allowedExtensions M r S
  have hH : 0 < H := Nat.mul_pos hM (Finset.prod_pos fun q hq => (hS q hq).1.pos)
  have hden := allowedExtensions_density_lower hM hr hrc hT hS hcop
  have hphi : 0 < (Nat.totient M : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hM
  have hTpos : 0 < (T : ℝ) := by exact_mod_cast (by omega : 0 < T)
  have hR : R.Nonempty := by
    by_contra hn
    have hz : R = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hzero : (allowedExtensions M r S).card = 0 := by change R.card = 0; rw [hz]; rfl
    rw [hzero, Nat.cast_zero, zero_div] at hden
    have hpositive : 0 < 1 / (2 * (Nat.totient M : ℝ) * (T : ℝ)) := by positivity
    linarith
  refine ⟨H, R, hH, hR, hden, ?_⟩
  intro u hu
  have humem := Finset.mem_filter.mp hu
  refine ⟨Finset.mem_range.mp humem.1, humem.2.1, ?_⟩
  intro p hprime hp hpu
  obtain ⟨hpbase, havoid⟩ := allowedExtensions_prime_properties hr
    (fun q hq => (hS q hq).1) hu (by omega) hpu
  have hbasic := hbase p hprime hp hpbase
  refine ⟨hbasic.1, ?_⟩
  intro q hq hq3 hqY
  by_cases hqM : q ∣ M
  · exact hbasic.2 q hq hq3 hqM
  · apply havoid q
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hq, hq3,
      (hq.coprime_iff_not_dvd.mpr hqM).symm⟩

/-! ### The lower bound for `-b` -/

/-- **Hooley's classification for `-b`.** A candidate in the selected classes at which `-b` is
not a primitive root is an exception of `b`. -/
theorem bad_negCandidates_subset {b : ℕ} (hb : 2 ≤ b) {Y H : ℕ} {R : Finset ℕ} {x : ℝ}
    (hx : 3 ≤ x)
    (hR : ∀ u ∈ R, ∀ p : ℕ, p.Prime → 3 < p → p ≡ u [MOD H] →
      ¬ IsSquare (((-(b : ℤ)) : ℤ) : ZMod p) ∧
        ∀ q : ℕ, q.Prime → 3 ≤ q → q ≤ Y → ¬ q ∣ p - 1) :
    (progressionCandidates H R x).filter (fun p => ¬ IsPrimitiveRootPrimeInt (-(b : ℤ)) p) ⊆
      smallOrderAt {b} x ∪ grhRangeExceptions {b} Y x ∪ windowExceptions x := by
  intro p hp
  obtain ⟨hpC, hpbad⟩ := Finset.mem_filter.mp hp
  obtain ⟨hprange, hpprime, hpx, hp2x, u, hu, hpu⟩ := Finset.mem_filter.mp hpC
  have hp3 : 3 < p := by
    have hcast : (3 : ℝ) < (p : ℝ) := hx.trans_lt hpx
    exact_mod_cast hcast
  obtain ⟨hsq, havoid⟩ := hR u hu p hpprime hp3 hpu
  haveI : Fact p.Prime := ⟨hpprime⟩
  have hc : (((-(b : ℤ)) : ℤ) : ZMod p) ≠ 0 := fun h0 => hsq ⟨0, by rw [h0, mul_zero]⟩
  obtain ⟨q, hq, hqp, hpow⟩ := exists_prime_obstruction_zmod hc (fun h => hpbad ⟨hpprime, h⟩)
  have hpodd : Odd p := hpprime.odd_of_ne_two (by omega)
  have hq2 : q ≠ 2 := by
    rintro rfl
    apply hsq
    apply (ZMod.euler_criterion p hc).mpr
    have hp2 : (p - 1) / 2 = p / 2 := by
      obtain ⟨k, hk⟩ := hpodd
      omega
    rwa [hp2] at hpow
  have hqY : Y < q := by
    by_contra hle
    exact havoid q hq (by have := hq.two_le; omega) (by omega) hqp
  have hpb : ¬ p ∣ b := by
    intro hdvd
    apply hc
    have h0 : ((b : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff b p).mpr hdvd
    push_cast
    rw [h0, neg_zero]
  have hqodd : Odd q := hq.odd_of_ne_two hq2
  have hbpow : (b : ZMod p) ^ ((p - 1) / q) = 1 := by
    rw [← neg_pow_div_eq hpodd hqodd hqp]
    push_cast at hpow
    exact hpow
  exact mem_exceptions_of_obstruction hb hx hprange hpprime hpx hp2x hpb hq hqY hqp hbpow

/-- **The positive lower bound for `-b`** (Hooley's method), from the GRH splitting estimate for
`b`. -/
theorem exists_negPrimitiveRoot_lower {b : ℕ} (hb : 2 ≤ b) {C : ℝ} (hC : 0 ≤ C)
    (hGRH : GRHSplittingBoundUpTo b C) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c * (x / Real.log x) ≤ ((goodPrimesInt (-(b : ℤ)) x).card : ℝ) := by
  classical
  obtain ⟨M, hM, hselector⟩ := exists_neg_progression_selector (by omega : 0 < b)
  have hphi : 0 < (Nat.totient M : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hM
  set θ : ℝ := 1 / 2 with hθdef
  have hθ : 0 < θ := by norm_num
  obtain ⟨T, hTlarge⟩ := exists_nat_gt
    (max 1 (max (4 * C * (Nat.totient M : ℝ) / θ) (b : ℝ)))
  have hTreal : 1 < (T : ℝ) := (le_max_left _ _).trans_lt hTlarge
  have hT : 1 ≤ T := by exact_mod_cast hTreal.le
  have hTpos : 0 < (T : ℝ) := by linarith
  have hlarge : 4 * C * (Nat.totient M : ℝ) ≤ θ * (T : ℝ) := by
    have hd : 4 * C * (Nat.totient M : ℝ) / θ < (T : ℝ) :=
      (le_max_left _ _).trans_lt ((le_max_right _ _).trans_lt hTlarge)
    have := (div_lt_iff₀ hθ).mp hd
    nlinarith
  have hbT : b ≤ 2 * T ^ 2 + 1 := by
    have hbT' : (b : ℝ) < T := (le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hTlarge)
    have hnat : b < T := by exact_mod_cast hbT'
    have hTpow : T ≤ T ^ 2 := Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) T
    omega
  obtain ⟨H, R, hH, _, hdensity, hprops⟩ := hselector T hT
  have hregular : ∀ u ∈ R, u < H ∧ u.Coprime H := fun u hu =>
    ⟨(hprops u hu).1, (hprops u hu).2.1⟩
  have hprogressions := fun u hu => (hprops u hu).2.2
  have hgap : C / (2 * (T : ℝ) ^ 2 + 1) < θ / (2 * (Nat.totient M : ℝ) * (T : ℝ)) :=
    positive_parameter_difference hθ hphi hTpos hlarge
  set g : ℝ := θ / (2 * (Nat.totient M : ℝ) * (T : ℝ)) - C / (2 * (T : ℝ) ^ 2 + 1) with hgdef
  have hg : 0 < g := sub_pos.mpr hgap
  obtain ⟨ε, hε, hexc⟩ := exists_exception_error ({b} : Finset ℕ) hC
  have hexc' := hexc (2 * T ^ 2 + 1) (by omega)
    (fun a ha => by rw [Finset.mem_singleton.mp ha]; exact hbT)
    (fun a ha => by rw [Finset.mem_singleton.mp ha]; exact hb)
    (fun a ha => by rw [Finset.mem_singleton.mp ha]; exact hGRH)
  have hsup := progressionCandidates_supply hH hregular (θ := θ) (by norm_num)
  have hεsmall := hε.eventually (gt_mem_nhds (half_pos hg))
  refine ⟨g / 2, half_pos hg, ?_⟩
  filter_upwards [hsup, hexc', hεsmall, eventually_ge_atTop (3 : ℝ)] with x hxs hxe hxε hx3
  have hscale : 0 < x / Real.log x := div_pos (by linarith) (Real.log_pos (by linarith))
  set P := progressionCandidates H R x with hPdef
  set Bad := P.filter (fun p => ¬ IsPrimitiveRootPrimeInt (-(b : ℤ)) p) with hBad
  have hsplit : P.card ≤ (goodPrimesInt (-(b : ℤ)) x).card + Bad.card := by
    have hsub : P ⊆ goodPrimesInt (-(b : ℤ)) x ∪ Bad := by
      intro p hp
      by_cases hprim : IsPrimitiveRootPrimeInt (-(b : ℤ)) p
      · apply Finset.mem_union_left
        obtain ⟨hr, _, hpx, _⟩ := Finset.mem_filter.mp hp
        exact Finset.mem_filter.mpr ⟨hr, hprim, hpx⟩
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, hprim⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hbad : (Bad.card : ℝ) ≤ ((smallOrderAt {b} x).card : ℝ) +
      (grhRangeExceptions {b} (2 * T ^ 2 + 1) x).card + (windowExceptions x).card := by
    have hsub := bad_negCandidates_subset hb hx3 hprogressions
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le
      (smallOrderAt {b} x ∪ grhRangeExceptions {b} (2 * T ^ 2 + 1) x) (windowExceptions x)
    have h3 := Finset.card_union_le (smallOrderAt {b} x)
      (grhRangeExceptions {b} (2 * T ^ 2 + 1) x)
    have hnat : Bad.card ≤ (smallOrderAt {b} x).card +
        (grhRangeExceptions {b} (2 * T ^ 2 + 1) x).card + (windowExceptions x).card := by
      omega
    exact_mod_cast hnat
  have hlower : θ / (2 * (Nat.totient M : ℝ) * (T : ℝ)) * (x / Real.log x) ≤
      (P.card : ℝ) := by
    have hmul := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hdensity hθ.le) hscale.le
    have heq : θ * (1 / (2 * (Nat.totient M : ℝ) * (T : ℝ))) =
        θ / (2 * (Nat.totient M : ℝ) * (T : ℝ)) := by ring
    rw [heq] at hmul
    exact hmul.trans hxs
  have hYcast : (((2 * T ^ 2 + 1 : ℕ) : ℕ) : ℝ) = 2 * (T : ℝ) ^ 2 + 1 := by push_cast; ring
  rw [hYcast, Finset.card_singleton, Nat.cast_one, one_mul] at hxe
  have hεle : (x / Real.log x) * ε x ≤ (x / Real.log x) * (g / 2) :=
    mul_le_mul_of_nonneg_left hxε.le hscale.le
  have hsplit' : (P.card : ℝ) ≤ (goodPrimesInt (-(b : ℤ)) x).card + Bad.card := by
    exact_mod_cast hsplit
  have hexpand : (x / Real.log x) * (C / (2 * (T : ℝ) ^ 2 + 1) + ε x) =
      C / (2 * (T : ℝ) ^ 2 + 1) * (x / Real.log x) + (x / Real.log x) * ε x := by ring
  have hfinal : g / 2 * (x / Real.log x) =
      θ / (2 * (Nat.totient M : ℝ) * (T : ℝ)) * (x / Real.log x) -
        C / (2 * (T : ℝ) ^ 2 + 1) * (x / Real.log x) - (x / Real.log x) * (g / 2) := by
    rw [hgdef]
    ring
  rw [hexpand] at hxe
  linarith

/-! ### The squeeze -/

/-- **The squeeze of `Density.lean`, abstractly.** Suppose `f ≤ g Y` eventually, `g Y` decreases
in `Y`, `g Y x / (x / log x) → d Y`, the excess `g Y - f` is at most `(C / Y + ε x) x / log x`
for `Y ≥ Y₀` with `ε → 0`, and `f ≥ c x / log x` with `c > 0`. Then `f x / (x / log x)`
converges to `inf_Y d Y ≥ c`. -/
theorem exists_tendsto_of_squeeze {f : ℝ → ℝ} {g : ℕ → ℝ → ℝ} {d : ℕ → ℝ}
    (hd : ∀ Y, Tendsto (fun x => g Y x / (x / Real.log x)) atTop (𝓝 (d Y)))
    (hfg : ∀ Y, ∀ᶠ x in atTop, f x ≤ g Y x)
    (hanti : ∀ Y Y', Y ≤ Y' → ∀ᶠ x in atTop, g Y' x ≤ g Y x)
    {C : ℝ} {ε : ℝ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (Y₀ : ℕ)
    (hexc : ∀ Y, Y₀ ≤ Y → 1 ≤ Y →
      ∀ᶠ x in atTop, g Y x ≤ f x + (x / Real.log x) * (C / Y + ε x))
    {c : ℝ} (hc : 0 < c) (hlow : ∀ᶠ x in atTop, c * (x / Real.log x) ≤ f x) :
    ∃ δ : ℝ, 0 < δ ∧ Tendsto (fun x => f x / (x / Real.log x)) atTop (𝓝 δ) := by
  have hscale : ∀ᶠ x : ℝ in atTop, 0 < x / Real.log x := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact div_pos (by linarith) (Real.log_pos hx)
  have hdc : ∀ Y, c ≤ d Y := fun Y =>
    ge_of_tendsto (hd Y) (by
      filter_upwards [hscale, hfg Y, hlow] with x hx hfgx hlowx
      rw [le_div_iff₀ hx]
      linarith)
  have hdanti : Antitone d := by
    intro Y Y' hYY'
    refine le_of_tendsto_of_tendsto (hd Y') (hd Y) ?_
    filter_upwards [hscale, hanti Y Y' hYY'] with x hx hg
    exact div_le_div_of_nonneg_right hg hx.le
  have hbdd : BddBelow (Set.range d) := ⟨c, by rintro _ ⟨Y, rfl⟩; exact hdc Y⟩
  set δ := ⨅ Y, d Y with hδdef
  have hdδ : Tendsto d atTop (𝓝 δ) := tendsto_atTop_ciInf hdanti hbdd
  have hδle : ∀ Y, δ ≤ d Y := fun Y => ciInf_le hbdd Y
  have hcδ : c ≤ δ := le_ciInf hdc
  refine ⟨δ, hc.trans_le hcδ, ?_⟩
  rw [tendsto_order]
  constructor
  · intro l hl
    set η := (δ - l) / 4 with hη
    have hη0 : 0 < η := by rw [hη]; linarith
    obtain ⟨Y, hY⟩ := exists_nat_gt (max (C / η) ((Y₀ : ℝ) + 1))
    have hY₀Y : ((Y₀ : ℝ) + 1) < Y := (le_max_right _ _).trans_lt hY
    have hYY₀ : Y₀ ≤ Y := by
      have : (Y₀ : ℝ) < Y := by linarith
      exact_mod_cast this.le
    have hY1 : 1 ≤ Y := by
      have h0 : (0 : ℝ) ≤ Y₀ := Nat.cast_nonneg _
      have : (1 : ℝ) < Y := by linarith
      exact_mod_cast this.le
    have hYpos : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
    have hCY : C / Y < η := by
      rw [div_lt_iff₀ hYpos]
      have h1 : C / η < Y := (le_max_left _ _).trans_lt hY
      rw [div_lt_iff₀ hη0] at h1
      linarith
    have hratio := (hd Y).eventually (lt_mem_nhds (show d Y - η < d Y by linarith))
    have hεsmall := hε.eventually (gt_mem_nhds hη0)
    filter_upwards [hexc Y hYY₀ hY1, hratio, hεsmall, hscale] with x hxe hxr hxε hxs
    rw [lt_div_iff₀ hxs]
    have hr' := (lt_div_iff₀ hxs).mp hxr
    have hεx : ε x < η := hxε
    have h1 : (x / Real.log x) * (C / Y) ≤ (x / Real.log x) * η :=
      mul_le_mul_of_nonneg_left hCY.le hxs.le
    have h2 : (x / Real.log x) * ε x ≤ (x / Real.log x) * η :=
      mul_le_mul_of_nonneg_left hεx.le hxs.le
    have h3 : (δ - η) * (x / Real.log x) ≤ (d Y - η) * (x / Real.log x) :=
      mul_le_mul_of_nonneg_right (by linarith [hδle Y]) hxs.le
    have h4 : 0 < (x / Real.log x) * η := mul_pos hxs hη0
    have hl : l = δ - 4 * η := by rw [hη]; ring
    rw [hl]
    nlinarith
  · intro u hu
    obtain ⟨Y, hY⟩ := (hdδ.eventually (gt_mem_nhds hu)).exists
    have hratio := (hd Y).eventually (gt_mem_nhds hY)
    filter_upwards [hratio, hscale, hfg Y] with x hxr hxs hfgx
    refine lt_of_le_of_lt ?_ hxr
    exact div_le_div_of_nonneg_right hfgx hxs.le

/-! ### The density for `-b` -/

/-- **The density of primes with primitive root `-b` exists and is positive** (dyadic form),
under the GRH-strength splitting estimate for `b`. -/
theorem exists_tendsto_negPrimitiveRoot_density {b : ℕ} (hb : 2 ≤ b) {C : ℝ} (hC : 0 ≤ C)
    (hGRH : GRHSplittingBoundUpTo b C) :
    ∃ δ : ℝ, 0 < δ ∧ Tendsto (fun x : ℝ =>
      ((goodPrimesInt (-(b : ℤ)) x).card : ℝ) / (x / Real.log x)) atTop (𝓝 δ) := by
  have hex : ∀ Y : ℕ, ∃ d : ℝ, Tendsto (fun x : ℝ =>
      ((residueFreePrimesInt (-(b : ℤ)) (primesUpTo Y) x).card : ℝ) / (x / Real.log x))
      atTop (𝓝 d) :=
    fun Y => exists_tendsto_residueFreePrimesInt (by omega) fun q hq => (mem_primesUpTo.mp hq).1
  choose d hd using hex
  obtain ⟨c, hc, hlow⟩ := exists_negPrimitiveRoot_lower hb hC hGRH
  obtain ⟨ε, hε, hexc⟩ := exists_exception_error ({b} : Finset ℕ) hC
  refine exists_tendsto_of_squeeze (f := fun x => ((goodPrimesInt (-(b : ℤ)) x).card : ℝ))
    (g := fun Y x => ((residueFreePrimesInt (-(b : ℤ)) (primesUpTo Y) x).card : ℝ)) hd ?_ ?_
    hε b ?_ hc hlow
  · intro Y
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact_mod_cast Finset.card_le_card (goodPrimesInt_subset_residueFree _
      (fun q hq => (mem_primesUpTo.mp hq).1) hx)
  · intro Y Y' hYY'
    filter_upwards with x
    exact_mod_cast Finset.card_le_card (residueFreePrimesInt_anti _ (primesUpTo_mono hYY') x)
  · intro Y hY hY1
    filter_upwards [hexc Y hY1 (fun a ha => by rw [Finset.mem_singleton.mp ha]; exact hY)
        (fun a ha => by rw [Finset.mem_singleton.mp ha]; exact hb)
        (fun a ha => by rw [Finset.mem_singleton.mp ha]; exact hGRH),
      eventually_ge_atTop (3 : ℝ), eventually_ge_atTop (b : ℝ)] with x hxe hx3 hxb
    rw [Finset.card_singleton, Nat.cast_one, one_mul] at hxe
    have hsub := residueFreeInt_neg_subset hb (Y := Y) (by omega) hx3 hxb
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (goodPrimesInt (-(b : ℤ)) x)
      (smallOrderAt {b} x ∪ grhRangeExceptions {b} Y x ∪ windowExceptions x)
    have h3 := Finset.card_union_le (smallOrderAt {b} x ∪ grhRangeExceptions {b} Y x)
      (windowExceptions x)
    have h4 := Finset.card_union_le (smallOrderAt {b} x) (grhRangeExceptions {b} Y x)
    have hnat : (residueFreePrimesInt (-(b : ℤ)) (primesUpTo Y) x).card ≤
        (goodPrimesInt (-(b : ℤ)) x).card + ((smallOrderAt {b} x).card +
          (grhRangeExceptions {b} Y x).card + (windowExceptions x).card) := by
      omega
    have hcast : ((residueFreePrimesInt (-(b : ℤ)) (primesUpTo Y) x).card : ℝ) ≤
        (goodPrimesInt (-(b : ℤ)) x).card + (((smallOrderAt {b} x).card : ℝ) +
          (grhRangeExceptions {b} Y x).card + (windowExceptions x).card) := by
      exact_mod_cast hnat
    show ((residueFreePrimesInt (-(b : ℤ)) (primesUpTo Y) x).card : ℝ) ≤
      ((goodPrimesInt (-(b : ℤ)) x).card : ℝ) + (x / Real.log x) * (C / Y + ε x)
    linarith

/-! ### Cumulative density -/

/-- There are infinitely many primes: `#{p ≤ x} → ∞`. -/
theorem tendsto_upCount_prime :
    Tendsto (fun x : ℝ => (upCount Nat.Prime x : ℝ)) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨n, hn⟩ := exists_nat_gt b
  obtain ⟨S, hS⟩ : ∃ S : Finset ℕ, S.card = n ∧ ∀ p ∈ S, p.Prime := by
    obtain ⟨S, hSsub, hScard⟩ :=
      Set.Infinite.exists_subset_card_eq Nat.infinite_setOfPred_prime n
    exact ⟨S, hScard, fun p hp => hSsub hp⟩
  set M := S.sup id
  refine ⟨M, fun x hx => ?_⟩
  have hsub : S ⊆ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime := by
    intro p hp
    refine Finset.mem_filter.mpr ⟨?_, hS.2 p hp⟩
    have h1 : p ≤ M := Finset.le_sup (f := id) hp
    have h2 : (M : ℝ) ≤ x := hx
    have h3 : p ≤ ⌊x⌋₊ := Nat.le_floor ((Nat.cast_le.mpr h1).trans h2)
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le h3)
  have hcard : n ≤ upCount Nat.Prime x := by
    unfold upCount
    rw [← hS.1]
    exact Finset.card_le_card hsub
  have hcard' : (n : ℝ) ≤ upCount Nat.Prime x := by exact_mod_cast hcard
  linarith

/-- **Dyadic to cumulative density among the primes.** If the dyadic increments of
`#{n ≤ x : Q n}` are `~ δ x / log x`, then `#{n ≤ x : Q n} / #{p ≤ x} → δ`. -/
theorem tendsto_upCount_div_prime (Q : ℕ → Prop) [DecidablePred Q] {δ : ℝ} (hδ : 0 ≤ δ)
    (hT : Tendsto (fun x : ℝ => ((upCount Q (2 * x) : ℝ) - upCount Q x) / (x / Real.log x))
      atTop (𝓝 δ)) :
    Tendsto (fun x : ℝ => (upCount Q x : ℝ) / upCount Nat.Prime x) atTop (𝓝 δ) := by
  refine tendsto_div_of_dyadic (upCount_mono _) (upCount_mono _)
    (fun _ => Nat.cast_nonneg _) (fun _ => Nat.cast_nonneg _) hδ ?_ ?_ tendsto_upCount_prime
  · have hP := tendsto_dyadicPrimes
    have h := hT.div hP one_ne_zero
    rw [div_one] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
    have hx0 : x ≠ 0 := by linarith
    simp only [Pi.div_apply]
    rw [div_div_div_cancel_right₀ (div_ne_zero hx0 hlog)]
  · have hP := tendsto_dyadicPrimes
    have hev := hP.eventually (lt_mem_nhds (show (1 : ℝ) / 2 < 1 by norm_num))
    filter_upwards [hev, eventually_gt_atTop (1 : ℝ)] with x hx hx1
    have hs : 0 < x / Real.log x := div_pos (by linarith) (Real.log_pos hx1)
    have := (lt_div_iff₀ hs).mp hx
    nlinarith

/-- **Artin's conjecture with density for `-b`, from the GRH splitting estimate for `b`.**
For `b ≥ 2`, `#{p ≤ x : -b primitive root mod p} / #{p ≤ x} → δ > 0`. -/
theorem negPrimitiveRoot_density_of_grhSplitting {b : ℕ} (hb : 2 ≤ b) {C : ℝ} (hC : 0 ≤ C)
    (hGRH : GRHSplittingBoundUpTo b C) :
    ∃ δ : ℝ, 0 < δ ∧ Tendsto (fun x : ℝ =>
      (upCount (IsPrimitiveRootPrimeInt (-(b : ℤ))) x : ℝ) / upCount Nat.Prime x) atTop
        (𝓝 δ) := by
  obtain ⟨δ, hδ, hT⟩ := exists_tendsto_negPrimitiveRoot_density hb hC hGRH
  refine ⟨δ, hδ, tendsto_upCount_div_prime _ hδ.le ?_⟩
  apply hT.congr'
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [goodPrimesInt_card_eq _ hx]

/-- **Artin's conjecture with density for `-b` under GRH for the Kummer fields of `b`.** -/
theorem negPrimitiveRoot_density_of_dedekindZetaGRH {b : ℕ} (hb : 2 ≤ b)
    (h : ∀ q : ℕ, ∀ hb : 2 ≤ b, ∀ hq : q.Prime, ∀ hbq : b < q,
      letI : Fact (2 ≤ b) := ⟨hb⟩
      letI : Fact q.Prime := ⟨hq⟩
      letI : Fact (b < q) := ⟨hbq⟩
      Explicit.DedekindZetaGRH (PrimeKummerField b q)) :
    ∃ δ : ℝ, 0 < δ ∧ Tendsto (fun x : ℝ =>
      (upCount (IsPrimitiveRootPrimeInt (-(b : ℤ))) x : ℝ) / upCount Nat.Prime x) atTop
        (𝓝 δ) := by
  obtain ⟨D, hD, hGRH⟩ := Explicit.grhSplittingBoundUpTo_of_kummerZetaGRH hb
    (Explicit.kummerZetaGRH_of_dedekindZetaGRH h)
  exact negPrimitiveRoot_density_of_grhSplitting hb hD hGRH

end

end SimultaneousPrimitiveRoots.Artin
