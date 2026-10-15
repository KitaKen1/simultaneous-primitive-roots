module

public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.NumberTheory.Divisors
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Monic polynomials over a finite field and the Newton recursion

This file contains the polynomial half of the classical proof of the Hasse--Davenport lifting
relation for Gauss sums (Ireland--Rosen, *A Classical Introduction to Modern Number Theory*,
Chapter 11, §4), in a form that does not mention characters or field extensions.

Let `k` be a finite field and let `lam : k[X] → R` be a function into a commutative ring that is
multiplicative on monic polynomials. Put

* `S_d = monicSum lam d`, the sum of `lam f` over the monic polynomials `f` of degree `d`;
* `N_j = primePowerSum lam j`, the sum of `deg P • lam P ^ (j / deg P)` over the monic irreducible
  polynomials `P` whose degree divides `j`.

In terms of the generating series `Z(T) = ∑_f lam f * T ^ deg f = ∑_d S_d T ^ d`, unique
factorization gives the Euler product `Z(T) = ∏_P (1 - lam P * T ^ deg P)⁻¹`, and taking the
logarithmic derivative gives `T Z'(T) = Z(T) * ∑_j N_j T ^ j`. We prove the coefficient form of
this identity directly, without power series:

* `natDegree_smul_monicSum`: `s • S_s = ∑_{1 ≤ j ≤ s} N_j * S_{s - j}`.

The proof writes the degree of a monic polynomial `f` as the sum of `deg P` over the pairs
`(P, m)` with `P` monic irreducible, `m ≥ 1` and `P ^ m ∣ f`
(`natDegree_eq_sum_irreducibleMonics`, the polynomial form of `log n = ∑_{d ∣ n} Λ(d)`), and
exchanges the order of summation, using that the monic multiples of degree `s` of a monic `h` are
the products `h * e` with `e` monic of degree `s - deg h` (`sum_monicsOfDegree_ite_dvd`).

When `S_d = 0` for all `d ≥ 2`, i.e. `Z(T) = 1 + S_1 T`, the recursion is solved by

* `neg_primePowerSum_eq_pow`: `-N_s = (-S_1) ^ s` for all `s ≥ 1`.

## Main definitions

* `monicsOfDegree k d`: the finite set of monic polynomials of degree `d` over the finite field
  `k`.
* `irreducibleMonics k s`: the finite set of monic irreducible polynomials of degree at most `s`.
* `irreducibleMonicsDvd k j`: the finite set of monic irreducible polynomials whose degree divides
  `j` (empty for `j = 0`).
* `monicSum lam d`, `primePowerSum lam j`: the sums `S_d` and `N_j` above.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Arithmetic

open Polynomial Finset

/-! ### Monic polynomials of a given degree over a finite field -/

section Monics

variable (k : Type*) [Field k] [Finite k]

/-- Over a finite field there are finitely many polynomials of degree at most `s`. -/
theorem finite_setOf_natDegree_le (s : ℕ) : {f : k[X] | f.natDegree ≤ s}.Finite := by
  have hfin : Finite (degreeLT k (s + 1)) :=
    Finite.of_equiv _ (degreeLTEquiv k (s + 1)).symm.toEquiv
  have hset : (degreeLT k (s + 1) : Set k[X]).Finite := Set.toFinite _
  refine hset.subset fun f hf => ?_
  rw [SetLike.mem_coe, mem_degreeLT]
  exact degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hf)

/-- The finite set of monic polynomials of degree `d` over a finite field. -/
noncomputable def monicsOfDegree (d : ℕ) : Finset k[X] :=
  ((finite_setOf_natDegree_le k d).subset
    (fun f (hf : f ∈ {f : k[X] | f.Monic ∧ f.natDegree = d}) => hf.2.le)).toFinset

/-- The finite set of monic irreducible polynomials of degree at most `s` over a finite field. -/
noncomputable def irreducibleMonics (s : ℕ) : Finset k[X] :=
  ((finite_setOf_natDegree_le k s).subset
    (fun f (hf : f ∈ {f : k[X] | f.Monic ∧ Irreducible f ∧ f.natDegree ≤ s}) => hf.2.2)).toFinset

/-- The finite set of monic irreducible polynomials whose degree divides `j`, for `j ≠ 0`
(it is empty for `j = 0`). -/
noncomputable def irreducibleMonicsDvd (j : ℕ) : Finset k[X] :=
  ((finite_setOf_natDegree_le k j).subset
    (fun f (hf : f ∈ {f : k[X] | f.Monic ∧ Irreducible f ∧ f.natDegree ∈ j.divisors}) =>
      Nat.divisor_le hf.2.2)).toFinset

variable {k}

@[simp]
theorem mem_monicsOfDegree {d : ℕ} {f : k[X]} :
    f ∈ monicsOfDegree k d ↔ f.Monic ∧ f.natDegree = d := by
  simp [monicsOfDegree]

@[simp]
theorem mem_irreducibleMonics {s : ℕ} {f : k[X]} :
    f ∈ irreducibleMonics k s ↔ f.Monic ∧ Irreducible f ∧ f.natDegree ≤ s := by
  simp [irreducibleMonics]

@[simp]
theorem mem_irreducibleMonicsDvd {j : ℕ} {f : k[X]} :
    f ∈ irreducibleMonicsDvd k j ↔ f.Monic ∧ Irreducible f ∧ f.natDegree ∈ j.divisors := by
  simp [irreducibleMonicsDvd]

/-- The only monic polynomial of degree `0` is `1`. -/
theorem monicsOfDegree_zero : monicsOfDegree k 0 = {1} := by
  ext f
  rw [mem_monicsOfDegree, Finset.mem_singleton]
  constructor
  · rintro ⟨hf, hd⟩
    exact hf.natDegree_eq_zero.mp hd
  · rintro rfl
    exact ⟨monic_one, natDegree_one⟩

/-- The monic polynomials of degree `1` are the `X - a`. -/
theorem sum_monicsOfDegree_one {M : Type*} [AddCommMonoid M] [Fintype k] (F : k[X] → M) :
    ∑ f ∈ monicsOfDegree k 1, F f = ∑ a : k, F (X - C a) := by
  symm
  refine Finset.sum_bij (fun a _ => X - C a) ?_ ?_ ?_ ?_
  · intro a _
    rw [mem_monicsOfDegree]
    exact ⟨monic_X_sub_C a, natDegree_X_sub_C a⟩
  · intro a _ b _ hab
    exact C_injective (sub_right_injective hab)
  · intro f hf
    rw [mem_monicsOfDegree] at hf
    refine ⟨-f.coeff 0, Finset.mem_univ _, ?_⟩
    conv_rhs => rw [hf.1.eq_X_add_C hf.2]
    rw [C_neg, sub_neg_eq_add]
  · intro a _
    rfl

/-- The monic polynomials of degree `s` divisible by a monic polynomial `h` are the products
`h * e` with `e` monic of degree `s - deg h`. -/
theorem sum_monicsOfDegree_ite_dvd {M : Type*} [AddCommMonoid M] (F : k[X] → M) {h : k[X]}
    (hh : h.Monic) (s : ℕ) [DecidablePred fun f : k[X] => h ∣ f] :
    ∑ f ∈ monicsOfDegree k s, (if h ∣ f then F f else 0) =
      if h.natDegree ≤ s then ∑ e ∈ monicsOfDegree k (s - h.natDegree), F (h * e) else 0 := by
  rw [← Finset.sum_filter]
  split_ifs with hle
  · symm
    refine Finset.sum_bij (fun e _ => h * e) ?_ ?_ ?_ ?_
    · intro e he
      rw [mem_monicsOfDegree] at he
      rw [Finset.mem_filter, mem_monicsOfDegree]
      refine ⟨⟨hh.mul he.1, ?_⟩, dvd_mul_right h e⟩
      rw [hh.natDegree_mul he.1, he.2]
      omega
    · intro e₁ _ e₂ _ he
      exact mul_left_cancel₀ hh.ne_zero he
    · intro f hf
      rw [Finset.mem_filter, mem_monicsOfDegree] at hf
      obtain ⟨⟨hfm, hfd⟩, e, rfl⟩ := hf
      have he : e.Monic := hh.of_mul_monic_left hfm
      refine ⟨e, ?_, rfl⟩
      rw [mem_monicsOfDegree]
      refine ⟨he, ?_⟩
      rw [hh.natDegree_mul he] at hfd
      omega
    · intro e _
      rfl
  · rw [Finset.filter_eq_empty_iff.mpr, Finset.sum_empty]
    intro f hf hdvd
    rw [mem_monicsOfDegree] at hf
    exact hle (hf.2 ▸ Polynomial.natDegree_le_of_dvd hdvd hf.1.ne_zero)

/-- **The degree of a monic polynomial through its prime power divisors**: the degree of `f` is
the sum of `deg P` over all pairs `(P, m)` with `P` monic irreducible, `m ≥ 1` and `P ^ m ∣ f`.
This is the polynomial form of `log n = ∑_{d ∣ n} Λ(d)`. -/
theorem natDegree_eq_sum_irreducibleMonics [DecidableRel fun a b : k[X] => a ∣ b] {f : k[X]}
    (hf : f.Monic) {s : ℕ} (hs : f.natDegree ≤ s) :
    f.natDegree =
      ∑ P ∈ irreducibleMonics k s, ∑ m ∈ Finset.Icc 1 s, if P ^ m ∣ f then P.natDegree else 0 := by
  classical
  have hf0 : f ≠ 0 := hf.ne_zero
  set nf := UniqueFactorizationMonoid.normalizedFactors f with hnf
  have hmem : ∀ P, P ∈ nf ↔ Irreducible P ∧ P.Monic ∧ P ∣ f := fun P =>
    Polynomial.mem_normalizedFactors_iff hf0
  have hprod : nf.prod = f := by
    have := leadingCoeff_mul_prod_normalizedFactors f
    rwa [hf.leadingCoeff, C_1, one_mul] at this
  have hdeg : f.natDegree = ∑ P ∈ nf.toFinset, nf.count P * P.natDegree := by
    conv_lhs => rw [← hprod]
    rw [natDegree_multiset_prod_of_monic nf (fun P hP => ((hmem P).mp hP).2.1),
      Finset.sum_multiset_map_count]
    simp only [smul_eq_mul]
  have hpow : ∀ P ∈ irreducibleMonics k s, ∀ m, P ^ m ∣ f ↔ m ≤ nf.count P := by
    intro P hP m
    rw [mem_irreducibleMonics] at hP
    rw [pow_dvd_iff_le_emultiplicity,
      UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors hP.2.1 hf0,
      hP.1.normalize_eq_self, Nat.cast_le]
  have hcount_le : ∀ P ∈ irreducibleMonics k s, nf.count P ≤ s := by
    intro P hP
    have h1 : P ^ nf.count P ∣ f := (hpow P hP _).mpr le_rfl
    have h2 := Polynomial.natDegree_le_of_dvd h1 hf0
    rw [mem_irreducibleMonics] at hP
    rw [hP.1.natDegree_pow] at h2
    have h3 : 0 < P.natDegree := hP.2.1.natDegree_pos
    calc nf.count P ≤ nf.count P * P.natDegree := Nat.le_mul_of_pos_right _ h3
      _ ≤ f.natDegree := h2
      _ ≤ s := hs
  have hinner : ∀ P ∈ irreducibleMonics k s,
      (∑ m ∈ Finset.Icc 1 s, if P ^ m ∣ f then P.natDegree else 0) =
        nf.count P * P.natDegree := by
    intro P hP
    have hfilter : (Finset.Icc 1 s).filter (fun m => P ^ m ∣ f) = Finset.Icc 1 (nf.count P) := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_Icc, hpow P hP m]
      have := hcount_le P hP
      omega
    rw [← Finset.sum_filter, hfilter, Finset.sum_const, Nat.card_Icc, smul_eq_mul,
      Nat.add_sub_cancel]
  rw [Finset.sum_congr rfl hinner, hdeg]
  refine Finset.sum_subset ?_ ?_
  · intro P hP
    rw [Multiset.mem_toFinset, hmem] at hP
    rw [mem_irreducibleMonics]
    exact ⟨hP.2.1, hP.1, (Polynomial.natDegree_le_of_dvd hP.2.2 hf0).trans hs⟩
  · intro P _ hP
    rw [Multiset.mem_toFinset] at hP
    rw [Multiset.count_eq_zero_of_notMem hP, zero_mul]

end Monics

/-- Reindexing the multiples `j = m * d` of `d` in `[1, s]` by the cofactor `m`. -/
theorem sum_Icc_ite_dvd_eq_sum_Icc_ite_mul_le {M : Type*} [AddCommMonoid M] {d : ℕ} (hd : 0 < d)
    (s : ℕ) (G : ℕ → ℕ → M) :
    ∑ j ∈ Finset.Icc 1 s, (if d ∣ j then G (j / d) j else 0) =
      ∑ m ∈ Finset.Icc 1 s, if m * d ≤ s then G m (m * d) else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_nbij' (fun j => j / d) (fun m => m * d) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj ⊢
    obtain ⟨⟨h1, h2⟩, c, rfl⟩ := hj
    rw [Nat.mul_div_cancel_left _ hd]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact Nat.pos_of_ne_zero (by rintro rfl; simp at h1)
    · exact (Nat.le_mul_of_pos_left c hd).trans h2
    · rwa [mul_comm]
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    exact ⟨⟨Nat.mul_pos hm.1.1 hd, hm.2⟩, dvd_mul_left d m⟩
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj
    exact Nat.div_mul_cancel hj.2
  · intro m _
    exact Nat.mul_div_cancel m hd
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_Icc] at hj
    rw [Nat.div_mul_cancel hj.2]

/-! ### The Newton recursion for a multiplicative function on monic polynomials -/

section Recursion

variable {k : Type*} [Field k] [Finite k] {R : Type*} [CommRing R] (lam : k[X] → R)

/-- The sum of `lam` over the monic polynomials of degree `d`. -/
noncomputable def monicSum (d : ℕ) : R :=
  ∑ f ∈ monicsOfDegree k d, lam f

/-- The weighted prime power sum `∑ deg P • lam P ^ (j / deg P)` over the monic irreducible
polynomials `P` whose degree divides `j`. -/
noncomputable def primePowerSum (j : ℕ) : R :=
  ∑ P ∈ irreducibleMonicsDvd k j, P.natDegree • lam P ^ (j / P.natDegree)

theorem monicSum_zero (h1 : lam 1 = 1) : monicSum lam 0 = 1 := by
  rw [monicSum, monicsOfDegree_zero, Finset.sum_singleton, h1]

/-- **Newton recursion.** For a function `lam` that is multiplicative on monic polynomials,
`s • S_s = ∑_{1 ≤ j ≤ s} N_j * S_{s - j}`, where `S_d` is the sum of `lam` over the monic
polynomials of degree `d` and `N_j` is the weighted prime power sum. This is the coefficient form
of the logarithmic derivative of the Euler product of `∑ lam f * T ^ deg f`. -/
theorem natDegree_smul_monicSum
    (hmul : ∀ f g : k[X], f.Monic → g.Monic → lam (f * g) = lam f * lam g) (h1 : lam 1 = 1)
    (s : ℕ) :
    s • monicSum lam s = ∑ j ∈ Finset.Icc 1 s, primePowerSum lam j * monicSum lam (s - j) := by
  classical
  have hpow : ∀ P : k[X], P.Monic → ∀ m : ℕ, lam (P ^ m) = lam P ^ m := by
    intro P hP m
    induction m with
    | zero => rw [pow_zero, pow_zero, h1]
    | succ m ih => rw [pow_succ, hmul _ _ (hP.pow m) hP, ih, pow_succ]
  have hL : s • monicSum lam s = ∑ P ∈ irreducibleMonics k s, ∑ m ∈ Finset.Icc 1 s,
      if m * P.natDegree ≤ s then
        P.natDegree • (lam P ^ m * monicSum lam (s - m * P.natDegree)) else 0 := by
    calc s • monicSum lam s = ∑ f ∈ monicsOfDegree k s, s • lam f := by
          rw [monicSum, Finset.smul_sum]
      _ = ∑ f ∈ monicsOfDegree k s, ∑ P ∈ irreducibleMonics k s, ∑ m ∈ Finset.Icc 1 s,
            if P ^ m ∣ f then P.natDegree • lam f else 0 := by
          refine Finset.sum_congr rfl fun f hf => ?_
          rw [mem_monicsOfDegree] at hf
          have key : s = ∑ P ∈ irreducibleMonics k s, ∑ m ∈ Finset.Icc 1 s,
              if P ^ m ∣ f then P.natDegree else 0 := by
            rw [← natDegree_eq_sum_irreducibleMonics hf.1 hf.2.le, hf.2]
          conv_lhs => rw [key]
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun P _ => ?_
          rw [Finset.sum_smul]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [ite_smul, zero_smul]
      _ = ∑ P ∈ irreducibleMonics k s, ∑ m ∈ Finset.Icc 1 s, ∑ f ∈ monicsOfDegree k s,
            if P ^ m ∣ f then P.natDegree • lam f else 0 := by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun P _ => Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun P hP => Finset.sum_congr rfl fun m _ => ?_
          rw [mem_irreducibleMonics] at hP
          rw [sum_monicsOfDegree_ite_dvd (fun f => P.natDegree • lam f) (hP.1.pow m) s,
            hP.1.natDegree_pow]
          refine if_congr Iff.rfl ?_ rfl
          rw [monicSum, Finset.mul_sum, Finset.smul_sum]
          refine Finset.sum_congr rfl fun e he => ?_
          rw [mem_monicsOfDegree] at he
          rw [hmul _ _ (hP.1.pow m) he.1, hpow P hP.1]
  have hR : ∀ j ∈ Finset.Icc 1 s, primePowerSum lam j * monicSum lam (s - j) =
      ∑ P ∈ irreducibleMonics k s, if P.natDegree ∣ j then
        P.natDegree • (lam P ^ (j / P.natDegree) * monicSum lam (s - j)) else 0 := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [primePowerSum, Finset.sum_mul, ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun P _ => smul_mul_assoc _ _ _
    ext P
    simp only [mem_irreducibleMonicsDvd, Finset.mem_filter, mem_irreducibleMonics,
      Nat.mem_divisors]
    constructor
    · rintro ⟨hm, hi, hd, -⟩
      exact ⟨⟨hm, hi, (Nat.le_of_dvd (by omega) hd).trans hj.2⟩, hd⟩
    · rintro ⟨⟨hm, hi, -⟩, hd⟩
      exact ⟨hm, hi, hd, by omega⟩
  rw [hL, Finset.sum_congr rfl hR]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun P hP => ?_
  rw [mem_irreducibleMonics] at hP
  exact (sum_Icc_ite_dvd_eq_sum_Icc_ite_mul_le hP.2.1.natDegree_pos s
    (fun m j => P.natDegree • (lam P ^ m * monicSum lam (s - j)))).symm

/-- **Newton's identities for a linear generating function.** If `lam` is multiplicative on monic
polynomials and its sums `S_d` over the monic polynomials of degree `d` vanish for `d ≥ 2`, so
that `∑ lam f * T ^ deg f = 1 + S_1 * T`, then the weighted prime power sums are
`N_s = (-1) ^ (s - 1) * S_1 ^ s`, that is, `-N_s = (-S_1) ^ s`, for all `s ≥ 1`. -/
theorem neg_primePowerSum_eq_pow
    (hmul : ∀ f g : k[X], f.Monic → g.Monic → lam (f * g) = lam f * lam g) (h1 : lam 1 = 1)
    (hS : ∀ d, 2 ≤ d → monicSum lam d = 0) {s : ℕ} (hs : s ≠ 0) :
    -primePowerSum lam s = (-monicSum lam 1) ^ s := by
  have h0 : monicSum lam 0 = 1 := monicSum_zero lam h1
  have hone : primePowerSum lam 1 = monicSum lam 1 := by
    have h := natDegree_smul_monicSum lam hmul h1 1
    rw [one_smul, Finset.Icc_self, Finset.sum_singleton, Nat.sub_self, h0, mul_one] at h
    exact h.symm
  have hstep : ∀ t : ℕ,
      primePowerSum lam (t + 1 + 1) = -(primePowerSum lam (t + 1) * monicSum lam 1) := by
    intro t
    have h := natDegree_smul_monicSum lam hmul h1 (t + 1 + 1)
    have hsum : ∑ j ∈ Finset.Icc 1 (t + 1 + 1), primePowerSum lam j * monicSum lam (t + 1 + 1 - j) =
        primePowerSum lam (t + 1) * monicSum lam 1 + primePowerSum lam (t + 1 + 1) := by
      rw [Finset.sum_eq_add_of_mem (t + 1) (t + 1 + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
        (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) (by omega)]
      · rw [show t + 1 + 1 - (t + 1) = 1 by omega, Nat.sub_self, h0, mul_one]
      · intro c hc hne
        rw [Finset.mem_Icc] at hc
        rw [hS _ (by omega), mul_zero]
    rw [hS (t + 1 + 1) (by omega), smul_zero, hsum] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  have key : ∀ t : ℕ, -primePowerSum lam (t + 1) = (-monicSum lam 1) ^ (t + 1) := by
    intro t
    induction t with
    | zero => rw [zero_add, hone, pow_one]
    | succ t ih => rw [hstep t, neg_neg, pow_succ, ← ih]; ring
  obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs
  exact key t

end Recursion

end SimultaneousPrimitiveRoots.Unconditional.Arithmetic
