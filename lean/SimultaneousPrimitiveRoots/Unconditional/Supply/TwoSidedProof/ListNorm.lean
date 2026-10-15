module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.EndpointSquaresProof
public import SimultaneousPrimitiveRoots.Unconditional.Supply.CoreSanity
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Pairing.Fiber
public import Mathlib.RingTheory.Coprime.Lemmas

/-!
# The normalized list sum (cor:list-norm)

`[P-06:0262–0285]`: "For a fixed ordered physical list with squarefree product `P`,
`n_* ∣ n/P`. … the normalized list sum satisfies
`∏_g V_g^{-M} ∑_{physical lists} 1/P ≤ ∏_g (∑_{p ∈ 𝒫_g} 1/(V_g p))^M = 1`. … It is essential here
to keep `q_0^{(ω_P(n) - M s_P)/2} ≤ 1` intact."

* `freePart_mul_dvd`, `norm_core_mul_le`: if every prime factor of `m` is active, then
  `(m v)_* ∣ v`, so `|G(m v)| ≤ L^C τ(v)^{⌈C⌉}`.
* `listLabel`, `listProd`: the labels of a list of all groups and their product `P`;
  `listProd_dvd_of_isPhys`: at a physical state `(n, 𝐩)` the labels are distinct primes dividing
  `n`, so `P ∣ n`; `stateMass_mul_inv_listProd`: `∏_g V_g^{-M} / P = ∏_{g,i} μ_g(p_{g,i})`, and
  these weights have total mass one (`sum_listWeight`).
* `sum_mul_unitNormSq_le`: if `∑_{n ∈ W, m ∣ n} a(n) ≤ R/m` for every product `m` of group primes,
  then `∑_{n ∈ W} a(n) ‖u_n‖² ≤ R`.
* `dampedMass_le_unitNormSq`, `sum_mul_dampedMass_le`: the same with the damped mass of the active
  groups of [P] §6, because the damping is at most one at a position that carries a physical
  state.
* `sum_wideWindow_dvd_le`: the multiples of `m` in the enlarged dyad `[X, 4X)` are the `m v` with
  `1 ≤ v ≤ 4X/m`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference

noncomputable section

/-! ### The free part of a multiple -/

/-- `(m v)_* ∣ v` if every prime factor of `m` is in `A`. -/
theorem freePart_mul_dvd {A : Finset ℕ} {m v : ℕ} (hm0 : m ≠ 0) (hv : v ≠ 0)
    (hm : ∀ p : ℕ, p.Prime → p ∣ m → p ∈ A) : freePart A (m * v) ∣ v := by
  rw [← Nat.factorization_le_iff_dvd (freePart_pos A (m * v)).ne' hv, freePart_factorization]
  refine Finsupp.le_def.mpr fun p => ?_
  rw [Finsupp.filter_apply]
  by_cases hp : p ∈ A
  · rw [if_neg (not_not.mpr hp)]
    exact Nat.zero_le _
  · have h0 : m.factorization p = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      by_cases hpp : p.Prime
      · exact Or.inr (Or.inl fun hd => hp (hm p hpp hd))
      · exact Or.inl hpp
    rw [if_pos hp, Nat.factorization_mul hm0 hv, Finsupp.add_apply, h0, zero_add]

/-- `|G(m v)| ≤ L^C τ(v)^k` with `k = ⌈C⌉₊`, for `m, v ≥ 1` with all prime factors of `m` active:
`(m v)_* ∣ v`. The exponent `C` may have any sign. -/
theorem norm_core_mul_le {𝔊 : ActiveGroups} {x C : ℝ} {G : ℕ → ℂ} (hG : CoreAdmissible 𝔊 x C G)
    (hL : 0 ≤ Real.log x) {m v : ℕ} (hm0 : 0 < m) (hv : 0 < v)
    (hm : ∀ p : ℕ, p.Prime → p ∣ m → p ∈ 𝔊.allPrimes) :
    ‖G (m * v)‖ ≤ Real.log x ^ C * (v.divisors.card : ℝ) ^ ⌈C⌉₊ := by
  have h1 : (1 : ℝ) ≤ ((freePart 𝔊.allPrimes (m * v)).divisors.card : ℝ) :=
    Nat.one_le_cast.mpr (Finset.one_le_card.mpr
      ⟨1, Nat.one_mem_divisors.mpr (freePart_pos 𝔊.allPrimes (m * v)).ne'⟩)
  have h2 : ((freePart 𝔊.allPrimes (m * v)).divisors.card : ℝ) ≤ (v.divisors.card : ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card
      (Nat.divisors_subset_of_dvd hv.ne' (freePart_mul_dvd hm0.ne' hv.ne' hm)))
  have h3 : ((freePart 𝔊.allPrimes (m * v)).divisors.card : ℝ) ^ C ≤
      (v.divisors.card : ℝ) ^ ⌈C⌉₊ :=
    calc ((freePart 𝔊.allPrimes (m * v)).divisors.card : ℝ) ^ C
        ≤ ((freePart 𝔊.allPrimes (m * v)).divisors.card : ℝ) ^ ((⌈C⌉₊ : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil C)
      _ = ((freePart 𝔊.allPrimes (m * v)).divisors.card : ℝ) ^ ⌈C⌉₊ := Real.rpow_natCast _ _
      _ ≤ (v.divisors.card : ℝ) ^ ⌈C⌉₊ := pow_le_pow_left₀ (zero_le_one.trans h1) h2 _
  exact (hG.growth (m * v) (Nat.mul_pos hm0 hv)).trans
    (mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hL C))

/-! ### The labels of a list and their product -/

/-- The weight `∏_{g,i} μ_g(p_{g,i})` of a label list is `∏_g V_g^{-M}` divided by the product
of the labels. -/
theorem idealWeight_eq_inv {ι : Type} [Fintype ι] (𝒬 : ι → Finset ℕ) (J ℓ : ℕ)
    (p : LabelList 𝒬 J ℓ) :
    idealWeight 𝒬 J ℓ p =
      (∏ g, (Graph.primeGroupReciprocalMass (𝒬 g) ^ (J + ℓ))⁻¹) *
        (((∏ g, ∏ i, (p g i : ℕ) : ℕ) : ℝ))⁻¹ := by
  unfold idealWeight
  rw [Nat.cast_prod, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [Nat.cast_prod, ← Finset.prod_inv_distrib]
  have h : ∀ i ∈ (Finset.univ : Finset (Slot J ℓ)),
      Graph.primeGroupLaw (𝒬 g) (p g i) =
        (Graph.primeGroupReciprocalMass (𝒬 g))⁻¹ * (((p g i : ℕ) : ℝ))⁻¹ := fun i _ => by
    unfold Graph.primeGroupLaw
    rw [one_div, mul_inv]
  rw [Finset.prod_congr rfl h, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    card_slot, inv_pow]

section Lists

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ}

/-- The labels of a list of all groups, indexed by the pairs (group, slot). -/
def listLabel (x : Lists 𝒢 J ℓ) : (S × Slot J ℓ) ⊕ (B × Slot J ℓ) → ℕ :=
  Sum.elim (fun a => (x.1 a.1 a.2 : ℕ)) (fun b => (x.2 b.1 b.2 : ℕ))

/-- The product `P` of all the labels of a list. -/
def listProd (x : Lists 𝒢 J ℓ) : ℕ := ∏ k, listLabel x k

omit [DecidableEq S] [DecidableEq B] in
theorem listProd_eq (x : Lists 𝒢 J ℓ) :
    listProd x = (∏ g, ∏ i, (x.1 g i : ℕ)) * ∏ g, ∏ i, (x.2 g i : ℕ) := by
  have h1 : listProd x =
      (∏ a : S × Slot J ℓ, (x.1 a.1 a.2 : ℕ)) * ∏ b : B × Slot J ℓ, (x.2 b.1 b.2 : ℕ) :=
    Fintype.prod_sum_type (listLabel x)
  have h2 : ∏ a : S × Slot J ℓ, (x.1 a.1 a.2 : ℕ) = ∏ g, ∏ i, (x.1 g i : ℕ) :=
    Fintype.prod_prod_type' fun g i => (x.1 g i : ℕ)
  have h3 : ∏ b : B × Slot J ℓ, (x.2 b.1 b.2 : ℕ) = ∏ g, ∏ i, (x.2 g i : ℕ) :=
    Fintype.prod_prod_type' fun g i => (x.2 g i : ℕ)
  rw [h1, h2, h3]

omit [DecidableEq S] [DecidableEq B] in
/-- **`∏_g V_g^{-M} / P` is the product of the laws `μ_g` at the labels.** -/
theorem stateMass_mul_inv_listProd (x : Lists 𝒢 J ℓ) :
    stateMass 𝒢 J ℓ * ((listProd x : ℕ) : ℝ)⁻¹ =
      idealWeight 𝒢.small J ℓ x.1 * idealWeight 𝒢.big J ℓ x.2 := by
  rw [idealWeight_eq_inv, idealWeight_eq_inv, listProd_eq, Nat.cast_mul, mul_inv]
  unfold stateMass
  ring

/-- **(cor:list-norm)**: the weights `∏_{g,i} μ_g(p_{g,i})` of the lists of all groups have total
mass one. -/
theorem sum_listWeight
    (hS : ∀ g, ∑ q ∈ 𝒢.small g, Graph.primeGroupLaw (𝒢.small g) q = 1)
    (hB : ∀ g, ∑ q ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) q = 1) :
    ∑ x : Lists 𝒢 J ℓ, idealWeight 𝒢.small J ℓ x.1 * idealWeight 𝒢.big J ℓ x.2 = 1 := by
  have h1 : ∑ x : Lists 𝒢 J ℓ, idealWeight 𝒢.small J ℓ x.1 * idealWeight 𝒢.big J ℓ x.2 =
      ∑ a : LabelList 𝒢.small J ℓ, ∑ b : LabelList 𝒢.big J ℓ,
        idealWeight 𝒢.small J ℓ a * idealWeight 𝒢.big J ℓ b :=
    Fintype.sum_prod_type' fun a b => idealWeight 𝒢.small J ℓ a * idealWeight 𝒢.big J ℓ b
  rw [h1, ← Finset.sum_mul_sum, sum_idealWeight hS, sum_idealWeight hB, mul_one]

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- The labels of a list are primes. -/
theorem listLabel_prime (hpS : ∀ g, ∀ p ∈ 𝒢.small g, p.Prime)
    (hpB : ∀ g, ∀ p ∈ 𝒢.big g, p.Prime) (x : Lists 𝒢 J ℓ) (k : (S × Slot J ℓ) ⊕ (B × Slot J ℓ)) :
    (listLabel x k).Prime := by
  rcases k with ⟨g, i⟩ | ⟨g, i⟩
  · exact hpS g _ (x.1 g i).2
  · exact hpB g _ (x.2 g i).2

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- The labels of a list with distinct labels in every group are distinct, the groups being
pairwise disjoint. -/
theorem listLabel_injective {x : Lists 𝒢 J ℓ} (h1 : ∀ g, Function.Injective (x.1 g))
    (h2 : ∀ g, Function.Injective (x.2 g))
    (hSS : ∀ g g', g ≠ g' → Disjoint (𝒢.small g) (𝒢.small g'))
    (hBB : ∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g'))
    (hSB : ∀ g g', Disjoint (𝒢.small g) (𝒢.big g')) : Function.Injective (listLabel x) := by
  rintro (⟨g, i⟩ | ⟨g, i⟩) (⟨g', i'⟩ | ⟨g', i'⟩) h
  · have h' : (x.1 g i : ℕ) = (x.1 g' i' : ℕ) := h
    by_cases hg : g = g'
    · subst hg
      have hi : i = i' := h1 g (Subtype.ext h')
      rw [hi]
    · exfalso
      have ha : (x.1 g i : ℕ) ∈ 𝒢.small g := (x.1 g i).2
      have hb : (x.1 g i : ℕ) ∈ 𝒢.small g' := by
        rw [h']
        exact (x.1 g' i').2
      exact Finset.disjoint_left.mp (hSS g g' hg) ha hb
  · exfalso
    have h' : (x.1 g i : ℕ) = (x.2 g' i' : ℕ) := h
    have ha : (x.1 g i : ℕ) ∈ 𝒢.small g := (x.1 g i).2
    have hb : (x.1 g i : ℕ) ∈ 𝒢.big g' := by
      rw [h']
      exact (x.2 g' i').2
    exact Finset.disjoint_left.mp (hSB g g') ha hb
  · exfalso
    have h' : (x.2 g i : ℕ) = (x.1 g' i' : ℕ) := h
    have ha : (x.2 g i : ℕ) ∈ 𝒢.big g := (x.2 g i).2
    have hb : (x.2 g i : ℕ) ∈ 𝒢.small g' := by
      rw [h']
      exact (x.1 g' i').2
    exact Finset.disjoint_left.mp (hSB g' g) hb ha
  · have h' : (x.2 g i : ℕ) = (x.2 g' i' : ℕ) := h
    by_cases hg : g = g'
    · subst hg
      have hi : i = i' := h2 g (Subtype.ext h')
      rw [hi]
    · exfalso
      have ha : (x.2 g i : ℕ) ∈ 𝒢.big g := (x.2 g i).2
      have hb : (x.2 g i : ℕ) ∈ 𝒢.big g' := by
        rw [h']
        exact (x.2 g' i').2
      exact Finset.disjoint_left.mp (hBB g g' hg) ha hb

omit [DecidableEq S] [DecidableEq B] in
/-- **At a physical state the product of the labels divides the position**: the labels are
distinct primes dividing `n`. -/
theorem listProd_dvd_of_isPhys {x : Lists 𝒢 J ℓ} {n : ℤ} (hx : IsPhys intPos n x)
    (hpS : ∀ g, ∀ p ∈ 𝒢.small g, p.Prime) (hpB : ∀ g, ∀ p ∈ 𝒢.big g, p.Prime)
    (hSS : ∀ g g', g ≠ g' → Disjoint (𝒢.small g) (𝒢.small g'))
    (hBB : ∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g'))
    (hSB : ∀ g g', Disjoint (𝒢.small g) (𝒢.big g')) : ((listProd x : ℕ) : ℤ) ∣ n := by
  have hinj := listLabel_injective hx.1 hx.2.1 hSS hBB hSB
  have hdvd : ∀ k, ((listLabel x k : ℕ) : ℤ) ∣ n := by
    rintro (⟨g, i⟩ | ⟨g, i⟩)
    · exact hx.2.2.1 g i
    · exact hx.2.2.2 g i
  have hcop : Pairwise (Function.onFun IsCoprime fun k => ((listLabel x k : ℕ) : ℤ)) := by
    intro k k' hkk'
    exact Nat.isCoprime_iff_coprime.mpr
      ((Nat.coprime_primes (listLabel_prime hpS hpB x k) (listLabel_prime hpS hpB x k')).mpr
        (hinj.ne hkk'))
  have h : (∏ k, ((listLabel x k : ℕ) : ℤ)) ∣ n := Fintype.prod_dvd_of_coprime hcop hdvd
  unfold listProd
  rw [Nat.cast_prod]
  exact h

omit [DecidableEq S] [DecidableEq B] in
/-- Every prime factor of the product of the labels is a group prime. -/
theorem prime_dvd_listProd (hpS : ∀ g, ∀ p ∈ 𝒢.small g, p.Prime)
    (hpB : ∀ g, ∀ p ∈ 𝒢.big g, p.Prime) {x : Lists 𝒢 J ℓ} {p : ℕ} (hp : p.Prime)
    (hd : p ∣ listProd x) : (∃ g, p ∈ 𝒢.small g) ∨ ∃ g, p ∈ 𝒢.big g := by
  unfold listProd at hd
  obtain ⟨k, -, hk⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hd
  rcases k with ⟨g, i⟩ | ⟨g, i⟩
  · have hk' : p ∣ (x.1 g i : ℕ) := hk
    have he : p = (x.1 g i : ℕ) :=
      (Nat.prime_dvd_prime_iff_eq hp (hpS g _ (x.1 g i).2)).mp hk'
    refine Or.inl ⟨g, ?_⟩
    rw [he]
    exact (x.1 g i).2
  · have hk' : p ∣ (x.2 g i : ℕ) := hk
    have he : p = (x.2 g i : ℕ) :=
      (Nat.prime_dvd_prime_iff_eq hp (hpB g _ (x.2 g i).2)).mp hk'
    refine Or.inr ⟨g, ?_⟩
    rw [he]
    exact (x.2 g i).2

/-- **The endpoint norm from sums over multiples** (`[P-06:0262–0285]`): for pairwise disjoint
groups of primes with the laws `μ_g` of total mass one, a set `W` of positions and `a ≥ 0`, if

`∑_{n ∈ W, m ∣ n} a(n) ≤ R / m`

for every `m ≥ 1` all of whose prime factors are group primes, then
`∑_{n ∈ W} a(n) ‖u_n‖² ≤ R`. -/
theorem sum_mul_unitNormSq_le (hpS : ∀ g, ∀ p ∈ 𝒢.small g, p.Prime)
    (hpB : ∀ g, ∀ p ∈ 𝒢.big g, p.Prime)
    (hSS : ∀ g g', g ≠ g' → Disjoint (𝒢.small g) (𝒢.small g'))
    (hBB : ∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g'))
    (hSB : ∀ g g', Disjoint (𝒢.small g) (𝒢.big g'))
    (hlS : ∀ g, ∑ q ∈ 𝒢.small g, Graph.primeGroupLaw (𝒢.small g) q = 1)
    (hlB : ∀ g, ∑ q ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) q = 1)
    (W : Finset ℤ) (a : ℤ → ℝ) (ha : ∀ n, 0 ≤ a n) {R : ℝ}
    (hsum : ∀ m : ℕ, 0 < m →
      (∀ p : ℕ, p.Prime → p ∣ m → (∃ g, p ∈ 𝒢.small g) ∨ ∃ g, p ∈ 𝒢.big g) →
        ∑ n ∈ W.filter (fun n : ℤ => (m : ℤ) ∣ n), a n ≤ R / (m : ℝ)) :
    ∑ n ∈ W, a n * unitNormSq intPos 𝒢 J ℓ n ≤ R := by
  have hsM : 0 ≤ stateMass 𝒢 J ℓ := Pairing.stateMass_nonneg 𝒢 J ℓ
  -- one list
  have hlist : ∀ x : Lists 𝒢 J ℓ,
      ∑ n ∈ W, a n * Pairing.physWeight intPos 𝒢 J ℓ (n, x) ≤
        R * (idealWeight 𝒢.small J ℓ x.1 * idealWeight 𝒢.big J ℓ x.2) := by
    intro x
    have hm0 : 0 < listProd x :=
      Finset.prod_pos fun k _ => (listLabel_prime hpS hpB x k).pos
    have hterm : ∀ n ∈ W, a n * Pairing.physWeight intPos 𝒢 J ℓ (n, x) ≤
        if ((listProd x : ℕ) : ℤ) ∣ n then stateMass 𝒢 J ℓ * a n else 0 := by
      intro n _
      by_cases hph : IsPhys intPos n x
      · rw [Pairing.physWeight_of_isPhys hph,
          if_pos (listProd_dvd_of_isPhys hph hpS hpB hSS hBB hSB)]
        exact le_of_eq (mul_comm _ _)
      · rw [Pairing.physWeight_of_not_isPhys hph, mul_zero]
        split_ifs
        · exact mul_nonneg hsM (ha n)
        · exact le_rfl
    calc ∑ n ∈ W, a n * Pairing.physWeight intPos 𝒢 J ℓ (n, x)
        ≤ ∑ n ∈ W, if ((listProd x : ℕ) : ℤ) ∣ n then stateMass 𝒢 J ℓ * a n else 0 :=
          Finset.sum_le_sum hterm
      _ = stateMass 𝒢 J ℓ *
            ∑ n ∈ W.filter (fun n : ℤ => ((listProd x : ℕ) : ℤ) ∣ n), a n := by
          rw [← Finset.sum_filter, Finset.mul_sum]
      _ ≤ stateMass 𝒢 J ℓ * (R / ((listProd x : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left
            (hsum (listProd x) hm0 fun p hp hd => prime_dvd_listProd hpS hpB hp hd) hsM
      _ = R * (idealWeight 𝒢.small J ℓ x.1 * idealWeight 𝒢.big J ℓ x.2) := by
          rw [← stateMass_mul_inv_listProd x]
          ring
  calc ∑ n ∈ W, a n * unitNormSq intPos 𝒢 J ℓ n
      = ∑ n ∈ W, ∑ x : Lists 𝒢 J ℓ, a n * Pairing.physWeight intPos 𝒢 J ℓ (n, x) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        exact (congrArg (fun t => a n * t) (Pairing.unitNormSq_eq_sum intPos 𝒢 J ℓ n)).trans
          (Finset.mul_sum _ _ _)
    _ = ∑ x : Lists 𝒢 J ℓ, ∑ n ∈ W, a n * Pairing.physWeight intPos 𝒢 J ℓ (n, x) :=
        Finset.sum_comm
    _ ≤ ∑ x : Lists 𝒢 J ℓ, R * (idealWeight 𝒢.small J ℓ x.1 * idealWeight 𝒢.big J ℓ x.2) :=
        Finset.sum_le_sum fun x _ => hlist x
    _ = R := by rw [← Finset.mul_sum, sum_listWeight hlS hlB, mul_one]

end Lists

/-! ### The damped mass of the active groups -/

/-- "It is essential here to keep `q_0^{(ω_P(n) - M s_P)/2} ≤ 1` intact": the damped mass is at
most `‖u_n‖²`, because the damping is at most one at a position with a physical state, and
`‖u_n‖² = 0` at the others. -/
theorem dampedMass_le_unitNormSq (𝔊 : ActiveGroups) (J : ℕ) {q₀ : ℝ} (h0 : 0 < q₀)
    (h1 : q₀ ≤ 1) (n : ℤ) :
    dampedMass 𝔊 J q₀ n ≤ unitNormSq intPos (groupFamily 𝔊) J 1 n := by
  have hU : 0 ≤ unitNormSq intPos (groupFamily 𝔊) J 1 n := by
    unfold unitNormSq
    exact mul_nonneg (Pairing.stateMass_nonneg _ _ _) (Nat.cast_nonneg _)
  unfold dampedMass
  by_cases hex : ∃ x : Lists (groupFamily 𝔊) J 1, IsPhys intPos n x
  · obtain ⟨x, hx⟩ := hex
    have hd1 : damping intPos (groupFamily 𝔊) J 1 q₀ n ≤ 1 := Schur.damping_le_one h0 h1 hx
    have hd0 : 0 < damping intPos (groupFamily 𝔊) J 1 q₀ n :=
      Schur.damping_pos intPos (groupFamily 𝔊) J 1 h0 n
    have hd2 : damping intPos (groupFamily 𝔊) J 1 q₀ n ^ 2 ≤ 1 := pow_le_one₀ hd0.le hd1
    calc damping intPos (groupFamily 𝔊) J 1 q₀ n ^ 2 * unitNormSq intPos (groupFamily 𝔊) J 1 n
        ≤ 1 * unitNormSq intPos (groupFamily 𝔊) J 1 n := mul_le_mul_of_nonneg_right hd2 hU
      _ = unitNormSq intPos (groupFamily 𝔊) J 1 n := one_mul _
  · have hz : unitNormSq intPos (groupFamily 𝔊) J 1 n = 0 :=
      (Pairing.unitNormSq_eq_sum intPos (groupFamily 𝔊) J 1 n).trans
        (Finset.sum_eq_zero fun x _ => Pairing.physWeight_of_not_isPhys fun hx => hex ⟨x, hx⟩)
    rw [hz, mul_zero]

/-- **The endpoint norm with the damped mass of admissible active groups**: if
`∑_{n ∈ W, m ∣ n} a(n) ≤ R / m` for every `m ≥ 1` all of whose prime factors are active, then
`∑_{n ∈ W} a(n) · dampedMass(n) ≤ R`. -/
theorem sum_mul_dampedMass_le {P : ActiveGroupConstants} {x : ℝ} {𝔊 : ActiveGroups}
    (h𝔊 : 𝔊.Admissible P x) (J : ℕ) {q₀ : ℝ} (h0 : 0 < q₀) (h1 : q₀ < 1) (W : Finset ℤ)
    (a : ℤ → ℝ) (ha : ∀ n, 0 ≤ a n) {R : ℝ}
    (hsum : ∀ m : ℕ, 0 < m → (∀ p : ℕ, p.Prime → p ∣ m → p ∈ 𝔊.allPrimes) →
      ∑ n ∈ W.filter (fun n : ℤ => (m : ℤ) ∣ n), a n ≤ R / (m : ℝ)) :
    ∑ n ∈ W, a n * dampedMass 𝔊 J q₀ n ≤ R := by
  have hle : ∑ n ∈ W, a n * dampedMass 𝔊 J q₀ n ≤
      ∑ n ∈ W, a n * unitNormSq intPos (groupFamily 𝔊) J 1 n :=
    Finset.sum_le_sum fun n _ =>
      mul_le_mul_of_nonneg_left (dampedMass_le_unitNormSq 𝔊 J h0 h1.le n) (ha n)
  refine hle.trans (sum_mul_unitNormSq_le (𝒢 := groupFamily 𝔊) ?_ ?_ ?_ ?_ ?_ ?_ ?_ W a ha ?_)
  · exact fun g p hp => h𝔊.prime (Sum.inl g) p hp
  · exact fun g p hp => h𝔊.prime (Sum.inr g) p hp
  · exact fun g g' hgg' => h𝔊.disjoint (Sum.inl g) (Sum.inl g') fun e => hgg' (Sum.inl.inj e)
  · exact fun g g' hgg' => h𝔊.disjoint (Sum.inr g) (Sum.inr g') fun e => hgg' (Sum.inr.inj e)
  · exact fun g g' => h𝔊.disjoint (Sum.inl g) (Sum.inr g') Sum.inl_ne_inr
  · exact (primeGroupsOf h𝔊 q₀ h0 h1).small_law_sum
  · exact (primeGroupsOf h𝔊 q₀ h0 h1).big_law_sum
  · intro m hm hfac
    refine hsum m hm fun p hp hd => ?_
    rcases hfac p hp hd with ⟨g, hg⟩ | ⟨g, hg⟩
    · exact Finset.mem_biUnion.mpr ⟨Sum.inl g, Finset.mem_univ _, hg⟩
    · exact Finset.mem_biUnion.mpr ⟨Sum.inr g, Finset.mem_univ _, hg⟩

/-! ### The multiples of `m` in the enlarged dyad -/

/-- The multiples of `m ≥ 1` in `[X, 4X)`, `X ≥ 1`, are among the `m v` with
`1 ≤ v ≤ 4X/m`. -/
theorem sum_wideWindow_dvd_le {a : ℤ → ℝ} (ha : ∀ n, 0 ≤ a n) {X : ℝ} (hX : 1 ≤ X) {m : ℕ}
    (hm : 0 < m) :
    ∑ n ∈ (wideWindow X).filter (fun n : ℤ => (m : ℤ) ∣ n), a n ≤
      ∑ v ∈ Finset.Icc 1 ⌊4 * X / (m : ℝ)⌋₊, a ((m * v : ℕ) : ℤ) := by
  have hinj : Set.InjOn (fun v : ℕ => ((m * v : ℕ) : ℤ))
      (Finset.Icc 1 ⌊4 * X / (m : ℝ)⌋₊ : Finset ℕ) := by
    intro v _ w _ h
    exact Nat.eq_of_mul_eq_mul_left hm (Int.ofNat_inj.mp h)
  have himg : ∑ n ∈ (Finset.Icc 1 ⌊4 * X / (m : ℝ)⌋₊).image (fun v : ℕ => ((m * v : ℕ) : ℤ)),
      a n = ∑ v ∈ Finset.Icc 1 ⌊4 * X / (m : ℝ)⌋₊, a ((m * v : ℕ) : ℤ) :=
    Finset.sum_image hinj
  rw [← himg]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => ha n
  obtain ⟨hnW, hdvd⟩ := Finset.mem_filter.mp hn
  have hnW' : ⌈X⌉ ≤ n ∧ n < ⌈4 * X⌉ := Finset.mem_Ico.mp hnW
  have hX1 : (1 : ℤ) ≤ ⌈X⌉ := Int.one_le_ceil_iff.mpr (lt_of_lt_of_le one_pos hX)
  have hn1 : (1 : ℤ) ≤ n := hX1.trans hnW'.1
  have hnlt : (n : ℝ) < 4 * X := Int.lt_ceil.mp hnW'.2
  obtain ⟨k, hk⟩ := hdvd
  have hk0 : 0 < k := by
    by_contra hcon
    have hk' : k ≤ 0 := not_lt.mp hcon
    have hm' : (0 : ℤ) ≤ (m : ℤ) := Int.natCast_nonneg m
    nlinarith [mul_nonneg hm' (neg_nonneg.mpr hk')]
  have hkv : ((k.toNat : ℕ) : ℤ) = k := Int.toNat_of_nonneg hk0.le
  have hnv : ((m * k.toNat : ℕ) : ℤ) = n := by
    rw [Nat.cast_mul, hkv]
    exact hk.symm
  refine Finset.mem_image.mpr ⟨k.toNat, Finset.mem_Icc.mpr ⟨?_, ?_⟩, hnv⟩
  · omega
  · refine Nat.le_floor ?_
    rw [le_div_iff₀' (Nat.cast_pos.mpr hm)]
    have h : (n : ℝ) = (m : ℝ) * (k.toNat : ℝ) := by
      rw [← hnv, Int.cast_natCast, Nat.cast_mul]
    rw [← h]
    exact hnlt.le

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
