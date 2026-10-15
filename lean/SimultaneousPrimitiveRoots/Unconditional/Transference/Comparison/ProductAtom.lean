module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison.Scales
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The product atom bound (eq:ideal-product-atom)

Source: `verification/stage7-sources/S-03.tex`, lines 79–96 (`[S-03:0079–0096]`).

`productAtomBound : ProductAtomBound`: `ρ_Λ(n) = ℙ(P_Λ = n) ≤ L^κ / n`,
`κ = C₀ (log(m!) + m log max(1, v₋⁻¹))`.

"Disjointness of the prime groups and unique factorization give, on the support of this product,
`ρ_Λ(n) = (1/n) ∏_g k_g! / (V_g^{k_g} ∏_{p ∈ 𝒫_g} a_p!)` … each factor apart from `1/n` is at most
`m! max(1, v₋⁻¹)^m`, and there are at most `C₀ T` big groups."

* `Atom.auxWeight_eq` — every tuple with product `n` has probability `(∏_g V_g^{-k_g}) / n`.
* `Atom.card_fiber_eq` — unique factorization and disjointness of the groups: the number of slots
  of the group `g` carrying the prime `q ∈ 𝒫_g` is the multiplicity `a_q` of `q` in the product.
* `Atom.card_fiber_le` — hence two tuples with the same product differ by a permutation of the
  slots of each group (`Atom.exists_perm_of_card_fiber_eq`), and there are at most `∏_g k_g!`
  tuples with a given product. (The exact count is the multinomial `∏_g k_g! / ∏_p a_p!`; only the
  upper bound is used.)
* `m!^{|ℬ|} max(1, v₋⁻¹)^{m |ℬ|} ≤ L^κ` because `|ℬ| ≤ C₀ T` and `L^κ = exp(κ T)`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison

open scoped BigOperators ComplexConjugate

noncomputable section

namespace Atom

/-- Two functions on a finite type with the same fiber cardinalities differ by a permutation of
the domain. -/
theorem exists_perm_of_card_fiber_eq {ι α : Type} [Fintype ι] [DecidableEq α] (f f₀ : ι → α)
    (h : ∀ a, (Finset.univ.filter fun i => f i = a).card =
      (Finset.univ.filter fun i => f₀ i = a).card) :
    ∃ σ : Equiv.Perm ι, ∀ i, f₀ (σ i) = f i := by
  have hc : ∀ a, Fintype.card {i // f i = a} = Fintype.card {i // f₀ i = a} := fun a => by
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact h a
  exact ⟨Equiv.ofFiberEquiv fun a => Fintype.equivOfCardEq (hc a),
    fun i => Equiv.ofFiberEquiv_map _ i⟩

section Tuples

variable {P : GroupParams} {x : ℝ} {S B : Type} [Fintype S] [Fintype B] [DecidableEq B] {J : ℕ}

omit [DecidableEq B] in
/-- The probability of a label tuple: `(∏_g V_g^{-k_g}) / P_Λ`. -/
theorem auxWeight_eq (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) (t : AuxList big Λ) :
    auxWeight big Λ t =
      (∏ g, ((Graph.primeGroupReciprocalMass (big g))⁻¹) ^ (Λ g).card) *
        (((tupleProd Λ t : ℕ) : ℝ))⁻¹ := by
  unfold auxWeight tupleProd Graph.primeGroupLaw
  rw [Nat.cast_prod, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [Nat.cast_prod, ← Finset.prod_inv_distrib]
  have h1 : ∀ i : {i : Fin J // i ∈ Λ g},
      1 / (Graph.primeGroupReciprocalMass (big g) * (((t g i : ℕ) : ℕ) : ℝ)) =
        (Graph.primeGroupReciprocalMass (big g))⁻¹ * ((((t g i : ℕ) : ℕ) : ℝ))⁻¹ :=
    fun i => by rw [one_div, mul_inv]
  rw [Finset.prod_congr rfl fun i _ => h1 i, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_coe]

omit [DecidableEq B] in
/-- The multiplicity of a prime in the product of a label tuple. -/
theorem factorization_tupleProd (𝔊 : PrimeGroups P x S B) (Λ : B → Finset (Fin J))
    (t : AuxList 𝔊.big Λ) (q : ℕ) :
    (tupleProd Λ t).factorization q =
      ∑ g, ∑ i : {i : Fin J // i ∈ Λ g}, if (t g i : ℕ) = q then 1 else 0 := by
  unfold tupleProd
  have h0 : ∀ g ∈ (Finset.univ : Finset B),
      (∏ i : {i : Fin J // i ∈ Λ g}, (t g i : ℕ)) ≠ 0 :=
    fun g _ => Finset.prod_ne_zero_iff.mpr fun i _ => (𝔊.prime_big g (t g i) (t g i).2).ne_zero
  rw [Nat.factorization_prod_apply h0]
  refine Finset.sum_congr rfl fun g _ => ?_
  have h1 : ∀ i ∈ (Finset.univ : Finset {i : Fin J // i ∈ Λ g}), (t g i : ℕ) ≠ 0 :=
    fun i _ => (𝔊.prime_big g (t g i) (t g i).2).ne_zero
  rw [Nat.factorization_prod_apply h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(𝔊.prime_big g (t g i) (t g i).2).factorization, Finsupp.single_apply]

omit [DecidableEq B] in
/-- **Unique factorization and disjointness of the prime groups**: the number of slots of the
group `g` carrying the prime `q ∈ 𝒫_g` is the multiplicity of `q` in the product. -/
theorem card_fiber_eq (𝔊 : PrimeGroups P x S B) (Λ : B → Finset (Fin J))
    (t : AuxList 𝔊.big Λ) (g : B) (q : {p : ℕ // p ∈ 𝔊.big g}) :
    (Finset.univ.filter fun i : {i : Fin J // i ∈ Λ g} => t g i = q).card =
      (tupleProd Λ t).factorization (q : ℕ) := by
  rw [factorization_tupleProd 𝔊 Λ t (q : ℕ), Finset.sum_eq_single g]
  · rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : t g i = q
    · rw [if_pos h, if_pos (congrArg Subtype.val h)]
    · rw [if_neg h, if_neg (fun h' => h (Subtype.ext h'))]
  · intro g' _ hne
    refine Finset.sum_eq_zero fun i _ => ?_
    refine if_neg fun h' => ?_
    have h1 : (t g' i : ℕ) ∈ 𝔊.big g' := (t g' i).2
    have h2 : (t g' i : ℕ) ∈ 𝔊.big g := by
      rw [h']
      exact q.2
    exact Finset.disjoint_left.mp (𝔊.disjoint_big g' g hne) h1 h2
  · intro h
    exact absurd (Finset.mem_univ g) h

/-- There are at most `∏_g k_g!` tuples with a given product. -/
theorem card_fiber_le (𝔊 : PrimeGroups P x S B) (Λ : B → Finset (Fin J)) (n : ℕ) :
    (Finset.univ.filter fun t : AuxList 𝔊.big Λ => tupleProd Λ t = n).card ≤
      ∏ g, ((Λ g).card).factorial := by
  by_cases hex : ∃ t₀ : AuxList 𝔊.big Λ, tupleProd Λ t₀ = n
  · obtain ⟨t₀, ht₀⟩ := hex
    have hsurj : Set.SurjOn
        (fun (σ : (g : B) → Equiv.Perm {i : Fin J // i ∈ Λ g}) (g : B)
          (i : {i : Fin J // i ∈ Λ g}) => t₀ g (σ g i))
        (↑(Finset.univ : Finset ((g : B) → Equiv.Perm {i : Fin J // i ∈ Λ g})))
        (↑(Finset.univ.filter fun t : AuxList 𝔊.big Λ => tupleProd Λ t = n)) := by
      intro t ht
      have htn : tupleProd Λ t = n := (Finset.mem_filter.mp (Finset.mem_coe.mp ht)).2
      have hσ : ∀ g, ∃ σ : Equiv.Perm {i : Fin J // i ∈ Λ g}, ∀ i, t₀ g (σ i) = t g i :=
        fun g => exists_perm_of_card_fiber_eq (t g) (t₀ g) fun q => by
          rw [card_fiber_eq 𝔊 Λ t g q, card_fiber_eq 𝔊 Λ t₀ g q, htn, ht₀]
      choose σ hσ' using hσ
      exact ⟨σ, Finset.mem_coe.mpr (Finset.mem_univ σ),
        funext fun g => funext fun i => hσ' g i⟩
    calc (Finset.univ.filter fun t : AuxList 𝔊.big Λ => tupleProd Λ t = n).card
        ≤ (Finset.univ : Finset ((g : B) → Equiv.Perm {i : Fin J // i ∈ Λ g})).card :=
          Finset.card_le_card_of_surjOn _ hsurj
      _ = ∏ g, ((Λ g).card).factorial := by
          rw [Finset.card_univ, Fintype.card_pi]
          refine Finset.prod_congr rfl fun g _ => ?_
          rw [Fintype.card_perm, Fintype.card_coe]
  · have hempty : (Finset.univ.filter fun t : AuxList 𝔊.big Λ => tupleProd Λ t = n) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun t _ ht => hex ⟨t, ht⟩
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _

/-- `ρ_Λ(n)` is the number of tuples with product `n` times their common probability. -/
theorem atomMass_eq (big : B → Finset ℕ) (Λ : B → Finset (Fin J)) (n : ℕ) :
    atomMass big Λ n =
      ((Finset.univ.filter fun t : AuxList big Λ => tupleProd Λ t = n).card : ℝ) *
        ((∏ g, ((Graph.primeGroupReciprocalMass (big g))⁻¹) ^ (Λ g).card) * ((n : ℝ))⁻¹) := by
  unfold atomMass
  rw [← Finset.sum_filter, ← nsmul_eq_mul, ← Finset.sum_const]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [auxWeight_eq, (Finset.mem_filter.mp ht).2]

end Tuples

end Atom

/-- **The product atom bound (eq:ideal-product-atom)** [S-03:0079–0096]. -/
theorem productAtomBound : ProductAtomBound := by
  intro P m
  refine ⟨Real.exp 1, ?_⟩
  intro x hx S B _ _ _ _ 𝔊 J Λ _ hΛ n hn
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hL0 : 0 < Real.log x := by linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmax1 : (1 : ℝ) ≤ max 1 P.vMinus⁻¹ := le_max_left _ _
  have hmax0 : (0 : ℝ) < max 1 P.vMinus⁻¹ := lt_of_lt_of_le zero_lt_one hmax1
  have hfact1 : (1 : ℝ) ≤ (m.factorial : ℝ) := Nat.one_le_cast.mpr (Nat.factorial_pos m)
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = (m.factorial : ℝ) * (max 1 P.vMinus⁻¹) ^ m := ⟨_, rfl⟩
  have hβ1 : 1 ≤ β := by
    rw [hβ]
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ (m.factorial : ℝ) * (max 1 P.vMinus⁻¹) ^ m :=
          mul_le_mul hfact1 (one_le_pow₀ hmax1) zero_le_one (le_trans zero_le_one hfact1)
  have hβ0 : 0 < β := lt_of_lt_of_le zero_lt_one hβ1
  have hV : ∀ g, 0 < Graph.primeGroupReciprocalMass (𝔊.big g) :=
    fun g => lt_of_lt_of_le P.vMinus_pos (𝔊.mass_big_ge g)
  have hfac : ∀ g, (((Λ g).card.factorial : ℕ) : ℝ) *
      ((Graph.primeGroupReciprocalMass (𝔊.big g))⁻¹) ^ (Λ g).card ≤ β := by
    intro g
    have hVinv : (Graph.primeGroupReciprocalMass (𝔊.big g))⁻¹ ≤ max 1 P.vMinus⁻¹ :=
      (inv_anti₀ P.vMinus_pos (𝔊.mass_big_ge g)).trans (le_max_right _ _)
    have h1 : (((Λ g).card.factorial : ℕ) : ℝ) ≤ (m.factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (hΛ g)
    have h2 : ((Graph.primeGroupReciprocalMass (𝔊.big g))⁻¹) ^ (Λ g).card ≤
        (max 1 P.vMinus⁻¹) ^ m :=
      (pow_le_pow_left₀ (inv_nonneg.mpr (hV g).le) hVinv _).trans
        (pow_le_pow_right₀ hmax1 (hΛ g))
    rw [hβ]
    exact mul_le_mul h1 h2 (pow_nonneg (inv_nonneg.mpr (hV g).le) _) (Nat.cast_nonneg _)
  have hW0 : 0 ≤ ∏ g, ((Graph.primeGroupReciprocalMass (𝔊.big g))⁻¹) ^ (Λ g).card :=
    Finset.prod_nonneg fun g _ => pow_nonneg (inv_nonneg.mpr (hV g).le) _
  have hcount : ((Finset.univ.filter fun t : AuxList 𝔊.big Λ => tupleProd Λ t = n).card : ℝ) ≤
      ((∏ g, ((Λ g).card).factorial : ℕ) : ℝ) := by
    exact_mod_cast Atom.card_fiber_le 𝔊 Λ n
  have hβpow : β ^ Fintype.card B ≤ Real.log x ^ atomExponent P m := by
    have h1 : β ^ Fintype.card B = β ^ ((Fintype.card B : ℕ) : ℝ) :=
      (Real.rpow_natCast β _).symm
    have h2 : β ^ ((Fintype.card B : ℕ) : ℝ) ≤ β ^ (P.C₀ * Real.log (Real.log x)) :=
      Real.rpow_le_rpow_of_exponent_le hβ1 𝔊.card_big_le
    have hlogβ : Real.log β =
        Real.log (m.factorial : ℝ) + (m : ℝ) * Real.log (max 1 P.vMinus⁻¹) := by
      rw [hβ, Real.log_mul (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m))
        (pow_ne_zero m hmax0.ne'), Real.log_pow]
    have h3 : β ^ (P.C₀ * Real.log (Real.log x)) = Real.log x ^ atomExponent P m := by
      rw [Real.rpow_def_of_pos hβ0, Real.rpow_def_of_pos hL0, hlogβ]
      unfold atomExponent
      congr 1
      ring
    rw [h1]
    exact h2.trans (le_of_eq h3)
  have hmain : ((Finset.univ.filter fun t : AuxList 𝔊.big Λ => tupleProd Λ t = n).card : ℝ) *
      (∏ g, ((Graph.primeGroupReciprocalMass (𝔊.big g))⁻¹) ^ (Λ g).card) ≤
      Real.log x ^ atomExponent P m := by
    calc ((Finset.univ.filter fun t : AuxList 𝔊.big Λ => tupleProd Λ t = n).card : ℝ) *
          (∏ g, ((Graph.primeGroupReciprocalMass (𝔊.big g))⁻¹) ^ (Λ g).card)
        ≤ ((∏ g, ((Λ g).card).factorial : ℕ) : ℝ) *
            (∏ g, ((Graph.primeGroupReciprocalMass (𝔊.big g))⁻¹) ^ (Λ g).card) :=
          mul_le_mul_of_nonneg_right hcount hW0
      _ = ∏ g, ((((Λ g).card.factorial : ℕ) : ℝ) *
            ((Graph.primeGroupReciprocalMass (𝔊.big g))⁻¹) ^ (Λ g).card) := by
          rw [Nat.cast_prod, ← Finset.prod_mul_distrib]
      _ ≤ ∏ _g : B, β :=
          Finset.prod_le_prod (fun g _ => mul_nonneg (Nat.cast_nonneg _)
            (pow_nonneg (inv_nonneg.mpr (hV g).le) _)) (fun g _ => hfac g)
      _ = β ^ Fintype.card B := by rw [Finset.prod_const, Finset.card_univ]
      _ ≤ Real.log x ^ atomExponent P m := hβpow
  rw [Atom.atomMass_eq, ← mul_assoc, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right hmain hn0.le

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Comparison
