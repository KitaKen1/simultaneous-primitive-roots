module

public import SimultaneousPrimitiveRoots.FiniteFieldKummer
public import Mathlib.Algebra.Polynomial.BigOperators

@[expose] public section

namespace SimultaneousPrimitiveRoots

open Polynomial UniqueFactorizationMonoid

theorem multiset_card_le_sum_map_of_one_le {ι : Type*} (s : Multiset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, 1 ≤ f i) : s.card ≤ (s.map f).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have ha := hf a (Multiset.mem_cons_self _ _)
    have hs := ih (fun i hi => hf i (Multiset.mem_cons_of_mem hi))
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons]
    omega

theorem multiset_sum_map_eq_card_iff_of_one_le {ι : Type*} (s : Multiset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, 1 ≤ f i) :
    (s.map f).sum = s.card ↔ ∀ i ∈ s, f i = 1 := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have ha := hf a (Multiset.mem_cons_self _ _)
    have hs : ∀ i ∈ s, 1 ≤ f i := fun i hi => hf i (Multiset.mem_cons_of_mem hi)
    have hle := multiset_card_le_sum_map_of_one_le s f hs
    simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
      Multiset.mem_cons, forall_eq_or_imp]
    rw [← ih hs]
    omega

theorem normalizedFactors_of_monic_splits {F : Type*} [Field F] [DecidableEq F] {f : F[X]}
    (hm : f.Monic) (hs : f.Splits) :
    normalizedFactors f = f.roots.map (fun r => X - C r) := by
  classical
  have hprod := hs.eq_prod_roots_of_monic hm
  conv_lhs => rw [hprod]
  rw [normalizedFactors_prod_eq]
  · simp only [Multiset.map_map]
    apply Multiset.map_congr rfl
    intro r _
    exact (monic_X_sub_C r).normalize_eq_self
  · intro g hg
    obtain ⟨r, _, rfl⟩ := Multiset.mem_map.mp hg
    exact irreducible_X_sub_C r

theorem normalizedFactors_card_le_degree {F : Type*} [Field F] [DecidableEq F] {f : F[X]}
    (hm : f.Monic) : (normalizedFactors f).toFinset.card ≤ f.natDegree := by
  classical
  have hprod : (normalizedFactors f).prod = f :=
    (prod_normalizedFactors_eq hm.ne_zero).trans hm.normalize_eq_self
  have hsum : ((normalizedFactors f).map natDegree).sum = f.natDegree := by
    rw [← natDegree_multiset_prod]
    · rw [hprod]
    · exact zero_notMem_normalizedFactors f
  exact (Multiset.toFinset_card_le _).trans
    ((multiset_card_le_sum_map_of_one_le _ _ (fun g hg =>
      (irreducible_of_normalized_factor _ hg).natDegree_pos)).trans_eq hsum)

/-- A separable monic polynomial has as many distinct irreducible factors as
its degree exactly when all its factors are linear. -/
theorem normalizedFactors_card_eq_degree_iff_splits {F : Type*} [Field F] [DecidableEq F] {f : F[X]}
    (hm : f.Monic) (hsep : f.Separable) :
    (normalizedFactors f).toFinset.card = f.natDegree ↔ f.Splits := by
  classical
  have hprod : (normalizedFactors f).prod = f :=
    (prod_normalizedFactors_eq hm.ne_zero).trans hm.normalize_eq_self
  have hpos : ∀ g ∈ normalizedFactors f, 1 ≤ g.natDegree :=
    fun g hg => (irreducible_of_normalized_factor _ hg).natDegree_pos
  have hsum : ((normalizedFactors f).map natDegree).sum = f.natDegree := by
    rw [← natDegree_multiset_prod]
    · rw [hprod]
    · exact zero_notMem_normalizedFactors f
  constructor
  · intro hc
    have hmcard : ((normalizedFactors f).map natDegree).sum = (normalizedFactors f).card := by
      have hl := multiset_card_le_sum_map_of_one_le _ _ hpos
      have ht := Multiset.toFinset_card_le (normalizedFactors f)
      omega
    have hdeg := (multiset_sum_map_eq_card_iff_of_one_le _ _ hpos).mp hmcard
    rw [← hprod]
    exact Splits.multisetProd (fun g hg => Splits.of_natDegree_eq_one (hdeg g hg))
  · intro hs
    rw [normalizedFactors_of_monic_splits hm hs,
      Multiset.toFinset_card_of_nodup]
    · rw [Multiset.card_map, ← hs.natDegree_eq_card_roots]
    · apply (nodup_roots hsep).map
      intro r t h
      have hc := congrArg (fun g : F[X] => g.coeff 0) h
      simpa using hc

theorem radical_normalizedFactors_card_le {a p q : ℕ} [Fact p.Prime] (hq : 0 < q) :
    (normalizedFactors (X ^ q - C (a : ZMod p))).toFinset.card ≤ q := by
  simpa only [natDegree_X_pow_sub_C] using
    normalizedFactors_card_le_degree (monic_X_pow_sub_C (a : ZMod p) hq.ne')

theorem radical_normalizedFactors_card_eq_iff {a p q : ℕ} [Fact p.Prime]
    (hq : 0 < q) (hqp : q ∣ p - 1) (ha : ¬ p ∣ a) :
    (normalizedFactors (X ^ q - C (a : ZMod p))).toFinset.card = q ↔
      (a : ZMod p) ^ ((p - 1) / q) = 1 := by
  have hs := normalizedFactors_card_eq_degree_iff_splits
    (monic_X_pow_sub_C (a : ZMod p) hq.ne')
    (radical_mod_separable Fact.out hq hqp ha)
  simpa only [natDegree_X_pow_sub_C] using
    hs.trans (powerResidue_iff_radical_splits Fact.out hq hqp ha).symm

end SimultaneousPrimitiveRoots
