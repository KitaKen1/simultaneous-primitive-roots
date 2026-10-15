module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.PrimeGroups
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Order.LiminfLimsup
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The count of one group in Lemma 3.4 ([S] (eq:physical-count-bound))

Source: `verification/stage7-sources/S-02.tex`, lines 142–150 (`[S-02:0142–0150]`).

"If the target has `y ≥ M` divisors from group `g`, then, after the `M - t_g` distinct shared
labels have been fixed, there are `(y - M + t_g)_{t_g}` possible ordered unshared target lists.
Hence their sum, with their endpoint damping, is at most
`sup_{z ≥ 0} V_g^{-t_g} (z + t_g)_{t_g} q^{z/2} ≤ C`. Here `t_g ≤ ℓ + m`, so `C` is independent of
`J`."

This file proves that statement for one group, for an arbitrary predicate `hit : ℕ → Prop` in
the place of "`p` divides the position".

* `GroupValid hit c a₀ f` — the list `f` of one group has distinct labels, all of them hits, and
  its labels in the shared slots (the slots of `{1, …, J} ∖ c`) are those of `a₀`.
  `validSet hit c a₀` is the finite set of these lists.
* `card_validSet_le` — if there is such a list then `y ≥ M` (`slots_le_countHits`) and their
  number is at most `(z + t)^t`, `z = y - M`, `t = ℓ + |c|`. The paper's count is the falling
  factorial `(z + t)_t ≤ (z + t)^t`; the power is what is proved and used here (the unshared
  labels avoid the `M - t` shared labels, so each of them has at most `y - (M - t) = z + t`
  values).
* `countSup T ρ = sup_{z ≥ 0} (z + T)^T ρ^z`, finite for `0 < ρ < 1` (`le_countSup`), and
  `groupConst v₋ q T = max(1, 1/v₋)^T · max(1, countSup T √q)`.
* `group_factor_le` — (eq:physical-count-bound): the number of lists times `V^{-t}` times the
  damping `q^{(y - M)/2}` is at most `groupConst v₋ q T` whenever `V ≥ v₋ > 0` and `t ≤ T`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Schur

open scoped BigOperators

noncomputable section

/-! ### Lists of one group with prescribed shared labels -/

/-- `M = J + ℓ` distinct labels of one group which all hit the position: the group has at least
`M` hits ("the target has `y ≥ M` divisors from group `g`"). -/
theorem slots_le_countHits {Q : Finset ℕ} {hit : ℕ → Prop} {J ℓ : ℕ}
    (f : Slot J ℓ → {p : ℕ // p ∈ Q}) (hinj : Function.Injective f) (hhit : ∀ s, hit (f s)) :
    J + ℓ ≤ countHits hit Q := by
  classical
  have h : (Finset.univ : Finset (Slot J ℓ)).card ≤ (Q.filter hit).card := by
    refine Finset.card_le_card_of_injOn (fun s => ((f s : {p : ℕ // p ∈ Q}) : ℕ))
      (fun s _ => ?_) ?_
    · exact Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨(f s).2, hhit s⟩)
    · intro s _ s' _ hss
      exact hinj (Subtype.ext hss)
  rw [Finset.card_univ, card_slot] at h
  exact h

/-- The lists of one group which can occur as the summed half of a row transition: the labels are
distinct, they all hit the position, and the labels in the shared slots (the slots of
`{1, …, J} ∖ c`) are those of the reference list `a₀`. -/
def GroupValid {Q : Finset ℕ} {J ℓ : ℕ} (hit : ℕ → Prop) (c : Finset (Fin J))
    (a₀ f : Slot J ℓ → {p : ℕ // p ∈ Q}) : Prop :=
  Function.Injective f ∧ (∀ s, hit (f s)) ∧
    ∀ i : Fin J, i ∉ c → f (Sum.inl i) = a₀ (Sum.inl i)

open Classical in
/-- The finite set of the lists with `GroupValid`. -/
def validSet {Q : Finset ℕ} {J ℓ : ℕ} (hit : ℕ → Prop) (c : Finset (Fin J))
    (a₀ : Slot J ℓ → {p : ℕ // p ∈ Q}) : Finset (Slot J ℓ → {p : ℕ // p ∈ Q}) :=
  Finset.univ.filter (GroupValid hit c a₀)

open Classical in
theorem mem_validSet {Q : Finset ℕ} {J ℓ : ℕ} {hit : ℕ → Prop} {c : Finset (Fin J)}
    {a₀ f : Slot J ℓ → {p : ℕ // p ∈ Q}} :
    f ∈ validSet hit c a₀ ↔ GroupValid hit c a₀ f := by
  unfold validSet
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

/-- The labels of a list in its unshared slots: the slots of `c` and the last `ℓ` slots. -/
def unsharedLabels {Q : Finset ℕ} {J ℓ : ℕ} (c : Finset (Fin J))
    (f : Slot J ℓ → {p : ℕ // p ∈ Q}) : ({i : Fin J // i ∈ c} ⊕ Fin ℓ) → ℕ :=
  fun u => Sum.elim (fun i : {i : Fin J // i ∈ c} => ((f (Sum.inl i.1) : {p : ℕ // p ∈ Q}) : ℕ))
    (fun j : Fin ℓ => ((f (Sum.inr j) : {p : ℕ // p ∈ Q}) : ℕ)) u

open Classical in
/-- A label of a valid list in an unshared slot is a hit of the group, and it is none of the
shared labels. -/
theorem valid_label_mem_sdiff {Q : Finset ℕ} {J ℓ : ℕ} {hit : ℕ → Prop} {c : Finset (Fin J)}
    {a₀ f : Slot J ℓ → {p : ℕ // p ∈ Q}} (hf : GroupValid hit c a₀ f) (s : Slot J ℓ)
    (hs : ∀ i : Fin J, i ∉ c → s ≠ Sum.inl i) :
    ((f s : {p : ℕ // p ∈ Q}) : ℕ) ∈
      (Q.filter hit) \
        (cᶜ.image fun i : Fin J => ((a₀ (Sum.inl i) : {p : ℕ // p ∈ Q}) : ℕ)) := by
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨(f s).2, hf.2.1 s⟩, fun hmem => ?_⟩
  obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hmem
  have hic : i ∉ c := Finset.mem_compl.mp hi
  have h1 : f (Sum.inl i) = f s := by
    rw [hf.2.2 i hic]
    exact Subtype.ext heq
  exact hs i hic (hf.1 h1).symm

open Classical in
/-- If a valid list exists, the `J - |c|` shared labels are distinct hits of the group; removing
them leaves `y - (J - |c|)` hits. -/
theorem card_sdiff_shared {Q : Finset ℕ} {J ℓ : ℕ} {hit : ℕ → Prop} {c : Finset (Fin J)}
    {a₀ f₀ : Slot J ℓ → {p : ℕ // p ∈ Q}} (hf₀ : GroupValid hit c a₀ f₀) :
    ((Q.filter hit) \
        (cᶜ.image fun i : Fin J => ((a₀ (Sum.inl i) : {p : ℕ // p ∈ Q}) : ℕ))).card +
      (J - c.card) = countHits hit Q := by
  have hsub : (cᶜ.image fun i : Fin J => ((a₀ (Sum.inl i) : {p : ℕ // p ∈ Q}) : ℕ)) ⊆
      Q.filter hit := by
    intro p hp
    obtain ⟨i, hi, hip⟩ := Finset.mem_image.mp hp
    have h := hf₀.2.2 i (Finset.mem_compl.mp hi)
    have hhit : hit ((a₀ (Sum.inl i) : {p : ℕ // p ∈ Q}) : ℕ) := by
      rw [← h]
      exact hf₀.2.1 (Sum.inl i)
    rw [← hip]
    exact Finset.mem_filter.mpr ⟨(a₀ (Sum.inl i)).2, hhit⟩
  have hinj : Set.InjOn (fun i : Fin J => ((a₀ (Sum.inl i) : {p : ℕ // p ∈ Q}) : ℕ))
      (cᶜ : Finset (Fin J)) := by
    intro i hi i' hi' h
    have hi1 : i ∉ c := Finset.mem_compl.mp (Finset.mem_coe.mp hi)
    have hi2 : i' ∉ c := Finset.mem_compl.mp (Finset.mem_coe.mp hi')
    have h1 : f₀ (Sum.inl i) = f₀ (Sum.inl i') := by
      rw [hf₀.2.2 i hi1, hf₀.2.2 i' hi2]
      exact Subtype.ext h
    exact Sum.inl.inj (hf₀.1 h1)
  have hcard : (cᶜ.image fun i : Fin J => ((a₀ (Sum.inl i) : {p : ℕ // p ∈ Q}) : ℕ)).card =
      J - c.card := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_compl, Fintype.card_fin]
  have h := Finset.card_sdiff_add_card_eq_card hsub
  rw [hcard] at h
  exact h

open Classical in
/-- **The count of [S-02:0143–0145]**, with a power in the place of the falling factorial: if
there is a valid list at all, the number of valid lists is at most `(z + t)^t`, where
`z = y - M` (`y` hits, `M = J + ℓ` slots) and `t = ℓ + |c|` is the number of unshared slots. -/
theorem card_validSet_le {Q : Finset ℕ} {J ℓ : ℕ} {hit : ℕ → Prop} {c : Finset (Fin J)}
    {a₀ f₀ : Slot J ℓ → {p : ℕ // p ∈ Q}} (hf₀ : GroupValid hit c a₀ f₀) :
    (validSet hit c a₀).card ≤
      (countHits hit Q - (J + ℓ) + (ℓ + c.card)) ^ (ℓ + c.card) := by
  have hM : J + ℓ ≤ countHits hit Q := slots_le_countHits f₀ hf₀.1 hf₀.2.1
  have hcJ : c.card ≤ J := by
    have h := Finset.card_le_univ c
    rw [Fintype.card_fin] at h
    exact h
  have hD := card_sdiff_shared hf₀
  have hDn : ((Q.filter hit) \
      (cᶜ.image fun i : Fin J => ((a₀ (Sum.inl i) : {p : ℕ // p ∈ Q}) : ℕ))).card =
      countHits hit Q - (J + ℓ) + (ℓ + c.card) := by
    omega
  have hmain : (validSet hit c a₀).card ≤
      (Fintype.piFinset fun _ : {i : Fin J // i ∈ c} ⊕ Fin ℓ =>
        (Q.filter hit) \
          (cᶜ.image fun i : Fin J => ((a₀ (Sum.inl i) : {p : ℕ // p ∈ Q}) : ℕ))).card := by
    refine Finset.card_le_card_of_injOn (unsharedLabels c) (fun f hf => ?_) ?_
    · have hv : GroupValid hit c a₀ f := mem_validSet.mp (Finset.mem_coe.mp hf)
      refine Finset.mem_coe.mpr (Fintype.mem_piFinset.mpr fun u => ?_)
      rcases u with ⟨i, hi⟩ | j
      · exact valid_label_mem_sdiff hv (Sum.inl i)
          fun i' hi' h => hi' (Sum.inl.inj h ▸ hi)
      · exact valid_label_mem_sdiff hv (Sum.inr j) fun i' _ h => Sum.inr_ne_inl h
    · intro f hf f' hf' h
      have hv : GroupValid hit c a₀ f := mem_validSet.mp (Finset.mem_coe.mp hf)
      have hv' : GroupValid hit c a₀ f' := mem_validSet.mp (Finset.mem_coe.mp hf')
      funext s
      rcases s with i | j
      · by_cases hi : i ∈ c
        · have h1 : ((f (Sum.inl i) : {p : ℕ // p ∈ Q}) : ℕ) =
              ((f' (Sum.inl i) : {p : ℕ // p ∈ Q}) : ℕ) := congrFun h (Sum.inl ⟨i, hi⟩)
          exact Subtype.ext h1
        · rw [hv.2.2 i hi, hv'.2.2 i hi]
      · have h1 : ((f (Sum.inr j) : {p : ℕ // p ∈ Q}) : ℕ) =
            ((f' (Sum.inr j) : {p : ℕ // p ∈ Q}) : ℕ) := congrFun h (Sum.inr j)
        exact Subtype.ext h1
  have hpi : (Fintype.piFinset fun _ : {i : Fin J // i ∈ c} ⊕ Fin ℓ =>
        (Q.filter hit) \
          (cᶜ.image fun i : Fin J => ((a₀ (Sum.inl i) : {p : ℕ // p ∈ Q}) : ℕ))).card =
      (countHits hit Q - (J + ℓ) + (ℓ + c.card)) ^ (ℓ + c.card) := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_sum,
      Fintype.card_coe, Fintype.card_fin, hDn, Nat.add_comm c.card ℓ]
  exact hmain.trans (le_of_eq hpi)

/-! ### The constant of (eq:physical-count-bound) -/

/-- `sup_{z ≥ 0} (z + T)^T ρ^z`; for `ρ = √q` this bounds the supremum
`sup_{z ≥ 0} (z + t)_t q^{z/2}` of (eq:physical-count-bound) for every `t ≤ T`. -/
def countSup (T : ℕ) (ρ : ℝ) : ℝ := ⨆ z : ℕ, ((z + T : ℕ) : ℝ) ^ T * ρ ^ z

/-- The supremum `countSup` is finite for `0 < ρ < 1`: `n^T ρ^n → 0`. -/
theorem countSup_bddAbove (T : ℕ) {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) :
    BddAbove (Set.range fun z : ℕ => ((z + T : ℕ) : ℝ) ^ T * ρ ^ z) := by
  have habs : |ρ| < 1 := by
    rw [abs_of_pos h0]
    exact h1
  obtain ⟨A, hA⟩ := (tendsto_pow_const_mul_const_pow_of_abs_lt_one T habs).bddAbove_range
  refine ⟨A / ρ ^ T, ?_⟩
  rintro _ ⟨z, rfl⟩
  have hz : ((z + T : ℕ) : ℝ) ^ T * ρ ^ (z + T) ≤ A := hA ⟨z + T, rfl⟩
  rw [pow_add, ← mul_assoc] at hz
  exact (le_div_iff₀ (pow_pos h0 T)).mpr hz

theorem le_countSup (T : ℕ) {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) (z : ℕ) :
    ((z + T : ℕ) : ℝ) ^ T * ρ ^ z ≤ countSup T ρ :=
  le_ciSup (countSup_bddAbove T h0 h1) z

/-- **The constant `C` of (eq:physical-count-bound)** for groups of mass at least `v₋`, damping
base `q` and at most `T` unshared slots: `max(1, 1/v₋)^T · max(1, sup_{z ≥ 0} (z + T)^T q^{z/2})`.
It does not depend on `J`. -/
def groupConst (vMinus q : ℝ) (T : ℕ) : ℝ :=
  (max 1 vMinus⁻¹) ^ T * max 1 (countSup T (Real.sqrt q))

theorem one_le_groupConst (vMinus q : ℝ) (T : ℕ) : 1 ≤ groupConst vMinus q T := by
  have h1 : (1 : ℝ) ≤ (max 1 vMinus⁻¹) ^ T := one_le_pow₀ (le_max_left _ _)
  have h2 : (1 : ℝ) ≤ max 1 (countSup T (Real.sqrt q)) := le_max_left _ _
  unfold groupConst
  calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
    _ ≤ (max 1 vMinus⁻¹) ^ T * max 1 (countSup T (Real.sqrt q)) :=
        mul_le_mul h1 h2 zero_le_one (zero_le_one.trans h1)

theorem pow_add_le_pow_add (z t T : ℕ) (h : t ≤ T) (hT : 0 < T) :
    (z + t) ^ t ≤ (z + T) ^ T :=
  (Nat.pow_le_pow_left (Nat.add_le_add_left h z) t).trans
    (Nat.pow_le_pow_right (by omega) h)

theorem inv_pow_le_max_pow {vMinus V : ℝ} (hv : 0 < vMinus) (hV : vMinus ≤ V) {t T : ℕ}
    (ht : t ≤ T) : (V ^ t)⁻¹ ≤ (max 1 vMinus⁻¹) ^ T := by
  have hVpos : 0 < V := lt_of_lt_of_le hv hV
  have h1 : V⁻¹ ≤ max 1 vMinus⁻¹ := (inv_anti₀ hv hV).trans (le_max_right _ _)
  calc (V ^ t)⁻¹ = V⁻¹ ^ t := (inv_pow V t).symm
    _ ≤ (max 1 vMinus⁻¹) ^ t := pow_le_pow_left₀ (inv_nonneg.mpr hVpos.le) h1 t
    _ ≤ (max 1 vMinus⁻¹) ^ T := pow_le_pow_right₀ (le_max_left _ _) ht

/-- **(eq:physical-count-bound)** [S-02:0143–0150] for one group with `V ≥ v₋`, `t = ℓ + |c|`
unshared slots, `t ≤ T`: the number of the valid lists, times the coefficient `V^{-t}`, times
the damping `q^{(y - M)/2}` of the group (`y` hits, `M = J + ℓ`), is at most
`groupConst v₋ q T`. -/
theorem group_factor_le {Q : Finset ℕ} {J ℓ : ℕ} {vMinus q V : ℝ} (hv : 0 < vMinus)
    (hV : vMinus ≤ V) (hq0 : 0 < q) (hq1 : q < 1) {T : ℕ} (hT : 0 < T) (hit : ℕ → Prop)
    (c : Finset (Fin J)) (a₀ : Slot J ℓ → {p : ℕ // p ∈ Q}) {t : ℕ} (ht : t = ℓ + c.card)
    (htT : t ≤ T) :
    ((validSet hit c a₀).card : ℝ) * (V ^ t)⁻¹ *
        q ^ ((((countHits hit Q : ℕ) : ℝ) - ((J + ℓ : ℕ) : ℝ)) / 2) ≤
      groupConst vMinus q T := by
  subst ht
  have hVpos : 0 < V := lt_of_lt_of_le hv hV
  rcases (validSet hit c a₀).eq_empty_or_nonempty with hempty | ⟨f₀, hf₀⟩
  · rw [hempty, Finset.card_empty, Nat.cast_zero, zero_mul, zero_mul]
    exact zero_le_one.trans (one_le_groupConst vMinus q T)
  · have hv₀ : GroupValid hit c a₀ f₀ := mem_validSet.mp hf₀
    have hM : J + ℓ ≤ countHits hit Q := slots_le_countHits f₀ hv₀.1 hv₀.2.1
    obtain ⟨z, hz⟩ : ∃ z : ℕ, countHits hit Q = J + ℓ + z :=
      ⟨countHits hit Q - (J + ℓ), by omega⟩
    have hcard : (validSet hit c a₀).card ≤ (z + T) ^ T := by
      have h1 := card_validSet_le hv₀
      have h2 : countHits hit Q - (J + ℓ) + (ℓ + c.card) = z + (ℓ + c.card) := by omega
      rw [h2] at h1
      exact h1.trans (pow_add_le_pow_add z (ℓ + c.card) T htT hT)
    have hcardR : ((validSet hit c a₀).card : ℝ) ≤ ((z + T : ℕ) : ℝ) ^ T := by
      exact_mod_cast hcard
    have hexp : (((countHits hit Q : ℕ) : ℝ) - ((J + ℓ : ℕ) : ℝ)) / 2 = (z : ℝ) / 2 := by
      rw [hz]
      push_cast
      ring
    have hsqrt0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq0
    have hsqrt1 : Real.sqrt q < 1 := by
      have h := Real.sqrt_lt_sqrt hq0.le hq1
      rw [Real.sqrt_one] at h
      exact h
    rw [hexp, Real.rpow_div_two_eq_sqrt _ hq0.le, Real.rpow_natCast]
    unfold groupConst
    calc ((validSet hit c a₀).card : ℝ) * (V ^ (ℓ + c.card))⁻¹ * Real.sqrt q ^ z
        ≤ ((z + T : ℕ) : ℝ) ^ T * (max 1 vMinus⁻¹) ^ T * Real.sqrt q ^ z :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hcardR (inv_pow_le_max_pow hv hV htT)
              (inv_nonneg.mpr (pow_nonneg hVpos.le _)) (pow_nonneg (Nat.cast_nonneg _) T))
            (pow_nonneg hsqrt0.le z)
      _ = (max 1 vMinus⁻¹) ^ T * (((z + T : ℕ) : ℝ) ^ T * Real.sqrt q ^ z) := by ring
      _ ≤ (max 1 vMinus⁻¹) ^ T * max 1 (countSup T (Real.sqrt q)) :=
          mul_le_mul_of_nonneg_left
            ((le_countSup T hsqrt0 hsqrt1 z).trans (le_max_right _ _))
            (pow_nonneg (zero_le_one.trans (le_max_left _ _)) T)

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Schur
