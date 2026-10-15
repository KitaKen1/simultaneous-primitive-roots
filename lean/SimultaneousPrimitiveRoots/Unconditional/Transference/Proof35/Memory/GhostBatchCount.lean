module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.BigDampingFactor
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Subsets of terminated zeros and ordered batches of births: two finite identities

Source: `verification/stage7-sources/S-02.tex`, lines 456–475 and 569–581
(`[S-02:0456–0475, 0569–0581]`), (eq:ghost-row).

Tools for `GhostStepFactorProof.lean` (part (M2) of the proof of [S] Lemma 3.7). Nothing here
involves the groups or the memories.

* `ghStep_sum_subsetTerm` — "selected old zeros terminate, continuing zeros are damped": the sum
  over the sets `s` of terminated pending zeros of
  `D^{|s|} A^{|Z| - |s|} ∏_{h ∉ s} pend_h ∏_{h ∈ s} dead_h` is the product over the particles of
  `D · dead_h + A · pend_h` (pending zeros) and of `pend_h` (the other particles).
* `ghStep_card_fiber`, `ghStep_sum_injective` — an injective `b`-tuple is a `b`-element set and
  one of its `b!` orderings: "distinct ghost births in an unordered batch are counted once by its
  factorial divisor".
* `ghStep_sum_batchTerm` — the sum over the ordered batches `(p'_1, …, p'_b)`, `b ≤ N`, of pairwise
  distinct admissible elements, with the weight `1/b!`, of `∏_h w(p'_h)` times `∏ u(p)` over the
  admissible elements which are not in the batch, is `∏_p (u(p) + w(p))` over the admissible
  elements (for `N ≥ #P`).
* `ghStep_ite_third` — the case distinction for one prime (active, pending, dead, unborn) before
  and after a visit operation.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### Subsets of terminated zeros -/

/-- The term of the set `s` of terminated positions: `D^{|s|} A^{|Z| - |s|}` times the values
`pd` of the surviving and `dd` of the terminated positions, if all positions of `s` are zeros
(`Z` is the set of all zeros); `0` otherwise. -/
def ghStep_subsetTerm {n : ℕ} (zero : Fin n → Prop) [DecidablePred zero] (Dc Ac : ℝ)
    (pd dd : Fin n → ℝ) (s : Finset (Fin n)) : ℝ :=
  if ∀ i ∈ s, zero i then
    Dc ^ s.card * Ac ^ ((Finset.univ.filter zero).card - s.card) * (∏ h ∈ sᶜ, pd h) *
      ∏ h ∈ s, dd h
  else 0

/-- The factor of one position after a visit operation: a zero terminates (`D · dd`) or continues
(`A · pd`); the other positions are not touched. -/
def ghStep_pendFactor {n : ℕ} (zero : Fin n → Prop) [DecidablePred zero] (Dc Ac : ℝ)
    (pd dd : Fin n → ℝ) (h : Fin n) : ℝ :=
  if zero h then Dc * dd h + Ac * pd h else pd h

/-- **The sum over the sets of terminated zeros is a product over the positions**
[S-02:0460–0464]. -/
theorem ghStep_sum_subsetTerm {n : ℕ} (zero : Fin n → Prop) [DecidablePred zero] (Dc Ac : ℝ)
    (pd dd : Fin n → ℝ) :
    ∑ s : Finset (Fin n), ghStep_subsetTerm zero Dc Ac pd dd s =
      ∏ h : Fin n, ghStep_pendFactor zero Dc Ac pd dd h := by
  have hpt : ∀ h : Fin n, ghStep_pendFactor zero Dc Ac pd dd h =
      (if zero h then Dc * dd h else 0) + (if zero h then Ac * pd h else pd h) := by
    intro h
    unfold ghStep_pendFactor
    by_cases hz : zero h
    · rw [if_pos hz, if_pos hz, if_pos hz]
    · rw [if_neg hz, if_neg hz, if_neg hz, zero_add]
  have hpt2 : ∀ h : Fin n, (if zero h then Ac * pd h else pd h) =
      (if zero h then Ac else 1) * pd h := by
    intro h
    by_cases hzh : zero h
    · rw [if_pos hzh, if_pos hzh]
    · rw [if_neg hzh, if_neg hzh, one_mul]
  have hexp : ∏ h : Fin n, ghStep_pendFactor zero Dc Ac pd dd h =
      ∑ t : Finset (Fin n), (∏ a ∈ t, (if zero a then Dc * dd a else 0)) *
        ∏ a ∈ tᶜ, (if zero a then Ac * pd a else pd a) :=
    (Finset.prod_congr rfl fun h _ => hpt h).trans
      (Fintype.prod_add (fun a => if zero a then Dc * dd a else 0)
        (fun a => if zero a then Ac * pd a else pd a))
  rw [hexp]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold ghStep_subsetTerm
  by_cases hz : ∀ i ∈ s, zero i
  · rw [if_pos hz]
    have h1 : ∏ h ∈ s, (if zero h then Dc * dd h else 0) = Dc ^ s.card * ∏ h ∈ s, dd h :=
      (Finset.prod_congr rfl fun h hh => if_pos (hz h hh)).trans
        (Finset.prod_mul_distrib.trans
          (congrArg (fun t => t * ∏ h ∈ s, dd h) (Finset.prod_const Dc)))
    have hcard : (Finset.univ.filter zero).card = s.card + (sᶜ.filter zero).card := by
      have hun : Finset.univ.filter zero = s ∪ sᶜ.filter zero := by
        ext h
        rw [Finset.mem_filter, Finset.mem_union, Finset.mem_filter, Finset.mem_compl]
        constructor
        · rintro ⟨-, hzh⟩
          by_cases hs : h ∈ s
          · exact Or.inl hs
          · exact Or.inr ⟨hs, hzh⟩
        · rintro (hs | ⟨-, hzh⟩)
          · exact ⟨Finset.mem_univ h, hz h hs⟩
          · exact ⟨Finset.mem_univ h, hzh⟩
      have hdis : Disjoint s (sᶜ.filter zero) :=
        Finset.disjoint_left.mpr fun h hs hf =>
          Finset.mem_compl.mp (Finset.mem_filter.mp hf).1 hs
      rw [hun, Finset.card_union_of_disjoint hdis]
    have e1 : ∏ h ∈ sᶜ, (if zero h then Ac * pd h else pd h) =
        ∏ h ∈ sᶜ, ((if zero h then Ac else 1) * pd h) :=
      Finset.prod_congr rfl fun h _ => hpt2 h
    have e2 : ∏ h ∈ sᶜ, (if zero h then Ac else 1) = Ac ^ (sᶜ.filter zero).card := by
      rw [← Finset.prod_filter, Finset.prod_const]
    have h2 : ∏ h ∈ sᶜ, (if zero h then Ac * pd h else pd h) =
        Ac ^ ((Finset.univ.filter zero).card - s.card) * ∏ h ∈ sᶜ, pd h := by
      rw [e1, Finset.prod_mul_distrib, e2, hcard, Nat.add_sub_cancel_left]
    rw [h1, h2]
    ring
  · rw [if_neg hz]
    obtain ⟨i, hi, hni⟩ : ∃ i ∈ s, ¬zero i := by
      by_contra hcon
      exact hz fun i hi => not_not.mp fun h => hcon ⟨i, hi, h⟩
    have h0 : ∏ h ∈ s, (if zero h then Dc * dd h else 0) = 0 :=
      Finset.prod_eq_zero hi (if_neg hni)
    rw [h0, zero_mul]

/-! ### Injective tuples with a given set of values -/

/-- The tuple `j ↦ e⁻¹(σ j)` of elements of the set `T`, for an enumeration `e` of `T` and a
permutation `σ` of the indices. -/
def ghStep_tupleOf {P : Type*} {b : ℕ} (T : Finset P) (e : T ≃ Fin b) (σ : Equiv.Perm (Fin b)) :
    Fin b → P :=
  fun j => ((e.symm (σ j) : T) : P)

theorem ghStep_tupleOf_injective {P : Type*} {b : ℕ} (T : Finset P) (e : T ≃ Fin b) :
    Function.Injective (ghStep_tupleOf T e) := by
  intro σ τ h
  refine Equiv.ext fun j => ?_
  exact e.symm.injective (Subtype.ext (congrFun h j))

/-- **A set of `b` elements has `b!` orderings**: the number of the injective `b`-tuples whose
set of values is `T`. -/
theorem ghStep_card_fiber {P : Type*} [Fintype P] [DecidableEq P] {b : ℕ} (T : Finset P)
    (hT : T.card = b)
    {hd : DecidablePred fun p' : Fin b → P => Function.Injective p' ∧ Finset.univ.image p' = T} :
    (@Finset.filter _ (fun p' : Fin b → P => Function.Injective p' ∧ Finset.univ.image p' = T)
      hd Finset.univ).card = b.factorial := by
  obtain ⟨e⟩ : Nonempty (T ≃ Fin b) :=
    ⟨Fintype.equivFinOfCardEq ((Fintype.card_coe T).trans hT)⟩
  have himg : @Finset.filter _
      (fun p' : Fin b → P => Function.Injective p' ∧ Finset.univ.image p' = T) hd Finset.univ =
      Finset.univ.image (ghStep_tupleOf T e) := by
    ext p'
    rw [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨-, hinj, himg⟩
      have hmem : ∀ j, p' j ∈ T := fun j => by
        rw [← himg]
        exact Finset.mem_image_of_mem p' (Finset.mem_univ j)
      have hf : Function.Injective fun j : Fin b => e ⟨p' j, hmem j⟩ := fun j k h =>
        hinj (congrArg Subtype.val (e.injective h))
      refine ⟨Equiv.ofBijective _ ⟨hf, Finite.injective_iff_surjective.mp hf⟩,
        Finset.mem_univ _, ?_⟩
      funext j
      exact congrArg Subtype.val (e.symm_apply_apply ⟨p' j, hmem j⟩)
    · rintro ⟨σ, -, rfl⟩
      refine ⟨Finset.mem_univ _,
        fun j k h => σ.injective (e.symm.injective (Subtype.ext h)), ?_⟩
      ext t
      rw [Finset.mem_image]
      constructor
      · rintro ⟨j, -, rfl⟩
        exact (e.symm (σ j)).2
      · intro ht
        refine ⟨σ.symm (e ⟨t, ht⟩), Finset.mem_univ _, ?_⟩
        exact congrArg Subtype.val
          ((congrArg e.symm (σ.apply_symm_apply (e ⟨t, ht⟩))).trans
            (e.symm_apply_apply ⟨t, ht⟩))
  rw [himg, Finset.card_image_of_injective _ (ghStep_tupleOf_injective T e), Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin]

/-- **A sum over the injective `b`-tuples of a function of their set of values** is `b!` times
the sum over the sets of `b` elements. -/
theorem ghStep_sum_injective {P : Type*} [Fintype P] [DecidableEq P] (b : ℕ)
    (G : Finset P → ℝ) :
    ∑ p' : Fin b → P, (if Function.Injective p' then G (Finset.univ.image p') else 0) =
      (b.factorial : ℝ) * ∑ T ∈ Finset.univ.filter (fun T : Finset P => T.card = b), G T := by
  have hmaps : ∀ p' ∈ Finset.univ.filter (fun p' : Fin b → P => Function.Injective p'),
      Finset.univ.image p' ∈ Finset.univ.filter (fun T : Finset P => T.card = b) := by
    intro p' hp'
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rw [Finset.card_image_of_injective _ (Finset.mem_filter.mp hp').2, Finset.card_univ,
      Fintype.card_fin]
  have h1 : ∑ p' : Fin b → P, (if Function.Injective p' then G (Finset.univ.image p') else 0) =
      ∑ p' ∈ Finset.univ.filter (fun p' : Fin b → P => Function.Injective p'),
        G (Finset.univ.image p') :=
    (Finset.sum_filter _ _).symm
  have h2 : ∑ T ∈ Finset.univ.filter (fun T : Finset P => T.card = b),
        ∑ p' ∈ (Finset.univ.filter (fun p' : Fin b → P => Function.Injective p')).filter
          (fun p' => Finset.univ.image p' = T), G (Finset.univ.image p') =
      ∑ p' ∈ Finset.univ.filter (fun p' : Fin b → P => Function.Injective p'),
        G (Finset.univ.image p') :=
    Finset.sum_fiberwise_of_maps_to hmaps (fun p' => G (Finset.univ.image p'))
  rw [h1, ← h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  have hTc : T.card = b := (Finset.mem_filter.mp hT).2
  refine (Finset.sum_congr rfl fun p' hp' =>
    congrArg G (Finset.mem_filter.mp hp').2).trans ?_
  rw [Finset.sum_const, Finset.filter_filter, ghStep_card_fiber T hTc, nsmul_eq_mul]

/-! ### Ordered batches of births -/

/-- The factor of the element `p` for the batch `p'`: `1` if `p` is not admissible (`bad`) or
occurs in the batch, and `u p` otherwise. -/
def ghStep_unbornFactor {P : Type*} [DecidableEq P] (bad : P → Prop) [DecidablePred bad]
    (u : P → ℝ) {b : ℕ} (p' : Fin b → P) (p : P) : ℝ :=
  if bad p then 1 else if ∃ j, p' j = p then 1 else u p

/-- The term of the ordered batch `p'` of `b` births: `1/b!` times the product of the weights
`w` of its elements and of the factors of the other elements, if the elements of the batch are
pairwise distinct and admissible; `0` otherwise. -/
def ghStep_batchTerm {P : Type*} [Fintype P] [DecidableEq P] (bad : P → Prop)
    [DecidablePred bad] (u w : P → ℝ) (b : ℕ) (p' : Fin b → P) : ℝ :=
  if Function.Injective p' ∧ ∀ j, ¬bad (p' j) then
    ((b.factorial : ℝ))⁻¹ * (∏ j, w (p' j)) * ∏ p : P, ghStep_unbornFactor bad u p' p
  else 0

/-- The term of the set `T` of births. -/
def ghStep_setTerm {P : Type*} [Fintype P] [DecidableEq P] (bad : P → Prop) [DecidablePred bad]
    (u w : P → ℝ) (T : Finset P) : ℝ :=
  if ∀ p ∈ T, ¬bad p then
    (∏ p ∈ T, w p) * ∏ p : P, (if bad p then 1 else if p ∈ T then 1 else u p)
  else 0

/-- The factor of one element after a visit operation: an admissible element stays unborn (`u`)
or is born (`w`). -/
def ghStep_bornFactor {P : Type*} (bad : P → Prop) [DecidablePred bad] (u w : P → ℝ) (p : P) :
    ℝ :=
  if bad p then 1 else u p + w p

/-- The term of an injective batch is `1/b!` times the term of its set of values. -/
theorem ghStep_batchTerm_eq {P : Type*} [Fintype P] [DecidableEq P] (bad : P → Prop)
    [DecidablePred bad] (u w : P → ℝ) (b : ℕ) (p' : Fin b → P) :
    ghStep_batchTerm bad u w b p' =
      if Function.Injective p' then
        ((b.factorial : ℝ))⁻¹ * ghStep_setTerm bad u w (Finset.univ.image p')
      else 0 := by
  unfold ghStep_batchTerm ghStep_setTerm
  by_cases hinj : Function.Injective p'
  · rw [if_pos hinj]
    have hiff : (Function.Injective p' ∧ ∀ j, ¬bad (p' j)) ↔
        ∀ p ∈ Finset.univ.image p', ¬bad p := by
      constructor
      · rintro ⟨-, h⟩ p hp
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp
        exact h j
      · intro h
        exact ⟨hinj, fun j => h _ (Finset.mem_image_of_mem p' (Finset.mem_univ j))⟩
    have hprod : ∏ j, w (p' j) = ∏ p ∈ Finset.univ.image p', w p :=
      (Finset.prod_image fun x _ y _ h => hinj h).symm
    have hex : ∀ p : P, (∃ j, p' j = p) ↔ p ∈ Finset.univ.image p' := fun p =>
      ⟨fun ⟨j, hj⟩ => Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩, fun hp => by
        obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hp
        exact ⟨j, hj⟩⟩
    by_cases hall : ∀ p ∈ Finset.univ.image p', ¬bad p
    · rw [if_pos (hiff.mpr hall), if_pos hall, hprod, mul_assoc]
      refine congrArg (fun t => ((b.factorial : ℝ))⁻¹ *
        ((∏ p ∈ Finset.univ.image p', w p) * t)) ?_
      refine Finset.prod_congr rfl fun p _ => ?_
      unfold ghStep_unbornFactor
      exact bigRes_ite_congr Iff.rfl rfl (bigRes_ite_congr (hex p) rfl rfl)
    · rw [if_neg (fun h => hall (hiff.mp h)), if_neg hall, mul_zero]
  · rw [if_neg (fun h : Function.Injective p' ∧ ∀ j, ¬bad (p' j) => hinj h.1),
      if_neg hinj]

/-- **The sum over the ordered batches of births is a product over the elements**
[S-02:0465–0472, 0578–0579]: "distinct ghost births in an unordered batch are counted once by its
factorial divisor". For `N ≥ #P`. -/
theorem ghStep_sum_batchTerm {P : Type*} [Fintype P] [DecidableEq P] (bad : P → Prop)
    [DecidablePred bad] (u w : P → ℝ) (N : ℕ) (hN : Fintype.card P ≤ N) :
    ∑ b : Fin (N + 1), ∑ p' : Fin b.val → P, ghStep_batchTerm bad u w b.val p' =
      ∏ p : P, ghStep_bornFactor bad u w p := by
  -- ordered batches of `b` births are sets of `b` births
  have key : ∀ b : ℕ, ∑ p' : Fin b → P, ghStep_batchTerm bad u w b p' =
      ∑ T ∈ Finset.univ.filter (fun T : Finset P => T.card = b), ghStep_setTerm bad u w T := by
    intro b
    have hb : (b.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero b)
    refine (Finset.sum_congr rfl fun p' _ => ghStep_batchTerm_eq bad u w b p').trans ?_
    refine (ghStep_sum_injective b
      (fun T => ((b.factorial : ℝ))⁻¹ * ghStep_setTerm bad u w T)).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun T _ => mul_inv_cancel_left₀ hb _
  -- all sets of births
  have hcardT : ∀ T ∈ (Finset.univ : Finset (Finset P)), T.card ∈ Finset.range (N + 1) :=
    fun T _ => Finset.mem_range.mpr (Nat.lt_succ_of_le ((Finset.card_le_univ T).trans hN))
  have hall : ∑ b : Fin (N + 1),
        ∑ T ∈ Finset.univ.filter (fun T : Finset P => T.card = b.val), ghStep_setTerm bad u w T =
      ∑ T : Finset P, ghStep_setTerm bad u w T :=
    (Fin.sum_univ_eq_sum_range (fun b =>
      ∑ T ∈ Finset.univ.filter (fun T : Finset P => T.card = b), ghStep_setTerm bad u w T)
      (N + 1)).trans (Finset.sum_fiberwise_of_maps_to hcardT _)
  -- the product over the elements
  have hpt : ∀ p : P, ghStep_bornFactor bad u w p =
      (if bad p then 0 else w p) + (if bad p then 1 else u p) := by
    intro p
    unfold ghStep_bornFactor
    by_cases hp : bad p
    · rw [if_pos hp, if_pos hp, if_pos hp, zero_add]
    · rw [if_neg hp, if_neg hp, if_neg hp]
      exact add_comm _ _
  have hpt3 : ∀ (T : Finset P) (p : P),
      (if p ∈ Tᶜ then (if bad p then (1 : ℝ) else u p) else 1) =
        (if bad p then 1 else if p ∈ T then 1 else u p) := by
    intro T p
    by_cases hpT : p ∈ T
    · have hc : p ∉ Tᶜ := fun h => Finset.mem_compl.mp h hpT
      rw [if_neg hc, if_pos hpT]
      exact (ite_self 1).symm
    · have hc : p ∈ Tᶜ := Finset.mem_compl.mpr hpT
      rw [if_pos hc, if_neg hpT]
  have hprod : ∏ p : P, ghStep_bornFactor bad u w p = ∑ T : Finset P, ghStep_setTerm bad u w T := by
    refine ((Finset.prod_congr rfl fun p _ => hpt p).trans
      (Fintype.prod_add (fun p => if bad p then 0 else w p)
        (fun p => if bad p then 1 else u p))).trans ?_
    refine Finset.sum_congr rfl fun T _ => ?_
    unfold ghStep_setTerm
    by_cases hT : ∀ p ∈ T, ¬bad p
    · rw [if_pos hT]
      have e1 : ∏ p ∈ T, (if bad p then 0 else w p) = ∏ p ∈ T, w p :=
        Finset.prod_congr rfl fun p hp => if_neg (hT p hp)
      have e2 : ∏ p ∈ Tᶜ, (if bad p then (1 : ℝ) else u p) =
          ∏ p : P, (if bad p then 1 else if p ∈ T then 1 else u p) :=
        ((congrArg (fun s => ∏ p ∈ s, (if bad p then (1 : ℝ) else u p))
          (Finset.univ_inter Tᶜ).symm).trans
          (Finset.prod_ite_mem Finset.univ Tᶜ (fun p => if bad p then (1 : ℝ) else u p)).symm).trans
          (Finset.prod_congr rfl fun p _ => hpt3 T p)
      rw [e1, e2]
    · rw [if_neg hT]
      obtain ⟨p, hp, hbp⟩ : ∃ p ∈ T, bad p := by
        by_contra hcon
        exact hT fun p hp hb => hcon ⟨p, hp, hb⟩
      have h0 : ∏ p ∈ T, (if bad p then (0 : ℝ) else w p) = 0 :=
        Finset.prod_eq_zero hp (if_pos hbp)
      rw [h0, zero_mul]
  exact ((Finset.sum_congr rfl fun b _ => key b.val).trans hall).trans hprod.symm

/-! ### One prime before and after a visit operation -/

/-- **The factor of one prime in the product of the values, after a visit operation**, for the
conditions `inU` (born), `inB` (in the new batch), `act` (active), `inS` (terminated), `inSurv`
(a surviving pending prime), `inM` (pending before the operation): it is the product of the
factor of a terminated prime, the factor of a born prime before the operation, and the factor of
an unborn prime after it. -/
theorem ghStep_ite_third {inU inB act inS inSurv inM : Prop} {d1 : Decidable (inU ∨ inB)}
    {d2 : Decidable (act ∨ (inSurv ∨ inB))} {d3 : Decidable inS} {d4 : Decidable inU}
    {d5 : Decidable (act ∨ inM)} {d6 : Decidable inB} (d u : ℝ) (hM : inM ↔ inS ∨ inSurv)
    (hSS : inS → ¬inSurv) (hMU : inM → inU) (hMa : inM → ¬act) (hBU : inB → ¬inU) :
    @ite ℝ (inU ∨ inB) d1 (@ite ℝ (act ∨ (inSurv ∨ inB)) d2 1 d) u =
      @ite ℝ inS d3 d 1 * @ite ℝ inU d4 (@ite ℝ (act ∨ inM) d5 1 d) 1 *
        @ite ℝ inU d4 1 (@ite ℝ inB d6 1 u) := by
  by_cases hU : inU
  · have hB : ¬inB := fun h => hBU h hU
    rw [if_pos (Or.inl hU : inU ∨ inB), if_pos hU, if_pos hU, mul_one]
    by_cases hS : inS
    · have hMm : inM := hM.mpr (Or.inl hS)
      have h1 : ¬(act ∨ (inSurv ∨ inB)) := by
        rintro (h | h | h)
        · exact hMa hMm h
        · exact hSS hS h
        · exact hB h
      rw [if_neg h1, if_pos hS, if_pos (Or.inr hMm : act ∨ inM), mul_one]
    · have h2 : (act ∨ (inSurv ∨ inB)) ↔ (act ∨ inM) :=
        ⟨fun h => h.elim Or.inl fun h' =>
          h'.elim (fun h'' => Or.inr (hM.mpr (Or.inr h''))) (fun h'' => absurd h'' hB),
          fun h => h.elim Or.inl fun h' => Or.inr (Or.inl ((hM.mp h').resolve_left hS))⟩
      rw [if_neg hS, one_mul]
      exact bigRes_ite_congr h2 rfl rfl
  · have hMn : ¬inM := fun h => hU (hMU h)
    have hSn : ¬inS := fun h => hMn (hM.mpr (Or.inl h))
    rw [if_neg hSn, if_neg hU, if_neg hU, one_mul, one_mul]
    by_cases hB : inB
    · rw [if_pos (Or.inr hB : inU ∨ inB),
        if_pos (Or.inr (Or.inr hB) : act ∨ (inSurv ∨ inB)), if_pos hB]
    · rw [if_neg (fun h : inU ∨ inB => h.elim hU hB), if_neg hB]

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
