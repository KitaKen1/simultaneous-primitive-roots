module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.ChainInvariant
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.BigDampingFactor
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# (M4) The transfer chain of a prime sums to its lifespan sum: `ChainLifespan`

Source: `verification/stage7-sources/S-02.tex`, lines 538–567 (`[S-02:0538–0567]`), with
[S-02:0375–0383].

`chainLifespan : ChainLifespan` is proved here: for a skeleton with `BigValid`, under `RawHyp`,

`1_{inj₀} · ⊗μ̃(xb₀) · (chain N).eval xb₀ ∅ U₀ = 1_{BigInj} · (label normalization) · ∏_p lifeSum p`.

* `chn_eval_init` — the product of the values at the initial state (empty memories, the set of the
  initial labels) is a product over the big primes: `μ̃ · act` for an initial label, `unborn` for
  the other primes.
* `Skel.chain_factor` — by the closed forms of `Memory/ChainInvariant.lean` each factor is
  `V_g^{-1_{p initial}} · Z_0(p) · lifeSum p`.
* `chn_prod_initial`, `Skel.prod_zW`, `Skel.prod_zTail` — if the big lists are injective at every
  visit, the product of the weights is the label normalization `∏_g V_g^{-M} ∏_i ∏_g V_g^{-t_g}`:
  every slot of the initial lists and every unshared target slot is the entry of exactly one
  prime.
* `Skel.bigInj_of_zW_ne_zero` — if the initial lists are injective and no weight vanishes, the
  big lists are injective at every visit; so otherwise both sides are `0`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### Products over the values of an injective map -/

open _root_.Classical in
/-- A product over the values of an injective map. -/
theorem chn_prod_inj {ι α : Type*} [Fintype ι] [Fintype α] {f : ι → α}
    (hf : Function.Injective f) (F : α → ℝ) :
    ∏ a, (if ∃ i, f i = a then F a else 1) = ∏ i, F (f i) := by
  rw [← Finset.prod_filter]
  have him : (Finset.univ.filter fun a => ∃ i, f i = a) = Finset.univ.image f := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  rw [him, Finset.prod_image fun i _ j _ h => hf h]

open _root_.Classical in
/-- A constant product over the values of a map which is injective on a set. -/
theorem chn_prod_inj_on {ι α : Type*} [Fintype ι] [Fintype α] (f : ι → α) (P : ι → Prop)
    (hf : ∀ i j, P i → P j → f i = f j → i = j) (c : ℝ) :
    ∏ a, (if ∃ i, P i ∧ f i = a then c else 1) = ∏ i, if P i then c else 1 := by
  rw [← Finset.prod_filter, ← Finset.prod_filter]
  have him : (Finset.univ.filter fun a => ∃ i, P i ∧ f i = a) =
      (Finset.univ.filter P).image f := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  rw [him, Finset.prod_image fun i hi j hj h =>
    hf i j (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2 h]

variable {S B : Type} [Fintype S] [Fintype B] {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type}
  {D : MemData 𝒢 J ℓ N}

/-! ### Unshared slots -/

/-- A slot is unshared or one of the shared slots `Sum.inl j`, `j ∉ C`. -/
theorem chn_unshared_or (C : Finset (Fin J)) (sl : Slot J ℓ) :
    Unshared C sl ∨ ∃ j : Fin J, j ∉ C ∧ sl = Sum.inl j := by
  rcases sl with j | k
  · by_cases hj : j ∈ C
    · exact Or.inl hj
    · exact Or.inr ⟨j, hj, rfl⟩
  · exact Or.inl trivial

open _root_.Classical in
/-- There are `t = ℓ + |C|` unshared slots. -/
theorem chn_prod_unshared (C : Finset (Fin J)) (c : ℝ) :
    ∏ sl : Slot J ℓ, (if Unshared C sl then c else 1) = c ^ (ℓ + C.card) := by
  rw [Fintype.prod_sum_type]
  have h1 : ∏ j : Fin J, (if Unshared C (Sum.inl j : Slot J ℓ) then c else 1) = c ^ C.card :=
    ((Finset.prod_congr rfl fun j _ => bigRes_ite_congr Iff.rfl rfl rfl).trans
      (Fintype.prod_ite_mem C (fun _ => c))).trans (Finset.prod_const c)
  have h2 : ∏ k : Fin ℓ, (if Unshared C (Sum.inr k : Slot J ℓ) then c else 1) = c ^ ℓ := by
    rw [Finset.prod_congr rfl fun k _ =>
        if_pos (show Unshared C (Sum.inr k : Slot J ℓ) from trivial),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h1, h2, ← pow_add, add_comm]

/-! ### The product of the values at the initial state -/

omit [Fintype S] in
open _root_.Classical in
/-- The product of the values on a state whose memories are empty. -/
theorem PrimeVals.eval_of_size_zero {Bc : ℕ} (v : PrimeVals 𝒢) (xb : LabelList 𝒢.big J ℓ)
    (mem : (g : B) → Mem 𝒢 Bc g) (U : Finset ℕ) (hmem : ∀ g, (mem g).1.val = 0) :
    v.eval xb mem U =
      (∏ g, ∏ sl : Slot J ℓ, v.act g (xb g sl)) *
        ∏ g, ∏ p : {p : ℕ // p ∈ 𝒢.big g},
          if (p : ℕ) ∈ U then (if ∃ sl, xb g sl = p then 1 else v.dead g p)
          else v.unborn g p := by
  unfold PrimeVals.eval
  have h2 : (∏ g, ∏ j : Fin (mem g).1.val, v.pend g ((mem g).2 j)) = 1 :=
    Finset.prod_eq_one fun g _ => Finset.prod_eq_one fun j _ =>
      absurd j.isLt (by
        have h0 := hmem g
        omega)
  rw [h2, mul_one]
  refine congrArg (fun x => (∏ g, ∏ sl : Slot J ℓ, v.act g (xb g sl)) * x) ?_
  refine Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun p _ => ?_
  refine bigRes_ite_congr Iff.rfl (bigRes_ite_congr ?_ rfl rfl) rfl
  refine ⟨fun h => h.elim id fun h' => ?_, Or.inl⟩
  obtain ⟨j, -⟩ := h'
  have h0 := hmem g
  exact absurd j.isLt (by omega)

omit [Fintype S] in
open _root_.Classical in
/-- **The product of the values at the initial state** (empty memories, the set of the initial
labels, which are pairwise distinct), times the measure of the initial list: `μ̃_g(p) · act` for
an initial label and `unborn` for every other big prime. -/
theorem chn_eval_init (hdis : ∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g')) {Bc : ℕ}
    (v : PrimeVals 𝒢) (xb : LabelList 𝒢.big J ℓ)
    (hinj : Function.Injective fun a : B × Slot J ℓ => (xb a.1 a.2 : ℕ)) :
    bigListMass 𝒢 D.q D.n xb *
        v.eval xb (fun g => emptyMem 𝒢 Bc g)
          (Finset.univ.image fun a : B × Slot J ℓ => (xb a.1 a.2 : ℕ)) =
      ∏ g, ∏ p : {p : ℕ // p ∈ 𝒢.big g},
        if ∃ sl, xb g sl = p then tiltLaw (𝒢.big g) D.q D.n p * v.act g p
        else v.unborn g p := by
  have hxinj : ∀ g, Function.Injective (xb g) := fun g sl sl' h =>
    (Prod.mk.inj (@hinj (g, sl) (g, sl') (congrArg Subtype.val h))).2
  have hU : ∀ (g : B) (p : {p : ℕ // p ∈ 𝒢.big g}),
      ((p : ℕ) ∈ Finset.univ.image fun a : B × Slot J ℓ => (xb a.1 a.2 : ℕ)) ↔
        ∃ sl, xb g sl = p := by
    intro g p
    rw [Finset.mem_image]
    constructor
    · rintro ⟨⟨g', sl⟩, -, h⟩
      have h' : (xb g' sl : ℕ) = (p : ℕ) := h
      have hg : g' = g := by
        by_contra hne
        have hp' : (p : ℕ) ∈ 𝒢.big g' := by
          rw [← h']
          exact (xb g' sl).2
        exact Finset.disjoint_left.mp (hdis g' g hne) hp' p.2
      subst hg
      exact ⟨sl, Subtype.ext h'⟩
    · rintro ⟨sl, h⟩
      exact ⟨(g, sl), Finset.mem_univ _, congrArg Subtype.val h⟩
  rw [v.eval_of_size_zero xb (fun g => emptyMem 𝒢 Bc g) _ (fun g => rfl)]
  unfold bigListMass
  rw [← mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [← Finset.prod_mul_distrib,
    ← chn_prod_inj (hxinj g) (fun p => tiltLaw (𝒢.big g) D.q D.n p * v.act g p),
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  by_cases hp : ∃ sl, xb g sl = p
  · rw [if_pos hp, if_pos ((hU g p).mpr hp), if_pos hp, if_pos hp, mul_one]
  · have hnU : ¬((p : ℕ) ∈ Finset.univ.image fun a : B × Slot J ℓ => (xb a.1 a.2 : ℕ)) :=
      fun h => hp ((hU g p).mp h)
    rw [if_neg hp, if_neg hnU, if_neg hp, one_mul]

/-! ### The factor of one prime -/

/-- **The factor of one big prime at the initial state**: `V_g^{-1_{p initial}} · Z_0 · lifeSum p`
[S-02:0563–0567]. -/
theorem Skel.chain_factor [DecidableEq S] [DecidableEq B] [Fintype N] (sk : Skel D)
    (hR : RawHyp D) (hVal : sk.BigValid) (g : B) (p : {p : ℕ // p ∈ 𝒢.big g})
    {inst : Decidable (∃ sl, sk.xb₀ g sl = p)} :
    @ite ℝ (∃ sl, sk.xb₀ g sl = p) inst
        (tiltLaw (𝒢.big g) D.q D.n p * (sk.chain D.n).act g p) ((sk.chain D.n).unborn g p) =
      @ite ℝ (∃ sl, sk.xb₀ g sl = p) inst (Graph.primeGroupReciprocalMass (𝒢.big g))⁻¹ 1 *
        sk.zTail g p 0 * sk.lifeSum p := by
  have hiff : 0 ∈ sk.activeVisits p ↔ ∃ sl, sk.xb₀ g sl = p :=
    sk.mem_activeVisits_iff hR.disjoint_big g p 0 (Nat.zero_le _)
  by_cases h : ∃ sl, sk.xb₀ g sl = p
  · rw [if_pos h, if_pos h, sk.chain_act_zero hR hVal g p (hiff.mpr h)]
  · rw [if_neg h, if_neg h, one_mul,
      sk.chain_unborn_zero hR hVal g p (fun h0 => h (hiff.mp h0))]

/-! ### Products over the big primes -/

omit [Fintype S] in
/-- For pairwise disjoint big groups, a product over the groups and their primes is a product over
the big primes. -/
theorem chn_prod_bigPrimes (hdis : ∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g'))
    (f : ℕ → ℝ) :
    ∏ g, ∏ p : {p : ℕ // p ∈ 𝒢.big g}, f p = ∏ p ∈ bigPrimes 𝒢, f p := by
  have h1 : ∀ g : B, ∏ p : {p : ℕ // p ∈ 𝒢.big g}, f p = ∏ p ∈ 𝒢.big g, f p := fun g =>
    (Finset.prod_subtype (𝒢.big g) (fun _ => Iff.rfl) f).symm
  rw [Finset.prod_congr rfl fun g _ => h1 g]
  exact (Finset.prod_biUnion fun g _ g' _ hne => hdis g g' hne).symm

omit [Fintype S] in
theorem chn_prod_split (hdis : ∀ g g', g ≠ g' → Disjoint (𝒢.big g) (𝒢.big g'))
    (a z : (g : B) → {p : ℕ // p ∈ 𝒢.big g} → ℝ) (L : ℕ → ℝ) :
    ∏ g, ∏ p : {p : ℕ // p ∈ 𝒢.big g}, (a g p * z g p * L p) =
      (∏ g, ∏ p : {p : ℕ // p ∈ 𝒢.big g}, a g p) *
          (∏ g, ∏ p : {p : ℕ // p ∈ 𝒢.big g}, z g p) * ∏ p ∈ bigPrimes 𝒢, L p := by
  rw [← chn_prod_bigPrimes hdis L, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun g _ => ?_
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

omit [Fintype S] in
/-- "A first active birth costs `1/(V_g p b_p)`": the `M` slots of an injective initial list give
`∏_g V_g^{-M}`. -/
theorem chn_prod_initial (xb : LabelList 𝒢.big J ℓ) (hxinj : ∀ g, Function.Injective (xb g))
    {inst : ∀ (g : B) (p : {p : ℕ // p ∈ 𝒢.big g}), Decidable (∃ sl, xb g sl = p)} :
    ∏ g, ∏ p : {p : ℕ // p ∈ 𝒢.big g},
        @ite ℝ (∃ sl, xb g sl = p) (inst g p) (Graph.primeGroupReciprocalMass (𝒢.big g))⁻¹ 1 =
      bigListNorm 𝒢 J ℓ := by
  unfold bigListNorm
  refine Finset.prod_congr rfl fun g _ => ?_
  have h := chn_prod_inj (hxinj g) (fun _ => (Graph.primeGroupReciprocalMass (𝒢.big g))⁻¹)
  refine Eq.trans ?_ (h.trans ?_)
  · exact Finset.prod_congr rfl fun p _ => bigRes_ite_congr Iff.rfl rfl rfl
  · rw [Finset.prod_const, Finset.card_univ, card_slot, inv_pow]

omit [Fintype S] [Fintype B] in
/-- **The weights of one edge**: if the target list of the group `g` is injective, the product
over the primes of the group is `V_g^{-t_g}`, `t_g = ℓ + |C_g|` ("each of its later promotions
omit [Fintype S] [Fintype B] in
costs `1/V_g`"; a fresh birth costs `μ̃_g(p) = 1/(V_g p b_p)`). -/
theorem Skel.prod_zW (sk : Skel D) (e : Fin D.n) (g : B)
    (hSh : SharedBig (sk.Cset e) (sk.src e).2 (sk.tgt e).2)
    (hinj : Function.Injective ((sk.tgt e).2 g)) :
    ∏ p : {p : ℕ // p ∈ 𝒢.big g}, sk.zW g p e.val =
      (Graph.primeGroupReciprocalMass (𝒢.big g) ^ (ℓ + (sk.Cset e g).card))⁻¹ := by
  have hprod := chn_prod_inj_on (fun sl : Slot J ℓ => (sk.tgt e).2 g sl)
    (fun sl => Unshared (sk.Cset e g) sl) (fun a b _ _ h => hinj h)
    (Graph.primeGroupReciprocalMass (𝒢.big g))⁻¹
  refine (Eq.trans (Finset.prod_congr rfl fun p _ => ?_) hprod).trans ?_
  · by_cases h : ∃ sl : Slot J ℓ, Unshared (sk.Cset e g) sl ∧ (sk.tgt e).2 g sl = p
    · have hne : sk.entryCount e g p ≠ 0 := (sk.entryCount_ne_zero_iff e g p).mpr h
      have he1 : sk.entryCount e g p = 1 := by
        have hle := sk.entryCount_le_one e g p hinj
        omega
      have hS : ¬∃ j : Fin J, j ∉ sk.Cset e g ∧ (sk.src e).2 g (Sum.inl j) = p := by
        rintro ⟨j, hj, hjp⟩
        obtain ⟨sl, hsl, hslp⟩ := h
        have heq : sl = Sum.inl j := hinj (hslp.trans ((hSh g j hj).trans hjp).symm)
        rw [heq] at hsl
        exact hj hsl
      rw [if_pos h, sk.zW_one g p e he1 hS]
    · have he0 : sk.entryCount e g p = 0 := by
        by_contra hne
        exact h ((sk.entryCount_ne_zero_iff e g p).mp hne)
      rw [if_neg h, sk.zW_zero g p e he0]
  · exact (Finset.prod_congr rfl fun sl _ => bigRes_ite_congr Iff.rfl rfl rfl).trans
      ((chn_prod_unshared (sk.Cset e g) _).trans (inv_pow _ _))

omit [Fintype S] in
/-- **The weights of all edges**: if the big lists are injective at every visit, the product of
all weights is `∏_i ∏_g V_g^{-t_g}`. -/
theorem Skel.prod_zTail (sk : Skel D) (hVal : sk.BigValid) (hBI : sk.BigInj) :
    ∏ g, ∏ p : {p : ℕ // p ∈ 𝒢.big g}, sk.zTail g p 0 =
      ∏ e : Fin D.n, bigTargetNorm 𝒢 ℓ (sk.Cset e) := by
  have h1 : ∀ (g : B) (p : {p : ℕ // p ∈ 𝒢.big g}),
      sk.zTail g p 0 = ∏ e : Fin D.n, sk.zW g p e.val := by
    intro g p
    unfold Skel.zTail
    rw [← Finset.range_eq_Ico]
    exact (Fin.prod_univ_eq_prod_range (fun t => sk.zW g p t) D.n).symm
  calc ∏ g, ∏ p : {p : ℕ // p ∈ 𝒢.big g}, sk.zTail g p 0
      = ∏ g, ∏ p : {p : ℕ // p ∈ 𝒢.big g}, ∏ e : Fin D.n, sk.zW g p e.val :=
        Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun p _ => h1 g p
    _ = ∏ g, ∏ e : Fin D.n, ∏ p : {p : ℕ // p ∈ 𝒢.big g}, sk.zW g p e.val :=
        Finset.prod_congr rfl fun g _ => Finset.prod_comm
    _ = ∏ e : Fin D.n, ∏ g, ∏ p : {p : ℕ // p ∈ 𝒢.big g}, sk.zW g p e.val := Finset.prod_comm
    _ = ∏ e : Fin D.n, bigTargetNorm 𝒢 ℓ (sk.Cset e) :=
        Finset.prod_congr rfl fun e _ => Finset.prod_congr rfl fun g _ =>
          sk.prod_zW e g (hVal e).1
            ((sk.tgt_injective_iff e g).mpr (hBI (e.val + 1) (Nat.succ_le_of_lt e.isLt) g))

/-! ### Lists which are not injective -/

omit [Fintype S] [Fintype B] in
/-- If the initial big lists are injective and no weight of an edge vanishes, the big lists are
injective at every visit: a label which occurs twice in a target list occurs in two unshared
omit [Fintype S] [Fintype B] in
slots, or in a shared and an unshared slot (the source list being injective). -/
theorem Skel.bigInj_of_zW_ne_zero (sk : Skel D) (hVal : sk.BigValid)
    (h0 : ∀ g, Function.Injective (sk.xb₀ g))
    (hz : ∀ (e : Fin D.n) (g : B) (p : {p : ℕ // p ∈ 𝒢.big g}), sk.zW g p e.val ≠ 0) :
    sk.BigInj := by
  intro i
  induction i with
  | zero =>
    intro _ g
    exact h0 g
  | succ i ih =>
    intro hi g
    obtain ⟨e, he⟩ : ∃ e : Fin D.n, e.val = i := ⟨⟨i, hi⟩, rfl⟩
    subst he
    have hsrc : Function.Injective ((sk.src e).2 g) :=
      (sk.src_injective_iff e g).mpr (ih (Nat.le_of_lt e.isLt) g)
    refine (sk.tgt_injective_iff e g).mp ?_
    intro sl sl' hsl
    by_contra hne
    have hzw := hz e g ((sk.tgt e).2 g sl)
    rcases chn_unshared_or (sk.Cset e g) sl with hu | ⟨j, hj, rfl⟩
    · rcases chn_unshared_or (sk.Cset e g) sl' with hu' | ⟨j', hj', rfl⟩
      · have h2 := sk.one_lt_entryCount e g ((sk.tgt e).2 g sl) hne ⟨hu, rfl⟩ ⟨hu', hsl.symm⟩
        exact hzw (sk.zW_bad g _ e (Nat.ne_of_gt (Nat.lt_trans Nat.zero_lt_one h2))
          (fun h => absurd h.1 (Nat.ne_of_gt h2)))
      · have hne0 : sk.entryCount e g ((sk.tgt e).2 g sl) ≠ 0 :=
          (sk.entryCount_ne_zero_iff e g _).mpr ⟨sl, hu, rfl⟩
        have hS : ∃ j : Fin J, j ∉ sk.Cset e g ∧
            (sk.src e).2 g (Sum.inl j) = (sk.tgt e).2 g sl :=
          ⟨j', hj', ((hVal e).1 g j' hj').symm.trans hsl.symm⟩
        exact hzw (sk.zW_bad g _ e hne0 (fun h => h.2 hS))
    · rcases chn_unshared_or (sk.Cset e g) sl' with hu' | ⟨j', hj', rfl⟩
      · have hne0 : sk.entryCount e g ((sk.tgt e).2 g (Sum.inl j)) ≠ 0 :=
          (sk.entryCount_ne_zero_iff e g _).mpr ⟨sl', hu', hsl.symm⟩
        have hS : ∃ j₁ : Fin J, j₁ ∉ sk.Cset e g ∧
            (sk.src e).2 g (Sum.inl j₁) = (sk.tgt e).2 g (Sum.inl j) :=
          ⟨j, hj, ((hVal e).1 g j hj).symm⟩
        exact hzw (sk.zW_bad g _ e hne0 (fun h => h.2 hS))
      · exact hne (hsrc ((((hVal e).1 g j hj).symm.trans hsl).trans ((hVal e).1 g j' hj')))

omit [Fintype S] in
/-- If the initial big lists are injective but the lists at some visit are not, the weight of some
edge vanishes for some prime. -/
theorem Skel.exists_zW_eq_zero (sk : Skel D) (hVal : sk.BigValid)
    (h0 : ∀ g, Function.Injective (sk.xb₀ g)) (hBI : ¬sk.BigInj) :
    ∃ (e : Fin D.n) (g : B) (p : {p : ℕ // p ∈ 𝒢.big g}), sk.zW g p e.val = 0 := by
  by_contra hcon
  exact hBI (sk.bigInj_of_zW_ne_zero hVal h0 fun e g p hz => hcon ⟨e, g, p, hz⟩)

/-! ### The statement -/

open _root_.Classical in
/-- **(M4) The transfer chain of a prime sums to its lifespan sum** [S-02:0538–0567]: for a
skeleton with `BigValid`, under `RawHyp`, the measure of the initial big list times the product of
the values `chain N` at the initial state (zero if two initial slots have the same label) is
`1_{big lists injective at all visits} · (label normalization) · ∏_{p big} lifeSum p`. -/
theorem chainLifespan : ChainLifespan := by
  intro S B _ _ _ _ 𝒢 J ℓ N _ D Bc sk hR hVal
  by_cases hinj : Function.Injective (fun a : B × Slot J ℓ => (sk.xb₀ a.1 a.2 : ℕ))
  · have hxinj : ∀ g, Function.Injective (sk.xb₀ g) := fun g sl sl' h =>
      (Prod.mk.inj (@hinj (g, sl) (g, sl') (congrArg Subtype.val h))).2
    rw [if_pos hinj, chn_eval_init hR.disjoint_big (sk.chain D.n) sk.xb₀ hinj]
    refine (Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun p _ =>
      sk.chain_factor hR hVal g p).trans ?_
    refine (chn_prod_split hR.disjoint_big _ _ (fun p => sk.lifeSum p)).trans ?_
    by_cases hBI : sk.BigInj
    · rw [if_pos hBI, one_mul, chn_prod_initial sk.xb₀ hxinj, sk.prod_zTail hVal hBI]
      rfl
    · obtain ⟨e, g, p, hz⟩ := sk.exists_zW_eq_zero hVal hxinj hBI
      have hzt : sk.zTail g p 0 = 0 :=
        Finset.prod_eq_zero (Finset.mem_Ico.mpr ⟨Nat.zero_le _, e.isLt⟩) hz
      have hprod : ∏ g, ∏ p : {p : ℕ // p ∈ 𝒢.big g}, sk.zTail g p 0 = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ g) (Finset.prod_eq_zero (Finset.mem_univ p) hzt)
      rw [if_neg hBI, hprod]
      simp only [mul_zero, zero_mul]
  · have hBI : ¬sk.BigInj := by
      intro h
      apply hinj
      rintro ⟨g, sl⟩ ⟨g', sl'⟩ hab
      have hab' : (sk.xb₀ g sl : ℕ) = (sk.xb₀ g' sl' : ℕ) := hab
      have hg : g = g' := by
        by_contra hne
        have hmem : (sk.xb₀ g sl : ℕ) ∈ 𝒢.big g' := by
          rw [hab']
          exact (sk.xb₀ g' sl').2
        exact Finset.disjoint_left.mp (hR.disjoint_big g g' hne) (sk.xb₀ g sl).2 hmem
      subst hg
      have hsl : sl = sl' := h 0 (Nat.zero_le _) g (Subtype.ext hab')
      rw [hsl]
    rw [if_neg hinj, if_neg hBI, zero_mul, zero_mul]

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
