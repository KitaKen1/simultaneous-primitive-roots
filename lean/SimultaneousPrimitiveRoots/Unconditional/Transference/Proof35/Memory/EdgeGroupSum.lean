module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.EdgePrimeCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# One big group at an edge: the sum over the stores and promotions

Source: `verification/stage7-sources/S-02.tex`, lines 477–514 and 569–581
(`[S-02:0477–0514, 0569–0581]`).

The one-group theorem of the proof of (M3) `EdgeStepFactor`:

`Skel.edgeT_sum`: for a group in which every prime occurs at most once, the sum over the stored
slots and the promotions of the terms `Skel.edgeT` is the factor of the group in the product of
the values `sk.edgeStepVals i v`.

* If the target list is not compatible with the source state (`EdgeGood`), every term vanishes
  (`edg_good_of_valid`) and so does the right side (`Skel.edge_rhs_zero`).
* Otherwise only the promotions which the target labels determine contribute
  (`edg_promo_unique`); the term of the stores `st` is a product over the primes of the group
  (`Skel.EdgeCtx.edgeT_eq_prod`), which agrees with the right side except at the labels of the
  unshared source slots (`Skel.EdgeCtx.sum_promo`, `Skel.EdgeCtx.rhs_eq`); the sum over the sets
  of stored slots is the product over the unshared source slots of "stored + dropped"
  (`edg_sum_subsets`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

theorem edg_mul5 (a b c d e : ℝ) : a * b * c * d * e = a * (b * c * d * e) := by ring

/-- `V^{-#{i : P i}} = ∏_i V^{-1_{P i}}`, for an arbitrary decidability instance. -/
theorem edg_inv_pow_card {ι : Type*} [Fintype ι] (P : ι → Prop) {inst : DecidablePred P}
    (V : ℝ) :
    (V ^ (@Finset.filter ι P inst Finset.univ).card)⁻¹ = ∏ i, @ite ℝ (P i) (inst i) V⁻¹ 1 := by
  rw [← inv_pow, ← Finset.prod_const, Finset.prod_filter]

variable {S B : Type} [Fintype S] [Fintype B] {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {N : Type}
  {D : MemData 𝒢 J ℓ N}

omit [Fintype S] [Fintype B] in
/-- `ρ^{#zeros}` of a memory as a product over the primes of the group. -/
theorem edg_sigma_prod {g : B} (ρ : ℝ) (z : Mem 𝒢 Bc g) :
    ρ ^ memZeroCount z =
      ∏ p : {p : ℕ // p ∈ 𝒢.big g}, edgMid (fun w => chnPow ρ (w.2 = 0)) (List.ofFn z.2) p := by
  rw [l38_memZeroCount_eq, edg_rho_pow_countP]
  unfold edgMid
  exact edg_prod_by_key (fun w : Particle 𝒢 g => w.1) _ _

omit [Fintype S] [Fintype B] in
/-- The term of an admissible local choice. -/
theorem edgeTG_of_valid {g : B} (ρ V : ℝ) (μ : {p : ℕ // p ∈ 𝒢.big g} → ℝ) (v : PrimeVals 𝒢)
    (x y : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) (C : Finset (Fin J)) (Δ : ℤ) (Dil : ℕ)
    (z : Mem 𝒢 Bc g) (U : Finset ℕ) (st : Finset (Slot J ℓ))
    (pm : Slot J ℓ → Option (Fin Bc))
    (h : EdgeNewG y C U pm ∧ EdgeStoreG x C Dil st ∧ EdgePromoG y C Δ Dil z pm) :
    ∃ (i1 : DecidablePred fun sl : Slot J ℓ => pm sl ≠ none)
      (i2 : DecidablePred fun sl : Slot J ℓ => EdgeFreshG C pm sl),
      edgeTG ρ V μ v x y C Δ Dil z U (st, pm) =
        ρ ^ memZeroCount z *
              (V ^ (@Finset.filter _ (fun sl : Slot J ℓ => pm sl ≠ none) i1 Finset.univ).card)⁻¹ *
            (∏ sl : Slot J ℓ, @ite ℝ (EdgeFreshG C pm sl) (i2 sl) (μ (y sl)) 1) *
            ρ ^ memZeroCount (memOfList (Bc := Bc) (edgeAbsNewList Δ z x st pm)) *
          v.evalL g y (edgeAbsNewList Δ z x st pm) (U ∪ edgeFreshSet y C pm) :=
  ⟨_, _, if_pos h⟩

/-! ### The terms and the alternatives of the stores -/

/-- **The term of a local choice** (stored slots, promotions) of the big group `g` at the edge
`i`, for the memory `z` of the group and the set `U` of the primes born so far. -/
def Skel.edgeT (sk : Skel D) (i : Fin D.n) (v : PrimeVals 𝒢) (g : B) (z : Mem 𝒢 Bc g)
    (U : Finset ℕ) (c : Finset (Slot J ℓ) × (Slot J ℓ → Option (Fin Bc))) : ℝ :=
  edgeTG D.ρ (Graph.primeGroupReciprocalMass (𝒢.big g)) (fun p => tiltLaw (𝒢.big g) D.q D.n p) v
    ((sk.src i).2 g) ((sk.tgt i).2 g) (sk.Cset i g) (sk.step i) (sk.dilAt i) z U c

open _root_.Classical in
/-- The alternative "stored" of a source slot: an unshared slot whose label does not divide `D`
is stored with the residue `Δ` (and `ρ` if this residue is zero). -/
def Skel.edgeStA (sk : Skel D) (i : Fin D.n) (v : PrimeVals 𝒢) (g : B) (sl : Slot J ℓ) : ℝ :=
  if Unshared (sk.Cset i g) sl ∧
      ¬((((sk.src i).2 g sl : {p : ℕ // p ∈ 𝒢.big g}) : ℕ) ∣ sk.dilAt i) then
    chnPow D.ρ ((shiftParticle (sk.step i) (⟨(sk.src i).2 g sl, 0⟩ : Particle 𝒢 g)).2 = 0) *
      v.pend g (shiftParticle (sk.step i) ⟨(sk.src i).2 g sl, 0⟩)
  else 0

open _root_.Classical in
/-- The alternative "not stored" of a source slot: an unshared slot is dropped. -/
def Skel.edgeStB (sk : Skel D) (i : Fin D.n) (v : PrimeVals 𝒢) (g : B) (sl : Slot J ℓ) : ℝ :=
  if Unshared (sk.Cset i g) sl then v.dead g ((sk.src i).2 g sl) else 1

open _root_.Classical in
/-- The product of the factors of the primes which are not labels of unshared source slots. -/
def Skel.edgeK (sk : Skel D) (i : Fin D.n) (v : PrimeVals 𝒢) (g : B) {n : ℕ}
    (zf : Fin n → Particle 𝒢 g) (U : Finset ℕ) : ℝ :=
  ∏ p ∈ ((Finset.univ.filter fun sl : Slot J ℓ => Unshared (sk.Cset i g) sl).image
    ((sk.src i).2 g))ᶜ, sk.edgeR i v g zf U p

/-! ### The right side -/

/-- The right side is the product of the factors of the primes of the group. -/
theorem Skel.edge_rhs_prod (sk : Skel D) (i : Fin D.n) (v : PrimeVals 𝒢) (g : B) {n : ℕ}
    (zf : Fin n → Particle 𝒢 g) (U : Finset ℕ) (hx : Function.Injective ((sk.src i).2 g)) :
    (sk.edgeStepVals i v).evalL g ((sk.src i).2 g) (List.ofFn zf) U =
      ∏ p : {p : ℕ // p ∈ 𝒢.big g}, sk.edgeR i v g zf U p := by
  rw [PrimeVals.evalL_eq_edgEval, edgEval_eq_prod _ _ _ _ _ hx]
  exact Finset.prod_congr rfl fun p _ => rfl

/-- **If the target list is not compatible with the source state, the right side vanishes**: a
label which occurs twice in the target list, or the label of an unshared target slot which was
born and is not a pending particle which may be promoted, has the value `0` in each of its
possible conditions. -/
theorem Skel.edge_rhs_zero (sk : Skel D) (i : Fin D.n) (v : PrimeVals 𝒢) (g : B) {n : ℕ}
    (zf : Fin n → Particle 𝒢 g) (U : Finset ℕ)
    (H : EdgeGroupHyp ((sk.src i).2 g) ((sk.tgt i).2 g) (sk.Cset i g) zf U)
    (hbad : ¬EdgeGood ((sk.tgt i).2 g) (sk.Cset i g) (sk.step i) (sk.dilAt i) zf U) :
    (sk.edgeStepVals i v).evalL g ((sk.src i).2 g) (List.ofFn zf) U = 0 := by
  rw [PrimeVals.evalL_eq_edgEval]
  have key : ∀ p : {p : ℕ // p ∈ 𝒢.big g}, sk.entryCount i g p ≠ 0 →
      (∀ j : Fin n, (zf j).1 = p → (sk.edgeStepVals i v).pend g (zf j) = 0) →
      ((p : ℕ) ∉ U → (sk.edgeStepVals i v).unborn g p = 0) →
      edgEval ((sk.edgeStepVals i v).act g) ((sk.edgeStepVals i v).pend g)
        ((sk.edgeStepVals i v).dead g) ((sk.edgeStepVals i v).unborn g) ((sk.src i).2 g)
        (List.ofFn zf) U = 0 := by
    intro p he hpend hunb
    refine edgEval_eq_zero _ _ _ _ _ _ _ p (fun _ _ => sk.edgeStepVals_act_ne i v g p he) ?_
      (fun _ => sk.edgeStepVals_dead_ne i v g p he) hunb
    intro w hw hwp
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' zf w).mp hw
    exact hpend j hwp
  by_cases hinj : Function.Injective ((sk.tgt i).2 g)
  · have h1 : ¬∀ sl, Unshared (sk.Cset i g) sl →
        (∃ j : Fin n, (zf j).1 = (sk.tgt i).2 g sl ∧ (shiftParticle (sk.step i) (zf j)).2 = 0 ∧
          ¬(((zf j).1 : ℕ) ∣ sk.dilAt i)) ∨ ((sk.tgt i).2 g sl : ℕ) ∉ U :=
      fun h => hbad ⟨hinj, h⟩
    obtain ⟨sl, hsl⟩ := not_forall.mp h1
    obtain ⟨hu, hnot⟩ := _root_.not_imp.mp hsl
    obtain ⟨hnp, hnU⟩ := not_or.mp hnot
    have hU : ((sk.tgt i).2 g sl : ℕ) ∈ U := not_not.mp hnU
    have he : sk.entryCount i g ((sk.tgt i).2 g sl) ≠ 0 :=
      (sk.entryCount_ne_zero_iff i g _).mpr ⟨sl, hu, rfl⟩
    refine key _ he (fun j hj => ?_) (fun h => absurd hU h)
    refine sk.edgeStepVals_pend_none i v g (zf j).1 (zf j).2 ?_ ?_
    · rw [hj]
      exact he
    · rintro ⟨-, hsh, hdv⟩
      exact hnp ⟨j, hj, hsh, hdv⟩
  · obtain ⟨sl, sl', hy, hne⟩ :
        ∃ sl sl', (sk.tgt i).2 g sl = (sk.tgt i).2 g sl' ∧ sl ≠ sl' := by
      by_contra hcon
      exact hinj fun a b hab => by_contra fun hne => hcon ⟨a, b, hab, hne⟩
    rcases edg_unshared_or (sk.Cset i g) sl with hu | ⟨j, hj, rfl⟩
    · have he : sk.entryCount i g ((sk.tgt i).2 g sl) ≠ 0 :=
        (sk.entryCount_ne_zero_iff i g _).mpr ⟨sl, hu, rfl⟩
      rcases edg_unshared_or (sk.Cset i g) sl' with hu' | ⟨j', hj', rfl⟩
      · have h2 := sk.one_lt_entryCount i g ((sk.tgt i).2 g sl) hne ⟨hu, rfl⟩ ⟨hu', hy.symm⟩
        have hne1 : sk.entryCount i g ((sk.tgt i).2 g sl) ≠ 1 := Nat.ne_of_gt h2
        refine key _ he (fun j hj => ?_)
          (fun _ => sk.edgeStepVals_unborn_big i v g _ he hne1)
        refine sk.edgeStepVals_pend_none i v g (zf j).1 (zf j).2 ?_ ?_
        · rw [hj]
          exact he
        · rintro ⟨h1, -, -⟩
          rw [hj] at h1
          exact hne1 h1
      · have hxp : (sk.src i).2 g (Sum.inl j') = (sk.tgt i).2 g sl :=
          (H.hSh j' hj').symm.trans hy.symm
        have hU : ((sk.tgt i).2 g sl : ℕ) ∈ U := by
          rw [← hxp]
          exact H.hxU _
        exact key _ he (fun j hj => absurd (hxp.trans hj.symm) (H.hne _ j))
          (fun h => absurd hU h)
    · rcases edg_unshared_or (sk.Cset i g) sl' with hu' | ⟨j', hj', rfl⟩
      · have he : sk.entryCount i g ((sk.tgt i).2 g (Sum.inl j)) ≠ 0 :=
          (sk.entryCount_ne_zero_iff i g _).mpr ⟨sl', hu', hy.symm⟩
        have hxp : (sk.src i).2 g (Sum.inl j) = (sk.tgt i).2 g (Sum.inl j) :=
          (H.hSh j hj).symm
        have hU : ((sk.tgt i).2 g (Sum.inl j) : ℕ) ∈ U := by
          rw [← hxp]
          exact H.hxU _
        exact key _ he (fun j₁ hj₁ => absurd (hxp.trans hj₁.symm) (H.hne _ j₁))
          (fun h => absurd hU h)
      · exact absurd (H.hx (((H.hSh j hj).symm.trans hy).trans (H.hSh j' hj'))) hne

/-! ### The left side -/

section Sum

variable {sk : Skel D} {i : Fin D.n} {g : B} {n : ℕ} {zf : Fin n → Particle 𝒢 g}
  {U : Finset ℕ}

/-- The factors `V_g⁻¹` of the promotions and `μ̃_g` of the fresh births, slot by slot. -/
theorem Skel.EdgeCtx.kappa_prod (ctx : sk.EdgeCtx i g zf U) (hnB : n ≤ Bc)
    {i1 : DecidablePred fun sl : Slot J ℓ =>
      edgPromo hnB (sk.Cset i g) ((sk.tgt i).2 g) zf sl ≠ none}
    {i2 : DecidablePred fun sl : Slot J ℓ =>
      EdgeFreshG (sk.Cset i g) (edgPromo hnB (sk.Cset i g) ((sk.tgt i).2 g) zf) sl} :
    (Graph.primeGroupReciprocalMass (𝒢.big g) ^
          (@Finset.filter _ (fun sl : Slot J ℓ =>
            edgPromo hnB (sk.Cset i g) ((sk.tgt i).2 g) zf sl ≠ none) i1 Finset.univ).card)⁻¹ *
        ∏ sl : Slot J ℓ,
          @ite ℝ (EdgeFreshG (sk.Cset i g) (edgPromo hnB (sk.Cset i g) ((sk.tgt i).2 g) zf) sl)
            (i2 sl) (tiltLaw (𝒢.big g) D.q D.n ((sk.tgt i).2 g sl)) 1 =
      ∏ sl : Slot J ℓ, sk.edgeKappa i g zf ((sk.tgt i).2 g sl) := by
  rw [edg_inv_pow_card, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun sl _ => ?_
  rcases edg_unshared_or (sk.Cset i g) sl with hu | ⟨j, hj, rfl⟩
  · have he : sk.entryCount i g ((sk.tgt i).2 g sl) ≠ 0 :=
      (sk.entryCount_ne_zero_iff i g _).mpr ⟨sl, hu, rfl⟩
    by_cases hp : ∃ j : Fin n, (zf j).1 = (sk.tgt i).2 g sl
    · have h1 : edgPromo hnB (sk.Cset i g) ((sk.tgt i).2 g) zf sl ≠ none :=
        (edgPromo_ne_none_iff hnB _ _ zf ctx.hyp.hz sl).mpr ⟨hu, hp⟩
      have h2 : ¬EdgeFreshG (sk.Cset i g)
          (edgPromo hnB (sk.Cset i g) ((sk.tgt i).2 g) zf) sl := fun hf =>
        ((edgPromo_fresh_iff hnB _ _ zf ctx.hyp.hz sl).mp hf).2 hp
      rw [if_pos h1, if_neg h2, mul_one, sk.edgeKappa_pend _ he hp]
    · have h1 : ¬(edgPromo hnB (sk.Cset i g) ((sk.tgt i).2 g) zf sl ≠ none) := fun hne =>
        hp ((edgPromo_ne_none_iff hnB _ _ zf ctx.hyp.hz sl).mp hne).2
      have h2 : EdgeFreshG (sk.Cset i g)
          (edgPromo hnB (sk.Cset i g) ((sk.tgt i).2 g) zf) sl :=
        (edgPromo_fresh_iff hnB _ _ zf ctx.hyp.hz sl).mpr ⟨hu, hp⟩
      rw [if_neg h1, if_pos h2, one_mul, sk.edgeKappa_fresh _ he hp]
  · have h0 : edgPromo hnB (sk.Cset i g) ((sk.tgt i).2 g) zf (Sum.inl j) = none :=
      edgPromo_none hnB _ _ zf (Sum.inl j) fun h => hj h.1
    have h1 : ¬(edgPromo hnB (sk.Cset i g) ((sk.tgt i).2 g) zf (Sum.inl j) ≠ none) :=
      fun hne => hne h0
    have h2 : ¬EdgeFreshG (sk.Cset i g)
        (edgPromo hnB (sk.Cset i g) ((sk.tgt i).2 g) zf) (Sum.inl j) := fun hf => hj hf.1
    have he : sk.entryCount i g ((sk.tgt i).2 g (Sum.inl j)) = 0 :=
      ctx.shared_entry _ ⟨j, hj, (ctx.hyp.hSh j hj).symm⟩
    rw [if_neg h1, if_neg h2, one_mul, sk.edgeKappa_zero _ he]

/-- **The term of admissible stores, with the promotions which the target labels determine, is
the product of the factors `Skel.edgeLam` of the primes of the group.** -/
theorem Skel.EdgeCtx.edgeT_eq_prod (ctx : sk.EdgeCtx i g zf U) (hn : n < Bc + 1)
    (hnB : n ≤ Bc) (hcard : (𝒢.big g).card ≤ Bc) (v : PrimeVals 𝒢) (st : Finset (Slot J ℓ))
    (hst : EdgeStoreG ((sk.src i).2 g) (sk.Cset i g) (sk.dilAt i) st) :
    sk.edgeT i v g (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) U
        (st, edgPromo hnB (sk.Cset i g) ((sk.tgt i).2 g) zf) =
      ∏ p : {p : ℕ // p ∈ 𝒢.big g}, sk.edgeLam i v g hn hnB zf U st p := by
  have hval := edgPromo_valid ctx.hyp hn hnB ctx.good
  have hlen : (edgeAbsNewList (sk.step i) (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) ((sk.src i).2 g) st
      (edgPromo hnB (sk.Cset i g) ((sk.tgt i).2 g) zf)).length ≤ Bc := by
    have h1 : (edgeAbsNewList (sk.step i) (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) ((sk.src i).2 g) st
        (edgPromo hnB (sk.Cset i g) ((sk.tgt i).2 g) zf)).length ≤ n + st.card :=
      edgeAbsNewList_length_le _ _ _ _ _
    have h2 := edg_size_le zf ((sk.src i).2 g) ctx.hyp.hx ctx.hyp.hz ctx.hyp.hne
    have h3 : st.card ≤ J + ℓ := by
      rw [← card_slot J ℓ]
      exact Finset.card_le_univ st
    omega
  obtain ⟨i1, i2, hterm⟩ := edgeTG_of_valid D.ρ (Graph.primeGroupReciprocalMass (𝒢.big g))
    (fun p => tiltLaw (𝒢.big g) D.q D.n p) v ((sk.src i).2 g) ((sk.tgt i).2 g) (sk.Cset i g)
    (sk.step i) (sk.dilAt i) (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) U st
    (edgPromo hnB (sk.Cset i g) ((sk.tgt i).2 g) zf) ⟨hval.1, hst, hval.2⟩
  unfold Skel.edgeT
  rw [hterm, edg_mul5, ctx.kappa_prod hnB, edg_sigma_prod D.ρ (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g),
    edg_rho_pow_memZeroCount_memOfList D.ρ hlen, v.evalL_eq_edgEval,
    ← edgEval_mul (sk.edgeKappa i g zf) (v.act g) (fun w => chnPow D.ρ (w.2 = 0)) (v.pend g)
      (v.dead g) (v.unborn g),
    edgEval_eq_prod _ _ _ _ _ ctx.good.1, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p _ => rfl

open _root_.Classical in
/-- **The sum over the promotions**, for a set `st` of stored slots: the product over the source
slots of the alternative chosen by `st`, times the factors of the other primes. -/
theorem Skel.EdgeCtx.sum_promo (ctx : sk.EdgeCtx i g zf U) (hn : n < Bc + 1) (hnB : n ≤ Bc)
    (hcard : (𝒢.big g).card ≤ Bc) (v : PrimeVals 𝒢) (st : Finset (Slot J ℓ)) :
    ∑ pm : Slot J ℓ → Option (Fin Bc),
        sk.edgeT i v g (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) U (st, pm) =
      (∏ sl : Slot J ℓ, if sl ∈ st then sk.edgeStA i v g sl else sk.edgeStB i v g sl) *
        sk.edgeK i v g zf U := by
  have h1 : ∑ pm : Slot J ℓ → Option (Fin Bc),
        sk.edgeT i v g (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) U (st, pm) =
      sk.edgeT i v g (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) U
        (st, edgPromo hnB (sk.Cset i g) ((sk.tgt i).2 g) zf) := by
    refine Fintype.sum_eq_single _ fun pm hpm => ?_
    unfold Skel.edgeT edgeTG
    exact if_neg fun h => hpm (edg_promo_unique ctx.hyp hn hnB h.1 h.2.2)
  rw [h1]
  by_cases hst : EdgeStoreG ((sk.src i).2 g) (sk.Cset i g) (sk.dilAt i) st
  · rw [ctx.edgeT_eq_prod hn hnB hcard v st hst,
      edg_prod_split ((sk.src i).2 g) ctx.hyp.hx (fun sl => Unshared (sk.Cset i g) sl)
        (fun p => sk.edgeLam i v g hn hnB zf U st p)]
    unfold Skel.edgeK
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun sl _ => ?_)
      (Finset.prod_congr rfl fun p hp => ?_)
    · by_cases hu : Unshared (sk.Cset i g) sl
      · rw [if_pos hu, ctx.lam_unshared hn hnB v st sl hu]
        by_cases hsl : sl ∈ st
        · rw [if_pos hsl, if_pos hsl]
          unfold Skel.edgeStA
          rw [if_pos (hst sl hsl)]
        · rw [if_neg hsl, if_neg hsl]
          unfold Skel.edgeStB
          rw [if_pos hu]
      · have hsl : sl ∉ st := fun h => hu (hst sl h).1
        rw [if_neg hu, if_neg hsl]
        unfold Skel.edgeStB
        rw [if_neg hu]
    · refine ctx.lam_eq_R hn hnB v st hst p fun ⟨sl, hu, hx⟩ => ?_
      rw [Finset.mem_compl, Finset.mem_image] at hp
      exact hp ⟨sl, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hu⟩, hx⟩
  · have h0 : sk.edgeT i v g (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) U
        (st, edgPromo hnB (sk.Cset i g) ((sk.tgt i).2 g) zf) = 0 := by
      unfold Skel.edgeT edgeTG
      exact if_neg fun h => hst h.2.1
    obtain ⟨sl, hsl, hbad⟩ : ∃ sl ∈ st, ¬(Unshared (sk.Cset i g) sl ∧
        ¬((((sk.src i).2 g sl : {p : ℕ // p ∈ 𝒢.big g}) : ℕ) ∣ sk.dilAt i)) := by
      by_contra hcon
      exact hst fun sl hsl => not_not.mp fun h => hcon ⟨sl, hsl, h⟩
    have hz : (if sl ∈ st then sk.edgeStA i v g sl else sk.edgeStB i v g sl) = 0 := by
      rw [if_pos hsl]
      unfold Skel.edgeStA
      exact if_neg hbad
    rw [h0, Finset.prod_eq_zero
      (f := fun sl => if sl ∈ st then sk.edgeStA i v g sl else sk.edgeStB i v g sl)
      (Finset.mem_univ sl) hz, zero_mul]

open _root_.Classical in
/-- **The right side**: the product over the source slots of the sum of the two alternatives,
times the factors of the other primes. -/
theorem Skel.EdgeCtx.rhs_eq (ctx : sk.EdgeCtx i g zf U) (v : PrimeVals 𝒢) :
    ∏ p : {p : ℕ // p ∈ 𝒢.big g}, sk.edgeR i v g zf U p =
      (∏ sl : Slot J ℓ, (sk.edgeStA i v g sl + sk.edgeStB i v g sl)) * sk.edgeK i v g zf U := by
  rw [edg_prod_split ((sk.src i).2 g) ctx.hyp.hx (fun sl => Unshared (sk.Cset i g) sl)
    (fun p => sk.edgeR i v g zf U p)]
  unfold Skel.edgeK
  refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun sl _ => ?_) rfl
  by_cases hu : Unshared (sk.Cset i g) sl
  · rw [if_pos hu, ctx.R_unshared v sl hu]
    unfold Skel.edgeStA Skel.edgeStB
    rw [if_pos hu]
    by_cases hdv : (((sk.src i).2 g sl : {p : ℕ // p ∈ 𝒢.big g}) : ℕ) ∣ sk.dilAt i
    · rw [if_pos hdv, if_neg (fun h : Unshared (sk.Cset i g) sl ∧
        ¬((((sk.src i).2 g sl : {p : ℕ // p ∈ 𝒢.big g}) : ℕ) ∣ sk.dilAt i) => h.2 hdv)]
    · rw [if_neg hdv, if_pos (And.intro hu hdv)]
  · unfold Skel.edgeStA Skel.edgeStB
    rw [if_neg hu, if_neg (fun h : Unshared (sk.Cset i g) sl ∧
      ¬((((sk.src i).2 g sl : {p : ℕ // p ∈ 𝒢.big g}) : ℕ) ∣ sk.dilAt i) => hu h.1),
      if_neg hu, zero_add]

end Sum

/-! ### The one-group theorem -/

/-- **The sum over the stores and promotions of one big group** [S-02:0477–0514, 0569–0581]: for
a group in which every prime occurs at most once (the source list is injective, the pending
particles have distinct primes which are not active, every prime which is present was born), at
an edge whose shared labels are copied, the sum of the terms of the local choices is the factor
of the group in the product of the values `sk.edgeStepVals i v`. -/
theorem Skel.edgeT_sum (sk : Skel D) (i : Fin D.n) (v : PrimeVals 𝒢) (g : B) (z : Mem 𝒢 Bc g)
    (U : Finset ℕ) (hSh : SharedBig (sk.Cset i) (sk.src i).2 (sk.tgt i).2)
    (hx : Function.Injective ((sk.src i).2 g))
    (hz : Function.Injective fun j : Fin z.1.val => (z.2 j).1)
    (hne : ∀ sl (j : Fin z.1.val), (sk.src i).2 g sl ≠ (z.2 j).1)
    (hzU : ∀ j : Fin z.1.val, ((z.2 j).1 : ℕ) ∈ U)
    (hxU : ∀ sl, ((sk.src i).2 g sl : ℕ) ∈ U) (hcard : (𝒢.big g).card ≤ Bc) :
    ∑ c : Finset (Slot J ℓ) × (Slot J ℓ → Option (Fin Bc)), sk.edgeT i v g z U c =
      (sk.edgeStepVals i v).evalL g ((sk.src i).2 g) (List.ofFn z.2) U := by
  obtain ⟨⟨n, hn⟩, zf⟩ := z
  have hnB : n ≤ Bc := Nat.le_of_lt_succ hn
  have H : EdgeGroupHyp ((sk.src i).2 g) ((sk.tgt i).2 g) (sk.Cset i g) zf U :=
    ⟨hx, hz, hne, hzU, hxU, fun j hj => hSh g j hj⟩
  show ∑ c : Finset (Slot J ℓ) × (Slot J ℓ → Option (Fin Bc)),
      sk.edgeT i v g (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) U c =
    (sk.edgeStepVals i v).evalL g ((sk.src i).2 g) (List.ofFn zf) U
  by_cases hgood : EdgeGood ((sk.tgt i).2 g) (sk.Cset i g) (sk.step i) (sk.dilAt i) zf U
  · have ctx : sk.EdgeCtx i g zf U := ⟨H, hgood, hSh⟩
    rw [Fintype.sum_prod_type, Finset.sum_congr rfl fun st _ => ctx.sum_promo hn hnB hcard v st,
      ← Finset.sum_mul, edg_sum_subsets, sk.edge_rhs_prod i v g zf U hx, ctx.rhs_eq v]
  · rw [sk.edge_rhs_zero i v g zf U H hgood]
    refine Finset.sum_eq_zero fun c _ => ?_
    unfold Skel.edgeT edgeTG
    exact if_neg fun h => hgood (edg_good_of_valid H hn hnB h.1 h.2.2)

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
