module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.EdgeGroupValid
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.ChainSkel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# One big prime at an edge: the factor before and after

Source: `verification/stage7-sources/S-02.tex`, lines 477–514 and 569–581
(`[S-02:0477–0514, 0569–0581]`): "Its active visits determine exactly when it is shared, stored,
promoted, or dropped … Between these uses it must remain pending."

Tools for the proof of (M3) `EdgeStepFactor`, for the group `g` at the edge `i` of a skeleton, a
memory with the particles `zf` and the set `U` of the primes born so far, when the target list is
compatible with the source state (`Skel.EdgeCtx`).

* `Skel.edgeR` — the factor of the prime `p` in the product of the values `sk.edgeStepVals i v` at
  the source state (the right side of (M3)).
* `Skel.edgeLam` — the factor of the prime `p` in the term of the stores `st` (with the promotions
  which the target labels determine): `ρ` if `p` is a pending zero, the factor `Skel.edgeKappa`
  (`V_g⁻¹` for a promotion, `μ̃_g(p)` for a fresh birth), `ρ` if `p` is pending with residue zero
  after the edge, and the value `v` of `p` in its new condition.
* `Skel.EdgeCtx.lam_eq_R` — for a prime which is not the label of an unshared source slot the two
  factors agree: shared (active → active), pending (→ pending or promoted), dead (→ dead), unborn
  (→ unborn or born in an unshared target slot).
* `Skel.EdgeCtx.lam_unshared`, `Skel.EdgeCtx.R_unshared` — the label of an unshared source slot is
  stored or dropped; the right side is the sum of the two alternatives.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

variable {S B : Type} [Fintype S] [Fintype B] {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {N : Type}
  {D : MemData 𝒢 J ℓ N}

/-! ### The particles of a memory with a given prime -/

omit [Fintype S] [Fintype B] in
theorem edgMid_ofFn_none {g : B} (b : Particle 𝒢 g → ℝ) {n : ℕ} (zf : Fin n → Particle 𝒢 g)
    (p : {p : ℕ // p ∈ 𝒢.big g}) (h : ∀ j, (zf j).1 ≠ p) : edgMid b (List.ofFn zf) p = 1 := by
  rw [edgMid_ofFn]
  exact Finset.prod_eq_one fun j _ => if_neg (h j)

omit [Fintype S] [Fintype B] in
theorem edgMid_ofFn_single {g : B} (b : Particle 𝒢 g → ℝ) {n : ℕ} (zf : Fin n → Particle 𝒢 g)
    (hz : Function.Injective fun j : Fin n => (zf j).1) (j₀ : Fin n) :
    edgMid b (List.ofFn zf) (zf j₀).1 = b (zf j₀) := by
  rw [edgMid_ofFn]
  refine (Fintype.prod_eq_single j₀ fun j hj => ?_).trans ?_
  · exact if_neg fun h => hj (hz h)
  · exact if_pos rfl

/-! ### More values of the edge operation -/

section Vals

variable (sk : Skel D) (i : Fin D.n) (v : PrimeVals 𝒢) (g : B) (p : {p : ℕ // p ∈ 𝒢.big g})

/-- A prime with an entry cannot be active before the edge. -/
theorem Skel.edgeStepVals_act_ne (he : sk.entryCount i g p ≠ 0) :
    (sk.edgeStepVals i v).act g p = 0 := by
  by_cases hS : ∃ j : Fin J, j ∉ sk.Cset i g ∧ (sk.src i).2 g (Sum.inl j) = p
  · exact sk.edgeStepVals_act_shared_ne i v g p hS he
  · exact sk.edgeStepVals_act_unshared_ne i v g p hS he

/-- An unshared active prime with `p ∤ D` is stored or dropped. -/
theorem Skel.edgeStepVals_act_store
    (hS : ¬∃ j : Fin J, j ∉ sk.Cset i g ∧ (sk.src i).2 g (Sum.inl j) = p)
    (he : sk.entryCount i g p = 0) (hdv : ¬((p : ℕ) ∣ sk.dilAt i)) :
    (sk.edgeStepVals i v).act g p =
      chnPow D.ρ ((shiftParticle (sk.step i) (⟨p, 0⟩ : Particle 𝒢 g)).2 = 0) *
          v.pend g (shiftParticle (sk.step i) ⟨p, 0⟩) + v.dead g p := by
  refine (if_neg hS).trans ((if_pos he).trans ?_)
  rw [if_neg hdv, chn_pow_ite]

/-- An unshared active prime with `p ∣ D` is dropped. -/
theorem Skel.edgeStepVals_act_drop
    (hS : ¬∃ j : Fin J, j ∉ sk.Cset i g ∧ (sk.src i).2 g (Sum.inl j) = p)
    (he : sk.entryCount i g p = 0) (hdv : (p : ℕ) ∣ sk.dilAt i) :
    (sk.edgeStepVals i v).act g p = v.dead g p := by
  refine (if_neg hS).trans ((if_pos he).trans ?_)
  rw [if_pos hdv, zero_add]

end Vals

/-! ### The factors of a prime -/

/-- **The target list of the group `g` at the edge `i` is compatible with the source state**
(the particles `zf`, the born primes `U`). -/
structure Skel.EdgeCtx (sk : Skel D) (i : Fin D.n) (g : B) {n : ℕ} (zf : Fin n → Particle 𝒢 g)
    (U : Finset ℕ) : Prop where
  hyp : EdgeGroupHyp ((sk.src i).2 g) ((sk.tgt i).2 g) (sk.Cset i g) zf U
  good : EdgeGood ((sk.tgt i).2 g) (sk.Cset i g) (sk.step i) (sk.dilAt i) zf U
  shared : SharedBig (sk.Cset i) (sk.src i).2 (sk.tgt i).2

/-- The new memory of the group for the stores `st` and the promotions which the target labels
determine. -/
abbrev Skel.edgeNewL (sk : Skel D) (i : Fin D.n) (g : B) {n : ℕ} (hn : n < Bc + 1) (hnB : n ≤ Bc)
    (zf : Fin n → Particle 𝒢 g) (st : Finset (Slot J ℓ)) : List (Particle 𝒢 g) :=
  edgeAbsNewList (sk.step i) (⟨⟨n, hn⟩, zf⟩ : Mem 𝒢 Bc g) ((sk.src i).2 g) st
    (edgPromo hnB (sk.Cset i g) ((sk.tgt i).2 g) zf)

/-- The primes born after the edge: the born primes and the fresh labels of the group. -/
abbrev Skel.edgeNewU (sk : Skel D) (i : Fin D.n) (g : B) {n : ℕ} (hnB : n ≤ Bc)
    (zf : Fin n → Particle 𝒢 g) (U : Finset ℕ) : Finset ℕ :=
  U ∪ edgeFreshSet ((sk.tgt i).2 g) (sk.Cset i g)
    (edgPromo hnB (sk.Cset i g) ((sk.tgt i).2 g) zf)

open _root_.Classical in
/-- The factor of the entry of the prime `p`: `V_g⁻¹` for a promotion, `μ̃_g(p)` for a fresh
birth, `1` without entry. -/
def Skel.edgeKappa (sk : Skel D) (i : Fin D.n) (g : B) {n : ℕ} (zf : Fin n → Particle 𝒢 g)
    (p : {p : ℕ // p ∈ 𝒢.big g}) : ℝ :=
  if sk.entryCount i g p = 0 then 1
  else if ∃ j : Fin n, (zf j).1 = p then (Graph.primeGroupReciprocalMass (𝒢.big g))⁻¹
  else tiltLaw (𝒢.big g) D.q D.n p

/-- **The factor of the prime `p` in the term of the stores `st`.** -/
def Skel.edgeLam (sk : Skel D) (i : Fin D.n) (v : PrimeVals 𝒢) (g : B) {n : ℕ}
    (hn : n < Bc + 1) (hnB : n ≤ Bc) (zf : Fin n → Particle 𝒢 g) (U : Finset ℕ)
    (st : Finset (Slot J ℓ)) (p : {p : ℕ // p ∈ 𝒢.big g}) : ℝ :=
  edgMid (fun w => chnPow D.ρ (w.2 = 0)) (List.ofFn zf) p *
    edgPF (fun p => sk.edgeKappa i g zf p * v.act g p)
      (fun w => chnPow D.ρ (w.2 = 0) * v.pend g w) (v.dead g) (v.unborn g) ((sk.tgt i).2 g)
      (sk.edgeNewL i g hn hnB zf st) (sk.edgeNewU i g hnB zf U) p

/-- **The factor of the prime `p` in the product of the values after the edge operation**, at the
source state. -/
def Skel.edgeR (sk : Skel D) (i : Fin D.n) (v : PrimeVals 𝒢) (g : B) {n : ℕ}
    (zf : Fin n → Particle 𝒢 g) (U : Finset ℕ) (p : {p : ℕ // p ∈ 𝒢.big g}) : ℝ :=
  edgPF ((sk.edgeStepVals i v).act g) ((sk.edgeStepVals i v).pend g)
    ((sk.edgeStepVals i v).dead g) ((sk.edgeStepVals i v).unborn g) ((sk.src i).2 g)
    (List.ofFn zf) U p

section Cases

variable {sk : Skel D} {i : Fin D.n} {g : B} {n : ℕ} {zf : Fin n → Particle 𝒢 g}
  {U : Finset ℕ}

omit [Fintype S] [Fintype B] in
theorem Skel.edgeKappa_zero (p : {p : ℕ // p ∈ 𝒢.big g}) (he : sk.entryCount i g p = 0) :
    sk.edgeKappa i g zf p = 1 := if_pos he

omit [Fintype S] [Fintype B] in
theorem Skel.edgeKappa_pend (p : {p : ℕ // p ∈ 𝒢.big g}) (he : sk.entryCount i g p ≠ 0)
    (hp : ∃ j : Fin n, (zf j).1 = p) :
    sk.edgeKappa i g zf p = (Graph.primeGroupReciprocalMass (𝒢.big g))⁻¹ :=
  (if_neg he).trans (if_pos hp)

omit [Fintype S] [Fintype B] in
theorem Skel.edgeKappa_fresh (p : {p : ℕ // p ∈ 𝒢.big g}) (he : sk.entryCount i g p ≠ 0)
    (hp : ¬∃ j : Fin n, (zf j).1 = p) :
    sk.edgeKappa i g zf p = tiltLaw (𝒢.big g) D.q D.n p :=
  (if_neg he).trans (if_neg hp)

/-! #### The right side, by the condition of the prime -/

theorem Skel.edgeR_act (v : PrimeVals 𝒢)
    (H : EdgeGroupHyp ((sk.src i).2 g) ((sk.tgt i).2 g) (sk.Cset i g) zf U) (sl : Slot J ℓ) :
    sk.edgeR i v g zf U ((sk.src i).2 g sl) =
      (sk.edgeStepVals i v).act g ((sk.src i).2 g sl) := by
  unfold Skel.edgeR
  exact edgPF_act _ _ _ _ _ _ _ _ ⟨sl, rfl⟩
    (edgMid_ofFn_none _ zf _ fun j h => H.hne sl j h.symm) (H.hxU sl)

theorem Skel.edgeR_pend (v : PrimeVals 𝒢)
    (H : EdgeGroupHyp ((sk.src i).2 g) ((sk.tgt i).2 g) (sk.Cset i g) zf U) (j₀ : Fin n) :
    sk.edgeR i v g zf U (zf j₀).1 = (sk.edgeStepVals i v).pend g (zf j₀) := by
  have hx : ¬∃ sl, (sk.src i).2 g sl = (zf j₀).1 := fun ⟨sl, h⟩ => H.hne sl j₀ h
  unfold Skel.edgeR
  rw [edgPF_pend _ _ _ _ _ _ _ _ hx ((ghStep_exists_ofFn zf _).mpr ⟨j₀, rfl⟩) (H.hzU j₀)]
  exact edgMid_ofFn_single _ zf H.hz j₀

theorem Skel.edgeR_dead (v : PrimeVals 𝒢) (p : {p : ℕ // p ∈ 𝒢.big g})
    (hx : ¬∃ sl, (sk.src i).2 g sl = p) (hz : ∀ j : Fin n, (zf j).1 ≠ p) (hU : (p : ℕ) ∈ U) :
    sk.edgeR i v g zf U p = (sk.edgeStepVals i v).dead g p := by
  have hL : ¬∃ w ∈ List.ofFn zf, w.1 = p := fun h => by
    obtain ⟨j, hj⟩ := (ghStep_exists_ofFn zf p).mp h
    exact hz j hj
  unfold Skel.edgeR
  exact edgPF_dead _ _ _ _ _ _ _ _ hx (edgMid_ofFn_none _ zf p hz) hL hU

theorem Skel.edgeR_unborn (v : PrimeVals 𝒢) (p : {p : ℕ // p ∈ 𝒢.big g})
    (hx : ¬∃ sl, (sk.src i).2 g sl = p) (hz : ∀ j : Fin n, (zf j).1 ≠ p) (hU : (p : ℕ) ∉ U) :
    sk.edgeR i v g zf U p = (sk.edgeStepVals i v).unborn g p := by
  unfold Skel.edgeR
  exact edgPF_unborn _ _ _ _ _ _ _ _ hx (edgMid_ofFn_none _ zf p hz) hU

/-! #### Facts about the entries -/

/-- A prime with an entry is the prime of a pending particle which may be promoted, or was not
born. -/
theorem Skel.EdgeCtx.entry_cases (ctx : sk.EdgeCtx i g zf U) (p : {p : ℕ // p ∈ 𝒢.big g})
    (he : sk.entryCount i g p ≠ 0) :
    (∃ j : Fin n, (zf j).1 = p ∧ (shiftParticle (sk.step i) (zf j)).2 = 0 ∧
      ¬(((zf j).1 : ℕ) ∣ sk.dilAt i)) ∨ (p : ℕ) ∉ U := by
  obtain ⟨sl, hu, hy⟩ := (sk.entryCount_ne_zero_iff i g p).mp he
  rw [← hy]
  exact ctx.good.2 sl hu

theorem Skel.EdgeCtx.entry_eq_one (ctx : sk.EdgeCtx i g zf U) (p : {p : ℕ // p ∈ 𝒢.big g})
    (he : sk.entryCount i g p ≠ 0) : sk.entryCount i g p = 1 := by
  have h := sk.entryCount_le_one i g p ctx.good.1
  omega

/-- A shared source label has no entry. -/
theorem Skel.EdgeCtx.shared_entry (ctx : sk.EdgeCtx i g zf U) (p : {p : ℕ // p ∈ 𝒢.big g})
    (hS : ∃ j : Fin J, j ∉ sk.Cset i g ∧ (sk.src i).2 g (Sum.inl j) = p) :
    sk.entryCount i g p = 0 := by
  by_contra he
  obtain ⟨sl, hu, hy⟩ := (sk.entryCount_ne_zero_iff i g p).mp he
  obtain ⟨j, hj, hx⟩ := hS
  have h1 : (sk.tgt i).2 g sl = (sk.tgt i).2 g (Sum.inl j) :=
    hy.trans (hx.symm.trans (ctx.hyp.hSh j hj).symm)
  have h2 : sl = Sum.inl j := ctx.good.1 h1
  rw [h2] at hu
  exact hj hu

/-- A source label has no entry. -/
theorem Skel.EdgeCtx.active_entry (ctx : sk.EdgeCtx i g zf U) (sl : Slot J ℓ) :
    sk.entryCount i g ((sk.src i).2 g sl) = 0 := by
  by_contra he
  rcases ctx.entry_cases _ he with ⟨j, hj, -, -⟩ | hnU
  · exact ctx.hyp.hne sl j hj.symm
  · exact hnU (ctx.hyp.hxU sl)

theorem Skel.EdgeCtx.tgt_iff (ctx : sk.EdgeCtx i g zf U) (p : {p : ℕ // p ∈ 𝒢.big g}) :
    (∃ sl, (sk.tgt i).2 g sl = p) ↔
      (∃ j : Fin J, j ∉ sk.Cset i g ∧ (sk.src i).2 g (Sum.inl j) = p) ∨
        sk.entryCount i g p ≠ 0 :=
  sk.exists_tgt_iff_shared_or_entry i g p ctx.shared

/-- An old particle is kept iff its prime has no entry. -/
theorem Skel.EdgeCtx.kept_iff (ctx : sk.EdgeCtx i g zf U) (hnB : n ≤ Bc) (j : Fin n) :
    (¬∃ sl, edgPromo hnB (sk.Cset i g) ((sk.tgt i).2 g) zf sl = some (Fin.castLE hnB j)) ↔
      sk.entryCount i g (zf j).1 = 0 := by
  rw [edgPromo_exists_iff hnB _ _ zf ctx.hyp.hz j, ← sk.entryCount_ne_zero_iff i g (zf j).1]
  exact not_not

/-- The primes of the group born after the edge. -/
theorem Skel.EdgeCtx.mem_newU (ctx : sk.EdgeCtx i g zf U) (hnB : n ≤ Bc)
    (p : {p : ℕ // p ∈ 𝒢.big g}) :
    (p : ℕ) ∈ sk.edgeNewU i g hnB zf U ↔
      (p : ℕ) ∈ U ∨ (sk.entryCount i g p ≠ 0 ∧ ¬∃ j : Fin n, (zf j).1 = p) := by
  rw [Finset.mem_union, mem_edgeFreshSet]
  refine or_congr Iff.rfl ?_
  constructor
  · rintro ⟨sl, hf, hy⟩
    obtain ⟨hu, hno⟩ := (edgPromo_fresh_iff hnB _ _ zf ctx.hyp.hz sl).mp hf
    have hy' : (sk.tgt i).2 g sl = p := Subtype.ext hy
    rw [hy'] at hno
    exact ⟨(sk.entryCount_ne_zero_iff i g p).mpr ⟨sl, hu, hy'⟩, hno⟩
  · rintro ⟨he, hno⟩
    obtain ⟨sl, hu, hy⟩ := (sk.entryCount_ne_zero_iff i g p).mp he
    refine ⟨sl, (edgPromo_fresh_iff hnB _ _ zf ctx.hyp.hz sl).mpr ⟨hu, ?_⟩,
      congrArg Subtype.val hy⟩
    rw [hy]
    exact hno

/-! #### The term of the stores, by the condition of the prime after the edge -/

/-- No particle of the new memory has the prime `p`. -/
theorem Skel.EdgeCtx.tgt_none (ctx : sk.EdgeCtx i g zf U) (hn : n < Bc + 1) (hnB : n ≤ Bc)
    (b : Particle 𝒢 g → ℝ) (st : Finset (Slot J ℓ)) (p : {p : ℕ // p ∈ 𝒢.big g})
    (hk : ∀ j : Fin n, (zf j).1 = p → sk.entryCount i g p ≠ 0)
    (hs : ∀ sl ∈ st, (sk.src i).2 g sl ≠ p) :
    edgMid b (sk.edgeNewL i g hn hnB zf st) p = 1 ∧
      ¬∃ w ∈ sk.edgeNewL i g hn hnB zf st, w.1 = p := by
  refine edgMid_newList_none b hn hnB zf _ _ st _ p (fun j hj hp => ?_) hs
  have he : sk.entryCount i g p = 0 := by
    rw [← hp]
    exact (ctx.kept_iff hnB j).mp hj
  exact hk j hp he

/-- A prime which is active after the edge. -/
theorem Skel.EdgeCtx.lam_act (ctx : sk.EdgeCtx i g zf U) (hn : n < Bc + 1) (hnB : n ≤ Bc)
    (v : PrimeVals 𝒢) (st : Finset (Slot J ℓ)) (p : {p : ℕ // p ∈ 𝒢.big g})
    (hy : ∃ sl, (sk.tgt i).2 g sl = p)
    (hk : ∀ j : Fin n, (zf j).1 = p → sk.entryCount i g p ≠ 0)
    (hs : ∀ sl ∈ st, (sk.src i).2 g sl ≠ p) (hU : (p : ℕ) ∈ sk.edgeNewU i g hnB zf U) :
    sk.edgeLam i v g hn hnB zf U st p =
      edgMid (fun w => chnPow D.ρ (w.2 = 0)) (List.ofFn zf) p *
        (sk.edgeKappa i g zf p * v.act g p) := by
  have ht := ctx.tgt_none hn hnB (fun w => chnPow D.ρ (w.2 = 0) * v.pend g w) st p hk hs
  unfold Skel.edgeLam
  rw [edgPF_act _ _ _ _ _ _ _ _ hy ht.1 hU]

/-- A prime which was born and is not present after the edge. -/
theorem Skel.EdgeCtx.lam_dead (ctx : sk.EdgeCtx i g zf U) (hn : n < Bc + 1) (hnB : n ≤ Bc)
    (v : PrimeVals 𝒢) (st : Finset (Slot J ℓ)) (p : {p : ℕ // p ∈ 𝒢.big g})
    (hy : ¬∃ sl, (sk.tgt i).2 g sl = p)
    (hk : ∀ j : Fin n, (zf j).1 = p → sk.entryCount i g p ≠ 0)
    (hs : ∀ sl ∈ st, (sk.src i).2 g sl ≠ p) (hU : (p : ℕ) ∈ sk.edgeNewU i g hnB zf U) :
    sk.edgeLam i v g hn hnB zf U st p =
      edgMid (fun w => chnPow D.ρ (w.2 = 0)) (List.ofFn zf) p * v.dead g p := by
  have ht := ctx.tgt_none hn hnB (fun w => chnPow D.ρ (w.2 = 0) * v.pend g w) st p hk hs
  unfold Skel.edgeLam
  rw [edgPF_dead _ _ _ _ _ _ _ _ hy ht.1 ht.2 hU]

/-- A prime which is not born after the edge. -/
theorem Skel.EdgeCtx.lam_unborn (ctx : sk.EdgeCtx i g zf U) (hn : n < Bc + 1) (hnB : n ≤ Bc)
    (v : PrimeVals 𝒢) (st : Finset (Slot J ℓ)) (p : {p : ℕ // p ∈ 𝒢.big g})
    (hy : ¬∃ sl, (sk.tgt i).2 g sl = p)
    (hk : ∀ j : Fin n, (zf j).1 = p → sk.entryCount i g p ≠ 0)
    (hs : ∀ sl ∈ st, (sk.src i).2 g sl ≠ p) (hU : (p : ℕ) ∉ sk.edgeNewU i g hnB zf U) :
    sk.edgeLam i v g hn hnB zf U st p =
      edgMid (fun w => chnPow D.ρ (w.2 = 0)) (List.ofFn zf) p * v.unborn g p := by
  have ht := ctx.tgt_none hn hnB (fun w => chnPow D.ρ (w.2 = 0) * v.pend g w) st p hk hs
  unfold Skel.edgeLam
  rw [edgPF_unborn _ _ _ _ _ _ _ _ hy ht.1 hU]

/-- The prime of an old particle without entry: the particle is kept. -/
theorem Skel.EdgeCtx.lam_kept (ctx : sk.EdgeCtx i g zf U) (hn : n < Bc + 1) (hnB : n ≤ Bc)
    (v : PrimeVals 𝒢) (st : Finset (Slot J ℓ)) (j₀ : Fin n)
    (he : sk.entryCount i g (zf j₀).1 = 0) :
    sk.edgeLam i v g hn hnB zf U st (zf j₀).1 =
      chnPow D.ρ ((zf j₀).2 = 0) *
        (chnPow D.ρ ((shiftParticle (sk.step i) (zf j₀)).2 = 0) *
          v.pend g (shiftParticle (sk.step i) (zf j₀))) := by
  have hy : ¬∃ sl, (sk.tgt i).2 g sl = (zf j₀).1 := fun h =>
    ((ctx.tgt_iff _).mp h).elim (fun ⟨j, _, hx⟩ => ctx.hyp.hne _ j₀ hx) (fun h' => h' he)
  have hU : ((zf j₀).1 : ℕ) ∈ sk.edgeNewU i g hnB zf U :=
    (ctx.mem_newU hnB _).mpr (Or.inl (ctx.hyp.hzU j₀))
  have ht := edgMid_newList_kept (fun w => chnPow D.ρ (w.2 = 0) * v.pend g w) hn hnB zf
    ctx.hyp.hz (sk.step i) ((sk.src i).2 g) st
    (edgPromo hnB (sk.Cset i g) ((sk.tgt i).2 g) zf) j₀ ((ctx.kept_iff hnB j₀).mpr he)
    (fun sl _ => ctx.hyp.hne sl j₀)
  unfold Skel.edgeLam
  rw [edgPF_pend _ _ _ _ _ _ _ _ hy ht.2 hU, ht.1,
    edgMid_ofFn_single _ zf ctx.hyp.hz j₀]

/-- The label of a stored slot: the particle is appended. -/
theorem Skel.EdgeCtx.lam_stored (ctx : sk.EdgeCtx i g zf U) (hn : n < Bc + 1) (hnB : n ≤ Bc)
    (v : PrimeVals 𝒢) (st : Finset (Slot J ℓ)) (sl₀ : Slot J ℓ) (hsl₀ : sl₀ ∈ st)
    (hy : ¬∃ sl, (sk.tgt i).2 g sl = (sk.src i).2 g sl₀) :
    sk.edgeLam i v g hn hnB zf U st ((sk.src i).2 g sl₀) =
      chnPow D.ρ ((shiftParticle (sk.step i)
          (⟨(sk.src i).2 g sl₀, 0⟩ : Particle 𝒢 g)).2 = 0) *
        v.pend g (shiftParticle (sk.step i) ⟨(sk.src i).2 g sl₀, 0⟩) := by
  have hU : (((sk.src i).2 g sl₀ : {p : ℕ // p ∈ 𝒢.big g}) : ℕ) ∈ sk.edgeNewU i g hnB zf U :=
    (ctx.mem_newU hnB _).mpr (Or.inl (ctx.hyp.hxU sl₀))
  have ht := edgMid_newList_stored (fun w => chnPow D.ρ (w.2 = 0) * v.pend g w) hn hnB zf
    (sk.step i) ((sk.src i).2 g) ctx.hyp.hx st
    (edgPromo hnB (sk.Cset i g) ((sk.tgt i).2 g) zf) sl₀ hsl₀
    (fun j h => ctx.hyp.hne sl₀ j h.symm)
  unfold Skel.edgeLam
  rw [edgPF_pend _ _ _ _ _ _ _ _ hy ht.2 hU, ht.1,
    edgMid_ofFn_none _ zf _ (fun j h => ctx.hyp.hne sl₀ j h.symm), one_mul]

/-! #### The two factors agree outside the unshared source labels -/

/-- **A prime which is not the label of an unshared source slot has the same factor on both
sides**, for admissible stores. -/
theorem Skel.EdgeCtx.lam_eq_R (ctx : sk.EdgeCtx i g zf U) (hn : n < Bc + 1) (hnB : n ≤ Bc)
    (v : PrimeVals 𝒢) (st : Finset (Slot J ℓ))
    (hst : EdgeStoreG ((sk.src i).2 g) (sk.Cset i g) (sk.dilAt i) st)
    (p : {p : ℕ // p ∈ 𝒢.big g})
    (hp : ¬∃ sl, Unshared (sk.Cset i g) sl ∧ (sk.src i).2 g sl = p) :
    sk.edgeLam i v g hn hnB zf U st p = sk.edgeR i v g zf U p := by
  by_cases hact : ∃ sl, (sk.src i).2 g sl = p
  · -- a shared label stays active
    obtain ⟨sl, rfl⟩ := hact
    rcases edg_unshared_or (sk.Cset i g) sl with hu | ⟨j, hj, rfl⟩
    · exact absurd ⟨sl, hu, rfl⟩ hp
    · have hS : ∃ j' : Fin J, j' ∉ sk.Cset i g ∧
          (sk.src i).2 g (Sum.inl j') = (sk.src i).2 g (Sum.inl j) := ⟨j, hj, rfl⟩
      have he := ctx.shared_entry _ hS
      have hs : ∀ sl ∈ st, (sk.src i).2 g sl ≠ (sk.src i).2 g (Sum.inl j) := by
        intro sl hsl h
        have hsl' := (hst sl hsl).1
        rw [ctx.hyp.hx h] at hsl'
        exact hj hsl'
      rw [ctx.lam_act hn hnB v st _ ((ctx.tgt_iff _).mpr (Or.inl hS))
          (fun j' h => absurd h.symm (ctx.hyp.hne _ j')) hs
          ((ctx.mem_newU hnB _).mpr (Or.inl (ctx.hyp.hxU _))),
        edgMid_ofFn_none _ zf _ (fun j' h => ctx.hyp.hne _ j' h.symm),
        sk.edgeKappa_zero _ he, sk.edgeR_act v ctx.hyp,
        sk.edgeStepVals_act_shared i v g _ hS he, one_mul, one_mul]
  · by_cases hpend : ∃ j : Fin n, (zf j).1 = p
    · obtain ⟨j₀, rfl⟩ := hpend
      rw [sk.edgeR_pend v ctx.hyp j₀]
      by_cases he : sk.entryCount i g (zf j₀).1 = 0
      · -- a pending particle without entry stays pending
        rw [ctx.lam_kept hn hnB v st j₀ he]
        exact (sk.edgeStepVals_pend_zero i v g (zf j₀).1 (zf j₀).2 he).symm
      · -- a pending particle with an entry is promoted
        have he1 := ctx.entry_eq_one _ he
        have hprom : (shiftParticle (sk.step i) (zf j₀)).2 = 0 ∧
            ¬(((zf j₀).1 : ℕ) ∣ sk.dilAt i) := by
          rcases ctx.entry_cases _ he with ⟨j, hj, hsh, hdv⟩ | hnU
          · have hjj : j = j₀ := ctx.hyp.hz hj
            rw [hjj] at hsh hdv
            exact ⟨hsh, hdv⟩
          · exact absurd (ctx.hyp.hzU j₀) hnU
        rw [ctx.lam_act hn hnB v st _ ((ctx.tgt_iff _).mpr (Or.inr he)) (fun _ _ => he)
            (fun sl _ h => ctx.hyp.hne sl j₀ h)
            ((ctx.mem_newU hnB _).mpr (Or.inl (ctx.hyp.hzU j₀))),
          edgMid_ofFn_single _ zf ctx.hyp.hz j₀, sk.edgeKappa_pend _ he ⟨j₀, rfl⟩]
        exact (sk.edgeStepVals_pend_promo i v g (zf j₀).1 (zf j₀).2 he1 hprom.1 hprom.2).symm
    · have hz : ∀ j : Fin n, (zf j).1 ≠ p := fun j h => hpend ⟨j, h⟩
      have hs : ∀ sl ∈ st, (sk.src i).2 g sl ≠ p := fun sl _ h => hact ⟨sl, h⟩
      have hσ := edgMid_ofFn_none (fun w : Particle 𝒢 g => chnPow D.ρ (w.2 = 0)) zf p hz
      by_cases hU : (p : ℕ) ∈ U
      · -- a dead prime stays dead
        have he : sk.entryCount i g p = 0 := by
          by_contra he
          rcases ctx.entry_cases _ he with ⟨j, hj, -, -⟩ | hnU
          · exact hz j hj
          · exact hnU hU
        have hy : ¬∃ sl, (sk.tgt i).2 g sl = p := fun h =>
          ((ctx.tgt_iff _).mp h).elim (fun ⟨j, _, hx⟩ => hact ⟨Sum.inl j, hx⟩) (fun h' => h' he)
        rw [ctx.lam_dead hn hnB v st p hy (fun j h => absurd h (hz j)) hs
            ((ctx.mem_newU hnB _).mpr (Or.inl hU)), hσ, one_mul,
          sk.edgeR_dead v p hact hz hU, sk.edgeStepVals_dead_zero i v g p he]
      · rw [sk.edgeR_unborn v p hact hz hU]
        by_cases he : sk.entryCount i g p = 0
        · -- an unborn prime without entry stays unborn
          have hy : ¬∃ sl, (sk.tgt i).2 g sl = p := fun h =>
            ((ctx.tgt_iff _).mp h).elim (fun ⟨j, _, hx⟩ => hact ⟨Sum.inl j, hx⟩)
              (fun h' => h' he)
          have hU' : (p : ℕ) ∉ sk.edgeNewU i g hnB zf U := fun h =>
            ((ctx.mem_newU hnB p).mp h).elim hU (fun h' => h'.1 he)
          rw [ctx.lam_unborn hn hnB v st p hy (fun j h => absurd h (hz j)) hs hU', hσ, one_mul,
            sk.edgeStepVals_unborn_zero i v g p he]
        · -- an unborn prime with an entry is born in that slot
          have he1 := ctx.entry_eq_one _ he
          rw [ctx.lam_act hn hnB v st p ((ctx.tgt_iff _).mpr (Or.inr he)) (fun _ _ => he) hs
              ((ctx.mem_newU hnB _).mpr (Or.inr ⟨he, hpend⟩)), hσ, one_mul,
            sk.edgeKappa_fresh _ he hpend, sk.edgeStepVals_unborn_one i v g p he1]

/-! #### The labels of the unshared source slots -/

/-- **The label of an unshared source slot** is stored or dropped. -/
theorem Skel.EdgeCtx.lam_unshared (ctx : sk.EdgeCtx i g zf U) (hn : n < Bc + 1) (hnB : n ≤ Bc)
    (v : PrimeVals 𝒢) (st : Finset (Slot J ℓ)) (sl₀ : Slot J ℓ)
    (hu₀ : Unshared (sk.Cset i g) sl₀) :
    sk.edgeLam i v g hn hnB zf U st ((sk.src i).2 g sl₀) =
      if sl₀ ∈ st then
        chnPow D.ρ ((shiftParticle (sk.step i)
            (⟨(sk.src i).2 g sl₀, 0⟩ : Particle 𝒢 g)).2 = 0) *
          v.pend g (shiftParticle (sk.step i) ⟨(sk.src i).2 g sl₀, 0⟩)
      else v.dead g ((sk.src i).2 g sl₀) := by
  have hS : ¬∃ j : Fin J, j ∉ sk.Cset i g ∧
      (sk.src i).2 g (Sum.inl j) = (sk.src i).2 g sl₀ := by
    rintro ⟨j, hj, hx⟩
    have h := ctx.hyp.hx hx
    rw [← h] at hu₀
    exact hj hu₀
  have he := ctx.active_entry sl₀
  have hy : ¬∃ sl, (sk.tgt i).2 g sl = (sk.src i).2 g sl₀ := fun h =>
    ((ctx.tgt_iff _).mp h).elim hS (fun h' => h' he)
  by_cases hsl : sl₀ ∈ st
  · rw [if_pos hsl]
    exact ctx.lam_stored hn hnB v st sl₀ hsl hy
  · rw [if_neg hsl,
      ctx.lam_dead hn hnB v st _ hy (fun j h => absurd h.symm (ctx.hyp.hne sl₀ j))
        (fun sl hs h => hsl (by
          rw [← ctx.hyp.hx h]
          exact hs))
        ((ctx.mem_newU hnB _).mpr (Or.inl (ctx.hyp.hxU sl₀))),
      edgMid_ofFn_none _ zf _ (fun j h => ctx.hyp.hne sl₀ j h.symm), one_mul]

/-- **The right side for the label of an unshared source slot**: the sum of the two
alternatives, stored (if `p ∤ D`) and dropped. -/
theorem Skel.EdgeCtx.R_unshared (ctx : sk.EdgeCtx i g zf U) (v : PrimeVals 𝒢) (sl₀ : Slot J ℓ)
    (hu₀ : Unshared (sk.Cset i g) sl₀) :
    sk.edgeR i v g zf U ((sk.src i).2 g sl₀) =
      (if (((sk.src i).2 g sl₀ : {p : ℕ // p ∈ 𝒢.big g}) : ℕ) ∣ sk.dilAt i then 0
        else chnPow D.ρ ((shiftParticle (sk.step i)
            (⟨(sk.src i).2 g sl₀, 0⟩ : Particle 𝒢 g)).2 = 0) *
          v.pend g (shiftParticle (sk.step i) ⟨(sk.src i).2 g sl₀, 0⟩)) +
        v.dead g ((sk.src i).2 g sl₀) := by
  have hS : ¬∃ j : Fin J, j ∉ sk.Cset i g ∧
      (sk.src i).2 g (Sum.inl j) = (sk.src i).2 g sl₀ := by
    rintro ⟨j, hj, hx⟩
    have h := ctx.hyp.hx hx
    rw [← h] at hu₀
    exact hj hu₀
  have he := ctx.active_entry sl₀
  rw [sk.edgeR_act v ctx.hyp sl₀]
  by_cases hdv : (((sk.src i).2 g sl₀ : {p : ℕ // p ∈ 𝒢.big g}) : ℕ) ∣ sk.dilAt i
  · rw [if_pos hdv, zero_add, sk.edgeStepVals_act_drop i v g _ hS he hdv]
  · rw [if_neg hdv, sk.edgeStepVals_act_store i v g _ hS he hdv]

end Cases

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
