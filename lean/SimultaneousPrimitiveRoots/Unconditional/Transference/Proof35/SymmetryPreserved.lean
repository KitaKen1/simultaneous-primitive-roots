module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.MemPerm
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Operators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The memory operators map symmetric functions to symmetric functions

Source: `verification/stage7-sources/S-02.tex`, lines 418–420, 456–514 and 1198–1214
(`[S-02:0418–0420, 0456–0514, 1198–1214]`).

The Hilbert space `ℋ` consists of the functions which are "invariant under permutations of the
`j` particle indices" (`MemSymmetric`). The operator bounds of `ℋ` (`OpBound … MemSymmetric`) can
only be composed along a product `G_0 ℰ_0 G_1 ⋯ ℰ_{N-1} G_N 𝟏_∅` if every factor maps `ℋ` to `ℋ`.
This file proves it for the visit and the edge operations with arbitrary multipliers on their
births: "the resulting operator acts on symmetric memories" [S-02:1209].

* `ghostOpWith_memSymmetric` — `G_i^φ F` is symmetric if `F` is.
* `edgeOpWith_memSymmetric` — `ℰ_i^ψ F` is symmetric if `F` is.

## The argument

Let the particle indices of the memory of one group of the source state `s` be permuted by `σ`.
Extend `σ` by the identity to a permutation `τ` of all `Bc` indices. Every local transition choice
refers to the particles of the source through their indices (the set `A` of terminated indices of a
visit operation; the promotion map of an edge operation), so re-indexing the choice by `τ`
(`ghostRelabel`, `edgeRelabel`) is a bijection of the choices which

* leaves the births, and hence the multiplier, unchanged (`edgeBirths_relabel`);
* leaves the coefficient unchanged (`ghostCoef_relabel`, `edgeCoef_relabel`): the conditions and
  the factors only depend on the particles through their indices, on the numbers of pending
  zeros, and on the sizes;
* changes the target state only by a permutation of the particle list of each new memory
  (`ghostNewMem_relabel`, `edgeNewList_relabel`): the surviving particles are listed in the order
  of their indices.

A symmetric `F` does not see the last change (`MemSymmetric.congr_mem`). The relation between the
two source memories is `MemRelabel`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {N : Type}

/-! ### Relabelled memories -/

/-- **The memories `m'` are the memories `m` with relabelled particle indices**: the particle with
index `j` of `m' g` is the particle with index `τ g j` of `m g`; the numbers of pending zeros and
the sizes agree. -/
structure MemRelabel (τ : B → Equiv.Perm (Fin Bc)) (m m' : (g : B) → Mem 𝒢 Bc g) : Prop where
  /-- the particle with index `j` of `m' g` is the particle with index `τ g j` of `m g` -/
  at_eq : ∀ g j, memAt (m' g) j = memAt (m g) (τ g j)
  /-- the numbers of pending zeros agree -/
  zero_eq : ∀ g, memZeroCount (m' g) = memZeroCount (m g)
  /-- the sizes agree -/
  size_eq : ∀ g, (m' g).1.val = (m g).1.val

omit [Fintype S] [Fintype B] [DecidableEq S] in
/-- A permutation of the particle indices of the memory of one group is a relabelling. -/
theorem memRelabel_permMem (m : (g : B) → Mem 𝒢 Bc g) (g₀ : B)
    (σ : Equiv.Perm (Fin (m g₀).1.val)) :
    MemRelabel (fun g => if g = g₀ then extPerm (m g₀).1 σ else Equiv.refl _) m
      (Function.update m g₀ ⟨(m g₀).1, (m g₀).2 ∘ σ⟩) := by
  refine ⟨?_, ?_, ?_⟩
  · refine (Function.forall_update_iff m (fun g z => ∀ j, memAt z j =
      memAt (m g) ((if g = g₀ then extPerm (m g₀).1 σ else Equiv.refl _) j))).mpr
      ⟨fun j => ?_, fun g hg j => ?_⟩
    · show memAt (⟨(m g₀).1, (m g₀).2 ∘ σ⟩ : Mem 𝒢 Bc g₀) j =
        memAt (m g₀) ((if g₀ = g₀ then extPerm (m g₀).1 σ else Equiv.refl _) j)
      rw [if_pos (rfl : g₀ = g₀)]
      exact memAt_comp_extPerm _ _ σ j
    · show memAt (m g) j =
        memAt (m g) ((if g = g₀ then extPerm (m g₀).1 σ else Equiv.refl _) j)
      rw [if_neg hg, Equiv.refl_apply]
  · exact (Function.forall_update_iff m
      (fun g z => memZeroCount z = memZeroCount (m g))).mpr
      ⟨memZeroCount_comp_perm _ _ σ, fun g _ => rfl⟩
  · exact (Function.forall_update_iff m (fun g z => z.1.val = (m g).1.val)).mpr
      ⟨rfl, fun g _ => rfl⟩

/-! ### The visit operation -/

section Ghost

variable {g : B} {z z' : Mem 𝒢 Bc g} {ρ : Equiv.Perm (Fin Bc)}

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem ghostValid_relabel (hat : ∀ j, memAt z' j = memAt z (ρ j)) (A : Finset (Fin Bc)) :
    GhostValid z' A ↔ GhostValid z (A.map ρ.toEmbedding) := by
  unfold GhostValid
  constructor
  · intro h j hj
    obtain ⟨i, hi, hij⟩ := Finset.mem_map.mp hj
    obtain ⟨pr, hpr, h0⟩ := h i hi
    refine ⟨pr, ?_, h0⟩
    rw [← hij]
    exact (hat i).symm.trans hpr
  · intro h i hi
    obtain ⟨pr, hpr, h0⟩ := h _ (Finset.mem_map_of_mem ρ.toEmbedding hi)
    exact ⟨pr, (hat i).trans hpr, h0⟩

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- The surviving particles of the relabelled memory are a permutation of the surviving
particles. -/
theorem ghostSurvivors_relabel (hat : ∀ j, memAt z' j = memAt z (ρ j)) (A : Finset (Fin Bc)) :
    (ghostSurvivors z' A).Perm (ghostSurvivors z (A.map ρ.toEmbedding)) := by
  have h : ghostSurvivors z' A = (List.finRange Bc).filterMap
      (fun j => (fun i => if i ∈ A.map ρ.toEmbedding then none else memAt z i) (ρ j)) := by
    unfold ghostSurvivors
    refine congrArg (fun φ => (List.finRange Bc).filterMap φ) (funext fun j => ?_)
    show (if j ∈ A then none else memAt z' j) =
      (if ρ j ∈ A.map ρ.toEmbedding then none else memAt z (ρ j))
    rw [hat j]
    exact ite_congr_of_iff (Finset.mem_map' ρ.toEmbedding).symm rfl rfl
  rw [h]
  exact filterMap_comp_perm ρ (fun i => if i ∈ A.map ρ.toEmbedding then none else memAt z i)

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem ghostNewSize_relabel (hat : ∀ j, memAt z' j = memAt z (ρ j))
    (c : Finset (Fin Bc) × Batch 𝒢 Bc g) :
    ghostNewSize z' c = ghostNewSize z (c.1.map ρ.toEmbedding, c.2) := by
  show (ghostSurvivors z' c.1).length + c.2.1.val =
    (ghostSurvivors z (c.1.map ρ.toEmbedding)).length + c.2.1.val
  rw [(ghostSurvivors_relabel hat c.1).length_eq]

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- The new memory of the relabelled memory has a permuted particle list. -/
theorem ghostNewMem_relabel (hat : ∀ j, memAt z' j = memAt z (ρ j))
    (c : Finset (Fin Bc) × Batch 𝒢 Bc g) :
    (List.ofFn (ghostNewMem z' c).2).Perm
      (List.ofFn (ghostNewMem z (c.1.map ρ.toEmbedding, c.2)).2) :=
  memOfList_perm ((ghostSurvivors_relabel hat c.1).append_right (batchParticles c.2))

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem ghostCoefG_relabel (q ρ₀ : ℝ) (n i : ℕ) (hat : ∀ j, memAt z' j = memAt z (ρ j))
    (hzero : memZeroCount z' = memZeroCount z) (c : Finset (Fin Bc) × Batch 𝒢 Bc g) :
    ghostCoefG 𝒢 q ρ₀ n i g z' c =
      ghostCoefG 𝒢 q ρ₀ n i g z (c.1.map ρ.toEmbedding, c.2) := by
  unfold ghostCoefG
  refine ite_congr_of_iff (ghostValid_relabel hat c.1) ?_ rfl
  show Graph.sourceGhostD (visitQ q n i) ρ₀ ^ c.1.card *
        Graph.sourceGhostA (visitQ q n i) ρ₀ ^ (memZeroCount z' - c.1.card) *
        (Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ q n i) ρ₀ ^
          c.2.1.val / (c.2.1.val.factorial : ℝ)) *
        ∏ j, tiltLaw (𝒢.big g) q n (c.2.2 j) =
      Graph.sourceGhostD (visitQ q n i) ρ₀ ^ (c.1.map ρ.toEmbedding).card *
        Graph.sourceGhostA (visitQ q n i) ρ₀ ^
          (memZeroCount z - (c.1.map ρ.toEmbedding).card) *
        (Graph.sourceGhostC (Graph.primeGroupReciprocalMass (𝒢.big g)) (visitQ q n i) ρ₀ ^
          c.2.1.val / (c.2.1.val.factorial : ℝ)) *
        ∏ j, tiltLaw (𝒢.big g) q n (c.2.2 j)
  rw [hzero, Finset.card_map]

end Ghost

/-- Relabelling of the terminated indices of a choice of the visit operation: a bijection of the
choices. -/
def ghostRelabel (τ : B → Equiv.Perm (Fin Bc)) : GhostChoice 𝒢 Bc ≃ GhostChoice 𝒢 Bc where
  toFun c := fun g => ((c g).1.map (τ g).toEmbedding, (c g).2)
  invFun c := fun g => ((c g).1.map (τ g).symm.toEmbedding, (c g).2)
  left_inv c := by
    funext g
    refine Prod.ext ?_ rfl
    show ((c g).1.map (τ g).toEmbedding).map (τ g).symm.toEmbedding = (c g).1
    ext j
    rw [Finset.mem_map_equiv, Finset.mem_map_equiv, Equiv.symm_symm, Equiv.symm_apply_apply]
  right_inv c := by
    funext g
    refine Prod.ext ?_ rfl
    show ((c g).1.map (τ g).symm.toEmbedding).map (τ g).toEmbedding = (c g).1
    ext j
    rw [Finset.mem_map_equiv, Finset.mem_map_equiv, Equiv.symm_symm, Equiv.apply_symm_apply]

section GhostOp

variable {τ : B → Equiv.Perm (Fin Bc)} {m m' : (g : B) → Mem 𝒢 Bc g}

omit [DecidableEq S] [DecidableEq B] in
/-- The coefficient of the visit operation at the relabelled state is the coefficient at the
relabelled choice. -/
theorem ghostCoef_relabel (D : MemData 𝒢 J ℓ N) (i : ℕ) (y : ResVec (smallPrimes 𝒢))
    (xs : LabelList 𝒢.small J ℓ) (xb : LabelList 𝒢.big J ℓ) (h : MemRelabel τ m m')
    (c : GhostChoice 𝒢 Bc) :
    ghostCoef D i (⟨y, xs, xb, m'⟩ : MState 𝒢 J ℓ Bc) c =
      ghostCoef D i (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) (ghostRelabel τ c) := by
  have h1 : memTotal (⟨y, xs, xb, m'⟩ : MState 𝒢 J ℓ Bc) =
      memTotal (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) := by
    unfold memTotal
    exact Finset.sum_congr rfl fun g _ => h.size_eq g
  have h2 : (∑ g, ghostNewSize (m' g) (c g)) =
      ∑ g, ghostNewSize (m g) (ghostRelabel τ c g) :=
    Finset.sum_congr rfl fun g _ => ghostNewSize_relabel (h.at_eq g) (c g)
  have h3 : (∏ g, ghostCoefG 𝒢 D.q D.ρ D.n i g (m' g) (c g)) =
      ∏ g, ghostCoefG 𝒢 D.q D.ρ D.n i g (m g) (ghostRelabel τ c g) :=
    Finset.prod_congr rfl fun g _ =>
      ghostCoefG_relabel D.q D.ρ D.n i (h.at_eq g) (h.zero_eq g) (c g)
  show (if memTotal (⟨y, xs, xb, m'⟩ : MState 𝒢 J ℓ Bc) ≤ Bc ∧
        (∑ g, ghostNewSize (m' g) (c g)) ≤ Bc then
        ∏ g, ghostCoefG 𝒢 D.q D.ρ D.n i g (m' g) (c g) else 0) =
      (if memTotal (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) ≤ Bc ∧
        (∑ g, ghostNewSize (m g) (ghostRelabel τ c g)) ≤ Bc then
        ∏ g, ghostCoefG 𝒢 D.q D.ρ D.n i g (m g) (ghostRelabel τ c g) else 0)
  rw [h1, h2, h3]

omit [DecidableEq S] in
/-- A symmetric function takes the same value at the target of the relabelled state and at the
target of the relabelled choice. -/
theorem ghostTgt_relabel {F : MState 𝒢 J ℓ Bc → ℂ} (hF : MemSymmetric F)
    (y : ResVec (smallPrimes 𝒢)) (xs : LabelList 𝒢.small J ℓ) (xb : LabelList 𝒢.big J ℓ)
    (h : MemRelabel τ m m') (c : GhostChoice 𝒢 Bc) :
    F (ghostTgt (⟨y, xs, xb, m'⟩ : MState 𝒢 J ℓ Bc) c) =
      F (ghostTgt (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) (ghostRelabel τ c)) :=
  MemSymmetric.congr_mem hF y xs xb (fun g => ghostNewMem (m' g) (c g))
    (fun g => ghostNewMem (m g) (ghostRelabel τ c g))
    (fun g => ghostNewMem_relabel (h.at_eq g) (c g))

omit [DecidableEq S] in
/-- The visit operation with a multiplier, applied to a symmetric function, takes the same value
at two states whose memories are relabellings of each other. -/
theorem ghostOpWith_relabel (D : MemData 𝒢 J ℓ N) (Bc : ℕ)
    (φ : ((g : B) → Batch 𝒢 Bc g) → ℂ) (i : ℕ) {F : MState 𝒢 J ℓ Bc → ℂ}
    (hF : MemSymmetric F) {τ : B → Equiv.Perm (Fin Bc)} (y : ResVec (smallPrimes 𝒢))
    (xs : LabelList 𝒢.small J ℓ) (xb : LabelList 𝒢.big J ℓ) {m m' : (g : B) → Mem 𝒢 Bc g}
    (h : MemRelabel τ m m') :
    ghostOpWith D Bc φ i F ⟨y, xs, xb, m'⟩ = ghostOpWith D Bc φ i F ⟨y, xs, xb, m⟩ := by
  simp only [ghostOpWith, rowOp_apply]
  refine Fintype.sum_equiv (ghostRelabel τ) _ _ fun c => ?_
  have hb : ghostBirths (ghostRelabel τ c) = ghostBirths c := rfl
  show φ (ghostBirths c) * ((ghostCoef D i (⟨y, xs, xb, m'⟩ : MState 𝒢 J ℓ Bc) c : ℝ) : ℂ) *
      F (ghostTgt (⟨y, xs, xb, m'⟩ : MState 𝒢 J ℓ Bc) c) =
    φ (ghostBirths (ghostRelabel τ c)) *
        ((ghostCoef D i (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) (ghostRelabel τ c) : ℝ) : ℂ) *
      F (ghostTgt (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) (ghostRelabel τ c))
  rw [hb, ghostCoef_relabel D i y xs xb h c, ghostTgt_relabel hF y xs xb h c]

end GhostOp

omit [DecidableEq S] in
/-- **The visit operation with a multiplier on its births maps symmetric functions to symmetric
functions** [S-02:1198–1214]: if `F` is invariant under the permutations of the particle indices
of every memory, so is `G_i^φ F`, for every multiplier `φ` (of any size) on the batches. Together
with `edgeOpWith_memSymmetric` this is what allows the operator bounds on `ℋ`
(`OpBound … MemSymmetric`) to be composed along the product `G_0 ℰ_0 ⋯ ℰ_{N-1} G_N 𝟏_∅`. -/
theorem ghostOpWith_memSymmetric (D : MemData 𝒢 J ℓ N) (Bc : ℕ)
    (φ : ((g : B) → Batch 𝒢 Bc g) → ℂ) (i : ℕ) {F : MState 𝒢 J ℓ Bc → ℂ}
    (hF : MemSymmetric F) : MemSymmetric (ghostOpWith D Bc φ i F) := by
  intro s g₀ σ
  exact ghostOpWith_relabel D Bc φ i hF s.y s.xs s.xb (memRelabel_permMem s.mem g₀ σ)

/-! ### The edge operation -/

section EdgeChoice

variable {𝔉 : N → Pattern 𝒢.big J ℓ}

/-- Relabelling of the promotions of a choice of the edge operation: the target slot which
received the pending particle with index `j` receives the pending particle with index `τ g j`. -/
def edgeRelabel (τ : B → Equiv.Perm (Fin Bc)) (c : EdgeChoice 𝒢 𝔉 Bc) : EdgeChoice 𝒢 𝔉 Bc :=
  { c with promo := fun g sl => (c.promo g sl).map (τ g) }

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem edgeRelabel_promo_iff (τ : B → Equiv.Perm (Fin Bc)) (c : EdgeChoice 𝒢 𝔉 Bc) (g : B)
    (sl : Slot J ℓ) (j : Fin Bc) :
    (edgeRelabel τ c).promo g sl = some (τ g j) ↔ c.promo g sl = some j := by
  show (c.promo g sl).map (τ g) = some (τ g j) ↔ c.promo g sl = some j
  rw [Option.map_eq_some_iff]
  constructor
  · rintro ⟨a, ha, hab⟩
    rw [ha, (τ g).injective hab]
  · intro h
    exact ⟨j, h, rfl⟩

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem edgeRelabel_symm_cancel (τ : B → Equiv.Perm (Fin Bc)) (c : EdgeChoice 𝒢 𝔉 Bc) :
    edgeRelabel (fun g => (τ g).symm) (edgeRelabel τ c) = c := by
  obtain ⟨ν, r, store, promo, xsT, xbT⟩ := c
  have h : (fun g sl => ((promo g sl).map (τ g)).map (τ g).symm) = promo := by
    funext g sl
    show ((promo g sl).map (τ g)).map (τ g).symm = promo g sl
    obtain ⟨x, hx⟩ : ∃ x, x = promo g sl := ⟨_, rfl⟩
    rw [← hx]
    cases x with
    | none => rfl
    | some j =>
      show some ((τ g).symm ((τ g) j)) = some j
      rw [Equiv.symm_apply_apply]
  show (⟨ν, r, store, fun g sl => ((promo g sl).map (τ g)).map (τ g).symm, xsT, xbT⟩ :
    EdgeChoice 𝒢 𝔉 Bc) = ⟨ν, r, store, promo, xsT, xbT⟩
  rw [h]

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem edgeRelabel_cancel_symm (τ : B → Equiv.Perm (Fin Bc)) (c : EdgeChoice 𝒢 𝔉 Bc) :
    edgeRelabel τ (edgeRelabel (fun g => (τ g).symm) c) = c := by
  obtain ⟨ν, r, store, promo, xsT, xbT⟩ := c
  have h : (fun g sl => ((promo g sl).map (τ g).symm).map (τ g)) = promo := by
    funext g sl
    show ((promo g sl).map (τ g).symm).map (τ g) = promo g sl
    obtain ⟨x, hx⟩ : ∃ x, x = promo g sl := ⟨_, rfl⟩
    rw [← hx]
    cases x with
    | none => rfl
    | some j =>
      show some ((τ g) ((τ g).symm j)) = some j
      rw [Equiv.apply_symm_apply]
  show (⟨ν, r, store, fun g sl => ((promo g sl).map (τ g).symm).map (τ g), xsT, xbT⟩ :
    EdgeChoice 𝒢 𝔉 Bc) = ⟨ν, r, store, promo, xsT, xbT⟩
  rw [h]

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem promoCount_relabel (τ : B → Equiv.Perm (Fin Bc)) (c : EdgeChoice 𝒢 𝔉 Bc) (g : B) :
    promoCount (edgeRelabel τ c) g = promoCount c g := by
  unfold promoCount
  congr 1
  ext sl
  rw [Finset.mem_filter, Finset.mem_filter]
  refine and_congr Iff.rfl ?_
  show (c.promo g sl).map (τ g) ≠ none ↔ c.promo g sl ≠ none
  exact not_congr Option.map_eq_none_iff

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem fresh_relabel (τ : B → Equiv.Perm (Fin Bc)) (c : EdgeChoice 𝒢 𝔉 Bc) (g : B)
    (sl : Slot J ℓ) : Fresh (edgeRelabel τ c) g sl ↔ Fresh c g sl := by
  unfold Fresh
  refine and_congr Iff.rfl ?_
  show (c.promo g sl).map (τ g) = none ↔ c.promo g sl = none
  exact Option.map_eq_none_iff

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- The relabelling does not change the births of a choice of the edge operation. -/
theorem edgeBirths_relabel (τ : B → Equiv.Perm (Fin Bc)) (c : EdgeChoice 𝒢 𝔉 Bc) :
    edgeBirths (edgeRelabel τ c) = edgeBirths c := by
  funext g sl
  unfold edgeBirths
  exact ite_congr_of_iff (fresh_relabel τ c g sl) rfl rfl

end EdgeChoice

section EdgeOp

variable [Fintype N] {τ : B → Equiv.Perm (Fin Bc)} {m m' : (g : B) → Mem 𝒢 Bc g}

/-- Relabelling of the promotions of a choice of the whole edge operation: a bijection of the
choices. -/
def edgeFullRelabel (D : MemData 𝒢 J ℓ N) (τ : B → Equiv.Perm (Fin Bc)) :
    EdgeFullChoice D Bc ≃ EdgeFullChoice D Bc where
  toFun ξ := (ξ.1, edgeRelabel τ ξ.2.1, ξ.2.2)
  invFun ξ := (ξ.1, edgeRelabel (fun g => (τ g).symm) ξ.2.1, ξ.2.2)
  left_inv ξ := by
    obtain ⟨π₁, c, π₂⟩ := ξ
    show (π₁, edgeRelabel (fun g => (τ g).symm) (edgeRelabel τ c), π₂) = (π₁, c, π₂)
    rw [edgeRelabel_symm_cancel]
  right_inv ξ := by
    obtain ⟨π₁, c, π₂⟩ := ξ
    show (π₁, edgeRelabel τ (edgeRelabel (fun g => (τ g).symm) c), π₂) = (π₁, c, π₂)
    rw [edgeRelabel_cancel_symm]

omit [Fintype N] [DecidableEq S] [DecidableEq B] in
/-- The new memory lists of the relabelled state are permutations of the new memory lists of the
relabelled choice. -/
theorem edgeNewList_relabel (D : MemData 𝒢 J ℓ N) (i : ℕ) (y : ResVec (smallPrimes 𝒢))
    (xs : LabelList 𝒢.small J ℓ) (xb : LabelList 𝒢.big J ℓ) (h : MemRelabel τ m m')
    (c : EdgeChoice 𝒢 D.fam Bc) (g : B) :
    (edgeNewList D i (⟨y, xs, xb, m'⟩ : MState 𝒢 J ℓ Bc) c g).Perm
      (edgeNewList D i (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) (edgeRelabel τ c) g) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin Bc → Option (Particle 𝒢 g), φ = fun j' =>
      if ∃ sl, (edgeRelabel τ c).promo g sl = some j' then none
      else (memAt (m g) j').map
        (shiftParticle (edgeStep D i (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) (edgeRelabel τ c))) :=
    ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L : List (Particle 𝒢 g), L =
      ((slotList J ℓ).filter fun sl => decide (sl ∈ c.store g)).map fun sl =>
        shiftParticle (edgeStep D i (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) (edgeRelabel τ c))
          ⟨xb g sl, 0⟩ := ⟨_, rfl⟩
  have e1 : edgeNewList D i (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) (edgeRelabel τ c) g =
      (List.finRange Bc).filterMap φ ++ L := by
    subst hφ
    subst hL
    rfl
  have e2 : edgeNewList D i (⟨y, xs, xb, m'⟩ : MState 𝒢 J ℓ Bc) c g =
      (List.finRange Bc).filterMap (fun j => φ (τ g j)) ++ L := by
    subst hφ
    subst hL
    unfold edgeNewList
    refine congrArg₂ (fun l₁ l₂ => l₁ ++ l₂)
      (congrArg (fun ψ => (List.finRange Bc).filterMap ψ) (funext fun j => ?_)) rfl
    show (if ∃ sl, c.promo g sl = some j then none
        else (memAt (m' g) j).map
          (shiftParticle (edgeStep D i (⟨y, xs, xb, m'⟩ : MState 𝒢 J ℓ Bc) c))) =
      (if ∃ sl, (edgeRelabel τ c).promo g sl = some (τ g j) then none
        else (memAt (m g) (τ g j)).map
          (shiftParticle (edgeStep D i (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) (edgeRelabel τ c))))
    rw [h.at_eq g j]
    exact ite_congr_of_iff
      (exists_congr fun sl => (edgeRelabel_promo_iff τ c g sl j).symm) rfl rfl
  rw [e1, e2]
  exact (filterMap_comp_perm (τ g) φ).append_right L

omit [Fintype N] [DecidableEq S] [DecidableEq B] in
theorem promoValid_relabel (D : MemData 𝒢 J ℓ N) (i : ℕ) (y : ResVec (smallPrimes 𝒢))
    (xs : LabelList 𝒢.small J ℓ) (xb : LabelList 𝒢.big J ℓ) (h : MemRelabel τ m m')
    (c : EdgeChoice 𝒢 D.fam Bc) :
    PromoValid D i (⟨y, xs, xb, m'⟩ : MState 𝒢 J ℓ Bc) c ↔
      PromoValid D i (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) (edgeRelabel τ c) := by
  constructor
  · intro hv g sl j' hj'
    have hj : c.promo g sl = some ((τ g).symm j') := by
      refine (edgeRelabel_promo_iff τ c g sl ((τ g).symm j')).mp ?_
      rw [Equiv.apply_symm_apply]
      exact hj'
    obtain ⟨hu, hinj, pr, hpr, h0, hdvd, hx⟩ := hv g sl ((τ g).symm j') hj
    have e := h.at_eq g ((τ g).symm j')
    rw [Equiv.apply_symm_apply] at e
    refine ⟨hu, fun sl' hsl' => hinj sl' ?_, pr, e.symm.trans hpr, h0, hdvd, hx⟩
    refine (edgeRelabel_promo_iff τ c g sl' ((τ g).symm j')).mp ?_
    rw [Equiv.apply_symm_apply]
    exact hsl'
  · intro hv g sl j hj
    have hj' : (edgeRelabel τ c).promo g sl = some (τ g j) :=
      (edgeRelabel_promo_iff τ c g sl j).mpr hj
    obtain ⟨hu, hinj, pr, hpr, h0, hdvd, hx⟩ := hv g sl (τ g j) hj'
    exact ⟨hu, fun sl' hsl' => hinj sl' ((edgeRelabel_promo_iff τ c g sl' j).mpr hsl'), pr,
      (h.at_eq g j).trans hpr, h0, hdvd, hx⟩

open _root_.Classical in
omit [Fintype N] [DecidableEq S] [DecidableEq B] in
/-- The coefficient of the row transition of the edge at the relabelled state is the coefficient
at the relabelled choice. -/
theorem edgeCoef_relabel (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) (y : ResVec (smallPrimes 𝒢))
    (xs : LabelList 𝒢.small J ℓ) (xb : LabelList 𝒢.big J ℓ) (h : MemRelabel τ m m')
    (c : EdgeChoice 𝒢 D.fam Bc) :
    edgeCoef D θ i (⟨y, xs, xb, m'⟩ : MState 𝒢 J ℓ Bc) c =
      edgeCoef D θ i (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) (edgeRelabel τ c) := by
  have hmt : memTotal (⟨y, xs, xb, m'⟩ : MState 𝒢 J ℓ Bc) =
      memTotal (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) := by
    unfold memTotal
    exact Finset.sum_congr rfl fun g _ => h.size_eq g
  have hlen : (∑ g, (edgeNewList D i (⟨y, xs, xb, m'⟩ : MState 𝒢 J ℓ Bc) c g).length) =
      ∑ g, (edgeNewList D i (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) (edgeRelabel τ c) g).length :=
    Finset.sum_congr rfl fun g _ => (edgeNewList_relabel D i y xs xb h c g).length_eq
  have hz1 : memZeros (⟨y, xs, xb, m'⟩ : MState 𝒢 J ℓ Bc) =
      memZeros (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) := by
    unfold memZeros
    exact Finset.sum_congr rfl fun g _ => h.zero_eq g
  have hz2 : memZeros (edgeTgt D i (⟨y, xs, xb, m'⟩ : MState 𝒢 J ℓ Bc) c) =
      memZeros (edgeTgt D i (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) (edgeRelabel τ c)) := by
    unfold memZeros
    exact Finset.sum_congr rfl fun g _ =>
      memZeroCount_congr (memOfList_perm (edgeNewList_relabel D i y xs xb h c g))
  unfold edgeCoef
  refine ite_congr_of_iff ?_ ?_ rfl
  · rw [hmt, hlen]
    exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
      (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
        (and_congr Iff.rfl (promoValid_relabel D i y xs xb h c)))))))))
  · rw [hz1, hz2]
    simp only [promoCount_relabel, fresh_relabel]
    rfl

omit [Fintype N] [DecidableEq S] in
/-- A symmetric function takes the same value at the target of the relabelled state and at the
target of the relabelled choice. -/
theorem edgeTgt_relabel {F : MState 𝒢 J ℓ Bc → ℂ} (hF : MemSymmetric F)
    (D : MemData 𝒢 J ℓ N) (i : ℕ) (y : ResVec (smallPrimes 𝒢)) (xs : LabelList 𝒢.small J ℓ)
    (xb : LabelList 𝒢.big J ℓ) (h : MemRelabel τ m m') (c : EdgeChoice 𝒢 D.fam Bc)
    (π₂ : ListPerms S B J ℓ) :
    F ((edgeTgt D i (⟨y, xs, xb, m'⟩ : MState 𝒢 J ℓ Bc) c).permLists π₂) =
      F ((edgeTgt D i (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) (edgeRelabel τ c)).permLists π₂) :=
  MemSymmetric.congr_mem hF
    ((resModel (smallPrimes 𝒢)).shift
      (edgeStep D i (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) (edgeRelabel τ c)) y)
    (permuteSlots π₂.1 c.xsT) (permuteSlots π₂.2 c.xbT)
    (fun g => memOfList (edgeNewList D i (⟨y, xs, xb, m'⟩ : MState 𝒢 J ℓ Bc) c g))
    (fun g => memOfList
      (edgeNewList D i (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) (edgeRelabel τ c) g))
    (fun g => memOfList_perm (edgeNewList_relabel D i y xs xb h c g))

/-- The edge operation with a multiplier, applied to a symmetric function, takes the same value
at two states whose memories are relabellings of each other. -/
theorem edgeOpWith_relabel (D : MemData 𝒢 J ℓ N) (Bc : ℕ)
    (ψ : ((g : B) → Slot J ℓ → Option ℕ) → ℂ) (θ : ℝ) (i : ℕ) {F : MState 𝒢 J ℓ Bc → ℂ}
    (hF : MemSymmetric F) {τ : B → Equiv.Perm (Fin Bc)} (y : ResVec (smallPrimes 𝒢))
    (xs : LabelList 𝒢.small J ℓ) (xb : LabelList 𝒢.big J ℓ) {m m' : (g : B) → Mem 𝒢 Bc g}
    (h : MemRelabel τ m m') :
    edgeOpWith D Bc ψ θ i F ⟨y, xs, xb, m'⟩ = edgeOpWith D Bc ψ θ i F ⟨y, xs, xb, m⟩ := by
  simp only [edgeOpWith, rowOp_apply]
  refine Fintype.sum_equiv (edgeFullRelabel D τ) _ _ fun ξ => ?_
  obtain ⟨π₁, c, π₂⟩ := ξ
  have hc : edgeFullCoef D ψ θ i (⟨y, xs, xb, m'⟩ : MState 𝒢 J ℓ Bc) (π₁, c, π₂) =
      edgeFullCoef D ψ θ i (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) (π₁, edgeRelabel τ c, π₂) := by
    show (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ *
          (ψ (edgeBirths c) * edgeCoef D θ i
            (⟨y, permuteSlots π₁.1 xs, permuteSlots π₁.2 xb, m'⟩ : MState 𝒢 J ℓ Bc) c) *
          (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ =
        (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ *
          (ψ (edgeBirths (edgeRelabel τ c)) * edgeCoef D θ i
            (⟨y, permuteSlots π₁.1 xs, permuteSlots π₁.2 xb, m⟩ : MState 𝒢 J ℓ Bc)
            (edgeRelabel τ c)) *
          (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹
    rw [edgeBirths_relabel,
      edgeCoef_relabel D θ i y (permuteSlots π₁.1 xs) (permuteSlots π₁.2 xb) h c]
  have ht : F (edgeFullTgt D i (⟨y, xs, xb, m'⟩ : MState 𝒢 J ℓ Bc) (π₁, c, π₂)) =
      F (edgeFullTgt D i (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) (π₁, edgeRelabel τ c, π₂)) :=
    edgeTgt_relabel hF D i y (permuteSlots π₁.1 xs) (permuteSlots π₁.2 xb) h c π₂
  show edgeFullCoef D ψ θ i (⟨y, xs, xb, m'⟩ : MState 𝒢 J ℓ Bc) (π₁, c, π₂) *
      F (edgeFullTgt D i (⟨y, xs, xb, m'⟩ : MState 𝒢 J ℓ Bc) (π₁, c, π₂)) =
    edgeFullCoef D ψ θ i (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) (π₁, edgeRelabel τ c, π₂) *
      F (edgeFullTgt D i (⟨y, xs, xb, m⟩ : MState 𝒢 J ℓ Bc) (π₁, edgeRelabel τ c, π₂))
  rw [hc, ht]

/-- **The edge operation with a multiplier on its fresh births maps symmetric functions to
symmetric functions** [S-02:1183–1196]: if `F` is invariant under the permutations of the particle
indices of every memory, so is `ℰ_i^ψ F`, for every multiplier `ψ` (of any size) on the fresh
births and every `θ`. In particular this holds for `ℰ_i = ℰ_i^1` (`edgeOp`). -/
theorem edgeOpWith_memSymmetric (D : MemData 𝒢 J ℓ N) (Bc : ℕ)
    (ψ : ((g : B) → Slot J ℓ → Option ℕ) → ℂ) (θ : ℝ) (i : ℕ) {F : MState 𝒢 J ℓ Bc → ℂ}
    (hF : MemSymmetric F) : MemSymmetric (edgeOpWith D Bc ψ θ i F) := by
  intro s g₀ σ
  exact edgeOpWith_relabel D Bc ψ θ i hF s.y s.xs s.xb (memRelabel_permMem s.mem g₀ σ)

end EdgeOp

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
