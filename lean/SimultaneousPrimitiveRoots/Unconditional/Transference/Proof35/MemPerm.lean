module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.MemorySpace
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Permutations of the particle indices of a memory

Source: `verification/stage7-sources/S-02.tex`, lines 418–420 (`[S-02:0418–0420]`): the functions
of `ℋ` are "invariant under permutations of the `j` particle indices, including when their
numerical values coincide".

Tools for `SymmetryPreserved.lean`: a function which is symmetric in the particle indices
(`MemSymmetric`) only depends on each memory through the list of its particles up to permutation.

* `exists_perm_ofFn` — if `l₁` is a permutation of `List.ofFn f`, then `l₁ = List.ofFn (f ∘ σ)` for
  a permutation `σ` of the indices.
* `mem_ext_ofFn`, `ofFn_memOfList`, `memOfList_perm` — a memory is determined by the list of its
  particles; the memory of a list.
* `MemSymmetric.congr_update`, `MemSymmetric.congr_mem` — a symmetric function takes the same
  value at two states which differ by permutations of the particle lists of their memories (in one
  group, in all groups).
* `filterMap_comp_perm` — relabelling the indices of `List.finRange n` by a permutation permutes a
  `filterMap`.
* `memZeroCount_congr` — the number of pending zeros only depends on the list of particles up to
  permutation.
* `extPerm`, `memAt_comp_extPerm` — a permutation of the first `k` indices, extended by the
  identity to all `Bc` indices; `memAt` of a memory with permuted indices.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

/-! ### Lists and tuples -/

section Lists

theorem ofFn_two {α : Type*} {m : ℕ} (h : Fin (m + 1 + 1) → α) :
    List.ofFn h = h 0 :: h (Fin.succ 0) :: List.ofFn (fun i : Fin m => h i.succ.succ) :=
  (List.ofFn_succ (f := h)).trans
    (congrArg (fun t => h 0 :: t) (List.ofFn_succ (f := fun i : Fin (m + 1) => h i.succ)))

/-- **A permutation of the list of a tuple is the list of the tuple with permuted indices**: if
`l₁` is a permutation of `List.ofFn f`, then `l₁ = List.ofFn (f ∘ σ)` for a permutation `σ` of the
indices. (The converse is `Equiv.Perm.ofFn_comp_perm`.) -/
theorem exists_perm_ofFn {α : Type*} {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    ∀ (n : ℕ) (f : Fin n → α), List.ofFn f = l₂ →
      ∃ σ : Equiv.Perm (Fin n), List.ofFn (f ∘ σ) = l₁ := by
  induction h with
  | nil =>
    intro n f hf
    exact ⟨Equiv.refl _, hf⟩
  | cons x _ ih =>
    intro n f hf
    cases n with
    | zero =>
      rw [List.ofFn_zero] at hf
      exact absurd hf.symm (List.cons_ne_nil _ _)
    | succ m =>
      have hf' : f 0 :: List.ofFn (fun i : Fin m => f i.succ) = _ :=
        (List.ofFn_succ (f := f)).symm.trans hf
      obtain ⟨h0, htail⟩ := List.cons.inj hf'
      obtain ⟨σ', hσ'⟩ := ih m (fun i => f i.succ) htail
      obtain ⟨τ, hτ⟩ : ∃ τ : Equiv.Perm (Fin (m + 1)),
          τ = Equiv.Perm.decomposeFin.symm ((0 : Fin (m + 1)), σ') := ⟨_, rfl⟩
      have hτ0 : τ 0 = 0 := by
        rw [hτ]
        exact Equiv.Perm.decomposeFin_symm_apply_zero _ _
      have hτs : ∀ i : Fin m, τ i.succ = (σ' i).succ := by
        intro i
        rw [hτ, Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.swap_self, Equiv.refl_apply]
      refine ⟨τ, ?_⟩
      have h1 : (f ∘ ⇑τ) 0 = x := by
        show f (τ 0) = x
        rw [hτ0]
        exact h0
      have h2 : (fun i : Fin m => (f ∘ ⇑τ) i.succ) = (fun i => f i.succ) ∘ ⇑σ' := by
        funext i
        show f (τ i.succ) = f (σ' i).succ
        rw [hτs]
      rw [List.ofFn_succ, h1, h2, hσ']
  | swap x y l =>
    intro n f hf
    have hlen : n = l.length + 1 + 1 := by
      have h' := congrArg List.length hf
      rw [List.length_ofFn, List.length_cons, List.length_cons] at h'
      exact h'
    subst hlen
    have hf' : f 0 :: f (Fin.succ 0) :: List.ofFn (fun i : Fin l.length => f i.succ.succ) =
        x :: y :: l := (ofFn_two f).symm.trans hf
    obtain ⟨hx, hrest⟩ := List.cons.inj hf'
    obtain ⟨hy, hl⟩ := List.cons.inj hrest
    refine ⟨Equiv.swap (0 : Fin (l.length + 1 + 1)) (Fin.succ 0), ?_⟩
    have h1 : (f ∘ ⇑(Equiv.swap (0 : Fin (l.length + 1 + 1)) (Fin.succ 0))) 0 = y := by
      show f (Equiv.swap (0 : Fin (l.length + 1 + 1)) (Fin.succ 0) 0) = y
      rw [Equiv.swap_apply_left]
      exact hy
    have h2 : (f ∘ ⇑(Equiv.swap (0 : Fin (l.length + 1 + 1)) (Fin.succ 0))) (Fin.succ 0) = x := by
      show f (Equiv.swap (0 : Fin (l.length + 1 + 1)) (Fin.succ 0) (Fin.succ 0)) = x
      rw [Equiv.swap_apply_right]
      exact hx
    have h3 : (fun i : Fin l.length =>
        (f ∘ ⇑(Equiv.swap (0 : Fin (l.length + 1 + 1)) (Fin.succ 0))) i.succ.succ) =
        fun i => f i.succ.succ := by
      funext i
      show f (Equiv.swap (0 : Fin (l.length + 1 + 1)) (Fin.succ 0) i.succ.succ) = f i.succ.succ
      rw [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _)
        (fun h => Fin.succ_ne_zero i (Fin.succ_injective _ h))]
    rw [ofFn_two, h1, h2, h3, hl]
  | trans _ _ ih₁ ih₂ =>
    intro n f hf
    obtain ⟨τ, hτ⟩ := ih₂ n f hf
    obtain ⟨σ, hσ⟩ := ih₁ n (f ∘ ⇑τ) hτ
    exact ⟨σ.trans τ, hσ⟩

/-- Relabelling the indices by a permutation permutes a `filterMap` over all indices. -/
theorem filterMap_comp_perm {n : ℕ} {β : Type*} (τ : Equiv.Perm (Fin n))
    (φ : Fin n → Option β) :
    ((List.finRange n).filterMap (fun j => φ (τ j))).Perm ((List.finRange n).filterMap φ) := by
  have h1 : (List.finRange n).filterMap (fun j => φ (τ j)) =
      ((List.finRange n).map ⇑τ).filterMap φ :=
    (List.filterMap_map (f := ⇑τ) (g := φ) (l := List.finRange n)).symm
  rw [h1]
  exact (Equiv.Perm.map_finRange_perm τ).filterMap φ

/-- A congruence for `if … then … else` whose two conditions are equivalent, for arbitrary
decidability instances of the two conditions. -/
theorem ite_congr_of_iff {α : Sort*} {P Q : Prop} {hP : Decidable P} {hQ : Decidable Q}
    {x y u v : α} (hc : P ↔ Q) (ht : x = u) (he : y = v) :
    @ite α P hP x y = @ite α Q hQ u v := by
  subst ht
  subst he
  by_cases h : P
  · exact (if_pos h).trans (if_pos (hc.mp h)).symm
  · exact (if_neg h).trans (if_neg (fun hq => h (hc.mpr hq))).symm

end Lists

/-! ### Memories and lists of particles -/

section Mem

variable {S B : Type} {𝒢 : GroupFamily S B} {Bc : ℕ} {g : B}

/-- A memory is determined by the list of its particles. -/
theorem mem_ext_ofFn (z₁ z₂ : Mem 𝒢 Bc g) (h : List.ofFn z₁.2 = List.ofFn z₂.2) : z₁ = z₂ := by
  obtain ⟨⟨k₁, hk₁⟩, f₁⟩ := z₁
  obtain ⟨⟨k₂, hk₂⟩, f₂⟩ := z₂
  have h' : List.ofFn f₁ = List.ofFn f₂ := h
  have hk : k₁ = k₂ := by
    have hl := congrArg List.length h'
    rw [List.length_ofFn, List.length_ofFn] at hl
    exact hl
  subst hk
  have hf : f₁ = f₂ := List.ofFn_injective h'
  subst hf
  rfl

/-- The particles of the memory of a list (of length at most the cutoff) are the list. -/
theorem ofFn_memOfList {l : List (Particle 𝒢 g)} (h : l.length ≤ Bc) :
    List.ofFn (memOfList (Bc := Bc) l).2 = l := by
  unfold memOfList
  rw [dif_pos h]
  exact List.ofFn_get l

theorem memOfList_of_not_le {l : List (Particle 𝒢 g)} (h : ¬l.length ≤ Bc) :
    memOfList (Bc := Bc) l = emptyMem 𝒢 Bc g := by
  unfold memOfList
  exact dif_neg h

/-- The memories of two lists which are permutations of each other have particle lists which are
permutations of each other. -/
theorem memOfList_perm {l₁ l₂ : List (Particle 𝒢 g)} (h : l₁.Perm l₂) :
    (List.ofFn (memOfList (Bc := Bc) l₁).2).Perm (List.ofFn (memOfList (Bc := Bc) l₂).2) := by
  by_cases h1 : l₁.length ≤ Bc
  · have h2 : l₂.length ≤ Bc := by
      rw [← h.length_eq]
      exact h1
    rw [ofFn_memOfList h1, ofFn_memOfList h2]
    exact h
  · have h2 : ¬l₂.length ≤ Bc := by
      rw [← h.length_eq]
      exact h1
    have e : memOfList (Bc := Bc) l₁ = memOfList (Bc := Bc) l₂ :=
      (memOfList_of_not_le h1).trans (memOfList_of_not_le h2).symm
    exact List.Perm.of_eq (congrArg (fun z : Mem 𝒢 Bc g => List.ofFn z.2) e)

/-- The number of zero residues of a tuple is invariant under permutations of its indices. -/
theorem ghostZeroCount_comp_perm {I P : Type*} {R : P → Type*} [Fintype I] [∀ p, Zero (R p)]
    (u : I → Σ p, R p) (σ : Equiv.Perm I) :
    Graph.ghostZeroCount (u ∘ σ) = Graph.ghostZeroCount u := by
  classical
  unfold Graph.ghostZeroCount
  exact Finset.card_equiv σ (fun i => by
    rw [Finset.mem_filter, Finset.mem_filter]
    exact and_congr (iff_of_true (Finset.mem_univ _) (Finset.mem_univ _)) Iff.rfl)

/-- The number of pending zeros is invariant under permutations of the particle indices. -/
theorem memZeroCount_comp_perm (k : Fin (Bc + 1)) (f : Fin k.val → Particle 𝒢 g)
    (σ : Equiv.Perm (Fin k.val)) :
    memZeroCount (⟨k, f ∘ σ⟩ : Mem 𝒢 Bc g) = memZeroCount (⟨k, f⟩ : Mem 𝒢 Bc g) :=
  ghostZeroCount_comp_perm f σ

/-- A memory whose particle list is a permutation of the particle list of `z₂` is `z₂` with
permuted particle indices. -/
theorem exists_perm_mem {z₁ z₂ : Mem 𝒢 Bc g} (hp : (List.ofFn z₁.2).Perm (List.ofFn z₂.2)) :
    ∃ σ : Equiv.Perm (Fin z₂.1.val), z₁ = ⟨z₂.1, z₂.2 ∘ σ⟩ := by
  obtain ⟨σ, hσ⟩ := exists_perm_ofFn hp z₂.1.val z₂.2 rfl
  exact ⟨σ, mem_ext_ofFn _ _ hσ.symm⟩

/-- The number of pending zeros only depends on the list of particles up to permutation. -/
theorem memZeroCount_congr {z₁ z₂ : Mem 𝒢 Bc g}
    (hp : (List.ofFn z₁.2).Perm (List.ofFn z₂.2)) : memZeroCount z₁ = memZeroCount z₂ := by
  obtain ⟨σ, hσ⟩ := exists_perm_mem hp
  rw [hσ]
  exact memZeroCount_comp_perm z₂.1 z₂.2 σ

/-- The first `k` of the `Bc` indices. -/
def finSubEquiv (k : Fin (Bc + 1)) : Fin k.val ≃ {j : Fin Bc // j.val < k.val} where
  toFun a := ⟨⟨a.val, Nat.lt_of_lt_of_le a.isLt (Nat.le_of_lt_succ k.isLt)⟩, a.isLt⟩
  invFun b := ⟨b.1.val, b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **A permutation of the first `k` indices, extended by the identity to all `Bc` indices.** -/
def extPerm (k : Fin (Bc + 1)) (σ : Equiv.Perm (Fin k.val)) : Equiv.Perm (Fin Bc) :=
  σ.extendDomain (finSubEquiv k)

/-- The particle with index `j` of a memory with permuted particle indices is the particle with
the permuted index. -/
theorem memAt_comp_extPerm (k : Fin (Bc + 1)) (f : Fin k.val → Particle 𝒢 g)
    (σ : Equiv.Perm (Fin k.val)) (j : Fin Bc) :
    memAt (⟨k, f ∘ σ⟩ : Mem 𝒢 Bc g) j = memAt (⟨k, f⟩ : Mem 𝒢 Bc g) (extPerm k σ j) := by
  by_cases hj : j.val < k.val
  · have hval : extPerm k σ j = (finSubEquiv k (σ ⟨j.val, hj⟩)).1 :=
      Equiv.Perm.extendDomain_apply_subtype σ (finSubEquiv k) hj
    have hlt : (extPerm k σ j).val < k.val := by
      rw [hval]
      exact (σ ⟨j.val, hj⟩).isLt
    have hv : (extPerm k σ j).val = (σ ⟨j.val, hj⟩).val :=
      congrArg (fun x : Fin Bc => x.val) hval
    have hidx : (⟨(extPerm k σ j).val, hlt⟩ : Fin k.val) = σ ⟨j.val, hj⟩ := Fin.ext hv
    show (if h : j.val < k.val then some (f (σ ⟨j.val, h⟩)) else none) =
      (if h : (extPerm k σ j).val < k.val then some (f ⟨(extPerm k σ j).val, h⟩) else none)
    rw [dif_pos hj, dif_pos hlt, hidx]
  · have hval : extPerm k σ j = j :=
      Equiv.Perm.extendDomain_apply_not_subtype σ (finSubEquiv k) hj
    rw [hval]
    show (if h : j.val < k.val then some (f (σ ⟨j.val, h⟩)) else none) =
      (if h : j.val < k.val then some (f ⟨j.val, h⟩) else none)
    rw [dif_neg hj, dif_neg hj]

end Mem

/-! ### Symmetric functions -/

section Symmetric

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ}

omit [Fintype B] [DecidableEq S] in
/-- A symmetric function is invariant under a permutation of the particle indices of the memory
of one group, the memory being given explicitly. -/
theorem MemSymmetric.update_perm {α : Type*} {F : MState 𝒢 J ℓ Bc → α} (hF : MemSymmetric F)
    (s : MState 𝒢 J ℓ Bc) (g : B) (z : Mem 𝒢 Bc g) (hz : s.mem g = z)
    (σ : Equiv.Perm (Fin z.1.val)) :
    F { s with mem := Function.update s.mem g ⟨z.1, z.2 ∘ σ⟩ } = F s := by
  subst hz
  exact hF s g σ

omit [Fintype B] [DecidableEq S] in
/-- **A symmetric function only depends on the memory of a group through the list of its
particles up to permutation.** -/
theorem MemSymmetric.congr_update {α : Type*} {F : MState 𝒢 J ℓ Bc → α} (hF : MemSymmetric F)
    (s : MState 𝒢 J ℓ Bc) (g : B) (z₁ z₂ : Mem 𝒢 Bc g)
    (hp : (List.ofFn z₁.2).Perm (List.ofFn z₂.2)) :
    F { s with mem := Function.update s.mem g z₁ } =
      F { s with mem := Function.update s.mem g z₂ } := by
  obtain ⟨σ, hσ⟩ := exists_perm_mem hp
  have h : F { s with mem := Function.update (Function.update s.mem g z₂) g ⟨z₂.1, z₂.2 ∘ σ⟩ } =
      F { s with mem := Function.update s.mem g z₂ } :=
    MemSymmetric.update_perm hF { s with mem := Function.update s.mem g z₂ } g z₂
      (Function.update_self g z₂ s.mem) σ
  rw [Function.update_idem] at h
  rw [hσ]
  exact h

omit [DecidableEq S] in
/-- **A symmetric function takes the same value at two states with the same residues and active
lists whose memories have, in every group, particle lists which are permutations of each
other.** -/
theorem MemSymmetric.congr_mem {α : Type*} {F : MState 𝒢 J ℓ Bc → α} (hF : MemSymmetric F)
    (y : ResVec (smallPrimes 𝒢)) (xs : LabelList 𝒢.small J ℓ) (xb : LabelList 𝒢.big J ℓ)
    (m₁ m₂ : (g : B) → Mem 𝒢 Bc g)
    (hp : ∀ g, (List.ofFn (m₁ g).2).Perm (List.ofFn (m₂ g).2)) :
    F ⟨y, xs, xb, m₁⟩ = F ⟨y, xs, xb, m₂⟩ := by
  -- replace the memories one group at a time
  have key : ∀ T : Finset B,
      F ⟨y, xs, xb, fun g => if g ∈ T then m₂ g else m₁ g⟩ = F ⟨y, xs, xb, m₁⟩ := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      have e : (fun g => if g ∈ (∅ : Finset B) then m₂ g else m₁ g) = m₁ :=
        funext fun g => if_neg (Finset.notMem_empty g)
      rw [e]
    | insert a T ha ih =>
      have e1 : (fun g => if g ∈ insert a T then m₂ g else m₁ g) =
          Function.update (fun g => if g ∈ T then m₂ g else m₁ g) a (m₂ a) := by
        funext g
        by_cases hga : g = a
        · subst hga
          rw [Function.update_self]
          exact if_pos (Finset.mem_insert_self _ _)
        · rw [Function.update_of_ne hga]
          by_cases hgT : g ∈ T
          · exact (if_pos (t := m₂ g) (e := m₁ g) (Finset.mem_insert_of_mem hgT)).trans
              (if_pos (t := m₂ g) (e := m₁ g) hgT).symm
          · have hgT' : g ∉ insert a T := fun h => (Finset.mem_insert.mp h).elim hga hgT
            exact (if_neg (t := m₂ g) (e := m₁ g) hgT').trans
              (if_neg (t := m₂ g) (e := m₁ g) hgT).symm
      have e2 : Function.update (fun g => if g ∈ T then m₂ g else m₁ g) a (m₁ a) =
          fun g => if g ∈ T then m₂ g else m₁ g := by
        have h0 : m₁ a = (fun g => if g ∈ T then m₂ g else m₁ g) a := (if_neg ha).symm
        rw [h0]
        exact Function.update_eq_self a _
      have h' : F ⟨y, xs, xb, Function.update (fun g => if g ∈ T then m₂ g else m₁ g) a (m₂ a)⟩ =
          F ⟨y, xs, xb, Function.update (fun g => if g ∈ T then m₂ g else m₁ g) a (m₁ a)⟩ :=
        MemSymmetric.congr_update hF ⟨y, xs, xb, fun g => if g ∈ T then m₂ g else m₁ g⟩ a
          (m₂ a) (m₁ a) (hp a).symm
      rw [e1, h', e2]
      exact ih
  have e : (fun g => if g ∈ (Finset.univ : Finset B) then m₂ g else m₁ g) = m₂ :=
    funext fun g => if_pos (Finset.mem_univ g)
  have h := key Finset.univ
  rw [e] at h
  exact h.symm

end Symmetric

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
