module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.EdgeSum
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.ListNorm

/-!
# Removal of the shared labels: the shared and the unshared labels of a list

`[P-06:0318–0339]`: "For a single pattern put `n = D_R w`, `n' = D_R w'`. … The factor `D_R⁻¹`
changes each shared sum into its probability law `μ_g`, and the remaining list factors and damping
are exactly `W_𝐭(w) W_𝐭(w')`."

For a pattern with freed slots `C_g ⊂ {1, …, J}` (`ℓ = 1`) a list of all groups is split into

* its *shared labels* `σ : ShT 𝔊 C`: one label for every first slot of a small group and for every
  first slot outside `C_g` of a big group `g` (the index type `ShIdx 𝔊 C` is flat, so that the
  shared labels are an independent family with the laws `μ_g`);
* its *unshared labels* `u : UnT 𝔊 C`: for every group `g` the labels in its `t_g` unshared slots,
  `t_g = markCount 𝔊 C g` — the last slot of a small group; the slots of `C_g`, numbered by
  `Fin |C_g|`, and then the last slot of a big group (`slotEquiv`). This is the type of the
  represented lists of `strippedSumOf` with values in the groups.

`listSplit 𝔊 C : Lists ≃ ShT × UnT` is the bijection. In these coordinates:

* `dil_mk`: the dilation is `D_R · D_C`, `D_R = shProd σ` the product of the shared labels;
* `listProd_mk`: the product of all the labels is `shProd σ · unProd u`;
* `shared_iff`: two lists have the same shared labels iff their first coordinates agree;
* `auxAvoids_mk_iff`: the ban on the free labels, for the shared and for the unshared labels;
* `isPhys_mk_iff`: the physical states.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference

noncomputable section

namespace Strip

/-! ### The slots of a big group -/

/-- **The slots of a big group with freed slots `c`**: the shared slots (the first `J` slots
outside `c`), and the `|c| + 1` unshared slots — the slots of `c`, numbered by `Fin |c|`, followed
by the last slot. -/
def slotEquiv {J : ℕ} (c : Finset (Fin J)) :
    {i : Fin J // i ∉ c} ⊕ Fin (c.card + 1) ≃ Slot J 1 where
  toFun := Sum.elim (fun i => Sum.inl i.1)
    (Fin.lastCases (Sum.inr 0) fun k => Sum.inl (c.equivFin.symm k).1)
  invFun := Sum.elim
    (fun i => if h : i ∈ c then Sum.inr (Fin.castSucc (c.equivFin ⟨i, h⟩)) else Sum.inl ⟨i, h⟩)
    (fun _ => Sum.inr (Fin.last c.card))
  left_inv := by
    rintro (i | j)
    · simp [i.2]
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp
      · simp
  right_inv := by
    rintro (i | j)
    · by_cases h : i ∈ c
      · simp [h]
      · simp [h]
    · have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      simp

theorem slotEquiv_inl {J : ℕ} (c : Finset (Fin J)) (i : {i : Fin J // i ∉ c}) :
    slotEquiv c (Sum.inl i) = Sum.inl i.1 := rfl

theorem slotEquiv_last {J : ℕ} (c : Finset (Fin J)) :
    slotEquiv c (Sum.inr (Fin.last c.card)) = Sum.inr 0 := by
  simp [slotEquiv]

theorem slotEquiv_castSucc {J : ℕ} (c : Finset (Fin J)) (k : Fin c.card) :
    slotEquiv c (Sum.inr (Fin.castSucc k)) = Sum.inl (c.equivFin.symm k).1 := by
  simp [slotEquiv]

/-! ### Shared and unshared labels -/

section Split

variable (𝔊 : ActiveGroups) {J : ℕ} (C : Fin 𝔊.numBig → Finset (Fin J))

/-- The shared slots of all groups: all the first `J` slots of the small groups, and the first
slots outside `C_g` of the big groups `g`. -/
abbrev ShIdx : Type :=
  (Fin 𝔊.numSmall × Fin J) ⊕ (Σ g : Fin 𝔊.numBig, {i : Fin J // i ∉ C g})

/-- The group of a shared slot. -/
def shGrp : ShIdx 𝔊 C → Finset ℕ :=
  Sum.elim (fun a => (groupFamily 𝔊).small a.1) (fun b => (groupFamily 𝔊).big b.1)

/-- The shared labels: one label of its group for every shared slot. -/
abbrev ShT : Type := (k : ShIdx 𝔊 C) → {p : ℕ // p ∈ shGrp 𝔊 C k}

/-- The unshared labels: `t_g` labels of the group `g` for every group. -/
abbrev UnT : Type :=
  (g : 𝔊.Index) → Fin (markCount 𝔊 C g) → {p : ℕ // p ∈ 𝔊.group g}

variable {𝔊 C}

/-- The values of the unshared labels: a list of the type of the represented lists. -/
def unVal (u : UnT 𝔊 C) : (g : 𝔊.Index) → Fin (markCount 𝔊 C g) → ℕ := fun g j => (u g j : ℕ)

/-- The product `D_R` of the shared labels. -/
def shProd (σ : ShT 𝔊 C) : ℕ := ∏ k, (σ k : ℕ)

/-- The product of the unshared labels. -/
def unProd (u : UnT 𝔊 C) : ℕ := ∏ g, ∏ j, (u g j : ℕ)

variable (𝔊 C)

/-- **A list of all groups is its shared labels and its unshared labels.** -/
def listSplit : Lists (groupFamily 𝔊) J 1 ≃ ShT 𝔊 C × UnT 𝔊 C where
  toFun s :=
    (fun k => match k with
      | Sum.inl a => s.1 a.1 (Sum.inl a.2)
      | Sum.inr b => s.2 b.1 (slotEquiv (C b.1) (Sum.inl b.2)),
     fun g => match g with
      | Sum.inl g => fun j => s.1 g (Sum.inr j)
      | Sum.inr g => fun j => s.2 g (slotEquiv (C g) (Sum.inr j)))
  invFun p :=
    (fun g => Sum.elim (fun i => p.1 (Sum.inl (g, i))) (p.2 (Sum.inl g)),
     fun g slot => Sum.elim (fun i => p.1 (Sum.inr ⟨g, i⟩)) (p.2 (Sum.inr g))
       ((slotEquiv (C g)).symm slot))
  left_inv s := by
    refine Prod.ext (funext fun g => funext fun slot => ?_)
      (funext fun g => funext fun slot => ?_)
    · rcases slot with i | j
      · rfl
      · rfl
    · have h := (slotEquiv (C g)).apply_symm_apply slot
      generalize (slotEquiv (C g)).symm slot = y at h
      subst h
      rcases y with i | j
      · exact congrArg (Sum.elim _ _) ((slotEquiv (C g)).symm_apply_apply (Sum.inl i))
      · exact congrArg (Sum.elim _ _) ((slotEquiv (C g)).symm_apply_apply (Sum.inr j))
  right_inv p := by
    refine Prod.ext (funext fun k => ?_) (funext fun g => ?_)
    · rcases k with a | b
      · rfl
      · exact congrArg (Sum.elim (fun i => p.1 (Sum.inr ⟨b.1, i⟩)) (p.2 (Sum.inr b.1)))
          ((slotEquiv (C b.1)).symm_apply_apply (Sum.inl b.2))
    · rcases g with g | g
      · rfl
      · exact funext fun j =>
          congrArg (Sum.elim (fun i => p.1 (Sum.inr ⟨g, i⟩)) (p.2 (Sum.inr g)))
            ((slotEquiv (C g)).symm_apply_apply (Sum.inr j))

variable {𝔊 C}

/-- The small lists of the list with shared labels `σ` and unshared labels `u`. -/
theorem mk_fst (σ : ShT 𝔊 C) (u : UnT 𝔊 C) (g : Fin 𝔊.numSmall) :
    ((listSplit 𝔊 C).symm (σ, u)).1 g =
      Sum.elim (fun i => σ (Sum.inl (g, i))) (u (Sum.inl g)) := rfl

/-- The big lists of the list with shared labels `σ` and unshared labels `u`, on the slots in
their shared/unshared order. -/
theorem mk_snd (σ : ShT 𝔊 C) (u : UnT 𝔊 C) (g : Fin 𝔊.numBig)
    (y : {i : Fin J // i ∉ C g} ⊕ Fin ((C g).card + 1)) :
    ((listSplit 𝔊 C).symm (σ, u)).2 g (slotEquiv (C g) y) =
      Sum.elim (fun i => σ (Sum.inr ⟨g, i⟩)) (u (Sum.inr g)) y := by
  change Sum.elim (fun i : {i : Fin J // i ∉ C g} => σ (Sum.inr ⟨g, i⟩)) (u (Sum.inr g))
    ((slotEquiv (C g)).symm (slotEquiv (C g) y)) = _
  rw [Equiv.symm_apply_apply]

/-- A shared label of a big group, at its slot. -/
theorem mk_snd_shared (σ : ShT 𝔊 C) (u : UnT 𝔊 C) (g : Fin 𝔊.numBig) {i : Fin J}
    (hi : i ∉ C g) :
    ((listSplit 𝔊 C).symm (σ, u)).2 g (Sum.inl i) = σ (Sum.inr ⟨g, ⟨i, hi⟩⟩) :=
  mk_snd σ u g (Sum.inl ⟨i, hi⟩)

/-! ### Products -/

theorem shProd_eq (σ : ShT 𝔊 C) :
    shProd σ = (∏ g : Fin 𝔊.numSmall, ∏ i : Fin J, (σ (Sum.inl (g, i)) : ℕ)) *
      ∏ g : Fin 𝔊.numBig, ∏ i : {i : Fin J // i ∉ C g}, (σ (Sum.inr ⟨g, i⟩) : ℕ) := by
  unfold shProd
  rw [Fintype.prod_sum_type]
  exact congrArg₂ (fun a b : ℕ => a * b)
    (Fintype.prod_prod_type' fun (g : Fin 𝔊.numSmall) (i : Fin J) => (σ (Sum.inl (g, i)) : ℕ))
    (Fintype.prod_sigma' fun (g : Fin 𝔊.numBig) (i : {i : Fin J // i ∉ C g}) =>
      (σ (Sum.inr ⟨g, i⟩) : ℕ))

/-- **The product of all the labels** is `D_R` times the product of the unshared labels. -/
theorem listProd_mk (σ : ShT 𝔊 C) (u : UnT 𝔊 C) :
    listProd ((listSplit 𝔊 C).symm (σ, u)) = shProd σ * unProd u := by
  have hS : ∀ g : Fin 𝔊.numSmall,
      ∏ i : Slot J 1, (((listSplit 𝔊 C).symm (σ, u)).1 g i : ℕ) =
        (∏ i : Fin J, (σ (Sum.inl (g, i)) : ℕ)) * ∏ j, (u (Sum.inl g) j : ℕ) := by
    intro g
    rw [Fintype.prod_sum_type]
    rfl
  have hB : ∀ g : Fin 𝔊.numBig,
      ∏ i : Slot J 1, (((listSplit 𝔊 C).symm (σ, u)).2 g i : ℕ) =
        (∏ i : {i : Fin J // i ∉ C g}, (σ (Sum.inr ⟨g, i⟩) : ℕ)) *
          ∏ j, (u (Sum.inr g) j : ℕ) := by
    intro g
    calc ∏ i : Slot J 1, (((listSplit 𝔊 C).symm (σ, u)).2 g i : ℕ)
        = ∏ y : {i : Fin J // i ∉ C g} ⊕ Fin ((C g).card + 1),
            (((listSplit 𝔊 C).symm (σ, u)).2 g (slotEquiv (C g) y) : ℕ) :=
          (Equiv.prod_comp (slotEquiv (C g))
            (fun slot => (((listSplit 𝔊 C).symm (σ, u)).2 g slot : ℕ))).symm
      _ = (∏ i : {i : Fin J // i ∉ C g},
            (((listSplit 𝔊 C).symm (σ, u)).2 g (slotEquiv (C g) (Sum.inl i)) : ℕ)) *
          ∏ j : Fin ((C g).card + 1),
            (((listSplit 𝔊 C).symm (σ, u)).2 g (slotEquiv (C g) (Sum.inr j)) : ℕ) :=
          Fintype.prod_sum_type _
      _ = (∏ i : {i : Fin J // i ∉ C g}, (σ (Sum.inr ⟨g, i⟩) : ℕ)) *
            ∏ j, (u (Sum.inr g) j : ℕ) :=
          congrArg₂ (fun a b : ℕ => a * b)
            (Finset.prod_congr rfl fun i _ =>
              congrArg Subtype.val (mk_snd σ u g (Sum.inl i)))
            (Finset.prod_congr rfl fun j _ =>
              congrArg Subtype.val (mk_snd σ u g (Sum.inr j)))
  have hU : unProd u = (∏ g : Fin 𝔊.numSmall, ∏ j, (u (Sum.inl g) j : ℕ)) *
      ∏ g : Fin 𝔊.numBig, ∏ j, (u (Sum.inr g) j : ℕ) := by
    unfold unProd
    exact Fintype.prod_sum_type _
  have e1 : ∏ g : Fin 𝔊.numSmall, ∏ i : Slot J 1,
        (((listSplit 𝔊 C).symm (σ, u)).1 g i : ℕ) =
      (∏ g : Fin 𝔊.numSmall, ∏ i : Fin J, (σ (Sum.inl (g, i)) : ℕ)) *
        ∏ g : Fin 𝔊.numSmall, ∏ j, (u (Sum.inl g) j : ℕ) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun g _ => hS g
  have e2 : ∏ g : Fin 𝔊.numBig, ∏ i : Slot J 1,
        (((listSplit 𝔊 C).symm (σ, u)).2 g i : ℕ) =
      (∏ g : Fin 𝔊.numBig, ∏ i : {i : Fin J // i ∉ C g}, (σ (Sum.inr ⟨g, i⟩) : ℕ)) *
        ∏ g : Fin 𝔊.numBig, ∏ j, (u (Sum.inr g) j : ℕ) := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun g _ => hB g
  rw [listProd_eq, e1, e2, shProd_eq, hU]
  ring

/-- **The dilation is `D = D_R D_C`** (`[P-06:0113–0118]`). -/
theorem dil_mk (σ : ShT 𝔊 C) (u : UnT 𝔊 C) (r : AuxList (groupFamily 𝔊).big C) :
    dil C ((listSplit 𝔊 C).symm (σ, u)) r = shProd σ * tupleProd C r := by
  have hS : smallDil ((listSplit 𝔊 C).symm (σ, u)).1 =
      ∏ g : Fin 𝔊.numSmall, ∏ i : Fin J, (σ (Sum.inl (g, i)) : ℕ) := rfl
  have hBg : ∀ g : Fin 𝔊.numBig,
      (∏ i : Fin J, if i ∈ C g then 1
        else (((listSplit 𝔊 C).symm (σ, u)).2 g (Sum.inl i) : ℕ)) =
      ∏ i : {i : Fin J // i ∉ C g}, (σ (Sum.inr ⟨g, i⟩) : ℕ) := by
    intro g
    have hpt : ∀ i : Fin J, (if i ∈ C g then 1
        else (((listSplit 𝔊 C).symm (σ, u)).2 g (Sum.inl i) : ℕ)) =
        if h : i ∈ C g then 1 else (σ (Sum.inr ⟨g, ⟨i, h⟩⟩) : ℕ) := by
      intro i
      split_ifs with h
      · rfl
      · exact congrArg Subtype.val (mk_snd_shared σ u g h)
    exact (Finset.prod_congr rfl fun i _ => hpt i).trans
      ((Fintype.prod_dite (fun (_ : Fin J) _ => (1 : ℕ))
        (fun (i : Fin J) (h : ¬i ∈ C g) => (σ (Sum.inr ⟨g, ⟨i, h⟩⟩) : ℕ))).trans
        ((congrArg (fun a : ℕ => a *
          ∏ i : {i : Fin J // i ∉ C g}, (σ (Sum.inr ⟨g, i⟩) : ℕ)) Finset.prod_const_one).trans
          (one_mul _)))
  have hB : bigDil C ((listSplit 𝔊 C).symm (σ, u)).2 r =
      (∏ g : Fin 𝔊.numBig, ∏ i : {i : Fin J // i ∉ C g}, (σ (Sum.inr ⟨g, i⟩) : ℕ)) *
        tupleProd C r := by
    unfold bigDil tupleProd
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun g _ => by rw [hBg g]
  unfold dil
  rw [hS, hB, shProd_eq, mul_assoc]

/-- **Two lists have the same shared labels** iff the shared coordinates agree. -/
theorem shared_iff (s s' : Lists (groupFamily 𝔊) J 1) :
    SharedSmall s.1 s'.1 ∧ SharedBig C s.2 s'.2 ↔
      (listSplit 𝔊 C s').1 = (listSplit 𝔊 C s).1 := by
  constructor
  · rintro ⟨h1, h2⟩
    funext k
    rcases k with a | b
    · exact h1 a.1 a.2
    · exact h2 b.1 b.2.1 b.2.2
  · intro h
    exact ⟨fun g i => congrFun h (Sum.inl (g, i)),
      fun g i hi => congrFun h (Sum.inr ⟨g, ⟨i, hi⟩⟩)⟩

/-- **The ban on the free labels** (`[P-06:0127–0128]`), for the shared and for the unshared
labels of a list. -/
theorem auxAvoids_mk_iff (σ : ShT 𝔊 C) (u : UnT 𝔊 C) (r : AuxList (groupFamily 𝔊).big C) :
    AuxAvoids C r ((listSplit 𝔊 C).symm (σ, u)) ↔
      (∀ (k : ShIdx 𝔊 C) (g : Fin 𝔊.numBig) (i : {i : Fin J // i ∈ C g}),
        (σ k : ℕ) ≠ (r g i : ℕ)) ∧
      ∀ (g' : 𝔊.Index) (j : Fin (markCount 𝔊 C g')) (g : Fin 𝔊.numBig)
        (i : {i : Fin J // i ∈ C g}), (u g' j : ℕ) ≠ (r g i : ℕ) := by
  constructor
  · intro h
    constructor
    · intro k g i
      rcases k with a | b
      · exact (h g i).1 a.1 (Sum.inl a.2)
      · intro heq
        exact (h g i).2 b.1 (Sum.inl b.2.1)
          ((congrArg Subtype.val (mk_snd_shared σ u b.1 b.2.2)).trans heq)
    · intro g' j g i
      rcases g' with g' | g'
      · exact (h g i).1 g' (Sum.inr j)
      · intro heq
        exact (h g i).2 g' (slotEquiv (C g') (Sum.inr j))
          ((congrArg Subtype.val (mk_snd σ u g' (Sum.inr j))).trans heq)
  · rintro ⟨h1, h2⟩ g i
    constructor
    · intro g' slot
      rcases slot with i' | j
      · exact h1 (Sum.inl (g', i')) g i
      · exact h2 (Sum.inl g') j g i
    · intro g' slot
      have hs := (slotEquiv (C g')).apply_symm_apply slot
      generalize (slotEquiv (C g')).symm slot = y at hs
      subst hs
      rcases y with i' | j
      · intro heq
        exact h1 (Sum.inr ⟨g', i'⟩) g i
          ((congrArg Subtype.val (mk_snd σ u g' (Sum.inl i'))).symm.trans heq)
      · intro heq
        exact h2 (Sum.inr g') j g i
          ((congrArg Subtype.val (mk_snd σ u g' (Sum.inr j))).symm.trans heq)

/-- **The physical states** in the coordinates (shared labels, unshared labels). -/
theorem isPhys_mk_iff (σ : ShT 𝔊 C) (u : UnT 𝔊 C) (n : ℤ) :
    IsPhys intPos n ((listSplit 𝔊 C).symm (σ, u)) ↔
      (∀ g : Fin 𝔊.numSmall, Function.Injective
        (Sum.elim (fun i : Fin J => σ (Sum.inl (g, i))) (u (Sum.inl g)))) ∧
      (∀ g : Fin 𝔊.numBig, Function.Injective
        (Sum.elim (fun i : {i : Fin J // i ∉ C g} => σ (Sum.inr ⟨g, i⟩)) (u (Sum.inr g)))) ∧
      (∀ k : ShIdx 𝔊 C, ((σ k : ℕ) : ℤ) ∣ n) ∧
      ∀ (g : 𝔊.Index) (j : Fin (markCount 𝔊 C g)), ((u g j : ℕ) : ℤ) ∣ n := by
  have hcomp : ∀ g : Fin 𝔊.numBig,
      ((listSplit 𝔊 C).symm (σ, u)).2 g ∘ slotEquiv (C g) =
        Sum.elim (fun i : {i : Fin J // i ∉ C g} => σ (Sum.inr ⟨g, i⟩)) (u (Sum.inr g)) :=
    fun g => funext fun y => mk_snd σ u g y
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, fun g => ?_, fun k => ?_, fun g j => ?_⟩
    · rw [← hcomp g]
      exact (Equiv.injective_comp (slotEquiv (C g)) _).mpr (h2 g)
    · rcases k with a | b
      · exact h3 a.1 (Sum.inl a.2)
      · have h := h4 b.1 (slotEquiv (C b.1) (Sum.inl b.2))
        rw [mk_snd] at h
        exact h
    · rcases g with g | g
      · exact h3 g (Sum.inr j)
      · have h := h4 g (slotEquiv (C g) (Sum.inr j))
        rw [mk_snd] at h
        exact h
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨h1, fun g => ?_, fun g slot => ?_, fun g slot => ?_⟩
    · have h := h2 g
      rw [← hcomp g] at h
      exact (Equiv.injective_comp (slotEquiv (C g)) _).mp h
    · rcases slot with i | j
      · exact h3 (Sum.inl (g, i))
      · exact h4 (Sum.inl g) j
    · have hs := (slotEquiv (C g)).apply_symm_apply slot
      generalize (slotEquiv (C g)).symm slot = y at hs
      subst hs
      rw [mk_snd]
      rcases y with i | j
      · exact h3 (Sum.inr ⟨g, i⟩)
      · exact h4 (Sum.inr g) j

end Split

end Strip

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
