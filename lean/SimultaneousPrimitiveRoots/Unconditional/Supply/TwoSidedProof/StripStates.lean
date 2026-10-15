module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.StripWeights

/-!
# Removal of the shared labels: physical states, invariance and collisions

`[P-06:0318–0339]`, `[PUB-tex:0482–0485]`. For `n = D_R w`:

* `dvd_of_isPhys_mk`, `isPhys_mk_of`: when the shared labels are distinct and none of them divides
  `w`, the list with shared labels `σ` and unshared labels `u` is physical at `D_R w` exactly when
  `u` is a represented list at `w` (`IsRepr`); `sum_representedLists`: the represented lists of
  `strippedSumOf` are the values of these `u`.
* `auxAvoids_mk_of`: the ban on the free labels.
* `first_shProd_mul`, `core_shProd_mul`, `weight_shProd_mul`: "The endpoint cores are invariant
  under these labels", and "Their product `R` is coprime to `H` for large `x`, so (eq:B-shared)
  preserves the joint factor exactly".
* `Good σ A`: the shared labels are distinct and avoid the set `A`; `forbid r w`: the free labels
  and the active primes dividing `w (w + D_C)`. `sum_shWeight_badInd_le`: "the harmonic mass of a
  shared/shared coincidence, a shared/free coincidence, or a shared prime dividing `w w'`" is at
  most `(n² + n |A|) δ` when every label has probability at most `δ` (`n` shared slots).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference

noncomputable section

namespace Strip

section States

variable {𝔊 : ActiveGroups} {J : ℕ} {C : Fin 𝔊.numBig → Finset (Fin J)}
  {P : ActiveGroupConstants} {x : ℝ}

/-! ### The active groups as a group family -/

theorem gf_prime_small (h𝔊 : 𝔊.Admissible P x) :
    ∀ g, ∀ p ∈ (groupFamily 𝔊).small g, p.Prime := fun g p hp => h𝔊.prime (Sum.inl g) p hp

theorem gf_prime_big (h𝔊 : 𝔊.Admissible P x) :
    ∀ g, ∀ p ∈ (groupFamily 𝔊).big g, p.Prime := fun g p hp => h𝔊.prime (Sum.inr g) p hp

theorem gf_disj_small (h𝔊 : 𝔊.Admissible P x) :
    ∀ g g', g ≠ g' → Disjoint ((groupFamily 𝔊).small g) ((groupFamily 𝔊).small g') :=
  fun g g' hgg' => h𝔊.disjoint (Sum.inl g) (Sum.inl g') fun e => hgg' (Sum.inl.inj e)

theorem gf_disj_big (h𝔊 : 𝔊.Admissible P x) :
    ∀ g g', g ≠ g' → Disjoint ((groupFamily 𝔊).big g) ((groupFamily 𝔊).big g') :=
  fun g g' hgg' => h𝔊.disjoint (Sum.inr g) (Sum.inr g') fun e => hgg' (Sum.inr.inj e)

theorem gf_disj_small_big (h𝔊 : 𝔊.Admissible P x) :
    ∀ g g', Disjoint ((groupFamily 𝔊).small g) ((groupFamily 𝔊).big g') :=
  fun g g' => h𝔊.disjoint (Sum.inl g) (Sum.inr g') Sum.inl_ne_inr

/-! ### Physical states at `n = D_R w` -/

/-- **A represented list at `w`**, with values in the groups: in every group the `t_g` unshared
labels are distinct and divide `w`. -/
def IsRepr (u : UnT 𝔊 C) (w : ℕ) : Prop :=
  (∀ g, Function.Injective (u g)) ∧ ∀ g j, (u g j : ℕ) ∣ w

/-- At a physical state at `D_R w` the unshared labels are a represented list at `w`: the product
of all the labels divides `D_R w`. -/
theorem dvd_of_isPhys_mk (h𝔊 : 𝔊.Admissible P x) (σ : ShT 𝔊 C) (u : UnT 𝔊 C) {w : ℕ}
    (h : IsPhys intPos ((shProd σ * w : ℕ) : ℤ) ((listSplit 𝔊 C).symm (σ, u))) :
    IsRepr u w := by
  have hd : ((listProd ((listSplit 𝔊 C).symm (σ, u)) : ℕ) : ℤ) ∣ ((shProd σ * w : ℕ) : ℤ) :=
    listProd_dvd_of_isPhys h (gf_prime_small h𝔊) (gf_prime_big h𝔊) (gf_disj_small h𝔊)
      (gf_disj_big h𝔊) (gf_disj_small_big h𝔊)
  rw [listProd_mk] at hd
  have hd' : unProd u ∣ w :=
    Nat.dvd_of_mul_dvd_mul_left (shProd_pos h𝔊 σ) (Int.natCast_dvd_natCast.mp hd)
  obtain ⟨h1, h2, -, -⟩ := (isPhys_mk_iff σ u _).mp h
  refine ⟨fun g => ?_, fun g j => ?_⟩
  · rcases g with g | g
    · intro a b hab
      exact Sum.inr.inj (h1 g (show Sum.elim (fun i : Fin J => σ (Sum.inl (g, i)))
        (u (Sum.inl g)) (Sum.inr a) = Sum.elim (fun i : Fin J => σ (Sum.inl (g, i)))
        (u (Sum.inl g)) (Sum.inr b) from hab))
    · intro a b hab
      exact Sum.inr.inj (h2 g (show Sum.elim
        (fun i : {i : Fin J // i ∉ C g} => σ (Sum.inr ⟨g, i⟩)) (u (Sum.inr g)) (Sum.inr a) =
        Sum.elim (fun i : {i : Fin J // i ∉ C g} => σ (Sum.inr ⟨g, i⟩)) (u (Sum.inr g))
          (Sum.inr b) from hab))
  · refine Dvd.dvd.trans ?_ hd'
    unfold unProd
    exact (Finset.dvd_prod_of_mem (fun j' => (u g j' : ℕ)) (Finset.mem_univ j)).trans
      (Finset.dvd_prod_of_mem (fun g' => ∏ j', (u g' j' : ℕ)) (Finset.mem_univ g))

/-- **Away from collisions, a represented list at `w` gives a physical state at `D_R w`.** -/
theorem isPhys_mk_of (σ : ShT 𝔊 C) (hinj : Function.Injective fun k => (σ k : ℕ)) {w : ℕ}
    (hw : ∀ k, ¬(σ k : ℕ) ∣ w) (u : UnT 𝔊 C) (hu : IsRepr u w) :
    IsPhys intPos ((shProd σ * w : ℕ) : ℤ) ((listSplit 𝔊 C).symm (σ, u)) := by
  refine (isPhys_mk_iff σ u _).mpr ⟨fun g => ?_, fun g => ?_, fun k => ?_, fun g j => ?_⟩
  · refine Function.Injective.sumElim (fun i i' h => ?_) (hu.1 (Sum.inl g)) (fun i j h => ?_)
    · have e : (σ (Sum.inl (g, i)) : ℕ) = (σ (Sum.inl (g, i')) : ℕ) := congrArg Subtype.val h
      exact (Prod.mk.inj (Sum.inl.inj (@hinj (Sum.inl (g, i)) (Sum.inl (g, i')) e))).2
    · have e : (σ (Sum.inl (g, i)) : ℕ) = (u (Sum.inl g) j : ℕ) := congrArg Subtype.val h
      exact hw (Sum.inl (g, i)) (by rw [e]; exact hu.2 (Sum.inl g) j)
  · refine Function.Injective.sumElim (fun i i' h => ?_) (hu.1 (Sum.inr g)) (fun i j h => ?_)
    · have e : (σ (Sum.inr ⟨g, i⟩) : ℕ) = (σ (Sum.inr ⟨g, i'⟩) : ℕ) := congrArg Subtype.val h
      exact eq_of_heq (Sigma.mk.inj_iff.mp
        (Sum.inr.inj (@hinj (Sum.inr ⟨g, i⟩) (Sum.inr ⟨g, i'⟩) e))).2
    · have e : (σ (Sum.inr ⟨g, i⟩) : ℕ) = (u (Sum.inr g) j : ℕ) := congrArg Subtype.val h
      exact hw (Sum.inr ⟨g, i⟩) (by rw [e]; exact hu.2 (Sum.inr g) j)
  · exact Int.natCast_dvd_natCast.mpr (Dvd.dvd.mul_right
      (Finset.dvd_prod_of_mem (fun k => (σ k : ℕ)) (Finset.mem_univ k)) w)
  · exact Int.natCast_dvd_natCast.mpr (Dvd.dvd.mul_left (hu.2 g j) _)

/-- The ban on the free labels holds when no shared label is a free label and the unshared labels
divide a number which no free label divides. -/
theorem auxAvoids_mk_of (σ : ShT 𝔊 C) (u : UnT 𝔊 C) (r : AuxList (groupFamily 𝔊).big C)
    (h1 : ∀ (k : ShIdx 𝔊 C) (g : Fin 𝔊.numBig) (i : {i : Fin J // i ∈ C g}),
      (σ k : ℕ) ≠ (r g i : ℕ)) {m : ℕ} (hu : ∀ g j, (u g j : ℕ) ∣ m)
    (hr : ∀ (g : Fin 𝔊.numBig) (i : {i : Fin J // i ∈ C g}), ¬(r g i : ℕ) ∣ m) :
    AuxAvoids C r ((listSplit 𝔊 C).symm (σ, u)) :=
  (auxAvoids_mk_iff σ u r).mpr ⟨h1, fun g' j g i heq => hr g i (by rw [← heq]; exact hu g' j)⟩

/-- A divisor of `D` and of `w + D` divides `w`. -/
theorem dvd_of_dvd_add {p w D : ℕ} (h : p ∣ w + D) (hD : p ∣ D) : p ∣ w := by
  have h1 : ((p : ℕ) : ℤ) ∣ ((w + D : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h
  have h2 : ((p : ℕ) : ℤ) ∣ ((D : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hD
  have h3 := dvd_sub h1 h2
  rw [Nat.cast_add, add_sub_cancel_right] at h3
  exact Int.natCast_dvd_natCast.mp h3

open _root_.Classical in
/-- **The represented lists of `strippedSumOf` are the values of the represented lists with
values in the groups.** -/
theorem sum_representedLists {M : Type*} [AddCommMonoid M] (w : ℕ)
    (φ : ((g : 𝔊.Index) → Fin (markCount 𝔊 C g) → ℕ) → M) :
    ∑ 𝔭 ∈ 𝔊.representedLists (markCount 𝔊 C) w, φ 𝔭 =
      ∑ u : UnT 𝔊 C, if IsRepr u w then φ (unVal u) else 0 := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun u _ => unVal u) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro u hu
    have hu' : IsRepr u w := (Finset.mem_filter.mp hu).2
    unfold ActiveGroups.representedLists
    refine Fintype.mem_piFinset.mpr fun g => Finset.mem_filter.mpr ⟨?_, ?_⟩
    · exact Fintype.mem_piFinset.mpr fun j =>
        Finset.mem_filter.mpr ⟨(u g j).2, hu'.2 g j⟩
    · exact Subtype.val_injective.comp (hu'.1 g)
  · intro u _ u' _ h
    funext g j
    exact Subtype.ext (congrFun (congrFun h g) j)
  · intro 𝔭 h𝔭
    unfold ActiveGroups.representedLists at h𝔭
    have h1 : ∀ g, (∀ j, 𝔭 g j ∈ (𝔊.group g).filter fun p => p ∣ w) ∧
        Function.Injective (𝔭 g) := fun g => by
      have hg := Finset.mem_filter.mp (Fintype.mem_piFinset.mp h𝔭 g)
      exact ⟨Fintype.mem_piFinset.mp hg.1, hg.2⟩
    refine ⟨fun g j => ⟨𝔭 g j, (Finset.mem_filter.mp ((h1 g).1 j)).1⟩, ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun g => ?_, fun g j => ?_⟩
    · intro a b hab
      exact (h1 g).2 (congrArg Subtype.val hab)
    · exact (Finset.mem_filter.mp ((h1 g).1 j)).2

/-! ### Invariance under the shared labels -/

/-- `(m v)_* = v_*` if every prime factor of `m` is in `A`. -/
theorem freePart_mul_eq {A : Finset ℕ} {m v : ℕ} (hm0 : m ≠ 0) (hv : v ≠ 0)
    (hm : ∀ p : ℕ, p.Prime → p ∣ m → p ∈ A) : freePart A (m * v) = freePart A v := by
  refine Nat.eq_of_factorization_eq (freePart_pos A _).ne' (freePart_pos A _).ne' fun p => ?_
  rw [freePart_factorization, freePart_factorization, Finsupp.filter_apply,
    Finsupp.filter_apply]
  by_cases hp : p ∈ A
  · rw [if_neg (not_not.mpr hp), if_neg (not_not.mpr hp)]
  · have h0 : m.factorization p = 0 := by
      rw [Nat.factorization_eq_zero_iff]
      by_cases hpp : p.Prime
      · exact Or.inr (Or.inl fun hd => hp (hm p hpp hd))
      · exact Or.inl hpp
    rw [if_pos hp, if_pos hp, Nat.factorization_mul hm0 hv, Finsupp.add_apply, h0,
      zero_add]

/-- Every prime factor of `D_R` is an active prime. -/
theorem prime_dvd_shProd (h𝔊 : 𝔊.Admissible P x) (σ : ShT 𝔊 C) {p : ℕ} (hp : p.Prime)
    (hd : p ∣ shProd σ) : p ∈ 𝔊.allPrimes := by
  unfold shProd at hd
  obtain ⟨k, -, hk⟩ := (Prime.dvd_finsetProd_iff hp.prime _).mp hd
  rw [(Nat.prime_dvd_prime_iff_eq hp (shLabel_prime h𝔊 σ k)).mp hk]
  exact shLabel_mem_allPrimes σ k

/-- "The endpoint cores are invariant under these labels": the first endpoint. -/
theorem first_shProd_mul {F : ℕ → ℝ} (hF : ∀ p ∈ 𝔊.allPrimes, ∀ n : ℕ, F (p * n) = F n)
    (σ : ShT 𝔊 C) (v : ℕ) : F (shProd σ * v) = F v := by
  have key : ∀ s : Finset (ShIdx 𝔊 C), F ((∏ k ∈ s, (σ k : ℕ)) * v) = F v := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.prod_empty, one_mul]
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, mul_assoc, hF _ (shLabel_mem_allPrimes σ a), ih]
  exact key Finset.univ

/-- "The endpoint cores are invariant under these labels": the second endpoint. -/
theorem core_shProd_mul (h𝔊 : 𝔊.Admissible P x) {x₁ Cg : ℝ} {G : ℕ → ℂ}
    (hG : CoreAdmissible 𝔊 x₁ Cg G) (σ : ShT 𝔊 C) {v : ℕ} (hv : 0 < v) :
    G (shProd σ * v) = G v := by
  rw [hG.invariant _ (Nat.mul_pos (shProd_pos h𝔊 σ) hv), hG.invariant v hv,
    freePart_mul_eq (shProd_pos h𝔊 σ).ne' hv.ne' fun p hp hd => prime_dvd_shProd h𝔊 σ hp hd]

/-- (eq:B-shared): "Their product `R` is coprime to `H` for large `x`, so (eq:B-shared) preserves
the joint factor exactly." -/
theorem weight_shProd_mul (h𝔊 : 𝔊.Admissible P x) {H : ℕ} (hH0 : 0 < H)
    (hH : ∀ p ∈ 𝔊.allPrimes, H < p) (𝔅 : JointResidueWeight H) (σ : ShT 𝔊 C) (a b : ℕ) :
    𝔅.toFun ((shProd σ * a : ℕ) : ZMod H) ((shProd σ * b : ℕ) : ZMod H) =
      𝔅.toFun (a : ZMod H) (b : ZMod H) := by
  have hcop : (shProd σ).Coprime H := by
    unfold shProd
    refine Nat.Coprime.prod_left fun k _ => ?_
    exact (Nat.Prime.coprime_iff_not_dvd (shLabel_prime h𝔊 σ k)).mpr
      (Nat.not_dvd_of_pos_of_lt hH0 (hH _ (shLabel_mem_allPrimes σ k)))
  have h := 𝔅.unit_mul (ZMod.unitOfCoprime (shProd σ) hcop) (a : ZMod H) (b : ZMod H)
  rw [ZMod.coe_unitOfCoprime] at h
  rw [Nat.cast_mul, Nat.cast_mul]
  exact h

/-! ### Collisions -/

/-- **No collision**: the shared labels are distinct and none of them lies in `A`. -/
def Good (σ : ShT 𝔊 C) (A : Finset ℕ) : Prop :=
  (Function.Injective fun k => (σ k : ℕ)) ∧ ∀ k, (σ k : ℕ) ∉ A

/-- The primes that a shared label must avoid at `(r, w)`: the free labels, and the active primes
dividing `w` or `w + D_C` (`[P-06:0340–0343]`). -/
def forbid (r : AuxList (groupFamily 𝔊).big C) (w : ℕ) : Finset ℕ :=
  (Finset.univ.image fun gi : (Σ g : Fin 𝔊.numBig, {i : Fin J // i ∈ C g}) =>
      (r gi.1 gi.2 : ℕ)) ∪
    ((𝔊.allPrimes.filter fun p => p ∣ w) ∪
      𝔊.allPrimes.filter fun p => p ∣ w + tupleProd C r)

theorem Good.ne_aux {σ : ShT 𝔊 C} {r : AuxList (groupFamily 𝔊).big C} {w : ℕ}
    (h : Good σ (forbid r w)) (k : ShIdx 𝔊 C) (g : Fin 𝔊.numBig)
    (i : {i : Fin J // i ∈ C g}) : (σ k : ℕ) ≠ (r g i : ℕ) := by
  intro heq
  refine h.2 k (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨⟨g, i⟩, Finset.mem_univ _, ?_⟩))
  exact heq.symm

theorem Good.not_dvd {σ : ShT 𝔊 C} {r : AuxList (groupFamily 𝔊).big C} {w : ℕ}
    (h : Good σ (forbid r w)) (k : ShIdx 𝔊 C) : ¬(σ k : ℕ) ∣ w := fun hd =>
  h.2 k (Finset.mem_union_right _ (Finset.mem_union_left _
    (Finset.mem_filter.mpr ⟨shLabel_mem_allPrimes σ k, hd⟩)))

theorem Good.not_dvd_add {σ : ShT 𝔊 C} {r : AuxList (groupFamily 𝔊).big C} {w : ℕ}
    (h : Good σ (forbid r w)) (k : ShIdx 𝔊 C) : ¬(σ k : ℕ) ∣ w + tupleProd C r := fun hd =>
  h.2 k (Finset.mem_union_right _ (Finset.mem_union_right _
    (Finset.mem_filter.mpr ⟨shLabel_mem_allPrimes σ k, hd⟩)))

/-- The number of forbidden primes. -/
theorem card_forbid_le (h𝔊 : 𝔊.Admissible P x) (r : AuxList (groupFamily 𝔊).big C) (w : ℕ) :
    (forbid r w).card ≤
      (∑ g, (C g).card) + (𝔊.totalHits w + 𝔊.totalHits (w + tupleProd C r)) := by
  have h1 : (Finset.univ.image fun gi : (Σ g : Fin 𝔊.numBig, {i : Fin J // i ∈ C g}) =>
      (r gi.1 gi.2 : ℕ)).card ≤ ∑ g, (C g).card := by
    refine Finset.card_image_le.trans (le_of_eq ?_)
    rw [Finset.card_univ, Fintype.card_sigma]
    exact Finset.sum_congr rfl fun g _ => Fintype.card_coe (C g)
  unfold forbid
  refine (Finset.card_union_le _ _).trans (Nat.add_le_add h1 ?_)
  refine (Finset.card_union_le _ _).trans (le_of_eq ?_)
  rw [totalHits_eq_card h𝔊, totalHits_eq_card h𝔊]

open _root_.Classical in
/-- The indicator of a collision of the shared labels. -/
def badInd (σ : ShT 𝔊 C) (A : Finset ℕ) : ℝ := if Good σ A then 0 else 1

theorem badInd_nonneg (σ : ShT 𝔊 C) (A : Finset ℕ) : 0 ≤ badInd σ A := by
  unfold badInd
  split_ifs
  · exact le_rfl
  · exact zero_le_one

theorem badInd_of_good {σ : ShT 𝔊 C} {A : Finset ℕ} (h : Good σ A) : badInd σ A = 0 := by
  unfold badInd
  exact if_pos h

theorem badInd_of_not {σ : ShT 𝔊 C} {A : Finset ℕ} (h : ¬Good σ A) : badInd σ A = 1 := by
  unfold badInd
  exact if_neg h

/-- A collision is a coincidence of two shared labels or a shared label in `A`. -/
theorem badInd_le (σ : ShT 𝔊 C) (A : Finset ℕ) :
    badInd σ A ≤
      (∑ k, ∑ k', (if k ≠ k' ∧ (σ k : ℕ) = (σ k' : ℕ) then (1 : ℝ) else 0)) +
        ∑ k, (if (σ k : ℕ) ∈ A then (1 : ℝ) else 0) := by
  have h1 : ∀ k k' : ShIdx 𝔊 C,
      (0 : ℝ) ≤ (if k ≠ k' ∧ (σ k : ℕ) = (σ k' : ℕ) then (1 : ℝ) else 0) := fun k k' => by
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  have h2 : ∀ k : ShIdx 𝔊 C, (0 : ℝ) ≤ (if (σ k : ℕ) ∈ A then (1 : ℝ) else 0) := fun k => by
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  have hS1 : (0 : ℝ) ≤ ∑ k, ∑ k', (if k ≠ k' ∧ (σ k : ℕ) = (σ k' : ℕ) then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun k' _ => h1 k k'
  have hS2 : (0 : ℝ) ≤ ∑ k, (if (σ k : ℕ) ∈ A then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun k _ => h2 k
  by_cases hg : Good σ A
  · rw [badInd_of_good hg]
    exact add_nonneg hS1 hS2
  · rw [badInd_of_not hg]
    unfold Good at hg
    rcases not_and_or.mp hg with hinj | hmem
    · have hex : ∃ k k' : ShIdx 𝔊 C, (σ k : ℕ) = (σ k' : ℕ) ∧ k ≠ k' := by
        by_contra hcon
        refine hinj fun k k' hkk' => ?_
        by_contra hne
        exact hcon ⟨k, k', hkk', hne⟩
      obtain ⟨k, k', he, hne⟩ := hex
      have hterm : (1 : ℝ) = (if k ≠ k' ∧ (σ k : ℕ) = (σ k' : ℕ) then (1 : ℝ) else 0) :=
        (if_pos ⟨hne, he⟩).symm
      have hle1 : (1 : ℝ) ≤ ∑ k'', (if k ≠ k'' ∧ (σ k : ℕ) = (σ k'' : ℕ) then (1 : ℝ) else 0) :=
        hterm.le.trans (Finset.single_le_sum
          (f := fun k'' => (if k ≠ k'' ∧ (σ k : ℕ) = (σ k'' : ℕ) then (1 : ℝ) else 0))
          (fun k'' _ => h1 k k'') (Finset.mem_univ k'))
      have hle2 : (1 : ℝ) ≤
          ∑ k₁, ∑ k'', (if k₁ ≠ k'' ∧ (σ k₁ : ℕ) = (σ k'' : ℕ) then (1 : ℝ) else 0) :=
        hle1.trans (Finset.single_le_sum
          (f := fun k₁ => ∑ k'', (if k₁ ≠ k'' ∧ (σ k₁ : ℕ) = (σ k'' : ℕ) then (1 : ℝ) else 0))
          (fun k₁ _ => Finset.sum_nonneg fun k'' _ => h1 k₁ k'') (Finset.mem_univ k))
      linarith
    · obtain ⟨k, hk⟩ : ∃ k, (σ k : ℕ) ∈ A := by
        by_contra hcon
        exact hmem fun k hk => hcon ⟨k, hk⟩
      have hterm : (1 : ℝ) = (if (σ k : ℕ) ∈ A then (1 : ℝ) else 0) := (if_pos hk).symm
      have hle : (1 : ℝ) ≤ ∑ k', (if (σ k' : ℕ) ∈ A then (1 : ℝ) else 0) :=
        hterm.le.trans (Finset.single_le_sum
          (f := fun k' => (if (σ k' : ℕ) ∈ A then (1 : ℝ) else 0))
          (fun k' _ => h2 k') (Finset.mem_univ k))
      linarith

/-- The probability that one shared label equals `p` is the atom of its law. -/
theorem marg_point (k : ShIdx 𝔊 C) (p : ℕ) :
    ∑ a : {q : ℕ // q ∈ shGrp 𝔊 C k},
        Graph.primeGroupLaw (shGrp 𝔊 C k) a * (if (a : ℕ) = p then (1 : ℝ) else 0) =
      if p ∈ shGrp 𝔊 C k then Graph.primeGroupLaw (shGrp 𝔊 C k) p else 0 := by
  rw [Finset.sum_coe_sort (shGrp 𝔊 C k)
    (fun q => Graph.primeGroupLaw (shGrp 𝔊 C k) q * (if q = p then (1 : ℝ) else 0))]
  have h : ∀ q ∈ shGrp 𝔊 C k,
      Graph.primeGroupLaw (shGrp 𝔊 C k) q * (if q = p then (1 : ℝ) else 0) =
        if q = p then Graph.primeGroupLaw (shGrp 𝔊 C k) q else 0 := fun q _ => by
    split_ifs
    · exact mul_one _
    · exact mul_zero _
  rw [Finset.sum_congr rfl h]
  exact Finset.sum_ite_eq' (shGrp 𝔊 C k) p _

/-- **A shared label lies in `A` with probability at most `|A| δ`.** -/
theorem sum_shWeight_mem_le
    (hlaw : ∀ g : 𝔊.Index, ∑ p ∈ 𝔊.group g, Graph.primeGroupLaw (𝔊.group g) p = 1) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hatom : ∀ (k : ShIdx 𝔊 C) (a : {p : ℕ // p ∈ shGrp 𝔊 C k}),
      Graph.primeGroupLaw (shGrp 𝔊 C k) a ≤ δ) (k : ShIdx 𝔊 C) (A : Finset ℕ) :
    ∑ σ : ShT 𝔊 C, shWeight σ * (if (σ k : ℕ) ∈ A then (1 : ℝ) else 0) ≤ (A.card : ℝ) * δ := by
  rw [sum_shWeight_mul_single hlaw k (fun p => if p ∈ A then (1 : ℝ) else 0),
    Finset.sum_coe_sort (shGrp 𝔊 C k)
      (fun q => Graph.primeGroupLaw (shGrp 𝔊 C k) q * (if q ∈ A then (1 : ℝ) else 0))]
  have hterm : ∀ q ∈ shGrp 𝔊 C k,
      Graph.primeGroupLaw (shGrp 𝔊 C k) q * (if q ∈ A then (1 : ℝ) else 0) ≤
        if q ∈ A then δ else 0 := fun q hq => by
    split_ifs
    · rw [mul_one]
      exact hatom k ⟨q, hq⟩
    · rw [mul_zero]
  calc ∑ q ∈ shGrp 𝔊 C k,
        Graph.primeGroupLaw (shGrp 𝔊 C k) q * (if q ∈ A then (1 : ℝ) else 0)
      ≤ ∑ q ∈ shGrp 𝔊 C k, (if q ∈ A then δ else 0) := Finset.sum_le_sum hterm
    _ = ∑ _q ∈ (shGrp 𝔊 C k).filter (fun q => q ∈ A), δ := (Finset.sum_filter _ _).symm
    _ = (((shGrp 𝔊 C k).filter (fun q => q ∈ A)).card : ℝ) * δ := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (A.card : ℝ) * δ :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card
          fun q hq => (Finset.mem_filter.mp hq).2)) hδ

/-- **Two shared labels coincide with probability at most `δ`.** -/
theorem sum_shWeight_coll_le
    (hlaw : ∀ g : 𝔊.Index, ∑ p ∈ 𝔊.group g, Graph.primeGroupLaw (𝔊.group g) p = 1) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hatom : ∀ (k : ShIdx 𝔊 C) (a : {p : ℕ // p ∈ shGrp 𝔊 C k}),
      Graph.primeGroupLaw (shGrp 𝔊 C k) a ≤ δ) {k k' : ShIdx 𝔊 C} (hkk' : k ≠ k') :
    ∑ σ : ShT 𝔊 C, shWeight σ * (if (σ k : ℕ) = (σ k' : ℕ) then (1 : ℝ) else 0) ≤ δ := by
  have hnn : ∀ (σ : ShT 𝔊 C), ∀ p ∈ shGrp 𝔊 C k',
      (0 : ℝ) ≤ (if (σ k : ℕ) = p then (1 : ℝ) else 0) *
        (if (σ k' : ℕ) = p then (1 : ℝ) else 0) := fun σ p _ => by
    split_ifs <;> norm_num
  have hpt : ∀ σ : ShT 𝔊 C, (if (σ k : ℕ) = (σ k' : ℕ) then (1 : ℝ) else 0) ≤
      ∑ p ∈ shGrp 𝔊 C k', (if (σ k : ℕ) = p then (1 : ℝ) else 0) *
        (if (σ k' : ℕ) = p then (1 : ℝ) else 0) := by
    intro σ
    by_cases he : (σ k : ℕ) = (σ k' : ℕ)
    · rw [if_pos he]
      refine le_trans (le_of_eq ?_) (Finset.single_le_sum (hnn σ) (σ k').2)
      show (1 : ℝ) = (if (σ k : ℕ) = (σ k' : ℕ) then (1 : ℝ) else 0) *
        (if (σ k' : ℕ) = (σ k' : ℕ) then (1 : ℝ) else 0)
      rw [if_pos he, if_pos rfl, mul_one]
    · rw [if_neg he]
      exact Finset.sum_nonneg (hnn σ)
  have hsum : ∑ p ∈ shGrp 𝔊 C k', Graph.primeGroupLaw (shGrp 𝔊 C k') p = 1 := by
    rw [shGrp_eq]
    exact hlaw _
  calc ∑ σ : ShT 𝔊 C, shWeight σ * (if (σ k : ℕ) = (σ k' : ℕ) then (1 : ℝ) else 0)
      ≤ ∑ σ : ShT 𝔊 C, shWeight σ *
          ∑ p ∈ shGrp 𝔊 C k', (if (σ k : ℕ) = p then (1 : ℝ) else 0) *
            (if (σ k' : ℕ) = p then (1 : ℝ) else 0) :=
        Finset.sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hpt σ) (shWeight_nonneg σ)
    _ = ∑ p ∈ shGrp 𝔊 C k', ∑ σ : ShT 𝔊 C, shWeight σ *
          ((if (σ k : ℕ) = p then (1 : ℝ) else 0) *
            (if (σ k' : ℕ) = p then (1 : ℝ) else 0)) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun σ _ => Finset.mul_sum _ _ _
    _ = ∑ p ∈ shGrp 𝔊 C k',
          (if p ∈ shGrp 𝔊 C k then Graph.primeGroupLaw (shGrp 𝔊 C k) p else 0) *
            (if p ∈ shGrp 𝔊 C k' then Graph.primeGroupLaw (shGrp 𝔊 C k') p else 0) :=
        Finset.sum_congr rfl fun p _ => by
          rw [sum_shWeight_mul_pair hlaw hkk' (fun q => if q = p then (1 : ℝ) else 0)
            (fun q => if q = p then (1 : ℝ) else 0), marg_point, marg_point]
    _ ≤ ∑ p ∈ shGrp 𝔊 C k', δ * Graph.primeGroupLaw (shGrp 𝔊 C k') p :=
        Finset.sum_le_sum fun p hp => by
          rw [if_pos hp]
          refine mul_le_mul_of_nonneg_right ?_ (Schur.primeGroupLaw_nonneg _ _)
          split_ifs with h
          · exact hatom k ⟨p, h⟩
          · exact hδ
    _ = δ := by rw [← Finset.mul_sum, hsum, mul_one]

/-- **(cor:shared-collision)** (`[P-06:0340–0346]`): "the harmonic mass of a shared/shared
coincidence, a shared/free coincidence, or a shared prime dividing `w w'`": with `n` shared slots
and every label of probability at most `δ`, a collision has probability at most
`(n² + n |A|) δ`. -/
theorem sum_shWeight_badInd_le
    (hlaw : ∀ g : 𝔊.Index, ∑ p ∈ 𝔊.group g, Graph.primeGroupLaw (𝔊.group g) p = 1) {δ : ℝ}
    (hδ : 0 ≤ δ)
    (hatom : ∀ (k : ShIdx 𝔊 C) (a : {p : ℕ // p ∈ shGrp 𝔊 C k}),
      Graph.primeGroupLaw (shGrp 𝔊 C k) a ≤ δ) (A : Finset ℕ) :
    ∑ σ : ShT 𝔊 C, shWeight σ * badInd σ A ≤
      ((Fintype.card (ShIdx 𝔊 C) : ℝ) ^ 2 +
        (Fintype.card (ShIdx 𝔊 C) : ℝ) * (A.card : ℝ)) * δ := by
  have hcoll : ∀ k k' : ShIdx 𝔊 C, ∑ σ : ShT 𝔊 C, shWeight σ *
      (if k ≠ k' ∧ (σ k : ℕ) = (σ k' : ℕ) then (1 : ℝ) else 0) ≤ δ := by
    intro k k'
    by_cases hkk' : k = k'
    · refine le_trans (le_of_eq ?_) hδ
      exact Finset.sum_eq_zero fun σ _ => by
        rw [if_neg (fun h : k ≠ k' ∧ (σ k : ℕ) = (σ k' : ℕ) => h.1 hkk'), mul_zero]
    · refine le_trans (le_of_eq ?_) (sum_shWeight_coll_le hlaw hδ hatom hkk')
      refine Finset.sum_congr rfl fun σ _ => ?_
      congr 1
      exact if_congr (and_iff_right hkk') rfl rfl
  have e1 : ∀ σ : ShT 𝔊 C, shWeight σ *
      ((∑ k, ∑ k', (if k ≠ k' ∧ (σ k : ℕ) = (σ k' : ℕ) then (1 : ℝ) else 0)) +
        ∑ k, (if (σ k : ℕ) ∈ A then (1 : ℝ) else 0)) =
      (∑ k, ∑ k', shWeight σ * (if k ≠ k' ∧ (σ k : ℕ) = (σ k' : ℕ) then (1 : ℝ) else 0)) +
        ∑ k, shWeight σ * (if (σ k : ℕ) ∈ A then (1 : ℝ) else 0) := fun σ => by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    exact congrArg₂ (fun a b : ℝ => a + b)
      (Finset.sum_congr rfl fun k _ => Finset.mul_sum _ _ _) rfl
  calc ∑ σ : ShT 𝔊 C, shWeight σ * badInd σ A
      ≤ ∑ σ : ShT 𝔊 C, shWeight σ *
          ((∑ k, ∑ k', (if k ≠ k' ∧ (σ k : ℕ) = (σ k' : ℕ) then (1 : ℝ) else 0)) +
            ∑ k, (if (σ k : ℕ) ∈ A then (1 : ℝ) else 0)) :=
        Finset.sum_le_sum fun σ _ =>
          mul_le_mul_of_nonneg_left (badInd_le σ A) (shWeight_nonneg σ)
    _ = (∑ k, ∑ k', ∑ σ : ShT 𝔊 C, shWeight σ *
            (if k ≠ k' ∧ (σ k : ℕ) = (σ k' : ℕ) then (1 : ℝ) else 0)) +
          ∑ k, ∑ σ : ShT 𝔊 C, shWeight σ * (if (σ k : ℕ) ∈ A then (1 : ℝ) else 0) := by
        rw [Finset.sum_congr rfl fun σ _ => e1 σ, Finset.sum_add_distrib]
        refine congrArg₂ (fun a b : ℝ => a + b) ?_ Finset.sum_comm
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ ≤ (∑ _k : ShIdx 𝔊 C, ∑ _k' : ShIdx 𝔊 C, δ) + ∑ _k : ShIdx 𝔊 C, (A.card : ℝ) * δ :=
        add_le_add
          (Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun k' _ => hcoll k k')
          (Finset.sum_le_sum fun k _ => sum_shWeight_mem_le hlaw hδ hatom k A)
    _ = ((Fintype.card (ShIdx 𝔊 C) : ℝ) ^ 2 +
          (Fintype.card (ShIdx 𝔊 C) : ℝ) * (A.card : ℝ)) * δ := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

end States

end Strip

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
