module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.StripSplit
public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.Sanity

/-!
# Removal of the shared labels: the law of the shared labels and the normalizations

`[P-06:0321–0328]`: "Away from shared-label collisions, (cor:stripping-normalization)
`ω_g(D_R w) - M = ω_g(w) - t_g`, `V_g^{-M-t_g} = V_g^{-(M-t_g)} V_g^{-2t_g}`,
`1/n = 1/(D_R w)`. The factor `D_R⁻¹` changes each shared sum into its probability law `μ_g`, and
the remaining list factors and damping are exactly `W_𝐭(w) W_𝐭(w')`."

* `shWeight σ = ∏_k μ_{g(k)}(σ_k)`: the law of the shared labels. `sum_shWeight_mul_prod`: the
  shared labels are independent; `sum_shWeight`, `sum_shWeight_mul_single`,
  `sum_shWeight_mul_pair`.
* `stateMass_mul_inv_shProd`: `∏_g V_g^{-M} / D_R = (law of the shared labels) · ∏_g V_g^{-t_g}`.
* `targetNorm_eq_prod`: [S]'s target coefficient is `∏_g V_g^{-t_g}` with `t = markCount`.
* `card_shIdx_add`: the numbers of shared and unshared slots add up to `M s_P`.
* `omegaOf_mul`: `ω(D_R w) = ω_P(w) + #(shared slots)` when the shared labels are distinct and
  none divides `w`.
* `targetNorm_mul_damping_sq`: then `∏_g V_g^{-t_g} · q₀^{ω(D_R w) - M s_P}` is the scalar factor
  `activeCoeff` of `W_𝐭(w)`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference

noncomputable section

namespace Strip

section Weights

variable {𝔊 : ActiveGroups} {J : ℕ} {C : Fin 𝔊.numBig → Finset (Fin J)}

/-! ### The groups of the shared slots -/

/-- The group of a shared slot, as an index of the active groups. -/
def shIndex (k : ShIdx 𝔊 C) : 𝔊.Index :=
  Sum.elim (fun a => Sum.inl a.1) (fun b => Sum.inr b.1) k

theorem shGrp_eq (k : ShIdx 𝔊 C) : shGrp 𝔊 C k = 𝔊.group (shIndex k) := by
  rcases k with a | b
  · rfl
  · rfl

theorem shLabel_mem_allPrimes (σ : ShT 𝔊 C) (k : ShIdx 𝔊 C) : (σ k : ℕ) ∈ 𝔊.allPrimes := by
  have h : (σ k : ℕ) ∈ 𝔊.group (shIndex k) := by
    rw [← shGrp_eq]
    exact (σ k).2
  exact Finset.mem_biUnion.mpr ⟨shIndex k, Finset.mem_univ _, h⟩

theorem prime_of_mem_allPrimes {P : ActiveGroupConstants} {x : ℝ} (h𝔊 : 𝔊.Admissible P x)
    {p : ℕ} (hp : p ∈ 𝔊.allPrimes) : p.Prime := by
  obtain ⟨g, -, hg⟩ := Finset.mem_biUnion.mp hp
  exact h𝔊.prime g p hg

theorem shLabel_prime {P : ActiveGroupConstants} {x : ℝ} (h𝔊 : 𝔊.Admissible P x)
    (σ : ShT 𝔊 C) (k : ShIdx 𝔊 C) : (σ k : ℕ).Prime :=
  prime_of_mem_allPrimes h𝔊 (shLabel_mem_allPrimes σ k)

theorem shProd_pos {P : ActiveGroupConstants} {x : ℝ} (h𝔊 : 𝔊.Admissible P x)
    (σ : ShT 𝔊 C) : 0 < shProd σ :=
  Finset.prod_pos fun k _ => (shLabel_prime h𝔊 σ k).pos

/-! ### The law of the shared labels -/

/-- **The law of the shared labels**: independent, of law `μ_g` in every shared slot of the
group `g`. -/
def shWeight (σ : ShT 𝔊 C) : ℝ := ∏ k, Graph.primeGroupLaw (shGrp 𝔊 C k) (σ k)

theorem shWeight_nonneg (σ : ShT 𝔊 C) : 0 ≤ shWeight σ :=
  Finset.prod_nonneg fun _ _ => Schur.primeGroupLaw_nonneg _ _

/-- **The shared labels are independent.** -/
theorem sum_shWeight_mul_prod (φ : ShIdx 𝔊 C → ℕ → ℝ) :
    ∑ σ : ShT 𝔊 C, shWeight σ * ∏ k, φ k (σ k : ℕ) =
      ∏ k, ∑ a : {p : ℕ // p ∈ shGrp 𝔊 C k},
        Graph.primeGroupLaw (shGrp 𝔊 C k) a * φ k (a : ℕ) := by
  rw [Fintype.prod_sum (fun (k : ShIdx 𝔊 C) (a : {p : ℕ // p ∈ shGrp 𝔊 C k}) =>
    Graph.primeGroupLaw (shGrp 𝔊 C k) a * φ k (a : ℕ))]
  refine Finset.sum_congr rfl fun σ _ => ?_
  unfold shWeight
  rw [← Finset.prod_mul_distrib]

/-- The law of one shared label has total mass one. -/
theorem sum_law (hlaw : ∀ g : 𝔊.Index, ∑ p ∈ 𝔊.group g, Graph.primeGroupLaw (𝔊.group g) p = 1)
    (k : ShIdx 𝔊 C) :
    ∑ a : {p : ℕ // p ∈ shGrp 𝔊 C k}, Graph.primeGroupLaw (shGrp 𝔊 C k) a = 1 := by
  rw [Finset.sum_coe_sort (shGrp 𝔊 C k) (fun q => Graph.primeGroupLaw (shGrp 𝔊 C k) q),
    shGrp_eq]
  exact hlaw _

/-- The law of the shared labels has total mass one. -/
theorem sum_shWeight
    (hlaw : ∀ g : 𝔊.Index, ∑ p ∈ 𝔊.group g, Graph.primeGroupLaw (𝔊.group g) p = 1) :
    ∑ σ : ShT 𝔊 C, shWeight σ = 1 := by
  have h : ∑ σ : ShT 𝔊 C, shWeight σ * ∏ _k : ShIdx 𝔊 C, (1 : ℝ) =
      ∏ k, ∑ a : {p : ℕ // p ∈ shGrp 𝔊 C k},
        Graph.primeGroupLaw (shGrp 𝔊 C k) a * (1 : ℝ) :=
    sum_shWeight_mul_prod (fun _ _ => (1 : ℝ))
  calc ∑ σ : ShT 𝔊 C, shWeight σ
      = ∑ σ : ShT 𝔊 C, shWeight σ * ∏ _k : ShIdx 𝔊 C, (1 : ℝ) :=
        Finset.sum_congr rfl fun σ _ => by rw [Finset.prod_const_one, mul_one]
    _ = ∏ k, ∑ a : {p : ℕ // p ∈ shGrp 𝔊 C k},
          Graph.primeGroupLaw (shGrp 𝔊 C k) a * (1 : ℝ) := h
    _ = 1 := Finset.prod_eq_one fun k _ =>
        (Finset.sum_congr rfl fun a _ => mul_one _).trans (sum_law hlaw k)

/-- **The law of one shared label.** -/
theorem sum_shWeight_mul_single
    (hlaw : ∀ g : 𝔊.Index, ∑ p ∈ 𝔊.group g, Graph.primeGroupLaw (𝔊.group g) p = 1)
    (k : ShIdx 𝔊 C) (ψ : ℕ → ℝ) :
    ∑ σ : ShT 𝔊 C, shWeight σ * ψ (σ k : ℕ) =
      ∑ a : {p : ℕ // p ∈ shGrp 𝔊 C k}, Graph.primeGroupLaw (shGrp 𝔊 C k) a * ψ (a : ℕ) := by
  have h : ∑ σ : ShT 𝔊 C, shWeight σ * ∏ j, (if j = k then ψ (σ j : ℕ) else 1) =
      ∏ j, ∑ a : {p : ℕ // p ∈ shGrp 𝔊 C j},
        Graph.primeGroupLaw (shGrp 𝔊 C j) a * (if j = k then ψ (a : ℕ) else 1) :=
    sum_shWeight_mul_prod (fun j a => if j = k then ψ a else 1)
  have hL : ∀ σ : ShT 𝔊 C, ∏ j, (if j = k then ψ (σ j : ℕ) else 1) = ψ (σ k : ℕ) := fun σ => by
    rw [Finset.prod_ite_eq' Finset.univ k (fun j => ψ (σ j : ℕ))]
    exact if_pos (Finset.mem_univ k)
  have hR : ∀ j : ShIdx 𝔊 C, j ≠ k →
      ∑ a : {p : ℕ // p ∈ shGrp 𝔊 C j},
        Graph.primeGroupLaw (shGrp 𝔊 C j) a * (if j = k then ψ (a : ℕ) else 1) = 1 :=
    fun j hj =>
      (Finset.sum_congr rfl fun a _ => by rw [if_neg hj, mul_one]).trans (sum_law hlaw j)
  calc ∑ σ : ShT 𝔊 C, shWeight σ * ψ (σ k : ℕ)
      = ∑ σ : ShT 𝔊 C, shWeight σ * ∏ j, (if j = k then ψ (σ j : ℕ) else 1) :=
        Finset.sum_congr rfl fun σ _ => by rw [hL σ]
    _ = ∏ j, ∑ a : {p : ℕ // p ∈ shGrp 𝔊 C j},
          Graph.primeGroupLaw (shGrp 𝔊 C j) a * (if j = k then ψ (a : ℕ) else 1) := h
    _ = ∑ a : {p : ℕ // p ∈ shGrp 𝔊 C k},
          Graph.primeGroupLaw (shGrp 𝔊 C k) a * (if k = k then ψ (a : ℕ) else 1) :=
        Fintype.prod_eq_single k hR
    _ = ∑ a : {p : ℕ // p ∈ shGrp 𝔊 C k}, Graph.primeGroupLaw (shGrp 𝔊 C k) a * ψ (a : ℕ) :=
        Finset.sum_congr rfl fun a _ => by rw [if_pos rfl]

/-- **The joint law of two shared labels is the product of their laws.** -/
theorem sum_shWeight_mul_pair
    (hlaw : ∀ g : 𝔊.Index, ∑ p ∈ 𝔊.group g, Graph.primeGroupLaw (𝔊.group g) p = 1)
    {k k' : ShIdx 𝔊 C} (hkk' : k ≠ k') (ψ ψ' : ℕ → ℝ) :
    ∑ σ : ShT 𝔊 C, shWeight σ * (ψ (σ k : ℕ) * ψ' (σ k' : ℕ)) =
      (∑ a : {p : ℕ // p ∈ shGrp 𝔊 C k}, Graph.primeGroupLaw (shGrp 𝔊 C k) a * ψ (a : ℕ)) *
        ∑ a : {p : ℕ // p ∈ shGrp 𝔊 C k'},
          Graph.primeGroupLaw (shGrp 𝔊 C k') a * ψ' (a : ℕ) := by
  have h : ∑ σ : ShT 𝔊 C, shWeight σ *
        ∏ j, ((if j = k then ψ (σ j : ℕ) else 1) * (if j = k' then ψ' (σ j : ℕ) else 1)) =
      ∏ j, ∑ a : {p : ℕ // p ∈ shGrp 𝔊 C j}, Graph.primeGroupLaw (shGrp 𝔊 C j) a *
        ((if j = k then ψ (a : ℕ) else 1) * (if j = k' then ψ' (a : ℕ) else 1)) :=
    sum_shWeight_mul_prod
      (fun j a => (if j = k then ψ a else 1) * (if j = k' then ψ' a else 1))
  have hL : ∀ σ : ShT 𝔊 C,
      ∏ j, ((if j = k then ψ (σ j : ℕ) else 1) * (if j = k' then ψ' (σ j : ℕ) else 1)) =
        ψ (σ k : ℕ) * ψ' (σ k' : ℕ) := fun σ => by
    rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k (fun j => ψ (σ j : ℕ)),
      Finset.prod_ite_eq' Finset.univ k' (fun j => ψ' (σ j : ℕ)),
      if_pos (Finset.mem_univ k), if_pos (Finset.mem_univ k')]
  have hR : ∀ j : ShIdx 𝔊 C, j ≠ k ∧ j ≠ k' →
      ∑ a : {p : ℕ // p ∈ shGrp 𝔊 C j}, Graph.primeGroupLaw (shGrp 𝔊 C j) a *
        ((if j = k then ψ (a : ℕ) else 1) * (if j = k' then ψ' (a : ℕ) else 1)) = 1 :=
    fun j hj =>
      (Finset.sum_congr rfl fun a _ => by
        rw [if_neg hj.1, if_neg hj.2, mul_one, mul_one]).trans (sum_law hlaw j)
  calc ∑ σ : ShT 𝔊 C, shWeight σ * (ψ (σ k : ℕ) * ψ' (σ k' : ℕ))
      = ∑ σ : ShT 𝔊 C, shWeight σ *
          ∏ j, ((if j = k then ψ (σ j : ℕ) else 1) * (if j = k' then ψ' (σ j : ℕ) else 1)) :=
        Finset.sum_congr rfl fun σ _ => by rw [hL σ]
    _ = ∏ j, ∑ a : {p : ℕ // p ∈ shGrp 𝔊 C j}, Graph.primeGroupLaw (shGrp 𝔊 C j) a *
          ((if j = k then ψ (a : ℕ) else 1) * (if j = k' then ψ' (a : ℕ) else 1)) := h
    _ = (∑ a : {p : ℕ // p ∈ shGrp 𝔊 C k}, Graph.primeGroupLaw (shGrp 𝔊 C k) a *
          ((if k = k then ψ (a : ℕ) else 1) * (if k = k' then ψ' (a : ℕ) else 1))) *
        ∑ a : {p : ℕ // p ∈ shGrp 𝔊 C k'}, Graph.primeGroupLaw (shGrp 𝔊 C k') a *
          ((if k' = k then ψ (a : ℕ) else 1) * (if k' = k' then ψ' (a : ℕ) else 1)) :=
        Fintype.prod_eq_mul k k' hkk' hR
    _ = _ := by
        refine congrArg₂ (fun a b : ℝ => a * b)
          (Finset.sum_congr rfl fun a _ => ?_) (Finset.sum_congr rfl fun a _ => ?_)
        · rw [if_pos rfl, if_neg hkk', mul_one]
        · rw [if_neg (Ne.symm hkk'), if_pos rfl, one_mul]

/-! ### The normalizations -/

/-- The shared slots of a big group and its freed slots are its first `J` slots. -/
theorem card_compl_slots (c : Finset (Fin J)) :
    Fintype.card {i : Fin J // i ∉ c} + c.card = J := by
  have h := Fintype.card_subtype_compl (fun i : Fin J => i ∈ c)
  rw [Fintype.card_fin, Fintype.card_coe] at h
  have hle : c.card ≤ J := (Finset.card_le_univ c).trans_eq (Fintype.card_fin J)
  omega

/-- **`∏_g V_g^{-M} / D_R` is the law of the shared labels times `∏_g V_g^{-t_g}`**
(`[P-06:0324–0326]`). -/
theorem stateMass_mul_inv_shProd (σ : ShT 𝔊 C) :
    stateMass (groupFamily 𝔊) J 1 * ((shProd σ : ℕ) : ℝ)⁻¹ =
      shWeight σ * targetNorm (groupFamily 𝔊) 1 C := by
  have h1 : shWeight σ =
      (∏ k : ShIdx 𝔊 C, (Graph.primeGroupReciprocalMass (shGrp 𝔊 C k))⁻¹) *
        ((shProd σ : ℕ) : ℝ)⁻¹ := by
    unfold shWeight shProd
    rw [Nat.cast_prod, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    unfold Graph.primeGroupLaw
    rw [one_div, mul_inv]
  have h2 : ∏ k : ShIdx 𝔊 C, (Graph.primeGroupReciprocalMass (shGrp 𝔊 C k))⁻¹ =
      (∏ g : Fin 𝔊.numSmall,
          (Graph.primeGroupReciprocalMass ((groupFamily 𝔊).small g))⁻¹ ^ J) *
        ∏ g : Fin 𝔊.numBig, (Graph.primeGroupReciprocalMass ((groupFamily 𝔊).big g))⁻¹ ^
          Fintype.card {i : Fin J // i ∉ C g} := by
    rw [Fintype.prod_sum_type]
    refine congrArg₂ (fun a b : ℝ => a * b) ?_ ?_
    · refine (Fintype.prod_prod_type' fun (g : Fin 𝔊.numSmall) (_ : Fin J) =>
        (Graph.primeGroupReciprocalMass ((groupFamily 𝔊).small g))⁻¹).trans ?_
      exact Finset.prod_congr rfl fun g _ => by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    · refine (Fintype.prod_sigma' fun (g : Fin 𝔊.numBig) (_ : {i : Fin J // i ∉ C g}) =>
        (Graph.primeGroupReciprocalMass ((groupFamily 𝔊).big g))⁻¹).trans ?_
      exact Finset.prod_congr rfl fun g _ => by rw [Finset.prod_const, Finset.card_univ]
  have hS : ∏ g : Fin 𝔊.numSmall,
        (Graph.primeGroupReciprocalMass ((groupFamily 𝔊).small g) ^ (J + 1))⁻¹ =
      (∏ g : Fin 𝔊.numSmall,
          (Graph.primeGroupReciprocalMass ((groupFamily 𝔊).small g))⁻¹ ^ J) *
        ∏ g : Fin 𝔊.numSmall,
          (Graph.primeGroupReciprocalMass ((groupFamily 𝔊).small g) ^ 1)⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun g _ => by rw [pow_one, pow_succ, mul_inv, inv_pow]
  have hB : ∏ g : Fin 𝔊.numBig,
        (Graph.primeGroupReciprocalMass ((groupFamily 𝔊).big g) ^ (J + 1))⁻¹ =
      (∏ g : Fin 𝔊.numBig, (Graph.primeGroupReciprocalMass ((groupFamily 𝔊).big g))⁻¹ ^
          Fintype.card {i : Fin J // i ∉ C g}) *
        ∏ g : Fin 𝔊.numBig,
          (Graph.primeGroupReciprocalMass ((groupFamily 𝔊).big g) ^ (1 + (C g).card))⁻¹ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun g _ => ?_
    have hc := card_compl_slots (C g)
    rw [← inv_pow, ← inv_pow, ← pow_add]
    congr 1
    omega
  have h3 : stateMass (groupFamily 𝔊) J 1 =
      (∏ k : ShIdx 𝔊 C, (Graph.primeGroupReciprocalMass (shGrp 𝔊 C k))⁻¹) *
        targetNorm (groupFamily 𝔊) 1 C := by
    unfold stateMass targetNorm
    rw [h2, hS, hB]
    ring
  rw [h1, h3]
  ring

/-- [S]'s target coefficient `∏_g V_g^{-t_g}` with `t_g = markCount`. -/
theorem targetNorm_eq_prod :
    targetNorm (groupFamily 𝔊) 1 C =
      ∏ g : 𝔊.Index, (reciprocalMass (𝔊.group g) ^ markCount 𝔊 C g)⁻¹ := by
  rw [Fintype.prod_sum_type]
  unfold targetNorm
  refine congrArg₂ (fun a b : ℝ => a * b) rfl (Finset.prod_congr rfl fun g _ => ?_)
  rw [Nat.add_comm]
  rfl

/-- **The shared and the unshared slots are all the slots**: `#(shared) + ∑_g t_g = M s_P`. -/
theorem card_shIdx_add (C : Fin 𝔊.numBig → Finset (Fin J)) :
    Fintype.card (ShIdx 𝔊 C) + ∑ g, markCount 𝔊 C g = (J + 1) * (𝔊.numSmall + 𝔊.numBig) := by
  have h1 : Fintype.card (ShIdx 𝔊 C) =
      𝔊.numSmall * J + ∑ g : Fin 𝔊.numBig, Fintype.card {i : Fin J // i ∉ C g} := by
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      Fintype.card_sigma]
  have h2 : ∑ g : 𝔊.Index, markCount 𝔊 C g =
      𝔊.numSmall + ∑ g : Fin 𝔊.numBig, ((C g).card + 1) := by
    rw [Fintype.sum_sum_type]
    refine congrArg₂ (fun a b : ℕ => a + b) ?_ rfl
    calc ∑ g : Fin 𝔊.numSmall, markCount 𝔊 C (Sum.inl g) = ∑ _g : Fin 𝔊.numSmall, 1 := rfl
      _ = 𝔊.numSmall := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  have h3 : ∑ g : Fin 𝔊.numBig, Fintype.card {i : Fin J // i ∉ C g} +
      ∑ g : Fin 𝔊.numBig, ((C g).card + 1) = 𝔊.numBig * (J + 1) := by
    rw [← Finset.sum_add_distrib]
    calc ∑ g : Fin 𝔊.numBig, (Fintype.card {i : Fin J // i ∉ C g} + ((C g).card + 1))
        = ∑ _g : Fin 𝔊.numBig, (J + 1) := Finset.sum_congr rfl fun g _ => by
          have hc := card_compl_slots (C g)
          omega
      _ = 𝔊.numBig * (J + 1) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  calc Fintype.card (ShIdx 𝔊 C) + ∑ g, markCount 𝔊 C g
      = 𝔊.numSmall * J + 𝔊.numSmall +
          (∑ g : Fin 𝔊.numBig, Fintype.card {i : Fin J // i ∉ C g} +
            ∑ g : Fin 𝔊.numBig, ((C g).card + 1)) := by
        rw [h1, h2]
        ring
    _ = 𝔊.numSmall * J + 𝔊.numSmall + 𝔊.numBig * (J + 1) := by rw [h3]
    _ = (J + 1) * (𝔊.numSmall + 𝔊.numBig) := by ring

/-! ### The number of active primes dividing a position -/

/-- For pairwise disjoint groups, the hits of all groups are the hits of their union. -/
theorem sum_card_filter {P : ActiveGroupConstants} {x : ℝ} (h𝔊 : 𝔊.Admissible P x)
    (hit : ℕ → Prop) [DecidablePred hit] :
    ∑ g : 𝔊.Index, ((𝔊.group g).filter hit).card = (𝔊.allPrimes.filter hit).card := by
  unfold ActiveGroups.allPrimes
  rw [Finset.filter_biUnion, Finset.card_biUnion]
  intro g _ g' _ hgg'
  exact Finset.disjoint_filter_filter (h𝔊.disjoint g g' hgg')

theorem totalHits_eq_card {P : ActiveGroupConstants} {x : ℝ} (h𝔊 : 𝔊.Admissible P x) (w : ℕ) :
    𝔊.totalHits w = (𝔊.allPrimes.filter fun p => p ∣ w).card :=
  sum_card_filter h𝔊 _

theorem omegaOf_eq_card {P : ActiveGroupConstants} {x : ℝ} (h𝔊 : 𝔊.Admissible P x)
    (hit : ℕ → Prop) [DecidablePred hit] :
    (groupFamily 𝔊).omegaOf hit = (𝔊.allPrimes.filter hit).card := by
  have hc : ∀ s : Finset ℕ, countHits hit s = (s.filter hit).card := fun s => by
    unfold countHits
    congr
  rw [← sum_card_filter h𝔊 hit, Fintype.sum_sum_type]
  unfold GroupFamily.omegaOf
  refine congrArg₂ (fun a b : ℕ => a + b) (Finset.sum_congr rfl fun g _ => hc _)
    (Finset.sum_congr rfl fun g _ => hc _)

/-- `ω(n)` of [S] at a natural position is the number of active primes dividing it. -/
theorem omegaOf_natCast {P : ActiveGroupConstants} {x : ℝ} (h𝔊 : 𝔊.Admissible P x) (m : ℕ) :
    (groupFamily 𝔊).omegaOf (fun p => intPos.hit p ((m : ℕ) : ℤ)) =
      (𝔊.allPrimes.filter fun p => p ∣ m).card := by
  classical
  rw [omegaOf_eq_card h𝔊]
  exact congrArg Finset.card (Finset.filter_congr fun p _ => Int.natCast_dvd_natCast)

/-- **`ω(D_R w) = ω_P(w) + #(shared slots)`** when the shared labels are distinct and none of
them divides `w` (`[P-06:0322]`). -/
theorem omegaOf_mul {P : ActiveGroupConstants} {x : ℝ} (h𝔊 : 𝔊.Admissible P x) (σ : ShT 𝔊 C)
    (hinj : Function.Injective fun k => (σ k : ℕ)) {w : ℕ} (hw : ∀ k, ¬(σ k : ℕ) ∣ w) :
    (groupFamily 𝔊).omegaOf (fun p => intPos.hit p ((shProd σ * w : ℕ) : ℤ)) =
      𝔊.totalHits w + Fintype.card (ShIdx 𝔊 C) := by
  have hset : (𝔊.allPrimes.filter fun p => p ∣ shProd σ * w) =
      (𝔊.allPrimes.filter fun p => p ∣ w) ∪ Finset.univ.image (fun k => (σ k : ℕ)) := by
    ext p
    rw [Finset.mem_filter, Finset.mem_union, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨hp, hd⟩
      have hpp : p.Prime := prime_of_mem_allPrimes h𝔊 hp
      rcases (Nat.Prime.dvd_mul hpp).mp hd with h1 | h1
      · obtain ⟨k, -, hk⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp h1
        exact Or.inr ⟨k, Finset.mem_univ k,
          ((Nat.prime_dvd_prime_iff_eq hpp (shLabel_prime h𝔊 σ k)).mp hk).symm⟩
      · exact Or.inl ⟨hp, h1⟩
    · rintro (⟨hp, hd⟩ | ⟨k, -, rfl⟩)
      · exact ⟨hp, Dvd.dvd.mul_left hd _⟩
      · exact ⟨shLabel_mem_allPrimes σ k,
          Dvd.dvd.mul_right (Finset.dvd_prod_of_mem (fun k => (σ k : ℕ)) (Finset.mem_univ k)) _⟩
  have hdisj : Disjoint (𝔊.allPrimes.filter fun p => p ∣ w)
      (Finset.univ.image (fun k => (σ k : ℕ))) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hq
    exact hw k (Finset.mem_filter.mp hp).2
  rw [omegaOf_natCast h𝔊, hset, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ hinj, Finset.card_univ, totalHits_eq_card h𝔊]

/-- **The damping and the list normalization of an endpoint become the scalar factor of
`W_𝐭(w)`** (`[P-06:0321–0328]`): for distinct shared labels none of which divides `w`, and `w`
with at least `∑_g t_g` active prime divisors,
`∏_g V_g^{-t_g} · q₀^{ω(D_R w) - M s_P} = q₀^{ω_P(w) - ∑_g t_g} ∏_g V_g^{-t_g}`. -/
theorem targetNorm_mul_damping_sq {P : ActiveGroupConstants} {x : ℝ} (h𝔊 : 𝔊.Admissible P x)
    {q₀ : ℝ} (hq : 0 < q₀) (σ : ShT 𝔊 C) (hinj : Function.Injective fun k => (σ k : ℕ))
    {w : ℕ} (hw : ∀ k, ¬(σ k : ℕ) ∣ w) (hle : ∑ g, markCount 𝔊 C g ≤ 𝔊.totalHits w) :
    targetNorm (groupFamily 𝔊) 1 C *
        damping intPos (groupFamily 𝔊) J 1 q₀ ((shProd σ * w : ℕ) : ℤ) ^ 2 =
      activeCoeff 𝔊 q₀ (markCount 𝔊 C) w := by
  have hω := omegaOf_mul h𝔊 σ hinj hw
  have hcount := card_shIdx_add (𝔊 := 𝔊) C
  have hgc : groupCount (Fin 𝔊.numSmall) (Fin 𝔊.numBig) = 𝔊.numSmall + 𝔊.numBig := by
    unfold groupCount
    rw [Fintype.card_fin, Fintype.card_fin]
  have hexp : (((groupFamily 𝔊).omegaOf
        (fun p => intPos.hit p ((shProd σ * w : ℕ) : ℤ)) : ℕ) : ℝ) -
        ((J + 1 : ℕ) : ℝ) * ((groupCount (Fin 𝔊.numSmall) (Fin 𝔊.numBig) : ℕ) : ℝ) =
      ((𝔊.totalHits w - ∑ g, markCount 𝔊 C g : ℕ) : ℝ) := by
    have h2 : ((Fintype.card (ShIdx 𝔊 C) : ℕ) : ℝ) + ((∑ g, markCount 𝔊 C g : ℕ) : ℝ) =
        ((J + 1 : ℕ) : ℝ) * ((𝔊.numSmall + 𝔊.numBig : ℕ) : ℝ) := by
      exact_mod_cast hcount
    rw [hω, hgc, Nat.cast_sub hle, Nat.cast_add]
    linarith
  have hd : damping intPos (groupFamily 𝔊) J 1 q₀ ((shProd σ * w : ℕ) : ℤ) ^ 2 =
      q₀ ^ (𝔊.totalHits w - ∑ g, markCount 𝔊 C g) := by
    unfold damping
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le, Nat.cast_ofNat,
      div_mul_cancel₀ _ (two_ne_zero), hexp, Real.rpow_natCast]
  rw [hd, targetNorm_eq_prod]
  unfold activeCoeff
  ring

end Weights

end Strip

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
