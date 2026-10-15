module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResidueSumVisit
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResidueActive
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The summation over paths, part 5: the absolute mass of all paths

Source: `verification/stage7-sources/S-02.tex`, lines 293–307 (`[S-02:0293–0307]`).

"This replacement may be summed over paths with absolute coefficients. Indeed retain the full
vector of residues as a position, with its Haar probability measure, and translate it by
`σ_i k D_i` on an edge. The expected total mass of all initial lists is at most one
(eq:initial-factorial-mass). By Lemma 3.4, the absolute mass of all length `N` paths, even
without a return condition, is `L^{O(N)}`."

* `physAbsOp_eq_rowOp`, `physAbsAdj_eq_rowOp`, `sum_norm_physFwdCoef`, `sum_norm_physBwdCoef` —
  the operator of Lemma 3.4 is the row operator of the forward edges with the moduli of their
  coefficients, so the moduli of the coefficients of the forward
  (backward) edges from a state sum to `physAbsRowSum` (`physAbsColSum`), the row sums of
  Lemma 3.4.
* `sum_norm_physRoundCoef_le`, `sum_norm_walkCoef_round_le` — hence the moduli of the coefficients
  of all walks of `R` rounds from a state sum to at most `(ρ₁ ρ₂)^R`, if `ρ₁` and `ρ₂` bound the
  row sums at all states.
* `resAvg_sum`, `resAvg_const_mul` — linearity of the expectation.
* `sum_labelList_prod_inv`, `resAvg_isPhys_le`, `resAvg_initial_mass_le_one` —
  **(eq:initial-factorial-mass)**: under independent uniform residues, the expected total mass of
  the physical lists at the start is at most one.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResSum

open scoped BigOperators ComplexConjugate

noncomputable section

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

/-! ### The row sums of Lemma 3.4 -/

section RowSums

variable (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ} {N : Type} [Fintype N]

/-- The operator of Lemma 3.4 (absolute coefficients "before adding patterns or averaging
permutations") is the row operator of the forward edges with the moduli of their coefficients. -/
theorem physAbsOp_eq_rowOp (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) :
    physAbsOp 𝔭 𝒢 q 𝔉 k ζ =
      rowOp (fun s ξ => ((‖physFwdCoef 𝔭 𝒢 q 𝔉 k ζ s ξ‖ : ℝ) : ℂ)) (physFwdTgt 𝔭 𝒢 𝔉 k) := by
  refine LinearMap.ext fun G => funext fun s => ?_
  simp only [physAbsOp, physSym, physRowAbs, physFwdCoef, physFwdTgt, LinearMap.comp_apply,
    LinearMap.sum_apply, Finset.sum_apply, rowOp_apply, Fintype.sum_prod_type,
    Fintype.sum_sigma, Finset.mul_sum]
  refine Finset.sum_congr rfl fun π₁ _ => Finset.sum_congr rfl fun π₂ _ =>
    Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun r _ =>
    Finset.sum_congr rfl fun x₁ _ => Finset.sum_congr rfl fun x₂ _ =>
    Finset.sum_congr rfl fun π₁' _ => Finset.sum_congr rfl fun π₂' _ => ?_
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast]
  push_cast
  ring

/-- The adjoint of the operator of Lemma 3.4 is the row operator of the backward edges with the
moduli of their coefficients. -/
theorem physAbsAdj_eq_rowOp (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) :
    physAbsAdj 𝔭 𝒢 q 𝔉 k ζ =
      rowOp (fun s ξ => ((‖physBwdCoef 𝔭 𝒢 q 𝔉 k ζ s ξ‖ : ℝ) : ℂ)) (physBwdTgt 𝔭 𝒢 𝔉 k) := by
  refine LinearMap.ext fun G => funext fun s => ?_
  simp only [physAbsAdj, physSym, physRowAdjAbs, physBwdCoef, physBwdTgt, LinearMap.comp_apply,
    LinearMap.sum_apply, Finset.sum_apply, rowOp_apply, Fintype.sum_prod_type,
    Fintype.sum_sigma, Finset.mul_sum]
  refine Finset.sum_congr rfl fun π₁ _ => Finset.sum_congr rfl fun π₂ _ =>
    Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun r _ =>
    Finset.sum_congr rfl fun x₁ _ => Finset.sum_congr rfl fun x₂ _ =>
    Finset.sum_congr rfl fun π₁' _ => Finset.sum_congr rfl fun π₂' _ => ?_
  rw [norm_mul, norm_mul, norm_inv, Complex.norm_natCast, RCLike.norm_conj]
  push_cast
  ring

/-- **The moduli of the coefficients of the forward edges from a state sum to the row sum of
Lemma 3.4.** -/
theorem sum_norm_physFwdCoef (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    (s : PState 𝔭 𝒢 J ℓ) :
    ∑ ξ : PhysChoice 𝒢 𝔉, ‖physFwdCoef 𝔭 𝒢 q 𝔉 k ζ s ξ‖ = physAbsRowSum 𝔭 𝒢 q 𝔉 k ζ s := by
  unfold physAbsRowSum
  rw [physAbsOp_eq_rowOp, rowOp_apply]
  simp only [mul_one]
  rw [← Complex.ofReal_sum, Complex.ofReal_re]

/-- **The moduli of the coefficients of the backward edges from a state sum to the column sum of
Lemma 3.4.** -/
theorem sum_norm_physBwdCoef (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ)
    (s : PState 𝔭 𝒢 J ℓ) :
    ∑ ξ : PhysChoice 𝒢 𝔉, ‖physBwdCoef 𝔭 𝒢 q 𝔉 k ζ s ξ‖ = physAbsColSum 𝔭 𝒢 q 𝔉 k ζ s := by
  unfold physAbsColSum
  rw [physAbsAdj_eq_rowOp, rowOp_apply]
  simp only [mul_one]
  rw [← Complex.ofReal_sum, Complex.ofReal_re]

/-- The moduli of the coefficients of the rounds from a state sum to at most `ρ₁ ρ₂`, if `ρ₁`
bounds the row sums and `ρ₂` the column sums of Lemma 3.4 at all states. -/
theorem sum_norm_physRoundCoef_le (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) {ρ₁ ρ₂ : ℝ}
    (h1 : ∀ s, physAbsRowSum 𝔭 𝒢 q 𝔉 k ζ s ≤ ρ₁) (h2 : ∀ s, physAbsColSum 𝔭 𝒢 q 𝔉 k ζ s ≤ ρ₂)
    (s : PState 𝔭 𝒢 J ℓ) :
    ∑ ξ : PhysChoice 𝒢 𝔉 × PhysChoice 𝒢 𝔉, ‖physRoundCoef 𝔭 𝒢 q 𝔉 k ζ s ξ‖ ≤ ρ₁ * ρ₂ := by
  have hρ₂ : 0 ≤ ρ₂ := by
    have h := h2 s
    rw [← sum_norm_physBwdCoef] at h
    exact (Finset.sum_nonneg fun ξ _ => norm_nonneg _).trans h
  rw [Fintype.sum_prod_type]
  calc ∑ ξ₁ : PhysChoice 𝒢 𝔉, ∑ ξ₂ : PhysChoice 𝒢 𝔉,
        ‖physRoundCoef 𝔭 𝒢 q 𝔉 k ζ s (ξ₁, ξ₂)‖
      = ∑ ξ₁ : PhysChoice 𝒢 𝔉, ‖physFwdCoef 𝔭 𝒢 q 𝔉 k ζ s ξ₁‖ *
          ∑ ξ₂ : PhysChoice 𝒢 𝔉,
            ‖physBwdCoef 𝔭 𝒢 q 𝔉 k ζ (physFwdTgt 𝔭 𝒢 𝔉 k s ξ₁) ξ₂‖ := by
        refine Finset.sum_congr rfl fun ξ₁ _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun ξ₂ _ => ?_
        exact norm_mul _ _
    _ ≤ ∑ ξ₁ : PhysChoice 𝒢 𝔉, ‖physFwdCoef 𝔭 𝒢 q 𝔉 k ζ s ξ₁‖ * ρ₂ := by
        refine Finset.sum_le_sum fun ξ₁ _ => mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        rw [sum_norm_physBwdCoef]
        exact h2 _
    _ = (∑ ξ₁ : PhysChoice 𝒢 𝔉, ‖physFwdCoef 𝔭 𝒢 q 𝔉 k ζ s ξ₁‖) * ρ₂ := by
        rw [Finset.sum_mul]
    _ ≤ ρ₁ * ρ₂ := by
        refine mul_le_mul_of_nonneg_right ?_ hρ₂
        rw [sum_norm_physFwdCoef]
        exact h1 s

/-- **The absolute mass of all walks of `R` rounds from a state** [S-02:0303–0304]: at most
`(ρ₁ ρ₂)^R`, "even without a return condition". -/
theorem sum_norm_walkCoef_round_le (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) {ρ₁ ρ₂ : ℝ}
    (h1 : ∀ s, physAbsRowSum 𝔭 𝒢 q 𝔉 k ζ s ≤ ρ₁) (h2 : ∀ s, physAbsColSum 𝔭 𝒢 q 𝔉 k ζ s ≤ ρ₂)
    (R : ℕ) (s : PState 𝔭 𝒢 J ℓ) :
    ∑ w : Fin R → PhysChoice 𝒢 𝔉 × PhysChoice 𝒢 𝔉,
        ‖walkCoef (physRoundCoef 𝔭 𝒢 q 𝔉 k ζ) (physRoundTgt 𝔭 𝒢 𝔉 k) s (List.ofFn w)‖ ≤
      (ρ₁ * ρ₂) ^ R :=
  sum_norm_walkCoef_le _ _ (sum_norm_physRoundCoef_le 𝔭 𝒢 q 𝔉 k ζ h1 h2) R s

end RowSums

/-! ### Linearity of the expectation -/

theorem resAvg_sum {α : Type*} (Q : Finset ℕ) (t : Finset α) (f : α → ResVec Q → ℝ) :
    resAvg Q (fun y => ∑ a ∈ t, f a y) = ∑ a ∈ t, resAvg Q (f a) := by
  unfold resAvg
  rw [Finset.sum_comm, Finset.mul_sum]

theorem resAvg_const_mul (Q : Finset ℕ) (c : ℝ) (f : ResVec Q → ℝ) :
    resAvg Q (fun y => c * f y) = c * resAvg Q f := by
  unfold resAvg
  rw [← Finset.mul_sum]
  ring

/-! ### (eq:initial-factorial-mass) -/

/-- `∑ ∏ 1/p` over all label lists of a family is `∏_g V_g^M`. -/
theorem sum_labelList_prod_inv {ι : Type} [Fintype ι] [DecidableEq ι] (𝒬 : ι → Finset ℕ)
    (J ℓ : ℕ) :
    ∑ xs : LabelList 𝒬 J ℓ, ∏ g, ∏ i : Slot J ℓ, (1 / ((xs g i : ℕ) : ℝ)) =
      ∏ g, Graph.primeGroupReciprocalMass (𝒬 g) ^ (J + ℓ) := by
  have h1 : ∑ xs : LabelList 𝒬 J ℓ, ∏ g, ∏ i : Slot J ℓ, (1 / ((xs g i : ℕ) : ℝ)) =
      ∏ g : ι, ∑ w : Slot J ℓ → {p : ℕ // p ∈ 𝒬 g},
        ∏ i : Slot J ℓ, (1 / ((w i : ℕ) : ℝ)) :=
    (Fintype.prod_sum fun (g : ι) (w : Slot J ℓ → {p : ℕ // p ∈ 𝒬 g}) =>
      ∏ i : Slot J ℓ, (1 / ((w i : ℕ) : ℝ))).symm
  have h2 : ∀ g : ι, ∑ w : Slot J ℓ → {p : ℕ // p ∈ 𝒬 g},
      ∏ i : Slot J ℓ, (1 / ((w i : ℕ) : ℝ)) =
        Graph.primeGroupReciprocalMass (𝒬 g) ^ (J + ℓ) := by
    intro g
    have h3 : ∑ w : Slot J ℓ → {p : ℕ // p ∈ 𝒬 g},
        ∏ i : Slot J ℓ, (1 / ((w i : ℕ) : ℝ)) =
          ∏ _i : Slot J ℓ, ∑ p : {p : ℕ // p ∈ 𝒬 g}, (1 / ((p : ℕ) : ℝ)) :=
      (Fintype.prod_sum fun (_ : Slot J ℓ) (p : {p : ℕ // p ∈ 𝒬 g}) =>
        (1 / ((p : ℕ) : ℝ))).symm
    have h4 : ∑ p : {p : ℕ // p ∈ 𝒬 g}, (1 / ((p : ℕ) : ℝ)) =
        Graph.primeGroupReciprocalMass (𝒬 g) :=
      Finset.sum_coe_sort (𝒬 g) fun p => (1 / (p : ℝ))
    rw [h3, Finset.prod_const, Finset.card_univ, card_slot, h4]
  rw [h1]
  exact Finset.prod_congr rfl fun g _ => h2 g

section InitialMass

variable {𝒢 : GroupFamily S B} {J ℓ : ℕ}

open _root_.Classical in
omit [DecidableEq S] [DecidableEq B] in
/-- Under independent uniform residues, the probability that the lists `xs` are physical at the
start is at most the product of the reciprocals of their labels. -/
theorem resAvg_isPhys_le (hd : GroupsDisjoint 𝒢) (hpos : ∀ p ∈ 𝒢.allPrimes, 0 < p)
    (xs : Lists 𝒢 J ℓ) :
    resAvg 𝒢.allPrimes
        (fun y => if IsPhys (tagModel 𝒢.allPrimes) (tagStart y) xs then (1 : ℝ) else 0) ≤
      (∏ g, ∏ i : Slot J ℓ, (1 / ((xs.1 g i : ℕ) : ℝ))) *
        ∏ g, ∏ i : Slot J ℓ, (1 / ((xs.2 g i : ℕ) : ℝ)) := by
  by_cases hI : ListInj xs
  · have hfun : (fun y : ResVec 𝒢.allPrimes =>
          if IsPhys (tagModel 𝒢.allPrimes) (tagStart y) xs then (1 : ℝ) else 0) =
        fun y => ∏ p : {p : ℕ // p ∈ 𝒢.allPrimes},
          (if p.1 ∈ labelSet xs then (if y p = 0 then (1 : ℝ) else 0)
            else (if y p = 0 then 1 else 1)) := by
      funext y
      have hiff : IsPhys (tagModel 𝒢.allPrimes) (tagStart y) xs ↔
          ∀ p ∈ labelSet xs, ∃ hp : p ∈ 𝒢.allPrimes, y ⟨p, hp⟩ = 0 := by
        rw [isPhys_iff]
        exact ⟨fun h => h.2, fun h => ⟨hI, h⟩⟩
      have hv := ResRepl.visit_factor_eq (labelSet_subset xs) y (1 : ℝ)
        (inst := Classical.propDecidable _)
      rw [← hv, one_pow]
      by_cases h : IsPhys (tagModel 𝒢.allPrimes) (tagStart y) xs
      · rw [if_pos h, if_pos (hiff.mp h)]
      · rw [if_neg h, if_neg fun h' => h (hiff.mpr h')]
    have hfac : ∀ p : {p : ℕ // p ∈ 𝒢.allPrimes},
        (∑ u : Res p.1, (if p.1 ∈ labelSet xs then (if u = 0 then (1 : ℝ) else 0)
          else (if u = 0 then 1 else 1))) / ((p.1 - 1 + 1 : ℕ) : ℝ) =
        if p.1 ∈ labelSet xs then 1 / (p.1 : ℝ) else 1 := by
      intro p
      have hp1 : p.1 - 1 + 1 = p.1 := Nat.sub_add_cancel (hpos p.1 p.2)
      by_cases hp : p.1 ∈ labelSet xs
      · have hs : ∑ u : Res p.1, (if p.1 ∈ labelSet xs then (if u = 0 then (1 : ℝ) else 0)
            else (if u = 0 then 1 else 1)) = 1 := by
          simp [hp]
        rw [hs, if_pos hp, hp1]
      · have hs : ∑ u : Res p.1, (if p.1 ∈ labelSet xs then (if u = 0 then (1 : ℝ) else 0)
            else (if u = 0 then 1 else 1)) = ((p.1 - 1 + 1 : ℕ) : ℝ) := by
          simp [hp, ZMod.card]
        rw [hs, if_neg hp]
        exact div_self (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))
    rw [hfun]
    refine le_of_eq_of_le ((ResRepl.resAvg_prod 𝒢.allPrimes
      (fun (p : {p : ℕ // p ∈ 𝒢.allPrimes}) (u : Res p.1) =>
        if p.1 ∈ labelSet xs then (if u = 0 then (1 : ℝ) else 0)
          else (if u = 0 then 1 else 1))).trans
      (Finset.prod_congr rfl fun p _ => hfac p)) ?_
    rw [Finset.prod_coe_sort 𝒢.allPrimes fun p => if p ∈ labelSet xs then 1 / (p : ℝ) else 1,
      Finset.prod_ite_mem, Finset.inter_eq_right.mpr (labelSet_subset xs)]
    unfold labelSet
    rw [Finset.prod_image fun a _ b _ h => labOf_injective hd hI h, Fintype.prod_sum_type,
      Fintype.prod_prod_type, Fintype.prod_prod_type]
    exact le_rfl
  · have hfun : (fun y : ResVec 𝒢.allPrimes =>
          if IsPhys (tagModel 𝒢.allPrimes) (tagStart y) xs then (1 : ℝ) else 0) =
        fun _ => (0 : ℝ) := by
      funext y
      exact if_neg fun h => hI ((isPhys_iff _ _ _).mp h).1
    rw [hfun, resAvg_const]
    exact mul_nonneg
      (Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun i _ =>
        div_nonneg zero_le_one (Nat.cast_nonneg _))
      (Finset.prod_nonneg fun g _ => Finset.prod_nonneg fun i _ =>
        div_nonneg zero_le_one (Nat.cast_nonneg _))

open _root_.Classical in
/-- **(eq:initial-factorial-mass)** [S-02:0296–0302]: "the expected total mass of all initial
lists is at most one". -/
theorem resAvg_initial_mass_le_one (hd : GroupsDisjoint 𝒢) (hpos : ∀ p ∈ 𝒢.allPrimes, 0 < p)
    (hVS : ∀ g, 0 < Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, 0 < Graph.primeGroupReciprocalMass (𝒢.big g)) (J ℓ : ℕ) :
    resAvg 𝒢.allPrimes (fun y => ∑ xs : Lists 𝒢 J ℓ,
      if IsPhys (tagModel 𝒢.allPrimes) (tagStart y) xs then stateMass 𝒢 J ℓ else 0) ≤ 1 := by
  have hmass0 : 0 ≤ stateMass 𝒢 J ℓ := by
    unfold stateMass
    exact mul_nonneg
      (Finset.prod_nonneg fun g _ => inv_nonneg.mpr (pow_nonneg (hVS g).le _))
      (Finset.prod_nonneg fun g _ => inv_nonneg.mpr (pow_nonneg (hVB g).le _))
  have hpt : (fun y : ResVec 𝒢.allPrimes => ∑ xs : Lists 𝒢 J ℓ,
        if IsPhys (tagModel 𝒢.allPrimes) (tagStart y) xs then stateMass 𝒢 J ℓ else 0) =
      fun y => ∑ xs : Lists 𝒢 J ℓ, stateMass 𝒢 J ℓ *
        (if IsPhys (tagModel 𝒢.allPrimes) (tagStart y) xs then (1 : ℝ) else 0) := by
    funext y
    refine Finset.sum_congr rfl fun xs _ => ?_
    split_ifs <;> simp
  rw [hpt, resAvg_sum]
  calc ∑ xs : Lists 𝒢 J ℓ, resAvg 𝒢.allPrimes (fun y => stateMass 𝒢 J ℓ *
        (if IsPhys (tagModel 𝒢.allPrimes) (tagStart y) xs then (1 : ℝ) else 0))
      = ∑ xs : Lists 𝒢 J ℓ, stateMass 𝒢 J ℓ * resAvg 𝒢.allPrimes
          (fun y => if IsPhys (tagModel 𝒢.allPrimes) (tagStart y) xs then (1 : ℝ) else 0) :=
        Finset.sum_congr rfl fun xs _ => resAvg_const_mul _ _ _
    _ ≤ ∑ xs : Lists 𝒢 J ℓ, stateMass 𝒢 J ℓ *
          ((∏ g, ∏ i : Slot J ℓ, (1 / ((xs.1 g i : ℕ) : ℝ))) *
            ∏ g, ∏ i : Slot J ℓ, (1 / ((xs.2 g i : ℕ) : ℝ))) :=
        Finset.sum_le_sum fun xs _ =>
          mul_le_mul_of_nonneg_left (resAvg_isPhys_le hd hpos xs) hmass0
    _ = stateMass 𝒢 J ℓ * ((∏ g, Graph.primeGroupReciprocalMass (𝒢.small g) ^ (J + ℓ)) *
          ∏ g, Graph.primeGroupReciprocalMass (𝒢.big g) ^ (J + ℓ)) := by
        rw [← Finset.mul_sum, Fintype.sum_prod_type]
        dsimp only
        rw [← Finset.sum_mul_sum, sum_labelList_prod_inv, sum_labelList_prod_inv]
    _ = 1 := by
        unfold stateMass
        rw [mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
          Finset.prod_eq_one fun g _ => inv_mul_cancel₀ (pow_ne_zero _ (hVS g).ne'),
          Finset.prod_eq_one fun g _ => inv_mul_cancel₀ (pow_ne_zero _ (hVB g).ne'), one_mul]

end InitialMass

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResSum
