module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.CleanNorm.Coef
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.EdgeAbsCol
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Lemma 3.10: the clean part of an edge between the symmetrizations

Source: `verification/stage7-sources/S-02.tex`, lines 896–1041 (`[S-02:0896–1041]`), in particular
the conditioned form [S-02:0954–0963] and the conclusion [S-02:1013–1017]:

"The clean bilinear form is now exactly `∑_𝐝 ⟨P_𝐝 w₁, 𝒯'_𝐝 P_𝐝 w₂⟩`. … Cauchy--Schwarz in `𝐝`
and (eq:small-map-norm) therefore give the clean bound."

The clean part `ℰ_{i,clean}` is the clean row transition between two symmetrizations in all
active lists (`edgeClean_eq_sym`). The symmetrization in the big lists alone is absorbed by the
symmetrization in all lists (`clean_memSym_symB`, `clean_symB_memSym`), and between two
symmetrizations in the big lists the clean row transition is the conditioned operator of
`Cond.lean` (`clean_symB_row_symB`), with the operators

`𝒯_{d'} = bigSym ∘ (translation-covariant big-list operator for d') ∘ bigSym`

between the conditioning maps (`cleanT`). The Fourier reduction of `Transfer.lean` bounds `𝒯_{d'}`
by the fibre operators (`cleanT_bound`), and `cleanCondOp_bound` gives

* `edgeClean_bound` — `‖ℰ_{i,clean}(θ) F‖ ≤ K_𝒮 C_T ‖F‖` on `L²` of the measure of `ℋ`, for all
  functions `F`, if all the fibre operators have norm at most `C_T` between the two big-list
  symmetrizations.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators ComplexConjugate

noncomputable section

/-- A constant factor inside an average. -/
theorem clean_avg_mul {ι : Type*} [Fintype ι] (c u : ℂ) (X : ι → ℂ) :
    c * ∑ τ, u * X τ = u * (c * ∑ τ, X τ) := by
  rw [← Finset.mul_sum]
  exact mul_left_comm _ _ _

section Sym

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {N : Type}

/-- The symmetrization in all active lists, pointwise. -/
theorem clean_memSym_apply (H : MState 𝒢 J ℓ Bc → ℂ) (s : MState 𝒢 J ℓ Bc) :
    memSym 𝒢 J ℓ Bc H s =
      ∑ π : ListPerms S B J ℓ,
        (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ * H (s.permLists π) := rfl

/-- **The symmetrization in all active lists is a contraction** of `L²` of the measure of `ℋ`
("the two list symmetrizations have norm at most one" [S-02:0806–0807]). -/
theorem clean_memSym_le {q : ℝ} {n : ℕ}
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p) (H : MState 𝒢 J ℓ Bc → ℂ) :
    wNorm (memWeight 𝒢 q n) (memSym 𝒢 J ℓ Bc H) ≤ wNorm (memWeight 𝒢 q n) H := by
  have : Nonempty (ListPerms S B J ℓ) :=
    ⟨((1 : SlotPerms S J ℓ), (1 : SlotPerms B J ℓ))⟩
  have h : memSym 𝒢 J ℓ Bc H = fun s : MState 𝒢 J ℓ Bc =>
      (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ *
        ∑ π : ListPerms S B J ℓ, H (l38_permListsEquiv π s) := by
    funext s
    show memSym 𝒢 J ℓ Bc H s = (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ *
      ∑ π : ListPerms S B J ℓ, H (s.permLists π)
    rw [clean_memSym_apply, Finset.mul_sum]
  rw [h]
  exact clean_wNorm_avg_le (memWeight_nonneg 𝒢 q n hν) (fun π => l38_permListsEquiv π)
    (fun π s => l38_memWeight_permLists q n π s) H

/-- Right multiplication of the permutations of the big slots, as a bijection of the slot
permutations of all active lists. -/
def cleanMulRight (τ : SlotPerms B J ℓ) : ListPerms S B J ℓ ≃ ListPerms S B J ℓ where
  toFun π := (π.1, π.2 * τ)
  invFun π := (π.1, π.2 * τ⁻¹)
  left_inv π := Prod.ext rfl (mul_inv_cancel_right π.2 τ)
  right_inv π := Prod.ext rfl (inv_mul_cancel_right π.2 τ)

/-- Left multiplication of the permutations of the big slots, as a bijection of the slot
permutations of all active lists. -/
def cleanMulLeft (τ : SlotPerms B J ℓ) : ListPerms S B J ℓ ≃ ListPerms S B J ℓ where
  toFun π := (π.1, τ * π.2)
  invFun π := (π.1, τ⁻¹ * π.2)
  left_inv π := Prod.ext rfl (inv_mul_cancel_left τ π.2)
  right_inv π := Prod.ext rfl (mul_inv_cancel_left τ π.2)

/-- **Symmetrization in the big active lists only**: the average over the slot permutations of
the big groups [S-02:0072–0075], on the memory states. -/
def cleanSymB (H : MState 𝒢 J ℓ Bc → ℂ) : MState 𝒢 J ℓ Bc → ℂ :=
  fun s => (Fintype.card (SlotPerms B J ℓ) : ℂ)⁻¹ *
    ∑ τ : SlotPerms B J ℓ, H (s.permLists ((1 : SlotPerms S J ℓ), τ))

/-- The symmetrization in all active lists absorbs the symmetrization in the big lists, on the
right. -/
theorem clean_memSym_symB (H : MState 𝒢 J ℓ Bc → ℂ) :
    memSym 𝒢 J ℓ Bc (cleanSymB H) = memSym 𝒢 J ℓ Bc H := by
  funext s
  have hcard : (Fintype.card (SlotPerms B J ℓ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hτ : ∀ τ : SlotPerms B J ℓ,
      ∑ π : ListPerms S B J ℓ, (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ *
          H ((s.permLists π).permLists ((1 : SlotPerms S J ℓ), τ)) =
        memSym 𝒢 J ℓ Bc H s := by
    intro τ
    rw [clean_memSym_apply]
    exact Fintype.sum_equiv (cleanMulRight τ) _ _ fun π => rfl
  calc memSym 𝒢 J ℓ Bc (cleanSymB H) s
      = ∑ π : ListPerms S B J ℓ, (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ *
          ((Fintype.card (SlotPerms B J ℓ) : ℂ)⁻¹ * ∑ τ : SlotPerms B J ℓ,
            H ((s.permLists π).permLists ((1 : SlotPerms S J ℓ), τ))) := rfl
    _ = ∑ π : ListPerms S B J ℓ, ∑ τ : SlotPerms B J ℓ,
          (Fintype.card (SlotPerms B J ℓ) : ℂ)⁻¹ *
            ((Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ *
              H ((s.permLists π).permLists ((1 : SlotPerms S J ℓ), τ))) := by
        refine Finset.sum_congr rfl fun π _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        exact mul_left_comm _ _ _
    _ = ∑ τ : SlotPerms B J ℓ, ∑ π : ListPerms S B J ℓ,
          (Fintype.card (SlotPerms B J ℓ) : ℂ)⁻¹ *
            ((Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ *
              H ((s.permLists π).permLists ((1 : SlotPerms S J ℓ), τ))) := Finset.sum_comm
    _ = ∑ _τ : SlotPerms B J ℓ,
          (Fintype.card (SlotPerms B J ℓ) : ℂ)⁻¹ * memSym 𝒢 J ℓ Bc H s := by
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [← Finset.mul_sum, hτ τ]
    _ = memSym 𝒢 J ℓ Bc H s := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel_left₀ hcard]

/-- The symmetrization in all active lists absorbs the symmetrization in the big lists, on the
left. -/
theorem clean_symB_memSym (F : MState 𝒢 J ℓ Bc → ℂ) :
    cleanSymB (memSym 𝒢 J ℓ Bc F) = memSym 𝒢 J ℓ Bc F := by
  funext s
  have hcard : (Fintype.card (SlotPerms B J ℓ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hτ : ∀ τ : SlotPerms B J ℓ,
      memSym 𝒢 J ℓ Bc F (s.permLists ((1 : SlotPerms S J ℓ), τ)) = memSym 𝒢 J ℓ Bc F s := by
    intro τ
    rw [clean_memSym_apply, clean_memSym_apply]
    exact Fintype.sum_equiv (cleanMulLeft τ) _ _ fun π => rfl
  calc cleanSymB (memSym 𝒢 J ℓ Bc F) s
      = (Fintype.card (SlotPerms B J ℓ) : ℂ)⁻¹ * ∑ τ : SlotPerms B J ℓ,
          memSym 𝒢 J ℓ Bc F (s.permLists ((1 : SlotPerms S J ℓ), τ)) := rfl
    _ = (Fintype.card (SlotPerms B J ℓ) : ℂ)⁻¹ * ∑ _τ : SlotPerms B J ℓ,
          memSym 𝒢 J ℓ Bc F s :=
        congrArg (fun t : ℂ => (Fintype.card (SlotPerms B J ℓ) : ℂ)⁻¹ * t)
          (Finset.sum_congr rfl fun τ _ => hτ τ)
    _ = memSym 𝒢 J ℓ Bc F s := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, inv_mul_cancel_left₀ hcard]

/-- **The conditioning map commutes with the symmetrization in the big lists.** -/
theorem cleanQ_symB (q ρ : ℝ) (a : CleanShared 𝒢 J) (G : MState 𝒢 J ℓ Bc → ℂ) :
    cleanQ q ρ a (cleanSymB G) = cleanLiftX (bigSym 𝒢.big J ℓ) (cleanQ q ρ a G) := by
  funext w
  have hR : cleanLiftX (bigSym 𝒢.big J ℓ) (cleanQ q ρ a G) w =
      (Fintype.card (SlotPerms B J ℓ) : ℂ)⁻¹ * ∑ τ : SlotPerms B J ℓ,
        ∑ xs : LabelList 𝒢.small J ℓ,
          ((cleanSmallW q a w.1.1 xs * ρ ^ cleanMemZeros w.1.2 : ℝ) : ℂ) *
            G (cleanMk (w.1, permuteSlots τ w.2) xs) :=
    bigSym_apply (fun x : LabelList 𝒢.big J ℓ => cleanQ q ρ a G (w.1, x)) w.2
  have hL : cleanQ q ρ a (cleanSymB G) w =
      ∑ xs : LabelList 𝒢.small J ℓ,
        ((cleanSmallW q a w.1.1 xs * ρ ^ cleanMemZeros w.1.2 : ℝ) : ℂ) *
          ((Fintype.card (SlotPerms B J ℓ) : ℂ)⁻¹ * ∑ τ : SlotPerms B J ℓ,
            G (cleanMk (w.1, permuteSlots τ w.2) xs)) := rfl
  rw [hL, hR, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun xs _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  exact mul_left_comm _ _ _

omit [DecidableEq S] [DecidableEq B] in
/-- The measure of the small residues and of the memories is nonnegative. -/
theorem cleanYW_nonneg {q : ℝ} {n : ℕ}
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) q n p) (J : ℕ) (yy : CleanY 𝒢 Bc) :
    0 ≤ cleanYW 𝒢 J q n yy :=
  mul_nonneg (mul_nonneg
    (Finset.prod_nonneg fun _ _ => inv_nonneg.mpr (pow_nonneg (Schur.reciprocalMass_nonneg _) _))
    (inv_nonneg.mpr (Nat.cast_nonneg _))) (clean_memMass_nonneg hν _)

variable [Fintype N]

open _root_.Classical in
/-- **`ℰ_{i,clean}` is the clean row transition between two symmetrizations** in all active
lists [S-02:0477–0480, 0826–0833]. -/
theorem edgeClean_eq_sym (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) (F : MState 𝒢 J ℓ Bc → ℂ) :
    edgeClean D Bc θ i F =
      memSym 𝒢 J ℓ Bc (cleanRow D Bc θ i (memSym 𝒢 J ℓ Bc F)) := by
  funext s
  have hL : edgeClean D Bc θ i F s =
      ∑ π : ListPerms S B J ℓ, ∑ c : EdgeChoice 𝒢 D.fam Bc, ∑ π' : ListPerms S B J ℓ,
        (if IsClean c then edgeFullCoef D (fun _ => 1) θ i s (π, c, π') else 0) *
          F (edgeFullTgt D i s (π, c, π')) := by
    have h0 : edgeClean D Bc θ i F s =
        ∑ ξ : EdgeFullChoice D Bc,
          (if IsClean ξ.2.1 then edgeFullCoef D (fun _ => 1) θ i s ξ else 0) *
            F (edgeFullTgt D i s ξ) := rfl
    rw [h0]
    refine (Fintype.sum_prod_type _).trans (Finset.sum_congr rfl fun π _ => ?_)
    exact Fintype.sum_prod_type _
  have hR : memSym 𝒢 J ℓ Bc (cleanRow D Bc θ i (memSym 𝒢 J ℓ Bc F)) s =
      ∑ π : ListPerms S B J ℓ, ∑ c : EdgeChoice 𝒢 D.fam Bc, ∑ π' : ListPerms S B J ℓ,
        (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ *
          ((if IsClean c then edgeCoef D θ i (s.permLists π) c else 0) *
            ((Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ *
              F ((edgeTgt D i (s.permLists π) c).permLists π'))) := by
    rw [clean_memSym_apply]
    refine Finset.sum_congr rfl fun π _ => ?_
    have h1 : cleanRow D Bc θ i (memSym 𝒢 J ℓ Bc F) (s.permLists π) =
        ∑ c : EdgeChoice 𝒢 D.fam Bc,
          (if IsClean c then edgeCoef D θ i (s.permLists π) c else 0) *
            memSym 𝒢 J ℓ Bc F (edgeTgt D i (s.permLists π) c) := rfl
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [clean_memSym_apply, Finset.mul_sum, Finset.mul_sum]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun c _ =>
    Finset.sum_congr rfl fun π' _ => ?_
  have ht : edgeFullTgt D i s (π, c, π') = (edgeTgt D i (s.permLists π) c).permLists π' := rfl
  have hc : edgeFullCoef D (fun _ => 1) θ i s (π, c, π') =
      (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ * (1 * edgeCoef D θ i (s.permLists π) c) *
        (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ := rfl
  rw [ht, hc]
  by_cases hcl : IsClean c
  · rw [if_pos hcl, if_pos hcl]
    ring
  · rw [if_neg hcl, if_neg hcl, zero_mul, zero_mul, mul_zero]

/-- **The operator between the conditioning maps** [S-02:0958–0963]: for the product `d` of the
shared small labels, the translation-covariant big-list operator between two symmetrizations of
the big lists. "The operator between these maps uses the big-list transitions and translates all
unrestricted small and memory residues by `σ_i k d' D_ℬ`." -/
def cleanT (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ) (i d : ℕ) (H : CleanW 𝒢 J ℓ Bc → ℂ) :
    CleanW 𝒢 J ℓ Bc → ℂ :=
  cleanLiftX (bigSym 𝒢.big J ℓ)
    (cleanCovOp (cleanSh (𝒢 := 𝒢) (Bc := Bc)) (cleanKappa D i d) (cleanStep D i d)
      (cleanTau D) θ (cleanLiftX (bigSym 𝒢.big J ℓ) H))

/-- **The clean row transition between two symmetrizations of the big lists is the conditioned
operator** (eq:clean-conditioned-form) [S-02:0954–0963]. -/
theorem clean_symB_row_symB (hdisj : ∀ g g', Disjoint (𝒢.small g) (𝒢.big g'))
    (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) (G : MState 𝒢 J ℓ Bc → ℂ) :
    cleanSymB (cleanRow D Bc θ i (cleanSymB G)) =
      cleanCondOp D.q D.ρ (cleanT D Bc θ i) G := by
  funext s
  have hτ : ∀ τ : SlotPerms B J ℓ,
      cleanRow D Bc θ i (cleanSymB G) (s.permLists ((1 : SlotPerms S J ℓ), τ)) =
        ((cleanU D.q D.ρ s : ℝ) : ℂ) *
          cleanCovOp (cleanSh (𝒢 := 𝒢) (Bc := Bc)) (cleanKappa D i (cleanD (cleanCls s.xs)))
            (cleanStep D i (cleanD (cleanCls s.xs))) (cleanTau D) θ
            (cleanLiftX (bigSym 𝒢.big J ℓ) (cleanQ D.q D.ρ (cleanCls s.xs) G))
            ((s.y, s.mem), permuteSlots τ s.xb) := by
    intro τ
    rw [← cleanQ_symB]
    exact cleanRow_apply hdisj D θ i (cleanSymB G) (s.permLists ((1 : SlotPerms S J ℓ), τ))
  have hR : cleanCondOp D.q D.ρ (cleanT D Bc θ i) G s =
      ((cleanU D.q D.ρ s : ℝ) : ℂ) *
        ((Fintype.card (SlotPerms B J ℓ) : ℂ)⁻¹ * ∑ τ : SlotPerms B J ℓ,
          cleanCovOp (cleanSh (𝒢 := 𝒢) (Bc := Bc)) (cleanKappa D i (cleanD (cleanCls s.xs)))
            (cleanStep D i (cleanD (cleanCls s.xs))) (cleanTau D) θ
            (cleanLiftX (bigSym 𝒢.big J ℓ) (cleanQ D.q D.ρ (cleanCls s.xs) G))
            ((s.y, s.mem), permuteSlots τ s.xb)) :=
    congrArg (fun t : ℂ => ((cleanU D.q D.ρ s : ℝ) : ℂ) * t)
      (bigSym_apply
        (fun x : LabelList 𝒢.big J ℓ =>
          cleanCovOp (cleanSh (𝒢 := 𝒢) (Bc := Bc)) (cleanKappa D i (cleanD (cleanCls s.xs)))
            (cleanStep D i (cleanD (cleanCls s.xs))) (cleanTau D) θ
            (cleanLiftX (bigSym 𝒢.big J ℓ) (cleanQ D.q D.ρ (cleanCls s.xs) G))
            ((s.y, s.mem), x)) s.xb)
  rw [hR]
  show (Fintype.card (SlotPerms B J ℓ) : ℂ)⁻¹ * ∑ τ : SlotPerms B J ℓ,
      cleanRow D Bc θ i (cleanSymB G) (s.permLists ((1 : SlotPerms S J ℓ), τ)) = _
  rw [Finset.sum_congr rfl fun τ _ => hτ τ]
  exact clean_avg_mul _ _ _

omit [DecidableEq S] in
/-- **The Fourier reduction for the operator between the conditioning maps**
[S-02:0964–0980]: if every fibre operator has norm at most `C_T` between two symmetrizations of
the big lists, on `L²` of the measure of the big active lists, then so has `𝒯_{d'}` on `L²` of the
product with the measure of the small residues and of the memories. -/
theorem cleanT_bound (D : MemData 𝒢 J ℓ N)
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p) {CT : ℝ} (hCT : 0 ≤ CT)
    (i d : ℕ)
    (hfib : ∀ (Θ : ℝ) (g : LabelList 𝒢.big J ℓ → ℂ),
      wNorm (bigListMass 𝒢 D.q D.n)
          (bigSym 𝒢.big J ℓ (cleanFibOp (cleanKappa D i d) (cleanStep D i d) (cleanTau D) Θ
            (bigSym 𝒢.big J ℓ g))) ≤ CT * wNorm (bigListMass 𝒢 D.q D.n) g)
    (θ : ℝ) (H : CleanW 𝒢 J ℓ Bc → ℂ) :
    wNorm (fun w : CleanW 𝒢 J ℓ Bc => cleanYW 𝒢 J D.q D.n w.1 * bigListMass 𝒢 D.q D.n w.2)
        (cleanT D Bc θ i d H) ≤
      CT * wNorm (fun w : CleanW 𝒢 J ℓ Bc =>
        cleanYW 𝒢 J D.q D.n w.1 * bigListMass 𝒢 D.q D.n w.2) H :=
  clean_transfer (cleanSh (𝒢 := 𝒢) (Bc := Bc)) cleanSh_zero cleanSh_add (cleanPeriod 𝒢)
    (cleanPeriod_pos 𝒢) cleanSh_period (cleanYW 𝒢 J D.q D.n) (cleanYW_nonneg hν J)
    (cleanYW_cleanSh J D.q D.n) (bigListMass 𝒢 D.q D.n) (clean_bigListMass_nonneg hν)
    (cleanKappa D i d) (cleanStep D i d) (cleanTau D) (bigSym 𝒢.big J ℓ) (bigSym 𝒢.big J ℓ)
    hCT hfib θ H

/-- **The clean bound from the fibre bound** [S-02:1013–1017]: "Cauchy--Schwarz in `𝐝` and
(eq:small-map-norm) therefore give the clean bound". If the small states with given shared labels
have total weight at most `K_𝒮`, and all the fibre operators have norm at most `C_T` between two
symmetrizations of the big lists, then `‖ℰ_{i,clean}(θ) F‖ ≤ K_𝒮 C_T ‖F‖` for every function `F`
on the memory states. -/
theorem edgeClean_bound (hdisj : ∀ g g', Disjoint (𝒢.small g) (𝒢.big g'))
    (D : MemData 𝒢 J ℓ N) (hq0 : 0 < D.q) (hq1 : D.q < 1) (hρ0 : 0 < D.ρ) (hρ1 : D.ρ ≤ 1)
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p) {KS CT : ℝ} (hKS0 : 0 ≤ KS)
    (hKS : ∀ (a : CleanShared 𝒢 J) (y : ResVec (smallPrimes 𝒢)),
      ∑ xs : LabelList 𝒢.small J ℓ, cleanSmallW D.q a y xs ≤ KS)
    (hCT : 0 ≤ CT) (i : ℕ)
    (hfib : ∀ (d : ℕ) (Θ : ℝ) (g : LabelList 𝒢.big J ℓ → ℂ),
      wNorm (bigListMass 𝒢 D.q D.n)
          (bigSym 𝒢.big J ℓ (cleanFibOp (cleanKappa D i d) (cleanStep D i d) (cleanTau D) Θ
            (bigSym 𝒢.big J ℓ g))) ≤ CT * wNorm (bigListMass 𝒢 D.q D.n) g)
    (θ : ℝ) (F : MState 𝒢 J ℓ Bc → ℂ) :
    wNorm (memWeight 𝒢 D.q D.n) (edgeClean D Bc θ i F) ≤
      KS * CT * wNorm (memWeight 𝒢 D.q D.n) F := by
  have h1 : wNorm (memWeight 𝒢 D.q D.n)
        (cleanCondOp D.q D.ρ (cleanT D Bc θ i) (memSym 𝒢 J ℓ Bc F)) ≤
      KS * CT * wNorm (memWeight 𝒢 D.q D.n) (memSym 𝒢 J ℓ Bc F) :=
    cleanCondOp_bound hq0 hq1 hρ0 hρ1 hν hKS0 hKS hCT (cleanT D Bc θ i)
      (fun d H => cleanT_bound D hν hCT i d (hfib d) θ H) (memSym 𝒢 J ℓ Bc F)
  have e : edgeClean D Bc θ i F =
      memSym 𝒢 J ℓ Bc (cleanCondOp D.q D.ρ (cleanT D Bc θ i) (memSym 𝒢 J ℓ Bc F)) := by
    rw [edgeClean_eq_sym, ← clean_memSym_symB (cleanRow D Bc θ i (memSym 𝒢 J ℓ Bc F)),
      ← clean_symB_row_symB hdisj D θ i (memSym 𝒢 J ℓ Bc F), clean_symB_memSym]
  rw [e]
  calc wNorm (memWeight 𝒢 D.q D.n)
        (memSym 𝒢 J ℓ Bc (cleanCondOp D.q D.ρ (cleanT D Bc θ i) (memSym 𝒢 J ℓ Bc F)))
      ≤ wNorm (memWeight 𝒢 D.q D.n)
          (cleanCondOp D.q D.ρ (cleanT D Bc θ i) (memSym 𝒢 J ℓ Bc F)) :=
        clean_memSym_le hν _
    _ ≤ KS * CT * wNorm (memWeight 𝒢 D.q D.n) (memSym 𝒢 J ℓ Bc F) := h1
    _ ≤ KS * CT * wNorm (memWeight 𝒢 D.q D.n) F :=
        mul_le_mul_of_nonneg_left (clean_memSym_le hν F) (mul_nonneg hKS0 hCT)

end Sym

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
