module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.ResidueSplit
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Memory.BigDampingFactor
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# One edge of a physical path: the symmetric form of the coefficient and its two halves

Source: `verification/stage7-sources/S-02.tex`, lines 105–130 and 212–234
(`[S-02:0105–0130, 0212–0234]`).

Tools for `PhaseSkeletonProof.lean` (part (A) of the proof of [S] Lemma 3.7). Nothing here
involves a skeleton.

* `symCoef` — the coefficient of a row transition between two positions `m`, `m'`, with an
  arbitrary multiplier: the conditions and the real factors of `physCoef`, symmetric in the two
  endpoints.
* `physCoef_eq_symCoef` — a forward edge: `physCoef` is `symCoef` with the multiplier
  `K_ν D^{iζ}`.
* `phSkel_conj_physCoef_rev` — a backward edge: "the adjoint moves by `-kD`, interchanges source
  and target labels in the coefficient, and conjugates the multiplier" [S-02:0120–0121]; "the
  shared product and hence `D` are unchanged on reversal" [S-02:0122–0123].
* `symCoef_tag_split` — in the residue model, `symCoef` (times the phase of the edge) is the
  product of the factor of the small residues and the small lists (the common factor of the edge)
  and the factor of the big residues and the big lists.
* `phSkel_prod_fin_pairs`, `phSkel_pairWordEquiv` — `2R` edges are `R` rounds of a forward and a
  backward edge.
* `phSkel_expUnit_sum` — `e(∑ t_i) = ∏ e(t_i)`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ### `if … then … else …` with arbitrary decidability instances -/

/-- The conjugate of an `if` whose value is a real number times a complex number. -/
theorem phSkel_conj_ite {A B : Prop} {hA : Decidable A} {hB : Decidable B} (hAB : A ↔ B)
    (R R' : ℝ) (Z : ℂ) (hR : R = R') :
    conj (@ite ℂ A hA ((R : ℂ) * Z) 0) = @ite ℂ B hB ((R' : ℂ) * conj Z) 0 := by
  subst hR
  by_cases h : A
  · rw [if_pos h, if_pos (hAB.mp h), map_mul, Complex.conj_ofReal]
  · rw [if_neg h, if_neg (fun hb => h (hAB.mpr hb)), map_zero]

/-- An `if` over a conjunction, times a factor, is the product of the `if`s of the two halves. -/
theorem phSkel_ite_split {P₀ Q P : Prop} {h₀ : Decidable P₀} {hQ : Decidable Q}
    {hP : Decidable P} (X Y E : ℂ) (Z : ℝ) (hiff : P₀ ↔ Q ∧ P) (hXY : X * E = Y * (Z : ℂ)) :
    (@ite ℂ P₀ h₀ X 0) * E = (@ite ℂ Q hQ Y 0) * (((@ite ℝ P hP Z 0 : ℝ)) : ℂ) := by
  by_cases hq : Q
  · by_cases hp : P
    · rw [if_pos (hiff.mpr ⟨hq, hp⟩), if_pos hq, if_pos hp]
      exact hXY
    · rw [if_neg (fun h => hp (hiff.mp h).2), if_neg hp, Complex.ofReal_zero,
        mul_zero, zero_mul]
  · rw [if_neg (fun h => hq (hiff.mp h).1), if_neg hq, zero_mul, zero_mul]

/-- A factor moves out of an `if` with default value `0`. -/
theorem phSkel_ite_mul {c : Prop} {hc : Decidable c} (a b : ℂ) :
    @ite ℂ c hc (a * b) 0 = @ite ℂ c hc a 0 * b := by
  by_cases h : c
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, zero_mul]

/-- An `if` with default value `0` and a factor move into a sum. -/
theorem phSkel_ite_mul_sum {ι : Type*} [Fintype ι] {c : Prop} {hc : Decidable c} (a : ℂ)
    (f : ι → ℂ) : @ite ℂ c hc (a * ∑ w, f w) 0 = ∑ w, @ite ℂ c hc (a * f w) 0 := by
  by_cases h : c
  · rw [if_pos h, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => (if_pos h).symm
  · rw [if_neg h]
    exact (Finset.sum_eq_zero fun w _ => if_neg h).symm

/-! ### The phase of a sum -/

/-- `e(∑ t_i) = ∏ e(t_i)`. -/
theorem phSkel_expUnit_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    expUnit (∑ i ∈ s, f i) = ∏ i ∈ s, expUnit (f i) := by
  have h : (2 * Real.pi * Complex.I * ((∑ i ∈ s, f i : ℝ) : ℂ)) =
      ∑ i ∈ s, 2 * Real.pi * Complex.I * ((f i : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Finset.mul_sum]
  unfold expUnit
  rw [h, Complex.exp_sum]

/-! ### Rounds and edges -/

/-- A product over `2R` consecutive indices is a product over `R` pairs. -/
theorem phSkel_prod_range_two_mul {M : Type*} [CommMonoid M] (F : ℕ → M) (R : ℕ) :
    ∏ i ∈ Finset.range (2 * R), F i = ∏ r ∈ Finset.range R, (F (2 * r) * F (2 * r + 1)) := by
  induction R with
  | zero => simp
  | succ R ih =>
    have e : 2 * (R + 1) = 2 * R + 1 + 1 := by omega
    rw [Finset.prod_range_succ _ R, ← ih, e, Finset.prod_range_succ, Finset.prod_range_succ,
      mul_assoc]

/-- **A product over `N = 2R` edges is a product over `R` rounds**: the edges `2r` and `2r + 1`
form the round `r`. -/
theorem phSkel_prod_fin_pairs {M : Type*} [CommMonoid M] {n R : ℕ} (hn : n = 2 * R)
    (c : Fin n → M) :
    ∏ i : Fin n, c i =
      ∏ r : Fin R, (c ⟨2 * r.val, by have := r.isLt; omega⟩ *
        c ⟨2 * r.val + 1, by have := r.isLt; omega⟩) := by
  subst hn
  rw [Finset.prod_fin_eq_prod_range c, phSkel_prod_range_two_mul,
    ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun r _ => ?_
  have hr := r.isLt
  rw [dif_pos (show 2 * r.val < 2 * R by omega),
    dif_pos (show 2 * r.val + 1 < 2 * R by omega)]

/-- **A word of `N = 2R` edges is a word of `R` rounds** (pairs of a forward and a backward
edge). -/
def phSkel_pairWordEquiv (α : Type*) {n R : ℕ} (hn : n = 2 * R) :
    (Fin n → α) ≃ (Fin R → α × α) where
  toFun e := fun r => (e ⟨2 * r.val, by have := r.isLt; omega⟩,
    e ⟨2 * r.val + 1, by have := r.isLt; omega⟩)
  invFun w := fun i =>
    if i.val % 2 = 0 then (w ⟨i.val / 2, by have := i.isLt; omega⟩).1
    else (w ⟨i.val / 2, by have := i.isLt; omega⟩).2
  left_inv e := by
    funext i
    show (if i.val % 2 = 0 then e ⟨2 * (i.val / 2), _⟩ else e ⟨2 * (i.val / 2) + 1, _⟩) = e i
    by_cases h : i.val % 2 = 0
    · rw [if_pos h]
      exact congrArg e (Fin.ext (show 2 * (i.val / 2) = i.val by omega))
    · rw [if_neg h]
      exact congrArg e (Fin.ext (show 2 * (i.val / 2) + 1 = i.val by omega))
  right_inv w := by
    funext r
    show ((if (2 * r.val) % 2 = 0 then (w ⟨2 * r.val / 2, _⟩).1 else (w ⟨2 * r.val / 2, _⟩).2),
      (if (2 * r.val + 1) % 2 = 0 then (w ⟨(2 * r.val + 1) / 2, _⟩).1
        else (w ⟨(2 * r.val + 1) / 2, _⟩).2)) = w r
    rw [if_pos (show 2 * r.val % 2 = 0 by omega),
      if_neg (show ¬(2 * r.val + 1) % 2 = 0 by omega)]
    exact Prod.ext
      (congrArg (fun j => (w j).1) (Fin.ext (show 2 * r.val / 2 = r.val by omega)))
      (congrArg (fun j => (w j).2) (Fin.ext (show (2 * r.val + 1) / 2 = r.val by omega)))

/-! ### The symmetric form of the coefficient of a row transition -/

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

open _root_.Classical in
/-- **The coefficient of a row transition in symmetric form**, between the position `m` with the
lists `xs` and the position `m'` with the lists `xt`, with the multiplier `μ`: zero unless both
states are physical, the shared labels agree and no auxiliary label occurs in either list;
otherwise the probability of the auxiliary labels, the coefficient `∏_g V_g^{-t_g}`, the two
damping factors and `μ` [S-02:0105–0115]. -/
def symCoef (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ} (ν : Pattern 𝒢.big J ℓ)
    (m m' : 𝔭.Pos) (xs xt : Lists 𝒢 J ℓ) (r : AuxList 𝒢.big ν.C) (μ : ℂ) : ℂ :=
  if IsPhys 𝔭 m xs ∧ IsPhys 𝔭 m' xt ∧ SharedSmall xs.1 xt.1 ∧ SharedBig ν.C xs.2 xt.2 ∧
      AuxAvoids ν.C r xs ∧ AuxAvoids ν.C r xt then
    ((auxWeight 𝒢.big ν.C r * targetNorm 𝒢 ℓ ν.C *
        (damping 𝔭 𝒢 J ℓ q m * damping 𝔭 𝒢 J ℓ q m') : ℝ) : ℂ) * μ
  else 0

variable {𝒢 : GroupFamily S B} {J ℓ : ℕ}

omit [DecidableEq S] [DecidableEq B] in
/-- **A forward edge**: `physCoef` is the symmetric coefficient between the position `n` and the
position `n + kD`, with the multiplier `K_ν D^{iζ}`. -/
theorem physCoef_eq_symCoef (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ)
    (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ)
    (r : AuxList 𝒢.big ν.C) (x' : Lists 𝒢 J ℓ) :
    physCoef 𝔭 𝒢 q ν k ζ n x r x' =
      symCoef 𝔭 𝒢 q ν n (𝔭.shift (k * dil ν.C x r) n) x x' r
        (ν.K x.2 x'.2 r * ((dil ν.C x r : ℕ) : ℂ) ^ ((ζ : ℂ) * Complex.I)) := by
  unfold physCoef symCoef
  exact bigRes_ite_congr Iff.rfl rfl rfl

omit [DecidableEq S] [DecidableEq B] in
/-- **A backward edge** [S-02:0120–0130]: "the adjoint moves by `-kD`, interchanges source and
target labels in the coefficient, and conjugates the multiplier". The conjugate of `physCoef` from
the position `m - kD` with the lists `xt` to the lists `xs` (`D` formed from `xs`) is the
symmetric coefficient between `m` with `xs` and `m - kD` with `xt`, with the conjugate multiplier;
"the shared product and hence `D` are unchanged on reversal". -/
theorem phSkel_conj_physCoef_rev (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ)
    (ν : Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (m : 𝔭.Pos) (xs xt : Lists 𝒢 J ℓ)
    (r : AuxList 𝒢.big ν.C) :
    conj (physCoef 𝔭 𝒢 q ν k ζ (𝔭.shift (-(k * dil ν.C xs r)) m) xt r xs) =
      symCoef 𝔭 𝒢 q ν m (𝔭.shift (-(k * dil ν.C xs r)) m) xs xt r
        (conj (ν.K xt.2 xs.2 r * ((dil ν.C xs r : ℕ) : ℂ) ^ ((ζ : ℂ) * Complex.I))) := by
  unfold symCoef
  by_cases hsh : SharedSmall xs.1 xt.1 ∧ SharedBig ν.C xs.2 xt.2
  · have hdil : dil ν.C xt r = dil ν.C xs r := by
      unfold dil
      rw [smallDil_eq_of_shared hsh.1, bigDil_eq_of_shared hsh.2]
    have hback : 𝔭.shift (k * (dil ν.C xt r : ℤ)) (𝔭.shift (-(k * (dil ν.C xs r : ℤ))) m) =
        m := by
      rw [hdil]
      exact 𝔭.shift_shift_neg _ _
    unfold physCoef
    rw [hback, hdil]
    refine phSkel_conj_ite ?_ _ _ _ ?_
    · constructor
      · rintro ⟨h1, h2, -, -, h5, h6⟩
        exact ⟨h2, h1, hsh.1, hsh.2, h6, h5⟩
      · rintro ⟨h1, h2, -, -, h5, h6⟩
        exact ⟨h2, h1, fun g i => (hsh.1 g i).symm, fun g i hi => (hsh.2 g i hi).symm, h6, h5⟩
    · ring
  · have hz : physCoef 𝔭 𝒢 q ν k ζ (𝔭.shift (-(k * dil ν.C xs r)) m) xt r xs = 0 := by
      unfold physCoef
      exact if_neg fun h =>
        hsh ⟨fun g i => (h.2.2.1 g i).symm, fun g i hi => (h.2.2.2.1 g i hi).symm⟩
    rw [hz, map_zero]
    exact (if_neg fun h => hsh ⟨h.2.2.1, h.2.2.2.1⟩).symm

omit [DecidableEq S] [DecidableEq B] in
open _root_.Classical in
/-- **The coefficient of an edge is the product of its small and its big half**
[S-02:0226–0234]: in the residue model with offsets, for `q > 0`, the symmetric coefficient
between `(a, y)` and `(a', y')`, times a factor `E` (the phase of the edge), is the product of

* the factor of the small residues and of the small lists, which also contains the conditions on
  the shared and on the auxiliary labels, the probability of the auxiliary labels, the multiplier
  and `E` (this is the common factor `Skel.edgeCommon` of an edge), and
* the factor of the big residues and of the big lists (the factor of an edge in
  `Skel.bigPhysAt`). -/
theorem symCoef_tag_split {q : ℝ} (hq : 0 < q) (ν : Pattern 𝒢.big J ℓ) (a a' : ℤ)
    (y y' : ResVec 𝒢.allPrimes) (yS yS' : ResVec (smallPrimes 𝒢))
    (yB yB' : ResVec (bigPrimes 𝒢)) (hS : resS 𝒢 y = yS) (hS' : resS 𝒢 y' = yS')
    (hB : resB 𝒢 y = yB) (hB' : resB 𝒢 y' = yB') (xs xt : Lists 𝒢 J ℓ)
    (r : AuxList 𝒢.big ν.C) (μ E : ℂ) :
    symCoef (tagModel 𝒢.allPrimes) 𝒢 q ν (tagPos a y) (tagPos a' y') xs xt r μ * E =
      (if IsSmallState 𝒢 yS xs.1 ∧ IsSmallState 𝒢 yS' xt.1 ∧ SharedSmall xs.1 xt.1 ∧
          SharedBig ν.C xs.2 xt.2 ∧ AuxAvoids ν.C r xs ∧ AuxAvoids ν.C r xt then
        ((auxWeight 𝒢.big ν.C r *
            ((∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
              (smallDamping 𝒢 J ℓ q yS * smallDamping 𝒢 J ℓ q yS')) : ℝ) : ℂ) * (μ * E)
      else 0) *
        (((if IsBigState 𝒢 yB xs.2 ∧ IsBigState 𝒢 yB' xt.2 then
            bigTargetNorm 𝒢 ℓ ν.C * (bigDamping 𝒢 J ℓ q yB * bigDamping 𝒢 J ℓ q yB')
          else 0 : ℝ)) : ℂ) := by
  subst hS hS' hB hB'
  have alg : ∀ (aw stn btn sd bd sd' bd' : ℝ) (μ E : ℂ),
      ((aw * (stn * btn) * ((sd * bd) * (sd' * bd')) : ℝ) : ℂ) * μ * E =
        ((aw * (stn * (sd * sd')) : ℝ) : ℂ) * (μ * E) * ((btn * (bd * bd') : ℝ) : ℂ) := by
    intro aw stn btn sd bd sd' bd' μ E
    push_cast
    ring
  unfold symCoef
  refine phSkel_ite_split _ _ _ _ ?_ ?_
  · rw [isPhys_tagPos_iff, isPhys_tagPos_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6, h7, h8⟩
      exact ⟨⟨h1, h3, h5, h6, h7, h8⟩, ⟨h2, h4⟩⟩
    · rintro ⟨⟨h1, h3, h5, h6, h7, h8⟩, ⟨h2, h4⟩⟩
      exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5, h6, h7, h8⟩
  · rw [damping_tagPos hq, damping_tagPos hq, targetNorm_eq_small_mul_big]
    exact alg _ _ _ _ _ _ _ _ _

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
