module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.CleanNorm.Shift
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.CleanNorm.Fibre
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Lemma 3.10: the clean row transition in conditioned form

Source: `verification/stage7-sources/S-02.tex`, lines 911–963 (`[S-02:0911–0963]`).

"A clean edge leaves all memory prime lists and sizes unchanged, translates their residues, drops
every unshared big source slot, and fills every unshared big target slot freshly. Its input and
output `ρ` factors and its memory projections are contractions. … The clean bilinear form is now
exactly `∑_𝐝 ⟨P_𝐝 w₁, 𝒯'_𝐝 P_𝐝 w₂⟩`. The operator between these maps uses the big-list transitions
and translates all unrestricted small and memory residues by `σ_i k d' D_ℬ`."

* `cleanChoice` — the clean local transition choices: a pattern, auxiliary labels, the small and
  the big target list (no store, no promotion); `clean_sum_choice`.
* `clean_edgeTgt` — the target of a clean transition: the residues and the memories are
  translated by the step, the lists are replaced.
* `clean_cond_iff` — the conditions of the coefficient of a clean transition split into the
  conditions of the source (`cleanU`), of the big lists (`cleanBeta`) and of the small target list
  (`cleanSmallW`). The ban of the auxiliary labels from the small lists is automatic, because the
  small and the big groups are disjoint.
* `clean_edgeCoef_eq` — the coefficient of a clean transition is the product of the source
  factor, the big-list coefficient with its phase, and the weight of the small target list.
* `cleanRow`, `cleanRow_apply` — **the clean row transition is `u · cov_{d'}(P_𝐝 ·)`**
  (eq:clean-conditioned-form), with the covariant operator of `Transfer.lean` for the big-list
  coefficients of `Fibre.lean`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators ComplexConjugate

noncomputable section

section Coef

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {N : Type}

/-- **A clean local transition choice** [S-02:0829–0830]: no store and no promotion. -/
def cleanChoice (D : MemData 𝒢 J ℓ N) (ν : N) (r : AuxList 𝒢.big (D.fam ν).C)
    (xsT : LabelList 𝒢.small J ℓ) (xbT : LabelList 𝒢.big J ℓ) : EdgeChoice 𝒢 D.fam Bc :=
  ⟨ν, r, fun _ => ∅, fun _ _ => none, xsT, xbT⟩

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem cleanChoice_isClean (D : MemData 𝒢 J ℓ N) (ν : N) (r : AuxList 𝒢.big (D.fam ν).C)
    (xsT : LabelList 𝒢.small J ℓ) (xbT : LabelList 𝒢.big J ℓ) :
    IsClean (cleanChoice (Bc := Bc) D ν r xsT xbT) := ⟨fun _ => rfl, fun _ _ => rfl⟩

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- The new memory of one big group without store and without promotion: the translated old
particles in their order. -/
theorem clean_edgeAbsNewList {g : B} (Δ : ℤ) (z : Mem 𝒢 Bc g)
    (xg : Slot J ℓ → {p : ℕ // p ∈ 𝒢.big g}) :
    edgeAbsNewList Δ z xg ∅ (fun _ => none) =
      (List.finRange Bc).filterMap (fun j => (memAt z j).map (shiftParticle Δ)) := by
  unfold edgeAbsNewList
  refine Eq.trans (clean_append_filter_nil _ _ _ _ ?_) ?_
  · intro sl
    exact decide_eq_false (Finset.notMem_empty sl)
  · refine congrArg (fun φ => (List.finRange Bc).filterMap φ) (funext fun j => ?_)
    exact if_neg fun ⟨sl, hsl⟩ => Option.some_ne_none j hsl.symm

omit [DecidableEq S] [DecidableEq B] in
theorem clean_edgeNewList (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc) (ν : N)
    (r : AuxList 𝒢.big (D.fam ν).C) (xsT : LabelList 𝒢.small J ℓ) (xbT : LabelList 𝒢.big J ℓ)
    (g : B) :
    edgeNewList D i s (cleanChoice D ν r xsT xbT) g =
      (List.finRange Bc).filterMap (fun j => (memAt (s.mem g) j).map
        (shiftParticle (edgeStep D i s (cleanChoice D ν r xsT xbT)))) :=
  clean_edgeAbsNewList (edgeStep D i s (cleanChoice D ν r xsT xbT)) (s.mem g) (s.xb g)

omit [DecidableEq S] [DecidableEq B] in
/-- **The target of a clean transition** [S-02:0911–0914]: the small residues and all pending
residues are translated by the step; the lists are replaced by the target lists. -/
theorem clean_edgeTgt (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc) (ν : N)
    (r : AuxList 𝒢.big (D.fam ν).C) (xsT : LabelList 𝒢.small J ℓ) (xbT : LabelList 𝒢.big J ℓ) :
    edgeTgt D i s (cleanChoice D ν r xsT xbT) =
      cleanMk (cleanSh (edgeStep D i s (cleanChoice D ν r xsT xbT)) (s.y, s.mem), xbT) xsT := by
  have hm : (fun g => memOfList (Bc := Bc) (edgeNewList D i s (cleanChoice D ν r xsT xbT) g)) =
      fun g => cleanShiftMem (edgeStep D i s (cleanChoice D ν r xsT xbT)) (s.mem g) := by
    funext g
    rw [clean_edgeNewList]
    exact clean_memOfList_map _ _
  exact congrArg (fun m => (⟨(resModel (smallPrimes 𝒢)).shift
    (edgeStep D i s (cleanChoice D ν r xsT xbT)) s.y, xsT, xbT, m⟩ : MState 𝒢 J ℓ Bc)) hm

omit [DecidableEq S] [DecidableEq B] in
theorem clean_sum_length (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc) (ν : N)
    (r : AuxList 𝒢.big (D.fam ν).C) (xsT : LabelList 𝒢.small J ℓ) (xbT : LabelList 𝒢.big J ℓ) :
    ∑ g, (edgeNewList D i s (cleanChoice D ν r xsT xbT) g).length = memTotal s := by
  unfold memTotal
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [clean_edgeNewList, clean_filterMap_memAt, List.length_ofFn]

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- **The ban of the auxiliary labels from the small lists is automatic**: the small and the big
groups are disjoint. -/
theorem clean_auxAvoids_iff (hdisj : ∀ g g', Disjoint (𝒢.small g) (𝒢.big g'))
    (C : B → Finset (Fin J)) (r : AuxList 𝒢.big C) (xs : LabelList 𝒢.small J ℓ)
    (xb : LabelList 𝒢.big J ℓ) :
    AuxAvoids C r ((xs, xb) : Lists 𝒢 J ℓ) ↔ cleanBan C r xb := by
  constructor
  · intro h g i
    exact (h g i).2
  · intro h g i
    refine ⟨fun g' s heq => ?_, h g i⟩
    have h1 : ((xs g' s : {p : ℕ // p ∈ 𝒢.small g'}) : ℕ) ∈ 𝒢.big g :=
      Eq.subst (motive := fun v : ℕ => v ∈ 𝒢.big g) heq.symm (r g i).2
    exact Finset.disjoint_left.mp (hdisj g' g) (xs g' s).2 h1

omit [DecidableEq S] [DecidableEq B] in
/-- **The conditions of the coefficient of a clean transition** split into the conditions of the
source, of the big lists and of the small target list. -/
theorem clean_cond_iff (hdisj : ∀ g g', Disjoint (𝒢.small g) (𝒢.big g'))
    (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc) (ν : N)
    (r : AuxList 𝒢.big (D.fam ν).C) (xsT : LabelList 𝒢.small J ℓ) (xbT : LabelList 𝒢.big J ℓ) :
    EdgeAbsCond D i s (cleanChoice D ν r xsT xbT) ↔
      (memTotal s ≤ Bc ∧ IsSmallState 𝒢 s.y s.xs) ∧
        (SharedBig (D.fam ν).C s.xb xbT ∧ cleanBan (D.fam ν).C r s.xb ∧
          cleanBan (D.fam ν).C r xbT) ∧
        (IsSmallState 𝒢 (cleanSh (edgeStep D i s (cleanChoice D ν r xsT xbT)) (s.y, s.mem)).1
            xsT ∧ cleanCls xsT = cleanCls s.xs) := by
  constructor
  · rintro ⟨h1, _, h3, h4, h5, h6, h7, h8, _, _⟩
    exact ⟨⟨h1, h3⟩,
      ⟨h6, (clean_auxAvoids_iff hdisj _ r s.xs s.xb).mp h7,
        (clean_auxAvoids_iff hdisj _ r xsT xbT).mp h8⟩,
      h4, funext fun g => funext fun i' => h5 g i'⟩
  · rintro ⟨⟨h1, h3⟩, ⟨h6, h7, h8⟩, h4, h5⟩
    refine ⟨h1, ?_, h3, h4, fun g i' => congrFun (congrFun h5 g) i', h6,
      (clean_auxAvoids_iff hdisj _ r s.xs s.xb).mpr h7,
      (clean_auxAvoids_iff hdisj _ r xsT xbT).mpr h8, ?_, ?_⟩
    · rw [clean_sum_length]
      exact h1
    · exact fun g sl hsl => absurd hsl (Finset.notMem_empty sl)
    · exact fun g sl j h => absurd h.symm (Option.some_ne_none j)

open _root_.Classical in
omit [DecidableEq S] [DecidableEq B] in
/-- The real prefactor of the coefficient of a clean transition. -/
theorem clean_edgeAbsReal (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc) (ν : N)
    (r : AuxList 𝒢.big (D.fam ν).C) (xsT : LabelList 𝒢.small J ℓ) (xbT : LabelList 𝒢.big J ℓ) :
    edgeAbsReal D i s (cleanChoice D ν r xsT xbT) =
      auxWeight 𝒢.big (D.fam ν).C r * D.ρ ^ memZeros s *
        (∏ g, ∏ sl : Slot J ℓ,
          (if Unshared ((D.fam ν).C g) sl then tiltLaw (𝒢.big g) D.q D.n (xbT g sl) else 1)) *
        D.ρ ^ cleanMemZeros
          (cleanSh (edgeStep D i s (cleanChoice D ν r xsT xbT)) (s.y, s.mem)).2 *
        ((∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
          (smallDamping 𝒢 J ℓ D.q s.y *
            smallDamping 𝒢 J ℓ D.q
              (cleanSh (edgeStep D i s (cleanChoice D ν r xsT xbT)) (s.y, s.mem)).1)) := by
  have hp : (∏ g, (Graph.primeGroupReciprocalMass (𝒢.big g) ^
      promoCount (cleanChoice (Bc := Bc) D ν r xsT xbT) g)⁻¹) = 1 := by
    refine Finset.prod_eq_one fun g _ => ?_
    have h0 : promoCount (cleanChoice (Bc := Bc) D ν r xsT xbT) g = 0 := by
      unfold promoCount
      exact Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun sl _ h => h rfl)
    rw [h0, pow_zero, inv_one]
  have hf : (∏ g, ∏ sl : Slot J ℓ,
        if Fresh (cleanChoice (Bc := Bc) D ν r xsT xbT) g sl then
          tiltLaw (𝒢.big g) D.q D.n ((cleanChoice (Bc := Bc) D ν r xsT xbT).xbT g sl) else 1) =
      ∏ g, ∏ sl : Slot J ℓ,
        (if Unshared ((D.fam ν).C g) sl then tiltLaw (𝒢.big g) D.q D.n (xbT g sl) else 1) :=
    Finset.prod_congr rfl fun g _ => Finset.prod_congr rfl fun sl _ =>
      ite_congr_of_iff ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩ rfl rfl
  have hz : memZeros (edgeTgt D i s (cleanChoice D ν r xsT xbT)) =
      cleanMemZeros (cleanSh (edgeStep D i s (cleanChoice D ν r xsT xbT)) (s.y, s.mem)).2 :=
    (congrArg (fun t : MState 𝒢 J ℓ Bc => memZeros t) (clean_edgeTgt D i s ν r xsT xbT)).trans rfl
  have key : edgeAbsReal D i s (cleanChoice D ν r xsT xbT) =
      auxWeight 𝒢.big (D.fam ν).C r * D.ρ ^ memZeros s *
        (∏ g, (Graph.primeGroupReciprocalMass (𝒢.big g) ^
          promoCount (cleanChoice (Bc := Bc) D ν r xsT xbT) g)⁻¹) *
        (∏ g, ∏ sl : Slot J ℓ,
          if Fresh (cleanChoice (Bc := Bc) D ν r xsT xbT) g sl then
            tiltLaw (𝒢.big g) D.q D.n ((cleanChoice (Bc := Bc) D ν r xsT xbT).xbT g sl) else 1) *
        D.ρ ^ memZeros (edgeTgt D i s (cleanChoice D ν r xsT xbT)) *
        ((∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
          (smallDamping 𝒢 J ℓ D.q s.y *
            smallDamping 𝒢 J ℓ D.q
              (cleanSh (edgeStep D i s (cleanChoice D ν r xsT xbT)) (s.y, s.mem)).1)) := rfl
  rw [key, hp, hf, hz, mul_one]

open _root_.Classical in
omit [DecidableEq S] [DecidableEq B] in
/-- **The coefficient of a clean transition** [S-02:0911–0963]: the source factor, times the
big-list coefficient with its phase, times the weight of the small target list in the
conditioning map and the output factor `ρ^{#zeros}`. -/
theorem clean_edgeCoef_eq (hdisj : ∀ g g', Disjoint (𝒢.small g) (𝒢.big g'))
    (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) (s : MState 𝒢 J ℓ Bc) (ν : N)
    (r : AuxList 𝒢.big (D.fam ν).C) (xsT : LabelList 𝒢.small J ℓ) (xbT : LabelList 𝒢.big J ℓ) :
    edgeCoef D θ i s (cleanChoice D ν r xsT xbT) =
      ((cleanU D.q D.ρ s : ℝ) : ℂ) *
        (cleanKappa D i (cleanD (cleanCls s.xs)) s.xb (⟨ν, (r, xbT)⟩ : CleanXi D) *
          expUnit (θ * ((cleanStep D i (cleanD (cleanCls s.xs)) s.xb
            (⟨ν, (r, xbT)⟩ : CleanXi D) : ℤ) : ℝ))) *
        ((cleanSmallW D.q (cleanCls s.xs)
            (cleanSh (cleanStep D i (cleanD (cleanCls s.xs)) s.xb (⟨ν, (r, xbT)⟩ : CleanXi D))
              (s.y, s.mem)).1 xsT *
          D.ρ ^ cleanMemZeros
            (cleanSh (cleanStep D i (cleanD (cleanCls s.xs)) s.xb (⟨ν, (r, xbT)⟩ : CleanXi D))
              (s.y, s.mem)).2 : ℝ) : ℂ) := by
  have hstep : cleanStep D i (cleanD (cleanCls s.xs)) s.xb (⟨ν, (r, xbT)⟩ : CleanXi D) =
      edgeStep D i s (cleanChoice D ν r xsT xbT) := rfl
  have ek : cleanKappa D i (cleanD (cleanCls s.xs)) s.xb (⟨ν, (r, xbT)⟩ : CleanXi D) =
      ((cleanBeta D ν s.xb r xbT : ℝ) : ℂ) *
        cleanMult D i (cleanD (cleanCls s.xs)) ν s.xb r xbT := rfl
  rw [hstep]
  by_cases hcond : EdgeAbsCond D i s (cleanChoice D ν r xsT xbT)
  · obtain ⟨⟨h1, h3⟩, ⟨h6, h7, h8⟩, h4, h5⟩ :=
      (clean_cond_iff hdisj D i s ν r xsT xbT).mp hcond
    have eu : cleanU D.q D.ρ s = D.ρ ^ memZeros s * smallDamping 𝒢 J ℓ D.q s.y :=
      if_pos ⟨h1, h3⟩
    have eb : cleanBeta D ν s.xb r xbT = auxWeight 𝒢.big (D.fam ν).C r *
        ∏ g, ∏ sl : Slot J ℓ,
          (if Unshared ((D.fam ν).C g) sl then tiltLaw (𝒢.big g) D.q D.n (xbT g sl) else 1) :=
      if_pos ⟨h6, h7, h8⟩
    have es : cleanSmallW D.q (cleanCls s.xs)
          (cleanSh (edgeStep D i s (cleanChoice D ν r xsT xbT)) (s.y, s.mem)).1 xsT =
        (∏ g : S, (Graph.primeGroupReciprocalMass (𝒢.small g) ^ ℓ)⁻¹) *
          smallDamping 𝒢 J ℓ D.q
            (cleanSh (edgeStep D i s (cleanChoice D ν r xsT xbT)) (s.y, s.mem)).1 :=
      if_pos ⟨h4, h5⟩
    have em : edgeMultiplier D i s (cleanChoice D ν r xsT xbT) =
        cleanMult D i (cleanD (cleanCls s.xs)) ν s.xb r xbT := rfl
    rw [edgeCoef_of_cond D θ i s _ hcond, clean_edgeAbsReal, ek, eu, eb, es, em]
    push_cast
    ring
  · rw [edgeCoef_of_not_cond D θ i s _ hcond]
    have hn := mt (clean_cond_iff hdisj D i s ν r xsT xbT).mpr hcond
    by_cases hA : memTotal s ≤ Bc ∧ IsSmallState 𝒢 s.y s.xs
    · by_cases hB : SharedBig (D.fam ν).C s.xb xbT ∧ cleanBan (D.fam ν).C r s.xb ∧
          cleanBan (D.fam ν).C r xbT
      · have hC : ¬(IsSmallState 𝒢
            (cleanSh (edgeStep D i s (cleanChoice D ν r xsT xbT)) (s.y, s.mem)).1 xsT ∧
            cleanCls xsT = cleanCls s.xs) := fun hC => hn ⟨hA, hB, hC⟩
        have es : cleanSmallW D.q (cleanCls s.xs)
            (cleanSh (edgeStep D i s (cleanChoice D ν r xsT xbT)) (s.y, s.mem)).1 xsT = 0 :=
          if_neg hC
        rw [es, zero_mul, Complex.ofReal_zero, mul_zero]
      · have eb : cleanBeta D ν s.xb r xbT = 0 := if_neg hB
        rw [ek, eb, Complex.ofReal_zero, zero_mul, zero_mul, mul_zero, zero_mul]
    · have eu : cleanU D.q D.ρ s = 0 := if_neg hA
      rw [eu, Complex.ofReal_zero, zero_mul, zero_mul]

variable [Fintype N]

open _root_.Classical in
/-- A sum over the clean local transition choices. -/
theorem clean_sum_choice (D : MemData 𝒢 J ℓ N) (F : EdgeChoice 𝒢 D.fam Bc → ℂ) :
    ∑ c, (if IsClean c then F c else 0) =
      ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C, ∑ xbT : LabelList 𝒢.big J ℓ,
        ∑ xsT : LabelList 𝒢.small J ℓ, F (cleanChoice D ν r xsT xbT) := by
  have h1 : ∑ c, (if IsClean c then F c else 0) =
      ∑ c ∈ Finset.univ.filter (fun c : EdgeChoice 𝒢 D.fam Bc => IsClean c), F c :=
    (Finset.sum_filter _ _).symm
  have h2 : ∑ c ∈ Finset.univ.filter (fun c : EdgeChoice 𝒢 D.fam Bc => IsClean c), F c =
      ∑ t : (Σ ν : N, AuxList 𝒢.big (D.fam ν).C × LabelList 𝒢.big J ℓ ×
        LabelList 𝒢.small J ℓ), F (cleanChoice D t.1 t.2.1 t.2.2.2 t.2.2.1) := by
    refine Finset.sum_nbij'
      (fun c : EdgeChoice 𝒢 D.fam Bc =>
        (⟨c.ν, (c.r, c.xbT, c.xsT)⟩ : Σ ν : N, AuxList 𝒢.big (D.fam ν).C ×
          LabelList 𝒢.big J ℓ × LabelList 𝒢.small J ℓ))
      (fun t : (Σ ν : N, AuxList 𝒢.big (D.fam ν).C × LabelList 𝒢.big J ℓ ×
          LabelList 𝒢.small J ℓ) => cleanChoice (Bc := Bc) D t.1 t.2.1 t.2.2.2 t.2.2.1)
      ?_ ?_ ?_ ?_ ?_
    · intro c _
      exact Finset.mem_univ _
    · intro t _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, cleanChoice_isClean D _ _ _ _⟩
    · intro c hc
      have hcl : IsClean c := (Finset.mem_filter.mp hc).2
      obtain ⟨ν, r, store, promo, xsT, xbT⟩ := c
      have e1 : store = fun _ => ∅ := funext hcl.1
      have e2 : promo = fun _ _ => none := funext fun g => funext fun sl => hcl.2 g sl
      subst e1
      subst e2
      rfl
    · intro t _
      obtain ⟨ν, r, xbT, xsT⟩ := t
      rfl
    · intro c hc
      have hcl : IsClean c := (Finset.mem_filter.mp hc).2
      obtain ⟨ν, r, store, promo, xsT, xbT⟩ := c
      have e1 : store = fun _ => ∅ := funext hcl.1
      have e2 : promo = fun _ _ => none := funext fun g => funext fun sl => hcl.2 g sl
      subst e1
      subst e2
      rfl
  rw [h1, h2]
  refine (Fintype.sum_sigma _).trans (Finset.sum_congr rfl fun ν _ => ?_)
  refine (Fintype.sum_prod_type _).trans (Finset.sum_congr rfl fun r _ => ?_)
  exact Fintype.sum_prod_type _

open _root_.Classical in
/-- **The clean row transition**: the row operator of the clean local transition choices, between
the two symmetrizations. -/
def cleanRow (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ) (i : ℕ) :
    (MState 𝒢 J ℓ Bc → ℂ) →ₗ[ℂ] (MState 𝒢 J ℓ Bc → ℂ) :=
  rowOp (fun s c => if IsClean c then edgeCoef D θ i s c else 0) (edgeTgt D i)

/-- **The clean row transition in conditioned form** (eq:clean-conditioned-form)
[S-02:0954–0963]: at a state with the shared small labels `𝐝`, it is the source factor times the
translation-covariant big-list operator for `d'`, applied to the conditioning map `P_𝐝`. -/
theorem cleanRow_apply (hdisj : ∀ g g', Disjoint (𝒢.small g) (𝒢.big g'))
    (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) (G : MState 𝒢 J ℓ Bc → ℂ) (s : MState 𝒢 J ℓ Bc) :
    cleanRow D Bc θ i G s =
      ((cleanU D.q D.ρ s : ℝ) : ℂ) *
        cleanCovOp (cleanSh (𝒢 := 𝒢) (Bc := Bc)) (cleanKappa D i (cleanD (cleanCls s.xs)))
          (cleanStep D i (cleanD (cleanCls s.xs))) (cleanTau D) θ
          (cleanQ D.q D.ρ (cleanCls s.xs) G) ((s.y, s.mem), s.xb) := by
  have hL : cleanRow D Bc θ i G s =
      ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C, ∑ xbT : LabelList 𝒢.big J ℓ,
        ∑ xsT : LabelList 𝒢.small J ℓ,
          edgeCoef D θ i s (cleanChoice D ν r xsT xbT) *
            G (edgeTgt D i s (cleanChoice D ν r xsT xbT)) := by
    unfold cleanRow
    rw [rowOp_apply,
      ← clean_sum_choice D (fun c => edgeCoef D θ i s c * G (edgeTgt D i s c))]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : IsClean c
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc, zero_mul]
  have hR : ((cleanU D.q D.ρ s : ℝ) : ℂ) *
        cleanCovOp (cleanSh (𝒢 := 𝒢) (Bc := Bc)) (cleanKappa D i (cleanD (cleanCls s.xs)))
          (cleanStep D i (cleanD (cleanCls s.xs))) (cleanTau D) θ
          (cleanQ D.q D.ρ (cleanCls s.xs) G) ((s.y, s.mem), s.xb) =
      ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C, ∑ xbT : LabelList 𝒢.big J ℓ,
        ∑ xsT : LabelList 𝒢.small J ℓ,
          ((cleanU D.q D.ρ s : ℝ) : ℂ) *
            (cleanKappa D i (cleanD (cleanCls s.xs)) s.xb (⟨ν, (r, xbT)⟩ : CleanXi D) *
              expUnit (θ * ((cleanStep D i (cleanD (cleanCls s.xs)) s.xb
                (⟨ν, (r, xbT)⟩ : CleanXi D) : ℤ) : ℝ)) *
              (((cleanSmallW D.q (cleanCls s.xs)
                  (cleanSh (cleanStep D i (cleanD (cleanCls s.xs)) s.xb
                    (⟨ν, (r, xbT)⟩ : CleanXi D)) (s.y, s.mem)).1 xsT *
                D.ρ ^ cleanMemZeros
                  (cleanSh (cleanStep D i (cleanD (cleanCls s.xs)) s.xb
                    (⟨ν, (r, xbT)⟩ : CleanXi D)) (s.y, s.mem)).2 : ℝ) : ℂ) *
                G (cleanMk (cleanSh (cleanStep D i (cleanD (cleanCls s.xs)) s.xb
                  (⟨ν, (r, xbT)⟩ : CleanXi D)) (s.y, s.mem), xbT) xsT))) := by
    unfold cleanCovOp
    rw [rowOp_apply, Finset.mul_sum]
    refine (Fintype.sum_sigma _).trans (Finset.sum_congr rfl fun ν _ => ?_)
    refine (Fintype.sum_prod_type _).trans
      (Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun xbT _ => ?_)
    show ((cleanU D.q D.ρ s : ℝ) : ℂ) *
        (cleanKappa D i (cleanD (cleanCls s.xs)) s.xb (⟨ν, (r, xbT)⟩ : CleanXi D) *
          expUnit (θ * ((cleanStep D i (cleanD (cleanCls s.xs)) s.xb
            (⟨ν, (r, xbT)⟩ : CleanXi D) : ℤ) : ℝ)) *
          cleanQ D.q D.ρ (cleanCls s.xs) G
            (cleanSh (cleanStep D i (cleanD (cleanCls s.xs)) s.xb
              (⟨ν, (r, xbT)⟩ : CleanXi D)) (s.y, s.mem), xbT)) = _
    have hq : cleanQ D.q D.ρ (cleanCls s.xs) G
          (cleanSh (cleanStep D i (cleanD (cleanCls s.xs)) s.xb
            (⟨ν, (r, xbT)⟩ : CleanXi D)) (s.y, s.mem), xbT) =
        ∑ xsT : LabelList 𝒢.small J ℓ,
          ((cleanSmallW D.q (cleanCls s.xs)
              (cleanSh (cleanStep D i (cleanD (cleanCls s.xs)) s.xb
                (⟨ν, (r, xbT)⟩ : CleanXi D)) (s.y, s.mem)).1 xsT *
            D.ρ ^ cleanMemZeros
              (cleanSh (cleanStep D i (cleanD (cleanCls s.xs)) s.xb
                (⟨ν, (r, xbT)⟩ : CleanXi D)) (s.y, s.mem)).2 : ℝ) : ℂ) *
            G (cleanMk (cleanSh (cleanStep D i (cleanD (cleanCls s.xs)) s.xb
              (⟨ν, (r, xbT)⟩ : CleanXi D)) (s.y, s.mem), xbT) xsT) := rfl
    rw [hq, Finset.mul_sum, Finset.mul_sum]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun r _ =>
    Finset.sum_congr rfl fun xbT _ => Finset.sum_congr rfl fun xsT _ => ?_
  have ht : edgeTgt D i s (cleanChoice D ν r xsT xbT) =
      cleanMk (cleanSh (cleanStep D i (cleanD (cleanCls s.xs)) s.xb
        (⟨ν, (r, xbT)⟩ : CleanXi D)) (s.y, s.mem), xbT) xsT :=
    clean_edgeTgt D i s ν r xsT xbT
  rw [clean_edgeCoef_eq hdisj D θ i s ν r xsT xbT, ht]
  ring

end Coef

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
