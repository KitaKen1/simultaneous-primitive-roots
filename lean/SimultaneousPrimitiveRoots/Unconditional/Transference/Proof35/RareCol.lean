module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.RareRow
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# [S] Lemma 3.9 (rare transfer): the column bound of the store part

Source: `verification/stage7-sources/S-02.tex`, lines 877–882 (`[S-02:0877–0882]`).

"Terms with stores and no promotion have the same improvement in their column bound by reversing
the edge: a stored particle becomes a retrieval from output memory. The exclusion `p ∤ D` is
retained under reversal, even when numerical coincidences have been allowed."

A store appends the particle `(p, Δ)` to the memory, `Δ = σ_i k D`, with `p ∤ D`; the dilation `D`
is formed from the shared labels, so it is the dilation of the target lists as well. Hence the
target of a choice with a store has a pending particle `(p, r)` with `r ≡ σ_i k D (mod p)`,
`p ∤ D` (`rareElig_of_store`). The target lists are symmetrized by a uniform slot permutation, so
for at most `B` of the `𝒟` omission choices of the target such a particle exists (`rareFrac_le`).

* `HasStore`, `rareStoreQ`, `rareElig_of_store` — the target of a choice with a store and a
  nonvanishing coefficient has an eligible pending particle.
* `rare_col_fixed_pattern` — fixed pattern, free labels and target slot permutation: the column
  inequality of Lemma 3.8 (`edgeAbs_col_fixed_pattern`) for the test function multiplied by the
  indicator of eligibility, which is symmetric in the particle indices.
* `rare_colBound` — the weighted column bound of the store part of the edge operation, with the
  factor `B/𝒟`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators

noncomputable section

section Col

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ Bc : ℕ} {N : Type}

/-- **A choice with at least one store** [S-02:0829]. -/
def HasStore {𝔉 : N → Pattern 𝒢.big J ℓ} (c : EdgeChoice 𝒢 𝔉 Bc) : Prop :=
  ∃ (g : B) (sl : Slot J ℓ), sl ∈ c.store g

/-- **The congruence of a stored particle** [S-02:0489–0493, 0877–0880]: the residue of the
pending particle is the step, `r ≡ Δ (mod p)` ("appending their particles at residue zero", then
"translate all pending residues, including the newly stored ones"). -/
def rareStoreQ (g : B) (pr : Particle 𝒢 g) (Δ : ℤ) : Prop := pr.2 = ((Δ : ℤ) : Res (pr.1 : ℕ))

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- Two steps which are the residue of the same pending particle `(p, r)` are congruent modulo
`p`. -/
theorem rareStoreQ_dvd (g : B) (pr : Particle 𝒢 g) (Δ₁ Δ₂ : ℤ) (hp : 0 < (pr.1 : ℕ))
    (h1 : rareStoreQ g pr Δ₁) (h2 : rareStoreQ g pr Δ₂) : ((pr.1 : ℕ) : ℤ) ∣ Δ₁ - Δ₂ := by
  have h3 : ((Δ₁ - Δ₂ : ℤ) : Res (pr.1 : ℕ)) = 0 := by
    rw [Int.cast_sub, sub_eq_zero]
    exact h1.symm.trans h2
  exact (Res.intCast_eq_zero_iff _ hp _).mp h3

omit [DecidableEq S] [DecidableEq B] in
/-- **The target of a choice with a store and a nonvanishing coefficient has an eligible pending
particle** [S-02:0877–0881]: the stored particle `(p, σ_i k D)`, with `p ∤ D`; "the exclusion
`p ∤ D` is retained under reversal". -/
theorem rareElig_of_store (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (c : EdgeChoice 𝒢 D.fam Bc) (hcond : EdgeAbsCond D i s c) (hS : HasStore c) :
    RareElig rareStoreQ (edgeSign i * D.k) (D.fam c.ν).C c.r (edgeTgt D i s c) := by
  obtain ⟨_, h2, _, h4, h5, h6, _, _, h9, _⟩ := hcond
  obtain ⟨g, sl, hsl⟩ := hS
  have hlen : ∀ g, (edgeNewList D i s c g).length ≤ Bc :=
    edgeNewList_length_le_of_sum D i s c h2
  have hmt : memTotal (edgeTgt D i s c) ≤ Bc := by
    have e : memTotal (edgeTgt D i s c) = ∑ g, (edgeNewList D i s c g).length := by
      unfold memTotal
      exact Finset.sum_congr rfl fun g _ => memOfList_size (hlen g)
    rw [e]
    exact h2
  have hdil : dil (D.fam c.ν).C ((c.xsT, c.xbT) : Lists 𝒢 J ℓ) c.r = edgeDil D s c := by
    show smallDil c.xsT * bigDil (D.fam c.ν).C c.xbT c.r =
      smallDil s.xs * bigDil (D.fam c.ν).C s.xb c.r
    rw [smallDil_eq_of_shared h5, bigDil_eq_of_shared h6]
  have hmem : shiftParticle (edgeStep D i s c) (⟨s.xb g sl, 0⟩ : Particle 𝒢 g) ∈
      edgeNewList D i s c g := by
    unfold edgeNewList
    exact List.mem_append_right _ (List.mem_map.mpr
      ⟨sl, List.mem_filter.mpr ⟨l38_mem_slotList sl, decide_eq_true hsl⟩, rfl⟩)
  have hmem2 : shiftParticle (edgeStep D i s c) (⟨s.xb g sl, 0⟩ : Particle 𝒢 g) ∈
      (List.finRange Bc).filterMap
        (memAt (memOfList (Bc := Bc) (edgeNewList D i s c g))) := by
    refine (l38_filterMap_memAt_perm
      (memOfList (Bc := Bc) (edgeNewList D i s c g))).mem_iff.mpr ?_
    rw [ofFn_memOfList (hlen g)]
    exact hmem
  obtain ⟨j, _, hj⟩ := List.mem_filterMap.mp hmem2
  have hQ : rareStoreQ g (shiftParticle (edgeStep D i s c) (⟨s.xb g sl, 0⟩ : Particle 𝒢 g))
      (edgeSign i * D.k *
        ((dil (D.fam c.ν).C ((c.xsT, c.xbT) : Lists 𝒢 J ℓ) c.r : ℕ) : ℤ)) := by
    rw [hdil]
    show ((edgeStep D i s c : ℤ) : Res (s.xb g sl : ℕ)) + 0 =
      ((edgeStep D i s c : ℤ) : Res (s.xb g sl : ℕ))
    exact add_zero _
  have hnd : ¬(((shiftParticle (edgeStep D i s c) (⟨s.xb g sl, 0⟩ : Particle 𝒢 g)).1 : ℕ) ∣
      dil (D.fam c.ν).C ((c.xsT, c.xbT) : Lists 𝒢 J ℓ) c.r) := by
    rw [hdil]
    exact (h9 g sl hsl).2
  exact ⟨hmt, h4.1, g, j,
    shiftParticle (edgeStep D i s c) (⟨s.xb g sl, 0⟩ : Particle 𝒢 g), hj, hQ, hnd⟩

open _root_.Classical in
/-- **The column of the store part for a fixed pattern, fixed free labels and a fixed target slot
permutation** [S-02:0877–0881]: for a nonnegative test function `f` which is symmetric in the
particle indices, evaluated at the target with its slots permuted by `π⁻¹`, the terms with a store
only see the targets `t` with an eligible pending particle, and the column inequality of
Lemma 3.8 applies to `t ↦ 1[eligible at t] f(t · π⁻¹)`. On the right the integration variable is
`s = t · π⁻¹`. -/
theorem rare_col_fixed_pattern (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) {v vMinus Mmax : ℝ}
    {T : ℕ} (hq0 : 0 < D.q) (hq1 : D.q < 1) (hρ0 : 0 < D.ρ) (hρ1 : D.ρ < 1) (hv : 1 ≤ v)
    (hvm : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p)
    (hM : ∀ g, ∑ p : {p : ℕ // p ∈ 𝒢.big g}, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax)
    (hT : 0 < T) (hℓT : ℓ ≤ T) (ν : N) (hC : ∀ g, ℓ + ((D.fam ν).C g).card ≤ T)
    (r : AuxList 𝒢.big (D.fam ν).C) (π : ListPerms S B J ℓ) (f : MState 𝒢 J ℓ Bc → ℝ)
    (hf0 : ∀ s, 0 ≤ f s) (hfsym : MemSymmetric f) :
    ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
        ∑ t : EdgeAbsTail 𝒢 J ℓ Bc,
          (if HasStore (edgeAbsChoice (𝔉 := D.fam) ν r t) then
              ‖edgeCoef D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t)‖ else 0) *
            f ((edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t)).permLists π⁻¹) ≤
      auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) *
          ((∏ _g : S, Schur.groupConst vMinus D.q T) *
            (∏ _g : B, edgeAbsColConst vMinus D.ρ v Mmax T)) *
        ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s * f s *
          (if RareElig rareStoreQ (edgeSign i * D.k) (D.fam ν).C r (s.permLists π) then 1
            else 0) := by
  have hv0 : 0 ≤ v := zero_le_one.trans hv
  have hind0 : ∀ u : MState 𝒢 J ℓ Bc, (0 : ℝ) ≤
      (if RareElig rareStoreQ (edgeSign i * D.k) (D.fam ν).C r u then (1 : ℝ) else 0) := by
    intro u
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  have hcol := edgeAbs_col_fixed_pattern D θ i hq0 hq1 hρ0 hρ1 hv hvm hVS hVB hν hM hT hℓT ν hC
    r
    (fun u : MState 𝒢 J ℓ Bc =>
      (if RareElig rareStoreQ (edgeSign i * D.k) (D.fam ν).C r u then (1 : ℝ) else 0) *
        f (u.permLists π⁻¹))
    (fun u => mul_nonneg (hind0 u) (hf0 _))
    (rare_ind_mul_memSymmetric rareStoreQ (edgeSign i * D.k) (D.fam ν).C r
      (l38_memSymmetric_permLists hfsym π⁻¹))
  have h1 : ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
        ∑ t : EdgeAbsTail 𝒢 J ℓ Bc,
          (if HasStore (edgeAbsChoice (𝔉 := D.fam) ν r t) then
              ‖edgeCoef D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t)‖ else 0) *
            f ((edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t)).permLists π⁻¹) ≤
      ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
        ∑ t : EdgeAbsTail 𝒢 J ℓ Bc,
          ‖edgeCoef D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t)‖ *
            ((if RareElig rareStoreQ (edgeSign i * D.k) (D.fam ν).C r
                (edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t)) then (1 : ℝ) else 0) *
              f ((edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t)).permLists π⁻¹)) := by
    refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun t _ => ?_)
      (mul_nonneg (memWeight_nonneg 𝒢 D.q D.n hν s) (pow_nonneg hv0 _))
    by_cases hS : HasStore (edgeAbsChoice (𝔉 := D.fam) ν r t)
    · by_cases hcond : EdgeAbsCond D i s (edgeAbsChoice (𝔉 := D.fam) ν r t)
      · have hel := rareElig_of_store D i s (edgeAbsChoice (𝔉 := D.fam) ν r t) hcond hS
        have hE : RareElig rareStoreQ (edgeSign i * D.k) (D.fam ν).C r
            (edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t)) := hel
        rw [if_pos hS, if_pos hE, one_mul]
      · rw [if_pos hS,
          edgeCoef_of_not_cond D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t) hcond, norm_zero,
          zero_mul, zero_mul]
    · rw [if_neg hS, zero_mul]
      exact mul_nonneg (norm_nonneg _) (mul_nonneg (hind0 _) (hf0 _))
  have h2 := l38_sum_permLists D.q D.n v π
    (fun u : MState 𝒢 J ℓ Bc =>
      (if RareElig rareStoreQ (edgeSign i * D.k) (D.fam ν).C r u then (1 : ℝ) else 0) *
        f (u.permLists π⁻¹))
  have h3 : ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
        ((if RareElig rareStoreQ (edgeSign i * D.k) (D.fam ν).C r s then (1 : ℝ) else 0) *
          f (s.permLists π⁻¹)) =
      ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s * f s *
        (if RareElig rareStoreQ (edgeSign i * D.k) (D.fam ν).C r (s.permLists π) then 1
          else 0) :=
    h2.symm.trans (Finset.sum_congr rfl fun s _ => by
      rw [rare_permLists_inv]
      ring)
  refine (h1.trans hcol).trans (le_of_eq ?_)
  rw [h3]

variable [Fintype N]

open _root_.Classical in
/-- **The column of the store part of the row transition between the two symmetrizations**, for a
fixed target slot permutation: the sum over the patterns and the free labels. -/
theorem rare_col_choice (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) {v vMinus Mmax : ℝ} {T : ℕ}
    (hq0 : 0 < D.q) (hq1 : D.q < 1) (hρ0 : 0 < D.ρ) (hρ1 : D.ρ < 1) (hv : 1 ≤ v)
    (hvm : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p)
    (hM : ∀ g, ∑ p : {p : ℕ // p ∈ 𝒢.big g}, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax)
    (hT : 0 < T) (hℓT : ℓ ≤ T) (hC : ∀ ν g, ℓ + ((D.fam ν).C g).card ≤ T)
    (π : ListPerms S B J ℓ) (f : MState 𝒢 J ℓ Bc → ℝ) (hf0 : ∀ s, 0 ≤ f s)
    (hfsym : MemSymmetric f) :
    ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
        ∑ c : EdgeChoice 𝒢 D.fam Bc, (if HasStore c then ‖edgeCoef D θ i s c‖ else 0) *
          f ((edgeTgt D i s c).permLists π⁻¹) ≤
      ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C,
        auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) *
            ((∏ _g : S, Schur.groupConst vMinus D.q T) *
              (∏ _g : B, edgeAbsColConst vMinus D.ρ v Mmax T)) *
          ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s * f s *
            (if RareElig rareStoreQ (edgeSign i * D.k) (D.fam ν).C r (s.permLists π) then 1
              else 0) := by
  have e1 : ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
        ∑ c : EdgeChoice 𝒢 D.fam Bc, (if HasStore c then ‖edgeCoef D θ i s c‖ else 0) *
          f ((edgeTgt D i s c).permLists π⁻¹) =
      ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C, ∑ s : MState 𝒢 J ℓ Bc,
        memWeight 𝒢 D.q D.n s * schurWeight v s *
          ∑ t : EdgeAbsTail 𝒢 J ℓ Bc,
            (if HasStore (edgeAbsChoice (𝔉 := D.fam) ν r t) then
                ‖edgeCoef D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t)‖ else 0) *
              f ((edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t)).permLists π⁻¹) :=
    (Finset.sum_congr rfl fun s _ => congrArg
      (fun t => memWeight 𝒢 D.q D.n s * schurWeight v s * t)
      (edgeAbs_sum_choice (𝔉 := D.fam) (Bc := Bc)
        (fun c => (if HasStore c then ‖edgeCoef D θ i s c‖ else 0) *
          f ((edgeTgt D i s c).permLists π⁻¹)))).trans
      (l38_sum_swap3 (γ := fun ν : N => AuxList 𝒢.big (D.fam ν).C)
        (fun s : MState 𝒢 J ℓ Bc => memWeight 𝒢 D.q D.n s * schurWeight v s)
        (fun (s : MState 𝒢 J ℓ Bc) (ν : N) (r : AuxList 𝒢.big (D.fam ν).C) =>
          ∑ t : EdgeAbsTail 𝒢 J ℓ Bc,
            (if HasStore (edgeAbsChoice (𝔉 := D.fam) ν r t) then
                ‖edgeCoef D θ i s (edgeAbsChoice (𝔉 := D.fam) ν r t)‖ else 0) *
              f ((edgeTgt D i s (edgeAbsChoice (𝔉 := D.fam) ν r t)).permLists π⁻¹)))
  rw [e1]
  exact Finset.sum_le_sum fun ν _ => Finset.sum_le_sum fun r _ =>
    rare_col_fixed_pattern D θ i hq0 hq1 hρ0 hρ1 hv hvm hVS hVB hν hM hT hℓT ν (hC ν) r π f
      hf0 hfsym

open _root_.Classical in
/-- **The column integral of the store part of the edge operation, by the two slot
permutations**: the two averages, with the second permutation inverted. -/
theorem rare_col_split (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) (v : ℝ)
    (f : MState 𝒢 J ℓ Bc → ℝ) :
    ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
        ∑ ξ : EdgeFullChoice D Bc,
          (if HasStore ξ.2.1 then ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ else 0) *
            f (edgeFullTgt D i s ξ) =
      ∑ π₁ : ListPerms S B J ℓ, ∑ π₂ : ListPerms S B J ℓ,
        (Fintype.card (ListPerms S B J ℓ) : ℝ)⁻¹ * ((Fintype.card (ListPerms S B J ℓ) : ℝ)⁻¹ *
          ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
            ∑ c : EdgeChoice 𝒢 D.fam Bc,
              (if HasStore c then ‖edgeCoef D θ i (s.permLists π₁) c‖ else 0) *
                f ((edgeTgt D i (s.permLists π₁) c).permLists π₂⁻¹)) := by
  obtain ⟨cd, hcd⟩ : ∃ cd : ℝ, cd = (Fintype.card (ListPerms S B J ℓ) : ℝ) := ⟨_, rfl⟩
  rw [← hcd]
  have hterm : ∀ (s : MState 𝒢 J ℓ Bc) (π₁ : ListPerms S B J ℓ) (c : EdgeChoice 𝒢 D.fam Bc)
      (π₂ : ListPerms S B J ℓ),
      (if HasStore c then ‖edgeFullCoef D (fun _ => 1) θ i s (π₁, c, π₂)‖ else 0) *
          f (edgeFullTgt D i s (π₁, c, π₂)) =
        cd⁻¹ * (cd⁻¹ * ((if HasStore c then ‖edgeCoef D θ i (s.permLists π₁) c‖ else 0) *
          f ((edgeTgt D i (s.permLists π₁) c).permLists π₂))) := by
    intro s π₁ c π₂
    have ht : edgeFullTgt D i s (π₁, c, π₂) = (edgeTgt D i (s.permLists π₁) c).permLists π₂ :=
      rfl
    have hn : ‖edgeFullCoef D (fun _ => 1) θ i s (π₁, c, π₂)‖ =
        cd⁻¹ * ‖edgeCoef D θ i (s.permLists π₁) c‖ * cd⁻¹ := by
      rw [hcd]
      exact norm_edgeFullCoef_one D θ i s (π₁, c, π₂)
    rw [ht]
    by_cases hS : HasStore c
    · rw [if_pos hS, if_pos hS, hn]
      ring
    · rw [if_neg hS, if_neg hS, zero_mul, mul_zero, mul_zero]
  have hξ : ∀ s : MState 𝒢 J ℓ Bc,
      ∑ ξ : EdgeFullChoice D Bc,
          (if HasStore ξ.2.1 then ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ else 0) *
            f (edgeFullTgt D i s ξ) =
        ∑ π₁ : ListPerms S B J ℓ, ∑ π₂ : ListPerms S B J ℓ,
          cd⁻¹ * (cd⁻¹ * ∑ c : EdgeChoice 𝒢 D.fam Bc,
            (if HasStore c then ‖edgeCoef D θ i (s.permLists π₁) c‖ else 0) *
              f ((edgeTgt D i (s.permLists π₁) c).permLists π₂)) := by
    intro s
    calc ∑ ξ : EdgeFullChoice D Bc,
          (if HasStore ξ.2.1 then ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ else 0) *
            f (edgeFullTgt D i s ξ)
        = ∑ π₁ : ListPerms S B J ℓ, ∑ c : EdgeChoice 𝒢 D.fam Bc, ∑ π₂ : ListPerms S B J ℓ,
            (if HasStore c then ‖edgeFullCoef D (fun _ => 1) θ i s (π₁, c, π₂)‖ else 0) *
              f (edgeFullTgt D i s (π₁, c, π₂)) := by
          refine (Fintype.sum_prod_type _).trans (Finset.sum_congr rfl fun π₁ _ => ?_)
          exact Fintype.sum_prod_type _
      _ = ∑ π₁ : ListPerms S B J ℓ, ∑ π₂ : ListPerms S B J ℓ,
            cd⁻¹ * (cd⁻¹ * ∑ c : EdgeChoice 𝒢 D.fam Bc,
              (if HasStore c then ‖edgeCoef D θ i (s.permLists π₁) c‖ else 0) *
                f ((edgeTgt D i (s.permLists π₁) c).permLists π₂)) := by
          refine Finset.sum_congr rfl fun π₁ _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun π₂ _ => ?_
          rw [Finset.sum_congr rfl fun c _ => hterm s π₁ c π₂, ← Finset.mul_sum,
            ← Finset.mul_sum]
  calc ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
        ∑ ξ : EdgeFullChoice D Bc,
          (if HasStore ξ.2.1 then ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ else 0) *
            f (edgeFullTgt D i s ξ)
      = ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
          ∑ π₁ : ListPerms S B J ℓ, ∑ π₂ : ListPerms S B J ℓ,
            cd⁻¹ * (cd⁻¹ * ∑ c : EdgeChoice 𝒢 D.fam Bc,
              (if HasStore c then ‖edgeCoef D θ i (s.permLists π₁) c‖ else 0) *
                f ((edgeTgt D i (s.permLists π₁) c).permLists π₂)) :=
        Finset.sum_congr rfl fun s _ =>
          congrArg (fun t => memWeight 𝒢 D.q D.n s * schurWeight v s * t) (hξ s)
    _ = ∑ π₁ : ListPerms S B J ℓ, ∑ π₂ : ListPerms S B J ℓ,
          cd⁻¹ * (cd⁻¹ * ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
            ∑ c : EdgeChoice 𝒢 D.fam Bc,
              (if HasStore c then ‖edgeCoef D θ i (s.permLists π₁) c‖ else 0) *
                f ((edgeTgt D i (s.permLists π₁) c).permLists π₂)) := by
        refine (l38_sum_swap3 (γ := fun _ : ListPerms S B J ℓ => ListPerms S B J ℓ)
          (fun s : MState 𝒢 J ℓ Bc => memWeight 𝒢 D.q D.n s * schurWeight v s)
          (fun (s : MState 𝒢 J ℓ Bc) (π₁ π₂ : ListPerms S B J ℓ) =>
            cd⁻¹ * (cd⁻¹ * ∑ c : EdgeChoice 𝒢 D.fam Bc,
              (if HasStore c then ‖edgeCoef D θ i (s.permLists π₁) c‖ else 0) *
                f ((edgeTgt D i (s.permLists π₁) c).permLists π₂)))).trans
          (Finset.sum_congr rfl fun π₁ _ => Finset.sum_congr rfl fun π₂ _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
    _ = ∑ π₁ : ListPerms S B J ℓ, ∑ π₂ : ListPerms S B J ℓ,
          cd⁻¹ * (cd⁻¹ * ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
            ∑ c : EdgeChoice 𝒢 D.fam Bc,
              (if HasStore c then ‖edgeCoef D θ i (s.permLists π₁) c‖ else 0) *
                f ((edgeTgt D i (s.permLists π₁) c).permLists π₂⁻¹)) :=
        Finset.sum_congr rfl fun π₁ _ =>
          (Equiv.sum_comp (Equiv.inv (ListPerms S B J ℓ))
            (fun π₂ : ListPerms S B J ℓ =>
              cd⁻¹ * (cd⁻¹ * ∑ s : MState 𝒢 J ℓ Bc,
                memWeight 𝒢 D.q D.n s * schurWeight v s *
                  ∑ c : EdgeChoice 𝒢 D.fam Bc,
                    (if HasStore c then ‖edgeCoef D θ i (s.permLists π₁) c‖ else 0) *
                      f ((edgeTgt D i (s.permLists π₁) c).permLists π₂)))).symm

open _root_.Classical in
/-- **The weighted column bound of the store part of an edge** [S-02:0877–0881]: "terms with
stores and no promotion have the same improvement in their column bound by reversing the edge".
The kernel is the modulus of the coefficients of the local transition choices with at least one
store; the constant is the column constant of Lemma 3.8 times `B/𝒟`. -/
theorem rare_colBound (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) {v vMinus Mmax : ℝ} {T : ℕ}
    (hq0 : 0 < D.q) (hq1 : D.q < 1) (hρ0 : 0 < D.ρ) (hρ1 : D.ρ < 1) (hv : 1 ≤ v)
    (hvm : 0 < vMinus)
    (hVS : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.small g))
    (hVB : ∀ g, vMinus ≤ Graph.primeGroupReciprocalMass (𝒢.big g))
    (hlaw : ∀ g, ∑ p ∈ 𝒢.big g, Graph.primeGroupLaw (𝒢.big g) p = 1)
    (hν : ∀ g, ∀ p ∈ 𝒢.big g, 0 ≤ tiltLaw (𝒢.big g) D.q D.n p)
    (hM : ∀ g, ∑ p ∈ 𝒢.big g, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax)
    (hT : 0 < T) (hℓT : ℓ ≤ T) (hC : ∀ ν g, ℓ + ((D.fam ν).C g).card ≤ T)
    (hA : RareArith 𝒢 ℓ (edgeSign i * D.k)) :
    ColBound (memWeight 𝒢 D.q D.n) (schurWeight v) (fun f => MemSymmetric f)
      (fun (s : MState 𝒢 J ℓ Bc) (ξ : EdgeFullChoice D Bc) =>
        if HasStore ξ.2.1 then ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ else 0) (edgeFullTgt D i)
      (patternMass D.fam *
        ((∏ _g : S, Schur.groupConst vMinus D.q T) *
          (∏ _g : B, edgeAbsColConst vMinus D.ρ v Mmax T)) *
        ((Bc : ℝ) / (omissionNumber S J ℓ : ℝ))) := by
  intro f hf0 hfsym
  have hv0 : 0 ≤ v := zero_le_one.trans hv
  have hM' : ∀ g, ∑ p : {p : ℕ // p ∈ 𝒢.big g}, tiltLaw (𝒢.big g) D.q D.n p ≤ Mmax :=
    fun g => (le_of_eq (Finset.sum_coe_sort (𝒢.big g)
      (fun p => tiltLaw (𝒢.big g) D.q D.n p))).trans (hM g)
  obtain ⟨cd, hcd⟩ : ∃ cd : ℝ, cd = (Fintype.card (ListPerms S B J ℓ) : ℝ) := ⟨_, rfl⟩
  have hcdpos : 0 < cd := by
    rw [hcd]
    exact Nat.cast_pos.mpr Fintype.card_pos
  have hci0 : 0 ≤ cd⁻¹ := inv_nonneg.mpr hcdpos.le
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (∏ _g : S, Schur.groupConst vMinus D.q T) *
      (∏ _g : B, edgeAbsColConst vMinus D.ρ v Mmax T) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℝ, F = (Bc : ℝ) / (omissionNumber S J ℓ : ℝ) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : ℝ,
      R = ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s * f s := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg
      (Finset.prod_nonneg fun _ _ => zero_le_one.trans (Schur.one_le_groupConst _ _ _))
      (Finset.prod_nonneg fun _ _ => edgeAbsColConst_nonneg hvm hρ0 hρ1 hv0 _)
  have hg0 : ∀ s : MState 𝒢 J ℓ Bc, 0 ≤ memWeight 𝒢 D.q D.n s * schurWeight v s * f s :=
    fun s => mul_nonneg (mul_nonneg (memWeight_nonneg 𝒢 D.q D.n hν s) (pow_nonneg hv0 _))
      (hf0 s)
  -- fixed slot permutations
  have hπ : ∀ π₁ π₂ : ListPerms S B J ℓ,
      ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
          ∑ c : EdgeChoice 𝒢 D.fam Bc,
            (if HasStore c then ‖edgeCoef D θ i (s.permLists π₁) c‖ else 0) *
              f ((edgeTgt D i (s.permLists π₁) c).permLists π₂⁻¹) ≤
        ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C,
          auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) * K *
            ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s * f s *
              (if RareElig rareStoreQ (edgeSign i * D.k) (D.fam ν).C r (s.permLists π₂) then 1
                else 0) := by
    intro π₁ π₂
    have e1 := l38_sum_permLists D.q D.n v π₁
      (fun s : MState 𝒢 J ℓ Bc => ∑ c : EdgeChoice 𝒢 D.fam Bc,
        (if HasStore c then ‖edgeCoef D θ i s c‖ else 0) *
          f ((edgeTgt D i s c).permLists π₂⁻¹))
    rw [hK]
    exact (le_of_eq e1).trans
      (rare_col_choice D θ i hq0 hq1 hρ0 hρ1 hv hvm hVS hVB hν hM' hT hℓT hC π₂ f hf0 hfsym)
  show ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
      ∑ ξ : EdgeFullChoice D Bc,
        (if HasStore ξ.2.1 then ‖edgeFullCoef D (fun _ => 1) θ i s ξ‖ else 0) *
          f (edgeFullTgt D i s ξ) ≤
    patternMass D.fam *
        ((∏ _g : S, Schur.groupConst vMinus D.q T) *
          (∏ _g : B, edgeAbsColConst vMinus D.ρ v Mmax T)) *
        ((Bc : ℝ) / (omissionNumber S J ℓ : ℝ)) *
      ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s * f s
  rw [rare_col_split D θ i v f, ← hK, ← hF, ← hR, ← hcd]
  calc ∑ π₁ : ListPerms S B J ℓ, ∑ π₂ : ListPerms S B J ℓ,
        cd⁻¹ * (cd⁻¹ * ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s *
          ∑ c : EdgeChoice 𝒢 D.fam Bc,
            (if HasStore c then ‖edgeCoef D θ i (s.permLists π₁) c‖ else 0) *
              f ((edgeTgt D i (s.permLists π₁) c).permLists π₂⁻¹))
      ≤ ∑ _π₁ : ListPerms S B J ℓ, ∑ π₂ : ListPerms S B J ℓ,
          cd⁻¹ * (cd⁻¹ * ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C,
            auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) * K *
              ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s * f s *
                (if RareElig rareStoreQ (edgeSign i * D.k) (D.fam ν).C r (s.permLists π₂)
                  then 1 else 0)) :=
        Finset.sum_le_sum fun π₁ _ => Finset.sum_le_sum fun π₂ _ =>
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hπ π₁ π₂) hci0) hci0
    _ = ∑ π₂ : ListPerms S B J ℓ, cd⁻¹ * ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C,
          auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) * K *
            ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s * f s *
              (if RareElig rareStoreQ (edgeSign i * D.k) (D.fam ν).C r (s.permLists π₂)
                then 1 else 0) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hcd, Finset.mul_sum]
        refine Finset.sum_congr rfl fun π₂ _ => ?_
        rw [mul_inv_cancel_left₀ hcdpos.ne']
    _ = ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C, ∑ π₂ : ListPerms S B J ℓ,
          cd⁻¹ * (auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) * K *
            ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s * f s *
              (if RareElig rareStoreQ (edgeSign i * D.k) (D.fam ν).C r (s.permLists π₂)
                then 1 else 0)) :=
        l38_sum_swap3 (γ := fun ν : N => AuxList 𝒢.big (D.fam ν).C)
          (fun _ : ListPerms S B J ℓ => cd⁻¹)
          (fun (π₂ : ListPerms S B J ℓ) (ν : N) (r : AuxList 𝒢.big (D.fam ν).C) =>
            auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) * K *
              ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s * f s *
                (if RareElig rareStoreQ (edgeSign i * D.k) (D.fam ν).C r (s.permLists π₂)
                  then (1 : ℝ) else 0))
    _ = ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C,
          auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) * K *
            ∑ π₂ : ListPerms S B J ℓ, cd⁻¹ *
              ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * schurWeight v s * f s *
                (if RareElig rareStoreQ (edgeSign i * D.k) (D.fam ν).C r (s.permLists π₂)
                  then 1 else 0) := by
        refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun π₂ _ => by ring
    _ ≤ ∑ ν : N, ∑ r : AuxList 𝒢.big (D.fam ν).C,
          auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) * K * (F * R) :=
        Finset.sum_le_sum fun ν _ => Finset.sum_le_sum fun r _ =>
          mul_le_mul_of_nonneg_left
            (by
              rw [hF, hR, hcd]
              exact rare_sum_frac_le hA rareStoreQ rareStoreQ_dvd (D.fam ν).C r
                (fun s : MState 𝒢 J ℓ Bc => memWeight 𝒢 D.q D.n s * schurWeight v s * f s)
                hg0)
            (mul_nonneg (mul_nonneg (Schur.auxWeight_nonneg _ _ _) (NNReal.coe_nonneg _)) hK0)
    _ = ∑ ν : N, ((D.fam ν).supNorm : ℝ) * (K * (F * R)) := by
        refine Finset.sum_congr rfl fun ν _ => ?_
        have h1 : ∑ r : AuxList 𝒢.big (D.fam ν).C,
              auxWeight 𝒢.big (D.fam ν).C r * ((D.fam ν).supNorm : ℝ) * K * (F * R) =
            (∑ r : AuxList 𝒢.big (D.fam ν).C, auxWeight 𝒢.big (D.fam ν).C r) *
              (((D.fam ν).supNorm : ℝ) * (K * (F * R))) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun r _ => by ring
        rw [h1, sum_auxWeight hlaw (D.fam ν).C, one_mul]
    _ = patternMass D.fam * K * F * R := by
        unfold patternMass
        rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun ν _ => by ring

end Col

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
