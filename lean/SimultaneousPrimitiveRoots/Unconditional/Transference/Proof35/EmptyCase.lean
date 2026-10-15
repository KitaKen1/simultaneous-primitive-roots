module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.History
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.ResidueModel
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Sanity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Sanity check: the memory identity without groups

`memoryIdentity_of_isEmpty` proves the identity of [S] Lemma 3.7
(`verification/stage7-sources/S-02.tex`, lines 523–535) for an empty family of groups and an even
number `N = 2R` of edges:

`phaseSum θ = (∏_{p big} b_p) · distinctSum Bc θ`,

both sides being `|∑_ν K_ν|^{2R}`. Without groups a memory state is a point, `D = 1`, the visit
operations are the identity, the edge `i` multiplies by `(∑_ν K_ν) e(θ k)` for even `i` and by
`conj(∑_ν K_ν) e(-θ k)` for odd `i`, and there are no births. On the physical side this is
`physOp_mul_physAdj_of_isEmpty` of `Transference/Sanity.lean`.

The check guards the bookkeeping of the definitions of `Operators.lean` and `History.lean` which
does not involve a prime: the orientation of the edges (the edge `0` is a row transition of `𝒜`),
the phases `e(θ σ_i k D)` and their cancellation on a closed walk, the normalization of the
symmetrizations and of the boundary, and the convention `N = 2R`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators ComplexConjugate

noncomputable section

set_option linter.unusedSectionVars false

theorem expUnit_mul_expUnit (a b : ℝ) : expUnit a * expUnit b = expUnit (a + b) := by
  unfold expUnit
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem expUnit_zero : expUnit 0 = 1 := by
  simp [expUnit]

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] [IsEmpty S]
  [IsEmpty B] {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N]

/-! ### The physical side -/

/-- Without groups, `phaseSum θ = |∑_ν K_ν|^{2R}` for every `θ`. -/
theorem phaseSum_of_isEmpty (𝒢 : GroupFamily S B) (q : ℝ) (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ)
    (ζ : ℝ) (R : ℕ) (θ : ℝ) :
    phaseSum 𝒢 q 𝔉 k ζ R θ =
      ((∑ ν, (𝔉 ν).K default default default) *
        conj (∑ ν, (𝔉 ν).K default default default)) ^ R := by
  have hpow : ∀ (R : ℕ) (G : PState (tagModel 𝒢.allPrimes) 𝒢 J ℓ → ℂ),
      ((physOp (tagModel 𝒢.allPrimes) 𝒢 q 𝔉 k ζ *
          physAdj (tagModel 𝒢.allPrimes) 𝒢 q 𝔉 k ζ) ^ R) G =
        ((∑ ν, (𝔉 ν).K default default default) *
          conj (∑ ν, (𝔉 ν).K default default default)) ^ R • G := by
    intro R
    induction R with
    | zero =>
      intro G
      rw [pow_zero, pow_zero, one_smul]
      rfl
    | succ R ih =>
      intro G
      rw [pow_succ, Module.End.mul_apply, physOp_mul_physAdj_of_isEmpty, ih, smul_smul,
        ← pow_succ]
  have hmass : stateMass 𝒢 J ℓ = 1 := by
    unfold stateMass
    simp
  have hterm : ∀ y : ResVec 𝒢.allPrimes,
      pairUnit (tagModel 𝒢.allPrimes) 𝒢 J ℓ (tagStart y)
          (((physOp (tagModel 𝒢.allPrimes) 𝒢 q 𝔉 k ζ *
              physAdj (tagModel 𝒢.allPrimes) 𝒢 q 𝔉 k ζ) ^ R) (phaseVec 𝒢 θ)) =
        ((∑ ν, (𝔉 ν).K default default default) *
          conj (∑ ν, (𝔉 ν).K default default default)) ^ R := by
    intro y
    have hv : ∀ x : Lists 𝒢 J ℓ, phaseVec 𝒢 θ (tagStart y, x) = 1 := by
      intro x
      unfold phaseVec
      rw [if_pos (isPhys_of_isEmpty _ _)]
      show expUnit (θ * ((0 : ℤ) : ℝ)) = 1
      rw [Int.cast_zero, mul_zero, expUnit_zero]
    unfold pairUnit
    rw [hpow, Fintype.sum_prod_type, Fintype.sum_unique, Fintype.sum_unique,
      if_pos (isPhys_of_isEmpty _ _), hmass, Pi.smul_apply, hv, smul_eq_mul,
      Complex.ofReal_one, one_mul, mul_one]
  have hne : (Fintype.card (ResVec 𝒢.allPrimes) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  unfold phaseSum
  rw [Finset.sum_congr rfl fun y _ => hterm y, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, Complex.ofReal_natCast, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]

/-! ### The memory side -/

section Memory

variable {Bc : ℕ}

theorem memTotal_of_isEmpty (s : MState 𝒢 J ℓ Bc) : memTotal s = 0 := by
  unfold memTotal
  exact Finset.sum_eq_zero fun g _ => isEmptyElim g

theorem memZeros_of_isEmpty (s : MState 𝒢 J ℓ Bc) : memZeros s = 0 := by
  unfold memZeros
  exact Finset.sum_eq_zero fun g _ => isEmptyElim g

theorem smallPrimes_of_isEmpty (𝒢 : GroupFamily S B) : smallPrimes 𝒢 = ∅ := by
  unfold smallPrimes
  rw [Finset.univ_eq_empty, Finset.biUnion_empty]

theorem notMem_smallPrimes_of_isEmpty (𝒢 : GroupFamily S B) (n : ℕ) : n ∉ smallPrimes 𝒢 := by
  rw [smallPrimes_of_isEmpty]
  exact Finset.notMem_empty n

theorem smallDamping_of_isEmpty (q : ℝ) (y : ResVec (smallPrimes 𝒢)) :
    smallDamping 𝒢 J ℓ q y = 1 := by
  unfold smallDamping
  rw [Finset.univ_eq_empty, Finset.sum_empty, Fintype.card_eq_zero]
  simp

/-- Without groups every memory state has mass one. -/
theorem memWeight_of_isEmpty (q : ℝ) (n : ℕ) (s : MState 𝒢 J ℓ Bc) :
    memWeight 𝒢 q n s = 1 := by
  have hs : IsSmallState 𝒢 s.y s.xs := ⟨fun g => isEmptyElim g, fun g => isEmptyElim g⟩
  have h1 : haarMass (smallPrimes 𝒢) = 1 := by
    unfold haarMass
    have : IsEmpty {p : ℕ // p ∈ smallPrimes 𝒢} :=
      ⟨fun p => notMem_smallPrimes_of_isEmpty 𝒢 p.1 p.2⟩
    rw [Fintype.card_unique, Nat.cast_one, inv_one]
  have h2 : smallListMass 𝒢 J ℓ = 1 := by
    unfold smallListMass
    exact Fintype.prod_empty _
  have h3 : bigListMass 𝒢 q n s.xb = 1 := by
    unfold bigListMass
    exact Fintype.prod_empty _
  have h4 : memMass 𝒢 q n s.mem = 1 := by
    unfold memMass
    exact Fintype.prod_empty _
  unfold memWeight
  rw [if_pos hs, h1, h2, h3, h4]
  norm_num

theorem emptyVec_of_isEmpty (s : MState 𝒢 J ℓ Bc) : emptyVec 𝒢 J ℓ Bc s = 1 := by
  unfold emptyVec
  rw [if_pos (memTotal_of_isEmpty s)]

/-- Without groups the visit operations have the coefficient one. -/
theorem ghostCoef_of_isEmpty (D : MemData 𝒢 J ℓ N) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (c : GhostChoice 𝒢 Bc) : ghostCoef D i s c = 1 := by
  have h : memTotal s ≤ Bc ∧ (∑ g, ghostNewSize (s.mem g) (c g)) ≤ Bc := by
    rw [memTotal_of_isEmpty, Finset.univ_eq_empty, Finset.sum_empty]
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  unfold ghostCoef
  rw [if_pos h]
  exact Fintype.prod_empty _

/-- The value of an edge without groups: `K_ν e(θ k)` on a forward edge and
`conj(K_ν) e(-θ k)` on a backward edge. -/
def emptyEdgeValue (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) (ν : N) : ℂ :=
  (if i % 2 = 0 then (D.fam ν).K default default default
    else conj ((D.fam ν).K default default default)) *
    expUnit (θ * ((edgeSign i * D.k : ℤ) : ℝ))

/-- Without groups the coefficient of an edge is `emptyEdgeValue`. -/
theorem edgeCoef_of_isEmpty (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (c : EdgeChoice 𝒢 D.fam Bc) : edgeCoef D θ i s c = emptyEdgeValue D θ i c.ν := by
  have hdil : edgeDil D s c = 1 := by
    unfold edgeDil
    exact dil_of_isEmpty _ _ _
  have hstep : edgeStep D i s c = edgeSign i * D.k := by
    unfold edgeStep
    rw [hdil, Nat.cast_one, mul_one]
  have hK : ∀ (a b : LabelList 𝒢.big J ℓ) (r : AuxList 𝒢.big (D.fam c.ν).C),
      (D.fam c.ν).K a b r = (D.fam c.ν).K default default default := by
    intro a b r
    rw [Subsingleton.elim a default, Subsingleton.elim b default, Subsingleton.elim r default]
  have hmult : edgeMultiplier D i s c =
      if i % 2 = 0 then (D.fam c.ν).K default default default
      else conj ((D.fam c.ν).K default default default) := by
    unfold edgeMultiplier
    rw [hdil, hK s.xb c.xbT c.r, hK c.xbT s.xb c.r, Nat.cast_one, Complex.one_cpow, mul_one]
  have h1 : memTotal s ≤ Bc := by
    rw [memTotal_of_isEmpty]
    exact Nat.zero_le _
  have h2 : (∑ g, (edgeNewList D i s c g).length) ≤ Bc := by
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact Nat.zero_le _
  unfold edgeCoef
  split_ifs with hc
  · have hsd : smallDamping 𝒢 J ℓ D.q
        ((resModel (smallPrimes 𝒢)).shift (edgeSign i * D.k) s.y) = 1 :=
      smallDamping_of_isEmpty _ _
    rw [hmult, hstep, memZeros_of_isEmpty, memZeros_of_isEmpty, smallDamping_of_isEmpty, hsd]
    unfold emptyEdgeValue
    simp [auxWeight]
  · exact absurd ⟨h1, h2, ⟨fun g => isEmptyElim g, fun g => isEmptyElim g⟩,
      ⟨fun g => isEmptyElim g, fun g => isEmptyElim g⟩, fun g => isEmptyElim g,
      fun g => isEmptyElim g, fun g => isEmptyElim g, fun g => isEmptyElim g,
      fun g => isEmptyElim g, fun g => isEmptyElim g⟩ hc

/-- Without groups the coefficient of the whole edge operation is `emptyEdgeValue`. -/
theorem edgeFullCoef_of_isEmpty (D : MemData 𝒢 J ℓ N) (θ : ℝ) (i : ℕ) (s : MState 𝒢 J ℓ Bc)
    (ξ : EdgeFullChoice D Bc) :
    edgeFullCoef D (fun _ => 1) θ i s ξ = emptyEdgeValue D θ i ξ.2.1.ν := by
  have hc : (Fintype.card (ListPerms S B J ℓ) : ℂ)⁻¹ = 1 := by
    rw [Fintype.card_prod, Fintype.card_unique, Fintype.card_unique]
    norm_num
  unfold edgeFullCoef
  rw [hc, edgeCoef_of_isEmpty]
  simp only [one_mul, mul_one]

/-- Without groups the weight of a history is the product of the values of its edges. -/
theorem History.weight_of_isEmpty (D : MemData 𝒢 J ℓ N) (θ : ℝ) (h : History D Bc) :
    h.weight θ = ∏ i : Fin D.n, emptyEdgeValue D θ i.val (h.edge i).2.1.ν := by
  unfold History.weight
  rw [memWeight_of_isEmpty, ghostCoef_of_isEmpty, emptyVec_of_isEmpty]
  simp only [Complex.ofReal_one, one_mul, mul_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ghostCoef_of_isEmpty, Complex.ofReal_one, one_mul, edgeFullCoef_of_isEmpty]

/-- Without groups an edge choice is determined by its pattern. -/
theorem edgeChoice_ext_of_isEmpty {𝔉 : N → Pattern 𝒢.big J ℓ} (c c' : EdgeChoice 𝒢 𝔉 Bc)
    (h : c.ν = c'.ν) : c = c' := by
  rcases c with ⟨ν, r, st, pr, xsT, xbT⟩
  rcases c' with ⟨ν', r', st', pr', xsT', xbT'⟩
  have h' : ν = ν' := h
  subst h'
  have hr : r = r' := funext fun g => isEmptyElim g
  have hst : st = st' := funext fun g => isEmptyElim g
  have hpr : pr = pr' := funext fun g => isEmptyElim g
  have hxs : xsT = xsT' := funext fun g => isEmptyElim g
  have hxb : xbT = xbT' := funext fun g => isEmptyElim g
  subst hr hst hpr hxs hxb
  rfl

theorem edgeFullChoice_ext_of_isEmpty (D : MemData 𝒢 J ℓ N) (ξ ξ' : EdgeFullChoice D Bc)
    (h : ξ.2.1.ν = ξ'.2.1.ν) : ξ = ξ' :=
  Prod.ext (Prod.ext (funext fun g => isEmptyElim g) (funext fun g => isEmptyElim g))
    (Prod.ext (edgeChoice_ext_of_isEmpty _ _ h)
      (Prod.ext (funext fun g => isEmptyElim g) (funext fun g => isEmptyElim g)))

/-- Without groups a history is determined by the patterns of its edges. -/
theorem History.ext_of_isEmpty (D : MemData 𝒢 J ℓ N) (h h' : History D Bc)
    (hν : ∀ i, (h.edge i).2.1.ν = (h'.edge i).2.1.ν) : h = h' := by
  rcases h with ⟨y, xs, xb, gh, ed⟩
  rcases h' with ⟨y', xs', xb', gh', ed'⟩
  have hy : y = y' := funext fun p => absurd p.2 (notMem_smallPrimes_of_isEmpty 𝒢 p.1)
  have hxs : xs = xs' := funext fun g => isEmptyElim g
  have hxb : xb = xb' := funext fun g => isEmptyElim g
  have hgh : gh = gh' := funext fun _ => funext fun g => isEmptyElim g
  have hed : ed = ed' := funext fun i => edgeFullChoice_ext_of_isEmpty D _ _ (hν i)
  subst hy hxs hxb hgh hed
  rfl

/-- Without groups a history is the sequence of the patterns of its edges. -/
def emptyHistEquiv (D : MemData 𝒢 J ℓ N) (Bc : ℕ) : History D Bc ≃ (Fin D.n → N) where
  toFun h := fun i => (h.edge i).2.1.ν
  invFun p :=
    ⟨fun _ => 0, fun g => isEmptyElim g, fun g => isEmptyElim g, fun _ g => isEmptyElim g,
      fun i => ((fun g => isEmptyElim g, fun g => isEmptyElim g),
        ⟨p i, fun g => isEmptyElim g, fun g => isEmptyElim g, fun g => isEmptyElim g,
          fun g => isEmptyElim g, fun g => isEmptyElim g⟩,
        (fun g => isEmptyElim g, fun g => isEmptyElim g))⟩
  left_inv _ := History.ext_of_isEmpty D _ _ fun _ => rfl
  right_inv _ := rfl

/-- Without groups the path integral is `∏_i ∑_ν (value of the edge i)`. -/
theorem distinctSum_of_isEmpty (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ) :
    distinctSum D Bc θ = ∏ i : Fin D.n, ∑ ν, emptyEdgeValue D θ i.val ν := by
  classical
  have hdist : ∀ h : History D Bc, Graph.PerformedBirthsDistinct h.birth :=
    fun h a => isEmptyElim a
  have hw : ∀ h : History D Bc,
      (if Graph.PerformedBirthsDistinct h.birth then h.weight θ else 0) =
        ∏ i : Fin D.n, emptyEdgeValue D θ i.val (h.edge i).2.1.ν := by
    intro h
    rw [if_pos (hdist h), History.weight_of_isEmpty]
  unfold distinctSum
  rw [Finset.sum_congr rfl fun h _ => hw h, Fintype.prod_sum]
  exact Fintype.sum_equiv (emptyHistEquiv D Bc) _ _ fun h => rfl

end Memory

/-! ### The identity -/

/-- The product of the values of the edges of a closed walk of `2R` edges is `(a b)^R`. -/
theorem prod_alternating (a b : ℂ) (f : ℕ → ℂ) (hf : ∀ i, f i = if i % 2 = 0 then a else b)
    (R : ℕ) : ∏ i ∈ Finset.range (2 * R), f i = (a * b) ^ R := by
  induction R with
  | zero => simp
  | succ R ih =>
    have e : 2 * (R + 1) = 2 * R + 1 + 1 := by ring
    have h0 : (2 * R) % 2 = 0 := by omega
    have h1 : ¬(2 * R + 1) % 2 = 0 := by omega
    rw [e, Finset.prod_range_succ, Finset.prod_range_succ, ih, hf (2 * R), hf (2 * R + 1),
      if_pos h0, if_neg h1, pow_succ]
    ring

/-- **The memory identity (Lemma 3.7) without groups** [S-02:0523–0535]: for an empty family of
groups, every cutoff and an even number `N = 2R` of edges,
`phaseSum θ = (∏_{p big} b_p) · distinctSum Bc θ`; both sides are `|∑_ν K_ν|^{2R}`. -/
theorem memoryIdentity_of_isEmpty (D : MemData 𝒢 J ℓ N) (Bc R : ℕ) (hn : D.n = 2 * R)
    (θ : ℝ) :
    phaseSum 𝒢 D.q D.fam D.k D.ζ R θ =
      ((baselineProd (bigPrimes 𝒢) D.q D.n : ℝ) : ℂ) * distinctSum D Bc θ := by
  have hbase : baselineProd (bigPrimes 𝒢) D.q D.n = 1 := by
    unfold baselineProd bigPrimes
    rw [Finset.univ_eq_empty, Finset.biUnion_empty, Finset.prod_empty]
  have e1 : ((1 * D.k : ℤ) : ℝ) = (D.k : ℝ) := by rw [one_mul]
  have e2 : ((-1 * D.k : ℤ) : ℝ) = -(D.k : ℝ) := by rw [neg_one_mul, Int.cast_neg]
  have hval : ∀ i : ℕ, ∑ ν, emptyEdgeValue D θ i ν =
      if i % 2 = 0 then
        (∑ ν, (D.fam ν).K default default default) * expUnit (θ * (D.k : ℝ))
      else conj (∑ ν, (D.fam ν).K default default default) * expUnit (θ * (-(D.k : ℝ))) := by
    intro i
    unfold emptyEdgeValue edgeSign
    split_ifs
    · rw [← Finset.sum_mul, e1]
    · rw [← Finset.sum_mul, map_sum, e2]
  have hphase : expUnit (θ * (D.k : ℝ)) * expUnit (θ * (-(D.k : ℝ))) = 1 := by
    have e : θ * (D.k : ℝ) + θ * (-(D.k : ℝ)) = 0 := by ring
    rw [expUnit_mul_expUnit, e, expUnit_zero]
  rw [phaseSum_of_isEmpty, hbase, Complex.ofReal_one, one_mul, distinctSum_of_isEmpty,
    Fin.prod_univ_eq_prod_range (fun i => ∑ ν, emptyEdgeValue D θ i ν) D.n, hn,
    prod_alternating _ _ _ hval R]
  congr 1
  calc (∑ ν, (D.fam ν).K default default default) *
        conj (∑ ν, (D.fam ν).K default default default)
      = (∑ ν, (D.fam ν).K default default default) *
          conj (∑ ν, (D.fam ν).K default default default) *
          (expUnit (θ * (D.k : ℝ)) * expUnit (θ * (-(D.k : ℝ)))) := by
        rw [hphase, mul_one]
    _ = (∑ ν, (D.fam ν).K default default default) * expUnit (θ * (D.k : ℝ)) *
          (conj (∑ ν, (D.fam ν).K default default default) *
            expUnit (θ * (-(D.k : ℝ)))) := by ring

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
