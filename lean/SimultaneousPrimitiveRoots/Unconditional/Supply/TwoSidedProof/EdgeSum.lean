module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.Statements
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Pairing.Main

/-!
# The edge sums as finite sums

Tools shared by the proofs of `InsertionLink`, `RawStrippingLink` and `ComparisonStrippingLink`
(`[P-06:0287–0370]`).

* `edgeSummand`: the summand of `edgeTerm` (`TwoSidedProof/Objects.lean`) at a position `n`,
  source lists `s`, auxiliary free labels `r` and target lists `s'`; `edgeTerm_eq_finsum`.
* `edgeTerm_eq_sum`: the edge sum is a finite sum over any finite set of positions outside which
  the cutoff `Ψ(n/(xD))` vanishes.
* `dil_pos`, `Config.dil_pos`: the dilation is positive (its factors are primes);
  `Config.dil_le`: every dilation is at most `2 exp(3 J C₀ log L · L^{0.46})`.
* `intPos_shift_one_mul`: the translation by `1 · D` of the operators is `n + D`.
* `Config.small_pos`, `Config.big_pos`: the primes of the active groups of a configuration are
  positive, in the form used for `groupFamily`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference

noncomputable section

/-! ### The summand -/

/-- **The summand of the physical edge sum** `edgeTerm` of the pattern `ν`, at the source position
`n`, the source lists `s`, the auxiliary free labels `r` and the target lists `s'`. -/
def edgeSummand (𝔊 : ActiveGroups) (q₀ : ℝ) {J : ℕ} (ν : Pattern (groupFamily 𝔊).big J 1)
    (x : ℝ) (Ψ : ℝ → ℂ) {H : ℕ} (𝔅 : JointResidueWeight H) (F : ℕ → ℝ) (G : ℕ → ℂ) (n : ℤ)
    (s : Lists (groupFamily 𝔊) J 1) (r : AuxList (groupFamily 𝔊).big ν.C)
    (s' : Lists (groupFamily 𝔊) J 1) : ℂ :=
  Ψ ((n : ℝ) / (x * (dil ν.C s r : ℝ))) / (n : ℂ) *
    ((𝔅.toFun (n : ZMod H) ((n + (dil ν.C s r : ℤ) : ℤ) : ZMod H) : ℝ) : ℂ) *
    ((F n.toNat : ℝ) : ℂ) * G (n + (dil ν.C s r : ℤ)).toNat *
    ((stateMass (groupFamily 𝔊) J 1 *
        (damping intPos (groupFamily 𝔊) J 1 q₀ n *
          damping intPos (groupFamily 𝔊) J 1 q₀ (n + (dil ν.C s r : ℤ))) : ℝ) : ℂ) *
    physCoef intPos (groupFamily 𝔊) q₀ ν 1 0 n s r s'

/-- The edge sum is the sum of its summands. -/
theorem edgeTerm_eq_finsum (𝔊 : ActiveGroups) (q₀ : ℝ) {J : ℕ}
    (ν : Pattern (groupFamily 𝔊).big J 1) (x : ℝ) (Ψ : ℝ → ℂ) {H : ℕ}
    (𝔅 : JointResidueWeight H) (F : ℕ → ℝ) (G : ℕ → ℂ) :
    edgeTerm 𝔊 q₀ ν x Ψ 𝔅 F G =
      ∑ᶠ n : ℤ, ∑ s : Lists (groupFamily 𝔊) J 1, ∑ r : AuxList (groupFamily 𝔊).big ν.C,
        ∑ s' : Lists (groupFamily 𝔊) J 1, edgeSummand 𝔊 q₀ ν x Ψ 𝔅 F G n s r s' := rfl

/-- The summand vanishes where the cutoff vanishes. -/
theorem edgeSummand_eq_zero {𝔊 : ActiveGroups} {q₀ : ℝ} {J : ℕ}
    {ν : Pattern (groupFamily 𝔊).big J 1} {x : ℝ} {Ψ : ℝ → ℂ} {H : ℕ}
    {𝔅 : JointResidueWeight H} {F : ℕ → ℝ} {G : ℕ → ℂ} {n : ℤ}
    {s : Lists (groupFamily 𝔊) J 1} {r : AuxList (groupFamily 𝔊).big ν.C}
    (s' : Lists (groupFamily 𝔊) J 1)
    (h : Ψ ((n : ℝ) / (x * (dil ν.C s r : ℝ))) = 0) :
    edgeSummand 𝔊 q₀ ν x Ψ 𝔅 F G n s r s' = 0 := by
  unfold edgeSummand
  rw [h, zero_div, zero_mul, zero_mul, zero_mul, zero_mul, zero_mul]

/-- **The edge sum is a finite sum** over any finite set `T` of positions outside which the
cutoff vanishes. -/
theorem edgeTerm_eq_sum (𝔊 : ActiveGroups) (q₀ : ℝ) {J : ℕ}
    (ν : Pattern (groupFamily 𝔊).big J 1) (x : ℝ) (Ψ : ℝ → ℂ) {H : ℕ}
    (𝔅 : JointResidueWeight H) (F : ℕ → ℝ) (G : ℕ → ℂ) (T : Finset ℤ)
    (hT : ∀ n : ℤ, n ∉ T → ∀ (s : Lists (groupFamily 𝔊) J 1)
      (r : AuxList (groupFamily 𝔊).big ν.C), Ψ ((n : ℝ) / (x * (dil ν.C s r : ℝ))) = 0) :
    edgeTerm 𝔊 q₀ ν x Ψ 𝔅 F G =
      ∑ n ∈ T, ∑ s : Lists (groupFamily 𝔊) J 1, ∑ r : AuxList (groupFamily 𝔊).big ν.C,
        ∑ s' : Lists (groupFamily 𝔊) J 1, edgeSummand 𝔊 q₀ ν x Ψ 𝔅 F G n s r s' := by
  rw [edgeTerm_eq_finsum]
  refine finsum_eq_sum_of_support_subset _ fun n hn => ?_
  by_contra hnT
  refine hn ?_
  exact Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun r _ =>
    Finset.sum_eq_zero fun s' _ =>
      edgeSummand_eq_zero s' (hT n (fun h => hnT (Finset.mem_coe.mpr h)) s r)

/-! ### Dilations -/

/-- The dilation is positive when all the labels are. -/
theorem dil_pos {S B : Type} [Fintype S] [Fintype B] {𝒢 : GroupFamily S B} {J ℓ : ℕ}
    (hS : ∀ g, ∀ p ∈ 𝒢.small g, 0 < p) (hB : ∀ g, ∀ p ∈ 𝒢.big g, 0 < p)
    (C : B → Finset (Fin J)) (x : Lists 𝒢 J ℓ) (r : AuxList 𝒢.big C) : 0 < dil C x r := by
  unfold dil smallDil bigDil
  refine Nat.mul_pos
    (Finset.prod_pos fun g _ => Finset.prod_pos fun i _ => hS g _ (x.1 g (Sum.inl i)).2)
    (Finset.prod_pos fun g _ => Nat.mul_pos (Finset.prod_pos fun i _ => ?_)
      (Finset.prod_pos fun i _ => hB g _ (r g i).2))
  split_ifs
  · exact Nat.one_pos
  · exact hB g _ (x.2 g (Sum.inl i)).2

/-- The translation by `1 · D` of the operators is `n + D`. -/
theorem intPos_shift_one_mul (n : ℤ) (D : ℕ) : intPos.shift (1 * (D : ℤ)) n = n + (D : ℤ) := by
  show n + 1 * (D : ℤ) = n + (D : ℤ)
  rw [one_mul]

namespace Config

variable {d : ℕ} {D : FixedData} {x : ℝ}

/-- The primes of the small groups of a configuration are positive. -/
theorem small_pos (I : Config d D x) (g : Fin I.𝔊.numSmall) (p : ℕ)
    (hp : p ∈ (groupFamily I.𝔊).small g) : 0 < p :=
  (I.groups.prime (Sum.inl g) p hp).pos

/-- The primes of the big groups of a configuration are positive. -/
theorem big_pos (I : Config d D x) (g : Fin I.𝔊.numBig) (p : ℕ)
    (hp : p ∈ (groupFamily I.𝔊).big g) : 0 < p :=
  (I.groups.prime (Sum.inr g) p hp).pos

/-- Every dilation of a configuration is positive. -/
theorem dil_pos (I : Config d D x) {J : ℕ} (C : Fin I.𝔊.numBig → Finset (Fin J))
    (s : Lists (groupFamily I.𝔊) J 1) (r : AuxList (groupFamily I.𝔊).big C) : 0 < dil C s r :=
  TwoSidedProof.dil_pos I.small_pos I.big_pos C s r

/-- **Every dilation of a configuration is at most `2 exp(3 J C₀ log L · L^{0.46})`**
(`[P-06:0275]`: "`P ≤ exp(O_J(L^{.46} log L)) = x^{o(1)}`"). -/
theorem dil_le (I : Config d D x) (hL : 1 ≤ Real.log x) {J : ℕ}
    (C : Fin I.𝔊.numBig → Finset (Fin J)) (s : Lists (groupFamily I.𝔊) J 1)
    (r : AuxList (groupFamily I.𝔊).big C) :
    (dil C s r : ℝ) ≤ 2 * Real.exp (3 * ((J : ℝ) * D.P.C₀) *
      (Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ))) := by
  have h1 : (dil C s r : ℝ) ≤ (Pairing.dilBound (groupFamily I.𝔊) J : ℝ) := by
    exact_mod_cast Pairing.dil_le_dilBound C s r
  have he : Pairing.stepBound (groupFamily I.𝔊) J 1 = Pairing.dilBound (groupFamily I.𝔊) J := by
    unfold Pairing.stepBound
    rw [Int.natAbs_one, one_mul]
  have hk : |((1 : ℤ) : ℝ)| ≤ Real.log x ^ (0 : ℝ) := by
    rw [Int.cast_one, abs_one, Real.rpow_zero]
  have h2 := Pairing.stepBound_add_one_le I.primeGroups hL J (k := 1) one_ne_zero hk
  have h3 : (Pairing.dilBound (groupFamily I.𝔊) J : ℝ) + 1 ≤
      2 * (Real.log x ^ (0 : ℝ) * Real.exp (3 * ((J : ℝ) * D.P.C₀) *
        (Real.log (Real.log x) * Real.log x ^ (0.46 : ℝ)))) := by
    rw [← he]
    exact h2
  rw [Real.rpow_zero, one_mul] at h3
  linarith

end Config

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
