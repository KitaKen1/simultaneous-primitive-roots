module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.Statements

/-!
# Sanity checks of the objects of `TwoSidedProof/Objects.lean`

These lemmas are not hypotheses of the proved chain. They record that the objects written for the
active groups of [P] §6 (`groupFamily 𝔊`, `ℓ = 1`) are the ones of the imported propositions
(written for `Config.primeGroups`, `FixedData.params`):

* `edgeTotal_eq_sum_family`: the total residual edge pairing `Config.edgeTotal` (the raw edge sum
  plus the comparison edge sums) is the sum of `edgeTerm` over the residual family
  `Config.family` of `PairingAt` and `SchurAt`;
* `activeWeight_eq_activeCoeff`: (cor:marked-weight) is the scalar factor `activeCoeff` times the
  sum of the test over the represented lists;
* `markCount_inl`, `markCount_inr`: `t_g = 1` on small groups and `|C_g| + 1` on big groups;
* `primeGroups_toGroupFamily`, `params_ℓ`, `params_q`: the bridge to [S]'s prime groups.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference

noncomputable section

variable {d : ℕ} {D : FixedData} {x : ℝ}

/-- The prime groups of a configuration have the small and big groups of the active groups. -/
theorem primeGroups_toGroupFamily (I : Config d D x) :
    I.primeGroups.toGroupFamily = groupFamily I.𝔊 := rfl

/-- `ℓ = 1` (`[P-06:0256–0258]`). -/
theorem params_ℓ (D : FixedData) : D.params.ℓ = 1 := rfl

/-- [S]'s damping `q` is `q₀` (`[P-06:0186]`). -/
theorem params_q (D : FixedData) : D.params.q = D.q₀ := rfl

/-- `t_g = 1` on a small group. -/
theorem markCount_inl (𝔊 : ActiveGroups) {J : ℕ} (C : Fin 𝔊.numBig → Finset (Fin J))
    (i : Fin 𝔊.numSmall) : markCount 𝔊 C (Sum.inl i) = 1 := rfl

/-- `t_g = |C_g| + 1` on a big group. -/
theorem markCount_inr (𝔊 : ActiveGroups) {J : ℕ} (C : Fin 𝔊.numBig → Finset (Fin J))
    (j : Fin 𝔊.numBig) : markCount 𝔊 C (Sum.inr j) = (C j).card + 1 := rfl

/-- (cor:marked-weight): the active marked weight is its scalar factor times the sum of the test
over the represented lists. -/
theorem activeWeight_eq_activeCoeff (𝔊 : ActiveGroups) (q₀ : ℝ) (t : 𝔊.Index → ℕ)
    (test : ((g : 𝔊.Index) → Fin (t g) → ℕ) → ℂ) (n : ℕ) :
    𝔊.activeWeight q₀ t test n =
      ((activeCoeff 𝔊 q₀ t n : ℝ) : ℂ) * ∑ 𝔭 ∈ 𝔊.representedLists t n, test 𝔭 := rfl

/-- **The total residual edge pairing is the edge sum of the residual family** of
Proposition 6.3: the raw pattern (`none`) and the comparison patterns (`some C`). -/
theorem edgeTotal_eq_sum_family (I : Config d D x) {H : ℕ} (𝔅 : JointResidueWeight H)
    (J m₀ : ℕ) (qs hs xs : ℝ) :
    I.edgeTotal 𝔅 J m₀ qs hs xs =
      ∑ ν : ComparisonIndex (Fin I.𝔊.numBig) I.blocks J m₀,
        edgeTerm I.𝔊 D.q₀ (I.family J m₀ qs hs xs ν) x D.Ψ 𝔅
          (centeredCore D.q D.𝔞 x I.S) I.G := by
  rw [Fintype.sum_option]
  rfl

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
