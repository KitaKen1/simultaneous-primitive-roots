module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof.Statements
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Pairing.Adjoint
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Schur.RowSums

/-!
# The pairing `⟨f, 𝒜 g⟩` of two mark-free vectors as an edge sum

This file is not a hypothesis of the proved chain (`TwoSidedProof/Assembly.lean`). It proves the
exact identity behind the first sentence of `[P-06:0262–0266]` ("Use endpoint vectors with values
`F_x(n)` and `G(n')`, respectively …"), which the proof of `InsertionLink` needs: for a first
vector with value `f_n` at every physical state at the position `n ∈ I` and a second vector with
value `g_{n'}` at every state at the position `n'`,

`⟨f, 𝒜 g⟩ = ∑_{n ∈ I} conj(f_n) ∑_ν ∑_{x, r, x'} ∏_g V_g^{-M} · (row coefficient of ν) · g_{n + kD}`

(`pairMarkFree_physOp_markFree`). The symmetrizations on both sides of `𝒜` disappear: a
mark-free vector is fixed by symmetrization (`physSym_markFree`), and the pairing with a mark-free
vector is unchanged by symmetrizing the other vector (`pairUnit_physSym`, from the
self-adjointness `Transference.Pairing.fib_physSym`). The summand is the one of `edgeTerm`
(`TwoSidedProof/Objects.lean`) before the cutoff, the joint weight and the extra half-dampings
are put into `f` and `g`.

Everything here is for an arbitrary position model and an arbitrary family of groups.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof

open SimultaneousPrimitiveRoots.Unconditional.Transference
open scoped BigOperators ComplexConjugate

noncomputable section

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

/-- `⟨u_n, G⟩` is the part at `n` of the inner product of the constant function `1` with `G`. -/
theorem pairUnit_eq_fib_one (𝔭 : PosModel) (𝒢 : GroupFamily S B) (J ℓ : ℕ) (n : 𝔭.Pos)
    (G : PState 𝔭 𝒢 J ℓ → ℂ) :
    pairUnit 𝔭 𝒢 J ℓ n G = Pairing.fib 𝔭 𝒢 J ℓ n (fun _ => 1) G := by
  rw [Pairing.pairUnit_eq_sum]
  unfold Pairing.fib
  refine Finset.sum_congr rfl fun x _ => ?_
  show (Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) : ℂ) * G (n, x) =
    (Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) : ℂ) * (conj (1 : ℂ) * G (n, x))
  rw [map_one, one_mul]

/-- **The pairing with `u_n` does not see a symmetrization**: `⟨u_n, Sym W⟩ = ⟨u_n, W⟩`. -/
theorem pairUnit_physSym (𝔭 : PosModel) (𝒢 : GroupFamily S B) (J ℓ : ℕ) (n : 𝔭.Pos)
    (W : PState 𝔭 𝒢 J ℓ → ℂ) :
    pairUnit 𝔭 𝒢 J ℓ n (physSym 𝔭 𝒢 J ℓ W) = pairUnit 𝔭 𝒢 J ℓ n W := by
  rw [pairUnit_eq_fib_one, Pairing.fib_physSym, Schur.physSym_const, ← pairUnit_eq_fib_one]

/-- **A mark-free vector is fixed by symmetrization.** -/
theorem physSym_markFree (𝔭 : PosModel) (𝒢 : GroupFamily S B) (J ℓ : ℕ) (gn : 𝔭.Pos → ℂ) :
    physSym 𝔭 𝒢 J ℓ (fun s : PState 𝔭 𝒢 J ℓ => gn s.1) = fun s => gn s.1 := by
  funext s
  obtain ⟨n, x⟩ := s
  have h1 : ∑ y : Lists 𝒢 J ℓ, symKernel x y * (1 : ℂ) = 1 := by
    have h := congrFun (Schur.physSym_const 𝔭 𝒢 J ℓ (1 : ℂ)) (n, x)
    rw [Pairing.physSym_apply_mk] at h
    exact h
  have h2 : ∑ y : Lists 𝒢 J ℓ, symKernel x y = 1 :=
    (Finset.sum_congr rfl fun y _ => (mul_one _).symm).trans h1
  rw [Pairing.physSym_apply_mk]
  show ∑ y : Lists 𝒢 J ℓ, symKernel x y * gn n = gn n
  rw [← Finset.sum_mul, h2, one_mul]

/-- **The pairing of two mark-free vectors is an edge sum** (`[P-06:0262–0266]`): for
`f = ∑_{n ∈ I} f_n u_n` and `g(n', x') = g_{n'}`,

`⟨f, 𝒜 g⟩ = ∑_{n ∈ I} conj(f_n) ∑_ν ∑_x ∑_{(r, x')}
    ∏_g V_g^{-M} · physCoef_ν(n, x, r, x') · g_{n + k D(x, r)}`.

The conditions "both states are physical, the target has the shared labels, no free label occurs
in the lists" are inside `physCoef`. -/
theorem pairMarkFree_physOp_markFree (𝔭 : PosModel) (𝒢 : GroupFamily S B) (q : ℝ) {J ℓ : ℕ}
    {N : Type} [Fintype N] (𝔉 : N → Pattern 𝒢.big J ℓ) (k : ℤ) (ζ : ℝ) (I : Finset 𝔭.Pos)
    (fn gn : 𝔭.Pos → ℂ) :
    pairMarkFree 𝔭 𝒢 J ℓ I fn (physOp 𝔭 𝒢 q 𝔉 k ζ (fun s => gn s.1)) =
      ∑ n ∈ I, conj (fn n) * ∑ ν, ∑ x : Lists 𝒢 J ℓ,
        ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
          (stateMass 𝒢 J ℓ : ℂ) * (physCoef 𝔭 𝒢 q (𝔉 ν) k ζ n x ξ.1 ξ.2 *
            gn (𝔭.shift (k * dil (𝔉 ν).C x ξ.1) n)) := by
  unfold pairMarkFree
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  rw [Pairing.physOp_apply, physSym_markFree 𝔭 𝒢 J ℓ gn, pairUnit_physSym,
    Pairing.pairUnit_eq_sum]
  have key : ∀ x : Lists 𝒢 J ℓ,
      (Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) : ℂ) *
          (∑ ν, physRow 𝔭 𝒢 q (𝔉 ν) k ζ (fun s : PState 𝔭 𝒢 J ℓ => gn s.1)) (n, x) =
        ∑ ν, ∑ ξ : AuxList 𝒢.big (𝔉 ν).C × Lists 𝒢 J ℓ,
          (stateMass 𝒢 J ℓ : ℂ) * (physCoef 𝔭 𝒢 q (𝔉 ν) k ζ n x ξ.1 ξ.2 *
            gn (𝔭.shift (k * dil (𝔉 ν).C x ξ.1) n)) := by
    intro x
    rw [Finset.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [Pairing.physRow_apply_mk, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    show (Pairing.physWeight 𝔭 𝒢 J ℓ (n, x) : ℂ) *
        (physCoef 𝔭 𝒢 q (𝔉 ν) k ζ n x ξ.1 ξ.2 * gn (𝔭.shift (k * dil (𝔉 ν).C x ξ.1) n)) =
      (stateMass 𝒢 J ℓ : ℂ) * (physCoef 𝔭 𝒢 q (𝔉 ν) k ζ n x ξ.1 ξ.2 *
        gn (𝔭.shift (k * dil (𝔉 ν).C x ξ.1) n))
    by_cases hx : IsPhys 𝔭 n x
    · rw [Pairing.physWeight_of_isPhys hx]
    · have hz : physCoef 𝔭 𝒢 q (𝔉 ν) k ζ n x ξ.1 ξ.2 = 0 :=
        Schur.physCoef_eq_zero_of_not fun hc => hx hc.1
      simp only [hz, zero_mul, mul_zero]
  exact (Finset.sum_congr rfl fun x _ => key x).trans Finset.sum_comm

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.TwoSidedProof
