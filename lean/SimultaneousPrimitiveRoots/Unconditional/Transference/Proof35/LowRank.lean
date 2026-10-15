module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.FourierMult
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.SymmetryPreserved
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.HistoryExpansionProof
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35.Statements
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# (eq:low-rank-path-bound): the contribution of a collection of small rank

Source: `verification/stage7-sources/S-02.tex`, lines 1172–1225 (`[S-02:1172–1225]`).

`lowRankStep : LowRankStep` is proved here: for every collection `π` of blocks of birth
addresses,

`|rankPart(π)| ≤ K₀ · Cg^{N+1} · Cw^{N - a} · Ce^{a}`, `a = min(N, 2 r(π))`,

from the operator bounds `Cg` for the visit operations with a multiplier of modulus at most one
on the births, `Ce` for the edge operations with such a multiplier, `Cw ≤ Ce` for the edge
operations without multiplier, and `K₀` for the squared norm of the boundary vector.

The proof follows the paper.

1. *The Fourier representation* (`card_mul_rankPart`, `FourierMult.lean`): the indicator of `𝒞_π`
   is the average over the Fourier parameters `t` of a product, over the addresses, of functions
   of the single births, so that `rankPart(π)` is the average over `t` of the path integrals
   `∑_h Φ_t(h) weight(h)` with the multipliers `Φ_t = fourierMult D Bc π Q t` on the operations.
2. *The operator product* (`historyExpansion`, `HistoryExpansionProof.lean`): each of these path
   integrals is the matrix element `⟨conj(Φ_init 𝟏_∅), G_0^Φ ℰ_0^Φ ⋯ ℰ_{N-1}^Φ G_N^Φ 𝟏_∅⟩`.
3. *The product of the norms* (`memTailWith_bound`): the operations preserve the symmetry in the
   particle indices (`SymmetryPreserved.lean`), so the bounds on symmetric functions compose.
   "An affected edge can lose its signed norm saving … Unaffected edges retain their complete
   signed pattern sum and both symmetrizations": the multiplier of an unaffected edge is `1`
   (`fourierMult_edge_of_not_affected`), and its bound is `Cw`; "at most `2r` edges are affected
   by a rank-`r` collection" (`card_affectedEdges_le`).
4. Cauchy's inequality (`norm_wInner_le`) and the bound `K₀` for the boundary vectors
   (`norm_sum_mult_weight_le`).
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ### Products of the constants of the steps -/

/-- `Ce^u Cw^v ≤ Cw^{n - a} Ce^a` when `u + v = n`, `u ≤ a ≤ n` and `0 ≤ Cw ≤ Ce`. -/
theorem pow_mul_pow_le (Cw Ce : ℝ) (h0 : 0 ≤ Cw) (hle : Cw ≤ Ce) (u v n a : ℕ)
    (huv : u + v = n) (hua : u ≤ a) (han : a ≤ n) :
    Ce ^ u * Cw ^ v ≤ Cw ^ (n - a) * Ce ^ a := by
  have hCe : 0 ≤ Ce := h0.trans hle
  have hv : v = (n - a) + (a - u) := by omega
  have ha : u + (a - u) = a := by omega
  have h1 : Cw ^ (a - u) ≤ Ce ^ (a - u) := pow_le_pow_left₀ h0 hle _
  have h2 : Ce ^ u * Ce ^ (a - u) = Ce ^ a := by rw [← pow_add, ha]
  have h3 : Cw ^ v = Cw ^ (n - a) * Cw ^ (a - u) := by rw [hv, pow_add]
  have h4 : Ce ^ u * (Cw ^ (n - a) * Cw ^ (a - u)) ≤ Ce ^ u * (Cw ^ (n - a) * Ce ^ (a - u)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (pow_nonneg h0 _))
      (pow_nonneg hCe _)
  calc Ce ^ u * Cw ^ v = Ce ^ u * (Cw ^ (n - a) * Cw ^ (a - u)) := by rw [h3]
    _ ≤ Ce ^ u * (Cw ^ (n - a) * Ce ^ (a - u)) := h4
    _ = Cw ^ (n - a) * (Ce ^ u * Ce ^ (a - u)) := by ring
    _ = Cw ^ (n - a) * Ce ^ a := by rw [h2]

/-- A product of constants which are `Ce` on at most `a` indices and `Cw ≤ Ce` on the others. -/
theorem prod_ite_const_le {ι : Type*} (s : Finset ι) (p : ι → Prop) [DecidablePred p]
    (Cw Ce : ℝ) (h0 : 0 ≤ Cw) (hle : Cw ≤ Ce) (a : ℕ) (ha : (s.filter p).card ≤ a)
    (has : a ≤ s.card) :
    ∏ x ∈ s, (if p x then Ce else Cw) ≤ Cw ^ (s.card - a) * Ce ^ a := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  exact pow_mul_pow_le Cw Ce h0 hle _ _ _ a (Finset.card_filter_add_card_filter_not p) ha has

/-- The reversal `k ↦ n - (k + 1)` of the steps `k < n` is injective. -/
theorem card_filter_rev_le (n : ℕ) (T : Finset ℕ) :
    ((Finset.range n).filter fun k => n - (k + 1) ∈ T).card ≤ T.card := by
  refine Finset.card_le_card_of_injOn (fun k => n - (k + 1)) ?_ ?_
  · intro k hk
    exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hk)).2
  · intro k₁ h₁ k₂ h₂ h
    have hk₁ := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp h₁)).1
    have hk₂ := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp h₂)).1
    have h' : n - (k₁ + 1) = n - (k₂ + 1) := h
    omega

/-- The constant of the edge `j`: `Ce` on the edges of the set `T`, `Cw` on the others. -/
def stepConst (T : Finset ℕ) (Cw Ce : ℝ) (j : ℕ) : ℝ := if j ∈ T then Ce else Cw

theorem stepConst_of_mem {T : Finset ℕ} {Cw Ce : ℝ} {j : ℕ} (h : j ∈ T) :
    stepConst T Cw Ce j = Ce := if_pos h

theorem stepConst_of_notMem {T : Finset ℕ} {Cw Ce : ℝ} {j : ℕ} (h : j ∉ T) :
    stepConst T Cw Ce j = Cw := if_neg h

theorem stepConst_nonneg (T : Finset ℕ) {Cw Ce : ℝ} (h0 : 0 ≤ Cw) (hle : Cw ≤ Ce) (j : ℕ) :
    0 ≤ stepConst T Cw Ce j := by
  by_cases h : j ∈ T
  · rw [stepConst_of_mem h]
    exact h0.trans hle
  · rw [stepConst_of_notMem h]
    exact h0

/-- The product of the constants of the `n` edges, when at most `r` edges are in `T`:
`Cw^{n - a} Ce^a` with `a = min(n, r)`. -/
theorem prod_stepConst_le (T : Finset ℕ) {Cw Ce : ℝ} (h0 : 0 ≤ Cw) (hle : Cw ≤ Ce) (n r : ℕ)
    (hT : T.card ≤ r) :
    ∏ k ∈ Finset.range n, stepConst T Cw Ce (n - (k + 1)) ≤
      Cw ^ (n - min n r) * Ce ^ min n r := by
  have hf1 : ((Finset.range n).filter fun k => n - (k + 1) ∈ T).card ≤ n :=
    (Finset.card_filter_le (Finset.range n) (fun k => n - (k + 1) ∈ T)).trans_eq
      (Finset.card_range n)
  have hf2 : ((Finset.range n).filter fun k => n - (k + 1) ∈ T).card ≤ r :=
    (card_filter_rev_le n T).trans hT
  have h := prod_ite_const_le (Finset.range n) (fun k => n - (k + 1) ∈ T) Cw Ce h0 hle
    (min n r) (le_min hf1 hf2) ((min_le_left n r).trans_eq (Finset.card_range n).symm)
  rw [Finset.card_range] at h
  exact h

/-- One step of the induction along the tail. -/
theorem tail_scalar (Cg c a e P x y : ℝ) (m : ℕ) (hCg : 0 ≤ Cg) (hc : 0 ≤ c)
    (h1 : x ≤ Cg * y) (h2 : y ≤ c * a) (h3 : a ≤ Cg ^ (m + 1) * P * e) :
    x ≤ Cg ^ (m + 1 + 1) * (P * c) * e := by
  have h4 : c * a ≤ c * (Cg ^ (m + 1) * P * e) := mul_le_mul_of_nonneg_left h3 hc
  have h5 : Cg * y ≤ Cg * (c * (Cg ^ (m + 1) * P * e)) :=
    mul_le_mul_of_nonneg_left (h2.trans h4) hCg
  refine (h1.trans h5).trans (le_of_eq ?_)
  ring

/-- If the average of the numbers `X t` over a nonempty finite type is `z` and every `X t` has
modulus at most `R`, then `z` has modulus at most `R`. -/
theorem norm_le_of_card_mul_eq_sum {T : Type*} [Fintype T] {z : ℂ} {X : T → ℂ} {R : ℝ}
    (hid : (Fintype.card T : ℂ) * z = ∑ t, X t) (hT : Nonempty T) (hX : ∀ t, ‖X t‖ ≤ R) :
    ‖z‖ ≤ R := by
  have hpos : (0 : ℝ) < (Fintype.card T : ℝ) := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr hT)
  have h1 : ‖(Fintype.card T : ℂ) * z‖ = (Fintype.card T : ℝ) * ‖z‖ := by
    rw [norm_mul, Complex.norm_natCast]
  have h2 : ‖∑ t, X t‖ ≤ (Fintype.card T : ℝ) * R := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun t _ => hX t).trans (le_of_eq ?_))
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← hid, h1] at h2
  exact le_of_mul_le_mul_left h2 hpos

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
  {𝒢 : GroupFamily S B} {J ℓ : ℕ} {N : Type} [Fintype N]

/-! ### The product of the operator bounds -/

/-- **The norm of the operator product is at most the product of the bounds of its factors**:
for multipliers `Φ` on the births, if the visit operations with the multipliers of `Φ` have the
bound `Cg` and the edge operation `ℰ_i` with the multiplier of `Φ` has the bound `c i`, on the
functions which are symmetric in the particle indices, then the tail
`G_{N-m} ℰ_{N-m} ⋯ ℰ_{N-1} G_N 𝟏_∅` is symmetric and its norm is at most
`Cg^{m+1} ∏_{k<m} c(N - (k+1)) ‖𝟏_∅‖`. The bounds compose because the operations preserve the
symmetry (`ghostOpWith_memSymmetric`, `edgeOpWith_memSymmetric`). -/
theorem memTailWith_bound (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (Φ : BirthMult 𝒢 J ℓ Bc) (θ : ℝ)
    (Cg : ℝ) (c : ℕ → ℝ) (hCg : 0 ≤ Cg) (hc : ∀ j, 0 ≤ c j)
    (hG : ∀ i : ℕ, i ≤ D.n →
      OpBound (memWeight 𝒢 D.q D.n) (fun F => MemSymmetric F)
        (ghostOpWith D Bc (Φ.ghost i) i) Cg)
    (hE : ∀ i : ℕ, i < D.n →
      OpBound (memWeight 𝒢 D.q D.n) (fun F => MemSymmetric F)
        (edgeOpWith D Bc (Φ.edge i) θ i) (c i)) :
    ∀ m : ℕ, m ≤ D.n →
      MemSymmetric (memTailWith D Bc Φ θ m) ∧
        wNorm (memWeight 𝒢 D.q D.n) (memTailWith D Bc Φ θ m) ≤
          Cg ^ (m + 1) * (∏ k ∈ Finset.range m, c (D.n - (k + 1))) *
            wNorm (memWeight 𝒢 D.q D.n) (emptyVec 𝒢 J ℓ Bc) := by
  intro m
  induction m with
  | zero =>
    intro _
    refine ⟨ghostOpWith_memSymmetric D Bc (Φ.ghost D.n) D.n emptyVec_memSymmetric, ?_⟩
    have h := hG D.n le_rfl (emptyVec 𝒢 J ℓ Bc) emptyVec_memSymmetric
    have h0 : Cg ^ (0 + 1) * (∏ k ∈ Finset.range 0, c (D.n - (k + 1))) *
        wNorm (memWeight 𝒢 D.q D.n) (emptyVec 𝒢 J ℓ Bc) =
        Cg * wNorm (memWeight 𝒢 D.q D.n) (emptyVec 𝒢 J ℓ Bc) := by
      rw [Finset.prod_range_zero, mul_one, zero_add, pow_one]
    exact h.trans (le_of_eq h0.symm)
  | succ m ih =>
    intro hm
    obtain ⟨hsym, hbd⟩ := ih (Nat.le_of_succ_le hm)
    have hj : D.n - (m + 1) < D.n := by omega
    have hEsym : MemSymmetric (edgeOpWith D Bc (Φ.edge (D.n - (m + 1))) θ (D.n - (m + 1))
        (memTailWith D Bc Φ θ m)) :=
      edgeOpWith_memSymmetric D Bc (Φ.edge (D.n - (m + 1))) θ (D.n - (m + 1)) hsym
    have hE1 := hE (D.n - (m + 1)) hj (memTailWith D Bc Φ θ m) hsym
    have hG1 := hG (D.n - (m + 1)) (Nat.sub_le _ _) _ hEsym
    refine ⟨ghostOpWith_memSymmetric D Bc (Φ.ghost (D.n - (m + 1))) (D.n - (m + 1)) hEsym, ?_⟩
    rw [Finset.prod_range_succ]
    exact tail_scalar Cg (c (D.n - (m + 1))) _ _ _ _ _ m hCg (hc _) hG1 hE1 hbd

/-! ### Cauchy's inequality for the matrix element -/

/-- **The path integral with multipliers `Φ` of modulus at most one on the initial list** is at
most `K₀ R`, if the operator product applied to `𝟏_∅` has norm at most `R ‖𝟏_∅‖` and
`‖𝟏_∅‖² ≤ K₀`: by `HistoryExpansion` it is the matrix element
`⟨conj(Φ_init 𝟏_∅), G_0^Φ ℰ_0^Φ ⋯ G_N^Φ 𝟏_∅⟩`, and `‖Φ_init 𝟏_∅‖ ≤ ‖𝟏_∅‖` ("initial-slot factors
merely modify the initial boundary vector by such a multiplier", [S-02:1190–1191]). -/
theorem norm_sum_mult_weight_le (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (Φ : BirthMult 𝒢 J ℓ Bc)
    (θ : ℝ) (R K₀ : ℝ) (hw : ∀ s : MState 𝒢 J ℓ Bc, 0 ≤ memWeight 𝒢 D.q D.n s)
    (hinit : ∀ xb, ‖Φ.init xb‖ ≤ 1) (hR : 0 ≤ R)
    (hK : wNormSq (memWeight 𝒢 D.q D.n) (emptyVec 𝒢 J ℓ Bc) ≤ K₀)
    (htail : wNorm (memWeight 𝒢 D.q D.n) (memTailWith D Bc Φ θ D.n) ≤
      R * wNorm (memWeight 𝒢 D.q D.n) (emptyVec 𝒢 J ℓ Bc)) :
    ‖∑ h : History D Bc, h.mult Φ * h.weight θ‖ ≤ K₀ * R := by
  -- the matrix element
  have hinner : (∑ h : History D Bc, h.mult Φ * h.weight θ) =
      wInner (memWeight 𝒢 D.q D.n) (fun s => conj (Φ.init s.xb * emptyVec 𝒢 J ℓ Bc s))
        (memTailWith D Bc Φ θ D.n) := by
    rw [historyExpansion_aux D Bc Φ θ]
    show _ = ∑ s : MState 𝒢 J ℓ Bc, ((memWeight 𝒢 D.q D.n s : ℝ) : ℂ) *
      (conj (conj (Φ.init s.xb * emptyVec 𝒢 J ℓ Bc s)) * memTailWith D Bc Φ θ D.n s)
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Complex.conj_conj]
  -- the modified boundary vector is not larger than the boundary vector
  have hU : wNorm (memWeight 𝒢 D.q D.n) (fun s => conj (Φ.init s.xb * emptyVec 𝒢 J ℓ Bc s)) ≤
      wNorm (memWeight 𝒢 D.q D.n) (emptyVec 𝒢 J ℓ Bc) := by
    unfold wNorm
    refine Real.sqrt_le_sqrt ?_
    show ∑ s : MState 𝒢 J ℓ Bc,
        memWeight 𝒢 D.q D.n s * ‖conj (Φ.init s.xb * emptyVec 𝒢 J ℓ Bc s)‖ ^ 2 ≤
      ∑ s : MState 𝒢 J ℓ Bc, memWeight 𝒢 D.q D.n s * ‖emptyVec 𝒢 J ℓ Bc s‖ ^ 2
    refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (hw s)
    have h1 : ‖conj (Φ.init s.xb * emptyVec 𝒢 J ℓ Bc s)‖ ≤ ‖emptyVec 𝒢 J ℓ Bc s‖ := by
      rw [Complex.norm_conj, norm_mul]
      exact (mul_le_mul_of_nonneg_right (hinit s.xb) (norm_nonneg _)).trans_eq (one_mul _)
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hcs := norm_wInner_le (w := memWeight 𝒢 D.q D.n) hw
    (fun s => conj (Φ.init s.xb * emptyVec 𝒢 J ℓ Bc s)) (memTailWith D Bc Φ θ D.n)
  have he0 : 0 ≤ wNorm (memWeight 𝒢 D.q D.n) (emptyVec 𝒢 J ℓ Bc) := wNorm_nonneg _ _
  have hV0 : 0 ≤ wNorm (memWeight 𝒢 D.q D.n) (memTailWith D Bc Φ θ D.n) := wNorm_nonneg _ _
  have h2 := mul_le_mul hU htail hV0 he0
  have h3 : wNorm (memWeight 𝒢 D.q D.n) (emptyVec 𝒢 J ℓ Bc) *
        (R * wNorm (memWeight 𝒢 D.q D.n) (emptyVec 𝒢 J ℓ Bc)) =
      R * wNormSq (memWeight 𝒢 D.q D.n) (emptyVec 𝒢 J ℓ Bc) := by
    rw [← wNorm_sq (w := memWeight 𝒢 D.q D.n) hw (emptyVec 𝒢 J ℓ Bc)]
    ring
  have h4 : R * wNormSq (memWeight 𝒢 D.q D.n) (emptyVec 𝒢 J ℓ Bc) ≤ R * K₀ :=
    mul_le_mul_of_nonneg_left hK hR
  rw [hinner]
  exact (hcs.trans h2).trans ((le_of_eq h3).trans (h4.trans_eq (mul_comm R K₀)))

/-! ### The bound for fixed Fourier parameters -/

/-- **The path integral with the Fourier multipliers of fixed parameters**
(eq:low-rank-path-bound) [S-02:1183–1221]: the visit operations cost `Cg`, the affected edges
`Ce`, the unaffected edges `Cw`, and at most `min(N, 2r)` edges are affected. -/
theorem norm_fourier_term_le (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ) (Cg Ce Cw K₀ : ℝ)
    (hCg : 0 ≤ Cg) (hCw : 0 ≤ Cw) (hCwe : Cw ≤ Ce)
    (hw : ∀ s : MState 𝒢 J ℓ Bc, 0 ≤ memWeight 𝒢 D.q D.n s)
    (hG : ∀ i : ℕ, i ≤ D.n → ∀ φ : ((g : B) → Batch 𝒢 Bc g) → ℂ, (∀ b, ‖φ b‖ ≤ 1) →
      OpBound (memWeight 𝒢 D.q D.n) (fun F => MemSymmetric F) (ghostOpWith D Bc φ i) Cg)
    (hE : ∀ i : ℕ, i < D.n → ∀ ψ : ((g : B) → Slot J ℓ → Option ℕ) → ℂ, (∀ b, ‖ψ b‖ ≤ 1) →
      OpBound (memWeight 𝒢 D.q D.n) (fun F => MemSymmetric F) (edgeOpWith D Bc ψ θ i) Ce)
    (hW : ∀ i : ℕ, i < D.n →
      OpBound (memWeight 𝒢 D.q D.n) (fun F => MemSymmetric F) (edgeOp D Bc θ i) Cw)
    (hK : wNormSq (memWeight 𝒢 D.q D.n) (emptyVec 𝒢 J ℓ Bc) ≤ K₀)
    (π : Finset (Finset (BirthAddr B J ℓ Bc D.n)))
    (hπ : π ∈ blockCollections (BirthAddr B J ℓ Bc D.n)) (Q : ℕ)
    (t : BirthAddr B J ℓ Bc D.n × BirthAddr B J ℓ Bc D.n → Fin Q) :
    ‖∑ h : History D Bc, h.mult (fourierMult D Bc π Q t) * h.weight θ‖ ≤
      K₀ * (Cg ^ (D.n + 1) *
        (Cw ^ (D.n - min D.n (2 * blockRank π)) * Ce ^ min D.n (2 * blockRank π))) := by
  have hCe : 0 ≤ Ce := hCw.trans hCwe
  -- the bounds of the operations with the Fourier multipliers
  have hGΦ : ∀ i : ℕ, i ≤ D.n →
      OpBound (memWeight 𝒢 D.q D.n) (fun F => MemSymmetric F)
        (ghostOpWith D Bc ((fourierMult D Bc π Q t).ghost i) i) Cg :=
    fun i hi => hG i hi _ (norm_fourierMult_ghost_le D Bc π Q t i)
  have hEΦ : ∀ i : ℕ, i < D.n →
      OpBound (memWeight 𝒢 D.q D.n) (fun F => MemSymmetric F)
        (edgeOpWith D Bc ((fourierMult D Bc π Q t).edge i) θ i)
        (stepConst (affectedEdges π) Cw Ce i) := by
    intro i hi
    by_cases hia : i ∈ affectedEdges π
    · rw [stepConst_of_mem hia]
      exact hE i hi _ (norm_fourierMult_edge_le D Bc π Q t i)
    · rw [stepConst_of_notMem hia, fourierMult_edge_of_not_affected D Bc π Q t hi hia]
      exact hW i hi
  -- the operator product
  have htail := (memTailWith_bound D Bc (fourierMult D Bc π Q t) θ Cg
    (stepConst (affectedEdges π) Cw Ce) hCg (stepConst_nonneg (affectedEdges π) hCw hCwe)
    hGΦ hEΦ D.n le_rfl).2
  -- at most `min(N, 2r)` edges are affected
  have hP := prod_stepConst_le (affectedEdges π) hCw hCwe D.n (2 * blockRank π)
    (card_affectedEdges_le hπ)
  have hR0 : 0 ≤ Cg ^ (D.n + 1) *
      (Cw ^ (D.n - min D.n (2 * blockRank π)) * Ce ^ min D.n (2 * blockRank π)) :=
    mul_nonneg (pow_nonneg hCg _) (mul_nonneg (pow_nonneg hCw _) (pow_nonneg hCe _))
  refine norm_sum_mult_weight_le D Bc (fourierMult D Bc π Q t) θ _ K₀ hw
    (norm_fourierMult_init_le D Bc π Q t) hR0 hK ?_
  exact htail.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hP (pow_nonneg hCg _)) (wNorm_nonneg _ _))

/-! ### The small-rank step -/

/-- `LowRankStep` for one family of groups. -/
theorem lowRank_aux (D : MemData 𝒢 J ℓ N) (Bc : ℕ) (θ : ℝ) (Cg Ce Cw K₀ : ℝ)
    (hCg : 0 ≤ Cg) (hCw : 0 ≤ Cw) (hCwe : Cw ≤ Ce)
    (hw : ∀ s : MState 𝒢 J ℓ Bc, 0 ≤ memWeight 𝒢 D.q D.n s)
    (hG : ∀ i : ℕ, i ≤ D.n → ∀ φ : ((g : B) → Batch 𝒢 Bc g) → ℂ, (∀ b, ‖φ b‖ ≤ 1) →
      OpBound (memWeight 𝒢 D.q D.n) (fun F => MemSymmetric F) (ghostOpWith D Bc φ i) Cg)
    (hE : ∀ i : ℕ, i < D.n → ∀ ψ : ((g : B) → Slot J ℓ → Option ℕ) → ℂ, (∀ b, ‖ψ b‖ ≤ 1) →
      OpBound (memWeight 𝒢 D.q D.n) (fun F => MemSymmetric F) (edgeOpWith D Bc ψ θ i) Ce)
    (hW : ∀ i : ℕ, i < D.n →
      OpBound (memWeight 𝒢 D.q D.n) (fun F => MemSymmetric F) (edgeOp D Bc θ i) Cw)
    (hK : wNormSq (memWeight 𝒢 D.q D.n) (emptyVec 𝒢 J ℓ Bc) ≤ K₀)
    (π : Finset (Finset (BirthAddr B J ℓ Bc D.n)))
    (hπ : π ∈ blockCollections (BirthAddr B J ℓ Bc D.n)) :
    ‖rankPart D Bc θ π‖ ≤
      K₀ * Cg ^ (D.n + 1) * Cw ^ (D.n - min D.n (2 * blockRank π)) *
        Ce ^ min D.n (2 * blockRank π) := by
  have h := norm_le_of_card_mul_eq_sum (card_mul_rankPart D Bc θ π hπ)
    ⟨fun _ => ⟨0, primeBound_pos 𝒢⟩⟩
    (fun t => norm_fourier_term_le D Bc θ Cg Ce Cw K₀ hCg hCw hCwe hw hG hE hW hK π hπ
      (primeBound 𝒢) t)
  refine h.trans (le_of_eq ?_)
  ring

/-- **(eq:low-rank-path-bound)** [S-02:1172–1225]: the path integral with the indicator of the
constraint `𝒞_π` of a collection of rank `r` is at most
`K₀ · Cg^{N+1} · Cw^{N - min(N, 2r)} · Ce^{min(N, 2r)}`. -/
theorem lowRankStep : LowRankStep := by
  intro S B _ _ _ _ 𝒢 J ℓ N _ D Bc θ Cg Ce Cw K₀ hCg hCw hCwe hw hG hE hW hK π hπ
  exact lowRank_aux D Bc θ Cg Ce Cw K₀ hCg hCw hCwe hw hG hE hW hK π hπ

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Proof35
