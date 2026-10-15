module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.Sanity
public import SimultaneousPrimitiveRoots.Unconditional.Transference.Schur.Pointwise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Corollary 3.11: the inner product of `ℋ_ph` at one position

Source: `verification/stage7-sources/S-02.tex`, lines 98–103 (the space `ℋ_ph`) and 120–130
(self-adjointness of the symmetrizing projections).

`ℋ_ph` is the `L²` space of the physical states, every physical state having the mass
`∏_g V_g^{-M}` (`stateMass`). Functions on states are functions on all pairs (position, lists), so
the mass of a pair is `physWeight`: `stateMass` at a physical state and `0` elsewhere.

* `physWeight` and its relation to `pairUnit`, `physDensity`, `unitNormSq`.
* `fib n u v`, `fibSq n u` — the part of `⟨u, v⟩` and of `‖u‖²` at the position `n` (a finite sum
  over the lists).
* `fib_physSym` — "the symmetrizing projections are self-adjoint" [S-02:0129–0130], position by
  position: a slot permutation maps physical states to physical states (`isPhys_permuteLists`).
* `norm_sum_weighted_sq_le`, `norm_sum_mul_sq_le` — the two forms of the Cauchy–Schwarz
  inequality for finite sums that are used.

Everything here is for an arbitrary position model.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.Pairing

open scoped BigOperators ComplexConjugate

noncomputable section

/-! ### Cauchy–Schwarz for finite sums -/

/-- Cauchy–Schwarz for a weighted finite sum of products `conj a * b`. -/
theorem norm_sum_weighted_sq_le {ι : Type*} (T : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ T, 0 ≤ w i)
    (a b : ι → ℂ) :
    ‖∑ i ∈ T, (w i : ℂ) * (conj (a i) * b i)‖ ^ 2 ≤
      (∑ i ∈ T, w i * ‖a i‖ ^ 2) * ∑ i ∈ T, w i * ‖b i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ T, (w i : ℂ) * (conj (a i) * b i)‖ ≤
      ∑ i ∈ T, (Real.sqrt (w i) * ‖a i‖) * (Real.sqrt (w i) * ‖b i‖) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i hi => ?_))
    rw [norm_mul, norm_mul, Complex.norm_of_nonneg (hw i hi), Complex.norm_conj]
    calc w i * (‖a i‖ * ‖b i‖)
        = (Real.sqrt (w i) * Real.sqrt (w i)) * (‖a i‖ * ‖b i‖) := by
          rw [Real.mul_self_sqrt (hw i hi)]
      _ = (Real.sqrt (w i) * ‖a i‖) * (Real.sqrt (w i) * ‖b i‖) := by ring
  have h2 : (∑ i ∈ T, (Real.sqrt (w i) * ‖a i‖) * (Real.sqrt (w i) * ‖b i‖)) ^ 2 ≤
      (∑ i ∈ T, (Real.sqrt (w i) * ‖a i‖) ^ 2) * ∑ i ∈ T, (Real.sqrt (w i) * ‖b i‖) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq T _ _
  have h3 : ∀ c : ι → ℂ, ∑ i ∈ T, (Real.sqrt (w i) * ‖c i‖) ^ 2 = ∑ i ∈ T, w i * ‖c i‖ ^ 2 :=
    fun c => Finset.sum_congr rfl fun i hi => by rw [mul_pow, Real.sq_sqrt (hw i hi)]
  rw [h3 a, h3 b] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

/-- Cauchy–Schwarz for a finite linear combination of complex numbers. -/
theorem norm_sum_mul_sq_le {ι : Type*} (s : Finset ι) (c z : ι → ℂ) :
    ‖∑ i ∈ s, c i * z i‖ ^ 2 ≤ (∑ i ∈ s, ‖c i‖ ^ 2) * ∑ i ∈ s, ‖z i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, c i * z i‖ ≤ ∑ i ∈ s, ‖c i‖ * ‖z i‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => norm_mul _ _))
  have h2 : (∑ i ∈ s, ‖c i‖ * ‖z i‖) ^ 2 ≤ (∑ i ∈ s, ‖c i‖ ^ 2) * ∑ i ∈ s, ‖z i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq s _ _
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

variable {S B : Type} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]

/-! ### The mass of a state -/

section Weight

variable (𝔭 : PosModel) (𝒢 : GroupFamily S B) (J ℓ : ℕ)

omit [DecidableEq S] [DecidableEq B] in
/-- The mass `∏_g V_g^{-M}` of a physical state is nonnegative. -/
theorem stateMass_nonneg : 0 ≤ stateMass 𝒢 J ℓ := by
  unfold stateMass
  exact mul_nonneg
    (Finset.prod_nonneg fun g _ => inv_nonneg.mpr (pow_nonneg (Schur.reciprocalMass_nonneg _) _))
    (Finset.prod_nonneg fun g _ => inv_nonneg.mpr (pow_nonneg (Schur.reciprocalMass_nonneg _) _))

open Classical in
/-- **The mass of a pair (position, lists) in `ℋ_ph`** [S-02:0099–0103]: `∏_g V_g^{-M}` at a
physical state and `0` elsewhere. -/
def physWeight (s : PState 𝔭 𝒢 J ℓ) : ℝ :=
  if IsPhys 𝔭 s.1 s.2 then stateMass 𝒢 J ℓ else 0

variable {𝔭 𝒢 J ℓ}

omit [DecidableEq S] [DecidableEq B] in
theorem physWeight_of_isPhys {n : 𝔭.Pos} {x : Lists 𝒢 J ℓ} (h : IsPhys 𝔭 n x) :
    physWeight 𝔭 𝒢 J ℓ (n, x) = stateMass 𝒢 J ℓ := by
  unfold physWeight
  exact if_pos h

omit [DecidableEq S] [DecidableEq B] in
theorem physWeight_of_not_isPhys {n : 𝔭.Pos} {x : Lists 𝒢 J ℓ} (h : ¬IsPhys 𝔭 n x) :
    physWeight 𝔭 𝒢 J ℓ (n, x) = 0 := by
  unfold physWeight
  exact if_neg h

variable (𝔭 𝒢 J ℓ)

omit [DecidableEq S] [DecidableEq B] in
theorem physWeight_nonneg (s : PState 𝔭 𝒢 J ℓ) : 0 ≤ physWeight 𝔭 𝒢 J ℓ s := by
  unfold physWeight
  split_ifs
  · exact stateMass_nonneg 𝒢 J ℓ
  · exact le_rfl

/-- `⟨u_n, G⟩` is the sum of `mass * G` over the lists at the position `n`. -/
theorem pairUnit_eq_sum (n : 𝔭.Pos) (G : PState 𝔭 𝒢 J ℓ → ℂ) :
    pairUnit 𝔭 𝒢 J ℓ n G =
      ∑ x : Lists 𝒢 J ℓ, (physWeight 𝔭 𝒢 J ℓ (n, x) : ℂ) * G (n, x) := by
  unfold pairUnit
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : IsPhys 𝔭 n x
  · rw [if_pos h, physWeight_of_isPhys h]
  · rw [if_neg h, physWeight_of_not_isPhys h, Complex.ofReal_zero, zero_mul]

omit [DecidableEq S] [DecidableEq B] in
/-- The summand of `‖g‖²` is `mass * |g|²`. -/
theorem physDensity_eq (g : PState 𝔭 𝒢 J ℓ → ℂ) (s : PState 𝔭 𝒢 J ℓ) :
    physDensity 𝔭 𝒢 J ℓ g s = physWeight 𝔭 𝒢 J ℓ s * ‖g s‖ ^ 2 := by
  unfold physDensity physWeight
  split_ifs
  · rfl
  · exact (zero_mul _).symm

/-- `‖u_n‖²` is the total mass of the lists at the position `n`. -/
theorem unitNormSq_eq_sum (n : 𝔭.Pos) :
    unitNormSq 𝔭 𝒢 J ℓ n = ∑ x : Lists 𝒢 J ℓ, physWeight 𝔭 𝒢 J ℓ (n, x) := by
  unfold unitNormSq
  rw [Finset.natCast_card_filter, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : IsPhys 𝔭 n x
  · rw [if_pos h, physWeight_of_isPhys h, mul_one]
  · rw [if_neg h, physWeight_of_not_isPhys h, mul_zero]

variable {𝔭 𝒢 J ℓ}

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem physUnit_apply_of_ne {n m : 𝔭.Pos} (h : m ≠ n) (x : Lists 𝒢 J ℓ) :
    physUnit 𝔭 𝒢 J ℓ n (m, x) = 0 := by
  unfold physUnit
  exact if_neg fun hc => h hc.1

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem physUnit_apply_of_isPhys {n : 𝔭.Pos} {x : Lists 𝒢 J ℓ} (h : IsPhys 𝔭 n x) :
    physUnit 𝔭 𝒢 J ℓ n (n, x) = 1 := by
  unfold physUnit
  exact if_pos ⟨rfl, h⟩

end Weight

/-! ### Slot permutations preserve physical states -/

section Permute

variable {𝔭 : PosModel} {𝒢 : GroupFamily S B} {J ℓ : ℕ}

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
/-- A slot permutation maps a physical state to a physical state: the labels of a group stay
distinct and still divide the position. -/
theorem isPhys_permuteLists {n : 𝔭.Pos} {x : Lists 𝒢 J ℓ}
    (π : SlotPerms S J ℓ × SlotPerms B J ℓ) (h : IsPhys 𝔭 n x) :
    IsPhys 𝔭 n (permuteLists π x) :=
  ⟨fun g => (h.1 g).comp (π.1 g).injective, fun g => (h.2.1 g).comp (π.2 g).injective,
    fun g i => h.2.2.1 g (π.1 g i), fun g i => h.2.2.2 g (π.2 g i)⟩

omit [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B] in
theorem isPhys_permuteLists_iff {n : 𝔭.Pos} {x : Lists 𝒢 J ℓ}
    (π : SlotPerms S J ℓ × SlotPerms B J ℓ) :
    IsPhys 𝔭 n (permuteLists π x) ↔ IsPhys 𝔭 n x := by
  refine ⟨fun h => ?_, isPhys_permuteLists π⟩
  have h1 := isPhys_permuteLists π⁻¹ h
  rwa [(permuteLists_eq_iff π x (permuteLists π x)).mp rfl] at h1

omit [DecidableEq S] [DecidableEq B] in
theorem physWeight_permuteLists (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ)
    (π : SlotPerms S J ℓ × SlotPerms B J ℓ) :
    physWeight 𝔭 𝒢 J ℓ (n, permuteLists π x) = physWeight 𝔭 𝒢 J ℓ (n, x) := by
  by_cases hx : IsPhys 𝔭 n x
  · rw [physWeight_of_isPhys hx, physWeight_of_isPhys (isPhys_permuteLists π hx)]
  · have hx' : ¬IsPhys 𝔭 n (permuteLists π x) := fun h' =>
      hx ((isPhys_permuteLists_iff π).mp h')
    rw [physWeight_of_not_isPhys hx, physWeight_of_not_isPhys hx']

/-- The symmetrization kernel only connects states of the same mass. -/
theorem physWeight_mul_symKernel (n : 𝔭.Pos) (x y : Lists 𝒢 J ℓ) :
    (physWeight 𝔭 𝒢 J ℓ (n, x) : ℂ) * symKernel x y =
      (physWeight 𝔭 𝒢 J ℓ (n, y) : ℂ) * symKernel x y := by
  by_cases h : ∃ π : SlotPerms S J ℓ × SlotPerms B J ℓ, permuteLists π x = y
  · obtain ⟨π, rfl⟩ := h
    rw [physWeight_permuteLists]
  · have hz : symKernel x y = 0 := by
      unfold symKernel
      rw [Finset.sum_eq_zero fun π _ => if_neg fun hπ => h ⟨π, hπ⟩, mul_zero]
    rw [hz, mul_zero, mul_zero]

/-- Symmetrization at the state `(n, x)`. -/
theorem physSym_apply_mk (G : PState 𝔭 𝒢 J ℓ → ℂ) (n : 𝔭.Pos) (x : Lists 𝒢 J ℓ) :
    physSym 𝔭 𝒢 J ℓ G (n, x) = ∑ y : Lists 𝒢 J ℓ, symKernel x y * G (n, y) :=
  physSym_apply_eq_sum G (n, x)

end Permute

/-! ### The inner product at one position -/

section Fiber

variable (𝔭 : PosModel) (𝒢 : GroupFamily S B) (J ℓ : ℕ)

/-- **The part of `⟨u, v⟩` at the position `n`**: the sum of `mass * conj u * v` over the lists.
It is conjugate-linear in `u` and linear in `v`. -/
def fib (n : 𝔭.Pos) (u v : PState 𝔭 𝒢 J ℓ → ℂ) : ℂ :=
  ∑ x : Lists 𝒢 J ℓ, (physWeight 𝔭 𝒢 J ℓ (n, x) : ℂ) * (conj (u (n, x)) * v (n, x))

/-- **The part of `‖u‖²` at the position `n`**: the sum of `mass * |u|²` over the lists. -/
def fibSq (n : 𝔭.Pos) (u : PState 𝔭 𝒢 J ℓ → ℂ) : ℝ :=
  ∑ x : Lists 𝒢 J ℓ, physWeight 𝔭 𝒢 J ℓ (n, x) * ‖u (n, x)‖ ^ 2

variable {𝔭 𝒢 J ℓ}

theorem fibSq_nonneg (n : 𝔭.Pos) (u : PState 𝔭 𝒢 J ℓ → ℂ) : 0 ≤ fibSq 𝔭 𝒢 J ℓ n u :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (physWeight_nonneg 𝔭 𝒢 J ℓ _) (sq_nonneg _)

theorem fib_self (n : 𝔭.Pos) (u : PState 𝔭 𝒢 J ℓ → ℂ) :
    fib 𝔭 𝒢 J ℓ n u u = (fibSq 𝔭 𝒢 J ℓ n u : ℂ) := by
  unfold fib fibSq
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.conj_mul', Complex.ofReal_mul, Complex.ofReal_pow]

theorem fib_conj (n : 𝔭.Pos) (u v : PState 𝔭 𝒢 J ℓ → ℂ) :
    conj (fib 𝔭 𝒢 J ℓ n u v) = fib 𝔭 𝒢 J ℓ n v u := by
  unfold fib
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul, map_mul, Complex.conj_ofReal, starRingEnd_self_apply, mul_comm (u (n, x))]

theorem fib_congr_left {n : 𝔭.Pos} {u u' : PState 𝔭 𝒢 J ℓ → ℂ} (h : ∀ x, u (n, x) = u' (n, x))
    (v : PState 𝔭 𝒢 J ℓ → ℂ) : fib 𝔭 𝒢 J ℓ n u v = fib 𝔭 𝒢 J ℓ n u' v := by
  unfold fib
  exact Finset.sum_congr rfl fun x _ => by rw [h x]

theorem fibSq_congr {n : 𝔭.Pos} {u u' : PState 𝔭 𝒢 J ℓ → ℂ} (h : ∀ x, u (n, x) = u' (n, x)) :
    fibSq 𝔭 𝒢 J ℓ n u = fibSq 𝔭 𝒢 J ℓ n u' := by
  unfold fibSq
  exact Finset.sum_congr rfl fun x _ => by rw [h x]

theorem fib_sum_right {ι : Type*} (s : Finset ι) (n : 𝔭.Pos) (u : PState 𝔭 𝒢 J ℓ → ℂ)
    (w : ι → PState 𝔭 𝒢 J ℓ → ℂ) :
    fib 𝔭 𝒢 J ℓ n u (∑ i ∈ s, w i) = ∑ i ∈ s, fib 𝔭 𝒢 J ℓ n u (w i) := by
  have h : ∀ x : Lists 𝒢 J ℓ,
      (physWeight 𝔭 𝒢 J ℓ (n, x) : ℂ) * (conj (u (n, x)) * (∑ i ∈ s, w i) (n, x)) =
        ∑ i ∈ s, (physWeight 𝔭 𝒢 J ℓ (n, x) : ℂ) * (conj (u (n, x)) * w i (n, x)) := by
    intro x
    rw [Finset.sum_apply, Finset.mul_sum, Finset.mul_sum]
  unfold fib
  rw [Finset.sum_congr rfl fun x _ => h x]
  exact Finset.sum_comm

theorem fib_sum_left {ι : Type*} (s : Finset ι) (n : 𝔭.Pos) (w : ι → PState 𝔭 𝒢 J ℓ → ℂ)
    (v : PState 𝔭 𝒢 J ℓ → ℂ) :
    fib 𝔭 𝒢 J ℓ n (∑ i ∈ s, w i) v = ∑ i ∈ s, fib 𝔭 𝒢 J ℓ n (w i) v := by
  have h : ∀ x : Lists 𝒢 J ℓ,
      (physWeight 𝔭 𝒢 J ℓ (n, x) : ℂ) * (conj ((∑ i ∈ s, w i) (n, x)) * v (n, x)) =
        ∑ i ∈ s, (physWeight 𝔭 𝒢 J ℓ (n, x) : ℂ) * (conj (w i (n, x)) * v (n, x)) := by
    intro x
    rw [Finset.sum_apply, map_sum, Finset.sum_mul, Finset.mul_sum]
  unfold fib
  rw [Finset.sum_congr rfl fun x _ => h x]
  exact Finset.sum_comm

theorem fib_smul_left (n : 𝔭.Pos) (c : ℂ) (u v : PState 𝔭 𝒢 J ℓ → ℂ) :
    fib 𝔭 𝒢 J ℓ n (c • u) v = conj c * fib 𝔭 𝒢 J ℓ n u v := by
  unfold fib
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, map_mul]
  ring

theorem fibSq_smul (n : 𝔭.Pos) (c : ℂ) (u : PState 𝔭 𝒢 J ℓ → ℂ) :
    fibSq 𝔭 𝒢 J ℓ n (c • u) = ‖c‖ ^ 2 * fibSq 𝔭 𝒢 J ℓ n u := by
  unfold fibSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
  ring

/-- `⟨u_n, G⟩` is the inner product with `u_n` at the position `n`. -/
theorem fib_physUnit_self (n : 𝔭.Pos) (G : PState 𝔭 𝒢 J ℓ → ℂ) :
    fib 𝔭 𝒢 J ℓ n (physUnit 𝔭 𝒢 J ℓ n) G = pairUnit 𝔭 𝒢 J ℓ n G := by
  rw [pairUnit_eq_sum]
  unfold fib
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : IsPhys 𝔭 n x
  · rw [physUnit_apply_of_isPhys h, map_one, one_mul]
  · rw [physWeight_of_not_isPhys h, Complex.ofReal_zero, zero_mul, zero_mul]

/-- `‖u_n‖²` at the position `n`. -/
theorem fibSq_physUnit_self (n : 𝔭.Pos) :
    fibSq 𝔭 𝒢 J ℓ n (physUnit 𝔭 𝒢 J ℓ n) = unitNormSq 𝔭 𝒢 J ℓ n := by
  rw [unitNormSq_eq_sum]
  unfold fibSq
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : IsPhys 𝔭 n x
  · rw [physUnit_apply_of_isPhys h, norm_one, one_pow, mul_one]
  · rw [physWeight_of_not_isPhys h, zero_mul]

/-- Cauchy–Schwarz for the inner product over a finite set of positions. -/
theorem norm_sum_fib_sq_le (T : Finset 𝔭.Pos) (u v : PState 𝔭 𝒢 J ℓ → ℂ) :
    ‖∑ n ∈ T, fib 𝔭 𝒢 J ℓ n u v‖ ^ 2 ≤
      (∑ n ∈ T, fibSq 𝔭 𝒢 J ℓ n u) * ∑ n ∈ T, fibSq 𝔭 𝒢 J ℓ n v := by
  have h := norm_sum_weighted_sq_le (T ×ˢ (Finset.univ : Finset (Lists 𝒢 J ℓ)))
    (fun s : 𝔭.Pos × Lists 𝒢 J ℓ => physWeight 𝔭 𝒢 J ℓ (s.1, s.2))
    (fun s _ => physWeight_nonneg 𝔭 𝒢 J ℓ _)
    (fun s : 𝔭.Pos × Lists 𝒢 J ℓ => u (s.1, s.2)) (fun s : 𝔭.Pos × Lists 𝒢 J ℓ => v (s.1, s.2))
  rw [Finset.sum_product' T Finset.univ
      (fun n x => (physWeight 𝔭 𝒢 J ℓ (n, x) : ℂ) * (conj (u (n, x)) * v (n, x))),
    Finset.sum_product' T Finset.univ (fun n x => physWeight 𝔭 𝒢 J ℓ (n, x) * ‖u (n, x)‖ ^ 2),
    Finset.sum_product' T Finset.univ (fun n x => physWeight 𝔭 𝒢 J ℓ (n, x) * ‖v (n, x)‖ ^ 2)]
    at h
  exact h

/-- Cauchy–Schwarz for a finite linear combination, at one position. -/
theorem fibSq_sum_smul_le {ι : Type*} (s : Finset ι) (n : 𝔭.Pos) (c : ι → ℂ)
    (w : ι → PState 𝔭 𝒢 J ℓ → ℂ) :
    fibSq 𝔭 𝒢 J ℓ n (∑ i ∈ s, c i • w i) ≤
      (∑ i ∈ s, ‖c i‖ ^ 2) * ∑ i ∈ s, fibSq 𝔭 𝒢 J ℓ n (w i) := by
  have hpt : ∀ x : Lists 𝒢 J ℓ,
      physWeight 𝔭 𝒢 J ℓ (n, x) * ‖(∑ i ∈ s, c i • w i) (n, x)‖ ^ 2 ≤
        ∑ i ∈ s, (∑ j ∈ s, ‖c j‖ ^ 2) * (physWeight 𝔭 𝒢 J ℓ (n, x) * ‖w i (n, x)‖ ^ 2) := by
    intro x
    have hval : (∑ i ∈ s, c i • w i) (n, x) = ∑ i ∈ s, c i * w i (n, x) := by
      rw [Finset.sum_apply]
      rfl
    rw [hval, ← Finset.mul_sum, ← Finset.mul_sum]
    calc physWeight 𝔭 𝒢 J ℓ (n, x) * ‖∑ i ∈ s, c i * w i (n, x)‖ ^ 2
        ≤ physWeight 𝔭 𝒢 J ℓ (n, x) * ((∑ i ∈ s, ‖c i‖ ^ 2) * ∑ i ∈ s, ‖w i (n, x)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (norm_sum_mul_sq_le s c fun i => w i (n, x))
            (physWeight_nonneg 𝔭 𝒢 J ℓ _)
      _ = (∑ j ∈ s, ‖c j‖ ^ 2) * (physWeight 𝔭 𝒢 J ℓ (n, x) * ∑ i ∈ s, ‖w i (n, x)‖ ^ 2) := by
          ring
  calc fibSq 𝔭 𝒢 J ℓ n (∑ i ∈ s, c i • w i)
      ≤ ∑ x : Lists 𝒢 J ℓ,
          ∑ i ∈ s, (∑ j ∈ s, ‖c j‖ ^ 2) * (physWeight 𝔭 𝒢 J ℓ (n, x) * ‖w i (n, x)‖ ^ 2) :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = ∑ i ∈ s, ∑ x : Lists 𝒢 J ℓ,
          (∑ j ∈ s, ‖c j‖ ^ 2) * (physWeight 𝔭 𝒢 J ℓ (n, x) * ‖w i (n, x)‖ ^ 2) :=
        Finset.sum_comm
    _ = (∑ i ∈ s, ‖c i‖ ^ 2) * ∑ i ∈ s, fibSq 𝔭 𝒢 J ℓ n (w i) := by
        unfold fibSq
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm

/-- **The symmetrizing projection is self-adjoint** [S-02:0129–0130], at every position. -/
theorem fib_physSym (n : 𝔭.Pos) (u v : PState 𝔭 𝒢 J ℓ → ℂ) :
    fib 𝔭 𝒢 J ℓ n u (physSym 𝔭 𝒢 J ℓ v) = fib 𝔭 𝒢 J ℓ n (physSym 𝔭 𝒢 J ℓ u) v := by
  have hL : fib 𝔭 𝒢 J ℓ n u (physSym 𝔭 𝒢 J ℓ v) =
      ∑ x : Lists 𝒢 J ℓ, ∑ y : Lists 𝒢 J ℓ,
        ((physWeight 𝔭 𝒢 J ℓ (n, x) : ℂ) * symKernel x y) * (conj (u (n, x)) * v (n, y)) := by
    unfold fib
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [physSym_apply_mk, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun y _ => by ring
  have hR : fib 𝔭 𝒢 J ℓ n (physSym 𝔭 𝒢 J ℓ u) v =
      ∑ y : Lists 𝒢 J ℓ, ∑ x : Lists 𝒢 J ℓ,
        ((physWeight 𝔭 𝒢 J ℓ (n, y) : ℂ) * symKernel x y) * (conj (u (n, x)) * v (n, y)) := by
    unfold fib
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [physSym_apply_mk, map_sum, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [map_mul, conj_symKernel, symKernel_symm y x]
    ring
  rw [hL, hR, Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by
    rw [physWeight_mul_symKernel]

end Fiber

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.Pairing
