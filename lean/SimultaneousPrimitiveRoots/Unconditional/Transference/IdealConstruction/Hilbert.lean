module

public import SimultaneousPrimitiveRoots.Unconditional.Transference.FiniteOperators
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Commuting averaging projections on a finite weighted `L²` space

Abstract tools for the proof of [S] Theorem 4.1 (`verification/stage7-sources/S-03.tex`,
lines 441–645), for the space `L²(X, w)` of `FiniteOperators.lean` with a nonnegative weight.

* `norm_wInner_le`, `wNorm_add_le` — Cauchy's inequality and the triangle inequality.
* `IsSA` — self-adjoint operators; `wNorm_apply_le_of_proj` — a self-adjoint idempotent is a
  contraction; `bessel` — Bessel's inequality for mutually orthogonal self-adjoint idempotents.
* `AvgSystem` — a family `E U` (`U` a finite set of coordinates) of self-adjoint operators with
  `E ∅ = 1` and `E U * E V = E (U ∪ V)`: "for a coordinate `i`, write `E_i` for averaging its
  label" [S-03:0474], and `E U = ∏_{i ∈ U} E_i`.
* `AvgSystem.D` — `D U = ∏_{i ∈ U} (1 - E_i) = ∑_{T ⊆ U} (-1)^{|T|} E T`, the projection on the
  functions which are "separately mean zero in each indicated probe" [S-03:0485–0487].
* `AvgSystem.card_mul_le` — if the vectors `E_k ∏_{i ∈ T, i ≠ k} (1 - E_i) F`, `k ∈ T`, have the
  same norm, then `|T| ‖E_k ∏_{i ≠ k} (1 - E_i) F‖² ≤ ‖F‖²`: these vectors are the images of `F`
  under mutually orthogonal projections. This is the form of the Hoeffding fraction
  (eq:ideal-hoeffding-fraction) [S-03:0491–0517] used here: with `T` the `m` probes and one of
  the last `ℓ ≥ 1` slots of a group, it gives the fraction `1/(m + 1)`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction

open scoped BigOperators ComplexConjugate

noncomputable section

variable {X : Type*} [Fintype X]

/-! ### Cauchy's inequality -/

/-- Cauchy's inequality for a nonnegative weight. -/
theorem sum_weight_mul_le (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (a b : X → ℝ) (ha : ∀ x, 0 ≤ a x)
    (hb : ∀ x, 0 ≤ b x) :
    ∑ x, w x * (a x * b x) ≤
      Real.sqrt (∑ x, w x * a x ^ 2) * Real.sqrt (∑ x, w x * b x ^ 2) := by
  have hsq : (∑ x, w x * (a x * b x)) ^ 2 ≤ (∑ x, w x * a x ^ 2) * ∑ x, w x * b x ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (fun x _ => mul_nonneg (hw x) (sq_nonneg _)) (fun x _ => mul_nonneg (hw x) (sq_nonneg _))
    intro x _
    apply le_of_eq
    ring
  have h0 : 0 ≤ ∑ x, w x * (a x * b x) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (mul_nonneg (ha x) (hb x))
  calc ∑ x, w x * (a x * b x) = Real.sqrt ((∑ x, w x * (a x * b x)) ^ 2) :=
        (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt ((∑ x, w x * a x ^ 2) * ∑ x, w x * b x ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∑ x, w x * a x ^ 2) * Real.sqrt (∑ x, w x * b x ^ 2) :=
        Real.sqrt_mul (Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (sq_nonneg _)) _

/-- Cauchy's inequality for the weighted inner product. -/
theorem norm_wInner_le {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (F G : X → ℂ) :
    ‖wInner w F G‖ ≤ wNorm w F * wNorm w G := by
  have hcs : ∑ x, w x * (‖F x‖ * ‖G x‖) ≤ wNorm w F * wNorm w G :=
    sum_weight_mul_le w hw (fun x => ‖F x‖) (fun x => ‖G x‖) (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _)
  refine le_trans ?_ hcs
  unfold wInner
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw x), RCLike.norm_conj]

/-- Multiplication by a function of modulus at most one is a contraction. -/
theorem wNorm_mul_le {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (m F : X → ℂ) (hm : ∀ x, ‖m x‖ ≤ 1) :
    wNorm w (fun x => m x * F x) ≤ wNorm w F := by
  unfold wNorm
  refine Real.sqrt_le_sqrt ?_
  unfold wNormSq
  refine Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left ?_ (hw x)
  rw [norm_mul]
  calc (‖m x‖ * ‖F x‖) ^ 2 ≤ (1 * ‖F x‖) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (hm x) (norm_nonneg _)) 2
    _ = ‖F x‖ ^ 2 := by rw [one_mul]

/-! ### Linearity of the inner product -/

theorem wInner_sub_right (w : X → ℝ) (F G H : X → ℂ) :
    wInner w F (G - H) = wInner w F G - wInner w F H := by
  unfold wInner
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.sub_apply]
  ring

theorem wInner_sub_left (w : X → ℝ) (F G H : X → ℂ) :
    wInner w (F - G) H = wInner w F H - wInner w G H := by
  unfold wInner
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.sub_apply, map_sub]
  ring

theorem wInner_add_right (w : X → ℝ) (F G H : X → ℂ) :
    wInner w F (G + H) = wInner w F G + wInner w F H := by
  unfold wInner
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.add_apply]
  ring

theorem wInner_smul_right (w : X → ℝ) (c : ℂ) (F G : X → ℂ) :
    wInner w F (c • G) = c * wInner w F G := by
  unfold wInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  ring

theorem wInner_sum_right {ι : Type*} (w : X → ℝ) (s : Finset ι) (F : X → ℂ)
    (G : ι → X → ℂ) : wInner w F (∑ i ∈ s, G i) = ∑ i ∈ s, wInner w F (G i) := by
  unfold wInner
  have h : ∀ x, (w x : ℂ) * (conj (F x) * (∑ i ∈ s, G i) x) =
      ∑ i ∈ s, (w x : ℂ) * (conj (F x) * G i x) := by
    intro x
    rw [Finset.sum_apply, Finset.mul_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun x _ => h x]
  exact Finset.sum_comm

theorem wInner_sum_left {ι : Type*} (w : X → ℝ) (s : Finset ι) (F : ι → X → ℂ)
    (G : X → ℂ) : wInner w (∑ i ∈ s, F i) G = ∑ i ∈ s, wInner w (F i) G := by
  unfold wInner
  have h : ∀ x, (w x : ℂ) * (conj ((∑ i ∈ s, F i) x) * G x) =
      ∑ i ∈ s, (w x : ℂ) * (conj (F i x) * G x) := by
    intro x
    rw [Finset.sum_apply, map_sum, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun x _ => h x]
  exact Finset.sum_comm

/-! ### Self-adjoint operators and projections -/

/-- `T` is self-adjoint on `L²(X, w)`. -/
def IsSA (w : X → ℝ) (T : Module.End ℂ (X → ℂ)) : Prop :=
  ∀ F G : X → ℂ, wInner w F (T G) = wInner w (T F) G

theorem isSA_one (w : X → ℝ) : IsSA w (1 : Module.End ℂ (X → ℂ)) := fun _ _ => rfl

theorem IsSA.sub {w : X → ℝ} {T S : Module.End ℂ (X → ℂ)} (hT : IsSA w T) (hS : IsSA w S) :
    IsSA w (T - S) := by
  intro F G
  have e1 : (T - S) G = T G - S G := rfl
  have e2 : (T - S) F = T F - S F := rfl
  rw [e1, e2, wInner_sub_right, wInner_sub_left, hT F G, hS F G]

theorem IsSA.sum {ι : Type*} {w : X → ℝ} (s : Finset ι) (T : ι → Module.End ℂ (X → ℂ))
    (h : ∀ i ∈ s, IsSA w (T i)) : IsSA w (∑ i ∈ s, T i) := by
  intro F G
  rw [LinearMap.sum_apply, LinearMap.sum_apply, wInner_sum_right, wInner_sum_left]
  exact Finset.sum_congr rfl fun i hi => h i hi F G

/-- A product of two commuting self-adjoint operators is self-adjoint. -/
theorem IsSA.mul_of_commute {w : X → ℝ} {T S : Module.End ℂ (X → ℂ)} (hT : IsSA w T)
    (hS : IsSA w S) (hc : T * S = S * T) : IsSA w (T * S) := by
  intro F G
  have h1 : (T * S) G = T (S G) := rfl
  have h2 : (T * S) F = S (T F) := by
    rw [hc]
    rfl
  rw [h1, h2, hT F (S G), hS (T F) G]

/-- A self-adjoint idempotent is a contraction. -/
theorem wNorm_apply_le_of_proj {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) {T : Module.End ℂ (X → ℂ)}
    (hsa : IsSA w T) (hid : T * T = T) (F : X → ℂ) : wNorm w (T F) ≤ wNorm w F := by
  have h2 : T (T F) = T F := LinearMap.congr_fun hid F
  have h1 : wInner w (T F) (T F) = wInner w F (T F) := by
    have h := hsa F (T F)
    rw [h2] at h
    exact h.symm
  have h3 : wNormSq w (T F) ≤ wNorm w F * wNorm w (T F) := by
    have h4 : ‖wInner w F (T F)‖ ≤ wNorm w F * wNorm w (T F) := norm_wInner_le hw F (T F)
    rw [← h1, wInner_self, Complex.norm_real, Real.norm_of_nonneg (wNormSq_nonneg hw _)] at h4
    exact h4
  have h5 : wNorm w (T F) ^ 2 = wNormSq w (T F) := wNorm_sq hw _
  have h7 : 0 ≤ wNorm w F := wNorm_nonneg _ _
  by_contra hcon
  have hlt : wNorm w F < wNorm w (T F) := not_le.mp hcon
  have hpos : 0 < wNorm w (T F) := lt_of_le_of_lt h7 hlt
  nlinarith [mul_pos (sub_pos.mpr hlt) hpos]

/-- **Bessel's inequality** for mutually orthogonal self-adjoint idempotents. -/
theorem bessel {ι : Type*} {w : X → ℝ} (hw : ∀ x, 0 ≤ w x) (s : Finset ι)
    (Q : ι → Module.End ℂ (X → ℂ)) (hsa : ∀ i ∈ s, IsSA w (Q i))
    (hidem : ∀ i ∈ s, Q i * Q i = Q i)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Q i * Q j = 0) (F : X → ℂ) :
    ∑ i ∈ s, wNormSq w (Q i F) ≤ wNormSq w F := by
  obtain ⟨P, hP⟩ : ∃ P : Module.End ℂ (X → ℂ), P = ∑ i ∈ s, Q i := ⟨_, rfl⟩
  have hPsa : IsSA w P := by
    rw [hP]
    exact IsSA.sum s Q hsa
  have hPid : P * P = P := by
    rw [hP, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mul_sum,
      Finset.sum_eq_single_of_mem i hi (fun j hj hji => horth i hi j hj (Ne.symm hji))]
    exact hidem i hi
  have hc : ((∑ i ∈ s, wNormSq w (Q i F) : ℝ) : ℂ) = ((wNormSq w (P F) : ℝ) : ℂ) := by
    calc ((∑ i ∈ s, wNormSq w (Q i F) : ℝ) : ℂ)
        = ∑ i ∈ s, wInner w (Q i F) (Q i F) := by
          rw [Complex.ofReal_sum]
          exact Finset.sum_congr rfl fun i _ => (wInner_self w (Q i F)).symm
      _ = ∑ i ∈ s, wInner w F (Q i F) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [← hsa i hi F (Q i F)]
          exact congrArg (wInner w F) (LinearMap.congr_fun (hidem i hi) F)
      _ = wInner w F (P F) := by
          rw [hP, LinearMap.sum_apply, wInner_sum_right]
      _ = wInner w (P F) (P F) := by
          rw [← hPsa F (P F)]
          exact (congrArg (wInner w F) (LinearMap.congr_fun hPid F)).symm
      _ = ((wNormSq w (P F) : ℝ) : ℂ) := wInner_self w (P F)
  have hreal : ∑ i ∈ s, wNormSq w (Q i F) = wNormSq w (P F) := Complex.ofReal_injective hc
  have h := wNorm_apply_le_of_proj hw hPsa hPid F
  rw [hreal, ← wNorm_sq hw (P F), ← wNorm_sq hw F]
  exact pow_le_pow_left₀ (wNorm_nonneg _ _) h 2

/-! ### Signs -/

/-- Multiplication by the number `(-1)^n`, as an operator. -/
def sgnOp (n : ℕ) : Module.End ℂ (X → ℂ) where
  toFun F := fun x => (-1 : ℂ) ^ n * F x
  map_add' F G := by
    funext x
    simp only [Pi.add_apply, mul_add]
  map_smul' c F := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

omit [Fintype X] in
theorem sgnOp_apply (n : ℕ) (F : X → ℂ) (x : X) : sgnOp n F x = (-1 : ℂ) ^ n * F x := rfl

omit [Fintype X] in
theorem sgnOp_zero : sgnOp 0 = (1 : Module.End ℂ (X → ℂ)) := by
  refine LinearMap.ext fun F => funext fun x => ?_
  show (-1 : ℂ) ^ 0 * F x = F x
  rw [pow_zero, one_mul]

omit [Fintype X] in
theorem sgnOp_succ_add (n : ℕ) : sgnOp (n + 1) + sgnOp n = (0 : Module.End ℂ (X → ℂ)) := by
  refine LinearMap.ext fun F => funext fun x => ?_
  show (-1 : ℂ) ^ (n + 1) * F x + (-1 : ℂ) ^ n * F x = 0
  ring

omit [Fintype X] in
/-- The signs commute with every operator. -/
theorem mul_sgnOp (A : Module.End ℂ (X → ℂ)) (n : ℕ) : A * sgnOp n = sgnOp n * A := by
  refine LinearMap.ext fun F => funext fun x => ?_
  have h1 : sgnOp n F = ((-1 : ℂ) ^ n) • F := by
    funext y
    exact (smul_eq_mul ((-1 : ℂ) ^ n) (F y)).symm
  have h2 : A (((-1 : ℂ) ^ n) • F) = ((-1 : ℂ) ^ n) • A F := A.map_smul _ _
  show A (sgnOp n F) x = (-1 : ℂ) ^ n * A F x
  exact (congrArg (fun G : X → ℂ => A G x) h1).trans
    ((congrFun h2 x).trans (smul_eq_mul _ _))

/-! ### Averaging systems -/

/-- A commuting family of averaging projections: `E U` averages the coordinates of `U`. -/
structure AvgSystem (K : Type*) [DecidableEq K] (w : X → ℝ) where
  /-- averaging the coordinates of `U` -/
  E : Finset K → Module.End ℂ (X → ℂ)
  E_empty : E ∅ = 1
  E_mul : ∀ U V : Finset K, E U * E V = E (U ∪ V)
  E_sa : ∀ U : Finset K, IsSA w (E U)

namespace AvgSystem

variable {K : Type*} [DecidableEq K] {w : X → ℝ} (S : AvgSystem K w)

theorem E_comm (U V : Finset K) : S.E U * S.E V = S.E V * S.E U := by
  rw [S.E_mul, S.E_mul, Finset.union_comm]

theorem E_idem (U : Finset K) : S.E U * S.E U = S.E U := by
  rw [S.E_mul, Finset.union_self]

theorem E_apply_apply (U V : Finset K) (F : X → ℂ) : S.E U (S.E V F) = S.E (U ∪ V) F :=
  LinearMap.congr_fun (S.E_mul U V) F

/-- `D U = ∏_{k ∈ U} (1 - E_k)`, in expanded form: `∑_{T ⊆ U} (-1)^{|T|} E T`. -/
def D (U : Finset K) : Module.End ℂ (X → ℂ) :=
  ∑ T ∈ U.powerset, sgnOp T.card * S.E T

theorem D_apply (U : Finset K) (F : X → ℂ) (x : X) :
    S.D U F x = ∑ T ∈ U.powerset, (-1 : ℂ) ^ T.card * S.E T F x := by
  have h1 : S.D U F =
      ∑ T ∈ U.powerset, (sgnOp T.card * S.E T : Module.End ℂ (X → ℂ)) F :=
    LinearMap.sum_apply _ _ _
  have h2 : S.D U F x =
      ∑ T ∈ U.powerset, (sgnOp T.card * S.E T : Module.End ℂ (X → ℂ)) F x := by
    rw [h1, Finset.sum_apply]
  exact h2

theorem D_empty : S.D ∅ = 1 := by
  unfold D
  rw [Finset.powerset_empty, Finset.sum_singleton, Finset.card_empty, sgnOp_zero, one_mul,
    S.E_empty]

theorem D_insert {k : K} {U : Finset K} (hk : k ∉ U) :
    S.D (insert k U) = (1 - S.E {k}) * S.D U := by
  have hterm : ∀ T ∈ U.powerset,
      sgnOp (insert k T).card * S.E (insert k T) + S.E {k} * (sgnOp T.card * S.E T) = 0 := by
    intro T hT
    have hkT : k ∉ T := fun h => hk (Finset.mem_powerset.mp hT h)
    have hE : S.E (insert k T) = S.E {k} * S.E T := by rw [S.E_mul, Finset.insert_eq]
    rw [Finset.card_insert_of_notMem hkT, hE, ← mul_assoc (S.E {k}), mul_sgnOp (S.E {k}) T.card,
      mul_assoc, ← add_mul, sgnOp_succ_add, zero_mul]
  have key : S.D (insert k U) + S.E {k} * S.D U = S.D U := by
    unfold D
    rw [Finset.sum_powerset_insert hk, Finset.mul_sum, add_assoc, ← Finset.sum_add_distrib,
      Finset.sum_eq_zero hterm, add_zero]
  rw [sub_mul, one_mul]
  exact eq_sub_of_add_eq key

/-- An operator which commutes with every `E T` commutes with every `D U`. -/
theorem D_commute_of {A : Module.End ℂ (X → ℂ)} (hA : ∀ T, A * S.E T = S.E T * A)
    (U : Finset K) : A * S.D U = S.D U * A := by
  unfold D
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun T _ => ?_
  calc A * (sgnOp T.card * S.E T)
      = A * sgnOp T.card * S.E T := (mul_assoc _ _ _).symm
    _ = sgnOp T.card * A * S.E T := by rw [mul_sgnOp A T.card]
    _ = sgnOp T.card * (A * S.E T) := mul_assoc _ _ _
    _ = sgnOp T.card * (S.E T * A) := by rw [hA]
    _ = sgnOp T.card * S.E T * A := (mul_assoc _ _ _).symm

theorem E_D_comm (V U : Finset K) : S.E V * S.D U = S.D U * S.E V :=
  S.D_commute_of (fun T => S.E_comm V T) U

theorem D_comm (U V : Finset K) : S.D U * S.D V = S.D V * S.D U :=
  S.D_commute_of (A := S.D U) (fun T => (S.E_D_comm T U).symm) V

theorem one_sub_E_comm_D (k : K) (U : Finset K) :
    (1 - S.E {k}) * S.D U = S.D U * (1 - S.E {k}) := by
  rw [sub_mul, mul_sub, one_mul, mul_one, S.E_D_comm]

theorem D_sa (U : Finset K) : IsSA w (S.D U) := by
  induction U using Finset.induction_on with
  | empty =>
    rw [S.D_empty]
    exact isSA_one w
  | @insert k U hk ih =>
    rw [S.D_insert hk]
    exact IsSA.mul_of_commute ((isSA_one w).sub (S.E_sa {k})) ih (S.one_sub_E_comm_D k U)

theorem D_idem (U : Finset K) : S.D U * S.D U = S.D U := by
  induction U using Finset.induction_on with
  | empty => rw [S.D_empty, one_mul]
  | @insert k U hk ih =>
    have hE : (1 - S.E {k}) * (1 - S.E {k}) = 1 - S.E {k} := by
      rw [sub_mul, one_mul, mul_sub, mul_one, S.E_idem, sub_self, sub_zero]
    have hc : S.D U * (1 - S.E {k}) = (1 - S.E {k}) * S.D U := (S.one_sub_E_comm_D k U).symm
    rw [S.D_insert hk]
    calc (1 - S.E {k}) * S.D U * ((1 - S.E {k}) * S.D U)
        = (1 - S.E {k}) * (S.D U * (1 - S.E {k})) * S.D U := by simp only [mul_assoc]
      _ = (1 - S.E {k}) * ((1 - S.E {k}) * S.D U) * S.D U := by rw [hc]
      _ = ((1 - S.E {k}) * (1 - S.E {k})) * (S.D U * S.D U) := by simp only [mul_assoc]
      _ = (1 - S.E {k}) * S.D U := by rw [hE, ih]

/-- `E_k ∏_{i ∈ U} (1 - E_i) = 0` when `k ∈ U`. -/
theorem E_singleton_mul_D {k : K} {U : Finset K} (hk : k ∈ U) : S.E {k} * S.D U = 0 := by
  have h := S.D_insert (Finset.notMem_erase k U)
  rw [Finset.insert_erase hk] at h
  rw [h, ← mul_assoc, mul_sub, mul_one, S.E_idem, sub_self, zero_mul]

theorem D_union {U V : Finset K} (h : Disjoint U V) : S.D (U ∪ V) = S.D U * S.D V := by
  induction V using Finset.induction_on with
  | empty => rw [Finset.union_empty, S.D_empty, mul_one]
  | @insert k V hk ih =>
    have hkU : k ∉ U := fun hmem =>
      Finset.disjoint_left.mp h hmem (Finset.mem_insert_self k V)
    have hd : Disjoint U V := Finset.disjoint_of_subset_right (Finset.subset_insert k V) h
    have hk' : k ∉ U ∪ V := fun hmem => (Finset.mem_union.mp hmem).elim hkU hk
    rw [Finset.union_insert, S.D_insert hk', ih hd, S.D_insert hk, ← mul_assoc, ← mul_assoc]
    congr 1
    exact S.one_sub_E_comm_D k U

theorem wNorm_E_le (hw : ∀ x, 0 ≤ w x) (U : Finset K) (F : X → ℂ) :
    wNorm w (S.E U F) ≤ wNorm w F :=
  wNorm_apply_le_of_proj hw (S.E_sa U) (S.E_idem U) F

theorem wNorm_D_le (hw : ∀ x, 0 ≤ w x) (U : Finset K) (F : X → ℂ) :
    wNorm w (S.D U F) ≤ wNorm w F :=
  wNorm_apply_le_of_proj hw (S.D_sa U) (S.D_idem U) F

/-- A symmetry of the coordinates which intertwines the averages intertwines the `D`'s. -/
theorem D_equivariant (π : K → K) (hπ : Function.Injective π) (Uπ : Module.End ℂ (X → ℂ))
    (h : ∀ (V : Finset K) (G : X → ℂ), Uπ (S.E V G) = S.E (V.image π) (Uπ G))
    (V : Finset K) (G : X → ℂ) : Uπ (S.D V G) = S.D (V.image π) (Uπ G) := by
  induction V using Finset.induction_on with
  | empty =>
    rw [Finset.image_empty, S.D_empty]
    rfl
  | @insert k V hk ih =>
    have hk' : π k ∉ V.image π := fun hmem => by
      obtain ⟨y, hy, hyk⟩ := Finset.mem_image.mp hmem
      exact hk (hπ hyk ▸ hy)
    have e1 : ((1 - S.E {k}) * S.D V) G = S.D V G - S.E {k} (S.D V G) := rfl
    have e2 : ((1 - S.E {π k}) * S.D (V.image π)) (Uπ G) =
        S.D (V.image π) (Uπ G) - S.E {π k} (S.D (V.image π) (Uπ G)) := rfl
    rw [Finset.image_insert, S.D_insert hk, S.D_insert hk', e1, e2, map_sub, h, ih,
      Finset.image_singleton]

/-- **The surviving fraction of a symmetric family of components.** If the vectors
`E_k ∏_{i ∈ T, i ≠ k} (1 - E_i) F`, `k ∈ T`, all have squared norm `c`, then
`|T| c ≤ ‖F‖²`. -/
theorem card_mul_le (hw : ∀ x, 0 ≤ w x) (T : Finset K) (F : X → ℂ) (c : ℝ)
    (hc : ∀ k ∈ T, wNormSq w (S.E {k} (S.D (T.erase k) F)) = c) :
    (T.card : ℝ) * c ≤ wNormSq w F := by
  have hb : ∑ k ∈ T, wNormSq w ((S.E {k} * S.D (T.erase k)) F) ≤ wNormSq w F := by
    refine bessel hw T (fun k => S.E {k} * S.D (T.erase k)) ?_ ?_ ?_ F
    · intro k _
      exact IsSA.mul_of_commute (S.E_sa {k}) (S.D_sa _) (S.E_D_comm {k} _)
    · intro k _
      calc S.E {k} * S.D (T.erase k) * (S.E {k} * S.D (T.erase k))
          = S.E {k} * (S.D (T.erase k) * S.E {k}) * S.D (T.erase k) := by
            simp only [mul_assoc]
        _ = S.E {k} * (S.E {k} * S.D (T.erase k)) * S.D (T.erase k) := by
            rw [← S.E_D_comm]
        _ = (S.E {k} * S.E {k}) * (S.D (T.erase k) * S.D (T.erase k)) := by
            simp only [mul_assoc]
        _ = S.E {k} * S.D (T.erase k) := by rw [S.E_idem, S.D_idem]
    · intro k _ k' hk' hne
      calc S.E {k} * S.D (T.erase k) * (S.E {k'} * S.D (T.erase k'))
          = S.E {k} * (S.D (T.erase k) * S.E {k'}) * S.D (T.erase k') := by
            simp only [mul_assoc]
        _ = S.E {k} * (S.E {k'} * S.D (T.erase k)) * S.D (T.erase k') := by
            rw [← S.E_D_comm]
        _ = 0 := by
            rw [S.E_singleton_mul_D (Finset.mem_erase.mpr ⟨hne.symm, hk'⟩), mul_zero, zero_mul]
  calc (T.card : ℝ) * c = ∑ _k ∈ T, c := by rw [Finset.sum_const, nsmul_eq_mul]
    _ = ∑ k ∈ T, wNormSq w ((S.E {k} * S.D (T.erase k)) F) :=
        (Finset.sum_congr rfl fun k hk => hc k hk).symm
    _ ≤ wNormSq w F := hb

end AvgSystem

end

end SimultaneousPrimitiveRoots.Unconditional.Transference.IdealConstruction
