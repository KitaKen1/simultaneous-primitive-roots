module

public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.WeightBound
public import SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction.Sanity
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The model bounds (ext:model-bounds)

`modelBounds_of_mertensReciprocal : MertensReciprocal → ModelBounds q` for `0 ≤ q < 1`
(`[P-07:0063–0075]`): there are constants `0 < c_K ≤ C_K` with `c_K ≤ m_𝒲 ≤ C_K` and
`M_x(𝒲²) ≤ C_K`, "independently of the particular fixed exponents".

* The model is a probability with nonnegative weights (`modelMean_le_of_le`), and `𝒲 ≤ C_W`
  pointwise for large `x` (`arrayWeightBounded_of_mertensReciprocal`), so `m_𝒲 ≤ C_W` and
  `M_x(𝒲²) ≤ C_W²`.
* One prime at a time: `M_{P ∪ {p}}(F) = (1 - 1/p) M_P(F) + (1/p) M_P(F(p ·))`
  (`modelMean_insert`).
* Independence: if `F` does not see the primes of `B` and `G` does not see the primes of `A`,
  `A ∩ B = ∅`, then `M_{A ∪ B}(F G) = M_A(F) M_B(G)` (`modelMean_union_mul`); for pairwise disjoint
  sets `M_{⋃ P_i}(∏ f_i) = ∏ M_{P_i}(f_i)` (`modelMean_biUnion_prod`). The bands of an array are
  pairwise disjoint for large `x` (`bandPrimes_disjoint`: `2 < L^{a' - a}`), and the factor of one
  band does not see the primes of the others (`markFactor_prime_mul`). So
  `m_𝒲 = ∏_i M_{𝒫_i}(q^{ω_i - 1} ω_i / V_i)`.
* One band: the configurations with exactly one prime give
  `M_𝒫(q^{ω-1} ω / V) ≥ (1/V) ∑_p (1/p) ∏_{p' ≠ p} (1 - 1/p') ≥ 1 - V`
  (`one_sub_mass_le_modelMean_markFactor`, with `∏ (1 - a_i) ≥ 1 - ∑ a_i`), and
  `V = log 2 + o(1) ≤ 0.8`.

The constants are `c_K = 5^{-K}` and `C_K = max(C_W, C_W²)`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction

open Filter
open scoped Topology

noncomputable section

/-! ### The independent divisor model -/

/-- The weights of the model are nonnegative: the model expectation is monotone. -/
theorem modelMean_le_of_le {P : Finset ℕ} (hP : ∀ p ∈ P, 1 ≤ p) {F G : ℕ → ℝ}
    (h : ∀ n, F n ≤ G n) : modelMean P F ≤ modelMean P G := by
  unfold modelMean
  refine Finset.sum_le_sum fun T _ => mul_le_mul_of_nonneg_left (h _) ?_
  refine mul_nonneg (Finset.prod_nonneg fun p _ => by positivity)
    (Finset.prod_nonneg fun p hp => ?_)
  have hpP : p ∈ P := (Finset.mem_sdiff.mp hp).1
  have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hP p hpP
  have h2 : 1 / (p : ℝ) ≤ 1 := (div_le_one (by linarith)).mpr h1
  linarith

/-- **One prime at a time**: `M_{P ∪ {p}}(F) = (1 - 1/p) M_P(F) + (1/p) M_P(F(p ·))`. -/
theorem modelMean_insert {P : Finset ℕ} {p : ℕ} (hp : p ∉ P) (F : ℕ → ℝ) :
    modelMean (insert p P) F =
      (1 - 1 / (p : ℝ)) * modelMean P F + 1 / (p : ℝ) * modelMean P fun n => F (p * n) := by
  unfold modelMean
  rw [Finset.sum_powerset_insert hp, Finset.mul_sum, Finset.mul_sum]
  refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun T hT => ?_)
    (Finset.sum_congr rfl fun T hT => ?_)
  · have hTP : T ⊆ P := Finset.mem_powerset.mp hT
    have hpT : p ∉ T := fun h => hp (hTP h)
    have hsd : insert p P \ T = insert p (P \ T) := Finset.insert_sdiff_of_notMem _ hpT
    have hpd : p ∉ P \ T := fun h => hp (Finset.mem_sdiff.mp h).1
    rw [hsd, Finset.prod_insert hpd]
    ring
  · have hTP : T ⊆ P := Finset.mem_powerset.mp hT
    have hpT : p ∉ T := fun h => hp (hTP h)
    have hsd : insert p P \ insert p T = P \ T := by
      ext a
      simp only [Finset.mem_sdiff, Finset.mem_insert]
      constructor
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd (Or.inl h1) h2
        · exact ⟨h1, fun h => h2 (Or.inr h)⟩
      · rintro ⟨h1, h2⟩
        refine ⟨Or.inr h1, ?_⟩
        rintro (h | h)
        · rw [h] at h1
          exact hp h1
        · exact h2 h
    rw [hsd, Finset.prod_insert hpT, Finset.prod_insert hpT]
    ring

/-- A function that does not see the primes of `B` is constant on the products of subsets of
`B`. -/
theorem apply_prod_eq_of_invariant {F : ℕ → ℝ} {B : Finset ℕ}
    (hF : ∀ p ∈ B, ∀ n, F (p * n) = F n) {T : Finset ℕ} (hT : T ⊆ B) :
    F (∏ p ∈ T, p) = F 1 := by
  induction T using Finset.induction_on with
  | empty => rw [Finset.prod_empty]
  | @insert a T' ha ih =>
    rw [Finset.prod_insert ha, hF a (hT (Finset.mem_insert_self a T'))]
    exact ih fun p hp => hT (Finset.mem_insert_of_mem hp)

/-- **Independence**: `M_{A ∪ B}(F G) = M_A(F) M_B(G)` for disjoint `A`, `B`, when `F` does not see
the primes of `B` and `G` does not see the primes of `A`. -/
theorem modelMean_union_mul {A B : Finset ℕ} (hAB : Disjoint A B) (G : ℕ → ℝ)
    (hG : ∀ p ∈ A, ∀ n, G (p * n) = G n) :
    ∀ F : ℕ → ℝ, (∀ p ∈ B, ∀ n, F (p * n) = F n) →
      modelMean (A ∪ B) (fun n => F n * G n) = modelMean A F * modelMean B G := by
  induction A using Finset.induction_on with
  | empty =>
    intro F hF
    rw [Finset.empty_union, modelMean_empty]
    unfold modelMean
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun T hT => ?_
    have h := apply_prod_eq_of_invariant hF (Finset.mem_powerset.mp hT)
    simp only [h]
    ring
  | @insert p A' hp ih =>
    intro F hF
    have hpB : p ∉ B := Finset.disjoint_left.mp hAB (Finset.mem_insert_self p A')
    have hAB' : Disjoint A' B :=
      Finset.disjoint_of_subset_left (Finset.subset_insert p A') hAB
    have hpU : p ∉ A' ∪ B := fun h => (Finset.mem_union.mp h).elim hp hpB
    have hG' : ∀ p' ∈ A', ∀ n, G (p' * n) = G n := fun p' hp' n =>
      hG p' (Finset.mem_insert_of_mem hp') n
    have hfun : (fun n => F (p * n) * G (p * n)) = fun n => F (p * n) * G n := by
      funext n
      rw [hG p (Finset.mem_insert_self p A') n]
    have hF' : ∀ p' ∈ B, ∀ n, F (p * (p' * n)) = F (p * n) := fun p' hp' n => by
      rw [mul_left_comm, hF p' hp']
    have h1 := ih hAB' hG' F hF
    have h2 := ih hAB' hG' (fun n => F (p * n)) hF'
    rw [Finset.insert_union, modelMean_insert hpU, modelMean_insert hp, hfun, h1, h2]
    ring

/-- **The product formula**: for pairwise disjoint sets `P_i` and functions `f_i` that do not see
the primes of the `P_j`, `j ≠ i`: `M_{⋃ P_i}(∏ f_i) = ∏ M_{P_i}(f_i)`. -/
theorem modelMean_biUnion_prod {ι : Type} [DecidableEq ι] (I : Finset ι) (P : ι → Finset ℕ)
    (f : ι → ℕ → ℝ) (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (P i) (P j))
    (hinv : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ∀ p ∈ P j, ∀ n, f i (p * n) = f i n) :
    modelMean (I.biUnion P) (fun n => ∏ i ∈ I, f i n) = ∏ i ∈ I, modelMean (P i) (f i) := by
  induction I using Finset.induction_on with
  | empty =>
    simp only [Finset.biUnion_empty, Finset.prod_empty]
    exact modelMean_const ∅ 1
  | @insert a I' ha ih =>
    have hfun : (fun n => ∏ i ∈ insert a I', f i n) = fun n => f a n * ∏ i ∈ I', f i n := by
      funext n
      rw [Finset.prod_insert ha]
    have hdisjU : Disjoint (P a) (I'.biUnion P) := by
      rw [Finset.disjoint_biUnion_right]
      intro j hj
      exact hdisj a (Finset.mem_insert_self a I') j (Finset.mem_insert_of_mem hj) fun h =>
        ha (by rw [h]; exact hj)
    have hG : ∀ p ∈ P a, ∀ n, (∏ i ∈ I', f i (p * n)) = ∏ i ∈ I', f i n := fun p hp n =>
      Finset.prod_congr rfl fun i hi =>
        hinv i (Finset.mem_insert_of_mem hi) a (Finset.mem_insert_self a I')
          (fun h => ha (by rw [← h]; exact hi)) p hp n
    have hF : ∀ p ∈ I'.biUnion P, ∀ n, f a (p * n) = f a n := fun p hp n => by
      obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
      exact hinv a (Finset.mem_insert_self a I') j (Finset.mem_insert_of_mem hj)
        (fun h => ha (by rw [h]; exact hj)) p hpj n
    have hih := ih
      (fun i hi j hj hij =>
        hdisj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
      (fun i hi j hj hij =>
        hinv i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij)
    rw [Finset.biUnion_insert, Finset.prod_insert ha, hfun,
      modelMean_union_mul hdisjU (fun n => ∏ i ∈ I', f i n) hG (f a) hF, hih]

/-! ### The bands -/

/-- `ω_T(pn) = ω_T(n)` for a set `T` of primes and a prime `p ∉ T`. -/
theorem primeHits_prime_mul {T : Finset ℕ} (hT : ∀ ℓ ∈ T, ℓ.Prime) {p : ℕ} (hp : p.Prime)
    (hpT : p ∉ T) (n : ℕ) : primeHits T (p * n) = primeHits T n := by
  unfold primeHits
  refine congrArg Finset.card (Finset.filter_congr fun ℓ hℓ => ?_)
  constructor
  · intro h
    rcases (hT ℓ hℓ).dvd_mul.mp h with h1 | h1
    · exfalso
      rcases (Nat.dvd_prime hp).mp h1 with h2 | h2
      · exact (hT ℓ hℓ).ne_one h2
      · apply hpT
        rw [← h2]
        exact hℓ
    · exact h1
  · intro h
    exact Dvd.dvd.mul_left h p

/-- The factor of one band does not see a prime outside the band. -/
theorem markFactor_prime_mul {T : Finset ℕ} (hT : ∀ ℓ ∈ T, ℓ.Prime) {p : ℕ} (hp : p.Prime)
    (hpT : p ∉ T) (q : ℝ) (n : ℕ) : markFactor q T (p * n) = markFactor q T n := by
  unfold markFactor
  rw [primeHits_prime_mul hT hp hpT n]

/-- A prime of a set of primes has exactly one divisor in the set. -/
theorem primeHits_self_of_mem {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {p : ℕ} (hp : p ∈ S) :
    primeHits S p = 1 := by
  unfold primeHits
  have h : (S.filter fun p' => p' ∣ p) = {p} := by
    ext p'
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩
      exact (Nat.prime_dvd_prime_iff_eq (hS p' h1) (hS p hp)).mp h2
    · intro h
      rw [h]
      exact ⟨hp, dvd_refl p⟩
  rw [h, Finset.card_singleton]

/-- Two bands with exponents `a < a'` are disjoint once `2 < L^{a' - a}`. -/
theorem bandPrimes_disjoint {a a' x : ℝ} (hL : 0 < Real.log x)
    (h : 2 < Real.log x ^ (a' - a)) : Disjoint (bandPrimes a x) (bandPrimes a' x) := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  obtain ⟨-, -, h1⟩ := mem_bandPrimes.mp hp
  obtain ⟨-, h2, -⟩ := mem_bandPrimes.mp hp'
  have h3 : Real.exp (Real.log x ^ a') ≤ Real.exp (2 * Real.log x ^ a) := h2.trans h1
  have h4 : Real.log x ^ a' ≤ 2 * Real.log x ^ a := Real.exp_le_exp.mp h3
  have h5 : Real.log x ^ a' = Real.log x ^ (a' - a) * Real.log x ^ a := by
    rw [← Real.rpow_add hL, sub_add_cancel]
  have h6 : 0 < Real.log x ^ a := Real.rpow_pos_of_pos hL a
  rw [h5] at h4
  have h7 : Real.log x ^ (a' - a) ≤ 2 := le_of_mul_le_mul_right h4 h6
  linarith

/-! ### One band -/

/-- `∏ (1 - a_i) ≥ 1 - ∑ a_i` for `0 ≤ a_i ≤ 1`. -/
theorem one_sub_sum_le_prod_one_sub (s : Finset ℕ) (a : ℕ → ℝ) (h0 : ∀ i ∈ s, 0 ≤ a i)
    (h1 : ∀ i ∈ s, a i ≤ 1) : 1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert b s hb ih =>
    have hb0 := h0 b (Finset.mem_insert_self b s)
    have hb1 := h1 b (Finset.mem_insert_self b s)
    have ih' := ih (fun i hi => h0 i (Finset.mem_insert_of_mem hi))
      (fun i hi => h1 i (Finset.mem_insert_of_mem hi))
    have hs0 : 0 ≤ ∑ i ∈ s, a i :=
      Finset.sum_nonneg fun i hi => h0 i (Finset.mem_insert_of_mem hi)
    rw [Finset.sum_insert hb, Finset.prod_insert hb]
    calc 1 - (a b + ∑ i ∈ s, a i) ≤ (1 - a b) * (1 - ∑ i ∈ s, a i) := by
          nlinarith [mul_nonneg hb0 hs0]
      _ ≤ (1 - a b) * ∏ i ∈ s, (1 - a i) := mul_le_mul_of_nonneg_left ih' (by linarith)

/-- The term of the model of a set `S` of primes at the configuration `{p}`. -/
theorem model_term_singleton (q : ℝ) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) {p : ℕ}
    (hp : p ∈ S) :
    (∏ p' ∈ ({p} : Finset ℕ), (1 / (p' : ℝ))) * (∏ p' ∈ S \ {p}, (1 - 1 / (p' : ℝ))) *
        markFactor q S (∏ p' ∈ ({p} : Finset ℕ), p') =
      1 / (p : ℝ) * (∏ p' ∈ S \ {p}, (1 - 1 / (p' : ℝ))) * (1 / reciprocalMass S) := by
  rw [Finset.prod_singleton, Finset.prod_singleton]
  unfold markFactor
  rw [primeHits_self_of_mem hS hp, Nat.sub_self, pow_zero, Nat.cast_one, one_mul]

/-- **One band**: `M_𝒫(q^{ω-1} ω / V) ≥ 1 - V` for a set `𝒫` of primes with `V > 0` and
`q ≥ 0`. -/
theorem one_sub_mass_le_modelMean_markFactor {q : ℝ} (hq : 0 ≤ q) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) (hV : 0 < reciprocalMass S) :
    1 - reciprocalMass S ≤ modelMean S (markFactor q S) := by
  have hcast : ∀ p ∈ S, (1 : ℝ) ≤ (p : ℝ) := fun p hp => by
    exact_mod_cast (hS p hp).one_lt.le
  have hinv0 : ∀ p ∈ S, (0 : ℝ) ≤ 1 / (p : ℝ) := fun p _ => by positivity
  have hinv1 : ∀ p ∈ S, 1 / (p : ℝ) ≤ 1 := fun p hp =>
    (div_le_one (by linarith [hcast p hp])).mpr (hcast p hp)
  -- the weights are nonnegative
  have hwt : ∀ T ∈ S.powerset, 0 ≤ (∏ p ∈ T, (1 / (p : ℝ))) *
      (∏ p ∈ S \ T, (1 - 1 / (p : ℝ))) * markFactor q S (∏ p ∈ T, p) := fun T _ =>
    mul_nonneg (mul_nonneg (Finset.prod_nonneg fun p _ => by positivity)
      (Finset.prod_nonneg fun p hp => by
        linarith [hinv1 p (Finset.mem_sdiff.mp hp).1])) (markFactor_nonneg hq S _)
  -- one configuration `{p}`
  have hone : ∀ p ∈ S, 1 / (p : ℝ) * ((1 - reciprocalMass S) / reciprocalMass S) ≤
      (∏ p' ∈ ({p} : Finset ℕ), (1 / (p' : ℝ))) * (∏ p' ∈ S \ {p}, (1 - 1 / (p' : ℝ))) *
        markFactor q S (∏ p' ∈ ({p} : Finset ℕ), p') := by
    intro p hp
    rw [model_term_singleton q hS hp]
    have hsub : S \ {p} ⊆ S := Finset.sdiff_subset
    have hW := one_sub_sum_le_prod_one_sub (S \ {p}) (fun p' => 1 / (p' : ℝ))
      (fun i hi => hinv0 i (hsub hi)) (fun i hi => hinv1 i (hsub hi))
    have hle : ∑ p' ∈ S \ {p}, 1 / (p' : ℝ) ≤ reciprocalMass S := by
      unfold reciprocalMass
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun i hi _ => hinv0 i hi
    have hprod : 1 - reciprocalMass S ≤ ∏ p' ∈ S \ {p}, (1 - 1 / (p' : ℝ)) := by linarith
    calc 1 / (p : ℝ) * ((1 - reciprocalMass S) / reciprocalMass S)
        = 1 / (p : ℝ) * (1 - reciprocalMass S) * (1 / reciprocalMass S) := by ring
      _ ≤ 1 / (p : ℝ) * (∏ p' ∈ S \ {p}, (1 - 1 / (p' : ℝ))) * (1 / reciprocalMass S) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (hinv0 p hp))
            (one_div_pos.mpr hV).le
  have hsubset : S.map ⟨fun p => ({p} : Finset ℕ), Finset.singleton_injective⟩ ⊆
      S.powerset := by
    intro T hT
    obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hT
    exact Finset.mem_powerset.mpr (Finset.singleton_subset_iff.mpr hp)
  have hsingle : ∑ p ∈ S, 1 / (p : ℝ) * ((1 - reciprocalMass S) / reciprocalMass S) ≤
      ∑ T ∈ S.map ⟨fun p => ({p} : Finset ℕ), Finset.singleton_injective⟩,
        (∏ p ∈ T, (1 / (p : ℝ))) * (∏ p ∈ S \ T, (1 - 1 / (p : ℝ))) *
          markFactor q S (∏ p ∈ T, p) := by
    rw [Finset.sum_map]
    exact Finset.sum_le_sum hone
  have hfirst : 1 - reciprocalMass S =
      ∑ p ∈ S, 1 / (p : ℝ) * ((1 - reciprocalMass S) / reciprocalMass S) := by
    have hsum : ∑ p ∈ S, 1 / (p : ℝ) = reciprocalMass S := rfl
    rw [← Finset.sum_mul, hsum, ← mul_div_assoc, mul_div_cancel_left₀ _ hV.ne']
  unfold modelMean
  calc 1 - reciprocalMass S
      = ∑ p ∈ S, 1 / (p : ℝ) * ((1 - reciprocalMass S) / reciprocalMass S) := hfirst
    _ ≤ ∑ T ∈ S.map ⟨fun p => ({p} : Finset ℕ), Finset.singleton_injective⟩,
          (∏ p ∈ T, (1 / (p : ℝ))) * (∏ p ∈ S \ T, (1 - 1 / (p : ℝ))) *
            markFactor q S (∏ p ∈ T, p) := hsingle
    _ ≤ ∑ T ∈ S.powerset, (∏ p ∈ T, (1 / (p : ℝ))) *
          (∏ p ∈ S \ T, (1 - 1 / (p : ℝ))) * markFactor q S (∏ p ∈ T, p) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsubset fun T hT _ => hwt T hT

/-! ### The statement -/

/-- **(ext:model-bounds)** (`[P-07:0063–0075]`) from Mertens' estimate for `∑ 1/p`, for
`0 ≤ q < 1`: `5^{-K} ≤ m_𝒲 ≤ C` and `M_x(𝒲²) ≤ C` for large `x`. For `0 < q < 1` this is the
field `modelBounds` of `ExtractionOpenLeaves d H b q q₀`. -/
theorem modelBounds_of_mertensReciprocal {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hM : MertensReciprocal) : ModelBounds q := by
  intro K
  obtain ⟨CW, hCW⟩ := arrayWeightBounded_of_mertensReciprocal hq0 hq1 hM K
  obtain ⟨Y₀, hY₀⟩ := dyadicPrimeMass_of_mertensReciprocal hM (1 / 10) (by norm_num)
  refine ⟨((1 : ℝ) / 5) ^ K, max CW (CW ^ 2), by positivity, fun 𝔞 => ?_⟩
  have hev1 : ∀ᶠ x : ℝ in atTop, ∀ i : Fin K, Y₀ ≤ Real.log x ^ 𝔞.exponent i := by
    refine Filter.eventually_all.mpr fun i => ?_
    have hpos : (0 : ℝ) < 𝔞.exponent i := lt_trans (by norm_num) (𝔞.gt_tenth i)
    exact ((tendsto_rpow_atTop hpos).comp Real.tendsto_log_atTop).eventually_ge_atTop Y₀
  have hev2 : ∀ᶠ x : ℝ in atTop, ∀ i j : Fin K, 𝔞.exponent i < 𝔞.exponent j →
      2 < Real.log x ^ (𝔞.exponent j - 𝔞.exponent i) := by
    refine Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j => ?_
    by_cases hij : 𝔞.exponent i < 𝔞.exponent j
    · have hpos : 0 < 𝔞.exponent j - 𝔞.exponent i := by linarith
      filter_upwards [((tendsto_rpow_atTop hpos).comp
        Real.tendsto_log_atTop).eventually_gt_atTop 2] with x hx _
      exact hx
    · exact Filter.Eventually.of_forall fun x h => absurd h hij
  filter_upwards [hCW 𝔞, hev1, hev2, Real.tendsto_log_atTop.eventually_gt_atTop 0]
    with x hW hx1 hx2 hL
  -- the bands
  have hprime : ∀ i : Fin K, ∀ p ∈ bandPrimes (𝔞.exponent i) x, p.Prime := fun i p hp =>
    (mem_bandPrimes.mp hp).1
  have hmass : ∀ i : Fin K,
      |reciprocalMass (bandPrimes (𝔞.exponent i) x) - Real.log 2| ≤ 1 / 10 := fun i =>
    hY₀ (Real.log x ^ 𝔞.exponent i) (hx1 i) (bandPrimes (𝔞.exponent i) x)
      (fun p hp => mem_bandPrimes.mp hp)
      (fun p hpp hlo hhi => mem_bandPrimes.mpr ⟨hpp, hlo.le, hhi.le⟩)
  have hlog2a := Real.log_two_gt_d9
  have hlog2b := Real.log_two_lt_d9
  have hdisj : ∀ i j : Fin K, i ≠ j →
      Disjoint (bandPrimes (𝔞.exponent i) x) (bandPrimes (𝔞.exponent j) x) := by
    intro i j hij
    rcases lt_or_gt_of_ne (𝔞.strictMono.injective.ne hij) with h | h
    · exact bandPrimes_disjoint hL (hx2 i j h)
    · exact (bandPrimes_disjoint hL (hx2 j i h)).symm
  -- the product formula
  have hprod : arrayMean q 𝔞 x = ∏ i : Fin K,
      modelMean (bandPrimes (𝔞.exponent i) x) (markFactor q (bandPrimes (𝔞.exponent i) x)) :=
    modelMean_biUnion_prod Finset.univ (fun i : Fin K => bandPrimes (𝔞.exponent i) x)
      (fun i => markFactor q (bandPrimes (𝔞.exponent i) x))
      (fun i _ j _ hij => hdisj i j hij)
      (fun i _ j _ hij p hp n =>
        markFactor_prime_mul (hprime i) (hprime j p hp)
          (Finset.disjoint_left.mp (hdisj j i hij.symm) hp) q n)
  -- the lower bound
  have hband : ∀ i : Fin K, (1 : ℝ) / 5 ≤
      modelMean (bandPrimes (𝔞.exponent i) x) (markFactor q (bandPrimes (𝔞.exponent i) x)) := by
    intro i
    have h1 := abs_le.mp (hmass i)
    have hV : 0 < reciprocalMass (bandPrimes (𝔞.exponent i) x) := by linarith [h1.1]
    have h2 := one_sub_mass_le_modelMean_markFactor hq0 (hprime i) hV
    linarith [h1.2]
  have hlow : ((1 : ℝ) / 5) ^ K ≤ arrayMean q 𝔞 x := by
    rw [hprod]
    calc ((1 : ℝ) / 5) ^ K = ∏ _i : Fin K, (1 : ℝ) / 5 := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ ∏ i : Fin K, modelMean (bandPrimes (𝔞.exponent i) x)
            (markFactor q (bandPrimes (𝔞.exponent i) x)) :=
          Finset.prod_le_prod (fun i _ => by norm_num) fun i _ => hband i
  -- the upper bounds
  have hP1 : ∀ p ∈ arrayPrimes 𝔞 x, 1 ≤ p := by
    intro p hp
    obtain ⟨i, -, hpi⟩ := Finset.mem_biUnion.mp hp
    exact (hprime i p hpi).one_lt.le
  have hup1 : arrayMean q 𝔞 x ≤ CW := by
    have h := modelMean_le_of_le hP1 (F := markedWeight q 𝔞 x) (G := fun _ => CW)
      fun n => (le_abs_self _).trans (hW n)
    rw [modelMean_const] at h
    exact h
  have hup2 : modelMean (arrayPrimes 𝔞 x) (fun n => markedWeight q 𝔞 x n ^ 2) ≤ CW ^ 2 := by
    have h := modelMean_le_of_le hP1 (F := fun n => markedWeight q 𝔞 x n ^ 2)
      (G := fun _ => CW ^ 2) fun n => by
        have h1 : markedWeight q 𝔞 x n ^ 2 = |markedWeight q 𝔞 x n| ^ 2 := (sq_abs _).symm
        rw [h1]
        exact pow_le_pow_left₀ (abs_nonneg _) (hW n) 2
    rw [modelMean_const] at h
    exact h
  exact ⟨hlow, hup1.trans (le_max_left _ _), hup2.trans (le_max_right _ _)⟩

end

end SimultaneousPrimitiveRoots.Unconditional.Supply.Extraction
