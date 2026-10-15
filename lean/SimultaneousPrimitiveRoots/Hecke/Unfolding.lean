module

public import SimultaneousPrimitiveRoots.Hecke.HeckeIntegralNF
public import SimultaneousPrimitiveRoots.Hecke.PoissonTorus

/-!
# Unfolding the unit group

Let `L ⊂ K` be stable under multiplication by units (for instance a fractional ideal). Every
nonzero `y ∈ L` is uniquely `η^k x` with `k ∈ ℤ^r` and `x ∈ L` in Mathlib's fundamental cone
(Dirichlet's unit theorem, `exist_unique_eq_mul_prod`, together with `exists_unit_smul_mem` and
`unit_smul_mem_iff_mem_torsion`). Multiplying by `η^k` translates the unit weights by `k`
(`normForm_unitPow_mul`). So for every `F` with `F(η^k x, p) = F(x, p + k)`,

`∑_{y ∈ L} ∫_{[0,1)^r} F(y, p) dp = ∑_{x ∈ L ∩ cone} ∫_{ℝ^r} F(x, p) dp`,

and with Hecke's integral the averaged Epstein zeta function of `L` becomes
`heckeConst · ∑_{x ∈ L ∩ cone} |N x|^{-2s/n}`.
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField NumberField.Units NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.mixedEmbedding.fundamentalCone MeasureTheory Set
open scoped ENNReal

variable {K : Type*} [Field K] [NumberField K]

/-- `η^k = ∏_i η_i^{k_i}` for the fundamental units. -/
def unitPow (k : Fin (rank K) → ℤ) : (𝓞 K)ˣ := ∏ i, fundSystem K i ^ k i

theorem unitPow_add (a b : Fin (rank K) → ℤ) : unitPow (a + b) = unitPow a * unitPow b := by
  unfold unitPow
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [Pi.add_apply, zpow_add]

theorem unitPow_zero : unitPow (0 : Fin (rank K) → ℤ) = 1 := by
  simp [unitPow]

theorem coe_unitPow (k : Fin (rank K) → ℤ) :
    ((unitPow k : (𝓞 K)ˣ) : K) = ∏ i, ((fundSystem K i : (𝓞 K)ˣ) : K) ^ k i := by
  unfold unitPow
  have : ∀ s : Finset (Fin (rank K)), ((∏ i ∈ s, fundSystem K i ^ k i : (𝓞 K)ˣ) : K) =
      ∏ i ∈ s, ((fundSystem K i : (𝓞 K)ˣ) : K) ^ k i := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.prod_insert hj, NumberField.Units.coe_mul,
        NumberField.Units.coe_zpow, ih]
  exact this Finset.univ

theorem norm_embedding_unitPow (k : Fin (rank K) → ℤ) (σ : K →+* ℂ) :
    ‖σ ((unitPow k : (𝓞 K)ˣ) : K)‖ = Real.exp (∑ i, (k i : ℝ) * unitLog K i σ) := by
  rw [coe_unitPow, map_prod, norm_prod, Real.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_zpow₀, norm_zpow]
  have hpos : 0 < ‖σ ((fundSystem K i : (𝓞 K)ˣ) : K)‖ := by
    rw [norm_pos_iff, map_ne_zero]
    exact NumberField.Units.coe_ne_zero _
  rw [← Real.rpow_intCast, Real.rpow_def_of_pos hpos, unitLog, mul_comm]

theorem unitWeight_mul_normSq_unitPow (p : Fin (rank K) → ℝ) (k : Fin (rank K) → ℤ)
    (σ : K →+* ℂ) :
    unitWeight p σ * Complex.normSq (σ ((unitPow k : (𝓞 K)ˣ) : K)) =
      unitWeight (p + intVec k) σ := by
  rw [Complex.normSq_eq_norm_sq, norm_embedding_unitPow, unitWeight, unitWeight, sq,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  simp only [Pi.add_apply, intVec, add_mul, Finset.sum_add_distrib]
  ring

/-- **Multiplying by `η^k` translates the weights by `k`.** -/
theorem normForm_unitPow_mul (k : Fin (rank K) → ℤ) (x : K) (p : Fin (rank K) → ℝ) :
    normForm (((unitPow k : (𝓞 K)ˣ) : K) * x) p = normForm x (p + intVec k) := by
  unfold normForm
  apply Finset.sum_congr rfl
  intro σ _
  rw [map_mul, Complex.normSq_mul, ← mul_assoc, unitWeight_mul_normSq_unitPow]

/-- Dirichlet uniqueness: `η^d` is a root of unity only for `d = 0`. -/
theorem eq_zero_of_unitPow_mem_torsion {d : Fin (rank K) → ℤ} (h : unitPow d ∈ torsion K) :
    d = 0 := by
  obtain ⟨z, _, huniq⟩ := exist_unique_eq_mul_prod K (unitPow d)
  have h1 := huniq (⟨1, (torsion K).one_mem⟩, d) (by simp [unitPow])
  have h2 := huniq (⟨unitPow d, h⟩, 0) (by simp)
  exact (Prod.mk.inj (h1.trans h2.symm)).2

omit [NumberField K] in
theorem mixedEmbedding_unit_mul (u : (𝓞 K)ˣ) (x : K) :
    mixedEmbedding K ((u : K) * x) = u • mixedEmbedding K x := by
  rw [unitSMul_smul, map_mul]

variable (L : Set K)

/-- The nonzero points of `L` in the fundamental cone. -/
def coneSet : Set K := {x | x ∈ L ∧ x ≠ 0 ∧ mixedEmbedding K x ∈ fundamentalCone K}

/-- The nonzero points of `L`. -/
def nzSet : Set K := {x | x ∈ L ∧ x ≠ 0}

theorem mem_coneSet {x : K} :
    x ∈ coneSet L ↔ x ∈ L ∧ x ≠ 0 ∧ mixedEmbedding K x ∈ fundamentalCone K := Iff.rfl

variable {L}

/-- `(x, k) ↦ η^k x`. -/
def unfoldMap (hL : ∀ (u : (𝓞 K)ˣ) (x : K), x ∈ L → (u : K) * x ∈ L) :
    coneSet L × (Fin (rank K) → ℤ) → nzSet L :=
  fun z => ⟨((unitPow z.2 : (𝓞 K)ˣ) : K) * z.1,
    hL _ _ z.1.2.1, mul_ne_zero (NumberField.Units.coe_ne_zero _) z.1.2.2.1⟩

theorem unfoldMap_injective (hL : ∀ (u : (𝓞 K)ˣ) (x : K), x ∈ L → (u : K) * x ∈ L) :
    Function.Injective (unfoldMap hL) := by
  rintro ⟨⟨x, hx⟩, k⟩ ⟨⟨x', hx'⟩, k'⟩ h0
  have h : ((unitPow k : (𝓞 K)ˣ) : K) * x = ((unitPow k' : (𝓞 K)ˣ) : K) * x' :=
    congrArg Subtype.val h0
  set u := unitPow (k - k') with hu
  have hsplit : ((unitPow k : (𝓞 K)ˣ) : K) = (u : K) * ((unitPow k' : (𝓞 K)ˣ) : K) := by
    rw [← NumberField.Units.coe_mul, hu, ← unitPow_add, sub_add_cancel]
  have hk'0 : ((unitPow k' : (𝓞 K)ˣ) : K) ≠ 0 := NumberField.Units.coe_ne_zero _
  have hux : (u : K) * x = x' := by
    rw [hsplit, mul_assoc] at h
    have h2 : ((unitPow k' : (𝓞 K)ˣ) : K) * ((u : K) * x) =
        ((unitPow k' : (𝓞 K)ˣ) : K) * x' := by
      rw [← h]
      ring
    exact mul_left_cancel₀ hk'0 h2
  have htor : u ∈ torsion K := by
    rw [← unit_smul_mem_iff_mem_torsion hx.2.2, ← mixedEmbedding_unit_mul, hux]
    exact hx'.2.2
  have hd : k - k' = 0 := eq_zero_of_unitPow_mem_torsion htor
  have hkk : k = k' := sub_eq_zero.mp hd
  subst hkk
  have hx_eq : x = x' := by
    rw [hu, sub_self, unitPow_zero] at hux
    simpa using hux
  subst hx_eq
  rfl

theorem unfoldMap_surjective (hL : ∀ (u : (𝓞 K)ˣ) (x : K), x ∈ L → (u : K) * x ∈ L) :
    Function.Surjective (unfoldMap hL) := by
  rintro ⟨y, hyL, hy0⟩
  have hnorm : mixedEmbedding.norm (mixedEmbedding K y) ≠ 0 := by
    rw [norm_eq_norm]
    simpa using hy0
  obtain ⟨u, hu⟩ := exists_unit_smul_mem hnorm
  obtain ⟨⟨ζ, e⟩, hζe, -⟩ := exist_unique_eq_mul_prod K u⁻¹
  simp only at hζe
  set v : (𝓞 K)ˣ := (ζ : (𝓞 K)ˣ) * u with hv
  have hvmem : mixedEmbedding K ((v : K) * y) ∈ fundamentalCone K := by
    rw [mixedEmbedding_unit_mul, hv, mul_smul]
    exact torsion_smul_mem_of_mem hu ζ.2
  have hone : unitPow e * v = 1 := by
    have h1 : unitPow e * v = u⁻¹ * u := by
      rw [hζe, hv, unitPow]
      ac_rfl
    rw [h1, inv_mul_cancel]
  refine ⟨(⟨(v : K) * y, (mem_coneSet L).mpr ⟨hL _ _ hyL,
    mul_ne_zero (NumberField.Units.coe_ne_zero _) hy0, hvmem⟩⟩, e), Subtype.ext ?_⟩
  show ((unitPow e : (𝓞 K)ˣ) : K) * ((v : K) * y) = y
  rw [← mul_assoc, ← NumberField.Units.coe_mul, hone, NumberField.Units.coe_one, one_mul]

/-- The unfolding bijection `(L ∩ cone) × ℤ^r ≃ L \ {0}`. -/
def unfoldEquiv (hL : ∀ (u : (𝓞 K)ˣ) (x : K), x ∈ L → (u : K) * x ∈ L) :
    coneSet L × (Fin (rank K) → ℤ) ≃ nzSet L :=
  Equiv.ofBijective _ ⟨unfoldMap_injective hL, unfoldMap_surjective hL⟩

variable (K) in
/-- Tiling `ℝ^r` by the unit cube. -/
theorem lintegral_eq_tsum_unitCube (f : (Fin (rank K) → ℝ) → ℝ≥0∞) :
    ∫⁻ p, f p = ∑' k : Fin (rank K) → ℤ, ∫⁻ p in unitCube K, f (p + intVec k) := by
  rw [isAddFundamentalDomain_cube.lintegral_eq_tsum'' f,
    ← (intLatticeEquiv (d := Fin (rank K))).tsum_eq]
  apply tsum_congr
  intro k
  unfold unitCube
  congr 1
  funext p
  simp only [AddSubgroup.vadd_def, vadd_eq_add, intLatticeEquiv_coe]
  rw [add_comm]

/-- **Unfolding.** -/
theorem tsum_lintegral_unfold (hL : ∀ (u : (𝓞 K)ˣ) (x : K), x ∈ L → (u : K) * x ∈ L)
    (F : K → (Fin (rank K) → ℝ) → ℝ≥0∞) (hF0 : ∀ p, F 0 p = 0)
    (hFshift : ∀ k x p, F (((unitPow k : (𝓞 K)ˣ) : K) * x) p = F x (p + intVec k)) :
    ∑' x : L, ∫⁻ p in unitCube K, F x p = ∑' x : coneSet L, ∫⁻ p, F x p := by
  classical
  have h1 : ∑' x : L, ∫⁻ p in unitCube K, F x p =
      ∑' x : nzSet L, ∫⁻ p in unitCube K, F x p := by
    rw [tsum_subtype L (fun x => ∫⁻ p in unitCube K, F x p),
      tsum_subtype (nzSet L) (fun x => ∫⁻ p in unitCube K, F x p)]
    congr 1
    funext x
    by_cases hx0 : x = 0
    · subst hx0
      simp [hF0, Set.indicator]
    · by_cases hxL : x ∈ L
      · have : x ∈ nzSet L := ⟨hxL, hx0⟩
        rw [Set.indicator_of_mem hxL, Set.indicator_of_mem this]
      · have : x ∉ nzSet L := fun h => hxL h.1
        rw [Set.indicator_of_notMem hxL, Set.indicator_of_notMem this]
  rw [h1, ← (unfoldEquiv hL).tsum_eq, ENNReal.tsum_prod']
  apply tsum_congr
  intro x
  rw [lintegral_eq_tsum_unitCube K]
  apply tsum_congr
  intro k
  change ∫⁻ p in unitCube K, F (((unitPow k : (𝓞 K)ˣ) : K) * (x : K)) p = _
  simp_rw [hFshift]

end SimultaneousPrimitiveRoots.Hecke

end
