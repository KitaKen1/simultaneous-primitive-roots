module

public import SimultaneousPrimitiveRoots.FrozenMultivariateSeries
public import SimultaneousPrimitiveRoots.NumberFieldFrozenProduct
public import SimultaneousPrimitiveRoots.NumberFieldNormSeries

@[expose] public section

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
noncomputable section

/-- The actual ideal encoded by a frozen exponent vector. -/
def numberFieldFrozenIdeal (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (e : s → ℕ) : Ideal (𝓞 K) :=
  ∏ v : s, v.val.asIdeal ^ e v

theorem numberFieldFrozenIdeal_absNorm (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (e : s → ℕ) :
    (numberFieldFrozenIdeal K s e).absNorm = ∏ v : s, v.val.asIdeal.absNorm ^ e v := by
  simp [numberFieldFrozenIdeal, map_prod, map_pow]

theorem numberFieldFrozenIdeal_ne_bot (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (e : s → ℕ) :
    numberFieldFrozenIdeal K s e ≠ ⊥ := by
  apply mt Ideal.absNorm_eq_zero_iff.mpr
  rw [numberFieldFrozenIdeal_absNorm]
  exact ne_of_gt (Finset.prod_pos fun v _ => pow_pos
    (lt_trans Nat.zero_lt_one (NumberField.HeightOneSpectrum.one_lt_absNorm v.val)) _)

/-- The vector weight is the coefficient times the norm of an actual ideal,
not a formal independent variable. -/
theorem numberFieldFrozenIdeal_dirichletTerm (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (σ : ℝ) (e : s → ℕ) :
    frozenExponentTerm (fun v : s => (v.val.asIdeal.absNorm : ℝ)) σ e =
      (∏ v : s, frozenLocalMajorant (v.val.asIdeal.absNorm : ℝ) (e v)) *
        ((numberFieldFrozenIdeal K s e).absNorm : ℝ) ^ (-σ) := by
  classical
  rw [frozenExponentTerm, Finset.prod_mul_distrib, numberFieldFrozenIdeal_absNorm,
    Nat.cast_prod]
  congr 1
  calc
    _ = ∏ v : s, ((v.val.asIdeal.absNorm : ℝ) ^ e v) ^ (-σ) := by
      apply Finset.prod_congr rfl
      intro v _
      rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
      congr 1
      ring
    _ = _ := by
      simpa only [Nat.cast_pow] using Real.finsetProd_rpow Finset.univ
        (fun v : s => (v.val.asIdeal.absNorm : ℝ) ^ e v) (fun _ _ => by positivity) (-σ)

/-- All ideals are allowed in the majorant. For sigma>1/2 the zero ideal
contributes zero; squarefreeness and coprimality only remove nonnegative terms. -/
def numberFieldFrozenMajorantTerm (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (σ : ℝ)
    (x : (s → ℕ) × Ideal (𝓞 K) × Ideal (𝓞 K)) : ℝ :=
  frozenExponentTerm (fun v : s => (v.val.asIdeal.absNorm : ℝ)) σ x.1 *
    ((x.2.1.absNorm : ℝ) ^ (-(σ + 1 / 2)) *
      (x.2.2.absNorm : ℝ) ^ (-(3 * σ + 1)))

theorem numberFieldFrozenMajorantTerm_nonneg (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (σ : ℝ)
    (x : (s → ℕ) × Ideal (𝓞 K) × Ideal (𝓞 K)) :
    0 ≤ numberFieldFrozenMajorantTerm K s σ x := by
  apply mul_nonneg
  · exact frozenExponentTerm_nonneg _ (fun _ => Nat.cast_nonneg _) _ _
  · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The separated summable weight is exactly the paper's frequency norm
weight for nonzero ideals c and n. No coprimality between c and n is used. -/
theorem numberFieldFrozenMajorantTerm_eq_frequency
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (σ : ℝ) (e : s → ℕ)
    (c n : Ideal (𝓞 K)) (hc : c ≠ ⊥) (hn : n ≠ ⊥) :
    numberFieldFrozenMajorantTerm K s σ (e, c, n) =
      (∏ v : s, frozenLocalMajorant (v.val.asIdeal.absNorm : ℝ) (e v)) *
        (c.absNorm : ℝ) ^ (-(1 / 2 : ℝ)) * (n.absNorm : ℝ) ^ (-1 : ℝ) *
          ((numberFieldFrozenIdeal K s e * c * n ^ 3).absNorm : ℝ) ^ (-σ) := by
  have hc0 : 0 < (c.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hc)
  have hn0 : 0 < (n.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (mt Ideal.absNorm_eq_zero_iff.mp hn)
  have ha0 : 0 ≤ ((numberFieldFrozenIdeal K s e).absNorm : ℝ) := Nat.cast_nonneg _
  have hcw : (c.absNorm : ℝ) ^ (-(σ + 1 / 2)) =
      (c.absNorm : ℝ) ^ (-(1 / 2 : ℝ)) * (c.absNorm : ℝ) ^ (-σ) := by
    rw [← Real.rpow_add hc0]
    congr 1
    ring
  have hnw : (n.absNorm : ℝ) ^ (-(3 * σ + 1)) =
      (n.absNorm : ℝ) ^ (-1 : ℝ) * ((n.absNorm : ℝ) ^ (3 : ℕ)) ^ (-σ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn0.le, ← Real.rpow_add hn0]
    congr 1
    ring
  rw [numberFieldFrozenMajorantTerm, numberFieldFrozenIdeal_dirichletTerm,
    hcw, hnw, map_mul, map_mul, map_pow, Nat.cast_mul, Nat.cast_mul, Nat.cast_pow,
    Real.mul_rpow (mul_nonneg ha0 hc0.le) (by positivity), Real.mul_rpow ha0 hc0.le]
  ring

theorem numberFieldFrozenMajorantTerm_hasSum (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 / 2 < σ) :
    HasSum (numberFieldFrozenMajorantTerm K s σ)
      ((∏ v ∈ s, frozenLocalDirichlet (v.asIdeal.absNorm : ℝ) σ) *
        ((∑' c : Ideal (𝓞 K), (c.absNorm : ℝ) ^ (-(σ + 1 / 2))) *
          ∑' n : Ideal (𝓞 K), (n.absNorm : ℝ) ^ (-(3 * σ + 1)))) := by
  have hc := numberField_idealNorm_rpow_summable K (σ := σ + 1 / 2) (by linarith)
  have hn := numberField_idealNorm_rpow_summable K (σ := 3 * σ + 1) (by linarith)
  have hcn := hc.mul_of_nonneg hn (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hN (v : s) : 2 ≤ (v.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast (show 2 ≤ v.val.asIdeal.absNorm by
      have := NumberField.HeightOneSpectrum.one_lt_absNorm v.val
      omega)
  have he := frozenExponentTerm_hasSum (fun v : s => (v.val.asIdeal.absNorm : ℝ)) hN
    (by linarith : 0 ≤ σ)
  have hprod := he.summable.mul_of_nonneg hcn
    (fun _ => frozenExponentTerm_nonneg _ (fun _ => Nat.cast_nonneg _) _ _)
    (fun _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  have hsupport : (∏ v : s, frozenLocalDirichlet (v.val.asIdeal.absNorm : ℝ) σ) =
      ∏ v ∈ s, frozenLocalDirichlet (v.asIdeal.absNorm : ℝ) σ := by
    simpa only [Finset.attach_eq_univ] using
      Finset.prod_attach s (fun v => frozenLocalDirichlet (v.asIdeal.absNorm : ℝ) σ)
  rw [← hsupport]
  exact he.mul (hc.hasSum.mul hn.hasSum hcn) hprod

theorem numberFieldFrozenMajorantTerm_summable (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (numberFieldFrozenMajorantTerm K s σ) :=
  (numberFieldFrozenMajorantTerm_hasSum K s hσ).summable

theorem numberFieldFrozenMajorantTerm_tsum (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 / 2 < σ) :
    (∑' x, numberFieldFrozenMajorantTerm K s σ x) =
      (∏ v ∈ s, frozenLocalDirichlet (v.asIdeal.absNorm : ℝ) σ) *
        ((∑' c : Ideal (𝓞 K), (c.absNorm : ℝ) ^ (-(σ + 1 / 2))) *
          ∑' n : Ideal (𝓞 K), (n.absNorm : ℝ) ^ (-(3 * σ + 1))) :=
  (numberFieldFrozenMajorantTerm_hasSum K s hσ).tsum_eq

/-- The two ideal norm series depend on sigma and K, but the small-prime
absorption constant is uniform in both sigma and the frozen support. -/
theorem numberFieldFrozenMajorantTerm_subpower (K : Type*) [Field K] [NumberField K]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset (HeightOneSpectrum (𝓞 K))) (σ : ℝ), 1 / 2 < σ →
      (∑' x, numberFieldFrozenMajorantTerm K s σ x) ≤
        C * (∏ v ∈ s, (v.asIdeal.absNorm : ℝ)) ^ ε *
          ((∑' c : Ideal (𝓞 K), (c.absNorm : ℝ) ^ (-(σ + 1 / 2))) *
            ∑' n : Ideal (𝓞 K), (n.absNorm : ℝ) ^ (-(3 * σ + 1))) := by
  obtain ⟨C, hC, h⟩ := numberField_frozenLocalDirichlet_product_bound K hε
  refine ⟨C, hC, fun s σ hσ => ?_⟩
  rw [numberFieldFrozenMajorantTerm_tsum K s hσ]
  exact mul_le_mul_of_nonneg_right (h s σ (by linarith))
    (mul_nonneg (tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- Any restrictions on frozen exponents and on the two ideals may be
imposed after convergence; their actual subseries is bounded by the full sum. -/
theorem numberFieldFrozenMajorantTerm_restricted (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 / 2 < σ)
    (U : Set ((s → ℕ) × Ideal (𝓞 K) × Ideal (𝓞 K))) :
    Summable (fun x : U => numberFieldFrozenMajorantTerm K s σ x.val) ∧
      (∑' x : U, numberFieldFrozenMajorantTerm K s σ x.val) ≤
        ∑' x, numberFieldFrozenMajorantTerm K s σ x := by
  have h := numberFieldFrozenMajorantTerm_summable K s hσ
  exact ⟨h.subtype U, Summable.tsum_subtype_le _ U
    (numberFieldFrozenMajorantTerm_nonneg K s σ) h⟩

/-- Absolute convergence for complex coefficients dominated by the actual
scalar majorant. No analytic estimate for theta coefficients is asserted here. -/
theorem numberFieldFrozenMajorantTerm_complex_summable
    (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) {σ : ℝ} (hσ : 1 / 2 < σ)
    (a : (s → ℕ) × Ideal (𝓞 K) × Ideal (𝓞 K) → ℂ)
    (ha : ∀ x, ‖a x‖ ≤ numberFieldFrozenMajorantTerm K s σ x) : Summable a := by
  exact ((numberFieldFrozenMajorantTerm_summable K s hσ).of_nonneg_of_le
    (fun _ => norm_nonneg _) ha).of_norm

end
end SimultaneousPrimitiveRoots
