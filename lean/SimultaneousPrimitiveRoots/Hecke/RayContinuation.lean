module

public import SimultaneousPrimitiveRoots.Hecke.RayCone
public import SimultaneousPrimitiveRoots.Hecke.DedekindContinuation
public import TauCeti.RingTheory.Ideal.CoprimeCoset

/-!
# Hecke's continuation of the partial zeta functions of ray classes

Let `𝔪` be a modulus of `K` with no infinite part and finite part `𝔪₀ ≠ 𝓞`, and `C` a ray class.
Choose `𝔟 ∈ C⁻¹` integral and prime to `𝔪` (`rayRep`), and `ξ ∈ 𝔟` with `ξ ≡ 1 (mod 𝔪₀)`
(`rayGen`). The elements of `𝔟` congruent to a unit modulo `𝔪₀` are the disjoint union of the
cosets `u ξ + 𝔟𝔪₀` (`RayCone.lean`), so the sum `rayΛ` of Hecke's coset `Λ`s is holomorphic on
`ℂ \ {n/2}` (no pole at `0`: the cosets avoid `0`), and at real `s = nσ/2`, `σ > 1`, it is

`π^{-s} Γ(s) heckeConst K s · w · N𝔟^{-σ} · ∑_{𝔞 ∈ C} N𝔞^{-σ}`   (`rayΛ_ofReal`).

Dividing by the entire coefficient of `DedekindContinuation.lean` gives `rayZetaHecke`,
holomorphic on `ℂ \ {1}` and equal to the partial zeta function `∑_{𝔞 ∈ C} N𝔞^{-σ}` for real
`σ > 1` (`rayZetaHecke_ofReal`). Main result: `exists_rayPartialZeta_continuation` (step Z2 of
`docs/unconditional-roadmap.md`).
-/

@[expose] public section

noncomputable section

namespace SimultaneousPrimitiveRoots.Hecke

open NumberField NumberField.Units Ideal Module Filter Topology
open TauCeti.GlobalNumberFields
open scoped nonZeroDivisors ENNReal Real

variable {K : Type*} [Field K] [NumberField K] (𝔪 : Modulus K)

instance : Finite (unitResidues 𝔪.finitePart) := finite_unitResidues _ 𝔪.finitePart_ne_bot

instance : Fintype (unitResidues 𝔪.finitePart) := Fintype.ofFinite _

/-! ### The data of a ray class -/

/-- An integral ideal prime to `𝔪` in the class `c⁻¹`. -/
def rayRep (c : RayClassGroup 𝔪) : integralIdealsPrimeTo 𝔪 := (idealClass_surjective 𝔪 c⁻¹).choose

theorem rayRep_spec (c : RayClassGroup 𝔪) : idealClass 𝔪 (rayRep 𝔪 c) = c⁻¹ :=
  (idealClass_surjective 𝔪 c⁻¹).choose_spec

theorem rayRep_sup (c : RayClassGroup 𝔪) :
    (rayRep 𝔪 c : Ideal (𝓞 K)) ⊔ 𝔪.finitePart = ⊤ :=
  (Modulus.isCoprimeTo_iff_sup_eq_top.mp (Modulus.mem_integralIdealsPrimeTo.mp (rayRep 𝔪 c).prop)).2

theorem exists_rayGen (c : RayClassGroup 𝔪) :
    ∃ ξ ∈ (rayRep 𝔪 c : Ideal (𝓞 K)), ξ - 1 ∈ 𝔪.finitePart :=
  Ideal.isCoprime_iff_exists_mem_and_sub_one_mem.mp (Ideal.isCoprime_iff_sup_eq.mpr (rayRep_sup 𝔪 c))

/-- An element of `rayRep c` congruent to one modulo `𝔪₀`. -/
def rayGen (c : RayClassGroup 𝔪) : 𝓞 K := (exists_rayGen 𝔪 c).choose

theorem rayGen_mem (c : RayClassGroup 𝔪) : rayGen 𝔪 c ∈ (rayRep 𝔪 c : Ideal (𝓞 K)) :=
  (exists_rayGen 𝔪 c).choose_spec.1

theorem rayGen_sub_one_mem (c : RayClassGroup 𝔪) : rayGen 𝔪 c - 1 ∈ 𝔪.finitePart :=
  (exists_rayGen 𝔪 c).choose_spec.2

/-- The lattice `𝔟 𝔪₀` of the class `c`. -/
def rayLattice (c : RayClassGroup 𝔪) : (Ideal (𝓞 K))⁰ :=
  ⟨(rayRep 𝔪 c : Ideal (𝓞 K)) * 𝔪.finitePart, mem_nonZeroDivisors_of_ne_zero fun h =>
    (Ideal.mul_eq_bot.mp h).elim (coe_ne_bot_of_mem 𝔪 _) 𝔪.finitePart_ne_bot⟩

/-- The fractional ideal of `rayLattice c`. -/
abbrev rayFrac (c : RayClassGroup 𝔪) : (FractionalIdeal (𝓞 K)⁰ K)ˣ :=
  FractionalIdeal.mk0 K (rayLattice 𝔪 c)

/-- The index type of the lattice basis of `rayLattice c`. -/
abbrev rayIdx (c : RayClassGroup 𝔪) := Free.ChooseBasisIndex ℤ (rayFrac 𝔪 c)

/-- A `ℚ`-basis of `K` that is a `ℤ`-basis of `rayLattice c`. -/
def rayBasis (c : RayClassGroup 𝔪) : Basis (rayIdx 𝔪 c) ℚ K :=
  basisOfFractionalIdeal K (rayFrac 𝔪 c)

theorem card_rayIdx (c : RayClassGroup 𝔪) :
    Fintype.card (rayIdx 𝔪 c) = Fintype.card (K →+* ℂ) := by
  rw [NumberField.Embeddings.card, Module.finrank_eq_card_basis (rayBasis 𝔪 c)]

theorem card_rayIdx_eq_finrank (c : RayClassGroup 𝔪) :
    Fintype.card (rayIdx 𝔪 c) = finrank ℚ K := by
  rw [card_rayIdx, NumberField.Embeddings.card]

/-- Indexing the lattice basis by the complex embeddings. -/
def rayEmb (c : RayClassGroup 𝔪) : rayIdx 𝔪 c ≃ (K →+* ℂ) :=
  Fintype.equivOfCardEq (card_rayIdx 𝔪 c)

instance (c : RayClassGroup 𝔪) : Nonempty (rayIdx 𝔪 c) := by
  rw [← Fintype.card_pos_iff, card_rayIdx_eq_finrank]
  exact Module.finrank_pos

theorem latticeSet_rayBasis (c : RayClassGroup 𝔪) :
    latticeSet (rayBasis 𝔪 c : rayIdx 𝔪 c → K) =
      idealInK ((rayRep 𝔪 c : Ideal (𝓞 K)) * 𝔪.finitePart) :=
  latticeSet_basisOfFractionalIdeal (rayLattice 𝔪 c)

theorem cosetSet_rayBasis (c : RayClassGroup 𝔪) :
    cosetSet (rayBasis 𝔪 c : rayIdx 𝔪 c → K) (rayShift 𝔪.finitePart (rayGen 𝔪 c)) =
      raySet 𝔪.finitePart (rayRep 𝔪 c : Ideal (𝓞 K)) :=
  cosetSet_rayShift_eq (rayRep_sup 𝔪 c) (latticeSet_rayBasis 𝔪 c) (rayGen_mem 𝔪 c)
    (rayGen_sub_one_mem 𝔪 c)

/-! ### Hecke's `Λ` of a ray class -/

variable {𝔪}

open scoped Classical in
/-- **Hecke's `Λ` of the ray class `c`**: the sum of the coset `Λ`s over `u ξ + 𝔟𝔪₀`. -/
def rayΛ (hnt : 𝔪.finitePart ≠ ⊤) (c : RayClassGroup 𝔪) (s : ℂ) : ℂ :=
  ∑ ρ : unitResidues 𝔪.finitePart, (heckeShiftedFEPair (rayBasis 𝔪 c) (rayEmb 𝔪 c)
    (rayShift_notMem hnt (latticeSet_rayBasis 𝔪 c) (rayGen_sub_one_mem 𝔪 c) ρ)).Λ s

/-- `rayΛ` is holomorphic away from `n/2`. -/
theorem differentiableAt_rayΛ (hnt : 𝔪.finitePart ≠ ⊤) (c : RayClassGroup 𝔪) {s : ℂ}
    (hs : s ≠ ((finrank ℚ K : ℝ) / 2 : ℝ)) : DifferentiableAt ℂ (rayΛ hnt c) s := by
  classical
  unfold rayΛ
  refine DifferentiableAt.fun_sum (u := Finset.univ) fun ρ _ => ?_
  refine heckeShiftedFEPair_differentiableAt _ _ _ ?_
  rwa [card_rayIdx_eq_finrank]

/-- The cone sum of the ray set and the partial zeta function of the class, at real `σ > 1`. -/
theorem cone_rayClass_relation (hinf : 𝔪.infinitePart = ∅) {σ : ℝ} (hσ : 1 < σ)
    (c : RayClassGroup 𝔪) :
    ∑' x : coneSet (raySet 𝔪.finitePart (rayRep 𝔪 c : Ideal (𝓞 K))),
        |((Algebra.norm ℚ (x : K) : ℚ) : ℝ)| ^ (-σ) =
      torsionOrder K * (absNorm (rayRep 𝔪 c : Ideal (𝓞 K)) : ℝ) ^ (-σ) *
        ∑' 𝔞 : {𝔞 : integralIdealsPrimeTo 𝔪 // idealClass 𝔪 𝔞 = c},
          (absNorm (𝔞.1 : Ideal (𝓞 K)) : ℝ) ^ (-σ) := by
  set 𝔟 := rayRep 𝔪 c
  have hE := tsum_coneSet_raySet_eq_class 𝔪 hinf 𝔟 (rayRep_spec 𝔪 c)
    (fun t => ENNReal.ofReal (t ^ (-σ)))
  have hsplit : ∀ 𝔞 : {𝔞 : integralIdealsPrimeTo 𝔪 // idealClass 𝔪 𝔞 = c},
      ENNReal.ofReal (((absNorm (𝔟 : Ideal (𝓞 K)) : ℝ) * absNorm (𝔞.1 : Ideal (𝓞 K))) ^ (-σ)) =
        ENNReal.ofReal ((absNorm (𝔟 : Ideal (𝓞 K)) : ℝ) ^ (-σ)) *
          ENNReal.ofReal ((absNorm (𝔞.1 : Ideal (𝓞 K)) : ℝ) ^ (-σ)) := fun 𝔞 => by
    rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  simp_rw [hsplit] at hE
  rw [ENNReal.tsum_mul_left] at hE
  -- finiteness of the class sum: it is part of the Dedekind zeta series
  have hinj : Function.Injective fun 𝔞 : {𝔞 : integralIdealsPrimeTo 𝔪 // idealClass 𝔪 𝔞 = c} =>
      (⟨(𝔞.1 : Ideal (𝓞 K)), mem_nonZeroDivisors_of_ne_zero (coe_ne_bot_of_mem 𝔪 𝔞.1)⟩ :
        (Ideal (𝓞 K))⁰) := by
    intro 𝔞 𝔞' h
    exact Subtype.ext (Subtype.ext (congrArg (fun I : (Ideal (𝓞 K))⁰ => (I : Ideal (𝓞 K))) h))
  have hcfin : ∑' 𝔞 : {𝔞 : integralIdealsPrimeTo 𝔪 // idealClass 𝔪 𝔞 = c},
      ENNReal.ofReal ((absNorm (𝔞.1 : Ideal (𝓞 K)) : ℝ) ^ (-σ)) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_comp_le_tsum_of_injective hinj
      (fun I : (Ideal (𝓞 K))⁰ => ENNReal.ofReal ((absNorm (I : Ideal (𝓞 K)) : ℝ) ^ (-σ))))
    rw [tsum_ideal_eq_dedekindZeta K hσ]
    exact ENNReal.ofReal_ne_top
  have hxfin : ∑' x : coneSet (raySet 𝔪.finitePart (𝔟 : Ideal (𝓞 K))),
      ENNReal.ofReal (|((Algebra.norm ℚ (x : K) : ℚ) : ℝ)| ^ (-σ)) ≠ ⊤ := by
    rw [hE]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hcfin)
  rw [ennreal_tsum_ofReal_eq (fun _ => Real.rpow_nonneg (abs_nonneg _) _) hxfin,
    ennreal_tsum_ofReal_eq (fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) hcfin] at hE
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hE
  rw [ENNReal.ofReal_eq_ofReal_iff (tsum_nonneg fun _ => Real.rpow_nonneg (abs_nonneg _) _)
    (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (tsum_nonneg fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)))] at hE
  rw [hE]
  ring

/-- **Real values of `rayΛ`.** -/
theorem rayΛ_ofReal (hinf : 𝔪.infinitePart = ∅) (hnt : 𝔪.finitePart ≠ ⊤)
    (c : RayClassGroup 𝔪) {σ : ℝ} (hσ : 1 < σ) :
    rayΛ hnt c ((finrank ℚ K * σ / 2 : ℝ) : ℂ) =
      ((π ^ (-(finrank ℚ K * σ / 2)) * Real.Gamma (finrank ℚ K * σ / 2) *
        (heckeConst K (finrank ℚ K * σ / 2) * (torsionOrder K *
          (absNorm (rayRep 𝔪 c : Ideal (𝓞 K)) : ℝ) ^ (-σ) *
            ∑' 𝔞 : {𝔞 : integralIdealsPrimeTo 𝔪 // idealClass 𝔪 𝔞 = c},
              (absNorm (𝔞.1 : Ideal (𝓞 K)) : ℝ) ^ (-σ))) : ℝ) : ℂ) := by
  classical
  set n : ℝ := (finrank ℚ K : ℝ) with hn
  have hn0 : 0 < n := by
    rw [hn]
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  set s' : ℝ := n * σ / 2 with hs'
  have hσeq : 2 * s' / n = σ := by rw [hs']; field_simp
  have hcard : (Fintype.card (rayIdx 𝔪 c) : ℝ) / 2 < s' := by
    rw [card_rayIdx_eq_finrank, hs']
    have : n / 2 < n * σ / 2 := by nlinarith
    exact this
  have hS : ∀ (u : (𝓞 K)ˣ) (x : K), x ∈ cosetSet (rayBasis 𝔪 c : rayIdx 𝔪 c → K)
      (rayShift 𝔪.finitePart (rayGen 𝔪 c)) → (u : K) * x ∈ cosetSet (rayBasis 𝔪 c : rayIdx 𝔪 c → K)
        (rayShift 𝔪.finitePart (rayGen 𝔪 c)) := fun u x hx => by
    rw [cosetSet_rayBasis] at hx ⊢
    exact raySet_unit_mul _ _ u x hx
  have hΛ := sum_heckeShiftedFEPair_ofReal (rayBasis 𝔪 c) (rayEmb 𝔪 c)
    (rayShift 𝔪.finitePart (rayGen 𝔪 c))
    (rayShift_notMem hnt (latticeSet_rayBasis 𝔪 c) (rayGen_sub_one_mem 𝔪 c))
    (rayShift_injective (latticeSet_rayBasis 𝔪 c) (rayGen_sub_one_mem 𝔪 c)) hS hcard
  rw [cosetSet_rayBasis, ← hn, hσeq, tsum_mul_left, cone_rayClass_relation hinf hσ c] at hΛ
  exact hΛ

/-! ### The entire coefficient and the continuation -/

variable (𝔪) in
/-- The entire coefficient `N𝔟^s |det| π^{ns/2} ∏_w m_w^{s m_w/2} Γ(s m_w/2)⁻¹ / w`, written
through the coefficient of the trivial ideal class. -/
def rayCoef (c : RayClassGroup 𝔪) (s : ℂ) : ℂ :=
  ((absNorm (rayRep 𝔪 c : Ideal (𝓞 K)) : ℝ) : ℂ) ^ s *
    ((absNorm (classRep K 1 : Ideal (𝓞 K)) : ℝ) : ℂ) ^ (-s) * zetaCoef K 1 s

theorem absNorm_rayRep_pos (c : RayClassGroup 𝔪) :
    (0 : ℝ) < absNorm (rayRep 𝔪 c : Ideal (𝓞 K)) := by
  have h := coe_ne_bot_of_mem 𝔪 (rayRep 𝔪 c)
  exact_mod_cast Nat.pos_of_ne_zero fun h0 => h (absNorm_eq_zero_iff.mp h0)

theorem differentiable_rayCoef (c : RayClassGroup 𝔪) : Differentiable ℂ (rayCoef 𝔪 c) := by
  have hN : ((absNorm (rayRep 𝔪 c : Ideal (𝓞 K)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (absNorm_rayRep_pos c).ne'
  have hN₁ : ((absNorm (classRep K 1 : Ideal (𝓞 K)) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (absNorm_classRep_pos K 1).ne'
  unfold rayCoef
  exact ((differentiable_id.const_cpow (Or.inl hN)).mul
    (differentiable_id.neg.const_cpow (Or.inl hN₁))).mul (differentiable_zetaCoef K 1)

theorem rayCoef_ofReal (c : RayClassGroup 𝔪) {σ : ℝ} (hσ : 0 < σ) :
    rayCoef 𝔪 c σ = (((absNorm (rayRep 𝔪 c : Ideal (𝓞 K)) : ℝ) ^ σ /
      (torsionOrder K * (π ^ (-(finrank ℚ K * σ / 2)) * Real.Gamma (finrank ℚ K * σ / 2) *
        heckeConst K (finrank ℚ K * σ / 2))) : ℝ) : ℂ) := by
  have hN := absNorm_rayRep_pos c
  have hN₁ := absNorm_classRep_pos K 1
  unfold rayCoef
  rw [zetaCoef_ofReal, zetaCoefReal_eq K 1 hσ,
    ← Complex.ofReal_cpow hN.le, show -(σ : ℂ) = ((-σ : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow hN₁.le, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
  congr 1
  have h1 : (absNorm (classRep K 1 : Ideal (𝓞 K)) : ℝ) ^ (-σ) *
      (absNorm (classRep K 1 : Ideal (𝓞 K)) : ℝ) ^ σ = 1 := by
    rw [← Real.rpow_add hN₁, neg_add_cancel, Real.rpow_zero]
  rw [mul_div_assoc', mul_assoc, h1, mul_one]

/-- **Hecke's continuation of the partial zeta function of the ray class `c`.** -/
def rayZetaHecke (hnt : 𝔪.finitePart ≠ ⊤) (c : RayClassGroup 𝔪) (s : ℂ) : ℂ :=
  rayCoef 𝔪 c s * rayΛ hnt c ((finrank ℚ K : ℂ) * s / 2)

theorem differentiableAt_rayZetaHecke (hnt : 𝔪.finitePart ≠ ⊤) (c : RayClassGroup 𝔪) {s : ℂ}
    (hs1 : s ≠ 1) : DifferentiableAt ℂ (rayZetaHecke hnt c) s := by
  have hn : (finrank ℚ K : ℂ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  have h2 : (finrank ℚ K : ℂ) * s / 2 ≠ (((finrank ℚ K : ℝ) / 2 : ℝ) : ℂ) := by
    intro h
    apply hs1
    push_cast at h
    have : (finrank ℚ K : ℂ) * (s - 1) = 0 := by linear_combination 2 * h
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd h' hn
    · exact sub_eq_zero.mp h'
  have hΛ := differentiableAt_rayΛ hnt c h2
  have hlin : DifferentiableAt ℂ (fun s : ℂ => (finrank ℚ K : ℂ) * s / 2) s := by fun_prop
  have hcomp : DifferentiableAt ℂ (rayΛ hnt c ∘ fun s : ℂ => (finrank ℚ K : ℂ) * s / 2) s :=
    DifferentiableAt.comp (g := rayΛ hnt c) s hΛ hlin
  show DifferentiableAt ℂ (fun s => rayCoef 𝔪 c s * rayΛ hnt c ((finrank ℚ K : ℂ) * s / 2)) s
  exact (differentiable_rayCoef c s).mul hcomp

/-- **The continuation is the partial zeta function** at real `σ > 1`. -/
theorem rayZetaHecke_ofReal (hinf : 𝔪.infinitePart = ∅) (hnt : 𝔪.finitePart ≠ ⊤)
    (c : RayClassGroup 𝔪) {σ : ℝ} (hσ : 1 < σ) :
    rayZetaHecke hnt c σ = ((∑' 𝔞 : {𝔞 : integralIdealsPrimeTo 𝔪 // idealClass 𝔪 𝔞 = c},
      (absNorm (𝔞.1 : Ideal (𝓞 K)) : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  have hσ0 : 0 < σ := by linarith
  have harg : (finrank ℚ K : ℂ) * (σ : ℂ) / 2 = ((finrank ℚ K * σ / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  unfold rayZetaHecke
  rw [harg, rayΛ_ofReal hinf hnt c hσ, rayCoef_ofReal c hσ0, ← Complex.ofReal_mul]
  congr 1
  set n : ℝ := (finrank ℚ K : ℝ) with hn
  have hn0 : 0 < n := by
    rw [hn]
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K))
  set s' : ℝ := n * σ / 2 with hs'
  have hs'0 : 0 < s' := by positivity
  have hN := absNorm_rayRep_pos c
  have hw : (0 : ℝ) < torsionOrder K := by exact_mod_cast torsionOrder_pos K
  have hπ : 0 < π ^ (-s') := Real.rpow_pos_of_pos Real.pi_pos _
  have hΓ : 0 < Real.Gamma s' := Real.Gamma_pos_of_pos hs'0
  have hH : 0 < heckeConst K s' := heckeConst_pos hs'0
  have hNσ : (absNorm (rayRep 𝔪 c : Ideal (𝓞 K)) : ℝ) ^ σ *
      (absNorm (rayRep 𝔪 c : Ideal (𝓞 K)) : ℝ) ^ (-σ) = 1 := by
    rw [← Real.rpow_add hN, add_neg_cancel, Real.rpow_zero]
  set A := ∑' 𝔞 : {𝔞 : integralIdealsPrimeTo 𝔪 // idealClass 𝔪 𝔞 = c},
    (absNorm (𝔞.1 : Ideal (𝓞 K)) : ℝ) ^ (-σ) with hA
  field_simp
  linear_combination A * hNσ

/-- **Hecke: the partial zeta function of a ray class continues holomorphically to `ℂ \ {1}`.**
For a modulus with no infinite part and finite part `≠ 𝓞`. -/
theorem exists_rayPartialZeta_continuation (hinf : 𝔪.infinitePart = ∅) (hnt : 𝔪.finitePart ≠ ⊤)
    (c : RayClassGroup 𝔪) :
    ∃ Z : ℂ → ℂ, (∀ s, s ≠ 1 → DifferentiableAt ℂ Z s) ∧
      ∀ σ : ℝ, 1 < σ → Z σ = ((∑' 𝔞 : {𝔞 : integralIdealsPrimeTo 𝔪 // idealClass 𝔪 𝔞 = c},
        (absNorm (𝔞.1 : Ideal (𝓞 K)) : ℝ) ^ (-σ) : ℝ) : ℂ) :=
  ⟨rayZetaHecke hnt c, fun _ hs => differentiableAt_rayZetaHecke hnt c hs,
    fun _ hσ => rayZetaHecke_ofReal hinf hnt c hσ⟩

end SimultaneousPrimitiveRoots.Hecke

end
