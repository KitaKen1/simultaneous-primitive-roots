import ClassFieldTheory.AlgebraicNumberTheory.SUnit.LogLattice
import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormOneCompact
import SimultaneousPrimitiveRoots.NumberFieldFiniteCompletionCompact

/-!
# Compact representatives modulo sixth powers of actual S-units

All infinite completions and the finite completions in S are retained.
The full S-unit logarithmic lattice gives a compact logarithmic parallelepiped
modulo six times the lattice. Local norm annuli are compact, so this lifts to
a fixed compact set of norm-one local tuples. The adjusting elements are
sixth powers of actual S-units, rather than arbitrary local powers.
-/

noncomputable section
open Module NumberField IsDedekindDomain
open scoped NumberField BigOperators

namespace SimultaneousPrimitiveRoots.Unconditional.CFTBridge

variable (F : Type) [Field F] [NumberField F]
variable (S : Finset (HeightOneSpectrum (𝓞 F)))

/-- The local multiplicative group at all infinite places and the finite places in S. -/
abbrev SLocalUnits := (∀ w : InfinitePlace F, w.Completionˣ) ×
  (∀ v : S, (v.1.adicCompletion F)ˣ)

/-- The diagonal map of field units into the actual local groups. -/
def fieldToSLocal : Fˣ →* SLocalUnits F S :=
  (MonoidHom.pi fun w => (IdeleGroup.infiniteComponent w).comp
    (IdeleGroup.principalIdele F)).prod
  (MonoidHom.pi fun v : S => (IdeleGroup.finiteComponent v.1).comp
    (IdeleGroup.principalIdele F))

/-- The same global S-unit is used at every coordinate. -/
def sUnitToSLocal : SUnitGroup (K := F) S →* SLocalUnits F S :=
  (fieldToSLocal F S).comp (SUnitGroup (K := F) S).subtype

/-- The normalized log absolute values, with multiplicity two at complex places. -/
def sLocalLog (x : SLocalUnits F S) : SUnitGroup.FullLogSpace (K := F) S :=
  Sum.elim (fun w => w.mult * Real.log ‖(x.1 w : w.Completion)‖)
    (fun v : S => Real.log ‖(x.2 v : v.1.adicCompletion F)‖)

/-- The actual normalized product of all local absolute values. -/
def sLocalNorm (x : SLocalUnits F S) : ℝ :=
  (∏ w : InfinitePlace F, ‖(x.1 w : w.Completion)‖ ^ w.mult) *
    ∏ v : S, ‖(x.2 v : v.1.adicCompletion F)‖

theorem sLocalNorm_pos (x : SLocalUnits F S) : 0 < sLocalNorm F S x := by
  apply mul_pos
  · exact Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.mpr (x.1 w).ne_zero) _
  · exact Finset.prod_pos fun v _ => norm_pos_iff.mpr (x.2 v).ne_zero

theorem log_sLocalNorm (x : SLocalUnits F S) :
    Real.log (sLocalNorm F S x) = ∑ p, sLocalLog F S x p := by
  have hi : ∀ w : InfinitePlace F, ‖(x.1 w : w.Completion)‖ ^ w.mult ≠ 0 :=
    fun w => pow_ne_zero _ (norm_ne_zero_iff.mpr (x.1 w).ne_zero)
  have hf : ∀ v : S, ‖(x.2 v : v.1.adicCompletion F)‖ ≠ 0 :=
    fun v => norm_ne_zero_iff.mpr (x.2 v).ne_zero
  rw [sLocalNorm, Real.log_mul
    (Finset.prod_ne_zero_iff.mpr (fun w _ => hi w))
    (Finset.prod_ne_zero_iff.mpr (fun v _ => hf v)),
    Real.log_prod (fun w _ => hi w), Real.log_prod (fun v _ => hf v)]
  simp only [Real.log_pow, Fintype.sum_sum_type, sLocalLog, Sum.elim_inl, Sum.elim_inr]

theorem sLocalNorm_eq_one_iff (x : SLocalUnits F S) :
    sLocalNorm F S x = 1 ↔ (∑ p, sLocalLog F S x p) = 0 := by
  rw [← log_sLocalNorm]
  constructor
  · intro h
    rw [h, Real.log_one]
  · intro h
    exact Real.log_injOn_pos (Set.mem_Ioi.mpr (sLocalNorm_pos F S x))
      (Set.mem_Ioi.mpr zero_lt_one)
      (h.trans Real.log_one.symm)

theorem sLocalLog_mul (x y : SLocalUnits F S) :
    sLocalLog F S (x * y) = sLocalLog F S x + sLocalLog F S y := by
  ext p
  cases p with
  | inl w => simp [sLocalLog, norm_mul, Real.log_mul, mul_add]
  | inr v => simp [sLocalLog, norm_mul, Real.log_mul]

theorem sLocalLog_pow (x : SLocalUnits F S) (n : ℕ) :
    sLocalLog F S (x ^ n) = n • sLocalLog F S x := by
  induction n with
  | zero => ext p; cases p <;> simp [sLocalLog]
  | succ n ih => rw [pow_succ, sLocalLog_mul, ih, succ_nsmul]

theorem sLocalLog_sUnit (u : SUnitGroup (K := F) S) :
    sLocalLog F S (sUnitToSLocal F S u) =
      SUnitGroup.fullLogAmbient (K := F) S (Additive.ofMul u) := by
  ext p
  cases p with
  | inl w =>
    change w.mult * Real.log ‖(IdeleGroup.infiniteComponent w
      (IdeleGroup.principalIdele F (u : Fˣ)) : w.Completion)‖ = _
    change w.mult * Real.log ‖(InfiniteIdeleGroup.component w
      (IdeleGroup.principalIdele F (u : Fˣ)).1 : w.Completion)‖ = _
    rw [InfiniteIdeleGroup.norm_infiniteComponent_principalIdele]
    rfl
  | inr v =>
    change Real.log ‖(IdeleGroup.finiteComponent v.1
      (IdeleGroup.principalIdele F (u : Fˣ)) : v.1.adicCompletion F)‖ = _
    change Real.log ‖FinitePlace.embedding v.1 ((u : Fˣ) : F)‖ = _
    rw [FinitePlace.norm_embedding]
    rfl

/-- A fixed compact logarithmic set meets every sixth-power S-unit orbit. -/
theorem exists_compact_sixth_log_representatives :
    ∃ C : Set (SUnitGroup.LogHyperplane (K := F) S), IsCompact C ∧
      ∀ x : SUnitGroup.LogHyperplane (K := F) S,
        ∃ u : SUnitGroup (K := F) S,
          x + 6 • SUnitGroup.fullLog (K := F) S (Additive.ofMul u) ∈ C := by
  classical
  let L := SUnitGroup.fullLogLattice (K := F) S
  have : Module.Free ℤ L := ZLattice.module_free ℝ L
  let b := (Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ
  refine ⟨(fun y => (6 : ℝ) • y) '' b.parallelepiped,
    b.parallelepiped.isCompact.image (continuous_id.const_smul (6 : ℝ)), ?_⟩
  intro x
  obtain ⟨v, hv, _⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b ((6 : ℝ)⁻¹ • x)
  have hvL : (v : SUnitGroup.LogHyperplane (K := F) S) ∈ L := by
    simpa only [b, Module.Basis.ofZLatticeBasis_span] using v.property
  have hvR : (v : SUnitGroup.LogHyperplane (K := F) S) ∈
      LinearMap.range (SUnitGroup.fullLog (K := F) S).toIntLinearMap :=
    (SUnitGroup.fullLogLattice_eq_range (K := F) S).le hvL
  obtain ⟨u, hu⟩ := hvR
  refine ⟨u.toMul, (6 : ℝ)⁻¹ • x + v,
    ?_, ?_⟩
  · exact ZSpan.fundamentalDomain_subset_parallelepiped b
      (by simpa only [Submodule.vadd_def, vadd_eq_add, add_comm] using hv)
  ·
    change (6 : ℝ) • ((6 : ℝ)⁻¹ • x + v) = x + 6 • SUnitGroup.fullLog (K := F) S u
    rw [smul_add, smul_smul, mul_inv_cancel₀ (by norm_num : (6 : ℝ) ≠ 0), one_smul]
    rw [← hu]
    norm_cast

/-- The compact annulus in a finite completion, including its inverse bound. -/
def finiteLocalAnnulus (v : HeightOneSpectrum (𝓞 F)) (B : ℝ) :
    Set (v.adicCompletion F)ˣ :=
  {x | Real.exp (-B) ≤ ‖(x : v.adicCompletion F)‖ ∧
    ‖(x : v.adicCompletion F)‖ ≤ Real.exp B}

theorem isCompact_finiteLocalAnnulus (v : HeightOneSpectrum (𝓞 F)) (B : ℝ) :
    IsCompact (finiteLocalAnnulus F v B) := by
  let A : Set (v.adicCompletion F) :=
    {x | Real.exp (-B) ≤ ‖x‖ ∧ ‖x‖ ≤ Real.exp B}
  have hclosed : IsClosed A := isClosed_Icc.preimage continuous_norm
  have hbounded : Bornology.IsBounded A := by
    rw [isBounded_iff_forall_norm_le]
    exact ⟨Real.exp B, fun x hx => hx.2⟩
  have hcompact : IsCompact A := Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hbounded⟩
  have hrange : A ⊆ Set.range (Units.val : (v.adicCompletion F)ˣ → v.adicCompletion F) := by
    intro x hx
    have hx0 : x ≠ 0 := by
      intro h
      have hnonpos : Real.exp (-B) ≤ 0 := by simpa [h] using hx.1
      exact (not_lt_of_ge hnonpos) (Real.exp_pos (-B))
    exact ⟨Units.mk0 x hx0, rfl⟩
  exact (Units.isEmbedding_val₀.isInducing.isCompact_preimage_iff hrange).mpr hcompact

/-- A product of local annuli retains every phase and every finite local coordinate. -/
def sLocalAnnulus (B : ℝ) : Set (SLocalUnits F S) :=
  (Set.univ.pi fun w : InfinitePlace F => InfiniteIdeleGroup.localAnnulus w B) ×ˢ
    (Set.univ.pi fun v : S => finiteLocalAnnulus F v.1 B)

theorem isCompact_sLocalAnnulus (B : ℝ) : IsCompact (sLocalAnnulus F S B) :=
  (isCompact_univ_pi fun w => InfiniteIdeleGroup.isCompact_localAnnulus w B).prod
    (isCompact_univ_pi fun v : S => isCompact_finiteLocalAnnulus F v.1 B)

theorem continuous_sLocalLog : Continuous (sLocalLog F S) := by
  apply continuous_pi
  intro p
  cases p with
  | inl w =>
    exact continuous_const.mul
      ((continuous_norm.comp (Units.continuous_val.comp
        ((continuous_apply w).comp continuous_fst))).log
        (fun x => norm_ne_zero_iff.mpr (x.1 w).ne_zero))
  | inr v =>
    exact (continuous_norm.comp (Units.continuous_val.comp
      ((continuous_apply v).comp continuous_snd))).log
        (fun x => norm_ne_zero_iff.mpr (x.2 v).ne_zero)

private theorem annulus_of_abs_log_le {K : Type*} [NormedField K]
    (x : Kˣ) (B : ℝ) (hx : |Real.log ‖(x : K)‖| ≤ B) :
    Real.exp (-B) ≤ ‖(x : K)‖ ∧ ‖(x : K)‖ ≤ Real.exp B := by
  have hp : 0 < ‖(x : K)‖ := norm_pos_iff.mpr x.ne_zero
  obtain ⟨hlo, hhi⟩ := abs_le.mp hx
  constructor
  · exact (Real.exp_le_exp.mpr hlo).trans_eq (Real.exp_log hp)
  · exact (Real.exp_log hp).symm.trans_le (Real.exp_le_exp.mpr hhi)

/-- **A compact set of actual norm-one local tuples meets every sixth-power S-unit orbit.** -/
theorem exists_compact_sixth_sUnit_representatives :
    ∃ K : Set (SLocalUnits F S), IsCompact K ∧
      (∀ y ∈ K, ∑ p, sLocalLog F S y p = 0) ∧
      ∀ x : SLocalUnits F S, (∑ p, sLocalLog F S x p) = 0 →
        ∃ u : SUnitGroup (K := F) S, x * sUnitToSLocal F S u ^ 6 ∈ K := by
  classical
  obtain ⟨C, hC, hcover⟩ := exists_compact_sixth_log_representatives F S
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn continuous_id.continuousOn
  let B := max M 0
  have hclosed : IsClosed {x : SLocalUnits F S | ∑ p, sLocalLog F S x p = 0} := by
    exact isClosed_eq (continuous_finsetSum _ (fun p _ =>
      (continuous_apply p).comp (continuous_sLocalLog F S))) continuous_const
  refine ⟨sLocalAnnulus F S B ∩ {x | ∑ p, sLocalLog F S x p = 0},
    (isCompact_sLocalAnnulus F S B).inter_right hclosed, fun y hy => hy.2, ?_⟩
  intro x hx
  let z : SUnitGroup.LogHyperplane (K := F) S := ⟨sLocalLog F S x, hx⟩
  obtain ⟨u, hu⟩ := hcover z
  let y := x * sUnitToSLocal F S u ^ 6
  let t := z + 6 • SUnitGroup.fullLog (K := F) S (Additive.ofMul u)
  have ht : sLocalLog F S y = (t : SUnitGroup.FullLogSpace (K := F) S) := by
    rw [sLocalLog_mul, sLocalLog_pow, sLocalLog_sUnit]
    rfl
  have hnorm : ‖t‖ ≤ B := (hM t hu).trans (le_max_left _ _)
  have hcoord : ∀ p, |sLocalLog F S y p| ≤ B := by
    intro p
    rw [ht, ← Real.norm_eq_abs]
    exact (norm_le_pi_norm (t : SUnitGroup.FullLogSpace (K := F) S) p).trans
      ((Submodule.norm_coe t).le.trans hnorm)
  refine ⟨u, ?_, ?_⟩
  · constructor
    · intro w _
      apply annulus_of_abs_log_le
      have h := hcoord (Sum.inl w)
      change |(w.mult : ℝ) * Real.log ‖(y.1 w : w.Completion)‖| ≤ B at h
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg _)] at h
      have hm : (1 : ℝ) ≤ w.mult := InfinitePlace.one_le_mult
      nlinarith [abs_nonneg (Real.log ‖(y.1 w : w.Completion)‖)]
    · intro v _
      exact annulus_of_abs_log_le (y.2 v) B (hcoord (Sum.inr v))
  · change (∑ p, sLocalLog F S y p) = 0
    rw [ht]
    exact t.property

end SimultaneousPrimitiveRoots.Unconditional.CFTBridge
