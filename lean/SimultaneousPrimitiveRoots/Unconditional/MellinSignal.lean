module

public import SimultaneousPrimitiveRoots.Unconditional.HeckeStatement
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Analytic.Uniqueness

/-!
# The last step of [A] Theorem 1.2: a Mellin signal excludes zeros (top of step Z6)

[A] (`A-02a:0140–0179`, §6) proves Theorem 1.2 for fixed `F` and `η` by constructing a function
`f_η` on `(0, ∞)` whose Mellin transform is `e^{(s - 5/6)²} H_η(s) / L^S(s, η)` on `Re s > 1`, with
`H_η` holomorphic and nowhere zero near `Re s ≥ .998`, and by proving
`f_η(Z) ≪ Z^{7/15 - 1/20000}` as `Z → ∞` and rapid decay as `Z → 0`. The Mellin transform then
converges on `Re s > 1 - 1/20000`, and the identity `L^S(s, η) · ∫ f_η Z^{-s+8/15} dZ/Z =
e^{(s-5/6)²} H_η(s)` continues there, so `L^S(s, η)` has no zeros.

`HasMellinSignal χ κ` states the existence of such a signal for a ray class character `χ`, with
`c = -8/15` and width `κ` in place of `1/20000`; `rayClassLZeroFree_of_hasMellinSignal` is the
conclusion, and `heckeZeroFreeStrip_of_heckeMellinSignal` gives `HeckeZeroFreeStrip κ` from
signals for all ray class characters of the cyclotomic fields `F ⊇ μ₁₂`.

A signal for `L^S(s, η)` ([A]'s incomplete `L`-function, `S` containing the primes of `𝔪`) gives
one for the ray class `L`-series: `L^S = L(s, χ) · E(s)` with `E` a finite product of factors
`1 - χ(𝔭) N𝔭^{-s}`, which do not vanish on `Re s > 0`; replace `H` by `H / E`.

The design follows `OAI.NumberTheory.DirichletL.Continuation` of openai/math (Apache-2.0), which
proves the same step for `ℚ` and `ℚ(√-3)` with width `1/8`.
-/

@[expose] public section

namespace SimultaneousPrimitiveRoots.Unconditional

open Filter Asymptotics MeasureTheory TauCeti TauCeti.GlobalNumberFields NumberField
open scoped Topology

noncomputable section

/-! ### Mellin signals -/

/-- The Mellin transform of a signal `f`, shifted by `c`: `∫₀^∞ f(Z) Z^{-s-c} dZ/Z`. -/
def signalMellin (f : ℝ → ℂ) (c : ℝ) (s : ℂ) : ℂ :=
  mellin f (-(s + (c : ℂ)))

/-- `f` decays faster than every power of `Z` as `Z → 0⁺`. -/
def RapidDecayAtZero (f : ℝ → ℂ) : Prop :=
  ∀ B : ℝ, f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ B)

/-- **The Mellin transform of a signal of growth `Z^{a + c}` is holomorphic on `Re s > a`.** -/
theorem signalMellin_analytic (f : ℝ → ℂ) (a c : ℝ)
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (htop : f =O[atTop] (fun x : ℝ => x ^ (a + c)))
    (hzero : RapidDecayAtZero f) :
    AnalyticOnNhd ℂ (signalMellin f c) {s : ℂ | a < s.re} := by
  apply (Complex.analyticOnNhd_iff_differentiableOn (Complex.isOpen_re_gt a)).2
  intro s hs
  have hd : DifferentiableAt ℂ (mellin f) (-(s + (c : ℂ))) := by
    apply mellin_differentiableAt_of_isBigO_rpow (a := -(a + c))
      (b := (-(s + (c : ℂ))).re - 1) hlocal
    · simpa only [neg_neg] using htop
    · simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]
      change a < s.re at hs
      linarith
    · exact hzero _
    · linarith
  exact (hd.comp s ((differentiableAt_id.add_const (c : ℂ)).neg)).differentiableWithinAt

/-- A half-plane `Re s > a` with `a < 1`, punctured at `1`, is preconnected. -/
theorem isPreconnected_halfPlane_diff_one {a : ℝ} (ha : a < 1) :
    IsPreconnected ({s : ℂ | a < s.re} \ {1}) := by
  let Up : Set ℂ := {s | a < s.re} ∩ {s | 0 < s.im}
  let Um : Set ℂ := {s | a < s.re} ∩ {s | s.im < 0}
  let V : Set ℂ := {s | 1 < s.re}
  let W : Set ℂ := {s | a < s.re} ∩ {s | s.re < 1}
  have hUp : IsPreconnected Up :=
    (convex_halfSpace_re_gt a).inter (convex_halfSpace_im_gt 0) |>.isPreconnected
  have hUm : IsPreconnected Um :=
    (convex_halfSpace_re_gt a).inter (convex_halfSpace_im_lt 0) |>.isPreconnected
  have hV : IsPreconnected V := (convex_halfSpace_re_gt 1).isPreconnected
  have hW : IsPreconnected W :=
    (convex_halfSpace_re_gt a).inter (convex_halfSpace_re_lt 1) |>.isPreconnected
  have heq : {s : ℂ | a < s.re} \ {1} = ((V ∪ Up) ∪ Um) ∪ W := by
    ext s
    simp only [Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_inter_iff, V, Up, Um, W]
    constructor
    · rintro ⟨hs, hs1⟩
      rcases lt_trichotomy s.im 0 with him | him | him
      · exact Or.inl (Or.inr ⟨hs, him⟩)
      · rcases lt_trichotomy s.re 1 with hre | hre | hre
        · exact Or.inr ⟨hs, hre⟩
        · exact absurd (Complex.ext (by simpa using hre) (by simpa using him)) hs1
        · exact Or.inl (Or.inl (Or.inl hre))
      · exact Or.inl (Or.inl (Or.inr ⟨hs, him⟩))
    · rintro (((h | ⟨h, him⟩) | ⟨h, him⟩) | ⟨h, hre⟩)
      · exact ⟨by linarith, fun h1 => by rw [h1, Complex.one_re] at h; exact lt_irrefl _ h⟩
      · exact ⟨h, fun h1 => by rw [h1, Complex.one_im] at him; exact lt_irrefl _ him⟩
      · exact ⟨h, fun h1 => by rw [h1, Complex.one_im] at him; exact lt_irrefl _ him⟩
      · exact ⟨h, fun h1 => by rw [h1, Complex.one_re] at hre; exact lt_irrefl _ hre⟩
  rw [heq]
  have h1 : (2 + Complex.I : ℂ) ∈ V ∧ (2 + Complex.I : ℂ) ∈ Up := by
    refine ⟨?_, ?_, ?_⟩
    · show (1 : ℝ) < (2 + Complex.I).re
      norm_num
    · show a < (2 + Complex.I).re
      norm_num
      linarith
    · show (0 : ℝ) < (2 + Complex.I).im
      norm_num
  have h2 : (2 - Complex.I : ℂ) ∈ V ∪ Up ∧ (2 - Complex.I : ℂ) ∈ Um := by
    refine ⟨Or.inl ?_, ?_, ?_⟩
    · show (1 : ℝ) < (2 - Complex.I).re
      norm_num
    · show a < (2 - Complex.I).re
      norm_num
      linarith
    · show (2 - Complex.I).im < 0
      norm_num
  have h3 : (((a + 1) / 2 : ℝ) + Complex.I : ℂ) ∈ (V ∪ Up) ∪ Um ∧
      (((a + 1) / 2 : ℝ) + Complex.I : ℂ) ∈ W := by
    refine ⟨Or.inl (Or.inr ⟨?_, ?_⟩), ?_, ?_⟩
    · show a < (((a + 1) / 2 : ℝ) + Complex.I : ℂ).re
      simp only [Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero]
      linarith
    · show (0 : ℝ) < (((a + 1) / 2 : ℝ) + Complex.I : ℂ).im
      simp only [Complex.add_im, Complex.ofReal_im, Complex.I_im, zero_add]
      norm_num
    · show a < (((a + 1) / 2 : ℝ) + Complex.I : ℂ).re
      simp only [Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero]
      linarith
    · show (((a + 1) / 2 : ℝ) + Complex.I : ℂ).re < 1
      simp only [Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero]
      linarith
  exact ((hV.union _ h1.1 h1.2 hUp).union _ h2.1 h2.2 hUm).union _ h3.1 h3.2 hW

/-! ### Ray class characters -/

variable {K : Type*} [Field K] [NumberField K]

/-- **A Mellin signal of width `κ` for a ray class character** (the output of [A] §§2–6 for one
character): a signal `f` on `(0, ∞)`, locally integrable, rapidly decaying at `0` and of growth
`Z^{1 - κ - 8/15}` at `∞`, and a multiplier `H` holomorphic and nowhere zero on `Re s > 1 - κ`, with
`L(s, χ) · ∫₀^∞ f(Z) Z^{-s+8/15} dZ/Z = e^{(s-5/6)²} H(s)` on `Re s > 1`. -/
def HasMellinSignal {𝔪 : Modulus K} (χ : RayClassCharacter 𝔪) (κ : ℝ) : Prop :=
  ∃ (H : ℂ → ℂ) (f : ℝ → ℂ),
    AnalyticOnNhd ℂ H {s : ℂ | 1 - κ < s.re} ∧ (∀ s : ℂ, 1 - κ < s.re → H s ≠ 0) ∧
    LocallyIntegrableOn f (Set.Ioi 0) ∧ RapidDecayAtZero f ∧
    f =O[atTop] (fun x : ℝ => x ^ (1 - κ + (-8 / 15 : ℝ))) ∧
    ∀ s : ℂ, 1 < s.re →
      rayClassLSeries χ s * signalMellin f (-8 / 15) s = Complex.exp ((s - 5 / 6) ^ 2) * H s

/-- **A Mellin signal excludes zeros**: if `χ` has a Mellin signal of width `0 < κ`, every
holomorphic continuation of `L(s, χ)` to `{Re s > 1 - κ} \ {1}` is nowhere zero there. -/
theorem rayClassLZeroFree_of_hasMellinSignal {𝔪 : Modulus K} {χ : RayClassCharacter 𝔪}
    {κ : ℝ} (hκ : 0 < κ) (h : HasMellinSignal χ κ) : RayClassLZeroFree χ κ := by
  obtain ⟨H, f, hH, hH0, hloc, hzero, htop, hid⟩ := h
  intro g hg hgL ρ hρ hρ1
  set U : Set ℂ := {s : ℂ | 1 - κ < s.re} \ {1} with hUdef
  have hUset : {s : ℂ | 1 - κ < s.re ∧ s ≠ 1} = U := by
    ext s
    simp [hUdef]
  have hUopen : IsOpen U := (Complex.isOpen_re_gt _).sdiff isClosed_singleton
  have hM : AnalyticOnNhd ℂ (signalMellin f (-8 / 15)) {s : ℂ | 1 - κ < s.re} :=
    signalMellin_analytic f (1 - κ) (-8 / 15) hloc htop hzero
  have hgA : AnalyticOnNhd ℂ g U := (hUset ▸ hg).analyticOnNhd hUopen
  have hW : AnalyticOnNhd ℂ (fun s => Complex.exp ((s - 5 / 6) ^ 2) * H s)
      {s : ℂ | 1 - κ < s.re} :=
    (((analyticOnNhd_id.sub analyticOnNhd_const).pow 2).cexp).mul hH
  have h2 : (2 : ℂ) ∈ U := by
    refine ⟨?_, ?_⟩
    · show 1 - κ < (2 : ℂ).re
      simp only [Complex.re_ofNat]
      linarith
    · simp only [Set.mem_singleton_iff]
      norm_num
  have hev : (fun s => g s * signalMellin f (-8 / 15) s) =ᶠ[𝓝 (2 : ℂ)]
      (fun s => Complex.exp ((s - 5 / 6) ^ 2) * H s) := by
    filter_upwards [(Complex.isOpen_re_gt 1).mem_nhds (show (1 : ℝ) < (2 : ℂ).re by simp)]
      with s hs
    rw [hgL s hs]
    exact hid s hs
  have heqOn := (hgA.mul (hM.mono Set.sdiff_subset)).eqOn_of_preconnected_of_eventuallyEq
    (hW.mono Set.sdiff_subset) (isPreconnected_halfPlane_diff_one (by linarith)) h2 hev
  intro hgρ
  have hρU : ρ ∈ U := ⟨hρ, hρ1⟩
  have := heqOn hρU
  simp only [hgρ, zero_mul] at this
  exact mul_ne_zero (Complex.exp_ne_zero _) (hH0 ρ hρ) this.symm

/-- **[A] §§2–6 in Mellin-signal form**: every ray class character of every cyclotomic field
`F ⊇ μ₁₂` has a Mellin signal of width `κ`. -/
def HeckeMellinSignal (κ : ℝ) : Prop :=
  ∀ (m : ℕ) [NeZero m], 12 ∣ m →
    ∀ (F : Type) [Field F] [NumberField F] [IsCyclotomicExtension {m} ℚ F],
      ∀ (𝔪 : Modulus F) (χ : RayClassCharacter 𝔪), HasMellinSignal χ κ

/-- **Mellin signals give the Hecke zero-free strip.** -/
theorem heckeZeroFreeStrip_of_heckeMellinSignal {κ : ℝ} (hκ : 0 < κ)
    (h : HeckeMellinSignal κ) : HeckeZeroFreeStrip κ :=
  fun m _ h12 F _ _ _ 𝔪 χ => rayClassLZeroFree_of_hasMellinSignal hκ (h m h12 F 𝔪 χ)

end

end SimultaneousPrimitiveRoots.Unconditional
