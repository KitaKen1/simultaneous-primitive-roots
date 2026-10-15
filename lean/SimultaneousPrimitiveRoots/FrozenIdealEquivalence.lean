module

public import SimultaneousPrimitiveRoots.NumberFieldFrozenMajorant
public import Mathlib.RingTheory.DedekindDomain.Factorization

@[expose] public section
set_option backward.isDefEq.respectTransparency false

namespace SimultaneousPrimitiveRoots

open NumberField IsDedekindDomain
noncomputable section

/-- The intrinsic ideal carrier: nonzero ideals with all prime divisors
in the specified finite set. It is not defined as the range of a vector map. -/
def FrozenIdealCarrier (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) : Type _ :=
  {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ I → v ∈ s}

theorem frozenIdeal_prime_dvd_mem (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (e : s → ℕ)
    (v : HeightOneSpectrum (𝓞 K)) (hv : v.asIdeal ∣ numberFieldFrozenIdeal K s e) :
    v ∈ s := by
  classical
  obtain ⟨w, _, hw⟩ := Prime.exists_mem_finset_dvd v.prime hv
  have h := v.prime.dvd_of_dvd_pow hw
  have heq : v = w.val := HeightOneSpectrum.ext
    (associated_iff_eq.mp ((Prime.dvd_prime_iff_associated v.prime w.val.prime).mp h))
  exact heq ▸ w.property

theorem frozenIdeal_emultiplicity (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (e : s → ℕ) (v : s) :
    emultiplicity v.val.asIdeal (numberFieldFrozenIdeal K s e) = (e v : ℕ∞) := by
  classical
  rw [numberFieldFrozenIdeal, Finset.emultiplicity_prod v.val.prime]
  have hp (w : s) : emultiplicity v.val.asIdeal (w.val.asIdeal ^ e w) =
      if w = v then (e v : ℕ∞) else 0 := by
    by_cases hw : w = v
    · subst w
      rw [if_pos rfl]
      exact emultiplicity_pow_self_of_prime v.val.prime _
    · rw [if_neg hw, emultiplicity_pow v.val.prime]
      have hn : ¬v.val.asIdeal ∣ w.val.asIdeal := by
        intro h
        apply hw
        apply Subtype.ext
        exact (HeightOneSpectrum.ext (associated_iff_eq.mp
          ((Prime.dvd_prime_iff_associated v.val.prime w.val.prime).mp h))).symm
      rw [emultiplicity_eq_zero.mpr hn, mul_zero]
  simp only [hp, Finset.sum_ite_eq', Finset.mem_univ, if_pos]

theorem frozenIdeal_multiplicity (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (e : s → ℕ) (v : s) :
    multiplicity v.val.asIdeal (numberFieldFrozenIdeal K s e) = e v := by
  exact multiplicity_eq_of_emultiplicity_eq_some (frozenIdeal_emultiplicity K s e v)

theorem frozenIdeal_vector_injective (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective (numberFieldFrozenIdeal K s) := by
  intro e f h
  funext v
  simpa only [frozenIdeal_multiplicity] using
    congrArg (multiplicity v.val.asIdeal) h

/-- Recover an ideal from its actual multiplicities on the allowed primes. -/
theorem frozenIdeal_reconstruct (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (I : FrozenIdealCarrier K s) :
    numberFieldFrozenIdeal K s (fun v => multiplicity v.val.asIdeal I.val) = I.val := by
  classical
  have hout (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ s) :
      multiplicity v.asIdeal I.val = 0 :=
    multiplicity_eq_zero.mpr fun hd => hv (I.property.2 v hd)
  have hs : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 K) =>
      v.asIdeal ^ multiplicity v.asIdeal I.val) ⊆ s := by
    intro v hv
    by_contra hn
    apply hv
    change v.asIdeal ^ multiplicity v.asIdeal I.val = 1
    rw [hout v hn, pow_zero]
  have hf := finprod_eq_finsetProd_of_mulSupport_subset
    (fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal ^ multiplicity v.asIdeal I.val) hs
  have ha : (∏ v : s, v.val.asIdeal ^ multiplicity v.val.asIdeal I.val) =
      ∏ v ∈ s, v.asIdeal ^ multiplicity v.asIdeal I.val := by
    simpa only [Finset.attach_eq_univ] using
      Finset.prod_attach s (fun v => v.asIdeal ^ multiplicity v.asIdeal I.val)
  rw [numberFieldFrozenIdeal, ha, ← hf]
  exact Ideal.finprod_heightOneSpectrum_pow_multiplicity I.property.1

/-- Exact bijection from all frozen exponent vectors to the intrinsic
supported ideal carrier, using multiplicities as the inverse. -/
def frozenIdealEquiv (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) : (s → ℕ) ≃ FrozenIdealCarrier K s where
  toFun e := ⟨numberFieldFrozenIdeal K s e, numberFieldFrozenIdeal_ne_bot K s e,
    frozenIdeal_prime_dvd_mem K s e⟩
  invFun I v := multiplicity v.val.asIdeal I.val
  left_inv e := funext (frozenIdeal_multiplicity K s e)
  right_inv I := Subtype.ext (frozenIdeal_reconstruct K s I)

theorem frozenIdealEquiv_apply_val (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (e : s → ℕ) :
    (frozenIdealEquiv K s e).val = numberFieldFrozenIdeal K s e := rfl

theorem frozenIdealEquiv_symm_apply (K : Type*) [Field K] [NumberField K]
    (s : Finset (HeightOneSpectrum (𝓞 K))) (I : FrozenIdealCarrier K s) (v : s) :
    (frozenIdealEquiv K s).symm I v = multiplicity v.val.asIdeal I.val := rfl

end
end SimultaneousPrimitiveRoots
