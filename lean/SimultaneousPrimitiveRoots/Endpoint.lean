module

public import Mathlib.Algebra.Group.Units.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

@[expose] public section

/-! The joint endpoint relation used in the fixed-progression bridge. -/

namespace SimultaneousPrimitiveRoots

section Ring

variable {R : Type*} [CommRing R]

def JointEndpoint (b s t : R) : Prop :=
  IsUnit t ∧ b * s = (b - 1) * t

theorem jointEndpoint_unit_shift {b u : R} (hb : IsUnit b) :
    JointEndpoint b u (u + 1) ↔ u + 1 = b := by
  constructor
  · rintro ⟨_, h⟩
    linear_combination h
  · intro h
    constructor
    · simpa [h] using hb
    · linear_combination h

theorem jointEndpoint_common_unit {b s t r : R} (hr : IsUnit r) :
    JointEndpoint b (r * s) (r * t) ↔ JointEndpoint b s t := by
  rcases hr with ⟨v, rfl⟩
  constructor
  · rintro ⟨ht, h⟩
    refine ⟨?_, ?_⟩
    · simpa [mul_assoc] using (v⁻¹).isUnit.mul ht
    · have he := congrArg (fun z : R => (↑(v⁻¹) : R) * z) h
      simpa [mul_left_comm, mul_assoc, mul_comm] using he
  · rintro ⟨ht, h⟩
    refine ⟨v.isUnit.mul ht, ?_⟩
    linear_combination (v : R) * h

theorem jointEndpoint_shift {b w d : R} (hb : IsUnit b) (hd : IsUnit d) :
    JointEndpoint b w (w + d) ↔ w = (b - 1) * d := by
  constructor
  · rintro ⟨_, h⟩
    linear_combination h
  · intro h
    constructor
    · have hw : w + d = b * d := by linear_combination h
      rw [hw]
      exact hb.mul hd
    · linear_combination h

end Ring

end SimultaneousPrimitiveRoots
