/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
/- Backport of the special-linear/determinant-kernel equivalence for Mathlib v4.33.1. -/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

namespace Matrix.SpecialLinearGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- The special linear group is isomorphic to the determinant kernel in the general linear group. -/
@[simps]
def toGLKerEquiv : SpecialLinearGroup n R ≃*
    (GeneralLinearGroup.det : GeneralLinearGroup n R →* Rˣ).ker where
  toFun g := ⟨toGL g, coeToGL_det g⟩
  invFun A := ⟨A.val.val, by simpa using congrArg Units.val A.2⟩
  left_inv _ := rfl
  right_inv _ := by ext; rfl
  map_mul' _ _ := by ext; rfl

end Matrix.SpecialLinearGroup
