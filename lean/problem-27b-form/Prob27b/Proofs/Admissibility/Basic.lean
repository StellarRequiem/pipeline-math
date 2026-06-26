/-
Copyright (c) 2026 Prob27b formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob27b formalization
-/
import Prob27b.Defs

/-!
# Stage Adm — Admissibility: `D = 𝔽₂[π]` has finite residue rings

This file proves `D_finite_residue_rings_proof`: for every nonzero
`g : (ZMod 2)[X]`, the quotient `(ZMod 2)[X] ⧸ span {g}` is finite.

Mathematics: `ZMod 2` is a finite field; for `g ≠ 0` the quotient is the
`natDegree g`-dimensional `ZMod 2`-vector space `AdjoinRoot g`
(`AdjoinRoot.powerBasis`), which over a finite field is finite
(`Module.finite_of_finite`). `AdjoinRoot g` is *definitionally*
`(ZMod 2)[X] ⧸ span {g}`, so the result transfers verbatim.
-/

namespace Prob27b

open Polynomial

theorem D_finite_residue_rings_proof :
    ∀ g : Polynomial (ZMod 2), g ≠ 0 → Finite (Polynomial (ZMod 2) ⧸ Ideal.span {g}) := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  intro g hg
  -- `AdjoinRoot g` is by definition `(ZMod 2)[X] ⧸ span {g}`.
  -- It is a finite-dimensional `ZMod 2`-vector space via its power basis.
  haveI : Module.Finite (ZMod 2) (AdjoinRoot g) :=
    .of_basis (AdjoinRoot.powerBasis hg).basis
  -- A finite-dimensional vector space over a finite field is finite.
  haveI : Finite (AdjoinRoot g) := Module.finite_of_finite (ZMod 2)
  -- `AdjoinRoot g` and the stated quotient are definitionally equal.
  exact this

end Prob27b
