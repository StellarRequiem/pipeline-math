/-
Copyright (c) 2026 Prob27b formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob27b formalization
-/
import Prob27b.Theorems
import Prob27b.Proofs.Capstone.Basic
import Prob27b.Proofs.Admissibility.Basic
import Prob27b.Proofs.KInterA.Basic

/-!
# Discharge: each frozen theorem is proven by its `Proofs/` counterpart

The frozen `Theorems.lean` holds the immutable *statements* (as `sorry`). The
real proofs live in `Proofs/` as `*_proof` declarations (or instances). Each
`example : @Frozen = @Proof := rfl` below compiles **iff** the proven version has
*exactly* the frozen proposition: by proof irrelevance the `rfl` typechecks when
the two share a type, and is a type error otherwise — a machine-checked guarantee
that no statement drifted and nothing was weakened.
-/

namespace Prob27b

-- Engine + milestone (`K(R)` is not a right ideal):
example : @F_is_null = @F_is_null_proof := rfl
example : @Fe_witness = @Fe_witness_proof := rfl

-- The counterexample over the literal `B = K ⊗_D A`:
example : @prob27b_counterexample = @prob27b_counterexample_proof := rfl
example : @problem27b_false = @problem27b_false_proof := rfl

-- Problem 27's hypotheses, certified (no assumptions):
example : @D_finite_residue_rings = @D_finite_residue_rings_proof := rfl
example : @A_finite_over_D = @instModuleFiniteDA := rfl
example : @A_torsionFree_over_D = @instNoZeroSMulDivisorsDA := rfl
example : @D_subset_A = @algDA_injective := rfl
example : @K_inter_A_eq_D = @K_inter_A_eq_D_proof := rfl

end Prob27b
