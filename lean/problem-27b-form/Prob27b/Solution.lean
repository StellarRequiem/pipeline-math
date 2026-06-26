/-
Copyright (c) 2026 Prob27b formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob27b formalization
-/
import Prob27b.Proofs.Capstone.Basic
import Prob27b.Proofs.Admissibility.Basic
import Prob27b.Proofs.KInterA.Basic

/-!
# Solution: the frozen statements, proven

`Theorems.lean` holds the immutable *spec* (each theorem is `:= sorry`). This file
restates each of those statements **verbatim** in the `Prob27b.Solution` namespace
and proves it with the corresponding sorry-free declaration from `Proofs/`. Each
`:= …_proof` typechecks only if the proof has *exactly* the frozen proposition, so
this file is simultaneously the no-drift certificate and the clean, named result:
`#print axioms Prob27b.Solution.problem27b_false` is `[propext, Classical.choice,
Quot.sound]` — no `sorry`, no `sorryAx`.
-/

namespace Prob27b.Solution

open Prob27b Polynomial

/-- **SKETCH Step 2.** `F` is a right null polynomial of `R`. -/
theorem F_is_null : ∀ r : R, evalR r F = 0 := F_is_null_proof

/-- **SKETCH Step 3.** `F · e` is not null (`= s ≠ 0` at `a₀`), so the right null
polynomials of `R` are not a right ideal of `R[X]`. -/
theorem Fe_witness : evalR a₀ (F * C e) = s ∧ s ≠ 0 := Fe_witness_proof

/-- **SKETCH Steps 4–5 (witnesses).** `Pb = F̃/π` and `econstB = e` are
integer-valued on `A`, but `Pb · econstB` is not. -/
theorem prob27b_counterexample :
    IntegerValued Pb ∧ IntegerValued econstB ∧ ¬ IntegerValued (Pb * econstB) :=
  prob27b_counterexample_proof

/-- **Headline — refutation of Problem 27(b).** `Int(A) = { f ∈ B[X] : f(A) ⊆ A }`
over the literal `B = K ⊗_D A` is not closed under multiplication. -/
theorem problem27b_false : ∃ g₁ ∈ IntA, ∃ g₂ ∈ IntA, g₁ * g₂ ∉ IntA :=
  problem27b_false_proof

/-- `D = 𝔽₂[π]` has finite residue rings. -/
theorem D_finite_residue_rings :
    ∀ g : Polynomial (ZMod 2), g ≠ 0 → Finite (Polynomial (ZMod 2) ⧸ Ideal.span {g}) :=
  D_finite_residue_rings_proof

/-- `A` is a finite `D`-module. -/
theorem A_finite_over_D : Module.Finite D A := instModuleFiniteDA

/-- `A` is torsion-free over `D`. -/
theorem A_torsionFree_over_D : NoZeroSMulDivisors D A := instNoZeroSMulDivisorsDA

/-- `D ⊆ A`. -/
theorem D_subset_A : Function.Injective (algebraMap D A) := algDA_injective

/-- `K ∩ A = D` inside `B`. -/
theorem K_inter_A_eq_D :
    Set.range (incK : K → B) ∩ Set.range (incA : A → B) = Set.range (algebraMap D B) :=
  K_inter_A_eq_D_proof

end Prob27b.Solution
