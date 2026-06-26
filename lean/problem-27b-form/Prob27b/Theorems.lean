/-
Copyright (c) 2026 Prob27b formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob27b formalization
-/
import Prob27b.Defs

/-!
# The frozen theorems for the Problem 27(b) counterexample

This file is **frozen** after the SETUP stage. Each statement is the minimal
faithful rendering of Problem 27(b) (Werner's conjecture) and `SKETCH.md`.

The headline `problem27b_false` is a Lean statement about the *literal* Problem 27
object `Int(A) = { f ∈ B[X] : f(A) ⊆ A }` with `B = K ⊗_D A`, `K = Frac(𝔽₂[π])`.
Every hypothesis of the conjecture is **certified as a proven theorem with no
assumptions** (`D_finite_residue_rings`, `A_finite_over_D`, `A_torsionFree_over_D`,
`D_subset_A`, `K_inter_A_eq_D`), so the counterexample lands squarely in the case
the conjecture is about. The ring-level `F_is_null` / `Fe_witness` are the engine
(and an intermediate milestone: `K(R)` is not a right ideal).
-/

namespace Prob27b

open Polynomial

/-- **SKETCH Step 2.** `F` is a right null polynomial of `R`: it vanishes at
*every* element of `R` (no hypotheses on `r`). -/
theorem F_is_null : ∀ r : R, evalR r F = 0 := sorry

/-- **SKETCH Step 3.** Right-multiplying `F` by the constant `e` destroys
nullity: `F * C e` evaluates to `s ≠ 0` at `a₀ = u + v`. With `F_is_null`, this
shows the right null polynomials of `R` are **not** a right ideal of `R[X]` —
the mathematical heart of the counterexample. -/
theorem Fe_witness : evalR a₀ (F * C e) = s ∧ s ≠ 0 := sorry

/-- **SKETCH Steps 4–5 (witnesses).** Over the Problem 27 coefficient ring
`B = K ⊗_D A`, both `Pb = F̃/π` and the constant `econstB = e` are integer-valued
on `A`, but their product is not. -/
theorem prob27b_counterexample :
    IntegerValued Pb ∧ IntegerValued econstB ∧ ¬ IntegerValued (Pb * econstB) := sorry

/-- **Headline — refutation of Problem 27(b).** `Int(A) = { f ∈ B[X] : f(A) ⊆ A }`
is **not** closed under multiplication: `Pb` and `econstB` lie in `Int(A)` but
their product does not. Hence `Int(A)` is not a ring. -/
theorem problem27b_false : ∃ g₁ ∈ IntA, ∃ g₂ ∈ IntA, g₁ * g₂ ∉ IntA := sorry

/-! ### Problem 27's hypotheses, certified for `D = 𝔽₂[π]`, `A = R[π]`
Each is proven unconditionally (no assumptions), so the example is admissible. -/

/-- `D = 𝔽₂[π]` has finite residue rings: every nonzero quotient `D/(g)` is
finite. -/
theorem D_finite_residue_rings :
    ∀ g : Polynomial (ZMod 2), g ≠ 0 → Finite (Polynomial (ZMod 2) ⧸ Ideal.span {g}) := sorry

/-- `A` is a finite `D`-algebra (finitely generated as a `D`-module). -/
theorem A_finite_over_D : Module.Finite D A := sorry

/-- `A` is torsion-free over `D`. -/
theorem A_torsionFree_over_D : NoZeroSMulDivisors D A := sorry

/-- `D ⊆ A`: the structure map `D → A` is injective. -/
theorem D_subset_A : Function.Injective (algebraMap D A) := sorry

/-- `K ∩ A = D` inside `B`: the only elements of `A` that are scalars (lie in `K`)
are those of `D`. -/
theorem K_inter_A_eq_D :
    Set.range (incK : K → B) ∩ Set.range (incA : A → B) = Set.range (algebraMap D B) := sorry

end Prob27b
