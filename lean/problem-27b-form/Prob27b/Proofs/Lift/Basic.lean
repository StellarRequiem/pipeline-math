/-
Copyright (c) 2026 Prob27b formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob27b formalization
-/
import Prob27b.Proofs.Null.Basic

/-!
# Stage D — Lift: `P = F̃/π` is integer-valued (`Lift/`)

We transport the ring-level nullity `F_is_null_proof` across the "mod `π`" ring
hom `piHom : A ↠ R` (`π ↦ 0`, i.e. the constant-coefficient map). The key support
lemma is

  `P_div : ∀ a : A, ∃ b : A, Ftilde.eval a = X * b`

("the numerator `F̃(a)` is divisible by `π`"), proved by evaluating the
*universal* `F_is_null_proof` at the arbitrary element `piHom a : R`. This is
where the hypothesis-free `∀ r : R` form of Stage B is essential.

No commutativity is used: `hom_eval₂` and `Polynomial.constantCoeff` hold for any
semiring, so they apply to the noncommutative `A = R[π]`.
-/

namespace Prob27b

open Polynomial

/-- The "mod `π`" ring hom `A = R[π] ↠ R`: the constant-coefficient map (`π ↦ 0`).
Its kernel is the ideal `π·A`. -/
def piHom : A →+* R := Polynomial.constantCoeff

@[simp] theorem piHom_C (r : R) : piHom (C r) = r := coeff_C_zero

theorem piHom_comp_C : piHom.comp (C : R →+* A) = RingHom.id R :=
  RingHom.ext fun r => piHom_C r

theorem piHom_apply (a : A) : piHom a = a.coeff 0 := rfl

/-- **Naturality.** Reducing the numerator `F̃(a)` mod `π` equals evaluating the
original `F` at `a` reduced mod `π`. -/
theorem piHom_natural (a : A) : piHom (Ftilde.eval a) = evalR (piHom a) F := by
  unfold Ftilde
  rw [eval_map, hom_eval₂, piHom_comp_C]
  rfl

/-- **`P = F̃/π` is integer-valued (numerator side).** For every `a : A`, the
numerator `F̃(a)` is divisible by `π = X`. Uses `F_is_null_proof` at the arbitrary
element `piHom a` — the universal form of Stage B is what makes this work. -/
theorem P_div (a : A) : ∃ b : A, Ftilde.eval a = X * b := by
  have key : piHom (Ftilde.eval a) = 0 := by
    rw [piHom_natural]; exact F_is_null_proof (piHom a)
  rw [piHom_apply] at key
  exact X_dvd_iff.mpr key

end Prob27b
