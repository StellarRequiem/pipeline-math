/-
Copyright (c) 2026 Prob30c formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob30c formalization
-/
import Prob30c.Proofs.Absorbing.Basic
import Prob30c.Proofs.UpperA.Basic
import Prob30c.Proofs.LowerA.Basic
import Prob30c.Proofs.UpperAX.Basic
import Prob30c.Proofs.LowerAX.Basic

/-!
# Stage W — the exact absorbing numbers and the headline refutation.

Combines the four bound theorems with the ring-agnostic
`absorbingNumber_eq_of` (Stage S0) to pin the absorbing numbers exactly:
`ω_{A q}(0) = q+1`, `ω_{(A q)[X]}(0) = q+2`, hence the polynomial extension
increases `ω` by exactly one, refuting Problem 30(c).

* `omega_A_proof`                  — `absorbingNumber (⊥ : Ideal (A q)) = q+1`  (W1, ★ MILESTONE)
* `omega_AX_proof`                 — `absorbingNumber (⊥ : Ideal (A q)[X]) = q+2`  (W2)
* `omega_polynomial_increase_proof`— the `+1` increase  (W3)
* `problem30c_false_proof`         — `∃ R I, ω(I[X]) ≠ ω(I)`  (W4, ★ HEADLINE)
-/

namespace Prob30c

open scoped Polynomial

/-- W1 (★ MILESTONE).  The down-stairs absorbing number is exactly `q+1`:
`absorbingNumber_eq_of` with `k = q+1`, fed `A_succAbsorbing_proof` (Stage UA,
the `(q+1)`-absorbing upper bound) and `A_not_qAbsorbing_proof` (Stage LA, the
non-`q`-absorbing lower bound, presented at index `(q+1)-1 = q`). -/
theorem omega_A_proof (q : ℕ) (hq : 2 ≤ q) :
    absorbingNumber (⊥ : Ideal (A q)) = q + 1 := by
  refine absorbingNumber_eq_of (by omega) (A_succAbsorbing_proof q hq) ?_
  rw [Nat.add_sub_cancel]
  exact A_not_qAbsorbing_proof q hq

/-- W2.  The up-stairs absorbing number is exactly `q+2`: `absorbingNumber_eq_of`
with `k = q+2`, fed `AX_succ2Absorbing_proof` (Stage UX) and
`AX_not_succAbsorbing_proof` (Stage LX, presented at index `(q+2)-1 = q+1`). -/
theorem omega_AX_proof (q : ℕ) (hq : 2 ≤ q) :
    absorbingNumber (⊥ : Ideal (Polynomial (A q))) = q + 2 := by
  refine absorbingNumber_eq_of (by omega) (AX_succ2Absorbing_proof q hq) ?_
  rw [show q + 2 - 1 = q + 1 from rfl]
  exact AX_not_succAbsorbing_proof q hq

/-- W3.  The polynomial extension increases the absorbing number by exactly one:
combine W1 and W2 (`q+2 = (q+1)+1`). -/
theorem omega_polynomial_increase_proof (q : ℕ) (hq : 2 ≤ q) :
    absorbingNumber (⊥ : Ideal (Polynomial (A q)))
      = absorbingNumber (⊥ : Ideal (A q)) + 1 := by
  rw [omega_A_proof q hq, omega_AX_proof q hq]

/-- W4 (★ HEADLINE).  Refutation of Problem 30(c): there is a commutative ring
`R` and an ideal `I` whose absorbing number strictly changes under the
polynomial extension `I ↦ I·R[X]`.  Witness `R = A 2`, `I = ⊥`: then
`(⊥).map C = ⊥` (`Ideal.map_bot`), and the two absorbing numbers are the genuine
values `4` (`omega_AX` at `q = 2`) and `3` (`omega_A` at `q = 2`), so `4 ≠ 3`. -/
theorem problem30c_false_proof :
    ∃ (R : Type) (_ : CommRing R) (I : Ideal R),
      absorbingNumber (I.map (Polynomial.C : R →+* Polynomial R)) ≠ absorbingNumber I := by
  refine ⟨A 2, inferInstance, (⊥ : Ideal (A 2)), ?_⟩
  rw [Ideal.map_bot, omega_A_proof 2 (by norm_num), omega_AX_proof 2 (by norm_num)]
  norm_num

end Prob30c
