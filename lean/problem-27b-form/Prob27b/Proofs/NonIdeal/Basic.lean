/-
Copyright (c) 2026 Prob27b formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob27b formalization
-/
import Prob27b.Proofs.RingModel.Basic

/-!
# Stage C — `K(R)` is not a right ideal (`NonIdeal/`)

This file proves `Fe_witness` (SKETCH Step 3): right-multiplying the null
polynomial `F` by the constant `e` destroys nullity, since `F * C e` evaluates
to `s ≠ 0` at `a₀ = u + v`. Together with `F_is_null` (Stage B) this shows the
set of right null polynomials of `R` is **not** a right ideal of `R[X]`.

* **C1.** Powers of `a₀`: `a0_sq : a₀^2 = p + q`, `a0_cube : a₀^3 = s + w`,
  `a0_pow4 : a₀^4 = 0` (hence `a₀^5 = a₀^6 = 0`).
* **C2/C3.** Reduce `evalR a₀ (F * C e)` via `eval₂` simp lemmas and the
  `mul_table` to `e * a₀^3 = e * (s + w) = s`.

The noncommutative subtlety is real: the coefficient is multiplied by `e` on
the **right** (`u * e = 0`, `(e+u) * e = e`), keeping `e` on the coefficient
side, then evaluated. No `sorry`, no `native_decide`, no custom axioms.
-/

namespace Prob27b

open Polynomial

/-! ## C1. Powers of `a₀ = u + v`

Each power is a concrete element of `R`, so `decide` settles it directly. -/

/-- `a₀^2 = p + q`. (`a₀ = u+v`; `u²=v²=0`, `uv=p`, `vu=q`.) -/
theorem a0_sq : (a₀ : R) ^ 2 = p + q := by decide

/-- `a₀^3 = s + w`. (`uq=s`, `vp=w`, the other length-3 terms vanish.) -/
theorem a0_cube : (a₀ : R) ^ 3 = s + w := by decide

/-- `a₀^4 = 0`: every path of length `≥ 4` is zero in `R`. -/
theorem a0_pow4 : (a₀ : R) ^ 4 = 0 := by decide

/-- `a₀^5 = 0`, from `a₀^4 = 0`. -/
theorem a0_pow5 : (a₀ : R) ^ 5 = 0 := by
  rw [show (5 : ℕ) = 4 + 1 from rfl, pow_add, a0_pow4, zero_mul]

/-- `a₀^6 = 0`, from `a₀^4 = 0`. -/
theorem a0_pow6 : (a₀ : R) ^ 6 = 0 := by
  rw [show (6 : ℕ) = 4 + 2 from rfl, pow_add, a0_pow4, zero_mul]

/-! ## C2. The right product `F * C e` as monomials

Right-multiplying `F` by `C e` multiplies each coefficient by `e` on the right
(`X` is central, so `X^i * C e = C e * X^i`). Coefficient products:
`u*e = 0`, `e*e = e`, `(e+u)*e = e`. -/

/-- A single `C-X^n` monomial times `C e` collapses the coefficient on the
right: `(C c * X^n) * C e = C (c * e) * X^n`. (`X` central.) -/
private theorem CX_mul_Ce (c : R) (n : ℕ) :
    (C c * X ^ n) * C e = C (c * e) * X ^ n := by
  have h : X ^ n * C e = C e * X ^ n := Commute.pow_left (commute_X (C e)) n
  rw [mul_assoc, h, ← mul_assoc, ← C_mul]

/-- `eval₂` of a monomial `C c * X^n` keeps `c` on the left: `c * a₀ ^ n`. -/
private theorem evalR_CX (c : R) (n : ℕ) :
    evalR a₀ (C c * X ^ n) = c * a₀ ^ n := by
  unfold evalR
  rw [C_mul_X_pow_eq_monomial, eval₂_monomial, RingHom.id_apply]

/-! ## C3. `Fe_witness`

Distribute `F * C e`, collapse each coefficient product and the high powers of
`a₀`, landing on `e * (s + w) = s`. -/

/-- **SKETCH Step 3.** `F * C e` evaluates to `s ≠ 0` at `a₀ = u + v`, so the
right null polynomials of `R` are not closed under right multiplication by the
constant `e`. -/
theorem Fe_witness_proof : evalR a₀ (F * C e) = s ∧ s ≠ 0 := by
  refine ⟨?_, s_ne_zero⟩
  show evalR a₀ (F * C e) = s
  unfold F
  -- distribute the right multiplication and collapse coefficients to monomials
  simp only [add_mul, CX_mul_Ce]
  -- evaluate: `evalR` is additive, and each monomial via `evalR_CX`
  unfold evalR
  rw [eval₂_add, eval₂_add, eval₂_add, eval₂_add]
  show evalR a₀ _ + evalR a₀ _ + evalR a₀ _ + evalR a₀ _ + evalR a₀ _ = s
  rw [evalR_CX, evalR_CX, evalR_CX, evalR_CX, evalR_CX]
  -- collapse coefficient products and high powers of a₀
  rw [a0_pow4, a0_pow5, a0_pow6, a0_cube]
  simp only [u_mul_e, e_mul_e, mul_zero, zero_mul, add_zero, zero_add,
    mul_add, e_mul_s, e_mul_w]

end Prob27b
