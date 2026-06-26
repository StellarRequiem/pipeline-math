/-
Copyright (c) 2026 Prob30c formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob30c formalization
-/
import Prob30c.Proofs.RingModel.Basic

/-!
# Stage PC — cancel_poly, the polynomial cancellation f·g = X(1+X)s (Step 4).

BLUEPRINT Part 2 Stage PC ↔ SKETCH Step 4.  With the frozen
`fPoly q = e₂ + X·e₃` and `gPoly q = (1+X)e₁ + (X+X²)e₂ + X²e₃`, the product
expands (using the Stage-A multiplication table) to

  fPoly·gPoly = (X²+(X²+X³)+X³)·u₁ + ((X+X²)+X(1+X))·u₂ + X(1+X)·s.

The free `u₁`- and `u₂`-graded parts vanish **in characteristic 2**, leaving
exactly `C (s q) * (X * (1 + X))`.  This is the polynomial cancellation that
`cancel_const` (Stage C) forbids for two constant `J`-factors.
-/

namespace Prob30c

open scoped Polynomial

variable (q : ℕ)

/-- Characteristic two: `(2 : A q) = 0`.  `A q` is a quotient of
`MvPolynomial (Fin 3) D` with `D = 𝔽₂[t]`, so `2 = 0` already in `D`. -/
theorem two_eq_zero_A : (2 : A q) = 0 := by
  have hD : (2 : D) = 0 := by
    rw [show (2 : D) = Polynomial.C (2 : ZMod 2) from (map_ofNat Polynomial.C 2).symm]
    rw [show (2 : ZMod 2) = 0 from by decide, map_zero]
  rw [show (2 : A q) = algebraMap D (A q) (2 : D) from (map_ofNat (algebraMap D (A q)) 2).symm,
    hD, map_zero]

/-- `C (u₂ q) + C (u₂ q) = 0` (char two, in `(A q)[X]`). -/
theorem C_u₂_add_self : Polynomial.C (u₂ q) + Polynomial.C (u₂ q) = 0 := by
  rw [← Polynomial.C_add, ← two_mul, two_eq_zero_A, zero_mul, map_zero]

/-- `C (u₁ q) + C (u₁ q) = 0` (char two, in `(A q)[X]`). -/
theorem C_u₁_add_self : Polynomial.C (u₁ q) + Polynomial.C (u₁ q) = 0 := by
  rw [← Polynomial.C_add, ← two_mul, two_eq_zero_A, zero_mul, map_zero]

/-- **PC1 — `cancel_poly`.**  The frozen polynomial identity
`fPoly q * gPoly q = C (s q) * (X * (1 + X))` in `(A q)[X]`.  The free `u₁, u₂`
parts cancel in characteristic two; only the `s`-graded `X(1+X)` survives. -/
theorem cancel_poly_proof (q : ℕ) :
    fPoly q * gPoly q = Polynomial.C (s q) * (Polynomial.X * (1 + Polynomial.X)) := by
  -- Expand the product into the six `C(eᵢ)·C(eⱼ)·monomial` terms (pure ring algebra).
  have key : fPoly q * gPoly q =
      Polynomial.C (e₂ q * e₁ q) * (1 + Polynomial.X)
      + Polynomial.C (e₂ q * e₂ q) * (Polynomial.X + Polynomial.X ^ 2)
      + Polynomial.C (e₂ q * e₃ q) * Polynomial.X ^ 2
      + Polynomial.C (e₃ q * e₁ q) * (Polynomial.X * (1 + Polynomial.X))
      + Polynomial.C (e₃ q * e₂ q) * (Polynomial.X * (Polynomial.X + Polynomial.X ^ 2))
      + Polynomial.C (e₃ q * e₃ q) * Polynomial.X ^ 3 := by
    rw [fPoly, gPoly]
    simp only [Polynomial.C_mul]
    ring
  rw [key, e2_mul_e1, e2_mul_e2, e2_mul_e3, e3_mul_e1, e3_mul_e2, e3_mul_e3,
    Polynomial.C_add]
  simp only [map_zero, zero_mul, zero_add]
  -- Remaining: free `u₁,u₂` parts cancel in char two.
  linear_combination (Polynomial.X + Polynomial.X ^ 2) * C_u₂_add_self q
    + (Polynomial.X ^ 2 + Polynomial.X ^ 3) * C_u₁_add_self q

end Prob30c
