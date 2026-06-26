/-
Copyright (c) 2026 Prob30c formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob30c formalization
-/
import Prob30c.Defs

/-!
# Frozen theorem statements for the Problem 30(c) counterexample

This file is **FROZEN** after the SETUP stage (`BLUEPRINT.md` Part −1 §3). It
holds the **ten** immutable theorem *statements* as `:= sorry` stubs. The real
proofs live in `Prob30c/Proofs/**` as `*_proof` declarations and are exposed,
verbatim and clean, in `Prob30c/Solution.lean`; `Prob30c/Discharge.lean`
machine-checks (`@Frozen = @Proof := rfl`) that no statement drifted.

`sorry` is permitted **only** in this file (the frozen stubs). The names below
are binding — `verify.sh`, `Discharge.lean`, and `Solution.lean` depend on them.
-/

namespace Prob30c

open scoped Polynomial

-- Step 2  (the constant cancellation — the obstruction that vanishes over R[X])
theorem cancel_const (q : ℕ) (x y : A q) (hx : x ∈ J q) (hy : y ∈ J q)
    (hxy : x * y ∈ sComponent q) : x * y ∈ tSComponent q := sorry

-- Step 4  (the new polynomial cancellation — free u₁,u₂ parts cancel in char 2)
theorem cancel_poly (q : ℕ) :
    fPoly q * gPoly q
      = Polynomial.C (s q) * (Polynomial.X * (1 + Polynomial.X)) := sorry

-- Step 3 lower  (ω_{A q}(0) ≥ q+1 : the length-(q+1) irredundant zero-product s·t^q)
theorem A_not_qAbsorbing (q : ℕ) (hq : 2 ≤ q) :
    ¬ IsNAbsorbing q (⊥ : Ideal (A q)) := sorry

-- Step 3 upper  (ω_{A q}(0) ≤ q+1 : every (q+2)-factor zero-product has an omit-one zero)
theorem A_succAbsorbing (q : ℕ) (hq : 2 ≤ q) :
    IsNAbsorbing (q + 1) (⊥ : Ideal (A q)) := sorry

-- Step 5  (ω_{(A q)[X]}(0) ≥ q+2 : the length-(q+2) witness f,g,t,…,t)
theorem AX_not_succAbsorbing (q : ℕ) (hq : 2 ≤ q) :
    ¬ IsNAbsorbing (q + 1) (⊥ : Ideal (Polynomial (A q))) := sorry

-- Step 6  (ω_{(A q)[X]}(0) ≤ q+2 : matching upper bound over D[X])
theorem AX_succ2Absorbing (q : ℕ) (hq : 2 ≤ q) :
    IsNAbsorbing (q + 2) (⊥ : Ideal (Polynomial (A q))) := sorry

-- Step 3  (the exact down-stairs value ω_{A q}(0) = q+1)  ★ MILESTONE
theorem omega_A (q : ℕ) (hq : 2 ≤ q) :
    absorbingNumber (⊥ : Ideal (A q)) = q + 1 := sorry

-- Step 6  (the exact up-stairs value ω_{(A q)[X]}(0) = q+2)
theorem omega_AX (q : ℕ) (hq : 2 ≤ q) :
    absorbingNumber (⊥ : Ideal (Polynomial (A q))) = q + 2 := sorry

-- Conclusion  (polynomial extension strictly increases ω by exactly 1)
theorem omega_polynomial_increase (q : ℕ) (hq : 2 ≤ q) :
    absorbingNumber (⊥ : Ideal (Polynomial (A q)))
      = absorbingNumber (⊥ : Ideal (A q)) + 1 := sorry

-- Headline  (refutation of Problem 30(c))
theorem problem30c_false :
    ∃ (R : Type) (_ : CommRing R) (I : Ideal R),
      absorbingNumber (I.map (Polynomial.C : R →+* Polynomial R)) ≠ absorbingNumber I := sorry

end Prob30c
