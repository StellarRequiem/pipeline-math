/-
Copyright (c) 2026 Prob30c formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob30c formalization
-/
import Mathlib

/-!
# Frozen definitions for the Problem 30(c) counterexample

This file is **FROZEN** after the SETUP stage (`BLUEPRINT.md` Part −1 §2): every
later agent consumes these definitions verbatim and never edits this file. It
fixes the modeling of the Anderson–Badawi polynomial-extension counterexample:

* the base ring `D = 𝔽₂[t] = Polynomial (ZMod 2)` (the variable `Polynomial.X`
  plays the uniformizer `t`);
* the central ring `A q`, realized as the **quotient** of `MvPolynomial (Fin 3) D`
  by the relation ideal `Arel q` (three variables `X 0, X 1, X 2` standing for
  `e₁, e₂, e₃`), so that `CommRing (A q)` and `Algebra D (A q)` are inherited for
  free — no associativity obligation is ever discharged;
* the canonical generators `e₁ e₂ e₃ u₁ u₂ s`, the image `tA` of `t`, and the
  augmentation ideal `J = (e₁, e₂, e₃)`;
* the `s`-layer submodules `sComponent = (D/t^q)·s` and `tSComponent = t·(D/t^q)·s`;
* the polynomial witnesses `fPoly, gPoly ∈ (A q)[X]`;
* the textbook absorbing predicate `IsNAbsorbing` and the absorbing number
  `absorbingNumber` (`= ω`).

See the `📝` modeling-decision entries in `PROGRESS.md` for the choices frozen here.
-/

namespace Prob30c

open scoped Polynomial

/-! ## (a) The base ring `D = 𝔽₂[t]`. -/

/-- The base ring `D = 𝔽₂[t]`.  The variable `Polynomial.X : D` plays the
uniformizer `t`; the `t`-adic valuation `v_t` is `Polynomial.rootMultiplicity 0`.
`D` is a PID and an `IsDomain`. -/
abbrev D : Type := Polynomial (ZMod 2)

/-! ## (b) The ring `A q` as a quotient of `MvPolynomial (Fin 3) D`. -/

/-- The augmentation-variable ideal `mP = (e₁, e₂, e₃) = (X 0, X 1, X 2)` of
`MvPolynomial (Fin 3) D`; its cube is one of the relations (`𝔪³ = 0`). -/
noncomputable def mP : Ideal (MvPolynomial (Fin 3) D) :=
  Ideal.span {MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2}

/-- The relation ideal.  Degree-2 rules (`e₁² = 0`, `e₁e₂ = 0`, `e₃² = e₂e₃`),
the cube `𝔪³ = 0`, and the torsion relation `t^q·(e₁e₃ − e₂²) = t^q·s = 0`. -/
noncomputable def Arel (q : ℕ) : Ideal (MvPolynomial (Fin 3) D) :=
  mP ^ 3
  ⊔ Ideal.span
      { MvPolynomial.X 0 ^ 2,                                       -- e₁² = 0
        MvPolynomial.X 0 * MvPolynomial.X 1,                        -- e₁e₂ = 0
        MvPolynomial.X 2 ^ 2 - MvPolynomial.X 1 * MvPolynomial.X 2, -- e₃² = e₂e₃ (= u₁)
        MvPolynomial.C (Polynomial.X ^ q)
          * (MvPolynomial.X 0 * MvPolynomial.X 2 - MvPolynomial.X 1 ^ 2) } -- t^q·s = 0

/-- The central ring `A q = MvPolynomial (Fin 3) D ⧸ Arel q`.  It is
`noncomputable`, infinite, and non-reduced (`J³ = 0`, `e₁² = 0` with `e₁ ≠ 0`).
Do **not** add `IsDomain`/`Field`/`Fintype` instances. -/
def A (q : ℕ) : Type := MvPolynomial (Fin 3) D ⧸ Arel q

noncomputable instance (q : ℕ) : CommRing (A q) := Ideal.Quotient.commRing _
-- the `Algebra D (A q)` instance also supplies `Module D (A q)`
noncomputable instance (q : ℕ) : Algebra D (A q) := Ideal.Quotient.algebra _

/-! ## (b cont.) Generators and canonical objects (images under `Ideal.Quotient.mk`). -/

/-- `e₁ = X 0`. -/
noncomputable def e₁ (q : ℕ) : A q := Ideal.Quotient.mk _ (MvPolynomial.X 0)
/-- `e₂ = X 1`. -/
noncomputable def e₂ (q : ℕ) : A q := Ideal.Quotient.mk _ (MvPolynomial.X 1)
/-- `e₃ = X 2`. -/
noncomputable def e₃ (q : ℕ) : A q := Ideal.Quotient.mk _ (MvPolynomial.X 2)
/-- `u₂ = e₂²` (a free `D`-generator). -/
noncomputable def u₂ (q : ℕ) : A q := e₂ q * e₂ q
/-- `u₁ = e₂e₃ = e₃²` (a free `D`-generator). -/
noncomputable def u₁ (q : ℕ) : A q := e₂ q * e₃ q
/-- `s = e₁e₃ − e₂²` (the `t^q`-torsion element). -/
noncomputable def s (q : ℕ) : A q := e₁ q * e₃ q - u₂ q
/-- `tA = algebraMap D (A q) t`, the image of `t = Polynomial.X ∈ D`. -/
noncomputable def tA (q : ℕ) : A q := algebraMap D (A q) Polynomial.X

/-- The augmentation ideal `J = (e₁, e₂, e₃)` (kernel of `A q → D`); `J³ = 0`. -/
noncomputable def J (q : ℕ) : Ideal (A q) := Ideal.span {e₁ q, e₂ q, e₃ q}

/-! ## (c) The `s`-layer submodules (vocabulary for `cancel_const`, Step 2). -/

/-- The `s`-component `(D/t^q)·s` as a `D`-submodule of `A q`. -/
noncomputable def sComponent (q : ℕ) : Submodule D (A q) := Submodule.span D {s q}
/-- The deeper layer `t·(D/t^q)·s`. -/
noncomputable def tSComponent (q : ℕ) : Submodule D (A q) := Submodule.span D {tA q * s q}

/-! ## (d) The polynomial witnesses `f, g` (Step 4). -/

/-- `f = e₂ + X·e₃ ∈ (A q)[X]`. -/
noncomputable def fPoly (q : ℕ) : Polynomial (A q) :=
  Polynomial.C (e₂ q) + Polynomial.C (e₃ q) * Polynomial.X            -- e₂ + X e₃
/-- `g = (1+X)·e₁ + (X+X²)·e₂ + X²·e₃ ∈ (A q)[X]`. -/
noncomputable def gPoly (q : ℕ) : Polynomial (A q) :=
  Polynomial.C (e₁ q) * (1 + Polynomial.X)
  + Polynomial.C (e₂ q) * (Polynomial.X + Polynomial.X ^ 2)
  + Polynomial.C (e₃ q) * Polynomial.X ^ 2                            -- (1+X)e₁+(X+X²)e₂+X²e₃

/-! ## (e) The absorbing predicates (part of the headline — frozen). -/

/-- `I` is **`n`-absorbing**: whenever a product of `n+1` factors lies in `I`,
some product of `n` of them (omit exactly one) already lies in `I`. -/
def IsNAbsorbing {R : Type*} [CommRing R] (n : ℕ) (I : Ideal R) : Prop :=
  ∀ a : Fin (n + 1) → R, (∏ i, a i) ∈ I →
    ∃ j : Fin (n + 1), (∏ i ∈ Finset.univ.erase j, a i) ∈ I

/-- The **absorbing number** `ω_R(I)`: the least *positive* `n` for which `I` is
`n`-absorbing (junk value `0` if no such `n` exists). -/
noncomputable def absorbingNumber {R : Type*} [CommRing R] (I : Ideal R) : ℕ :=
  sInf {n : ℕ | 1 ≤ n ∧ IsNAbsorbing n I}

end Prob30c
