import Mathlib

/-!
# Defs.lean — FROZEN definitions for the Problem 20 counterexample

This file constructs, **`sorry`-free**, every object the proof of Problem 20
needs:

* the field `Kt = 𝔽₂(t)` and the element `t`;
* the semilocal PID `T` (`Tsub`) realized as a subalgebra of `Kt`, its two
  residue maps `res0, res1` at the places `t = 0`, `t = 1`;
* the conductor pullback `D = 𝔽₂ + 𝔪` (`Dom`), as the equalizer of the two
  residues, with its residue `resD` and maximal ideal `mIdeal`;
* the **genuine** integer-valued subalgebras `IntPoly D K = {f ∈ K[X] : f(D) ⊆ D}`
  and `IntPolyN D K n` (quantified over **all** of `D` / `Dⁿ`), parameterized by
  an arbitrary domain `D ⊆ K`;
* the canonical product map `thetaN D K n : ⨂[D] (_ : Fin n), IntPoly → K[X₀,…]`,
  built from `MultilinearMap.mkPiAlgebra` and `PiTensorProduct.lift` over the
  base **`D`**;
* the explicit polynomials `pPoly, tpPoly, t1pPoly, qPoly, gPoly, PMv`;
* the submodule `mIntPoly = 𝔪·Int(D)` of `K[X]`.

The modeling decisions are recorded in `BLUEPRINT.md` Part −1 §2 and in
`PROGRESS.md`. This file is byte-frozen after SETUP (pinned in
`scripts/frozen.sha256`) and is never edited during the proving phase.
-/

open scoped nonZeroDivisors TensorProduct

namespace Prob20

/-! ## Generic integer-valued polynomials and the canonical map `θₙ`

These are parameterized by an arbitrary domain `D` sitting inside a field `K`,
so that the headline `problem20_answer` can quantify over domains. The concrete
counterexample instantiates `(D, K) := (Dom, Kt)`. -/

section Generic

variable (D K : Type) [CommRing D] [Field K] [Algebra D K]

/-- `Int(D) = { f ∈ K[X] : f(D) ⊆ D }`, the genuine integer-valued polynomial
subalgebra. Membership is quantified over **all** `d : D`: `f(ι d)` lies in the
image of `D` in `K`, where `ι = algebraMap D K`. -/
noncomputable def IntPoly : Subalgebra D (Polynomial K) where
  carrier := { f | ∀ d : D, Polynomial.aeval (algebraMap D K d) f ∈ (algebraMap D K).range }
  mul_mem' hf hg := fun d => by rw [map_mul]; exact Subring.mul_mem _ (hf d) (hg d)
  add_mem' hf hg := fun d => by rw [map_add]; exact Subring.add_mem _ (hf d) (hg d)
  algebraMap_mem' r := fun d => by
    refine ⟨r, ?_⟩
    rw [Polynomial.algebraMap_apply, Polynomial.aeval_C]
    rfl

/-- `Int(Dⁿ) = { F ∈ K[X₀,…,X_{n-1}] : F(Dⁿ) ⊆ D }`, the genuine multivariate
integer-valued polynomial subalgebra, quantified over **all** `d : Fin n → D`. -/
noncomputable def IntPolyN (n : ℕ) : Subalgebra D (MvPolynomial (Fin n) K) where
  carrier := { F | ∀ d : Fin n → D,
                 MvPolynomial.eval (fun i => algebraMap D K (d i)) F ∈ (algebraMap D K).range }
  mul_mem' hf hg := fun d => by rw [map_mul]; exact Subring.mul_mem _ (hf d) (hg d)
  add_mem' hf hg := fun d => by rw [map_add]; exact Subring.add_mem _ (hf d) (hg d)
  algebraMap_mem' r := fun d => by
    refine ⟨r, ?_⟩
    rw [MvPolynomial.algebraMap_apply, MvPolynomial.eval_C]

/-- The `i`-th coordinate inclusion `Int(D) → K[X₀,…,X_{n-1}]`, sending the
variable `X` to `Xᵢ`. A `D`-algebra hom. -/
noncomputable def incl (n : ℕ) (i : Fin n) : IntPoly D K →ₐ[D] MvPolynomial (Fin n) K :=
  ((Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) K)).restrictScalars D).comp
    (IntPoly D K).val

/-- The multilinear map `(f₀,…,f_{n-1}) ↦ ∏ᵢ fᵢ(Xᵢ)`, obtained from the algebra
product `MultilinearMap.mkPiAlgebra` precomposed with the `n` coordinate
inclusions. -/
noncomputable def thetaMul (n : ℕ) :
    MultilinearMap D (fun _ : Fin n => IntPoly D K) (MvPolynomial (Fin n) K) :=
  (MultilinearMap.mkPiAlgebra D (Fin n) (MvPolynomial (Fin n) K)).compLinearMap
    (fun i => (incl D K n i).toLinearMap)

/-- The canonical product map `θₙ : Int(D)^{⊗_D n} → K[X₀,…,X_{n-1}]`,
`f₀ ⊗ ⋯ ⊗ f_{n-1} ↦ ∏ᵢ fᵢ(Xᵢ)`. The tensor power is over the base **`D`**. It is
a `D`-linear map. -/
noncomputable def thetaN (n : ℕ) :
    (⨂[D] (_ : Fin n), IntPoly D K) →ₗ[D] MvPolynomial (Fin n) K :=
  PiTensorProduct.lift (thetaMul D K n)

end Generic

/-! ## The concrete counterexample domain `D = 𝔽₂ + 𝔪`

`K = Frac(D) = 𝔽₂(t) = RatFunc (ZMod 2)`. `T = S⁻¹𝔽₂[t]` is the semilocal PID
realized as a subalgebra of `Kt`, where `S` is the set of polynomials
nonvanishing at `t = 0` and `t = 1`. `D` is the equalizer of the two residue
maps `res0, res1 : T → 𝔽₂`. -/

/-- The field `K = 𝔽₂(t)`. -/
abbrev Kt : Type := RatFunc (ZMod 2)

noncomputable section

/-- The element `t ∈ 𝔽₂(t)`. -/
def tElt : Kt := RatFunc.X

/-- Evaluation `𝔽₂[t] → 𝔽₂` at `t = 0`. -/
def eval0 : Polynomial (ZMod 2) →+* ZMod 2 := Polynomial.evalRingHom 0

/-- Evaluation `𝔽₂[t] → 𝔽₂` at `t = 1`. -/
def eval1 : Polynomial (ZMod 2) →+* ZMod 2 := Polynomial.evalRingHom 1

/-- The multiplicative set `S ⊆ 𝔽₂[t]` of polynomials nonvanishing at both places
`t = 0` and `t = 1`. -/
def Sset : Submonoid (Polynomial (ZMod 2)) :=
  (nonZeroDivisors (ZMod 2)).comap eval0 ⊓ (nonZeroDivisors (ZMod 2)).comap eval1

/-- `S` contains no zero divisors of `𝔽₂[t]`. -/
theorem hSset : Sset ≤ nonZeroDivisors (Polynomial (ZMod 2)) := by
  intro s hs
  have h0 : eval0 s ∈ nonZeroDivisors (ZMod 2) :=
    Submonoid.mem_comap.mp (Submonoid.mem_inf.mp hs).1
  rw [mem_nonZeroDivisors_iff_ne_zero] at h0 ⊢
  intro hs0
  exact h0 (by rw [hs0, map_zero])

/-- The semilocal PID `T = S⁻¹𝔽₂[t]`, as a subalgebra of `Kt`. -/
def Tsub : Subalgebra (Polynomial (ZMod 2)) Kt :=
  Localization.subalgebra.ofField Kt Sset hSset

instance : IsLocalization Sset Tsub :=
  Localization.subalgebra.isLocalization_ofField Kt Sset hSset

/-- `eval0` sends `S` into the units of `𝔽₂`, so it lifts to `T`. -/
theorem hu0 : ∀ y : Sset, IsUnit (eval0 (y : Polynomial (ZMod 2))) := by
  rintro ⟨y, hy⟩
  have h : eval0 y ∈ nonZeroDivisors (ZMod 2) :=
    Submonoid.mem_comap.mp (Submonoid.mem_inf.mp hy).1
  rw [mem_nonZeroDivisors_iff_ne_zero] at h
  exact isUnit_iff_ne_zero.mpr h

/-- `eval1` sends `S` into the units of `𝔽₂`, so it lifts to `T`. -/
theorem hu1 : ∀ y : Sset, IsUnit (eval1 (y : Polynomial (ZMod 2))) := by
  rintro ⟨y, hy⟩
  have h : eval1 y ∈ nonZeroDivisors (ZMod 2) :=
    Submonoid.mem_comap.mp (Submonoid.mem_inf.mp hy).2
  rw [mem_nonZeroDivisors_iff_ne_zero] at h
  exact isUnit_iff_ne_zero.mpr h

/-- The residue map `res0 : T → 𝔽₂` ("value at `t = 0`"). -/
def res0 : Tsub →+* ZMod 2 := IsLocalization.lift (g := eval0) hu0

/-- The residue map `res1 : T → 𝔽₂` ("value at `t = 1`"). -/
def res1 : Tsub →+* ZMod 2 := IsLocalization.lift (g := eval1) hu1

/-- The conductor pullback `D = 𝔽₂ + 𝔪 = { x ∈ T | res0 x = res1 x }`, as a
subring of `T`. -/
def Dsub : Subring Tsub := res0.eqLocus res1

/-- The counterexample domain `D`. -/
abbrev Dom : Type := Dsub

/-- The `D`-algebra structure on `K = 𝔽₂(t)`, via `D ⊆ T ⊆ K`. -/
def domToKt : Dom →+* Kt := (Subalgebra.val Tsub).toRingHom.comp Dsub.subtype

instance : Algebra Dom Kt := domToKt.toAlgebra

/-- The residue map `resD : D → 𝔽₂` (equal to `res0` and `res1` on `D`). -/
def resD : Dom →+* ZMod 2 := res0.comp Dsub.subtype

/-- The maximal ideal `𝔪 = ker(resD)` of `D`. -/
def mIdeal : Ideal Dom := RingHom.ker resD

/-! ## The explicit polynomials of the sketch (in `Kt[X]`)

These are plain (multivariate) polynomials with no membership proof; their
`Int(D)`-memberships are the frozen theorems. -/

/-- `p = X² + X`. -/
def pPoly : Polynomial Kt := Polynomial.X ^ 2 + Polynomial.X

/-- `tp = t·(X² + X)`. -/
def tpPoly : Polynomial Kt := Polynomial.C tElt * pPoly

/-- `(t+1)p = (t+1)·(X² + X)`. -/
def t1pPoly : Polynomial Kt := Polynomial.C (tElt + 1) * pPoly

/-- `π = t(t+1)`. -/
def piElt : Kt := tElt * (tElt + 1)

/-- `q = p/π = (X² + X)/(t(t+1))`. -/
def qPoly : Polynomial Kt := Polynomial.C piElt⁻¹ * pPoly

/-- `g = q² + q`. -/
def gPoly : Polynomial Kt := qPoly ^ 2 + qPoly

/-- `P(X,Y) = g(XY)`, the bivariate polynomial witnessing non-surjectivity. -/
def PMv : MvPolynomial (Fin 2) Kt :=
  Polynomial.aeval (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) Kt) gPoly

/-! ## The submodule `𝔪·Int(D)` of `Kt[X]`

Used to phrase the `𝔽₂`-linear independence of `p̄, t̄p̄` in `Int(D)/𝔪·Int(D)`
ambiently inside `Kt[X]`. -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- `𝔪·Int(D)`, as a `Dom`-submodule of the ambient `Kt[X]`: the image of
`𝔪 · (⊤ : Int(D))` under `Int(D) ↪ Kt[X]`. -/
def mIntPoly : Submodule Dom (Polynomial Kt) :=
  (mIdeal • (⊤ : Submodule Dom (IntPoly Dom Kt))).map (IntPoly Dom Kt).val.toLinearMap

end

end Prob20
