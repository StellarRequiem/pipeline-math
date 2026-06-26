import Prob20.Defs
import Prob20.Theorems

/-!
# Stage 1.3 — `D_fraction_field` : `Frac(D) = 𝔽₂(t)`

We prove `IsFractionRing Dom Kt`, i.e. `Kt` is the fraction field of the conductor
pullback `Dom = 𝔽₂ + 𝔪`.

Strategy (BLUEPRINT Stage 1.3 / SKETCH *Counterexample Domain*):

* `Kt` is the fraction field of the localization `Tsub = S⁻¹𝔽₂[t]`
  (`IsFractionRing Tsub Kt`, by localization transitivity).
* `algebraMap Dom Kt` is injective (composition of subtype/subalgebra inclusions
  into the field `Kt`).
* Every `z : Kt` is a ratio of `Dom`-elements: writing `z = w₁/w₂` with
  `wᵢ ∈ Tsub`, multiply numerator and denominator by `π = t(t+1)`.  Because the
  two residues of `π` vanish (`π` lies in the maximal ideal of `T` at both
  places `t = 0` and `t = 1`), `π·wᵢ` lands in `Dsub = Dom`, so
  `z = (π·w₁)/(π·w₂)` is a ratio of `Dom`-elements.

This is the honest `IsFractionRing` onto **all** of `𝔽₂(t)` (`t ∈ Frac(Dom)`),
not a proper subfield.
-/

open scoped nonZeroDivisors

namespace Prob20.Proofs.Domain

open Prob20

/-- `Kt` is the fraction field of the localization `Tsub = S⁻¹𝔽₂[t]`. -/
instance instIsFractionRingTsub : IsFractionRing Tsub Kt :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Sset Tsub Kt

/-- The structural element `π = t(t+1) ∈ Tsub`, as the image of the polynomial
`X·(X+1)` under `𝔽₂[t] → T`. -/
noncomputable def piTsub : Tsub :=
  algebraMap (Polynomial (ZMod 2)) Tsub (Polynomial.X * (Polynomial.X + 1))

/-- `res0 π = 0`: `π = t(t+1)` vanishes at the place `t = 0`. -/
theorem res0_piTsub : res0 piTsub = 0 := by
  simp only [res0, piTsub, IsLocalization.lift_eq, eval0, Polynomial.coe_evalRingHom,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  ring

/-- `res1 π = 0`: `π = t(t+1)` vanishes at the place `t = 1` (note `t+1 = 0` there
in characteristic two). -/
theorem res1_piTsub : res1 piTsub = 0 := by
  simp only [res1, piTsub, IsLocalization.lift_eq, eval1, Polynomial.coe_evalRingHom,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
  decide

/-- For every `a : Tsub`, the product `π·a` lands in `Dsub = Dom`: both residues
of `π·a` vanish because both residues of `π` do. -/
theorem mul_piTsub_mem (a : Tsub) : piTsub * a ∈ Dsub := by
  rw [Dsub, RingHom.mem_eqLocus]
  rw [map_mul, map_mul, res0_piTsub, res1_piTsub, zero_mul, zero_mul]

/-- `X·(X+1)` is a nonzero polynomial of `𝔽₂[t]`. -/
theorem poly_ne_zero : (Polynomial.X * (Polynomial.X + 1) : Polynomial (ZMod 2)) ≠ 0 := by
  refine mul_ne_zero Polynomial.X_ne_zero ?_
  intro h
  have := congrArg (Polynomial.eval 0) h
  simp at this

/-- `π ≠ 0` in `Tsub`. -/
theorem piTsub_ne_zero : piTsub ≠ 0 := by
  intro h
  have hinj : Function.Injective (algebraMap (Polynomial (ZMod 2)) Tsub) :=
    IsLocalization.injective Tsub hSset
  apply poly_ne_zero
  apply hinj
  rw [map_zero]
  exact h

/-- `algebraMap Dom Kt` is injective (it is `Dom ↪ Tsub ↪ Kt`, a composition of
subtype inclusions into the field `Kt`). -/
theorem injective_algebraMap : Function.Injective (algebraMap Dom Kt) := by
  intro a b h
  exact Subtype.ext (Subtype.ext h)

/-- **Stage 1.3 — `D_fraction_field`.** `Kt = 𝔽₂(t)` is the fraction field of the
conductor pullback `Dom`. -/
theorem D_fraction_field_proof : IsFractionRing Dom Kt := by
  refine (isLocalization_iff (M := nonZeroDivisors Dom) (S := Kt)).mpr ⟨?_, ?_, ?_⟩
  · -- every nonzero element of `Dom` maps to a unit of the field `Kt`
    rintro ⟨y, hy⟩
    rw [mem_nonZeroDivisors_iff_ne_zero] at hy
    rw [isUnit_iff_ne_zero]
    intro h
    exact hy (injective_algebraMap (by rw [h, map_zero]))
  · -- surjectivity: every `z : Kt` is `(π·w₁)/(π·w₂)` with `π·wᵢ ∈ Dom`
    intro z
    obtain ⟨⟨w1, w2⟩, hw⟩ := IsLocalization.surj (nonZeroDivisors Tsub) z
    simp only [Subalgebra.algebraMap_apply] at hw
    -- hw : z * ↑↑w2 = ↑w1
    have hden : (⟨piTsub * (w2 : Tsub), mul_piTsub_mem _⟩ : Dom) ∈ nonZeroDivisors Dom := by
      rw [mem_nonZeroDivisors_iff_ne_zero]
      intro hz
      have hz' : piTsub * (w2 : Tsub) = 0 := congrArg (Subtype.val) hz
      rcases mul_eq_zero.mp hz' with h | h
      · exact piTsub_ne_zero h
      · exact (nonZeroDivisors.coe_ne_zero w2) h
    refine ⟨(⟨piTsub * w1, mul_piTsub_mem _⟩, ⟨_, hden⟩), ?_⟩
    show z * algebraMap Dom Kt ⟨piTsub * (w2 : Tsub), _⟩
        = algebraMap Dom Kt ⟨piTsub * w1, _⟩
    have e1 : algebraMap Dom Kt ⟨piTsub * (w2 : Tsub), mul_piTsub_mem _⟩
        = (piTsub : Kt) * ((w2 : Tsub) : Kt) := by
      rfl
    have e2 : algebraMap Dom Kt ⟨piTsub * w1, mul_piTsub_mem _⟩
        = (piTsub : Kt) * (w1 : Kt) := by
      rfl
    rw [e1, e2, mul_left_comm, hw]
  · -- the localization equality is forced by injectivity
    intro x y h
    exact ⟨1, by rw [injective_algebraMap h]⟩

end Prob20.Proofs.Domain
