import Prob20.Defs
import Prob20.Theorems
import Prob20.Proofs.Domain.ResidueField
import Prob20.Proofs.Domain.FractionField
import Prob20.Proofs.KeyObs.KeyMembership

/-!
# Stage 4.1 — `g_mem` : `g = q² + q ∈ Int(D)`

We prove `g_mem` (frozen in `Prob20/Theorems.lean`): the polynomial
`g = q² + q`, with `q = p/π = (X²+X)/(t(t+1))`, lies in the genuine
integer-valued subalgebra `Int(D)`, quantified over **all** `d : Dom`.

The argument (SKETCH *Failure of Surjectivity*, first paragraph):

* For every `d : Dom`, `p(d) = d² + d ∈ 𝔪` (reuse `Prob20.Proofs.KeyObs.pd_mem`).
* `𝔪 ⊆ π·T`: an element of `𝔪 = ker resD ⊆ T` has both residues `res0 = res1 = 0`,
  hence vanishes at the two places `t = 0`, `t = 1`, so (writing it as `a/s` with
  `a ∈ 𝔽₂[t]`, `s ∈ S`) `X` and `X+1` both divide `a`, and by coprimality
  `X(X+1) = π` divides `a`; thus the element is `π·w` for some `w : T`.
* Therefore `q(d) = π⁻¹·p(d) = w ∈ T`.
* Finally `g(d) = q(d)² + q(d) = w² + w`, and since both residues of `T` land in
  `𝔽₂` where `x² + x = 0`, we get `res0(g(d)) = res1(g(d)) = 0`, so `g(d) ∈ D`.
  Hence `g(ι d) ∈ ι(D)`.

No point is sampled; everything is `∀ d : Dom`.
-/

open scoped nonZeroDivisors

open Prob20 Prob20.Proofs.Domain Prob20.Proofs.KeyObs

namespace Prob20.Proofs.Surjective

open Polynomial

/-- In `𝔽₂ = ZMod 2`, `z² + z = 0`. -/
private theorem sq_add_self_zmod2' : ∀ z : ZMod 2, z ^ 2 + z = 0 := by decide

/-- `res0` of an `algebraMap`ped polynomial is its evaluation at `t = 0`. -/
private theorem res0_algebraMap (a : Polynomial (ZMod 2)) :
    res0 (algebraMap (Polynomial (ZMod 2)) Tsub a) = eval0 a := by
  simp only [res0, IsLocalization.lift_eq]

/-- `res1` of an `algebraMap`ped polynomial is its evaluation at `t = 1`. -/
private theorem res1_algebraMap (a : Polynomial (ZMod 2)) :
    res1 (algebraMap (Polynomial (ZMod 2)) Tsub a) = eval1 a := by
  simp only [res1, IsLocalization.lift_eq]

/-- In `Polynomial (ZMod 2)`, vanishing at `t = 1` gives divisibility by `X + 1`
(`= X - 1` in characteristic two). -/
private theorem X_add_one_dvd (a : Polynomial (ZMod 2)) (hr : a.eval 1 = 0) :
    (Polynomial.X + 1 : Polynomial (ZMod 2)) ∣ a := by
  have hd : (Polynomial.X - Polynomial.C (1 : ZMod 2)) ∣ a :=
    (Polynomial.dvd_iff_isRoot).mpr hr
  have hsum : (1 : Polynomial (ZMod 2)) + 1 = 0 := by
    rw [← Polynomial.C_1, ← Polynomial.C_add, show (1 + 1 : ZMod 2) = 0 from by decide,
      Polynomial.C_0]
  have hneg : (-1 : Polynomial (ZMod 2)) = 1 := neg_eq_of_add_eq_zero_left hsum
  have hX1 : (Polynomial.X - Polynomial.C (1 : ZMod 2)) = Polynomial.X + 1 := by
    rw [Polynomial.C_1, sub_eq_add_neg, hneg]
  rwa [hX1] at hd

/-- **The divisibility lemma `𝔪 ⊆ π·T`.** Any `m : T` whose two residues vanish is
divisible by `π = t(t+1)` in `T`. -/
theorem mem_piTsub (m : Tsub) (h0 : res0 m = 0) (h1 : res1 m = 0) :
    ∃ w : Tsub, m = piTsub * w := by
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj Sset m
  -- hs : m * algebraMap _ Tsub ↑s = algebraMap _ Tsub a
  have ha0 : eval0 a = 0 := by
    have h := congrArg res0 hs
    rw [map_mul, h0, zero_mul, res0_algebraMap] at h
    exact h.symm
  have ha1 : eval1 a = 0 := by
    have h := congrArg res1 hs
    rw [map_mul, h1, zero_mul, res1_algebraMap] at h
    exact h.symm
  have hX : (Polynomial.X : Polynomial (ZMod 2)) ∣ a := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    simpa [eval0, Polynomial.coe_evalRingHom] using ha0
  have hX1 : (Polynomial.X + 1 : Polynomial (ZMod 2)) ∣ a := by
    have hr : a.eval 1 = 0 := by simpa [eval1, Polynomial.coe_evalRingHom] using ha1
    exact X_add_one_dvd a hr
  have hcop : IsCoprime (Polynomial.X : Polynomial (ZMod 2)) (Polynomial.X + 1) :=
    ⟨-1, 1, by ring⟩
  obtain ⟨b, hb⟩ := hcop.mul_dvd hX hX1
  -- s maps to a unit of T
  obtain ⟨v, hv⟩ := IsLocalization.map_units Tsub s
  refine ⟨algebraMap (Polynomial (ZMod 2)) Tsub b * (↑(v⁻¹) : Tsub), ?_⟩
  have hav : algebraMap (Polynomial (ZMod 2)) Tsub a
      = piTsub * algebraMap (Polynomial (ZMod 2)) Tsub b := by
    rw [hb, map_mul]; rfl
  have key : m * (v : Tsub) = piTsub * algebraMap (Polynomial (ZMod 2)) Tsub b := by
    rw [hv, hs, hav]
  calc m = m * ((v : Tsub) * (↑(v⁻¹) : Tsub)) := by rw [Units.mul_inv, mul_one]
    _ = (m * (v : Tsub)) * (↑(v⁻¹) : Tsub) := by rw [mul_assoc]
    _ = (piTsub * algebraMap (Polynomial (ZMod 2)) Tsub b) * (↑(v⁻¹) : Tsub) := by rw [key]
    _ = piTsub * (algebraMap (Polynomial (ZMod 2)) Tsub b * (↑(v⁻¹) : Tsub)) := by rw [mul_assoc]

/-- `(piTsub : Kt) = π = t(t+1)`. -/
theorem coe_piTsub : (piTsub : Kt) = piElt := by
  have h : (piTsub : Kt)
      = algebraMap (Polynomial (ZMod 2)) Kt (Polynomial.X * (Polynomial.X + 1)) := by
    rw [piTsub, IsScalarTower.algebraMap_apply (Polynomial (ZMod 2)) Tsub Kt]
    rfl
  rw [h, piElt, tElt, map_mul, map_add, map_one, RatFunc.algebraMap_X]

/-- `π = t(t+1) ≠ 0` in `Kt`. -/
theorem piElt_ne_zero : (piElt : Kt) ≠ 0 := by
  rw [← coe_piTsub]
  simp only [ne_eq, ZeroMemClass.coe_eq_zero]
  exact piTsub_ne_zero

/-- **Stage 4.1 — `g_mem`.** `g = q² + q ∈ Int(D)`. -/
theorem g_mem_proof : gPoly ∈ IntPoly Dom Kt := by
  intro d
  -- `m = d² + d ∈ 𝔪`, so both residues vanish
  have hm0 : res0 ((d ^ 2 + d : Dom) : Tsub) = 0 := RingHom.mem_ker.mp (pd_mem d)
  have hm1 : res1 ((d ^ 2 + d : Dom) : Tsub) = 0 := ((d ^ 2 + d : Dom).2).symm.trans hm0
  -- `m = π·w` in T
  obtain ⟨w, hw⟩ := mem_piTsub ((d ^ 2 + d : Dom) : Tsub) hm0 hm1
  -- `g(d) = w² + w`, with res0 = res1 = 0 ⇒ `∈ D`
  have hwmem : res0 (w ^ 2 + w) = res1 (w ^ 2 + w) := by
    have e0 : res0 (w ^ 2 + w) = 0 := by
      rw [map_add, map_pow]; exact sq_add_self_zmod2' (res0 w)
    have e1 : res1 (w ^ 2 + w) = 0 := by
      rw [map_add, map_pow]; exact sq_add_self_zmod2' (res1 w)
    rw [e0, e1]
  refine ⟨⟨w ^ 2 + w, hwmem⟩, ?_⟩
  -- `q(d) = w`
  have hQ : aeval (algebraMap Dom Kt d) qPoly = (w : Kt) := by
    have e : aeval (algebraMap Dom Kt d) qPoly
        = piElt⁻¹ * algebraMap Dom Kt (d ^ 2 + d) := by
      simp only [qPoly, pPoly, map_mul, map_add, map_pow, Polynomial.aeval_C,
        Polynomial.aeval_X, Algebra.algebraMap_self_apply]
    have hcoe : algebraMap Dom Kt (d ^ 2 + d) = piElt * (w : Kt) := by
      rw [domToKt_eq, hw, Subalgebra.coe_mul, coe_piTsub]
    rw [e, hcoe, ← mul_assoc, inv_mul_cancel₀ piElt_ne_zero, one_mul]
  -- assemble: `g(ι d) = (w:Kt)² + (w:Kt) = ι ⟨w²+w, _⟩`
  show algebraMap Dom Kt ⟨w ^ 2 + w, hwmem⟩ = aeval (algebraMap Dom Kt d) gPoly
  rw [gPoly, map_add, map_pow, hQ, domToKt_eq]
  show ((w ^ 2 + w : Tsub) : Kt) = (w : Kt) ^ 2 + (w : Kt)
  rw [Subalgebra.coe_add, Subalgebra.coe_pow]

end Prob20.Proofs.Surjective
