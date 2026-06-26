import Prob20.Defs
import Prob20.Theorems
import Prob20.Proofs.Surjective.Missing

/-!
# Stage 4.2 — the crux lemma `KEY`, proved **unconditionally**, closing `theta2_missing`

`Missing.lean` reduced `theta2_missing` (frozen in `Prob20/Theorems.lean`) — modulo
a single place-1 valuation gap — to the hypothesis

> `KEY : ∀ f ∈ Int(D), ∃ N₀, ∀ N ≥ N₀, f(u_N) − f(0) ∈ 𝔪`   (with `u_N = π(t+1)^N`).

This file discharges `KEY` and feeds it to `theta2_missing_of_KEY`.

## Why `KEY` is true and elementary

For `f ∈ Int(D)`, both `f(u_N)` and `f(0)` lie in `D`, so their difference
`d_N := f(u_N) − f(0) ∈ D`, whence `res0 d_N = res1 d_N`.  It therefore suffices to
show `res1 d_N = 0` for `N` large.

The image of `u_N` in `Kt` is `π·(t+1)^N = t·(t+1)^{N+1}`, which is precisely
`ι(uN')` for the **polynomial** `uN' = X·(X+1)^{N+1} ∈ 𝔽₂[t]`.  Clearing the
denominator of `f.val` (`G/b`), let `E₁` be the multiplicity of the place `t = 1`
in `b`.  For `N ≥ E₁` the divisibility `(X+1)^{E₁+1} ∣ uN'` holds, so the
single-place comparison `place_eq` (copied from `CruxL.lean`) gives
`res1 (f(u_N)) = res1 (f(0))`.  Combined with the `D`-equalizer `res0 = res1` on
the two `Dom`-values, `res0 (d_N) = res1 (f(u_N)) − res1 (f(0)) = 0`, i.e.
`d_N ∈ 𝔪`.

Unlike the Stage-2.2 lemma `L` (the *fixed* order-`1` element `π`, needing genuine
two-place compatibility), `KEY` lets `N → ∞`, so a *one-place* (place-`t=1`)
estimate plus the `D`-equalizer suffices — **no compatibility lemma**, **no DVR /
valuation API** (only `res0`/`res1` + `𝔽₂[t]` divisibility +
`IsLocalization.integerNormalization`).
-/

open scoped nonZeroDivisors TensorProduct

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace Prob20.Proofs.Surjective

open Prob20 Polynomial
open Prob20.Proofs.Domain Prob20.Proofs.KeyObs

/-- **Single-place comparison** (copied from `CruxL.lean`, where it is `private`).
With `g` cleared to `G/b` (`G.map ι = C(ι b)·g`), a place `res` lifting an
evaluation `ev` (`res ∘ algebraMap = ev`), a factor `b = f^E · c` with `ev f = 0`
but `ev c ≠ 0`, and two points `w', z'` agreeing to order `> E` at the place
(`f^{E+1} ∣ w' − z'`): if `gw, gz : T` are the values `g(w'), g(z')`, then
`res gw = res gz`. -/
private theorem place_eq
    (g : Polynomial Kt) (G : Polynomial (Polynomial (ZMod 2))) (b : Polynomial (ZMod 2))
    (hGb : G.map (algebraMap (Polynomial (ZMod 2)) Kt)
        = Polynomial.C (algebraMap (Polynomial (ZMod 2)) Kt b) * g)
    (res : Tsub →+* ZMod 2) (ev : Polynomial (ZMod 2) →+* ZMod 2)
    (hev : ∀ x, res (algebraMap (Polynomial (ZMod 2)) Tsub x) = ev x)
    (f : Polynomial (ZMod 2)) (E : ℕ) (c : Polynomial (ZMod 2))
    (hbfc : b = f ^ E * c) (hfc : ev f = 0) (hcne : ev c ≠ 0) (hfne : f ≠ 0)
    (w' z' : Polynomial (ZMod 2)) (hdvd : f ^ (E + 1) ∣ (w' - z'))
    (gw gz : Tsub)
    (hgw : (gw : Kt) = g.eval (algebraMap (Polynomial (ZMod 2)) Kt w'))
    (hgz : (gz : Kt) = g.eval (algebraMap (Polynomial (ZMod 2)) Kt z')) :
    res gw = res gz := by
  have hιinj : Function.Injective (algebraMap (Polynomial (ZMod 2)) Kt) :=
    IsFractionRing.injective (Polynomial (ZMod 2)) Kt
  have hfK_ne : algebraMap (Polynomial (ZMod 2)) Kt f ≠ 0 := fun h =>
    hfne (hιinj (h.trans (map_zero _).symm))
  have emap : ∀ (y' : Polynomial (ZMod 2)) (gy : Tsub),
      (gy : Kt) = g.eval (algebraMap (Polynomial (ZMod 2)) Kt y') →
      algebraMap (Polynomial (ZMod 2)) Kt b * (gy : Kt)
        = algebraMap (Polynomial (ZMod 2)) Kt (G.eval y') := by
    intro y' gy hgy
    have hmap : (G.map (algebraMap (Polynomial (ZMod 2)) Kt)).eval
          (algebraMap (Polynomial (ZMod 2)) Kt y')
        = algebraMap (Polynomial (ZMod 2)) Kt (G.eval y') := by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom]
    have hmul : (G.map (algebraMap (Polynomial (ZMod 2)) Kt)).eval
          (algebraMap (Polynomial (ZMod 2)) Kt y')
        = algebraMap (Polynomial (ZMod 2)) Kt b * (gy : Kt) := by
      rw [hGb, Polynomial.eval_mul, Polynomial.eval_C, hgy]
    rw [← hmul, hmap]
  have e1 := emap w' gw hgw
  have e2 := emap z' gz hgz
  obtain ⟨Rq, hR⟩ := dvd_trans hdvd (Polynomial.sub_dvd_eval_sub w' z' G)
  have lhs : algebraMap (Polynomial (ZMod 2)) Kt b * ((gw : Kt) - (gz : Kt))
      = algebraMap (Polynomial (ZMod 2)) Kt (f ^ (E + 1) * Rq) := by
    rw [mul_sub, e1, e2, ← map_sub, hR]
  have key2 : algebraMap (Polynomial (ZMod 2)) Kt f ^ E
        * (algebraMap (Polynomial (ZMod 2)) Kt c * ((gw : Kt) - (gz : Kt)))
      = algebraMap (Polynomial (ZMod 2)) Kt f ^ E
        * (algebraMap (Polynomial (ZMod 2)) Kt f * algebraMap (Polynomial (ZMod 2)) Kt Rq) := by
    have hb_eq : algebraMap (Polynomial (ZMod 2)) Kt b
        = algebraMap (Polynomial (ZMod 2)) Kt f ^ E * algebraMap (Polynomial (ZMod 2)) Kt c := by
      rw [hbfc, map_mul, map_pow]
    have hfR_eq : algebraMap (Polynomial (ZMod 2)) Kt (f ^ (E + 1) * Rq)
        = algebraMap (Polynomial (ZMod 2)) Kt f ^ E
          * (algebraMap (Polynomial (ZMod 2)) Kt f * algebraMap (Polynomial (ZMod 2)) Kt Rq) := by
      rw [map_mul, map_pow]; ring
    rw [← hfR_eq, ← lhs, hb_eq]; ring
  have cancellation : algebraMap (Polynomial (ZMod 2)) Kt c * ((gw : Kt) - (gz : Kt))
      = algebraMap (Polynomial (ZMod 2)) Kt (f * Rq) := by
    rw [map_mul]
    exact mul_left_cancel₀ (pow_ne_zero E hfK_ne) key2
  have htower : ∀ x : Polynomial (ZMod 2),
      ((algebraMap (Polynomial (ZMod 2)) Tsub x : Tsub) : Kt)
        = algebraMap (Polynomial (ZMod 2)) Kt x :=
    fun x => (IsScalarTower.algebraMap_apply (Polynomial (ZMod 2)) Tsub Kt x).symm
  have hT : algebraMap (Polynomial (ZMod 2)) Tsub c * gw
      = algebraMap (Polynomial (ZMod 2)) Tsub c * gz
        + algebraMap (Polynomial (ZMod 2)) Tsub (f * Rq) := by
    apply Subtype.coe_injective
    simp only [Subalgebra.coe_mul, Subalgebra.coe_add, htower]
    linear_combination cancellation
  have hres := congrArg res hT
  rw [map_mul, map_add, map_mul, hev c, hev (f * Rq), map_mul, hfc, zero_mul, add_zero] at hres
  exact mul_left_cancel₀ hcne hres

/-- **The crux lemma `KEY`, unconditionally.**  For every `f ∈ Int(D)` there is an
`N₀` such that for all `N ≥ N₀`, `f(u_N) − f(0) ∈ 𝔪` (with `u_N = π(t+1)^N`). -/
theorem KEY_proof :
    ∀ f : ↥(IntPoly Dom Kt), ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      ∃ w : Dom, w ∈ mIdeal ∧ algebraMap Dom Kt w
        = Polynomial.aeval (algebraMap Dom Kt (uN N)) ((f : Polynomial Kt))
            - Polynomial.aeval (0 : Kt) ((f : Polynomial Kt)) := by
  intro f
  set g : Polynomial Kt := (f : Polynomial Kt) with hg
  have hmem : ∀ d : Dom,
      Polynomial.aeval (algebraMap Dom Kt d) g ∈ (algebraMap Dom Kt).range := f.2
  -- clear denominators: `G.map ι = C(ι b) · g`
  obtain ⟨b, hbM, hGb0⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors (Polynomial (ZMod 2))) g
  set G : Polynomial (Polynomial (ZMod 2)) :=
    IsLocalization.integerNormalization (nonZeroDivisors (Polynomial (ZMod 2))) g with hG
  have hb_ne : b ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hbM
  have hsmul : (b • g) = Polynomial.C (algebraMap (Polynomial (ZMod 2)) Kt b) * g := by
    rw [Algebra.smul_def,
      IsScalarTower.algebraMap_apply (Polynomial (ZMod 2)) Kt (Polynomial Kt) b,
      Polynomial.algebraMap_eq]
  have hGb : G.map (algebraMap (Polynomial (ZMod 2)) Kt)
      = Polynomial.C (algebraMap (Polynomial (ZMod 2)) Kt b) * g := hGb0.trans hsmul
  -- multiplicity of the place `t = 1` in `b`
  set E1 := Polynomial.rootMultiplicity 1 b with hE1
  obtain ⟨c1, hc1⟩ : (Polynomial.X + 1 : Polynomial (ZMod 2)) ^ E1 ∣ b := by
    have h := Polynomial.pow_rootMultiplicity_dvd b 1
    rwa [show (Polynomial.X - Polynomial.C (1 : ZMod 2)) = (Polynomial.X + 1) by
      rw [CharTwo.sub_eq_add, Polynomial.C_1]] at h
  have hc1ne : Polynomial.eval 1 c1 ≠ 0 := by
    intro hcontra
    have hX1c1 : (Polynomial.X + 1 : Polynomial (ZMod 2)) ∣ c1 := by
      have hroot : c1.IsRoot 1 := hcontra
      have hdvd' : (Polynomial.X - Polynomial.C (1 : ZMod 2)) ∣ c1 :=
        Polynomial.dvd_iff_isRoot.mpr hroot
      rwa [show (Polynomial.X - Polynomial.C (1 : ZMod 2)) = (Polynomial.X + 1) by
        rw [CharTwo.sub_eq_add, Polynomial.C_1]] at hdvd'
    obtain ⟨c1', hc1'⟩ := hX1c1
    have hdvd2 : (Polynomial.X + 1 : Polynomial (ZMod 2)) ^ (E1 + 1) ∣ b :=
      ⟨c1', by rw [hc1, hc1']; ring⟩
    have hnot := Polynomial.pow_rootMultiplicity_not_dvd hb_ne 1
    rw [show (Polynomial.X - Polynomial.C (1 : ZMod 2)) = (Polynomial.X + 1) by
      rw [CharTwo.sub_eq_add, Polynomial.C_1]] at hnot
    exact hnot hdvd2
  have hX1ne : (Polynomial.X + 1 : Polynomial (ZMod 2)) ≠ 0 := by
    intro h
    have hc := congrArg (fun p => Polynomial.coeff p 1) h
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_one, Polynomial.coeff_one,
      Polynomial.coeff_zero] at hc
    revert hc; decide
  -- `N₀ := E1`
  refine ⟨E1, fun N hN => ?_⟩
  -- the witness polynomial `uN' = X · (X+1)^{N+1}`, with `ι(uN') = π·(t+1)^N`
  set uN' : Polynomial (ZMod 2) := Polynomial.X * (Polynomial.X + 1) ^ (N + 1) with huN'
  have hX : algebraMap (Polynomial (ZMod 2)) Kt Polynomial.X = tElt := by
    rw [tElt]; exact RatFunc.algebraMap_X
  have huNimg : algebraMap Dom Kt (uN N) = algebraMap (Polynomial (ZMod 2)) Kt uN' := by
    rw [uK_eq, huN', map_mul, map_pow, map_add, map_one, hX, piElt]
    ring
  -- divisibility `(X+1)^{E1+1} ∣ (uN' − 0)` since `E1 + 1 ≤ N + 1`
  have hdvd : (Polynomial.X + 1 : Polynomial (ZMod 2)) ^ (E1 + 1) ∣ (uN' - 0) := by
    rw [sub_zero, huN']
    exact dvd_mul_of_dvd_right (pow_dvd_pow _ (by omega)) Polynomial.X
  -- range witnesses for `f(u_N)` and `f(0)`
  obtain ⟨wuN, hwuN⟩ := hmem (uN N)
  obtain ⟨w0, hw0⟩ := hmem 0
  -- value identifications in `Kt`
  have hgw_uN : ((wuN : Tsub) : Kt) = g.eval (algebraMap (Polynomial (ZMod 2)) Kt uN') := by
    rw [← domToKt_eq, hwuN, huNimg]
    exact congrFun (Polynomial.coe_aeval_eq_eval (algebraMap (Polynomial (ZMod 2)) Kt uN')) g
  have hgz_0 : ((w0 : Tsub) : Kt)
      = g.eval (algebraMap (Polynomial (ZMod 2)) Kt (0 : Polynomial (ZMod 2))) := by
    rw [map_zero, ← domToKt_eq, hw0, map_zero]
    exact congrFun (Polynomial.coe_aeval_eq_eval (0 : Kt)) g
  -- place-1 comparison: `res1 (f(u_N)) = res1 (f(0))`
  have place1 : res1 (wuN : Tsub) = res1 (w0 : Tsub) :=
    place_eq g G b hGb res1 eval1 (fun x => IsLocalization.lift_eq hu1 x)
      (Polynomial.X + 1) E1 c1 hc1
      (by simp only [eval1, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_X,
            Polynomial.eval_one]; decide)
      hc1ne hX1ne uN' 0 hdvd (wuN : Tsub) (w0 : Tsub) hgw_uN hgz_0
  -- conclude `w := wuN − w0 ∈ 𝔪` (via the `Dom`-equalizer) and the value identity
  refine ⟨wuN - w0, ?_, ?_⟩
  · rw [mIdeal, RingHom.mem_ker, map_sub]
    show res0 (wuN : Tsub) - res0 (w0 : Tsub) = 0
    rw [wuN.2, w0.2, place1, sub_self]
  · have hval : algebraMap Dom Kt (wuN - w0)
        = Polynomial.aeval (algebraMap Dom Kt (uN N)) g
          - Polynomial.aeval (algebraMap Dom Kt (0 : Dom)) g := by
      rw [map_sub, hwuN, hw0]
    rw [hval, map_zero]

/-- **`theta2_missing`, unconditionally.**  `PMv = g(XY) ∈ Int(D²)` but
`PMv ∉ im θ₂`.  The frozen statement, with `KEY` now discharged. -/
theorem theta2_missing_proof :
    PMv ∈ IntPolyN Dom Kt 2 ∧ PMv ∉ Set.range (thetaN Dom Kt 2) :=
  theta2_missing_of_KEY KEY_proof

end Prob20.Proofs.Surjective
