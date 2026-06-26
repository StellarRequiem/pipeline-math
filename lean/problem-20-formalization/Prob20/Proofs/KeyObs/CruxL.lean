import Prob20.Defs
import Prob20.Theorems
import Prob20.Proofs.Domain.FractionField
import Prob20.Proofs.KeyObs.KeyMembership
import Prob20.Proofs.KeyObs.Valuation

/-!
# Stage 2.2 — the crux lemma `L`, proved **unconditionally**

This file discharges the single remaining gap of Stage 2.2 (see `LinIndep.lean`,
`Valuation.lean`, and the `PROGRESS.md` entries): the place-order lemma

> `L : ∀ g ∈ Int(D), g(π) − g(0) ∈ ι(𝔪)`   (i.e. `resD (g(π)) = resD (g(0))`).

`L` is true for the **two-place** pullback `D = 𝔽₂ + 𝔪` (places `t = 0`, `t = 1`),
even though its single-place analogue is false (the `(X²+X)/t` binomial
obstruction).  The proof here is elementary — it uses only `res0`/`res1`,
polynomial divisibility in `𝔽₂[t]`, and the clearing of denominators
(`IsLocalization.integerNormalization`); **no DVR / valuation API.**

## The argument

For `g ∈ Int(D)` clear denominators: `G : 𝔽₂[t][X]`, `b : 𝔽₂[t]` with
`G.map ι = C(ι b) · g`.  Let `E₀, E₁` be the multiplicities of `t`, `t+1` in `b`
and `M₀ = E₀+1`, `M₁ = E₁+1`.  By CRT pick `d' ∈ 𝔽₂[t]` with
`d' ≡ π mod t^{M₀}` and `d' ≡ 0 mod (t+1)^{M₁}` (so `d := ι d' ∈ 𝔪 ⊆ D`).
The single-place comparison

* `res0 (g d) = res0 (g π)`  (because `d ≡ π` to order `> E₀` at `t = 0`)
* `res1 (g d) = res1 (g 0)`  (because `d ≡ 0` to order `> E₁` at `t = 1`)

is the lemma `place_eq` below.  Its proof: `ι b · (g d − g π) = ι(G d' − G π')`,
the divided difference `t^{M₀} ∣ (G d' − G π')`, cancel `ι(t^{E₀})` from
`b = t^{E₀}·c` (`c(0) ≠ 0`), then apply the ring hom `res0` and use that
`c(0) ≠ 0` in the field `𝔽₂`.  Chaining with the *output* condition
`res0 (g d) = res1 (g d)` (as `g d ∈ D`):

`res0(gπ) = res0(gd) = res1(gd) = res1(g0) = res0(g0)`,

so `g(π) − g(0) ∈ 𝔪`.
-/

open scoped nonZeroDivisors

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace Prob20.Proofs.KeyObs

open Prob20 Polynomial
open Prob20.Proofs.Domain

/-- **Single-place comparison.**  With `g` cleared to `G/b` (`G.map ι = C(ι b)·g`),
a place `res` lifting an evaluation `ev` (`res ∘ algebraMap = ev`), a factor
`b = f^E · c` with `ev f = 0` but `ev c ≠ 0`, and two points `w', z'` agreeing to
order `> E` at the place (`f^{E+1} ∣ w' − z'`): if `gw, gz : T` are the values
`g(w'), g(z')`, then `res gw = res gz`. -/
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
  -- `ι b · g(y') = ι (G y')`
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
  -- divided difference: `f^{E+1} ∣ (G w' − G z')`
  obtain ⟨Rq, hR⟩ := dvd_trans hdvd (Polynomial.sub_dvd_eval_sub w' z' G)
  have lhs : algebraMap (Polynomial (ZMod 2)) Kt b * ((gw : Kt) - (gz : Kt))
      = algebraMap (Polynomial (ZMod 2)) Kt (f ^ (E + 1) * Rq) := by
    rw [mul_sub, e1, e2, ← map_sub, hR]
  -- cancel `ι(f^E)`
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
  -- transfer to `T` and apply the place `res`
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

/-- **The crux lemma `L`, unconditionally.**  For every `g ∈ Int(D)`,
`g(π) − g(0) ∈ ι(𝔪)`: there is `w ∈ 𝔪` with `ι w = aeval piK g − aeval 0 g`. -/
theorem L_proof :
    ∀ n : ↥(IntPoly Dom Kt), ∃ w : Dom, w ∈ mIdeal ∧
      algebraMap Dom Kt w =
        Polynomial.aeval piK (n : Polynomial Kt)
          - Polynomial.aeval (0 : Kt) (n : Polynomial Kt) := by
  intro n
  set g : Polynomial Kt := (n : Polynomial Kt) with hg
  have hmem : ∀ d : Dom,
      Polynomial.aeval (algebraMap Dom Kt d) g ∈ (algebraMap Dom Kt).range := n.2
  -- clear denominators
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
  -- the multiplicities of the two places in `b`
  set E0 := Polynomial.rootMultiplicity 0 b with hE0
  set E1 := Polynomial.rootMultiplicity 1 b with hE1
  -- `b = X^{E0} · c0` with `c0(0) ≠ 0`
  obtain ⟨c0, hc0⟩ : (Polynomial.X : Polynomial (ZMod 2)) ^ E0 ∣ b := by
    have h := Polynomial.pow_rootMultiplicity_dvd b 0
    rwa [Polynomial.C_0, sub_zero] at h
  have hc0ne : Polynomial.eval 0 c0 ≠ 0 := by
    intro hcontra
    have hXc0 : (Polynomial.X : Polynomial (ZMod 2)) ∣ c0 := by
      rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]; exact hcontra
    obtain ⟨c0', hc0'⟩ := hXc0
    have hdvd2 : (Polynomial.X : Polynomial (ZMod 2)) ^ (E0 + 1) ∣ b :=
      ⟨c0', by rw [hc0, hc0']; ring⟩
    have hnot := Polynomial.pow_rootMultiplicity_not_dvd hb_ne 0
    rw [Polynomial.C_0, sub_zero] at hnot
    exact hnot hdvd2
  -- `b = (X+1)^{E1} · c1` with `c1(1) ≠ 0`
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
  -- CRT: a point `d'` with `d' ≡ π mod X^{E0+1}` and `d' ≡ 0 mod (X+1)^{E1+1}`
  have hcop : IsCoprime ((Polynomial.X : Polynomial (ZMod 2)) ^ (E0 + 1))
      ((Polynomial.X + 1) ^ (E1 + 1)) := by
    have hc : IsCoprime (Polynomial.X : Polynomial (ZMod 2)) (Polynomial.X + 1) := by
      have h := Polynomial.isCoprime_X_sub_C_of_isUnit_sub (R := ZMod 2) (a := 0) (b := 1)
        (by rw [show ((0 : ZMod 2) - 1) = 1 by decide]; exact isUnit_one)
      rwa [show (Polynomial.X - Polynomial.C (0 : ZMod 2)) = Polynomial.X by
            rw [Polynomial.C_0, sub_zero],
          show (Polynomial.X - Polynomial.C (1 : ZMod 2)) = (Polynomial.X + 1) by
            rw [CharTwo.sub_eq_add, Polynomial.C_1]] at h
    exact hc.pow
  obtain ⟨u, v, huv⟩ := hcop
  set pi' : Polynomial (ZMod 2) := Polynomial.X * (Polynomial.X + 1) with hpi'
  set d' : Polynomial (ZMod 2) := pi' * v * (Polynomial.X + 1) ^ (E1 + 1) with hd'
  -- divisibilities
  have hd0 : (Polynomial.X : Polynomial (ZMod 2)) ^ (E0 + 1) ∣ (d' - pi') := by
    refine ⟨-(pi' * u), ?_⟩
    have hvb : v * (Polynomial.X + 1) ^ (E1 + 1)
        = 1 - u * Polynomial.X ^ (E0 + 1) := by linear_combination huv
    rw [hd']
    calc pi' * v * (Polynomial.X + 1) ^ (E1 + 1) - pi'
        = pi' * (v * (Polynomial.X + 1) ^ (E1 + 1)) - pi' := by ring
      _ = pi' * (1 - u * Polynomial.X ^ (E0 + 1)) - pi' := by rw [hvb]
      _ = Polynomial.X ^ (E0 + 1) * (-(pi' * u)) := by ring
  have hd1 : (Polynomial.X + 1 : Polynomial (ZMod 2)) ^ (E1 + 1) ∣ (d' - 0) := by
    rw [sub_zero, hd']; exact ⟨pi' * v, by ring⟩
  -- `d'` evaluates to `0` at both places, so `d := ι d' ∈ 𝔪 ⊆ D`
  have hev0_d' : Polynomial.eval 0 d' = 0 := by
    rw [hd', hpi']; simp
  have hev1_d' : Polynomial.eval 1 d' = 0 := by
    rw [hd']
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one]
    rw [show (1 + 1 : ZMod 2) = 0 by decide, zero_pow (Nat.succ_ne_zero E1), mul_zero]
  have e0d : res0 (algebraMap (Polynomial (ZMod 2)) Tsub d') = Polynomial.eval 0 d' :=
    IsLocalization.lift_eq hu0 d'
  have e1d : res1 (algebraMap (Polynomial (ZMod 2)) Tsub d') = Polynomial.eval 1 d' :=
    IsLocalization.lift_eq hu1 d'
  have hd'_mem : (algebraMap (Polynomial (ZMod 2)) Tsub d') ∈ Dsub := by
    rw [Dsub, RingHom.mem_eqLocus, e0d, e1d, hev0_d', hev1_d']
  set dDom : Dom := ⟨algebraMap (Polynomial (ZMod 2)) Tsub d', hd'_mem⟩ with hdDom
  have hdDom_mem : dDom ∈ mIdeal := by
    rw [mIdeal, RingHom.mem_ker]
    show res0 (algebraMap (Polynomial (ZMod 2)) Tsub d') = 0
    rw [e0d, hev0_d']
  -- the three integer-valued witnesses
  obtain ⟨wπ, hwπ⟩ := hmem piD
  obtain ⟨w0, hw0⟩ := hmem 0
  obtain ⟨wd, hwd⟩ := hmem dDom
  -- value identifications
  have haeval_d : Polynomial.aeval (algebraMap Dom Kt dDom) g
      = g.eval (algebraMap (Polynomial (ZMod 2)) Kt d') := by
    have h3 : algebraMap Dom Kt dDom = algebraMap (Polynomial (ZMod 2)) Kt d' := by
      rw [domToKt_eq]
      show ((algebraMap (Polynomial (ZMod 2)) Tsub d' : Tsub) : Kt)
        = algebraMap (Polynomial (ZMod 2)) Kt d'
      exact (IsScalarTower.algebraMap_apply (Polynomial (ZMod 2)) Tsub Kt d').symm
    rw [congrFun (Polynomial.coe_aeval_eq_eval (algebraMap Dom Kt dDom)) g, h3]
  have haeval_pi : Polynomial.aeval (algebraMap Dom Kt piD) g
      = g.eval (algebraMap (Polynomial (ZMod 2)) Kt pi') := by
    have h2 : algebraMap Dom Kt piD = algebraMap (Polynomial (ZMod 2)) Kt pi' := by
      have h1 : algebraMap Dom Kt piD = (piTsub : Kt) := piK_eq
      rw [h1, hpi']
      show ((algebraMap (Polynomial (ZMod 2)) Tsub (Polynomial.X * (Polynomial.X + 1)) : Tsub) : Kt)
        = algebraMap (Polynomial (ZMod 2)) Kt (Polynomial.X * (Polynomial.X + 1))
      exact (IsScalarTower.algebraMap_apply (Polynomial (ZMod 2)) Tsub Kt _).symm
    rw [congrFun (Polynomial.coe_aeval_eq_eval (algebraMap Dom Kt piD)) g, h2]
  -- the `T`-values and their place residues
  have hgw_d : ((wd : Tsub) : Kt) = g.eval (algebraMap (Polynomial (ZMod 2)) Kt d') := by
    rw [← domToKt_eq, hwd]; exact haeval_d
  have hgz_pi : ((wπ : Tsub) : Kt) = g.eval (algebraMap (Polynomial (ZMod 2)) Kt pi') := by
    rw [← domToKt_eq, hwπ]; exact haeval_pi
  have hgz_0 : ((w0 : Tsub) : Kt)
      = g.eval (algebraMap (Polynomial (ZMod 2)) Kt (0 : Polynomial (ZMod 2))) := by
    rw [map_zero, ← domToKt_eq, hw0, map_zero]
    exact congrFun (Polynomial.coe_aeval_eq_eval (0 : Kt)) g
  have place0 : res0 (wd : Tsub) = res0 (wπ : Tsub) :=
    place_eq g G b hGb res0 eval0 (fun x => IsLocalization.lift_eq hu0 x)
      Polynomial.X E0 c0 hc0
      (by simp only [eval0, Polynomial.coe_evalRingHom, Polynomial.eval_X])
      hc0ne Polynomial.X_ne_zero d' pi' hd0 (wd : Tsub) (wπ : Tsub) hgw_d hgz_pi
  have hX1ne : (Polynomial.X + 1 : Polynomial (ZMod 2)) ≠ 0 := by
    intro h
    have hc := congrArg (fun p => Polynomial.coeff p 1) h
    simp only [Polynomial.coeff_add, Polynomial.coeff_X_one, Polynomial.coeff_one,
      Polynomial.coeff_zero] at hc
    revert hc; decide
  have place1 : res1 (wd : Tsub) = res1 (w0 : Tsub) :=
    place_eq g G b hGb res1 eval1 (fun x => IsLocalization.lift_eq hu1 x)
      (Polynomial.X + 1) E1 c1 hc1
      (by simp only [eval1, Polynomial.coe_evalRingHom, Polynomial.eval_add, Polynomial.eval_X,
            Polynomial.eval_one]; decide)
      hc1ne hX1ne d' 0 hd1 (wd : Tsub) (w0 : Tsub) hgw_d hgz_0
  -- chain the residues using the output condition `g d ∈ D`
  have hwd_dom : res0 (wd : Tsub) = res1 (wd : Tsub) := wd.2
  have hw0_dom : res0 (w0 : Tsub) = res1 (w0 : Tsub) := w0.2
  have hchain : res0 (wπ : Tsub) = res0 (w0 : Tsub) := by
    rw [← place0, hwd_dom, place1, hw0_dom]
  have hresD : resD wπ = resD w0 := by
    show res0 (wπ : Tsub) = res0 (w0 : Tsub)
    exact hchain
  refine ⟨wπ - w0, ?_, ?_⟩
  · rw [mIdeal, RingHom.mem_ker, map_sub, hresD, sub_self]
  · have hval : algebraMap Dom Kt (wπ - w0)
        = Polynomial.aeval (algebraMap Dom Kt piD) g
          - Polynomial.aeval (algebraMap Dom Kt (0 : Dom)) g := by
      rw [map_sub, hwπ, hw0]
    rw [hval, map_zero]
    rfl

end Prob20.Proofs.KeyObs
