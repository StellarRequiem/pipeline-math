import Prob20.Defs
import Prob20.Theorems

/-!
# Stage 2.1 — the Key Observation memberships (`Proofs/KeyObs/KeyMembership.lean`)

We prove `key_membership` (frozen in `Prob20/Theorems.lean`): the three explicit
polynomials `p = X²+X`, `tp = t·p`, `(t+1)p = (t+1)·p` all lie in the genuine
integer-valued subalgebra `Int(D) = {f ∈ K[X] : ∀ d : D, f(ι d) ∈ ι(D)}`,
quantified over **all** `d : Dom`.

The argument (SKETCH *Key Observation*):

* For every `d : Dom`, `p(ι d) = (ι d)² + ι d = ι(d² + d)`, which is trivially in
  the range of `ι = algebraMap Dom Kt` — `Int(D)` always contains `D[X]`.
* Moreover `d² + d ∈ 𝔪 = ker resD`, because in the residue field `Dom/𝔪 ≅ 𝔽₂`
  every element satisfies `z² + z = 0` (`decide` over `ZMod 2`).
* `𝔪` is killed by both residues, so for any `c : Tsub` the product `c·(d²+d)`
  again lands in `Dsub = Dom` (`res0 = res1 = 0` on it). Hence `t·p(ι d)` and
  `(t+1)·p(ι d)` are in `ι(Dom)` too, using `t, t+1 ∈ Tsub`.

No point is sampled; everything is `∀ d : Dom`.
-/

open Prob20

namespace Prob20.Proofs.KeyObs

open Polynomial

/-- In `𝔽₂ = ZMod 2`, the Frobenius/`a²=a` identity gives `z² + z = 0`. -/
private theorem sq_add_self_zmod2 : ∀ z : ZMod 2, z ^ 2 + z = 0 := by decide

/-- For every `d : Dom`, the element `d² + d` lies in `𝔪 = ker resD`, because its
residue `resD(d²+d) = (resD d)² + resD d = 0` in `𝔽₂`. -/
theorem pd_mem (d : Dom) : (d ^ 2 + d : Dom) ∈ mIdeal := by
  rw [mIdeal, RingHom.mem_ker, map_add, map_pow]
  exact sq_add_self_zmod2 (resD d)

/-- The `D`-algebra map `Dom → Kt` is the composite `D ⊆ T ⊆ K`, so on elements it
is just the underlying coercion `Dom → Tsub → Kt`. -/
theorem domToKt_eq (x : Dom) : algebraMap Dom Kt x = ((x : Tsub) : Kt) := rfl

/-- **Key multiplicative closure.** For `c : Tsub` and `a : Dom` with `a ∈ 𝔪`, the
product `c · a` lifts back to an element of `Dom` whose image in `Kt` is
`(c : Kt) · (image of a)`. This is the engine behind `tp, (t+1)p ∈ Int(D)`:
multiplying a value in `𝔪` by any `T`-element stays in `Dom`. -/
theorem smul_m_mem_range (c : Tsub) (a : Dom) (ha : a ∈ mIdeal) :
    (c : Kt) * algebraMap Dom Kt a ∈ (algebraMap Dom Kt).range := by
  have h0 : res0 (a : Tsub) = 0 := RingHom.mem_ker.mp ha
  have ha2 : res0 (a : Tsub) = res1 (a : Tsub) := a.2
  have h1 : res1 (a : Tsub) = 0 := ha2.symm.trans h0
  refine ⟨⟨c * (a : Tsub), ?_⟩, ?_⟩
  · show res0 (c * (a : Tsub)) = res1 (c * (a : Tsub))
    rw [map_mul, map_mul, h0, h1, mul_zero, mul_zero]
  · show ((c * (a : Tsub) : Tsub) : Kt) = (c : Kt) * algebraMap Dom Kt a
    rw [domToKt_eq a, Subalgebra.coe_mul]

/-- `tElt = t = RatFunc.X` lies in the subalgebra `Tsub`: it is the image of the
polynomial `X` under `algebraMap 𝔽₂[t] Kt`. -/
theorem tElt_mem : tElt ∈ Tsub := by
  have h := Subalgebra.algebraMap_mem Tsub (Polynomial.X : Polynomial (ZMod 2))
  rwa [RatFunc.algebraMap_X] at h

/-- `t` packaged as an element of `Tsub`. -/
noncomputable def tT : Tsub := ⟨tElt, tElt_mem⟩

@[simp] theorem coe_tT : (tT : Kt) = tElt := rfl

/-- For any `c : Tsub`, the polynomial `C (c:Kt) · p = c·(X²+X)` is integer-valued:
at every `d`, its value is `(c:Kt)·(d²+d)`, the image of an element of `Dom`. -/
theorem cp_mem (c : Tsub) : (Polynomial.C (c : Kt) * pPoly) ∈ IntPoly Dom Kt := by
  intro d
  have h : aeval (algebraMap Dom Kt d) (Polynomial.C (c : Kt) * pPoly)
      = (c : Kt) * algebraMap Dom Kt (d ^ 2 + d) := by
    simp only [pPoly, map_mul, map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_self_apply]
  rw [h]
  exact smul_m_mem_range c (d ^ 2 + d) (pd_mem d)

/-- **`key_membership`.** `p, tp, (t+1)p ∈ Int(D)`. -/
theorem key_membership_proof :
    pPoly ∈ IntPoly Dom Kt ∧ tpPoly ∈ IntPoly Dom Kt ∧ t1pPoly ∈ IntPoly Dom Kt := by
  refine ⟨?_, ?_, ?_⟩
  · -- p = X²+X: at every d, value is ι(d²+d), trivially in range
    intro d
    refine ⟨d ^ 2 + d, ?_⟩
    simp only [pPoly, map_add, map_pow, Polynomial.aeval_X]
  · -- tp = C t · p
    show Polynomial.C tElt * pPoly ∈ IntPoly Dom Kt
    have := cp_mem tT
    rwa [coe_tT] at this
  · -- (t+1)p = C (t+1) · p
    show Polynomial.C (tElt + 1) * pPoly ∈ IntPoly Dom Kt
    have hc : (tElt + 1 : Kt) = ((tT + 1 : Tsub) : Kt) := by
      rw [Subalgebra.coe_add, Subalgebra.coe_one, coe_tT]
    rw [hc]
    exact cp_mem (tT + 1)

end Prob20.Proofs.KeyObs
