import Prob20.Defs

/-!
# Theorems.lean — FROZEN statements for the Problem 20 counterexample

The **ten** theorem statements, each `:= sorry`. Each renders a claim of
`SKETCH.md` minimally and faithfully (see `BLUEPRINT.md` Part −1 §3). After
SETUP these statements are byte-frozen (pinned in `scripts/frozen.sha256`); the
proofs live in `Prob20/Proofs/**` and are exposed, with the exact frozen types,
as `Prob20.Solution.<name>` (`Solution.lean`) and machine-checked for no drift by
`Discharge.lean`.

`sorry` is permitted **only** in this file.
-/

open scoped TensorProduct

namespace Prob20

/-! ## Stage 1 — the counterexample domain -/

/-- `D/𝔪 ≅ 𝔽₂`: the residue field of the conductor pullback is `𝔽₂`. -/
theorem D_residue_field : Nonempty (Dom ⧸ mIdeal ≃+* ZMod 2) := sorry

/-- `Frac(D) = 𝔽₂(t)`: `Kt` is the fraction field of `Dom`. -/
theorem D_fraction_field : IsFractionRing Dom Kt := sorry

/-! ## Stage 2 — the Key Observation -/

/-- `p, tp, (t+1)p ∈ Int(D)`. -/
theorem key_membership :
    pPoly ∈ IntPoly Dom Kt ∧ tpPoly ∈ IntPoly Dom Kt ∧ t1pPoly ∈ IntPoly Dom Kt := sorry

/-- `p̄, t̄p̄` are `𝔽₂`-linearly independent in `Int(D)/𝔪·Int(D)`: any nontrivial
`𝔽₂`-combination `a·p + b·tp` lands in `𝔪·Int(D)` only if `a = b = 0`. -/
theorem p_tp_linindep :
    ∀ a b : ZMod 2,
      Polynomial.C (algebraMap (ZMod 2) Kt a) * pPoly
        + Polynomial.C (algebraMap (ZMod 2) Kt b) * tpPoly ∈ mIntPoly →
      a = 0 ∧ b = 0 := sorry

/-! ## Stage 3 — failure of injectivity -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- The explicit nonzero kernel element `τ = (tp)⊗p − p⊗(tp)` of `θ₂`. -/
theorem theta2_kernel :
    ∃ τ : ⨂[Dom] (_ : Fin 2), IntPoly Dom Kt,
      τ ≠ 0 ∧ thetaN Dom Kt 2 τ = 0 := sorry

/-- `θₙ` is not injective for any `n ≥ 2`. -/
theorem thetaN_not_injective :
    ∀ n : ℕ, 2 ≤ n → ¬ Function.Injective (thetaN Dom Kt n) := sorry

/-! ## Stage 4 — failure of surjectivity -/

/-- `g ∈ Int(D)`. -/
theorem g_mem : gPoly ∈ IntPoly Dom Kt := sorry

/-- `P = g(XY) ∈ Int(D²)` but `P ∉ im θ₂`. -/
theorem theta2_missing :
    PMv ∈ IntPolyN Dom Kt 2 ∧ PMv ∉ Set.range (thetaN Dom Kt 2) := sorry

/-- `θₙ` is not surjective onto `Int(Dⁿ)` for any `n ≥ 2`. -/
theorem thetaN_not_surjective :
    ∀ n : ℕ, 2 ≤ n →
      ¬ ((IntPolyN Dom Kt n : Set (MvPolynomial (Fin n) Kt))
            ⊆ Set.range (thetaN Dom Kt n)) := sorry

/-! ## Headline — the answer to Problem 20 -/

/-- **Problem 20, answered.** There exists an integral domain `D` with fraction
field `K` whose canonical map `θ₂` is **neither injective nor surjective**. -/
theorem problem20_answer :
    ∃ (D K : Type) (_ : CommRing D) (_ : IsDomain D) (_ : Field K)
      (_ : Algebra D K) (_ : IsFractionRing D K),
      ¬ Function.Injective (thetaN D K 2) ∧
      ¬ ((IntPolyN D K 2 : Set (MvPolynomial (Fin 2) K)) ⊆ Set.range (thetaN D K 2)) := sorry

end Prob20
