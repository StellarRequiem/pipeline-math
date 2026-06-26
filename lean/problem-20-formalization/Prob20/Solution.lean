import Prob20.Proofs.Domain.Basic
import Prob20.Proofs.KeyObs.Basic
import Prob20.Proofs.Injective.Basic
import Prob20.Proofs.Surjective.Basic
import Prob20.Proofs.Headline.Basic

/-!
# Solution.lean — clean, named restatements of the ten frozen theorems

During the proving phase, each frozen theorem of `Prob20/Theorems.lean` is
restated **verbatim** here in `namespace Prob20.Solution` and proved by the
sorry-free declaration from `Prob20/Proofs/**` (`:= <name>_proof`). `verify.sh`
checks that `#print axioms Prob20.Solution.<name>` is clean (only `propext`,
`Classical.choice`, `Quot.sound`) for all ten names.

SETUP-stage placeholder: no proofs are exposed yet (the frozen statements are
still `sorry`), so this module is intentionally empty apart from its namespace.
The ten `Prob20.Solution.<name>` declarations are added here once the
corresponding `Proofs/**` proofs land.
-/

open scoped TensorProduct

namespace Prob20.Solution

/-! ## Stage 1 — the counterexample domain -/

/-- `D/𝔪 ≅ 𝔽₂`: the residue field of the conductor pullback is `𝔽₂`. -/
theorem D_residue_field : Nonempty (Dom ⧸ mIdeal ≃+* ZMod 2) :=
  Prob20.Proofs.Domain.D_residue_field_proof

/-- `Frac(D) = 𝔽₂(t)`: `Kt` is the fraction field of `Dom`. -/
theorem D_fraction_field : IsFractionRing Dom Kt :=
  Prob20.Proofs.Domain.D_fraction_field_proof

/-! ## Stage 2 — the Key Observation -/

/-- `p, tp, (t+1)p ∈ Int(D)`: the three integer-valued polynomials. -/
theorem key_membership :
    pPoly ∈ IntPoly Dom Kt ∧ tpPoly ∈ IntPoly Dom Kt ∧ t1pPoly ∈ IntPoly Dom Kt :=
  Prob20.Proofs.KeyObs.key_membership_proof

/-- `p̄, t̄p̄` are `𝔽₂`-linearly independent in `Int(D)/𝔪·Int(D)`. -/
theorem p_tp_linindep :
    ∀ a b : ZMod 2,
      Polynomial.C (algebraMap (ZMod 2) Kt a) * pPoly
        + Polynomial.C (algebraMap (ZMod 2) Kt b) * tpPoly ∈ mIntPoly →
      a = 0 ∧ b = 0 :=
  Prob20.Proofs.KeyObs.p_tp_linindep_proof

/-! ## Stage 3 — failure of injectivity -/

set_option synthInstance.maxHeartbeats 1000000 in
/-- The explicit nonzero kernel element `τ = (tp)⊗p − p⊗(tp)` of `θ₂`. -/
theorem theta2_kernel :
    ∃ τ : ⨂[Dom] (_ : Fin 2), IntPoly Dom Kt,
      τ ≠ 0 ∧ thetaN Dom Kt 2 τ = 0 :=
  Prob20.Proofs.Injective.theta2_kernel_proof

/-- `θₙ` is not injective for any `n ≥ 2`. -/
theorem thetaN_not_injective :
    ∀ n : ℕ, 2 ≤ n → ¬ Function.Injective (thetaN Dom Kt n) :=
  Prob20.Proofs.Injective.thetaN_not_injective_proof

/-! ## Stage 4 — failure of surjectivity -/

/-- `g = q² + q ∈ Int(D)`: the integer-valued polynomial behind the missing element. -/
theorem g_mem : gPoly ∈ IntPoly Dom Kt :=
  Prob20.Proofs.Surjective.g_mem_proof

/-- `P = g(XY) ∈ Int(D²)` but `P ∉ im θ₂`. -/
theorem theta2_missing :
    PMv ∈ IntPolyN Dom Kt 2 ∧ PMv ∉ Set.range (thetaN Dom Kt 2) :=
  Prob20.Proofs.Surjective.theta2_missing_proof

/-- `θₙ` is not surjective onto `Int(Dⁿ)` for any `n ≥ 2`. -/
theorem thetaN_not_surjective :
    ∀ n : ℕ, 2 ≤ n →
      ¬ ((IntPolyN Dom Kt n : Set (MvPolynomial (Fin n) Kt))
            ⊆ Set.range (thetaN Dom Kt n)) :=
  Prob20.Proofs.Surjective.thetaN_not_surjective_proof

/-! ## Headline — the answer to Problem 20 -/

/-- **Problem 20, answered.** There exists an integral domain `D` with fraction
field `K` whose canonical map `θ₂` is **neither injective nor surjective**. -/
theorem problem20_answer :
    ∃ (D K : Type) (_ : CommRing D) (_ : IsDomain D) (_ : Field K)
      (_ : Algebra D K) (_ : IsFractionRing D K),
      ¬ Function.Injective (thetaN D K 2) ∧
      ¬ ((IntPolyN D K 2 : Set (MvPolynomial (Fin 2) K)) ⊆ Set.range (thetaN D K 2)) :=
  Prob20.Proofs.Headline.problem20_answer_proof

end Prob20.Solution
