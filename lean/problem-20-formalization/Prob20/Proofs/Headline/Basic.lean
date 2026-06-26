import Prob20.Defs
import Prob20.Theorems
import Prob20.Proofs.Injective.Amplify
import Prob20.Proofs.Surjective.Place1
import Prob20.Proofs.Domain.FractionField

/-!
# Stage 5 — the answer to Problem 20 (`Proofs/Headline/`)

The Stage 5 support proof (SKETCH *Conclusion*): `problem20_answer`, assembled
from the `n = 2` milestones `thetaN_not_injective` / `theta2_missing` together
with `D_fraction_field` (`IsFractionRing Dom Kt`).

The frozen statement lives in `Prob20/Theorems.lean`; this file produces the
sorry-free proof term `problem20_answer_proof` with EXACTLY the frozen type, and
it is re-exposed in `Prob20/Solution.lean`.
-/

open scoped TensorProduct

namespace Prob20.Proofs.Headline

set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 1000000 in
/-- **Problem 20, answered.** Witnessed by the concrete domain `Dom` with fraction
field `Kt = 𝔽₂(t)`: its canonical map `θ₂` is neither injective nor surjective. -/
theorem problem20_answer_proof :
    ∃ (D K : Type) (_ : CommRing D) (_ : IsDomain D) (_ : Field K)
      (_ : Algebra D K) (_ : IsFractionRing D K),
      ¬ Function.Injective (thetaN D K 2) ∧
      ¬ ((IntPolyN D K 2 : Set (MvPolynomial (Fin 2) K)) ⊆ Set.range (thetaN D K 2)) :=
  ⟨Dom, Kt, inferInstance, inferInstance, inferInstance, inferInstance,
    Prob20.Proofs.Domain.D_fraction_field_proof,
    Prob20.Proofs.Injective.thetaN_not_injective_proof 2 (le_refl 2),
    fun hsub => Prob20.Proofs.Surjective.theta2_missing_proof.2
      (hsub Prob20.Proofs.Surjective.theta2_missing_proof.1)⟩

end Prob20.Proofs.Headline
