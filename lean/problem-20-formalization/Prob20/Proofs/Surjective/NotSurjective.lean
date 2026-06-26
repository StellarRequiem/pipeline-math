import Prob20.Proofs.Surjective.Amplify
import Prob20.Proofs.Surjective.Place1

/-!
# Stage 4.3 — `thetaN_not_surjective` : the unconditional `∀ n ≥ 2` non-surjectivity

This module closes the frozen `Prob20.thetaN_not_surjective` by feeding the now-✅
`n = 2` non-surjectivity milestone `theta2_missing_proof` (from
`Prob20.Proofs.Surjective.Place1`) into the ✅ conditional lift
`thetaN_not_surjective_of_theta2` (from `Prob20.Proofs.Surjective.Amplify`).

* `Amplify.lean` supplies the genuine `∀ n` reduction to `n = 2`
  (`thetaN_not_surjective_of_theta2`), conditional on the frozen `theta2_missing`
  statement as a hypothesis.
* `Place1.lean` supplies the unconditional `n = 2` fact `theta2_missing_proof`.

Both ingredients are sorry-free and axiom-clean; their composition is the frozen
theorem with no drift.  (The two files coexist now that the duplicate-name clash
between `Amplify.lean` and `Missing.lean` — the latter pulled in transitively via
`Place1.lean` — has been resolved by renaming Amplify's `incl_apply`/`thetaN_add`
to `incl_apply_n`/`thetaN_add_n`.)
-/

open scoped TensorProduct

open Prob20

namespace Prob20.Proofs.Surjective

/-- **Stage 4.3 (HEADLINE non-surjectivity).**  The canonical product map `θₙ` is
not surjective onto `Int(Dⁿ)` for every `n ≥ 2`.  Statement COPIED VERBATIM from the
frozen `Prob20.thetaN_not_surjective`; proved by composing the genuine `∀ n` lift
`thetaN_not_surjective_of_theta2` with the unconditional `n = 2` milestone
`theta2_missing_proof`. -/
theorem thetaN_not_surjective_proof :
    ∀ n : ℕ, 2 ≤ n →
      ¬ ((IntPolyN Dom Kt n : Set (MvPolynomial (Fin n) Kt))
            ⊆ Set.range (thetaN Dom Kt n)) :=
  thetaN_not_surjective_of_theta2 theta2_missing_proof

end Prob20.Proofs.Surjective
