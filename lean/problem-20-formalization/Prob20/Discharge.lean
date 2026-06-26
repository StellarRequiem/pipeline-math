import Prob20.Solution

/-!
# Discharge.lean — machine-checked no-drift gate

During the proving phase, for each of the ten frozen theorems this module pairs
the frozen statement with its clean proof via `example : @<Frozen> = @<Proof> :=
rfl`. Each such `example` compiles **iff** the proof has *exactly* the frozen
proposition, so it is a machine proof that no statement drifted.

SETUP-stage placeholder: the `Prob20.Solution.<name>` proofs do not exist yet
(the frozen statements are still `sorry`), so no `rfl`-gates are emitted. They
are added here once `Solution.lean` exposes the proven theorems.
-/

namespace Prob20.Discharge

/-! ## Stage 1 — no-drift gates -/

example : @Prob20.D_residue_field = @Prob20.Proofs.Domain.D_residue_field_proof := rfl
example : @Prob20.D_fraction_field = @Prob20.Proofs.Domain.D_fraction_field_proof := rfl

/-! ## Stage 2 — no-drift gates -/

example : @Prob20.key_membership = @Prob20.Proofs.KeyObs.key_membership_proof := rfl
example : @Prob20.p_tp_linindep = @Prob20.Proofs.KeyObs.p_tp_linindep_proof := rfl

/-! ## Stage 3 — no-drift gates -/

example : @Prob20.theta2_kernel = @Prob20.Proofs.Injective.theta2_kernel_proof := rfl
example : @Prob20.thetaN_not_injective = @Prob20.Proofs.Injective.thetaN_not_injective_proof := rfl

/-! ## Stage 4 — no-drift gates -/

example : @Prob20.g_mem = @Prob20.Proofs.Surjective.g_mem_proof := rfl
example : @Prob20.theta2_missing = @Prob20.Proofs.Surjective.theta2_missing_proof := rfl
example : @Prob20.thetaN_not_surjective = @Prob20.Proofs.Surjective.thetaN_not_surjective_proof := rfl

/-! ## Headline — no-drift gate -/

example : @Prob20.problem20_answer = @Prob20.Proofs.Headline.problem20_answer_proof := rfl

end Prob20.Discharge
