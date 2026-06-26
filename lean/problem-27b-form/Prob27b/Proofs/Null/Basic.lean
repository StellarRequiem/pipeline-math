/-
Copyright (c) 2026 Prob27b formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob27b formalization
-/
import Prob27b.Proofs.RingModel.Basic

/-!
# Stage B — `F` is a right null polynomial (`Null/`)

This support file proves the mathematical heart of the counterexample:

  `F_is_null_proof : ∀ r : R, evalR r F = 0`

i.e. the polynomial `F(X) = u X² + e X³ + (e+u) X⁴ + e X⁵ + e X⁶` vanishes when
its evaluation variable is replaced by **any** element `r` of the truncated path
algebra `R`. The statement is hypothesis-free and quantifies over all of `R`;
nothing is ever assumed about `r` (see the cardinal rule in `BLUEPRINT.md`): we
`R_generic`-decompose an *arbitrary* `r` into its eight `ZMod 2` coefficients and
discharge the resulting unconditional scalar identity.

## Route

1. `evalR_F` unfolds the noncomputable `evalR`/`F` (built on `Polynomial.eval₂`)
   into the concrete `↥R`-expression
   `u * r² + e * r³ + (e+u) * r⁴ + e * r⁵ + e * r⁶`.
2. `R_generic` rewrites `r` as `α•e + … + κ•w`. We never compute matrix powers of
   `r` directly (that is far too expensive); instead the eight lemmas
   `e_r … w_r` give the reduced form of *each basis element times `r`*, and
   `comb_r` lifts this to "an arbitrary combination times `r`". Iterating `comb_r`
   computes each power `r², …, r⁶` as a short `ZMod 2`-combination of the basis,
   keeping every intermediate expression 8-dimensional. The final scalar identity
   is closed by `module` (linear algebra over `ZMod 2`) after collecting like
   terms; each scalar coefficient vanishes in characteristic two.
-/

namespace Prob27b

open Polynomial

/-- **Reduction lemma.** `evalR r F` is the concrete `↥R`-expression
`u * r² + e * r³ + (e+u) * r⁴ + e * r⁵ + e * r⁶`. Unfolds the noncomputable
`evalR`/`F` (defined via `Polynomial.eval₂`) into a computable form. -/
theorem evalR_F (r : R) :
    evalR r F = u * r ^ 2 + e * r ^ 3 + (e + u) * r ^ 4 + e * r ^ 5 + e * r ^ 6 := by
  simp [evalR, F, eval₂_add]

section Reduction
variable (α β γ δ η θ ι κ : ZMod 2)

/-- The generic element of `R`, abbreviated for the section. -/
local notation "rr" =>
  α • e + β • f + γ • u + δ • v + η • p + θ • q + ι • s + κ • w

/-! ### Each basis element times the generic element `rr`

These eight identities encode the truncated-path multiplication and are the only
ring computation in the whole stage; everything else is `ZMod 2` linear algebra. -/

theorem e_r : e * rr = α • e + γ • u + η • p + ι • s := by
  simp only [mul_add, mul_smul_comm, e_mul_e, e_mul_u, e_mul_p, e_mul_s,
    e_mul_f, e_mul_v, e_mul_q, e_mul_w, smul_zero, add_zero]
theorem f_r : f * rr = β • f + δ • v + θ • q + κ • w := by
  simp only [mul_add, mul_smul_comm, f_mul_f, f_mul_v, f_mul_q, f_mul_w,
    f_mul_e, f_mul_u, f_mul_p, f_mul_s, smul_zero, add_zero, zero_add]
theorem u_r : u * rr = β • u + δ • p + θ • s := by
  simp only [mul_add, mul_smul_comm, u_mul_f, u_mul_v, u_mul_q,
    u_mul_e, u_mul_u, u_mul_p, u_mul_s, u_mul_w, smul_zero, add_zero, zero_add]
theorem v_r : v * rr = α • v + γ • q + η • w := by
  simp only [mul_add, mul_smul_comm, v_mul_e, v_mul_u, v_mul_p,
    v_mul_f, v_mul_v, v_mul_q, v_mul_s, v_mul_w, smul_zero, add_zero]
theorem p_r : p * rr = α • p + γ • s := by
  simp only [mul_add, mul_smul_comm, p_mul_e, p_mul_u,
    p_mul_f, p_mul_v, p_mul_p, p_mul_q, p_mul_s, p_mul_w, smul_zero, add_zero]
theorem q_r : q * rr = β • q + δ • w := by
  simp only [mul_add, mul_smul_comm, q_mul_f, q_mul_v,
    q_mul_e, q_mul_u, q_mul_p, q_mul_q, q_mul_s, q_mul_w, smul_zero, add_zero, zero_add]
theorem s_r : s * rr = β • s := by
  simp only [mul_add, mul_smul_comm, s_mul_f,
    s_mul_e, s_mul_u, s_mul_v, s_mul_p, s_mul_q, s_mul_s, s_mul_w, smul_zero, add_zero, zero_add]
theorem w_r : w * rr = α • w := by
  simp only [mul_add, mul_smul_comm, w_mul_e,
    w_mul_f, w_mul_u, w_mul_v, w_mul_p, w_mul_q, w_mul_s, w_mul_w, smul_zero, add_zero]

/-- **An arbitrary combination times `rr`.** Lifts the eight `*_r` lemmas from
basis elements to a general `ZMod 2`-combination, reducing it to another (short)
combination. Iterating this computes every power of `rr`. -/
theorem comb_r (a b c d ee ff g h : ZMod 2) :
    (a • e + b • f + c • u + d • v + ee • p + ff • q + g • s + h • w) * rr
    = a • (α • e + γ • u + η • p + ι • s) + b • (β • f + δ • v + θ • q + κ • w)
      + c • (β • u + δ • p + θ • s) + d • (α • v + γ • q + η • w)
      + ee • (α • p + γ • s) + ff • (β • q + δ • w) + g • (β • s) + h • (α • w) := by
  simp only [add_mul, smul_mul_assoc, e_r, f_r, u_r, v_r, p_r, q_r, s_r, w_r]

/-- **Canonical-form right multiplication by `rr`.** Same as `comb_r` but with the
result already collected into the eight-coefficient normal form, so it chains:
the output again matches the input pattern, letting us compute successive powers
of `rr` without nested-`smul` blow-up. -/
theorem mulr_canon (a b c d ee ff g h : ZMod 2) :
    (a • e + b • f + c • u + d • v + ee • p + ff • q + g • s + h • w) * rr
    = (a * α) • e + (b * β) • f + (a * γ + c * β) • u + (b * δ + d * α) • v
      + (a * η + c * δ + ee * α) • p + (b * θ + d * γ + ff * β) • q
      + (a * ι + c * θ + ee * γ + g * β) • s + (b * κ + d * η + ff * δ + h * α) • w := by
  rw [comb_r]; module

end Reduction

/-- **`F` is a right null polynomial of `R`.** For every `r : R`, the
left-coefficient evaluation `evalR r F` is `0`. The statement is copied verbatim
from the frozen `F_is_null` (only the `_proof` suffix differs); in particular it
ranges over all of `R` with no hypotheses on `r`. -/
theorem F_is_null_proof : ∀ r : R, evalR r F = 0 := by
  intro r
  rw [evalR_F]
  obtain ⟨α, β, γ, δ, η, θ, ι, κ, rfl⟩ := R_generic r
  -- Step 1: reduce every power `rr^k` to canonical eight-coefficient form via the
  -- chaining lemma `mulr_canon` (mul-table only — no matrices, bounded width).
  simp only [pow_succ, pow_zero, one_mul, mulr_canon]
  -- Step 2: reduce the leading `u *`, `e *`, `(e+u) *` over the canonical combos
  -- using the mul-table; everything becomes a flat `ZMod 2`-combination.
  simp only [add_mul, mul_add, mul_smul_comm, e_mul_e, e_mul_f, e_mul_u, e_mul_v,
    e_mul_p, e_mul_q, e_mul_s, e_mul_w, u_mul_e, u_mul_f, u_mul_u, u_mul_v, u_mul_p,
    u_mul_q, u_mul_s, u_mul_w, smul_zero, add_zero, zero_add]
  -- Step 3: extract the per-basis-element scalar coefficients (`match_scalars`)
  -- and discharge each as a `ZMod 2` identity — true in characteristic two,
  -- checked by exhausting the two values of each coefficient (`fin_cases`).
  match_scalars <;>
    (fin_cases α <;> fin_cases β <;> fin_cases γ <;> fin_cases δ <;>
     fin_cases η <;> fin_cases θ <;> fin_cases ι <;> fin_cases κ <;> rfl)

end Prob27b
