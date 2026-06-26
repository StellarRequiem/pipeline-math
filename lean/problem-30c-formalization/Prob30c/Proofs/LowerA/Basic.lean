/-
Copyright (c) 2026 Prob30c formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob30c formalization
-/
import Prob30c.Proofs.RingModel.Basic

/-!
# Stage LA — `A_not_qAbsorbing`, the `s·t^q` lower-bound witness (Step 3 lower).

This file proves the Stage LA support lemmas (BLUEPRINT "Stage LA" ↔ SKETCH
Step 3 lower) for the Problem 30(c) counterexample.

The down-stairs lower bound `ω_{A q}(0) ≥ q+1` is witnessed by the
length-`(q+1)` family

* **LA1** `witnessA q : Fin (q+1) → A q`, sending `0 ↦ s q` and every other
  index to `tA q`.  Its full product is `s q · tA q ^ q = tA q ^ q · s q = 0`
  (Stage A `t_pow_q_mul_s`), so it lies in `⊥`.
* **LA2** `witnessA_irredundant`: for **every** `j`, the omit-one product is
  nonzero — omitting `0` leaves `tA q ^ q ≠ 0` (a free coordinate, certified by
  `χ1`), omitting a `t`-index leaves `tA q ^ (q-1) · s q ≠ 0` (Stage A
  `t_pow_pred_mul_s_ne_zero`).
* **LA3** `A_not_qAbsorbing_proof`: the family has product in `⊥` but no
  omit-one product in `⊥`, directly negating `IsNAbsorbing q (⊥)`.
-/

namespace Prob30c

open MvPolynomial Finset

variable (q : ℕ)

/-! ## A free-coordinate nonvanishing: `tA q ^ q ≠ 0` -/

/-- `tA q ^ q = mkA q (C (t^q))`. -/
theorem tA_pow_q_eq : tA q ^ q = mkA q (C (Polynomial.X ^ q)) := by
  rw [tA_eq, ← map_pow, ← map_pow]

/-- **`tA q ^ q ≠ 0`** — `tA` is a free (unit-direction) coordinate; its
constant-coordinate functional `χ1` reads `t^q ≠ 0`.  (No char-2 cancellation:
this is a genuinely nonzero free coordinate.) -/
theorem t_pow_q_ne_zero : tA q ^ q ≠ 0 := by
  intro h
  have hχ : χ1 q (tA q ^ q) = (Polynomial.X : D) ^ q := by
    rw [tA_pow_q_eq, χ1, descendN_mk]
    change coeff 0 (C (Polynomial.X ^ q)) = (Polynomial.X : D) ^ q
    rw [coeff_C]; simp
  rw [h, map_zero] at hχ
  exact pow_ne_zero q Polynomial.X_ne_zero hχ.symm

/-! ## LA1 — the witness -/

/-- The length-`(q+1)` witness family: `0 ↦ s q`, every other index `↦ tA q`. -/
noncomputable def witnessA (q : ℕ) : Fin (q + 1) → A q :=
  fun i => if i = 0 then s q else tA q

theorem witnessA_zero : witnessA q 0 = s q := by simp [witnessA]

theorem witnessA_ne_zero {i : Fin (q + 1)} (hi : i ≠ 0) : witnessA q i = tA q := by
  simp [witnessA, hi]

/-- **LA1 — the full product vanishes:** `∏ i, witnessA q i = s q · tA q ^ q = 0`. -/
theorem witnessA_prod : ∏ i, witnessA q i = 0 := by
  rw [Fin.prod_univ_succ]
  have h0 : witnessA q 0 = s q := witnessA_zero q
  have hrest : ∏ i : Fin q, witnessA q i.succ = tA q ^ q := by
    rw [Finset.prod_congr rfl (fun i _ => witnessA_ne_zero q (Fin.succ_ne_zero i)),
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h0, hrest, mul_comm, t_pow_q_mul_s]

/-! ## LA2 — irredundancy: every omit-one product is nonzero -/

/-- The omit-`0` product is `tA q ^ q ≠ 0`. -/
theorem witnessA_erase_zero : ∏ i ∈ univ.erase (0 : Fin (q + 1)), witnessA q i = tA q ^ q := by
  rw [Finset.prod_congr rfl
      (fun i hi => witnessA_ne_zero q (Finset.ne_of_mem_erase hi)),
    Finset.prod_const]
  congr 1
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

/-- The omit-`j` product for `j ≠ 0` is `s q · tA q ^ (q-1)`. -/
theorem witnessA_erase_ne_zero {j : Fin (q + 1)} (hj : j ≠ 0) :
    ∏ i ∈ univ.erase j, witnessA q i = s q * tA q ^ (q - 1) := by
  have h0mem : (0 : Fin (q + 1)) ∈ univ.erase j :=
    Finset.mem_erase.mpr ⟨Ne.symm hj, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase _ _ h0mem, witnessA_zero]
  congr 1
  rw [Finset.prod_congr rfl
      (fun i hi => witnessA_ne_zero q (Finset.ne_of_mem_erase hi)),
    Finset.prod_const]
  congr 1
  rw [Finset.card_erase_of_mem h0mem, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin]
  omega

/-- **LA2 — irredundancy.**  For **every** `j : Fin (q+1)`, the omit-one product
of `witnessA q` is nonzero (`hq : 2 ≤ q` guarantees `0 < q`, needed for the
torsion nonvanishing). -/
theorem witnessA_irredundant (hq : 2 ≤ q) (j : Fin (q + 1)) :
    ∏ i ∈ univ.erase j, witnessA q i ≠ 0 := by
  rcases eq_or_ne j 0 with rfl | hj
  · rw [witnessA_erase_zero]
    exact t_pow_q_ne_zero q
  · rw [witnessA_erase_ne_zero q hj, mul_comm]
    exact t_pow_pred_mul_s_ne_zero q (by omega)

/-! ## LA3 — `A_not_qAbsorbing` -/

/-- **LA3 — the frozen `A_not_qAbsorbing`.**  `witnessA q` is a `Fin (q+1)`
family (`n = q`, `n+1 = q+1` factors) with full product in `⊥` but **no**
omit-one product in `⊥`, directly negating `IsNAbsorbing q (⊥)`. -/
theorem A_not_qAbsorbing_proof (q : ℕ) (hq : 2 ≤ q) :
    ¬ IsNAbsorbing q (⊥ : Ideal (A q)) := by
  intro h
  obtain ⟨j, hj⟩ := h (witnessA q) (by rw [Ideal.mem_bot]; exact witnessA_prod q)
  rw [Ideal.mem_bot] at hj
  exact witnessA_irredundant q hq j hj

end Prob30c
