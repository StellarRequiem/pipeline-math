/-
Copyright (c) 2026 Prob30c formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob30c formalization
-/
import Prob30c.Proofs.PolyCancel.Basic
import Prob30c.Proofs.LowerA.Basic

/-!
# Stage LX — `AX_not_succAbsorbing`, the `f,g,t,…,t` witness (Step 5).

The up-stairs lower bound `ω_{(A q)[X]}(0) ≥ q+2`: a length-`(q+2)` irredundant
zero product in `(A q)[X]`.  The witness is

  `witnessAX q : Fin (q+2) → (A q)[X]`,  `0 ↦ fPoly q`, `1 ↦ gPoly q`,
  the remaining `q` indices `↦ C (tA q)`.

* **LX1** (`witnessAX_prod`): full product `= C(tA q ^ q · s q) · X(1+X) = 0`
  via `cancel_poly_proof` (Stage PC) + `t_pow_q_mul_s` (Stage A).
* **LX2** (`witnessAX_irredundant`): every omit-one product is nonzero —
  omitting a `t`-index leaves `C(tA^{q-1} s)·X(1+X)` whose `X¹`-coefficient is
  `tA^{q-1}·s ≠ 0`; omitting `f`/`g` leaves `C(tA^q)·(other)` whose constant
  coefficient is `tA^q·e₂` resp. `tA^q·e₁`, nonzero via `χe2`/`χe1`.
* **LX3** (`AX_not_succAbsorbing_proof`): assembling negates
  `IsNAbsorbing (q+1) (⊥ : Ideal (A q)[X])`.

This is the crux that beats the down-stairs bound: the length-`q+2` witness
exists only because `fPoly·gPoly` produces a top-level (`t`-free) `s`-term.
-/

namespace Prob30c

open MvPolynomial Finsupp Finset
open scoped Polynomial

variable (q : ℕ)

/-! ## Free-coordinate nonvanishing for the omit-`f`/omit-`g` cases -/

/-- `tA q ^ q · e₁ q ≠ 0` — a free coordinate read by `χe1`. -/
theorem tApow_mul_e1_ne_zero : tA q ^ q * e₁ q ≠ 0 := by
  intro h
  have hχ : χe1 q (tA q ^ q * e₁ q) = (Polynomial.X : D) ^ q := by
    rw [tA_pow_q_eq, e1_eq, ← map_mul, χe1, descendN_mk]
    change MvPolynomial.coeff (single 0 1) (C (Polynomial.X ^ q) * X 0) = _
    rw [MvPolynomial.coeff_C_mul]
    simp
  rw [h, map_zero] at hχ
  exact pow_ne_zero q Polynomial.X_ne_zero hχ.symm

/-- `tA q ^ q · e₂ q ≠ 0` — a free coordinate read by `χe2`. -/
theorem tApow_mul_e2_ne_zero : tA q ^ q * e₂ q ≠ 0 := by
  intro h
  have hχ : χe2 q (tA q ^ q * e₂ q) = (Polynomial.X : D) ^ q := by
    rw [tA_pow_q_eq, e2_eq, ← map_mul, χe2, descendN_mk]
    change MvPolynomial.coeff (single 1 1) (C (Polynomial.X ^ q) * X 1) = _
    rw [MvPolynomial.coeff_C_mul]
    simp
  rw [h, map_zero] at hχ
  exact pow_ne_zero q Polynomial.X_ne_zero hχ.symm

/-! ## LX1 — the witness and its full product -/

/-- The length-`(q+2)` witness family: `0 ↦ fPoly q`, `1 ↦ gPoly q`, every other
index `↦ C (tA q)`. -/
noncomputable def witnessAX (q : ℕ) : Fin (q + 2) → Polynomial (A q) :=
  fun i => if i = 0 then fPoly q else if i = 1 then gPoly q else Polynomial.C (tA q)

theorem witnessAX_zero : witnessAX q 0 = fPoly q := by simp [witnessAX]

theorem witnessAX_one : witnessAX q 1 = gPoly q := by
  simp [witnessAX, (one_ne_zero : (1 : Fin (q + 2)) ≠ 0)]

theorem witnessAX_ge2 {i : Fin (q + 2)} (h0 : i ≠ 0) (h1 : i ≠ 1) :
    witnessAX q i = Polynomial.C (tA q) := by simp [witnessAX, h0, h1]

/-- On any index set avoiding `0` and `1`, the product is `C(tA q) ^ card`. -/
theorem prod_witnessAX_const {S : Finset (Fin (q + 2))} (h0 : (0 : Fin (q + 2)) ∉ S)
    (h1 : (1 : Fin (q + 2)) ∉ S) :
    ∏ i ∈ S, witnessAX q i = Polynomial.C (tA q) ^ S.card := by
  rw [Finset.prod_congr rfl
      (fun i hi => witnessAX_ge2 q (by rintro rfl; exact h0 hi) (by rintro rfl; exact h1 hi)),
    Finset.prod_const]

/-- The omit-`0` product (drop `fPoly`) is `gPoly q · C(tA q) ^ q`. -/
theorem witnessAX_erase_zero :
    ∏ i ∈ univ.erase (0 : Fin (q + 2)), witnessAX q i = gPoly q * Polynomial.C (tA q) ^ q := by
  have h1mem : (1 : Fin (q + 2)) ∈ univ.erase (0 : Fin (q + 2)) :=
    Finset.mem_erase.mpr ⟨one_ne_zero, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase _ _ h1mem, witnessAX_one]
  congr 1
  rw [prod_witnessAX_const]
  · congr 1
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨one_ne_zero, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  · exact fun h => Finset.notMem_erase 0 univ (Finset.mem_of_mem_erase h)
  · exact Finset.notMem_erase 1 _

/-- The omit-`1` product (drop `gPoly`) is `fPoly q · C(tA q) ^ q`. -/
theorem witnessAX_erase_one :
    ∏ i ∈ univ.erase (1 : Fin (q + 2)), witnessAX q i = fPoly q * Polynomial.C (tA q) ^ q := by
  have h0mem : (0 : Fin (q + 2)) ∈ univ.erase (1 : Fin (q + 2)) :=
    Finset.mem_erase.mpr ⟨Ne.symm one_ne_zero, Finset.mem_univ _⟩
  rw [← Finset.mul_prod_erase _ _ h0mem, witnessAX_zero]
  congr 1
  rw [prod_witnessAX_const]
  · congr 1
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm one_ne_zero, Finset.mem_univ _⟩),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  · exact Finset.notMem_erase 0 _
  · exact fun h => Finset.notMem_erase 1 univ (Finset.mem_of_mem_erase h)

/-- The omit-`j` product for `j ∉ {0,1}` (drop a `t`-factor) is
`fPoly q · (gPoly q · C(tA q) ^ (q-1))`. -/
theorem witnessAX_erase_t {j : Fin (q + 2)} (hj0 : j ≠ 0) (hj1 : j ≠ 1) :
    ∏ i ∈ univ.erase j, witnessAX q i = fPoly q * (gPoly q * Polynomial.C (tA q) ^ (q - 1)) := by
  have h0mem : (0 : Fin (q + 2)) ∈ univ.erase j :=
    Finset.mem_erase.mpr ⟨Ne.symm hj0, Finset.mem_univ _⟩
  have h1mem : (1 : Fin (q + 2)) ∈ (univ.erase j).erase 0 :=
    Finset.mem_erase.mpr ⟨one_ne_zero, Finset.mem_erase.mpr ⟨Ne.symm hj1, Finset.mem_univ _⟩⟩
  rw [← Finset.mul_prod_erase _ _ h0mem, witnessAX_zero,
    ← Finset.mul_prod_erase _ _ h1mem, witnessAX_one]
  congr 2
  rw [prod_witnessAX_const]
  · congr 1
    rw [Finset.card_erase_of_mem h1mem,
      Finset.card_erase_of_mem h0mem,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega
  · exact fun h => Finset.notMem_erase 0 (univ.erase j) (Finset.mem_of_mem_erase h)
  · exact Finset.notMem_erase 1 _

/-- **LX1 — the full product vanishes.** -/
theorem witnessAX_prod : ∏ i, witnessAX q i = 0 := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (0 : Fin (q + 2))), witnessAX_zero,
    witnessAX_erase_zero]
  -- `fPoly · (gPoly · C(tA)^q) = C(tA^q · s) · X(1+X) = 0`
  have hcp : fPoly q * (gPoly q * Polynomial.C (tA q) ^ q)
      = Polynomial.C (tA q ^ q * s q) * (Polynomial.X * (1 + Polynomial.X)) := by
    rw [← mul_assoc, cancel_poly_proof, ← Polynomial.C_pow, map_mul]
    ring
  rw [hcp, t_pow_q_mul_s, map_zero, zero_mul]

/-! ## LX2 — irredundancy: every omit-one product is nonzero -/

/-- The `X¹`-coefficient of `C c · (X·(1+X))` is `c`. -/
theorem coeff_one_C_mul (c : A q) :
    (Polynomial.C c * (Polynomial.X * (1 + Polynomial.X))).coeff 1 = c := by
  have hX : (Polynomial.X : (A q)[X]) * (1 + Polynomial.X) = Polynomial.X + Polynomial.X ^ 2 := by
    ring
  rw [hX, mul_add, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_one, Polynomial.coeff_X_pow, mul_one, if_neg (by norm_num), mul_zero,
    add_zero]

/-- The constant coefficient of `gPoly q` is `e₁ q`. -/
theorem coeff_zero_gPoly : (gPoly q).coeff 0 = e₁ q := by
  rw [gPoly]
  simp [Polynomial.coeff_X_pow]

/-- The constant coefficient of `fPoly q` is `e₂ q`. -/
theorem coeff_zero_fPoly : (fPoly q).coeff 0 = e₂ q := by
  rw [fPoly]
  simp

/-- **LX2 — irredundancy.**  For every `j`, the omit-`j` product is nonzero. -/
theorem witnessAX_irredundant (hq : 2 ≤ q) (j : Fin (q + 2)) :
    ∏ i ∈ univ.erase j, witnessAX q i ≠ 0 := by
  by_cases hj0 : j = 0
  · -- omit `fPoly`: product `= gPoly · C(tA^q)`, constant coeff `= tA^q · e₁ ≠ 0`.
    subst hj0
    rw [witnessAX_erase_zero]
    intro h
    apply tApow_mul_e1_ne_zero q
    have hc : (gPoly q * Polynomial.C (tA q) ^ q).coeff 0 = tA q ^ q * e₁ q := by
      rw [mul_comm, ← Polynomial.C_pow, Polynomial.coeff_C_mul, coeff_zero_gPoly]
    rw [h, Polynomial.coeff_zero] at hc
    exact hc.symm
  · by_cases hj1 : j = 1
    · -- omit `gPoly`: product `= fPoly · C(tA^q)`, constant coeff `= tA^q · e₂ ≠ 0`.
      subst hj1
      rw [witnessAX_erase_one]
      intro h
      apply tApow_mul_e2_ne_zero q
      have hc : (fPoly q * Polynomial.C (tA q) ^ q).coeff 0 = tA q ^ q * e₂ q := by
        rw [mul_comm, ← Polynomial.C_pow, Polynomial.coeff_C_mul, coeff_zero_fPoly]
      rw [h, Polynomial.coeff_zero] at hc
      exact hc.symm
    · -- omit a `t`-factor: product `= C(tA^{q-1}·s)·X(1+X)`, `X¹`-coeff `= tA^{q-1}·s ≠ 0`.
      rw [witnessAX_erase_t q hj0 hj1]
      intro h
      apply t_pow_pred_mul_s_ne_zero q (by omega)
      have hcp : fPoly q * (gPoly q * Polynomial.C (tA q) ^ (q - 1))
          = Polynomial.C (tA q ^ (q - 1) * s q) * (Polynomial.X * (1 + Polynomial.X)) := by
        rw [← mul_assoc, cancel_poly_proof, ← Polynomial.C_pow, map_mul]
        ring
      have hc : (fPoly q * (gPoly q * Polynomial.C (tA q) ^ (q - 1))).coeff 1
          = tA q ^ (q - 1) * s q := by rw [hcp, coeff_one_C_mul]
      rw [h, Polynomial.coeff_zero] at hc
      exact hc.symm

/-! ## LX3 — `AX_not_succAbsorbing` -/

/-- **Stage LX deliverable.**  `(⊥ : Ideal (A q)[X])` is *not* `(q+1)`-absorbing:
`witnessAX q` is a length-`(q+2)` irredundant zero product. -/
theorem AX_not_succAbsorbing_proof (q : ℕ) (hq : 2 ≤ q) :
    ¬ IsNAbsorbing (q + 1) (⊥ : Ideal (Polynomial (A q))) := by
  intro hAbs
  obtain ⟨j, hj⟩ := hAbs (witnessAX q) (by rw [Ideal.mem_bot]; exact witnessAX_prod q)
  rw [Ideal.mem_bot] at hj
  exact witnessAX_irredundant q hq j hj

end Prob30c
