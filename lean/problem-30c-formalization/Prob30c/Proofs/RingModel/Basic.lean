/-
Copyright (c) 2026 Prob30c formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob30c formalization
-/
import Prob30c.Defs

/-!
# Stage A — `A q` is the `𝔽₂[t]`-algebra: mul table, `J³=0`, `D`-basis, coordinate functionals.

This file proves the Stage A support lemmas (BLUEPRINT "Stage A" ↔ SKETCH Step 1)
for the Problem 30(c) counterexample.  `A q = MvPolynomial (Fin 3) D ⧸ Arel q`
with `D = 𝔽₂[t]`.  We recover the computational handles every later stage uses:

* **A1** the degree-`2` multiplication table (`e₁²=0`, `e₁e₂=0`, `e₃²=u₁`,
  `e₂e₃=u₁`, `e₂²=u₂`, `e₁e₃=u₂+s`) and the degree-`3` vanishing;
* **A2** `J³ = ⊥` (`J_pow_three`), `J² = span_D{u₁,u₂,s}` (`J_sq`), and the
  torsion facts `tA^q·s = 0` (`t_pow_q_mul_s`) / `tA^{q−1}·s ≠ 0`;
* **A3** the augmentation `aug : A q →+* D` and `J = ker aug` (`J_eq_ker`);
* **A4** the `D`-coordinate functionals `χ_*` reading the coordinates in
  `A q ≅ D⁶ ⊕ (D/t^q)`, each descended from `MvPolynomial.lcoeff` through `Arel`.

All (non)vanishing in `A q` goes through the coordinate functionals (mirroring
prob4b's `phiP`/`lcoeff_vanish` recipe, now `D`-valued).  No `decide` over `A q`.
-/

namespace Prob30c

open MvPolynomial Finsupp

/-- Local name for the polynomial ring `P3 = MvPolynomial (Fin 3) D`. -/
abbrev P3 : Type := MvPolynomial (Fin 3) D

variable (q : ℕ)

/-- The quotient ring hom `mkA q : P3 →+* A q`, with codomain pinned to `A q`
(definitionally `Ideal.Quotient.mk (Arel q)`).  Routing through this avoids the
`A q`-is-a-`def` transparency issues that arise when rewriting with the bare
`Ideal.Quotient.mk` (whose codomain is the unfolded quotient type). -/
noncomputable def mkA (q : ℕ) : P3 →+* A q := Ideal.Quotient.mk (Arel q)

theorem mkA_eq_zero_iff {p : P3} : mkA q p = 0 ↔ p ∈ Arel q :=
  Ideal.Quotient.eq_zero_iff_mem

theorem mkA_ker : RingHom.ker (mkA q) = Arel q := Ideal.mk_ker

theorem e1_eq : e₁ q = mkA q (X 0) := rfl
theorem e2_eq : e₂ q = mkA q (X 1) := rfl
theorem e3_eq : e₃ q = mkA q (X 2) := rfl
theorem tA_eq : tA q = mkA q (C Polynomial.X) := rfl

/-! ## A1 — the multiplication table -/

/-- `e₁² = 0` (the relation `X₀² ∈ Arel`). -/
@[simp] theorem e1_sq : e₁ q ^ 2 = 0 := by
  rw [e1_eq, ← map_pow, mkA_eq_zero_iff]
  exact Ideal.mem_sup_right (Ideal.subset_span (by simp))

/-- `e₁ * e₂ = 0` (the relation `X₀X₁ ∈ Arel`). -/
@[simp] theorem e1_mul_e2 : e₁ q * e₂ q = 0 := by
  rw [e1_eq, e2_eq, ← map_mul, mkA_eq_zero_iff]
  exact Ideal.mem_sup_right (Ideal.subset_span (by simp))

/-- `e₂ * e₃ = u₁` (definitional). -/
@[simp] theorem e2_mul_e3 : e₂ q * e₃ q = u₁ q := rfl

/-- `e₂² = u₂` (definitional, via `pow_two`). -/
@[simp] theorem e2_sq : e₂ q ^ 2 = u₂ q := by rw [pow_two]; rfl

/-- `e₃² = u₁` (the relation `X₂² − X₁X₂ ∈ Arel`). -/
@[simp] theorem e3_sq : e₃ q ^ 2 = u₁ q := by
  unfold u₁
  rw [e2_eq, e3_eq, ← map_mul, ← map_pow, ← sub_eq_zero, ← map_sub, mkA_eq_zero_iff]
  exact Ideal.mem_sup_right (Ideal.subset_span (by simp))

/-- `e₁ * e₃ = u₂ + s` (definitional: `s = e₁e₃ − u₂`). -/
theorem e1_mul_e3 : e₁ q * e₃ q = u₂ q + s q := by unfold s; ring

theorem e2_mul_e1 : e₂ q * e₁ q = 0 := by rw [mul_comm]; exact e1_mul_e2 q
theorem e3_mul_e2 : e₃ q * e₂ q = u₁ q := by rw [mul_comm]; exact e2_mul_e3 q
theorem e3_mul_e1 : e₃ q * e₁ q = u₂ q + s q := by rw [mul_comm]; exact e1_mul_e3 q
theorem e1_mul_e1 : e₁ q * e₁ q = 0 := by rw [← pow_two]; exact e1_sq q
theorem e2_mul_e2 : e₂ q * e₂ q = u₂ q := rfl
theorem e3_mul_e3 : e₃ q * e₃ q = u₁ q := by rw [← pow_two]; exact e3_sq q

/-! ## A2 — `J³ = 0` and the torsion relation -/

/-- The augmentation ideal `J = (e₁,e₂,e₃)` is the image of `mP = (X₀,X₁,X₂)`. -/
theorem J_eq_map : J q = mP.map (mkA q) := by
  unfold J mP
  rw [Ideal.map_span, e1_eq, e2_eq, e3_eq]
  congr 1
  simp [Set.image_insert_eq]

/-- `J³ = ⊥`: the augmentation ideal is nilpotent of order `3`
(`mP³ ≤ Arel = ker (mkA)`). -/
theorem J_pow_three : J q ^ 3 = (⊥ : Ideal (A q)) := by
  rw [J_eq_map, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker, mkA_ker]
  exact le_sup_left

/-- `e₁ ∈ J`. -/
theorem e1_mem_J : e₁ q ∈ J q := by unfold J; exact Ideal.subset_span (by simp)
/-- `e₂ ∈ J`. -/
theorem e2_mem_J : e₂ q ∈ J q := by unfold J; exact Ideal.subset_span (by simp)
/-- `e₃ ∈ J`. -/
theorem e3_mem_J : e₃ q ∈ J q := by unfold J; exact Ideal.subset_span (by simp)

/-- Any product of three elements of `J` vanishes (`J³ = 0`). -/
theorem mul_mem_J3 {x y z : A q} (hx : x ∈ J q) (hy : y ∈ J q) (hz : z ∈ J q) :
    x * y * z = 0 := by
  have hmem : x * y * z ∈ J q ^ 3 := by
    have h2 : x * y ∈ J q ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul hx hy
    rw [pow_succ]
    exact Ideal.mul_mem_mul h2 hz
  rwa [J_pow_three, Ideal.mem_bot] at hmem

/-- `s = mk (X₀X₂ − X₁²)`. -/
theorem s_eq : s q = mkA q (X 0 * X 2 - X 1 ^ 2) := by
  unfold s u₂
  rw [e1_eq, e2_eq, e3_eq, pow_two, ← map_mul, ← map_mul, ← map_sub]

/-- The torsion relation `tA^q · s = 0` (the relation
`C(t^q)·(X₀X₂ − X₁²) ∈ Arel`). -/
theorem t_pow_q_mul_s : tA q ^ q * s q = 0 := by
  rw [tA_eq, s_eq, ← map_pow, ← map_mul, mkA_eq_zero_iff, ← map_pow]
  exact Ideal.mem_sup_right (Ideal.subset_span (by simp))

/-! ## A4 — the `D`-coordinate functionals (`lcoeff`-descent)

We read off coordinates of `A q` in `D⁶ ⊕ (D/t^q)` through `MvPolynomial.lcoeff`.
The pattern (mirroring prob4b's `phiP`) is: a `D`-linear combination of `lcoeff`s
that vanishes on every generator of `Arel`, hence detects nonvanishing in `A q`.
-/

/-- Exponent vector of `X₀X₂`. -/
noncomputable def m02 : Fin 3 →₀ ℕ := single 0 1 + single 2 1
/-- Exponent vector of `X₁²`. -/
noncomputable def m1sq : Fin 3 →₀ ℕ := single 1 2
/-- Exponent vector of `X₀²`. -/
noncomputable def m0sq : Fin 3 →₀ ℕ := single 0 2
/-- Exponent vector of `X₀X₁`. -/
noncomputable def m01 : Fin 3 →₀ ℕ := single 0 1 + single 1 1
/-- Exponent vector of `X₂²`. -/
noncomputable def m2sq : Fin 3 →₀ ℕ := single 2 2
/-- Exponent vector of `X₁X₂`. -/
noncomputable def m12 : Fin 3 →₀ ℕ := single 1 1 + single 2 1

theorem degree_m02 : degree m02 = 2 := by rw [m02, map_add]; simp [Finsupp.degree_single]
theorem degree_m1sq : degree m1sq = 2 := by simp [m1sq, Finsupp.degree_single]

/-- A `¬ (a ≤ b)` certificate from a single bad coordinate. -/
theorem fin3_not_le {a b : Fin 3 →₀ ℕ} (i : Fin 3) (h : ¬ a i ≤ b i) : ¬ a ≤ b :=
  fun hle => h (hle i)

theorem X0X2_eq : (X 0 * X 2 : P3) = monomial m02 1 := by
  rw [X, X, monomial_mul, mul_one]; rfl
theorem X1sq_eq : (X 1 ^ 2 : P3) = monomial m1sq 1 := by
  rw [pow_two, X, monomial_mul, mul_one]; rw [m1sq]; congr 1; rw [← single_add]
theorem X0sq_eq : (X 0 ^ 2 : P3) = monomial m0sq 1 := by
  rw [pow_two, X, monomial_mul, mul_one]; rw [m0sq]; congr 1; rw [← single_add]
theorem X0X1_eq : (X 0 * X 1 : P3) = monomial m01 1 := by
  rw [X, X, monomial_mul, mul_one]; rfl
theorem X2sq_eq : (X 2 ^ 2 : P3) = monomial m2sq 1 := by
  rw [pow_two, X, monomial_mul, mul_one]; rw [m2sq]; congr 1; rw [← single_add]
theorem X1X2_eq : (X 1 * X 2 : P3) = monomial m12 1 := by
  rw [X, X, monomial_mul, mul_one]; rfl

/-- The `u₂`-coordinate functional at the polynomial level:
`χu2P p = coeff (X₀X₂) p + coeff (X₁²) p`. -/
noncomputable def χu2P : P3 →ₗ[D] D := lcoeff D m02 + lcoeff D m1sq

theorem χu2P_apply (p : P3) : χu2P p = coeff m02 p + coeff m1sq p := rfl

/-- `mP = idealOfVars (Fin 3) D`. -/
theorem mP_eq : mP = idealOfVars (Fin 3) D := by
  unfold mP idealOfVars
  congr 1
  ext p
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_range]
  constructor
  · rintro (h | h | h) <;> subst h
    exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩]
  · rintro ⟨i, rfl⟩; fin_cases i <;> simp

/-- `χu2P` vanishes on `mP³` (it reads only degree-`2` coefficients). -/
theorem χu2P_vanish_mP3 {y : P3} (hy : y ∈ mP ^ 3) : χu2P y = 0 := by
  rw [mP_eq, mem_pow_idealOfVars_iff'] at hy
  rw [χu2P_apply, hy m02 (by rw [degree_m02]; norm_num),
    hy m1sq (by rw [degree_m1sq]; norm_num), add_zero]

/-! ### Coordinate (in)equalities of the exponent vectors -/

theorem m0sq_not_le_m02 : ¬ m0sq ≤ m02 :=
  fin3_not_le 0 (by simp [m0sq, m02])
theorem m0sq_not_le_m1sq : ¬ m0sq ≤ m1sq :=
  fin3_not_le 0 (by simp [m0sq, m1sq])
theorem m01_not_le_m02 : ¬ m01 ≤ m02 :=
  fin3_not_le 1 (by simp [m01, m02])
theorem m01_not_le_m1sq : ¬ m01 ≤ m1sq :=
  fin3_not_le 0 (by simp [m01, m1sq])
theorem m2sq_not_le_m02 : ¬ m2sq ≤ m02 :=
  fin3_not_le 2 (by simp [m2sq, m02])
theorem m2sq_not_le_m1sq : ¬ m2sq ≤ m1sq :=
  fin3_not_le 2 (by simp [m2sq, m1sq])
theorem m12_not_le_m02 : ¬ m12 ≤ m02 :=
  fin3_not_le 1 (by simp [m12, m02, Finsupp.add_apply])
theorem m12_not_le_m1sq : ¬ m12 ≤ m1sq :=
  fin3_not_le 2 (by simp [m12, m1sq, Finsupp.add_apply])
theorem m1sq_not_le_m02 : ¬ m1sq ≤ m02 :=
  fin3_not_le 1 (by simp [m1sq, m02, Finsupp.add_apply])
theorem m02_not_le_m1sq : ¬ m02 ≤ m1sq :=
  fin3_not_le 0 (by simp [m02, m1sq, Finsupp.add_apply])
theorem m1sq_ne_m02 : m1sq ≠ m02 := by
  intro h; apply_fun (· 1) at h
  simp [m1sq, m02, Finsupp.add_apply] at h

-- Coordinate inequalities for the `u₁`-functional (targets `m12`, `m2sq`).
theorem m0sq_not_le_m12 : ¬ m0sq ≤ m12 :=
  fin3_not_le 0 (by simp [m0sq, m12, Finsupp.add_apply])
theorem m0sq_not_le_m2sq : ¬ m0sq ≤ m2sq := fin3_not_le 0 (by simp [m0sq, m2sq])
theorem m01_not_le_m12 : ¬ m01 ≤ m12 :=
  fin3_not_le 0 (by simp [m01, m12, Finsupp.add_apply])
theorem m01_not_le_m2sq : ¬ m01 ≤ m2sq := fin3_not_le 0 (by simp [m01, m2sq])
theorem m2sq_not_le_m12 : ¬ m2sq ≤ m12 :=
  fin3_not_le 2 (by simp [m2sq, m12, Finsupp.add_apply])
theorem m12_not_le_m2sq : ¬ m12 ≤ m2sq :=
  fin3_not_le 1 (by simp [m12, m2sq, Finsupp.add_apply])
theorem m02_not_le_m12 : ¬ m02 ≤ m12 :=
  fin3_not_le 0 (by simp [m02, m12, Finsupp.add_apply])
theorem m1sq_not_le_m12 : ¬ m1sq ≤ m12 :=
  fin3_not_le 1 (by simp [m1sq, m12, Finsupp.add_apply])
theorem m02_not_le_m2sq : ¬ m02 ≤ m2sq :=
  fin3_not_le 0 (by simp [m02, m2sq, Finsupp.add_apply])
theorem m1sq_not_le_m2sq : ¬ m1sq ≤ m2sq := fin3_not_le 1 (by simp [m1sq, m2sq])

/-! ### `χu2P` vanishes on each `Arel`-generator times an arbitrary multiplier -/

theorem χu2P_g1 (a : P3) : χu2P (a * X 0 ^ 2) = 0 := by
  rw [mul_comm, X0sq_eq, χu2P_apply, coeff_monomial_mul', coeff_monomial_mul',
    if_neg m0sq_not_le_m02, if_neg m0sq_not_le_m1sq, add_zero]

theorem χu2P_g2 (a : P3) : χu2P (a * (X 0 * X 1)) = 0 := by
  rw [mul_comm, X0X1_eq, χu2P_apply, coeff_monomial_mul', coeff_monomial_mul',
    if_neg m01_not_le_m02, if_neg m01_not_le_m1sq, add_zero]

theorem χu2P_g3 (a : P3) : χu2P (a * (X 2 ^ 2 - X 1 * X 2)) = 0 := by
  rw [mul_comm, sub_mul, χu2P_apply, coeff_sub, coeff_sub, X2sq_eq, X1X2_eq,
    coeff_monomial_mul', coeff_monomial_mul', coeff_monomial_mul', coeff_monomial_mul',
    if_neg m2sq_not_le_m02, if_neg m12_not_le_m02, if_neg m2sq_not_le_m1sq,
    if_neg m12_not_le_m1sq]
  ring

theorem χu2P_g4 (a : P3) :
    χu2P (a * (C (Polynomial.X ^ q) * (X 0 * X 2 - X 1 ^ 2))) = 0 := by
  rw [mul_comm, mul_assoc, χu2P_apply, coeff_C_mul, coeff_C_mul]
  have h1 : coeff m02 ((X 0 * X 2 - X 1 ^ 2) * a) = coeff 0 a := by
    rw [sub_mul, coeff_sub, X0X2_eq, X1sq_eq, coeff_monomial_mul', coeff_monomial_mul',
      if_pos le_rfl, if_neg m1sq_not_le_m02, tsub_self, one_mul, sub_zero]
  have h2 : coeff m1sq ((X 0 * X 2 - X 1 ^ 2) * a) = - coeff 0 a := by
    rw [sub_mul, coeff_sub, X0X2_eq, X1sq_eq, coeff_monomial_mul', coeff_monomial_mul',
      if_neg m02_not_le_m1sq, if_pos le_rfl, tsub_self, one_mul, zero_sub]
  rw [h1, h2]; ring

/-- `χu2P` vanishes on all of `Arel q`. -/
theorem χu2P_vanish_Arel : ∀ p ∈ Arel q, χu2P p = 0 := by
  intro p hp
  unfold Arel at hp
  rw [Submodule.mem_sup] at hp
  obtain ⟨y, hy, z, hz, rfl⟩ := hp
  rw [map_add, χu2P_vanish_mP3 hy, zero_add]
  rw [Ideal.mem_span_insert] at hz
  obtain ⟨a1, z1, hz1, rfl⟩ := hz
  rw [Ideal.mem_span_insert] at hz1
  obtain ⟨a2, z2, hz2, rfl⟩ := hz1
  rw [Ideal.mem_span_insert] at hz2
  obtain ⟨a3, z3, hz3, rfl⟩ := hz2
  rw [Ideal.mem_span_singleton'] at hz3
  obtain ⟨a4, rfl⟩ := hz3
  rw [map_add, map_add, map_add, χu2P_g1, χu2P_g2, χu2P_g3, χu2P_g4,
    add_zero, add_zero, add_zero]

/-- Detection: `χu2P p ≠ 0` certifies `mkA q p ≠ 0`. -/
theorem ne_zero_of_χu2P {p : P3} (h : χu2P p ≠ 0) : mkA q p ≠ 0 := by
  intro hp
  rw [mkA_eq_zero_iff] at hp
  exact h (χu2P_vanish_Arel q p hp)

/-- **`u₂ ≠ 0`** — `u₂` is a *free* `D`-generator (validation example below). -/
theorem u2_ne_zero : u₂ q ≠ 0 := by
  have hu : u₂ q = mkA q (X 1 ^ 2) := by rw [← e2_sq, e2_eq, ← map_pow]
  rw [hu]
  apply ne_zero_of_χu2P
  rw [χu2P_apply, X1sq_eq, coeff_monomial, coeff_monomial, if_neg m1sq_ne_m02, if_pos rfl,
    zero_add]
  exact one_ne_zero

/-! ### The `s`-coordinate functional `χ_s : A q →ₗ[D] D ⧸ (t^q)`

`s` is *torsion* (`t^q·s = 0`) but nonzero below level `q`; its coordinate is
only well-defined modulo `t^q`.  `χsP q = mkQ ∘ coeff (X₀X₂)` reads it. -/

/-- The `s`-coordinate functional at the polynomial level, valued in `D ⧸ (t^q)`. -/
noncomputable def χsP (q : ℕ) : P3 →ₗ[D] D ⧸ Ideal.span {(Polynomial.X : D) ^ q} :=
  (Ideal.span {(Polynomial.X : D) ^ q}).mkQ ∘ₗ lcoeff D m02

theorem χsP_apply (p : P3) :
    χsP q p = (Ideal.span {(Polynomial.X : D) ^ q}).mkQ (coeff m02 p) := rfl

/-- `mkQ` kills every multiple of `t^q`. -/
theorem mkQ_Xq_mul (c : D) :
    (Ideal.span {(Polynomial.X : D) ^ q}).mkQ (Polynomial.X ^ q * c) = 0 := by
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

/-! The `m02`-coefficient of each generator times an arbitrary multiplier. -/

theorem coeff_m02_g1 (a : P3) : coeff m02 (a * X 0 ^ 2) = 0 := by
  rw [mul_comm, X0sq_eq, coeff_monomial_mul', if_neg m0sq_not_le_m02]

theorem coeff_m02_g2 (a : P3) : coeff m02 (a * (X 0 * X 1)) = 0 := by
  rw [mul_comm, X0X1_eq, coeff_monomial_mul', if_neg m01_not_le_m02]

theorem coeff_m02_g3 (a : P3) : coeff m02 (a * (X 2 ^ 2 - X 1 * X 2)) = 0 := by
  rw [mul_comm, sub_mul, coeff_sub, X2sq_eq, X1X2_eq, coeff_monomial_mul',
    coeff_monomial_mul', if_neg m2sq_not_le_m02, if_neg m12_not_le_m02, sub_zero]

theorem coeff_m02_g4 (a : P3) :
    coeff m02 (a * (C (Polynomial.X ^ q) * (X 0 * X 2 - X 1 ^ 2)))
      = Polynomial.X ^ q * coeff 0 a := by
  rw [mul_comm, mul_assoc, coeff_C_mul, sub_mul, coeff_sub, X0X2_eq, X1sq_eq,
    coeff_monomial_mul', coeff_monomial_mul', if_pos le_rfl, if_neg m1sq_not_le_m02,
    tsub_self, one_mul, sub_zero]

theorem χsP_g1 (a : P3) : χsP q (a * X 0 ^ 2) = 0 := by
  rw [χsP_apply, coeff_m02_g1, map_zero]
theorem χsP_g2 (a : P3) : χsP q (a * (X 0 * X 1)) = 0 := by
  rw [χsP_apply, coeff_m02_g2, map_zero]
theorem χsP_g3 (a : P3) : χsP q (a * (X 2 ^ 2 - X 1 * X 2)) = 0 := by
  rw [χsP_apply, coeff_m02_g3, map_zero]
theorem χsP_g4 (a : P3) :
    χsP q (a * (C (Polynomial.X ^ q) * (X 0 * X 2 - X 1 ^ 2))) = 0 := by
  rw [χsP_apply, coeff_m02_g4, mkQ_Xq_mul]

/-- `χsP` vanishes on `mP³`. -/
theorem χsP_vanish_mP3 {y : P3} (hy : y ∈ mP ^ 3) : χsP q y = 0 := by
  rw [mP_eq, mem_pow_idealOfVars_iff'] at hy
  rw [χsP_apply, hy m02 (by rw [degree_m02]; norm_num), map_zero]

/-- `χsP` vanishes on all of `Arel q`. -/
theorem χsP_vanish_Arel : ∀ p ∈ Arel q, χsP q p = 0 := by
  intro p hp
  unfold Arel at hp
  rw [Submodule.mem_sup] at hp
  obtain ⟨y, hy, z, hz, rfl⟩ := hp
  rw [map_add, χsP_vanish_mP3 q hy, zero_add]
  rw [Ideal.mem_span_insert] at hz
  obtain ⟨a1, z1, hz1, rfl⟩ := hz
  rw [Ideal.mem_span_insert] at hz1
  obtain ⟨a2, z2, hz2, rfl⟩ := hz1
  rw [Ideal.mem_span_insert] at hz2
  obtain ⟨a3, z3, hz3, rfl⟩ := hz2
  rw [Ideal.mem_span_singleton'] at hz3
  obtain ⟨a4, rfl⟩ := hz3
  rw [map_add, map_add, map_add, χsP_g1, χsP_g2, χsP_g3, χsP_g4,
    add_zero, add_zero, add_zero]

/-- Detection: `χsP q p ≠ 0` certifies `mkA q p ≠ 0`. -/
theorem ne_zero_of_χsP {p : P3} (h : χsP q p ≠ 0) : mkA q p ≠ 0 := by
  intro hp
  rw [mkA_eq_zero_iff] at hp
  exact h (χsP_vanish_Arel q p hp)

/-- **`tA^{q−1}·s ≠ 0`** — `s` is torsion but nonzero below level `q` (the engine
of the lower bound; validation example below). -/
theorem t_pow_pred_mul_s_ne_zero (hq : 0 < q) : tA q ^ (q - 1) * s q ≠ 0 := by
  have hrepr : tA q ^ (q - 1) * s q
      = mkA q (C (Polynomial.X ^ (q - 1)) * (X 0 * X 2 - X 1 ^ 2)) := by
    rw [tA_eq, s_eq, ← map_pow, ← map_mul, ← map_pow]
  rw [hrepr]
  apply ne_zero_of_χsP
  rw [χsP_apply, coeff_C_mul, coeff_sub, X0X2_eq, X1sq_eq, coeff_monomial, coeff_monomial,
    if_pos rfl, if_neg m1sq_ne_m02, sub_zero, mul_one, Ne, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]
  intro hdvd
  have hle := Polynomial.natDegree_le_of_dvd hdvd (pow_ne_zero _ Polynomial.X_ne_zero)
  rw [Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow] at hle
  omega

/-! ## A4 (objects) — the descended `D`-linear coordinate functionals on `A q`

Each `D`-linear `lcoeff`-combination that vanishes on `Arel q` descends to a
genuine functional `A q →ₗ[D] D` (or `→ₗ[D] D ⧸ (t^q)` for `χ_s`) via
`Submodule.liftQ`.  The application lemma `*_mk` is definitional. -/

/-- Generic descent of a `D`-linear functional through the quotient `A q`. -/
noncomputable def descendN {N : Type*} [AddCommGroup N] [Module D N] (f : P3 →ₗ[D] N)
    (h : ∀ p ∈ Arel q, f p = 0) : A q →ₗ[D] N :=
  Submodule.liftQ ((Arel q).restrictScalars D) f
    (fun p hp => by rw [LinearMap.mem_ker]; exact h p hp)

@[simp] theorem descendN_mk {N : Type*} [AddCommGroup N] [Module D N] (f : P3 →ₗ[D] N)
    (h : ∀ p ∈ Arel q, f p = 0) (p : P3) : descendN q f h (mkA q p) = f p := rfl

/-! ### `Arel ≤ mP²`, hence low-degree coefficient functionals vanish -/

/-- Every generator of `Arel q` lies in `mP²`, so `Arel q ≤ mP²`. -/
theorem Arel_le_mP2 : Arel q ≤ mP ^ 2 := by
  have hX0 : (X 0 : P3) ∈ mP := by unfold mP; exact Ideal.subset_span (by simp)
  have hX1 : (X 1 : P3) ∈ mP := by unfold mP; exact Ideal.subset_span (by simp)
  have hX2 : (X 2 : P3) ∈ mP := by unfold mP; exact Ideal.subset_span (by simp)
  unfold Arel
  apply sup_le (Ideal.pow_le_pow_right (by norm_num))
  rw [Ideal.span_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  have hX0X2 : (X 0 * X 2 : P3) ∈ mP ^ 2 := by
    rw [pow_two]; exact Ideal.mul_mem_mul hX0 hX2
  have hX1sq : (X 1 ^ 2 : P3) ∈ mP ^ 2 := Ideal.pow_mem_pow hX1 2
  rcases hx with rfl | rfl | rfl | rfl
  · exact Ideal.pow_mem_pow hX0 2
  · rw [pow_two]; exact Ideal.mul_mem_mul hX0 hX1
  · exact sub_mem (Ideal.pow_mem_pow hX2 2) (by rw [pow_two]; exact Ideal.mul_mem_mul hX1 hX2)
  · exact Ideal.mul_mem_left _ _ (sub_mem hX0X2 hX1sq)

/-- A coefficient at a degree-`< 2` monomial vanishes on all of `Arel q`. -/
theorem coeff_eq_zero_of_Arel {p : P3} (hp : p ∈ Arel q) {m : Fin 3 →₀ ℕ}
    (hm : degree m < 2) : coeff m p = 0 := by
  have hmem : p ∈ idealOfVars (Fin 3) D ^ 2 := by rw [← mP_eq]; exact Arel_le_mP2 q hp
  rw [mem_pow_idealOfVars_iff'] at hmem
  exact hmem m hm

/-! ### The constant- and `eᵢ`-coordinate functionals (degree `≤ 1`) -/

/-- `χ₁ = coeff 1` (the augmentation / constant coordinate). -/
noncomputable def χ1 : A q →ₗ[D] D :=
  descendN q (lcoeff D 0) (fun _ hp => coeff_eq_zero_of_Arel q hp (by simp))
/-- `χ_{e₁} = coeff (X₀)`. -/
noncomputable def χe1 : A q →ₗ[D] D :=
  descendN q (lcoeff D (single 0 1))
    (fun _ hp => coeff_eq_zero_of_Arel q hp (by simp [Finsupp.degree_single]))
/-- `χ_{e₂} = coeff (X₁)`. -/
noncomputable def χe2 : A q →ₗ[D] D :=
  descendN q (lcoeff D (single 1 1))
    (fun _ hp => coeff_eq_zero_of_Arel q hp (by simp [Finsupp.degree_single]))
/-- `χ_{e₃} = coeff (X₂)`. -/
noncomputable def χe3 : A q →ₗ[D] D :=
  descendN q (lcoeff D (single 2 1))
    (fun _ hp => coeff_eq_zero_of_Arel q hp (by simp [Finsupp.degree_single]))

/-! ### The `u₁`-coordinate functional (degree `2`, reads `X₁X₂` and `X₂²`) -/

/-- `χ_{u₁} = coeff (X₁X₂) + coeff (X₂²)`. -/
noncomputable def χu1P : P3 →ₗ[D] D := lcoeff D m12 + lcoeff D m2sq

theorem χu1P_apply (p : P3) : χu1P p = coeff m12 p + coeff m2sq p := rfl

theorem degree_m12 : degree m12 = 2 := by rw [m12, map_add]; simp [Finsupp.degree_single]
theorem degree_m2sq : degree m2sq = 2 := by simp [m2sq, Finsupp.degree_single]

theorem χu1P_vanish_mP3 {y : P3} (hy : y ∈ mP ^ 3) : χu1P y = 0 := by
  rw [mP_eq, mem_pow_idealOfVars_iff'] at hy
  rw [χu1P_apply, hy m12 (by rw [degree_m12]; norm_num),
    hy m2sq (by rw [degree_m2sq]; norm_num), add_zero]

theorem χu1P_g1 (a : P3) : χu1P (a * X 0 ^ 2) = 0 := by
  rw [mul_comm, X0sq_eq, χu1P_apply, coeff_monomial_mul', coeff_monomial_mul',
    if_neg m0sq_not_le_m12, if_neg m0sq_not_le_m2sq, add_zero]

theorem χu1P_g2 (a : P3) : χu1P (a * (X 0 * X 1)) = 0 := by
  rw [mul_comm, X0X1_eq, χu1P_apply, coeff_monomial_mul', coeff_monomial_mul',
    if_neg m01_not_le_m12, if_neg m01_not_le_m2sq, add_zero]

theorem χu1P_g3 (a : P3) : χu1P (a * (X 2 ^ 2 - X 1 * X 2)) = 0 := by
  rw [mul_comm, sub_mul, χu1P_apply, coeff_sub, coeff_sub, X2sq_eq, X1X2_eq,
    coeff_monomial_mul', coeff_monomial_mul', coeff_monomial_mul', coeff_monomial_mul',
    if_neg m2sq_not_le_m12, if_pos le_rfl, if_pos le_rfl, if_neg m12_not_le_m2sq,
    tsub_self, tsub_self]
  ring

theorem χu1P_g4 (a : P3) :
    χu1P (a * (C (Polynomial.X ^ q) * (X 0 * X 2 - X 1 ^ 2))) = 0 := by
  rw [mul_comm, mul_assoc, χu1P_apply, coeff_C_mul, coeff_C_mul]
  have h1 : coeff m12 ((X 0 * X 2 - X 1 ^ 2) * a) = 0 := by
    rw [sub_mul, coeff_sub, X0X2_eq, X1sq_eq, coeff_monomial_mul', coeff_monomial_mul',
      if_neg m02_not_le_m12, if_neg m1sq_not_le_m12, sub_zero]
  have h2 : coeff m2sq ((X 0 * X 2 - X 1 ^ 2) * a) = 0 := by
    rw [sub_mul, coeff_sub, X0X2_eq, X1sq_eq, coeff_monomial_mul', coeff_monomial_mul',
      if_neg m02_not_le_m2sq, if_neg m1sq_not_le_m2sq, sub_zero]
  rw [h1, h2, mul_zero, add_zero]

/-- `χu1P` vanishes on all of `Arel q`. -/
theorem χu1P_vanish_Arel : ∀ p ∈ Arel q, χu1P p = 0 := by
  intro p hp
  unfold Arel at hp
  rw [Submodule.mem_sup] at hp
  obtain ⟨y, hy, z, hz, rfl⟩ := hp
  rw [map_add, χu1P_vanish_mP3 hy, zero_add]
  rw [Ideal.mem_span_insert] at hz
  obtain ⟨a1, z1, hz1, rfl⟩ := hz
  rw [Ideal.mem_span_insert] at hz1
  obtain ⟨a2, z2, hz2, rfl⟩ := hz1
  rw [Ideal.mem_span_insert] at hz2
  obtain ⟨a3, z3, hz3, rfl⟩ := hz2
  rw [Ideal.mem_span_singleton'] at hz3
  obtain ⟨a4, rfl⟩ := hz3
  rw [map_add, map_add, map_add, χu1P_g1, χu1P_g2, χu1P_g3, χu1P_g4,
    add_zero, add_zero, add_zero]

/-! ### The descended functionals as `A q`-objects -/

/-- `χ_{u₁} : A q →ₗ[D] D`. -/
noncomputable def χu1 : A q →ₗ[D] D := descendN q χu1P (χu1P_vanish_Arel q)
/-- `χ_{u₂} : A q →ₗ[D] D`. -/
noncomputable def χu2 : A q →ₗ[D] D := descendN q χu2P (χu2P_vanish_Arel q)
/-- `χ_s : A q →ₗ[D] D ⧸ (t^q)`. -/
noncomputable def χs : A q →ₗ[D] D ⧸ Ideal.span {(Polynomial.X : D) ^ q} :=
  descendN q (χsP q) (χsP_vanish_Arel q)

/-! ## A3 — the augmentation `aug : A q →+* D` and `J = ker aug` -/

/-- The augmentation at the polynomial level: evaluation of all `eᵢ` at `0`,
i.e. the constant coefficient. -/
noncomputable def augHom : P3 →+* D := (aeval (fun _ => (0 : D))).toRingHom

theorem augHom_apply (p : P3) : augHom p = constantCoeff p := by
  change aeval (fun _ => (0 : D)) p = constantCoeff p
  rw [aeval_zero']; simp

theorem augHom_vanish_Arel : ∀ a ∈ Arel q, augHom a = 0 := by
  have hker : mP ≤ RingHom.ker augHom := by
    unfold mP; rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl <;>
      · rw [SetLike.mem_coe, RingHom.mem_ker, augHom_apply]; simp
  intro a ha
  rw [← RingHom.mem_ker]
  exact hker (((Arel_le_mP2 q).trans (Ideal.pow_le_self (by norm_num))) ha)

/-- The augmentation `aug : A q →+* D` (kills `e₁,e₂,e₃`; restricts to `id` on `D`). -/
noncomputable def aug (q : ℕ) : A q →+* D :=
  Ideal.Quotient.lift (Arel q) augHom (augHom_vanish_Arel q)

@[simp] theorem aug_mk (p : P3) : aug q (mkA q p) = augHom p := rfl

/-- `aug` restricts to the identity on the scalars `D`. -/
theorem aug_algebraMap (d : D) : aug q (algebraMap D (A q) d) = d := by
  change aug q (mkA q (C d)) = d
  rw [aug_mk, augHom_apply]; simp

/-- **`J = ker aug`** — the augmentation ideal is the kernel of the augmentation. -/
theorem J_eq_ker : J q = RingHom.ker (aug q) := by
  apply le_antisymm
  · unfold J; rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · rw [SetLike.mem_coe, RingHom.mem_ker, e1_eq, aug_mk, augHom_apply]; simp
    · rw [SetLike.mem_coe, RingHom.mem_ker, e2_eq, aug_mk, augHom_apply]; simp
    · rw [SetLike.mem_coe, RingHom.mem_ker, e3_eq, aug_mk, augHom_apply]; simp
  · intro x hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hcc : constantCoeff p = 0 := by
      rwa [show aug q (Ideal.Quotient.mk (Arel q) p) = augHom p from rfl,
        augHom_apply] at hx
    rw [J_eq_map]
    apply Ideal.mem_map_of_mem
    rw [mP_eq, ← pow_one (idealOfVars (Fin 3) D), mem_pow_idealOfVars_iff']
    intro y hy
    rw [Nat.lt_one_iff, Finsupp.degree_eq_zero_iff] at hy
    subst hy
    rwa [← constantCoeff_eq]

/-! ## A2 (cont.) — `J² = W = (u₁,u₂,s)` -/

/-- `u₁ ∈ J²`. -/
theorem u1_mem_J2 : u₁ q ∈ J q ^ 2 := by
  rw [pow_two, ← e2_mul_e3]; exact Ideal.mul_mem_mul (e2_mem_J q) (e3_mem_J q)
/-- `u₂ ∈ J²`. -/
theorem u2_mem_J2 : u₂ q ∈ J q ^ 2 := by
  rw [pow_two]
  have : u₂ q = e₂ q * e₂ q := rfl
  rw [this]; exact Ideal.mul_mem_mul (e2_mem_J q) (e2_mem_J q)
/-- `s ∈ J²`. -/
theorem s_mem_J2 : s q ∈ J q ^ 2 := by
  have hrepr : s q = e₁ q * e₃ q - u₂ q := rfl
  rw [hrepr]
  exact sub_mem (by rw [pow_two]; exact Ideal.mul_mem_mul (e1_mem_J q) (e3_mem_J q))
    (u2_mem_J2 q)

/-- **`J² = (u₁,u₂,s)` as ideals.**  The degree-`2` products of `J`'s generators
reduce (mul table) to `{0, u₁, u₂, u₂+s}`, whose ideal span is `(u₁,u₂,s)`. -/
theorem J_sq_ideal : J q ^ 2 = Ideal.span {u₁ q, u₂ q, s q} := by
  apply le_antisymm
  · rw [pow_two]
    unfold J
    rw [Ideal.span_mul_span, Ideal.span_le]
    have hm1 : u₁ q ∈ Ideal.span {u₁ q, u₂ q, s q} := Ideal.subset_span (by simp)
    have hm2 : u₂ q ∈ Ideal.span {u₁ q, u₂ q, s q} := Ideal.subset_span (by simp)
    have hms : s q ∈ Ideal.span {u₁ q, u₂ q, s q} := Ideal.subset_span (by simp)
    rintro x ⟨a, ha, b, hb, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      simp only [SetLike.mem_coe, e1_mul_e1, e1_mul_e2, e2_mul_e1, e2_mul_e2, e2_mul_e3,
        e3_mul_e2, e1_mul_e3, e3_mul_e1, e3_mul_e3] <;>
      first
        | exact Submodule.zero_mem _
        | exact hm1
        | exact hm2
        | exact hms
        | exact Submodule.add_mem _ hm2 hms
  · rw [Ideal.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    exacts [u1_mem_J2 q, u2_mem_J2 q, s_mem_J2 q]

/-- **`J² = W`** as a `D`-module (`Submodule D`): `J²` restricted to `D`-scalars
equals the `D`-span of `{u₁, u₂, s}`.  The nontrivial direction uses that the
`eᵢ`-multiples of `J²` vanish (`J·J² = J³ = 0`), so the `A`-span collapses to the
`D`-span. -/
theorem J_sq : (J q ^ 2).restrictScalars D = Submodule.span D {u₁ q, u₂ q, s q} := by
  rw [J_sq_ideal]
  apply le_antisymm
  · intro x hx
    rw [Submodule.restrictScalars_mem] at hx
    refine Submodule.span_induction
      (p := fun x _ => x ∈ Submodule.span D {u₁ q, u₂ q, s q})
      (fun w hw => Submodule.subset_span hw) (Submodule.zero_mem _)
      (fun a b _ _ ha hb => Submodule.add_mem _ ha hb) ?_ hx
    intro a x _ hxD
    have hxJ2 : x ∈ J q ^ 2 := by
      have hle : Submodule.span D {u₁ q, u₂ q, s q} ≤ (J q ^ 2).restrictScalars D :=
        Submodule.span_le.mpr (by
          intro w hw
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
          rcases hw with rfl | rfl | rfl
          · exact u1_mem_J2 q
          · exact u2_mem_J2 q
          · exact s_mem_J2 q)
      exact hle hxD
    have hj : a - algebraMap D (A q) (aug q a) ∈ J q := by
      rw [J_eq_ker, RingHom.mem_ker, map_sub, aug_algebraMap, sub_self]
    have hzero : (a - algebraMap D (A q) (aug q a)) * x = 0 := by
      have hmem : (a - algebraMap D (A q) (aug q a)) * x ∈ J q ^ 3 := by
        rw [pow_succ']; exact Ideal.mul_mem_mul hj hxJ2
      rwa [J_pow_three, Ideal.mem_bot] at hmem
    have hsplit : a • x = aug q a • x := by
      rw [smul_eq_mul, ← sub_eq_zero, Algebra.smul_def, ← sub_mul, hzero]
    rw [hsplit]
    exact Submodule.smul_mem _ _ hxD
  · rw [Submodule.span_le]
    intro w hw
    exact Ideal.subset_span hw

/-! ## Mandatory Stage-A validation examples (BLUEPRINT cheat-watch)

These certify the modeling is *live*: the multiplication table holds, the torsion
relation `t^q·s = 0` holds, and the nonvanishings `u₂ ≠ 0` (free) /
`t^{q−1}·s ≠ 0` (torsion-but-nonzero) go through the coordinate functionals. -/

example : e₂ q ^ 2 = u₂ q := e2_sq q
example : e₃ q ^ 2 = e₂ q * e₃ q := by rw [e3_sq, e2_mul_e3]
example : tA q ^ q * s q = 0 := t_pow_q_mul_s q
example : u₂ q ≠ 0 := u2_ne_zero q
example (hq : 0 < q) : tA q ^ (q - 1) * s q ≠ 0 := t_pow_pred_mul_s_ne_zero q hq

end Prob30c
