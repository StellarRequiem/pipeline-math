/-
Copyright (c) 2026 Prob30c formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob30c formalization
-/
import Prob30c.Proofs.RingModel.Basic
import Prob30c.Proofs.Cancellation.Basic

/-!
# Stage UA — `A_succAbsorbing`, the down-stairs upper bound (Step 3 upper).

`A_succAbsorbing_proof q (hq : 2 ≤ q) : IsNAbsorbing (q + 1) (⊥ : Ideal (A q))`.

Every family `a : Fin (q+2) → A q` with `∏ a = 0` has an omit-one subproduct `= 0`.
Equivalently: every *irredundant* zero-product in `A q` (all `q+2` omit-one
products nonzero) is impossible at length `q+2`.  We argue by contradiction on
`k := #{i | a i ∈ J q}` (using the augmentation `aug : A q →+* D`, whose kernel is
`J q`, and the domain `D`):

* **`k ≥ 3`.**  `J³ = 0` makes any product containing three `J`-factors vanish; as
  `q+2 ≥ 4` we can omit a fourth index and still keep three `J`-factors, so an
  omit-one product already vanishes.
* **`k = 2` / `k = 1`.**  The product of the `J`-factors lands (after the free
  `u₁,u₂` coordinates are forced to vanish) in the `s`-layer `γ • s`, with
  `γ`-divisibility `X^r ∣ γ` (`r = 1` from `cancel_const` when `k = 2`, `r = 0`
  when `k = 1`).  A `t`-adic valuation count over the domain `D` (`dvd_count`)
  caps the number of out-of-`J` factors, contradicting the length `q + 2`.

The arithmetic core `dvd_count` and the `s`-layer reduction `core_count` are
exported for reuse by Stage UX.  All (non)vanishing in `A q` routes through the
Stage-A coordinate functionals `χu1, χu2, χs, χe_i`; nothing uses `decide` over
`A q`.
-/

namespace Prob30c

open Polynomial MvPolynomial Finsupp

variable (q : ℕ)

/-! ## The `t`-adic valuation count over `D` (the arithmetic core) -/

/-- **Valuation count.**  In the domain `D = 𝔽₂[t]`, if a product `(∏ g) · γ` of
`t = X`-factors is divisible by `t^q`, while every omit-one product is *not*, and
`t^r ∣ γ`, then the number of factors is bounded: `|t| + r ≤ q`. -/
theorem dvd_count {ι : Type*} [DecidableEq ι] {q r : ℕ} (t : Finset ι) (ht : t.Nonempty)
    (g : ι → D) (γ : D)
    (hfull : (Polynomial.X : D) ^ q ∣ (∏ i ∈ t, g i) * γ)
    (hγ : (Polynomial.X : D) ^ r ∣ γ)
    (homit : ∀ j ∈ t, ¬ (Polynomial.X : D) ^ q ∣ (∏ i ∈ t.erase j, g i) * γ) :
    t.card + r ≤ q := by
  classical
  -- Each factor is divisible by `X` (else coprime cancellation contradicts `homit`).
  have hXg : ∀ i ∈ t, (Polynomial.X : D) ∣ g i := by
    intro i hi
    by_contra hni
    apply homit i hi
    have hsplit : (∏ j ∈ t, g j) * γ = g i * ((∏ j ∈ t.erase i, g j) * γ) := by
      rw [← Finset.mul_prod_erase t g hi, mul_assoc]
    rw [hsplit] at hfull
    exact (Polynomial.prime_X).pow_dvd_of_dvd_mul_left q hni hfull
  -- The count.
  by_contra hlt
  rw [not_le] at hlt
  have hcard : 1 ≤ t.card := Finset.card_pos.mpr ht
  obtain ⟨j, hj⟩ := ht
  apply homit j hj
  have hpe : (Polynomial.X : D) ^ (t.card - 1) ∣ ∏ i ∈ t.erase j, g i := by
    have h1 : (∏ _i ∈ t.erase j, (Polynomial.X : D)) ∣ ∏ i ∈ t.erase j, g i :=
      Finset.prod_dvd_prod_of_dvd (fun _ => Polynomial.X) g
        (fun i hi => hXg i (Finset.mem_of_mem_erase hi))
    rwa [Finset.prod_const, Finset.card_erase_of_mem hj] at h1
  have hdvd2 : (Polynomial.X : D) ^ ((t.card - 1) + r) ∣ (∏ i ∈ t.erase j, g i) * γ := by
    rw [pow_add]; exact mul_dvd_mul hpe hγ
  have hqle : q ≤ (t.card - 1) + r := by omega
  exact dvd_trans (pow_dvd_pow _ hqle) hdvd2

/-! ## The `s`-coordinate functional `χs` on `mkA`-images and the generators -/

theorem χs_mk (p : P3) : χs q (mkA q p) = χsP q p := rfl

/-- `χs q (s q) = [1]` (the `s`-coordinate of `s`, modulo `t^q`). -/
theorem χs_s : χs q (s q) = (Ideal.span {(Polynomial.X : D) ^ q}).mkQ 1 := by
  rw [s_eq, χs_mk, χsP_apply, coeff_sub, X0X2_eq, X1sq_eq,
    MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial,
    if_pos rfl, if_neg m1sq_ne_m02, sub_zero]

theorem χs_u1 : χs q (u₁ q) = 0 := by
  have h : u₁ q = mkA q (X 1 * X 2) := by rw [← e2_mul_e3, e2_eq, e3_eq, ← map_mul]
  rw [h, χs_mk, χsP_apply, X1X2_eq, MvPolynomial.coeff_monomial, if_neg m12_ne_m02, map_zero]

theorem χs_u2 : χs q (u₂ q) = 0 := by
  have h : u₂ q = mkA q (X 1 ^ 2) := by rw [← e2_sq, e2_eq, ← map_pow]
  rw [h, χs_mk, χsP_apply, X1sq_eq, MvPolynomial.coeff_monomial, if_neg m1sq_ne_m02, map_zero]

/-- **Annihilator of `s`.**  `e • s = 0 ⇔ t^q ∣ e`: the `s`-layer is exactly the
torsion module `D ⧸ (t^q)`. -/
theorem smul_s_eq_zero_iff (e : D) : e • s q = 0 ↔ (Polynomial.X : D) ^ q ∣ e := by
  constructor
  · intro he
    have hh : χs q (e • s q) = 0 := by rw [he, map_zero]
    rw [map_smul, χs_s] at hh
    rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one] at hh
    rw [← Ideal.mem_span_singleton]
    rwa [Submodule.Quotient.mk_eq_zero] at hh
  · intro hdvd
    obtain ⟨f, rfl⟩ := hdvd
    rw [mul_comm, mul_smul]
    have hxs : (Polynomial.X : D) ^ q • s q = tA q ^ q * s q := by
      rw [Algebra.smul_def, map_pow]; rfl
    rw [hxs, t_pow_q_mul_s, smul_zero]

/-! ## Reducing a `J²`-element times anything to a scalar action -/

/-- For `z ∈ J²`, multiplication by any `w` collapses to scalar action by the
augmentation: `w * z = aug w • z` (the `J`-part of `w` kills `z` via `J³ = 0`). -/
theorem mul_J2_eq_aug_smul (w : A q) {z : A q} (hz : z ∈ J q ^ 2) :
    w * z = aug q w • z := by
  have hj : w - algebraMap D (A q) (aug q w) ∈ J q := by
    rw [J_eq_ker, RingHom.mem_ker, map_sub, aug_algebraMap, sub_self]
  have hzero : (w - algebraMap D (A q) (aug q w)) * z = 0 := by
    have hmem : (w - algebraMap D (A q) (aug q w)) * z ∈ J q ^ 3 := by
      rw [pow_succ']; exact Ideal.mul_mem_mul hj hz
    rwa [J_pow_three, Ideal.mem_bot] at hmem
  have heq : w * z = algebraMap D (A q) (aug q w) * z := by
    rw [← sub_eq_zero, ← sub_mul, hzero]
  rw [heq, Algebra.smul_def]

/-- Every `z ∈ J²` decomposes as `α • u₁ + β • u₂ + γ • s` over `D`. -/
theorem J2_decomp {z : A q} (hz : z ∈ J q ^ 2) :
    ∃ α β γ : D, z = α • u₁ q + β • u₂ q + γ • s q := by
  have hz2 : z ∈ Submodule.span D {u₁ q, u₂ q, s q} := by rw [← J_sq]; exact hz
  rw [Submodule.mem_span_insert] at hz2
  obtain ⟨α, z₁, hz₁, rfl⟩ := hz2
  rw [Submodule.mem_span_insert] at hz₁
  obtain ⟨β, z₂, hz₂, rfl⟩ := hz₁
  rw [Submodule.mem_span_singleton] at hz₂
  obtain ⟨γ, rfl⟩ := hz₂
  exact ⟨α, β, γ, by rw [add_assoc]⟩

/-- If `z ∈ J²` is killed by a nonzero scalar `e`, then its free `u₁,u₂`
coordinates vanish, so `z` lies in the `s`-layer: `z = γ • s`. -/
theorem eq_s_smul_of_torsion {z : A q} (hz : z ∈ J q ^ 2) {e : D} (he : e ≠ 0)
    (h0 : e • z = 0) : ∃ γ : D, z = γ • s q := by
  obtain ⟨α, β, γ, rfl⟩ := J2_decomp q hz
  have hα : e * α = 0 := by
    have h1 : χu1 q (e • (α • u₁ q + β • u₂ q + γ • s q)) = e * α := by
      simp only [map_smul, map_add, χu1_u1, χu1_u2, χu1_s, smul_eq_mul, mul_one, mul_zero,
        add_zero]
    rw [h0, map_zero] at h1; exact h1.symm
  have hβ : e * β = 0 := by
    have h1 : χu2 q (e • (α • u₁ q + β • u₂ q + γ • s q)) = e * β := by
      simp only [map_smul, map_add, χu2_u1, χu2_u2, χu2_s, smul_eq_mul, mul_one, mul_zero,
        add_zero, zero_add]
    rw [h0, map_zero] at h1; exact h1.symm
  have hα0 : α = 0 := by rcases mul_eq_zero.mp hα with h | h; exacts [absurd h he, h]
  have hβ0 : β = 0 := by rcases mul_eq_zero.mp hβ with h | h; exacts [absurd h he, h]
  exact ⟨γ, by rw [hα0, hβ0, zero_smul, zero_smul, zero_add, zero_add]⟩

/-! ## The `s`-layer count: the unified `k = 1` / `k = 2` engine -/

/-- **Core count.**  Suppose the `J`-product reduced to `γ • s`, every out-of-`J`
factor `c i` (`i ∈ t`) has `aug (c i) ≠ 0`, `t^r ∣ γ`, the full product
`(γ•s)·∏ c = 0`, and every omit-one (omitting one `c`-factor) is nonzero.  Then
`t.card + r ≤ q`. -/
theorem core_count {ι : Type*} [DecidableEq ι] (q : ℕ) (γ : D) (t : Finset ι)
    (ht : t.Nonempty) (c : ι → A q) (_hct : ∀ i ∈ t, aug q (c i) ≠ 0) (r : ℕ)
    (hγr : (Polynomial.X : D) ^ r ∣ γ)
    (hfull : (γ • s q) * (∏ i ∈ t, c i) = 0)
    (homit : ∀ j ∈ t, (γ • s q) * (∏ i ∈ t.erase j, c i) ≠ 0) :
    t.card + r ≤ q := by
  classical
  have hsJ2 : γ • s q ∈ J q ^ 2 := by
    rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ (s_mem_J2 q)
  have hred : ∀ u : Finset ι,
      (γ • s q) * (∏ i ∈ u, c i) = ((∏ i ∈ u, aug q (c i)) * γ) • s q := by
    intro u
    rw [mul_comm, mul_J2_eq_aug_smul q (∏ i ∈ u, c i) hsJ2, map_prod, smul_smul]
  have hfull' : (Polynomial.X : D) ^ q ∣ (∏ i ∈ t, aug q (c i)) * γ := by
    rw [← smul_s_eq_zero_iff q, ← hred t]; exact hfull
  have homit' : ∀ j ∈ t,
      ¬ (Polynomial.X : D) ^ q ∣ (∏ i ∈ t.erase j, aug q (c i)) * γ := by
    intro j hj hdvd
    apply homit j hj
    rw [hred (t.erase j), smul_s_eq_zero_iff q]
    exact hdvd
  exact dvd_count t ht (fun i => aug q (c i)) γ hfull' hγr homit'

/-! ## The degree-1 coordinate functionals (for the `k = 1` reduction) -/

theorem χe1_mk (p : P3) : χe1 q (mkA q p) = MvPolynomial.coeff (single 0 1) p := rfl
theorem χe2_mk (p : P3) : χe2 q (mkA q p) = MvPolynomial.coeff (single 1 1) p := rfl
theorem χe3_mk (p : P3) : χe3 q (mkA q p) = MvPolynomial.coeff (single 2 1) p := rfl

/-- `single a 1 ≠ single b 1` for `a ≠ b`. -/
theorem single_ne {a b : Fin 3} (h : a ≠ b) : (single a 1 : Fin 3 →₀ ℕ) ≠ single b 1 :=
  fun he => h (Finsupp.single_left_injective one_ne_zero he)

/-- `single i 1` (degree 1) differs from any degree-2 exponent vector. -/
theorem single_ne_deg2 (i : Fin 3) {m : Fin 3 →₀ ℕ} (hm : Finsupp.degree m = 2) :
    (single i 1 : Fin 3 →₀ ℕ) ≠ m := by
  intro he; rw [← he] at hm; simp [Finsupp.degree_single] at hm

theorem χe1_e1 : χe1 q (e₁ q) = 1 := by rw [e1_eq, χe1_mk, MvPolynomial.coeff_X, if_pos rfl]
theorem χe1_e2 : χe1 q (e₂ q) = 0 := by
  rw [e2_eq, χe1_mk, MvPolynomial.coeff_X, if_neg (single_ne (by decide))]
theorem χe1_e3 : χe1 q (e₃ q) = 0 := by
  rw [e3_eq, χe1_mk, MvPolynomial.coeff_X, if_neg (single_ne (by decide))]
theorem χe2_e1 : χe2 q (e₁ q) = 0 := by
  rw [e1_eq, χe2_mk, MvPolynomial.coeff_X, if_neg (single_ne (by decide))]
theorem χe2_e2 : χe2 q (e₂ q) = 1 := by rw [e2_eq, χe2_mk, MvPolynomial.coeff_X, if_pos rfl]
theorem χe2_e3 : χe2 q (e₃ q) = 0 := by
  rw [e3_eq, χe2_mk, MvPolynomial.coeff_X, if_neg (single_ne (by decide))]
theorem χe3_e1 : χe3 q (e₁ q) = 0 := by
  rw [e1_eq, χe3_mk, MvPolynomial.coeff_X, if_neg (single_ne (by decide))]
theorem χe3_e2 : χe3 q (e₂ q) = 0 := by
  rw [e2_eq, χe3_mk, MvPolynomial.coeff_X, if_neg (single_ne (by decide))]
theorem χe3_e3 : χe3 q (e₃ q) = 1 := by rw [e3_eq, χe3_mk, MvPolynomial.coeff_X, if_pos rfl]

/-- The degree-1 functionals vanish on the degree-2 monomial `u₁ = X₁X₂`. -/
theorem χei_u1 (i : Fin 3) (χ : A q →ₗ[D] D)
    (hχ : ∀ p, χ (mkA q p) = MvPolynomial.coeff (single i 1) p) : χ (u₁ q) = 0 := by
  have h : u₁ q = mkA q (X 1 * X 2) := by rw [← e2_mul_e3, e2_eq, e3_eq, ← map_mul]
  rw [h, hχ, X1X2_eq, MvPolynomial.coeff_monomial,
    if_neg ((single_ne_deg2 i degree_m12).symm)]
theorem χei_u2 (i : Fin 3) (χ : A q →ₗ[D] D)
    (hχ : ∀ p, χ (mkA q p) = MvPolynomial.coeff (single i 1) p) : χ (u₂ q) = 0 := by
  have h : u₂ q = mkA q (X 1 ^ 2) := by rw [← e2_sq, e2_eq, ← map_pow]
  rw [h, hχ, X1sq_eq, MvPolynomial.coeff_monomial,
    if_neg ((single_ne_deg2 i degree_m1sq).symm)]
theorem χei_s (i : Fin 3) (χ : A q →ₗ[D] D)
    (hχ : ∀ p, χ (mkA q p) = MvPolynomial.coeff (single i 1) p) : χ (s q) = 0 := by
  rw [s_eq, hχ, coeff_sub, X0X2_eq, X1sq_eq, MvPolynomial.coeff_monomial,
    MvPolynomial.coeff_monomial, if_neg ((single_ne_deg2 i degree_m02).symm),
    if_neg ((single_ne_deg2 i degree_m1sq).symm), sub_zero]

/-- The degree-1 functionals vanish on all of `J²`. -/
theorem χe1_J2 {w : A q} (hw : w ∈ J q ^ 2) : χe1 q w = 0 := by
  obtain ⟨α, β, γ, rfl⟩ := J2_decomp q hw
  simp only [map_add, map_smul, χei_u1 q 0 (χe1 q) (χe1_mk q),
    χei_u2 q 0 (χe1 q) (χe1_mk q), χei_s q 0 (χe1 q) (χe1_mk q), smul_zero, add_zero]
theorem χe2_J2 {w : A q} (hw : w ∈ J q ^ 2) : χe2 q w = 0 := by
  obtain ⟨α, β, γ, rfl⟩ := J2_decomp q hw
  simp only [map_add, map_smul, χei_u1 q 1 (χe2 q) (χe2_mk q),
    χei_u2 q 1 (χe2 q) (χe2_mk q), χei_s q 1 (χe2 q) (χe2_mk q), smul_zero, add_zero]
theorem χe3_J2 {w : A q} (hw : w ∈ J q ^ 2) : χe3 q w = 0 := by
  obtain ⟨α, β, γ, rfl⟩ := J2_decomp q hw
  simp only [map_add, map_smul, χei_u1 q 2 (χe3 q) (χe3_mk q),
    χei_u2 q 2 (χe3 q) (χe3_mk q), χei_s q 2 (χe3 q) (χe3_mk q), smul_zero, add_zero]

/-- A `J`-element whose three degree-1 coordinates vanish lies in `J²`. -/
theorem mem_J2_of_χe_zero {z : A q} (hz : z ∈ J q) (h1 : χe1 q z = 0) (h2 : χe2 q z = 0)
    (h3 : χe3 q z = 0) : z ∈ J q ^ 2 := by
  obtain ⟨a₁, a₂, a₃, w, hw, rfl⟩ := J_decomp q hz
  have ha1 : a₁ = 0 := by
    have hc := h1
    simp only [map_add, map_smul, χe1_e1, χe1_e2, χe1_e3, χe1_J2 q hw, smul_eq_mul,
      mul_one, mul_zero, add_zero] at hc
    exact hc
  have ha2 : a₂ = 0 := by
    have hc := h2
    simp only [map_add, map_smul, χe2_e1, χe2_e2, χe2_e3, χe2_J2 q hw, smul_eq_mul,
      mul_one, mul_zero, add_zero, zero_add] at hc
    exact hc
  have ha3 : a₃ = 0 := by
    have hc := h3
    simp only [map_add, map_smul, χe3_e1, χe3_e2, χe3_e3, χe3_J2 q hw, smul_eq_mul,
      mul_one, mul_zero, add_zero, zero_add] at hc
    exact hc
  rw [ha1, ha2, ha3, zero_smul, zero_smul, zero_smul, zero_add, zero_add, zero_add]
  exact hw

/-! ## Product of `J`-members lies in a power of `J` (for the `k ≥ 3` case) -/

theorem prod_mem_Jpow {ι : Type*} (u : Finset ι) (a : ι → A q)
    (h : ∀ i ∈ u, a i ∈ J q) : ∏ i ∈ u, a i ∈ J q ^ u.card := by
  classical
  induction u using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.card_insert_of_notMem hx, pow_succ']
    exact Ideal.mul_mem_mul (h x (Finset.mem_insert_self x s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-! ## `A_succAbsorbing` — the down-stairs upper bound -/

/-- **`A_succAbsorbing` (Step 3 upper).**  `⊥ : Ideal (A q)` is `(q+1)`-absorbing:
every product of `q+2` elements that vanishes has an omit-one subproduct that
already vanishes. -/
theorem A_succAbsorbing_proof (q : ℕ) (hq : 2 ≤ q) :
    IsNAbsorbing (q + 1) (⊥ : Ideal (A q)) := by
  classical
  intro a hprod
  rw [Ideal.mem_bot] at hprod
  by_contra hcon
  simp only [not_exists] at hcon
  -- all omit-one products are nonzero
  have hirr : ∀ j : Fin (q + 2), (∏ i ∈ Finset.univ.erase j, a i) ≠ 0 := by
    intro j hj; exact hcon j (by rw [Ideal.mem_bot]; exact hj)
  -- the set of `J`-indices and its complement
  set S : Finset (Fin (q + 2)) := Finset.univ.filter (fun i => a i ∈ J q) with hS
  set T : Finset (Fin (q + 2)) := Finset.univ.filter (fun i => a i ∉ J q) with hT
  have hpart : (∏ i ∈ S, a i) * (∏ i ∈ T, a i) = ∏ i, a i :=
    Finset.prod_filter_mul_prod_filter_not _ _ _
  have hcardST : S.card + T.card = q + 2 := by
    rw [hS, hT, Finset.card_filter_add_card_filter_not, Finset.card_univ,
      Fintype.card_fin]
  have haugT : ∀ i ∈ T, aug q (a i) ≠ 0 := by
    intro i hi
    rw [hT, Finset.mem_filter] at hi
    rw [J_eq_ker, RingHom.mem_ker] at hi
    exact hi.2
  have hprodT_ne : (∏ i ∈ T, aug q (a i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr haugT
  -- relate the omit-one product (omitting a `T`-index) to `(∏_S) * (∏_{T.erase j})`
  have homit_split : ∀ j ∈ T,
      (∏ i ∈ S, a i) * (∏ i ∈ T.erase j, a i) = ∏ i ∈ Finset.univ.erase j, a i := by
    intro j hj
    have hdisj : Disjoint S (T.erase j) :=
      (Finset.disjoint_filter_filter_not Finset.univ Finset.univ
        (fun i => a i ∈ J q)).mono_right (Finset.erase_subset _ _)
    rw [← Finset.prod_union hdisj]
    apply Finset.prod_congr _ (fun _ _ => rfl)
    rw [hT, Finset.mem_filter] at hj
    ext i
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, and_true,
      Finset.mem_erase, hS, hT]
    constructor
    · rintro (h | ⟨h, _⟩)
      · intro heq; exact hj.2 (heq ▸ h)
      · exact h
    · intro hij
      by_cases hiJ : a i ∈ J q
      · exact Or.inl hiJ
      · exact Or.inr ⟨hij, hiJ⟩
  -- `k = 0` is impossible (`∏ aug (a i) = aug 0 = 0` among nonzeros)
  by_cases h0 : S.card = 0
  · rw [Finset.card_eq_zero] at h0
    have hTall : ∀ i : Fin (q + 2), i ∈ T := by
      intro i
      rw [hT, Finset.mem_filter]
      refine ⟨Finset.mem_univ i, ?_⟩
      intro hiJ
      have : i ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ i, hiJ⟩
      rw [h0] at this; exact absurd this (Finset.notMem_empty i)
    have hz : aug q (∏ i, a i) = 0 := by rw [hprod, map_zero]
    rw [map_prod, Finset.prod_eq_zero_iff] at hz
    obtain ⟨i, _, hi⟩ := hz
    exact haugT i (hTall i) hi
  -- `S.card ≤ q + 1`, so `T` is nonempty
  have hScardlt : S.card < q + 2 := by
    by_contra hge
    rw [not_lt] at hge
    have hSU : S = Finset.univ :=
      Finset.eq_univ_of_card S (by
        have hle := Finset.card_le_univ S
        rw [Fintype.card_fin] at hle ⊢; omega)
    have hSall : ∀ i : Fin (q + 2), a i ∈ J q := by
      intro i
      have : i ∈ S := by rw [hSU]; exact Finset.mem_univ i
      rw [hS, Finset.mem_filter] at this; exact this.2
    have hq2 : 0 < q + 2 := by omega
    apply hirr ⟨0, hq2⟩
    have hcarderase : (Finset.univ.erase (⟨0, hq2⟩ : Fin (q + 2))).card = q + 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    have hmem : ∏ i ∈ Finset.univ.erase (⟨0, hq2⟩ : Fin (q + 2)), a i
        ∈ J q ^ (Finset.univ.erase (⟨0, hq2⟩ : Fin (q + 2))).card :=
      prod_mem_Jpow q _ a (fun i _ => hSall i)
    rw [hcarderase] at hmem
    have hle : J q ^ (q + 1) ≤ J q ^ 3 := Ideal.pow_le_pow_right (by omega)
    rw [J_pow_three] at hle
    exact Ideal.mem_bot.mp (hle hmem)
  have hTne : T.Nonempty := by rw [← Finset.card_pos]; omega
  -- `k ≥ 3`: omit a `T`-index, keep all `S.card ≥ 3` `J`-factors
  by_cases h3 : 3 ≤ S.card
  · obtain ⟨j, hjT⟩ := hTne
    apply hirr j
    rw [← homit_split j hjT]
    have hSmem : ∏ i ∈ S, a i ∈ J q ^ S.card :=
      prod_mem_Jpow q S a (fun i hi => by rw [hS, Finset.mem_filter] at hi; exact hi.2)
    have hle : J q ^ S.card ≤ J q ^ 3 := Ideal.pow_le_pow_right h3
    rw [J_pow_three] at hle
    rw [Ideal.mem_bot.mp (hle hSmem), zero_mul]
  rw [not_le] at h3  -- S.card < 3
  -- common setup: the `J`-product `z := ∏_S a`
  set z : A q := ∏ i ∈ S, a i with hzdef
  have hfullz : z * (∏ i ∈ T, a i) = 0 := by rw [hzdef, hpart, hprod]
  have homitz : ∀ j ∈ T, z * (∏ i ∈ T.erase j, a i) ≠ 0 := by
    intro j hj; rw [hzdef, homit_split j hj]; exact hirr j
  -- `S.card ∈ {1, 2}`
  rcases (by omega : S.card = 1 ∨ S.card = 2) with hk | hk
  · -- `k = 1`: show `z ∈ J²` via the degree-1 functionals, then reduce
    have hTcard : T.card = q + 1 := by omega
    obtain ⟨i₀, hSi₀⟩ := Finset.card_eq_one.mp hk
    have hziJ : z ∈ J q := by
      rw [hzdef, hSi₀, Finset.prod_singleton]
      have : i₀ ∈ S := by rw [hSi₀]; exact Finset.mem_singleton_self i₀
      rw [hS, Finset.mem_filter] at this; exact this.2
    set C : A q := ∏ i ∈ T, a i with hC
    have hdne : aug q C ≠ 0 := by rw [hC, map_prod]; exact hprodT_ne
    have hdz_mem : (aug q C) • z ∈ J q ^ 2 := by
      have hCsplit : C - algebraMap D (A q) (aug q C) ∈ J q := by
        rw [J_eq_ker, RingHom.mem_ker, map_sub, aug_algebraMap, sub_self]
      have hexp : (aug q C) • z = - (z * (C - algebraMap D (A q) (aug q C))) := by
        rw [mul_sub, hfullz, Algebra.smul_def]; ring
      rw [hexp]
      exact Submodule.neg_mem _ (by rw [pow_two]; exact Ideal.mul_mem_mul hziJ hCsplit)
    have hχe : ∀ (χ : A q →ₗ[D] D), χ ((aug q C) • z) = 0 → χ z = 0 := by
      intro χ hχ0
      rw [map_smul, smul_eq_mul] at hχ0
      rcases mul_eq_zero.mp hχ0 with h' | h'
      · exact absurd h' hdne
      · exact h'
    have hzJ2 : z ∈ J q ^ 2 :=
      mem_J2_of_χe_zero q hziJ (hχe (χe1 q) (χe1_J2 q hdz_mem))
        (hχe (χe2 q) (χe2_J2 q hdz_mem)) (hχe (χe3 q) (χe3_J2 q hdz_mem))
    have h0z : (∏ i ∈ T, aug q (a i)) • z = 0 := by
      have hh : z * (∏ i ∈ T, a i) = (∏ i ∈ T, aug q (a i)) • z := by
        rw [mul_comm, mul_J2_eq_aug_smul q _ hzJ2, map_prod]
      rw [← hh]; exact hfullz
    obtain ⟨γ, hγeq⟩ := eq_s_smul_of_torsion q hzJ2 hprodT_ne h0z
    have hb := core_count q γ T hTne a haugT 0 (by simp)
      (by rw [← hγeq]; exact hfullz) (fun j hj => by rw [← hγeq]; exact homitz j hj)
    omega
  · -- `k = 2`: `z = a i₁ * a i₂ ∈ J²`; use `cancel_const` for `X ∣ γ`
    have hTcard : T.card = q := by omega
    obtain ⟨i₁, i₂, hne, hSi⟩ := Finset.card_eq_two.mp hk
    have hi₁ : a i₁ ∈ J q := by
      have : i₁ ∈ S := by rw [hSi]; exact Finset.mem_insert_self _ _
      rw [hS, Finset.mem_filter] at this; exact this.2
    have hi₂ : a i₂ ∈ J q := by
      have : i₂ ∈ S := by rw [hSi]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      rw [hS, Finset.mem_filter] at this; exact this.2
    have hzi : z = a i₁ * a i₂ := by
      rw [hzdef, hSi, Finset.prod_insert (by simp [hne]), Finset.prod_singleton]
    have hzJ2 : z ∈ J q ^ 2 := by rw [hzi, pow_two]; exact Ideal.mul_mem_mul hi₁ hi₂
    have h0z : (∏ i ∈ T, aug q (a i)) • z = 0 := by
      have hh : z * (∏ i ∈ T, a i) = (∏ i ∈ T, aug q (a i)) • z := by
        rw [mul_comm, mul_J2_eq_aug_smul q _ hzJ2, map_prod]
      rw [← hh]; exact hfullz
    obtain ⟨γ, hγeq⟩ := eq_s_smul_of_torsion q hzJ2 hprodT_ne h0z
    -- `z ∈ sComponent`, hence `z ∈ tSComponent` by `cancel_const`
    have hzs : z ∈ sComponent q := by
      rw [hγeq, sComponent]
      exact Submodule.smul_mem _ γ (Submodule.mem_span_singleton_self _)
    have hzts : z ∈ tSComponent q := by
      rw [hzi]
      exact cancel_const_proof q (a i₁) (a i₂) hi₁ hi₂ (by rw [← hzi]; exact hzs)
    rw [tSComponent, Submodule.mem_span_singleton] at hzts
    obtain ⟨δ, hδ⟩ := hzts
    have hXγ : (Polynomial.X : D) ∣ γ := by
      -- Pass through the torsion coordinate `χs` (D-side) to read `X ∣ γ`.
      have hts : tA q * s q = (Polynomial.X : D) • s q := by rw [tA, Algebra.smul_def]
      have h1 : χs q z = (Ideal.span {(Polynomial.X : D) ^ q}).mkQ γ := by
        rw [hγeq, map_smul, χs_s, ← map_smul, smul_eq_mul, mul_one]
      have h2 : χs q z = (Ideal.span {(Polynomial.X : D) ^ q}).mkQ (δ * Polynomial.X) := by
        rw [← hδ, map_smul, hts, map_smul, χs_s, ← map_smul, smul_eq_mul, mul_one,
          ← map_smul, smul_eq_mul]
      have hco : (Ideal.span {(Polynomial.X : D) ^ q}).mkQ (γ - δ * Polynomial.X) = 0 := by
        rw [map_sub, ← h1, ← h2, sub_self]
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton] at hco
      have h3 : (Polynomial.X : D) ∣ (γ - δ * Polynomial.X) :=
        dvd_trans (dvd_pow_self _ (by omega : q ≠ 0)) hco
      have h4 : (Polynomial.X : D) ∣ δ * Polynomial.X := dvd_mul_left _ _
      have h5 := dvd_add h3 h4
      rwa [sub_add_cancel] at h5
    have hb := core_count q γ T hTne a haugT 1 (by rwa [pow_one])
      (by rw [← hγeq]; exact hfullz) (fun j hj => by rw [← hγeq]; exact homitz j hj)
    omega

end Prob30c
