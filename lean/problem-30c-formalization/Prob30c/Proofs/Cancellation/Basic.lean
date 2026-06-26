/-
Copyright (c) 2026 Prob30c formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob30c formalization
-/
import Prob30c.Proofs.RingModel.Basic

/-!
# Stage C — `cancel_const`, the constant cancellation (Step 2).

For `x, y ∈ J`, if `x*y ∈ sComponent` (the `(D/t^q)·s` layer) then in fact
`x*y ∈ tSComponent` (`t·(D/t^q)·s`).  The mechanism is the characteristic-`2`
cancellation `α + α = 0`: writing `x, y` in the `D`-basis of `J`, the product
`x*y` is a degree-`2` form whose `u₁`- and `u₂`-coordinates are forced to vanish
by the hypothesis, and the `s`-coordinate is then forced to be divisible by `t`.

The whole argument lives on the `Submodule D` side, using the Stage-A
multiplication table, `J³ = 0`, and the coordinate functionals `χu1`, `χu2`.
-/

namespace Prob30c

open MvPolynomial Finsupp

variable (q : ℕ)

/-! ## Auxiliary monomial inequalities (for reading `χ`-coordinates) -/

theorem m02_ne_m1sq : m02 ≠ m1sq := fun h => m1sq_ne_m02 h.symm
theorem m12_ne_m02 : m12 ≠ m02 := by
  intro h; apply_fun (· 0) at h
  simp [m12, m02, Finsupp.add_apply] at h
theorem m12_ne_m1sq : m12 ≠ m1sq := by
  intro h; apply_fun (· 2) at h
  simp [m12, m1sq, Finsupp.add_apply] at h
theorem m1sq_ne_m12 : m1sq ≠ m12 := fun h => m12_ne_m1sq h.symm
theorem m1sq_ne_m2sq : m1sq ≠ m2sq := by
  intro h; apply_fun (· 1) at h
  simp [m1sq, m2sq] at h
theorem m12_ne_m2sq : m12 ≠ m2sq := by
  intro h; apply_fun (· 1) at h
  simp [m12, m2sq, Finsupp.add_apply] at h
theorem m02_ne_m12 : m02 ≠ m12 := fun h => m12_ne_m02 h.symm
theorem m02_ne_m2sq : m02 ≠ m2sq := by
  intro h; apply_fun (· 0) at h
  simp [m02, m2sq, Finsupp.add_apply] at h

/-! ## The descended coordinate functionals on `mkA`-images -/

theorem χu2_mk (p : P3) : χu2 q (mkA q p) = χu2P p := rfl
theorem χu1_mk (p : P3) : χu1 q (mkA q p) = χu1P p := rfl

/-! ## Values of `χu1`, `χu2` on the three `J²`-generators `u₁, u₂, s` -/

theorem χu2_u2 : χu2 q (u₂ q) = 1 := by
  have h : u₂ q = mkA q (X 1 ^ 2) := by rw [← e2_sq, e2_eq, ← map_pow]
  rw [h, χu2_mk, χu2P_apply, X1sq_eq]
  simp [coeff_monomial, m1sq_ne_m02]

theorem χu2_u1 : χu2 q (u₁ q) = 0 := by
  have h : u₁ q = mkA q (X 1 * X 2) := by rw [← e2_mul_e3, e2_eq, e3_eq, ← map_mul]
  rw [h, χu2_mk, χu2P_apply, X1X2_eq]
  simp [coeff_monomial, m12_ne_m02, m12_ne_m1sq]

theorem χu2_s : χu2 q (s q) = 0 := by
  rw [s_eq, χu2_mk, χu2P_apply, coeff_sub, coeff_sub, X0X2_eq, X1sq_eq]
  simp [coeff_monomial, m1sq_ne_m02, m02_ne_m1sq]

theorem χu1_u2 : χu1 q (u₂ q) = 0 := by
  have h : u₂ q = mkA q (X 1 ^ 2) := by rw [← e2_sq, e2_eq, ← map_pow]
  rw [h, χu1_mk, χu1P_apply, X1sq_eq]
  simp [coeff_monomial, m1sq_ne_m12, m1sq_ne_m2sq]

theorem χu1_u1 : χu1 q (u₁ q) = 1 := by
  have h : u₁ q = mkA q (X 1 * X 2) := by rw [← e2_mul_e3, e2_eq, e3_eq, ← map_mul]
  rw [h, χu1_mk, χu1P_apply, X1X2_eq]
  simp [coeff_monomial, m12_ne_m2sq]

theorem χu1_s : χu1 q (s q) = 0 := by
  rw [s_eq, χu1_mk, χu1P_apply, coeff_sub, coeff_sub, X0X2_eq, X1sq_eq]
  simp [coeff_monomial, m02_ne_m12, m02_ne_m2sq, m1sq_ne_m12, m1sq_ne_m2sq]

/-! ## Nilpotence helper: `J · J² = 0` -/

/-- A product of an element of `J` and an element of `J²` vanishes (`J³ = 0`). -/
theorem mul_J_J2 {p w : A q} (hp : p ∈ J q) (hw : w ∈ J q ^ 2) : p * w = 0 := by
  have hmem : p * w ∈ J q ^ 3 := by
    have h := Ideal.mul_mem_mul hp hw
    rwa [← pow_succ'] at h
  rwa [J_pow_three, Ideal.mem_bot] at hmem

/-- `a • eᵢ ∈ J` for any `D`-scalar `a`. -/
theorem smul_e1_mem_J (a : D) : a • e₁ q ∈ J q := by
  rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ (e1_mem_J q)
theorem smul_e2_mem_J (a : D) : a • e₂ q ∈ J q := by
  rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ (e2_mem_J q)
theorem smul_e3_mem_J (a : D) : a • e₃ q ∈ J q := by
  rw [Algebra.smul_def]; exact Ideal.mul_mem_left _ _ (e3_mem_J q)

/-! ## Decomposition of an element of `J` into degree-1 part + `J²` -/

/-- Every `x ∈ J` is `a₁•e₁ + a₂•e₂ + a₃•e₃` (with `D`-scalars given by the
augmentation) plus a `J²` remainder. -/
theorem J_decomp {x : A q} (hx : x ∈ J q) :
    ∃ a₁ a₂ a₃ : D, ∃ w ∈ J q ^ 2,
      x = a₁ • e₁ q + a₂ • e₂ q + a₃ • e₃ q + w := by
  rw [show J q = Submodule.span (A q) {e₁ q, e₂ q, e₃ q} from rfl] at hx
  rw [Submodule.mem_span_insert] at hx
  obtain ⟨c₁, z₁, hz₁, rfl⟩ := hx
  rw [Submodule.mem_span_insert] at hz₁
  obtain ⟨c₂, z₂, hz₂, rfl⟩ := hz₁
  rw [Submodule.mem_span_singleton] at hz₂
  obtain ⟨c₃, rfl⟩ := hz₂
  refine ⟨aug q c₁, aug q c₂, aug q c₃,
    (c₁ - algebraMap D (A q) (aug q c₁)) * e₁ q
      + (c₂ - algebraMap D (A q) (aug q c₂)) * e₂ q
      + (c₃ - algebraMap D (A q) (aug q c₃)) * e₃ q, ?_, ?_⟩
  · have hr1 : c₁ - algebraMap D (A q) (aug q c₁) ∈ J q := by
      rw [J_eq_ker, RingHom.mem_ker, map_sub, aug_algebraMap, sub_self]
    have hr2 : c₂ - algebraMap D (A q) (aug q c₂) ∈ J q := by
      rw [J_eq_ker, RingHom.mem_ker, map_sub, aug_algebraMap, sub_self]
    have hr3 : c₃ - algebraMap D (A q) (aug q c₃) ∈ J q := by
      rw [J_eq_ker, RingHom.mem_ker, map_sub, aug_algebraMap, sub_self]
    have hp : ∀ {r : A q}, r ∈ J q → ∀ e ∈ J q, r * e ∈ J q ^ 2 := by
      intro r hr e he; rw [pow_two]; exact Ideal.mul_mem_mul hr he
    exact add_mem (add_mem (hp hr1 _ (e1_mem_J q)) (hp hr2 _ (e2_mem_J q)))
      (hp hr3 _ (e3_mem_J q))
  · simp only [smul_eq_mul, Algebra.smul_def]; ring

/-! ## The characteristic-2 finite check (over `ZMod 2`) -/

/-- The arithmetic heart, in the residue field `𝔽₂`: if the `u₂`- and
`u₁`-coordinates of `x*y` vanish, then so does the `t`-free part of its
`s`-coordinate.  A `64`-case check over `(ZMod 2)`. -/
theorem charTwo_cancel (A1 A2 A3 B1 B2 B3 : ZMod 2)
    (h1 : A1 * B3 + A3 * B1 + A2 * B2 = 0)
    (h2 : A2 * B3 + A3 * B2 + A3 * B3 = 0) : A1 * B3 + A3 * B1 = 0 := by
  revert A1 A2 A3 B1 B2 B3; decide

/-! ## The constant cancellation -/

/-- **`cancel_const` (Step 2).**  For `x, y ∈ J`, if `x*y` lands in the
`s`-component `(D/t^q)s`, then it lands one layer deeper, in `t·(D/t^q)s`. -/
theorem cancel_const_proof (q : ℕ) (x y : A q) (hx : x ∈ J q) (hy : y ∈ J q)
    (hxy : x * y ∈ sComponent q) : x * y ∈ tSComponent q := by
  -- Decompose x and y.
  obtain ⟨a₁, a₂, a₃, wx, hwx, hxeq⟩ := J_decomp q hx
  obtain ⟨b₁, b₂, b₃, wy, hwy, hyeq⟩ := J_decomp q hy
  -- The degree-1 parts.
  set dx := a₁ • e₁ q + a₂ • e₂ q + a₃ • e₃ q with hdx
  set dy := b₁ • e₁ q + b₂ • e₂ q + b₃ • e₃ q with hdy
  have hdxJ : dx ∈ J q :=
    add_mem (add_mem (smul_e1_mem_J q a₁) (smul_e2_mem_J q a₂)) (smul_e3_mem_J q a₃)
  have hdyJ : dy ∈ J q :=
    add_mem (add_mem (smul_e1_mem_J q b₁) (smul_e2_mem_J q b₂)) (smul_e3_mem_J q b₃)
  -- Kill the J³ cross terms: x*y = dx*dy.
  have hwxJ : wx ∈ J q := (Ideal.pow_le_self (by norm_num)) hwx
  have hxy_deg1 : x * y = dx * dy := by
    rw [hxeq, hyeq]
    have c1 : dx * wy = 0 := mul_J_J2 q hdxJ hwy
    have c2 : wx * dy = 0 := by rw [mul_comm]; exact mul_J_J2 q hdyJ hwx
    have c3 : wx * wy = 0 := mul_J_J2 q hwxJ hwy
    rw [show (dx + wx) * (dy + wy)
        = dx * dy + (dx * wy + (wx * dy + wx * wy)) from by ring, c1, c2, c3]
    ring
  -- Expand the degree-1 product through the mul table.
  have E : x * y = ((a₁ * b₃ + a₃ * b₁) + a₂ * b₂) • u₂ q
      + ((a₂ * b₃ + a₃ * b₂) + a₃ * b₃) • u₁ q
      + (a₁ * b₃ + a₃ * b₁) • s q := by
    rw [hxy_deg1, hdx, hdy]
    simp only [Algebra.smul_def, map_add, map_mul, u₂, u₁, s]
    linear_combination
      (algebraMap D (A q) a₁ * algebraMap D (A q) b₁) * e1_mul_e1 q
      + (algebraMap D (A q) a₁ * algebraMap D (A q) b₂
          + algebraMap D (A q) a₂ * algebraMap D (A q) b₁) * e1_mul_e2 q
      + (algebraMap D (A q) a₃ * algebraMap D (A q) b₃)
          * (by rw [e3_mul_e3, e2_mul_e3] : e₃ q * e₃ q = e₂ q * e₃ q)
  -- Read the s-component hypothesis.
  rw [sComponent, Submodule.mem_span_singleton] at hxy
  obtain ⟨γ, hγ⟩ := hxy
  -- The u₂-coordinate vanishes.
  have hcu2 : (a₁ * b₃ + a₃ * b₁) + a₂ * b₂ = 0 := by
    have h1 : χu2 q (x * y) = (a₁ * b₃ + a₃ * b₁) + a₂ * b₂ := by
      rw [E]; simp only [map_add, map_smul, χu2_u2, χu2_u1, χu2_s, smul_eq_mul,
        mul_one, mul_zero, add_zero]
    have h2 : χu2 q (x * y) = 0 := by
      rw [← hγ]; simp only [map_smul, χu2_s, smul_eq_mul, mul_zero]
    exact h1.symm.trans h2
  -- The u₁-coordinate vanishes.
  have hcu1 : (a₂ * b₃ + a₃ * b₂) + a₃ * b₃ = 0 := by
    have h1 : χu1 q (x * y) = (a₂ * b₃ + a₃ * b₂) + a₃ * b₃ := by
      rw [E]; simp only [map_add, map_smul, χu1_u2, χu1_u1, χu1_s, smul_eq_mul,
        mul_one, mul_zero, add_zero, zero_add]
    have h2 : χu1 q (x * y) = 0 := by
      rw [← hγ]; simp only [map_smul, χu1_s, smul_eq_mul, mul_zero]
    exact h1.symm.trans h2
  -- Char-2 finite check ⇒ the s-coordinate is divisible by t.
  set φ := (Polynomial.evalRingHom (0 : ZMod 2) : D →+* ZMod 2) with hφ
  have e1 : φ a₁ * φ b₃ + φ a₃ * φ b₁ + φ a₂ * φ b₂ = 0 := by
    have := congrArg φ hcu2; simpa [map_add, map_mul] using this
  have e2 : φ a₂ * φ b₃ + φ a₃ * φ b₂ + φ a₃ * φ b₃ = 0 := by
    have := congrArg φ hcu1; simpa [map_add, map_mul] using this
  have hcs0 : φ (a₁ * b₃ + a₃ * b₁) = 0 := by
    rw [map_add, map_mul, map_mul]
    exact charTwo_cancel _ _ _ _ _ _ e1 e2
  have hdvd : (Polynomial.X : D) ∣ (a₁ * b₃ + a₃ * b₁) := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_zero_eq_eval_zero]
    exact hcs0
  obtain ⟨δ, hδ⟩ := hdvd
  -- Conclude: x*y = cs • s = δ • (t·s) ∈ tSComponent.
  have hxy_cs : x * y = (a₁ * b₃ + a₃ * b₁) • s q := by
    rw [E, hcu2, hcu1, zero_smul, zero_smul, zero_add, zero_add]
  rw [hxy_cs, hδ, tSComponent]
  have hrw : (Polynomial.X * δ) • s q = δ • (tA q * s q) := by
    rw [tA, mul_comm Polynomial.X δ, mul_smul]
    congr 1
    rw [Algebra.smul_def]
  rw [hrw]
  exact Submodule.smul_mem _ δ (Submodule.mem_span_singleton_self _)

end Prob30c
