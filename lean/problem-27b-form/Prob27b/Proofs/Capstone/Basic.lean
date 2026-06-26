/-
Copyright (c) 2026 Prob27b formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob27b formalization
-/
import Prob27b.Proofs.Algebra.Basic
import Prob27b.Proofs.Lift.Basic
import Prob27b.Proofs.NonIdeal.Basic

/-!
# Stage E — Capstone: `Int(A)` is not closed under multiplication

Over the literal Problem 27 coefficient ring `B = K ⊗_D A`, we prove `Pb = F̃/π`
and the constant `econstB = e` are integer-valued on `A`, but `Pb · econstB` is
not — refuting Problem 27(b). The bridge "value ∈ A ⇔ numerator divisible by π"
is formalized using the injectivity of `A ↪ B` (`incA_injective`) together with
`Stage D`'s `P_div` (`F̃(a) = X·b`) and `Stage C`'s `Fe_witness_proof`.
-/

namespace Prob27b

open Polynomial

/-- Naturality of evaluation under a coefficient ring hom (no commutativity). -/
theorem eval_map_hom {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂] (f : R₁ →+* R₂)
    (p : Polynomial R₁) (x : R₁) : (p.map f).eval (f x) = f (p.eval x) := by
  have h := Polynomial.hom_eval₂ p (RingHom.id R₁) f x
  rw [RingHom.comp_id] at h
  rw [Polynomial.eval_map, ← h]; rfl

/-! ### `π`'s image in `B` is invertible -/

theorem algDA_X : algDA (X : D) = (X : A) := by
  rw [algDA, Polynomial.coe_mapRingHom, Polynomial.map_X]

/-- `incA π = incK (algebraMap D K π)`: both are the image of the central `π ∈ D`. -/
theorem incA_X_eq : incA (X : A) = incK (algebraMap D K (X : D)) := by
  rw [← algDA_X, ← algebraMap_D_A_eq, AlgHom.commutes, incK,
    Algebra.TensorProduct.algebraMap_def]
  rfl

theorem algebraMap_D_K_X_ne_zero : algebraMap D K (X : D) ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective D K)).mpr Polynomial.X_ne_zero

theorem incAX_mul_πBinv : incA (X : A) * πBinv = 1 := by
  rw [incA_X_eq, πBinv, ← map_mul, mul_inv_cancel₀ algebraMap_D_K_X_ne_zero, map_one]

theorem πBinv_mul_incAX : πBinv * incA (X : A) = 1 := by
  rw [incA_X_eq, πBinv, ← map_mul, inv_mul_cancel₀ algebraMap_D_K_X_ne_zero, map_one]

/-- Coercion-matched naturality for `incA` (eval point is the `AlgHom` `incA a`,
the map uses the `RingHom` coercion `↑incA`). -/
theorem incA_eval_map (p : Polynomial A) (a : A) :
    (p.map (incA : A →+* B)).eval (incA a) = incA (p.eval a) :=
  eval_map_hom (incA : A →+* B) p a

/-! ### The two factors are integer-valued -/

theorem Pb_eval (a : A) : Pb.eval (incA a) = πBinv * incA (Ftilde.eval a) := by
  rw [Pb, Polynomial.eval_C_mul]; congr 1; exact incA_eval_map Ftilde a

/-- **`Pb = F̃/π` is integer-valued.** For each `a`, `F̃(a) = π·b` (`P_div`), so
`Pb(incA a) = πBinv · incA(π·b) = incA b ∈ range incA`. -/
theorem IntegerValued_Pb : IntegerValued Pb := by
  intro a
  obtain ⟨b, hb⟩ := P_div a
  refine ⟨b, ?_⟩
  rw [Pb_eval, hb, map_mul, ← mul_assoc, πBinv_mul_incAX, one_mul]

/-- **The constant `e` is integer-valued** (trivially: it evaluates to `incA (C e)`). -/
theorem IntegerValued_econstB : IntegerValued econstB := by
  intro a
  exact ⟨C e, by rw [econstB, Polynomial.eval_C]⟩

/-! ### The product escapes `Int(A)` -/

/-- Lift of `Fe_witness`: `(F̃ · e)(C a₀) = C s` in `A`. -/
theorem Fe_eval_lift : (Ftilde * C (C e)).eval (C a₀) = C s := by
  have hmap : Ftilde * C (C e) = (F * C e).map (C : R →+* A) := by
    rw [Ftilde, Polynomial.map_mul, Polynomial.map_C]
  rw [hmap, eval_map_hom]
  exact congrArg _ Fe_witness_proof.1

theorem PeconstB_eq : Pb * econstB = C πBinv * (Ftilde * C (C e)).map (incA : A →+* B) := by
  rw [Pb, econstB, mul_assoc]; congr 1
  rw [Polynomial.map_mul, Polynomial.map_C]; rfl

theorem PeconstB_eval (a : A) :
    (Pb * econstB).eval (incA a) = πBinv * incA ((Ftilde * C (C e)).eval a) := by
  rw [PeconstB_eq, Polynomial.eval_C_mul]; congr 1; exact incA_eval_map _ a

/-- **`Pb · econstB` is NOT integer-valued.** At `a₀ = u+v`, its value is
`πBinv · incA (C s)`; were it `incA y`, then (multiplying by `incA π` and using
injectivity of `incA`) `C s = X·y` in `A`, i.e. `s` is divisible by `π` — false,
since `s ≠ 0` is the constant coefficient. -/
theorem not_IntegerValued_PeconstB : ¬ IntegerValued (Pb * econstB) := by
  intro h
  obtain ⟨y, hy⟩ := h (C a₀)
  rw [PeconstB_eval, Fe_eval_lift] at hy
  have key : incA ((X : A) * y) = incA (C s) := by
    have e1 : incA (X : A) * incA y = incA (X : A) * (πBinv * incA (C s)) := by rw [hy]
    rw [← map_mul] at e1
    rwa [← mul_assoc, incAX_mul_πBinv, one_mul] at e1
  have hxy : (X : A) * y = C s := incA_injective key
  have hco : ((X : A) * y).coeff 0 = (C s).coeff 0 := by rw [hxy]
  rw [coeff_C_zero, mul_coeff_zero, coeff_X_zero, zero_mul] at hco
  exact Fe_witness_proof.2 hco.symm

/-! ### The frozen targets -/

/-- **SKETCH Steps 4–5 (witnesses).** -/
theorem prob27b_counterexample_proof :
    IntegerValued Pb ∧ IntegerValued econstB ∧ ¬ IntegerValued (Pb * econstB) :=
  ⟨IntegerValued_Pb, IntegerValued_econstB, not_IntegerValued_PeconstB⟩

/-- **Headline — refutation of Problem 27(b).** `Int(A)` is not closed under
multiplication. -/
theorem problem27b_false_proof : ∃ g₁ ∈ IntA, ∃ g₂ ∈ IntA, g₁ * g₂ ∉ IntA :=
  ⟨Pb, IntegerValued_Pb, econstB, IntegerValued_econstB, not_IntegerValued_PeconstB⟩

end Prob27b
