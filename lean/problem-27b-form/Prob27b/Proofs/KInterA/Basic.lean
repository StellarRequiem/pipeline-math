/-
Copyright (c) 2026 Prob27b formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob27b formalization
-/
import Prob27b.Proofs.Algebra.Basic

/-!
# The augmentation `R → 𝔽₂` (toward `K ∩ A = D`)

Every matrix in `R` has its top row supported only at column `0` (only `mE` has a
nonzero `(0,·)` entry, at `(0,0)`). Hence the `(0,0)`-entry map is multiplicative
on `R`, giving an `𝔽₂`-algebra hom `Raug : R →ₐ[𝔽₂] 𝔽₂` (the augmentation to the
`e`-vertex). It is the key to `K ∩ A = D`.
-/

namespace Prob27b

open Polynomial Matrix

/-! ### Top row of each basis matrix -/

theorem mE_row0 (k : Fin 8) : mE 0 k = if k = 0 then 1 else 0 := by fin_cases k <;> decide
theorem mF_row0 (k : Fin 8) : mF 0 k = 0 := by fin_cases k <;> decide
theorem mU_row0 (k : Fin 8) : mU 0 k = 0 := by fin_cases k <;> decide
theorem mV_row0 (k : Fin 8) : mV 0 k = 0 := by fin_cases k <;> decide
theorem mP_row0 (k : Fin 8) : (mU * mV) 0 k = 0 := by fin_cases k <;> decide
theorem mQ_row0 (k : Fin 8) : (mV * mU) 0 k = 0 := by fin_cases k <;> decide
theorem mS_row0 (k : Fin 8) : (mU * mV * mU) 0 k = 0 := by fin_cases k <;> decide
theorem mW_row0 (k : Fin 8) : (mV * mU * mV) 0 k = 0 := by fin_cases k <;> decide

/-- The coercion `R ↪ Mat` of the eight basis elements. -/
theorem coe_e : ((e : R) : Mat) = mE := rfl
theorem coe_f : ((f : R) : Mat) = mF := rfl
theorem coe_u : ((u : R) : Mat) = mU := rfl
theorem coe_v : ((v : R) : Mat) = mV := rfl
theorem coe_p : ((p : R) : Mat) = mU * mV := rfl
theorem coe_q : ((q : R) : Mat) = mV * mU := rfl
theorem coe_s : ((s : R) : Mat) = mU * mV * mU := rfl
theorem coe_w : ((w : R) : Mat) = mV * mU * mV := rfl

/-- **Top-row support.** For every `x : R` and `k ≠ 0`, the `(0,k)` matrix entry
of `x` vanishes. -/
theorem R_row0 (x : R) {k : Fin 8} (hk : k ≠ 0) : (x : Mat) 0 k = 0 := by
  obtain ⟨α, β, γ, δ, η, θ, ι, κ, rfl⟩ := R_generic x
  simp only [Subalgebra.coe_add, Subalgebra.coe_smul, Matrix.add_apply, Matrix.smul_apply,
    coe_e, coe_f, coe_u, coe_v, coe_p, coe_q, coe_s, coe_w, mE_row0, mF_row0, mU_row0, mV_row0,
    mP_row0, mQ_row0, mS_row0, mW_row0, if_neg hk, smul_zero, add_zero, smul_eq_mul, mul_zero]

/-- The `(0,0)`-entry is multiplicative on `R` (top-row support kills the cross
terms). -/
theorem R_mul_entry00 (x y : R) : ((x * y : R) : Mat) 0 0 = ((x : Mat) 0 0) * ((y : Mat) 0 0) := by
  rw [Subalgebra.coe_mul, Matrix.mul_apply, Finset.sum_eq_single (0 : Fin 8)]
  · intro j _ hj; rw [R_row0 x hj, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The augmentation `Raug : R →ₐ[𝔽₂] 𝔽₂`, `x ↦ x₀₀` (the `e`-vertex component). -/
def Raug : R →ₐ[ZMod 2] ZMod 2 where
  toFun x := (x : Mat) 0 0
  map_one' := by decide
  map_mul' := R_mul_entry00
  map_zero' := rfl
  map_add' x y := by rw [Subalgebra.coe_add, Matrix.add_apply]
  commutes' c := by
    show ((algebraMap (ZMod 2) R c : R) : Mat) 0 0 = c
    rw [Algebra.algebraMap_eq_smul_one]
    simp [Subalgebra.coe_smul]

theorem Raug_comp_algebraMap : (Raug : R →+* ZMod 2).comp (algebraMap (ZMod 2) R) = RingHom.id _ :=
  RingHom.ext fun c => Raug.commutes c

/-- The augmentation lifted to a `D`-algebra hom `ε : A = R[π] →ₐ[D] D = 𝔽₂[π]`
(apply `Raug` to coefficients; `π ↦ π`). -/
noncomputable def εA : A →ₐ[D] D where
  toRingHom := Polynomial.mapRingHom (Raug : R →+* ZMod 2)
  commutes' d := by
    show Polynomial.map (Raug : R →+* ZMod 2) (algebraMap D A d) = algebraMap D D d
    rw [algebraMap_D_A_eq, algDA, Polynomial.coe_mapRingHom, Polynomial.map_map,
      Raug_comp_algebraMap, Polynomial.map_id]
    simp

/-- `A →ₐ[D] K`: the augmentation followed by `D ↪ K`. -/
noncomputable def gAK : A →ₐ[D] K := (Algebra.ofId D K).comp εA

/-- The augmentation extended to `B = K ⊗_D A → K` (`incK k ↦ k`,
`incA a ↦ algebraMap D K (ε a)`). -/
noncomputable def εK : B →ₐ[D] K :=
  Algebra.TensorProduct.lift (AlgHom.id D K) gAK (fun _ _ => Commute.all _ _)

theorem εK_incK (k : K) : εK (incK k) = k := by
  show εK (Algebra.TensorProduct.includeLeftRingHom k) = k
  rw [Algebra.TensorProduct.includeLeftRingHom_apply, εK, Algebra.TensorProduct.lift_tmul]
  simp [gAK]

theorem εK_incA (a : A) : εK (incA a) = algebraMap D K (εA a) := by
  show εK (Algebra.TensorProduct.includeRight a) = _
  rw [Algebra.TensorProduct.includeRight_apply, εK, Algebra.TensorProduct.lift_tmul]
  simp [gAK, Algebra.ofId_apply]

theorem algebraMap_D_B_eq (d : D) : algebraMap D B d = incK (algebraMap D K d) := by
  rw [incK, Algebra.TensorProduct.algebraMap_def]; rfl

/-- **`K ∩ A = D`** inside `B`: the only elements of `B` lying in both the image
of `K` and the image of `A` are the images of `D`. (Problem 27 hypothesis.) -/
theorem K_inter_A_eq_D_proof :
    Set.range (incK : K → B) ∩ Set.range (incA : A → B) = Set.range (algebraMap D B) := by
  apply Set.eq_of_subset_of_subset
  · rintro x ⟨⟨k, hk⟩, ⟨a, ha⟩⟩
    refine ⟨εA a, ?_⟩
    have hkx : εK x = k := by rw [← hk]; exact εK_incK k
    have hax : εK x = algebraMap D K (εA a) := by rw [← ha]; exact εK_incA a
    rw [algebraMap_D_B_eq, ← hkx.symm.trans hax]; exact hk
  · rintro x ⟨d, rfl⟩
    exact ⟨⟨algebraMap D K d, (algebraMap_D_B_eq d).symm⟩,
      ⟨algebraMap D A d, AlgHom.commutes incA d⟩⟩

end Prob27b
