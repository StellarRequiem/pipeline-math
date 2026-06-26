import Prob20.Defs
import Prob20.Theorems
import Prob20.Proofs.KeyObs.KeyMembership
import Prob20.Proofs.KeyObs.LinIndep

/-!
# Injective/Kernel.lean — Stage 3.1: the explicit nonzero kernel element of `θ₂`

We produce `theta2_kernel_proof`, the frozen Stage-3.1 statement
`∃ τ, τ ≠ 0 ∧ thetaN Dom Kt 2 τ = 0`, with the explicit witness

  `τ = (tp) ⊗ p − p ⊗ (tp)  ∈  ⨂[Dom] (_ : Fin 2), Int(D).`

* `θ₂ τ = 0`: a direct `MvPolynomial` computation (`tp(X₀)p(X₁) = p(X₀)tp(X₁) =
  t·p(X₀)p(X₁)`).
* `τ ≠ 0`: we build two `Dom`-linear functionals `Λ, Μ : Int(D) →ₗ[Dom] 𝔽₂` from
  the divided difference `δ(g) = (g(π) − g(0))/π ∈ T` (well-defined by the crux
  lemma `L` plus `𝔪 ⊆ πT`), with `Λ = res0 ∘ δ`, `Μ = res1 ∘ δ`.  On the bundled
  generators: `Λ(p)=1, Μ(p)=1, Λ(tp)=0, Μ(tp)=1`.  Lifting the multilinear map
  `(f,g) ↦ Λ(f)·Μ(g)` to `Φ : ⨂ →ₗ[Dom] 𝔽₂` gives
  `Φ τ = Λ(tp)Μ(p) − Λ(p)Μ(tp) = 0·1 − 1·1 = 1 ≠ 0`, hence `τ ≠ 0`.

The tensor base is **`Dom`** throughout (`⨂[Dom]`), as required: over `K` the
classes `p̄, t̄p̄` are dependent and `τ` would vanish.
-/

open scoped TensorProduct
open Prob20 Polynomial
open Prob20.Proofs.Domain
open Prob20.Proofs.KeyObs

namespace Prob20.Proofs.Injective

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

/-- `ZMod 2` as a `Dom`-algebra via the residue map `resD`; the only `Dom`-module
structure on `ZMod 2` we use (for the separating functionals and their lift). -/
noncomputable instance instAlgDomZMod2 : Algebra Dom (ZMod 2) := resD.toAlgebra

theorem algebraMap_dom_zmod2 : algebraMap Dom (ZMod 2) = resD := rfl

/-! ### The bundled generators `p, tp ∈ Int(D)` -/

/-- `p` bundled as an element of `Int(D)` (via `key_membership`). -/
noncomputable def pR : ↥(IntPoly Dom Kt) := ⟨pPoly, key_membership_proof.1⟩
/-- `tp` bundled as an element of `Int(D)`. -/
noncomputable def tpR : ↥(IntPoly Dom Kt) := ⟨tpPoly, key_membership_proof.2.1⟩

@[simp] theorem pR_val : (pR : Polynomial Kt) = pPoly := rfl
@[simp] theorem tpR_val : (tpR : Polynomial Kt) = tpPoly := rfl

/-! ### The divided difference `δ(g) = (g(π) − g(0))/π ∈ T` -/

theorem ddiff_exists (g : ↥(IntPoly Dom Kt)) :
    ∃ s : Tsub, (piTsub : Kt) * (s : Kt)
      = aeval piK (g : Polynomial Kt) - aeval (0 : Kt) (g : Polynomial Kt) := by
  obtain ⟨w, hw, hweq⟩ := L_proof g
  obtain ⟨s, hs⟩ := m_sub w hw
  refine ⟨s, ?_⟩
  rw [← hweq, domToKt_eq, hs, Subalgebra.coe_mul]

/-- The divided difference `δ(g) = (g(π) − g(0))/π`, as an element of `T`. -/
noncomputable def ddiff (g : ↥(IntPoly Dom Kt)) : Tsub := Classical.choose (ddiff_exists g)

theorem ddiff_spec (g : ↥(IntPoly Dom Kt)) :
    (piTsub : Kt) * ((ddiff g : Tsub) : Kt)
      = aeval piK (g : Polynomial Kt) - aeval (0 : Kt) (g : Polynomial Kt) :=
  Classical.choose_spec (ddiff_exists g)

theorem ddiff_unique (g : ↥(IntPoly Dom Kt)) (s : Tsub)
    (h : (piTsub : Kt) * (s : Kt)
      = aeval piK (g : Polynomial Kt) - aeval (0 : Kt) (g : Polynomial Kt)) :
    ddiff g = s := by
  have hpi : (piTsub : Kt) ≠ 0 := by rw [← piK_eq]; exact piK_ne_zero
  have hk : ((ddiff g : Tsub) : Kt) = (s : Kt) :=
    mul_left_cancel₀ hpi (by rw [ddiff_spec, h])
  exact Subtype.coe_injective hk

theorem ddiff_add (g h : ↥(IntPoly Dom Kt)) : ddiff (g + h) = ddiff g + ddiff h := by
  apply ddiff_unique
  rw [Subalgebra.coe_add, mul_add, ddiff_spec g, ddiff_spec h, AddMemClass.coe_add,
    map_add, map_add]
  ring

theorem ddiff_smul (c : Dom) (g : ↥(IntPoly Dom Kt)) :
    ddiff (c • g) = (c : Tsub) * ddiff g := by
  apply ddiff_unique
  have hscal : ((c • g : ↥(IntPoly Dom Kt)) : Polynomial Kt)
      = C (algebraMap Dom Kt c) * (g : Polynomial Kt) := by rw [Algebra.smul_def]; rfl
  rw [Subalgebra.coe_mul, hscal, map_mul, map_mul]
  simp only [Polynomial.aeval_C, Algebra.algebraMap_self_apply]
  rw [← domToKt_eq c]
  linear_combination (algebraMap Dom Kt c) * ddiff_spec g

/-! ### The two `Dom`-linear place functionals `Λ = res0 ∘ δ`, `Μ = res1 ∘ δ` -/

/-- A place functional `g ↦ res (δ g) : Int(D) →ₗ[Dom] 𝔽₂`, for any residue `res`
on `T` that restricts on `D` to `resD`. -/
noncomputable def funcL (res : Tsub →+* ZMod 2) (hres : ∀ c : Dom, res (c : Tsub) = resD c) :
    ↥(IntPoly Dom Kt) →ₗ[Dom] ZMod 2 where
  toFun g := res (ddiff g)
  map_add' g h := by simp only [ddiff_add, map_add]
  map_smul' c g := by
    show res (ddiff (c • g)) = c • res (ddiff g)
    rw [ddiff_smul, map_mul, hres, Algebra.smul_def, algebraMap_dom_zmod2]

/-- `Λ(g) = res0(δ g)`. -/
noncomputable def LamL : ↥(IntPoly Dom Kt) →ₗ[Dom] ZMod 2 := funcL res0 (fun _ => rfl)
/-- `Μ(g) = res1(δ g)`. -/
noncomputable def MuL : ↥(IntPoly Dom Kt) →ₗ[Dom] ZMod 2 :=
  funcL res1 (fun c => (RingHom.mem_eqLocus.mp c.2).symm)

@[simp] theorem LamL_apply (g : ↥(IntPoly Dom Kt)) : LamL g = res0 (ddiff g) := rfl
@[simp] theorem MuL_apply (g : ↥(IntPoly Dom Kt)) : MuL g = res1 (ddiff g) := rfl

/-! ### The divided differences of the generators -/

theorem ddiff_pR : ddiff pR = piTsub + 1 := by
  apply ddiff_unique
  have hval : ((pR : ↥(IntPoly Dom Kt)) : Polynomial Kt) = pPoly := rfl
  rw [hval, pPoly, Subalgebra.coe_add, Subalgebra.coe_one, ← piK_eq]
  simp only [map_add, map_pow, Polynomial.aeval_X]
  ring

theorem ddiff_tpR : ddiff tpR = tT * (piTsub + 1) := by
  apply ddiff_unique
  have hval : ((tpR : ↥(IntPoly Dom Kt)) : Polynomial Kt) = tpPoly := rfl
  rw [hval, tpPoly, pPoly, Subalgebra.coe_mul, Subalgebra.coe_add, Subalgebra.coe_one,
    coe_tT, ← piK_eq]
  simp only [map_mul, map_add, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
    Algebra.algebraMap_self_apply]
  ring

theorem LamL_pR : LamL pR = 1 := by
  rw [LamL_apply, ddiff_pR, map_add, res0_piTsub, map_one, zero_add]
theorem MuL_pR : MuL pR = 1 := by
  rw [MuL_apply, ddiff_pR, map_add, res1_piTsub, map_one, zero_add]
theorem LamL_tpR : LamL tpR = 0 := by
  rw [LamL_apply, ddiff_tpR, map_mul, res0_tT, zero_mul]
theorem MuL_tpR : MuL tpR = 1 := by
  rw [MuL_apply, ddiff_tpR, map_mul, res1_tT, map_add, res1_piTsub, map_one, zero_add, one_mul]

/-! ### The coordinate inclusion, unfolded -/

theorem incl_apply (n : ℕ) (i : Fin n) (f : ↥(IntPoly Dom Kt)) :
    incl Dom Kt n i f = Polynomial.aeval (MvPolynomial.X i) (f : Polynomial Kt) := rfl

/-! ### The kernel element `τ` -/

/-- `τ = (tp) ⊗ p − p ⊗ (tp)`. -/
noncomputable def tau : ⨂[Dom] (_ : Fin 2), ↥(IntPoly Dom Kt) :=
  PiTensorProduct.tprod Dom ![tpR, pR] - PiTensorProduct.tprod Dom ![pR, tpR]

theorem thetaN_tau : thetaN Dom Kt 2 tau = 0 := by
  have key : thetaN Dom Kt 2 (PiTensorProduct.tprod Dom ![tpR, pR])
           - thetaN Dom Kt 2 (PiTensorProduct.tprod Dom ![pR, tpR]) = 0 := by
    rw [thetaN, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
    simp only [thetaMul,
      MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, Fin.prod_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, AlgHom.toLinearMap_apply,
      incl_apply, tpR_val, pR_val, tpPoly, map_mul, Polynomial.aeval_C]
    ring
  calc thetaN Dom Kt 2 tau
      = thetaN Dom Kt 2 (PiTensorProduct.tprod Dom ![tpR, pR])
        - thetaN Dom Kt 2 (PiTensorProduct.tprod Dom ![pR, tpR]) := map_sub _ _ _
    _ = 0 := key

/-! ### The separating functional `Φ` and `τ ≠ 0` -/

/-- The multilinear map `(f,g) ↦ Λ(f)·Μ(g)`. -/
noncomputable def sepMul : MultilinearMap Dom (fun _ : Fin 2 => ↥(IntPoly Dom Kt)) (ZMod 2) :=
  (MultilinearMap.mkPiAlgebra Dom (Fin 2) (ZMod 2)).compLinearMap ![LamL, MuL]

/-- `Φ : ⨂ →ₗ[Dom] 𝔽₂`, the lift of `sepMul`. -/
noncomputable def Phi : (⨂[Dom] (_ : Fin 2), ↥(IntPoly Dom Kt)) →ₗ[Dom] ZMod 2 :=
  PiTensorProduct.lift sepMul

theorem Phi_tau : Phi tau = 1 := by
  have ha : Phi (PiTensorProduct.tprod Dom ![tpR, pR]) = 0 := by
    rw [Phi, PiTensorProduct.lift.tprod]
    simp only [sepMul, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
    exact Finset.prod_eq_zero (Finset.mem_univ (0 : Fin 2)) LamL_tpR
  have hb : Phi (PiTensorProduct.tprod Dom ![pR, tpR]) = 1 := by
    rw [Phi, PiTensorProduct.lift.tprod]
    simp only [sepMul, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
    refine Finset.prod_eq_one ?_
    intro i _
    fin_cases i
    · exact LamL_pR
    · exact MuL_tpR
  have key : Phi (PiTensorProduct.tprod Dom ![tpR, pR])
           - Phi (PiTensorProduct.tprod Dom ![pR, tpR]) = 1 := by rw [ha, hb]; decide
  calc Phi tau
      = Phi (PiTensorProduct.tprod Dom ![tpR, pR])
        - Phi (PiTensorProduct.tprod Dom ![pR, tpR]) := map_sub _ _ _
    _ = 1 := key

/-- **Stage 3.1 — `theta2_kernel`.**  The explicit nonzero kernel element of `θ₂`. -/
theorem theta2_kernel_proof :
    ∃ τ : ⨂[Dom] (_ : Fin 2), ↥(IntPoly Dom Kt),
      τ ≠ 0 ∧ thetaN Dom Kt 2 τ = 0 := by
  refine ⟨tau, ?_, thetaN_tau⟩
  intro h
  have hz : Phi tau = 0 := by rw [h, map_zero]
  rw [Phi_tau] at hz
  exact one_ne_zero hz

end Prob20.Proofs.Injective
