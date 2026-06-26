import Prob20.Proofs.Injective.Kernel

/-!
# Injective/Amplify.lean — Stage 3.2: `θₙ` is not injective for every `n ≥ 2`

The genuine `∀ n` lift of the Stage-3.1 kernel witness.  For `n ≥ 2` we place the
`tp, p` generators in slots `0, 1` and `p` in the remaining `n−2` slots:

  `τₙ = (tp ⊗ p ⊗ p ⊗ ⋯) − (p ⊗ tp ⊗ p ⊗ ⋯)  ∈  ⨂[Dom] (_ : Fin n), Int(D).`

* `θₙ τₙ = 0`: each pure tensor maps to `C t · ∏ᵢ p(Xᵢ)`, so they agree.
* `τₙ ≠ 0`: the multilinear functional with `Λ` in slot 0, `Μ` in slot 1, and `Λ`
  in the rest (recall `Λ(p)=1`) separates: `Φₙ τₙ = 0 − 1 = 1 ≠ 0`.

Hence `θₙ τₙ = 0 = θₙ 0` with `τₙ ≠ 0`, so `θₙ` is not injective. Tensor base is
`Dom` throughout.
-/

open scoped TensorProduct
open Prob20 Polynomial
open Prob20.Proofs.Domain
open Prob20.Proofs.KeyObs

namespace Prob20.Proofs.Injective

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

/-! ### The lifted kernel element `τₙ` -/

/-- `tp` in slot `0`, `p` elsewhere. -/
noncomputable def aFun (n : ℕ) : Fin n → ↥(IntPoly Dom Kt) :=
  fun i => if i.val = 0 then tpR else pR
/-- `tp` in slot `1`, `p` elsewhere. -/
noncomputable def bFun (n : ℕ) : Fin n → ↥(IntPoly Dom Kt) :=
  fun i => if i.val = 1 then tpR else pR

/-- `τₙ = tprod(aFun) − tprod(bFun)`. -/
noncomputable def tauN (n : ℕ) : ⨂[Dom] (_ : Fin n), ↥(IntPoly Dom Kt) :=
  PiTensorProduct.tprod Dom (aFun n) - PiTensorProduct.tprod Dom (bFun n)

/-! ### `θₙ τₙ = 0` -/

/-- The product `∏ᵢ (if i = k then tp else p)(Xᵢ)` equals `C t · ∏ᵢ p(Xᵢ)`, for any
distinguished slot `k`. -/
theorem prod_at (n k : ℕ) (hk : k < n) :
    (∏ i : Fin n, Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) Kt)
        ((if i.val = k then tpR else pR : ↥(IntPoly Dom Kt)) : Polynomial Kt))
      = algebraMap Kt (MvPolynomial (Fin n) Kt) tElt
        * ∏ i : Fin n,
            Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) Kt) (pPoly : Polynomial Kt) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨k, hk⟩ : Fin n)),
      ← Finset.mul_prod_erase Finset.univ
        (fun i => Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) Kt) (pPoly : Polynomial Kt))
        (Finset.mem_univ (⟨k, hk⟩ : Fin n))]
  have hj : Polynomial.aeval (MvPolynomial.X (⟨k, hk⟩ : Fin n) : MvPolynomial (Fin n) Kt)
        ((if (⟨k, hk⟩ : Fin n).val = k then tpR else pR : ↥(IntPoly Dom Kt)) : Polynomial Kt)
      = algebraMap Kt (MvPolynomial (Fin n) Kt) tElt
        * Polynomial.aeval (MvPolynomial.X (⟨k, hk⟩ : Fin n) : MvPolynomial (Fin n) Kt)
            (pPoly : Polynomial Kt) := by
    rw [if_pos rfl]
    show Polynomial.aeval (MvPolynomial.X (⟨k, hk⟩ : Fin n) : MvPolynomial (Fin n) Kt)
      (tpPoly : Polynomial Kt) = _
    rw [tpPoly, map_mul, Polynomial.aeval_C]
  have hrest : (∏ i ∈ Finset.univ.erase (⟨k, hk⟩ : Fin n),
        Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) Kt)
          ((if i.val = k then tpR else pR : ↥(IntPoly Dom Kt)) : Polynomial Kt))
      = ∏ i ∈ Finset.univ.erase (⟨k, hk⟩ : Fin n),
          Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) Kt) (pPoly : Polynomial Kt) := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    rw [Finset.mem_erase] at hi
    have hik : i.val ≠ k := fun h => hi.1 (Fin.ext h)
    rw [if_neg hik, pR_val]
  rw [hj, hrest, mul_assoc]

theorem thetaN_tauN (n : ℕ) (hn : 2 ≤ n) : thetaN Dom Kt n (tauN n) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have key : thetaN Dom Kt (m + 2) (PiTensorProduct.tprod Dom (aFun (m + 2)))
           - thetaN Dom Kt (m + 2) (PiTensorProduct.tprod Dom (bFun (m + 2))) = 0 := by
    rw [thetaN, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
    simp only [thetaMul, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
      AlgHom.toLinearMap_apply, incl_apply, aFun, bFun]
    rw [prod_at (m + 2) 0 (by omega), prod_at (m + 2) 1 (by omega), sub_self]
  calc thetaN Dom Kt (m + 2) (tauN (m + 2))
      = thetaN Dom Kt (m + 2) (PiTensorProduct.tprod Dom (aFun (m + 2)))
        - thetaN Dom Kt (m + 2) (PiTensorProduct.tprod Dom (bFun (m + 2))) := map_sub _ _ _
    _ = 0 := key

/-! ### The separating functional `Φₙ` and `τₙ ≠ 0` -/

/-- `Μ` in slot 1, `Λ` everywhere else (recall `Λ(p)=1`, so the extra slots keep
the product nonzero). -/
noncomputable def sepFun (n : ℕ) : Fin n → (↥(IntPoly Dom Kt) →ₗ[Dom] ZMod 2) :=
  fun i => if i.val = 1 then MuL else LamL

noncomputable def sepMulN (n : ℕ) :
    MultilinearMap Dom (fun _ : Fin n => ↥(IntPoly Dom Kt)) (ZMod 2) :=
  (MultilinearMap.mkPiAlgebra Dom (Fin n) (ZMod 2)).compLinearMap (sepFun n)

noncomputable def PhiN (n : ℕ) :
    (⨂[Dom] (_ : Fin n), ↥(IntPoly Dom Kt)) →ₗ[Dom] ZMod 2 :=
  PiTensorProduct.lift (sepMulN n)

theorem PhiN_tauN (n : ℕ) (hn : 2 ≤ n) : PhiN n (tauN n) = 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have ha : PhiN (m + 2) (PiTensorProduct.tprod Dom (aFun (m + 2))) = 0 := by
    rw [PhiN, PiTensorProduct.lift.tprod]
    simp only [sepMulN, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
    refine Finset.prod_eq_zero (Finset.mem_univ (0 : Fin (m + 2))) ?_
    simp only [sepFun, aFun, Fin.val_zero, if_true]
    exact LamL_tpR
  have hb : PhiN (m + 2) (PiTensorProduct.tprod Dom (bFun (m + 2))) = 1 := by
    rw [PhiN, PiTensorProduct.lift.tprod]
    simp only [sepMulN, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
    refine Finset.prod_eq_one ?_
    intro i _
    simp only [sepFun, bFun]
    by_cases hi : i.val = 1
    · rw [if_pos hi, if_pos hi]; exact MuL_tpR
    · rw [if_neg hi, if_neg hi]; exact LamL_pR
  have key : PhiN (m + 2) (PiTensorProduct.tprod Dom (aFun (m + 2)))
           - PhiN (m + 2) (PiTensorProduct.tprod Dom (bFun (m + 2))) = 1 := by
    rw [ha, hb]; decide
  calc PhiN (m + 2) (tauN (m + 2))
      = PhiN (m + 2) (PiTensorProduct.tprod Dom (aFun (m + 2)))
        - PhiN (m + 2) (PiTensorProduct.tprod Dom (bFun (m + 2))) := map_sub _ _ _
    _ = 1 := key

/-- **Stage 3.2 — `thetaN_not_injective`.**  `θₙ` is not injective for any `n ≥ 2`. -/
theorem thetaN_not_injective_proof :
    ∀ n : ℕ, 2 ≤ n → ¬ Function.Injective (thetaN Dom Kt n) := by
  intro n hn hinj
  have h0 : thetaN Dom Kt n (tauN n) = thetaN Dom Kt n 0 := by
    rw [thetaN_tauN n hn, map_zero]
  have htau0 : tauN n = 0 := hinj h0
  have hone : PhiN n (tauN n) = 1 := PhiN_tauN n hn
  rw [htau0, map_zero] at hone
  exact one_ne_zero hone.symm

end Prob20.Proofs.Injective
