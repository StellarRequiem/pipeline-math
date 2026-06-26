import Prob20.Defs
import Prob20.Theorems

/-!
# Stage 4.3 — `thetaN_not_surjective` : the `∀ n ≥ 2` lift (conditional reduction)

We build the genuine `∀ n` non-surjectivity lift as a CONDITIONAL reduction to the
`n = 2` milestone `theta2_missing` (whose statement type is frozen in
`Prob20/Theorems.lean`).  The `n = 2` fact is kept as a HYPOTHESIS `h2` — we do NOT
import or consume the not-yet-✅ `theta2_missing_proof`.

The argument (SKETCH *Failure of Surjectivity*, last ¶; BLUEPRINT Stage 4.3):

* View `PMv = P(X₀,X₁)` as a polynomial on `Fin n` variables, independent of
  `X₂,…,X_{n−1}`: `Pₙ := rename (Fin.castLE) PMv ∈ Int(Dⁿ)` (from `h2.1`).
* If `Pₙ ∈ im θₙ`, write `Pₙ = θₙ τ`.  Apply the `Kt`-algebra contraction
  `φ : K[X₀,…,X_{n−1}] → K[X₀,X₁]` sending `Xᵢ ↦ Xᵢ` (`i < 2`) and `Xᵢ ↦ 1`
  (`i ≥ 2`).  Then `φ Pₙ = PMv`, while `φ(θₙ τ) ∈ im θ₂` (a tensor induction: on a
  pure tensor the extra slots evaluate to constants `(m i)(1) ∈ ι(D)`, which fold
  back into a slot-0 factor, exhibiting the contraction as `θ₂` of an explicit
  tensor).
* Hence `PMv ∈ im θ₂`, contradicting `h2.2`.  So `Int(Dⁿ) ⊄ im θₙ`.

The lift is genuine (a reduction to `n = 2`, not a re-specialization): tensor base
is `D` (`⨂[Dom]`), `Int(Dⁿ)` is the genuine `∀ d : Fin n → D` algebra, and the
non-inclusion `¬ (Int(Dⁿ) ⊆ Set.range θₙ)` is the genuine frozen conclusion.
-/

open scoped TensorProduct

open Prob20

namespace Prob20.Proofs.Surjective

open Polynomial MvPolynomial

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

/-- The scalar tower `Dom → Kt → Kt[X₀,…,X_{n−1}]`. -/
instance instTower (n : ℕ) : IsScalarTower Dom Kt (MvPolynomial (Fin n) Kt) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-! ## The contraction `φ : K[X₀,…,X_{n−1}] →ₐ[K] K[X₀,X₁]` -/

/-- The substitution underlying the contraction: `Xᵢ ↦ Xᵢ` for `i < 2`, else `↦ 1`. -/
noncomputable def contractSub (n : ℕ) : Fin n → MvPolynomial (Fin 2) Kt :=
  fun i => if h : (i : ℕ) < 2 then MvPolynomial.X (⟨(i : ℕ), h⟩ : Fin 2) else 1

/-- The contraction `K[X₀,…,X_{n−1}] →ₐ[K] K[X₀,X₁]`. -/
noncomputable def contract (n : ℕ) :
    MvPolynomial (Fin n) Kt →ₐ[Kt] MvPolynomial (Fin 2) Kt :=
  MvPolynomial.aeval (contractSub n)

theorem contract_X (n : ℕ) (i : Fin n) :
    contract n (MvPolynomial.X i) = contractSub n i := by
  rw [contract, MvPolynomial.aeval_X]

/-! ## The lifted polynomial `Pₙ = rename (castLE) PMv` -/

/-- `Pₙ ∈ Int(Dⁿ)` : evaluating the renamed `PMv` at `d : Fin n → Dom` only uses
`d 0, d 1` and equals `PMv` evaluated at `d ∘ castLE`, which lies in `ι(D)` by
`h2.1`. -/
theorem Pn_mem (n : ℕ) (hn : 2 ≤ n) (h1 : PMv ∈ IntPolyN Dom Kt 2) :
    (MvPolynomial.rename (Fin.castLE hn) PMv) ∈ IntPolyN Dom Kt n := by
  intro d
  rw [MvPolynomial.eval_rename]
  exact h1 (fun j => d (Fin.castLE hn j))

/-- `φ Pₙ = PMv` : the contraction inverts the renaming on the first two variables. -/
theorem contract_Pn (n : ℕ) (hn : 2 ≤ n) :
    contract n (MvPolynomial.rename (Fin.castLE hn) PMv) = PMv := by
  rw [contract, MvPolynomial.aeval_rename]
  have : (contractSub n ∘ Fin.castLE hn)
      = (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) Kt) := by
    funext j
    show contractSub n (Fin.castLE hn j) = MvPolynomial.X j
    have hj : ((Fin.castLE hn j : Fin n) : ℕ) < 2 := by
      rw [Fin.val_castLE]; exact j.isLt
    rw [contractSub, dif_pos hj]
    have hfix : (⟨((Fin.castLE hn j : Fin n) : ℕ), hj⟩ : Fin 2) = j :=
      Fin.ext (by rw [Fin.val_castLE])
    rw [hfix]
  rw [this, MvPolynomial.aeval_X_left_apply]

/-! ## `θₙ` on pure tensors, and the contraction of the separated product -/

/-- `θₙ` of the multilinear product is the product of the coordinate inclusions. -/
theorem thetaMul_eq_prod (n : ℕ) (m : Fin n → ↥(IntPoly Dom Kt)) :
    thetaMul Dom Kt n m = ∏ i, incl Dom Kt n i (m i) := by
  simp only [thetaMul, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply,
    AlgHom.toLinearMap_apply]

/-- `incl n i f = f(Xᵢ)`. -/
theorem incl_apply_n (n : ℕ) (i : Fin n) (f : ↥(IntPoly Dom Kt)) :
    incl Dom Kt n i f = Polynomial.aeval (MvPolynomial.X i) (f : Polynomial Kt) := rfl

/-- `θₙ` on a pure tensor equals the multilinear product. -/
theorem thetaN_tprod_n (n : ℕ) (m : Fin n → ↥(IntPoly Dom Kt)) :
    thetaN Dom Kt n (PiTensorProduct.tprod Dom m) = thetaMul Dom Kt n m := by
  rw [thetaN, PiTensorProduct.lift.tprod]

/-- `θ₂` on a pure tensor equals the separated product `(m 0)(X₀)·(m 1)(X₁)`. -/
theorem thetaN_tprod2 (m : Fin 2 → ↥(IntPoly Dom Kt)) :
    thetaN Dom Kt 2 (PiTensorProduct.tprod Dom m) = thetaMul Dom Kt 2 m :=
  thetaN_tprod_n 2 m

/-- `θₙ` is additive. -/
theorem thetaN_add_n (n : ℕ) (x y : ⨂[Dom] (_ : Fin n), IntPoly Dom Kt) :
    thetaN Dom Kt n (x + y) = thetaN Dom Kt n x + thetaN Dom Kt n y :=
  map_add _ _ _

/-- Evaluating the univariate `aeval` at the point `1 : K[X₀,X₁]` gives the constant
polynomial `C (p(1))`. -/
theorem aeval_one_eq_C (p : Polynomial Kt) :
    Polynomial.aeval (1 : MvPolynomial (Fin 2) Kt) p
      = MvPolynomial.C (Polynomial.aeval (1 : Kt) p) := by
  have hcomm :
      (Polynomial.aeval (1 : MvPolynomial (Fin 2) Kt) : Polynomial Kt →ₐ[Kt] _)
        = (Algebra.ofId Kt (MvPolynomial (Fin 2) Kt)).comp (Polynomial.aeval (1 : Kt)) := by
    apply Polynomial.algHom_ext
    simp [Algebra.ofId_apply]
  rw [hcomm]
  simp [Algebra.ofId_apply, MvPolynomial.algebraMap_eq]

/-! ## The key membership : the contraction of `θₙ` lands in `im θ₂` -/

/-- The contraction of `θₙ` on a separated product lies in `range θ₂`.  The extra
slots (`i ≥ 2`) evaluate to constants `(m i)(1) ∈ ι(D)`; their product folds into a
slot-`0` factor, exhibiting the contraction as `θ₂` of an explicit pure tensor. -/
theorem contract_thetaMul_mem (n : ℕ) (hn : 2 ≤ n) (m : Fin n → ↥(IntPoly Dom Kt)) :
    contract n (thetaMul Dom Kt n m) ∈ LinearMap.range (thetaN Dom Kt 2) := by
  classical
  set j0 : Fin n := ⟨0, by omega⟩ with hj0
  set j1 : Fin n := ⟨1, by omega⟩ with hj1
  have j0val : ((j0 : Fin n) : ℕ) = 0 := by rw [hj0]
  have j1val : ((j1 : Fin n) : ℕ) = 1 := by rw [hj1]
  -- contraction of each `incl` slot is `aeval (contractSub n i)`
  have hFi : ∀ i : Fin n, contract n (incl Dom Kt n i (m i))
      = Polynomial.aeval (contractSub n i) ((m i : Polynomial Kt)) := by
    intro i
    rw [incl_apply_n, ← Polynomial.aeval_algHom_apply, contract_X]
  -- contraction of the product is the product of contractions
  have hprod : contract n (thetaMul Dom Kt n m)
      = ∏ i, Polynomial.aeval (contractSub n i) ((m i : Polynomial Kt)) := by
    rw [thetaMul_eq_prod, map_prod]
    exact Finset.prod_congr rfl (fun i _ => hFi i)
  rw [hprod,
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i : Fin n => (i : ℕ) < 2)]
  -- the `i < 2` filter is exactly `{j0, j1}`
  have hfilter : Finset.univ.filter (fun i : Fin n => (i : ℕ) < 2) = {j0, j1} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton, Fin.ext_iff, j0val, j1val]
    omega
  have hne : j0 ≠ j1 := by
    intro h
    have hv := congrArg Fin.val h
    rw [j0val, j1val] at hv
    omega
  rw [hfilter, Finset.prod_pair hne]
  -- value at `j0`, `j1`
  have hcs0 : contractSub n j0 = MvPolynomial.X (0 : Fin 2) := by
    have h2 : ((j0 : Fin n) : ℕ) < 2 := by rw [j0val]; omega
    rw [contractSub, dif_pos h2]
    have : (⟨((j0 : Fin n) : ℕ), h2⟩ : Fin 2) = 0 := Fin.ext j0val
    rw [this]
  have hcs1 : contractSub n j1 = MvPolynomial.X (1 : Fin 2) := by
    have h2 : ((j1 : Fin n) : ℕ) < 2 := by rw [j1val]; omega
    rw [contractSub, dif_pos h2]
    have : (⟨((j1 : Fin n) : ℕ), h2⟩ : Fin 2) = 1 := Fin.ext j1val
    rw [this]
  -- a `Dom`-witness for each `(m i)(1) ∈ ι(D)`
  have hw : ∀ i : Fin n, ∃ a : Dom,
      algebraMap Dom Kt a = Polynomial.aeval (1 : Kt) ((m i : Polynomial Kt)) := by
    intro i
    have h := (m i).2 1
    rw [map_one] at h
    obtain ⟨a, ha⟩ := h
    exact ⟨a, ha⟩
  choose wit hwit using hw
  set S : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => ¬ (i : ℕ) < 2) with hS
  set c' : Dom := ∏ i ∈ S, wit i with hc'
  -- the `i ≥ 2` product is `C (ι c')`
  have hsecond : (∏ i ∈ S, Polynomial.aeval (contractSub n i) ((m i : Polynomial Kt)))
      = MvPolynomial.C (algebraMap Dom Kt c') := by
    have hstep : ∀ i ∈ S, Polynomial.aeval (contractSub n i) ((m i : Polynomial Kt))
        = MvPolynomial.C (Polynomial.aeval (1 : Kt) ((m i : Polynomial Kt))) := by
      intro i hi
      have hi2 : ¬ ((i : Fin n) : ℕ) < 2 := by
        rw [hS, Finset.mem_filter] at hi; exact hi.2
      have hci : contractSub n i = 1 := by rw [contractSub, dif_neg hi2]
      rw [hci, aeval_one_eq_C]
    rw [Finset.prod_congr rfl hstep, ← map_prod]
    congr 1
    rw [hc', map_prod]
    exact Finset.prod_congr rfl (fun i _ => (hwit i).symm)
  rw [hcs0, hcs1, hsecond, ← incl_apply_n, ← incl_apply_n]
  -- assemble : contraction = θ₂ of the explicit tensor
  have hconst : Polynomial.C (algebraMap Dom Kt c') ∈ IntPoly Dom Kt := by
    intro d
    rw [Polynomial.aeval_C]
    exact ⟨c', rfl⟩
  set constPoly : ↥(IntPoly Dom Kt) := ⟨Polynomial.C (algebraMap Dom Kt c'), hconst⟩ with hcp
  have incl_constPoly : incl Dom Kt 2 0 constPoly = MvPolynomial.C (algebraMap Dom Kt c') := by
    rw [incl_apply_n]
    show Polynomial.aeval (MvPolynomial.X (0 : Fin 2)) (Polynomial.C (algebraMap Dom Kt c'))
        = MvPolynomial.C (algebraMap Dom Kt c')
    rw [Polynomial.aeval_C, MvPolynomial.algebraMap_eq]
  refine ⟨PiTensorProduct.tprod Dom ![m j0 * constPoly, m j1], ?_⟩
  rw [thetaN_tprod2, thetaMul_eq_prod, Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [map_mul, incl_constPoly]
  ring

/-! ## The contraction of `θₙ` of an arbitrary tensor lands in `im θ₂` -/

/-- The composite `Dom`-linear map `τ ↦ φ(θₙ τ)`.  Using a single linear map makes
the `map_smul` / `smul_mem` steps in the tensor induction use one uniform
`Dom`-module instance, sidestepping the diamond on `↥(IntPoly Dom Kt)`. -/
noncomputable def Psi (n : ℕ) :
    (⨂[Dom] (_ : Fin n), IntPoly Dom Kt) →ₗ[Dom] MvPolynomial (Fin 2) Kt :=
  ((contract n).toLinearMap.restrictScalars Dom).comp (thetaN Dom Kt n)

theorem contraction_mem (n : ℕ) (hn : 2 ≤ n)
    (τ : ⨂[Dom] (_ : Fin n), IntPoly Dom Kt) :
    contract n (thetaN Dom Kt n τ) ∈ LinearMap.range (thetaN Dom Kt 2) := by
  have key : ∀ σ : ⨂[Dom] (_ : Fin n), IntPoly Dom Kt,
      Psi n σ ∈ LinearMap.range (thetaN Dom Kt 2) := by
    intro σ
    induction σ using PiTensorProduct.induction_on' with
    | tprodCoeff r m =>
        rw [PiTensorProduct.tprodCoeff_eq_smul_tprod, map_smul]
        refine Submodule.smul_mem _ r ?_
        show contract n (thetaN Dom Kt n (PiTensorProduct.tprod Dom m))
            ∈ LinearMap.range (thetaN Dom Kt 2)
        rw [thetaN_tprod_n]
        exact contract_thetaMul_mem n hn m
    | add x y hx hy =>
        rw [map_add]
        exact Submodule.add_mem _ hx hy
  exact key τ

/-! ## The frozen `∀ n ≥ 2` lift (conditional on the `n = 2` fact `h2`) -/

/-- **Stage 4.3 (conditional).**  Given the `n = 2` non-surjectivity fact `h2`
(whose type is COPIED VERBATIM from the frozen `theta2_missing`), the canonical map
`θₙ` is not surjective for every `n ≥ 2`.  This is the genuine `∀ n` lift, packaged
with the `n = 2` milestone as a hypothesis; a follow-up closes the frozen
`thetaN_not_surjective_proof := thetaN_not_surjective_of_theta2 theta2_missing_proof`
once `theta2_missing` is ✅. -/
theorem thetaN_not_surjective_of_theta2
    (h2 : PMv ∈ IntPolyN Dom Kt 2 ∧ PMv ∉ Set.range (thetaN Dom Kt 2)) :
    ∀ n : ℕ, 2 ≤ n →
      ¬ ((IntPolyN Dom Kt n : Set (MvPolynomial (Fin n) Kt))
            ⊆ Set.range (thetaN Dom Kt n)) := by
  intro n hn hsub
  have hPnmem : (MvPolynomial.rename (Fin.castLE hn) PMv) ∈ IntPolyN Dom Kt n :=
    Pn_mem n hn h2.1
  obtain ⟨τ, hτ⟩ := hsub hPnmem
  have hmem : PMv ∈ LinearMap.range (thetaN Dom Kt 2) := by
    have h := contraction_mem n hn τ
    rwa [hτ, contract_Pn n hn] at h
  exact h2.2 (LinearMap.mem_range.mp hmem)

end Prob20.Proofs.Surjective
