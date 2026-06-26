/-
Copyright (c) 2026 Prob30c formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob30c formalization
-/
import Prob30c.Defs

/-!
# Stage S0 — ring-agnostic n-absorbing API.

This file builds the general, ring-agnostic infrastructure around the textbook
predicate `IsNAbsorbing` and the absorbing number `absorbingNumber` frozen in
`Defs.lean`.  Nothing here depends on the `A q` ring model; everything is stated
for an arbitrary `{R : Type*} [CommRing R]` and `I : Ideal R`.

Main results:
* `nAbsorbing_succ`     : `IsNAbsorbing n I → IsNAbsorbing (n+1) I`  (S0.1)
* `nAbsorbing_of_le`    : monotonicity in `n`
* `not_nAbsorbing_of_not` : the contrapositive
* `absorbingNumber_eq_of` : `absorbingNumber I = k` from a two-sided witness  (S0.2)
-/

open Finset

namespace Prob30c

/-! ### Erase-product helper lemmas (over `Fin`). -/

/-- Product over `univ.erase 0` equals the product over the `succ`-shifted tail. -/
theorem prod_erase_zero {M : Type*} [CommMonoid M] {N : ℕ} (f : Fin (N + 1) → M) :
    ∏ i ∈ univ.erase (0 : Fin (N + 1)), f i = ∏ i : Fin N, f i.succ := by
  rw [Fin.univ_succ (n := N), Finset.erase_cons, Finset.prod_map]
  rfl

/-- Peeling the `0`-th factor out of a product over `univ.erase (m.succ)`. -/
theorem prod_erase_succ {M : Type*} [CommMonoid M] {N : ℕ} (f : Fin (N + 1) → M)
    (m : Fin N) :
    ∏ i ∈ univ.erase (m.succ), f i = f 0 * ∏ i ∈ univ.erase m, f i.succ := by
  rw [Fin.univ_succ (n := N),
      Finset.erase_cons_of_ne (by simp) (Fin.succ_ne_zero m).symm, Finset.prod_cons]
  congr 1
  have hset : (univ.map ⟨Fin.succ, Fin.succ_injective N⟩).erase m.succ
      = (univ.erase m).map ⟨Fin.succ, Fin.succ_injective N⟩ :=
    (Finset.map_erase _ univ m).symm
  rw [hset, Finset.prod_map]
  rfl

/-! ### S0.1 — monotonicity. -/

/-- **n-absorbing implies (n+1)-absorbing** (for every commutative ring). -/
theorem nAbsorbing_succ {R : Type*} [CommRing R] {n : ℕ} {I : Ideal R}
    (h : IsNAbsorbing n I) : IsNAbsorbing (n + 1) I := by
  intro a ha
  -- merge the first two factors `a 0, a 1` into one, giving an `(n+1)`-factor tuple.
  have hE0 : (∏ i, (Fin.cons (a 0 * a 1) (fun i : Fin n => a i.succ.succ)) i) = ∏ i, a i := by
    rw [Fin.prod_cons, Fin.prod_univ_succ a, Fin.prod_univ_succ (fun i : Fin (n + 1) => a i.succ)]
    simp only [Fin.succ_zero_eq_one']
    ring
  obtain ⟨j, hj⟩ :=
    h (Fin.cons (a 0 * a 1) (fun i : Fin n => a i.succ.succ)) (by rw [hE0]; exact ha)
  rcases j.eq_zero_or_eq_succ with rfl | ⟨k, rfl⟩
  · -- merged factor `a 0 * a 1` was dropped: re-absorb `a 0` to omit just `a 1`.
    rw [prod_erase_zero] at hj
    simp only [Fin.cons_succ] at hj
    refine ⟨1, ?_⟩
    have h2 : ∏ i ∈ univ.erase (1 : Fin (n + 2)), a i
        = a 0 * ∏ i : Fin n, a i.succ.succ := by
      rw [show (1 : Fin (n + 2)) = (0 : Fin (n + 1)).succ from (Fin.succ_zero_eq_one').symm,
          prod_erase_succ, prod_erase_zero]
    rw [h2]
    exact Ideal.mul_mem_left I _ hj
  · -- a genuine factor `a (k+2)` was dropped: same omit-one index works for `a`.
    refine ⟨k.succ.succ, ?_⟩
    have hb1 : ∏ i ∈ univ.erase k.succ,
        (Fin.cons (a 0 * a 1) (fun i : Fin n => a i.succ.succ)) i
        = (a 0 * a 1) * ∏ i ∈ univ.erase k, a i.succ.succ := by
      rw [prod_erase_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
    have ha1 : ∏ i ∈ univ.erase k.succ.succ, a i
        = (a 0 * a 1) * ∏ i ∈ univ.erase k, a i.succ.succ := by
      rw [prod_erase_succ, prod_erase_succ]
      simp only [Fin.succ_zero_eq_one']
      ring
    rw [ha1, ← hb1]
    exact hj

/-- Monotonicity of the absorbing predicate. -/
theorem nAbsorbing_of_le {R : Type*} [CommRing R] {m n : ℕ} {I : Ideal R}
    (hmn : m ≤ n) (h : IsNAbsorbing m I) : IsNAbsorbing n I := by
  induction n, hmn using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact nAbsorbing_succ ih

/-- Contrapositive of monotonicity. -/
theorem not_nAbsorbing_of_not {R : Type*} [CommRing R] {m n : ℕ} {I : Ideal R}
    (hmn : m ≤ n) (h : ¬ IsNAbsorbing n I) : ¬ IsNAbsorbing m I :=
  fun hm => h (nAbsorbing_of_le hmn hm)

/-! ### S0.2 — `absorbingNumber` from a two-sided witness. -/

/-- If `I` is `k`-absorbing but not `(k-1)`-absorbing (with `1 ≤ k`), then its
absorbing number is exactly `k`.  Both `sInf ≤ k` and `k ≤ sInf` are established. -/
theorem absorbingNumber_eq_of {R : Type*} [CommRing R] {I : Ideal R} {k : ℕ}
    (hk : 1 ≤ k) (habs : IsNAbsorbing k I) (hnot : ¬ IsNAbsorbing (k - 1) I) :
    absorbingNumber I = k := by
  have hmem : k ∈ {n : ℕ | 1 ≤ n ∧ IsNAbsorbing n I} := ⟨hk, habs⟩
  have hle : absorbingNumber I ≤ k := Nat.sInf_le hmem
  have hsmem : absorbingNumber I ∈ {n : ℕ | 1 ≤ n ∧ IsNAbsorbing n I} :=
    Nat.sInf_mem ⟨k, hmem⟩
  have hge : k ≤ absorbingNumber I := by
    by_contra hlt
    rw [not_le] at hlt
    exact hnot (nAbsorbing_of_le (by omega) hsmem.2)
  omega

end Prob30c
