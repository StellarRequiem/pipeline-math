/-
Copyright (c) 2026 Prob27b formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob27b formalization
-/
import Prob27b.Defs

/-!
# Stage A — `R` is the 8-dimensional associative algebra (`RingModel/`)

This support file turns the frozen subalgebra `R := Algebra.adjoin (ZMod 2)
{mE,mF,mU,mV}` into something computable:

* **A.** The full `8 × 8` multiplication table of the basis `{e,f,u,v,p,q,s,w}`,
  every one of the 64 products as an `R`-equality, bundled into the simp set
  `mul_table`. Plus char-2 facts (`x + x = 0`) and `e + f = 1`.
* **B.** `s_ne_zero : (s : R) ≠ 0`.
* **C.** the spanning / generic-element lemma `R_generic`: every `r : R` is a
  `ZMod 2`-combination of the eight basis elements; together with the cleaner
  packaging `R_span_eq_top` (`Submodule.span … {e,…,w} = ⊤`).

All proofs reduce ring identities to decidable `8 × 8` matrix equalities over
`ZMod 2`; no `native_decide`, no `sorry`, no custom axioms.
-/

namespace Prob27b

open Matrix

/-! ## Guardrails: `R` is genuinely noncommutative -/

/-- `R` is noncommutative: `u * v = p ≠ q = v * u`. Never add a `Comm` instance. -/
example : (u : R) * v ≠ v * u := by decide

/-! ## A. The multiplication table

Every product of two basis elements, as an `R`-equality. The 24 nonzero products
are listed first (matching the table in `BLUEPRINT.md` Part −1 §2), then all the
zero products. Everything is collected into the `@[simp]` set `mul_table` so that
later stages can rewrite any product of basis elements to normal form.

Each equality reduces to an `8 × 8` `ZMod 2` matrix identity, discharged by the
kernel `decide` (no axioms added). -/

-- The 24 nonzero products.
@[simp] theorem e_mul_e : (e : R) * e = e := by decide
@[simp] theorem e_mul_u : (e : R) * u = u := by decide
@[simp] theorem e_mul_p : (e : R) * p = p := by decide
@[simp] theorem e_mul_s : (e : R) * s = s := by decide
@[simp] theorem f_mul_f : (f : R) * f = f := by decide
@[simp] theorem f_mul_v : (f : R) * v = v := by decide
@[simp] theorem f_mul_q : (f : R) * q = q := by decide
@[simp] theorem f_mul_w : (f : R) * w = w := by decide
@[simp] theorem u_mul_f : (u : R) * f = u := by decide
@[simp] theorem u_mul_v : (u : R) * v = p := by decide
@[simp] theorem u_mul_q : (u : R) * q = s := by decide
@[simp] theorem v_mul_e : (v : R) * e = v := by decide
@[simp] theorem v_mul_u : (v : R) * u = q := by decide
@[simp] theorem v_mul_p : (v : R) * p = w := by decide
@[simp] theorem p_mul_e : (p : R) * e = p := by decide
@[simp] theorem p_mul_u : (p : R) * u = s := by decide
@[simp] theorem q_mul_f : (q : R) * f = q := by decide
@[simp] theorem q_mul_v : (q : R) * v = w := by decide
@[simp] theorem s_mul_f : (s : R) * f = s := by decide
@[simp] theorem w_mul_e : (w : R) * e = w := by decide

-- The 40 zero products (everything not listed above).
@[simp] theorem e_mul_f : (e : R) * f = 0 := by decide
@[simp] theorem e_mul_v : (e : R) * v = 0 := by decide
@[simp] theorem e_mul_q : (e : R) * q = 0 := by decide
@[simp] theorem e_mul_w : (e : R) * w = 0 := by decide
@[simp] theorem f_mul_e : (f : R) * e = 0 := by decide
@[simp] theorem f_mul_u : (f : R) * u = 0 := by decide
@[simp] theorem f_mul_p : (f : R) * p = 0 := by decide
@[simp] theorem f_mul_s : (f : R) * s = 0 := by decide
@[simp] theorem u_mul_e : (u : R) * e = 0 := by decide
@[simp] theorem u_mul_u : (u : R) * u = 0 := by decide
@[simp] theorem u_mul_p : (u : R) * p = 0 := by decide
@[simp] theorem u_mul_s : (u : R) * s = 0 := by decide
@[simp] theorem u_mul_w : (u : R) * w = 0 := by decide
@[simp] theorem v_mul_f : (v : R) * f = 0 := by decide
@[simp] theorem v_mul_v : (v : R) * v = 0 := by decide
@[simp] theorem v_mul_q : (v : R) * q = 0 := by decide
@[simp] theorem v_mul_s : (v : R) * s = 0 := by decide
@[simp] theorem v_mul_w : (v : R) * w = 0 := by decide
@[simp] theorem p_mul_f : (p : R) * f = 0 := by decide
@[simp] theorem p_mul_v : (p : R) * v = 0 := by decide
@[simp] theorem p_mul_p : (p : R) * p = 0 := by decide
@[simp] theorem p_mul_q : (p : R) * q = 0 := by decide
@[simp] theorem p_mul_s : (p : R) * s = 0 := by decide
@[simp] theorem p_mul_w : (p : R) * w = 0 := by decide
@[simp] theorem q_mul_e : (q : R) * e = 0 := by decide
@[simp] theorem q_mul_u : (q : R) * u = 0 := by decide
@[simp] theorem q_mul_p : (q : R) * p = 0 := by decide
@[simp] theorem q_mul_q : (q : R) * q = 0 := by decide
@[simp] theorem q_mul_s : (q : R) * s = 0 := by decide
@[simp] theorem q_mul_w : (q : R) * w = 0 := by decide
@[simp] theorem s_mul_e : (s : R) * e = 0 := by decide
@[simp] theorem s_mul_u : (s : R) * u = 0 := by decide
@[simp] theorem s_mul_v : (s : R) * v = 0 := by decide
@[simp] theorem s_mul_p : (s : R) * p = 0 := by decide
@[simp] theorem s_mul_q : (s : R) * q = 0 := by decide
@[simp] theorem s_mul_s : (s : R) * s = 0 := by decide
@[simp] theorem s_mul_w : (s : R) * w = 0 := by decide
@[simp] theorem w_mul_f : (w : R) * f = 0 := by decide
@[simp] theorem w_mul_u : (w : R) * u = 0 := by decide
@[simp] theorem w_mul_v : (w : R) * v = 0 := by decide
@[simp] theorem w_mul_p : (w : R) * p = 0 := by decide
@[simp] theorem w_mul_q : (w : R) * q = 0 := by decide
@[simp] theorem w_mul_s : (w : R) * s = 0 := by decide
@[simp] theorem w_mul_w : (w : R) * w = 0 := by decide

/-! ## Char-2 and unit facts -/

/-- `e + f = 1` (the two vertex idempotents sum to the identity matrix). -/
@[simp] theorem e_add_f : (e : R) + f = 1 := by decide

/-- Characteristic two: every element is its own additive inverse. -/
theorem add_self (x : R) : x + x = 0 := by
  have : (2 : ZMod 2) • x = 0 := by
    rw [show (2 : ZMod 2) = 0 from by decide, zero_smul]
  simpa [two_smul] using this

/-- `(2 : R) • x = 0`, the scalar form of characteristic two. -/
theorem two_smul_eq_zero (x : R) : (2 : R) • x = 0 := by
  rw [show (2 : R) = 0 from by decide, zero_smul]

/-! ## B. `s ≠ 0`

`s = u * v * u` has matrix `mU * mV * mU` with entry `(6,1) = 1`, so it is a
nonzero element of `R`. -/

/-- `s ≠ 0` in `R`. The third stage (`Fe_witness`) needs exactly this. -/
theorem s_ne_zero : (s : R) ≠ 0 := by decide

/-! ## C. Spanning / generic-element lemma

We prove that the eight basis elements span `R` over `ZMod 2`. The strategy:

1. `Bset := {e,f,u,v,p,q,s,w} : Set R`, with `Bspan := Submodule.span (ZMod 2) Bset`.
2. `Bspan` is closed under multiplication (`Bspan_mul_closed`): by
   `Submodule.span_mul_span` it suffices that each of the 64 products of basis
   elements lies in `Bspan`, which the `mul_table` simp set settles.
3. Hence `Bspan` underlies a subalgebra `Bsub` containing `e,f,u,v` and `1`.
4. The algebra generated by `e,f,u,v` inside `↥R` is everything
   (`Algebra.adjoin_adjoin_coe_preimage`), so `Bsub = ⊤`, i.e. `Bspan = ⊤`.
5. Reading off membership of an arbitrary `r : R` in `Bspan` gives the explicit
   coefficient decomposition `R_generic`. -/

/-- The eight basis elements of `R`, as a set. -/
def Bset : Set R := {e, f, u, v, p, q, s, w}

/-- The `ZMod 2`-span of the eight basis elements. -/
def Bspan : Submodule (ZMod 2) R := Submodule.span (ZMod 2) Bset

theorem subset_Bspan {x : R} (hx : x ∈ Bset) : x ∈ Bspan :=
  Submodule.subset_span hx

theorem e_mem_Bspan : (e : R) ∈ Bspan := subset_Bspan (by simp [Bset])
theorem f_mem_Bspan : (f : R) ∈ Bspan := subset_Bspan (by simp [Bset])
theorem u_mem_Bspan : (u : R) ∈ Bspan := subset_Bspan (by simp [Bset])
theorem v_mem_Bspan : (v : R) ∈ Bspan := subset_Bspan (by simp [Bset])
theorem p_mem_Bspan : (p : R) ∈ Bspan := subset_Bspan (by simp [Bset])
theorem q_mem_Bspan : (q : R) ∈ Bspan := subset_Bspan (by simp [Bset])
theorem s_mem_Bspan : (s : R) ∈ Bspan := subset_Bspan (by simp [Bset])
theorem w_mem_Bspan : (w : R) ∈ Bspan := subset_Bspan (by simp [Bset])

theorem one_mem_Bspan : (1 : R) ∈ Bspan := by
  have h1 : (1 : R) = e + f := by rw [e_add_f]
  rw [h1]
  exact Submodule.add_mem _ e_mem_Bspan f_mem_Bspan

/-- A basis element (or `0`) lies in `Bspan`. Helper for closing the 64
product-membership goals after rewriting via `mul_table`. -/
private theorem mem_basis_or_zero {x : R}
    (h : x = 0 ∨ x ∈ Bset) : x ∈ Bspan := by
  rcases h with rfl | h
  · exact Submodule.zero_mem _
  · exact subset_Bspan h

theorem basis_mul_mem (m : R) (hm : m ∈ Bset) (n : R) (hn : n ∈ Bset) :
    m * n ∈ Bspan := by
  simp only [Bset, Set.mem_insert_iff, Set.mem_singleton_iff] at hm hn
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    refine mem_basis_or_zero ?_ <;>
    simp only [Bset, Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true,
      e_mul_e, e_mul_f,
      e_mul_u, e_mul_v, e_mul_p, e_mul_q, e_mul_s, e_mul_w, f_mul_e, f_mul_f,
      f_mul_u, f_mul_v, f_mul_p, f_mul_q, f_mul_s, f_mul_w, u_mul_e, u_mul_f,
      u_mul_u, u_mul_v, u_mul_p, u_mul_q, u_mul_s, u_mul_w, v_mul_e, v_mul_f,
      v_mul_u, v_mul_v, v_mul_p, v_mul_q, v_mul_s, v_mul_w, p_mul_e, p_mul_f,
      p_mul_u, p_mul_v, p_mul_p, p_mul_q, p_mul_s, p_mul_w, q_mul_e, q_mul_f,
      q_mul_u, q_mul_v, q_mul_p, q_mul_q, q_mul_s, q_mul_w, s_mul_e, s_mul_f,
      s_mul_u, s_mul_v, s_mul_p, s_mul_q, s_mul_s, s_mul_w, w_mul_e, w_mul_f,
      w_mul_u, w_mul_v, w_mul_p, w_mul_q, w_mul_s, w_mul_w]

/-- `Bspan` is closed under multiplication: `Bspan * Bspan ≤ Bspan`. -/
theorem Bspan_mul_closed : Bspan * Bspan ≤ Bspan := by
  rw [Bspan, Submodule.span_mul_span, Submodule.span_le]
  rintro _ ⟨m, hm, n, hn, rfl⟩
  exact basis_mul_mem m hm n hn

/-- `Bspan`, packaged as a subalgebra of `↥R`: the span is closed under `+`,
`0`, scalar multiplication (it is a submodule), `*` (`Bspan_mul_closed`), and
contains `1` (`one_mem_Bspan`) and the image of `ZMod 2` (scalar multiples of
`1`). -/
def Bsub : Subalgebra (ZMod 2) R where
  carrier := Bspan
  mul_mem' {a b} ha hb := Bspan_mul_closed (Submodule.mul_mem_mul ha hb)
  one_mem' := one_mem_Bspan
  add_mem' {a b} ha hb := Bspan.add_mem ha hb
  zero_mem' := Bspan.zero_mem
  algebraMap_mem' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Bspan.smul_mem r one_mem_Bspan

theorem mem_Bsub_iff {x : R} : x ∈ Bsub ↔ x ∈ Bspan := Iff.rfl

/-- The four generators `e,f,u,v` generate all of `↥R` as a `ZMod 2`-algebra. -/
theorem adjoin_efuv_eq_top :
    Algebra.adjoin (ZMod 2) ({e, f, u, v} : Set R) = ⊤ := by
  refine le_antisymm le_top ?_
  have htop : Algebra.adjoin (ZMod 2)
      (Subtype.val ⁻¹' ({mE, mF, mU, mV} : Set Mat) : Set R) = ⊤ :=
    Algebra.adjoin_adjoin_coe_preimage
  refine le_trans (le_of_eq htop.symm) ?_
  apply Algebra.adjoin_le
  rintro x hx
  -- `x ∈ Subtype.val ⁻¹' {mE,mF,mU,mV}`, i.e. `x.val ∈ {mE,mF,mU,mV}`.
  simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  have he : (e : R).val = mE := rfl
  have hf : (f : R).val = mF := rfl
  have hu : (u : R).val = mU := rfl
  have hv : (v : R).val = mV := rfl
  rcases hx with h | h | h | h
  · have : x = e := Subtype.ext (h.trans he.symm); subst this
    exact Algebra.subset_adjoin (by simp)
  · have : x = f := Subtype.ext (h.trans hf.symm); subst this
    exact Algebra.subset_adjoin (by simp)
  · have : x = u := Subtype.ext (h.trans hu.symm); subst this
    exact Algebra.subset_adjoin (by simp)
  · have : x = v := Subtype.ext (h.trans hv.symm); subst this
    exact Algebra.subset_adjoin (by simp)

/-- The span of the eight basis elements is all of `R`. -/
theorem Bspan_eq_top : Bspan = ⊤ := by
  have hBsub : Bsub = ⊤ := by
    rw [eq_top_iff, ← adjoin_efuv_eq_top]
    apply Algebra.adjoin_le
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact e_mem_Bspan
    · exact f_mem_Bspan
    · exact u_mem_Bspan
    · exact v_mem_Bspan
  -- transfer subalgebra-`⊤` to submodule-`⊤`
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Bsub := by rw [hBsub]; exact Algebra.mem_top
  exact hx

/-- Spanning lemma, packaged form: the `ZMod 2`-span of `{e,f,u,v,p,q,s,w}` is
all of `R`. -/
theorem R_span_eq_top :
    Submodule.span (ZMod 2) ({e, f, u, v, p, q, s, w} : Set R) = ⊤ :=
  Bspan_eq_top

/-- **Generic-element lemma.** Every `r : R` is a `ZMod 2`-linear combination of
the eight basis elements `e,f,u,v,p,q,s,w`. This is what lets Stage B reduce
`∀ r, F r = 0` to the eight scalar coefficients. -/
theorem R_generic (r : R) :
    ∃ α β γ δ η θ ι κ : ZMod 2,
      r = α • e + β • f + γ • u + δ • v + η • p + θ • q + ι • s + κ • w := by
  have hr : r ∈ Bspan := Bspan_eq_top ▸ Submodule.mem_top
  rw [Bspan, Bset, Submodule.mem_span_insert] at hr
  obtain ⟨α, r1, h1, rfl⟩ := hr
  rw [Submodule.mem_span_insert] at h1
  obtain ⟨β, r2, h2, rfl⟩ := h1
  rw [Submodule.mem_span_insert] at h2
  obtain ⟨γ, r3, h3, rfl⟩ := h2
  rw [Submodule.mem_span_insert] at h3
  obtain ⟨δ, r4, h4, rfl⟩ := h3
  rw [Submodule.mem_span_insert] at h4
  obtain ⟨η, r5, h5, rfl⟩ := h4
  rw [Submodule.mem_span_insert] at h5
  obtain ⟨θ, r6, h6, rfl⟩ := h5
  rw [Submodule.mem_span_insert] at h6
  obtain ⟨ι, r7, h7, rfl⟩ := h6
  rw [Submodule.mem_span_singleton] at h7
  obtain ⟨κ, rfl⟩ := h7
  exact ⟨α, β, γ, δ, η, θ, ι, κ, by abel⟩

end Prob27b
