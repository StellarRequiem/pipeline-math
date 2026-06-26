/-
Copyright (c) 2026 Prob30c formalization. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prob30c formalization
-/
import Prob30c.Proofs.RingModel.Basic
import Prob30c.Proofs.Cancellation.Basic
import Prob30c.Proofs.UpperA.Basic

/-!
# Stage UX — `AX_succ2Absorbing`, the up-stairs upper bound (Step 6).

`AX_succ2Absorbing_proof q (hq : 2 ≤ q) : IsNAbsorbing (q + 2) (⊥ : Ideal (A q)[X])`.

Every family `a : Fin (q+3) → (A q)[X]` with `∏ a = 0` has an omit-one subproduct
`= 0`.  We re-run the Stage-UA case analysis **one degree higher over `D[X]`**: the
augmentation `aug : A q →+* D` extends coefficient-wise to
`augX := mapRingHom (aug q) : (A q)[X] →+* D[X]`, the domain `D[X] = 𝔽₂[t,X]`
replaces `D`, and the valuation count runs against the prime `t = C X : D[X]` (still
prime — `t` is prime in `𝔽₂[t,X]`).

The argument is the down-stairs one with the family one factor longer (`q+3` instead
of `q+2`), so the valuation budget `q` now caps the *out-of-`JX`* factors at `q`
(rather than `q-1`), giving the matching length `q+2`.  Partition by
`k := #{i | a i ∈ JX}`:

* **`k ≥ 3`.**  `JX³ = 0`, so an omit-one product still keeps three `JX`-factors and
  vanishes.
* **`k = 2` / `k = 1`.**  The `JX`-product lands (free `u₁,u₂` coordinates forced to
  vanish, read off by the coefficient-wise lifts `liftχ`) in the `s`-layer
  `secX γ · C s`; the `t`-adic count over the domain `D[X]` (`dvd_count_gen`) caps the
  number of out-of-`JX` factors at `q`, contradicting length `q+3`.

The coefficient-wise lift `liftχ` of the Stage-A `D`-coordinate functionals and the
generic valuation count `dvd_count_gen` are the only genuinely new pieces; the rest
mirrors Stage UA.  Nothing uses `decide` over `A q`.
-/

namespace Prob30c

open Polynomial

variable (q : ℕ)

/-! ## The generic `t`-adic valuation count (any domain, any prime) -/

/-- **Generic valuation count.**  In a domain `R` with a prime `p`, if a product
`(∏ g) · γ` is divisible by `p^Q` while every omit-one product is *not*, and
`p^r ∣ γ`, then `|t| + r ≤ Q`.  (This is `UpperA.dvd_count` with `Polynomial.X : D`
replaced by an arbitrary prime — used here with `R = D[X]`, `p = C X`.) -/
theorem dvd_count_gen {R : Type*} [CommRing R] [IsDomain R] {ι : Type*} [DecidableEq ι]
    {p : R} (hp : Prime p) {Q r : ℕ} (t : Finset ι) (ht : t.Nonempty)
    (g : ι → R) (γ : R)
    (hfull : p ^ Q ∣ (∏ i ∈ t, g i) * γ)
    (hγ : p ^ r ∣ γ)
    (homit : ∀ j ∈ t, ¬ p ^ Q ∣ (∏ i ∈ t.erase j, g i) * γ) :
    t.card + r ≤ Q := by
  classical
  have hXg : ∀ i ∈ t, p ∣ g i := by
    intro i hi
    by_contra hni
    apply homit i hi
    have hsplit : (∏ j ∈ t, g j) * γ = g i * ((∏ j ∈ t.erase i, g j) * γ) := by
      rw [← Finset.mul_prod_erase t g hi, mul_assoc]
    rw [hsplit] at hfull
    exact hp.pow_dvd_of_dvd_mul_left Q hni hfull
  by_contra hlt
  rw [not_le] at hlt
  have hcard : 1 ≤ t.card := Finset.card_pos.mpr ht
  obtain ⟨j, hj⟩ := ht
  apply homit j hj
  have hpe : p ^ (t.card - 1) ∣ ∏ i ∈ t.erase j, g i := by
    have h1 : (∏ _i ∈ t.erase j, p) ∣ ∏ i ∈ t.erase j, g i :=
      Finset.prod_dvd_prod_of_dvd _ g (fun i hi => hXg i (Finset.mem_of_mem_erase hi))
    rwa [Finset.prod_const, Finset.card_erase_of_mem hj] at h1
  have hdvd2 : p ^ ((t.card - 1) + r) ∣ (∏ i ∈ t.erase j, g i) * γ := by
    rw [pow_add]; exact mul_dvd_mul hpe hγ
  have hqle : Q ≤ (t.card - 1) + r := by omega
  exact dvd_trans (pow_dvd_pow _ hqle) hdvd2

/-- Product of ideal members lies in the corresponding power of the ideal. -/
theorem prod_mem_pow {R : Type*} [CommRing R] (I : Ideal R) {ι : Type*} (u : Finset ι)
    (a : ι → R) (h : ∀ i ∈ u, a i ∈ I) : ∏ i ∈ u, a i ∈ I ^ u.card := by
  classical
  induction u using Finset.induction with
  | empty => simp
  | insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.card_insert_of_notMem hx, pow_succ']
    exact Ideal.mul_mem_mul (h x (Finset.mem_insert_self x s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-! ## The coefficient-wise lift of a `D`-linear functional -/

/-- Apply a `D`-linear functional `f : A q →ₗ[D] D` coefficient-wise to a polynomial
in `(A q)[X]`, producing a polynomial in `D[X]`. -/
noncomputable def liftχ (f : A q →ₗ[D] D) (p : (A q)[X]) : D[X] :=
  Polynomial.ofFinsupp (Finsupp.mapRange f (map_zero f) p.toFinsupp)

theorem liftχ_coeff (f : A q →ₗ[D] D) (p : (A q)[X]) (n : ℕ) :
    (liftχ q f p).coeff n = f (p.coeff n) := by
  simp only [liftχ, Polynomial.coeff_ofFinsupp, Finsupp.mapRange_apply]; rfl

theorem liftχ_add (f : A q →ₗ[D] D) (p p' : (A q)[X]) :
    liftχ q f (p + p') = liftχ q f p + liftχ q f p' := by
  ext n; simp only [liftχ_coeff, Polynomial.coeff_add, map_add]

theorem liftχ_C (f : A q →ₗ[D] D) (x : A q) :
    liftχ q f (Polynomial.C x) = Polynomial.C (f x) := by
  ext n
  rw [liftχ_coeff]
  rcases eq_or_ne n 0 with h | h
  · subst h; simp [Polynomial.coeff_C]
  · simp [Polynomial.coeff_C, h, map_zero]

/-- Multiplication by a scalar polynomial (image of `D[X]`) pulls out of `liftχ`. -/
theorem liftχ_secX_mul (f : A q →ₗ[D] D) (d : D[X]) (w : (A q)[X]) :
    liftχ q f ((d.map (algebraMap D (A q))) * w) = d * liftχ q f w := by
  refine Polynomial.ext fun n => ?_
  rw [liftχ_coeff, Polynomial.coeff_mul, Polynomial.coeff_mul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [liftχ_coeff, Polynomial.coeff_map,
    show algebraMap D (A q) (d.coeff x.1) * w.coeff x.2 = (d.coeff x.1) • (w.coeff x.2)
      from (Algebra.smul_def _ _).symm, map_smul, smul_eq_mul]

theorem liftχ_zero (f : A q →ₗ[D] D) : liftχ q f 0 = 0 := by
  ext n; rw [liftχ_coeff]; simp

/-! ## The two ring homs `secX`, `augX` and the prime `t = C X` -/

/-- The coefficient-wise embedding `D[X] →+* (A q)[X]` (the "scalars"). -/
noncomputable def secX (q : ℕ) : D[X] →+* (A q)[X] := Polynomial.mapRingHom (algebraMap D (A q))

/-- The coefficient-wise augmentation `(A q)[X] →+* D[X]`. -/
noncomputable def augX (q : ℕ) : (A q)[X] →+* D[X] := Polynomial.mapRingHom (aug q)

theorem secX_apply (d : D[X]) : secX q d = d.map (algebraMap D (A q)) := rfl
theorem augX_apply (p : (A q)[X]) : augX q p = p.map (aug q) := rfl

/-- The prime `t = C X : D[X]` (the uniformizer, viewed in `𝔽₂[t,X]`). -/
noncomputable def tX : D[X] := Polynomial.C (Polynomial.X : D)

theorem tX_prime : Prime (tX) := Polynomial.prime_C_iff.mpr Polynomial.prime_X

theorem tX_pow (n : ℕ) : (tX) ^ n = Polynomial.C ((Polynomial.X : D) ^ n) := by
  rw [tX, ← Polynomial.C_pow]

/-- `augX ∘ secX = id`. -/
theorem augX_secX (d : D[X]) : augX q (secX q d) = d := by
  rw [augX_apply, secX_apply, Polynomial.map_map]
  have h : (aug q).comp (algebraMap D (A q)) = RingHom.id D :=
    RingHom.ext (fun x => by simp [aug_algebraMap])
  rw [h, Polynomial.map_id]

/-! ## The augmentation kernel `JX` and its structure -/

/-- The up-stairs augmentation ideal `JX = ker augX = (J q).map C`. -/
noncomputable def JX (q : ℕ) : Ideal ((A q)[X]) := RingHom.ker (augX q)

theorem mem_JX_ker {x : (A q)[X]} : x ∈ JX q ↔ augX q x = 0 := RingHom.mem_ker

theorem mem_JX_iff {p : (A q)[X]} : p ∈ JX q ↔ ∀ n, p.coeff n ∈ J q := by
  rw [JX, RingHom.mem_ker, augX_apply, Polynomial.ext_iff]
  simp only [Polynomial.coeff_map, Polynomial.coeff_zero, J_eq_ker, RingHom.mem_ker]

theorem JX_eq_map : JX q = (J q).map (Polynomial.C : A q →+* (A q)[X]) := by
  ext p; rw [mem_JX_iff, Ideal.mem_map_C_iff]

theorem JX_sq_eq : (JX q) ^ 2 = (J q ^ 2).map (Polynomial.C : A q →+* (A q)[X]) := by
  rw [JX_eq_map, ← Ideal.map_pow]

theorem mem_JX_sq_iff {p : (A q)[X]} : p ∈ (JX q) ^ 2 ↔ ∀ n, p.coeff n ∈ J q ^ 2 := by
  rw [JX_sq_eq, Ideal.mem_map_C_iff]

theorem JX_pow_three : (JX q) ^ 3 = (⊥ : Ideal ((A q)[X])) := by
  rw [JX_eq_map, ← Ideal.map_pow, J_pow_three, Ideal.map_bot]

theorem Cu1_mem_JX2 : Polynomial.C (u₁ q) ∈ (JX q) ^ 2 := by
  rw [mem_JX_sq_iff]; intro n; rcases eq_or_ne n 0 with h | h
  · subst h; rw [Polynomial.coeff_C_zero]; exact u1_mem_J2 q
  · rw [Polynomial.coeff_C, if_neg h]; exact Submodule.zero_mem _

theorem Cu2_mem_JX2 : Polynomial.C (u₂ q) ∈ (JX q) ^ 2 := by
  rw [mem_JX_sq_iff]; intro n; rcases eq_or_ne n 0 with h | h
  · subst h; rw [Polynomial.coeff_C_zero]; exact u2_mem_J2 q
  · rw [Polynomial.coeff_C, if_neg h]; exact Submodule.zero_mem _

theorem Cs_mem_JX2 : Polynomial.C (s q) ∈ (JX q) ^ 2 := by
  rw [mem_JX_sq_iff]; intro n; rcases eq_or_ne n 0 with h | h
  · subst h; rw [Polynomial.coeff_C_zero]; exact s_mem_J2 q
  · rw [Polynomial.coeff_C, if_neg h]; exact Submodule.zero_mem _

/-! ## The `JX²`-collapse and the `s`-annihilator over `D[X]` -/

/-- For `z ∈ JX²`, multiplication by any `w` collapses to the scalar action of the
augmentation: `w * z = secX (augX w) * z` (the `JX`-part of `w` kills `z` via
`JX³ = 0`). -/
theorem mul_JX2_collapse (w : (A q)[X]) {z : (A q)[X]} (hz : z ∈ (JX q) ^ 2) :
    w * z = secX q (augX q w) * z := by
  have hj : w - secX q (augX q w) ∈ JX q := by
    rw [JX, RingHom.mem_ker, map_sub, augX_secX, sub_self]
  have hzero : (w - secX q (augX q w)) * z = 0 := by
    have hmem : (w - secX q (augX q w)) * z ∈ (JX q) ^ 3 := by
      rw [pow_succ']; exact Ideal.mul_mem_mul hj hz
    rwa [JX_pow_three, Ideal.mem_bot] at hmem
  rw [← sub_eq_zero, ← sub_mul, hzero]

/-- **Annihilator of `C s` over `D[X]`.**  `secX e · C s = 0 ⇔ t^q ∣ e` (the `s`-layer
is the torsion module `D[X] ⧸ (t^q)`). -/
theorem s_annX (e : D[X]) : secX q e * Polynomial.C (s q) = 0 ↔ tX ^ q ∣ e := by
  rw [tX_pow, Polynomial.C_dvd_iff_dvd_coeff, Polynomial.ext_iff]
  have key : ∀ n, (secX q e * Polynomial.C (s q)).coeff n = (e.coeff n) • s q := by
    intro n
    rw [Polynomial.coeff_mul_C, secX_apply, Polynomial.coeff_map, ← Algebra.smul_def]
  constructor
  · intro h n
    rw [← smul_s_eq_zero_iff]
    have hn := h n; rw [key, Polynomial.coeff_zero] at hn; exact hn
  · intro h n
    rw [key, Polynomial.coeff_zero, smul_s_eq_zero_iff]; exact h n

/-! ## Reading the `s`-layer coordinate via the lifted functionals -/

/-- `secX`-flavoured restatement of `liftχ_secX_mul`. -/
theorem liftχ_secX_mul' (f : A q →ₗ[D] D) (d : D[X]) (w : (A q)[X]) :
    liftχ q f (secX q d * w) = d * liftχ q f w := by
  rw [secX_apply]; exact liftχ_secX_mul q f d w

/-- `liftχ f` of a single `secX d · C x` term. -/
theorem liftχ_term (f : A q →ₗ[D] D) (d : D[X]) (x : A q) :
    liftχ q f (secX q d * Polynomial.C x) = d * Polynomial.C (f x) := by
  rw [liftχ_secX_mul', liftχ_C]

/-- `liftχ f` kills `JX²` whenever `f` kills `J²`. -/
theorem liftχ_eq_zero_of_JX2 (f : A q →ₗ[D] D) (hf : ∀ x ∈ J q ^ 2, f x = 0)
    {w : (A q)[X]} (hw : w ∈ (JX q) ^ 2) : liftχ q f w = 0 := by
  refine Polynomial.ext fun n => ?_
  rw [liftχ_coeff, Polynomial.coeff_zero]
  exact hf _ ((mem_JX_sq_iff q).mp hw n)

/-- Every `z ∈ JX²` decomposes as `secX a · C u₁ + secX b · C u₂ + secX c · C s`. -/
theorem JX2_decomp {z : (A q)[X]} (hz : z ∈ (JX q) ^ 2) :
    ∃ a b c : D[X], z = secX q a * Polynomial.C (u₁ q) + secX q b * Polynomial.C (u₂ q)
      + secX q c * Polynomial.C (s q) := by
  have hspan : (JX q) ^ 2
      = Ideal.span {Polynomial.C (u₁ q), Polynomial.C (u₂ q), Polynomial.C (s q)} := by
    rw [JX_sq_eq, J_sq_ideal, Ideal.map_span]
    congr 1
    simp only [Set.image_insert_eq, Set.image_singleton]
  rw [hspan] at hz
  rw [Submodule.mem_span_insert] at hz
  obtain ⟨α, z₁, hz₁, rfl⟩ := hz
  rw [Submodule.mem_span_insert] at hz₁
  obtain ⟨β, z₂, hz₂, rfl⟩ := hz₁
  rw [Submodule.mem_span_singleton] at hz₂
  obtain ⟨γ, rfl⟩ := hz₂
  refine ⟨augX q α, augX q β, augX q γ, ?_⟩
  rw [smul_eq_mul, smul_eq_mul, smul_eq_mul,
    mul_JX2_collapse q α (Cu1_mem_JX2 q), mul_JX2_collapse q β (Cu2_mem_JX2 q),
    mul_JX2_collapse q γ (Cs_mem_JX2 q), add_assoc]

/-- If `z ∈ JX²` is killed by a nonzero scalar `secX e` (`e ∈ D[X]` a domain), then its
free `u₁, u₂` coordinates vanish and `z` lies in the `s`-layer: `z = secX γ · C s`. -/
theorem eq_sX {z : (A q)[X]} (hz : z ∈ (JX q) ^ 2) {e : D[X]} (he : e ≠ 0)
    (h0 : secX q e * z = 0) : ∃ γ : D[X], z = secX q γ * Polynomial.C (s q) := by
  obtain ⟨a, b, c, rfl⟩ := JX2_decomp q hz
  have expand : secX q e * (secX q a * Polynomial.C (u₁ q) + secX q b * Polynomial.C (u₂ q)
        + secX q c * Polynomial.C (s q))
      = secX q (e * a) * Polynomial.C (u₁ q) + secX q (e * b) * Polynomial.C (u₂ q)
        + secX q (e * c) * Polynomial.C (s q) := by
    simp only [mul_add, ← mul_assoc, map_mul]
  have ha : e * a = 0 := by
    have h1 : liftχ q (χu1 q) (secX q e * (secX q a * Polynomial.C (u₁ q)
        + secX q b * Polynomial.C (u₂ q) + secX q c * Polynomial.C (s q))) = e * a := by
      rw [expand, liftχ_add, liftχ_add, liftχ_term, liftχ_term, liftχ_term,
        χu1_u1, χu1_u2, χu1_s, Polynomial.C_1, Polynomial.C_0,
        mul_zero, mul_zero, mul_one, add_zero, add_zero]
    rw [h0, liftχ_zero] at h1; exact h1.symm
  have hb : e * b = 0 := by
    have h1 : liftχ q (χu2 q) (secX q e * (secX q a * Polynomial.C (u₁ q)
        + secX q b * Polynomial.C (u₂ q) + secX q c * Polynomial.C (s q))) = e * b := by
      rw [expand, liftχ_add, liftχ_add, liftχ_term, liftχ_term, liftχ_term,
        χu2_u1, χu2_u2, χu2_s, Polynomial.C_1, Polynomial.C_0,
        mul_zero, mul_zero, mul_one, zero_add, add_zero]
    rw [h0, liftχ_zero] at h1; exact h1.symm
  have ha0 : a = 0 := (mul_eq_zero.mp ha).resolve_left he
  have hb0 : b = 0 := (mul_eq_zero.mp hb).resolve_left he
  exact ⟨c, by rw [ha0, hb0, map_zero, zero_mul, zero_mul, zero_add, zero_add]⟩

/-! ## The `s`-layer count over `D[X]` -/

/-- **Core count over `D[X]`.**  If the `JX`-product reduced to `secX γ · C s`, every
out-of-`JX` factor `c i` has `augX (c i) ≠ 0`, `t^r ∣ γ`, the full product vanishes,
and every omit-one product is nonzero, then `t.card + r ≤ q`. -/
theorem coreX_count {ι : Type*} [DecidableEq ι] (q : ℕ) (γ : D[X]) (t : Finset ι)
    (ht : t.Nonempty) (c : ι → (A q)[X]) (_hc : ∀ i ∈ t, augX q (c i) ≠ 0) (r : ℕ)
    (hγr : tX ^ r ∣ γ)
    (hfull : (secX q γ * Polynomial.C (s q)) * (∏ i ∈ t, c i) = 0)
    (homit : ∀ j ∈ t, (secX q γ * Polynomial.C (s q)) * (∏ i ∈ t.erase j, c i) ≠ 0) :
    t.card + r ≤ q := by
  classical
  have hsJ2 : secX q γ * Polynomial.C (s q) ∈ (JX q) ^ 2 :=
    Ideal.mul_mem_left _ _ (Cs_mem_JX2 q)
  have hred : ∀ u : Finset ι,
      (secX q γ * Polynomial.C (s q)) * (∏ i ∈ u, c i)
        = secX q ((∏ i ∈ u, augX q (c i)) * γ) * Polynomial.C (s q) := by
    intro u
    rw [mul_comm, mul_JX2_collapse q (∏ i ∈ u, c i) hsJ2, map_prod, ← mul_assoc, ← map_mul]
  have hfull' : tX ^ q ∣ (∏ i ∈ t, augX q (c i)) * γ := by
    rw [← s_annX, ← hred]; exact hfull
  have homit' : ∀ j ∈ t, ¬ tX ^ q ∣ (∏ i ∈ t.erase j, augX q (c i)) * γ := by
    intro j hj hdvd
    apply homit j hj
    rw [hred, s_annX]; exact hdvd
  exact dvd_count_gen tX_prime t ht (fun i => augX q (c i)) γ hfull' hγr homit'

/-! ## The degree-1 functionals lifted (for the `k = 1` reduction) -/

/-- A `JX`-element whose lifted degree-1 coordinates all vanish lies in `JX²`. -/
theorem mem_JX2_of_χe_zero {z : (A q)[X]} (hz : z ∈ JX q)
    (h1 : ∀ n, χe1 q (z.coeff n) = 0) (h2 : ∀ n, χe2 q (z.coeff n) = 0)
    (h3 : ∀ n, χe3 q (z.coeff n) = 0) : z ∈ (JX q) ^ 2 := by
  rw [mem_JX_sq_iff]; intro n
  exact mem_J2_of_χe_zero q ((mem_JX_iff q).mp hz n) (h1 n) (h2 n) (h3 n)

/-! ## `AX_succ2Absorbing` — the up-stairs upper bound -/

/-- **`AX_succ2Absorbing` (Step 6).**  `⊥ : Ideal (A q)[X]` is `(q+2)`-absorbing:
every product of `q+3` polynomials that vanishes has an omit-one subproduct that
already vanishes.  The down-stairs argument run one degree higher over `D[X]`. -/
theorem AX_succ2Absorbing_proof (q : ℕ) (hq : 2 ≤ q) :
    IsNAbsorbing (q + 2) (⊥ : Ideal ((A q)[X])) := by
  classical
  intro a hprod
  rw [Ideal.mem_bot] at hprod
  by_contra hcon
  simp only [not_exists] at hcon
  have hirr : ∀ j : Fin (q + 3), (∏ i ∈ Finset.univ.erase j, a i) ≠ 0 := by
    intro j hj; exact hcon j (by rw [Ideal.mem_bot]; exact hj)
  set S : Finset (Fin (q + 3)) := Finset.univ.filter (fun i => a i ∈ JX q) with hS
  set T : Finset (Fin (q + 3)) := Finset.univ.filter (fun i => a i ∉ JX q) with hT
  have hpart : (∏ i ∈ S, a i) * (∏ i ∈ T, a i) = ∏ i, a i :=
    Finset.prod_filter_mul_prod_filter_not _ _ _
  have hcardST : S.card + T.card = q + 3 := by
    rw [hS, hT, Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have haugT : ∀ i ∈ T, augX q (a i) ≠ 0 := by
    intro i hi
    rw [hT, Finset.mem_filter, mem_JX_ker] at hi
    exact hi.2
  have hprodT_ne : (∏ i ∈ T, augX q (a i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr haugT
  have homit_split : ∀ j ∈ T,
      (∏ i ∈ S, a i) * (∏ i ∈ T.erase j, a i) = ∏ i ∈ Finset.univ.erase j, a i := by
    intro j hj
    have hdisj : Disjoint S (T.erase j) :=
      (Finset.disjoint_filter_filter_not Finset.univ Finset.univ
        (fun i => a i ∈ JX q)).mono_right (Finset.erase_subset _ _)
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
      by_cases hiJ : a i ∈ JX q
      · exact Or.inl hiJ
      · exact Or.inr ⟨hij, hiJ⟩
  -- `k = 0` is impossible
  by_cases h0 : S.card = 0
  · rw [Finset.card_eq_zero] at h0
    have hTall : ∀ i : Fin (q + 3), i ∈ T := by
      intro i
      rw [hT, Finset.mem_filter]
      refine ⟨Finset.mem_univ i, ?_⟩
      intro hiJ
      have : i ∈ S := by rw [hS, Finset.mem_filter]; exact ⟨Finset.mem_univ i, hiJ⟩
      rw [h0] at this; exact absurd this (Finset.notMem_empty i)
    have hz : augX q (∏ i, a i) = 0 := by rw [hprod, map_zero]
    rw [map_prod, Finset.prod_eq_zero_iff] at hz
    obtain ⟨i, _, hi⟩ := hz
    exact haugT i (hTall i) hi
  -- `S.card ≤ q + 2`, so `T` is nonempty
  have hScardlt : S.card < q + 3 := by
    by_contra hge
    rw [not_lt] at hge
    have hSU : S = Finset.univ :=
      Finset.eq_univ_of_card S (by
        have hle := Finset.card_le_univ S
        rw [Fintype.card_fin] at hle ⊢; omega)
    have hSall : ∀ i : Fin (q + 3), a i ∈ JX q := by
      intro i
      have : i ∈ S := by rw [hSU]; exact Finset.mem_univ i
      rw [hS, Finset.mem_filter] at this; exact this.2
    have hq3 : 0 < q + 3 := by omega
    apply hirr ⟨0, hq3⟩
    have hcarderase : (Finset.univ.erase (⟨0, hq3⟩ : Fin (q + 3))).card = q + 2 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
      omega
    have hmem : ∏ i ∈ Finset.univ.erase (⟨0, hq3⟩ : Fin (q + 3)), a i
        ∈ (JX q) ^ (Finset.univ.erase (⟨0, hq3⟩ : Fin (q + 3))).card :=
      prod_mem_pow (JX q) _ a (fun i _ => hSall i)
    rw [hcarderase] at hmem
    have hle : (JX q) ^ (q + 2) ≤ (JX q) ^ 3 := Ideal.pow_le_pow_right (by omega)
    rw [JX_pow_three] at hle
    exact Ideal.mem_bot.mp (hle hmem)
  have hTne : T.Nonempty := by rw [← Finset.card_pos]; omega
  -- `k ≥ 3`: omit a `T`-index, keep all `S.card ≥ 3` `JX`-factors
  by_cases h3 : 3 ≤ S.card
  · obtain ⟨j, hjT⟩ := hTne
    apply hirr j
    rw [← homit_split j hjT]
    have hSmem : ∏ i ∈ S, a i ∈ (JX q) ^ S.card :=
      prod_mem_pow (JX q) S a (fun i hi => by rw [hS, Finset.mem_filter] at hi; exact hi.2)
    have hle : (JX q) ^ S.card ≤ (JX q) ^ 3 := Ideal.pow_le_pow_right h3
    rw [JX_pow_three] at hle
    rw [Ideal.mem_bot.mp (hle hSmem), zero_mul]
  rw [not_le] at h3
  -- `S.card ∈ {1, 2}`: the `JX`-product reduces to the `s`-layer; the count caps `T.card`
  set z : (A q)[X] := ∏ i ∈ S, a i with hzdef
  have hfullz : z * (∏ i ∈ T, a i) = 0 := by rw [hzdef, hpart, hprod]
  have homitz : ∀ j ∈ T, z * (∏ i ∈ T.erase j, a i) ≠ 0 := by
    intro j hj; rw [hzdef, homit_split j hj]; exact hirr j
  have hdne : augX q (∏ i ∈ T, a i) ≠ 0 := by rw [map_prod]; exact hprodT_ne
  have hzJ2 : z ∈ (JX q) ^ 2 := by
    rcases (by omega : S.card = 1 ∨ S.card = 2) with hk | hk
    · -- `k = 1`: upgrade `z ∈ JX` to `z ∈ JX²` via the lifted degree-1 functionals
      obtain ⟨i₀, hSi₀⟩ := Finset.card_eq_one.mp hk
      have hziJ : z ∈ JX q := by
        rw [hzdef, hSi₀, Finset.prod_singleton]
        have : i₀ ∈ S := by rw [hSi₀]; exact Finset.mem_singleton_self i₀
        rw [hS, Finset.mem_filter] at this; exact this.2
      have hdz_mem : secX q (augX q (∏ i ∈ T, a i)) * z ∈ (JX q) ^ 2 := by
        have hCsplit : (∏ i ∈ T, a i) - secX q (augX q (∏ i ∈ T, a i)) ∈ JX q := by
          rw [mem_JX_ker, map_sub, augX_secX, sub_self]
        have hexp : secX q (augX q (∏ i ∈ T, a i)) * z
            = - (z * ((∏ i ∈ T, a i) - secX q (augX q (∏ i ∈ T, a i)))) := by
          rw [mul_sub, hfullz]; ring
        rw [hexp]
        exact Submodule.neg_mem _ (by rw [pow_two]; exact Ideal.mul_mem_mul hziJ hCsplit)
      have χe_coord : ∀ (f : A q →ₗ[D] D), (∀ x ∈ J q ^ 2, f x = 0) →
          ∀ n, f (z.coeff n) = 0 := by
        intro f hf n
        have hz0 : liftχ q f (secX q (augX q (∏ i ∈ T, a i)) * z) = 0 :=
          liftχ_eq_zero_of_JX2 q f hf hdz_mem
        rw [liftχ_secX_mul'] at hz0
        have hzero := (mul_eq_zero.mp hz0).resolve_left hdne
        have hc := liftχ_coeff q f z n
        rw [hzero, Polynomial.coeff_zero] at hc; exact hc.symm
      exact mem_JX2_of_χe_zero q hziJ (χe_coord (χe1 q) (fun x hx => χe1_J2 q hx))
        (χe_coord (χe2 q) (fun x hx => χe2_J2 q hx)) (χe_coord (χe3 q) (fun x hx => χe3_J2 q hx))
    · -- `k = 2`: `z = a i₁ * a i₂ ∈ JX²` directly
      obtain ⟨i₁, i₂, hne, hSi⟩ := Finset.card_eq_two.mp hk
      have hi₁ : a i₁ ∈ JX q := by
        have : i₁ ∈ S := by rw [hSi]; exact Finset.mem_insert_self _ _
        rw [hS, Finset.mem_filter] at this; exact this.2
      have hi₂ : a i₂ ∈ JX q := by
        have : i₂ ∈ S := by rw [hSi]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
        rw [hS, Finset.mem_filter] at this; exact this.2
      have hzi : z = a i₁ * a i₂ := by
        rw [hzdef, hSi, Finset.prod_insert (by simp [hne]), Finset.prod_singleton]
      rw [hzi, pow_two]; exact Ideal.mul_mem_mul hi₁ hi₂
  -- common tail: reduce `z` to the `s`-layer and run the `D[X]`-valuation count
  have hsecXez0 : secX q (augX q (∏ i ∈ T, a i)) * z = 0 := by
    rw [← mul_JX2_collapse q (∏ i ∈ T, a i) hzJ2, mul_comm]; exact hfullz
  obtain ⟨γ, hγeq⟩ := eq_sX q hzJ2 hdne hsecXez0
  have hb := coreX_count q γ T hTne a haugT 0 (by rw [pow_zero]; exact one_dvd _)
    (by rw [← hγeq]; exact hfullz) (fun j hj => by rw [← hγeq]; exact homitz j hj)
  omega

end Prob30c
