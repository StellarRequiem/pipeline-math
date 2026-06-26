import Prob20.Defs

/-!
# Stage 1.2 — the residue field `D/𝔪 ≅ 𝔽₂` (`Proofs/Domain/ResidueField.lean`)

We prove `D_residue_field` (frozen in `Prob20/Theorems.lean`): the residue field
of the conductor pullback `D = 𝔽₂ + 𝔪` is exactly `𝔽₂ = ZMod 2`.

The argument: the residue map `resD : Dom →+* ZMod 2` is surjective — a ring hom,
so it commutes with the natural-number cast, and `ℕ → ZMod 2` is surjective; hence
`0 ↦ 0`, `1 ↦ 1` already exhaust `ZMod 2 = {0, 1}`. Then `mIdeal = RingHom.ker resD`
by definition, and `RingHom.quotientKerEquivOfSurjective` gives
`Dom ⧸ mIdeal ≃+* ZMod 2`.
-/

namespace Prob20.Proofs.Domain

/-- The residue map `resD : Dom →+* 𝔽₂` is surjective: every element of `ZMod 2`
is a natural-number cast, and `resD` commutes with the cast. -/
theorem resD_surjective : Function.Surjective resD := by
  intro z
  obtain ⟨n, rfl⟩ := ZMod.natCast_zmod_surjective z
  exact ⟨(n : Dom), by rw [map_natCast]⟩

/-- **`D_residue_field`.** The residue field of the conductor pullback `D` is `𝔽₂`:
`Dom ⧸ mIdeal ≃+* ZMod 2`. Since `mIdeal = RingHom.ker resD` definitionally, the
first isomorphism theorem applied to the surjective `resD` produces the equivalence. -/
theorem D_residue_field_proof : Nonempty (Dom ⧸ mIdeal ≃+* ZMod 2) :=
  ⟨RingHom.quotientKerEquivOfSurjective resD_surjective⟩

end Prob20.Proofs.Domain
