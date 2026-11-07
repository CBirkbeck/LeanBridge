import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Induced Dirichlet characters

A Dirichlet character `χ₁` of modulus `q₁` is induced by a Dirichlet character `χ₂` of modulus `q₂`
dividing `q₁` if `χ₁(m) = χ₂(m)` for every integer `m` prime to `q₁`, that is, if `χ₁` is Mathlib's
`DirichletCharacter.changeLevel` of `χ₂`. A character of modulus `q ≥ 1` is primitive (Mathlib's
`DirichletCharacter.IsPrimitive`: its conductor is `q`) if and only if no character other than
itself induces it, and every character is induced by exactly one primitive character, Mathlib's
`DirichletCharacter.primitiveCharacter` at the level of its conductor. The uniqueness rests on the
invariance of the conductor under `changeLevel` (Mathlib's
`DirichletCharacter.conductor_changeLevel`) and on the injectivity of `changeLevel`; Tau Ceti's main
has the same short argument as `DirichletCharacter.IsPrimitive.changeLevel_eq_changeLevel_iff`,
which is not at the pinned commit.

## Main definitions

* `DirichletCharacter.IsInducedBy` (LMFDB `character.dirichlet.induce`): induced characters.

## Main results

* `DirichletCharacter.isInducedBy_iff`: a character is induced by `ψ` if and only if it is
  `changeLevel` of `ψ`.
* `DirichletCharacter.isPrimitive_iff_forall_isInducedBy` (LMFDB `character.dirichlet.induce`): a
  character is primitive if and only if it is induced by no character other than itself.
* `DirichletCharacter.isPrimitive_and_isInducedBy_iff` (LMFDB `character.dirichlet.induce`): every
  character is induced by a unique primitive character.
-/

namespace DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R] {q d : ℕ} (χ : DirichletCharacter R q)
  (ψ : DirichletCharacter R d)

/-- A Dirichlet character `χ` of modulus `q` is **induced** (LMFDB `character.dirichlet.induce`) by
a Dirichlet character `ψ` of modulus `d` if `d` divides `q` and `χ(m) = ψ(m)` for every integer `m`
prime to `q`. Equivalently, `χ` is Mathlib's `changeLevel` of `ψ`
(`DirichletCharacter.isInducedBy_iff`). -/
def IsInducedBy : Prop :=
  d ∣ q ∧ ∀ m : ℤ, IsCoprime m q → χ m = ψ m

lemma isInducedBy_self : χ.IsInducedBy χ :=
  ⟨dvd_rfl, fun _ _ ↦ rfl⟩

lemma isInducedBy_primitiveCharacter : χ.IsInducedBy χ.primitiveCharacter :=
  ⟨χ.conductor_dvd_level, fun _ hm ↦ (χ.primitiveCharacter_apply_of_isCoprime hm).symm⟩

variable [NeZero q]

/-- **A character is induced by `ψ` if and only if it is `changeLevel` of `ψ`.** -/
lemma isInducedBy_iff : χ.IsInducedBy ψ ↔ ∃ h : d ∣ q, changeLevel h ψ = χ := by
  refine ⟨fun ⟨h, hχ⟩ ↦ ⟨h, MulChar.ext fun u ↦ ?_⟩, fun ⟨h, hψ⟩ ↦ ⟨h, fun m hm ↦ ?_⟩⟩
  · have hu : IsCoprime ((u : ZMod q).val : ℤ) q :=
      Nat.isCoprime_iff_coprime.mpr <| ZMod.val_coe_unit_coprime u
    rw [← ZMod.natCast_zmod_val (u : ZMod q), ← Int.cast_natCast,
      ψ.changeLevel_eq_cast_of_dvd' h hu, hχ _ hu]
  · rw [← hψ, ψ.changeLevel_eq_cast_of_dvd' h hm]

/-- **A Dirichlet character of modulus `q ≥ 1` is primitive if and only if it is induced by no
character other than itself.** -/
lemma isPrimitive_iff_forall_isInducedBy :
    χ.IsPrimitive ↔ ∀ x : Σ d, DirichletCharacter R d, χ.IsInducedBy x.2 → x = ⟨q, χ⟩ := by
  refine ⟨fun hχ ⟨d, ψ⟩ hψ ↦ ?_,
    fun h ↦ congrArg Sigma.fst <| h ⟨_, _⟩ χ.isInducedBy_primitiveCharacter⟩
  rcases (χ.isInducedBy_iff ψ).mp hψ with ⟨h, rfl⟩
  have hd : d = q := h.antisymm <| (ψ.conductor_changeLevel h).symm.trans hχ ▸ ψ.conductor_dvd_level
  subst hd
  exact congrArg (Sigma.mk d) ψ.changeLevel_self.symm

/-- **Every Dirichlet character of modulus `q ≥ 1` is induced by a unique primitive character**,
the primitive character `χ.primitiveCharacter` of modulus the conductor of `χ`. -/
lemma isPrimitive_and_isInducedBy_iff (x : Σ d, DirichletCharacter R d) :
    x.2.IsPrimitive ∧ χ.IsInducedBy x.2 ↔ x = ⟨χ.conductor, χ.primitiveCharacter⟩ := by
  refine ⟨fun ⟨hx, hχ⟩ ↦ ?_, ?_⟩
  · rcases x with ⟨d, ψ⟩
    rcases (χ.isInducedBy_iff ψ).mp hχ with ⟨h, hψχ⟩
    have hd : d = χ.conductor := hx.symm.trans <| hψχ ▸ ψ.conductor_changeLevel h |>.symm
    subst hd
    exact congrArg (Sigma.mk _) <| changeLevel_injective h <|
      hψχ.trans χ.changeLevel_primitiveCharacter.symm
  · rintro rfl
    exact ⟨χ.primitiveCharacter_isPrimitive, χ.isInducedBy_primitiveCharacter⟩

end DirichletCharacter
