import Mathlib.FieldTheory.KrullTopology
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import LeanBridge.ForMathlib.NumberTheory.Artin.Basic

/-!
# The Dirichlet character of a one-dimensional Artin representation

A one-dimensional Artin representation `ρ` of `Gal(ℚ̄/ℚ)` acts by the scalars `det ρ(σ)`. Suppose
that `ρ` is trivial on `Gal(ℚ̄/ℚ(ζ_n))`, the kernel of the mod-`n` cyclotomic character
`χ_n : Gal(ℚ̄/ℚ) → (ℤ/nℤ)ˣ`, `σ(ζ) = ζ ^ χ_n(σ)` for the `n`-th roots of unity `ζ`; equivalently,
the Artin field of `ρ` lies in `ℚ(ζ_n)`. Since `χ_n` is surjective, it induces the canonical
isomorphism `Gal(ℚ(ζ_n)/ℚ) ≅ (ℤ/nℤ)ˣ`, and `σ ↦ det ρ(σ)` factors through it: this gives a
homomorphism `(ℤ/nℤ)ˣ → ℂˣ`, which extended by `0` is the Dirichlet character `χ_ρ` modulo `n`.
The construction is a bijection between the one-dimensional representations trivial on `ker χ_n`,
up to isomorphism, and the Dirichlet characters modulo `n`, and it is compatible with replacing `n`
by a multiple.

By the Kronecker–Weber theorem, which is in neither Mathlib nor Tau Ceti, every one-dimensional
Artin representation is trivial on `ker χ_n` for some `n`, so that `χ_ρ` is defined for all of them;
the results here assume it for the given `n`. The LMFDB takes `n` to be the conductor of `ρ`, at
which `χ_ρ` is primitive; that the Artin conductor of `ρ` is the conductor of `χ_ρ` is a further
consequence of class field theory, not proved here.

## Main definitions

* `Rat.cyclotomicCharacterMod`: the mod-`n` cyclotomic character of `ℚ`.
* `Representation.detCharacter`: the character `σ ↦ det ρ(σ)`.
* `Representation.dirichletCharacter` (LMFDB `artin.dimensionone`): the Dirichlet character
  modulo `n` of a one-dimensional Artin representation trivial on `ker χ_n`.
* `DirichletCharacter.artinRepresentation`: the one-dimensional Artin representation of a
  Dirichlet character.

## Main results

* `Rat.surjective_cyclotomicCharacterMod`: the mod-`n` cyclotomic character is surjective.
* `Representation.dirichletCharacter_apply_cyclotomicCharacterMod` and
  `Representation.apply_eq_dirichletCharacter_smul`: `ρ(σ)` is multiplication by `χ_ρ(χ_n(σ))`.
* `Representation.dirichletCharacter_eq_iff`: `χ_ρ` is the only Dirichlet character with this
  property.
* `DirichletCharacter.isArtin_artinRepresentation` and
  `DirichletCharacter.dirichletCharacter_artinRepresentation`: every Dirichlet character modulo
  `n` is `χ_ρ` for a one-dimensional Artin representation `ρ`.
* `Representation.dirichletCharacter_changeLevel`: changing `n` to a multiple `m` changes the level
  of `χ_ρ` to `m`.
* `Representation.factorsThrough_dirichletCharacter_iff`: `χ_ρ` factors through level `d ∣ n`
  exactly when `ρ` is trivial on `Gal(ℚ̄/ℚ(ζ_d))`, so the conductor of `χ_ρ` is the least such `d`.
-/

open Algebra IntermediateField Module Polynomial Rat

namespace Rat

variable (n : ℕ) [NeZero n] {m : ℕ} [NeZero m] {μ : AlgebraicClosure ℚ}
  {σ : Gal(AlgebraicClosure ℚ/ℚ)}

/-- The **mod-`n` cyclotomic character** `χ_n : Gal(ℚ̄/ℚ) → (ℤ/nℤ)ˣ` of `ℚ`, Mathlib's
`modularCyclotomicCharacter` of `ℚ̄`, by which `Gal(ℚ̄/ℚ)` acts on the `n`-th roots of unity:
`σ(ζ) = ζ ^ χ_n(σ)` for every `n`-th root of unity `ζ` of `ℚ̄`
(`Rat.cyclotomicCharacterMod_apply_of_pow_eq_one`). It is surjective
(`Rat.surjective_cyclotomicCharacterMod`) with kernel `Gal(ℚ̄/ℚ(ζ_n))`, so that it induces the
canonical isomorphism `Gal(ℚ(ζ_n)/ℚ) ≅ (ℤ/nℤ)ˣ`. -/
noncomputable def cyclotomicCharacterMod : Gal(AlgebraicClosure ℚ/ℚ) →* (ZMod n)ˣ :=
  (modularCyclotomicCharacter _ (HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure ℚ)
    n).choose_spec.card_rootsOfUnity).comp (MulSemiringAction.toRingAut _ _)

variable (σ) in
lemma cyclotomicCharacterMod_apply_of_pow_eq_one {ζ : AlgebraicClosure ℚ} (hζ : ζ ^ n = 1) :
    σ ζ = ζ ^ (cyclotomicCharacterMod n σ : ZMod n).val := by
  lift ζ to (AlgebraicClosure ℚ)ˣ using .of_pow_eq_one hζ (NeZero.ne n)
  exact modularCyclotomicCharacter.spec _ _ (MulSemiringAction.toRingAut _ _ σ)
    ((mem_rootsOfUnity' n ζ).mpr hζ)

lemma cyclotomicCharacterMod_eq (hμ : IsPrimitiveRoot μ n) {a : (ZMod n)ˣ}
    (h : σ μ = μ ^ (a : ZMod n).val) : cyclotomicCharacterMod n σ = a := by
  have h' : σ μ = μ ^ (cyclotomicCharacterMod n σ : ZMod n).val :=
    cyclotomicCharacterMod_apply_of_pow_eq_one n σ hμ.pow_eq_one
  rw [h] at h'
  exact Units.ext (ZMod.val_injective n (hμ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h').symm)

lemma mem_ker_cyclotomicCharacterMod_iff (hμ : IsPrimitiveRoot μ n) :
    σ ∈ (cyclotomicCharacterMod n).ker ↔ σ μ = μ := by
  have h : μ ^ ((1 : (ZMod n)ˣ) : ZMod n).val = μ := by
    rw [Units.val_one, ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod 1 hμ.pow_eq_one, pow_one]
  refine ⟨fun hσ ↦ ?_, fun hσ ↦ cyclotomicCharacterMod_eq n hμ (hσ.trans h.symm)⟩
  rw [cyclotomicCharacterMod_apply_of_pow_eq_one n σ hμ.pow_eq_one, MonoidHom.mem_ker.mp hσ, h]

lemma isOpen_ker_cyclotomicCharacterMod :
    IsOpen ((cyclotomicCharacterMod n).ker : Set Gal(AlgebraicClosure ℚ/ℚ)) := by
  rcases HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure ℚ) n with ⟨μ, hμ⟩
  have : FiniteDimensional ℚ ℚ⟮μ⟯ := adjoin.finiteDimensional (IsIntegral.isIntegral μ)
  refine Subgroup.isOpen_mono (fun σ hσ ↦ ?_) ℚ⟮μ⟯.fixingSubgroup_isOpen
  exact (mem_ker_cyclotomicCharacterMod_iff n hμ).mpr
    ((mem_fixingSubgroup_iff _ _).mp hσ μ (mem_adjoin_simple_self ℚ μ))

/-- **The mod-`n` cyclotomic character of `ℚ` is surjective**: since the cyclotomic polynomial `Φ_n`
is irreducible over `ℚ`, every class `a ∈ (ℤ/nℤ)ˣ` is the image of an automorphism of `ℚ(ζ_n)`,
which extends to `ℚ̄`. -/
lemma surjective_cyclotomicCharacterMod : Function.Surjective (cyclotomicCharacterMod n) := by
  intro a
  rcases HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure ℚ) n with ⟨μ, hμ⟩
  have hirr : Irreducible (cyclotomic n ℚ) := cyclotomic.irreducible_rat (NeZero.pos n)
  have : IsCyclotomicExtension {n} ℚ ℚ⟮μ⟯ := hμ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have : IsGalois ℚ ℚ⟮μ⟯ := IsCyclotomicExtension.isGalois {n} ℚ ℚ⟮μ⟯
  let τ : Gal(ℚ⟮μ⟯/ℚ) := (IsCyclotomicExtension.autEquivPow ℚ⟮μ⟯ hirr).symm a
  rcases AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure ℚ) τ with ⟨σ, hσ⟩
  have hμL : IsPrimitiveRoot (AdjoinSimple.gen ℚ μ) n :=
    IsPrimitiveRoot.of_map_of_injective (f := ℚ⟮μ⟯.val) hμ ℚ⟮μ⟯.val.injective
  have hc : hμL.autToPow ℚ τ = a := by
    rw [IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter _ ℚ hμL τ,
      ← IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter _ ℚ
        (IsCyclotomicExtension.zeta_spec n ℚ ℚ⟮μ⟯) τ]
    exact (IsCyclotomicExtension.autEquivPow ℚ⟮μ⟯ hirr).apply_symm_apply a
  have hτ : τ (AdjoinSimple.gen ℚ μ) = AdjoinSimple.gen ℚ μ ^ (a : ZMod n).val := by
    rw [← hc]
    exact (hμL.autToPow_spec ℚ τ).symm
  refine ⟨σ, cyclotomicCharacterMod_eq n hμ ?_⟩
  have hcomm : algebraMap ℚ⟮μ⟯ (AlgebraicClosure ℚ) (τ (AdjoinSimple.gen ℚ μ)) =
      σ (algebraMap ℚ⟮μ⟯ (AlgebraicClosure ℚ) (AdjoinSimple.gen ℚ μ)) :=
    hσ ▸ AlgEquiv.restrictNormal_commutes σ ℚ⟮μ⟯ (AdjoinSimple.gen ℚ μ)
  rw [hτ] at hcomm
  exact hcomm.symm

lemma unitsMap_cyclotomicCharacterMod (h : n ∣ m) :
    ZMod.unitsMap h (cyclotomicCharacterMod m σ) = cyclotomicCharacterMod n σ := by
  rcases HasEnoughRootsOfUnity.exists_isPrimitiveRoot (AlgebraicClosure ℚ) n with ⟨μ, hμ⟩
  refine (cyclotomicCharacterMod_eq n hμ ?_).symm
  rw [ZMod.unitsMap_val, ZMod.cast_eq_val, ZMod.val_natCast, ← pow_eq_pow_mod _ hμ.pow_eq_one]
  exact cyclotomicCharacterMod_apply_of_pow_eq_one m σ <| by
    rcases h with ⟨k, rfl⟩
    rw [pow_mul, hμ.pow_eq_one, one_pow]

lemma ker_cyclotomicCharacterMod_le (h : n ∣ m) :
    (cyclotomicCharacterMod m).ker ≤ (cyclotomicCharacterMod n).ker := fun σ hσ ↦ by
  rw [MonoidHom.mem_ker, ← unitsMap_cyclotomicCharacterMod n h, MonoidHom.mem_ker.mp hσ, map_one]

end Rat

namespace Representation

section Group

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)

/-- The **determinant character** `σ ↦ det ρ(σ)` of a representation `ρ`; on a one-dimensional space
`ρ(σ)` is multiplication by `det ρ(σ)` (`Representation.apply_eq_detCharacter_smul`). -/
noncomputable def detCharacter : G →* ℂˣ :=
  (LinearMap.det.comp ρ).toHomUnits

lemma coe_detCharacter_apply (g : G) : (ρ.detCharacter g : ℂ) = (ρ g).det :=
  rfl

lemma apply_eq_detCharacter_smul (hV : finrank ℂ V = 1) (g : G) (v : V) :
    ρ g v = (ρ.detCharacter g : ℂ) • v := by
  rcases ((ρ g).existsUnique_eq_smul_id_of_finrank_eq_one hV).exists with ⟨c, hc⟩
  rw [coe_detCharacter_apply, hc, LinearMap.det_smul, hV, pow_one, LinearMap.det_id, mul_one]
  rfl

lemma ker_le_ker_detCharacter : ρ.ker ≤ ρ.detCharacter.ker := fun g hg ↦ by
  rw [MonoidHom.mem_ker] at hg ⊢
  exact Units.ext <| by rw [coe_detCharacter_apply, hg, map_one, Units.val_one]

end Group

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ Gal(AlgebraicClosure ℚ/ℚ) V) {n m : ℕ} [NeZero n] [NeZero m]
  (hn : (cyclotomicCharacterMod n).ker ≤ ρ.ker) (σ : Gal(AlgebraicClosure ℚ/ℚ))

/-- The **Dirichlet character** `χ_ρ` modulo `n` of a one-dimensional Artin representation `ρ` of
`Gal(ℚ̄/ℚ)` (LMFDB `artin.dimensionone`) trivial on `Gal(ℚ̄/ℚ(ζ_n))`, the kernel of the mod-`n`
cyclotomic character `χ_n`, that is, whose Artin field lies in `ℚ(ζ_n)`: the character
`σ ↦ det ρ(σ)` factors through the surjection `χ_n : Gal(ℚ̄/ℚ) → (ℤ/nℤ)ˣ`, which induces the
canonical isomorphism `Gal(ℚ(ζ_n)/ℚ) ≅ (ℤ/nℤ)ˣ`, and `χ_ρ` is the resulting homomorphism
`(ℤ/nℤ)ˣ → ℂˣ` extended by `0` to `ℤ/nℤ` (Mathlib's Dirichlet characters are functions on `ℤ/nℤ`).
On a one-dimensional space, `ρ(σ)` is multiplication by `χ_ρ(χ_n(σ))`
(`Representation.apply_eq_dirichletCharacter_smul`).

By the Kronecker–Weber theorem, not available, every one-dimensional Artin representation is
trivial on `Gal(ℚ̄/ℚ(ζ_n))` for some `n`. The LMFDB takes for `n` the conductor of `ρ`; here `n` is
any modulus for which the hypothesis holds, and changing it to a multiple changes the level of `χ_ρ`
(`Representation.dirichletCharacter_changeLevel`). -/
noncomputable def dirichletCharacter : DirichletCharacter ℂ n :=
  MulChar.ofUnitHom <| (cyclotomicCharacterMod n).liftOfSurjective
    (surjective_cyclotomicCharacterMod n) ⟨ρ.detCharacter, hn.trans ρ.ker_le_ker_detCharacter⟩

/-- **The Dirichlet character of `ρ` at `χ_n(σ)` is `det ρ(σ)`.** -/
lemma dirichletCharacter_apply_cyclotomicCharacterMod :
    ρ.dirichletCharacter hn (cyclotomicCharacterMod n σ) = (ρ σ).det := by
  rw [dirichletCharacter, MulChar.ofUnitHom_coe, MonoidHom.liftOfRightInverse_comp_apply]
  rfl

/-- **A one-dimensional representation acts by its Dirichlet character**: `ρ(σ)` is multiplication
by `χ_ρ(χ_n(σ))`. -/
lemma apply_eq_dirichletCharacter_smul (hV : finrank ℂ V = 1) (v : V) :
    ρ σ v = ρ.dirichletCharacter hn (cyclotomicCharacterMod n σ) • v := by
  rw [ρ.apply_eq_detCharacter_smul hV, dirichletCharacter_apply_cyclotomicCharacterMod,
    coe_detCharacter_apply]

/-- **The Dirichlet character of `ρ` is characterised by its values**: it is the only Dirichlet
character `χ` modulo `n` with `χ(χ_n(σ)) = det ρ(σ)` for every `σ`. -/
lemma dirichletCharacter_eq_iff (χ : DirichletCharacter ℂ n) :
    ρ.dirichletCharacter hn = χ ↔ ∀ σ, χ (cyclotomicCharacterMod n σ) = (ρ σ).det := by
  refine ⟨fun h σ ↦ h ▸ ρ.dirichletCharacter_apply_cyclotomicCharacterMod hn σ, fun h ↦ ?_⟩
  refine MulChar.ext fun a ↦ ?_
  rcases surjective_cyclotomicCharacterMod n a with ⟨σ, rfl⟩
  rw [dirichletCharacter_apply_cyclotomicCharacterMod, h]

/-- **The Dirichlet character is compatible with changing the modulus**: for `n ∣ m`, the Dirichlet
character of `ρ` modulo `m` is the one modulo `n` with its level changed to `m`. -/
lemma dirichletCharacter_changeLevel (h : n ∣ m) :
    ρ.dirichletCharacter ((ker_cyclotomicCharacterMod_le n h).trans hn) =
      (ρ.dirichletCharacter hn).changeLevel h := by
  refine (ρ.dirichletCharacter_eq_iff _ _).mpr fun σ ↦ ?_
  rw [DirichletCharacter.changeLevel_def, MulChar.ofUnitHom_coe, MonoidHom.comp_apply,
    unitsMap_cyclotomicCharacterMod n h, MulChar.coe_toUnitHom,
    dirichletCharacter_apply_cyclotomicCharacterMod]

/-- **The Dirichlet character of a one-dimensional `ρ` factors through level `d ∣ n` exactly when
`ρ` is trivial on `Gal(ℚ̄/ℚ(ζ_d))`**: the conductor of `χ_ρ` is the least `d ∣ n` such that the
Artin field of `ρ` lies in `ℚ(ζ_d)`. -/
lemma factorsThrough_dirichletCharacter_iff (hV : finrank ℂ V = 1) {d : ℕ} [NeZero d] (hd : d ∣ n) :
    (ρ.dirichletCharacter hn).FactorsThrough d ↔ (cyclotomicCharacterMod d).ker ≤ ρ.ker := by
  refine ⟨fun ⟨_, χ₀, hχ₀⟩ σ hσ ↦ ?_,
    fun h ↦ ⟨hd, ρ.dirichletCharacter h, ρ.dirichletCharacter_changeLevel h hd⟩⟩
  refine MonoidHom.mem_ker.mpr (LinearMap.ext fun v ↦ ?_)
  rw [ρ.apply_eq_dirichletCharacter_smul hn σ hV, hχ₀, DirichletCharacter.changeLevel_def,
    MulChar.ofUnitHom_coe, MonoidHom.comp_apply, unitsMap_cyclotomicCharacterMod d hd,
    MonoidHom.mem_ker.mp hσ, map_one, Units.val_one, one_smul, End.one_apply]

end Representation

namespace DirichletCharacter

variable {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n)

/-- The **one-dimensional Artin representation** of a Dirichlet character `χ` modulo `n`: `σ` acts
on `ℂ` by multiplication by `χ(χ_n(σ))`, where `χ_n` is the mod-`n` cyclotomic character. Its
Dirichlet character modulo `n` is `χ` (`DirichletCharacter.dirichletCharacter_artinRepresentation`).
-/
noncomputable def artinRepresentation : Representation ℂ Gal(AlgebraicClosure ℚ/ℚ) ℂ :=
  (Algebra.lmul ℂ ℂ).toMonoidHom.comp <|
    (Units.coeHom ℂ).comp (χ.toUnitHom.comp (cyclotomicCharacterMod n))

lemma ker_le_ker_artinRepresentation :
    (cyclotomicCharacterMod n).ker ≤ χ.artinRepresentation.ker := fun σ hσ ↦ by
  rw [MonoidHom.mem_ker] at hσ ⊢
  ext
  simp [artinRepresentation, hσ]

/-- **The representation of a Dirichlet character is an Artin representation**: its kernel contains
the open subgroup `Gal(ℚ̄/ℚ(ζ_n))`. -/
lemma isArtin_artinRepresentation : χ.artinRepresentation.IsArtin :=
  ⟨inferInstance, Subgroup.isOpen_mono χ.ker_le_ker_artinRepresentation
    (isOpen_ker_cyclotomicCharacterMod n)⟩

/-- **Every Dirichlet character is the Dirichlet character of a one-dimensional Artin
representation**: that of `χ.artinRepresentation` is `χ`. -/
lemma dirichletCharacter_artinRepresentation :
    χ.artinRepresentation.dirichletCharacter χ.ker_le_ker_artinRepresentation = χ := by
  refine (χ.artinRepresentation.dirichletCharacter_eq_iff _ χ).mpr fun σ ↦ ?_
  simp [artinRepresentation]

end DirichletCharacter
