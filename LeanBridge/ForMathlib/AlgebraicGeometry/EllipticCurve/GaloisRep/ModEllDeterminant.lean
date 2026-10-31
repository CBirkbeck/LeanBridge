import Mathlib.FieldTheory.Normal.Basic
import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.Bilinear
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.WeilPairing.RootsOfUnity
import TauCeti.LinearAlgebra.Determinant.Basic
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.GaloisRep.ModEllImageExceptional

/-!
# The determinant of the mod-`ℓ` Galois representation

For an elliptic curve `W` over a field `F` and a separably closed extension `K` of `F` in which `ℓ`
is invertible, the determinant of the mod-`ℓ` Galois representation is the mod-`ℓ` cyclotomic
character: an `F`-automorphism `σ` of `K` acts on `E[ℓ]` with determinant `χ_ℓ(σ)`, where
`σ(ζ) = ζ ^ χ_ℓ(σ)` for every `ℓ`-th root of unity `ζ` (Mathlib's
`modularCyclotomicCharacter`). This is the Weil pairing: Tau Ceti's Weil pairing `e_ℓ` on `E[ℓ]`,
on the same `ℓ`-torsion as LeanBridge's mod-`ℓ` representation, is an alternating left-separating
`ZMod ℓ`-bilinear form with values in `μ_ℓ`, and it is Galois-equivariant,
`e_ℓ(σ P, σ Q) = σ(e_ℓ(P, Q)) = χ_ℓ(σ) • e_ℓ(P, Q)`, while an endomorphism of a rank-two module
scales an alternating form by its determinant.

Over `ℚ`, with `K` a separable closure, the cyclotomic character is surjective, every primitive
`ℓ`-th root of unity having the cyclotomic polynomial, irreducible over `ℚ`, as its minimal
polynomial, so that the Galois group permutes them transitively. So the determinant of the mod-`ℓ`
image is surjective, `d = 1` in the label `ℓS.a.b.c[d]` of LMFDB `ec.galois_rep_modell_image`, and
the exceptional types `A4` and `A5` cannot occur, as the knowl states.

## Main results

* `WeierstrassCurve.det_modGaloisRepresentation`: the determinant of the mod-`ℓ` representation is
  the mod-`ℓ` cyclotomic character.
* `WeierstrassCurve.modGaloisImageDetIndex_eq_one` (LMFDB `ec.galois_rep_modell_image`): over `ℚ`,
  the determinant of the mod-`ℓ` image is surjective.
* `WeierstrassCurve.eq_S4_of_hasModGaloisImageExceptionalType_of_rat`
  (LMFDB `ec.galois_rep_modell_image`): over `ℚ`, an exceptional mod-`ℓ` image has type `S4`, not
  `A4` or `A5`.
-/

open Matrix TauCeti Isogeny

open scoped WeierstrassCurve

namespace WeierstrassCurve

section SepClosed

variable {F K : Type*} [Field F] [Field K] [Algebra F K] {ℓ : ℕ} [Fact ℓ.Prime]

lemma restrictRootsOfUnity_eq_pow (hcard : Nat.card (rootsOfUnity ℓ K) = ℓ) (σ : K ≃ₐ[F] K)
    (ζ : rootsOfUnity ℓ K) : restrictRootsOfUnity σ ℓ ζ =
      ζ ^ (modularCyclotomicCharacter K hcard σ.toRingEquiv : ZMod ℓ).val := by
  refine Subtype.ext (Units.ext ?_)
  rw [restrictRootsOfUnity_coe_apply]
  exact modularCyclotomicCharacter.spec K hcard σ.toRingEquiv ζ.2

variable [DecidableEq K] [IsSepClosed K] (W : WeierstrassCurve F) [W.IsElliptic]

/-- **The determinant of the mod-`ℓ` Galois representation is the mod-`ℓ` cyclotomic character**:
for a separably closed extension `K` of `F` in which `ℓ` is invertible, an `F`-automorphism `σ` of
`K` acts on `E[ℓ]` with determinant `χ_ℓ(σ)`, where `σ(ζ) = ζ ^ χ_ℓ(σ)` for the `ℓ`-th roots of
unity `ζ`, by the Galois equivariance of the Weil pairing. -/
lemma det_modGaloisRepresentation (hℓ : (ℓ : K) ≠ 0) (hcard : Nat.card (rootsOfUnity ℓ K) = ℓ)
    (σ : K ≃ₐ[F] K) : LinearMap.det (W.modGaloisRepresentation ℓ σ).val =
      (modularCyclotomicCharacter K hcard σ.toRingEquiv : ZMod ℓ) := by
  rcases (W⁄K).nonempty_basis_torsionBy ℓ hℓ with ⟨b⟩
  refine LinearMap.det_eq_of_compl₁₂_self_eq_smul_of_separatingLeft b
    (isAlt_weilPairingBilin (W⁄K) ℓ hℓ) (separatingLeft_weilPairingBilin (W⁄K) ℓ hℓ) ?_
  refine LinearMap.ext₂ fun S T ↦ ?_
  rw [LinearMap.compl₁₂_apply, LinearMap.smul_apply, LinearMap.smul_apply, weilPairingBilin_apply,
    weilPairingBilin_apply]
  refine (weilPairing_torsionGaloisAction W ℓ hℓ σ S T).trans ?_
  rw [restrictRootsOfUnity_eq_pow hcard σ, ofMul_pow, ofMul_toMul,
    ← Nat.cast_smul_eq_nsmul (ZMod ℓ), ZMod.natCast_zmod_val]

end SepClosed

variable {K : Type*} [Field K] [DecidableEq K] [Algebra ℚ K] [IsSepClosure ℚ K]
  (W : WeierstrassCurve ℚ) [W.IsElliptic] (ℓ : ℕ) [Fact ℓ.Prime]

/-- **Over `ℚ` the determinant of the mod-`ℓ` image is surjective** (LMFDB
`ec.galois_rep_modell_image`): the index `d` of its image in `𝔽_ℓˣ` is `1`, for `K` a separable
closure of `ℚ`. The determinant is the cyclotomic character, and the Galois group of `K` over `ℚ`
sends a primitive `ℓ`-th root of unity `ζ` to every `ζ ^ a` with `a` prime to `ℓ`, these having the
same minimal polynomial, the cyclotomic polynomial. -/
lemma modGaloisImageDetIndex_eq_one : W.modGaloisImageDetIndex K ℓ = 1 := by
  have hK₀ : CharZero K := Algebra.charZero_of_charZero ℚ K
  have hK₁ : ‹Algebra ℚ K› = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  subst hK₁
  have hK : IsSepClosed K := IsSepClosure.sep_closed ℚ
  have hℓ : (ℓ : K) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne ℓ)
  have hpos : 0 < ℓ := NeZero.pos ℓ
  rcases exists_isPrimitiveRoot_weilPairing (W⁄K) ℓ hℓ with ⟨S, T, hζ⟩
  have hcard : Nat.card (rootsOfUnity ℓ K) = ℓ := hζ.card_rootsOfUnity
  rw [modGaloisImageDetIndex, Subgroup.index_eq_one, eq_top_iff]
  rintro u -
  have hu :
      IsPrimitiveRoot ((((weilPairing (W⁄K) ℓ hℓ S T).toMul : Kˣ) : K) ^ (u : ZMod ℓ).val) ℓ :=
    hζ.pow_of_coprime _ (ZMod.val_coe_unit_coprime u)
  rcases (Normal.minpoly_eq_iff_mem_orbit K).mp
    ((Polynomial.cyclotomic_eq_minpoly_rat hu hpos).symm.trans
      (Polynomial.cyclotomic_eq_minpoly_rat hζ hpos)) with ⟨σ, hσ⟩
  have hχ : modularCyclotomicCharacter K hcard σ.toRingEquiv = u := by
    refine Units.ext (ZMod.val_injective ℓ (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) ?_))
    exact (modularCyclotomicCharacter.spec K hcard σ.toRingEquiv
      (weilPairing (W⁄K) ℓ hℓ S T).toMul.2).symm.trans hσ
  exact ⟨W.modGaloisRepresentation ℓ σ, ⟨σ, rfl⟩,
    Units.ext ((W.det_modGaloisRepresentation hℓ hcard σ).trans (congrArg Units.val hχ))⟩

/-- **The exceptional types `A4` and `A5` do not occur over `ℚ`** (LMFDB
`ec.galois_rep_modell_image`): for an elliptic curve over `ℚ` and `K` a separable closure of `ℚ`,
an exceptional mod-`ℓ` image has type `S4`, the determinant of the image being surjective. -/
lemma eq_S4_of_hasModGaloisImageExceptionalType_of_rat {t : GeneralLinearGroup.ExceptionalType}
    (ht : W.HasModGaloisImageExceptionalType K ℓ t) : t = .S4 :=
  W.eq_S4_of_hasModGaloisImageExceptionalType K ℓ (W.modGaloisImageDetIndex_eq_one ℓ) ht

end WeierstrassCurve
