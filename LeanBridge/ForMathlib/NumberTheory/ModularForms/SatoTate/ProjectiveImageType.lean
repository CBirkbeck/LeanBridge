import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.RepresentationTheory.Irreducible
import LeanBridge.ForMathlib.NumberTheory.ModularForms.SatoTate.GaloisRepresentation

/-!
# The type of the projective image of a newform of weight one

The projective image of a newform of weight one (LMFDB `cmf.projective_image`) is a finite subgroup
of `PGL₂(ℂ)`, which the LMFDB classifies into four types: the dihedral groups `D_n`, `n ≥ 2`, of
order `2n`, and `A₄`, `S₄`, `A₅` (`HeckeRing.GL2.Newform.GaloisRep.ProjectiveImageType`). For the
type to be a function of the newform, a finite subgroup of `PGL₂(ℂ)` must have exactly one type.

That it has at most one is proved here: the four kinds of groups are pairwise non-isomorphic, by
their orders and, for a dihedral group of order `12`, `24` or `60`, by its nontrivial centre. The
type is then defined, given that the projective image has one.

That it has one combines the classification of the finite subgroups of `PGL₂(ℂ)` (cyclic,
dihedral, `A₄`, `S₄` or `A₅`), which is not formalised, with the irreducibility of the Galois
representation `ρ`, part of the Deligne–Serre theorem: the projective image of an irreducible
representation is not cyclic, which is proved here, since an eigenvector of a lift of a generator of
a cyclic projective image is an eigenvector of every `ρ(σ)`. The structure
`HeckeRing.GL2.Newform.GaloisRep` does not record irreducibility, which is taken as a hypothesis.

## Main definitions

* `HeckeRing.GL2.Newform.GaloisRep.ProjectiveImageType.order`: the order of the groups of a type.
* `HeckeRing.GL2.Newform.GaloisRep.projectiveImageType`: the type of the projective image
  (LMFDB `cmf.projective_image`), given that it has one.

## Main results

* `HeckeRing.GL2.Newform.GaloisRep.ProjectiveImageType.IsTypeOf.eq`: a finite subgroup of
  `PGL₂(ℂ)` has at most one type.
* `HeckeRing.GL2.Newform.GaloisRep.exists_mulVec_eq_smul_of_isCyclic`: a Galois representation
  with cyclic projective image has a common eigenvector, so it is reducible.
* `HeckeRing.GL2.Newform.GaloisRep.not_isCyclic_projectiveImage`: the projective image of an
  irreducible Galois representation is not cyclic.
* `HeckeRing.GL2.Newform.GaloisRep.exists_isTypeOf_projectiveImage`: the projective image of an
  irreducible Galois representation has a type, given the classification of the finite subgroups
  of `PGL₂(ℂ)`.
-/

open DihedralGroup Equiv Matrix Module

namespace HeckeRing.GL2.Newform.GaloisRep

variable {N : ℕ} [NeZero N] {f : Newform N 1} (ρ : GaloisRep f)
  {H : Subgroup (GL (Fin 2) ℂ ⧸ Subgroup.center (GL (Fin 2) ℂ))} {t t' : ProjectiveImageType}
  {n : ℕ}

namespace ProjectiveImageType

/-- The **order** of the groups of a type: `2n` for the dihedral group `D_n`, and `12`, `24` and
`60` for `A₄`, `S₄` and `A₅`. -/
def order : ProjectiveImageType → ℕ
  | dihedral n => 2 * n
  | tetrahedral => 12
  | octahedral => 24
  | icosahedral => 60

lemma IsTypeOf.natCard_eq (ht : t.IsTypeOf H) : Nat.card H = t.order := by
  cases t with
  | dihedral n => exact (Nat.card_congr ht.2.some.toEquiv).trans DihedralGroup.nat_card
  | tetrahedral =>
    rw [Nat.card_congr ht.some.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl
  | octahedral =>
    rw [Nat.card_congr ht.some.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  | icosahedral =>
    rw [Nat.card_congr ht.some.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    rfl

lemma IsTypeOf.natCard_center_eq_one (ht : t.IsTypeOf H) (hn : ∀ n, t ≠ dihedral n) :
    Nat.card (Subgroup.center H) = 1 := by
  cases t with
  | dihedral n => exact (hn n rfl).elim
  | tetrahedral =>
    rw [Nat.card_congr (Subgroup.centerCongr ht.some).toEquiv, alternatingGroup.center_eq_bot
      (by simp), Subgroup.card_bot]
  | octahedral =>
    have h : ∀ z : Perm (Fin 4), (∀ g : Perm (Fin 4), g * z = z * g) → z = 1 := by
      decide
    rw [Nat.card_congr (Subgroup.centerCongr ht.some).toEquiv, (Subgroup.eq_bot_iff_forall _).mpr
      fun z hz ↦ h z (Subgroup.mem_center_iff.mp hz), Subgroup.card_bot]
  | icosahedral =>
    rw [Nat.card_congr (Subgroup.centerCongr ht.some).toEquiv, alternatingGroup.center_eq_bot
      (by simp), Subgroup.card_bot]

lemma IsTypeOf.natCard_center_ne_one (ht : (dihedral n).IsTypeOf H) (hn : Even n) (hn2 : n ≠ 2) :
    Nat.card (Subgroup.center H) ≠ 1 := by
  rw [Nat.card_congr (Subgroup.centerCongr ht.2.some).toEquiv,
    DihedralGroup.center_eq_closure_of_even_ne_two hn hn2, Ne, Subgroup.card_eq_one,
    Subgroup.zpowers_eq_bot, DihedralGroup.one_def, r.injEq, ZMod.natCast_eq_zero_iff]
  have h2 : 2 ≤ n := ht.1
  exact fun h ↦ absurd (Nat.le_of_dvd (by omega) h) (by omega)

/-- **The type of a finite subgroup of `PGL₂(ℂ)` is unique**: the groups `D_n` for `n ≥ 2`, `A₄`,
`S₄` and `A₅` are pairwise non-isomorphic. Their orders are `2n`, `12`, `24` and `60`, and a
dihedral group of order `12`, `24` or `60` has a nontrivial centre, unlike `A₄`, `S₄` and `A₅`. -/
lemma IsTypeOf.eq (ht : t.IsTypeOf H) (ht' : t'.IsTypeOf H) : t = t' := by
  have h : t.order = t'.order := ht.natCard_eq.symm.trans ht'.natCard_eq
  cases t <;> cases t' <;> simp only [order] at h ⊢ <;> first
    | exact congrArg dihedral (by omega)
    | omega
    | exact absurd (ht'.natCard_center_eq_one (by simp))
        (ht.natCard_center_ne_one (Nat.even_iff.mpr (by omega)) (by omega))
    | exact absurd (ht.natCard_center_eq_one (by simp))
        (ht'.natCard_center_ne_one (Nat.even_iff.mpr (by omega)) (by omega))

end ProjectiveImageType

/-- The **type** of the projective image of a weight-one newform (LMFDB `cmf.projective_image`),
given that it has one: the type `t`, unique by `ProjectiveImageType.IsTypeOf.eq`, such that the
projective image is isomorphic to `D_n` (`n ≥ 2`), `A₄`, `S₄` or `A₅` as `t` says. That the
projective image has a type is the classification of the finite subgroups of `PGL₂(ℂ)` together
with the irreducibility of `ρ`, which are not proved here and enter as the hypothesis `h`. -/
noncomputable def projectiveImageType
    (h : ∃ t : ProjectiveImageType, t.IsTypeOf ρ.projectiveImage) : ProjectiveImageType :=
  h.choose

lemma isTypeOf_projectiveImageType (h : ∃ t : ProjectiveImageType, t.IsTypeOf ρ.projectiveImage) :
    (ρ.projectiveImageType h).IsTypeOf ρ.projectiveImage :=
  h.choose_spec

lemma projectiveImageType_eq (h : ∃ t : ProjectiveImageType, t.IsTypeOf ρ.projectiveImage)
    (ht : t.IsTypeOf ρ.projectiveImage) : ρ.projectiveImageType h = t :=
  (ρ.isTypeOf_projectiveImageType h).eq ht

/-- **A Galois representation with cyclic projective image is reducible**: an eigenvector `v` of a
lift `A ∈ GL₂(ℂ)` of a generator of the projective image is an eigenvector of every `ρ(σ)`, which
is a scalar multiple of a power of `A`. -/
lemma exists_mulVec_eq_smul_of_isCyclic [IsCyclic ρ.projectiveImage] :
    ∃ v : Fin 2 → ℂ, v ≠ 0 ∧ ∀ σ : Gal(AlgebraicClosure ℚ/ℚ), ∃ c : ℂ,
      (ρ.toMonoidHom σ : Matrix (Fin 2) (Fin 2) ℂ) *ᵥ v = c • v := by
  rcases IsCyclic.exists_generator (α := ρ.projectiveImage) with ⟨x, hx⟩
  rcases QuotientGroup.mk_surjective (x : GL (Fin 2) ℂ ⧸ Subgroup.center (GL (Fin 2) ℂ)) with
    ⟨A, hA⟩
  rcases End.exists_eigenvalue (toLin' (A : Matrix (Fin 2) (Fin 2) ℂ)) with ⟨μ, hμ⟩
  rcases hμ.exists_hasEigenvector with ⟨v, hv⟩
  refine ⟨v, hv.2, fun σ ↦ ?_⟩
  rcases mem_powers_iff_mem_zpowers.mpr (hx ⟨ρ.projective σ, σ, rfl⟩) with ⟨m, hm⟩
  have h : (QuotientGroup.mk (A ^ m) : GL (Fin 2) ℂ ⧸ Subgroup.center (GL (Fin 2) ℂ)) =
      QuotientGroup.mk (ρ.toMonoidHom σ) := by
    rw [QuotientGroup.mk_pow, hA]
    exact congrArg Subtype.val hm
  rcases GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp (QuotientGroup.eq.mp h) with
    ⟨c, hc⟩
  have hρ :
      (ρ.toMonoidHom σ : Matrix (Fin 2) (Fin 2) ℂ) = c • (A : Matrix (Fin 2) (Fin 2) ℂ) ^ m := by
    rw [← mul_inv_cancel_left (A ^ m) (ρ.toMonoidHom σ), Units.val_mul, ← hc, scalar_apply,
      ← smul_one_eq_diagonal, Matrix.mul_smul, mul_one, Units.val_pow_eq_pow_val]
  refine ⟨c * μ ^ m, ?_⟩
  rw [hρ, smul_mulVec, ← toLin'_apply, toLin'_pow, hv.pow_apply, smul_smul]

/-- **The projective image of an irreducible Galois representation is not cyclic**: otherwise the
line spanned by a common eigenvector of the `ρ(σ)` would be a proper nonzero subrepresentation. The
Galois representation of a newform of weight one is irreducible, by the Deligne–Serre theorem. -/
lemma not_isCyclic_projectiveImage [Representation.IsIrreducible ρ.toRepresentation] :
    ¬IsCyclic ρ.projectiveImage := by
  intro hcyc
  rcases ρ.exists_mulVec_eq_smul_of_isCyclic with ⟨v, hv, hσ⟩
  have hW : ∀ (σ : Gal(AlgebraicClosure ℚ/ℚ)) ⦃w : Fin 2 → ℂ⦄, w ∈ ℂ ∙ v →
      ρ.toRepresentation σ w ∈ ℂ ∙ v := by
    intro σ w hw
    rcases Submodule.mem_span_singleton.mp hw with ⟨a, rfl⟩
    rcases hσ σ with ⟨c, hc⟩
    exact Submodule.mem_span_singleton.mpr ⟨a * c, by
      rw [map_smul]
      exact ((congrArg (a • ·) hc).trans (smul_smul a c v)).symm⟩
  rcases IsSimpleOrder.eq_bot_or_eq_top (⟨ℂ ∙ v, hW⟩ : Subrepresentation ρ.toRepresentation) with
    h | h
  · have h' : ℂ ∙ v = ⊥ := congrArg Subrepresentation.toSubmodule h
    exact hv <| (Submodule.mem_bot ℂ).mp <| h' ▸ Submodule.mem_span_singleton_self v
  · have h' : ℂ ∙ v = ⊤ := congrArg Subrepresentation.toSubmodule h
    have h₁ : Module.finrank ℂ (ℂ ∙ v) = 1 := finrank_span_singleton hv
    rw [h', finrank_top, Module.finrank_fin_fun] at h₁
    exact absurd h₁ (by decide)

/-- **The projective image of an irreducible Galois representation has a type**, given the
classification of the finite subgroups of `PGL₂(ℂ)`: here the hypothesis `hcl` that every finite
subgroup of `PGL₂(ℂ)` is cyclic or of one of the four types, which is not proved here. The
projective image is finite, and it is not cyclic (`not_isCyclic_projectiveImage`). -/
lemma exists_isTypeOf_projectiveImage [Representation.IsIrreducible ρ.toRepresentation]
    (hcl : ∀ H : Subgroup (GL (Fin 2) ℂ ⧸ Subgroup.center (GL (Fin 2) ℂ)), Finite H →
      IsCyclic H ∨ ∃ t : ProjectiveImageType, t.IsTypeOf H) :
    ∃ t : ProjectiveImageType, t.IsTypeOf ρ.projectiveImage :=
  (hcl _ inferInstance).resolve_left ρ.not_isCyclic_projectiveImage

end HeckeRing.GL2.Newform.GaloisRep
