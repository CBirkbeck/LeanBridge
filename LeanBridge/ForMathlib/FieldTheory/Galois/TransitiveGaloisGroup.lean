import LeanBridge.ForMathlib.FieldTheory.Galois.StemFieldAutomorphisms
import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# Every transitive permutation group is the Galois group of a polynomial

The Galois group of an irreducible separable polynomial of degree `n` acts faithfully and
transitively on its roots (LMFDB `gg.galois_group`; Mathlib's `Polynomial.Gal.galActionHom`,
`Polynomial.Gal.galActionHom_injective`, `Polynomial.Gal.galAction_isPretransitive`), and
conversely every transitive subgroup `G` of `S_n` arises so. Let `G` act on the field
`L = ℚ(x_i : i ∈ X)` of rational functions by permuting the variables and let `K = L^G` be the
fixed field, so that `L / K` is Galois with group `G` (Artin's theorem). The minimal polynomial
`f` of `x_{i₀}` over `K` is irreducible and separable, and its roots in `L` are the conjugates
`g x_{i₀} = x_{g i₀}`, that is, all the `x_i`, `G` being transitive. Labelling the root `x_i` by
`i`, the Galois group of `f`, acting on its roots, becomes `G`: an automorphism of `L / K` comes
from some `g ∈ G` and maps `x_i` to `x_{g i}`. Its action on the roots in the splitting field of
`f` is the same, through the Galois-equivariant bijection between the two sets of roots.

## Main results

* `Subgroup.exists_galActionHom_range_eq` (LMFDB `gg.galois_group`): a transitive group `G` of
  permutations of a finite nonempty set `X` is the Galois group of an irreducible separable
  polynomial of degree `|X|`, acting on its roots, labelled by `X`.
* `Subgroup.exists_galActionHom_range_eq_fin` (LMFDB `gg.galois_group`): the same for a
  transitive subgroup of `S_n`, `n ≥ 1`.
-/

universe u

open Polynomial

namespace Subgroup

/-- **Every transitive group of permutations of a finite nonempty set `X` is the Galois group of a
polynomial** (LMFDB `gg.galois_group`): there are a field `K` and an irreducible separable
polynomial `f` over `K` of degree `|X|` whose roots, in its splitting field, can be labelled by `X`
so that the Galois group of `f`, acting on them, becomes `G`. Here `K` is the fixed field of `G`
acting on `ℚ(x_i : i ∈ X)` by permuting the variables, and `f` is the minimal polynomial of a
variable `x_{i₀}`, whose roots are the variables. -/
lemma exists_galActionHom_range_eq {ι : Type u} [Finite ι] [Nonempty ι]
    (G : Subgroup (Equiv.Perm ι)) [MulAction.IsPretransitive G ι] : ∃ (K : Type u) (_ : Field K)
    (f : K[X]), Irreducible f ∧ f.Separable ∧ f.natDegree = Nat.card ι ∧
    haveI : Fact ((f.map (algebraMap K f.SplittingField)).Splits) := ⟨SplittingField.splits f⟩
    ∃ e : f.rootSet f.SplittingField ≃ ι,
    (Gal.galActionHom f f.SplittingField).range.map e.permCongrHom.toMonoidHom = G := by
  let ρ₀ : Equiv.Perm ι →* MvPolynomial ι ℚ ≃ₐ[ℚ] MvPolynomial ι ℚ :=
    { toFun := MvPolynomial.renameEquiv ℚ
      map_one' := MvPolynomial.renameEquiv_refl ℚ
      map_mul' := fun σ τ ↦ (MvPolynomial.renameEquiv_trans ℚ τ σ).symm }
  let _ : MulSemiringAction G (MvPolynomial ι ℚ) := MulSemiringAction.compHom _ (ρ₀.comp G.subtype)
  have hsmul (g : G) (p : MvPolynomial ι ℚ) : g • p = MvPolynomial.rename (g : Equiv.Perm ι) p :=
    rfl
  have _ : FaithfulSMul G (MvPolynomial ι ℚ) := ⟨fun h ↦ Subtype.ext <| Equiv.ext fun i ↦ by
    simpa [hsmul] using h (MvPolynomial.X i)⟩
  let L : Type u := FractionRing (MvPolynomial ι ℚ)
  let _ : MulSemiringAction G L := IsFractionRing.mulSemiringAction G (MvPolynomial ι ℚ) L
  have _ : FaithfulSMul G L := IsFractionRing.faithfulSMul G (MvPolynomial ι ℚ) L
  let K : Subfield L := FixedPoints.subfield G L
  let x : ι → L := fun i ↦ algebraMap (MvPolynomial ι ℚ) L (MvPolynomial.X i)
  have hx : Function.Injective x :=
    (IsFractionRing.injective (MvPolynomial ι ℚ) L).comp MvPolynomial.X_injective
  have hgx (g : G) (i : ι) : g • x i = x (g • i) := by
    rw [← algebraMap.coe_smul', hsmul, MvPolynomial.rename_X]
    rfl
  have hσ (σ : L ≃ₐ[K] L) : ∃ g : G, ∀ z, σ z = g • z := by
    rcases FixedPoints.toAlgAut_surjective G L σ with ⟨g, rfl⟩
    exact ⟨g, fun z ↦ MulSemiringAction.toAlgEquiv_apply _ _ g z⟩
  let i₀ : ι := Classical.arbitrary ι
  have hint : IsIntegral K (x i₀) := .of_finite K (x i₀)
  let f : K[X] := minpoly K (x i₀)
  have hroots (z : L) : z ∈ f.rootSet L ↔ z ∈ Set.range x := by
    rw [mem_rootSet]
    constructor
    · rintro ⟨-, hz⟩
      rcases (Normal.minpoly_eq_iff_mem_orbit L).mp (minpoly.eq_of_irreducible_of_monic
        (minpoly.irreducible hint) hz (minpoly.monic hint)).symm with ⟨σ, hσz⟩
      rcases hσ σ with ⟨g, hg⟩
      exact ⟨g • i₀, by rw [← hgx, ← hg]; exact hσz⟩
    · rintro ⟨i, rfl⟩
      rcases MulAction.exists_smul_eq G i₀ i with ⟨g, rfl⟩
      refine ⟨minpoly.ne_zero hint, ?_⟩
      have h : aeval ((MulSemiringAction.toAlgAut G K L g : L →ₐ[K] L) (x i₀)) f = 0 :=
        minpoly.aeval_algHom K _ (x i₀)
      simpa [hgx] using h
  have hsplit : (f.map (algebraMap K L)).Splits := Normal.splits inferInstance (x i₀)
  have _ : Fact ((f.map (algebraMap K L)).Splits) := ⟨hsplit⟩
  let eL : f.rootSet L ≃ ι :=
    (Equiv.subtypeEquivRight hroots).trans (Equiv.ofInjective x hx).symm
  have heL (i : ι) : (eL.symm i : L) = x i :=
    rfl
  have hgal (g : G) : eL.permCongr (Gal.galActionHom f L (Gal.restrict f L
      (MulSemiringAction.toAlgAut G K L g))) = (g : Equiv.Perm ι) := by
    refine Equiv.ext fun i ↦ eL.eq_symm_apply.mp <| Subtype.ext ?_
    rw [Equiv.trans_apply, Gal.galActionHom_restrict, heL, heL, MulSemiringAction.toAlgAut_apply,
      MulSemiringAction.toAlgEquiv_apply, hgx]
    rfl
  have hrange : (Gal.galActionHom f L).range.map eL.permCongrHom.toMonoidHom = G := by
    ext π
    rw [MonoidHom.map_range, MonoidHom.mem_range]
    refine ⟨?_, fun hπ ↦ ⟨_, hgal ⟨π, hπ⟩⟩⟩
    rintro ⟨τ, rfl⟩
    rcases Gal.restrict_surjective f L τ with ⟨σ, rfl⟩
    rcases FixedPoints.toAlgAut_surjective G L σ with ⟨g, rfl⟩
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Equiv.permCongrHom_coe, hgal]
    exact g.2
  have hsep : f.Separable := (minpoly.irreducible hint).separable
  have _ : Fact ((f.map (algebraMap K f.SplittingField)).Splits) := ⟨SplittingField.splits f⟩
  refine ⟨K, inferInstance, f, minpoly.irreducible hint, hsep, ?_,
    (Gal.rootsEquivRoots f f.SplittingField L).trans eL, ?_⟩
  · rw [← card_rootSet_eq_natDegree hsep hsplit, ← Nat.card_eq_fintype_card, Nat.card_congr eL]
  · refine Eq.trans ?_ hrange
    rw [MonoidHom.map_range, MonoidHom.map_range]
    refine congrArg MonoidHom.range (MonoidHom.ext fun τ ↦ Equiv.ext fun i ↦ ?_)
    exact congrArg eL <| (Gal.smul_rootsEquivRoots f f.SplittingField L τ _).symm.trans <|
      congrArg (τ • ·) (Equiv.apply_symm_apply _ _)

/-- **Every transitive subgroup `G` of `S_n`, `n ≥ 1`, is the Galois group of a polynomial**
(LMFDB `gg.galois_group`): there are a field `K` and an irreducible separable polynomial `f` of
degree `n` over `K` whose roots, in its splitting field, can be labelled by `{1, …, n}` so that the
Galois group of `f`, acting on them, becomes `G`. -/
lemma exists_galActionHom_range_eq_fin {n : ℕ} [NeZero n] (G : Subgroup (Equiv.Perm (Fin n)))
    [MulAction.IsPretransitive G (Fin n)] : ∃ (K : Type) (_ : Field K) (f : K[X]), Irreducible f ∧
    f.Separable ∧ f.natDegree = n ∧
    haveI : Fact ((f.map (algebraMap K f.SplittingField)).Splits) := ⟨SplittingField.splits f⟩
    ∃ e : f.rootSet f.SplittingField ≃ Fin n,
    (Gal.galActionHom f f.SplittingField).range.map e.permCongrHom.toMonoidHom = G := by
  simpa using G.exists_galActionHom_range_eq

end Subgroup
