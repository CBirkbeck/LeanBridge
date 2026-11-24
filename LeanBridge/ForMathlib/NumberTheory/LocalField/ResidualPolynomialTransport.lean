import LeanBridge.ForMathlib.NumberTheory.LocalField.GaloisClosureRamification
import LeanBridge.ForMathlib.NumberTheory.LocalField.ResidualPolynomialInvariance
import TauCeti.NumberTheory.LocalField.Unramified.Factorization

/-!
# Residual polynomials along isomorphisms of extensions

Let `L / K` be a finite extension of nonarchimedean local fields, `L^un` its maximal unramified
subextension, `α` a uniformiser of `L` and `ρ` the ramification polynomial of the minimal polynomial
of `α` over `L^un`. The list of residual polynomials of `L` at `α` (LMFDB
`lf.residual_polynomials`) lies over the residue field `L̲`, and its equivalence class is the orbit
of the list under the residue units, acting by `A_i ↦ γ_{δ,i} A_i(δ ^ h_i x)`.

This file proves that these objects are transported by a `K`-isomorphism `σ : L ≃ L'` of extensions
of `K`: `σ` preserves the normalised valuations, maps `L^un` onto `L'^un`, the minimal polynomial of
`α` over `L^un` to that of `σ α` over `L'^un`, the ramification polynomial and the ramification
polygon along, and the list of residual polynomials and its class by the isomorphism `σ̲ : L̲ ≃ L̲'`
of residue fields that `σ` induces.

It also proves the algebra of the action of the residue units on lists of pairs `(h_i, A_i)`: the
action composes (`δ'` then `δ` is `δ δ'`), so the classes are the orbits of a group action and two
classes are equal or disjoint; it commutes with every homomorphism of fields applied to the
coefficients, so the image of a class under an isomorphism of residue fields, such as a power of
Frobenius, is again a class. Finally, two polynomials with the same ramification polygon, over two
different fields, have the same segments and slopes, so their lists of pairs carry the same `h_i`.

## Main definitions

* `IsNonarchimedeanLocalField.residualActOrbit`: the orbit of a list of pairs `(h_i, A_i)` under the
  action of the units of the field of coefficients.

## Main results

* `IsNonarchimedeanLocalField.residualAct_residualAct`: the action of `δ` after that of `δ'` is the
  action of `δ δ'`.
* `IsNonarchimedeanLocalField.residualActOrbit_eq_of_mem`: two orbits that meet are equal.
* `IsNonarchimedeanLocalField.map_residualAct` and
  `IsNonarchimedeanLocalField.image_map_residualActOrbit`: the action commutes with the
  homomorphisms of fields applied to the coefficients, and an isomorphism maps orbits to orbits.
* `IsNonarchimedeanLocalField.residualPolynomialClass_eq_residualActOrbit` (LMFDB
  `lf.residual_polynomials`): for a totally ramified extension the class of residual polynomials is
  the orbit of the list under all the units of the residue field.
* `IsNonarchimedeanLocalField.coeffEnvelope_eq_of_ramificationPolygonOf_eq`: two polynomials with
  the same ramification polygon have the same Newton polygon.
* `IsNonarchimedeanLocalField.addValuation_algEquiv`: a `K`-isomorphism of extensions of `K`
  preserves the normalised valuations.
* `IsNonarchimedeanLocalField.map_unramifiedExtension_algEquiv`: it maps the unramified extension of
  degree `f` inside `L` onto the one inside `L'`.
* `IsNonarchimedeanLocalField.ramificationPolynomial_minpoly_algEquiv` and
  `IsNonarchimedeanLocalField.ramificationPolygonOf_minpoly_algEquiv` (LMFDB
  `lf.ramification_polygon`): it maps the ramification polynomial of `L / L^un` at `α` to that of
  `L' / L'^un` at `σ α`, with the same ramification polygon.
* `IsNonarchimedeanLocalField.residualPolynomials_minpoly_algEquiv` and
  `IsNonarchimedeanLocalField.residualPolynomialClass_minpoly_algEquiv` (LMFDB
  `lf.residual_polynomials`): the list of residual polynomials of `L' / L'^un` at `σ α` and its
  class are the images of those of `L / L^un` at `α` under `σ̲`.

## References

* S. Pauli and B. Sinclair, *Enumerating extensions of (π)-adic fields with given invariants*,
  Int. J. Number Theory 13 (2017); arXiv:1504.06671, Section 4.
-/

open IsLocalRing Polynomial TauCeti ValuativeRel

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

namespace Polynomial

variable {F : Type*} [Field F] {A : F[X]} {γ c : F}

lemma natDegree_C_mul_comp_C_mul_X (hγ : γ ≠ 0) (hc : c ≠ 0) :
    (C γ * A.comp (C c * X)).natDegree = A.natDegree := by
  rw [natDegree_C_mul hγ, natDegree_comp, natDegree_C_mul_X c hc, mul_one]

variable (A) in
lemma C_mul_comp_C_mul_X_comp (a b u v : F) :
    C a * (C b * A.comp (C u * X)).comp (C v * X) = C (a * b) * A.comp (C (u * v) * X) := by
  rw [mul_comp, C_comp, comp_assoc, mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul,
    ← mul_assoc (C u), ← C_mul]

end Polynomial

namespace IsNonarchimedeanLocalField

section Action

variable {F F' : Type*} [Field F] [Field F'] {δ δ' : F} {P Q : List (ℤ × F[X])} {B : List F[X]}

variable (δ) in
lemma residualAct_nil : residualAct δ ([] : List (ℤ × F[X])) = [] :=
  List.zipWith_nil_right

variable (δ P) in
lemma residualAct_cons (hA : ℤ × F[X]) : residualAct δ (hA :: P) =
    (C ((residualGammas δ P).headD 1 * δ ^ (-(hA.1 * hA.2.natDegree))) *
      hA.2.comp (C (δ ^ hA.1) * X)) :: residualAct δ P :=
  rfl

variable (δ δ' P) in
lemma headD_residualGammas_mul : (residualGammas (δ * δ') P).headD 1 =
    (residualGammas δ P).headD 1 * (residualGammas δ' P).headD 1 := by
  induction P with
  | nil => rw [residualGammas, residualGammas, residualGammas, List.headD_nil, mul_one]
  | cons hA t ih =>
    rw [residualGammas, residualGammas, residualGammas, List.headD_cons, List.headD_cons,
      List.headD_cons, ih, mul_zpow, mul_mul_mul_comm]

variable (δ δ' P) in
lemma residualGammas_mul : residualGammas (δ * δ') P =
    List.zipWith (· * ·) (residualGammas δ P) (residualGammas δ' P) := by
  induction P with
  | nil => rfl
  | cons hA t ih =>
    rw [residualGammas, residualGammas, residualGammas, List.zipWith_cons_cons, ← ih,
      headD_residualGammas_mul, mul_zpow, mul_mul_mul_comm]

lemma residualGammas_eq_of_map_eq
    (h : P.map (fun x ↦ x.1 * (x.2.natDegree : ℤ)) = Q.map fun x ↦ x.1 * (x.2.natDegree : ℤ)) :
    residualGammas δ P = residualGammas δ Q := by
  induction P generalizing Q with
  | nil =>
    rcases Q with _ | ⟨hB, Q⟩
    · rfl
    · cases h
  | cons hA t ih =>
    rcases Q with _ | ⟨hB, Q⟩
    · cases h
    · rw [List.map_cons, List.map_cons, List.cons_eq_cons] at h
      rw [residualGammas, residualGammas, ih h.2, h.1]

lemma headD_residualGammas_ne_zero (hδ : δ ≠ 0) : (residualGammas δ P).headD 1 ≠ 0 := by
  induction P with
  | nil => exact one_ne_zero
  | cons hA t ih => exact mul_ne_zero ih (zpow_ne_zero _ hδ)

lemma natDegree_residualAct_head (hδ : δ ≠ 0) (hA : ℤ × F[X]) :
    (C ((residualGammas δ P).headD 1 * δ ^ (-(hA.1 * hA.2.natDegree))) *
      hA.2.comp (C (δ ^ hA.1) * X)).natDegree = hA.2.natDegree :=
  natDegree_C_mul_comp_C_mul_X (headD_residualGammas_ne_zero hδ (P := hA :: P)) (zpow_ne_zero _ hδ)

lemma residualGammas_zip_residualAct (hδ' : δ' ≠ 0) :
    residualGammas δ ((P.map Prod.fst).zip (residualAct δ' P)) = residualGammas δ P := by
  refine residualGammas_eq_of_map_eq ?_
  induction P with
  | nil => rfl
  | cons hA t ih =>
    rw [List.map_cons, residualAct_cons, List.zip_cons_cons, List.map_cons, List.map_cons,
      natDegree_residualAct_head hδ', ih]

variable (P) in
/-- **The action of the residue units composes** (LMFDB `lf.residual_polynomials`): for `δ'`
nonzero, acting by `δ` on the pairs `(h_i, B_i)` with `B_i = γ_{δ',i} A_i(δ' ^ h_i x)`, the image of
the pairs `(h_i, A_i)` under `δ'`, gives the image of the pairs `(h_i, A_i)` under `δ δ'`. The
degrees of the `B_i` are those of the `A_i`, so the constants `γ` multiply. -/
lemma residualAct_residualAct (hδ' : δ' ≠ 0) :
    residualAct δ ((P.map Prod.fst).zip (residualAct δ' P)) = residualAct (δ * δ') P := by
  induction P with
  | nil => rw [List.map_nil, List.zip_nil_left, residualAct_nil, residualAct_nil]
  | cons hA t ih =>
    rw [List.map_cons, residualAct_cons, List.zip_cons_cons, residualAct_cons, residualAct_cons,
      ih, residualGammas_zip_residualAct hδ']
    dsimp only
    rw [natDegree_residualAct_head hδ', C_mul_comp_C_mul_X_comp, headD_residualGammas_mul]
    conv_lhs => rw [mul_mul_mul_comm, ← mul_zpow, ← mul_zpow, mul_comm δ' δ]

variable (P) in
lemma headD_residualGammas_one : (residualGammas 1 P).headD 1 = 1 := by
  induction P with
  | nil => rfl
  | cons hA t ih => rw [residualGammas, List.headD_cons, ih, one_zpow, mul_one]

variable (P) in
lemma residualAct_one : residualAct 1 P = P.map Prod.snd := by
  induction P with
  | nil => rfl
  | cons hA t ih =>
    rw [residualAct_cons, ih, headD_residualGammas_one, one_zpow, one_zpow, mul_one, C_1, one_mul,
      one_mul, comp_X, List.map_cons]

variable (f : F →+* F')

variable (δ P) in
lemma map_residualGammas :
    (residualGammas δ P).map f = residualGammas (f δ) (P.map (Prod.map id (map f))) := by
  induction P with
  | nil => rfl
  | cons hA t ih =>
    have hhead : f ((residualGammas δ t).headD 1) =
        (residualGammas (f δ) (t.map (Prod.map id (map f)))).headD 1 := by
      rw [← ih, ← map_one f, List.headD_map]
    rw [residualGammas, List.map_cons, List.map_cons, residualGammas, ih, map_mul, map_zpow₀,
      hhead, Prod.map_fst, Prod.map_snd, id_eq, natDegree_map]

variable (δ P) in
/-- **The action of the residue units commutes with homomorphisms of fields** (LMFDB
`lf.residual_polynomials`): for a homomorphism of fields `f : F → F'`, applying `f` to the
coefficients of `(γ_{δ,1} A_1(δ ^ h_1 x), …, γ_{δ,ℓ} A_ℓ(δ ^ h_ℓ x))` gives the image of the pairs
`(h_i, f(A_i))` under `f(δ)`. -/
lemma map_residualAct :
    (residualAct δ P).map (map f) = residualAct (f δ) (P.map (Prod.map id (map f))) := by
  rw [residualAct, residualAct, List.map_zipWith, ← map_residualGammas, List.zipWith_map]
  congr 1
  funext γ hA
  rw [Polynomial.map_mul, map_C, map_comp, Polynomial.map_mul, map_C, map_X, map_zpow₀]
  rfl

variable (F P) in
/-- The **orbit of a list of pairs** `(h_i, A_i)` of integers and polynomials over a field `F`
under the action of the units of `F` (LMFDB `lf.residual_polynomials`): the set of the lists
`(γ_{δ,1} A_1(δ ^ h_1 x), …, γ_{δ,ℓ} A_ℓ(δ ^ h_ℓ x))` for `δ ∈ F ^ ×`, with
`γ_{δ,ℓ} = δ ^ (-h_ℓ deg A_ℓ)` and `γ_{δ,i} = γ_{δ,i+1} δ ^ (-h_i deg A_i)`. For the list of
residual polynomials of a totally ramified extension, with the numerators of the slopes, it is the
equivalence class of residual polynomials
(`IsNonarchimedeanLocalField.residualPolynomialClass_eq_residualActOrbit`). -/
noncomputable def residualActOrbit : Set (List F[X]) :=
  Set.range fun δ : Fˣ ↦ residualAct (δ : F) P

variable (P) in
lemma map_snd_mem_residualActOrbit : P.map Prod.snd ∈ residualActOrbit F P :=
  ⟨1, residualAct_one P⟩

/-- **Two orbits that meet are equal** (LMFDB `lf.residual_polynomials`): if a list `B` lies in the
orbit of the pairs `(h_i, A_i)`, the orbit of the pairs `(h_i, B_i)` is the orbit of the pairs
`(h_i, A_i)`, since the action composes. So the equivalence classes of residual polynomials with
given `h_i` are equal or disjoint. -/
lemma residualActOrbit_eq_of_mem (hB : B ∈ residualActOrbit F P) :
    residualActOrbit F ((P.map Prod.fst).zip B) = residualActOrbit F P := by
  rcases hB with ⟨δ₀, rfl⟩
  refine Set.ext fun A ↦ ⟨?_, ?_⟩
  · rintro ⟨δ, rfl⟩
    exact ⟨δ * δ₀, (residualAct_residualAct P δ₀.ne_zero).symm⟩
  · rintro ⟨δ, rfl⟩
    refine ⟨δ * δ₀⁻¹, ?_⟩
    dsimp only
    rw [residualAct_residualAct P δ₀.ne_zero, ← Units.val_mul, inv_mul_cancel_right]

variable (P) in
/-- **An isomorphism of fields maps orbits to orbits** (LMFDB `lf.residual_polynomials`): for a
surjective homomorphism of fields `f : F → F'`, applying `f` to the coefficients maps the orbit of
the pairs `(h_i, A_i)` onto the orbit of the pairs `(h_i, f(A_i))`. So the image of an equivalence
class of residual polynomials under an automorphism of the residue field, such as a power of
Frobenius, is again a class. -/
lemma image_map_residualActOrbit (hf : Function.Surjective f) : List.map (map f) ''
    residualActOrbit F P = residualActOrbit F' (P.map (Prod.map id (map f))) := by
  refine Set.ext fun A ↦ ⟨?_, ?_⟩
  · rintro ⟨_, ⟨δ, rfl⟩, rfl⟩
    exact ⟨Units.mk0 (f δ) ((map_ne_zero f).mpr δ.ne_zero), (map_residualAct (δ : F) P f).symm⟩
  · rintro ⟨δ', rfl⟩
    rcases hf δ' with ⟨δ, hδ⟩
    exact ⟨residualAct δ P, ⟨Units.mk0 δ ((map_ne_zero f).mp (hδ ▸ δ'.ne_zero)), rfl⟩,
      by rw [map_residualAct, hδ]⟩

end Action

section Polygon

variable {L L' : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Field L'] [ValuativeRel L'] [TopologicalSpace L']
  [IsNonarchimedeanLocalField L'] {ρ : L[X]} {ρ' : L'[X]} {kl : ℕ × ℕ}

lemma eq_of_polygonGraph_eq {a b : ℕ → WithTop ℝ} (h : polygonGraph a = polygonGraph b) :
    a = b := by
  funext n
  have key (y : ℝ) : a n = y ↔ b n = y := by
    rw [← natCast_mem_polygonGraph, ← natCast_mem_polygonGraph, h]
  rcases eq_or_ne (a n) ⊤ with ha | ha
  · rcases eq_or_ne (b n) ⊤ with hb | hb
    · rw [ha, hb]
    · rcases WithTop.ne_top_iff_exists.mp hb with ⟨y, hy⟩
      exact absurd (ha ▸ (key y).mpr hy.symm) WithTop.top_ne_coe
  · rcases WithTop.ne_top_iff_exists.mp ha with ⟨y, hy⟩
    rw [← hy]
    exact ((key y).mp hy.symm).symm

/-- **Two polynomials with the same ramification polygon have the same Newton polygon**: if the
ramification polygons of `φ` at `α` and of `φ'` at `α'`, over two nonarchimedean local fields, are
the same subset of the plane, then the lower convex envelopes of the heights of the coefficients of
the two ramification polynomials agree. So the ramification polynomials have the same segments,
with the same slopes. -/
lemma coeffEnvelope_eq_of_ramificationPolygonOf_eq {F F' : Type*} [Field F] [Field F'] [Algebra F L]
    [Algebra F' L'] {φ : F[X]} {φ' : F'[X]} {α : L} {α' : L'}
    (h : ramificationPolygonOf φ α = ramificationPolygonOf φ' α') :
    coeffEnvelope (ramificationPolynomial φ α) = coeffEnvelope (ramificationPolynomial φ' α') := by
  rw [ramificationPolygonOf_eq_image_reflectVertical,
    ramificationPolygonOf_eq_image_reflectVertical,
    lowerConvexHull_heightPoints finite_coeffHeight_ne_top,
    lowerConvexHull_heightPoints finite_coeffHeight_ne_top] at h
  refine eq_of_polygonGraph_eq ?_
  rw [← image_reflectVertical_image_reflectVertical (polygonGraph _), h,
    image_reflectVertical_image_reflectVertical]

lemma residualSegments_eq_of_coeffEnvelope_eq' (h : coeffEnvelope ρ' = coeffEnvelope ρ) :
    residualSegments ρ' = residualSegments ρ := by
  have hU : residualUnitSlopes ρ' = residualUnitSlopes ρ :=
    Finset.ext fun s ↦ by rw [mem_residualUnitSlopes, mem_residualUnitSlopes, h]
  rw [residualSegments, residualSegments, residualSlopeList, residualSlopeList, hU]
  congr 1
  funext s
  rw [residualSegmentOf, residualSegmentOf, h]

lemma residualSlope_eq_of_coeffEnvelope_eq' (h : coeffEnvelope ρ' = coeffEnvelope ρ)
    (hkl : kl ∈ residualSegments ρ) : residualSlope ρ' kl.1 kl.2 = residualSlope ρ kl.1 kl.2 := by
  have hkl' : kl ∈ residualSegments ρ' := by
    rwa [residualSegments_eq_of_coeffEnvelope_eq' h]
  have h₁ : (coeffHeight ρ' kl.1).untop₀ = (coeffHeight ρ kl.1).untop₀ :=
    congrArg WithTop.untop₀ ((coeffEnvelope_fst_of_mem_residualSegments hkl').symm.trans
      ((congrFun h kl.1).trans (coeffEnvelope_fst_of_mem_residualSegments hkl)))
  have h₂ : (coeffHeight ρ' (kl.1 + kl.2)).untop₀ = (coeffHeight ρ (kl.1 + kl.2)).untop₀ :=
    congrArg WithTop.untop₀ ((coeffEnvelope_add_of_mem_residualSegments hkl').symm.trans
      ((congrFun h (kl.1 + kl.2)).trans (coeffEnvelope_add_of_mem_residualSegments hkl)))
  rw [untop₀_coeffHeight, untop₀_coeffHeight] at h₁ h₂
  rw [residualSlope, residualSlope, Int.cast_inj.mp h₁, Int.cast_inj.mp h₂]

lemma map_fst_residualPairs_eq_of_coeffEnvelope_eq (h : coeffEnvelope ρ' = coeffEnvelope ρ) (α : L)
    (α' : L') : (residualPairs ρ' α').map Prod.fst = (residualPairs ρ α).map Prod.fst := by
  rw [residualPairs, residualPairs, List.map_map, List.map_map,
    residualSegments_eq_of_coeffEnvelope_eq' h]
  exact List.map_congr_left fun kl hkl ↦
    congrArg Rat.num (residualSlope_eq_of_coeffEnvelope_eq' h hkl)

end Polygon

lemma map_ramificationPolynomial {F F' L L' : Type*} [Field F] [Field F'] [Field L] [Field L']
    [Algebra F L] [Algebra F' L'] (τ : F →+* F') (σ : L →+* L')
    (h : (algebraMap F' L').comp τ = σ.comp (algebraMap F L)) (φ : F[X]) (α : L) :
    (ramificationPolynomial φ α).map σ = ramificationPolynomial (φ.map τ) (σ α) := by
  rw [ramificationPolynomial, ramificationPolynomial, Polynomial.map_mul, map_C, map_comp,
    Polynomial.map_add, Polynomial.map_mul, map_C, map_X, map_map, ← h, ← map_map, natDegree_map,
    map_pow, map_inv₀]

/-- **A `K`-isomorphism maps the unramified extension of degree `f` onto that of the target**: for a
`K`-isomorphism `σ : L ≃ L'` of extensions of a nonarchimedean local field `K`, the image under `σ`
of the unramified extension of `K` of degree `f` inside `L`, generated by the roots of
`X ^ (q ^ f) - X`, is the one inside `L'`. -/
lemma map_unramifiedExtension_algEquiv {K L L' : Type*} [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Field L] [Field L'] [Algebra K L]
    [Algebra K L'] (σ : L ≃ₐ[K] L') (f : ℕ) :
    (unramifiedExtension K L f).map (σ : L →ₐ[K] L') = unramifiedExtension K L' f :=
  le_antisymm (map_unramifiedExtension_le f (σ : L →ₐ[K] L')) fun x hx ↦ ⟨σ.symm x,
    map_unramifiedExtension_le f (σ.symm : L' →ₐ[K] L) ⟨x, hx, rfl⟩, σ.apply_symm_apply x⟩

section Transport

variable {K L L' : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L] [Field L'] [ValuativeRel L']
  [TopologicalSpace L'] [IsNonarchimedeanLocalField L'] [Algebra K L'] [ValuativeExtension K L']
  (σ : L ≃ₐ[K] L') (ρ : L[X]) {x : L} (α : L) (k l : ℕ)

variable {ρ α} in
/-- **The class of residual polynomials is an orbit** (LMFDB `lf.residual_polynomials`): when the
residue field of `L` is that of `K`, as for a totally ramified extension, the equivalence class
`𝒜 = {(γ_{δ,1} A_1(δ ^ h_1 x), …, γ_{δ,ℓ} A_ℓ(δ ^ h_ℓ x)) : δ ∈ K̲ ^ ×}` of the list of residual
polynomials of `ρ` at `α` is the orbit of the pairs `(h_i, A_i)` under all the units of `L̲`. -/
lemma residualPolynomialClass_eq_residualActOrbit (h : Function.Surjective (algebraMap 𝓀[K] 𝓀[L])) :
    residualPolynomialClass K ρ α = residualActOrbit 𝓀[L] (residualPairs ρ α) := by
  refine Set.ext fun A ↦ ⟨?_, ?_⟩
  · rintro ⟨δ, rfl⟩
    exact ⟨Units.mk0 (algebraMap 𝓀[K] 𝓀[L] δ)
      ((map_ne_zero (algebraMap 𝓀[K] 𝓀[L])).mpr δ.ne_zero), rfl⟩
  · rintro ⟨δ', rfl⟩
    rcases h δ' with ⟨δ, hδ⟩
    refine ⟨Units.mk0 δ ((map_ne_zero (algebraMap 𝓀[K] 𝓀[L])).mp (hδ ▸ δ'.ne_zero)), ?_⟩
    dsimp only
    rw [Units.val_mk0, hδ]

variable (x) in
/-- **A `K`-isomorphism of extensions preserves the normalised valuations**: for a `K`-isomorphism
`σ : L ≃ L'` of extensions of a nonarchimedean local field `K`, `v_{L'}(σ x) = v_L(x)`. Through
`σ`, `L'` is an extension of `L` of degree `1`, so of ramification index `1`. -/
lemma addValuation_algEquiv : addValuation L' (σ x) = addValuation L x := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, addValuation_zero, addValuation_zero]
  have hK : Module.Finite K L := finite_of_valuativeExtension K L
  let _ : Algebra L L' := σ.toRingHom.toAlgebra
  have hv : ValuativeExtension L L' := σ.toAlgHom.valuativeExtension
  have hf : Module.finrank L L' = 1 := Module.finrank_of_bijective_algebraMap σ.bijective
  have hfin : Module.Finite L L' := Module.finite_of_finrank_eq_succ hf
  have he : ramificationIndex L L' = 1 :=
    (mul_eq_one.mp ((ramificationIndex_mul_inertiaDegree L L').trans hf)).1
  have hσx : σ x ≠ 0 := (map_ne_zero σ).mpr hx
  have h₁ : Units.mk0 (σ x) hσx = Units.map (algebraMap L L' : L →* L') (Units.mk0 x hx) :=
    Units.ext rfl
  rw [addValuation_of_ne_zero hσx, addValuation_of_ne_zero hx, h₁,
    toAdd_normalizedValuation_algebraMap, he, Nat.cast_one, one_mul]

lemma mem_integer_algEquiv : σ x ∈ 𝒪[L'] ↔ x ∈ 𝒪[L] := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero]
    exact ⟨fun _ ↦ zero_mem _, fun _ ↦ zero_mem _⟩
  · rw [mem_integer_iff_zero_le_addValuation ((map_ne_zero σ).mpr hx),
      mem_integer_iff_zero_le_addValuation hx, addValuation_algEquiv]

lemma coeffVal_map_algEquiv (i : ℕ) : coeffVal (ρ.map (σ : L →+* L')) i = coeffVal ρ i := by
  rw [coeffVal, coeffVal, coeff_map]
  exact congrArg WithTop.untop₀ (addValuation_algEquiv σ _)

lemma coeffHeight_map_algEquiv : coeffHeight (ρ.map (σ : L →+* L')) = coeffHeight ρ := by
  funext n
  rw [coeffHeight_apply, coeffHeight_apply, coeff_map]
  exact congrArg (WithTop.map _) (addValuation_algEquiv σ _)

lemma residualSegments_map_algEquiv :
    residualSegments (ρ.map (σ : L →+* L')) = residualSegments ρ :=
  residualSegments_eq_of_coeffEnvelope_eq' <|
    congrArg lowerConvexEnvelope (coeffHeight_map_algEquiv σ ρ)

lemma residualSlope_map_algEquiv :
    residualSlope (ρ.map (σ : L →+* L')) k l = residualSlope ρ k l := by
  rw [residualSlope, residualSlope, coeffVal_map_algEquiv, coeffVal_map_algEquiv]

lemma inertiaDegree_eq_of_algEquiv (e : L ≃ₐ[K] L') : inertiaDegree K L' = inertiaDegree K L := by
  have hL' : Module.Finite K L' := finite_of_valuativeExtension K L'
  exact (ResidueField.mapAlgEquiv' e.integerRingEquiv).toLinearEquiv.finrank_eq.symm

variable (x) [Algebra.IsAlgebraic K L] in
lemma residueOf_algEquiv : residueOf L' (σ x) = σ.toAlgHom.residueFieldHom (residueOf L x) := by
  by_cases hx : x ∈ 𝒪[L]
  · rw [residueOf, dite_eq_left ((mem_integer_algEquiv σ).mpr hx), residueOf, dite_eq_left hx,
      AlgHom.residueFieldHom_residue]
    rfl
  · rw [residueOf, dite_eq_right (mt (mem_integer_algEquiv σ).mp hx), residueOf,
      dite_eq_right hx, map_zero]

variable [Algebra.IsAlgebraic K L] in
lemma residualPolynomial_map_algEquiv : residualPolynomial (ρ.map (σ : L →+* L')) (σ α) k l =
    (residualPolynomial ρ α k l).map σ.toAlgHom.residueFieldHom := by
  rw [residualPolynomial, residualPolynomial, residualSlope_map_algEquiv, coeffVal_map_algEquiv,
    Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Polynomial.map_mul, map_C, Polynomial.map_pow, map_X, coeff_map, RingHom.coe_coe,
    RingHom.coe_coe, ← map_zpow₀, ← map_mul, residueOf_algEquiv]

variable [Algebra.IsAlgebraic K L] in
lemma residualPolynomials_map_algEquiv : residualPolynomials (ρ.map (σ : L →+* L')) (σ α) =
    (residualPolynomials ρ α).map (map σ.toAlgHom.residueFieldHom) := by
  rw [residualPolynomials, residualPolynomials, residualSegments_map_algEquiv, List.map_map]
  exact List.map_congr_left fun kl _ ↦ residualPolynomial_map_algEquiv σ ρ α kl.1 kl.2

variable [Algebra.IsAlgebraic K L] in
lemma residualPairs_map_algEquiv : residualPairs (ρ.map (σ : L →+* L')) (σ α) =
    (residualPairs ρ α).map (Prod.map id (map σ.toAlgHom.residueFieldHom)) := by
  rw [residualPairs, residualPairs, residualSegments_map_algEquiv, List.map_map]
  exact List.map_congr_left fun kl _ ↦ by
    rw [residualSlope_map_algEquiv, residualPolynomial_map_algEquiv]
    rfl

variable [FiniteDimensional K L]

/-- **A `K`-isomorphism maps the ramification polynomial of `L / L^un` at `α` to that of
`L' / L'^un` at `σ α`** (LMFDB `lf.ramification_polygon`): for a `K`-isomorphism `σ : L ≃ L'` of
finite extensions of a nonarchimedean local field `K`, with maximal unramified subextensions `L^un`
and `L'^un`, `σ` maps `L^un` onto `L'^un` and the minimal polynomial of `α` over `L^un` to that of
`σ α` over `L'^un`, so it maps the ramification polynomial `α ^ (-n) φ(α x + α)` to
`(σ α) ^ (-n) φ'(σ α x + σ α)`. -/
lemma ramificationPolynomial_minpoly_algEquiv : ramificationPolynomial
    (minpoly (unramifiedExtension K L' (inertiaDegree K L')) (σ α)) (σ α) =
      (ramificationPolynomial (minpoly (unramifiedExtension K L (inertiaDegree K L)) α) α).map
        (σ : L →+* L') := by
  have hU : (unramifiedExtension K L (inertiaDegree K L)).map (σ : L →ₐ[K] L') =
      unramifiedExtension K L' (inertiaDegree K L') := by
    rw [map_unramifiedExtension_algEquiv, inertiaDegree_eq_of_algEquiv σ]
  let τ : unramifiedExtension K L (inertiaDegree K L) ≃ₐ[K]
      unramifiedExtension K L' (inertiaDegree K L') :=
    (IntermediateField.equivMap _ (σ : L →ₐ[K] L')).trans (IntermediateField.equivOfEq hU)
  have hτ : (algebraMap (unramifiedExtension K L' (inertiaDegree K L')) L').comp
      (τ.toRingEquiv : unramifiedExtension K L (inertiaDegree K L) →+*
        unramifiedExtension K L' (inertiaDegree K L')) =
      (σ.toRingEquiv : L →+* L').comp
        (algebraMap (unramifiedExtension K L (inertiaDegree K L)) L) :=
    RingHom.ext fun _ ↦ rfl
  have hmin : minpoly (unramifiedExtension K L' (inertiaDegree K L')) (σ α) =
      (minpoly (unramifiedExtension K L (inertiaDegree K L)) α).map
        (τ.toRingEquiv : unramifiedExtension K L (inertiaDegree K L) →+*
          unramifiedExtension K L' (inertiaDegree K L')) :=
    (minpoly.map_eq_of_equiv_equiv hτ α).symm
  rw [hmin]
  exact (map_ramificationPolynomial _ _ hτ _ α).symm

/-- **A `K`-isomorphism preserves the ramification polygon** (LMFDB `lf.ramification_polygon`):
for a `K`-isomorphism `σ : L ≃ L'` of finite extensions of a nonarchimedean local field `K`, the
ramification polygon of `L' / L'^un` at `σ α` is that of `L / L^un` at `α`. -/
lemma ramificationPolygonOf_minpoly_algEquiv : ramificationPolygonOf
    (minpoly (unramifiedExtension K L' (inertiaDegree K L')) (σ α)) (σ α) =
      ramificationPolygonOf (minpoly (unramifiedExtension K L (inertiaDegree K L)) α) α := by
  rw [ramificationPolygonOf, ramificationPolygonOf, ramificationPolynomial_minpoly_algEquiv,
    coeffHeight_map_algEquiv]

/-- **A `K`-isomorphism maps the residual polynomials of `L` at `α` to those of `L'` at `σ α`**
(LMFDB `lf.residual_polynomials`): for a `K`-isomorphism `σ : L ≃ L'` of finite extensions of a
nonarchimedean local field `K`, the list of residual polynomials of `L' / L'^un` at `σ α` is the
image of that of `L / L^un` at `α` under the isomorphism `σ̲ : L̲ ≃ L̲'` of residue fields induced
by `σ`, applied to the coefficients. -/
lemma residualPolynomials_minpoly_algEquiv : residualPolynomials (ramificationPolynomial
    (minpoly (unramifiedExtension K L' (inertiaDegree K L')) (σ α)) (σ α)) (σ α) =
      (residualPolynomials (ramificationPolynomial
        (minpoly (unramifiedExtension K L (inertiaDegree K L)) α) α) α).map
          (map σ.toAlgHom.residueFieldHom) := by
  rw [ramificationPolynomial_minpoly_algEquiv, residualPolynomials_map_algEquiv]

/-- **A `K`-isomorphism maps the class of residual polynomials of `L` to that of `L'`** (LMFDB
`lf.residual_polynomials`): for a `K`-isomorphism `σ : L ≃ L'` of finite extensions of a
nonarchimedean local field `K` and an element `α` of `L`, the equivalence class of residual
polynomials of `L' / L'^un` at `σ α` is the image of that of `L / L^un` at `α` under the isomorphism
`σ̲ : L̲ ≃ L̲'` of residue fields, applied to the coefficients. -/
lemma residualPolynomialClass_minpoly_algEquiv : residualPolynomialClass
    (unramifiedExtension K L' (inertiaDegree K L')) (ramificationPolynomial
      (minpoly (unramifiedExtension K L' (inertiaDegree K L')) (σ α)) (σ α)) (σ α) =
      List.map (map σ.toAlgHom.residueFieldHom) '' residualPolynomialClass
        (unramifiedExtension K L (inertiaDegree K L)) (ramificationPolynomial
          (minpoly (unramifiedExtension K L (inertiaDegree K L)) α) α) α := by
  have hL' : FiniteDimensional K L' := σ.toLinearEquiv.finiteDimensional
  have hσ : Function.Surjective σ.toAlgHom.residueFieldHom := fun y ↦
    ⟨σ.symm.toAlgHom.residueFieldHom y, by rw [← AlgHom.comp_apply, ← AlgHom.residueFieldHom_comp,
      AlgEquiv.comp_symm, AlgHom.residueFieldHom_id, AlgHom.id_apply]⟩
  rw [residualPolynomialClass_eq_residualActOrbit
      ((isTotallyRamified_iff_surjective_algebraMap_residueField _ L').mp
        (isTotallyRamified_unramifiedExtension_inertiaDegree K L')),
    residualPolynomialClass_eq_residualActOrbit
      ((isTotallyRamified_iff_surjective_algebraMap_residueField _ L).mp
        (isTotallyRamified_unramifiedExtension_inertiaDegree K L)),
    ramificationPolynomial_minpoly_algEquiv, residualPairs_map_algEquiv,
    image_map_residualActOrbit _ (σ.toAlgHom.residueFieldHom : 𝓀[L] →+* 𝓀[L']) hσ]

end Transport

end IsNonarchimedeanLocalField
