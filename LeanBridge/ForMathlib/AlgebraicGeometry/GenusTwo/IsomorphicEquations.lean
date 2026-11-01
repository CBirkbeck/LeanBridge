import LeanBridge.ForMathlib.AlgebraicGeometry.GenusTwo.ChangeOfVariables
import TauCeti.FieldTheory.FunctionField.Hyperelliptic.RationalSubfield
import TauCeti.FieldTheory.RatFunc.Mobius
import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Weierstrass equations of the same curve

Two Weierstrass equations `y² + h(x)y = f(x)` and `Y² + h'(X)Y = f'(X)` of genus `g ≥ 2` with
nonzero discriminant, over a field `K` of characteristic not two, define the same curve when their
function fields are isomorphic over `K`. This file proves that this happens exactly when they are
related by a change of variables `x = (aX + b) / (cX + d)`, `y = (eY + t(X)) / (cX + d)^(g + 1)`
with `ad - bc ≠ 0` and `e ≠ 0` (`HyperellipticEquation.changeOfVariables`).

A `K`-isomorphism `τ : K(x, y) ≃ K(X, Y)` carries the rational subfield `K(x)` of index two onto a
rational subfield of index two, which is `K(X)` by Tau Ceti's uniqueness of the rational subfield
of index two of a hyperelliptic function field. So `τ x` generates `K(X)`, hence is a linear
fractional transformation `(aX + b) / (cX + d)` with `ad - bc ≠ 0`, and `τ` acts on `K(x)` through
the automorphism `X ↦ (aX + b) / (cX + d)` of `K(X)`. The coordinate `w = 2y + h(x)` of the
simplified equation `w² = F(x)`, with `F = 4f + h²`, is not in `K(x)` and has its square in `K(x)`,
so `τ w = βW` for some `β ∈ K(X)`, where `W = 2Y + h'(X)`: an element `α + βW` of
`K(X, Y) = K(X) ⊕ K(X)W` with square `α² + β²F' + 2αβW` in `K(X)` has `α = 0` or `β = 0`.
Squaring, `F(aX + b, cX + d) = γ² F'(X)` for the binary form `F(x, z)` of degree `2g + 2` and
`γ = β (cX + d)^(g + 1)`; as `F'` is squarefree of degree at least `2g + 1`, `γ` is a nonzero
constant `e`. The change of variables with these `a, b, c, d, e` and
`t = (e h'(X) - h(aX + b, cX + d)) / 2` then turns the first equation into the second. The
characteristic is not two throughout, as for the discriminant itself.

Conversely, `x ↦ (aX + b) / (cX + d)`, `y ↦ (eY + t(X)) / (cX + d)^(g + 1)` is a `K`-isomorphism
of function fields. With the transformation law of the discriminant under changes of variables,
`Δ' = e^(-(8g + 4)) (ad - bc)^((2g + 2)(2g + 1)) Δ`, whose factor is a square, two minimal
equations of the same curve over `ℚ` have the same discriminant (LMFDB `g2c.discriminant`).

## Main results

* `HyperellipticEquation.exists_mobiusOf_eq_of_algEquiv`: an isomorphism of function fields maps
  `x` to a linear fractional transformation of `X`.
* `HyperellipticEquation.exists_changeOfVariables_of_algEquiv` (LMFDB `g2c.discriminant`):
  equations with isomorphic function fields are related by a change of variables.
* `HyperellipticEquation.nonempty_algEquiv_changeOfVariables`: a change of variables gives an
  equation with an isomorphic function field.
* `HyperellipticEquation.nonempty_algEquiv_iff_exists_changeOfVariables`: two equations define the
  same curve exactly when they are related by a change of variables.
* `HyperellipticEquation.IsMinimal.discriminant_eq` (LMFDB `g2c.discriminant`): two minimal
  equations of the same curve over `ℚ` have the same discriminant.
-/

open Polynomial
open scoped IntermediateField

variable {K : Type*} [Field K] {a b c d : K}

namespace Polynomial

lemma algebraMap_binaryComp (hdet : a * d - b * c ≠ 0) {n : ℕ} {p : K[X]} (hp : p.natDegree ≤ n) :
    algebraMap K[X] (RatFunc K) (p.binaryComp n a b c d) =
      aeval (RatFunc.mobiusOf a b c d) p * (RatFunc.C c * RatFunc.X + RatFunc.C d) ^ n := by
  let ι : K[X] →ₐ[K] RatFunc K := IsScalarTower.toAlgHom K K[X] (RatFunc K)
  have hw : (fun i ↦ ι (![C a * X + C b, C c * X + C d] i)) =
      ![RatFunc.C a * RatFunc.X + RatFunc.C b, RatFunc.C c * RatFunc.X + RatFunc.C d] := by
    ext i
    fin_cases i <;> simp [ι]
  rw [binaryComp, ← IsScalarTower.coe_toAlgHom' K K[X] (RatFunc K), ← AlgHom.comp_apply,
    MvPolynomial.comp_aeval, hw, MvPolynomial.aeval_def, ← MvPolynomial.eval_map, ← homogenize_map,
    eval_homogenize (natDegree_map_le.trans hp) _ (RatFunc.mobiusOf_den_ne_zero hdet),
    eval_map_algebraMap]
  rfl

lemma exists_eq_C_sq_mul_of_algebraMap_eq {G F : K[X]} (hF : Squarefree F)
    (hG : G.natDegree < F.natDegree + 2) {γ : RatFunc K} (hγ : γ ≠ 0)
    (h : algebraMap K[X] (RatFunc K) G = γ ^ 2 * algebraMap K[X] (RatFunc K) F) :
    ∃ e : K, e ≠ 0 ∧ G = C (e ^ 2) * F := by
  have hq : algebraMap K[X] (RatFunc K) γ.num = γ * algebraMap K[X] (RatFunc K) γ.denom :=
    (div_eq_iff (RatFunc.algebraMap_ne_zero γ.denom_ne_zero)).mp γ.num_div_denom
  have hGF : G * γ.denom ^ 2 = γ.num ^ 2 * F := by
    refine RatFunc.algebraMap_injective K ?_
    rw [map_mul, map_mul, map_pow, map_pow, h, hq]
    ring1
  have hdvd : γ.denom ^ 2 ∣ F :=
    γ.isCoprime_num_denom.symm.pow.dvd_of_dvd_mul_left ⟨G, by rw [← hGF, mul_comm]⟩
  have h1 : γ.denom = 1 := γ.monic_denom.isUnit_iff.mp <| hF _ <| by rwa [← sq]
  rw [h1, one_pow, mul_one] at hGF
  have hn : γ.num ≠ 0 := RatFunc.num_ne_zero hγ
  have hd : G.natDegree = 2 * γ.num.natDegree + F.natDegree := by
    rw [hGF, natDegree_mul (pow_ne_zero 2 hn) hF.ne_zero, natDegree_pow]
  have h0 : γ.num = C (γ.num.coeff 0) := eq_C_of_natDegree_eq_zero (by omega)
  refine ⟨γ.num.coeff 0, fun he ↦ hn (by rw [h0, he, C_0]), ?_⟩
  rw [hGF, C_pow, ← h0]

end Polynomial

namespace RatFunc

lemma mobiusAutOf_algebraMap (hdet : a * d - b * c ≠ 0) (p : K[X]) :
    mobiusAutOf hdet (algebraMap K[X] (RatFunc K) p) = aeval (mobiusOf a b c d) p := by
  rw [← aeval_X_left_eq_algebraMap, ← aeval_algHom_apply, mobiusAutOf_X]

end RatFunc

namespace AlgEquiv

variable {F F' : Type*} [Field F] [Field F'] [Algebra K F] [Algebra K F']

lemma finrank_adjoin_apply (τ : F ≃ₐ[K] F') (z : F) :
    Module.finrank K⟮τ z⟯ F' = Module.finrank K⟮z⟯ F := by
  have hmap : K⟮z⟯.map τ.toAlgHom = K⟮τ z⟯ := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  refine (Algebra.finrank_eq_of_equiv_equiv
    ((K⟮z⟯.equivMap τ.toAlgHom).trans (IntermediateField.equivOfEq hmap)).toRingEquiv
    τ.toRingEquiv (RingHom.ext fun y ↦ ?_)).symm
  simp

end AlgEquiv

namespace HyperellipticEquation

variable {g : ℕ}

section Field

variable (E : HyperellipticEquation g K) {E' : HyperellipticEquation g K} {e : K} (s : RatFunc K)

lemma monic_equationPolynomial : E.equationPolynomial.Monic := by
  rw [equationPolynomial]
  monicity!

lemma finrank_functionField : Module.finrank (RatFunc K) E.FunctionField = 2 := by
  rw [(AdjoinRoot.powerBasis' E.monic_equationPolynomial).finrank, AdjoinRoot.powerBasis'_dim,
    natDegree_equationPolynomial]

lemma y_ne_algebraMap : E.y ≠ algebraMap (RatFunc K) E.FunctionField s := by
  intro h
  have h' : AdjoinRoot.mk E.equationPolynomial (X - C s) = 0 := by
    rw [map_sub, AdjoinRoot.mk_X, AdjoinRoot.mk_C]
    exact sub_eq_zero.mpr h
  refine X_sub_C_ne_zero s <| eq_zero_of_dvd_of_natDegree_lt (AdjoinRoot.mk_eq_zero.mp h') ?_
  rw [natDegree_X_sub_C, natDegree_equationPolynomial]
  omega

variable [Invertible (2 : K)] in
lemma algebraMap_invOf_two_mul_two :
    algebraMap (RatFunc K) E.FunctionField (algebraMap K (RatFunc K) ⅟2) * 2 = 1 := by
  rw [← IsScalarTower.algebraMap_apply, ← map_ofNat (algebraMap K E.FunctionField) 2, ← map_mul,
    invOf_mul_self, map_one]

variable [Invertible (2 : K)] in
lemma w_ne_algebraMap : E.w ≠ algebraMap (RatFunc K) E.FunctionField s := by
  intro h
  refine E.y_ne_algebraMap (algebraMap K (RatFunc K) ⅟2 * (s - algebraMap K[X] (RatFunc K) E.h)) ?_
  rw [map_mul, map_sub, ← h, w]
  linear_combination (-E.y) * E.algebraMap_invOf_two_mul_two

variable {E} in
lemma algEquiv_algebraMap (τ : E.FunctionField ≃ₐ[K] E'.FunctionField) (hdet : a * d - b * c ≠ 0)
    (hτ : τ (algebraMap (RatFunc K) E.FunctionField RatFunc.X) =
      algebraMap (RatFunc K) E'.FunctionField (RatFunc.mobiusOf a b c d)) (u : RatFunc K) :
    τ (algebraMap (RatFunc K) E.FunctionField u) =
      algebraMap (RatFunc K) E'.FunctionField (RatFunc.mobiusAutOf hdet u) := by
  have h : τ.toAlgHom.comp (IsScalarTower.toAlgHom K (RatFunc K) E.FunctionField) =
      (IsScalarTower.toAlgHom K (RatFunc K) E'.FunctionField).comp (RatFunc.mobiusAutOf hdet) :=
    RatFunc.algHom_ext (by simpa using hτ)
  exact AlgHom.congr_fun h u

section Irreducible

variable [Fact (Irreducible E.equationPolynomial)] (z : E.FunctionField)

lemma exists_eq_algebraMap_add_mul_y :
    ∃ α β : RatFunc K, z = algebraMap _ _ α + algebraMap _ _ β * E.y := by
  rcases (AdjoinRoot.powerBasis' E.monic_equationPolynomial).exists_eq_aeval z with ⟨p, hp, rfl⟩
  rw [AdjoinRoot.powerBasis'_dim, natDegree_equationPolynomial] at hp
  rw [AdjoinRoot.powerBasis'_gen, eq_X_add_C_of_natDegree_le_one (by omega : p.natDegree ≤ 1)]
  refine ⟨p.coeff 0, p.coeff 1, ?_⟩
  simp only [map_add, map_mul, aeval_C, aeval_X, y]
  ring1

lemma transcendental_algebraMap_X :
    Transcendental K (algebraMap (RatFunc K) E.FunctionField RatFunc.X) :=
  (transcendental_algebraMap_iff (algebraMap (RatFunc K) E.FunctionField).injective).mpr
    RatFunc.transcendental_X

lemma finrank_adjoin_algebraMap_X :
    Module.finrank K⟮algebraMap (RatFunc K) E.FunctionField RatFunc.X⟯ E.FunctionField = 2 :=
  TauCeti.finrank_adjoin_algebraMap_X.trans E.finrank_functionField

lemma isFunctionField : TauCeti.IsFunctionField K E.FunctionField :=
  ⟨_, E.transcendental_algebraMap_X,
    Module.finite_of_finrank_pos (by rw [E.finrank_adjoin_algebraMap_X]; omega)⟩

variable [Invertible (2 : K)]

lemma exists_eq_algebraMap_add_mul_w :
    ∃ α β : RatFunc K, z = algebraMap _ _ α + algebraMap _ _ β * E.w := by
  rcases E.exists_eq_algebraMap_add_mul_y z with ⟨α, β, rfl⟩
  refine ⟨α - β * algebraMap K (RatFunc K) ⅟2 * algebraMap K[X] (RatFunc K) E.h,
    β * algebraMap K (RatFunc K) ⅟2, ?_⟩
  rw [map_sub, map_mul, map_mul, w]
  linear_combination (-(algebraMap (RatFunc K) E.FunctionField β * E.y)) *
    E.algebraMap_invOf_two_mul_two

variable {E z s} in
lemma exists_eq_algebraMap_mul_w (hz : ∀ s, z ≠ algebraMap (RatFunc K) E.FunctionField s)
    (hs : z ^ 2 = algebraMap (RatFunc K) E.FunctionField s) :
    ∃ β : RatFunc K, z = algebraMap (RatFunc K) E.FunctionField β * E.w := by
  rcases E.exists_eq_algebraMap_add_mul_w z with ⟨α, β, rfl⟩
  rcases eq_or_ne β 0 with rfl | hβ
  · exact (hz α (by rw [map_zero, zero_mul, add_zero])).elim
  rcases eq_or_ne α 0 with rfl | hα
  · exact ⟨β, by rw [map_zero, zero_add]⟩
  have h2 : (2 : RatFunc K) ≠ 0 := by
    rw [← map_ofNat (algebraMap K (RatFunc K)) 2, ← map_zero (algebraMap K (RatFunc K))]
    exact (algebraMap K (RatFunc K)).injective.ne two_ne_zero
  have hne : algebraMap (RatFunc K) E.FunctionField (2 * α * β) ≠ 0 := fun h ↦
    mul_ne_zero (mul_ne_zero h2 hα) hβ <|
      (algebraMap (RatFunc K) E.FunctionField).injective <| h.trans (map_zero _).symm
  refine (E.w_ne_algebraMap ((s - α ^ 2 - β ^ 2 * algebraMap K[X] (RatFunc K)
    E.simplifiedPolynomial) / (2 * α * β)) ?_).elim
  rw [map_div₀, eq_div_iff hne]
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  linear_combination hs - algebraMap (RatFunc K) E.FunctionField β ^ 2 * E.w_sq

variable {E} in
lemma isIntegrallyClosedIn (hE : E.discriminant ≠ 0) : IsIntegrallyClosedIn K E.FunctionField :=
  TauCeti.isIntegrallyClosedIn_of_sq_eq two_ne_zero (squarefree_simplifiedPolynomial hE)
    (by rcases natDegree_simplifiedPolynomial_eq hE with h | h <;> omega) adjoin_w_eq_top E.w_sq

variable [Fact (Irreducible E'.equationPolynomial)]

variable {E} in
/-- **An isomorphism of function fields maps `x` to a linear fractional transformation of `X`**:
for equations of genus `g ≥ 2` with nonzero discriminant, a `K`-isomorphism `τ : K(x, y) ≃ K(X, Y)`
maps `x` to `(aX + b) / (cX + d)` with `ad - bc ≠ 0`. Indeed `K(τ x)` is a rational subfield of
index two of `K(X, Y)`, so it is `K(X)` (Tau Ceti's uniqueness of the rational subfield of index
two of a hyperelliptic function field), and the generators of `K(X)` are the linear fractional
transformations of `X`. -/
lemma exists_mobiusOf_eq_of_algEquiv (τ : E.FunctionField ≃ₐ[K] E'.FunctionField) (hg : 2 ≤ g)
    (hE' : E'.discriminant ≠ 0) : ∃ a b c d : K, a * d - b * c ≠ 0 ∧
      τ (algebraMap (RatFunc K) E.FunctionField RatFunc.X) =
        algebraMap (RatFunc K) E'.FunctionField (RatFunc.mobiusOf a b c d) := by
  let ι : RatFunc K →ₐ[K] E'.FunctionField := IsScalarTower.toAlgHom K (RatFunc K) E'.FunctionField
  have hadj : K⟮τ (algebraMap (RatFunc K) E.FunctionField RatFunc.X)⟯ =
      K⟮algebraMap (RatFunc K) E'.FunctionField RatFunc.X⟯ :=
    TauCeti.adjoin_eq_adjoin_of_finrank_adjoin_eq_two E'.isFunctionField (isIntegrallyClosedIn hE')
      (by rw [genus_functionField hE']; exact hg) E'.transcendental_algebraMap_X
      E'.finrank_adjoin_algebraMap_X
      (by rw [τ.finrank_adjoin_apply]; exact E.finrank_adjoin_algebraMap_X)
  have hX : K⟮algebraMap (RatFunc K) E'.FunctionField RatFunc.X⟯ =
      (⊤ : IntermediateField K (RatFunc K)).map ι := by
    rw [← RatFunc.adjoin_X, IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  rcases (IntermediateField.mem_map _).mp
    (hX ▸ hadj ▸ IntermediateField.mem_adjoin_simple_self K _) with ⟨r, -, hr⟩
  have hXr : algebraMap (RatFunc K) E'.FunctionField RatFunc.X ∈ K⟮r⟯.map ι := by
    rw [IntermediateField.adjoin_map, Set.image_singleton, hr, hadj]
    exact IntermediateField.mem_adjoin_simple_self K _
  rcases (IntermediateField.mem_map _).mp hXr with ⟨u, hu, hu'⟩
  have htop : K⟮r⟯ = ⊤ := by
    rw [eq_top_iff, ← RatFunc.adjoin_X, IntermediateField.adjoin_simple_le_iff,
      ← ι.injective (hu'.trans rfl)]
    exact hu
  rcases RatFunc.exists_mobiusOf_eq_of_adjoin_eq_top htop with ⟨a, b, c, d, hdet, hm⟩
  exact ⟨a, b, c, d, hdet, by rw [hm]; exact hr.symm⟩

end Irreducible

variable [Invertible (2 : K)] {t : K[X]} (ht : t.natDegree ≤ g + 1)

variable {E} in
lemma natDegree_changeOfVariablesShift_le :
    (C ⅟2 * (C e * E'.h - E.h.binaryComp (g + 1) a b c d)).natDegree ≤ g + 1 :=
  (natDegree_C_mul_le _ _).trans <| (natDegree_sub_le _ _).trans <|
    max_le ((natDegree_C_mul_le _ _).trans E'.natDegree_h_le) (natDegree_binaryComp_le _)

variable {E} in
lemma eq_changeOfVariables_of_binaryComp_eq (he : e ≠ 0)
    (hth : C 2 * t = C e * E'.h - E.h.binaryComp (g + 1) a b c d)
    (h : E.simplifiedPolynomial.binaryComp (2 * g + 2) a b c d =
      C (e ^ 2) * E'.simplifiedPolynomial) : E' = E.changeOfVariables a b c d e t ht := by
  have he' : (C e⁻¹ : K[X]) * C e = 1 := by
    rw [← C_mul, inv_mul_cancel₀ he, C_1]
  have hh : E'.h = (E.changeOfVariables a b c d e t ht).h := by
    simp only [changeOfVariables]
    linear_combination -E'.h * he' - C e⁻¹ * hth
  have hs :
      E'.simplifiedPolynomial = (E.changeOfVariables a b c d e t ht).simplifiedPolynomial := by
    rw [simplifiedPolynomial_changeOfVariables, h, ← mul_assoc, ← C_mul, ← mul_pow,
      inv_mul_cancel₀ he, one_pow, C_1, one_mul]
  have h4 : IsUnit (4 : K[X]) := by
    rw [← map_ofNat C 4]
    exact isUnit_C.mpr isUnit_four
  refine HyperellipticEquation.ext hh <| h4.mul_left_cancel ?_
  rw [simplifiedPolynomial, simplifiedPolynomial, hh] at hs
  exact add_right_cancel hs

variable {E} in
/-- **Equations with isomorphic function fields are related by a change of variables** (LMFDB
`g2c.discriminant`): if two Weierstrass equations `y² + h(x)y = f(x)` and `Y² + h'(X)Y = f'(X)` of
genus `g ≥ 2` with nonzero discriminant, over a field of characteristic not two, have isomorphic
function fields, then the second is obtained from the first by the change of variables
`x = (aX + b) / (cX + d)`, `y = (eY + t(X)) / (cX + d)^(g + 1)` for some `ad - bc ≠ 0`, `e ≠ 0` and
`t` of degree at most `g + 1`. -/
lemma exists_changeOfVariables_of_algEquiv (hg : 2 ≤ g) (hE : E.discriminant ≠ 0)
    (hE' : E'.discriminant ≠ 0) (τ : E.FunctionField ≃ₐ[K] E'.FunctionField) :
    ∃ (a b c d e : K) (t : K[X]) (ht : t.natDegree ≤ g + 1), a * d - b * c ≠ 0 ∧ e ≠ 0 ∧ E' =
      E.changeOfVariables a b c d e t ht := by
  have hfE : Fact (Irreducible E.equationPolynomial) := ⟨irreducible_equationPolynomial hE⟩
  have hfE' : Fact (Irreducible E'.equationPolynomial) := ⟨irreducible_equationPolynomial hE'⟩
  rcases exists_mobiusOf_eq_of_algEquiv τ hg hE' with ⟨a, b, c, d, hdet, hτ⟩
  let σ : RatFunc K ≃ₐ[K] RatFunc K := RatFunc.mobiusAutOf hdet
  have hw (s : RatFunc K) : τ E.w ≠ algebraMap (RatFunc K) E'.FunctionField s := fun hs ↦
    E.w_ne_algebraMap (σ.symm s) <| τ.injective <| by
      rw [hs, algEquiv_algebraMap τ hdet hτ, σ.apply_symm_apply]
  have hsq : τ E.w ^ 2 = algebraMap (RatFunc K) E'.FunctionField
      (σ (algebraMap K[X] (RatFunc K) E.simplifiedPolynomial)) := by
    rw [← map_pow, E.w_sq, algEquiv_algebraMap τ hdet hτ]
  rcases exists_eq_algebraMap_mul_w hw hsq with ⟨β, hβ⟩
  have hβ0 : β ≠ 0 := by
    rintro rfl
    exact hw 0 (by rw [hβ, map_zero, zero_mul])
  have hF : σ (algebraMap K[X] (RatFunc K) E.simplifiedPolynomial) =
      β ^ 2 * algebraMap K[X] (RatFunc K) E'.simplifiedPolynomial := by
    refine (algebraMap (RatFunc K) E'.FunctionField).injective ?_
    rw [← hsq, hβ, mul_pow, E'.w_sq, map_mul, map_pow]
  have hG : algebraMap K[X] (RatFunc K) (E.simplifiedPolynomial.binaryComp (2 * g + 2) a b c d) =
      (β * (RatFunc.C c * RatFunc.X + RatFunc.C d) ^ (g + 1)) ^ 2 *
        algebraMap K[X] (RatFunc K) E'.simplifiedPolynomial := by
    rw [algebraMap_binaryComp hdet (E.natDegree_simplifiedPolynomial.trans_le E.natDegree_rhs_le),
      ← RatFunc.mobiusAutOf_algebraMap hdet, hF]
    ring1
  rcases exists_eq_C_sq_mul_of_algebraMap_eq (squarefree_simplifiedPolynomial hE')
    ((natDegree_binaryComp_le _).trans_lt (by
      rcases natDegree_simplifiedPolynomial_eq hE' with h | h <;> omega))
    (mul_ne_zero hβ0 (pow_ne_zero (g + 1) (RatFunc.mobiusOf_den_ne_zero hdet))) hG
    with ⟨e, he, heq⟩
  refine ⟨a, b, c, d, e, C ⅟2 * (C e * E'.h - E.h.binaryComp (g + 1) a b c d),
    natDegree_changeOfVariablesShift_le, hdet, he,
    eq_changeOfVariables_of_binaryComp_eq _ he ?_ heq⟩
  rw [← mul_assoc, ← C_mul, mul_invOf_self, C_1, one_mul]

/-- **A change of variables gives an isomorphic function field**: for a Weierstrass equation
`y² + h(x)y = f(x)` with nonzero discriminant over a field of characteristic not two, and a change
of variables with `ad - bc ≠ 0` and `e ≠ 0`, the substitution `x ↦ (aX + b) / (cX + d)`,
`y ↦ (eY + t(X)) / (cX + d)^(g + 1)` is a `K`-isomorphism from the function field of the equation
onto that of the new equation. -/
lemma nonempty_algEquiv_changeOfVariables (hE : E.discriminant ≠ 0) (hdet : a * d - b * c ≠ 0)
    (he : e ≠ 0) :
    Nonempty (E.FunctionField ≃ₐ[K] (E.changeOfVariables a b c d e t ht).FunctionField) := by
  have hE' : (E.changeOfVariables a b c d e t ht).discriminant ≠ 0 := by
    rw [discriminant_changeOfVariables _ _ _ _ _ _ _ he]
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (inv_ne_zero he)) (pow_ne_zero _ hdet)) hE
  have hh :
      (E.changeOfVariables a b c d e t ht).h = C e⁻¹ * (E.h.binaryComp (g + 1) a b c d + C 2 * t) :=
    rfl
  have hf : (E.changeOfVariables a b c d e t ht).f = C (e⁻¹ ^ 2) *
      (E.f.binaryComp (2 * g + 2) a b c d - t ^ 2 - E.h.binaryComp (g + 1) a b c d * t) :=
    rfl
  generalize E.changeOfVariables a b c d e t ht = E' at hE' hh hf ⊢
  have hfE : Fact (Irreducible E.equationPolynomial) := ⟨irreducible_equationPolynomial hE⟩
  have hfE' : Fact (Irreducible E'.equationPolynomial) := ⟨irreducible_equationPolynomial hE'⟩
  let σ : RatFunc K ≃ₐ[K] RatFunc K := RatFunc.mobiusAutOf hdet
  let D : RatFunc K := (RatFunc.C c * RatFunc.X + RatFunc.C d) ^ (g + 1)
  have huv : algebraMap (RatFunc K) E'.FunctionField D⁻¹ *
      algebraMap (RatFunc K) E'.FunctionField D = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (pow_ne_zero _ (RatFunc.mobiusOf_den_ne_zero hdet)), map_one]
  have hε : algebraMap (RatFunc K) E'.FunctionField (RatFunc.C e) *
      algebraMap (RatFunc K) E'.FunctionField (RatFunc.C e⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ he, map_one, map_one]
  let i : RatFunc K →ₐ[K] E'.FunctionField :=
    (IsScalarTower.toAlgHom K (RatFunc K) E'.FunctionField).comp σ.toAlgHom
  have hi (r : RatFunc K) :
      (i : RatFunc K →+* E'.FunctionField) r = algebraMap (RatFunc K) E'.FunctionField (σ r) :=
    rfl
  let z : E'.FunctionField := algebraMap (RatFunc K) E'.FunctionField D⁻¹ *
    (algebraMap (RatFunc K) E'.FunctionField (RatFunc.C e) * E'.y +
      algebraMap (RatFunc K) E'.FunctionField (algebraMap K[X] (RatFunc K) t))
  have hz : E.equationPolynomial.eval₂ i z = 0 := by
    have hy : E'.y ^ 2 + algebraMap (RatFunc K) E'.FunctionField (algebraMap K[X] _ E'.h) * E'.y =
        algebraMap (RatFunc K) E'.FunctionField (algebraMap K[X] _ E'.f) :=
      E'.y_sq_add
    have hH : algebraMap (RatFunc K) E'.FunctionField (aeval (RatFunc.mobiusOf a b c d) E.h) *
        algebraMap (RatFunc K) E'.FunctionField D = algebraMap (RatFunc K) E'.FunctionField
          (algebraMap K[X] _ (E.h.binaryComp (g + 1) a b c d)) := by
      rw [← map_mul, algebraMap_binaryComp hdet E.natDegree_h_le]
    have hF : algebraMap (RatFunc K) E'.FunctionField (aeval (RatFunc.mobiusOf a b c d) E.f) *
        algebraMap (RatFunc K) E'.FunctionField D ^ 2 = algebraMap (RatFunc K) E'.FunctionField
          (algebraMap K[X] _ (E.f.binaryComp (2 * g + 2) a b c d)) := by
      rw [← map_pow, ← map_mul, algebraMap_binaryComp hdet E.natDegree_f_le, ← pow_mul,
        (by ring1 : (g + 1) * 2 = 2 * g + 2)]
    have h2 : algebraMap (RatFunc K) E'.FunctionField (RatFunc.C 2) = 2 := by
      rw [map_ofNat RatFunc.C 2, map_ofNat]
    rw [hh, hf] at hy
    simp only [map_mul, map_add, map_sub, map_pow, RatFunc.algebraMap_C] at hy
    rw [h2, ← hH, ← hF] at hy
    simp only [equationPolynomial, eval₂_sub, eval₂_add, eval₂_mul, eval₂_X_pow, eval₂_C, eval₂_X,
      hi, z, σ, RatFunc.mobiusAutOf_algebraMap]
    generalize algebraMap (RatFunc K) E'.FunctionField D⁻¹ = u at huv ⊢
    generalize algebraMap (RatFunc K) E'.FunctionField D = v at huv hy ⊢
    generalize algebraMap (RatFunc K) E'.FunctionField (RatFunc.C e) = ê at hε ⊢
    generalize algebraMap (RatFunc K) E'.FunctionField (RatFunc.C e⁻¹) = ε at hε hy ⊢
    generalize algebraMap (RatFunc K) E'.FunctionField (algebraMap K[X] (RatFunc K) t) = T at hy ⊢
    generalize algebraMap (RatFunc K) E'.FunctionField (aeval (RatFunc.mobiusOf a b c d) E.h) = H
      at hy ⊢
    generalize algebraMap (RatFunc K) E'.FunctionField (aeval (RatFunc.mobiusOf a b c d) E.f) = F
      at hy ⊢
    linear_combination ê ^ 2 * u ^ 2 * hy +
      (-2 * u ^ 2 * ê * T * E'.y - u ^ 2 * T ^ 2 * (ê * ε + 1) - H * u * ê * E'.y * (u * v) -
        H * u * T * (ê * ε + 1) * (u * v) + F * (ê * ε * (u * v) + 1) * (u * v)) * hε +
      (-H * u * ê * E'.y - H * u * T + F * (ê * ε * (u * v) + 1)) * huv
  let φ : E.FunctionField →ₐ[K] E'.FunctionField :=
    AdjoinRoot.liftAlgHom E.equationPolynomial i z hz
  have hmem (r : RatFunc K) : algebraMap (RatFunc K) E'.FunctionField r ∈ φ.range :=
    φ.mem_range.mpr ⟨algebraMap (RatFunc K) E.FunctionField (σ.symm r),
      (AdjoinRoot.liftAlgHom_of _ _ _ _ _).trans <| (hi _).trans <|
        congrArg _ (σ.apply_symm_apply r)⟩
  have hφy : φ E.y = z := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hY : E'.y = algebraMap (RatFunc K) E'.FunctionField (RatFunc.C e⁻¹) *
      (algebraMap (RatFunc K) E'.FunctionField D * φ E.y -
        algebraMap (RatFunc K) E'.FunctionField (algebraMap K[X] (RatFunc K) t)) := by
    rw [hφy]
    linear_combination (-E'.y * (algebraMap (RatFunc K) E'.FunctionField D⁻¹ *
      algebraMap (RatFunc K) E'.FunctionField D)) * hε + (-E'.y - algebraMap (RatFunc K)
        E'.FunctionField (RatFunc.C e⁻¹) * algebraMap (RatFunc K) E'.FunctionField
          (algebraMap K[X] (RatFunc K) t)) * huv
  refine ⟨AlgEquiv.ofBijective φ ⟨φ.toRingHom.injective, fun w ↦ φ.mem_range.mp ?_⟩⟩
  rcases E'.exists_eq_algebraMap_add_mul_y w with ⟨α, β, rfl⟩
  exact add_mem (hmem α) <| mul_mem (hmem β) <| hY ▸ mul_mem (hmem _) <|
    sub_mem (mul_mem (hmem _) (φ.mem_range_self E.y)) (hmem _)

variable {E} in
/-- **Two equations define the same curve exactly when they are related by a change of
variables**: two Weierstrass equations of genus `g ≥ 2` with nonzero discriminant, over a field of
characteristic not two, have isomorphic function fields if and only if the second is obtained from
the first by a change of variables `x = (aX + b) / (cX + d)`, `y = (eY + t(X)) / (cX + d)^(g + 1)`
with `ad - bc ≠ 0` and `e ≠ 0`. -/
lemma nonempty_algEquiv_iff_exists_changeOfVariables (hg : 2 ≤ g) (hE : E.discriminant ≠ 0)
    (hE' : E'.discriminant ≠ 0) : Nonempty (E.FunctionField ≃ₐ[K] E'.FunctionField) ↔
      ∃ (a b c d e : K) (t : K[X]) (ht : t.natDegree ≤ g + 1), a * d - b * c ≠ 0 ∧ e ≠ 0 ∧ E' =
        E.changeOfVariables a b c d e t ht := by
  refine ⟨fun ⟨τ⟩ ↦ exists_changeOfVariables_of_algEquiv hg hE hE' τ, ?_⟩
  rintro ⟨a, b, c, d, e, t, ht, hdet, he, rfl⟩
  exact E.nonempty_algEquiv_changeOfVariables ht hE hdet he

end Field

variable {E E' : HyperellipticEquation g ℤ}

/-- **Two minimal equations of the same curve have the same discriminant** (LMFDB
`g2c.discriminant`): for minimal integral Weierstrass equations of genus `g ≥ 2` with isomorphic
function fields over `ℚ`, the equations are related by a change of variables, which multiplies the
discriminant by a square, so the discriminants, which have the same absolute value, are equal. -/
lemma IsMinimal.discriminant_eq (hg : 2 ≤ g) (hE : E.IsMinimal) (hE' : E'.IsMinimal)
    (eF : E'.toRat.FunctionField ≃ₐ[ℚ] E.toRat.FunctionField) :
    E.toRat.discriminant = E'.toRat.discriminant := by
  rcases exists_changeOfVariables_of_algEquiv hg hE.discriminant_ne_zero hE'.discriminant_ne_zero
    (by convert eF.symm <;> exact Subsingleton.elim _ _) with ⟨a, b, c, d, e, t, ht, -, he, hc⟩
  exact hE.discriminant_eq_of_changeOfVariables hE' eF he ht hc

end HyperellipticEquation
