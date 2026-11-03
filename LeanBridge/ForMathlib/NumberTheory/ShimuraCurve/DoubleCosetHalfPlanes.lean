import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.AdelicEllipticPoint

/-!
# The double coset spaces `B^× \ (ℋ^± × B̂^×) / K`

The LMFDB (knowl `shimcurve`) writes the complex points of a Shimura curve as a double coset space
`B^× \ (ℋ^± × B̂^×) / K`, where `ℋ^± = ℂ ∖ ℝ` and `B^×` acts on it by Möbius transformations through
a fixed embedding `ι : B → M₂(ℝ)`. This file constructs `ℋ^±` with its action of `GL₂(ℝ)`, the
double coset space `B^× \ (ℋ^± × B̂^×) / K` of any subgroup `K` of `B̂^×`, and the stabilizer group
and the elliptic points of its points. The stabilizer group of `[z, b]` is the image of the
stabilizer of `(z, b)` in `B^× × K` in the quotient by the elements `(q, q)`, `q ∈ ℚ^×`, which are
exactly the elements acting trivially on `ℋ^± × B̂^×`, for `B` central simple.

To state all this with Mathlib's orbit spaces and stabilizers, the group `B^× × K` is realised as a
subgroup of `GL₂(ℝ) × B̂^× × B̂^×`, which acts on `ℋ^± × B̂^×` by
`(g, u, k) • (z, b) = (g z, u b k⁻¹)`.

For `K = K_H` the comparison with the model `B^×_+ \ (ℍ × B̂^×) / K_H` of
`LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.AdelicEllipticPoint` is in
`LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.DoubleCosetLevelGroup`.

## Main definitions

* `UpperLowerHalfPlane` (LMFDB `shimcurve`): the space `ℋ^± = ℂ ∖ ℝ`, with the action of `GL₂(ℝ)`
  by Möbius transformations.
* `UpperLowerHalfPlane.ofUpperHalfPlane`: the inclusion `ℍ → ℋ^±`.
* `Subalgebra.shimuraActingHom`: the homomorphism `B^× × B̂^× → GL₂(ℝ) × B̂^× × B̂^×` of the action.
* `Subalgebra.shimuraActingGroup`: the group `B^× × K` acting on `ℋ^± × B̂^×`.
* `Subalgebra.shimuraActing`: the element `(β, k)` of `B^× × K`.
* `Subalgebra.ShimuraDoubleCoset` (LMFDB `shimcurve`): the space `B^× \ (ℋ^± × B̂^×) / K`.
* `Subalgebra.shimuraScalarHom`: the homomorphism `ℚ^× → GL₂(ℝ) × B̂^× × B̂^×`, `q ↦ (q, q, q)`.
* `Subalgebra.shimuraActingScalars`: the elements `(q, q)`, `q ∈ ℚ^×`, of `B^× × K`.
* `Subalgebra.shimuraDoubleCosetStabilizer` (LMFDB `shimcurve.elliptic_points`): the stabilizer
  group of a point of `B^× \ (ℋ^± × B̂^×) / K`.
* `Subalgebra.shimuraDoubleCosetEllipticPoints` (LMFDB `shimcurve.elliptic_points`): the elliptic
  points of `B^× \ (ℋ^± × B̂^×) / K`.

## Main results

* `UpperLowerHalfPlane.ofUpperHalfPlane_smul`: on `ℍ` Mathlib's action of a matrix of positive
  determinant is the action on `ℋ^±`.
* `UpperLowerHalfPlane.det_pos_of_smul_eq`: a matrix mapping a point of `ℍ` into `ℍ` has positive
  determinant.
* `UpperLowerHalfPlane.exists_smul_eq_ofUpperHalfPlane`: a matrix of negative determinant maps the
  lower half-plane into the upper half-plane.
* `UpperLowerHalfPlane.scalar_smul`: the scalar matrices act trivially on `ℋ^±`.
* `AlgHom.exists_unit_det_lt_zero`: a quaternion algebra with a map to `M₂(ℝ)` has units of negative
  norm.
* `Subalgebra.shimuraActingScalars_smul`,
  `Subalgebra.forall_smul_eq_self_iff_mem_shimuraActingScalars`: the elements `(q, q)` are the
  elements of `B^× × K` acting trivially.
* `Subalgebra.natCard_shimuraDoubleCosetStabilizer_smul`: the order of the stabilizer group does not
  depend on the representative.
* `Subalgebra.quotientMk_mem_shimuraDoubleCosetEllipticPoints_iff`: being an elliptic point does not
  depend on the representative.
* `Subalgebra.exists_smul_ofUpperHalfPlane_eq`: every point has a representative in `ℍ × B̂^×`.
* `Subalgebra.natCard_shimuraDoubleCosetStabilizer_eq_natCard_range`: the stabilizer group of
  `[τ, b]`, `τ ∈ ℍ`, is the stabilizer of `τ` in `B^×_+ ∩ b K b⁻¹` modulo `ℚ^×`.
-/

open Algebra Module MulAction UpperHalfPlane

open Matrix hiding mul_smul

/-- The union **`ℋ^± = ℂ ∖ ℝ`** of the complex upper and lower half-planes (LMFDB `shimcurve`), on
which `GL₂(ℝ)` acts by Möbius transformations `z ↦ (a z + b) / (c z + d)`. -/
def UpperLowerHalfPlane : Type :=
  {z : ℂ // z.im ≠ 0}

namespace UpperLowerHalfPlane

variable (g h : GL (Fin 2) ℝ) (z : UpperLowerHalfPlane) (τ : ℍ)

private lemma num_mul {w : ℂ} (hw : w.im ≠ 0) :
    num (g * h) w = num g (num h w / denom h w) * denom h w := by
  have e : num g (num h w / denom h w) * denom h w = g 0 0 * num h w + g 0 1 * denom h w := by
    rw [num, add_mul, mul_assoc, div_mul_cancel₀ _ (denom_ne_zero_of_im h hw)]
  rw [e]
  simp only [num, denom, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Complex.ofReal_add,
    Complex.ofReal_mul]
  ring1

noncomputable instance : SMul (GL (Fin 2) ℝ) UpperLowerHalfPlane where
  smul g z := ⟨num g z.1 / denom g z.1, by
    rw [moebius_im]
    exact div_ne_zero (mul_ne_zero g.det.ne_zero z.2) (normSq_denom_ne_zero g z.2)⟩

lemma coe_smul : (g • z).1 = num g z.1 / denom g z.1 :=
  rfl

noncomputable instance : MulAction (GL (Fin 2) ℝ) UpperLowerHalfPlane where
  one_smul z := Subtype.ext <| by
    rw [coe_smul]
    simp [num, denom]
  mul_smul g h z := Subtype.ext <| by
    rw [coe_smul, coe_smul, coe_smul, num_mul g h z.2, denom_cocycle g h z.2,
      mul_div_mul_right _ _ (denom_ne_zero_of_im h z.2)]

lemma im_smul : (g • z).1.im = g.det.val * z.1.im / Complex.normSq (denom g z.1) :=
  moebius_im g z.1

/-- The inclusion `ℍ → ℋ^±` of the upper half-plane. -/
def ofUpperHalfPlane : UpperLowerHalfPlane :=
  ⟨τ, τ.im_ne_zero⟩

lemma ofUpperHalfPlane_injective : Function.Injective ofUpperHalfPlane := fun _ _ h ↦
  UpperHalfPlane.ext (congrArg Subtype.val h)

variable {g} in
/-- **On the upper half-plane the two actions of a matrix of positive determinant agree**: Mathlib's
action of `GL₂(ℝ)` on `ℍ`, which uses complex conjugation for negative determinants, and the Möbius
transformations of `ℋ^±`. -/
lemma ofUpperHalfPlane_smul (hg : 0 < g.det.val) :
    ofUpperHalfPlane (g • τ) = g • ofUpperHalfPlane τ :=
  Subtype.ext <| coe_smul_of_det_pos hg τ

variable {g τ} in
/-- **A matrix mapping a point of `ℍ` into `ℍ` has positive determinant.** -/
lemma det_pos_of_smul_eq {τ' : ℍ} (hτ : g • ofUpperHalfPlane τ = ofUpperHalfPlane τ') :
    0 < g.det.val := by
  have h₀ : (g • ofUpperHalfPlane τ).1.im = τ'.im :=
    congrArg (fun w : UpperLowerHalfPlane ↦ w.1.im) hτ
  have h₁ : (0 : ℝ) < g.det.val * τ.im / Complex.normSq (denom g τ) :=
    τ'.im_pos.trans_eq (h₀.symm.trans (im_smul g (ofUpperHalfPlane τ)))
  by_contra h₂
  exact (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (not_lt.mp h₂) τ.im_pos.le)
    (Complex.normSq_nonneg _)).not_gt h₁

variable {g z} in
/-- **A matrix of negative determinant maps the lower half-plane into the upper half-plane.** -/
lemma exists_smul_eq_ofUpperHalfPlane (hg : g.det.val < 0) (hz : z.1.im < 0) :
    ∃ τ' : ℍ, g • z = ofUpperHalfPlane τ' := by
  have h : 0 < (g • z).1.im := by
    rw [im_smul]
    exact div_pos (mul_pos_of_neg_of_neg hg hz) (normSq_denom_pos g z.2)
  exact ⟨⟨(g • z).1, h⟩, rfl⟩

/-- **The scalar matrices act trivially on `ℋ^±`.** -/
lemma scalar_smul (u : ℝˣ) : GeneralLinearGroup.scalar (Fin 2) u • z = z :=
  Subtype.ext <| by
    rw [coe_smul]
    simp [num, denom]

end UpperLowerHalfPlane

section Action

variable {A : Type*} [Monoid A] (g g' : GL (Fin 2) ℝ × Aˣ × Aˣ) (p : UpperLowerHalfPlane × Aˣ)

noncomputable instance : SMul (GL (Fin 2) ℝ × Aˣ × Aˣ) (UpperLowerHalfPlane × Aˣ) where
  smul g p := (g.1 • p.1, g.2.1 * p.2 * g.2.2⁻¹)

lemma upperLowerHalfPlane_prod_smul_def : g • p = (g.1 • p.1, g.2.1 * p.2 * g.2.2⁻¹) :=
  rfl

noncomputable instance : MulAction (GL (Fin 2) ℝ × Aˣ × Aˣ) (UpperLowerHalfPlane × Aˣ) where
  one_smul p := Prod.ext (one_smul _ p.1) <| by
    rw [upperLowerHalfPlane_prod_smul_def]
    simp
  mul_smul g g' p := Prod.ext (mul_smul g.1 g'.1 p.1) <| by
    simp [upperLowerHalfPlane_prod_smul_def, mul_assoc]

end Action

variable {G : Type*} [Group G]

private lemma natCard_map_mk_stabilizer_smul {X : Type*} [MulAction G X] (Z : Subgroup G) [Z.Normal]
    (g : G) (p : X) : Nat.card ((stabilizer G (g • p)).map (QuotientGroup.mk' Z)) =
      Nat.card ((stabilizer G p).map (QuotientGroup.mk' Z)) := by
  have h : (stabilizer G (g • p)).map (QuotientGroup.mk' Z) =
      ((stabilizer G p).map (QuotientGroup.mk' Z)).map
        (MulAut.conj (QuotientGroup.mk' Z g)).toMonoidHom := by
    rw [stabilizer_smul_eq_stabilizer_map_conj, Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [h]
  exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ (MulAut.conj _).injective).toEquiv.symm

private lemma natCard_range_eq_of_ker_eq {T T' : Type*} [Group T] [Group T'] (φ : G →* T)
    (ψ : G →* T') (h : φ.ker = ψ.ker) : Nat.card φ.range = Nat.card ψ.range :=
  Nat.card_congr ((QuotientGroup.quotientKerEquivRange φ).symm.toEquiv.trans
    ((QuotientGroup.quotientMulEquivOfEq h).toEquiv.trans
      (QuotientGroup.quotientKerEquivRange ψ).toEquiv))

private lemma natCard_map_mk_stabilizer_eq {S T X : Type*} [Group S] [Group T] [MulAction G X]
    (Z : Subgroup G) [Z.Normal] (φ : S →* G) (ψ : S →* T) (p : X)
    (hrange : φ.range = stabilizer G p) (hker : ∀ s, φ s ∈ Z ↔ ψ s = 1) :
    Nat.card ((stabilizer G p).map (QuotientGroup.mk' Z)) = Nat.card ψ.range := by
  rw [← hrange, ← MonoidHom.range_comp]
  refine natCard_range_eq_of_ker_eq _ _ <| Subgroup.ext fun s ↦ ?_
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← hker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff]

namespace AlgHom

variable {B : Type*} [Ring B] [Algebra ℚ B] [IsCentral ℚ B] [IsSimpleRing B]
  (ι : B →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ)

/-- **A quaternion algebra `B` over `ℚ` with a `ℚ`-algebra map `ι : B → M₂(ℝ)` has units of negative
norm**: an element of negative norm (`AlgHom.exists_det_lt_zero`) is not a zero divisor, `ι` being
injective, hence a unit, `B` being Artinian. -/
lemma exists_unit_det_lt_zero (hB : finrank ℚ B = 4) : ∃ β : Bˣ, (ι β).det < 0 := by
  rcases ι.exists_det_lt_zero hB with ⟨β, hβ⟩
  have : Module.Finite ℚ B := Module.finite_of_finrank_pos (by omega)
  have : IsArtinianRing B := IsArtinianRing.of_finite ℚ B
  have hu : IsUnit (ι β) := (isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hβ.ne)
  rcases IsArtinianRing.isUnit_of_mem_nonZeroDivisors (comap_nonZeroDivisors_le_of_injective
    ι.toRingHom.injective hu.mem_nonZeroDivisors) with ⟨u, rfl⟩
  exact ⟨u, hβ⟩

end AlgHom

namespace Subalgebra

open UpperLowerHalfPlane

variable {B : Type*} [Ring B] [Algebra ℚ B] {O : Subalgebra ℤ B} (hO : O.IsQuaternionOrder)
  (ι : B →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (K : Subgroup O.FiniteAdelicAlgebraˣ)
  (p : UpperLowerHalfPlane × O.FiniteAdelicAlgebraˣ)

/-- The homomorphism `B^× × B̂^× → GL₂(ℝ) × B̂^× × B̂^×`, `(β, k) ↦ (ι(β), β, k)`, describing the
action of `B^× × B̂^×` on `ℋ^± × B̂^×`. -/
noncomputable def shimuraActingHom :
    Bˣ × O.FiniteAdelicAlgebraˣ →* GL (Fin 2) ℝ × O.FiniteAdelicAlgebraˣ × O.FiniteAdelicAlgebraˣ :=
  ((Units.map ι.toMonoidHom).comp (MonoidHom.fst _ _)).prod
    (((Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom).comp (MonoidHom.fst _ _)).prod
      (MonoidHom.snd _ _))

/-- The group `B^× × K` acting on `ℋ^± × B̂^×` by `(β, k) • (z, b) = (β z, β b k⁻¹)` (LMFDB
`shimcurve`), for a subgroup `K` of `B̂^×`, as a subgroup of `GL₂(ℝ) × B̂^× × B̂^×`, which acts by
`(g, u, k) • (z, b) = (g z, u b k⁻¹)`. -/
noncomputable def shimuraActingGroup :
    Subgroup (GL (Fin 2) ℝ × O.FiniteAdelicAlgebraˣ × O.FiniteAdelicAlgebraˣ) :=
  (Subgroup.prod ⊤ K).map (shimuraActingHom hO ι)

variable {K} in
/-- The element `(β, k)` of the group `B^× × K` acting on `ℋ^± × B̂^×`. -/
noncomputable def shimuraActing (β : Bˣ) {k : O.FiniteAdelicAlgebraˣ} (hk : k ∈ K) :
    shimuraActingGroup hO ι K :=
  ⟨shimuraActingHom hO ι (β, k), (β, k), ⟨trivial, hk⟩, rfl⟩

variable {K} in
lemma shimuraActing_smul (β : Bˣ) {k : O.FiniteAdelicAlgebraˣ} (hk : k ∈ K) :
    shimuraActing hO ι β hk • p = (Units.map ι.toMonoidHom β • p.1,
      Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom β * p.2 * k⁻¹) :=
  rfl

/-- The **double coset space `B^× \ (ℋ^± × B̂^×) / K`** (LMFDB `shimcurve`) of a subgroup `K` of
`B̂^×`: the orbits of `B^× × K` acting on `ℋ^± × B̂^×` by `(β, k) • (z, b) = (β z, β b k⁻¹)`, the
group `B^×` acting on `ℋ^± = ℂ ∖ ℝ` by Möbius transformations through `ι`. -/
abbrev ShimuraDoubleCoset : Type _ :=
  orbitRel.Quotient (shimuraActingGroup hO ι K) (UpperLowerHalfPlane × O.FiniteAdelicAlgebraˣ)

/-- The homomorphism `ℚ^× → GL₂(ℝ) × B̂^× × B̂^×`, `q ↦ (q, q, q)`. -/
noncomputable def shimuraScalarHom :
    ℚˣ →* GL (Fin 2) ℝ × O.FiniteAdelicAlgebraˣ × O.FiniteAdelicAlgebraˣ :=
  (shimuraActingHom hO ι).comp <| MonoidHom.prod (Units.map (algebraMap ℚ B : ℚ →* B))
    (Units.map ((O.toFiniteAdelicAlgebra hO).comp (algebraMap ℚ B)).toMonoidHom)

lemma shimuraScalarHom_mem_center (q : ℚˣ) : shimuraScalarHom hO ι q ∈
    Subgroup.center (GL (Fin 2) ℝ × O.FiniteAdelicAlgebraˣ × O.FiniteAdelicAlgebraˣ) := by
  refine Subgroup.mem_center_iff.mpr fun g ↦ Prod.ext ?_ (Prod.ext ?_ ?_)
  · have h : ((shimuraScalarHom hO ι q).1 : Matrix (Fin 2) (Fin 2) ℝ) = algebraMap ℚ _ (q : ℚ) :=
      ι.commutes _
    refine Units.ext ?_
    rw [Prod.fst_mul, Prod.fst_mul, Units.val_mul, Units.val_mul, h]
    exact (Algebra.commutes (q : ℚ) _).symm
  · exact Units.ext (commute_toFiniteAdelicAlgebra_algebraMap hO q _).eq.symm
  · exact Units.ext (commute_toFiniteAdelicAlgebra_algebraMap hO q _).eq.symm

/-- The elements `(q, q)`, `q ∈ ℚ^×`, of the group `B^× × K` acting on `ℋ^± × B̂^×`. They act
trivially (`Subalgebra.shimuraActingScalars_smul`), and they are the only elements doing so when `B`
is central simple (`Subalgebra.forall_smul_eq_self_iff_mem_shimuraActingScalars`). -/
noncomputable def shimuraActingScalars : Subgroup (shimuraActingGroup hO ι K) :=
  (shimuraScalarHom hO ι).range.subgroupOf _

instance : (shimuraActingScalars hO ι K).Normal :=
  (Subgroup.normal_of_le_center <| by
    rintro _ ⟨q, rfl⟩
    exact shimuraScalarHom_mem_center hO ι q).subgroupOf _

lemma algebraMap_smul (q : ℚˣ) (z : UpperLowerHalfPlane) :
    Units.map ι.toMonoidHom (Units.map (algebraMap ℚ B : ℚ →* B) q) • z = z := by
  have h : Units.map ι.toMonoidHom (Units.map (algebraMap ℚ B : ℚ →* B) q) =
      GeneralLinearGroup.scalar (Fin 2) (Units.map (algebraMap ℚ ℝ) q) := by
    ext i j
    simp
    rfl
  rw [h]
  exact UpperLowerHalfPlane.scalar_smul z _

lemma algebraMap_inv_smul (q : ℚˣ) (z : UpperLowerHalfPlane) :
    Units.map ι.toMonoidHom (Units.map (algebraMap ℚ B : ℚ →* B) q)⁻¹ • z = z := by
  rw [map_inv, inv_smul_eq_iff, algebraMap_smul]

/-- **The elements `(q, q)`, `q ∈ ℚ^×`, of `B^× × K` act trivially on `ℋ^± × B̂^×`.** -/
lemma shimuraActingScalars_smul {g : shimuraActingGroup hO ι K}
    (hg : g ∈ shimuraActingScalars hO ι K) : g • p = p := by
  rcases hg with ⟨q, hq⟩
  have hq' : (g : GL (Fin 2) ℝ × O.FiniteAdelicAlgebraˣ × O.FiniteAdelicAlgebraˣ) =
      shimuraScalarHom hO ι q :=
    hq.symm
  have h₁ : (g : GL (Fin 2) ℝ × O.FiniteAdelicAlgebraˣ × O.FiniteAdelicAlgebraˣ).1 =
      Units.map ι.toMonoidHom (Units.map (algebraMap ℚ B : ℚ →* B) q) := by
    rw [hq']
    rfl
  have h₂ : (g : GL (Fin 2) ℝ × O.FiniteAdelicAlgebraˣ × O.FiniteAdelicAlgebraˣ).2.1 =
      (g : GL (Fin 2) ℝ × O.FiniteAdelicAlgebraˣ × O.FiniteAdelicAlgebraˣ).2.2 := by
    rw [hq']
    rfl
  have h₃ : Commute (g : GL (Fin 2) ℝ × O.FiniteAdelicAlgebraˣ × O.FiniteAdelicAlgebraˣ).2.1 p.2 :=
    Units.ext <| by
      rw [hq']
      exact commute_toFiniteAdelicAlgebra_algebraMap hO q _
  refine Prod.ext ((congrArg (· • p.1) h₁).trans (algebraMap_smul ι q p.1)) ?_
  show (g : GL (Fin 2) ℝ × O.FiniteAdelicAlgebraˣ × O.FiniteAdelicAlgebraˣ).2.1 * p.2 *
    (g : GL (Fin 2) ℝ × O.FiniteAdelicAlgebraˣ × O.FiniteAdelicAlgebraˣ).2.2⁻¹ = p.2
  rw [← h₂, h₃.eq, mul_inv_cancel_right]

/-- The **stabilizer group** (LMFDB `shimcurve.elliptic_points`) of the point `[z, b]` of the double
coset space `B^× \ (ℋ^± × B̂^×) / K`: the image of the stabilizer of `(z, b)` in `B^× × K` in the
quotient by the group of the elements `(q, q)`, `q ∈ ℚ^×`, which act trivially. -/
noncomputable def shimuraDoubleCosetStabilizer :
    Subgroup (shimuraActingGroup hO ι K ⧸ shimuraActingScalars hO ι K) :=
  (stabilizer (shimuraActingGroup hO ι K) p).map (QuotientGroup.mk' _)

/-- **The order of the stabilizer group does not depend on the representative**: the stabilizers of
`g • p` and `p` are conjugate by `g`. -/
lemma natCard_shimuraDoubleCosetStabilizer_smul (g : shimuraActingGroup hO ι K) :
    Nat.card (shimuraDoubleCosetStabilizer hO ι K (g • p)) =
      Nat.card (shimuraDoubleCosetStabilizer hO ι K p) :=
  natCard_map_mk_stabilizer_smul _ g p

/-- The **elliptic points** (LMFDB `shimcurve.elliptic_points`) of the double coset space
`B^× \ (ℋ^± × B̂^×) / K`, for a subgroup `K` of `B̂^×`: the points with a nontrivial stabilizer
group. -/
noncomputable def shimuraDoubleCosetEllipticPoints : Set (ShimuraDoubleCoset hO ι K) :=
  Quotient.mk _ '' {p | shimuraDoubleCosetStabilizer hO ι K p ≠ ⊥}

/-- **Being an elliptic point is a property of the point**, not of the representative. -/
lemma quotientMk_mem_shimuraDoubleCosetEllipticPoints_iff :
    (Quotient.mk _ p : ShimuraDoubleCoset hO ι K) ∈ shimuraDoubleCosetEllipticPoints hO ι K ↔
      shimuraDoubleCosetStabilizer hO ι K p ≠ ⊥ := by
  refine ⟨?_, fun h ↦ ⟨p, h, rfl⟩⟩
  rintro ⟨p', hp', h⟩ hp
  rcases Quotient.exact h with ⟨g, rfl⟩
  refine hp' (Subgroup.card_eq_one.mp ?_)
  rw [natCard_shimuraDoubleCosetStabilizer_smul, Subgroup.card_eq_one.mpr hp]

variable {K}

variable [IsCentral ℚ B] [IsSimpleRing B] in
/-- **The elements of `B^× × K` acting trivially on `ℋ^± × B̂^×` are the `(q, q)`, `q ∈ ℚ^×`**, for
`B` central simple over `ℚ`: `ι(β)` fixing every point of `ℍ` is a scalar matrix, so `β` is central,
`ι` being injective, hence rational, and `β k⁻¹ = 1` at `b = 1`. -/
lemma forall_smul_eq_self_iff_mem_shimuraActingScalars {g : shimuraActingGroup hO ι K} :
    (∀ p : UpperLowerHalfPlane × O.FiniteAdelicAlgebraˣ, g • p = p) ↔
      g ∈ shimuraActingScalars hO ι K := by
  refine ⟨fun h ↦ ?_, fun hg p ↦ shimuraActingScalars_smul hO ι K p hg⟩
  rcases g with ⟨_, ⟨β, k⟩, ⟨_, hk⟩, rfl⟩
  have h₁ (τ : ℍ) : Units.map ι.toMonoidHom β • ofUpperHalfPlane τ = ofUpperHalfPlane τ :=
    congrArg Prod.fst (h (ofUpperHalfPlane τ, 1))
  have h₂ : Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom β * 1 * k⁻¹ = 1 :=
    congrArg Prod.snd (h (ofUpperHalfPlane UpperHalfPlane.I, 1))
  have hτ (τ : ℍ) : Units.map ι.toMonoidHom β • τ = τ := ofUpperHalfPlane_injective <|
    (ofUpperHalfPlane_smul τ (det_pos_of_smul_eq (h₁ τ))).trans (h₁ τ)
  rcases GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp
    (forall_smul_eq_self_iff_mem_center.mp hτ) with ⟨r, hr⟩
  have hscal : ι (β : B) = scalar (Fin 2) r := hr.symm
  have hcomm (x : B) : x * β = β * x := ι.toRingHom.injective <| by
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_mul, map_mul, hscal]
    exact (scalar_commute r (Commute.all r) (ι x)).eq.symm
  have hmem : (β : B) ∈ (⊥ : Subalgebra ℚ B) :=
    IsCentral.center_eq_bot ℚ B ▸ Subalgebra.mem_center_iff.mpr hcomm
  rcases mem_bot.mp hmem with ⟨q, hq⟩
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact Units.ne_zero _ (hq.symm.trans (map_zero _))
  have hβ : β = Units.map (algebraMap ℚ B : ℚ →* B) (Units.mk0 q hq0) := Units.ext hq.symm
  have hkβ : k = Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom β := by
    rw [mul_one, mul_inv_eq_one] at h₂
    exact h₂.symm
  subst hkβ
  subst hβ
  exact ⟨Units.mk0 q hq0, rfl⟩

variable (K) [IsCentral ℚ B] [IsSimpleRing B] in
private lemma exists_smul_ofUpperHalfPlane_eq_of_im_neg (hB : finrank ℚ B = 4) (hz : p.1.1.im < 0) :
    ∃ (g : shimuraActingGroup hO ι K) (τ : ℍ) (b : O.FiniteAdelicAlgebraˣ),
      g • (ofUpperHalfPlane τ, b) = p := by
  rcases ι.exists_unit_det_lt_zero hB with ⟨β, hβ⟩
  rcases exists_smul_eq_ofUpperHalfPlane (g := Units.map ι.toMonoidHom β) hβ hz with ⟨τ', hτ'⟩
  refine ⟨(shimuraActing hO ι β (one_mem K))⁻¹, τ',
    Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom β * p.2 * 1⁻¹, inv_smul_eq_iff.mpr ?_⟩
  rw [shimuraActing_smul, hτ']

variable (K) in
private lemma exists_smul_ofUpperHalfPlane_eq_of_im_pos (hz : 0 < p.1.1.im) :
    ∃ (g : shimuraActingGroup hO ι K) (τ : ℍ) (b : O.FiniteAdelicAlgebraˣ),
      g • (ofUpperHalfPlane τ, b) = p :=
  ⟨1, ⟨p.1.1, hz⟩, p.2, one_smul _ p⟩

variable (K) [IsCentral ℚ B] [IsSimpleRing B] in
/-- **Every point of `B^× \ (ℋ^± × B̂^×) / K` has a representative in `ℍ × B̂^×`**, for a quaternion
algebra `B`: a unit of negative norm (`AlgHom.exists_unit_det_lt_zero`) maps the lower half-plane
into the upper half-plane. -/
lemma exists_smul_ofUpperHalfPlane_eq (hB : finrank ℚ B = 4) :
    ∃ (g : shimuraActingGroup hO ι K) (τ : ℍ) (b : O.FiniteAdelicAlgebraˣ),
      g • (ofUpperHalfPlane τ, b) = p :=
  (lt_or_gt_of_ne p.1.2).elim (exists_smul_ofUpperHalfPlane_eq_of_im_neg hO ι K p hB)
    (exists_smul_ofUpperHalfPlane_eq_of_im_pos hO ι K p)

variable (τ : ℍ) (b : O.FiniteAdelicAlgebraˣ) {S T : Type*} [Group S] [Group T] (t : S →* Bˣ)
  (ψ : S →* T)

/-- The homomorphism `β ↦ (ι(β), β, b⁻¹ β b)`, whose values at the elements of `B^×` fixing `τ` are
the elements of `B^× × B̂^×` fixing `(τ, b)`. -/
private noncomputable def stabilizerGraph :
    Bˣ →* GL (Fin 2) ℝ × O.FiniteAdelicAlgebraˣ × O.FiniteAdelicAlgebraˣ :=
  (Units.map ι.toMonoidHom).prod ((Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom).prod
    ((MulAut.conj b⁻¹).toMonoidHom.comp (Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom)))

variable {t} in
/-- The homomorphism `s ↦ (t s, b⁻¹ t(s) b)` to `B^× × K`, for `t : S → B^×` with
`b⁻¹ t(s) b ∈ K`. -/
private noncomputable def stabilizerToActing (hK : ∀ s, (MulAut.conj b⁻¹).toMonoidHom
      (Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom (t s)) ∈ K) :
    S →* shimuraActingGroup hO ι K :=
  ((stabilizerGraph hO ι b).comp t).codRestrict _ fun s ↦ ⟨(_, _), ⟨trivial, hK s⟩, rfl⟩

variable {t} in
private lemma range_stabilizerToActing (hK : ∀ s, (MulAut.conj b⁻¹).toMonoidHom
      (Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom (t s)) ∈ K)
    (hpos : ∀ s, 0 < (GeneralLinearGroup.det (Units.map ι.toMonoidHom (t s))).val)
    (hfix : ∀ s, Units.map ι.toMonoidHom (t s) • τ = τ)
    (hsurj : ∀ β : Bˣ, 0 < (GeneralLinearGroup.det (Units.map ι.toMonoidHom β)).val →
      Units.map ι.toMonoidHom β • τ = τ → (MulAut.conj b⁻¹).toMonoidHom
        (Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom β) ∈ K → ∃ s, t s = β) :
    (stabilizerToActing hO ι b hK).range =
      stabilizer (shimuraActingGroup hO ι K) (ofUpperHalfPlane τ, b) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨s, rfl⟩
    refine mem_stabilizer_iff.mpr (Prod.ext ?_ ?_)
    · exact (ofUpperHalfPlane_smul τ (hpos s)).symm.trans (congrArg ofUpperHalfPlane (hfix s))
    · show Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom (t s) * b *
        (b⁻¹ * Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom (t s) * b⁻¹⁻¹)⁻¹ = b
      group
  · rintro ⟨_, ⟨β, k⟩, ⟨_, hk⟩, rfl⟩ hg
    have h₁ : Units.map ι.toMonoidHom β • ofUpperHalfPlane τ = ofUpperHalfPlane τ :=
      congrArg Prod.fst hg
    have h₂ : Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom β * b * k⁻¹ = b :=
      congrArg Prod.snd hg
    have hdet : 0 < (GeneralLinearGroup.det (Units.map ι.toMonoidHom β)).val :=
      det_pos_of_smul_eq h₁
    have hk' : k = (MulAut.conj b⁻¹).toMonoidHom
        (Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom β) := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, mul_assoc]
      exact eq_inv_mul_of_mul_eq (mul_inv_eq_iff_eq_mul.mp h₂).symm
    rcases hsurj β hdet (ofUpperHalfPlane_injective <| (ofUpperHalfPlane_smul τ hdet).trans h₁)
      (hk' ▸ hk) with ⟨s, rfl⟩
    refine ⟨s, Subtype.ext ?_⟩
    exact Prod.ext rfl (Prod.ext rfl hk'.symm)

variable {t} in
private lemma stabilizerToActing_mem_iff [IsSimpleRing B] (hK : ∀ s, (MulAut.conj b⁻¹).toMonoidHom
      (Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom (t s)) ∈ K) (s : S) :
    stabilizerToActing hO ι b hK s ∈ shimuraActingScalars hO ι K ↔
      t s ∈ (Units.map (algebraMap ℚ B : ℚ →* B)).range := by
  rw [shimuraActingScalars, Subgroup.mem_subgroupOf, MonoidHom.mem_range, MonoidHom.mem_range]
  refine exists_congr fun q ↦ ⟨fun hq ↦ ?_, fun hq ↦ ?_⟩
  · have h : Units.map ι.toMonoidHom (Units.map (algebraMap ℚ B : ℚ →* B) q) =
        Units.map ι.toMonoidHom (t s) :=
      congrArg Prod.fst hq
    exact Units.ext <| ι.toRingHom.injective <| congrArg Units.val h
  · have hc : Commute (Units.map ((O.toFiniteAdelicAlgebra hO).comp
        (algebraMap ℚ B)).toMonoidHom q) b⁻¹ :=
      Units.ext (commute_toFiniteAdelicAlgebra_algebraMap hO q _)
    refine Prod.ext (congrArg (Units.map ι.toMonoidHom) hq) (Prod.ext
      (congrArg (Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom) hq) ?_)
    show Units.map ((O.toFiniteAdelicAlgebra hO).comp (algebraMap ℚ B)).toMonoidHom q =
      b⁻¹ * Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom (t s) * b⁻¹⁻¹
    rw [← hq, ← map_toFiniteAdelicAlgebra_comp_algebraMap, ← hc.eq, mul_inv_cancel_right]

variable {t ψ} in
/-- **The stabilizer group of `[τ, b]`, `τ ∈ ℍ`, is the stabilizer of `τ` in `B^×_+ ∩ b K b⁻¹`
modulo `ℚ^×`**, for `B` simple: if `t : S → B^×` has image this stabilizer, and `ψ : S → T` has
kernel the elements sent to `ℚ^×`, then the stabilizer group has the order of the image of `ψ`. The
stabilizer of `(τ, b)` in `B^× × K` consists of the `(β, b⁻¹ β b)` for `β` in the stabilizer of `τ`
in `B^×_+ ∩ b K b⁻¹`. -/
lemma natCard_shimuraDoubleCosetStabilizer_eq_natCard_range [IsSimpleRing B]
    (hK : ∀ s, (MulAut.conj b⁻¹).toMonoidHom
      (Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom (t s)) ∈ K)
    (hpos : ∀ s, 0 < (GeneralLinearGroup.det (Units.map ι.toMonoidHom (t s))).val)
    (hfix : ∀ s, Units.map ι.toMonoidHom (t s) • τ = τ)
    (hsurj : ∀ β : Bˣ, 0 < (GeneralLinearGroup.det (Units.map ι.toMonoidHom β)).val →
      Units.map ι.toMonoidHom β • τ = τ → (MulAut.conj b⁻¹).toMonoidHom
        (Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom β) ∈ K → ∃ s, t s = β)
    (hker : ∀ s, ψ s = 1 ↔ t s ∈ (Units.map (algebraMap ℚ B : ℚ →* B)).range) :
    Nat.card (shimuraDoubleCosetStabilizer hO ι K (ofUpperHalfPlane τ, b)) = Nat.card ψ.range :=
  natCard_map_mk_stabilizer_eq _ (stabilizerToActing hO ι b hK) ψ _
    (range_stabilizerToActing hO ι τ b hK hpos hfix hsurj) fun s ↦
      (stabilizerToActing_mem_iff hO ι b hK s).trans (hker s).symm

end Subalgebra
