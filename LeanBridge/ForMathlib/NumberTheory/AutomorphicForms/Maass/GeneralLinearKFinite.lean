import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.GeneralLinear

/-!
# Non-spherical Maass forms on `GL(n)`

An automorphic form on `GL_n(ℝ)` for a subgroup `Γ` of `GL_n(ℤ)` is a smooth function that is left
`Γ`-invariant, right `K`-finite for the maximal compact subgroup `K = O(n)`, `Z(U(gl_n))`-finite
and of moderate growth; a Maass form (LMFDB `mf.maass`) is such a form that is moreover an
eigenfunction of the Casimir element of `U(gl_n)`. The spherical Maass forms of
`Matrix.GeneralLinearGroup.IsMaassForm` are those that are right `O(n)`-invariant; here the
`K`-type is arbitrary (for instance the Maass forms of nonzero weight on `GL(2)`), and the
`Z(U(gl_n))`-finiteness, which for `n ≥ 3` does not follow from being a Casimir eigenfunction, is
part of the definition. As in `Matrix.GeneralLinearGroup.IsMaassForm`, functions on `GL_n(ℝ)` are
given on all square real matrices, the Lie algebra `gl_n(ℝ)` and so `U(gl_n)` act on the smooth ones
by left-invariant differential operators, and the forms are invariant under the positive scalars.

## Main definitions

* `Matrix.GeneralLinearGroup.rightTranslate`: the right translate `g ↦ φ(gk)`.
* `Matrix.GeneralLinearGroup.IsOrthogonalFinite`: right `O(n)`-finiteness.
* `Matrix.GeneralLinearGroup.IsCenterFinite`: `Z(U(gl_n))`-finiteness.
* `Matrix.GeneralLinearGroup.IsAutomorphicForm`: automorphic forms on `GL_n(ℝ)`.
* `Matrix.GeneralLinearGroup.IsCasimirEigenfunction`: eigenfunctions of the Casimir element.
* `Matrix.GeneralLinearGroup.IsKFiniteMaassForm` (LMFDB `mf.maass`): Maass forms on `GL_n`.

## Main results

* `Matrix.GeneralLinearGroup.isCenterFinite_of_forall_lie_eq_zero`,
  `Matrix.GeneralLinearGroup.isCenterFinite_const`: smooth functions killed by `gl_n(ℝ)`, such as
  the constants, are `Z(U(gl_n))`-finite.
* `Matrix.GeneralLinearGroup.isKFiniteMaassForm_const`: constants are Maass forms of eigenvalue
  `0`.
* `Matrix.GeneralLinearGroup.isKFiniteMaassForm_sign_det`,
  `Matrix.GeneralLinearGroup.not_isMaassForm_sign_det`: `g ↦ sign(det g)` is a non-spherical Maass
  form of eigenvalue `0` for every subgroup of `SL_n(ℤ)`.
* `Matrix.GeneralLinearGroup.IsCasimirEigenfunction.eigenvalue_eq`: the Casimir eigenvalue of a
  nonzero eigenfunction is unique.
* `Matrix.GeneralLinearGroup.IsMaassForm.isKFiniteMaassForm`,
  `Matrix.GeneralLinearGroup.IsKFiniteMaassForm.isMaassForm`: the spherical Maass forms that are
  `Z(U(gl_n))`-finite are exactly the right `O(n)`-invariant Maass forms.
-/

open Module TauCeti

open scoped ContDiff

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] (Γ : Subgroup (GL n ℤ)) (φ : (n → n → ℝ) → ℂ)
  (eigenvalue : ℂ) {a b : ℂ} {g : n → n → ℝ} (c : ℂ)

/-- The **right translate** `g ↦ φ(gk)` of a function `φ` on `GL_n(ℝ)`, given on all square real
matrices, by a square matrix `k`. -/
def rightTranslate (k : Matrix n n ℝ) : (n → n → ℝ) → ℂ :=
  fun g ↦ φ (of.symm (of g * k))

/-- A function `φ` on `GL_n(ℝ)` is **right `O(n)`-finite** (`K`-finite for the maximal compact
subgroup `K = O(n)`) if its right translates by the orthogonal group span a finite-dimensional
complex vector space. Right `O(n)`-invariant functions, the spherical ones, are `O(n)`-finite. -/
def IsOrthogonalFinite : Prop :=
  FiniteDimensional ℂ <| Submodule.span ℂ <| Set.range fun k : orthogonalGroup n ℝ ↦
    rightTranslate φ k

/-- A function `φ` on `GL_n(ℝ)` is **`Z(U(gl_n))`-finite** if it is smooth and the elements of the
centre `Z(U(gl_n))` of the universal enveloping algebra of `gl_n(ℝ)`, acting on smooth functions
by left-invariant differential operators, carry it into a finite-dimensional real vector space;
equivalently, it is annihilated by an ideal of finite codimension of `Z(U(gl_n))`. -/
def IsCenterFinite : Prop :=
  ∃ hφ : φ ∈ smoothFunctions n, FiniteDimensional ℝ <| Submodule.span ℝ <| Set.range
    fun z : Subalgebra.center ℝ (UniversalEnvelopingAlgebra ℝ (Matrix n n ℝ)) ↦
      UniversalEnvelopingAlgebra.representation ℝ (Matrix n n ℝ) (smoothFunctions n) z ⟨φ, hφ⟩

/-- A function `φ` on `GL_n(ℝ)`, given on all square real matrices, is an **automorphic form** for
a subgroup `Γ` of `GL_n(ℤ)` (such as `SL_n(ℤ)`) if it is left `Γ`-invariant, right `O(n)`-finite,
smooth and `Z(U(gl_n))`-finite (`IsCenterFinite`, which includes smoothness), invariant under the
positive scalars (a trivial central character on `ℝ_{>0}`), and of moderate growth (bounded by a
power of `‖g‖ + ‖g⁻¹‖`). -/
def IsAutomorphicForm : Prop :=
  (∀ γ ∈ Γ, ∀ g, φ (of.symm ((γ : Matrix n n ℤ).map (↑) * of g)) = φ g) ∧
    IsOrthogonalFinite φ ∧ IsCenterFinite φ ∧ (∀ t : ℝ, 0 < t → ∀ g, φ (t • g) = φ g) ∧
    ∃ (C : ℝ) (N : ℕ), ∀ g ∈ glSet n, ‖φ g‖ ≤ C * (‖g‖ + ‖of.symm (of g)⁻¹‖) ^ N

/-- A function `φ` on `GL_n(ℝ)` is an **eigenfunction of the Casimir element** `Σ_{i,j} E_ij E_ji`
of `U(gl_n)` (Tau Ceti's `TauCeti.glCasimir`) with eigenvalue `λ` if it is smooth and the Casimir
operator `casimirOperator` carries it to `λ φ` on `GL_n(ℝ)`. -/
def IsCasimirEigenfunction : Prop :=
  ∃ hφ : φ ∈ smoothFunctions n,
    ∀ g ∈ glSet n, (casimirOperator ⟨φ, hφ⟩ : (n → n → ℝ) → ℂ) g = eigenvalue * φ g

/-- A function `φ` on `GL_n(ℝ)`, given on all square real matrices, is a **Maass form** (LMFDB
`mf.maass`) for a subgroup `Γ` of `GL_n(ℤ)` with Casimir eigenvalue `λ` if it is an automorphic
form for `Γ` (`IsAutomorphicForm`: left `Γ`-invariant, right `O(n)`-finite, `Z(U(gl_n))`-finite,
invariant under the positive scalars, of moderate growth) and an eigenfunction of the Casimir
element of `U(gl_n)` with eigenvalue `λ`. Its `K`-type is arbitrary: the right `O(n)`-invariant
ones are the spherical Maass forms of `IsMaassForm` (`IsMaassForm.isKFiniteMaassForm`,
`IsKFiniteMaassForm.isMaassForm`), and `g ↦ sign(det g)` is a non-spherical one
(`isKFiniteMaassForm_sign_det`, `not_isMaassForm_sign_det`). The knowl's "not holomorphic"
contrasts the Casimir equation with the Cauchy–Riemann equations rather than adding a condition:
for `n ≥ 3` no automorphic form on `GL_n(ℝ)` comes from a holomorphic function, and on `GL(2)` the
definition, like the LMFDB's Maass forms of weight `k` (`UpperHalfPlane.IsMaassFormOfWeight`),
does not exclude the lifts of holomorphic forms. -/
def IsKFiniteMaassForm : Prop :=
  IsAutomorphicForm Γ φ ∧ IsCasimirEigenfunction φ eigenvalue

variable {φ eigenvalue} in
/-- **The Casimir eigenvalue of a nonzero eigenfunction is unique**: if `φ(g) ≠ 0` at some
`g ∈ GL_n(ℝ)`, the eigenvalue equation at `g` determines `λ`. -/
lemma IsCasimirEigenfunction.eigenvalue_eq (ha : IsCasimirEigenfunction φ a)
    (hb : IsCasimirEigenfunction φ b) (hg : g ∈ glSet n) (hφ : φ g ≠ 0) : a = b :=
  mul_right_cancel₀ hφ <| (ha.snd g hg).symm.trans <| hb.snd g hg

/-- **Functions killed by `gl_n(ℝ)` are `Z(U(gl_n))`-finite**: if every left-invariant derivative
kills a smooth function `F`, then `U(gl_n)` carries `F` into the line it spans. -/
lemma isCenterFinite_of_forall_lie_eq_zero (F : smoothFunctions n)
    (hF : ∀ X : Matrix n n ℝ, ⁅X, F⁆ = 0) : IsCenterFinite (F : (n → n → ℝ) → ℂ) := by
  have h (u : UniversalEnvelopingAlgebra ℝ (Matrix n n ℝ)) :
      UniversalEnvelopingAlgebra.representation ℝ (Matrix n n ℝ) (smoothFunctions n) u F ∈
        ℝ ∙ F := by
    induction u using UniversalEnvelopingAlgebra.induction_ι with
    | ι X =>
      rw [UniversalEnvelopingAlgebra.representation_ι, LieModule.toEnd_apply_apply, hF X]
      exact zero_mem _
    | algebraMap r =>
      rw [AlgHom.commutes, Module.algebraMap_end_apply]
      exact Submodule.smul_mem _ r <| Submodule.mem_span_singleton_self _
    | add a b ha hb =>
      rw [map_add, LinearMap.add_apply]
      exact add_mem ha hb
    | mul a b ha hb =>
      rcases Submodule.mem_span_singleton.mp hb with ⟨r, hr⟩
      rw [map_mul, End.mul_apply, ← hr, map_smul]
      exact Submodule.smul_mem _ r ha
  exact ⟨F.2, Submodule.finiteDimensional_of_le <| Submodule.span_le.mpr <|
    Set.range_subset_iff.mpr fun z ↦ h z⟩

/-- **Constants are `Z(U(gl_n))`-finite**: every element of `gl_n(ℝ)` kills a constant. -/
lemma isCenterFinite_const : IsCenterFinite fun _ : n → n → ℝ ↦ c :=
  isCenterFinite_of_forall_lie_eq_zero ⟨fun _ ↦ c, contDiffOn_const⟩ fun _ ↦
    Subtype.ext <| funext fun _ ↦ by simp [coe_bracket, leftInvariantDeriv]

lemma isOrthogonalFinite_of_forall
    (hK : ∀ k ∈ orthogonalGroup n ℝ, ∀ g, φ (of.symm (of g * k)) = φ g) : IsOrthogonalFinite φ := by
  have h : Set.range (fun k : orthogonalGroup n ℝ ↦ rightTranslate φ k) ⊆ {φ} :=
    Set.range_subset_iff.mpr fun k ↦ funext fun g ↦ hK k k.2 g
  exact FiniteDimensional.span_of_finite ℂ <| (Set.finite_singleton φ).subset h

variable {Γ φ eigenvalue} in
/-- **Spherical Maass forms are Maass forms**: a right `O(n)`-invariant Maass form of
`IsMaassForm` that is `Z(U(gl_n))`-finite is a Maass form of `IsKFiniteMaassForm`. -/
lemma IsMaassForm.isKFiniteMaassForm (h : IsMaassForm Γ φ eigenvalue) (hZ : IsCenterFinite φ) :
    IsKFiniteMaassForm Γ φ eigenvalue := by
  rcases h with ⟨hφ, hΓ, hK, ht, hC, hc⟩
  exact ⟨⟨hΓ, isOrthogonalFinite_of_forall φ hK, hZ, ht, hC⟩, hφ, hc⟩

variable {Γ φ eigenvalue} in
/-- **Right `O(n)`-invariant Maass forms are spherical**: a Maass form of `IsKFiniteMaassForm`
that is right `O(n)`-invariant is a Maass form of `IsMaassForm`. -/
lemma IsKFiniteMaassForm.isMaassForm (h : IsKFiniteMaassForm Γ φ eigenvalue)
    (hK : ∀ k ∈ orthogonalGroup n ℝ, ∀ g, φ (of.symm (of g * k)) = φ g) :
    IsMaassForm Γ φ eigenvalue := by
  rcases h with ⟨⟨hΓ, -, -, ht, hC⟩, hφ, hc⟩
  exact ⟨hφ, hΓ, hK, ht, hC, hc⟩

/-- **Constants are Maass forms** on `GL_n` of Casimir eigenvalue `0`, for every `Γ`. -/
lemma isKFiniteMaassForm_const : IsKFiniteMaassForm Γ (fun _ ↦ c) 0 :=
  (isMaassForm_const Γ c).isKFiniteMaassForm <| isCenterFinite_const c

lemma sign_det_eventuallyEq (hg : g ∈ glSet n) :
    (fun g' : n → n → ℝ ↦ (SignType.sign (of g').det : ℂ)) =ᶠ[nhds g]
      fun _ ↦ (SignType.sign (of g).det : ℂ) := by
  have hc : Continuous fun g' : n → n → ℝ ↦ (of g').det := continuous_id.matrix_det
  rcases (isUnit_iff_ne_zero.mp hg).lt_or_gt with h | h
  · filter_upwards [hc.continuousAt.eventually_lt continuousAt_const h] with g' hg'
    rw [sign_neg hg', sign_neg h]
  · filter_upwards [continuousAt_const.eventually_lt hc.continuousAt h] with g' hg'
    rw [sign_pos hg', sign_pos h]

lemma contDiffOn_sign_det :
    ContDiffOn ℝ ∞ (fun g : n → n → ℝ ↦ (SignType.sign (of g).det : ℂ)) (glSet n) :=
  fun _ hg ↦ (contDiffAt_const.congr_of_eventuallyEq (sign_det_eventuallyEq hg)).contDiffWithinAt

lemma lie_sign_det_eq_zero (X : Matrix n n ℝ) :
    ⁅X, (⟨_, contDiffOn_sign_det⟩ : smoothFunctions n)⁆ = 0 := by
  refine Subtype.ext <| funext fun g ↦ ?_
  by_cases hg : g ∈ glSet n
  · simp [coe_bracket, leftInvariantDeriv, (sign_det_eventuallyEq hg).fderiv_eq]
  · simp [coe_bracket, leftInvariantDeriv, hg]

/-- **The sign of the determinant is a Maass form** on `GL_n` of Casimir eigenvalue `0`, for every
subgroup `Γ` of `SL_n(ℤ)`: `g ↦ sign(det g)` (`0` at the singular matrices) is locally constant on
`GL_n(ℝ)`, hence killed by `gl_n(ℝ)`, and its right translate by `k` is `sign(det k)` times
itself. For `n ≥ 1` it is not right `O(n)`-invariant (a reflection changes its sign), so it is a
non-spherical example, not covered by `IsMaassForm`. -/
lemma isKFiniteMaassForm_sign_det (hΓ : ∀ γ ∈ Γ, (γ : Matrix n n ℤ).det = 1) :
    IsKFiniteMaassForm Γ (fun g ↦ (SignType.sign (of g).det : ℂ)) 0 := by
  refine ⟨⟨fun γ hγ g ↦ ?_, ?_, isCenterFinite_of_forall_lie_eq_zero _ lie_sign_det_eq_zero,
    fun t ht g ↦ ?_, 1, 0, fun g _ ↦ ?_⟩, contDiffOn_sign_det, fun g _ ↦ ?_⟩
  · simp [← Int.cast_det, hΓ γ hγ]
  · refine Submodule.finiteDimensional_of_le (S₂ := ℂ ∙ fun g ↦ (SignType.sign (of g).det : ℂ)) <|
      Submodule.span_le.mpr <| Set.range_subset_iff.mpr fun k ↦ Submodule.mem_span_singleton.mpr
        ⟨SignType.sign (k : Matrix n n ℝ).det, funext fun g ↦ ?_⟩
    simp [rightTranslate, sign_mul, mul_comm]
  · simp only [← smul_of, det_smul, sign_mul, sign_pos (pow_pos ht (Fintype.card n)), one_mul]
  · rcases lt_trichotomy (of g).det 0 with h | h | h
    · simp [sign_neg h]
    · simp [h]
    · simp [sign_pos h]
  · simp [casimirOperator_apply, lie_sign_det_eq_zero]

variable [Nonempty n] in
/-- **The sign of the determinant is not spherical**: for `n` nonempty, `g ↦ sign(det g)` is not
a Maass form of `IsMaassForm` (not right `O(n)`-invariant: a reflection `k` changes its sign at
`1`), so `IsKFiniteMaassForm` is strictly more general. -/
lemma not_isMaassForm_sign_det :
    ¬IsMaassForm Γ (fun g ↦ (SignType.sign (of g).det : ℂ)) eigenvalue := by
  rintro ⟨-, -, hK, -⟩
  have hk : (diagonal fun i ↦ if i = Classical.arbitrary n then -1 else 1 : Matrix n n ℝ) ∈
      orthogonalGroup n ℝ := by
    rw [mem_orthogonalGroup_iff, diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    split_ifs <;> norm_num
  exact absurd (hK _ hk (of.symm 1)) <| by norm_num

end Matrix.GeneralLinearGroup
