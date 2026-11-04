import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.BaseChange
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.AutomorphicFormSpace
import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.FiniteComponent

/-!
# Hecke operators and Euler factors of automorphic forms on `GL₂(𝔸_F)`

Let `v` be a finite place of the number field `F`, with uniformizer `ϖ` and residue field `𝒪_F / v`.
A function `φ` on `GL₂(𝔸_F)` is **spherical** at `v` if it is right invariant under `GL₂(𝒪_v)`. The
**Hecke operator** `T_v` is the action of the double coset `GL₂(𝒪_v) diag(ϖ, 1) GL₂(𝒪_v)`:
`(T_v φ)(g) = ∑_{r mod v} φ(g (ϖ, r; 0, 1)_v) + φ(g (1, 0; 0, ϖ)_v)`. On spherical functions it does
not depend on the choices of `ϖ` and of the representatives, and it preserves sphericity.

A **Hecke eigenform** of level `𝔑` is a nonzero automorphic form which, at every finite place
`v ∤ 𝔑`, is spherical and an eigenvector of `T_v`, with eigenvalue `a_v`. Its **Euler factor** at
`v`, in the analytic normalisation of `L(s, π_v)` with `T = N(v)^{-s}`, is
`L_v(φ, T) = 1 - N(v)^{-1/2} a_v T + ω(ϖ) T²`, where `ω` is the central character.

The LMFDB's Euler factors are in the arithmetic normalisation of a motivic weight `w`,
`1 - N(v)^{(w-1)/2} a_v T + ω(ϖ) N(v)^w T²`, the analytic one evaluated at `N(v)^{w/2} T`
(`AdelicGL2.arithmeticEulerFactor`). For the adelic lift of a classical newform `f` of weight `k`,
with `w = k - 1`, it is the factor `1 - a_p(f) T + χ(p) p^{k-1} T²`, with `a_p = p^{k/2-1} a_v`
(`AdelicGL2.arithmeticEulerFactor_adelicLift`). The base change relation does not depend on `w`
(`AdelicGL2.isBaseChangeOf_arithmetic_iff`).

The residue field `𝒪_F / v` is given a `Fintype` instance, scoped to `AdelicGL2`, for the sums
over its elements.

## Main definitions

* `AdelicGL2.IsSphericalAt`: sphericity at a finite place.
* `AdelicGL2.heckeOp`: the Hecke operator `T_v`.
* `AdelicGL2.IsHeckeEigenform`: Hecke eigenforms of level `𝔑`.
* `AdelicGL2.heckeEigenvalue`: the eigenvalue `a_v`.
* `AdelicGL2.characterAt`: the value of a Hecke character on a uniformizer at `v`.
* `AdelicGL2.eulerFactor`: the Euler factor `L_v(φ, T)`.

## Main results

* `AdelicGL2.heckeOp_eq_sum`: `T_v` on spherical functions does not depend on the choices.
* `AdelicGL2.IsSphericalAt.heckeOp`: `T_v` preserves sphericity at `v`.
* `AdelicGL2.heckeOp_mul_levelOne`: for `v ∤ 𝔑`, `T_v` preserves right invariance under `K₁(𝔑)`.
* `AdelicGL2.IsAutomorphicForm.heckeOp`, `AdelicGL2.IsCuspidal.heckeOp`: `T_v` preserves automorphic
  forms and cusp forms.
* `AdelicGL2.IsHeckeEigenform.heckeOp_eq`: `T_v φ = a_v φ`.
* `AdelicGL2.IsHeckeEigenform.eq_heckeEigenvalue`: the eigenvalue at `v ∤ 𝔑` is unique.
* `AdelicGL2.IsHeckeEigenform.finiteComponent_eq_one`: the central character of a Hecke eigenform
  is unramified at the places `v ∤ 𝔑`.
* `AdelicGL2.IsHeckeEigenform.finiteComponent_eq_characterAt`: the value of the central character at
  `v ∤ 𝔑` does not depend on the uniformizer.
-/

open IsDedekindDomain HeightOneSpectrum Matrix NumberField Polynomial TauCeti GlobalNumberFields
  ValuationSubring

open mixedEmbedding (mixedSpace)

open scoped AdeleRing MatrixGroups Classical

namespace AdelicGL2

variable {F : Type*} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  {ω : HeckeCharacter F} {𝔑 : Ideal (𝓞 F)} {φ : AdelicGL2 F → ℂ}

/-- The residue field `𝒪_F / v` as a `Fintype`, for the sums over it, scoped to `AdelicGL2`. -/
noncomputable scoped instance : Fintype (𝓞 F ⧸ v.asIdeal) :=
  Fintype.ofFinite _

variable (φ) in
/-- A function on `GL₂(𝔸_F)` is **spherical at `v`** if it is right invariant under `GL₂(𝒪_v)`. -/
def IsSphericalAt : Prop :=
  ∀ k ∈ (v.adicCompletionIntegers F).gl2, ∀ g, φ (g * ofFin F (localGL v k)) = φ g

variable (φ) in
/-- The **Hecke operator** `T_v` at a finite place `v` of `F`:
`(T_v φ)(g) = ∑_{r mod v} φ(g (ϖ, r; 0, 1)_v) + φ(g (1, 0; 0, ϖ)_v)`, for the chosen uniformizer
`ϖ` and representatives `r`. On spherical functions it does not depend on these choices
(`heckeOp_eq_sum`). -/
noncomputable def heckeOp : AdelicGL2 F → ℂ :=
  fun g ↦ heckeSum (uniformizer v) (residueRep v) (fun m ↦ φ (g * ofFin F (localGL v m))) 1

variable {v}

lemma IsSphericalAt.mul_localGL (h : IsSphericalAt v φ) (g : AdelicGL2 F)
    (m : GL (Fin 2) (v.adicCompletion F)) {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : k ∈ (v.adicCompletionIntegers F).gl2) :
    φ (g * ofFin F (localGL v (m * k))) = φ (g * ofFin F (localGL v m)) := by
  rw [map_mul, map_mul, ← mul_assoc]
  exact h k hk _

/-- **The Hecke operator does not depend on the choices** on a function spherical at `v`: it is
the sum over the representatives `(ϖ, r i; 0, 1)` and `(1, 0; 0, ϖ)` of the cosets of the double
coset, for any uniformizer `ϖ` and any system of representatives `r` of the residue field. -/
lemma heckeOp_eq_sum (h : IsSphericalAt v φ) {ι : Type*} [Fintype ι]
    {ϖ : (v.adicCompletion F)ˣ} {r : ι → v.adicCompletion F}
    (hϖ : (v.adicCompletionIntegers F).IsUniformizer (ϖ : v.adicCompletion F))
    (hr : (v.adicCompletionIntegers F).IsResidueSystem (ϖ : v.adicCompletion F) r)
    (g : AdelicGL2 F) :
    heckeOp v φ g = ∑ o : Option ι, φ (g * ofFin F (localGL v (heckeRep ϖ r o))) := by
  have hE : heckeSum (uniformizer v) (residueRep v) (fun m ↦ φ (g * ofFin F (localGL v m))) 1 =
      heckeSum ϖ r (fun m ↦ φ (g * ofFin F (localGL v m))) 1 :=
    (isUniformizer_uniformizer v).heckeSum_eq (isResidueSystem_residueRep v (valued_uniformizer v))
      hϖ hr (fun m k hk ↦ h.mul_localGL g m hk) 1
  rw [heckeOp, hE, heckeSum]
  simp only [one_mul]

/-- **`T_v` preserves sphericity at `v`.** -/
lemma IsSphericalAt.heckeOp (h : IsSphericalAt v φ) : IsSphericalAt v (heckeOp v φ) := by
  intro k hk g
  have hE : heckeSum (uniformizer v) (residueRep v) (fun m ↦ φ (g * ofFin F (localGL v m)))
      (1 * k) =
      heckeSum (uniformizer v) (residueRep v) (fun m ↦ φ (g * ofFin F (localGL v m))) 1 :=
    (isUniformizer_uniformizer v).heckeSum_mul
      (isResidueSystem_residueRep v (valued_uniformizer v))
      (fun m k' hk' ↦ h.mul_localGL g m hk') 1 hk
  simp only [AdelicGL2.heckeOp, heckeSum, one_mul]
  simp only [heckeSum, one_mul, map_mul] at hE
  simpa only [mul_assoc, map_mul] using hE

variable (φ) in
lemma heckeOp_eq_sum_rightTranslate : heckeOp v φ =
    ∑ o : Option (𝓞 F ⧸ v.asIdeal), rightTranslate
      (ofFin F (localGL v (heckeRep (uniformizer v) (residueRep v) o))) φ := by
  ext g
  simp [heckeOp, heckeSum, rightTranslate]

/-- **`T_v` preserves automorphic forms.** -/
lemma IsAutomorphicForm.heckeOp (h : IsAutomorphicForm ω φ) :
    IsAutomorphicForm ω (heckeOp v φ) := by
  rw [heckeOp_eq_sum_rightTranslate]
  exact Submodule.sum_mem (automorphicForms ω) fun o _ ↦ h.rightTranslate _

/-- **`T_v` preserves cusp forms.** -/
lemma IsCuspidal.heckeOp (h₁ : IsAutomorphicForm ω φ) (h₂ : IsCuspidal φ) :
    IsCuspidal (heckeOp v φ) := by
  rw [heckeOp_eq_sum_rightTranslate]
  refine (Submodule.sum_mem (cuspForms ω) fun o _ ↦ ?_ : _ ∈ cuspForms ω).2
  exact ⟨h₁.rightTranslate _, h₂.rightTranslate _⟩

lemma heckeOp_rightTranslate {y : GL (Fin 2) 𝔸ᶠ[F]} (hy : atPlace v y = 1) (ψ : AdelicGL2 F → ℂ) :
    heckeOp v (rightTranslate (ofFin F y) ψ) = rightTranslate (ofFin F y) (heckeOp v ψ) := by
  ext g
  simp only [heckeOp, heckeSum, rightTranslate, mul_assoc, ← map_mul, localGL_commute hy]

lemma isSphericalAt_of_levelOne (hv : ¬𝔑 ≤ v.asIdeal)
    (hφ : ∀ u ∈ levelOne 𝔑, ∀ g, φ (g * ofFin F u) = φ g) : IsSphericalAt v φ :=
  fun _ hk g ↦ hφ _ (localGL_mem_levelOne hv hk) g

/-- **`T_v` preserves the right invariance under `K₁(𝔑)`** for `v ∤ 𝔑`. -/
lemma heckeOp_mul_levelOne (hv : ¬𝔑 ≤ v.asIdeal)
    (hφ : ∀ u ∈ levelOne 𝔑, ∀ g, φ (g * ofFin F u) = φ g) {u : GL (Fin 2) 𝔸ᶠ[F]}
    (hu : u ∈ levelOne 𝔑) (g : AdelicGL2 F) : heckeOp v φ (g * ofFin F u) = heckeOp v φ g := by
  have h₁ : heckeOp v (rightTranslate (ofFin F (awayFrom v u)) φ) = heckeOp v φ :=
    congrArg _ (funext fun g' ↦ hφ _ (awayFrom_mem_levelOne hv hu) g')
  have h₃ : g * ofFin F u = g * ofFin F (localGL v (atPlace v u)) * ofFin F (awayFrom v u) := by
    rw [mul_assoc, ← map_mul, localGL_mul_awayFrom]
  have h₄ : heckeOp v φ (g * ofFin F (localGL v (atPlace v u)) * ofFin F (awayFrom v u)) =
      heckeOp v φ (g * ofFin F (localGL v (atPlace v u))) :=
    (congrFun (h₁.symm.trans (heckeOp_rightTranslate (atPlace_awayFrom v u) φ)) _).symm
  rw [h₃, h₄]
  exact (isSphericalAt_of_levelOne hv hφ).heckeOp _ (atPlace_mem_gl2_of_mem_integralGL hu.1) g

variable (ω 𝔑 φ) in
/-- A **Hecke eigenform** of level `𝔑 ≠ 0` with central character `ω`: a nonzero automorphic form
which at every finite place `v ∤ 𝔑` is spherical and an eigenvector of the Hecke operator `T_v`.
Right invariance under `K₁(𝔑)` gives sphericity at every `v ∤ 𝔑` (`isSphericalAt_of_levelOne`),
but is not asked for: it would exclude forms such as `χ ∘ det` of level the conductor of `χ`, as
`det` maps `K₁(𝔑)` onto the integral finite ideles, on which `χ` is not trivial, while only the
places `v ∤ 𝔑` matter for the eigenvalues and the Euler factors. -/
structure IsHeckeEigenform : Prop where
  /-- A Hecke eigenform is an automorphic form. -/
  isAutomorphicForm : IsAutomorphicForm ω φ
  /-- The level is nonzero: the good places are all but finitely many. -/
  level_ne_bot : 𝔑 ≠ ⊥
  /-- A Hecke eigenform is nonzero. -/
  ne_zero : φ ≠ 0
  /-- A Hecke eigenform is spherical at the good places. -/
  spherical (v : HeightOneSpectrum (𝓞 F)) : ¬𝔑 ≤ v.asIdeal → IsSphericalAt v φ
  /-- A Hecke eigenform is an eigenvector of the Hecke operators at the good places. -/
  exists_eigenvalue (v : HeightOneSpectrum (𝓞 F)) : ¬𝔑 ≤ v.asIdeal → ∃ a : ℂ, heckeOp v φ = a • φ

variable (v φ) in
/-- The **Hecke eigenvalue** `a_v` of `φ` at `v`: the scalar `a` with `T_v φ = a φ` if there is one,
and `0` otherwise. -/
noncomputable def heckeEigenvalue : ℂ :=
  if h : ∃ a : ℂ, heckeOp v φ = a • φ then h.choose else 0

/-- **`T_v φ = a_v φ`** for a Hecke eigenform and `v ∤ 𝔑`. -/
lemma IsHeckeEigenform.heckeOp_eq (h : IsHeckeEigenform ω 𝔑 φ) (hv : ¬𝔑 ≤ v.asIdeal) :
    heckeOp v φ = heckeEigenvalue v φ • φ := by
  rw [heckeEigenvalue, dite_eq_left_of_eq_true (eq_true (h.exists_eigenvalue v hv))]
  exact (h.exists_eigenvalue v hv).choose_spec

/-- **The eigenvalue of a Hecke eigenform at `v ∤ 𝔑` is unique.** -/
lemma IsHeckeEigenform.eq_heckeEigenvalue (h : IsHeckeEigenform ω 𝔑 φ) (hv : ¬𝔑 ≤ v.asIdeal)
    {a : ℂ} (ha : heckeOp v φ = a • φ) : a = heckeEigenvalue v φ :=
  smul_left_injective ℂ h.ne_zero (ha.symm.trans (h.heckeOp_eq hv))

variable (v) in
/-- The value of a Hecke character `χ` of `F` on the chosen uniformizer at the place `v`: the value
`χ(v)` of the ideal character at the prime `v` when `χ` is unramified at `v`
(`TauCeti.GlobalNumberFields.HeckeCharacter.idealCharacter_apply_prime`). -/
noncomputable def characterAt (χ : HeckeCharacter F) : ℂˣ :=
  χ.finiteComponent v (uniformizer v)

lemma scalar_ofAdicCompletion (u : (v.adicCompletion F)ˣ) :
    scalar F (IdeleGroup.ofAdicCompletion (𝓞 F) F v u) =
      ofFin F (localGL v (GeneralLinearGroup.scalar (Fin 2) u)) := by
  refine ext_toInf_toFin ?_ ?_
  · rw [toInf_ofFin]
    refine GeneralLinearGroup.ext fun i j ↦ ?_
    rw [toInf_apply]
    rcases eq_or_ne i j with rfl | hij
    · have h : ((scalar F (IdeleGroup.ofAdicCompletion (𝓞 F) F v u) :
          Matrix (Fin 2) (Fin 2) 𝔸[F]) i i).1 = 1 := by
        simp only [scalar, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq]
        rfl
      rw [h, map_one, Units.val_one, one_apply_eq]
    · have h : ((scalar F (IdeleGroup.ofAdicCompletion (𝓞 F) F v u) :
          Matrix (Fin 2) (Fin 2) 𝔸[F]) i j).1 = 0 := by
        simp only [scalar, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_ne _ hij]
        rfl
      rw [h, map_zero, Units.val_one, one_apply_ne hij]
  · rw [toFin_ofFin]
    refine ext_atPlace fun w ↦ GeneralLinearGroup.ext fun i j ↦ ?_
    rw [atPlace_apply, atPlace_apply, toFin_apply, localGL_apply]
    rcases eq_or_ne w v with rfl | hw
    · rw [localMat_apply_self]
      rcases eq_or_ne i j with rfl | hij
      · simp only [scalar, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq]
        exact (FiniteAdeleRing.ofAdicCompletion_apply_coe F w u w).trans (Pi.mulSingle_eq_same _ _)
      · simp [scalar, hij]
    · rw [localMat_apply_of_ne hw]
      rcases eq_or_ne i j with rfl | hij
      · simp only [scalar, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq,
          one_apply_eq]
        exact (FiniteAdeleRing.ofAdicCompletion_apply_coe F v u w).trans
          (Pi.mulSingle_eq_of_ne hw _)
      · simp [scalar, hij]

private lemma scalar_mem_gl2 {u : (v.adicCompletion F)ˣ}
    (hu : Valued.v (u : v.adicCompletion F) = 1) :
    GeneralLinearGroup.scalar (Fin 2) u ∈ (v.adicCompletionIntegers F).gl2 := by
  have h₁ : (u : v.adicCompletion F) ∈ v.adicCompletionIntegers F :=
    (mem_adicCompletionIntegers _ _ v).mpr hu.le
  have h₂ : ((u⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    refine (mem_adicCompletionIntegers _ _ v).mpr ?_
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  refine fun i j ↦ ?_
  rw [← map_inv]
  simp only [GeneralLinearGroup.coe_scalar, scalar_apply]
  rcases eq_or_ne i j with rfl | hij
  · exact ⟨by simpa using h₁, by simpa using h₂⟩
  · simp [hij]

/-- **The central character of a Hecke eigenform is unramified at the good places.** -/
lemma IsHeckeEigenform.finiteComponent_eq_one (h : IsHeckeEigenform ω 𝔑 φ) (hv : ¬𝔑 ≤ v.asIdeal)
    {u : (v.adicCompletion F)ˣ} (hu : Valued.v (u : v.adicCompletion F) = 1) :
    ω.finiteComponent v u = 1 := by
  rcases Function.ne_iff.mp h.ne_zero with ⟨g, hg⟩
  have h₂ : scalar F (IdeleGroup.ofAdicCompletion (𝓞 F) F v u) * g =
      g * ofFin F (localGL v (GeneralLinearGroup.scalar (Fin 2) u)) := by
    rw [← scalar_ofAdicCompletion]
    exact GeneralLinearGroup.scalar_commute _ _
  have h₁ : φ g = (ω (QuotientGroup.mk (IdeleGroup.ofAdicCompletion (𝓞 F) F v u)) : ℂ) * φ g := by
    rw [← h.isAutomorphicForm.central, h₂, h.spherical v hv _ (scalar_mem_gl2 hu) g]
  exact Units.ext <| (mul_left_eq_self₀.mp h₁.symm).resolve_right hg

/-- **The value of the central character on a uniformizer at a good place does not depend on the
uniformizer.** -/
lemma IsHeckeEigenform.finiteComponent_eq_characterAt (h : IsHeckeEigenform ω 𝔑 φ)
    (hv : ¬𝔑 ≤ v.asIdeal) {ϖ : (v.adicCompletion F)ˣ}
    (hϖ : Valued.v (ϖ : v.adicCompletion F) = WithZero.exp (-1)) :
    ω.finiteComponent v ϖ = characterAt v ω := by
  have hu : Valued.v ((ϖ * (uniformizer v)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
      1 := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hϖ, valued_uniformizer,
      mul_inv_cancel₀ WithZero.exp_ne_zero]
  have h₁ : ω.finiteComponent v (ϖ * (uniformizer v)⁻¹) = 1 := h.finiteComponent_eq_one hv hu
  rwa [map_mul, map_inv, mul_inv_eq_one] at h₁

variable (ω v φ) in
/-- The **Euler factor** `L_v(φ, T) = 1 - N(v)^{-1/2} a_v T + ω(v) T²` of a Hecke eigenform `φ`
with central character `ω` at a good place `v`, in the analytic normalisation: `L(s, π_v)⁻¹` at
`T = N(v)^{-s}`, for the automorphic representation `π` generated by `φ`, the action of `T_v` on
the spherical vector of `π_v` having eigenvalue `N(v)^{1/2} (α + β)` for the Satake parameters
`α, β`, with `αβ = ω(v)`. -/
noncomputable def eulerFactor : ℂ[X] :=
  1 - C (((Real.sqrt (Ideal.absNorm v.asIdeal))⁻¹ : ℝ) * heckeEigenvalue v φ) * X +
    C (characterAt v ω : ℂ) * X ^ 2

variable (ω φ) in
/-- The Euler factors of `φ`, as a function of the nonzero prime ideals of `𝒪_F`, and `1` at the
other ideals. -/
noncomputable def eulerFactorOfIdeal (𝔭 : Ideal (𝓞 F)) : ℂ[X] :=
  if h : 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ then eulerFactor ⟨𝔭, h.1, h.2⟩ ω φ else 1

variable (ω v φ) in
/-- The **Euler factor in the arithmetic normalisation of motivic weight `w`**:
`1 - N(v)^{(w-1)/2} a_v T + ω(v) N(v)^w T²`, the Euler factor evaluated at `N(v)^{w/2} T`. For the
adelic lift of a classical newform `f` of weight `k`, with `w = k - 1`, it is the factor
`1 - a_p(f) T + χ(p) p^{k-1} T²` of the LMFDB. -/
noncomputable def arithmeticEulerFactor (w : ℤ) : ℂ[X] :=
  (eulerFactor v ω φ).comp (C (((Real.sqrt (Ideal.absNorm v.asIdeal) ^ w : ℝ) : ℂ)) * X)

variable (ω φ) in
/-- The Euler factors in the arithmetic normalisation of motivic weight `w`, as a function of the
nonzero prime ideals of `𝒪_F`, and `1` at the other ideals. -/
noncomputable def arithmeticEulerFactorOfIdeal (w : ℤ) (𝔭 : Ideal (𝓞 F)) : ℂ[X] :=
  if h : 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ then arithmeticEulerFactor ⟨𝔭, h.1, h.2⟩ ω φ w else 1

end AdelicGL2
