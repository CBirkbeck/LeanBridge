import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.Newform

/-!
# Maass forms of trivial character on `Γ₀(N)`

The Maass forms of weight `0` on `Γ₀(N)` with the trivial character
(`UpperHalfPlane.IsMaassFormWithCharacter`, square-integrable on a fundamental domain of the image
of `Γ₀(N)` in `PSL(2, ℤ)`) are the Maass forms on `Γ₀(N)` of `UpperHalfPlane.IsMaassForm`
(square-integrable on a fundamental domain of the image of `Γ₀(N)` in `PGL(2, ℝ)`): the map
`PSL(2, ℤ) → PGL(2, ℝ)` induced by `SL(2, ℤ) → GL(2, ℝ)` is injective and compatible with the
actions on `ℍ`, so that the two images of `Γ₀(N)` have the same fundamental domains.

## Main definitions

* `UpperHalfPlane.pslToPGL`: the map `PSL(2, ℤ) → PGL(2, ℝ)`.
* `UpperHalfPlane.gammaZeroPSLEquivPGL`: the isomorphism between the images of `Γ₀(N)` in
  `PSL(2, ℤ)` and in `PGL(2, ℝ)`.

## Main results

* `UpperHalfPlane.isFundamentalDomain_pgl_iff`: the two images of `Γ₀(N)` have the same
  fundamental domains in `ℍ`.
* `UpperHalfPlane.isMaassFormWithCharacter_one_iff`: the Maass forms on `Γ₀(N)` of trivial
  character are those of `UpperHalfPlane.IsMaassForm`.
-/

open MeasureTheory CongruenceSubgroup Matrix SpecialLinearGroup

open scoped MatrixGroups

namespace UpperHalfPlane

variable {N : ℕ} {f : ℂ → ℂ} {eigenvalue : ℂ} {D : Set ℍ} {γ : SL(2, ℤ)}

/-- The map `PSL(2, ℤ) → PGL(2, ℝ)` induced by `SL(2, ℤ) → GL(2, ℝ)`: it is well defined since
`±1` act trivially on `ℍ`, on which `PGL(2, ℝ)` acts faithfully, and it is injective and compatible
with the actions on `ℍ` (`pslToPGL_smul`). -/
noncomputable def pslToPGL : PSL(2, ℤ) →* PGL(2, ℝ) :=
  QuotientGroup.lift (Subgroup.center SL(2, ℤ)) (ProjGenLinGroup.mk.comp (mapGL ℝ)) fun z hz ↦ by
    refine MonoidHom.mem_ker.mpr <| eq_of_smul_eq_smul (α := ℍ) fun x ↦ ?_
    have h : (z : PSL(2, ℤ)) • x = z • x := pslMk_smul z x
    rw [(QuotientGroup.eq_one_iff z).mpr hz, one_smul] at h
    rw [MonoidHom.comp_apply, pglMk_smul, one_smul]
    exact h.symm

lemma pslToPGL_smul (g : PSL(2, ℤ)) (z : ℍ) : pslToPGL g • z = g • z := by
  induction g using QuotientGroup.induction_on with
  | H γ =>
    rw [pslToPGL, QuotientGroup.lift_mk, MonoidHom.comp_apply, pglMk_smul, pslMk_smul]
    rfl

lemma pslToPGL_injective : Function.Injective pslToPGL := fun g h hgh ↦
  eq_of_smul_eq_smul (α := ℍ) fun x ↦ by rw [← pslToPGL_smul, hgh, pslToPGL_smul]

lemma map_gamma0_pslToPGL :
    ((Gamma0 N).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))).map pslToPGL =
      ((Gamma0 N).map (mapGL ℝ)).map ProjGenLinGroup.mk := by
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

variable (N) in
/-- The isomorphism between the images of `Γ₀(N)` in `PSL(2, ℤ)` and in `PGL(2, ℝ)`, induced by
`pslToPGL`, which is compatible with the actions on `ℍ`. -/
noncomputable def gammaZeroPSLEquivPGL :
    (Gamma0 N).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))) ≃*
      ((Gamma0 N).map (mapGL ℝ)).map ProjGenLinGroup.mk :=
  ((Gamma0 N).map _).equivMapOfInjective pslToPGL pslToPGL_injective |>.trans <|
    MulEquiv.subgroupCongr map_gamma0_pslToPGL

lemma gammaZeroPSLEquivPGL_smul (g : (Gamma0 N).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ))))
    (z : ℍ) : gammaZeroPSLEquivPGL N g • z = g • z :=
  pslToPGL_smul g z

/-- **The images of `Γ₀(N)` in `PGL(2, ℝ)` and in `PSL(2, ℤ)` have the same fundamental
domains** in `ℍ`, for the invariant measure. -/
lemma isFundamentalDomain_pgl_iff :
    IsFundamentalDomain (((Gamma0 N).map (mapGL ℝ)).map ProjGenLinGroup.mk) D volume ↔
      IsFundamentalDomain ((Gamma0 N).map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) D
        volume := by
  constructor
  · intro hD
    simpa using hD.preimage_of_equiv (QuasiMeasurePreserving.id volume)
      (gammaZeroPSLEquivPGL N).symm.bijective fun g x ↦
        (gammaZeroPSLEquivPGL_smul _ x).symm.trans <| congrArg (· • x) <|
          MulEquiv.apply_symm_apply _ g
  · intro hD
    simpa using hD.preimage_of_equiv (QuasiMeasurePreserving.id volume)
      (gammaZeroPSLEquivPGL N).bijective fun g x ↦ gammaZeroPSLEquivPGL_smul g x

lemma dirichletCharacter_one_apply_of_mem_gamma0 (hγ : γ ∈ Gamma0 N) :
    (1 : DirichletCharacter ℂ N) (γ 1 1 : ℤ) = 1 := by
  rw [← ZMod.coe_unitOfIsCoprime _ (isCoprime_of_mem_gamma0 hγ)]
  exact MulChar.one_apply_coe _

lemma forall_smul_eq_iff :
    (∀ γ ∈ Gamma0 N, ∀ z : ℍ, f ↑(γ • z) = (1 : DirichletCharacter ℂ N) (γ 1 1 : ℤ) * f z) ↔
      ∀ γ ∈ (Gamma0 N).map (mapGL ℝ), ∀ z : ℍ, f ↑(γ • z) = f z := by
  constructor
  · rintro h _ ⟨γ, hγ, rfl⟩ z
    exact (h γ hγ z).trans <| by rw [dirichletCharacter_one_apply_of_mem_gamma0 hγ, one_mul]
  · intro h γ hγ z
    rw [dirichletCharacter_one_apply_of_mem_gamma0 hγ, one_mul]
    exact h _ (Subgroup.mem_map_of_mem _ hγ) z

/-- **Maass forms of trivial character are the Maass forms on `Γ₀(N)`** of `IsMaassForm`: the
square-integrability on a fundamental domain in `PSL(2, ℤ)` and in `PGL(2, ℝ)` agree
(`isFundamentalDomain_pgl_iff`), and the trivial character takes the value `1` on `Γ₀(N)`. -/
lemma isMaassFormWithCharacter_one_iff : IsMaassFormWithCharacter N 1 f eigenvalue ↔
    IsMaassForm ((Gamma0 N).map (mapGL ℝ)) f eigenvalue := by
  constructor
  · rintro ⟨hs, hL, hinv, he⟩
    exact ⟨hs, ⟨gammaZeroDomain N,
      isFundamentalDomain_pgl_iff.mpr (isFundamentalDomain_gammaZeroDomain N), hL⟩,
      forall_smul_eq_iff.mp hinv, he⟩
  · rintro ⟨hs, ⟨D, hD, hL⟩, hinv, he⟩
    exact ⟨hs, (integrableOn_iff_of_isFundamentalDomain (forall_smul_eq_iff.mpr hinv)
      (isFundamentalDomain_pgl_iff.mp hD)).mp hL, forall_smul_eq_iff.mpr hinv, he⟩

end UpperHalfPlane
