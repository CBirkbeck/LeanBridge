import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.CuspFormsFiniteDimensional
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwoDecomposition
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.PeterssonKlingen
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.PeterssonSiegelEisenstein

/-!
# The decompositions `M_{j,k}(Γ₂) = S_{j,k}(Γ₂) ⊕ N_{j,k}(Γ₂)` and `N_{j,k}(Γ₂) = E ⊕ KE`

Let `N_{j,k}(Γ₂)` be the orthogonal complement of the cusp forms in `M_{j,k}(Γ₂)`, for the Petersson
product with respect to an admissible positive definite Hermitian form on `Sym^j(ℂ²)`, such as
`SiegelUpperHalfSpace.symHermitianForm`. In every weight, the Petersson product is definite on the
finite-dimensional space `S_{j,k}(Γ₂)`, so that every modular form has an orthogonal projection to
`S_{j,k}(Γ₂)` and `M_{j,k}(Γ₂) = S_{j,k}(Γ₂) ⊕ N_{j,k}(Γ₂)`. For `k > 4`, the Siegel Eisenstein
series and the Klingen–Eisenstein series lie in `N_{j,k}(Γ₂)`, by the unfolding of the Petersson
product. Since `M_{j,k}(Γ₂) = S_{j,k}(Γ₂) ⊕ E_{j,k}(Γ₂) ⊕ KE_{j,k}(Γ₂)` for `k > 4`, this gives
`N_{j,k}(Γ₂) = E_{j,k}(Γ₂) ⊕ KE_{j,k}(Γ₂)`. These are the decompositions of the knowl
`mf.siegel.subspace.degree.two`, which paraphrases Arakawa (*Vector valued Siegel's modular forms of
degree two and the associated Andrianov L-functions*, Manuscripta Math. 44 (1983), Introduction and
§1): the Petersson product is his (1.3), `KE_{j,k}(Γ₂)` the span of his series (1.4), and he takes
`k > 4` for the isomorphism with the cusp forms of `SL(2, ℤ)`.

For `k ≤ 4` the second decomposition is not proved here, and `KE_{j,k}(Γ₂)` has no meaning there, as
the series do not converge. What is proved in every weight is that the Siegel operator is injective
on `N_{j,k}(Γ₂)`, and that `N_{j,k}(Γ₂) = 0` for odd `k`.

## Main results

* `SiegelUpperHalfSpace.disjoint_cuspFormsKJ_cuspFormsOrthogonalKJ`:
  `S_{j,k}(Γ₂) ∩ N_{j,k}(Γ₂) = 0`.
* `SiegelUpperHalfSpace.eq_zero_of_mem_cuspFormsOrthogonalKJ_of_siegelOperatorVanishes`: the Siegel
  operator is injective on `N_{j,k}(Γ₂)`.
* `SiegelUpperHalfSpace.cuspFormsOrthogonalKJ_eq_bot_of_odd`: `N_{j,k}(Γ₂) = 0` for odd `k`.
* `SiegelUpperHalfSpace.klingenEisensteinSubspaceKJ_le_cuspFormsOrthogonalKJ`:
  `KE_{j,k}(Γ₂) ⊆ N_{j,k}(Γ₂)` for `k > 4`.
* `SiegelUpperHalfSpace.siegelEisensteinSubspaceKJ_le_cuspFormsOrthogonalKJ`:
  `E_{j,k}(Γ₂) ⊆ N_{j,k}(Γ₂)` for `k > 4`.
* `SiegelUpperHalfSpace.exists_mem_forall_peterssonProduct_eq`: the orthogonal projection onto a
  finite-dimensional space with a definite Petersson product.
* `SiegelUpperHalfSpace.modularFormsKJ_eq_cuspFormsKJ_sup_cuspFormsOrthogonalKJ` (LMFDB
  `mf.siegel.subspace.degree.two`): `M_{j,k}(Γ₂) = S_{j,k}(Γ₂) + N_{j,k}(Γ₂)` in every weight.
* `SiegelUpperHalfSpace.cuspFormsOrthogonalKJ_eq_sup` (LMFDB `mf.siegel.subspace.degree.two`):
  `N_{j,k}(Γ₂) = E_{j,k}(Γ₂) + KE_{j,k}(Γ₂)` for `k > 4`.
* `SiegelUpperHalfSpace.disjoint_siegelEisensteinSubspaceKJ_klingenEisensteinSubspaceKJ`: the sum is
  direct.
-/

open Matrix hiding mul_inv_rev inv_zpow inv_zpow' zpow_neg one_zpow

open Complex MeasureTheory Module SymplecticGroup

open scoped ComplexOrder TensorProduct

namespace SiegelUpperHalfSpace

variable {k : ℤ} {j : ℕ} {c : Sym[ℂ]^j (Fin 2 → ℂ) →ₗ[ℂ] Sym[ℂ]^j (Fin 2 → ℂ) →ₗ⋆[ℂ] ℂ}

/-- **A form both cuspidal and orthogonal to the cusp forms vanishes**: for an admissible positive
definite form `c`, `S_{j,k}(Γ₂) ∩ N_{j,k}(Γ₂) = 0`, in every weight. -/
lemma disjoint_cuspFormsKJ_cuspFormsOrthogonalKJ (hadm : IsAdmissibleForm (rhoKJ k j) c)
    (hpos : ∀ v, v ≠ 0 → 0 < c v v) : Disjoint (cuspFormsKJ k j (integral (Fin 2)))
      (cuspFormsOrthogonalKJ (integral (Fin 2)) k j c) :=
  Submodule.disjoint_def.mpr fun F hF hF' ↦
    (isPeterssonDefinite_cuspForms (isModerateForm_rhoKJ k c) hadm hpos).eq_zero F hF (hF'.2 F hF).2

/-- **The Klingen–Eisenstein series are orthogonal to the cusp forms**: for `k > 4` and an
admissible form `c`, `KE_{j,k}(Γ₂) ⊆ N_{j,k}(Γ₂)`. -/
lemma klingenEisensteinSubspaceKJ_le_cuspFormsOrthogonalKJ (hadm : IsAdmissibleForm (rhoKJ k j) c)
    (hk : 4 < k) :
    klingenEisensteinSubspaceKJ k j ≤ cuspFormsOrthogonalKJ (integral (Fin 2)) k j c := by
  intro F hF
  rcases Int.even_or_odd k with hk' | hk'
  · rcases Nat.even_or_odd j with hj | hj
    · have hF₀ : F ∈ LinearMap.range (vectorKlingenEisensteinLinear k j hk) :=
        klingenEisensteinSubspaceKJ_eq_range hk hj ▸ hF
      rcases hF₀ with ⟨f, rfl⟩
      exact ⟨hF.2, fun G hG ↦ isPeterssonOrthogonal_vectorKlingenEisenstein f hadm hk hk' hG⟩
    · have h₀ : F ∈ modularFormsKJ k j (integral (Fin 2)) := hF.2
      rw [modularFormsKJ_eq_bot_of_odd hj, Submodule.mem_bot] at h₀
      rw [h₀]
      exact zero_mem _
  · have h₁ : F ∈ cuspFormsKJ k j (integral (Fin 2)) := by
      rw [← modularFormsKJ_eq_cuspFormsKJ_of_odd hk']
      exact hF.2
    rw [Submodule.disjoint_def.mp (disjoint_klingenEisensteinSubspaceKJ_cuspFormsKJ hk) F hF h₁]
    exact zero_mem _

/-- **The Siegel Eisenstein series are orthogonal to the cusp forms**: for `k > 4` and an admissible
form `c`, `E_{j,k}(Γ₂) ⊆ N_{j,k}(Γ₂)`. -/
lemma siegelEisensteinSubspaceKJ_le_cuspFormsOrthogonalKJ (hadm : IsAdmissibleForm (rhoKJ k j) c)
    (hk : 4 < k) :
    siegelEisensteinSubspaceKJ k j ≤ cuspFormsOrthogonalKJ (integral (Fin 2)) k j c := by
  rcases eq_or_ne j 0 with rfl | hj
  · rcases Int.even_or_odd k with hk' | hk'
    · have hk₅ : 5 < k := by
        rcases hk' with ⟨m, rfl⟩
        omega
      rw [siegelEisensteinSubspaceKJ_eq_span_singleton hk₅ hk', Submodule.span_singleton_le_iff_mem]
      exact ⟨siegelEisensteinKJ_mem_modularFormsKJ hk₅ hk',
        fun G hG ↦ isPeterssonOrthogonal_siegelEisensteinKJ hadm hk₅ hk' hG⟩
    · intro F hF
      have h₁ : F ∈ cuspFormsKJ k 0 (integral (Fin 2)) := by
        rw [← modularFormsKJ_eq_cuspFormsKJ_of_odd hk']
        exact siegelEisensteinSubspaceKJ_le_modularFormsKJ k 0 hk hF
      rw [Submodule.disjoint_def.mp (disjoint_sup_siegelEisensteinSubspaceKJ k 0 hk) F
        (Submodule.mem_sup_left h₁) hF]
      exact zero_mem _
  · rw [siegelEisensteinSubspaceKJ_eq_bot k hj]
    exact bot_le

private lemma integrableOn_fundamentalDomain (hadm : IsAdmissibleForm (rhoKJ k j) c)
    {f g : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)}
    (hf : f ∈ modularFormsKJ k j (integral (Fin 2))) (hg : g ∈ cuspFormsKJ k j (integral (Fin 2))) :
    IntegrableOn (peterssonIntegrand (rhoKJ k j) c f g) (fundamentalDomain (integral (Fin 2)))
      (invariantMeasure (Fin 2)) :=
  integrableOn_peterssonIntegrand (isModerateForm_rhoKJ k c) hadm hf hg
    (isFundamentalDomain_fundamentalDomain (isArithmetic_integral (Fin 2)))

variable {l V : Type*} [Fintype l] [DecidableEq l] [AddCommGroup V] [Module ℂ V]
    {Γ : Subgroup (symplecticGroup l ℚ)} {ρ : Representation ℂ (GL l ℂ) V}
    {b : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {W : Submodule ℂ (SiegelUpperHalfSpace l → V)}

/-- The conjugate-linear form `G ↦ ⟨f, G⟩` on `W`, for `f` with integrable Petersson integrands. -/
private noncomputable def peterssonRightForm {f : SiegelUpperHalfSpace l → V}
    (hf : ∀ g ∈ W, IntegrableOn (peterssonIntegrand ρ b f g) (fundamentalDomain Γ)
      (invariantMeasure l)) : W →ₗ⋆[ℂ] ℂ where
  toFun G := peterssonProduct Γ ρ b f G
  map_add' G G' := by
    rw [Submodule.coe_add, peterssonProduct, peterssonIntegrand_add_right]
    simp only [Pi.add_apply]
    rw [integral_add (hf _ G.2) (hf _ G'.2), ← peterssonProduct, ← peterssonProduct]
  map_smul' a G := by
    rw [Submodule.coe_smul, peterssonProduct, peterssonIntegrand_smul_right]
    simp only [Pi.smul_apply]
    rw [integral_smul, ← peterssonProduct]

/-- The linear form `g ↦ ⟨g, G⟩` on `W`, for `G ∈ W`, when the Petersson product of `W` is
definite. -/
private noncomputable def peterssonLeftForm (h : IsPeterssonDefinite Γ ρ b W)
    {G : SiegelUpperHalfSpace l → V} (hG : G ∈ W) : W →ₗ[ℂ] ℂ where
  toFun g := peterssonProduct Γ ρ b g G
  map_add' g g' := by
    rw [Submodule.coe_add, peterssonProduct, peterssonIntegrand_add_left]
    simp only [Pi.add_apply]
    rw [integral_add (h.integrableOn _ _ g.2 hG) (h.integrableOn _ _ g'.2 hG), ← peterssonProduct,
      ← peterssonProduct]
  map_smul' a g := by
    rw [Submodule.coe_smul, peterssonProduct, peterssonIntegrand_smul_left]
    simp only [Pi.smul_apply]
    rw [integral_smul, ← peterssonProduct, RingHom.id_apply]

/-- **The orthogonal projection onto a finite-dimensional space with a definite Petersson product**:
for `F` with integrable Petersson integrands against `W`, there is `g ∈ W` with `⟨F, G⟩ = ⟨g, G⟩`
for all `G ∈ W`: the linear map `g ↦ (⟨g, w_i⟩)_i`, for a basis `(w_i)` of `W`, is injective, hence
surjective. -/
lemma exists_mem_forall_peterssonProduct_eq [FiniteDimensional ℂ W]
    (h : IsPeterssonDefinite Γ ρ b W) {F : SiegelUpperHalfSpace l → V}
    (hF : ∀ g ∈ W, IntegrableOn (peterssonIntegrand ρ b F g) (fundamentalDomain Γ)
      (invariantMeasure l)) :
    ∃ g ∈ W, ∀ G ∈ W, peterssonProduct Γ ρ b F G = peterssonProduct Γ ρ b g G := by
  let w : Basis (Fin (finrank ℂ W)) ℂ W := finBasis ℂ W
  let Φ : W →ₗ[ℂ] Fin (finrank ℂ W) → ℂ :=
    LinearMap.pi fun i ↦ peterssonLeftForm h (w i).2
  have hinj : Function.Injective Φ := (injective_iff_map_eq_zero _).mpr fun g hg ↦ by
    have h₀ : peterssonRightForm (fun G hG ↦ h.integrableOn g G g.2 hG) = 0 :=
      w.ext fun i ↦ congrFun hg i
    exact Subtype.ext <| h.eq_zero g g.2 (LinearMap.congr_fun h₀ g)
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (finrank_fin_fun ℂ).symm).mp hinj
  rcases hsurj fun i ↦ peterssonRightForm hF (w i) with ⟨g, hg⟩
  refine ⟨g, g.2, fun G hG ↦ ?_⟩
  have h₀ : peterssonRightForm hF = peterssonRightForm (fun G hG ↦ h.integrableOn g G g.2 hG) :=
    w.ext fun i ↦ (congrFun hg i).symm
  exact LinearMap.congr_fun h₀ ⟨G, hG⟩

/-- **The Siegel operator is injective on `N_{j,k}(Γ₂)`**, in every weight, for an admissible
positive definite form `c`: an element of `N_{j,k}(Γ₂)` whose Siegel operator vanishes is a cusp
form, hence `0`. -/
lemma eq_zero_of_mem_cuspFormsOrthogonalKJ_of_siegelOperatorVanishes
    (hadm : IsAdmissibleForm (rhoKJ k j) c) (hpos : ∀ v, v ≠ 0 → 0 < c v v)
    {F : SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)}
    (hF : F ∈ cuspFormsOrthogonalKJ (integral (Fin 2)) k j c) (hv : SiegelOperatorVanishes F) :
    F = 0 :=
  Submodule.disjoint_def.mp (disjoint_cuspFormsKJ_cuspFormsOrthogonalKJ hadm hpos) F
    ⟨hF.1, isCuspForm_of_siegelOperatorVanishes hF.1 hv⟩ hF

/-- **`N_{j,k}(Γ₂) = 0` for odd `k`**, in every weight, for an admissible positive definite form
`c`, since then `M_{j,k}(Γ₂) = S_{j,k}(Γ₂)`. -/
lemma cuspFormsOrthogonalKJ_eq_bot_of_odd (hadm : IsAdmissibleForm (rhoKJ k j) c)
    (hpos : ∀ v, v ≠ 0 → 0 < c v v) (hk : Odd k) :
    cuspFormsOrthogonalKJ (integral (Fin 2)) k j c = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun F hF ↦
    Submodule.disjoint_def.mp (disjoint_cuspFormsKJ_cuspFormsOrthogonalKJ hadm hpos) F
      (modularFormsKJ_eq_cuspFormsKJ_of_odd hk ▸ hF.1) hF

/-- **`M_{j,k}(Γ₂) = S_{j,k}(Γ₂) ⊕ N_{j,k}(Γ₂)`** (LMFDB `mf.siegel.subspace.degree.two`), in every
weight, for an admissible positive definite form `c`; the sum is direct
(`SiegelUpperHalfSpace.disjoint_cuspFormsKJ_cuspFormsOrthogonalKJ`). -/
lemma modularFormsKJ_eq_cuspFormsKJ_sup_cuspFormsOrthogonalKJ
    (hadm : IsAdmissibleForm (rhoKJ k j) c) (hpos : ∀ v, v ≠ 0 → 0 < c v v) :
    modularFormsKJ k j (integral (Fin 2)) =
      cuspFormsKJ k j (integral (Fin 2)) ⊔ cuspFormsOrthogonalKJ (integral (Fin 2)) k j c := by
  refine le_antisymm (fun F hF ↦ ?_)
    (sup_le (cuspForms_le_modularForms _ _ _) (cuspFormsOrthogonal_le _ _ _))
  have : FiniteDimensional ℂ (cuspForms (rhoKJ k j) (integral (Fin 2)) 1) :=
    finiteDimensional_cuspFormsKJ k j
  rcases exists_mem_forall_peterssonProduct_eq
    (isPeterssonDefinite_cuspForms (isModerateForm_rhoKJ k c) hadm hpos)
    (fun g hg ↦ integrableOn_fundamentalDomain hadm hF hg) with ⟨g, hg, hgF⟩
  have hsub : F - g ∈ modularFormsKJ k j (integral (Fin 2)) :=
    sub_mem hF (cuspForms_le_modularForms _ _ _ hg)
  refine Submodule.mem_sup.mpr ⟨g, hg, F - g, ⟨hsub, fun G hG ↦
    ⟨integrableOn_fundamentalDomain hadm hsub hG, ?_⟩⟩, add_sub_cancel _ _⟩
  have e : peterssonIntegrand (rhoKJ k j) c (F - g) G = peterssonIntegrand (rhoKJ k j) c F G -
      peterssonIntegrand (rhoKJ k j) c g G := by
    ext τ
    simp [peterssonIntegrand_apply]
  rw [peterssonProduct, e]
  simp only [Pi.sub_apply]
  rw [integral_sub (integrableOn_fundamentalDomain hadm hF hG)
    (integrableOn_fundamentalDomain hadm hg.1 hG), ← peterssonProduct, ← peterssonProduct, hgF G hG,
    sub_self]

/-- **`N_{j,k}(Γ₂) = E_{j,k}(Γ₂) ⊕ KE_{j,k}(Γ₂)`** (LMFDB `mf.siegel.subspace.degree.two`), for
`k > 4` and an admissible positive definite form `c`; the sum is direct
(`SiegelUpperHalfSpace.disjoint_siegelEisensteinSubspaceKJ_klingenEisensteinSubspaceKJ`). -/
lemma cuspFormsOrthogonalKJ_eq_sup (hadm : IsAdmissibleForm (rhoKJ k j) c)
    (hpos : ∀ v, v ≠ 0 → 0 < c v v) (hk : 4 < k) : cuspFormsOrthogonalKJ (integral (Fin 2)) k j c =
      siegelEisensteinSubspaceKJ k j ⊔ klingenEisensteinSubspaceKJ k j := by
  have hE : siegelEisensteinSubspaceKJ k j ≤ cuspFormsOrthogonalKJ (integral (Fin 2)) k j c :=
    siegelEisensteinSubspaceKJ_le_cuspFormsOrthogonalKJ hadm hk
  have hK : klingenEisensteinSubspaceKJ k j ≤ cuspFormsOrthogonalKJ (integral (Fin 2)) k j c :=
    klingenEisensteinSubspaceKJ_le_cuspFormsOrthogonalKJ hadm hk
  refine le_antisymm (fun F hF ↦ ?_) (sup_le hE hK)
  have hM : F ∈ cuspFormsKJ k j (integral (Fin 2)) ⊔ (siegelEisensteinSubspaceKJ k j ⊔
      klingenEisensteinSubspaceKJ k j) := by
    rw [← sup_assoc, ← modularFormsKJ_eq_sup k j hk]
    exact cuspFormsOrthogonal_le _ _ _ hF
  rcases Submodule.mem_sup.mp hM with ⟨s, hs, n, hn, rfl⟩
  have hs' : s ∈ cuspFormsOrthogonalKJ (integral (Fin 2)) k j c := by
    have h₁ : s + n - n ∈ cuspFormsOrthogonalKJ (integral (Fin 2)) k j c :=
      sub_mem hF (sup_le hE hK hn)
    rwa [add_sub_cancel_right] at h₁
  rw [Submodule.disjoint_def.mp (disjoint_cuspFormsKJ_cuspFormsOrthogonalKJ hadm hpos) s hs hs',
    zero_add]
  exact hn

/-- **The sum `E_{j,k}(Γ₂) + KE_{j,k}(Γ₂)` is direct**, for `k > 4`. -/
lemma disjoint_siegelEisensteinSubspaceKJ_klingenEisensteinSubspaceKJ (hk : 4 < k) :
    Disjoint (siegelEisensteinSubspaceKJ k j) (klingenEisensteinSubspaceKJ k j) :=
  (disjoint_sup_siegelEisensteinSubspaceKJ k j hk).symm.mono_right le_sup_right

end SiegelUpperHalfSpace
