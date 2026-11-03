import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.LevelTwoScalarRepresentation
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParamodularLevelRaisingThetaPrime
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParamodularNonliftNewformLevelOne
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParamodularOldModularForms

/-!
# Paramodular newforms and the level raising operators `V_p^±`, `U_p`

The LMFDB knowl `mf.siegel.newform.paramodular` calls a Hecke eigenform on the paramodular group
`K(N)` a newform if it is not a Gritsenko lift and not the result of applying a level raising
operator to a paramodular form of lower level, the level raising operators being
`V_m^±: S_k(K(N)) → S_k(K(mN))` and `U_m: S_k(K(N)) → S_k(K(m²N))`, after Roberts and Schmidt.
The knowl does not define them. Roberts and Schmidt (*On modular forms for the paramodular group*,
in *Automorphic forms and zeta functions*, World Scientific 2006, §4;
https://sites.math.unt.edu/~schmidt/papers/arakawa.pdf) define, for a prime `p`, three level
raising operators, the classical counterparts of the local operators `η`, `θ`, `θ'` of their book
*Local newforms for GSp(4)*:
* `η_p F = F ∣ η_p⁻¹`, `η_p = diag(1, p⁻¹, 1, p)`, from level `N` to `Np²` (their (7)), so that
  `(η_p F)(τ, z, ω) = p^k F(τ, pz, p²ω)`, compatible with the operator `U_p` of Eichler and Zagier
  on the Fourier–Jacobi coefficients (their (8)): it is `SiegelUpperHalfSpace.levelRaisingEta`
  (`SiegelUpperHalfSpace.coe_levelRaisingEta`, `diag(1, p, 1, p⁻¹) = η_p⁻¹`);
* `θ_p F = ∑_γ F ∣ diag(1, 1, p⁻¹, p⁻¹) ι(γ)`, `γ ∈ Γ₀(p) \ SL(2, ℤ)`, from level `N` to `Np`
  (their (10)), compatible with the operator `V_p` of Eichler and Zagier (their (11)): up to the
  normalisation of the slash operator on scalar matrices it is
  `SiegelUpperHalfSpace.levelRaisingThetaPrime` (`SiegelUpperHalfSpace.coe_levelRaisingThetaPrime`);
* `θ'_p = u_p θ_p u_p`, its conjugate by the Atkin–Lehner involutions (their (14)), which is the
  trace from `K(N) ∩ K(Np)` to `K(Np)` (their (16)), that is
  `SiegelUpperHalfSpace.levelRaisingTheta`.
The existing names `levelRaisingTheta` and `levelRaisingThetaPrime` are thus swapped with respect
to Roberts and Schmidt. Accordingly the knowl's `U_m` is `η_m` (`F ↦ F ∣ diag(1, m, 1, m⁻¹)`,
defined for every `m`, whose image lies in that of `η_p` for the primes `p ∣ m`,
`SiegelUpperHalfSpace.levelRaisingModularImage_levelRaisingEta_mul_le`), and its `V_p^±` are `θ_p`
and `θ'_p`; which sign is which is not said by the sources, and `V_p^+ = θ_p` (compatible with
`V_p`), `V_p^- = θ'_p` is used here. For composite `m` the sources define no `V_m^±`; Roberts and
Schmidt's old forms are those obtained by repeatedly applying `θ_p`, `θ'_p`, `η_p`, and a composite
from a lower level ends with one of them, applied to a paramodular form of an intermediate lower
level, the operators preserving modular forms when the slash operator preserves holomorphy
(`SiegelUpperHalfSpace.levelRaisingModularImage_comp_le`).
The compatibilities with `U_p`, `V_p` are Roberts and Schmidt's, not proved here. The operators are
defined here as linear maps between the spaces `S_ρ(K(N))`, when the slash operator preserves
holomorphy (as it does for the holomorphic representations `ρ`, such as `det^k`, of the LMFDB),
and the newforms of the knowl, the Hecke eigenforms that are not Gritsenko lifts and not in the
image of `θ_p`, `θ'_p` (from level `N / p`) or `η_p` (from level `N / p²`) of a paramodular form,
for the primes `p`.

## Main definitions

* `SiegelUpperHalfSpace.paramodularCuspFormsMap`: an operator mapping cusp forms to cusp forms, as
  a linear map `S_ρ(K(M)) → S_ρ(K(N))`.
* `SiegelUpperHalfSpace.paramodularVPlus`, `SiegelUpperHalfSpace.paramodularVMinus`,
  `SiegelUpperHalfSpace.paramodularU` (LMFDB `mf.siegel.newform.paramodular`): the level raising
  operators `V_p^+ = θ_p`, `V_p^- = θ'_p` and `U_m = η_m`.
* `SiegelUpperHalfSpace.IsNotLevelRaised` (LMFDB `mf.siegel.newform.paramodular`): not the image
  of a paramodular form of lower level under a level raising operator.
* `SiegelUpperHalfSpace.IsNewParamodularEigenform` (LMFDB `mf.siegel.newform.paramodular`): the
  paramodular newforms of the knowl.

For the scalar weights `ρ = det^k` of the knowl the slash operator preserves holomorphy
(`SiegelUpperHalfSpace.isHolomorphic_gspSlash_detPowerRep`), so that the knowl's operators
`S_k(K(N)) → S_k(K(pN))`, `S_k(K(N)) → S_k(K(m²N))` are
`paramodularVPlus (TauCeti.detPowerRep ℂ 2 k) N p (isHolomorphic_gspSlash_detPowerRep k) hp` and
its analogues.

## Main results

* `SiegelUpperHalfSpace.isHolomorphic_gspSlash_detPowerRep`: the slash operator of `GSp(4, ℚ)⁺` of
  scalar weight `k` preserves holomorphy.
* `SiegelUpperHalfSpace.doubleCosetOperator_mem_modularForms`: the level raising operators map
  modular forms to modular forms when the slash operator preserves holomorphy.
* `SiegelUpperHalfSpace.levelRaisingModularImage_comp_le`: the image of a composite of level
  raising operators lies in the image of the last one.
* `SiegelUpperHalfSpace.levelRaisingModularImage_levelRaisingEta_mul_le`: the image of
  `U_{mp} = η_{mp}` lies in the image of `U_p = η_p`.
* `SiegelUpperHalfSpace.coe_paramodularVPlus`, `SiegelUpperHalfSpace.coe_paramodularU`: the
  formulas of `V_p^+` and `U_m`.
* `SiegelUpperHalfSpace.isNotLevelRaised_one`: in level `1` no function is obtained by level
  raising.
* `SiegelUpperHalfSpace.isNotLevelRaised_of_not_mem_paramodularOldModularForms`: a modular form
  which is not old is not obtained by level raising.
* `SiegelUpperHalfSpace.IsNotLevelRaised.isNotFromLowerLevel`: not obtained from paramodular forms
  of lower level, a fortiori not from cusp forms of lower level.
* `SiegelUpperHalfSpace.IsNewParamodularEigenform.isParamodularNonliftNewform`: the newforms of
  the knowl satisfy the weaker condition of `SiegelUpperHalfSpace.IsParamodularNonliftNewform`.
* `SiegelUpperHalfSpace.isNewParamodularEigenform_one_iff`: in level `1` the newforms are the
  Hecke eigenforms that are not Maass lifts of Jacobi cusp forms.
-/

open Matrix hiding inv_zpow' zpow_neg

open ModularForm

namespace SiegelUpperHalfSpace

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) ℂ) V)
    (M p : ℕ+) (k : ℤ)

/-- **The slash operator of `GSp(4, ℚ)⁺` of scalar weight `k` preserves holomorphy**:
`f ∣_k β = r(β)^(2k - 3) det(cτ + d)^(-k) f(βτ)` is a constant multiple of the slash operator of
the symplectic matrix `r(β)^(-1/2) β`. This is the hypothesis `hρ` of the level raising operators
for `ρ = det^k`. -/
lemma isHolomorphic_gspSlash_detPowerRep (β : gspPlus (Fin 2))
    (f : SiegelUpperHalfSpace (Fin 2) → ℂ) (hf : IsHolomorphic f) :
    IsHolomorphic (gspSlash (TauCeti.detPowerRep ℂ 2 k) β f) := by
  have h : gspSlash (TauCeti.detPowerRep ℂ 2 k) β f =
      ((multiplier β : ℂ) ^ slashExponent (TauCeti.detPowerRep ℂ 2 k) *
        ((√(multiplier β : ℝ) : ℂ) ^ 2) ^ (-k)) • slash (TauCeti.detPowerRep ℂ 2 k) (toSp β) f := by
    funext τ
    rw [Pi.smul_apply, slash_detPowerRep_apply, gspSlash]
    simp only [gspSmul, TauCeti.detPowerRep_apply, map_inv, inv_zpow', zpow_neg,
      Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, GeneralLinearGroup.val_det_apply,
      coe_gspDenomGL, gspDenom_eq, Complex.coe_smul, det_smul_of_tower, Fintype.card_fin,
      Complex.real_smul, Complex.ofReal_pow]
    rw [mul_zpow, mul_inv]
    ring1
  rw [h]
  exact (hf.slash_detPowerRep (toSp β) k).const_smul _

/-- **The double coset operators between paramodular groups map modular forms to modular forms**,
such as the level raising operators `θ_p`, `θ'_p`, `η_p`, when the slash operator preserves
holomorphy: `F ∣ D = ∑ᵢ F ∣_ρ αᵢ` is holomorphic and `K(N)`-invariant. -/
lemma doubleCosetOperator_mem_modularForms
    (hρ : ∀ α f, IsHolomorphic f → IsHolomorphic (gspSlash ρ α f)) {N : ℕ+}
    (D : HeckeCoset (gspPlusGL (Fin 2)) (heckeGammaOf (paramodularLevel M))
      (heckeGammaOf (paramodularLevel N)))
    {F : slashInvariantsOf ρ (gspPlusGL (Fin 2)) (heckeGammaOf (paramodularLevel M))}
    (hF : (F : SiegelUpperHalfSpace (Fin 2) → V) ∈ modularForms ρ (paramodularLevel M) 1) :
    (doubleCosetOperator ρ D F : SiegelUpperHalfSpace (Fin 2) → V) ∈
      modularForms ρ (paramodularLevel N) 1 := by
  refine (mem_modularForms_iff_slashInvariantsOf ρ _ _).mpr
    ⟨?_, fun γ hγ ↦ (doubleCosetOperator ρ D F).2 γ hγ⟩
  rw [coe_doubleCosetOperator]
  exact Finset.sum_induction _ IsHolomorphic (fun _ _ ↦ IsHolomorphic.add) isHolomorphic_zero
    fun _ _ ↦ hρ _ _ ((mem_modularForms_iff_slashInvariantsOf ρ _ _).mp hF).1

/-- **The image of a composite of level raising operators lies in the image of the last one**: for
`T₂ = [K(M) α K(M')]` and an operator `T₁` from level `M'` to level `N`, the image of `M_ρ(K(M))`
under `T₁ ∘ T₂` lies in the image of `M_ρ(K(M'))` under `T₁`, the operator `T₂` mapping modular
forms to modular forms when the slash operator preserves holomorphy. -/
lemma levelRaisingModularImage_comp_le
    (hρ : ∀ α f, IsHolomorphic f → IsHolomorphic (gspSlash ρ α f)) {M' N : ℕ+}
    (D : HeckeCoset (gspPlusGL (Fin 2)) (heckeGammaOf (paramodularLevel M))
      (heckeGammaOf (paramodularLevel M')))
    (T : slashInvariantsOf ρ (gspPlusGL (Fin 2)) (heckeGammaOf (paramodularLevel M')) →ₗ[ℂ]
      slashInvariantsOf ρ (gspPlusGL (Fin 2)) (heckeGammaOf (paramodularLevel N))) :
    levelRaisingModularImage ρ (T ∘ₗ doubleCosetOperator ρ D) ≤ levelRaisingModularImage ρ T := by
  rintro _ ⟨G, hG, rfl⟩
  exact ⟨doubleCosetOperator ρ D G, doubleCosetOperator_mem_modularForms ρ M hρ D hG, rfl⟩

lemma etaDiag_mul (m : ℕ+) : etaDiag (m * p) = etaDiag m * etaDiag p :=
  Subtype.ext <| Units.ext <| by
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
      simp [etaDiag, diagSimilitude, mul_comm]

/-- **The image of `η_{mp}` lies in the image of `η_p`**: `η_{mp} = η_p ∘ η_m`, the slash operators
of `diag(1, m, 1, m⁻¹)` and `diag(1, p, 1, p⁻¹)` composing to that of `diag(1, mp, 1, (mp)⁻¹)`, and
`η_m` mapping modular forms to modular forms when the slash operator preserves holomorphy. So the
image of the knowl's `U_m`, for any `m`, lies in the image of `U_p` for every prime `p ∣ m`. -/
lemma levelRaisingModularImage_levelRaisingEta_mul_le
    (hρ : ∀ α f, IsHolomorphic f → IsHolomorphic (gspSlash ρ α f)) (m : ℕ+) :
    levelRaisingModularImage ρ (levelRaisingEta ρ M (m * p)) ≤
      levelRaisingModularImage ρ (levelRaisingEta ρ (M * m * m) p) := by
  rintro _ ⟨G, hG, rfl⟩
  refine ⟨levelRaisingEta ρ M m G, doubleCosetOperator_mem_modularForms ρ M hρ _ hG, ?_⟩
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]
  rw [coe_levelRaisingEta, coe_levelRaisingEta, coe_levelRaisingEta, etaDiag_mul,
    heckeMonoidSlash_mul]

lemma paramodularCuspForms_le_slashInvariantsOf : paramodularCuspForms ρ M ≤
    slashInvariantsOf ρ (gspPlusGL (Fin 2)) (heckeGammaOf (paramodularLevel M)) :=
  fun _ hF ↦ modularForms_le_slashInvariantsOf ρ _ hF.1

variable {M} in
/-- An operator `T` from the `K(M)`-invariant to the `K(N)`-invariant functions mapping the cusp
forms `S_ρ(K(M))` to `S_ρ(K(N))`, as a linear map `S_ρ(K(M)) → S_ρ(K(N))`. -/
noncomputable def paramodularCuspFormsMap {N : ℕ+}
    (T : slashInvariantsOf ρ (gspPlusGL (Fin 2)) (heckeGammaOf (paramodularLevel M)) →ₗ[ℂ]
      slashInvariantsOf ρ (gspPlusGL (Fin 2)) (heckeGammaOf (paramodularLevel N)))
    (hT : ∀ F : slashInvariantsOf ρ (gspPlusGL (Fin 2)) (heckeGammaOf (paramodularLevel M)),
      (F : SiegelUpperHalfSpace (Fin 2) → V) ∈ paramodularCuspForms ρ M →
        (T F : SiegelUpperHalfSpace (Fin 2) → V) ∈ paramodularCuspForms ρ N) :
    paramodularCuspForms ρ M →ₗ[ℂ] paramodularCuspForms ρ N :=
  LinearMap.codRestrict _
    ((slashInvariantsOf ρ (gspPlusGL (Fin 2)) (heckeGammaOf (paramodularLevel N))).subtype ∘ₗ T ∘ₗ
      Submodule.inclusion (paramodularCuspForms_le_slashInvariantsOf ρ M)) fun F ↦ hT _ F.2

variable (hρ : ∀ α f, IsHolomorphic f → IsHolomorphic (gspSlash ρ α f))

/-- The **level raising operator** `V_p^+` (LMFDB `mf.siegel.newform.paramodular`) from
`S_ρ(K(M))` to `S_ρ(K(Mp))`, for a prime `p`: the operator `θ_p` of Roberts and Schmidt,
`F ↦ ∑_γ F ∣_ρ diag(p, p, 1, 1) ι(γ)` over `γ ∈ Γ₀(p) \ SL(2, ℤ)`
(`SiegelUpperHalfSpace.coe_paramodularVPlus`), the double coset operator of
`K(M) diag(p, p, 1, 1) K(Mp)`, compatible with the operator `V_p` of Eichler and Zagier on the
Fourier–Jacobi coefficients (Roberts–Schmidt, equation (11), not proved here). Roberts and Schmidt
normalise the slash operator so that scalar matrices act trivially, which multiplies the operator by
a nonzero constant (`p^(3 - k)` for `ρ = det^k`,
`SiegelUpperHalfSpace.rsTheta_eq_smul_levelRaisingThetaPrime`). It is defined when the slash
operator preserves holomorphy (`hρ`), as it does for the holomorphic `ρ` of the LMFDB. The knowl
does not say which of `θ_p`, `θ'_p` it calls `V_p^+`. -/
noncomputable def paramodularVPlus (hp : (p : ℕ).Prime) :
    paramodularCuspForms ρ M →ₗ[ℂ] paramodularCuspForms ρ (M * p) :=
  paramodularCuspFormsMap ρ (levelRaisingThetaPrime ρ M p) fun _ hF ↦
    levelRaisingThetaPrime_mem_paramodularCuspForms ρ M p hp hρ hF

/-- The **level raising operator** `V_p^-` (LMFDB `mf.siegel.newform.paramodular`) from `S_ρ(K(M))`
to `S_ρ(K(Mp))`: the trace `F ↦ ∑ᵢ F ∣_ρ γᵢ` over the right cosets `(K(M) ∩ K(Mp)) γᵢ` of `K(Mp)`
(`SiegelUpperHalfSpace.levelRaisingTheta`), which for a prime `p` is the operator
`θ'_p = u_p θ_p u_p` of Roberts and Schmidt (their equation (16);
`SiegelUpperHalfSpace.rsThetaPrime_eq_levelRaisingTheta` for `ρ = det^k` and `M = q M₀` with `q p`
and `M₀` coprime). It is defined when the slash operator preserves holomorphy (`hρ`). -/
noncomputable def paramodularVMinus :
    paramodularCuspForms ρ M →ₗ[ℂ] paramodularCuspForms ρ (M * p) :=
  paramodularCuspFormsMap ρ (levelRaisingTheta ρ M p) fun _ hF ↦
    levelRaisingTheta_mem_paramodularCuspForms ρ M p hρ hF

/-- The **level raising operator** `U_m` (LMFDB `mf.siegel.newform.paramodular`) from
`S_ρ(K(M))` to `S_ρ(K(Mm²))`: the operator `η_m F = F ∣_ρ η_m⁻¹`, `η_m = diag(1, m⁻¹, 1, m)`, of
Roberts and Schmidt (equation (7), for `m = p` prime), that is
`(U_m F)(τ, z, ω) = ρ(diag(1, m)) F(τ, mz, m²ω)` (`SiegelUpperHalfSpace.coe_paramodularU`),
compatible with the operator `U_m` of Eichler and Zagier on the Fourier–Jacobi coefficients
(Roberts–Schmidt, equation (8), not proved here). It is defined when the slash operator preserves
holomorphy (`hρ`). -/
noncomputable def paramodularU :
    paramodularCuspForms ρ M →ₗ[ℂ] paramodularCuspForms ρ (M * p * p) :=
  paramodularCuspFormsMap ρ (levelRaisingEta ρ M p) fun _ hF ↦
    levelRaisingEta_mem_paramodularCuspForms ρ M p hρ hF

variable (F : paramodularCuspForms ρ M)

/-- **The level raising operator `V_p^+` is `θ_p`**:
`V_p^+ F = ∑_γ F ∣_ρ diag(p, p, 1, 1) ι(γ)` over the representatives `γ = (1, 0; c, 1)`,
`0 ≤ c < p`, and `γ = (0, -1; 1, 0)` of `Γ₀(p) \ SL(2, ℤ)`. -/
lemma coe_paramodularVPlus (hp : (p : ℕ).Prime) :
    (paramodularVPlus ρ M p hρ hp F : SiegelUpperHalfSpace (Fin 2) → V) =
      ∑ i, heckeMonoidSlash ρ (thetaRep p i) F :=
  coe_levelRaisingThetaPrime ρ M p hp _

/-- **The level raising operator `U_m` is the slash operator of `η_m⁻¹ = diag(1, m, 1, m⁻¹)`**. -/
lemma coe_paramodularU : (paramodularU ρ M p hρ F : SiegelUpperHalfSpace (Fin 2) → V) =
    heckeMonoidSlash ρ (etaDiag p) F :=
  coe_levelRaisingEta M p ρ _

lemma coe_paramodularVMinus : (paramodularVMinus ρ M p hρ F : SiegelUpperHalfSpace (Fin 2) → V) =
    levelRaisingTheta ρ M p ⟨F, paramodularCuspForms_le_slashInvariantsOf ρ M F.2⟩ :=
  rfl

variable (N : ℕ+) (f : SiegelUpperHalfSpace (Fin 2) → V)

/-- A function `f : ℋ₂ → V`, such as a paramodular form of level `N`, is **not obtained by level
raising** (LMFDB `mf.siegel.newform.paramodular`): it is not the image of a paramodular form
(a modular form, not necessarily a cusp form, as in the knowl) of level `N / p` under the level
raising operators `V_p^+ = θ_p` or `V_p^- = θ'_p` of Roberts and Schmidt
(`SiegelUpperHalfSpace.levelRaisingThetaPrime`, `SiegelUpperHalfSpace.levelRaisingTheta`), nor of
one of level `N / p²` under `U_p = η_p` (`SiegelUpperHalfSpace.levelRaisingEta`), for a prime `p`.
A composite of these operators from a lower level ends with one of them, applied to a paramodular
form of an intermediate lower level, the operators preserving modular forms when the slash operator
preserves holomorphy (`SiegelUpperHalfSpace.levelRaisingModularImage_comp_le`), as it does for
`ρ = det^k` (`SiegelUpperHalfSpace.isHolomorphic_gspSlash_detPowerRep`); so this also excludes the
images of the composites, and those of `U_m = η_m` for every `m`
(`SiegelUpperHalfSpace.levelRaisingModularImage_levelRaisingEta_mul_le`). This is the knowl's
literal condition, a single operator applied to a single form; Roberts and Schmidt's old space
is the span of these images (`SiegelUpperHalfSpace.paramodularOldModularForms`), and a form outside
it satisfies the condition
(`SiegelUpperHalfSpace.isNotLevelRaised_of_not_mem_paramodularOldModularForms`). -/
def IsNotLevelRaised : Prop :=
  (∀ p : ℕ+, (p : ℕ).Prime → ∀ M : ℕ+, M * p = N →
    f ∉ levelRaisingModularImage ρ (levelRaisingThetaPrime ρ M p) ∧
      f ∉ levelRaisingModularImage ρ (levelRaisingTheta ρ M p)) ∧
    ∀ p : ℕ+, (p : ℕ).Prime → ∀ M : ℕ+, M * p * p = N →
      f ∉ levelRaisingModularImage ρ (levelRaisingEta ρ M p)

variable {M p} in
private lemma not_prime_of_mul_eq_one (h : M * p = 1) : ¬(p : ℕ).Prime := fun hp ↦
  hp.ne_one <| Nat.eq_one_of_mul_eq_one_left (m := (M : ℕ)) (by exact_mod_cast congrArg PNat.val h)

/-- **In level `1` no function is obtained by level raising**, no prime dividing `1`. -/
lemma isNotLevelRaised_one : IsNotLevelRaised ρ 1 f :=
  ⟨fun _ hp _ hM ↦ absurd hp (not_prime_of_mul_eq_one hM),
    fun _ hp _ hM ↦ absurd hp (not_prime_of_mul_eq_one hM)⟩

variable {N f}

/-- **A function not obtained by level raising from paramodular forms is not obtained from cusp
forms** (`SiegelUpperHalfSpace.IsNotFromLowerLevel`), the cusp forms being modular forms. -/
lemma IsNotLevelRaised.isNotFromLowerLevel (hf : IsNotLevelRaised ρ N f) :
    IsNotFromLowerLevel ρ N f :=
  ⟨fun p hp M hM ↦
    ⟨fun h ↦ (hf.1 p hp M hM).2 (levelRaisingImage_le_levelRaisingModularImage ρ _ h),
      fun h ↦ (hf.1 p hp M hM).1 (levelRaisingImage_le_levelRaisingModularImage ρ _ h)⟩,
    fun p hp M hM h ↦ hf.2 p hp M hM (levelRaisingImage_le_levelRaisingModularImage ρ _ h)⟩

/-- **A modular form of level `N` which is not old is not obtained by level raising**: its images
under the level raising operators of modular forms of lower level are old forms
(`SiegelUpperHalfSpace.paramodularOldModularForms`, Roberts and Schmidt's `M_k^old(N)`). -/
lemma isNotLevelRaised_of_not_mem_paramodularOldModularForms
    (hf : f ∈ modularForms ρ (paramodularLevel N) 1) (hold : f ∉ paramodularOldModularForms ρ N) :
    IsNotLevelRaised ρ N f := by
  refine ⟨fun p hp M hM ↦ ⟨fun h ↦ hold ?_, fun h ↦ hold ?_⟩, fun p hp M hM h ↦ hold ?_⟩ <;>
  [refine Submodule.mem_sup_left <| Submodule.mem_iSup_of_mem p <| Submodule.mem_iSup_of_mem hp <|
      Submodule.mem_iSup_of_mem M <| Submodule.mem_iSup_of_mem hM <|
        Submodule.mem_sup_right ?_;
    refine Submodule.mem_sup_left <| Submodule.mem_iSup_of_mem p <| Submodule.mem_iSup_of_mem hp <|
      Submodule.mem_iSup_of_mem M <| Submodule.mem_iSup_of_mem hM <|
        Submodule.mem_sup_left ?_;
    refine Submodule.mem_sup_right <| Submodule.mem_iSup_of_mem p <|
      Submodule.mem_iSup_of_mem hp <| Submodule.mem_iSup_of_mem M <|
        Submodule.mem_iSup_of_mem hM ?_] <;>
  exact Submodule.mem_inf.mpr ⟨hf, h⟩

variable (N)

/-- A **paramodular newform** (LMFDB `mf.siegel.newform.paramodular`) of weight `k` and level
`N`: a Hecke eigenform `G` on the paramodular group `K(N)` (`SiegelUpperHalfSpace.IsHeckeEigenform`,
an eigenvector of every Hecke operator of `K(N)`) which is not a Gritsenko lift
(`SiegelUpperHalfSpace.IsGritsenkoLift`) and not the image of a paramodular form of lower level
under a level raising operator `V_p^± ∈ {θ_p, θ'_p}` or `U_p = η_p` of Roberts and Schmidt
(`SiegelUpperHalfSpace.IsNotLevelRaised`). As in the knowl, `G` is a paramodular form, not required
to be a cusp form, and the forms of lower level are paramodular forms. -/
def IsNewParamodularEigenform (G : slashInvariantsOf (TauCeti.detPowerRep ℂ 2 k)
    (heckeMonoidOf (paramodularLevel N)) (heckeGammaOf (paramodularLevel N))) : Prop :=
  IsHeckeEigenform (TauCeti.detPowerRep ℂ 2 k) G ∧ ¬IsGritsenkoLift k N G ∧
    IsNotLevelRaised (TauCeti.detPowerRep ℂ 2 k) N G

variable {N k} in
/-- **A paramodular newform of the knowl satisfies the weaker condition of
`SiegelUpperHalfSpace.IsParamodularNonliftNewform`**, which only excludes images of cusp forms of
lower level. -/
lemma IsNewParamodularEigenform.isParamodularNonliftNewform
    {G : slashInvariantsOf (TauCeti.detPowerRep ℂ 2 k) (heckeMonoidOf (paramodularLevel N))
      (heckeGammaOf (paramodularLevel N))} (hG : IsNewParamodularEigenform k N G) :
    IsParamodularNonliftNewform k N G :=
  ⟨hG.1, hG.2.1, hG.2.2.isNotFromLowerLevel _⟩

variable {k} in
/-- **The paramodular newforms of level `1`** (LMFDB `mf.siegel.newform.paramodular`) are the
Hecke eigenforms of weight `k` on `K(1) = Sp(4, ℤ)` that are not Maass lifts of Jacobi cusp forms
of index `1`, that is, not Saito–Kurokawa lifts: in level `1` there is no lower level. -/
lemma isNewParamodularEigenform_one_iff (G : slashInvariantsOf (TauCeti.detPowerRep ℂ 2 k)
    (heckeMonoidOf (paramodularLevel 1)) (heckeGammaOf (paramodularLevel 1))) :
    IsNewParamodularEigenform k 1 G ↔ IsHeckeEigenform (TauCeti.detPowerRep ℂ 2 k) G ∧
      ¬∃ φ ∈ jacobiCuspFormSpace k 1, (G : SiegelUpperHalfSpace (Fin 2) → ℂ) = maassLift k φ := by
  rw [IsNewParamodularEigenform, isGritsenkoLift_one_iff, and_iff_left (isNotLevelRaised_one _ _)]

end SiegelUpperHalfSpace
