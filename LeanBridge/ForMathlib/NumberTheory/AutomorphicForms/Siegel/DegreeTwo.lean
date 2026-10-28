import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ModularForm
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import TauCeti.RepresentationTheory.ClassicalGroups.SymmetricPower

/-!
# Siegel cusp forms of degree 2

Vector-valued Siegel modular forms of degree 2 take values in the irreducible representations
`ρ_{k,j} = det^k ⊗ Sym^j(St)` of `GL(2, ℂ)`. A Siegel modular form `F` of degree 2 and weight `ρ`
on `Γ ≤ Sp(4, ℚ)` is a cusp form if `Φ(F ∣_ρ γ) = 0` for every `γ ∈ Sp(4, ℚ)`, where `∣_ρ` is the
slash operator of `ρ` and `Φ(G)(τ') = lim_{t → ∞} G(diag(τ', it))` is the Siegel operator.

## Main definitions

* `SiegelUpperHalfSpace.rhoKJ`: the representation `ρ_{k,j}` (LMFDB
  `mf.siegel.vector_valued_degree_two`).
* `SiegelUpperHalfSpace.modularFormsKJ`: the space `M_{k,j}(Γ)`.
* `SiegelUpperHalfSpace.SiegelOperatorVanishes`: the Siegel operator `Φ` vanishes on a function.
* `SiegelUpperHalfSpace.IsCuspForm` (LMFDB `mf.siegel.cusp_form_degree2`): cusp forms of degree 2.
* `SiegelUpperHalfSpace.cuspForms` and `SiegelUpperHalfSpace.cuspFormsKJ` (LMFDB
  `mf.siegel.cusp_form_degree2`): the spaces `S_ρ(Γ, ψ)` and `S_{k,j}(Γ)` of degree 2.
-/

open Filter Module
open scoped TensorProduct Topology

namespace SiegelUpperHalfSpace

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) ℂ) V)
    {F G : SiegelUpperHalfSpace (Fin 2) → V} (k : ℤ) (j : ℕ)
    (Γ : Subgroup (Matrix.symplecticGroup (Fin 2) ℚ)) (ψ : Γ →* ℂˣ)

/-- The irreducible representation `ρ_{k,j} = det^k ⊗ Sym^j(St)` of `GL(2, ℂ)` on `Sym^j(ℂ²)`
(LMFDB `mf.siegel.vector_valued_degree_two`), where `St` is the standard representation:
`g` acts by `det(g)^k` times its `j`-th symmetric power. -/
noncomputable def rhoKJ : Representation ℂ (GL (Fin 2) ℂ) (Sym[ℂ]^j (Fin 2 → ℂ)) where
  toFun g := ((g.det ^ k : ℂˣ) : ℂ) • TauCeti.symPowerRep ℂ 2 j g
  map_one' := by simp [End.one_eq_id]
  map_mul' g h := by
    simp only [map_mul, mul_zpow, Units.val_mul, smul_mul_smul_comm]

/-- The point `diag(τ', it)` of the Siegel upper half-space of degree 2, for `τ'` in the upper
half-plane and `t > 0`. -/
def diagPoint (τ' : UpperHalfPlane) (t : Set.Ioi (0 : ℝ)) : SiegelUpperHalfSpace (Fin 2) where
  val := !![(τ' : ℂ), 0; 0, (t : ℝ) * Complex.I]
  transpose_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  posDef_im := by
    have h : (!![(τ' : ℂ), 0; 0, (t : ℝ) * Complex.I]).map Complex.im =
        Matrix.diagonal ![τ'.im, (t : ℝ)] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    rw [h, Matrix.posDef_diagonal_iff]
    intro i
    fin_cases i
    · exact τ'.im_pos
    · exact t.2

variable (F) in
/-- The **Siegel operator** `Φ(F)(τ') = lim_{t → ∞} F(diag(τ', it))` **vanishes** on
`F : ℋ_2 → V`: the limit is `0` for every `τ'` in the upper half-plane. The limit is taken
coordinatewise, through every linear form on `V`, which is the limit in the usual topology when
`V` is finite-dimensional. -/
def SiegelOperatorVanishes : Prop :=
  ∀ (τ' : UpperHalfPlane) (φ : Dual ℂ V), Tendsto (fun t ↦ φ (F (diagPoint τ' t))) atTop (𝓝 0)

lemma siegelOperatorVanishes_zero : SiegelOperatorVanishes (0 : SiegelUpperHalfSpace (Fin 2) → V) :=
  fun τ' φ ↦ by simp

lemma SiegelOperatorVanishes.add (hF : SiegelOperatorVanishes F) (hG : SiegelOperatorVanishes G) :
    SiegelOperatorVanishes (F + G) :=
  fun τ' φ ↦ by simpa using (hF τ' φ).add (hG τ' φ)

lemma SiegelOperatorVanishes.const_smul (hF : SiegelOperatorVanishes F) (c : ℂ) :
    SiegelOperatorVanishes (c • F) :=
  fun τ' φ ↦ by simpa using (hF τ' φ).const_mul c

variable (F) in
/-- A function `F : ℋ_2 → V` is a **cusp form** (LMFDB `mf.siegel.cusp_form_degree2`) of weight
`ρ` if `Φ(F ∣_ρ γ) = 0` for every `γ ∈ Sp(4, ℚ)`, where `∣_ρ` is the slash operator
`(F ∣_ρ γ)(τ) = ρ(cτ + d)⁻¹ F(γτ)` and `Φ` the Siegel operator. -/
def IsCuspForm : Prop :=
  ∀ γ : Matrix.symplecticGroup (Fin 2) ℚ,
    SiegelOperatorVanishes (slash ρ (SymplecticGroup.map (algebraMap ℚ ℝ) γ) F)

/-- The space `S_ρ(Γ, ψ)` of **Siegel cusp forms of degree 2** (LMFDB
`mf.siegel.cusp_form_degree2`) with character `ψ` and weight `ρ` on a subgroup `Γ` of `Sp(4, ℚ)`:
the Siegel modular forms `F ∈ M_ρ(Γ, ψ)` with `Φ(F ∣_ρ γ) = 0` for every `γ ∈ Sp(4, ℚ)`. The LMFDB
allows arithmetic subgroups of `GSp(4, ℚ)`; see `modularForms`. -/
def cuspForms : Submodule ℂ (SiegelUpperHalfSpace (Fin 2) → V) where
  carrier := {F | F ∈ modularForms ρ Γ ψ ∧ IsCuspForm ρ F}
  add_mem' {F G} hF hG := ⟨add_mem hF.1 hG.1, fun γ ↦ by
    rw [slash_add]
    exact (hF.2 γ).add (hG.2 γ)⟩
  zero_mem' := ⟨zero_mem _, fun γ ↦ by
    rw [slash_zero]
    exact siegelOperatorVanishes_zero⟩
  smul_mem' c F hF := ⟨Submodule.smul_mem _ c hF.1, fun γ ↦ by
    rw [slash_smul]
    exact (hF.2 γ).const_smul c⟩

lemma cuspForms_le_modularForms : cuspForms ρ Γ ψ ≤ modularForms ρ Γ ψ :=
  fun _ hF ↦ hF.1

/-- The space `M_{k,j}(Γ)` of **vector-valued Siegel modular forms of degree 2**
(LMFDB `mf.siegel.vector_valued_degree_two`) and weight `ρ_{k,j}` on a subgroup `Γ` of
`Sp(4, ℚ)`. -/
noncomputable abbrev modularFormsKJ :
    Submodule ℂ (SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) :=
  modularForms (rhoKJ k j) Γ 1

/-- The space `S_{k,j}(Γ)` of **Siegel cusp forms of degree 2** (LMFDB
`mf.siegel.cusp_form_degree2`) and weight `ρ_{k,j}` on a subgroup `Γ` of `Sp(4, ℚ)`: the
vector-valued Siegel modular forms `F ∈ M_{k,j}(Γ)` with `Φ(F ∣_{k,j} γ) = 0` for every
`γ ∈ Sp(4, ℚ)`. -/
noncomputable abbrev cuspFormsKJ :
    Submodule ℂ (SiegelUpperHalfSpace (Fin 2) → Sym[ℂ]^j (Fin 2 → ℂ)) :=
  cuspForms (rhoKJ k j) Γ 1

end SiegelUpperHalfSpace
