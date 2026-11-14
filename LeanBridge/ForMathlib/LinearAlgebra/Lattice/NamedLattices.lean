import LeanBridge.ForMathlib.LinearAlgebra.Lattice.Dual
import LeanBridge.ForMathlib.LinearAlgebra.Lattice.RootSublattice
import TauCeti.LinearAlgebra.IntegralLattice.Dual.Basic
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.Basic
import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeE.Basic

/-!
# The named lattices of the LMFDB

Some integral lattices have names in the LMFDB (LMFDB `lattice.name`): the root lattices `A₂`, …,
`A₁₄`, `D₃ = A₃` and `E₈`, the dual `A₃* = D₃*` of a root lattice, the square lattices `ℤ²` and
`ℤ³`, and the Leech lattice. They are Tau Ceti's `TauCeti.IntegralLattice.typeARootLattice`, its
checkerboard lattice `TauCeti.IntegralLattice.checkerboardLattice` (the root lattice `Dₙ` for
`n ≥ 4`, and `D₃` for `n = 3`), `TauCeti.IntegralLattice.typeE₈RootLattice`,
`TauCeti.IntegralLattice.unitLattice` and the Leech lattice `TauCeti.leechLattice` (on Tau Ceti's
main branch). As the lattices of the LMFDB are integral, its dual of a root lattice is the rescaled
dual `TauCeti.IntegralLattice.rescaledDual` (LMFDB `lattice.dual`): the dual of `A₃`, with the
form of `A₃`, has vectors of norm `3 / 4`.

This file proves the two identifications in the names. The checkerboard lattice `D₃` has the
`ℤ`-basis `(0, 1, -1)`, `(1, -1, 0)`, `(0, 1, 1)`, whose Gram matrix is the Cartan matrix of `A₃`,
so `D₃` and `A₃` are isometric. An isometry of lattices, which is an isometry of their ambient
rational quadratic spaces, maps the dual onto the dual, so the duals of `A₃` and `D₃` correspond;
for nondegenerate lattices it also preserves the dual scale, so it induces an isometry of the
rescaled duals: `A₃*` and `D₃*` are isometric. The file also shows that `D₃` and `E₈` are root
lattices in the sense of LMFDB `lattice.root_sublattice`, as `Aₙ` is
(`TauCeti.IntegralLattice.isRootLattice_typeARootLattice`): they are positive definite and generated
by vectors of norm `2`.

## Main definitions

* `TauCeti.IntegralLattice.checkerboardThreeBasis`: a `ℤ`-basis of `D₃` of three roots.
* `TauCeti.IntegralLattice.typeAThreeIsometryCheckerboardLattice` (LMFDB `lattice.name`): the
  isometry `A₃ ≃ D₃`.
* `TauCeti.IntegralLattice.Isometry.rescaledDual`: the isometry of rescaled duals induced by an
  isometry.
* `TauCeti.IntegralLattice.typeAThreeRescaledDualIsometry` (LMFDB `lattice.name`): the isometry
  `A₃* ≃ D₃*`.

## Main results

* `TauCeti.IntegralLattice.gramMatrix_checkerboardThreeBasis`: the Gram matrix of that basis of
  `D₃` is the Cartan matrix of `A₃`.
* `TauCeti.IntegralLattice.map_dualCarrier_typeAThreeIsometryCheckerboardLattice` (LMFDB
  `lattice.name`): the isometry `A₃ ≃ D₃` maps the dual of `A₃` onto the dual of `D₃`.
* `TauCeti.IntegralLattice.Isometry.dualScale_eq`: isometric lattices have the same dual scale.
* `TauCeti.IntegralLattice.isRootLattice_checkerboardLattice_three` and
  `TauCeti.IntegralLattice.isRootLattice_typeE₈RootLattice`: `D₃` and `E₈` are root lattices.
-/

namespace TauCeti.IntegralLattice

open Module

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {L : IntegralLattice V} {M : IntegralLattice W}

/-! ### `D₃ = A₃` -/

/-- The three roots `(0, 1, -1)`, `(1, -1, 0)` and `(0, 1, 1)` of the checkerboard lattice `D₃`,
with integer coordinates. -/
def checkerboardThreeRootInt : Fin 3 → Fin 3 → ℤ :=
  ![![0, 1, -1], ![1, -1, 0], ![0, 1, 1]]

/-- The three roots `(0, 1, -1)`, `(1, -1, 0)` and `(0, 1, 1)` of the checkerboard lattice `D₃`, in
its ambient space `ℚ³`. -/
def checkerboardThreeRoot (i : Fin 3) : Fin 3 → ℚ :=
  fun j ↦ checkerboardThreeRootInt i j

lemma checkerboardThreeRoot_mem_checkerboardCarrier (i : Fin 3) :
    checkerboardThreeRoot i ∈ checkerboardCarrier 3 :=
  mem_checkerboardCarrier_of (checkerboardThreeRootInt i) (fun _ ↦ rfl) <| by
    fin_cases i <;> decide

lemma linearIndependent_checkerboardThreeRoot : LinearIndependent ℤ checkerboardThreeRoot := by
  refine Fintype.linearIndependent_iff.mpr fun g hg i ↦ ?_
  have h₀ : (g 1 : ℚ) = 0 := by
    simpa [Fin.sum_univ_three, checkerboardThreeRoot, checkerboardThreeRootInt] using congrFun hg 0
  have h₁ : (g 0 : ℚ) - g 1 + g 2 = 0 := by
    simpa [Fin.sum_univ_three, checkerboardThreeRoot, checkerboardThreeRootInt, sub_eq_add_neg]
      using congrFun hg 1
  have h₂ : -(g 0 : ℚ) + g 2 = 0 := by
    simpa [Fin.sum_univ_three, checkerboardThreeRoot, checkerboardThreeRootInt] using congrFun hg 2
  norm_cast at h₀ h₁ h₂
  fin_cases i
  exacts [(by omega : g 0 = 0), h₀, (by omega : g 2 = 0)]

lemma span_range_checkerboardThreeRoot :
    Submodule.span ℤ (Set.range checkerboardThreeRoot) = checkerboardCarrier 3 := by
  refine le_antisymm (Submodule.span_le.mpr ?_) fun x hx ↦ ?_
  · rintro _ ⟨i, rfl⟩
    exact checkerboardThreeRoot_mem_checkerboardCarrier i
  · rcases (mem_checkerboardCarrier_iff x).mp hx with ⟨hint, m, hm⟩
    choose z hz using hint
    rw [Fin.sum_univ_three, hz, hz, hz] at hm
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨![m - z 2, z 0, m], funext fun k ↦ ?_⟩
    fin_cases k <;> simp [Fin.sum_univ_three, checkerboardThreeRoot, checkerboardThreeRootInt, hz]
    linarith

/-- The `ℤ`-basis `(0, 1, -1)`, `(1, -1, 0)`, `(0, 1, 1)` of the checkerboard lattice `D₃`, whose
Gram matrix is the Cartan matrix of `A₃` (`gramMatrix_checkerboardThreeBasis`). -/
noncomputable def checkerboardThreeBasis : Basis (Fin 3) ℤ (checkerboardLattice 3) :=
  (Basis.span linearIndependent_checkerboardThreeRoot).map <| LinearEquiv.ofEq _ _ <| by
    rw [span_range_checkerboardThreeRoot, checkerboardLattice_carrier]

@[simp]
lemma coe_checkerboardThreeBasis_apply (i : Fin 3) :
    (checkerboardThreeBasis i : Fin 3 → ℚ) = checkerboardThreeRoot i := by
  simp [checkerboardThreeBasis]

/-- **The Gram matrix of the basis `(0, 1, -1)`, `(1, -1, 0)`, `(0, 1, 1)` of `D₃` is the Cartan
matrix of `A₃`.** -/
lemma gramMatrix_checkerboardThreeBasis :
    (checkerboardLattice 3).gramMatrix checkerboardThreeBasis = CartanMatrix.A 3 := by
  ext i j
  have h : ((checkerboardLattice 3).gramMatrix checkerboardThreeBasis i j : ℚ) =
      CartanMatrix.A 3 i j := by
    rw [intCast_gramMatrix_apply, coe_checkerboardThreeBasis_apply,
      coe_checkerboardThreeBasis_apply, checkerboardLattice_form_apply]
    fin_cases i <;> fin_cases j <;>
      norm_num [Fin.sum_univ_three, checkerboardThreeRoot, checkerboardThreeRootInt,
        CartanMatrix.A]
  exact_mod_cast h

/-- **`D₃ = A₃`** (LMFDB `lattice.name`): the root lattice `A₃` is isometric to the checkerboard
lattice `D₃`, by the isometry carrying its simple roots to `(0, 1, -1)`, `(1, -1, 0)` and
`(0, 1, 1)`. -/
noncomputable def typeAThreeIsometryCheckerboardLattice :
    Isometry (typeARootLattice 3) (checkerboardLattice 3) :=
  Isometry.ofGramMatrixEq (typeASimpleRootBasis 3) checkerboardThreeBasis <| by
    rw [gramMatrix_typeASimpleRootBasis, gramMatrix_checkerboardThreeBasis]

/-! ### Root lattices -/

private lemma isRootLattice_of_basis {ι : Type*} (hL : L.IsPosDef) (b : Basis ι ℤ L)
    (hb : ∀ i, L.gramMatrix b i i = 2) : L.IsRootLattice := by
  refine ⟨hL, eq_top_iff.mpr <| b.span_eq ▸ Submodule.span_mono ?_⟩
  rintro _ ⟨i, rfl⟩
  exact Or.inr ((mem_vectorsOfNorm_natCast _).mpr <| by
    rw [integralNorm_apply, ← gramMatrix_apply, hb]
    rfl)

/-- **The checkerboard lattice `D₃` is a root lattice**: it is positive definite and generated by
the roots `(0, 1, -1)`, `(1, -1, 0)` and `(0, 1, 1)`. -/
lemma isRootLattice_checkerboardLattice_three : (checkerboardLattice 3).IsRootLattice :=
  isRootLattice_of_basis (isPosDef_checkerboardLattice 3) checkerboardThreeBasis fun i ↦ by
    rw [gramMatrix_checkerboardThreeBasis]
    fin_cases i <;> rfl

/-- **The lattice `E₈` is a root lattice**: it is positive definite and generated by its simple
roots, of norm `2`. -/
lemma isRootLattice_typeE₈RootLattice : typeE₈RootLattice.IsRootLattice :=
  isRootLattice_of_basis isPosDef_typeE₈RootLattice
    (ofGramMatrix.basis (Pi.basisFun ℚ (Fin 8)) (CartanMatrix.E 8) (CartanMatrix.E_isSymm 8))
    fun i ↦ (congrFun₂ (gramMatrix_ofGramMatrix _ _ _) i i).trans <| by fin_cases i <;> rfl

/-! ### `A₃* = D₃*` -/

/-- **`A₃* = D₃*`, for the duals in the ambient spaces** (LMFDB `lattice.name`): the isometry
`A₃ ≃ D₃`, an isometry of the ambient rational quadratic spaces, maps the dual of `A₃` onto the dual
of `D₃`. -/
lemma map_dualCarrier_typeAThreeIsometryCheckerboardLattice : (typeARootLattice 3).dualCarrier.map
    typeAThreeIsometryCheckerboardLattice.ambientEquiv.toLinearMap =
      (checkerboardLattice 3).dualCarrier :=
  typeAThreeIsometryCheckerboardLattice.map_dualCarrier_ambientEquiv

lemma Isometry.dualIntegralityIdeal_le (e : Isometry L M) :
    M.dualIntegralityIdeal ≤ L.dualIntegralityIdeal := fun N hN x hx y hy ↦ by
  rw [← e.map_app]
  exact hN (e x) ((e.apply_mem_dualCarrier_iff x).mpr hx) (e y)
    ((e.apply_mem_dualCarrier_iff y).mpr hy)

/-- **Isometric lattices have the same dual scale**: the integers `N` for which `N • B` is integral
on the dual are the same. -/
lemma Isometry.dualScale_eq (e : Isometry L M) : L.dualScale = M.dualScale := by
  have h (N : ℤ) : (L.dualScale : ℤ) ∣ N ↔ (M.dualScale : ℤ) ∣ N := by
    rw [dualScale_dvd_iff, dualScale_dvd_iff]
    exact ⟨fun hN ↦ e.symm.dualIntegralityIdeal_le hN, fun hN ↦ e.dualIntegralityIdeal_le hN⟩
  exact Nat.dvd_antisymm (Int.natCast_dvd_natCast.mp ((h _).mpr dvd_rfl))
    (Int.natCast_dvd_natCast.mp ((h _).mp dvd_rfl))

variable [L.IsNondegenerate] [M.IsNondegenerate]

/-- **An isometry of nondegenerate lattices induces an isometry of their rescaled duals**
(LMFDB `lattice.dual`): it maps the dual onto the dual, and the two dual scales agree
(`Isometry.dualScale_eq`). -/
noncomputable def Isometry.rescaledDual (e : Isometry L M) :
    Isometry L.rescaledDual M.rescaledDual where
  toIsometryEquiv :=
    { (e : V ≃ₗ[ℚ] W) with
      map_app' := fun x y ↦ by
        simp only [rescaledDual_form, e.dualScale_eq]
        exact congrArg _ (e.map_app x y) }
  map_carrier := e.map_dualCarrier_ambientEquiv

/-- **`A₃* = D₃*`** (LMFDB `lattice.name`): the rescaled duals of the root lattice `A₃` and of the
checkerboard lattice `D₃`, the integral lattices the LMFDB names `A₃*` and `D₃*`, are isometric. -/
noncomputable def typeAThreeRescaledDualIsometry :
    Isometry (typeARootLattice 3).rescaledDual (checkerboardLattice 3).rescaledDual :=
  typeAThreeIsometryCheckerboardLattice.rescaledDual

end TauCeti.IntegralLattice
