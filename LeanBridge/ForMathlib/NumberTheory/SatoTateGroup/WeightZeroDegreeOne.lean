import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.Rational
import TauCeti.LinearAlgebra.Trace.Idempotent
import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Character
import TauCeti.RepresentationTheory.Compact.Finite

/-!
# The rational Sato–Tate groups of weight `0` and degree `1`

The Sato–Tate groups of weight `0` and degree `1` that the LMFDB uses are the finite subgroups
`μ(n)` of the unitary group `U(1)`, one for each number `n` of components (LMFDB
`st_group.label`); in LeanBridge's `SatoTateGroup`, whose groups of even weight lie in
`O(1) = {±1}`, only `μ(1)` and `μ(2)` occur (a recorded issue of LMFDB `st_group.definition`). Only
two of them are rational (LMFDB `rcs.cande.st_group`). Every component of a finite group is a
point, so a finite subgroup `K` of `U(1)` is rational (`SatoTateGroup.IsRationalSubgroup`) when the
irreducible characters of `GL₁(ℂ)` take integer values on `K`. These characters are those of Tau
Ceti's rational Weyl modules, and for `GL₁` the character of the one of weight `(k)` is `g ↦ gᵏ`
(`TauCeti.character_rationalWeylRep_fin_one`). For `k = 1` an element of `K` is then an integer of
absolute value `1`, so `K` lies in `O(1) = {±1}`. Conversely the character of every
finite-dimensional representation of `GL₁(ℂ)` is an integer at `±1`, as `-1` acts as an involution,
whose trace is an integer. The rational ones are therefore the trivial group `μ(1)` and
`O(1) = μ(2)`, whichever representations of `GL₁(ℂ)` are counted as its irreducible characters, as
long as the identity character `g ↦ g` is one; and every Sato–Tate group of weight `0` and degree
`1` in LeanBridge's sense is rational.

## Main results

* `TauCeti.character_rationalWeylRep_fin_one`: the character of the rational Weyl module of a
  dominant weight `(k)` of `GL₁(ℂ)` is `g ↦ det g ^ k`.
* `SatoTateGroup.le_ambientGroup_zero_one_iff`: the subgroups of `O(1)` are `1` and `O(1)`.
* `SatoTateGroup.exists_setIntegral_character_div_eq_intCast`: a subgroup of `O(1) = {±1}`
  satisfies the rationality condition for every finite-dimensional representation of `GL₁(ℂ)`.
* `SatoTateGroup.isRationalSubgroup_iff_le_ambientGroup` (LMFDB `rcs.cande.st_group`): a finite
  subgroup of `U(1)` is rational exactly when it lies in `O(1) = {±1}`.
* `SatoTateGroup.setOf_isRationalSubgroup_eq` and `SatoTateGroup.ncard_setOf_isRationalSubgroup`
  (LMFDB `rcs.cande.st_group`): the rational Sato–Tate groups of weight `0` and degree `1` are the
  two groups `μ(1) = 1` and `μ(2) = O(1)`.
* `SatoTateGroup.isRational_of_weight_eq_zero_of_degree_eq_one`: every Sato–Tate group of weight
  `0` and degree `1` in LeanBridge's sense is rational.
-/

open Matrix MeasureTheory TauCeti

namespace TauCeti

/-- **The rational Weyl modules of `GL₁(ℂ)` are the characters `g ↦ det g ^ k`**: the polynomial
part of a dominant weight `(k)` of `GL₁` is the empty diagram, whose Weyl module is the trivial
representation, so the character of its determinant twist is `det g ^ k`. -/
lemma character_rationalWeylRep_fin_one (l : DominantWeight 1) (g : GL (Fin 1) ℂ) :
    Representation.character (V := (weylModuleOfShape ℂ 1 l.detShiftShape).toSubmodule)
      (rationalWeylRep ℂ 1 l) g = (GeneralLinearGroup.det g ^ l.detShift : ℂˣ) := by
  have hcol : l.detShiftShape.colLen 0 = 0 := by
    have h : l.detShiftShape.colLen 0 ≤ 1 - 1 := l.colLen_zero_detShiftShape_le_pred
    omega
  have hcard : l.detShiftShape.card = 0 :=
    Finset.card_eq_zero.mpr <| Finset.eq_empty_of_forall_notMem fun ⟨i, j⟩ hc ↦ by
      have h : i < l.detShiftShape.colLen 0 := YoungDiagram.mem_iff_lt_colLen.mp
        (l.detShiftShape.up_left_mem le_rfl (Nat.zero_le j) hc)
      omega
  have hg : diagGL (fun _ : Fin 1 ↦ GeneralLinearGroup.det g) = g :=
    Units.ext <| Matrix.ext fun i j ↦ by
      fin_cases i
      fin_cases j
      simp
  have hW : Representation.character (V := (weylModuleOfShape ℂ 1 l.detShiftShape).toSubmodule)
      (weylRepOfShape ℂ 1 l.detShiftShape) g = 1 := by
    rw [← hg, char_weylRepOfShape_diagonal_of_colLen_le_one ℂ 1 _ (hcol.trans_le zero_le_one),
      diagramSchurPoly_eq_hsymm_of_colLen_le_one (hcol.trans_le zero_le_one), hcard,
      MvPolynomial.hsymm_zero, map_one]
  rw [char_rationalWeylRep, hW, mul_one]

end TauCeti

namespace SatoTateGroup

variable {A B : unitaryGroup (Fin 1) ℂ} {K : Subgroup (unitaryGroup (Fin 1) ℂ)}

private lemma ext_of_apply_zero_zero_eq
    (h : (A : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = (B : Matrix (Fin 1) (Fin 1) ℂ) 0 0) : A = B :=
  Subtype.ext <| Matrix.ext fun i j ↦ by
    rwa [Subsingleton.elim i 0, Subsingleton.elim j 0]

variable (A) in
lemma mem_ambientGroup_zero_one_iff_mul_self_eq_one : A ∈ ambientGroup 0 1 ↔
    (A : Matrix (Fin 1) (Fin 1) ℂ) 0 0 * (A : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = 1 := by
  rw [mem_ambientGroup, ambientForm_of_even ⟨0, rfl⟩, Matrix.mul_one]
  refine ⟨fun h ↦ ?_, fun h ↦ Matrix.ext fun i j ↦ ?_⟩
  · simpa [Matrix.mul_apply] using Matrix.ext_iff.mpr h 0 0
  · rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
    simpa [Matrix.mul_apply] using h

variable (A) in
lemma mem_ambientGroup_zero_one_iff : A ∈ ambientGroup 0 1 ↔ A = 1 ∨ A = -1 := by
  rw [mem_ambientGroup_zero_one_iff_mul_self_eq_one, mul_self_eq_one_iff]
  exact or_congr ⟨fun h ↦ ext_of_apply_zero_zero_eq (by simpa using h), fun h ↦ by simp [h]⟩
    ⟨fun h ↦ ext_of_apply_zero_zero_eq (by simpa [Unitary.coe_neg] using h),
      fun h ↦ by simp [h, Unitary.coe_neg]⟩

variable (K) in
/-- **The subgroups of `O(1) = {±1}` are `1` and `O(1)`.** -/
lemma le_ambientGroup_zero_one_iff : K ≤ ambientGroup 0 1 ↔ K = ⊥ ∨ K = ambientGroup 0 1 := by
  refine ⟨fun h ↦ ?_, by rintro (rfl | rfl); exacts [bot_le, le_rfl]⟩
  by_cases hneg : -1 ∈ K
  · refine Or.inr (le_antisymm h fun A hA ↦ ?_)
    rcases (mem_ambientGroup_zero_one_iff A).mp hA with rfl | rfl
    exacts [K.one_mem, hneg]
  · refine Or.inl ((Subgroup.eq_bot_iff_forall K).mpr fun A hA ↦ ?_)
    rcases (mem_ambientGroup_zero_one_iff A).mp (h hA) with rfl | rfl
    exacts [rfl, absurd hA hneg]

private lemma finite_of_le_ambientGroup (h : K ≤ ambientGroup 0 1) : Finite K :=
  ((Set.toFinite {1, -1}).subset fun A hA ↦ (mem_ambientGroup_zero_one_iff A).mp (h hA)).to_subtype

variable [Finite K] {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  (ρ : Representation ℂ (GL (Fin 1) ℂ) V)

private lemma setIntegral_connectedComponent_div [MeasurableSpace K] [BorelSpace K] (f : K → ℂ)
    (g : K) : (∫ x in connectedComponent g, f x ∂haarProb K) /
      ((haarProb K (connectedComponent g)).toReal : ℂ) = f g := by
  rw [connectedComponent_eq_singleton, integral_singleton, ← measureReal_def,
    haarProb_real_singleton, Complex.real_smul,
    mul_div_cancel_left₀ _ (by simpa using (Nat.card_pos (α := K)).ne')]

lemma exists_character_eq_intCast_of_mem_ambientGroup (hA : A ∈ ambientGroup 0 1) :
    ∃ n : ℤ, ρ.character (Unitary.toUnits A) = n := by
  have hsq : ρ (Unitary.toUnits A) ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, ← map_one ρ, ← map_one Unitary.toUnits]
    rcases (mem_ambientGroup_zero_one_iff A).mp hA with rfl | rfl <;> simp
  exact ⟨Module.finrank ℂ V - 2 * Module.finrank ℂ (LinearMap.ker (1 + ρ (Unitary.toUnits A))), by
    rw [Representation.character]
    push_cast
    linear_combination LinearMap.two_mul_finrank_ker_one_add_of_sq_eq_one hsq⟩

/-- **A subgroup of `O(1) = {±1}` satisfies the rationality condition for every representation of
`GL₁(ℂ)`**: the average over each component, a point, of the character of a finite-dimensional
representation `ρ` of `GL₁(ℂ)` is an integer, as `ρ(-1)` is an involution, of trace
`dim V - 2 dim ker(1 + ρ(-1))`. So the rationality of `μ(1)` and `μ(2)` does not depend on which
representations of `GL₁(ℂ)` are counted as its irreducible characters in LMFDB
`st_group.rational`. -/
lemma exists_setIntegral_character_div_eq_intCast [MeasurableSpace K] [BorelSpace K]
    (h : K ≤ ambientGroup 0 1) (g : K) : ∃ n : ℤ, (∫ x in connectedComponent g,
      ρ.character (Unitary.toUnits (x : unitaryGroup (Fin 1) ℂ)) ∂haarProb K) /
        ((haarProb K (connectedComponent g)).toReal : ℂ) = n := by
  rw [setIntegral_connectedComponent_div]
  exact exists_character_eq_intCast_of_mem_ambientGroup ρ (h g.2)

/-- **A finite subgroup of `U(1)` is rational exactly when it lies in `O(1) = {±1}`** (LMFDB
`rcs.cande.st_group`): its components are points, where the character `g ↦ g` of `GL₁(ℂ)` must
take integer values, and an integer of absolute value `1` is `±1`; conversely every character of
`GL₁(ℂ)` is an integer at `±1`. -/
lemma isRationalSubgroup_iff_le_ambientGroup (hK : IsClosed (K : Set (unitaryGroup (Fin 1) ℂ))) :
    IsRationalSubgroup K hK ↔ K ≤ ambientGroup 0 1 := by
  let _ : MeasurableSpace K := borel K
  have _ : BorelSpace K := ⟨rfl⟩
  refine ⟨fun h A hA ↦ ?_, fun h l g ↦ exists_setIntegral_character_div_eq_intCast _ h g⟩
  rcases h ⟨fun _ ↦ 1, fun _ _ _ ↦ le_rfl⟩ ⟨A, hA⟩ with ⟨n, hn⟩
  rw [setIntegral_connectedComponent_div, character_rationalWeylRep_fin_one,
    Units.val_zpow_eq_zpow_val, GeneralLinearGroup.val_det_apply, Matrix.det_fin_one] at hn
  have hn' : (A : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = n := by
    simpa using hn
  have hu : star ((A : Matrix (Fin 1) (Fin 1) ℂ) 0 0) * (A : Matrix (Fin 1) (Fin 1) ℂ) 0 0 = 1 := by
    simpa [Matrix.mul_apply] using Matrix.ext_iff.mpr (Unitary.star_mul_self_of_mem A.2) 0 0
  rw [hn', star_intCast] at hu
  rwa [mem_ambientGroup_zero_one_iff_mul_self_eq_one, hn']

/-- **The two rational Sato–Tate groups of weight `0` and degree `1`** (LMFDB
`rcs.cande.st_group`): the finite subgroups of `U(1)` that are rational are the trivial group
`μ(1)` and `O(1) = μ(2) = {±1}`. -/
lemma setOf_isRationalSubgroup_eq : {K : Subgroup (unitaryGroup (Fin 1) ℂ) | Finite K ∧
    ∃ hK : IsClosed (K : Set (unitaryGroup (Fin 1) ℂ)), IsRationalSubgroup K hK} =
      {⊥, ambientGroup 0 1} := by
  ext K
  simp only [Set.mem_insert_iff]
  refine ⟨fun ⟨_, hK, h⟩ ↦ (le_ambientGroup_zero_one_iff K).mp
    ((isRationalSubgroup_iff_le_ambientGroup hK).mp h), fun h ↦ ?_⟩
  have hle : K ≤ ambientGroup 0 1 := (le_ambientGroup_zero_one_iff K).mpr h
  have _ : Finite K := finite_of_le_ambientGroup hle
  exact ⟨inferInstance, (Set.toFinite _).isClosed,
    (isRationalSubgroup_iff_le_ambientGroup _).mpr hle⟩

/-- **There are exactly two rational Sato–Tate groups of weight `0` and degree `1`** (LMFDB
`rcs.cande.st_group`). -/
lemma ncard_setOf_isRationalSubgroup : {K : Subgroup (unitaryGroup (Fin 1) ℂ) | Finite K ∧
    ∃ hK : IsClosed (K : Set (unitaryGroup (Fin 1) ℂ)), IsRationalSubgroup K hK}.ncard = 2 := by
  rw [setOf_isRationalSubgroup_eq, Set.ncard_pair]
  intro h
  have hneg : (-1 : unitaryGroup (Fin 1) ℂ) = 1 :=
    Subgroup.mem_bot.mp (h ▸ (mem_ambientGroup_zero_one_iff _).mpr (Or.inr rfl))
  have h₀ : ((-1 : unitaryGroup (Fin 1) ℂ) : Matrix (Fin 1) (Fin 1) ℂ) 0 0 =
      ((1 : unitaryGroup (Fin 1) ℂ) : Matrix (Fin 1) (Fin 1) ℂ) 0 0 := by
    rw [hneg]
  norm_num [Unitary.coe_neg] at h₀

/-- **Every Sato–Tate group of weight `0` and degree `1` is rational**, in LeanBridge's sense, where
it is a subgroup of `O(1) = {±1}`. -/
lemma isRational_of_weight_eq_zero_of_degree_eq_one (G : SatoTateGroup) (hw : G.weight = 0)
    (hd : G.degree = 1) : G.IsRational := by
  revert hw hd
  rcases G with ⟨w, d, -, K, hK, hle⟩
  rintro rfl rfl
  have _ : Finite K := finite_of_le_ambientGroup hle
  exact (isRationalSubgroup_iff_le_ambientGroup hK).mpr hle

end SatoTateGroup
