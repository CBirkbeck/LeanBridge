import LeanBridge.ForMathlib.AlgebraicGeometry.HilbertModularSurface.Label
import LeanBridge.ForMathlib.AlgebraicGeometry.HilbertModularSurface.PolarizationModule
import Mathlib.RingTheory.DedekindDomain.Different

/-!
# The component ideal of a Hilbert modular surface

Let `F` be a real quadratic field. The adelic Hilbert modular surface may be geometrically
reducible, with components in bijection with the narrow class group `Cl⁺(F)`. The component of a
narrow ideal class `[𝔟]` is the Hilbert modular surface of the group `GL⁺(𝒪_F ⊕ 𝔟)`, or of its
congruence subgroups such as `Γ₀(𝔑)_𝔟` (LMFDB `hmsurface.x0`), and `𝔟` is its **component ideal**
(LMFDB `hmsurface.component_ideal`); it parametrizes abelian surfaces with real multiplication by
`𝒪_F` whose polarization module is isomorphic to `(𝔡_F 𝔟)⁻¹`, for the different `𝔡_F` of `F`. The
adelic surface, its components and the moduli interpretation are not available, so the knowl is
formalised through what makes it meaningful:

* the component of `[𝔟]` only depends on the narrow class of `𝔟`: for `t ∈ F^×`, the groups
  `GL⁺(𝒪_F ⊕ t𝔟)`, `SL(𝒪_F ⊕ t𝔟)` and `Γ₀(𝔑)_{t𝔟}` are the conjugates of `GL⁺(𝒪_F ⊕ 𝔟)`,
  `SL(𝒪_F ⊕ 𝔟)` and `Γ₀(𝔑)_𝔟` by `diag(1, t)`, which has totally positive determinant when `t` is
  totally positive, so that two component ideals in the same narrow class give groups that are
  conjugate in `GL₂⁺(F)`, hence isomorphic Hilbert modular surfaces (the isomorphism of the
  surfaces is not formalised);
* the surfaces of the component of `𝔟` are principally polarized if and only if `𝔟` is in the
  narrow class of the inverse different `𝔡_F⁻¹`: a principal polarization generates the
  polarization module (not formalised), which is then isomorphic to `𝒪_F`, and `(𝔡_F 𝔟)⁻¹` is
  isomorphic to `𝒪_F`, with its positive cone, exactly when `[𝔟] = [𝔡_F⁻¹]` in `Cl⁺(F)`.

The knowl says that the component of `[𝔟]` parametrizes abelian surfaces "whose polarization
module is isomorphic to `ℤ_F ⊕ 𝔟`". The polarization module of an abelian surface with real
multiplication by `𝒪_F` has rank one over `𝒪_F`, and LMFDB `hmsurface.x0` and `hmsurface.x01`, as
the knowl's own characterisation of the principally polarized component, give `(𝔡_F 𝔟)⁻¹`: the
lattice `𝒪_F ⊕ 𝔟` is that of the Hilbert modular group, not the polarization module.

The inverse different `𝔡_F⁻¹` is Mathlib's `FractionalIdeal.dual ℤ ℚ 1`, whose inverse is the
different ideal (`coeIdeal_differentIdeal`).

## Main definitions

* `HilbertModularGroup.diagonalOneUnit`: the matrix `diag(1, t)` of `GL₂(F)`.

## Main results

* `HilbertModularGroup.glPlus_spanSingleton_mul`: `GL⁺(𝒪_F ⊕ t𝔟)` is the conjugate of
  `GL⁺(𝒪_F ⊕ 𝔟)` by `diag(1, t)`.
* `HilbertModularGroup.sl_spanSingleton_mul`: `SL(𝒪_F ⊕ t𝔟)` is the conjugate of `SL(𝒪_F ⊕ 𝔟)` by
  `diag(1, t)`.
* `HilbertModularGroup.gammaZero_spanSingleton_mul`: `Γ₀(𝔑)_{t𝔟}` is the conjugate of `Γ₀(𝔑)_𝔟` by
  `diag(1, t)`.
* `HilbertModularGroup.exists_glPlus_eq_map_conj_of_mk_eq`: `GL⁺(𝒪_F ⊕ 𝔟)` only depends on the
  narrow class of `𝔟`, up to conjugation in `GL₂⁺(F)`.
* `HilbertModularGroup.SurfaceType.congruenceSubgroup_spanSingleton_mul`: the congruence subgroup of
  `X_0(𝔑)_{t𝔟}` or `X_0^1(𝔑)_{t𝔟}` is the conjugate of that of `X_0(𝔑)_𝔟` or `X_0^1(𝔑)_𝔟` by
  `diag(1, t)`.
* `HilbertModularGroup.SurfaceType.exists_congruenceSubgroup_eq_map_conj_of_mk_eq`: it only depends
  on the narrow class of `𝔟`, up to conjugation in `GL₂⁺(F)`.
* `HilbertModularGroup.isOrientedIsomorphic_inv_mul_iff`: the polarization module `(𝔡_F 𝔟)⁻¹` is
  isomorphic to `𝒪_F` if and only if `𝔟` is in the narrow class of `𝔡_F⁻¹`.
-/

open Matrix NumberField FractionalIdeal

open scoped nonZeroDivisors Pointwise

namespace HilbertModularGroup

variable {F : Type*} [Field F] (𝔟 : FractionalIdeal (𝓞 F)⁰ F) (G : Subgroup (GL (Fin 2) F))
  (𝔑 : Ideal (𝓞 F)) (t : Fˣ) {g δ : GL (Fin 2) F} {v : Fin 2 → F} {y : F}
  {L L' : Submodule (𝓞 F) (Fin 2 → F)}

/-- The matrix `diag(1, t)` of `GL₂(F)`, for `t ∈ Fˣ`, which maps the lattice `𝒪_F ⊕ 𝔟` of `F²` to
`𝒪_F ⊕ t𝔟`. -/
noncomputable def diagonalOneUnit : GL (Fin 2) F :=
  haveI h : diagonal ![1, (t : F)] * diagonal ![1, ((t⁻¹ : Fˣ) : F)] = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp
  ⟨diagonal ![1, (t : F)], diagonal ![1, ((t⁻¹ : Fˣ) : F)], h, mul_eq_one_comm.mp h⟩

lemma det_diagonalOneUnit : (diagonalOneUnit t).det = t :=
  Units.ext <| by simp [diagonalOneUnit]

lemma det_inv_mul_mul : (δ⁻¹ * g * δ).det = g.det := by
  rw [map_mul, map_mul, map_inv, mul_comm _ δ.det, mul_inv_cancel_left]

lemma forall_mem_iff_mulVec_mem_iff (hL : ∀ v, v ∈ L' ↔ (δ⁻¹).val *ᵥ v ∈ L) :
    (∀ v, v ∈ L' ↔ g.val *ᵥ v ∈ L') ↔ ∀ w, w ∈ L ↔ (δ⁻¹ * g * δ).val *ᵥ w ∈ L := by
  refine ⟨fun hg w ↦ ?_, fun hg v ↦ ?_⟩
  · have h : δ.val *ᵥ w ∈ L' ↔ g.val *ᵥ (δ.val *ᵥ w) ∈ L' := hg (δ.val *ᵥ w)
    rwa [hL, hL, mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec,
      mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul] at h
  · have h : (δ⁻¹).val *ᵥ v ∈ L ↔ (δ⁻¹ * g * δ).val *ᵥ ((δ⁻¹).val *ᵥ v) ∈ L := hg _
    rwa [mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right, Units.val_mul, ← mulVec_mulVec,
      ← hL, ← hL] at h

variable [NumberField F] {I J : (FractionalIdeal (𝓞 F)⁰ F)ˣ}

lemma mem_spanSingleton_mul_iff : y ∈ spanSingleton (𝓞 F)⁰ (t : F) * 𝔟 ↔ (t : F)⁻¹ * y ∈ 𝔟 := by
  rw [mem_singleton_mul]
  refine ⟨?_, fun h ↦ ⟨_, h, by field_simp⟩⟩
  rintro ⟨y', hy', rfl⟩
  simpa using hy'

lemma mem_smul_spanSingleton_mul_iff :
    y ∈ 𝔑 • ((spanSingleton (𝓞 F)⁰ (t : F) * 𝔟 : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) ↔
      (t : F)⁻¹ * y ∈ 𝔑 • (𝔟 : Submodule (𝓞 F) F) := by
  rw [coe_mul, coe_spanSingleton, Submodule.span_singleton_mul, Submodule.pointwise_smul_def,
    ← Submodule.map_smul'', ← Submodule.pointwise_smul_def,
    Submodule.mem_smul_iff_inv_mul_mem t.ne_zero]

lemma mem_lattice_spanSingleton_mul_iff : v ∈ lattice (spanSingleton (𝓞 F)⁰ (t : F) * 𝔟) ↔
    ((diagonalOneUnit t)⁻¹).val *ᵥ v ∈ lattice 𝔟 := by
  rw [mem_lattice, mem_lattice, mem_spanSingleton_mul_iff]
  simp [diagonalOneUnit, mulVec_diagonal]

lemma mem_gammaZeroLattice_spanSingleton_mul_iff :
    v ∈ gammaZeroLattice (spanSingleton (𝓞 F)⁰ (t : F) * 𝔟) 𝔑 ↔
      ((diagonalOneUnit t)⁻¹).val *ᵥ v ∈ gammaZeroLattice 𝔟 𝔑 := by
  rw [mem_gammaZeroLattice, mem_gammaZeroLattice, mem_smul_spanSingleton_mul_iff]
  simp [diagonalOneUnit, mulVec_diagonal]

lemma mem_gl_spanSingleton_mul_iff : g ∈ gl (spanSingleton (𝓞 F)⁰ (t : F) * 𝔟) ↔
    (diagonalOneUnit t)⁻¹ * g * diagonalOneUnit t ∈ gl 𝔟 :=
  forall_mem_iff_mulVec_mem_iff fun _ ↦ mem_lattice_spanSingleton_mul_iff 𝔟 t

/-- **Changing the component ideal `𝔟` to `t𝔟` conjugates `GL⁺(𝒪_F ⊕ 𝔟)` by `diag(1, t)`**:
`GL⁺(𝒪_F ⊕ t𝔟) = diag(1, t) GL⁺(𝒪_F ⊕ 𝔟) diag(1, t)⁻¹`. -/
lemma glPlus_spanSingleton_mul : glPlus (spanSingleton (𝓞 F)⁰ (t : F) * 𝔟) =
    (glPlus 𝔟).map (MulAut.conj (diagonalOneUnit t)).toMonoidHom := by
  ext g
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, glPlus, glPlus, Subgroup.mem_inf,
    Subgroup.mem_inf, mem_gl_spanSingleton_mul_iff, Subgroup.mem_comap, Subgroup.mem_comap,
    det_inv_mul_mul]

/-- **Changing the component ideal `𝔟` to `t𝔟` conjugates `SL(𝒪_F ⊕ 𝔟)` by `diag(1, t)`**:
`SL(𝒪_F ⊕ t𝔟) = diag(1, t) SL(𝒪_F ⊕ 𝔟) diag(1, t)⁻¹`. -/
lemma sl_spanSingleton_mul : sl (spanSingleton (𝓞 F)⁰ (t : F) * 𝔟) =
    (sl 𝔟).map (MulAut.conj (diagonalOneUnit t)).toMonoidHom := by
  ext g
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, sl, sl, Subgroup.mem_inf,
    Subgroup.mem_inf, mem_gl_spanSingleton_mul_iff, MonoidHom.mem_ker, MonoidHom.mem_ker,
    det_inv_mul_mul]

/-- **Changing the component ideal `𝔟` to `t𝔟` conjugates `Γ₀(𝔑)_𝔟` by `diag(1, t)`**, the
Hilbert modular group `G` of `𝒪_F ⊕ 𝔟` being replaced by its conjugate. -/
lemma gammaZero_spanSingleton_mul : gammaZero (spanSingleton (𝓞 F)⁰ (t : F) * 𝔟)
    (G.map (MulAut.conj (diagonalOneUnit t)).toMonoidHom) 𝔑 =
      (gammaZero 𝔟 G 𝔑).map (MulAut.conj (diagonalOneUnit t)).toMonoidHom := by
  ext g
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  exact and_congr (by rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]) <|
    forall_mem_iff_mulVec_mem_iff fun _ ↦ mem_gammaZeroLattice_spanSingleton_mul_iff 𝔟 𝔑 t

lemma exists_eq_map_conj_of_mk_eq (Φ : FractionalIdeal (𝓞 F)⁰ F → Subgroup (GL (Fin 2) F))
    (hΦ : ∀ 𝔟 (t : Fˣ), Φ (spanSingleton (𝓞 F)⁰ (t : F) * 𝔟) =
      (Φ 𝔟).map (MulAut.conj (diagonalOneUnit t)).toMonoidHom)
    (h : NarrowClassGroup.mk I = NarrowClassGroup.mk J) :
    ∃ δ ∈ totallyPositiveUnits.comap GeneralLinearGroup.det, Φ J.val =
      (Φ I.val).map (MulAut.conj δ).toMonoidHom := by
  rcases NarrowClassGroup.mk_eq_mk_iff.mp h with ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  refine ⟨diagonalOneUnit x, by rwa [Subgroup.mem_comap, det_diagonalOneUnit], ?_⟩
  rw [Units.val_mul, coe_toPrincipalIdeal, mul_comm, hΦ]

/-- **The Hilbert modular group `GL⁺(𝒪_F ⊕ 𝔟)` only depends on the narrow ideal class of the
component ideal `𝔟`, up to conjugation in `GL₂⁺(F)`**: if `I` and `J` have the same class in the
narrow class group, then `GL⁺(𝒪_F ⊕ J) = δ GL⁺(𝒪_F ⊕ I) δ⁻¹` for some `δ ∈ GL₂(F)` with totally
positive determinant, which induces an isomorphism of the two Hilbert modular surfaces (not
formalised). -/
lemma exists_glPlus_eq_map_conj_of_mk_eq (h : NarrowClassGroup.mk I = NarrowClassGroup.mk J) :
    ∃ δ ∈ totallyPositiveUnits.comap GeneralLinearGroup.det, glPlus J.val =
      (glPlus I.val).map (MulAut.conj δ).toMonoidHom :=
  exists_eq_map_conj_of_mk_eq glPlus (glPlus_spanSingleton_mul · ·) h

variable (I) in
/-- **The polarization module `(𝔡_F 𝔟)⁻¹` of the component of `𝔟` is isomorphic to `𝒪_F`, with its
positive cone, if and only if `𝔟` is in the narrow ideal class of the inverse different
`𝔡_F⁻¹`**: the knowl's characterisation of the components whose abelian surfaces are principally
polarized, a principal polarization generating the polarization module (not formalised). Here the
different `𝔡_F` is the inverse of Mathlib's `FractionalIdeal.dual ℤ ℚ 1`. -/
lemma isOrientedIsomorphic_inv_mul_iff :
    letI 𝔡 : (FractionalIdeal (𝓞 F)⁰ F)ˣ :=
      (Units.mk0 (dual ℤ ℚ 1) (dual_ne_zero ℤ ℚ one_ne_zero))⁻¹
    ((𝔡 * I)⁻¹).val.IsOrientedIsomorphic {x : 𝓞 F | IsTotallyPositive (x : F)} ↔
      NarrowClassGroup.mk I = NarrowClassGroup.mk 𝔡⁻¹ := by
  rw [isOrientedIsomorphic_iff_mk_eq_one, map_inv, inv_eq_one, map_mul, mul_eq_one_iff_inv_eq,
    ← map_inv]
  exact eq_comm

namespace SurfaceType

variable (s : SurfaceType)

lemma group_spanSingleton_mul : s.group (spanSingleton (𝓞 F)⁰ (t : F) * 𝔟) =
    (s.group 𝔟).map (MulAut.conj (diagonalOneUnit t)).toMonoidHom := by
  cases s
  · exact sl_spanSingleton_mul 𝔟 t
  · exact glPlus_spanSingleton_mul 𝔟 t

/-- **Changing the component ideal `𝔟` to `t𝔟` conjugates the congruence subgroups `Γ₀¹(𝔑)_𝔟` and
`Γ₀(𝔑)_𝔟` of the surfaces `X_0^1(𝔑)_𝔟` and `X_0(𝔑)_𝔟` by `diag(1, t)`.** -/
lemma congruenceSubgroup_spanSingleton_mul :
    s.congruenceSubgroup (spanSingleton (𝓞 F)⁰ (t : F) * 𝔟) 𝔑 =
      (s.congruenceSubgroup 𝔟 𝔑).map (MulAut.conj (diagonalOneUnit t)).toMonoidHom := by
  rw [congruenceSubgroup, congruenceSubgroup, group_spanSingleton_mul, gammaZero_spanSingleton_mul]

/-- **The congruence subgroups `Γ₀¹(𝔑)_𝔟` and `Γ₀(𝔑)_𝔟` only depend on the narrow ideal class of
the component ideal `𝔟`, up to conjugation in `GL₂⁺(F)`**, so that the surfaces `X_0^1(𝔑)_𝔟` and
`X_0(𝔑)_𝔟` only depend on it up to isomorphism (not formalised). -/
lemma exists_congruenceSubgroup_eq_map_conj_of_mk_eq
    (h : NarrowClassGroup.mk I = NarrowClassGroup.mk J) :
    ∃ δ ∈ totallyPositiveUnits.comap GeneralLinearGroup.det, s.congruenceSubgroup J.val 𝔑 =
      (s.congruenceSubgroup I.val 𝔑).map (MulAut.conj δ).toMonoidHom :=
  exists_eq_map_conj_of_mk_eq (s.congruenceSubgroup · 𝔑)
    (s.congruenceSubgroup_spanSingleton_mul · 𝔑 ·) h

end SurfaceType

end HilbertModularGroup
