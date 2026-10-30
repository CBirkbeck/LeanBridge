import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.ModularForm
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.SlashAction
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Hilbert.HeckeRing
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex

/-!
# Hecke operators on Bianchi modular forms

Let `K` be a number field embedded in `ℂ` by `σ`, imaginary quadratic for the LMFDB. A matrix
`α ∈ GL₂(K)` acts on `ℋ₃` through the image of `σ(α)` in `PGL₂(ℂ) ≅ PSL₂(ℂ)`: its
**`SL(2, ℂ)`-representatives** are the matrices `g = s⁻¹ σ(α)` with `s² = det σ(α)`, and a function
`F : ℋ₃ → ℂ^{k+1}` is invariant under a subgroup `Γ` of `GL₂(K)` if `F ∣_k g = F` for every
representative `g` of every `γ ∈ Γ`, both signs included, as for Bianchi modular forms (LMFDB
`mf.bianchi`). Since `F ∣_k gh = (F ∣_k g) ∣_k h`, the value `F ∣_k g` of an invariant `F` only
depends on the right coset `Γα` of the matrix `α` that `g` represents.

For a Hecke pair `(Γ, Δ)`, a double coset `ΓαΓ = ⊔ᵢ Γαᵢ`, `α ∈ Δ`, acts on the invariant functions
by `F ↦ ∑ᵢ F ∣_k gᵢ`, `gᵢ` representing `αᵢ`, which does not depend on the choices and is again
invariant; linearly, the Hecke ring acts. For the level `Γ₀(𝔑)` (`Ideal.gamma0GL`, LMFDB
`mf.bianchi.level`) of an imaginary quadratic field, the Hecke pair is `(Γ₀(𝔑), GL₂(K))`: viewed in
`GL₂(K)`, `Γ₀(𝔑)` is the group `HilbertModularGroup.gammaZero 1 (glPlus 1) 𝔑` of the matrices
stabilising the lattices `𝒪_K ⊕ 𝒪_K` and `𝒪_K ⊕ 𝔑` (`mem_bianchiGammaZero_iff`), every
element of `GL₂(K)` commensurates it (`HilbertModularGroup.mem_commensurator_gammaZero`), and the
total positivity of `HilbertModularGroup.glTotallyPositive` is vacuous for a totally complex `K`.
For `π ∈ Kˣ`, the double coset `Γ₀(𝔑) diag(1, π) Γ₀(𝔑)` (`HilbertModularGroup.heckeT`) gives the
Hecke operator `T_𝔭` of the prime `𝔭 = (π)`; it is `U_𝔭` when `𝔭 ∣ 𝔑`.

The matrices act through `PSL(2, ℂ)`, without a determinant factor. In weight `2`, the weight of
the LMFDB's Bianchi newforms, this is the usual normalisation, in which `T_𝔭` acts on harmonic
`1`-forms as on the cohomology of `Γ₀(𝔑)` and has algebraic integer eigenvalues. In the knowl's
weight `k > 2` (values in `ℂ^{k+1}`), the arithmetic normalisation, with algebraic integer
eigenvalues, differs from this one by a power of `N𝔭`; the algebra the operators generate is the
same.

## Main definitions

* `HyperbolicThreeSpace.IsSLRepresentative`: `g ∈ SL(2, ℂ)` represents `α ∈ GL₂(K)`.
* `HyperbolicThreeSpace.slRepresentative`: a chosen representative.
* `HyperbolicThreeSpace.bianchiSlashInvariants`: the functions invariant under `Γ ≤ GL₂(K)`.
* `HyperbolicThreeSpace.bianchiHeckeOperator` (LMFDB `mf.bianchi.hecke_algebra`): the Hecke
  operator `F ↦ ∑ᵢ F ∣_k gᵢ` of a double coset.
* `HyperbolicThreeSpace.bianchiHeckeRingAction` (LMFDB `mf.bianchi.hecke_algebra`): the linear
  extension of the Hecke operators to the Hecke ring.
* `HyperbolicThreeSpace.bianchiGammaZero`: the level `Γ₀(𝔑)` as a subgroup of `GL₂(K)`.
* `HyperbolicThreeSpace.bianchiHeckeT` (LMFDB `mf.bianchi.hecke_algebra`): the Hecke operator of
  `Γ₀(𝔑) diag(1, π) Γ₀(𝔑)`.

## Main results

* `HyperbolicThreeSpace.bianchiSlash_eq_of_mul_inv_mem`: for an invariant `F`, `F ∣_k g` only
  depends on the right coset of the matrix that `g` represents.
* `HyperbolicThreeSpace.bianchiHeckeOperator_eq_sum`: the Hecke operator is the sum over any
  family of representatives of the right cosets.
* `HyperbolicThreeSpace.mem_bianchiGammaZero_iff`: for totally complex `K`, the group
  `bianchiGammaZero 𝔑` is the image of the level `Γ₀(𝔑)` of `GL₂(𝒪_K)`.
* `HyperbolicThreeSpace.isBianchiSlashInvariant_iff_mem`: invariance under the level `Γ₀(𝔑)` in
  the sense of LMFDB `mf.bianchi` is invariance under `bianchiGammaZero 𝔑`.
* `HyperbolicThreeSpace.bianchiHeckeT_mul_unit`: `T_π` only depends on the ideal `(π)`.
-/

open Matrix hiding mul_inv_rev

open Complex MulAction NumberField DoubleCoset HilbertModularGroup

open scoped MatrixGroups Pointwise nonZeroDivisors

namespace HyperbolicThreeSpace

variable {K : Type*} [Field K] (σ : K →+* ℂ) (k : ℕ) {α β : GL (Fin 2) K} {g h : SL(2, ℂ)}
  (F : HyperbolicThreeSpace → Fin (k + 1) → ℂ)

variable (α g) in
/-- `g ∈ SL(2, ℂ)` **represents** `α ∈ GL₂(K)`, for `K` embedded in `ℂ` by `σ`: `g = s⁻¹ σ(α)` for
some `s ∈ ℂ`, necessarily a square root of `det σ(α)`. The two representatives `±g` are the lifts
to `SL(2, ℂ)` of the image of `σ(α)` in `PGL₂(ℂ) ≅ PSL₂(ℂ)`, through which `α` acts on `ℋ₃`. -/
def IsSLRepresentative : Prop :=
  ∃ s : ℂ, (g : Matrix (Fin 2) (Fin 2) ℂ) = s⁻¹ • (α : Matrix (Fin 2) (Fin 2) K).map σ

variable {σ}

lemma IsSLRepresentative.mul (hg : IsSLRepresentative σ α g) (hh : IsSLRepresentative σ β h) :
    IsSLRepresentative σ (α * β) (g * h) := by
  rcases hg with ⟨s, hs⟩
  rcases hh with ⟨t, ht⟩
  refine ⟨s * t, ?_⟩
  rw [SpecialLinearGroup.coe_mul, hs, ht, Units.val_mul, Matrix.map_mul, smul_mul_smul_comm,
    mul_inv]

lemma ne_zero_of_coe_eq_inv_smul {s : ℂ}
    (hs : (g : Matrix (Fin 2) (Fin 2) ℂ) = s⁻¹ • (α : Matrix (Fin 2) (Fin 2) K).map σ) : s ≠ 0 := by
  rintro rfl
  have h₁ : (g : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := g.det_coe
  simp [hs] at h₁

lemma IsSLRepresentative.inv (hg : IsSLRepresentative σ α g) : IsSLRepresentative σ α⁻¹ g⁻¹ := by
  rcases hg with ⟨s, hs⟩
  refine ⟨s⁻¹, ?_⟩
  have h₁ : (g : Matrix (Fin 2) (Fin 2) ℂ) *
      (s⁻¹⁻¹ • ((α⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map σ) = 1 := by
    rw [hs, smul_mul_smul_comm, ← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      inv_inv, inv_mul_cancel₀ (ne_zero_of_coe_eq_inv_smul hs), one_smul,
      Matrix.map_one _ σ.map_zero σ.map_one]
  rw [SpecialLinearGroup.coe_inv, ← inv_eq_right_inv h₁, Matrix.inv_def, g.det_coe,
    Ring.inverse_one, one_smul]

variable (α) in
lemma det_map_ne_zero : ((α : Matrix (Fin 2) (Fin 2) K).map σ).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero σ).mpr (by simpa using α.det.ne_zero)

variable (σ α) in
/-- The chosen representative `s⁻¹ σ(α) ∈ SL(2, ℂ)` of `α ∈ GL₂(K)`, with `s` the principal square
root of `det σ(α)`. -/
noncomputable def slRepresentative : SL(2, ℂ) :=
  ⟨(((α : Matrix (Fin 2) (Fin 2) K).map σ).det ^ (2⁻¹ : ℂ))⁻¹ •
    (α : Matrix (Fin 2) (Fin 2) K).map σ, by
    have hs : (((α : Matrix (Fin 2) (Fin 2) K).map σ).det ^ (2⁻¹ : ℂ)) ^ 2 =
        ((α : Matrix (Fin 2) (Fin 2) K).map σ).det := by
      simp
    rw [det_smul, Fintype.card_fin, inv_pow, hs, inv_mul_cancel₀ (det_map_ne_zero α)]⟩

variable (α) in
lemma isSLRepresentative_slRepresentative : IsSLRepresentative σ α (slRepresentative σ α) :=
  ⟨_, rfl⟩

variable (g) in
lemma bianchiSlash_sum {ι : Type*} (s : Finset ι) (G : ι → HyperbolicThreeSpace → Fin (k + 1) → ℂ) :
    bianchiSlash k g (∑ i ∈ s, G i) = ∑ i ∈ s, bianchiSlash k g (G i) := by
  ext z : 1
  simp [bianchiSlash, mulVec_sum]

variable (σ) (Γ : Subgroup (GL (Fin 2) K))

/-- The space of functions `F : ℋ₃ → ℂ^{k+1}` **invariant** under a subgroup `Γ` of `GL₂(K)` in
weight `k`, for `K` embedded in `ℂ` by `σ`: `F ∣_k g = F` for every `SL(2, ℂ)`-representative `g`
of every `γ ∈ Γ`, both signs included, as in LMFDB `mf.bianchi`. -/
def bianchiSlashInvariants : Submodule ℂ (HyperbolicThreeSpace → Fin (k + 1) → ℂ) where
  carrier := {F | ∀ γ ∈ Γ, ∀ g, IsSLRepresentative σ γ g → bianchiSlash k g F = F}
  add_mem' hF hG γ hγ g hg := by
    rw [bianchiSlash_add, hF γ hγ g hg, hG γ hγ g hg]
  zero_mem' _ _ g _ := bianchiSlash_zero g
  smul_mem' c _ hF γ hγ g hg := by
    rw [bianchiSlash_smul, hF γ hγ g hg]

variable {σ k Γ F}

/-- **For an invariant function, `F ∣_k g` only depends on the right coset**: if `g` represents
`x ∈ GL₂(K)`, `h` represents `y` and `Γx = Γy`, then `F ∣_k h = F ∣_k g`, as `hg⁻¹` represents
`yx⁻¹ ∈ Γ`. -/
lemma bianchiSlash_eq_of_mul_inv_mem (hF : F ∈ bianchiSlashInvariants σ k Γ) {x y : GL (Fin 2) K}
    (hxy : y * x⁻¹ ∈ Γ) (hg : IsSLRepresentative σ x g) (hh : IsSLRepresentative σ y h) :
    bianchiSlash k h F = bianchiSlash k g F := by
  rw [← inv_mul_cancel_right h g, bianchiSlash_mul, hF _ hxy _ (hh.mul hg.inv)]

variable (σ k Γ) (Δ : Submonoid (GL (Fin 2) K)) [IsHeckeTriple Δ Γ Γ] (D : HeckeCoset Δ Γ Γ)
  (Φ : bianchiSlashInvariants σ k Γ)

attribute [local instance] Fintype.ofFinite

/-- The **Hecke operator** (LMFDB `mf.bianchi.hecke_algebra`) of a double coset
`D = ΓαΓ = ⊔ᵢ Γαᵢ`, `α ∈ Δ`, of a Hecke pair `(Γ, Δ)` in `GL₂(K)`, such as
`(Γ₀(𝔑), GL₂(K))`, on the functions invariant under `Γ` in weight `k`: `F ↦ ∑ᵢ F ∣_k gᵢ`, with
`gᵢ ∈ SL(2, ℂ)` representing `αᵢ`. It is defined with chosen representatives but does not depend on
them (`bianchiHeckeOperator_eq_sum`), and its value is again invariant, since right
multiplication by `γ ∈ Γ` permutes the right cosets `Γαᵢ`.

The matrices act through `PSL(2, ℂ)`, without a determinant factor: this is the normalisation of
LMFDB `mf.bianchi.weight2` in weight `2`, the weight of the LMFDB's Bianchi newforms, in which
`T_𝔭` acts on the harmonic `1`-forms, as on the cohomology of `Γ₀(𝔑)`. In the knowl's weight
`k > 2`, the arithmetic normalisation of a double coset `ΓαΓ` differs from this one by a power of
`|N(det α)|`. -/
noncomputable def bianchiHeckeOperator : Module.End ℂ (bianchiSlashInvariants σ k Γ) where
  toFun F := ⟨∑ v, bianchiSlash k (slRepresentative σ (rightCosetRep D v)) F, fun γ hγ g hg ↦ by
    rw [bianchiSlash_sum]
    refine Fintype.sum_equiv (toPerm (⟨γ, hγ⟩ : Γ)⁻¹) _ _ fun v ↦ ?_
    rcases exists_mem_out_mul_inv_eq_mul_rightCosetRep D (mul_mem (inv_mem hγ) v.out.2) with
      ⟨γ₁, hγ₁, hsplit⟩
    have hmk : (QuotientGroup.mk ⟨γ⁻¹ * (v.out : GL (Fin 2) K), mul_mem (inv_mem hγ) v.out.2⟩ :
        DecompQuotient Γ Γ (D.out : GL (Fin 2) K)⁻¹) = (⟨γ, hγ⟩ : Γ)⁻¹ • v :=
      Quotient.mk_smul_out _ (⟨γ, hγ⟩ : Γ)⁻¹ v
    have hprod : rightCosetRep D v * γ = γ₁ * rightCosetRep D ((⟨γ, hγ⟩ : Γ)⁻¹ • v) := by
      simpa only [hmk, mul_inv_rev, inv_inv, ← mul_assoc, rightCosetRep_def] using hsplit
    rw [← bianchiSlash_mul]
    refine bianchiSlash_eq_of_mul_inv_mem F.2 ?_ (isSLRepresentative_slRepresentative _)
      ((isSLRepresentative_slRepresentative _).mul hg)
    rwa [hprod, toPerm_apply, mul_inv_cancel_right]⟩
  map_add' F G := Subtype.ext <| by
    simp [bianchiSlash_add, Finset.sum_add_distrib]
  map_smul' c F := Subtype.ext <| by
    simp [bianchiSlash_smul, Finset.smul_sum]

lemma coe_bianchiHeckeOperator :
    (bianchiHeckeOperator σ k Γ Δ D Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) =
      ∑ v, bianchiSlash k (slRepresentative σ (rightCosetRep D v)) Φ :=
  rfl

/-- **The Hecke operator does not depend on the representatives**: for any family `(aᵢ)` in
`GL₂(K)` whose right cosets `Γaᵢ` are pairwise distinct and cover `D = ΓαΓ`, and any
representatives `gᵢ ∈ SL(2, ℂ)` of the `aᵢ`, `F ∣_k D = ∑ᵢ F ∣_k gᵢ`. -/
lemma bianchiHeckeOperator_eq_sum {ι : Type*} [Fintype ι] (a : ι → GL (Fin 2) K)
    (hcover : doubleCoset (D.out : GL (Fin 2) K) (Γ : Set (GL (Fin 2) K)) Γ =
      ⋃ i, MulOpposite.op (a i) • (Γ : Set (GL (Fin 2) K)))
    (hinj : Function.Injective fun i ↦ MulOpposite.op (a i) • (Γ : Set (GL (Fin 2) K)))
    (r : ι → SL(2, ℂ)) (hr : ∀ i, IsSLRepresentative σ (a i) (r i)) :
    (bianchiHeckeOperator σ k Γ Δ D Φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) =
      ∑ i, bianchiSlash k (r i) Φ := by
  rcases exists_bijective_rightCosetRep_smul_eq D a hcover hinj with ⟨e, he, h⟩
  exact (Fintype.sum_bijective e he _ _ fun i ↦ (bianchiSlash_eq_of_mul_inv_mem Φ.2
    ((rightCoset_eq_iff _).mp (h i)) (hr i) (isSLRepresentative_slRepresentative _)).symm).symm

/-- The action of the **Hecke ring** (LMFDB `mf.bianchi.hecke_algebra`) of a Hecke pair `(Γ, Δ)`
in `GL₂(K)`, such as `(Γ₀(𝔑), GL₂(K))`, on the functions invariant under `Γ` in weight `k`: the
linear extension of the Hecke operators of the double cosets. That it is compatible with the
product of the Hecke ring is not proved here. -/
noncomputable def bianchiHeckeRingAction :
    (HeckeCoset Δ Γ Γ →₀ ℂ) →ₗ[ℂ] Module.End ℂ (bianchiSlashInvariants σ k Γ) :=
  Finsupp.linearCombination ℂ (bianchiHeckeOperator σ k Γ Δ)

variable (𝔑 : Ideal (𝓞 K))

/-- The level `Γ₀(𝔑)` (LMFDB `mf.bianchi.level`) as a subgroup of `GL₂(K)`: the matrices with
totally positive determinant stabilising the lattices `𝒪_K ⊕ 𝒪_K` and `𝒪_K ⊕ 𝔑` of `K²`, that is
`HilbertModularGroup.gammaZero 1 (glPlus 1) 𝔑`. For a totally complex `K`, such as an imaginary
quadratic field, total positivity is vacuous and this is the image in `GL₂(K)` of the level
`Γ₀(𝔑) = Ideal.gamma0GL 𝔑` of `GL₂(𝒪_K)` (`mem_bianchiGammaZero_iff`). -/
noncomputable abbrev bianchiGammaZero : Subgroup (GL (Fin 2) K) :=
  gammaZero 1 (glPlus 1) 𝔑

variable {𝔑} {v : Fin 2 → K} {γ : GL (Fin 2) (𝓞 K)}

lemma mem_lattice_one_iff : v ∈ lattice (1 : FractionalIdeal (𝓞 K)⁰ K) ↔
    ∃ w : Fin 2 → 𝓞 K, algebraMap (𝓞 K) K ∘ w = v := by
  rw [mem_lattice, FractionalIdeal.mem_one_iff, Submodule.mem_one]
  refine ⟨fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ↦ ⟨![a, b], funext fun i ↦ ?_⟩, fun ⟨w, hw⟩ ↦
    ⟨⟨w 0, congrFun hw 0⟩, ⟨w 1, congrFun hw 1⟩⟩⟩
  fin_cases i
  exacts [ha, hb]

lemma mem_ideal_smul_one_iff {x : K} :
    x ∈ 𝔑 • (1 : Submodule (𝓞 K) K) ↔ ∃ n ∈ 𝔑, algebraMap (𝓞 K) K n = x := by
  rw [Submodule.one_eq_range, LinearMap.range_eq_map, ← Submodule.map_smul'', smul_eq_mul,
    Ideal.mul_top, Submodule.mem_map]
  rfl

lemma mem_gammaZeroLattice_one_iff : v ∈ gammaZeroLattice (1 : FractionalIdeal (𝓞 K)⁰ K) 𝔑 ↔
    ∃ w : Fin 2 → 𝓞 K, w 1 ∈ 𝔑 ∧ algebraMap (𝓞 K) K ∘ w = v := by
  rw [mem_gammaZeroLattice, FractionalIdeal.coe_one, Submodule.mem_one, mem_ideal_smul_one_iff]
  refine ⟨fun ⟨⟨a, ha⟩, ⟨b, hb, hb'⟩⟩ ↦ ⟨![a, b], hb, funext fun i ↦ ?_⟩, fun ⟨w, hw, hw'⟩ ↦
    ⟨⟨w 0, congrFun hw' 0⟩, ⟨w 1, hw, congrFun hw' 1⟩⟩⟩
  fin_cases i
  exacts [ha, hb']

variable (γ) in
lemma map_mulVec_mem_lattice_one (hv : v ∈ lattice (1 : FractionalIdeal (𝓞 K)⁰ K)) :
    (GeneralLinearGroup.map (algebraMap (𝓞 K) K) γ).val *ᵥ v ∈
      lattice (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  rcases mem_lattice_one_iff.mp hv with ⟨w, rfl⟩
  exact mem_lattice_one_iff.mpr ⟨γ.val *ᵥ w, funext fun i ↦ RingHom.map_mulVec _ _ _ i⟩

lemma map_mulVec_mem_gammaZeroLattice_one (hγ : γ ∈ 𝔑.gamma0GL)
    (hv : v ∈ gammaZeroLattice (1 : FractionalIdeal (𝓞 K)⁰ K) 𝔑) :
    (GeneralLinearGroup.map (algebraMap (𝓞 K) K) γ).val *ᵥ v ∈
      gammaZeroLattice (1 : FractionalIdeal (𝓞 K)⁰ K) 𝔑 := by
  rcases mem_gammaZeroLattice_one_iff.mp hv with ⟨w, hw, rfl⟩
  refine mem_gammaZeroLattice_one_iff.mpr ⟨γ.val *ᵥ w, ?_, funext fun i ↦
    RingHom.map_mulVec _ _ _ i⟩
  simp only [mulVec, dotProduct, Fin.sum_univ_two]
  exact 𝔑.add_mem (𝔑.mul_mem_right _ hγ) (𝔑.mul_mem_left _ hw)

lemma map_inv_mulVec_map_mulVec : (GeneralLinearGroup.map (algebraMap (𝓞 K) K) γ⁻¹).val *ᵥ
    ((GeneralLinearGroup.map (algebraMap (𝓞 K) K) γ).val *ᵥ v) = v := by
  rw [mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
    one_mulVec]

variable [IsTotallyComplex K]

lemma isTotallyPositive_of_isTotallyComplex (x : K) : IsTotallyPositive x :=
  fun _ hw ↦ absurd hw (by simp)

/-- **`bianchiGammaZero 𝔑` is the level `Γ₀(𝔑)` of `GL₂(𝒪_K)`**: for a totally complex number
field `K`, the elements of `GL₂(K)` stabilising `𝒪_K ⊕ 𝒪_K` and `𝒪_K ⊕ 𝔑` are the images of the
matrices `(a, b; c, d) ∈ GL₂(𝒪_K)` with `c ∈ 𝔑`. -/
lemma mem_bianchiGammaZero_iff (x : GL (Fin 2) K) : x ∈ bianchiGammaZero 𝔑 ↔
    ∃ γ ∈ 𝔑.gamma0GL, GeneralLinearGroup.map (algebraMap (𝓞 K) K) γ = x := by
  refine ⟨fun hx ↦ ?_, ?_⟩
  · rcases hx with ⟨⟨hgl, -⟩, hL⟩
    have hsingle (j : Fin 2) : algebraMap (𝓞 K) K ∘ Pi.single j 1 = Pi.single j 1 := by
      ext i
      by_cases hij : i = j <;> simp [hij]
    have hcol (y : GL (Fin 2) K) (hy : y ∈ gl (1 : FractionalIdeal (𝓞 K)⁰ K)) (j : Fin 2) :
        ∃ w : Fin 2 → 𝓞 K, algebraMap (𝓞 K) K ∘ w = fun i ↦ y.val i j := by
      refine mem_lattice_one_iff.mp ?_
      have h₁ : Pi.single j 1 ∈ lattice (1 : FractionalIdeal (𝓞 K)⁰ K) :=
        mem_lattice_one_iff.mpr ⟨Pi.single j 1, hsingle j⟩
      have h₂ : y.val *ᵥ Pi.single j 1 = fun i ↦ y.val i j := mulVec_single_one _ _
      exact h₂ ▸ (hy _).mp h₁
    choose wA hwA using hcol x hgl
    choose wB hwB using hcol x⁻¹ (inv_mem hgl)
    have hA : (of fun i j ↦ wA j i).map (algebraMap (𝓞 K) K) = x.val := by
      ext i j
      exact congrFun (hwA j) i
    have hB : (of fun i j ↦ wB j i).map (algebraMap (𝓞 K) K) = (x⁻¹).val := by
      ext i j
      exact congrFun (hwB j) i
    have hinj :
        Function.Injective fun M : Matrix (Fin 2) (Fin 2) (𝓞 K) ↦ M.map (algebraMap (𝓞 K) K) :=
      map_injective RingOfIntegers.coe_injective
    let γ : GL (Fin 2) (𝓞 K) := ⟨of fun i j ↦ wA j i, of fun i j ↦ wB j i,
      hinj <| by simp only [Matrix.map_mul, hA, hB, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)],
      hinj <| by simp only [Matrix.map_mul, hA, hB, ← Units.val_mul, inv_mul_cancel,
        Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]⟩
    have h₀ : Pi.single 0 1 ∈ gammaZeroLattice (1 : FractionalIdeal (𝓞 K)⁰ K) 𝔑 :=
      mem_gammaZeroLattice_one_iff.mpr ⟨Pi.single 0 1, by simp, hsingle 0⟩
    rcases mem_gammaZeroLattice_one_iff.mp ((hL _).mp h₀) with ⟨w, hw, hw'⟩
    have h₁₀ : algebraMap (𝓞 K) K (w 1) = x.val 1 0 := by
      simpa using congrFun hw' 1
    have hc : wA 0 1 ∈ 𝔑 := RingOfIntegers.coe_injective (h₁₀.trans (congrFun (hwA 0) 1).symm) ▸ hw
    exact ⟨γ, hc, Units.ext hA⟩
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨⟨fun v ↦ ⟨map_mulVec_mem_lattice_one γ, fun h ↦ ?_⟩, Subgroup.mem_comap.mpr <|
      mem_totallyPositiveUnits.mpr <| isTotallyPositive_of_isTotallyComplex _⟩,
      fun v ↦ ⟨map_mulVec_mem_gammaZeroLattice_one hγ, fun h ↦ ?_⟩⟩
    · simpa only [map_inv_mulVec_map_mulVec] using map_mulVec_mem_lattice_one γ⁻¹ h
    · simpa only [map_inv_mulVec_map_mulVec] using
        map_mulVec_mem_gammaZeroLattice_one (inv_mem hγ) h

variable {σ k} (𝔑) (π : Kˣ) (u : (𝓞 K)ˣ)

/-- **Invariance under the level `Γ₀(𝔑)` of LMFDB `mf.bianchi` is invariance under
`bianchiGammaZero 𝔑`**: for a totally complex `K`, `F ∣_k g = F` for the representatives `g` of the
elements of `Γ₀(𝔑) ≤ GL₂(𝒪_K)` exactly when `F` lies in
`bianchiSlashInvariants σ k (bianchiGammaZero 𝔑)`. -/
lemma isBianchiSlashInvariant_iff_mem : IsBianchiSlashInvariant σ 𝔑.gamma0GL k F ↔
    F ∈ bianchiSlashInvariants σ k (bianchiGammaZero 𝔑) := by
  refine ⟨fun hF γ hγ g ⟨s, hs⟩ ↦ ?_, fun hF γ hγ g s hs ↦ ?_⟩
  · rcases (mem_bianchiGammaZero_iff γ).mp hγ with ⟨γ₀, hγ₀, rfl⟩
    exact hF γ₀ hγ₀ g s hs
  · exact hF _ ((mem_bianchiGammaZero_iff _).mpr ⟨γ, hγ, rfl⟩) g ⟨s, hs⟩

lemma heckeT_mul_unit : heckeT 1 𝔑 (π * Units.map (algebraMap (𝓞 K) K).toMonoidHom u)
    (isTotallyPositive_of_isTotallyComplex _) =
    heckeT 1 𝔑 π (isTotallyPositive_of_isTotallyComplex _) := by
  have hu : GeneralLinearGroup.map (algebraMap (𝓞 K) K) (GeneralLinearGroup.rowScale 1 u) ∈
      bianchiGammaZero 𝔑 :=
    (mem_bianchiGammaZero_iff _).mpr ⟨GeneralLinearGroup.rowScale 1 u,
      by simp [Ideal.gamma0GL], rfl⟩
  refine HeckeCoset.mk_eq_mk_of_mem (DoubleCoset.mem_doubleCoset.mpr
    ⟨1, one_mem _, _, hu, Units.ext ?_⟩)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heckeDiagonal]

variable (σ k) [NumberField K] [NeZero 𝔑]

/-- The **Hecke operator `T_π`** (LMFDB `mf.bianchi.hecke_algebra`) of `π ∈ Kˣ` on the functions
invariant under the level `Γ₀(𝔑)` in weight `k`, for a totally complex `K` embedded in `ℂ` by `σ`:
the operator of the double coset `Γ₀(𝔑) diag(1, π) Γ₀(𝔑)` (`HilbertModularGroup.heckeT`), whose
total positivity condition is vacuous here. For `π` a generator of a prime `𝔭` of `𝒪_K`, it is the
Hecke operator `T_𝔭` of the LMFDB, `U_𝔭` when `𝔭 ∣ 𝔑`; it only depends on `𝔭`
(`bianchiHeckeT_mul_unit`). -/
noncomputable def bianchiHeckeT : Module.End ℂ (bianchiSlashInvariants σ k (bianchiGammaZero 𝔑)) :=
  bianchiHeckeOperator σ k (bianchiGammaZero 𝔑) (glTotallyPositive K)
    (heckeT 1 𝔑 π (isTotallyPositive_of_isTotallyComplex _))

/-- **`T_π` only depends on the ideal `(π)`**: multiplying `π` by a unit of `𝒪_K` does not change
the double coset `Γ₀(𝔑) diag(1, π) Γ₀(𝔑)`, as `diag(1, u) ∈ Γ₀(𝔑)`. -/
lemma bianchiHeckeT_mul_unit : bianchiHeckeT σ k 𝔑
    (π * Units.map (algebraMap (𝓞 K) K).toMonoidHom u) = bianchiHeckeT σ k 𝔑 π := by
  rw [bianchiHeckeT, heckeT_mul_unit, bianchiHeckeT]

end HyperbolicThreeSpace
