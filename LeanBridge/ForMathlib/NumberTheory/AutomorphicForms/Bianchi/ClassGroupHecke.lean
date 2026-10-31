import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.NewformOfWeight
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Hilbert.HeckeIdeal

/-!
# Bianchi modular forms over fields of any class number and their Hecke operators

Let `K` be an imaginary quadratic field, of any class number, embedded in `ℂ` by `σ`, `𝔑` a nonzero
ideal of `𝒪_K`, and `(𝔟_c)` representatives of the ideal classes of `K` (the narrow class group of a
totally complex field is its class group). Adelically, a Bianchi modular form of weight `k` and
level `𝔑` is a function on `GL₂(K) \ GL₂(𝔸_K) / K₀(𝔑)`, whose `h` components are the functions
`F_c : ℋ₃ → ℂ^{k+1}` invariant under the groups `Γ₀(𝔑)_{𝔟_c}` of the matrices of `GL₂(K)`
stabilising the lattices `𝒪_K ⊕ 𝔟_c` and `𝒪_K ⊕ 𝔑𝔟_c` (`HilbertModularGroup.gammaZero`), the
component of the trivial class with `𝔟 = 𝒪_K` being the level `Γ₀(𝔑)` of LMFDB `mf.bianchi.level`.
A tuple `(F_c)` of Bianchi modular forms (real analytic, invariant, harmonic, of polynomial growth
at the cusps) is the analogue for any class number of the space `M_k(Γ₀(𝔑))` of the LMFDB, which
only considers fields of class number `1`.

For every nonzero ideal `𝔞` of `𝒪_K`, the **Hecke operator** `T_𝔞` (LMFDB `mf.bianchi.hecke_algebra`
for class number `1`) is `(T_𝔞 F)_c = ∑_α F_{c'} ∣_k α`, `c' = c [𝔞]⁻¹`, where `α` runs over the
finitely many right cosets `Γ₀(𝔑)_{𝔟_{c'}} α` of the matrices `α ∈ GL₂(K)` mapping `𝒪_K ⊕ 𝔟_c` into
`𝒪_K ⊕ 𝔟_{c'}` and `𝒪_K ⊕ 𝔑𝔟_c` into `𝒪_K ⊕ 𝔑𝔟_{c'}`, with `(det α) 𝔟_c = 𝔞 𝔟_{c'}`
(`HilbertModularGroup.heckeSet`, Shimura's `T(𝔞)`; for a prime `𝔭 ∤ 𝔑` this is `T_𝔭`), acting
through `PSL(2, ℂ)`. It permutes the components, and is defined at every prime, principal or not.
As in `bianchiHeckeTPrimeArith`, the arithmetic normalisation, in which the eigenvalues `a_𝔭` of
the LMFDB are algebraic integers, is `N(𝔞)^{(k - 2) / 4} T_𝔞`.

A **Hecke eigenform** is a nonzero form which is an eigenvector of every `T_𝔭`, `𝔭 ∤ 𝔑` prime, with
eigenvalues `a_𝔭`; its **Hecke field** is the field they generate, and its **dimension** the degree
of the Hecke field (LMFDB `mf.bianchi.newform` for class number `1`). It is **normalised** if the
component of the trivial class, with `𝔟 = 𝒪_K`, has the Fourier–Bessel coefficient `c(1) = 1`.
That the operators preserve cusp forms, commute, and that the eigenvalues `a_𝔭` are the Fourier
coefficients of a normalised eigenform are theorems, not proved here; newforms, which need the
oldforms of every component, are only formalised for class number `1`
(`BianchiNewformOfWeight`).

## Main definitions

* `HyperbolicThreeSpace.IsBianchiModularFormGL`: Bianchi modular forms for a subgroup of `GL₂(K)`.
* `HyperbolicThreeSpace.bianchiClassGroupForms`: the space of tuples of Bianchi modular forms of
  weight `k` and level `𝔑` on the components.
* `HyperbolicThreeSpace.bianchiHeckeIdealOperator`: `T_𝔞` from one component to another.
* `HyperbolicThreeSpace.bianchiHeckeIdeal` (LMFDB `mf.bianchi.hecke_algebra`): the Hecke operator
  `T_𝔞` on the space of tuples.
* `HyperbolicThreeSpace.bianchiHeckeIdealArith` (LMFDB `mf.bianchi.newform`): its arithmetic
  normalisation `N(𝔞)^{(k - 2) / 4} T_𝔞`.
* `HyperbolicThreeSpace.IsBianchiHeckeEigenform`: Hecke eigenforms.
* `HyperbolicThreeSpace.IsBianchiHeckeEigenform.eigenvalue` (LMFDB `mf.bianchi.newform`): the
  eigenvalue `a_𝔭` at a prime `𝔭 ∤ 𝔑`.
* `HyperbolicThreeSpace.IsBianchiHeckeEigenform.heckeField`,
  `HyperbolicThreeSpace.IsBianchiHeckeEigenform.dimension` (LMFDB `mf.bianchi.newform`): the Hecke
  field and the dimension.
* `HyperbolicThreeSpace.IsNormalisedBianchiForm`: normalisation by the Fourier–Bessel coefficient
  `c(1) = 1` of the component of the trivial class.

## Main results

* `HyperbolicThreeSpace.isBianchiModularFormGL_iff`: for the level `Γ₀(𝔑)` of `GL₂(𝒪_K)`, these are
  the Bianchi modular forms `IsBianchiModularForm` of LMFDB `mf.bianchi`.
* `HyperbolicThreeSpace.IsBianchiModularFormGL.heckeIdeal`: the Hecke operators map Bianchi modular
  forms on one component to Bianchi modular forms on another.
* `HyperbolicThreeSpace.IsBianchiHeckeEigenform.eigenvalue_spec`: `T_𝔭 F = a_𝔭 F`.
* `HyperbolicThreeSpace.IsBianchiHeckeEigenform.eq_eigenvalue`: the eigenvalue is unique.
-/

open Matrix NumberField HilbertModularGroup

open scoped MatrixGroups nonZeroDivisors

namespace HyperbolicThreeSpace

variable {K : Type*} [Field K] (σ : K →+* ℂ) (k : ℕ) (Γ : Subgroup (GL (Fin 2) K))
  {F G : HyperbolicThreeSpace → Fin (k + 1) → ℂ}

/-- `F : ℋ₃ → ℂ^{k+1}` is a **Bianchi modular form** of weight `k` for a subgroup `Γ` of `GL₂(K)`,
`K` being embedded in `ℂ` by `σ`: it is real analytic, invariant under every `SL(2, ℂ)`
representative of every element of `Γ` (`bianchiSlashInvariants`), harmonic and of polynomial
growth at the cusps, as in LMFDB `mf.bianchi` (`IsBianchiModularForm`, for subgroups of `GL₂(𝒪_K)`;
`isBianchiModularFormGL_iff`). The groups `Γ₀(𝔑)_𝔟` of the components of Bianchi modular forms
over fields of class number `> 1` are not contained in `GL₂(𝒪_K)`. -/
structure IsBianchiModularFormGL (F : HyperbolicThreeSpace → Fin (k + 1) → ℂ) : Prop where
  /-- `F` is real analytic. -/
  analyticAt (z : HyperbolicThreeSpace) : AnalyticAt ℝ (extend F) z.coords
  /-- `F ∣_k g = F` for the representatives `g` of the elements of `Γ`. -/
  mem_bianchiSlashInvariants : F ∈ bianchiSlashInvariants σ k Γ
  /-- `F` is harmonic. -/
  harmonic : IsBianchiHarmonic k F
  /-- `F` has at worst polynomial growth at the cusps. -/
  growth : HasPolynomialGrowthAtCusps σ k F

variable {σ k Γ}

lemma HasPolynomialGrowthAtCusps.const_smul (c : ℂ) (hF : HasPolynomialGrowthAtCusps σ k F) :
    HasPolynomialGrowthAtCusps σ k (c • F) := by
  intro g
  rcases hF g with ⟨C, m, h⟩
  refine ⟨‖c‖ * C, m, fun z hz ↦ ?_⟩
  rw [bianchiSlash_smul, Pi.smul_apply, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h z hz) (norm_nonneg c)

lemma IsBianchiModularFormGL.add (hF : IsBianchiModularFormGL σ k Γ F)
    (hG : IsBianchiModularFormGL σ k Γ G) : IsBianchiModularFormGL σ k Γ (F + G) where
  analyticAt z := by
    rw [extend_add]
    exact (hF.analyticAt z).add (hG.analyticAt z)
  mem_bianchiSlashInvariants := add_mem hF.mem_bianchiSlashInvariants hG.mem_bianchiSlashInvariants
  harmonic := hF.harmonic.add hF.analyticAt hG.analyticAt hG.harmonic
  growth := hF.growth.add hG.growth

lemma IsBianchiModularFormGL.const_smul (c : ℂ) (hF : IsBianchiModularFormGL σ k Γ F) :
    IsBianchiModularFormGL σ k Γ (c • F) where
  analyticAt z := by
    rw [extend_smul]
    exact (hF.analyticAt z).const_smul
  mem_bianchiSlashInvariants := Submodule.smul_mem _ c hF.mem_bianchiSlashInvariants
  harmonic := hF.harmonic.const_smul c hF.analyticAt
  growth := hF.growth.const_smul c

variable (σ k Γ) in
lemma isBianchiModularFormGL_zero : IsBianchiModularFormGL σ k Γ 0 where
  analyticAt z := by
    rw [extend_zero]
    exact analyticAt_const
  mem_bianchiSlashInvariants := zero_mem _
  harmonic := isBianchiHarmonic_zero k
  growth _ := ⟨0, 0, fun _ _ ↦ by simp [bianchiSlash_zero]⟩

/-- **For the level `Γ₀(𝔑)`, these are the Bianchi modular forms of LMFDB `mf.bianchi`**: for a
totally complex `K`, `F` is a Bianchi modular form for the image `bianchiGammaZero 𝔑` of
`Γ₀(𝔑) ≤ GL₂(𝒪_K)` in `GL₂(K)` exactly when it is one for `Γ₀(𝔑)` in the sense of
`IsBianchiModularForm`. -/
lemma isBianchiModularFormGL_iff [IsTotallyComplex K] (𝔑 : Ideal (𝓞 K)) :
    IsBianchiModularFormGL σ k (bianchiGammaZero 𝔑) F ↔ IsBianchiModularForm σ 𝔑.gamma0GL k F :=
  ⟨fun hF ↦ ⟨hF.analyticAt, (isBianchiSlashInvariant_iff_mem 𝔑).mpr hF.mem_bianchiSlashInvariants,
    hF.harmonic, hF.growth⟩, fun hF ↦ ⟨hF.analyticAt, hF.mem_bianchiSlashInvariants, hF.harmonic,
      hF.growth⟩⟩

variable (σ k) (𝔑 : Ideal (𝓞 K)) {𝔫 : Ideal (𝓞 K)} {𝔡 𝔠 : FractionalIdeal (𝓞 K)⁰ K}

variable {σ k 𝔑} in
lemma bianchiSlash_slRepresentative_out_mk
    (hF : F ∈ bianchiSlashInvariants σ k (gammaZero 𝔠 (glPlus 𝔠) 𝔑)) (x : GL (Fin 2) K)
    {g : SL(2, ℂ)} (hg : IsSLRepresentative σ x g) :
    bianchiSlash k (slRepresentative σ (⟦x⟧ : gammaZeroRightCosets 𝔑 𝔠).out) F =
      bianchiSlash k g F :=
  bianchiSlash_eq_of_mul_inv_mem hF (out_mul_inv_mem x) hg (isSLRepresentative_slRepresentative _)

variable [NumberField K] (𝔟 : NarrowClassGroup K → (FractionalIdeal (𝓞 K)⁰ K)ˣ)

/-- The space of **Bianchi modular forms** of weight `k` and level `𝔑` over a number field `K` of
any class number (LMFDB `mf.bianchi` for class number `1`), embedded in `ℂ` by `σ`: the tuples
`(F_c)`, indexed by the narrow class group of `K` (its class group for `K` totally complex), of
Bianchi modular forms `F_c : ℋ₃ → ℂ^{k+1}` for the groups `Γ₀(𝔑)_{𝔟_c}` of the matrices of
`GL₂(K)` stabilising `𝒪_K ⊕ 𝔟_c` and `𝒪_K ⊕ 𝔑𝔟_c`, for representatives `𝔟_c` of the classes. For
class number `1` and `𝔟 = 𝒪_K` it is `M_k(Γ₀(𝔑))` (`isBianchiModularFormGL_iff`). -/
def bianchiClassGroupForms :
    Submodule ℂ (NarrowClassGroup K → HyperbolicThreeSpace → Fin (k + 1) → ℂ) where
  carrier := {F | ∀ c, IsBianchiModularFormGL σ k
    (gammaZero (𝔟 c : FractionalIdeal (𝓞 K)⁰ K) (glPlus (𝔟 c : FractionalIdeal (𝓞 K)⁰ K)) 𝔑) (F c)}
  add_mem' hF hG c := (hF c).add (hG c)
  zero_mem' _ := isBianchiModularFormGL_zero σ k _
  smul_mem' a _ hF c := (hF c).const_smul a

variable (𝔫 𝔡 𝔠) [NeZero 𝔑] [NeZero 𝔫] [NeZero 𝔡]

/-- The **Hecke operator `T_𝔫`** (LMFDB `mf.bianchi.hecke_algebra`) from the component of `𝔠` to the
component of `𝔡`, on the functions invariant under `Γ₀(𝔑)_𝔠` in weight `k`: `φ ↦ ∑_α φ ∣_k g_α`,
where `α` runs over representatives of the finitely many right cosets `Γ₀(𝔑)_𝔠 α` of the matrices
of `HilbertModularGroup.heckeSet 𝔑 𝔫 𝔡 𝔠` (`HilbertModularGroup.finite_heckeCosets`) and `g_α` is
the chosen `SL(2, ℂ)`-representative of `α`. The sum does not depend on the representatives, as
`φ` is invariant, and is invariant under `Γ₀(𝔑)_𝔡`, which permutes the cosets. -/
noncomputable def bianchiHeckeIdealOperator :
    bianchiSlashInvariants σ k (gammaZero 𝔠 (glPlus 𝔠) 𝔑) →ₗ[ℂ]
      bianchiSlashInvariants σ k (gammaZero 𝔡 (glPlus 𝔡) 𝔑) where
  toFun φ := ⟨∑ q ∈ (finite_heckeCosets (𝔠 := 𝔠) (NeZero.ne 𝔡) (NeZero.ne 𝔑)
      (NeZero.ne 𝔫)).toFinset, bianchiSlash k (slRepresentative σ q.out) φ, fun γ hγ g hg ↦ by
    rw [bianchiSlash_sum]
    have hfin : (heckeCosets 𝔑 𝔫 𝔡 𝔠).Finite :=
      finite_heckeCosets (NeZero.ne 𝔡) (NeZero.ne 𝔑) (NeZero.ne 𝔫)
    refine Finset.sum_nbij' (fun q ↦ ⟦q.out * γ⟧) (fun q ↦ ⟦q.out * γ⁻¹⟧) ?_ ?_
      (fun q _ ↦ mk_out_mul_mul_inv q γ) (fun q _ ↦ by simpa using mk_out_mul_mul_inv q γ⁻¹)
      fun q _ ↦ ?_
    · rintro q hq
      rcases hfin.mem_toFinset.mp hq with ⟨α, hα, rfl⟩
      refine hfin.mem_toFinset.mpr ?_
      rw [mk_out_mul]
      exact ⟨_, mul_mem_heckeSet (NeZero.ne 𝔡) hα hγ, rfl⟩
    · rintro q hq
      rcases hfin.mem_toFinset.mp hq with ⟨α, hα, rfl⟩
      refine hfin.mem_toFinset.mpr ?_
      rw [mk_out_mul]
      exact ⟨_, mul_mem_heckeSet (NeZero.ne 𝔡) hα (inv_mem hγ), rfl⟩
    · rw [← bianchiSlash_mul, bianchiSlash_slRepresentative_out_mk φ.2 _
        ((isSLRepresentative_slRepresentative _).mul hg)]⟩
  map_add' φ ψ := Subtype.ext <| by
    simp [bianchiSlash_add, Finset.sum_add_distrib]
  map_smul' c φ := Subtype.ext <| by
    simp [bianchiSlash_smul, Finset.smul_sum]

lemma coe_bianchiHeckeIdealOperator (φ : bianchiSlashInvariants σ k (gammaZero 𝔠 (glPlus 𝔠) 𝔑)) :
    (bianchiHeckeIdealOperator σ k 𝔑 𝔫 𝔡 𝔠 φ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) =
      ∑ q ∈ (finite_heckeCosets (𝔠 := 𝔠) (NeZero.ne 𝔡) (NeZero.ne 𝔑) (NeZero.ne 𝔫)).toFinset,
        bianchiSlash k (slRepresentative σ q.out) φ :=
  rfl

variable {σ k 𝔑 𝔫 𝔡 𝔠}

/-- **The Hecke operators preserve Bianchi modular forms**: `T_𝔫` maps a Bianchi modular form for
`Γ₀(𝔑)_𝔠` to a Bianchi modular form for `Γ₀(𝔑)_𝔡`, as every slash operator preserves real
analyticity, harmonicity and polynomial growth at the cusps. -/
lemma IsBianchiModularFormGL.heckeIdeal
    (hF : IsBianchiModularFormGL σ k (gammaZero 𝔠 (glPlus 𝔠) 𝔑) F) :
    IsBianchiModularFormGL σ k (gammaZero 𝔡 (glPlus 𝔡) 𝔑)
      (bianchiHeckeIdealOperator σ k 𝔑 𝔫 𝔡 𝔠 ⟨F, hF.mem_bianchiSlashInvariants⟩ :
        HyperbolicThreeSpace → Fin (k + 1) → ℂ) := by
  have h : (∀ z : HyperbolicThreeSpace, AnalyticAt ℝ (extend (bianchiHeckeIdealOperator σ k 𝔑 𝔫 𝔡
      𝔠 ⟨F, hF.mem_bianchiSlashInvariants⟩ : HyperbolicThreeSpace → Fin (k + 1) → ℂ)) z.coords) ∧
      IsBianchiHarmonic k (bianchiHeckeIdealOperator σ k 𝔑 𝔫 𝔡 𝔠
        ⟨F, hF.mem_bianchiSlashInvariants⟩ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) ∧
      HasPolynomialGrowthAtCusps σ k (bianchiHeckeIdealOperator σ k 𝔑 𝔫 𝔡 𝔠
        ⟨F, hF.mem_bianchiSlashInvariants⟩ : HyperbolicThreeSpace → Fin (k + 1) → ℂ) := by
    rw [coe_bianchiHeckeIdealOperator]
    refine Finset.sum_induction _ (fun G : HyperbolicThreeSpace → Fin (k + 1) → ℂ ↦
      (∀ z : HyperbolicThreeSpace, AnalyticAt ℝ (extend G) z.coords) ∧ IsBianchiHarmonic k G ∧
        HasPolynomialGrowthAtCusps σ k G) (fun G H hG hH ↦ ⟨fun z ↦ ?_,
          hG.2.1.add hG.1 hH.1 hH.2.1, hG.2.2.add hH.2.2⟩)
      ⟨(isBianchiModularFormGL_zero σ k ⊥).analyticAt, isBianchiHarmonic_zero k,
        (isBianchiModularFormGL_zero σ k ⊥).growth⟩
      fun q _ ↦ ⟨analyticAt_extend_bianchiSlash _ hF.analyticAt, hF.harmonic.bianchiSlash _,
        hF.growth.bianchiSlash (isSLRepresentative_slRepresentative _)⟩
    rw [extend_add]
    exact (hG.1 z).add (hH.1 z)
  exact ⟨h.1, Subtype.prop _, h.2.1, h.2.2⟩

variable (σ k 𝔑) (𝔞 : (Ideal (𝓞 K))⁰)

/-- The component `Φ_c` of a Bianchi modular form `Φ = (Φ_c)` over a field of any class number, as
a function invariant under `Γ₀(𝔑)_{𝔟_c}`. -/
noncomputable def bianchiClassGroupFormsComponent (c : NarrowClassGroup K) :
    bianchiClassGroupForms σ k 𝔑 𝔟 →ₗ[ℂ] bianchiSlashInvariants σ k
      (gammaZero (𝔟 c : FractionalIdeal (𝓞 K)⁰ K) (glPlus (𝔟 c : FractionalIdeal (𝓞 K)⁰ K)) 𝔑) :=
  LinearMap.codRestrict _ ((LinearMap.proj c).comp (bianchiClassGroupForms σ k 𝔑 𝔟).subtype)
    fun Φ ↦ (Φ.2 c).mem_bianchiSlashInvariants

/-- The **Hecke operator `T_𝔞`** (LMFDB `mf.bianchi.hecke_algebra`) of a nonzero ideal `𝔞` of `𝒪_K`
on the space of Bianchi modular forms of weight `k` and level `𝔑` over `K` of any class number:
`(T_𝔞 F)_c = ∑_α F_{c'} ∣_k α`, where `c' = c [𝔞]⁻¹` and `α` runs over representatives of the right
cosets `Γ₀(𝔑)_{𝔟_{c'}} α ⊆ heckeSet 𝔑 𝔞 𝔟_c 𝔟_{c'}` (`bianchiHeckeIdealOperator`), acting through
`PSL(2, ℂ)`. For a prime `𝔭 ∤ 𝔑`, principal or not, it is the Hecke operator `T_𝔭`; its arithmetic
normalisation is `bianchiHeckeIdealArith`. -/
noncomputable def bianchiHeckeIdeal : Module.End ℂ (bianchiClassGroupForms σ k 𝔑 𝔟) :=
  LinearMap.codRestrict _ (LinearMap.pi fun c ↦ (bianchiSlashInvariants σ k _).subtype ∘ₗ
    bianchiHeckeIdealOperator σ k 𝔑 𝔞 (𝔟 c) (𝔟 (c * (NarrowClassGroup.mk0 𝔞)⁻¹)) ∘ₗ
      bianchiClassGroupFormsComponent σ k 𝔑 𝔟 (c * (NarrowClassGroup.mk0 𝔞)⁻¹))
    fun Φ _ ↦ (Φ.2 _).heckeIdeal

/-- The **arithmetic Hecke operator** `N(𝔞)^{(k - 2) / 4} T_𝔞` (LMFDB `mf.bianchi.newform`) on the
space of Bianchi modular forms of weight `k` and level `𝔑` over `K` of any class number, as in
`bianchiHeckeTPrimeArith`: its eigenvalues `a_𝔭` on newforms are the LMFDB's, algebraic integers
equal to the Fourier–Bessel coefficients (theorems, not proved here). In weight `2` it is `T_𝔞`. -/
noncomputable def bianchiHeckeIdealArith : Module.End ℂ (bianchiClassGroupForms σ k 𝔑 𝔟) :=
  (((Ideal.absNorm (𝔞 : Ideal (𝓞 K)) : ℝ) ^ (((k : ℝ) - 2) / 4) : ℝ) : ℂ) •
    bianchiHeckeIdeal σ k 𝔑 𝔟 𝔞

variable {σ k 𝔑 𝔟} (Φ : bianchiClassGroupForms σ k 𝔑 𝔟)

/-- `Φ` is a **Hecke eigenform**: `Φ ≠ 0` is an eigenvector of the arithmetic Hecke operator `T_𝔭`
(`bianchiHeckeIdealArith`) of every prime `𝔭 ∤ 𝔑` of `𝒪_K`, principal or not. -/
def IsBianchiHeckeEigenform : Prop :=
  Φ ≠ 0 ∧ ∀ 𝔭 : (Ideal (𝓞 K))⁰, (𝔭 : Ideal (𝓞 K)).IsPrime → ¬𝔑 ≤ 𝔭 →
    ∃ a : ℂ, bianchiHeckeIdealArith σ k 𝔑 𝔟 𝔭 Φ = a • Φ

/-- `Φ` is **normalised**: for the representative `𝔟₁ = 𝒪_K` of the trivial class, whose component
is a Bianchi modular form for the level `Γ₀(𝔑)` of `GL₂(𝒪_K)`, the component `Φ₁` has a
Fourier–Bessel expansion of weight `k` (`HasBianchiWhittakerExpansion`, with the principal square
root of the discriminant) whose coefficient of `(1)` is `1`, as the LMFDB normalises its newforms
(LMFDB `mf.bianchi.spaces`). -/
def IsNormalisedBianchiForm : Prop :=
  (𝔟 1 : FractionalIdeal (𝓞 K)⁰ K) = 1 ∧ ∃ c : 𝓞 K → ℂ,
    HasBianchiWhittakerExpansion σ ((discr K : ℂ) ^ (2⁻¹ : ℂ)) k (extend (Φ.1 1)) c ∧ c 1 = 1

namespace IsBianchiHeckeEigenform

variable {Φ} (hΦ : IsBianchiHeckeEigenform Φ)
  (𝔭 : {𝔭 : (Ideal (𝓞 K))⁰ // (𝔭 : Ideal (𝓞 K)).IsPrime ∧ ¬𝔑 ≤ 𝔭})

/-- The **Hecke eigenvalue** `a_𝔭` (LMFDB `mf.bianchi.newform`) of a Hecke eigenform `Φ` at a prime
`𝔭 ∤ 𝔑`, principal or not: the unique `a_𝔭 ∈ ℂ` with `T_𝔭 Φ = a_𝔭 Φ` for the arithmetic Hecke
operator (`eigenvalue_spec`, `eq_eigenvalue`). -/
noncomputable def eigenvalue : ℂ :=
  (hΦ.2 𝔭.1 𝔭.2.1 𝔭.2.2).choose

/-- **`Φ` is an eigenform of `T_𝔭` with eigenvalue `a_𝔭`.** -/
lemma eigenvalue_spec : bianchiHeckeIdealArith σ k 𝔑 𝔟 𝔭.1 Φ = hΦ.eigenvalue 𝔭 • Φ :=
  (hΦ.2 𝔭.1 𝔭.2.1 𝔭.2.2).choose_spec

/-- **The Hecke eigenvalue is unique**, as `Φ ≠ 0`. -/
lemma eq_eigenvalue {a : ℂ} (h : bianchiHeckeIdealArith σ k 𝔑 𝔟 𝔭.1 Φ = a • Φ) :
    a = hΦ.eigenvalue 𝔭 :=
  smul_left_injective ℂ hΦ.1 <| h.symm.trans (hΦ.eigenvalue_spec 𝔭)

/-- The **Hecke field** (LMFDB `mf.bianchi.newform` for class number `1`) of a Hecke eigenform: the
subfield of `ℂ` generated by its eigenvalues `a_𝔭` at the primes `𝔭 ∤ 𝔑`, principal or not. That
it is a totally real number field for a newform is a theorem, not proved here. -/
noncomputable def heckeField : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (Set.range hΦ.eigenvalue)

/-- The **dimension** (LMFDB `mf.bianchi.newform` for class number `1`) of a Hecke eigenform: the
degree of its Hecke field over `ℚ`. -/
noncomputable def dimension : ℕ :=
  Module.finrank ℚ hΦ.heckeField

end IsBianchiHeckeEigenform

end HyperbolicThreeSpace
