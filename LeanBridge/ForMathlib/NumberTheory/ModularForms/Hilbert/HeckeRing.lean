import LeanBridge.ForMathlib.NumberTheory.ModularForms.Hilbert.Basic
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import TauCeti.NumberTheory.HeckeRing.Associativity

/-!
# The Hecke ring of `Γ₀(𝔑)_𝔟`

Let `F` be a number field with ring of integers `𝒪_F`, let `𝔟` be a nonzero fractional ideal and
`𝔑` a nonzero ideal of `𝒪_F`. The group `Γ₀(𝔑)_𝔟 = HilbertModularGroup.gammaZero 𝔟 (glPlus 𝔟) 𝔑`
of the Hilbert modular forms of level `𝔑` is the group of matrices of `GL₂(F)` with totally positive
determinant stabilising the lattices `𝒪_F ⊕ 𝔟` and `𝒪_F ⊕ 𝔑𝔟` of `F²`. Every `g ∈ GL₂(F)`
commensurates it: the lattices `L` and `gL'` (`L, L'` among these two) are commensurable, so the
orbit of `gL'` under `Γ₀(𝔑)_𝔟` lies in the finite set of lattices `N` with `c L ⊆ N` and
`c N ⊆ L` for a fixed nonzero `c ∈ 𝒪_F` (finite since `𝒪_F / c𝒪_F` is), and the stabiliser of
`gL'` has finite index; the intersection of these stabilisers lies in `gΓ₀(𝔑)_𝔟g⁻¹`. Hence
`(Γ₀(𝔑)_𝔟, GL₂⁺(F))` is a Hecke pair, `GL₂⁺(F)` being the matrices with totally positive
determinant, and it has a Hecke ring. For a totally positive `π ∈ Fˣ`, the double coset
`Γ₀(𝔑)_𝔟 diag(1, π) Γ₀(𝔑)_𝔟` is the Hecke operator `T_𝔭` of the prime `𝔭 = (π)` when `π` is
integral, `𝔭` is prime and `𝔭 ∤ 𝔑`: these are the primes trivial in the narrow class group, for
which `T_𝔭` maps each component of a Hilbert modular form to itself.

## Main definitions

* `HilbertModularGroup.mulVecDistribMulAction`: the action of `GL₂(F)` on `F²`, a local instance.
* `HilbertModularGroup.IsCommensurableLattice`: commensurable `𝒪_F`-lattices.
* `HilbertModularGroup.integralLattice`: the lattice `𝒪_F²`.
* `HilbertModularGroup.glTotallyPositive`: the monoid `GL₂⁺(F)`.
* `HilbertModularGroup.hilbertHeckeRing`: the Hecke ring of `Γ₀(𝔑)_𝔟`.
* `HilbertModularGroup.heckeDiagonal`: the matrix `diag(1, π)`.
* `HilbertModularGroup.heckeT`: the double coset `T_𝔭 = Γ₀(𝔑)_𝔟 diag(1, π) Γ₀(𝔑)_𝔟`.

## Main results

* `HilbertModularGroup.mem_commensurator_gammaZero`: every element of `GL₂(F)` commensurates
  `Γ₀(𝔑)_𝔟`, so that `(Γ₀(𝔑)_𝔟, GL₂⁺(F))` is a Hecke pair (an instance of `IsHeckeTriple`).
-/

open Matrix NumberField Subgroup Commensurable

open scoped nonZeroDivisors Pointwise

namespace HilbertModularGroup

variable {F : Type*} [Field F]

/-- The action of `GL₂(F)` on the column vectors of `F²` by matrix multiplication, a local instance
of this file. -/
@[instance_reducible]
def mulVecDistribMulAction : DistribMulAction (GL (Fin 2) F) (Fin 2 → F) where
  smul g v := g.val *ᵥ v
  one_smul := one_mulVec
  mul_smul g h v := (mulVec_mulVec v g.val h.val).symm
  smul_zero _ := mulVec_zero _
  smul_add _ := mulVec_add _

attribute [local instance] mulVecDistribMulAction

lemma smul_def (g : GL (Fin 2) F) (v : Fin 2 → F) : g • v = g.val *ᵥ v :=
  rfl

local instance : SMulCommClass (GL (Fin 2) F) (𝓞 F) (Fin 2 → F) where
  smul_comm g r v := smul_comm g.val r v

lemma smul_comm_submodule (c : 𝓞 F) (g : GL (Fin 2) F) (N : Submodule (𝓞 F) (Fin 2 → F)) :
    c • g • N = g • c • N := by
  ext v
  simp only [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨-, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨c • b, ⟨b, hb, rfl⟩, smul_comm g c b⟩
  · rintro ⟨-, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨g • b, ⟨b, hb, rfl⟩, smul_comm c g b⟩

variable {M : Type*} [AddCommGroup M] [Module (𝓞 F) M] {A B C : Submodule (𝓞 F) M}

/-- Two `𝒪_F`-submodules `A` and `B` of a module are **commensurable lattices** if `c A ⊆ B` and
`c B ⊆ A` for some nonzero `c ∈ 𝒪_F`. -/
def IsCommensurableLattice (A B : Submodule (𝓞 F) M) : Prop :=
  ∃ c : 𝓞 F, c ≠ 0 ∧ c • A ≤ B ∧ c • B ≤ A

lemma IsCommensurableLattice.symm (h : IsCommensurableLattice A B) :
    IsCommensurableLattice B A := by
  rcases h with ⟨c, hc, h₁, h₂⟩
  exact ⟨c, hc, h₂, h₁⟩

lemma IsCommensurableLattice.of_smul_le {c d : 𝓞 F} (hc : c ≠ 0) (hd : d ≠ 0) (h₁ : c • A ≤ B)
    (h₂ : d • B ≤ A) : IsCommensurableLattice A B := by
  refine ⟨c * d, mul_ne_zero hc hd, ?_, ?_⟩
  · rw [mul_comm, mul_smul]
    exact (smul_le_smul_left d h₁).trans (Submodule.smul_le_self_of_tower d B)
  · rw [mul_smul]
    exact (smul_le_smul_left c h₂).trans (Submodule.smul_le_self_of_tower c A)

lemma IsCommensurableLattice.trans (h₁ : IsCommensurableLattice A B)
    (h₂ : IsCommensurableLattice B C) : IsCommensurableLattice A C := by
  rcases h₁ with ⟨c, hc, h₁, h₁'⟩
  rcases h₂ with ⟨d, hd, h₂, h₂'⟩
  refine IsCommensurableLattice.of_smul_le (mul_ne_zero hd hc) (mul_ne_zero hc hd) ?_ ?_
  · rw [mul_smul]
    exact (smul_le_smul_left d h₁).trans h₂
  · rw [mul_smul]
    exact (smul_le_smul_left c h₂').trans h₁'

lemma IsCommensurableLattice.smul_gl {A B : Submodule (𝓞 F) (Fin 2 → F)}
    (h : IsCommensurableLattice A B) (g : GL (Fin 2) F) :
    IsCommensurableLattice (g • A) (g • B) := by
  rcases h with ⟨c, hc, h₁, h₂⟩
  refine ⟨c, hc, ?_, ?_⟩
  · rw [smul_comm_submodule]
    exact Submodule.map_mono h₁
  · rw [smul_comm_submodule]
    exact Submodule.map_mono h₂

lemma isCommensurableLattice_refl (A : Submodule (𝓞 F) M) : IsCommensurableLattice A A :=
  ⟨1, one_ne_zero, by rw [one_smul], by rw [one_smul]⟩

lemma smul_le_of_dvd {c d : 𝓞 F} (hcd : c ∣ d) (h : c • A ≤ B) : d • A ≤ B := by
  rcases hcd with ⟨e, rfl⟩
  rw [mul_comm, mul_smul]
  exact (smul_le_smul_left e h).trans (Submodule.smul_le_self_of_tower e B)

lemma isCommensurableLattice_ideal_smul {𝔑 : Ideal (𝓞 F)} (h𝔑 : 𝔑 ≠ ⊥)
    (h : IsCommensurableLattice A B) : IsCommensurableLattice (𝔑 • A) B := by
  rcases h with ⟨c, hc, h₁, h₂⟩
  rcases Submodule.exists_mem_ne_zero_of_ne_bot h𝔑 with ⟨n, hn, hn0⟩
  refine IsCommensurableLattice.of_smul_le hc (mul_ne_zero hn0 hc)
    ((smul_le_smul_left c Submodule.smul_le_right).trans h₁) ?_
  rw [mul_smul]
  refine (smul_le_smul_left n h₂).trans fun v hv ↦ ?_
  rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hv with ⟨a, ha, rfl⟩
  exact Submodule.smul_mem_smul hn ha

lemma isCommensurableLattice_pi {ι : Type*} [Fintype ι] {Q Q' : ι → Submodule (𝓞 F) F}
    (h : ∀ i, IsCommensurableLattice (Q i) (Q' i)) :
    IsCommensurableLattice (Submodule.pi Set.univ Q) (Submodule.pi Set.univ Q') := by
  choose c hc h₁ h₂ using h
  refine ⟨∏ i, c i, Finset.prod_ne_zero_iff.mpr fun i _ ↦ hc i, ?_, ?_⟩
  · rintro - ⟨w, hw, rfl⟩ i -
    exact smul_le_of_dvd (Finset.dvd_prod_of_mem c (Finset.mem_univ i)) (h₁ i)
      (Submodule.smul_mem_pointwise_smul _ _ _ (hw i (Set.mem_univ i)))
  · rintro - ⟨w, hw, rfl⟩ i -
    exact smul_le_of_dvd (Finset.dvd_prod_of_mem c (Finset.mem_univ i)) (h₂ i)
      (Submodule.smul_mem_pointwise_smul _ _ _ (hw i (Set.mem_univ i)))

lemma mem_stabilizer_iff {g : GL (Fin 2) F} {N : Submodule (𝓞 F) (Fin 2 → F)} :
    g ∈ MulAction.stabilizer (GL (Fin 2) F) N ↔ ∀ v, v ∈ N ↔ g.val *ᵥ v ∈ N := by
  rw [MulAction.mem_stabilizer_iff]
  refine ⟨fun h v ↦ ⟨fun hv ↦ h ▸ Submodule.smul_mem_pointwise_smul v g N hv, fun hv ↦ ?_⟩,
    fun h ↦ le_antisymm ?_ fun v hv ↦ ?_⟩
  · rw [← smul_def, ← h] at hv
    rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hv with ⟨w, hw, hwv⟩
    rwa [← smul_left_cancel g hwv]
  · rintro - ⟨w, hw, rfl⟩
    exact (h w).mp hw
  · refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨g⁻¹ • v, (h _).mpr ?_, smul_inv_smul g v⟩
    rwa [← smul_def, smul_inv_smul]

lemma gl_eq_stabilizer (𝔟 : FractionalIdeal (𝓞 F)⁰ F) :
    gl 𝔟 = MulAction.stabilizer (GL (Fin 2) F) (lattice 𝔟) :=
  Subgroup.ext fun _ ↦ mem_stabilizer_iff.symm

variable (F) in
/-- The lattice `𝒪_F²` of `F²`. -/
noncomputable def integralLattice : Submodule (𝓞 F) (Fin 2 → F) :=
  Submodule.pi Set.univ fun _ ↦ 1

lemma smul_mulVec_mem_integralLattice {A : Matrix (Fin 2) (Fin 2) F} {d : 𝓞 F}
    (hA : ∀ i j, d • A i j ∈ (⊥ : Subalgebra (𝓞 F) F)) {v : Fin 2 → F}
    (hv : v ∈ integralLattice F) : d • (A *ᵥ v) ∈ integralLattice F := by
  rw [integralLattice, Submodule.mem_pi] at hv ⊢
  rintro i -
  have hv' (j : Fin 2) : v j ∈ (⊥ : Subalgebra (𝓞 F) F) := by
    rw [← Subalgebra.mem_toSubmodule, Algebra.toSubmodule_bot]
    exact hv j (Set.mem_univ j)
  rw [← Algebra.toSubmodule_bot, Subalgebra.mem_toSubmodule, Pi.smul_apply, mulVec, dotProduct,
    Finset.smul_sum]
  exact Subalgebra.sum_mem _ fun j _ ↦ by
    rw [← smul_mul_assoc]
    exact mul_mem (hA i j) (hv' j)

lemma integralLattice_le_range :
    integralLattice F ≤ LinearMap.range ((Algebra.linearMap (𝓞 F) F).compLeft (Fin 2)) := by
  intro v hv
  rw [integralLattice, Submodule.mem_pi] at hv
  choose r hr using fun i ↦ Submodule.mem_one.mp (hv i (Set.mem_univ i))
  exact ⟨r, funext hr⟩

variable {𝔟 : FractionalIdeal (𝓞 F)⁰ F} {𝔑 : Ideal (𝓞 F)}

lemma gammaZero_eq : gammaZero 𝔟 (glPlus 𝔟) 𝔑 = glPlus 𝔟 ⊓
    MulAction.stabilizer (GL (Fin 2) F) (gammaZeroLattice 𝔟 𝔑) :=
  Subgroup.ext fun _ ↦ and_congr_right fun _ ↦ mem_stabilizer_iff.symm

variable (F) in
/-- The monoid `GL₂⁺(F)` of the matrices of `GL₂(F)` with totally positive determinant, which act on
`ℍⁿ` through the real places of `F`. -/
noncomputable def glTotallyPositive : Submonoid (GL (Fin 2) F) :=
  (totallyPositiveUnits.comap GeneralLinearGroup.det).toSubmonoid

lemma gammaZero_le_glTotallyPositive :
    (gammaZero 𝔟 (glPlus 𝔟) 𝔑).toSubmonoid ≤ glTotallyPositive F :=
  fun _ hx ↦ hx.1.2

lemma isTotallyPositive_det_of_mem_gammaZero {γ : GL (Fin 2) F}
    (hγ : γ ∈ gammaZero 𝔟 (glPlus 𝔟) 𝔑) : IsTotallyPositive γ.det.val :=
  mem_totallyPositiveUnits.mp hγ.1.2

/-- The matrix `diag(1, π)` of `GL₂⁺(F)`, for a totally positive `π ∈ Fˣ`. -/
noncomputable def heckeDiagonal (π : Fˣ) (hπ : IsTotallyPositive (π : F)) :
    glTotallyPositive F where
  val := ⟨diagonal ![1, (π : F)], diagonal ![1, (π⁻¹ : Fˣ)], by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp, by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp⟩
  property := by
    refine Subgroup.mem_comap.mpr (mem_totallyPositiveUnits.mpr ?_)
    simpa using hπ

variable [NumberField F]

lemma isCommensurableLattice_fractionalIdeal (h𝔟 : 𝔟 ≠ 0) :
    IsCommensurableLattice (𝔟 : Submodule (𝓞 F) F) 1 := by
  rcases 𝔟.isFractional with ⟨a, ha, hint⟩
  rcases FractionalIdeal.exists_ne_zero_mem_isInteger h𝔟 with ⟨x, hx, hxb⟩
  refine IsCommensurableLattice.of_smul_le (nonZeroDivisors.ne_zero ha) hx ?_ ?_
  · rintro - ⟨b, hb, rfl⟩
    rcases hint b hb with ⟨y, hy⟩
    exact Submodule.mem_one.mpr ⟨y, hy⟩
  · rintro - ⟨b, hb, rfl⟩
    rcases Submodule.mem_one.mp hb with ⟨y, rfl⟩
    rw [DistribSMul.toLinearMap_apply, Algebra.smul_def, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ y hxb

lemma isCommensurableLattice_gl_smul (g : GL (Fin 2) F) :
    IsCommensurableLattice (g • integralLattice F) (integralLattice F) := by
  rcases IsLocalization.exist_integer_multiples (𝓞 F)⁰ Finset.univ
    (Sum.elim (fun p : Fin 2 × Fin 2 ↦ g.val p.1 p.2) fun p : Fin 2 × Fin 2 ↦
      (g⁻¹).val p.1 p.2) with ⟨⟨d, hd⟩, hint⟩
  have h₁ (i j : Fin 2) : d • g.val i j ∈ (⊥ : Subalgebra (𝓞 F) F) :=
    Algebra.mem_bot.mpr (hint (.inl (i, j)) (Finset.mem_univ _))
  have h₂ (i j : Fin 2) : d • (g⁻¹).val i j ∈ (⊥ : Subalgebra (𝓞 F) F) :=
    Algebra.mem_bot.mpr (hint (.inr (i, j)) (Finset.mem_univ _))
  refine ⟨d, nonZeroDivisors.ne_zero hd, ?_, fun v hv ↦ ?_⟩
  · rintro - ⟨-, ⟨w, hw, rfl⟩, rfl⟩
    exact smul_mulVec_mem_integralLattice h₁ hw
  · rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hv with ⟨w, hw, rfl⟩
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
      ⟨d • ((g⁻¹).val *ᵥ w), smul_mulVec_mem_integralLattice h₂ hw, ?_⟩
    rw [← smul_def g⁻¹, smul_comm g d, smul_inv_smul]

lemma finite_setOf_le_integralLattice {d : 𝓞 F} (hd : d ≠ 0) :
    {M | d • integralLattice F ≤ M ∧ M ≤ integralLattice F}.Finite := by
  let ι : (Fin 2 → 𝓞 F) →ₗ[𝓞 F] Fin 2 → F := (Algebra.linearMap (𝓞 F) F).compLeft (Fin 2)
  let P : Submodule (𝓞 F) (Fin 2 → 𝓞 F) := Submodule.pi Set.univ fun _ ↦ Ideal.span {d}
  have : Finite (𝓞 F ⧸ Ideal.span {d}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by rwa [Ne, Ideal.span_singleton_eq_bot])
  have : Finite ((Fin 2 → 𝓞 F) ⧸ P) :=
    Finite.of_equiv _ (Submodule.quotientPi _).toEquiv.symm
  have : Finite (Submodule (𝓞 F) ((Fin 2 → 𝓞 F) ⧸ P)) :=
    Finite.of_injective _ SetLike.coe_injective
  have hφ {M : Submodule (𝓞 F) (Fin 2 → F)}
      (hM : d • integralLattice F ≤ M ∧ M ≤ integralLattice F) :
      (((M.comap ι).map P.mkQ).comap P.mkQ).map ι = M := by
    have hP : P ≤ M.comap ι := fun x hx ↦ by
      choose a ha using fun i ↦ Ideal.mem_span_singleton'.mp (hx i (Set.mem_univ i))
      have hx' : ι x = d • ι a := funext fun i ↦ by
        simp [ι, ← ha i, Algebra.smul_def, mul_comm]
      rw [Submodule.mem_comap, hx']
      exact hM.1 <| Submodule.smul_mem_pointwise_smul _ _ _ fun i _ ↦
        Submodule.mem_one.mpr ⟨a i, rfl⟩
    rw [Submodule.comap_map_mkQ, sup_eq_right.mpr hP, Submodule.map_comap_eq,
      inf_eq_right.mpr (hM.2.trans integralLattice_le_range)]
  refine Set.Finite.of_finite_image (f := fun M ↦ (M.comap ι).map P.mkQ) (Set.toFinite _)
    fun M₁ hM₁ M₂ hM₂ h ↦ ?_
  rw [← hφ hM₁, ← hφ hM₂]
  exact congrArg (fun N : Submodule (𝓞 F) ((Fin 2 → 𝓞 F) ⧸ P) ↦ (N.comap P.mkQ).map ι) h

lemma finite_setOf_isBand {L : Submodule (𝓞 F) (Fin 2 → F)}
    (hL : IsCommensurableLattice L (integralLattice F)) {c : 𝓞 F} (hc : c ≠ 0) :
    {N | c • L ≤ N ∧ c • N ≤ L}.Finite := by
  rcases hL with ⟨e, he, h₁, h₂⟩
  have hf : c * e ≠ 0 :=
    mul_ne_zero hc he
  have h₃ {N : Submodule (𝓞 F) (Fin 2 → F)} (hN : c • L ≤ N) : (c * e) • integralLattice F ≤ N := by
    rw [mul_smul]
    exact (smul_le_smul_left c h₂).trans hN
  refine Set.Finite.of_finite_image (f := fun N ↦ (c * e) • N)
    ((finite_setOf_le_integralLattice (mul_ne_zero hf hf)).subset ?_)
    fun N₁ _ N₂ _ h ↦ Submodule.map_injective_of_injective (smul_right_injective _ hf) h
  rintro - ⟨N, hN, rfl⟩
  beta_reduce
  refine ⟨?_, ?_⟩
  · rw [mul_smul]
    exact smul_le_smul_left _ (h₃ hN.1)
  · rw [mul_comm, mul_smul]
    exact (smul_le_smul_left e hN.2).trans h₁

lemma isFiniteRelIndex_stabilizer {Γ : Subgroup (GL (Fin 2) F)}
    {L N : Submodule (𝓞 F) (Fin 2 → F)} (hΓ : Γ ≤ MulAction.stabilizer (GL (Fin 2) F) L)
    (hL : IsCommensurableLattice L (integralLattice F)) (hN : IsCommensurableLattice N L) :
    (MulAction.stabilizer (GL (Fin 2) F) N).IsFiniteRelIndex Γ := by
  rcases hN with ⟨c, hc, h₁, h₂⟩
  rw [isFiniteRelIndex_iff_relIndex_ne_zero, relIndex, MulAction.stabilizer_subgroupOf,
    MulAction.index_stabilizer]
  refine ((Set.ncard_pos ?_).mpr ⟨N, MulAction.mem_orbit_self N⟩).ne'
  refine (finite_setOf_isBand hL hc).subset ?_
  rintro - ⟨γ, rfl⟩
  have hγ : (γ : GL (Fin 2) F) • L = L :=
    hΓ γ.2
  beta_reduce
  refine ⟨?_, ?_⟩
  · rw [Subgroup.smul_def, ← hγ, smul_comm_submodule]
    exact Submodule.map_mono h₂
  · rw [Subgroup.smul_def]
    exact (smul_comm_submodule c _ N).trans_le ((Submodule.map_mono h₁).trans_eq hγ)

lemma isCommensurableLattice_lattice (h𝔟 : 𝔟 ≠ 0) :
    IsCommensurableLattice (lattice 𝔟) (integralLattice F) := by
  refine isCommensurableLattice_pi fun i ↦ ?_
  fin_cases i
  exacts [isCommensurableLattice_refl 1, isCommensurableLattice_fractionalIdeal h𝔟]

lemma isCommensurableLattice_gammaZeroLattice (h𝔟 : 𝔟 ≠ 0) (h𝔑 : 𝔑 ≠ ⊥) :
    IsCommensurableLattice (gammaZeroLattice 𝔟 𝔑) (integralLattice F) := by
  refine isCommensurableLattice_pi fun i ↦ ?_
  fin_cases i
  exacts [isCommensurableLattice_refl 1,
    isCommensurableLattice_ideal_smul h𝔑 (isCommensurableLattice_fractionalIdeal h𝔟)]

lemma isFiniteRelIndex_conj_smul_gammaZero (h𝔟 : 𝔟 ≠ 0) (h𝔑 : 𝔑 ≠ ⊥) (g : GL (Fin 2) F) :
    (MulAut.conj g • gammaZero 𝔟 (glPlus 𝔟) 𝔑).IsFiniteRelIndex (gammaZero 𝔟 (glPlus 𝔟) 𝔑) := by
  have h₁ : IsCommensurableLattice (lattice 𝔟) (integralLattice F) :=
    isCommensurableLattice_lattice h𝔟
  have h₂ : IsCommensurableLattice (gammaZeroLattice 𝔟 𝔑) (integralLattice F) :=
    isCommensurableLattice_gammaZeroLattice h𝔟 h𝔑
  have hg (L : Submodule (𝓞 F) (Fin 2 → F)) (hL : IsCommensurableLattice L (integralLattice F)) :
      IsCommensurableLattice (g • L) (lattice 𝔟) :=
    ((hL.smul_gl g).trans (isCommensurableLattice_gl_smul g)).trans h₁.symm
  have hΓ : gammaZero 𝔟 (glPlus 𝔟) 𝔑 ≤ MulAction.stabilizer (GL (Fin 2) F) (lattice 𝔟) :=
    fun _ hx ↦ (gl_eq_stabilizer 𝔟).le hx.1.1
  have hK : (MulAction.stabilizer (GL (Fin 2) F) (g • lattice 𝔟) ⊓
      MulAction.stabilizer (GL (Fin 2) F) (g • gammaZeroLattice 𝔟 𝔑) ⊓
      gammaZero 𝔟 (glPlus 𝔟) 𝔑).IsFiniteRelIndex (gammaZero 𝔟 (glPlus 𝔟) 𝔑) := by
    rw [isFiniteRelIndex_iff_relIndex_ne_zero, inf_relIndex_right,
      ← isFiniteRelIndex_iff_relIndex_ne_zero]
    exact (isFiniteRelIndex_stabilizer hΓ h₁ (hg _ h₁)).inf
      (isFiniteRelIndex_stabilizer hΓ h₁ (hg _ h₂))
  refine @isFiniteRelIndex_of_le_left _ _ _ _ _ hK fun x hx ↦ ?_
  rcases hx with ⟨⟨hx₁, hx₂⟩, hx₃⟩
  have hstab (L : Submodule (𝓞 F) (Fin 2 → F)) (hxL : x ∈ MulAction.stabilizer _ (g • L)) :
      g⁻¹ * x * g ∈ MulAction.stabilizer (GL (Fin 2) F) L := by
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj] at hxL
    rcases hxL with ⟨y, hy, rfl⟩
    rwa [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_assoc, inv_mul_cancel_right,
      inv_mul_cancel_left]
  rw [gammaZero_eq] at hx₃
  rw [mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv,
    gammaZero_eq]
  refine ⟨⟨(gl_eq_stabilizer 𝔟).ge (hstab _ hx₁), Subgroup.mem_comap.mpr ?_⟩, hstab _ hx₂⟩
  rw [map_mul, map_mul, map_inv, mul_comm, mul_inv_cancel_left]
  exact hx₃.1.2

/-- **Every element of `GL₂(F)` commensurates `Γ₀(𝔑)_𝔟`**: for `g ∈ GL₂(F)`, the subgroup of
`Γ₀(𝔑)_𝔟` stabilising the lattices `g(𝒪_F ⊕ 𝔟)` and `g(𝒪_F ⊕ 𝔑𝔟)` lies in `gΓ₀(𝔑)_𝔟g⁻¹`, and
has finite index in `Γ₀(𝔑)_𝔟`: its orbits on lattices lie in the finite set of lattices `N` with
`c L ⊆ N` and `c N ⊆ L` for a fixed `c ≠ 0`. -/
lemma mem_commensurator_gammaZero (h𝔟 : 𝔟 ≠ 0) (h𝔑 : 𝔑 ≠ ⊥) (g : GL (Fin 2) F) :
    g ∈ commensurator (gammaZero 𝔟 (glPlus 𝔟) 𝔑) := by
  refine ⟨isFiniteRelIndex_conj_smul_gammaZero h𝔟 h𝔑 g, ?_⟩
  rw [isFiniteRelIndex_iff_relIndex_ne_zero, ← relIndex_pointwise_smul (MulAut.conj g⁻¹),
    smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul,
    ← isFiniteRelIndex_iff_relIndex_ne_zero]
  exact isFiniteRelIndex_conj_smul_gammaZero h𝔟 h𝔑 g⁻¹

instance [NeZero 𝔟] [NeZero 𝔑] :
    IsHeckeTriple (glTotallyPositive F) (gammaZero 𝔟 (glPlus 𝔟) 𝔑) (gammaZero 𝔟 (glPlus 𝔟) 𝔑) :=
  .of_diagonal gammaZero_le_glTotallyPositive fun g _ ↦
    mem_commensurator_gammaZero (NeZero.ne 𝔟) (NeZero.ne 𝔑) g

variable (𝔟 𝔑) in
/-- The **Hecke ring** of `Γ₀(𝔑)_𝔟`: the complex Hecke ring of the Hecke pair
`(Γ₀(𝔑)_𝔟, GL₂⁺(F))`, with basis the double cosets `Γ₀(𝔑)_𝔟 α Γ₀(𝔑)_𝔟`, `α ∈ GL₂⁺(F)`, each a
finite union of right cosets since `α` commensurates `Γ₀(𝔑)_𝔟`. It is a ring when `𝔟 ≠ 0` and
`𝔑 ≠ 0` (instances `NeZero 𝔟` and `NeZero 𝔑`). -/
abbrev hilbertHeckeRing : Type _ :=
  HeckeRing (glTotallyPositive F) (gammaZero 𝔟 (glPlus 𝔟) 𝔑) ℂ

variable (𝔟 𝔑) in
/-- The **Hecke operator `T_𝔭`** of `Γ₀(𝔑)_𝔟` for a prime `𝔭 = (π)` with `π` totally positive,
that is, `𝔭` trivial in the narrow class group: the double coset `Γ₀(𝔑)_𝔟 diag(1, π) Γ₀(𝔑)_𝔟`. It
is defined for every totally positive `π ∈ Fˣ`; it is the Hecke operator `T_𝔭` of the LMFDB when `π`
is integral and generates a prime ideal `𝔭 ∤ 𝔑`. -/
noncomputable def heckeT (π : Fˣ) (hπ : IsTotallyPositive (π : F)) :
    HeckeCoset (glTotallyPositive F) (gammaZero 𝔟 (glPlus 𝔟) 𝔑) (gammaZero 𝔟 (glPlus 𝔟) 𝔑) :=
  HeckeCoset.mk _ _ (heckeDiagonal π hπ)

end HilbertModularGroup
