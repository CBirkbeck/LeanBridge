import LeanBridge.ForMathlib.AlgebraicGeometry.HilbertModularSurface.LevelGammaZero
import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Strong approximation for `SL(𝒪_F ⊕ 𝔟)` and the level of its congruence subgroups

Let `F` be a number field with ring of integers `𝒪_F` and `𝔟` a nonzero fractional ideal of `F`.
For ideals `𝔐` and `𝔑` of `𝒪_F`, the principal congruence subgroups (LMFDB
`hmsurface.congruence_subgroup`) of `SL(𝒪_F ⊕ 𝔟)` satisfy `Γ_𝔟(𝔐 + 𝔑) = Γ_𝔟(𝔐) Γ_𝔟(𝔑)`, a
form of strong approximation for `SL₂`. The proof is Shimura's for `SL₂(ℤ)`. Write an element `g`
of `Γ_𝔟(𝔐 + 𝔑)` as `1 + P + Q`, where `P` maps `𝒪_F ⊕ 𝔟` into `𝔐(𝒪_F ⊕ 𝔟)` and `Q` maps it into
`𝔑(𝒪_F ⊕ 𝔟)`. Then `1 + Q` has determinant `1` modulo `𝔐 ∩ 𝔑`, and a matrix `(a, b; c, d)`
preserving `𝒪_F ⊕ 𝔟` with determinant `1` modulo a nonzero ideal `𝔄` is congruent modulo `𝔄` to
an element of `SL(𝒪_F ⊕ 𝔟)`: make `c` nonzero, make `d` prime to `c𝔟⁻¹` by prime avoidance, solve
`xd + yc = 1` with `x ∈ 𝒪_F` and `y ∈ 𝔟⁻¹`, and add `ε(x, -y)` to the top row, where `ε` is `1`
minus the determinant. This gives an element `k` of `Γ_𝔟(𝔑)` congruent to `g` modulo `𝔐`, so that
`gk⁻¹ ∈ Γ_𝔟(𝔐)`.

So for every subgroup `Γ` of `GL₂(F)`, the nonzero ideals `𝔑` with `Γ_𝔟(𝔑) ≤ Γ` in
`SL(𝒪_F ⊕ 𝔟)` are closed under sums, and when there is one, the largest of them, which exists by
noetherianity, is the level of `Γ` in the sense of `HilbertModularGroup.IsLevel`: a congruence
subgroup of `SL(𝒪_F ⊕ 𝔟)` has a level.

## Main results

* `Ideal.exists_mem_span_singleton_add_sup_eq_top`: if `(d) + 𝔠 + 𝔄 = R` in a Dedekind domain `R`
  with `𝔠 ≠ 0`, then `(d + μ) + 𝔠 = R` for some `μ ∈ 𝔄`.
* `HilbertModularGroup.exists_det_add_eq_one`: a matrix preserving `𝒪_F ⊕ 𝔟` with determinant `1`
  modulo `𝔄` is congruent modulo `𝔄` to a matrix with determinant `1`.
* `HilbertModularGroup.principalCongruenceSubgroup_sup` (LMFDB `hmsurface.congruence_subgroup`):
  `Γ_𝔟(𝔐 + 𝔑) = Γ_𝔟(𝔐) ⊔ Γ_𝔟(𝔑)` in `SL(𝒪_F ⊕ 𝔟)`.
* `HilbertModularGroup.isLevel_level` (LMFDB `hmsurface.congruence_subgroup`): a congruence
  subgroup of `SL(𝒪_F ⊕ 𝔟)` has a level, `HilbertModularGroup.level`.

## References

* G. Shimura, *Introduction to the arithmetic theory of automorphic functions*, Princeton
  University Press (1971), Lemma 1.38.
-/

open IsDedekindDomain Matrix NumberField FractionalIdeal

open scoped nonZeroDivisors

namespace Ideal

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {𝔠 𝔄 : Ideal R} {d : R}

/-- **A unimodular lift by prime avoidance**: in a Dedekind domain, if `(d) + 𝔠 + 𝔄 = R` with
`𝔠 ≠ 0`, then `(d + μ) + 𝔠 = R` for some `μ ∈ 𝔄`. -/
lemma exists_mem_span_singleton_add_sup_eq_top (h𝔠 : 𝔠 ≠ ⊥) (h : span {d} ⊔ 𝔠 ⊔ 𝔄 = ⊤) :
    ∃ μ ∈ 𝔄, span {d + μ} ⊔ 𝔠 = ⊤ := by
  classical
  have hfin : {v : HeightOneSpectrum R | v.asIdeal ∣ 𝔠}.Finite := finite_factors h𝔠
  let S : Finset (HeightOneSpectrum R) := hfin.toFinset
  let J : Ideal R := 𝔄 * ∏ v ∈ S.filter (fun v ↦ d ∉ v.asIdeal), v.asIdeal
  let A : Set (Ideal R) := HeightOneSpectrum.asIdeal '' (S.filter (fun v ↦ d ∈ v.asIdeal) : Set _)
  have hs : A.Finite := (Finset.finite_toSet _).image _
  have hJ : ¬(J : Set R) ⊆ ⋃ P ∈ A, (P : Set R) := by
    rw [subset_union_prime_finite hs ⊥ ⊥ fun P hP _ _ ↦ ?_]
    · rintro ⟨P, ⟨v, hv, rfl⟩, hJv⟩
      rcases Finset.mem_filter.mp hv with ⟨hvS, hdv⟩
      rcases v.isPrime.mul_le.mp hJv with h𝔄 | hprod
      · have hle : span {d} ⊔ 𝔠 ⊔ 𝔄 ≤ v.asIdeal :=
          sup_le (sup_le ((span_singleton_le_iff_mem _).mpr hdv)
            (le_of_dvd (hfin.mem_toFinset.mp hvS))) h𝔄
        rw [h] at hle
        exact v.isPrime.ne_top (top_le_iff.mp hle)
      · rcases v.isPrime.prod_le.mp hprod with ⟨w, hw, hwv⟩
        have hwv' : w.asIdeal = v.asIdeal := w.isMaximal.eq_of_le v.isPrime.ne_top hwv
        exact (Finset.mem_filter.mp hw).2 (hwv' ▸ hdv)
    · rcases hP with ⟨v, -, rfl⟩
      exact v.isPrime
  rcases Set.not_subset.mp hJ with ⟨μ, hμJ, hμ⟩
  refine ⟨μ, mul_le_left hμJ, ?_⟩
  by_contra hne
  rcases exists_le_maximal _ hne with ⟨M, hM, hle⟩
  have hcM : 𝔠 ≤ M := le_sup_right.trans hle
  have hdM : d + μ ∈ M := hle (mem_sup_left (mem_span_singleton_self _))
  let v : HeightOneSpectrum R := ⟨M, hM.isPrime, ne_bot_of_le_ne_bot h𝔠 hcM⟩
  have hvS : v ∈ S := hfin.mem_toFinset.mpr (dvd_iff_le.mpr hcM)
  by_cases hd : d ∈ M
  · exact hμ (Set.mem_biUnion ⟨v, Finset.mem_filter.mpr ⟨hvS, hd⟩, rfl⟩
      ((add_mem_cancel_left hd).mp hdM))
  · have hμM : μ ∈ M := (mul_le_right.trans (le_of_dvd (Finset.dvd_prod_of_mem
      (fun w : HeightOneSpectrum R ↦ w.asIdeal) (Finset.mem_filter.mpr ⟨hvS, hd⟩)))) hμJ
    exact hd ((add_mem_cancel_right hμM).mp hdM)

end Ideal

namespace HilbertModularGroup

variable {F : Type*} [Field F] (𝔟 : FractionalIdeal (𝓞 F)⁰ F) {𝔐 𝔑 𝔄 : Ideal (𝓞 F)}
  {I J K : FractionalIdeal (𝓞 F)⁰ F} {g k : GL (Fin 2) F} {M : Matrix (Fin 2) (Fin 2) F}
  {v : Fin 2 → F} {x y : F}

/-! ### The lattice `𝔑(𝒪_F ⊕ 𝔟)` in terms of fractional ideals -/

private lemma add_mem_of_mem (hx : x ∈ I) (hy : y ∈ I) : x + y ∈ I :=
  (I : Submodule (𝓞 F) F).add_mem hx hy

private lemma sub_mem_of_mem (hx : x ∈ I) (hy : y ∈ I) : x - y ∈ I :=
  (I : Submodule (𝓞 F) F).sub_mem hx hy

private lemma neg_mem_of_mem (hx : x ∈ I) : -x ∈ I :=
  (I : Submodule (𝓞 F) F).neg_mem hx

private lemma mul_mem_of_mul_eq (hx : x ∈ I) (hy : y ∈ J) (h : I * J = K) : x * y ∈ K :=
  h ▸ mul_mem_mul hx hy

lemma single_zero_mem_lattice : (Pi.single 0 1 : Fin 2 → F) ∈ lattice 𝔟 := by
  refine (mem_lattice 𝔟).mpr ⟨by simp, ?_⟩
  simpa using FractionalIdeal.zero_mem 𝔟

lemma single_one_mem_lattice (hy : y ∈ 𝔟) : Pi.single 1 y ∈ lattice 𝔟 :=
  (mem_lattice 𝔟).mpr ⟨by simp, by simpa using hy⟩

lemma apply_zero_mem_of_mem_smul_lattice (hv : v ∈ 𝔑 • lattice 𝔟) :
    v 0 ∈ (𝔑 : FractionalIdeal (𝓞 F)⁰ F) := by
  let π : (Fin 2 → F) →ₗ[𝓞 F] F := (LinearMap.proj (R := F) 0).restrictScalars (𝓞 F)
  have h : (𝔑 • lattice 𝔟).map π ≤ 𝔑 • (1 : Submodule (𝓞 F) F) := by
    rw [Submodule.map_smul'']
    exact smul_mono_right _ (Submodule.map_le_iff_le_comap.mpr fun w hw ↦
      ((mem_lattice 𝔟).mp hw).1)
  have h' : 𝔑 • (1 : Submodule (𝓞 F) F) ≤ ((𝔑 : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) :=
    Submodule.smul_le.mpr fun r hr y hy ↦ by
      rcases Submodule.mem_one.mp hy with ⟨y, rfl⟩
      rw [Algebra.smul_def, ← map_mul]
      exact mem_coeIdeal_of_mem _ (Ideal.mul_mem_right _ _ hr)
  exact h' (h ⟨v, hv, rfl⟩)

lemma apply_one_mem_mul_of_mem_smul_lattice (hv : v ∈ 𝔑 • lattice 𝔟) :
    v 1 ∈ (𝔑 : FractionalIdeal (𝓞 F)⁰ F) * 𝔟 := by
  have h : 𝔑 • (𝔟 : Submodule (𝓞 F) F) ≤
      (((𝔑 : FractionalIdeal (𝓞 F)⁰ F) * 𝔟 : FractionalIdeal (𝓞 F)⁰ F) : Submodule (𝓞 F) F) :=
    Submodule.smul_le.mpr fun r hr y hy ↦ by
      rw [Algebra.smul_def]
      exact mul_mem_mul (mem_coeIdeal_of_mem _ hr) hy
  exact h (apply_one_mem_of_mem_smul_lattice 𝔟 𝔑 hv)

lemma mem_smul_lattice_of_mem (h₀ : v 0 ∈ (𝔑 : FractionalIdeal (𝓞 F)⁰ F))
    (h₁ : v 1 ∈ (𝔑 : FractionalIdeal (𝓞 F)⁰ F) * 𝔟) : v ∈ 𝔑 • lattice 𝔟 := by
  have hv : v = Pi.single 0 (v 0) + Pi.single 1 (v 1) := by
    ext i
    fin_cases i <;> simp
  rw [hv]
  refine add_mem ?_ (single_mem_smul_lattice 𝔟 ?_)
  · rcases (mem_coeIdeal _).mp h₀ with ⟨r, hr, e⟩
    have e' : (Pi.single 0 (v 0) : Fin 2 → F) = r • (Pi.single 0 1 : Fin 2 → F) := by
      rw [← e]
      ext i
      fin_cases i <;> simp [Algebra.smul_def]
    rw [e']
    exact Submodule.smul_mem_smul hr (single_zero_mem_lattice 𝔟)
  · refine FractionalIdeal.mul_induction_on h₁ (fun i hi j hj ↦ ?_) fun _ _ ↦ add_mem
    rcases (mem_coeIdeal _).mp hi with ⟨r, hr, rfl⟩
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem_smul hr hj

/-! ### Matrices in terms of their entries -/

lemma apply_zero_zero_mem_of_forall (hM : ∀ v ∈ lattice 𝔟, M *ᵥ v ∈ 𝔑 • lattice 𝔟) :
    M 0 0 ∈ (𝔑 : FractionalIdeal (𝓞 F)⁰ F) := by
  simpa using apply_zero_mem_of_mem_smul_lattice 𝔟 (hM _ (single_zero_mem_lattice 𝔟))

lemma apply_one_zero_mem_of_forall (hM : ∀ v ∈ lattice 𝔟, M *ᵥ v ∈ 𝔑 • lattice 𝔟) :
    M 1 0 ∈ (𝔑 : FractionalIdeal (𝓞 F)⁰ F) * 𝔟 := by
  simpa using apply_one_mem_mul_of_mem_smul_lattice 𝔟 (hM _ (single_zero_mem_lattice 𝔟))

lemma mul_inv_mem_reductionKernel (hg : g ∈ gl 𝔟) (hk : k ∈ gl 𝔟)
    (h : ∀ v ∈ lattice 𝔟, (g.val - k.val) *ᵥ v ∈ 𝔐 • lattice 𝔟) :
    g * k⁻¹ ∈ reductionKernel 𝔟 𝔐 := by
  refine ⟨mul_mem hg (inv_mem hk), fun v hv ↦ ?_⟩
  have h₁ : (g.val - k.val) *ᵥ ((k⁻¹).val *ᵥ v) ∈ 𝔐 • lattice 𝔟 := h _ ((inv_mem hk v).mp hv)
  rwa [sub_mulVec, mulVec_mulVec, mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, mul_inv_cancel,
    Units.val_one, one_mulVec] at h₁

variable [NumberField F]

lemma mem_mul_inv_of_forall (h𝔟 : 𝔟 ≠ 0) (h : ∀ y ∈ 𝔟, x * y ∈ I) : x ∈ I * 𝔟⁻¹ := by
  have h₁ : spanSingleton (𝓞 F)⁰ x * 𝔟 ≤ I := mul_le.mpr fun i hi j hj ↦ by
    rcases (mem_spanSingleton _).mp hi with ⟨z, rfl⟩
    rw [smul_mul_assoc]
    exact (I : Submodule (𝓞 F) F).smul_mem z (h j hj)
  have h₂ : spanSingleton (𝓞 F)⁰ x * 𝔟 * 𝔟⁻¹ ≤ I * 𝔟⁻¹ := mul_le_mul_left h₁ 𝔟⁻¹
  rw [mul_inv_cancel_right₀ h𝔟] at h₂
  exact h₂ (mem_spanSingleton_self _ x)

lemma apply_zero_one_mem_of_forall (h𝔟 : 𝔟 ≠ 0) (hM : ∀ v ∈ lattice 𝔟, M *ᵥ v ∈ 𝔑 • lattice 𝔟) :
    M 0 1 ∈ (𝔑 : FractionalIdeal (𝓞 F)⁰ F) * 𝔟⁻¹ :=
  mem_mul_inv_of_forall 𝔟 h𝔟 fun y hy ↦ by
    simpa using apply_zero_mem_of_mem_smul_lattice 𝔟 (hM _ (single_one_mem_lattice 𝔟 hy))

lemma apply_one_one_mem_of_forall (h𝔟 : 𝔟 ≠ 0) (hM : ∀ v ∈ lattice 𝔟, M *ᵥ v ∈ 𝔑 • lattice 𝔟) :
    M 1 1 ∈ (𝔑 : FractionalIdeal (𝓞 F)⁰ F) := by
  have h : M 1 1 ∈ (𝔑 : FractionalIdeal (𝓞 F)⁰ F) * 𝔟 * 𝔟⁻¹ :=
    mem_mul_inv_of_forall 𝔟 h𝔟 fun y hy ↦ by
      simpa using apply_one_mem_mul_of_mem_smul_lattice 𝔟 (hM _ (single_one_mem_lattice 𝔟 hy))
  rwa [mul_inv_cancel_right₀ h𝔟] at h

lemma forall_mulVec_mem_smul_lattice (h𝔟 : 𝔟 ≠ 0) (h₀₀ : M 0 0 ∈ (𝔑 : FractionalIdeal (𝓞 F)⁰ F))
    (h₀₁ : M 0 1 ∈ (𝔑 : FractionalIdeal (𝓞 F)⁰ F) * 𝔟⁻¹)
    (h₁₀ : M 1 0 ∈ (𝔑 : FractionalIdeal (𝓞 F)⁰ F) * 𝔟)
    (h₁₁ : M 1 1 ∈ (𝔑 : FractionalIdeal (𝓞 F)⁰ F)) : ∀ v ∈ lattice 𝔟, M *ᵥ v ∈ 𝔑 • lattice 𝔟 := by
  intro v hv
  rcases (mem_lattice 𝔟).mp hv with ⟨hv₀, hv₁⟩
  have hv₀' : v 0 ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := (mem_one_iff _).mpr (Submodule.mem_one.mp hv₀)
  refine mem_smul_lattice_of_mem 𝔟 ?_ ?_ <;> simp only [mulVec, dotProduct, Fin.sum_univ_two]
  · exact add_mem_of_mem (mul_mem_of_mul_eq h₀₀ hv₀' (mul_one _))
      (mul_mem_of_mul_eq h₀₁ hv₁ (inv_mul_cancel_right₀ h𝔟 _))
  · exact add_mem_of_mem (mul_mem_of_mul_eq h₁₀ hv₀' (mul_one _)) (mul_mem_mul h₁₁ hv₁)

lemma forall_adjugate_mulVec_mem (h𝔟 : 𝔟 ≠ 0) (hM : ∀ v ∈ lattice 𝔟, M *ᵥ v ∈ 𝔑 • lattice 𝔟) :
    ∀ v ∈ lattice 𝔟, adjugate M *ᵥ v ∈ 𝔑 • lattice 𝔟 := by
  rw [adjugate_fin_two]
  refine forall_mulVec_mem_smul_lattice 𝔟 h𝔟 ?_ ?_ ?_ ?_
  · simpa using apply_one_one_mem_of_forall 𝔟 h𝔟 hM
  · simpa using neg_mem_of_mem (apply_zero_one_mem_of_forall 𝔟 h𝔟 hM)
  · simpa using neg_mem_of_mem (apply_one_zero_mem_of_forall 𝔟 hM)
  · simpa using apply_zero_zero_mem_of_forall 𝔟 hM

lemma mem_gl_of_forall (h𝔟 : 𝔟 ≠ 0) (hg : ∀ v ∈ lattice 𝔟, g.val *ᵥ v ∈ lattice 𝔟)
    (hdet : g.val.det = 1) : g ∈ gl 𝔟 := by
  have hg' : ∀ v ∈ lattice 𝔟, g.val *ᵥ v ∈ (⊤ : Ideal (𝓞 F)) • lattice 𝔟 := by simpa using hg
  refine fun v ↦ ⟨hg v, fun hv ↦ ?_⟩
  have h : adjugate g.val *ᵥ (g.val *ᵥ v) ∈ (⊤ : Ideal (𝓞 F)) • lattice 𝔟 :=
    forall_adjugate_mulVec_mem 𝔟 h𝔟 hg' _ hv
  rwa [mulVec_mulVec, adjugate_mul, hdet, one_smul, one_mulVec, Submodule.top_smul] at h

lemma det_one_add_sub_one_mem (h𝔟 : 𝔟 ≠ 0) (hM : ∀ v ∈ lattice 𝔟, M *ᵥ v ∈ 𝔑 • lattice 𝔟) :
    (1 + M).det - 1 ∈ (𝔑 : FractionalIdeal (𝓞 F)⁰ F) := by
  have h₀₀ : M 0 0 ∈ (𝔑 : FractionalIdeal (𝓞 F)⁰ F) := apply_zero_zero_mem_of_forall 𝔟 hM
  have h₁ : 1 + M 0 0 ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) :=
    add_mem_of_mem (one_mem_one _) (coeIdeal_le_one h₀₀)
  have h₀₁ : M 0 1 ∈ 𝔟⁻¹ :=
    mul_le_of_le_one_left' coeIdeal_le_one (apply_zero_one_mem_of_forall 𝔟 h𝔟 hM)
  have e : (1 + M).det - 1 = M 0 0 + M 1 1 * (1 + M 0 0) - M 1 0 * M 0 1 := by
    rw [det_fin_two]
    simp
    ring1
  rw [e]
  exact sub_mem_of_mem (add_mem_of_mem h₀₀
    (mul_mem_of_mul_eq (apply_one_one_mem_of_forall 𝔟 h𝔟 hM) h₁ (mul_one _)))
    (mul_mem_of_mul_eq (apply_one_zero_mem_of_forall 𝔟 hM) h₀₁ (mul_inv_cancel_right₀ h𝔟 _))

lemma exists_add_eq_of_forall (h𝔟 : 𝔟 ≠ 0) (hM : ∀ v ∈ lattice 𝔟, M *ᵥ v ∈ (𝔐 ⊔ 𝔑) • lattice 𝔟) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) F, (∀ v ∈ lattice 𝔟, P *ᵥ v ∈ 𝔐 • lattice 𝔟) ∧
      (∀ v ∈ lattice 𝔟, Q *ᵥ v ∈ 𝔑 • lattice 𝔟) ∧ P + Q = M := by
  have h₀₀ : M 0 0 ∈ (𝔐 : FractionalIdeal (𝓞 F)⁰ F) + 𝔑 := by
    simpa using apply_zero_zero_mem_of_forall 𝔟 hM
  have h₀₁ : M 0 1 ∈ (𝔐 : FractionalIdeal (𝓞 F)⁰ F) * 𝔟⁻¹ + 𝔑 * 𝔟⁻¹ := by
    simpa [add_mul] using apply_zero_one_mem_of_forall 𝔟 h𝔟 hM
  have h₁₀ : M 1 0 ∈ (𝔐 : FractionalIdeal (𝓞 F)⁰ F) * 𝔟 + 𝔑 * 𝔟 := by
    simpa [add_mul] using apply_one_zero_mem_of_forall 𝔟 hM
  have h₁₁ : M 1 1 ∈ (𝔐 : FractionalIdeal (𝓞 F)⁰ F) + 𝔑 := by
    simpa using apply_one_one_mem_of_forall 𝔟 h𝔟 hM
  rcases (mem_add _ _ _).mp h₀₀ with ⟨p₀₀, hp₀₀, q₀₀, hq₀₀, e₀₀⟩
  rcases (mem_add _ _ _).mp h₀₁ with ⟨p₀₁, hp₀₁, q₀₁, hq₀₁, e₀₁⟩
  rcases (mem_add _ _ _).mp h₁₀ with ⟨p₁₀, hp₁₀, q₁₀, hq₁₀, e₁₀⟩
  rcases (mem_add _ _ _).mp h₁₁ with ⟨p₁₁, hp₁₁, q₁₁, hq₁₁, e₁₁⟩
  refine ⟨!![p₀₀, p₀₁; p₁₀, p₁₁], !![q₀₀, q₀₁; q₁₀, q₁₁], forall_mulVec_mem_smul_lattice 𝔟 h𝔟
    (by simpa) (by simpa) (by simpa) (by simpa), forall_mulVec_mem_smul_lattice 𝔟 h𝔟 (by simpa)
    (by simpa) (by simpa) (by simpa), ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [e₀₀, e₀₁, e₁₀, e₁₁]

/-- **Lifting to `SL(𝒪_F ⊕ 𝔟)`**: if a matrix `M` preserving `𝒪_F ⊕ 𝔟` has determinant `1`
modulo a nonzero ideal `𝔄`, then `M + Y` has determinant `1` for a matrix `Y` mapping
`𝒪_F ⊕ 𝔟` into `𝔄(𝒪_F ⊕ 𝔟)`. -/
lemma exists_det_add_eq_one (h𝔟 : 𝔟 ≠ 0) (h𝔄 : 𝔄 ≠ ⊥) (hM : ∀ v ∈ lattice 𝔟, M *ᵥ v ∈ lattice 𝔟)
    (h : M.det - 1 ∈ (𝔄 : FractionalIdeal (𝓞 F)⁰ F)) : ∃ Y : Matrix (Fin 2) (Fin 2) F,
      (∀ v ∈ lattice 𝔟, Y *ᵥ v ∈ 𝔄 • lattice 𝔟) ∧ (M + Y).det = 1 := by
  have hM' : ∀ v ∈ lattice 𝔟, M *ᵥ v ∈ (⊤ : Ideal (𝓞 F)) • lattice 𝔟 := by simpa using hM
  have ha : M 0 0 ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    simpa using apply_zero_zero_mem_of_forall 𝔟 hM'
  have hb : M 0 1 ∈ 𝔟⁻¹ := by simpa using apply_zero_one_mem_of_forall 𝔟 h𝔟 hM'
  have hc : M 1 0 ∈ 𝔟 := by simpa using apply_one_zero_mem_of_forall 𝔟 hM'
  have hd : M 1 1 ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    simpa using apply_one_one_mem_of_forall 𝔟 h𝔟 hM'
  have hγ : ∃ γ ∈ (𝔄 : FractionalIdeal (𝓞 F)⁰ F) * 𝔟, M 1 0 + γ ≠ 0 := by
    by_cases hc₀ : M 1 0 = 0
    · rcases Submodule.exists_mem_ne_zero_of_ne_bot (coeToSubmodule_ne_bot.mpr
        (mul_ne_zero (coeIdeal_ne_zero.mpr h𝔄) h𝔟)) with ⟨γ, hγ, hγ₀⟩
      exact ⟨γ, hγ, by rwa [hc₀, zero_add]⟩
    · exact ⟨0, FractionalIdeal.zero_mem _, by rwa [add_zero]⟩
  rcases hγ with ⟨γ, hγ, hcγ⟩
  have hc' : M 1 0 + γ ∈ 𝔟 := add_mem_of_mem hc (mul_le_of_le_one_left' coeIdeal_le_one hγ)
  have h𝔠 : spanSingleton (𝓞 F)⁰ (M 1 0 + γ) * 𝔟⁻¹ ≤ 1 := by
    simpa [mul_inv_cancel₀ h𝔟] using mul_le_mul_left (spanSingleton_le_iff_mem.mpr hc') 𝔟⁻¹
  rcases le_one_iff_exists_coeIdeal.mp h𝔠 with ⟨𝔠, e𝔠⟩
  have h𝔠₀ : 𝔠 ≠ ⊥ := by
    rw [← coeIdeal_ne_zero (K := F), e𝔠]
    exact mul_ne_zero (spanSingleton_ne_zero_iff.mpr hcγ) (inv_ne_zero h𝔟)
  rcases (mem_one_iff _).mp ha with ⟨s, hs⟩
  rcases (mem_one_iff _).mp hd with ⟨r, hr⟩
  have hw : M 0 1 * (M 1 0 + γ) ∈ (𝔠 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [e𝔠, mul_comm (M 0 1)]
    exact mul_mem_mul (mem_spanSingleton_self _ _) hb
  rcases (mem_coeIdeal _).mp hw with ⟨w, hw, ew⟩
  have hη : M 0 0 * M 1 1 - M 0 1 * (M 1 0 + γ) - 1 ∈ (𝔄 : FractionalIdeal (𝓞 F)⁰ F) := by
    have e : M 0 0 * M 1 1 - M 0 1 * (M 1 0 + γ) - 1 = M.det - 1 - γ * M 0 1 := by
      rw [det_fin_two]
      ring1
    rw [e]
    exact sub_mem_of_mem h (mul_mem_of_mul_eq hγ hb (mul_inv_cancel_right₀ h𝔟 _))
  rcases (mem_coeIdeal _).mp hη with ⟨η, hη𝔄, eη⟩
  have htop : Ideal.span {r} ⊔ 𝔠 ⊔ 𝔄 = ⊤ := by
    have e : s * r - w - η = 1 := IsFractionRing.injective (𝓞 F) F (by
      rw [map_sub, map_sub, map_mul, hs, hr, ew, eη, map_one]
      ring1)
    rw [Ideal.eq_top_iff_one, ← e]
    exact sub_mem (sub_mem (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mul_mem_left _ s
      (Ideal.mem_span_singleton_self r)))) (Ideal.mem_sup_left (Ideal.mem_sup_right hw)))
      (Ideal.mem_sup_right hη𝔄)
  rcases Ideal.exists_mem_span_singleton_add_sup_eq_top h𝔠₀ htop with ⟨μ, hμ, hμ𝔠⟩
  rcases Ideal.mem_span_singleton_sup.mp ((Ideal.eq_top_iff_one _).mp hμ𝔠) with ⟨z, t, ht, ezt⟩
  have ht' : algebraMap (𝓞 F) F t ∈ spanSingleton (𝓞 F)⁰ (M 1 0 + γ) * 𝔟⁻¹ :=
    e𝔠 ▸ mem_coeIdeal_of_mem _ ht
  rcases mem_singleton_mul.mp ht' with ⟨y, hy, ey⟩
  have key : algebraMap (𝓞 F) F z * (M 1 1 + algebraMap (𝓞 F) F μ) + (M 1 0 + γ) * y = 1 := by
    rw [← hr, ← ey, ← map_add, ← map_mul, ← map_add, ezt, map_one]
  let ε : F := 1 - (M 0 0 * (M 1 1 + algebraMap (𝓞 F) F μ) - M 0 1 * (M 1 0 + γ))
  have hμ' : algebraMap (𝓞 F) F μ ∈ (𝔄 : FractionalIdeal (𝓞 F)⁰ F) := mem_coeIdeal_of_mem _ hμ
  have hε : ε ∈ (𝔄 : FractionalIdeal (𝓞 F)⁰ F) := by
    have e : ε = -(M 0 0 * M 1 1 - M 0 1 * (M 1 0 + γ) - 1) - algebraMap (𝓞 F) F μ * M 0 0 := by
      ring1
    rw [e]
    exact sub_mem_of_mem (neg_mem_of_mem hη) (mul_mem_of_mul_eq hμ' ha (mul_one _))
  refine ⟨!![ε * algebraMap (𝓞 F) F z, -(ε * y); γ, algebraMap (𝓞 F) F μ],
    forall_mulVec_mem_smul_lattice 𝔟 h𝔟 ?_ ?_ (by simpa) (by simpa), ?_⟩
  · simpa using mul_mem_of_mul_eq hε (coe_mem_one _ z) (mul_one _)
  · simpa using neg_mem_of_mem (mul_mem_mul hε hy)
  · rw [det_fin_two]
    simp only [Matrix.add_apply, of_apply, cons_val_zero, cons_val_one]
    linear_combination ε * key

lemma principalCongruenceSubgroup_sup_le (h𝔟 : 𝔟 ≠ 0) :
    principalCongruenceSubgroup 𝔟 (sl 𝔟) (𝔐 ⊔ 𝔑) ≤
      principalCongruenceSubgroup 𝔟 (sl 𝔟) 𝔐 ⊔ principalCongruenceSubgroup 𝔟 (sl 𝔟) 𝔑 := by
  rcases eq_or_ne 𝔐 ⊥ with rfl | h𝔐
  · rw [bot_sup_eq]
    exact le_sup_right
  rcases eq_or_ne 𝔑 ⊥ with rfl | h𝔑
  · rw [sup_bot_eq]
    exact le_sup_left
  rintro g ⟨hgsl, -, hg⟩
  have hM : ∀ v ∈ lattice 𝔟, (g.val - 1) *ᵥ v ∈ (𝔐 ⊔ 𝔑) • lattice 𝔟 := fun v hv ↦ by
    rw [sub_mulVec, one_mulVec]
    exact hg v hv
  rcases exists_add_eq_of_forall 𝔟 h𝔟 hM with ⟨P, Q, hP, hQ, hPQ⟩
  have hg₁ : P + Q + 1 = g.val := eq_sub_iff_add_eq.mp hPQ
  have hgl : g ∈ gl 𝔟 := hgsl.1
  have hdet' : g.val.det = 1 := by
    simpa using congrArg Units.val (MonoidHom.mem_ker.mp hgsl.2)
  have hQ₁ : ∀ v ∈ lattice 𝔟, (1 + Q) *ᵥ v ∈ lattice 𝔟 := fun v hv ↦ by
    rw [add_mulVec, one_mulVec]
    exact add_mem hv (Submodule.smul_le_right (hQ v hv))
  have e : 1 + Q = g.val * (1 + -((g⁻¹).val * P)) := by
    rw [mul_add, mul_one, mul_neg, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mul, ← hg₁]
    abel
  have hdetQ : (1 + Q).det - 1 ∈ ((𝔐 ⊓ 𝔑 : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [coeIdeal_inf, ← mem_coe, coe_inf, Submodule.mem_inf]
    refine ⟨?_, det_one_add_sub_one_mem 𝔟 h𝔟 hQ⟩
    rw [e, det_mul, hdet', one_mul]
    refine det_one_add_sub_one_mem 𝔟 h𝔟 fun v hv ↦ ?_
    rw [neg_mulVec, ← mulVec_mulVec]
    exact neg_mem (mulVec_mem_smul_lattice 𝔟 (inv_mem hgl) (hP v hv))
  have h𝔄 : 𝔐 ⊓ 𝔑 ≠ ⊥ := ne_bot_of_le_ne_bot (mul_ne_zero h𝔐 h𝔑) Ideal.mul_le_inf
  rcases exists_det_add_eq_one 𝔟 h𝔟 h𝔄 hQ₁ hdetQ with ⟨Y, hY, hdetY⟩
  let k : GL (Fin 2) F := GeneralLinearGroup.mkOfDetNeZero (1 + Q + Y) (hdetY ▸ one_ne_zero)
  have hk : k.val = 1 + (Q + Y) := add_assoc 1 Q Y
  have hk₁ : ∀ v ∈ lattice 𝔟, k.val *ᵥ v - v ∈ 𝔑 • lattice 𝔟 := fun v hv ↦ by
    rw [hk, add_mulVec, one_mulVec, add_sub_cancel_left, add_mulVec]
    exact add_mem (hQ v hv) (Submodule.smul_mono_left inf_le_right (hY v hv))
  have hkdet : k.val.det = 1 := hdetY
  have hkgl : k ∈ gl 𝔟 := mem_gl_of_forall 𝔟 h𝔟 (fun v hv ↦ by
    simpa using add_mem (Submodule.smul_le_right (hk₁ v hv)) hv) hkdet
  have hksl : k ∈ sl 𝔟 := ⟨hkgl, MonoidHom.mem_ker.mpr (Units.ext (by simpa using hkdet))⟩
  have hkN : k ∈ principalCongruenceSubgroup 𝔟 (sl 𝔟) 𝔑 := ⟨hksl, hkgl, hk₁⟩
  have hgk : g * k⁻¹ ∈ principalCongruenceSubgroup 𝔟 (sl 𝔟) 𝔐 := by
    refine Subgroup.mem_inf.mpr ⟨mul_mem hgsl (inv_mem hksl),
      mul_inv_mem_reductionKernel 𝔟 hgl hkgl fun v hv ↦ ?_⟩
    have e' : g.val - k.val = P - Y := by
      rw [hk, ← hg₁]
      abel
    rw [e', sub_mulVec]
    exact sub_mem (hP v hv) (Submodule.smul_mono_left inf_le_left (hY v hv))
  simpa using Subgroup.mul_mem_sup hgk hkN

/-- **Strong approximation for `SL(𝒪_F ⊕ 𝔟)`** (LMFDB `hmsurface.congruence_subgroup`): for ideals
`𝔐` and `𝔑` of `𝒪_F`, `Γ_𝔟(𝔐 + 𝔑) = Γ_𝔟(𝔐) ⊔ Γ_𝔟(𝔑)` in `SL(𝒪_F ⊕ 𝔟)`; in fact every element of
`Γ_𝔟(𝔐 + 𝔑)` is a product of an element of `Γ_𝔟(𝔐)` and one of `Γ_𝔟(𝔑)`. -/
lemma principalCongruenceSubgroup_sup (h𝔟 : 𝔟 ≠ 0) : principalCongruenceSubgroup 𝔟 (sl 𝔟) (𝔐 ⊔ 𝔑) =
    principalCongruenceSubgroup 𝔟 (sl 𝔟) 𝔐 ⊔ principalCongruenceSubgroup 𝔟 (sl 𝔟) 𝔑 :=
  (principalCongruenceSubgroup_sup_le 𝔟 h𝔟).antisymm (sup_le
    (principalCongruenceSubgroup_mono 𝔟 _ le_sup_left)
    (principalCongruenceSubgroup_mono 𝔟 _ le_sup_right))

/-- **A congruence subgroup of `SL(𝒪_F ⊕ 𝔟)` has a level** (LMFDB `hmsurface.congruence_subgroup`):
if `Γ` contains the principal congruence subgroup `Γ_𝔟(𝔑)` of `SL(𝒪_F ⊕ 𝔟)` for a nonzero ideal
`𝔑`, then `level 𝔟 (sl 𝔟) Γ` is its level: the nonzero ideals `𝔐` with `Γ_𝔟(𝔐) ≤ Γ` have a
maximal element by noetherianity, which is the largest as they are closed under sums. -/
lemma isLevel_level (Γ : Subgroup (GL (Fin 2) F)) (h𝔟 : 𝔟 ≠ 0) (h𝔑 : 𝔑 ≠ ⊥)
    (h : principalCongruenceSubgroup 𝔟 (sl 𝔟) 𝔑 ≤ Γ) : IsLevel 𝔟 (sl 𝔟) Γ (level 𝔟 (sl 𝔟) Γ) := by
  rcases set_has_maximal_iff_noetherian.mpr inferInstance
    {𝔐 | 𝔐 ≠ ⊥ ∧ principalCongruenceSubgroup 𝔟 (sl 𝔟) 𝔐 ≤ Γ} ⟨𝔑, h𝔑, h⟩ with ⟨𝔐, h𝔐, hmax⟩
  have hlevel : IsLevel 𝔟 (sl 𝔟) Γ 𝔐 := ⟨h𝔐.1, h𝔐.2, fun 𝔄 _ h𝔄 ↦ le_sup_right.trans
    (eq_of_le_of_not_lt le_sup_left (hmax _ ⟨ne_bot_of_le_ne_bot h𝔐.1 le_sup_left,
      (principalCongruenceSubgroup_sup_le 𝔟 h𝔟).trans (sup_le h𝔐.2 h𝔄)⟩)).ge⟩
  rwa [level_eq_of_isLevel 𝔟 (sl 𝔟) Γ hlevel]

end HilbertModularGroup
