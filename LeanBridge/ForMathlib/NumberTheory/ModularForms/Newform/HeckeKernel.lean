import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.NewformSubspace
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.RingTheory.Polynomial.Tower

/-!
# Hecke kernels of newforms

A newform `f = ∑ aₙ qⁿ` of nebentypus `χ` lies in the kernel of the operator `gₙ(Tₙ)` on the
newspace `S_k^{new}(N, χ)`, where `gₙ` is the minimal polynomial of `aₙ` and `Tₙ` is the `n`-th
Hecke operator (LMFDB `cmf.hecke_kernels`): `Tₙ f = aₙ f`. The newforms of nebentypus `χ` are a
basis of `S_k^{new}(N, χ)` of simultaneous eigenvectors of the `Tₙ`, so the intersection of the
kernels of the `gₙ(Tₙ)` for `n` in a nonempty set `X` is spanned by the newforms `h` whose
coefficients `aₙ(h)`, `n ∈ X`, are roots of the `gₙ`, i.e. are conjugate to the `aₙ(f)`.

The LMFDB states that for a set `X` of distinguishing primes (LMFDB `cmf.distinguishing_primes`)
the intersection of the kernels of the `g_p(T_p)`, `p ∈ X`, is the span of the Galois orbit of `f`
(the newform subspace `V_f`). As stated this can fail: distinguishing primes separate the Galois
orbits by the characteristic polynomials of the `T_p` on the `V_h`, whose degrees are the
dimensions of the orbits, while the Hecke kernels only see their minimal polynomials, so an orbit
of another dimension whose `a_p`, `p ∈ X`, are conjugate to those of `f` also lies in the
intersection. The characterisation holds when the minimal polynomials of the `a_p`, `p ∈ X`,
separate the orbit of `f` from the other newforms of nebentypus `χ`
(`HeckeRing.GL2.Newform.map_iInf_heckeKernel_eq_newformSubspace_inf`). In `S_k^{new}(N, χ)` for a
fixed `χ` the span of the orbit is its `χ`-part `V_f ∩ S_k(N, χ)`, spanned by the Galois
conjugates of `f` of nebentypus `χ`.

## Main definitions

* `HeckeRing.GL2.Newform.coeffMinpoly`: the minimal polynomial `gₙ` of `aₙ` over `ℚ`.
* `HeckeRing.GL2.Newform.heckeKernel` (LMFDB `cmf.hecke_kernels`): the kernel of `gₙ(Tₙ)` on
  `S_k^{new}(N, χ)`.
* `HeckeRing.GL2.Newform.toCuspFormCharSpace`: a newform of nebentypus `χ`, as an element of
  `S_k(N, χ)`.

## Main results

* `HeckeRing.GL2.Newform.mem_heckeKernel`: a newform lies in its Hecke kernels.
* `HeckeRing.GL2.Newform.map_iInf_heckeKernel`: the intersection of the Hecke kernels of `f` over
  a nonempty set `X` is spanned by the newforms `h` of nebentypus `χ` such that every `aₙ(h)`,
  `n ∈ X`, is a root of `gₙ`.
* `HeckeRing.GL2.Newform.newformSubspace_inf_le_map_heckeKernel`: the Galois conjugates of `f`
  of nebentypus `χ` lie in its Hecke kernels.
* `HeckeRing.GL2.Newform.map_iInf_heckeKernel_eq_newformSubspace_inf`: if the minimal polynomials
  of the `a_p(f)`, `p ∈ X`, separate the Galois orbit of `f`, the intersection of the Hecke kernels
  is `V_f ∩ S_k(N, χ)`.
-/

open UpperHalfPlane TauCeti CongruenceSubgroup Polynomial Module

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} {f h : Newform N k} (n : ℕ+) {X : Set ℕ+} {χ : (ZMod N)ˣ →* ℂˣ}
    (hχ : h.χ = χ)

variable (f) in
/-- The minimal polynomial `gₙ ∈ ℚ[X]` of the coefficient `aₙ` of a newform `f = ∑ aₙ qⁿ`. -/
noncomputable def coeffMinpoly : ℚ[X] :=
  minpoly ℚ ((qExpansion 1 f.toCuspForm).coeff n)

variable (f) in
/-- The **Hecke kernel** (LMFDB `cmf.hecke_kernels`) of a newform `f = ∑ aₙ qⁿ` of nebentypus `χ`
at `n ≥ 1`: the kernel of the operator `gₙ(Tₙ)` on the newspace `S_k^{new}(N, χ)`, where `gₙ` is
the minimal polynomial of `aₙ` over `ℚ` and `Tₙ` is the `n`-th Hecke operator, the action of Tau
Ceti's `heckeTCompositeGamma0 N n` on `S_k(N, χ)`. It is taken as the subspace of the kernel of
`gₙ(Tₙ)` on `S_k(N, χ)` of the forms in the new subspace, which is the kernel on
`S_k^{new}(N, χ)` since `Tₙ` preserves the new subspace. The LMFDB takes the primitive
`gₙ ∈ ℤ[X]`, a rational multiple of the minimal polynomial over `ℚ`, which has the same
kernel. -/
noncomputable def heckeKernel : Submodule ℂ (cuspFormCharSpace k f.χ) :=
  LinearMap.ker (aeval (heckeRingHomCuspCharSpace k f.χ (heckeTCompositeGamma0 N n))
    ((f.coeffMinpoly n).map (algebraMap ℚ ℂ))) ⊓
      (cuspFormsNew N k).comap (cuspFormCharSpace k f.χ).subtype

variable (h) in
/-- A newform `h` of nebentypus `χ`, as an element of `S_k(N, χ)`. -/
def toCuspFormCharSpace : cuspFormCharSpace k χ :=
  ⟨h.toCuspForm, hχ ▸ h.mem_charSpace⟩

lemma toCuspFormCharSpace_ne_zero : h.toCuspFormCharSpace hχ ≠ 0 :=
  fun h0 ↦ h.ne_zero <| congrArg Subtype.val h0

lemma heckeRingHomCuspCharSpace_toCuspFormCharSpace :
    heckeRingHomCuspCharSpace k χ (heckeTCompositeGamma0 N n) (h.toCuspFormCharSpace hχ) =
      (qExpansion 1 h.toCuspForm).coeff n • h.toCuspFormCharSpace hχ := by
  subst hχ
  rw [← h.toEigenform_eigenvalue_eq_qExpansion_coeff n]
  exact h.toEigenform.isEigen n

private lemma linearIndependent_toCuspFormCharSpace :
    LinearIndependent ℂ fun h : {h : Newform N k // h.χ = χ} ↦ h.1.toCuspFormCharSpace h.2 :=
  LinearIndependent.of_comp (cuspFormCharSpace k χ).subtype <|
    linearIndependent_toCuspForm.comp Subtype.val Subtype.val_injective

private lemma mem_span_of_forall_aeval_eq_zero {ι M : Type*} [AddCommGroup M] [Module ℂ M]
    {v : ι → M} (hv : LinearIndependent ℂ v) (T : ℕ+ → End ℂ M) (μ : ℕ+ → ι → ℂ)
    (hT : ∀ n i, T n (v i) = μ n i • v i) (g : ℕ+ → ℂ[X]) {w : M}
    (hw : w ∈ Submodule.span ℂ (Set.range v)) (hg : ∀ n ∈ X, aeval (T n) (g n) w = 0) :
    w ∈ Submodule.span ℂ (v '' {i | ∀ n ∈ X, (g n).eval (μ n i) = 0}) := by
  rw [← Set.image_univ] at hw
  rcases (Finsupp.mem_span_image_iff_linearCombination ℂ).mp hw with ⟨l, -, rfl⟩
  refine (Finsupp.mem_span_image_iff_linearCombination ℂ).mpr ⟨l, fun i hi n hn ↦ ?_, rfl⟩
  have hg' : ∑ j ∈ l.support, (l j * (g n).eval (μ n j)) • v j = 0 := by
    rw [← hg n hn, Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, End.aeval_apply_of_hasEigenvector ⟨End.mem_eigenspace_iff.mpr (hT n j),
      hv.ne_zero j⟩, smul_smul]
  exact (mul_eq_zero.mp (linearIndependent_iff'.mp hv _ _ hg' i hi)).resolve_left <|
    Finsupp.mem_support_iff.mp hi

lemma mem_heckeKernel_iff (hχf : h.χ = f.χ) : h.toCuspFormCharSpace hχf ∈ f.heckeKernel n ↔
    aeval ((qExpansion 1 h.toCuspForm).coeff n) (f.coeffMinpoly n) = 0 := by
  rw [heckeKernel, Submodule.mem_inf, LinearMap.mem_ker, End.aeval_apply_of_hasEigenvector
    ⟨End.mem_eigenspace_iff.mpr (heckeRingHomCuspCharSpace_toCuspFormCharSpace n hχf),
      toCuspFormCharSpace_ne_zero hχf⟩, smul_eq_zero, or_iff_left (toCuspFormCharSpace_ne_zero hχf),
    eval_map_algebraMap, Submodule.mem_comap]
  exact and_iff_left h.isNew

variable (f) in
/-- **A newform lies in its Hecke kernels**: `gₙ(Tₙ) f = gₙ(aₙ) f = 0` for every `n ≥ 1`, as
`Tₙ f = aₙ f`. -/
lemma mem_heckeKernel : f.toCuspFormCharSpace rfl ∈ f.heckeKernel n :=
  (mem_heckeKernel_iff n rfl).mpr <| minpoly.aeval ℚ _

lemma IsGaloisConjugateBy.aeval_coeffMinpoly {σ : Gal(ℂ/ℚ)} (hσ : f.IsGaloisConjugateBy σ h) :
    aeval ((qExpansion 1 h.toCuspForm).coeff n) (f.coeffMinpoly n) = 0 := by
  rw [hσ.coeff, aeval_algHom_apply, coeffMinpoly, minpoly.aeval, map_zero]

/-- **The intersection of the Hecke kernels** of `f` over a nonempty set `X` of indices is spanned
by the newforms `h` of nebentypus `χ = f.χ` such that `aₙ(h)` is a root of the minimal polynomial
`gₙ` of `aₙ(f)` for every `n ∈ X`: these newforms are a basis of `S_k^{new}(N, χ)` on which each
`gₙ(Tₙ)` acts by the scalar `gₙ(aₙ(h))`. -/
lemma map_iInf_heckeKernel (hX : X.Nonempty) :
    (⨅ n ∈ X, f.heckeKernel n).map (cuspFormCharSpace k f.χ).subtype = Submodule.span ℂ
      ((fun h : Newform N k ↦ h.toCuspForm) '' {h | h.χ = f.χ ∧
        ∀ n ∈ X, aeval ((qExpansion 1 h.toCuspForm).coeff n) (f.coeffMinpoly n) = 0}) := by
  refine le_antisymm (fun x hx ↦ ?_) <| Submodule.span_le.mpr ?_
  · rcases Submodule.mem_map.mp hx with ⟨w, hw, rfl⟩
    simp only [Submodule.mem_iInf] at hw
    rcases hX with ⟨n₀, hn₀⟩
    have hspan : w ∈ Submodule.span ℂ
        (Set.range fun h : {h : Newform N k // h.χ = f.χ} ↦ h.1.toCuspFormCharSpace h.2) := by
      have hw₀ : (cuspFormCharSpace k f.χ).subtype w ∈ cuspFormsNew N k ⊓ cuspFormCharSpace k f.χ :=
        ⟨(hw n₀ hn₀).2, w.2⟩
      have hset : (fun h : Newform N k ↦ h.toCuspForm) '' {h | h.χ = f.χ} =
          (cuspFormCharSpace k f.χ).subtype '' Set.range fun h : {h : Newform N k // h.χ = f.χ} ↦
            h.1.toCuspFormCharSpace h.2 := by
        ext x
        constructor
        · rintro ⟨h, hχ, rfl⟩
          exact ⟨_, ⟨⟨h, hχ⟩, rfl⟩, rfl⟩
        · rintro ⟨_, ⟨⟨h, hχ⟩, rfl⟩, rfl⟩
          exact ⟨h, hχ, rfl⟩
      rw [← span_image_toCuspForm_eq_cuspFormsNew_inf_cuspFormCharSpace, hset,
        ← Submodule.map_span] at hw₀
      rcases Submodule.mem_map.mp hw₀ with ⟨w', hw', hww'⟩
      rwa [← (cuspFormCharSpace k f.χ).injective_subtype hww']
    convert Submodule.mem_map_of_mem (f := (cuspFormCharSpace k f.χ).subtype) <|
      mem_span_of_forall_aeval_eq_zero linearIndependent_toCuspFormCharSpace
        (fun n ↦ heckeRingHomCuspCharSpace k f.χ (heckeTCompositeGamma0 N n))
        (fun n h ↦ (qExpansion 1 h.1.toCuspForm).coeff n)
        (fun n h ↦ heckeRingHomCuspCharSpace_toCuspFormCharSpace n h.2)
        (fun n ↦ (f.coeffMinpoly n).map (algebraMap ℚ ℂ)) hspan
        fun n hn ↦ LinearMap.mem_ker.mp (hw n hn).1 using 1
    rw [Submodule.map_span, ← Set.image_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨h, ⟨hχ, hh⟩, rfl⟩
      exact ⟨⟨h, hχ⟩, fun n hn ↦ by rw [eval_map_algebraMap]; exact hh n hn, rfl⟩
    · rintro ⟨⟨h, hχ⟩, hh, rfl⟩
      exact ⟨h, ⟨hχ, fun n hn ↦ by rw [← eval_map_algebraMap]; exact hh n hn⟩, rfl⟩
  · rintro _ ⟨h, ⟨hχ, hh⟩, rfl⟩
    refine ⟨h.toCuspFormCharSpace hχ, ?_, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_iInf]
    exact fun n hn ↦ (mem_heckeKernel_iff n hχ).mpr (hh n hn)

/-- **The Galois conjugates of `f` of nebentypus `χ` lie in its Hecke kernels**: if `g = σ(f)`,
then `aₙ(g) = σ(aₙ(f))` is a root of the minimal polynomial of `aₙ(f)`. So the `χ`-part
`V_f ∩ S_k(N, χ)` of the newform subspace of `f` lies in each Hecke kernel of `f`. -/
lemma newformSubspace_inf_le_map_heckeKernel : f.newformSubspace ⊓ cuspFormCharSpace k f.χ ≤
    (f.heckeKernel n).map (cuspFormCharSpace k f.χ).subtype := by
  rw [newformSubspace, span_image_toCuspForm_inf_cuspFormCharSpace]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g, ⟨⟨σ, hσ⟩, hχ⟩, rfl⟩
  exact ⟨g.toCuspFormCharSpace hχ, (mem_heckeKernel_iff n hχ).mpr (hσ.aeval_coeffMinpoly n), rfl⟩

/-- **The Hecke kernels cut out the Galois orbit** (LMFDB `cmf.hecke_kernels`), in weight at least
two: if the minimal polynomials of the `aₙ(f)`, `n ∈ X`, separate `f` from the newforms of
nebentypus `χ` that are not Galois conjugate to it, the intersection of the Hecke kernels of `f`
over `X` is the `χ`-part `V_f ∩ S_k(N, χ)` of its newform subspace, spanned by the Galois
conjugates of `f` of nebentypus `χ`. The LMFDB asks for a set of distinguishing primes instead,
which separates the orbits by the characteristic polynomials of the `T_p` on the `V_h`; this is
not enough when another orbit has a different dimension but the same minimal polynomials. -/
lemma map_iInf_heckeKernel_eq_newformSubspace_inf (hk : 2 ≤ k) (hX : X.Nonempty)
    (hsep : ∀ h : Newform N k, h.χ = f.χ → (∀ n ∈ X, h.coeffMinpoly n = f.coeffMinpoly n) →
      f.IsGaloisConjugate h) : (⨅ n ∈ X, f.heckeKernel n).map (cuspFormCharSpace k f.χ).subtype =
    f.newformSubspace ⊓ cuspFormCharSpace k f.χ := by
  have hint (n : ℕ) : IsIntegral ℚ ((qExpansion 1 f.toCuspForm).coeff n) :=
    (f.isIntegral_qExpansion_coeff hk n).tower_top
  rw [map_iInf_heckeKernel hX, newformSubspace, span_image_toCuspForm_inf_cuspFormCharSpace]
  congr 2
  ext h
  refine ⟨fun ⟨hχ, hh⟩ ↦ ⟨hsep h hχ fun n hn ↦ (minpoly.eq_of_irreducible_of_monic
    (minpoly.irreducible (hint n)) (hh n hn) (minpoly.monic (hint n))).symm, hχ⟩, ?_⟩
  rintro ⟨⟨σ, hσ⟩, hχ⟩
  exact ⟨hχ, fun n _ ↦ hσ.aeval_coeffMinpoly n⟩

end HeckeRing.GL2.Newform
