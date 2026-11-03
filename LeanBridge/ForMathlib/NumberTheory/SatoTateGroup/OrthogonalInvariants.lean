import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.AmbientDensity
import Mathlib.MeasureTheory.Integral.Pi
import TauCeti.Analysis.InnerProductSpace.SingularValues
import TauCeti.Combinatorics.Enumerative.PerfectMatching
import TauCeti.LinearAlgebra.Multilinear.Polarization

/-!
# The first fundamental theorem of invariant theory for `O(d)`

A tensor invariant under the compact orthogonal group `O(d)` is a combination of the tensors of the
perfect matchings of its slots, the products of copies of the invariant form. This is the first
fundamental theorem of invariant theory (Weyl, *The Classical Groups*, Chapter II; Goodman and
Wallach, *Symmetry, Representations, and Invariants*, Chapter 5). The classical proofs go through
Capelli's identity or the commutant of `GL(d)`. The proof here uses only the Haar measure.

Let `X` be the random real `d × d` matrix whose column `s` is the column `s` of `g_s`, for
independent Haar random elements `g_s` of `O(d)`. It is not itself orthogonal, since its columns are
independent. Polarization and the transitivity of `O(d)` on the spheres show that the moments of one
column are a combination of the tensors of perfect matchings, and by independence so are the moments
of `X`, the entries of the expectation of `X^{⊗P}`, as tensors in their first index. So if an
invariant tensor `f` is orthogonal to the tensors of perfect matchings, then the expectation of
`⟨f, X^{⊗P} f⟩` vanishes. But the singular value decomposition `A = B D C` of a real matrix and the
invariance of `f` give `⟨f, A^{⊗P} f⟩ = ⟨f, D^{⊗P} f⟩`, with a nonnegative real part since `D` is
diagonal with nonnegative entries. It is `‖f‖²` at `A = 1`, the value of `X` at `g_s = 1`, so it has
a positive expectation unless `f = 0`.

Tau Ceti's main has short statements parallel to two helpers here, which can be replaced at the next
bump: `Matrix.exists_unitary_mul_diagonal_mul_unitary` is the singular value decomposition of a
matrix (here read off the operator decomposition at the pin), and
`TauCeti.BrauerDiagram.sum_isConstantOnArcs_prod_apply` is the invariance of the tensor of a Brauer
diagram (`SatoTateGroup.tensorRep_mulVec_matchingTensor`). The first fundamental theorem is not on
Tau Ceti's main.

## Main definitions

* `SatoTateGroup.matchingTensor`: the tensor of a perfect matching of the slots.
* `SatoTateGroup.columnMoment`: the moments of a column of a Haar random element of `O(d)`.
* `SatoTateGroup.randomMoment`: the moments of a matrix with independent such columns.

## Main results

* `SatoTateGroup.tensorRep_mulVec_matchingTensor`: the tensor of a perfect matching is invariant.
* `SatoTateGroup.eq_zero_of_forall_sum_mul_prod`: polarization.
* `SatoTateGroup.columnMoment_mem_span`: the moments of a column are a combination of the tensors of
  perfect matchings.
* `SatoTateGroup.mem_span_matchingTensor_of_forall_mulVec_eq`: the first fundamental theorem.
-/

open Equiv Filter Matrix MeasureTheory Module TauCeti TopologicalSpace

open scoped ComplexOrder

universe u

namespace SatoTateGroup

section Matching

variable {P : Type u} {I : Type*} [Fintype P] [DecidableEq I] {Q : Type*} [Fintype Q]

/-- The **tensor of a perfect matching** `π` of the slots `P`, in coordinates: the product over the
pairs `{p, π p}` of the Kronecker deltas `δ_{a p, a (π p)}`. These are the products of copies of the
invariant form of `O(d)`. -/
def matchingTensor (π : PerfectMatching P) (a : P → I) : ℂ :=
  if a ∘ π.val = a then 1 else 0

lemma exists_sumEquiv_perfectMatching (π : PerfectMatching P) : ∃ (Q : Type u) (_ : Fintype Q)
    (_ : DecidableEq Q) (e : Q ⊕ Q ≃ P), ∀ q, π.val (e (.inl q)) = e (.inr q) := by
  let f : P ≃ Fin (Fintype.card P) := Fintype.equivFin P
  let Q : Type u := {p : P // f p < f (π.val p)}
  let φ : Q ⊕ Q → P := Sum.elim (fun q ↦ q.1) fun q ↦ π.val q.1
  have hne (p : P) : f p ≠ f (π.val p) := fun h ↦ π.apply_ne p (f.injective h).symm
  have hφ : Function.Bijective φ := by
    constructor
    · rintro (x | x) (y | y) h
      · exact congrArg Sum.inl (Subtype.ext h)
      · have h₁ : x.1 = π.val y.1 := h
        have h₂ : f x.1 < f (π.val x.1) := x.2
        have h₃ : f y.1 < f (π.val y.1) := y.2
        rw [h₁, π.apply_apply] at h₂
        exact absurd (h₂.trans h₃) (lt_irrefl _)
      · have h₁ : π.val x.1 = y.1 := h
        have h₂ : f x.1 < f (π.val x.1) := x.2
        have h₃ : f y.1 < f (π.val y.1) := y.2
        rw [← h₁, π.apply_apply] at h₃
        exact absurd (h₂.trans h₃) (lt_irrefl _)
      · exact congrArg Sum.inr (Subtype.ext (π.val.injective h))
    · intro p
      rcases lt_or_gt_of_ne (hne p) with h | h
      · exact ⟨.inl ⟨p, h⟩, rfl⟩
      · have h₁ : f (π.val p) < f (π.val (π.val p)) := by
          rwa [π.apply_apply]
        exact ⟨.inr ⟨π.val p, h₁⟩, π.apply_apply p⟩
  exact ⟨Q, inferInstance, Classical.decEq _, ofBijective φ hφ, fun q ↦ rfl⟩

lemma matchingTensor_eq_prod {π : PerfectMatching P} {e : Q ⊕ Q ≃ P}
    (he : ∀ q, π.val (e (.inl q)) = e (.inr q)) (a : P → I) :
    matchingTensor π a = ∏ q, if a (e (.inl q)) = a (e (.inr q)) then 1 else 0 := by
  rw [Fintype.prod_ite_zero, Finset.prod_const_one]
  refine if_congr ⟨fun h q ↦ ?_, fun h ↦ funext fun p ↦ ?_⟩ rfl rfl
  · have h₁ : a (π.val (e (.inl q))) = a (e (.inl q)) := congrFun h _
    rw [he] at h₁
    exact h₁.symm
  · rcases e.surjective p with ⟨x | x, rfl⟩
    · rw [Function.comp_apply, he]
      exact (h x).symm
    · rw [Function.comp_apply, ← he, π.apply_apply, he]
      exact h x

lemma matchingTensor_comp (π : PerfectMatching P) (σ : Perm P) (a : P → I) :
    matchingTensor π (a ∘ σ) = matchingTensor (PerfectMatching.congr σ π) a := by
  refine if_congr ⟨fun h ↦ funext fun p ↦ ?_, fun h ↦ funext fun p ↦ ?_⟩ rfl rfl
  · have h₁ : a (σ (π.val (σ.symm p))) = a (σ (σ.symm p)) := congrFun h (σ.symm p)
    rwa [apply_symm_apply] at h₁
  · have h₁ : a (σ (π.val (σ.symm (σ p)))) = a (σ p) := congrFun h (σ p)
    rwa [symm_apply_apply] at h₁

variable [DecidableEq P]

lemma sum_matchingTensor_comp (σ : Perm P) (a : P → I) :
    ∑ π : PerfectMatching P, matchingTensor π (a ∘ σ) = ∑ π, matchingTensor π a := by
  simp only [matchingTensor_comp]
  exact (PerfectMatching.congr σ).sum_comp fun π ↦ matchingTensor π a

variable [Fintype I] [DecidableEq Q]

lemma sum_matchingTensor_mul_prod {π : PerfectMatching P} {e : Q ⊕ Q ≃ P}
    (he : ∀ q, π.val (e (.inl q)) = e (.inr q)) (f : P → I → ℂ) : ∑ b : P → I, matchingTensor π b *
      ∏ p, f p (b p) = ∏ q, ∑ c, f (e (.inl q)) c * f (e (.inr q)) c := by
  let E : (Q → I) × (Q → I) ≃ (P → I) :=
    (sumArrowEquivProdArrow Q Q I).symm.trans (arrowCongr e (Equiv.refl I))
  have hE (x : (Q → I) × (Q → I)) (r : Q ⊕ Q) : E x (e r) = Sum.elim x.1 x.2 r := by
    simp only [E, trans_apply, arrowCongr, coe_fn_mk, Function.comp_apply, symm_apply_apply]
    rcases r with r | r <;> rfl
  have hE₁ (x : (Q → I) × (Q → I)) (q : Q) : E x (e (.inl q)) = x.1 q := hE x (.inl q)
  have hE₂ (x : (Q → I) × (Q → I)) (q : Q) : E x (e (.inr q)) = x.2 q := hE x (.inr q)
  have h₁ (x : (Q → I) × (Q → I)) : matchingTensor π (E x) * ∏ p, f p (E x p) =
      if x.1 = x.2 then ∏ q, (f (e (.inl q)) (x.1 q) * f (e (.inr q)) (x.2 q)) else 0 := by
    have h₂ : ∏ p, f p (E x p) = ∏ q, (f (e (.inl q)) (x.1 q) * f (e (.inr q)) (x.2 q)) := by
      rw [← e.prod_comp, Fintype.prod_sum_type, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun q _ ↦ by rw [hE₁, hE₂]
    rw [h₂, matchingTensor_eq_prod he, Fintype.prod_ite_zero, Finset.prod_const_one]
    by_cases h : x.1 = x.2
    · rw [ite_eq_left fun q ↦ by rw [hE₁, hE₂, h], ite_eq_left h, one_mul]
    · have h₃ : ¬∀ q, E x (e (.inl q)) = E x (e (.inr q)) := fun h₄ ↦
        h (funext fun q ↦ by rw [← hE₁, ← hE₂, h₄ q])
      rw [ite_eq_right h₃, ite_eq_right h, zero_mul]
  rw [← E.sum_comp, Finset.sum_congr rfl fun x _ ↦ h₁ x, Fintype.sum_prod_type]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.prod_univ_sum,
    Fintype.piFinset_univ]

/-- **The tensor of a perfect matching is invariant under `O(d)`.** -/
lemma tensorRep_mulVec_matchingTensor {g : Matrix I I ℂ} (hg : g * gᵀ = 1) (π : PerfectMatching P) :
    tensorRep g *ᵥ matchingTensor π = matchingTensor (I := I) π := by
  rcases exists_sumEquiv_perfectMatching π with ⟨Q, _, _, e, he⟩
  funext a
  have h₁ (x y : I) : ∑ c, g x c * g y c = if x = y then 1 else 0 := by
    have h₂ : (g * gᵀ) x y = ∑ c, g x c * g y c := Matrix.mul_apply
    rw [← h₂, hg, one_apply]
  have h₂ :
      (tensorRep g *ᵥ matchingTensor π) a = ∑ b : P → I, matchingTensor π b * ∏ p, g (a p) (b p) :=
    Finset.sum_congr rfl fun b _ ↦ mul_comm _ _
  rw [h₂, sum_matchingTensor_mul_prod he, matchingTensor_eq_prod he]
  exact Finset.prod_congr rfl fun q _ ↦ h₁ _ _

lemma sum_matchingTensor_mul_prod_real (π : PerfectMatching P) (y : I → ℝ) {k : ℕ}
    (hk : Fintype.card P = 2 * k) :
    ∑ a, matchingTensor π a * ∏ p, (y (a p) : ℂ) = ((y ⬝ᵥ y : ℝ) : ℂ) ^ k := by
  rcases exists_sumEquiv_perfectMatching π with ⟨Q, _, _, e, he⟩
  have h₁ : Fintype.card Q = k := by
    have h₂ : Fintype.card (Q ⊕ Q) = Fintype.card P := Fintype.card_congr e
    rw [Fintype.card_sum] at h₂
    omega
  rw [sum_matchingTensor_mul_prod he fun _ c ↦ (y c : ℂ), ← h₁, ← Finset.card_univ,
    ← Finset.prod_const]
  refine Finset.prod_congr rfl fun q _ ↦ ?_
  simp [dotProduct]

end Matching

section Polarization

variable {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I]

/-- **Polarization.** A symmetric tensor whose polynomial vanishes on real vectors is zero. -/
lemma eq_zero_of_forall_sum_mul_prod {F : (S → I) → ℂ} (hF : ∀ (σ : Perm S) a, F (a ∘ σ) = F a)
    (h : ∀ y : I → ℝ, ∑ a, F a * ∏ p, (y (a p) : ℂ) = 0) : F = 0 := by
  funext a₀
  let f : MultilinearMap ℂ (fun _ : S ↦ I → ℂ) ℂ :=
    ∑ a, F a • (MultilinearMap.mkPiAlgebra ℂ S ℂ).compLinearMap fun p ↦ LinearMap.proj (a p)
  have hf (m : S → I → ℂ) : f m = ∑ a, F a * ∏ p, m p (a p) := by
    simp [f]
  have h₁ : ∑ T : Finset S, (-1 : ℂ) ^ T.card • f (fun _ ↦ ∑ i ∈ Tᶜ, Pi.single (a₀ i) 1) =
      ∑ σ : Perm S, f fun i ↦ Pi.single (a₀ (σ i)) 1 :=
    f.sum_neg_one_pow_card_smul_apply_sum_compl fun p ↦ Pi.single (a₀ p) 1
  have h₂ (T : Finset S) : f (fun _ ↦ ∑ i ∈ T, Pi.single (a₀ i) 1) = 0 := by
    rw [hf, ← h fun l ↦ ∑ i ∈ T, (Pi.single (a₀ i) 1 : I → ℝ) l]
    refine Finset.sum_congr rfl fun a _ ↦ congrArg _ (Finset.prod_congr rfl fun p _ ↦ ?_)
    simp [Pi.single_apply]
  have h₃ (σ : Perm S) : f (fun i ↦ Pi.single (a₀ (σ i)) 1) = F a₀ := by
    rw [hf, Finset.sum_eq_single (a₀ ∘ σ), hF]
    · simp
    · intro a _ ha
      rcases Function.ne_iff.mp ha with ⟨p, hp⟩
      rw [Finset.prod_eq_zero (Finset.mem_univ p), mul_zero]
      exact Pi.single_eq_of_ne hp _
    · simp
  simp only [h₂, h₃, smul_zero, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
    nsmul_eq_mul] at h₁
  exact (mul_eq_zero.mp h₁.symm).resolve_left (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

end Polarization

section Moment

variable {w d : ℕ}

lemma exists_orthogonal_column (i₀ : Fin d) {u : Fin d → ℝ} (hu : u ⬝ᵥ u = 1) :
    ∃ R : Matrix (Fin d) (Fin d) ℝ, Rᵀ * R = 1 ∧ ∀ i, R i i₀ = u i := by
  let e : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) := EuclideanSpace.basisFun (Fin d) ℝ
  have hv : Orthonormal ℝ (({i₀} : Set (Fin d)).domRestrict fun _ ↦
      (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d))) := by
    rw [orthonormal_iff_ite]
    rintro ⟨i, rfl⟩ ⟨j, rfl⟩
    rw [ite_eq_left rfl]
    exact (EuclideanSpace.inner_eq_star_dotProduct _ _).trans hu
  rcases hv.exists_orthonormalBasis_extension_of_card_eq (by simp) with ⟨b, hb⟩
  refine ⟨e.toBasis.toMatrix b, e.toMatrix_orthonormalBasis_conjTranspose_mul_self b, fun i ↦ ?_⟩
  rw [Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply, hb i₀ rfl]
  rfl

lemma transpose_mul_self_ambient (hw : Even w) (g : ambientGroup w d) :
    (g : Matrix (Fin d) (Fin d) ℂ)ᵀ * g = 1 := by
  have h : (g : Matrix (Fin d) (Fin d) ℂ)ᵀ * ambientForm w d * g = ambientForm w d := g.2
  rwa [ambientForm_of_even hw, Matrix.mul_one] at h

lemma mul_transpose_self_ambient (hw : Even w) (g : ambientGroup w d) :
    (g : Matrix (Fin d) (Fin d) ℂ) * (g : Matrix (Fin d) (Fin d) ℂ)ᵀ = 1 :=
  mul_eq_one_comm.mp (transpose_mul_self_ambient hw g)

lemma coe_inv_ambient (hw : Even w) (g : ambientGroup w d) :
    ((g⁻¹ : ambientGroup w d) : Matrix (Fin d) (Fin d) ℂ) = (g : Matrix (Fin d) (Fin d) ℂ)ᵀ := by
  have h₂ : ((g⁻¹ : ambientGroup w d) : Matrix (Fin d) (Fin d) ℂ) * g = 1 := by
    have h₁ : ((g⁻¹ * g : ambientGroup w d) : Matrix (Fin d) (Fin d) ℂ) = 1 := by simp
    exact h₁
  rw [← Matrix.mul_one ((g⁻¹ : ambientGroup w d) : Matrix (Fin d) (Fin d) ℂ),
    ← mul_transpose_self_ambient hw g, ← Matrix.mul_assoc, h₂, Matrix.one_mul]

lemma exists_ambient_coe_eq (hw : Even w) {R : Matrix (Fin d) (Fin d) ℝ} (hR : Rᵀ * R = 1) :
    ∃ g : ambientGroup w d, (g : Matrix (Fin d) (Fin d) ℂ) = R.map Complex.ofReal := by
  have h₁ : (R.map Complex.ofReal)ᵀ * R.map Complex.ofReal = 1 := by
    rw [← transpose_map]
    refine (Matrix.map_mul (f := Complex.ofRealHom)).symm.trans ?_
    rw [hR]
    simp
  have h₂ : star (R.map Complex.ofReal) = (R.map Complex.ofReal)ᵀ := by
    ext i j
    simp
  have hu : R.map Complex.ofReal ∈ unitaryGroup (Fin d) ℂ := by
    rw [mem_unitaryGroup_iff', h₂]
    exact h₁
  refine ⟨⟨⟨R.map Complex.ofReal, hu⟩, ?_⟩, rfl⟩
  rw [mem_ambientGroup, ambientForm_of_even hw, Matrix.mul_one]
  exact h₁

lemma exists_ambient_column (hw : Even w) (i₀ : Fin d) {u : Fin d → ℝ} (hu : u ⬝ᵥ u = 1) :
    ∃ r : ambientGroup w d, ∀ i, (r : Matrix (Fin d) (Fin d) ℂ) i i₀ = u i := by
  rcases exists_orthogonal_column i₀ hu with ⟨R, hR, hc⟩
  rcases exists_ambient_coe_eq hw hR with ⟨r, hr⟩
  exact ⟨r, fun i ↦ by rw [hr, map_apply, hc]⟩

variable {S : Type*} [Fintype S]

variable (w) in
/-- The moments of the entries of a fixed column of `O(d)`, for its Haar probability measure, as a
tensor with slots `S`. -/
noncomputable def columnMoment (i₀ : Fin d) (a : S → Fin d) : ℂ :=
  ∫ h : ambientGroup w d, ∏ p, (h : Matrix (Fin d) (Fin d) ℂ) (a p) i₀ ∂haarProb (ambientGroup w d)

variable [DecidableEq S]

lemma sum_columnMoment_mul_prod (hw : Even w) (i₀ : Fin d) (y : Fin d → ℝ) {k : ℕ}
    (hk : Fintype.card S = 2 * k) : ∑ a : S → Fin d, columnMoment w i₀ a * ∏ p, (y (a p) : ℂ) =
      (∫ h : ambientGroup w d, (h : Matrix (Fin d) (Fin d) ℂ) i₀ i₀ ^ (2 * k)
        ∂haarProb (ambientGroup w d)) * ((y ⬝ᵥ y : ℝ) : ℂ) ^ k := by
  have h₁ : ∑ a : S → Fin d, columnMoment w i₀ a * ∏ p, (y (a p) : ℂ) =
      ∫ h : ambientGroup w d, (∑ i, (h : Matrix (Fin d) (Fin d) ℂ) i i₀ * (y i : ℂ)) ^ (2 * k)
        ∂haarProb (ambientGroup w d) := by
    have hint (a : S → Fin d) : Integrable (fun h : ambientGroup w d ↦
        (∏ p, (h : Matrix (Fin d) (Fin d) ℂ) (a p) i₀) * ∏ p, (y (a p) : ℂ))
          (haarProb (ambientGroup w d)) :=
      ((continuous_ambient_tensorRep_apply a fun _ ↦ i₀).mul
        continuous_const).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    simp only [columnMoment, ← integral_mul_const]
    rw [← integral_finsetSum _ fun a _ ↦ hint a]
    refine integral_congr_ae (Eventually.of_forall fun h ↦ ?_)
    simp only [← Finset.prod_mul_distrib]
    rw [← hk, ← Finset.card_univ, ← Finset.prod_const, Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [h₁]
  by_cases hy : y ⬝ᵥ y = 0
  · have hy₀ : y = 0 := dotProduct_self_eq_zero.mp hy
    subst hy₀
    rcases k with _ | k
    · simp
    · simp
  · have hs : 0 < y ⬝ᵥ y :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg _) (Ne.symm hy)
    let s : ℝ := Real.sqrt (y ⬝ᵥ y)
    have hs₁ : s * s = y ⬝ᵥ y := Real.mul_self_sqrt hs.le
    have hs₂ : s ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
    have hu : (s⁻¹ • y) ⬝ᵥ (s⁻¹ • y) = 1 := by
      rw [smul_dotProduct, dotProduct_smul, smul_smul, smul_eq_mul, ← hs₁]
      field_simp
    rcases exists_ambient_column hw i₀ hu with ⟨r, hr⟩
    have h₂ (h : ambientGroup w d) : ∑ i, (h : Matrix (Fin d) (Fin d) ℂ) i i₀ * (y i : ℂ) =
        s * ((r⁻¹ * h : ambientGroup w d) : Matrix (Fin d) (Fin d) ℂ) i₀ i₀ := by
      have h₃ : ((r⁻¹ * h : ambientGroup w d) : Matrix (Fin d) (Fin d) ℂ) =
          ((r⁻¹ : ambientGroup w d) : Matrix (Fin d) (Fin d) ℂ) * h := rfl
      rw [h₃, coe_inv_ambient hw, Matrix.mul_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [transpose_apply, hr]
      simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv]
      have h₄ : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs₂
      field_simp
    simp only [h₂, mul_pow]
    rw [integral_const_mul, integral_mul_left_eq_self
      (fun h : ambientGroup w d ↦ (h : Matrix (Fin d) (Fin d) ℂ) i₀ i₀ ^ (2 * k)) r⁻¹, mul_comm,
      pow_mul, ← Complex.ofReal_pow, sq, hs₁]

/-- **The moments of a column of `O(d)` are a combination of the tensors of perfect matchings.** -/
lemma columnMoment_mem_span (hw : Even w) (i₀ : Fin d) :
    columnMoment w i₀ ∈ Submodule.span ℂ (Set.range (matchingTensor (P := S) (I := Fin d))) := by
  rcases Nat.even_or_odd (Fintype.card S) with hk | hk
  · rcases hk with ⟨k, hk⟩
    have hk' : Fintype.card S = 2 * k := by omega
    have hN : (Fintype.card (PerfectMatching S) : ℂ) ≠ 0 := by
      rw [card_perfectMatching S hk']
      exact Nat.cast_ne_zero.mpr (Nat.doubleFactorial_pos _).ne'
    let C : ℂ := ∫ h : ambientGroup w d, (h : Matrix (Fin d) (Fin d) ℂ) i₀ i₀ ^ (2 * k)
      ∂haarProb (ambientGroup w d)
    have h₁ : columnMoment w i₀ =
        (C / Fintype.card (PerfectMatching S)) • ∑ π : PerfectMatching S, matchingTensor π := by
      rw [← sub_eq_zero]
      refine eq_zero_of_forall_sum_mul_prod (fun σ a ↦ ?_) fun y ↦ ?_
      · simp only [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply]
        rw [sum_matchingTensor_comp]
        congr 1
        exact integral_congr_ae (Eventually.of_forall fun h ↦
          Equiv.prod_comp σ fun p ↦ (h : Matrix (Fin d) (Fin d) ℂ) (a p) i₀)
      · simp only [Pi.sub_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, sub_mul,
          Finset.sum_sub_distrib]
        rw [sum_columnMoment_mul_prod hw i₀ y hk', sub_eq_zero]
        have h₂ : ∑ a : S → Fin d, C / (Fintype.card (PerfectMatching S) : ℂ) *
            (∑ π : PerfectMatching S, matchingTensor π a) * ∏ p, (y (a p) : ℂ) =
              C / (Fintype.card (PerfectMatching S) : ℂ) * ∑ π : PerfectMatching S,
                ∑ a : S → Fin d, matchingTensor π a * ∏ p, (y (a p) : ℂ) := by
          simp only [mul_assoc, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
        rw [h₂]
        simp only [sum_matchingTensor_mul_prod_real _ y hk', Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul]
        field_simp
        exact mul_comm _ _
    rw [h₁]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun π _ ↦ Submodule.subset_span ⟨π, rfl⟩)
  · have h₁ : columnMoment w i₀ = (0 : (S → Fin d) → ℂ) := by
      funext a
      rcases exists_ambient_coe_eq (w := w) hw (R := (-1 : Matrix (Fin d) (Fin d) ℝ)) (by simp) with
        ⟨n, hn⟩
      have h₂ : columnMoment w i₀ a = -columnMoment w i₀ a := by
        rw [columnMoment, ← integral_neg]
        refine (integral_mul_left_eq_self _ n).symm.trans
          (integral_congr_ae (Eventually.of_forall fun h ↦ ?_))
        have h₃ : ((n * h : ambientGroup w d) : Matrix (Fin d) (Fin d) ℂ) =
            (n : Matrix (Fin d) (Fin d) ℂ) * h := rfl
        have h₄ : (n : Matrix (Fin d) (Fin d) ℂ) = -1 := by
          rw [hn]
          ext i j
          simp [one_apply, apply_ite]
        simp only [h₃, h₄, Matrix.neg_mul, Matrix.one_mul, Matrix.neg_apply]
        rw [Finset.prod_neg, Finset.card_univ, hk.neg_one_pow, neg_one_mul]
      exact CharZero.eq_neg_self_iff.mp h₂
    rw [h₁]
    exact Submodule.zero_mem _

end Moment

section Gluing

variable {P : Type u} {I : Type*} [Fintype P] [DecidableEq I] {J : Type*} [Fintype J]
  [DecidableEq J] (j : P → J)

lemma exists_matchingTensor_eq_prod (π : ∀ s, PerfectMatching {p // j p = s}) :
    ∃ π' : PerfectMatching P, ∀ a : P → I, ∏ s, matchingTensor (π s) (fun p ↦ a p.1) =
      matchingTensor π' a := by
  let e : Perm P := ofFiberEquiv fun s ↦ (π s).val
  have he (s : J) (q : P) (h : j q = s) : e q = ((π s).val ⟨q, h⟩).1 := by
    subst h
    rfl
  have he₁ (s : J) (x : {p // j p = s}) : e x.1 = ((π s).val x).1 := he s x.1 x.2
  refine ⟨⟨e, fun p ↦ ?_, fun p h ↦ ?_⟩, fun a ↦ ?_⟩
  · rw [he (j p) p rfl, he₁, (π (j p)).apply_apply]
  · rw [he (j p) p rfl] at h
    exact (π (j p)).apply_ne ⟨p, rfl⟩ (Subtype.ext h)
  · simp only [matchingTensor]
    rw [Fintype.prod_ite_zero, Finset.prod_const_one]
    refine if_congr ⟨fun h ↦ funext fun p ↦ ?_, fun h s ↦ funext fun x ↦ ?_⟩ rfl rfl
    · have h₁ : a ((π (j p)).val ⟨p, rfl⟩).1 = a p := congrFun (h (j p)) ⟨p, rfl⟩
      rw [Function.comp_apply, he (j p) p rfl, h₁]
    · have h₁ : a (e x.1) = a x.1 := congrFun h x.1
      rwa [he₁] at h₁

lemma prod_fiber_mem_span {F : ∀ s, ({p // j p = s} → I) → ℂ}
    (hF : ∀ s, F s ∈ Submodule.span ℂ (Set.range (matchingTensor (P := {p // j p = s}) (I := I)))) :
    (fun a : P → I ↦ ∏ s, F s fun p ↦ a p.1) ∈
      Submodule.span ℂ (Set.range (matchingTensor (P := P) (I := I))) := by
  classical
  choose c hc using fun s ↦ (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hF s)
  have h₁ : (fun a : P → I ↦ ∏ s, F s fun p ↦ a p.1) = ∑ π : ∀ s, PerfectMatching {p // j p = s},
      (∏ s, c s (π s)) • fun a : P → I ↦ ∏ s, matchingTensor (π s) fun p ↦ a p.1 := by
    funext a
    simp only [← hc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.prod_univ_sum,
      Fintype.piFinset_univ, Finset.prod_mul_distrib]
  rw [h₁]
  refine Submodule.sum_mem _ fun π _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  rcases exists_matchingTensor_eq_prod (I := I) j π with ⟨π', hπ'⟩
  exact ⟨π', (funext hπ').symm⟩

end Gluing

section Fundamental

variable {w d : ℕ} {P : Type u} [Fintype P]

instance : SecondCountableTopology (ambientGroup w d) := by
  have : SecondCountableTopology (Matrix (Fin d) (Fin d) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin d → Fin d → ℂ))
  have : SecondCountableTopology (unitaryGroup (Fin d) ℂ) :=
    Subtype.secondCountableTopology _
  exact Subtype.secondCountableTopology _

variable (w) in
/-- The moments of the random matrix whose column `s` is the column `s` of `g_s`, for independent
Haar random elements `g_s` of `O(d)`: the entry at the tuple of rows `a` and the tuple of columns
`j` of the expectation of its tensor power. -/
noncomputable def randomMoment (j a : P → Fin d) : ℂ :=
  ∫ g : Fin d → ambientGroup w d, ∏ p, (g (j p) : Matrix (Fin d) (Fin d) ℂ) (a p) (j p)
    ∂Measure.pi fun _ ↦ haarProb (ambientGroup w d)

lemma randomMoment_eq_prod (j a : P → Fin d) :
    randomMoment w j a = ∏ s, columnMoment w s fun p : {p // j p = s} ↦ a p.1 := by
  have h₁ (g : Fin d → ambientGroup w d) : ∏ p, (g (j p) : Matrix (Fin d) (Fin d) ℂ) (a p) (j p) =
      ∏ s, ∏ p : {p // j p = s}, (g s : Matrix (Fin d) (Fin d) ℂ) (a p.1) s := by
    rw [← Fintype.prod_fiberwise j]
    refine Finset.prod_congr rfl fun s _ ↦ Finset.prod_congr rfl fun p _ ↦ ?_
    rw [p.2]
  simp only [randomMoment, h₁]
  exact integral_fintype_prod_eq_prod fun s (h : ambientGroup w d) ↦
    ∏ p : {p // j p = s}, (h : Matrix (Fin d) (Fin d) ℂ) (a p.1) s

variable [DecidableEq P]

lemma randomMoment_mem_span (hw : Even w) (j : P → Fin d) :
    randomMoment w j ∈ Submodule.span ℂ (Set.range (matchingTensor (P := P) (I := Fin d))) := by
  have h₁ : randomMoment w j = fun a ↦ ∏ s, columnMoment w s fun p : {p // j p = s} ↦ a p.1 :=
    funext (randomMoment_eq_prod j)
  rw [h₁]
  exact prod_fiber_mem_span j fun s ↦ columnMoment_mem_span hw s

lemma exists_mul_diagonal_mul (A : Matrix (Fin d) (Fin d) ℝ) : ∃ (B C : Matrix (Fin d) (Fin d) ℝ)
    (D : Fin d → ℝ), Bᵀ * B = 1 ∧ Cᵀ * C = 1 ∧ (∀ i, 0 ≤ D i) ∧ A = B * diagonal D * C := by
  let e : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) := EuclideanSpace.basisFun (Fin d) ℝ
  rcases (toEuclideanLin A).exists_linearIsometryEquiv_eq_comp_toLin_diagonal_comp e with ⟨U, V, h⟩
  have hc (W : EuclideanSpace ℝ (Fin d) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin d)) :
      (W : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) = W.toLinearEquiv.toLinearMap :=
    rfl
  have hU : U.toMatrix e.toBasis e.toBasis ∈ unitaryGroup (Fin d) ℝ :=
    U.toMatrix_mem_unitaryGroup e e
  have hV : V.toMatrix e.toBasis e.toBasis ∈ unitaryGroup (Fin d) ℝ :=
    V.toMatrix_mem_unitaryGroup e e
  rw [hc U, hc V] at h
  refine ⟨U.toMatrix e.toBasis e.toBasis, V.toMatrix e.toBasis e.toBasis,
    fun i ↦ (toEuclideanLin A).singularValues i, mem_unitaryGroup_iff'.mp hU,
    mem_unitaryGroup_iff'.mp hV, fun i ↦ (toEuclideanLin A).singularValues_nonneg _, ?_⟩
  simpa only [e, toEuclideanLin_eq_toLin_orthonormal, LinearMap.toMatrix_comp e.toBasis e.toBasis
    e.toBasis, LinearMap.toMatrix_toLin, mul_assoc, RCLike.ofReal_real_eq_id, id] using
      congrArg (LinearMap.toMatrix e.toBasis e.toBasis) h

lemma ofReal_re_ambient (hw : Even w) (g : ambientGroup w d) (a b : Fin d) :
    (((g : Matrix (Fin d) (Fin d) ℂ) a b).re : ℂ) = (g : Matrix (Fin d) (Fin d) ℂ) a b := by
  rcases (mem_ambientGroup_iff_of_even hw g.1).mp g.2 with ⟨B, -, hB⟩
  have h₁ : (g : Matrix (Fin d) (Fin d) ℂ) a b = (B a b : ℂ) := by
    rw [← hB]
    rfl
  rw [h₁, Complex.ofReal_re]

variable {f : (P → Fin d) → ℂ}

lemma star_dotProduct_tensorRep_mulVec_eq
    (hf : ∀ g : ambientGroup w d, tensorRep (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ f = f)
    (g : ambientGroup w d) (v : (P → Fin d) → ℂ) :
    star f ⬝ᵥ tensorRep (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ v = star f ⬝ᵥ v := by
  have h₁ : (tensorRep (g : Matrix (Fin d) (Fin d) ℂ))ᴴ *ᵥ f = f := by
    have h₂ :
        (g : Matrix (Fin d) (Fin d) ℂ)ᴴ = ((g⁻¹ : ambientGroup w d) : Matrix (Fin d) (Fin d) ℂ) :=
      rfl
    rw [conjTranspose_tensorRep, h₂, hf]
  rw [dotProduct_mulVec]
  have h₂ : star f ᵥ* tensorRep (g : Matrix (Fin d) (Fin d) ℂ) =
      star ((tensorRep (g : Matrix (Fin d) (Fin d) ℂ))ᴴ *ᵥ f) := by
    rw [star_mulVec, conjTranspose_conjTranspose]
  rw [h₂, h₁]

lemma zero_le_re_star_dotProduct (hw : Even w)
    (hf : ∀ g : ambientGroup w d, tensorRep (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ f = f)
    (A : Matrix (Fin d) (Fin d) ℝ) : 0 ≤ (star f ⬝ᵥ tensorRep (A.map Complex.ofReal) *ᵥ f).re := by
  rcases exists_mul_diagonal_mul A with ⟨B, C, D, hB, hC, hD, rfl⟩
  rcases exists_ambient_coe_eq hw hB with ⟨g₁, hg₁⟩
  rcases exists_ambient_coe_eq hw hC with ⟨g₂, hg₂⟩
  have h₁ : (B * diagonal D * C).map Complex.ofReal = (g₁ : Matrix (Fin d) (Fin d) ℂ) *
      diagonal (fun i ↦ (D i : ℂ)) * (g₂ : Matrix (Fin d) (Fin d) ℂ) := by
    rw [hg₁, hg₂]
    have h₂ : (diagonal D).map Complex.ofReal = diagonal fun i ↦ (D i : ℂ) := by
      ext i j
      by_cases h : i = j
      · subst h
        simp
      · simp [h]
    rw [← h₂]
    exact (Matrix.map_mul (f := Complex.ofRealHom)).trans
      (congrArg (· * C.map Complex.ofReal) (Matrix.map_mul (f := Complex.ofRealHom)))
  rw [h₁, tensorRep_mul, tensorRep_mul, ← mulVec_mulVec, hf, ← mulVec_mulVec,
    star_dotProduct_tensorRep_mulVec_eq hf, tensorRep_diagonal, dotProduct, Complex.re_sum]
  refine Finset.sum_nonneg fun a _ ↦ ?_
  have h₂ : star (f a) * ((∏ p, (D (a p) : ℂ)) * f a) =
      (((∏ p, D (a p)) * Complex.normSq (f a) : ℝ) : ℂ) := by
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
    ring1
  rw [mulVec_diagonal, Pi.star_apply, h₂, Complex.ofReal_re]
  exact mul_nonneg (Finset.prod_nonneg fun p _ ↦ hD _) (Complex.normSq_nonneg _)

lemma eq_zero_of_star_dotProduct_eq_zero (hw : Even w)
    (hf : ∀ g : ambientGroup w d, tensorRep (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ f = f)
    (h : ∀ v ∈ Submodule.span ℂ (Set.range (matchingTensor (P := P) (I := Fin d))),
      star f ⬝ᵥ v = 0) : f = 0 := by
  by_contra hne
  let X (g : Fin d → ambientGroup w d) : Matrix (Fin d) (Fin d) ℂ :=
    of fun a s ↦ (g s : Matrix (Fin d) (Fin d) ℂ) a s
  let I₀ (a b : P → Fin d) (g : Fin d → ambientGroup w d) : ℂ :=
    ∏ p, (g (b p) : Matrix (Fin d) (Fin d) ℂ) (a p) (b p)
  have hI₀ (a b : P → Fin d) : Continuous (I₀ a b) := continuous_finsetProd _ fun p _ ↦
    (ambientEntry (a p) (b p)).continuous.comp (continuous_apply _)
  let ψ (g : Fin d → ambientGroup w d) : ℂ := star f ⬝ᵥ tensorRep (X g) *ᵥ f
  have hψ (g : Fin d → ambientGroup w d) : ψ g = ∑ a, ∑ b, star (f a) * (I₀ a b g * f b) := by
    simp only [ψ, dotProduct, mulVec, Finset.mul_sum]
    rfl
  have hcont : Continuous ψ := by
    have h₁ : ψ = fun g ↦ ∑ a, ∑ b, star (f a) * (I₀ a b g * f b) := funext hψ
    rw [h₁]
    exact continuous_finsetSum _ fun a _ ↦ continuous_finsetSum _ fun b _ ↦
      continuous_const.mul ((hI₀ a b).mul continuous_const)
  have hint₁ (a b : P → Fin d) : Integrable (fun g ↦ star (f a) * (I₀ a b g * f b))
      (Measure.pi fun _ ↦ haarProb (ambientGroup w d)) :=
    (continuous_const.mul ((hI₀ a b).mul continuous_const)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hzero : ∫ g, ψ g ∂Measure.pi (fun _ ↦ haarProb (ambientGroup w d)) = 0 := by
    have h₁ : ∫ g, ψ g ∂Measure.pi (fun _ ↦ haarProb (ambientGroup w d)) =
        star f ⬝ᵥ ∑ b, f b • randomMoment w b := by
      simp only [hψ]
      rw [integral_finsetSum _ fun a _ ↦ integrable_finsetSum _ fun b _ ↦ hint₁ a b]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [integral_finsetSum _ fun b _ ↦ hint₁ a b, Finset.sum_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ ↦ ?_
      rw [integral_const_mul, integral_mul_const, Pi.smul_apply, smul_eq_mul, mul_comm (f b)]
      rfl
    rw [h₁]
    exact h _ (Submodule.sum_mem _ fun b _ ↦ Submodule.smul_mem _ _ (randomMoment_mem_span hw b))
  have hre (g : Fin d → ambientGroup w d) : 0 ≤ (ψ g).re := by
    have h₁ : X g =
        (Matrix.of fun a s ↦ ((g s : Matrix (Fin d) (Fin d) ℂ) a s).re).map Complex.ofReal := by
      ext a s
      exact (ofReal_re_ambient hw (g s) a s).symm
    have h₂ : ψ g = star f ⬝ᵥ tensorRep (X g) *ᵥ f := rfl
    rw [h₂, h₁]
    exact zero_le_re_star_dotProduct hw hf _
  have hX : X 1 = 1 := by
    ext a s
    rfl
  have hpos : (ψ 1).re ≠ 0 := by
    have h₁ : ψ 1 = star f ⬝ᵥ f := by
      simp only [ψ, hX, tensorRep_one, one_mulVec]
    rw [h₁]
    exact (Complex.pos_iff.mp (dotProduct_star_self_pos_iff.mpr hne)).1.ne'
  have h₁ : 0 < ∫ g, (ψ g).re ∂Measure.pi (fun _ ↦ haarProb (ambientGroup w d)) :=
    (Complex.continuous_re.comp hcont).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (HasCompactSupport.of_compactSpace _) hre hpos
  have h₂ : ∫ g, (ψ g).re ∂Measure.pi (fun _ ↦ haarProb (ambientGroup w d)) = 0 := by
    have h₃ : Integrable ψ (Measure.pi fun _ ↦ haarProb (ambientGroup w d)) :=
      hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    exact (Complex.reCLM.integral_comp_comm h₃).trans (by rw [hzero, map_zero])
  exact absurd h₂ h₁.ne'

lemma exists_eq_add_star_dotProduct_eq_zero {ι : Type*} [Fintype ι] (K : Submodule ℂ (ι → ℂ))
    (v : ι → ℂ) : ∃ y ∈ K, ∃ z, (∀ x ∈ K, star x ⬝ᵥ z = 0) ∧ v = y + z := by
  let L : EuclideanSpace ℂ ι ≃ₗ[ℂ] (ι → ℂ) := WithLp.linearEquiv 2 ℂ (ι → ℂ)
  rcases (K.comap L.toLinearMap).exists_add_mem_mem_orthogonal (L.symm v) with ⟨y, hy, z, hz, hyz⟩
  refine ⟨L y, hy, L z, fun x hx ↦ ?_, ?_⟩
  · have h₁ : L.symm x ∈ K.comap L.toLinearMap := by
      rwa [Submodule.mem_comap, LinearEquiv.coe_coe, L.apply_symm_apply]
    have h₂ : inner ℂ (L.symm x) z = 0 := Submodule.inner_right_of_mem_orthogonal h₁ hz
    rwa [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h₂
  · rw [← map_add, ← hyz, L.apply_symm_apply]

/-- **The first fundamental theorem of invariant theory for `O(d)`**: an invariant tensor is a
combination of the tensors of perfect matchings. -/
lemma mem_span_matchingTensor_of_forall_mulVec_eq (hw : Even w)
    (hf : ∀ g : ambientGroup w d, tensorRep (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ f = f) :
    f ∈ Submodule.span ℂ (Set.range (matchingTensor (P := P) (I := Fin d))) := by
  rcases exists_eq_add_star_dotProduct_eq_zero
    (Submodule.span ℂ (Set.range (matchingTensor (P := P) (I := Fin d)))) f with ⟨y, hy, z, hz, rfl⟩
  have hK (g : ambientGroup w d) {v : (P → Fin d) → ℂ}
      (hv : v ∈ Submodule.span ℂ (Set.range (matchingTensor (P := P) (I := Fin d)))) :
      tensorRep (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ v = v := by
    induction hv using Submodule.span_induction with
    | mem x hx =>
      rcases hx with ⟨π, rfl⟩
      exact tensorRep_mulVec_matchingTensor (mul_transpose_self_ambient hw g) π
    | zero => exact mulVec_zero _
    | add x y _ _ hx hy => rw [mulVec_add, hx, hy]
    | smul c x _ hx => rw [mulVec_smul, hx]
  have hz₀ : z = 0 := by
    refine eq_zero_of_star_dotProduct_eq_zero hw (fun g ↦ ?_) fun v hv ↦ ?_
    · have h₁ : tensorRep (g : Matrix (Fin d) (Fin d) ℂ) *ᵥ (y + z) = y + z := hf g
      rw [mulVec_add, hK g hy] at h₁
      exact add_left_cancel h₁
    · rw [star_dotProduct, hz v hv, star_zero]
  rw [hz₀, add_zero]
  exact hy

end Fundamental

end SatoTateGroup
