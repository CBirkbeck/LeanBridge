import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Matrix.CharP
import LeanBridge.ForMathlib.GroupTheory.GroupAction.ProjectiveLineCoprime
import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.SutherlandGroupLabel
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.CenterFinTwo
import TauCeti.LinearAlgebra.Matrix.RationalCanonicalFormFinTwo

/-!
# Dickson's classification of the subgroups of `GL₂(𝔽_p)`

Every subgroup `H` of `GL₂(𝔽_p)` satisfies one of the conditions of Sutherland's classes `G`, `B`,
`Cs`, `Cn`, `Ns`, `Nn`, `A4`, `S4`, `A5` (`SutherlandClass.Holds`), so it has a Sutherland class
(`Matrix.GeneralLinearGroup.exists_hasSutherlandClass`): this is Dickson's classification, as stated
in Proposition 3.1 of Sutherland, *Computing images of Galois representations attached to elliptic
curves* (arXiv:1504.07618v7). The proof is the following.

* If `p` divides `|H|`, then `H` contains an element `x` of order `p`, which is a transvection with
  a fixed vector `v`. Either `H` preserves the line of `v`, so `H` lies in a Borel subgroup; or some
  `h ∈ H` moves it, and `x` and `h x h⁻¹` are transvections with different axes, whose powers give
  all the elementary matrices in a suitable basis, so `H` contains `SL₂(𝔽_p)`.
* If `p` does not divide `|H|`, the image of `H` in `PGL₂(𝔽_p) ⊆ PGL₂(𝔽̄_p)` has order prime to `p`,
  so it is cyclic, dihedral or isomorphic to `A₄`, `S₄`, `A₅` by the classification of the finite
  groups acting with two fixed points (`Matrix.ProjGenLinGroup.classification_of_natCard_ne_zero`).
  A matrix of finite order modulo scalars, order prime to `p`, is scalar, or diagonalisable, or has
  no eigenvalue in `𝔽_p`, and then it is conjugate into the non-split Cartan subgroup. So cyclic
  images come from subgroups of Cartan subgroups, and dihedral images from subgroups of their
  normalizers, as an element conjugating a non-scalar element of a Cartan subgroup into that
  subgroup normalizes it.

## Main results

* `Matrix.GeneralLinearGroup.exists_le_cartan_of_isCyclic`: a subgroup of order prime to `p` with
  cyclic projective image is conjugate to a subgroup of a Cartan subgroup, for odd `p`.
* `Matrix.GeneralLinearGroup.exists_le_cartan_normalizer_of_dihedral`: a subgroup of order prime to
  `p` with dihedral projective image is conjugate to a subgroup of the normalizer of a Cartan
  subgroup, for odd `p`.
* `Matrix.GeneralLinearGroup.classification_projectiveImage`: the image in `PGL₂(𝔽_p)` of a subgroup
  of order prime to `p` is cyclic, dihedral or isomorphic to `A₄`, `S₄`, `A₅`.
* `Matrix.GeneralLinearGroup.holds_G_or_holds_B_of_orderOf_eq`: a subgroup containing an element of
  order `p` contains `SL₂(𝔽_p)` or lies in a Borel subgroup.
* `Matrix.GeneralLinearGroup.exists_conj_mem_cartan`: a matrix of finite order prime to `p` modulo
  scalars is conjugate into a Cartan subgroup, for odd `p`.
* `Matrix.GeneralLinearGroup.mem_labelNs_iff`: `Ns` consists of the diagonal and the antidiagonal
  invertible matrices.
* `Matrix.GeneralLinearGroup.mem_labelNs_of_mulAut_conj_mem`, `mem_labelNn_of_mulAut_conj_mem`: an
  element conjugating a non-scalar element of `Cs` (`Cn`) into `Cs` (`Cn`) lies in `Ns` (`Nn`).
* `Matrix.GeneralLinearGroup.exists_holds` and `Matrix.GeneralLinearGroup.exists_hasSutherlandClass`
  (LMFDB `ec.galois_rep_modell_image`): Dickson's classification: every subgroup of `GL₂(𝔽_p)`
  satisfies the condition of some class, and so has a Sutherland class.
* `Matrix.GeneralLinearGroup.HasSutherlandClass.eq`: the class is unique.
-/

open Matrix MulAction TauCeti

open scoped MatrixGroups Pointwise

namespace Matrix.GeneralLinearGroup

section Field

variable {F : Type*} [Field F] {N : Matrix (Fin 2) (Fin 2) F} {n : ℕ} {v w : Fin 2 → F}
  {K : Subgroup (GL (Fin 2) F)}

lemma mul_self_eq_zero_of_pow_eq_zero (hN : N ^ n = 0) : N * N = 0 := by
  have h : Polynomial.aeval N N.charpoly = 0 := aeval_self_charpoly N
  rw [sub_eq_zero.mp (isNilpotent_charpoly_sub_pow_of_isNilpotent ⟨n, hN⟩).eq_zero] at h
  simpa [sq] using h

lemma swapGL_inv : (swapGL F)⁻¹ = swapGL F :=
  inv_eq_of_mul_eq_one_right (swapGL_mul_self F)

lemma val_upperRightHom (u : F) : (upperRightHom u).val = !![1, u; 0, 1] :=
  rfl

lemma det_ker_le_of_forall_mem (hU : ∀ u, upperRightHom u ∈ K)
    (hL : ∀ u, MulAut.conj (swapGL F) (upperRightHom u) ∈ K) :
    (det : GL (Fin 2) F →* Fˣ).ker ≤ K := by
  rw [← SpecialLinearGroup.range_toGL_eq_ker_det]
  rintro - ⟨M, rfl⟩
  refine SL2.transvection_induction (fun M ↦ SpecialLinearGroup.toGL M ∈ K) (fun i j hij c ↦ ?_)
    (fun A B hA hB ↦ by simpa using mul_mem hA hB) M
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · have h : SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij c) = upperRightHom c :=
      Units.ext <| by
        ext a b
        fin_cases a <;> fin_cases b <;> simp [SpecialLinearGroup.transvection_coe]
    exact h ▸ hU c
  · have h : SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij c) =
        MulAut.conj (swapGL F) (upperRightHom c) := Units.ext <| by
      simp only [MulAut.conj_apply, swapGL_inv]
      ext a b
      fin_cases a <;> fin_cases b <;> simp [SpecialLinearGroup.transvection_coe]
    exact h ▸ hL c
  · exact absurd rfl hij

lemma exists_eq_smul_of_cross_eq_zero (hv : v ≠ 0) (h : v 0 * w 1 - w 0 * v 1 = 0) :
    ∃ c : F, w = c • v := by
  by_cases h₀ : v 0 = 0
  · have h₁ : v 1 ≠ 0 := fun h₁ ↦ hv <| funext fun i ↦ by fin_cases i <;> assumption
    have hw₀ : w 0 = 0 := by
      rw [h₀, zero_mul, zero_sub, neg_eq_zero] at h
      exact (mul_eq_zero.mp h).resolve_right h₁
    refine ⟨w 1 / v 1, funext fun i ↦ ?_⟩
    fin_cases i
    · simp [h₀, hw₀]
    · simp [div_mul_cancel₀ _ h₁]
  · refine ⟨w 0 / v 0, funext fun i ↦ ?_⟩
    fin_cases i
    · simp [div_mul_cancel₀ _ h₀]
    · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul]
      field_simp
      linear_combination h

end Field

variable {p : ℕ} [Fact p.Prime] {H K : Subgroup (GL (Fin 2) (ZMod p))} {g x : GL (Fin 2) (ZMod p)}
  {s : ZMod p}

variable (H) in
lemma map_conj_mem_subgroupConjClass (P : GL (Fin 2) (ZMod p)) :
    H.map (MulAut.conj P).toMonoidHom ∈ subgroupConjClass p H :=
  ⟨ConjAct.toConjAct P, (map_conj_eq_smul P).symm⟩

lemma orderOf_mulAut_conj (P y : GL (Fin 2) (ZMod p)) : orderOf (MulAut.conj P y) = orderOf y :=
  (MulAut.conj P).orderOf_eq y

lemma mul_self_sub_one_eq_zero (hx : orderOf x = p) : (x.val - 1) * (x.val - 1) = 0 :=
  mul_self_eq_zero_of_pow_eq_zero (n := p) <| by
    have h₁ : x ^ p = 1 := orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hx)
    rw [sub_pow_char_of_commute p (Commute.one_right _), one_pow, ← Units.val_pow_eq_pow_val, h₁,
      Units.val_one, sub_self]

lemma exists_eq_upperRightHom (hx : orderOf x = p) (hfix : x.val *ᵥ Pi.single 0 1 = Pi.single 0 1) :
    ∃ s : ZMod p, s ≠ 0 ∧ x = upperRightHom s := by
  have h₀₀ : x 0 0 = 1 := by
    simpa using congrFun hfix 0
  have h₁₀ : x 1 0 = 0 := by
    simpa using congrFun hfix 1
  have h₁₁ : x 1 1 = 1 := by
    have h : ((x.val - 1) * (x.val - 1)) 1 1 = 0 := by
      rw [mul_self_sub_one_eq_zero hx]
      rfl
    simp [Matrix.mul_apply, h₁₀] at h
    exact sub_eq_zero.mp h
  have hx' : x = upperRightHom (x 0 1) := by
    refine Units.ext ?_
    rw [val_upperRightHom]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h₀₀, h₁₀, h₁₁]
  refine ⟨x 0 1, fun hs ↦ ?_, hx'⟩
  rw [hs, AddChar.map_zero_eq_one] at hx'
  rw [hx', orderOf_one] at hx
  exact (Fact.out : p.Prime).ne_one hx.symm

lemma upperRightHom_eq_pow (hs : s ≠ 0) (u : ZMod p) :
    upperRightHom u = upperRightHom s ^ (u / s).val := by
  rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, div_mul_cancel₀ _ hs]

lemma upperRightHom_mem_of_mem (hs : s ≠ 0) (h : upperRightHom s ∈ K) (u : ZMod p) :
    upperRightHom u ∈ K :=
  upperRightHom_eq_pow hs u ▸ pow_mem h _

lemma conj_upperRightHom_mem_of_mem (hs : s ≠ 0) {P : GL (Fin 2) (ZMod p)}
    (h : MulAut.conj P (upperRightHom s) ∈ K) (u : ZMod p) :
    MulAut.conj P (upperRightHom u) ∈ K := by
  rw [upperRightHom_eq_pow hs u, map_pow]
  exact pow_mem h _

/-- **A subgroup of `GL₂(𝔽_p)` containing an element of order `p` contains `SL₂(𝔽_p)` or lies in a
Borel subgroup**, up to conjugacy (Proposition 3.1 of Sutherland, arXiv:1504.07618v7): an element
`x` of order `p` has a fixed vector `v`. If `H` preserves the line of `v`, it lies in a Borel
subgroup. Otherwise, for `h ∈ H` moving this line, `x` and `h x h⁻¹` are, in the basis
`(v, h v)`, an upper and a lower triangular transvection, whose powers generate `SL₂(𝔽_p)`. -/
lemma holds_G_or_holds_B_of_orderOf_eq (hxH : x ∈ H) (hx : orderOf x = p) :
    SutherlandClass.Holds p H .G ∨ SutherlandClass.Holds p H .B := by
  have hN : x.val - 1 ≠ 0 := fun hN ↦ by
    have h₁ : x = 1 := Units.ext (sub_eq_zero.mp hN)
    rw [h₁, orderOf_one] at hx
    exact (Fact.out : p.Prime).ne_one hx.symm
  rcases (not_forall.mp fun h ↦ hN (Matrix.mulVec_injective (funext fun w ↦ by
    simpa using h w)) : ∃ w, ¬(x.val - 1) *ᵥ w = 0) with ⟨w, hw⟩
  have hfix : x.val *ᵥ ((x.val - 1) *ᵥ w) = (x.val - 1) *ᵥ w := by
    have h₁ : (x.val - 1) *ᵥ ((x.val - 1) *ᵥ w) = 0 := by
      rw [Matrix.mulVec_mulVec, mul_self_sub_one_eq_zero hx, Matrix.zero_mulVec]
    rwa [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at h₁
  by_cases hH : ∀ h ∈ H, ∃ c : ZMod p, h.val *ᵥ ((x.val - 1) *ᵥ w) = c • (x.val - 1) *ᵥ w
  · refine Or.inr ?_
    rcases exists_mulVec_single_eq hw with ⟨P, hP⟩
    refine ⟨H.map (MulAut.conj P⁻¹).toMonoidHom, map_conj_mem_subgroupConjClass H _, ?_,
      MulAut.conj P⁻¹ x, Subgroup.mem_map_of_mem _ hxH, (orderOf_mulAut_conj _ x).trans hx⟩
    rw [gl2Borel_eq_lineStabilizer]
    rintro - ⟨h, hh, rfl⟩
    rcases hH h hh with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    have hP' : ((P⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ
        ((x.val - 1) *ᵥ w) = Pi.single 0 1 := by
      rw [← hP, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Units.val_mul]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hP, hc, Matrix.mulVec_smul, hP']
  · refine Or.inl ?_
    push Not at hH
    rcases hH with ⟨h, hh, hc⟩
    have hdet : (!![((x.val - 1) *ᵥ w) 0, (h.val *ᵥ ((x.val - 1) *ᵥ w)) 0;
        ((x.val - 1) *ᵥ w) 1, (h.val *ᵥ ((x.val - 1) *ᵥ w)) 1] :
        Matrix (Fin 2) (Fin 2) (ZMod p)).det ≠ 0 := fun hd ↦ by
      rw [Matrix.det_fin_two_of] at hd
      rcases exists_eq_smul_of_cross_eq_zero hw (w := h.val *ᵥ ((x.val - 1) *ᵥ w))
        (by linear_combination hd) with ⟨c, hc'⟩
      exact hc c hc'
    let P : GL (Fin 2) (ZMod p) := mkOfDetNeZero _ hdet
    have hP₀ : P.val *ᵥ Pi.single 0 1 = (x.val - 1) *ᵥ w := by
      ext i
      fin_cases i <;> simp [P]
    have hP₁ : P.val *ᵥ Pi.single 1 1 = h.val *ᵥ ((x.val - 1) *ᵥ w) := by
      ext i
      fin_cases i <;> simp [P]
    have hPinv (u : Fin 2 → ZMod p) :
        ((P⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ (P.val *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rcases exists_eq_upperRightHom ((orderOf_mulAut_conj P⁻¹ x).trans hx) (by
      simp only [MulAut.conj_apply, inv_inv, Units.val_mul]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hP₀, hfix, ← hP₀, hPinv]) with
      ⟨s, hs, hsx⟩
    have hy : orderOf (MulAut.conj (swapGL (ZMod p)) (MulAut.conj P⁻¹ (h * x * h⁻¹))) = p := by
      rw [orderOf_mulAut_conj, orderOf_mulAut_conj, ← MulAut.conj_apply, orderOf_mulAut_conj, hx]
    have hyfix : (MulAut.conj (swapGL (ZMod p)) (MulAut.conj P⁻¹ (h * x * h⁻¹))).val *ᵥ
        Pi.single 0 1 = Pi.single 0 1 := by
      have hs₀ : (swapGL (ZMod p)).val *ᵥ Pi.single 0 1 = Pi.single 1 1 := by
        ext i
        fin_cases i <;> simp
      have hs₁ : (swapGL (ZMod p)).val *ᵥ Pi.single 1 1 = Pi.single 0 1 := by
        ext i
        fin_cases i <;> simp
      have hh' : ((h⁻¹ : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ
          (h.val *ᵥ ((x.val - 1) *ᵥ w)) = (x.val - 1) *ᵥ w := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
          Matrix.one_mulVec]
      simp only [MulAut.conj_apply, inv_inv, swapGL_inv, Units.val_mul]
      simp only [← Matrix.mulVec_mulVec]
      rw [hs₀, hP₁, hh', hfix, ← hP₁, hPinv, hs₁]
    rcases exists_eq_upperRightHom hy hyfix with ⟨s', hs', hsy⟩
    refine ⟨H.map (MulAut.conj P⁻¹).toMonoidHom, map_conj_mem_subgroupConjClass H _,
      det_ker_le_of_forall_mem (upperRightHom_mem_of_mem hs ?_)
        (conj_upperRightHom_mem_of_mem hs' ?_)⟩
    · exact hsx ▸ Subgroup.mem_map_of_mem _ hxH
    · have hyl : MulAut.conj (swapGL (ZMod p)) (upperRightHom s') =
          MulAut.conj P⁻¹ (h * x * h⁻¹) := by
        rw [← hsy, ← MulAut.mul_apply, ← map_mul, swapGL_mul_self, map_one, MulAut.one_apply]
      exact hyl ▸ Subgroup.mem_map_of_mem _ (mul_mem (mul_mem hh hxH) (inv_mem hh))

lemma injective_map_algebraMap_algebraicClosure :
    Function.Injective (ProjGenLinGroup.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) :
      PGL(Fin 2, ZMod p) →* PGL(Fin 2, AlgebraicClosure (ZMod p))) := by
  refine (injective_iff_map_eq_one _).mpr fun h hh ↦ ?_
  induction h using ProjGenLinGroup.induction_on with
  | mk g =>
    rw [ProjGenLinGroup.map_mk, ProjGenLinGroup.mk_eq_one,
      mem_center_iff_val_mem_range_scalar] at hh
    rcases hh with ⟨c, hc⟩
    have hij (i j : Fin 2) : algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) (g i j) =
        Matrix.scalar (Fin 2) c i j := by
      rw [hc]
      exact (GeneralLinearGroup.map_apply _ i j g).symm
    have hf : Function.Injective (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))) :=
      (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))).injective
    have h₀₁ : g 0 1 = 0 := hf <| by
      simpa using hij 0 1
    have h₁₀ : g 1 0 = 0 := hf <| by
      simpa using hij 1 0
    have h₀₀ : g 0 0 = g 1 1 := hf <| by
      rw [hij, hij]
      simp
    refine ProjGenLinGroup.mk_eq_one.mpr <| mem_center_iff_val_mem_range_scalar.mpr ⟨g 0 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h₀₁, h₁₀, h₀₀]

/-- **The image in `PGL₂(𝔽_p)` of a subgroup of `GL₂(𝔽_p)` of order prime to `p` is cyclic, dihedral
of order `2n` with `n ≥ 2`, or isomorphic to `A₄`, `S₄` or `A₅`** (Dickson's classification; see
Proposition 3.1 of Sutherland, arXiv:1504.07618v7). -/
lemma classification_projectiveImage (hH : ¬p ∣ Nat.card H) :
    IsCyclic (projectiveImage H) ∨ (∃ n, 2 ≤ n ∧ Nonempty (projectiveImage H ≃* DihedralGroup n)) ∨
      Nonempty (projectiveImage H ≃* alternatingGroup (Fin 4)) ∨
        Nonempty (projectiveImage H ≃* Equiv.Perm (Fin 4)) ∨
          Nonempty (projectiveImage H ≃* alternatingGroup (Fin 5)) := by
  let e : projectiveImage H ≃* (projectiveImage H).map
      (ProjGenLinGroup.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p)))) :=
    Subgroup.equivMapOfInjective (projectiveImage H) _
      (injective_map_algebraMap_algebraicClosure (p := p))
  have : Finite (projectiveImage H) :=
    Finite.of_surjective _ (ProjGenLinGroup.mk.subgroupMap_surjective H)
  have : Finite ((projectiveImage H).map
      (ProjGenLinGroup.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))) :=
    Finite.of_equiv _ e.toEquiv
  have hdvd : Nat.card ((projectiveImage H).map
      (ProjGenLinGroup.map (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))) ∣ Nat.card H := by
    rw [← Nat.card_congr e.toEquiv]
    exact H.card_map_dvd ProjGenLinGroup.mk
  have hcard : (Nat.card ((projectiveImage H).map (ProjGenLinGroup.map
      (algebraMap (ZMod p) (AlgebraicClosure (ZMod p))))) : AlgebraicClosure (ZMod p)) ≠ 0 :=
    fun h ↦ hH (((CharP.cast_eq_zero_iff (AlgebraicClosure (ZMod p)) p _).mp h).trans hdvd)
  rcases ProjGenLinGroup.classification_of_natCard_ne_zero _ hcard with
    h | ⟨n, hn, hf⟩ | hf | hf | hf
  · exact Or.inl <| isCyclic_of_surjective e.symm e.symm.surjective
  · exact Or.inr <| Or.inl ⟨n, hn, hf.map e.trans⟩
  · exact Or.inr <| Or.inr <| Or.inl (hf.map e.trans)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (hf.map e.trans)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr (hf.map e.trans)

lemma scalar_mem_diagonalTorus (u : (ZMod p)ˣ) : scalar (Fin 2) u ∈ diagonalTorus (ZMod p) 2 :=
  mem_diagonalTorus_of_fin_two (ZMod p) (by simp) (by simp)

lemma scalar_mem_labelCn (hp : p ≠ 2) (u : (ZMod p)ˣ) : scalar (Fin 2) u ∈ labelCn p :=
  (mem_labelCn_iff p hp).mpr ⟨by simp, by simp⟩

/-- **A matrix of finite order prime to `p` modulo scalars is conjugate into a Cartan subgroup of
`GL₂(𝔽_p)`**, for odd `p`: into `Cs` if its characteristic polynomial has a root in `𝔽_p`, its two
roots then being distinct unless the matrix is scalar, and into `Cn` otherwise. -/
lemma exists_conj_mem_cartan (hp : p ≠ 2) {n : ℕ} (hn : (n : ZMod p) ≠ 0)
    (hgn : g ^ n ∈ Subgroup.center (GL (Fin 2) (ZMod p))) :
    ∃ P : GL (Fin 2) (ZMod p), MulAut.conj P⁻¹ g ∈ diagonalTorus (ZMod p) 2 ∨
      MulAut.conj P⁻¹ g ∈ labelCn p := by
  by_cases hgs : g.val ∈ Set.range (Matrix.scalar (Fin 2))
  · rcases mem_range_scalar_fin_two_iff.mp hgs with ⟨h₀₁, h₁₀, -⟩
    refine ⟨1, Or.inl ?_⟩
    simpa using mem_diagonalTorus_of_fin_two (ZMod p) h₀₁ h₁₀
  have hconj {M : GL (Fin 2) (ZMod p)} (hM : M.val ∉ Set.range (Matrix.scalar (Fin 2)))
      (htr : M.val.trace = g.val.trace) (hd : M.val.det = g.val.det) :
      ∃ P : GL (Fin 2) (ZMod p), MulAut.conj P⁻¹ g = M := by
    rcases exists_det_ne_zero_mul_eq_mul_companionFinTwo hgs with ⟨A, hA, hgA⟩
    rcases exists_det_ne_zero_mul_eq_mul_companionFinTwo hM with ⟨B, hB, hMB⟩
    rw [htr, hd] at hMB
    let A' : GL (Fin 2) (ZMod p) := mkOfDetNeZero A hA
    let B' : GL (Fin 2) (ZMod p) := mkOfDetNeZero B hB
    have hgA' : g.val * A'.val = A'.val * companionFinTwo g.val.trace g.val.det := hgA
    have hMB' : M.val * B'.val = B'.val * companionFinTwo g.val.trace g.val.det := hMB
    have h : g * A' = A' * (B'⁻¹ * M * B') := Units.ext <| by
      rw [Units.val_mul, hgA', Units.val_mul, Units.val_mul, Units.val_mul,
        Matrix.mul_assoc _ M.val, hMB', ← Matrix.mul_assoc _ B'.val, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, Matrix.one_mul]
    refine ⟨A' * B'⁻¹, ?_⟩
    rw [MulAut.conj_apply, inv_inv, mul_assoc, inv_mul_eq_iff_eq_mul, ← mul_assoc, h]
    simp [mul_assoc]
  have hdet : g.val.det ≠ 0 := (isUnits_det_units g).ne_zero
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_ne_two p hp
  by_cases hroot : ∃ μ : ZMod p, μ * μ - g.val.trace * μ + g.val.det = 0
  · rcases hroot with ⟨μ, hμ⟩
    by_cases hμ' : μ = g.val.trace - μ
    · have hμ₀ : μ ≠ 0 := fun hμ₀ ↦ hdet <| by
        rw [hμ₀] at hμ
        simpa using hμ
      have htr : g.val.trace = 2 * μ := by
        linear_combination -hμ'
      have hdet' : g.val.det = μ * μ := by
        rw [htr] at hμ
        linear_combination hμ
      have hN : (g.val - μ • 1) * (g.val - μ • 1) = 0 := by
        simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
          Matrix.mul_one]
        rw [← sq, sq_eq_trace_smul_sub_det_smul_one_fin_two, hdet', htr]
        module
      have hg : g.val = μ • 1 := sub_eq_zero.mp <|
        ProjGenLinGroup.eq_zero_of_pow_eq_smul_one_of_natCast_ne_zero hn hμ₀ hN <| by
          rw [add_sub_cancel]
          exact ProjGenLinGroup.val_pow_eq_smul_one_of_field hgn
      exact absurd ⟨μ, by rw [hg, scalar_apply, smul_one_eq_diagonal]⟩ hgs
    · have hdetM : (!![μ, 0; 0, g.val.trace - μ] : Matrix (Fin 2) (Fin 2) (ZMod p)).det ≠ 0 := by
        rw [Matrix.det_fin_two_of]
        intro h
        exact hdet (by linear_combination hμ + h)
      rcases hconj (M := mkOfDetNeZero _ hdetM)
        (fun h ↦ hμ' (by simpa using (mem_range_scalar_fin_two_iff.mp h).2.2))
        (by rw [val_mkOfDetNeZero, Matrix.trace_fin_two_of]; ring1)
        (by rw [val_mkOfDetNeZero, Matrix.det_fin_two_of]; linear_combination -hμ) with ⟨P, hP⟩
      exact ⟨P, Or.inl (hP ▸ mem_diagonalTorus_of_fin_two (ZMod p) (by simp) (by simp))⟩
  · push Not at hroot
    have h4 : (4 : ZMod p) ≠ 0 := by
      have h : (4 : ZMod p) = 2 * 2 := by
        norm_num
      rw [h]
      exact mul_ne_zero h2 h2
    have hs : ¬IsSquare (g.val.trace * g.val.trace / 4 - g.val.det) := by
      rintro ⟨t, ht⟩
      refine hroot (g.val.trace / 2 + t) ?_
      field_simp at ht ⊢
      linear_combination -ht
    have hε : ¬IsSquare (ZMod.leastPrimitiveRoot p : ZMod p) :=
      ZMod.not_isSquare_leastPrimitiveRoot p hp
    have hε₀ : (ZMod.leastPrimitiveRoot p : ZMod p) ≠ 0 := ZMod.leastPrimitiveRoot_ne_zero p
    have hs₀ : g.val.trace * g.val.trace / 4 - g.val.det ≠ 0 := fun h0 ↦ hs ⟨0, by simp [h0]⟩
    have hquot : IsSquare ((g.val.trace * g.val.trace / 4 - g.val.det) /
        (ZMod.leastPrimitiveRoot p : ZMod p)) := by
      refine (quadraticChar_one_iff_isSquare (div_ne_zero hs₀ hε₀)).mp ?_
      have hχ : quadraticChar (ZMod p) ((ZMod.leastPrimitiveRoot p : ZMod p) *
          ((g.val.trace * g.val.trace / 4 - g.val.det) / (ZMod.leastPrimitiveRoot p : ZMod p))) =
          quadraticChar (ZMod p) (ZMod.leastPrimitiveRoot p : ZMod p) * quadraticChar (ZMod p)
            ((g.val.trace * g.val.trace / 4 - g.val.det) / (ZMod.leastPrimitiveRoot p : ZMod p)) :=
        map_mul _ _ _
      rw [mul_div_cancel₀ _ hε₀, quadraticChar_neg_one_iff_not_isSquare.mpr hs,
        quadraticChar_neg_one_iff_not_isSquare.mpr hε] at hχ
      linarith
    rcases hquot with ⟨y, hy⟩
    have hy₀ : y ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hy
      exact (div_ne_zero hs₀ hε₀) hy
    have hsy : g.val.trace * g.val.trace / 4 - g.val.det =
        (ZMod.leastPrimitiveRoot p : ZMod p) * (y * y) := by
      rw [← hy, mul_div_cancel₀ _ hε₀]
    have hdetM : (!![g.val.trace / 2, (ZMod.leastPrimitiveRoot p : ZMod p) * y; y,
        g.val.trace / 2] : Matrix (Fin 2) (Fin 2) (ZMod p)).det = g.val.det := by
      rw [Matrix.det_fin_two_of]
      field_simp at hsy ⊢
      linear_combination hsy
    rcases hconj (M := mkOfDetNeZero _ (hdetM ▸ hdet))
      (fun h ↦ hy₀ (by simpa using (mem_range_scalar_fin_two_iff.mp h).2.1))
      (by rw [val_mkOfDetNeZero, Matrix.trace_fin_two_of]; field_simp; ring1) hdetM with ⟨P, hP⟩
    exact ⟨P, Or.inr (hP ▸ (mem_labelCn_iff p hp).mpr ⟨by simp, by simp⟩)⟩

variable (g) in
lemma inv_apply_of_field : g.val⁻¹ = (g.val.det)⁻¹ • !![g 1 1, -g 0 1; -g 1 0, g 0 0] := by
  rw [Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv']

/-- **`Ns` consists of the diagonal and the antidiagonal invertible matrices.** -/
lemma mem_labelNs_iff : g ∈ labelNs p ↔ (g 0 1 = 0 ∧ g 1 0 = 0) ∨ (g 0 0 = 0 ∧ g 1 1 = 0) := by
  refine ⟨fun hg ↦ ?_, ?_⟩
  · rw [labelNs, Subgroup.zpowers_eq_closure, ← Subgroup.closure_eq (diagonalTorus (ZMod p) 2),
      ← Subgroup.closure_union] at hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact Or.inl ⟨mem_diagonalTorus_iff.mp hx (by decide),
          mem_diagonalTorus_iff.mp hx (by decide)⟩
      · rw [Set.mem_singleton_iff.mp hx]
        simp
    | one => simp
    | mul x y _ _ hx hy =>
      rcases hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases hy with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩
      · exact Or.inl ⟨by simp [Matrix.mul_apply, h₁, h₃], by simp [Matrix.mul_apply, h₂, h₄]⟩
      · exact Or.inr ⟨by simp [Matrix.mul_apply, h₁, h₃], by simp [Matrix.mul_apply, h₂, h₄]⟩
      · exact Or.inr ⟨by simp [Matrix.mul_apply, h₁, h₄], by simp [Matrix.mul_apply, h₂, h₃]⟩
      · exact Or.inl ⟨by simp [Matrix.mul_apply, h₁, h₄], by simp [Matrix.mul_apply, h₂, h₃]⟩
    | inv x _ hx =>
      rcases hx with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
      · exact Or.inl ⟨by simp [inv_apply_of_field, h₁], by simp [inv_apply_of_field, h₂]⟩
      · exact Or.inr ⟨by simp [inv_apply_of_field, h₂], by simp [inv_apply_of_field, h₁]⟩
  · rintro (⟨h₀₁, h₁₀⟩ | ⟨h₀₀, h₁₁⟩)
    · exact diagonalTorus_le_labelNs p (mem_diagonalTorus_of_fin_two (ZMod p) h₀₁ h₁₀)
    · exact mem_sup_zpowers_swapGL_of_fin_two (ZMod p) h₀₀ h₁₁

lemma apply_zero_zero_of_mem_labelNs (hx : x ∈ labelNs p) (hxd : x ∉ diagonalTorus (ZMod p) 2) :
    x 0 0 = 0 :=
  ((mem_labelNs_iff.mp hx).resolve_left fun h ↦ hxd (mem_diagonalTorus_of_fin_two _ h.1 h.2)).1

lemma apply_one_one_of_mem_labelNs (hx : x ∈ labelNs p) (hxd : x ∉ diagonalTorus (ZMod p) 2) :
    x 1 1 = 0 :=
  ((mem_labelNs_iff.mp hx).resolve_left fun h ↦ hxd (mem_diagonalTorus_of_fin_two _ h.1 h.2)).2

lemma trace_eq_zero_of_mem_labelNs (hx : x ∈ labelNs p) (hxd : x ∉ diagonalTorus (ZMod p) 2) :
    x.val.trace = 0 := by
  rw [Matrix.trace_fin_two, apply_zero_zero_of_mem_labelNs hx hxd,
    apply_one_one_of_mem_labelNs hx hxd, add_zero]

/-- **An element conjugating a non-scalar element of `Cs` into `Cs` lies in `Ns`.** -/
lemma mem_labelNs_of_mulAut_conj_mem {h g₁ : GL (Fin 2) (ZMod p)}
    (hg₁ : g₁ ∈ diagonalTorus (ZMod p) 2) (hg₂ : MulAut.conj h g₁ ∈ diagonalTorus (ZMod p) 2)
    (hne : g₁ 0 0 ≠ g₁ 1 1) : h ∈ labelNs p := by
  generalize he : MulAut.conj h g₁ = g₂ at hg₂
  have h₁₀ : g₁ 1 0 = 0 := mem_diagonalTorus_iff.mp hg₁ (by decide)
  have h₀₁ : g₁ 0 1 = 0 := mem_diagonalTorus_iff.mp hg₁ (by decide)
  have h₂₁₀ : g₂ 1 0 = 0 := mem_diagonalTorus_iff.mp hg₂ (by decide)
  have h₂₀₁ : g₂ 0 1 = 0 := mem_diagonalTorus_iff.mp hg₂ (by decide)
  have hm : h.val * g₁.val = g₂.val * h.val := by
    rw [← he, MulAut.conj_apply, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel_right]
  have e₀₀ : h 0 0 * g₁ 0 0 = g₂ 0 0 * h 0 0 := by
    simpa [Matrix.mul_apply, h₁₀, h₂₀₁] using congrFun (congrFun hm 0) 0
  have e₀₁ : h 0 1 * g₁ 1 1 = g₂ 0 0 * h 0 1 := by
    simpa [Matrix.mul_apply, h₀₁, h₂₀₁] using congrFun (congrFun hm 0) 1
  have e₁₀ : h 1 0 * g₁ 0 0 = g₂ 1 1 * h 1 0 := by
    simpa [Matrix.mul_apply, h₁₀, h₂₁₀] using congrFun (congrFun hm 1) 0
  have e₁₁ : h 1 1 * g₁ 1 1 = g₂ 1 1 * h 1 1 := by
    simpa [Matrix.mul_apply, h₀₁, h₂₁₀] using congrFun (congrFun hm 1) 1
  have hdet : h 0 0 * h 1 1 - h 0 1 * h 1 0 ≠ 0 := by
    rw [← Matrix.det_fin_two]
    exact (isUnits_det_units h).ne_zero
  have hA : h 0 0 = 0 ∨ h 0 1 = 0 := by
    by_contra hc
    push Not at hc
    exact hne ((mul_left_cancel₀ hc.1 (e₀₀.trans (mul_comm _ _))).trans
      (mul_left_cancel₀ hc.2 (e₀₁.trans (mul_comm _ _))).symm)
  have hB : h 1 0 = 0 ∨ h 1 1 = 0 := by
    by_contra hc
    push Not at hc
    exact hne ((mul_left_cancel₀ hc.1 (e₁₀.trans (mul_comm _ _))).trans
      (mul_left_cancel₀ hc.2 (e₁₁.trans (mul_comm _ _))).symm)
  refine mem_labelNs_iff.mpr ?_
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · exact absurd (by rw [hA, hB]; ring1) hdet
  · exact Or.inr ⟨hA, hB⟩
  · exact Or.inl ⟨hA, hB⟩
  · exact absurd (by rw [hA, hB]; ring1) hdet

/-- **An element conjugating a non-scalar element of `Cn` into `Cn` lies in `Nn`**, for odd `p`: it
conjugates the matrix `ω` of `Cn` to `±ω`, by comparing traces and determinants; so it or its
product with `!![1, 0; 0, -1]` commutes with `ω`. -/
lemma mem_labelNn_of_mulAut_conj_mem (hp : p ≠ 2) {h g₁ : GL (Fin 2) (ZMod p)}
    (hg₁ : g₁ ∈ labelCn p) (hg₂ : MulAut.conj h g₁ ∈ labelCn p) (hne : g₁ 1 0 ≠ 0) :
    h ∈ labelNn p := by
  generalize he : MulAut.conj h g₁ = g₂ at hg₂
  rw [mem_labelCn_iff p hp] at hg₁ hg₂
  have hω : (omegaGL p).val = !![0, (ZMod.leastPrimitiveRoot p : ZMod p); 1, 0] := by
    rw [coe_omegaGL, nonsplitCartanA_of_ne_two p hp, nonsplitCartanB_of_ne_two p hp]
  have hε₀ : (ZMod.leastPrimitiveRoot p : ZMod p) ≠ 0 := ZMod.leastPrimitiveRoot_ne_zero p
  have htr : g₂.val.trace = g₁.val.trace := by
    rw [← he]
    exact Matrix.trace_units_conj h g₁
  have hdet : g₂.val.det = g₁.val.det := by
    rw [← he]
    exact Matrix.det_units_conj h g₁
  rw [Matrix.trace_fin_two, Matrix.trace_fin_two, hg₁.1, hg₂.1] at htr
  rw [Matrix.det_fin_two, Matrix.det_fin_two, hg₁.1, hg₂.1, hg₁.2, hg₂.2] at hdet
  have h₀₀ : g₂ 0 0 = g₁ 0 0 :=
    mul_left_cancel₀ (two_ne_zero_of_ne_two p hp) (by linear_combination htr)
  have hb : (g₂ 1 0 - g₁ 1 0) * (g₂ 1 0 + g₁ 1 0) = 0 := by
    refine mul_left_cancel₀ hε₀ ?_
    rw [h₀₀] at hdet
    linear_combination -hdet
  have hexp (z : GL (Fin 2) (ZMod p)) (hz : z 1 1 = z 0 0 ∧
      z 0 1 = (ZMod.leastPrimitiveRoot p : ZMod p) * z 1 0) :
      z.val = z 0 0 • 1 + z 1 0 • (omegaGL p).val := by
    rw [hω]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hz.1, hz.2, mul_comm]
  have hm : h.val * (g₁ 0 0 • 1 + g₁ 1 0 • (omegaGL p).val) =
      (g₂ 0 0 • 1 + g₂ 1 0 • (omegaGL p).val) * h.val := by
    rw [← hexp g₁ hg₁, ← hexp g₂ hg₂, ← he, MulAut.conj_apply, ← Units.val_mul, ← Units.val_mul,
      inv_mul_cancel_right]
  rw [h₀₀, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul, add_right_inj, Matrix.mul_smul, Matrix.smul_mul] at hm
  rcases mul_eq_zero.mp hb with hb | hb
  · rw [sub_eq_zero.mp hb] at hm
    exact labelCn_le_labelNn p <| mem_labelCn_of_commute p hp <| smul_right_injective _ hne hm
  · have hb' : g₂ 1 0 = -g₁ 1 0 := eq_neg_of_add_eq_zero_left hb
    rw [hb', neg_smul, ← smul_neg] at hm
    have hm' : h.val * (omegaGL p).val = -((omegaGL p).val * h.val) :=
      smul_right_injective _ hne hm
    have hσω : (canonicalInvolutionGL (nonsplitCartanBasis p)).val * (omegaGL p).val =
        -((omegaGL p).val * (canonicalInvolutionGL (nonsplitCartanBasis p)).val) := by
      rw [coe_canonicalInvolutionGL_of_ne_two p hp, hω]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have hgσ : h * canonicalInvolutionGL (nonsplitCartanBasis p) ∈ labelCn p := by
      refine mem_labelCn_of_commute p hp ?_
      rw [Units.val_mul, Matrix.mul_assoc, hσω, Matrix.mul_neg, ← Matrix.mul_assoc, hm',
        Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [← mul_one h, ← canonicalInvolutionGL_mul_self (nonsplitCartanBasis p), ← mul_assoc]
    exact mul_mem (labelCn_le_labelNn p hgσ) (canonicalInvolutionGL_mem_extendedCartanSubgroup _)

lemma mulAut_conj_scalar (P : GL (Fin 2) (ZMod p)) (u : (ZMod p)ˣ) :
    MulAut.conj P (scalar (Fin 2) u) = scalar (Fin 2) u := by
  rw [MulAut.conj_apply, ← scalar_commute, mul_inv_cancel_right]

lemma pow_natCard_mem_center (hg : g ∈ H) :
    g ^ Nat.card H ∈ Subgroup.center (GL (Fin 2) (ZMod p)) := by
  have h₁ : (⟨g, hg⟩ : H) ^ Nat.card H = 1 := pow_card_eq_one'
  have h₂ : g ^ Nat.card H = 1 := congrArg Subtype.val h₁
  exact h₂ ▸ one_mem _

lemma mem_center_of_mulAut_conj_mem {P : GL (Fin 2) (ZMod p)}
    (h : MulAut.conj P g ∈ Subgroup.center (GL (Fin 2) (ZMod p))) :
    g ∈ Subgroup.center (GL (Fin 2) (ZMod p)) := by
  have h₁ : P⁻¹ * MulAut.conj P g * P⁻¹⁻¹ ∈ Subgroup.center (GL (Fin 2) (ZMod p)) :=
    (inferInstance : (Subgroup.center (GL (Fin 2) (ZMod p))).Normal).conj_mem _ h P⁻¹
  simpa [mul_assoc] using h₁

lemma natCast_natCard_ne_zero (hH : ¬p ∣ Nat.card H) : (Nat.card H : ZMod p) ≠ 0 :=
  fun h ↦ hH ((ZMod.natCast_eq_zero_iff _ p).mp h)

/-- **A subgroup of `GL₂(𝔽_p)` of order prime to `p` with cyclic projective image is conjugate to a
subgroup of a Cartan subgroup**, for odd `p`. -/
lemma exists_le_cartan_of_isCyclic (hp : p ≠ 2) (hH : ¬p ∣ Nat.card H)
    (hc : IsCyclic (projectiveImage H)) :
    (∃ K ∈ subgroupConjClass p H, K ≤ diagonalTorus (ZMod p) 2) ∨
      ∃ K ∈ subgroupConjClass p H, K ≤ labelCn p := by
  rcases hc.exists_generator with ⟨g', hg'⟩
  rcases g'.2 with ⟨g, hg, hgg'⟩
  have hgen (h : GL (Fin 2) (ZMod p)) (hh : h ∈ H) :
      ∃ (k : ℤ) (u : (ZMod p)ˣ), h = g ^ k * scalar (Fin 2) u := by
    rcases Subgroup.mem_zpowers_iff.mp (hg' ⟨_, Subgroup.mem_map_of_mem _ hh⟩) with ⟨k, hk⟩
    have hk' : ProjGenLinGroup.mk (g ^ k) = ProjGenLinGroup.mk h := by
      rw [map_zpow, hgg']
      exact congrArg Subtype.val hk
    rcases ProjGenLinGroup.mk_eq_mk_iff.mp hk' with ⟨u, hu⟩
    exact ⟨k, u, hu.symm⟩
  rcases exists_conj_mem_cartan hp (natCast_natCard_ne_zero hH) (pow_natCard_mem_center hg) with
    ⟨P, hP | hP⟩
  · refine Or.inl ⟨_, map_conj_mem_subgroupConjClass H P⁻¹, ?_⟩
    rintro - ⟨h, hh, rfl⟩
    rcases hgen h hh with ⟨k, u, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_zpow, mulAut_conj_scalar]
    exact mul_mem (zpow_mem hP k) (scalar_mem_diagonalTorus u)
  · refine Or.inr ⟨_, map_conj_mem_subgroupConjClass H P⁻¹, ?_⟩
    rintro - ⟨h, hh, rfl⟩
    rcases hgen h hh with ⟨k, u, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_zpow, mulAut_conj_scalar]
    exact mul_mem (zpow_mem hP k) (scalar_mem_labelCn hp u)

lemma conj_dihedralGroup_r_one {n : ℕ} (y : DihedralGroup n) :
    y * .r 1 * y⁻¹ = .r 1 ∨ y * .r 1 * y⁻¹ = (.r 1)⁻¹ := by
  rcases y with i | i
  · refine Or.inl ?_
    simp
  · refine Or.inr ?_
    simp

lemma dihedralGroup_r_one_ne_one {n : ℕ} (hn : 2 ≤ n) : (DihedralGroup.r 1 : DihedralGroup n) ≠ 1 :=
  fun hr ↦ by
    have h₁ : orderOf (DihedralGroup.r 1 : DihedralGroup n) = n := DihedralGroup.orderOf_r_one
    rw [hr, orderOf_one] at h₁
    omega

lemma mulAut_conj_toMonoidHom_mulAut_conj (P h : GL (Fin 2) (ZMod p)) :
    MulAut.conj ((MulAut.conj P).toMonoidHom h) (MulAut.conj P g) =
      MulAut.conj P (h * g * h⁻¹) := by
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul, map_inv]

/-- **A subgroup of `GL₂(𝔽_p)` of order prime to `p` with dihedral projective image is conjugate to
a subgroup of the normalizer of a Cartan subgroup**, for odd `p`: a lift of the rotation of the
dihedral group is conjugate into a Cartan subgroup, and is mapped by every element of the subgroup
to its inverse or to itself, up to scalars. -/
lemma exists_le_cartan_normalizer_of_dihedral (hp : p ≠ 2) (hH : ¬p ∣ Nat.card H) {n : ℕ}
    (hn : 2 ≤ n) (e : projectiveImage H ≃* DihedralGroup n) :
    (∃ K ∈ subgroupConjClass p H, K ≤ labelNs p) ∨ ∃ K ∈ subgroupConjClass p H, K ≤ labelNn p := by
  rcases (e.symm (.r 1)).2 with ⟨g, hg, hgr⟩
  have hgc : g ∉ Subgroup.center (GL (Fin 2) (ZMod p)) := by
    intro hgc
    have h₁ : e.symm (.r 1) = 1 := Subtype.ext <| hgr.symm.trans <|
      ProjGenLinGroup.mk_eq_one.mpr hgc
    exact dihedralGroup_r_one_ne_one hn (e.symm.map_eq_one_iff.mp h₁)
  have hconj (h : GL (Fin 2) (ZMod p)) (hh : h ∈ H) :
      ∃ (k : ℤ) (u : (ZMod p)ˣ), h * g * h⁻¹ = g ^ k * scalar (Fin 2) u := by
    let z : DihedralGroup n := e ⟨_, Subgroup.mem_map_of_mem _ hh⟩
    have hmk : ProjGenLinGroup.mk (h * g * h⁻¹) =
        ((e.symm (z * .r 1 * z⁻¹) : projectiveImage H) : PGL(Fin 2, ZMod p)) := by
      simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, z, Subgroup.coe_mul, Subgroup.coe_inv,
        hgr]
    rcases conj_dihedralGroup_r_one z with hz | hz
    · rw [hz] at hmk
      rcases ProjGenLinGroup.mk_eq_mk_iff.mp (hmk.trans hgr.symm).symm with ⟨u, hu⟩
      exact ⟨1, u, by rw [zpow_one]; exact hu.symm⟩
    · rw [hz, map_inv, Subgroup.coe_inv] at hmk
      have hmk' : ProjGenLinGroup.mk g⁻¹ = ProjGenLinGroup.mk (h * g * h⁻¹) := by
        rw [hmk, map_inv, hgr]
      rcases ProjGenLinGroup.mk_eq_mk_iff.mp hmk' with ⟨u, hu⟩
      exact ⟨-1, u, by simpa using hu.symm⟩
  rcases exists_conj_mem_cartan hp (natCast_natCard_ne_zero hH) (pow_natCard_mem_center hg) with
    ⟨P, hP | hP⟩
  · refine Or.inl ⟨_, map_conj_mem_subgroupConjClass H P⁻¹, ?_⟩
    rintro - ⟨h, hh, rfl⟩
    rcases hconj h hh with ⟨k, u, hk⟩
    have hne : (MulAut.conj P⁻¹ g) 0 0 ≠ (MulAut.conj P⁻¹ g) 1 1 := fun h₀ ↦ hgc <|
      mem_center_of_mulAut_conj_mem <| mem_center_iff_entries.mpr
        ⟨mem_diagonalTorus_iff.mp hP (by decide), mem_diagonalTorus_iff.mp hP (by decide), h₀⟩
    refine mem_labelNs_of_mulAut_conj_mem hP ?_ hne
    rw [mulAut_conj_toMonoidHom_mulAut_conj, hk, map_mul, map_zpow, mulAut_conj_scalar]
    exact mul_mem (zpow_mem hP k) (scalar_mem_diagonalTorus u)
  · refine Or.inr ⟨_, map_conj_mem_subgroupConjClass H P⁻¹, ?_⟩
    rintro - ⟨h, hh, rfl⟩
    rcases hconj h hh with ⟨k, u, hk⟩
    have hP' : (MulAut.conj P⁻¹ g) 1 1 = (MulAut.conj P⁻¹ g) 0 0 ∧ (MulAut.conj P⁻¹ g) 0 1 =
        (ZMod.leastPrimitiveRoot p : ZMod p) * (MulAut.conj P⁻¹ g) 1 0 :=
      (mem_labelCn_iff p hp).mp hP
    have hne : (MulAut.conj P⁻¹ g) 1 0 ≠ 0 := fun h₀ ↦ hgc <| mem_center_of_mulAut_conj_mem <|
      mem_center_iff_entries.mpr ⟨by rw [hP'.2, h₀, mul_zero], h₀, hP'.1.symm⟩
    refine mem_labelNn_of_mulAut_conj_mem hp hP ?_ hne
    rw [mulAut_conj_toMonoidHom_mulAut_conj, hk, map_mul, map_zpow, mulAut_conj_scalar]
    exact mul_mem (zpow_mem hP k) (scalar_mem_labelCn hp u)

variable (H) in
/-- The image in `PGL₂(𝔽_p)` of a conjugate of a subgroup of `GL₂(𝔽_p)` is isomorphic to that of the
subgroup. -/
noncomputable def projectiveImageMapConjEquiv (P : GL (Fin 2) (ZMod p)) :
    projectiveImage (H.map (MulAut.conj P).toMonoidHom) ≃* projectiveImage H :=
  (MulEquiv.subgroupCongr (by
    rw [projectiveImage, projectiveImage, Subgroup.map_map, Subgroup.map_map]
    congr 1)).trans
    ((MulAut.conj (ProjGenLinGroup.mk P)).subgroupMap (projectiveImage H)).symm

lemma HasDihedralImage.of_mem_subgroupConjClass (hK : K ∈ subgroupConjClass p H)
    (hH : HasDihedralImage p H) : HasDihedralImage p K := by
  rcases hK with ⟨g, rfl⟩
  rcases hH with ⟨n, hn, ⟨e⟩⟩
  refine ⟨n, hn, ⟨?_⟩⟩
  have hg : (fun x ↦ g • x) H = H.map (MulAut.conj (ConjAct.ofConjAct g)).toMonoidHom := by
    rw [map_conj_eq_smul, ConjAct.toConjAct_ofConjAct]
  exact (MulEquiv.subgroupCongr (congrArg projectiveImage hg)).trans
    ((projectiveImageMapConjEquiv H _).trans e)

variable (H) in
/-- **Dickson's classification of the subgroups of `GL₂(𝔽_p)`** (LMFDB
`ec.galois_rep_modell_image`; Proposition 3.1 of Sutherland, arXiv:1504.07618v7): every subgroup of
`GL₂(𝔽_p)` satisfies the condition of one of Sutherland's classes `G`, `B`, `Cs`, `Cn`, `Ns`, `Nn`,
`A4`, `S4`, `A5`. -/
lemma exists_holds : ∃ S : SutherlandClass, S.Holds p H := by
  by_cases hpH : p ∣ Nat.card H
  · rcases exists_prime_orderOf_dvd_card' p hpH with ⟨x, hx⟩
    rcases holds_G_or_holds_B_of_orderOf_eq x.2 ((Subgroup.orderOf_coe x).trans hx) with h | h
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩
  rcases eq_or_ne p 2 with rfl | hp
  · have h6 : Nat.card H ∣ 6 := by
      have h₁ : Nat.card H ∣ Nat.card (GL (Fin 2) (ZMod 2)) := Subgroup.card_subgroup_dvd_card H
      rwa [natCard_GL_fin_two_eq_sq_sub_one_mul, ZMod.card] at h₁
    have hcard : Nat.card H = 1 ∨ Nat.card H = 3 := by
      have hle : Nat.card H ≤ 6 := Nat.le_of_dvd (by norm_num) h6
      interval_cases hc : Nat.card H <;> simp_all
    rcases hcard with h₁ | h₃
    · refine ⟨.Cs, H, mem_orbit_self H, ?_⟩
      rw [Subgroup.card_eq_one.mp h₁]
      exact bot_le
    · by_cases hCs : ∃ K ∈ subgroupConjClass 2 H, K ≤ diagonalTorus (ZMod 2) 2
      · exact ⟨.Cs, hCs⟩
      refine ⟨.Cn, ⟨H, mem_orbit_self H, ?_⟩, hCs⟩
      have hcard : Nat.card H * H.index = 6 := by
        rw [Subgroup.card_mul_index, natCard_GL_fin_two_eq_sq_sub_one_mul, ZMod.card]
        rfl
      rw [h₃] at hcard
      rw [labelCn_two_eq_of_index_eq_two (by omega : H.index = 2)]
  by_cases hker : (det : GL (Fin 2) (ZMod p) →* (ZMod p)ˣ).ker ≤ H
  · exact ⟨.G, H, mem_orbit_self H, hker⟩
  rcases classification_projectiveImage hpH with hc | ⟨n, hn, ⟨e⟩⟩ | hA | hS | hA
  · rcases exists_le_cartan_of_isCyclic hp hpH hc with hK | hK
    · exact ⟨.Cs, hK⟩
    · by_cases hCs : ∃ K ∈ subgroupConjClass p H, K ≤ diagonalTorus (ZMod p) 2
      · exact ⟨.Cs, hCs⟩
      · exact ⟨.Cn, hK, hCs⟩
  · have hdih : HasDihedralImage p H := ⟨n, hn, ⟨e⟩⟩
    rcases exists_le_cartan_normalizer_of_dihedral hp hpH hn e with ⟨K, hK, hle⟩ | ⟨K, hK, hle⟩
    · exact ⟨.Ns, K, hK, hle, hdih.of_mem_subgroupConjClass hK⟩
    · by_cases hNs : ∃ K ∈ subgroupConjClass p H, K ≤ labelNs p
      · rcases hNs with ⟨K', hK', hle'⟩
        exact ⟨.Ns, K', hK', hle', hdih.of_mem_subgroupConjClass hK'⟩
      · exact ⟨.Nn, ⟨K, hK, hle, hdih.of_mem_subgroupConjClass hK⟩, hNs⟩
  · exact ⟨.A4, H, mem_orbit_self H, hA, hker⟩
  · exact ⟨.S4, H, mem_orbit_self H, hS, hker⟩
  · exact ⟨.A5, H, mem_orbit_self H, hA, hker⟩

variable (H) in
/-- **Every subgroup of `GL₂(𝔽_p)` has a Sutherland class** (LMFDB `ec.galois_rep_modell_image`):
the first in his list whose condition it satisfies. -/
lemma exists_hasSutherlandClass : ∃ S : SutherlandClass, HasSutherlandClass p H S := by
  classical
  have hex : ∃ n : ℕ, ∃ S : SutherlandClass, S.toNat = n ∧ S.Holds p H := by
    rcases exists_holds H with ⟨S, hS⟩
    exact ⟨_, S, rfl, hS⟩
  rcases Nat.find_spec hex with ⟨S, hS, hhS⟩
  refine ⟨S, hhS, fun T hT hhT ↦ Nat.find_min hex (m := T.toNat) (hS ▸ hT) ⟨T, rfl, hhT⟩⟩

/-- **The Sutherland class of a subgroup of `GL₂(𝔽_p)` is unique.** -/
lemma HasSutherlandClass.eq {S T : SutherlandClass} (hS : HasSutherlandClass p H S)
    (hT : HasSutherlandClass p H T) : S = T := by
  rcases lt_trichotomy S.toNat T.toNat with h | h | h
  · exact absurd hS.1 (hT.2 _ h)
  · exact SutherlandClass.toNat_injective h
  · exact absurd hT.1 (hS.2 _ h)

end Matrix.GeneralLinearGroup
