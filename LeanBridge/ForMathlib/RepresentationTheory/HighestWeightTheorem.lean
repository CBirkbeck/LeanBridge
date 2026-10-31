import LeanBridge.ForMathlib.LinearAlgebra.Matrix.BigCell
import LeanBridge.ForMathlib.RepresentationTheory.HighestWeight
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.Topology.Algebra.MvPolynomial
import TauCeti.RepresentationTheory.ClassicalGroups.Weight.CentralCharacter

/-!
# The theorem of the highest weight for `GL(n, ℂ)`

An irreducible rational representation `ρ` of `GL(n, ℂ)` has a highest weight vector: a nonzero
weight vector fixed by the upper unitriangular matrices (`Representation.IsGLHighestWeightVector`).
The LMFDB knowls `repn.highest.weight` and `repn.irrep.gl` rest on the theorem of the highest
weight: the line of such a vector and its weight are unique, the weight `λ` is dominant, and `ρ`
is isomorphic to the rational Weyl module `V_λ` (Tau Ceti's `TauCeti.rationalWeylRep`) for a
unique dominant `λ`. This file proves it.

The proof is algebraic. The lower unitriangular, invertible diagonal and upper unitriangular
matrices multiply to the big cell `B⁻ B`, which is Zariski dense
(`Matrix.eq_zero_of_forall_eval_mul_diagonal_mul`), so a rational function on `GL(n, ℂ)` vanishing
on it is zero. A highest weight vector `v` of weight `λ` is fixed by every upper unitriangular
matrix, and if `ψ` is the coordinate of the `λ`-weight component with `ψ v = 1`, then
`ψ (ρ (L t U) v) = λ(t)` on the big cell: conjugating a lower unitriangular `L` by the torus
contracts it to `1` along a polynomial curve. So for highest weight vectors `v` of `ρ` and `w` of
`σ` of the same weight, `g ↦ ψ (ρ g v) - ψ' (σ g w)` vanishes, and the span of the pairs
`(ρ g v, σ g w)` is the graph of an isomorphism `ρ ≃ σ` sending `v` to `w`. The rational Weyl
module `V_λ` is rational (`TauCeti.isRationalRep_rationalWeylRep`) and has a highest weight vector
of weight `λ`, which gives the isomorphism with `V_λ`; Schur's lemma gives the uniqueness of the
line, and the dominance order on the weights of `V_λ` the uniqueness of the weight.

As stated in the LMFDB, the uniqueness in `repn.highest.weight` fails, and the bijection in
`repn.irrep.gl` is wrong: `ρ` must be rational (`|det|` is irreducible with no weight at all) and
`v₀` must be fixed by the upper unitriangular matrices (in `Sym²(ℂ²)`, `e₁²` and `e₁e₂` both
satisfy the knowl's condition, with the dominant weights `(2, 0)` and `(1, 1)`).

## Main results

* `TauCeti.isRationalRep_rationalWeylRep`: the rational Weyl module `V_λ` is rational.
* `Matrix.GeneralLinearGroup.eq_zero_of_forall_mul_diagGL_mul`: a rational function on
  `GL(n, ℂ)` vanishing on the big cell is zero.
* `Representation.apply_eq_self_of_isUpperTriangular`: a vector fixed by the upper unitriangular
  transvections is fixed by every upper unitriangular matrix.
* `Representation.IsGLHighestWeightVector.exists_intertwiningMap_apply_eq` and
  `Representation.nonempty_equiv_of_isGLHighestWeightVector`: irreducible rational
  representations with highest weight vectors of the same weight are isomorphic.
* `Representation.nonempty_equiv_rationalWeylRep_iff_eq_highestWeight` and
  `Representation.existsUnique_nonempty_equiv_rationalWeylRep` (LMFDB `repn.irrep.gl`): an
  irreducible rational representation is isomorphic to `V_λ` exactly for `λ` its highest weight.
* `Representation.IsGLHighestWeightVector.eq_highestWeight` and
  `Representation.IsGLHighestWeightVector.mem_span_singleton` (LMFDB `repn.highest.weight`): the
  highest weight vectors of an irreducible rational representation span a single line, of weight
  `Representation.highestWeight`; together, `Representation.existsUnique_isGLHighestWeightVector`:
  the line and the weight exist and are unique.
-/

open TauCeti Matrix GeneralLinearGroup Module

variable {n : ℕ} {W V : Type*} [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ (GL (Fin n) ℂ) W} {σ : Representation ℂ (GL (Fin n) ℂ) V}
  {l l' : Fin n → ℤ} {μ : DominantWeight n} {φ ψ : W →ₗ[ℂ] ℂ} {v v' : W} {w : V}
  {g : GL (Fin n) ℂ}

namespace TauCeti.IsRationalRep

variable (φ v) in
lemma apply_mem_rationalFunctions (h : IsRationalRep ρ) :
    (fun g ↦ φ (ρ g v)) ∈ rationalFunctions ℂ n := by
  have : Module.Finite ℂ W := h.finite
  let b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W := Module.finBasis ℂ W
  have hb : ∀ i j, (fun g ↦ LinearMap.toMatrix b b (ρ g) i j) ∈ rationalFunctions ℂ n :=
    (isRationalRep_iff_forall_mem_rationalFunctions b).mp h
  have key : (fun g ↦ φ (ρ g v)) =
      ∑ p, ∑ q, (φ (b p) * b.repr v q) • fun g ↦ LinearMap.toMatrix b b (ρ g) p q := by
    funext g
    conv_lhs => rw [← b.sum_repr (ρ g v)]
    simp only [map_sum, map_smul, smul_eq_mul, ← LinearMap.toMatrix_mulVec_repr b b, mulVec,
      dotProduct, Finset.sum_mul, Finset.sum_apply, Pi.smul_apply]
    exact Finset.sum_congr rfl fun p _ ↦ Finset.sum_congr rfl fun q _ ↦ by ring1
  rw [key]
  exact Subalgebra.sum_mem _ fun p _ ↦ Subalgebra.sum_mem _ fun q _ ↦
    Subalgebra.smul_mem _ (hb p q) _

lemma apply_apply_eq_zero_pow_mul (h : IsRationalRep ρ) (hv : v ∈ weightSpace ρ l)
    (hψ : ∀ t y, ψ (ρ (diagGL t) y) = (weightChar ℂ l' t : ℂ) * ψ y) {k : ℕ}
    (hk : ∑ i : Fin n, ((i : ℕ) : ℤ) * (l' i - l i) + k = 0)
    (hg : (g : Matrix (Fin n) (Fin n) ℂ).IsLowerTriangular)
    (hg1 : ∀ i, (g : Matrix (Fin n) (Fin n) ℂ) i i = 1) : ψ (ρ g v) = 0 ^ k * ψ v := by
  rcases mem_rationalFunctions_iff_inv.1 (h.apply_mem_rationalFunctions ψ v) with ⟨P, m, hP⟩
  let N : ℂ → Matrix (Fin n) (Fin n) ℂ :=
    fun s ↦ of fun i j ↦ s ^ ((i : ℕ) - j) * (g : Matrix (Fin n) (Fin n) ℂ) i j
  have hN (s : ℂ) (hs : s ≠ 0) : s ^ k * MvPolynomial.eval (fun p ↦ N s p.1 p.2) P = ψ (ρ g v) := by
    let t : Fin n → ℂˣ := fun i ↦ Units.mk0 s hs ^ (i : ℕ)
    have hχ (ν : Fin n → ℤ) :
        weightChar ℂ ν t = Units.mk0 s hs ^ ∑ i : Fin n, ((i : ℕ) : ℤ) * ν i := by
      rw [weightChar_apply, torusCharacter_def, ← Finset.prod_zpow_eq_zpow_sum]
      exact Finset.prod_congr rfl fun i _ ↦ by rw [zpow_mul, zpow_natCast]
    have hc : ((diagGL t * g * (diagGL t)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = N s := by
      ext i j
      rw [← map_inv, Units.val_mul, Units.val_mul, diagGL_coe, diagGL_coe, mul_diagonal,
        diagonal_mul]
      rcases le_or_gt j i with hji | hij
      · simp [N, t, pow_sub₀ s hs (Fin.le_def.1 hji)]
        ring1
      · simp [N, hg hij]
    have hdet : (N s).det = 1 := by
      rw [det_of_isLowerTriangular (N s) fun i j hij ↦ ?_]
      · simp [N, hg1]
      · simp [N, hg hij]
    have h1 :
        ψ (ρ (diagGL t * g * (diagGL t)⁻¹) v) = MvPolynomial.eval (fun p ↦ N s p.1 p.2) P := by
      rw [hP, hc, hdet, one_pow, inv_one, one_mul]
    rw [← h1, map_mul, map_mul, End.mul_apply, End.mul_apply, hψ, ← map_inv,
      apply_of_mem_weightSpace hv, map_smul, map_smul, smul_eq_mul, ← mul_assoc, ← mul_assoc,
      map_inv, hχ, hχ]
    convert one_mul (ψ (ρ g v)) using 2
    have hsk : s ^ k = ((Units.mk0 s hs ^ k : ℂˣ) : ℂ) := by
      simp
    have hab :
        (k : ℤ) + ∑ i : Fin n, ((i : ℕ) : ℤ) * l' i + -∑ i : Fin n, ((i : ℕ) : ℤ) * l i = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib] at hk
      linarith
    rw [hsk, ← Units.val_mul, ← Units.val_mul, ← zpow_natCast, ← zpow_add, ← zpow_neg, ← zpow_add,
      hab, zpow_zero, Units.val_one]
  have hc : Continuous fun s ↦ s ^ k * MvPolynomial.eval (fun p ↦ N s p.1 p.2) P :=
    (continuous_pow k).mul <| (MvPolynomial.continuous_eval P).comp <| continuous_pi fun p ↦
      (continuous_pow _).mul continuous_const
  have h0 : 0 ^ k * MvPolynomial.eval (fun p ↦ N 0 p.1 p.2) P = ψ (ρ g v) :=
    congrFun (hc.ext_on (dense_compl_singleton 0) continuous_const fun s hs ↦ hN s hs) 0
  have hN0 : N 0 = 1 := by
    ext i j
    rcases lt_trichotomy i j with hij | rfl | hij
    · simp [N, hg hij, one_apply_ne hij.ne]
    · simp [N, hg1]
    · simp [N, one_apply_ne hij.ne', Nat.sub_ne_zero_of_lt (Fin.lt_def.1 hij)]
  have h1 : ψ v = MvPolynomial.eval (fun p ↦ N 0 p.1 p.2) P := by
    simpa [hN0] using hP 1
  rw [← h0, h1]

lemma apply_apply_eq_of_isLowerTriangular (h : IsRationalRep ρ) (hv : v ∈ weightSpace ρ l)
    (hψ : ∀ t y, ψ (ρ (diagGL t) y) = (weightChar ℂ l t : ℂ) * ψ y)
    (hg : (g : Matrix (Fin n) (Fin n) ℂ).IsLowerTriangular)
    (hg1 : ∀ i, (g : Matrix (Fin n) (Fin n) ℂ) i i = 1) : ψ (ρ g v) = ψ v := by
  simpa using h.apply_apply_eq_zero_pow_mul hv hψ (k := 0) (by simp) hg hg1

lemma exists_apply_eq_one_forall_apply_diagGL (h : IsRationalRep ρ) (hv : v ∈ weightSpace ρ l)
    (hv0 : v ≠ 0) :
    ∃ ψ : W →ₗ[ℂ] ℂ, ψ v = 1 ∧ ∀ t y, ψ (ρ (diagGL t) y) = (weightChar ℂ l t : ℂ) * ψ y := by
  let K : Submodule ℂ W := ⨆ (μ) (_ : μ ≠ l), weightSpace ρ μ
  have hvK : v ∉ K := fun hK ↦ hv0 <|
    Submodule.disjoint_def.1 (iSupIndep_weightSpace weightChar_injective ρ l) v hv hK
  rcases K.exists_dual_map_eq_bot_of_notMem hvK inferInstance with ⟨f, hf, hfK⟩
  have hfK' (y : W) (hy : y ∈ K) : f y = 0 :=
    (Submodule.mem_bot ℂ).1 (hfK ▸ Submodule.mem_map_of_mem hy)
  refine ⟨(f v)⁻¹ • f, by simp [hf], fun t y ↦ ?_⟩
  have hy : y ∈ weightSpace ρ l ⊔ K := by
    rw [← iSup_split_single (weightSpace ρ) l, h.iSup_weightSpace_eq_top]
    trivial
  rcases Submodule.mem_sup.1 hy with ⟨a, ha, b, hb, rfl⟩
  have hKt : K ≤ K.comap (ρ (diagGL t)) := iSup₂_le fun μ hμ y hy ↦ Submodule.mem_comap.2 <|
    (apply_of_mem_weightSpace hy t).symm ▸
      le_iSup₂ (f := fun μ (_ : μ ≠ l) ↦ weightSpace ρ μ) μ hμ (Submodule.smul_mem _ _ hy)
  simp [apply_of_mem_weightSpace ha, hfK' b hb, hfK' _ (hKt hb)]
  ring1

lemma toRepresentation (h : IsRationalRep ρ) (ρ' : Subrepresentation ρ) :
    IsRationalRep ρ'.toRepresentation := by
  have : Module.Finite ℂ W := h.finite
  let b : Module.Basis (Fin (Module.finrank ℂ ρ'.toSubmodule)) ℂ ρ'.toSubmodule :=
    Module.finBasis ℂ ρ'.toSubmodule
  refine (isRationalRep_iff_forall_mem_rationalFunctions b).2 fun i j ↦ ?_
  rcases LinearMap.exists_extend (b.coord i) with ⟨φ, hφ⟩
  have key :
      (fun g ↦ LinearMap.toMatrix b b (ρ'.toRepresentation g) i j) = fun g ↦ φ (ρ g (b j)) := by
    funext g
    rw [LinearMap.toMatrix_apply, ← b.coord_apply, ← hφ]
    rfl
  rw [key]
  exact h.apply_mem_rationalFunctions φ _

lemma charTwist (h : IsRationalRep ρ) (m : ℤ) :
    IsRationalRep (ρ.charTwist (GeneralLinearGroup.det ^ m)) := by
  have : Module.Finite ℂ W := h.finite
  let b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W := Module.finBasis ℂ W
  refine (isRationalRep_iff_forall_mem_rationalFunctions b).2 fun i j ↦ ?_
  have key : (fun g ↦ LinearMap.toMatrix b b (ρ.charTwist (GeneralLinearGroup.det ^ m) g) i j) =
      (fun g ↦ ((GeneralLinearGroup.det g ^ m : ℂˣ) : ℂ)) *
        fun g ↦ LinearMap.toMatrix b b (ρ g) i j := by
    funext g
    simp
  rw [key]
  exact mul_mem (det_zpow_mem_rationalFunctions m)
    ((isRationalRep_iff_forall_mem_rationalFunctions b).1 h i j)

end TauCeti.IsRationalRep

variable (μ) in
/-- **The rational Weyl module `V_λ` is rational**: it is the twist by `det ^ λₙ` of a
subrepresentation of a tensor power of the standard representation, and the matrix coefficients
of a subrepresentation and of a twist by a power of the determinant are rational functions. -/
lemma TauCeti.isRationalRep_rationalWeylRep :
    IsRationalRep (W := (weylModuleOfShape ℂ n μ.detShiftShape).toSubmodule)
      (rationalWeylRep ℂ n μ) := by
  rw [rationalWeylRep_def]
  exact ((isPolynomialRep_tensorPowerRep n _).isRationalRep.toRepresentation _).charTwist _

namespace Matrix.GeneralLinearGroup

/-- **A rational function on `GL(n, ℂ)` vanishing on the big cell is zero**: its numerator vanishes
on every product `L * diagonal d * U` of a lower unitriangular, an invertible diagonal and an
upper unitriangular matrix, and these products are Zariski dense
(`Matrix.eq_zero_of_forall_eval_mul_diagonal_mul`). -/
lemma eq_zero_of_forall_mul_diagGL_mul {f : GL (Fin n) ℂ → ℂ} (hf : f ∈ rationalFunctions ℂ n)
    (h : ∀ gL gU : GL (Fin n) ℂ, (gL : Matrix (Fin n) (Fin n) ℂ).IsLowerTriangular →
      (∀ i, (gL : Matrix (Fin n) (Fin n) ℂ) i i = 1) →
        (gU : Matrix (Fin n) (Fin n) ℂ).IsUpperTriangular →
          (∀ i, (gU : Matrix (Fin n) (Fin n) ℂ) i i = 1) → ∀ t, f (gL * diagGL t * gU) = 0) :
    f = 0 := by
  rcases mem_rationalFunctions_iff_inv.1 hf with ⟨P, m, hP⟩
  have hP0 : P = 0 := by
    refine eq_zero_of_forall_eval_mul_diagonal_mul fun L U hL hL1 hU hU1 d hd ↦ ?_
    have hLdet : L.det ≠ 0 := by
      rw [det_of_isLowerTriangular L hL]
      simp [hL1]
    have hUdet : U.det ≠ 0 := by
      rw [det_of_isUpperTriangular hU]
      simp [hU1]
    let t : Fin n → ℂˣ := fun i ↦ Units.mk0 (d i) (hd i)
    have hg : ((mkOfDetNeZero L hLdet * diagGL t * mkOfDetNeZero U hUdet : GL (Fin n) ℂ) :
        Matrix (Fin n) (Fin n) ℂ) = L * diagonal d * U := by
      rw [Units.val_mul, Units.val_mul, diagGL_coe]
      rfl
    have h1 : ((L * diagonal d * U).det ^ m)⁻¹ *
        MvPolynomial.eval (fun p ↦ (L * diagonal d * U) p.1 p.2) P = 0 := by
      rw [← hg, ← hP, h _ _ hL hL1 hU hU1 t]
    refine (mul_eq_zero.1 h1).resolve_left (inv_ne_zero (pow_ne_zero _ ?_))
    rw [det_mul, det_mul, det_diagonal]
    exact mul_ne_zero (mul_ne_zero hLdet (Finset.prod_ne_zero_iff.2 fun i _ ↦ hd i)) hUdet
  funext g
  rw [hP g, hP0, map_zero, mul_zero, Pi.zero_apply]

end Matrix.GeneralLinearGroup

namespace Representation

/-- **A vector fixed by the upper unitriangular transvections is fixed by every upper
unitriangular matrix.** Left multiplication by the transvection `xᵢⱼ(-gᵢⱼ)`, for `i` the lowest row
of `g` with a nonzero entry above the diagonal, clears that entry and changes no other, so `g` is a
product of upper unitriangular transvections. -/
lemma apply_eq_self_of_isUpperTriangular
    (hv : ∀ (i j : Fin n) (hij : i < j) (c : ℂ), ρ (transvectionUnit hij.ne c) v = v)
    (hg : (g : Matrix (Fin n) (Fin n) ℂ).IsUpperTriangular)
    (hg1 : ∀ i, (g : Matrix (Fin n) (Fin n) ℂ) i i = 1) : ρ g v = v := by
  classical
  induction hk : (Finset.univ.filter fun p : Fin n × Fin n ↦
      p.1 < p.2 ∧ (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2 ≠ 0).card using Nat.strong_induction_on
      generalizing g with
  | _ k ih =>
    rcases (Finset.univ.filter fun p : Fin n × Fin n ↦
        p.1 < p.2 ∧ (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2 ≠ 0).eq_empty_or_nonempty with hS | hS
    · have h1 (i j : Fin n) : (g : Matrix (Fin n) (Fin n) ℂ) i j = (1 : GL (Fin n) ℂ) i j := by
        rcases lt_trichotomy i j with hij | rfl | hij
        · by_contra hne
          exact Finset.eq_empty_iff_forall_notMem.1 hS (i, j)
            (by simpa [hij, one_apply_ne hij.ne] using hne)
        · simp [hg1]
        · simp [hg hij, one_apply_ne hij.ne']
      rw [GeneralLinearGroup.ext h1, map_one, End.one_apply]
    · rcases Finset.exists_max_image _ Prod.fst hS with ⟨⟨i, j⟩, hij, hmax⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hij
      have hrow (b : Fin n) :
          (g : Matrix (Fin n) (Fin n) ℂ) j b = (1 : Matrix (Fin n) (Fin n) ℂ) j b := by
        rcases lt_trichotomy b j with hb | rfl | hb
        · simp [hg hb, one_apply_ne hb.ne']
        · simp [hg1]
        · by_contra hne
          have hjb : j ≤ i := hmax (j, b) (by simpa [hb, one_apply_ne hb.ne] using hne)
          exact absurd hij.1 (not_lt.2 hjb)
      let g' : GL (Fin n) ℂ :=
        transvectionUnit hij.1.ne (-(g : Matrix (Fin n) (Fin n) ℂ) i j) * g
      have hg' (a b : Fin n) : (g' : Matrix (Fin n) (Fin n) ℂ) a b =
          if a = i ∧ b = j then 0 else (g : Matrix (Fin n) (Fin n) ℂ) a b := by
        rw [Units.val_mul, coe_transvectionUnit]
        by_cases ha : a = i
        · subst ha
          rw [transvection_mul_apply_same, hrow]
          by_cases hb : b = j
          · subst hb
            simp
          · simp [hb, one_apply_ne (Ne.symm hb)]
        · simp [ha]
      have hgg' : g = transvectionUnit hij.1.ne ((g : Matrix (Fin n) (Fin n) ℂ) i j) * g' := by
        rw [← mul_assoc, ← transvectionUnit_add, add_neg_cancel, transvectionUnit_zero, one_mul]
      have hrec : ρ g' v = v := ih _ ?_ ?_ ?_ rfl
      · rw [hgg', map_mul, End.mul_apply, hrec, hv i j hij.1]
      · have hS' : (Finset.univ.filter fun p : Fin n × Fin n ↦
            p.1 < p.2 ∧ (g' : Matrix (Fin n) (Fin n) ℂ) p.1 p.2 ≠ 0) =
            (Finset.univ.filter fun p : Fin n × Fin n ↦
              p.1 < p.2 ∧ (g : Matrix (Fin n) (Fin n) ℂ) p.1 p.2 ≠ 0).erase (i, j) := by
          ext ⟨a, b⟩
          by_cases hab : a = i ∧ b = j
          · rcases hab with ⟨rfl, rfl⟩
            simp [hg']
          · simp [hg', hab]
            exact fun _ _ ha hb ↦ hab ⟨ha, hb⟩
        rw [hS', ← hk]
        exact Finset.card_erase_lt_of_mem (by simpa using hij)
      · intro a b hab
        rw [hg']
        split_ifs
        · rfl
        · exact hg hab
      · intro a
        rw [hg']
        split_ifs with h
        · exact absurd (h.1.symm.trans h.2) hij.1.ne
        · exact hg1 a

variable (φ) in
lemma IsGLHighestWeightVector.apply_mul_diagGL_mul (hv : ρ.IsGLHighestWeightVector v l)
    (gL : GL (Fin n) ℂ) {gU : GL (Fin n) ℂ} (hU : (gU : Matrix (Fin n) (Fin n) ℂ).IsUpperTriangular)
    (hU1 : ∀ i, (gU : Matrix (Fin n) (Fin n) ℂ) i i = 1) (t : Fin n → ℂˣ) :
    φ (ρ (gL * diagGL t * gU) v) = weightChar ℂ l t * φ (ρ gL v) := by
  rw [map_mul, map_mul, End.mul_apply, End.mul_apply,
    apply_eq_self_of_isUpperTriangular hv.2.2 hU hU1, apply_of_mem_weightSpace hv.2.1, map_smul,
    map_smul, smul_eq_mul]

variable (g) in
lemma apply_apply_eq_of_isGLHighestWeightVector (hρ : IsRationalRep ρ) (hσ : IsRationalRep σ)
    (hv : ρ.IsGLHighestWeightVector v l) (hw : σ.IsGLHighestWeightVector w l)
    (hψ : ∀ t y, ψ (ρ (diagGL t) y) = (weightChar ℂ l t : ℂ) * ψ y) {ψ' : V →ₗ[ℂ] ℂ}
    (hψ' : ∀ t y, ψ' (σ (diagGL t) y) = (weightChar ℂ l t : ℂ) * ψ' y) (hψψ' : ψ v = ψ' w) :
    ψ (ρ g v) = ψ' (σ g w) := by
  have h : (fun g ↦ ψ (ρ g v)) - (fun g ↦ ψ' (σ g w)) = 0 :=
    eq_zero_of_forall_mul_diagGL_mul (sub_mem (hρ.apply_mem_rationalFunctions ψ v)
      (hσ.apply_mem_rationalFunctions ψ' w)) fun gL gU hL hL1 hU hU1 t ↦ by
        rw [Pi.sub_apply, hv.apply_mul_diagGL_mul ψ gL hU hU1, hw.apply_mul_diagGL_mul ψ' gL hU hU1,
          hρ.apply_apply_eq_of_isLowerTriangular hv.2.1 hψ hL hL1,
          hσ.apply_apply_eq_of_isLowerTriangular hw.2.1 hψ' hL hL1, hψψ', sub_self]
  exact sub_eq_zero.1 (congrFun h g)

variable [IsIrreducible ρ] [IsIrreducible σ]

/-- **Highest weight vectors of the same weight in irreducible rational representations
correspond under an intertwining map.** With `ψ` and `ψ'` the coordinates of the weight components
of `v` and `w`, the function `g ↦ ψ (ρ g v) - ψ' (σ g w)` is rational and vanishes on the big cell,
so the span of the pairs `(ρ g v, σ g w)` meets `0 × V` and `W × 0` trivially: it is the graph of
an intertwining map sending `v` to `w`. -/
lemma IsGLHighestWeightVector.exists_intertwiningMap_apply_eq (hρ : IsRationalRep ρ)
    (hσ : IsRationalRep σ) (hv : ρ.IsGLHighestWeightVector v l)
    (hw : σ.IsGLHighestWeightVector w l) : ∃ f : IntertwiningMap ρ σ, f v = w := by
  rcases hρ.exists_apply_eq_one_forall_apply_diagGL hv.2.1 hv.1 with ⟨ψ, hψv, hψ⟩
  rcases hσ.exists_apply_eq_one_forall_apply_diagGL hw.2.1 hw.1 with ⟨ψ', hψw, hψ'⟩
  let Γ : Submodule ℂ (W × V) := Submodule.span ℂ (Set.range fun g ↦ (ρ g v, σ g w))
  have hΓ (g : GL (Fin n) ℂ) (x : W × V) (hx : x ∈ Γ) : (ρ g x.1, σ g x.2) ∈ Γ := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp⟩
    | zero =>
      rw [Prod.fst_zero, Prod.snd_zero, map_zero, map_zero]
      exact Γ.zero_mem
    | add y z _ _ hy hz => simpa using Γ.add_mem hy hz
    | smul c y _ hy => simpa using Γ.smul_mem c hy
  have hΛ (x : W × V) (hx : x ∈ Γ) : ψ x.1 = ψ' x.2 := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ⟨g, rfl⟩
      exact apply_apply_eq_of_isGLHighestWeightVector g hρ hσ hv hw hψ hψ' (hψv.trans hψw.symm)
    | zero => simp
    | add y z _ _ hy hz => simp [hy, hz]
    | smul c y _ hy => simp [hy]
  have hK (b : V) (hb : ((0 : W), b) ∈ Γ) : b = 0 := by
    let K : Subrepresentation σ :=
      ⟨Γ.comap (LinearMap.inr ℂ W V), fun g b hb ↦ by simpa using hΓ g _ hb⟩
    have hb' : b ∈ Γ.comap (LinearMap.inr ℂ W V) := hb
    rcases eq_bot_or_eq_top K with hK | hK
    · have hK' : Γ.comap (LinearMap.inr ℂ W V) = ⊥ := congrArg Subrepresentation.toSubmodule hK
      rw [hK'] at hb'
      exact (Submodule.mem_bot ℂ).1 hb'
    · have hK' : Γ.comap (LinearMap.inr ℂ W V) = ⊤ := congrArg Subrepresentation.toSubmodule hK
      have hw' : w ∈ Γ.comap (LinearMap.inr ℂ W V) := hK' ▸ Submodule.mem_top
      have h0w : ψ 0 = ψ' w := hΛ _ hw'
      simp [hψw] at h0w
  have hR (a : W) : ∃ b, (a, b) ∈ Γ := by
    let R : Subrepresentation ρ :=
      ⟨Γ.map (LinearMap.fst ℂ W V), fun g a ha ↦ by
        rcases ha with ⟨x, hx, rfl⟩
        exact ⟨_, hΓ g x hx, rfl⟩⟩
    rcases eq_bot_or_eq_top R with hR | hR
    · have hR' : Γ.map (LinearMap.fst ℂ W V) = ⊥ := congrArg Subrepresentation.toSubmodule hR
      have hv' : v ∈ Γ.map (LinearMap.fst ℂ W V) :=
        ⟨(v, w), Submodule.subset_span ⟨1, by simp⟩, rfl⟩
      rw [hR'] at hv'
      exact absurd ((Submodule.mem_bot ℂ).1 hv') hv.1
    · have hR' : Γ.map (LinearMap.fst ℂ W V) = ⊤ := congrArg Subrepresentation.toSubmodule hR
      have ha : a ∈ Γ.map (LinearMap.fst ℂ W V) := hR' ▸ Submodule.mem_top
      rcases ha with ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
  let p : Γ →ₗ[ℂ] W := LinearMap.fst ℂ W V ∘ₗ Γ.subtype
  have hp : Function.Bijective p := by
    refine ⟨fun x y hxy ↦ Subtype.ext <| Prod.ext hxy <| sub_eq_zero.1 <| hK _ ?_, fun a ↦ ?_⟩
    · have hxy' : (x : W × V).1 - (y : W × V).1 = 0 := sub_eq_zero.2 hxy
      rw [← hxy']
      exact Γ.sub_mem x.2 y.2
    · rcases hR a with ⟨b, hb⟩
      exact ⟨⟨(a, b), hb⟩, rfl⟩
  let e : Γ ≃ₗ[ℂ] W := LinearEquiv.ofBijective p hp
  have he (x : W × V) (hx : x ∈ Γ) : ((e.symm x.1 : Γ) : W × V) = x := by
    have h : e.symm x.1 = ⟨x, hx⟩ := e.symm_apply_eq.2 rfl
    rw [h]
  let f : W →ₗ[ℂ] V := LinearMap.snd ℂ W V ∘ₗ Γ.subtype ∘ₗ e.symm.toLinearMap
  have hfx (x : W × V) (hx : x ∈ Γ) : f x.1 = x.2 := by
    simp [f, he x hx]
  refine ⟨LinearMap.intertwiningMap_of_isIntertwiningMap ρ σ f fun g a ↦ ?_,
    hfx (v, w) (Submodule.subset_span ⟨1, by simp⟩)⟩
  have ha : ((e.symm a : Γ) : W × V).1 = a := e.apply_symm_apply a
  have h : f (ρ g ((e.symm a : Γ) : W × V).1) = σ g ((e.symm a : Γ) : W × V).2 :=
    hfx _ (hΓ g _ (e.symm a).2)
  rwa [ha] at h

/-- **Irreducible rational representations with highest weight vectors of the same weight are
isomorphic**: the intertwining map sending one highest weight vector to the other is nonzero,
hence bijective by Schur's lemma. -/
lemma nonempty_equiv_of_isGLHighestWeightVector (hρ : IsRationalRep ρ) (hσ : IsRationalRep σ)
    (hv : ρ.IsGLHighestWeightVector v l) (hw : σ.IsGLHighestWeightVector w l) :
    Nonempty (ρ.Equiv σ) := by
  rcases hv.exists_intertwiningMap_apply_eq hρ hσ hw with ⟨f, hf⟩
  refine ⟨f.ofBijective <| (IsIrreducible.bijective_or_eq_zero f).resolve_right fun h0 ↦ hw.1 ?_⟩
  rw [← hf, h0, IntertwiningMap.coe_zero, Pi.zero_apply]

variable (μ) in
/-- **The theorem of the highest weight** (LMFDB `repn.irrep.gl`): an irreducible rational
representation of `GL(n, ℂ)` is isomorphic to the rational Weyl module `V_μ` of a dominant weight
`μ` exactly when `μ` is its highest weight. Both have highest weight vectors of weight `μ`. -/
lemma nonempty_equiv_rationalWeylRep_iff_eq_highestWeight (h : IsRationalRep ρ) :
    Nonempty (ρ.Equiv (rationalWeylRep ℂ n μ)) ↔ μ.1 = ρ.highestWeight := by
  refine ⟨fun ⟨e⟩ ↦ (highestWeight_rationalWeylRep μ).symm.trans (highestWeight_eq_of_equiv e).symm,
    fun hμ ↦ ?_⟩
  have : Nontrivial W := IsIrreducible.nontrivial ‹_›
  have : Nontrivial (weylModuleOfShape ℂ n μ.detShiftShape).toSubmodule :=
    (isIrreducible_rationalWeylRep ℂ n μ).nontrivial
  rcases exists_isGLHighestWeightVector_highestWeight h with ⟨v, hv⟩
  rcases exists_isGLHighestWeightVector_highestWeight (isRationalRep_rationalWeylRep μ) with
    ⟨w, hw⟩
  rw [highestWeight_rationalWeylRep, hμ] at hw
  exact nonempty_equiv_of_isGLHighestWeightVector h (isRationalRep_rationalWeylRep μ) hv hw

/-- **The classification of the irreducible rational representations of `GL(n, ℂ)`** (LMFDB
`repn.irrep.gl`): each is isomorphic to the rational Weyl module `V_μ` for exactly one dominant
weight `μ`, its highest weight. Together with the irreducibility of the `V_μ`
(`TauCeti.isIrreducible_rationalWeylRep`) and their rationality, this is the bijection between the
dominant weights and the isomorphism classes of irreducible rational representations. -/
lemma existsUnique_nonempty_equiv_rationalWeylRep (h : IsRationalRep ρ) :
    ∃! μ : DominantWeight n, Nonempty (ρ.Equiv (rationalWeylRep ℂ n μ)) := by
  have : Nontrivial W := IsIrreducible.nontrivial ‹_›
  exact ⟨⟨ρ.highestWeight, antitone_highestWeight h⟩,
    (nonempty_equiv_rationalWeylRep_iff_eq_highestWeight _ h).2 rfl,
    fun μ hμ ↦ Subtype.ext ((nonempty_equiv_rationalWeylRep_iff_eq_highestWeight μ h).1 hμ)⟩

private lemma sum_mul_sub_nonpos {a b : Fin n → ℤ} (hab : ∑ i, a i = ∑ i, b i)
    (hle : ∀ m : ℕ, ∑ j ∈ Finset.univ.filter fun j : Fin n ↦ (j : ℕ) < m, a j ≤
      ∑ j ∈ Finset.univ.filter fun j : Fin n ↦ (j : ℕ) < m, b j) :
    ∑ i : Fin n, ((i : ℕ) : ℤ) * (b i - a i) ≤ 0 := by
  have key : ∑ i : Fin n, ((i : ℕ) : ℤ) * (b i - a i) =
      ∑ m : Fin n, ∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ m < i), (b i - a i) := by
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_gt_eq_Iio, Fin.card_Iio, nsmul_eq_mul]
  rw [key]
  refine Finset.sum_nonpos fun m _ ↦ ?_
  have hsplit : ∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ m < i), (b i - a i) +
      ∑ i ∈ Finset.univ.filter (fun i : Fin n ↦ ¬m < i), (b i - a i) = ∑ i, (b i - a i) :=
    Finset.sum_filter_add_sum_filter_not _ _ _
  have h2 : (Finset.univ.filter fun i : Fin n ↦ ¬m < i) =
      Finset.univ.filter fun j : Fin n ↦ (j : ℕ) < m + 1 := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  rw [h2] at hsplit
  simp only [Finset.sum_sub_distrib] at hsplit ⊢
  linarith [hle (m + 1)]

lemma eq_zero_of_forall_apply_apply_eq_zero (hv0 : v ≠ 0) (hφ : ∀ g, φ (ρ g v) = 0) : φ = 0 := by
  let S : Subrepresentation ρ := ⟨Submodule.span ℂ (Set.range fun g ↦ ρ g v), fun g x hx ↦ by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp⟩
    | zero => simp
    | add y z _ _ hy hz => simpa using Submodule.add_mem _ hy hz
    | smul c y _ hy => simpa using Submodule.smul_mem _ c hy⟩
  have hS : Submodule.span ℂ (Set.range fun g ↦ ρ g v) ≤ LinearMap.ker φ :=
    Submodule.span_le.2 (Set.range_subset_iff.2 hφ)
  rcases eq_bot_or_eq_top S with hS' | hS'
  · have hS'' : Submodule.span ℂ (Set.range fun g ↦ ρ g v) = ⊥ :=
      congrArg Subrepresentation.toSubmodule hS'
    have hv : v ∈ Submodule.span ℂ (Set.range fun g ↦ ρ g v) :=
      Submodule.subset_span ⟨1, by simp⟩
    rw [hS''] at hv
    exact absurd ((Submodule.mem_bot ℂ).1 hv) hv0
  · have hS'' : Submodule.span ℂ (Set.range fun g ↦ ρ g v) = ⊤ :=
      congrArg Subrepresentation.toSubmodule hS'
    rwa [hS'', top_le_iff, LinearMap.ker_eq_top] at hS

/-- **The weight of a highest weight vector of an irreducible rational representation is its
highest weight** (LMFDB `repn.highest.weight`): the weight `λ` of `ρ` is unique. Otherwise the
coordinate `ψ` of the `λ`-weight component vanishes on `v`; since `λ` dominates every weight of
`ρ ≅ V_λ`, contracting a lower unitriangular `L` to `1` along the torus shows that
`ψ (ρ L v) = 0`, so `g ↦ ψ (ρ g v)` vanishes on the big cell, hence everywhere, while the
`ρ g v` span `W`. -/
lemma IsGLHighestWeightVector.eq_highestWeight (h : IsRationalRep ρ)
    (hv : ρ.IsGLHighestWeightVector v l) : l = ρ.highestWeight := by
  have : Nontrivial W := IsIrreducible.nontrivial ‹_›
  by_contra hne
  rcases exists_isGLHighestWeightVector_highestWeight h with ⟨v₀, hv₀⟩
  rcases h.exists_apply_eq_one_forall_apply_diagGL hv₀.2.1 hv₀.1 with ⟨ψ, hψv₀, hψ⟩
  have hψv : ψ v = 0 := by
    rcases DFunLike.ne_iff.1 fun h' ↦ hne (weightChar_injective (K := ℂ) h') with ⟨t, ht⟩
    have h1 : ψ (ρ (diagGL t) v) = weightChar ℂ ρ.highestWeight t * ψ v := hψ t v
    rw [apply_of_mem_weightSpace hv.2.1, map_smul, smul_eq_mul] at h1
    by_contra h0
    exact ht (Units.ext (mul_right_cancel₀ h0 h1))
  have hl : weightSpace ρ l ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨v, hv.2.1, hv.1⟩
  rcases (nonempty_equiv_rationalWeylRep_iff_eq_highestWeight
    ⟨ρ.highestWeight, antitone_highestWeight h⟩ h).2 rfl with ⟨e⟩
  have he : ∑ i : Fin n, ((i : ℕ) : ℤ) * (ρ.highestWeight i - l i) ≤ 0 :=
    sum_mul_sub_nonpos (sum_eq_sum_of_weightSpace_ne_bot hl (weightSpace_highestWeight_ne_bot h))
      (sum_le_sum_of_weightSpace_rationalWeylRep_ne_bot ((e.weightSpace_eq_bot_iff l).not.1 hl))
  have hzero : (fun g ↦ ψ (ρ g v)) = 0 :=
    eq_zero_of_forall_mul_diagGL_mul (h.apply_mem_rationalFunctions ψ v)
      fun gL gU hL hL1 hU hU1 t ↦ by
        rw [hv.apply_mul_diagGL_mul ψ gL hU hU1, h.apply_apply_eq_zero_pow_mul hv.2.1 hψ
          (k := (-∑ i : Fin n, ((i : ℕ) : ℤ) * (ρ.highestWeight i - l i)).toNat) (by omega) hL
          hL1, hψv, mul_zero, mul_zero]
  rw [eq_zero_of_forall_apply_apply_eq_zero hv.1 (congrFun hzero)] at hψv₀
  exact zero_ne_one hψv₀

/-- **The highest weight line is unique** (LMFDB `repn.highest.weight`): any two highest weight
vectors of an irreducible rational representation of `GL(n, ℂ)` are proportional. Both have the
highest weight as weight, so an intertwining map sends one to the other, and by Schur's lemma it is
a scalar. -/
lemma IsGLHighestWeightVector.mem_span_singleton (h : IsRationalRep ρ)
    (hv : ρ.IsGLHighestWeightVector v l) (hv' : ρ.IsGLHighestWeightVector v' l') : v' ∈ ℂ ∙ v := by
  rw [hv'.eq_highestWeight h, ← hv.eq_highestWeight h] at hv'
  rcases hv.exists_intertwiningMap_apply_eq h h hv' with ⟨f, hf⟩
  have : FiniteDimensional ℂ W := h.finite
  rcases IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed.2 f with ⟨c, rfl⟩
  exact Submodule.mem_span_singleton.2 ⟨c, hf ▸ rfl⟩

/-- **The theorem of the highest weight, as stated in LMFDB `repn.highest.weight`**: an
irreducible rational representation of `GL(n, ℂ)` has a unique line `⟨v₀⟩` and a unique weight `λ`
such that `v₀` is a highest weight vector of weight `λ`. This `λ` is `ρ.highestWeight`
(`Representation.IsGLHighestWeightVector.eq_highestWeight`), which is dominant
(`Representation.antitone_highestWeight`), so it is the knowl's `λ₁ ≥ ⋯ ≥ λₙ`. -/
lemma existsUnique_isGLHighestWeightVector (h : IsRationalRep ρ) :
    ∃! L : Submodule ℂ W × (Fin n → ℤ), ∃ v, L.1 = ℂ ∙ v ∧ ρ.IsGLHighestWeightVector v L.2 := by
  have : Nontrivial W := IsIrreducible.nontrivial ‹_›
  rcases exists_isGLHighestWeightVector_highestWeight h with ⟨v₀, hv₀⟩
  refine ⟨(ℂ ∙ v₀, ρ.highestWeight), ⟨v₀, rfl, hv₀⟩, ?_⟩
  rintro ⟨L, l'⟩ ⟨v', rfl, hv'⟩
  refine Prod.ext (le_antisymm ?_ ?_) (hv'.eq_highestWeight h)
  · exact (Submodule.span_singleton_le_iff_mem _ _).2 (hv₀.mem_span_singleton h hv')
  · exact (Submodule.span_singleton_le_iff_mem _ _).2 (hv'.mem_span_singleton h hv₀)

end Representation
