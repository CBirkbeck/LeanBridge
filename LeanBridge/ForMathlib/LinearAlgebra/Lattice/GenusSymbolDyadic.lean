import LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolSign
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-!
# The dyadic data of the Conway genus symbol: signs and oddities of Jordan constituents

In the Conway genus symbol (LMFDB `lattice.conway_genus_symbol`; Conway and Sloane, *Sphere
Packings, Lattices and Groups*, Chapter 15, §7.3–7.4) of an integral lattice, every constituent
`q f_q`, `q = 2 ^ j`, of a dyadic Jordan decomposition carries, besides its rank and its type, a
sign `ε_q = (2 | det f_q)`, which is `+1` when `det f_q ≡ ±1 mod 8` and `-1` when
`det f_q ≡ ±3 mod 8`, and an oddity `t_q ∈ ℤ/8`, the trace of a diagonalization of `f_q` when
`f_q` is odd and `0` when it is even.

The oddity is defined here intrinsically, through characteristic vectors: a vector `w` with
`C w x ≡ C x x mod 2` for all `x`. A unimodular symmetric form over `ℤ_2` has characteristic
vectors, any two of which have norms `C w w` congruent modulo `8`; this norm is the oddity. It is
the trace modulo `8` of any diagonalization (`LinearMap.BilinForm.dyadicOddity_eq_sum`), `0` for
an even form (`LinearMap.BilinForm.dyadicOddity_eq_zero_of_forall_two_dvd`), and an isometry
invariant (`LinearMap.BilinForm.dyadicOddity_eq_of_equivalent`). Tau Ceti's `main` branch has the
same theory of characteristic vectors (`LinearMap.BilinForm.IsCharacteristic`), not in the pinned
version.

The sign and the oddity of a constituent do not depend on the choice of basis or characteristic
vector, but they depend on the Jordan decomposition: only the total oddity of each compartment and
the total sign of each train are invariants, up to the rules of oddity fusion and sign walking,
which lead to Conway and Sloane's canonical `2`-adic symbol. That normal form and its invariance
are not formalised.

## Main definitions

* `LinearMap.BilinForm.IsDyadicCharacteristic`: a characteristic vector of a form over `ℤ_2`.
* `LinearMap.BilinForm.dyadicOddity`: the oddity of a form over `ℤ_2`.
* `LinearMap.BilinForm.IsJordanSplitting.dyadicSign` (LMFDB `lattice.conway_genus_symbol`): the
  sign of a constituent of a dyadic Jordan splitting.
* `LinearMap.BilinForm.IsJordanSplitting.dyadicOddity` (LMFDB `lattice.conway_genus_symbol`): the
  oddity of a constituent of a dyadic Jordan splitting.

## Main results

* `LinearMap.BilinForm.dyadicOddity_eq`: the oddity of a unimodular form is the norm modulo `8`
  of any characteristic vector.
* `LinearMap.BilinForm.dyadicOddity_eq_sum`: the oddity of a diagonal unimodular form is its trace
  modulo `8`.
* `LinearMap.BilinForm.dyadicOddity_eq_zero_of_forall_two_dvd`: the oddity of an even unimodular
  form is `0`.
* `LinearMap.BilinForm.dyadicOddity_eq_of_equivalent`: the oddity is an isometry invariant.
* `LinearMap.BilinForm.IsJordanSplitting.dyadicSign_eq`: the sign of a constituent can be computed
  in any basis.
* `LinearMap.BilinForm.IsJordanSplitting.dyadicSign_eq_one_or_eq_neg_one`: it is `±1`.
* `LinearMap.BilinForm.IsJordanSplitting.dyadicOddity_eq_zero`: constituents of type `II` have
  oddity `0`.
-/

open Module

open LinearMap (BilinForm)

namespace PadicInt

lemma two_dvd_mul_self_sub (r : ℤ_[2]) : (2 : ℤ_[2]) ∣ r * r - r := by
  have h : toZMod (r * r - r) = 0 := by
    rw [map_sub, map_mul]
    generalize toZMod r = a
    revert a
    decide
  rw [← RingHom.mem_ker, ker_toZMod, maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
  exact_mod_cast h

lemma toZModPow_three_eq_of_eight_dvd {x y : ℤ_[2]} (h : (8 : ℤ_[2]) ∣ x - y) :
    toZModPow 3 x = toZModPow 3 y := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, ker_toZModPow, Ideal.mem_span_singleton]
  exact_mod_cast h

lemma χ₈_toZModPow_mul_mul {u d : ℤ_[2]} (hu : IsUnit u) :
    ZMod.χ₈ (toZModPow 3 (u * d * u)) = ZMod.χ₈ (toZModPow 3 d) := by
  rcases hu.map (toZModPow 3 : ℤ_[2] →+* ZMod 8) with ⟨U, hU⟩
  have hχ : ZMod.χ₈ (U : ZMod 8) ^ 2 = 1 := by
    rw [← MulChar.pow_apply_coe, ZMod.isQuadratic_χ₈.sq_eq_one, MulChar.one_apply_coe]
  rw [map_mul (toZModPow 3), map_mul (toZModPow 3), ← hU, map_mul, map_mul, mul_comm, ← mul_assoc,
    ← sq, hχ, one_mul]

end PadicInt

namespace LinearMap.BilinForm

variable {K K' : Type*} [AddCommGroup K] [Module ℤ_[2] K] [AddCommGroup K'] [Module ℤ_[2] K']
  {C : BilinForm ℤ_[2] K} {C' : BilinForm ℤ_[2] K'} {w : K}

variable (C w) in
/-- A **characteristic vector** of a bilinear form `C` over `ℤ_2`: a vector `w` with
`C w x ≡ C x x mod 2` for every `x`. -/
def IsDyadicCharacteristic : Prop :=
  ∀ x, (2 : ℤ_[2]) ∣ C w x - C x x

lemma isDyadicCharacteristic_of_basis {ι : Type*} (hC : C.IsSymm) (b : Basis ι ℤ_[2] K)
    (hw : ∀ i, (2 : ℤ_[2]) ∣ C w (b i) - C (b i) (b i)) : C.IsDyadicCharacteristic w := by
  intro x
  induction (b.span_eq ▸ Submodule.mem_top : x ∈ Submodule.span ℤ_[2] (Set.range b)) using
    Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨i, rfl⟩
    exact hw i
  | zero => simp
  | add x y _ _ hx hy =>
    have hxy :
        C w (x + y) - C (x + y) (x + y) = (C w x - C x x) + (C w y - C y y) - 2 * C x y := by
      rw [map_add, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hC.eq y x]
      ring1
    rw [hxy]
    exact dvd_sub (dvd_add hx hy) (dvd_mul_right 2 _)
  | smul r x _ hx =>
    have hrx : C w (r • x) - C (r • x) (r • x) = r * (C w x - C x x) - (r * r - r) * C x x := by
      simp only [map_smul, LinearMap.smul_apply]
      ring1
    rw [hrx]
    exact dvd_sub (dvd_mul_of_dvd_right hx r)
      (dvd_mul_of_dvd_left (PadicInt.two_dvd_mul_self_sub r) _)

variable [Module.Free ℤ_[2] K] in
lemma exists_isDyadicCharacteristic (hC : C.IsPerfPair) (hCs : C.IsSymm) :
    ∃ w, C.IsDyadicCharacteristic w := by
  rcases hC.bijective_left.2 ((Free.chooseBasis ℤ_[2] K).constr ℤ_[2]
    fun i ↦ C (Free.chooseBasis ℤ_[2] K i) (Free.chooseBasis ℤ_[2] K i)) with ⟨w, hw⟩
  refine ⟨w, isDyadicCharacteristic_of_basis hCs (Free.chooseBasis ℤ_[2] K) fun i ↦ ?_⟩
  rw [hw, Basis.constr_basis, sub_self]
  exact dvd_zero 2

lemma IsDyadicCharacteristic.eight_dvd_sub (hC : C.IsPerfPair) (hCs : C.IsSymm) {w' : K}
    (hw : C.IsDyadicCharacteristic w) (hw' : C.IsDyadicCharacteristic w') :
    (8 : ℤ_[2]) ∣ C w w - C w' w' := by
  rcases (isModular_one_iff.mpr hC).exists_eq_smul_of_forall_dvd (nonZeroDivisors ℤ_[2]).one_mem
    (mem_nonZeroDivisors_of_ne_zero two_ne_zero) (x := w - w') fun y ↦ by
      rw [one_mul, map_sub, LinearMap.sub_apply, ← sub_sub_sub_cancel_right _ _ (C y y)]
      exact dvd_sub (hw y) (hw' y) with ⟨v, hv⟩
  rw [sub_eq_iff_eq_add.mp hv]
  have hsub : C ((2 : ℤ_[2]) • v + w') ((2 : ℤ_[2]) • v + w') - C w' w' =
      4 * ((C w' v - C v v) + 2 * C v v) := by
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hCs.eq v w']
    ring1
  have h8 : (8 : ℤ_[2]) = 4 * 2 := by norm_num
  rw [hsub, h8]
  exact mul_dvd_mul_left 4 (dvd_add (hw' v) (dvd_mul_right 2 _))

open scoped Classical in
variable (C) in
/-- The **oddity** of a symmetric bilinear form `C` over `ℤ_2` (Conway and Sloane): the norm
`C w w` modulo `8` of a characteristic vector `w`, and `0` if there is none. For a unimodular form
it does not depend on `w` (`dyadicOddity_eq`), it is the trace modulo `8` of a diagonalization
(`dyadicOddity_eq_sum`), which is Conway and Sloane's definition for an odd form, and it is `0`
for an even form (`dyadicOddity_eq_zero_of_forall_two_dvd`). -/
noncomputable def dyadicOddity : ZMod 8 :=
  if h : ∃ w, C.IsDyadicCharacteristic w then PadicInt.toZModPow 3 (C h.choose h.choose) else 0

/-- **The oddity of a unimodular form is the norm modulo `8` of any characteristic vector.** -/
lemma dyadicOddity_eq (hC : C.IsPerfPair) (hCs : C.IsSymm) (hw : C.IsDyadicCharacteristic w) :
    C.dyadicOddity = PadicInt.toZModPow 3 (C w w) := by
  rw [dyadicOddity, dite_eq_left ⟨w, hw⟩]
  exact PadicInt.toZModPow_three_eq_of_eight_dvd
    ((Exists.choose_spec ⟨w, hw⟩).eight_dvd_sub hC hCs hw)

/-- **The oddity of a diagonal unimodular form is its trace modulo `8`.** -/
lemma dyadicOddity_eq_sum {ι : Type*} [Fintype ι] (hC : C.IsPerfPair) (hCs : C.IsSymm)
    (b : Basis ι ℤ_[2] K) (hb : C.iIsOrtho b) :
    C.dyadicOddity = ∑ i, PadicInt.toZModPow 3 (C (b i) (b i)) := by
  classical
  have hdiag (k : ι) : C (∑ i, b i) (b k) = C (b k) (b k) := by
    rw [map_sum, LinearMap.sum_apply]
    exact Finset.sum_eq_single k (fun i _ hik ↦ hb hik) (by simp)
  have hw : C.IsDyadicCharacteristic (∑ i, b i) :=
    isDyadicCharacteristic_of_basis hCs b fun k ↦ by rw [hdiag, sub_self]; exact dvd_zero 2
  rw [dyadicOddity_eq hC hCs hw, map_sum, map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [hdiag]

/-- **The oddity of an even unimodular form is `0`.** -/
lemma dyadicOddity_eq_zero_of_forall_two_dvd (hC : C.IsPerfPair) (hCs : C.IsSymm)
    (heven : ∀ x, (2 : ℤ_[2]) ∣ C x x) : C.dyadicOddity = 0 := by
  have hw : C.IsDyadicCharacteristic 0 := fun x ↦ by
    rw [map_zero, LinearMap.zero_apply, zero_sub]
    exact dvd_neg.mpr (heven x)
  rw [dyadicOddity_eq hC hCs hw, map_zero, map_zero]

variable [Module.Free ℤ_[2] K] in
/-- **The oddity is an isometry invariant** of unimodular forms over `ℤ_2`. -/
lemma dyadicOddity_eq_of_equivalent (hC : C.IsPerfPair) (hCs : C.IsSymm) (hC' : C'.IsPerfPair)
    (hC's : C'.IsSymm) (h : C.Equivalent C') : C.dyadicOddity = C'.dyadicOddity := by
  rcases h with ⟨e⟩
  rcases exists_isDyadicCharacteristic hC hCs with ⟨w, hw⟩
  have hw' : C'.IsDyadicCharacteristic (e w) := fun x ↦ by
    rw [← e.toLinearEquiv.apply_symm_apply x, e.coe_toLinearEquiv, e.map_app, e.map_app]
    exact hw _
  rw [dyadicOddity_eq hC hCs hw, dyadicOddity_eq hC' hC's hw', e.map_app]

variable {M : Type*} [AddCommGroup M] [Module ℤ_[2] M] {B : BilinForm ℤ_[2] M}
  {N : ℕ → Submodule ℤ_[2] M} {j : ℕ}

variable (j) in
/-- The **oddity** `t_q` (LMFDB `lattice.conway_genus_symbol`) of the constituent `N j`, of scale
`q = 2 ^ j`, of a Jordan splitting `N` of a bilinear form over `ℤ_2`: the oddity of its unit form
`C`, `B|N j = 2 ^ j • C`, which is `0` when the constituent has type `II`
(`dyadicOddity_eq_zero`). It depends on the Jordan splitting (oddity fusion). -/
noncomputable def IsJordanSplitting.dyadicOddity (h : B.IsJordanSplitting ((2 : ℕ) : ℤ_[2]) N) :
    ZMod 8 :=
  (h.unitForm j).dyadicOddity

/-- **Jordan constituents of type `II` have oddity `0`.** -/
lemma IsJordanSplitting.dyadicOddity_eq_zero (h : B.IsJordanSplitting ((2 : ℕ) : ℤ_[2]) N)
    (hB : B.IsSymm) (hII : ∀ x ∈ N j, ((2 : ℕ) : ℤ_[2]) ^ (j + 1) ∣ B x x) :
    h.dyadicOddity j = 0 := by
  refine dyadicOddity_eq_zero_of_forall_two_dvd (h.isPerfPair_unitForm j) (h.isSymm_unitForm hB)
    fun x ↦ ?_
  have hx :
      ((2 : ℕ) : ℤ_[2]) ^ j * ((2 : ℕ) : ℤ_[2]) ∣ ((2 : ℕ) : ℤ_[2]) ^ j * h.unitForm j x x := by
    rw [← pow_succ, ← smul_eq_mul, ← LinearMap.smul_apply, ← LinearMap.smul_apply,
      h.pow_smul_unitForm]
    exact hII x x.2
  exact_mod_cast (mul_dvd_mul_iff_left (pow_ne_zero j PadicInt.irreducible_p.ne_zero)).mp hx

variable [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M]

variable (j) in
/-- The **dyadic sign** `ε_q` (LMFDB `lattice.conway_genus_symbol`) of the constituent `N j`, of
scale `q = 2 ^ j`, of a Jordan splitting `N` of a bilinear form over `ℤ_2`: the Jacobi symbol
`(2 | d) = χ₈(d)` of the determinant `d` of the unit form `C`, `B|N j = 2 ^ j • C`, in a basis of
`N j`, that is `+1` when `d ≡ ±1 mod 8` and `-1` when `d ≡ ±3 mod 8`. It is `±1`
(`dyadicSign_eq_one_or_eq_neg_one`) and does not depend on the basis (`dyadicSign_eq`), but it
depends on the Jordan splitting (sign walking). -/
noncomputable def IsJordanSplitting.dyadicSign (h : B.IsJordanSplitting ((2 : ℕ) : ℤ_[2]) N) : ℤ :=
  ZMod.χ₈ (PadicInt.toZModPow 3
    (toMatrix₂ (finBasis ℤ_[2] (N j)) (finBasis ℤ_[2] (N j)) (h.unitForm j)).det)

/-- **The dyadic sign of a Jordan constituent can be computed in any basis**, the determinants in
two bases differing by the square of a unit, which is `1` modulo `8`. -/
lemma IsJordanSplitting.dyadicSign_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : B.IsJordanSplitting ((2 : ℕ) : ℤ_[2]) N) (b : Basis ι ℤ_[2] (N j)) :
    h.dyadicSign j = ZMod.χ₈ (PadicInt.toZModPow 3 (toMatrix₂ b b (h.unitForm j)).det) := by
  have hcard : Fintype.card (Fin (finrank ℤ_[2] (N j))) = Fintype.card ι := by
    rw [Fintype.card_fin, finrank_eq_card_basis b]
  rw [dyadicSign, ← det_toMatrix₂_reindex _ (Fintype.equivOfCardEq hcard),
    ← LinearMap.toMatrix₂_mul_basis_toMatrix
    ((finBasis ℤ_[2] (N j)).reindex (Fintype.equivOfCardEq hcard))
    ((finBasis ℤ_[2] (N j)).reindex (Fintype.equivOfCardEq hcard)) b b, Matrix.det_mul,
    Matrix.det_mul, Matrix.det_transpose, PadicInt.χ₈_toZModPow_mul_mul
    (Matrix.isUnit_det_of_right_inverse (Basis.toMatrix_mul_toMatrix_flip _ _))]

/-- **The dyadic sign of a Jordan constituent is `±1`**, the determinant of its unit form being a
unit. -/
lemma IsJordanSplitting.dyadicSign_eq_one_or_eq_neg_one
    (h : B.IsJordanSplitting ((2 : ℕ) : ℤ_[2]) N) : h.dyadicSign j = 1 ∨ h.dyadicSign j = -1 := by
  rcases ((isUnit_det_toMatrix₂_of_isPerfPair (finBasis ℤ_[2] (N j))
    (h.isPerfPair_unitForm j)).map (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod 8)) with ⟨U, hU⟩
  rw [dyadicSign, ← hU, ← sq_eq_one_iff, ← MulChar.pow_apply_coe, ZMod.isQuadratic_χ₈.sq_eq_one,
    MulChar.one_apply_coe]

end LinearMap.BilinForm
