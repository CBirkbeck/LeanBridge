import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.RingTheory.Polynomial.GaussLemma
import LeanBridge.ForMathlib.Algebra.Quaternion.OfFinrankEqFour
import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.QuaternionOrder

/-!
# The discriminant of a quaternion order is the square of a positive integer

Let `O` be an order of a quaternion algebra `B` over `ℚ`, with `ℤ`-basis `x₁, …, x₄`. Its
discriminant is `disc(O) = |det (trd(x_i x_j))|` and its reduced discriminant `discrd(O)` is the
positive integer with `discrd(O)² = disc(O)` (LMFDB `shimcurve.disco`,
`Subalgebra.quaternionDisc`, `Subalgebra.quaternionDiscrd`). This file proves the facts that make
these definitions meaningful.

* An order has a `ℤ`-basis of four elements: it is a free `ℤ`-module of rank `4`, and a `ℤ`-basis
  of it is a `ℚ`-basis of `B` (Mathlib's `Module.Basis.extendOfIsLattice`).
* The reduced trace is an integer on an order: for `x ∈ O`, integral over `ℤ`, the minimal
  polynomial `X² - trd(x) X + nrd(x)` over `ℚ` (when `x ∉ ℚ`) divides a monic integer polynomial, so
  it has integer coefficients by Gauss's lemma. So `disc(O)` is an integer.
* For a `ℚ`-basis `y` of `B ≅ (a, b / ℚ)`, `det (trd(y_i y_j)) = -(4 a b det Q)²`, where `Q` is the
  matrix of `y` in the basis `1, i, j, k`, at which the Gram matrix of the trace form is
  `diag(2, 2a, 2b, -2ab)`. So `disc(O)` is the square of the rational number `4 a b det Q`, an
  integer since its square is, and positive.
* A change of `ℤ`-basis of `O` multiplies `det Q` by the determinant `±1` of an integral matrix with
  integral inverse, so `disc(O)` does not depend on the basis.

## Main definitions

* `QuaternionAlgebra.traceForm`: the reduced trace form `(x, y) ↦ trd(x y)`, a `ℚ`-bilinear form.

## Main results

* `Subalgebra.nonempty_basis_of_isQuaternionOrder` (LMFDB `shimcurve.disco`): an order has a
  `ℤ`-basis of four elements.
* `Subalgebra.exists_reducedTrace_eq_intCast` (LMFDB `shimcurve.disco`): the reduced trace is an
  integer on an order.
* `Subalgebra.quaternionDisc_eq_quaternionDiscOfBasis` (LMFDB `shimcurve.disco`): the discriminant
  of an order does not depend on the basis.
* `Subalgebra.exists_quaternionDisc_eq_natCast` (LMFDB `shimcurve.disco`): the discriminant is an
  integer.
* `Subalgebra.exists_quaternionDiscrd_eq_natCast`, `Subalgebra.quaternionDiscrd_pos`,
  `Subalgebra.quaternionDiscrd_sq` (LMFDB `shimcurve.disco`): the reduced discriminant is a
  positive integer whose square is the discriminant.
-/

open Module Matrix Polynomial QuaternionAlgebra

open LinearMap (BilinForm)

open Submodule (IsLattice)

open scoped Quaternion

namespace QuaternionAlgebra

variable (B : Type*) [Ring B] [Algebra ℚ B]

/-- The **reduced trace form** `(x, y) ↦ trd(x y)` of a quaternion algebra `B` over `ℚ`, a
`ℚ`-bilinear form on `B`. -/
noncomputable def traceForm : BilinForm ℚ B :=
  (LinearMap.mul ℚ B).compr₂ ((2⁻¹ : ℚ) • (LinearMap.trace ℚ B ∘ₗ LinearMap.mul ℚ B))

variable {B}

lemma traceForm_apply (x y : B) : traceForm B x y = reducedTrace B (x * y) := by
  rw [reducedTrace, div_eq_inv_mul]
  rfl

lemma reducedTrace_algEquiv {C : Type*} [Ring C] [Algebra ℚ C] (e : C ≃ₐ[ℚ] B) (x : C) :
    reducedTrace B (e x) = reducedTrace C x := by
  have h : LinearMap.mulLeft ℚ (e x) = e.toLinearEquiv.conj (LinearMap.mulLeft ℚ x) := by
    ext y
    simp
  rw [reducedTrace, reducedTrace, h, LinearMap.trace_conj']

lemma toMatrix_traceForm_basisOneIJK (a b : ℚ) :
    BilinForm.toMatrix (basisOneIJK a 0 b) (traceForm ℍ[ℚ,a,b]) =
      diagonal ![2, 2 * a, 2 * b, -(2 * a * b)] := by
  ext k l
  rw [BilinForm.toMatrix_apply, traceForm_apply, reducedTrace_quaternionAlgebra]
  fin_cases k <;> fin_cases l <;> simp [basisOneIJK, mul_assoc]

lemma det_toMatrix_traceForm {a b : ℚ} (e : ℍ[ℚ,a,b] ≃ₐ[ℚ] B) (c : Module.Basis (Fin 4) ℚ B) :
    (BilinForm.toMatrix c (traceForm B)).det =
      -(4 * a * b * ((basisOneIJK a 0 b).map e.toLinearEquiv).det c) ^ 2 := by
  let f : Module.Basis (Fin 4) ℚ B := (basisOneIJK a 0 b).map e.toLinearEquiv
  have hf : BilinForm.toMatrix f (traceForm B) = diagonal ![2, 2 * a, 2 * b, -(2 * a * b)] := by
    rw [← toMatrix_traceForm_basisOneIJK]
    ext k l
    simp [traceForm_apply, f, ← map_mul, reducedTrace_algEquiv]
  rw [← BilinForm.toMatrix_mul_basis_toMatrix f c, det_mul, det_mul, det_transpose, hf,
    det_diagonal, Fin.prod_univ_four, Basis.det_apply]
  dsimp only [f]
  simp
  ring1

lemma aeval_sq_sub_two_mul_re_add {a b : ℚ} (q : ℍ[ℚ,a,b]) :
    aeval q (X ^ 2 - C (2 * q.re) * X + C (q * star q).re) = 0 := by
  have h1 : star q = ↑(2 * q.re) - q := by
    rw [eq_sub_iff_add_eq, add_comm, self_add_star', zero_mul, add_zero]
  have hn : ((q * star q).re : ℍ[ℚ,a,b]) = ↑(2 * q.re) * q - q * q := by
    rw [← mul_star_eq_coe, h1, mul_sub, ← coe_commutes]
  rw [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C, aeval_C, coe_algebraMap, hn, pow_two]
  abel

lemma exists_two_mul_re_eq_intCast {a b : ℚ} {q : ℍ[ℚ,a,b]} (hq : IsIntegral ℤ q) :
    ∃ z : ℤ, 2 * q.re = z := by
  by_cases hq₀ : q ∈ (algebraMap ℚ ℍ[ℚ,a,b]).range
  · rcases hq₀ with ⟨r, rfl⟩
    have hr : IsIntegral ℤ r := (isIntegral_algHom_iff ((Algebra.ofId ℚ ℍ[ℚ,a,b]).restrictScalars ℤ)
      (algebraMap ℚ ℍ[ℚ,a,b]).injective).mp hq
    rcases IsIntegrallyClosed.isIntegral_iff.mp hr with ⟨z, hz⟩
    exact ⟨2 * z, by simp [← hz]⟩
  have hint : IsIntegral ℚ q := hq.tower_top
  have hpm : (X ^ 2 - C (2 * q.re) * X + C (q * star q).re : ℚ[X]).Monic := by
    monicity!
  have hpd : (X ^ 2 - C (2 * q.re) * X + C (q * star q).re : ℚ[X]).natDegree = 2 := by
    compute_degree!
  have hmin : minpoly ℚ q = X ^ 2 - C (2 * q.re) * X + C (q * star q).re := by
    refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hpm
      (minpoly.dvd ℚ q (aeval_sq_sub_two_mul_re_add q)) ?_).symm
    rw [hpd]
    by_contra hlt
    have h1 : (minpoly ℚ q).natDegree = 1 := by
      have hpos : 0 < (minpoly ℚ q).natDegree := minpoly.natDegree_pos hint
      omega
    exact hq₀ (minpoly.mem_range_of_degree_eq_one ℚ q (degree_eq_iff_natDegree_eq_of_pos
      one_pos |>.mpr h1))
  rcases hq with ⟨f, hfm, hf⟩
  have hdvd : minpoly ℚ q ∣ f.map (algebraMap ℤ ℚ) :=
    minpoly.dvd ℚ q (by rw [aeval_map_algebraMap, aeval_def, hf])
  rcases IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ hfm hdvd with ⟨g, hg⟩
  rw [(minpoly.monic hint).leadingCoeff, C_1, mul_one, hmin] at hg
  refine ⟨-g.coeff 1, ?_⟩
  have h : (g.coeff 1 : ℚ) = -(2 * q.re) := by
    simpa using congrArg (coeff · 1) hg
  rw [Int.cast_neg, h, neg_neg]

end QuaternionAlgebra

namespace Subalgebra

lemma exists_intCast_eq_of_sq_eq_natCast {r : ℚ} {n : ℕ} (h : r ^ 2 = n) : ∃ w : ℤ, r = w := by
  have hr : IsIntegral ℤ r := ⟨X ^ 2 - C (n : ℤ), by monicity!, by simp [h]⟩
  rcases IsIntegrallyClosed.isIntegral_iff.mp hr with ⟨w, hw⟩
  exact ⟨w, hw.symm⟩

variable {B : Type*} [Ring B] [Algebra ℚ B] {O : Subalgebra ℤ B}

/-- **An order of a quaternion algebra over `ℚ` has a `ℤ`-basis of four elements** (LMFDB
`shimcurve.disco`): it is a free `ℤ`-module of rank `4`. -/
lemma nonempty_basis_of_isQuaternionOrder (h4 : finrank ℚ B = 4) (hO : O.IsQuaternionOrder) :
    Nonempty (Basis (Fin 4) ℤ O) := by
  have : IsLattice ℚ (toSubmodule O) := hO
  have hr : finrank ℤ (toSubmodule O) = 4 := by
    rw [← h4, finrank, finrank, IsLattice.rank' ℚ (toSubmodule O)]
  exact ⟨(Module.finBasisOfFinrankEq ℤ (toSubmodule O) hr).map O.toSubmoduleEquiv⟩

lemma exists_basis_coe_eq (hO : O.IsQuaternionOrder) (x : Basis (Fin 4) ℤ O) :
    ∃ c : Basis (Fin 4) ℚ B, ∀ k, c k = x k := by
  have : IsLattice ℚ (toSubmodule O) := hO
  exact ⟨(x.map O.toSubmoduleEquiv.symm).extendOfIsLattice ℚ, fun k ↦ by simp; rfl⟩

lemma repr_coe_eq_intCast {x : Basis (Fin 4) ℤ O} {c : Basis (Fin 4) ℚ B}
    (hc : ∀ k, c k = x k) (v : O) (k : Fin 4) : c.repr v k = x.repr v k := by
  have hv : (v : B) = ∑ k, ((x.repr v k : ℤ) : ℚ) • c k := by
    conv_lhs => rw [← x.sum_repr v]
    simp [hc, Int.cast_smul_eq_zsmul]
  rw [hv, c.repr_sum_self]

lemma quaternionDiscOfBasis_eq_sq {a b : ℚ} (e : ℍ[ℚ,a,b] ≃ₐ[ℚ] B) {x : Basis (Fin 4) ℤ O}
    {c : Basis (Fin 4) ℚ B} (hc : ∀ k, c k = x k) : O.quaternionDiscOfBasis x =
      (4 * a * b * ((basisOneIJK a 0 b).map e.toLinearEquiv).det c) ^ 2 := by
  have hm : (Matrix.of fun i j ↦ reducedTrace B ((x i : B) * x j)) =
      BilinForm.toMatrix c (traceForm B) := by
    ext i j
    rw [BilinForm.toMatrix_apply, traceForm_apply, hc, hc, of_apply]
  rw [quaternionDiscOfBasis, hm, det_toMatrix_traceForm e c, abs_neg, abs_sq]

lemma sq_det_eq_sq_det {a b : ℚ} (e : ℍ[ℚ,a,b] ≃ₐ[ℚ] B) {x y : Basis (Fin 4) ℤ O}
    {c d : Basis (Fin 4) ℚ B} (hc : ∀ k, c k = x k) (hd : ∀ k, d k = y k) :
    ((basisOneIJK a 0 b).map e.toLinearEquiv).det d ^ 2 =
      ((basisOneIJK a 0 b).map e.toLinearEquiv).det c ^ 2 := by
  have hM : c.toMatrix d = (Int.castRingHom ℚ).mapMatrix (x.toMatrix y) := by
    ext k j
    rw [Basis.toMatrix_apply, hd, repr_coe_eq_intCast hc, RingHom.mapMatrix_apply, map_apply,
      Basis.toMatrix_apply, eq_intCast]
  have hdet : (x.toMatrix y).det ^ 2 = 1 := by
    have h : (x.toMatrix y).det * (y.toMatrix x).det = 1 := by
      rw [← det_mul, x.toMatrix_mul_toMatrix_flip, det_one]
    rcases Int.eq_one_or_neg_one_of_mul_eq_one h with h1 | h1 <;> simp [h1]
  rw [Basis.det_apply, Basis.det_apply, ← Basis.toMatrix_mul_toMatrix _ c d, det_mul, hM,
    ← RingHom.map_det, mul_pow, ← map_pow, hdet, map_one, mul_one]

lemma quaternionDiscrd_eq_abs {w : ℤ} (hw : O.quaternionDisc = w ^ 2) :
    O.quaternionDiscrd = |(w : ℚ)| := by
  rw [quaternionDiscrd, hw, sq, Rat.sqrt_eq]

variable [Algebra.IsCentral ℚ B] [IsSimpleRing B]

/-- **The reduced trace is an integer on an order** of a quaternion algebra over `ℚ`. -/
lemma exists_reducedTrace_eq_intCast (h4 : finrank ℚ B = 4) (hO : O.IsQuaternionOrder) {u : B}
    (hu : u ∈ O) : ∃ z : ℤ, reducedTrace B u = z := by
  rcases exists_nonempty_algEquiv_of_finrank_eq_four (by simp) h4 with ⟨a, b, ⟨e⟩⟩
  rcases exists_two_mul_re_eq_intCast <| (IsIntegral.of_mem_of_fg O hO.fg u hu).map
    (e.symm.toAlgHom.restrictScalars ℤ) with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  rw [← e.apply_symm_apply u, reducedTrace_algEquiv, reducedTrace_quaternionAlgebra, zero_mul,
    add_zero]
  exact hz

/-- **The discriminant of an order does not depend on the basis** (LMFDB `shimcurve.disco`): it is
`|det (trd(x_i x_j))|` for every `ℤ`-basis `x₁, …, x₄` of `O`. -/
lemma quaternionDisc_eq_quaternionDiscOfBasis (h4 : finrank ℚ B = 4) (hO : O.IsQuaternionOrder)
    (x : Basis (Fin 4) ℤ O) : O.quaternionDisc = O.quaternionDiscOfBasis x := by
  have hne : Nonempty (Basis (Fin 4) ℤ O) := ⟨x⟩
  rcases exists_nonempty_algEquiv_of_finrank_eq_four (by simp) h4 with ⟨a, b, ⟨e⟩⟩
  rcases exists_basis_coe_eq hO x with ⟨c, hc⟩
  rcases exists_basis_coe_eq hO hne.some with ⟨d, hd⟩
  rw [quaternionDisc, dite_eq_left hne, quaternionDiscOfBasis_eq_sq e hd,
    quaternionDiscOfBasis_eq_sq e hc, mul_pow, sq_det_eq_sq_det e hc hd, ← mul_pow]

/-- **The discriminant of an order is an integer** (LMFDB `shimcurve.disco`). -/
lemma exists_quaternionDisc_eq_natCast (h4 : finrank ℚ B = 4) (hO : O.IsQuaternionOrder) :
    ∃ n : ℕ, O.quaternionDisc = n := by
  rcases nonempty_basis_of_isQuaternionOrder h4 hO with ⟨x⟩
  choose z hz using fun i j ↦ exists_reducedTrace_eq_intCast h4 hO (mul_mem (x i).2 (x j).2)
  have hm : (Matrix.of fun i j ↦ reducedTrace B ((x i : B) * x j)) =
      (Int.castRingHom ℚ).mapMatrix (Matrix.of z) := by
    ext i j
    simp [hz]
  refine ⟨(Matrix.of z).det.natAbs, ?_⟩
  rw [quaternionDisc_eq_quaternionDiscOfBasis h4 hO x, quaternionDiscOfBasis, hm, ← RingHom.map_det,
    Nat.cast_natAbs, eq_intCast, Int.cast_abs]

lemma exists_quaternionDisc_eq_sq (h4 : finrank ℚ B = 4) (hO : O.IsQuaternionOrder) :
    ∃ w : ℤ, w ≠ 0 ∧ O.quaternionDisc = w ^ 2 := by
  rcases nonempty_basis_of_isQuaternionOrder h4 hO with ⟨x⟩
  rcases exists_nonempty_algEquiv_of_finrank_eq_four (by simp) h4 with ⟨a, b, ⟨e⟩⟩
  rcases exists_basis_coe_eq hO x with ⟨c, hc⟩
  have hdisc : O.quaternionDisc =
      (4 * a * b * ((basisOneIJK (a : ℚ) 0 b).map e.toLinearEquiv).det c) ^ 2 :=
    (quaternionDisc_eq_quaternionDiscOfBasis h4 hO x).trans (quaternionDiscOfBasis_eq_sq e hc)
  rcases exists_quaternionDisc_eq_natCast h4 hO with ⟨n, hn⟩
  rcases exists_intCast_eq_of_sq_eq_natCast (hdisc.symm.trans hn) with ⟨w, hw⟩
  refine ⟨w, fun h0 ↦ ?_, by rw [hdisc, hw]⟩
  rw [h0, Int.cast_zero] at hw
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero four_ne_zero a.ne_zero) b.ne_zero)
    (((basisOneIJK _ 0 _).map e.toLinearEquiv).isUnit_det c).ne_zero hw

/-- **The reduced discriminant of an order is an integer** (LMFDB `shimcurve.disco`). -/
lemma exists_quaternionDiscrd_eq_natCast (h4 : finrank ℚ B = 4) (hO : O.IsQuaternionOrder) :
    ∃ d : ℕ, O.quaternionDiscrd = d := by
  rcases exists_quaternionDisc_eq_sq h4 hO with ⟨w, -, hw⟩
  exact ⟨w.natAbs, by rw [quaternionDiscrd_eq_abs hw, Nat.cast_natAbs, Int.cast_abs]⟩

/-- **The reduced discriminant of an order is positive** (LMFDB `shimcurve.disco`). -/
lemma quaternionDiscrd_pos (h4 : finrank ℚ B = 4) (hO : O.IsQuaternionOrder) :
    0 < O.quaternionDiscrd := by
  rcases exists_quaternionDisc_eq_sq h4 hO with ⟨w, hw₀, hw⟩
  rw [quaternionDiscrd_eq_abs hw]
  exact abs_pos.mpr (Int.cast_ne_zero.mpr hw₀)

/-- **The square of the reduced discriminant of an order is its discriminant** (LMFDB
`shimcurve.disco`). -/
lemma quaternionDiscrd_sq (h4 : finrank ℚ B = 4) (hO : O.IsQuaternionOrder) :
    O.quaternionDiscrd ^ 2 = O.quaternionDisc := by
  rcases exists_quaternionDisc_eq_sq h4 hO with ⟨w, -, hw⟩
  rw [quaternionDiscrd_eq_abs hw, sq_abs, hw]

end Subalgebra
