import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParabolicDecomposition
import Mathlib.Algebra.Group.Nat.Range
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import TauCeti.LinearAlgebra.Matrix.Divisibility
import TauCeti.LinearAlgebra.Matrix.SmithNormalForm

/-!
# The rank-one count behind the Weyl invariance of the Satake map

Let `p` be a prime. Every `2 × 2` integer matrix `m` with `|det m| = p^K` is, up to `GL(2, ℤ)` on
the left, a unique Hermite normal form `(p^{e₁}, j; 0, p^{e₂})` with `e₁ + e₂ = K` and
`0 ≤ j < p^{e₂}`; its triple `(e₁, e₂, j)` is `SiegelUpperHalfSpace.hnfData p m`. The right cosets
`GL(2, ℤ) m Q`, `Q ∈ SL(2, ℤ)`, are exactly those with the same `K` and the same content
`c = gcd(p^{min(e₁, e₂)}, j)` (Tau Ceti's `2 × 2` elementary divisor classification), and their
triples form the set `SiegelUpperHalfSpace.hnfSet p K c`. In it, the number `N(e₁, e₂)` of `j`
with given `(e₁, e₂)` is `p^{e₂ - c'} C(c')`, `c' = min(e₁, e₂)`, so that
`p^{e₁} N(e₁, e₂) = p^{e₂} N(e₂, e₁)`: this is the symmetry of the Satake map of `GL(2)`, and
`SiegelUpperHalfSpace.sum_hnfSet` is the resulting identity of sums.

`SiegelUpperHalfSpace.sum_mul_hnfData_eq` packages it for a finite set `X` with an action of
`SL(2, ℤ)` and a block `blk : X → M₂(ℤ)` on which `SL(2, ℤ)` acts by right multiplication up to
`GL(2, ℤ)` on the left: for a function `out` constant on the orbits,
`∑_v out(v) w'(e₁(v), e₂(v)) = ∑_v out(v) w(e₁(v), e₂(v))` whenever
`w'(e₁, e₂) = p^{e₁ - e₂} w(e₂, e₁)`. It rests on a general fact about orbits
(`SiegelUpperHalfSpace.sum_mul_eq_sum_mul_of_orbit`): an equivariant map hits each point of the
image of an orbit equally often.

## Main definitions

* `SiegelUpperHalfSpace.hnfMat`: the Hermite normal form `(p^{e₁}, j; 0, p^{e₂})` of a triple.
* `SiegelUpperHalfSpace.hnfData`: the triple of the Hermite normal form of a matrix.
* `SiegelUpperHalfSpace.hnfContent`: the content `gcd(p^{min(e₁, e₂)}, j)` of a triple.
* `SiegelUpperHalfSpace.hnfSet`: the triples of degree `K` and content `c`.

## Main results

* `SiegelUpperHalfSpace.sum_mul_eq_sum_mul_of_orbit`: sums over orbits through an equivariant map.
* `SiegelUpperHalfSpace.sum_hnfSet`: the rank-one symmetry of the counts.
* `SiegelUpperHalfSpace.sum_mul_hnfData_eq`: the rank-one reduction.
-/

open Matrix Finset

open scoped MatrixGroups

namespace SiegelUpperHalfSpace

/-! ### Sums over the orbits of a group action -/

/-- **Sums through an equivariant map over the orbits**: for an action of `G` on a finite set
`X`, a function `F` constant on the orbits and a map `φ` with `φ x = φ x' → φ (g x) = φ (g x')`,
`∑_x F(x) f(φ(x)) = ∑_x F(x) f'(φ(x))` as soon as `f` and `f'` have the same sum over the image
`{φ(g x) : g ∈ G}` of each orbit: each point of the image of an orbit is hit equally often. -/
lemma sum_mul_eq_sum_mul_of_orbit {G X Y R : Type*} [Group G] [MulAction G X] [Fintype X]
    [CommSemiring R] (φ : X → Y) (F : X → R) (f f' : Y → R) (hF : ∀ (g : G) x, F (g • x) = F x)
    (hφ : ∀ (g : G) x x', φ x = φ x' → φ (g • x) = φ (g • x'))
    (hf : ∀ x, ∃ T : Finset Y, (∀ y, y ∈ T ↔ ∃ g : G, φ (g • x) = y) ∧
      ∑ y ∈ T, f y = ∑ y ∈ T, f' y) :
    ∑ x, F x * f (φ x) = ∑ x, F x * f' (φ x) := by
  classical
  rw [sum_partition (MulAction.orbitRel G X), sum_partition (MulAction.orbitRel G X)]
  refine sum_congr rfl fun ω _ ↦ ?_
  induction ω using Quotient.inductionOn with
  | h x₀ =>
    have hO : (univ.filter fun y ↦ (⟦y⟧ : Quotient (MulAction.orbitRel G X)) = ⟦x₀⟧) =
        univ.filter fun y ↦ y ∈ MulAction.orbit G x₀ :=
      filter_congr fun y _ ↦ Quotient.eq.trans MulAction.orbitRel_apply
    have hFO (y : X) (hy : y ∈ univ.filter fun y ↦ y ∈ MulAction.orbit G x₀) : F y = F x₀ := by
      rcases (mem_filter.mp hy).2 with ⟨g, rfl⟩
      exact hF g x₀
    have hc (z : Y) (hz : z ∈ (univ.filter fun y ↦ y ∈ MulAction.orbit G x₀).image φ) :
        ((univ.filter fun y ↦ y ∈ MulAction.orbit G x₀).filter fun y ↦ φ y = z).card =
          ((univ.filter fun y ↦ y ∈ MulAction.orbit G x₀).filter fun y ↦ φ y = φ x₀).card := by
      rcases mem_image.mp hz with ⟨y₁, hy₁, rfl⟩
      rcases (mem_filter.mp hy₁).2 with ⟨g, rfl⟩
      refine card_nbij' (g⁻¹ • ·) (g • ·) (fun y hy ↦ ?_) (fun y hy ↦ ?_)
        (fun y _ ↦ smul_inv_smul g y) fun y _ ↦ inv_smul_smul g y
      · simp only [mem_coe, mem_filter, mem_univ, true_and] at hy ⊢
        refine ⟨MulAction.mem_orbit_of_mem_orbit g⁻¹ hy.1, ?_⟩
        rw [hφ g⁻¹ y _ hy.2, inv_smul_smul]
      · simp only [mem_coe, mem_filter, mem_univ, true_and] at hy ⊢
        exact ⟨MulAction.mem_orbit_of_mem_orbit g hy.1, hφ g y x₀ hy.2⟩
    have hsplit (u : Y → R) : ∑ y ∈ univ.filter (fun y ↦ y ∈ MulAction.orbit G x₀), F y * u (φ y) =
        F x₀ * (((univ.filter fun y ↦ y ∈ MulAction.orbit G x₀).filter fun y ↦ φ y = φ x₀).card •
          ∑ z ∈ (univ.filter fun y ↦ y ∈ MulAction.orbit G x₀).image φ, u z) := by
      rw [sum_congr rfl fun y hy ↦ by rw [hFO y hy], ← mul_sum, sum_comp,
        sum_congr rfl fun z hz ↦ by rw [hc z hz], ← smul_sum]
    rcases hf x₀ with ⟨T, hT, hsum⟩
    have himage : (univ.filter fun y ↦ y ∈ MulAction.orbit G x₀).image φ = T := by
      ext y
      simp only [mem_image, mem_filter, mem_univ, true_and, hT]
      constructor
      · rintro ⟨-, ⟨g, rfl⟩, h⟩
        exact ⟨g, h⟩
      · rintro ⟨g, h⟩
        exact ⟨g • x₀, ⟨g, rfl⟩, h⟩
    rw [hO, hsplit, hsplit, himage, hsum]

variable (p : ℕ) {m N : Matrix (Fin 2) (Fin 2) ℤ} {t : ℕ × ℕ × ℕ}

/-! ### Hermite normal forms of `2 × 2` matrices -/

/-- The **data of an upper triangular integer matrix** `(a, b; 0, d)`, the triple
`(v_p |a|, v_p |d|, sgn(a) b mod |d|)` (LMFDB `mf.siegel.lift`, through the Weyl invariance of the
Satake map). -/
def upperData (N : Matrix (Fin 2) (Fin 2) ℤ) : ℕ × ℕ × ℕ :=
  (padicValNat p (N 0 0).natAbs, padicValNat p (N 1 1).natAbs,
    (((N 0 0).sign * N 0 1) % ((N 1 1).natAbs : ℤ)).toNat)

/-- The **Hermite normal form** `(p^{e₁}, j; 0, p^{e₂})` of a triple `(e₁, e₂, j)` (LMFDB
`mf.siegel.lift`, through the Weyl invariance of the Satake map). -/
def hnfMat (t : ℕ × ℕ × ℕ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(p : ℤ) ^ t.1, t.2.2; 0, (p : ℤ) ^ t.2.1]

/-- The **content** `gcd(p^{min(e₁, e₂)}, j)` of a triple `(e₁, e₂, j)`, the greatest common divisor
of the entries of its Hermite normal form (LMFDB `mf.siegel.lift`, through the Weyl invariance of
the Satake map). -/
def hnfContent (t : ℕ × ℕ × ℕ) : ℕ :=
  Nat.gcd (p ^ min t.1 t.2.1) t.2.2

lemma exists_GL_mul_apply_one_zero (m : Matrix (Fin 2) (Fin 2) ℤ) :
    ∃ U : GL (Fin 2) ℤ, ((U : Matrix (Fin 2) (Fin 2) ℤ) * m) 1 0 = 0 := by
  rcases SymplecticGroup.exists_SL2Z_eq_gcd (m 0 0) (m 1 0) with ⟨U, -, hU⟩
  exact ⟨U.toGL, by simpa [Matrix.mul_apply] using hU⟩

/-- The triple `(e₁, e₂, j)` of the **Hermite normal form** of `m` (LMFDB `mf.siegel.lift`, through
the Weyl invariance of the Satake map): the data of an upper triangular `U m`, `U ∈ GL(2, ℤ)`. For
`|det m| = p^K`, `GL(2, ℤ) m` contains `(p^{e₁}, j; 0, p^{e₂})`. -/
noncomputable def hnfData (m : Matrix (Fin 2) (Fin 2) ℤ) : ℕ × ℕ × ℕ :=
  upperData p (((exists_GL_mul_apply_one_zero m).choose : Matrix (Fin 2) (Fin 2) ℤ) * m)

lemma isUnit_det_coe (V : GL (Fin 2) ℤ) : IsUnit (V : Matrix (Fin 2) (Fin 2) ℤ).det :=
  V.isUnit.map detMonoidHom

lemma apply_zero_zero_ne_zero (hN : N 1 0 = 0) (hN₀ : N.det ≠ 0) : N 0 0 ≠ 0 :=
  fun h ↦ hN₀ (by rw [det_fin_two, h, hN, zero_mul, mul_zero, sub_zero])

lemma upperData_mul_left (V : GL (Fin 2) ℤ) (hN : N 1 0 = 0) (hN₀ : N 0 0 ≠ 0)
    (hV : ((V : Matrix (Fin 2) (Fin 2) ℤ) * N) 1 0 = 0) :
    upperData p ((V : Matrix (Fin 2) (Fin 2) ℤ) * N) = upperData p N := by
  have h₁₀ : (V : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0 := by
    simpa [Matrix.mul_apply, hN, hN₀] using hV
  have hdet : IsUnit ((V : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (V : Matrix (Fin 2) (Fin 2) ℤ) 1 1) := by
    simpa [det_fin_two, h₁₀] using isUnit_det_coe V
  rcases Int.isUnit_iff.mp (isUnit_of_mul_isUnit_left hdet) with h₀ | h₀ <;>
  rcases Int.isUnit_iff.mp (isUnit_of_mul_isUnit_right hdet) with h₁ | h₁ <;>
  · simp only [upperData, Matrix.mul_apply, Fin.sum_univ_two, hN, h₁₀, h₀, h₁]
    simp [mul_add, ← mul_assoc]

lemma hnfData_eq (U : GL (Fin 2) ℤ) (hU : ((U : Matrix (Fin 2) (Fin 2) ℤ) * m) 1 0 = 0)
    (hm : m.det ≠ 0) : hnfData p m = upperData p ((U : Matrix (Fin 2) (Fin 2) ℤ) * m) := by
  have h₀ : (((exists_GL_mul_apply_one_zero m).choose : Matrix (Fin 2) (Fin 2) ℤ) * m).det ≠ 0 := by
    rw [det_mul]
    exact mul_ne_zero (isUnit_det_coe _).ne_zero hm
  have e : (((U * (exists_GL_mul_apply_one_zero m).choose⁻¹ : GL (Fin 2) ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ) * (((exists_GL_mul_apply_one_zero m).choose :
        Matrix (Fin 2) (Fin 2) ℤ) * m) = (U : Matrix (Fin 2) (Fin 2) ℤ) * m := by
    rw [Units.val_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ m, Units.inv_mul, Matrix.one_mul]
  rw [← e]
  exact (upperData_mul_left p (U * (exists_GL_mul_apply_one_zero m).choose⁻¹)
    (exists_GL_mul_apply_one_zero m).choose_spec
    (apply_zero_zero_ne_zero (exists_GL_mul_apply_one_zero m).choose_spec h₀) (e ▸ hU)).symm

lemma hnfData_mul_left (V : GL (Fin 2) ℤ) (hm : m.det ≠ 0) :
    hnfData p ((V : Matrix (Fin 2) (Fin 2) ℤ) * m) = hnfData p m := by
  have e : (((exists_GL_mul_apply_one_zero m).choose * V⁻¹ : GL (Fin 2) ℤ) :
      Matrix (Fin 2) (Fin 2) ℤ) * ((V : Matrix (Fin 2) (Fin 2) ℤ) * m) =
        ((exists_GL_mul_apply_one_zero m).choose : Matrix (Fin 2) (Fin 2) ℤ) * m := by
    rw [Units.val_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ _ m, Units.inv_mul, Matrix.one_mul]
  rw [hnfData_eq p ((exists_GL_mul_apply_one_zero m).choose * V⁻¹)
    (e ▸ (exists_GL_mul_apply_one_zero m).choose_spec)
    (by rw [det_mul]; exact mul_ne_zero (isUnit_det_coe V).ne_zero hm), e]
  rfl

lemma hnfData_eq_upperData (hN : N 1 0 = 0) (hN₀ : N.det ≠ 0) : hnfData p N = upperData p N := by
  simpa using hnfData_eq p 1 (by simpa using hN) hN₀

lemma det_hnfMat : (hnfMat p t).det = (p : ℤ) ^ (t.1 + t.2.1) := by
  simp [hnfMat, pow_add]

/-! ### Contents -/

lemma forall_dvd_mul_mul_iff (V W : GL (Fin 2) ℤ) {e : ℤ} :
    (∀ i j, e ∣ ((V : Matrix (Fin 2) (Fin 2) ℤ) * m * W) i j) ↔ ∀ i j, e ∣ m i j := by
  refine ⟨fun h i j ↦ ?_, fun h ↦ dvd_mul_mul_apply h _ _⟩
  have h' : e ∣ (((V⁻¹ : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *
      ((V : Matrix (Fin 2) (Fin 2) ℤ) * m * W) * ((W⁻¹ : GL (Fin 2) ℤ) :
        Matrix (Fin 2) (Fin 2) ℤ)) i j :=
    dvd_mul_mul_apply h _ _ i j
  rwa [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc,
    Units.mul_inv, Matrix.mul_one] at h'

lemma forall_dvd_hnfMat_iff {e : ℤ} : (∀ i j, e ∣ hnfMat p t i j) ↔ e ∣ (hnfContent p t : ℤ) := by
  have hmin : e ∣ (p : ℤ) ^ t.1 ∧ e ∣ (p : ℤ) ^ t.2.1 ↔ e ∣ (p : ℤ) ^ min t.1 t.2.1 := by
    rcases le_total t.1 t.2.1 with h | h
    · rw [min_eq_left h]
      exact ⟨And.left, fun he ↦ ⟨he, he.trans (pow_dvd_pow _ h)⟩⟩
    · rw [min_eq_right h]
      exact ⟨And.right, fun he ↦ ⟨he.trans (pow_dvd_pow _ h), he⟩⟩
  rw [hnfContent, Int.dvd_natCast, Nat.dvd_gcd_iff, ← Int.dvd_natCast, ← Int.dvd_natCast,
    Nat.cast_pow, ← hmin]
  simp only [Fin.forall_fin_two, hnfMat, of_apply, cons_val', cons_val_zero, cons_val_one, dvd_zero]
  tauto

/-! ### The triples of given degree and content -/

/-- The **Hermite triples of degree `K` and content `c`** (LMFDB `mf.siegel.lift`, through the Weyl
invariance of the Satake map): the `(K - e, e, j)` with `e ≤ K`, `j < p^e` and
`gcd(p^{min(K - e, e)}, j) = c`, the Hermite normal forms of the right cosets of `GL(2, ℤ)` in a
double coset of `GL(2, ℤ)` and `SL(2, ℤ)` of determinant `±p^K`. -/
def hnfSet (K c : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (range (K + 1)).biUnion fun e ↦
    ((range (p ^ e)).filter fun j ↦ Nat.gcd (p ^ min (K - e) e) j = c).image fun j ↦ (K - e, e, j)

lemma mem_hnfSet {K c : ℕ} :
    t ∈ hnfSet p K c ↔ t.1 + t.2.1 = K ∧ t.2.2 < p ^ t.2.1 ∧ hnfContent p t = c := by
  rcases t with ⟨a, b, j⟩
  simp only [hnfSet, mem_biUnion, mem_range, mem_image, mem_filter, Prod.mk.injEq]
  constructor
  · rintro ⟨e, he, j', ⟨hj', hc⟩, rfl, rfl, rfl⟩
    exact ⟨by omega, hj', hc⟩
  · rintro ⟨hK, hj, hc⟩
    refine ⟨b, by omega, j, ⟨hj, ?_⟩, by omega, rfl, rfl⟩
    rwa [Nat.sub_eq_of_eq_add hK.symm]

lemma card_filter_range_mul_mod (N k : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    ((range (k * N)).filter fun j ↦ P (j % N)).card = k * ((range N).filter P).card := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [add_mul, one_mul, range_add_eq_union, filter_union, card_union_of_disjoint
      (disjoint_filter_filter (disjoint_range_addLeftEmbedding _ _)), ih, filter_map, card_map,
      add_mul, one_mul]
    congr 2
    exact filter_congr fun i hi ↦ by
      rw [Function.comp_apply, addLeftEmbedding_apply, add_comm, Nat.add_mul_mod_self_right,
        Nat.mod_eq_of_lt (mem_range.mp hi)]

lemma card_filter_range_mod (q : ℕ) {a b : ℕ} (hab : a ≤ b) (P : ℕ → Prop) [DecidablePred P] :
    ((range (q ^ b)).filter fun j ↦ P (j % q ^ a)).card =
      q ^ (b - a) * ((range (q ^ a)).filter P).card := by
  rw [← card_filter_range_mul_mod, ← pow_add, Nat.sub_add_cancel hab]

lemma sum_hnfSet_eq_sum_range {M : Type*} [AddCommMonoid M] (K c : ℕ) (F : ℕ → ℕ → M) :
    ∑ t ∈ hnfSet p K c, F t.1 t.2.1 = ∑ e ∈ range (K + 1),
      ((range (p ^ e)).filter fun j ↦ Nat.gcd (p ^ min (K - e) e) j = c).card • F (K - e) e := by
  rw [hnfSet, sum_biUnion]
  · refine sum_congr rfl fun e _ ↦ ?_
    rw [sum_image fun j _ j' _ h ↦ by simpa using h]
    exact sum_const (F (K - e) e)
  · intro e _ e' _ hee'
    rw [Function.onFun, disjoint_left]
    rintro t ht ht'
    rcases mem_image.mp ht with ⟨j, -, rfl⟩
    rcases mem_image.mp ht' with ⟨j', -, h⟩
    exact hee' (congrArg (fun t : ℕ × ℕ × ℕ ↦ t.2.1) h).symm

variable [Fact p.Prime]

lemma det_ne_zero_of_natAbs_eq {K : ℕ} (hm : m.det.natAbs = p ^ K) : m.det ≠ 0 :=
  fun h ↦ pow_ne_zero K (Fact.out : p.Prime).ne_zero (by rw [← hm, h, Int.natAbs_zero])

lemma hnfData_hnfMat (ht : t.2.2 < p ^ t.2.1) : hnfData p (hnfMat p t) = t := by
  have hp : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [hnfData_eq_upperData p (by simp [hnfMat]) (by rw [det_hnfMat]; exact pow_ne_zero _ hp)]
  have hj : ((t.2.2 : ℤ) % ((p ^ t.2.1 : ℕ) : ℤ)) = t.2.2 :=
    Int.emod_eq_of_lt (Nat.cast_nonneg _) (by exact_mod_cast ht)
  simp only [upperData, hnfMat, of_apply, cons_val', cons_val_zero, cons_val_one, Int.natAbs_pow,
    Int.natAbs_natCast, padicValNat.prime_pow]
  rw [Int.sign_eq_one_of_pos (pow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) _), one_mul, hj,
    Int.toNat_natCast]

lemma exists_natAbs_eq_pow {K : ℕ} (hm : m.det.natAbs = p ^ K) (hN : N 1 0 = 0) (V : GL (Fin 2) ℤ)
    (hV : (V : Matrix (Fin 2) (Fin 2) ℤ) * m = N) :
    ∃ e₁ e₂ : ℕ, (N 0 0).natAbs = p ^ e₁ ∧ (N 1 1).natAbs = p ^ e₂ ∧ e₁ + e₂ = K := by
  have hp : p.Prime := Fact.out
  have hdetN : N.det = N 0 0 * N 1 1 := by
    rw [det_fin_two, hN, mul_zero, sub_zero]
  have hdetV : N.det.natAbs = m.det.natAbs := by
    rw [← hV, det_mul, Int.natAbs_mul, Int.isUnit_iff_natAbs_eq.mp (isUnit_det_coe V), one_mul]
  have hdet : (N 0 0).natAbs * (N 1 1).natAbs = p ^ K := by
    rw [← Int.natAbs_mul, ← hdetN, hdetV, hm]
  rcases (Nat.dvd_prime_pow hp).mp (Dvd.intro _ hdet) with ⟨e₁, -, he₁⟩
  rcases (Nat.dvd_prime_pow hp).mp (Dvd.intro_left _ hdet) with ⟨e₂, -, he₂⟩
  refine ⟨e₁, e₂, he₁, he₂, Nat.pow_right_injective hp.two_le ?_⟩
  simp only
  rw [pow_add, ← he₁, ← he₂, hdet]

lemma exists_mul_eq_hnfMat_of_upper {e₁ e₂ : ℕ} (hN : N 1 0 = 0) (h₁ : (N 0 0).natAbs = p ^ e₁)
    (h₂ : (N 1 1).natAbs = p ^ e₂) :
    ∃ V : GL (Fin 2) ℤ, (V : Matrix (Fin 2) (Fin 2) ℤ) * N = hnfMat p (upperData p N) := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hN₀ : N 0 0 ≠ 0 := fun h ↦ pow_ne_zero e₁ hp (by rw [← h₁, h, Int.natAbs_zero])
  have hN₁ : N 1 1 ≠ 0 := fun h ↦ pow_ne_zero e₂ hp (by rw [← h₂, h, Int.natAbs_zero])
  have hs₀ : (N 0 0).sign * (N 0 0).sign = 1 :=
    Int.isUnit_mul_self (Int.isUnit_iff_natAbs_eq.mpr (Int.natAbs_sign_of_ne_zero hN₀))
  have hs₁ : (N 1 1).sign * (N 1 1).sign = 1 :=
    Int.isUnit_mul_self (Int.isUnit_iff_natAbs_eq.mpr (Int.natAbs_sign_of_ne_zero hN₁))
  have hd : ((N 1 1).natAbs : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr (Int.natAbs_ne_zero.mpr hN₁)
  have hD : !![(N 0 0).sign, 0; 0, (N 1 1).sign] * !![(N 0 0).sign, 0; 0, (N 1 1).sign] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hs₀, hs₁]
  have hE : !![1, -(((N 0 0).sign * N 0 1) / ((N 1 1).natAbs : ℤ)); 0, 1] *
      !![1, ((N 0 0).sign * N 0 1) / ((N 1 1).natAbs : ℤ); 0, 1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hE' : !![1, ((N 0 0).sign * N 0 1) / ((N 1 1).natAbs : ℤ); 0, 1] *
      !![1, -(((N 0 0).sign * N 0 1) / ((N 1 1).natAbs : ℤ)); 0, 1] = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hj : ((((N 0 0).sign * N 0 1) % ((N 1 1).natAbs : ℤ)).toNat : ℤ) = (N 0 0).sign * N 0 1 -
      ((N 1 1).natAbs : ℤ) * (((N 0 0).sign * N 0 1) / ((N 1 1).natAbs : ℤ)) := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hd), Int.emod_def]
  have hA : (p : ℤ) ^ padicValNat p (N 0 0).natAbs = ((N 0 0).natAbs : ℤ) := by
    rw [h₁, padicValNat.prime_pow, Nat.cast_pow]
  have hB : (p : ℤ) ^ padicValNat p (N 1 1).natAbs = ((N 1 1).natAbs : ℤ) := by
    rw [h₂, padicValNat.prime_pow, Nat.cast_pow]
  have hmat : hnfMat p (upperData p N) = !![((N 0 0).natAbs : ℤ), (N 0 0).sign * N 0 1 -
      ((N 1 1).natAbs : ℤ) * (((N 0 0).sign * N 0 1) / ((N 1 1).natAbs : ℤ));
        0, ((N 1 1).natAbs : ℤ)] := by
    rw [hnfMat, upperData, hA, hB, hj]
  refine ⟨⟨_, _, hE, hE'⟩ * ⟨_, _, hD, hD⟩, ?_⟩
  rw [hmat]
  ext i j
  have h₁' : (N 1 1).sign * N 1 1 = |N 1 1| :=
    (Int.sign_mul_self_eq_natAbs _).trans (Int.natCast_natAbs _)
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, hN]
  linear_combination (-((N 0 0).sign * N 0 1 / |N 1 1|)) * h₁'

lemma exists_mul_eq_hnfMat {K : ℕ} (hm : m.det.natAbs = p ^ K) :
    ∃ V : GL (Fin 2) ℤ, (V : Matrix (Fin 2) (Fin 2) ℤ) * m = hnfMat p (hnfData p m) := by
  rcases exists_natAbs_eq_pow p hm (exists_GL_mul_apply_one_zero m).choose_spec _ rfl with
    ⟨e₁, e₂, h₁, h₂, -⟩
  rcases exists_mul_eq_hnfMat_of_upper p (exists_GL_mul_apply_one_zero m).choose_spec h₁ h₂ with
    ⟨V, hV⟩
  refine ⟨V * (exists_GL_mul_apply_one_zero m).choose, ?_⟩
  rw [Units.val_mul, Matrix.mul_assoc, hV]
  rfl

lemma hnfData_snd_snd_lt {K : ℕ} (hm : m.det.natAbs = p ^ K) :
    (hnfData p m).2.2 < p ^ (hnfData p m).2.1 := by
  rcases exists_natAbs_eq_pow p hm (exists_GL_mul_apply_one_zero m).choose_spec _ rfl with
    ⟨e₁, e₂, -, h₂, -⟩
  have hd : (0 : ℤ) < (p ^ e₂ : ℕ) := Nat.cast_pos.mpr (pow_pos (Fact.out : p.Prime).pos _)
  simp only [hnfData, upperData, h₂, padicValNat.prime_pow]
  exact (Int.toNat_lt (Int.emod_nonneg _ hd.ne')).mpr (Int.emod_lt_of_pos _ hd)

lemma hnfData_fst_add {K : ℕ} (hm : m.det.natAbs = p ^ K) :
    (hnfData p m).1 + (hnfData p m).2.1 = K := by
  rcases exists_natAbs_eq_pow p hm (exists_GL_mul_apply_one_zero m).choose_spec _ rfl with
    ⟨e₁, e₂, h₁, h₂, h⟩
  simp only [hnfData, upperData, h₁, h₂, padicValNat.prime_pow, h]

lemma hnfContent_mul_mul {K : ℕ} (hm : m.det.natAbs = p ^ K) (V W : GL (Fin 2) ℤ) :
    hnfContent p (hnfData p ((V : Matrix (Fin 2) (Fin 2) ℤ) * m * W)) =
      hnfContent p (hnfData p m) := by
  have hm' : ((V : Matrix (Fin 2) (Fin 2) ℤ) * m * W).det.natAbs = p ^ K := by
    rw [det_mul, det_mul, Int.natAbs_mul, Int.natAbs_mul,
      Int.isUnit_iff_natAbs_eq.mp (isUnit_det_coe V),
      Int.isUnit_iff_natAbs_eq.mp (isUnit_det_coe W), one_mul, mul_one, hm]
  rcases exists_mul_eq_hnfMat p hm with ⟨V₁, hV₁⟩
  rcases exists_mul_eq_hnfMat p hm' with ⟨V₂, hV₂⟩
  have key (e : ℤ) : e ∣ (hnfContent p (hnfData p ((V : Matrix (Fin 2) (Fin 2) ℤ) * m * W)) : ℤ) ↔
      e ∣ (hnfContent p (hnfData p m) : ℤ) := by
    have h₁ : (∀ i j, e ∣ ((V₂ : Matrix (Fin 2) (Fin 2) ℤ) *
        ((V : Matrix (Fin 2) (Fin 2) ℤ) * m * W) * ((1 : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ))
          i j) ↔ ∀ i j, e ∣ ((V : Matrix (Fin 2) (Fin 2) ℤ) * m * W) i j :=
      forall_dvd_mul_mul_iff V₂ 1
    have h₂ : (∀ i j, e ∣ ((V₁ : Matrix (Fin 2) (Fin 2) ℤ) * m *
        ((1 : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ)) i j) ↔ ∀ i j, e ∣ m i j :=
      forall_dvd_mul_mul_iff V₁ 1
    rw [Units.val_one, Matrix.mul_one] at h₁ h₂
    rw [← forall_dvd_hnfMat_iff, ← forall_dvd_hnfMat_iff, ← hV₂, ← hV₁, h₁, h₂,
      forall_dvd_mul_mul_iff]
  exact Nat.dvd_antisymm (Int.natCast_dvd_natCast.mp ((key _).mp dvd_rfl))
    (Int.natCast_dvd_natCast.mp ((key _).mpr dvd_rfl))

lemma hnfData_mem_hnfSet {K : ℕ} (hm : m.det.natAbs = p ^ K) :
    hnfData p m ∈ hnfSet p K (hnfContent p (hnfData p m)) :=
  (mem_hnfSet p).mpr ⟨hnfData_fst_add p hm, hnfData_snd_snd_lt p hm, rfl⟩

lemma exists_hnfData_mul_eq {K : ℕ} (hm : m.det.natAbs = p ^ K)
    (ht : t ∈ hnfSet p K (hnfContent p (hnfData p m))) :
    ∃ Q : SL(2, ℤ), hnfData p (m * (Q : Matrix (Fin 2) (Fin 2) ℤ)) = t := by
  rcases (mem_hnfSet p).mp ht with ⟨h₁, h₂, h₃⟩
  rcases exists_mul_eq_hnfMat p hm with ⟨V, hV⟩
  have hpK : (p : ℤ) ^ K ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  have hdetA : (hnfMat p (hnfData p m)).det = (p : ℤ) ^ K := by
    rw [det_hnfMat, hnfData_fst_add p hm]
  have hdetB : (hnfMat p t).det = (p : ℤ) ^ K := by
    rw [det_hnfMat, h₁]
  rcases exists_SL_mul_mul_eq_of_det_eq_of_dvd_iff (hdetA ▸ hpK) (hdetB.trans hdetA.symm)
    (fun e ↦ by rw [forall_dvd_hnfMat_iff, forall_dvd_hnfMat_iff, h₃]) with ⟨P, Q, hPQ⟩
  refine ⟨Q, ?_⟩
  have e₁ : m * (Q : Matrix (Fin 2) (Fin 2) ℤ) = ((V⁻¹ : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) *
      (hnfMat p (hnfData p m) * (Q : Matrix (Fin 2) (Fin 2) ℤ)) := by
    rw [← hV, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have e₂ : hnfMat p (hnfData p m) * (Q : Matrix (Fin 2) (Fin 2) ℤ) =
      ((P⁻¹ : SL(2, ℤ)).toGL : Matrix (Fin 2) (Fin 2) ℤ) * hnfMat p t := by
    rw [SpecialLinearGroup.coe_GL_coe_matrix, ← hPQ, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      ← SpecialLinearGroup.coe_mul, inv_mul_cancel, SpecialLinearGroup.coe_one, Matrix.one_mul]
  have hAQ : (hnfMat p (hnfData p m) * (Q : Matrix (Fin 2) (Fin 2) ℤ)).det ≠ 0 := by
    rw [det_mul, SpecialLinearGroup.det_coe, mul_one, hdetA]
    exact hpK
  have hB : (hnfMat p t).det ≠ 0 := by
    rw [hdetB]
    exact hpK
  rw [e₁, hnfData_mul_left p _ hAQ, e₂, hnfData_mul_left p _ hB, hnfData_hnfMat p h₂]

/-- **The rank-one symmetry**: over the Hermite triples of degree `K` and content `c`, the number of
triples with diagonal `(p^{e₁}, p^{e₂})` times `p^{e₁}` is symmetric in `e₁` and `e₂`, so
`∑_t p^{e₁ - e₂} w(e₂, e₁) = ∑_t w(e₁, e₂)`. -/
lemma sum_hnfSet {M : Type*} [AddCommMonoid M] [Module ℂ M] (K c : ℕ) (w : ℕ → ℕ → M) :
    ∑ t ∈ hnfSet p K c, ((p : ℂ) ^ (t.1 : ℤ) * (p : ℂ) ^ (-(t.2.1 : ℤ))) • w t.2.1 t.1 =
      ∑ t ∈ hnfSet p K c, w t.1 t.2.1 := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hcount (e : ℕ) : ((range (p ^ e)).filter fun j ↦ Nat.gcd (p ^ min (K - e) e) j = c).card =
      p ^ (e - min (K - e) e) * ((range (p ^ min (K - e) e)).filter fun j ↦
        Nat.gcd (p ^ min (K - e) e) j = c).card := by
    rw [← card_filter_range_mod p (min_le_right _ _)]
    exact congrArg card (filter_congr fun j _ ↦ by
      rw [Nat.gcd_rec (p ^ min (K - e) e) j, Nat.gcd_comm (j % _)])
  rw [sum_hnfSet_eq_sum_range p K c fun a b ↦ ((p : ℂ) ^ (a : ℤ) * (p : ℂ) ^ (-(b : ℤ))) • w b a,
    sum_hnfSet_eq_sum_range p K c w, ← sum_range_reflect]
  refine sum_congr rfl fun e he ↦ ?_
  have heK : e ≤ K := Nat.lt_succ_iff.mp (mem_range.mp he)
  rw [Nat.add_sub_cancel, hcount (K - e), hcount e, Nat.sub_sub_self heK, min_comm e (K - e),
    ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 1
  have hnat : p ^ (K - e - min (K - e) e) * ((range (p ^ min (K - e) e)).filter fun j ↦
      Nat.gcd (p ^ min (K - e) e) j = c).card * p ^ e = p ^ (e - min (K - e) e) *
        ((range (p ^ min (K - e) e)).filter fun j ↦ Nat.gcd (p ^ min (K - e) e) j = c).card *
          p ^ (K - e) := by
    rw [mul_right_comm, ← pow_add, mul_right_comm _ _ (p ^ (K - e)), ← pow_add]
    congr 2
    omega
  have hc : ((p ^ (K - e - min (K - e) e) * ((range (p ^ min (K - e) e)).filter fun j ↦
      Nat.gcd (p ^ min (K - e) e) j = c).card : ℕ) : ℂ) * (p : ℂ) ^ e =
        ((p ^ (e - min (K - e) e) * ((range (p ^ min (K - e) e)).filter fun j ↦
          Nat.gcd (p ^ min (K - e) e) j = c).card : ℕ) : ℂ) * (p : ℂ) ^ (K - e) := by
    exact_mod_cast hnat
  rw [zpow_natCast, zpow_neg (p : ℂ), zpow_natCast, ← mul_assoc, hc, mul_assoc,
    mul_inv_cancel₀ (pow_ne_zero _ hp), mul_one]

/-- **The rank-one reduction**: let `SL(2, ℤ)` act on a finite set `X`, with a block
`blk : X → M₂(ℤ)` of determinant `±p^{K(v)}` such that `blk(h v) ∈ GL(2, ℤ) blk(v) h⁻¹`. For a
function `out` constant on the orbits and `w'(e₁, e₂) = p^{e₁ - e₂} w(e₂, e₁)`,
`∑_v out(v) w'(e₁(v), e₂(v)) = ∑_v out(v) w(e₁(v), e₂(v))`, `(e₁(v), e₂(v))` being the diagonal
exponents of the Hermite normal form of `blk(v)`. -/
lemma sum_mul_hnfData_eq {X M : Type*} [Fintype X] [hX : MulAction SL(2, ℤ) X] [CommRing M]
    [Algebra ℂ M] (blk : X → Matrix (Fin 2) (Fin 2) ℤ)
    (hK : ∀ v, ∃ K : ℕ, (blk v).det.natAbs = p ^ K)
    (hact : ∀ (h : SL(2, ℤ)) v, ∃ U : GL (Fin 2) ℤ,
      blk (h • v) = U * blk v * ((h⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) (out : X → M)
    (hout : ∀ (h : SL(2, ℤ)) v, out (h • v) = out v) (w w' : ℕ → ℕ → M)
    (hw : ∀ e₁ e₂, w' e₁ e₂ = ((p : ℂ) ^ (e₁ : ℤ) * (p : ℂ) ^ (-(e₂ : ℤ))) • w e₂ e₁) :
    ∑ v, out v * w' (hnfData p (blk v)).1 (hnfData p (blk v)).2.1 =
      ∑ v, out v * w (hnfData p (blk v)).1 (hnfData p (blk v)).2.1 := by
  choose K hK using hK
  have hdetQ (v : X) (Q : SL(2, ℤ)) : (blk v * (Q : Matrix (Fin 2) (Fin 2) ℤ)).det ≠ 0 := by
    rw [det_mul, SpecialLinearGroup.det_coe, mul_one]
    exact det_ne_zero_of_natAbs_eq p (hK v)
  have hact' (h : SL(2, ℤ)) (v : X) : hnfData p (blk (h • v)) =
      hnfData p (blk v * ((h⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
    rcases hact h v with ⟨U, hU⟩
    rw [hU, Matrix.mul_assoc, hnfData_mul_left p U (hdetQ v _)]
  have hblk (v : X) (Q : SL(2, ℤ)) : hnfData p (blk v * (Q : Matrix (Fin 2) (Fin 2) ℤ)) =
      hnfData p (hnfMat p (hnfData p (blk v)) * (Q : Matrix (Fin 2) (Fin 2) ℤ)) := by
    rcases exists_mul_eq_hnfMat p (hK v) with ⟨V, hV⟩
    rw [← hV, Matrix.mul_assoc, hnfData_mul_left p V (hdetQ v Q)]
  refine sum_mul_eq_sum_mul_of_orbit (G := SL(2, ℤ)) (fun v ↦ hnfData p (blk v)) out
    (fun t ↦ w' t.1 t.2.1) (fun t ↦ w t.1 t.2.1) hout (fun h v v' hvv' ↦ ?_) fun v ↦
      ⟨hnfSet p (K v) (hnfContent p (hnfData p (blk v))), fun t ↦ ⟨fun ht ↦ ?_, ?_⟩, ?_⟩
  · rw [hact', hact', hblk, hblk, hvv']
  · rcases exists_hnfData_mul_eq p (hK v) ht with ⟨Q, hQ⟩
    exact ⟨Q⁻¹, by rw [hact', inv_inv, hQ]⟩
  · rintro ⟨h, rfl⟩
    have hm : (blk v * ((h⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).det.natAbs = p ^ K v := by
      rw [det_mul, SpecialLinearGroup.det_coe, mul_one, hK v]
    have hc : hnfContent p (hnfData p (((1 : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) * blk v *
        (((h⁻¹ : SL(2, ℤ)).toGL : GL (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ))) =
          hnfContent p (hnfData p (blk v)) :=
      hnfContent_mul_mul p (hK v) 1 (h⁻¹).toGL
    rw [Units.val_one, Matrix.one_mul, SpecialLinearGroup.coe_GL_coe_matrix] at hc
    rw [hact', ← hc]
    exact hnfData_mem_hnfSet p hm
  · simp only [hw]
    exact sum_hnfSet p (K v) _ w

end SiegelUpperHalfSpace
