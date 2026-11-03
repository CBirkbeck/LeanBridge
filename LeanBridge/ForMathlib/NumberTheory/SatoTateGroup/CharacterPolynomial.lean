import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.HodgeCircle
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.KoikeTeradaMonomial
import Mathlib.Algebra.MvPolynomial.Supported
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# The irreducible characters of `USp(2g)` as integer polynomials

Each irreducible character of `USp(2g)` is an integer polynomial in `a₁, …, a_g`, and the moments
`E[χᵢ χⱼ]` are the integer linear combinations of the mixed moments `E[a₁^{e₁} ⋯ a_g^{e_g}]`
corresponding to the terms of `χᵢ χⱼ` (LMFDB `st_group.moment_matrix`). The LMFDB computes the
polynomials with the Brauer–Klimyk formula and the algorithm of Shieh, a method of computation that
is not formalised; here they are read off the determinant of Koike and Terada, using
`eᵢ = (-1)ⁱ aᵢ` and `e_{2g - i} = eᵢ` on `USp(2g)`. If `G` contains `-1`, the mixed moments of odd
weighted degree vanish, so that these combinations only involve entries of the moment simplex. The
knowls do not say why they vanish (LMFDB `st_group.moment_simplex`: "symmetry constraints") and
a `SatoTateGroup` need not contain `-1`, the trivial group being one; but the Sato–Tate group of a
motive of odd weight does, by its Hodge circle.

## Main definitions

* `SatoTateGroup.esymmPolynomial`: the integer polynomial in `a₁, …, a_g` which is `e_m` on
  `USp(2g)`.
* `SatoTateGroup.symplecticPolynomial`: the integer polynomial in `a₁, …, a_g` which is the
  irreducible character of highest weight `e₁^{c₁} ⋯ e_g^{c_g}`.

## Main results

* `SatoTateGroup.symplecticPolynomial_mem_supported`: this polynomial only involves `a₁, …, a_g`.
* `SatoTateGroup.symplecticCharacter_eq_aeval`: its value is the Koike–Terada function.
* `SatoTateGroup.HasSymplecticMonomial.irreducibleCharacter_eq_aeval`: so every irreducible
  character of `USp(2g)` is the value of such a polynomial.
* `SatoTateGroup.symplecticMomentMatrix_eq_sum`: the moments of the Koike–Terada functions as
  integer linear combinations of mixed moments.
* `SatoTateGroup.momentMatrix_eq_sum`: the same for the moment matrix over the irreducible
  characters.
* `SatoTateGroup.mixedMoment_eq_zero_of_odd`: the mixed moments of odd weighted degree vanish if `G`
  contains `-1`.
* `SatoTateGroup.mem_momentSimplexRow`: so each nonzero term is an entry of the moment simplex.
* `SatoTateGroup.neg_one_mem_of_hasHodgeEigenvalues`: a Sato–Tate group of odd weight contains `-1`
  if it has a Hodge circle with the Hodge numbers of a motive.
-/

open Matrix MeasureTheory MvPolynomial TauCeti

namespace SatoTateGroup

variable {n : Type*} [Fintype n] [DecidableEq n] (i : ℕ)

section Polynomial

variable (g : ℕ)

/-- The integer polynomial in `a₁, …, a_g` which is the elementary symmetric function `e_m` of the
eigenvalues on `USp(2g)`, for an integer `m`: `e_m = (-1)^m a_m` for `0 ≤ m ≤ g` with `a₀ = 1`,
`e_m = e_{2g - m}` for `g ≤ m ≤ 2g`, and `0` otherwise. -/
noncomputable def esymmPolynomial (m : ℤ) : MvPolynomial ℕ ℤ :=
  if 0 ≤ m ∧ m ≤ g + g then
    (-1) ^ m.toNat * if min m.toNat (g + g - m.toNat) = 0 then 1
      else X (min m.toNat (g + g - m.toNat))
  else 0

lemma esymmPolynomial_mem_supported (m : ℤ) : esymmPolynomial g m ∈ supported ℤ (Set.Icc 1 g) := by
  have h₀ : (-1 : MvPolynomial ℕ ℤ) ^ m.toNat ∈ supported ℤ (Set.Icc 1 g) :=
    pow_mem (neg_mem (one_mem _)) _
  rw [esymmPolynomial]
  split_ifs with h₁ h₂
  · exact mul_mem h₀ (one_mem _)
  · exact mul_mem h₀ (X_mem_supported.mpr ⟨by omega, by omega⟩)
  · exact zero_mem _

variable {g} {c : Fin g → ℕ}

variable (c) in
/-- The integer polynomial in `a₁, …, a_g` which is the irreducible character of `USp(2g)` of
highest weight `e₁^{c₁} ⋯ e_g^{c_g}`: the determinant of Koike and Terada
(`SatoTateGroup.symplecticSchur`), whose entries are integer polynomials in `a₁, …, a_g`. -/
noncomputable def symplecticPolynomial : MvPolynomial ℕ ℤ :=
  (of fun i j : Fin (∑ k, c k) ↦
    esymmPolynomial g (conjugateHighestWeight c (i + 1) - i + j) -
      esymmPolynomial g (conjugateHighestWeight c (i + 1) - i - j - 2)).det

/-- **The polynomial of a character only involves `a₁, …, a_g`.** -/
lemma symplecticPolynomial_mem_supported : symplecticPolynomial c ∈ supported ℤ (Set.Icc 1 g) := by
  rw [symplecticPolynomial, det_apply']
  exact sum_mem fun σ _ ↦ mul_mem (intCast_mem _ _) <| prod_mem fun i _ ↦
    sub_mem (esymmPolynomial_mem_supported g _) (esymmPolynomial_mem_supported g _)

variable {s : Multiset ℂ} {a : ℕ → ℂ}

lemma aeval_esymmPolynomial (hc : Multiset.card s = g + g)
    (hs : ∀ k ≤ g + g, s.esymm (g + g - k) = s.esymm k)
    (ha : ∀ i ≤ g + g, s.esymm i = (-1) ^ i * a i) (m : ℤ) :
    aeval a (esymmPolynomial g m) = esymmOfInt s m := by
  have h₀ : a 0 = 1 := by
    simpa using (ha 0 (Nat.zero_le _)).symm
  rw [esymmPolynomial, esymmOfInt]
  by_cases hm : 0 ≤ m ∧ m ≤ g + g
  · have h₁ : m.toNat ≤ g + g := by
      omega
    have h₂ : (-1 : ℂ) ^ (g + g - m.toNat) = (-1) ^ m.toNat :=
      neg_one_pow_congr <| by
        simp only [Nat.even_iff]
        omega
    have h₃ : s.esymm m.toNat = (-1) ^ m.toNat * a (min m.toNat (g + g - m.toNat)) := by
      rcases le_total m.toNat (g + g - m.toNat) with h | h
      · rw [min_eq_left h, ha _ h₁]
      · rw [min_eq_right h, ← hs _ h₁, ha _ (Nat.sub_le _ _), h₂]
    rw [ite_eq_left hm, ite_eq_left hm.1, h₃, map_mul, map_pow, map_neg, map_one]
    congr 1
    split_ifs with h
    · rw [h, h₀, map_one]
    · rw [aeval_X]
  · rw [ite_eq_right hm, map_zero]
    split_ifs with h
    · rw [Multiset.esymm, Multiset.powersetCard_eq_empty _ (by omega), Multiset.map_zero,
        Multiset.sum_zero]
    · rfl

lemma aeval_symplecticPolynomial (hc : Multiset.card s = g + g)
    (hs : ∀ k ≤ g + g, s.esymm (g + g - k) = s.esymm k)
    (ha : ∀ i ≤ g + g, s.esymm i = (-1) ^ i * a i) :
    aeval a (symplecticPolynomial c) = symplecticSchur c s := by
  rw [symplecticPolynomial, symplecticSchur, AlgHom.map_det]
  congr 1
  ext i j
  simp only [AlgHom.mapMatrix_apply, map_apply, of_apply, map_sub, aeval_esymmPolynomial hc hs ha]

end Polynomial

lemma esymm_roots_charpoly_sub {w g d : ℕ} (hw : Odd w) (hd : d = g + g) (h : ambientGroup w d)
    {k : ℕ} (hk : k ≤ g + g) : (h : Matrix (Fin d) (Fin d) ℂ).charpoly.roots.esymm (g + g - k) =
      (h : Matrix (Fin d) (Fin d) ℂ).charpoly.roots.esymm k := by
  subst hd
  rcases exists_eq_conj_uspTorus hw h with ⟨x, y, h₁⟩
  rw [charpoly_eq_of_eq_conj_uspTorus hw h₁, roots_charpoly_uspTorusMatrix]
  exact esymm_torusEigenvalues_eq (fun j ↦ Circle.coe_ne_zero (x j)) hk

lemma coeff_reverse_charpoly_neg (M : Matrix n n ℂ) :
    (-M).charpoly.reverse.coeff i = (-1) ^ i * M.charpoly.reverse.coeff i := by
  have h : (-M).charpolyRev = M.charpolyRev.comp (Polynomial.C (-1) * Polynomial.X) := by
    rw [charpolyRev, charpolyRev, ← Polynomial.coe_compRingHom_apply, RingHom.map_det]
    congr 1
    refine Matrix.ext fun a b ↦ ?_
    by_cases hab : a = b <;> simp [hab]
  rw [reverse_charpoly, reverse_charpoly, h, Polynomial.comp_C_mul_X_coeff, mul_comm]

lemma continuous_coeff_charpoly : Continuous fun M : Matrix n n ℂ ↦ M.charpoly.coeff i := by
  have h₁ (M : Matrix n n ℂ) : M.charpoly.coeff i = eval (fun p : n × n ↦ M p.1 p.2)
      (MvPolynomial.map (Int.castRingHom ℂ) ((charpoly.univ ℤ n).coeff i)) := by
    rw [eval_map]
    exact (charpoly.univ_coeff_eval₂Hom n (Int.castRingHom ℂ) (fun p : n × n ↦ M p.1 p.2) i).symm
  rw [funext h₁]
  exact (MvPolynomial.continuous_eval _).comp (continuous_pi fun p ↦ continuous_id.matrix_elem _ _)

variable (G : SatoTateGroup) (c c' : Fin (G.degree / 2) → ℕ) (x : G.toSubgroup)

/-- **Each Koike–Terada function is an integer polynomial in `a₁, …, a_g`**: its value at `x` is the
value of the polynomial `SatoTateGroup.symplecticPolynomial c` at `aᵢ = aᵢ(x)`. -/
lemma symplecticCharacter_eq_aeval (hw : Odd G.weight) :
    G.symplecticCharacter c x = aeval (G.charpolyCoeff · x) (symplecticPolynomial c) := by
  have hd : G.degree = G.degree / 2 + G.degree / 2 := G.degree_eq_of_odd hw
  refine (aeval_symplecticPolynomial ?_ (fun k hk ↦ esymm_roots_charpoly_sub hw hd (G.toAmbient x)
    hk) fun i hi ↦ ?_).symm
  · exact (IsAlgClosed.splits (G.matrix x).charpoly).natDegree_eq_card_roots.symm.trans
      ((G.natDegree_charpoly x).trans hd)
  · exact G.esymmEigen_eq (hi.trans_eq hd.symm) x

lemma continuous_charpolyCoeff : Continuous (G.charpolyCoeff i) := by
  have h₁ (x : G.toSubgroup) :
      G.charpolyCoeff i x = (G.matrix x).charpoly.coeff (Polynomial.revAt G.degree i) := by
    rw [charpolyCoeff, Polynomial.coeff_reverse, G.natDegree_charpoly]
  rw [funext h₁]
  exact (continuous_coeff_charpoly _).comp (continuous_subtype_val.comp continuous_subtype_val)

lemma expectation_aeval (P : MvPolynomial ℕ ℤ) :
    G.expectation (fun x ↦ aeval (G.charpolyCoeff · x) P) =
      ∑ e ∈ P.support, (P.coeff e : ℂ) * G.mixedMoment e := by
  have h₁ (e : ℕ →₀ ℕ) : Continuous fun x : G.toSubgroup ↦
      (P.coeff e : ℂ) * e.prod fun i k ↦ G.charpolyCoeff i x ^ k :=
    continuous_const.mul <| continuous_finsetProd _ fun i _ ↦ (G.continuous_charpolyCoeff i).pow _
  simp only [mixedMoment, expectation, ← integral_const_mul]
  rw [← integral_finsetSum _ fun e _ ↦
    (h₁ e).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)]
  refine congrArg _ (funext fun x ↦ ?_)
  simp [aeval_def, eval₂_eq, Finsupp.prod]

/-- **The moments of the Koike–Terada functions are integer linear combinations of the mixed
moments** corresponding to the terms of `χ_c χ_{c'}`. -/
lemma symplecticMomentMatrix_eq_sum (hw : Odd G.weight) : G.symplecticMomentMatrix c c' =
    ∑ e ∈ (symplecticPolynomial c * symplecticPolynomial c').support,
      ((symplecticPolynomial c * symplecticPolynomial c').coeff e : ℂ) * G.mixedMoment e := by
  rw [← expectation_aeval, symplecticMomentMatrix, of_apply]
  refine congrArg _ (funext fun x ↦ ?_)
  rw [Pi.mul_apply, map_mul, G.symplecticCharacter_eq_aeval c x hw,
    G.symplecticCharacter_eq_aeval c' x hw]

variable {c c'} {hw : Odd G.weight} {hd : G.degree = G.degree / 2 + G.degree / 2}
  {χ χ' : IrrepClass ℂ (ambientGroup G.weight G.degree)} {e : ℕ →₀ ℕ}

variable {G} in
/-- **Every irreducible character of `USp(2g)` is an integer polynomial in `a₁, …, a_g`.** -/
lemma HasSymplecticMonomial.irreducibleCharacter_eq_aeval (hc : HasSymplecticMonomial hw hd χ c) :
    G.irreducibleCharacter χ x = aeval (G.charpolyCoeff · x) (symplecticPolynomial c) :=
  (hc.ambientCharacter_eq (G.toAmbient x)).trans (G.symplecticCharacter_eq_aeval c x hw)

/-- **The moments of the irreducible characters of `USp(2g)` are integer linear combinations of the
mixed moments** corresponding to the terms of `χ χ'`. -/
lemma momentMatrix_eq_sum (hc : HasSymplecticMonomial hw hd χ c)
    (hc' : HasSymplecticMonomial hw hd χ' c') : G.momentMatrix χ χ' =
      ∑ e ∈ (symplecticPolynomial c * symplecticPolynomial c').support,
        ((symplecticPolynomial c * symplecticPolynomial c').coeff e : ℂ) * G.mixedMoment e :=
  (G.momentMatrix_eq_symplecticMomentMatrix hc hc').trans (G.symplecticMomentMatrix_eq_sum c c' hw)

/-- **The mixed moments of odd weighted degree vanish if `G` contains `-1`**, the symmetry behind
the restriction of the moment simplex to even weighted degrees. -/
lemma mixedMoment_eq_zero_of_odd (h : -1 ∈ G.toSubgroup) (he : Odd (weightedDegree e)) :
    G.mixedMoment e = 0 := by
  refine integral_eq_zero_of_mul_left_eq_neg (g := (⟨-1, h⟩ : G.toSubgroup)) fun x ↦ ?_
  have h₁ (i : ℕ) : G.charpolyCoeff i (⟨-1, h⟩ * x) = (-1) ^ i * G.charpolyCoeff i x := by
    refine (congrArg (fun M : Matrix (Fin G.degree) (Fin G.degree) ℂ ↦
      M.charpoly.reverse.coeff i) ?_).trans (coeff_reverse_charpoly_neg i (G.matrix x))
    simp [matrix, Unitary.coe_neg]
  simp only [h₁, Finsupp.prod, mul_pow, ← pow_mul, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum]
  have h₂ : (-1 : ℂ) ^ ∑ i ∈ e.support, i * e i = -1 := he.neg_one_pow
  rw [h₂, neg_one_mul]

/-- **Each nonzero term is an entry of the moment simplex** when `G` contains `-1`: the terms of
`χ_c χ_{c'}` only involve `a₁, …, a_g`, and the moments of odd weighted degree vanish. -/
lemma mem_momentSimplexRow (h : -1 ∈ G.toSubgroup)
    (he : e ∈ (symplecticPolynomial c * symplecticPolynomial c').support)
    (h₀ : G.mixedMoment e ≠ 0) : e ∈ G.momentSimplexRow (weightedDegree e / 2) := by
  have h₁ :
      symplecticPolynomial c * symplecticPolynomial c' ∈ supported ℤ (Set.Icc 1 (G.degree / 2)) :=
    mul_mem symplecticPolynomial_mem_supported symplecticPolynomial_mem_supported
  refine ⟨fun i hi ↦ mem_supported.mp h₁ ?_, ?_, h₀⟩
  · exact Finset.mem_coe.mpr ((mem_vars_iff_mem_support i).mpr ⟨e, he, Finset.mem_coe.mp hi⟩)
  · have h₂ : ¬Odd (weightedDegree e) := fun h₃ ↦ h₀ (G.mixedMoment_eq_zero_of_odd h h₃)
    rw [Nat.not_odd_iff] at h₂
    omega

/-- **A Sato–Tate group of odd weight contains `-1` if it has a Hodge circle with the Hodge numbers
of a motive**, `h^{p,q} ≠ 0` only for `p + q = w`. The knowl `st_group.hodge_circle` does not ask
for `p + q = w`, and the knowl `st_group.definition` does not ask for a Hodge circle. -/
lemma neg_one_mem_of_hasHodgeEigenvalues (hw' : Odd G.weight) {h : Circle →ₜ* G.toSubgroup}
    {hodge : ℕ → ℕ → ℕ} (hh : G.HasHodgeEigenvalues h hodge)
    (hpq : ∀ p q, hodge p q ≠ 0 → p + q = G.weight) : -1 ∈ G.toSubgroup := by
  let A : Matrix (Fin G.degree) (Fin G.degree) ℂ := G.matrix (h (-1))
  have hA : A * A = 1 := by
    have h₁ : h (-1) * h (-1) = 1 := by
      rw [← map_mul, neg_mul_neg, one_mul, map_one]
    exact congrArg (fun y : G.toSubgroup ↦ G.matrix y) h₁
  have hcharpoly : A.charpoly.eval 1 ≠ 0 := by
    rw [hh.2 (-1)]
    simp only [Polynomial.eval_prod, Finset.prod_ne_zero_iff]
    intro p _ q _
    by_cases hz : hodge p q = 0
    · simp [hz]
    · have hodd : Odd ((p : ℤ) - q) := by
        have h₂ : Odd (p + q) := hpq p q hz ▸ hw'
        rw [Int.odd_sub]
        rw [Nat.odd_add] at h₂
        exact_mod_cast h₂
      have h₃ : ((-1 : Circle) : ℂ) ^ ((p : ℤ) - q) = -1 := by
        rw [Circle.coe_neg, Circle.coe_one]
        exact hodd.neg_one_zpow
      rw [h₃]
      simp
  have hunit : IsUnit (1 - A) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← map_one (Matrix.scalar (Fin G.degree)),
      ← Matrix.eval_charpoly]
    exact hcharpoly
  have h₁ : A = -1 := by
    have h₂ : (1 - A) * (1 + A) = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, hA]
      abel
    exact eq_neg_of_add_eq_zero_right (hunit.mul_right_eq_zero.mp h₂)
  have h₂ : ((h (-1) : G.toSubgroup) : unitaryGroup (Fin G.degree) ℂ) = -1 :=
    Subtype.ext (h₁.trans (by simp [Unitary.coe_neg]))
  exact h₂ ▸ (h (-1)).2

end SatoTateGroup
