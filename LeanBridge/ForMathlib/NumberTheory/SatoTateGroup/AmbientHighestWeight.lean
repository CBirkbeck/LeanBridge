import Mathlib.Analysis.Complex.Circle
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.IrreducibleMomentMatrix
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.KoikeTerada

/-!
# Highest weights of the irreducible characters of the ambient group

The LMFDB orders the irreducible characters of the ambient group of a Sato–Tate group by their
highest weights, "which can be written as a monomial in the elementary symmetric functions" (LMFDB
`st_group.moment_matrix`).

For `USp(2g)`, the odd weight case, the weights of a representation are the joint eigencharacters
of the diagonal torus `diag(t₁, …, t_g, t₁⁻¹, …, t_g⁻¹)`, the highest weight is the
lexicographically largest one, and the highest weight `λ = c₁ ω₁ + ⋯ + c_g ω_g`, with
`ω_k = e₁ + ⋯ + e_k` the fundamental weights, is the monomial `e₁^{c₁} ⋯ e_g^{c_g}`, whose leading
term on the torus is `t^λ`.

For `O(d)`, the even weight case, the highest weight of the identity component does not determine
the character: the trivial character and the determinant have the same one. The knowl does not say
what it means there and the LMFDB has no data: its table `gps_st` has no moment matrix in even
weight. We follow Weyl's labelling of the irreducible representations of `O(d)` (Weyl, *The
Classical Groups*, Chapter V; Fulton and Harris, *Representation Theory*, §19.5) by the partitions
`λ` with `λ'₁ + λ'₂ ≤ d`: classically, the character `χ_λ` occurs in `∏ᵢ e_{λ'ᵢ}`, and every
monomial in `e₁, …, e_d` in which it occurs is that of a partition lexicographically at least `λ`.
So we take the monomial of `χ` to be the monomial `e₁^{c₁} ⋯ e_d^{c_d}` containing `χ` with the
least partition (`SatoTateGroup.HasOrthogonalMonomial`). Neither the comparison with Weyl's
labelling nor the fact that distinct characters of `O(d)` have distinct monomials is proved here, so
in even weight the order `SatoTateGroup.IsBeforeInMomentMatrix` is only known to be a total
preorder.

## Main definitions

* `SatoTateGroup.uspTorus`: the diagonal torus of `USp(2g)`.
* `SatoTateGroup.IsTorusWeight`, `SatoTateGroup.IsHighestTorusWeight`: the weights of an irreducible
  character of `USp(2g)`, and the highest one.
* `SatoTateGroup.HasSymplecticMonomial` (LMFDB `st_group.moment_matrix`): the highest weight of an
  irreducible character of `USp(2g)` is the monomial with exponent vector `c`.
* `SatoTateGroup.HasOrthogonalMonomial` (LMFDB `st_group.moment_matrix`): Weyl's monomial of an
  irreducible character of `O(d)`.
* `SatoTateGroup.IsBeforeInMomentMatrix` (LMFDB `st_group.moment_matrix`): the order of the
  irreducible characters of the ambient group in the moment matrix.

## Main results

* `SatoTateGroup.IsHighestTorusWeight.eq`: the highest weight is unique.
* `SatoTateGroup.HasSymplecticMonomial.eq`: so is its exponent vector.
* `SatoTateGroup.HasOrthogonalMonomial.eq`: so is Weyl's monomial.
* `SatoTateGroup.roots_charpoly_uspTorusMatrix`: the eigenvalues of a matrix of the torus.
* `SatoTateGroup.symplecticSchur_uspTorusMatrix_mul_det`: the function
  `SatoTateGroup.symplecticSchur` on the torus is the quotient in Weyl's character formula.
-/

open Matrix MeasureTheory Polynomial TauCeti

open scoped ComplexConjugate

namespace SatoTateGroup

lemma highestWeight_injective {g : ℕ} : Function.Injective (highestWeight (g := g)) := by
  intro c c' h
  funext i
  induction i using WellFoundedGT.induction with
  | ind i ih =>
    have h₁ (e : Fin g → ℕ) : highestWeight e i = e i + ∑ k ∈ Finset.Ioi i, e k := by
      rw [highestWeight, ← Finset.Ioi_insert, Finset.sum_insert (by simp)]
    have h₂ : ∑ k ∈ Finset.Ioi i, c k = ∑ k ∈ Finset.Ioi i, c' k :=
      Finset.sum_congr rfl fun k hk ↦ ih k (Finset.mem_Ioi.mp hk)
    have h₃ : highestWeight c i = highestWeight c' i := congrFun h i
    rw [h₁, h₁, h₂] at h₃
    omega

section Torus

variable {g : ℕ}

/-- The diagonal entries `t₁, …, t_g, t₁⁻¹, …, t_g⁻¹` of a matrix of the torus of `USp(2g)`. -/
noncomputable def uspTorusEntry (t : Fin g → Circle) (i : Fin (g + g)) : Circle :=
  Fin.addCases (motive := fun _ ↦ Circle) t (fun j ↦ (t j)⁻¹) i

lemma uspTorusEntry_castAdd (t : Fin g → Circle) (j : Fin g) :
    uspTorusEntry t (Fin.castAdd g j) = t j :=
  Fin.addCases_left j

lemma uspTorusEntry_natAdd (t : Fin g → Circle) (j : Fin g) :
    uspTorusEntry t (Fin.natAdd g j) = (t j)⁻¹ :=
  Fin.addCases_right j

lemma uspTorusEntry_mul (t t' : Fin g → Circle) (i : Fin (g + g)) :
    uspTorusEntry (t * t') i = uspTorusEntry t i * uspTorusEntry t' i := by
  induction i using Fin.addCases with
  | left j =>
    rw [uspTorusEntry_castAdd, uspTorusEntry_castAdd, uspTorusEntry_castAdd, Pi.mul_apply]
  | right j =>
    rw [uspTorusEntry_natAdd, uspTorusEntry_natAdd, uspTorusEntry_natAdd, Pi.mul_apply, mul_inv]

/-- The matrix `diag(t₁, …, t_g, t₁⁻¹, …, t_g⁻¹)`. -/
noncomputable def uspTorusMatrix (t : Fin g → Circle) : Matrix (Fin (g + g)) (Fin (g + g)) ℂ :=
  diagonal fun i ↦ (uspTorusEntry t i : ℂ)

lemma uspTorusMatrix_mem_unitaryGroup (t : Fin g → Circle) :
    uspTorusMatrix t ∈ unitaryGroup (Fin (g + g)) ℂ := by
  rw [mem_unitaryGroup_iff, star_eq_conjTranspose, uspTorusMatrix, diagonal_conjTranspose,
    diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  simp [Complex.mul_conj]

lemma uspTorusMatrix_mul (t t' : Fin g → Circle) :
    uspTorusMatrix (t * t') = uspTorusMatrix t * uspTorusMatrix t' := by
  rw [uspTorusMatrix, uspTorusMatrix, uspTorusMatrix, diagonal_mul_diagonal]
  congr 1
  funext i
  rw [uspTorusEntry_mul, Circle.coe_mul]

lemma uspTorusMatrix_one : uspTorusMatrix (1 : Fin g → Circle) = 1 := by
  rw [uspTorusMatrix, ← diagonal_one]
  congr 1
  funext i
  induction i using Fin.addCases with
  | left j => rw [uspTorusEntry_castAdd]; simp
  | right j => rw [uspTorusEntry_natAdd]; simp

lemma uspTorusMatrix_mem_form (t : Fin g → Circle) :
    (uspTorusMatrix t)ᵀ * satoTateForm (g + g) * uspTorusMatrix t = satoTateForm (g + g) := by
  have h : (g + g) / 2 = g := by
    omega
  have hcancel (j : Fin g) : (t j : ℂ) * ((t j)⁻¹ : Circle) = 1 := by
    rw [← Circle.coe_mul, mul_inv_cancel, Circle.coe_one]
  have hcancel' (j : Fin g) : (((t j)⁻¹ : Circle) : ℂ) * (t j : ℂ) = 1 := by
    rw [← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
  rw [uspTorusMatrix, diagonal_transpose]
  ext i j
  rw [mul_diagonal, diagonal_mul]
  induction i using Fin.addCases with
  | left a =>
    have ha : (a : ℕ) < g := a.2
    induction j using Fin.addCases with
    | left b =>
      have hb : (b : ℕ) < g := b.2
      simp only [satoTateForm, of_apply, Fin.val_castAdd]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp
    | right b =>
      have hb : (b : ℕ) < g := b.2
      simp only [satoTateForm, of_apply, h, Fin.val_castAdd, Fin.val_natAdd, uspTorusEntry_castAdd,
        uspTorusEntry_natAdd]
      rw [ite_eq_right (c := g + (b : ℕ) + g = a) (by omega)]
      split_ifs with hab
      · have hab' : a = b := Fin.ext (by omega)
        subst hab'
        linear_combination -hcancel a
      · simp
  | right a =>
    induction j using Fin.addCases with
    | left b =>
      have hb : (b : ℕ) < g := b.2
      simp only [satoTateForm, of_apply, h, Fin.val_castAdd, Fin.val_natAdd, uspTorusEntry_castAdd,
        uspTorusEntry_natAdd]
      rw [ite_eq_right (c := g + (a : ℕ) + g = b) (by omega)]
      split_ifs with hab
      · have hab' : a = b := Fin.ext (by omega)
        subst hab'
        linear_combination hcancel' a
      · simp
    | right b =>
      simp only [satoTateForm, of_apply, Fin.val_natAdd]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      simp

lemma charpoly_uspTorusMatrix (t : Fin g → Circle) : (uspTorusMatrix t).charpoly =
    (∏ j, (X - C (t j : ℂ))) * ∏ j : Fin g, (X - C (((t j)⁻¹ : Circle) : ℂ)) := by
  rw [uspTorusMatrix, charpoly_diagonal, Fin.prod_univ_add]
  simp only [uspTorusEntry_castAdd, uspTorusEntry_natAdd]

/-- **The eigenvalues of a matrix of the torus of `USp(2g)`.** -/
lemma roots_charpoly_uspTorusMatrix (t : Fin g → Circle) :
    (uspTorusMatrix t).charpoly.roots = torusEigenvalues fun j ↦ (t j : ℂ) := by
  have hne : (∏ j, (X - C (t j : ℂ))) * ∏ j : Fin g, (X - C (((t j)⁻¹ : Circle) : ℂ)) ≠ 0 := by
    refine mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ ↦ X_sub_C_ne_zero _)
      (Finset.prod_ne_zero_iff.mpr fun j _ ↦ X_sub_C_ne_zero _)
  rw [charpoly_uspTorusMatrix, roots_mul hne, Finset.prod_eq_multiset_prod,
    Finset.prod_eq_multiset_prod, torusEigenvalues]
  have h₁ (f : Fin g → ℂ) :
      ((Finset.univ.val.map fun j ↦ X - C (f j)).prod).roots = Finset.univ.val.map f := by
    have h₂ : ((Multiset.map (fun a ↦ X - C a) (Finset.univ.val.map f)).prod).roots =
        Finset.univ.val.map f :=
      roots_multiset_prod_X_sub_C (Finset.univ.val.map f)
    rwa [Multiset.map_map] at h₂
  rw [h₁, h₁]
  simp

/-- **The symplectic Schur function on the torus is the quotient in Weyl's character formula.** -/
lemma symplecticSchur_uspTorusMatrix_mul_det (c : Fin g → ℕ) (t : Fin g → Circle) :
    symplecticSchur c (uspTorusMatrix t).charpoly.roots *
        (of fun i j : Fin g ↦ weylEntry (fun k ↦ (t k : ℂ)) j (g - i)).det =
      (of fun i j : Fin g ↦ weylEntry (fun k ↦ (t k : ℂ)) j (highestWeight c i + g - i)).det := by
  rw [roots_charpoly_uspTorusMatrix]
  exact symplecticSchur_mul_det c fun j ↦ Circle.coe_ne_zero (t j)

end Torus

section Monomial

variable {w d g : ℕ} (hw : Odd w) (hd : d = g + g)

/-- The **diagonal torus** `diag(t₁, …, t_g, t₁⁻¹, …, t_g⁻¹)` of the ambient group `USp(2g)`. -/
noncomputable def uspTorus : (Fin g → Circle) →* ambientGroup w d := by
  subst hd
  exact
    { toFun := fun t ↦ ⟨⟨uspTorusMatrix t, uspTorusMatrix_mem_unitaryGroup t⟩, by
        rw [mem_ambientGroup, ambientForm, ite_eq_left hw]
        exact uspTorusMatrix_mem_form t⟩
      map_one' := Subtype.ext <| Subtype.ext uspTorusMatrix_one
      map_mul' := fun t t' ↦ Subtype.ext <| Subtype.ext (uspTorusMatrix_mul t t') }

lemma coe_uspTorus (t : Fin g → Circle) :
    ((uspTorus hw rfl t : ambientGroup w (g + g)) : Matrix (Fin (g + g)) (Fin (g + g)) ℂ) =
      uspTorusMatrix t :=
  rfl

variable (χ : IrrepClass ℂ (ambientGroup w d))

/-- `m` is a **weight** of the irreducible character `χ` of `USp(2g)`: the model of `χ` has a
nonzero vector on which the torus acts by the character `t ↦ ∏ₖ t_k ^ m_k`. -/
def IsTorusWeight (m : Fin g → ℤ) : Prop :=
  ∃ v : EuclideanSpace ℂ (Fin χ.model.dim), v ≠ 0 ∧ ∀ t : Fin g → Circle,
    χ.model.rep (uspTorus hw hd t) v = (∏ k, (t k : ℂ) ^ m k) • v

/-- `m` is the **highest weight** of the irreducible character `χ` of `USp(2g)`: the
lexicographically largest weight. -/
def IsHighestTorusWeight (m : Fin g → ℤ) : Prop :=
  IsTorusWeight hw hd χ m ∧ ∀ m', IsTorusWeight hw hd χ m' → toLex m' ≤ toLex m

variable {hw hd χ} in
/-- **The highest weight is unique.** -/
lemma IsHighestTorusWeight.eq {m m' : Fin g → ℤ} (h : IsHighestTorusWeight hw hd χ m)
    (h' : IsHighestTorusWeight hw hd χ m') : m = m' :=
  toLex.injective (le_antisymm (h'.2 m h.1) (h.2 m' h'.1))

/-- The highest weight of the irreducible character `χ` of `USp(2g)` is the monomial
`e₁^{c₁} ⋯ e_g^{c_g}` in the elementary symmetric functions (LMFDB `st_group.moment_matrix`): it is
`λ = c₁ ω₁ + ⋯ + c_g ω_g`, for the fundamental weights `ω_k = e₁ + ⋯ + e_k`. -/
def HasSymplecticMonomial (c : Fin g → ℕ) : Prop :=
  IsHighestTorusWeight hw hd χ fun i ↦ highestWeight c i

variable {hw hd χ} in
/-- **The exponent vector of the highest weight is unique.** -/
lemma HasSymplecticMonomial.eq {c c' : Fin g → ℕ} (h : HasSymplecticMonomial hw hd χ c)
    (h' : HasSymplecticMonomial hw hd χ c') : c = c' :=
  highestWeight_injective <| funext fun i ↦ by
    exact_mod_cast congrFun (IsHighestTorusWeight.eq h h') i

/-- The function `∏ₖ e_{k + 1} ^ c_k` on the ambient group, `e_k` the elementary symmetric functions
of the eigenvalues: the character of `⨂ₖ (⋀^{k + 1} V)^{⊗ c_k}`, for `V` the standard
representation. -/
noncomputable def ambientMonomial (c : Fin d → ℕ) (a : ambientGroup w d) : ℂ :=
  ∏ k : Fin d, (a : Matrix (Fin d) (Fin d) ℂ).charpoly.roots.esymm ((k : ℕ) + 1) ^ c k

/-- The irreducible character `χ` of the ambient group occurs in the monomial with exponent
vector `c`. -/
def OccursInMonomial (c : Fin d → ℕ) : Prop :=
  ∫ a, ambientMonomial c a * conj (ambientCharacter w d χ a) ∂haarProb (ambientGroup w d) ≠ 0

/-- **Weyl's monomial** of an irreducible character `χ` of `O(d)` (Weyl, *The Classical Groups*,
Chapter V; LMFDB `st_group.moment_matrix`, which has no data in this case): `χ` occurs in the
monomial `e₁^{c₁} ⋯ e_d^{c_d}`, and every other monomial in which `χ` occurs has a lexicographically
larger partition. Classically this partition is the one labelling `χ` in Weyl's classification; this
is not proved here. -/
def HasOrthogonalMonomial (c : Fin d → ℕ) : Prop :=
  OccursInMonomial χ c ∧ ∀ c', OccursInMonomial χ c' →
    toLex (highestWeight c) ≤ toLex (highestWeight c')

variable {χ} in
/-- **Weyl's monomial is unique.** -/
lemma HasOrthogonalMonomial.eq {c c' : Fin d → ℕ} (h : HasOrthogonalMonomial χ c)
    (h' : HasOrthogonalMonomial χ c') : c = c' :=
  highestWeight_injective <| toLex.injective (le_antisymm (h.2 c' h'.1) (h'.2 c h.1))

end Monomial

/-- The **order of the irreducible characters** of the ambient group in the moment matrix of a
Sato–Tate group (LMFDB `st_group.moment_matrix`): by the monomial of their highest weights
(`HasSymplecticMonomial`, `HasOrthogonalMonomial`), in the order `IsBeforeInDisplayOrder`. In odd
weight this is a linear order. In even weight it is a total preorder, and it is a linear order
exactly when distinct characters of `O(d)` have distinct Weyl's monomials, which is classical but
not proved here. -/
def IsBeforeInMomentMatrix (G : SatoTateGroup)
    (χ χ' : IrrepClass ℂ (ambientGroup G.weight G.degree)) : Prop :=
  (∀ (hw : Odd G.weight) (hd : G.degree = G.degree / 2 + G.degree / 2)
      (c c' : Fin (G.degree / 2) → ℕ), HasSymplecticMonomial hw hd χ c →
        HasSymplecticMonomial hw hd χ' c' → IsBeforeInDisplayOrder c c') ∧
    (Even G.weight → ∀ c c' : Fin G.degree → ℕ, HasOrthogonalMonomial χ c →
      HasOrthogonalMonomial χ' c' → IsBeforeInDisplayOrder c c')

end SatoTateGroup
