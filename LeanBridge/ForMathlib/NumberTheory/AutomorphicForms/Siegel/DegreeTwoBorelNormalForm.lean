import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwoElementaryDivisors
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SatakeParameters

/-!
# Normal forms of the right cosets of `Sp(4, ℤ)` in the Borel subgroup

Every right coset `Γx` of `Γ = Sp(4, ℤ)` in the semigroup `S_p` of integral similitudes of `p`-power
multiplier `r` contains exactly one element in **Borel normal form**
`(r D⁻ᵀ, X D; 0, D)` with `D = (d₀, 0; c, d₁)`, `d₀, d₁ > 0`, `0 ≤ c < d₀`, and `X` symmetric
with entries in `[0, 1)` (Andrianov, *Quadratic forms and Hecke operators*, §3.3, in degree `2`,
with the Borel subgroup `SiegelUpperHalfSpace.siegelBorel`). Existence: the Iwasawa decomposition
(`SiegelUpperHalfSpace.exists_mem_heckeGamma_mul_mem_siegelBorel`) gives an element of the Borel
subgroup, which is the normal form of its own entries; the embedded `-1 ∈ SL(2, ℤ)`
make `d₀, d₁` positive, a rotation `(U, 0; 0, U⁻ᵀ)` with `U` unipotent reduces `c` modulo `d₀` and
a translation `(1, S; 0, 1)` reduces `X` modulo `1`. Uniqueness: an element of `Γ` between two
normal forms is block upper triangular with lower right block `D D'⁻¹`, an integral lower
triangular matrix of determinant `±1` and positive diagonal, hence unipotent; reduction forces it
to be `1`, and then the upper right block is `X - X'`, integral with entries in `(-1, 1)`.

## Main definitions

* `SiegelUpperHalfSpace.borelNF`: the matrix `(r D⁻ᵀ, X D; 0, D)`.
* `SiegelUpperHalfSpace.borelNFGL`: it as an element of `GL(4, ℚ)`.

## Main results

* `SiegelUpperHalfSpace.exists_mul_eq_borelNF`: every right coset of `Sp(4, ℤ)` in `S_p` contains a
  normal form.
* `SiegelUpperHalfSpace.borelNF_eq_of_mul_eq`: two normal forms in the same right coset are equal.
-/

open Matrix SymplecticGroup

open scoped MatrixGroups

namespace SiegelUpperHalfSpace

local notation "M₄" => Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ

local notation "Mℤ" => Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ

variable (r d₀ d₁ c x₀₀ x₀₁ x₁₁ : ℚ)

/-- The **Borel normal form** `(r D⁻ᵀ, X D; 0, D)` with `D = (d₀, 0; c, d₁)` and
`X = (x₀₀, x₀₁; x₀₁, x₁₁)`, a symplectic similitude of multiplier `r` in the Borel subgroup when
`d₀, d₁ ≠ 0`. -/
def borelNF : M₄ :=
  fromBlocks !![r / d₀, -(r * c) / (d₀ * d₁); 0, r / d₁]
    !![x₀₀ * d₀ + x₀₁ * c, x₀₁ * d₁; x₀₁ * d₀ + x₁₁ * c, x₁₁ * d₁] 0 !![d₀, 0; c, d₁]

variable {r d₀ d₁ c x₀₀ x₀₁ x₁₁}

lemma borelNF_transpose_mul_J_mul (hd₀ : d₀ ≠ 0) (hd₁ : d₁ ≠ 0) :
    (borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁)ᵀ * J (Fin 2) ℚ * borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁ =
      r • J (Fin 2) ℚ := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [borelNF, J, mul_apply] <;> field_simp <;> ring1

lemma det_borelNF (hd₀ : d₀ ≠ 0) (hd₁ : d₁ ≠ 0) :
    (borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁).det = r ^ 2 := by
  rw [borelNF, det_fromBlocks_zero₂₁, det_fin_two_of, det_fin_two_of]
  field_simp
  ring1

lemma int_eq_zero_of_abs_lt_one {z : ℤ} {q : ℚ} (hz : (z : ℚ) = q) (h₀ : -1 < q) (h₁ : q < 1) :
    z = 0 := by
  have h₀' : -1 < z := by exact_mod_cast hz ▸ h₀
  have h₁' : z < 1 := by exact_mod_cast hz ▸ h₁
  omega

/-- **Two Borel normal forms in the same right coset of `Sp(4, ℤ)` are equal.** -/
lemma borelNF_eq_of_mul_eq {d₀' d₁' c' x₀₀' x₀₁' x₁₁' : ℚ} (hr : r ≠ 0) {γ : Mℤ}
    (hγ : γ ∈ symplecticGroup (Fin 2) ℤ) (hd₀ : 0 < d₀) (hd₁ : 0 < d₁) (hd₀' : 0 < d₀')
    (hd₁' : 0 < d₁') (hc : c ∈ Set.Ico 0 d₀) (hc' : c' ∈ Set.Ico 0 d₀')
    (hx : ∀ x ∈ ({x₀₀, x₀₁, x₁₁} : Finset ℚ), x ∈ Set.Ico 0 1)
    (hx' : ∀ x ∈ ({x₀₀', x₀₁', x₁₁'} : Finset ℚ), x ∈ Set.Ico 0 1)
    (h : γ.map (↑) * borelNF r d₀' d₁' c' x₀₀' x₀₁' x₁₁' = borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁) :
    (d₀, d₁, c, x₀₀, x₀₁, x₁₁) = (d₀', d₁', c', x₀₀', x₀₁', x₁₁') := by
  have e (i j : Fin 2 ⊕ Fin 2) : (γ.map ((↑) : ℤ → ℚ) * borelNF r d₀' d₁' c' x₀₀' x₀₁' x₁₁') i j =
      borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁ i j :=
    congrFun (congrFun h i) j
  have e₁ : (γ.map ((↑) : ℤ → ℚ) * borelNF r d₀' d₁' c' x₀₀' x₀₁' x₁₁') (.inr 0) (.inl 0) =
      borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁ (.inr 0) (.inl 0) :=
    e (.inr 0) (.inl 0)
  have e₂ : (γ.map ((↑) : ℤ → ℚ) * borelNF r d₀' d₁' c' x₀₀' x₀₁' x₁₁') (.inr 1) (.inl 0) =
      borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁ (.inr 1) (.inl 0) :=
    e (.inr 1) (.inl 0)
  simp [borelNF, mul_apply, hr, hd₀'.ne'] at e₁ e₂
  have e₃ : (γ.map ((↑) : ℤ → ℚ) * borelNF r d₀' d₁' c' x₀₀' x₀₁' x₁₁') (.inr 0) (.inl 1) =
      borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁ (.inr 0) (.inl 1) :=
    e (.inr 0) (.inl 1)
  have e₄ : (γ.map ((↑) : ℤ → ℚ) * borelNF r d₀' d₁' c' x₀₀' x₀₁' x₁₁') (.inr 1) (.inl 1) =
      borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁ (.inr 1) (.inl 1) :=
    e (.inr 1) (.inl 1)
  simp [borelNF, mul_apply, hr, hd₁'.ne', e₁, e₂] at e₃ e₄
  have e₅ : (γ.map ((↑) : ℤ → ℚ) * borelNF r d₀' d₁' c' x₀₀' x₀₁' x₁₁') (.inr 0) (.inr 1) =
      borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁ (.inr 0) (.inr 1) :=
    e (.inr 0) (.inr 1)
  simp [borelNF, mul_apply, hd₁'.ne', e₁, e₃] at e₅
  have e₆ : (γ.map ((↑) : ℤ → ℚ) * borelNF r d₀' d₁' c' x₀₀' x₀₁' x₁₁') (.inr 0) (.inr 0) =
      borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁ (.inr 0) (.inr 0) :=
    e (.inr 0) (.inr 0)
  have e₇ : (γ.map ((↑) : ℤ → ℚ) * borelNF r d₀' d₁' c' x₀₀' x₀₁' x₁₁') (.inr 1) (.inr 1) =
      borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁ (.inr 1) (.inr 1) :=
    e (.inr 1) (.inr 1)
  have e₈ : (γ.map ((↑) : ℤ → ℚ) * borelNF r d₀' d₁' c' x₀₀' x₀₁' x₁₁') (.inr 1) (.inr 0) =
      borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁ (.inr 1) (.inr 0) :=
    e (.inr 1) (.inr 0)
  simp [borelNF, mul_apply, e₁, e₂, e₃, e₄, e₅] at e₆ e₇
  simp [borelNF, mul_apply, e₂, e₄] at e₈
  have hJ (a b : Fin 2 ⊕ Fin 2) : ∑ c, (γ (.inr c) a * γ (.inl c) b - γ (.inl c) a * γ (.inr c) b) =
      J (Fin 2) ℤ a b := by
    rw [← transpose_mul_J_mul_apply_eq_sum, SymplecticGroup.mem_iff'.mp hγ]
  have j₁ : ∑ c, (γ (.inr c) (.inl 1) * γ (.inl c) (.inr 1) -
      γ (.inl c) (.inl 1) * γ (.inr c) (.inr 1)) = J (Fin 2) ℤ (.inl 1) (.inr 1) :=
    hJ (.inl 1) (.inr 1)
  have j₂ : ∑ c, (γ (.inr c) (.inl 0) * γ (.inl c) (.inr 1) -
      γ (.inl c) (.inl 0) * γ (.inr c) (.inr 1)) = J (Fin 2) ℤ (.inl 0) (.inr 1) :=
    hJ (.inl 0) (.inr 1)
  have j₃ : ∑ c, (γ (.inr c) (.inl 0) * γ (.inl c) (.inr 0) -
      γ (.inl c) (.inl 0) * γ (.inr c) (.inr 0)) = J (Fin 2) ℤ (.inl 0) (.inr 0) :=
    hJ (.inl 0) (.inr 0)
  have j₄ : ∑ c, (γ (.inr c) (.inl 1) * γ (.inl c) (.inr 0) -
      γ (.inl c) (.inl 1) * γ (.inr c) (.inr 0)) = J (Fin 2) ℤ (.inl 1) (.inr 0) :=
    hJ (.inl 1) (.inr 0)
  simp [J, e₁, e₂, e₃, e₄, e₅] at j₁ j₂ j₃ j₄
  have hg₁ : γ (.inr 1) (.inr 1) = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' j₁ with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · rw [h] at e₇
      push_cast at e₇
      linarith
  have hg₂ : γ (.inl 1) (.inl 0) = 0 := j₂.resolve_right (by rw [hg₁]; exact one_ne_zero)
  rw [hg₂, zero_mul, neg_zero, zero_add, neg_inj] at j₃
  have hg₀ : γ (.inr 0) (.inr 0) = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' j₃ with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · rw [h] at e₆
      push_cast at e₆
      linarith
  have hg₀' : γ (.inl 0) (.inl 0) = 1 := by
    rw [hg₀, mul_one] at j₃
    exact j₃
  have hg₁' : γ (.inl 1) (.inl 1) = 1 := by
    rw [hg₁, mul_one] at j₁
    exact j₁
  rw [hg₀, Int.cast_one, one_mul] at e₆
  rw [hg₁, Int.cast_one, one_mul] at e₇
  rw [hg₁, Int.cast_one, one_mul, e₆] at e₈
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq, Set.mem_Ico]
    at hc hc' hx hx'
  have hg₃ : γ (.inr 1) (.inr 0) = 0 := by
    refine int_eq_zero_of_abs_lt_one (q := (c - c') / d₀) ?_ ?_ ?_
    · field_simp
      linarith
    · rw [lt_div_iff₀ hd₀]
      linarith
    · rw [div_lt_iff₀ hd₀]
      linarith
  rw [hg₃, Int.cast_zero, zero_mul, zero_add] at e₈
  rw [hg₃, hg₀, hg₁', mul_zero, neg_zero, mul_one, zero_add, neg_eq_zero] at j₄
  have f₁ : (γ.map ((↑) : ℤ → ℚ) * borelNF r d₀' d₁' c' x₀₀' x₀₁' x₁₁') (.inl 0) (.inr 1) =
      borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁ (.inl 0) (.inr 1) :=
    e (.inl 0) (.inr 1)
  have f₂ : (γ.map ((↑) : ℤ → ℚ) * borelNF r d₀' d₁' c' x₀₀' x₀₁' x₁₁') (.inl 1) (.inr 1) =
      borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁ (.inl 1) (.inr 1) :=
    e (.inl 1) (.inr 1)
  have f₃ : (γ.map ((↑) : ℤ → ℚ) * borelNF r d₀' d₁' c' x₀₀' x₀₁' x₁₁') (.inl 0) (.inr 0) =
      borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁ (.inl 0) (.inr 0) :=
    e (.inl 0) (.inr 0)
  simp [borelNF, mul_apply, hg₀', hg₁', hg₂, j₄, e₆, e₇, e₈] at f₁ f₂ f₃
  have k₁' : (γ (.inl 0) (.inr 1) : ℚ) * d₁ = (x₀₁ - x₀₁') * d₁ := by
    linear_combination f₁
  have k₂' : (γ (.inl 1) (.inr 1) : ℚ) * d₁ = (x₁₁ - x₁₁') * d₁ := by
    linear_combination f₂
  have k₁ : γ (.inl 0) (.inr 1) = 0 :=
    int_eq_zero_of_abs_lt_one (mul_right_cancel₀ hd₁.ne' k₁') (by linarith) (by linarith)
  have k₂ : γ (.inl 1) (.inr 1) = 0 :=
    int_eq_zero_of_abs_lt_one (mul_right_cancel₀ hd₁.ne' k₂') (by linarith) (by linarith)
  rw [k₁, Int.cast_zero, zero_mul, add_zero] at f₁ f₃
  rw [k₂, Int.cast_zero, zero_mul, add_zero] at f₂
  have h₀₁ : x₀₁ = x₀₁' := (mul_right_cancel₀ hd₁.ne' f₁).symm
  have k₃' : (γ (.inl 0) (.inr 0) : ℚ) * d₀ = (x₀₀ - x₀₀') * d₀ := by
    linear_combination f₃ + c * h₀₁
  have k₃ : γ (.inl 0) (.inr 0) = 0 :=
    int_eq_zero_of_abs_lt_one (mul_right_cancel₀ hd₀.ne' k₃') (by linarith) (by linarith)
  rw [k₃, Int.cast_zero, zero_mul] at k₃'
  have h₀₀ : x₀₀ - x₀₀' = 0 := mul_right_cancel₀ hd₀.ne' (k₃'.symm.trans (zero_mul d₀).symm)
  simp only [Prod.mk.injEq]
  exact ⟨e₆.symm, e₇.symm, e₈.symm, by linarith, h₀₁, (mul_right_cancel₀ hd₁.ne' f₂).symm⟩

lemma embedFirst_neg_one_mul_borelNF :
    ((embedFirst (-1 : SL(2, ℤ)) : Mℤ).map (↑)) * borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁ =
      borelNF r (-d₀) d₁ c x₀₀ (-x₀₁) x₁₁ := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [borelNF, embedFirst, mul_apply, div_neg, add_comm]

lemma embedSecond_neg_one_mul_borelNF :
    ((embedSecond (-1 : SL(2, ℤ)) : Mℤ).map (↑)) * borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁ =
      borelNF r d₀ (-d₁) (-c) x₀₀ (-x₀₁) x₁₁ := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [borelNF, embedSecond, mul_apply, neg_div, div_neg, add_comm]

lemma rotation_mul_borelNF (hd₀ : d₀ ≠ 0) (hd₁ : d₁ ≠ 0) (u : ℤ) :
    ((rotation (upperUnipotent u) : Mℤ).map (↑)) * borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁ =
      borelNF r d₀ d₁ (c - u * d₀) (x₀₀ + 2 * u * x₀₁ + u ^ 2 * x₁₁) (x₀₁ + u * x₁₁) x₁₁ := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [borelNF, rotation, upperUnipotent, mul_apply] <;> field_simp <;> ring1

lemma translation_mul_borelNF (s₀₀ s₀₁ s₁₁ : ℤ) :
    (fromBlocks 1 !![s₀₀, s₀₁; s₀₁, s₁₁] 0 1 : Mℤ).map (↑) * borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁ =
      borelNF r d₀ d₁ c (x₀₀ + s₀₀) (x₀₁ + s₀₁) (x₁₁ + s₁₁) := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [borelNF, mul_apply] <;> ring1

lemma translation_mem (s₀₀ s₀₁ s₁₁ : ℤ) :
    (fromBlocks 1 !![s₀₀, s₀₁; s₀₁, s₁₁] 0 1 : Mℤ) ∈ symplecticGroup (Fin 2) ℤ := by
  refine fromBlocks_mem_iff.mpr ⟨by simp, ?_, by simp⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma exists_borelNF_pos (hd₀ : d₀ ≠ 0) (hd₁ : d₁ ≠ 0) : ∃ γ ∈ symplecticGroup (Fin 2) ℤ,
    ∃ d₀' d₁' c' x₀₁' : ℚ, 0 < d₀' ∧ 0 < d₁' ∧
      γ.map (↑) * borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁ = borelNF r d₀' d₁' c' x₀₀ x₀₁' x₁₁ := by
  have h₁ : ∃ γ ∈ symplecticGroup (Fin 2) ℤ, ∃ d₀' x₀₁' : ℚ, 0 < d₀' ∧
      γ.map (↑) * borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁ = borelNF r d₀' d₁ c x₀₀ x₀₁' x₁₁ := by
    rcases hd₀.lt_or_gt with h | h
    · exact ⟨_, (embedFirst (-1 : SL(2, ℤ))).2, _, _, neg_pos.mpr h,
        embedFirst_neg_one_mul_borelNF⟩
    · exact ⟨1, one_mem _, d₀, x₀₁, h, by simp⟩
  rcases h₁ with ⟨γ, hγ, d₀', x₀₁', hd₀', h⟩
  rcases hd₁.lt_or_gt with h' | h'
  · refine ⟨(embedSecond (-1 : SL(2, ℤ)) : Mℤ) * γ, mul_mem (embedSecond _).2 hγ, d₀', -d₁, -c,
      -x₀₁', hd₀', neg_pos.mpr h', ?_⟩
    have hmap (N : Mℤ) : N.map (↑) = (Int.castRingHom ℚ).mapMatrix N :=
      rfl
    rw [hmap, map_mul, ← hmap, ← hmap, Matrix.mul_assoc, h]
    exact embedSecond_neg_one_mul_borelNF
  · exact ⟨γ, hγ, _, _, _, _, hd₀', h', h⟩

lemma eq_borelNF_of_entries {b : M₄} (hr : r ≠ 0)
    (hb : bᵀ * J (Fin 2) ℚ * b = r • J (Fin 2) ℚ) (hC : ∀ i j, b (.inr i) (.inl j) = 0)
    (hA : b (.inl 1) (.inl 0) = 0) :
    b = borelNF r (b (.inr 0) (.inr 0)) (b (.inr 1) (.inr 1)) (b (.inr 1) (.inr 0))
      (b (.inl 0) (.inr 0) / b (.inr 0) (.inr 0) -
        b (.inl 0) (.inr 1) * b (.inr 1) (.inr 0) / (b (.inr 0) (.inr 0) * b (.inr 1) (.inr 1)))
      (b (.inl 0) (.inr 1) / b (.inr 1) (.inr 1)) (b (.inl 1) (.inr 1) / b (.inr 1) (.inr 1)) := by
  have hJ (a a' : Fin 2 ⊕ Fin 2) :
      ∑ c, (b (.inr c) a * b (.inl c) a' - b (.inl c) a * b (.inr c) a') =
        (r • J (Fin 2) ℚ) a a' := by
    rw [← transpose_mul_J_mul_apply_eq_sum, hb]
  have h₀₀ : ∑ c, (b (.inr c) (.inl 0) * b (.inl c) (.inr 0) -
      b (.inl c) (.inl 0) * b (.inr c) (.inr 0)) = (r • J (Fin 2) ℚ) (.inl 0) (.inr 0) :=
    hJ (.inl 0) (.inr 0)
  have h₀₁ : ∑ c, (b (.inr c) (.inl 0) * b (.inl c) (.inr 1) -
      b (.inl c) (.inl 0) * b (.inr c) (.inr 1)) = (r • J (Fin 2) ℚ) (.inl 0) (.inr 1) :=
    hJ (.inl 0) (.inr 1)
  have h₁₀ : ∑ c, (b (.inr c) (.inl 1) * b (.inl c) (.inr 0) -
      b (.inl c) (.inl 1) * b (.inr c) (.inr 0)) = (r • J (Fin 2) ℚ) (.inl 1) (.inr 0) :=
    hJ (.inl 1) (.inr 0)
  have h₁₁ : ∑ c, (b (.inr c) (.inl 1) * b (.inl c) (.inr 1) -
      b (.inl c) (.inl 1) * b (.inr c) (.inr 1)) = (r • J (Fin 2) ℚ) (.inl 1) (.inr 1) :=
    hJ (.inl 1) (.inr 1)
  have hs : ∑ c, (b (.inr c) (.inr 0) * b (.inl c) (.inr 1) -
      b (.inl c) (.inr 0) * b (.inr c) (.inr 1)) = (r • J (Fin 2) ℚ) (.inr 0) (.inr 1) :=
    hJ (.inr 0) (.inr 1)
  simp [J, hC, hA] at h₀₀ h₀₁ h₁₀ h₁₁ hs
  have ha₀ : b (.inl 0) (.inl 0) ≠ 0 := fun h ↦ hr (by rw [← h₀₀, h, zero_mul])
  have hd₀ : b (.inr 0) (.inr 0) ≠ 0 := fun h ↦ hr (by rw [← h₀₀, h, mul_zero])
  have hd₀₁ : b (.inr 0) (.inr 1) = 0 := h₀₁.resolve_left ha₀
  rw [hd₀₁, mul_zero, neg_zero, add_zero, neg_inj] at h₁₁
  rw [hd₀₁, mul_zero, zero_add] at hs
  have hd₁ : b (.inr 1) (.inr 1) ≠ 0 := fun h ↦ hr (by rw [← h₁₁, h, mul_zero])
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [borelNF, hC, hA, hd₀₁] <;>
    field_simp <;>
    first
    | linear_combination h₀₀
    | linear_combination h₁₁
    | linear_combination -hs
    | linear_combination (-b (.inr 1) (.inr 1)) * h₁₀ - b (.inr 1) (.inr 0) * h₁₁
    | ring1

lemma exists_eq_borelNF {b : M₄} (hr : r ≠ 0) (hb : bᵀ * J (Fin 2) ℚ * b = r • J (Fin 2) ℚ)
    (hC : ∀ i j, b (.inr i) (.inl j) = 0) (hA : b (.inl 1) (.inl 0) = 0) :
    ∃ d₀ d₁ c x₀₀ x₀₁ x₁₁ : ℚ, d₀ ≠ 0 ∧ d₁ ≠ 0 ∧ b = borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁ := by
  have hJ (a a' : Fin 2 ⊕ Fin 2) :
      ∑ c, (b (.inr c) a * b (.inl c) a' - b (.inl c) a * b (.inr c) a') =
        (r • J (Fin 2) ℚ) a a' := by
    rw [← transpose_mul_J_mul_apply_eq_sum, hb]
  have h₀₀ : ∑ c, (b (.inr c) (.inl 0) * b (.inl c) (.inr 0) -
      b (.inl c) (.inl 0) * b (.inr c) (.inr 0)) = (r • J (Fin 2) ℚ) (.inl 0) (.inr 0) :=
    hJ (.inl 0) (.inr 0)
  have h₀₁ : ∑ c, (b (.inr c) (.inl 0) * b (.inl c) (.inr 1) -
      b (.inl c) (.inl 0) * b (.inr c) (.inr 1)) = (r • J (Fin 2) ℚ) (.inl 0) (.inr 1) :=
    hJ (.inl 0) (.inr 1)
  have h₁₁ : ∑ c, (b (.inr c) (.inl 1) * b (.inl c) (.inr 1) -
      b (.inl c) (.inl 1) * b (.inr c) (.inr 1)) = (r • J (Fin 2) ℚ) (.inl 1) (.inr 1) :=
    hJ (.inl 1) (.inr 1)
  simp [J, hC, hA] at h₀₀ h₀₁ h₁₁
  have ha₀ : b (.inl 0) (.inl 0) ≠ 0 := fun h ↦ hr (by rw [← h₀₀, h, zero_mul])
  rw [h₀₁.resolve_left ha₀, mul_zero, neg_zero, add_zero, neg_inj] at h₁₁
  exact ⟨_, _, _, _, _, _, fun h ↦ hr (by rw [← h₀₀, h, mul_zero]),
    fun h ↦ hr (by rw [← h₁₁, h, mul_zero]), eq_borelNF_of_entries hr hb hC hA⟩

lemma exists_borelNF_normalized (hd₀ : 0 < d₀) (hd₁ : 0 < d₁) : ∃ γ ∈ symplecticGroup (Fin 2) ℤ,
    ∃ c' x₀₀' x₀₁' x₁₁' : ℚ, 0 ≤ c' ∧ c' < d₀ ∧ 0 ≤ x₀₀' ∧ x₀₀' < 1 ∧ 0 ≤ x₀₁' ∧ x₀₁' < 1 ∧
      0 ≤ x₁₁' ∧ x₁₁' < 1 ∧
        γ.map (↑) * borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁ = borelNF r d₀ d₁ c' x₀₀' x₀₁' x₁₁' := by
  let u : ℤ := ⌊c / d₀⌋
  let y₀₀ : ℚ := x₀₀ + 2 * u * x₀₁ + u ^ 2 * x₁₁
  let y₀₁ : ℚ := x₀₁ + u * x₁₁
  refine ⟨fromBlocks 1 !![-⌊y₀₀⌋, -⌊y₀₁⌋; -⌊y₀₁⌋, -⌊x₁₁⌋] 0 1 * (rotation (upperUnipotent u) : Mℤ),
    mul_mem (translation_mem _ _ _) (rotation _).2, c - u * d₀, y₀₀ + -⌊y₀₀⌋, y₀₁ + -⌊y₀₁⌋,
      x₁₁ + -⌊x₁₁⌋, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h : (⌊c / d₀⌋ : ℚ) ≤ c / d₀ := Int.floor_le (c / d₀)
    rw [le_div_iff₀ hd₀] at h
    linarith
  · have h : c / d₀ < ⌊c / d₀⌋ + 1 := Int.lt_floor_add_one (c / d₀)
    rw [div_lt_iff₀ hd₀] at h
    linarith
  · linarith [Int.floor_le y₀₀]
  · linarith [Int.lt_floor_add_one y₀₀]
  · linarith [Int.floor_le y₀₁]
  · linarith [Int.lt_floor_add_one y₀₁]
  · linarith [Int.floor_le x₁₁]
  · linarith [Int.lt_floor_add_one x₁₁]
  · have hmap (N : Mℤ) : N.map (↑) = (Int.castRingHom ℚ).mapMatrix N :=
      rfl
    rw [hmap, map_mul, ← hmap, ← hmap, Matrix.mul_assoc, rotation_mul_borelNF hd₀.ne' hd₁.ne']
    exact translation_mul_borelNF _ _ _

/-- **Every right coset of `Sp(4, ℤ)` in `S_p` contains a Borel normal form**: for `x ∈ S_p` of
multiplier `p^k` there are `γ ∈ Sp(4, ℤ)` and normalized parameters with
`γ x = (p^k D⁻ᵀ, X D; 0, D)`. -/
lemma exists_mul_eq_borelNF {p : ℕ} (hp : p ≠ 0) (x : heckeMonoidAt (Fin 2) p) : ∃ k : ℕ,
    ∃ γ ∈ heckeGamma (Fin 2), ∃ d₀ d₁ c x₀₀ x₀₁ x₁₁ : ℚ, 0 < d₀ ∧ 0 < d₁ ∧ 0 ≤ c ∧ c < d₀ ∧
      0 ≤ x₀₀ ∧ x₀₀ < 1 ∧ 0 ≤ x₀₁ ∧ x₀₁ < 1 ∧ 0 ≤ x₁₁ ∧ x₁₁ < 1 ∧
        ((γ * (x : GL (Fin 2 ⊕ Fin 2) ℚ) : GL (Fin 2 ⊕ Fin 2) ℚ) : M₄) =
          borelNF ((p : ℚ) ^ k) d₀ d₁ c x₀₀ x₀₁ x₁₁ := by
  rcases x.2 with ⟨-, k, hk⟩
  rcases exists_mem_heckeGamma_mul_mem_siegelBorel
    (heckeMonoid_le_gspPlusGL (heckeMonoidAt_le_heckeMonoid p x.2)) with ⟨γ₀, hγ₀, hB⟩
  have hγs : ((γ₀ : GL (Fin 2 ⊕ Fin 2) ℚ) : M₄) ∈ symplecticGroup (Fin 2) ℚ := by
    rcases hγ₀ with ⟨g, -, rfl⟩
    exact SymplecticGroup.map_mem g.2 (Int.castRingHom ℚ)
  have hb : ((γ₀ * (x : GL (Fin 2 ⊕ Fin 2) ℚ) : GL (Fin 2 ⊕ Fin 2) ℚ) : M₄)ᵀ * J (Fin 2) ℚ *
      ((γ₀ * (x : GL (Fin 2 ⊕ Fin 2) ℚ) : GL (Fin 2 ⊕ Fin 2) ℚ) : M₄) =
        ((p : ℚ) ^ k) • J (Fin 2) ℚ := by
    have e : ((γ₀ * (x : GL (Fin 2 ⊕ Fin 2) ℚ) : GL (Fin 2 ⊕ Fin 2) ℚ) : M₄)ᵀ * J (Fin 2) ℚ *
        ((γ₀ * (x : GL (Fin 2 ⊕ Fin 2) ℚ) : GL (Fin 2 ⊕ Fin 2) ℚ) : M₄) =
          ((x : GL (Fin 2 ⊕ Fin 2) ℚ) : M₄)ᵀ * ((γ₀ : M₄)ᵀ * J (Fin 2) ℚ * γ₀) *
            ((x : GL (Fin 2 ⊕ Fin 2) ℚ) : M₄) := by
      simp only [Units.val_mul, transpose_mul, Matrix.mul_assoc]
    rw [e, SymplecticGroup.mem_iff'.mp hγs]
    exact hk
  have hC (i j : Fin 2) :
      ((γ₀ * (x : GL (Fin 2 ⊕ Fin 2) ℚ) : GL (Fin 2 ⊕ Fin 2) ℚ) : M₄) (.inr i) (.inl j) = 0 :=
    congrFun (congrFun hB.2.1 i) j
  have hA : ((γ₀ * (x : GL (Fin 2 ⊕ Fin 2) ℚ) : GL (Fin 2 ⊕ Fin 2) ℚ) : M₄) (.inl 1) (.inl 0) = 0 :=
    hB.2.2 (by decide : (0 : Fin 2) < 1)
  rcases exists_eq_borelNF (pow_ne_zero k (Nat.cast_ne_zero.mpr hp)) hb hC hA with
    ⟨d₀, d₁, c, x₀₀, x₀₁, x₁₁, hd₀, hd₁, h⟩
  rcases exists_borelNF_pos hd₀ hd₁ with ⟨γ₁, hγ₁, d₀', d₁', c', x₀₁', hd₀', hd₁', h₁⟩
  rcases exists_borelNF_normalized (r := (p : ℚ) ^ k) (c := c') (x₀₀ := x₀₀) (x₀₁ := x₀₁')
    (x₁₁ := x₁₁) hd₀' hd₁' with ⟨γ₂, hγ₂, c'', y₀₀, y₀₁, y₁₁, h₂⟩
  refine ⟨k, spToGL (Fin 2) ⟨γ₂ * γ₁, mul_mem hγ₂ hγ₁⟩ * γ₀,
    mul_mem ⟨_, trivial, rfl⟩ hγ₀, d₀', d₁', c'', y₀₀, y₀₁, y₁₁, hd₀', hd₁', ?_⟩
  rcases h₂ with ⟨hc₀, hc₁, hy₀₀, hy₀₀', hy₀₁, hy₀₁', hy₁₁, hy₁₁', h₂⟩
  refine ⟨hc₀, hc₁, hy₀₀, hy₀₀', hy₀₁, hy₀₁', hy₁₁, hy₁₁', ?_⟩
  have hmap (N : Mℤ) : N.map (↑) = (Int.castRingHom ℚ).mapMatrix N :=
    rfl
  rw [mul_assoc, Units.val_mul, h, ← h₂, ← h₁, ← Matrix.mul_assoc, hmap γ₂, hmap γ₁, ← map_mul]
  rfl

lemma mem_heckeMonoidAt_of_mem_doubleCoset {p : ℕ}
    {D : HeckeCoset (heckeMonoidAt (Fin 2) p) (heckeGamma (Fin 2)) (heckeGamma (Fin 2))}
    {x : GL (Fin 2 ⊕ Fin 2) ℚ} (hx : x ∈ DoubleCoset.doubleCoset (D.rep : GL (Fin 2 ⊕ Fin 2) ℚ)
      (heckeGamma (Fin 2) : Set (GL (Fin 2 ⊕ Fin 2) ℚ)) (heckeGamma (Fin 2))) :
    x ∈ heckeMonoidAt (Fin 2) p := by
  rcases DoubleCoset.mem_doubleCoset.mp hx with ⟨γ, hγ, γ', hγ', rfl⟩
  exact mul_mem (mul_mem (heckeGamma_le_heckeMonoidAt p hγ) D.rep.2)
    (heckeGamma_le_heckeMonoidAt p hγ')

variable (r d₀ d₁ c x₀₀ x₀₁ x₁₁) in
open scoped Classical in
/-- The Borel normal form as an element of `GL(4, ℚ)` when `r, d₀, d₁ ≠ 0`, and `1` otherwise. -/
noncomputable def borelNFGL : GL (Fin 2 ⊕ Fin 2) ℚ :=
  if h : r ≠ 0 ∧ d₀ ≠ 0 ∧ d₁ ≠ 0 then
    GeneralLinearGroup.mkOfDetNeZero (borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁)
      (by rw [det_borelNF h.2.1 h.2.2]; exact pow_ne_zero 2 h.1)
  else 1

lemma coe_borelNFGL (hr : r ≠ 0) (hd₀ : d₀ ≠ 0) (hd₁ : d₁ ≠ 0) :
    ((borelNFGL r d₀ d₁ c x₀₀ x₀₁ x₁₁ : GL (Fin 2 ⊕ Fin 2) ℚ) : M₄) =
      borelNF r d₀ d₁ c x₀₀ x₀₁ x₁₁ := by
  rw [borelNFGL, dite_eq_left ⟨hr, hd₀, hd₁⟩]
  rfl

lemma borelNFGL_mem_siegelBorel (hr : 0 < r) (hd₀ : d₀ ≠ 0) (hd₁ : d₁ ≠ 0) :
    borelNFGL r d₀ d₁ c x₀₀ x₀₁ x₁₁ ∈ siegelBorel 2 := by
  refine ⟨⟨r, hr, ?_⟩, ?_, ?_⟩
  · rw [Units.coeHom_apply, coe_borelNFGL hr.ne' hd₀ hd₁]
    exact borelNF_transpose_mul_J_mul hd₀ hd₁
  · rw [coe_borelNFGL hr.ne' hd₀ hd₁, borelNF, toBlocks_fromBlocks₂₁]
  · rw [coe_borelNFGL hr.ne' hd₀ hd₁, borelNF, toBlocks_fromBlocks₁₁]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

end SiegelUpperHalfSpace
