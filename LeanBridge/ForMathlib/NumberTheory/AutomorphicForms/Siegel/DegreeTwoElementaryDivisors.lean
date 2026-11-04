import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.HeckeRing
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParabolicDecomposition
import TauCeti.LinearAlgebra.Matrix.SmithNormalForm

/-!
# Symplectic elementary divisors in degree 2

Let `p` be a prime and `S_p` the semigroup of integral symplectic similitudes of `Sp(4, ℤ)` whose
multiplier is a power of `p` (`SiegelUpperHalfSpace.heckeMonoidAt`). Every `x ∈ S_p` lies in the
double coset `Γ diag(p^a, p^{a+s}, p^{a+2s+t}, p^{a+s+t}) Γ` of `Γ = Sp(4, ℤ)` for unique
`a, s, t ≥ 0`, the coordinates being `(e_0, e_1, f_0, f_1)` (Andrianov, *Quadratic forms and Hecke
operators*, §3.3, in degree `2`). So the double cosets `T(a, s, t)` form a basis of the local
Hecke algebra of `Sp(4, ℤ)` at `p`: `T(p) = T(0, 0, 1)`, `T_1(p²) = T(0, 1, 0)` and
`T_0(p²) = Γ (p 1₄) Γ = T(1, 0, 0)`, in the indexing
`T_i(p²) = Γ diag(1_i, p 1_{2-i}, p² 1_i, p 1_{2-i}) Γ` of LMFDB `mf.siegel.hecke_operator`
(`SiegelUpperHalfSpace.heckeTi`); Andrianov indexes the other way and writes the scalar `T_2(p²)`.

Existence. If `p` divides every entry of `x`, then `x = p x'` with `x' ∈ S_p`, and induction on the
multiplier applies. Otherwise a column of `x` with an entry prime to `p` is a primitive vector: a
common divisor of its entries divides the multiplier `p^δ`, as `J⁻¹ xᵀ J x = p^δ`. `Sp(4, ℤ)` acts
transitively on the primitive vectors (two embedded `SL(2, ℤ)` and a rotation `(U, 0; 0, U⁻ᵀ)`),
so `γ x γ'` has first column `e_0`. A rotation and a translation `(1, S; 0, 1)` clear the first
row, the symplectic relations clear the row and column of `f_0`, and the remaining block on
`(e_1, f_1)` has determinant `p^δ`, so the Smith normal form in `SL(2, ℤ)` (Tau Ceti's
`Matrix.exists_smith_normal_form_of_det_pos`) finishes.

Uniqueness. The determinant `p^{4a+4s+2t}`, the largest power `p^a` of `p` dividing every entry
and the largest power `p^{2a+s}` dividing every `2 × 2` minor are invariants of the double coset.
The last two (`SiegelUpperHalfSpace.EntriesDvd`, `SiegelUpperHalfSpace.MinorsDvd`) are moreover
superadditive under products, the minors by the expansion of a `2 × 2` minor of a product as a sum
of products of `2 × 2` minors of the factors (the Cauchy–Binet formula for `2 × 2` minors).

## Main definitions

* `SiegelUpperHalfSpace.diagExp`: the diagonal entries `(p^a, p^{a+s}, p^{a+2s+t}, p^{a+s+t})`.
* `SiegelUpperHalfSpace.symplecticDiag`, `SiegelUpperHalfSpace.heckeCosetDiag`: the element
  `diag(p^a, p^{a+s}, p^{a+2s+t}, p^{a+s+t})` of `S_p` and its double coset `T(a, s, t)`.
* `SiegelUpperHalfSpace.EntriesDvd`, `SiegelUpperHalfSpace.MinorsDvd`: `p^k` divides every entry,
  every `2 × 2` minor, of an integral matrix.

## Main results

* `SiegelUpperHalfSpace.exists_mem_mulVec_eq_single`: `Sp(4, ℤ)` acts transitively on the
  primitive vectors of `ℤ⁴`.
* `SiegelUpperHalfSpace.exists_eq_heckeCosetDiag`: every double coset of `S_p` is some
  `T(a, s, t)`.
* `SiegelUpperHalfSpace.heckeCosetDiag_injective`: the exponents `(a, s, t)` are unique.
-/

open Matrix SymplecticGroup

open scoped MatrixGroups

namespace SiegelUpperHalfSpace

local notation "Mℤ" => Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ

local notation "Γ₂" => heckeGamma (Fin 2)

/-! ### Integral symplectic matrices of degree `2` -/

/-- The integral matrix acting by `A` on the coordinates `(e_0, f_0)` and by `B` on `(e_1, f_1)`. -/
def pairDiag (A B : Matrix (Fin 2) (Fin 2) ℤ) : Mℤ :=
  fromBlocks !![A 0 0, 0; 0, B 0 0] !![A 0 1, 0; 0, B 0 1] !![A 1 0, 0; 0, B 1 0]
    !![A 1 1, 0; 0, B 1 1]

lemma pairDiag_mul (A B A' B' : Matrix (Fin 2) (Fin 2) ℤ) :
    pairDiag A B * pairDiag A' B' = pairDiag (A * A') (B * B') := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [pairDiag, Matrix.mul_apply]

lemma coe_embedSecond (M : SL(2, ℤ)) : (embedSecond M : Mℤ) = pairDiag 1 M := by
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [pairDiag, embedSecond]

lemma transpose_mul_J_mul_apply_eq_sum {R : Type*} [CommRing R]
    {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} (a b : Fin 2 ⊕ Fin 2) :
    (Mᵀ * J (Fin 2) R * M) a b =
      ∑ c, (M (.inr c) a * M (.inl c) b - M (.inl c) a * M (.inr c) b) := by
  simp [J, mul_apply]
  ring1

variable {c : Fin 2 ⊕ Fin 2 → ℤ} {r : ℤ} {M : Mℤ}

lemma transpose_mul_J_mul_mul_mul {γ γ' : Mℤ} (hγ : γ ∈ symplecticGroup (Fin 2) ℤ)
    (hγ' : γ' ∈ symplecticGroup (Fin 2) ℤ) (hM : Mᵀ * J (Fin 2) ℤ * M = r • J (Fin 2) ℤ) :
    (γ * M * γ')ᵀ * J (Fin 2) ℤ * (γ * M * γ') = r • J (Fin 2) ℤ := by
  have e : (γ * M * γ')ᵀ * J (Fin 2) ℤ * (γ * M * γ') =
      γ'ᵀ * (Mᵀ * (γᵀ * J (Fin 2) ℤ * γ) * M) * γ' := by
    simp only [transpose_mul, Matrix.mul_assoc]
  rw [e, SymplecticGroup.mem_iff'.mp hγ, hM, Matrix.mul_smul, Matrix.smul_mul,
    SymplecticGroup.mem_iff'.mp hγ']

/-- **`Sp(4, ℤ)` acts transitively on the primitive vectors**: a vector of `ℤ⁴` whose entries have
no common non-unit divisor is `γ⁻¹ e_0` for some `γ ∈ Sp(4, ℤ)`. -/
lemma exists_mem_mulVec_eq_single (hc : ∀ d : ℤ, (∀ i, d ∣ c i) → IsUnit d) :
    ∃ γ ∈ symplecticGroup (Fin 2) ℤ, γ *ᵥ c = Pi.single (.inl 0) 1 := by
  rcases exists_SL2Z_eq_gcd (c (.inl 0)) (c (.inr 0)) with ⟨M₀, h₀, h₀'⟩
  rcases exists_SL2Z_eq_gcd (c (.inl 1)) (c (.inr 1)) with ⟨M₁, h₁, h₁'⟩
  rcases exists_SL2Z_eq_gcd ((c (.inl 0)).gcd (c (.inr 0))) ((c (.inl 1)).gcd (c (.inr 1))) with
    ⟨U, hU, hU'⟩
  have hg : ((c (.inl 0)).gcd (c (.inr 0))).gcd ((c (.inl 1)).gcd (c (.inr 1))) = 1 := by
    have hd (i : Fin 2 ⊕ Fin 2) :
        ((((c (.inl 0)).gcd (c (.inr 0))).gcd ((c (.inl 1)).gcd (c (.inr 1))) : ℕ) : ℤ) ∣ c i := by
      rcases i with i | i <;> fin_cases i
      · exact (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)).trans (Int.gcd_dvd_left _ _)
      · exact (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)).trans (Int.gcd_dvd_left _ _)
      · exact (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left _ _)).trans (Int.gcd_dvd_right _ _)
      · exact (Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right _ _)).trans (Int.gcd_dvd_right _ _)
    rcases Int.isUnit_iff.mp (hc _ hd) with h | h
    · exact_mod_cast h
    · omega
  have e₁ : (embedFirst M₀ : Mℤ) *ᵥ c =
      Sum.elim ![((c (.inl 0)).gcd (c (.inr 0)) : ℤ), c (.inl 1)] ![0, c (.inr 1)] := by
    ext (i | i) <;> fin_cases i <;> simp [embedFirst, mulVec, dotProduct, h₀, h₀']
  have e₂ : (embedSecond M₁ : Mℤ) *ᵥ
      Sum.elim ![((c (.inl 0)).gcd (c (.inr 0)) : ℤ), c (.inl 1)] ![0, c (.inr 1)] =
        Sum.elim ![((c (.inl 0)).gcd (c (.inr 0)) : ℤ), ((c (.inl 1)).gcd (c (.inr 1)) : ℤ)]
          ![0, 0] := by
    ext (i | i) <;> fin_cases i <;> simp [embedSecond, mulVec, dotProduct, h₁, h₁']
  have e₃ : (rotation U : Mℤ) *ᵥ
      Sum.elim ![((c (.inl 0)).gcd (c (.inr 0)) : ℤ), ((c (.inl 1)).gcd (c (.inr 1)) : ℤ)]
        ![0, 0] = Pi.single (.inl 0) 1 := by
    ext (i | i) <;> fin_cases i <;> simp [rotation, mulVec, dotProduct, hU, hU', hg]
  refine ⟨_, mul_mem (mul_mem (rotation U).2 (embedSecond M₁).2) (embedFirst M₀).2, ?_⟩
  rw [← mulVec_mulVec, ← mulVec_mulVec, e₁, e₂, e₃]

lemma dvd_of_dvd_col (hM : Mᵀ * J (Fin 2) ℤ * M = r • J (Fin 2) ℤ) {j : Fin 2 ⊕ Fin 2} {d : ℤ}
    (hd : ∀ i, d ∣ M i j) : d ∣ r := by
  have h' : Mᵀ * (J (Fin 2) ℤ * M) = r • J (Fin 2) ℤ := by
    rw [← Matrix.mul_assoc, hM]
  have hN : -(J (Fin 2) ℤ * Mᵀ * J (Fin 2) ℤ) * M = r • 1 := by
    rw [neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, h', Matrix.mul_smul, J_squared, smul_neg,
      neg_neg]
  have h : (-(J (Fin 2) ℤ * Mᵀ * J (Fin 2) ℤ) * M) j j = r := by
    rw [hN, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one]
  rw [← h, mul_apply]
  exact Finset.dvd_sum fun k _ ↦ (hd k).mul_left _

lemma exists_mul_row_eq (hcol : ∀ i, M i (.inl 0) = if i = .inl 0 then 1 else 0) :
    ∃ γ ∈ symplecticGroup (Fin 2) ℤ, (∀ i, (M * γ) i (.inl 0) = if i = .inl 0 then 1 else 0) ∧
      ∀ j, (M * γ) (.inl 0) j = if j = .inl 0 then 1 else 0 := by
  let U : SL(2, ℤ) := ⟨!![1, -M (.inl 0) (.inl 1); 0, 1], by simp⟩
  let S : Matrix (Fin 2) (Fin 2) ℤ :=
    !![-(M (.inl 0) (.inr 0) + M (.inl 0) (.inr 1) * M (.inl 0) (.inl 1)), -M (.inl 0) (.inr 1);
      -M (.inl 0) (.inr 1), 0]
  have hS : fromBlocks 1 S 0 1 ∈ symplecticGroup (Fin 2) ℤ := by
    refine fromBlocks_mem_iff.mpr ⟨by simp, ?_, by simp⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [S]
  refine ⟨(rotation U : Mℤ) * fromBlocks 1 S 0 1, mul_mem (rotation U).2 hS, fun i ↦ ?_, fun j ↦ ?_⟩
  · simp [U, rotation, Matrix.mul_apply, hcol]
  · rcases j with j | j <;> fin_cases j <;> simp [U, S, rotation, Matrix.mul_apply, hcol]

lemma eq_pairDiag (hr : r ≠ 0) (hM : Mᵀ * J (Fin 2) ℤ * M = r • J (Fin 2) ℤ)
    (hcol : ∀ i, M i (.inl 0) = if i = .inl 0 then 1 else 0)
    (hrow : ∀ j, M (.inl 0) j = if j = .inl 0 then 1 else 0) :
    M = pairDiag !![1, 0; 0, r] !![M (.inl 1) (.inl 1), M (.inl 1) (.inr 1);
      M (.inr 1) (.inl 1), M (.inr 1) (.inr 1)] := by
  have hJ (a b : Fin 2 ⊕ Fin 2) : ∑ c, (M (.inr c) a * M (.inl c) b - M (.inl c) a * M (.inr c) b) =
      (r • J (Fin 2) ℤ) a b := by
    rw [← transpose_mul_J_mul_apply_eq_sum, hM]
  have h₁ : ∑ c, (M (.inr c) (.inl 0) * M (.inl c) (.inl 1) -
      M (.inl c) (.inl 0) * M (.inr c) (.inl 1)) = (r • J (Fin 2) ℤ) (.inl 0) (.inl 1) :=
    hJ (.inl 0) (.inl 1)
  have h₂ : ∑ c, (M (.inr c) (.inl 0) * M (.inl c) (.inr 0) -
      M (.inl c) (.inl 0) * M (.inr c) (.inr 0)) = (r • J (Fin 2) ℤ) (.inl 0) (.inr 0) :=
    hJ (.inl 0) (.inr 0)
  have h₃ : ∑ c, (M (.inr c) (.inl 0) * M (.inl c) (.inr 1) -
      M (.inl c) (.inl 0) * M (.inr c) (.inr 1)) = (r • J (Fin 2) ℤ) (.inl 0) (.inr 1) :=
    hJ (.inl 0) (.inr 1)
  simp [hcol, J] at h₁ h₂ h₃
  have h₄ : ∑ c, (M (.inr c) (.inl 1) * M (.inl c) (.inr 0) -
      M (.inl c) (.inl 1) * M (.inr c) (.inr 0)) = (r • J (Fin 2) ℤ) (.inl 1) (.inr 0) :=
    hJ (.inl 1) (.inr 0)
  have h₅ : ∑ c, (M (.inr c) (.inr 1) * M (.inl c) (.inr 0) -
      M (.inl c) (.inr 1) * M (.inr c) (.inr 0)) = (r • J (Fin 2) ℤ) (.inr 1) (.inr 0) :=
    hJ (.inr 1) (.inr 0)
  have h₆ : ∑ c, (M (.inr c) (.inl 1) * M (.inl c) (.inr 1) -
      M (.inl c) (.inl 1) * M (.inr c) (.inr 1)) = (r • J (Fin 2) ℤ) (.inl 1) (.inr 1) :=
    hJ (.inl 1) (.inr 1)
  simp [hrow, J] at h₄ h₅ h₆
  have hx' : r * M (.inl 1) (.inr 0) = 0 := by
    linear_combination M (.inl 1) (.inl 1) * h₅ - M (.inl 1) (.inr 1) * h₄ +
      M (.inl 1) (.inr 0) * h₆
  have hy' : r * M (.inr 1) (.inr 0) = 0 := by
    linear_combination M (.inr 1) (.inl 1) * h₅ - M (.inr 1) (.inr 1) * h₄ +
      M (.inr 1) (.inr 0) * h₆
  have hx : M (.inl 1) (.inr 0) = 0 := (mul_eq_zero.mp hx').resolve_left hr
  have hy : M (.inr 1) (.inr 0) = 0 := (mul_eq_zero.mp hy').resolve_left hr
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [pairDiag, hcol, hrow, h₁, h₂, h₃, hx, hy]

lemma det_pairBlock (hM : Mᵀ * J (Fin 2) ℤ * M = r • J (Fin 2) ℤ)
    (hcol : ∀ i, M i (.inl 0) = if i = .inl 0 then 1 else 0)
    (hrow : ∀ j, M (.inl 0) j = if j = .inl 0 then 1 else 0) :
    !![M (.inl 1) (.inl 1), M (.inl 1) (.inr 1); M (.inr 1) (.inl 1), M (.inr 1) (.inr 1)].det =
      r := by
  have hJ (a b : Fin 2 ⊕ Fin 2) : ∑ c, (M (.inr c) a * M (.inl c) b - M (.inl c) a * M (.inr c) b) =
      (r • J (Fin 2) ℤ) a b := by
    rw [← transpose_mul_J_mul_apply_eq_sum, hM]
  have h₃ : ∑ c, (M (.inr c) (.inl 0) * M (.inl c) (.inr 1) -
      M (.inl c) (.inl 0) * M (.inr c) (.inr 1)) = (r • J (Fin 2) ℤ) (.inl 0) (.inr 1) :=
    hJ (.inl 0) (.inr 1)
  simp [hcol, J] at h₃
  have h₆ : ∑ c, (M (.inr c) (.inl 1) * M (.inl c) (.inr 1) -
      M (.inl c) (.inl 1) * M (.inr c) (.inr 1)) = (r • J (Fin 2) ℤ) (.inl 1) (.inr 1) :=
    hJ (.inl 1) (.inr 1)
  simp [hrow, J, h₃] at h₆
  rw [det_fin_two_of]
  linear_combination -h₆

/-! ### Integral matrices and double cosets -/

variable {p : ℕ} {x y : GL (Fin 2 ⊕ Fin 2) ℚ} {k l : ℕ}

variable (p) in
/-- The diagonal entries `(p^a, p^{a+s}, p^{a+2s+t}, p^{a+s+t})`, at `(e_0, e_1, f_0, f_1)`, of the
symplectic elementary divisors of an integral similitude of multiplier `p^{2a+2s+t}`. -/
def diagExp (a s t : ℕ) : Fin 2 ⊕ Fin 2 → ℕ :=
  Sum.elim ![p ^ a, p ^ (a + s)] ![p ^ (a + 2 * s + t), p ^ (a + s + t)]

lemma diagExp_mul_diagExp (a s t : ℕ) (j : Fin 2) :
    diagExp p a s t (.inl j) * diagExp p a s t (.inr j) = p ^ (2 * a + 2 * s + t) := by
  fin_cases j <;> simp [diagExp] <;> ring1

lemma exists_intMatrix (g : heckeMonoidAt (Fin 2) p) : ∃ M : Mℤ, ∃ k : ℕ,
    (Int.castRingHom ℚ).mapMatrix M = (g : GL (Fin 2 ⊕ Fin 2) ℚ) ∧
      Mᵀ * J (Fin 2) ℤ * M = ((p : ℤ) ^ k) • J (Fin 2) ℤ := by
  rcases g.2 with ⟨⟨-, M, hM⟩, k, hk⟩
  have hM' : (Int.castRingHom ℚ).mapMatrix M = (g : GL (Fin 2 ⊕ Fin 2) ℚ) := hM
  refine ⟨M, k, hM', Matrix.map_injective (Int.cast_injective (α := ℚ)) ?_⟩
  have h (N : Mℤ) : N.map (↑) = (Int.castRingHom ℚ).mapMatrix N :=
    rfl
  have hJ : (((p : ℤ) ^ k) • J (Fin 2) ℤ).map (↑) = ((p : ℚ) ^ k) • J (Fin 2) ℚ := by
    rw [← map_J (Fin 2) (Int.castRingHom ℚ)]
    ext i j
    simp only [map_apply, Matrix.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_pow,
      Int.cast_natCast, eq_intCast]
  have hT : (Int.castRingHom ℚ).mapMatrix Mᵀ = ((g : GL (Fin 2 ⊕ Fin 2) ℚ) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ)ᵀ := by
    rw [← hM', RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, transpose_map]
  have hJ' : (Int.castRingHom ℚ).mapMatrix (J (Fin 2) ℤ) = J (Fin 2) ℚ := by
    rw [RingHom.mapMatrix_apply, map_J]
  dsimp only
  rw [hJ, h, map_mul, map_mul, hM', hT, hJ', hk]

lemma mem_doubleCoset_of_mul_mul_eq {M N γ γ' : Mℤ} (hx : (Int.castRingHom ℚ).mapMatrix M = x)
    (hy : (Int.castRingHom ℚ).mapMatrix N = y) (hγ : γ ∈ symplecticGroup (Fin 2) ℤ)
    (hγ' : γ' ∈ symplecticGroup (Fin 2) ℤ) (h : γ * M * γ' = N) :
    x ∈ DoubleCoset.doubleCoset y (Γ₂ : Set (GL (Fin 2 ⊕ Fin 2) ℚ)) Γ₂ := by
  have e : y = spToGL (Fin 2) ⟨γ, hγ⟩ * x * spToGL (Fin 2) ⟨γ', hγ'⟩ :=
    Units.ext <| by
      rw [← hy, ← h, map_mul, map_mul, hx]
      rfl
  refine DoubleCoset.mem_doubleCoset.mpr ⟨(spToGL (Fin 2) ⟨γ, hγ⟩)⁻¹,
    inv_mem ⟨_, trivial, rfl⟩, (spToGL (Fin 2) ⟨γ', hγ'⟩)⁻¹, inv_mem ⟨_, trivial, rfl⟩, ?_⟩
  rw [e]
  group

lemma det_eq_one_of_mem (hx : x ∈ Γ₂) :
    (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ).det = 1 := by
  rcases hx with ⟨g, -, rfl⟩
  exact SymplecticGroup.det_eq_one (SymplecticGroup.map_mem g.2 (Int.castRingHom ℚ))

lemma det_eq_of_mem_doubleCoset (h : x ∈ DoubleCoset.doubleCoset y (Γ₂ : Set _) Γ₂) :
    (x : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ).det =
      (y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ).det := by
  rcases DoubleCoset.mem_doubleCoset.mp h with ⟨γ, hγ₁, γ', hγ₂, rfl⟩
  rw [Units.val_mul, Units.val_mul, det_mul, det_mul, det_eq_one_of_mem hγ₁,
    det_eq_one_of_mem hγ₂, one_mul, mul_one]

/-! ### Invariants of the double cosets -/

variable (p) in
/-- `p^k` divides every entry of the integral matrix underlying `x ∈ GL(4, ℚ)`. -/
def EntriesDvd (k : ℕ) (x : GL (Fin 2 ⊕ Fin 2) ℚ) : Prop :=
  ∃ M : Mℤ, (Int.castRingHom ℚ).mapMatrix M = x ∧ ∀ i j, (p : ℤ) ^ k ∣ M i j

variable (p) in
/-- `p^k` divides every `2 × 2` minor of the integral matrix underlying `x ∈ GL(4, ℚ)`. -/
def MinorsDvd (k : ℕ) (x : GL (Fin 2 ⊕ Fin 2) ℚ) : Prop :=
  ∃ M : Mℤ, (Int.castRingHom ℚ).mapMatrix M = x ∧
    ∀ i i' j j', (p : ℤ) ^ k ∣ M i j * M i' j' - M i j' * M i' j

lemma EntriesDvd.mul (hx : EntriesDvd p k x) (hy : EntriesDvd p l y) :
    EntriesDvd p (k + l) (x * y) := by
  rcases hx with ⟨M, hM, hMk⟩
  rcases hy with ⟨N, hN, hNl⟩
  refine ⟨M * N, by rw [map_mul, hM, hN, Units.val_mul], fun i j ↦ ?_⟩
  rw [mul_apply, pow_add]
  exact Finset.dvd_sum fun m _ ↦ mul_dvd_mul (hMk i m) (hNl m j)

private lemma minor_mul (M N : Mℤ) (i i' j j' : Fin 2 ⊕ Fin 2) :
    (M * N) i j * (M * N) i' j' - (M * N) i j' * (M * N) i' j =
      (M i (.inl 0) * M i' (.inl 1) - M i (.inl 1) * M i' (.inl 0)) *
          (N (.inl 0) j * N (.inl 1) j' - N (.inl 0) j' * N (.inl 1) j) +
        (M i (.inl 0) * M i' (.inr 0) - M i (.inr 0) * M i' (.inl 0)) *
          (N (.inl 0) j * N (.inr 0) j' - N (.inl 0) j' * N (.inr 0) j) +
        (M i (.inl 0) * M i' (.inr 1) - M i (.inr 1) * M i' (.inl 0)) *
          (N (.inl 0) j * N (.inr 1) j' - N (.inl 0) j' * N (.inr 1) j) +
        (M i (.inl 1) * M i' (.inr 0) - M i (.inr 0) * M i' (.inl 1)) *
          (N (.inl 1) j * N (.inr 0) j' - N (.inl 1) j' * N (.inr 0) j) +
        (M i (.inl 1) * M i' (.inr 1) - M i (.inr 1) * M i' (.inl 1)) *
          (N (.inl 1) j * N (.inr 1) j' - N (.inl 1) j' * N (.inr 1) j) +
        (M i (.inr 0) * M i' (.inr 1) - M i (.inr 1) * M i' (.inr 0)) *
          (N (.inr 0) j * N (.inr 1) j' - N (.inr 0) j' * N (.inr 1) j) := by
  simp only [mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two]
  ring1

lemma MinorsDvd.mul (hx : MinorsDvd p k x) (hy : MinorsDvd p l y) :
    MinorsDvd p (k + l) (x * y) := by
  rcases hx with ⟨M, hM, hMk⟩
  rcases hy with ⟨N, hN, hNl⟩
  refine ⟨M * N, by rw [map_mul, hM, hN, Units.val_mul], fun i i' j j' ↦ ?_⟩
  have h (a b : Fin 2 ⊕ Fin 2) : (p : ℤ) ^ (k + l) ∣
      (M i a * M i' b - M i b * M i' a) * (N a j * N b j' - N a j' * N b j) :=
    pow_add (p : ℤ) k l ▸ mul_dvd_mul (hMk i i' a b) (hNl a b j j')
  rw [minor_mul]
  exact dvd_add (dvd_add (dvd_add (dvd_add (dvd_add (h _ _) (h _ _)) (h _ _)) (h _ _)) (h _ _))
    (h _ _)

lemma entriesDvd_zero_of_mem (hx : x ∈ Γ₂) : EntriesDvd p 0 x := by
  rcases hx with ⟨g, -, rfl⟩
  exact ⟨g, rfl, fun i j ↦ by rw [pow_zero]; exact one_dvd _⟩

lemma minorsDvd_zero_of_mem (hx : x ∈ Γ₂) : MinorsDvd p 0 x := by
  rcases hx with ⟨g, -, rfl⟩
  exact ⟨g, rfl, fun i i' j j' ↦ by rw [pow_zero]; exact one_dvd _⟩

lemma EntriesDvd.of_mem_doubleCoset (hy : EntriesDvd p k y)
    (h : x ∈ DoubleCoset.doubleCoset y (Γ₂ : Set (GL (Fin 2 ⊕ Fin 2) ℚ)) Γ₂) :
    EntriesDvd p k x := by
  rcases DoubleCoset.mem_doubleCoset.mp h with ⟨γ, hγ, γ', hγ', rfl⟩
  simpa using ((entriesDvd_zero_of_mem hγ).mul hy).mul (entriesDvd_zero_of_mem hγ')

lemma MinorsDvd.of_mem_doubleCoset (hy : MinorsDvd p k y)
    (h : x ∈ DoubleCoset.doubleCoset y (Γ₂ : Set (GL (Fin 2 ⊕ Fin 2) ℚ)) Γ₂) :
    MinorsDvd p k x := by
  rcases DoubleCoset.mem_doubleCoset.mp h with ⟨γ, hγ, γ', hγ', rfl⟩
  simpa using ((minorsDvd_zero_of_mem hγ).mul hy).mul (minorsDvd_zero_of_mem hγ')

/-! ### The elementary divisor theorem -/

variable [Fact p.Prime]

lemma exists_mul_mul_eq_diagonal (δ : ℕ) (M : Mℤ)
    (hM : Mᵀ * J (Fin 2) ℤ * M = ((p : ℤ) ^ δ) • J (Fin 2) ℤ) :
    ∃ a s t : ℕ, 2 * a + 2 * s + t = δ ∧ ∃ γ ∈ symplecticGroup (Fin 2) ℤ,
      ∃ γ' ∈ symplecticGroup (Fin 2) ℤ, γ * M * γ' = diagonal fun i ↦ (diagExp p a s t i : ℤ) := by
  have hp : p.Prime := Fact.out
  induction δ using Nat.strong_induction_on generalizing M with
  | _ δ ih =>
    by_cases hdvd : ∀ i j, (p : ℤ) ∣ M i j
    · choose N hN using hdvd
      have hMN : M = (p : ℤ) • Matrix.of N := by
        ext i k
        rw [hN i k, Matrix.smul_apply, of_apply, smul_eq_mul]
      have hp₂ : ((p : ℤ) ^ 2) • ((Matrix.of N)ᵀ * J (Fin 2) ℤ * Matrix.of N) =
          (p : ℤ) ^ δ • J (Fin 2) ℤ := by
        rw [← hM, hMN]
        simp only [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]
      have h2 : 2 ≤ δ := by
        have hJ : J (Fin 2) ℤ (.inl 0) (.inr 0) = -1 := by
          simp [J]
        have h' : ((p : ℤ) ^ 2 • ((Matrix.of N)ᵀ * J (Fin 2) ℤ * Matrix.of N)) (.inl 0) (.inr 0) =
            ((p : ℤ) ^ δ • J (Fin 2) ℤ) (.inl 0) (.inr 0) :=
          congrFun (congrFun hp₂ (.inl 0)) (.inr 0)
        simp only [Matrix.smul_apply, hJ] at h'
        have hd : (p : ℤ) ^ 2 ∣ (p : ℤ) ^ δ :=
          Dvd.intro (-((Matrix.of N)ᵀ * J (Fin 2) ℤ * Matrix.of N) (.inl 0) (.inr 0))
            (by linear_combination -h')
        exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp (Int.natCast_dvd_natCast.mp (by
          push_cast
          exact hd))
      have hN' : (Matrix.of N)ᵀ * J (Fin 2) ℤ * Matrix.of N = (p : ℤ) ^ (δ - 2) • J (Fin 2) ℤ := by
        have hp2 : (p : ℤ) ^ 2 ≠ 0 := pow_ne_zero 2 (Nat.cast_ne_zero.mpr hp.ne_zero)
        refine smul_right_injective _ hp2 ?_
        simp only [hp₂, smul_smul, ← pow_add, Nat.add_sub_cancel' h2]
      rcases ih (δ - 2) (by omega) _ hN' with ⟨a, s, t, hδ, γ, hγ, γ', hγ', h⟩
      refine ⟨a + 1, s, t, by omega, γ, hγ, γ', hγ', ?_⟩
      rw [hMN, Matrix.mul_smul, Matrix.smul_mul, h]
      ext i k
      rcases eq_or_ne i k with rfl | hik
      · rcases i with i | i <;> fin_cases i <;> simp [diagExp] <;> ring1
      · simp [hik]
    · rcases not_forall.mp hdvd with ⟨i₀, hi₀⟩
      rcases not_forall.mp hi₀ with ⟨j, hij⟩
      have hprim : ∀ d : ℤ, (∀ i, d ∣ M.col j i) → IsUnit d := fun d hd ↦
        ((((Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd).mpr hij).pow_left
          (m := δ)).isUnit_of_dvd' (dvd_of_dvd_col hM hd) (hd i₀)
      rcases exists_mem_mulVec_eq_single hprim with ⟨γ₁, hγ₁, h₁⟩
      rcases exists_mem_mulVec_eq_single (c := Pi.single j 1) fun d hd ↦
        isUnit_of_dvd_one (by simpa using hd j) with ⟨γ₂, hγ₂, h₂⟩
      have hγ₂i : γ₂⁻¹ ∈ symplecticGroup (Fin 2) ℤ :=
        SymplecticGroup.coe_inv' (⟨γ₂, hγ₂⟩ : symplecticGroup (Fin 2) ℤ) ▸ (⟨γ₂, hγ₂⟩⁻¹ :
          symplecticGroup (Fin 2) ℤ).2
      have he : γ₂⁻¹ *ᵥ Pi.single (.inl 0) 1 = Pi.single j 1 := by
        rw [← h₂, mulVec_mulVec, nonsing_inv_mul _ (symplectic_det hγ₂), one_mulVec]
      have h : (γ₁ * M * γ₂⁻¹) *ᵥ Pi.single (.inl 0) 1 = Pi.single (.inl 0) 1 := by
        rw [← mulVec_mulVec, he, ← mulVec_mulVec, mulVec_single_one, h₁]
      have hcol (i : Fin 2 ⊕ Fin 2) :
          (γ₁ * M * γ₂⁻¹) i (.inl 0) = if i = .inl 0 then 1 else 0 := by
        have hi : ((γ₁ * M * γ₂⁻¹) *ᵥ Pi.single (.inl 0) 1) i =
            (Pi.single (.inl 0) 1 : Fin 2 ⊕ Fin 2 → ℤ) i :=
          congrFun h i
        rw [mulVec_single_one] at hi
        simpa [Pi.single_apply] using hi
      have hp₀ : (p : ℤ) ^ δ ≠ 0 := pow_ne_zero δ (Nat.cast_ne_zero.mpr hp.ne_zero)
      have hM₁ : (γ₁ * M * γ₂⁻¹)ᵀ * J (Fin 2) ℤ * (γ₁ * M * γ₂⁻¹) = (p : ℤ) ^ δ • J (Fin 2) ℤ :=
        transpose_mul_J_mul_mul_mul hγ₁ hγ₂i hM
      rcases exists_mul_row_eq hcol with ⟨γ₃, hγ₃, hcol₃, hrow₃⟩
      have hM₂ : (γ₁ * M * γ₂⁻¹ * γ₃)ᵀ * J (Fin 2) ℤ * (γ₁ * M * γ₂⁻¹ * γ₃) =
          (p : ℤ) ^ δ • J (Fin 2) ℤ := by
        simpa only [Matrix.one_mul] using transpose_mul_J_mul_mul_mul (one_mem _) hγ₃ hM₁
      have hdet : !![(γ₁ * M * γ₂⁻¹ * γ₃) (.inl 1) (.inl 1), (γ₁ * M * γ₂⁻¹ * γ₃) (.inl 1) (.inr 1);
          (γ₁ * M * γ₂⁻¹ * γ₃) (.inr 1) (.inl 1), (γ₁ * M * γ₂⁻¹ * γ₃) (.inr 1) (.inr 1)].det =
            (p : ℤ) ^ δ :=
        det_pairBlock hM₂ hcol₃ hrow₃
      rcases exists_smith_normal_form_of_det_pos _ (hdet ▸ pow_pos (Int.natCast_pos.mpr hp.pos) δ)
        with ⟨L, R, d, hd, hdd, hLR⟩
      have hprod : d 0 * d 1 = (p : ℤ) ^ δ := by
        rw [← Fin.prod_univ_two, ← det_diagonal, ← hLR, det_mul, det_mul, L.2, R.2, one_mul,
          mul_one, hdet]
      rcases (Nat.dvd_prime_pow hp).mp (Int.natAbs_dvd_natAbs.mpr (Dvd.intro _ hprod)) with
        ⟨s, hsδ, hs⟩
      have h₀ : d 0 = (p : ℤ) ^ s := by
        rw [← Int.natAbs_of_nonneg (hd 0).le, hs, Nat.cast_pow]
      have h₁' : d 1 = (p : ℤ) ^ (δ - s) := by
        refine mul_left_cancel₀ (pow_ne_zero s (Nat.cast_ne_zero.mpr hp.ne_zero)) ?_
        rw [← pow_add, Nat.add_sub_cancel' hsδ, ← hprod, h₀]
      have hst : s ≤ δ - s := by
        have h' : d 0 ∣ d 1 := hdd (Fin.zero_le 1)
        rw [h₀, h₁'] at h'
        exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp
          (by exact_mod_cast Int.natAbs_dvd_natAbs.mpr h')
      refine ⟨0, s, δ - 2 * s, by omega, pairDiag 1 L * γ₁, ?_, γ₂⁻¹ * γ₃ * pairDiag 1 R, ?_, ?_⟩
      · exact mul_mem (coe_embedSecond L ▸ (embedSecond L).2) hγ₁
      · exact mul_mem (mul_mem hγ₂i hγ₃) (coe_embedSecond R ▸ (embedSecond R).2)
      · have e : pairDiag 1 L * γ₁ * M * (γ₂⁻¹ * γ₃ * pairDiag 1 R) =
            pairDiag 1 L * (γ₁ * M * γ₂⁻¹ * γ₃) * pairDiag 1 R := by
          simp only [Matrix.mul_assoc]
        rw [e, eq_pairDiag hp₀ hM₂ hcol₃ hrow₃, pairDiag_mul, pairDiag_mul, hLR, Matrix.one_mul,
          Matrix.mul_one]
        have e₁ : 2 * s + (δ - 2 * s) = δ := by omega
        have e₂ : s + (δ - 2 * s) = δ - s := by omega
        ext (i | i) (k | k) <;> fin_cases i <;> fin_cases k <;>
          simp [pairDiag, diagExp, h₀, h₁', e₁, e₂]

variable (p) in
/-- The element `diag(p^a, p^{a+s}, p^{a+2s+t}, p^{a+s+t})` of the semigroup `S_p` of the local
Hecke algebra of `Sp(4, ℤ)` at `p`, of multiplier `p^{2a+2s+t}`. -/
def symplecticDiag (a s t : ℕ) : heckeMonoidAt (Fin 2) p :=
  heckeDiagonal (diagExp p a s t) p (2 * a + 2 * s + t) (Fact.out : p.Prime).pos
    (diagExp_mul_diagExp a s t)

variable (p) in
/-- The double coset `T(a, s, t) = Γ diag(p^a, p^{a+s}, p^{a+2s+t}, p^{a+s+t}) Γ` of
`Γ = Sp(4, ℤ)`, an element of the basis of the local Hecke algebra at `p`: `T(p)` is `T(0, 0, 1)`,
`T_1(p²)` is `T(0, 1, 0)` and the scalar `T_0(p²) = Γ (p 1₄) Γ` is `T(1, 0, 0)`. -/
def heckeCosetDiag (a s t : ℕ) : HeckeCoset (heckeMonoidAt (Fin 2) p) Γ₂ Γ₂ :=
  HeckeCoset.mk _ _ (symplecticDiag p a s t)

lemma coe_symplecticDiag (a s t : ℕ) :
    (((symplecticDiag p a s t : heckeMonoidAt (Fin 2) p) : GL (Fin 2 ⊕ Fin 2) ℚ) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ) =
        (Int.castRingHom ℚ).mapMatrix (diagonal fun i ↦ (diagExp p a s t i : ℤ)) := by
  rw [RingHom.mapMatrix_apply, diagonal_map (map_zero _)]
  rfl

/-- **The symplectic elementary divisor theorem in degree `2`**: every double coset of
`Γ = Sp(4, ℤ)` in `S_p` is `T(a, s, t) = Γ diag(p^a, p^{a+s}, p^{a+2s+t}, p^{a+s+t}) Γ` for some
`a, s, t`. -/
lemma exists_eq_heckeCosetDiag (D : HeckeCoset (heckeMonoidAt (Fin 2) p) Γ₂ Γ₂) :
    ∃ a s t : ℕ, D = heckeCosetDiag p a s t := by
  rcases exists_intMatrix D.rep with ⟨M, k, hM, hk⟩
  rcases exists_mul_mul_eq_diagonal k M hk with ⟨a, s, t, -, γ, hγ, γ', hγ', h⟩
  refine ⟨a, s, t, ?_⟩
  rw [← HeckeCoset.mk_rep D]
  exact HeckeCoset.mk_eq_mk_of_mem
    (mem_doubleCoset_of_mul_mul_eq hM (coe_symplecticDiag a s t).symm hγ hγ' h)

variable (a s t : ℕ)

lemma det_symplecticDiag : (((symplecticDiag p a s t : heckeMonoidAt (Fin 2) p) :
    GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ).det =
      (p : ℚ) ^ (4 * a + 4 * s + 2 * t) := by
  rw [coe_symplecticDiag, ← RingHom.map_det, det_diagonal]
  simp only [Fintype.prod_sum_type, Fin.prod_univ_two, diagExp, Sum.elim_inl, Sum.elim_inr,
    eq_intCast]
  push_cast
  ring1

lemma symplecticDiag_mul (a' s' t' : ℕ) :
    (symplecticDiag p a s t : GL (Fin 2 ⊕ Fin 2) ℚ) * symplecticDiag p a' s' t' =
      symplecticDiag p (a + a') (s + s') (t + t') := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_symplecticDiag, coe_symplecticDiag, coe_symplecticDiag, ← map_mul,
    diagonal_mul_diagonal]
  congr 2
  funext i
  rcases i with i | i <;> fin_cases i <;> simp [diagExp] <;> ring1

lemma rep_mem_doubleCoset_symplecticDiag : ((heckeCosetDiag p a s t).rep : GL (Fin 2 ⊕ Fin 2) ℚ) ∈
    DoubleCoset.doubleCoset (symplecticDiag p a s t : GL (Fin 2 ⊕ Fin 2) ℚ) (Γ₂ : Set _) Γ₂ :=
  HeckeCoset.toSet_mk (H₁ := Γ₂) (H₂ := Γ₂) (symplecticDiag p a s t) ▸ HeckeCoset.rep_mem _

lemma symplecticDiag_mem_doubleCoset_rep : (symplecticDiag p a s t : GL (Fin 2 ⊕ Fin 2) ℚ) ∈
    DoubleCoset.doubleCoset ((heckeCosetDiag p a s t).rep : GL (Fin 2 ⊕ Fin 2) ℚ)
      (Γ₂ : Set _) Γ₂ := by
  rw [← HeckeCoset.toSet_eq_doubleCoset_rep]
  exact HeckeCoset.mem_toSet_iff.mpr rfl

lemma entriesDvd_symplecticDiag : EntriesDvd p a (symplecticDiag p a s t) := by
  refine ⟨_, (coe_symplecticDiag a s t).symm, fun i j ↦ ?_⟩
  rw [diagonal_apply]
  split_ifs with hij
  · subst hij
    rcases i with i | i <;> fin_cases i <;> push_cast <;> exact pow_dvd_pow _ (by omega)
  · exact dvd_zero _

lemma minorsDvd_symplecticDiag : MinorsDvd p (2 * a + s) (symplecticDiag p a s t) := by
  refine ⟨_, (coe_symplecticDiag a s t).symm, fun i i' j j' ↦ ?_⟩
  have h₁ (m : Fin 2 ⊕ Fin 2) : (p : ℤ) ^ a ∣ (diagExp p a s t m : ℤ) := by
    rcases m with m | m <;> fin_cases m <;> push_cast <;> exact pow_dvd_pow _ (by omega)
  have h₂ (m : Fin 2 ⊕ Fin 2) (hm : m ≠ .inl 0) : (p : ℤ) ^ (a + s) ∣ (diagExp p a s t m : ℤ) := by
    rcases m with m | m <;> fin_cases m <;> push_cast <;>
      first | exact absurd rfl hm | exact pow_dvd_pow _ (by omega)
  have hP (m m' : Fin 2 ⊕ Fin 2) (hm : m ≠ m') :
      (p : ℤ) ^ (2 * a + s) ∣ (diagExp p a s t m : ℤ) * (diagExp p a s t m' : ℤ) := by
    rw [show 2 * a + s = a + (a + s) by ring1, pow_add]
    by_cases hm' : m' = .inl 0
    · rw [mul_comm (diagExp p a s t m : ℤ)]
      exact mul_dvd_mul (h₁ m') (h₂ m (hm' ▸ hm))
    · exact mul_dvd_mul (h₁ m) (h₂ m' hm')
  rcases eq_or_ne i i' with rfl | hii'
  · rw [show diagonal (fun m ↦ (diagExp p a s t m : ℤ)) i j *
        diagonal (fun m ↦ (diagExp p a s t m : ℤ)) i j' -
          diagonal (fun m ↦ (diagExp p a s t m : ℤ)) i j' *
            diagonal (fun m ↦ (diagExp p a s t m : ℤ)) i j = 0 by ring1]
    exact dvd_zero _
  · simp only [diagonal_apply]
    split_ifs <;> subst_vars <;> first | exact absurd rfl hii' | simp [hP _ _ hii']

variable {a s t}

lemma le_of_entriesDvd_symplecticDiag (h : EntriesDvd p k (symplecticDiag p a s t)) : k ≤ a := by
  rcases h with ⟨M, hM, hk⟩
  rw [coe_symplecticDiag] at hM
  have hM' : M = diagonal fun i ↦ (diagExp p a s t i : ℤ) :=
    Matrix.map_injective (Int.cast_injective (α := ℚ)) hM
  have h' : (p : ℤ) ^ k ∣ M (.inl 0) (.inl 0) := hk (.inl 0) (.inl 0)
  rw [hM', diagonal_apply_eq] at h'
  exact (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp
    (Int.natCast_dvd_natCast.mp (by simpa [diagExp] using h'))

lemma le_of_minorsDvd_symplecticDiag (h : MinorsDvd p k (symplecticDiag p a s t)) :
    k ≤ 2 * a + s := by
  rcases h with ⟨M, hM, hk⟩
  rw [coe_symplecticDiag] at hM
  have hM' : M = diagonal fun i ↦ (diagExp p a s t i : ℤ) :=
    Matrix.map_injective (Int.cast_injective (α := ℚ)) hM
  have h' : (p : ℤ) ^ k ∣
      M (.inl 0) (.inl 0) * M (.inl 1) (.inl 1) - M (.inl 0) (.inl 1) * M (.inl 1) (.inl 0) :=
    hk (.inl 0) (.inl 1) (.inl 0) (.inl 1)
  rw [hM'] at h'
  have e : 2 * a + s = a + (a + s) := by
    ring1
  exact (Nat.pow_dvd_pow_iff_le_right (Fact.out : p.Prime).one_lt).mp
    (Int.natCast_dvd_natCast.mp (by simpa [diagExp, e, pow_add] using h'))

variable (p) in
/-- **The symplectic elementary divisors are unique**: the double cosets `T(a, s, t)` are distinct,
the determinant `p^{4a+4s+2t}`, the largest power `p^a` of `p` dividing every entry and the largest
power `p^{2a+s}` dividing every `2 × 2` minor being invariants of the double coset. -/
lemma heckeCosetDiag_injective :
    Function.Injective fun x : ℕ × ℕ × ℕ ↦ heckeCosetDiag p x.1 x.2.1 x.2.2 := by
  rintro ⟨a, s, t⟩ ⟨a', s', t'⟩ h
  have hD : DoubleCoset.doubleCoset (symplecticDiag p a s t : GL (Fin 2 ⊕ Fin 2) ℚ)
      (Γ₂ : Set (GL (Fin 2 ⊕ Fin 2) ℚ)) Γ₂ =
        DoubleCoset.doubleCoset (symplecticDiag p a' s' t' : GL (Fin 2 ⊕ Fin 2) ℚ)
          (Γ₂ : Set (GL (Fin 2 ⊕ Fin 2) ℚ)) Γ₂ :=
    HeckeCoset.eq_iff.mp h
  have h₁ : ((symplecticDiag p a s t : heckeMonoidAt (Fin 2) p) : GL (Fin 2 ⊕ Fin 2) ℚ) ∈
      DoubleCoset.doubleCoset (symplecticDiag p a' s' t' : GL (Fin 2 ⊕ Fin 2) ℚ)
        (Γ₂ : Set (GL (Fin 2 ⊕ Fin 2) ℚ)) Γ₂ :=
    hD ▸ DoubleCoset.mem_doubleCoset_self _ _ _
  have h₂ : ((symplecticDiag p a' s' t' : heckeMonoidAt (Fin 2) p) : GL (Fin 2 ⊕ Fin 2) ℚ) ∈
      DoubleCoset.doubleCoset (symplecticDiag p a s t : GL (Fin 2 ⊕ Fin 2) ℚ)
        (Γ₂ : Set (GL (Fin 2 ⊕ Fin 2) ℚ)) Γ₂ :=
    hD ▸ DoubleCoset.mem_doubleCoset_self _ _ _
  have ha : a ≤ a' :=
    le_of_entriesDvd_symplecticDiag ((entriesDvd_symplecticDiag a s t).of_mem_doubleCoset h₂)
  have ha' : a' ≤ a :=
    le_of_entriesDvd_symplecticDiag ((entriesDvd_symplecticDiag a' s' t').of_mem_doubleCoset h₁)
  have hs : 2 * a + s ≤ 2 * a' + s' :=
    le_of_minorsDvd_symplecticDiag ((minorsDvd_symplecticDiag a s t).of_mem_doubleCoset h₂)
  have hs' : 2 * a' + s' ≤ 2 * a + s :=
    le_of_minorsDvd_symplecticDiag ((minorsDvd_symplecticDiag a' s' t').of_mem_doubleCoset h₁)
  have hdet : ((symplecticDiag p a s t : GL (Fin 2 ⊕ Fin 2) ℚ) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ).det = ((symplecticDiag p a' s' t' :
        GL (Fin 2 ⊕ Fin 2) ℚ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ).det :=
    det_eq_of_mem_doubleCoset h₁
  rw [coe_symplecticDiag, coe_symplecticDiag, ← RingHom.map_det, ← RingHom.map_det, det_diagonal,
    det_diagonal, ← Nat.cast_prod, ← Nat.cast_prod] at hdet
  have hprod (b c d : ℕ) : ∏ i, diagExp p b c d i = p ^ (4 * b + 4 * c + 2 * d) := by
    simp only [Fintype.prod_sum_type, Fin.prod_univ_two, diagExp, Sum.elim_inl, Sum.elim_inr,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    ring1
  have hδ : 4 * a + 4 * s + 2 * t = 4 * a' + 4 * s' + 2 * t' := by
    refine Nat.pow_right_injective (Fact.out : p.Prime).two_le ?_
    dsimp only
    rw [← hprod, ← hprod]
    exact Nat.cast_injective ((Int.castRingHom ℚ).injective_int hdet)
  simp only [Prod.mk.injEq]
  omega

end SiegelUpperHalfSpace
