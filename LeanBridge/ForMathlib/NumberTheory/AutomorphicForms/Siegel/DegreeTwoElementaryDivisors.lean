import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SatakeElementaryDivisors

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

Existence is the case `g = 2` of the symplectic elementary divisor theorem
(`SiegelUpperHalfSpace.exists_eq_elementaryCoset`): the double coset
`Γ diag(p^{a_0}, p^{a_1}, p^{δ-a_0}, p^{δ-a_1}) Γ` with `a_0 ≤ a_1` and `2 a_1 ≤ δ` is
`T(a_0, a_1 - a_0, δ - 2 a_1)`. So is the transitivity of `Sp(4, ℤ)` on the primitive vectors of
`ℤ⁴`, the case `k = 0` of `SiegelUpperHalfSpace.exists_mem_lowFix_mulVec_eq_single`, where
`Γ_0 = Sp(4, ℤ)`.

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

open Matrix

namespace SiegelUpperHalfSpace

local notation "Mℤ" => Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ

local notation "Γ₂" => heckeGamma (Fin 2)

/-! ### Integral symplectic matrices of degree `2` -/

lemma transpose_mul_J_mul_apply_eq_sum {R : Type*} [CommRing R]
    {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) R} (a b : Fin 2 ⊕ Fin 2) :
    (Mᵀ * J (Fin 2) R * M) a b =
      ∑ c, (M (.inr c) a * M (.inl c) b - M (.inl c) a * M (.inr c) b) := by
  simp [J, mul_apply]
  ring1

variable {c : Fin 2 ⊕ Fin 2 → ℤ} {r : ℤ} {M : Mℤ}

lemma transpose_mul_J_mul_mul_mul {γ γ' : Mℤ} (hγ : γ ∈ symplecticGroup (Fin 2) ℤ)
    (hγ' : γ' ∈ symplecticGroup (Fin 2) ℤ) (hM : Mᵀ * J (Fin 2) ℤ * M = r • J (Fin 2) ℤ) :
    (γ * M * γ')ᵀ * J (Fin 2) ℤ * (γ * M * γ') = r • J (Fin 2) ℤ :=
  transpose_mul_J_mul_eq_of_mem hγ hγ' hM

/-- **`Sp(4, ℤ)` acts transitively on the primitive vectors**: a vector of `ℤ⁴` whose entries have
no common non-unit divisor is `γ⁻¹ e_0` for some `γ ∈ Sp(4, ℤ)`. -/
lemma exists_mem_mulVec_eq_single (hc : ∀ d : ℤ, (∀ i, d ∣ c i) → IsUnit d) :
    ∃ γ ∈ symplecticGroup (Fin 2) ℤ, γ *ᵥ c = Pi.single (.inl 0) 1 := by
  rcases exists_mem_lowFix_mulVec_eq_single zero_lt_two (fun _ h ↦ absurd h (Nat.not_lt_zero _))
    hc with ⟨γ, -, h⟩
  exact ⟨γ, γ.2, h⟩

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
      Mᵀ * J (Fin 2) ℤ * M = ((p : ℤ) ^ k) • J (Fin 2) ℤ :=
  exists_intMatrix_of_mem g

lemma mem_doubleCoset_of_mul_mul_eq {M N γ γ' : Mℤ} (hx : (Int.castRingHom ℚ).mapMatrix M = x)
    (hy : (Int.castRingHom ℚ).mapMatrix N = y) (hγ : γ ∈ symplecticGroup (Fin 2) ℤ)
    (hγ' : γ' ∈ symplecticGroup (Fin 2) ℤ) (h : γ * M * γ' = N) :
    x ∈ DoubleCoset.doubleCoset y (Γ₂ : Set (GL (Fin 2 ⊕ Fin 2) ℚ)) Γ₂ :=
  mem_doubleCoset_of_intMatrix hx hy hγ hγ' h

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
  rcases exists_mul_mul_eq_diagonal_of_mul_J hM with ⟨b, hb, h2b, γ, hγ, γ', hγ', h⟩
  have h₀ : b 0 ≤ b 1 := hb (Fin.zero_le 1)
  have h₁ : 2 * b 1 ≤ δ := h2b 1
  have e : elementaryEntries p δ b = diagExp p (b 0) (b 1 - b 0) (δ - 2 * b 1) := by
    funext i
    rcases i with i | i <;> fin_cases i <;> simp [elementaryEntries] <;> congr 1 <;> omega
  refine ⟨b 0, b 1 - b 0, δ - 2 * b 1, by omega, γ, hγ, γ', hγ', ?_⟩
  rw [h, e]

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
