import LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolCanonical

/-!
# The signs of the trains of the canonical `2`-adic symbol

In the `2`-adic part of the Conway genus symbol (LMFDB `lattice.conway_genus_symbol`; Conway and
Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.5), a *stop* is a pair of consecutive
scales `2 ^ k`, `2 ^ (k + 1)` at which both Jordan constituents have type `II` (zero constituents
included), and the trains are the maximal runs of constituents between two stops. The signs
`ε_q = χ₈(det f_q)` of the constituents depend on the Jordan decomposition (sign walking), but the
product of the signs of the constituents below a stop does not: it is an isometry invariant of the
dyadic localization, and so a genus invariant
(`TauCeti.IntegralLattice.SameGenus.prod_dyadicJordanSign_le_eq`). The sign of each train is the
quotient of the products below the two stops that bound it, so the signs of the trains of the
canonical `2`-adic symbol are genus invariants (`TauCeti.IntegralLattice.SameGenus.trainSigns_eq`).

To compare two Jordan splittings of isometric forms, write their Gram matrices in adapted bases as
`G = ⊕_j 2 ^ j C_j` and `G' = ⊕_j 2 ^ j C'_j = Pᵀ G P`. With the projection `S` onto the
constituents of scale at most `2 ^ k` and `S' = 1 - S`, one has
`S G' S + S' = Ãᵀ (S G S + S') Ã + S Pᵀ (S' G S') P S` for `Ã = S P S + S'`, and the last term is
`2 ^ (k + 1)` times a matrix `K + Kᵀ` since `C_(k + 1)` is even. Factoring the scales out of
`S G' S + S'`, the determinants of the truncations `⊕_(j ≤ k) C_j` and `⊕_(j ≤ k) C'_j` differ by
`(det Ã) ^ 2` and by `det (1 + 2 (U + Uᵀ) (V + Vᵀ))` for matrices `U`, `V` (this uses that `C'_k`
is even), and the latter is `1` modulo `8`
(`Matrix.eight_dvd_det_one_add_two_smul_mul_sub_one`), so that both truncations have the same
`χ₈` of the determinant.

## Main definitions

* `TauCeti.IntegralLattice.DyadicBlock.TypeTwoAt`: a scale without constituent of type `I`; a stop
  is a pair of consecutive such scales.

## Main results

* `Matrix.eight_dvd_det_one_add_two_smul_mul_sub_one`: over `ℤ_2`,
  `det (1 + 2 (U + Uᵀ) (V + Vᵀ)) ≡ 1 mod 8`.
* `Matrix.χ₈_prod_det_eq_of_blockDiagonal'_eq`: two block diagonal Gram matrices of the shape of
  Jordan splittings, related by a change of basis, have the same `χ₈` of the determinant of their
  truncations below a stop.
* `LinearMap.BilinForm.IsJordanSplitting.prod_dyadicSign_le_eq`: the product of the dyadic signs
  below a stop is an isometry invariant.
* `TauCeti.IntegralLattice.SameGenus.prod_dyadicJordanSign_le_eq`: it is a genus invariant.
* `TauCeti.IntegralLattice.DyadicBlock.trainSigns_eq_of_prod_filter_eq`: the signs of the trains are
  determined by the sign products below the stops.
* `TauCeti.IntegralLattice.SameGenus.trainSigns_eq`: the signs of the trains of the canonical
  `2`-adic symbol are genus invariants.
-/

open Matrix Module

open LinearMap (BilinForm)

namespace PadicInt

variable {x y : ℤ_[2]}

lemma isUnit_of_two_dvd_sub_one (h : (2 : ℤ_[2]) ∣ x - 1) : IsUnit x := by
  by_contra hx
  have h2 : (2 : ℤ_[2]) ∣ x := by
    have hmem : x ∈ IsLocalRing.maximalIdeal ℤ_[2] := (IsLocalRing.mem_maximalIdeal x).mpr hx
    rw [maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hmem
    exact_mod_cast hmem
  have h1 : (2 : ℤ_[2]) ∣ 1 := by
    simpa using dvd_sub h2 h
  exact irreducible_p.not_isUnit (by exact_mod_cast isUnit_of_dvd_one h1)

lemma eight_dvd_mul_self_sub_one (h : (2 : ℤ_[2]) ∣ x - 1) : (8 : ℤ_[2]) ∣ x * x - 1 := by
  rcases h with ⟨a, ha⟩
  rcases two_dvd_mul_self_sub a with ⟨b, hb⟩
  exact ⟨a + b, by linear_combination (x + 1 + 2 * a) * ha + 4 * hb⟩

lemma eight_dvd_mul_sub_one (hx : (8 : ℤ_[2]) ∣ x - 1) (hy : (8 : ℤ_[2]) ∣ y - 1) :
    (8 : ℤ_[2]) ∣ x * y - 1 := by
  have h : x * y - 1 = (x - 1) * y + (y - 1) := by
    ring1
  rw [h]
  exact dvd_add (dvd_mul_of_dvd_left hx y) hy

end PadicInt

namespace Matrix

variable {ι : Type*} [Fintype ι] (U V M : Matrix ι ι ℤ_[2]) {S S' G P : Matrix ι ι ℤ_[2]}

lemma trace_mul_add_transpose_eq :
    ((U * (V + Vᵀ) * Uᵀ) * (V + Vᵀ)).trace = 2 * ((U * V * Uᵀ) * (V + Vᵀ)).trace := by
  have hK : U * (V + Vᵀ) * Uᵀ = U * V * Uᵀ + (U * V * Uᵀ)ᵀ := by
    rw [transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_add, Matrix.add_mul,
      Matrix.mul_assoc U Vᵀ]
  have hT : (V + Vᵀ)ᵀ = V + Vᵀ := by
    rw [transpose_add, transpose_transpose, add_comm]
  rw [hK, Matrix.add_mul, trace_add, two_mul, ← trace_transpose ((U * V * Uᵀ)ᵀ * (V + Vᵀ)),
    transpose_mul, transpose_transpose, hT, trace_mul_comm (V + Vᵀ)]

lemma proj_conj_add_eq (h1 : S * S = S) (h2 : S * S' = 0) (h3 : S' * S = 0) (h4 : S' * S' = S')
    (h5 : Sᵀ = S) (h6 : S'ᵀ = S') (hG : G = S * G * S + S' * G * S') : S * (Pᵀ * G * P) * S + S' =
      (S * P * S + S')ᵀ * (S * G * S + S') * (S * P * S + S') + S * Pᵀ * (S' * G * S') * P * S := by
  have k1 (X : Matrix ι ι ℤ_[2]) : S * (S * X) = S * X := by
    rw [← Matrix.mul_assoc, h1]
  have k3 (X : Matrix ι ι ℤ_[2]) : S' * (S * X) = 0 := by
    rw [← Matrix.mul_assoc, h3, Matrix.zero_mul]
  conv_lhs => rw [hG]
  simp only [transpose_add, transpose_mul, h5, h6, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
    k1, k3, h2, h4, Matrix.mul_zero, add_zero, zero_add]
  abel

variable [DecidableEq ι]

lemma two_dvd_det_one_add_two_smul_sub_one : (2 : ℤ_[2]) ∣ det (1 + (2 : ℤ_[2]) • M) - 1 := by
  rw [det_one_add_smul]
  exact ⟨M.trace + (det (1 + (Polynomial.X : Polynomial ℤ_[2]) • M.map Polynomial.C)).divX.divX.eval
    2 * 2, by ring1⟩

lemma eight_dvd_det_one_sub_four_smul_sub_one (hM : (2 : ℤ_[2]) ∣ M.trace) :
    (8 : ℤ_[2]) ∣ det (1 + (-4 : ℤ_[2]) • M) - 1 := by
  rcases hM with ⟨z, hz⟩
  rw [det_one_add_smul, hz]
  exact ⟨2 * (det (1 + (Polynomial.X : Polynomial ℤ_[2]) • M.map Polynomial.C)).divX.divX.eval
    (-4) - z, by ring1⟩

lemma sub_smul_eq_mul_one_add_smul (c : ℤ_[2]) (hM : IsUnit M.det) :
    M - c • U = M * (1 + (-c) • (M⁻¹ * U)) := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ hM, Matrix.one_mul, neg_smul, sub_eq_add_neg]

/-- **`det (1 + 2 (U + Uᵀ) (V + Vᵀ)) ≡ 1 mod 8` over `ℤ_2`.** With `A = 1 + 2 U T` and
`A' = 1 + 2 Uᵀ T`, `T = V + Vᵀ`, one has `1 + 2 (U + Uᵀ) T = A A' - 4 U T Uᵀ T`, the determinants
of `A` and `A'` are equal and odd, so `det (A A') ≡ 1 mod 8`, and the trace of `U T Uᵀ T` is
even. -/
lemma eight_dvd_det_one_add_two_smul_mul_sub_one :
    (8 : ℤ_[2]) ∣ det (1 + (2 : ℤ_[2]) • ((U + Uᵀ) * (V + Vᵀ))) - 1 := by
  have hS : (1 + (2 : ℤ_[2]) • (U * (V + Vᵀ))) * (1 + (2 : ℤ_[2]) • (Uᵀ * (V + Vᵀ))) =
      1 + (2 : ℤ_[2]) • ((U + Uᵀ) * (V + Vᵀ) + (2 : ℤ_[2]) • (U * (V + Vᵀ) * Uᵀ * (V + Vᵀ))) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc]
    module
  have hAB : 1 + (2 : ℤ_[2]) • ((U + Uᵀ) * (V + Vᵀ)) =
      (1 + (2 : ℤ_[2]) • (U * (V + Vᵀ))) * (1 + (2 : ℤ_[2]) • (Uᵀ * (V + Vᵀ))) -
        (4 : ℤ_[2]) • (U * (V + Vᵀ) * Uᵀ * (V + Vᵀ)) := by
    rw [hS]
    module
  have hdetB :
      det (1 + (2 : ℤ_[2]) • (Uᵀ * (V + Vᵀ))) = det (1 + (2 : ℤ_[2]) • (U * (V + Vᵀ))) := by
    rw [← det_transpose, transpose_add, transpose_one, transpose_smul, transpose_mul,
      transpose_transpose, transpose_add, transpose_transpose, add_comm Vᵀ V, ← Matrix.smul_mul,
      det_one_add_mul_comm, Matrix.mul_smul]
  rcases two_dvd_det_one_add_two_smul_sub_one (U * (V + Vᵀ)) with ⟨a, ha⟩
  have hunit : IsUnit (det ((1 + (2 : ℤ_[2]) • (U * (V + Vᵀ))) *
      (1 + (2 : ℤ_[2]) • (Uᵀ * (V + Vᵀ))))) := by
    rw [det_mul, hdetB, ← sq, isUnit_pow_iff two_ne_zero]
    exact PadicInt.isUnit_of_two_dvd_sub_one ⟨a, ha⟩
  have hinv : ((1 + (2 : ℤ_[2]) • (U * (V + Vᵀ))) * (1 + (2 : ℤ_[2]) • (Uᵀ * (V + Vᵀ))))⁻¹ =
      1 + (2 : ℤ_[2]) • -(((1 + (2 : ℤ_[2]) • (U * (V + Vᵀ))) *
        (1 + (2 : ℤ_[2]) • (Uᵀ * (V + Vᵀ))))⁻¹ * ((U + Uᵀ) * (V + Vᵀ) +
          (2 : ℤ_[2]) • (U * (V + Vᵀ) * Uᵀ * (V + Vᵀ)))) := by
    have key : ((1 + (2 : ℤ_[2]) • (U * (V + Vᵀ))) * (1 + (2 : ℤ_[2]) • (Uᵀ * (V + Vᵀ))))⁻¹ *
        (1 + (2 : ℤ_[2]) • ((U + Uᵀ) * (V + Vᵀ) +
          (2 : ℤ_[2]) • (U * (V + Vᵀ) * Uᵀ * (V + Vᵀ)))) = 1 := by
      rw [← hS]
      exact nonsing_inv_mul _ hunit
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul] at key
    rw [smul_neg, ← sub_eq_add_neg]
    exact eq_sub_of_add_eq key
  have htr : (2 : ℤ_[2]) ∣ (((1 + (2 : ℤ_[2]) • (U * (V + Vᵀ))) *
      (1 + (2 : ℤ_[2]) • (Uᵀ * (V + Vᵀ))))⁻¹ * (U * (V + Vᵀ) * Uᵀ * (V + Vᵀ))).trace := by
    rw [hinv, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul, trace_add, trace_smul,
      trace_mul_add_transpose_eq, smul_eq_mul]
    exact dvd_add (dvd_mul_right 2 _) (dvd_mul_right 2 _)
  rw [hAB, sub_smul_eq_mul_one_add_smul _ _ _ hunit, det_mul, det_mul, hdetB]
  exact PadicInt.eight_dvd_mul_sub_one (PadicInt.eight_dvd_mul_self_sub_one ⟨a, ha⟩)
    (eight_dvd_det_one_sub_four_smul_sub_one _ htr)

lemma exists_eq_add_transpose {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ_[2]) (hA : Aᵀ = A)
    (hd : ∀ i, (2 : ℤ_[2]) ∣ A i i) : ∃ W : Matrix (Fin m) (Fin m) ℤ_[2], A = W + Wᵀ := by
  choose c hc using hd
  refine ⟨Matrix.of fun i j ↦ if i < j then A i j else if i = j then c i else 0,
    Matrix.ext fun i j ↦ ?_⟩
  rw [Matrix.add_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.of_apply]
  rcases lt_trichotomy i j with hij | rfl | hij
  · simp [hij, hij.not_gt, hij.ne']
  · simp [hc i, two_mul]
  · have hji : A j i = A i j := congrFun (congrFun hA i) j
    simp [hij, hij.not_gt, hij.ne', hji]

variable {J : ℕ} {n : Fin J → ℕ}

/-- **Truncations below a stop of congruent block diagonal Gram matrices have the same `χ₈` of the
determinant.** Let `G = ⊕_j 2 ^ j C_j` and `G' = ⊕_j 2 ^ j C'_j` be block diagonal matrices over
`ℤ_2` with symmetric blocks, the `C'_j` invertible, and `G' = Pᵀ G P`. If `C_(k + 1)` and `C'_k`
are even, of the form `W + Wᵀ`, then `∏_(j ≤ k) det C_j` and `∏_(j ≤ k) det C'_j` have the same
`χ₈`. -/
lemma χ₈_prod_det_eq_of_blockDiagonal'_eq (k : ℕ)
    (C C' W W' : (j : Fin J) → Matrix (Fin (n j)) (Fin (n j)) ℤ_[2]) (hC : ∀ j, (C j)ᵀ = C j)
    (hC' : ∀ j, (C' j)ᵀ = C' j) (hdet : ∀ j, IsUnit (C' j).det)
    (hW : ∀ j : Fin J, (j : ℕ) = k + 1 → C j = W j + (W j)ᵀ)
    (hW' : ∀ j : Fin J, (j : ℕ) = k → C' j = W' j + (W' j)ᵀ)
    (P : Matrix (Σ j, Fin (n j)) (Σ j, Fin (n j)) ℤ_[2])
    (hP : blockDiagonal' (fun j : Fin J ↦ (2 : ℤ_[2]) ^ (j : ℕ) • C' j) =
      Pᵀ * blockDiagonal' (fun j : Fin J ↦ (2 : ℤ_[2]) ^ (j : ℕ) • C j) * P) :
    ZMod.χ₈ (PadicInt.toZModPow 3 (∏ j : Fin J, if (j : ℕ) ≤ k then (C j).det else 1)) =
      ZMod.χ₈ (PadicInt.toZModPow 3 (∏ j : Fin J, if (j : ℕ) ≤ k then (C' j).det else 1)) := by
  classical
  set S : Matrix (Σ j, Fin (n j)) (Σ j, Fin (n j)) ℤ_[2] :=
    blockDiagonal' fun j : Fin J ↦ if (j : ℕ) ≤ k then 1 else 0 with hS
  set S' : Matrix (Σ j, Fin (n j)) (Σ j, Fin (n j)) ℤ_[2] :=
    blockDiagonal' fun j : Fin J ↦ if (j : ℕ) ≤ k then 0 else 1 with hS'
  set G : Matrix (Σ j, Fin (n j)) (Σ j, Fin (n j)) ℤ_[2] :=
    blockDiagonal' fun j : Fin J ↦ (2 : ℤ_[2]) ^ (j : ℕ) • C j with hG
  set G' : Matrix (Σ j, Fin (n j)) (Σ j, Fin (n j)) ℤ_[2] :=
    blockDiagonal' fun j : Fin J ↦ (2 : ℤ_[2]) ^ (j : ℕ) • C' j with hG'
  set Λ : Matrix (Σ j, Fin (n j)) (Σ j, Fin (n j)) ℤ_[2] :=
    blockDiagonal' fun j : Fin J ↦ if (j : ℕ) ≤ k then (2 : ℤ_[2]) ^ (j : ℕ) • 1 else 1 with hΛ
  set Ct : Matrix (Σ j, Fin (n j)) (Σ j, Fin (n j)) ℤ_[2] :=
    blockDiagonal' fun j : Fin J ↦ if (j : ℕ) ≤ k then C j else 1 with hCt
  set Ct' : Matrix (Σ j, Fin (n j)) (Σ j, Fin (n j)) ℤ_[2] :=
    blockDiagonal' fun j : Fin J ↦ if (j : ℕ) ≤ k then C' j else 1 with hCt'
  set V₀ : Matrix (Σ j, Fin (n j)) (Σ j, Fin (n j)) ℤ_[2] :=
    blockDiagonal' fun j : Fin J ↦ if (j : ℕ) ≤ k then 0 else if (j : ℕ) = k + 1 then W j
      else (2 : ℤ_[2]) ^ ((j : ℕ) - (k + 2)) • C j with hV₀
  set Lt : Matrix (Σ j, Fin (n j)) (Σ j, Fin (n j)) ℤ_[2] :=
    blockDiagonal' fun j : Fin J ↦ if (j : ℕ) ≤ k then (2 : ℤ_[2]) ^ (k - (j : ℕ)) • 1 else 0
      with hLt
  set E : Matrix (Σ j, Fin (n j)) (Σ j, Fin (n j)) ℤ_[2] :=
    blockDiagonal' fun j : Fin J ↦ if (j : ℕ) ≤ k then (2 : ℤ_[2]) ^ (k - (j : ℕ)) • (C' j)⁻¹
      else 0 with hE
  set U₀ : Matrix (Σ j, Fin (n j)) (Σ j, Fin (n j)) ℤ_[2] :=
    blockDiagonal' fun j : Fin J ↦ if (j : ℕ) < k then (2 : ℤ_[2]) ^ (k - (j : ℕ) - 1) • (C' j)⁻¹
      else if (j : ℕ) = k then (C' j)⁻¹ * W' j * (C' j)⁻¹ else 0 with hU₀
  have f1 : S * S = S := by
    rw [hS, ← blockDiagonal'_mul]
    congr 1
    funext j
    split_ifs <;> simp
  have f2 : S * S' = 0 := by
    rw [hS, hS', ← blockDiagonal'_mul, ← blockDiagonal'_zero]
    congr 1
    funext j
    split_ifs <;> simp
  have f3 : S' * S = 0 := by
    rw [hS, hS', ← blockDiagonal'_mul, ← blockDiagonal'_zero]
    congr 1
    funext j
    split_ifs <;> simp
  have f4 : S' * S' = S' := by
    rw [hS', ← blockDiagonal'_mul]
    congr 1
    funext j
    split_ifs <;> simp
  have f5 : Sᵀ = S := by
    rw [hS, blockDiagonal'_transpose]
    congr 1
    funext j
    split_ifs <;> simp
  have f6 : S'ᵀ = S' := by
    rw [hS', blockDiagonal'_transpose]
    congr 1
    funext j
    split_ifs <;> simp
  have fG : G = S * G * S + S' * G * S' := by
    rw [hS, hS', hG, ← blockDiagonal'_mul, ← blockDiagonal'_mul, ← blockDiagonal'_mul,
      ← blockDiagonal'_mul, ← blockDiagonal'_add]
    congr 1
    funext j
    by_cases hj : (j : ℕ) ≤ k <;> simp [hj]
  have fX : S * G * S + S' = Λ * Ct := by
    rw [hS, hS', hG, hΛ, hCt, ← blockDiagonal'_mul, ← blockDiagonal'_mul, ← blockDiagonal'_add,
      ← blockDiagonal'_mul]
    congr 1
    funext j
    by_cases hj : (j : ℕ) ≤ k <;> simp [hj]
  have fX' : S * G' * S + S' = Λ * Ct' := by
    rw [hS, hS', hG', hΛ, hCt', ← blockDiagonal'_mul, ← blockDiagonal'_mul, ← blockDiagonal'_add,
      ← blockDiagonal'_mul]
    congr 1
    funext j
    by_cases hj : (j : ℕ) ≤ k <;> simp [hj]
  have fLt : Λ * ((2 : ℤ_[2]) • Lt) = (2 : ℤ_[2]) ^ (k + 1) • S := by
    rw [hΛ, hLt, hS, ← blockDiagonal'_smul, ← blockDiagonal'_mul, ← blockDiagonal'_smul]
    congr 1
    funext j
    by_cases hj : (j : ℕ) ≤ k
    · have hpow : 2 * (2 : ℤ_[2]) ^ (k - (j : ℕ)) * 2 ^ (j : ℕ) = 2 ^ (k + 1) := by
        rw [← pow_succ', ← pow_add]
        congr 1
        omega
      simp [hj, smul_smul, hpow]
    · simp [hj]
  have fE : Ct' * E = Lt := by
    rw [hCt', hE, hLt, ← blockDiagonal'_mul]
    congr 1
    funext j
    by_cases hj : (j : ℕ) ≤ k
    · simp [hj, mul_nonsing_inv _ (hdet j)]
    · simp [hj]
  have fV : S' * G * S' = (2 : ℤ_[2]) ^ (k + 1) • (V₀ + V₀ᵀ) := by
    rw [hS', hG, hV₀, ← blockDiagonal'_mul, ← blockDiagonal'_mul, blockDiagonal'_transpose,
      ← blockDiagonal'_add, ← blockDiagonal'_smul]
    congr 1
    funext j
    by_cases hj : (j : ℕ) ≤ k
    · simp [hj]
    · by_cases hj1 : (j : ℕ) = k + 1
      · simp [hj1, hW j hj1]
      · have hpow : (2 : ℤ_[2]) ^ (k + 1) * (2 ^ ((j : ℕ) - (k + 2)) + 2 ^ ((j : ℕ) - (k + 2))) =
            2 ^ (j : ℕ) := by
          rw [← two_mul, ← mul_assoc, ← pow_succ, ← pow_add]
          congr 1
          omega
        simp [hj, hj1, hC j, smul_smul, ← add_smul, hpow]
  have fU : E = U₀ + U₀ᵀ := by
    rw [hE, hU₀, blockDiagonal'_transpose, ← blockDiagonal'_add]
    congr 1
    funext j
    have hinvT : ((C' j)⁻¹)ᵀ = (C' j)⁻¹ := by
      rw [transpose_nonsing_inv, hC' j]
    by_cases hjk : (j : ℕ) < k
    · have hpow :
          (2 : ℤ_[2]) ^ (k - (j : ℕ)) = 2 ^ (k - (j : ℕ) - 1) + 2 ^ (k - (j : ℕ) - 1) := by
        rw [← two_mul, ← pow_succ']
        congr 1
        omega
      simp [hjk.le, hjk, hinvT, hpow, add_smul]
    · by_cases hj : (j : ℕ) = k
      · have hsum :
            (C' j)⁻¹ * W' j * (C' j)⁻¹ + ((C' j)⁻¹ * W' j * (C' j)⁻¹)ᵀ = (C' j)⁻¹ := by
          rw [transpose_mul, transpose_mul, hinvT, Matrix.mul_assoc, ← Matrix.mul_add,
            ← Matrix.add_mul, ← hW' j hj, mul_nonsing_inv _ (hdet j), Matrix.mul_one]
        simp only [Pi.add_apply, hj, le_refl, lt_self_iff_false, Nat.sub_self, pow_zero, one_smul]
        exact hsum.symm
      · have hkj : ¬(j : ℕ) ≤ k := by
          omega
        simp [hjk, hj, hkj]
  have k1 (X : Matrix (Σ j, Fin (n j)) (Σ j, Fin (n j)) ℤ_[2]) : S * (S * X) = S * X := by
    rw [← Matrix.mul_assoc, f1]
  have hmain : Λ * Ct' = (S * P * S + S')ᵀ * (Λ * Ct) * (S * P * S + S') +
      S * Pᵀ * ((2 : ℤ_[2]) ^ (k + 1) • (V₀ + V₀ᵀ)) * P * S := by
    rw [← fX', ← fX, ← fV, hP]
    exact proj_conj_add_eq f1 f2 f3 f4 f5 f6 fG
  have hD : S * Pᵀ * ((2 : ℤ_[2]) ^ (k + 1) • (V₀ + V₀ᵀ)) * P * S =
      Λ * ((2 : ℤ_[2]) • Lt) * (S * Pᵀ * V₀ * P * S + (S * Pᵀ * V₀ * P * S)ᵀ) := by
    rw [fLt]
    simp only [transpose_mul, f5, transpose_transpose, Matrix.mul_add, Matrix.add_mul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc, k1, smul_add]
  have hfinal : (S * P * S + S')ᵀ * (Λ * Ct) * (S * P * S + S') = Λ * Ct' * (1 + (2 : ℤ_[2]) •
      ((U₀ + U₀ᵀ) * (-(S * Pᵀ * V₀ * P * S) + (-(S * Pᵀ * V₀ * P * S))ᵀ))) := by
    rw [eq_sub_of_add_eq hmain.symm, hD, ← fU, ← fE, transpose_neg, ← neg_add]
    simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_neg, Matrix.smul_mul,
      Matrix.mul_assoc]
    module
  have hΛne : det Λ ≠ 0 := by
    rw [hΛ, det_blockDiagonal', Finset.prod_ne_zero_iff]
    intro j _
    split_ifs
    · rw [det_smul, det_one, mul_one]
      exact pow_ne_zero _ (pow_ne_zero _ two_ne_zero)
    · rw [det_one]
      exact one_ne_zero
  have hdet' : det (S * P * S + S') * (det Λ * det Ct) * det (S * P * S + S') =
      det Λ * det Ct' * det (1 + (2 : ℤ_[2]) • ((U₀ + U₀ᵀ) * (-(S * Pᵀ * V₀ * P * S) +
        (-(S * Pᵀ * V₀ * P * S))ᵀ))) := by
    simpa only [det_mul, det_transpose] using congrArg det hfinal
  have hcancel : det (S * P * S + S') * det Ct * det (S * P * S + S') = det Ct' *
      det (1 + (2 : ℤ_[2]) • ((U₀ + U₀ᵀ) * (-(S * Pᵀ * V₀ * P * S) +
        (-(S * Pᵀ * V₀ * P * S))ᵀ))) := by
    refine mul_left_cancel₀ hΛne ?_
    linear_combination hdet'
  have hw : (8 : ℤ_[2]) ∣ det (1 + (2 : ℤ_[2]) • ((U₀ + U₀ᵀ) * (-(S * Pᵀ * V₀ * P * S) +
      (-(S * Pᵀ * V₀ * P * S))ᵀ))) - 1 :=
    eight_dvd_det_one_add_two_smul_mul_sub_one U₀ _
  have hCt'unit : IsUnit (det Ct') := by
    rw [hCt', det_blockDiagonal']
    refine IsUnit.prod_univ_iff.mpr fun j ↦ ?_
    split_ifs
    · exact hdet j
    · rw [det_one]
      exact isUnit_one
  have hA : IsUnit (det (S * P * S + S')) := by
    refine isUnit_of_mul_isUnit_left (y := det Ct * det (S * P * S + S')) ?_
    rw [← mul_assoc, hcancel]
    exact hCt'unit.mul (PadicInt.isUnit_of_two_dvd_sub_one (dvd_trans ⟨4, by norm_num⟩ hw))
  have hprod (D : (j : Fin J) → Matrix (Fin (n j)) (Fin (n j)) ℤ_[2]) :
      ∏ j : Fin J, (if (j : ℕ) ≤ k then (D j).det else 1) =
        det (blockDiagonal' fun j : Fin J ↦ if (j : ℕ) ≤ k then D j else 1) := by
    rw [det_blockDiagonal']
    exact Finset.prod_congr rfl fun j _ ↦ by split_ifs <;> simp
  rw [hprod, hprod, ← hCt, ← hCt', ← PadicInt.χ₈_toZModPow_mul_mul hA, hcancel, map_mul, map_mul,
    PadicInt.toZModPow_three_eq_of_eight_dvd hw, map_one, map_one, mul_one]

end Matrix

namespace LinearMap.BilinForm

variable {M M' : Type*} [AddCommGroup M] [Module ℤ_[2] M] [AddCommGroup M'] [Module ℤ_[2] M']
  {B : BilinForm ℤ_[2] M} {B' : BilinForm ℤ_[2] M'} {N : ℕ → Submodule ℤ_[2] M}
  {N' : ℕ → Submodule ℤ_[2] M'} {J j : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
  (h : B.IsJordanSplitting ((2 : ℕ) : ℤ_[2]) N) (h' : B'.IsJordanSplitting ((2 : ℕ) : ℤ_[2]) N')
  (b : Basis ι ℤ_[2] (N j))

lemma IsJordanSplitting.two_dvd_toMatrix₂_unitForm
    (hj : ∀ x ∈ N j, ((2 : ℕ) : ℤ_[2]) ^ (j + 1) ∣ B x x) (i : ι) :
    (2 : ℤ_[2]) ∣ toMatrix₂ b b (h.unitForm j) i i := by
  have hx : ((2 : ℕ) : ℤ_[2]) ^ j * ((2 : ℕ) : ℤ_[2]) ∣
      ((2 : ℕ) : ℤ_[2]) ^ j * toMatrix₂ b b (h.unitForm j) i i := by
    rw [toMatrix₂_apply, h.pow_mul_unitForm, ← pow_succ]
    exact hj _ (b i).2
  exact_mod_cast (mul_dvd_mul_iff_left (pow_ne_zero j PadicInt.irreducible_p.ne_zero)).mp hx

lemma IsJordanSplitting.transpose_toMatrix₂_unitForm (hB : B.IsSymm) :
    (toMatrix₂ b b (h.unitForm j))ᵀ = toMatrix₂ b b (h.unitForm j) :=
  Matrix.ext fun a c ↦ by
    rw [Matrix.transpose_apply, toMatrix₂_apply, toMatrix₂_apply, (h.isSymm_unitForm hB).eq]

lemma IsJordanSplitting.toMatrix₂_collectedBasis (hJ : ∀ j, J ≤ j → N j = ⊥) {m : Fin J → ℕ}
    (v : (j : Fin J) → Basis (Fin (m j)) ℤ_[2] (N j)) :
    toMatrix₂ ((h.isInternal_fin hJ).collectedBasis v) ((h.isInternal_fin hJ).collectedBasis v) B =
      Matrix.blockDiagonal' fun j : Fin J ↦ (2 : ℤ_[2]) ^ (j : ℕ) •
        toMatrix₂ (v j) (v j) (h.unitForm j) := by
  refine Matrix.ext fun x y ↦ ?_
  rcases x with ⟨j, a⟩
  rcases y with ⟨k, c⟩
  rw [LinearMap.toMatrix₂_apply, (h.isInternal_fin hJ).collectedBasis_coe]
  rcases eq_or_ne j k with rfl | hjk
  · rw [Matrix.blockDiagonal'_apply_eq, Matrix.smul_apply, smul_eq_mul, h.apply_basis,
      Nat.cast_ofNat]
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hjk, h.apply_eq_zero j k (Fin.val_ne_of_ne hjk) _
      (v j a).2 _ (v k c).2]

variable [Module.Free ℤ_[2] M] [Module.Finite ℤ_[2] M] [Module.Free ℤ_[2] M']
  [Module.Finite ℤ_[2] M']

/-- **The product of the dyadic signs below a stop is an isometry invariant.** Let `N` and `N'` be
Jordan splittings of isometric symmetric bilinear forms over `ℤ_2`, with constituents vanishing from
the index `J` on, and let `k` be such that the constituent `N (k + 1)` and the constituent `N' k`
have type `II` (as do then `N k` and `N' (k + 1)`, the types being isometry invariants). Then the
products of the signs `ε_q = χ₈(det f_q)` of the constituents of scale at most `2 ^ k` agree. -/
lemma IsJordanSplitting.prod_dyadicSign_le_eq (hB : B.IsSymm) (hB' : B'.IsSymm)
    (hJ : ∀ j, J ≤ j → N j = ⊥) (hJ' : ∀ j, J ≤ j → N' j = ⊥) (hBB' : B.Equivalent B') {k : ℕ}
    (hk : ∀ x ∈ N (k + 1), ((2 : ℕ) : ℤ_[2]) ^ (k + 1 + 1) ∣ B x x)
    (hk' : ∀ x ∈ N' k, ((2 : ℕ) : ℤ_[2]) ^ (k + 1) ∣ B' x x) :
    ∏ j : Fin J, (if (j : ℕ) ≤ k then h.dyadicSign j else 1) =
      ∏ j : Fin J, (if (j : ℕ) ≤ k then h'.dyadicSign j else 1) := by
  classical
  rcases hBB' with ⟨e⟩
  have hrank (j : ℕ) : finrank ℤ_[2] (N j) = finrank ℤ_[2] (N' j) :=
    h.finrank_eq_of_equivalent h' ⟨e⟩ PadicInt.irreducible_p.ne_zero
      PadicInt.irreducible_p.not_isUnit j
  have hW (j : Fin J) (hj : (j : ℕ) = k + 1) : ∃ W : Matrix (Fin (finrank ℤ_[2] (N j)))
      (Fin (finrank ℤ_[2] (N j))) ℤ_[2], toMatrix₂ (finBasis ℤ_[2] (N j))
        (finBasis ℤ_[2] (N j)) (h.unitForm j) = W + Wᵀ :=
    Matrix.exists_eq_add_transpose _ (h.transpose_toMatrix₂_unitForm _ hB)
      (h.two_dvd_toMatrix₂_unitForm _ (hj ▸ hk))
  have hW' (j : Fin J) (hj : (j : ℕ) = k) : ∃ W : Matrix (Fin (finrank ℤ_[2] (N j)))
      (Fin (finrank ℤ_[2] (N j))) ℤ_[2], toMatrix₂
        ((finBasis ℤ_[2] (N' j)).reindex (finCongr (hrank j).symm))
        ((finBasis ℤ_[2] (N' j)).reindex (finCongr (hrank j).symm)) (h'.unitForm j) = W + Wᵀ :=
    Matrix.exists_eq_add_transpose _ (h'.transpose_toMatrix₂_unitForm _ hB')
      (h'.two_dvd_toMatrix₂_unitForm _ (hj ▸ hk'))
  choose! W hWspec using hW
  choose! W' hW'spec using hW'
  convert Matrix.χ₈_prod_det_eq_of_blockDiagonal'_eq k
    (fun j ↦ toMatrix₂ (finBasis ℤ_[2] (N j)) (finBasis ℤ_[2] (N j)) (h.unitForm j))
    (fun j ↦ toMatrix₂ ((finBasis ℤ_[2] (N' j)).reindex (finCongr (hrank j).symm))
      ((finBasis ℤ_[2] (N' j)).reindex (finCongr (hrank j).symm)) (h'.unitForm j)) W W'
    (fun j ↦ h.transpose_toMatrix₂_unitForm _ hB) (fun j ↦ h'.transpose_toMatrix₂_unitForm _ hB')
    (fun j ↦ isUnit_det_toMatrix₂_of_isPerfPair _ (h'.isPerfPair_unitForm j)) hWspec hW'spec
    (((h.isInternal_fin hJ).collectedBasis fun j ↦ finBasis ℤ_[2] (N j)).toMatrix
      (((h'.isInternal_fin hJ').collectedBasis fun j ↦
        (finBasis ℤ_[2] (N' j)).reindex (finCongr (hrank j).symm)).map e.symm.toLinearEquiv)) ?_
    using 1
  · rw [map_prod, map_prod]
    exact Finset.prod_congr rfl fun j _ ↦ by
      split_ifs
      · rfl
      · rw [map_one, map_one]
  · rw [map_prod, map_prod]
    exact Finset.prod_congr rfl fun j _ ↦ by
      split_ifs
      · rw [IsJordanSplitting.dyadicSign, det_toMatrix₂_reindex]
      · rw [map_one, map_one]
  · rw [← h.toMatrix₂_collectedBasis hJ, ← h'.toMatrix₂_collectedBasis hJ',
      LinearMap.toMatrix₂_mul_basis_toMatrix, e.symm.toMatrix₂_basis_map]

end LinearMap.BilinForm

namespace TauCeti.IntegralLattice

namespace DyadicBlock

variable (a b : DyadicBlock) (l l' : List DyadicBlock) (X : List ℤ)

/-- The scale `2 ^ s` carries **no constituent of type `I`** in the list `l` of nonzero
constituents of a `2`-adic symbol: the constituent of scale `2 ^ s` is zero or of type `II`. A
*stop* (Conway and Sloane) is a pair of scales `2 ^ k`, `2 ^ (k + 1)` both of this kind. -/
def TypeTwoAt (s : ℕ) : Prop :=
  ∀ b ∈ l, b.scale = s → b.type = .II

lemma map_modifyHead_trainSign (L : List (List DyadicBlock)) :
    (L.modifyHead (a :: ·)).map trainSign = (L.map trainSign).modifyHead (a.sign * ·) := by
  cases L with
  | nil => rfl
  | cons T L => simp [trainSign]

lemma modifyHead_mul_modifyHead_mul (u v : ℤ) :
    (X.modifyHead (u * ·)).modifyHead (v * ·) = X.modifyHead (v * u * ·) := by
  cases X <;> simp [mul_assoc]

lemma modifyHead_one_mul : X.modifyHead (1 * ·) = X := by
  cases X <;> simp

lemma trains_cons_cons : trains (a :: b :: l) =
    if sameTrain a b then (trains (b :: l)).modifyHead (a :: ·) else [a] :: trains (b :: l) :=
  splitBy_cons_cons l sameTrain a b

/-- **The signs of the trains are determined by the sign products below the stops.** Let `l` and
`l'` be lists of nonzero constituents of `2`-adic symbols, in strictly increasing order of scale,
with the same scales and types, and with signs `±1`. If, for some `c`, at every stop `k` from the
first scale of `l` on, the product of the signs of the constituents of `l` of scale at most
`2 ^ k`, times `c`, is that of `l'`, then the signs of the trains of `l`, the first multiplied by
`c`, are those of `l'`. -/
lemma trainSigns_eq_of_prod_filter_eq (hl : l.Pairwise fun b c ↦ b.scale < c.scale)
    (hdata : l.map (fun b ↦ (b.scale, b.type)) = l'.map (fun b ↦ (b.scale, b.type)))
    (hsign : ∀ b ∈ l', b.sign = 1 ∨ b.sign = -1) (c : ℤ)
    (hstop : ∀ k, (∀ a ∈ l.head?, a.scale ≤ k) → TypeTwoAt l k → TypeTwoAt l (k + 1) →
      c * ((l.filter (·.scale ≤ k)).map sign).prod = ((l'.filter (·.scale ≤ k)).map sign).prod) :
    ((trains l).map trainSign).modifyHead (c * ·) = (trains l').map trainSign := by
  induction l generalizing l' c with
  | nil =>
    rcases l' with _ | ⟨a', l'⟩
    · rfl
    · simp at hdata
  | cons a rest ih =>
    rcases l' with _ | ⟨a', rest'⟩
    · simp at hdata
    rw [List.map_cons, List.map_cons, List.cons.injEq, Prod.mk.injEq] at hdata
    rcases hdata with ⟨⟨hsc, hty⟩, hrest⟩
    have ha' : a'.sign * a'.sign = 1 := by
      rcases hsign a' List.mem_cons_self with h | h <;> rw [h] <;> norm_num
    rcases rest with _ | ⟨b, rest⟩
    · rcases rest' with _ | ⟨b', rest'⟩
      · have h1 : c * a.sign = a'.sign := by
          simpa [hsc] using hstop (a.scale + 1) (by simp)
            (fun x hx hxs ↦ by rw [List.mem_singleton] at hx; subst hx; omega)
            (fun x hx hxs ↦ by rw [List.mem_singleton] at hx; subst hx; omega)
        simp [trains_singleton, trainSign, h1]
      · simp at hrest
    · rcases rest' with _ | ⟨b', rest'⟩
      · simp at hrest
      have hdata' : (b :: rest).map (fun b ↦ (b.scale, b.type)) =
          (b' :: rest').map (fun b ↦ (b.scale, b.type)) := hrest
      rw [List.map_cons, List.map_cons, List.cons.injEq, Prod.mk.injEq] at hrest
      rcases hrest with ⟨⟨hscb, htyb⟩, -⟩
      rw [List.pairwise_cons] at hl
      rcases hl with ⟨hla, hl⟩
      have hab : a.scale < b.scale := hla b List.mem_cons_self
      have hsame : sameTrain a' b' = sameTrain a b := by
        simp only [sameTrain, ← hsc, ← hty, ← hscb, ← htyb]
      have htail (k : ℕ) (hk : b.scale ≤ k) (h0 : TypeTwoAt (b :: rest) k)
          (h1 : TypeTwoAt (b :: rest) (k + 1)) :
          c * (a.sign * (((b :: rest).filter (·.scale ≤ k)).map sign).prod) =
            a'.sign * (((b' :: rest').filter (·.scale ≤ k)).map sign).prod := by
        have h : c * (((a :: b :: rest).filter (·.scale ≤ k)).map sign).prod =
            (((a' :: b' :: rest').filter (·.scale ≤ k)).map sign).prod :=
          hstop k (by simpa using (hab.trans_le hk).le)
            (fun x hx hxs ↦ by
              rcases List.mem_cons.mp hx with rfl | hx
              · omega
              · exact h0 x hx hxs)
            (fun x hx hxs ↦ by
              rcases List.mem_cons.mp hx with rfl | hx
              · omega
              · exact h1 x hx hxs)
        simp only [List.filter_cons, show a.scale ≤ k by omega, show a'.scale ≤ k by omega] at h ⊢
        exact h
      have hsign' : ∀ x ∈ b' :: rest', x.sign = 1 ∨ x.sign = -1 :=
        fun x hx ↦ hsign x (List.mem_cons_of_mem a' hx)
      have hsc' (x' : DyadicBlock) (hx' : x' ∈ b' :: rest') :
          ∃ x ∈ b :: rest, x.scale = x'.scale := by
        have hmap : (b :: rest).map (·.scale) = (b' :: rest').map (·.scale) := by
          simpa [Function.comp_def] using congrArg (List.map Prod.fst) hdata'
        have hmem : x'.scale ∈ (b :: rest).map (·.scale) := hmap ▸ List.mem_map_of_mem hx'
        simpa [eq_comm] using hmem
      have hgt (x : DyadicBlock) (hx : x ∈ b :: rest) : b.scale ≤ x.scale := by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact le_rfl
        · exact ((List.pairwise_cons.mp hl).1 x hx).le
      rw [trains_cons_cons, trains_cons_cons, hsame]
      cases hab' : sameTrain a b
      · have hfirst : c * a.sign = a'.sign := by
          have hk₀ (x : DyadicBlock) (hx : x ∈ b :: rest) :
              a.scale + (if a.type = .I then 1 else 0) < x.scale := by
            have hx' : b.scale ≤ x.scale := hgt x hx
            cases hta : a.type
            · have hb : b.scale ≠ a.scale + 1 := by
                intro hb
                simp [sameTrain, hta, hb] at hab'
              simp only [↓reduceIte]
              omega
            · simp only [reduceCtorEq, ↓reduceIte]
              omega
          have h0 : TypeTwoAt (a :: b :: rest) (a.scale + (if a.type = .I then 1 else 0)) := by
            intro x hx hxs
            rcases List.mem_cons.mp hx with rfl | hx
            · cases hta : x.type
              · simp [hta] at hxs
              · rfl
            · exact absurd hxs (hk₀ x hx).ne'
          have h1 :
              TypeTwoAt (a :: b :: rest) (a.scale + (if a.type = .I then 1 else 0) + 1) := by
            intro x hx hxs
            rcases List.mem_cons.mp hx with rfl | hx
            · omega
            · rcases List.mem_cons.mp hx with rfl | hx
              · cases htb : x.type
                · simp [sameTrain, htb, hxs] at hab'
                · rfl
              · have hbx : b.scale < x.scale := (List.pairwise_cons.mp hl).1 x hx
                have hb₀ : a.scale + (if a.type = .I then 1 else 0) < b.scale :=
                  hk₀ b List.mem_cons_self
                omega
          have e1 : (a :: b :: rest).filter (·.scale ≤ a.scale + (if a.type = .I then 1 else 0)) =
              [a] := by
            rw [List.filter_cons_of_pos (by simp),
              List.filter_eq_nil_iff.mpr fun x hx ↦ by simpa using hk₀ x hx]
          have e2 :
              (a' :: b' :: rest').filter (·.scale ≤ a.scale + (if a.type = .I then 1 else 0)) =
                [a'] := by
            rw [List.filter_cons_of_pos (by simp [← hsc]),
              List.filter_eq_nil_iff.mpr fun x' hx' ↦ by
                rcases hsc' x' hx' with ⟨x, hx, hxx'⟩
                simpa [← hxx'] using hk₀ x hx]
          simpa [e1, e2] using hstop (a.scale + (if a.type = .I then 1 else 0)) (by simp) h0 h1
        have hX : ((trains (b :: rest)).map trainSign).modifyHead (1 * ·) =
            (trains (b' :: rest')).map trainSign :=
          ih (b' :: rest') hl hdata' hsign' 1 fun k hk h0 h1 ↦ by
            have h : a'.sign * (((b :: rest).filter (·.scale ≤ k)).map sign).prod =
                a'.sign * (((b' :: rest').filter (·.scale ≤ k)).map sign).prod := by
              rw [← htail k (by simpa using hk) h0 h1, ← mul_assoc, hfirst]
            rw [one_mul]
            exact mul_left_cancel₀ (by rintro h0; simp [h0] at ha') h
        rw [modifyHead_one_mul] at hX
        simp [trainSign, hfirst, hX]
      · simp only [↓reduceIte]
        rw [map_modifyHead_trainSign, map_modifyHead_trainSign, modifyHead_mul_modifyHead_mul,
          ← ih (b' :: rest') hl hdata' hsign' (c * a.sign * a'.sign) fun k hk h0 h1 ↦ ?_,
          modifyHead_mul_modifyHead_mul]
        · rw [show a'.sign * (c * a.sign * a'.sign) = c * a.sign by
            linear_combination (c * a.sign) * ha']
        · linear_combination a'.sign * htail k (by simpa using hk) h0 h1 +
            (((b' :: rest').filter (·.scale ≤ k)).map sign).prod * ha'

end DyadicBlock

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {L : IntegralLattice V} {M : IntegralLattice W} [L.IsNondegenerate] [M.IsNondegenerate] {k : ℕ}

lemma forall_mem_pow_dvd_of_dyadicJordanType_eq (hk : L.dyadicJordanType k = .II) :
    ∀ x ∈ (L.exists_isJordanSplitting_localIntegralForm 2 L.form_nondegenerate).choose k,
      ((2 : ℕ) : ℤ_[2]) ^ (k + 1) ∣ L.localIntegralForm 2 x x := by
  classical
  rw [dyadicJordanType] at hk
  split_ifs at hk with hc
  exact hc

/-- **The product of the dyadic signs below a stop is a genus invariant.** If the dyadic Jordan
constituents of scales `2 ^ k` and `2 ^ (k + 1)` of a nondegenerate lattice `L` both have type `II`
(zero constituents included), then lattices in the genus of `L` have the same product of the signs
`ε_q = χ₈(det f_q)` of their dyadic Jordan constituents of scale at most `2 ^ k`. -/
lemma SameGenus.prod_dyadicJordanSign_le_eq (h : L.SameGenus M) (hk : L.dyadicJordanType k = .II)
    (hk1 : L.dyadicJordanType (k + 1) = .II) : ∏ j : Fin (L.determinant.natAbs.factorization 2 + 1),
      (if (j : ℕ) ≤ k then L.dyadicJordanSign j else 1) =
        ∏ j : Fin (L.determinant.natAbs.factorization 2 + 1),
          (if (j : ℕ) ≤ k then M.dyadicJordanSign j else 1) :=
  (L.exists_isJordanSplitting_localIntegralForm 2
    L.form_nondegenerate).choose_spec.prod_dyadicSign_le_eq
    (M.exists_isJordanSplitting_localIntegralForm 2 M.form_nondegenerate).choose_spec
    (L.isSymm_localIntegralForm 2) (M.isSymm_localIntegralForm 2)
    (fun _ hj ↦ dyadicJordanSplitting_eq_bot hj)
    (fun _ hj ↦ dyadicJordanSplitting_eq_bot (h.natAbs_determinant_eq ▸ hj))
    (h.localIntegralForm_equivalent 2) (forall_mem_pow_dvd_of_dyadicJordanType_eq hk1)
    (forall_mem_pow_dvd_of_dyadicJordanType_eq ((h.dyadicJordanType_eq k).symm.trans hk))

lemma pairwise_dyadicConstituents :
    L.dyadicConstituents.Pairwise fun b c ↦ b.scale < c.scale := by
  rw [dyadicConstituents, List.pairwise_map]
  exact List.pairwise_lt_range.filter _

lemma dyadicJordanType_eq_of_typeTwoAt (h : DyadicBlock.TypeTwoAt L.dyadicConstituents k) :
    L.dyadicJordanType k = .II := by
  classical
  by_contra hne
  have hrank : L.jordanRank 2 k ≠ 0 := by
    intro h0
    refine hne ?_
    rw [dyadicJordanType, ite_eq_left]
    intro x hx
    rw [Submodule.finrank_eq_zero.mp h0, Submodule.mem_bot] at hx
    rw [hx, map_zero]
    exact dvd_zero _
  have hk : k ≤ L.determinant.natAbs.factorization 2 := by
    by_contra hk
    exact hrank (L.jordanRank_eq_zero_of_lt 2 (by omega))
  exact hne (h ⟨k, L.jordanRank 2 k, L.dyadicJordanType k, L.dyadicJordanSign k,
    L.dyadicJordanOddity k⟩ (List.mem_map.mpr ⟨k, List.mem_filter.mpr
      ⟨List.mem_range.mpr (by omega), by simpa using hrank⟩, rfl⟩) rfl)

variable (k) in
lemma prod_filter_dyadicConstituents :
    ((L.dyadicConstituents.filter (·.scale ≤ k)).map DyadicBlock.sign).prod =
      ∏ j : Fin (L.determinant.natAbs.factorization 2 + 1),
        (if (j : ℕ) ≤ k then L.dyadicJordanSign j else 1) := by
  rw [← Finset.prod_range (fun j ↦ if j ≤ k then L.dyadicJordanSign j else 1),
    ← Finset.prod_filter, ← Finset.prod_filter_of_ne (p := fun j ↦ L.jordanRank 2 j ≠ 0)
      fun i _ ↦ mt (dyadicJordanSign_eq_one i), Finset.filter_filter,
    Finset.prod_eq_multiset_prod, Finset.filter_val, Finset.range_val, Multiset.range,
    Multiset.filter_coe, Multiset.map_coe, Multiset.prod_coe, dyadicConstituents, List.filter_map,
    List.map_map, List.filter_filter]
  congr 2

/-- **The signs of the trains of the canonical `2`-adic symbol are genus invariants.** Lattices in
the same genus have the same signs of the trains: the sign of each train is the quotient of the
sign products below the stops that bound it, which are genus invariants. -/
lemma SameGenus.trainSigns_eq (h : L.SameGenus M) : L.trainSigns = M.trainSigns := by
  rw [trainSigns, trainSigns,
    ← DyadicBlock.modifyHead_one_mul ((DyadicBlock.trains L.dyadicConstituents).map _)]
  refine DyadicBlock.trainSigns_eq_of_prod_filter_eq _ _ pairwise_dyadicConstituents
    h.map_dyadicConstituents_eq (fun b hb ↦ ?_) 1 fun k _ h0 h1 ↦ ?_
  · rcases List.mem_map.mp hb with ⟨v, -, rfl⟩
    exact (M.exists_isJordanSplitting_localIntegralForm 2
      M.form_nondegenerate).choose_spec.dyadicSign_eq_one_or_eq_neg_one
  · rw [one_mul, prod_filter_dyadicConstituents, prod_filter_dyadicConstituents,
      ← h.natAbs_determinant_eq]
    exact h.prod_dyadicJordanSign_le_eq (dyadicJordanType_eq_of_typeTwoAt h0)
      (dyadicJordanType_eq_of_typeTwoAt h1)

end TauCeti.IntegralLattice
