import LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbol
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.Padics.RingHoms

/-!
# The Conway genus symbol of an integral lattice: signs and dyadic types

The Conway genus symbol (LMFDB `lattice.conway_genus_symbol`; Conway and Sloane, *Sphere Packings,
Lattices and Groups*, Chapter 15, §7) of a nondegenerate integral lattice `L` records, for every
prime `p` and every `p`-adic Jordan decomposition `L ⊗ ℤ_p = ⊕_q q f_q` over the powers `q = p ^ k`,
with unimodular forms `f_q`, the rank `n_q` of `f_q` and a sign `ε_q`; at `p = 2` it also records
the type `I` (odd) or `II` (even) of `f_q`, and oddities. The type of `L`, its signature and the
ranks `n_q` are the genus invariants of `LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbol`.

This file proves that the signs `ε_q = (det f_q / p)` at an odd prime `p` and the types of the
dyadic constituents do not depend on the Jordan decomposition and are genus invariants. For the
signs, the key point is that if `N` and `N'` are two Jordan splittings of a symmetric form `B` over
`ℤ_p`, the vectors `x` with `p ^ j ∣ B x y` for all `y` are, modulo the constituents of index above
`j` and `p` times the module, the vectors of `N j`; so projecting a basis of `N' j` to `N j` modulo
these gives a matrix `P` with `A' ≡ Pᵀ A P mod p` for the Gram matrices `A`, `A'` of the unit
forms, and `det A' ≡ (det P) ^ 2 det A mod p`. For the types, `f_q` is even exactly when `2 q`
divides the norm of every vector `x` with `q ∣ B x y` for all `y`, a condition that does not
mention the splitting.

At `p = 2`, Conway and Sloane's signs `ε_q = (2 | det f_q)` and the oddities of the constituents
depend on the decomposition; only the oddity of each compartment and the sign of each train of the
canonical `2`-adic symbol are invariants (oddity fusion and sign walking), which is not formalised.
That the symbol and the signature determine the genus is proved at the odd primes in
`LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolOddPrime`.

## Main definitions

* `LinearMap.BilinForm.IsJordanSplitting.unitForm`: the unimodular form `C` of a Jordan
  constituent, `B|N j = p ^ j • C`.
* `LinearMap.BilinForm.IsJordanSplitting.sign` (LMFDB `lattice.conway_genus_symbol`): the sign of
  a Jordan constituent over `ℤ_p`.
* `TauCeti.IntegralLattice.jordanSign` (LMFDB `lattice.conway_genus_symbol`): the sign `ε_q` of an
  integral lattice at an odd prime.
* `TauCeti.IntegralLattice.dyadicJordanType` (LMFDB `lattice.conway_genus_symbol`): the type of a
  dyadic Jordan constituent.
* `TauCeti.IntegralLattice.ConwayGenusSymbolSigned` and
  `TauCeti.IntegralLattice.conwayGenusSymbolSigned` (LMFDB `lattice.conway_genus_symbol`,
  partial): the type, the signature, the Jordan ranks, the signs at the odd primes and the dyadic
  types.

## Main results

* `LinearMap.BilinForm.IsJordanSplitting.sign_eq_quadraticChar`: the sign can be computed in any
  basis of the constituent.
* `LinearMap.BilinForm.IsJordanSplitting.sign_eq_one_or_eq_neg_one`: the sign is `±1`.
* `LinearMap.BilinForm.IsJordanSplitting.sign_eq_of_equivalent`: the signs are isometry invariants,
  and in particular do not depend on the Jordan splitting.
* `TauCeti.IntegralLattice.jordanSign_eq` and `TauCeti.IntegralLattice.dyadicJordanType_eq`: the
  signs and the dyadic types can be read off any Jordan splitting.
* `TauCeti.IntegralLattice.jordanSign_eq_one_or_eq_neg_one`: the signs are `±1`.
* `TauCeti.IntegralLattice.SameGenus.jordanSign_eq` and
  `TauCeti.IntegralLattice.SameGenus.dyadicJordanType_eq`: they are genus invariants.
* `TauCeti.IntegralLattice.SameGenus.conwayGenusSymbolSigned_eq`: the formalised part of the
  Conway genus symbol is a genus invariant.
-/

open Module

open LinearMap (BilinForm)

namespace PadicInt

variable {p : ℕ} [Fact p.Prime] {j : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma toZMod_eq_of_pow_succ_dvd {x y : ℤ_[p]}
    (hxy : (p : ℤ_[p]) ^ (j + 1) ∣ (p : ℤ_[p]) ^ j * x - (p : ℤ_[p]) ^ j * y) :
    toZMod x = toZMod y := by
  rw [← mul_sub, pow_succ, mul_dvd_mul_iff_left (pow_ne_zero j irreducible_p.ne_zero)] at hxy
  rcases hxy with ⟨c, hc⟩
  rw [← sub_eq_zero, ← map_sub, hc, map_mul, map_natCast, ZMod.natCast_self, zero_mul]

lemma quadraticChar_toZMod_det_eq {A A' P Q : Matrix ι ι ℤ_[p]}
    (hP : A'.map toZMod = (P.transpose * A * P).map toZMod)
    (hQ : A.map toZMod = (Q.transpose * A' * Q).map toZMod) :
    quadraticChar (ZMod p) (toZMod A'.det) = quadraticChar (ZMod p) (toZMod A.det) := by
  have hdet {X Y R : Matrix ι ι ℤ_[p]} (h : X.map toZMod = (R.transpose * Y * R).map toZMod) :
      toZMod X.det = toZMod R.det ^ 2 * toZMod Y.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, h, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
      Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, map_mul, map_mul]
    ring1
  by_cases hA : toZMod A'.det = 0
  · rw [hA, hdet hQ, hA, mul_zero]
  · rw [hdet hP, map_mul, map_pow, quadraticChar_sq_one
      (ne_zero_pow two_ne_zero (left_ne_zero_of_mul (hdet hP ▸ hA))), one_mul]

end PadicInt

namespace LinearMap.BilinForm

variable {p : ℕ} [Fact p.Prime] {M M' : Type*} [AddCommGroup M] [Module ℤ_[p] M] [AddCommGroup M']
  [Module ℤ_[p] M'] {B : BilinForm ℤ_[p] M} {B' : BilinForm ℤ_[p] M'} {N : ℕ → Submodule ℤ_[p] M}
  {N' : ℕ → Submodule ℤ_[p] M'} {j : ℕ} {ι κ R K : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] [CommRing R] [AddCommGroup K] [Module R K] {C : BilinForm R K}

lemma det_toMatrix₂_reindex (b : Basis ι R K) (e : ι ≃ κ) :
    (toMatrix₂ (b.reindex e) (b.reindex e) C).det = (toMatrix₂ b b C).det := by
  rw [← Matrix.det_submatrix_equiv_self e.symm]
  congr 1
  ext a c
  simp

lemma isUnit_det_toMatrix₂_of_isPerfPair (b : Basis ι R K) (hC : C.IsPerfPair) :
    IsUnit (toMatrix₂ b b C).det := by
  have : Module.Finite R K := .of_basis b
  have : Module.Free R K := .of_basis b
  have hC' : C = b.toDualEquiv.toLinearMap ∘ₗ Matrix.toLin b b (toMatrix₂ b b C).transpose :=
    b.ext fun i ↦ b.ext fun j ↦ by simp [Basis.toDual_apply]
  have hbij : Function.Bijective C := hC.bijective_left
  rw [hC', LinearMap.coe_comp, LinearEquiv.coe_coe, b.toDualEquiv.bijective.of_comp_iff'] at hbij
  rw [← Matrix.det_transpose, ← LinearMap.det_toLin b, ← LinearMap.isUnit_iff_isUnit_det]
  exact (End.isUnit_iff _).mpr hbij

lemma IsJordanSplitting.exists_sub_mem_sup (h : B.IsJordanSplitting (p : ℤ_[p]) N) {x : M}
    (hx : ∀ y, (p : ℤ_[p]) ^ j ∣ B x y) :
    ∃ a ∈ N j, x - a ∈ (⨆ i ∈ Set.Ici (j + 1), N i) ⊔ Ideal.span {(p : ℤ_[p])} • ⊤ := by
  rcases Submodule.mem_sup.mp <| h.mem_biSup_sup_smul_top
    (mem_nonZeroDivisors_of_ne_zero PadicInt.irreducible_p.ne_zero) hx with ⟨s, hs, t, ht, rfl⟩
  have hIci : Set.Ici j = insert j (Set.Ici (j + 1)) := by
    ext i
    simp only [Set.mem_Ici, Set.mem_insert_iff]
    omega
  rw [hIci, iSup_insert] at hs
  rcases Submodule.mem_sup.mp hs with ⟨a, ha, s', hs', rfl⟩
  exact ⟨a, ha, by rw [add_assoc, add_sub_cancel_left]; exact Submodule.add_mem_sup hs' ht⟩

lemma IsJordanSplitting.pow_succ_dvd_apply (h : B.IsJordanSplitting (p : ℤ_[p]) N) (hB : B.IsSymm)
    {d z : M} (hd : d ∈ (⨆ i ∈ Set.Ici (j + 1), N i) ⊔ Ideal.span {(p : ℤ_[p])} • ⊤)
    (hz : ∀ y, (p : ℤ_[p]) ^ j ∣ B z y) : (p : ℤ_[p]) ^ (j + 1) ∣ B d z := by
  rcases Submodule.mem_sup.mp hd with ⟨s, hs, t, ht, rfl⟩
  rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at ht
  rcases ht with ⟨m, -, rfl⟩
  rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hB.eq m z]
  exact dvd_add (h.pow_dvd_apply_of_mem_biSup hs z) (pow_succ' (p : ℤ_[p]) j ▸
    mul_dvd_mul_left _ (hz m))

lemma IsJordanSplitting.pow_succ_dvd_sub (h : B.IsJordanSplitting (p : ℤ_[p]) N) (hB : B.IsSymm)
    {x y a c : M} (hxa : x - a ∈ (⨆ i ∈ Set.Ici (j + 1), N i) ⊔ Ideal.span {(p : ℤ_[p])} • ⊤)
    (hyc : y - c ∈ (⨆ i ∈ Set.Ici (j + 1), N i) ⊔ Ideal.span {(p : ℤ_[p])} • ⊤)
    (hy : ∀ z, (p : ℤ_[p]) ^ j ∣ B y z) (ha : ∀ z, (p : ℤ_[p]) ^ j ∣ B a z) :
    (p : ℤ_[p]) ^ (j + 1) ∣ B x y - B a c := by
  have hsub : B x y - B a c = B (x - a) y + B (y - c) a := by
    rw [map_sub, map_sub, LinearMap.sub_apply, LinearMap.sub_apply, hB.eq y a, hB.eq c a]
    ring1
  rw [hsub]
  exact dvd_add (h.pow_succ_dvd_apply hB hxa hy) (h.pow_succ_dvd_apply hB hyc ha)

variable (j) in
/-- The **unit form** of the constituent `N j` of a Jordan splitting `N` of a bilinear form `B` over
`ℤ_p`: the perfect pairing `C` on `N j` with `p ^ j • C = B|N j`, unique since `p` is a
non-zero-divisor. -/
noncomputable def IsJordanSplitting.unitForm (h : B.IsJordanSplitting (p : ℤ_[p]) N) :
    BilinForm ℤ_[p] (N j) :=
  (h.isModular j).choose

variable (j) in
lemma IsJordanSplitting.pow_smul_unitForm (h : B.IsJordanSplitting (p : ℤ_[p]) N) :
    (p : ℤ_[p]) ^ j • h.unitForm j = B.restrict (N j) :=
  (h.isModular j).choose_spec.1

variable (j) in
lemma IsJordanSplitting.isPerfPair_unitForm (h : B.IsJordanSplitting (p : ℤ_[p]) N) :
    (h.unitForm j).IsPerfPair :=
  (h.isModular j).choose_spec.2

lemma IsJordanSplitting.isSymm_unitForm (h : B.IsJordanSplitting (p : ℤ_[p]) N) (hB : B.IsSymm) :
    (h.unitForm j).IsSymm :=
  ⟨fun x y ↦ mul_left_cancel₀ (pow_ne_zero j PadicInt.irreducible_p.ne_zero) <| by
    have hxy : ((p : ℤ_[p]) ^ j • h.unitForm j) x y = ((p : ℤ_[p]) ^ j • h.unitForm j) y x := by
      rw [h.pow_smul_unitForm]
      exact hB.eq x y
    simpa using hxy⟩

lemma IsJordanSplitting.apply_basis (h : B.IsJordanSplitting (p : ℤ_[p]) N)
    (b : Basis ι ℤ_[p] (N j)) (a c : ι) :
    B (b a) (b c) = (p : ℤ_[p]) ^ j * toMatrix₂ b b (h.unitForm j) a c := by
  rw [LinearMap.toMatrix₂_apply, ← smul_eq_mul, ← LinearMap.smul_apply, ← LinearMap.smul_apply,
    h.pow_smul_unitForm]
  rfl

lemma IsJordanSplitting.exists_map_toZMod_eq (h : B.IsJordanSplitting (p : ℤ_[p]) N)
    (h' : B'.IsJordanSplitting (p : ℤ_[p]) N') (hB : B.IsSymm) (e : B'.IsometryEquiv B)
    (b : Basis ι ℤ_[p] (N j)) (b' : Basis ι ℤ_[p] (N' j)) : ∃ P : Matrix ι ι ℤ_[p],
    (toMatrix₂ b' b' (h'.unitForm j)).map PadicInt.toZMod =
      (P.transpose * toMatrix₂ b b (h.unitForm j) * P).map PadicInt.toZMod := by
  have hx (a : ι) (y : M) : (p : ℤ_[p]) ^ j ∣ B (e (b' a)) y := by
    rw [← e.toLinearEquiv.apply_symm_apply y, e.coe_toLinearEquiv, e.map_app]
    exact h'.pow_dvd_apply (b' a).2 _
  choose w hwN hwD using fun a ↦ h.exists_sub_mem_sup (hx a)
  let l : N' j →ₗ[ℤ_[p]] N j := b'.constr ℤ_[p] fun a ↦ ⟨w a, hwN a⟩
  have hl (a : ι) : l (b' a) = ⟨w a, hwN a⟩ := b'.constr_basis ℤ_[p] _ a
  refine ⟨LinearMap.toMatrix b' b l, Matrix.ext fun a c ↦ ?_⟩
  have hG : toMatrix₂ b' b' ((B.restrict (N j)).compl₁₂ l l) a c =
      ((LinearMap.toMatrix b' b l).transpose * toMatrix₂ b b (B.restrict (N j)) *
        LinearMap.toMatrix b' b l) a c := by
    rw [LinearMap.toMatrix₂_compl₁₂ b b]
  rw [← h.pow_smul_unitForm, map_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply,
    smul_eq_mul, LinearMap.toMatrix₂_apply, compl₁₂_apply, hl, hl, h.pow_smul_unitForm] at hG
  rw [Matrix.map_apply, Matrix.map_apply]
  refine PadicInt.toZMod_eq_of_pow_succ_dvd (j := j) ?_
  rw [← hG, ← h'.apply_basis b' a c, ← e.map_app]
  exact h.pow_succ_dvd_sub hB (hwD a) (hwD c) (hx c) (h.pow_dvd_apply (hwN a))

variable [Module.Finite ℤ_[p] M'] in
lemma IsJordanSplitting.quadraticChar_det_eq (h : B.IsJordanSplitting (p : ℤ_[p]) N)
    (h' : B'.IsJordanSplitting (p : ℤ_[p]) N') (hB : B.IsSymm) (hB' : B'.IsSymm)
    (e : B.IsometryEquiv B') (b : Basis ι ℤ_[p] (N j)) (b' : Basis κ ℤ_[p] (N' j)) :
    quadraticChar (ZMod p) (PadicInt.toZMod (toMatrix₂ b b (h.unitForm j)).det) =
      quadraticChar (ZMod p) (PadicInt.toZMod (toMatrix₂ b' b' (h'.unitForm j)).det) := by
  have hcard : Fintype.card κ = Fintype.card ι := by
    rw [← finrank_eq_card_basis b, ← finrank_eq_card_basis b', h.finrank_eq_of_equivalent h' ⟨e⟩
      PadicInt.irreducible_p.ne_zero PadicInt.irreducible_p.not_isUnit j]
  rcases h.exists_map_toZMod_eq h' hB e.symm b (b'.reindex (Fintype.equivOfCardEq hcard)) with
    ⟨P, hP⟩
  rcases h'.exists_map_toZMod_eq h hB' e (b'.reindex (Fintype.equivOfCardEq hcard)) b with ⟨Q, hQ⟩
  rw [← det_toMatrix₂_reindex b' (Fintype.equivOfCardEq hcard)]
  exact (PadicInt.quadraticChar_toZMod_det_eq hP hQ).symm

lemma IsJordanSplitting.forall_mem_pow_succ_dvd_iff (h : B.IsJordanSplitting (p : ℤ_[p]) N)
    (hB : B.IsSymm) : (∀ x ∈ N j, (p : ℤ_[p]) ^ (j + 1) ∣ B x x) ↔
      ∀ x, (∀ y, (p : ℤ_[p]) ^ j ∣ B x y) → (p : ℤ_[p]) ^ (j + 1) ∣ B x x := by
  refine ⟨fun hN x hx ↦ ?_, fun H x hx ↦ H x (h.pow_dvd_apply hx)⟩
  rcases h.exists_sub_mem_sup hx with ⟨a, ha, hxa⟩
  rw [← sub_add_cancel (B x x) (B a a)]
  exact dvd_add (h.pow_succ_dvd_sub hB hxa hxa hx (h.pow_dvd_apply ha)) (hN a ha)

lemma IsometryEquiv.forall_pow_succ_dvd_imp (e : B.IsometryEquiv B')
    (H : ∀ x, (∀ y, (p : ℤ_[p]) ^ j ∣ B x y) → (p : ℤ_[p]) ^ (j + 1) ∣ B x x) (x : M')
    (hx : ∀ y, (p : ℤ_[p]) ^ j ∣ B' x y) : (p : ℤ_[p]) ^ (j + 1) ∣ B' x x := by
  rw [← e.toLinearEquiv.apply_symm_apply x, e.coe_toLinearEquiv, e.map_app]
  refine H _ fun y ↦ ?_
  rw [← e.map_app, ← e.coe_toLinearEquiv, e.toLinearEquiv.apply_symm_apply]
  exact hx _

variable [Module.Free ℤ_[p] M] [Module.Finite ℤ_[p] M]

variable (j) in
/-- The **sign** `ε_q` (LMFDB `lattice.conway_genus_symbol`) of the constituent `N j`, of scale
`q = p ^ j`, of a Jordan splitting `N` of a bilinear form `B` over `ℤ_p`: the quadratic character
of `ZMod p` (the Legendre symbol) of the reduction modulo `p` of the determinant of the unit form
`C`, `B|N j = p ^ j • C`, in a basis of `N j`. It is `±1` (`sign_eq_one_or_eq_neg_one`), it does
not depend on the basis (`sign_eq_quadraticChar`) and, for a symmetric form, it does not depend on
the Jordan splitting either, being an isometry invariant (`sign_eq_of_equivalent`). This is the sign
`ε_q = (det f_q / p)` of Conway and Sloane at an odd prime `p`. At `p = 2` the quadratic character
of `ZMod 2` is trivial, so that the sign is `1`: there Conway and Sloane use the Jacobi symbol
`(2 | det f_q)` instead, which depends on the splitting (sign walking). -/
noncomputable def IsJordanSplitting.sign (h : B.IsJordanSplitting (p : ℤ_[p]) N) : ℤ :=
  quadraticChar (ZMod p) (PadicInt.toZMod
    (toMatrix₂ (finBasis ℤ_[p] (N j)) (finBasis ℤ_[p] (N j)) (h.unitForm j)).det)

/-- **The sign of a Jordan constituent can be computed in any basis.** -/
lemma IsJordanSplitting.sign_eq_quadraticChar (h : B.IsJordanSplitting (p : ℤ_[p]) N)
    (hB : B.IsSymm) (b : Basis ι ℤ_[p] (N j)) :
    h.sign j = quadraticChar (ZMod p) (PadicInt.toZMod (toMatrix₂ b b (h.unitForm j)).det) :=
  h.quadraticChar_det_eq h hB hB (.refl B) _ b

/-- **The sign of a Jordan constituent is `±1`**, the determinant of its unit form being a unit. -/
lemma IsJordanSplitting.sign_eq_one_or_eq_neg_one (h : B.IsJordanSplitting (p : ℤ_[p]) N) :
    h.sign j = 1 ∨ h.sign j = -1 :=
  quadraticChar_dichotomy ((isUnit_det_toMatrix₂_of_isPerfPair _
    (h.isPerfPair_unitForm j)).map PadicInt.toZMod).ne_zero

variable [Module.Free ℤ_[p] M'] [Module.Finite ℤ_[p] M'] in
/-- **The signs of the Jordan constituents are isometry invariants.** If two symmetric bilinear
forms over `ℤ_p` are isometric, then Jordan splittings of them have constituents of equal sign at
every scale. Taking the same form twice shows that the signs do not depend on the splitting. -/
lemma IsJordanSplitting.sign_eq_of_equivalent (h : B.IsJordanSplitting (p : ℤ_[p]) N)
    (h' : B'.IsJordanSplitting (p : ℤ_[p]) N') (hB : B.IsSymm) (hB' : B'.IsSymm)
    (hBB' : B.Equivalent B') : h.sign j = h'.sign j := by
  rcases hBB' with ⟨e⟩
  exact h.quadraticChar_det_eq h' hB hB' e _ _

end LinearMap.BilinForm

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {L : IntegralLattice V} {M : IntegralLattice W} [L.IsNondegenerate] [M.IsNondegenerate] (p : ℕ)
  [Fact p.Prime] (k : ℕ)

variable (L) in
/-- The **sign** `ε_q` (LMFDB `lattice.conway_genus_symbol`) of the `q`-modular constituent `q f_q`
of the `p`-adic Jordan decompositions of a nondegenerate integral lattice `L`, `q = p ^ k`, for an
odd prime `p`: the Legendre symbol of the determinant of the unimodular form `f_q`, `1` for a zero
constituent. It is `±1` (`jordanSign_eq_one_or_eq_neg_one`), it can be read off any Jordan
splitting (`jordanSign_eq`) and it is a genus invariant (`SameGenus.jordanSign_eq`). At `p = 2` it
is `1`, which is not Conway and Sloane's dyadic sign. -/
noncomputable def jordanSign : ℤ :=
  (L.exists_isJordanSplitting_localIntegralForm p L.form_nondegenerate).choose_spec.sign k

/-- **The sign `ε_q` can be read off any Jordan splitting.** -/
lemma jordanSign_eq {N : ℕ → Submodule ℤ_[p] (L.LocalCarrier p)}
    (hN : (L.localIntegralForm p).IsJordanSplitting (p : ℤ_[p]) N) : L.jordanSign p k = hN.sign k :=
  (L.exists_isJordanSplitting_localIntegralForm p
    L.form_nondegenerate).choose_spec.sign_eq_of_equivalent hN (L.isSymm_localIntegralForm p)
    (L.isSymm_localIntegralForm p) (.refl _)

/-- **The sign `ε_q` is `±1`.** -/
lemma jordanSign_eq_one_or_eq_neg_one : L.jordanSign p k = 1 ∨ L.jordanSign p k = -1 :=
  (L.exists_isJordanSplitting_localIntegralForm p
    L.form_nondegenerate).choose_spec.sign_eq_one_or_eq_neg_one

/-- **The signs `ε_q` are genus invariants.** -/
lemma SameGenus.jordanSign_eq (h : L.SameGenus M) : L.jordanSign p k = M.jordanSign p k :=
  (L.exists_isJordanSplitting_localIntegralForm p
    L.form_nondegenerate).choose_spec.sign_eq_of_equivalent
    (M.exists_isJordanSplitting_localIntegralForm p M.form_nondegenerate).choose_spec
    (L.isSymm_localIntegralForm p) (M.isSymm_localIntegralForm p) (h.localIntegralForm_equivalent p)

open scoped Classical in
variable (L) in
/-- The **type** `I` or `II` (LMFDB `lattice.conway_genus_symbol`) of the `q`-modular constituent
`q f_q` of the dyadic Jordan decompositions of a nondegenerate integral lattice `L`, `q = 2 ^ k`:
`II` when the unimodular form `f_q` is even, i.e. `2 q` divides the norm of every vector of the
constituent, and `I` when it is odd. A zero constituent has type `II`, as in Conway and Sloane. It
can be read off any Jordan splitting (`dyadicJordanType_eq`) and it is a genus invariant
(`SameGenus.dyadicJordanType_eq`). -/
noncomputable def dyadicJordanType : ConwayType :=
  if ∀ x ∈ (L.exists_isJordanSplitting_localIntegralForm 2 L.form_nondegenerate).choose k,
      ((2 : ℕ) : ℤ_[2]) ^ (k + 1) ∣ L.localIntegralForm 2 x x then .II else .I

open scoped Classical in
/-- **The dyadic types can be read off any Jordan splitting.** -/
lemma dyadicJordanType_eq {N : ℕ → Submodule ℤ_[2] (L.LocalCarrier 2)}
    (hN : (L.localIntegralForm 2).IsJordanSplitting ((2 : ℕ) : ℤ_[2]) N) : L.dyadicJordanType k =
    if ∀ x ∈ N k, ((2 : ℕ) : ℤ_[2]) ^ (k + 1) ∣ L.localIntegralForm 2 x x then .II else .I := by
  rw [dyadicJordanType, (L.exists_isJordanSplitting_localIntegralForm 2
    L.form_nondegenerate).choose_spec.forall_mem_pow_succ_dvd_iff (L.isSymm_localIntegralForm 2),
    hN.forall_mem_pow_succ_dvd_iff (L.isSymm_localIntegralForm 2)]

/-- **The dyadic types are genus invariants.** -/
lemma SameGenus.dyadicJordanType_eq (h : L.SameGenus M) :
    L.dyadicJordanType k = M.dyadicJordanType k := by
  classical
  rcases h.localIntegralForm_equivalent 2 with ⟨e⟩
  rw [dyadicJordanType, dyadicJordanType, (L.exists_isJordanSplitting_localIntegralForm 2
    L.form_nondegenerate).choose_spec.forall_mem_pow_succ_dvd_iff (L.isSymm_localIntegralForm 2),
    (M.exists_isJordanSplitting_localIntegralForm 2
    M.form_nondegenerate).choose_spec.forall_mem_pow_succ_dvd_iff (M.isSymm_localIntegralForm 2)]
  exact if_congr ⟨e.forall_pow_succ_dvd_imp, e.symm.forall_pow_succ_dvd_imp⟩ rfl rfl

/-- The part of the **Conway genus symbol** (LMFDB `lattice.conway_genus_symbol`) formalised in
LeanBridge: `ConwayGenusSymbolCore` (the type `I` or `II`, the signature `(r, s)` and the Jordan
ranks `n_q`) together with the signs `ε_q` of the Jordan constituents at the odd primes and the
types of the dyadic Jordan constituents. Missing are the oddities of the compartments and the signs
of the trains of Conway and Sloane's canonical `2`-adic symbol. -/
@[ext]
structure ConwayGenusSymbolSigned extends ConwayGenusSymbolCore where
  /-- The sign `ε_q` of the constituent of scale `q = p ^ k`, for an odd prime `p` (`1` at `2`). -/
  jordanSign : Nat.Primes → ℕ → ℤ
  /-- The type of the dyadic constituent of scale `2 ^ k`. -/
  dyadicType : ℕ → ConwayType

variable (L) in
/-- The type, signature, Jordan ranks, signs at the odd primes and dyadic types of a nondegenerate
integral lattice `L`: the part of its **Conway genus symbol** (LMFDB `lattice.conway_genus_symbol`)
formalised here. -/
noncomputable def conwayGenusSymbolSigned : ConwayGenusSymbolSigned where
  toConwayGenusSymbolCore := L.conwayGenusSymbolCore
  jordanSign q n :=
    haveI : Fact (q : ℕ).Prime := ⟨q.2⟩
    L.jordanSign q n
  dyadicType := L.dyadicJordanType

/-- **The type, signature, Jordan ranks, signs at the odd primes and dyadic types are genus
invariants.** -/
lemma SameGenus.conwayGenusSymbolSigned_eq (h : L.SameGenus M) :
    L.conwayGenusSymbolSigned = M.conwayGenusSymbolSigned := by
  rw [conwayGenusSymbolSigned, conwayGenusSymbolSigned, h.conwayGenusSymbolCore_eq,
    ConwayGenusSymbolSigned.mk.injEq]
  refine ⟨rfl, funext fun q ↦ funext fun n ↦ ?_, funext h.dyadicJordanType_eq⟩
  have : Fact (q : ℕ).Prime := ⟨q.2⟩
  exact h.jordanSign_eq q n

end TauCeti.IntegralLattice
