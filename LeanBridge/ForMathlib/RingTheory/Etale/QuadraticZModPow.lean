import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.CartanEtale
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.RingTheory.Smooth.Basic
import TauCeti.Algebra.QuadraticAlgebra.Etale

/-!
# Quadratic étale algebras over `ℤ/p^eℤ`

Let `p` be a prime, `e ≥ 1` and `R = ℤ/p^eℤ`. A free étale `R`-algebra `A` of rank `2` is
determined by its reduction `𝔽_p ⊗ A`, which is `𝔽_p × 𝔽_p` or `𝔽_{p²}`. Indeed `A` is formally
smooth, so an isomorphism between the reductions of two such algebras lifts along the nilpotent
ideal `(p)` to an algebra map; this map is surjective by Nakayama's lemma, `p` being nilpotent, and
bijective since both sides have `p^{2e}` elements. So there are two such algebras up to
isomorphism (LMFDB `gl2.cartan`): the split algebra `R × R`, and the non-split algebra
`NonsplitCartanAlgebraPow p e = R[ω]`, `ω² = a + b ω`, where `a` and `b` lift the coefficients of
the field `𝔽_{p²} = NonsplitCartanAlgebra p`, so that the discriminant `b² + 4 a` is a unit and
the algebra is étale. They are not isomorphic: `(1, 0)` is an idempotent of `R × R` other than `0`
and `1`, while the reduction of the non-split algebra is a field, and an idempotent reducing to `0`
lies in `p R[ω]`, hence is nilpotent, hence is `0`.

## Main definitions

* `AlgEquiv.piFinTwo`: the algebra isomorphism `(Π i : Fin 2, A i) ≃ A 0 × A 1`, which makes the
  split algebra `R × R` étale.
* `RingHom.toZModAlgHom`: a ring homomorphism between `ZMod n`-algebras, as a `ZMod n`-algebra
  homomorphism.
* `Matrix.GeneralLinearGroup.NonsplitCartanAlgebraPow p e` (LMFDB `gl2.cartan`): the non-split
  algebra over `ℤ/p^eℤ`.

## Main results

* `Algebra.FormallySmooth.nonempty_algEquiv_of_surjective`: a finite formally smooth algebra `A`
  with a surjection onto `C` is isomorphic to every algebra with at least as many elements and a
  surjection onto `C` whose kernel lies in `t M`, for a nilpotent scalar `t`.
* `Matrix.GeneralLinearGroup.nonempty_algEquiv_prod_of_surjective` and
  `Matrix.GeneralLinearGroup.nonempty_algEquiv_nonsplitCartanAlgebraPow_of_surjective`: an algebra
  over `ℤ/p^eℤ` with `p^{2e}` elements whose reduction modulo `p` is `𝔽_p × 𝔽_p`, respectively
  `𝔽_{p²}`, is the split, respectively the non-split, algebra.
* `Matrix.GeneralLinearGroup.nonempty_algEquiv_prod_or_nonempty_algEquiv_nonsplitCartanAlgebraPow`
  (LMFDB `gl2.cartan`): a free étale algebra of rank `2` over `ℤ/p^eℤ` is the split or the
  non-split algebra.
* `Matrix.GeneralLinearGroup.not_nonempty_algEquiv_prod_nonsplitCartanAlgebraPow` (LMFDB
  `gl2.cartan`): the split and the non-split algebras are not isomorphic.
-/

open Module TensorProduct

namespace Algebra.FormallySmooth

variable {R A M C : Type*} [CommRing R] [CommRing A] [CommRing M] [CommRing C] [Algebra R A]
  [Algebra R M] [Algebra R C]

/-- **Lifting isomorphisms along a nilpotent thickening.** Let `A` be a finite formally smooth
`R`-algebra with a surjection `f : A → C`, and `M` an `R`-algebra with at least as many elements
and a surjection `g : M → C` whose kernel lies in `t M` for a nilpotent `t ∈ R`. Then `A ≅ M`: `f`
lifts to `φ : A → M` with `g ∘ φ = f`, which is surjective by Nakayama's lemma for the nilpotent
`t`, hence bijective. -/
lemma nonempty_algEquiv_of_surjective [FormallySmooth R A] [Finite A] {t : R} (ht : IsNilpotent t)
    {f : A →ₐ[R] C} (hf : Function.Surjective f) {g : M →ₐ[R] C} (hg : Function.Surjective g)
    (hker : ∀ m, g m = 0 → ∃ m', m = t • m') (hcard : Nat.card A ≤ Nat.card M) :
    Nonempty (A ≃ₐ[R] M) := by
  rcases ht with ⟨n, hn⟩
  have hle : RingHom.ker (g : M →+* C) ≤ Ideal.span {algebraMap R M t} := fun m hm ↦ by
    rcases hker m (RingHom.mem_ker.mp hm) with ⟨m', rfl⟩
    exact Ideal.mem_span_singleton'.mpr ⟨m', by rw [Algebra.smul_def, mul_comm]⟩
  have hnil : IsNilpotent (RingHom.ker (g : M →+* C)) := by
    refine ⟨n, le_bot_iff.mp ((Ideal.pow_right_mono hle n).trans ?_)⟩
    rw [Ideal.span_singleton_pow, ← map_pow, hn, map_zero, Ideal.span_singleton_eq_bot.mpr rfl]
  let φ : A →ₐ[R] M := liftOfSurjective f g hg hnil
  have hφ (a : A) : g (φ a) = f a := liftOfSurjective_apply f g hg hnil a
  have hstep (m : M) : ∃ a m', m = φ a + t • m' := by
    rcases hf (g m) with ⟨a, ha⟩
    rcases hker (m - φ a) (by rw [map_sub, hφ, ha, sub_self]) with ⟨m', hm'⟩
    exact ⟨a, m', by rw [← hm', add_sub_cancel]⟩
  have hpow (k : ℕ) (m : M) : ∃ a m', m = φ a + t ^ k • m' := by
    induction k generalizing m with
    | zero => exact ⟨0, m, by rw [map_zero, pow_zero, one_smul, zero_add]⟩
    | succ k ih =>
      rcases ih m with ⟨a, m', rfl⟩
      rcases hstep m' with ⟨a', m'', rfl⟩
      exact ⟨a + t ^ k • a', m'', by
        rw [map_add, map_smul, smul_add, pow_succ, mul_smul, add_assoc]⟩
  have hsurj : Function.Surjective φ := fun m ↦ by
    rcases hpow n m with ⟨a, m', rfl⟩
    exact ⟨a, by rw [hn, zero_smul, add_zero]⟩
  exact ⟨AlgEquiv.ofBijective φ (hsurj.bijective_of_nat_card_le hcard)⟩

end Algebra.FormallySmooth

namespace AlgEquiv

variable (R : Type*) [CommSemiring R] (A : Fin 2 → Type*) [∀ i, Semiring (A i)]
  [∀ i, Algebra R (A i)]

/-- The algebra isomorphism `(Π i : Fin 2, A i) ≃ A 0 × A 1`. -/
def piFinTwo : (∀ i, A i) ≃ₐ[R] A 0 × A 1 :=
  ofLinearEquiv (LinearEquiv.piFinTwo R A) rfl fun _ _ ↦ rfl

end AlgEquiv

namespace RingHom

variable (n : ℕ) {A B : Type*} [Semiring A] [Semiring B] [Algebra (ZMod n) A] [Algebra (ZMod n) B]

/-- A ring homomorphism between `ZMod n`-algebras, as a `ZMod n`-algebra homomorphism: a ring has
at most one `ZMod n`-algebra structure. -/
def toZModAlgHom (f : A →+* B) : A →ₐ[ZMod n] B where
  __ := f
  commutes' r :=
    RingHom.congr_fun (Subsingleton.elim (f.comp (algebraMap (ZMod n) A)) (algebraMap _ B)) r

@[simp]
lemma coe_toZModAlgHom (f : A →+* B) : ⇑(f.toZModAlgHom n) = f :=
  rfl

end RingHom

namespace ZMod

lemma isUnit_iff_castHom_ne_zero {p e : ℕ} [Fact p.Prime] (he : e ≠ 0) {x : ZMod (p ^ e)} :
    IsUnit x ↔ castHom (dvd_pow_self p he) (ZMod p) x ≠ 0 := by
  rw [castHom_apply, ← natCast_zmod_val x,
    isUnit_natCast_iff_not_dvd_pow Fact.out (Nat.pos_of_ne_zero he),
    cast_natCast (dvd_pow_self p he), Ne, natCast_eq_zero_iff]

end ZMod

namespace Matrix.GeneralLinearGroup

instance {R : Type*} [CommRing R] : Algebra.Etale R (R × R) :=
  .of_equiv (AlgEquiv.piFinTwo R fun _ ↦ R)

variable {p e : ℕ}

lemma natCard_eq_of_basis {A : Type*} [AddCommGroup A] [Module (ZMod (p ^ e)) A]
    (b : Basis (Fin 2) (ZMod (p ^ e)) A) : Nat.card A = p ^ (2 * e) := by
  rw [Nat.card_congr b.equivFun.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
    Fintype.card_fin, ← pow_mul, mul_comm]

lemma eq_zero_or_eq_one_of_isIdempotentElem {R M C : Type*} [CommRing R] [CommRing M] [Algebra R M]
    [CommRing C] [IsDomain C] {t : R} (ht : IsNilpotent t) (g : M →+* C)
    (hker : ∀ m, g m = 0 → ∃ m', m = t • m') {x : M} (hx : IsIdempotentElem x) : x = 0 ∨ x = 1 := by
  have key {y : M} (hy : IsIdempotentElem y) (hgy : g y = 0) : y = 0 := by
    rcases ht with ⟨n, hn⟩
    rcases hker y hgy with ⟨m', rfl⟩
    rw [← hy.pow_succ_eq n, smul_pow, pow_succ, hn, zero_mul, zero_smul]
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp (hx.map g) with h | h
  · exact .inl (key hx h)
  · exact .inr (sub_eq_zero.mp (key hx.one_sub (by rw [map_sub, map_one, h, sub_self]))).symm

variable [Fact p.Prime]

variable (p e) in
/-- The **non-split algebra** over `ℤ/p^eℤ` (LMFDB `gl2.cartan`): the quadratic algebra
`(ℤ/p^eℤ)[ω]`, `ω² = a + b ω`, where `a` and `b` lift the coefficients of the field
`NonsplitCartanAlgebra p = 𝔽_{p²}`: `ω² = ε` for odd `p`, `ε` the least primitive root modulo `p`,
and `ω² = 1 + ω` for `p = 2`. Every free étale algebra of rank `2` over `ℤ/p^eℤ` whose reduction
modulo `p` is a field is isomorphic to it. -/
abbrev NonsplitCartanAlgebraPow : Type :=
  QuadraticAlgebra (ZMod (p ^ e)) ((nonsplitCartanA p).val : ZMod (p ^ e))
    ((nonsplitCartanB p).val : ZMod (p ^ e))

lemma discr_nonsplitCartanA_ne_zero :
    QuadraticAlgebra.discr (nonsplitCartanA p) (nonsplitCartanB p) ≠ 0 := by
  rw [QuadraticAlgebra.discr_def]
  by_cases hp : p = 2
  · subst hp
    simp only [nonsplitCartanA, nonsplitCartanB, ite_true]
    rw [show (1 : ZMod 2) ^ 2 + 4 * 1 = ((5 : ℕ) : ZMod 2) by norm_num, Ne,
      ZMod.natCast_eq_zero_iff]
    decide
  · have h4 : (2 * 2 : ZMod p) ≠ 0 := mul_ne_zero (two_ne_zero_of_ne_two p hp)
      (two_ne_zero_of_ne_two p hp)
    norm_num at h4
    rw [nonsplitCartanA_of_ne_two p hp, nonsplitCartanB_of_ne_two p hp]
    simp [h4, ZMod.leastPrimitiveRoot_ne_zero p]

lemma isUnit_discr_nonsplitCartanAlgebraPow : IsUnit (QuadraticAlgebra.discr
    ((nonsplitCartanA p).val : ZMod (p ^ e)) ((nonsplitCartanB p).val : ZMod (p ^ e))) := by
  rcases eq_or_ne e 0 with rfl | he
  · have : Subsingleton (ZMod (p ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero p)
    exact isUnit_of_subsingleton _
  · rw [ZMod.isUnit_iff_castHom_ne_zero he]
    simpa only [QuadraticAlgebra.discr_def, map_add, map_pow, map_mul, map_ofNat, map_natCast,
      ZMod.natCast_zmod_val] using discr_nonsplitCartanA_ne_zero

instance : Algebra.Etale (ZMod (p ^ e)) (NonsplitCartanAlgebraPow p e) :=
  QuadraticAlgebra.etale_of_isUnit_discr isUnit_discr_nonsplitCartanAlgebraPow

instance : Finite (NonsplitCartanAlgebraPow p e) :=
  Module.finite_of_finite (ZMod (p ^ e))

section Reduction

variable [Algebra (ZMod (p ^ e)) (ZMod p)]

lemma exists_eq_natCast_mul_of_algebraMap_eq_zero {x : ZMod (p ^ e)}
    (hx : algebraMap (ZMod (p ^ e)) (ZMod p) x = 0) : ∃ y, x = p * y := by
  rw [← ZMod.natCast_zmod_val x, map_natCast, ZMod.natCast_eq_zero_iff] at hx
  rcases hx with ⟨k, hk⟩
  exact ⟨k, by rw [← ZMod.natCast_zmod_val x, hk, Nat.cast_mul]⟩

lemma exists_eq_smul_of_one_tmul_eq_zero {B ι : Type*} [CommRing B] [Algebra (ZMod (p ^ e)) B]
    [Fintype ι] (b : Basis ι (ZMod (p ^ e)) B) {x : B} (hx : (1 : ZMod p) ⊗ₜ[ZMod (p ^ e)] x = 0) :
    ∃ y, x = (p : ZMod (p ^ e)) • y := by
  have h (i : ι) : ∃ d, b.repr x i = p * d := by
    refine exists_eq_natCast_mul_of_algebraMap_eq_zero ?_
    have hi : (Algebra.TensorProduct.basis (ZMod p) b).repr ((1 : ZMod p) ⊗ₜ x) i = 0 := by
      rw [hx, map_zero, Finsupp.coe_zero, Pi.zero_apply]
    rwa [Algebra.TensorProduct.basis_repr_tmul, one_smul, Finsupp.mapRange_apply] at hi
  choose d hd using h
  refine ⟨∑ i, d i • b i, ?_⟩
  conv_lhs => rw [← b.sum_repr x]
  simp only [hd, mul_smul, Finset.smul_sum]

lemma exists_eq_smul_of_baseChange_eq_zero {a b : ZMod (p ^ e)}
    {x : QuadraticAlgebra (ZMod (p ^ e)) a b}
    (hx : QuadraticAlgebra.baseChange (ZMod p) a b x = 0) : ∃ y, x = (p : ZMod (p ^ e)) • y := by
  rcases exists_eq_natCast_mul_of_algebraMap_eq_zero (congrArg QuadraticAlgebra.re hx) with
    ⟨y₁, h₁⟩
  rcases exists_eq_natCast_mul_of_algebraMap_eq_zero (congrArg QuadraticAlgebra.im hx) with
    ⟨y₂, h₂⟩
  exact ⟨⟨y₁, y₂⟩, QuadraticAlgebra.ext h₁ h₂⟩

instance : Fact (∀ r : ZMod p, r ^ 2 ≠ algebraMap (ZMod (p ^ e)) (ZMod p) (nonsplitCartanA p).val +
    algebraMap (ZMod (p ^ e)) (ZMod p) (nonsplitCartanB p).val * r) :=
  ⟨by simpa only [map_natCast, ZMod.natCast_zmod_val] using sq_ne_nonsplitCartanA_add p⟩

variable {M C : Type*} [CommRing M] [Algebra (ZMod (p ^ e)) M] [CommRing C]
  [Algebra (ZMod (p ^ e)) C]

open Algebra in
/-- **Recognising the split algebra over `ℤ/p^eℤ`**: an algebra `M` over `ℤ/p^eℤ` with at least
`p^{2e}` elements and a surjection onto `C ≅ 𝔽_p × 𝔽_p` with kernel in `p M` is isomorphic to
`ℤ/p^eℤ × ℤ/p^eℤ`. -/
lemma nonempty_algEquiv_prod_of_surjective (hM : p ^ (2 * e) ≤ Nat.card M)
    {g : M →ₐ[ZMod (p ^ e)] C} (hg : Function.Surjective g)
    (hker : ∀ m, g m = 0 → ∃ m', m = (p : ZMod (p ^ e)) • m') (eC : C ≃+* ZMod p × ZMod p) :
    Nonempty ((ZMod (p ^ e) × ZMod (p ^ e)) ≃ₐ[ZMod (p ^ e)] M) := by
  have hf : Function.Surjective
      ((Algebra.ofId (ZMod (p ^ e)) (ZMod p)).prodMap (Algebra.ofId _ (ZMod p))) :=
    (ZMod.ringHom_surjective (algebraMap (ZMod (p ^ e)) (ZMod p))).prodMap
      (ZMod.ringHom_surjective (algebraMap (ZMod (p ^ e)) (ZMod p)))
  refine FormallySmooth.nonempty_algEquiv_of_surjective
    ⟨e, by rw [← Nat.cast_pow, ZMod.natCast_self]⟩
    (f := (eC.symm.toRingHom.toZModAlgHom _).comp
      ((Algebra.ofId (ZMod (p ^ e)) (ZMod p)).prodMap (Algebra.ofId _ (ZMod p))))
    (eC.symm.surjective.comp hf) hg hker ?_
  rwa [Nat.card_prod, Nat.card_zmod, ← sq, ← pow_mul, mul_comm]

open Algebra in
/-- **Recognising the non-split algebra over `ℤ/p^eℤ`**: an algebra `M` over `ℤ/p^eℤ` with at
least `p^{2e}` elements and a surjection onto `C ≅ 𝔽_{p²}` with kernel in `p M` is isomorphic to
`NonsplitCartanAlgebraPow p e`. -/
lemma nonempty_algEquiv_nonsplitCartanAlgebraPow_of_surjective (hM : p ^ (2 * e) ≤ Nat.card M)
    {g : M →ₐ[ZMod (p ^ e)] C} (hg : Function.Surjective g)
    (hker : ∀ m, g m = 0 → ∃ m', m = (p : ZMod (p ^ e)) • m') (eC : C ≃+* GaloisField p 2) :
    Nonempty (NonsplitCartanAlgebraPow p e ≃ₐ[ZMod (p ^ e)] M) := by
  have hcard : Nat.card (QuadraticAlgebra (ZMod p)
      (algebraMap (ZMod (p ^ e)) (ZMod p) (nonsplitCartanA p).val)
      (algebraMap (ZMod (p ^ e)) (ZMod p) (nonsplitCartanB p).val)) = p ^ 2 := by
    rw [Nat.card_congr (QuadraticAlgebra.equivProd _ _), Nat.card_prod, Nat.card_zmod, sq]
  have hf : Function.Surjective (QuadraticAlgebra.baseChange (ZMod p)
      ((nonsplitCartanA p).val : ZMod (p ^ e)) ((nonsplitCartanB p).val : ZMod (p ^ e))) :=
    QuadraticAlgebra.mapRingHom_surjective _ _ _ (ZMod.ringHom_surjective _)
  refine FormallySmooth.nonempty_algEquiv_of_surjective
    ⟨e, by rw [← Nat.cast_pow, ZMod.natCast_self]⟩
    (f := ((eC.symm.toRingHom.comp
      (GaloisField.algEquivGaloisField p 2 hcard).toRingEquiv.toRingHom).toZModAlgHom _).comp
      (QuadraticAlgebra.baseChange (ZMod p) _ _))
    ((eC.symm.surjective.comp (GaloisField.algEquivGaloisField p 2 hcard).surjective).comp hf)
    hg hker ?_
  rwa [Nat.card_congr (QuadraticAlgebra.equivProd _ _), Nat.card_prod, Nat.card_zmod, ← sq,
    ← pow_mul, mul_comm]

end Reduction

variable [NeZero e]

/-- **The two quadratic étale algebras over `ℤ/p^eℤ`** (LMFDB `gl2.cartan`): a free étale algebra
`A` of rank `2` over `ℤ/p^eℤ` is isomorphic to the split algebra `ℤ/p^eℤ × ℤ/p^eℤ` or to the
non-split algebra `NonsplitCartanAlgebraPow p e`, according as its reduction `𝔽_p ⊗ A` is
`𝔽_p × 𝔽_p` or `𝔽_{p²}`. -/
lemma nonempty_algEquiv_prod_or_nonempty_algEquiv_nonsplitCartanAlgebraPow {A : Type} [CommRing A]
    [Algebra (ZMod (p ^ e)) A] [Algebra.Etale (ZMod (p ^ e)) A]
    (b : Basis (Fin 2) (ZMod (p ^ e)) A) :
    Nonempty (A ≃ₐ[ZMod (p ^ e)] ZMod (p ^ e) × ZMod (p ^ e)) ∨
      Nonempty (A ≃ₐ[ZMod (p ^ e)] NonsplitCartanAlgebraPow p e) := by
  let _ : Algebra (ZMod (p ^ e)) (ZMod p) := ZMod.algebra' (ZMod p) p (dvd_pow_self p (NeZero.ne e))
  have hA : p ^ (2 * e) ≤ Nat.card A := (natCard_eq_of_basis b).ge
  have hg : Function.Surjective
      (Algebra.TensorProduct.includeRight : A →ₐ[ZMod (p ^ e)] ZMod p ⊗[ZMod (p ^ e)] A) :=
    Algebra.TensorProduct.includeRight_surjective A (ZMod.ringHom_surjective _)
  have hker (x : A) (hx : Algebra.TensorProduct.includeRight x = (0 : ZMod p ⊗[ZMod (p ^ e)] A)) :
      ∃ y, x = (p : ZMod (p ^ e)) • y :=
    exists_eq_smul_of_one_tmul_eq_zero b hx
  rcases nonempty_algEquiv_prod_or_nonempty_algEquiv_galoisField
    (Algebra.TensorProduct.basis (ZMod p) b) with ⟨⟨eA⟩⟩ | ⟨⟨eA⟩⟩
  · exact .inl ((nonempty_algEquiv_prod_of_surjective hA hg hker eA.toRingEquiv).map .symm)
  · exact .inr <| (nonempty_algEquiv_nonsplitCartanAlgebraPow_of_surjective hA hg hker
      eA.toRingEquiv).map .symm

/-- **The split and the non-split algebras over `ℤ/p^eℤ` are not isomorphic** (LMFDB
`gl2.cartan`): `(1, 0)` is an idempotent of `ℤ/p^eℤ × ℤ/p^eℤ` other than `0` and `1`, while the
idempotents of `NonsplitCartanAlgebraPow p e` are `0` and `1`. -/
lemma not_nonempty_algEquiv_prod_nonsplitCartanAlgebraPow :
    ¬Nonempty ((ZMod (p ^ e) × ZMod (p ^ e)) ≃ₐ[ZMod (p ^ e)] NonsplitCartanAlgebraPow p e) := by
  rintro ⟨φ⟩
  let _ : Algebra (ZMod (p ^ e)) (ZMod p) := ZMod.algebra' (ZMod p) p (dvd_pow_self p (NeZero.ne e))
  have : Fact (1 < p ^ e) := ⟨Nat.one_lt_pow (NeZero.ne e) (Fact.out : p.Prime).one_lt⟩
  have h10 : IsIdempotentElem ((1, 0) : ZMod (p ^ e) × ZMod (p ^ e)) :=
    Prod.ext (mul_one 1) (mul_zero 0)
  have hφ : IsIdempotentElem (φ (1, 0)) := h10.map φ
  rcases eq_zero_or_eq_one_of_isIdempotentElem ⟨e, by rw [← Nat.cast_pow, ZMod.natCast_self]⟩
    (QuadraticAlgebra.baseChange (ZMod p) _ _).toRingHom
    (fun _ hm ↦ exists_eq_smul_of_baseChange_eq_zero hm) hφ with h | h
  · exact one_ne_zero (congrArg Prod.fst (φ.injective (h.trans (map_zero φ).symm)))
  · exact zero_ne_one (congrArg Prod.snd (φ.injective (h.trans (map_one φ).symm)))

end Matrix.GeneralLinearGroup
