import LeanBridge.ForMathlib.RingTheory.Etale.QuadraticZModPow
import Mathlib.Algebra.QuadraticAlgebra.BaseChange
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Quadratic étale algebras over `ℤ/Nℤ`

Let `N ≥ 1`. By the Chinese remainder theorem `ℤ/Nℤ ≅ ∏_{p ∣ N} ℤ/p^{v_p(N)}ℤ`, so an algebra `A`
over `ℤ/Nℤ` is the product of its components `ℤ/p^{v_p(N)}ℤ ⊗ A` at the primes `p ∣ N`. When `A`
is free étale of rank `2`, each component is the split or the non-split algebra over
`ℤ/p^{v_p(N)}ℤ`, and `A` is determined up to isomorphism by the set of primes where it is non-split.
Every set of primes dividing `N` occurs: the quadratic algebra `(ℤ/Nℤ)[ω]`, `ω² = a + b ω`, where
`(a, b)` is congruent modulo `p^{v_p(N)}` to the coefficients of the non-split algebra for `p` in
the set and to `(0, 1)` otherwise, is non-split exactly at the primes of the set; its discriminant
is a unit, and `ω² = ω` splits. So `A` can be split or non-split independently at each prime
dividing `N` (LMFDB `gl2.cartan`).

## Main definitions

* `Matrix.GeneralLinearGroup.IsSplitAt N p A` and `Matrix.GeneralLinearGroup.IsNonsplitAt N p A`
  (LMFDB `gl2.cartan`): the component of `A` at `p` is the split, respectively the non-split,
  algebra.
* `Matrix.GeneralLinearGroup.NonsplitAtAlgebra N S` (LMFDB `gl2.cartan`): a free étale algebra of
  rank `2` over `ℤ/Nℤ` that is non-split exactly at the primes of `S`.
* `Matrix.GeneralLinearGroup.zmodAlgEquivPi` and `Matrix.GeneralLinearGroup.algEquivPiTensor`: the
  Chinese remainder theorem for `ℤ/Nℤ` and for an algebra over it.

## Main results

* `Matrix.GeneralLinearGroup.isSplitAt_or_isNonsplitAt` and
  `Matrix.GeneralLinearGroup.not_isSplitAt_and_isNonsplitAt`: a free étale algebra of rank `2` over
  `ℤ/Nℤ` is split or non-split at each prime dividing `N`, and not both.
* `Matrix.GeneralLinearGroup.isNonsplitAt_iff_isField_quotient_span_natCast` (LMFDB `gl2.cartan`):
  it is non-split at `p` exactly when its reduction `A/pA` modulo `p` is a field.
* `Matrix.GeneralLinearGroup.isSplitAt_nonsplitAtAlgebra_iff` and
  `Matrix.GeneralLinearGroup.isNonsplitAt_nonsplitAtAlgebra_iff` (LMFDB `gl2.cartan`): every set of
  primes dividing `N` is the set of primes where some free étale algebra of rank `2` is non-split.
* `Matrix.GeneralLinearGroup.nonempty_algEquiv_iff_forall_isSplitAt_iff`: two free étale algebras
  of rank `2` over `ℤ/Nℤ` are isomorphic exactly when they are split at the same primes.
* `Matrix.GeneralLinearGroup.existsUnique_nonempty_algEquiv_nonsplitAtAlgebra` (LMFDB
  `gl2.cartan`): a free étale algebra of rank `2` over `ℤ/Nℤ` is isomorphic to
  `NonsplitAtAlgebra N S` for exactly one set `S` of primes dividing `N`.
-/

open Module TensorProduct

namespace Matrix.GeneralLinearGroup

variable {R : Type*} [CommRing R]

lemma nonempty_algEquiv_quadraticAlgebra_of_eq {a b a' b' : R} (ha : a = a') (hb : b = b') :
    Nonempty (QuadraticAlgebra R a b ≃ₐ[R] QuadraticAlgebra R a' b') := by
  subst ha hb
  exact ⟨AlgEquiv.refl⟩

variable (R) in
lemma nonempty_algEquiv_quadraticAlgebra_zero_one :
    Nonempty (QuadraticAlgebra R 0 1 ≃ₐ[R] R × R) := by
  have hu : ((0, 1) : R × R) * (0, 1) = (0 : R) • 1 + (1 : R) • (0, 1) := by
    ext <;> simp
  refine ⟨AlgEquiv.ofBijective (QuadraticAlgebra.lift ⟨(0, 1), hu⟩)
    ⟨fun z w h ↦ ?_, fun y ↦ ⟨⟨y.1, y.2 - y.1⟩, ?_⟩⟩⟩
  · have h₁ : z.re = w.re := by simpa using congrArg Prod.fst h
    have h₂ : z.re + z.im = w.re + w.im := by simpa using congrArg Prod.snd h
    exact QuadraticAlgebra.ext h₁ (add_left_cancel (h₁ ▸ h₂))
  · ext <;> simp

variable (N : ℕ)

/-- The reduction `ℤ/Nℤ → ℤ/p^{v_p(N)}ℤ`, as an algebra structure (a local instance in this
file). -/
abbrev zmodPrimePowAlgebra (p : ℕ) : Algebra (ZMod N) (ZMod (p ^ N.factorization p)) :=
  ZMod.algebra' _ (p ^ N.factorization p) (Nat.ordProj_dvd N p)

attribute [local instance] zmodPrimePowAlgebra

section Defs

variable (p : ℕ) (A : Type*) [CommRing A] [Algebra (ZMod N) A]

/-- A `ℤ/Nℤ`-algebra `A` is **split at `p`** (LMFDB `gl2.cartan`): its component
`ℤ/p^{v_p(N)}ℤ ⊗ A` at `p` is the split algebra `ℤ/p^{v_p(N)}ℤ × ℤ/p^{v_p(N)}ℤ`. -/
def IsSplitAt : Prop :=
  Nonempty (ZMod (p ^ N.factorization p) ⊗[ZMod N] A ≃ₐ[ZMod (p ^ N.factorization p)]
    ZMod (p ^ N.factorization p) × ZMod (p ^ N.factorization p))

/-- A `ℤ/Nℤ`-algebra `A` is **non-split at the prime `p`** (LMFDB `gl2.cartan`): its component
`ℤ/p^{v_p(N)}ℤ ⊗ A` at `p` is the non-split algebra `NonsplitCartanAlgebraPow p (v_p(N))`. -/
def IsNonsplitAt [Fact p.Prime] : Prop :=
  Nonempty (ZMod (p ^ N.factorization p) ⊗[ZMod N] A ≃ₐ[ZMod (p ^ N.factorization p)]
    NonsplitCartanAlgebraPow p (N.factorization p))

end Defs

variable {N} {p : ℕ} {A A' : Type} [CommRing A] [Algebra (ZMod N) A] [CommRing A']
  [Algebra (ZMod N) A']

lemma neZero_factorization (hp : p ∈ N.primeFactors) : NeZero (N.factorization p) :=
  ⟨Finsupp.mem_support_iff.mp ((Nat.support_factorization N).symm ▸ hp)⟩

variable [Fact p.Prime] [Algebra.Etale (ZMod N) A] in
/-- **A free étale algebra of rank `2` over `ℤ/Nℤ` is split or non-split at each prime dividing
`N`** (LMFDB `gl2.cartan`): its component at `p` is a free étale algebra of rank `2` over
`ℤ/p^{v_p(N)}ℤ`. -/
lemma isSplitAt_or_isNonsplitAt (b : Basis (Fin 2) (ZMod N) A) (hp : p ∈ N.primeFactors) :
    IsSplitAt N p A ∨ IsNonsplitAt N p A := by
  have : NeZero (N.factorization p) := neZero_factorization hp
  exact nonempty_algEquiv_prod_or_nonempty_algEquiv_nonsplitCartanAlgebraPow
    (Algebra.TensorProduct.basis _ b)

variable [Fact p.Prime] in
/-- **An algebra over `ℤ/Nℤ` is not both split and non-split at a prime dividing `N`.** -/
lemma not_isSplitAt_and_isNonsplitAt (hp : p ∈ N.primeFactors) :
    ¬(IsSplitAt N p A ∧ IsNonsplitAt N p A) := by
  rintro ⟨⟨e₁⟩, ⟨e₂⟩⟩
  have : NeZero (N.factorization p) := neZero_factorization hp
  exact not_nonempty_algEquiv_prod_nonsplitCartanAlgebraPow ⟨e₁.symm.trans e₂⟩

variable [Fact p.Prime] [Algebra.Etale (ZMod N) A] in
/-- **Non-split at `p` means that the reduction modulo `p` is a field** (LMFDB `gl2.cartan`): for a
free étale algebra `A` of rank `2` over `ℤ/Nℤ` and a prime `p ∣ N`, the component of `A` at `p` is
the non-split algebra exactly when `A/pA` is a field. The reduction `A → A/pA` factors through the
component, with kernel `p` times it, and the reduction of the non-split algebra is `𝔽_{p²}`, while
that of the split algebra `ℤ/p^{v_p(N)}ℤ × ℤ/p^{v_p(N)}ℤ` has zero divisors. -/
lemma isNonsplitAt_iff_isField_quotient_span_natCast (b : Basis (Fin 2) (ZMod N) A)
    (hp : p ∈ N.primeFactors) : IsNonsplitAt N p A ↔ IsField (A ⧸ Ideal.span {(p : A)}) := by
  have he : NeZero (N.factorization p) := neZero_factorization hp
  have hC : ((p : ℕ) : A ⧸ Ideal.span {(p : A)}) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  let _ : Algebra (ZMod (p ^ N.factorization p)) (A ⧸ Ideal.span {(p : A)}) :=
    ZMod.algebra' _ _ (ringChar.dvd (by rw [Nat.cast_pow, hC, zero_pow he.out]))
  let g : ZMod (p ^ N.factorization p) ⊗[ZMod N] A →ₐ[ZMod (p ^ N.factorization p)]
      A ⧸ Ideal.span {(p : A)} :=
    (Algebra.TensorProduct.lift ((algebraMap _ _).toZModAlgHom N)
      (Ideal.Quotient.mkₐ (ZMod N) _) fun _ _ ↦ .all _ _).toRingHom.toZModAlgHom _
  have hg : Function.Surjective g := fun c ↦ by
    rcases Ideal.Quotient.mk_surjective c with ⟨a, rfl⟩
    exact ⟨1 ⊗ₜ a, by simp [g]⟩
  have hker (m : ZMod (p ^ N.factorization p) ⊗[ZMod N] A) (hm : g m = 0) :
      ∃ m', m = (p : ZMod (p ^ N.factorization p)) • m' := by
    rcases Algebra.TensorProduct.includeRight_surjective A (ZMod.ringHom_surjective _) m with
      ⟨a, rfl⟩
    have ha : Ideal.Quotient.mk (Ideal.span {(p : A)}) a = 0 := by simpa [g] using hm
    rcases Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq_zero_iff_mem.mp ha) with ⟨c, rfl⟩
    exact ⟨Algebra.TensorProduct.includeRight c, by
      rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, nsmul_eq_mul, mul_comm]⟩
  refine ⟨fun ⟨φ⟩ ↦ ?_, fun h ↦ ?_⟩
  · let _ : Algebra (ZMod (p ^ N.factorization p)) (ZMod p) :=
      ZMod.algebra' (ZMod p) p (dvd_pow_self p he.out)
    let bc : NonsplitCartanAlgebraPow p (N.factorization p) →ₐ[ZMod (p ^ N.factorization p)]
        QuadraticAlgebra (ZMod p) (algebraMap (ZMod (p ^ N.factorization p)) (ZMod p)
          (nonsplitCartanA p).val) (algebraMap (ZMod (p ^ N.factorization p)) (ZMod p)
          (nonsplitCartanB p).val) :=
      QuadraticAlgebra.baseChange (ZMod p) _ _
    have hbc : Function.Surjective bc :=
      QuadraticAlgebra.mapRingHom_surjective _ _ _ (ZMod.ringHom_surjective _)
    let g' : NonsplitCartanAlgebraPow p (N.factorization p) →ₐ[ZMod (p ^ N.factorization p)]
        A ⧸ Ideal.span {(p : A)} :=
      g.comp φ.symm.toAlgHom
    have hg' : Function.Surjective g' := hg.comp φ.symm.surjective
    have hker' : RingHom.ker g' = RingHom.ker bc := by
      ext m
      rw [RingHom.mem_ker, RingHom.mem_ker]
      refine ⟨fun hm ↦ ?_, fun hm ↦ ?_⟩
      · rcases hker (φ.symm m) hm with ⟨m', hm'⟩
        rw [← φ.apply_symm_apply m, hm', map_smul, map_smul]
        ext <;> simp [Algebra.smul_def]
      · rcases exists_eq_smul_of_baseChange_eq_zero hm with ⟨m', rfl⟩
        rw [map_smul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul, hC, zero_mul]
    exact ((Ideal.quotientKerAlgEquivOfSurjective hg').symm.trans
      ((Ideal.quotientEquivAlgOfEq _ hker').trans
        (Ideal.quotientKerAlgEquivOfSurjective hbc))).toMulEquiv.isField (Field.toIsField _)
  · rcases isSplitAt_or_isNonsplitAt b hp with ⟨⟨φ⟩⟩ | h'
    · let _ : Field (A ⧸ Ideal.span {(p : A)}) := h.toField
      have hpu : ¬IsUnit (p : ZMod (p ^ N.factorization p)) := by
        rw [ZMod.isUnit_iff_castHom_ne_zero he.out, map_natCast, ZMod.natCast_self, ne_eq,
          not_not]
      have hnot (z : ZMod (p ^ N.factorization p) × ZMod (p ^ N.factorization p))
          (hz : IsUnit z.1 ∨ IsUnit z.2) : g (φ.symm z) ≠ 0 := fun h0 ↦ by
        rcases hker _ h0 with ⟨m', hm'⟩
        rw [← φ.apply_symm_apply z, hm', map_smul, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
          smul_eq_mul] at hz
        exact hz.elim (fun hz ↦ hpu (isUnit_of_mul_isUnit_left hz))
          fun hz ↦ hpu (isUnit_of_mul_isUnit_left hz)
      have h0 : g (φ.symm (1, 0)) * g (φ.symm (0, 1)) = 0 := by
        rw [← map_mul, ← map_mul, Prod.mk_mul_mk, mul_zero, zero_mul, Prod.mk_zero_zero, map_zero,
          map_zero]
      exact ((mul_eq_zero.mp h0).elim (hnot (1, 0) (.inl isUnit_one))
        (hnot (0, 1) (.inr isUnit_one))).elim
    · exact h'

variable [Algebra.Etale (ZMod N) A] [Algebra.Etale (ZMod N) A'] in
lemma nonempty_algEquiv_tensor_of_isSplitAt_iff (b : Basis (Fin 2) (ZMod N) A)
    (b' : Basis (Fin 2) (ZMod N) A') (hp : p ∈ N.primeFactors)
    (h : IsSplitAt N p A ↔ IsSplitAt N p A') :
    Nonempty (ZMod (p ^ N.factorization p) ⊗[ZMod N] A ≃ₐ[ZMod (p ^ N.factorization p)]
      ZMod (p ^ N.factorization p) ⊗[ZMod N] A') := by
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  rcases isSplitAt_or_isNonsplitAt b hp with ⟨⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩
  · rcases h.mp ⟨e₁⟩ with ⟨e₂⟩
    exact ⟨e₁.trans e₂.symm⟩
  · rcases isSplitAt_or_isNonsplitAt b' hp with h₂ | ⟨⟨e₂⟩⟩
    · exact absurd ⟨h.mpr h₂, ⟨e₁⟩⟩ (not_isSplitAt_and_isNonsplitAt hp)
    · exact ⟨e₁.trans e₂.symm⟩

variable [NeZero N]

variable (N) in
/-- The Chinese remainder theorem for `ℤ/Nℤ`, as an isomorphism of `ℤ/Nℤ`-algebras
`ℤ/Nℤ ≅ ∏_{p ∣ N} ℤ/p^{v_p(N)}ℤ`. -/
noncomputable def zmodAlgEquivPi :
    ZMod N ≃ₐ[ZMod N] Π p : N.primeFactors, ZMod ((p : ℕ) ^ N.factorization p) :=
  AlgEquiv.ofRingEquiv (f := ZMod.equivPi N (NeZero.ne N)) fun x ↦
    RingHom.congr_fun (Subsingleton.elim ((ZMod.equivPi N (NeZero.ne N)).toRingHom.comp
      (algebraMap (ZMod N) (ZMod N))) (algebraMap _ _)) x

variable (N A) in
/-- The Chinese remainder theorem for an algebra `A` over `ℤ/Nℤ`: `A` is the product of its
components `ℤ/p^{v_p(N)}ℤ ⊗ A` at the primes `p ∣ N`. -/
noncomputable def algEquivPiTensor :
    A ≃ₐ[ZMod N] Π p : N.primeFactors, ZMod ((p : ℕ) ^ N.factorization p) ⊗[ZMod N] A :=
  (Algebra.TensorProduct.lid (ZMod N) A).symm.trans <|
    (Algebra.TensorProduct.congr (zmodAlgEquivPi N) AlgEquiv.refl).trans <|
    (Algebra.TensorProduct.comm (ZMod N) _ A).trans <|
    (Algebra.TensorProduct.piRight (ZMod N) (ZMod N) A _).trans <|
    AlgEquiv.piCongrRight fun _ ↦ Algebra.TensorProduct.comm (ZMod N) A _

lemma algebraMap_eq_equivPi (hp : p ∈ N.primeFactors) (x : ZMod N) :
    algebraMap (ZMod N) (ZMod (p ^ N.factorization p)) x = ZMod.equivPi N (NeZero.ne N) x ⟨p, hp⟩ :=
  RingHom.congr_fun (Subsingleton.elim _
    ((Pi.evalRingHom _ ⟨p, hp⟩).comp (ZMod.equivPi N (NeZero.ne N)).toRingHom)) x

variable (N) in
/-- The coefficient `a` of `NonsplitAtAlgebra N S`: congruent modulo `p^{v_p(N)}` to the
coefficient `a` of the non-split algebra for `p ∈ S`, and to `0` for the other primes `p ∣ N`. -/
noncomputable def nonsplitAtCoeffA (S : Finset ℕ) : ZMod N :=
  (ZMod.equivPi N (NeZero.ne N)).symm fun p ↦
    haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    if (p : ℕ) ∈ S then ((nonsplitCartanA (p : ℕ)).val : ZMod _) else 0

variable (N) in
/-- The coefficient `b` of `NonsplitAtAlgebra N S`: congruent modulo `p^{v_p(N)}` to the
coefficient `b` of the non-split algebra for `p ∈ S`, and to `1` for the other primes `p ∣ N`. -/
noncomputable def nonsplitAtCoeffB (S : Finset ℕ) : ZMod N :=
  (ZMod.equivPi N (NeZero.ne N)).symm fun p ↦
    haveI : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    if (p : ℕ) ∈ S then ((nonsplitCartanB (p : ℕ)).val : ZMod _) else 1

variable (N) in
/-- The quadratic algebra `(ℤ/Nℤ)[ω]`, `ω² = a + b ω`, that is non-split exactly at the primes of
`S` dividing `N` (LMFDB `gl2.cartan`): modulo `p^{v_p(N)}` it is the non-split algebra for `p ∈ S`
and `ω² = ω`, the split algebra, for the other primes `p ∣ N`. -/
abbrev NonsplitAtAlgebra (S : Finset ℕ) : Type :=
  QuadraticAlgebra (ZMod N) (nonsplitAtCoeffA N S) (nonsplitAtCoeffB N S)

variable {S : Finset ℕ}

variable [Fact p.Prime] in
lemma algebraMap_nonsplitAtCoeffA (hp : p ∈ N.primeFactors) :
    algebraMap (ZMod N) (ZMod (p ^ N.factorization p)) (nonsplitAtCoeffA N S) =
      if p ∈ S then ((nonsplitCartanA p).val : ZMod _) else 0 := by
  rw [algebraMap_eq_equivPi hp, nonsplitAtCoeffA, RingEquiv.apply_symm_apply]

variable [Fact p.Prime] in
lemma algebraMap_nonsplitAtCoeffB (hp : p ∈ N.primeFactors) :
    algebraMap (ZMod N) (ZMod (p ^ N.factorization p)) (nonsplitAtCoeffB N S) =
      if p ∈ S then ((nonsplitCartanB p).val : ZMod _) else 1 := by
  rw [algebraMap_eq_equivPi hp, nonsplitAtCoeffB, RingEquiv.apply_symm_apply]

lemma isUnit_discr_nonsplitAtCoeffA :
    IsUnit (QuadraticAlgebra.discr (nonsplitAtCoeffA N S) (nonsplitAtCoeffB N S)) := by
  rw [← MulEquiv.isUnit_map (ZMod.equivPi N (NeZero.ne N)).toMulEquiv, Pi.isUnit_iff]
  intro p
  have : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
  rw [RingEquiv.toMulEquiv_eq_coe, RingEquiv.coe_toMulEquiv, ← algebraMap_eq_equivPi p.2,
    QuadraticAlgebra.discr_def, map_add, map_pow, map_mul, map_ofNat,
    algebraMap_nonsplitAtCoeffA p.2, algebraMap_nonsplitAtCoeffB p.2, ← QuadraticAlgebra.discr_def]
  split_ifs
  · exact isUnit_discr_nonsplitCartanAlgebraPow
  · simp [QuadraticAlgebra.discr_def]

instance : Algebra.Etale (ZMod N) (NonsplitAtAlgebra N S) :=
  QuadraticAlgebra.etale_of_isUnit_discr isUnit_discr_nonsplitAtCoeffA

variable [Fact p.Prime] in
lemma isNonsplitAt_nonsplitAtAlgebra (hpN : p ∈ N.primeFactors) (hp : p ∈ S) :
    IsNonsplitAt N p (NonsplitAtAlgebra N S) := by
  rcases nonempty_algEquiv_quadraticAlgebra_of_eq ((algebraMap_nonsplitAtCoeffA hpN).trans
    (ite_eq_left hp)) ((algebraMap_nonsplitAtCoeffB hpN).trans (ite_eq_left hp)) with ⟨φ⟩
  exact ⟨(QuadraticAlgebra.baseChangeEquiv _ _ _).trans φ⟩

variable [Fact p.Prime] in
lemma isSplitAt_nonsplitAtAlgebra (hpN : p ∈ N.primeFactors) (hp : p ∉ S) :
    IsSplitAt N p (NonsplitAtAlgebra N S) := by
  rcases nonempty_algEquiv_quadraticAlgebra_of_eq ((algebraMap_nonsplitAtCoeffA hpN).trans
    (ite_eq_right hp)) ((algebraMap_nonsplitAtCoeffB hpN).trans (ite_eq_right hp)) with ⟨φ⟩
  rcases nonempty_algEquiv_quadraticAlgebra_zero_one (ZMod (p ^ N.factorization p)) with ⟨ψ⟩
  exact ⟨((QuadraticAlgebra.baseChangeEquiv _ _ _).trans φ).trans ψ⟩

/-- **`NonsplitAtAlgebra N S` is split exactly at the primes dividing `N` outside `S`** (LMFDB
`gl2.cartan`). -/
lemma isSplitAt_nonsplitAtAlgebra_iff (hp : p ∈ N.primeFactors) :
    IsSplitAt N p (NonsplitAtAlgebra N S) ↔ p ∉ S := by
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  refine ⟨fun h hS ↦ not_isSplitAt_and_isNonsplitAt hp ⟨h, isNonsplitAt_nonsplitAtAlgebra hp hS⟩,
    isSplitAt_nonsplitAtAlgebra hp⟩

variable [Fact p.Prime] in
/-- **`NonsplitAtAlgebra N S` is non-split exactly at the primes of `S` dividing `N`** (LMFDB
`gl2.cartan`): a free étale algebra of rank `2` over `ℤ/Nℤ` can be split or non-split
independently at each prime dividing `N`. -/
lemma isNonsplitAt_nonsplitAtAlgebra_iff (hp : p ∈ N.primeFactors) :
    IsNonsplitAt N p (NonsplitAtAlgebra N S) ↔ p ∈ S :=
  ⟨fun h ↦ not_not.mp fun hS ↦ not_isSplitAt_and_isNonsplitAt hp
    ⟨isSplitAt_nonsplitAtAlgebra hp hS, h⟩, isNonsplitAt_nonsplitAtAlgebra hp⟩

variable [Algebra.Etale (ZMod N) A] [Algebra.Etale (ZMod N) A'] in
/-- **Free étale algebras of rank `2` over `ℤ/Nℤ` are determined by their split primes**: two of
them are isomorphic exactly when they are split at the same primes dividing `N`. -/
lemma nonempty_algEquiv_iff_forall_isSplitAt_iff (b : Basis (Fin 2) (ZMod N) A)
    (b' : Basis (Fin 2) (ZMod N) A') :
    Nonempty (A ≃ₐ[ZMod N] A') ↔ ∀ p ∈ N.primeFactors, (IsSplitAt N p A ↔ IsSplitAt N p A') := by
  refine ⟨fun ⟨φ⟩ p _ ↦ ?_, fun h ↦ ?_⟩
  · let ψ : ZMod (p ^ N.factorization p) ⊗[ZMod N] A ≃ₐ[ZMod (p ^ N.factorization p)]
        ZMod (p ^ N.factorization p) ⊗[ZMod N] A' :=
      Algebra.TensorProduct.congr AlgEquiv.refl φ
    exact ⟨fun ⟨e⟩ ↦ ⟨ψ.symm.trans e⟩, fun ⟨e⟩ ↦ ⟨ψ.trans e⟩⟩
  · exact ⟨(algEquivPiTensor N A).trans ((AlgEquiv.piCongrRight fun q : N.primeFactors ↦
      (nonempty_algEquiv_tensor_of_isSplitAt_iff b b' q.2 (h q q.2)).some.restrictScalars
        (ZMod N)).trans (algEquivPiTensor N A').symm)⟩

variable [Algebra.Etale (ZMod N) A] in
/-- **The free étale algebras of rank `2` over `ℤ/Nℤ`** (LMFDB `gl2.cartan`): such an algebra is
isomorphic to `NonsplitAtAlgebra N S` for exactly one set `S` of primes dividing `N`, the set of
primes where it is non-split. -/
lemma existsUnique_nonempty_algEquiv_nonsplitAtAlgebra (b : Basis (Fin 2) (ZMod N) A) :
    ∃! S : Finset ℕ, S ⊆ N.primeFactors ∧ Nonempty (A ≃ₐ[ZMod N] NonsplitAtAlgebra N S) := by
  classical
  refine ⟨N.primeFactors.filter fun p ↦ ¬IsSplitAt N p A, ⟨Finset.filter_subset _ _,
    (nonempty_algEquiv_iff_forall_isSplitAt_iff b (QuadraticAlgebra.basis _ _)).mpr fun p hp ↦ ?_⟩,
    fun S ⟨hS, ⟨φ⟩⟩ ↦ ?_⟩
  · simp [isSplitAt_nonsplitAtAlgebra_iff hp, hp]
  · ext p
    by_cases hp : p ∈ N.primeFactors
    · have h : IsSplitAt N p A ↔ p ∉ S := ((nonempty_algEquiv_iff_forall_isSplitAt_iff b
        (QuadraticAlgebra.basis _ _)).mp ⟨φ⟩ p hp).trans (isSplitAt_nonsplitAtAlgebra_iff hp)
      simp [hp, h]
    · simpa [hp] using fun h ↦ hp (hS h)

end Matrix.GeneralLinearGroup
