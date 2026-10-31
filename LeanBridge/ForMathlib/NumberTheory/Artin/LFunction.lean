import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.FieldTheory.Galois.IsGaloisGroup
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Eigenspace.Charpoly
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.RingTheory.Frobenius
import LeanBridge.ForMathlib.NumberTheory.Artin.Basic
import LeanBridge.ForMathlib.NumberTheory.Artin.Conductor

/-!
# Artin L-functions

Let `K/ℚ` be a finite Galois extension and `ρ` a representation of `Gal(K/ℚ)` on a
finite-dimensional complex vector space `V`. At a prime `Q` of `𝓞 K` above a prime number `p`, the
inertia group `I_Q` is normal in the decomposition group `D_Q`, so `D_Q` acts on the inertia
invariants `V^{I_Q}`; the arithmetic Frobenius elements at `Q` (Mathlib's `IsArithFrobAt`) form a
coset of `I_Q`, so they all act on `V^{I_Q}` by the same linear map. Its reversed characteristic
polynomial `det(1 - T ρ(Frob_Q) | V^{I_Q})` does not depend on the prime `Q` above `p`, and the
Artin L-function is the Euler product `L(ρ, s) = ∏_p det(1 - ρ(Frob_p) p ^ (-s) | V^{I_p})⁻¹`,
which converges for `re s > 1`.

## Main definitions

* `Representation.inertiaInvariants`: the inertia invariants `V^{I_Q}`.
* `Representation.frobeniusInertiaInvariants` (LMFDB `artin.lfunction`): Frobenius acting on
  `V^{I_Q}`.
* `Representation.eulerPolynomialAt`: the polynomial `det(1 - T ρ(Frob_Q) | V^{I_Q})`.
* `Representation.artinEulerPolynomial` (LMFDB `artin.lfunction`): the Euler polynomial at a prime
  number `p`.
* `Representation.artinLFunction` (LMFDB `artin.lfunction`): the Artin L-function.
* `Representation.IsArtin.galoisFactor`: the representation of the Galois group of the Artin field
  through which an Artin representation of `Gal(ℚ̄/ℚ)` factors.
* `Representation.IsArtin.eulerPolynomial` and `Representation.IsArtin.lFunction` (LMFDB
  `artin.lfunction`): the Euler polynomials and the L-function of an Artin representation of
  `Gal(ℚ̄/ℚ)`, computed in the Galois group of its Artin field.

## Main results

* `Representation.apply_eq_frobeniusInertiaInvariants`: every arithmetic Frobenius element at `Q`
  acts on `V^{I_Q}` as `frobeniusInertiaInvariants`.
* `Representation.eulerPolynomialAt_smul` and `Representation.artinEulerPolynomial_eq`: the Euler
  polynomial does not depend on the prime above `p`.
* `Representation.eval_eulerPolynomialAt`: the Euler polynomial is `det(1 - T ρ(Frob_Q))`.
* `Representation.multipliable_artinLFunction` and `Representation.IsArtin.multipliable_lFunction`:
  the Euler product converges for `re s > 1`.
-/

open Module Nat NumberField Polynomial
open scoped Pointwise

lemma Polynomial.reverse_multisetProd_X_sub_C {F : Type*} [Field F] (s : Multiset F) :
    (s.map fun μ ↦ X - C μ).prod.reverse = (s.map fun μ ↦ 1 - C μ * X).prod := by
  have hX : (X : F[X]).reverse = 1 := by
    rw [← one_mul X, ← C_1, reverse_mul_X, reverse_C]
  induction s using Multiset.induction_on with
  | empty => simpa using reverse_C (1 : F)
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain, ih, Multiset.map_cons,
      Multiset.prod_cons, sub_eq_add_neg, ← C_neg, reverse_add_C, hX, natDegree_X, pow_one, C_neg,
      neg_mul, ← sub_eq_add_neg]

lemma LinearMap.eval_reverse_charpoly {W : Type*} [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (f : Module.End ℂ W) (y : ℂ) :
    f.charpoly.reverse.eval y = (f.charpoly.roots.map fun μ ↦ 1 - μ * y).prod := by
  conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq f.charpoly_monic
    IsAlgClosed.card_roots_eq_natDegree]
  rw [reverse_multisetProd_X_sub_C, eval_multiset_prod, Multiset.map_map]
  simp

lemma Complex.norm_multisetProd_inv_one_sub_mul_sub_one_le {s : Multiset ℂ} (hs : ∀ μ ∈ s, ‖μ‖ = 1)
    {y : ℂ} (hy : ‖y‖ ≤ 1 / 2) : ‖(s.map fun μ ↦ (1 - μ * y)⁻¹).prod - 1‖ ≤ 4 ^ s.card * ‖y‖ := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : ‖a‖ = 1 := hs a (Multiset.mem_cons_self a s)
    have h₁ : 1 / 2 ≤ ‖1 - a * y‖ := by
      have h : ‖(1 : ℂ)‖ - ‖a * y‖ ≤ ‖1 - a * y‖ := norm_sub_norm_le 1 (a * y)
      rw [norm_one, norm_mul, ha, one_mul] at h
      linarith
    have h₀ : 1 - a * y ≠ 0 := norm_pos_iff.mp (by linarith)
    have h₂ : ‖(1 - a * y)⁻¹‖ ≤ 2 := by
      rw [norm_inv]
      exact inv_le_of_inv_le₀ two_pos (by linarith)
    have h₃ : ‖(1 - a * y)⁻¹ - 1‖ ≤ 2 * ‖y‖ := by
      have h : (1 - a * y)⁻¹ - 1 = a * y * (1 - a * y)⁻¹ := by
        field_simp
        ring1
      rw [h, norm_mul, norm_mul, ha, one_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right h₂ (norm_nonneg y)
    have h₄ : ‖(s.map fun μ ↦ (1 - μ * y)⁻¹).prod - 1‖ ≤ 4 ^ s.card * ‖y‖ :=
      ih fun μ hμ ↦ hs μ (Multiset.mem_cons_of_mem hμ)
    have h₅ : (1 - a * y)⁻¹ * (s.map fun μ ↦ (1 - μ * y)⁻¹).prod - 1 = (1 - a * y)⁻¹ *
        ((s.map fun μ ↦ (1 - μ * y)⁻¹).prod - 1) + ((1 - a * y)⁻¹ - 1) := by
      ring1
    have h₆ : (1 : ℝ) ≤ 4 ^ s.card := one_le_pow₀ (by norm_num)
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, h₅]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul]
    nlinarith [mul_le_mul h₂ h₄ (norm_nonneg _) zero_le_two, norm_nonneg y]

namespace Representation

variable {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
  {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [MulSemiringAction G S]
  [SMulCommClass G R S] (Q : Ideal S) {σ : G} {v : V} (τ : G)

/-- The **inertia invariants** `V^{I_Q}` of a representation `ρ` of a group `G` acting on a ring
`S`, at an ideal `Q` of `S`: the vectors fixed by the inertia group `I_Q` of `Q`, the subgroup of
the elements of `G` acting trivially on `S ⧸ Q`. -/
noncomputable def inertiaInvariants : Submodule ℂ V :=
  invariants (ρ.comp (Q.inertia G).subtype)

lemma apply_mem_inertiaInvariants_smul (hv : v ∈ ρ.inertiaInvariants Q) :
    ρ τ v ∈ ρ.inertiaInvariants (τ • Q) := by
  rintro ⟨g, hg⟩
  rw [Ideal.inertia_smul] at hg
  rcases hg with ⟨h, hh, rfl⟩
  have hv' : ρ h v = v := hv ⟨h, hh⟩
  simp [hv']

lemma apply_mem_inertiaInvariants (hσ : σ ∈ MulAction.stabilizer G Q)
    (hv : v ∈ ρ.inertiaInvariants Q) : ρ σ v ∈ ρ.inertiaInvariants Q :=
  MulAction.mem_stabilizer_iff.mp hσ ▸ ρ.apply_mem_inertiaInvariants_smul Q σ hv

variable (R) [Finite G] [Algebra.IsInvariant R S G] [Q.IsPrime] [Finite (S ⧸ Q)]

/-- **Frobenius on the inertia invariants** (LMFDB `artin.lfunction`): the action on `V^{I_Q}` of
Mathlib's choice `arithFrobAt R G Q` of an arithmetic Frobenius element at `Q`, an element of the
decomposition group of `Q` that acts on `S ⧸ Q` as `x ↦ x ^ q`, where `q` is the number of elements
of `R ⧸ (Q ∩ R)`. Every arithmetic Frobenius element at `Q` acts on `V^{I_Q}` by this map
(`Representation.apply_eq_frobeniusInertiaInvariants`). -/
noncomputable def frobeniusInertiaInvariants : Module.End ℂ (ρ.inertiaInvariants Q) :=
  (ρ (arithFrobAt R G Q)).restrict fun _ ↦
    ρ.apply_mem_inertiaInvariants Q (IsArithFrobAt.arithFrobAt R G Q).mem_stabilizer

/-- **Frobenius acts on the inertia invariants by a single linear map**: every arithmetic Frobenius
element `σ` at `Q` acts on `V^{I_Q}` as `frobeniusInertiaInvariants`, since two of them differ by
an element of the inertia group. -/
lemma apply_eq_frobeniusInertiaInvariants (hσ : IsArithFrobAt R σ Q) (w : ρ.inertiaInvariants Q) :
    ρ σ w = ρ.frobeniusInertiaInvariants R Q w := by
  have h : ρ (σ * (arithFrobAt R G Q)⁻¹) (ρ (arithFrobAt R G Q) w) = ρ (arithFrobAt R G Q) w :=
    ρ.apply_mem_inertiaInvariants Q (IsArithFrobAt.arithFrobAt R G Q).mem_stabilizer w.2
      ⟨_, hσ.mul_inv_mem_inertia (.arithFrobAt R G Q)⟩
  rwa [← End.mul_apply, ← map_mul, inv_mul_cancel_right] at h

lemma coe_frobeniusInertiaInvariants_pow_apply (n : ℕ) (w : ρ.inertiaInvariants Q) :
    ((ρ.frobeniusInertiaInvariants R Q ^ n) w : V) = ρ (arithFrobAt R G Q ^ n) w := by
  induction n generalizing w with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, End.mul_apply, ih, pow_succ, map_mul, End.mul_apply]
    rfl

lemma frobeniusInertiaInvariants_pow_card : ρ.frobeniusInertiaInvariants R Q ^ Nat.card G = 1 :=
  LinearMap.ext fun v ↦ Subtype.ext <| by
    rw [coe_frobeniusInertiaInvariants_pow_apply, pow_card_eq_one', map_one]
    rfl

variable [FiniteDimensional ℂ V]

/-- The **Euler polynomial** of `ρ` at `Q`: the reversed characteristic polynomial
`det(1 - T ρ(Frob_Q) | V^{I_Q})` of Frobenius on the inertia invariants
(`Representation.eval_eulerPolynomialAt`). -/
noncomputable def eulerPolynomialAt : ℂ[X] :=
  (ρ.frobeniusInertiaInvariants R Q).charpoly.reverse

/-- **The Euler polynomial is invariant under the Galois action on primes**: `ρ(τ)` maps `V^{I_Q}`
onto `V^{I_{τ Q}}` and conjugates Frobenius at `Q` to Frobenius at `τ Q`. -/
lemma eulerPolynomialAt_smul [Finite (S ⧸ τ • Q)] :
    ρ.eulerPolynomialAt R (τ • Q) = ρ.eulerPolynomialAt R Q := by
  let e : ρ.inertiaInvariants Q ≃ₗ[ℂ] ρ.inertiaInvariants (τ • Q) :=
    LinearEquiv.ofLinearMap ((ρ τ).restrict fun _ ↦ ρ.apply_mem_inertiaInvariants_smul Q τ)
      ((ρ τ⁻¹).restrict fun _ hv ↦
        inv_smul_smul τ Q ▸ ρ.apply_mem_inertiaInvariants_smul (τ • Q) τ⁻¹ hv)
      (LinearMap.ext fun v ↦ Subtype.ext (ρ.self_inv_apply τ v))
      (LinearMap.ext fun v ↦ Subtype.ext (ρ.inv_self_apply τ v))
  have h : ρ.frobeniusInertiaInvariants R (τ • Q) = e.conj (ρ.frobeniusInertiaInvariants R Q) := by
    ext v
    rw [← ρ.apply_eq_frobeniusInertiaInvariants R (τ • Q)
      ((IsArithFrobAt.arithFrobAt R G Q).conj τ) v]
    simp [e, frobeniusInertiaInvariants]
  rw [eulerPolynomialAt, eulerPolynomialAt, h, LinearEquiv.charpoly_conj]

/-- **The Euler polynomial is `det(1 - T ρ(Frob_Q) | V^{I_Q})`**: its value at `y` is the
determinant of `1 - y ρ(Frob_Q)` on the inertia invariants. -/
lemma eval_eulerPolynomialAt (y : ℂ) :
    (ρ.eulerPolynomialAt R Q).eval y = (1 - y • ρ.frobeniusInertiaInvariants R Q).det := by
  rw [eulerPolynomialAt, ← LinearMap.charpoly_toMatrix _ (Free.chooseBasis ℂ _),
    Matrix.reverse_charpoly, Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det,
    ← LinearMap.det_toMatrix (Free.chooseBasis ℂ _)]
  congr 1
  ext i j
  simp [Matrix.one_apply, apply_ite (eval y)]
  ring1

lemma norm_eq_one_of_mem_roots_charpoly {μ : ℂ}
    (hμ : μ ∈ (ρ.frobeniusInertiaInvariants R Q).charpoly.roots) : ‖μ‖ = 1 := by
  rcases ((End.hasEigenvalue_iff_isRoot_charpoly _ μ).mpr
    (isRoot_of_mem_roots hμ)).exists_hasEigenvector with ⟨w, hw⟩
  refine Complex.norm_eq_one_of_pow_eq_one (smul_left_injective ℂ hw.2
    (?_ : μ ^ Nat.card G • w = (1 : ℂ) • w)) Nat.card_pos.ne'
  rw [← hw.pow_apply, frobeniusInertiaInvariants_pow_card, End.one_apply, one_smul]

lemma norm_inv_eval_eulerPolynomialAt_sub_one_le {y : ℂ} (hy : ‖y‖ ≤ 1 / 2) :
    ‖((ρ.eulerPolynomialAt R Q).eval y)⁻¹ - 1‖ ≤ 4 ^ finrank ℂ V * ‖y‖ := by
  rw [eulerPolynomialAt, LinearMap.eval_reverse_charpoly, ← Multiset.prod_map_inv]
  refine (Complex.norm_multisetProd_inv_one_sub_mul_sub_one_le
    (fun μ hμ ↦ ρ.norm_eq_one_of_mem_roots_charpoly R Q hμ) hy).trans ?_
  gcongr
  · norm_num
  · rw [IsAlgClosed.card_roots_eq_natDegree, LinearMap.charpoly_natDegree]
    exact Submodule.finrank_le _

end Representation

namespace Representation

variable {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V] (ρ : Representation ℂ Gal(K/ℚ) V) (p : Nat.Primes) {s : ℂ}

lemma finite_quotient_of_liesOver (Q : Ideal (𝓞 K)) [Q.LiesOver (Ideal.span {(p : ℤ)})] :
    Finite (𝓞 K ⧸ Q) := by
  have hp : Ideal.span {(p : ℤ)} ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (by exact_mod_cast p.prop.ne_zero)
  exact Q.finiteQuotientOfFreeOfNeBot (Ideal.ne_bot_of_liesOver_of_ne_bot hp Q)

variable [IsGalois ℚ K]

/-- The **Euler polynomial** of `ρ` at a prime number `p` (LMFDB `artin.lfunction`): the polynomial
`det(1 - T ρ(Frob_Q) | V^{I_Q})` of Frobenius acting on the inertia invariants at a prime `Q` of
`𝓞 K` above `p`, which does not depend on `Q` (`Representation.artinEulerPolynomial_eq`). Here
`Frob_Q` is any arithmetic Frobenius element at `Q`, acting on `𝓞 K ⧸ Q` as `x ↦ x ^ p`
(`Representation.apply_eq_frobeniusInertiaInvariants`). -/
noncomputable def artinEulerPolynomial : ℂ[X] :=
  haveI : (Ideal.span {(p : ℤ)}).IsPrime := isPrime_span_natCast p
  letI Q : Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K) := Classical.arbitrary _
  haveI : Finite (𝓞 K ⧸ Q.1) := finite_quotient_of_liesOver p Q.1
  ρ.eulerPolynomialAt ℤ Q.1

/-- **The Euler polynomial at `p` is that of any prime above `p`**, since the Galois group acts
transitively on the primes above `p`. -/
lemma artinEulerPolynomial_eq (Q : Ideal (𝓞 K)) [Q.IsPrime] [Q.LiesOver (Ideal.span {(p : ℤ)})]
    [Finite (𝓞 K ⧸ Q)] : ρ.artinEulerPolynomial p = ρ.eulerPolynomialAt ℤ Q := by
  have : (Ideal.span {(p : ℤ)}).IsPrime := isPrime_span_natCast p
  let Q₀ : Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K) := Classical.arbitrary _
  have : Finite (𝓞 K ⧸ Q₀.1) := finite_quotient_of_liesOver p Q₀.1
  rcases Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(p : ℤ)}) Q₀.1 Q Gal(K/ℚ) with ⟨τ, rfl⟩
  rw [ρ.eulerPolynomialAt_smul ℤ Q₀.1 τ]
  rfl

variable (s) in
/-- The **Artin L-function** of `ρ` (LMFDB `artin.lfunction`): the Euler product
`L(ρ, s) = ∏_p det(1 - ρ(Frob_p) p ^ (-s) | V^{I_p})⁻¹` over the prime numbers `p`, where
`Frob_p` acts on the inertia invariants `V^{I_p}` (all of `V` at the primes unramified in `K`). It
converges for `re s > 1` (`Representation.multipliable_artinLFunction`), where it defines `L(ρ, s)`.
Elsewhere the value is junk: Mathlib's `tprod` is `1` where the product does not converge, and the
product may also converge there, e.g. to `0` at `s = 0` for the trivial representation, where every
factor is `0⁻¹ = 0`. The meromorphic continuation of `L(ρ, s)` is not defined here. -/
noncomputable def artinLFunction : ℂ :=
  ∏' p : Nat.Primes, ((ρ.artinEulerPolynomial p).eval ((p : ℂ) ^ (-s)))⁻¹

/-- **The Euler product of an Artin L-function converges for `re s > 1`**: the factor at `p` is
`1 + O(p ^ (-re s))`. -/
lemma multipliable_artinLFunction (hs : 1 < s.re) :
    Multipliable fun p : Nat.Primes ↦ ((ρ.artinEulerPolynomial p).eval ((p : ℂ) ^ (-s)))⁻¹ := by
  have hnorm (p : Nat.Primes) : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [Complex.norm_natCast_cpow_of_pos p.prop.pos, Complex.neg_re]
  have hle (p : Nat.Primes) : ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
    rw [hnorm, one_div, ← Real.rpow_neg_one]
    refine (Real.rpow_le_rpow_of_nonpos two_pos (by exact_mod_cast p.prop.two_le)
      (by linarith)).trans (Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith))
  have hsum :
      Summable fun p : Nat.Primes ↦ ‖((ρ.artinEulerPolynomial p).eval ((p : ℂ) ^ (-s)))⁻¹ - 1‖ := by
    refine (((Primes.summable_rpow (r := -s.re)).mpr (by linarith)).mul_left
      (4 ^ finrank ℂ V)).of_nonneg_of_le (fun _ ↦ norm_nonneg _) fun p ↦ ?_
    have : (Ideal.span {(p : ℤ)}).IsPrime := isPrime_span_natCast p
    have : Finite (𝓞 K ⧸ (Classical.arbitrary (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K))).1) :=
      finite_quotient_of_liesOver p _
    rw [← hnorm]
    exact ρ.norm_inv_eval_eulerPolynomialAt_sub_one_le ℤ _ (hle p)
  simpa using multipliable_one_add_of_summable hsum

end Representation

namespace Representation.IsArtin

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ Gal(AlgebraicClosure ℚ/ℚ) V} (h : ρ.IsArtin) {s : ℂ}

/-- The **Galois factor** of an Artin representation `ρ` of `Gal(ℚ̄/ℚ)`: the representation of the
Galois group `Gal(L/ℚ)` of its Artin field `L` through which `ρ` factors
(`Representation.IsArtin.galoisFactor_restrictNormalHom`). -/
noncomputable def galoisFactor : Representation ℂ Gal(ρ.artinField/ℚ) V :=
  haveI : IsGalois ℚ ρ.artinField := h.isGalois
  (Units.coeHom _).comp <| (AlgEquiv.restrictNormalHom ρ.artinField).liftOfSurjective
    (AlgEquiv.restrictNormalHom_surjective _) ⟨ρ.toHomUnits, fun _ hσ ↦ Units.ext <|
      MonoidHom.mem_ker.mp <| h.fixingSubgroup_artinField ▸
        (IntermediateField.restrictNormalHom_ker _).le hσ⟩

lemma galoisFactor_restrictNormalHom (σ : Gal(AlgebraicClosure ℚ/ℚ)) :
    haveI : IsGalois ℚ ρ.artinField := h.isGalois
    h.galoisFactor (AlgEquiv.restrictNormalHom ρ.artinField σ) = ρ σ :=
  congrArg Units.val (MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ σ)

/-- The **Euler polynomial** at a prime number `p` of an Artin representation `ρ` of `Gal(ℚ̄/ℚ)`
(LMFDB `artin.lfunction`): `det(1 - T ρ(Frob_p) | V^{I_p})`, computed in the Galois group of the
Artin field of `ρ`, the smallest finite Galois extension through which `ρ` factors. -/
noncomputable def eulerPolynomial (p : Nat.Primes) : ℂ[X] :=
  haveI : FiniteDimensional ℂ V := h.finiteDimensional_space
  haveI : FiniteDimensional ℚ ρ.artinField := h.finiteDimensional
  haveI : NumberField ρ.artinField := ⟨⟩
  haveI : IsGalois ℚ ρ.artinField := h.isGalois
  h.galoisFactor.artinEulerPolynomial p

variable (s) in
/-- The **Artin L-function** `L(ρ, s) = ∏_p det(1 - ρ(Frob_p) p ^ (-s) | V^{I_p})⁻¹` of an Artin
representation `ρ` of `Gal(ℚ̄/ℚ)` (LMFDB `artin.lfunction`), the Euler product of
`Representation.IsArtin.eulerPolynomial`, which converges for `re s > 1`
(`Representation.IsArtin.multipliable_lFunction`). As for `Representation.artinLFunction`, its
value outside `re s > 1` is junk. -/
noncomputable def lFunction : ℂ :=
  ∏' p : Nat.Primes, ((h.eulerPolynomial p).eval ((p : ℂ) ^ (-s)))⁻¹

/-- **The Euler product of the Artin L-function of an Artin representation converges for
`re s > 1`.** -/
lemma multipliable_lFunction (hs : 1 < s.re) :
    Multipliable fun p : Nat.Primes ↦ ((h.eulerPolynomial p).eval ((p : ℂ) ^ (-s)))⁻¹ := by
  have : FiniteDimensional ℂ V := h.finiteDimensional_space
  have : FiniteDimensional ℚ ρ.artinField := h.finiteDimensional
  have : NumberField ρ.artinField := ⟨⟩
  have : IsGalois ℚ ρ.artinField := h.isGalois
  exact h.galoisFactor.multipliable_artinLFunction hs

end Representation.IsArtin
