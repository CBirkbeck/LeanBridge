import LeanBridge.ForMathlib.RingTheory.Etale.QuadraticZModPow
import Mathlib.Algebra.QuadraticAlgebra.Int
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.TensorProduct.Quotient
import TauCeti.NumberTheory.NumberField.Global.Orders.Basic
import TauCeti.NumberTheory.NumberField.QuadraticAlgebra

/-!
# The non-split algebra over `ℤ/p^eℤ` as a quotient `O/p^eO`

Let `p` be a prime and `e ≥ 1`. If `O` is a commutative ring in which `p O` is a prime ideal, with
`#(O/pO) = p²` and `#(O/p^eO) = p^{2e}`, then `O/p^eO` is the non-split algebra over `ℤ/p^eℤ`
(LMFDB `gl2.cartan`): `O/pO` is a finite domain, hence the field `𝔽_{p²}`, and the reduction
`O/p^eO → O/pO` is surjective with kernel `p (O/p^eO)`, so the non-split algebra, which is
formally smooth, lifts to an isomorphism onto `O/p^eO`. The cardinalities hold for every `O` free
of rank `2` over `ℤ_p` or over `ℤ`, since `O/tO ≅ (Λ/tΛ) ⊗ O ≅ (Λ/tΛ)²` for such an algebra over
`Λ`. This covers the knowl's two descriptions:
* the unramified extension of degree `2` of `ℤ_p`, a free `ℤ_p`-algebra of rank `2` in which `p`
  generates the maximal ideal, that is, in which `p O` is prime;
* a quadratic order in which `p` is inert, that is, an order `O` of a quadratic number field (Tau
  Ceti's `NumberFieldOrder`), free of rank `2` over `ℤ`, with `p O` prime.

The statements are ring isomorphisms: a ring has at most one `ℤ/p^eℤ`-algebra structure, so they
are isomorphisms of `ℤ/p^eℤ`-algebras.

## Main results

* `Matrix.GeneralLinearGroup.nonempty_ringEquiv_nonsplitCartanAlgebraPow_of_isPrime`: `O/p^eO` is
  the non-split algebra when `p O` is prime and `O/pO`, `O/p^eO` have `p²`, `p^{2e}` elements.
* `Matrix.GeneralLinearGroup.nonempty_ringEquiv_nonsplitCartanAlgebraPow_of_padicInt` (LMFDB
  `gl2.cartan`): the case of a free `ℤ_p`-algebra of rank `2`, such as the unramified quadratic
  extension of `ℤ_p`.
* `Matrix.GeneralLinearGroup.isPrime_span_natCast_quadraticAlgebra_padicInt`: `p` is inert in the
  free `ℤ_p`-algebra `ℤ_p[ω]` of rank `2`, `ω² = a + b ω` with `a` and `b` lifting the coefficients
  of `𝔽_{p²}`.
* `Matrix.GeneralLinearGroup.nonempty_ringEquiv_nonsplitCartanAlgebraPow_of_int`: the case of a
  free `ℤ`-algebra of rank `2`.
* `Matrix.GeneralLinearGroup.nonempty_ringEquiv_nonsplitCartanAlgebraPow_of_numberFieldOrder`
  (LMFDB `gl2.cartan`): the case of a quadratic order in which `p` is inert.
* `Matrix.GeneralLinearGroup.isPrime_span_natCast_ofIsFractionRing_quadraticAlgebra`: every prime
  `p` is inert in the order `ℤ[ω]` of the quadratic field `ℚ(ω)`, with `ω` as above.
* `TauCeti.GlobalNumberFields.NumberFieldOrder.finrank_int_toSubalgebra`: an order of a number
  field `K` has rank `[K : ℚ]` over `ℤ`.

The ring of integers of Tau Ceti's unramified quadratic extension `TauCeti.unramifiedExtension ℚ_[p]
Ω 2` is such a free `ℤ_p`-algebra: see
`LeanBridge.ForMathlib.NumberTheory.LocalField.UnramifiedNonsplitCartan`.
-/

open Module

namespace TauCeti.GlobalNumberFields.NumberFieldOrder

/-- **An order of a number field `K` is a free `ℤ`-module of rank `[K : ℚ]`**: a `ℤ`-basis of the
order is linearly independent over `ℚ` and spans `K`. -/
lemma finrank_int_toSubalgebra {K : Type*} [Field K] [NumberField K] (O : NumberFieldOrder K) :
    finrank ℤ O.toSubalgebra = finrank ℚ K := by
  let b : Basis (Free.ChooseBasisIndex ℤ O.toSubalgebra) ℤ O.toSubalgebra :=
    Free.chooseBasis ℤ O.toSubalgebra
  let f : O.toSubalgebra →ₗ[ℤ] K := O.toSubalgebra.val.toLinearMap.restrictScalars ℤ
  have hli : LinearIndependent ℚ fun i ↦ (b i : K) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).mp
      (b.linearIndependent.map' f (LinearMap.ker_eq_bot.mpr Subtype.val_injective))
  have hspan : ⊤ ≤ Submodule.span ℚ (Set.range fun i ↦ (b i : K)) := by
    rw [← O.spans, Submodule.span_le]
    intro x hx
    have hx' : (⟨x, hx⟩ : O.toSubalgebra) ∈ Submodule.span ℤ (Set.range b) := b.span_eq ▸ trivial
    have h : f ⟨x, hx⟩ ∈ Submodule.span ℤ (f '' Set.range b) :=
      Submodule.apply_mem_span_image_of_mem_span f hx'
    rw [← Set.range_comp] at h
    exact Submodule.span_subset_span ℤ ℚ _ h
  rw [finrank_eq_card_chooseBasisIndex, finrank_eq_card_basis (Basis.mk hli hspan)]

end TauCeti.GlobalNumberFields.NumberFieldOrder

namespace Matrix.GeneralLinearGroup

variable {p e : ℕ} {O Λ : Type*} [CommRing O] [CommRing Λ]

lemma natCard_quotient_span_algebraMap [Algebra Λ O] (b : Basis (Fin 2) Λ O) (t : Λ) :
    Nat.card (O ⧸ Ideal.span {algebraMap Λ O t}) = Nat.card (Λ ⧸ Ideal.span {t}) ^ 2 := by
  rw [← Set.image_singleton, ← Ideal.map_span,
    Nat.card_congr (Algebra.TensorProduct.quotIdealMapEquivQuotTensor O (Ideal.span {t})).toEquiv,
    Nat.card_congr (Algebra.TensorProduct.basis _ b).equivFun.toEquiv, Nat.card_fun,
    Nat.card_fin]

lemma natCard_int_quotient (n : ℕ) : Nat.card (ℤ ⧸ Ideal.span {(p : ℤ) ^ n}) = p ^ n := by
  rw [← Nat.cast_pow, Nat.card_congr (Int.quotientSpanNatEquivZMod _).toEquiv, Nat.card_zmod]

variable [Fact p.Prime]

lemma natCard_padicInt_quotient (n : ℕ) :
    Nat.card (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p]) ^ n}) = p ^ n := by
  rw [← PadicInt.ker_toZModPow,
    Nat.card_congr (RingHom.quotientKerEquivOfSurjective (ZMod.ringHom_surjective _)).toEquiv,
    Nat.card_zmod]

variable [NeZero e]

/-- **`O/p^eO` is the non-split algebra when `p` is inert in `O`**: if `p O` is a prime ideal of a
commutative ring `O`, with `#(O/pO) = p²` and `#(O/p^eO) = p^{2e}`, then `O/p^eO` is isomorphic to
`NonsplitCartanAlgebraPow p e`. -/
lemma nonempty_ringEquiv_nonsplitCartanAlgebraPow_of_isPrime (hp : (Ideal.span {(p : O)}).IsPrime)
    (h₁ : Nat.card (O ⧸ Ideal.span {(p : O)}) = p ^ 2)
    (hₑ : Nat.card (O ⧸ Ideal.span {(p : O) ^ e}) = p ^ (2 * e)) :
    Nonempty (O ⧸ Ideal.span {(p : O) ^ e} ≃+* NonsplitCartanAlgebraPow p e) := by
  have hle : Ideal.span {(p : O) ^ e} ≤ Ideal.span {(p : O)} :=
    Ideal.span_singleton_le_span_singleton.mpr (dvd_pow_self _ (NeZero.ne e))
  have hM : ((p ^ e : ℕ) : O ⧸ Ideal.span {(p : O) ^ e}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk _), Nat.cast_pow, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  have hC : ((p : ℕ) : O ⧸ Ideal.span {(p : O)}) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton_self _
  have : Finite (O ⧸ Ideal.span {(p : O)}) :=
    Nat.finite_of_card_ne_zero (by rw [h₁]; exact pow_ne_zero 2 (NeZero.ne p))
  have : (Ideal.span {(p : O)}).IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (Finite.isField_of_domain _)
  let _ : Field (O ⧸ Ideal.span {(p : O)}) := Ideal.Quotient.field _
  let _ : Algebra (ZMod p) (O ⧸ Ideal.span {(p : O)}) := ZMod.algebra' _ _ (ringChar.dvd hC)
  let _ : Algebra (ZMod (p ^ e)) (O ⧸ Ideal.span {(p : O)}) :=
    ZMod.algebra' _ _ (ringChar.dvd (by rw [Nat.cast_pow, hC, zero_pow (NeZero.ne e)]))
  let _ : Algebra (ZMod (p ^ e)) (O ⧸ Ideal.span {(p : O) ^ e}) :=
    ZMod.algebra' _ _ (ringChar.dvd hM)
  let _ : Algebra (ZMod (p ^ e)) (ZMod p) := ZMod.algebra' (ZMod p) p (dvd_pow_self p (NeZero.ne e))
  have hker (m : O ⧸ Ideal.span {(p : O) ^ e})
      (hm : (Ideal.Quotient.factor hle).toZModAlgHom (p ^ e) m = 0) :
      ∃ m', m = (p : ZMod (p ^ e)) • m' := by
    rcases Ideal.Quotient.mk_surjective m with ⟨x, rfl⟩
    rw [RingHom.coe_toZModAlgHom, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton'] at hm
    rcases hm with ⟨y, rfl⟩
    refine ⟨Ideal.Quotient.mk _ y, ?_⟩
    rw [Algebra.smul_def, map_natCast, ← map_natCast (Ideal.Quotient.mk _), ← map_mul, mul_comm]
  rcases nonempty_algEquiv_nonsplitCartanAlgebraPow_of_surjective hₑ.ge
    (g := (Ideal.Quotient.factor hle).toZModAlgHom (p ^ e)) (Ideal.Quotient.factor_surjective hle)
    hker (GaloisField.algEquivGaloisField p 2 h₁).toRingEquiv with ⟨φ⟩
  exact ⟨φ.symm.toRingEquiv⟩

/-- **`O/p^eO` for the unramified quadratic extension `O` of `ℤ_p`** (LMFDB `gl2.cartan`): if `O`
is a free `ℤ_p`-algebra of rank `2` in which `p O` is a prime ideal, such as the ring of integers
of the unramified quadratic extension of `ℚ_p`, then `O/p^eO` is isomorphic to the non-split
algebra `NonsplitCartanAlgebraPow p e`. -/
lemma nonempty_ringEquiv_nonsplitCartanAlgebraPow_of_padicInt [Algebra ℤ_[p] O]
    (b : Basis (Fin 2) ℤ_[p] O) (hp : (Ideal.span {(p : O)}).IsPrime) :
    Nonempty (O ⧸ Ideal.span {(p : O) ^ e} ≃+* NonsplitCartanAlgebraPow p e) := by
  have h (n : ℕ) : Nat.card (O ⧸ Ideal.span {(p : O) ^ n}) = p ^ (2 * n) := by
    rw [← map_natCast (algebraMap ℤ_[p] O), ← map_pow, natCard_quotient_span_algebraMap b,
      natCard_padicInt_quotient, ← pow_mul, mul_comm]
  exact nonempty_ringEquiv_nonsplitCartanAlgebraPow_of_isPrime hp (by simpa using h 1) (h e)

/-- **`O/p^eO` for a free `ℤ`-algebra `O` of rank `2` in which `p` is inert**: if `p O` is a prime
ideal, then `O/p^eO` is isomorphic to the non-split algebra `NonsplitCartanAlgebraPow p e`. -/
lemma nonempty_ringEquiv_nonsplitCartanAlgebraPow_of_int (b : Basis (Fin 2) ℤ O)
    (hp : (Ideal.span {(p : O)}).IsPrime) :
    Nonempty (O ⧸ Ideal.span {(p : O) ^ e} ≃+* NonsplitCartanAlgebraPow p e) := by
  have h (n : ℕ) : Nat.card (O ⧸ Ideal.span {(p : O) ^ n}) = p ^ (2 * n) := by
    rw [← map_natCast (algebraMap ℤ O), ← map_pow, natCard_quotient_span_algebraMap b,
      natCard_int_quotient, ← pow_mul, mul_comm]
  exact nonempty_ringEquiv_nonsplitCartanAlgebraPow_of_isPrime hp (by simpa using h 1) (h e)

open TauCeti GlobalNumberFields in
/-- **`O/p^eO` for a quadratic order `O` in which `p` is inert** (LMFDB `gl2.cartan`): if `O` is an
order of a quadratic number field and `p O` is a prime ideal, then `O/p^eO` is isomorphic to the
non-split algebra `NonsplitCartanAlgebraPow p e`. -/
lemma nonempty_ringEquiv_nonsplitCartanAlgebraPow_of_numberFieldOrder {K : Type*} [Field K]
    [NumberField K] (hK : finrank ℚ K = 2) (O : NumberFieldOrder K)
    (hp : (Ideal.span {(p : O.toSubalgebra)}).IsPrime) :
    Nonempty (O.toSubalgebra ⧸ Ideal.span {(p : O.toSubalgebra) ^ e} ≃+*
      NonsplitCartanAlgebraPow p e) :=
  nonempty_ringEquiv_nonsplitCartanAlgebraPow_of_int
    (finBasisOfFinrankEq ℤ O.toSubalgebra (O.finrank_int_toSubalgebra.trans hK)) hp

lemma isPrime_span_natCast_quadraticAlgebra {a b : Λ} (π : Λ →+* ZMod p)
    (hπ : ∀ x, π x = 0 → ∃ y, x = p * y) [Fact (∀ r : ZMod p, r ^ 2 ≠ π a + π b * r)] :
    (Ideal.span {(p : QuadraticAlgebra Λ a b)}).IsPrime := by
  have h : RingHom.ker (QuadraticAlgebra.mapRingHom π a b) =
      Ideal.span {(p : QuadraticAlgebra Λ a b)} := by
    ext x
    rw [RingHom.mem_ker, Ideal.mem_span_singleton']
    refine ⟨fun hx ↦ ?_, ?_⟩
    · rcases hπ x.re (congrArg QuadraticAlgebra.re hx) with ⟨y₁, h₁⟩
      rcases hπ x.im (congrArg QuadraticAlgebra.im hx) with ⟨y₂, h₂⟩
      exact ⟨⟨y₁, y₂⟩, by ext <;> simp [h₁, h₂, mul_comm]⟩
    · rintro ⟨y, rfl⟩
      have hp : (p : QuadraticAlgebra (ZMod p) (π a) (π b)) = 0 := by
        ext <;> simp
      rw [map_mul, map_natCast, hp, mul_zero]
  exact h ▸ RingHom.ker_isPrime _

/-- **The unramified quadratic extension `ℤ_p[ω]` of `ℤ_p`**: in the quadratic algebra `ℤ_p[ω]`,
`ω² = a + b ω`, with `a` and `b` lifting the coefficients of `𝔽_{p²}`, the ideal `p ℤ_p[ω]` is
prime. So this free `ℤ_p`-algebra of rank `2` satisfies the hypotheses of
`nonempty_ringEquiv_nonsplitCartanAlgebraPow_of_padicInt`. -/
lemma isPrime_span_natCast_quadraticAlgebra_padicInt : (Ideal.span {(p : QuadraticAlgebra ℤ_[p]
    (nonsplitCartanA p).val (nonsplitCartanB p).val)}).IsPrime := by
  have : Fact (∀ r : ZMod p, r ^ 2 ≠ PadicInt.toZMod ((nonsplitCartanA p).val : ℤ_[p]) +
      PadicInt.toZMod ((nonsplitCartanB p).val : ℤ_[p]) * r) :=
    ⟨by simpa only [map_natCast, ZMod.natCast_zmod_val] using sq_ne_nonsplitCartanA_add p⟩
  refine isPrime_span_natCast_quadraticAlgebra PadicInt.toZMod fun x hx ↦ ?_
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton'] at hx
  rcases hx with ⟨y, rfl⟩
  exact ⟨y, mul_comm _ _⟩

lemma isPrime_span_natCast_quadraticAlgebra_int : (Ideal.span {(p : QuadraticAlgebra ℤ
    (nonsplitCartanA p).val (nonsplitCartanB p).val)}).IsPrime := by
  have : Fact (∀ r : ZMod p, r ^ 2 ≠ Int.castRingHom (ZMod p) ((nonsplitCartanA p).val : ℤ) +
      Int.castRingHom (ZMod p) ((nonsplitCartanB p).val : ℤ) * r) :=
    ⟨by simpa only [map_natCast, ZMod.natCast_zmod_val] using sq_ne_nonsplitCartanA_add p⟩
  refine isPrime_span_natCast_quadraticAlgebra (Int.castRingHom (ZMod p)) fun x hx ↦ ?_
  rcases (ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp hx with ⟨y, rfl⟩
  exact ⟨y, rfl⟩

lemma isPrime_span_natCast_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (f : R ≃+* S)
    {n : ℕ} (h : (Ideal.span {(n : R)}).IsPrime) : (Ideal.span {(n : S)}).IsPrime := by
  rw [← map_natCast f, ← Set.image_singleton, ← Ideal.map_span]
  exact Ideal.map_isPrime_of_equiv f

lemma not_isSquare_discr_nonsplitCartan_int : ¬IsSquare
    (QuadraticAlgebra.discr ((nonsplitCartanA p).val : ℤ) ((nonsplitCartanB p).val : ℤ)) := by
  by_cases hp : p = 2
  · subst hp
    simp only [nonsplitCartanA, nonsplitCartanB, ite_true, ZMod.val_one, QuadraticAlgebra.discr_def]
    rintro ⟨k, hk⟩
    push_cast at hk
    have h₁ : k ≤ 2 := by nlinarith
    have h₂ : -2 ≤ k := by nlinarith
    interval_cases k <;> norm_num at hk
  · rintro ⟨k, hk⟩
    have h : Int.castRingHom (ZMod p) (QuadraticAlgebra.discr ((nonsplitCartanA p).val : ℤ)
        ((nonsplitCartanB p).val : ℤ)) = Int.castRingHom (ZMod p) (k * k) :=
      congrArg _ hk
    rw [QuadraticAlgebra.discr_def, map_add, map_pow, map_mul, map_ofNat, map_natCast,
      map_natCast, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, nonsplitCartanA_of_ne_two p hp,
      nonsplitCartanB_of_ne_two p hp, map_mul] at h
    refine ZMod.not_isSquare_leastPrimitiveRoot p hp ⟨Int.castRingHom (ZMod p) k * 2⁻¹, ?_⟩
    have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_ne_two p hp
    rw [mul_mul_mul_comm, ← h]
    field_simp
    ring1

instance : Fact (¬IsSquare
    (QuadraticAlgebra.discr ((nonsplitCartanA p).val : ℤ) ((nonsplitCartanB p).val : ℤ))) :=
  ⟨not_isSquare_discr_nonsplitCartan_int⟩

instance : Fact (∀ r : ℚ, r ^ 2 ≠ (((nonsplitCartanA p).val : ℤ) : ℚ) +
    (((nonsplitCartanB p).val : ℤ) : ℚ) * r) :=
  ⟨fun r hr ↦ not_isSquare_discr_nonsplitCartan_int <| Rat.isSquare_intCast_iff.mp <| by
    rw [← QuadraticAlgebra.discr_intCast]
    exact QuadraticAlgebra.exists_sq_eq_iff_isSquare_discr.mp ⟨r, hr⟩⟩

open TauCeti GlobalNumberFields in
/-- **Every prime `p` is inert in a quadratic order**: in the order `ℤ[ω]`, `ω² = a + b ω`, of the
quadratic field `ℚ(ω)` (of degree `2` by `QuadraticAlgebra.finrank_eq_two`), with `a` and `b`
lifting the coefficients of `𝔽_{p²}`, the ideal `p ℤ[ω]` is prime. So the hypotheses of
`nonempty_ringEquiv_nonsplitCartanAlgebraPow_of_numberFieldOrder` are met for every `p`. -/
lemma isPrime_span_natCast_ofIsFractionRing_quadraticAlgebra : (Ideal.span {(p :
    (NumberFieldOrder.ofIsFractionRing (QuadraticAlgebra ℤ ((nonsplitCartanA p).val : ℤ)
    ((nonsplitCartanB p).val : ℤ)) (QuadraticAlgebra ℚ (((nonsplitCartanA p).val : ℤ) : ℚ)
    (((nonsplitCartanB p).val : ℤ) : ℚ))).toSubalgebra)}).IsPrime :=
  isPrime_span_natCast_of_ringEquiv (NumberFieldOrder.ofIsFractionRingEquiv _ _)
    isPrime_span_natCast_quadraticAlgebra_int

end Matrix.GeneralLinearGroup
