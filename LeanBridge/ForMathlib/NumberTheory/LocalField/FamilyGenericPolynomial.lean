import LeanBridge.ForMathlib.NumberTheory.LocalField.EisensteinDiagram
import LeanBridge.ForMathlib.NumberTheory.LocalField.ExtensionFamily
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

/-!
# Generic and semicanonical polynomials of families of extensions of `p`-adic fields

Let `K` be a `p`-adic field with residue field of `q` elements, `I = [s_1, …, s_w]_ε^f` a Herbrand
invariant and `e = ε p ^ w`. The family `I / K` (LMFDB `lf.family_polynomial`) is the set of
`K`-isomorphism classes of the extensions of `K` of residue degree `f`, ramification index `e` and
Swan slopes `s_1, …, s_w` (`IsNonarchimedeanLocalField.HerbrandInvariant.family`); it is an
absolute family if `K = ℚ_p` and a relative family otherwise.

Following Monge, the LMFDB attaches to `I / K` a generic polynomial
`f_I(x) = x ^ e + π ∑_σ f_σ π ^ j x ^ i`, `σ = j e + i` with `0 ≤ i < e`, over the ring of integers
`𝒪_{K_f}` of the unramified extension `K_f` of degree `f`, `π` a uniformiser of `K`. The sum runs
over the `D`-point `σ = 0`, the `A`- and `B`-points and the critical `C`-points of the Eisenstein
diagram of `I` (LMFDB `lf.eisenstein_diagram`); the coefficients `f_σ` are indeterminates, written
`d_0`, `a_σ`, `b_σ`, `c_σ` according to the type of the point. The semicanonical polynomials are
its specialisations with `a_σ ∈ ℛ ∖ {0}`, `b_σ ∈ ℛ`, `c_σ ∈ S_σ` and `d_0 ∈ 𝒟`, where `ℛ ∋ 0, 1` is
a set of representatives of the residue field `λ` of `K_f`, `S_σ ⊆ ℛ` a set of representatives of
a quotient `λ / W_σ`, and `𝒟 ⊆ ℛ ∖ {0}` a set of representatives of `λ^× / (λ^×)^ε`, `𝒟 = {1}`
when `gcd(ε, q ^ f - 1) = 1`. The knowl leaves the subgroups `W_σ` to Monge's reduction algorithm,
and they are data here (`IsNonarchimedeanLocalField.HerbrandInvariant.SemicanonicalChoice`). The
polynomials are defined over any commutative ring `R` with an element `π`, the LMFDB's case being
`R = 𝒪_{K_f}`; over a discrete valuation ring with uniformiser `π` the semicanonical polynomials are
Eisenstein polynomials of degree `e`. That every extension in `I / K` is generated over `K_f` by a
root of a semicanonical polynomial (Monge) is not formalised.

The knowl writes the terms of `f_I` as `a_{σ(i, j)} π_K ^ i x ^ j` with `σ(i, j) = e j + i`, which
is inconsistent with its term `d_0 π_K` and with LMFDB `lf.eisenstein_diagram`; the monomial of
`σ = e j + i` is `π_K ^ (j + 1) x ^ i`, as in `lf.eisenstein_diagram`, which is used here.

## Main definitions

* `IsNonarchimedeanLocalField.HerbrandInvariant.absoluteFamily` (LMFDB `lf.family_polynomial`): the
  absolute family `I / ℚ_p`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.genericIndices`: the indices `σ` of the terms of the
  generic polynomial.
* `IsNonarchimedeanLocalField.HerbrandInvariant.specialisation`: the polynomial
  `x ^ e + π ∑_σ f_σ π ^ j x ^ i` for given coefficients `f_σ`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.genericPolynomial` (LMFDB `lf.family_polynomial`):
  the generic polynomial `f_I`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.SemicanonicalChoice`: the sets `ℛ`, `S_σ` and `𝒟`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.semicanonicalPolynomials`
  (LMFDB `lf.family_polynomial`): the semicanonical polynomials.

## Main results

* `IsNonarchimedeanLocalField.HerbrandInvariant.map_eval_genericPolynomial`: the specialisations of
  the generic polynomial.
* `IsNonarchimedeanLocalField.HerbrandInvariant.monic_specialisation` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.natDegree_specialisation`: they are monic of degree
  `e`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.isEisensteinAt_of_mem_semicanonicalPolynomials`:
  over a discrete valuation ring, the semicanonical polynomials are Eisenstein.
-/

open Ideal IsLocalRing Polynomial

namespace IsNonarchimedeanLocalField.HerbrandInvariant

variable {p : ℕ} (I : HerbrandInvariant p)

variable [Fact p.Prime] in
/-- The **absolute family** (LMFDB `lf.family_polynomial`) of a Herbrand invariant `I`: the family
`I / ℚ_p` of extensions of `ℚ_p`. A family `I / K` over a `p`-adic field `K ≠ ℚ_p` is a **relative
family**. -/
noncomputable def absoluteFamily : ExtensionFamily ℚ_[p] :=
  I.family ℚ_[p]

/-- The **indices** `σ = j e + i` of the terms of the generic polynomial of a Herbrand invariant
`I`: the `D`-point `σ = 0`, the `A`- and `B`-points, and the critical `C`-points, those on the top
border `s = s_j` of a band, of the Eisenstein diagram of `I`. They all lie in its strip
`σ ≤ e s_w`. -/
noncomputable def genericIndices : Finset ℕ :=
  {σ ∈ Finset.range (⌊(I.ramificationIndex : ℚ) * I.swanSlope I.w⌋₊ + 1) | I.pointType σ = .D ∨
    I.pointType σ = .A ∨ I.pointType σ = .B ∨
      I.pointType σ = .C ∧ (I.point σ).2 ∈ (Finset.Icc 1 I.w).image I.swanSlope}

lemma pointType_zero : I.pointType 0 = .D :=
  ite_eq_left rfl

lemma zero_mem_genericIndices : 0 ∈ I.genericIndices :=
  Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos _), Or.inl I.pointType_zero⟩

variable {R : Type*} [CommRing R] (π : R) (f : ℕ → R)

/-- The polynomial `x ^ e + π ∑_σ f_σ π ^ j x ^ i`, the sum over the indices `σ = j e + i`,
`0 ≤ i < e`, of `genericIndices`, for given coefficients `f_σ` in a commutative ring `R` and
`π ∈ R`: the **specialisation** of the generic polynomial of `I` at these coefficients
(`map_eval_genericPolynomial`). -/
noncomputable def specialisation : R[X] :=
  X ^ I.ramificationIndex + C π * ∑ σ ∈ I.genericIndices,
    C (f σ * π ^ (σ / I.ramificationIndex)) * X ^ (σ % I.ramificationIndex)

/-- The **generic polynomial** `f_I` (LMFDB `lf.family_polynomial`) of a Herbrand invariant
`I = [s_1, …, s_w]_ε^f`, for a uniformiser `π` of the base field: the polynomial
`x ^ e + π ∑_σ f_σ π ^ j x ^ i` with indeterminate coefficients `f_σ = X σ` (the LMFDB's `d_0`,
`a_σ`, `b_σ`, `c_σ` for the `D`-, `A`-, `B`- and critical `C`-points), `σ = j e + i` running over
`genericIndices`. Its coefficients are polynomials in the `f_σ` over a commutative ring `R`, for
the LMFDB the ring of integers of the unramified extension `K_f` of `K` of degree `f`, which
contains `π`. -/
noncomputable def genericPolynomial : (MvPolynomial ℕ R)[X] :=
  I.specialisation (MvPolynomial.C π) MvPolynomial.X

/-- **The specialisations of the generic polynomial**: evaluating its coefficients at `f_σ ∈ R`
gives `x ^ e + π ∑_σ f_σ π ^ j x ^ i`. -/
lemma map_eval_genericPolynomial :
    (I.genericPolynomial π).map (MvPolynomial.eval f) = I.specialisation π f := by
  simp [genericPolynomial, specialisation, Polynomial.map_sum]

/-- The **choices of coefficients** of the semicanonical polynomials of a Herbrand invariant
`I = [s_1, …, s_w]_ε^f` over a commutative ring `R` with an ideal `𝔪`, the LMFDB's case being the
ring of integers of `K_f` and its maximal ideal, with residue field `λ = R / 𝔪` (LMFDB
`lf.family_polynomial`): a set `ℛ` of representatives of `λ` containing `0` and `1`, for each
critical `C`-point `σ` a subset `S_σ ⊆ ℛ` of representatives of a quotient `λ / W_σ` of `λ`, for an
additive subgroup `W_σ` that the knowl leaves to Monge, and a subset `𝒟 ⊆ ℛ ∖ {0}` of
representatives of `λ^× / (λ^×)^ε`, which is `{1}` when `gcd(ε, |λ| - 1) = 1`. -/
structure SemicanonicalChoice (𝔪 : Ideal R) where
  /-- The set `ℛ` of representatives of the residue ring `λ = R / 𝔪`. -/
  reps : Set R
  zero_mem_reps : 0 ∈ reps
  one_mem_reps : 1 ∈ reps
  existsUnique_mem_reps (x : R ⧸ 𝔪) : ∃! r, r ∈ reps ∧ algebraMap R (R ⧸ 𝔪) r = x
  /-- The subgroup `W_σ` of `λ` whose quotient the coefficient `c_σ` represents. -/
  subgroup : ℕ → AddSubgroup (R ⧸ 𝔪)
  /-- The set `S_σ ⊆ ℛ` of representatives of `λ / W_σ` from which `c_σ` is chosen. -/
  quotientReps : ℕ → Set R
  quotientReps_subset (σ : ℕ) : quotientReps σ ⊆ reps
  existsUnique_mem_quotientReps (σ : ℕ) (x : R ⧸ 𝔪) :
    ∃! r, r ∈ quotientReps σ ∧ algebraMap R (R ⧸ 𝔪) r - x ∈ subgroup σ
  /-- The set `𝒟 ⊆ ℛ ∖ {0}` of representatives of `λ^× / (λ^×)^ε` from which `d_0` is chosen. -/
  unitReps : Set R
  unitReps_subset : unitReps ⊆ reps \ {0}
  existsUnique_mem_unitReps (u : (R ⧸ 𝔪)ˣ) :
    ∃! d, d ∈ unitReps ∧ ∃ v : (R ⧸ 𝔪)ˣ, algebraMap R (R ⧸ 𝔪) d = ↑(u * v ^ I.ε)
  unitReps_eq (h : I.ε.gcd (Nat.card (R ⧸ 𝔪) - 1) = 1) : unitReps = {1}

namespace SemicanonicalChoice

variable {I} {𝔪 : Ideal R} (D : I.SemicanonicalChoice 𝔪)

/-- The set from which the coefficient `f_σ` of a semicanonical polynomial is chosen, according to
the type of the point `P_σ`: `𝒟` for the `D`-point, `ℛ ∖ {0}` for an `A`-point, `ℛ` for a
`B`-point, `S_σ` for a `C`-point and `{0}` for a `Z`-point. -/
noncomputable def coeffSet (σ : ℕ) : Set R :=
  match I.pointType σ with
  | .D => D.unitReps
  | .A => D.reps \ {0}
  | .B => D.reps
  | .C => D.quotientReps σ
  | .Z => {0}

lemma coeffSet_zero : D.coeffSet 0 = D.unitReps := by
  simp only [coeffSet, pointType_zero]

lemma notMem_of_mem_unitReps {d : R} (hd : d ∈ D.unitReps) : d ∉ 𝔪 := by
  intro hd𝔪
  rcases D.existsUnique_mem_reps 0 with ⟨r, -, hr⟩
  have h₀ : (0 : R) = r := hr 0 ⟨D.zero_mem_reps, map_zero _⟩
  have h₁ : d = r := hr d ⟨(D.unitReps_subset hd).1, Quotient.eq_zero_iff_mem.mpr hd𝔪⟩
  exact (D.unitReps_subset hd).2 (h₁.trans h₀.symm)

end SemicanonicalChoice

/-- The **semicanonical polynomials** (LMFDB `lf.family_polynomial`) of a Herbrand invariant `I`,
for a uniformiser `π` and choices `D` of coefficient sets: the specialisations
`x ^ e + π ∑_σ f_σ π ^ j x ^ i` of the generic polynomial with `f_σ` in the set
`D.coeffSet σ` attached to the type of `P_σ`: `d_0 ∈ 𝒟`, `a_σ ∈ ℛ ∖ {0}`, `b_σ ∈ ℛ` and
`c_σ ∈ S_σ`. Over the ring of integers of `K_f`, with Monge's choice of the `S_σ`, every extension
in the family `I / K` is generated over `K_f` by a root of one of them (not formalised). -/
def semicanonicalPolynomials {𝔪 : Ideal R} (D : I.SemicanonicalChoice 𝔪) : Set R[X] :=
  {g | ∃ f : ℕ → R, (∀ σ ∈ I.genericIndices, f σ ∈ D.coeffSet σ) ∧ I.specialisation π f = g}

variable {I}

lemma coeff_specialisation_of_lt {n : ℕ} (hn : n < I.ramificationIndex) :
    (I.specialisation π f).coeff n = π * ∑ σ ∈ I.genericIndices,
      if n = σ % I.ramificationIndex then f σ * π ^ (σ / I.ramificationIndex) else 0 := by
  rw [specialisation, coeff_add, coeff_X_pow, ite_eq_right hn.ne, zero_add, coeff_C_mul,
    finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]

variable [NeZero p]

lemma ramificationIndex_pos : 0 < I.ramificationIndex :=
  Nat.mul_pos I.ε_pos <| Nat.pos_of_ne_zero <| pow_ne_zero _ <| NeZero.ne p

lemma degree_specialisation_sub_lt :
    (C π * ∑ σ ∈ I.genericIndices, C (f σ * π ^ (σ / I.ramificationIndex)) *
      X ^ (σ % I.ramificationIndex)).degree < I.ramificationIndex := by
  refine (degree_lt_iff_coeff_zero _ _).mpr fun m hm ↦ ?_
  rw [coeff_C_mul, finsetSum_coeff]
  refine mul_eq_zero_of_right π <| Finset.sum_eq_zero fun σ _ ↦ ?_
  rw [coeff_C_mul_X_pow, ite_eq_right ((Nat.mod_lt σ I.ramificationIndex_pos).trans_le hm).ne']

variable [Nontrivial R] in
/-- **The specialisations of the generic polynomial are monic.** -/
lemma monic_specialisation : (I.specialisation π f).Monic :=
  (monic_X_pow _).add_of_left <| (degree_X_pow (R := R) _).symm ▸ degree_specialisation_sub_lt π f

variable [Nontrivial R] in
/-- **The specialisations of the generic polynomial have degree `e`.** -/
lemma natDegree_specialisation : (I.specialisation π f).natDegree = I.ramificationIndex := by
  rw [specialisation, natDegree_add_eq_left_of_degree_lt <|
    (degree_X_pow (R := R) _).symm ▸ degree_specialisation_sub_lt π f, natDegree_X_pow]

variable [IsDomain R] [IsDiscreteValuationRing R] {π f}

lemma isEisensteinAt_specialisation (hπ : Irreducible π) (hf : f 0 ∉ maximalIdeal R) :
    (I.specialisation π f).IsEisensteinAt (maximalIdeal R) := by
  have h𝔪 : maximalIdeal R = Ideal.span {π} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  refine ⟨?_, fun {n} hn ↦ ?_, ?_⟩
  · rw [(monic_specialisation π f).leadingCoeff]
    exact (maximalIdeal.isMaximal R).ne_top ∘ (Ideal.eq_top_iff_one _).mpr
  · rw [natDegree_specialisation] at hn
    rw [coeff_specialisation_of_lt π f hn, h𝔪]
    exact Ideal.mem_span_singleton.mpr <| dvd_mul_right π _
  · rw [coeff_specialisation_of_lt π f I.ramificationIndex_pos,
      ← Finset.add_sum_erase _ _ I.zero_mem_genericIndices, h𝔪, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, pow_two, mul_dvd_mul_iff_left hπ.ne_zero, Nat.zero_mod,
      Nat.zero_div, pow_zero, mul_one, ite_eq_left rfl]
    refine fun h ↦ hf <| h𝔪 ▸ Ideal.mem_span_singleton.mpr <|
      (dvd_add_left <| Finset.dvd_sum fun σ hσ ↦ ?_).mp h
    split_ifs with hσe
    · refine (dvd_pow_self π fun h0 ↦ ?_).mul_left _
      have h : I.ramificationIndex * (σ / I.ramificationIndex) + σ % I.ramificationIndex = σ :=
        Nat.div_add_mod σ I.ramificationIndex
      rw [h0, mul_zero, zero_add, ← hσe] at h
      exact (Finset.mem_erase.mp hσ).1 h.symm
    · exact dvd_zero π

/-- **The semicanonical polynomials are Eisenstein polynomials**: over a discrete valuation ring
`R` with uniformiser `π`, such as the ring of integers of `K_f`, every semicanonical polynomial of
`I` is Eisenstein at the maximal ideal (and monic of degree `e`, `natDegree_specialisation`), since
its coefficient `d_0 ∈ 𝒟 ⊆ ℛ ∖ {0}` is a unit. -/
lemma isEisensteinAt_of_mem_semicanonicalPolynomials (hπ : Irreducible π)
    {D : I.SemicanonicalChoice (maximalIdeal R)} {g : R[X]}
    (hg : g ∈ I.semicanonicalPolynomials π D) : g.IsEisensteinAt (maximalIdeal R) := by
  rcases hg with ⟨f, hf, rfl⟩
  exact isEisensteinAt_specialisation hπ <| D.notMem_of_mem_unitReps <|
    D.coeffSet_zero ▸ hf 0 I.zero_mem_genericIndices

end IsNonarchimedeanLocalField.HerbrandInvariant
