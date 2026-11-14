import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Subgroup.ZPowers.Lemmas
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# The Mazur–Ullom subtypes of three elements of an abelian group

Let `K` be a real biquadratic field with units `U`, and let `e₀, e₁, e₂` be fundamental units of
its three quadratic subfields. Their classes generate a subgroup of `U/{±1}` that contains every
square, and Kubota's list, as Mazur and Ullom quote it, sorts the ways in which square roots of
products of the `eᵢ` generate `U/{±1}` into the subtypes I (i), I (ii), I (iii), II (i), II (ii),
III and IV (LMFDB `nf.galois_group.gmodule_v4_type_i_i` to `nf.galois_group.gmodule_v4_type_iv`;
Mazur and Ullom split type IV further by the norms of the `eᵢ`, the LMFDB does not). This file
isolates the group theory behind the classification.

Let `e : Fin 3 → G` be a family of a torsion-free commutative group `G` whose monomials
`∏ i, e i ^ v i` (`v : Fin 3 → ℤ`) are pairwise distinct and contain every square of `G`
(`IsSquareBasis e`). Then whether `e` has a subtype `t` is decided by which monomials are squares:
`IsSquareBasis.isTypeOf_iff` says that `e` has subtype `t` exactly when the monomial of `v` is a
square for the exponent vectors `v` of the parity pattern `t.Parity` and for no others. Hence two
relabellings of `e`, even with some `eᵢ` inverted, never have different subtypes
(`IsSquareBasis.eq_of_isTypeOf`), and some relabelling of `e` has a subtype unless all of
`e₀, e₁, e₂` are squares (`IsSquareBasis.exists_isTypeOf_comp`). The finitely many parity
patterns are compared by `decide`.

## Main definitions

* `NumberField.Units.MazurUllomType`: the seven subtypes of Mazur and Ullom.
* `NumberField.Units.MazurUllomType.IsTypeOf`: a family `e₀, e₁, e₂` has subtype `t`, in the words
  of the knowls (for type II (i): `√(e₀e₁), e₁, e₂` generate the group).
* `NumberField.Units.MazurUllomType.Parity`: the parity pattern of the subtype `t`, the exponent
  vectors of the monomials that are squares.
* `NumberField.Units.MazurUllomType.IsSquareBasis`: the monomials of `e` are pairwise distinct and
  contain every square.

## Main results

* `NumberField.Units.MazurUllomType.IsSquareBasis.isTypeOf_iff`: `e` has subtype `t` iff its
  monomials that are squares are those of the parity pattern of `t`.
* `NumberField.Units.MazurUllomType.IsSquareBasis.eq_of_isTypeOf`: relabellings of `e`, with some
  of its elements inverted, have the same subtype.
* `NumberField.Units.MazurUllomType.IsSquareBasis.exists_isTypeOf_comp`: unless `e₀, e₁, e₂` are
  all squares, some relabelling of `e` has a subtype.
* `NumberField.Units.MazurUllomType.IsSquareBasis.of_monoidHom`: a criterion for `IsSquareBasis`
  through three endomorphisms, which the Galois group of a real biquadratic field provides.

## References

* M. Mazur and S. V. Ullom, *Galois module structure of units in real biquadratic number fields*,
  Acta Arith. 111 (2004), 105–124.
* T. Kubota, *Über den bizyklischen biquadratischen Zahlkörper*, Nagoya Math. J. 10 (1956), 65–85.
-/

open Equiv Finset

open Additive (ofMul)

@[to_additive]
lemma Subgroup.mem_closure_triple {C : Type*} [CommGroup C] {x y z w : C} :
    w ∈ closure ({x, y, z} : Set C) ↔ ∃ a b c : ℤ, x ^ a * y ^ b * z ^ c = w := by
  rw [← Set.singleton_union, closure_union, mem_sup]
  simp_rw [mem_closure_singleton, mem_closure_pair, exists_exists_eq_and]
  exact ⟨fun ⟨a, _, ⟨b, c, rfl⟩, h⟩ ↦ ⟨a, b, c, by rw [mul_assoc, h]⟩,
    fun ⟨a, b, c, h⟩ ↦ ⟨a, _, ⟨b, c, rfl⟩, by rw [← mul_assoc, h]⟩⟩

namespace NumberField.Units

/-- The seven subtypes of the units of a real biquadratic field in the LMFDB's notation, after
Mazur and Ullom (who split type IV further by the norms of the `eᵢ`): they describe how square
roots of products of fundamental units `e₀, e₁, e₂` of the three quadratic subfields generate the
units modulo `±1` (the knowls' `e₁, e₂, e₃`). -/
inductive MazurUllomType
  /-- Type I (i): `e₀, e₁, e₂` generate. -/
  | I₁
  /-- Type I (ii): `√e₀, e₁, e₂` generate. -/
  | I₂
  /-- Type I (iii): `√e₀, √e₁, e₂` generate. -/
  | I₃
  /-- Type II (i): `√(e₀e₁), e₁, e₂` generate. -/
  | II₁
  /-- Type II (ii): `√(e₀e₁), e₁, √e₂` generate. -/
  | II₂
  /-- Type III: `√(e₀e₁), √(e₁e₂), √(e₂e₀)` generate. -/
  | III
  /-- Type IV: `√(e₀e₁e₂), e₁, e₂` generate. -/
  | IV
  deriving DecidableEq

namespace MazurUllomType

variable (t : MazurUllomType) {v w : Fin 3 → ℤ}

instance : Fintype MazurUllomType :=
  ⟨{I₁, I₂, I₃, II₁, II₂, III, IV}, fun t ↦ by cases t <;> decide⟩

/-- The parity pattern of the subtype `t`: the exponent vectors `v` for which the monomial
`e₀ ^ v₀ * e₁ ^ v₁ * e₂ ^ v₂` is a square, when `e` has subtype `t` (`IsSquareBasis.isTypeOf_iff`).
It depends only on the parities of `v₀, v₁, v₂`. -/
def Parity : MazurUllomType → (Fin 3 → ℤ) → Prop
  | I₁, v => 2 ∣ v 0 ∧ 2 ∣ v 1 ∧ 2 ∣ v 2
  | I₂, v => 2 ∣ v 1 ∧ 2 ∣ v 2
  | I₃, v => 2 ∣ v 2
  | II₁, v => 2 ∣ v 0 - v 1 ∧ 2 ∣ v 2
  | II₂, v => 2 ∣ v 0 - v 1
  | III, v => 2 ∣ v 0 + v 1 + v 2
  | IV, v => 2 ∣ v 0 - v 1 ∧ 2 ∣ v 1 - v 2

instance : Decidable (t.Parity v) := by
  cases t <;> unfold Parity <;> infer_instance

lemma parity_congr (h : ∀ i, 2 ∣ v i - w i) : t.Parity v ↔ t.Parity w := by
  have h₀ : 2 ∣ v 0 - w 0 := h 0
  have h₁ : 2 ∣ v 1 - w 1 := h 1
  have h₂ : 2 ∣ v 2 - w 2 := h 2
  cases t <;> simp only [Parity] <;> omega

/-- The exponent vectors of the squares of the three generators of the subtype `t`, in the order
of `IsTypeOf`: for type II (i), the generators `√(e₀e₁), e₁, e₂` have squares with exponent
vectors `(1, 1, 0), (0, 2, 0), (0, 0, 2)`. -/
def sqExponents : MazurUllomType → Fin 3 → Fin 3 → ℤ
  | I₁ => ![![2, 0, 0], ![0, 2, 0], ![0, 0, 2]]
  | I₂ => ![![1, 0, 0], ![0, 2, 0], ![0, 0, 2]]
  | I₃ => ![![1, 0, 0], ![0, 1, 0], ![0, 0, 2]]
  | II₁ => ![![1, 1, 0], ![0, 2, 0], ![0, 0, 2]]
  | II₂ => ![![1, 1, 0], ![0, 2, 0], ![0, 0, 1]]
  | III => ![![1, 1, 0], ![0, 1, 1], ![1, 0, 1]]
  | IV => ![![1, 1, 1], ![0, 2, 0], ![0, 0, 2]]

variable (v) in
lemma parity_iff_exists : t.Parity v ↔ ∃ a b c : ℤ, v = a • t.sqExponents 0 + b • t.sqExponents 1 +
    c • t.sqExponents 2 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · cases t <;> simp only [Parity] at h
    · refine ⟨v 0 / 2, v 1 / 2, v 2 / 2, funext fun i ↦ ?_⟩
      fin_cases i <;> simp [sqExponents] <;> omega
    · refine ⟨v 0, v 1 / 2, v 2 / 2, funext fun i ↦ ?_⟩
      fin_cases i <;> simp [sqExponents] <;> omega
    · refine ⟨v 0, v 1, v 2 / 2, funext fun i ↦ ?_⟩
      fin_cases i <;> simp [sqExponents]
      omega
    · refine ⟨v 0, (v 1 - v 0) / 2, v 2 / 2, funext fun i ↦ ?_⟩
      fin_cases i <;> simp [sqExponents] <;> omega
    · refine ⟨v 0, (v 1 - v 0) / 2, v 2, funext fun i ↦ ?_⟩
      fin_cases i <;> simp [sqExponents]
      omega
    · refine ⟨(v 0 + v 1 - v 2) / 2, (v 1 + v 2 - v 0) / 2, (v 0 + v 2 - v 1) / 2,
        funext fun i ↦ ?_⟩
      fin_cases i <;> simp [sqExponents] <;> omega
    · refine ⟨v 0, (v 1 - v 0) / 2, (v 2 - v 0) / 2, funext fun i ↦ ?_⟩
      fin_cases i <;> simp [sqExponents] <;> omega
  · rintro ⟨a, b, c, rfl⟩
    cases t <;> simp [Parity, sqExponents] <;> omega

/-- The index `u₀ + 2 u₁ + 4 u₂` of a vector `u` of parities. -/
def parityIndex (u : Fin 3 → Fin 2) : Fin 8 :=
  ⟨u 0 + 2 * u 1 + 4 * u 2, by omega⟩

/-- The vector of parities of index `k`, the inverse of `parityIndex`. -/
def parityVector (k : Fin 8) : Fin 3 → Fin 2 :=
  ![⟨k % 2, by omega⟩, ⟨k / 2 % 2, by omega⟩, ⟨k / 4 % 2, by omega⟩]

lemma parityVector_parityIndex : ∀ u : Fin 3 → Fin 2, parityVector (parityIndex u) = u := by
  decide

lemma eq_of_forall_parity_iff : ∀ (t t' : MazurUllomType) (π : Perm (Fin 3)), (∀ u : Fin 3 → Fin 2,
    t'.Parity (fun i ↦ (u i : ℤ)) ↔ t.Parity (fun i ↦ (u (π.symm i) : ℤ))) → t = t' := by
  decide +kernel

lemma exists_parity_iff_of_closed : ∀ B : Fin 8 → Bool, B 0 = true → (∀ u u' : Fin 3 → Fin 2,
    B (parityIndex u) = true → B (parityIndex u') = true → B (parityIndex (u + u')) = true) →
    ¬(B 1 = true ∧ B 2 = true ∧ B 4 = true) → ∃ (t : MazurUllomType) (π : Perm (Fin 3)),
    ∀ u : Fin 3 → Fin 2, B (parityIndex (u ∘ π.symm)) = true ↔ t.Parity (fun i ↦ (u i : ℤ)) := by
  decide +kernel

variable {G : Type*} [CommGroup G]

/-- A family `e₀, e₁, e₂` of a commutative group has the subtype `t` of Mazur and Ullom: the
elements that `t` names (for type II (i) an element `x` with `x ^ 2 = e₀ * e₁`, with `e₁` and
`e₂`) generate the group. These are the conditions of the predicates `IsMazurUllomTypeI₁` to
`IsMazurUllomTypeIV` on the classes of a frame of quadratic units. -/
def IsTypeOf : MazurUllomType → (Fin 3 → G) → Prop
  | I₁, e => Subgroup.closure {e 0, e 1, e 2} = ⊤
  | I₂, e => ∃ x, x ^ 2 = e 0 ∧ Subgroup.closure {x, e 1, e 2} = ⊤
  | I₃, e => ∃ x y, x ^ 2 = e 0 ∧ y ^ 2 = e 1 ∧ Subgroup.closure {x, y, e 2} = ⊤
  | II₁, e => ∃ x, x ^ 2 = e 0 * e 1 ∧ Subgroup.closure {x, e 1, e 2} = ⊤
  | II₂, e => ∃ x y, x ^ 2 = e 0 * e 1 ∧ y ^ 2 = e 2 ∧ Subgroup.closure {x, e 1, y} = ⊤
  | III, e => ∃ x y z, x ^ 2 = e 0 * e 1 ∧ y ^ 2 = e 1 * e 2 ∧ z ^ 2 = e 2 * e 0 ∧
      Subgroup.closure {x, y, z} = ⊤
  | IV, e => ∃ x, x ^ 2 = e 0 * e 1 * e 2 ∧ Subgroup.closure {x, e 1, e 2} = ⊤

/-- The monomials `∏ i, e i ^ v i` of a family `e₀, e₁, e₂` are pairwise distinct and contain
every square: `e` is a basis of a subgroup that contains the squares of `G`, which then has index
dividing `8` if `G` is torsion-free. Fundamental units of the quadratic subfields of a real
biquadratic field have this property in the units modulo `±1`. -/
structure IsSquareBasis (e : Fin 3 → G) : Prop where
  /-- Every square is a monomial in `e₀, e₁, e₂`. -/
  exists_sq_eq (x : G) : ∃ u : Fin 3 → ℤ, x ^ 2 = ∏ i, e i ^ u i
  /-- The elements `e₀, e₁, e₂` are independent. -/
  eq_zero_of_prod_eq_one {u : Fin 3 → ℤ} : ∏ i, e i ^ u i = 1 → u = 0

variable {e e' : Fin 3 → G} {π : Perm (Fin 3)}

lemma prod_zpow_add : ∏ i, e i ^ (v + w) i = (∏ i, e i ^ v i) * ∏ i, e i ^ w i := by
  simp only [Pi.add_apply, zpow_add, prod_mul_distrib]

lemma prod_zpow_smul (n : ℤ) : ∏ i, e i ^ (n • v) i = (∏ i, e i ^ v i) ^ n := by
  simp only [Pi.smul_apply, smul_eq_mul, mul_comm n, zpow_mul, prod_zpow]

lemma prod_zpow_sub : ∏ i, e i ^ (v - w) i = (∏ i, e i ^ v i) / ∏ i, e i ^ w i := by
  simp only [Pi.sub_apply, zpow_sub, prod_mul_distrib, prod_inv_distrib, div_eq_mul_inv]

lemma prod_zpow_vec (a b c : ℤ) : ∏ i, e i ^ ![a, b, c] i = e 0 ^ a * e 1 ^ b * e 2 ^ c := by
  simp [Fin.prod_univ_three]

variable (π) in
lemma prod_comp_perm : ∏ i, e (π i) ^ v i = ∏ i, e i ^ v (π.symm i) :=
  Eq.trans (by simp) (Equiv.prod_comp π fun i ↦ e i ^ v (π.symm i))

lemma isSquare_prod_iff_of_dvd_sub (h : ∀ i, 2 ∣ v i - w i) :
    IsSquare (∏ i, e i ^ v i) ↔ IsSquare (∏ i, e i ^ w i) := by
  choose c hc using h
  have hv : v = w + (2 : ℤ) • c := by
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hc i]
  rw [hv, prod_zpow_add, prod_zpow_smul, zpow_two]
  exact ⟨fun h ↦ by simpa using h.div (IsSquare.mul_self (∏ i, e i ^ c i)),
    fun h ↦ h.mul (IsSquare.mul_self _)⟩

lemma isSquare_prod_iff_of_forall_eq (hπ : ∀ i, e' i = e (π i) ∨ e' i = (e (π i))⁻¹) :
    IsSquare (∏ i, e' i ^ v i) ↔ IsSquare (∏ i, e i ^ v (π.symm i)) := by
  have hs (i : Fin 3) : ∃ s : ℤ, 2 ∣ s - 1 ∧ e' i = e (π i) ^ s := by
    rcases hπ i with h | h
    · exact ⟨1, by norm_num, by rw [h, zpow_one]⟩
    · exact ⟨-1, by norm_num, by rw [h, zpow_neg_one]⟩
  choose s hs hs' using hs
  have h : ∏ i, e' i ^ v i = ∏ i, (e ∘ π) i ^ (s * v) i := by
    simp only [hs', Function.comp_apply, Pi.mul_apply, zpow_mul]
  rw [h, isSquare_prod_iff_of_dvd_sub (w := v) fun i ↦ ?_]
  · exact iff_of_eq (congrArg IsSquare (prod_comp_perm π))
  · rcases hs i with ⟨k, hk⟩
    exact ⟨k * v i, by simp only [Pi.mul_apply]; linear_combination v i * hk⟩

namespace IsSquareBasis

lemma eq_of_prod_eq (he : IsSquareBasis e) (h : ∏ i, e i ^ v i = ∏ i, e i ^ w i) : v = w :=
  sub_eq_zero.mp <| he.eq_zero_of_prod_eq_one <| by rw [prod_zpow_sub, h, div_self']

variable (π) in
lemma comp_perm (he : IsSquareBasis e) : IsSquareBasis (e ∘ π) where
  exists_sq_eq w := by
    rcases he.exists_sq_eq w with ⟨v, hv⟩
    exact ⟨v ∘ π, hv.trans (Equiv.prod_comp π fun i ↦ e i ^ v i).symm⟩
  eq_zero_of_prod_eq_one {v} h := by
    have h' : (fun i ↦ v (π.symm i)) = 0 :=
      he.eq_zero_of_prod_eq_one ((prod_comp_perm π).symm.trans h)
    funext i
    simpa using congrFun h' (π i)

/-- **A criterion for a square basis**: let `φ₀, φ₁, φ₂` be endomorphisms of `G` such that `φᵢ`
fixes `eᵢ` and inverts the other two, `w * φᵢ w` is a power of `eᵢ` and
`w * φ₀ w * φ₁ w * φ₂ w = 1` for every `w`, and no `eᵢ` has finite order. Then `e` is a square
basis. For the units of a real biquadratic field, `φᵢ` is the automorphism fixing the `i`-th
quadratic subfield, `w * φᵢ w` the norm to that subfield and `w * φ₀ w * φ₁ w * φ₂ w` the norm to
`ℚ`. -/
lemma of_monoidHom (φ : Fin 3 → G →* G) (hfix : ∀ i, φ i (e i) = e i)
    (hinv : ∀ i j, i ≠ j → e j * φ i (e j) = 1) (hne : ∀ i (n : ℤ), e i ^ n = 1 → n = 0)
    (hnorm : ∀ i w, ∃ n : ℤ, w * φ i w = e i ^ n) (hprod : ∀ w, w * φ 0 w * φ 1 w * φ 2 w = 1) :
    IsSquareBasis e where
  exists_sq_eq w := by
    rcases hnorm 0 w with ⟨a, ha⟩
    rcases hnorm 1 w with ⟨b, hb⟩
    rcases hnorm 2 w with ⟨c, hc⟩
    refine ⟨![a, b, c], ?_⟩
    rw [prod_zpow_vec]
    have ha' : ofMul w + ofMul (φ 0 w) = a • ofMul (e 0) := ha
    have hb' : ofMul w + ofMul (φ 1 w) = b • ofMul (e 1) := hb
    have hc' : ofMul w + ofMul (φ 2 w) = c • ofMul (e 2) := hc
    have hw : ofMul w + ofMul (φ 0 w) + ofMul (φ 1 w) + ofMul (φ 2 w) = 0 := hprod w
    exact (by linear_combination (norm := module) ha' + hb' + hc' - hw :
      2 • ofMul w = a • ofMul (e 0) + b • ofMul (e 1) + c • ofMul (e 2))
  eq_zero_of_prod_eq_one {v} h := by
    funext i
    have h' : ∏ j, (e j * φ i (e j)) ^ v j = 1 := by
      simp only [mul_zpow, prod_mul_distrib, ← map_zpow, ← map_prod, h, map_one, mul_one]
    rw [Fintype.prod_eq_single i fun j hj ↦ by rw [hinv i j hj.symm, one_zpow], hfix, ← sq,
      ← zpow_natCast, ← zpow_mul] at h'
    have h2 : (2 : ℕ) * v i = 0 := hne i _ h'
    simp only [Pi.zero_apply]
    omega

variable [IsMulTorsionFree G]

lemma closure_eq_top_iff (he : IsSquareBasis e) {g₁ g₂ g₃ : G} {V₁ V₂ V₃ : Fin 3 → ℤ}
    (h₁ : g₁ ^ 2 = ∏ i, e i ^ V₁ i) (h₂ : g₂ ^ 2 = ∏ i, e i ^ V₂ i) (h₃ : g₃ ^ 2 = ∏ i, e i ^ V₃ i)
    {R : (Fin 3 → ℤ) → Prop} (hR : ∀ v, R v ↔ ∃ a b c : ℤ, v = a • V₁ + b • V₂ + c • V₃) :
    Subgroup.closure {g₁, g₂, g₃} = ⊤ ↔ ∀ v, IsSquare (∏ i, e i ^ v i) ↔ R v := by
  have key (a b c : ℤ) :
      ∏ i, e i ^ (a • V₁ + b • V₂ + c • V₃) i = (g₁ ^ a * g₂ ^ b * g₃ ^ c) ^ 2 := by
    rw [prod_zpow_add, prod_zpow_add, prod_zpow_smul, prod_zpow_smul, prod_zpow_smul, ← h₁, ← h₂,
      ← h₃]
    exact Additive.ofMul.injective <| by simp only [ofMul_mul, ofMul_pow, ofMul_zpow]; module
  refine ⟨fun hcl v ↦ ⟨fun ⟨r, hr⟩ ↦ ?_, fun hv ↦ ?_⟩, fun h ↦ ?_⟩
  · rcases Subgroup.mem_closure_triple.mp (hcl ▸ Subgroup.mem_top r) with ⟨a, b, c, rfl⟩
    exact (hR v).mpr ⟨a, b, c, he.eq_of_prod_eq (by rw [hr, key, sq])⟩
  · rcases (hR v).mp hv with ⟨a, b, c, rfl⟩
    exact ⟨_, (key a b c).trans (sq _)⟩
  · refine eq_top_iff.mpr fun w _ ↦ ?_
    rcases he.exists_sq_eq w with ⟨v, hv⟩
    rcases (hR v).mp ((h v).mp ⟨w, hv.symm.trans (sq w)⟩) with ⟨a, b, c, rfl⟩
    exact Subgroup.mem_closure_triple.mpr ⟨a, b, c,
      eq_of_pow_eq_pow_of_commute two_ne_zero (.all _ _) ((key a b c).symm.trans hv.symm)⟩

/-- **The subtype of `e` is decided by its square monomials**: if `e` is a square basis of a
torsion-free group, `e` has the subtype `t` iff the monomial `∏ i, e i ^ v i` is a square exactly
for the exponent vectors `v` of the parity pattern of `t`. -/
lemma isTypeOf_iff (he : IsSquareBasis e) :
    t.IsTypeOf e ↔ ∀ v, IsSquare (∏ i, e i ^ v i) ↔ t.Parity v := by
  have h₀ : e 0 ^ 2 = ∏ i, e i ^ ![(2 : ℤ), 0, 0] i := by
    rw [prod_zpow_vec]
    simp
  have h₁ : e 1 ^ 2 = ∏ i, e i ^ ![(0 : ℤ), 2, 0] i := by
    rw [prod_zpow_vec]
    simp
  have h₂ : e 2 ^ 2 = ∏ i, e i ^ ![(0 : ℤ), 0, 2] i := by
    rw [prod_zpow_vec]
    simp
  have hsq {x : G} {a b c : ℤ} (h : x ^ 2 = e 0 ^ a * e 1 ^ b * e 2 ^ c) :
      x ^ 2 = ∏ i, e i ^ ![a, b, c] i := by
    rw [prod_zpow_vec, h]
  have hroot {a b c : ℤ} (h : IsSquare (∏ i, e i ^ ![a, b, c] i)) :
      ∃ x : G, x ^ 2 = e 0 ^ a * e 1 ^ b * e 2 ^ c := by
    rcases h with ⟨r, hr⟩
    exact ⟨r, by rw [sq, ← hr, prod_zpow_vec]⟩
  cases t
  · exact he.closure_eq_top_iff h₀ h₁ h₂ (parity_iff_exists I₁)
  · refine ⟨fun ⟨x, hx, hcl⟩ ↦ (he.closure_eq_top_iff (hsq (a := 1) (b := 0) (c := 0)
      (by simpa using hx)) h₁ h₂ (parity_iff_exists I₂)).mp hcl, fun h ↦ ?_⟩
    rcases hroot ((h ![1, 0, 0]).mpr (by decide)) with ⟨x, hx⟩
    exact ⟨x, by simpa using hx,
      (he.closure_eq_top_iff (hsq hx) h₁ h₂ (parity_iff_exists I₂)).mpr h⟩
  · refine ⟨fun ⟨x, y, hx, hy, hcl⟩ ↦ (he.closure_eq_top_iff (hsq (a := 1) (b := 0) (c := 0)
      (by simpa using hx)) (hsq (a := 0) (b := 1) (c := 0) (by simpa using hy)) h₂
      (parity_iff_exists I₃)).mp hcl, fun h ↦ ?_⟩
    rcases hroot ((h ![1, 0, 0]).mpr (by decide)) with ⟨x, hx⟩
    rcases hroot ((h ![0, 1, 0]).mpr (by decide)) with ⟨y, hy⟩
    exact ⟨x, y, by simpa using hx, by simpa using hy,
      (he.closure_eq_top_iff (hsq hx) (hsq hy) h₂ (parity_iff_exists I₃)).mpr h⟩
  · refine ⟨fun ⟨x, hx, hcl⟩ ↦ (he.closure_eq_top_iff (hsq (a := 1) (b := 1) (c := 0)
      (by simpa using hx)) h₁ h₂ (parity_iff_exists II₁)).mp hcl, fun h ↦ ?_⟩
    rcases hroot ((h ![1, 1, 0]).mpr (by decide)) with ⟨x, hx⟩
    exact ⟨x, by simpa using hx,
      (he.closure_eq_top_iff (hsq hx) h₁ h₂ (parity_iff_exists II₁)).mpr h⟩
  · refine ⟨fun ⟨x, y, hx, hy, hcl⟩ ↦ (he.closure_eq_top_iff (hsq (a := 1) (b := 1) (c := 0)
      (by simpa using hx)) h₁ (hsq (a := 0) (b := 0) (c := 1) (by simpa using hy))
      (parity_iff_exists II₂)).mp hcl, fun h ↦ ?_⟩
    rcases hroot ((h ![1, 1, 0]).mpr (by decide)) with ⟨x, hx⟩
    rcases hroot ((h ![0, 0, 1]).mpr (by decide)) with ⟨y, hy⟩
    exact ⟨x, y, by simpa using hx, by simpa using hy,
      (he.closure_eq_top_iff (hsq hx) h₁ (hsq hy) (parity_iff_exists II₂)).mpr h⟩
  · refine ⟨fun ⟨x, y, z, hx, hy, hz, hcl⟩ ↦ (he.closure_eq_top_iff
      (hsq (a := 1) (b := 1) (c := 0) (by simpa using hx))
      (hsq (a := 0) (b := 1) (c := 1) (by simpa using hy))
      (hsq (a := 1) (b := 0) (c := 1) (by simpa [mul_comm] using hz))
      (parity_iff_exists III)).mp hcl, fun h ↦ ?_⟩
    rcases hroot ((h ![1, 1, 0]).mpr (by decide)) with ⟨x, hx⟩
    rcases hroot ((h ![0, 1, 1]).mpr (by decide)) with ⟨y, hy⟩
    rcases hroot ((h ![1, 0, 1]).mpr (by decide)) with ⟨z, hz⟩
    exact ⟨x, y, z, by simpa using hx, by simpa using hy, by simpa [mul_comm] using hz,
      (he.closure_eq_top_iff (hsq hx) (hsq hy) (hsq hz) (parity_iff_exists III)).mpr h⟩
  · refine ⟨fun ⟨x, hx, hcl⟩ ↦ (he.closure_eq_top_iff (hsq (a := 1) (b := 1) (c := 1)
      (by simpa using hx)) h₁ h₂ (parity_iff_exists IV)).mp hcl, fun h ↦ ?_⟩
    rcases hroot ((h ![1, 1, 1]).mpr (by decide)) with ⟨x, hx⟩
    exact ⟨x, by simpa using hx,
      (he.closure_eq_top_iff (hsq hx) h₁ h₂ (parity_iff_exists IV)).mpr h⟩

variable {t} in
/-- **Relabellings of a square basis have the same subtype**: if `e'ᵢ` is `e_{π i}` or its
inverse for every `i`, and `e` has subtype `t` and `e'` has subtype `t'`, then `t = t'`. -/
lemma eq_of_isTypeOf (he : IsSquareBasis e) (he' : IsSquareBasis e')
    (hπ : ∀ i, e' i = e (π i) ∨ e' i = (e (π i))⁻¹) {t' : MazurUllomType} (ht : t.IsTypeOf e)
    (ht' : t'.IsTypeOf e') : t = t' := by
  refine eq_of_forall_parity_iff t t' π fun u ↦ ?_
  rw [← (he'.isTypeOf_iff t').mp ht', isSquare_prod_iff_of_forall_eq hπ,
    (he.isTypeOf_iff t).mp ht]

/-- **Some relabelling of a square basis has a subtype**, unless `e₀, e₁, e₂` are all squares. -/
lemma exists_isTypeOf_comp (he : IsSquareBasis e) (hne : ¬∀ i, IsSquare (e i)) :
    ∃ (t : MazurUllomType) (π : Perm (Fin 3)), t.IsTypeOf (e ∘ π) := by
  classical
  let B (k : Fin 8) : Bool := decide (IsSquare (∏ i, e i ^ ((parityVector k i : ℕ) : ℤ)))
  have hB (u : Fin 3 → Fin 2) :
      B (parityIndex u) = true ↔ IsSquare (∏ i, e i ^ ((u i : ℕ) : ℤ)) := by
    simp only [B, parityVector_parityIndex, decide_eq_true_iff]
  have hclosed (u u' : Fin 3 → Fin 2) (h : B (parityIndex u) = true)
      (h' : B (parityIndex u') = true) : B (parityIndex (u + u')) = true := by
    rw [hB] at h h' ⊢
    have hmul : IsSquare ((∏ i, e i ^ ((u i : ℕ) : ℤ)) * ∏ i, e i ^ ((u' i : ℕ) : ℤ)) :=
      h.mul h'
    rw [← prod_zpow_add] at hmul
    refine (isSquare_prod_iff_of_dvd_sub fun i ↦ ?_).mp hmul
    have hval : ((u i + u' i : Fin 2) : ℕ) = ((u i : ℕ) + u' i) % 2 := Fin.val_add (u i) (u' i)
    simp only [Pi.add_apply]
    omega
  have hnot : ¬(B 1 = true ∧ B 2 = true ∧ B 4 = true) := by
    rintro ⟨h₁, h₂, h₄⟩
    have h₁' : IsSquare (∏ i, e i ^ ((![1, 0, 0] i : ℕ) : ℤ)) := (hB ![1, 0, 0]).mp h₁
    have h₂' : IsSquare (∏ i, e i ^ ((![0, 1, 0] i : ℕ) : ℤ)) := (hB ![0, 1, 0]).mp h₂
    have h₄' : IsSquare (∏ i, e i ^ ((![0, 0, 1] i : ℕ) : ℤ)) := (hB ![0, 0, 1]).mp h₄
    simp [Fin.prod_univ_three] at h₁' h₂' h₄'
    refine hne fun i ↦ ?_
    fin_cases i <;> assumption
  rcases exists_parity_iff_of_closed B ((hB 0).mpr (by simp)) hclosed hnot with ⟨t, π, h⟩
  refine ⟨t, π, ((he.comp_perm π).isTypeOf_iff t).mpr fun v ↦ ?_⟩
  let u : Fin 3 → Fin 2 := fun i ↦ if 2 ∣ v i then 0 else 1
  have hu (i : Fin 3) : 2 ∣ v i - ((u i : ℕ) : ℤ) := by
    simp only [u]
    split_ifs with hv <;> simp <;> omega
  rw [t.parity_congr hu, ← h u, hB]
  simp only [Function.comp_apply]
  rw [prod_comp_perm]
  exact isSquare_prod_iff_of_dvd_sub fun i ↦ hu (π.symm i)

end IsSquareBasis

end MazurUllomType

end NumberField.Units
