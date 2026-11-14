import LeanBridge.ForMathlib.NumberTheory.NumberField.Units.MazurUllomType
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.RepresentationTheory.Intertwining

/-!
# The four Galois modules of Mazur and Ullom

Mazur and Ullom sort the units `U` of a real biquadratic field `K`, modulo `±1`, as a module over
the group ring `ℤ[V₄]` of its Galois group `V₄`, into four basic types I–IV, each the union of some
of the seven subtypes of Kubota's list (`NumberField.Units.MazurUllomType.basicType`). This file
defines a `ℤ[V₄]`-module for each basic type and proves that the four are pairwise non-isomorphic,
even after an automorphism of `V₄` (Mazur and Ullom, Remark 1). It also proves the group theory
behind their Theorem 1, by which the units of a field of each basic type are isomorphic to the
module of that type (`Units/BiquadraticGaloisModule.lean`).

We take `V₄ = ℤˣ × ℤˣ`, with nontrivial elements `σ₀ = (1, -1)`, `σ₁ = (-1, 1)`, `σ₂ = (-1, -1)`
and nontrivial characters `χ₀ (a, b) = a`, `χ₁ (a, b) = b`, `χ₂ (a, b) = a b`, so that `χⱼ σᵢ` is
`1` for `i = j` and `-1` otherwise. Mazur and Ullom's `Aⱼ` is `ℤ` with `V₄` acting through `χⱼ`,
and each of the four modules is a sublattice of `A₀ ⊕ A₁ ⊕ A₂ = ℤ³`, on which `g` multiplies the
`j`-th coordinate by `χⱼ g`:
* type I: `ℤ³ = A₀ ⊕ A₁ ⊕ A₂`;
* type II: `{v | v₀ ≡ v₁ mod 2} = B₂ ⊕ A₂`, where `B₂` has the basis `(1, 1, 0)`, `(1, -1, 0)`;
* type III: `{v | v₀ + v₁ + v₂ ≡ 0 mod 2}`, isomorphic to the augmentation ideal of `ℤ[V₄]`;
* type IV: `{v | v₀ ≡ v₁ ≡ v₂ mod 2}`, isomorphic to `ℤ[V₄]/(ν)` for `ν = Σ_{g ∈ V₄} g`.
The last three descriptions are proved in `Units/MazurUllomModuleGroupRing.lean`.

The vectors of the module of type `T` fixed by `σᵢ` are the multiples of `mᵢ eᵢ`, for
`m = (1, 1, 1)`, `(2, 2, 1)`, `(2, 2, 2)`, `(2, 2, 2)` as `T` is I, II, III or IV, and the vector
`(mᵢ wᵢ)ᵢ` is twice an element of the module exactly when `w` lies in the parity pattern of the
subtype I (i), II (i), III or IV respectively. An isomorphism, even twisted by an automorphism of
`V₄`, maps fixed vectors to fixed vectors, so it preserves this pattern up to a permutation of the
indices, and the patterns of the four subtypes are not permutations of each other.

For Theorem 1: if `e` is a square basis of a torsion-free group `G` (every square is a product
`∏ i, e i ^ vᵢ`, and these products are distinct) with subtype `t`, then `x ↦ v`, where
`x ^ 2 = ∏ i, (e i ^ sᵢ) ^ vᵢ` for the rescaling `s = t.scale`, is an isomorphism of `G` onto the
module of the basic type of `t`. An endomorphism of `G` acting on each `e i` by a sign becomes the
diagonal action of these signs.

## Main definitions

* `NumberField.Units.MazurUllomBasicType`: the four basic types I–IV.
* `NumberField.Units.MazurUllomType.basicType`: the basic type of a subtype.
* `NumberField.Units.MazurUllomBasicType.kleinChar`: the characters `χ₀, χ₁, χ₂` of `ℤˣ × ℤˣ`.
* `NumberField.Units.MazurUllomBasicType.kleinSigma`: its nontrivial elements `σ₀, σ₁, σ₂`.
* `NumberField.Units.MazurUllomBasicType.charSumRep`: the `ℤ[V₄]`-module `A₀ ⊕ A₁ ⊕ A₂ = ℤ³`.
* `NumberField.Units.MazurUllomBasicType.lattice`: the lattice of `ℤ³` of a basic type.
* `NumberField.Units.MazurUllomBasicType.rep`: the `ℤ[V₄]`-module of a basic type.
* `NumberField.Units.MazurUllomType.IsSquareBasis.sqVecEquiv`: the isomorphism `x ↦ v` above.

## Main results

* `NumberField.Units.MazurUllomBasicType.eq_of_equiv`: **the four modules are pairwise
  non-isomorphic, even after an automorphism of `V₄`** (Mazur and Ullom, Remark 1).
* `NumberField.Units.MazurUllomBasicType.eq_of_equiv_comp`: the same for the four modules pulled
  back to a group `G` along isomorphisms `G ≃* V₄`, the form used for Galois groups.

## References

* M. Mazur and S. V. Ullom, *Galois module structure of units in real biquadratic number fields*,
  Acta Arith. 111 (2004), 105–124.
-/

open Equiv

namespace NumberField.Units

/-- The four **basic types** I–IV of Mazur and Ullom for the units `U` of a real biquadratic field:
the isomorphism classes of `U/{±1}` as a module over the group ring of the Galois group, up to an
automorphism of the Galois group. Each is the union of some of the seven subtypes
(`MazurUllomType.basicType`). -/
inductive MazurUllomBasicType
  /-- Type I: the subtypes I (i), I (ii) and I (iii). -/
  | I
  /-- Type II: the subtypes II (i) and II (ii). -/
  | II
  /-- Type III. -/
  | III
  /-- Type IV. -/
  | IV
  deriving DecidableEq

/-- The basic type I, II, III or IV of a subtype: the roman numeral of its name. -/
def MazurUllomType.basicType : MazurUllomType → MazurUllomBasicType
  | .I₁ | .I₂ | .I₃ => .I
  | .II₁ | .II₂ => .II
  | .III => .III
  | .IV => .IV

namespace MazurUllomBasicType

variable (T : MazurUllomBasicType) {T' : MazurUllomBasicType} {v w : Fin 3 → ℤ} (i j : Fin 3)
  (g : ℤˣ × ℤˣ) (n : ℤ)

/-- The subtype I (i), II (i), III or IV of the basic type `T`: the subtype of the generators of the
lattices fixed by `σ₀`, `σ₁` and `σ₂` in the module of type `T`. -/
def toType : MazurUllomBasicType → MazurUllomType
  | I => .I₁
  | II => .II₁
  | III => .III
  | IV => .IV

lemma basicType_toType : T.toType.basicType = T := by
  cases T <;> rfl

/-- The congruences modulo `2` cutting out the module of the basic type `T` in `ℤ³`: none for type
I, `v₀ ≡ v₁` for type II, `v₀ + v₁ + v₂ ≡ 0` for type III and `v₀ ≡ v₁ ≡ v₂` for type IV. -/
def Cond : MazurUllomBasicType → (Fin 3 → ℤ) → Prop
  | I, _ => True
  | II, u => 2 ∣ u 0 - u 1
  | III, u => 2 ∣ u 0 + u 1 + u 2
  | IV, u => 2 ∣ u 0 - u 1 ∧ 2 ∣ u 1 - u 2

lemma cond_congr (h : ∀ i, 2 ∣ v i - w i) : T.Cond v ↔ T.Cond w := by
  have h₀ : 2 ∣ v 0 - w 0 := h 0
  have h₁ : 2 ∣ v 1 - w 1 := h 1
  have h₂ : 2 ∣ v 2 - w 2 := h 2
  cases T <;> simp only [Cond] <;> omega

/-- The lattice of `ℤ³` of the basic type `T`: the vectors satisfying the congruences `T.Cond`. -/
def lattice : Submodule ℤ (Fin 3 → ℤ) :=
  AddSubgroup.toIntSubmodule
    { carrier := {u | T.Cond u}
      add_mem' := fun {a b} ha hb ↦ by
        cases T <;> simp only [Cond, Set.mem_ofPred_eq, Pi.add_apply] at ha hb ⊢ <;> omega
      zero_mem' := by
        cases T <;> simp [Cond]
      neg_mem' := fun {a} ha ↦ by
        cases T <;> simp only [Cond, Set.mem_ofPred_eq, Pi.neg_apply] at ha ⊢ <;> omega }

lemma mem_lattice : v ∈ T.lattice ↔ T.Cond v :=
  Iff.rfl

variable {u : T.lattice}

/-- The nontrivial characters `χ₀, χ₁, χ₂` of the Klein four-group `V₄ = ℤˣ × ℤˣ`:
`χ₀ (a, b) = a`, `χ₁ (a, b) = b` and `χ₂ (a, b) = a b`. -/
def kleinChar : Fin 3 → ℤˣ × ℤˣ →* ℤˣ :=
  ![MonoidHom.fst ℤˣ ℤˣ, MonoidHom.snd ℤˣ ℤˣ, MonoidHom.fst ℤˣ ℤˣ * MonoidHom.snd ℤˣ ℤˣ]

/-- The nontrivial elements `σ₀ = (1, -1)`, `σ₁ = (-1, 1)` and `σ₂ = (-1, -1)` of the Klein
four-group `V₄ = ℤˣ × ℤˣ`, labelled so that `χᵢ σᵢ = 1`. -/
def kleinSigma : Fin 3 → ℤˣ × ℤˣ :=
  ![(1, -1), (-1, 1), (-1, -1)]

lemma kleinChar_kleinSigma : ∀ i j, kleinChar j (kleinSigma i) = if i = j then 1 else -1 := by
  decide

lemma eq_one_or_exists_kleinSigma : ∀ g : ℤˣ × ℤˣ, g = 1 ∨ ∃ i, kleinSigma i = g := by
  decide

lemma kleinSigma_injective : Function.Injective kleinSigma := by
  decide

lemma kleinSigma_ne_one : ∀ i, kleinSigma i ≠ 1 := by
  decide

lemma bijective_elim_kleinSigma :
    Function.Bijective fun o : Option (Fin 3) ↦ o.elim (1 : ℤˣ × ℤˣ) kleinSigma := by
  decide

instance : IsKleinFour (ℤˣ × ℤˣ) where
  card_four := by
    simp
  exponent_two := by
    have : Nontrivial (ℤˣ × ℤˣ) := ⟨⟨1, (-1, 1), by decide⟩⟩
    exact (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun g hg ↦
      orderOf_eq_prime (Prod.ext (Int.units_sq g.1) (Int.units_sq g.2)) hg

/-- The `ℤ[V₄]`-module `A₀ ⊕ A₁ ⊕ A₂ = ℤ³` for `V₄ = ℤˣ × ℤˣ`: `g` multiplies the `j`-th coordinate
by `χⱼ g`. Mazur and Ullom's `Aⱼ` is `ℤ` with `σⱼ` acting trivially and the two other nontrivial
elements by `-1`, that is with `V₄` acting through `χⱼ`. -/
def charSumRep : Representation ℤ (ℤˣ × ℤˣ) (Fin 3 → ℤ) where
  toFun g := LinearMap.pi fun j ↦ (kleinChar j g : ℤ) • LinearMap.proj j
  map_one' := LinearMap.ext fun v ↦ funext fun j ↦ by simp
  map_mul' g h := LinearMap.ext fun v ↦ funext fun j ↦ by simp [mul_assoc]

lemma charSumRep_apply : charSumRep g v j = kleinChar j g * v j :=
  rfl

lemma cond_charSumRep (hv : T.Cond v) : T.Cond (charSumRep g v) := by
  refine (T.cond_congr fun i ↦ ?_).mpr hv
  rw [charSumRep_apply]
  rcases Int.units_eq_one_or (kleinChar i g) with h | h
  · simp [h]
  · simp only [h, Units.val_neg, Units.val_one]
    omega

/-- The module of the basic type `T` as a subrepresentation of `A₀ ⊕ A₁ ⊕ A₂`. -/
def subrep : Subrepresentation charSumRep where
  toSubmodule := T.lattice
  apply_mem_toSubmodule g _ := T.cond_charSumRep g

/-- **The `ℤ[V₄]`-module of the basic type `T`** of Mazur and Ullom, for `V₄ = ℤˣ × ℤˣ`: the lattice
`T.lattice` of `ℤ³`, on which `g` multiplies the `j`-th coordinate by `χⱼ g`. -/
def rep : Representation ℤ (ℤˣ × ℤˣ) T.lattice :=
  T.subrep.toRepresentation

variable (u) in
lemma coe_rep_apply : (T.rep g u : Fin 3 → ℤ) = charSumRep g u :=
  rfl

/-- The multipliers of the generators of the fixed lattices of the module of type `T`: the vectors
fixed by `σᵢ` are the multiples of `mᵢ eᵢ`. -/
def fixedMul : MazurUllomBasicType → Fin 3 → ℤ
  | I => ![1, 1, 1]
  | II => ![2, 2, 1]
  | III | IV => ![2, 2, 2]

lemma fixedMul_ne_zero : T.fixedMul i ≠ 0 := by
  fin_cases i <;> cases T <;> decide

lemma cond_fixedMul : T.Cond fun i ↦ T.fixedMul i * w i := by
  cases T <;> simp [Cond, fixedMul] <;> omega

lemma cond_single_iff : T.Cond (Pi.single i n) ↔ T.fixedMul i ∣ n := by
  fin_cases i <;> cases T <;> simp [Cond, fixedMul]

/-- The linear map `w ↦ (mᵢ wᵢ)ᵢ` into the module of type `T`, whose image is the sum of the
lattices fixed by `σ₀`, `σ₁` and `σ₂`. -/
def fixedMap : (Fin 3 → ℤ) →ₗ[ℤ] T.lattice where
  toFun w := ⟨fun i ↦ T.fixedMul i * w i, T.cond_fixedMul⟩
  map_add' _ _ := Subtype.ext <| funext fun _ ↦ mul_add _ _ _
  map_smul' c _ := Subtype.ext <| funext fun _ ↦ mul_left_comm _ c _

lemma coe_fixedMap_apply : (T.fixedMap w : Fin 3 → ℤ) i = T.fixedMul i * w i :=
  rfl

lemma fixedMap_injective : Function.Injective T.fixedMap :=
  fun _ _ h ↦ funext fun i ↦ mul_left_cancel₀ (T.fixedMul_ne_zero i)
    (congrFun (congrArg Subtype.val h) i)

lemma fixedMap_single : T.fixedMap (Pi.single i n) = n • T.fixedMap (Pi.single i 1) := by
  rw [← map_smul]
  congr 1
  ext j
  simp [Pi.single_apply]

lemma rep_kleinSigma_fixedMap_single :
    T.rep (kleinSigma i) (T.fixedMap (Pi.single i n)) = T.fixedMap (Pi.single i n) := by
  refine Subtype.ext <| funext fun j ↦ ?_
  rw [coe_rep_apply, charSumRep_apply, coe_fixedMap_apply, kleinChar_kleinSigma]
  split_ifs with hij
  · rw [Units.val_one, one_mul]
  · rw [Pi.single_eq_of_ne (Ne.symm hij), mul_zero, mul_zero]

lemma fixedMap_single_div_eq (hu : T.rep (kleinSigma i) u = u) :
    T.fixedMap (Pi.single i ((u : Fin 3 → ℤ) i / T.fixedMul i)) = u := by
  have h0 (j : Fin 3) (hji : j ≠ i) : (u : Fin 3 → ℤ) j = 0 := by
    have h : (kleinChar j (kleinSigma i) : ℤ) * (u : Fin 3 → ℤ) j = (u : Fin 3 → ℤ) j :=
      congrFun (congrArg Subtype.val hu) j
    rw [kleinChar_kleinSigma, ite_eq_right (Ne.symm hji), Units.val_neg, Units.val_one] at h
    omega
  have hsingle : (u : Fin 3 → ℤ) = Pi.single i ((u : Fin 3 → ℤ) i) := by
    funext j
    rcases eq_or_ne j i with rfl | hji
    · rw [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne hji, h0 j hji]
  have hdvd : T.fixedMul i ∣ (u : Fin 3 → ℤ) i := by
    rw [← cond_single_iff, ← hsingle]
    exact u.2
  refine Subtype.ext <| funext fun j ↦ ?_
  rw [coe_fixedMap_apply]
  rcases eq_or_ne j i with rfl | hji
  · rw [Pi.single_eq_same, Int.mul_ediv_cancel' hdvd]
  · rw [Pi.single_eq_of_ne hji, mul_zero, h0 j hji]

variable (w) in
lemma even_fixedMap_iff : Even (T.fixedMap w) ↔ T.toType.Parity w := by
  refine ⟨fun ⟨r, hr⟩ ↦ ?_, fun hw ↦ ?_⟩
  · have h (i : Fin 3) : T.fixedMul i * w i = (r : Fin 3 → ℤ) i + (r : Fin 3 → ℤ) i :=
      congrFun (congrArg Subtype.val hr) i
    have h₀ : T.fixedMul 0 * w 0 = (r : Fin 3 → ℤ) 0 + (r : Fin 3 → ℤ) 0 := h 0
    have h₁ : T.fixedMul 1 * w 1 = (r : Fin 3 → ℤ) 1 + (r : Fin 3 → ℤ) 1 := h 1
    have h₂ : T.fixedMul 2 * w 2 = (r : Fin 3 → ℤ) 2 + (r : Fin 3 → ℤ) 2 := h 2
    have hr' : T.Cond r := r.2
    cases T <;> simp [fixedMul, toType, Cond, MazurUllomType.Parity] at h₀ h₁ h₂ hr' ⊢ <;> omega
  · have hdvd (i : Fin 3) : 2 ∣ T.fixedMul i * w i := by
      fin_cases i <;> cases T <;> simp [fixedMul, toType, MazurUllomType.Parity] at hw ⊢ <;> omega
    refine ⟨⟨fun i ↦ T.fixedMul i * w i / 2, ?_⟩, Subtype.ext <| funext fun i ↦ ?_⟩
    · cases T <;> simp [mem_lattice, Cond, fixedMul, toType, MazurUllomType.Parity] at hw ⊢ <;>
        omega
    · have hi : 2 ∣ T.fixedMul i * w i := hdvd i
      have hz : T.fixedMul i * w i = T.fixedMul i * w i / 2 + T.fixedMul i * w i / 2 := by
        generalize T.fixedMul i * w i = z at hi ⊢
        omega
      exact hz

lemma eq_of_forall_apply_rep (ψ : ℤˣ × ℤˣ ≃* ℤˣ × ℤˣ) (α : T.lattice ≃ₗ[ℤ] T'.lattice)
    (h : ∀ g u, α (T.rep g u) = T'.rep (ψ g) (α u)) : T = T' := by
  -- `ψ` permutes the nontrivial elements: `ψ σᵢ = σ_{p i}`.
  have hp (i : Fin 3) : ∃ j, kleinSigma j = ψ (kleinSigma i) :=
    (eq_one_or_exists_kleinSigma _).resolve_left fun h1 ↦
      kleinSigma_ne_one i <| ψ.injective <| h1.trans (map_one ψ).symm
  choose p hp using hp
  have hpinj : Function.Injective p := fun i j hij ↦ kleinSigma_injective <| ψ.injective <|
    (hp i).symm.trans <| (congrArg kleinSigma hij).trans (hp j)
  let π : Perm (Fin 3) := Equiv.ofBijective p hpinj.bijective_of_finite
  -- `α` maps the generator of the lattice fixed by `σᵢ` to `±` the one fixed by `σ_{p i}`.
  have hc (i : Fin 3) : ∃ c : ℤ, (c = 1 ∨ c = -1) ∧
      T'.fixedMap (Pi.single (p i) c) = α (T.fixedMap (Pi.single i 1)) := by
    have hfix : T'.rep (kleinSigma (p i)) (α (T.fixedMap (Pi.single i 1))) =
        α (T.fixedMap (Pi.single i 1)) := by
      rw [hp, ← h, T.rep_kleinSigma_fixedMap_single]
    have hfix' : T.rep (kleinSigma i) (α.symm (T'.fixedMap (Pi.single (p i) 1))) =
        α.symm (T'.fixedMap (Pi.single (p i) 1)) := by
      refine α.injective ?_
      rw [h, α.apply_symm_apply, ← hp, T'.rep_kleinSigma_fixedMap_single]
    rcases (⟨_, T'.fixedMap_single_div_eq _ hfix⟩ : ∃ c : ℤ,
      T'.fixedMap (Pi.single (p i) c) = α (T.fixedMap (Pi.single i 1))) with ⟨c, hc⟩
    rcases (⟨_, T.fixedMap_single_div_eq _ hfix'⟩ : ∃ d : ℤ,
      T.fixedMap (Pi.single i d) = α.symm (T'.fixedMap (Pi.single (p i) 1))) with ⟨d, hd⟩
    have h1 : T'.fixedMap (Pi.single (p i) (d * c)) = T'.fixedMap (Pi.single (p i) 1) := by
      rw [T'.fixedMap_single _ (d * c), mul_smul, ← T'.fixedMap_single, hc,
        ← map_smul α d, ← T.fixedMap_single, hd, α.apply_symm_apply]
    have h2 : d * c = 1 := by
      simpa using congrFun (T'.fixedMap_injective h1) (p i)
    exact ⟨c, Int.eq_one_or_neg_one_of_mul_eq_one ((mul_comm c d).trans h2), hc⟩
  choose c hc₁ hc using hc
  -- Hence `α` maps `(mᵢ wᵢ)ᵢ` to `(m'ⱼ cᵢ wᵢ)ⱼ` with `j = π i`.
  have hmap (w : Fin 3 → ℤ) :
      α (T.fixedMap w) = T'.fixedMap fun j ↦ c (π.symm j) * w (π.symm j) := by
    let L : (Fin 3 → ℤ) →ₗ[ℤ] Fin 3 → ℤ :=
      LinearMap.pi fun j ↦ c (π.symm j) • LinearMap.proj (π.symm j)
    have hlin : α.toLinearMap ∘ₗ T.fixedMap = T'.fixedMap ∘ₗ L := by
      refine LinearMap.pi_ext fun i x ↦ ?_
      have hπ : π.symm (p i) = i := π.symm_apply_eq.mpr rfl
      have hL : L (Pi.single i x) = Pi.single (p i) (c i * x) := by
        funext j
        simp only [L, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
        rcases eq_or_ne j (p i) with rfl | hj
        · rw [hπ, Pi.single_eq_same, Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne hj, Pi.single_eq_of_ne fun h' ↦ hj (π.symm_apply_eq.mp h'),
            mul_zero]
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hL, LinearEquiv.coe_coe, T.fixedMap_single,
        map_smul, ← hc i, T'.fixedMap_single _ (c i), T'.fixedMap_single _ (c i * x), smul_smul,
        mul_comm]
    exact LinearMap.congr_fun hlin w
  -- So the parity patterns of `T.toType` and `T'.toType` differ by `π`.
  have hpar (w : Fin 3 → ℤ) :
      T.toType.Parity w ↔ T'.toType.Parity fun j ↦ c (π.symm j) * w (π.symm j) := by
    rw [← T.even_fixedMap_iff, ← T'.even_fixedMap_iff, ← hmap w]
    exact ⟨fun hx ↦ hx.map α, fun hx ↦ by simpa using hx.map α.symm⟩
  refine (T.basicType_toType.symm.trans ?_).trans T'.basicType_toType
  refine congrArg MazurUllomType.basicType <|
    MazurUllomType.eq_of_forall_parity_iff T.toType T'.toType π.symm fun u ↦ ?_
  refine (T'.toType.parity_congr fun j ↦ ?_).trans (hpar fun i ↦ (u (π i) : ℤ)).symm
  rw [π.apply_symm_apply]
  rcases hc₁ (π.symm j) with h' | h' <;> rw [h'] <;> omega

/-- **The four modules of Mazur and Ullom are pairwise non-isomorphic, even after an automorphism
of `V₄`** (their Remark 1): if the module of type `T` is isomorphic as a `ℤ[V₄]`-module to the
module of type `T'` twisted by an automorphism `ψ` of `V₄ = ℤˣ × ℤˣ`, then `T = T'`. -/
lemma eq_of_equiv (ψ : ℤˣ × ℤˣ ≃* ℤˣ × ℤˣ) (e : T.rep.Equiv (T'.rep.comp ψ.toMonoidHom)) : T = T' :=
  T.eq_of_forall_apply_rep ψ e.toLinearEquiv fun g u ↦ LinearMap.congr_fun (e.isIntertwining' g) u

/-- **The four modules of Mazur and Ullom stay pairwise non-isomorphic when pulled back to a group
`G`** along any two isomorphisms `φ φ' : G ≃* V₄`: if the module of type `T` pulled back along `φ`
is isomorphic to that of type `T'` pulled back along `φ'`, then `T = T'`. For `G` a Galois group,
this says that the type is an invariant of the Galois module. -/
lemma eq_of_equiv_comp {G : Type*} [Group G] (φ φ' : G ≃* ℤˣ × ℤˣ)
    (e : Representation.Equiv (T.rep.comp φ.toMonoidHom) (T'.rep.comp φ'.toMonoidHom)) : T = T' :=
  T.eq_of_forall_apply_rep (φ.symm.trans φ') e.toLinearEquiv fun g u ↦ by
    simpa using LinearMap.congr_fun (e.isIntertwining' (φ.symm g)) u

end MazurUllomBasicType

namespace MazurUllomType

variable (t : MazurUllomType) {v w : Fin 3 → ℤ} (i : Fin 3)

/-- The rescaling of the subtype `t`: `w` lies in the lattice of the basic type of `t` iff the
vector `(t.scale i * w i)ᵢ` lies in the parity pattern of `t`. -/
def scale : MazurUllomType → Fin 3 → ℤ
  | I₁ => ![2, 2, 2]
  | I₂ => ![1, 2, 2]
  | I₃ | II₁ => ![1, 1, 2]
  | II₂ | III | IV => ![1, 1, 1]

lemma scale_ne_zero : t.scale i ≠ 0 := by
  fin_cases i <;> cases t <;> decide

lemma scale_dvd (hv : t.Parity v) : t.scale i ∣ v i := by
  fin_cases i <;> cases t <;> simp [Parity, scale] at hv ⊢ <;> omega

lemma parity_scale_iff : t.Parity (fun i ↦ t.scale i * w i) ↔ t.basicType.Cond w := by
  cases t <;> simp [Parity, scale, basicType, MazurUllomBasicType.Cond]

namespace IsSquareBasis

variable {G : Type*} [CommGroup G] {e : Fin 3 → G} {t}

variable [IsMulTorsionFree G] in
lemma isSquare_prod_rescale_iff (he : IsSquareBasis e) (ht : t.IsTypeOf e) :
    IsSquare (∏ i, (e i ^ t.scale i) ^ w i) ↔ w ∈ t.basicType.lattice := by
  have h : IsSquare (∏ i, e i ^ (t.scale i * w i)) ↔ t.Parity fun i ↦ t.scale i * w i :=
    (he.isTypeOf_iff t).mp ht _
  simpa only [zpow_mul, t.parity_scale_iff, MazurUllomBasicType.mem_lattice] using h

variable [IsMulTorsionFree G] in
lemma rescale (he : IsSquareBasis e) (ht : t.IsTypeOf e) :
    IsSquareBasis fun i ↦ e i ^ t.scale i where
  exists_sq_eq x := by
    rcases he.exists_sq_eq x with ⟨a, ha⟩
    have hpar : t.Parity a := ((he.isTypeOf_iff t).mp ht a).mp ⟨x, ha.symm.trans (sq x)⟩
    choose b hb using fun i ↦ t.scale_dvd i hpar
    exact ⟨b, ha.trans <| by simp only [hb, zpow_mul]⟩
  eq_zero_of_prod_eq_one {b} h := by
    have h' : (fun i ↦ t.scale i * b i) = 0 :=
      he.eq_zero_of_prod_eq_one <| by simpa only [zpow_mul] using h
    exact funext fun i ↦ (mul_eq_zero.mp (congrFun h' i)).resolve_left (t.scale_ne_zero i)

variable (he : IsSquareBasis e) (x y : G)

/-- The exponent vector of `x ^ 2` in the square basis `e`: `x ^ 2 = ∏ i, e i ^ he.sqVec x i`. -/
noncomputable def sqVec : Fin 3 → ℤ :=
  (he.exists_sq_eq x).choose

lemma sq_eq_prod_sqVec : x ^ 2 = ∏ i, e i ^ he.sqVec x i :=
  (he.exists_sq_eq x).choose_spec

variable {x} in
lemma sqVec_eq (h : x ^ 2 = ∏ i, e i ^ v i) : he.sqVec x = v :=
  he.eq_of_prod_eq <| (he.sq_eq_prod_sqVec x).symm.trans h

lemma sqVec_one : he.sqVec 1 = 0 :=
  he.sqVec_eq <| by simp

lemma sqVec_mul : he.sqVec (x * y) = he.sqVec x + he.sqVec y :=
  he.sqVec_eq <| by rw [mul_pow, he.sq_eq_prod_sqVec x, he.sq_eq_prod_sqVec y, prod_zpow_add]

lemma sqVec_map {τ : G →* G} {s : Fin 3 → ℤ} (hτ : ∀ i, τ (e i) = e i ^ s i) :
    he.sqVec (τ x) = fun i ↦ s i * he.sqVec x i :=
  he.sqVec_eq <| by
    rw [← map_pow, he.sq_eq_prod_sqVec x, map_prod]
    simp only [map_zpow, hτ, ← zpow_mul]

variable {P : Submodule ℤ (Fin 3 → ℤ)} (hP : ∀ v, IsSquare (∏ i, e i ^ v i) ↔ v ∈ P)

/-- The map `x ↦ he.sqVec x` into a lattice `P` whose vectors are those of the products of the
`e i` that are squares. -/
noncomputable def sqVecHom : Additive G →+ P where
  toFun a := ⟨he.sqVec a.toMul, (hP _).mp ⟨a.toMul, (he.sq_eq_prod_sqVec _).symm.trans (sq _)⟩⟩
  map_zero' := Subtype.ext he.sqVec_one
  map_add' a b := Subtype.ext <| he.sqVec_mul a.toMul b.toMul

variable [IsMulTorsionFree G]

lemma sqVecHom_bijective : Function.Bijective (he.sqVecHom hP) := by
  refine ⟨fun a b hab ↦ Additive.toMul.injective ?_, fun u ↦ ?_⟩
  · have hab' : he.sqVec a.toMul = he.sqVec b.toMul := congrArg Subtype.val hab
    refine eq_of_pow_eq_pow_of_commute two_ne_zero (.all _ _) ?_
    rw [he.sq_eq_prod_sqVec, hab', ← he.sq_eq_prod_sqVec]
  · rcases (hP u).mpr u.2 with ⟨r, hr⟩
    exact ⟨Additive.ofMul r, Subtype.ext <| he.sqVec_eq <| (sq r).trans hr.symm⟩

/-- **The square-exponent isomorphism**: if the products `∏ i, e i ^ vᵢ` that are squares are those
with `v ∈ P`, then `x ↦ he.sqVec x` is an isomorphism of the torsion-free group `G` onto `P`. -/
noncomputable def sqVecEquiv : Additive G ≃ₗ[ℤ] P :=
  (AddEquiv.ofBijective _ (he.sqVecHom_bijective hP)).toIntLinearEquiv

lemma coe_sqVecEquiv_apply (a : Additive G) : (he.sqVecEquiv hP a : Fin 3 → ℤ) = he.sqVec a.toMul :=
  rfl

end IsSquareBasis

end MazurUllomType

end NumberField.Units
