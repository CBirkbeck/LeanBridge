import LeanBridge.ForMathlib.NumberTheory.LocalField.TateLocalConstant
import TauCeti.NumberTheory.ClassFieldTheory.Local.Conductor
import TauCeti.NumberTheory.ClassFieldTheory.Local.ExplicitCyclotomicSymbol.ArtinMap

/-!
# Local root numbers of Galois characters and of abelian extensions of `ℚ_p`

The local root number `ε(ρ)` of a representation `ρ` of `Gal(ℚ̄_p/ℚ_p)` (LMFDB `lf.root_number`) is
the Langlands–Deligne local constant of `ρ`, and `ε(K) = ε(ρ_K)` for the permutation representation
`ρ_K` on the embeddings of a `p`-adic field `K` in `ℚ̄_p`. The committed file
`TateLocalConstant.lean` has Tate's local root numbers `W(χ)` of the characters `χ` of `ℚ_p^×` and
of `ℝ^×`. This file passes to characters of the Galois group, through Tau Ceti's local Artin map
`Art : ℚ_p^× → G_{ℚ_p}^ab`, normalised by arithmetic Frobenius
(`TauCeti.ClassFieldTheory.artinMap`), so that `ε(χ) = W(χ ∘ Art)` for a continuous character `χ`
of `G_{ℚ_p}`, and `ε(K)` makes sense for abelian extensions `K / ℚ_p`.

The normalisation of the passage is pinned by the cyclotomic characters: a Dirichlet character `ψ`
modulo `p ^ n` gives the Galois character `σ ↦ ψ(χ_cyc(σ))`, which is `ψ(q)` on an arithmetic
Frobenius at a prime `q ≠ p`, so that the Artin L-function of this character is `L(s, ψ)`. Since
`Art(p ^ k u)` acts on the roots of unity of `p`-power order through `u⁻¹`, its character of `ℚ_p^×`
is the local component at `p` of the idele class character of `ψ`, and for primitive `ψ` the product
of the local root numbers at `∞` and `p` is Mathlib's root number of `L(s, ψ)`
(`Padic.real_tateRootNumber_mul_galoisRootNumber`), as the knowl states for the global root number.

If `K / ℚ_p` is finite and abelian with group `G`, then the character of `ρ_K` is the sum of the
characters of `G`, inflated to `G_{ℚ_p}` (`Padic.natCast_permutationCharacter_eq_finsum`), so
`ρ_K` is the direct sum of these characters. Multiplicativity, which the knowl lists as a property
of the local root numbers, then gives `ε(K) = ∏_χ ε(χ)`, the definition of
`Padic.abelianRootNumber`.

## What remains for general `K` and dimension at least `2`

The local root numbers of representations of dimension at least `2`, which `ρ_K` is for every `K`
that is not abelian over `ℚ_p`, are not defined here. Their definition rests on the following.
* Tate's local constants `ε(χ, ψ_F, dx)` for characters of `F^×`, `F / ℚ_p` finite, the additive
  characters `ψ_F = ψ_p ∘ Tr_{F/ℚ_p}` and the self-dual Haar measures, of which only the case
  `F = ℚ_p` is formalised.
* Deligne's existence theorem (*Les constantes des équations fonctionnelles des fonctions L*, LNM
  349, Théorème 4.1; Langlands' local proof is unpublished): there is a unique function `ε` on
  the virtual representations of the Weil groups of all finite `F / ℚ_p` that is additive in `ρ`,
  equal to Tate's constant on characters and inductive in degree `0`. Tau Ceti has Brauer induction,
  which gives the uniqueness; the existence is a theorem on global L-functions (the functional
  equations of the Hecke L-functions of all number fields with their factorisation into Tate's local
  constants), none of which is formalised.
* The values `ε(K) ∈ {1, i, -1, -i}` of the knowl, which for abelian `K` also need the identity
  `W(χ) W(χ⁻¹) = χ(-1)`; they are not proved here.

## Main definitions

* `Padic.artinCharacter`: the character `χ ∘ Art` of `ℚ_p^×` of a character `χ` of `G_{ℚ_p}`.
* `Padic.galoisRootNumber` (LMFDB `lf.root_number`): the local root number of a character of
  `G_{ℚ_p}`.
* `Padic.dirichletGaloisCharacter`: the character of `G_{ℚ_p}` of a Dirichlet character modulo
  `p ^ n`, through the cyclotomic character.
* `Padic.inflateCharacter`: the character of `G_{ℚ_p}` of a character of `Gal(K / ℚ_p)`.
* `Padic.permutationCharacter`: the character of the permutation representation `ρ_K`.
* `Padic.abelianRootNumber` (LMFDB `lf.root_number`): the local root number `ε(K)` of an abelian
  extension `K` of `ℚ_p`.
* `Real.artinSign`: the Artin map of `ℝ`.
* `Real.galoisRootNumber` (LMFDB `lf.root_number`): the local root number of a character of
  `Gal(ℂ/ℝ)`.

## Main results

* `Padic.charConductorExponent_artinCharacter` and
  `Padic.isTrivialOnUnitsMod_charConductorExponent_artinCharacter`: the conductor of `χ ∘ Art` is
  Tau Ceti's, and it is attained, so the local root number of a continuous character of `G_{ℚ_p}`
  never takes the junk value of `Padic.tateRootNumber`.
* `Padic.galoisRootNumber_eq_one`: an unramified character has local root number `1`.
* `Padic.charConductorExponent_dirichletGaloisCharacter`: the character of a primitive Dirichlet
  character modulo `p ^ n` has conductor `p ^ n`.
* `Padic.galoisRootNumber_dirichletGaloisCharacter`: the local root number at `p` of a primitive
  Dirichlet character `ψ` modulo `p ^ n`, `n ≠ 0`, is `τ(ψ) / √(p ^ n)`.
* `Padic.real_tateRootNumber_mul_galoisRootNumber`: the local root numbers of a primitive Dirichlet
  character modulo `p ^ n` multiply to the root number of its L-function.
* `Padic.natCast_permutationCharacter_eq_finsum`: the permutation representation of an abelian
  extension is the sum of the characters of its Galois group.
* `Padic.abelianRootNumber_of_subsingleton`: `ε(ℚ_p) = 1`.
* `Real.galoisRootNumber_one`, `Real.galoisRootNumber_of_apply_conj_ne_one`: the trivial and sign
  characters of `Gal(ℂ/ℝ)` have local root numbers `1` and `-i`.
* `Real.galoisRootNumber_mul_galoisRootNumber`: the same product formula with both local root
  numbers on the Galois side.
-/

open Complex TauCeti ClassFieldTheory

namespace Padic

variable {p n : ℕ} [Fact p.Prime] (χ : Field.absoluteGaloisGroup ℚ_[p] →ₜ* ℂˣ) {x : ℚ_[p]ˣ}
  {φ : ℚ_[p]ˣ →* ℂˣ}

/-- The character `χ ∘ Art` of `ℚ_p^×` of a continuous character `χ` of `Gal(ℚ̄_p/ℚ_p)`, for the
local Artin map `Art : ℚ_p^× → Gal(ℚ̄_p/ℚ_p)^ab` of Tau Ceti, which sends a uniformiser to the class
of an arithmetic Frobenius, and the factorisation `TopologicalAbelianization.lift χ` of `χ` through
the abelianisation. -/
noncomputable def artinCharacter : ℚ_[p]ˣ →* ℂˣ :=
  (TopologicalAbelianization.lift χ).toMonoidHom.comp (artinMap ℚ_[p])

lemma artinCharacter_eq_of_mk_eq {σ : Field.absoluteGaloisGroup ℚ_[p]}
    (hσ : (σ : Field.absoluteGaloisGroupAbelianization ℚ_[p]) = artinMap ℚ_[p] x) :
    artinCharacter χ x = χ σ := by
  rw [artinCharacter, MonoidHom.comp_apply, ← hσ]
  exact TopologicalAbelianization.lift_mk χ σ

lemma continuous_artinCharacter : Continuous (artinCharacter χ) :=
  (TopologicalAbelianization.lift χ).continuous.comp (continuous_artinMap ℚ_[p])

/-- The **local root number** `ε(χ)` (LMFDB `lf.root_number`) of a continuous character `χ` of
`Gal(ℚ̄_p/ℚ_p)`: Tate's local root number `W(χ ∘ Art)` of the character `χ ∘ Art` of `ℚ_p^×`
(`Padic.tateRootNumber`), whose conductor exponent is that of Tau Ceti
(`Padic.charConductorExponent_artinCharacter`), so that it is not a junk value. -/
noncomputable def galoisRootNumber : ℂ :=
  tateRootNumber (artinCharacter χ)

lemma coe_normalizedAbsoluteValue (y : ℚ_[p]) : (normalizedAbsoluteValue ℚ_[p] y : ℝ) = ‖y‖ := by
  have h : ((normalizedAbsoluteValue ℚ_[p] y : NNReal) : ℝ) = ‖y‖ :=
    congrArg ((↑) : NNReal → ℝ) (normalizedAbsoluteValue_eq_nnnorm p y)
  exact_mod_cast h

lemma norm_eq_one_iff_valuation (y : ℚ_[p]) : ‖y‖ = 1 ↔ ValuativeRel.valuation ℚ_[p] y = 1 := by
  rw [← normalizedAbsoluteValue_eq_one_iff, ← coe_normalizedAbsoluteValue]
  norm_cast

lemma norm_le_iff_valuation_le (y z : ℚ_[p]) :
    ‖y‖ ≤ ‖z‖ ↔ ValuativeRel.valuation ℚ_[p] y ≤ ValuativeRel.valuation ℚ_[p] z := by
  rw [← normalizedAbsoluteValue_le_normalizedAbsoluteValue_iff, ← coe_normalizedAbsoluteValue,
    ← coe_normalizedAbsoluteValue]
  norm_cast

lemma mem_unitFiltration_iff_norm {u : ℚ_[p]ˣ} :
    u ∈ unitFiltration ℚ_[p] n ↔ ‖(u : ℚ_[p])‖ = 1 ∧ ‖(u : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  have hp : (p : ℝ) ^ (-(n : ℤ)) = ‖(p : ℚ_[p]) ^ n‖ := by
    rw [norm_pow, norm_p, zpow_neg, zpow_natCast, inv_pow]
  rw [mem_unitFiltration_iff_valuation_le (Padic.irreducible_natCast_self p),
    norm_eq_one_iff_valuation, hp, norm_le_iff_valuation_le, map_pow]
  rfl

lemma isTrivialOnUnitsMod_iff : IsTrivialOnUnitsMod φ n ↔ unitFiltration ℚ_[p] n ≤ φ.ker :=
  ⟨fun h _ hu ↦ h _ (mem_unitFiltration_iff_norm.mp hu).1 (mem_unitFiltration_iff_norm.mp hu).2,
    fun h _ hu hu₁ ↦ h (mem_unitFiltration_iff_norm.mpr ⟨hu, hu₁⟩)⟩

/-- **The conductor of `χ ∘ Art`**: the exponent `charConductorExponent` of the conductor of the
character `χ ∘ Art` of `ℚ_p^×`, for a continuous character `χ` of `Gal(ℚ̄_p/ℚ_p)`, is Tau Ceti's
conductor exponent, the least `n` with `U(ℚ_p, n) ⊆ ker (χ ∘ Art)`. -/
lemma charConductorExponent_artinCharacter : charConductorExponent (artinCharacter χ) =
    characterConductorExp ℚ_[p] ⟨artinCharacter χ, continuous_artinCharacter χ⟩ :=
  congrArg sInf <| Set.ext fun _ ↦ isTrivialOnUnitsMod_iff

/-- **The conductor of `χ ∘ Art` is attained**: for a continuous character `χ` of `Gal(ℚ̄_p/ℚ_p)`,
`χ ∘ Art` is trivial on the units congruent to `1` modulo its conductor, so the junk case of
`Padic.charConductorExponent` does not arise in the local root number of `χ`. -/
lemma isTrivialOnUnitsMod_charConductorExponent_artinCharacter :
    IsTrivialOnUnitsMod (artinCharacter χ) (charConductorExponent (artinCharacter χ)) := by
  rw [isTrivialOnUnitsMod_iff, charConductorExponent_artinCharacter]
  exact unitFiltration_characterConductorExp_le_ker ℚ_[p] _

variable {χ}

/-- **An unramified character has local root number `1`** (LMFDB `lf.root_number`): a character of
`Gal(ℚ̄_p/ℚ_p)` that is trivial on the inertia subgroup. -/
lemma galoisRootNumber_eq_one (h : ∀ σ ∈ inertiaSubgroup ℚ_[p], χ σ = 1) :
    galoisRootNumber χ = 1 := by
  refine tateRootNumber_eq_one fun u hu _ ↦ ?_
  rcases QuotientGroup.mk_surjective (artinMap ℚ_[p] u) with ⟨σ, hσ⟩
  rw [artinCharacter_eq_of_mk_eq χ hσ]
  exact h σ <|
    mem_inertiaSubgroup_of_mk_eq_artinMap ℚ_[p] u ((norm_eq_one_iff_valuation _).mp hu) σ hσ

variable (ψ : DirichletCharacter ℂ (p ^ n))

variable (n) in
lemma mem_ker_units_toZModPow_iff (u : ℤ_[p]ˣ) : u ∈
    (Units.map (PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n)).toMonoidHom).ker ↔
      ‖(u : ℤ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
  rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub,
    map_one, sub_eq_zero, MonoidHom.mem_ker, Units.ext_iff]
  rfl

/-- The **character of `Gal(ℚ̄_p/ℚ_p)` of a Dirichlet character** `ψ` modulo `p ^ n`: the composite
`σ ↦ ψ(χ_cyc(σ) mod p ^ n)` with the cyclotomic character `χ_cyc`. It is `ψ(q)` on an arithmetic
Frobenius at a prime `q ≠ p`, in the sense that `χ_cyc` sends such a Frobenius to `q`. -/
noncomputable def dirichletGaloisCharacter : Field.absoluteGaloisGroup ℚ_[p] →ₜ* ℂˣ where
  toMonoidHom := (ψ.toUnitHom.comp
    (Units.map (PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n)).toMonoidHom)).comp
      (localCyclotomicCharacter p ℚ_[p])
  continuous_toFun := (continuous_of_discreteTopology (f := ψ.toUnitHom)).comp <|
    (map_continuous (PadicInt.unitsToZModPow n)).comp (localCyclotomicCharacter_continuous p ℚ_[p])

variable {k : ℤ} {u : ℤ_[p]ˣ}

lemma artinCharacter_dirichletGaloisCharacter (hx : (x : ℚ_[p]) = (p : ℚ_[p]) ^ k * (u : ℤ_[p])) :
    artinCharacter (dirichletGaloisCharacter ψ) x = ψ.toUnitHom
      (Units.map (PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n)).toMonoidHom u⁻¹) := by
  rcases QuotientGroup.mk_surjective (artinMap ℚ_[p] x) with ⟨σ, hσ⟩
  rw [artinCharacter_eq_of_mk_eq _ hσ]
  have hcyc : localCyclotomicCharacter p ℚ_[p] σ = u⁻¹ := by
    rw [← abelianizedLocalCyclotomicCharacter_mk]
    exact (congrArg _ hσ).trans (abelianizedLocalCyclotomicCharacter_artinMap_padic p hx)
  exact congrArg (ψ.toUnitHom.comp
    (Units.map (PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n)).toMonoidHom)) hcyc

lemma charValueNat_self_dirichletGaloisCharacter :
    charValueNat (artinCharacter (dirichletGaloisCharacter ψ)) p = 1 := by
  have hp : p ≠ 0 :=
    (Fact.out : p.Prime).ne_zero
  rw [charValueNat, dite_eq_right hp, artinCharacter_dirichletGaloisCharacter ψ (k := 1) (u := 1)
    (by simp)]
  simp

lemma charValueNat_dirichletGaloisCharacter {m : ℕ} (hm : p.Coprime m) :
    charValueNat (artinCharacter (dirichletGaloisCharacter ψ)) m = (ψ m)⁻¹ := by
  have hm₀ : m ≠ 0 := by
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' (by simpa using hm)
  have hnorm : ‖(m : ℚ_[p])‖ = 1 :=
    Padic.norm_natCast_eq_one_iff.mpr hm
  rw [charValueNat, dite_eq_right hm₀, artinCharacter_dirichletGaloisCharacter ψ (k := 0)
    (u := PadicInt.mkUnits hnorm) (by simp), map_inv, map_inv, Units.val_inv_eq_inv_val]
  congr 1
  rw [MulChar.coe_toUnitHom]
  congr 1
  have h₁ : ((PadicInt.mkUnits hnorm : ℤ_[p]ˣ) : ℤ_[p]) = m :=
    Subtype.ext (by simp)
  rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, h₁, map_natCast]

lemma isTrivialOnUnitsMod_dirichletGaloisCharacter :
    IsTrivialOnUnitsMod (artinCharacter (dirichletGaloisCharacter ψ)) n := by
  intro u hu hu₁
  have hv : (u : ℚ_[p]) = (p : ℚ_[p]) ^ (0 : ℤ) * ((PadicInt.mkUnits hu : ℤ_[p]ˣ) : ℤ_[p]) := by
    simp
  rw [artinCharacter_dirichletGaloisCharacter ψ hv]
  have hker : PadicInt.mkUnits hu ∈
      (Units.map (PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n)).toMonoidHom).ker := by
    rw [mem_ker_units_toZModPow_iff, PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_one,
      PadicInt.mkUnits_eq]
    exact hu₁
  rw [map_inv, MonoidHom.mem_ker.mp hker, inv_one, map_one]

variable {ψ}

lemma not_isTrivialOnUnitsMod_dirichletGaloisCharacter (hψ : ψ.IsPrimitive) {a : ℕ} (ha : a < n) :
    ¬IsTrivialOnUnitsMod (artinCharacter (dirichletGaloisCharacter ψ)) a := by
  intro h
  have hp : p.Prime :=
    Fact.out
  have hne : NeZero (p ^ n) :=
    ⟨pow_ne_zero n hp.ne_zero⟩
  have hd : p ^ a ∣ p ^ n :=
    pow_dvd_pow p ha.le
  have hfac : ψ.FactorsThrough (p ^ a) := by
    refine (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mpr fun v hv ↦ ?_
    have hcop : p.Coprime (v : ZMod (p ^ n)).val :=
      ((ZMod.val_coe_unit_coprime v).coprime_dvd_right
        (dvd_pow_self p (Nat.ne_of_gt (Nat.zero_lt_of_lt ha)))).symm
    have hval : (((v : ZMod (p ^ n)).val : ℕ) : ZMod (p ^ n)) = v :=
      ZMod.natCast_zmod_val _
    have hnorm : ‖(((v : ZMod (p ^ n)).val : ℕ) : ℚ_[p])‖ = 1 :=
      Padic.norm_natCast_eq_one_iff.mpr hcop
    have hm₀ : (v : ZMod (p ^ n)).val ≠ 0 := by
      intro h₀
      rw [h₀] at hnorm
      simp at hnorm
    have hcast : (((v : ZMod (p ^ n)).val : ℕ) : ZMod (p ^ a)) = 1 := by
      have h₁ : ((ZMod.unitsMap hd v : (ZMod (p ^ a))ˣ) : ZMod (p ^ a)) = 1 := by
        rw [MonoidHom.mem_ker.mp hv, Units.val_one]
      rw [ZMod.unitsMap_val, ← hval, ZMod.cast_natCast hd] at h₁
      exact h₁
    have hdvd : ((p ^ a : ℕ) : ℤ) ∣ (((v : ZMod (p ^ n)).val : ℕ) : ℤ) - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hcast, sub_self]
    have hle : ‖((v : ZMod (p ^ n)).val : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(a : ℤ)) := by
      simpa using (Padic.norm_int_le_pow_iff_dvd (p := p)
        (((v : ZMod (p ^ n)).val : ℤ) - 1) a).mpr (by exact_mod_cast hdvd)
    have hχ :
        charValueNat (artinCharacter (dirichletGaloisCharacter ψ)) (v : ZMod (p ^ n)).val = 1 := by
      rw [charValueNat, dite_eq_right hm₀, h (Units.mk0 _ (Nat.cast_ne_zero.mpr hm₀))
        (by simpa using hnorm) (by simpa using hle), Units.val_one]
    rw [charValueNat_dirichletGaloisCharacter ψ hcop, inv_eq_one, hval] at hχ
    exact Units.ext (by rw [MulChar.coe_toUnitHom, hχ, Units.val_one])
  have hle : ψ.conductor ≤ p ^ a :=
    Nat.sInf_le hfac
  rw [hψ] at hle
  exact absurd (Nat.pow_lt_pow_right hp.one_lt ha) (not_lt.mpr hle)

/-- **The Galois character of a primitive Dirichlet character** modulo `p ^ n` has conductor
`p ^ n`. -/
lemma charConductorExponent_dirichletGaloisCharacter (hψ : ψ.IsPrimitive) :
    charConductorExponent (artinCharacter (dirichletGaloisCharacter ψ)) = n := by
  refine le_antisymm (Nat.sInf_le (isTrivialOnUnitsMod_dirichletGaloisCharacter ψ)) ?_
  refine le_csInf ⟨n, isTrivialOnUnitsMod_dirichletGaloisCharacter ψ⟩ fun a ha ↦ ?_
  exact not_lt.mp fun hlt ↦ not_isTrivialOnUnitsMod_dirichletGaloisCharacter hψ hlt ha

variable (ψ) in
lemma tateRootNumber_eq_gaussSum_div_of_eq (hφ : charConductorExponent φ = n) (hn : n ≠ 0)
    (hp : charValueNat φ p = 1) (hψ : ∀ m, p.Coprime m → charValueNat φ m = (ψ m)⁻¹) :
    tateRootNumber φ = gaussSum ψ ZMod.stdAddChar / ((p ^ n : ℕ) : ℂ) ^ (1 / 2 : ℂ) := by
  subst hφ
  exact tateRootNumber_eq_gaussSum_div ψ hn hp hψ

variable (ψ) in
lemma real_tateRootNumber_mul_tateRootNumber_of_eq (hφ : charConductorExponent φ = n)
    {χ' : ℝˣ →* ℂˣ} (hp : charValueNat φ p = 1) (hψ : ∀ m, p.Coprime m → charValueNat φ m = (ψ m)⁻¹)
    (hψ' : (χ' (-1) : ℂ) = ψ (-1)) : Real.tateRootNumber χ' * tateRootNumber φ = ψ.rootNumber := by
  subst hφ
  exact real_tateRootNumber_mul_tateRootNumber ψ hp hψ hψ'

/-- **The local root number at `p` of a primitive Dirichlet character** `ψ` modulo `p ^ n`, `n ≠ 0`,
is `τ(ψ) / √(p ^ n)`, for the Gauss sum `τ(ψ)`. -/
lemma galoisRootNumber_dirichletGaloisCharacter (hψ : ψ.IsPrimitive) (hn : n ≠ 0) : galoisRootNumber
    (dirichletGaloisCharacter ψ) = gaussSum ψ ZMod.stdAddChar / ((p ^ n : ℕ) : ℂ) ^ (1 / 2 : ℂ) :=
  tateRootNumber_eq_gaussSum_div_of_eq ψ (charConductorExponent_dirichletGaloisCharacter hψ) hn
    (charValueNat_self_dirichletGaloisCharacter ψ) fun _ hm ↦
      charValueNat_dirichletGaloisCharacter ψ hm

/-- **The local root numbers of a primitive Dirichlet character multiply to its root number**: for a
primitive Dirichlet character `ψ` modulo `p ^ n` and a character `χ'` of `ℝ^×` with
`χ'(-1) = ψ(-1)`, the local root numbers at `∞` and `p` multiply to the root number of `L(s, ψ)`,
Mathlib's `DirichletCharacter.rootNumber`. This pins the normalisation of the Artin map in the local
root numbers of Galois characters, as in the knowl's product formula. -/
lemma real_tateRootNumber_mul_galoisRootNumber (hψ : ψ.IsPrimitive) {χ' : ℝˣ →* ℂˣ}
    (hψ' : (χ' (-1) : ℂ) = ψ (-1)) :
    Real.tateRootNumber χ' * galoisRootNumber (dirichletGaloisCharacter ψ) = ψ.rootNumber :=
  real_tateRootNumber_mul_tateRootNumber_of_eq ψ (charConductorExponent_dirichletGaloisCharacter hψ)
    (charValueNat_self_dirichletGaloisCharacter ψ)
    (fun _ hm ↦ charValueNat_dirichletGaloisCharacter ψ hm) hψ'

variable (L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))

/-- The character of the **permutation representation** `ρ_L` of `Gal(ℚ̄_p/ℚ_p)` on the embeddings
of a finite extension `L` of `ℚ_p` in `ℚ̄_p` (LMFDB `lf.root_number`), by composition: the number of
embeddings fixed by `σ`. -/
noncomputable def permutationCharacter (σ : Field.absoluteGaloisGroup ℚ_[p]) : ℕ :=
  Nat.card {τ : L →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p] //
    ∀ y, DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) σ (τ y) = τ y}

variable [FiniteDimensional ℚ_[p] L] [IsGalois ℚ_[p] L]

/-- The **inflation** to `Gal(ℚ̄_p/ℚ_p)` of a character `η` of `Gal(L / ℚ_p)`, for a finite Galois
extension `L` of `ℚ_p` in `ℚ̄_p`. -/
noncomputable def inflateCharacter (η : (L ≃ₐ[ℚ_[p]] L) →* ℂˣ) :
    Field.absoluteGaloisGroup ℚ_[p] →ₜ* ℂˣ where
  toMonoidHom := η.comp (AlgEquiv.restrictNormalHom (K₁ := AlgebraicClosure ℚ_[p]) L)
  continuous_toFun := by
    refine MonoidHom.continuous_of_isOpen_ker _ (Subgroup.isOpen_mono (H₁ := L.fixingSubgroup)
      (fun σ hσ ↦ ?_) L.fixingSubgroup_isOpen)
    rw [← IntermediateField.restrictNormalHom_ker] at hσ
    exact MonoidHom.mem_ker.mpr ((congrArg η (MonoidHom.mem_ker.mp hσ)).trans (map_one η))

/-- The **local root number** `ε(L)` (LMFDB `lf.root_number`) of an abelian extension `L` of `ℚ_p`:
the product `∏_χ ε(χ)` of the local root numbers of the characters of `Gal(L / ℚ_p)`. Its
permutation representation `ρ_L` is the direct sum of these characters
(`natCast_permutationCharacter_eq_finsum`), so this is `ε(ρ_L)` by the multiplicativity of the local
root numbers, and for `L` not abelian over `ℚ_p` it does not have this meaning: it is then the
local root number of the maximal abelian subextension of `L`. -/
noncomputable def abelianRootNumber : ℂ :=
  ∏ᶠ χ : (L ≃ₐ[ℚ_[p]] L) →* ℂˣ, galoisRootNumber (inflateCharacter L χ)

/-- **The local root number of `ℚ_p` is `1`**: if `Gal(L / ℚ_p)` is trivial, `ε(L) = 1`. -/
lemma abelianRootNumber_of_subsingleton [Subsingleton (L ≃ₐ[ℚ_[p]] L)] :
    abelianRootNumber L = 1 := by
  refine finprod_eq_one_of_forall_eq_one fun χ ↦ ?_
  refine galoisRootNumber_eq_one fun σ _ ↦ ?_
  have h₁ : AlgEquiv.restrictNormalHom (K₁ := AlgebraicClosure ℚ_[p]) L σ = 1 :=
    Subsingleton.elim _ _
  exact (congrArg χ h₁).trans (map_one χ)

open scoped Classical in
lemma finsum_units_apply_eq_ite {G : Type*} [CommGroup G] [Finite G] (g : G) :
    ∑ᶠ χ : G →* ℂˣ, ((χ g : ℂˣ) : ℂ) = if g = 1 then (Nat.card G : ℂ) else 0 := by
  have hne : NeZero ((Monoid.exponent G : ℕ) : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  have hcard : Nat.card (G →* ℂˣ) = Nat.card G :=
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G ℂ
  have hfin : Finite (G →* ℂˣ) :=
    Nat.finite_of_card_ne_zero (hcard ▸ Nat.card_pos.ne')
  have hf : Fintype (G →* ℂˣ) :=
    Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  split_ifs with hg
  · simp [hg, ← Nat.card_eq_fintype_card, hcard]
  · rcases CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ hg with ⟨χ₀, hχ₀⟩
    have hs :
        ((χ₀ g : ℂˣ) : ℂ) * ∑ χ : G →* ℂˣ, ((χ g : ℂˣ) : ℂ) = ∑ χ : G →* ℂˣ, ((χ g : ℂˣ) : ℂ) := by
      rw [Finset.mul_sum]
      exact Fintype.sum_equiv (Equiv.mulLeft χ₀) _ _ fun χ ↦ by simp
    have h₀ : (((χ₀ g : ℂˣ) : ℂ) - 1) * ∑ χ : G →* ℂˣ, ((χ g : ℂˣ) : ℂ) = 0 := by
      rw [sub_mul, hs, one_mul, sub_self]
    exact (mul_eq_zero.mp h₀).resolve_left (sub_ne_zero.mpr fun h ↦ hχ₀ (Units.ext h))

open scoped IsMulCommutative in
/-- **The permutation representation of an abelian extension** `L` of `ℚ_p` is the sum of the
characters of `Gal(L / ℚ_p)`: at `σ`, the number of embeddings of `L` fixed by `σ` is
`∑_χ χ(σ|_L)`. -/
lemma natCast_permutationCharacter_eq_finsum [IsMulCommutative (L ≃ₐ[ℚ_[p]] L)]
    (σ : Field.absoluteGaloisGroup ℚ_[p]) : (permutationCharacter L σ : ℂ) =
      ∑ᶠ χ : (L ≃ₐ[ℚ_[p]] L) →* ℂˣ,
        ((χ (AlgEquiv.restrictNormalHom (K₁ := AlgebraicClosure ℚ_[p]) L σ) : ℂˣ) : ℂ) := by
  have hN : Normal ℚ_[p] L :=
    IsGalois.to_normal
  have hres (w : L) : ((AlgEquiv.restrictNormalHom (K₁ := AlgebraicClosure ℚ_[p]) L σ w : L) :
      AlgebraicClosure ℚ_[p]) =
        DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) σ (w : AlgebraicClosure ℚ_[p]) :=
    AlgEquiv.restrictNormal_commutes σ L w
  rw [finsum_units_apply_eq_ite (AlgEquiv.restrictNormalHom (K₁ := AlgebraicClosure ℚ_[p]) L σ)]
  split_ifs with hg
  · have hfix (τ : L →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]) (y : L) :
        DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) σ (τ y) = τ y := by
      have hmem : τ y ∈ L :=
        (SetLike.ext_iff.mp (AlgHom.fieldRange_of_normal τ) (τ y)).mp ⟨y, rfl⟩
      have h₂ : ((AlgEquiv.restrictNormalHom (K₁ := AlgebraicClosure ℚ_[p]) L σ ⟨τ y, hmem⟩ : L) :
          AlgebraicClosure ℚ_[p]) = DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) σ (τ y) :=
        hres ⟨τ y, hmem⟩
      rw [hg] at h₂
      exact h₂.symm
    have hs : Algebra.IsSeparable ℚ_[p] L :=
      IsGalois.to_isSeparable
    rw [permutationCharacter, Nat.card_congr (Equiv.subtypeUnivEquiv fun τ y ↦ hfix τ y),
      Nat.card_eq_fintype_card, AlgHom.card, IsGalois.card_aut_eq_finrank]
  · have hempty : IsEmpty {τ : L →ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p] //
        ∀ y, DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[p]/ℚ_[p])) σ (τ y) = τ y} := by
      refine ⟨fun ⟨τ, hτ⟩ ↦ hg (AlgEquiv.ext fun w ↦ Subtype.ext ?_)⟩
      rcases (SetLike.ext_iff.mp (AlgHom.fieldRange_of_normal τ) (w : AlgebraicClosure ℚ_[p])).mpr
        w.2 with ⟨y, hy⟩
      rw [AlgEquiv.one_apply, hres, ← hy]
      exact hτ y
    rw [permutationCharacter, Nat.card_of_isEmpty, Nat.cast_zero]

end Padic

namespace Real

lemma conjAe_mul_self : (conjAe * conjAe : ℂ ≃ₐ[ℝ] ℂ) = 1 :=
  AlgEquiv.ext fun z ↦ Complex.conj_conj z

/-- The **Artin map of `ℝ`**: `x ↦ 1` for `x > 0` and complex conjugation for `x < 0`. -/
noncomputable def artinSign : ℝˣ →* (ℂ ≃ₐ[ℝ] ℂ) where
  toFun x := if 0 < (x : ℝ) then 1 else conjAe
  map_one' := by simp
  map_mul' x y := by
    rcases lt_or_gt_of_ne x.ne_zero with hx | hx <;> rcases lt_or_gt_of_ne y.ne_zero with hy | hy
    · simp [hx.not_gt, hy.not_gt, mul_pos_of_neg_of_neg hx hy, conjAe_mul_self]
    · simp [hy]
    · simp [hx]
    · simp [hy]

lemma artinSign_neg_one : artinSign (-1) = conjAe := by
  have h : ¬(0 : ℝ) < ((-1 : ℝˣ) : ℝ) := by
    norm_num
  exact ite_eq_right h

/-- The **local root number** (LMFDB `lf.root_number`) of a character `χ` of `Gal(ℂ/ℝ)`: Tate's
local root number of the character `χ ∘ Art` of `ℝ^×`, which is `1` for the trivial character and
`-i` for the sign character, as in the knowl. -/
noncomputable def galoisRootNumber (χ : (ℂ ≃ₐ[ℝ] ℂ) →* ℂˣ) : ℂ :=
  tateRootNumber (χ.comp artinSign)

/-- **The trivial character of `Gal(ℂ/ℝ)` has local root number `1`.** -/
lemma galoisRootNumber_one : galoisRootNumber 1 = 1 := by
  simp [galoisRootNumber, tateRootNumber]

/-- **The sign character of `Gal(ℂ/ℝ)` has local root number `-i`**: a character `χ` of `Gal(ℂ/ℝ)`
with `χ(conj) ≠ 1`. -/
lemma galoisRootNumber_of_apply_conj_ne_one {χ : (ℂ ≃ₐ[ℝ] ℂ) →* ℂˣ} (h : χ conjAe ≠ 1) :
    galoisRootNumber χ = -I := by
  refine tateRootNumber_of_apply_neg_one_ne_one ?_
  rwa [MonoidHom.comp_apply, artinSign_neg_one]

/-- **The local root numbers of a primitive Dirichlet character multiply to its root number**, on
the Galois side (LMFDB `lf.root_number`): for a primitive Dirichlet character `ψ` modulo `p ^ n` and
a character `χ` of `Gal(ℂ/ℝ)` with `χ(conj) = ψ(-1)`, the local root numbers of `χ` and of the
character of `Gal(ℚ̄_p/ℚ_p)` of `ψ` multiply to the root number of `L(s, ψ)`. -/
lemma galoisRootNumber_mul_galoisRootNumber {p n : ℕ} [Fact p.Prime]
    {ψ : DirichletCharacter ℂ (p ^ n)} (hψ : ψ.IsPrimitive) {χ : (ℂ ≃ₐ[ℝ] ℂ) →* ℂˣ}
    (h : (χ conjAe : ℂ) = ψ (-1)) :
    galoisRootNumber χ * Padic.galoisRootNumber (Padic.dirichletGaloisCharacter ψ) = ψ.rootNumber :=
  Padic.real_tateRootNumber_mul_galoisRootNumber hψ <| by
    rwa [MonoidHom.comp_apply, artinSign_neg_one]

end Real
