/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Group.Equiv.Finite
import Mathlib.Data.FunLike.Fintype

/-!
# The abstract iso `C₂³ ⋊ C₃ ≅ A₄ × C₂` (C8)

The semidirect product of `C₂³ = (ZMod 2)³` by `C₃` acting by cyclic coordinate permutation is
isomorphic to `A₄ × C₂`. Maschke splits `𝔽₂³ = ⟨(1,1,1)⟩ ⊕ {Σ = 0}`: the `C₃`-fixed diagonal
`(1,1,1)` is central, giving the `C₂` factor; the sum-zero plane `V₄ ⋊ C₃ = A₄`.

This is the pure finite-group-theory endpoint used to name `Gal(X⁶−5X⁴−50X²+125)` as `A₄ × C₂`
(`6T6`). See `.mathlib-quality/decomposition.md`, Result R4 leaf L4.9, and `.mathlib-quality/tickets.md`,
T022.

## Foundation (done)

`A₄` itself is realised as an internal semidirect product: Mathlib's `alternatingGroup.kleinFour (Fin 4)`
(the normal `V₄`) has the order-3 subgroup `⟨c3⟩` (`c3 = (0 1 2)`) as a complement, so
`A4iso : kleinFour ⋊ ⟨c3⟩ ≃* A₄` (`SemidirectProduct.mulEquivSubgroup`).
-/

open Equiv Equiv.Perm

namespace IdealArithmetic.Galois

/-- Precomposition by `ρ⁻¹` as an additive automorphism of `S → ZMod 2`. -/
def precompAddAut {S : Type*} (ρ : Equiv.Perm S) : (S → ZMod 2) ≃+ (S → ZMod 2) where
  toFun v := v ∘ ρ.symm
  invFun v := v ∘ ρ
  left_inv v := by funext s; simp
  right_inv v := by funext s; simp
  map_add' _ _ := rfl

/-- **Precomposition automorphism**, as a genuine (covariant) group homomorphism
`Perm S →* MulAut (Multiplicative (S → ZMod 2))`, `ρ ↦ (v ↦ v ∘ ρ⁻¹)`. Using `ρ⁻¹` (rather than `ρ`)
makes it covariant, so it composes cleanly with other homs — this is the action a permutation of the
coordinate set induces on `C₂^S`. -/
noncomputable def precompAut {S : Type*} :
    Equiv.Perm S →* MulAut (Multiplicative (S → ZMod 2)) where
  toFun ρ := AddEquiv.toMultiplicative (precompAddAut ρ)
  map_one' := by ext v s; simp [precompAddAut, AddEquiv.toMultiplicative, pull_end]
  map_mul' ρ σ := by ext v s; simp [precompAddAut, AddEquiv.toMultiplicative]; rfl

/-- `precompAut ρ` sends `Multiplicative.ofAdd v` to `Multiplicative.ofAdd (v ∘ ρ.symm)`. -/
@[simp] theorem precompAut_ofAdd {S : Type*} (ρ : Equiv.Perm S) (v : S → ZMod 2) :
    precompAut ρ (Multiplicative.ofAdd v) = Multiplicative.ofAdd (v ∘ ρ.symm) := rfl

/-- The named target group `A₄ × C₂` (with `C₂ = Multiplicative (ZMod 2)`). -/
abbrev A4timesC2 : Type := alternatingGroup (Fin 4) × Multiplicative (ZMod 2)

/-- Sanity check: `|A₄ × C₂| = 24`. -/
theorem card_A4timesC2 : Nat.card A4timesC2 = 24 := by
  rw [A4timesC2, Nat.card_prod,
    alternatingGroup.card_of_card_eq_four (Nat.card_fin 4),
    Nat.card_eq_fintype_card]
  rfl

/-- The 3-cycle `(0 1 2)` as an element of `A₄` (a `C₃` generator complementing the Klein four). -/
def c3 : alternatingGroup (Fin 4) :=
  ⟨swap 0 1 * swap 1 2, mem_alternatingGroup.mpr (by decide)⟩

/-- The 3-cycle `c3` has order `3`. -/
theorem c3_order : orderOf c3 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  exact orderOf_eq_prime (by decide) (by decide)

/-- The Klein four subgroup `V₄` of `A₄` is normal. -/
theorem klein_normal : (alternatingGroup.kleinFour (Fin 4)).Normal :=
  alternatingGroup.normal_kleinFour (Nat.card_fin 4)

/-- `⟨c3⟩ = C₃` is a complement to the Klein four `V₄` in `A₄` (orders `3` and `4` are coprime,
`3·4 = 12 = |A₄|`). -/
theorem klein_compl : (alternatingGroup.kleinFour (Fin 4)).IsComplement' (Subgroup.zpowers c3) := by
  have hk : Nat.card (alternatingGroup.kleinFour (Fin 4)) = 4 :=
    alternatingGroup.kleinFour_card_of_card_eq_four (Nat.card_fin 4)
  have hz : Nat.card (Subgroup.zpowers c3) = 3 := by rw [Nat.card_zpowers, c3_order]
  apply Subgroup.isComplement'_of_coprime
  · rw [hk, hz, alternatingGroup.card_of_card_eq_four (Nat.card_fin 4)]
  · rw [hk, hz]; decide

/-- **`A₄` as an internal semidirect product `V₄ ⋊ C₃`** (`V₄ = kleinFour`, `C₃ = ⟨c3⟩`, acting by
conjugation). The endpoint used to identify the sum-zero plane of the block group with `A₄`. -/
noncomputable def A4iso :=
  letI := klein_normal
  SemidirectProduct.mulEquivSubgroup klein_compl

/-!
## The abstract iso `C₂³ ⋊ C₃ ≅ A₄ × C₂`

We realise `A₄ × C₂` as the semidirect product `C₂³ ⋊ C₃` with `C₃` acting by cyclic coordinate
permutation, then transport a single explicit lift and check bijectivity by `decide` (everything
in sight is a finite decidable structure). No abstract Maschke splitting is needed: the intertwining
map `blockHom` bakes the decomposition `𝔽₂³ = ⟨(1,1,1)⟩ ⊕ {Σ = 0}` into its formula, and the
compatibility with the two cyclic actions is a finite check.
-/

/-- Cyclic coordinate shift `(x,y,z) ↦ (z,x,y)` on `𝔽₂³`, as an additive automorphism of order 3. -/
def shiftAdd : (ZMod 2 × ZMod 2 × ZMod 2) ≃+ (ZMod 2 × ZMod 2 × ZMod 2) where
  toFun p := (p.2.2, p.1, p.2.1)
  invFun p := (p.2.1, p.2.2, p.1)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The cyclic shift as a multiplicative automorphism of `C₂³ = Multiplicative 𝔽₂³`. -/
def shiftMul : MulAut (Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)) :=
  AddEquiv.toMultiplicative shiftAdd

/-- The `C₃`-action on `C₂³` by cyclic coordinate permutation (`gen ↦ shift`). This is the action
under which `C₂³ ⋊ C₃ ≅ A₄ × C₂`; the trivial action would give the abelian `C₂³ × C₃` instead. -/
def cycAction : Multiplicative (ZMod 3) →* MulAut (Multiplicative (ZMod 2 × ZMod 2 × ZMod 2)) where
  toFun k := shiftMul ^ (Multiplicative.toAdd k).val
  map_one' := by decide
  map_mul' := by decide

/-- `C₂³ ⋊ C₃` with the cyclic action — the abstract group shape of
`Gal(X⁶ − 5X⁴ − 50X² + 125)` (`6T6`). -/
abbrev C2cubedC3 : Type :=
  Multiplicative (ZMod 2 × ZMod 2 × ZMod 2) ⋊[cycAction] Multiplicative (ZMod 3)

/-- The double transposition `(0 1)(2 3)` — a nonidentity Klein-four element of `A₄`. -/
def kleinU : alternatingGroup (Fin 4) := ⟨swap 0 1 * swap 2 3, mem_alternatingGroup.mpr (by decide)⟩
/-- The double transposition `(0 2)(1 3)`. -/
def kleinV : alternatingGroup (Fin 4) := ⟨swap 0 2 * swap 1 3, mem_alternatingGroup.mpr (by decide)⟩
/-- The double transposition `(0 3)(1 2)`. -/
def kleinW : alternatingGroup (Fin 4) := ⟨swap 0 3 * swap 1 2, mem_alternatingGroup.mpr (by decide)⟩

/-- The Klein-four image of `(x,y,z)`: the invariant `(x+y, y+z)` selects `1 / U / W / V`. This is
`𝔽₂³ ↠ {Σ = 0} ≅ V₄` (the sum-zero plane, `≅ V₄ ⊂ A₄`). -/
def kleinOf (p : ZMod 2 × ZMod 2 × ZMod 2) : alternatingGroup (Fin 4) :=
  if p.1 + p.2.1 = 0 then (if p.2.1 + p.2.2 = 0 then 1 else kleinU)
  else (if p.2.1 + p.2.2 = 0 then kleinW else kleinV)

/-- The intertwining hom `C₂³ →* A₄ × C₂`: the `V₄`-part is `kleinOf` (the sum-zero plane),
the `C₂`-part is the coordinate sum `Σ = x+y+z` (the `C₃`-fixed diagonal `⟨(1,1,1)⟩`). -/
def blockHom : Multiplicative (ZMod 2 × ZMod 2 × ZMod 2) →* A4timesC2 where
  toFun p := (kleinOf (Multiplicative.toAdd p),
    Multiplicative.ofAdd ((Multiplicative.toAdd p).1 + (Multiplicative.toAdd p).2.1 +
      (Multiplicative.toAdd p).2.2))
  map_one' := by decide
  map_mul' := by decide

/-- The complement hom `C₃ →* A₄ × C₂`, `gen ↦ (c3, 1)`. -/
def c3Hom : Multiplicative (ZMod 3) →* A4timesC2 where
  toFun k := (c3, 1) ^ (Multiplicative.toAdd k).val
  map_one' := by decide
  map_mul' := by decide

/-- `blockHom` intertwines the cyclic action with conjugation by `c3Hom` (finite check). -/
theorem cycAction_compat : ∀ g, blockHom.comp (MulEquiv.toMonoidHom (cycAction g)) =
    (MulEquiv.toMonoidHom (MulAut.conj (c3Hom g))).comp blockHom := by decide

/-- The universal lift `C₂³ ⋊ C₃ →* A₄ × C₂` from `blockHom` and `c3Hom`. -/
noncomputable def semidirectHom : C2cubedC3 →* A4timesC2 :=
  SemidirectProduct.lift blockHom c3Hom cycAction_compat

instance : Fintype C2cubedC3 := Fintype.ofEquiv _ SemidirectProduct.equivProd.symm
instance : DecidableEq C2cubedC3 := SemidirectProduct.equivProd.decidableEq

/-- **The abstract iso `C₂³ ⋊ C₃ ≅ A₄ × C₂`** (`6T6`). Both sides are finite of order 24; the
explicit lift `semidirectHom` is bijective by a finite `decide`. -/
noncomputable def C2cubedC3MulEquivA4timesC2 : C2cubedC3 ≃* A4timesC2 :=
  MulEquiv.ofBijective semidirectHom (by decide)

/-!
## Transport to an abstract block set: `C₂^S ⋊ C₃ ≅ A₄ × C₂`

For an arbitrary 3-element set `S` and an order-3 permutation `τ` of it, `C₂^S ⋊ C₃` with `C₃` acting
by precomposition-with-`τ` is `≅ A₄ × C₂`. This is the shape the Galois group `Gal(g(X²))` presents,
with `S = rootSet g` the three blocks and `τ` the `C₃`-block-permutation. We reduce it to
`C2cubedC3MulEquivA4timesC2` by choosing an indexing `e : Fin 3 ≃ S` that turns `τ` into the standard
shift, then `SemidirectProduct.congr`. -/

/-- The `+1` cyclic permutation of `Fin 3` (the standard order-3 block permutation). -/
def succ3 : Equiv.Perm (Fin 3) := Equiv.mk (· + 1) (· - 1) (by decide) (by decide)

/-- Every order-3 permutation of `Fin 3` is `succ3` or `succ3²` (finite check). -/
theorem eq_succ3_or_sq (ρ : Equiv.Perm (Fin 3)) (h3 : ρ ^ 3 = 1) (h1 : ρ ≠ 1) :
    ρ = succ3 ∨ ρ = succ3 ^ 2 := by revert ρ; decide

/-- **Choosing an adapted indexing.** For an order-3 `τ` on a 3-element set `S`, there is a bijection
`e : Fin 3 ≃ S` conjugating the standard shift `succ3` to `τ` (`τ ∘ e = e ∘ succ3`). Proven without a
"no fixed point" argument: transport an arbitrary indexing, then case on `succ3 / succ3²` and correct
the orientation by `swap 0 1` in the second case. -/
theorem exists_indexing {S : Type*} [Fintype S] [DecidableEq S] (hcard : Fintype.card S = 3)
    (τ : Equiv.Perm S) (hτ : orderOf τ = 3) :
    ∃ e : Fin 3 ≃ S, ∀ i, τ (e i) = e (succ3 i) := by
  have hτ3 : τ ^ 3 = 1 := hτ ▸ pow_orderOf_eq_one τ
  have hτ1 : τ ≠ 1 := by rintro rfl; simp at hτ
  have e₀ := (Fintype.equivFinOfCardEq hcard).symm
  let φ : Equiv.Perm S ≃* Equiv.Perm (Fin 3) :=
    { Equiv.permCongr e₀.symm with map_mul' := fun a b => by ext i; simp [Equiv.permCongr] }
  set ρ₀ := φ τ with hρ0
  have hconj : ∀ i, τ (e₀ i) = e₀ (ρ₀ i) := by
    intro i; simp only [hρ0, φ, MulEquiv.coe_mk, Equiv.permCongr_apply, Equiv.symm_symm,
      Equiv.apply_symm_apply]
  have hρ3 : ρ₀ ^ 3 = 1 := by rw [hρ0, ← map_pow, hτ3, map_one]
  have hρ1 : ρ₀ ≠ 1 := by
    rw [hρ0]; intro h; exact hτ1 (φ.injective (by rw [h, map_one]))
  rcases eq_succ3_or_sq ρ₀ hρ3 hρ1 with hc | hc
  · exact ⟨e₀, fun i => by rw [hconj i, hc]⟩
  · refine ⟨(swap (0 : Fin 3) 1).trans e₀, fun i => ?_⟩
    simp only [Equiv.trans_apply]
    rw [hconj (swap 0 1 i), hc]
    congr 1
    have hkey : succ3 ^ 2 * swap (0 : Fin 3) 1 = swap 0 1 * succ3 := by decide
    simpa [Equiv.Perm.mul_apply] using DFunLike.congr_fun hkey i

/-- The coordinate iso `C₂^S ≅ C₂³` induced by an indexing `e : Fin 3 ≃ S` (evaluation at
`e 0, e 1, e 2`). -/
def coordAdd {S : Type*} [DecidableEq S] (e : Fin 3 ≃ S) :
    (S → ZMod 2) ≃+ (ZMod 2 × ZMod 2 × ZMod 2) where
  toFun v := (v (e 0), v (e 1), v (e 2))
  invFun w := fun s => (![w.1, w.2.1, w.2.2] : Fin 3 → ZMod 2) (e.symm s)
  left_inv v := by
    funext s; simp only; rw [show s = e (e.symm s) from (e.apply_symm_apply s).symm]
    generalize e.symm s = j; rw [e.symm_apply_apply]; fin_cases j <;> rfl
  right_inv w := by simp [Equiv.symm_apply_apply]
  map_add' v w := rfl

/-- The coordinate iso as a `MulEquiv` of the multiplicative groups. -/
noncomputable def coordEquiv {S : Type*} [DecidableEq S] (e : Fin 3 ≃ S) :
    Multiplicative (S → ZMod 2) ≃* Multiplicative (ZMod 2 × ZMod 2 × ZMod 2) :=
  AddEquiv.toMultiplicative (coordAdd e)

/-- With an adapted indexing, `coordEquiv` conjugates precomposition-by-`τ` to the standard shift. -/
theorem coord_intertwine {S : Type*} [DecidableEq S] (e : Fin 3 ≃ S) (τ : Equiv.Perm S)
    (he : ∀ i, τ (e i) = e (succ3 i)) (x : Multiplicative (S → ZMod 2)) :
    coordEquiv e (precompAut τ x) = shiftMul (coordEquiv e x) := by
  have hsymm : ∀ j : Fin 3, τ.symm (e j) = e (succ3.symm j) := by
    intro j; have := he (succ3.symm j); rw [Equiv.apply_symm_apply] at this
    rw [← this, Equiv.symm_apply_apply]
  obtain ⟨w, rfl⟩ := Multiplicative.ofAdd.surjective x
  show Multiplicative.ofAdd (coordAdd e (w ∘ τ.symm))
    = Multiplicative.ofAdd (shiftAdd (coordAdd e w))
  congr 1
  show (w (τ.symm (e 0)), w (τ.symm (e 1)), w (τ.symm (e 2)))
    = ((w (e 0), w (e 1), w (e 2)).2.2, (w (e 0), w (e 1), w (e 2)).1, (w (e 0), w (e 1), w (e 2)).2.1)
  rw [hsymm 0, hsymm 1, hsymm 2, show succ3.symm 0 = 2 by decide,
     show succ3.symm 1 = 0 by decide, show succ3.symm 2 = 1 by decide]

/-- The power version of `coord_intertwine`: `coordEquiv` conjugates `(precompAut τ)ⁿ` to `shiftMulⁿ`. -/
theorem coord_pow {S : Type*} [DecidableEq S] (e : Fin 3 ≃ S) (τ : Equiv.Perm S)
    (he : ∀ i, τ (e i) = e (succ3 i)) :
    ∀ (n : ℕ) (x : Multiplicative (S → ZMod 2)),
      coordEquiv e ((precompAut τ ^ n) x) = (shiftMul ^ n) (coordEquiv e x) := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ m ih =>
      intro x
      rw [pow_succ, pow_succ]
      show coordEquiv e ((precompAut τ ^ m) (precompAut τ x))
        = (shiftMul ^ m) (shiftMul (coordEquiv e x))
      rw [ih, coord_intertwine e τ he]

/-- A homomorphism `Multiplicative (ZMod 3) →* M` from an element `x` with `x³ = 1` (`gen ↦ x`). -/
noncomputable def zmodPowHom {M : Type*} [Group M] (x : M) (hx : x ^ 3 = 1) :
    Multiplicative (ZMod 3) →* M where
  toFun k := x ^ (Multiplicative.toAdd k).val
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul]; rw [← pow_add, pow_eq_pow_iff_modEq]
    exact Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one hx)
      (by rw [ZMod.val_add]; exact Nat.mod_modEq _ _)

/-- `zmodPowHom x hx` sends the generator `Multiplicative.ofAdd 1` to `x`. -/
@[simp] theorem zmodPowHom_gen {M : Type*} [Group M] (x : M) (hx : x ^ 3 = 1) :
    zmodPowHom x hx (Multiplicative.ofAdd 1) = x := by
  simp [zmodPowHom, ZMod.val_one]

/-- The `C₃`-action on `C₂^S` by precomposition-with-`τ` (`gen ↦ v ↦ v ∘ τ⁻¹`), packaged as a hom
from `Multiplicative (ZMod 3)`. Needs `τ³ = 1` for well-definedness. -/
noncomputable def blockAction {S : Type*} [DecidableEq S] (τ : Equiv.Perm S) (hτ3 : τ ^ 3 = 1) :
    Multiplicative (ZMod 3) →* MulAut (Multiplicative (S → ZMod 2)) :=
  zmodPowHom (precompAut τ) (by rw [← map_pow, hτ3, map_one])

/-- **`C₂^S ⋊ C₃ ≅ A₄ × C₂`** for a 3-element block set `S` and an order-3 block permutation `τ`
acting by precomposition. The concrete-abstract endpoint feeding the `Gal(g(X²))` identification. -/
theorem threeBlockIso {S : Type*} [Fintype S] [DecidableEq S] (hcard : Fintype.card S = 3)
    (τ : Equiv.Perm S) (hτ : orderOf τ = 3) (hτ3 : τ ^ 3 = 1) :
    Nonempty ((Multiplicative (S → ZMod 2)) ⋊[blockAction τ hτ3] (Multiplicative (ZMod 3))
      ≃* A4timesC2) := by
  obtain ⟨e, he⟩ := exists_indexing hcard τ hτ
  have compat : ∀ k, (blockAction τ hτ3 k).trans (coordEquiv e)
      = (coordEquiv e).trans (cycAction k) := fun k =>
    MulEquiv.ext fun x => coord_pow e τ he (Multiplicative.toAdd k).val x
  exact ⟨(SemidirectProduct.congr (coordEquiv e) (MulEquiv.refl _) compat).trans
    C2cubedC3MulEquivA4timesC2⟩

/-- **Semiconjugacy is preserved by powers.** If a `MulEquiv` `e` intertwines the automorphisms
`a` and `b` (`e ∘ a = b ∘ e`), then it intertwines `aⁿ` and `bⁿ` for every `n`. The inductive
engine that lifts a base-case action-compatibility (`n = 1`) to full `C₃`-equivariance. -/
theorem conj_pow_trans {M N : Type*} [Group M] [Group N] (e : M ≃* N) (a : MulAut M) (b : MulAut N)
    (base : ∀ x, e (a x) = b (e x)) (n : ℕ) : ∀ x, e ((a ^ n) x) = (b ^ n) (e x) := by
  induction n with
  | zero => intro x; simp
  | succ k ih =>
    intro x; rw [pow_succ', pow_succ']
    show e (a ((a ^ k) x)) = b ((b ^ k) (e x))
    rw [base, ih]

/-- `Multiplicative.ofAdd 1` generates `Multiplicative (ZMod 3)`: every `y` is `(ofAdd 1) ^ y.val`
(where `y.val` is the canonical representative in `{0,1,2}`). The discrete-log identity used to reduce
`C₃`-equivariance to its generator. -/
theorem ofAdd_one_pow_toAdd_val (y : Multiplicative (ZMod 3)) :
    (Multiplicative.ofAdd (1 : ZMod 3)) ^ (Multiplicative.toAdd y).val = y := by
  rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]; rfl

end IdealArithmetic.Galois
