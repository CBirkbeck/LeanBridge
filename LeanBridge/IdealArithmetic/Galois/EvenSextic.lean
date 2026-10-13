/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanBridge.IdealArithmetic.Galois.Certificate
import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# Even sextics `f = g(X²)`: block system and the Frobenius-generated kernel (Route G)

Reusable machinery for an even polynomial `f = g.comp (X ^ 2)`. The squaring map `α ↦ α²` sends the
roots of `f` to the roots of `g`, giving a `Gal f`-invariant block system (the `±` pairs) and hence an
embedding `Gal f ↪ C₂ ≀ (Gal g)`. When `g` is an irreducible cyclic cubic (`disc g` a square), the
block action is `Gal g = C₃`, so `Gal f ↪ C₂³ ⋊ C₃` (order 24, the upper bound). The **kernel**
`K = ker(restrictComp) = Gal(L/M)` is the sign-change subgroup `↪ (ZMod 2)³`; Route G *generates* it to
all of `C₂³` from a single `p = 13` Frobenius involution (via `Certificate.lean`) together with the
cubic's `C₃` symmetry — the lower bound — avoiding multiquadratic Kummer theory.

This file holds the general lemmas; the specific showcase is in `Examples/DegSixA4C2.lean`.
See `.mathlib-quality/decomposition.md`, Result R4, and `.mathlib-quality/tickets.md`, T015–T020.
-/

open Polynomial

namespace IdealArithmetic.Galois.EvenSextic

variable {R : Type*} [CommRing R]

/-- **(L4.2 monicity).** `g(X²)` is monic when `g` is. -/
theorem monic_comp_X_sq [Nontrivial R] {g : R[X]} (hg : g.Monic) : (g.comp (X ^ 2)).Monic :=
  hg.comp (monic_X_pow 2) (by simp)

/-- **(L4.2 degree).** `deg (g(X²)) = 2 · deg g` (over a domain, e.g. `ℤ`, `ℚ`, `ZMod p`). -/
theorem natDegree_comp_X_sq [Nontrivial R] [NoZeroDivisors R] (g : R[X]) :
    (g.comp (X ^ 2)).natDegree = 2 * g.natDegree := by
  rw [natDegree_comp, natDegree_X_pow, mul_comm]

/-- **(L4.2 transport helper).** Transport a Galois group along a polynomial equality. Built with
`subst` (not `rw`): an inline rewrite along `p = q` triggers a "motive is not type correct" failure
because `Polynomial.Gal`'s splitting-`Fact` instance depends on the polynomial (red-team ATTACK-1). -/
noncomputable def galCongr {F : Type*} [Field F] {p q : F[X]} (h : p = q) : p.Gal ≃* q.Gal := by
  subst h; exact MulEquiv.refl _

open scoped Classical in
/-- Transport of the root-permutation partition across `galCongr`: for `p = q`, the image
`galCongr h σ` acts on the roots of `q` with the same cycle-type partition as `σ` on the roots of `p`.
Used to carry a Frobenius certificate stated for `f` to the composed form `g(X²) = f`. -/
theorem galActionHom_partition_galCongr {F : Type*} [Field F] {p q : F[X]} (h : p = q)
    [Fact ((p.map (algebraMap F p.SplittingField)).Splits)]
    [Fact ((q.map (algebraMap F q.SplittingField)).Splits)] (σ : p.Gal) :
    (Gal.galActionHom q q.SplittingField (galCongr h σ)).partition.parts
      = (Gal.galActionHom p p.SplittingField σ).partition.parts := by
  subst h
  rfl

/-- **(L4.3) The Galois-group order factors through the composition.** For any `p, q` with
`q.natDegree ≠ 0`, the restriction `restrictComp : (p.comp q).Gal ↠ p.Gal` is surjective
(`restrictComp_surjective`), so by Lagrange + the first isomorphism theorem
`|Gal(p∘q)| = |Gal p| · |ker restrictComp|`. For the even sextic `f = g(X²)` this reads
`|Gal f| = |Gal g| · |K|` with `K = Gal(L/M)` the sign-change kernel. -/
theorem card_gal_comp_eq {F : Type*} [Field F] (p q : F[X]) (hq : q.natDegree ≠ 0) :
    Nat.card (p.comp q).Gal
      = Nat.card p.Gal * Nat.card (MonoidHom.ker (Gal.restrictComp p q hq)) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (MonoidHom.ker (Gal.restrictComp p q hq))]
  congr 1
  exact Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective _ (Gal.restrictComp_surjective p q hq)).toEquiv

/-! ### The `±`-block system on the roots of an even polynomial `h(X²)` (Route G, L4.4)

For `p = h.comp (X²)` and `L = p.SplittingField`, negation `x ↦ -x` is an involution on
`rootSet p L` whose orbits are the `±`-pairs (the blocks). The honest Galois action
`galActionAux` satisfies `↑(σ • x) = σ ↑x` by `rfl`, so it commutes with negation, and for a
kernel element `σ` (fixing the roots of `h`, i.e. the block-squares) `σ • x ∈ {x, -x}`: this is
the sign coordinate. -/

section EvenPoly

variable {F : Type*} [Field F] (h : F[X])

/-- Negation as an involution on `rootSet (h(X²)) L`: since `(-x)² = x²`, if `x` is a root of
`h(X²)` then so is `-x`. This is the `±`-pairing whose orbits are the Awtrey–Jakes blocks. -/
noncomputable def negRoot (x : (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField) :
    (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField :=
  ⟨-(x : (h.comp (X ^ 2)).SplittingField), by
    obtain ⟨hne, hx⟩ := mem_rootSet.mp x.2
    rw [mem_rootSet]
    exact ⟨hne, by simpa [aeval_comp, neg_sq] using hx⟩⟩

@[simp] theorem negRoot_val (x : (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField) :
    (negRoot h x : (h.comp (X ^ 2)).SplittingField) = -(x : (h.comp (X ^ 2)).SplittingField) :=
  rfl

theorem negRoot_involutive : Function.Involutive (negRoot h) := fun x => Subtype.ext (by simp)

variable (hq : (X ^ 2 : F[X]).natDegree ≠ 0)

/-- **Kernel fixes the block-squares.** An element `σ ∈ ker(restrictComp)` fixes every root of `h`
in `L` (the squares `θ` of the roots of `h(X²)`): `restrictComp = restrict h L`, and
`restrict_smul` says `↑(restrict h L σ • θ) = σ θ`; since `restrict h L σ = 1`, this is `θ`. -/
theorem fixes_rootSet_of_mem_ker {σ : (h.comp (X ^ 2)).Gal}
    (hσ : σ ∈ MonoidHom.ker (Gal.restrictComp h (X ^ 2) hq))
    (x : h.rootSet (h.comp (X ^ 2)).SplittingField) :
    σ (x : (h.comp (X ^ 2)).SplittingField) = (x : (h.comp (X ^ 2)).SplittingField) := by
  have : Fact ((h.map (algebraMap F (h.comp (X ^ 2)).SplittingField)).Splits) :=
    ⟨Gal.splits_in_splittingField_of_comp h (X ^ 2) hq⟩
  have hkey := Gal.restrict_smul (p := h) (E := (h.comp (X ^ 2)).SplittingField) σ x
  rw [show Gal.restrict h (h.comp (X ^ 2)).SplittingField σ
      = Gal.restrictComp h (X ^ 2) hq σ from rfl, MonoidHom.mem_ker.mp hσ, one_smul] at hkey
  exact hkey.symm

/-- **Roots generate `L`.** Two Galois elements agreeing on every root of `h(X²)` are equal
(`SplittingField.adjoin_rootSet` + `AlgHom.ext_of_adjoin_eq_top`). This is the injectivity core. -/
theorem eq_of_agrees_on_rootSet {σ τ : (h.comp (X ^ 2)).Gal}
    (H : ∀ x : (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField,
      σ (x : (h.comp (X ^ 2)).SplittingField) = τ (x : (h.comp (X ^ 2)).SplittingField)) :
    σ = τ := by
  have hAlg : σ.toAlgHom = τ.toAlgHom :=
    AlgHom.ext_of_adjoin_eq_top (Polynomial.SplittingField.adjoin_rootSet (h.comp (X ^ 2)))
      fun x hx => H ⟨x, hx⟩
  ext x
  exact AlgHom.ext_iff.mp hAlg x

/-- The **squaring map** on roots: `x ↦ x²` sends a root of `h(X²)` to a root of `h` (its block
label). The fibres are the `±`-pairs. -/
noncomputable def sqRoot (x : (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField) :
    h.rootSet (h.comp (X ^ 2)).SplittingField :=
  ⟨(x : (h.comp (X ^ 2)).SplittingField) ^ 2, by
    rw [mem_rootSet]
    obtain ⟨hne, hx⟩ := mem_rootSet.mp x.2
    refine ⟨fun hh => hne (by rw [hh, zero_comp]), ?_⟩
    simpa [aeval_comp, map_pow, aeval_X] using hx⟩

@[simp] theorem sqRoot_val (x : (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField) :
    (sqRoot h x : (h.comp (X ^ 2)).SplittingField) = (x : (h.comp (X ^ 2)).SplittingField) ^ 2 :=
  rfl

/-- **Kernel elements act within blocks.** For `σ ∈ ker(restrictComp)` and a root `x` of `h(X²)`,
`(σ x)² = σ(x²) = x²` (the block-square is fixed), so `σ x = x` or `σ x = -x`. -/
theorem apply_eq_or_eq_neg_of_mem_ker {σ : (h.comp (X ^ 2)).Gal}
    (hσ : σ ∈ MonoidHom.ker (Gal.restrictComp h (X ^ 2) hq))
    (x : (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField) :
    σ (x : (h.comp (X ^ 2)).SplittingField) = (x : (h.comp (X ^ 2)).SplittingField)
      ∨ σ (x : (h.comp (X ^ 2)).SplittingField) = -(x : (h.comp (X ^ 2)).SplittingField) := by
  have hθ := fixes_rootSet_of_mem_ker h hq hσ (sqRoot h x)
  rw [sqRoot_val, map_pow] at hθ
  have hfac :
      (σ (x : (h.comp (X ^ 2)).SplittingField) - (x : (h.comp (X ^ 2)).SplittingField))
        * (σ (x : (h.comp (X ^ 2)).SplittingField) + (x : (h.comp (X ^ 2)).SplittingField)) = 0 := by
    linear_combination hθ
  rcases mul_eq_zero.mp hfac with h' | h'
  · exact Or.inl (sub_eq_zero.mp h')
  · exact Or.inr (eq_neg_of_add_eq_zero_left h')

/-- **The squaring map is surjective:** every root `θ` of `h` has a square root among the roots of
`h(X²)`. Since `θ` is a root of `h`, `X² - θ` divides `h(X²)`, which splits in `L`; hence `X² - θ`
splits and has a root `x` with `x² = θ`. -/
theorem sqRoot_surjective (hmon : h.Monic) : Function.Surjective (sqRoot h) := by
  intro θ
  set L := (h.comp (X ^ 2)).SplittingField
  obtain ⟨hne, hθ⟩ := mem_rootSet.mp θ.2
  have hdvd1 : (X - C (θ : L)) ∣ h.map (algebraMap F L) := by
    rwa [dvd_iff_isRoot, IsRoot.def, eval_map, ← aeval_def]
  obtain ⟨k, hk⟩ := hdvd1
  have hdvd2 : (X ^ 2 - C (θ : L)) ∣ (h.comp (X ^ 2)).map (algebraMap F L) := by
    refine ⟨k.comp (X ^ 2), ?_⟩
    rw [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X, hk, mul_comp, sub_comp,
      X_comp, C_comp]
  have hp0 : (h.comp (X ^ 2)).map (algebraMap F L) ≠ 0 :=
    ((monic_comp_X_sq hmon).map (algebraMap F L)).ne_zero
  have hsplit2 : Splits (X ^ 2 - C (θ : L)) :=
    (Polynomial.SplittingField.splits (h.comp (X ^ 2))).of_dvd hp0 hdvd2
  have hdeg : (X ^ 2 - C (θ : L)).degree ≠ 0 := by
    rw [degree_X_pow_sub_C (by norm_num)]; decide
  obtain ⟨x, hx⟩ := hsplit2.exists_eval_eq_zero hdeg
  have hx2 : x ^ 2 = (θ : L) :=
    sub_eq_zero.mp (by simpa [eval_sub, eval_pow, eval_X, eval_C] using hx)
  have hxroot : x ∈ (h.comp (X ^ 2)).rootSet L := by
    rw [mem_rootSet]
    refine ⟨(monic_comp_X_sq hmon).ne_zero, ?_⟩
    rw [aeval_comp]
    simp only [map_pow, aeval_X]
    rw [hx2]; exact hθ
  exact ⟨⟨x, hxroot⟩, Subtype.ext (by rw [sqRoot_val]; exact hx2)⟩

/-- A chosen square root for each block: a section of the surjective squaring map. -/
noncomputable def sqSection (hmon : h.Monic) :
    h.rootSet (h.comp (X ^ 2)).SplittingField →
      (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField :=
  Function.surjInv (sqRoot_surjective h hmon)

@[simp] theorem sqRoot_sqSection (hmon : h.Monic)
    (θ : h.rootSet (h.comp (X ^ 2)).SplittingField) : sqRoot h (sqSection h hmon θ) = θ :=
  Function.surjInv_eq _ _

open scoped Classical in
/-- The **block-sign** of `σ`: on each block `θ`, `0` if `σ` fixes the chosen square root
`sqSection θ`, `1` if it flips it. Restricted to the kernel `K` it is an injective homomorphism
`K → (rootSet h L → ZMod 2)`, whence `|K| ≤ 2^{deg h}` and (once surjective) `= 2^{deg h}`. -/
noncomputable def blockSign (hmon : h.Monic) (σ : (h.comp (X ^ 2)).Gal)
    (θ : h.rootSet (h.comp (X ^ 2)).SplittingField) : ZMod 2 :=
  if σ (sqSection h hmon θ : (h.comp (X ^ 2)).SplittingField)
      = (sqSection h hmon θ : (h.comp (X ^ 2)).SplittingField) then 0 else 1

/-- **(L4.4, injectivity).** The block-sign is injective on the kernel: two elements with the same
signs agree on every chosen square root, hence (each acting within blocks) on every root, hence
everywhere since the roots generate `L`. -/
theorem blockSign_injective (hmon : h.Monic) :
    Function.Injective
      (fun σ : ↥(MonoidHom.ker (Gal.restrictComp h (X ^ 2) hq)) =>
        blockSign h hmon (σ : (h.comp (X ^ 2)).Gal)) := by
  classical
  intro σ τ hστ
  apply Subtype.ext
  apply eq_of_agrees_on_rootSet h
  intro y
  have hsq : ((sqSection h hmon (sqRoot h y) : (h.comp (X ^ 2)).SplittingField)) ^ 2
      = (y : (h.comp (X ^ 2)).SplittingField) ^ 2 := by
    simpa only [sqRoot_val] using congrArg Subtype.val (sqRoot_sqSection h hmon (sqRoot h y))
  have hrep : (σ : (h.comp (X ^ 2)).Gal) (sqSection h hmon (sqRoot h y) :
        (h.comp (X ^ 2)).SplittingField)
      = (τ : (h.comp (X ^ 2)).Gal) (sqSection h hmon (sqRoot h y) :
        (h.comp (X ^ 2)).SplittingField) := by
    have hσv := apply_eq_or_eq_neg_of_mem_ker h hq σ.2 (sqSection h hmon (sqRoot h y))
    have hτv := apply_eq_or_eq_neg_of_mem_ker h hq τ.2 (sqSection h hmon (sqRoot h y))
    have key := congrFun hστ (sqRoot h y)
    simp only [blockSign] at key
    by_cases hσc : (σ : (h.comp (X ^ 2)).Gal) (sqSection h hmon (sqRoot h y) :
          (h.comp (X ^ 2)).SplittingField) = (sqSection h hmon (sqRoot h y) :
          (h.comp (X ^ 2)).SplittingField) <;>
      by_cases hτc : (τ : (h.comp (X ^ 2)).Gal) (sqSection h hmon (sqRoot h y) :
          (h.comp (X ^ 2)).SplittingField) = (sqSection h hmon (sqRoot h y) :
          (h.comp (X ^ 2)).SplittingField)
    · rw [hσc, hτc]
    · rw [if_pos hσc, if_neg hτc] at key; exact absurd key (by decide)
    · rw [if_neg hσc, if_pos hτc] at key; exact absurd key (by decide)
    · rcases hσv with h1 | h1
      · exact absurd h1 hσc
      · rcases hτv with h2 | h2
        · exact absurd h2 hτc
        · rw [h1, h2]
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with hy | hy
  · rwa [← hy]
  · rw [hy, map_neg, map_neg] at hrep; exact neg_injective hrep

/-- **(L4.4) `|K| ≤ 2^{deg h}`** — from injectivity of the block-sign into `rootSet h L → ZMod 2`. -/
theorem card_ker_le (hmon : h.Monic) :
    Nat.card (MonoidHom.ker (Gal.restrictComp h (X ^ 2) hq)) ≤ 2 ^ h.natDegree := by
  calc Nat.card (MonoidHom.ker (Gal.restrictComp h (X ^ 2) hq))
      ≤ Nat.card (h.rootSet (h.comp (X ^ 2)).SplittingField → ZMod 2) :=
        Nat.card_le_card_of_injective _ (blockSign_injective h hq hmon)
    _ = 2 ^ Nat.card (h.rootSet (h.comp (X ^ 2)).SplittingField) := by
        rw [Nat.card_fun, Nat.card_zmod]
    _ ≤ 2 ^ h.natDegree := by
        apply Nat.pow_le_pow_right (by norm_num)
        rw [Nat.card_coe_set_eq]
        exact Polynomial.ncard_rootSet_le h _

/-- **(L4.4, homomorphism).** On the kernel the block-sign is additive: `blockSign(στ) = blockSign σ
+ blockSign τ` (signs compose). Needs nondegenerate blocks (`x ≠ -x`, i.e. no root is `0` and char
≠ 2) so that "flip" is well-defined. -/
theorem blockSign_mul (hmon : h.Monic)
    (hnd : ∀ x : (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField,
      (x : (h.comp (X ^ 2)).SplittingField) ≠ -(x : (h.comp (X ^ 2)).SplittingField))
    {σ τ : (h.comp (X ^ 2)).Gal}
    (hσ : σ ∈ MonoidHom.ker (Gal.restrictComp h (X ^ 2) hq))
    (hτ : τ ∈ MonoidHom.ker (Gal.restrictComp h (X ^ 2) hq)) :
    blockSign h hmon (σ * τ) = blockSign h hmon σ + blockSign h hmon τ := by
  classical
  funext θ
  simp only [blockSign, Pi.add_apply]
  have hane := hnd (sqSection h hmon θ)
  have hσv := apply_eq_or_eq_neg_of_mem_ker h hq hσ (sqSection h hmon θ)
  have hτv := apply_eq_or_eq_neg_of_mem_ker h hq hτ (sqSection h hmon θ)
  have hmul : (σ * τ) (sqSection h hmon θ : (h.comp (X ^ 2)).SplittingField)
      = σ (τ (sqSection h hmon θ : (h.comp (X ^ 2)).SplittingField)) := rfl
  rw [hmul]
  rcases hτv with hτv | hτv <;> rcases hσv with hσv | hσv <;>
    simp only [hτv, hσv, map_neg, neg_neg, if_true, if_neg (Ne.symm hane)] <;> decide

/-! ### Conjugation covariance (Route G, L4.6): the block-action permutes the sign coordinates -/

/-- The honest action of `σ` on the roots of `h(X²)` (`x ↦ σ x`). -/
noncomputable def fRoot (σ : (h.comp (X ^ 2)).Gal)
    (x : (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField) :
    (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField :=
  ⟨σ (x : (h.comp (X ^ 2)).SplittingField), by
    rw [mem_rootSet]; obtain ⟨hne, hx⟩ := mem_rootSet.mp x.2
    exact ⟨hne, by rw [aeval_algHom_apply, hx, map_zero]⟩⟩

@[simp] theorem fRoot_val (σ : (h.comp (X ^ 2)).Gal)
    (x : (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField) :
    (fRoot h σ x : (h.comp (X ^ 2)).SplittingField) = σ (x : (h.comp (X ^ 2)).SplittingField) :=
  rfl

/-- The honest action of `σ` on the roots of `h` (the block labels). -/
noncomputable def hRoot (σ : (h.comp (X ^ 2)).Gal)
    (x : h.rootSet (h.comp (X ^ 2)).SplittingField) :
    h.rootSet (h.comp (X ^ 2)).SplittingField :=
  ⟨σ (x : (h.comp (X ^ 2)).SplittingField), by
    rw [mem_rootSet]; obtain ⟨hne, hx⟩ := mem_rootSet.mp x.2
    exact ⟨hne, by rw [aeval_algHom_apply, hx, map_zero]⟩⟩

@[simp] theorem hRoot_val (σ : (h.comp (X ^ 2)).Gal)
    (x : h.rootSet (h.comp (X ^ 2)).SplittingField) :
    (hRoot h σ x : (h.comp (X ^ 2)).SplittingField) = σ (x : (h.comp (X ^ 2)).SplittingField) :=
  rfl

/-- The honest action of `σ` on the roots of `h` (the block labels), packaged as a permutation
(inverse is the action of `σ⁻¹`). -/
noncomputable def hRootEquiv (σ : (h.comp (X ^ 2)).Gal) :
    Equiv.Perm (h.rootSet (h.comp (X ^ 2)).SplittingField) where
  toFun := hRoot h σ
  invFun := hRoot h σ⁻¹
  left_inv x := by
    apply Subtype.ext
    simp only [hRoot_val]
    rw [show (σ⁻¹) (σ (x : (h.comp (X ^ 2)).SplittingField))
        = (σ⁻¹ * σ) (x : (h.comp (X ^ 2)).SplittingField) from rfl, inv_mul_cancel]; rfl
  right_inv x := by
    apply Subtype.ext
    simp only [hRoot_val]
    rw [show σ ((σ⁻¹) (x : (h.comp (X ^ 2)).SplittingField))
        = (σ * σ⁻¹) (x : (h.comp (X ^ 2)).SplittingField) from rfl, mul_inv_cancel]; rfl

@[simp] theorem hRootEquiv_apply (σ : (h.comp (X ^ 2)).Gal)
    (x : h.rootSet (h.comp (X ^ 2)).SplittingField) :
    hRootEquiv h σ x = hRoot h σ x := rfl

theorem hRoot_one (x : h.rootSet (h.comp (X ^ 2)).SplittingField) : hRoot h 1 x = x :=
  Subtype.ext rfl

theorem hRoot_mul (σ τ : (h.comp (X ^ 2)).Gal)
    (x : h.rootSet (h.comp (X ^ 2)).SplittingField) :
    hRoot h (σ * τ) x = hRoot h σ (hRoot h τ x) :=
  Subtype.ext rfl

/-- The block-label action as a group homomorphism `Gal(h(X²)) →* Perm(rootSet h)`. -/
noncomputable def hRootHom :
    (h.comp (X ^ 2)).Gal →* Equiv.Perm (h.rootSet (h.comp (X ^ 2)).SplittingField) where
  toFun := hRootEquiv h
  map_one' := by ext x; simp [hRoot_one]
  map_mul' σ τ := by ext x; simp [hRoot_mul]

/-- **The `hRoot ↔ restrictComp` link.** The honest block-permutation `hRootEquiv σ` is the honest
Galois action of `restrictComp σ ∈ Gal h` on the roots of `h` in `L`. (`restrict_smul`: for
`σ ∈ Gal(L/F)` the action of `restrict h L σ = restrictComp σ` on `rootSet h L` sends `x ↦ σ x`.) -/
theorem hRootEquiv_eq_galActionHom_restrictComp (σ : (h.comp (X ^ 2)).Gal) :
    haveI : Fact ((h.map (algebraMap F (h.comp (X ^ 2)).SplittingField)).Splits) :=
      ⟨Gal.splits_in_splittingField_of_comp h (X ^ 2) hq⟩
    hRootEquiv h σ = Gal.galActionHom h (h.comp (X ^ 2)).SplittingField
      (Gal.restrictComp h (X ^ 2) hq σ) := by
  have : Fact ((h.map (algebraMap F (h.comp (X ^ 2)).SplittingField)).Splits) :=
    ⟨Gal.splits_in_splittingField_of_comp h (X ^ 2) hq⟩
  ext x
  rw [hRootEquiv_apply, hRoot_val,
    show (Gal.galActionHom h (h.comp (X ^ 2)).SplittingField (Gal.restrictComp h (X ^ 2) hq σ)) x
      = (Gal.restrictComp h (X ^ 2) hq σ) • x from rfl]
  exact (Gal.restrict_smul (p := h) (E := (h.comp (X ^ 2)).SplittingField) σ x).symm

/-- The block-permutation of `σ` and the `Gal h`-restriction `restrictComp σ` have the same order
(the honest `Gal h`-action on the roots of `h` is faithful). Lets the `C₃`-symmetry of the resolvent
descend to an order-3 block permutation. -/
theorem orderOf_hRootEquiv (σ : (h.comp (X ^ 2)).Gal) :
    orderOf (hRootEquiv h σ) = orderOf (Gal.restrictComp h (X ^ 2) hq σ) := by
  have : Fact ((h.map (algebraMap F (h.comp (X ^ 2)).SplittingField)).Splits) :=
    ⟨Gal.splits_in_splittingField_of_comp h (X ^ 2) hq⟩
  rw [hRootEquiv_eq_galActionHom_restrictComp h hq σ]
  exact orderOf_injective (Gal.galActionHom h (h.comp (X ^ 2)).SplittingField)
    (Gal.galActionHom_injective h (h.comp (X ^ 2)).SplittingField) _

/-- Squaring intertwines the two honest actions: `sqRoot (σ x) = σ · (sqRoot x)`. -/
theorem sqRoot_fRoot (σ : (h.comp (X ^ 2)).Gal)
    (x : (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField) :
    sqRoot h (fRoot h σ x) = hRoot h σ (sqRoot h x) :=
  Subtype.ext (by simp)

open scoped Classical in
/-- **Block-constancy.** The block-sign at block `sqRoot x` (computed via the canonical section)
equals the flip-sign of `κ` at the specific root `x` — since the two roots share a block (`= ±`),
`κ` treats them the same. Holds for any `κ`. -/
theorem blockSign_eq_of_mem_block (hmon : h.Monic) (κ : (h.comp (X ^ 2)).Gal)
    (x : (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField) :
    blockSign h hmon κ (sqRoot h x)
      = if κ (x : (h.comp (X ^ 2)).SplittingField) = (x : (h.comp (X ^ 2)).SplittingField)
        then 0 else 1 := by
  simp only [blockSign]
  have hsq : ((sqSection h hmon (sqRoot h x) : (h.comp (X ^ 2)).SplittingField)) ^ 2
      = (x : (h.comp (X ^ 2)).SplittingField) ^ 2 := by
    simpa only [sqRoot_val] using congrArg Subtype.val (sqRoot_sqSection h hmon (sqRoot h x))
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with hx | hx
  · rw [hx]
  · rw [hx, map_neg, neg_inj]

/-- **(L4.6) Conjugation permutes the sign coordinates.** For any `c`, conjugating by `c` translates
the block-sign of `κ` by the block-permutation `hRoot c⁻¹`: `blockSign (cκc⁻¹) θ = blockSign κ (c⁻¹·θ)`.
(The block-action of `c` on the roots of `h` is `restrictComp c`; see `T019`/the example.) -/
theorem blockSign_conj (hmon : h.Monic) (c κ : (h.comp (X ^ 2)).Gal)
    (θ : h.rootSet (h.comp (X ^ 2)).SplittingField) :
    blockSign h hmon (c * κ * c⁻¹) θ = blockSign h hmon κ (hRoot h c⁻¹ θ) := by
  classical
  have hci : ∀ y : (h.comp (X ^ 2)).SplittingField, (c⁻¹) (c y) = y := fun y => by
    rw [show (c⁻¹) (c y) = (c⁻¹ * c) y from rfl, inv_mul_cancel]; rfl
  have hic : ∀ y : (h.comp (X ^ 2)).SplittingField, c ((c⁻¹) y) = y := fun y => by
    rw [show c ((c⁻¹) y) = (c * c⁻¹) y from rfl, mul_inv_cancel]; rfl
  have hblock : hRoot h c⁻¹ θ = sqRoot h (fRoot h c⁻¹ (sqSection h hmon θ)) := by
    rw [sqRoot_fRoot, sqRoot_sqSection]
  rw [hblock, blockSign_eq_of_mem_block]
  simp only [blockSign, fRoot_val]
  refine if_congr ?_ rfl rfl
  rw [show (c * κ * c⁻¹) (sqSection h hmon θ : (h.comp (X ^ 2)).SplittingField)
      = c (κ (c⁻¹ (sqSection h hmon θ : (h.comp (X ^ 2)).SplittingField))) from rfl]
  constructor
  · intro hh
    have := congrArg (fun z => (c⁻¹) z) hh
    simpa only [hci] using this
  · intro hh
    rw [hh, hic]

/-- **`hRoot` is the Mathlib Galois action of `restrictComp`.** The honest block-action `hRoot h σ`
on `rootSet h` coincides with `Polynomial.Gal.galActionHom h L (restrictComp h (X²) hq σ)` — since
`restrictComp = restrict` definitionally and `galActionHom_restrict` says the restricted action is
`σ` itself. This transports order/cycle-type facts about the `C₃`-block-permutation (accessible for
the Mathlib `galActionHom`) to `hRoot`, which drives `blockSign_conj`. -/
theorem galActionHom_restrictComp_eq_hRoot (σ : (h.comp (X ^ 2)).Gal)
    (θ : h.rootSet (h.comp (X ^ 2)).SplittingField) :
    haveI : Fact ((h.map (algebraMap F (h.comp (X ^ 2)).SplittingField)).Splits) :=
      ⟨Gal.splits_in_splittingField_of_comp h (X ^ 2) hq⟩
    Gal.galActionHom h (h.comp (X ^ 2)).SplittingField (Gal.restrictComp h (X ^ 2) hq σ) θ
      = hRoot h σ θ := by
  have : Fact ((h.map (algebraMap F (h.comp (X ^ 2)).SplittingField)).Splits) :=
    ⟨Gal.splits_in_splittingField_of_comp h (X ^ 2) hq⟩
  have hrc : Gal.restrictComp h (X ^ 2) hq σ
      = Gal.restrict h ((h.comp (X ^ 2)).SplittingField) σ := rfl
  apply Subtype.ext
  rw [hRoot_val, hrc]
  exact Gal.galActionHom_restrict h (h.comp (X ^ 2)).SplittingField σ θ

/-- The identity has trivial block-sign. -/
@[simp] theorem blockSign_one (hmon : h.Monic) : blockSign h hmon 1 = 0 := by
  funext θ
  exact if_pos rfl

/-! ### The block-sign as a homomorphism, and `|K| = 2^{deg h}` from surjectivity (L4.8) -/

open scoped Classical in
/-- The block-sign packaged as a group homomorphism `K →* Multiplicative (rootSet h L → ZMod 2)`
(signs compose additively). Injective; surjective once the coordinate flips are all realised. -/
noncomputable def blockSignHom (hmon : h.Monic)
    (hnd : ∀ x : (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField,
      (x : (h.comp (X ^ 2)).SplittingField) ≠ -(x : (h.comp (X ^ 2)).SplittingField)) :
    ↥(MonoidHom.ker (Gal.restrictComp h (X ^ 2) hq)) →*
      Multiplicative (h.rootSet (h.comp (X ^ 2)).SplittingField → ZMod 2) where
  toFun σ := Multiplicative.ofAdd (blockSign h hmon (σ : (h.comp (X ^ 2)).Gal))
  map_one' := by simp
  map_mul' σ τ := by
    simp only [Subgroup.coe_mul]
    rw [blockSign_mul h hq hmon hnd σ.2 τ.2, ofAdd_add]

open scoped Classical in
/-- **`blockSignHom` is bijective** (nondegenerate blocks + all coordinate flips realised): injective
by `blockSign_injective`, surjective because the realised flips `Pi.single θ 1` span. -/
theorem blockSignHom_bijective (hmon : h.Monic)
    (hnd : ∀ x : (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField,
      (x : (h.comp (X ^ 2)).SplittingField) ≠ -(x : (h.comp (X ^ 2)).SplittingField))
    (hgen : ∀ θ : h.rootSet (h.comp (X ^ 2)).SplittingField,
      ∃ κ : ↥(MonoidHom.ker (Gal.restrictComp h (X ^ 2) hq)),
        blockSign h hmon (κ : (h.comp (X ^ 2)).Gal) = Pi.single θ 1) :
    Function.Bijective (blockSignHom h hq hmon hnd) := by
  refine ⟨?_, ?_⟩
  · intro σ τ hστ
    apply blockSign_injective h hq hmon
    have := congrArg Multiplicative.toAdd hστ
    simpa only [blockSignHom, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd] using this
  · rw [← MonoidHom.range_eq_top, eq_top_iff]
    intro v _
    choose κ hκ using hgen
    have hmem : ∀ θ, Multiplicative.ofAdd (Pi.single θ (1 : ZMod 2))
        ∈ (blockSignHom h hq hmon hnd).range := fun θ =>
      ⟨κ θ, by simp only [blockSignHom, MonoidHom.coe_mk, OneHom.coe_mk]; rw [hκ θ]⟩
    have hv : v = ∏ θ ∈ Finset.univ.filter (fun θ => Multiplicative.toAdd v θ = 1),
        Multiplicative.ofAdd (Pi.single θ (1 : ZMod 2)) := by
      rw [← ofAdd_sum]
      conv_lhs => rw [← ofAdd_toAdd v]
      congr 1
      funext i
      rw [Finset.sum_apply]
      simp only [Pi.single_apply, Finset.sum_ite_eq, Finset.mem_filter, Finset.mem_univ, true_and]
      generalize Multiplicative.toAdd v i = a
      revert a; decide
    rw [hv]
    exact Subgroup.prod_mem _ (fun θ _ => hmem θ)

open scoped Classical in
/-- **(L4.8) `|K| = 2^{#roots of h}`** — given that every coordinate flip `Pi.single θ 1` is realised
by some kernel element (`hgen`), the block-sign homomorphism is bijective. -/
theorem card_ker_eq (hmon : h.Monic)
    (hnd : ∀ x : (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField,
      (x : (h.comp (X ^ 2)).SplittingField) ≠ -(x : (h.comp (X ^ 2)).SplittingField))
    (hgen : ∀ θ : h.rootSet (h.comp (X ^ 2)).SplittingField,
      ∃ κ : ↥(MonoidHom.ker (Gal.restrictComp h (X ^ 2) hq)),
        blockSign h hmon (κ : (h.comp (X ^ 2)).Gal) = Pi.single θ 1) :
    Nat.card (MonoidHom.ker (Gal.restrictComp h (X ^ 2) hq))
      = 2 ^ Nat.card (h.rootSet (h.comp (X ^ 2)).SplittingField) := by
  rw [Nat.card_congr (Equiv.ofBijective _ (blockSignHom_bijective h hq hmon hnd hgen))]
  show Nat.card (h.rootSet (h.comp (X ^ 2)).SplittingField → ZMod 2)
      = 2 ^ Nat.card (h.rootSet (h.comp (X ^ 2)).SplittingField)
  rw [Nat.card_fun, Nat.card_zmod]

open scoped Classical in
/-- **The block-sign isomorphism** `K ≃* Multiplicative (rootSet h L → ZMod 2)`. Packages
`blockSignHom` (bijective under nondegeneracy + generation) as a `MulEquiv`; the concrete endpoint for
identifying the kernel `K = Gal(L/M)` with `C₂^{#roots of h}`. -/
noncomputable def blockSignEquiv (hmon : h.Monic)
    (hnd : ∀ x : (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField,
      (x : (h.comp (X ^ 2)).SplittingField) ≠ -(x : (h.comp (X ^ 2)).SplittingField))
    (hgen : ∀ θ : h.rootSet (h.comp (X ^ 2)).SplittingField,
      ∃ κ : ↥(MonoidHom.ker (Gal.restrictComp h (X ^ 2) hq)),
        blockSign h hmon (κ : (h.comp (X ^ 2)).Gal) = Pi.single θ 1) :
    ↥(MonoidHom.ker (Gal.restrictComp h (X ^ 2) hq)) ≃*
      Multiplicative (h.rootSet (h.comp (X ^ 2)).SplittingField → ZMod 2) :=
  MulEquiv.ofBijective (blockSignHom h hq hmon hnd) (blockSignHom_bijective h hq hmon hnd hgen)

open scoped Classical in
/-- `blockSignEquiv` applied is the block-sign vector (cheap unfolding avoiding the bijectivity
proof; the direct `rfl` is expensive because of the `SplittingField` instances). -/
@[simp] theorem blockSignEquiv_apply (hmon : h.Monic)
    (hnd : ∀ x : (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField,
      (x : (h.comp (X ^ 2)).SplittingField) ≠ -(x : (h.comp (X ^ 2)).SplittingField))
    (hgen : ∀ θ : h.rootSet (h.comp (X ^ 2)).SplittingField,
      ∃ κ : ↥(MonoidHom.ker (Gal.restrictComp h (X ^ 2) hq)),
        blockSign h hmon (κ : (h.comp (X ^ 2)).Gal) = Pi.single θ 1)
    (κ : ↥(MonoidHom.ker (Gal.restrictComp h (X ^ 2) hq))) :
    blockSignEquiv h hq hmon hnd hgen κ
      = Multiplicative.ofAdd (blockSign h hmon (κ : (h.comp (X ^ 2)).Gal)) := by
  rw [blockSignEquiv, MulEquiv.ofBijective_apply]; rfl

/-! ### Weight-from-cycle-type (L4.5): a `{2,1⁴}` kernel involution flips exactly one block

The `p = 13` Frobenius certificate delivers a `σ₀` whose *twisted* `galActionHom` permutation of the
roots has partition `{2,1,1,1,1}`. `galActionHom` is conjugate (via the `rootsEquivRootsAux` twist) to the
**honest** action `fRootEquiv σ` (`x ↦ σ x`), so both have the same partition. On the honest side the
block combinatorics are transparent: `σ₀ ∈ K` flips whole `±`-pairs, so a single transposition means a
single flipped block, i.e. `blockSign σ₀` is a standard basis vector. -/

/-- The honest action of `σ` on the roots of `h(X²)`, packaged as a permutation (inverse is the action
of `σ⁻¹`). -/
noncomputable def fRootEquiv (σ : (h.comp (X ^ 2)).Gal) :
    Equiv.Perm ((h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField) where
  toFun := fRoot h σ
  invFun := fRoot h σ⁻¹
  left_inv x := by
    apply Subtype.ext
    simp only [fRoot_val]
    rw [show (σ⁻¹) (σ (x : (h.comp (X ^ 2)).SplittingField))
        = (σ⁻¹ * σ) (x : (h.comp (X ^ 2)).SplittingField) from rfl, inv_mul_cancel]; rfl
  right_inv x := by
    apply Subtype.ext
    simp only [fRoot_val]
    rw [show σ ((σ⁻¹) (x : (h.comp (X ^ 2)).SplittingField))
        = (σ * σ⁻¹) (x : (h.comp (X ^ 2)).SplittingField) from rfl, mul_inv_cancel]; rfl

@[simp] theorem fRootEquiv_apply (σ : (h.comp (X ^ 2)).Gal)
    (x : (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField) :
    fRootEquiv h σ x = fRoot h σ x := rfl

/-- **The twist, dissolved.** `galActionHom σ` (twisted by the `rootsEquivRootsAux` lift `Splitting↪E`)
equals the honest `fRootEquiv σ` conjugated by `rootsEquivRootsAux` — the same `smul_def` cancellation used
for Dedekind's theorem (`exists_reduction_rootSet_equiv_permCongr`). No `galActionHom_val`/`L = id`
lemma is needed (both are unprovable). -/
theorem galActionHom_eq_permCongr_fRootEquiv (σ : (h.comp (X ^ 2)).Gal) :
    Gal.galActionHom (h.comp (X ^ 2)) (h.comp (X ^ 2)).SplittingField σ
      = (Gal.rootsEquivRootsAux (h.comp (X ^ 2)) (h.comp (X ^ 2)).SplittingField).permCongr
          (fRootEquiv h σ) := by
  ext r
  rw [Equiv.permCongr_apply,
    show Gal.galActionHom (h.comp (X ^ 2)) (h.comp (X ^ 2)).SplittingField σ r
        = Gal.rootsEquivRootsAux (h.comp (X ^ 2)) (h.comp (X ^ 2)).SplittingField
            (fRootEquiv h σ
              ((Gal.rootsEquivRootsAux (h.comp (X ^ 2)) (h.comp (X ^ 2)).SplittingField).symm r))
      from rfl]

open scoped Classical in
/-- Conjugate permutations have the same partition: the certificate's `galActionHom σ` cycle structure
transfers to the honest `fRootEquiv σ`. -/
theorem galActionHom_partition_parts_eq (σ : (h.comp (X ^ 2)).Gal) :
    (Gal.galActionHom (h.comp (X ^ 2)) (h.comp (X ^ 2)).SplittingField σ).partition.parts
      = (fRootEquiv h σ).partition.parts := by
  rw [galActionHom_eq_permCongr_fRootEquiv, partition_parts_permCongr]

/-- `orderOf σ` equals the order of the honest root permutation `fRootEquiv σ`: they are conjugate
(via `rootsEquivRootsAux`, `galActionHom_eq_permCongr_fRootEquiv`) and `galActionHom` is injective. This
lets a caller read `orderOf σ` off the concrete cycle structure of `fRootEquiv σ` — never touching the
twisted `galActionHom` in downstream (instance-diamond-prone) contexts. -/
theorem orderOf_eq_orderOf_fRootEquiv (σ : (h.comp (X ^ 2)).Gal) :
    orderOf σ = orderOf (fRootEquiv h σ) := by
  rw [← orderOf_injective (Gal.galActionHom (h.comp (X ^ 2)) (h.comp (X ^ 2)).SplittingField)
      (Gal.galActionHom_injective _ _) σ, galActionHom_eq_permCongr_fRootEquiv]
  exact orderOf_injective
    (Gal.rootsEquivRootsAux (h.comp (X ^ 2)) (h.comp (X ^ 2)).SplittingField).permCongrHom.toMonoidHom
    (Gal.rootsEquivRootsAux (h.comp (X ^ 2)) (h.comp (X ^ 2)).SplittingField).permCongrHom.injective _

open scoped Classical in
/-- Membership in the support of the honest permutation is "`σ` moves the root". -/
theorem mem_support_fRootEquiv {σ : (h.comp (X ^ 2)).Gal}
    {x : (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField} :
    x ∈ (fRootEquiv h σ).support
      ↔ σ (x : (h.comp (X ^ 2)).SplittingField) ≠ (x : (h.comp (X ^ 2)).SplittingField) := by
  rw [Equiv.Perm.mem_support, ne_eq, ne_eq, not_iff_not, Subtype.ext_iff, fRootEquiv_apply, fRoot_val]

/-- Squaring identifies a root with its negative: they lie in the same block. -/
theorem sqRoot_negRoot (x : (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField) :
    sqRoot h (negRoot h x) = sqRoot h x :=
  Subtype.ext (by simp)

open scoped Classical in
/-- **Support of a size-`2` root permutation is a single `±`-pair.** When no root equals its negative
(`hnd`), the support of `fRootEquiv σ` is closed under the fixed-point-free involution `negRoot`; if it
has exactly `2` elements it is therefore `{x₀, -x₀}` for some `x₀` in it. -/
private theorem exists_support_eq_negRoot_pair_of_card_two (σ : (h.comp (X ^ 2)).Gal)
    (hnd : ∀ x : (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField,
      (x : (h.comp (X ^ 2)).SplittingField) ≠ -(x : (h.comp (X ^ 2)).SplittingField))
    (hsupp : (fRootEquiv h σ).support.card = 2) :
    ∃ x₀, x₀ ∈ (fRootEquiv h σ).support ∧
      (fRootEquiv h σ).support = {x₀, negRoot h x₀} := by
  obtain ⟨x₀, hx₀⟩ : (fRootEquiv h σ).support.Nonempty := by
    rw [← Finset.card_pos, hsupp]; norm_num
  refine ⟨x₀, hx₀, ?_⟩
  have hx₀' : σ (x₀ : (h.comp (X ^ 2)).SplittingField) ≠ (x₀ : (h.comp (X ^ 2)).SplittingField) :=
    (mem_support_fRootEquiv h).mp hx₀
  have hneg_mem : negRoot h x₀ ∈ (fRootEquiv h σ).support := by
    rw [mem_support_fRootEquiv, negRoot_val, map_neg]
    intro hc; exact hx₀' (neg_injective hc)
  have hne : x₀ ≠ negRoot h x₀ := fun hc =>
    hnd x₀ (by rw [← negRoot_val h x₀]; exact congrArg Subtype.val hc)
  have hsub : ({x₀, negRoot h x₀} : Finset _) ⊆ (fRootEquiv h σ).support :=
    Finset.insert_subset_iff.mpr ⟨hx₀, Finset.singleton_subset_iff.mpr hneg_mem⟩
  have hcard2 : ({x₀, negRoot h x₀} : Finset _).card = 2 := Finset.card_pair hne
  exact (Finset.eq_of_subset_of_card_le hsub (le_of_eq (hsupp.trans hcard2.symm))).symm

open scoped Classical in
/-- **`σ` fixes the section point of every non-flipped block.** If the support of `fRootEquiv σ` is the
single `±`-pair `{x₀, -x₀}`, then for any block `θ` other than `sqRoot x₀` the chosen square root
`sqSection θ` is fixed by `σ`: moving it would place it in the support, yet its square is `θ ≠ sqRoot x₀`
(and `sqRoot (-x₀) = sqRoot x₀`), a contradiction. -/
private theorem apply_sqSection_eq_of_ne_sqRoot (hmon : h.Monic) (σ : (h.comp (X ^ 2)).Gal)
    {x₀ : (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField}
    (hsupp_eq : (fRootEquiv h σ).support = {x₀, negRoot h x₀})
    {θ : h.rootSet (h.comp (X ^ 2)).SplittingField} (hθ : θ ≠ sqRoot h x₀) :
    σ (sqSection h hmon θ : (h.comp (X ^ 2)).SplittingField)
      = (sqSection h hmon θ : (h.comp (X ^ 2)).SplittingField) := by
  by_contra hcc
  have hmemx1 : sqSection h hmon θ ∈ (fRootEquiv h σ).support :=
    (mem_support_fRootEquiv h).mpr hcc
  rw [hsupp_eq, Finset.mem_insert, Finset.mem_singleton] at hmemx1
  have hsq : sqRoot h (sqSection h hmon θ) = θ := sqRoot_sqSection h hmon θ
  rcases hmemx1 with h' | h'
  · rw [h'] at hsq; exact hθ hsq.symm
  · rw [h', sqRoot_negRoot] at hsq; exact hθ hsq.symm

open scoped Classical in
/-- **(L4.5) Weight-one from a single transposition.** If the honest permutation of `σ` has support of
size exactly `2` (a single transposition of a `±`-pair), then `blockSign σ` is a standard basis vector
`Pi.single θ₀ 1`: exactly one block is flipped. (No kernel hypothesis: pure block combinatorics — the
support is closed under the fixed-point-free involution `negRoot`, so being size `2` it is a single
`±`-pair `{x₀, -x₀}`, both squaring to the one flipped block `θ₀`.) -/
theorem blockSign_eq_single_of_support_card_two (hmon : h.Monic)
    (hnd : ∀ x : (h.comp (X ^ 2)).rootSet (h.comp (X ^ 2)).SplittingField,
      (x : (h.comp (X ^ 2)).SplittingField) ≠ -(x : (h.comp (X ^ 2)).SplittingField))
    (σ : (h.comp (X ^ 2)).Gal) (hsupp : (fRootEquiv h σ).support.card = 2) :
    ∃ θ₀, blockSign h hmon σ = Pi.single θ₀ 1 := by
  obtain ⟨x₀, hx₀, hsupp_eq⟩ := exists_support_eq_negRoot_pair_of_card_two h σ hnd hsupp
  refine ⟨sqRoot h x₀, ?_⟩
  funext θ
  by_cases hθ : θ = sqRoot h x₀
  · subst hθ
    rw [Pi.single_eq_same, blockSign_eq_of_mem_block, if_neg ((mem_support_fRootEquiv h).mp hx₀)]
  · rw [Pi.single_eq_of_ne hθ, blockSign,
      if_pos (apply_sqSection_eq_of_ne_sqRoot h hmon σ hsupp_eq hθ)]

/-! ### Conjugation covers all blocks (L4.6): the C₃ symmetry generates the full sign group

A single weight-one kernel element `σ₀` (`blockSign σ₀ = e_{θ₀}`) generates *every* basis vector by
conjugation: the block-action is transitive (the resolvent `h` is irreducible, so its roots are Galois
conjugate), so for each block `θ` some `c` maps `θ₀ ↦ θ`, and `blockSign_conj` turns `c σ₀ c⁻¹` into
`e_θ`. This is the `hgen` hypothesis of `card_ker_eq`. -/

/-- `hRoot c⁻¹` undoes `hRoot c`. -/
theorem hRoot_leftInv (c : (h.comp (X ^ 2)).Gal)
    (x : h.rootSet (h.comp (X ^ 2)).SplittingField) : hRoot h c⁻¹ (hRoot h c x) = x := by
  apply Subtype.ext
  rw [hRoot_val, hRoot_val,
    show c⁻¹ (c (x : (h.comp (X ^ 2)).SplittingField)) = (c⁻¹ * c) (x : _) from rfl,
    inv_mul_cancel]; rfl

/-- `hRoot c` undoes `hRoot c⁻¹`. -/
theorem hRoot_rightInv (c : (h.comp (X ^ 2)).Gal)
    (x : h.rootSet (h.comp (X ^ 2)).SplittingField) : hRoot h c (hRoot h c⁻¹ x) = x := by
  apply Subtype.ext
  rw [hRoot_val, hRoot_val,
    show c (c⁻¹ (x : (h.comp (X ^ 2)).SplittingField)) = (c * c⁻¹) (x : _) from rfl,
    mul_inv_cancel]; rfl

/-- **Transitivity of the block-action.** For irreducible `h`, any two roots (blocks) are Galois
conjugate: the normal extension `SplittingField` acts transitively on the roots of the irreducible
`h`. Hence some `c` carries `θ₀` to `θ`. -/
theorem hRoot_transitive (hmon : h.Monic) (hirr : Irreducible h)
    (θ₀ θ : h.rootSet (h.comp (X ^ 2)).SplittingField) :
    ∃ c : (h.comp (X ^ 2)).Gal, hRoot h c θ₀ = θ := by
  have hmp : ∀ y : h.rootSet (h.comp (X ^ 2)).SplittingField,
      minpoly F (y : (h.comp (X ^ 2)).SplittingField) = h :=
    fun y => (minpoly.eq_of_irreducible_of_monic hirr (mem_rootSet.mp y.2).2 hmon).symm
  have : Normal F (h.comp (X ^ 2)).SplittingField := SplittingField.instNormal _
  obtain ⟨c, hc⟩ := (Normal.minpoly_eq_iff_mem_orbit (h.comp (X ^ 2)).SplittingField).mp
    ((hmp θ).trans (hmp θ₀).symm)
  exact ⟨c, Subtype.ext ((hRoot_val h c θ₀).trans hc)⟩

open scoped Classical in
/-- **(L4.6) One weight-one element generates all coordinate flips.** Given a kernel element `σ₀` with
`blockSign σ₀ = Pi.single θ₀ 1` and irreducible `h`, every `Pi.single θ 1` is realised by a kernel
element (a conjugate `c σ₀ c⁻¹`). This is exactly the `hgen` input to `card_ker_eq`, giving `|K| =
2^{#blocks}`. -/
theorem blockSign_generates (hmon : h.Monic) (hirr : Irreducible h)
    {σ₀ : (h.comp (X ^ 2)).Gal}
    (hσ₀ : σ₀ ∈ MonoidHom.ker (Gal.restrictComp h (X ^ 2) hq))
    {θ₀ : h.rootSet (h.comp (X ^ 2)).SplittingField}
    (h0 : blockSign h hmon σ₀ = Pi.single θ₀ 1)
    (θ : h.rootSet (h.comp (X ^ 2)).SplittingField) :
    ∃ κ : ↥(MonoidHom.ker (Gal.restrictComp h (X ^ 2) hq)),
      blockSign h hmon (κ : (h.comp (X ^ 2)).Gal) = Pi.single θ 1 := by
  obtain ⟨c, hc⟩ := hRoot_transitive h hmon hirr θ₀ θ
  have hmem : c * σ₀ * c⁻¹ ∈ MonoidHom.ker (Gal.restrictComp h (X ^ 2) hq) := by
    rw [MonoidHom.mem_ker] at hσ₀ ⊢
    rw [map_mul, map_mul, map_inv, hσ₀, mul_one, mul_inv_cancel]
  refine ⟨⟨c * σ₀ * c⁻¹, hmem⟩, ?_⟩
  funext θ'
  rw [show ((⟨c * σ₀ * c⁻¹, hmem⟩ : ↥(MonoidHom.ker (Gal.restrictComp h (X ^ 2) hq))) :
      (h.comp (X ^ 2)).Gal) = c * σ₀ * c⁻¹ from rfl, blockSign_conj, h0,
    Pi.single_apply, Pi.single_apply]
  refine if_congr ?_ rfl rfl
  constructor
  · intro hh
    have := congrArg (hRoot h c) hh
    rwa [hRoot_rightInv, hc] at this
  · intro hh; subst hh; rw [← hc, hRoot_leftInv]

end EvenPoly

end IdealArithmetic.Galois.EvenSextic
