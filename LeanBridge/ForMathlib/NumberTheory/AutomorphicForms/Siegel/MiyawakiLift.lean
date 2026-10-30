import TauCeti.NumberTheory.ModularForms.Newforms.Satake

/-!
# The Euler factors of Miyawaki lifts

A Miyawaki lift (LMFDB `mf.siegel.lift.miyawaki`) is a lift from elliptic modular forms to Siegel
modular forms of degree `3` on `Sp(6, ℤ)`, described through the Euler factors of the lift. For a
normalised Hecke eigenform `f ∈ S_k(SL(2, ℤ))` and a prime `p`, the elliptic Euler factor is
`Q_p(f, X) = 1 - a_p(f) X + p^{k-1} X² = (1 - γ₊X)(1 - γ₋X)`, the standard elliptic Euler factor
is `Q_p^st(f, X) = (1 - X)(1 - (γ₊/γ₋)X)(1 - (γ₋/γ₊)X)`, and for a second eigenform
`g ∈ S_ℓ(SL(2, ℤ))` with `Q_p(g, X) = (1 - δ₊X)(1 - δ₋X)` the Rankin–Selberg Euler factor is
`Q_p(f ⊗ g, X) = ∏ (1 - γ_± δ_± X)`. The knowl expresses the last two through `a_p(f)` and
`a_p(g)`; these formulas are proved here.

The Ikeda–Miyawaki lift, or Miyawaki lift of type I (LMFDB `mf.siegel.lift.miyawaki1`), of
eigenforms `f ∈ S_{2ℓ-4}(SL(2, ℤ))` and `g ∈ S_ℓ(SL(2, ℤ))`, `ℓ` even, is a Siegel eigenform
`F ∈ S_ℓ(Sp(6, ℤ))` with standard Euler factors `Q_p(f, p^{2-ℓ}X) Q_p(f, p^{3-ℓ}X) Q_p^st(g, X)`
and spinor Euler factors `Q_p(g, p^{ℓ-2}X) Q_p(g, p^{ℓ-3}X) Q_p(f ⊗ g, X)` when it is nonzero (the
knowl calls the weight of `g` and `F` `k`). These products are defined here, and they are proved
to have the shape of the standard and spinor Euler factors of a Siegel eigenform of degree `3` and
weight `ℓ`: `(1 - X) ∏_{i=1}^3 (1 - α_i X)(1 - α_i⁻¹ X)`, and `∏_{i=1}^4 (1 - β_i X)(1 - β_i' X)`
with `β_i β_i' = p^{3ℓ-6}`, for nonzero `α_i` and `β_i` given explicitly by the Satake parameters
of `f` and `g`, taken in either order.

The normalised eigenforms of level `1` are Tau Ceti's newforms `HeckeRing.GL2.Newform 1 k`, and
`γ_±` are their Satake parameters `HeckeRing.GL2.Newform.satakeParameters`. The lifts themselves are
not formalised: Ikeda constructs the type I lift from the Duke–Imamoglu–Ikeda lift (LMFDB
`mf.siegel.lift.ikeda`), the type II lift is conjectural, and the standard and spinor Euler factors
of Siegel eigenforms of degree `3` need the Satake isomorphism for the Hecke rings of `Sp(6, ℤ)`,
which is not available. So only the Euler factors that the lifts are asserted to have are defined.

## Main definitions

* `HeckeRing.GL2.Newform.ellipticEulerFactor` (LMFDB `mf.siegel.lift.miyawaki`): `Q_p(f, X)`.
* `HeckeRing.GL2.Newform.satakeRatios`: the ratios `γ₊/γ₋`, `γ₋/γ₊` of the Satake parameters.
* `HeckeRing.GL2.Newform.standardEulerFactor` (LMFDB `mf.siegel.lift.miyawaki`): `Q_p^st(f, X)`.
* `HeckeRing.GL2.Newform.rankinSelbergEulerFactor` (LMFDB `mf.siegel.lift.miyawaki`):
  `Q_p(f ⊗ g, X)`.
* `HeckeRing.GL2.Newform.miyawakiStandardEulerFactor` (LMFDB `mf.siegel.lift.miyawaki1`): the
  standard Euler factor of the Ikeda–Miyawaki lift.
* `HeckeRing.GL2.Newform.miyawakiSpinorEulerFactor` (LMFDB `mf.siegel.lift.miyawaki1`): the spinor
  Euler factor of the Ikeda–Miyawaki lift.

## Main results

* `HeckeRing.GL2.Newform.ellipticEulerFactor_eq_prod`: `Q_p(f, X) = (1 - γ₊X)(1 - γ₋X)`.
* `HeckeRing.GL2.Newform.standardEulerFactor_eq`:
  `Q_p^st(f, X) = (1 - X)(1 - (a_p(f)²/p^{k-1} - 2)X + X²)`.
* `HeckeRing.GL2.Newform.rankinSelbergEulerFactor_eq`: the knowl's formula for `Q_p(f ⊗ g, X)`.
* `HeckeRing.GL2.Newform.miyawakiStandardEulerFactor_eq`: the standard Euler factor of the
  Ikeda–Miyawaki lift is `(1 - X) ∏_{i=1}^3 (1 - α_i X)(1 - α_i⁻¹ X)` with `α_1, α_2 = γ_± p^{2-ℓ}`
  and `α_3 = δ₊/δ₋`.
* `HeckeRing.GL2.Newform.miyawakiSpinorEulerFactor_eq`: the spinor Euler factor of the
  Ikeda–Miyawaki lift is `∏_{i=1}^4 (1 - β_i X)(1 - p^{3ℓ-6} β_i⁻¹ X)` with `β_1, β_2 = δ_± p^{ℓ-2}`
  and `β_3, β_4 = γ₊δ_±`.
-/

open Polynomial UpperHalfPlane

namespace HeckeRing.GL2.Newform

section

variable {k ℓ : ℤ} (f : Newform 1 k) (g : Newform 1 ℓ) (p : ℕ)

lemma dirichletLift_natCast_eq_one (n : ℕ) : f.dirichletLift n = 1 := by
  rw [Subsingleton.elim (n : ZMod 1) 1, map_one]

lemma ne_zero_of_mem_satakeParameters (hp : p ≠ 0) {γ : ℂ} (hγ : γ ∈ f.satakeParameters p) :
    γ ≠ 0 :=
  fun h ↦ f.zero_notMem_satakeParameters hp (Nat.coprime_one_right p) (h ▸ hγ)

/-- The **elliptic Euler factor** `Q_p(f, X) = 1 - a_p(f) X + p^{k-1} X²` (LMFDB
`mf.siegel.lift.miyawaki`) of a normalised Hecke eigenform `f ∈ S_k(SL(2, ℤ))` at `p`, where
`a_p(f)` is the `p`-th Fourier coefficient of `f`. It is `(1 - γ₊X)(1 - γ₋X)` for the Satake
parameters `γ_±` of `f` at `p` (`ellipticEulerFactor_eq_prod`), and `Q_p(f, p^{-s})⁻¹` is the Euler
factor of `L(s, f)`. As for Tau Ceti's Satake parameters, this and the following Euler factors are
defined for every natural number `p`, and are meaningful for primes `p`. -/
noncomputable def ellipticEulerFactor : ℂ[X] :=
  1 - C ((qExpansion 1 f.toCuspForm).coeff p) * X + C ((p : ℂ) ^ (k - 1)) * X ^ 2

/-- The multiset `{γ₊/γ₋, γ₋/γ₊}` of the **ratios of the Satake parameters** `γ_±` of a normalised
Hecke eigenform `f` of level `1` at `p` (`satakeRatios_eq`): each Satake parameter divided by the
other one. -/
noncomputable def satakeRatios : Multiset ℂ :=
  (f.satakeParameters p).bind fun γ ↦ ((f.satakeParameters p).erase γ).map (γ / ·)

/-- The **standard elliptic Euler factor** `Q_p^st(f, X) = (1 - X)(1 - (γ₊/γ₋)X)(1 - (γ₋/γ₊)X)`
(LMFDB `mf.siegel.lift.miyawaki`) of a normalised Hecke eigenform `f ∈ S_k(SL(2, ℤ))` at `p`, for
the Satake parameters `γ_±` of `f` at `p`; it is `(1 - X)(1 - (a_p(f)²/p^{k-1} - 2)X + X²)`
(`standardEulerFactor_eq`). -/
noncomputable def standardEulerFactor : ℂ[X] :=
  (1 - X) * ((f.satakeRatios p).map fun x ↦ 1 - C x * X).prod

/-- The **Rankin–Selberg Euler factor**
`Q_p(f ⊗ g, X) = (1 - γ₊δ₊X)(1 - γ₊δ₋X)(1 - γ₋δ₊X)(1 - γ₋δ₋X)` (LMFDB `mf.siegel.lift.miyawaki`)
of normalised Hecke eigenforms `f ∈ S_k(SL(2, ℤ))` and `g ∈ S_ℓ(SL(2, ℤ))` at `p`, for the Satake
parameters `γ_±` of `f` and `δ_±` of `g` at `p` (`rankinSelbergEulerFactor_eq`). -/
noncomputable def rankinSelbergEulerFactor : ℂ[X] :=
  ((f.satakeParameters p ×ˢ g.satakeParameters p).map fun x ↦ 1 - C (x.1 * x.2) * X).prod

/-- **The elliptic Euler factor is `(1 - γ₊X)(1 - γ₋X)`** for the Satake parameters `γ_±`. -/
lemma ellipticEulerFactor_eq_prod :
    f.ellipticEulerFactor p = ((f.satakeParameters p).map fun γ ↦ 1 - C γ * X).prod := by
  rcases f.exists_satakeParameters_eq_pair p with ⟨α, β, h⟩
  rcases (f.satakeParameters_eq_pair_iff p).mp h with ⟨hs, hpr⟩
  rw [f.dirichletLift_natCast_eq_one, one_mul] at hpr
  rw [h, ellipticEulerFactor, ← hs, ← hpr]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, map_add, map_mul]
  ring1

lemma satakeRatios_eq {α β : ℂ} (h : f.satakeParameters p = {α, β}) :
    f.satakeRatios p = {α / β, β / α} := by
  have h' : f.satakeParameters p = {β, α} :=
    h.trans (Multiset.pair_comm α β)
  rw [satakeRatios]
  nth_rw 1 [h]
  rw [Multiset.insert_eq_cons, Multiset.cons_bind, Multiset.singleton_bind, h,
    Multiset.insert_eq_cons, Multiset.erase_cons_head, ← Multiset.insert_eq_cons, ← h, h',
    Multiset.insert_eq_cons, Multiset.erase_cons_head]
  simp

/-- **The standard elliptic Euler factor of the knowl**:
`Q_p^st(f, X) = (1 - X)(1 - (a_p(f)²/p^{k-1} - 2)X + X²)` for `p ≠ 0`. -/
lemma standardEulerFactor_eq (hp : p ≠ 0) : f.standardEulerFactor p = (1 - X) *
    (1 - C ((qExpansion 1 f.toCuspForm).coeff p ^ 2 / (p : ℂ) ^ (k - 1) - 2) * X + X ^ 2) := by
  rcases f.exists_satakeParameters_eq_pair p with ⟨α, β, h⟩
  rcases (f.satakeParameters_eq_pair_iff p).mp h with ⟨hs, hpr⟩
  rw [f.dirichletLift_natCast_eq_one, one_mul] at hpr
  have hα : α ≠ 0 := f.ne_zero_of_mem_satakeParameters p hp (h ▸ Multiset.mem_cons_self α _)
  have hβ : β ≠ 0 := f.ne_zero_of_mem_satakeParameters p hp
    (h ▸ Multiset.mem_cons_of_mem (Multiset.mem_singleton_self β))
  have hc : (qExpansion 1 f.toCuspForm).coeff p ^ 2 / (p : ℂ) ^ (k - 1) - 2 = α / β + β / α := by
    rw [← hs, ← hpr]
    field_simp
    ring1
  have hC : C (α / β) * C (β / α) = 1 := by
    rw [← C_mul, div_mul_div_comm, mul_comm β α, div_self (mul_ne_zero hα hβ), C_1]
  rw [standardEulerFactor, f.satakeRatios_eq p h, hc, C_add]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton]
  linear_combination (1 - X) * X ^ 2 * hC

/-- **The Rankin–Selberg Euler factor of the knowl**: for `p ≠ 0`,
`Q_p(f ⊗ g, X) = 1 - a_p(f) a_p(g) X + (a_p(f)² p^{ℓ-1} + a_p(g)² p^{k-1} - 2 p^{k+ℓ-2}) X²
- a_p(f) a_p(g) p^{k+ℓ-2} X³ + p^{2k+2ℓ-4} X⁴`. -/
lemma rankinSelbergEulerFactor_eq (hp : p ≠ 0) :
    letI a : ℂ := (qExpansion 1 f.toCuspForm).coeff p
    letI b : ℂ := (qExpansion 1 g.toCuspForm).coeff p
    f.rankinSelbergEulerFactor g p = 1 - C (a * b) * X +
      C (a ^ 2 * (p : ℂ) ^ (ℓ - 1) + b ^ 2 * (p : ℂ) ^ (k - 1) - 2 * (p : ℂ) ^ (k + ℓ - 2)) *
          X ^ 2 -
      C (a * b * (p : ℂ) ^ (k + ℓ - 2)) * X ^ 3 + C ((p : ℂ) ^ (2 * k + 2 * ℓ - 4)) * X ^ 4 := by
  rcases f.exists_satakeParameters_eq_pair p with ⟨α, β, hf⟩
  rcases (f.satakeParameters_eq_pair_iff p).mp hf with ⟨hfs, hfp⟩
  rcases g.exists_satakeParameters_eq_pair p with ⟨γ, δ, hg⟩
  rcases (g.satakeParameters_eq_pair_iff p).mp hg with ⟨hgs, hgp⟩
  rw [f.dirichletLift_natCast_eq_one, one_mul] at hfp
  rw [g.dirichletLift_natCast_eq_one, one_mul] at hgp
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have e₁ : (p : ℂ) ^ (k + ℓ - 2) = α * β * (γ * δ) := by
    rw [hfp, hgp, ← zpow_add₀ hp']
    exact congrArg _ (by ring1)
  have e₂ : (p : ℂ) ^ (2 * k + 2 * ℓ - 4) = (α * β * (γ * δ)) ^ 2 := by
    rw [sq, ← e₁, ← zpow_add₀ hp']
    exact congrArg _ (by ring1)
  rw [rankinSelbergEulerFactor, hf, hg, e₁, e₂, ← hfs, ← hgs, ← hfp, ← hgp]
  simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero, Multiset.cons_product,
    Multiset.zero_product, Multiset.map_cons, Multiset.map_zero, Multiset.map_add,
    Multiset.prod_add, Multiset.prod_cons, Multiset.prod_zero, map_add, map_sub, map_mul, map_pow,
    map_ofNat]
  ring1

end

variable {ℓ : ℤ} (f : Newform 1 (2 * ℓ - 4)) (g : Newform 1 ℓ) (p : ℕ) {a b c d : ℂ}

/-- The **standard Euler factor of the Ikeda–Miyawaki lift** (LMFDB `mf.siegel.lift.miyawaki1`)
of normalised Hecke eigenforms `f ∈ S_{2ℓ-4}(SL(2, ℤ))` and `g ∈ S_ℓ(SL(2, ℤ))` at `p`:
`Q_p(f, p^{2-ℓ}X) Q_p(f, p^{3-ℓ}X) Q_p^st(g, X)`, the standard Euler factor `Q_p^st(F, X)` of the
lift `F ∈ S_ℓ(Sp(6, ℤ))` of `(f, g)` when `F` is nonzero, by Ikeda's theorem (not proved here, nor
are the lift and its Euler factors defined). It has the shape of a standard Euler factor of degree
`3` (`miyawakiStandardEulerFactor_eq`). -/
noncomputable def miyawakiStandardEulerFactor : ℂ[X] :=
  (f.ellipticEulerFactor p).comp (C ((p : ℂ) ^ (2 - ℓ)) * X) *
    (f.ellipticEulerFactor p).comp (C ((p : ℂ) ^ (3 - ℓ)) * X) * g.standardEulerFactor p

/-- The **spinor Euler factor of the Ikeda–Miyawaki lift** (LMFDB `mf.siegel.lift.miyawaki1`) of
normalised Hecke eigenforms `f ∈ S_{2ℓ-4}(SL(2, ℤ))` and `g ∈ S_ℓ(SL(2, ℤ))` at `p`:
`Q_p(g, p^{ℓ-2}X) Q_p(g, p^{ℓ-3}X) Q_p(f ⊗ g, X)`, the spinor Euler factor `Q_p^spin(F, X)` of the
lift `F ∈ S_ℓ(Sp(6, ℤ))` of `(f, g)` when `F` is nonzero, by Ikeda's theorem (not proved here, nor
are the lift and its Euler factors defined). It has the shape of a spinor Euler factor of degree
`3` and weight `ℓ` (`miyawakiSpinorEulerFactor_eq`). -/
noncomputable def miyawakiSpinorEulerFactor : ℂ[X] :=
  (g.ellipticEulerFactor p).comp (C ((p : ℂ) ^ (ℓ - 2)) * X) *
    (g.ellipticEulerFactor p).comp (C ((p : ℂ) ^ (ℓ - 3)) * X) * f.rankinSelbergEulerFactor g p

/-- **The standard Euler factor of the Ikeda–Miyawaki lift has the shape of a standard Euler
factor of degree `3`**: for `p ≠ 0` and Satake parameters `{a, b}` of `f` and `{c, d}` of `g` at
`p`, taken in either order, it is `(1 - X) ∏_{i=1}^3 (1 - α_i X)(1 - α_i⁻¹ X)` with
`α_1 = a p^{2-ℓ}`, `α_2 = b p^{2-ℓ}` and `α_3 = c/d`, which are nonzero
(`HeckeRing.GL2.Newform.zero_notMem_satakeParameters`); the inverses `α_1⁻¹ = b p^{3-ℓ}` and
`α_2⁻¹ = a p^{3-ℓ}` are the inverse roots of `Q_p(f, p^{3-ℓ}X)`. -/
lemma miyawakiStandardEulerFactor_eq (hp : p ≠ 0) (hf : f.satakeParameters p = {a, b})
    (hg : g.satakeParameters p = {c, d}) :
    letI α₁ : ℂ := a * (p : ℂ) ^ (2 - ℓ)
    letI α₂ : ℂ := b * (p : ℂ) ^ (2 - ℓ)
    letI α₃ : ℂ := c / d
    f.miyawakiStandardEulerFactor g p = (1 - X) * ((1 - C α₁ * X) * (1 - C α₁⁻¹ * X)) *
        ((1 - C α₂ * X) * (1 - C α₂⁻¹ * X)) * ((1 - C α₃ * X) * (1 - C α₃⁻¹ * X)) := by
  rcases (f.satakeParameters_eq_pair_iff p).mp hf with ⟨-, hab⟩
  rw [f.dirichletLift_natCast_eq_one, one_mul] at hab
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have e : (p : ℂ) ^ (2 * ℓ - 4 - 1) * ((p : ℂ) ^ (2 - ℓ) * (p : ℂ) ^ (3 - ℓ)) = 1 := by
    rw [← zpow_add₀ hp', ← zpow_add₀ hp', ← zpow_zero (p : ℂ)]
    exact congrArg _ (by ring1)
  have h (x y : ℂ) (hxy : x * y = (p : ℂ) ^ (2 * ℓ - 4 - 1)) :
      (x * (p : ℂ) ^ (2 - ℓ))⁻¹ = y * (p : ℂ) ^ (3 - ℓ) :=
    inv_eq_of_mul_eq_one_right <| by
      linear_combination ((p : ℂ) ^ (2 - ℓ) * (p : ℂ) ^ (3 - ℓ)) * hxy + e
  rw [h a b hab, h b a ((mul_comm b a).trans hab), inv_div, miyawakiStandardEulerFactor,
    ellipticEulerFactor_eq_prod, hf, standardEulerFactor, g.satakeRatios_eq p hg]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, mul_comp, sub_comp, one_comp, C_comp, X_comp, map_mul]
  ring1

/-- **The spinor Euler factor of the Ikeda–Miyawaki lift has the shape of a spinor Euler factor of
degree `3` and weight `ℓ`**: for `p ≠ 0` and Satake parameters `{a, b}` of `f` and `{c, d}` of `g`
at `p`, taken in either order, it is `∏_{i=1}^4 (1 - β_i X)(1 - p^{3ℓ-6} β_i⁻¹ X)`, the inverse
roots pairing up with product `p^{3ℓ-6}`, with `β_1 = c p^{ℓ-2}`, `β_2 = d p^{ℓ-2}`, `β_3 = a c`
and `β_4 = a d`, which are nonzero; their partners `p^{3ℓ-6} β_i⁻¹` are `d p^{ℓ-3}`, `c p^{ℓ-3}`,
`b d` and `b c`. -/
lemma miyawakiSpinorEulerFactor_eq (hp : p ≠ 0) (hf : f.satakeParameters p = {a, b})
    (hg : g.satakeParameters p = {c, d}) :
    letI q : ℂ := (p : ℂ) ^ (3 * ℓ - 6)
    letI β₁ : ℂ := c * (p : ℂ) ^ (ℓ - 2)
    letI β₂ : ℂ := d * (p : ℂ) ^ (ℓ - 2)
    letI β₃ : ℂ := a * c
    letI β₄ : ℂ := a * d
    f.miyawakiSpinorEulerFactor g p = (1 - C β₁ * X) * (1 - C (q / β₁) * X) *
        ((1 - C β₂ * X) * (1 - C (q / β₂) * X)) * ((1 - C β₃ * X) * (1 - C (q / β₃) * X)) *
        ((1 - C β₄ * X) * (1 - C (q / β₄) * X)) := by
  rcases (f.satakeParameters_eq_pair_iff p).mp hf with ⟨-, hab⟩
  rcases (g.satakeParameters_eq_pair_iff p).mp hg with ⟨-, hcd⟩
  rw [f.dirichletLift_natCast_eq_one, one_mul] at hab
  rw [g.dirichletLift_natCast_eq_one, one_mul] at hcd
  have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  have ha : a ≠ 0 := f.ne_zero_of_mem_satakeParameters p hp (hf ▸ Multiset.mem_cons_self a _)
  have hc : c ≠ 0 := g.ne_zero_of_mem_satakeParameters p hp (hg ▸ Multiset.mem_cons_self c _)
  have hd : d ≠ 0 := g.ne_zero_of_mem_satakeParameters p hp
    (hg ▸ Multiset.mem_cons_of_mem (Multiset.mem_singleton_self d))
  have hpℓ : (p : ℂ) ^ (ℓ - 2) ≠ 0 := zpow_ne_zero _ hp'
  have e₁ :
      (p : ℂ) ^ (3 * ℓ - 6) = (p : ℂ) ^ (ℓ - 1) * ((p : ℂ) ^ (ℓ - 3) * (p : ℂ) ^ (ℓ - 2)) := by
    rw [← zpow_add₀ hp', ← zpow_add₀ hp']
    exact congrArg _ (by ring1)
  have e₂ : (p : ℂ) ^ (3 * ℓ - 6) = (p : ℂ) ^ (2 * ℓ - 4 - 1) * (p : ℂ) ^ (ℓ - 1) := by
    rw [← zpow_add₀ hp']
    exact congrArg _ (by ring1)
  have h₁ (x y : ℂ) (hx : x ≠ 0) (hxy : x * y = (p : ℂ) ^ (ℓ - 1)) :
      (p : ℂ) ^ (3 * ℓ - 6) / (x * (p : ℂ) ^ (ℓ - 2)) = y * (p : ℂ) ^ (ℓ - 3) :=
    div_eq_of_eq_mul (mul_ne_zero hx hpℓ) <| by
      linear_combination e₁ - ((p : ℂ) ^ (ℓ - 3) * (p : ℂ) ^ (ℓ - 2)) * hxy
  have h₂ (x y : ℂ) (hx : x ≠ 0) (hxy : x * y = (p : ℂ) ^ (ℓ - 1)) :
      (p : ℂ) ^ (3 * ℓ - 6) / (a * x) = b * y :=
    div_eq_of_eq_mul (mul_ne_zero ha hx) <| by
      linear_combination e₂ - x * y * hab - (p : ℂ) ^ (2 * ℓ - 4 - 1) * hxy
  have hdc : d * c = (p : ℂ) ^ (ℓ - 1) :=
    (mul_comm d c).trans hcd
  rw [h₁ c d hc hcd, h₁ d c hd hdc, h₂ c d hc hcd, h₂ d c hd hdc, miyawakiSpinorEulerFactor,
    ellipticEulerFactor_eq_prod, rankinSelbergEulerFactor, hf, hg]
  simp only [Multiset.insert_eq_cons, ← Multiset.cons_zero, Multiset.cons_product,
    Multiset.zero_product, Multiset.map_cons, Multiset.map_zero, Multiset.map_add,
    Multiset.prod_add, Multiset.prod_cons, Multiset.prod_zero, mul_comp, sub_comp, one_comp, C_comp,
    X_comp, map_mul]
  ring1

end HeckeRing.GL2.Newform
