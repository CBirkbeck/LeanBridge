import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.GaussSum
import Mathlib.NumberTheory.LSeries.PrimesInAP
import TauCeti.NumberTheory.DirichletCharacter.GaussSum
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Character
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.OfSquarefree

/-!
# Primitive quadratic Dirichlet characters

A primitive quadratic Dirichlet character `χ` of modulus `M` is the character `(D/·)` of a
fundamental discriminant `D` with `|D| = M`, i.e. the Kronecker character of the quadratic field
`ℚ(√D)` when `χ` is nontrivial. This is proved here for integer-valued characters, with Tau Ceti's
`TauCeti.Multiquadratic.fundamentalDiscriminantChar`. At an odd prime `p ∤ M`, the Gauss sum `τ` of
`χ`, computed in a field of characteristic `p` containing the `M`-th roots of unity, satisfies
`τ² = χ(-1) M` and `τᵖ = χ(p) τ`, so `χ(p) = (χ(-1) M)^((p - 1)/2) = (χ(-1) M / p)` by Euler's
criterion. Writing `χ(-1) M = b² d` with `d` squarefree, `χ` and the character of the fundamental
discriminant `D` of `ℚ(√d)` agree at almost all primes, so they are equal, as primitive Dirichlet
characters that agree at almost all primes are equal, by Dirichlet's theorem on primes in arithmetic
progressions.

## Main definitions

* `DirichletCharacter.intCharOfIsQuadratic`: the integer-valued character of a quadratic complex
  Dirichlet character.

## Main results

* `DirichletCharacter.eq_of_isPrimitive_of_eventually_eq`: primitive Dirichlet characters that
  agree at almost all primes are equal.
* `DirichletCharacter.IsPrimitive.apply_eq_legendreSym`: a primitive quadratic character `χ` of
  modulus `M` takes the value `(χ(-1) M / p)` at an odd prime `p ∤ M`.
* `DirichletCharacter.IsPrimitive.exists_eq_fundamentalDiscriminantChar`,
  `DirichletCharacter.IsPrimitive.exists_eq_ringHomComp_fundamentalDiscriminantChar`: a primitive
  quadratic character, with integer or complex values, is the character of a fundamental
  discriminant.
-/

open TauCeti Multiquadratic

namespace DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R] {M : ℕ} {χ : DirichletCharacter ℤ M}
  {ψ : DirichletCharacter ℂ M} {F : Type*} [Field F] {p : ℕ}

/-- **Primitive Dirichlet characters that agree at almost all primes are equal**: they induce the
same character modulo the least common multiple of their moduli, as every class of units contains
arbitrarily large primes (Dirichlet's theorem), so they have the same conductor, their modulus. -/
lemma eq_of_isPrimitive_of_eventually_eq {x y : Σ M : ℕ+, DirichletCharacter R M}
    (hx : x.2.IsPrimitive) (hy : y.2.IsPrimitive)
    (h : ∀ᶠ p : ℕ in Filter.cofinite, p.Prime → x.2 p = y.2 p) : x = y := by
  rcases x with ⟨M, χ⟩
  rcases y with ⟨M', ψ⟩
  have : NeZero (Nat.lcm M M') := ⟨Nat.lcm_ne_zero M.ne_zero M'.ne_zero⟩
  rcases Filter.eventually_atTop.mp (Nat.cofinite_eq_atTop ▸ h) with ⟨B, hB⟩
  have hL : χ.changeLevel (Nat.dvd_lcm_left M M') = ψ.changeLevel (Nat.dvd_lcm_right M M') := by
    refine MulChar.ext fun u ↦ ?_
    rcases Nat.forall_exists_prime_gt_and_eq_mod u.isUnit (B + Nat.lcm M M') with ⟨p, hpB, hp, hpu⟩
    have hp' : IsCoprime (p : ℤ) (Nat.lcm M M' : ℕ) := Nat.isCoprime_iff_coprime.mpr
      (Nat.coprime_of_lt_prime (NeZero.ne _) (by omega) hp)
    rw [← hpu, ← Int.cast_natCast, changeLevel_eq_cast_of_dvd' _ _ hp',
      changeLevel_eq_cast_of_dvd' _ _ hp']
    simpa using hB p (by omega) hp
  have hM : M = M' := PNat.coe_inj.mp <| hx.symm.trans <| (conductor_changeLevel _ _).symm.trans <|
    (congrArg conductor hL).trans <| (conductor_changeLevel _ _).trans hy
  subst hM
  exact congrArg _ (changeLevel_injective _ hL)

lemma IsQuadratic.apply_unit_eq_one_or (hq : χ.IsQuadratic) (u : (ZMod M)ˣ) :
    χ u = 1 ∨ χ u = -1 :=
  (hq u).resolve_left (u.isUnit.map χ).ne_zero

variable [NeZero M] in
lemma IsPrimitive.ringHomComp_intCast (hF : ringChar F ≠ 2) (hχ : χ.IsPrimitive)
    (hq : χ.IsQuadratic) : IsPrimitive (χ.ringHomComp (Int.castRingHom F)) := by
  refine le_antisymm (Nat.le_of_dvd (NeZero.pos M) (conductor_dvd_level _)) ?_
  have h : FactorsThrough (χ.ringHomComp (Int.castRingHom F))
      (conductor (χ.ringHomComp (Int.castRingHom F))) :=
    factorsThrough_conductor (χ.ringHomComp (Int.castRingHom F))
  refine hχ.symm.trans_le (Nat.sInf_le ((factorsThrough_iff_ker_unitsMap h.dvd).mpr fun u hu ↦ ?_))
  have hu' : (χ.ringHomComp (Int.castRingHom F)).toUnitHom u = 1 :=
    MonoidHom.mem_ker.mp ((factorsThrough_iff_ker_unitsMap h.dvd).mp h hu)
  have h1 : ((χ u : ℤ) : F) = ((1 : ℤ) : F) := by
    simpa using congrArg ((↑) : Fˣ → F) hu'
  exact MonoidHom.mem_ker.mpr <| Units.ext <| by
    simpa using Int.cast_injOn_of_ringChar_ne_two hF (hq u) (by simp) h1

private lemma eq_legendreSym_of_pow_eq [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) {τ : F} {a d : ℤ}
    (ha : a ∈ ({0, 1, -1} : Set ℤ)) (hd : (d : ZMod p) ≠ 0) (h2 : τ ^ 2 = d) (hp : τ ^ p = a * τ) :
    a = legendreSym p d := by
  have hF : ringChar F ≠ 2 := by
    rwa [ringChar.eq F p]
  have hdF : (d : F) ≠ 0 := by
    rwa [Ne, CharP.intCast_eq_zero_iff F p, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hτ : τ ≠ 0 := fun hτ ↦ hdF (by rw [← h2, hτ, zero_pow two_ne_zero])
  have hpow : (a : F) = (d : F) ^ (p / 2) := by
    refine mul_right_cancel₀ hτ ?_
    rw [← hp, ← h2, ← pow_mul, ← pow_succ, Nat.two_mul_div_two_add_one_of_odd
      ((Fact.out : p.Prime).odd_of_ne_two hp2)]
  refine Int.cast_injOn_of_ringChar_ne_two hF ha (Or.inr (legendreSym.eq_one_or_neg_one p hd))
    (hpow.trans ?_)
  rw [← map_intCast (ZMod.castHom (dvd_refl p) F) (legendreSym p d), legendreSym.eq_pow, map_pow,
    map_intCast]

variable [NeZero M] in
/-- **The values of a primitive quadratic character at odd primes are Legendre symbols**: for a
primitive quadratic Dirichlet character `χ` of modulus `M` and an odd prime `p ∤ M`,
`χ(p) = (χ(-1) M / p)`. The Gauss sum `τ` of `χ` in the cyclotomic field of level `M` over `𝔽_p`
satisfies `τ² = χ(-1) M` and `τᵖ = χ(p) τ`. -/
lemma IsPrimitive.apply_eq_legendreSym (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) [Fact p.Prime]
    (hp2 : p ≠ 2) (hpM : p.Coprime M) : χ p = legendreSym p (χ (-1) * M) := by
  have hMp : (M : ZMod p) ≠ 0 := fun h ↦ (Fact.out : p.Prime).coprime_iff_not_dvd.mp hpM
    ((ZMod.natCast_eq_zero_iff M p).mp h)
  have : NeZero (M : ZMod p) := ⟨hMp⟩
  have : CharP (CyclotomicField M (ZMod p)) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) (CyclotomicField M (ZMod p))).injective p
  have hF : ringChar (CyclotomicField M (ZMod p)) ≠ 2 := by
    rwa [ringChar.eq (CyclotomicField M (ZMod p)) p]
  have hζ :
      IsPrimitiveRoot (IsCyclotomicExtension.zeta M (ZMod p) (CyclotomicField M (ZMod p))) M :=
    IsCyclotomicExtension.zeta_spec M (ZMod p) (CyclotomicField M (ZMod p))
  have hpu : IsUnit (p : ZMod M) := (ZMod.isUnit_iff_coprime p M).mpr hpM
  have hχ1 : χ (-1) = 1 ∨ χ (-1) = -1 := by
    simpa using IsQuadratic.apply_unit_eq_one_or hq (-1)
  refine eq_legendreSym_of_pow_eq (τ := gaussSum (χ.ringHomComp (Int.castRingHom _))
    (AddChar.zmodChar M hζ.pow_eq_one)) hp2 (hq p) ?_ ?_ ?_
  · rw [Int.cast_mul, Int.cast_natCast]
    exact mul_ne_zero (by rcases hχ1 with h | h <;> simp [h]) hMp
  · refine (gaussSum_sq_of_isPrimitive_of_isQuadratic (hχ.ringHomComp_intCast hF hq) (hq.comp _)
      (AddChar.zmodChar_primitive_of_primitive_root M hζ)).trans ?_
    rw [MulChar.ringHomComp_apply, eq_intCast, ZMod.card, Int.cast_mul, Int.cast_natCast]
  · refine ((hq.comp _).gaussSum_frob p hpu _).trans ?_
    rw [MulChar.ringHomComp_apply, eq_intCast]

variable [NeZero M] in
/-- **A primitive quadratic Dirichlet character is the character of a fundamental discriminant**:
for a primitive quadratic `χ` of modulus `M`, there is a fundamental discriminant `D` with
`|D| = M` and `χ = (D/·)`, Tau Ceti's `fundamentalDiscriminantChar`. If `χ(-1) M = b² d` with `d`
squarefree, `D` is the discriminant of `ℚ(√d)`, and `χ` and `(D/·)` agree at the odd primes not
dividing `M`. -/
lemma IsPrimitive.exists_eq_fundamentalDiscriminantChar (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    ∃ (D : ℤ) (hD : D.IsFundamentalDiscr),
      (⟨⟨M, NeZero.pos M⟩, χ⟩ : Σ M : ℕ+, DirichletCharacter ℤ M) =
        ⟨⟨D.natAbs, Int.natAbs_pos.mpr hD.ne_zero⟩, fundamentalDiscriminantChar D hD⟩ := by
  rcases exists_sq_mul_squarefree M with ⟨b, a, hab, ha⟩
  have hχ1 : χ (-1) = 1 ∨ χ (-1) = -1 := by
    simpa using IsQuadratic.apply_unit_eq_one_or hq (-1)
  have hd : Squarefree (χ (-1) * a) := Int.squarefree_natAbs.mp <| by
    rcases hχ1 with h | h <;> simpa [h] using ha
  refine ⟨_, isFundamentalDiscr_fundamentalDiscriminant hd, eq_of_isPrimitive_of_eventually_eq hχ
    (isPrimitive_fundamentalDiscriminantChar (isFundamentalDiscr_fundamentalDiscriminant hd)) ?_⟩
  filter_upwards [Nat.cofinite_eq_atTop ▸ Filter.eventually_gt_atTop (2 * M)] with p hpM hp
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by
    have : 0 < M := NeZero.pos M
    omega
  have hpM' : p.Coprime M := Nat.coprime_of_lt_prime (NeZero.ne M) (by omega) hp
  rcases exists_sq_mul_eq_fundamentalDiscriminant (χ (-1) * a) with ⟨c, hc, hcd⟩
  have hb : ((b : ℤ) : ZMod p) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    exact fun hpb ↦ hp.coprime_iff_not_dvd.mp hpM'
      (hab ▸ (hpb.pow two_ne_zero).mul_right a)
  have hc' : (c : ZMod p) ≠ 0 := by
    rcases hc with rfl | rfl
    · simp
    · rw [Int.cast_ofNat, Ne, ← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff]
      exact fun h ↦ hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  have hD : fundamentalDiscriminantChar _ (isFundamentalDiscr_fundamentalDiscriminant hd) p =
      legendreSym p (fundamentalDiscriminant (χ (-1) * a)) := by
    simpa using fundamentalDiscriminantChar_natCast_eq_legendreSym
      (isFundamentalDiscr_fundamentalDiscriminant hd) hp2
  have hM : (M : ℤ) = (b : ℤ) ^ 2 * a :=
    mod_cast hab.symm
  refine (hχ.apply_eq_legendreSym hq hp2 hpM').trans (Eq.trans ?_ hD.symm)
  rw [hM, ← hcd]
  simp only [legendreSym.mul, legendreSym.sq_one' p hb, legendreSym.sq_one' p hc', one_mul]

variable (ψ) in
/-- The **integer-valued character** of a quadratic complex Dirichlet character `ψ`: the character
with the values `0`, `1`, `-1` of `ψ`, seen in `ℤ`. -/
noncomputable def intCharOfIsQuadratic (hψ : ψ.IsQuadratic) : DirichletCharacter ℤ M where
  toFun a := if ψ a = 1 then 1 else if ψ a = -1 then -1 else 0
  map_one' := by
    simp
  map_mul' a b := by
    rcases hψ a with ha | ha | ha <;> rcases hψ b with hb | hb | hb <;> norm_num [ha, hb]
  map_nonunit' a ha := by
    simp [ψ.map_nonunit ha]

lemma ringHomComp_intCharOfIsQuadratic (hψ : ψ.IsQuadratic) :
    (ψ.intCharOfIsQuadratic hψ).ringHomComp (Int.castRingHom ℂ) = ψ :=
  MulChar.ext' fun a ↦ by
    rcases hψ a with ha | ha | ha <;> norm_num [intCharOfIsQuadratic, ha]

lemma isQuadratic_intCharOfIsQuadratic (hψ : ψ.IsQuadratic) :
    (ψ.intCharOfIsQuadratic hψ).IsQuadratic := fun a ↦ by
  rcases hψ a with ha | ha | ha <;> norm_num [intCharOfIsQuadratic, ha]

variable [NeZero M] in
/-- **A primitive quadratic complex Dirichlet character is the character of a fundamental
discriminant**: for a primitive quadratic `ψ` of modulus `M` with complex values, there is a
fundamental discriminant `D` with `|D| = M` and `ψ = (D/·)`, the character of `D` with complex
values. -/
lemma IsPrimitive.exists_eq_ringHomComp_fundamentalDiscriminantChar (hψ : ψ.IsPrimitive)
    (hq : ψ.IsQuadratic) : ∃ (D : ℤ) (hD : D.IsFundamentalDiscr),
      (⟨⟨M, NeZero.pos M⟩, ψ⟩ : Σ M : ℕ+, DirichletCharacter ℂ M) = ⟨⟨D.natAbs,
        Int.natAbs_pos.mpr hD.ne_zero⟩, (fundamentalDiscriminantChar D hD).ringHomComp
          (Int.castRingHom ℂ)⟩ := by
  have hχ : IsPrimitive (ψ.intCharOfIsQuadratic hq) :=
    (isPrimitive_ringHomComp_iff _ _ Int.cast_injective).mp
      ((ringHomComp_intCharOfIsQuadratic hq).symm ▸ hψ)
  rcases hχ.exists_eq_fundamentalDiscriminantChar (isQuadratic_intCharOfIsQuadratic hq) with
    ⟨D, hD, h⟩
  exact ⟨D, hD, (congrArg (fun ψ' : DirichletCharacter ℂ M ↦
    (⟨⟨M, NeZero.pos M⟩, ψ'⟩ : Σ M : ℕ+, DirichletCharacter ℂ M))
      (ringHomComp_intCharOfIsQuadratic hq).symm).trans
    (congrArg (fun x : Σ M : ℕ+, DirichletCharacter ℤ M ↦
      (⟨x.1, x.2.ringHomComp (Int.castRingHom ℂ)⟩ : Σ M : ℕ+, DirichletCharacter ℂ M)) h)⟩

end DirichletCharacter
