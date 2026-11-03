import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.NebentypusRigidity
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.InnerTwist
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.SelfTwistField

/-!
# Self twists are quadratic, and the self twist field

The LMFDB states (LMFDB `cmf.self_twist_field`) that the inner twists of a newform `f` that are self
twists arise either from the trivial character or from the Kronecker character of a quadratic field
`K`, and that `f` has complex multiplication by `K` if `K` is imaginary and real multiplication by
`K` if `K` is real. This file proves that statement, with no hypothesis on `f`.

Let `a_p(f) = ψ(p) a_p(f)` at almost all primes `p`. By Tau Ceti, the twist `f ⊗ ψ` has a primitive
associate `g`, a newform of some level, with nebentypus `χ_f ψ²` and `a_p(g) = ψ(p) a_p(f)`. So
`a_p(g) = a_p(f)` at almost all primes, and nebentypus rigidity
(`HeckeRing.GL2.Newform.comp_unitsMap_eq_of_eventually_coeff_eq`, by a weak Rankin–Selberg argument)
gives `χ_f ψ² = χ_f`, that is `ψ² = 1`. Neither strong multiplicity one for the newform itself, nor
Galois representations, are used. The rest, that a primitive quadratic character is the Kronecker
character of a quadratic field, is in
`LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.SelfTwistField`.

## Main definitions

* `HeckeRing.GL2.Newform.HasSelfTwist.discr`: the discriminant of the self twist field.

## Main results

* `HeckeRing.GL2.Newform.IsTwistAtAlmostAllPrimes.isQuadratic_of_self`: a character with
  `a_p(f) = ψ(p) a_p(f)` at almost all primes `p` is quadratic.
* `HeckeRing.GL2.Newform.HasSelfTwist.isQuadratic_character`: a self twist character is quadratic.
* `HeckeRing.GL2.Newform.HasSelfTwist.exists_kroneckerChar_of_ne_one`: a nontrivial self twist
  character is the Kronecker character of a quadratic field, by which `f` has complex or real
  multiplication.
* `HeckeRing.GL2.Newform.eq_one_or_exists_kroneckerChar_of_mk_self_mem_innerTwists`: the inner
  twists that are self twists, as the LMFDB states (LMFDB `cmf.self_twist_field`).
* `HeckeRing.GL2.Newform.HasSelfTwist.hasCMBy_or_hasRMBy_discr`: `f` has complex or real
  multiplication by the self twist field of a nontrivial self twist.
-/

open UpperHalfPlane

namespace HeckeRing.GL2.Newform

variable {N M : ℕ} [NeZero N] {k : ℤ} {f : Newform N k} {ψ : DirichletCharacter ℂ M}

/-- **A self twist character is quadratic**: if `a_p(f) = ψ(p) a_p(f)` for all but finitely many
primes `p`, for a Dirichlet character `ψ` of positive modulus, then `ψ² = 1`. -/
lemma IsTwistAtAlmostAllPrimes.isQuadratic_of_self [NeZero M]
    (hf : f.IsTwistAtAlmostAllPrimes ψ f) : ψ.IsQuadratic := by
  have hNL : N * M ∣ N * M * M := dvd_mul_right (N * M) M
  have hML : M * M ∣ N * M * M := ⟨N, by ring1⟩
  rcases exists_newform_qExpansion_coeff_prime_eq_twist f ψ hNL hML with ⟨R, _, hR, g, hgχ, hg⟩
  have hgf : ∀ᶠ p in Filter.cofinite, p.Prime → (qExpansion 1 g.toCuspForm).coeff p =
      (qExpansion 1 f.toCuspForm).coeff p := by
    filter_upwards [hf, (N * M * M).primeFactors.finite_toSet.compl_mem_cofinite] with p hfp hpL hp
    exact (hg p hp (hp.coprime_iff_not_dvd.mpr fun hd ↦
      hpL (Nat.mem_primeFactors.mpr ⟨hp, hd, NeZero.ne _⟩))).trans (hfp hp).symm
  have h1 : (ψ.toUnitHom.comp (ZMod.unitsMap (dvd_of_mul_left_dvd hML))) ^ 2 = 1 :=
    left_eq_mul.mp ((comp_unitsMap_eq_of_eventually_coeff_eq f g (dvd_of_mul_right_dvd hNL) hR
      hgf).trans hgχ)
  refine MulChar.isQuadratic_iff_sq_eq_one.mpr <| MulChar.ext fun u ↦ ?_
  rcases ZMod.unitsMap_surjective (dvd_of_mul_left_dvd hML) u with ⟨w, rfl⟩
  have hw :
      ((((ψ.toUnitHom.comp (ZMod.unitsMap (dvd_of_mul_left_dvd hML))) ^ 2) w : ℂˣ) : ℂ) = 1 := by
    rw [h1, MonoidHom.one_apply, Units.val_one]
  simp only [MonoidHom.pow_apply] at hw
  rw [MulChar.pow_apply' _ two_ne_zero, MulChar.one_apply_coe]
  exact hw

/-- **A self twist character is quadratic** (LMFDB `cmf.self_twist`, `cmf.self_twist_field`), with
no hypothesis: if `f` admits a self twist by `ψ`, then `ψ² = 1`. -/
lemma HasSelfTwist.isQuadratic_character (hf : f.HasSelfTwist ψ) : ψ.IsQuadratic :=
  have : NeZero M := ⟨hf.1⟩
  hf.2.2.isQuadratic_of_self

/-- **A nontrivial self twist character is the Kronecker character of a quadratic field**, by which
`f` has complex or real multiplication (LMFDB `cmf.self_twist_field`): there is a fundamental
discriminant `D` with `ψ = (D/·)` (of modulus `|D|`), and `f` has complex multiplication by `ℚ(√D)`
if `D < 0` and real multiplication by it if `D > 1`. -/
lemma HasSelfTwist.exists_kroneckerChar_of_ne_one (hf : f.HasSelfTwist ψ) (hψ : ψ ≠ 1) :
    ∃ (D : ℤ) (hD : D.IsFundamentalDiscr),
      (⟨⟨M, Nat.pos_of_ne_zero hf.1⟩, ψ⟩ : Σ M : ℕ+, DirichletCharacter ℂ M) =
        ⟨⟨D.natAbs, Int.natAbs_pos.mpr hD.ne_zero⟩, hD.kroneckerChar⟩ ∧
      (f.HasCMBy D ∨ f.HasRMBy D) :=
  hf.exists_kroneckerChar_of_isQuadratic hf.isQuadratic_character hψ

/-- **The self twists of a newform** (LMFDB `cmf.self_twist_field`): an inner twist `(χ, f)` of `f`
that is a self twist arises either from the trivial character (of modulus `1`) or from the
Kronecker character of a quadratic field `ℚ(√D)`, by which `f` has complex multiplication if
`D < 0` and real multiplication if `D > 1`. -/
lemma eq_one_or_exists_kroneckerChar_of_mk_self_mem_innerTwists
    {x : Σ M : ℕ+, DirichletCharacter ℂ M} (hx : (x, f) ∈ f.innerTwists) : x = ⟨1, 1⟩ ∨
      ∃ (D : ℤ) (hD : D.IsFundamentalDiscr),
        x = ⟨⟨D.natAbs, Int.natAbs_pos.mpr hD.ne_zero⟩, hD.kroneckerChar⟩ ∧
          (f.HasCMBy D ∨ f.HasRMBy D) := by
  rcases x with ⟨M, χ⟩
  have hf : f.HasSelfTwist χ := mk_self_mem_innerTwists_iff.mp hx
  by_cases hχ : χ = 1
  · subst hχ
    have hM : M = 1 := PNat.coe_eq_one_iff.mp <| hf.2.1.symm.trans DirichletCharacter.conductor_one
    subst hM
    exact Or.inl rfl
  · exact Or.inr <| hf.exists_kroneckerChar_of_ne_one hχ

/-- The **discriminant of the self twist field** of `f` for a self twist `ψ`
(LMFDB `cmf.self_twist_field`): the unique fundamental discriminant `D` with `ψ = (D/·)`, by which
the LMFDB identifies the field `K = ℚ(√D)`; it is `1` for the trivial character. -/
noncomputable def HasSelfTwist.discr (hf : f.HasSelfTwist ψ) : ℤ :=
  haveI : NeZero M := ⟨hf.1⟩
  ψ.quadraticDiscr hf.2.1 hf.isQuadratic_character

/-- **A newform has complex or real multiplication by its self twist field**: for a nontrivial self
twist `ψ`, the newform `f` has complex multiplication by `ℚ(√D)` if `D < 0` and real multiplication
by it if `D > 1`, for `D` the discriminant of the self twist field. -/
lemma HasSelfTwist.hasCMBy_or_hasRMBy_discr (hf : f.HasSelfTwist ψ) (hψ : ψ ≠ 1) :
    f.HasCMBy hf.discr ∨ f.HasRMBy hf.discr := by
  have : NeZero M := ⟨hf.1⟩
  rcases hf.exists_kroneckerChar_of_ne_one hψ with ⟨D, hD, h, hfD⟩
  have hdisc : hf.discr = D :=
    DirichletCharacter.quadraticDiscr_eq hf.2.1 hf.isQuadratic_character hD h
  rwa [hdisc]

end HeckeRing.GL2.Newform
