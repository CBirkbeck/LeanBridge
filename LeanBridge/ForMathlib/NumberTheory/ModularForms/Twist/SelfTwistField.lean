import LeanBridge.ForMathlib.NumberTheory.DirichletCharacter.PrimitiveQuadratic
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.SelfTwist

/-!
# The self twist field of a newform

The LMFDB states (LMFDB `cmf.self_twist_field`, `cmf.self_twist`) that the inner twists of a
newform `f` that are self twists arise either from the trivial character or from the Kronecker
character of a quadratic field `K`, the self twist field, and that `f` has complex multiplication by
`K` if `K` is imaginary and real multiplication by `K` if `K` is real.

The first step is that a self twist character `χ` is quadratic. If `f` is its own twist `f ⊗ χ` in
the sense of the LMFDB (`aₙ(f) = χ(n) aₙ(f)` for all `n` coprime to the level and the modulus of
`χ`, `HeckeRing.GL2.Newform.IsTwistBy`), this is elementary and proved here: at a prime `p` with
`χ(p)² ≠ 1`, both `a_p` and `a_{p²}` vanish, against the Hecke relation
`a_{p²} = a_p² - ε(p) p^{k - 1}`, so `χ(p)² = 1` at almost all primes, hence everywhere by
Dirichlet's theorem on primes in arithmetic progressions. A self twist in the sense of
`HeckeRing.GL2.Newform.HasSelfTwist`, through `a_p(f) = χ(p) a_p(f)` at almost all primes, is the
twist `f ⊗ χ = f` by strong multiplicity one, which is not proved here: the results on such self
twists take it as an explicit hypothesis on `f`.

The second step is that a nontrivial primitive quadratic Dirichlet character is the Kronecker
character `(D/·)` of the quadratic field `ℚ(√D)` of a fundamental discriminant `D ≠ 1`
(`Int.IsFundamentalDiscr.kroneckerChar`), which is
`DirichletCharacter.IsPrimitive.exists_eq_ringHomComp_fundamentalDiscriminantChar`. The newform
then has complex multiplication by `ℚ(√D)` if `D < 0` and real multiplication if `D > 1`. The
discriminant `D`, by which the LMFDB identifies the self twist field, is unique, and is
`DirichletCharacter.quadraticDiscr`.

## Main definitions

* `DirichletCharacter.quadraticDiscr`: the discriminant of the quadratic field of a primitive
  quadratic character, i.e. of the self twist field (LMFDB `cmf.self_twist_field`).

## Main results

* `Int.IsFundamentalDiscr.eq_of_sigma_kroneckerChar_eq`: a fundamental discriminant is determined
  by its Kronecker character.
* `DirichletCharacter.quadraticDiscr_eq`: `quadraticDiscr` is the unique fundamental discriminant
  `D` with `χ = (D/·)`.
* `HeckeRing.GL2.Newform.IsTwistBy.isQuadratic`: if `f ⊗ χ = f`, then `χ` is quadratic.
* `HeckeRing.GL2.Newform.HasSelfTwist.isQuadratic`: a self twist character is quadratic, if
  strong multiplicity one holds for `f`.
* `HeckeRing.GL2.Newform.HasSelfTwist.hasCMBy_or_hasRMBy`: a self twist by the Kronecker character
  of a quadratic field gives complex or real multiplication by that field.
* `HeckeRing.GL2.Newform.IsTwistBy.exists_kroneckerChar`: if `f ⊗ χ = f` for a nontrivial `χ`,
  then `χ` is the Kronecker character of a quadratic field, by which `f` has complex or real
  multiplication.
* `HeckeRing.GL2.Newform.HasSelfTwist.exists_kroneckerChar`: a nontrivial self twist character is
  the Kronecker character of a quadratic field, by which `f` has complex or real multiplication, if
  strong multiplicity one holds for `f`.
-/

open UpperHalfPlane

namespace Int.IsFundamentalDiscr

variable {D D' : ℤ}

/-- **A fundamental discriminant is determined by its Kronecker character**: `|D|` is the modulus of
`(D/·)` and the sign of `D` its value at `-1`. -/
lemma eq_of_sigma_kroneckerChar_eq (hD : D.IsFundamentalDiscr) (hD' : D'.IsFundamentalDiscr)
    (h : (⟨⟨D.natAbs, Int.natAbs_pos.mpr hD.ne_zero⟩, hD.kroneckerChar⟩ :
      Σ M : ℕ+, DirichletCharacter ℂ M) = ⟨⟨D'.natAbs, Int.natAbs_pos.mpr hD'.ne_zero⟩,
        hD'.kroneckerChar⟩) : D = D' := by
  have hs : (D.sign : ℂ) = D'.sign := by
    rw [← hD.kroneckerChar_neg_one, ← hD'.kroneckerChar_neg_one]
    exact congrArg (fun x : Σ M : ℕ+, DirichletCharacter ℂ M ↦ x.2 (-1)) h
  have ha : D.natAbs = D'.natAbs :=
    congrArg (fun x : Σ M : ℕ+, DirichletCharacter ℂ M ↦ (x.1 : ℕ)) h
  rw [← D.sign_mul_natAbs, ← D'.sign_mul_natAbs, Int.cast_injective hs, ha]

end Int.IsFundamentalDiscr

namespace DirichletCharacter

variable {M : ℕ} [NeZero M] {χ : DirichletCharacter ℂ M} {D : ℤ}

variable (χ) in
/-- The **discriminant of the quadratic field** of a primitive quadratic Dirichlet character `χ`
(LMFDB `cmf.self_twist_field`): the unique fundamental discriminant `D` with `χ = (D/·)`, by which
the LMFDB identifies the self twist field `ℚ(√D)` of a nontrivial self twist `χ`. It is `1` for the
trivial character. -/
noncomputable def quadraticDiscr (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) : ℤ :=
  (hχ.exists_eq_ringHomComp_fundamentalDiscriminantChar hq).choose

lemma isFundamentalDiscr_quadraticDiscr (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    (χ.quadraticDiscr hχ hq).IsFundamentalDiscr :=
  (hχ.exists_eq_ringHomComp_fundamentalDiscriminantChar hq).choose_spec.choose

lemma sigma_eq_kroneckerChar_quadraticDiscr (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) :
    (⟨⟨M, NeZero.pos M⟩, χ⟩ : Σ M : ℕ+, DirichletCharacter ℂ M) =
      ⟨⟨(χ.quadraticDiscr hχ hq).natAbs, Int.natAbs_pos.mpr
        (isFundamentalDiscr_quadraticDiscr hχ hq).ne_zero⟩,
        (isFundamentalDiscr_quadraticDiscr hχ hq).kroneckerChar⟩ :=
  (hχ.exists_eq_ringHomComp_fundamentalDiscriminantChar hq).choose_spec.choose_spec

/-- **The discriminant of the quadratic field of `χ` is the unique fundamental discriminant `D`
with `χ = (D/·)`.** -/
lemma quadraticDiscr_eq (hχ : χ.IsPrimitive) (hq : χ.IsQuadratic) (hD : D.IsFundamentalDiscr)
    (h : (⟨⟨M, NeZero.pos M⟩, χ⟩ : Σ M : ℕ+, DirichletCharacter ℂ M) =
      ⟨⟨D.natAbs, Int.natAbs_pos.mpr hD.ne_zero⟩, hD.kroneckerChar⟩) :
    χ.quadraticDiscr hχ hq = D :=
  (isFundamentalDiscr_quadraticDiscr hχ hq).eq_of_sigma_kroneckerChar_eq hD
    ((sigma_eq_kroneckerChar_quadraticDiscr hχ hq).symm.trans h)

end DirichletCharacter

namespace HeckeRing.GL2.Newform

variable {N M : ℕ} [NeZero N] {k : ℤ} {f : Newform N k} {χ : DirichletCharacter ℂ M} {p : ℕ}

lemma IsTwistBy.apply_sq_eq_one (hf : f.IsTwistBy χ f) (hp : p.Prime) (hpNM : p.Coprime (N * M)) :
    χ p ^ 2 = 1 := by
  have hpN : p.Coprime N := hpNM.coprime_dvd_right (dvd_mul_right N M)
  have h₁ : (qExpansion 1 f.toCuspForm).coeff p = χ p * (qExpansion 1 f.toCuspForm).coeff p :=
    hf.2.2 p hpNM
  have h₂ : (qExpansion 1 f.toCuspForm).coeff (p ^ 2) =
      χ p ^ 2 * (qExpansion 1 f.toCuspForm).coeff (p ^ 2) := by
    rw [← map_pow, ← Nat.cast_pow]
    exact hf.2.2 _ (hpNM.pow_left 2)
  have h₃ : (qExpansion 1 f.toCuspForm).coeff (p ^ 2) = (qExpansion 1 f.toCuspForm).coeff p *
      (qExpansion 1 f.toCuspForm).coeff p - f.χ (ZMod.unitOfCoprime p hpN) * (p : ℂ) ^ (k - 1) := by
    simpa using f.toEigenformAwayFromLevel.qExpansion_coeff_prime_pow_add_two f.isNorm
      (p := ⟨p, hp.pos⟩) hp hpN 0
  by_contra hχ
  have ha₂ : (qExpansion 1 f.toCuspForm).coeff (p ^ 2) = 0 :=
    (mul_left_eq_self₀.mp h₂.symm).resolve_left hχ
  have ha₁ : (qExpansion 1 f.toCuspForm).coeff p = 0 :=
    (mul_left_eq_self₀.mp h₁.symm).resolve_left fun h ↦ hχ (by rw [h, one_pow])
  rw [ha₂, ha₁, mul_zero, zero_sub, zero_eq_neg] at h₃
  exact mul_ne_zero (Units.ne_zero _) (zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne_zero)) h₃

/-- **A newform that is its own twist by `χ` has `χ` quadratic**: if `f ⊗ χ = f`, i.e.
`aₙ(f) = χ(n) aₙ(f)` for all `n` coprime to the level of `f` and the modulus of `χ`, then
`χ² = 1`. -/
lemma IsTwistBy.isQuadratic (hf : f.IsTwistBy χ f) : χ.IsQuadratic := by
  have : NeZero M := ⟨hf.1⟩
  refine MulChar.isQuadratic_iff_sq_eq_one.mpr (MulChar.ext fun u ↦ ?_)
  rcases Nat.forall_exists_prime_gt_and_eq_mod u.isUnit (N * M) with ⟨p, hpNM, hp, hpu⟩
  rw [MulChar.one_apply_coe, MulChar.pow_apply' _ two_ne_zero, ← hpu]
  exact hf.apply_sq_eq_one hp (Nat.coprime_of_lt_prime (mul_ne_zero (NeZero.ne N) hf.1) hpNM hp)

/-- **A self twist character is quadratic**, if **strong multiplicity one** holds for `f`: here
the hypothesis `hsmo` that every newform of weight `k`, of any level, whose coefficients `a_p` agree
with those of `f` at almost all primes `p` has the `q`-expansion of `f`. The twist `f ⊗ χ` then
has the `q`-expansion of `f`, and `IsTwistBy.isQuadratic` applies. -/
lemma HasSelfTwist.isQuadratic (hf : f.HasSelfTwist χ) (hsmo : ∀ (N' : ℕ+) (g : Newform N' k),
    (∀ᶠ p in Filter.cofinite, p.Prime → (qExpansion 1 g.toCuspForm).coeff p =
      (qExpansion 1 f.toCuspForm).coeff p) →
      qExpansion 1 g.toCuspForm = qExpansion 1 f.toCuspForm) : χ.IsQuadratic := by
  have : NeZero M := ⟨hf.1⟩
  rcases f.exists_isTwistBy hf.2.1 with ⟨N', g, -, hg⟩
  have hfg : qExpansion 1 g.toCuspForm = qExpansion 1 f.toCuspForm := hsmo N' g <| by
    filter_upwards [hg.isTwistAtAlmostAllPrimes, hf.2.2] with p hgp hfp hp
    rw [hgp hp, ← hfp hp]
  exact IsTwistBy.isQuadratic ⟨hf.1, hf.2.1, fun n hn ↦ hfg ▸ hg.2.2 n hn⟩

/-- **A self twist by the Kronecker character of a quadratic field gives complex or real
multiplication by that field**: for a fundamental discriminant `D ≠ 1`, a self twist by `(D/·)`
means complex multiplication by `ℚ(√D)` if `D < 0` and real multiplication if `D > 1`. -/
lemma HasSelfTwist.hasCMBy_or_hasRMBy {D : ℤ} (hD : D.IsFundamentalDiscr)
    (hf : f.HasSelfTwist hD.kroneckerChar) (hD1 : D ≠ 1) : f.HasCMBy D ∨ f.HasRMBy D := by
  rcases lt_or_gt_of_ne hD.ne_zero with hD0 | hD0
  · exact Or.inl ⟨hD, hD0, hf⟩
  · exact Or.inr ⟨hD, by omega, hf⟩

lemma HasSelfTwist.exists_kroneckerChar_of_isQuadratic (hf : f.HasSelfTwist χ) (hq : χ.IsQuadratic)
    (hχ : χ ≠ 1) : ∃ (D : ℤ) (hD : D.IsFundamentalDiscr),
      (⟨⟨M, Nat.pos_of_ne_zero hf.1⟩, χ⟩ : Σ M : ℕ+, DirichletCharacter ℂ M) =
        ⟨⟨D.natAbs, Int.natAbs_pos.mpr hD.ne_zero⟩, hD.kroneckerChar⟩ ∧
      (f.HasCMBy D ∨ f.HasRMBy D) := by
  have : NeZero M := ⟨hf.1⟩
  rcases hf.2.1.exists_eq_ringHomComp_fundamentalDiscriminantChar hq with ⟨D, hD, h⟩
  have hfD : f.HasSelfTwist hD.kroneckerChar :=
    (congrArg (fun x : Σ M : ℕ+, DirichletCharacter ℂ M ↦ f.HasSelfTwist x.2) h).mp hf
  refine ⟨D, hD, h, hfD.hasCMBy_or_hasRMBy hD fun hD1 ↦ hχ ?_⟩
  have hM : M = D.natAbs := congrArg (fun x : Σ M : ℕ+, DirichletCharacter ℂ M ↦ (x.1 : ℕ)) h
  exact DirichletCharacter.eq_one_iff_conductor_eq_one.mpr <| hf.2.1.trans <| hM.trans <| by
    rw [hD1, Int.natAbs_one]

/-- **A nontrivial character `χ` with `f ⊗ χ = f` is the Kronecker character of a quadratic
field**, by which `f` has complex or real multiplication (LMFDB `cmf.self_twist_field`): there is a
fundamental discriminant `D` with `χ = (D/·)` (of modulus `|D|`), and `f` has complex
multiplication by `ℚ(√D)` (`D < 0`) or real multiplication by it (`D > 1`). -/
lemma IsTwistBy.exists_kroneckerChar (hf : f.IsTwistBy χ f) (hχ : χ ≠ 1) :
    ∃ (D : ℤ) (hD : D.IsFundamentalDiscr),
      (⟨⟨M, Nat.pos_of_ne_zero hf.1⟩, χ⟩ : Σ M : ℕ+, DirichletCharacter ℂ M) =
        ⟨⟨D.natAbs, Int.natAbs_pos.mpr hD.ne_zero⟩, hD.kroneckerChar⟩ ∧
      (f.HasCMBy D ∨ f.HasRMBy D) :=
  HasSelfTwist.exists_kroneckerChar_of_isQuadratic ⟨hf.1, hf.2.1, hf.isTwistAtAlmostAllPrimes⟩
    hf.isQuadratic hχ

/-- **A nontrivial self twist character is the Kronecker character of a quadratic field**, by which
`f` has complex or real multiplication (LMFDB `cmf.self_twist_field`), if **strong multiplicity
one** holds for `f` (the hypothesis `hsmo` of `HasSelfTwist.isQuadratic`). -/
lemma HasSelfTwist.exists_kroneckerChar (hf : f.HasSelfTwist χ) (hχ : χ ≠ 1)
    (hsmo : ∀ (N' : ℕ+) (g : Newform N' k), (∀ᶠ p in Filter.cofinite, p.Prime →
      (qExpansion 1 g.toCuspForm).coeff p = (qExpansion 1 f.toCuspForm).coeff p) →
      qExpansion 1 g.toCuspForm = qExpansion 1 f.toCuspForm) :
    ∃ (D : ℤ) (hD : D.IsFundamentalDiscr),
      (⟨⟨M, Nat.pos_of_ne_zero hf.1⟩, χ⟩ : Σ M : ℕ+, DirichletCharacter ℂ M) =
        ⟨⟨D.natAbs, Int.natAbs_pos.mpr hD.ne_zero⟩, hD.kroneckerChar⟩ ∧
      (f.HasCMBy D ∨ f.HasRMBy D) :=
  hf.exists_kroneckerChar_of_isQuadratic (hf.isQuadratic hsmo) hχ

end HeckeRing.GL2.Newform
