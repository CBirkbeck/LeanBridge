import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.GaloisConjugate
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.Basic
import TauCeti.NumberTheory.DirichletCharacter.Conductor
import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Character

/-!
# Self twists, and newforms with complex or real multiplication

A newform `f` admits a *self twist* by a primitive Dirichlet character `χ` (LMFDB
`cmf.self_twist`) if `a_p(f) = χ(p) a_p(f)` for all but finitely many primes `p`, i.e. if `f` is a
twist of itself by `χ`. Every newform admits the self twist by the trivial character. The LMFDB
records that a nontrivial `χ` is then the Kronecker character `(D/·)` of a quadratic field `K` of
discriminant `D`, and says that `f` has *complex multiplication* (CM) by `K` if `D < 0`
(LMFDB `cmf.cm_form`) and *real multiplication* (RM) by `K` if `D > 0` (LMFDB `cmf.rm_form`).

Quadratic fields are identified here by their discriminants, which are the fundamental
discriminants other than `1` (Mathlib's `Int.IsFundamentalDiscr`): the negative ones for the
imaginary quadratic fields, the positive ones for the real quadratic fields. The Kronecker
character of the quadratic field `ℚ(√D)` of discriminant `D` is the primitive quadratic character
`(D/·)` modulo `|D|`, Tau Ceti's `TauCeti.Multiquadratic.fundamentalDiscriminantChar`, taken here
with complex values.

That a nontrivial self twist is quadratic, that only newforms of weight one can have real
multiplication, and that a newform has several nontrivial self twists exactly when it has weight
one and projective image `C₂ × C₂`, are theorems resting on Galois representations, which are not
proved here.

## Main definitions

* `Int.IsFundamentalDiscr.kroneckerChar`: the Kronecker character `(D/·)` of the quadratic field
  of discriminant `D`, as a complex Dirichlet character modulo `|D|`.
* `HeckeRing.GL2.Newform.HasSelfTwist`: the newform `f` admits a self twist by `χ`
  (LMFDB `cmf.self_twist`).
* `HeckeRing.GL2.Newform.HasCMBy`, `HeckeRing.GL2.Newform.HasCM`: `f` has complex multiplication
  by the imaginary quadratic field of discriminant `D`, or by some imaginary quadratic field
  (LMFDB `cmf.cm_form`).
* `HeckeRing.GL2.Newform.HasRMBy`, `HeckeRing.GL2.Newform.HasRM`: `f` has real multiplication by
  the real quadratic field of discriminant `D`, or by some real quadratic field
  (LMFDB `cmf.rm_form`).

## Main results

* `Int.IsFundamentalDiscr.isPrimitive_kroneckerChar`: the Kronecker character is primitive.
* `HeckeRing.GL2.Newform.IsTwistAtAlmostAllPrimes.map`: `σ(g)` is a twist of `σ(f)` by `σ ∘ χ`
  when `g` is a twist of `f` by `χ`.
* `HeckeRing.GL2.Newform.IsGaloisConjugateBy.hasSelfTwist`: `σ(f)` has a self twist by `σ ∘ χ`
  when `f` has a self twist by `χ`.
* `HeckeRing.GL2.Newform.HasCM.exists_hasSelfTwist`: a newform with CM has a self twist by an odd
  quadratic character, and `HeckeRing.GL2.Newform.HasRM.exists_hasSelfTwist`: one with RM has a
  self twist by an even nontrivial quadratic character.
* `HeckeRing.GL2.Newform.IsGaloisConjugate.hasCMBy_iff`,
  `HeckeRing.GL2.Newform.IsGaloisConjugate.hasRMBy_iff`: complex and real multiplication by a given
  field are invariants of the Galois orbit.
-/

open UpperHalfPlane TauCeti.Multiquadratic

namespace DirichletCharacter

variable {R R' : Type*} [CommRing R] [CommRing R'] {n : ℕ} {χ : DirichletCharacter R n}

lemma IsPrimitive.ringHomComp (hχ : χ.IsPrimitive) (f : R →+* R') (hf : Function.Injective f) :
    IsPrimitive (χ.ringHomComp f) := by
  rcases eq_zero_or_neZero n with rfl | _
  · exact conductor_eq_zero_iff_level_eq_zero.mpr rfl
  · exact (χ.isPrimitive_ringHomComp_iff f hf).mpr hχ

end DirichletCharacter

namespace Int.IsFundamentalDiscr

variable {D : ℤ} (hD : D.IsFundamentalDiscr)

/-- The **Kronecker character** `(D/·)` of the quadratic field `ℚ(√D)` of discriminant `D`, for a
fundamental discriminant `D`: the primitive quadratic Dirichlet character modulo `|D|` with value
the Legendre symbol `(D/q)` at an odd prime `q`, Tau Ceti's `fundamentalDiscriminantChar`, with
complex values. It is the character of the quadratic field through which the LMFDB identifies
self twists (`cmf.self_twist`). For `D = 1` it is the trivial character. -/
noncomputable def kroneckerChar : DirichletCharacter ℂ D.natAbs :=
  (fundamentalDiscriminantChar D hD).ringHomComp (Int.castRingHom ℂ)

lemma kroneckerChar_apply (a : ZMod D.natAbs) :
    hD.kroneckerChar a = fundamentalDiscriminantChar D hD a :=
  rfl

/-- **The Kronecker character is primitive**: its conductor is `|D|`. -/
lemma isPrimitive_kroneckerChar : hD.kroneckerChar.IsPrimitive :=
  (isPrimitive_fundamentalDiscriminantChar hD).ringHomComp _ Int.cast_injective

lemma isQuadratic_kroneckerChar : hD.kroneckerChar.IsQuadratic :=
  (fundamentalDiscriminantChar_isQuadratic hD).comp _

lemma kroneckerChar_neg_one : hD.kroneckerChar (-1) = D.sign := by
  rw [kroneckerChar_apply, fundamentalDiscriminantChar_neg_one]

lemma odd_kroneckerChar (hD0 : D < 0) : hD.kroneckerChar.Odd := by
  rw [DirichletCharacter.Odd, kroneckerChar_neg_one, Int.sign_eq_neg_one_of_neg hD0, Int.cast_neg,
    Int.cast_one]

lemma even_kroneckerChar (hD0 : 0 < D) : hD.kroneckerChar.Even := by
  rw [DirichletCharacter.Even, kroneckerChar_neg_one, Int.sign_eq_one_of_pos hD0, Int.cast_one]

lemma kroneckerChar_ne_one (hD1 : D ≠ 1) : hD.kroneckerChar ≠ 1 := by
  have : NeZero D.natAbs := ⟨Int.natAbs_ne_zero.mpr hD.ne_zero⟩
  have hD4 : D % 4 = 0 ∨ D % 4 = 1 := hD.emod_four_eq_zero_or_one
  rw [Ne, DirichletCharacter.eq_one_iff_conductor_eq_one, hD.isPrimitive_kroneckerChar]
  omega

lemma ringHomComp_kroneckerChar (σ : ℂ →+* ℂ) : hD.kroneckerChar.ringHomComp σ = hD.kroneckerChar :=
  MulChar.ext fun _ ↦ map_intCast σ _

end Int.IsFundamentalDiscr

namespace HeckeRing.GL2.Newform

variable {N N' N₁ N₂ M : ℕ} [NeZero N] [NeZero N'] [NeZero N₁] [NeZero N₂] {k k' k₁ k₂ : ℤ}
  {f : Newform N k} {χ : DirichletCharacter ℂ M} {g : Newform N' k'} {f₁ : Newform N₁ k₁}
  {g₁ : Newform N₂ k₂} {σ : Gal(ℂ/ℚ)} {D : ℤ} (hσ : f.IsGaloisConjugateBy σ g)
  (hfg : f.IsGaloisConjugate g)

/-- **Twists are Galois equivariant**: if `g` is a twist of `f` by `χ` at almost all primes, then
`σ(g)` is a twist of `σ(f)` by `σ ∘ χ`. -/
lemma IsTwistAtAlmostAllPrimes.map (hχ : f.IsTwistAtAlmostAllPrimes χ g)
    (hf : f.IsGaloisConjugateBy σ f₁) (hg : g.IsGaloisConjugateBy σ g₁) :
    f₁.IsTwistAtAlmostAllPrimes (χ.ringHomComp σ) g₁ := by
  filter_upwards [hχ] with p hχp hp
  rw [hg.coeff, hχp hp, map_mul, hf.coeff, MulChar.ringHomComp_apply]
  rfl

variable (f χ) in
/-- The newform `f` **admits a self twist** by the primitive Dirichlet character `χ`
(LMFDB `cmf.self_twist`) if `a_p(f) = χ(p) a_p(f)` for all but finitely many primes `p`, i.e. if
`a_p(f) = 0` at almost all primes `p` with `χ(p) ≠ 1` (`hasSelfTwist_iff`). Dirichlet characters
have positive modulus in the LMFDB, and the modulus `M = 0`, for which Mathlib's
`DirichletCharacter.IsPrimitive` always holds, is excluded. -/
def HasSelfTwist : Prop :=
  M ≠ 0 ∧ χ.IsPrimitive ∧ f.IsTwistAtAlmostAllPrimes χ f

lemma hasSelfTwist_iff : f.HasSelfTwist χ ↔ M ≠ 0 ∧ χ.IsPrimitive ∧ ∀ᶠ p : ℕ in Filter.cofinite,
    p.Prime → χ p = 1 ∨ (qExpansion 1 f.toCuspForm).coeff p = 0 := by
  simp only [HasSelfTwist, IsTwistAtAlmostAllPrimes, eq_comm (a := (qExpansion 1 _).coeff _),
    mul_left_eq_self₀]

variable (f) in
lemma hasSelfTwist_one : f.HasSelfTwist (1 : DirichletCharacter ℂ 1) :=
  ⟨one_ne_zero, DirichletCharacter.isPrimitive_one_level_one, f.isTwistAtAlmostAllPrimes_one⟩

include hσ in
/-- **Self twists are Galois equivariant**: if `f` has a self twist by `χ`, then its Galois
conjugate `σ(f)` has a self twist by `σ ∘ χ`. -/
lemma IsGaloisConjugateBy.hasSelfTwist (hf : f.HasSelfTwist χ) : g.HasSelfTwist (χ.ringHomComp σ) :=
  ⟨hf.1, hf.2.1.ringHomComp _ (RingHom.injective (σ : ℂ →+* ℂ)), hf.2.2.map hσ hσ⟩

variable (f D) in
/-- The newform `f` has **complex multiplication** by the imaginary quadratic field `ℚ(√D)` of
discriminant `D` (LMFDB `cmf.cm_form`) if it admits a self twist by the Kronecker character `(D/·)`
of that field. The imaginary quadratic fields are identified with their discriminants, the
negative fundamental discriminants. -/
def HasCMBy : Prop :=
  ∃ hD : D.IsFundamentalDiscr, D < 0 ∧ f.HasSelfTwist hD.kroneckerChar

variable (f) in
/-- The newform `f` has **complex multiplication** (LMFDB `cmf.cm_form`) if it admits a self twist
by the Kronecker character of an imaginary quadratic field, i.e. if it has complex multiplication
by some imaginary quadratic field (`HasCMBy`). -/
def HasCM : Prop :=
  ∃ D : ℤ, f.HasCMBy D

variable (f D) in
/-- The newform `f` has **real multiplication** by the real quadratic field `ℚ(√D)` of
discriminant `D` (LMFDB `cmf.rm_form`) if it admits a self twist by the Kronecker character
`(D/·)` of that field. The real quadratic fields are identified with their discriminants, the
fundamental discriminants greater than `1`. Only newforms of weight one have real multiplication,
which is not proved here. -/
def HasRMBy : Prop :=
  ∃ hD : D.IsFundamentalDiscr, 1 < D ∧ f.HasSelfTwist hD.kroneckerChar

variable (f) in
/-- The newform `f` has **real multiplication** (LMFDB `cmf.rm_form`) if it admits a self twist by
the Kronecker character of a real quadratic field, i.e. if it has real multiplication by some real
quadratic field (`HasRMBy`). -/
def HasRM : Prop :=
  ∃ D : ℤ, f.HasRMBy D

/-- **A newform with complex multiplication has a self twist by an odd quadratic character**,
which is in particular nontrivial. -/
lemma HasCM.exists_hasSelfTwist (hf : f.HasCM) :
    ∃ (M : ℕ) (χ : DirichletCharacter ℂ M), f.HasSelfTwist χ ∧ χ.IsQuadratic ∧ χ.Odd :=
  hf.elim fun D ⟨hD, hD0, hχ⟩ ↦ ⟨D.natAbs, hD.kroneckerChar, hχ, hD.isQuadratic_kroneckerChar,
    hD.odd_kroneckerChar hD0⟩

/-- **A newform with real multiplication has a self twist by an even nontrivial quadratic
character.** -/
lemma HasRM.exists_hasSelfTwist (hf : f.HasRM) :
    ∃ (M : ℕ) (χ : DirichletCharacter ℂ M), f.HasSelfTwist χ ∧ χ.IsQuadratic ∧ χ.Even ∧ χ ≠ 1 :=
  hf.elim fun D ⟨hD, hD1, hχ⟩ ↦ ⟨D.natAbs, hD.kroneckerChar, hχ, hD.isQuadratic_kroneckerChar,
    hD.even_kroneckerChar (by omega), hD.kroneckerChar_ne_one hD1.ne'⟩

include hσ in
lemma IsGaloisConjugateBy.hasSelfTwist_kroneckerChar (hD : D.IsFundamentalDiscr)
    (hχ : f.HasSelfTwist hD.kroneckerChar) : g.HasSelfTwist hD.kroneckerChar :=
  hD.ringHomComp_kroneckerChar σ ▸ hσ.hasSelfTwist hχ

include hσ in
lemma IsGaloisConjugateBy.hasCMBy (hf : f.HasCMBy D) : g.HasCMBy D :=
  hf.elim fun hD ⟨hD0, hχ⟩ ↦ ⟨hD, hD0, hσ.hasSelfTwist_kroneckerChar hD hχ⟩

include hσ in
lemma IsGaloisConjugateBy.hasRMBy (hf : f.HasRMBy D) : g.HasRMBy D :=
  hf.elim fun hD ⟨hD1, hχ⟩ ↦ ⟨hD, hD1, hσ.hasSelfTwist_kroneckerChar hD hχ⟩

include hfg in
/-- **Complex multiplication by a given field is an invariant of the Galois orbit.** -/
lemma IsGaloisConjugate.hasCMBy_iff : f.HasCMBy D ↔ g.HasCMBy D :=
  hfg.elim fun _ h ↦ ⟨h.hasCMBy, h.symm.hasCMBy⟩

include hfg in
/-- **Real multiplication by a given field is an invariant of the Galois orbit.** -/
lemma IsGaloisConjugate.hasRMBy_iff : f.HasRMBy D ↔ g.HasRMBy D :=
  hfg.elim fun _ h ↦ ⟨h.hasRMBy, h.symm.hasRMBy⟩

include hfg in
lemma IsGaloisConjugate.hasCM_iff : f.HasCM ↔ g.HasCM :=
  exists_congr fun _ ↦ hfg.hasCMBy_iff

include hfg in
lemma IsGaloisConjugate.hasRM_iff : f.HasRM ↔ g.HasRM :=
  exists_congr fun _ ↦ hfg.hasRMBy_iff

end HeckeRing.GL2.Newform
