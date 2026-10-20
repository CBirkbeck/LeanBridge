import TauCeti.NumberTheory.ModularForms.Newforms.Coefficient
import TauCeti.NumberTheory.ModularForms.Newforms.Twist

/-!
# Twists of newforms

For a newform `f = ∑ aₙ qⁿ` of level `N` and a primitive Dirichlet character `ψ`, the *twist*
`f ⊗ ψ` (LMFDB `cmf.twist`) is the newform `g` with `aₙ(g) = ψ(n) aₙ(f)` for all `n ≥ 1` coprime
to `N` and to the conductor of `ψ`, which the LMFDB asserts to exist and to be unique. The newforms
`f` and `g` are then *twist equivalent*, an equivalence relation whose classes are the *twist
classes*.

The newforms are Tau Ceti's `HeckeRing.GL2.Newform`, of level `Γ₁(N)` with a nebentypus. Tau Ceti
twists cusp forms coefficientwise (`CuspForm.twist`), into level `M · lcm(N, M)` for a character
of modulus `M`, and attaches to the twist of a newform a newform with the same eigenvalues at the
primes not dividing that level. The Hecke recursion of the coefficients of newforms identifies it
as the twist `f ⊗ ψ` in the sense of the LMFDB, which proves that the twist exists. Its uniqueness
is strong multiplicity one across levels, which is not proved here.

Twist equivalence is defined through the condition `a_p(g) = ψ(p) a_p(f)` at all but finitely
many primes `p`, the form in which the LMFDB states self twists and inner twists, for which it is
an equivalence relation without further theory. By strong multiplicity one, `g` satisfies this
condition for a character `ψ` of positive modulus exactly when `g = f ⊗ ψ'` for the primitive
character `ψ'` inducing `ψ`, so this is the LMFDB relation, but only the direction from
`g = f ⊗ ψ'` is proved here. The relations are stated between newforms of any levels and weights.
Twist equivalent newforms have the same weight, a theorem that is not proved here, and twist
classes are taken among the newforms of a given weight.

## Main definitions

* `HeckeRing.GL2.Newform.IsTwistAtAlmostAllPrimes`: `a_p(g) = ψ(p) a_p(f)` for all but finitely
  many primes `p`.
* `HeckeRing.GL2.Newform.IsTwistBy`: the newform `g` is the twist `f ⊗ ψ` (LMFDB `cmf.twist`).
* `HeckeRing.GL2.Newform.IsTwistEquivalent`: twist equivalence of newforms (LMFDB `cmf.twist`).
* `HeckeRing.GL2.Newform.twistEquivalence`: twist equivalence, as an equivalence relation on the
  newforms of a given weight and of all levels.
* `HeckeRing.GL2.Newform.twistClass`: the twist class of a newform (LMFDB `cmf.twist`).

## Main results

* `HeckeRing.GL2.Newform.IsTwistBy.isTwistAtAlmostAllPrimes`: `f ⊗ ψ` is a twist of `f` by `ψ` at
  almost all primes.
* `HeckeRing.GL2.Newform.IsTwistBy.isTwistEquivalent`: `f` and `f ⊗ ψ` are twist equivalent.
* `HeckeRing.GL2.Newform.exists_isTwistBy`: the twist `f ⊗ ψ` exists, and its level divides
  `M · lcm(N, M)`.
* `HeckeRing.GL2.Newform.isTwistEquivalent_iff_exists_isPrimitive`: twist equivalence can be
  tested on primitive characters, as in the LMFDB.
-/

open UpperHalfPlane

namespace HeckeRing.GL2.Newform

variable {N N' N'' M M' L m n p r : ℕ} [NeZero N] [NeZero N'] [NeZero N''] {k k' k'' : ℤ}
  {f : Newform N k} {ψ : DirichletCharacter ℂ M} {ψ' : DirichletCharacter ℂ M'} {g : Newform N' k'}
  {h : Newform N'' k''} {x : Σ L : ℕ+, Newform L k} (hp : p.Prime) (hNL : N ∣ L) (hN'L : N' ∣ L)

variable (f ψ g) in
/-- The newform `g` is **a twist of `f` by `ψ` at almost all primes** if `a_p(g) = ψ(p) a_p(f)`
for all but finitely many primes `p`. This is the condition through which the LMFDB defines self
twists and inner twists (`cmf.self_twist`, `cmf.inner_twist`). For a primitive `ψ` of positive
modulus it holds exactly when `g` is the twist `f ⊗ ψ` (`IsTwistBy`), by strong multiplicity one,
but only the direction `IsTwistBy.isTwistAtAlmostAllPrimes` is proved here. -/
def IsTwistAtAlmostAllPrimes : Prop :=
  ∀ᶠ p in Filter.cofinite, p.Prime → (qExpansion 1 g.toCuspForm).coeff p = ψ p *
    (qExpansion 1 f.toCuspForm).coeff p

variable (f ψ g) in
/-- The newform `g` is **the twist** `f ⊗ ψ` of the newform `f` of level `N` by the primitive
Dirichlet character `ψ` of modulus `M` (LMFDB `cmf.twist`) if `aₙ(g) = ψ(n) aₙ(f)` for all `n`
coprime to `N` and to the conductor `M` of `ψ`. Both are cusp forms, so it is the same to ask it for
`n ≥ 1` as the LMFDB does. Dirichlet characters have positive modulus in the LMFDB, and the
modulus `M = 0`, for which Mathlib's `DirichletCharacter.IsPrimitive` always holds, is excluded.
The twist exists (`exists_isTwistBy`); that it is unique is strong multiplicity one across levels,
which is not proved here. -/
def IsTwistBy : Prop :=
  M ≠ 0 ∧ ψ.IsPrimitive ∧ ∀ n : ℕ, n.Coprime (N * M) → (qExpansion 1 g.toCuspForm).coeff n = ψ n *
    (qExpansion 1 f.toCuspForm).coeff n

variable (f g) in
/-- The newforms `f` and `g` are **twist equivalent** (LMFDB `cmf.twist`) if `g` is a twist of `f`
by a Dirichlet character `ψ` of positive modulus, in the sense that `a_p(g) = ψ(p) a_p(f)` for all
but finitely many primes `p`. The character can be taken primitive
(`isTwistEquivalent_iff_exists_isPrimitive`), and then by strong multiplicity one this holds
exactly when `g` is the twist `f ⊗ ψ` (`IsTwistBy`), which is the LMFDB definition; only the
direction `IsTwistBy.isTwistEquivalent` is proved here. -/
def IsTwistEquivalent : Prop :=
  ∃ (M : ℕ+) (ψ : DirichletCharacter ℂ M), f.IsTwistAtAlmostAllPrimes ψ g

variable (hψ : f.IsTwistAtAlmostAllPrimes ψ g) (hg : f.IsTwistBy ψ g) (hfg : f.IsTwistEquivalent g)

private lemma eventually_not_dvd (hm : m ≠ 0) : ∀ᶠ q in Filter.cofinite, ¬q ∣ m :=
  Nat.cofinite_eq_atTop ▸ (Filter.eventually_gt_atTop m).mono fun _ ↦ Nat.not_dvd_of_pos_of_lt
    (Nat.pos_of_ne_zero hm)

variable (f) in
lemma isTwistBy_one : f.IsTwistBy (1 : DirichletCharacter ℂ 1) f :=
  ⟨one_ne_zero, DirichletCharacter.isPrimitive_one_level_one, fun _ _ ↦ by
    rw [MulChar.one_apply (isUnit_of_subsingleton _), one_mul]⟩

include hg in
/-- **The twist `f ⊗ ψ` is a twist of `f` by `ψ` at almost all primes**: `a_p(g) = ψ(p) a_p(f)` at
every prime `p` not dividing `N M`. -/
lemma IsTwistBy.isTwistAtAlmostAllPrimes : f.IsTwistAtAlmostAllPrimes ψ g :=
  (eventually_not_dvd (mul_ne_zero (NeZero.ne N) hg.1)).mono fun p hpNM hp ↦ hg.2.2 p
    (hp.coprime_iff_not_dvd.mpr hpNM)

variable (f) in
lemma isTwistAtAlmostAllPrimes_one : f.IsTwistAtAlmostAllPrimes (1 : DirichletCharacter ℂ 1) f :=
  f.isTwistBy_one.isTwistAtAlmostAllPrimes

include hg in
/-- **A newform and its twist are twist equivalent.** -/
lemma IsTwistBy.isTwistEquivalent : f.IsTwistEquivalent g :=
  ⟨⟨M, Nat.pos_of_ne_zero hg.1⟩, ψ, hg.isTwistAtAlmostAllPrimes⟩

variable (f) in
lemma IsTwistEquivalent.refl : f.IsTwistEquivalent f :=
  f.isTwistBy_one.isTwistEquivalent

private lemma mul_apply_natCast (hn : n.Coprime (M.lcm M')) : ψ.mul ψ' n = ψ n * ψ' n := by
  have hn' : IsCoprime (n : ℤ) (M.lcm M' : ℕ) := hn.isCoprime
  have h₁ : ψ.changeLevel (M.dvd_lcm_left M') (n : ℤ) = ψ (n : ℤ) :=
    ψ.changeLevel_eq_cast_of_dvd' (M.dvd_lcm_left M') hn'
  have h₂ : ψ'.changeLevel (M.dvd_lcm_right M') (n : ℤ) = ψ' (n : ℤ) :=
    ψ'.changeLevel_eq_cast_of_dvd' (M.dvd_lcm_right M') hn'
  simp only [Int.cast_natCast] at h₁ h₂
  rw [DirichletCharacter.mul, MulChar.mul_apply, h₁, h₂]

variable (f) in
private lemma qExpansion_coeff_mul_of_coprime (hm : 0 < m) (hn : 0 < n) (hmn : m.Coprime n)
    (hmN : m.Coprime N) (hnN : n.Coprime N) : (qExpansion 1 f.toCuspForm).coeff (m * n) =
    (qExpansion 1 f.toCuspForm).coeff m * (qExpansion 1 f.toCuspForm).coeff n :=
  f.toEigenformAwayFromLevel.qExpansion_coeff_mul f.isNorm (m := ⟨m, hm⟩) (n := ⟨n, hn⟩) hmn hmN hnN

variable (f) in
include hp in
private lemma qExpansion_coeff_prime_pow_add_two (hpN : p.Coprime N) : (qExpansion 1
    f.toCuspForm).coeff (p ^ (r + 2)) = (qExpansion 1 f.toCuspForm).coeff p * (qExpansion 1
    f.toCuspForm).coeff (p ^ (r + 1)) - f.dirichletLift p * (p : ℂ) ^ (k - 1) * (qExpansion 1
    f.toCuspForm).coeff (p ^ r) := by
  rw [f.dirichletLift_apply_of_coprime hpN]
  exact f.toEigenformAwayFromLevel.qExpansion_coeff_prime_pow_add_two f.isNorm (p := ⟨p, hp.pos⟩) hp
    hpN r

include hp hNL hN'L in
private lemma qExpansion_coeff_prime_pow_eq (hpL : p.Coprime L)
    (hχ : g.dirichletLift p * (p : ℂ) ^ (k' - 1) = ψ p ^ 2 * f.dirichletLift p * (p : ℂ) ^ (k - 1))
    (ha : (qExpansion 1 g.toCuspForm).coeff p = ψ p * (qExpansion 1 f.toCuspForm).coeff p) :
    (qExpansion 1 g.toCuspForm).coeff (p ^ r) = ψ p ^ r * (qExpansion 1 f.toCuspForm).coeff (p ^
    r) := by
  induction r using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using ha
  | more r ih₀ ih₁ =>
    rw [g.qExpansion_coeff_prime_pow_add_two hp (hpL.coprime_dvd_right hN'L),
      f.qExpansion_coeff_prime_pow_add_two hp (hpL.coprime_dvd_right hNL), ih₀, ih₁, ha, hχ]
    ring1

include hNL hN'L in
private lemma qExpansion_coeff_eq_of_forall_prime (hχ : ∀ p : ℕ, p.Coprime L → g.dirichletLift p *
    (p : ℂ) ^ (k' - 1) = ψ p ^ 2 * f.dirichletLift p * (p : ℂ) ^ (k - 1)) (ha : ∀ p : ℕ, p.Prime →
    p.Coprime L → (qExpansion 1 g.toCuspForm).coeff p = ψ p * (qExpansion 1 f.toCuspForm).coeff p)
    (hn : n.Coprime L) :
    (qExpansion 1 g.toCuspForm).coeff n = ψ n * (qExpansion 1 f.toCuspForm).coeff n := by
  induction n using Nat.recOnPrimePow with
  | zero =>
    rw [CuspFormClass.qExpansion_coeff_zero g.toCuspForm one_pos
      (TauCeti.one_mem_strictPeriods_Gamma1_map N'), CuspFormClass.qExpansion_coeff_zero
      f.toCuspForm one_pos (TauCeti.one_mem_strictPeriods_Gamma1_map N), mul_zero]
  | one => simp
  | prime_pow_mul a p r hp hpa hr ih =>
    have hpL : p.Coprime L := hn.coprime_dvd_left ((dvd_pow_self p hr.ne').mul_right a)
    have haL : a.Coprime L := hn.coprime_dvd_left (dvd_mul_left a _)
    have ha0 : 0 < a := Nat.pos_of_ne_zero fun ha0 ↦ hpa (ha0 ▸ dvd_zero p)
    have hpa' : (p ^ r).Coprime a := (hp.coprime_iff_not_dvd.mpr hpa).pow_left r
    rw [g.qExpansion_coeff_mul_of_coprime (pow_pos hp.pos r) ha0 hpa'
        ((hpL.pow_left r).coprime_dvd_right hN'L) (haL.coprime_dvd_right hN'L),
      f.qExpansion_coeff_mul_of_coprime (pow_pos hp.pos r) ha0 hpa'
        ((hpL.pow_left r).coprime_dvd_right hNL) (haL.coprime_dvd_right hNL),
      qExpansion_coeff_prime_pow_eq hp hNL hN'L hpL (hχ p hpL) (ha p hp hpL), ih haL, Nat.cast_mul,
      Nat.cast_pow, map_mul, map_pow]
    ring1

variable [NeZero M]

include hψ in
lemma IsTwistAtAlmostAllPrimes.symm : g.IsTwistAtAlmostAllPrimes ψ⁻¹ f := by
  filter_upwards [hψ, eventually_not_dvd (NeZero.ne M)] with p hψp hpM hp
  rw [hψp hp, ← mul_assoc, ← MulChar.mul_apply, MulChar.inv_mul, MulChar.one_apply <|
    (ZMod.isUnit_iff_coprime p M).mpr <| hp.coprime_iff_not_dvd.mpr hpM, one_mul]

include hψ in
lemma IsTwistAtAlmostAllPrimes.trans [NeZero M'] (hgh : g.IsTwistAtAlmostAllPrimes ψ' h) :
    f.IsTwistAtAlmostAllPrimes (ψ.mul ψ') h := by
  filter_upwards [hψ, hgh, eventually_not_dvd (Nat.lcm_ne_zero (NeZero.ne M) (NeZero.ne M'))]
    with p hψp hghp hpM hp
  rw [hghp hp, hψp hp, mul_apply_natCast (hp.coprime_iff_not_dvd.mpr hpM)]
  ring1

include hψ in
lemma IsTwistAtAlmostAllPrimes.primitiveCharacter :
    f.IsTwistAtAlmostAllPrimes ψ.primitiveCharacter g := by
  filter_upwards [hψ, eventually_not_dvd (NeZero.ne M)] with p hψp hpM hp
  have hpc : ψ.primitiveCharacter (p : ℤ) = ψ (p : ℤ) :=
    ψ.primitiveCharacter_apply_of_isCoprime (hp.coprime_iff_not_dvd.mpr hpM).isCoprime
  simp only [Int.cast_natCast] at hpc
  rw [hψp hp, hpc]

variable (f) in
/-- **The twist exists**: for a newform `f` of level `N` and a primitive Dirichlet character `ψ` of
modulus `M ≠ 0`, there is a newform `g = f ⊗ ψ` of level dividing `M · lcm(N, M)` with
`aₙ(g) = ψ(n) aₙ(f)` for all `n` coprime to `N M`. Tau Ceti's
`exists_newform_qExpansion_coeff_prime_eq_twist` gives a newform of such a level with
`a_p(g) = ψ(p) a_p(f)` and nebentypus `χψ²` at the primes not dividing the level, and the Hecke
recursion of the coefficients of newforms at the good primes extends the equality to all `n`. -/
lemma exists_isTwistBy (hprim : ψ.IsPrimitive) :
    ∃ (N' : ℕ+) (g : Newform N' k), (N' : ℕ) ∣ M * N.lcm M ∧ f.IsTwistBy ψ g := by
  have hNM : N * M ∣ M * N.lcm M := mul_comm N M ▸ mul_dvd_mul_left M (N.dvd_lcm_left M)
  have hMM : M * M ∣ M * N.lcm M := mul_dvd_mul_left M (N.dvd_lcm_right M)
  have : NeZero (M * N.lcm M) :=
    ⟨mul_ne_zero (NeZero.ne M) (Nat.lcm_ne_zero (NeZero.ne N) (NeZero.ne M))⟩
  rcases f.exists_newform_qExpansion_coeff_prime_eq_twist ψ hNM hMM with ⟨R, _, hR, g, hχ, ha⟩
  refine ⟨⟨R, NeZero.pos R⟩, g, hR, NeZero.ne M, hprim, fun n hn ↦ ?_⟩
  refine (qExpansion_coeff_eq_of_forall_prime (dvd_of_mul_right_dvd hNM) hR (fun p hpL ↦ ?_) ha
    ((hn.coprime_dvd_right (dvd_mul_left M N)).mul_right
      (hn.coprime_dvd_right (N.lcm_dvd_mul M))) :)
  rw [g.dirichletLift_apply_of_coprime (hpL.coprime_dvd_right hR),
    f.dirichletLift_apply_of_coprime (hpL.coprime_dvd_right (dvd_of_mul_right_dvd hNM))]
  simpa [mul_comm] using
    congrArg (fun χ ↦ (χ (ZMod.unitOfCoprime p hpL) : ℂ) * (p : ℂ) ^ (k - 1)) hχ

include hfg in
lemma IsTwistEquivalent.symm : g.IsTwistEquivalent f :=
  hfg.elim fun M ⟨ψ, hψ⟩ ↦ ⟨M, ψ⁻¹, hψ.symm⟩

include hfg in
lemma IsTwistEquivalent.trans (hgh : g.IsTwistEquivalent h) : f.IsTwistEquivalent h :=
  hfg.elim fun M ⟨ψ, hψ⟩ ↦ hgh.elim fun M' ⟨ψ', hψ'⟩ ↦ ⟨M.lcm M', ψ.mul ψ', hψ.trans hψ'⟩

lemma isTwistEquivalent_comm : f.IsTwistEquivalent g ↔ g.IsTwistEquivalent f :=
  ⟨.symm, .symm⟩

/-- **Twist equivalence through primitive characters**: `f` and `g` are twist equivalent exactly
when `g` is a twist of `f` at almost all primes by a primitive character, as in the LMFDB
definition, since a character and the primitive character inducing it agree at the primes not
dividing its modulus. -/
lemma isTwistEquivalent_iff_exists_isPrimitive : f.IsTwistEquivalent g ↔ ∃ (M : ℕ+) (ψ :
    DirichletCharacter ℂ M), ψ.IsPrimitive ∧ f.IsTwistAtAlmostAllPrimes ψ g :=
  ⟨fun ⟨_, ψ, hψ⟩ ↦ ⟨⟨ψ.conductor, Nat.pos_of_ne_zero ψ.conductor_ne_zero⟩, ψ.primitiveCharacter,
    ψ.primitiveCharacter_isPrimitive, hψ.primitiveCharacter⟩, fun ⟨M, ψ, _, hψ⟩ ↦ ⟨M, ψ, hψ⟩⟩

variable (k) in
/-- **Twist equivalence** (LMFDB `cmf.twist`), as an equivalence relation on the newforms of weight
`k` and of all levels. Its classes are the twist classes (`twistClass`). -/
def twistEquivalence : Setoid (Σ L : ℕ+, Newform L k) where
  r x y := x.2.IsTwistEquivalent y.2
  iseqv := ⟨fun x ↦ .refl x.2, .symm, .trans⟩

variable (f) in
/-- The **twist class** of a newform `f` of weight `k` (LMFDB `cmf.twist`): the set of newforms of
weight `k`, of all levels, that are twist equivalent to `f`. Twist equivalent newforms have the
same weight, a theorem that is not proved here, so this is the LMFDB twist class. -/
def twistClass : Set (Σ L : ℕ+, Newform L k) :=
  {x | f.IsTwistEquivalent x.2}

lemma mem_twistClass : x ∈ f.twistClass ↔ f.IsTwistEquivalent x.2 :=
  Iff.rfl

variable (f) in
lemma self_mem_twistClass : ⟨⟨N, NeZero.pos N⟩, f⟩ ∈ f.twistClass :=
  IsTwistEquivalent.refl f

lemma twistClass_eq_iff : f.twistClass = x.2.twistClass ↔ x ∈ f.twistClass :=
  ⟨fun hfx ↦ hfx ▸ IsTwistEquivalent.refl x.2, fun (hfx : f.IsTwistEquivalent x.2) ↦ Set.ext fun _ ↦
    ⟨hfx.symm.trans, hfx.trans⟩⟩

end HeckeRing.GL2.Newform
