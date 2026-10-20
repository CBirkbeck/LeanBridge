import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.GaloisOrbit
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.SelfTwist
import TauCeti.NumberTheory.MulChar.GaloisOrbit

/-!
# Inner twists of newforms

Galois conjugate newforms `f` and `g` are *inner twists* (LMFDB `cmf.inner_twist`) if there is a
Dirichlet character `χ` with `a_p(g) = χ(p) a_p(f)` for all but finitely many primes `p`; the
character can be taken primitive, and `f` then *admits an inner twist* by `χ`. By a theorem of
Ribet, `g = σ(f)` for an automorphism `σ` of the coefficient field of `f`, and the pairs `(χ, σ)`
form the group of inner twists of `f`, whose order is the *inner twist count* of `f` (LMFDB
`cmf.inner_twist_count`). The pair `(1, 1)` is the self twist by the trivial character, and the
other inner twists are *nontrivial* (LMFDB `cmf.nontrivial_twist`). The number of characters `χ`
in a Galois orbit of Dirichlet characters by which `f` admits an inner twist is the *inner twist
multiplicity* (LMFDB `cmf.inner_twist_multiplicity`).

The newforms are Tau Ceti's `HeckeRing.GL2.Newform`, and Galois conjugacy is
`HeckeRing.GL2.Newform.IsGaloisConjugate`, through automorphisms of `ℂ`. Galois conjugate newforms
have the same level and weight, which is not proved here, and the Galois conjugates of `f` are
taken in its Galois orbit, among the newforms of its level and weight. An inner twist of `f` is
recorded here as the pair `(χ, g)` of the primitive character `χ` and the Galois conjugate `g` of
`f`, rather than as the pair `(χ, σ)`. The newform `g` corresponds to `σ` through the embedding of
the coefficient field of `f` that it defines, and the two descriptions agree by Ribet's theorem,
which is not proved here. Nor is it proved here that `χ` determines the inner twist, or that there
are finitely many inner twists (`Set.ncard` is `0` on an infinite set).

The LMFDB states that the inner twist count and the inner twist multiplicities are invariants of the
Galois orbit of `f`. This is proved here under the assumption that the Galois conjugates `σ(f)` of
`f` are newforms, which is a theorem that is not proved here (it is the same assumption as in
`HeckeRing.GL2.Newform.ncard_galoisOrbit_eq`).

Galois orbits of Dirichlet characters are Tau Ceti's `MulChar.galoisOrbit`, the characters
generating the same cyclic group as `χ`. They are the conjugates `σ ∘ χ` under the embeddings `σ` of
the field of values of `χ` (`MulChar.mem_galoisOrbit_iff_exists_algHom`), i.e. the LMFDB orbits
(LMFDB `character.dirichlet.galois_orbit`).

## Main definitions

* `HeckeRing.GL2.Newform.IsInnerTwist`: the newforms `f` and `g` are inner twists
  (LMFDB `cmf.inner_twist`).
* `HeckeRing.GL2.Newform.HasInnerTwist`: `f` admits an inner twist by the primitive character `χ`
  (LMFDB `cmf.inner_twist`).
* `HeckeRing.GL2.Newform.innerTwists`: the set of inner twists of `f` (LMFDB `cmf.inner_twist`).
* `HeckeRing.GL2.Newform.innerTwistCount`: the number of inner twists of `f`
  (LMFDB `cmf.inner_twist_count`).
* `HeckeRing.GL2.Newform.nontrivialInnerTwists`: the nontrivial inner twists of `f`
  (LMFDB `cmf.nontrivial_twist`).
* `HeckeRing.GL2.Newform.innerTwistMultiplicity`: the number of characters in the Galois orbit of
  `χ` by which `f` admits an inner twist (LMFDB `cmf.inner_twist_multiplicity`).

## Main results

* `HeckeRing.GL2.Newform.mk_self_mem_innerTwists_iff`: the inner twists `(χ, f)` are the self
  twists of `f`.
* `HeckeRing.GL2.Newform.ncard_nontrivialInnerTwists`: there is one nontrivial inner twist fewer
  than inner twists.
* `HeckeRing.GL2.Newform.mk_ringHomComp_mem_innerTwists`: `(σ ∘ χ, σ(g))` is an inner twist of
  `σ(f)` when `(χ, g)` is an inner twist of `f`.
* `HeckeRing.GL2.Newform.IsGaloisConjugateBy.innerTwistCount_eq`,
  `HeckeRing.GL2.Newform.IsGaloisConjugateBy.innerTwistMultiplicity_eq`: the inner twist count and
  the inner twist multiplicities are invariants of the Galois orbit, if the Galois conjugates of
  `f` are newforms.
-/

open UpperHalfPlane

namespace MulChar

variable {M : Type*} [CommMonoid M] {χ φ : MulChar M ℂ} (σ : Gal(ℂ/ℚ))

lemma ringHomComp_inv_ringHomComp :
    (φ.ringHomComp ((σ⁻¹ : Gal(ℂ/ℚ)) : ℂ →+* ℂ)).ringHomComp (σ : ℂ →+* ℂ) = φ :=
  ext fun a ↦ σ.apply_symm_apply (φ a)

variable [Finite Mˣ]

lemma ringHomComp_mem_galoisOrbit_of_mem (hφ : φ ∈ χ.galoisOrbit) :
    φ.ringHomComp σ ∈ χ.galoisOrbit :=
  galoisOrbit_eq_galoisOrbit_iff.mpr hφ ▸ φ.ringHomComp_mem_galoisOrbit (RingHom.injective _)

lemma ncard_galoisOrbit_inter_eq {P Q : MulChar M ℂ → Prop} (hPQ : ∀ φ, P φ → Q (φ.ringHomComp σ))
    (hQP : ∀ φ, Q φ → P (φ.ringHomComp (σ⁻¹ : Gal(ℂ/ℚ)))) :
    (χ.galoisOrbit ∩ {φ | Q φ}).ncard = (χ.galoisOrbit ∩ {φ | P φ}).ncard := by
  rw [← Set.ncard_image_of_injective (χ.galoisOrbit ∩ {φ | P φ})
    (injective_ringHomComp (RingHom.injective (σ : ℂ →+* ℂ)))]
  refine congrArg Set.ncard (Set.ext fun φ ↦ ⟨fun ⟨hφ, hQφ⟩ ↦ ⟨φ.ringHomComp (σ⁻¹ : Gal(ℂ/ℚ)),
    ⟨ringHomComp_mem_galoisOrbit_of_mem _ hφ, hQP φ hQφ⟩, ringHomComp_inv_ringHomComp σ⟩, ?_⟩)
  rintro ⟨φ, ⟨hφ, hPφ⟩, rfl⟩
  exact ⟨ringHomComp_mem_galoisOrbit_of_mem σ hφ, hPQ φ hPφ⟩

end MulChar

namespace HeckeRing.GL2.Newform

variable {N N' N'' M : ℕ} [NeZero N] [NeZero N'] [NeZero N''] {k k' k'' : ℤ} {f : Newform N k}
  {χ φ : DirichletCharacter ℂ M} {g : Newform N' k'} {h : Newform N'' k''} {f₁ g₀ g₁ : Newform N k}
  {σ : Gal(ℂ/ℚ)} {x : Σ M : ℕ+, DirichletCharacter ℂ M} (hσ : f.IsGaloisConjugateBy σ f₁)
  (hg₀ : g₀ ∈ f.galoisOrbit) (hnew : ∀ τ : Gal(ℂ/ℚ), ∃ g : Newform N k, f.IsGaloisConjugateBy τ g)

variable (f g) in
/-- The Galois conjugate newforms `f` and `g` are **inner twists** (LMFDB `cmf.inner_twist`) if
there is a Dirichlet character `χ` with `a_p(g) = χ(p) a_p(f)` for all but finitely many primes `p`,
i.e. if they are Galois conjugate and twist equivalent. -/
def IsInnerTwist : Prop :=
  f.IsGaloisConjugate g ∧ f.IsTwistEquivalent g

variable (f χ) in
/-- The newform `f` **admits an inner twist** by the primitive Dirichlet character `χ` (LMFDB
`cmf.inner_twist`) if `a_p(g) = χ(p) a_p(f)` for all but finitely many primes `p`, for some newform
`g` Galois conjugate to `f`. Galois conjugate newforms have the same level and weight, a theorem
that is not proved here, so `g` is taken in the Galois orbit of `f`
(`HeckeRing.GL2.Newform.galoisOrbit`), among the newforms of the level and weight of `f`.
Dirichlet characters have positive modulus in the LMFDB, and the modulus `M = 0` is excluded. -/
def HasInnerTwist : Prop :=
  M ≠ 0 ∧ χ.IsPrimitive ∧ ∃ g ∈ f.galoisOrbit, f.IsTwistAtAlmostAllPrimes χ g

variable (hfg : f.IsInnerTwist g) (hf : f.HasInnerTwist χ)

variable (f) in
lemma IsInnerTwist.refl : f.IsInnerTwist f :=
  ⟨.refl f, .refl f⟩

include hfg in
lemma IsInnerTwist.symm : g.IsInnerTwist f :=
  ⟨hfg.1.symm, hfg.2.symm⟩

include hfg in
lemma IsInnerTwist.trans (hgh : g.IsInnerTwist h) : f.IsInnerTwist h :=
  ⟨hfg.1.trans hgh.1, hfg.2.trans hgh.2⟩

lemma HasSelfTwist.hasInnerTwist (hχ : f.HasSelfTwist χ) : f.HasInnerTwist χ :=
  ⟨hχ.1, hχ.2.1, f, f.self_mem_galoisOrbit, hχ.2.2⟩

include hf in
lemma HasInnerTwist.exists_isInnerTwist : ∃ g ∈ f.galoisOrbit, f.IsInnerTwist g :=
  hf.2.2.elim fun g ⟨hg, hχ⟩ ↦ ⟨g, hg, hg, ⟨M, Nat.pos_of_ne_zero hf.1⟩, χ, hχ⟩

variable (f) in
/-- The set of **inner twists** of the newform `f` (LMFDB `cmf.inner_twist`): the pairs `(χ, g)` of
a primitive Dirichlet character `χ`, of positive modulus, and a newform `g` in the Galois orbit of
`f` with `a_p(g) = χ(p) a_p(f)` for all but finitely many primes `p`. The LMFDB records the inner
twist as the pair `(χ, σ)` with `g = σ(f)` for an automorphism `σ` of the coefficient field of `f`,
which exists by a theorem of Ribet that is not proved here; `g` and `σ` determine each other. -/
def innerTwists : Set ((Σ M : ℕ+, DirichletCharacter ℂ M) × Newform N k) :=
  {x | x.1.2.IsPrimitive ∧ x.2 ∈ f.galoisOrbit ∧ f.IsTwistAtAlmostAllPrimes x.1.2 x.2}

lemma hasInnerTwist_iff_exists_mem_innerTwists :
    f.HasInnerTwist x.2 ↔ ∃ g, (x, g) ∈ f.innerTwists :=
  ⟨fun ⟨_, hx, g, hg, hfg⟩ ↦ ⟨g, hx, hg, hfg⟩, fun ⟨g, hx, hg, hfg⟩ ↦ ⟨x.1.ne_zero, hx, g, hg, hfg⟩⟩

/-- **The inner twists `(χ, f)` are the self twists of `f`**: the inner twists with `σ = 1`, i.e.
`g = f`, are the self twists. -/
lemma mk_self_mem_innerTwists_iff : (x, f) ∈ f.innerTwists ↔ f.HasSelfTwist x.2 :=
  ⟨fun ⟨hx, _, hf⟩ ↦ ⟨x.1.ne_zero, hx, hf⟩, fun ⟨_, hx, hf⟩ ↦ ⟨hx, f.self_mem_galoisOrbit, hf⟩⟩

variable (f) in
lemma one_mem_innerTwists : (⟨1, 1⟩, f) ∈ f.innerTwists :=
  mk_self_mem_innerTwists_iff.mpr f.hasSelfTwist_one

variable (f) in
/-- The **inner twist count** of the newform `f` (LMFDB `cmf.inner_twist_count`): the number of its
inner twists, including the self twists and the trivial self twist by the trivial character. That
there are finitely many inner twists is a theorem of Ribet that is not proved here; `Set.ncard`
is `0` on an infinite set. It is an invariant of the Galois orbit of `f` if the Galois conjugates of
`f` are newforms (`IsGaloisConjugateBy.innerTwistCount_eq`). -/
noncomputable def innerTwistCount : ℕ :=
  f.innerTwists.ncard

variable (f) in
/-- The **nontrivial inner twists** of the newform `f` (LMFDB `cmf.nontrivial_twist`): its inner
twists other than the self twist by the trivial character. -/
noncomputable def nontrivialInnerTwists : Set ((Σ M : ℕ+, DirichletCharacter ℂ M) × Newform N k) :=
  f.innerTwists \ {(⟨1, 1⟩, f)}

lemma innerTwistCount_pos (hfin : f.innerTwists.Finite) : 0 < f.innerTwistCount :=
  (Set.ncard_pos hfin).mpr ⟨_, f.one_mem_innerTwists⟩

variable (f) in
/-- **The number of nontrivial inner twists** is one less than the inner twist count. -/
lemma ncard_nontrivialInnerTwists : f.nontrivialInnerTwists.ncard = f.innerTwistCount - 1 :=
  Set.ncard_sdiff_singleton_of_mem f.one_mem_innerTwists

variable (f χ) in
/-- The **inner twist multiplicity** (LMFDB `cmf.inner_twist_multiplicity`) of the newform `f` for
the Galois orbit `[χ]` of the Dirichlet character `χ` (Tau Ceti's `MulChar.galoisOrbit`): the
number of characters in `[χ]` by which `f` admits an inner twist. The LMFDB states that it does not
depend on the embedding of `f`, i.e. on `f` in its Galois orbit, which is proved here if the Galois
conjugates of `f` are newforms (`IsGaloisConjugateBy.innerTwistMultiplicity_eq`). -/
noncomputable def innerTwistMultiplicity : ℕ :=
  (χ.galoisOrbit ∩ {φ | f.HasInnerTwist φ}).ncard

include hf in
lemma innerTwistMultiplicity_pos : 0 < f.innerTwistMultiplicity χ :=
  (Set.ncard_pos (χ.finite_galoisOrbit.inter_of_left _)).mpr ⟨χ, χ.mem_galoisOrbit_self, hf⟩

lemma innerTwistMultiplicity_eq_of_mem_galoisOrbit (hφ : φ ∈ χ.galoisOrbit) :
    f.innerTwistMultiplicity φ = f.innerTwistMultiplicity χ := by
  rw [innerTwistMultiplicity, innerTwistMultiplicity, MulChar.galoisOrbit_eq_galoisOrbit_iff.mpr hφ]

include hσ in
/-- **Inner twists are Galois equivariant**: if `(χ, g)` is an inner twist of `f`, then
`(σ ∘ χ, σ(g))` is an inner twist of `σ(f)`. -/
lemma mk_ringHomComp_mem_innerTwists (hg : g₀.IsGaloisConjugateBy σ g₁)
    (hx : (x, g₀) ∈ f.innerTwists) : (⟨x.1, x.2.ringHomComp σ⟩, g₁) ∈ f₁.innerTwists :=
  ⟨hx.1.ringHomComp _ (RingHom.injective (σ : ℂ →+* ℂ)), hσ.isGaloisConjugate.symm.trans
    (hx.2.1.trans hg.isGaloisConjugate), hx.2.2.map hσ hg⟩

private lemma eq_of_mk_ringHomComp_eq {y : Σ M : ℕ+, DirichletCharacter ℂ M} (hxy : (⟨x.1,
    x.2.ringHomComp σ⟩ : Σ M : ℕ+, DirichletCharacter ℂ M) = ⟨y.1, y.2.ringHomComp σ⟩) : x = y := by
  rcases x with ⟨M, χ⟩
  rcases y with ⟨M', χ'⟩
  rcases Sigma.ext_iff.mp hxy with ⟨rfl, hχ⟩
  exact congrArg _ (MulChar.injective_ringHomComp (RingHom.injective _) (eq_of_heq hχ))

include hg₀ hnew in
lemma exists_isGaloisConjugateBy_of_mem_galoisOrbit (τ : Gal(ℂ/ℚ)) :
    ∃ g₁ : Newform N k, g₀.IsGaloisConjugateBy τ g₁ := by
  rcases hg₀ with ⟨ρ, hρ⟩
  rcases hnew (τ * ρ) with ⟨g₁, hg₁⟩
  exact ⟨g₁, mul_inv_cancel_right τ ρ ▸ hρ.symm.trans hg₁⟩

include hσ hf hnew in
lemma HasInnerTwist.map : f₁.HasInnerTwist (χ.ringHomComp σ) := by
  rcases hf with ⟨hM, hχ, g, hg, hfg⟩
  rcases exists_isGaloisConjugateBy_of_mem_galoisOrbit hg hnew σ with ⟨g₁, hg₁⟩
  exact ⟨hM, hχ.ringHomComp _ (RingHom.injective (σ : ℂ →+* ℂ)), g₁, hσ.isGaloisConjugate.symm.trans
    (hg.trans hg₁.isGaloisConjugate), hfg.map hσ hg₁⟩

include hσ hnew in
/-- **The inner twist multiplicity does not depend on the embedding of `f`**: it is the same for
the Galois conjugates of `f`, provided they are newforms (a theorem that is not proved here). -/
lemma IsGaloisConjugateBy.innerTwistMultiplicity_eq :
    f₁.innerTwistMultiplicity χ = f.innerTwistMultiplicity χ :=
  MulChar.ncard_galoisOrbit_inter_eq σ (fun _ hφ ↦ hφ.map hσ hnew) fun _ hφ ↦ hφ.map hσ.symm
    (exists_isGaloisConjugateBy_of_mem_galoisOrbit hσ.isGaloisConjugate hnew)

variable (σ) in
/-- The Galois conjugate `σ(g₀)` of a newform `g₀` in the Galois orbit of `f`, a newform when the
Galois conjugates of `f` are. -/
private noncomputable def orbitConj : Newform N k :=
  (exists_isGaloisConjugateBy_of_mem_galoisOrbit hg₀ hnew σ).choose

variable (σ) in
private lemma isGaloisConjugateBy_orbitConj : g₀.IsGaloisConjugateBy σ (orbitConj σ hg₀ hnew) :=
  (exists_isGaloisConjugateBy_of_mem_galoisOrbit hg₀ hnew σ).choose_spec

include hσ hnew in
/-- **The inner twist count is an invariant of the Galois orbit**: it is the same for the Galois
conjugates of `f`, provided they are newforms (a theorem that is not proved here). The inner twists
of `σ(f)` are the `(σ ∘ χ, σ(g))` for the inner twists `(χ, g)` of `f`. -/
lemma IsGaloisConjugateBy.innerTwistCount_eq : f₁.innerTwistCount = f.innerTwistCount := by
  refine (Set.ncard_congr (fun y (hy : y ∈ f.innerTwists) ↦
      ((⟨y.1.1, y.1.2.ringHomComp σ⟩ : Σ M : ℕ+, DirichletCharacter ℂ M), orbitConj σ hy.2.1 hnew))
    (fun y hy ↦ mk_ringHomComp_mem_innerTwists hσ (isGaloisConjugateBy_orbitConj σ hy.2.1 hnew) hy)
    (fun y y' hy hy' hyy' ↦ Prod.ext (eq_of_mk_ringHomComp_eq (Prod.mk_inj.mp hyy').1)
      ((isGaloisConjugateBy_orbitConj σ hy.2.1 hnew).symm.unique
        ((Prod.mk_inj.mp hyy').2 ▸ (isGaloisConjugateBy_orbitConj σ hy'.2.1 hnew).symm)))
    fun y hy ↦ ?_).symm
  rcases exists_isGaloisConjugateBy_of_mem_galoisOrbit hy.2.1
    (exists_isGaloisConjugateBy_of_mem_galoisOrbit hσ.isGaloisConjugate hnew) σ⁻¹ with ⟨g, hg⟩
  have hy₀ : ((⟨y.1.1, y.1.2.ringHomComp (σ⁻¹ : Gal(ℂ/ℚ))⟩ : Σ M : ℕ+, DirichletCharacter ℂ M), g) ∈
      f.innerTwists :=
    mk_ringHomComp_mem_innerTwists hσ.symm hg hy
  exact ⟨_, hy₀, Prod.ext (Sigma.ext rfl (heq_of_eq (MulChar.ringHomComp_inv_ringHomComp σ)))
    ((isGaloisConjugateBy_orbitConj σ hy₀.2.1 hnew).unique (inv_inv σ ▸ hg.symm))⟩

end HeckeRing.GL2.Newform
