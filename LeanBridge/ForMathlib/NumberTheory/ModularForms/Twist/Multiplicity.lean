import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.InnerTwist

/-!
# Twists of newform orbits and their multiplicity

The newform orbit `[g]` is a *twist* of the newform orbit `[f]` by the Galois orbit `[ψ]` of a
primitive Dirichlet character `ψ` (LMFDB `cmf.twist`) if some `g' ∈ [g]` is the twist `f ⊗ ψ'` of
`f` by some `ψ' ∈ [ψ]`. The *multiplicity* of `[g]` as a twist of `[f]` by `[ψ]`
(LMFDB `cmf.twist_multiplicity`) is the number of characters `ψ' ∈ [ψ]` with `f ⊗ ψ' ∈ [g]`. The
*twist class* of a newform orbit (LMFDB `cmf.twist`) is its class under twist equivalence.

Newform orbits are the Galois orbits `HeckeRing.GL2.Newform.galoisOrbit`, and Galois orbits of
Dirichlet characters are Tau Ceti's `MulChar.galoisOrbit`, the characters generating the same
cyclic group as `ψ`. These are the conjugates `σ ∘ ψ` under the embeddings `σ` of the field of
values of `ψ` (`MulChar.mem_galoisOrbit_iff_exists_algHom`), i.e. the LMFDB orbits
(LMFDB `character.dirichlet.galois_orbit`).

Twists of newform orbits and their multiplicity are defined through representatives `f`, `ψ` and
`g` of the orbits, and only depend on the Galois orbits of `ψ` and of `g`. The LMFDB states that
the multiplicity does not depend on the representative `f` of `[f]` either. This rests on the
Galois conjugates of newforms being newforms, which is not proved here, and is proved under that
assumption on `g`. The twist class of a newform orbit is defined through all of its newforms; if
the Galois conjugates of newforms are newforms, it is the set of the newform orbits of the twist
class of any one of them.

The LMFDB also states that the multiplicity of an inner twist is the inner twist count. That is not
right: when `[g] = [f]`, the multiplicity is the number of inner twists of `f` by characters in
`[ψ]`, its inner twist multiplicity for `[ψ]` (LMFDB `cmf.inner_twist_multiplicity`), and the inner
twist count is the sum of these over the Galois orbits `[ψ]`. A newform with complex multiplication
and no other nontrivial inner twist has inner twist count `2`, but multiplicity `1` as a twist of
itself by the Galois orbit of the trivial character, or of its Kronecker character. It is proved
here that the multiplicity of `[f]` as a twist of itself is at most the inner twist multiplicity;
equality is strong multiplicity one across levels, which is not proved here.

## Main definitions

* `HeckeRing.GL2.Newform.IsOrbitTwistBy`: the newform orbit `[g]` is a twist of `[f]` by `[ψ]`
  (LMFDB `cmf.twist`).
* `HeckeRing.GL2.Newform.twistMultiplicity`: the multiplicity of `[g]` as a twist of `[f]` by
  `[ψ]` (LMFDB `cmf.twist_multiplicity`).
* `HeckeRing.GL2.NewformOrbit.twistClass`: the twist class of a newform orbit (LMFDB `cmf.twist`).

## Main results

* `HeckeRing.GL2.Newform.isOrbitTwistBy_iff_twistMultiplicity_pos`: `[g]` is a twist of `[f]` by
  `[ψ]` exactly when the multiplicity is positive.
* `HeckeRing.GL2.Newform.twistMultiplicity_eq_of_mem_galoisOrbit`,
  `HeckeRing.GL2.Newform.IsGaloisConjugate.twistMultiplicity_eq`: the multiplicity only depends on
  the Galois orbits of `ψ` and of `g`.
* `HeckeRing.GL2.Newform.IsTwistBy.map`: `σ(f ⊗ ψ) = σ(f) ⊗ σ(ψ)`.
* `HeckeRing.GL2.Newform.IsGaloisConjugateBy.twistMultiplicity_eq`: the multiplicity only depends
  on the Galois orbit of `f`, if the Galois conjugates of `g` are newforms.
* `HeckeRing.GL2.Newform.twistMultiplicity_self_le_innerTwistMultiplicity`: the multiplicity of
  `[f]` as a twist of itself by `[ψ]` is at most the inner twist multiplicity of `f` for `[ψ]`.
-/

namespace HeckeRing.GL2

variable {N N' M : ℕ} [NeZero N] [NeZero N'] {k k' : ℤ}

namespace Newform

variable {f f₁ : Newform N k} {ψ ψ₁ : DirichletCharacter ℂ M} {g g₁ : Newform N' k'} {σ : Gal(ℂ/ℚ)}
  (hfg : f.IsTwistBy ψ g) (hσ : f.IsGaloisConjugateBy σ f₁)
  (hnew : ∀ τ : Gal(ℂ/ℚ), ∃ h : Newform N' k', g.IsGaloisConjugateBy τ h)

variable (f ψ g) in
/-- The newform orbit `[g]` is a **twist** of the newform orbit `[f]` by the Galois orbit `[ψ]` of
the primitive Dirichlet character `ψ` (LMFDB `cmf.twist`) if some newform in the Galois orbit of
`g` is the twist `f ⊗ ψ'` of `f` by a character `ψ'` in the Galois orbit of `ψ`. This is stated for
the representative `f` of `[f]`; it does not depend on it if the Galois conjugates of `g` are
newforms, by `isOrbitTwistBy_iff_twistMultiplicity_pos` and
`IsGaloisConjugateBy.twistMultiplicity_eq`. -/
def IsOrbitTwistBy : Prop :=
  ∃ ψ' ∈ ψ.galoisOrbit, ∃ h ∈ g.galoisOrbit, f.IsTwistBy ψ' h

variable (f ψ g) in
/-- The **multiplicity** of the newform orbit `[g]` as a twist of the newform orbit `[f]` by the
Galois orbit `[ψ]` of the primitive Dirichlet character `ψ` (LMFDB `cmf.twist_multiplicity`): the
number of characters `ψ' ∈ [ψ]` for which the twist `f ⊗ ψ'` lies in the Galois orbit of `g`. This
is stated for the representative `f` of `[f]`; the LMFDB states that it does not depend on it, which
is proved here if the Galois conjugates of `g` are newforms
(`IsGaloisConjugateBy.twistMultiplicity_eq`). -/
noncomputable def twistMultiplicity : ℕ :=
  (ψ.galoisOrbit ∩ {ψ' | ∃ h ∈ g.galoisOrbit, f.IsTwistBy ψ' h}).ncard

include hfg in
lemma IsTwistBy.isOrbitTwistBy : f.IsOrbitTwistBy ψ g :=
  ⟨ψ, ψ.mem_galoisOrbit_self, g, g.self_mem_galoisOrbit, hfg⟩

/-- **A newform orbit is a twist of another exactly when the multiplicity is positive.** -/
lemma isOrbitTwistBy_iff_twistMultiplicity_pos :
    f.IsOrbitTwistBy ψ g ↔ 0 < f.twistMultiplicity ψ g :=
  (Set.ncard_pos <| ψ.finite_galoisOrbit.inter_of_left
    {ψ' | ∃ h ∈ g.galoisOrbit, f.IsTwistBy ψ' h}).symm

/-- **The multiplicity only depends on the Galois orbit of the character.** -/
lemma twistMultiplicity_eq_of_mem_galoisOrbit (hψ : ψ₁ ∈ ψ.galoisOrbit) :
    f.twistMultiplicity ψ₁ g = f.twistMultiplicity ψ g := by
  rw [twistMultiplicity, twistMultiplicity, MulChar.galoisOrbit_eq_galoisOrbit_iff.mpr hψ]

/-- **The multiplicity only depends on the Galois orbit of `g`.** -/
lemma IsGaloisConjugate.twistMultiplicity_eq (hg : g.IsGaloisConjugate g₁) :
    f.twistMultiplicity ψ g = f.twistMultiplicity ψ g₁ := by
  rw [twistMultiplicity, twistMultiplicity, galoisOrbit_eq_iff.mpr hg]

include hfg hσ in
/-- **Twists are Galois equivariant**: if `g = f ⊗ ψ`, then `σ(g) = σ(f) ⊗ (σ ∘ ψ)`. -/
lemma IsTwistBy.map (hg : g.IsGaloisConjugateBy σ g₁) : f₁.IsTwistBy (ψ.ringHomComp σ) g₁ :=
  ⟨hfg.1, hfg.2.1.ringHomComp _ (RingHom.injective (σ : ℂ →+* ℂ)), fun n hn ↦ by
    rw [hg.coeff, hfg.2.2 n hn, map_mul, hσ.coeff, MulChar.ringHomComp_apply]
    rfl⟩

include hσ hnew in
private lemma exists_isTwistBy_ringHomComp (hψ : ∃ h ∈ g.galoisOrbit, f.IsTwistBy ψ h) :
    ∃ h ∈ g.galoisOrbit, f₁.IsTwistBy (ψ.ringHomComp σ) h := by
  rcases hψ with ⟨h, hh, hfh⟩
  rcases exists_isGaloisConjugateBy_of_mem_galoisOrbit hh hnew σ with ⟨h₁, hh₁⟩
  exact ⟨h₁, hh.trans hh₁.isGaloisConjugate, hfh.map hσ hh₁⟩

include hσ hnew in
/-- **The multiplicity does not depend on the representative of `[f]`**: it is the same for the
Galois conjugates of `f`, provided the Galois conjugates of `g` are newforms (a theorem that is not
proved here). The twists of `σ(f)` in `[g]` are the `σ(f ⊗ ψ') = σ(f) ⊗ σ(ψ')`. -/
lemma IsGaloisConjugateBy.twistMultiplicity_eq :
    f₁.twistMultiplicity ψ g = f.twistMultiplicity ψ g :=
  MulChar.ncard_galoisOrbit_inter_eq σ (fun _ ↦ exists_isTwistBy_ringHomComp hσ hnew) fun _ ↦
    exists_isTwistBy_ringHomComp hσ.symm hnew

/-- **The multiplicity of `[f]` as a twist of itself is at most the inner twist multiplicity** of
`f` for `[ψ]`: the characters `ψ' ∈ [ψ]` with `f ⊗ ψ' ∈ [f]` are among those by which `f` admits
an inner twist. The LMFDB states that the multiplicity of an inner twist is the inner twist count,
which is not right: it is the inner twist multiplicity, the converse inequality being strong
multiplicity one across levels, which is not proved here. -/
lemma twistMultiplicity_self_le_innerTwistMultiplicity :
    f.twistMultiplicity ψ f ≤ f.innerTwistMultiplicity ψ :=
  Set.ncard_le_ncard (Set.inter_subset_inter_right _ fun _ ⟨h, hh, hfh⟩ ↦ ⟨hfh.1, hfh.2.1, h, hh,
    hfh.isTwistAtAlmostAllPrimes⟩) (ψ.finite_galoisOrbit.inter_of_left _)

end Newform

namespace NewformOrbit

variable (x : NewformOrbit N k)

/-- The **twist class** of a newform orbit `x` of weight `k` (LMFDB `cmf.twist`): the newform
orbits of weight `k`, of all levels, containing a newform that is twist equivalent to a newform of
`x`, i.e. the class of `x` under twist equivalence. If the Galois conjugates of newforms are
newforms, which is not proved here, twist equivalence is compatible with Galois conjugacy, and this
is the set of the newform orbits of the newforms in the twist class of any newform of `x`. -/
def twistClass : Set (Σ L : ℕ+, NewformOrbit L k) :=
  {y | ∃ (f : Newform N k) (g : Newform y.1 k), f.newformOrbit = x ∧ g.newformOrbit = y.2 ∧
    f.IsTwistEquivalent g}

lemma self_mem_twistClass : ⟨⟨N, NeZero.pos N⟩, x⟩ ∈ x.twistClass :=
  x.inductionOn fun f ↦ ⟨f, f, rfl, rfl, .refl f⟩

lemma mk_mem_twistClass {f : Newform N k} {y : Σ L : ℕ+, Newform L k} (hy : y ∈ f.twistClass) :
    ⟨y.1, y.2.newformOrbit⟩ ∈ f.newformOrbit.twistClass :=
  ⟨f, y.2, rfl, rfl, hy⟩

end NewformOrbit

end HeckeRing.GL2
