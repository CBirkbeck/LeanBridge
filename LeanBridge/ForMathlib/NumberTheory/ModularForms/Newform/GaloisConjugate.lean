import Mathlib.NumberTheory.LSeries.PrimesInAP
import TauCeti.NumberTheory.ModularForms.Newforms.Conjugate
import TauCeti.NumberTheory.ModularForms.Newforms.Fields

/-!
# Galois conjugate newforms

Two newforms `f = ∑ aₙ qⁿ` and `g = ∑ bₙ qⁿ` are *Galois conjugate* (LMFDB
`cmf.galois_conjugate`) if there is an automorphism `σ` with `bₙ = σ(aₙ)` for all `n ≥ 1`, and one
then writes `g = σ(f)`. The newforms are Tau Ceti's `HeckeRing.GL2.Newform`: normalised good
Hecke eigenforms in the new subspace of `S_k(Γ₁(N))`, with a nebentypus.

The LMFDB takes `σ ∈ Gal(ℚ̄/ℚ)`. Here `σ` is an automorphism of `ℂ`, an element of `Gal(ℂ/ℚ)`
(Mathlib's notation for `ℂ ≃ₐ[ℚ] ℂ`), which acts on the complex Fourier coefficients of a newform
directly. This is the same relation: the coefficients of a newform are algebraic (Tau Ceti proves
it in weight at least two), so only the restriction of `σ` to `ℚ̄` matters, and every automorphism
of `ℚ̄` extends to `ℂ`.

The relation is defined between newforms of any two levels and weights, as the LMFDB definition
does not fix them, so that it applies for instance to a newform and a twist of it. Galois conjugate
newforms do have the same level and weight, but that is not proved here. That `σ(f)` exists for
every newform `f` and every `σ`, i.e. that `σ` applied to the coefficients of a newform gives a
newform, is not proved either.

## Main definitions

* `HeckeRing.GL2.Newform.IsGaloisConjugateBy`: `g = σ(f)` for an automorphism `σ` of `ℂ`
  (LMFDB `cmf.galois_conjugate`).
* `HeckeRing.GL2.Newform.IsGaloisConjugate`: Galois conjugacy of newforms
  (LMFDB `cmf.galois_conjugate`).
* `HeckeRing.GL2.Newform.IsGaloisConjugateBy.coefficientFieldEquiv`: the isomorphism
  `ℚ(f) ≃ ℚ(σ(f))` of coefficient fields induced by `σ`.

## Main results

* `HeckeRing.GL2.Newform.isGaloisConjugateBy_iff_forall_pnat`: `g = σ(f)` exactly when
  `bₙ = σ(aₙ)` for all `n ≥ 1`, the form of the LMFDB definition.
* `HeckeRing.GL2.Newform.isGaloisConjugateBy_conj`: Tau Ceti's conjugate newform `f.conj` is the
  Galois conjugate of `f` by complex conjugation.
* `HeckeRing.GL2.Newform.IsGaloisConjugateBy.unique`: `σ(f)` is unique for given level and weight.
* `HeckeRing.GL2.Newform.IsGaloisConjugateBy.χ_eq`: the nebentypus of `σ(f)` is `σ ∘ χ`.
* `HeckeRing.GL2.Newform.IsGaloisConjugateBy.map_coefficientField`: `σ` maps the coefficient field
  of `f` onto that of `σ(f)`.

Galois conjugacy is reflexive, symmetric and transitive; the induced equivalence relation and the
Galois orbits are in `LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.GaloisOrbit`.
-/

open UpperHalfPlane TauCeti

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} {σ τ : Gal(ℂ/ℚ)} {f : Newform N k}

section

variable {N' N'' : ℕ} [NeZero N'] [NeZero N''] {k' k'' : ℤ} {g : Newform N' k'}
  {h : Newform N'' k''}

variable (σ f g) in
/-- For an automorphism `σ` of `ℂ`, the newform `g = ∑ bₙ qⁿ` is the **Galois conjugate** `σ(f)`
of the newform `f = ∑ aₙ qⁿ` (LMFDB `cmf.galois_conjugate`) if `bₙ = σ(aₙ)` for all `n`, i.e. if
the `q`-expansion of `g` is that of `f` with `σ` applied to its coefficients. Both are cusp forms,
so `a₀ = b₀ = 0`, and it is the same to ask it for `n ≥ 1` as the LMFDB does
(`isGaloisConjugateBy_iff_forall_pnat`). The LMFDB takes `σ ∈ Gal(ℚ̄/ℚ)`; this is the same
relation, as the coefficients of a newform are algebraic and automorphisms of `ℚ̄` extend to
`ℂ`. -/
def IsGaloisConjugateBy : Prop :=
  qExpansion 1 g.toCuspForm = PowerSeries.map σ (qExpansion 1 f.toCuspForm)

lemma isGaloisConjugateBy_iff : f.IsGaloisConjugateBy σ g ↔ ∀ n : ℕ,
    (qExpansion 1 g.toCuspForm).coeff n = σ ((qExpansion 1 f.toCuspForm).coeff n) := by
  simp [IsGaloisConjugateBy, PowerSeries.ext_iff]

/-- **Galois conjugacy is a condition on the coefficients `aₙ` with `n ≥ 1`**: `g = σ(f)` exactly
when `bₙ = σ(aₙ)` for all `n ≥ 1`, which is the form of the LMFDB definition. -/
lemma isGaloisConjugateBy_iff_forall_pnat : f.IsGaloisConjugateBy σ g ↔ ∀ n : ℕ+,
    (qExpansion 1 g.toCuspForm).coeff n = σ ((qExpansion 1 f.toCuspForm).coeff n) := by
  refine isGaloisConjugateBy_iff.trans ⟨fun hfg n ↦ hfg n, fun hfg n ↦ ?_⟩
  rcases n with _ | n
  · rw [CuspFormClass.qExpansion_coeff_zero g.toCuspForm one_pos
      (one_mem_strictPeriods_Gamma1_map N'), CuspFormClass.qExpansion_coeff_zero f.toCuspForm
      one_pos (one_mem_strictPeriods_Gamma1_map N), map_zero]
  · exact hfg n.succPNat

lemma IsGaloisConjugateBy.coeff (hfg : f.IsGaloisConjugateBy σ g) (n : ℕ) :
    (qExpansion 1 g.toCuspForm).coeff n = σ ((qExpansion 1 f.toCuspForm).coeff n) :=
  isGaloisConjugateBy_iff.mp hfg n

variable (f) in
lemma isGaloisConjugateBy_one : f.IsGaloisConjugateBy 1 f :=
  isGaloisConjugateBy_iff.mpr fun _ ↦ rfl

lemma IsGaloisConjugateBy.symm (hfg : f.IsGaloisConjugateBy σ g) : g.IsGaloisConjugateBy σ⁻¹ f :=
  isGaloisConjugateBy_iff.mpr fun n ↦ by rw [hfg.coeff, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]

lemma IsGaloisConjugateBy.trans (hfg : f.IsGaloisConjugateBy σ g)
    (hgh : g.IsGaloisConjugateBy τ h) : f.IsGaloisConjugateBy (τ * σ) h :=
  isGaloisConjugateBy_iff.mpr fun n ↦ by rw [hgh.coeff, hfg.coeff, AlgEquiv.mul_apply]

variable (f) in
/-- **The conjugate newform is a Galois conjugate**: Tau Ceti's conjugate newform `f.conj`, with
coefficients the complex conjugates of those of `f`, is `σ(f)` for complex conjugation `σ`. -/
lemma isGaloisConjugateBy_conj : f.IsGaloisConjugateBy (Complex.conjAe.restrictScalars ℚ) f.conj :=
  f.qExpansion_conj

/-- **Uniqueness of `σ(f)`**: for a given automorphism `σ`, at most one newform of a given level and
weight is the Galois conjugate `σ(f)`. -/
lemma IsGaloisConjugateBy.unique {g' : Newform N' k'} (hfg : f.IsGaloisConjugateBy σ g)
    (hfg' : f.IsGaloisConjugateBy σ g') : g = g' :=
  Newform.ext <| CuspForm.qExpansion_injective one_pos (one_mem_strictPeriods_Gamma1_map N') <|
    Eq.trans hfg (Eq.symm hfg')

lemma IsGaloisConjugateBy.eigenvalue (hfg : f.IsGaloisConjugateBy σ g) {n : ℕ+}
    (hn : n.val.Coprime N) (hn' : n.val.Coprime N') :
    g.eigenvalue n hn' = σ (f.eigenvalue n hn) := by
  rw [← g.qExpansion_coeff_eq_eigenvalue g.isNorm n hn',
    ← f.qExpansion_coeff_eq_eigenvalue f.isNorm n hn, hfg.coeff]

/-- **`σ` maps the coefficient field of `f` onto that of `σ(f)`.** -/
lemma IsGaloisConjugateBy.map_coefficientField (hfg : f.IsGaloisConjugateBy σ g) :
    (CoefficientField f).map (σ : ℂ →ₐ[ℚ] ℂ) = CoefficientField g := by
  rw [CoefficientField_def, CoefficientField_def, IntermediateField.adjoin_map, ← Set.range_comp]
  exact congrArg _ <| congrArg _ <| funext fun n ↦ (hfg.coeff n).symm

/-- The isomorphism `ℚ(f) ≃ ℚ(σ(f))` between the coefficient fields of `f` and of its Galois
conjugate `σ(f)` induced by `σ`. -/
noncomputable def IsGaloisConjugateBy.coefficientFieldEquiv (hfg : f.IsGaloisConjugateBy σ g) :
    CoefficientField f ≃ₐ[ℚ] CoefficientField g :=
  ((CoefficientField f).equivMap (σ : ℂ →ₐ[ℚ] ℂ)).trans <|
    IntermediateField.equivOfEq hfg.map_coefficientField

@[simp]
lemma IsGaloisConjugateBy.coe_coefficientFieldEquiv_apply (hfg : f.IsGaloisConjugateBy σ g)
    (x : CoefficientField f) : (hfg.coefficientFieldEquiv x : ℂ) = σ x :=
  rfl

variable (f g) in
/-- Two newforms `f` and `g` are **Galois conjugate** (LMFDB `cmf.galois_conjugate`) if
`g = σ(f)` for some automorphism `σ` of `ℂ`, i.e. if `bₙ = σ(aₙ)` for all `n`. -/
def IsGaloisConjugate : Prop :=
  ∃ σ : Gal(ℂ/ℚ), f.IsGaloisConjugateBy σ g

lemma IsGaloisConjugateBy.isGaloisConjugate (hfg : f.IsGaloisConjugateBy σ g) :
    f.IsGaloisConjugate g :=
  ⟨σ, hfg⟩

variable (f) in
lemma IsGaloisConjugate.refl : f.IsGaloisConjugate f :=
  ⟨1, f.isGaloisConjugateBy_one⟩

lemma IsGaloisConjugate.symm (hfg : f.IsGaloisConjugate g) : g.IsGaloisConjugate f :=
  hfg.elim fun _ hσ ↦ hσ.symm.isGaloisConjugate

lemma IsGaloisConjugate.trans (hfg : f.IsGaloisConjugate g) (hgh : g.IsGaloisConjugate h) :
    f.IsGaloisConjugate h :=
  hfg.elim fun _ hσ ↦ hgh.elim fun _ hτ ↦ (hσ.trans hτ).isGaloisConjugate

lemma isGaloisConjugate_comm : f.IsGaloisConjugate g ↔ g.IsGaloisConjugate f :=
  ⟨.symm, .symm⟩

variable (f) in
lemma isGaloisConjugate_conj : f.IsGaloisConjugate f.conj :=
  f.isGaloisConjugateBy_conj.isGaloisConjugate

lemma IsGaloisConjugate.finrank_coefficientField_eq (hfg : f.IsGaloisConjugate g) :
    Module.finrank ℚ (CoefficientField f) = Module.finrank ℚ (CoefficientField g) :=
  hfg.elim fun _ hσ ↦ hσ.coefficientFieldEquiv.toLinearEquiv.finrank_eq

end

variable {g : Newform N k}

/-- **The nebentypus of `σ(f)` is `σ ∘ χ`**: if `g = σ(f)` for newforms `f` and `g` of the same
level and weight, the nebentypus of `g` is that of `f` followed by `σ`. At a prime `p ∤ N`, Tau
Ceti's `char_prime_eq_coeff` gives `χ(p) = (a_p² - a_{p²}) / p ^ (k - 1)`, and every unit modulo
`N` is the class of such a prime, by Dirichlet's theorem. -/
lemma IsGaloisConjugateBy.χ_eq (hfg : f.IsGaloisConjugateBy σ g) :
    g.χ = (Units.map (σ : ℂ →* ℂ)).comp f.χ := by
  refine MonoidHom.ext fun u ↦ Units.ext ?_
  rcases Nat.forall_exists_prime_gt_and_eq_mod u.isUnit N with ⟨p, hpN, hp, hpu⟩
  have hcop : p.Coprime N :=
    hp.coprime_iff_not_dvd.mpr fun h ↦ (Nat.le_of_dvd (NeZero.pos N) h).not_gt hpN
  have hu : ZMod.unitOfCoprime p hcop = u := Units.ext <| by rw [ZMod.coe_unitOfCoprime, hpu]
  subst hu
  rw [MonoidHom.comp_apply, Units.coe_map, char_prime_eq_coeff g hp hcop,
    char_prime_eq_coeff f hp hcop, hfg.coeff p, hfg.coeff (p ^ 2)]
  simp

lemma IsGaloisConjugateBy.χ_apply (hfg : f.IsGaloisConjugateBy σ g) (u : (ZMod N)ˣ) :
    (g.χ u : ℂ) = σ (f.χ u) := by
  rw [hfg.χ_eq, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_ofClass]

end HeckeRing.GL2.Newform
