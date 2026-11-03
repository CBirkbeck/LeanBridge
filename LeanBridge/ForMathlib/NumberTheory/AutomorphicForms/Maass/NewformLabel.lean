import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.Label
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.NewformAtkinLehner
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Maass.NewformSpectrum
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.GaloisOrbitLabel
import Std.Data.String.ToNat

/-!
# The label of a Maass cusp newform of trivial character

The label of a Maass newform `f ∈ M_k(Γ₀(N), χ)` (LMFDB `mf.maass.label`) is `N.k.a.m.d`, or `N.m`
when `k = 0`, `a = 1` and `d = 1`, where `N.a` is the Conrey label of `χ`, `m` the spectral index of
the eigenvalue of `f` and `d` the index of `f` among the finitely many newforms of level `N`,
character `χ` and eigenvalue `λ`, ordered lexicographically by the sequences
`(Re a(n), Im a(n))_{n ≥ 1}`.

For weight `k = 0` and the trivial character, whose Conrey label is `N.1` (the knowl
`character.dirichlet.conrey`: "`χ_q(1, ·)` is always trivial"), which is the case of the LMFDB's
data, all the components are functions of the form:

* `m` is the spectral index in the spectrum of the Maass cusp newforms
  (`UpperHalfPlane.maassNewformSpectralIndexLabel`), which determines the eigenvalue
  (`UpperHalfPlane.maassNewformSpectralIndexLabel_injOn`);
* the coefficients `a(n)` of the even and odd cusp newforms with spectral parameter `R`, normalised
  by `a(1) = 1` (`mf.maass.mwf.coefficients`), form a finite set
  (`UpperHalfPlane.finite_maassNewformCoeffSet`): two such forms with different coefficients and the
  same parity are orthogonal, since their Hecke eigenvalues must differ at a prime `p ∤ N` by strong
  multiplicity one in the new space, the Hecke operators `T_p` being self-adjoint; and the cusp
  forms with a given eigenvalue have finite dimension.

The knowl's "there are only finitely many Maass newforms" with a given eigenvalue needs this
normalisation, since a nonzero multiple of a newform is a newform.

Not available here: the Conrey labels `N.a` of the other characters (`TauCeti.conreyCharacter`, on
Tau Ceti's main but not at the pinned version), the coefficients of the newforms with a nontrivial
character, and the Maass newforms of weight `k ≠ 0`, for which `UpperHalfPlane.IsMaassFormOfWeight`
has no new space. For them the label is `UpperHalfPlane.maassLabel`, from its components.
Classically a newform of trivial character is even or odd, and an even and an odd newform never
have the same normalised coefficients, which are not proved here either. So the index `d`
determines the newform among those with the same eigenvalue and parity, and a cusp newform neither
even nor odd, having no coefficients, would get the junk index `1`.

## Main definitions

* `UpperHalfPlane.maassNewformCoeffSet`: the set of the coefficient sequences of the normalised even
  and odd cusp newforms of level `N` and spectral parameter `R`.
* `UpperHalfPlane.maassNewformCoeffFinset`: the same set as a finite set.
* `UpperHalfPlane.maassNewformCoeffIndex` (LMFDB `mf.maass.label`): the index `d` of a cusp newform.
* `UpperHalfPlane.maassNewformLabel` (LMFDB `mf.maass.label`): the label of a cusp newform of weight
  `0` with trivial character.

## Main results

* `UpperHalfPlane.IsMaassCuspNewform.maassCoefficients_normalisedNewform_mem_of_even`,
  `UpperHalfPlane.IsMaassCuspNewform.maassCoefficients_normalisedNewform_mem_of_odd`: the
  coefficients of the normalised newform lie in this set.
* `UpperHalfPlane.maassPetersson_eq_zero_of_cosine`,
  `UpperHalfPlane.maassPetersson_eq_zero_of_sine`: cusp newforms normalised by `a(1) = 1` with the
  same parity and different coefficients are orthogonal.
* `UpperHalfPlane.finite_maassNewformCoeffSet`: there are finitely many coefficient sequences.
* `UpperHalfPlane.maassNewformSpectralIndexLabel_injOn`: the spectral index `m`, as written in the
  labels, determines the eigenvalue.
* `UpperHalfPlane.maassNewformLabel_neg`: the label does not depend on the sign of `R`, which the
  form determines up to sign.
* `UpperHalfPlane.IsMaassCuspNewform.maassNormalisedNewform_eq_of_even`,
  `UpperHalfPlane.IsMaassCuspNewform.maassNormalisedNewform_eq_of_odd`: the index `d` determines the
  normalised newform among those with the same eigenvalue and parity.
-/

open scoped ComplexConjugate

namespace DirichletCharacter

lemma letterCode_ne_toString (m n : ℕ) : letterCode m ≠ toString n := by
  intro h
  have hl : (letterCode m).toList = Nat.toDigits 10 n := by
    rw [h, Nat.toString_eq_repr, Nat.toList_repr]
  rcases List.exists_mem_of_ne_nil (Nat.toDigits 10 n) Nat.toDigits_ne_nil with ⟨c, hc⟩
  have hd : c.isDigit = true := Nat.isDigit_of_mem_toDigits (by norm_num) (by norm_num) hc
  rw [← hl, toList_letterCode] at hc
  split_ifs at hc
  · rw [List.mem_singleton] at hc
    subst hc
    exact absurd hd (by decide)
  · rcases List.mem_map.mp hc with ⟨d, hd', rfl⟩
    have hd26 : d < 26 := Nat.digits_lt_base (by norm_num) (List.mem_reverse.mp hd')
    have key : ∀ d : Fin 26, (Char.ofNat (97 + d)).isDigit = false := by
      decide
    rw [key ⟨d, hd26⟩] at hd
    exact Bool.false_ne_true hd

end DirichletCharacter

namespace UpperHalfPlane

variable {N p : ℕ} {χ : DirichletCharacter ℂ N} {R a e e' : ℂ} {F G : ℍ → ℂ} {c c' : ℕ+ → ℂ}

lemma IsMaassCuspNewform.mem_maassCuspSpace (hF : IsMaassCuspNewform N R F) :
    F ∈ maassCuspSpace N 1 (((maassEigenvalue R).re : ℝ) : ℂ) := by
  rw [hF.ofReal_re_maassEigenvalue]
  exact mem_maassCuspSpace_iff.mpr ⟨hF.1.1.1, hF.mem_maassCuspidalSpace⟩

variable (N R) in
/-- The set of the **coefficient sequences** (LMFDB `mf.maass.label`, `mf.maass.mwf.coefficients`)
of the even and odd Maass cusp newforms of weight `0` on `Γ₀(N)` with trivial character and spectral
parameter `R`, normalised by `a(1) = 1`: the sequences `c` with `c(1) = 1` for which such a newform
has the cosine or the sine expansion with coefficients `c`. It is finite
(`finite_maassNewformCoeffSet`). -/
def maassNewformCoeffSet : Set (ℕ+ → ℂ) :=
  {c | c 1 = 1 ∧ ∃ F : ℍ → ℂ, IsMaassCuspNewform N R F ∧
    (HasMaassCosineExpansion (F ∘ ofComplex) R c ∨ HasMaassSineExpansion (F ∘ ofComplex) R c)}

variable (N R) in
lemma maassNewformCoeffSet_neg : maassNewformCoeffSet N (-R) = maassNewformCoeffSet N R := by
  have hK (x : ℝ) : (Complex.I * -R).besselK x = (Complex.I * R).besselK x := by
    rw [mul_neg, Complex.besselK_neg]
  simp only [maassNewformCoeffSet, IsMaassCuspNewform, maassEigenvalue, neg_sq,
    HasMaassCosineExpansion, HasMaassSineExpansion, hK]

variable [NeZero N]

/-- **The spectral index determines the eigenvalue** (LMFDB `mf.maass.label`: "`m` is the spectral
index, which uniquely identifies the eigenvalue"): as written in the labels, in decimal or with
letters, the index takes different values at different elements of the spectrum. -/
lemma maassNewformSpectralIndexLabel_injOn :
    Set.InjOn (maassNewformSpectralIndexLabel N χ) (maassNewformSpectrum N χ) := by
  intro x hx y hy he
  simp only [maassNewformSpectralIndexLabel, maassSpectralIndexLabel] at he
  split_ifs at he with h1 h2 h2
  · exact maassNewformSpectralIndex_injOn_exceptional ⟨hx, h1⟩ ⟨hy, h2⟩
      (DirichletCharacter.letterCode_injective he)
  · exact absurd he (DirichletCharacter.letterCode_ne_toString _ _)
  · exact absurd he.symm (DirichletCharacter.letterCode_ne_toString _ _)
  · have h : maassSpectralIndex (maassNewformSpectrum N χ) x =
        maassSpectralIndex (maassNewformSpectrum N χ) y := Nat.repr_injective he
    rcases (not_lt.mp h1).eq_or_lt with h3 | h3 <;> rcases (not_lt.mp h2).eq_or_lt with h4 | h4
    · rw [← h3, ← h4]
    · rw [← h3, maassSpectralIndex_quarter] at h
      exact absurd h.symm (maassNewformSpectralIndex_pos hy h4.ne').ne'
    · rw [← h4, maassSpectralIndex_quarter] at h
      exact absurd h (maassNewformSpectralIndex_pos hx h3.ne').ne'
    · exact maassNewformSpectralIndex_injOn_standard ⟨hx, h3⟩ ⟨hy, h4⟩ h

/-- **The coefficients of a normalised even cusp newform lie in the set of coefficient
sequences**. -/
lemma IsMaassCuspNewform.maassCoefficients_normalisedNewform_mem_of_even
    (hF : IsMaassCuspNewform N R F) (hs : IsEvenMaassForm (F ∘ ofComplex)) :
    maassCoefficients R (maassNormalisedNewform R F ∘ ofComplex) ∈ maassNewformCoeffSet N R := by
  refine ⟨hF.maassCoefficients_normalisedNewform_one_of_even hs, maassNormalisedNewform R F,
    hF.normalisedNewform_of_even hs, Or.inl ?_⟩
  rw [(hF.hasMaassCosineExpansion hs).maassCoefficients_normalisedNewform]
  exact (hF.hasMaassCosineExpansion hs).normalisedNewform

/-- **The coefficients of a normalised odd cusp newform lie in the set of coefficient
sequences**. -/
lemma IsMaassCuspNewform.maassCoefficients_normalisedNewform_mem_of_odd
    (hF : IsMaassCuspNewform N R F) (hs : IsOddMaassForm (F ∘ ofComplex)) :
    maassCoefficients R (maassNormalisedNewform R F ∘ ofComplex) ∈ maassNewformCoeffSet N R := by
  refine ⟨hF.maassCoefficients_normalisedNewform_one_of_odd hs, maassNormalisedNewform R F,
    hF.normalisedNewform_of_odd hs, Or.inr ?_⟩
  rw [(hF.hasMaassSineExpansion hs).maassCoefficients_normalisedNewform]
  exact (hF.hasMaassSineExpansion hs).normalisedNewform

lemma IsMaassNewform.eq_of_maassPetersson_ne_zero (hF : IsMaassNewform N 1 a F)
    (hG : IsMaassNewform N 1 a G) (h : maassPetersson N F G ≠ 0) (hp : p.Prime) (hpN : ¬p ∣ N)
    (he : ∀ z : ℂ, 0 < z.im → maassHeckeOperator p (F ∘ ofComplex) z = e * (F ∘ ofComplex) z)
    (he' : ∀ z : ℂ, 0 < z.im → maassHeckeOperator p (G ∘ ofComplex) z = e' * (G ∘ ofComplex) z)
    (hr : conj e' = e') : e = e' := by
  have h1 : maassPetersson N (fun τ ↦ maassHeckeOperator p (F ∘ ofComplex) τ) G =
      maassPetersson N F fun τ ↦ maassHeckeOperator p (G ∘ ofComplex) τ :=
    maassPetersson_maassHeckeOperator (hp.coprime_iff_not_dvd.mpr hpN) hp hF.1.1 hG.1.1
  have h2 : (fun τ : ℍ ↦ maassHeckeOperator p (F ∘ ofComplex) (τ : ℂ)) = e • F := by
    funext τ
    simpa using he τ τ.im_pos
  have h3 : (fun τ : ℍ ↦ maassHeckeOperator p (G ∘ ofComplex) (τ : ℂ)) = e' • G := by
    funext τ
    simpa using he' τ τ.im_pos
  have h4 : maassPetersson N (e • F) ((1 : ℂ) • G) = e * conj 1 * maassPetersson N F G :=
    maassPetersson_smul_smul e 1
  have h5 : maassPetersson N ((1 : ℂ) • F) (e' • G) = 1 * conj e' * maassPetersson N F G :=
    maassPetersson_smul_smul 1 e'
  rw [h2, h3] at h1
  simp only [one_smul, map_one, mul_one, one_mul] at h4 h5
  rw [h4, h5, hr] at h1
  exact mul_right_cancel₀ h h1

lemma maassPetersson_eq_zero_of_coeff (hF : IsMaassNewform N 1 a F) (hG : IsMaassNewform N 1 a G)
    (hrecF : ∀ {p : ℕ} {e : ℂ}, p.Prime → (∀ z : ℂ, 0 < z.im →
      maassHeckeOperator p (F ∘ ofComplex) z = e * (F ∘ ofComplex) z) → ∀ m : ℕ+,
        c (p.toPNat' * m) + (if p ∣ (m : ℕ) then c ((m : ℕ) / p).toPNat' else 0) = e * c m)
    (hrecG : ∀ {p : ℕ} {e : ℂ}, p.Prime → (∀ z : ℂ, 0 < z.im →
      maassHeckeOperator p (G ∘ ofComplex) z = e * (G ∘ ofComplex) z) → ∀ m : ℕ+,
        c' (p.toPNat' * m) + (if p ∣ (m : ℕ) then c' ((m : ℕ) / p).toPNat' else 0) = e * c' m)
    (heq : (∀ n : ℕ+, (n : ℕ).Coprime N → c n = c' n) → F = G) (hne : F ≠ G) (h1 : c 1 = c' 1) :
    maassPetersson N F G = 0 := by
  by_contra h
  refine hne (heq fun n hn ↦ sub_eq_zero.mp ?_)
  refine coeff_eq_zero_of_coprime (N := N) (c := fun n ↦ c n - c' n) (sub_eq_zero.mpr h1)
    (fun p hp hpN ↦ ?_) hn
  rcases hF.exists_maassHeckeOperator_eq hp hpN with ⟨e, -, he⟩
  rcases hG.exists_maassHeckeOperator_eq hp hpN with ⟨e', hr', he'⟩
  rw [hF.eq_of_maassPetersson_ne_zero hG h hp hpN he he' hr'] at he
  refine ⟨e', fun m ↦ ?_⟩
  have h2 : c (p.toPNat' * m) + (if p ∣ (m : ℕ) then c ((m : ℕ) / p).toPNat' else 0) = e' * c m :=
    hrecF hp he m
  have h3 :
      c' (p.toPNat' * m) + (if p ∣ (m : ℕ) then c' ((m : ℕ) / p).toPNat' else 0) = e' * c' m :=
    hrecG hp he' m
  split_ifs at h2 h3 ⊢ with hpm
  · linear_combination h2 - h3
  · linear_combination h2 - h3

/-- **Normalised even cusp newforms with different coefficients are orthogonal**: for even cusp
newforms `F`, `G` with the same spectral parameter and the cosine expansions with coefficients
`c ≠ c'`, `c(1) = c'(1)`, `⟨F, G⟩ = 0`. Otherwise their Hecke eigenvalues agree at every prime
`p ∤ N`, since `T_p` is self-adjoint, so that `c` and `c'` agree prime to `N` by the Hecke
relations, and `F = G` by strong multiplicity one in the new space. -/
lemma maassPetersson_eq_zero_of_cosine (hF : IsMaassCuspNewform N R F)
    (hG : IsMaassCuspNewform N R G) (hcF : HasMaassCosineExpansion (F ∘ ofComplex) R c)
    (hcG : HasMaassCosineExpansion (G ∘ ofComplex) R c') (h1 : c 1 = c' 1) (hne : c ≠ c') :
    maassPetersson N F G = 0 := by
  refine maassPetersson_eq_zero_of_coeff (c := c) (c' := c') hF.1 hG.1
    (fun hp he m ↦ hcF.coeff_mul_add_eq hp he m) (fun hp he m ↦ hcG.coeff_mul_add_eq hp he m)
    (eq_of_mem_maassNewSpace_of_cosine hF.1.1 hG.1.1 hcF hcG) (fun he ↦ hne ?_) h1
  subst he
  exact hcF.unique hcG

/-- **Normalised odd cusp newforms with different coefficients are orthogonal**: for odd cusp
newforms `F`, `G` with the same spectral parameter and the sine expansions with coefficients
`c ≠ c'`, `c(1) = c'(1)`, `⟨F, G⟩ = 0`. -/
lemma maassPetersson_eq_zero_of_sine (hF : IsMaassCuspNewform N R F) (hG : IsMaassCuspNewform N R G)
    (hcF : HasMaassSineExpansion (F ∘ ofComplex) R c)
    (hcG : HasMaassSineExpansion (G ∘ ofComplex) R c') (h1 : c 1 = c' 1) (hne : c ≠ c') :
    maassPetersson N F G = 0 := by
  refine maassPetersson_eq_zero_of_coeff (c := c) (c' := c') hF.1 hG.1
    (fun hp he m ↦ hcF.coeff_mul_add_eq hp he m) (fun hp he m ↦ hcG.coeff_mul_add_eq hp he m)
    (eq_of_mem_maassNewSpace_of_sine hF.1.1 hG.1.1 hcF hcG) (fun he ↦ hne ?_) h1
  subst he
  exact hcF.unique hcG

variable (N R)

/-- **There are finitely many normalised even and odd cusp newforms with a given eigenvalue** (LMFDB
`mf.maass.label`, for the trivial character): their coefficient sequences form a finite set, since
those of a given parity belong to pairwise orthogonal cusp forms with the same eigenvalue
(`maassPetersson_eq_zero_of_cosine`, `maassPetersson_eq_zero_of_sine`,
`finite_of_forall_maassPetersson_eq_zero`). -/
lemma finite_maassNewformCoeffSet : (maassNewformCoeffSet N R).Finite := by
  have hcos : {c : ℕ+ → ℂ | c 1 = 1 ∧ ∃ F : ℍ → ℂ, IsMaassCuspNewform N R F ∧
      HasMaassCosineExpansion (F ∘ ofComplex) R c}.Finite := by
    have hch : ∀ c ∈ {c : ℕ+ → ℂ | c 1 = 1 ∧ ∃ F : ℍ → ℂ, IsMaassCuspNewform N R F ∧
        HasMaassCosineExpansion (F ∘ ofComplex) R c}, ∃ F : ℍ → ℂ, IsMaassCuspNewform N R F ∧
          HasMaassCosineExpansion (F ∘ ofComplex) R c := fun c hc ↦ hc.2
    choose! F hF using hch
    exact finite_of_forall_maassPetersson_eq_zero (χ := 1) (Λ := (maassEigenvalue R).re)
      (e := fun _ ↦ (maassEigenvalue R).re) (fun c hc ↦ (hF c hc).1.1.2.1)
      (fun c hc ↦ (hF c hc).1.mem_maassCuspSpace) (fun _ _ ↦ le_rfl) fun c hc c' hc' hne ↦
        maassPetersson_eq_zero_of_cosine (hF c hc).1 (hF c' hc').1 (hF c hc).2 (hF c' hc').2
          (hc.1.trans hc'.1.symm) hne
  have hsin : {c : ℕ+ → ℂ | c 1 = 1 ∧ ∃ F : ℍ → ℂ, IsMaassCuspNewform N R F ∧
      HasMaassSineExpansion (F ∘ ofComplex) R c}.Finite := by
    have hch : ∀ c ∈ {c : ℕ+ → ℂ | c 1 = 1 ∧ ∃ F : ℍ → ℂ, IsMaassCuspNewform N R F ∧
        HasMaassSineExpansion (F ∘ ofComplex) R c}, ∃ F : ℍ → ℂ, IsMaassCuspNewform N R F ∧
          HasMaassSineExpansion (F ∘ ofComplex) R c := fun c hc ↦ hc.2
    choose! F hF using hch
    exact finite_of_forall_maassPetersson_eq_zero (χ := 1) (Λ := (maassEigenvalue R).re)
      (e := fun _ ↦ (maassEigenvalue R).re) (fun c hc ↦ (hF c hc).1.1.2.1)
      (fun c hc ↦ (hF c hc).1.mem_maassCuspSpace) (fun _ _ ↦ le_rfl) fun c hc c' hc' hne ↦
        maassPetersson_eq_zero_of_sine (hF c hc).1 (hF c' hc').1 (hF c hc).2 (hF c' hc').2
          (hc.1.trans hc'.1.symm) hne
  refine (hcos.union hsin).subset ?_
  rintro c ⟨h1, F, hF, hc | hc⟩
  · exact Or.inl ⟨h1, F, hF, hc⟩
  · exact Or.inr ⟨h1, F, hF, hc⟩

/-- The set `maassNewformCoeffSet N R` of the coefficient sequences of the normalised even and odd
cusp newforms, as a finite set. -/
noncomputable def maassNewformCoeffFinset : Finset (ℕ+ → ℂ) :=
  (finite_maassNewformCoeffSet N R).toFinset

variable (F)

/-- The **index** `d` (LMFDB `mf.maass.label`) of a Maass cusp newform `F` of weight `0` on `Γ₀(N)`
with trivial character, even or odd, and spectral parameter `R`: the position of the coefficient
sequence of the newform normalised by `a(1) = 1` in the finite set of those with this eigenvalue
(`maassNewformCoeffFinset`), in the lexicographic order of `(Re a(n), Im a(n))_{n ≥ 1}`
(`maassCoeffIndex`), counted from `1`. For a function with neither a cosine nor a sine expansion,
such as a cusp newform neither even nor odd if there is one, `maassNormalisedNewform R F` is `0`,
and its coefficient sequence `0`, which precedes the whole set, gets the junk index `1`. -/
noncomputable def maassNewformCoeffIndex : ℕ :=
  maassCoeffIndex (maassNewformCoeffFinset N R)
    (maassCoefficients R (maassNormalisedNewform R F ∘ ofComplex))

/-- The **label** (LMFDB `mf.maass.label`) of a Maass cusp newform `F` of weight `0` on `Γ₀(N)` with
trivial character, even or odd, and spectral parameter `R`: `N.m` when `d = 1`, and `N.0.1.m.d`
otherwise (`maassLabel`, with the Conrey index `a = 1` of the trivial character), where `m` is the
spectral index of the eigenvalue `1/4 + R²` among those of the cusp newforms of level `N`
(`maassNewformSpectralIndexLabel`) and `d` is `maassNewformCoeffIndex`. The form determines `R` up
to sign, and the label does not depend on the sign (`maassNewformLabel_neg`). For a function that is
not an even or odd cusp newform with spectral parameter `R`, the label is junk. -/
noncomputable def maassNewformLabel : String :=
  maassLabel N 0 1 (maassNewformSpectralIndexLabel N 1 (maassEigenvalue R).re)
    (maassNewformCoeffIndex N R F)

/-- **The label does not depend on the sign of the spectral parameter**, which a nonzero form
determines up to sign (`HasMaassSpectralParameter.eq_or_eq_neg`), so that it is a function of the
form. -/
lemma maassNewformLabel_neg : maassNewformLabel N (-R) F = maassNewformLabel N R F := by
  have h1 : maassEigenvalue (-R) = maassEigenvalue R := by
    rw [maassEigenvalue, maassEigenvalue, neg_sq]
  have h2 : maassNewformCoeffFinset N (-R) = maassNewformCoeffFinset N R := by
    ext c
    rw [maassNewformCoeffFinset, maassNewformCoeffFinset,
      (finite_maassNewformCoeffSet N (-R)).mem_toFinset,
      (finite_maassNewformCoeffSet N R).mem_toFinset, maassNewformCoeffSet_neg]
  have h3 : maassNormalisedNewform (-R) F = maassNormalisedNewform R F := by
    rw [maassNormalisedNewform, maassNormalisedNewform, maassCoefficients_neg]
  rw [maassNewformLabel, maassNewformLabel, maassNewformCoeffIndex, maassNewformCoeffIndex, h1, h2,
    h3, maassCoefficients_neg]

variable {N R F}

/-- **The index `d` determines an even normalised cusp newform** (LMFDB `mf.maass.label`): two even
Maass cusp newforms with the same spectral parameter and the same index have the same normalised
newform, by strong multiplicity one in the new space. -/
lemma IsMaassCuspNewform.maassNormalisedNewform_eq_of_even (hF : IsMaassCuspNewform N R F)
    (hG : IsMaassCuspNewform N R G) (hsF : IsEvenMaassForm (F ∘ ofComplex))
    (hsG : IsEvenMaassForm (G ∘ ofComplex))
    (h : maassNewformCoeffIndex N R F = maassNewformCoeffIndex N R G) :
    maassNormalisedNewform R F = maassNormalisedNewform R G := by
  have hc : maassCoefficients R (maassNormalisedNewform R F ∘ ofComplex) =
      maassCoefficients R (maassNormalisedNewform R G ∘ ofComplex) :=
    maassCoeffIndex_injOn _ ((finite_maassNewformCoeffSet N R).mem_toFinset.mpr
      (hF.maassCoefficients_normalisedNewform_mem_of_even hsF))
      ((finite_maassNewformCoeffSet N R).mem_toFinset.mpr
        (hG.maassCoefficients_normalisedNewform_mem_of_even hsG)) h
  have hF2 : HasMaassCosineExpansion (maassNormalisedNewform R F ∘ ofComplex) R
      (maassCoefficients R (maassNormalisedNewform R F ∘ ofComplex)) := by
    rw [(hF.hasMaassCosineExpansion hsF).maassCoefficients_normalisedNewform]
    exact (hF.hasMaassCosineExpansion hsF).normalisedNewform
  have hG2 : HasMaassCosineExpansion (maassNormalisedNewform R G ∘ ofComplex) R
      (maassCoefficients R (maassNormalisedNewform R G ∘ ofComplex)) := by
    rw [(hG.hasMaassCosineExpansion hsG).maassCoefficients_normalisedNewform]
    exact (hG.hasMaassCosineExpansion hsG).normalisedNewform
  exact eq_of_mem_maassNewSpace_of_cosine (hF.normalisedNewform_of_even hsF).1.1
    (hG.normalisedNewform_of_even hsG).1.1 hF2 hG2 fun n _ ↦ congrFun hc n

/-- **The index `d` determines an odd normalised cusp newform** (LMFDB `mf.maass.label`): two odd
Maass cusp newforms with the same spectral parameter and the same index have the same normalised
newform, by strong multiplicity one in the new space. -/
lemma IsMaassCuspNewform.maassNormalisedNewform_eq_of_odd (hF : IsMaassCuspNewform N R F)
    (hG : IsMaassCuspNewform N R G) (hsF : IsOddMaassForm (F ∘ ofComplex))
    (hsG : IsOddMaassForm (G ∘ ofComplex))
    (h : maassNewformCoeffIndex N R F = maassNewformCoeffIndex N R G) :
    maassNormalisedNewform R F = maassNormalisedNewform R G := by
  have hc : maassCoefficients R (maassNormalisedNewform R F ∘ ofComplex) =
      maassCoefficients R (maassNormalisedNewform R G ∘ ofComplex) :=
    maassCoeffIndex_injOn _ ((finite_maassNewformCoeffSet N R).mem_toFinset.mpr
      (hF.maassCoefficients_normalisedNewform_mem_of_odd hsF))
      ((finite_maassNewformCoeffSet N R).mem_toFinset.mpr
        (hG.maassCoefficients_normalisedNewform_mem_of_odd hsG)) h
  have hF2 : HasMaassSineExpansion (maassNormalisedNewform R F ∘ ofComplex) R
      (maassCoefficients R (maassNormalisedNewform R F ∘ ofComplex)) := by
    rw [(hF.hasMaassSineExpansion hsF).maassCoefficients_normalisedNewform]
    exact (hF.hasMaassSineExpansion hsF).normalisedNewform
  have hG2 : HasMaassSineExpansion (maassNormalisedNewform R G ∘ ofComplex) R
      (maassCoefficients R (maassNormalisedNewform R G ∘ ofComplex)) := by
    rw [(hG.hasMaassSineExpansion hsG).maassCoefficients_normalisedNewform]
    exact (hG.hasMaassSineExpansion hsG).normalisedNewform
  exact eq_of_mem_maassNewSpace_of_sine (hF.normalisedNewform_of_odd hsF).1.1
    (hG.normalisedNewform_of_odd hsG).1.1 hF2 hG2 fun n _ ↦ congrFun hc n

end UpperHalfPlane
