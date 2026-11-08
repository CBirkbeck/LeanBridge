import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.ClassicalLiftHecke
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.SelfTwistHecke
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.AlmostAllPrimes
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.SelfTwistQuadratic

/-!
# Complex multiplication of the adelic lift of a classical newform

Let `f` be a newform of level `N` and weight `k`, `φ_f` its adelic lift, and `ψ` a primitive
nontrivial Dirichlet character of modulus `M`, with Hecke character `ψ_𝔸` (Tau Ceti's
`HeckeCharacter.ofDirichletCharacter`). The condition `a_𝔭 = ψ_𝔸(𝔭) a_𝔭` at the good primes of the
knowl `mf.cm` (`AdelicGL2.HasCMEigenvalues`) holds for `φ_f` exactly when `f` admits a self twist by
`ψ` in the classical sense of the LMFDB (`HeckeRing.GL2.Newform.HasSelfTwist`, LMFDB
`cmf.self_twist`): the Hecke eigenvalue of `φ_f` at `p ∤ N` is `p ^ (1 - k / 2) a_p`
(`AdelicGL2.heckeEigenvalue_adelicLift`), `ψ_𝔸` is unramified at `p` exactly when `p ∤ M`, where its
value at `p` is `ψ(p)`, and a self twist at almost all primes holds at all the primes prime to
`N M` (`HeckeRing.GL2.Newform.IsTwistAtAlmostAllPrimes.isTwistBy`). In particular complex
multiplication of the adelic lift by `ψ_𝔸`, in the sense that `φ_f` is equal to its twist
(`AdelicGL2.HasCMBy`), gives the classical self twist, and the character of the condition on the
eigenvalues is quadratic, as the self twists of a classical newform are
(`HeckeRing.GL2.Newform.HasSelfTwist.isQuadratic_character`). The converse, from the classical self
twist to the equality of the representations, is strong multiplicity one, which is not proved here.

No newform with complex multiplication is formalised at the pins of Mathlib and Tau Ceti, nor in
LeanBridge, so these statements have no concrete instance with a nontrivial `ψ`.

## Main results

* `AdelicGL2.hasCMEigenvalues_adelicLift_iff` (LMFDB `mf.cm`): the condition on the eigenvalues for
  the adelic lift is the classical self twist.
* `AdelicGL2.isQuadratic_of_hasCMEigenvalues_adelicLift` (LMFDB `mf.cm`): its character is
  quadratic.
* `AdelicGL2.HasCMBy.hasSelfTwist` (LMFDB `mf.cm`): complex multiplication of the adelic lift gives
  the classical self twist.
-/

open IsDedekindDomain NumberField Rat HeightOneSpectrum UpperHalfPlane TauCeti GlobalNumberFields
  HeckeRing GL2

open scoped AdeleRing Classical

namespace AdelicGL2

variable {N : ℕ} [NeZero N] {k : ℤ} {M : ℕ} [NeZero M] {ψ : DirichletCharacter ℂ M}
  (f : Newform N k)

lemma conductorExponent_ofDirichletCharacter_eq_zero_iff (v : HeightOneSpectrum (𝓞 ℚ)) :
    (HeckeCharacter.ofDirichletCharacter M (NeZero.ne M) ψ).conductorExponent v = 0 ↔
      ¬Ideal.absNorm v.asIdeal ∣ ψ.conductor := by
  rw [← HeckeCharacter.exponent_conductor
    (HeckeCharacter.isFiniteOrder_ofDirichletCharacter (hn := NeZero.ne M) ψ) v, ← Nat.lt_one_iff,
    ← not_le, ← Modulus.pow_dvd_finitePart_iff_le_exponent,
    HeckeCharacter.conductor_ofDirichletCharacter_finitePart_eq_span, pow_one, Ideal.dvd_iff_le,
    Ideal.span_singleton_le_iff_mem, HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd]

lemma not_le_of_conductorExponent_eq_zero (hψ : ψ.IsPrimitive) {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : (HeckeCharacter.ofDirichletCharacter M (NeZero.ne M) ψ).conductorExponent v = 0) :
    ¬Ideal.span {(M : 𝓞 ℚ)} ≤ v.asIdeal := by
  rw [conductorExponent_ofDirichletCharacter_eq_zero_iff, hψ] at hv
  rw [Ideal.span_singleton_le_iff_mem, HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd]
  exact hv

lemma heckeEigenvalue_adelicLift_eq_iff {v : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ¬Ideal.span {(N : 𝓞 ℚ)} ≤ v.asIdeal) (hM : ¬Ideal.span {(M : 𝓞 ℚ)} ≤ v.asIdeal) :
    heckeEigenvalue v (adelicLift N k f.toCuspForm) =
        (characterAt v (HeckeCharacter.ofDirichletCharacter M (NeZero.ne M) ψ) : ℂ) *
          heckeEigenvalue v (adelicLift N k f.toCuspForm) ↔
      (qExpansion 1 f.toCuspForm).coeff (Ideal.absNorm v.asIdeal) =
        ψ (Ideal.absNorm v.asIdeal) *
          (qExpansion 1 f.toCuspForm).coeff (Ideal.absNorm v.asIdeal) := by
  have hs : ((Real.sqrt (Ideal.absNorm v.asIdeal) ^ (2 - k) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (zpow_ne_zero _ (Real.sqrt_ne_zero'.mpr
      (Nat.cast_pos.mpr (prime_absNorm_asIdeal v).pos)))
  rw [heckeEigenvalue_adelicLift f hv, characterAt_ofDirichletCharacter _ hM, mul_left_comm,
    mul_right_inj' hs]

/-- **The condition of `mf.cm` on the eigenvalues of the adelic lift of a newform is the classical
self twist** (LMFDB `mf.cm`, `cmf.self_twist`): for a primitive nontrivial Dirichlet character `ψ`,
`a_𝔭 = ψ(𝔭) a_𝔭` holds for the adelic lift of `f` at the good primes exactly when `f` admits a self
twist by `ψ`. -/
lemma hasCMEigenvalues_adelicLift_iff (hψ : ψ.IsPrimitive) (hψ₁ : ψ ≠ 1) :
    HasCMEigenvalues (HeckeCharacter.ofDirichletCharacter M (NeZero.ne M) ψ)
      (Ideal.span {(N : 𝓞 ℚ)}) (adelicLift N k f.toCuspForm) ↔ f.HasSelfTwist ψ := by
  refine ⟨fun h ↦ ⟨NeZero.ne M, hψ, ?_⟩, fun h ↦ ⟨fun h₁ ↦ hψ₁ ?_, fun v hv hc ↦ ?_⟩⟩
  · have hfin : {p : ℕ | p ∣ N * M}.Finite :=
      (Nat.divisors (N * M)).finite_toSet.subset fun p hp ↦
        Nat.mem_divisors.mpr ⟨hp, mul_ne_zero (NeZero.ne N) (NeZero.ne M)⟩
    refine Filter.mem_of_superset hfin.compl_mem_cofinite fun p hp hpp ↦ ?_
    rcases HeightOneSpectrum.exists_absNorm_eq hpp with ⟨v, rfl⟩
    have hvN : ¬Ideal.span {(N : 𝓞 ℚ)} ≤ v.asIdeal := by
      rw [Ideal.span_singleton_le_iff_mem, HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd]
      exact fun h₁ ↦ hp (h₁.mul_right M)
    have hvM : ¬Ideal.span {(M : 𝓞 ℚ)} ≤ v.asIdeal := by
      rw [Ideal.span_singleton_le_iff_mem, HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd]
      exact fun h₁ ↦ hp (h₁.mul_left N)
    have hc : (HeckeCharacter.ofDirichletCharacter M (NeZero.ne M) ψ).conductorExponent v = 0 := by
      rw [conductorExponent_ofDirichletCharacter_eq_zero_iff, hψ]
      exact fun h₁ ↦ hp (h₁.mul_left N)
    exact (heckeEigenvalue_adelicLift_eq_iff f hvN hvM).mp (h.2 v hvN hc)
  · exact HeckeCharacter.ofDirichletCharacter_injective (h₁.trans (map_one _).symm)
  · have hM : ¬Ideal.span {(M : 𝓞 ℚ)} ≤ v.asIdeal := not_le_of_conductorExponent_eq_zero hψ hc
    exact (heckeEigenvalue_adelicLift_eq_iff f hv hM).mpr ((h.2.2.isTwistBy h.1 h.2.1).2.2 _
      ((coprime_absNorm_of_not_le hv).mul_right (coprime_absNorm_of_not_le hM)))

/-- **The character of the condition of `mf.cm` is quadratic for the adelic lift of a newform**
(LMFDB `mf.cm`): if `a_𝔭 = ψ(𝔭) a_𝔭` holds for the adelic lift of `f` at the good primes, for a
primitive Dirichlet character `ψ`, then `ψ² = 1`. Over `ℚ` this is the knowl's "such a character is
necessarily quadratic" from the condition on the eigenvalues alone. -/
lemma isQuadratic_of_hasCMEigenvalues_adelicLift (hψ : ψ.IsPrimitive)
    (h : HasCMEigenvalues (HeckeCharacter.ofDirichletCharacter M (NeZero.ne M) ψ)
      (Ideal.span {(N : 𝓞 ℚ)}) (adelicLift N k f.toCuspForm)) : ψ.IsQuadratic :=
  (hasCMEigenvalues_adelicLift_iff f hψ fun h₁ ↦ h.1 (by rw [h₁, map_one])).mp h
    |>.isQuadratic_character

/-- **Complex multiplication of the adelic lift of a newform gives the classical self twist**
(LMFDB `mf.cm`): if the adelic lift of `f` is equal to its twist by the Hecke character of a
primitive Dirichlet character `ψ`, then `f` admits a self twist by `ψ`. -/
lemma HasCMBy.hasSelfTwist (hψ : ψ.IsPrimitive)
    (h : HasCMBy (HeckeCharacter.ofDirichletCharacter M (NeZero.ne M) ψ)
      (adelicLift N k f.toCuspForm)) : f.HasSelfTwist ψ := by
  have hψ₁ : ψ ≠ 1 := fun h₁ ↦ h.1 (by rw [h₁, map_one])
  exact (hasCMEigenvalues_adelicLift_iff f hψ hψ₁).mp
    (h.hasCMEigenvalues (isHeckeEigenform_adelicLift f))

end AdelicGL2
