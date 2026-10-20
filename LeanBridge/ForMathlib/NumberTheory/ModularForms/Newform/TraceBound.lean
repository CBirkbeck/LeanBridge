import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.Embedding
import Mathlib.RingTheory.Trace.Defs

/-!
# The trace bound of a space of newforms

The trace bound of a space of newforms `S_k^{new}(N, χ)` (LMFDB `cmf.trace_bound`) is the least
`m ≥ 1` such that the traces `Tr_{ℚ(f)/ℚ}(aₙ)`, for `n ≤ m`, of the coefficients of its newforms
distinguish their Galois orbits. The traces are invariants of the Galois orbit, and the trace of
`a₁ = 1` is the degree `[ℚ(f) : ℚ]`, so the trace bound is `1` when non-conjugate newforms of the
space have coefficient fields of distinct degrees (the LMFDB says distinct dimensions, the dimension
of a newform being the degree of its coefficient field).

That some `m` distinguishes the Galois orbits follows from the linear independence of the trace
forms, whose coefficients are these traces once every Galois conjugate of a newform is known to be
a newform; this is not proved here, and the trace bound is `0` if no `m` works.

## Main definitions

* `HeckeRing.GL2.Newform.coeffTrace`: the trace `Tr_{ℚ(f)/ℚ}(aₙ)` of a coefficient of a newform.
* `HeckeRing.GL2.Newform.TracesDistinguishNewforms`: the traces of the first `m` coefficients
  distinguish the Galois orbits of a space of newforms (LMFDB `cmf.trace_bound`).
* `HeckeRing.GL2.Newform.traceBound`: the trace bound of a space of newforms
  (LMFDB `cmf.trace_bound`).

## Main results

* `HeckeRing.GL2.Newform.IsGaloisConjugate.coeffTrace_eq`: the traces of the coefficients only
  depend on the Galois orbit.
* `HeckeRing.GL2.Newform.coeffTrace_one`: the trace of `a₁` is the degree of the coefficient field.
* `HeckeRing.GL2.Newform.traceBound_eq_one`: the trace bound is `1` when non-conjugate newforms of
  the space have coefficient fields of distinct degrees.
-/

open UpperHalfPlane TauCeti

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} {f g : Newform N k} {χ : (ZMod N)ˣ →* ℂˣ} {m : ℕ} (n : ℕ)

variable (f) in
/-- The trace `Tr_{ℚ(f)/ℚ}(aₙ)` of the `n`-th coefficient `aₙ` of a newform `f` from its
coefficient field `ℚ(f)` down to `ℚ`. -/
noncomputable def coeffTrace : ℚ :=
  Algebra.trace ℚ (CoefficientField f) (f.orbitQExpansion.coeff n)

/-- **The traces of the coefficients only depend on the Galois orbit.** -/
lemma IsGaloisConjugate.coeffTrace_eq (hfg : f.IsGaloisConjugate g) :
    f.coeffTrace n = g.coeffTrace n := by
  rcases hfg with ⟨σ, hσ⟩
  rw [coeffTrace, coeffTrace, ← Algebra.trace_eq_of_algEquiv hσ.coefficientFieldEquiv,
    ← hσ.map_orbitQExpansion, PowerSeries.coeff_map]
  rfl

variable (f) in
/-- **The trace of `a₁ = 1` is the degree of the coefficient field.** -/
lemma coeffTrace_one : f.coeffTrace 1 = Module.finrank ℚ (CoefficientField f) := by
  have h : f.orbitQExpansion.coeff 1 = 1 := Subtype.ext <| by simp
  rw [coeffTrace, h, ← map_one (algebraMap ℚ (CoefficientField f)), Algebra.trace_algebraMap,
    nsmul_eq_mul, mul_one]

variable (N k χ m) in
/-- The traces `Tr_{ℚ(f)/ℚ}(aₙ)` for `1 ≤ n ≤ m` **distinguish the newforms** of the space of
newforms `S_k^{new}(N, χ)` (LMFDB `cmf.trace_bound`) if newforms of nebentypus `χ` with the same
traces `Tr(aₙ)` for `1 ≤ n ≤ m` are Galois conjugate. -/
def TracesDistinguishNewforms : Prop :=
  ∀ f g : Newform N k, f.χ = χ → g.χ = χ → (∀ n ∈ Set.Icc 1 m, f.coeffTrace n = g.coeffTrace n) →
    f.IsGaloisConjugate g

variable (N k χ) in
/-- The **trace bound** of the space of newforms `S_k^{new}(N, χ)` (LMFDB `cmf.trace_bound`): the
least `m ≥ 1` such that the traces `Tr_{ℚ(f)/ℚ}(aₙ)` for `1 ≤ n ≤ m` distinguish the Galois orbits
of the newforms of nebentypus `χ`. It is `0` if there is no such `m`, which does not happen, but
that is not proved here. -/
noncomputable def traceBound : ℕ :=
  sInf {m | 0 < m ∧ TracesDistinguishNewforms N k χ m}

variable (hne : {m | 0 < m ∧ TracesDistinguishNewforms N k χ m}.Nonempty)

lemma traceBound_le (hm : 0 < m) (h : TracesDistinguishNewforms N k χ m) : traceBound N k χ ≤ m :=
  Nat.sInf_le ⟨hm, h⟩

include hne in
lemma traceBound_pos : 0 < traceBound N k χ :=
  (Nat.sInf_mem hne).1

include hne in
lemma tracesDistinguishNewforms_traceBound : TracesDistinguishNewforms N k χ (traceBound N k χ) :=
  (Nat.sInf_mem hne).2

/-- **The trace bound is `1` when the degrees of the coefficient fields distinguish the Galois
orbits** of the newforms of nebentypus `χ`, the trace of `a₁` being the degree. -/
lemma traceBound_eq_one (h : ∀ f g : Newform N k, f.χ = χ → g.χ = χ →
    Module.finrank ℚ (CoefficientField f) = Module.finrank ℚ (CoefficientField g) →
    f.IsGaloisConjugate g) : traceBound N k χ = 1 := by
  have h₁ : TracesDistinguishNewforms N k χ 1 :=
    fun f g hf hg hfg ↦ h f g hf hg <| by
      exact_mod_cast (f.coeffTrace_one.symm.trans (hfg 1 ⟨le_rfl, le_rfl⟩)).trans g.coeffTrace_one
  exact le_antisymm (traceBound_le one_pos h₁) (traceBound_pos ⟨1, one_pos, h₁⟩)

end HeckeRing.GL2.Newform
