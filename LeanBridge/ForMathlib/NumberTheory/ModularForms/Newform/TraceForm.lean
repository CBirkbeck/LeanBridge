import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.Dimension
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.GaloisOrbitLabel

/-!
# Trace forms of newforms

The trace form `Tr(f)` of a newform `f` (LMFDB `cmf.trace_form`) is the sum of its distinct Galois
conjugates, here the sum of the newforms in its Galois orbit. It is a cusp form in the new subspace
`S_k(Γ₁(N))ⁿᵉʷ`, whose first coefficient is the dimension of `f`.

The LMFDB describes it equivalently as the sum `∑ ι(f)` over the embeddings `ι` of the coefficient
field `ℚ(f)` into `ℂ`, so that `aₙ(Tr(f)) = Tr_{ℚ(f)/ℚ}(aₙ(f))` is an integer, in every weight. That
needs every Galois conjugate of `f` to be a newform, which holds by
`HeckeRing.GL2.Newform.exists_isGaloisConjugateBy`, in `Newform/GaloisConjugateExists.lean`.

The trace form of a space of newforms `S_k^{new}(N, χ)` is the sum of the trace forms of its
newform orbits, i.e. of the newforms in the Galois orbits of the newforms of nebentypus `χ`.

## Main definitions

* `HeckeRing.GL2.Newform.traceForm`: the trace form of a newform (LMFDB `cmf.trace_form`).
* `HeckeRing.GL2.Newform.newspaceTraceForm`: the trace form of a space of newforms
  `S_k^{new}(N, χ)` (LMFDB `cmf.trace_form`).

## Main results

* `HeckeRing.GL2.Newform.traceForm_mem_cuspFormsNew`,
  `HeckeRing.GL2.Newform.newspaceTraceForm_mem_cuspFormsNew`: the trace forms of a newform and of a
  space of newforms are new.
* `HeckeRing.GL2.Newform.qExpansion_coeff_one_traceForm`: its first coefficient is the dimension
  of `f`.
* `HeckeRing.GL2.Newform.qExpansion_coeff_traceForm_eq_trace`,
  `HeckeRing.GL2.Newform.exists_int_qExpansion_coeff_traceForm`: `aₙ(Tr(f)) = Tr_{ℚ(f)/ℚ}(aₙ(f))`,
  an integer, in every weight.
-/

open UpperHalfPlane TauCeti CongruenceSubgroup Matrix SpecialLinearGroup

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} {f g : Newform N k} {χ : (ZMod N)ˣ →* ℂˣ} (n : ℕ)

variable (f) in
/-- The **trace form** `Tr(f)` of a newform `f` (LMFDB `cmf.trace_form`): the sum of the distinct
Galois conjugates of `f`, i.e. of the newforms in its Galois orbit. The LMFDB equivalently sums the
embeddings `ι(f)` over all embeddings `ι` of the coefficient field, which is the same sum, as every
Galois conjugate of `f` is a newform (`galoisOrbitEmbedding_surjective`, in
`Newform/GaloisOrbit.lean`, and `qExpansion_coeff_traceForm_eq_trace`). -/
noncomputable def traceForm : CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  ∑ᶠ g ∈ f.galoisOrbit, g.toCuspForm

variable (f) in
lemma traceForm_eq_sum : f.traceForm = ∑ g ∈ f.finite_galoisOrbit.toFinset, g.toCuspForm :=
  finsum_mem_eq_finite_toFinset_sum _ f.finite_galoisOrbit

lemma IsGaloisConjugate.traceForm_eq (hfg : f.IsGaloisConjugate g) : f.traceForm = g.traceForm := by
  rw [traceForm, traceForm, galoisOrbit_eq_iff.mpr hfg]

variable (f) in
lemma traceForm_mem_newformSubspace : f.traceForm ∈ f.newformSubspace :=
  f.traceForm_eq_sum ▸ Submodule.sum_mem _ fun _ hg ↦
    toCuspForm_mem_newformSubspace (f.finite_galoisOrbit.mem_toFinset.mp hg)

variable (f) in
/-- **The trace form is new**: it lies in `S_k(Γ₁(N))ⁿᵉʷ`. -/
lemma traceForm_mem_cuspFormsNew : f.traceForm ∈ cuspFormsNew N k :=
  f.newformSubspace_le_cuspFormsNew f.traceForm_mem_newformSubspace

variable (f) in
lemma qExpansion_coeff_traceForm : (qExpansion 1 f.traceForm).coeff n =
    ∑ g ∈ f.finite_galoisOrbit.toFinset, (qExpansion 1 g.toCuspForm).coeff n := by
  simp only [← CuspForm.qExpansionCoeffₗ_apply one_pos (one_mem_strictPeriods_Gamma1_map N),
    traceForm_eq_sum, map_sum]

variable (f) in
/-- **The first coefficient of the trace form is the dimension of the newform**: each Galois
conjugate is normalised. -/
lemma qExpansion_coeff_one_traceForm : (qExpansion 1 f.traceForm).coeff 1 = f.dimension := by
  simp [qExpansion_coeff_traceForm, dimension_eq_ncard_galoisOrbit,
    Set.ncard_eq_toFinset_card _ f.finite_galoisOrbit]

variable (f) in
/-- **The coefficients of the trace form are traces**, in every weight: `aₙ(Tr(f))` is the trace
from `ℚ(f)` to `ℚ` of `aₙ(f)`, the trace form being the sum of the embeddings of `f`. -/
lemma qExpansion_coeff_traceForm_eq_trace : (qExpansion 1 f.traceForm).coeff n =
    algebraMap ℚ ℂ (Algebra.trace ℚ (CoefficientField f) (f.orbitQExpansion.coeff n)) :=
  (f.qExpansion_coeff_traceForm n).trans <| (f.coeffTrace_eq_sum n).symm.trans <|
    (eq_ratCast (algebraMap ℚ ℂ) _).symm

variable (f) in
/-- **The trace form has integer coefficients**, in every weight: the coefficients of a newform are
algebraic integers, so their traces are integers. -/
lemma exists_int_qExpansion_coeff_traceForm : ∃ m : ℤ, (qExpansion 1 f.traceForm).coeff n = m :=
  (f.exists_int_coeffTrace n).imp fun m hm ↦ by
    rw [qExpansion_coeff_traceForm, ← coeffTrace_eq_sum, hm, Rat.cast_intCast]

variable (N k χ) in
/-- The **trace form of the space of newforms** `S_k^{new}(N, χ)` (LMFDB `cmf.trace_form`): the sum
of the trace forms of its newform orbits, i.e. of the newforms Galois conjugate to a newform of
nebentypus `χ`. -/
noncomputable def newspaceTraceForm : CuspForm ((Gamma1 N).map (mapGL ℝ)) k :=
  ∑ᶠ g ∈ {g : Newform N k | ∃ f : Newform N k, f.χ = χ ∧ f.IsGaloisConjugate g}, g.toCuspForm

/-- **The trace form of a space of newforms is new.** -/
lemma newspaceTraceForm_mem_cuspFormsNew : newspaceTraceForm N k χ ∈ cuspFormsNew N k :=
  finsum_mem_induction (· ∈ cuspFormsNew N k) (zero_mem _) (fun _ _ ↦ add_mem) fun g _ ↦ g.isNew

end HeckeRing.GL2.Newform
