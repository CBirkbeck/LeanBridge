import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.AmbientDensity
import TauCeti.RepresentationTheory.Compact.Invariants

/-!
# The trace moments of a Sato–Tate group

The trace `t` of a Haar-random element of a Sato–Tate group `G ⊆ U(d)` (LMFDB
`st_group.trace_moments`) has as distribution the pushforward of the Haar probability measure of `G`
under the trace map (`SatoTateGroup.traceDistribution`), and its `n`th moment `Mₙ[t] = E[tⁿ]`
(`SatoTateGroup.traceMoment`) is the moment of that distribution. The character of the `n`th tensor
power `(ℂ^d)^{⊗n}` of the standard representation of `G` is `tⁿ`, so `E[tⁿ]` is the Haar integral of
a character, which is the dimension of the invariants of `G` in `(ℂ^d)^{⊗n}` (Tau Ceti's
`ContRepresentation.integral_character_eq_finrank_invariants`): it is a nonnegative integer.

The knowl also says that in odd weight `t = -a₁` (`SatoTateGroup.charpolyCoeff_one_eq_neg_trace`,
in every weight and degree), and that the moment sequences of `t` and `a₁` coincide because their
distributions are symmetric about zero. The distribution of `t` is symmetric when `-1 ∈ G`
(`SatoTateGroup.traceDistribution_map_neg`), and then the moment sequences of `t` and `a₁`
coincide (`SatoTateGroup.moment_charpolyCoeff_one_eq_traceMoment`). The Sato–Tate group of a
motive of odd weight contains `-1`, the image of `-1` under its Hodge circle, but this is not part
of LeanBridge's `SatoTateGroup`, a closed subgroup of the ambient group: the trivial subgroup of
`USp(2)`, of weight `1`, has `E[t] = 2` and `E[a₁] = -2`.

## Main definitions

* `SatoTateGroup.traceDistribution` (LMFDB `st_group.trace_moments`): the distribution of the
  trace.
* `SatoTateGroup.tensorPowerRep`: the `n`th tensor power of the standard representation of a
  Sato–Tate group.

## Main results

* `SatoTateGroup.traceMoment_eq_integral_traceDistribution`: `E[tⁿ]` is the `n`th moment of the
  distribution of `t`.
* `SatoTateGroup.traceMoment_eq_finrank_invariants` (LMFDB `st_group.trace_moments`): `E[tⁿ]` is
  the dimension of the invariants of `G` in `(ℂ^d)^{⊗n}`, a nonnegative integer.
* `SatoTateGroup.charpolyCoeff_one_eq_neg_trace`: `a₁ = -t`.
* `SatoTateGroup.traceDistribution_map_neg`: the distribution of `t` is symmetric about zero when
  `-1 ∈ G`.
* `SatoTateGroup.moment_charpolyCoeff_one_eq_traceMoment`: the moment sequences of `t` and `a₁`
  coincide when `-1 ∈ G`.
-/

open Matrix MeasureTheory TauCeti

open scoped InnerProductSpace

namespace SatoTateGroup

variable (G : SatoTateGroup) (n : ℕ)

lemma measurable_trace : Measurable G.trace :=
  (continuous_subtype_val.comp continuous_subtype_val).matrix_trace.measurable

/-- The **distribution** of the trace `t` of a Haar-random element of a Sato–Tate group (LMFDB
`st_group.trace_moments`): the pushforward of the Haar probability measure under the trace map. -/
noncomputable def traceDistribution : Measure ℂ :=
  (haarProb G.toSubgroup).map G.trace

/-- **The `n`th trace moment `E[tⁿ]` is the `n`th moment of the distribution of `t`.** -/
lemma traceMoment_eq_integral_traceDistribution :
    G.traceMoment n = ∫ z, z ^ n ∂G.traceDistribution :=
  (integral_map G.measurable_trace.aemeasurable (continuous_pow n).aestronglyMeasurable).symm

/-- The `n`th **tensor power** `(ℂ^d)^{⊗n}` of the standard representation of a Sato–Tate group
`G ⊆ U(d)`, in coordinates: the restriction to `G` of the tensor power of the standard
representation of its ambient group, acting on the functions on the tuples `Fin n → Fin d`. -/
noncomputable def tensorPowerRep :
    ContRepresentation ℂ G.toSubgroup (EuclideanSpace ℂ (Fin n → Fin G.degree)) :=
  ambientTensorRep.restrict (Subgroup.inclusion G.le_ambientGroup)

lemma continuous_tensorPowerRep : Continuous (G.tensorPowerRep n) :=
  continuous_ambientTensorRep.comp (continuous_subtype_val.subtype_mk _)

lemma character_tensorPowerRep (g : G.toSubgroup) :
    (G.tensorPowerRep n).character (G.continuous_tensorPowerRep n) g = G.trace g ^ n := by
  rw [ContRepresentation.character_apply,
    LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin n → Fin G.degree) ℂ)]
  have h (a : Fin n → Fin G.degree) : ⟪EuclideanSpace.basisFun (Fin n → Fin G.degree) ℂ a,
      G.tensorPowerRep n g (EuclideanSpace.basisFun (Fin n → Fin G.degree) ℂ a)⟫_ℂ =
        tensorRep (P := Fin n) (G.matrix g) a a := by
    rw [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_left, map_one, one_mul]
    exact (ambientTensorRep_apply _ _ a).trans (by rw [PiLp.ofLp_single, mulVec_single_one]; rfl)
  refine (Finset.sum_congr rfl fun a _ ↦ h a).trans ?_
  exact (trace_tensorRep (P := Fin n) (G.matrix g)).trans (by rw [Fintype.card_fin]; rfl)

/-- **The trace moments of a Sato–Tate group are nonnegative integers** (LMFDB
`st_group.trace_moments`): `E[tⁿ]` is the dimension of the invariants of `G` in the `n`th tensor
power `(ℂ^d)^{⊗n}` of its standard representation, whose character is `tⁿ`. -/
lemma traceMoment_eq_finrank_invariants :
    G.traceMoment n = Module.finrank ℂ (G.tensorPowerRep n).invariants := by
  rw [← (G.tensorPowerRep n).integral_character_eq_finrank_invariants
    (G.continuous_tensorPowerRep n)]
  simp only [character_tensorPowerRep]
  rfl

/-- **`a₁ = -t`** (LMFDB `st_group.trace_moments`), in every weight and degree. -/
lemma charpolyCoeff_one_eq_neg_trace (g : G.toSubgroup) : G.charpolyCoeff 1 g = -G.trace g := by
  rcases Nat.eq_zero_or_pos G.degree with hd | hd
  · have : IsEmpty (Fin G.degree) := by
      rw [hd]
      infer_instance
    rw [G.charpolyCoeff_of_lt (by omega) g]
    simp [trace]
  · exact G.charpolyCoeff_one hd g

variable {G}

lemma trace_neg_one_mul (h : -1 ∈ G.toSubgroup) (g : G.toSubgroup) :
    G.trace (⟨-1, h⟩ * g) = -G.trace g := by
  simp [trace, matrix, Unitary.coe_neg]

/-- **The distribution of the trace of a Sato–Tate group `G` containing `-1` is symmetric about
zero**: left translation by `-1` preserves the Haar measure and negates the trace. -/
lemma traceDistribution_map_neg (h : -1 ∈ G.toSubgroup) :
    G.traceDistribution.map Neg.neg = G.traceDistribution := by
  have h₁ : Neg.neg ∘ G.trace = G.trace ∘ (⟨-1, h⟩ * ·) :=
    funext fun g ↦ (trace_neg_one_mul h g).symm
  rw [traceDistribution, Measure.map_map measurable_neg G.measurable_trace, h₁,
    ← Measure.map_map G.measurable_trace (measurable_const_mul _), map_mul_left_eq_self]

variable {n}

lemma traceMoment_eq_zero_of_odd (h : -1 ∈ G.toSubgroup) (hn : Odd n) : G.traceMoment n = 0 := by
  have h₁ : ∫ g, G.trace (⟨-1, h⟩ * g) ^ n ∂haarProb G.toSubgroup =
      ∫ g, G.trace g ^ n ∂haarProb G.toSubgroup :=
    integral_mul_left_eq_self (fun g ↦ G.trace g ^ n) _
  simp only [trace_neg_one_mul, hn.neg_pow, integral_neg] at h₁
  exact CharZero.neg_eq_self_iff.mp h₁

variable (G n) in
lemma moment_charpolyCoeff_one : G.moment (G.charpolyCoeff 1) n = (-1) ^ n * G.traceMoment n := by
  rw [traceMoment, moment, moment, expectation, expectation, ← integral_const_mul]
  refine congrArg (integral _) (funext fun g ↦ ?_)
  rw [Pi.pow_apply, Pi.pow_apply, charpolyCoeff_one_eq_neg_trace, neg_pow]

variable (n) in
/-- **The moment sequences of `t` and `a₁` coincide for a Sato–Tate group containing `-1`**
(LMFDB `st_group.trace_moments`): `a₁ = -t` and the odd moments of `t` vanish. -/
lemma moment_charpolyCoeff_one_eq_traceMoment (h : -1 ∈ G.toSubgroup) :
    G.moment (G.charpolyCoeff 1) n = G.traceMoment n := by
  rw [moment_charpolyCoeff_one]
  rcases n.even_or_odd with hn | hn
  · rw [hn.neg_one_pow, one_mul]
  · rw [traceMoment_eq_zero_of_odd h hn, mul_zero]

end SatoTateGroup
