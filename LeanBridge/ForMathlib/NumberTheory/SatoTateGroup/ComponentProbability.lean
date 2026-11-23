import LeanBridge.ForMathlib.MeasureTheory.Group.AnalyticLevelSet
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.Components
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.Embedding
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.HodgeCircle
import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.OneParameter
import LeanBridge.ForMathlib.Topology.Instances.Matrix
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# The probabilities of a Sato–Tate group

Let `G` be a Sato–Tate group (LMFDB `st_group.definition`) with its Haar probability measure. A
random variable on `G` that is a polynomial in the entries of the matrices
(`SatoTateGroup.IsEntryPolynomial`), such as a coefficient `aᵢ` of the characteristic polynomial or
the trace, is real-analytic along the one-parameter subgroups `t ↦ exp (t • X)` of `G`, which
generate its identity component `G⁰`
(`SatoTateGroup.connectedComponentOfOne_le_closure_iUnion_range_expOneParameter`). So, by Serre's
argument (`MeasureTheory.measure_setOf_eq_sdiff_setOf_forall_mem_closure_eq_zero`), almost every
point of a level set has its coset `G⁰ g` in the level set
(`SatoTateGroup.IsEntryPolynomial.measure_setOf_eq_sdiff_eq_zero`): on each connected component of
`G` the random variable is either identically equal to a value `z` or equal to `z` with
probability zero (`SatoTateGroup.IsEntryPolynomial.forall_eq_or_measure_eq_zero`), and the
probability that it equals `z` is the proportion of the connected components on which it is
identically `z` (`SatoTateGroup.IsEntryPolynomial.measureReal_setOf_eq`), a rational number, as
`G` has finitely many connected components. This is Proposition 8.4.3.3 of Serre's *Lectures on
`N_X(p)`*.

For the event probabilities `Pr[aᵢ = n]` (LMFDB `st_group.probabilities`):
* `Pr[aᵢ = n]` is a rational number, the proportion of the connected components on which `aᵢ` is
  identically `n` (`SatoTateGroup.probability_eq_card_div_card`), and it vanishes unless `n` is one
  of finitely many integers (`SatoTateGroup.finite_setOf_probability_ne_zero`);
* `Pr[aᵢ = n] = 0` exactly when `{g | aᵢ(g) = n}` has measure zero
  (`SatoTateGroup.probability_eq_zero_iff`), and on a finite group exactly when that set is empty
  (`SatoTateGroup.probability_eq_zero_iff_of_finite`), but not in general: on the Sato–Tate group
  `U(1)` of weight `1` and degree `2` (`SatoTateGroup.torusU1`), `a₁ = -(u + ū)` vanishes at
  `u = i` (`SatoTateGroup.nonempty_setOf_charpolyCoeff_torusU1_one_eq_zero`), though with
  probability zero (`SatoTateGroup.probability_torusU1_one_zero`).

The knowl writes the characteristic polynomial as `∑ aᵢ xⁱ`, while the LMFDB, and
`SatoTateGroup.charpolyCoeff`, take `aᵢ` to be the coefficient of `x ^ (d - i)`. Every coefficient
of the characteristic polynomial is a polynomial in the entries, so the results on polynomials in
the entries hold in either indexing.

For the trace zero density (LMFDB `st_group.trace_zero_density`): on each connected component the
trace is either constant or takes each value with probability zero
(`SatoTateGroup.trace_const_or_forall_measure_eq_zero`), and the trace zero density is the
proportion of the connected components on which the trace is identically zero
(`SatoTateGroup.traceZeroDensity_eq_card_div_card`). A constant trace need not be zero, as on the
finite groups `μ(n)` of weight `0`, but it is zero when `-1` lies in the identity component
(`SatoTateGroup.eq_zero_of_trace_eq_of_neg_one_mem`). In odd weight this is the case when the
identity component contains a Hodge circle whose Hodge numbers `h^{p,q}` vanish off `p + q = w`, as
those of a motive of weight `w` do: such a circle passes through `-1`
(`SatoTateGroup.matrix_eq_neg_one_of_hasHodgeEigenvalues`), so a constant trace is zero
(`SatoTateGroup.eq_zero_of_trace_eq_of_hasHodgeEigenvalues`). The Hodge circle of `U(1)` is an
example (`SatoTateGroup.hasHodgeEigenvalues_torusU1HodgeCircle`). A `SatoTateGroup` carries no
Hodge circle, and without one the claim fails: the trivial subgroup of `USp(2)`, of weight `1`, has
the constant trace `2`.

## Main definitions

* `SatoTateGroup.torusU1`: the Sato–Tate group `U(1)` of weight `1` and degree `2`, and
  `SatoTateGroup.torusU1HodgeCircle`, its Hodge circle.

## Main results

* `SatoTateGroup.IsEntryPolynomial.measure_setOf_eq_sdiff_eq_zero`,
  `SatoTateGroup.IsEntryPolynomial.forall_eq_or_measure_eq_zero`,
  `SatoTateGroup.IsEntryPolynomial.measureReal_setOf_eq`: Serre's Proposition 8.4.3.3 for the
  polynomials in the entries.
* `SatoTateGroup.probability_eq_card_div_card`, `SatoTateGroup.finite_setOf_probability_ne_zero`,
  `SatoTateGroup.probability_eq_zero_iff`, `SatoTateGroup.probability_eq_zero_iff_of_finite`,
  `SatoTateGroup.probability_torusU1_one_zero`,
  `SatoTateGroup.nonempty_setOf_charpolyCoeff_torusU1_one_eq_zero` (LMFDB `st_group.probabilities`).
* `SatoTateGroup.trace_const_or_forall_measure_eq_zero`,
  `SatoTateGroup.traceZeroDensity_eq_card_div_card`,
  `SatoTateGroup.eq_zero_of_trace_eq_of_neg_one_mem`,
  `SatoTateGroup.eq_zero_of_trace_eq_of_hasHodgeEigenvalues`,
  `SatoTateGroup.hasHodgeEigenvalues_torusU1HodgeCircle` (LMFDB `st_group.trace_zero_density`).

## References

* J.-P. Serre, *Lectures on `N_X(p)`*, CRC Press (2012), Proposition 8.4.3.3.
-/

open Matrix MeasureTheory Polynomial Set TauCeti

open Subgroup (connectedComponentOfOne)

namespace SatoTateGroup

open TopologicalSpace in
instance (G : SatoTateGroup) : SecondCountableTopology G.toSubgroup :=
  Subtype.secondCountableTopology _

end SatoTateGroup

namespace SatoTateGroup.IsEntryPolynomial

variable {G : SatoTateGroup} {f : G.toSubgroup → ℂ} (z : ℂ)

/-- **Almost every point of a level set of a polynomial in the entries of a Sato–Tate group `G` has
its whole coset `G⁰ g` in the level set**: the polynomial is real-analytic along the
one-parameter subgroups `t ↦ exp (t • X)` of `G`, which generate a subgroup containing `G⁰`. -/
lemma measure_setOf_eq_sdiff_eq_zero (hf : G.IsEntryPolynomial f) : haarProb G.toSubgroup
    ({g | f g = z} \ {g | ∀ h ∈ connectedComponentOfOne G.toSubgroup, f (h * g) = z}) = 0 := by
  have hFγ (X : G.matrixLieAlgebra) (w g : G.toSubgroup) :
      AnalyticOnNhd ℝ (fun s ↦ f (w * expOneParameter X s * g)) univ := by
    rcases hf with ⟨P, hP⟩
    rintro s -
    have h : (fun s ↦ f (w * expOneParameter X s * g)) = fun s : ℝ ↦ MvPolynomial.eval
        (fun p ↦ (G.matrix w * NormedSpace.exp (s • X.1) * G.matrix g) p.1 p.2) P := by
      funext s
      rw [hP, ← matrix_expOneParameter]
      rfl
    rw [h]
    exact analyticAt_eval_mul_exp_smul_mul _ _ _ s P
  refine measure_mono_null ?_ (measure_setOf_eq_sdiff_setOf_forall_mem_closure_eq_zero (z := z)
    continuous_expOneParameter expOneParameter_zero expOneParameter_neg hf.continuous hFγ)
  exact fun g hg ↦ ⟨hg.1, fun hT ↦ hg.2 fun h hh ↦
    hT h (G.connectedComponentOfOne_le_closure_iUnion_range_expOneParameter hh)⟩

/-- **On each connected component of a Sato–Tate group, a polynomial in the entries is either
identically `z` or equal to `z` with probability zero** (Serre, Proposition 8.4.3.3). -/
lemma forall_eq_or_measure_eq_zero (hf : G.IsEntryPolynomial f)
    (c : ConnectedComponents G.toSubgroup) : (∀ g, ConnectedComponents.mk g = c → f g = z) ∨
      haarProb G.toSubgroup ({g | f g = z} ∩ ConnectedComponents.mk ⁻¹' {c}) = 0 := by
  rcases ConnectedComponents.surjective_coe c with ⟨g₀, rfl⟩
  rw [connectedComponents_preimage_singleton]
  refine (forall_eq_or_measure_inter_connectedComponent_eq_zero
    (hf.measure_setOf_eq_sdiff_eq_zero z) g₀).imp (fun h g hg ↦ h g ?_) id
  exact ConnectedComponents.coe_eq_coe.mp hg ▸ mem_connectedComponent

/-- **The probability that a polynomial in the entries of a Sato–Tate group `G` equals `z` is the
proportion of the connected components of `G` on which it is identically `z`** (Serre,
Proposition 8.4.3.3), the connected components being finitely many. -/
lemma measureReal_setOf_eq (hf : G.IsEntryPolynomial f) :
    (haarProb G.toSubgroup).real {g | f g = z} = Nat.card {c : ConnectedComponents G.toSubgroup //
      ∀ g, ConnectedComponents.mk g = c → f g = z} / Nat.card (ConnectedComponents G.toSubgroup) :=
  measureReal_setOf_eq_eq_card_div_card (hf.measure_setOf_eq_sdiff_eq_zero z)

end SatoTateGroup.IsEntryPolynomial

namespace SatoTateGroup

variable (G : SatoTateGroup) (i : ℕ) (n : ℤ)

/-! ### Event probabilities -/

/-- **`Pr[aᵢ = n]` is a rational number, the proportion of the connected components of `G` on
which `aᵢ` is identically `n`** (LMFDB `st_group.probabilities`; Serre, Proposition 8.4.3.3). -/
lemma probability_eq_card_div_card : G.probability i n = ((Nat.card
    {c : ConnectedComponents G.toSubgroup // ∀ g, ConnectedComponents.mk g = c →
      G.charpolyCoeff i g = n} / Nat.card (ConnectedComponents G.toSubgroup) : ℚ) : ℝ) := by
  push_cast
  exact (G.isEntryPolynomial_charpolyCoeff i).measureReal_setOf_eq n

/-- **`Pr[aᵢ = n]` vanishes unless `n` is one of finitely many integers** (LMFDB
`st_group.probabilities`): the values of `aᵢ` on the connected components on which it is
constant. -/
lemma finite_setOf_probability_ne_zero : {n : ℤ | G.probability i n ≠ 0}.Finite := by
  let v : ConnectedComponents G.toSubgroup → ℂ := fun c ↦
    G.charpolyCoeff i (Function.surjInv ConnectedComponents.surjective_coe c)
  refine ((finite_range v).preimage Int.cast_injective.injOn).subset fun n hn ↦ ?_
  rw [mem_ofPred_eq, probability_eq_card_div_card] at hn
  have hne : Nat.card {c : ConnectedComponents G.toSubgroup //
      ∀ g, ConnectedComponents.mk g = c → G.charpolyCoeff i g = n} ≠ 0 := fun h ↦ hn <| by
    rw [h]
    simp
  rcases (Nat.card_ne_zero.mp hne).1 with ⟨c, hc⟩
  exact ⟨c, hc _ (Function.surjInv_eq _ c)⟩

/-- **`Pr[aᵢ = n] = 0` exactly when the set of the `g` with `aᵢ(g) = n` has Haar measure zero**
(LMFDB `st_group.probabilities`). -/
lemma probability_eq_zero_iff :
    G.probability i n = 0 ↔ haarProb G.toSubgroup {g | G.charpolyCoeff i g = n} = 0 :=
  measureReal_eq_zero_iff

variable [Finite G.toSubgroup] in
/-- **On a finite Sato–Tate group, `Pr[aᵢ = n] = 0` only when no element has `aᵢ = n`** (LMFDB
`st_group.probabilities`): every element has positive Haar measure. -/
lemma probability_eq_zero_iff_of_finite :
    G.probability i n = 0 ↔ {g | G.charpolyCoeff i g = n} = ∅ := by
  rw [probability_eq_zero_iff]
  refine ⟨fun h ↦ eq_empty_of_forall_notMem fun g hg ↦ ?_, fun h ↦ by rw [h, measure_empty]⟩
  exact (isOpen_discrete {g}).measure_ne_zero _ (singleton_nonempty g)
    (measure_mono_null (singleton_subset_iff.mpr hg) h)

/-- The Sato–Tate group **`U(1)`** of weight `1` and degree `2` (LMFDB `1.2.B.1.1a`): the diagonal
torus `{diag(u, ū) | |u| = 1}` of `USp(2)`, `SatoTateGroup.ofTorus` of the whole circle. It is the
Sato–Tate group `WeierstrassCurve.satoTateU1` of an elliptic curve with complex multiplication
(`SatoTateGroup.torusU1_eq_satoTateU1`). -/
noncomputable def torusU1 : SatoTateGroup :=
  ofTorus (⊤ : Subgroup (Fin 1 → Circle)) isClosed_univ

instance : ConnectedSpace torusU1.toSubgroup := by
  have _ : ConnectedSpace Circle := Circle.exp_surjective.connectedSpace Circle.exp.continuous
  have _ : ConnectedSpace (⊤ : Subgroup (Fin 1 → Circle)) :=
    isConnected_iff_connectedSpace.mp isConnected_univ
  exact (ofTorusEquiv (⊤ : Subgroup (Fin 1 → Circle)) isClosed_univ).toHomeomorph.connectedSpace_iff
    |>.mp inferInstance

/-- **On the Sato–Tate group `U(1)`, `a₁ = 0` has probability zero** (LMFDB
`st_group.probabilities`): `U(1)` is connected, and `a₁ = -2` at the identity. -/
lemma probability_torusU1_one_zero : torusU1.probability 1 0 = 0 := by
  have h : IsEmpty {c : ConnectedComponents torusU1.toSubgroup //
      ∀ g, ConnectedComponents.mk g = c → torusU1.charpolyCoeff 1 g = (0 : ℤ)} := by
    refine ⟨fun c ↦ ?_⟩
    rcases ConnectedComponents.surjective_coe c.1 with ⟨g, hg⟩
    have h₁ : ConnectedComponents.mk (1 : torusU1.toSubgroup) = c.1 := by
      rw [← hg, ConnectedComponents.coe_eq_coe, PreconnectedSpace.connectedComponent_eq_univ,
        PreconnectedSpace.connectedComponent_eq_univ]
    have h₂ : torusU1.charpolyCoeff 1 (ofTorusEquiv _ isClosed_univ 1) = -2 :=
      (charpolyCoeff_one_ofTorusEquiv one_pos 1).trans (by norm_num)
    rw [map_one] at h₂
    have h₃ : (-2 : ℂ) = ((0 : ℤ) : ℂ) := h₂.symm.trans (c.2 1 h₁)
    norm_num at h₃
  rw [probability_eq_card_div_card, Nat.card_of_isEmpty]
  simp

/-- **On the Sato–Tate group `U(1)`, `a₁ = 0` at `diag(i, -i)`** (LMFDB `st_group.probabilities`):
an event of probability zero need not be empty. -/
lemma nonempty_setOf_charpolyCoeff_torusU1_one_eq_zero :
    {g | torusU1.charpolyCoeff 1 g = 0}.Nonempty := by
  refine ⟨ofTorusEquiv (⊤ : Subgroup (Fin 1 → Circle)) isClosed_univ
    ⟨fun _ ↦ Circle.exp (Real.pi / 2), Subgroup.mem_top _⟩, ?_⟩
  refine (charpolyCoeff_one_ofTorusEquiv one_pos _).trans ?_
  simp

/-! ### The trace zero density -/

variable (c : ConnectedComponents G.toSubgroup) {t : ℂ}

/-- **On each connected component of a Sato–Tate group, the trace is either constant or takes
each value with probability zero** (LMFDB `st_group.trace_zero_density`, corrected: a constant
trace need not be zero). -/
lemma trace_const_or_forall_measure_eq_zero : (∃ t, ∀ g, ConnectedComponents.mk g = c →
    G.trace g = t) ∨ ∀ t, haarProb G.toSubgroup
      ({g | G.trace g = t} ∩ ConnectedComponents.mk ⁻¹' {c}) = 0 := by
  by_cases h : ∃ t, ∀ g, ConnectedComponents.mk g = c → G.trace g = t
  · exact Or.inl h
  · exact Or.inr fun t ↦
      (G.isEntryPolynomial_trace.forall_eq_or_measure_eq_zero t c).resolve_left fun h' ↦ h ⟨t, h'⟩

/-- **The trace zero density of a Sato–Tate group is the proportion of its connected components
on which the trace is identically zero** (LMFDB `st_group.trace_zero_density`). -/
lemma traceZeroDensity_eq_card_div_card : G.traceZeroDensity = Nat.card
    {c : ConnectedComponents G.toSubgroup // ∀ g, ConnectedComponents.mk g = c → G.trace g = 0} /
      Nat.card (ConnectedComponents G.toSubgroup) :=
  G.isEntryPolynomial_trace.measureReal_setOf_eq 0

/-- **A trace constant on a connected component is zero when `-1` lies in the identity
component** (LMFDB `st_group.trace_zero_density`): translating by `-1` keeps the component and
changes the sign of the trace. -/
lemma eq_zero_of_trace_eq_of_neg_one_mem {ε : G.toSubgroup}
    (hε : ε ∈ connectedComponentOfOne G.toSubgroup) (hε' : G.matrix ε = -1)
    (ht : ∀ g, ConnectedComponents.mk g = c → G.trace g = t) : t = 0 := by
  rcases ConnectedComponents.surjective_coe c with ⟨g, rfl⟩
  have hmem : (ε * g)⁻¹ * g ∈ connectedComponentOfOne G.toSubgroup := by
    simpa using Subgroup.normal_connectedComponentOfOne.conj_mem _ (inv_mem hε) g⁻¹
  have h₁ : G.trace (ε * g) = t :=
    ht _ (ConnectedComponents.coe_eq_coe.mpr
      ((connectedComponent_eq_connectedComponent_iff _ _).mpr hmem))
  have h₂ : G.trace (ε * g) = -G.trace g := by
    have h : G.matrix (ε * g) = -G.matrix g := by
      rw [← neg_one_mul, ← hε']
      rfl
    rw [SatoTateGroup.trace, h, Matrix.trace_neg]
    rfl
  have h₃ : G.trace g = t := ht g rfl
  linear_combination (h₂ - h₁ - h₃) / 2

variable {h : Circle →ₜ* G.toSubgroup} {hodge : ℕ → ℕ → ℕ}

/-- **In odd weight, a trace constant on a connected component of a Sato–Tate group is zero**
(LMFDB `st_group.trace_zero_density`), when `G⁰` contains a Hodge circle whose Hodge numbers
`h^{p,q}` vanish off `p + q = w`, as for the Sato–Tate group of a motive of odd weight `w`: the
Hodge circle passes through `-1`. -/
lemma eq_zero_of_trace_eq_of_hasHodgeEigenvalues (hw : Odd G.weight)
    (h₀ : ∀ u, h u ∈ connectedComponentOfOne G.toSubgroup) (hh : G.HasHodgeEigenvalues h hodge)
    (hpq : ∀ p q, hodge p q ≠ 0 → p + q = G.weight)
    (ht : ∀ g, ConnectedComponents.mk g = c → G.trace g = t) : t = 0 :=
  G.eq_zero_of_trace_eq_of_neg_one_mem c (h₀ _)
    (matrix_eq_neg_one_of_hasHodgeEigenvalues hw hh hpq) ht

/-- The **Hodge circle** `u ↦ diag(u, ū)` (LMFDB `st_group.hodge_circle`) of the Sato–Tate group
`U(1)`, onto `U(1)` itself. -/
noncomputable def torusU1HodgeCircle : Circle →ₜ* torusU1.toSubgroup where
  toMonoidHom := (ofTorusEquiv (⊤ : Subgroup (Fin 1 → Circle)) isClosed_univ).toMonoidHom.comp
    (Subgroup.topEquiv.symm.toMonoidHom.comp (Pi.constMonoidHom (Fin 1) Circle))
  continuous_toFun := (ofTorusEquiv _ isClosed_univ).continuous.comp <|
    (continuous_pi fun _ ↦ continuous_id).subtype_mk _

lemma torusU1HodgeCircle_mem (u : Circle) :
    torusU1HodgeCircle u ∈ connectedComponentOfOne torusU1.toSubgroup := by
  rw [Subgroup.connectedComponentOfOne_eq_top]
  exact Subgroup.mem_top _

/-- **The Hodge circle of `U(1)` has the Hodge numbers `h^{1,0} = h^{0,1} = 1` of an elliptic
curve**, which vanish off `p + q = 1`: `diag(u, ū)` has the eigenvalues `u^{1-0}` and `u^{0-1}`.
So `U(1)` satisfies the hypotheses of `SatoTateGroup.eq_zero_of_trace_eq_of_hasHodgeEigenvalues`. -/
lemma hasHodgeEigenvalues_torusU1HodgeCircle :
    torusU1.HasHodgeEigenvalues torusU1HodgeCircle fun p q ↦ if p + q = 1 then 1 else 0 := by
  refine ⟨rfl, fun u ↦ ?_⟩
  have hchar : (torusU1.matrix (torusU1HodgeCircle u)).charpoly =
      (∏ _ : Fin 1, (X - C (u : ℂ))) * ∏ _ : Fin 1, (X - C ((u⁻¹ : Circle) : ℂ)) :=
    charpoly_uspTorusMatrix fun _ ↦ u
  rw [hchar]
  simp [torusU1, ofTorus, Finset.prod_range_succ]
  ring1

end SatoTateGroup
