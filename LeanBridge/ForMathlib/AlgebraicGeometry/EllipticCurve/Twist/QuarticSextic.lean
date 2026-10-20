import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Twist.Basic

/-!
# Quartic and sextic twists

Over a field `K` of characteristic not `2` or `3`, an elliptic curve `W` with invariants `c₄` and
`c₆` has the model `y² = x³ - 27 c₄ x - 54 c₆`. When `j(W) = 1728`, that is `c₆ = 0`, the twists of
`W` are its quartic twists `y² = x³ - 27 c₄ D x` by `D ∈ K*`, and two of them are isomorphic over
`K` exactly when the ratio of their parameters is a fourth power: the twists of `W` are
parametrised by `K*/(K*)⁴`. When `j(W) = 0`, that is `c₄ = 0`, the twists of `W` are its sextic
twists `y² = x³ - 54 c₆ D`, parametrised by `K*/(K*)⁶` in the same way.

## Main definitions

* `WeierstrassCurve.quarticTwist` (LMFDB `ec.twists`): the quartic twist of `W` by `D`.
* `WeierstrassCurve.sexticTwist` (LMFDB `ec.twists`): the sextic twist of `W` by `D`.

## Main results

* `WeierstrassCurve.isTwist_quarticTwist` and `WeierstrassCurve.isTwist_sexticTwist`: for
  `D ≠ 0`, the quartic twists of a curve with `j`-invariant `1728` and the sextic twists of a curve
  with `j`-invariant `0` are twists of it.
* `WeierstrassCurve.exists_smul_eq_quarticTwist_of_isTwist` and
  `WeierstrassCurve.exists_smul_eq_sexticTwist_of_isTwist`: conversely, every twist of such a curve
  is isomorphic over `K` to one of them.
* `WeierstrassCurve.exists_smul_quarticTwist_eq_quarticTwist_iff` and
  `WeierstrassCurve.exists_smul_sexticTwist_eq_sexticTwist_iff`: two of them are isomorphic over
  `K` exactly when the ratio of their parameters is a fourth, respectively sixth, power.
-/

namespace WeierstrassCurve

variable {K : Type*} [Field K] {W W' : WeierstrassCurve K} {D D' : K}

variable (W D) in
/-- The **quartic twist** (LMFDB `ec.twists`) of a Weierstrass curve `W` by `D`: the curve
`y² = x³ - 27 c₄ D x`. Over a field of characteristic not `2` or `3`, the curve
`y² = x³ - 27 c₄ x - 54 c₆` is a model of `W`, so when `j(W) = 1728`, that is `c₆ = 0`, the quartic
twist by `1` is a model of `W`. The quartic twists of such a `W` by `D ≠ 0` are then its twists,
parametrised by `K*/(K*)⁴` (`exists_smul_quarticTwist_eq_quarticTwist_iff`). -/
def quarticTwist : WeierstrassCurve K :=
  ⟨0, 0, 0, -27 * W.c₄ * D, 0⟩

variable (W D) in
/-- The **sextic twist** (LMFDB `ec.twists`) of a Weierstrass curve `W` by `D`: the curve
`y² = x³ - 54 c₆ D`. Over a field of characteristic not `2` or `3`, the curve
`y² = x³ - 27 c₄ x - 54 c₆` is a model of `W`, so when `j(W) = 0`, that is `c₄ = 0`, the sextic
twist by `1` is a model of `W`. The sextic twists of such a `W` by `D ≠ 0` are then its twists,
parametrised by `K*/(K*)⁶` (`exists_smul_sexticTwist_eq_sexticTwist_iff`). -/
def sexticTwist : WeierstrassCurve K :=
  ⟨0, 0, 0, 0, -54 * W.c₆ * D⟩

instance : (W.quarticTwist D).IsShortNF :=
  ⟨rfl, rfl, rfl⟩

instance : (W.sexticTwist D).IsShortNF :=
  ⟨rfl, rfl, rfl⟩

lemma c₆_quarticTwist : (W.quarticTwist D).c₆ = 0 := by
  rw [c₆_of_isShortNF, quarticTwist, mul_zero]

lemma Δ_quarticTwist : (W.quarticTwist D).Δ = -2 ^ 6 * (-27 * W.c₄ * D) ^ 3 := by
  rw [Δ_of_isShortNF, quarticTwist]
  ring1

lemma c₄_sexticTwist : (W.sexticTwist D).c₄ = 0 := by
  rw [c₄_of_isShortNF, sexticTwist, mul_zero]

lemma Δ_sexticTwist : (W.sexticTwist D).Δ = -(2 ^ 4 * 3 ^ 3) * (-54 * W.c₆ * D) ^ 2 := by
  rw [Δ_of_isShortNF, sexticTwist]
  ring1

variable [NeZero (2 : K)] [NeZero (3 : K)]

variable (W) in
lemma exists_smul_eq_short : ∃ C : VariableChange K, C • W = ⟨0, 0, 0, -27 * W.c₄, -54 * W.c₆⟩ := by
  have h6 : (6 : K) ≠ 0 := by
    rw [show (6 : K) = 2 * 3 by norm_num]
    exact mul_ne_zero two_ne_zero three_ne_zero
  have h12 : (12 : K) ≠ 0 := by
    rw [show (12 : K) = 2 * 6 by norm_num]
    exact mul_ne_zero two_ne_zero h6
  have h24 : (24 : K) ≠ 0 := by
    rw [show (24 : K) = 2 * 12 by norm_num]
    exact mul_ne_zero two_ne_zero h12
  refine ⟨⟨(Units.mk0 6 h6)⁻¹, -W.b₂ / 12, -W.a₁ / 2, W.a₁ * W.b₂ / 24 - W.a₃ / 2⟩, ?_⟩
  ext <;> simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, inv_inv, Units.val_mk0, c₄, c₆, b₂, b₄, b₆] <;> field_simp <;> ring1

lemma exists_smul_short_eq_short_iff {a b a' b' : K} :
    (∃ C : VariableChange K, C • (⟨0, 0, 0, a, b⟩ : WeierstrassCurve K) = ⟨0, 0, 0, a', b'⟩) ↔
    ∃ u : K, u ≠ 0 ∧ a' = u ^ 4 * a ∧ b' = u ^ 6 * b := by
  refine ⟨fun ⟨C, hC⟩ ↦ ?_, fun ⟨u, hu, ha, hb⟩ ↦ ⟨⟨(Units.mk0 u hu)⁻¹, 0, 0, 0⟩, ?_⟩⟩
  · have h₁ : C.u⁻¹ * (2 * C.s) = 0 := by simpa [variableChange_a₁] using congrArg a₁ hC
    have hs : C.s = 0 := by simpa [two_ne_zero] using h₁
    have h₂ : C.u⁻¹ ^ 2 * (3 * C.r) = 0 := by simpa [variableChange_a₂, hs] using congrArg a₂ hC
    have hr : C.r = 0 := by simpa [three_ne_zero] using h₂
    have h₃ : C.u⁻¹ ^ 3 * (2 * C.t) = 0 := by simpa [variableChange_a₃] using congrArg a₃ hC
    have ht : C.t = 0 := by simpa [two_ne_zero] using h₃
    exact ⟨C.u⁻¹, inv_ne_zero C.u.ne_zero,
      by simpa [variableChange_a₄, hr, ht] using (congrArg a₄ hC).symm,
      by simpa [variableChange_a₆, hr, ht] using (congrArg a₆ hC).symm⟩
  · ext <;> simp [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
      variableChange_a₆, ha, hb]

private lemma ne_zero_1728 : (1728 : K) ≠ 0 := by
  rw [show (1728 : K) = 2 ^ 6 * 3 ^ 3 by norm_num]
  exact mul_ne_zero (pow_ne_zero 6 two_ne_zero) (pow_ne_zero 3 three_ne_zero)

omit [NeZero (2 : K)] in
private lemma ne_zero_27 : (27 : K) ≠ 0 := by
  rw [show (27 : K) = 3 ^ 3 by norm_num]
  exact pow_ne_zero 3 three_ne_zero

private lemma ne_zero_54 : (54 : K) ≠ 0 := by
  rw [show (54 : K) = 2 * 27 by norm_num]
  exact mul_ne_zero two_ne_zero ne_zero_27

variable [W.IsElliptic] [W'.IsElliptic] (h₁₇₂₈ : W.j = 1728) (h₀ : W.j = 0) (hD : D ≠ 0)
  (h : W.IsTwist W')

/-! ### Quartic twists -/

include h₁₇₂₈ in
private lemma c₄_ne_zero_of_j_eq_1728 : W.c₄ ≠ 0 :=
  fun h ↦ ne_zero_1728 <| h₁₇₂₈.symm.trans <| W.j_eq_zero_iff.mpr h

include h₁₇₂₈ hD in
lemma isElliptic_quarticTwist : (W.quarticTwist D).IsElliptic := by
  rw [isElliptic_iff, isUnit_iff_ne_zero, Δ_quarticTwist]
  exact mul_ne_zero (neg_ne_zero.mpr <| pow_ne_zero 6 two_ne_zero) <| pow_ne_zero 3 <|
    mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr ne_zero_27) (c₄_ne_zero_of_j_eq_1728 h₁₇₂₈)) hD

include h₁₇₂₈ hD in
/-- **The quartic twists of a curve with `j`-invariant `1728` are twists of it**: they are elliptic
with `j`-invariant `1728`. -/
lemma isTwist_quarticTwist : W.IsTwist (W.quarticTwist D) := by
  have : (W.quarticTwist D).IsElliptic := isElliptic_quarticTwist h₁₇₂₈ hD
  rw [isTwist_iff_j_eq, h₁₇₂₈, eq_comm, j_eq_1728_iff, c₆_quarticTwist]

include h₁₇₂₈ h in
/-- **Every twist of a curve with `j`-invariant `1728` is isomorphic to one of its quartic
twists**: a twist `W'` has `j`-invariant `1728`, so `c₆(W') = 0` and `W'` has the model
`y² = x³ - 27 c₄(W') x`, the quartic twist of `W` by `c₄(W') / c₄(W)`. -/
lemma exists_smul_eq_quarticTwist_of_isTwist :
    ∃ D : K, D ≠ 0 ∧ ∃ C : VariableChange K, C • W' = W.quarticTwist D := by
  have hW' : W'.j = 1728 := (isTwist_iff_j_eq.mp h).symm.trans h₁₇₂₈
  have hc₄ : W.c₄ ≠ 0 := c₄_ne_zero_of_j_eq_1728 h₁₇₂₈
  rcases W'.exists_smul_eq_short with ⟨C, hC⟩
  refine ⟨W'.c₄ / W.c₄, div_ne_zero (c₄_ne_zero_of_j_eq_1728 hW') hc₄, C, ?_⟩
  rw [hC, W'.j_eq_1728_iff.mp hW', quarticTwist, mul_zero, mul_assoc, mul_div_cancel₀ _ hc₄]

include h₁₇₂₈ in
/-- **Two quartic twists of a curve with `j`-invariant `1728` are isomorphic exactly when the ratio
of their parameters is a fourth power**, so that the twists are parametrised by `K*/(K*)⁴`. -/
lemma exists_smul_quarticTwist_eq_quarticTwist_iff :
    (∃ C : VariableChange K, C • W.quarticTwist D = W.quarticTwist D') ↔ ∃ u : K, u ≠ 0 ∧
    D' = u ^ 4 * D := by
  rw [quarticTwist, quarticTwist, exists_smul_short_eq_short_iff]
  refine exists_congr fun u ↦ and_congr_right fun _ ↦ ?_
  rw [mul_zero, and_iff_left rfl, mul_left_comm, mul_right_inj' <|
    mul_ne_zero (neg_ne_zero.mpr ne_zero_27) (c₄_ne_zero_of_j_eq_1728 h₁₇₂₈)]

/-! ### Sextic twists -/

include h₀ in
private lemma c₆_ne_zero_of_j_eq_zero : W.c₆ ≠ 0 :=
  fun h ↦ ne_zero_1728 <| (W.j_eq_1728_iff.mpr h).symm.trans h₀

include h₀ hD in
lemma isElliptic_sexticTwist : (W.sexticTwist D).IsElliptic := by
  rw [isElliptic_iff, isUnit_iff_ne_zero, Δ_sexticTwist]
  exact mul_ne_zero (neg_ne_zero.mpr <| mul_ne_zero (pow_ne_zero 4 two_ne_zero)
    (pow_ne_zero 3 three_ne_zero)) <| pow_ne_zero 2 <|
    mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr ne_zero_54) (c₆_ne_zero_of_j_eq_zero h₀)) hD

include h₀ hD in
/-- **The sextic twists of a curve with `j`-invariant `0` are twists of it**: they are elliptic
with `j`-invariant `0`. -/
lemma isTwist_sexticTwist : W.IsTwist (W.sexticTwist D) := by
  have : (W.sexticTwist D).IsElliptic := isElliptic_sexticTwist h₀ hD
  rw [isTwist_iff_j_eq, h₀, eq_comm, j_eq_zero_iff, c₄_sexticTwist]

include h₀ h in
/-- **Every twist of a curve with `j`-invariant `0` is isomorphic to one of its sextic twists**: a
twist `W'` has `j`-invariant `0`, so `c₄(W') = 0` and `W'` has the model `y² = x³ - 54 c₆(W')`,
the sextic twist of `W` by `c₆(W') / c₆(W)`. -/
lemma exists_smul_eq_sexticTwist_of_isTwist :
    ∃ D : K, D ≠ 0 ∧ ∃ C : VariableChange K, C • W' = W.sexticTwist D := by
  have hW' : W'.j = 0 := (isTwist_iff_j_eq.mp h).symm.trans h₀
  have hc₆ : W.c₆ ≠ 0 := c₆_ne_zero_of_j_eq_zero h₀
  rcases W'.exists_smul_eq_short with ⟨C, hC⟩
  refine ⟨W'.c₆ / W.c₆, div_ne_zero (c₆_ne_zero_of_j_eq_zero hW') hc₆, C, ?_⟩
  rw [hC, W'.j_eq_zero_iff.mp hW', sexticTwist, mul_zero, mul_assoc, mul_div_cancel₀ _ hc₆]

include h₀ in
/-- **Two sextic twists of a curve with `j`-invariant `0` are isomorphic exactly when the ratio of
their parameters is a sixth power**, so that the twists are parametrised by `K*/(K*)⁶`. -/
lemma exists_smul_sexticTwist_eq_sexticTwist_iff :
    (∃ C : VariableChange K, C • W.sexticTwist D = W.sexticTwist D') ↔ ∃ u : K, u ≠ 0 ∧
    D' = u ^ 6 * D := by
  rw [sexticTwist, sexticTwist, exists_smul_short_eq_short_iff]
  refine exists_congr fun u ↦ and_congr_right fun _ ↦ ?_
  rw [mul_zero, and_iff_right rfl, mul_left_comm, mul_right_inj' <|
    mul_ne_zero (neg_ne_zero.mpr ne_zero_54) (c₆_ne_zero_of_j_eq_zero h₀)]

end WeierstrassCurve
