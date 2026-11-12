import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.EverywhereGoodReduction
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Arithmetic.SzpiroRatio
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.ModifiedSzpiroAbc

/-!
# The Szpiro conjectures as finiteness statements

LMFDB `ec.q.szpiro_ratio` states the modified Szpiro conjecture as a finiteness statement: for every
`ε > 0`, only finitely many elliptic curves over `ℚ`, up to isomorphism, have modified Szpiro ratio
`σₘ = log max (|c₄|³, c₆²) / log N` (`WeierstrassCurve.algorithmicModifiedSzpiroRatio`) greater than
`6 + ε`. The isomorphism classes are the orbits of the changes of variables. Tau Ceti states the
conjecture as a bound, `max (|c₄|³, c₆²) ≤ C N ^ (6 + ε)`
(`TauCeti.AlgorithmicModifiedSzpiroConjecture`). This file proves that the two forms are equivalent,
so that, by LeanBridge's `TauCeti.abcConjecture_iff_algorithmicModifiedSzpiroConjecture`, the
finiteness form is equivalent to the abc conjecture, as Oesterlé proves (LMFDB `ec.q.szpiro_ratio`
and `ec.q.abc_quality`).

A bound with constant `C` at the exponent `6 + ε / 2` leaves as curves of ratio above `6 + ε` only
curves with `N ^ (ε / 2) < C`, whose invariants `c₄` and `c₆` are then bounded. The reduced minimal
model is determined by `a₁, a₂, a₃ ∈ {-1, 0, 1}` and by `c₄` and `c₆`, which are integers, so these
curves have finitely many reduced minimal models, hence lie in finitely many isomorphism classes.
Conversely, as `N > 1` (`WeierstrassCurve.one_lt_absNorm_algorithmicConductor`), a curve of ratio
`σₘ ≤ 6 + ε` has `max (|c₄|³, c₆²) = N ^ σₘ ≤ N ^ (6 + ε)`, and the largest `max (|c₄|³, c₆²)` among
the finitely many reduced minimal models of the other curves is a constant.

The knowl's other conjecture, that only finitely many curves have Szpiro ratio
`log |Δ_min| / log N` (`WeierstrassCurve.algorithmicSzpiroRatio`) greater than `6 + ε`, follows from
the modified one, since that ratio is at most `σₘ`.

## Main definitions

* `TauCeti.AlgorithmicModifiedSzpiroRatioConjecture` (LMFDB `ec.q.szpiro_ratio`): the modified
  Szpiro conjecture, as finitely many isomorphism classes of modified Szpiro ratio above `6 + ε`.
* `TauCeti.AlgorithmicSzpiroRatioConjecture` (LMFDB `ec.q.szpiro_ratio`): Szpiro's conjecture, as
  finitely many isomorphism classes of Szpiro ratio above `6 + ε`.

## Main results

* `WeierstrassCurve.finite_image_mk_orbitRel_iff`: a set of elliptic curves over `ℚ` meets finitely
  many isomorphism classes exactly when its curves have finitely many reduced minimal models.
* `TauCeti.algorithmicModifiedSzpiroConjecture_iff_algorithmicModifiedSzpiroRatioConjecture` (LMFDB
  `ec.q.szpiro_ratio`): the bound form and the finiteness form of the modified Szpiro conjecture are
  equivalent.
* `TauCeti.abcConjecture_iff_algorithmicModifiedSzpiroRatioConjecture` (LMFDB `ec.q.szpiro_ratio`,
  `ec.q.abc_quality`): the abc conjecture is equivalent to the finiteness form (Oesterlé).
* `TauCeti.AlgorithmicModifiedSzpiroRatioConjecture.algorithmicSzpiroRatioConjecture` (LMFDB
  `ec.q.szpiro_ratio`): the modified Szpiro conjecture implies Szpiro's conjecture, in finiteness
  form.

## References

* J. Oesterlé, *Nouvelles approches du « théorème » de Fermat*, Séminaire Bourbaki 694 (1988),
  Astérisque 161–162 (1988), 165–186.
-/

open MulAction WeierstrassCurve

namespace WeierstrassCurve

/-- **Finitely many isomorphism classes are finitely many reduced minimal models**: the elliptic
curves over `ℚ` with a property `P` meet finitely many orbits of the changes of variables exactly
when their reduced minimal models are finitely many, as the reduced minimal model of a curve
determines its orbit. -/
lemma finite_image_mk_orbitRel_iff {P : ∀ E : WeierstrassCurve ℚ, [E.IsElliptic] → Prop} :
    (Quotient.mk (orbitRel (VariableChange ℚ) (WeierstrassCurve ℚ)) '' {E | ∃ _ : E.IsElliptic,
      P E}).Finite ↔ {W | ∃ (E : WeierstrassCurve ℚ) (_ : E.IsElliptic), P E ∧
        reducedMinimalModel E = W}.Finite := by
  have hmk (E : WeierstrassCurve ℚ) [E.IsElliptic] : Quotient.mk (orbitRel (VariableChange ℚ) _)
      (reducedMinimalModel E) = Quotient.mk _ E := by
    rcases exists_smul_eq_reducedMinimalModel E with ⟨C, hC⟩
    exact Quotient.sound ⟨C, hC⟩
  refine ⟨fun h ↦ Set.Finite.of_finite_image (f := Quotient.mk (orbitRel (VariableChange ℚ) _))
    (h.subset ?_) ?_, fun h ↦ (h.image (Quotient.mk _)).subset ?_⟩
  · rintro _ ⟨_, ⟨E, _, hE, rfl⟩, rfl⟩
    exact ⟨E, ⟨inferInstance, hE⟩, (hmk E).symm⟩
  · rintro _ ⟨E, _, -, rfl⟩ _ ⟨E', _, -, rfl⟩ h
    rcases Quotient.exact h with ⟨C, hC⟩
    exact ((isReducedMinimal_reducedMinimalModel E').eq_of_smul_eq
      (isReducedMinimal_reducedMinimalModel E) C hC).symm
  · rintro _ ⟨E, ⟨_, hE⟩, rfl⟩
    exact ⟨reducedMinimalModel E, ⟨E, inferInstance, hE, rfl⟩, hmk E⟩

end WeierstrassCurve

namespace TauCeti

/-- **The modified Szpiro conjecture** in the form of LMFDB `ec.q.szpiro_ratio`, against the
algorithmic conductor: for every `ε > 0`, only finitely many elliptic curves over `ℚ`, up to
isomorphism, have modified Szpiro ratio `log max (|c₄|³, c₆²) / log N` greater than `6 + ε`. The
isomorphism classes are the orbits of the changes of variables. It is equivalent to Tau Ceti's
bound form `TauCeti.AlgorithmicModifiedSzpiroConjecture`
(`TauCeti.algorithmicModifiedSzpiroConjecture_iff_algorithmicModifiedSzpiroRatioConjecture`). -/
def AlgorithmicModifiedSzpiroRatioConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → (Quotient.mk (orbitRel (VariableChange ℚ) (WeierstrassCurve ℚ)) ''
    {E : WeierstrassCurve ℚ | ∃ _ : E.IsElliptic, 6 + ε < E.algorithmicModifiedSzpiroRatio}).Finite

/-- **Szpiro's conjecture** in the form of LMFDB `ec.q.szpiro_ratio`, against the algorithmic
conductor: for every `ε > 0`, only finitely many elliptic curves over `ℚ`, up to isomorphism, have
Szpiro ratio `log |Δ_min| / log N` greater than `6 + ε`. The ratio is defined since `N > 1`
(`WeierstrassCurve.one_lt_absNorm_algorithmicConductor`). -/
def AlgorithmicSzpiroRatioConjecture : Prop :=
  ∀ ε : ℝ, 0 < ε → (Quotient.mk (orbitRel (VariableChange ℚ) (WeierstrassCurve ℚ)) ''
    {E : WeierstrassCurve ℚ | ∃ _ : E.IsElliptic,
      6 + ε < E.algorithmicSzpiroRatio (one_lt_absNorm_algorithmicConductor E)}).Finite

private lemma le_mul_rpow_of_rpow_lt_of_le_mul_rpow {N M C ε : ℝ} (hN : 1 < N) (hε : 0 < ε)
    (hlt : N ^ (6 + ε) < M) (hle : M ≤ C * N ^ (6 + ε / 2)) : M ≤ C * C ^ ((12 + ε) / ε) := by
  have hN₀ : 0 < N := zero_lt_one.trans hN
  have hmul : N ^ (6 + ε / 2) * N ^ (ε / 2) < N ^ (6 + ε / 2) * C := by
    rw [← Real.rpow_add hN₀, mul_comm _ C, show 6 + ε / 2 + ε / 2 = 6 + ε by ring1]
    exact hlt.trans_le hle
  have hNC : N ^ (ε / 2) < C := lt_of_mul_lt_mul_left hmul (Real.rpow_nonneg hN₀.le _)
  have he : 6 + ε / 2 = ε / 2 * ((12 + ε) / ε) := by
    field_simp
    ring1
  have hpow : N ^ (6 + ε / 2) ≤ C ^ ((12 + ε) / ε) := by
    rw [he, Real.rpow_mul hN₀.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hN₀.le _) hNC.le (by positivity)
  exact hle.trans (mul_le_mul_of_nonneg_left hpow ((Real.rpow_nonneg hN₀.le _).trans hNC.le))

/-- **The two forms of the modified Szpiro conjecture are equivalent**: Tau Ceti's bound
`max (|c₄|³, c₆²) ≤ C N ^ (6 + ε)` and the finiteness of the isomorphism classes of modified Szpiro
ratio above `6 + ε` of LMFDB `ec.q.szpiro_ratio`. A bound at `6 + ε / 2` bounds `N`, hence `c₄` and
`c₆`, on the curves of ratio above `6 + ε`; conversely the largest `max (|c₄|³, c₆²)` among the
finitely many exceptions is a constant. -/
lemma algorithmicModifiedSzpiroConjecture_iff_algorithmicModifiedSzpiroRatioConjecture :
    AlgorithmicModifiedSzpiroConjecture ↔ AlgorithmicModifiedSzpiroRatioConjecture := by
  refine ⟨fun h ε hε ↦ ?_, fun h ↦ algorithmicModifiedSzpiroConjecture_iff.mpr fun ε hε ↦ ?_⟩
  · rcases algorithmicModifiedSzpiroConjecture_iff.mp h (ε / 2) (by positivity) with ⟨C, hC⟩
    have hK : C * C ^ ((12 + ε) / ε) ≤ ⌈C * C ^ ((12 + ε) / ε)⌉₊ := Nat.le_ceil _
    generalize ⌈C * C ^ ((12 + ε) / ε)⌉₊ = K at hK
    -- an integer whose absolute value has a power at most `K` lies in `[-K, K]`
    have hmem (n : ℤ) (k : ℕ) (hk : k ≠ 0) (hn : |(n : ℝ)| ^ k ≤ K) : n ∈ Set.Icc (-(K : ℤ)) K := by
      have h1 : |(n : ℝ)| ≤ |(n : ℝ)| ^ k := by
        rcases eq_or_ne n 0 with rfl | hn0
        · simp
        · exact le_self_pow₀ (by exact_mod_cast Int.one_le_abs hn0) hk
      exact abs_le.mp (by exact_mod_cast h1.trans hn)
    -- a curve is determined by `a₁`, `a₂`, `a₃`, `c₄` and `c₆`
    have hinj : Function.Injective fun W : WeierstrassCurve ℚ ↦ (W.a₁, W.a₂, W.a₃, W.c₄, W.c₆) := by
      intro W W' h
      simp only [Prod.mk.injEq] at h
      rcases h with ⟨h₁, h₂, h₃, h₄, h₆⟩
      have ha₄ : W.a₄ = W'.a₄ := by
        simp only [c₄, b₂, b₄, h₁, h₂, h₃] at h₄
        linarith
      have ha₆ : W.a₆ = W'.a₆ := by
        simp only [c₆, b₂, b₄, b₆, h₁, h₂, h₃, ha₄] at h₆
        linarith
      exact WeierstrassCurve.ext h₁ h₂ h₃ ha₄ ha₆
    have hI : (Int.cast '' Set.Icc (-(K : ℤ)) K : Set ℚ).Finite := (Set.finite_Icc _ _).image _
    refine finite_image_mk_orbitRel_iff.mpr <| (((Set.toFinite ({0, 1} : Set ℚ)).prod
      ((Set.toFinite ({-1, 0, 1} : Set ℚ)).prod ((Set.toFinite ({0, 1} : Set ℚ)).prod
        (hI.prod hI)))).preimage hinj.injOn).subset ?_
    rintro _ ⟨E, _, hE, rfl⟩
    -- on the curves of ratio above `6 + ε`, `N ^ (ε / 2) < C`, so `max (|c₄|³, c₆²) ≤ K`
    have hN : (1 : ℝ) < Ideal.absNorm (algorithmicConductor ℤ E) :=
      mod_cast one_lt_absNorm_algorithmicConductor E
    have hM : max (|((reducedMinimalModel E).c₄ : ℝ)| ^ 3) (((reducedMinimalModel E).c₆ : ℝ) ^ 2) ≤
        K := by
      refine (le_mul_rpow_of_rpow_lt_of_le_mul_rpow hN hε ?_ (hC E)).trans hK
      rw [← E.rpow_algorithmicModifiedSzpiroRatio (one_lt_absNorm_algorithmicConductor E)]
      exact Real.rpow_lt_rpow_of_exponent_lt hN hE
    rcases isReducedMinimal_iff.mp (isReducedMinimal_reducedMinimalModel E) with ⟨hmin, h₁, h₂, h₃⟩
    have : IsIntegral ℤ (reducedMinimalModel E) := hmin.isIntegral
    have hW₀ : (integralModel ℤ (reducedMinimalModel E)).baseChange ℚ = reducedMinimalModel E :=
      baseChange_integralModel_eq ℤ _
    generalize integralModel ℤ (reducedMinimalModel E) = W₀ at hW₀
    have hc₄ : (reducedMinimalModel E).c₄ = (W₀.c₄ : ℚ) := by
      rw [← algebraMap_c₄_of_baseChange_eq hW₀, algebraMap_int_eq, eq_intCast]
    have hc₆ : (reducedMinimalModel E).c₆ = (W₀.c₆ : ℚ) := by
      rw [← algebraMap_c₆_of_baseChange_eq hW₀, algebraMap_int_eq, eq_intCast]
    rw [hc₄, hc₆, Rat.cast_intCast, Rat.cast_intCast, ← sq_abs] at hM
    exact ⟨h₁, h₂, h₃, ⟨_, hmem _ 3 (by norm_num) ((le_max_left _ _).trans hM), hc₄.symm⟩,
      ⟨_, hmem _ 2 (by norm_num) ((le_max_right _ _).trans hM), hc₆.symm⟩⟩
  · -- the largest `max (|c₄|³, c₆²)` among the finitely many exceptions is a constant
    rcases ((finite_image_mk_orbitRel_iff.mp (h ε hε)).image
      fun W : WeierstrassCurve ℚ ↦ max (|(W.c₄ : ℝ)| ^ 3) ((W.c₆ : ℝ) ^ 2)).bddAbove with ⟨B, hB⟩
    refine ⟨max B 1, fun E _ ↦ ?_⟩
    have hN : (1 : ℝ) < Ideal.absNorm (algorithmicConductor ℤ E) :=
      mod_cast one_lt_absNorm_algorithmicConductor E
    have hN1 : (1 : ℝ) ≤ (Ideal.absNorm (algorithmicConductor ℤ E) : ℝ) ^ (6 + ε) :=
      Real.one_le_rpow hN.le (by positivity)
    by_cases hE : 6 + ε < E.algorithmicModifiedSzpiroRatio
    · exact (hB ⟨reducedMinimalModel E, ⟨E, inferInstance, hE, rfl⟩, rfl⟩).trans <|
        (le_max_left B 1).trans (le_mul_of_one_le_right (zero_le_one.trans (le_max_right B 1)) hN1)
    · rw [← E.rpow_algorithmicModifiedSzpiroRatio (one_lt_absNorm_algorithmicConductor E)]
      exact (Real.rpow_le_rpow_of_exponent_le hN.le (not_lt.mp hE)).trans
        (le_mul_of_one_le_left (zero_le_one.trans hN1) (le_max_right B 1))

/-- **The abc conjecture is equivalent to the modified Szpiro conjecture in finiteness form**
(Oesterlé; LMFDB `ec.q.szpiro_ratio` and `ec.q.abc_quality`): for every `ε > 0`, only finitely many
elliptic curves over `ℚ`, up to isomorphism, have modified Szpiro ratio greater than `6 + ε`. -/
lemma abcConjecture_iff_algorithmicModifiedSzpiroRatioConjecture :
    AbcConjecture ↔ AlgorithmicModifiedSzpiroRatioConjecture :=
  abcConjecture_iff_algorithmicModifiedSzpiroConjecture.trans
    algorithmicModifiedSzpiroConjecture_iff_algorithmicModifiedSzpiroRatioConjecture

/-- **The modified Szpiro conjecture implies Szpiro's conjecture**, in the finiteness forms of LMFDB
`ec.q.szpiro_ratio`, since the Szpiro ratio `log |Δ_min| / log N` is at most the modified one. -/
lemma AlgorithmicModifiedSzpiroRatioConjecture.algorithmicSzpiroRatioConjecture
    (h : AlgorithmicModifiedSzpiroRatioConjecture) : AlgorithmicSzpiroRatioConjecture :=
  fun ε hε ↦ (h ε hε).subset <| Set.image_mono fun E ⟨hE', hE⟩ ↦
    ⟨hE', hE.trans_le (E.algorithmicSzpiroRatio_le_algorithmicModifiedSzpiroRatio _)⟩

end TauCeti
