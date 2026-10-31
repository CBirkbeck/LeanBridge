import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParamodularNonliftNewform

/-!
# Paramodular newforms of level one

In level `1` there is no lower level, so every function is not obtained from a lower level, and
the Gritsenko lifts of level `1` are the Maass lifts of the Jacobi cusp forms of index `1`
(`SiegelUpperHalfSpace.maassLift_eq_gritsenkoLift`). So the paramodular newforms of level `1` in
the sense of the LMFDB knowl `mf.siegel.newform.paramodular` are the Hecke eigenforms on
`K(1) = Sp(4, ℤ)` that are not Maass lifts of Jacobi cusp forms, that is, not Saito–Kurokawa
lifts.

## Main results

* `SiegelUpperHalfSpace.isNotFromLowerLevel_one`: in level `1`, no function is obtained from a
  lower level.
* `SiegelUpperHalfSpace.isGritsenkoLift_one_iff`: the Gritsenko lifts of level `1` are the Maass
  lifts of the Jacobi cusp forms of index `1`.
* `SiegelUpperHalfSpace.isParamodularNonliftNewform_one_iff` (LMFDB
  `mf.siegel.newform.paramodular`): the paramodular newforms of level `1` are the Hecke eigenforms
  that are not Maass lifts of Jacobi cusp forms.
-/

open ModularForm

namespace SiegelUpperHalfSpace

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) ℂ) V)
    (f : SiegelUpperHalfSpace (Fin 2) → V)

private lemma not_prime_of_mul_eq_one {M p : ℕ+} (h : M * p = 1) : ¬(p : ℕ).Prime := fun hp ↦
  hp.ne_one <| Nat.eq_one_of_mul_eq_one_left (m := (M : ℕ)) (by exact_mod_cast congrArg PNat.val h)

/-- **In level `1` no function is obtained from a lower level**, no prime dividing `1`. -/
lemma isNotFromLowerLevel_one : IsNotFromLowerLevel ρ 1 f :=
  ⟨fun _ hp _ hM ↦ absurd hp (not_prime_of_mul_eq_one hM),
    fun _ hp _ hM ↦ absurd hp (not_prime_of_mul_eq_one hM)⟩

variable (k : ℤ) (F : SiegelUpperHalfSpace (Fin 2) → ℂ)

/-- **The Gritsenko lifts of level `1` are the Maass lifts of the Jacobi cusp forms of index `1`**
(`SiegelUpperHalfSpace.maassLift_eq_gritsenkoLift`). -/
lemma isGritsenkoLift_one_iff :
    IsGritsenkoLift k 1 F ↔ ∃ φ ∈ jacobiCuspFormSpace k 1, F = maassLift k φ :=
  exists_congr fun _ ↦ and_congr_right fun hφ ↦ by
    rw [maassLift_eq_gritsenkoLift hφ]
    rfl

variable {k} in
/-- **The paramodular newforms of level `1`** (LMFDB `mf.siegel.newform.paramodular`) are the
Hecke eigenforms of weight `k` on `K(1) = Sp(4, ℤ)` that are not Maass lifts of Jacobi cusp forms of
index `1`, that is, not Saito–Kurokawa lifts: in level `1` there is no lower level. -/
lemma isParamodularNonliftNewform_one_iff (G : slashInvariantsOf (TauCeti.detPowerRep ℂ 2 k)
    (heckeMonoidOf (paramodularLevel 1)) (heckeGammaOf (paramodularLevel 1))) :
    IsParamodularNonliftNewform k 1 G ↔ IsHeckeEigenform (TauCeti.detPowerRep ℂ 2 k) G ∧
      ¬∃ φ ∈ jacobiCuspFormSpace k 1, (G : SiegelUpperHalfSpace (Fin 2) → ℂ) = maassLift k φ := by
  rw [IsParamodularNonliftNewform, isGritsenkoLift_one_iff,
    and_iff_left (isNotFromLowerLevel_one _ _)]

end SiegelUpperHalfSpace
