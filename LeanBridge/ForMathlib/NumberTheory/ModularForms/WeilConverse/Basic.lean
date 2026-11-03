import LeanBridge.ForMathlib.NumberTheory.ModularForms.WeilConverse.Hecke
import LeanBridge.ForMathlib.NumberTheory.ModularForms.WeilConverse.ModerateGrowth
import LeanBridge.ForMathlib.NumberTheory.ModularForms.WeilConverse.Transformation
import LeanBridge.ForMathlib.NumberTheory.ModularForms.WeilConverse.Twist
import TauCeti.NumberTheory.ModularForms.DiamondOperators

/-!
# Weil's converse theorem

Let `N ≥ 1`, `k > 0` and let `χ` be a Dirichlet character modulo `N`. Let `a, b` be sequences of
polynomial growth, with constant terms `a₀, b₀`, and with completed Dirichlet series
`Λ_a(s) = (2π) ^ (-s) Γ(s) ∑ a n n ^ (-s)` and `Λ_b`. Suppose that `Λ_a` continues to
`E(s) - a₀ / s - i ^ k N ^ (-k / 2) b₀ / (k - s)`, with `E` entire and bounded on vertical strips,
with `Λ_a(s) = i ^ k N ^ (k / 2 - s) Λ_b(k - s)`, and that the same holds for the twists by every
nontrivial character `ψ` modulo every sufficiently large prime `r ∤ N`, which have no constant term,
with `Λ_{ψ a}(s) = i ^ k χ(r) ψ(N) τ(ψ) ^ 2 / r (N r²) ^ (k / 2 - s) Λ_{ψ⁻¹ b}(k - s)`. Then
`∑ a n e(n z)` is a modular form of weight `k`, level `N` and character `χ` (Weil, 1967). The form
obtained need not be a cusp form, even if `a₀ = b₀ = 0`, since these only control the cusps `∞` and
`0`. Conversely, every such form satisfies these hypotheses
(`ModularForm.hasWeilFunctionalEquations_qExpansion_coeff`).

## Main definitions

* `ModularForm.IsEntireCompletion`: an entire completion of a Dirichlet series.
* `ModularForm.HasFunctionalEquation`: the functional equation of two Dirichlet series.
* `ModularForm.modularFormOfNebentypus`: a holomorphic function of moderate growth with a nebentypus
  law, as a modular form.
* `ModularForm.HasWeilFunctionalEquations`: the hypotheses of Weil's converse theorem.
* `ModularForm.HasWeilFunctionalEquations.modularForm`: the modular form of the theorem.

## Main results

* `ModularForm.IsEntireCompletion.hasFunctionalEquation`: the functional equation of entire
  completions of two sequences without constant term.
* `ModularForm.hasTwistedTransformation_iff_expSum_slash_frickeGL`: the twisted transformation law
  as a Fricke law for the twists.
* `ModularForm.hasTwistedTransformation_of_hasFunctionalEquation`: the twisted transformation law
  from the functional equations.
* `ModularForm.expSum_slash_eq_smul_of_hasFunctionalEquation`: the transformation law on `Γ₀(N)`.
* `ModularForm.HasWeilFunctionalEquations.modularForm_mem`: **Weil's converse theorem**.

## References

* A. Weil, *Über die Bestimmung Dirichletscher Reihen durch Funktionalgleichungen*, Math. Ann. 168
  (1967), 149–156.
* T. Miyake, *Modular Forms*, Theorem 4.3.15.
* D. Bump, *Automorphic Forms and Representations*, Theorem 1.5.1.
* H. Iwaniec, *Topics in Classical Automorphic Forms*, Theorem 7.8.
-/

open Complex TauCeti CongruenceSubgroup

open scoped Real Manifold ModularForm MatrixGroups

open UpperHalfPlane hiding I I_re I_im

open Matrix GeneralLinearGroup SpecialLinearGroup

namespace ModularForm

/-- `Λ` is an **entire completion** of the Dirichlet series of `c`: an entire function, bounded on
vertical strips, that equals the completed Dirichlet series `(2π) ^ (-s) Γ(s) ∑ c n n ^ (-s)` on a
right half plane. -/
structure IsEntireCompletion (c : ℕ → ℂ) (Λ : ℂ → ℂ) : Prop where
  differentiable : Differentiable ℂ Λ
  exists_eq : ∃ σ₀ : ℝ, ∀ s : ℂ, σ₀ < s.re → Λ s = completedLSeries c s
  exists_bound : ∀ a b : ℝ, ∃ M : ℝ, ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖Λ s‖ ≤ M

/-- The sequences `a` and `b` satisfy the **functional equation** of weight `κ`, level `A` and sign
`ε`: the completed Dirichlet series of `a` continues to `Λ(s) = E(s) - a₀ / s - R / (κ - s)`, with
`E` entire and bounded on vertical strips and `R = ε A ^ (-κ / 2) b₀`, and
`Λ(s) = ε A ^ (κ / 2 - s) Λ'(κ - s)` on a left half plane, where `Λ'` is the completed Dirichlet
series of `b`. -/
def HasFunctionalEquation (a b : ℕ → ℂ) (κ : ℤ) (A : ℕ) (ε : ℂ) : Prop :=
  ∃ (E : ℂ → ℂ) (σ₀ : ℝ), Differentiable ℂ E ∧
    (∀ x y : ℝ, ∃ M : ℝ, ∀ s : ℂ, x ≤ s.re → s.re ≤ y → ‖E s‖ ≤ M) ∧
    (∀ s : ℂ, σ₀ < s.re →
      completedLSeries a s = addPoles E (a 0) (ε * (A : ℂ) ^ (-(κ : ℂ) / 2) * b 0) κ s) ∧
    ∀ s : ℂ, s.re < κ - σ₀ → addPoles E (a 0) (ε * (A : ℂ) ^ (-(κ : ℂ) / 2) * b 0) κ s =
      ε * (A : ℂ) ^ ((κ : ℂ) / 2 - s) * completedLSeries b (κ - s)

variable {a b : ℕ → ℂ} {k : ℤ} {N A : ℕ} {ε : ℂ} {χ : DirichletCharacter ℂ N} {r : ℕ} [Fact r.Prime]
    {ψ : DirichletCharacter ℂ r}

/-- **The functional equation of entire completions**: for sequences without constant term, entire
completions `Λ`, `Λ'` with `Λ(s) = ε A ^ (k / 2 - s) Λ'(k - s)` give the functional equation. -/
lemma IsEntireCompletion.hasFunctionalEquation {Λ Λ' : ℂ → ℂ} (h₁ : IsEntireCompletion a Λ)
    (h₂ : IsEntireCompletion b Λ') (ha : a 0 = 0) (hb : b 0 = 0)
    (hfe : ∀ s : ℂ, Λ s = ε * (A : ℂ) ^ ((k : ℂ) / 2 - s) * Λ' (k - s)) :
    HasFunctionalEquation a b k A ε := by
  rcases h₁.exists_eq with ⟨σ₁, hσ₁⟩
  rcases h₂.exists_eq with ⟨σ₂, hσ₂⟩
  have hadd : ∀ s : ℂ, addPoles Λ (a 0) (ε * (A : ℂ) ^ (-(k : ℂ) / 2) * b 0) k s = Λ s := fun s ↦ by
    simp [addPoles, ha, hb]
  refine ⟨Λ, max σ₁ σ₂, h₁.differentiable, h₁.exists_bound, fun s hs ↦ ?_, fun s hs ↦ ?_⟩
  · rw [hadd, hσ₁ s (lt_of_le_of_lt (le_max_left _ _) hs)]
  · rw [hadd, hfe, hσ₂]
    have h1 : σ₂ ≤ max σ₁ σ₂ := le_max_right _ _
    simp only [sub_re, intCast_re]
    linarith

variable [NeZero A] in
lemma HasFunctionalEquation.expSum_slash_frickeGL (h : HasFunctionalEquation a b k A ε) (hk : 0 < k)
    (ha : HasPolyGrowth a) (hb : HasPolyGrowth b) :
    expSum a ∣[k] frickeGL ℝ A = (ε * I ^ (-k) * (A : ℂ) ^ ((k : ℂ) / 2 - 1)) • expSum b := by
  rcases h with ⟨E, σ₀, hE, hbd, h₁, h₂⟩
  exact expSum_slash_frickeGL_eq_of_functional_equation ha hb hk hE hbd h₁ h₂

variable (k) in
private lemma cpow_mul_sq_eq : ((N * r ^ 2 : ℕ) : ℂ) ^ ((k : ℂ) / 2 - 1) =
    (N : ℂ) ^ ((k : ℂ) / 2 - 1) * ((r : ℝ) : ℂ) ^ (k - 2) := by
  have hr : ((r : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Nat.cast_ne_zero.mpr (NeZero.ne r))
  have hr2 : ((r ^ 2 : ℕ) : ℂ) = ((r : ℝ) : ℂ) ^ 2 := by
    push_cast
    rfl
  have h1 : ((r ^ 2 : ℕ) : ℂ) ^ ((k : ℂ) / 2 - 1) = ((r : ℝ) : ℂ) ^ (k - 2) := by
    have h2 : Real.sqrt ((r ^ 2 : ℕ) : ℝ) = (r : ℝ) := by
      push_cast
      exact Real.sqrt_sq (Nat.cast_nonneg r)
    rw [cpow_sub _ _ (by rw [hr2]; exact pow_ne_zero 2 hr), natCast_cpow_div_two_eq, h2, cpow_one,
      hr2, zpow_sub₀ hr]
    rfl
  rw [Nat.cast_mul, natCast_mul_natCast_cpow, h1]

variable [NeZero N]

variable (k χ) in
/-- **The twisted transformation law as a Fricke law for the twists.** If
`∑ a n e(n z) ∣[k] W_N = N ^ (k / 2 - 1) ∑ b n e(n z)`, the law `HasTwistedTransformation` at a
nontrivial character `ψ` modulo a prime `r` says that the twists `F_ψ` of `a` and `G_ψ̄` of `b`
satisfy `F_ψ ∣[k] W_{N r²} = χ(r) ψ(N) τ(ψ) ^ 2 / r (N r²) ^ (k / 2 - 1) G_ψ̄`. -/
lemma hasTwistedTransformation_iff_expSum_slash_frickeGL (ha : HasPolyGrowth a)
    (hb : HasPolyGrowth b)
    (hW : expSum a ∣[k] frickeGL ℝ N = (N : ℂ) ^ ((k : ℂ) / 2 - 1) • expSum b) (hψ : ψ ≠ 1) :
    HasTwistedTransformation χ k (expSum a) ψ ↔ expSum (twistSeq ψ a) ∣[k] frickeGL ℝ (N * r ^ 2) =
      (I ^ k * χ r * ψ N * gaussSum ψ ZMod.stdAddChar ^ 2 / r * I ^ (-k) *
        ((N * r ^ 2 : ℕ) : ℂ) ^ ((k : ℂ) / 2 - 1)) • expSum (twistSeq ψ⁻¹ b) := by
  have hI : I ^ k * I ^ (-k) = 1 := by
    rw [← zpow_add₀ I_ne_zero, add_neg_cancel, zpow_zero]
  have hr : (r : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne r)
  have hdet : ∀ x : ℝ, 0 < ((upperRightHom x : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det :=
    fun x ↦ by simp
  have hL : ∑ u : ZMod r, ψ⁻¹ u • expSum a ∣[k] (upperRightHom ((u.val : ℝ) / r) *
      frickeGL ℝ (N * r ^ 2)) =
        gaussSum ψ⁻¹ ZMod.stdAddChar • expSum (twistSeq ψ a) ∣[k] frickeGL ℝ (N * r ^ 2) := by
    rw [← smul_slash_of_det_pos k val_det_frickeGL_pos,
      ← sum_smul_expSum_slash_upperRightHom ha hψ, SlashAction.sum_slash]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [smul_slash_of_det_pos k val_det_frickeGL_pos, SlashAction.slash_mul]
  have hR : ∑ v : ZMod r, ψ v • (expSum a ∣[k] frickeGL ℝ N) ∣[k] upperRightHom ((v.val : ℝ) / r) =
      (N : ℂ) ^ ((k : ℂ) / 2 - 1) • gaussSum ψ ZMod.stdAddChar • expSum (twistSeq ψ⁻¹ b) := by
    have h1 : ∑ u : ZMod r, ψ⁻¹⁻¹ u • expSum b ∣[k] upperRightHom ((u.val : ℝ) / r) =
        gaussSum ψ⁻¹⁻¹ ZMod.stdAddChar • expSum (twistSeq ψ⁻¹ b) :=
      sum_smul_expSum_slash_upperRightHom hb (inv_ne_one.mpr hψ)
    rw [inv_inv] at h1
    rw [hW, ← h1, Finset.smul_sum]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    rw [smul_slash_of_det_pos k (hdet _), smul_comm]
  have hG : gaussSum ψ ZMod.stdAddChar * gaussSum ψ⁻¹ ZMod.stdAddChar = ψ (-1) * r :=
    gaussSum_mul_gaussSum_inv hψ
  have hτ : gaussSum ψ⁻¹ ZMod.stdAddChar ≠ 0 := right_ne_zero_of_mul <| by
    rw [hG]
    exact mul_ne_zero (IsUnit.map ψ isUnit_one.neg).ne_zero hr
  have hc : ((r : ℝ) : ℂ) ^ (k - 2) * χ r * ψ (-1) * ψ N * ((N : ℂ) ^ ((k : ℂ) / 2 - 1) *
      gaussSum ψ ZMod.stdAddChar) = gaussSum ψ⁻¹ ZMod.stdAddChar * (I ^ k * χ r * ψ N *
        gaussSum ψ ZMod.stdAddChar ^ 2 / r * I ^ (-k) *
          ((N * r ^ 2 : ℕ) : ℂ) ^ ((k : ℂ) / 2 - 1)) := by
    have e : gaussSum ψ⁻¹ ZMod.stdAddChar * (I ^ k * χ r * ψ N *
        gaussSum ψ ZMod.stdAddChar ^ 2 / r * I ^ (-k) *
          ((N : ℂ) ^ ((k : ℂ) / 2 - 1) * ((r : ℝ) : ℂ) ^ (k - 2))) =
            (I ^ k * I ^ (-k)) * χ r * ψ N * (gaussSum ψ ZMod.stdAddChar *
              gaussSum ψ⁻¹ ZMod.stdAddChar) * gaussSum ψ ZMod.stdAddChar *
                ((N : ℂ) ^ ((k : ℂ) / 2 - 1) * ((r : ℝ) : ℂ) ^ (k - 2)) / r := by
      ring1
    rw [cpow_mul_sq_eq, e, hI, hG]
    field_simp
  rw [HasTwistedTransformation, hL, hR]
  simp only [smul_smul]
  rw [hc, mul_smul, smul_right_inj hτ]

/-- **The twisted transformation law from the functional equations.** -/
lemma hasTwistedTransformation_of_hasFunctionalEquation (hk : 0 < k) (ha : HasPolyGrowth a)
    (hb : HasPolyGrowth b) (h₀ : HasFunctionalEquation a b k N (I ^ k)) (hψ : ψ ≠ 1)
    (h : HasFunctionalEquation (twistSeq ψ a) (twistSeq ψ⁻¹ b) k (N * r ^ 2)
      (I ^ k * χ r * ψ N * gaussSum ψ ZMod.stdAddChar ^ 2 / r)) :
    HasTwistedTransformation χ k (expSum a) ψ := by
  have hI : I ^ k * I ^ (-k) = 1 := by
    rw [← zpow_add₀ I_ne_zero, add_neg_cancel, zpow_zero]
  have hW : expSum a ∣[k] frickeGL ℝ N = (N : ℂ) ^ ((k : ℂ) / 2 - 1) • expSum b := by
    rw [h₀.expSum_slash_frickeGL hk ha hb, hI, one_mul]
  exact (hasTwistedTransformation_iff_expSum_slash_frickeGL k χ ha hb hW hψ).mpr
    (h.expSum_slash_frickeGL hk (ha.twistSeq ψ) (hb.twistSeq ψ⁻¹))

/-- **Weil's converse theorem: the transformation law.** Let `a, b` be sequences of polynomial
growth, `k > 0`, and `χ` a Dirichlet character modulo `N`. Suppose that their Dirichlet series
satisfy the functional equation `Λ_a(s) = i ^ k N ^ (k / 2 - s) Λ_b(k - s)`, and that for every
nontrivial character `ψ` modulo every prime `r > R` not dividing `N`, the twists satisfy
`Λ_{ψ a}(s) = i ^ k χ(r) ψ(N) τ(ψ) ^ 2 / r (N r²) ^ (k / 2 - s) Λ_{ψ⁻¹ b}(k - s)`. Then
`f = ∑ a n e(n z)` satisfies `f ∣[k] γ = χ(d) f` for every `γ = (a, b; c, d) ∈ Γ₀(N)`. -/
lemma expSum_slash_eq_smul_of_hasFunctionalEquation (hk : 0 < k) (ha : HasPolyGrowth a)
    (hb : HasPolyGrowth b) (h₀ : HasFunctionalEquation a b k N (I ^ k)) {R : ℕ}
    (h : ∀ (r : ℕ) [Fact r.Prime], R < r → ¬r ∣ N → ∀ ψ : DirichletCharacter ℂ r, ψ ≠ 1 →
      HasFunctionalEquation (twistSeq ψ a) (twistSeq ψ⁻¹ b) k (N * r ^ 2)
        (I ^ k * χ r * ψ N * gaussSum ψ ZMod.stdAddChar ^ 2 / r)) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gamma0 N) : expSum a ∣[k] γ = χ (γ 1 1 : ℤ) • expSum a := by
  have hI : I ^ k * I ^ (-k) = 1 := by
    rw [← zpow_add₀ I_ne_zero, add_neg_cancel, zpow_zero]
  have hW : expSum a ∣[k] frickeGL ℝ N = (N : ℂ) ^ ((k : ℂ) / 2 - 1) • expSum b := by
    rw [h₀.expSum_slash_frickeGL hk ha hb, hI, one_mul]
  have hdet : 0 < ((upperRightHom (1 : ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det := by
    simp
  have hg₁ :
      (expSum a ∣[k] frickeGL ℝ N) ∣[k] upperRightHom (1 : ℝ) = expSum a ∣[k] frickeGL ℝ N := by
    rw [hW, smul_slash_of_det_pos k hdet, expSum_slash_upperRightHom_one]
  exact slash_eq_smul_of_hasTwistedTransformation (mdifferentiable_expSum ha) hk
    expSum_slash_upperRightHom_one hg₁ (fun r _ hR hrN ψ hψ ↦
      hasTwistedTransformation_of_hasFunctionalEquation hk ha hb h₀ hψ (h r hR hrN ψ hψ)) hγ

variable {f : ℍ → ℂ}

variable (χ) in
/-- A holomorphic function on `ℍ` of moderate growth satisfying the nebentypus law of `χ` on `Γ₀(N)`
in weight `k > 0`, as a modular form for `Γ₁(N)`. -/
noncomputable def modularFormOfNebentypus (hf : MDiff f) (hk : 0 < k)
    (hlaw : ∀ γ ∈ Gamma0 N, f ∣[k] γ = χ (γ 1 1 : ℤ) • f) (hbd : HasModerateGrowth f) :
    ModularForm ((Gamma1 N).map (mapGL ℝ)) k where
  toFun := f
  slash_action_eq' := by
    rintro _ ⟨γ, hγ, rfl⟩
    have h1 :
        ((γ 0 0 : ℤ) : ZMod N) = 1 ∧ ((γ 1 1 : ℤ) : ZMod N) = 1 ∧ ((γ 1 0 : ℤ) : ZMod N) = 0 :=
      (Gamma1_mem N γ).mp hγ
    have h2 : f ∣[k] γ = χ (γ 1 1 : ℤ) • f := hlaw γ (Gamma0_mem.mpr h1.2.2)
    rw [h1.2.1, map_one, one_smul] at h2
    exact h2
  holo' := hf
  bdd_at_cusps' := fun {c} hc ↦ by
    have hc' : IsCusp c 𝒮ℒ := hc.mono (by
      rintro _ ⟨γ, -, rfl⟩
      exact ⟨γ, rfl⟩)
    exact (OnePoint.isBoundedAt_iff_forall_SL2Z hc').mpr fun γ _ ↦
      isBoundedAtImInfty_slash_of_nebentypus γ hf hk hlaw hbd

lemma modularFormOfNebentypus_mem (hf : MDiff f) (hk : 0 < k)
    (hlaw : ∀ γ ∈ Gamma0 N, f ∣[k] γ = χ (γ 1 1 : ℤ) • f) (hbd : HasModerateGrowth f) :
    modularFormOfNebentypus χ hf hk hlaw hbd ∈ modFormCharSpace k χ.toUnitHom := by
  rw [mem_modFormCharSpace_iff_nebentypus]
  intro g
  have h1 : f ∣[k] (g : SL(2, ℤ)) = χ ((g : SL(2, ℤ)) 1 1 : ℤ) • f := hlaw g g.2
  have h2 : ((χ.toUnitHom ((Gamma0Map N).toHomUnits g) : ℂˣ) : ℂ) = χ ((g : SL(2, ℤ)) 1 1 : ℤ) := by
    simp [Gamma0Map_apply]
  rw [h2]
  exact h1

variable (a b k χ) in
/-- The hypotheses of **Weil's converse theorem** for sequences `a, b`, weight `k` and a Dirichlet
character `χ` modulo `N`: polynomial growth; the functional equation
`Λ_a(s) = i ^ k N ^ (k / 2 - s) Λ_b(k - s)`, with the poles of `Λ_a` at `0` and `k` given by the
constant terms; and, for some `R`, for every nontrivial character `ψ` modulo every prime `r > R` not
dividing `N`, the functional equation
`Λ_{ψ a}(s) = i ^ k χ(r) ψ(N) τ(ψ) ^ 2 / r (N r²) ^ (k / 2 - s) Λ_{ψ⁻¹ b}(k - s)` of the twists,
where `τ(ψ) = ∑_u ψ(u) e(u / r)`. -/
structure HasWeilFunctionalEquations : Prop where
  polyGrowth_left : HasPolyGrowth a
  polyGrowth_right : HasPolyGrowth b
  base : HasFunctionalEquation a b k N (I ^ k)
  twist : ∃ R : ℕ, ∀ (r : ℕ) [Fact r.Prime], R < r → ¬r ∣ N → ∀ ψ : DirichletCharacter ℂ r, ψ ≠ 1 →
    HasFunctionalEquation (twistSeq ψ a) (twistSeq ψ⁻¹ b) k (N * r ^ 2)
      (I ^ k * χ r * ψ N * gaussSum ψ ZMod.stdAddChar ^ 2 / r)

/-- The modular form `∑ a n e(n z)` of **Weil's converse theorem**. -/
noncomputable def HasWeilFunctionalEquations.modularForm (h : HasWeilFunctionalEquations a b k χ)
    (hk : 0 < k) : ModularForm ((Gamma1 N).map (mapGL ℝ)) k :=
  modularFormOfNebentypus χ (mdifferentiable_expSum h.polyGrowth_left) hk
    (fun _ hγ ↦ h.twist.elim fun _ hR ↦ expSum_slash_eq_smul_of_hasFunctionalEquation hk
      h.polyGrowth_left h.polyGrowth_right h.base hR hγ)
    h.polyGrowth_left.hasModerateGrowth

lemma HasWeilFunctionalEquations.coe_modularForm (h : HasWeilFunctionalEquations a b k χ)
    (hk : 0 < k) : ⇑(h.modularForm hk) = expSum a :=
  rfl

/-- **Weil's converse theorem.** If the sequences `a, b` satisfy the functional equations
`HasWeilFunctionalEquations a b k χ` in weight `k > 0`, then `∑ a n e(n z)` is a modular form of
weight `k`, level `N` and character `χ`. -/
lemma HasWeilFunctionalEquations.modularForm_mem (h : HasWeilFunctionalEquations a b k χ)
    (hk : 0 < k) : h.modularForm hk ∈ modFormCharSpace k χ.toUnitHom :=
  modularFormOfNebentypus_mem _ hk _ _

end ModularForm
