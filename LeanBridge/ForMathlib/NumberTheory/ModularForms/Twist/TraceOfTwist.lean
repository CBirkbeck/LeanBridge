import LeanBridge.ForMathlib.NumberTheory.ModularForms.LowerUnipotent
import TauCeti.NumberTheory.ModularForms.Degeneracy
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic
import TauCeti.NumberTheory.ModularForms.Twist.Basic

/-!
# The trace of a twist

Let `q` be a prime, `F` a cusp form of level `Γ₁(P)` with `q ∤ P`, and `ψ` a Dirichlet character of
modulus `M = q M'` with `M' ∣ P`, not factoring through `M'`. This file shows, by an elementary
computation with matrices, that the twist `F ⊗ ψ` has zero trace at `q`, and deduces that the
coefficients of a form of level prime to `q` cannot be supported on the kernel of `ψ`. This is the
reason why a prime dividing the modulus of a self twist of a newform exactly once divides the level,
without strong multiplicity one across levels and without the sharp level of a twist (Atkin–Li,
*Twists of newforms and pseudo-eigenvalues of `W`-operators*, Invent. Math. 48 (1978)).

The twist `F ⊗ ψ` is a combination of the translates `F_a(τ) = F(τ + a / M)`, by Tau Ceti's
definition, with coefficients the discrete Fourier transform of `ψ`. The trace is the sum
`Tr h = ∑ h ∣ [1, 0; M P t, 1]` over the classes `t` modulo `q`. As
`[1, a/M; 0, 1] [1, 0; M c, 1] = γ [1, a'/M; 0, 1]` with `γ` in `Γ₁(P)` if `P ∣ c` and
`a ≡ (1 + a c) a'` modulo `M`, the matrices of the trace permute the translates `F_a` with `q ∤ a`
and `a` in a given class modulo `M'`, apart from one term. So `Tr F_a` depends only on the class of
`a` modulo `M'`. Multiplying `a` by a unit `u ≡ 1` modulo `M'` with `ψ(u) ≠ 1` multiplies the
Fourier transform of `ψ` by `ψ(u)⁻¹`, and so `Tr (F ⊗ ψ) = 0`.

Now let `E = F - D` be `F` with its coefficients at the multiples of `q` removed, where
`D = q⁻¹ ∑ F(τ + x / q)` over the classes `x` modulo `q`. Then `Tr F = q F` and
`Tr D = q⁻¹ (q F + (q - 1) Ω)`, for `Ω = Tr F(τ + 1 / q)`. Here `Ω = S - F + q D`, where the term
`S` left apart above is a multiple of `F(q² τ)`, as
`[1, 1/q; 0, 1] [1, 0; q j, 1] = [w, 1; j, q] diag(q, q⁻¹)` when `q w = 1 + j`. If
`ψ(n) a_n(F) = a_n(F)` for all `n` prime to `q`, then `F ⊗ ψ = E`, so `Tr E = 0`, which says
`Ω = q F`, that is `S = (q + 1) F - q D`. The coefficient at `1` of this identity is
`(q + 1) a₁(F) = 0`.

## Main definitions

* `TauCeti.slashLevelTrace`: the sum `∑ h ∣ [1, 0; M P t, 1]` over the classes `t` modulo `q`, the
  trace at the prime `q`.

## Main results

* `TauCeti.slashLevelTrace_twist_eq_zero`: the trace of `F ⊗ ψ` vanishes.
* `TauCeti.qExpansion_coeff_one_eq_zero_of_forall_coprime_apply_mul_eq`: if `F` has level prime to
  `q` and `ψ(n) a_n(F) = a_n(F)` for all `n` prime to `q`, then `a₁(F) = 0`.
-/

open UpperHalfPlane CongruenceSubgroup Matrix SpecialLinearGroup

open GeneralLinearGroup (upperRightHom)

open scoped MatrixGroups ModularForm ZMod

namespace TauCeti

variable {M P q M' L : ℕ} {k : ℤ} {F : CuspForm ((Gamma1 P).map (mapGL ℝ)) k} {a a' c : ℤ}
  {ε : (ZMod P)ˣ →* ℂˣ}

private lemma exists_upperRightHom_mul_mapGL_lowerUnipotent_eq {e : ℤ} (hM : M ≠ 0)
    (he : a - (1 + a * c) * a' = M * e) : ∃ γ : SL(2, ℤ), γ 0 0 = 1 + a * c ∧ γ 1 0 = M * c ∧
      γ 1 1 = 1 - c * a' ∧ upperRightHom ((a : ℝ) / M) * mapGL ℝ (lowerUnipotent (M * c)) =
        mapGL ℝ γ * upperRightHom ((a' : ℝ) / M) := by
  let γ : SL(2, ℤ) := ⟨!![1 + a * c, e; M * c, 1 - c * a'], by
    rw [Matrix.det_fin_two_of]
    linear_combination c * he⟩
  have hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![1 + a * c, e; M * c, 1 - c * a'] := rfl
  refine ⟨γ, by simp [hγ], by simp [hγ], by simp [hγ], ?_⟩
  have hMR : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM
  have heR : (a : ℝ) - (1 + a * c) * a' = M * e := by exact_mod_cast he
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, hγ, coe_lowerUnipotent] <;>
    field_simp
  · linear_combination heR
  · ring1

private lemma slash_upperRightHom_slash_lowerUnipotent (hM : M ≠ 0) (hP : (P : ℤ) ∣ c)
    (he : (M : ℤ) ∣ a - (1 + a * c) * a') : (⇑F ∣[k] upperRightHom ((a : ℝ) / M)) ∣[k]
      mapGL ℝ (lowerUnipotent (M * c)) = ⇑F ∣[k] upperRightHom ((a' : ℝ) / M) := by
  rcases he with ⟨e, he⟩
  rcases exists_upperRightHom_mul_mapGL_lowerUnipotent_eq hM he with ⟨γ, hA, hC, hD, heq⟩
  have hc : ((c : ℤ) : ZMod P) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hP
  have hγ : γ ∈ Gamma1 P := by
    rw [Gamma1_mem, hA, hC, hD]
    simp [hc]
  rw [← SlashAction.slash_mul, heq, SlashAction.slash_mul,
    SlashInvariantFormClass.slash_action_eq F (mapGL ℝ γ) (Subgroup.mem_map_of_mem _ hγ)]

private lemma slash_lowerUnipotent_of_dvd (hP : (P : ℤ) ∣ c) :
    ⇑F ∣[k] mapGL ℝ (lowerUnipotent c) = ⇑F := by
  have hc : ((c : ℤ) : ZMod P) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hP
  have hγ : lowerUnipotent c ∈ Gamma1 P := by
    rw [Gamma1_mem, coe_lowerUnipotent]
    simp [hc]
  exact SlashInvariantFormClass.slash_action_eq F _ (Subgroup.mem_map_of_mem _ hγ)

variable [NeZero M'] in
private lemma div_natCast_mul_eq_div {x : ℤ} :
    (((M' * x : ℤ) : ℝ) / (q * M' : ℕ)) = (x : ℝ) / q := by
  have hM' : (M' : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M')
  push_cast
  rw [mul_comm (q : ℝ), mul_div_mul_left _ _ hM']

variable [NeZero M'] in
private lemma one_div_eq_div_natCast_mul : (1 : ℝ) / q = ((M' : ℤ) : ℝ) / (q * M' : ℕ) := by
  have h : (((M' * 1 : ℤ) : ℝ) / (q * M' : ℕ)) = ((1 : ℤ) : ℝ) / q := div_natCast_mul_eq_div
  simpa using h.symm

variable [NeZero q]

variable (M P q k) in
/-- The **trace at the prime `q`** of a function `h` on the upper half plane: the sum of the
`h ∣ [1, 0; M P t, 1]` over the classes `t` modulo `q`. For `M = q M'` and `P` prime to `q`, and `h`
a form of level `q²` at `q`, it is the trace from level `q²` to level `q` at `q`. -/
noncomputable def slashLevelTrace (h : ℍ → ℂ) : ℍ → ℂ :=
  ∑ t : ZMod q, h ∣[k] mapGL ℝ (lowerUnipotent (M * (P * (t.val : ℤ))))

private lemma sum_val_add_eq {X : Type*} [AddCommMonoid X] {u : ℤ → X}
    (hu : ∀ n s : ℤ, u (n + q * s) = u n) (t₀ : ℤ) :
    ∑ t : ZMod q, u (t₀ + (t.val : ℤ)) = ∑ t : ZMod q, u (t.val : ℤ) := by
  have hval (n : ℤ) : u (((n : ZMod q).val : ℤ)) = u n := by
    have hn : ((n : ZMod q).val : ℤ) = n % q := ZMod.val_intCast n
    rw [hn, ← hu (n % q) (n / q), Int.emod_add_mul_ediv]
  rw [← Equiv.sum_comp (Equiv.addLeft (t₀ : ZMod q)) fun t : ZMod q ↦ u (t.val : ℤ)]
  refine Finset.sum_congr rfl fun t _ ↦ ?_
  rw [Equiv.coe_addLeft, ← hval (t₀ + (t.val : ℤ))]
  simp

private lemma slashLevelTrace_slash (hM : M ≠ 0) (hMP : M ∣ q * P) (t₀ : ℤ) :
    slashLevelTrace M P q k ((⇑F ∣[k] upperRightHom ((a : ℝ) / M)) ∣[k]
      mapGL ℝ (lowerUnipotent (M * (P * t₀)))) =
        slashLevelTrace M P q k (⇑F ∣[k] upperRightHom ((a : ℝ) / M)) := by
  let u : ℤ → ℍ → ℂ := fun n ↦
    (⇑F ∣[k] upperRightHom ((a : ℝ) / M)) ∣[k] mapGL ℝ (lowerUnipotent (M * (P * n)))
  have hu (n s : ℤ) : u (n + q * s) = u n := by
    have h : lowerUnipotent (M * (P * (n + q * s))) =
        lowerUnipotent (M * (P * (q * s))) * lowerUnipotent (M * (P * n)) := by
      rw [← lowerUnipotent_add]
      congr 1
      ring1
    simp only [u]
    rw [h, map_mul, SlashAction.slash_mul,
      slash_upperRightHom_slash_lowerUnipotent (a' := a) hM (Dvd.intro _ rfl) ?_]
    rcases hMP with ⟨R, hR⟩
    have hRz : (q : ℤ) * P = M * R := by exact_mod_cast hR
    exact ⟨-a ^ 2 * R * s, by linear_combination -a ^ 2 * s * hRz⟩
  have h₀ (t : ZMod q) : ((⇑F ∣[k] upperRightHom ((a : ℝ) / M)) ∣[k]
      mapGL ℝ (lowerUnipotent (M * (P * t₀)))) ∣[k]
        mapGL ℝ (lowerUnipotent (M * (P * (t.val : ℤ)))) = u (t₀ + (t.val : ℤ)) := by
    simp only [u]
    rw [← SlashAction.slash_mul, ← map_mul, ← lowerUnipotent_add]
    congr 3
    ring1
  simp only [slashLevelTrace, h₀]
  exact sum_val_add_eq hu t₀

private lemma slashLevelTrace_smul (b : ℂ) (h : ℍ → ℂ) :
    slashLevelTrace M P q k (b • h) = b • slashLevelTrace M P q k h := by
  simp only [slashLevelTrace, Finset.smul_sum]
  exact Finset.sum_congr rfl fun t _ ↦ ModularForm.SL_smul_slash k _ h b

private lemma slashLevelTrace_sum {ι : Type*} [Fintype ι] (h : ι → ℍ → ℂ) :
    slashLevelTrace M P q k (∑ i, h i) = ∑ i, slashLevelTrace M P q k (h i) := by
  simp only [slashLevelTrace, SlashAction.sum_slash]
  exact Finset.sum_comm

private lemma slashLevelTrace_sub (h h' : ℍ → ℂ) :
    slashLevelTrace M P q k (h - h') = slashLevelTrace M P q k h - slashLevelTrace M P q k h' := by
  simp only [slashLevelTrace, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
    Finset.sum_add_distrib, Finset.sum_neg_distrib]

private lemma slashLevelTrace_coe : slashLevelTrace M P q k ⇑F = (q : ℂ) • ⇑F := by
  have h (t : ZMod q) : ⇑F ∣[k] mapGL ℝ (lowerUnipotent (M * (P * (t.val : ℤ)))) = ⇑F :=
    slash_lowerUnipotent_of_dvd ((Dvd.intro _ rfl).mul_left _)
  simp only [slashLevelTrace, h, Finset.sum_const]
  funext τ
  simp

variable [NeZero M] in
private lemma coe_twist_eq_sum_slash (Φ : ZMod M → ℂ) (hNL : P * M ∣ L) (hML : M * M ∣ L) :
    ⇑(CuspForm.twist Φ hNL hML F) =
      (M : ℂ)⁻¹ • ∑ a : ZMod M, 𝓕 Φ a • (⇑F ∣[k] upperRightHom (((a.val : ℤ) : ℝ) / M)) := by
  funext τ
  simp only [CuspForm.twist_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul,
    ModularForm.slash_upperRightHom_apply, Int.cast_natCast]

variable [NeZero M'] (ψ : DirichletCharacter ℂ (q * M'))

private lemma slashLevelTrace_eq_of_dvd_sub {a₁ a₂ : ℤ} (hq : q.Prime) (hP : M' ∣ P) (hqP : ¬q ∣ P)
    (ha₁ : ¬(q : ℤ) ∣ a₁) (ha₂ : ¬(q : ℤ) ∣ a₂) (h : (M' : ℤ) ∣ a₁ - a₂) :
    slashLevelTrace (q * M') P q k (⇑F ∣[k] upperRightHom ((a₂ : ℝ) / (q * M' : ℕ))) =
      slashLevelTrace (q * M') P q k (⇑F ∣[k] upperRightHom ((a₁ : ℝ) / (q * M' : ℕ))) := by
  rcases hP with ⟨P₁, rfl⟩
  rcases h with ⟨b, hb⟩
  have hq' : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hP₁q : ¬(q : ℤ) ∣ P₁ := fun hd ↦ hqP <| Int.natCast_dvd_natCast.mp <| by
    push_cast
    exact hd.mul_left _
  have hc : IsCoprime (q : ℤ) (a₁ * a₂ * P₁) := hq'.coprime_iff_not_dvd.mpr fun hd ↦
    (hq'.dvd_or_dvd hd).elim (fun hd ↦ (hq'.dvd_or_dvd hd).elim ha₁ ha₂) hP₁q
  rcases hc with ⟨y, x, hxy⟩
  have hslash : (⇑F ∣[k] upperRightHom ((a₁ : ℝ) / (q * M' : ℕ))) ∣[k]
      mapGL ℝ (lowerUnipotent ((q * M' : ℕ) * ((M' * P₁ : ℕ) * (b * x)))) =
        ⇑F ∣[k] upperRightHom ((a₂ : ℝ) / (q * M' : ℕ)) := by
    refine slash_upperRightHom_slash_lowerUnipotent (NeZero.ne _) (Dvd.intro _ rfl) ⟨b * y, ?_⟩
    push_cast
    linear_combination hb - (M' : ℤ) * b * hxy
  rw [← hslash]
  exact slashLevelTrace_slash (NeZero.ne _) (mul_dvd_mul_left q (dvd_mul_right M' P₁)) (b * x)

/-- **The trace of a twist vanishes**: let `F` be a cusp form of level `Γ₁(P)`, with `q` a prime not
dividing `P`, and let `ψ` be a Dirichlet character modulo `q M'`, with `M' ∣ P`, that does not
factor through `M'`. Then the trace at `q` of the twist `F ⊗ ψ` is zero. -/
lemma slashLevelTrace_twist_eq_zero (hq : q.Prime) (hP : M' ∣ P) (hqP : ¬q ∣ P)
    (hψ : ¬ψ.FactorsThrough M') (hNL : P * (q * M') ∣ L) (hML : q * M' * (q * M') ∣ L) :
    slashLevelTrace (q * M') P q k ⇑(CuspForm.twist ψ hNL hML F) = 0 := by
  have hM'M : M' ∣ q * M' := dvd_mul_left M' q
  have hqM : q ∣ q * M' := dvd_mul_right q M'
  have hqM' : ¬q ∣ M' := fun h ↦ hqP (h.trans hP)
  rcases IsConcreteLE.not_le_iff_exists.mp
    (mt (DirichletCharacter.factorsThrough_iff_ker_unitsMap hM'M).mpr hψ) with ⟨u, hu, hψu'⟩
  have hψu : ψ u ≠ 1 := fun h₁ ↦ hψu' <| MonoidHom.mem_ker.mpr <| Units.ext <| by
    rw [MulChar.coe_toUnitHom, h₁, Units.val_one]
  let T : ZMod (q * M') → ℍ → ℂ := fun a ↦ 𝓕 ψ a •
    slashLevelTrace (q * M') P q k (⇑F ∣[k] upperRightHom (((a.val : ℤ) : ℝ) / (q * M' : ℕ)))
  have hF₁ (a : ZMod (q * M')) : 𝓕 ψ a = ψ u * 𝓕 ψ (u * a) := by
    have h : 𝓕 (fun j ↦ ψ ((u : ZMod (q * M')) * j)) ((u : ZMod (q * M')) * a) =
        𝓕 ψ (((u⁻¹ : (ZMod (q * M'))ˣ) : ZMod (q * M')) * ((u : ZMod (q * M')) * a)) :=
      ZMod.dft_comp_unitMul (⇑ψ) u (u * a)
    have hfun : (fun j ↦ ψ ((u : ZMod (q * M')) * j)) = ψ ↑u • ⇑ψ := by
      ext j
      simp
    rw [hfun, map_smul, Units.inv_mul_cancel_left, Pi.smul_apply, smul_eq_mul] at h
    exact h.symm
  have hψu₀ : ψ u ≠ 0 := (u.isUnit.map ψ).ne_zero
  have hcastu : ZMod.castHom hM'M (ZMod M') (u : ZMod (q * M')) = 1 := by
    have h : ((ZMod.unitsMap hM'M u : (ZMod M')ˣ) : ZMod M') = 1 := by
      rw [hu, Units.val_one]
    simpa [ZMod.unitsMap_val] using h
  have hval {b : ℕ} (hb : b ∣ q * M') (x : ZMod (q * M')) :
      (x.val : ZMod b) = ZMod.castHom hb (ZMod b) x := by
    rw [ZMod.castHom_apply, ZMod.natCast_val]
  have hT (a : ZMod (q * M')) : T (u * a) = (ψ u)⁻¹ • T a := by
    by_cases ha : ZMod.castHom hqM (ZMod q) a = 0
    · have hua : (u : ZMod (q * M')) * a = a := by
        have hx (x : ZMod (q * M')) (h₁ : ZMod.castHom hqM (ZMod q) x = 0)
            (h₂ : ZMod.castHom hM'M (ZMod M') x = 0) : x = 0 := by
          rw [← hval] at h₁ h₂
          rw [← ZMod.natCast_zmod_val x, ZMod.natCast_eq_zero_iff]
          exact (hq.coprime_iff_not_dvd.mpr hqM').mul_dvd_of_dvd_of_dvd
            ((ZMod.natCast_eq_zero_iff _ _).mp h₁) ((ZMod.natCast_eq_zero_iff _ _).mp h₂)
        refine sub_eq_zero.mp (hx _ ?_ ?_)
        · rw [map_sub, map_mul, ha, mul_zero, sub_zero]
        · rw [map_sub, map_mul, hcastu, one_mul, sub_self]
      have h0 : 𝓕 ψ a = 0 := by
        by_contra h
        have h₁ : ψ u * 𝓕 ψ a = 𝓕 ψ a := by
          have h₂ : 𝓕 ψ a = ψ u * 𝓕 ψ (u * a) := hF₁ a
          rw [hua] at h₂
          exact h₂.symm
        exact hψu ((mul_eq_right₀ h).mp h₁)
      simp [T, hua, h0]
    · have hqa : ¬(q : ℤ) ∣ (a.val : ℤ) := fun h ↦ ha <| by
        rw [← hval, (ZMod.natCast_eq_zero_iff _ _).mpr (Int.natCast_dvd_natCast.mp h)]
      have hqua : ¬(q : ℤ) ∣ (((u : ZMod (q * M')) * a).val : ℤ) := fun h ↦ ha <| by
        have h₁ : ZMod.castHom hqM (ZMod q) ((u : ZMod (q * M')) * a) = 0 := by
          rw [← hval, (ZMod.natCast_eq_zero_iff _ _).mpr (Int.natCast_dvd_natCast.mp h)]
        rw [map_mul] at h₁
        exact ((u.isUnit.map _).mul_right_eq_zero).mp h₁
      have hsub : (M' : ℤ) ∣ (a.val : ℤ) - (((u : ZMod (q * M')) * a).val : ℤ) := by
        refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ M').mp ?_
        rw [Int.cast_natCast, Int.cast_natCast, hval hM'M, hval hM'M, map_mul, hcastu, one_mul]
      have htr : slashLevelTrace (q * M') P q k
          (⇑F ∣[k] upperRightHom ((((u * a : ZMod (q * M')).val : ℤ) : ℝ) / (q * M' : ℕ))) =
            slashLevelTrace (q * M') P q k
              (⇑F ∣[k] upperRightHom (((a.val : ℤ) : ℝ) / (q * M' : ℕ))) :=
        slashLevelTrace_eq_of_dvd_sub hq hP hqP hqa hqua hsub
      simp only [T]
      rw [htr, hF₁ a, mul_smul, smul_smul, inv_mul_cancel₀ hψu₀, one_smul]
  have hX : ∑ a, T a = (ψ u)⁻¹ • ∑ a, T a := by
    rw [Finset.smul_sum, ← Equiv.sum_comp (Units.mulLeft u) T]
    exact Finset.sum_congr rfl fun a _ ↦ hT a
  have hX₀ : ∑ a, T a = 0 := by
    have h₁ : (1 - (ψ u)⁻¹) • ∑ a, T a = 0 := by
      rw [sub_smul, one_smul, ← hX, sub_self]
    exact (smul_eq_zero.mp h₁).resolve_left fun h₂ ↦
      hψu (inv_eq_one.mp (sub_eq_zero.mp h₂).symm)
  rw [coe_twist_eq_sum_slash, slashLevelTrace_smul, slashLevelTrace_sum]
  simp only [slashLevelTrace_smul]
  exact (congrArg (fun G : ℍ → ℂ ↦ ((q * M' : ℕ) : ℂ)⁻¹ • G) hX₀).trans (smul_zero _)

variable (q) in
/-- The matrix `diag(q, q⁻¹)` of `GL(2, ℝ)`. -/
private noncomputable def diagInvGL : GL (Fin 2) ℝ :=
  diagGL ![Units.mk0 (q : ℝ) (Nat.cast_ne_zero.mpr (NeZero.ne q)),
    (Units.mk0 (q : ℝ) (Nat.cast_ne_zero.mpr (NeZero.ne q)))⁻¹]

private lemma coe_diagInvGL :
    ((diagInvGL q : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(q : ℝ), 0; 0, (q : ℝ)⁻¹] := by
  rw [diagInvGL, diagGL_coe, Matrix.diagonal_fin_two]
  simp

private lemma val_det_diagInvGL : ((diagInvGL q).det : ℝ) = 1 := by
  rw [diagInvGL, det_diagGL, Fin.prod_univ_two]
  simp

private lemma val_det_diagInvGL_pos : 0 < ((diagInvGL q).det : ℝ) :=
  val_det_diagInvGL (q := q).symm ▸ one_pos

private lemma slash_diagInvGL_apply (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] diagInvGL q) τ = (q : ℂ) ^ k * f (scaleGL (q ^ 2) • τ) := by
  have hsmul : diagInvGL q • τ = scaleGL (q ^ 2) • τ := by
    ext1
    rw [coe_scaleGL_smul, coe_smul_of_det_pos val_det_diagInvGL_pos]
    simp [UpperHalfPlane.num, UpperHalfPlane.denom, coe_diagInvGL]
    ring1
  rw [ModularForm.slash_apply, σ_eq_refl_of_det_pos val_det_diagInvGL_pos, hsmul, val_det_diagInvGL]
  simp [UpperHalfPlane.denom, coe_diagInvGL, mul_comm]

private lemma exists_slash_upperRightHom_slash_lowerUnipotent_eq_smul_levelRaise {j w : ℤ}
    (hF : F ∈ cuspFormCharSpace k ε) (hP : (P : ℤ) ∣ j) (hw : 1 + j = q * w) (hL : q ^ 2 * P ∣ L) :
    ∃ C : ℂ, (⇑F ∣[k] upperRightHom ((1 : ℝ) / q)) ∣[k] mapGL ℝ (lowerUnipotent (q * j)) =
      C • ⇑(CuspForm.levelRaise (q ^ 2) (Gamma1_map_le_conjAct_scaleGL_of_dvd hL) F) := by
  have hq : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  let γ : SL(2, ℤ) := ⟨!![w, 1; j, q], by
    rw [Matrix.det_fin_two_of]
    linear_combination -hw⟩
  have hγ₀ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = !![w, 1; j, q] := rfl
  have hγ : γ ∈ Gamma0 P := by
    rw [Gamma0_mem, hγ₀]
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hP
  have hwR : (1 : ℝ) + j = q * w := by exact_mod_cast hw
  have heq :
      upperRightHom ((1 : ℝ) / q) * mapGL ℝ (lowerUnipotent (q * j)) = mapGL ℝ γ * diagInvGL q := by
    ext i l
    fin_cases i <;> fin_cases l <;>
      simp [Matrix.mul_apply, hγ₀, coe_lowerUnipotent, coe_diagInvGL]
    · rw [inv_mul_cancel_left₀ hq, hwR, mul_comm]
    · exact mul_comm _ _
  refine ⟨((ε ((Gamma0Map P).toHomUnits ⟨γ, hγ⟩) : ℂˣ) : ℂ) * (q : ℂ) ^ k, ?_⟩
  rw [← SlashAction.slash_mul, heq, SlashAction.slash_mul,
    (mem_cuspFormCharSpace_iff_nebentypus k ε F).mp hF ⟨γ, hγ⟩]
  funext τ
  rw [ModularForm.smul_slash, σ_eq_refl_of_det_pos val_det_diagInvGL_pos, Pi.smul_apply,
    Pi.smul_apply, smul_eq_mul, smul_eq_mul, slash_diagInvGL_apply, CuspForm.levelRaise_apply,
    mul_assoc]
  rfl

variable (q) in
/-- The indicator function of `0` on `ZMod q`: the twist of a form by it keeps the coefficients at
the multiples of `q`. -/
private noncomputable def zeroIndicator : ZMod q → ℂ := fun n ↦ if n = 0 then 1 else 0

private lemma dft_zeroIndicator (x : ZMod q) : 𝓕 (zeroIndicator q) x = 1 := by
  rw [ZMod.dft_apply]
  simp [zeroIndicator]

private lemma slashLevelTrace_slash_upperRightHom_one_div_eq (hq : q.Prime) (hqP : ¬q ∣ P)
    (hqM' : ¬q ∣ M') (hF : F ∈ cuspFormCharSpace k ε) (hL : q ^ 2 * P ∣ L) :
    ∃ C : ℂ, slashLevelTrace (q * M') P q k (⇑F ∣[k] upperRightHom ((1 : ℝ) / q)) =
      C • ⇑(CuspForm.levelRaise (q ^ 2) (Gamma1_map_le_conjAct_scaleGL_of_dvd hL) F) - ⇑F +
        ∑ x : ZMod q, ⇑F ∣[k] upperRightHom (((x.val : ℤ) : ℝ) / q) := by
  have : Fact q.Prime := ⟨hq⟩
  let r : ZMod q := ((M' * P : ℕ) : ZMod q)
  have hr : r ≠ 0 := fun h ↦
    (hq.dvd_mul.mp ((ZMod.natCast_eq_zero_iff _ _).mp h)).elim hqM' hqP
  let e : ZMod q ≃ ZMod q := (Equiv.mulLeft₀ r hr).trans (Equiv.addLeft 1)
  have he (t : ZMod q) : e t = 1 + r * t := rfl
  have hval (t : ZMod q) : (((1 + M' * (P * t.val) : ℤ)) : ZMod q) = e t := by
    rw [he]
    simp [r, mul_assoc]
  have ht₀ : e (e.symm 0) = 0 := e.apply_symm_apply 0
  rcases (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp ((hval (e.symm 0)).trans ht₀) with ⟨w, hw⟩
  rcases exists_slash_upperRightHom_slash_lowerUnipotent_eq_smul_levelRaise hF
    ((Dvd.intro _ rfl : (P : ℤ) ∣ P * ((e.symm 0).val : ℤ)).mul_left (M' : ℤ)) hw hL with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  let h : ZMod q → ℍ → ℂ := fun x ↦ ⇑F ∣[k] upperRightHom (((x.val : ℤ) : ℝ) / q)
  let g : ZMod q → ℍ → ℂ := fun v ↦ if v = 0 then
    C • ⇑(CuspForm.levelRaise (q ^ 2) (Gamma1_map_le_conjAct_scaleGL_of_dvd hL) F) else h v⁻¹
  have hterm (t : ZMod q) : (⇑F ∣[k] upperRightHom ((1 : ℝ) / q)) ∣[k]
      mapGL ℝ (lowerUnipotent ((q * M' : ℕ) * (P * (t.val : ℤ)))) = g (e t) := by
    by_cases ht : e t = 0
    · have htt : t = e.symm 0 := e.injective (ht.trans ht₀.symm)
      subst htt
      simp only [g, ht]
      rw [← hC]
      congr 3
      push_cast
      ring1
    · simp only [g, ht, ↓reduceIte]
      have hcast : (((1 - (1 + M' * (P * t.val)) * ((e t)⁻¹).val : ℤ)) : ZMod q) = 0 := by
        rw [Int.cast_sub, Int.cast_mul, hval t, Int.cast_natCast, ZMod.natCast_zmod_val,
          mul_inv_cancel₀ ht]
        simp
      rcases (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp hcast with ⟨s, hs⟩
      have key : (⇑F ∣[k] upperRightHom (((M' : ℤ) : ℝ) / (q * M' : ℕ))) ∣[k]
          mapGL ℝ (lowerUnipotent ((q * M' : ℕ) * (P * (t.val : ℤ)))) =
            ⇑F ∣[k] upperRightHom ((((M' : ℤ) * (((e t)⁻¹).val : ℤ) : ℤ) : ℝ) / (q * M' : ℕ)) :=
        slash_upperRightHom_slash_lowerUnipotent (NeZero.ne _) (Dvd.intro _ rfl) ⟨s, by
          push_cast
          linear_combination (M' : ℤ) * hs⟩
      rw [one_div_eq_div_natCast_mul (M' := M'), key, div_natCast_mul_eq_div]
  have hg (v : ZMod q) : g v = h v⁻¹ + if v = 0 then
      C • ⇑(CuspForm.levelRaise (q ^ 2) (Gamma1_map_le_conjAct_scaleGL_of_dvd hL) F) - h 0
      else 0 := by
    by_cases hv : v = 0 <;> simp [g, hv]
  have hh₀ : h 0 = ⇑F := by
    simp only [h]
    rw [ZMod.val_zero, Nat.cast_zero, Int.cast_zero, zero_div, AddChar.map_zero_eq_one,
      SlashAction.slash_one]
  have hsum : slashLevelTrace (q * M') P q k (⇑F ∣[k] upperRightHom ((1 : ℝ) / q)) = ∑ v, g v := by
    simp only [slashLevelTrace, hterm]
    exact e.sum_comp g
  have hinv : ∑ x, h x⁻¹ = ∑ x, h x := Equiv.sum_comp (Equiv.inv (ZMod q)) h
  have hsumh : ∑ x, h x = ∑ x : ZMod q, ⇑F ∣[k] upperRightHom (((x.val : ℤ) : ℝ) / q) := rfl
  rw [hsum]
  simp only [hg, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [hinv, hh₀, hsumh]
  abel

/-- **A form of level prime to `q` is not supported on the kernel of a character ramified at `q`**:
let `F ∈ S_k(Γ₁(P), ε)` with `q` a prime not dividing `P`, and let `ψ` be a Dirichlet character
modulo `q M'`, with `M' ∣ P`, that does not factor through `M'`. If `ψ(n) a_n(F) = a_n(F)` for all
`n` prime to `q`, then `a₁(F) = 0`. -/
lemma qExpansion_coeff_one_eq_zero_of_forall_coprime_apply_mul_eq (hq : q.Prime) (hP : M' ∣ P)
    (hqP : ¬q ∣ P) (hF : F ∈ cuspFormCharSpace k ε) (hψ : ¬ψ.FactorsThrough M')
    (h : ∀ n : ℕ, n.Coprime q → ψ n * (qExpansion 1 F).coeff n = (qExpansion 1 F).coeff n) :
    (qExpansion 1 F).coeff 1 = 0 := by
  have hqM' : ¬q ∣ M' := fun h ↦ hqP (h.trans hP)
  have hqM : q ∣ q * M' := dvd_mul_right q M'
  have hNL : P * (q * M') ∣ P * (q * M') * (q * M') := dvd_mul_right _ _
  have hML : q * M' * (q * M') ∣ P * (q * M') * (q * M') := ⟨P, by ring1⟩
  have hqNL : P * q ∣ P * (q * M') * (q * M') := (mul_dvd_mul_left P hqM).mul_right _
  have hqML : q * q ∣ P * (q * M') * (q * M') := ⟨P * M' * M', by ring1⟩
  have hL : q ^ 2 * P ∣ P * (q * M') * (q * M') := ⟨M' * M', by ring1⟩
  have hPL : P ∣ P * (q * M') * (q * M') := (dvd_mul_right P _).mul_right _
  have h1 : (1 : ℝ) ∈ ((Gamma1 (P * (q * M') * (q * M'))).map (mapGL ℝ)).strictPeriods :=
    one_mem_strictPeriods_Gamma1_map _
  let A : CuspForm ((Gamma1 (P * (q * M') * (q * M'))).map (mapGL ℝ)) k :=
    CuspForm.twist ψ hNL hML F
  let D : CuspForm ((Gamma1 (P * (q * M') * (q * M'))).map (mapGL ℝ)) k :=
    CuspForm.twist (zeroIndicator q) hqNL hqML F
  let R : CuspForm ((Gamma1 (P * (q * M') * (q * M'))).map (mapGL ℝ)) k :=
    CuspForm.restrict (Gamma1_map_le_Gamma1_map_of_dvd hPL) F
  have hARD : A = R - D := by
    refine CuspForm.qExpansion_injective one_pos h1 <| PowerSeries.ext fun n ↦ ?_
    beta_reduce
    rw [← CuspForm.qExpansionCoeffₗ_apply one_pos h1 n (R - D), map_sub,
      CuspForm.qExpansionCoeffₗ_apply, CuspForm.qExpansionCoeffₗ_apply,
      CuspForm.qExpansion_twist_coeff, CuspForm.qExpansion_twist_coeff, CuspForm.coe_restrict]
    by_cases hn : q ∣ n
    · have hψn : ψ n = 0 := MulChar.map_nonunit _ fun hun ↦ hq.one_lt.ne' <|
        Nat.eq_one_of_dvd_coprimes ((ZMod.isUnit_iff_coprime n (q * M')).mp hun) hn hqM
      have hδ : zeroIndicator q n = 1 := by
        simp [zeroIndicator, (ZMod.natCast_eq_zero_iff n q).mpr hn]
      rw [hψn, hδ, zero_mul, one_mul, sub_self]
    · have hδ : zeroIndicator q n = 0 := by
        simp [zeroIndicator, (ZMod.natCast_eq_zero_iff n q).not.mpr hn]
      rw [h n ((hq.coprime_iff_not_dvd.mpr hn).symm), hδ, zero_mul, sub_zero]
  have hRF : ⇑R = ⇑F := CuspForm.coe_restrict _ _
  have hDsum : (q : ℂ) • ⇑D = ∑ x : ZMod q, ⇑F ∣[k] upperRightHom (((x.val : ℤ) : ℝ) / q) := by
    have hq₀ : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne_zero
    simp only [D, coe_twist_eq_sum_slash, dft_zeroIndicator, one_smul]
    rw [smul_smul, mul_inv_cancel₀ hq₀, one_smul]
  rcases slashLevelTrace_slash_upperRightHom_one_div_eq (M' := M') hq hqP hqM' hF hL with ⟨C, hC⟩
  have hq' : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have hqM'z : ¬(q : ℤ) ∣ (M' : ℤ) := fun h' ↦ hqM' (Int.natCast_dvd_natCast.mp h')
  have htrx (x : ZMod q) (hx : x ≠ 0) :
      slashLevelTrace (q * M') P q k (⇑F ∣[k] upperRightHom (((x.val : ℤ) : ℝ) / q)) =
        slashLevelTrace (q * M') P q k (⇑F ∣[k] upperRightHom ((1 : ℝ) / q)) := by
    have hxq : ¬(q : ℤ) ∣ (x.val : ℤ) := fun h' ↦ hx <| by
      rw [← ZMod.natCast_zmod_val x]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr (Int.natCast_dvd_natCast.mp h')
    have hmul : ¬(q : ℤ) ∣ ((M' : ℤ) * (x.val : ℤ)) := fun h' ↦
      (hq'.dvd_or_dvd h').elim hqM'z hxq
    have hsub : (M' : ℤ) ∣ (M' : ℤ) - (M' : ℤ) * (x.val : ℤ) :=
      dvd_sub dvd_rfl (dvd_mul_right _ _)
    have key : slashLevelTrace (q * M') P q k
        (⇑F ∣[k] upperRightHom ((((M' : ℤ) * (x.val : ℤ) : ℤ) : ℝ) / (q * M' : ℕ))) =
          slashLevelTrace (q * M') P q k (⇑F ∣[k] upperRightHom (((M' : ℤ) : ℝ) / (q * M' : ℕ))) :=
      slashLevelTrace_eq_of_dvd_sub hq hP hqP hqM'z hmul hsub
    rwa [div_natCast_mul_eq_div, ← one_div_eq_div_natCast_mul] at key
  have htr₀ : slashLevelTrace (q * M') P q k
      (⇑F ∣[k] upperRightHom (((0 : ZMod q).val : ℤ) / (q : ℝ))) = (q : ℂ) • ⇑F := by
    rw [ZMod.val_zero, Nat.cast_zero, Int.cast_zero, zero_div, AddChar.map_zero_eq_one,
      SlashAction.slash_one, slashLevelTrace_coe]
  let Ω : ℍ → ℂ := slashLevelTrace (q * M') P q k (⇑F ∣[k] upperRightHom ((1 : ℝ) / q))
  have hsumtr : (q : ℂ) • slashLevelTrace (q * M') P q k ⇑D = (q : ℂ) • Ω + ((q : ℂ) • ⇑F - Ω) := by
    rw [← slashLevelTrace_smul, hDsum, slashLevelTrace_sum]
    have hterm (x : ZMod q) :
        slashLevelTrace (q * M') P q k (⇑F ∣[k] upperRightHom (((x.val : ℤ) : ℝ) / q)) =
          Ω + if x = 0 then (q : ℂ) • ⇑F - Ω else 0 := by
      by_cases hx : x = 0
      · subst hx
        simp only [↓reduceIte]
        rw [htr₀]
        abel
      · simp only [hx, ↓reduceIte, add_zero]
        exact htrx x hx
    simp only [hterm, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  have htrD : (q : ℂ) • ⇑F = slashLevelTrace (q * M') P q k ⇑D := by
    have h₀ : slashLevelTrace (q * M') P q k ⇑A = 0 :=
      slashLevelTrace_twist_eq_zero ψ hq hP hqP hψ hNL hML
    rw [hARD, FunLike.coe_sub, slashLevelTrace_sub, hRF, slashLevelTrace_coe, sub_eq_zero] at h₀
    exact h₀
  have hΩ : Ω = (q : ℂ) • ⇑F := by
    have hq₁ : (q : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (Nat.cast_ne_one.mpr hq.ne_one)
    funext τ
    have h₂ : ((q : ℂ) • (q : ℂ) • ⇑F) τ = ((q : ℂ) • Ω + ((q : ℂ) • ⇑F - Ω)) τ :=
      congrFun ((congrArg (fun G : ℍ → ℂ ↦ (q : ℂ) • G) htrD).trans hsumtr) τ
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply] at h₂ ⊢
    refine sub_eq_zero.mp (mul_left_cancel₀ hq₁ ?_)
    linear_combination -h₂
  have hfun : (q : ℂ) • ⇑F = C • ⇑(CuspForm.levelRaise (q ^ 2)
      (Gamma1_map_le_conjAct_scaleGL_of_dvd hL) F) - ⇑F + (q : ℂ) • ⇑D := by
    rw [hDsum, ← hC]
    exact hΩ.symm
  have hform : C • CuspForm.levelRaise (q ^ 2) (Gamma1_map_le_conjAct_scaleGL_of_dvd hL) F =
      (q : ℂ) • R + R - (q : ℂ) • D := by
    refine CuspForm.ext fun τ ↦ ?_
    have h₂ : ((q : ℂ) • ⇑F) τ = (C • ⇑(CuspForm.levelRaise (q ^ 2)
        (Gamma1_map_le_conjAct_scaleGL_of_dvd hL) F) - ⇑F + (q : ℂ) • ⇑D) τ := congrFun hfun τ
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply] at h₂
    simp only [FunLike.coe_smul, FunLike.coe_add, FunLike.coe_sub, hRF, Pi.smul_apply, Pi.add_apply,
      Pi.sub_apply]
    linear_combination -h₂
  have hco : CuspForm.qExpansionCoeffₗ one_pos h1 k 1 (C • CuspForm.levelRaise (q ^ 2)
      (Gamma1_map_le_conjAct_scaleGL_of_dvd hL) F) =
        CuspForm.qExpansionCoeffₗ one_pos h1 k 1 ((q : ℂ) • R + R - (q : ℂ) • D) :=
    congrArg _ hform
  rw [map_smul, map_sub, map_add, map_smul, map_smul, CuspForm.qExpansionCoeffₗ_apply,
    CuspForm.qExpansionCoeffₗ_apply, CuspForm.qExpansionCoeffₗ_apply, hRF,
    CuspForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map _) h1,
    CuspForm.qExpansion_twist_coeff,
    ite_eq_right fun hd ↦ (Nat.one_lt_pow two_ne_zero hq.one_lt).ne' (Nat.dvd_one.mp hd)] at hco
  have : Fact q.Prime := ⟨hq⟩
  have hδ : zeroIndicator q (1 : ℕ) = 0 := by
    simp [zeroIndicator]
  rw [hδ] at hco
  refine (mul_eq_zero.mp ?_).resolve_left (Nat.cast_add_one_ne_zero q)
  simp only [smul_eq_mul] at hco
  linear_combination -hco

end TauCeti
