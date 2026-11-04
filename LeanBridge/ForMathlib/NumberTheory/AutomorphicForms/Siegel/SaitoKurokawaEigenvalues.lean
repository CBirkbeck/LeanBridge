import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwoSaitoKurokawaHecke
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.MaassLiftHeckeCoeff

/-!
# The Hecke eigenvalues of the Saito–Kurokawa lifts

A Saito–Kurokawa lift `F = Vφ` of a normalised Hecke eigenform `f ∈ S_{2k}(SL(2, ℤ))` is the
Maass lift of a nonzero Jacobi cusp form `φ ∈ J_{k+1,1}^cusp` whose Kohnen `D`-th Shimura lifts
are `c(|D|) f` (`SiegelUpperHalfSpace.IsSaitoKurokawaLift`). Its Fourier coefficients are the
Maass coefficients `SiegelUpperHalfSpace.maassFormCoeff` of the coefficients `c(N)` of `φ` by
discriminant, which satisfy the Jacobi relation (`ModularForm.jacobiDiscrCoeff_hecke`). From the
Fourier coefficients of `F ∣ T(p)` and `F ∣ T_1(p²)` and the action of these operators on Maass
coefficients, `F` is an eigenvector of `T(p)` and `T_1(p²)` with the eigenvalues
`a_p(f) + p^{k-1} + p^k` and `(p + 1) p^{k-2} a_p(f) + p^{2k-2} - p^{2k-4}`, and it is nonzero
since `φ` is. By `SiegelUpperHalfSpace.saitoKurokawaSpinTheorem_of_heckeOperator` this proves the
identity of spin `L`-functions `SiegelUpperHalfSpace.SaitoKurokawaSpinTheorem`.

## Main results

* `SiegelUpperHalfSpace.heckeOperator_Tp_maassLift`: the eigenvalue of `T(p)`.
* `SiegelUpperHalfSpace.heckeOperator_T₁_maassLift`: the eigenvalue of `T_1(p²)`.
* `SiegelUpperHalfSpace.maassLift_ne_zero`: the Maass lift of a nonzero Jacobi cusp form is
  nonzero.
* `SiegelUpperHalfSpace.saitoKurokawaSpinTheorem`: the spin `L`-function of the Saito–Kurokawa
  lifts.
-/

open ModularForm TauCeti BinaryQuadraticForm HeckeRing GL2 UpperHalfPlane

namespace SiegelUpperHalfSpace

local notation "Γ₂" => heckeGamma (Fin 2)

variable {k : ℤ} {φ : ℍ × ℂ → ℂ}

lemma maassCoeff_eq_maassFormCoeff (hφ : φ ∈ jacobiCuspFormSpace (k + 1) 1) (n r m : ℤ) :
    maassCoeff (k + 1) (jacobiCoeff φ) n r m =
      maassFormCoeff k (fun N ↦ jacobiDiscrCoeff φ N.toNat) ⟨n, r, m⟩ := by
  have hd : (⟨n, r, m⟩ : BinaryQuadraticForm ℤ).discrim = r ^ 2 - 4 * n * m := by
    rw [discrim_def, discrim]
  have hc : (⟨n, r, m⟩ : BinaryQuadraticForm ℤ).content = (n.gcd r : ℤ).gcd m := by
    rw [content_def, Int.gcd_assoc]
  rw [maassCoeff_eq_gritsenkoCoeff _ _ _ hφ, gritsenkoCoeff, maassFormCoeff]
  by_cases hf : 0 < (⟨n, r, m⟩ : BinaryQuadraticForm ℤ).a ∧
      (⟨n, r, m⟩ : BinaryQuadraticForm ℤ).discrim < 0
  · have hn : 0 < n := hf.1
    have hD : r ^ 2 - 4 * n * m < 0 := hd ▸ hf.2
    have hm : 0 < m := by
      nlinarith [sq_nonneg r]
    rw [ite_eq_left hm, ite_eq_left hf, liftDivisorSum, hc, add_sub_cancel_right]
    refine Finset.sum_congr rfl fun d hd' ↦ congrArg _ ?_
    have hd0 : (0 : ℤ) < (d : ℤ) ^ 2 :=
      pow_pos (Int.natCast_pos.mpr (Nat.pos_of_mem_divisors hd')) 2
    have h₁ : (d : ℤ) ^ 2 * (4 * (n * m / (d : ℤ) ^ 2) - (r / d) ^ 2) = 4 * n * m - r ^ 2 := by
      simpa using sq_mul_disc_level 1 n r m hd'
    have h₂ : -(⟨n, r, m⟩ : BinaryQuadraticForm ℤ).discrim / (d : ℤ) ^ 2 =
        4 * (n * m / (d : ℤ) ^ 2) - (r / d) ^ 2 := by
      rw [hd, neg_sub, ← h₁, Int.mul_ediv_cancel_left _ hd0.ne']
    have h₃ : 0 ≤ 4 * (n * m / (d : ℤ) ^ 2) - (r / d) ^ 2 := by
      nlinarith
    rw [h₂]
    exact jacobiCoeff_eq_jacobiDiscrCoeff φ _ hφ.1 (Int.toNat_of_nonneg h₃).symm
  · rw [ite_eq_right hf]
    refine ite_eq_right_iff.mpr fun hm ↦ Finset.sum_eq_zero fun d hd' ↦ ?_
    have hd0 : (0 : ℤ) < (d : ℤ) ^ 2 :=
      pow_pos (Int.natCast_pos.mpr (Nat.pos_of_mem_divisors hd')) 2
    have h₁ : (d : ℤ) ^ 2 * (4 * (n * m / (d : ℤ) ^ 2) - (r / d) ^ 2) = 4 * n * m - r ^ 2 := by
      simpa using sq_mul_disc_level 1 n r m hd'
    have hD : 4 * n * m - r ^ 2 ≤ 0 := by
      by_contra h
      exact hf ⟨by nlinarith [sq_nonneg r], by rw [hd]; linarith⟩
    have h₂ : 4 * (n * m / (d : ℤ) ^ 2) ≤ (r / d) ^ 2 := by
      nlinarith
    rw [jacobiCoeff_eq_zero_of_mem_jacobiFourierSupported hφ.2 (by simpa using h₂), mul_zero]

lemma hasSum_maassLift (hφ : φ ∈ jacobiCuspFormSpace (k + 1) 1)
    (W : SiegelUpperHalfSpace (Fin 2)) : HasSum (fun T : ℤ × ℤ × ℤ ↦
      maassFormCoeff k (fun N ↦ jacobiDiscrCoeff φ N.toNat) ⟨T.1, T.2.1, T.2.2⟩ *
        liftExp 1 T.1 T.2.1 T.2.2 W) (maassLift (k + 1) φ W) :=
  (maassLiftTheorem.summable (k + 1) φ hφ.1 W).hasSum.congr_fun fun T ↦ by
    rw [maassCoeff_eq_maassFormCoeff hφ]

variable {p : ℕ}

lemma eq_smul_of_hasSum {κ : ℤ}
    {F G : slashInvariantsOf (TauCeti.detPowerRep ℂ 2 κ) (heckeMonoidAt (Fin 2) p) Γ₂}
    {a b : ℤ × ℤ × ℤ → ℂ} (c : ℂ) (hF : ∀ W, HasSum (fun T : ℤ × ℤ × ℤ ↦
      a T * liftExp 1 T.1 T.2.1 T.2.2 W) ((F : SiegelUpperHalfSpace (Fin 2) → ℂ) W))
    (hG : ∀ W, HasSum (fun T : ℤ × ℤ × ℤ ↦ b T * liftExp 1 T.1 T.2.1 T.2.2 W)
      ((G : SiegelUpperHalfSpace (Fin 2) → ℂ) W)) (hab : ∀ T, b T = c * a T) : G = c • F := by
  refine Subtype.ext (funext fun Z ↦ ?_)
  rw [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  have h : HasSum (fun T : ℤ × ℤ × ℤ ↦ c * (a T * liftExp 1 T.1 T.2.1 T.2.2 Z))
      ((G : SiegelUpperHalfSpace (Fin 2) → ℂ) Z) :=
    (hG Z).congr_fun fun T ↦ by rw [hab T, mul_assoc]
  exact h.unique ((hF Z).mul_left c)

variable [Fact p.Prime] {f : Newform 1 (2 * k)}

lemma jacobiDiscrCoeff_toNat_hecke (hK : ∀ (D : ℤ) (hD : D.IsFundamentalDiscr), D < 0 →
    ∀ n : ℕ, 0 < n → jacobiShimuraCoeff k φ D hD n =
      jacobiDiscrCoeff φ D.natAbs * (qExpansion 1 f.toCuspForm).coeff n) {N : ℤ} (hN : 0 < N)
    (h4 : N % 4 = 0 ∨ N % 4 = 3) : jacobiDiscrCoeff φ ((p : ℤ) ^ 2 * N).toNat +
      negKronecker p N * (p : ℂ) ^ (k - 1) * jacobiDiscrCoeff φ N.toNat +
        (p : ℂ) ^ (2 * k - 1) * (if (p : ℤ) ^ 2 ∣ N then jacobiDiscrCoeff φ (N / (p : ℤ) ^ 2).toNat
          else 0) = (qExpansion 1 f.toCuspForm).coeff p * jacobiDiscrCoeff φ N.toNat := by
  lift N to ℕ using hN.le
  have e : ((p : ℤ) ^ 2 * N).toNat = p ^ 2 * N := by
    exact_mod_cast Int.toNat_natCast (p ^ 2 * N)
  have hdiv : (if (p : ℤ) ^ 2 ∣ (N : ℤ) then jacobiDiscrCoeff φ ((N : ℤ) / (p : ℤ) ^ 2).toNat
      else 0) = if p ^ 2 ∣ N then jacobiDiscrCoeff φ (N / p ^ 2) else 0 := by
    by_cases hpN : p ^ 2 ∣ N
    · rw [ite_eq_left hpN, ite_eq_left (by exact_mod_cast hpN)]
      rfl
    · rw [ite_eq_right hpN, ite_eq_right (by exact_mod_cast hpN)]
  rw [e, Int.toNat_natCast, hdiv]
  exact jacobiDiscrCoeff_hecke hK (by exact_mod_cast hN) (by omega)

/-- **The Hecke operator `T(p)` on a Maass lift of a Saito–Kurokawa Jacobi form**: if the Kohnen
`D`-th Shimura lifts of `φ ∈ J_{k+1,1}^cusp` are `c(|D|) f`, then the Maass lift `Vφ` satisfies
`Vφ ∣ T(p) = (a_p(f) + p^{k-1} + p^k) Vφ`. -/
lemma heckeOperator_Tp_maassLift (hφ : φ ∈ jacobiCuspFormSpace (k + 1) 1)
    (hK : ∀ (D : ℤ) (hD : D.IsFundamentalDiscr), D < 0 → ∀ n : ℕ, 0 < n →
      jacobiShimuraCoeff k φ D hD n =
        jacobiDiscrCoeff φ D.natAbs * (qExpansion 1 f.toCuspForm).coeff n)
    (hF : maassLift (k + 1) φ ∈
      slashInvariantsOf (TauCeti.detPowerRep ℂ 2 (k + 1)) (heckeMonoidAt (Fin 2) p) Γ₂) :
    heckeOperator (TauCeti.detPowerRep ℂ 2 (k + 1)) (heckeCosetDiag p 0 0 1) ⟨_, hF⟩ =
      ((qExpansion 1 f.toCuspForm).coeff p + (p : ℂ) ^ (k - 1) + (p : ℂ) ^ k) • ⟨_, hF⟩ := by
  have e₁ : 2 * (k + 1) - 3 = 2 * k - 1 := by ring1
  have e₂ : k + 1 - 2 = k - 1 := by ring1
  refine eq_smul_of_hasSum _ (hasSum_maassLift hφ)
    (hasSum_heckeOperator_Tp (F := ⟨_, hF⟩) · (hasSum_maassLift hφ)) fun T ↦ ?_
  refine (heckeTpCoeff_eq (f := ⟨T.1, T.2.1, T.2.2⟩) (Fact.out : p.Prime).ne_zero (k + 1)
    _).trans ?_
  rw [e₁, e₂]
  exact heckeTp_maassFormCoeff (fun N hN h4 ↦ jacobiDiscrCoeff_toNat_hecke hK hN h4)
    fun N hN h4 ↦ jacobiDiscrCoeff_eq_zero_of_emod_four (by omega)

/-- **The Hecke operator `T_1(p²)` on a Maass lift of a Saito–Kurokawa Jacobi form**: if the
Kohnen `D`-th Shimura lifts of `φ ∈ J_{k+1,1}^cusp` are `c(|D|) f`, then the Maass lift `Vφ`
satisfies `Vφ ∣ T_1(p²) = ((p + 1) p^{k-2} a_p(f) + p^{2k-2} - p^{2k-4}) Vφ`. -/
lemma heckeOperator_T₁_maassLift (hφ : φ ∈ jacobiCuspFormSpace (k + 1) 1)
    (hK : ∀ (D : ℤ) (hD : D.IsFundamentalDiscr), D < 0 → ∀ n : ℕ, 0 < n →
      jacobiShimuraCoeff k φ D hD n =
        jacobiDiscrCoeff φ D.natAbs * (qExpansion 1 f.toCuspForm).coeff n)
    (hF : maassLift (k + 1) φ ∈
      slashInvariantsOf (TauCeti.detPowerRep ℂ 2 (k + 1)) (heckeMonoidAt (Fin 2) p) Γ₂) :
    heckeOperator (TauCeti.detPowerRep ℂ 2 (k + 1)) (heckeCosetDiag p 0 1 0) ⟨_, hF⟩ =
      (((p : ℂ) + 1) * (p : ℂ) ^ (k - 2) * (qExpansion 1 f.toCuspForm).coeff p +
        (p : ℂ) ^ (2 * k - 2) - (p : ℂ) ^ (2 * k - 4)) • ⟨_, hF⟩ := by
  have e₁ : 3 * (k + 1) - 6 = 3 * k - 3 := by ring1
  have e₂ : 2 * (k + 1) - 6 = 2 * k - 4 := by ring1
  have e₃ : k + 1 - 3 = k - 2 := by ring1
  refine eq_smul_of_hasSum _ (hasSum_maassLift hφ)
    (hasSum_heckeOperator_T₁ (F := ⟨_, hF⟩) · (hasSum_maassLift hφ)) fun T ↦ ?_
  refine (heckeT₁Coeff_eq (f := ⟨T.1, T.2.1, T.2.2⟩) (k + 1) _).trans ?_
  rw [e₁, e₂, e₃]
  exact heckeT₁_maassFormCoeff (fun N hN h4 ↦ jacobiDiscrCoeff_toNat_hecke hK hN h4)
    fun N hN h4 ↦ jacobiDiscrCoeff_eq_zero_of_emod_four (by omega)

/-- **The Maass lift of a nonzero Jacobi cusp form of index `1` is nonzero.** -/
lemma maassLift_ne_zero (hφ : φ ∈ jacobiCuspFormSpace k 1) (h₀ : φ ≠ 0) : maassLift k φ ≠ 0 :=
  fun h ↦ gritsenkoLift_ne_zero (L := 1) hφ h₀ <| (maassLift_eq_gritsenkoLift hφ).symm.trans h

/-- **The spin `L`-function of the Saito–Kurokawa lifts** (LMFDB `mf.siegel.lift.saito_kurokawa`):
`SiegelUpperHalfSpace.SaitoKurokawaSpinTheorem` holds. Every Saito–Kurokawa lift `F = Vφ` of
`f ∈ S_{2k}(SL(2, ℤ))` is nonzero, and at every prime `p` it is an eigenvector of `T(p)` and
`T_1(p²)` with the eigenvalues `a_p(f) + p^{k-1} + p^k` and
`(p + 1) p^{k-2} a_p(f) + p^{2k-2} - p^{2k-4}`, so that its spinor Euler factor at `p` is
`Q_p(f, X)(1 - p^{k-1} X)(1 - p^k X)`: `L^spin(F, s) = L(f, s) ζ(s - k + 1) ζ(s - k)` in the
classical normalisation, the knowl's `L(s, F) = L(s, f) ζ(s + 1/2) ζ(s - 1/2)` in the analytic one
(`HeckeRing.GL2.Newform.eval_spinorEulerFactor_saitoKurokawa`). -/
lemma saitoKurokawaSpinTheorem : SaitoKurokawaSpinTheorem := by
  refine saitoKurokawaSpinTheorem_of_heckeOperator fun k f F hF p _ ↦ ?_
  have hF' : F ∈ slashInvariantsOf (TauCeti.detPowerRep ℂ 2 (k + 1)) (heckeMonoidAt (Fin 2) p) Γ₂ :=
    fun γ hγ ↦ hF.mem_slashInvariants γ hγ
  rcases hF with ⟨φ, hφ, h₀, hK, rfl⟩
  exact ⟨hF', maassLift_ne_zero hφ h₀, heckeOperator_Tp_maassLift hφ hK hF',
    heckeOperator_T₁_maassLift hφ hK hF'⟩

end SiegelUpperHalfSpace
