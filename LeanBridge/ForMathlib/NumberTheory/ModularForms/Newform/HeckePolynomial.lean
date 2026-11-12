import LeanBridge.ForMathlib.NumberTheory.ModularForms.Analytic.Satake
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Degeneracy
import TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform

/-!
# The Hecke polynomial of a newform as a determinant of `T_p`

Let `f` be a newform of level `N`, weight `k` and character `χ`, and `p ∤ N` a prime. The LMFDB
defines the Satake parameters of `f` at `p` (LMFDB `cmf.satake_parameters`) through the Hecke
polynomial `L_p(t) = 1 - a_p t + χ(p) p^{k-1} t²`, which it also writes `det(1 - t T_p)` with `a_p`
the trace of `T_p`. Read on `S_k(N, χ)`, where `f` lives, that determinant has degree
`dim S_k(N, χ)` and is `1 - a_p t` on the line of `f`, so it is never `L_p(t)`. The identity holds
for the Hecke operator `T_p` of level `pN`, which is `U_p` since `p ∣ pN`, on the two-dimensional
space of `p`-oldforms of `f`, spanned by `f(z)` and `f(pz)`. There `T_p f(pz) = f(z)` (Tau Ceti's
`HeckeRing.GL2.heckeTCuspNat_levelRaise_mul`, that is `U_p V_p = 1`) and
`T_p f = a_p f - χ(p) p^{k-1} f(pz)` (Tau Ceti's `HeckeRing.GL2.heckeTCuspNat_levelRaise_eq_sub`,
with `T_p f = a_p f` at level `N`), so in the basis `(f(z), f(pz))` the operator `T_p` has the
matrix `(a_p 1; -χ(p) p^{k-1} 0)`, of trace `a_p`, and `det(1 - t T_p) = L_p(t)`. With the
factorisation of `L_p` proved in `LeanBridge.ForMathlib.NumberTheory.ModularForms.Analytic.Satake`,
the Satake parameters are the reciprocal roots of `det(1 - p^{-(k-1)/2} t T_p)`.

## Main definitions

* `HeckeRing.GL2.Newform.oldformOne`, `HeckeRing.GL2.Newform.oldformP`: `f(z)` and `f(pz)`, as cusp
  forms of level `pN`.
* `HeckeRing.GL2.Newform.pOldSpace`: the space of `p`-oldforms of `f`, which they span.
* `HeckeRing.GL2.Newform.pOldSpaceBasis`: its basis `(f(z), f(pz))`.
* `HeckeRing.GL2.Newform.pOldSpaceHeckeT`: the Hecke operator `T_p` of level `pN` on it.

## Main results

* `HeckeRing.GL2.Newform.finrank_pOldSpace`: the space of `p`-oldforms of `f` has dimension `2`.
* `HeckeRing.GL2.Newform.trace_pOldSpaceHeckeT` (LMFDB `cmf.satake_parameters`): `a_p` is the
  trace of `T_p` on it.
* `HeckeRing.GL2.Newform.det_one_sub_smul_pOldSpaceHeckeT` (LMFDB `cmf.satake_parameters`):
  `det(1 - t T_p) = 1 - a_p t + χ(p) p^{k-1} t²` on it.
* `HeckeRing.GL2.Newform.prod_map_one_sub_mul_normalizedSatakeParameters_eq_det` (LMFDB
  `cmf.satake_parameters`): the Satake parameters are the reciprocal roots of
  `det(1 - p^{-(k-1)/2} t T_p)`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.6.
-/

open UpperHalfPlane Matrix SpecialLinearGroup CongruenceSubgroup TauCeti Module

open scoped MatrixGroups

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) (p n : ℕ) (t : ℂ)

lemma diamondOpCuspNat_toCuspForm (hpN : p.Coprime N) :
    diamondOpCuspNat k p f.toCuspForm = f.dirichletLift p • f.toCuspForm := by
  rw [diamondOpCuspNat_of_coprime k hpN, f.dirichletLift_apply_of_coprime hpN,
    diamondOpCusp_apply_of_mem_cuspFormCharSpace k f.χ _ f.mem_charSpace]

/-- The newform `f`, as a cusp form of level `pN`: the level raise `V_1 f`, with the same
`q`-expansion. -/
noncomputable def oldformOne : CuspForm ((Gamma1 (p * N)).map (mapGL ℝ)) k :=
  CuspForm.levelRaise 1 (Gamma1_map_le_conjAct_scaleGL_of_dvd <| mul_dvd_mul_right (one_dvd p) N)
    f.toCuspForm

lemma qExpansion_coeff_oldformOne :
    (qExpansion 1 (f.oldformOne p)).coeff n = (qExpansion 1 f.toCuspForm).coeff n := by
  rw [oldformOne, CuspForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map N)
    (one_mem_strictPeriods_Gamma1_map _)]
  simp

variable [Fact p.Prime]

/-- The cusp form `f(pz)` of level `pN`: the level raise `V_p f` of the newform `f`. -/
noncomputable def oldformP : CuspForm ((Gamma1 (p * N)).map (mapGL ℝ)) k :=
  CuspForm.levelRaise p (Gamma1_map_le_conjAct_scaleGL_of_dvd dvd_rfl) f.toCuspForm

/-- The space of **`p`-oldforms** of the newform `f`: the subspace of `S_k(Γ₁(pN))` spanned by
`f(z)` and `f(pz)`. It has dimension `2` (`finrank_pOldSpace`), and for `p ∤ N` the Hecke operator
`T_p` of level `pN` preserves it (`pOldSpaceHeckeT`). -/
noncomputable def pOldSpace : Submodule ℂ (CuspForm ((Gamma1 (p * N)).map (mapGL ℝ)) k) :=
  Submodule.span ℂ (Set.range ![f.oldformOne p, f.oldformP p])

lemma qExpansion_coeff_oldformP : (qExpansion 1 (f.oldformP p)).coeff n =
    if p ∣ n then (qExpansion 1 f.toCuspForm).coeff (n / p) else 0 := by
  rw [oldformP, CuspForm.qExpansion_levelRaise_coeff (one_mem_strictPeriods_Gamma1_map N)
    (one_mem_strictPeriods_Gamma1_map _)]

lemma heckeTCuspNat_oldformP : heckeTCuspNat k p (f.oldformP p) = f.oldformOne p := by
  rw [oldformP, oldformOne]
  simpa only [mul_one] using
    heckeTCuspNat_levelRaise_mul k (by rw [mul_one] : p * 1 * N ∣ p * N) f.toCuspForm

lemma heckeTCuspNat_oldformOne (hpN : p.Coprime N) : heckeTCuspNat k p (f.oldformOne p) =
    (qExpansion 1 f.toCuspForm).coeff p • f.oldformOne p -
      (f.dirichletLift p * (p : ℂ) ^ (k - 1)) • f.oldformP p := by
  rw [oldformOne, heckeTCuspNat_levelRaise_eq_sub k Fact.out (Nat.coprime_one_right p)
    (by rw [one_mul] : 1 * p * N ∣ p * N), f.heckeTCuspNat_eq_qExpansion_coeff_smul Fact.out,
    f.diamondOpCuspNat_toCuspForm p hpN, ← CuspForm.levelRaiseₗ_apply, map_smul,
    ← CuspForm.levelRaiseₗ_apply, map_smul, CuspForm.levelRaiseₗ_apply,
    CuspForm.levelRaiseₗ_apply, smul_smul, mul_comm (f.dirichletLift p)]
  simp only [one_mul]
  rfl

lemma linearIndependent_oldformOne_oldformP :
    LinearIndependent ℂ ![f.oldformOne p, f.oldformP p] := by
  refine LinearIndependent.pair_iff.mpr fun s u hsu ↦ ?_
  have hc (m : ℕ) : s * (qExpansion 1 f.toCuspForm).coeff m +
      u * (if p ∣ m then (qExpansion 1 f.toCuspForm).coeff (m / p) else 0) = 0 := by
    have h : (qExpansion 1 ⇑(s • f.oldformOne p + u • f.oldformP p)).coeff m = 0 := by
      rw [hsu, FunLike.coe_zero, qExpansion_zero, map_zero]
    rwa [FunLike.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_Gamma1_map _),
      FunLike.coe_smul, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map _),
      FunLike.coe_smul, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1_map _),
      map_add, map_smul, map_smul, qExpansion_coeff_oldformOne, qExpansion_coeff_oldformP,
      smul_eq_mul, smul_eq_mul] at h
  have hs : s = 0 := by
    simpa [(Fact.out : p.Prime).ne_one] using hc 1
  refine ⟨hs, ?_⟩
  simpa [hs, Nat.div_self (Fact.out : p.Prime).pos] using hc p

lemma heckeTCuspNat_mem_pOldSpace (hpN : p.Coprime N) :
    ∀ g ∈ f.pOldSpace p, heckeTCuspNat k p g ∈ f.pOldSpace p := by
  have h : Submodule.map (heckeTCuspNat k p) (f.pOldSpace p) ≤ f.pOldSpace p := by
    rw [pOldSpace, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    fin_cases i
    · simp only [Fin.zero_eta, cons_val_zero, f.heckeTCuspNat_oldformOne p hpN]
      exact sub_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
    · simp only [Fin.mk_one, cons_val_one, cons_val_fin_one, f.heckeTCuspNat_oldformP p]
      exact Submodule.subset_span ⟨0, rfl⟩
  exact fun g hg ↦ h (Submodule.mem_map_of_mem hg)

/-- The basis `(f(z), f(pz))` of the space of `p`-oldforms of `f`. -/
noncomputable def pOldSpaceBasis : Module.Basis (Fin 2) ℂ (f.pOldSpace p) :=
  Basis.span (f.linearIndependent_oldformOne_oldformP p)

lemma coe_pOldSpaceBasis (i : Fin 2) :
    (f.pOldSpaceBasis p i : CuspForm ((Gamma1 (p * N)).map (mapGL ℝ)) k) =
      ![f.oldformOne p, f.oldformP p] i :=
  congrArg Subtype.val (Basis.span_apply _ i)

/-- The **Hecke operator `T_p` of level `pN` on the `p`-oldforms** of a newform `f` of level `N`,
for a prime `p ∤ N`: the restriction of `T_p`, which is `U_p` at level `pN`, to the span of `f(z)`
and `f(pz)`, which it preserves. -/
noncomputable def pOldSpaceHeckeT (hpN : p.Coprime N) : Module.End ℂ (f.pOldSpace p) :=
  (heckeTCuspNat k p).restrict (f.heckeTCuspNat_mem_pOldSpace p hpN)

lemma toMatrix_pOldSpaceHeckeT (hpN : p.Coprime N) :
    LinearMap.toMatrix (f.pOldSpaceBasis p) (f.pOldSpaceBasis p) (f.pOldSpaceHeckeT p hpN) =
      !![(qExpansion 1 f.toCuspForm).coeff p, 1; -(f.dirichletLift p * (p : ℂ) ^ (k - 1)), 0] := by
  rw [← LinearMap.toMatrix_toLin (f.pOldSpaceBasis p) (f.pOldSpaceBasis p)
    !![(qExpansion 1 f.toCuspForm).coeff p, 1; -(f.dirichletLift p * (p : ℂ) ^ (k - 1)), 0]]
  congr 1
  refine (f.pOldSpaceBasis p).ext fun i ↦ Subtype.ext ?_
  rw [toLin_self, Fin.sum_univ_two, pOldSpaceHeckeT]
  fin_cases i
  · simp [coe_pOldSpaceBasis, f.heckeTCuspNat_oldformOne p hpN, sub_eq_add_neg]
  · simp [coe_pOldSpaceBasis, f.heckeTCuspNat_oldformP p]

/-- **The determinant of `1 - t T_p` on the `p`-oldforms is the Hecke polynomial** (LMFDB
`cmf.satake_parameters`): for a newform `f` of level `N` and a prime `p ∤ N`, the Hecke operator
`T_p` of level `pN` (that is, `U_p`) acts on the span of `f(z)` and `f(pz)` with
`det(1 - t T_p) = 1 - a_p t + χ(p) p^{k-1} t² = L_p(t)`. -/
lemma det_one_sub_smul_pOldSpaceHeckeT (hpN : p.Coprime N) :
    LinearMap.det (1 - t • f.pOldSpaceHeckeT p hpN) = 1 - (qExpansion 1 f.toCuspForm).coeff p * t +
      f.dirichletLift p * (p : ℂ) ^ (k - 1) * t ^ 2 := by
  rw [← LinearMap.det_toMatrix (f.pOldSpaceBasis p), map_sub, map_smul, LinearMap.toMatrix_one,
    f.toMatrix_pOldSpaceHeckeT p hpN, det_fin_two]
  simp
  ring1

/-- **`a_p` is the trace of `T_p` on the `p`-oldforms** (LMFDB `cmf.satake_parameters`): for a
newform `f` of level `N` and a prime `p ∤ N`, the Hecke operator `T_p` of level `pN` acts on the
span of `f(z)` and `f(pz)` with trace `a_p`. -/
lemma trace_pOldSpaceHeckeT (hpN : p.Coprime N) :
    LinearMap.trace ℂ _ (f.pOldSpaceHeckeT p hpN) = (qExpansion 1 f.toCuspForm).coeff p := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (f.pOldSpaceBasis p), f.toMatrix_pOldSpaceHeckeT p hpN,
    trace_fin_two]
  simp

/-- **The space of `p`-oldforms of a newform has dimension `2`**: `f(z)` and `f(pz)` are linearly
independent, by their `q`-expansion coefficients at `1` and at `p`. -/
lemma finrank_pOldSpace : Module.finrank ℂ (f.pOldSpace p) = 2 :=
  (finrank_span_eq_card (f.linearIndependent_oldformOne_oldformP p)).trans (Fintype.card_fin 2)

/-- **The Satake parameters are the reciprocal roots of `det(1 - p^{-(k-1)/2} t T_p)`** (LMFDB
`cmf.satake_parameters`): for a newform `f` of level `N` and a prime `p ∤ N`,
`(1 - α_p t)(1 - β_p t) = det(1 - p^{-(k-1)/2} t T_p)` for its Satake parameters `{α_p, β_p}`, with
`T_p` the Hecke operator of level `pN` on the span of `f(z)` and `f(pz)`. -/
lemma prod_map_one_sub_mul_normalizedSatakeParameters_eq_det (hpN : p.Coprime N) :
    ((f.normalizedSatakeParameters p).map fun α ↦ 1 - α * t).prod =
      LinearMap.det (1 - (t / ((p : ℝ) ^ (((k : ℝ) - 1) / 2) : ℝ)) • f.pOldSpaceHeckeT p hpN) := by
  rw [f.det_one_sub_smul_pOldSpaceHeckeT p _ hpN,
    f.prod_map_one_sub_mul_normalizedSatakeParameters p (Fact.out : p.Prime).ne_zero]

end HeckeRing.GL2.Newform
