import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.ClassicalLiftCentral
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.ClassicalLiftCuspidal
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.Hecke
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.Delta
import TauCeti.NumberTheory.ModularForms.HeckeSlash.Operators
import TauCeti.NumberTheory.ModularForms.Newforms.Coefficient
import TauCeti.NumberTheory.ModularForms.Newforms.RingEigenvalue

/-!
# The Hecke eigenvalues of the adelic lift

Let `f` be a cusp form of weight `k` on `Γ₁(N)` with nebentypus `χ`, `φ_f` its adelic lift
(`AdelicGL2.adelicLift`), and `v` the place of a prime `p ∤ N`. With the uniformizer `p` of `ℚ_p`
(`AdelicGL2.primeUnit`) and the representatives `-b`, `0 ≤ b < p`, of the residue field
(`AdelicGL2.negResidueRep`), the Hecke operator `T_v` (`AdelicGL2.heckeOp`) is the sum of the right
translates of `φ_f` by the matrices `(p, -b; 0, 1)` and `(1, 0; 0, p) = p (1 / p, 0; 0, 1)` at `v`.
The matrices `δ_b = (p, -b; 0, 1)` and `δ = (1 / p, 0; 0, 1)` of `GL₂(ℚ)` lie in `K₁(N)` at the
places other than `v`, so the master formula gives `φ_f(x δ_{b, v}) = Φ_f(δ_b⁻¹ x)` and
`φ_f(x δ_v) = Φ_f(δ⁻¹ x)` for `x ∈ GL₂(ℝ)`, with `δ_b⁻¹ = p⁻¹ (1, b; 0, p)` and
`δ⁻¹ = (p, 0; 0, 1)`, while the scalar `p` at `v` contributes the central character `χ(p)`. So
`T_v φ_f = p ^ (1 - k / 2) φ_{T_p f}` for the classical Hecke operator
`T_p f = ∑_b f ∣[k] (1, b; 0, p) + χ(p) f ∣[k] (p, 0; 0, 1)` of Tau Ceti
(`HeckeRing.GL2.coe_heckeTCuspNat_prime`), the factor `p ^ (1 - k / 2)` coming from the
normalisation of `Φ_f` against Mathlib's slash operator.

For a newform `f`, normalised by `a₁ = 1`, `T_p f = a_p f`, so `φ_f` is a Hecke eigenform of level
`N` with eigenvalue `a_v = p ^ (1 - k / 2) a_p` at `p ∤ N`, and its Euler factor in the arithmetic
normalisation of weight `k - 1` is the LMFDB's `1 - a_p T + χ(p) p ^ (k - 1) T²`. The newform `Δ`
of level one and weight twelve (`HeckeRing.GL2.deltaNewform`) gives a concrete nonzero cuspidal
Hecke eigenform on `GL₂(𝔸_ℚ)`, its cuspidality coming from `AdelicGL2.isCuspidal_adelicLift`.

## Main definitions

* `AdelicGL2.primeUnit`: the prime `p` as a unit of `ℚ_p`.
* `AdelicGL2.negResidueRep`: the representatives `-b`, `0 ≤ b < p`, of the residue field of `ℚ_p`.
* `AdelicGL2.normalizedSlashAddHom`: `F ↦ Φ_F(h)` as an additive map.
* `AdelicGL2.heckeUpperMat`, `AdelicGL2.heckeLowerMat`: the matrices `δ_b` and `δ` of `GL₂(ℚ)`.

## Main results

* `AdelicGL2.heckeOp_adelicLift`: `T_v φ_f = p ^ (1 - k / 2) φ_{T_p f}` for `p ∤ N`.
* `AdelicGL2.adelicLift_ne_zero`: the adelic lift of a nonzero cusp form is nonzero.
* `AdelicGL2.isHeckeEigenform_adelicLift`: the adelic lift of a newform is a Hecke eigenform.
* `AdelicGL2.heckeEigenvalue_adelicLift`: its eigenvalue at `p ∤ N` is `p ^ (1 - k / 2) a_p`.
* `AdelicGL2.arithmeticEulerFactor_adelicLift`: its Euler factor at `p ∤ N` is
  `1 - a_p T + χ(p) p ^ (k - 1) T²`.
* `AdelicGL2.isHeckeEigenform_adelicLift_deltaNewform`,
  `AdelicGL2.isCuspidal_adelicLift_deltaNewform`: the adelic lift of `Δ` is a cuspidal Hecke
  eigenform.
-/

open Matrix hiding mul_inv_rev one_zpow zpow_mul zpow_neg zpow_neg_one

open IsDedekindDomain HeightOneSpectrum NumberField Polynomial Rat UpperHalfPlane TauCeti
  GlobalNumberFields ValuationSubring WithZero HeckeRing GL2

open FiniteAdeleRing (integralAdeles mem_integralAdeles)

open mixedEmbedding (mixedSpace)

open scoped AdeleRing Classical MatrixGroups ModularForm

namespace AdelicGL2

section Valuation

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

lemma valued_intCast_eq_intValuation (z : ℤ) :
    Valued.v (z : v.adicCompletion K) = v.intValuation (z : R) := by
  rw [← map_intCast (algebraMap R (v.adicCompletion K)) z]
  exact (v.valuedAdicCompletion_eq_valuation (z : R)).trans (v.valuation_of_algebraMap (z : R))

lemma valued_natCast_eq_intValuation (n : ℕ) :
    Valued.v (n : v.adicCompletion K) = v.intValuation (n : R) := by
  have h : Valued.v (((n : ℤ) : ℤ) : v.adicCompletion K) = v.intValuation ((n : ℤ) : R) :=
    valued_intCast_eq_intValuation v (n : ℤ)
  rwa [Int.cast_natCast, Int.cast_natCast] at h

end Valuation

section Place

variable (v : HeightOneSpectrum (𝓞 ℚ))

lemma prime_absNorm_asIdeal : (Ideal.absNorm v.asIdeal).Prime := by
  rw [HeightOneSpectrum.absNorm_asIdeal]
  exact HeightOneSpectrum.prime_natGenerator v

lemma algebraMap_finiteAdeleRing_apply (q : ℚ) :
    (algebraMap ℚ 𝔸ᶠ[ℚ] q) v = (q : v.adicCompletion ℚ) :=
  eq_ratCast ((evalRingHom v).comp (algebraMap ℚ 𝔸ᶠ[ℚ])) q

lemma valued_natCast_absNorm :
    Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion ℚ) = exp (-1) := by
  rw [valued_natCast_eq_intValuation v, v.intValuation_singleton
    (Nat.cast_ne_zero.mpr (prime_absNorm_asIdeal v).ne_zero)
    (RingOfIntegers.ideal_span_absNorm_eq_self v.asIdeal).symm]

lemma valued_intCast_le_iff (z : ℤ) :
    Valued.v (z : v.adicCompletion ℚ) ≤ exp (-1) ↔ ((Ideal.absNorm v.asIdeal : ℕ) : ℤ) ∣ z := by
  have h₂ : v.intValuation (z : 𝓞 ℚ) ≤ exp (-((1 : ℕ) : ℤ)) ↔
      ((HeightOneSpectrum.natGenerator v : ℕ) : ℤ) ^ 1 ∣ z :=
    HeightOneSpectrum.intValuation_intCast_le_exp_neg_iff v
  rw [Nat.cast_one, pow_one, ← HeightOneSpectrum.absNorm_asIdeal] at h₂
  rw [valued_intCast_eq_intValuation v]
  exact h₂

lemma valued_natCast_absNorm_of_ne {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : w.adicCompletion ℚ) = 1 := by
  have hnot : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h ↦ by
    have hle : v.asIdeal ≤ w.asIdeal := by
      rw [← RingOfIntegers.ideal_span_absNorm_eq_self v.asIdeal]
      exact (Ideal.span_singleton_le_iff_mem _).mpr h
    exact hw (HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top hle).symm)
  rw [valued_natCast_eq_intValuation w, intValuation_eq_one_iff.mpr hnot]

/-- The prime `p` of the place `v` of `ℚ`, as a unit of `ℚ_p`: a uniformizer. -/
noncomputable def primeUnit : (v.adicCompletion ℚ)ˣ :=
  Units.mk0 ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion ℚ) fun h ↦ by
    have h₁ : Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion ℚ) = exp (-1) :=
      valued_natCast_absNorm v
    rw [h, map_zero] at h₁
    exact exp_ne_zero h₁.symm

lemma coe_primeUnit : (primeUnit v : v.adicCompletion ℚ) = (Ideal.absNorm v.asIdeal : ℕ) :=
  rfl

lemma isUniformizer_primeUnit :
    (v.adicCompletionIntegers ℚ).IsUniformizer (primeUnit v : v.adicCompletion ℚ) :=
  isUniformizer_of_valued_eq (valued_natCast_absNorm v)

lemma inv_primeUnit_mul_mem_iff {x : v.adicCompletion ℚ} :
    (primeUnit v : v.adicCompletion ℚ)⁻¹ * x ∈ v.adicCompletionIntegers ℚ ↔
      Valued.v x ≤ exp (-1) := by
  rw [mem_adicCompletionIntegers, map_mul, map_inv₀, coe_primeUnit, valued_natCast_absNorm,
    inv_exp, neg_neg]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h₂ : exp (-1) * (exp 1 * Valued.v x) ≤ exp (-1) * 1 := mul_le_mul' le_rfl h
    rwa [← mul_assoc, ← exp_add, neg_add_cancel, exp_zero, one_mul, mul_one] at h₂
  · have h₂ : exp 1 * Valued.v x ≤ exp 1 * exp (-1) := mul_le_mul' le_rfl h
    rwa [← exp_add, add_neg_cancel, exp_zero] at h₂

/-- The representatives `-b`, `0 ≤ b < p`, of the residue field of `ℚ_p`, for the prime `p` of the
place `v` of `ℚ`. -/
noncomputable def negResidueRep (b : Fin (Ideal.absNorm v.asIdeal)) : v.adicCompletion ℚ :=
  -(((b : ℕ) : ℤ) : v.adicCompletion ℚ)

lemma isResidueSystem_negResidueRep : (v.adicCompletionIntegers ℚ).IsResidueSystem
    (primeUnit v : v.adicCompletion ℚ) (negResidueRep v) := by
  have hp₀ : (0 : ℤ) < (Ideal.absNorm v.asIdeal : ℕ) := by
    exact_mod_cast (prime_absNorm_asIdeal v).pos
  refine ⟨fun b ↦ neg_mem (intCast_mem _ _), fun x hx ↦ ?_⟩
  rcases v.exists_valued_sub_le (K := ℚ) ⟨x, hx⟩ 1 with ⟨a, ha⟩
  have ha₁ : ((Rat.ringOfIntegersEquiv a : ℤ) : 𝓞 ℚ) = a :=
    (eq_intCast Rat.ringOfIntegersEquiv.symm _).symm.trans
      (Rat.ringOfIntegersEquiv.symm_apply_apply a)
  rw [← ha₁, map_intCast, Nat.cast_one] at ha
  have hb₀ : 0 ≤ (-(Rat.ringOfIntegersEquiv a : ℤ)) % ((Ideal.absNorm v.asIdeal : ℕ) : ℤ) :=
    Int.emod_nonneg _ hp₀.ne'
  have hb₁ : (-(Rat.ringOfIntegersEquiv a : ℤ)) % ((Ideal.absNorm v.asIdeal : ℕ) : ℤ) <
      (Ideal.absNorm v.asIdeal : ℕ) :=
    Int.emod_lt_of_pos _ hp₀
  let b₀ : Fin (Ideal.absNorm v.asIdeal) :=
    ⟨((-(Rat.ringOfIntegersEquiv a : ℤ)) % ((Ideal.absNorm v.asIdeal : ℕ) : ℤ)).toNat, by omega⟩
  have hb : (((b₀ : ℕ) : ℤ) : ℤ) =
      (-(Rat.ringOfIntegersEquiv a : ℤ)) % ((Ideal.absNorm v.asIdeal : ℕ) : ℤ) :=
    Int.toNat_of_nonneg hb₀
  have hd : ((Ideal.absNorm v.asIdeal : ℕ) : ℤ) ∣ (Rat.ringOfIntegersEquiv a : ℤ) + (b₀ : ℕ) :=
    ⟨-((-(Rat.ringOfIntegersEquiv a : ℤ)) / ((Ideal.absNorm v.asIdeal : ℕ) : ℤ)), by
      rw [hb, Int.emod_def]
      ring1⟩
  have hx₀ : Valued.v (x - -(((b₀ : ℕ) : ℤ) : v.adicCompletion ℚ)) ≤ exp (-1) := by
    have he : x - -(((b₀ : ℕ) : ℤ) : v.adicCompletion ℚ) =
        (x - ((Rat.ringOfIntegersEquiv a : ℤ) : v.adicCompletion ℚ)) +
          (((Rat.ringOfIntegersEquiv a : ℤ) + (b₀ : ℕ) : ℤ) : v.adicCompletion ℚ) := by
      push_cast
      ring1
    rw [he]
    exact Valuation.map_add_le _ ha ((valued_intCast_le_iff v _).mpr hd)
  refine ⟨b₀, (inv_primeUnit_mul_mem_iff v).mpr hx₀, fun b hb' ↦ Fin.ext ?_⟩
  have hb₂ : Valued.v (x - -(((b : ℕ) : ℤ) : v.adicCompletion ℚ)) ≤ exp (-1) :=
    (inv_primeUnit_mul_mem_iff v).mp hb'
  have he : (((b : ℕ) - (b₀ : ℕ) : ℤ) : v.adicCompletion ℚ) =
      (x - -(((b : ℕ) : ℤ) : v.adicCompletion ℚ)) -
        (x - -(((b₀ : ℕ) : ℤ) : v.adicCompletion ℚ)) := by
    push_cast
    ring1
  have hd₂ : ((Ideal.absNorm v.asIdeal : ℕ) : ℤ) ∣ ((b : ℕ) - (b₀ : ℕ) : ℤ) := by
    rw [← valued_intCast_le_iff v, he]
    exact (Valuation.map_sub _ _ _).trans (max_le hb₂ hx₀)
  have hmod : (b₀ : ℕ) ≡ (b : ℕ) [MOD Ideal.absNorm v.asIdeal] := Nat.modEq_iff_dvd.mpr hd₂
  rw [← Nat.mod_eq_of_lt b.2, ← Nat.mod_eq_of_lt b₀.2]
  exact hmod.symm

variable {v}

lemma coprime_absNorm_of_not_le {N : ℕ} (hv : ¬Ideal.span {(N : 𝓞 ℚ)} ≤ v.asIdeal) :
    (Ideal.absNorm v.asIdeal).Coprime N := by
  rw [(prime_absNorm_asIdeal v).coprime_iff_not_dvd,
    ← HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd]
  exact fun h ↦ hv ((Ideal.span_singleton_le_iff_mem _).mpr h)

end Place

section Away

variable {F : Type*} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
  {y : GL (Fin 2) 𝔸ᶠ[F]}

lemma atPlace_awayFrom_of_ne {w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) :
    atPlace w (awayFrom v y) = atPlace w y := by
  rw [awayFrom, map_mul, map_inv, atPlace_localGL_of_ne hw, inv_one, one_mul]

lemma localGL_atPlace : localGL v (atPlace v y) = y * (awayFrom v y)⁻¹ :=
  eq_mul_inv_of_mul_eq (localGL_mul_awayFrom v y)

lemma awayFrom_mem_levelOne_of_forall {𝔑 : Ideal (𝓞 F)}
    (hy : ∀ w ≠ v, atPlace w y ∈ (w.adicCompletionIntegers F).gl2)
    (h₁₀ : ∀ w ≠ v, (y : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) 1 0 w = 0)
    (h₁₁ : ∀ w ≠ v, (y : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) 1 1 w = 1) : awayFrom v y ∈ levelOne 𝔑 := by
  have hgl (w : HeightOneSpectrum (𝓞 F)) :
      atPlace w (awayFrom v y) ∈ (w.adicCompletionIntegers F).gl2 := by
    rcases eq_or_ne w v with rfl | hw
    · rw [atPlace_awayFrom]
      exact one_mem _
    · rw [atPlace_awayFrom_of_ne hw]
      exact hy w hw
  have h₀ : ((awayFrom v y : GL (Fin 2) 𝔸ᶠ[F]) : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) 1 0 = 0 := by
    refine FiniteAdeleRing.ext F fun w ↦ ?_
    rw [← atPlace_apply]
    rcases eq_or_ne w v with rfl | hw
    · rw [atPlace_awayFrom, Units.val_one, one_apply_ne (by decide)]
      rfl
    · rw [atPlace_awayFrom_of_ne hw, atPlace_apply, h₁₀ w hw]
      rfl
  have h₁ : ((awayFrom v y : GL (Fin 2) 𝔸ᶠ[F]) : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) 1 1 = 1 := by
    refine FiniteAdeleRing.ext F fun w ↦ ?_
    rw [← atPlace_apply]
    rcases eq_or_ne w v with rfl | hw
    · rw [atPlace_awayFrom, Units.val_one, one_apply_eq]
      rfl
    · rw [atPlace_awayFrom_of_ne hw, atPlace_apply, h₁₁ w hw]
      rfl
  refine ⟨fun i j ↦ ⟨mem_integralAdeles.mpr fun w ↦ ?_, mem_integralAdeles.mpr fun w ↦ ?_⟩, ?_, ?_⟩
  · rw [← atPlace_apply]
    exact (hgl w i j).1
  · rw [← atPlace_apply, map_inv]
    exact (hgl w i j).2
  · intro w n _
    rw [h₀]
    simp
  · intro w n _
    rw [h₁, sub_self]
    simp

lemma ofInf_mul_ofFin_map (δ : GL (Fin 2) F) (x : GL (Fin 2) (mixedSpace F)) :
    ofInf F x * ofFin F (GeneralLinearGroup.map (algebraMap F 𝔸ᶠ[F]) δ * y) =
      ofGlobal F δ * ofInf F ((toInf F (ofGlobal F δ))⁻¹ * x) * ofFin F y := by
  refine ext_toInf_toFin ?_ ?_
  · simp
  · simp [toFin_ofGlobal]

end Away

section Lift

variable {k : ℤ} {f : ℍ → ℂ} (h : GL (Fin 2) ℝ)

lemma normalizedSlash_add {g : ℍ → ℂ} :
    normalizedSlash k (f + g) h = normalizedSlash k f h + normalizedSlash k g h := by
  rw [normalizedSlash, normalizedSlash, normalizedSlash, SlashAction.add_slash, Pi.add_apply,
    mul_add]

variable (k) in
/-- The value `Φ_F(h) = |det h| ^ (1 - k / 2) (F ∣[k] h)(i)` at a fixed `h ∈ GL₂(ℝ)`, as an additive
map of the functions `F` on `ℍ`. -/
noncomputable def normalizedSlashAddHom : (ℍ → ℂ) →+ ℂ where
  toFun F := normalizedSlash k F h
  map_zero' := by
    rw [normalizedSlash, SlashAction.zero_slash, Pi.zero_apply, mul_zero]
  map_add' _ _ := normalizedSlash_add h

lemma normalizedSlash_sum {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ) :
    normalizedSlash k (∑ i ∈ s, F i) h = ∑ i ∈ s, normalizedSlash k (F i) h :=
  map_sum (normalizedSlashAddHom k h) F s

lemma classicalFun_smul (c : ℂ) : classicalFun k (c • f) h = c * classicalFun k f h :=
  normalizedSlash_smul_of_pos k (det_posDet_pos h) c

variable (v : HeightOneSpectrum (𝓞 ℚ))

lemma det_heckeUpperMat_ne_zero (b : ℤ) :
    (!![((Ideal.absNorm v.asIdeal : ℕ) : ℚ), -(b : ℚ); 0, 1]).det ≠ 0 := by
  rw [det_fin_two_of, mul_one, mul_zero, sub_zero]
  exact Nat.cast_ne_zero.mpr (prime_absNorm_asIdeal v).ne_zero

/-- The matrix `δ_b = (p, -b; 0, 1)` of `GL₂(ℚ)`, for the prime `p` of the place `v` of `ℚ`: its
component at `v` is a representative of the Hecke operator `T_v`. -/
noncomputable def heckeUpperMat (b : ℤ) : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero _ (det_heckeUpperMat_ne_zero v b)

lemma coe_heckeUpperMat (b : ℤ) : (heckeUpperMat v b : Matrix (Fin 2) (Fin 2) ℚ) =
    !![((Ideal.absNorm v.asIdeal : ℕ) : ℚ), -(b : ℚ); 0, 1] :=
  rfl

lemma det_heckeLowerMat_ne_zero : (!![((Ideal.absNorm v.asIdeal : ℕ) : ℚ)⁻¹, 0; 0, 1]).det ≠ 0 := by
  rw [det_fin_two_of, mul_one, mul_zero, sub_zero]
  exact inv_ne_zero (Nat.cast_ne_zero.mpr (prime_absNorm_asIdeal v).ne_zero)

/-- The matrix `δ = (1 / p, 0; 0, 1)` of `GL₂(ℚ)`, for the prime `p` of the place `v` of `ℚ`: its
component at `v` is `p⁻¹` times a representative of the Hecke operator `T_v`. -/
noncomputable def heckeLowerMat : GL (Fin 2) ℚ :=
  GeneralLinearGroup.mkOfDetNeZero _ (det_heckeLowerMat_ne_zero v)

lemma coe_heckeLowerMat : (heckeLowerMat v : Matrix (Fin 2) (Fin 2) ℚ) =
    !![((Ideal.absNorm v.asIdeal : ℕ) : ℚ)⁻¹, 0; 0, 1] :=
  rfl

lemma atPlace_heckeUpperMat (b : Fin (Ideal.absNorm v.asIdeal)) :
    atPlace v (GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) (heckeUpperMat v (b : ℕ))) =
      heckeRep (primeUnit v) (negResidueRep v) (some b) := by
  refine GeneralLinearGroup.ext fun i j ↦ ?_
  rw [atPlace_apply, GeneralLinearGroup.map_apply, algebraMap_finiteAdeleRing_apply,
    coe_heckeUpperMat]
  fin_cases i <;> fin_cases j <;>
    simp only [heckeRep, negResidueRep, coe_primeUnit, of_apply, cons_val_zero, cons_val_one,
      Fin.zero_eta, Fin.mk_one, Rat.cast_natCast, Rat.cast_neg, Rat.cast_intCast, Rat.cast_zero,
      Rat.cast_one]

lemma heckeRep_none : heckeRep (primeUnit v) (negResidueRep v) none =
    GeneralLinearGroup.scalar (Fin 2) (primeUnit v) *
      atPlace v (GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) (heckeLowerMat v)) := by
  refine GeneralLinearGroup.ext fun i j ↦ ?_
  have hp : ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion ℚ) ≠ 0 := (primeUnit v).ne_zero
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_mul, atPlace_apply,
    GeneralLinearGroup.map_apply, algebraMap_finiteAdeleRing_apply, coe_heckeLowerMat]
  fin_cases i <;> fin_cases j <;>
    simp only [heckeRep, coe_primeUnit, of_apply, cons_val_zero, cons_val_one, Fin.zero_eta,
      Fin.mk_one, Rat.cast_inv, Rat.cast_natCast, Rat.cast_zero, Rat.cast_one, mul_inv_cancel₀ hp,
      mul_zero, mul_one]

lemma inv_natCast_mem_adicCompletionIntegers {w : HeightOneSpectrum (𝓞 ℚ)} (hw : w ≠ v) :
    ((Ideal.absNorm v.asIdeal : ℕ) : w.adicCompletion ℚ)⁻¹ ∈ w.adicCompletionIntegers ℚ := by
  rw [mem_adicCompletionIntegers, map_inv₀, valued_natCast_absNorm_of_ne v hw, inv_one]

lemma awayFrom_heckeUpperMat_mem_levelOne {𝔑 : Ideal (𝓞 ℚ)} (b : ℤ) :
    awayFrom v (GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) (heckeUpperMat v b)) ∈ levelOne 𝔑 := by
  refine awayFrom_mem_levelOne_of_forall
    (fun w hw ↦ mem_gl2_of_apply_mem_of_det (fun i j ↦ ?_) ?_) (fun w _ ↦ ?_) (fun w _ ↦ ?_)
  · rw [atPlace_apply, GeneralLinearGroup.map_apply, algebraMap_finiteAdeleRing_apply,
      coe_heckeUpperMat]
    fin_cases i <;> fin_cases j <;>
      simp only [of_apply, cons_val_zero, cons_val_one, Fin.zero_eta, Fin.mk_one, Rat.cast_natCast,
        Rat.cast_neg, Rat.cast_intCast, Rat.cast_zero, Rat.cast_one]
    · exact natCast_mem _ _
    · exact neg_mem (intCast_mem _ _)
    · exact (w.adicCompletionIntegers ℚ).zero_mem
    · exact (w.adicCompletionIntegers ℚ).one_mem
  · simp only [det_fin_two, atPlace_apply, GeneralLinearGroup.map_apply,
      algebraMap_finiteAdeleRing_apply, coe_heckeUpperMat, of_apply, cons_val_zero, cons_val_one,
      Rat.cast_natCast, Rat.cast_zero, Rat.cast_one, mul_one, mul_zero, sub_zero]
    exact inv_natCast_mem_adicCompletionIntegers v hw
  · rw [GeneralLinearGroup.map_apply, algebraMap_finiteAdeleRing_apply, coe_heckeUpperMat]
    simp
  · rw [GeneralLinearGroup.map_apply, algebraMap_finiteAdeleRing_apply, coe_heckeUpperMat]
    simp

lemma awayFrom_heckeLowerMat_mem_levelOne {𝔑 : Ideal (𝓞 ℚ)} :
    awayFrom v (GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) (heckeLowerMat v)) ∈ levelOne 𝔑 := by
  refine awayFrom_mem_levelOne_of_forall
    (fun w hw ↦ mem_gl2_of_apply_mem_of_det (fun i j ↦ ?_) ?_) (fun w _ ↦ ?_) (fun w _ ↦ ?_)
  · rw [atPlace_apply, GeneralLinearGroup.map_apply, algebraMap_finiteAdeleRing_apply,
      coe_heckeLowerMat]
    fin_cases i <;> fin_cases j <;>
      simp only [of_apply, cons_val_zero, cons_val_one, Fin.zero_eta, Fin.mk_one, Rat.cast_inv,
        Rat.cast_natCast, Rat.cast_zero, Rat.cast_one]
    · exact inv_natCast_mem_adicCompletionIntegers v hw
    · exact (w.adicCompletionIntegers ℚ).zero_mem
    · exact (w.adicCompletionIntegers ℚ).zero_mem
    · exact (w.adicCompletionIntegers ℚ).one_mem
  · simp only [det_fin_two, atPlace_apply, GeneralLinearGroup.map_apply,
      algebraMap_finiteAdeleRing_apply, coe_heckeLowerMat, of_apply, cons_val_zero, cons_val_one,
      Rat.cast_inv, Rat.cast_natCast, Rat.cast_zero, Rat.cast_one, mul_one, mul_zero, sub_zero,
      inv_inv]
    exact natCast_mem _ _
  · rw [GeneralLinearGroup.map_apply, algebraMap_finiteAdeleRing_apply, coe_heckeLowerMat]
    simp
  · rw [GeneralLinearGroup.map_apply, algebraMap_finiteAdeleRing_apply, coe_heckeLowerMat]
    simp

lemma map_heckeUpperMat_inv (b : Fin (Ideal.absNorm v.asIdeal)) :
    (GeneralLinearGroup.map (algebraMap ℚ ℝ) (heckeUpperMat v (b : ℕ)))⁻¹ =
      GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep _ b) *
        GeneralLinearGroup.scalar (Fin 2) (Units.mk0 ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹
          (inv_ne_zero (Nat.cast_ne_zero.mpr (prime_absNorm_asIdeal v).ne_zero))) := by
  have hp : (HeightOneSpectrum.natGenerator v : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (HeightOneSpectrum.prime_natGenerator v).ne_zero
  rw [inv_eq_iff_mul_eq_one]
  refine GeneralLinearGroup.ext fun i j ↦ ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, coe_heckeUpperMat, hp,
      mul_left_comm _ _ ((HeightOneSpectrum.natGenerator v : ℝ))⁻¹]

lemma map_heckeLowerMat_inv : (GeneralLinearGroup.map (algebraMap ℚ ℝ) (heckeLowerMat v))⁻¹ =
    GeneralLinearGroup.map (algebraMap ℚ ℝ) (scaleRep (Ideal.absNorm v.asIdeal)) := by
  have hp : (HeightOneSpectrum.natGenerator v : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (HeightOneSpectrum.prime_natGenerator v).ne_zero
  rw [inv_eq_iff_mul_eq_one]
  refine GeneralLinearGroup.ext fun i j ↦ ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, coe_heckeLowerMat,
      coe_scaleRep _ (HeightOneSpectrum.prime_natGenerator v).pos, hp]

lemma det_map_upperTriRep (b : Fin (Ideal.absNorm v.asIdeal)) :
    ((GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep _ b)).det : ℝ) =
      (Ideal.absNorm v.asIdeal : ℕ) := by
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_map_apply, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, coe_upperTriRep, det_fin_two_of, one_mul, mul_zero, sub_zero, map_natCast]

lemma det_map_scaleRep :
    ((GeneralLinearGroup.map (algebraMap ℚ ℝ) (scaleRep (Ideal.absNorm v.asIdeal))).det : ℝ) =
      (Ideal.absNorm v.asIdeal : ℕ) := by
  rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.val_map_apply, ← RingHom.mapMatrix_apply,
    ← RingHom.map_det, coe_scaleRep _ (prime_absNorm_asIdeal v).pos, det_fin_two_of, mul_one,
    mul_zero, sub_zero, map_natCast]

variable {N : ℕ} [NeZero N] {v}

lemma adelicLift_smul (c : ℂ) : adelicLift N k (c • f) = c • adelicLift N k f :=
  funext fun _ ↦ classicalFun_smul _ c

lemma adelicLift_ofInf_mul_localGL
    (hf : ∀ g ∈ CongruenceSubgroup.Gamma1 N, f ∣[k] SpecialLinearGroup.mapGL ℝ g = f)
    {δ : GL (Fin 2) ℚ}
    (hδ : awayFrom v (GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) δ) ∈
      levelOne (Ideal.span {(N : 𝓞 ℚ)})) (x : GL (Fin 2) (mixedSpace ℚ)) :
    adelicLift N k f (ofInf ℚ x * ofFin ℚ
      (localGL v (atPlace v (GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) δ)))) =
        classicalFun k f ((GeneralLinearGroup.map (algebraMap ℚ ℝ) δ)⁻¹ * ratInfEquiv x) := by
  rw [localGL_atPlace, ofInf_mul_ofFin_map, adelicLift_apply hf _ _ (inv_mem hδ), map_mul, map_inv,
    toInf_ofGlobal, ratInfEquiv_map_mixedEmbedding]

lemma adelicLift_ofInf_mul_heckeRep_some
    (hf : ∀ g ∈ CongruenceSubgroup.Gamma1 N, f ∣[k] SpecialLinearGroup.mapGL ℝ g = f)
    (b : Fin (Ideal.absNorm v.asIdeal)) {x : GL (Fin 2) (mixedSpace ℚ)}
    (hx : 0 < ((ratInfEquiv x).det : ℝ)) :
    adelicLift N k f (ofInf ℚ x * ofFin ℚ (localGL v (heckeRep (primeUnit v) (negResidueRep v)
      (some b)))) = ((Real.sqrt (Ideal.absNorm v.asIdeal) ^ (2 - k) : ℝ) : ℂ) *
        normalizedSlash k (f ∣[k] upperTriRep _ b) (ratInfEquiv x) := by
  have hp : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by
    exact_mod_cast (prime_absNorm_asIdeal v).pos
  have hpos : 0 < ((GeneralLinearGroup.map (algebraMap ℚ ℝ) (upperTriRep _ b) *
      ratInfEquiv x).det : ℝ) := by
    rw [map_mul, Units.val_mul, det_map_upperTriRep]
    positivity
  rw [← atPlace_heckeUpperMat, adelicLift_ofInf_mul_localGL hf
    (awayFrom_heckeUpperMat_mem_levelOne v (b : ℕ)), map_heckeUpperMat_inv, mul_assoc,
    GeneralLinearGroup.scalar_commute _ (ratInfEquiv x), ← mul_assoc,
    classicalFun_mul_scalar_of_pos k _ _ (inv_pos.mpr hp), classicalFun_of_pos k f hpos,
    normalizedSlash_mul, det_map_upperTriRep, abs_of_pos hp]
  rfl

lemma adelicLift_ofInf_mul_localGL_heckeLowerMat
    (hf : ∀ g ∈ CongruenceSubgroup.Gamma1 N, f ∣[k] SpecialLinearGroup.mapGL ℝ g = f)
    {x : GL (Fin 2) (mixedSpace ℚ)} (hx : 0 < ((ratInfEquiv x).det : ℝ)) :
    adelicLift N k f (ofInf ℚ x * ofFin ℚ (localGL v (atPlace v
      (GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) (heckeLowerMat v))))) =
        ((Real.sqrt (Ideal.absNorm v.asIdeal) ^ (2 - k) : ℝ) : ℂ) *
          normalizedSlash k (f ∣[k] scaleRep (Ideal.absNorm v.asIdeal)) (ratInfEquiv x) := by
  have hp : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by
    exact_mod_cast (prime_absNorm_asIdeal v).pos
  have hpos : 0 < ((GeneralLinearGroup.map (algebraMap ℚ ℝ)
      (scaleRep (Ideal.absNorm v.asIdeal)) * ratInfEquiv x).det : ℝ) := by
    rw [map_mul, Units.val_mul, det_map_scaleRep]
    positivity
  rw [adelicLift_ofInf_mul_localGL hf (awayFrom_heckeLowerMat_mem_levelOne v),
    map_heckeLowerMat_inv, classicalFun_of_pos k f hpos, normalizedSlash_mul, det_map_scaleRep,
    abs_of_pos hp]
  rfl

end Lift

section CuspForm

variable {N : ℕ} [NeZero N] {k : ℤ}
  {f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (SpecialLinearGroup.mapGL ℝ)) k}
  {χ : (ZMod N)ˣ →* ℂˣ} {v : HeightOneSpectrum (𝓞 ℚ)}

lemma ofDirichletCharacter_ofAdicCompletion_primeUnit (hv : ¬Ideal.span {(N : 𝓞 ℚ)} ≤ v.asIdeal) :
    (HeckeCharacter.ofDirichletCharacter N (NeZero.ne N) (MulChar.ofUnitHom χ)
      (QuotientGroup.mk (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v (primeUnit v))) : ℂ) =
        χ (ZMod.unitOfCoprime _ (coprime_absNorm_of_not_le hv)) := by
  have hu : Valued.v (primeUnit v : v.adicCompletion ℚ) = exp (-((1 : ℕ) : ℤ)) := by
    rw [Nat.cast_one]
    exact valued_natCast_absNorm v
  rw [ofDirichletCharacter_ofAdicCompletion _ hv hu, pow_one,
    ← ZMod.coe_unitOfCoprime _ (coprime_absNorm_of_not_le hv), MulChar.ofUnitHom_coe]

lemma heckeOp_adelicLift_ofInf (hχ : f ∈ cuspFormCharSpace k χ)
    (hv : ¬Ideal.span {(N : 𝓞 ℚ)} ≤ v.asIdeal) {x : GL (Fin 2) (mixedSpace ℚ)}
    (hx : 0 < ((ratInfEquiv x).det : ℝ)) : heckeOp v (adelicLift N k f) (ofInf ℚ x) =
      ((Real.sqrt (Ideal.absNorm v.asIdeal) ^ (2 - k) : ℝ) : ℂ) *
        normalizedSlash k (heckeSlashUpperTri k (Ideal.absNorm v.asIdeal) f +
          ((χ (ZMod.unitOfCoprime _ (coprime_absNorm_of_not_le hv)) : ℂ) • ⇑f) ∣[k]
            scaleRep (Ideal.absNorm v.asIdeal)) (ratInfEquiv x) := by
  have hf : ∀ g ∈ CongruenceSubgroup.Gamma1 N, ⇑f ∣[k] SpecialLinearGroup.mapGL ℝ g = ⇑f :=
    slash_mapGL_eq_of_mem_gamma1 f
  have hsph : IsSphericalAt v (adelicLift N k f) :=
    isSphericalAt_of_levelOne hv fun _ hu g ↦ adelicLift_mul_ofFin hf g hu
  have hS : 0 < ((scaleRep (Ideal.absNorm v.asIdeal) : Matrix (Fin 2) (Fin 2) ℚ)).det := by
    rw [coe_scaleRep _ (prime_absNorm_asIdeal v).pos, det_fin_two_of, mul_one, mul_zero, sub_zero]
    exact_mod_cast (prime_absNorm_asIdeal v).pos
  have hnone : adelicLift N k f (ofInf ℚ x * ofFin ℚ (localGL v (heckeRep (primeUnit v)
      (negResidueRep v) none))) = (χ (ZMod.unitOfCoprime _ (coprime_absNorm_of_not_le hv)) : ℂ) *
        (((Real.sqrt (Ideal.absNorm v.asIdeal) ^ (2 - k) : ℝ) : ℂ) *
          normalizedSlash k (⇑f ∣[k] scaleRep (Ideal.absNorm v.asIdeal)) (ratInfEquiv x)) := by
    rw [heckeRep_none, map_mul, map_mul, ← scalar_ofAdicCompletion, ← mul_assoc,
      ← scalar_mul_comm, mul_assoc, adelicLift_scalar_mul f hχ,
      ofDirichletCharacter_ofAdicCompletion_primeUnit hv,
      adelicLift_ofInf_mul_localGL_heckeLowerMat hf hx]
  rw [heckeOp_eq_sum hsph (isUniformizer_primeUnit v) (isResidueSystem_negResidueRep v),
    Fintype.sum_option, hnone,
    Finset.sum_congr rfl fun b _ ↦ adelicLift_ofInf_mul_heckeRep_some hf b hx,
    normalizedSlash_add, heckeSlashUpperTri_def, normalizedSlash_sum,
    ModularForm.rat_smul_slash_of_det_pos k hS, normalizedSlash_smul_of_pos k hx, ← Finset.mul_sum]
  ring1

/-- **The Hecke operator `T_v` on the adelic lift** of a cusp form `f` of nebentypus `χ`, at the
place `v` of a prime `p ∤ N`, is the classical Hecke operator `T_p` up to the factor
`p ^ (1 - k / 2)`: `T_v φ_f = p ^ (1 - k / 2) φ_{T_p f}`. -/
lemma heckeOp_adelicLift (hχ : f ∈ cuspFormCharSpace k χ)
    (hv : ¬Ideal.span {(N : 𝓞 ℚ)} ≤ v.asIdeal) :
    heckeOp v (adelicLift N k f) = ((Real.sqrt (Ideal.absNorm v.asIdeal) ^ (2 - k) : ℝ) : ℂ) •
      adelicLift N k (heckeTCuspNat k (Ideal.absNorm v.asIdeal)
        (_hn := ⟨(prime_absNorm_asIdeal v).ne_zero⟩) f) := by
  have hf : ∀ g ∈ CongruenceSubgroup.Gamma1 N, ⇑f ∣[k] SpecialLinearGroup.mapGL ℝ g = ⇑f :=
    slash_mapGL_eq_of_mem_gamma1 f
  funext g
  rcases exists_eq_ofGlobal_mul_ofInf_mul_ofFin_of_pos N g with ⟨γ, x, hx, u, hu, rfl⟩
  rw [heckeOp_mul_levelOne hv (fun _ hu' g' ↦ adelicLift_mul_ofFin hf g' hu') hu,
    (isAutomorphicForm_adelicLift f hχ).heckeOp.left_invariant, Pi.smul_apply,
    adelicLift_apply (slash_mapGL_eq_of_mem_gamma1 _) _ _ hu, heckeOp_adelicLift_ofInf hχ hv hx,
    classicalFun_of_pos k _ hx, coe_heckeTCuspNat_prime k (prime_absNorm_asIdeal v),
    diamondOpCuspNat_of_coprime k (coprime_absNorm_of_not_le hv),
    diamondOpCusp_apply_of_mem_cuspFormCharSpace k χ _ hχ, FunLike.coe_smul, smul_eq_mul]

/-- **The adelic lift of a nonzero cusp form is nonzero.** -/
lemma adelicLift_ne_zero (hf : f ≠ 0) : adelicLift N k f ≠ 0 := by
  rcases DFunLike.ne_iff.mp hf with ⟨τ, hτ⟩
  let h : GL (Fin 2) ℝ := SpecialLinearGroup.mapGL ℝ τ.toSL2R
  have hdet : 0 < (h.det : ℝ) := by
    simp [h]
  have hI : h • I = τ := toSL2R_smul_I τ
  intro h₀
  have h₁ : adelicLift N k f (ofGlobal ℚ 1 * ofInf ℚ (ratInfEquiv.symm h) * ofFin ℚ 1) = 0 :=
    congrFun h₀ _
  rw [adelicLift_apply (slash_mapGL_eq_of_mem_gamma1 f) _ _ (one_mem _),
    MulEquiv.apply_symm_apply, classicalFun_of_pos k f hdet] at h₁
  have h₂ : ‖normalizedSlash k f h‖ = (h • I).im ^ (k / 2 : ℝ) * ‖f (h • I)‖ :=
    norm_normalizedSlash k hdet
  rw [h₁, norm_zero, hI] at h₂
  exact (mul_ne_zero (Real.rpow_pos_of_pos τ.im_pos _).ne' (norm_ne_zero_iff.mpr hτ)) h₂.symm

end CuspForm

section Newform

variable {N : ℕ} [NeZero N] {k : ℤ} (f : Newform N k) {v : HeightOneSpectrum (𝓞 ℚ)}

lemma heckeOp_adelicLift_eq_smul (hv : ¬Ideal.span {(N : 𝓞 ℚ)} ≤ v.asIdeal) :
    heckeOp v (adelicLift N k f.toCuspForm) =
      (((Real.sqrt (Ideal.absNorm v.asIdeal) ^ (2 - k) : ℝ) : ℂ) *
        (qExpansion 1 f.toCuspForm).coeff (Ideal.absNorm v.asIdeal)) •
          adelicLift N k f.toCuspForm := by
  have he : f.eigenvalue ⟨Ideal.absNorm v.asIdeal, (prime_absNorm_asIdeal v).pos⟩
      (coprime_absNorm_of_not_le hv) =
        (qExpansion 1 f.toCuspForm).coeff (Ideal.absNorm v.asIdeal) :=
    (f.toEigenformAwayFromLevel.qExpansion_coeff_eq_eigenvalue f.isNorm _ _).symm
  rw [heckeOp_adelicLift f.mem_charSpace hv,
    f.toEigenformAwayFromLevel.heckeTCuspNat_eq_eigenvalue_smul (prime_absNorm_asIdeal v)
      (coprime_absNorm_of_not_le hv), he, FunLike.coe_smul, adelicLift_smul, smul_smul]

/-- **The adelic lift of a newform is a Hecke eigenform** of level `N`, with central character the
Hecke character of its nebentypus: a nonzero automorphic form which is spherical and an
eigenvector of `T_v` at the places `v ∤ N`. It is cuspidal (`AdelicGL2.isCuspidal_adelicLift`). -/
lemma isHeckeEigenform_adelicLift :
    IsHeckeEigenform (HeckeCharacter.ofDirichletCharacter N (NeZero.ne N) f.dirichletLift)
      (Ideal.span {(N : 𝓞 ℚ)}) (adelicLift N k f.toCuspForm) where
  isAutomorphicForm := isAutomorphicForm_adelicLift f.toCuspForm f.mem_charSpace
  level_ne_bot := span_natCast_ne_bot N
  ne_zero := adelicLift_ne_zero f.ne_zero
  spherical _ hv := isSphericalAt_of_levelOne hv fun _ hu g ↦
    adelicLift_mul_ofFin (slash_mapGL_eq_of_mem_gamma1 _) g hu
  exists_eigenvalue _ hv := ⟨_, heckeOp_adelicLift_eq_smul f hv⟩

/-- **The Hecke eigenvalue of the adelic lift of a newform** at the place of a prime `p ∤ N` is
`p ^ (1 - k / 2) a_p`, for the coefficient `a_p` of `qᵖ`. -/
lemma heckeEigenvalue_adelicLift (hv : ¬Ideal.span {(N : 𝓞 ℚ)} ≤ v.asIdeal) :
    heckeEigenvalue v (adelicLift N k f.toCuspForm) =
      ((Real.sqrt (Ideal.absNorm v.asIdeal) ^ (2 - k) : ℝ) : ℂ) *
        (qExpansion 1 f.toCuspForm).coeff (Ideal.absNorm v.asIdeal) :=
  ((isHeckeEigenform_adelicLift f).eq_heckeEigenvalue hv (heckeOp_adelicLift_eq_smul f hv)).symm

/-- **The Euler factor of the adelic lift of a newform** at the place of a prime `p ∤ N`, in the
arithmetic normalisation of motivic weight `k - 1`, is the LMFDB's `1 - a_p T + χ(p) p ^ (k - 1) T²`
(LMFDB `mf.base_change`). -/
lemma arithmeticEulerFactor_adelicLift (hv : ¬Ideal.span {(N : 𝓞 ℚ)} ≤ v.asIdeal) :
    arithmeticEulerFactor v (HeckeCharacter.ofDirichletCharacter N (NeZero.ne N) f.dirichletLift)
      (adelicLift N k f.toCuspForm) (k - 1) =
        1 - C ((qExpansion 1 f.toCuspForm).coeff (Ideal.absNorm v.asIdeal)) * X +
          C (f.dirichletLift (Ideal.absNorm v.asIdeal) *
            ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (k - 1)) * X ^ 2 := by
  have hp : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℕ) := by
    exact_mod_cast (prime_absNorm_asIdeal v).pos
  have hs : Real.sqrt (Ideal.absNorm v.asIdeal) ≠ 0 := (Real.sqrt_pos.mpr hp).ne'
  have h₀ : (Real.sqrt (Ideal.absNorm v.asIdeal))⁻¹ *
      Real.sqrt (Ideal.absNorm v.asIdeal) ^ (2 - k) *
        Real.sqrt (Ideal.absNorm v.asIdeal) ^ (k - 1) = 1 := by
    rw [← zpow_neg_one, ← zpow_add₀ hs, ← zpow_add₀ hs]
    have he : -1 + (2 - k) + (k - 1) = 0 := by
      ring1
    rw [he, zpow_zero]
  have h₁ (a : ℂ) : (((Real.sqrt (Ideal.absNorm v.asIdeal))⁻¹ : ℝ) : ℂ) *
      ((Real.sqrt (Ideal.absNorm v.asIdeal) ^ (2 - k) : ℝ) : ℂ) * a *
        ((Real.sqrt (Ideal.absNorm v.asIdeal) ^ (k - 1) : ℝ) : ℂ) = a := by
    rw [mul_right_comm _ a, ← Complex.ofReal_mul, ← Complex.ofReal_mul, h₀, Complex.ofReal_one,
      one_mul]
  have h₂ : ((Real.sqrt (Ideal.absNorm v.asIdeal) ^ (k - 1) : ℝ) : ℂ) ^ 2 =
      ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ^ (k - 1) := by
    rw [← Complex.ofReal_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      Real.sq_sqrt hp.le, Complex.ofReal_zpow, Complex.ofReal_natCast]
  rw [arithmeticEulerFactor, eulerFactor, heckeEigenvalue_adelicLift f hv,
    characterAt_ofDirichletCharacter _ hv]
  simp only [sub_comp, add_comp, one_comp, mul_comp, C_comp, X_comp, X_pow_comp, mul_pow, ← C_pow,
    ← mul_assoc, ← C_mul, h₁, h₂]

/-- **The adelic lift of `Δ` is a Hecke eigenform** of level one: a concrete nonzero automorphic
form on `GL₂(𝔸_ℚ)` with Hecke eigenvalue `p ^ (-5) τ(p)` at every prime `p`. -/
lemma isHeckeEigenform_adelicLift_deltaNewform :
    IsHeckeEigenform (HeckeCharacter.ofDirichletCharacter 1 (NeZero.ne 1)
      deltaNewform.dirichletLift) (Ideal.span {((1 : ℕ) : 𝓞 ℚ)})
        (adelicLift 1 12 deltaNewform.toCuspForm) :=
  isHeckeEigenform_adelicLift deltaNewform

/-- **The adelic lift of `Δ` is cuspidal**: with `isHeckeEigenform_adelicLift_deltaNewform`, a
concrete nonzero cuspidal Hecke eigenform on `GL₂(𝔸_ℚ)`. -/
lemma isCuspidal_adelicLift_deltaNewform : IsCuspidal (adelicLift 1 12 deltaNewform.toCuspForm) :=
  isCuspidal_adelicLift deltaNewform.toCuspForm

end Newform

end AdelicGL2
