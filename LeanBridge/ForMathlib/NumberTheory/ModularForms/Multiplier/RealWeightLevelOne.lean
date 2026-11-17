import LeanBridge.ForMathlib.NumberTheory.ModularForms.EtaMultiplier
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.RealWeight

/-!
# The multiplier systems of real weight on `SL(2, ℤ)`

The LMFDB's knowl on Maass forms of weight `k` (`mf.maass.mwf`) says: "If the level is equal to 1,
the only possible multiplier systems are given by the Dedekind eta function. A compatible
multiplier system for weight `k ∈ ℝ` is given by `v_η^{2k}` or one of its 6 conjugates." This is
Strömberg's Remark 2.6, the source of the LMFDB's Maass forms with the eta multiplier: for every
real `k` there are exactly six multiplier systems of weight `k` on `SL(2, ℤ)`, the
`v_η^{2(k + r)}` for `r ∈ {0, 2, 4, 6, 8, 10}`. The "6 conjugates" are these six, `v_η^{2k}`
among them; in the companion paper (Lemma 2.1) they are the multiplier systems `v` with
`v(T) = ξ₆ e^{πik/6}`, `ξ₆` running over the sixth roots of unity, and `v` is determined by `v(T)`.

Two multiplier systems of weight `k` differ by a character of `SL(2, ℤ)` trivial at `-I`. A
character `χ` of `SL(2, ℤ)` is determined by `χ(T)`, since `S` and `T` generate `SL(2, ℤ)`, and the
relations `S² = -I` and `S³TSTS = T⁻¹` give `χ(S) χ(T)³ = 1`, `χ(T)¹² = 1` and `χ(-I) = χ(T)⁶`.
The eta multiplier of weight `1`, `v_η²`, the multiplier system of `η²`, is a character with
`v_η²(T) = e^{πi/6}`, a primitive twelfth root of unity: the characters of `SL(2, ℤ)` are its
twelve powers, and those trivial at `-I` are the six `v_η^{4m}`. So the multiplier systems of
weight `k` are the `v_η^{2k} v_η^{4m} = v_η^{2(k + 2m)}`, `m = 0, …, 5`; they are distinct, since
their values `e^{πi(k + 2m)/6}` at `T` are. The multiplier of a function on `ℍ` that is not
identically zero and has the transformation law of weight `k`, in particular of a nonzero Maass
form of weight `k` on `SL(2, ℤ)`, is a multiplier system of weight `k`, hence one of the six. For
`v_η^{2k}` itself the eta Maass forms built from `y^{k/2} η(z)^{2k}` are such functions.

## Main definitions

* `ModularForm.etaCharacter`: the character `v_η²` of `SL(2, ℤ)`.

## Main results

* `ModularGroup.map_S_mul_map_T_pow_three`, `ModularGroup.map_T_pow_twelve`,
  `ModularGroup.map_neg_one_eq_map_T_pow_six`, `ModularGroup.monoidHom_ext_T`: a character `χ` of
  `SL(2, ℤ)` satisfies `χ(S) χ(T)³ = 1`, `χ(T)¹² = 1` and `χ(-I) = χ(T)⁶`, and is determined by
  `χ(T)`.
* `ModularForm.exists_eq_etaCharacter_zpow`: the characters of `SL(2, ℤ)` are the powers of `v_η²`.
* `ModularForm.isMultiplierSystemOfWeight_etaMultiplier` (LMFDB `mf.maass.mwf`): `v_η^{2k}` is a
  multiplier system of weight `k` on `SL(2, ℤ)`, for every real `k`.
* `ModularForm.isMultiplierSystemOfWeight_iff_exists_etaMultiplier` (LMFDB `mf.maass.mwf`): the
  multiplier systems of weight `k` on `SL(2, ℤ)` are the six `v_η^{2(k + 2m)}`, `m = 0, …, 5`.
* `ModularForm.injective_etaMultiplier_add_two_mul`: these six are distinct.
* `ModularForm.ncard_setOf_isMultiplierSystemOfWeight` (LMFDB `mf.maass.mwf`): there are exactly six
  multiplier systems of weight `k` on `SL(2, ℤ)`.
* `ModularForm.IsMultiplierSystemOfWeight.ext_T`,
  `ModularForm.IsMultiplierSystemOfWeight.pow_six_apply_T`: Strömberg's form of the
  classification, a multiplier system `v` of weight `k` on `SL(2, ℤ)` is determined by `v(T)`, and
  `v(T)⁶ = e^{πik}`.
* `UpperHalfPlane.IsMaassFormOfWeight.exists_eq_etaMultiplier` (LMFDB `mf.maass.mwf`): the
  multiplier of a nonzero Maass form of weight `k` on `SL(2, ℤ)` is one of the six.

## References

* F. Strömberg, *Computation of Maass waveforms with nontrivial multiplier systems*, Math. Comp. 77
  (2008), 2375–2416 (arXiv:math/0611146), Definition 2.2 and Remark 2.6.
* F. Strömberg, *Hecke operators for Maass waveforms on PSL(2, ℤ) with integer weight and eta
  multiplier*, arXiv:math/0611148, Lemma 2.1.
-/

open Complex UpperHalfPlane Matrix SpecialLinearGroup ModularGroup ModularForm

open scoped MatrixGroups Real

namespace ModularGroup

variable (χ : SL(2, ℤ) →* Circle)

lemma S_mul_S_eq_neg_one : S * S = -1 :=
  Subtype.ext S_mul_S_eq

lemma coe_map_S_pow_four : (χ S : ℂ) ^ 4 = 1 := by
  have h : χ (S * S * (S * S)) = 1 := by
    rw [S_mul_S_eq_neg_one, neg_one_mul, neg_neg, map_one]
  rw [map_mul, map_mul, ← Circle.coe_inj, Circle.coe_mul, Circle.coe_mul, Circle.coe_one] at h
  linear_combination h

lemma coe_map_S_pow_five_mul_coe_map_T_pow_three : (χ S : ℂ) ^ 5 * (χ T : ℂ) ^ 3 = 1 := by
  have h : (χ S : ℂ) * ((χ S : ℂ) * ((χ S : ℂ) * ((χ T : ℂ) * ((χ S : ℂ) * ((χ T : ℂ) *
      (χ S : ℂ)))))) = (χ T : ℂ)⁻¹ := by
    simpa using congrArg (fun g ↦ (χ g : ℂ)) T_S_rel
  field_simp at h
  linear_combination h

/-- **`χ(S) χ(T)³ = 1`** for a character `χ` of `SL(2, ℤ)`, by `S⁴ = 1` and `S³TSTS = T⁻¹`. -/
lemma map_S_mul_map_T_pow_three : χ S * χ T ^ 3 = 1 := by
  refine Circle.ext ?_
  rw [Circle.coe_mul, Circle.coe_pow, Circle.coe_one]
  linear_combination (-((χ S : ℂ) * (χ T : ℂ) ^ 3)) * coe_map_S_pow_four χ +
    coe_map_S_pow_five_mul_coe_map_T_pow_three χ

/-- **`χ(T)¹² = 1`** for a character `χ` of `SL(2, ℤ)`. -/
lemma map_T_pow_twelve : χ T ^ 12 = 1 := by
  have h : (χ S : ℂ) * (χ T : ℂ) ^ 3 = 1 := by
    simpa using congrArg ((↑) : Circle → ℂ) (map_S_mul_map_T_pow_three χ)
  refine Circle.ext ?_
  rw [Circle.coe_pow, Circle.coe_one]
  linear_combination (-((χ T : ℂ) ^ 12)) * coe_map_S_pow_four χ + (((χ S : ℂ) * (χ T : ℂ) ^ 3) ^ 3 +
    ((χ S : ℂ) * (χ T : ℂ) ^ 3) ^ 2 + (χ S : ℂ) * (χ T : ℂ) ^ 3 + 1) * h

/-- **`χ(-I) = χ(T)⁶`** for a character `χ` of `SL(2, ℤ)`. -/
lemma map_neg_one_eq_map_T_pow_six : χ (-1) = χ T ^ 6 := by
  have h : (χ S : ℂ) * (χ T : ℂ) ^ 3 = 1 := by
    simpa using congrArg ((↑) : Circle → ℂ) (map_S_mul_map_T_pow_three χ)
  have h12 : (χ T : ℂ) ^ 12 = 1 := by
    simpa using congrArg ((↑) : Circle → ℂ) (map_T_pow_twelve χ)
  refine Circle.ext ?_
  rw [← S_mul_S_eq_neg_one, map_mul, Circle.coe_mul, Circle.coe_pow]
  linear_combination (-((χ S : ℂ) ^ 2)) * h12 + (χ T : ℂ) ^ 6 * ((χ S : ℂ) * (χ T : ℂ) ^ 3 + 1) * h

variable {χ} in
/-- **A character of `SL(2, ℤ)` is determined by its value at `T`**: `S` and `T` generate
`SL(2, ℤ)`, and `χ(S) = χ(T)⁻³`. -/
lemma monoidHom_ext_T {χ' : SL(2, ℤ) →* Circle} (h : χ T = χ' T) : χ = χ' := by
  refine MonoidHom.eq_of_eqOn_dense SpecialLinearGroup.SL2Z_generators fun g hg ↦ ?_
  rcases hg with rfl | rfl
  · rw [eq_inv_of_mul_eq_one_left (map_S_mul_map_T_pow_three χ),
      eq_inv_of_mul_eq_one_left (map_S_mul_map_T_pow_three χ'), h]
  · exact h

end ModularGroup

namespace ModularForm

variable (k : ℝ) (γ : SL(2, ℤ)) (χ : SL(2, ℤ) →* Circle) {v v' : 𝒮ℒ → Circle}

/-- The **character `v_η²` of `SL(2, ℤ)`**: the eta multiplier of weight `1`, the multiplier system
of `η²`, which has integral weight `1` and is therefore a homomorphism. Its value at `T` is
`e^{πi/6}`, a primitive twelfth root of unity, and the eta multiplier of an integral weight `n` is
its `n`-th power. -/
noncomputable def etaCharacter : SL(2, ℤ) →* Circle :=
  MonoidHom.mk' (fun γ ↦ etaMultiplier 1 γ) fun γ δ ↦ Circle.ext <|
    mul_right_cancel₀ (denom_ne_zero (γ * δ : SL(2, ℤ)) UpperHalfPlane.I) <| by
      rw [denom_mul_SL, Circle.coe_mul]
      simpa only [ofReal_one, cpow_one, denom_mul_SL, mul_assoc] using
        etaMultiplier_mul_cpow_denom 1 γ δ UpperHalfPlane.I

lemma etaCharacter_apply : etaCharacter γ = etaMultiplier 1 γ :=
  rfl

lemma etaMultiplier_intCast (n : ℤ) : etaMultiplier n γ = etaCharacter γ ^ n := by
  rw [etaCharacter_apply, etaMultiplier, etaMultiplier, ← Circle.exp_intCast_mul]
  congr 1
  ring1

lemma etaMultiplier_T : etaMultiplier k T = Circle.exp (π * k / 6) := by
  rw [etaMultiplier, etaPhase_T]
  congr 1
  ring1

lemma etaCharacter_T : etaCharacter T = Circle.exp (π / 6) := by
  rw [etaCharacter_apply, etaMultiplier_T, mul_one]

lemma etaMultiplier_add_twelve_mul (n : ℤ) : etaMultiplier (k + 12 * n) γ = etaMultiplier k γ := by
  have h : etaMultiplier (12 * n) γ = etaMultiplier 12 γ ^ n := by
    rw [etaMultiplier, etaMultiplier, ← Circle.exp_intCast_mul]
    congr 1
    ring1
  rw [etaMultiplier_add, h, etaMultiplier_twelve]
  simp

/-- **The characters of `SL(2, ℤ)` are the powers of `v_η²`**: every homomorphism
`χ : SL(2, ℤ) → S¹` is `v_η^{2n}` for an integer `n`, since `χ(T)` is a twelfth root of unity and
`v_η²(T) = e^{πi/6}`. -/
lemma exists_eq_etaCharacter_zpow : ∃ n : ℤ, χ = etaCharacter ^ n := by
  rcases Circle.exp_surjective (χ T) with ⟨θ, hθ⟩
  have h : Circle.exp ((12 : ℕ) * θ) = 1 := by
    rw [Circle.exp_natCast_mul, hθ, map_T_pow_twelve]
  rcases Circle.exp_eq_one.mp h with ⟨n, hn⟩
  refine ⟨n, monoidHom_ext_T ?_⟩
  rw [MonoidHom.zpow_apply, etaCharacter_T, ← Circle.exp_intCast_mul, ← hθ]
  congr 1
  push_cast at hn
  linear_combination hn / 12

lemma exists_eq_etaCharacter_zpow_two_mul (h1 : χ (-1) = 1) :
    ∃ m : ℤ, χ = etaCharacter ^ (2 * m) := by
  rcases Circle.exp_surjective (χ T) with ⟨θ, hθ⟩
  have h : Circle.exp ((6 : ℕ) * θ) = 1 := by
    rw [Circle.exp_natCast_mul, hθ, ← map_neg_one_eq_map_T_pow_six, h1]
  rcases Circle.exp_eq_one.mp h with ⟨m, hm⟩
  refine ⟨m, monoidHom_ext_T ?_⟩
  rw [MonoidHom.zpow_apply, etaCharacter_T, ← Circle.exp_intCast_mul, ← hθ]
  congr 1
  push_cast at hm ⊢
  linear_combination hm / 6

/-- **The eta multiplier `v_η^{2k}` is a multiplier system of weight `k` on `SL(2, ℤ)`** (LMFDB
`mf.maass.mwf`), for every real `k`: the consistency condition is
`ModularForm.etaMultiplier_mul_cpow_denom`, and `v_η^{2k}(-I) = e^{-πik}`. -/
lemma isMultiplierSystemOfWeight_etaMultiplier :
    IsMultiplierSystemOfWeight 𝒮ℒ k fun γ ↦ etaMultiplier k γ := by
  refine ⟨?_, fun _ ↦ etaMultiplier_neg_one k⟩
  rintro ⟨_, γ, rfl⟩ ⟨_, δ, rfl⟩ z
  rw [Subgroup.coe_mul, ← map_mul]
  exact etaMultiplier_mul_cpow_denom k γ δ z

/-- **The multiplier systems of weight `k` on `SL(2, ℤ)`** (LMFDB `mf.maass.mwf`, Strömberg's
Remark 2.6): for every real `k`, a function `v : SL(2, ℤ) → S¹` (on the image `𝒮ℒ` of `SL(2, ℤ)`
in `GL(2, ℝ)`) is a multiplier system of weight `k` exactly when it is one of the six
`v_η^{2(k + 2m)}`, `m = 0, …, 5`, the knowl's "`v_η^{2k}` or one of its 6 conjugates". Its quotient
by `v_η^{2k}` is a character of `SL(2, ℤ)` trivial at `-I`, so a power `v_η^{4m}` of `v_η²`, and
`v_η^{2(k + 12)} = v_η^{2k}`. -/
lemma isMultiplierSystemOfWeight_iff_exists_etaMultiplier : IsMultiplierSystemOfWeight 𝒮ℒ k v ↔
    ∃ m : Fin 6, ∀ γ : 𝒮ℒ, v γ = etaMultiplier (k + 2 * (m : ℕ)) γ := by
  refine ⟨fun hv ↦ ?_, fun ⟨m, hm⟩ ↦ ?_⟩
  · have h1 : (hv.divMonoidHom (isMultiplierSystemOfWeight_etaMultiplier k)).comp
        (mapGL ℝ).rangeRestrict (-1) = 1 := by
      have h : (mapGL ℝ).rangeRestrict (-1 : SL(2, ℤ)) = ⟨-1, -1, mapGL_neg_one⟩ :=
        Subtype.ext mapGL_neg_one
      rw [MonoidHom.comp_apply, h]
      exact hv.divMonoidHom_neg_one _ _
    rcases exists_eq_etaCharacter_zpow_two_mul _ h1 with ⟨m, hm⟩
    refine ⟨⟨(m % 6).toNat, by omega⟩, ?_⟩
    rintro ⟨_, γ, rfl⟩
    have h : v ⟨mapGL ℝ γ, γ, rfl⟩ / etaMultiplier k γ = etaCharacter γ ^ (2 * m) :=
      DFunLike.congr_fun hm γ
    rw [div_eq_iff_eq_mul] at h
    rw [h, mul_comm (etaCharacter γ ^ (2 * m)), ← etaMultiplier_intCast, ← etaMultiplier_add,
      ← etaMultiplier_add_twelve_mul (k + ((2 * m : ℤ) : ℝ)) γ (-(m / 6))]
    congr 1
    have hm6 : (((m % 6).toNat : ℕ) : ℝ) = ((m - 6 * (m / 6) : ℤ) : ℝ) := by
      rw [← Int.emod_def, ← Int.cast_natCast, Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num))]
    rw [Fin.val_mk, hm6]
    push_cast
    ring1
  · have hv : v = fun γ : 𝒮ℒ ↦ etaMultiplier (k + 2 * (m : ℕ)) γ := funext hm
    rw [hv, ← isMultiplierSystemOfWeight_add_two_mul_iff ((m : ℕ) : ℤ), Int.cast_natCast]
    exact isMultiplierSystemOfWeight_etaMultiplier _

/-- **The six multiplier systems `v_η^{2(k + 2m)}`, `m = 0, …, 5`, of weight `k` on `SL(2, ℤ)` are
distinct**: their values at `T` are the six `e^{πi(k + 2m)/6}`. -/
lemma injective_etaMultiplier_add_two_mul :
    Function.Injective fun (m : Fin 6) (γ : 𝒮ℒ) ↦ etaMultiplier (k + 2 * (m : ℕ)) γ := by
  intro m n hmn
  have h : etaMultiplier (k + 2 * (m : ℕ)) T = etaMultiplier (k + 2 * (n : ℕ)) T :=
    congrFun hmn ⟨mapGL ℝ T, T, rfl⟩
  rw [etaMultiplier_T, etaMultiplier_T, Circle.exp_eq_exp] at h
  rcases h with ⟨j, hj⟩
  have h0 : π * ((m : ℕ) - (n : ℕ) - 6 * j : ℝ) = 0 := by
    linear_combination 3 * hj
  have h1 : ((m : ℕ) : ℤ) - (n : ℕ) = 6 * j := by
    have h2 : ((m : ℕ) - (n : ℕ) - 6 * j : ℝ) = 0 :=
      (mul_eq_zero.mp h0).resolve_left Real.pi_ne_zero
    exact_mod_cast (sub_eq_zero.mp h2)
  exact Fin.ext <| by omega

/-- **There are exactly six multiplier systems of weight `k` on `SL(2, ℤ)`** (LMFDB `mf.maass.mwf`,
Strömberg's Remark 2.6), for every real `k`: the six `v_η^{2(k + 2m)}`, `m = 0, …, 5`. -/
lemma ncard_setOf_isMultiplierSystemOfWeight :
    {v : 𝒮ℒ → Circle | IsMultiplierSystemOfWeight 𝒮ℒ k v}.ncard = 6 := by
  have h : {v : 𝒮ℒ → Circle | IsMultiplierSystemOfWeight 𝒮ℒ k v} =
      Set.range fun (m : Fin 6) (γ : 𝒮ℒ) ↦ etaMultiplier (k + 2 * (m : ℕ)) γ := by
    ext v
    exact (isMultiplierSystemOfWeight_iff_exists_etaMultiplier k).trans <| (exists_congr fun m ↦
      ⟨fun h ↦ (funext h).symm, fun h γ ↦ (congrFun h γ).symm⟩).trans Set.mem_range.symm
  rw [h, Set.ncard_range_of_injective (injective_etaMultiplier_add_two_mul k),
    Nat.card_eq_fintype_card, Fintype.card_fin]

namespace IsMultiplierSystemOfWeight

variable {k}

/-- **A multiplier system of weight `k` on `SL(2, ℤ)` is determined by its value at `T`**
(Strömberg's Lemma 2.1): the quotient of two of them is a character of `SL(2, ℤ)`, which is
determined by its value at `T`. -/
lemma ext_T (hv : IsMultiplierSystemOfWeight 𝒮ℒ k v) (hv' : IsMultiplierSystemOfWeight 𝒮ℒ k v')
    (h : v ⟨mapGL ℝ T, T, rfl⟩ = v' ⟨mapGL ℝ T, T, rfl⟩) : v = v' := by
  have hχ : (hv.divMonoidHom hv').comp (mapGL ℝ).rangeRestrict = 1 :=
    monoidHom_ext_T <| (hv.divMonoidHom_apply hv' _).trans (div_eq_one.mpr h)
  funext γ
  rcases γ with ⟨_, γ, rfl⟩
  exact div_eq_one.mp (DFunLike.congr_fun hχ γ)

/-- **`v(T)⁶ = e^{πik}`** for a multiplier system `v` of weight `k` on `SL(2, ℤ)`: in Strömberg's
form (Lemma 2.1), `v(T) = ξ₆ e^{πik/6}` for a sixth root of unity `ξ₆`, and `v` is determined by
`v(T)` (`ext_T`), so that `v ↦ ξ₆` is a bijection onto the sixth roots of unity. -/
lemma pow_six_apply_T (hv : IsMultiplierSystemOfWeight 𝒮ℒ k v) :
    v ⟨mapGL ℝ T, T, rfl⟩ ^ 6 = Circle.exp (π * k) := by
  rcases (isMultiplierSystemOfWeight_iff_exists_etaMultiplier k).mp hv with ⟨m, hm⟩
  have h : v ⟨mapGL ℝ T, T, rfl⟩ = etaMultiplier (k + 2 * (m : ℕ)) T := hm _
  rw [h, etaMultiplier_T, ← Circle.exp_natCast_mul, Circle.exp_eq_exp]
  refine ⟨(m : ℕ), ?_⟩
  push_cast
  ring1

end IsMultiplierSystemOfWeight

end ModularForm

namespace UpperHalfPlane

variable {k : ℝ} {f : ℂ → ℂ} {v : 𝒮ℒ → Circle} {eigenvalue : ℂ} {z : ℍ}

/-- **The only possible multiplier systems at level `1`** (LMFDB `mf.maass.mwf`): if `f` is a Maass
form of weight `k` and multiplier `v` on `SL(2, ℤ)`, not zero at some point of `ℍ`, then `v` is one
of the six multiplier systems `v_η^{2(k + 2m)}`, `m = 0, …, 5`, of weight `k`. Only the
transformation law is used, not square-integrability nor the Laplace equation. -/
lemma IsMaassFormOfWeight.exists_eq_etaMultiplier (hf : IsMaassFormOfWeight 𝒮ℒ k f v eigenvalue)
    (hz : f z ≠ 0) : ∃ m : Fin 6, ∀ γ : 𝒮ℒ, v γ = etaMultiplier (k + 2 * (m : ℕ)) γ :=
  (isMultiplierSystemOfWeight_iff_exists_etaMultiplier k).mp <|
    hf.isMultiplierSystemOfWeight (isMultiplierSystemOfWeight_etaMultiplier k) hz

end UpperHalfPlane
