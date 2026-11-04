import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwoBorelNormalForm
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwoHeckeGenerators

/-!
# The Satake map of `Sp(4, ℤ)` on `T(p)` and `T_0(p²)`

The Satake map `ω_α` of the local Hecke algebra of `Γ = Sp(4, ℤ)` at `p`
(`SiegelUpperHalfSpace.satakeMap`) sends a double coset to the sum, over its right cosets, of the
unramified character `α₀^δ (α_0 p⁻²)^{d₀} (α_1 p⁻¹)^{d₁}` of the Borel normal form
`(p^δ D⁻ᵀ, X D; 0, D)`, `D = (d₀, 0; c, d₁)`, `d_j = p^{e_j}`, of the coset
(`SiegelUpperHalfSpace.exists_mul_eq_borelNF`, `SiegelUpperHalfSpace.borelNF_eq_of_mul_eq`). Its
values on two of the three generators of the local Hecke algebra
(`SiegelUpperHalfSpace.mem_of_heckeGenerators`) are computed here:

* the scalar `T_0(p²) = Γ (p 1₄) Γ` is a single right coset, of normal form `p 1₄`;
* `T(p) = Γ diag(1, 1, p, p) Γ` is the set of integral similitudes of multiplier `p`
  (`SiegelUpperHalfSpace.exists_eq_heckeCosetDiag`), and its right cosets are the `1 + p + p² + p³`
  normal forms with `(d₀, d₁) = (1, 1)`, `X = 0`; `(1, p)`, `X = (0, 0; 0, t/p)`; `(p, 1)`,
  `0 ≤ c < p`, `X = (t/p, 0; 0, 0)`; and `(p, p)`, `X = T/p` (Andrianov, *Quadratic forms and Hecke
  operators*, §3.3, in degree `2`). Integrality of the normal form forces this list.

The values agree with the coset enumeration of the ZV2 review and with the eigenvalues of `χ₁₀`
and of the Siegel Eisenstein series computed from Fourier coefficients.

## Main definitions

* `SiegelUpperHalfSpace.tpRep`: the right coset representatives of `T(p)`.

## Main results

* `SiegelUpperHalfSpace.satakeMap_T₀`: `ω_α(T_0(p²)) = α₀² (α_0 p⁻²)(α_1 p⁻¹)`.
* `SiegelUpperHalfSpace.satakeMap_Tp`: `ω_α(T(p)) = α₀ (1 + α_0)(1 + α_1)`.
-/

open Matrix hiding mul_inv_rev

open scoped Pointwise

namespace SiegelUpperHalfSpace

local notation "M₄" => Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ

local notation "GL₄" => GL (Fin 2 ⊕ Fin 2) ℚ

local notation "Γ₂" => heckeGamma (Fin 2)

variable {p : ℕ} [Fact p.Prime] (α₀ : ℂˣ) (α : Fin 2 → ℂˣ)

lemma borelValue_borelNFGL {δ e₀ e₁ : ℕ} (c x₀₀ x₀₁ x₁₁ : ℚ) :
    HeckeCoset.borelValue Γ₂ ((satakeCharacter p α₀ α).comp (satakeValuation p))
      (borelNFGL ((p : ℚ) ^ δ) ((p : ℚ) ^ e₀) ((p : ℚ) ^ e₁) c x₀₀ x₀₁ x₁₁) =
        (α₀ : ℂ) ^ δ * ((α 0 : ℂ) * ((p : ℂ) ^ 2)⁻¹) ^ e₀ * ((α 1 : ℂ) * (p : ℂ)⁻¹) ^ e₁ := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hB' : 1 * borelNFGL ((p : ℚ) ^ δ) ((p : ℚ) ^ e₀) ((p : ℚ) ^ e₁) c x₀₀ x₀₁ x₁₁ ∈
      siegelBorel 2 := by
    rw [one_mul]
    exact borelNFGL_mem_siegelBorel (pow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) δ)
      (pow_ne_zero e₀ hp) (pow_ne_zero e₁ hp)
  have hcoe : (((⟨_, hB'⟩ : siegelBorel 2) : GL₄) : M₄) =
      borelNF ((p : ℚ) ^ δ) ((p : ℚ) ^ e₀) ((p : ℚ) ^ e₁) c x₀₀ x₀₁ x₁₁ := by
    rw [Subgroup.coe_mk, one_mul, coe_borelNFGL (pow_ne_zero δ hp) (pow_ne_zero e₀ hp)
      (pow_ne_zero e₁ hp)]
  have hJ : (((⟨_, hB'⟩ : siegelBorel 2) : GL₄) : M₄)ᵀ * J (Fin 2) ℚ *
      (((⟨_, hB'⟩ : siegelBorel 2) : GL₄) : M₄) = (p : ℚ) ^ δ • J (Fin 2) ℚ := by
    rw [hcoe]
    exact borelNF_transpose_mul_J_mul (pow_ne_zero e₀ hp) (pow_ne_zero e₁ hp)
  have hm : borelMultiplier ⟨_, hB'⟩ = (p : ℚ) ^ δ :=
    multiplier_eq _ hJ
  have hd₀ : borelDiag ⟨_, hB'⟩ 0 = (p : ℚ) ^ δ / (p : ℚ) ^ e₀ := by
    rw [borelDiag, hcoe]
    simp [borelNF]
  have hd₁ : borelDiag ⟨_, hB'⟩ 1 = (p : ℚ) ^ δ / (p : ℚ) ^ e₁ := by
    rw [borelDiag, hcoe]
    simp [borelNF]
  have hv₀ (e : ℕ) : padicValRat p ((p : ℚ) ^ e) = e := by
    rw [padicValRat.pow, padicValRat.self (Fact.out : p.Prime).one_lt, mul_one]
  have hv (e : ℕ) : padicValRat p ((p : ℚ) ^ δ / (p : ℚ) ^ e) = δ - e := by
    rw [padicValRat.div (pow_ne_zero δ hp) (pow_ne_zero e hp), hv₀, hv₀]
  rw [HeckeCoset.borelValue_eq (fun b hb ↦ satakeCharacter_satakeValuation_eq_one p α₀ α hb)
    (one_mem _) hB']
  simp only [MonoidHom.comp_apply, satakeValuation, MonoidHom.coe_mk, OneHom.coe_mk,
    satakeCharacter, toAdd_ofAdd, Fin.prod_univ_two, hm, hd₀, hd₁, hv₀, hv]
  simp [primeUnit, mul_assoc]

lemma satakeMap_single_eq_sum (D : HeckeCoset (heckeMonoidAt (Fin 2) p) Γ₂ Γ₂) {ι : Type*}
    [Fintype ι] (a : ι → GL₄)
    (hmem : ∀ i, a i ∈ DoubleCoset.doubleCoset (D.rep : GL₄) (Γ₂ : Set GL₄) Γ₂)
    (hcard : ∀ x ∈ DoubleCoset.doubleCoset (D.rep : GL₄) (Γ₂ : Set GL₄) Γ₂,
      ∃! i, x * (a i)⁻¹ ∈ Γ₂) :
    satakeMap p α₀ α (HeckeCosetModule.single ℂ D 1) =
      ∑ i, HeckeCoset.borelValue Γ₂ ((satakeCharacter p α₀ α).comp (satakeValuation p)) (a i) := by
  rw [satakeMap_single, one_smul]
  have h : ∑ i, HeckeCoset.borelValue Γ₂ ((satakeCharacter p α₀ α).comp (satakeValuation p))
      (a i) = 1 • HeckeCoset.rightCosetSum D (HeckeCoset.borelValue Γ₂
        ((satakeCharacter p α₀ α).comp (satakeValuation p))) :=
    HeckeCoset.sum_eq_nsmul_rightCosetSum D (fun γ hγ x ↦ HeckeCoset.borelValue_mul_left
      (fun b hb ↦ satakeCharacter_satakeValuation_eq_one p α₀ α hb) hγ) a 1 hmem fun x hx ↦ by
    rcases hcard x hx with ⟨i, hi, hu⟩
    exact Nat.card_eq_one_iff_unique.mpr ⟨⟨fun j k ↦ Subtype.ext
      ((hu _ ((rightCoset_eq_iff Γ₂).mp j.2)).trans (hu _ ((rightCoset_eq_iff Γ₂).mp k.2)).symm)⟩,
        ⟨⟨i, (rightCoset_eq_iff Γ₂).mpr hi⟩⟩⟩
  rw [h, one_smul]
  rfl

lemma mem_doubleCoset_heckeCosetDiag {x : heckeMonoidAt (Fin 2) p} {a s t : ℕ}
    (h : ∀ a' s' t', (x : GL₄) ∈ DoubleCoset.doubleCoset (symplecticDiag p a' s' t' : GL₄)
      (Γ₂ : Set GL₄) Γ₂ → (a', s', t') = (a, s, t)) :
    (x : GL₄) ∈ DoubleCoset.doubleCoset ((heckeCosetDiag p a s t).rep : GL₄) (Γ₂ : Set GL₄) Γ₂ := by
  rcases exists_eq_heckeCosetDiag (HeckeCoset.mk Γ₂ Γ₂ x) with ⟨a', s', t', hx⟩
  have hD : DoubleCoset.doubleCoset (x : GL₄) (Γ₂ : Set GL₄) Γ₂ =
      DoubleCoset.doubleCoset (symplecticDiag p a' s' t' : GL₄) (Γ₂ : Set GL₄) Γ₂ :=
    HeckeCoset.eq_iff.mp hx
  have hmem : (x : GL₄) ∈ DoubleCoset.doubleCoset (symplecticDiag p a' s' t' : GL₄)
      (Γ₂ : Set GL₄) Γ₂ :=
    hD ▸ DoubleCoset.mem_doubleCoset_self _ _ _
  have h' : (a', s', t') = (a, s, t) := h a' s' t' hmem
  simp only [Prod.mk.injEq] at h'
  rcases h' with ⟨rfl, rfl, rfl⟩
  rw [← HeckeCoset.toSet_eq_doubleCoset_rep]
  exact HeckeCoset.mem_toSet_iff.mpr hx

lemma borelNFGL_mem_heckeMonoidAt {δ e₀ e₁ : ℕ} {c x₀₀ x₀₁ x₁₁ : ℚ}
    (hint : ∃ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ, (Int.castRingHom ℚ).mapMatrix M =
      borelNF ((p : ℚ) ^ δ) ((p : ℚ) ^ e₀) ((p : ℚ) ^ e₁) c x₀₀ x₀₁ x₁₁) :
    borelNFGL ((p : ℚ) ^ δ) ((p : ℚ) ^ e₀) ((p : ℚ) ^ e₁) c x₀₀ x₀₁ x₁₁ ∈
      heckeMonoidAt (Fin 2) p := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hcoe : ((borelNFGL ((p : ℚ) ^ δ) ((p : ℚ) ^ e₀) ((p : ℚ) ^ e₁) c x₀₀ x₀₁ x₁₁ : GL₄) : M₄) =
      borelNF ((p : ℚ) ^ δ) ((p : ℚ) ^ e₀) ((p : ℚ) ^ e₁) c x₀₀ x₀₁ x₁₁ :=
    coe_borelNFGL (pow_ne_zero δ hp) (pow_ne_zero e₀ hp) (pow_ne_zero e₁ hp)
  have hJ : (borelNF ((p : ℚ) ^ δ) ((p : ℚ) ^ e₀) ((p : ℚ) ^ e₁) c x₀₀ x₀₁ x₁₁)ᵀ * J (Fin 2) ℚ *
      borelNF ((p : ℚ) ^ δ) ((p : ℚ) ^ e₀) ((p : ℚ) ^ e₁) c x₀₀ x₀₁ x₁₁ =
        (p : ℚ) ^ δ • J (Fin 2) ℚ :=
    borelNF_transpose_mul_J_mul (pow_ne_zero e₀ hp) (pow_ne_zero e₁ hp)
  rcases hint with ⟨M, hM⟩
  refine ⟨⟨⟨(p : ℚ) ^ δ, pow_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) δ, ?_⟩, M, ?_⟩, δ, ?_⟩
  · rw [Units.coeHom_apply, hcoe]
    exact hJ
  · rw [RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, Units.coeHom_apply, hcoe]
    exact hM
  · rw [hcoe]
    exact hJ

lemma det_borelNFGL {δ e₀ e₁ : ℕ} (c x₀₀ x₀₁ x₁₁ : ℚ) :
    ((borelNFGL ((p : ℚ) ^ δ) ((p : ℚ) ^ e₀) ((p : ℚ) ^ e₁) c x₀₀ x₀₁ x₁₁ : GL₄) : M₄).det =
      (p : ℚ) ^ (2 * δ) := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [coe_borelNFGL (pow_ne_zero δ hp) (pow_ne_zero e₀ hp) (pow_ne_zero e₁ hp),
    det_borelNF (pow_ne_zero e₀ hp) (pow_ne_zero e₁ hp), ← pow_mul, mul_comm]

/-! ### `T_0(p²)` -/

lemma borelNFGL_eq_symplecticDiag :
    borelNFGL ((p : ℚ) ^ 2) p p 0 0 0 0 = (symplecticDiag p 1 0 0 : GL₄) := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  refine Units.ext ?_
  rw [coe_borelNFGL (pow_ne_zero 2 hp) hp hp, coe_symplecticDiag]
  ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [borelNF, diagExp] <;>
    field_simp

/-- **The Satake map on the scalar `T_0(p²) = Γ (p 1₄) Γ`**:
`ω_α(T_0(p²)) = α₀² (α_0 p⁻²) (α_1 p⁻¹)`. -/
lemma satakeMap_T₀ : satakeMap p α₀ α (HeckeCosetModule.single ℂ (heckeCosetDiag p 1 0 0) 1) =
    (α₀ : ℂ) ^ 2 * ((α 0 : ℂ) * ((p : ℂ) ^ 2)⁻¹) * ((α 1 : ℂ) * (p : ℂ)⁻¹) := by
  have he : borelNFGL ((p : ℚ) ^ 2) ((p : ℚ) ^ 1) ((p : ℚ) ^ 1) 0 0 0 0 =
      (symplecticDiag p 1 0 0 : GL₄) := by
    rw [pow_one]
    exact borelNFGL_eq_symplecticDiag
  rw [satakeMap_single_eq_sum α₀ α _ (fun _ : Unit ↦ borelNFGL ((p : ℚ) ^ 2) ((p : ℚ) ^ 1)
    ((p : ℚ) ^ 1) 0 0 0 0) (fun _ ↦ he ▸ symplecticDiag_mem_doubleCoset_rep 1 0 0) ?_,
    Fintype.sum_unique, borelValue_borelNFGL α₀ α, pow_one, pow_one]
  · intro x hx
    refine ⟨(), ?_, fun _ _ ↦ rfl⟩
    rcases DoubleCoset.mem_doubleCoset.mp hx with ⟨γ, hγ, γ', hγ', rfl⟩
    rcases DoubleCoset.mem_doubleCoset.mp (rep_mem_doubleCoset_symplecticDiag (p := p) 1 0 0) with
      ⟨γ₁, hγ₁, γ₂, hγ₂, h₁⟩
    have e : γ * (γ₁ * (symplecticDiag p 1 0 0 : GL₄) * γ₂) * γ' *
        (symplecticDiag p 1 0 0 : GL₄)⁻¹ = γ * γ₁ * (γ₂ * γ') := by
      rw [show γ * (γ₁ * (symplecticDiag p 1 0 0 : GL₄) * γ₂) * γ' *
          (symplecticDiag p 1 0 0 : GL₄)⁻¹ = γ * γ₁ * ((symplecticDiag p 1 0 0 : GL₄) *
            (γ₂ * γ') * (symplecticDiag p 1 0 0 : GL₄)⁻¹) by group,
        symplecticDiag_one_zero_zero_mul, mul_inv_cancel_right]
    rw [h₁, he, e]
    exact mul_mem (mul_mem hγ hγ₁) (mul_mem hγ₂ hγ')

/-! ### `T(p)` -/

lemma eq_zero_of_int {x : ℚ} (h₀ : 0 ≤ x) (h₁ : x < 1) (h : ∃ z : ℤ, (z : ℚ) = x) : x = 0 := by
  rcases h with ⟨z, rfl⟩
  have : z = 0 := by
    have h₀' : (0 : ℤ) ≤ z := by exact_mod_cast h₀
    have h₁' : z < 1 := by exact_mod_cast h₁
    omega
  rw [this, Int.cast_zero]

lemma exists_fin_eq {x : ℚ} (n : ℕ) (h₀ : 0 ≤ x) (h₁ : x < n) (h : ∃ z : ℤ, (z : ℚ) = x) :
    ∃ t : Fin n, x = t := by
  rcases h with ⟨z, rfl⟩
  have h₀' : (0 : ℤ) ≤ z := by exact_mod_cast h₀
  have h₁' : z < n := by exact_mod_cast h₁
  refine ⟨⟨z.toNat, by omega⟩, ?_⟩
  exact_mod_cast (Int.toNat_of_nonneg h₀').symm

lemma exists_fin_eq_div {x : ℚ} (n : ℕ) (hn : 0 < n) (h₀ : 0 ≤ x) (h₁ : x < 1)
    (h : ∃ z : ℤ, (z : ℚ) = x * n) : ∃ t : Fin n, x = t / n := by
  have hn' : (0 : ℚ) < n := Nat.cast_pos.mpr hn
  rcases exists_fin_eq n (by positivity) (by nlinarith) h with ⟨t, ht⟩
  exact ⟨t, by rw [← ht]; field_simp⟩

lemma eq_one_or_eq_of_int {d : ℚ} (hd : 0 < d) (h₁ : ∃ z : ℤ, (z : ℚ) = d)
    (h₂ : ∃ z : ℤ, (z : ℚ) = p / d) : d = 1 ∨ d = p := by
  rcases h₁ with ⟨z, rfl⟩
  rcases h₂ with ⟨w, hw⟩
  have hz : 0 < z := by exact_mod_cast hd
  have hzw : z * w = p := by
    have : (z : ℚ) * w = p := by rw [hw]; field_simp
    exact_mod_cast this
  have hdvd : z.toNat ∣ p := by
    refine ⟨w.toNat, ?_⟩
    have hw' : 0 ≤ w := by
      by_contra hw'
      have : z * w < 0 := mul_neg_of_pos_of_neg hz (by omega)
      omega
    zify
    rw [Int.toNat_of_nonneg hz.le, Int.toNat_of_nonneg hw']
    exact hzw.symm
  rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd _ hdvd with h | h
  · left
    have : z = 1 := by omega
    rw [this, Int.cast_one]
  · right
    have : z = p := by omega
    rw [this, Int.cast_natCast]

variable (p) in
/-- The index set of the right cosets of `T(p)`: the four families of Borel normal forms with
`(d₀, d₁) = (1, 1), (1, p), (p, 1), (p, p)`. -/
abbrev TpIndex : Type :=
  Unit ⊕ Fin p ⊕ (Fin p × Fin p) ⊕ (Fin p × Fin p × Fin p)

/-- The exponents `(v_p(d₀), v_p(d₁))` of the right coset representatives of `T(p)`. -/
def tpExp : TpIndex p → ℕ × ℕ
  | .inl _ => (0, 0)
  | .inr (.inl _) => (0, 1)
  | .inr (.inr (.inl _)) => (1, 0)
  | .inr (.inr (.inr _)) => (1, 1)

/-- The data `(c, x₀₀, x₀₁, x₁₁)` of the right coset representatives of `T(p)`. -/
def tpData : TpIndex p → ℚ × ℚ × ℚ × ℚ
  | .inl _ => (0, 0, 0, 0)
  | .inr (.inl t) => (0, 0, 0, t / p)
  | .inr (.inr (.inl (c, t))) => (c, t / p, 0, 0)
  | .inr (.inr (.inr (t₀, t₁, t₂))) => (0, t₀ / p, t₁ / p, t₂ / p)

/-- The right coset representatives of `T(p)`, in Borel normal form. -/
noncomputable def tpRep (i : TpIndex p) : GL₄ :=
  borelNFGL ((p : ℚ) ^ 1) ((p : ℚ) ^ (tpExp i).1) ((p : ℚ) ^ (tpExp i).2) (tpData i).1
    (tpData i).2.1 (tpData i).2.2.1 (tpData i).2.2.2

lemma tpRep_int (i : TpIndex p) : ∃ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ,
    (Int.castRingHom ℚ).mapMatrix M = borelNF ((p : ℚ) ^ 1) ((p : ℚ) ^ (tpExp i).1)
      ((p : ℚ) ^ (tpExp i).2) (tpData i).1 (tpData i).2.1 (tpData i).2.2.1 (tpData i).2.2.2 := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rcases i with - | t | ⟨c, t⟩ | ⟨t₀, t₁, t₂⟩
  · exact ⟨fromBlocks !![(p : ℤ), 0; 0, p] 0 0 1, by
      ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [borelNF, tpExp, tpData]⟩
  · exact ⟨fromBlocks !![(p : ℤ), 0; 0, 1] !![0, 0; 0, (t : ℤ)] 0 !![1, 0; 0, (p : ℤ)], by
      ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [borelNF, tpExp, tpData]⟩
  · exact ⟨fromBlocks !![1, -(c : ℤ); 0, p] !![(t : ℤ), 0; 0, 0] 0 !![(p : ℤ), 0; c, 1], by
      ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [borelNF, tpExp, tpData]
      field_simp⟩
  · exact ⟨fromBlocks 1 !![(t₀ : ℤ), t₁; t₁, t₂] 0 !![(p : ℤ), 0; 0, p], by
      ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [borelNF, tpExp, tpData]⟩

lemma tpRep_mem (i : TpIndex p) : tpRep i ∈ DoubleCoset.doubleCoset
    ((heckeCosetDiag p 0 0 1).rep : GL₄) (Γ₂ : Set GL₄) Γ₂ := by
  have hmon : tpRep i ∈ heckeMonoidAt (Fin 2) p := borelNFGL_mem_heckeMonoidAt (tpRep_int i)
  have hdet₀ : ((tpRep i : GL₄) : M₄).det = (p : ℚ) ^ (2 * 1) :=
    det_borelNFGL (δ := 1) _ _ _ _
  refine mem_doubleCoset_heckeCosetDiag (x := ⟨tpRep i, hmon⟩) fun a' s' t' h ↦ ?_
  have hdet : ((symplecticDiag p a' s' t' : GL₄) : M₄).det = (p : ℚ) ^ (2 * 1) :=
    (det_eq_of_mem_doubleCoset h).symm.trans hdet₀
  rw [det_symplecticDiag] at hdet
  have h' : 4 * a' + 4 * s' + 2 * t' = 2 * 1 :=
    Nat.pow_right_injective (Fact.out : p.Prime).two_le (Nat.cast_injective (R := ℚ) (by
      push_cast
      exact hdet))
  simp only [Prod.mk.injEq]
  omega

lemma exists_tpRep_eq {d₀ d₁ c x₀₀ x₀₁ x₁₁ : ℚ} (hd₀ : 0 < d₀) (hd₁ : 0 < d₁) (hc : 0 ≤ c)
    (hc' : c < d₀) (hx₀₀ : 0 ≤ x₀₀) (hx₀₀' : x₀₀ < 1) (hx₀₁ : 0 ≤ x₀₁) (hx₀₁' : x₀₁ < 1)
    (hx₁₁ : 0 ≤ x₁₁) (hx₁₁' : x₁₁ < 1) (M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ)
    (hM : (Int.castRingHom ℚ).mapMatrix M = borelNF ((p : ℚ) ^ 1) d₀ d₁ c x₀₀ x₀₁ x₁₁) :
    ∃ i : TpIndex p, tpRep i = borelNFGL ((p : ℚ) ^ 1) d₀ d₁ c x₀₀ x₀₁ x₁₁ := by
  have hp₀ : (0 : ℚ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have he (a b : Fin 2 ⊕ Fin 2) :
      ∃ z : ℤ, (z : ℚ) = borelNF ((p : ℚ) ^ 1) d₀ d₁ c x₀₀ x₀₁ x₁₁ a b :=
    ⟨M a b, by rw [← hM]; rfl⟩
  have e₀ : ∃ z : ℤ, (z : ℚ) = d₀ := by simpa [borelNF] using he (.inr 0) (.inr 0)
  have e₀' : ∃ z : ℤ, (z : ℚ) = p / d₀ := by simpa [borelNF] using he (.inl 0) (.inl 0)
  have e₁ : ∃ z : ℤ, (z : ℚ) = d₁ := by simpa [borelNF] using he (.inr 1) (.inr 1)
  have e₁' : ∃ z : ℤ, (z : ℚ) = p / d₁ := by simpa [borelNF] using he (.inl 1) (.inl 1)
  have ec : ∃ z : ℤ, (z : ℚ) = c := by simpa [borelNF] using he (.inr 1) (.inr 0)
  have f₀₀ : ∃ z : ℤ, (z : ℚ) = x₀₀ * d₀ + x₀₁ * c := by simpa [borelNF] using he (.inl 0) (.inr 0)
  have f₀₁ : ∃ z : ℤ, (z : ℚ) = x₀₁ * d₁ := by simpa [borelNF] using he (.inl 0) (.inr 1)
  have f₁₀ : ∃ z : ℤ, (z : ℚ) = x₀₁ * d₀ + x₁₁ * c := by simpa [borelNF] using he (.inl 1) (.inr 0)
  have f₁₁ : ∃ z : ℤ, (z : ℚ) = x₁₁ * d₁ := by simpa [borelNF] using he (.inl 1) (.inr 1)
  have g : ∃ z : ℤ, (z : ℚ) = -(p * c) / (d₀ * d₁) := by
    simpa [borelNF] using he (.inl 0) (.inl 1)
  rcases eq_one_or_eq_of_int hd₀ e₀ e₀' with rfl | rfl <;>
    rcases eq_one_or_eq_of_int hd₁ e₁ e₁' with rfl | rfl
  · have hc₀ : c = 0 := eq_zero_of_int hc hc' ec
    subst hc₀
    have h₀₁ : x₀₁ = 0 := eq_zero_of_int hx₀₁ hx₀₁' (by simpa using f₀₁)
    have h₁₁ : x₁₁ = 0 := eq_zero_of_int hx₁₁ hx₁₁' (by simpa using f₁₁)
    have h₀₀ : x₀₀ = 0 := eq_zero_of_int hx₀₀ hx₀₀' (by simpa using f₀₀)
    subst h₀₁ h₁₁ h₀₀
    exact ⟨.inl (), by simp [tpRep, tpExp, tpData]⟩
  · have hc₀ : c = 0 := eq_zero_of_int hc hc' ec
    subst hc₀
    have h₀₁ : x₀₁ = 0 := eq_zero_of_int hx₀₁ hx₀₁' (by simpa using f₁₀)
    have h₀₀ : x₀₀ = 0 := eq_zero_of_int hx₀₀ hx₀₀' (by simpa using f₀₀)
    subst h₀₁ h₀₀
    rcases exists_fin_eq_div p (Fact.out : p.Prime).pos hx₁₁ hx₁₁' f₁₁ with ⟨t, rfl⟩
    exact ⟨.inr (.inl t), by simp [tpRep, tpExp, tpData]⟩
  · have h₀₁ : x₀₁ = 0 := eq_zero_of_int hx₀₁ hx₀₁' (by simpa using f₀₁)
    have h₁₁ : x₁₁ = 0 := eq_zero_of_int hx₁₁ hx₁₁' (by simpa using f₁₁)
    subst h₀₁ h₁₁
    rcases exists_fin_eq p hc hc' ec with ⟨c', rfl⟩
    rcases exists_fin_eq_div p (Fact.out : p.Prime).pos hx₀₀ hx₀₀' (by simpa using f₀₀) with
      ⟨t, rfl⟩
    exact ⟨.inr (.inr (.inl (c', t))), by simp [tpRep, tpExp, tpData]⟩
  · have hc₀ : c = 0 := by
      have h : c / p = 0 := by
        refine eq_zero_of_int (div_nonneg hc hp₀.le) ((div_lt_one hp₀).mpr hc') ?_
        rcases g with ⟨z, hz⟩
        refine ⟨-z, ?_⟩
        rw [Int.cast_neg, hz]
        field_simp
      rwa [div_eq_zero_iff, or_iff_left hp₀.ne'] at h
    subst hc₀
    rcases exists_fin_eq_div p (Fact.out : p.Prime).pos hx₀₀ hx₀₀' (by simpa using f₀₀) with
      ⟨t₀, rfl⟩
    rcases exists_fin_eq_div p (Fact.out : p.Prime).pos hx₀₁ hx₀₁' f₀₁ with ⟨t₁, rfl⟩
    rcases exists_fin_eq_div p (Fact.out : p.Prime).pos hx₁₁ hx₁₁' f₁₁ with ⟨t₂, rfl⟩
    exact ⟨.inr (.inr (.inr (t₀, t₁, t₂))), by simp [tpRep, tpExp, tpData]⟩

lemma tpData_fst_mem (i : TpIndex p) : (tpData i).1 ∈ Set.Ico 0 ((p : ℚ) ^ (tpExp i).1) := by
  rcases i with - | t | ⟨c, t⟩ | ⟨t₀, t₁, t₂⟩ <;> simp [tpExp, tpData, (Fact.out : p.Prime).pos]

lemma tpData_snd_mem (i : TpIndex p) :
    ∀ x ∈ ({(tpData i).2.1, (tpData i).2.2.1, (tpData i).2.2.2} : Finset ℚ), x ∈ Set.Ico 0 1 := by
  have hp₀ : (0 : ℚ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have ht (t : Fin p) : (0 : ℚ) ≤ t / p ∧ (t : ℚ) / p < 1 :=
    ⟨by positivity, (div_lt_one hp₀).mpr (by exact_mod_cast t.2)⟩
  rcases i with - | t | ⟨c, t⟩ | ⟨t₀, t₁, t₂⟩ <;> simp [tpData, ht]

/-- The full data `(d₀, d₁, c, x₀₀, x₀₁, x₁₁)` of the right coset representatives of `T(p)`. -/
def tpKey (i : TpIndex p) : ℚ × ℚ × ℚ × ℚ × ℚ × ℚ :=
  ((p : ℚ) ^ (tpExp i).1, (p : ℚ) ^ (tpExp i).2, tpData i)

lemma tpKey_injective : Function.Injective (tpKey (p := p)) := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hdiv (t t' : Fin p) (h : (t : ℚ) / p = t' / p) : t = t' :=
    Fin.ext (by exact_mod_cast (div_left_inj' hp).mp h)
  intro i j h
  have hpow (a b : ℕ) (h : (p : ℚ) ^ a = (p : ℚ) ^ b) : a = b :=
    Nat.pow_right_injective (Fact.out : p.Prime).two_le (by exact_mod_cast h)
  have h₁ : tpExp i = tpExp j :=
    Prod.ext (hpow _ _ (congrArg (fun k ↦ k.1) h)) (hpow _ _ (congrArg (fun k ↦ k.2.1) h))
  have h₂ : tpData i = tpData j := congrArg (fun k ↦ k.2.2) h
  rcases i with _ | t | ⟨c, t⟩ | ⟨t₀, t₁, t₂⟩ <;>
    rcases j with _ | t' | ⟨c', t'⟩ | ⟨t₀', t₁', t₂'⟩ <;>
    simp only [tpExp, Prod.mk.injEq] at h₁ <;> simp only [tpData, Prod.mk.injEq] at h₂ <;>
    try omega
  · rfl
  · rw [hdiv t t' h₂.2.2.2]
  · rw [Fin.ext (by exact_mod_cast h₂.1 : (c : ℕ) = c'), hdiv t t' h₂.2.1]
  · rw [hdiv t₀ t₀' h₂.2.1, hdiv t₁ t₁' h₂.2.2.1, hdiv t₂ t₂' h₂.2.2.2]

lemma eq_of_tpRep_mul_inv_mem {i j : TpIndex p} (h : tpRep i * (tpRep j)⁻¹ ∈ Γ₂) : i = j := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hp₀ : (0 : ℚ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  rcases h with ⟨g, -, hg⟩
  have hgm : (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ).map (↑) * borelNF ((p : ℚ) ^ 1)
      ((p : ℚ) ^ (tpExp j).1) ((p : ℚ) ^ (tpExp j).2) (tpData j).1 (tpData j).2.1 (tpData j).2.2.1
        (tpData j).2.2.2 = borelNF ((p : ℚ) ^ 1) ((p : ℚ) ^ (tpExp i).1) ((p : ℚ) ^ (tpExp i).2)
          (tpData i).1 (tpData i).2.1 (tpData i).2.2.1 (tpData i).2.2.2 := by
    have e : spToGL (Fin 2) g * tpRep j = tpRep i := by rw [hg, inv_mul_cancel_right]
    have e' : ((spToGL (Fin 2) g * tpRep j : GL₄) : M₄) = (tpRep i : M₄) :=
      congrArg (fun y : GL₄ ↦ (y : M₄)) e
    simp only [Units.val_mul, tpRep] at e'
    rwa [coe_borelNFGL (pow_ne_zero 1 hp) (pow_ne_zero _ hp) (pow_ne_zero _ hp),
      coe_borelNFGL (pow_ne_zero 1 hp) (pow_ne_zero _ hp) (pow_ne_zero _ hp)] at e'
  exact tpKey_injective (borelNF_eq_of_mul_eq (pow_ne_zero 1 hp) g.2 (pow_pos hp₀ _)
    (pow_pos hp₀ _) (pow_pos hp₀ _) (pow_pos hp₀ _) (tpData_fst_mem i) (tpData_fst_mem j)
    (tpData_snd_mem i) (tpData_snd_mem j) hgm)

lemma exists_borelNF_of_mem_doubleCoset {a s t : ℕ} {x : GL₄}
    (hx : x ∈ DoubleCoset.doubleCoset ((heckeCosetDiag p a s t).rep : GL₄) (Γ₂ : Set GL₄) Γ₂) :
    ∃ γ ∈ Γ₂, ∃ d₀ d₁ c x₀₀ x₀₁ x₁₁ : ℚ, 0 < d₀ ∧ 0 < d₁ ∧ 0 ≤ c ∧ c < d₀ ∧
      0 ≤ x₀₀ ∧ x₀₀ < 1 ∧ 0 ≤ x₀₁ ∧ x₀₁ < 1 ∧ 0 ≤ x₁₁ ∧ x₁₁ < 1 ∧
        (∃ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ, (Int.castRingHom ℚ).mapMatrix M =
          borelNF ((p : ℚ) ^ (2 * a + 2 * s + t)) d₀ d₁ c x₀₀ x₀₁ x₁₁) ∧
        γ * x = borelNFGL ((p : ℚ) ^ (2 * a + 2 * s + t)) d₀ d₁ c x₀₀ x₀₁ x₁₁ := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hxΔ : x ∈ heckeMonoidAt (Fin 2) p := mem_heckeMonoidAt_of_mem_doubleCoset hx
  rcases exists_mul_eq_borelNF (Fact.out : p.Prime).ne_zero ⟨x, hxΔ⟩ with
    ⟨k, γ, hγ, d₀, d₁, c, x₀₀, x₀₁, x₁₁, hd₀, hd₁, hc, hc', h₀₀, h₀₀', h₀₁, h₀₁', h₁₁, h₁₁', h⟩
  have hk : k = 2 * a + 2 * s + t := by
    have h₁ : ((γ * x : GL₄) : M₄).det = (borelNF ((p : ℚ) ^ k) d₀ d₁ c x₀₀ x₀₁ x₁₁).det :=
      congrArg Matrix.det h
    rw [Units.val_mul, Matrix.det_mul, det_eq_one_of_mem hγ, one_mul,
      det_eq_of_mem_doubleCoset hx, det_eq_of_mem_doubleCoset
        (rep_mem_doubleCoset_symplecticDiag (p := p) a s t), det_symplecticDiag,
      det_borelNF hd₀.ne' hd₁.ne', ← pow_mul] at h₁
    have h₂ : 4 * a + 4 * s + 2 * t = k * 2 :=
      Nat.pow_right_injective (Fact.out : p.Prime).two_le (Nat.cast_injective (R := ℚ) (by
        push_cast
        exact h₁))
    omega
  subst hk
  have hγx : γ * x ∈ heckeMonoidAt (Fin 2) p := mul_mem (heckeGamma_le_heckeMonoidAt p hγ) hxΔ
  rcases exists_intMatrix ⟨γ * x, hγx⟩ with ⟨M, -, hM, -⟩
  refine ⟨γ, hγ, d₀, d₁, c, x₀₀, x₀₁, x₁₁, hd₀, hd₁, hc, hc', h₀₀, h₀₀', h₀₁, h₀₁', h₁₁, h₁₁',
    ⟨M, hM.trans h⟩, Units.ext ?_⟩
  rw [h, coe_borelNFGL (pow_ne_zero _ hp) hd₀.ne' hd₁.ne']

/-- **The Satake map on `T(p)`**: `ω_α(T(p)) = α₀ (1 + α_0)(1 + α_1)`, the right cosets of
`T(p) = Γ diag(1, 1, p, p) Γ` being the `1 + p + p² + p³` Borel normal forms with
`(d₀, d₁) = (1, 1), (1, p), (p, 1), (p, p)` (`SiegelUpperHalfSpace.tpRep`). -/
lemma satakeMap_Tp : satakeMap p α₀ α (HeckeCosetModule.single ℂ (heckeCosetDiag p 0 0 1) 1) =
    (α₀ : ℂ) * (1 + α 0) * (1 + α 1) := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [satakeMap_single_eq_sum α₀ α _ tpRep tpRep_mem fun x hx ↦ ?_]
  · have hval (i : TpIndex p) : HeckeCoset.borelValue Γ₂ ((satakeCharacter p α₀ α).comp
        (satakeValuation p)) (tpRep i) = (α₀ : ℂ) ^ 1 *
          ((α 0 : ℂ) * ((p : ℂ) ^ 2)⁻¹) ^ (tpExp i).1 * ((α 1 : ℂ) * (p : ℂ)⁻¹) ^ (tpExp i).2 :=
      borelValue_borelNFGL α₀ α _ _ _ _
    simp only [hval, Fintype.sum_sum_type, tpExp, Finset.sum_const, Finset.card_univ,
      Fintype.card_unit, Fintype.card_fin, Fintype.card_prod, nsmul_eq_mul]
    push_cast
    field_simp
    ring1
  · rcases exists_borelNF_of_mem_doubleCoset hx with
      ⟨γ, hγ, d₀, d₁, c, x₀₀, x₀₁, x₁₁, hd₀, hd₁, hc, hc', h₀₀, h₀₀', h₀₁, h₀₁', h₁₁, h₁₁',
        ⟨M, hM⟩, h⟩
    simp only [mul_zero, zero_add] at hM h
    rcases exists_tpRep_eq hd₀ hd₁ hc hc' h₀₀ h₀₀' h₀₁ h₀₁' h₁₁ h₁₁' M hM with ⟨i, hi⟩
    have hmem : x * (tpRep i)⁻¹ ∈ Γ₂ := by
      rw [hi, ← h, mul_inv_rev, mul_inv_cancel_left]
      exact inv_mem hγ
    refine ⟨i, hmem, fun j hj ↦ eq_of_tpRep_mul_inv_mem ?_⟩
    have e : tpRep j * (tpRep i)⁻¹ = (x * (tpRep j)⁻¹)⁻¹ * (x * (tpRep i)⁻¹) := by
      group
    rw [e]
    exact mul_mem (inv_mem hj) hmem

end SiegelUpperHalfSpace
