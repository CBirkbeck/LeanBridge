import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.DegreeTwoSatakeMap

/-!
# The Satake map of `Sp(4, ℤ)` on `T_1(p²)`

The double coset `T_1(p²) = Γ diag(1, p, p², p) Γ` of `Γ = Sp(4, ℤ)` consists of the integral
symplectic similitudes of multiplier `p²` whose `2 × 2` minors are all divisible by `p` but whose
entries are not (`SiegelUpperHalfSpace.exists_eq_heckeCosetDiag` and its invariants), those of rank
`1` modulo `p`. Its `p (p + 1)(p² + 1)` right cosets are the Borel normal forms
`(p² D⁻ᵀ, X D; 0, D)` (`SiegelUpperHalfSpace.exists_mul_eq_borelNF`) of five families:

* `D = diag(1, p)` and `X = 0` (one coset);
* `D = (p, 0; c, 1)`, `0 ≤ c < p`, and `X = 0` (`p` cosets);
* `D = p 1` and `X = T/p`, `T` symmetric of rank `1` modulo `p`, so `T = λ v vᵀ` with
  `λ ∈ (ℤ/p)ˣ` and `v = (0, 1)` or `(1, a)` (`p² - 1` cosets);
* `D = diag(p, p²)` and `X = (0, b/p; b/p, w/p²)` (`p³` cosets);
* `D = (p², 0; p x, p)` and `X = (w/p², s/p; s/p, 0)` (`p⁴` cosets).

Integrality and the minors of the normal forms leave exactly these. The families agree with a
brute-force enumeration of the normal forms of multiplier `p²` for `p = 2, 3, 5`.

## Main definitions

* `SiegelUpperHalfSpace.t1Rep`: the right coset representatives of `T_1(p²)`.

## Main results

* `SiegelUpperHalfSpace.satakeMap_T₁`:
  `ω_α(T_1(p²)) = α₀² p⁻¹ ((α_0 + α_1)(1 + α_0 α_1) + (1 - p⁻²) α_0 α_1)`.
-/

open Matrix hiding mul_inv_rev

open scoped Pointwise

namespace SiegelUpperHalfSpace

local notation "Mℤ" => Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℤ

local notation "M₄" => Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℚ

local notation "GL₄" => GL (Fin 2 ⊕ Fin 2) ℚ

local notation "Γ₂" => heckeGamma (Fin 2)

variable {p : ℕ} [Fact p.Prime]

/-! ### Rank one symmetric matrices modulo `p` -/

/-- The vector `(0, 1)` or `(1, a)` spanning a line of `(ℤ/p)²`. -/
def lineVec : Option (ZMod p) → Fin 2 → ZMod p
  | none => ![0, 1]
  | some a => ![1, a]

lemma exists_lineVec {t₀₀ t₀₁ t₁₁ : ZMod p} (h : t₀₀ * t₁₁ = t₀₁ ^ 2)
    (h₀ : ¬(t₀₀ = 0 ∧ t₀₁ = 0 ∧ t₁₁ = 0)) : ∃ (l : (ZMod p)ˣ) (v : Option (ZMod p)),
      l * lineVec v 0 * lineVec v 0 = t₀₀ ∧ l * lineVec v 0 * lineVec v 1 = t₀₁ ∧
        l * lineVec v 1 * lineVec v 1 = t₁₁ := by
  by_cases ht : t₀₀ = 0
  · have h₁ : t₀₁ = 0 := by
      rw [ht, zero_mul, eq_comm] at h
      exact pow_eq_zero_iff two_ne_zero |>.mp h
    have h₂ : t₁₁ ≠ 0 := fun h₂ ↦ h₀ ⟨ht, h₁, h₂⟩
    exact ⟨Units.mk0 t₁₁ h₂, none, by simp [lineVec, ht], by simp [lineVec, h₁],
      by simp [lineVec]⟩
  · refine ⟨Units.mk0 t₀₀ ht, some (t₀₁ / t₀₀), by simp [lineVec], ?_, ?_⟩
    · simp [lineVec]
      field_simp
    · simp [lineVec]
      field_simp
      linear_combination h.symm

lemma lineVec_injective {l l' : (ZMod p)ˣ} {v v' : Option (ZMod p)}
    (h₀₀ : l * lineVec v 0 * lineVec v 0 = l' * lineVec v' 0 * lineVec v' 0)
    (h₀₁ : l * lineVec v 0 * lineVec v 1 = l' * lineVec v' 0 * lineVec v' 1)
    (h₁₁ : l * lineVec v 1 * lineVec v 1 = l' * lineVec v' 1 * lineVec v' 1) :
    (l, v) = (l', v') := by
  rcases v with _ | a <;> rcases v' with _ | a' <;> simp [lineVec] at h₀₀ h₀₁ h₁₁
  · rw [Units.ext h₁₁]
  · exact absurd h₀₀.symm l'.ne_zero
  · rw [Units.ext h₀₀] at h₀₁ ⊢
    rw [mul_left_cancel₀ l'.ne_zero h₀₁]

/-! ### The right cosets of `T_1(p²)` -/

variable (p) in
/-- The index set of the right cosets of `T_1(p²)`: the five families of Borel normal forms with
`(d₀, d₁) = (1, p), (p, 1), (p, p), (p, p²), (p², p)`. -/
abbrev T1Index : Type :=
  Unit ⊕ Fin p ⊕ ((ZMod p)ˣ × Option (ZMod p)) ⊕ (Fin p × Fin (p ^ 2)) ⊕
    (Fin p × Fin p × Fin (p ^ 2))

/-- The exponents `(v_p(d₀), v_p(d₁))` of the right coset representatives of `T_1(p²)`. -/
def t1Exp : T1Index p → ℕ × ℕ
  | .inl _ => (0, 1)
  | .inr (.inl _) => (1, 0)
  | .inr (.inr (.inl _)) => (1, 1)
  | .inr (.inr (.inr (.inl _))) => (1, 2)
  | .inr (.inr (.inr (.inr _))) => (2, 1)

/-- The data `(c, x₀₀, x₀₁, x₁₁)` of the right coset representatives of `T_1(p²)`. -/
def t1Data : T1Index p → ℚ × ℚ × ℚ × ℚ
  | .inl _ => (0, 0, 0, 0)
  | .inr (.inl c) => (c, 0, 0, 0)
  | .inr (.inr (.inl (l, v))) => (0, ((l * lineVec v 0 * lineVec v 0 : ZMod p).val : ℚ) / p,
      ((l * lineVec v 0 * lineVec v 1 : ZMod p).val : ℚ) / p,
      ((l * lineVec v 1 * lineVec v 1 : ZMod p).val : ℚ) / p)
  | .inr (.inr (.inr (.inl (b, w)))) => (0, 0, b / p, w / p ^ 2)
  | .inr (.inr (.inr (.inr (x, s, w)))) => (p * x, w / p ^ 2, s / p, 0)

/-- The integral matrices of the right coset representatives of `T_1(p²)`. -/
def t1Mat : T1Index p → Mℤ
  | .inl _ => fromBlocks !![(p : ℤ) ^ 2, 0; 0, p] 0 0 !![1, 0; 0, (p : ℤ)]
  | .inr (.inl c) => fromBlocks !![(p : ℤ), -(p * c); 0, p ^ 2] 0 0 !![(p : ℤ), 0; c, 1]
  | .inr (.inr (.inl (l, v))) => fromBlocks !![(p : ℤ), 0; 0, p]
      !![((l * lineVec v 0 * lineVec v 0 : ZMod p).val : ℤ),
        ((l * lineVec v 0 * lineVec v 1 : ZMod p).val : ℤ);
        ((l * lineVec v 0 * lineVec v 1 : ZMod p).val : ℤ),
        ((l * lineVec v 1 * lineVec v 1 : ZMod p).val : ℤ)] 0 !![(p : ℤ), 0; 0, p]
  | .inr (.inr (.inr (.inl (b, w)))) =>
      fromBlocks !![(p : ℤ), 0; 0, 1] !![0, (b : ℤ) * p; b, w] 0 !![(p : ℤ), 0; 0, p ^ 2]
  | .inr (.inr (.inr (.inr (x, s, w)))) => fromBlocks !![1, -(x : ℤ); 0, p]
      !![(w : ℤ) + s * x, s; s * p, 0] 0 !![(p : ℤ) ^ 2, 0; p * x, p]

/-- The right coset representatives of `T_1(p²)`, in Borel normal form. -/
noncomputable def t1Rep (i : T1Index p) : GL₄ :=
  borelNFGL ((p : ℚ) ^ 2) ((p : ℚ) ^ (t1Exp i).1) ((p : ℚ) ^ (t1Exp i).2) (t1Data i).1
    (t1Data i).2.1 (t1Data i).2.2.1 (t1Data i).2.2.2

lemma t1Mat_cast (i : T1Index p) : (Int.castRingHom ℚ).mapMatrix (t1Mat i) =
    borelNF ((p : ℚ) ^ 2) ((p : ℚ) ^ (t1Exp i).1) ((p : ℚ) ^ (t1Exp i).2) (t1Data i).1
      (t1Data i).2.1 (t1Data i).2.2.1 (t1Data i).2.2.2 := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rcases i with - | c | ⟨l, v⟩ | ⟨b, w⟩ | ⟨x, s, w⟩ <;>
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;>
    simp [borelNF, t1Mat, t1Exp, t1Data] <;> field_simp

lemma coe_t1Rep (i : T1Index p) : (Int.castRingHom ℚ).mapMatrix (t1Mat i) = (t1Rep i : M₄) := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [t1Rep, coe_borelNFGL (pow_ne_zero 2 hp) (pow_ne_zero _ hp) (pow_ne_zero _ hp), t1Mat_cast]

lemma minorsDvd_of_cast_eq {x : GL₄} {M : Mℤ} (hM : (Int.castRingHom ℚ).mapMatrix M = x)
    (u w : Fin 2 ⊕ Fin 2 → ZMod p) (h : ∀ i j, (M i j : ZMod p) = u i * w j) :
    MinorsDvd p 1 x :=
  ⟨M, hM, fun i i' j j' ↦ by
    rw [pow_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [h, h, h, h]
    ring1⟩

lemma not_entriesDvd_of_cast_ne {x : GL₄} {M : Mℤ} (hM : (Int.castRingHom ℚ).mapMatrix M = x)
    {i j : Fin 2 ⊕ Fin 2} (h : (M i j : ZMod p) ≠ 0) : ¬EntriesDvd p 1 x := by
  rintro ⟨M', hM', hdvd⟩
  have e : M' = M := Matrix.map_injective (Int.cast_injective (α := ℚ)) (hM'.trans hM.symm)
  subst e
  exact h ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by simpa using hdvd i j))

lemma minorsDvd_t1Rep (i : T1Index p) : MinorsDvd p 1 (t1Rep i) := by
  rcases i with - | c | ⟨l, v⟩ | ⟨b, w⟩ | ⟨x, s, w⟩
  · refine minorsDvd_of_cast_eq (coe_t1Rep _) (Sum.elim ![0, 0] ![1, 0])
      (Sum.elim ![0, 0] ![1, 0]) ?_
    rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [t1Mat]
  · refine minorsDvd_of_cast_eq (coe_t1Rep _) (Sum.elim ![0, 0] ![0, 1])
      (Sum.elim ![0, 0] ![(c : ZMod p), 1]) ?_
    rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [t1Mat]
  · refine minorsDvd_of_cast_eq (coe_t1Rep _)
      (Sum.elim ![l * lineVec v 0, l * lineVec v 1] ![0, 0])
      (Sum.elim ![0, 0] ![lineVec v 0, lineVec v 1]) ?_
    rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [t1Mat]
    ring1
  · refine minorsDvd_of_cast_eq (coe_t1Rep _) (Sum.elim ![0, 1] ![0, 0])
      (Sum.elim ![0, 1] ![(b : ZMod p), (w : ZMod p)]) ?_
    rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [t1Mat]
  · refine minorsDvd_of_cast_eq (coe_t1Rep _) (Sum.elim ![1, 0] ![0, 0])
      (Sum.elim ![1, -(x : ZMod p)] ![(w : ZMod p) + s * x, (s : ZMod p)]) ?_
    rintro (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [t1Mat]

lemma not_entriesDvd_t1Rep (i : T1Index p) : ¬EntriesDvd p 1 (t1Rep i) := by
  rcases i with - | c | ⟨l, v⟩ | ⟨b, w⟩ | ⟨x, s, w⟩
  · exact not_entriesDvd_of_cast_ne (coe_t1Rep _) (i := .inr 0) (j := .inr 0) (by simp [t1Mat])
  · exact not_entriesDvd_of_cast_ne (coe_t1Rep _) (i := .inr 1) (j := .inr 1) (by simp [t1Mat])
  · rcases v with _ | a
    · exact not_entriesDvd_of_cast_ne (coe_t1Rep _) (i := .inl 1) (j := .inr 1)
        (by simp [t1Mat, lineVec])
    · exact not_entriesDvd_of_cast_ne (coe_t1Rep _) (i := .inl 0) (j := .inr 0)
        (by simp [t1Mat, lineVec])
  · exact not_entriesDvd_of_cast_ne (coe_t1Rep _) (i := .inl 1) (j := .inl 1) (by simp [t1Mat])
  · exact not_entriesDvd_of_cast_ne (coe_t1Rep _) (i := .inl 0) (j := .inl 0) (by simp [t1Mat])

lemma mem_doubleCoset_symm {x y : GL₄} (h : x ∈ DoubleCoset.doubleCoset y (Γ₂ : Set GL₄) Γ₂) :
    y ∈ DoubleCoset.doubleCoset x (Γ₂ : Set GL₄) Γ₂ := by
  rw [DoubleCoset.doubleCoset_eq_of_mem h]
  exact DoubleCoset.mem_doubleCoset_self _ _ _

lemma mul_mem_doubleCoset {x y γ : GL₄} (hγ : γ ∈ Γ₂)
    (h : x ∈ DoubleCoset.doubleCoset y (Γ₂ : Set GL₄) Γ₂) :
    γ * x ∈ DoubleCoset.doubleCoset y (Γ₂ : Set GL₄) Γ₂ := by
  rcases DoubleCoset.mem_doubleCoset.mp h with ⟨γ₁, hγ₁, γ₂, hγ₂, rfl⟩
  exact DoubleCoset.mem_doubleCoset.mpr ⟨γ * γ₁, mul_mem hγ hγ₁, γ₂, hγ₂, by simp only [mul_assoc]⟩

lemma t1Rep_mem (i : T1Index p) : t1Rep i ∈ DoubleCoset.doubleCoset
    ((heckeCosetDiag p 0 1 0).rep : GL₄) (Γ₂ : Set GL₄) Γ₂ := by
  have hmon : t1Rep i ∈ heckeMonoidAt (Fin 2) p :=
    borelNFGL_mem_heckeMonoidAt ⟨t1Mat i, t1Mat_cast i⟩
  have hdet₀ : ((t1Rep i : GL₄) : M₄).det = (p : ℚ) ^ (2 * 2) :=
    det_borelNFGL (δ := 2) _ _ _ _
  refine mem_doubleCoset_heckeCosetDiag (x := ⟨t1Rep i, hmon⟩) fun a' s' t' h ↦ ?_
  have hdet : ((symplecticDiag p a' s' t' : GL₄) : M₄).det = (p : ℚ) ^ (2 * 2) :=
    (det_eq_of_mem_doubleCoset h).symm.trans hdet₀
  rw [det_symplecticDiag] at hdet
  have h' : 4 * a' + 4 * s' + 2 * t' = 2 * 2 :=
    Nat.pow_right_injective (Fact.out : p.Prime).two_le (Nat.cast_injective (R := ℚ) (by
      push_cast
      exact hdet))
  have hs : 1 ≤ 2 * a' + s' :=
    le_of_minorsDvd_symplecticDiag ((minorsDvd_t1Rep i).of_mem_doubleCoset (mem_doubleCoset_symm h))
  have ha : a' = 0 := by
    by_contra ha
    have e : a' = 1 ∧ s' = 0 ∧ t' = 0 := by
      omega
    rcases e with ⟨rfl, rfl, rfl⟩
    exact not_entriesDvd_t1Rep i ((entriesDvd_symplecticDiag 1 0 0).of_mem_doubleCoset h)
  simp only [Prod.mk.injEq]
  omega

lemma natCast_mul_intCast_ne_one (z : ℤ) : (p : ℚ) * z ≠ 1 := by
  intro h
  have h' : (p : ℤ) * z = 1 := by exact_mod_cast h
  have e : ((p : ℕ) : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right (Int.natCast_nonneg p) h'
  exact (Fact.out : p.Prime).one_lt.ne' (by exact_mod_cast e)

lemma eq_one_or_eq_or_eq_of_int {d : ℚ} (hd : 0 < d) (h₁ : ∃ z : ℤ, (z : ℚ) = d)
    (h₂ : ∃ z : ℤ, (z : ℚ) = p ^ 2 / d) : d = 1 ∨ d = p ∨ d = p ^ 2 := by
  rcases h₁ with ⟨z, rfl⟩
  rcases h₂ with ⟨w, hw⟩
  have hz : 0 < z := by exact_mod_cast hd
  have hzw : z * w = (p : ℤ) ^ 2 := by
    have e : (z : ℚ) * w = (p : ℚ) ^ 2 := by
      rw [hw]
      field_simp
    exact_mod_cast e
  have hw' : 0 ≤ w := by
    by_contra hw'
    have e : z * w < 0 := mul_neg_of_pos_of_neg hz (by omega)
    have e' : (0 : ℤ) < (p : ℤ) ^ 2 := pow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) 2
    linarith
  have hdvd : z.toNat ∣ p ^ 2 := by
    refine ⟨w.toNat, ?_⟩
    zify
    rw [Int.toNat_of_nonneg hz.le, Int.toNat_of_nonneg hw']
    exact hzw.symm
  rcases (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hdvd with ⟨k, hk, hk'⟩
  have hz' : z = (p : ℤ) ^ k := by
    have e : ((z.toNat : ℕ) : ℤ) = ((p ^ k : ℕ) : ℤ) := by rw [hk']
    rwa [Int.toNat_of_nonneg hz.le, Nat.cast_pow] at e
  interval_cases k <;> simp [hz']

lemma exists_t1Rep_eq {d₀ d₁ c x₀₀ x₀₁ x₁₁ : ℚ} (hd₀ : 0 < d₀) (hd₁ : 0 < d₁) (hc : 0 ≤ c)
    (hc' : c < d₀) (hx₀₀ : 0 ≤ x₀₀) (hx₀₀' : x₀₀ < 1) (hx₀₁ : 0 ≤ x₀₁) (hx₀₁' : x₀₁ < 1)
    (hx₁₁ : 0 ≤ x₁₁) (hx₁₁' : x₁₁ < 1)
    (hmin : MinorsDvd p 1 (borelNFGL ((p : ℚ) ^ 2) d₀ d₁ c x₀₀ x₀₁ x₁₁))
    (hent : ¬EntriesDvd p 1 (borelNFGL ((p : ℚ) ^ 2) d₀ d₁ c x₀₀ x₀₁ x₁₁)) :
    ∃ i : T1Index p, t1Rep i = borelNFGL ((p : ℚ) ^ 2) d₀ d₁ c x₀₀ x₀₁ x₁₁ := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hp₀ : (0 : ℚ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  rcases hmin with ⟨M, hM, hdvd⟩
  rw [coe_borelNFGL (pow_ne_zero 2 hp) hd₀.ne' hd₁.ne'] at hM
  have he (a b : Fin 2 ⊕ Fin 2) :
      ∃ z : ℤ, (z : ℚ) = borelNF ((p : ℚ) ^ 2) d₀ d₁ c x₀₀ x₀₁ x₁₁ a b :=
    ⟨M a b, by rw [← hM]; rfl⟩
  have hm (a a' b b' : Fin 2 ⊕ Fin 2) : ∃ z : ℤ, (p : ℚ) * z =
      borelNF ((p : ℚ) ^ 2) d₀ d₁ c x₀₀ x₀₁ x₁₁ a b *
          borelNF ((p : ℚ) ^ 2) d₀ d₁ c x₀₀ x₀₁ x₁₁ a' b' -
        borelNF ((p : ℚ) ^ 2) d₀ d₁ c x₀₀ x₀₁ x₁₁ a b' *
          borelNF ((p : ℚ) ^ 2) d₀ d₁ c x₀₀ x₀₁ x₁₁ a' b := by
    rcases hdvd a a' b b' with ⟨z, hz⟩
    have hz' : (p : ℤ) * z = M a b * M a' b' - M a b' * M a' b := by
      rw [← pow_one (p : ℤ)]
      exact hz.symm
    refine ⟨z, ?_⟩
    rw [← hM]
    simp only [RingHom.mapMatrix_apply, map_apply, eq_intCast]
    exact_mod_cast hz'
  have e₀ : ∃ z : ℤ, (z : ℚ) = d₀ := by simpa [borelNF] using he (.inr 0) (.inr 0)
  have e₀' : ∃ z : ℤ, (z : ℚ) = p ^ 2 / d₀ := by simpa [borelNF] using he (.inl 0) (.inl 0)
  have e₁ : ∃ z : ℤ, (z : ℚ) = d₁ := by simpa [borelNF] using he (.inr 1) (.inr 1)
  have e₁' : ∃ z : ℤ, (z : ℚ) = p ^ 2 / d₁ := by simpa [borelNF] using he (.inl 1) (.inl 1)
  have ec : ∃ z : ℤ, (z : ℚ) = c := by simpa [borelNF] using he (.inr 1) (.inr 0)
  have f₀₀ : ∃ z : ℤ, (z : ℚ) = x₀₀ * d₀ + x₀₁ * c := by
    simpa [borelNF] using he (.inl 0) (.inr 0)
  have f₀₁ : ∃ z : ℤ, (z : ℚ) = x₀₁ * d₁ := by simpa [borelNF] using he (.inl 0) (.inr 1)
  have f₁₀ : ∃ z : ℤ, (z : ℚ) = x₀₁ * d₀ + x₁₁ * c := by
    simpa [borelNF] using he (.inl 1) (.inr 0)
  have f₁₁ : ∃ z : ℤ, (z : ℚ) = x₁₁ * d₁ := by simpa [borelNF] using he (.inl 1) (.inr 1)
  have g : ∃ z : ℤ, (z : ℚ) = -(p ^ 2 * c) / (d₀ * d₁) := by
    simpa [borelNF] using he (.inl 0) (.inl 1)
  rcases eq_one_or_eq_or_eq_of_int hd₀ e₀ e₀' with rfl | rfl | rfl <;>
    rcases eq_one_or_eq_or_eq_of_int hd₁ e₁ e₁' with rfl | rfl | rfl
  · rcases hm (.inr 0) (.inr 1) (.inr 0) (.inr 1) with ⟨z, hz⟩
    simp [borelNF] at hz
    exact absurd hz (natCast_mul_intCast_ne_one z)
  · have hc₀ : c = 0 := eq_zero_of_int hc hc' ec
    subst hc₀
    have h₀₀ : x₀₀ = 0 := eq_zero_of_int hx₀₀ hx₀₀' (by simpa using f₀₀)
    have h₀₁ : x₀₁ = 0 := eq_zero_of_int hx₀₁ hx₀₁' (by simpa using f₁₀)
    have h₁₁ : x₁₁ = 0 := by
      rcases hm (.inl 1) (.inr 0) (.inr 0) (.inr 1) with ⟨z, hz⟩
      refine eq_zero_of_int hx₁₁ hx₁₁' ⟨-z, mul_left_cancel₀ hp ?_⟩
      simp [borelNF] at hz
      push_cast
      linarith
    subst h₀₀ h₀₁ h₁₁
    exact ⟨.inl (), by simp [t1Rep, t1Exp, t1Data]⟩
  · rcases hm (.inl 1) (.inr 0) (.inl 1) (.inr 0) with ⟨z, hz⟩
    simp [borelNF] at hz
    exact absurd hz (natCast_mul_intCast_ne_one z)
  · rcases exists_fin_eq p hc hc' ec with ⟨c', rfl⟩
    have h₀₁ : x₀₁ = 0 := eq_zero_of_int hx₀₁ hx₀₁' (by simpa using f₀₁)
    have h₁₁ : x₁₁ = 0 := eq_zero_of_int hx₁₁ hx₁₁' (by simpa using f₁₁)
    subst h₀₁ h₁₁
    have h₀₀ : x₀₀ = 0 := by
      rcases hm (.inl 0) (.inr 1) (.inr 0) (.inr 1) with ⟨z, hz⟩
      refine eq_zero_of_int hx₀₀ hx₀₀' ⟨z, mul_left_cancel₀ hp ?_⟩
      simp [borelNF] at hz
      linarith
    subst h₀₀
    exact ⟨.inr (.inl c'), by simp [t1Rep, t1Exp, t1Data]⟩
  · have hc₀ : c = 0 := by
      rcases ec with ⟨zc, rfl⟩
      have k : borelNF ((p : ℚ) ^ 2) p p zc x₀₀ x₀₁ x₁₁ (.inl 0) (.inl 1) = -zc := by
        simp [borelNF]
        field_simp
      rcases hm (.inl 0) (.inr 1) (.inl 1) (.inr 0) with ⟨z, hz⟩
      rw [k] at hz
      simp [borelNF] at hz
      have h₁ : (p : ℤ) ∣ zc ^ 2 := ⟨-z, by
        have e : (zc : ℚ) ^ 2 = p * -z := by linear_combination hz
        exact_mod_cast e⟩
      have h₂ : zc = 0 := Int.eq_zero_of_dvd_of_nonneg_of_lt (by exact_mod_cast hc)
        (by exact_mod_cast hc') ((Nat.prime_iff_prime_int.mp Fact.out).dvd_of_dvd_pow h₁)
      rw [h₂, Int.cast_zero]
    subst hc₀
    rcases exists_fin_eq_div p (Fact.out : p.Prime).pos hx₀₀ hx₀₀' (by simpa using f₀₀) with
      ⟨t₀₀, rfl⟩
    rcases exists_fin_eq_div p (Fact.out : p.Prime).pos hx₀₁ hx₀₁' f₀₁ with ⟨t₀₁, rfl⟩
    rcases exists_fin_eq_div p (Fact.out : p.Prime).pos hx₁₁ hx₁₁' f₁₁ with ⟨t₁₁, rfl⟩
    have hdet : ((t₀₀ : ℕ) : ZMod p) * (t₁₁ : ℕ) = ((t₀₁ : ℕ) : ZMod p) ^ 2 := by
      rcases hm (.inl 0) (.inl 1) (.inr 0) (.inr 1) with ⟨z, hz⟩
      simp [borelNF] at hz
      have e : ((t₀₀ : ℕ) : ℤ) * (t₁₁ : ℕ) - ((t₀₁ : ℕ) : ℤ) ^ 2 = p * z := by
        have e' : ((t₀₀ : ℕ) : ℚ) * (t₁₁ : ℕ) - ((t₀₁ : ℕ) : ℚ) ^ 2 = p * z := by
          linear_combination -hz
        exact_mod_cast e'
      have e'' : ((((t₀₀ : ℕ) : ℤ) * (t₁₁ : ℕ) - ((t₀₁ : ℕ) : ℤ) ^ 2 : ℤ) : ZMod p) =
          ((p * z : ℤ) : ZMod p) :=
        congrArg (Int.cast : ℤ → ZMod p) e
      push_cast at e''
      rwa [ZMod.natCast_self, zero_mul, sub_eq_zero] at e''
    have hne : ¬(((t₀₀ : ℕ) : ZMod p) = 0 ∧ ((t₀₁ : ℕ) : ZMod p) = 0 ∧
        ((t₁₁ : ℕ) : ZMod p) = 0) := by
      rintro ⟨h₀, h₁, h₂⟩
      have z₀ : (t₀₀ : ℕ) = 0 :=
        Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff _ _).mp h₀) t₀₀.2
      have z₁ : (t₀₁ : ℕ) = 0 :=
        Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff _ _).mp h₁) t₀₁.2
      have z₂ : (t₁₁ : ℕ) = 0 :=
        Nat.eq_zero_of_dvd_of_lt ((ZMod.natCast_eq_zero_iff _ _).mp h₂) t₁₁.2
      apply hent
      rw [z₀, z₁, z₂, Nat.cast_zero, zero_div, borelNFGL_eq_symplecticDiag]
      exact entriesDvd_symplecticDiag 1 0 0
    rcases exists_lineVec hdet hne with ⟨l, v, h₀₀, h₀₁, h₁₁⟩
    refine ⟨.inr (.inr (.inl (l, v))), ?_⟩
    simp only [t1Rep, t1Exp, t1Data, h₀₀, h₀₁, h₁₁, ZMod.val_natCast_of_lt t₀₀.2,
      ZMod.val_natCast_of_lt t₀₁.2, ZMod.val_natCast_of_lt t₁₁.2, pow_one]
  · have hc₀ : c = 0 := by
      have h : c / p = 0 := by
        refine eq_zero_of_int (div_nonneg hc hp₀.le) ((div_lt_one hp₀).mpr hc') ?_
        rcases g with ⟨z, hz⟩
        refine ⟨-z, ?_⟩
        rw [Int.cast_neg, hz]
        field_simp
      rwa [div_eq_zero_iff, or_iff_left hp₀.ne'] at h
    subst hc₀
    have h₀₀ : x₀₀ = 0 := by
      rcases hm (.inl 0) (.inl 1) (.inl 1) (.inr 0) with ⟨z, hz⟩
      refine eq_zero_of_int hx₀₀ hx₀₀' ⟨-z, mul_left_cancel₀ hp ?_⟩
      simp [borelNF] at hz
      push_cast
      linarith
    subst h₀₀
    rcases exists_fin_eq_div p (Fact.out : p.Prime).pos hx₀₁ hx₀₁' (by simpa using f₁₀) with
      ⟨b, rfl⟩
    rcases exists_fin_eq_div (p ^ 2) (pow_pos (Fact.out : p.Prime).pos 2) hx₁₁ hx₁₁'
        (by simpa using f₁₁) with
      ⟨w, rfl⟩
    exact ⟨.inr (.inr (.inr (.inl (b, w)))), by simp [t1Rep, t1Exp, t1Data]⟩
  · rcases hm (.inl 0) (.inr 1) (.inl 0) (.inr 1) with ⟨z, hz⟩
    simp [borelNF] at hz
    exact absurd hz (natCast_mul_intCast_ne_one z)
  · have hcx : ∃ z : ℤ, (z : ℚ) = c / p := by
      rcases g with ⟨z, hz⟩
      refine ⟨-z, ?_⟩
      rw [Int.cast_neg, hz]
      field_simp
    rcases exists_fin_eq p (div_nonneg hc hp₀.le) (by rw [div_lt_iff₀ hp₀, ← sq]; exact hc') hcx
      with ⟨x, hx⟩
    have hc₀ : c = p * x := by
      field_simp at hx
      linarith
    subst hc₀
    rcases exists_fin_eq_div p (Fact.out : p.Prime).pos hx₀₁ hx₀₁' f₀₁ with ⟨s, rfl⟩
    have h₁₁ : x₁₁ = 0 := by
      rcases hm (.inl 0) (.inl 1) (.inl 0) (.inr 1) with ⟨z, hz⟩
      refine eq_zero_of_int hx₁₁ hx₁₁' ⟨z, mul_left_cancel₀ hp ?_⟩
      simp [borelNF] at hz
      linarith
    subst h₁₁
    have hw : ∃ z : ℤ, (z : ℚ) = x₀₀ * ((p ^ 2 : ℕ) : ℚ) := by
      rcases f₀₀ with ⟨z, hz⟩
      refine ⟨z - s * x, ?_⟩
      push_cast
      rw [hz]
      field_simp
      ring1
    rcases exists_fin_eq_div (p ^ 2) (pow_pos (Fact.out : p.Prime).pos 2) hx₀₀ hx₀₀' hw with
      ⟨w, rfl⟩
    exact ⟨.inr (.inr (.inr (.inr (x, s, w)))), by simp [t1Rep, t1Exp, t1Data]⟩
  · rcases hm (.inl 0) (.inl 1) (.inl 0) (.inl 1) with ⟨z, hz⟩
    simp [borelNF] at hz
    exact absurd hz (natCast_mul_intCast_ne_one z)

lemma t1Data_fst_mem (i : T1Index p) : (t1Data i).1 ∈ Set.Ico 0 ((p : ℚ) ^ (t1Exp i).1) := by
  have hp₀ : (0 : ℚ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  rcases i with - | c | ⟨l, v⟩ | ⟨b, w⟩ | ⟨x, s, w⟩
  · simp [t1Exp, t1Data]
  · simp [t1Exp, t1Data]
  · simp [t1Data, hp₀]
  · simp [t1Data, hp₀]
  · simp only [t1Exp, t1Data, sq]
    exact ⟨by positivity, mul_lt_mul_of_pos_left (by exact_mod_cast x.2) hp₀⟩

lemma t1Data_snd_mem (i : T1Index p) :
    ∀ x ∈ ({(t1Data i).2.1, (t1Data i).2.2.1, (t1Data i).2.2.2} : Finset ℚ), x ∈ Set.Ico 0 1 := by
  have hp₀ : (0 : ℚ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have ht (t : Fin p) : (0 : ℚ) ≤ t / p ∧ (t : ℚ) / p < 1 :=
    ⟨by positivity, (div_lt_one hp₀).mpr (by exact_mod_cast t.2)⟩
  have ht₂ (t : Fin (p ^ 2)) : (0 : ℚ) ≤ t / p ^ 2 ∧ (t : ℚ) / p ^ 2 < 1 :=
    ⟨by positivity, (div_lt_one (pow_pos hp₀ 2)).mpr (by exact_mod_cast t.2)⟩
  have hz (z : ZMod p) : (0 : ℚ) ≤ z.val / p ∧ (z.val : ℚ) / p < 1 :=
    ⟨by positivity, (div_lt_one hp₀).mpr (by exact_mod_cast z.val_lt)⟩
  rcases i with - | c | ⟨l, v⟩ | ⟨b, w⟩ | ⟨x, s, w⟩ <;>
    simp [t1Data, ht, ht₂, hz, -ZMod.natCast_val]

/-- The full data `(d₀, d₁, c, x₀₀, x₀₁, x₁₁)` of the right coset representatives of `T_1(p²)`. -/
def t1Key (i : T1Index p) : ℚ × ℚ × ℚ × ℚ × ℚ × ℚ :=
  ((p : ℚ) ^ (t1Exp i).1, (p : ℚ) ^ (t1Exp i).2, t1Data i)

lemma t1Key_injective : Function.Injective (t1Key (p := p)) := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hdiv (t t' : Fin p) (h : (t : ℚ) / p = t' / p) : t = t' :=
    Fin.ext (by exact_mod_cast (div_left_inj' hp).mp h)
  have hdiv₂ (t t' : Fin (p ^ 2)) (h : (t : ℚ) / p ^ 2 = t' / p ^ 2) : t = t' :=
    Fin.ext (by exact_mod_cast (div_left_inj' (pow_ne_zero 2 hp)).mp h)
  have hval (z z' : ZMod p) (h : (z.val : ℚ) / p = z'.val / p) : z = z' :=
    ZMod.val_injective p (by exact_mod_cast (div_left_inj' hp).mp h)
  intro i j h
  have hpow (a b : ℕ) (h : (p : ℚ) ^ a = (p : ℚ) ^ b) : a = b :=
    Nat.pow_right_injective (Fact.out : p.Prime).two_le (by exact_mod_cast h)
  have h₁ : t1Exp i = t1Exp j :=
    Prod.ext (hpow _ _ (congrArg (fun k ↦ k.1) h)) (hpow _ _ (congrArg (fun k ↦ k.2.1) h))
  have h₂ : t1Data i = t1Data j := congrArg (fun k ↦ k.2.2) h
  rcases i with _ | c | ⟨l, v⟩ | ⟨b, w⟩ | ⟨x, s, w⟩ <;>
    rcases j with _ | c' | ⟨l', v'⟩ | ⟨b', w'⟩ | ⟨x', s', w'⟩ <;>
    simp only [t1Exp, Prod.mk.injEq] at h₁ <;> simp only [t1Data, Prod.mk.injEq] at h₂ <;>
    try omega
  · rfl
  · rw [Fin.ext (by exact_mod_cast h₂.1 : (c : ℕ) = c')]
  · rw [lineVec_injective (hval _ _ h₂.2.1) (hval _ _ h₂.2.2.1) (hval _ _ h₂.2.2.2)]
  · rw [hdiv b b' h₂.2.2.1, hdiv₂ w w' h₂.2.2.2]
  · rw [Fin.ext (by exact_mod_cast (mul_right_inj' hp).mp h₂.1 : (x : ℕ) = x'),
      hdiv₂ w w' h₂.2.1, hdiv s s' h₂.2.2.1]

lemma eq_of_t1Rep_mul_inv_mem {i j : T1Index p} (h : t1Rep i * (t1Rep j)⁻¹ ∈ Γ₂) : i = j := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  have hp₀ : (0 : ℚ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  rcases h with ⟨g, -, hg⟩
  have hgm : (g : Mℤ).map (↑) * borelNF ((p : ℚ) ^ 2) ((p : ℚ) ^ (t1Exp j).1)
      ((p : ℚ) ^ (t1Exp j).2) (t1Data j).1 (t1Data j).2.1 (t1Data j).2.2.1 (t1Data j).2.2.2 =
        borelNF ((p : ℚ) ^ 2) ((p : ℚ) ^ (t1Exp i).1) ((p : ℚ) ^ (t1Exp i).2) (t1Data i).1
          (t1Data i).2.1 (t1Data i).2.2.1 (t1Data i).2.2.2 := by
    have e : spToGL (Fin 2) g * t1Rep j = t1Rep i := by rw [hg, inv_mul_cancel_right]
    have e' : ((spToGL (Fin 2) g * t1Rep j : GL₄) : M₄) = (t1Rep i : M₄) :=
      congrArg (fun y : GL₄ ↦ (y : M₄)) e
    simp only [Units.val_mul, t1Rep] at e'
    rwa [coe_borelNFGL (pow_ne_zero 2 hp) (pow_ne_zero _ hp) (pow_ne_zero _ hp),
      coe_borelNFGL (pow_ne_zero 2 hp) (pow_ne_zero _ hp) (pow_ne_zero _ hp)] at e'
  exact t1Key_injective (borelNF_eq_of_mul_eq (pow_ne_zero 2 hp) g.2 (pow_pos hp₀ _)
    (pow_pos hp₀ _) (pow_pos hp₀ _) (pow_pos hp₀ _) (t1Data_fst_mem i) (t1Data_fst_mem j)
    (t1Data_snd_mem i) (t1Data_snd_mem j) hgm)

variable (α₀ : ℂˣ) (α : Fin 2 → ℂˣ)

/-- **The Satake map on `T_1(p²)`**:
`ω_α(T_1(p²)) = α₀² p⁻¹ ((α_0 + α_1)(1 + α_0 α_1) + (1 - p⁻²) α_0 α_1)`, the right cosets of
`T_1(p²) = Γ diag(1, p, p², p) Γ` being the `p (p + 1)(p² + 1)` Borel normal forms
`SiegelUpperHalfSpace.t1Rep`. -/
lemma satakeMap_T₁ : satakeMap p α₀ α (HeckeCosetModule.single ℂ (heckeCosetDiag p 0 1 0) 1) =
    (α₀ : ℂ) ^ 2 * (p : ℂ)⁻¹ *
      ((α 0 + α 1) * (1 + α 0 * α 1) + (1 - ((p : ℂ) ^ 2)⁻¹) * α 0 * α 1) := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [satakeMap_single_eq_sum α₀ α _ t1Rep t1Rep_mem fun x hx ↦ ?_]
  · have hval (i : T1Index p) : HeckeCoset.borelValue Γ₂ ((satakeCharacter p α₀ α).comp
        (satakeValuation p)) (t1Rep i) = (α₀ : ℂ) ^ 2 *
          ((α 0 : ℂ) * ((p : ℂ) ^ 2)⁻¹) ^ (t1Exp i).1 * ((α 1 : ℂ) * (p : ℂ)⁻¹) ^ (t1Exp i).2 :=
      borelValue_borelNFGL α₀ α _ _ _ _
    simp only [hval, Fintype.sum_sum_type, t1Exp, Finset.sum_const, Finset.card_univ,
      Fintype.card_unit, Fintype.card_fin, Fintype.card_prod, Fintype.card_option,
      ZMod.card_units, ZMod.card, nsmul_eq_mul]
    push_cast [Nat.cast_pred (Fact.out : p.Prime).pos]
    field_simp
    ring1
  · rcases exists_borelNF_of_mem_doubleCoset hx with
      ⟨γ, hγ, d₀, d₁, c, x₀₀, x₀₁, x₁₁, hd₀, hd₁, hc, hc', h₀₀, h₀₀', h₀₁, h₀₁', h₁₁, h₁₁', -, h⟩
    simp only [mul_zero] at h
    have hmem : borelNFGL ((p : ℚ) ^ 2) d₀ d₁ c x₀₀ x₀₁ x₁₁ ∈
        DoubleCoset.doubleCoset (symplecticDiag p 0 1 0 : GL₄) (Γ₂ : Set GL₄) Γ₂ := by
      rw [← h, ← DoubleCoset.doubleCoset_eq_of_mem
        (rep_mem_doubleCoset_symplecticDiag (p := p) 0 1 0)]
      exact mul_mem_doubleCoset hγ hx
    have hmin : MinorsDvd p 1 (borelNFGL ((p : ℚ) ^ 2) d₀ d₁ c x₀₀ x₀₁ x₁₁) :=
      (minorsDvd_symplecticDiag 0 1 0).of_mem_doubleCoset hmem
    have hent : ¬EntriesDvd p 1 (borelNFGL ((p : ℚ) ^ 2) d₀ d₁ c x₀₀ x₀₁ x₁₁) := fun he ↦
      Nat.not_succ_le_zero 0
        (le_of_entriesDvd_symplecticDiag (he.of_mem_doubleCoset (mem_doubleCoset_symm hmem)))
    rcases exists_t1Rep_eq hd₀ hd₁ hc hc' h₀₀ h₀₀' h₀₁ h₀₁' h₁₁ h₁₁' hmin hent with ⟨i, hi⟩
    have hmem' : x * (t1Rep i)⁻¹ ∈ Γ₂ := by
      rw [hi, ← h, mul_inv_rev, mul_inv_cancel_left]
      exact inv_mem hγ
    refine ⟨i, hmem', fun j hj ↦ eq_of_t1Rep_mul_inv_mem ?_⟩
    have e : t1Rep j * (t1Rep i)⁻¹ = (x * (t1Rep j)⁻¹)⁻¹ * (x * (t1Rep i)⁻¹) := by
      group
    rw [e]
    exact mul_mem (inv_mem hj) hmem'

end SiegelUpperHalfSpace
