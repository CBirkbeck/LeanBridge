import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SaitoKurokawaJacobiHecke
import TauCeti.NumberTheory.BinaryQuadraticForm.Content

/-!
# Binary quadratic forms on the sublattices of index `p`

The `p + 1` sublattices of index `p` of `ℤ²` are the `g_ℓ ℤ²` above the lines `ℓ ∈ P¹(𝔽_p)`, with
`g_∞(x, y) = (x, py)` and `g_c(x, y) = (px + cy, y)` for `0 ≤ c < p`. For a binary quadratic form
`Q = [a, b, c]` the forms `Q ∘ g_ℓ` (`TauCeti.BinaryQuadraticForm.lineForm`) have discriminant
`p² disc Q`, and their contents lie between that of `Q` and `p²` times it. The Hecke operators
`T(p)` and `T_1(p²)` of `Sp(4, ℤ)` act on the Fourier coefficients of a Siegel modular form of
degree `2` through the forms `Q ∘ g_ℓ`, `(Q ∘ g_ℓ)/p` and `(Q ∘ g_ℓ)/p²`; the Maass lifts have
coefficients that only depend on the content and the discriminant, so what matters is the number
`ν_i(Q)` of lines with `p^i ∣ Q ∘ g_ℓ` (`TauCeti.BinaryQuadraticForm.lineCount`). For `Q`
primitive at `p`: `ν_1 = 1 + (-Δ/p)`, `Δ = -disc Q`, the number of roots of `Q` on `P¹(𝔽_p)`,
with the Kronecker symbol `ModularForm.negKronecker`; `ν_2 = 1` when `Δ/p²` is again a
discriminant; and `ν_3 = 0`. For `p^a Q`, `ν_i = p + 1` for `i ≤ a` and `ν_{a+i}(p^a Q) = ν_i(Q)`.
These counts were checked by brute force for `p ≤ 7`.

## Main definitions

* `TauCeti.BinaryQuadraticForm.lineForm`: the forms `Q ∘ g_ℓ`.
* `TauCeti.BinaryQuadraticForm.lineCount`: the number `ν_i(Q)` of lines with `p^i ∣ Q ∘ g_ℓ`.

## Main results

* `TauCeti.BinaryQuadraticForm.lineCount_one`: `ν_1 = 1 + (-Δ/p)` for `Q` primitive at `p`.
* `TauCeti.BinaryQuadraticForm.lineCount_two`: `ν_2 = 1` when `Δ/p²` is a discriminant.
* `TauCeti.BinaryQuadraticForm.lineCount_three`: `ν_3 = 0`.
-/

open ModularForm

namespace TauCeti.BinaryQuadraticForm

variable (p : ℕ) (f : BinaryQuadraticForm ℤ)

/-- The form `Q ∘ g_ℓ` of `Q = f` on the sublattice `g_ℓ ℤ²` of index `p` above a line
`ℓ ∈ P¹(𝔽_p)`, `none` standing for `(1 : 0)`, with `g_∞(x, y) = (x, py)`, and `some c` for
`(c : 1)`, with `g_c(x, y) = (px + cy, y)`: `[a, pb, p²c]` and `[p²a, p(b + 2ca), c + bc + ac²]`. -/
def lineForm : Option (Fin p) → BinaryQuadraticForm ℤ
  | none => ⟨f.a, p * f.b, p ^ 2 * f.c⟩
  | some c => ⟨p ^ 2 * f.a, p * (f.b + 2 * c * f.a), f.c + f.b * c + f.a * c ^ 2⟩

/-- The **number of lines** `ℓ ∈ P¹(𝔽_p)` such that `p^i` divides the form `Q ∘ g_ℓ`
(`TauCeti.BinaryQuadraticForm.lineForm`). -/
def lineCount (i : ℕ) : ℕ :=
  (Finset.univ.filter fun ℓ ↦ p ^ i ∣ (f.lineForm p ℓ).content).card

variable {p f}

lemma discrim_lineForm (ℓ : Option (Fin p)) : (f.lineForm p ℓ).discrim = p ^ 2 * f.discrim := by
  rcases ℓ with - | c <;> simp only [lineForm, discrim_def, discrim] <;> ring1

lemma content_dvd_content_lineForm (ℓ : Option (Fin p)) :
    f.content ∣ (f.lineForm p ℓ).content := by
  rw [dvd_content_iff]
  rcases ℓ with - | c
  · exact ⟨f.content_dvd_a, f.content_dvd_b.mul_left _, f.content_dvd_c.mul_left _⟩
  · exact ⟨f.content_dvd_a.mul_left _,
      (f.content_dvd_b.add (f.content_dvd_a.mul_left _)).mul_left _,
        (f.content_dvd_c.add (f.content_dvd_b.mul_right _)).add (f.content_dvd_a.mul_right _)⟩

lemma content_lineForm_dvd (ℓ : Option (Fin p)) :
    (f.lineForm p ℓ).content ∣ p ^ 2 * f.content := by
  have h : p ^ 2 * f.content = (((p : ℤ) ^ 2) • f).content := by
    rw [content_smul', Int.natAbs_pow, Int.natAbs_natCast]
  rw [h, dvd_content_iff]
  have ha : ((f.lineForm p ℓ).content : ℤ) ∣ (f.lineForm p ℓ).a := content_dvd_a _
  have hb : ((f.lineForm p ℓ).content : ℤ) ∣ (f.lineForm p ℓ).b := content_dvd_b _
  have hc : ((f.lineForm p ℓ).content : ℤ) ∣ (f.lineForm p ℓ).c := content_dvd_c _
  rcases ℓ with - | c
  · refine ⟨ha.mul_left _, ?_, hc⟩
    have e : (((p : ℤ) ^ 2) • f).b = p * (f.lineForm p none).b := by
      simp only [lineForm, smul_b']
      ring1
    rw [e]
    exact hb.mul_left _
  · refine ⟨ha, ?_, ?_⟩
    · have e : (((p : ℤ) ^ 2) • f).b =
          p * (f.lineForm p (some c)).b - 2 * c * (f.lineForm p (some c)).a := by
        simp only [lineForm, smul_b']
        ring1
      rw [e]
      exact dvd_sub (hb.mul_left _) (ha.mul_left _)
    · have e : (((p : ℤ) ^ 2) • f).c = p ^ 2 * (f.lineForm p (some c)).c -
          c * p * (f.lineForm p (some c)).b + c ^ 2 * (f.lineForm p (some c)).a := by
        simp only [lineForm, smul_c']
        ring1
      rw [e]
      exact (dvd_sub (hc.mul_left _) (hb.mul_left _)).add (ha.mul_left _)

lemma lineForm_smul (r : ℤ) (ℓ : Option (Fin p)) :
    (r • f).lineForm p ℓ = r • f.lineForm p ℓ := by
  rcases ℓ with - | c <;> ext <;> simp only [lineForm, smul_a', smul_b', smul_c'] <;> ring1

lemma lineCount_zero : f.lineCount p 0 = p + 1 := by
  simp [lineCount]

lemma lineCount_pow_smul_add (hp : p ≠ 0) (a i : ℕ) :
    (((p : ℤ) ^ a) • f).lineCount p (a + i) = f.lineCount p i := by
  simp only [lineCount, lineForm_smul, content_smul', Int.natAbs_pow, Int.natAbs_natCast, pow_add,
    Nat.mul_dvd_mul_iff_left (pow_pos (Nat.pos_of_ne_zero hp) a)]

lemma lineCount_pow_smul_of_le {a i : ℕ} (h : i ≤ a) :
    (((p : ℤ) ^ a) • f).lineCount p i = p + 1 := by
  simp only [lineCount, lineForm_smul, content_smul', Int.natAbs_pow, Int.natAbs_natCast,
    (pow_dvd_pow p h).mul_right, Finset.filter_true, Finset.card_univ, Fintype.card_option,
    Fintype.card_fin]

lemma lineCount_eq (i : ℕ) : f.lineCount p i =
    (if p ^ i ∣ (f.lineForm p none).content then 1 else 0) +
      (Finset.univ.filter fun c : Fin p ↦ p ^ i ∣ (f.lineForm p (some c)).content).card := by
  rw [lineCount, Finset.card_filter, Fintype.sum_option, Finset.card_filter]

/-! ### Forms primitive at `p` -/

lemma dvd_of_pow_succ_dvd_pow_mul (hp : p ≠ 0) (k : ℕ) {x : ℤ}
    (h : (p : ℤ) ^ (k + 1) ∣ (p : ℤ) ^ k * x) : (p : ℤ) ∣ x := by
  rw [pow_succ] at h
  exact (mul_dvd_mul_iff_left (pow_ne_zero k (Nat.cast_ne_zero.mpr hp))).mp h

/-- **No sublattice of index `p` carries a form divisible by `p³`** when `Q` is primitive at `p`. -/
lemma lineCount_three (hp : p.Prime) (hf : ¬p ∣ f.content) : f.lineCount p 3 = 0 := by
  have hp₀ : p ≠ 0 := hp.ne_zero
  refine Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun ℓ _ h ↦ hf ?_)
  rw [dvd_content_iff]
  rw [dvd_content_iff] at h
  push_cast at h
  rcases ℓ with - | c <;> rcases h with ⟨ha, hb, hc⟩ <;> simp only [lineForm] at ha hb hc
  · refine ⟨(dvd_pow_self _ three_ne_zero).trans ha,
      dvd_of_pow_succ_dvd_pow_mul hp₀ 1 ?_, dvd_of_pow_succ_dvd_pow_mul hp₀ 2 hc⟩
    rw [pow_one]
    exact (pow_dvd_pow _ (by norm_num)).trans hb
  · have ha' : (p : ℤ) ∣ f.a := dvd_of_pow_succ_dvd_pow_mul hp₀ 2 ha
    have hb' : (p : ℤ) ∣ f.b + 2 * c * f.a := by
      refine dvd_of_pow_succ_dvd_pow_mul hp₀ 1 ?_
      rw [pow_one]
      exact (pow_dvd_pow _ (by norm_num)).trans hb
    have hb'' : (p : ℤ) ∣ f.b := by
      have e : f.b = f.b + 2 * c * f.a - 2 * c * f.a := by ring1
      rw [e]
      exact dvd_sub hb' (ha'.mul_left _)
    have hc' : (p : ℤ) ∣ f.c + f.b * c + f.a * c ^ 2 := (dvd_pow_self _ three_ne_zero).trans hc
    refine ⟨ha', hb'', ?_⟩
    have e : f.c = f.c + f.b * c + f.a * c ^ 2 - (f.b * c + f.a * c ^ 2) := by ring1
    rw [e]
    exact dvd_sub hc' ((hb''.mul_right _).add (ha'.mul_right _))

lemma dvd_content_lineForm_none_iff : p ∣ (f.lineForm p none).content ↔ (p : ℤ) ∣ f.a := by
  rw [dvd_content_iff]
  exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, dvd_mul_right _ _, (dvd_pow_self _ two_ne_zero).mul_right _⟩⟩

lemma dvd_content_lineForm_some_iff (c : Fin p) :
    p ∣ (f.lineForm p (some c)).content ↔ (p : ℤ) ∣ f.c + f.b * c + f.a * c ^ 2 := by
  rw [dvd_content_iff]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨(dvd_pow_self _ two_ne_zero).mul_right _, dvd_mul_right _ _, h⟩⟩

variable [NeZero p] in
lemma card_filter_fin (P : ZMod p → Prop) [DecidablePred P] :
    (Finset.univ.filter fun c : Fin p ↦ P ((c : ℕ) : ZMod p)).card =
      (Finset.univ.filter P).card :=
  Finset.card_equiv (ZMod.finEquiv p).toEquiv fun c ↦ by simp

variable [Fact p.Prime]

lemma two_ne_zero_zmod (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 :=
  Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])

lemma card_roots_add_ite (hp2 : p ≠ 2) (hf : ¬p ∣ f.content) :
    ((if (p : ℤ) ∣ f.a then 1 else 0) +
      (Finset.univ.filter fun c : Fin p ↦ (p : ℤ) ∣ f.c + f.b * c + f.a * c ^ 2).card : ℤ) =
        1 + legendreSym p f.discrim := by
  have hcast (x : ℤ) : (p : ℤ) ∣ x ↔ (x : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd x p).symm
  have hcard : (Finset.univ.filter fun c : Fin p ↦ (p : ℤ) ∣ f.c + f.b * c + f.a * c ^ 2).card =
      (Finset.univ.filter fun x : ZMod p ↦ (f.c : ZMod p) + f.b * x + f.a * x ^ 2 = 0).card := by
    rw [← card_filter_fin]
    congr 1
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, hcast]
    push_cast
    rfl
  have hD : ((f.discrim : ℤ) : ZMod p) = (f.b : ZMod p) ^ 2 - 4 * f.a * f.c := by
    rw [discrim_def, discrim]
    push_cast
    ring1
  have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
  rw [hcard]
  by_cases ha : (f.a : ZMod p) = 0
  · rw [ite_eq_left ((hcast _).mpr ha)]
    by_cases hb : (f.b : ZMod p) = 0
    · have hc : (f.c : ZMod p) ≠ 0 := fun hc ↦ hf ((dvd_content_iff f p).mpr
        ⟨(hcast _).mpr ha, (hcast _).mpr hb, (hcast _).mpr hc⟩)
      have h0 : (Finset.univ.filter fun x : ZMod p ↦ (f.c : ZMod p) + f.b * x + f.a * x ^ 2 = 0) =
          ∅ := by
        refine Finset.filter_eq_empty_iff.mpr fun x _ ↦ ?_
        rw [ha, hb]
        simpa using hc
      rw [h0, Finset.card_empty,
        (legendreSym.eq_zero_iff p f.discrim).mpr (by rw [hD, ha, hb]; ring1)]
      norm_num
    · have h1 : (Finset.univ.filter fun x : ZMod p ↦ (f.c : ZMod p) + f.b * x + f.a * x ^ 2 = 0) =
          {-(f.c : ZMod p) / f.b} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, ha,
          zero_mul]
        constructor
        · intro h
          field_simp
          linear_combination h
        · rintro rfl
          field_simp
          ring1
      have e : legendreSym p f.discrim = legendreSym p (f.b ^ 2) := by
        simp only [legendreSym]
        congr 1
        push_cast
        rw [hD, ha]
        ring1
      rw [h1, Finset.card_singleton, e, legendreSym.sq_one' p hb]
      norm_num
  · rw [ite_eq_right fun h ↦ ha ((hcast _).mp h)]
    have : NeZero (2 : ZMod p) := ⟨h2⟩
    have hsq :
        (Finset.univ.filter fun x : ZMod p ↦ (f.c : ZMod p) + f.b * x + f.a * x ^ 2 = 0).card =
          (Finset.univ.filter fun y : ZMod p ↦ y ^ 2 = ((f.discrim : ℤ) : ZMod p)).card := by
      refine Finset.card_nbij' (fun x ↦ 2 * f.a * x + f.b) (fun y ↦ (y - f.b) / (2 * f.a))
        (fun x hx ↦ ?_) (fun y hy ↦ ?_) (fun x _ ↦ ?_) fun y _ ↦ ?_
      · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx ⊢
        have h : (f.b : ZMod p) ^ 2 - 4 * f.a * f.c = (2 * f.a * x + f.b) ^ 2 :=
          (quadratic_eq_zero_iff_discrim_eq_sq ha x).mp (by linear_combination hx)
        rw [hD, h]
      · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy ⊢
        have h : (f.a : ZMod p) * ((y - f.b) / (2 * f.a) * ((y - f.b) / (2 * f.a))) +
            f.b * ((y - f.b) / (2 * f.a)) + f.c = 0 :=
          (quadratic_eq_zero_iff_discrim_eq_sq ha _).mpr (by
            rw [discrim, ← hD, ← hy]
            field_simp
            ring1)
        linear_combination h
      · field_simp
        ring1
      · field_simp
        ring1
    rw [hsq, ← Set.toFinset_ofPred, legendreSym.card_sqrts p hp2]
    ring1

lemma two_dvd_iff_four_mul_eq_zero (x : ℤ) : (2 : ℤ) ∣ x ↔ 4 * (x : ZMod 8) = 0 := by
  have e : (4 : ZMod 8) * (x : ZMod 8) = ((4 * x : ℤ) : ZMod 8) := by
    push_cast
    ring1
  rw [e, ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  omega

lemma lineCount_count_mod_eight : ∀ a b c : ZMod 8, ¬(4 * a = 0 ∧ 4 * b = 0 ∧ 4 * c = 0) →
    ((if 4 * a = 0 then 1 else 0) + ((if 4 * c = 0 then 1 else 0) +
      (if 4 * (c + b + a) = 0 then 1 else 0)) : ℤ) = 1 + ZMod.χ₈ (-(b ^ 2 - 4 * a * c)) := by
  decide

/-- **The roots of `Q` on `P¹(𝔽_p)`**: for `Q` primitive at `p`, the number of lines `ℓ` with
`p ∣ Q ∘ g_ℓ` is `1 + (-Δ/p)`, where `Δ = -disc Q` and `(-Δ/p)` is the Kronecker symbol
`ModularForm.negKronecker`. -/
lemma lineCount_one (hf : ¬p ∣ f.content) :
    (f.lineCount p 1 : ℤ) = 1 + negKronecker p (-f.discrim) := by
  rw [lineCount_eq, pow_one]
  simp only [dvd_content_lineForm_none_iff, dvd_content_lineForm_some_iff]
  push_cast
  by_cases hp2 : p = 2
  · subst hp2
    have hprim : ¬(4 * (f.a : ZMod 8) = 0 ∧ 4 * (f.b : ZMod 8) = 0 ∧ 4 * (f.c : ZMod 8) = 0) := by
      rw [← two_dvd_iff_four_mul_eq_zero, ← two_dvd_iff_four_mul_eq_zero,
        ← two_dvd_iff_four_mul_eq_zero]
      exact fun h ↦ hf ((dvd_content_iff f 2).mpr (by exact_mod_cast h))
    rw [negKronecker, ite_eq_left rfl, Finset.card_filter, Fin.sum_univ_two, discrim_def, discrim]
    simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, mul_zero, mul_one,
      add_zero, zero_pow two_ne_zero, one_pow]
    push_cast
    simp only [two_dvd_iff_four_mul_eq_zero]
    push_cast
    exact lineCount_count_mod_eight f.a f.b f.c hprim
  · rw [negKronecker, ite_eq_right hp2, neg_neg]
    exact card_roots_add_ite hp2 hf

lemma pow_two_dvd_mul_iff (x : ℤ) : (p : ℤ) ^ 2 ∣ p * x ↔ (p : ℤ) ∣ x := by
  rw [pow_two]
  exact mul_dvd_mul_iff_left (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

lemma pow_two_dvd_content_lineForm_none_iff :
    p ^ 2 ∣ (f.lineForm p none).content ↔ (p : ℤ) ^ 2 ∣ f.a ∧ (p : ℤ) ∣ f.b := by
  rw [dvd_content_iff]
  simp only [lineForm]
  push_cast
  simp only [pow_two_dvd_mul_iff, dvd_mul_right, and_true]

lemma pow_two_dvd_content_lineForm_some_iff (c : Fin p) :
    p ^ 2 ∣ (f.lineForm p (some c)).content ↔
      (p : ℤ) ∣ f.b + 2 * c * f.a ∧ (p : ℤ) ^ 2 ∣ f.c + f.b * c + f.a * c ^ 2 := by
  rw [dvd_content_iff]
  simp only [lineForm]
  push_cast
  simp only [pow_two_dvd_mul_iff, dvd_mul_right, true_and]

lemma lineCount_count_mod_four : ∀ a s c : ZMod 4, ¬(2 * a = 0 ∧ 2 * c = 0) →
    (a * c - s ^ 2 = 0 ∨ a * c - s ^ 2 = 3) →
      (if a = 0 then 1 else 0) + ((if c = 0 then 1 else 0) + if c + 2 * s + a = 0 then 1 else 0) =
        1 := by
  decide

lemma isCoprime_pow_two_of_not_dvd (hp2 : p ≠ 2) {x : ℤ} (hx : ¬(p : ℤ) ∣ x) :
    IsCoprime ((p : ℤ) ^ 2) (4 * x) := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  refine IsCoprime.pow_left (hp.coprime_iff_not_dvd.mpr fun h ↦ ?_)
  rcases hp.dvd_or_dvd h with h | h
  · have h' : p ∣ 2 ^ 2 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      ((Nat.prime_iff.mp Fact.out).dvd_of_dvd_pow h'))
  · exact hx h

/-- **The form `Q ∘ g_ℓ` divisible by `p²`**: if `Q` is primitive at `p` and its discriminant
`-Δ` is `p²` times a discriminant, then exactly one line `ℓ` has `p² ∣ Q ∘ g_ℓ`. -/
lemma lineCount_two (hf : ¬p ∣ f.content) (hD : (p : ℤ) ^ 2 ∣ f.discrim)
    (h4 : -f.discrim / p ^ 2 % 4 = 0 ∨ -f.discrim / p ^ 2 % 4 = 3) : f.lineCount p 2 = 1 := by
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have hdisc : f.discrim = f.b ^ 2 - 4 * f.a * f.c := by
    rw [discrim_def, discrim]
  simp only [lineCount_eq, pow_two_dvd_content_lineForm_none_iff,
    pow_two_dvd_content_lineForm_some_iff]
  by_cases hp2 : p = 2
  · subst hp2
    push_cast at hD h4 ⊢
    have hb : (2 : ℤ) ∣ f.b := Int.prime_two.dvd_of_dvd_pow (n := 2) (by
      have e : f.b ^ 2 = f.discrim + 4 * f.a * f.c := by rw [hdisc]; ring1
      rw [e]
      exact (dvd_trans (by norm_num) hD).add
        (((by norm_num : (2 : ℤ) ∣ 4).mul_right f.a).mul_right f.c))
    rcases hb with ⟨s, hs⟩
    have e : -f.discrim = 4 * (f.a * f.c - s ^ 2) := by
      rw [hdisc, hs]
      ring1
    rw [e, Int.mul_ediv_cancel_left _ (by norm_num)] at h4
    have h4' : ((f.a : ZMod 4) * f.c - (s : ZMod 4) ^ 2 = 0 ∨
        (f.a : ZMod 4) * f.c - (s : ZMod 4) ^ 2 = 3) := by
      have hx : ((f.a * f.c - s ^ 2 : ℤ) : ZMod 4) = (((f.a * f.c - s ^ 2) % 4 : ℤ) : ZMod 4) :=
        (ZMod.intCast_mod _ 4).symm
      push_cast at hx
      rcases h4 with h | h <;> rw [h] at hx
      · exact Or.inl hx
      · exact Or.inr hx
    have h2 (x : ℤ) : (2 : ℤ) ∣ x ↔ 2 * (x : ZMod 4) = 0 := by
      have e₂ : (2 : ZMod 4) * (x : ZMod 4) = ((2 * x : ℤ) : ZMod 4) := by
        push_cast
        ring1
      rw [e₂, ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      omega
    have hprim : ¬(2 * (f.a : ZMod 4) = 0 ∧ 2 * (f.c : ZMod 4) = 0) := by
      rw [← h2, ← h2]
      exact fun h ↦ hf ((dvd_content_iff f 2).mpr ⟨by exact_mod_cast h.1,
        by exact_mod_cast (⟨s, hs⟩ : (2 : ℤ) ∣ f.b), by exact_mod_cast h.2⟩)
    have h4z (x : ℤ) : (4 : ℤ) ∣ x ↔ (x : ZMod 4) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd x 4).symm
    have hc₁ : ((4 : ℤ) ∣ f.a ∧ (2 : ℤ) ∣ f.b) ↔ (f.a : ZMod 4) = 0 := by
      rw [← h4z]
      exact ⟨fun h ↦ h.1, fun h ↦ ⟨h, ⟨s, hs⟩⟩⟩
    have hc₂ (x : Fin 2) : ((2 : ℤ) ∣ f.b + 2 * x * f.a ∧ (4 : ℤ) ∣ f.c + f.b * x + f.a * x ^ 2) ↔
        (f.c : ZMod 4) + 2 * s * ((x : ℕ) : ZMod 4) + f.a * ((x : ℕ) : ZMod 4) ^ 2 = 0 := by
      rw [hs]
      have e₃ : ((f.c + 2 * s * x + f.a * x ^ 2 : ℤ) : ZMod 4) =
          (f.c : ZMod 4) + 2 * s * ((x : ℕ) : ZMod 4) + f.a * ((x : ℕ) : ZMod 4) ^ 2 := by
        push_cast
        rfl
      rw [← e₃, ← h4z]
      refine ⟨fun h ↦ ?_, fun h ↦ ⟨⟨s + x * f.a, by ring1⟩, ?_⟩⟩
      · convert h.2 using 1
      · convert h using 1
    simp only [hc₁, hc₂]
    rw [Finset.card_filter, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one, mul_zero, mul_one,
      add_zero, zero_pow two_ne_zero, one_pow]
    exact lineCount_count_mod_four _ _ _ hprim h4'
  · have hpD : (p : ℤ) ∣ f.discrim := (dvd_pow_self _ two_ne_zero).trans hD
    by_cases ha : (p : ℤ) ∣ f.a
    · have hb : (p : ℤ) ∣ f.b := hp.dvd_of_dvd_pow (n := 2) (by
        have e : f.b ^ 2 = f.discrim + 4 * f.a * f.c := by rw [hdisc]; ring1
        rw [e]
        exact hpD.add ((ha.mul_left 4).mul_right _))
      have hc : ¬(p : ℤ) ∣ f.c := fun hc ↦ hf ((dvd_content_iff f p).mpr ⟨ha, hb, hc⟩)
      have ha2 : (p : ℤ) ^ 2 ∣ f.a := by
        refine (isCoprime_pow_two_of_not_dvd hp2 hc).dvd_of_dvd_mul_right ?_
        have e : f.a * (4 * f.c) = f.b ^ 2 - f.discrim := by rw [hdisc]; ring1
        rw [e]
        exact dvd_sub (pow_dvd_pow_of_dvd hb 2) hD
      rw [ite_eq_left ⟨ha2, hb⟩, Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr
        fun c _ h ↦ hc ?_)]
      have e : f.c = f.c + f.b * c + f.a * c ^ 2 - (f.b * c + f.a * c ^ 2) := by ring1
      rw [e]
      exact dvd_sub ((dvd_pow_self _ two_ne_zero).trans h.2) ((hb.mul_right _).add (ha.mul_right _))
    · rw [ite_eq_right fun h ↦ ha ((dvd_pow_self _ two_ne_zero).trans h.1), zero_add]
      have hcast (x : ℤ) : (p : ℤ) ∣ x ↔ (x : ZMod p) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd x p).symm
      have ha' : (f.a : ZMod p) ≠ 0 := fun h ↦ ha ((hcast _).mpr h)
      have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_zmod hp2
      have hco : IsCoprime ((p : ℤ) ^ 2) (4 * f.a) := isCoprime_pow_two_of_not_dvd hp2 ha
      have hfilter : (Finset.univ.filter fun c : Fin p ↦ (p : ℤ) ∣ f.b + 2 * c * f.a ∧
          (p : ℤ) ^ 2 ∣ f.c + f.b * c + f.a * c ^ 2) =
            Finset.univ.filter fun c : Fin p ↦
              (f.b : ZMod p) + 2 * ((c : ℕ) : ZMod p) * f.a = 0 := by
        refine Finset.filter_congr fun c _ ↦ ?_
        have hQ : (p : ℤ) ∣ f.b + 2 * c * f.a → (p : ℤ) ^ 2 ∣ f.c + f.b * c + f.a * c ^ 2 :=
          fun h ↦ hco.dvd_of_dvd_mul_right (by
            have e : (f.c + f.b * c + f.a * c ^ 2) * (4 * f.a) =
                (f.b + 2 * c * f.a) ^ 2 - f.discrim := by
              rw [hdisc]
              ring1
            rw [e]
            exact dvd_sub (pow_dvd_pow_of_dvd h 2) hD)
        rw [and_iff_left_of_imp hQ, hcast]
        push_cast
        rfl
      rw [hfilter, card_filter_fin (fun x : ZMod p ↦ (f.b : ZMod p) + 2 * x * f.a = 0),
        Finset.card_eq_one]
      refine ⟨-(f.b : ZMod p) / (2 * f.a), Finset.ext fun x ↦ ?_⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        field_simp
        linear_combination h
      · rintro rfl
        field_simp
        ring1

end TauCeti.BinaryQuadraticForm
