import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import TauCeti.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import TauCeti.NumberTheory.ModularForms.JacobiTheta.GaussSum

/-!
# Quadratic Gauss sums with an odd modulus

For a positive integer `a` and an integer `β`, the quadratic Gauss sum is
`G(β, a) = ∑_{m mod a} e(β m² / a)`, where `e(x) = e^{2πix}`. For odd `a` and `β` prime to `a`,
`G(β, a)` is the Jacobi symbol `(β / a)` times `G(1, a)`, and Gauss's evaluation gives
`G(1, a) = ε_a √a`, with `ε_a` equal to `1` or `i` as `a ≡ 1` or `3` modulo `4`. The proof is an
induction on `a` from three facts: the prime case, `G(β, a₁ a₂) = G(β a₂, a₁) G(β a₁, a₂)` for
coprime `a₁, a₂`, and `G(β, p² a) = p G(β, a)` for an odd prime `p ∤ β`.

The last two facts are the rank-one cases of `Matrix.sum_stdAddChar_dotProduct_mulVec_mul` and
`Matrix.IsSymm.sum_stdAddChar_dotProduct_mulVec_of_eq_sq_mul` in
`TauCeti/NumberTheory/QuadraticForm/GaussSum.lean`, which is on Tau Ceti's main but not at its pin
and evaluates only the even rank. They should be replaced by those after the bump.

## Main definitions

* `ZMod.quadraticGaussSum`: the sum `G(β, a)`.

## Main results

* `ZMod.quadraticGaussSum_mul_of_coprime`: the factorisation for a coprime modulus.
* `ZMod.quadraticGaussSum_prime_mul_prime_mul`: the reduction by the square of a prime.
* `ZMod.quadraticGaussSum_prime`: `G(β, p) = (β / p) G(1, p)` for an odd prime `p ∤ β`.
* `ZMod.quadraticGaussSum_eq_jacobiSym_mul`: `G(β, a) = (β / a) G(1, a)` for odd `a`.
* `ZMod.quadraticGaussSum_one_of_mod_four_eq_one`: Gauss's evaluation of `G(1, a)` for `a ≡ 1`.
* `ZMod.quadraticGaussSum_one_of_mod_four_eq_three`: Gauss's evaluation of `G(1, a)` for `a ≡ 3`.
-/

open Complex

open scoped Real NumberTheorySymbols

open jacobiSym (legendreSym.to_jacobiSym)

namespace ZMod

variable (β : ℤ) (a : ℕ) [NeZero a] {M : Type*} [AddCommMonoid M]

/-- The **quadratic Gauss sum** `G(β, a) = ∑_{m mod a} e(β m² / a)`. -/
noncomputable def quadraticGaussSum : ℂ :=
  ∑ m : ZMod a, stdAddChar ((β : ZMod a) * m ^ 2)

lemma sum_range_natCast_eq (F : ZMod a → M) :
    ∑ r ∈ Finset.range a, F (r : ZMod a) = ∑ x : ZMod a, F x := by
  refine Finset.sum_bij (fun r _ ↦ (r : ZMod a)) (fun _ _ ↦ Finset.mem_univ _) ?_ ?_ fun _ _ ↦ rfl
  · intro r hr s hs h
    have h1 : (r : ZMod a).val = (s : ZMod a).val := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt (Finset.mem_range.mp hr),
      ZMod.val_natCast_of_lt (Finset.mem_range.mp hs)] at h1
  · exact fun x _ ↦ ⟨x.val, Finset.mem_range.mpr (ZMod.val_lt x), ZMod.natCast_zmod_val x⟩

variable {a} in
lemma sum_Icc_one_natCast (F : ZMod a → M) : ∑ n ∈ Finset.Icc 1 a, F n = ∑ x, F x := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel,
    ← Equiv.sum_comp (Equiv.addLeft 1) F, ← sum_range_natCast_eq]
  exact Finset.sum_congr rfl fun k _ ↦ by rw [Nat.cast_add, Nat.cast_one, Equiv.coe_addLeft]

variable {a} in
lemma sum_eq_sum_units {F : ZMod a → M} (hF : ∀ x, ¬IsUnit x → F x = 0) :
    ∑ x, F x = ∑ u : (ZMod a)ˣ, F u := by
  have hsub :
      ∑ x ∈ Finset.univ.map ⟨((↑) : (ZMod a)ˣ → ZMod a), Units.val_injective⟩, F x = ∑ x, F x :=
    Finset.sum_subset (Finset.subset_univ _) fun x _ hx ↦ hF x fun hu ↦ hx <|
      Finset.mem_map.mpr ⟨hu.unit, Finset.mem_univ _, hu.unit_spec⟩
  rw [← hsub, Finset.sum_map]
  rfl

variable {a} in
lemma stdAddChar_natCast_div_mul {d : ℕ} [NeZero d] (hd : d ∣ a) (x : ZMod a) :
    stdAddChar (((a / d : ℕ) : ZMod a) * x) = stdAddChar (cast x : ZMod d) := by
  have had : ((a / d : ℕ) : ℂ) * d = a := by exact_mod_cast Nat.div_mul_cancel hd
  have had0 : ((a / d : ℕ) : ℂ) ≠ 0 := fun h ↦ NeZero.ne a <| by
    rw [h, zero_mul] at had
    exact_mod_cast had.symm
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  rw [← natCast_zmod_val x, cast_natCast hd, ← Nat.cast_mul, stdAddChar_apply, stdAddChar_apply,
    toCircle_natCast, toCircle_natCast, Nat.cast_mul, ← had]
  congr 1
  field_simp

lemma stdAddChar_natCast_mul (a₁ a₂ : ℕ) [NeZero a₁] [NeZero (a₁ * a₂)] (j : ℤ) :
    stdAddChar (((a₂ : ℤ) * j : ℤ) : ZMod (a₁ * a₂)) = stdAddChar ((j : ℤ) : ZMod a₁) := by
  have h : stdAddChar (((a₁ * a₂ / a₁ : ℕ) : ZMod (a₁ * a₂)) * (j : ZMod (a₁ * a₂))) =
      stdAddChar (cast (j : ZMod (a₁ * a₂)) : ZMod a₁) :=
    stdAddChar_natCast_div_mul (dvd_mul_right a₁ a₂) _
  rwa [Nat.mul_div_cancel_left a₂ (NeZero.pos a₁), cast_intCast (dvd_mul_right a₁ a₂),
    ← Int.cast_natCast, ← Int.cast_mul] at h

lemma stdAddChar_natCast_mul' (a₁ a₂ : ℕ) [NeZero a₂] [NeZero (a₁ * a₂)] (j : ℤ) :
    stdAddChar (((a₁ : ℤ) * j : ℤ) : ZMod (a₁ * a₂)) = stdAddChar ((j : ℤ) : ZMod a₂) := by
  have h : stdAddChar (((a₁ * a₂ / a₂ : ℕ) : ZMod (a₁ * a₂)) * (j : ZMod (a₁ * a₂))) =
      stdAddChar (cast (j : ZMod (a₁ * a₂)) : ZMod a₂) :=
    stdAddChar_natCast_div_mul (dvd_mul_left a₂ a₁) _
  rwa [Nat.mul_div_cancel a₁ (NeZero.pos a₂), cast_intCast (dvd_mul_left a₂ a₁),
    ← Int.cast_natCast, ← Int.cast_mul] at h

variable (a₁ a₂ : ℕ) [NeZero a₁] [NeZero a₂] [NeZero (a₁ * a₂)]

private lemma bijective_add_mul (h : a₁.Coprime a₂) : Function.Bijective fun p : ZMod a₁ × ZMod a₂ ↦
    ((a₂ * p.1.val + a₁ * p.2.val : ℕ) : ZMod (a₁ * a₂)) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, by simp⟩
  rintro ⟨u, v⟩ ⟨u', v'⟩ huv
  have h1 : a₂ * u.val + a₁ * v.val ≡ a₂ * u'.val + a₁ * v'.val [MOD a₁ * a₂] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp huv
  have h2 : a₂ * u.val ≡ a₂ * u'.val [MOD a₁] := by
    have h3 : a₂ * u.val + a₁ * v.val ≡ a₂ * u'.val + a₁ * v'.val [MOD a₁] :=
      h1.of_mul_right a₂
    simpa using h3
  have h4 : a₁ * v.val ≡ a₁ * v'.val [MOD a₂] := by
    have h3 : a₂ * u.val + a₁ * v.val ≡ a₂ * u'.val + a₁ * v'.val [MOD a₂] :=
      h1.of_mul_left a₁
    simpa using h3
  have h5 : u.val ≡ u'.val [MOD a₁] := h2.cancel_left_of_coprime (by
    rw [Nat.gcd_comm]; exact h.symm)
  have h6 : v.val ≡ v'.val [MOD a₂] := h4.cancel_left_of_coprime (by
    rw [Nat.gcd_comm]; exact h)
  have h7 : u = u' := ZMod.val_injective a₁ (h5.eq_of_lt_of_lt (ZMod.val_lt u) (ZMod.val_lt u'))
  have h8 : v = v' := ZMod.val_injective a₂ (h6.eq_of_lt_of_lt (ZMod.val_lt v) (ZMod.val_lt v'))
  rw [h7, h8]

/-- **The factorisation of a quadratic Gauss sum**: `G(β, a₁ a₂) = G(β a₂, a₁) G(β a₁, a₂)` for
coprime `a₁, a₂`. -/
lemma quadraticGaussSum_mul_of_coprime (h : a₁.Coprime a₂) : quadraticGaussSum β (a₁ * a₂) =
    quadraticGaussSum (β * a₂) a₁ * quadraticGaussSum (β * a₁) a₂ := by
  rw [quadraticGaussSum, ← (bijective_add_mul a₁ a₂ h).sum_comp, Fintype.sum_prod_type,
    quadraticGaussSum, quadraticGaussSum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun u _ ↦ Finset.sum_congr rfl fun v _ ↦ ?_
  have h0 : ((a₁ * a₂ : ℕ) : ZMod (a₁ * a₂)) = 0 := ZMod.natCast_self _
  have h1 : (β : ZMod (a₁ * a₂)) * ((a₂ * u.val + a₁ * v.val : ℕ) : ZMod (a₁ * a₂)) ^ 2 =
      (((a₂ : ℤ) * (β * a₂ * u.val ^ 2) : ℤ) : ZMod (a₁ * a₂)) +
        (((a₁ : ℤ) * (β * a₁ * v.val ^ 2) : ℤ) : ZMod (a₁ * a₂)) := by
    push_cast at h0 ⊢
    linear_combination (2 * (β : ZMod (a₁ * a₂)) * u.val * v.val) * h0
  have h2 : ((β * a₂ * u.val ^ 2 : ℤ) : ZMod a₁) = ((β * a₂ : ℤ) : ZMod a₁) * u ^ 2 := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  have h3 : ((β * a₁ * v.val ^ 2 : ℤ) : ZMod a₂) = ((β * a₁ : ℤ) : ZMod a₂) * v ^ 2 := by
    push_cast
    rw [ZMod.natCast_zmod_val]
  rw [h1, AddChar.map_add_eq_mul, stdAddChar_natCast_mul, stdAddChar_natCast_mul', h2, h3]

variable (p : ℕ) [Fact p.Prime]

private lemma bijective_add_prime_mul : Function.Bijective fun x : ZMod (p * a) × ZMod p ↦
    ((x.1.val + (p * a) * x.2.val : ℕ) : ZMod (p * (p * a))) := by
  refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, by simp [mul_comm]⟩
  rintro ⟨m, t⟩ ⟨m', t'⟩ hmt
  have h1 : m.val + (p * a) * t.val ≡ m'.val + (p * a) * t'.val [MOD p * (p * a)] :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mp hmt
  have h2 : m.val + (p * a) * t.val ≡ m'.val + (p * a) * t'.val [MOD p * a] := h1.of_mul_left p
  have h3 : m.val ≡ m'.val [MOD p * a] := by
    simpa using h2
  have h4 : m = m' := ZMod.val_injective _ (h3.eq_of_lt_of_lt (ZMod.val_lt m) (ZMod.val_lt m'))
  rw [h4] at h1
  have h5 : (p * a) * t.val ≡ (p * a) * t'.val [MOD (p * a) * p] := by
    rw [mul_comm (p * a) p]
    exact h1.add_left_cancel' _
  have h6 : t.val ≡ t'.val [MOD p] := h5.mul_left_cancel' (NeZero.ne (p * a))
  have h7 : t = t' := ZMod.val_injective _ (h6.eq_of_lt_of_lt (ZMod.val_lt t) (ZMod.val_lt t'))
  rw [h4, h7]

/-- **The reduction of a quadratic Gauss sum by the square of a prime**: `G(β, p² a) = p G(β, a)`
for an odd prime `p` not dividing `β`. -/
lemma quadraticGaussSum_prime_mul_prime_mul [NeZero (p * a)] [NeZero (p * (p * a))] (hp : p ≠ 2)
    (hβ : (β : ZMod p) ≠ 0) : quadraticGaussSum β (p * (p * a)) = p * quadraticGaussSum β a := by
  have hψ : (stdAddChar (N := p)).IsPrimitive := isPrimitive_stdAddChar p
  have h2 : (2 : ZMod p) ≠ 0 := by
    have h3 : p.Prime := Fact.out
    intro h0
    have h4 : (p : ℕ) ∣ 2 := by
      have h5 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
      exact (ZMod.natCast_eq_zero_iff 2 p).mp h5
    exact hp ((Nat.prime_dvd_prime_iff_eq h3 Nat.prime_two).mp h4)
  have hterm : ∀ (m : ZMod (p * a)) (t : ZMod p), stdAddChar ((β : ZMod (p * (p * a))) *
      ((m.val + (p * a) * t.val : ℕ) : ZMod (p * (p * a))) ^ 2) =
        stdAddChar ((β * m.val ^ 2 : ℤ) : ZMod (p * (p * a))) *
          stdAddChar (t * ((2 * β * m.val : ℤ) : ZMod p)) := fun m t ↦ by
    have h0 : ((p * (p * a) : ℕ) : ZMod (p * (p * a))) = 0 := ZMod.natCast_self _
    have h1 : (β : ZMod (p * (p * a))) *
        ((m.val + (p * a) * t.val : ℕ) : ZMod (p * (p * a))) ^ 2 =
          ((β * m.val ^ 2 : ℤ) : ZMod (p * (p * a))) +
            ((((p * a : ℕ) : ℤ) * (2 * β * m.val * t.val) : ℤ) : ZMod (p * (p * a))) := by
      push_cast at h0 ⊢
      linear_combination ((β : ZMod (p * (p * a))) * a * t.val ^ 2) * h0
    rw [h1, AddChar.map_add_eq_mul, stdAddChar_natCast_mul]
    congr 2
    push_cast
    rw [ZMod.natCast_zmod_val]
    ring1
  have hinner : ∀ m : ZMod (p * a), ∑ t : ZMod p,
      stdAddChar ((β * m.val ^ 2 : ℤ) : ZMod (p * (p * a))) *
        stdAddChar (t * ((2 * β * m.val : ℤ) : ZMod p)) =
          if ((m.val : ℕ) : ZMod p) = 0 then
            (p : ℂ) * stdAddChar ((β * m.val ^ 2 : ℤ) : ZMod (p * (p * a))) else 0 := fun m ↦ by
    have h3 : ((2 * β * m.val : ℤ) : ZMod p) = 0 ↔ ((m.val : ℕ) : ZMod p) = 0 := by
      push_cast
      rw [mul_assoc, mul_eq_zero, mul_eq_zero]
      simp [h2, hβ]
    rw [← Finset.mul_sum, AddChar.sum_mulShift _ hψ, ZMod.card]
    simp only [h3]
    split_ifs
    · ring1
    · ring1
  rw [quadraticGaussSum, ← (bijective_add_prime_mul a p).sum_comp, Fintype.sum_prod_type]
  simp only [hterm, hinner]
  rw [quadraticGaussSum, Finset.mul_sum, ← Finset.sum_filter]
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hv : ∀ m₁ : ZMod a, ((p * m₁.val : ℕ) : ZMod (p * a)).val = p * m₁.val := fun m₁ ↦
    ZMod.val_natCast_of_lt (Nat.mul_lt_mul_of_pos_left (ZMod.val_lt m₁) hp0)
  refine (Finset.sum_nbij (fun m₁ : ZMod a ↦ ((p * m₁.val : ℕ) : ZMod (p * a))) ?_ ?_ ?_ ?_).symm
  · intro m₁ _
    simp only [Finset.mem_filter]
    rw [hv]
    push_cast
    simp
  · intro x _ y _ hxy
    have h3 : ((p * x.val : ℕ) : ZMod (p * a)).val = ((p * y.val : ℕ) : ZMod (p * a)).val :=
      congrArg ZMod.val hxy
    rw [hv, hv] at h3
    exact ZMod.val_injective _ (Nat.eq_of_mul_eq_mul_left hp0 h3)
  · intro m hm
    have hm' : ((m.val : ℕ) : ZMod p) = 0 := (Finset.mem_filter.mp hm).2
    rcases (ZMod.natCast_eq_zero_iff _ _).mp hm' with ⟨q, hq⟩
    have hqa : q < a := by
      have h3 : p * q < p * a := hq ▸ ZMod.val_lt m
      exact Nat.lt_of_mul_lt_mul_left h3
    refine ⟨(q : ZMod a), Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
    simp only [ZMod.val_natCast_of_lt hqa]
    rw [← hq, ZMod.natCast_zmod_val]
  · intro m₁ _
    rw [hv]
    congr 1
    have h3 : ((β * ((p * m₁.val : ℕ) : ℤ) ^ 2 : ℤ) : ZMod (p * (p * a))) =
        (((p : ℤ) * ((p : ℤ) * (β * m₁.val ^ 2)) : ℤ) : ZMod (p * (p * a))) := by
      congr 1
      push_cast
      ring1
    have h4 : ((β * m₁.val ^ 2 : ℤ) : ZMod a) = (β : ZMod a) * m₁ ^ 2 := by
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [h3, stdAddChar_natCast_mul', stdAddChar_natCast_mul', h4]

/-- **A quadratic Gauss sum modulo an odd prime**: `G(β, p) = (β / p) G(1, p)` for `p ∤ β`. -/
lemma quadraticGaussSum_prime (hp : p ≠ 2) (hβ : (β : ZMod p) ≠ 0) :
    quadraticGaussSum β p = J(β | p) * quadraticGaussSum 1 p := by
  have hF : ringChar (ZMod p) ≠ 2 := by
    rwa [ZMod.ringChar_zmod_n]
  rw [← legendreSym.to_jacobiSym, legendreSym]
  simp only [quadraticGaussSum, Int.cast_one, one_mul]
  exact TauCeti.sum_addChar_mul_sq hF (isPrimitive_stdAddChar p) hβ

private lemma aux_eq_jacobiSym_mul (n : ℕ) : ∀ (a : ℕ) [NeZero a], a ≤ n → Odd a → ∀ β : ℤ,
    IsCoprime β a → quadraticGaussSum β a = J(β | a) * quadraticGaussSum 1 a := by
  induction n with
  | zero =>
    intro a _ ha
    exact absurd (Nat.le_zero.mp ha) (NeZero.ne a)
  | succ n ih =>
    intro a _ ha hodd β hβ
    rcases eq_or_ne a 1 with rfl | ha1
    · have h1 : ∀ m : ZMod 1, (β : ZMod 1) * m ^ 2 = ((1 : ℤ) : ZMod 1) * m ^ 2 := fun m ↦
        Subsingleton.elim _ _
      simp [quadraticGaussSum, h1]
    rcases Nat.exists_prime_and_dvd ha1 with ⟨p, hp, a₀, rfl⟩
    have hfact : Fact p.Prime := ⟨hp⟩
    have ha₀ : NeZero a₀ := ⟨right_ne_zero_of_mul (NeZero.ne (p * a₀))⟩
    have hodd₀ : Odd a₀ := (Nat.odd_mul.mp hodd).2
    have hp2 : p ≠ 2 := fun h ↦ by
      have h1 : Odd p := (Nat.odd_mul.mp hodd).1
      rw [h] at h1
      exact absurd h1 (by decide)
    have hlt : a₀ ≤ n := by
      have h1 : 2 * a₀ ≤ p * a₀ := Nat.mul_le_mul_right _ hp.two_le
      have h2 : 0 < a₀ := NeZero.pos a₀
      omega
    have hβp : (β : ZMod p) ≠ 0 := fun h0 ↦ by
      have h1 : (p : ℤ) ∣ β := (ZMod.intCast_zmod_eq_zero_iff_dvd β p).mp h0
      have h2 : (p : ℤ) ∣ ((p * a₀ : ℕ) : ℤ) := by
        push_cast
        exact dvd_mul_right _ _
      exact (Nat.prime_iff_prime_int.mp hp).not_isUnit (hβ.isUnit_of_dvd' h1 h2)
    have hβ' : IsCoprime β ((p : ℤ) * (a₀ : ℤ)) := by
      rw [← Nat.cast_mul]
      exact hβ
    have hβa₀ : IsCoprime β a₀ := hβ'.of_mul_right_right
    have hβp' : IsCoprime β p := hβ'.of_mul_right_left
    have h1p : ((1 : ℤ) : ZMod p) ≠ 0 := by
      simp
    by_cases hd : p ∣ a₀
    · rcases hd with ⟨a', rfl⟩
      have ha' : NeZero a' := ⟨right_ne_zero_of_mul (NeZero.ne (p * a'))⟩
      have hlt' : a' ≤ n := by
        have h1 : 2 * a' ≤ p * a' := Nat.mul_le_mul_right _ hp.two_le
        have h2 : 0 < a' := NeZero.pos a'
        omega
      have hodd' : Odd a' := (Nat.odd_mul.mp hodd₀).2
      have hβa' : IsCoprime β a' := by
        have h1 : IsCoprime β ((p : ℤ) * (a' : ℤ)) := by
          rw [← Nat.cast_mul]
          exact hβa₀
        exact h1.of_mul_right_right
      have hsq : J(β | p) * J(β | p) = 1 := by
        have h1 : J(β | p) ^ 2 = 1 := jacobiSym.sq_one (Int.isCoprime_iff_gcd_eq_one.mp hβp')
        rwa [sq] at h1
      rw [quadraticGaussSum_prime_mul_prime_mul β a' p hp2 hβp,
        quadraticGaussSum_prime_mul_prime_mul 1 a' p hp2 h1p, ih a' hlt' hodd' β hβa',
        jacobiSym.mul_right, jacobiSym.mul_right]
      have h2 : ((J(β | p) * (J(β | p) * J(β | a')) : ℤ) : ℂ) = (J(β | a') : ℂ) := by
        rw [← mul_assoc, hsq, one_mul]
      rw [h2]
      ring1
    · have hcop : p.Coprime a₀ := hp.coprime_iff_not_dvd.mpr hd
      have ha₀p : ((a₀ : ℤ) : ZMod p) ≠ 0 := fun h0 ↦ hd <| by
        have h1 : ((a₀ : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
        exact (ZMod.natCast_eq_zero_iff _ _).mp h1
      have hpa₀ : IsCoprime ((p : ℕ) : ℤ) ((a₀ : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
      have e1 : ((β * a₀ : ℤ) : ZMod p) ≠ 0 := by
        rw [Int.cast_mul]
        exact mul_ne_zero hβp ha₀p
      have e2 : ((1 * a₀ : ℤ) : ZMod p) ≠ 0 := by
        rwa [one_mul]
      rw [quadraticGaussSum_mul_of_coprime β p a₀ hcop,
        quadraticGaussSum_mul_of_coprime 1 p a₀ hcop, quadraticGaussSum_prime (β * a₀) p hp2 e1,
        quadraticGaussSum_prime (1 * a₀) p hp2 e2,
        ih a₀ hlt hodd₀ (β * p) (hβa₀.mul_left hpa₀),
        ih a₀ hlt hodd₀ (1 * p) (by rwa [one_mul]), one_mul, one_mul, jacobiSym.mul_left,
        jacobiSym.mul_left, jacobiSym.mul_right]
      push_cast
      ring1

/-- **The quadratic Gauss sum and the Jacobi symbol**: `G(β, a) = (β / a) G(1, a)` for odd `a` and
`β` prime to `a`. -/
lemma quadraticGaussSum_eq_jacobiSym_mul (ha : Odd a) (hβ : IsCoprime β a) :
    quadraticGaussSum β a = J(β | a) * quadraticGaussSum 1 a :=
  aux_eq_jacobiSym_mul a a le_rfl ha β hβ

variable {a} in
private lemma quadraticGaussSum_one_eq :
    quadraticGaussSum 1 a = (1 + I) / 2 * (1 + (-I) ^ a) * Real.sqrt a := by
  rw [← TauCeti.sum_range_cexp_two_pi_I_sq_div, quadraticGaussSum, ← sum_range_natCast_eq]
  refine Finset.sum_congr rfl fun r _ ↦ ?_
  have e : ((1 : ℤ) : ZMod a) * (r : ZMod a) ^ 2 = ((r ^ 2 : ℤ) : ZMod a) := by
    push_cast
    ring1
  rw [e, stdAddChar_coe]
  push_cast
  rfl

/-- **Gauss's evaluation** for `a ≡ 1` modulo `4`: `G(1, a) = √a`. -/
lemma quadraticGaussSum_one_of_mod_four_eq_one (ha : a % 4 = 1) :
    quadraticGaussSum 1 a = Real.sqrt a := by
  have h4 : (-I) ^ 4 = 1 := by
    rw [neg_pow, I_pow_four]
    norm_num
  rw [quadraticGaussSum_one_eq, pow_eq_pow_mod a h4, ha, pow_one]
  have h1 : (1 + I) / 2 * (1 + -I) = 1 := by
    linear_combination (-1 / 2 : ℂ) * I_sq
  rw [h1, one_mul]

/-- **Gauss's evaluation** for `a ≡ 3` modulo `4`: `G(1, a) = i √a`. -/
lemma quadraticGaussSum_one_of_mod_four_eq_three (ha : a % 4 = 3) :
    quadraticGaussSum 1 a = I * Real.sqrt a := by
  have h4 : (-I) ^ 4 = 1 := by
    rw [neg_pow, I_pow_four]
    norm_num
  have h3 : (-I) ^ 3 = I := by
    rw [neg_pow, I_pow_three]
    norm_num
  rw [quadraticGaussSum_one_eq, pow_eq_pow_mod a h4, ha, h3]
  have h1 : (1 + I) / 2 * (1 + I) = I := by
    linear_combination (1 / 2 : ℂ) * I_sq
  rw [h1]

end ZMod
