/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanBridge.ForMathlib.AbstractHeckeRing.Associativity

/-!
# Hecke Rings: Ring Instance and API

The `Ring (𝕋 P ℤ)` instance and user-facing API lemmas for working with Hecke rings.
-/

open Classical MulOpposite Set DoubleCoset Subgroup

open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G]

variable (P : HeckePair G) (Z : Type*) [CommRing Z]

open Finsupp

/-- Associativity of multiplication in the Hecke ring, deduced from `IsScalarTower`
and faithfulness of the module action. -/
lemma mul_assoc_𝕋 (f g h : 𝕋 P ℤ) : (f * g) * h = f * (g * h) := by
  refine (instFaithfulSMulHeckeModule P).eq_of_smul_eq_smul (M := 𝕋 P ℤ) fun a ↦ ?_
  have e1 := (instIsScalarTower P).smul_assoc g f a
  have e2 := (instIsScalarTower P).smul_assoc h g (f • a)
  have e4 := (instIsScalarTower P).smul_assoc h (f * g) a
  simp only [smul_def] at e1 e2 e4
  rw [e1, ← e2, ← (instIsScalarTower P).smul_assoc (g * h) f a, smul_def] at e4
  exact e4

/-- The Hecke ring is a non-unital semiring (associativity + distributivity). -/
noncomputable instance instNonUnitalSemiring : NonUnitalSemiring (𝕋 P ℤ) :=
  { instNonUnitalNonAssocSemiring P with mul_assoc := mul_assoc_𝕋 P }

/-- The multiplicative identity of the Hecke ring is `T_single (HeckeCoset.one P) 1`. -/
noncomputable instance instOne𝕋 : One (𝕋 P Z) :=
  ⟨T_single P Z (HeckeCoset.one P) 1⟩

/-- The one element of the Hecke ring unfolds to `T_single (HeckeCoset.one P) 1`. -/
theorem one_def : (1 : 𝕋 P Z) = T_single P Z (HeckeCoset.one P) 1 := rfl

/-- The Hecke ring is a non-associative semiring (one is a two-sided identity). -/
noncomputable instance instNonAssocSemiring : NonAssocSemiring (𝕋 P ℤ) :=
  { instNonUnitalNonAssocSemiring P with
    natCast := fun n ↦ T_single P ℤ (HeckeCoset.one P) n
    natCast_zero := by simp only [Nat.cast_zero, single_zero]; rfl
    natCast_succ := fun _ ↦ by
      simp only [Nat.cast_add, Nat.cast_one, single_add]; rfl
    one_mul := fun f ↦ by
      simp only [one_def, mul_def, T_single]
      simp
      nth_rw 2 [← Finsupp.sum_single f]
      congr
      ext D z v
      have := one_mul_singleton_𝕋 P D z
      simp_rw [T_single] at *
      rw [← this, mul_singleton_𝕋, one_smul]
    mul_one := fun f ↦ by
      simp only [one_def, mul_def, zero_smul, smul_zero, sum_single_index, one_smul]
      nth_rw 2 [← Finsupp.sum_single f]
      congr
      ext D z v
      have := singleton_one_mul_𝕋 P D z
      simp_rw [T_single] at this
      rw [← this, mul_singleton_𝕋, one_smul] }

/-- The Hecke ring is a semiring. -/
noncomputable instance instSemiring : Semiring (𝕋 P ℤ) :=
  { HeckeRing.instNonUnitalSemiring P,
    HeckeRing.instNonAssocSemiring P with }

/-- The Hecke ring is a non-associative ring (semiring + additive inverses). -/
noncomputable instance instNonAssocRing : NonAssocRing (𝕋 P ℤ) :=
  { HeckeRing.instAddCommGroup𝕋 P ℤ,
    HeckeRing.instNonAssocSemiring P with
    intCast := fun n ↦ T_single P ℤ (HeckeCoset.one P) n
    intCast_ofNat := fun _ ↦ rfl
    intCast_negSucc := fun _ ↦ by
      simp only [T_single, Int.negSucc_eq, Finsupp.single_neg]; congr 1 }

/-- The Hecke ring `𝕋 P ℤ` is a ring. -/
noncomputable instance instRing : Ring (𝕋 P ℤ) :=
  { HeckeRing.instNonAssocRing P, HeckeRing.instSemiring P with }

section API

/-- A basis element with coefficient zero is zero. -/
@[simp] lemma T_single_zero (D : HeckeCoset P) :
    T_single P ℤ D 0 = 0 := Finsupp.single_zero _

/-- Addition of two basis elements with the same double coset. -/
@[simp] lemma T_single_add (D : HeckeCoset P) (a b : ℤ) :
    T_single P ℤ D a + T_single P ℤ D b = T_single P ℤ D (a + b) :=
  (Finsupp.single_add D a b).symm

/-- Negation of a basis element. -/
@[simp] lemma T_single_neg (D : HeckeCoset P) (a : ℤ) :
    -T_single P ℤ D a = T_single P ℤ D (-a) := (Finsupp.single_neg D a).symm

/-- Scalar multiplication on a basis element. -/
lemma T_single_smul (D : HeckeCoset P) (n a : ℤ) :
    n • T_single P ℤ D a = T_single P ℤ D (n * a) := Finsupp.smul_single' n D a

/-- The integer cast into the Hecke ring lands on the identity double coset. -/
@[simp] lemma intCast_eq (n : ℤ) : (n : 𝕋 P ℤ) = T_single P ℤ (HeckeCoset.one P) n :=
  rfl

/-- The product of two basis elements equals the scaled multiplication finsupp. -/
lemma T_single_mul_T_single (D₁ D₂ : HeckeCoset P) (a b : ℤ) :
    T_single P ℤ D₁ a * T_single P ℤ D₂ b =
      a • b • m P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) :=
  mul_singleton_𝕋 P D₁ D₂ a b

/-- The product of two unit-coefficient basis elements is the multiplication finsupp. -/
@[simp] lemma T_single_one_mul_T_single_one (D₁ D₂ : HeckeCoset P) :
    T_single P ℤ D₁ 1 * T_single P ℤ D₂ 1 =
      m P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) := by
  simp [T_single_mul_T_single]

/-- Right multiplication by 1 is the identity. -/
@[simp] lemma T_single_mul_one (D : HeckeCoset P) (a : ℤ) :
    T_single P ℤ D a * 1 = T_single P ℤ D a := singleton_one_mul_𝕋 P D a

/-- Left multiplication by 1 is the identity. -/
@[simp] lemma one_mul_T_single (D : HeckeCoset P) (a : ℤ) :
    1 * T_single P ℤ D a = T_single P ℤ D a := one_mul_singleton_𝕋 P D a

/-- When `heckeMultiplicity` is one on a single output and zero elsewhere, multiplication of
unit-coefficient basis elements produces a single basis element. -/
lemma T_single_one_mul_eq_single (D₁ D₂ D_out : HeckeCoset P)
    (h_one : heckeMultiplicity P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)
      (HeckeCoset.rep D_out) = 1)
    (h_zero : ∀ A, A ≠ D_out → heckeMultiplicity P (HeckeCoset.rep D₁)
      (HeckeCoset.rep D₂) (HeckeCoset.rep A) = 0) :
    T_single P ℤ D₁ 1 * T_single P ℤ D₂ 1 = T_single P ℤ D_out 1 := by
  rw [T_single_one_mul_T_single_one,
    m_eq_single P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) D_out h_one h_zero]

/-- Evaluating the multiplication finsupp at a double coset gives `heckeMultiplicity`. -/
@[simp] lemma m_apply (g₁ g₂ : P.Δ) (D : HeckeCoset P) :
    (m P g₁ g₂) D = heckeMultiplicity P g₁ g₂ (HeckeCoset.rep D) := rfl

/-- Right multiplication by `HeckeCoset.one` is the identity on `m`. -/
@[simp] lemma m_mul_T_one (D : HeckeCoset P) :
    m P (HeckeCoset.rep D) (HeckeCoset.one P).rep =
      Finsupp.single (⟦HeckeCoset.rep D⟧ : HeckeCoset P) 1 :=
  m_mul_one_eq_single P (HeckeCoset.rep D)

/-- Left multiplication by `HeckeCoset.one` is the identity on `m`. -/
@[simp] lemma m_T_one_mul (D : HeckeCoset P) :
    m P (HeckeCoset.one P).rep (HeckeCoset.rep D) =
      Finsupp.single (⟦HeckeCoset.rep D⟧ : HeckeCoset P) 1 :=
  m_one_mul_eq_single P (HeckeCoset.rep D)

/-- The support of the multiplication finsupp equals `mulSupport`. -/
lemma m_support (g₁ g₂ : P.Δ) :
    (m P g₁ g₂).support = mulSupport P g₁ g₂ := rfl

/-- The multiplicity `heckeMultiplicity` is nonneg since it is a natural number cast to `ℤ`. -/
lemma heckeMultiplicity_nonneg (g₁ g₂ d : P.Δ) :
    0 ≤ heckeMultiplicity P g₁ g₂ d := by
  simp [heckeMultiplicity]

/-- Extensionality for Hecke ring elements. -/
@[ext] lemma ext_𝕋 {f g : 𝕋 P ℤ}
    (h : ∀ D : HeckeCoset P, f.toFun D = g.toFun D) : f = g := Finsupp.ext h

/-- Linear induction principle: reduce to zero, single basis elements, and sums. -/
lemma induction_linear_𝕋 {C : 𝕋 P ℤ → Prop} (f : 𝕋 P ℤ) (h_zero : C 0)
    (h_single : ∀ (D : HeckeCoset P) (a : ℤ), C (T_single P ℤ D a))
    (h_add : ∀ f g : 𝕋 P ℤ, C f → C g → C (f + g)) : C f :=
  Finsupp.induction_linear f h_zero h_add h_single

/-- The action of a basis Hecke element on a basis module element as a sum over orbits. -/
lemma T_single_smul_HeckeLeftCoset_single (D : HeckeCoset P) (m₀ : HeckeLeftCoset P) (a b : Z) :
    T_single P Z D a • HeckeLeftCoset_single P Z m₀ b =
    ∑ i ∈ smulOrbit P (HeckeCoset.rep D) (HeckeLeftCoset.rep m₀),
      HeckeLeftCoset_single P Z i (a * b) :=
  single_smul_single P Z D m₀ a b

end API

end HeckeRing
