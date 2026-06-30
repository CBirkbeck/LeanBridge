/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanBridge.ForMathlib.AbstractHeckeRing.Ring

/-!
# Hecke Rings: Degree Map

The degree ring homomorphism `deg : 𝕋 P ℤ →+* ℤ`, which sends each
double coset `HgH` to the number of left cosets it contains:
`deg(HgH) = [H : H ∩ gHg⁻¹]`.

This is Shimura §3.1, Proposition 3.3.

## Main definitions

* `HeckeCoset_deg P D` : the degree of a single double coset
* `deg P` : the degree ring homomorphism `𝕋 P ℤ →+* ℤ`

## Main results

* `deg_T_single` : `deg(T_single D a) = a * HeckeCoset_deg D`
* `HeckeCoset_deg_pos` : `0 < HeckeCoset_deg D`
* `deg_mul` : `deg(f * g) = deg f * deg g` (the degree map is multiplicative)

## Proof strategy

Multiplicativity `deg(f * g) = deg(f) * deg(g)` is proved using the module action
on `HeckeModule P ℤ`.
We show `deg(f) = coeffSum(f • 1)` where `coeffSum` sums all coefficients, and then use
`IsScalarTower` (Shimura Prop 3.4) to get `(f * g) • 1 = g • (f • 1)`. The key intermediate
result is `coeffSum(f • m) = deg(f) * coeffSum(m)`, which follows from the orbit cardinality
lemma `smulOrbit_card`.
-/

open Classical MulOpposite Set DoubleCoset Subgroup

open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G]
variable (P : HeckePair G)

open Finsupp

/-- The degree of a double coset: `deg(HgH) = [H : H ∩ gHg⁻¹]`, the number of left cosets
in the decomposition of `HgH`. -/
noncomputable def HeckeCoset_deg (D : HeckeCoset P) : ℤ :=
  Fintype.card (decompQuot P (HeckeCoset.rep D))

/-- The degree of the identity double coset is 1. -/
@[simp] lemma HeckeCoset_deg_T_one : HeckeCoset_deg P (HeckeCoset.one P) = 1 := by
  haveI := subsingleton_decompQuot_T_one P
  haveI : Unique (decompQuot P (HeckeCoset.one P).rep) :=
    uniqueOfSubsingleton (one_in_decompQuot_T_one P).some
  simp [HeckeCoset_deg, Fintype.card_unique]

/-- Every double coset has positive degree. -/
lemma HeckeCoset_deg_pos (D : HeckeCoset P) : 0 < HeckeCoset_deg P D := by
  unfold HeckeCoset_deg; exact_mod_cast Fintype.card_pos

section SmulOrbitCard

private lemma smulOrbit_map_inj (g : P.Δ) (β : P.Δ) :
    Function.Injective (fun i : decompQuot P g ↦
      (⟦⟨(β : G) * (i.out : G) * (g : G),
        delta_mul_mem P.H P.Δ i.out β g P.h₀⟩⟧ : HeckeLeftCoset P)) := by
  intro i₁ i₂ heq
  by_contra hne
  have hset : ({(β : G) * (i₁.out : G) * (g : G)} : Set G) * (P.H : Set G) =
      {(β : G) * (i₂.out : G) * (g : G)} * P.H := Quotient.exact heq
  have hmem : (β : G) * (i₁.out : G) * (g : G) ∈
      ({(β : G) * (i₂.out : G) * (g : G)} : Set G) * (P.H : Set G) :=
    hset ▸ ⟨_, rfl, 1, P.H.one_mem, mul_one _⟩
  obtain ⟨_, ha, k, hk, hkk⟩ := hmem
  rw [Set.mem_singleton_iff] at ha; subst ha
  have cancel : (i₂.out : G) * (g : G) * k = (i₁.out : G) * (g : G) := by
    refine mul_left_cancel (a := (β : G)) ?_
    have := hkk; group at this ⊢; exact this
  refine decompQuot_coset_diff P g i₁ i₂ hne
    (leftCoset_eq_of_not_disjoint (H := P.H) _ _ ?_)
  rw [Set.not_disjoint_iff]
  exact ⟨(i₁.out : G) * (g : G), ⟨1, P.H.one_mem, mul_one _⟩, ⟨k, hk, cancel⟩⟩

/-- The cardinality of a smul orbit equals the degree of the acting double coset. -/
lemma smulOrbit_card (g : P.Δ) (β : P.Δ) :
    (smulOrbit P g β).card = Fintype.card (decompQuot P g) := by
  show (Finset.image _ ⊤).card = _
  rw [Finset.top_eq_univ]
  convert (Finset.card_image_of_injective Finset.univ
    (smulOrbit_map_inj P g β)).trans Finset.card_univ
  rfl

/-- The cardinality of a smul orbit cast to `ℤ` equals `HeckeCoset_deg`. -/
lemma smulOrbit_card_intCast (D : HeckeCoset P) (β : P.Δ) :
    ((smulOrbit P (HeckeCoset.rep D) β).card : ℤ) = HeckeCoset_deg P D := by
  simp [smulOrbit_card, HeckeCoset_deg]

end SmulOrbitCard

section CoeffSum

/-- The coefficient sum homomorphism: sums all coefficients of a formal linear combination
of left cosets. -/
noncomputable def coeffSum : HeckeModule P ℤ →+ ℤ :=
  Finsupp.liftAddHom (fun _ : HeckeLeftCoset P ↦ AddMonoidHom.id ℤ)

/-- The coefficient sum of a single basis element is its coefficient. -/
@[simp] lemma coeffSum_single (m₀ : HeckeLeftCoset P) (b : ℤ) :
    coeffSum P (HeckeLeftCoset_single P ℤ m₀ b) = b := Finsupp.liftAddHom_apply_single _ _ _

/-- The coefficient sum is additive. -/
lemma coeffSum_add (m₁ m₂ : HeckeModule P ℤ) :
    coeffSum P (m₁ + m₂) = coeffSum P m₁ + coeffSum P m₂ := map_add _ _ _

/-- The coefficient sum distributes over finite sums. -/
lemma coeffSum_finset_sum {ι : Type*} (s : Finset ι) (f : ι → HeckeModule P ℤ) :
    coeffSum P (∑ i ∈ s, f i) = ∑ i ∈ s, coeffSum P (f i) := map_sum _ _ _

/-- The coefficient sum of a single-single smul product equals `a * deg(D) * b`. -/
lemma coeffSum_single_smul_single (D : HeckeCoset P) (m₀ : HeckeLeftCoset P) (a b : ℤ) :
    coeffSum P (T_single P ℤ D a • HeckeLeftCoset_single P ℤ m₀ b) =
    a * HeckeCoset_deg P D * b := by
  rw [T_single_smul_HeckeLeftCoset_single, coeffSum_finset_sum]
  simp only [coeffSum_single, Finset.sum_const, Int.nsmul_eq_mul,
    smulOrbit_card_intCast P D (HeckeLeftCoset.rep m₀)]
  ring

end CoeffSum

section DegreeMap

/-- The underlying function of the degree map: `Σ_D a_D * deg(D)`. -/
noncomputable def deg_fun (f : 𝕋 P ℤ) : ℤ := f.sum fun D a ↦ a * HeckeCoset_deg P D

/-- The degree function of zero is zero. -/
@[simp] lemma deg_fun_zero : deg_fun P (0 : 𝕋 P ℤ) = 0 := Finsupp.sum_zero_index

/-- The degree function of a basis element is `a * deg(D)`. -/
@[simp] lemma deg_fun_T_single (D : HeckeCoset P) (a : ℤ) :
    deg_fun P (T_single P ℤ D a) = a * HeckeCoset_deg P D :=
  Finsupp.sum_single_index (by simp)

/-- The degree function is additive. -/
lemma deg_fun_add (f g : 𝕋 P ℤ) :
    deg_fun P (f + g) = deg_fun P f + deg_fun P g :=
  Finsupp.sum_add_index' (fun _ ↦ by simp) (fun _ _ _ ↦ by ring)

/-- The degree function of the identity is 1. -/
@[simp] lemma deg_fun_one : deg_fun P (1 : 𝕋 P ℤ) = 1 := by
  simp [one_def]

/-- The degree equals the coefficient sum of the action on the identity module element. -/
lemma deg_fun_eq_coeffSum_smul_one (f : 𝕋 P ℤ) :
    deg_fun P f = coeffSum P (f • (1 : HeckeModule P ℤ)) := by
  let toT : (HeckeCoset P →₀ ℤ) → 𝕋 P ℤ := fun a ↦ a
  let mot : (HeckeCoset P →₀ ℤ) → Prop :=
    fun f' ↦ deg_fun P (toT f') = coeffSum P ((toT f') • (1 : HeckeModule P ℤ))
  change mot f
  apply Finsupp.induction_linear
  · show deg_fun P (toT 0) = coeffSum P ((toT 0) • (1 : HeckeModule P ℤ))
    change deg_fun P (0 : 𝕋 P ℤ) = coeffSum P (((0 : 𝕋 P ℤ)) • (1 : HeckeModule P ℤ))
    simp [zero_smul_HeckeModule]
  · intro f g ihf ihg
    show deg_fun P (toT (f + g)) =
      coeffSum P ((toT (f + g)) • (1 : HeckeModule P ℤ))
    change deg_fun P ((toT f + toT g) : 𝕋 P ℤ) =
      coeffSum P (((toT f + toT g) : 𝕋 P ℤ) • (1 : HeckeModule P ℤ))
    rw [deg_fun_add, ihf, ihg, smul_add_left, coeffSum_add]
  · intro D a
    show deg_fun P (toT (Finsupp.single D a)) =
      coeffSum P ((toT (Finsupp.single D a)) • (1 : HeckeModule P ℤ))
    rw [deg_fun_T_single, one_eq_HeckeLeftCoset_single,
      coeffSum_single_smul_single, mul_one]

/-- The coefficient sum of a smul product factors as `deg(f) * coeffSum(m)`. -/
lemma coeffSum_smul_eq (f : 𝕋 P ℤ) (m : HeckeModule P ℤ) :
    coeffSum P (f • m) = deg_fun P f * coeffSum P m := by
  let toT : (HeckeCoset P →₀ ℤ) → 𝕋 P ℤ := fun a ↦ a
  let toM : (HeckeLeftCoset P →₀ ℤ) → HeckeModule P ℤ := fun a ↦ a
  let motf : (HeckeCoset P →₀ ℤ) → Prop :=
    fun f' ↦ coeffSum P ((toT f') • m) = deg_fun P (toT f') * coeffSum P m
  change motf f
  apply Finsupp.induction_linear
  · show coeffSum P ((toT 0) • m) = deg_fun P (toT 0) * coeffSum P m
    change coeffSum P (((0 : 𝕋 P ℤ)) • m) = deg_fun P (0 : 𝕋 P ℤ) * coeffSum P m
    simp [zero_smul_HeckeModule]
  · intro f₁ f₂ ih₁ ih₂
    show coeffSum P ((toT (f₁ + f₂)) • m) =
      deg_fun P (toT (f₁ + f₂)) * coeffSum P m
    change coeffSum P (((toT f₁ + toT f₂) : 𝕋 P ℤ) • m) =
      deg_fun P ((toT f₁ + toT f₂) : 𝕋 P ℤ) * coeffSum P m
    rw [smul_add_left, coeffSum_add, ih₁, ih₂, deg_fun_add]; ring
  · intro D a
    show coeffSum P ((toT (Finsupp.single D a)) • m) =
      deg_fun P (toT (Finsupp.single D a)) * coeffSum P m
    let motm : (HeckeLeftCoset P →₀ ℤ) → Prop :=
      fun m' ↦ coeffSum P ((toT (Finsupp.single D a)) • (toM m')) =
        deg_fun P (toT (Finsupp.single D a)) * coeffSum P (toM m')
    change motm m
    apply Finsupp.induction_linear
    · show coeffSum P ((toT (Finsupp.single D a)) • (toM 0)) =
        deg_fun P (toT (Finsupp.single D a)) * coeffSum P (toM 0)
      change coeffSum P ((toT (Finsupp.single D a)) • (0 : HeckeModule P ℤ)) =
        deg_fun P (toT (Finsupp.single D a)) * coeffSum P (0 : HeckeModule P ℤ)
      simp [smul_zero_HeckeModule]
    · intro m₁ m₂ ih₁ ih₂
      show coeffSum P ((toT (Finsupp.single D a)) • (toM (m₁ + m₂))) =
        deg_fun P (toT (Finsupp.single D a)) * coeffSum P (toM (m₁ + m₂))
      change coeffSum P
          ((toT (Finsupp.single D a)) • ((toM m₁ + toM m₂) : HeckeModule P ℤ)) =
        deg_fun P (toT (Finsupp.single D a)) *
          coeffSum P ((toM m₁ + toM m₂) : HeckeModule P ℤ)
      rw [smul_add_right, coeffSum_add, ih₁, ih₂, coeffSum_add, deg_fun_T_single]; ring
    · intro m₀ b
      show coeffSum P ((toT (Finsupp.single D a)) • (toM (Finsupp.single m₀ b))) =
        deg_fun P (toT (Finsupp.single D a)) * coeffSum P (toM (Finsupp.single m₀ b))
      rw [coeffSum_single_smul_single, coeffSum_single, deg_fun_T_single]

/-- The degree function is multiplicative. -/
lemma deg_fun_mul (f g : 𝕋 P ℤ) :
    deg_fun P (f * g) = deg_fun P f * deg_fun P g := by
  have h := (instIsScalarTower P).smul_assoc g f (1 : HeckeModule P ℤ)
  simp only [smul_def] at h
  rw [deg_fun_eq_coeffSum_smul_one P (f * g), h, coeffSum_smul_eq,
    ← deg_fun_eq_coeffSum_smul_one P f]; ring

/-- The degree ring homomorphism `deg : 𝕋 P ℤ →+* ℤ`, sending each double coset to the
number of left cosets it contains (Shimura Proposition 3.3). -/
noncomputable def deg : 𝕋 P ℤ →+* ℤ where
  toFun := deg_fun P
  map_zero' := deg_fun_zero P
  map_one' := deg_fun_one P
  map_add' := deg_fun_add P
  map_mul' := deg_fun_mul P

end DegreeMap

section API

/-- The degree of a basis element is the coefficient times the degree of the double coset. -/
@[simp] lemma deg_T_single (D : HeckeCoset P) (a : ℤ) :
    deg P (T_single P ℤ D a) = a * HeckeCoset_deg P D := deg_fun_T_single P D a

/-- The degree map is multiplicative: `deg(f * g) = deg(f) * deg(g)`. -/
lemma deg_mul (f g : 𝕋 P ℤ) : deg P (f * g) = deg P f * deg P g := (deg P).map_mul f g

/-- **Generic multiplicity-degree-sum identity**: when the support of the
multiplication finsupp `m P D₁ D₂` is contained in `{D_out1, D_out2}`, the
weighted sum of multiplicities by degrees equals the product of degrees. -/
lemma heckeMultiplicity_deg_sum_eq (D1 D2 D_out1 D_out2 : HeckeCoset P)
    (h_ne : D_out1 ≠ D_out2) (h_zero : ∀ A, A ≠ D_out1 → A ≠ D_out2 →
      heckeMultiplicity P (HeckeCoset.rep D1) (HeckeCoset.rep D2)
        (HeckeCoset.rep A) = 0) :
    heckeMultiplicity P (HeckeCoset.rep D1) (HeckeCoset.rep D2)
      (HeckeCoset.rep D_out1) * HeckeCoset_deg P D_out1 +
      heckeMultiplicity P (HeckeCoset.rep D1) (HeckeCoset.rep D2)
        (HeckeCoset.rep D_out2) * HeckeCoset_deg P D_out2 =
      HeckeCoset_deg P D1 * HeckeCoset_deg P D2 := by
  have h1 : deg P (m P (HeckeCoset.rep D1) (HeckeCoset.rep D2)) =
      HeckeCoset_deg P D1 * HeckeCoset_deg P D2 := by
    rw [← T_single_one_mul_T_single_one, deg_mul, deg_T_single, deg_T_single]; ring
  have h2 : deg P (m P (HeckeCoset.rep D1) (HeckeCoset.rep D2)) =
      heckeMultiplicity P (HeckeCoset.rep D1) (HeckeCoset.rep D2)
        (HeckeCoset.rep D_out1) * HeckeCoset_deg P D_out1 +
        heckeMultiplicity P (HeckeCoset.rep D1) (HeckeCoset.rep D2)
          (HeckeCoset.rep D_out2) * HeckeCoset_deg P D_out2 := by
    simp only [deg, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, deg_fun]
    have hsub : (m P (HeckeCoset.rep D1) (HeckeCoset.rep D2)).support ⊆
        ({D_out1, D_out2} : Finset _) := fun A hA ↦ by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      rw [Finsupp.mem_support_iff] at hA
      exact or_iff_not_imp_left.mpr fun h1 ↦
        (Classical.em (A = D_out2)).elim id fun h2 ↦ absurd (h_zero A h1 h2) hA
    exact (Finset.sum_subset hsub fun A _ hA ↦ by
        rw [Finsupp.notMem_support_iff.mp hA]; simp).trans (Finset.sum_pair h_ne)
  linarith

end API

end HeckeRing
