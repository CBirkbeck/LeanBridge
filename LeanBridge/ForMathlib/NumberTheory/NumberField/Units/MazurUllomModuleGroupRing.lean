import LeanBridge.ForMathlib.NumberTheory.NumberField.Units.MazurUllomModule
import TauCeti.RepresentationTheory.Augmentation.Basic

/-!
# The modules of Mazur and Ullom as modules over the group ring

Mazur and Ullom describe the four basic types I–IV of the units of a real biquadratic field by four
`ℤ[V₄]`-modules: `A₁ ⊕ A₂ ⊕ A₃`, `Aₖ ⊕ Bₖ`, the augmentation ideal `J` of `ℤ[V₄]`, and
`ℤ[V₄]/(ν)` for the trace `ν = Σ_{g ∈ V₄} g`. Here `Aₖ` is `ℤ` with `σₖ` acting by `1` and the two
other nontrivial elements by `-1`, and `Bₖ` is free with a basis `b, c` such that `σₖ b = -b`,
`σᵢ b = c` and `σⱼ b = -c`, for `{i, j, k} = {1, 2, 3}`. This file identifies the modules
`NumberField.Units.MazurUllomBasicType.rep` of `Units/MazurUllomModule.lean`, sublattices of `ℤ³` on
which `V₄ = ℤˣ × ℤˣ` acts by signs, with these. The module of type I is `A₀ ⊕ A₁ ⊕ A₂` by
definition, and:
* the module of type II has the basis `b = (1, 1, 0)`, `c = (1, -1, 0)`, `a = (0, 0, 1)`, with
  `σ₀ b = c`, `σ₁ b = -c`, `σ₂ b = -b` and `σ₂ a = a`, `σ₀ a = σ₁ a = -a`: it is `B₂ ⊕ A₂`;
* the module of type III is isomorphic to `J`, by `x ↦ (x₁ + x_{σⱼ})ⱼ`, which is half of
  `x ↦ (Σ_g x_g χⱼ g)ⱼ` on `J` and sends `1 - σᵢ` to the vector with `0` in place `i` and `1`
  elsewhere;
* the module of type IV is isomorphic to `ℤ[V₄]/(ν)`, by `x ↦ (Σ_g x_g χⱼ g)ⱼ`, whose kernel is
  `ℤ ν`. As `g ν = ν` for every `g`, the multiples `ℤ ν` of `ν` form the ideal `(ν)`.

Here `ℤ[V₄]` carries Mathlib's left regular representation, and `J`, `ν` and `ℤ ν` are Tau Ceti's
augmentation subrepresentation `TauCeti.augmentationSubrepresentation` (the kernel of the
coefficient sum), sum of the standard basis `TauCeti.permutationSum` and invariant line
`TauCeti.invariantLine` for the action of `V₄` on itself.

## Main definitions

* `NumberField.Units.MazurUllomBasicType.typeIIBasis`: the basis `b, c, a` of the module of type II.
* `NumberField.Units.MazurUllomBasicType.augmentationEquiv`: `J` is the module of type III.
* `NumberField.Units.MazurUllomBasicType.traceQuotientEquiv`: `ℤ[V₄]/(ν)` is the module of type IV.

## Main results

* `NumberField.Units.MazurUllomBasicType.rep_typeIIBasis_zero`: the action on `b`, that on `B₂`.
* `NumberField.Units.MazurUllomBasicType.rep_typeIIBasis_two`: the action on `a`, that on `A₂`.

## References

* M. Mazur and S. V. Ullom, *Galois module structure of units in real biquadratic number fields*,
  Acta Arith. 111 (2004), 105–124.
-/

open Module MonoidAlgebra TauCeti

namespace NumberField.Units.MazurUllomBasicType

variable (g : ℤˣ × ℤˣ) (x : MonoidAlgebra ℤ (ℤˣ × ℤˣ)) (j : Fin 3)

/-- The coordinates of the module of type II in the basis `(1, 1, 0)`, `(1, -1, 0)`, `(0, 0, 1)`. -/
def typeIICoords : II.lattice ≃+ (Fin 3 → ℤ) where
  toFun u := ![((u : Fin 3 → ℤ) 0 + (u : Fin 3 → ℤ) 1) / 2,
    ((u : Fin 3 → ℤ) 0 - (u : Fin 3 → ℤ) 1) / 2, (u : Fin 3 → ℤ) 2]
  invFun y := ⟨![y 0 + y 1, y 0 - y 1, y 2], by
    simp only [mem_lattice, Cond, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega⟩
  left_inv u := by
    have hu : 2 ∣ (u : Fin 3 → ℤ) 0 - (u : Fin 3 → ℤ) 1 := u.2
    refine Subtype.ext <| funext fun k ↦ ?_
    fin_cases k <;> simp <;> omega
  right_inv y := by
    funext k
    fin_cases k <;> simp <;> omega
  map_add' u u' := by
    have hu : 2 ∣ (u : Fin 3 → ℤ) 0 - (u : Fin 3 → ℤ) 1 := u.2
    have hu' : 2 ∣ (u' : Fin 3 → ℤ) 0 - (u' : Fin 3 → ℤ) 1 := u'.2
    funext k
    fin_cases k <;> simp <;> omega

/-- The basis `b = (1, 1, 0)`, `c = (1, -1, 0)`, `a = (0, 0, 1)` of the module of type II, on which
`V₄` acts as on the bases of Mazur and Ullom's `B₂` and `A₂`. -/
noncomputable def typeIIBasis : Basis (Fin 3) ℤ II.lattice :=
  .ofEquivFun typeIICoords.toIntLinearEquiv

lemma coe_typeIIBasis (i : Fin 3) :
    (typeIIBasis i : Fin 3 → ℤ) = ![![1, 1, 0], ![1, -1, 0], ![0, 0, 1]] i := by
  rw [typeIIBasis, Basis.coe_ofEquivFun]
  fin_cases i <;> funext k <;> fin_cases k <;> rfl

/-- **The module of type II contains `B₂`**: on `b = (1, 1, 0)` and `c = (1, -1, 0)`,
`σ₀ b = c`, `σ₁ b = -c` and `σ₂ b = -b`, the relations defining Mazur and Ullom's `B₂`. -/
lemma rep_typeIIBasis_zero (i : Fin 3) :
    II.rep (kleinSigma i) (typeIIBasis 0) = ![typeIIBasis 1, -typeIIBasis 1, -typeIIBasis 0] i := by
  refine Subtype.ext <| funext fun k ↦ ?_
  fin_cases i <;> fin_cases k <;> simp [coe_rep_apply, charSumRep_apply, coe_typeIIBasis,
    kleinChar_kleinSigma]

/-- **The module of type II contains `A₂`**: on `a = (0, 0, 1)`, `σ₂ a = a` and `σ₀ a = σ₁ a = -a`,
the relations defining Mazur and Ullom's `A₂`. -/
lemma rep_typeIIBasis_two (i : Fin 3) :
    II.rep (kleinSigma i) (typeIIBasis 2) = ![-typeIIBasis 2, -typeIIBasis 2, typeIIBasis 2] i := by
  refine Subtype.ext <| funext fun k ↦ ?_
  fin_cases i <;> fin_cases k <;> simp [coe_rep_apply, charSumRep_apply, coe_typeIIBasis,
    kleinChar_kleinSigma]

lemma univ_eq :
    (Finset.univ : Finset (ℤˣ × ℤˣ)) = {1, kleinSigma 0, kleinSigma 1, kleinSigma 2} := by
  decide

lemma sum_eq (F : ℤˣ × ℤˣ → ℤ) :
    ∑ g, F g = F 1 + F (kleinSigma 0) + F (kleinSigma 1) + F (kleinSigma 2) := by
  rw [univ_eq, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  ring1

/-- The values `(Σ_g x_g χⱼ g)ⱼ` of the characters `χ₀, χ₁, χ₂` at an element `x` of `ℤ[V₄]`. -/
noncomputable def charVec : MonoidAlgebra ℤ (ℤˣ × ℤˣ) →ₗ[ℤ] Fin 3 → ℤ where
  toFun x j := ∑ g, x.coeff g * kleinChar j g
  map_add' x y := funext fun j ↦ by simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := funext fun j ↦ by
    simp only [coeff_smul, Finsupp.smul_apply, smul_eq_mul, Pi.smul_apply, RingHom.id_apply,
      Finset.mul_sum, mul_assoc]

lemma charVec_apply : charVec x j = ∑ g, x.coeff g * kleinChar j g :=
  rfl

lemma charVec_single (r : ℤ) : charVec (single g r) j = r * kleinChar j g := by
  simp [charVec_apply, Finsupp.single_apply]

lemma charVec_eq : charVec x j = x.coeff 1 + x.coeff (kleinSigma 0) * kleinChar j (kleinSigma 0) +
    x.coeff (kleinSigma 1) * kleinChar j (kleinSigma 1) +
      x.coeff (kleinSigma 2) * kleinChar j (kleinSigma 2) := by
  rw [charVec_apply, sum_eq, (kleinChar j).map_one, Units.val_one, mul_one]

lemma charVec_leftRegular :
    charVec (Representation.leftRegular ℤ (ℤˣ × ℤˣ) g x) = charSumRep g (charVec x) := by
  funext j
  rw [charSumRep_apply, charVec_apply, charVec_apply, Finset.mul_sum]
  refine (Equiv.sum_comp (Equiv.mulLeft g) _).symm.trans (Finset.sum_congr rfl fun k _ ↦ ?_)
  simp only [Equiv.coe_mulLeft, Representation.coeff_ofMulAction, smul_eq_mul,
    inv_mul_cancel_left, map_mul, Units.val_mul]
  ring1

lemma charVec_permutationSum : charVec (permutationSum ℤ (ℤˣ × ℤˣ)) = 0 := by
  funext j
  rw [charVec_eq]
  fin_cases j <;> simp [kleinChar_kleinSigma]

lemma charVec_mem_lattice : charVec x ∈ IV.lattice := by
  simp only [mem_lattice, Cond, charVec_eq, kleinChar_kleinSigma]
  simp
  omega

lemma ker_charVec : LinearMap.ker charVec = (invariantLine ℤ (ℤˣ × ℤˣ) (ℤˣ × ℤˣ)).toSubmodule := by
  ext y
  rw [LinearMap.mem_ker, toSubmodule_invariantLine, Submodule.mem_span_singleton]
  refine ⟨fun h ↦ ⟨y.coeff 1, ?_⟩, ?_⟩
  · have h₀ : charVec y 0 = 0 := congrFun h 0
    have h₁ : charVec y 1 = 0 := congrFun h 1
    have h₂ : charVec y 2 = 0 := congrFun h 2
    rw [charVec_eq] at h₀ h₁ h₂
    simp [kleinChar_kleinSigma] at h₀ h₁ h₂
    ext h
    rw [coeff_smul, Finsupp.smul_apply, coeff_permutationSum, smul_eq_mul, mul_one]
    rcases eq_one_or_exists_kleinSigma h with rfl | ⟨i, rfl⟩
    · rfl
    · fin_cases i <;> simp <;> omega
  · rintro ⟨n, rfl⟩
    rw [map_smul, charVec_permutationSum, smul_zero]

lemma surjective_charVec :
    Function.Surjective (charVec.codRestrict IV.lattice charVec_mem_lattice) := by
  intro v
  have hv : IV.Cond v := v.2
  simp only [Cond] at hv
  refine ⟨single 1 (((v : Fin 3 → ℤ) 0 + (v : Fin 3 → ℤ) 1) / 2) +
    single (kleinSigma 0) (((v : Fin 3 → ℤ) 0 - (v : Fin 3 → ℤ) 2) / 2) +
      single (kleinSigma 1) (((v : Fin 3 → ℤ) 1 - (v : Fin 3 → ℤ) 2) / 2),
    Subtype.ext <| funext fun k ↦ ?_⟩
  rw [LinearMap.codRestrict_apply, map_add, map_add, Pi.add_apply, Pi.add_apply, charVec_single,
    charVec_single, charVec_single, map_one, kleinChar_kleinSigma, kleinChar_kleinSigma]
  fin_cases k <;> simp <;> omega

/-- **The module of type IV is `ℤ[V₄]/(ν)`** (Mazur and Ullom's `A`): `x ↦ (Σ_g x_g χⱼ g)ⱼ`
induces an isomorphism of `ℤ[V₄]`-modules from `ℤ[V₄]/(ν)` onto the module of type IV, the class
of `1` going to `(1, 1, 1)`. The ideal `(ν)` is the line `ℤ ν`, Tau Ceti's invariant line. -/
noncomputable def traceQuotientEquiv :
    (invariantLine ℤ (ℤˣ × ℤˣ) (ℤˣ × ℤˣ)).quotient.Equiv IV.rep :=
  .mk ((Submodule.quotEquivOfEq _ _ <| ker_charVec.symm.trans
      (LinearMap.ker_codRestrict _ _ _).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ surjective_charVec)) fun g ↦
    Submodule.linearMap_qext _ <| LinearMap.ext fun y ↦ Subtype.ext (charVec_leftRegular g y)

lemma sumCoords_basis_eq_sum : (MonoidAlgebra.basis (ℤˣ × ℤˣ) ℤ).sumCoords x = ∑ g, x.coeff g :=
  Finsupp.sum_fintype _ _ fun _ ↦ rfl

/-- The map `x ↦ (x₁ + x_{σⱼ})ⱼ` on the augmentation ideal, half of `x ↦ (Σ_g x_g χⱼ g)ⱼ`. -/
noncomputable def halfCharVec :
    (augmentationSubrepresentation ℤ (ℤˣ × ℤˣ) (ℤˣ × ℤˣ)).toSubmodule →ₗ[ℤ] Fin 3 → ℤ where
  toFun y j := y.1.coeff 1 + y.1.coeff (kleinSigma j)
  map_add' y z := funext fun j ↦ by
    simp only [Submodule.coe_add, coeff_add, Finsupp.add_apply, Pi.add_apply]
    ring1
  map_smul' c y := funext fun j ↦ by
    simp only [Submodule.coe_smul, coeff_smul, Finsupp.smul_apply, RingHom.id_apply, Pi.smul_apply]
    ring1

variable (y : (augmentationSubrepresentation ℤ (ℤˣ × ℤˣ) (ℤˣ × ℤˣ)).toSubmodule)

lemma halfCharVec_apply : halfCharVec y j = y.1.coeff 1 + y.1.coeff (kleinSigma j) :=
  rfl

lemma sum_coeff_eq_zero : y.1.coeff 1 + y.1.coeff (kleinSigma 0) + y.1.coeff (kleinSigma 1) +
    y.1.coeff (kleinSigma 2) = 0 := by
  rw [← sum_eq, ← sumCoords_basis_eq_sum]
  exact y.2

lemma two_smul_halfCharVec : (2 : ℤ) • halfCharVec y = charVec y := by
  funext k
  rw [Pi.smul_apply, halfCharVec_apply, charVec_eq]
  fin_cases k <;> simp [kleinChar_kleinSigma] <;> linarith [sum_coeff_eq_zero y]

lemma halfCharVec_mem_lattice : halfCharVec y ∈ III.lattice := by
  simp only [mem_lattice, Cond, halfCharVec_apply]
  exact ⟨y.1.coeff 1, by linarith [sum_coeff_eq_zero y]⟩

lemma halfCharVec_leftRegular :
    halfCharVec ((augmentationSubrepresentation ℤ (ℤˣ × ℤˣ) (ℤˣ × ℤˣ)).toRepresentation g y) =
      charSumRep g (halfCharVec y) := by
  refine smul_right_injective (Fin 3 → ℤ) (two_ne_zero : (2 : ℤ) ≠ 0) ?_
  dsimp only
  rw [two_smul_halfCharVec, ← map_smul, two_smul_halfCharVec]
  exact charVec_leftRegular g y

lemma injective_halfCharVec : Function.Injective halfCharVec := by
  refine (injective_iff_map_eq_zero halfCharVec).mpr fun y hy ↦ ?_
  have h0 : charVec y = 0 := by
    rw [← two_smul_halfCharVec, hy, smul_zero]
  have hmem : y.1 ∈ LinearMap.ker charVec := LinearMap.mem_ker.mpr h0
  rw [ker_charVec] at hmem
  rcases mem_invariantLine_iff.mp hmem with ⟨n, hn⟩
  have hcoeff (h : ℤˣ × ℤˣ) : y.1.coeff h = n := by
    rw [← hn, coeff_smul, Finsupp.smul_apply, coeff_permutationSum, smul_eq_mul, mul_one]
  have hn0 : n = 0 := by
    linarith [sum_coeff_eq_zero y, hcoeff 1, hcoeff (kleinSigma 0), hcoeff (kleinSigma 1),
      hcoeff (kleinSigma 2)]
  exact Subtype.ext <| by rw [← hn, hn0, zero_smul, Submodule.coe_zero]

lemma surjective_halfCharVec :
    Function.Surjective (halfCharVec.codRestrict III.lattice halfCharVec_mem_lattice) := by
  intro v
  have hv : III.Cond v := v.2
  simp only [Cond] at hv
  have hmem (i : Fin 3) : single 1 1 - single (kleinSigma i) 1 ∈
      (augmentationSubrepresentation ℤ (ℤˣ × ℤˣ) (ℤˣ × ℤˣ)).toSubmodule :=
    single_sub_single_mem_augmentationSubrepresentation 1 (kleinSigma i)
  let z : (augmentationSubrepresentation ℤ (ℤˣ × ℤˣ) (ℤˣ × ℤˣ)).toSubmodule :=
    (((v : Fin 3 → ℤ) 1 + (v : Fin 3 → ℤ) 2 - (v : Fin 3 → ℤ) 0) / 2) • ⟨_, hmem 0⟩ +
      (((v : Fin 3 → ℤ) 0 + (v : Fin 3 → ℤ) 2 - (v : Fin 3 → ℤ) 1) / 2) • ⟨_, hmem 1⟩ +
        (((v : Fin 3 → ℤ) 0 + (v : Fin 3 → ℤ) 1 - (v : Fin 3 → ℤ) 2) / 2) • ⟨_, hmem 2⟩
  refine ⟨z, Subtype.ext <| smul_right_injective (Fin 3 → ℤ) (two_ne_zero : (2 : ℤ) ≠ 0) ?_⟩
  dsimp only
  rw [LinearMap.codRestrict_apply, two_smul_halfCharVec]
  funext k
  simp only [z, Submodule.coe_add, Submodule.coe_smul, map_add, map_smul, map_sub, Pi.add_apply,
    Pi.smul_apply, Pi.sub_apply, charVec_single, kleinChar_kleinSigma]
  fin_cases k <;> simp <;> omega

/-- **The module of type III is the augmentation ideal `J` of `ℤ[V₄]`** (Mazur and Ullom's `J`):
`x ↦ (x₁ + x_{σⱼ})ⱼ` is an isomorphism of `ℤ[V₄]`-modules from `J`, Tau Ceti's augmentation
subrepresentation of `ℤ[V₄]`, onto the module of type III, sending `1 - σᵢ` to the vector with `0`
in place `i` and `1` elsewhere. -/
noncomputable def augmentationEquiv :
    (augmentationSubrepresentation ℤ (ℤˣ × ℤˣ) (ℤˣ × ℤˣ)).toRepresentation.Equiv III.rep :=
  .mk (LinearEquiv.ofBijective _ ⟨fun _ _ h ↦ injective_halfCharVec (congrArg Subtype.val h),
    surjective_halfCharVec⟩) fun g ↦ LinearMap.ext fun y ↦ Subtype.ext (halfCharVec_leftRegular g y)

end NumberField.Units.MazurUllomBasicType
