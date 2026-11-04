import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SatakeHeckeProduct
import TauCeti.NumberTheory.HeckeRing.LinearExtension

/-!
# Spherical maps of Hecke rings

Let `(Γ, Δ)` be a Hecke pair in a group `G` and `B ≤ G` a subgroup such that every right coset `Γx`,
`x ∈ Δ`, meets `B`, and let `χ : B → Rˣ` be a character, with values in a commutative ring, trivial
on `B ∩ Γ`. Then `χ(Γx) := χ(b)` for `b ∈ Γx ∩ B` is well defined, and
`ω_χ(ΓαΓ) = ∑_{Γx ⊆ ΓαΓ} χ(Γx)` extends to a **ring homomorphism** `ω_χ : 𝓗(Γ, Δ) → R`: by Shimura's
product formula (`HeckeCoset.rightCosetSumLinear_single_mul_single`), `ω_χ(D₁D₂)` is the sum of
`χ(Γaᵥb_w)` over the right coset representatives `aᵥ` of `D₁` and `b_w` of `D₂`; writing
`b_w = γ_w⁻¹ b'_w` with `b'_w ∈ B`, `χ(Γaᵥb_w) = χ(Γaᵥγ_w⁻¹) χ(b'_w)`, and right multiplication by
`γ_w⁻¹` permutes the right cosets of `D₁`. This is the construction of the Satake map
(Andrianov, *Quadratic forms and Hecke operators*, §3.3.3; Satake, *Theory of spherical functions on
reductive algebraic groups over p-adic fields*) in the generality of a Hecke pair.

## Main definitions

* `HeckeCoset.borelValue`: the value `χ(Γx)` of `χ` on the right coset `Γx`.
* `HeckeCoset.sphericalMap`: the spherical map `ω_χ : 𝓗(Γ, Δ) → R`.

## Main results

* `HeckeCoset.sphericalMap_single`: `ω_χ(ΓαΓ) = ∑_{Γx ⊆ ΓαΓ} χ(Γx)`.
-/

open DoubleCoset

namespace HeckeCoset

variable {G : Type*} [Group G] {Δ : Submonoid G} (Γ : Subgroup G) [IsHeckeTriple Δ Γ Γ]
  {B : Subgroup G} {R : Type*} [CommRing R] (χ : B →* Rˣ)

open scoped Classical in
/-- The value `χ(Γx) = χ(γx)` of a character `χ` of `B` on a right coset `Γx` meeting `B` at
`γx`, `γ ∈ Γ`; it is `0` when `Γx` does not meet `B`. It does not depend on `γ` when `χ` is
trivial on `B ∩ Γ`. -/
noncomputable def borelValue (x : G) : R :=
  if h : ∃ γ ∈ Γ, γ * x ∈ B then (χ ⟨_, h.choose_spec.2⟩ : R) else 0

variable {Γ χ} {γ x : G}

lemma borelValue_eq (hχ : ∀ b : B, (b : G) ∈ Γ → χ b = 1) (hγ : γ ∈ Γ) (hb : γ * x ∈ B) :
    borelValue Γ χ x = χ ⟨γ * x, hb⟩ := by
  have hex : ∃ γ ∈ Γ, γ * x ∈ B := ⟨γ, hγ, hb⟩
  rw [borelValue, dite_eq_left hex]
  have hmem : hex.choose * x * (γ * x)⁻¹ ∈ B := mul_mem hex.choose_spec.2 (inv_mem hb)
  have hΓ : hex.choose * x * (γ * x)⁻¹ ∈ Γ := by
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel_right]
    exact mul_mem hex.choose_spec.1 (inv_mem hγ)
  have e : (⟨hex.choose * x, hex.choose_spec.2⟩ : B) = ⟨_, hmem⟩ * ⟨γ * x, hb⟩ :=
    Subtype.ext (inv_mul_cancel_right _ _).symm
  rw [e, map_mul, hχ ⟨_, hmem⟩ hΓ, one_mul]

lemma borelValue_mul_left (hχ : ∀ b : B, (b : G) ∈ Γ → χ b = 1) (hγ : γ ∈ Γ) :
    borelValue Γ χ (γ * x) = borelValue Γ χ x := by
  by_cases hx : ∃ γ' ∈ Γ, γ' * x ∈ B
  · rcases hx with ⟨γ', hγ', hb⟩
    have hb' : γ' * γ⁻¹ * (γ * x) ∈ B := by rwa [mul_assoc, inv_mul_cancel_left]
    have e : (⟨γ' * γ⁻¹ * (γ * x), hb'⟩ : B) = ⟨γ' * x, hb⟩ :=
      Subtype.ext <| (mul_assoc _ _ _).trans (congrArg (γ' * ·) (inv_mul_cancel_left γ x))
    rw [borelValue_eq hχ (mul_mem hγ' (inv_mem hγ)) hb', borelValue_eq hχ hγ' hb, e]
  · have hγx : ¬∃ γ' ∈ Γ, γ' * (γ * x) ∈ B := fun ⟨γ', hγ', hb⟩ ↦
      hx ⟨γ' * γ, mul_mem hγ' hγ, by rwa [mul_assoc]⟩
    rw [borelValue, dite_eq_right hγx, borelValue, dite_eq_right hx]

lemma borelValue_mul_mem (hχ : ∀ b : B, (b : G) ∈ Γ → χ b = 1) (hx : ∃ γ ∈ Γ, γ * x ∈ B) (b : B) :
    borelValue Γ χ (x * b) = borelValue Γ χ x * χ b := by
  rcases hx with ⟨γ, hγ, hb⟩
  have hb' : γ * (x * b) ∈ B := by
    rw [← mul_assoc]
    exact mul_mem hb b.2
  rw [borelValue_eq hχ hγ hb', borelValue_eq hχ hγ hb, ← Units.val_mul, ← map_mul]
  exact congrArg _ (congrArg _ (Subtype.ext (mul_assoc _ _ _).symm))

attribute [local instance] Fintype.ofFinite

private lemma sum_borelValue_mul (hB : ∀ x ∈ Δ, ∃ γ ∈ Γ, γ * x ∈ B)
    (hχ : ∀ b : B, (b : G) ∈ Γ → χ b = 1) (D₁ D₂ : HeckeCoset Δ Γ Γ) :
    ∑ q : DecompQuotient Γ Γ (D₁.out : G)⁻¹ × DecompQuotient Γ Γ (D₂.out : G)⁻¹,
        borelValue Γ χ (rightCosetRep D₁ q.1 * rightCosetRep D₂ q.2) =
      rightCosetSum D₁ (borelValue Γ χ) * rightCosetSum D₂ (borelValue Γ χ) := by
  have hΔ (D : HeckeCoset Δ Γ Γ) (v : DecompQuotient Γ Γ (D.out : G)⁻¹) : rightCosetRep D v ∈ Δ :=
    rightCosetRep_mem D D.out.2 (IsHeckeTriple.right_le (H₁ := Γ)) v
  rw [Fintype.sum_prod_type_right, rightCosetSum, rightCosetSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ ↦ ?_
  rcases hB _ (hΔ D₂ w) with ⟨γ, hγ, hb⟩
  have key (v : DecompQuotient Γ Γ (D₁.out : G)⁻¹) :
      borelValue Γ χ (rightCosetRep D₁ v * rightCosetRep D₂ w) =
        borelValue Γ χ (rightCosetRep D₁ v * γ⁻¹) * χ ⟨_, hb⟩ := by
    rw [← borelValue_mul_mem hχ
      (hB _ (mul_mem (hΔ D₁ v) (IsHeckeTriple.mem_of_mem_left Γ (inv_mem hγ)))),
      Subgroup.coe_mk, mul_assoc, inv_mul_cancel_left]
  have hperm (v : DecompQuotient Γ Γ (D₁.out : G)⁻¹) : borelValue Γ χ (rightCosetRep D₁ v * γ⁻¹) =
      borelValue Γ χ (rightCosetRep D₁ ((⟨γ⁻¹, inv_mem hγ⟩ : Γ)⁻¹ • v)) := by
    rcases SiegelUpperHalfSpace.exists_mem_rightCosetRep_mul_eq_mul_rightCosetRep D₁ v
      (inv_mem hγ) with ⟨γ₁, hγ₁, h⟩
    rw [h, borelValue_mul_left hχ hγ₁]
  rw [Finset.sum_congr rfl fun v _ ↦ key v, ← Finset.sum_mul, borelValue_eq hχ hγ hb,
    Finset.sum_congr rfl fun v _ ↦ hperm v]
  exact congrArg (· * _) <|
    Fintype.sum_equiv (MulAction.toPerm (⟨γ⁻¹, inv_mem hγ⟩ : Γ)⁻¹) _ _ fun v ↦ rfl

variable (k : Type*) [CommRing k] [Algebra k R]

variable (χ) in
/-- The **spherical map** `ω_χ : 𝓗(Γ, Δ) → R` of a character `χ : B → Rˣ` trivial on `B ∩ Γ`, for a
subgroup `B` meeting every right coset `Γx`, `x ∈ Δ`: the ring homomorphism with
`ω_χ(ΓαΓ) = ∑_{Γx ⊆ ΓαΓ} χ(Γx)` (`HeckeCoset.sphericalMap_single`), on the Hecke ring with
coefficients in a commutative ring `k` over which `R` is an algebra. -/
noncomputable def sphericalMap (hB : ∀ x ∈ Δ, ∃ γ ∈ Γ, γ * x ∈ B)
    (hχ : ∀ b : B, (b : G) ∈ Γ → χ b = 1) : HeckeRing Δ Γ k →+* R where
  toFun := rightCosetSumLinear (borelValue Γ χ) k
  map_one' := by
    rcases (inferInstance : Nonempty (DecompQuotient Γ Γ ((1 : HeckeCoset Δ Γ Γ).out : G)⁻¹)) with
      ⟨v⟩
    have hB₁ : (rightCosetRep (1 : HeckeCoset Δ Γ Γ) v)⁻¹ * rightCosetRep 1 v ∈ B := by
      rw [inv_mul_cancel]
      exact one_mem B
    rw [HeckeCosetModule.one_def, rightCosetSumLinear_single, one_smul, rightCosetSum,
      Fintype.sum_subsingleton _ v, borelValue_eq hχ (inv_mem (rightCosetRep_one_mem v)) hB₁]
    exact congrArg Units.val ((congrArg χ (Subtype.ext (inv_mul_cancel _))).trans (map_one χ))
  map_mul' := (rightCosetSumLinear (borelValue Γ χ) k).map_mul_of_basis fun D₁ D₂ ↦ by
    rw [rightCosetSumLinear_single_mul_single D₁ D₂ _ k fun _ hγ _ ↦ borelValue_mul_left hχ hγ,
      sum_borelValue_mul hB hχ, rightCosetSumLinear_single, rightCosetSumLinear_single, one_smul,
      one_smul]
  map_zero' := map_zero _
  map_add' := map_add _

variable (χ) in
/-- **The spherical map on a double coset is the sum of the character over its right cosets**:
`ω_χ(ΓαΓ) = ∑_{Γx ⊆ ΓαΓ} χ(Γx)`, over the chosen representatives of the right cosets. -/
lemma sphericalMap_single (hB : ∀ x ∈ Δ, ∃ γ ∈ Γ, γ * x ∈ B) (hχ : ∀ b : B, (b : G) ∈ Γ → χ b = 1)
    (D : HeckeCoset Δ Γ Γ) (c : k) : sphericalMap χ k hB hχ (HeckeCosetModule.single k D c) =
      c • ∑ v : DecompQuotient Γ Γ (D.out : G)⁻¹, borelValue Γ χ (rightCosetRep D v) :=
  rightCosetSumLinear_single D _ k c

end HeckeCoset
