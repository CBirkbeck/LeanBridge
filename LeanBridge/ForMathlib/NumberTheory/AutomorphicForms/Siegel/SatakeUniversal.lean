import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.SatakeParameters

/-!
# The universal Satake map of `Sp(2g, ℤ)` at `p`

Let `L_g = ℂ[x₀^{±1}, x_0^{±1}, …, x_{g-1}^{±1}]` be the ring of Laurent polynomials, the monoid
algebra of the weights `(δ; d) ∈ ℤ × ℤ^g` (`SiegelUpperHalfSpace.SatakeLaurent`). The **universal
Satake map** `Ω : 𝓗_p → L_g` (`SiegelUpperHalfSpace.satakeMapUniv`) is the spherical map
(`HeckeCoset.sphericalMap`) of the universal unramified character
`b ↦ p^{-∑_j (g-j) d_j} x₀^δ ∏_j x_j^{d_j}` of the Borel subgroup, `(δ; d)` being the valuation of
`b`: `Ω(ΓαΓ) = ∑_{Γx ⊆ ΓαΓ} p^{-∑_j (g-j) d_j} x₀^δ ∏_j x_j^{d_j}` over the right cosets, a ring
homomorphism. Its value at a point `α = (α₀; α_0, …, α_{g-1})` of `(ℂˣ)^{g+1}` is the Satake map
`ω_α` (`SiegelUpperHalfSpace.satakeEval_satakeMapUniv`).

The Weyl group `W_g` of signed permutations acts on the weights: a permutation `σ` of the
coordinates by `(δ; d) ↦ (δ; d ∘ σ⁻¹)` (`SiegelUpperHalfSpace.weylPerm`) and the sign change at `j`
by `(δ; d) ↦ (δ; …, δ - d_j, …)` (`SiegelUpperHalfSpace.weylSign`). On points this is the action
`(α₀; α) ↦ (α₀; α ∘ σ)` and `(α₀; α) ↦ (α₀ α_j; …, α_j⁻¹, …)` under which the Euler factors are
invariant.

## Main definitions

* `SiegelUpperHalfSpace.SatakeWeight`, `SiegelUpperHalfSpace.SatakeLaurent`: the weights and the
  Laurent polynomials.
* `SiegelUpperHalfSpace.satakeEval`: the evaluation at a point of `(ℂˣ)^{g+1}`.
* `SiegelUpperHalfSpace.weylPerm`, `SiegelUpperHalfSpace.weylSign`: the Weyl group on the weights.
* `SiegelUpperHalfSpace.weylInvariants`: the subalgebra `L_g^{W_g}` of invariants.
* `SiegelUpperHalfSpace.borelRep`: a representative of a right coset in the Borel subgroup.
* `SiegelUpperHalfSpace.satakeCharacterUniv`: the universal unramified character.
* `SiegelUpperHalfSpace.satakeMapUniv`: the universal Satake map `Ω : 𝓗_p → L_g`.

## Main results

* `SiegelUpperHalfSpace.satakeEval_satakeMapUniv`: `Ω` evaluated at `α` is `ω_α`.
* `SiegelUpperHalfSpace.satakeMapUniv_single_one`: `Ω(ΓαΓ)` as a sum over the right cosets.
-/

open MonoidAlgebra DoubleCoset

open HeckeCosetModule (single)

namespace SiegelUpperHalfSpace

variable (n : ℕ)

/-- The **weights** `(δ; d_0, …, d_{g-1}) ∈ ℤ × ℤ^g` of the Satake map (LMFDB `mf.siegel.lift`,
through the Satake map), written multiplicatively: the exponents of the monomials
`x₀^δ ∏_j x_j^{d_j}`. -/
abbrev SatakeWeight : Type :=
  Multiplicative (ℤ × (Fin n → ℤ))

/-- The ring `L_g = ℂ[x₀^{±1}, x_0^{±1}, …, x_{g-1}^{±1}]` of **Laurent polynomials** in which the
universal Satake map takes its values (LMFDB `mf.siegel.lift`, through the Satake map): the monoid
algebra of the weights. -/
abbrev SatakeLaurent : Type :=
  MonoidAlgebra ℂ (SatakeWeight n)

variable {n} (α₀ : ℂˣ) (α : Fin n → ℂˣ) (m : SatakeWeight n)

/-- The **character of the weights** `(δ; d) ↦ α₀^δ ∏_j α_j^{d_j}` at a point `(α₀; α)` (LMFDB
`mf.siegel.lift`, through the Satake map). -/
def weightCharacter : SatakeWeight n →* ℂˣ where
  toFun m := α₀ ^ m.toAdd.1 * ∏ i, α i ^ m.toAdd.2 i
  map_one' := by simp
  map_mul' m m' := by
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, Pi.add_apply, zpow_add,
      Finset.prod_mul_distrib]
    exact mul_mul_mul_comm _ _ _ _

lemma weightCharacter_mul (β₀ : ℂˣ) (β : Fin n → ℂˣ) :
    weightCharacter (α₀ * β₀) (α * β) m = weightCharacter α₀ α m * weightCharacter β₀ β m := by
  simp only [weightCharacter, MonoidHom.coe_mk, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]
  exact mul_mul_mul_comm _ _ _ _

/-- The **evaluation** `L_g → ℂ` at a point `(α₀; α)` of `(ℂˣ)^{g+1}` (LMFDB `mf.siegel.lift`,
through the Satake map), sending `x₀^δ ∏_j x_j^{d_j}` to `α₀^δ ∏_j α_j^{d_j}`. -/
noncomputable def satakeEval : SatakeLaurent n →ₐ[ℂ] ℂ :=
  lift ℂ ℂ (SatakeWeight n) ((Units.coeHom ℂ).comp (weightCharacter α₀ α))

lemma satakeEval_single (c : ℂ) : satakeEval α₀ α (single m c) = c * weightCharacter α₀ α m := by
  rw [satakeEval, lift_single, smul_eq_mul]
  rfl

/-! ### The Weyl group on the weights -/

variable (σ : Equiv.Perm (Fin n)) (j : Fin n)

/-- The **permutation** `σ` of the coordinates acting on the weights (LMFDB `mf.siegel.lift`,
through the Weyl group): `(δ; d) ↦ (δ; d ∘ σ⁻¹)`. -/
def weylPerm : SatakeWeight n ≃* SatakeWeight n where
  toFun m := .ofAdd (m.toAdd.1, m.toAdd.2 ∘ σ.symm)
  invFun m := .ofAdd (m.toAdd.1, m.toAdd.2 ∘ σ)
  left_inv m := by simp [Function.comp_assoc]
  right_inv m := by simp [Function.comp_assoc]
  map_mul' _ _ := rfl

/-- The **sign change** at `j` acting on the weights (LMFDB `mf.siegel.lift`, through the Weyl
group): `(δ; d) ↦ (δ; …, δ - d_j, …)`, dual to `(α₀; α) ↦ (α₀ α_j; …, α_j⁻¹, …)`. -/
def weylSign : SatakeWeight n ≃* SatakeWeight n where
  toFun m := .ofAdd (m.toAdd.1, Function.update m.toAdd.2 j (m.toAdd.1 - m.toAdd.2 j))
  invFun m := .ofAdd (m.toAdd.1, Function.update m.toAdd.2 j (m.toAdd.1 - m.toAdd.2 j))
  left_inv m := by simp
  right_inv m := by simp
  map_mul' m m' := by
    refine congrArg Multiplicative.ofAdd (Prod.ext rfl (funext fun i ↦ ?_))
    rcases eq_or_ne i j with rfl | hi
    · simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, Pi.add_apply, toAdd_ofAdd,
        Function.update_self]
      ring1
    · simp [Function.update_of_ne hi]

lemma satakeEval_weylPerm (f : SatakeLaurent n) :
    satakeEval α₀ α (domCongr ℂ ℂ (weylPerm σ) f) = satakeEval α₀ (α ∘ σ) f := by
  induction f using MonoidAlgebra.induction_on with
  | of m =>
    rw [of_apply, domCongr_single, satakeEval_single, satakeEval_single, one_mul, one_mul]
    simp only [weightCharacter, weylPerm, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk,
      Equiv.coe_fn_mk, toAdd_ofAdd]
    rw [← Equiv.prod_comp σ fun i ↦ α i ^ (m.toAdd.2 ∘ σ.symm) i]
    simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add]
  | smul c f hf => rw [map_smul, map_smul, hf, map_smul]

lemma satakeEval_weylSign (f : SatakeLaurent n) :
    satakeEval α₀ α (domCongr ℂ ℂ (weylSign j) f) =
      satakeEval (α₀ * α j) (Function.update α j (α j)⁻¹) f := by
  induction f using MonoidAlgebra.induction_on with
  | of m =>
    rw [of_apply, domCongr_single, satakeEval_single, satakeEval_single, one_mul, one_mul]
    have h₁ : ∏ i, α i ^ Function.update m.toAdd.2 j (m.toAdd.1 - m.toAdd.2 j) i =
        α j ^ (m.toAdd.1 - m.toAdd.2 j) * ∏ i ∈ Finset.univ.erase j, α i ^ m.toAdd.2 i := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Function.update_self]
      exact congrArg _ (Finset.prod_congr rfl fun i hi ↦ by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])
    have h₂ : ∏ i, Function.update α j (α j)⁻¹ i ^ m.toAdd.2 i =
        (α j)⁻¹ ^ m.toAdd.2 j * ∏ i ∈ Finset.univ.erase j, α i ^ m.toAdd.2 i := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Function.update_self]
      exact congrArg _ (Finset.prod_congr rfl fun i hi ↦ by
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)])
    refine congrArg Units.val ?_
    simp only [weightCharacter, weylSign, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk,
      Equiv.coe_fn_mk, toAdd_ofAdd, h₁, h₂, mul_zpow, inv_zpow, zpow_sub, mul_assoc]
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add]
  | smul c f hf => rw [map_smul, map_smul, hf, map_smul]

variable (n) in
/-- The subalgebra `L_g^{W_g}` of the **Weyl-invariant** Laurent polynomials (LMFDB
`mf.siegel.lift`, through the Satake map): those fixed by every permutation
(`SiegelUpperHalfSpace.weylPerm`) and every sign change (`SiegelUpperHalfSpace.weylSign`) of the
coordinates. -/
noncomputable def weylInvariants : Subalgebra ℂ (SatakeLaurent n) :=
  (⨅ σ, AlgHom.equalizer (domCongr ℂ ℂ (weylPerm σ)).toAlgHom (AlgHom.id ℂ _)) ⊓
    ⨅ j, AlgHom.equalizer (domCongr ℂ ℂ (weylSign j)).toAlgHom (AlgHom.id ℂ _)

variable {f : SatakeLaurent n}

lemma mem_weylInvariants (hσ : ∀ σ, domCongr ℂ ℂ (weylPerm σ) f = f)
    (hj : ∀ j, domCongr ℂ ℂ (weylSign j) f = f) : f ∈ weylInvariants n :=
  Algebra.mem_inf.mpr ⟨Algebra.mem_iInf.mpr hσ, Algebra.mem_iInf.mpr hj⟩

lemma domCongr_weylPerm_of_mem (hf : f ∈ weylInvariants n) : domCongr ℂ ℂ (weylPerm σ) f = f :=
  Algebra.mem_iInf.mp (Algebra.mem_inf.mp hf).1 σ

lemma domCongr_weylSign_of_mem (hf : f ∈ weylInvariants n) : domCongr ℂ ℂ (weylSign j) f = f :=
  Algebra.mem_iInf.mp (Algebra.mem_inf.mp hf).2 j

/-! ### Representatives in the Borel subgroup -/

variable {x : GL (Fin n ⊕ Fin n) ℚ} (p : ℕ)

attribute [local instance] Fintype.ofFinite

lemma rightCosetRep_mem_gspPlusGL
    (D : HeckeCoset (heckeMonoidAt (Fin n) p) (heckeGamma (Fin n)) (heckeGamma (Fin n)))
    (v : DecompQuotient (heckeGamma (Fin n)) (heckeGamma (Fin n))
      (D.out : GL (Fin n ⊕ Fin n) ℚ)⁻¹) : rightCosetRep D v ∈ gspPlusGL (Fin n) :=
  heckeMonoid_le_gspPlusGL <| heckeMonoidAt_le_heckeMonoid p <|
    rightCosetRep_mem D D.out.2 (IsHeckeTriple.right_le (H₁ := heckeGamma (Fin n))) v

/-- A **representative in the Borel subgroup** `γ x`, `γ ∈ Sp(2g, ℤ)`, of the right coset `Γ x`
of `x ∈ GSp(2g, ℚ)⁺` (LMFDB `mf.siegel.lift`, through the Satake map;
`SiegelUpperHalfSpace.exists_mem_heckeGamma_mul_mem_siegelBorel`). -/
noncomputable def borelRep (hx : x ∈ gspPlusGL (Fin n)) : siegelBorel n :=
  ⟨_, (exists_mem_heckeGamma_mul_mem_siegelBorel hx).choose_spec.2⟩

lemma exists_borelRep_eq (hx : x ∈ gspPlusGL (Fin n)) :
    ∃ γ ∈ heckeGamma (Fin n), (borelRep hx : GL (Fin n ⊕ Fin n) ℚ) = γ * x :=
  ⟨_, (exists_mem_heckeGamma_mul_mem_siegelBorel hx).choose_spec.1, rfl⟩

lemma borelValue_eq_borelRep {R : Type*} [CommRing R] {χ : siegelBorel n →* Rˣ}
    (hχ : ∀ b : siegelBorel n, (b : GL (Fin n ⊕ Fin n) ℚ) ∈ heckeGamma (Fin n) → χ b = 1)
    (hx : x ∈ gspPlusGL (Fin n)) :
    HeckeCoset.borelValue (heckeGamma (Fin n)) χ x = χ (borelRep hx) :=
  HeckeCoset.borelValue_eq hχ (exists_mem_heckeGamma_mul_mem_siegelBorel hx).choose_spec.1 _

/-! ### The universal Satake map -/

variable [Fact p.Prime]

/-- The **universal unramified character** `(δ; d) ↦ p^{-∑_j (g-j) d_j} x₀^δ ∏_j x_j^{d_j}` of the
weights (LMFDB `mf.siegel.lift`, through the Satake map), with values in the units of `L_g`; its
value at a point `(α₀; α)` is `SiegelUpperHalfSpace.satakeCharacter`. -/
noncomputable def satakeCharacterUniv : SatakeWeight n →* (SatakeLaurent n)ˣ :=
  (Units.map (algebraMap ℂ (SatakeLaurent n)).toMonoidHom).comp
      (weightCharacter 1 fun i ↦ (primeUnit p)⁻¹ ^ (n - (i : ℕ))) *
    (Units.map (of ℂ (SatakeWeight n))).comp toUnits.toMonoidHom

lemma coe_satakeCharacterUniv : (satakeCharacterUniv p m : SatakeLaurent n) =
    single m (weightCharacter 1 (fun i ↦ (primeUnit p)⁻¹ ^ (n - (i : ℕ))) m : ℂ) := by
  simp [satakeCharacterUniv]

lemma satakeEval_satakeCharacterUniv :
    satakeEval α₀ α (satakeCharacterUniv p m) = satakeCharacter p α₀ α m := by
  rw [coe_satakeCharacterUniv, satakeEval_single, ← Units.val_mul, ← weightCharacter_mul, one_mul,
    mul_comm]
  rfl

variable [NeZero n]

/-- The **universal Satake map** `Ω : 𝓗_p → L_g` (LMFDB `mf.siegel.lift`, through the Satake map)
of the local Hecke algebra of `Sp(2g, ℤ)` at `p`: the ring homomorphism with
`Ω(ΓαΓ) = ∑_{Γx ⊆ ΓαΓ} p^{-∑_j (g-j) d_j} x₀^δ ∏_j x_j^{d_j}` over the right cosets, `(δ; d)` being
the valuation of the representative of `Γx` in the Borel subgroup. -/
noncomputable def satakeMapUniv : localSiegelHeckeRing (Fin n) p →+* SatakeLaurent n :=
  HeckeCoset.sphericalMap ((satakeCharacterUniv p).comp (satakeValuation p)) ℂ
    (fun _ hx ↦ exists_mem_heckeGamma_mul_mem_siegelBorel
      (heckeMonoid_le_gspPlusGL (heckeMonoidAt_le_heckeMonoid p hx)))
    fun _ hb ↦ by rw [MonoidHom.comp_apply, satakeValuation_eq_one p hb, map_one]

/-- **The universal Satake map evaluated at a point is the Satake map**: `Ω(T)(α) = ω_α(T)` for
every `T ∈ 𝓗_p` and every `α ∈ (ℂˣ)^{g+1}`. -/
lemma satakeEval_satakeMapUniv (T : localSiegelHeckeRing (Fin n) p) :
    satakeEval α₀ α (satakeMapUniv p T) = satakeMap p α₀ α T := by
  induction T using HeckeCosetModule.induction_linear with
  | h0 => rw [map_zero, map_zero, map_zero]
  | hadd T₁ T₂ h₁ h₂ => rw [map_add, map_add, map_add, h₁, h₂]
  | hsingle D c =>
    rw [satakeMapUniv, HeckeCoset.sphericalMap_single, satakeMap_single, map_smul, map_sum]
    refine congrArg (c • ·) (Finset.sum_congr rfl fun v _ ↦ ?_)
    simp only [HeckeCoset.borelValue]
    split_ifs
    · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, satakeEval_satakeCharacterUniv]
    · rw [map_zero]

/-- **The universal Satake map of a double coset as a sum over its right cosets**:
`Ω(ΓαΓ) = ∑_v χ(b_v)`, `b_v` being the representative in the Borel subgroup of the `v`-th right
coset and `χ` the universal unramified character. -/
lemma satakeMapUniv_single_one
    (D : HeckeCoset (heckeMonoidAt (Fin n) p) (heckeGamma (Fin n)) (heckeGamma (Fin n))) :
    satakeMapUniv p (single ℂ D 1) = ∑ v, (satakeCharacterUniv p (satakeValuation p
      (borelRep (rightCosetRep_mem_gspPlusGL p D v))) : SatakeLaurent n) := by
  rw [satakeMapUniv, HeckeCoset.sphericalMap_single, one_smul]
  refine Finset.sum_congr rfl fun v _ ↦ ?_
  rw [borelValue_eq_borelRep (fun b hb ↦ by
    rw [MonoidHom.comp_apply, satakeValuation_eq_one p hb, map_one])
    (rightCosetRep_mem_gspPlusGL p D v)]
  rfl

end SiegelUpperHalfSpace
