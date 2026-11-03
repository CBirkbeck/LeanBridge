import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.DoubleCosetLevelGroup

/-!
# The full level `N` Shimura curve and the quotient by `H`

The LMFDB (knowl `shimcurve`) forms the double coset space
`X(O;N)^big(ℂ) = B^× \ (ℋ^± × B̂^×) / Γ(Ô, N)`, for `Γ(Ô, N) = ker(Ô^× → (O/NO)^×)`, the complex
points of the full level `N` Shimura curve, on which a subgroup `H` of level `N` of the enhanced
group `Aut_{±μ}(O) ⋉ Ô^×` acts, and the Shimura curve `X_H` is the coarse space of the quotient
stack `[H \ X(O;N)^big]`, whose complex points are `H \ X(O;N)^big(ℂ)`. The action is not spelled
out by the knowl: an element `h` acts on `X(O;N)^big(ℂ)` by right translation
`[z, b] ↦ [z, b y⁻¹]` by any lift `y ∈ B̂^×` of its image `f(h) ∈ B̂^× / ℚ^×` under the homomorphism
`f : Aut_{±μ}(O) ⋉ Ô^× → B̂^× / ℚ^×`, `(w, x) ↦ w x`, of
`LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.AdelicEllipticPoint`. It is well defined, since `y`
normalizes `Γ(Ô, N)` and `ℚ^× ⊆ B^×` acts trivially on `ℋ^±`.

This file constructs this action and proves `H \ X(O;N)^big(ℂ) ≃ B^× \ (ℋ^± × B̂^×) / K_H` for the
inverse image `K_H ⊆ B̂^×` of `f(H)`, when `H` contains the kernel of `Ô^× → (O/NO)^×`. Together
with `LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.DoubleCosetLevelGroup`, this identifies the
model `B^×_+ \ (ℍ × B̂^×) / K_H` of `X_H(ℂ)` with the knowl's, so that the elliptic points
`Subalgebra.shimuraCurveEllipticPoints` are those of the Shimura curve of the knowl.

The algebraic curves over `ℚ` of Shimura and Deligne, the quotient stack and its coarse space are
not formalised: the orbits `H \ X(O;N)^big(ℂ)` are taken as the definition of `X_H(ℂ)`. The
stabilizer group of a point `[z, b]` is the stabilizer of `(z, b)` in `B^× × K_H` modulo the
rational scalars, which act trivially, that is, the stabilizer of `z` in the group of the component
through `[z, b]` acting on `ℋ^±`, of order `1`, `2`, `3`, `4` or `6`. It does not depend on `N`.
The stabilizer in `H` of the class of `[z, b]` in `X(O;N)^big(ℂ)` is not used: modulo the kernel of
the action it is this group for `N ≥ 3` (not proved here), but not for `N ≤ 2`, where `Γ(Ô, N)` has
fixed points; for instance `H = Ô^×`, of level `1`, acts trivially on `X(O;1)^big(ℂ)`.

## Main definitions

* `Subalgebra.fullLevelGroup` (LMFDB `shimcurve`): the group `Γ(Ô, N) ⊆ B̂^×`.
* `Subalgebra.FullLevelPoints` (LMFDB `shimcurve`): the space `X(O;N)^big(ℂ)`.
* The instance `MulAction (Subgroup.normalizer K) (ShimuraDoubleCoset hO ι K)`: right translation by
  the normalizer of `K` in `B̂^×`.
* `Subalgebra.doubleCosetMap`: the map of double coset spaces of an inclusion `K₀ ⊆ K`.
* `Subalgebra.enhancedGroupLift`: the lift to the normalizer of `Γ(Ô, N)` of the image of an element
  of the enhanced group.
* The instance `MulAction (O.EnhancedGroup μ) (FullLevelPoints hO ι N)`: the action of the enhanced
  group on `X(O;N)^big(ℂ)`: `h` acts by the right translation `[z, b] ↦ [z, b y⁻¹]` by any lift
  `y ∈ B̂^×` of its image `f(h) ∈ B̂^× / ℚ^×`.
* `Subalgebra.ShimuraCurveOrbits` (LMFDB `shimcurve`): the complex points `H \ X(O;N)^big(ℂ)` of
  `X_H`.
* `Subalgebra.shimuraCurveOrbitsToDoubleCoset`: the map
  `H \ X(O;N)^big(ℂ) → B^× \ (ℋ^± × B̂^×) / K_H`.
* `Subalgebra.shimuraCurveOrbitsEquivDoubleCoset` (LMFDB `shimcurve`): the bijection
  `H \ X(O;N)^big(ℂ) ≃ B^× \ (ℋ^± × B̂^×) / K_H`.
* `Subalgebra.shimuraCurvePointsEquivOrbits` (LMFDB `shimcurve`): the bijection
  `B^×_+ \ (ℍ × B̂^×) / K_H ≃ H \ X(O;N)^big(ℂ)`.
* `Subalgebra.shimuraCurveOrbitsEllipticPoints` (LMFDB `shimcurve.elliptic_points`): the elliptic
  points of `H \ X(O;N)^big(ℂ)`.

## Main results

* `Subalgebra.normalizer_smul_eq_self`: the elements of `ℚ^×` act trivially by right translation.
* `Subalgebra.mem_normalizer_fullLevelGroup`: a lift of `f(h)` normalizes `Γ(Ô, N)`.
* `Subalgebra.fullLevelGroup_le_shimuraLevelGroup`: `Γ(Ô, N) ⊆ K_H` when `H` contains the kernel of
  `Ô^× → (O/NO)^×`.
* `Subalgebra.quotientMk_mem_shimuraCurveOrbitsEllipticPoints_iff` (LMFDB
  `shimcurve.elliptic_points`): the point `[z, b]` of `H \ X(O;N)^big(ℂ)` is elliptic exactly when
  the stabilizer of `(z, b)` in `B^× × K_H`, modulo the rational scalars, is nontrivial.
* `Subalgebra.shimuraCurvePointsEquivOrbits_mem_iff` (LMFDB `shimcurve.elliptic_points`): the
  elliptic points of `H \ X(O;N)^big(ℂ)` are those of `Subalgebra.shimuraCurveEllipticPoints`.
-/

open Module MulAction UpperHalfPlane

open Matrix hiding mul_smul mul_inv_rev

namespace Subalgebra

variable {B : Type*} [Ring B] [Algebra ℚ B] {O : Subalgebra ℤ B} (hO : O.IsQuaternionOrder)
  (ι : B →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ)

section Translation

variable (K : Subgroup O.FiniteAdelicAlgebraˣ)
  (y y' : Subgroup.normalizer (K : Set O.FiniteAdelicAlgebraˣ)) (x : ShimuraDoubleCoset hO ι K)

noncomputable instance :
    SMul (Subgroup.normalizer (K : Set O.FiniteAdelicAlgebraˣ)) (ShimuraDoubleCoset hO ι K) where
  smul y := Quotient.map' (fun p ↦ (p.1, p.2 * (y : O.FiniteAdelicAlgebraˣ)⁻¹)) fun _ q ⟨g, hg⟩ ↦ by
    subst hg
    rcases g with ⟨_, ⟨β, k⟩, ⟨_, hk⟩, rfl⟩
    refine ⟨shimuraActing hO ι β ((Subgroup.mem_normalizer_iff.mp y.2 k).mp hk), Prod.ext rfl ?_⟩
    show Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom β *
      (q.2 * (y : O.FiniteAdelicAlgebraˣ)⁻¹) *
        ((y : O.FiniteAdelicAlgebraˣ) * k * (y : O.FiniteAdelicAlgebraˣ)⁻¹)⁻¹ =
      Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom β * q.2 * k⁻¹ *
        (y : O.FiniteAdelicAlgebraˣ)⁻¹
    group

lemma normalizer_smul_mk (p : UpperLowerHalfPlane × O.FiniteAdelicAlgebraˣ) :
    y • (Quotient.mk _ p : ShimuraDoubleCoset hO ι K) =
      Quotient.mk _ (p.1, p.2 * (y : O.FiniteAdelicAlgebraˣ)⁻¹) :=
  rfl

noncomputable instance :
    MulAction (Subgroup.normalizer (K : Set O.FiniteAdelicAlgebraˣ))
      (ShimuraDoubleCoset hO ι K) where
  one_smul x := by
    induction x using Quotient.inductionOn with | h p => ?_
    rw [normalizer_smul_mk]
    exact congrArg (Quotient.mk _) (Prod.ext rfl (by simp))
  mul_smul y y' x := by
    induction x using Quotient.inductionOn with | h p => ?_
    rw [normalizer_smul_mk, normalizer_smul_mk, normalizer_smul_mk]
    exact congrArg (Quotient.mk _) (Prod.ext rfl (by simp [mul_assoc]))

variable {K y} in
/-- **The elements of `ℚ^×` act trivially by right translation on `B^× \ (ℋ^± × B̂^×) / K`**: they
lie in `B^×`, are central in `B̂^×`, and act trivially on `ℋ^±`. -/
lemma normalizer_smul_eq_self {q : ℚˣ} (hy : (y : O.FiniteAdelicAlgebraˣ) =
    Units.map ((O.toFiniteAdelicAlgebra hO).comp (algebraMap ℚ B)).toMonoidHom q) : y • x = x := by
  induction x using Quotient.inductionOn with | h p => ?_
  rw [normalizer_smul_mk]
  refine Quotient.sound ⟨shimuraActing hO ι (Units.map (algebraMap ℚ B : ℚ →* B) q)⁻¹ (one_mem K),
    Prod.ext (algebraMap_inv_smul ι q p.1) ?_⟩
  have hc : Commute (Units.map ((O.toFiniteAdelicAlgebra hO).comp (algebraMap ℚ B)).toMonoidHom q)
      p.2 := Units.ext (commute_toFiniteAdelicAlgebra_algebraMap hO q _)
  show (Units.map ((O.toFiniteAdelicAlgebra hO).comp (algebraMap ℚ B)).toMonoidHom q)⁻¹ * p.2 *
    1⁻¹ = p.2 * (y : O.FiniteAdelicAlgebraˣ)⁻¹
  rw [inv_one, mul_one, hy, hc.inv_left.eq]

/-- The map `B^× \ (ℋ^± × B̂^×) / K₀ → B^× \ (ℋ^± × B̂^×) / K` for subgroups `K₀ ⊆ K` of `B̂^×`. -/
noncomputable def doubleCosetMap {K₀ : Subgroup O.FiniteAdelicAlgebraˣ} (hK : K₀ ≤ K) :
    ShimuraDoubleCoset hO ι K₀ → ShimuraDoubleCoset hO ι K :=
  Quotient.map' id fun _ q ⟨g, hg⟩ ↦ by
    subst hg
    rcases g with ⟨_, ⟨β, k⟩, ⟨_, hk⟩, rfl⟩
    exact ⟨shimuraActing hO ι β (hK hk), rfl⟩

end Translation

variable (O) in
/-- The group **`Γ(Ô, N) = ker(Ô^× → (O/NO)^×)`** (LMFDB `shimcurve`), as a subgroup of `B̂^×`. -/
noncomputable def fullLevelGroup (N : ℕ+) : Subgroup O.FiniteAdelicAlgebraˣ :=
  (O.completedUnitsReduction N).ker.map O.completedUnitsToUnits

variable (N : ℕ+) (μ : B)

lemma completedUnitsAction_mem_ker (w : O.autPmMu μ) {c : O.completedUnits}
    (hc : c ∈ (O.completedUnitsReduction N).ker) :
    O.completedUnitsAction μ w c ∈ (O.completedUnitsReduction N).ker := by
  have h : O.completedUnitsReduction N (O.completedUnitsAction μ w c) =
      O.autPmMuQuotientUnitsAction N μ w (O.completedUnitsReduction N c) :=
    rfl
  rw [MonoidHom.mem_ker, h, MonoidHom.mem_ker.mp hc, map_one]

lemma conj_mem_fullLevelGroup {y : O.FiniteAdelicAlgebraˣ} {h : O.EnhancedGroup μ}
    (hy : (QuotientGroup.mk y : O.FiniteAdelicAlgebraˣ ⧸ finiteAdelicRatUnits hO) =
      enhancedGroupToFiniteAdelic hO μ h) {c : O.FiniteAdelicAlgebraˣ}
    (hc : c ∈ O.fullLevelGroup N) : y * c * y⁻¹ ∈ O.fullLevelGroup N := by
  rcases h with ⟨x, w, hw⟩
  rcases QuotientGroup.mk_surjective w with ⟨γ, rfl⟩
  rcases hc with ⟨c', hc', rfl⟩
  have hf : enhancedGroupToFiniteAdelic hO μ ⟨x, ⟨_, hw⟩⟩ = QuotientGroup.mk
      (O.completedUnitsToUnits x * Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom (γ : Bˣ)) :=
    rfl
  rw [hf] at hy
  rcases QuotientGroup.eq.mp hy with ⟨q, hq⟩
  have hy' : y = O.completedUnitsToUnits x * Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom
      (γ : Bˣ) *
        (Units.map ((O.toFiniteAdelicAlgebra hO).comp (algebraMap ℚ B)).toMonoidHom q)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, hq, mul_inv_cancel_left]
  have hcq₀ : Commute (Units.map ((O.toFiniteAdelicAlgebra hO).comp (algebraMap ℚ B)).toMonoidHom q)
      (O.completedUnitsToUnits c') :=
    Units.ext (commute_toFiniteAdelicAlgebra_algebraMap hO q _)
  have hcq : Commute (Units.map ((O.toFiniteAdelicAlgebra hO).comp
      (algebraMap ℚ B)).toMonoidHom q)⁻¹ (O.completedUnitsToUnits c') :=
    hcq₀.inv_left
  refine ⟨x * O.completedUnitsAction μ ⟨_, hw⟩ c' * x⁻¹, (MonoidHom.normal_ker _).conj_mem _
    (completedUnitsAction_mem_ker N μ ⟨_, hw⟩ hc') x, ?_⟩
  rw [map_mul, map_mul, map_inv, completedUnitsToUnits_completedUnitsAction hO μ γ hw, hy',
    mul_assoc (O.completedUnitsToUnits x * _), hcq.eq]
  group

/-- **A lift `y ∈ B̂^×` of the image `f(h) ∈ B̂^× / ℚ^×` of an element of the enhanced group
normalizes `Γ(Ô, N)`**: `y = x γ q` with `x ∈ Ô^×`, `γ ∈ N_{B^×}(O)`, `q ∈ ℚ^×`, and `Γ(Ô, N)` is
normal in `Ô^×`, conjugation by `γ` is compatible with the reductions modulo `N`, and `q` is
central. -/
lemma mem_normalizer_fullLevelGroup {y : O.FiniteAdelicAlgebraˣ} {h : O.EnhancedGroup μ}
    (hy : (QuotientGroup.mk y : O.FiniteAdelicAlgebraˣ ⧸ finiteAdelicRatUnits hO) =
      enhancedGroupToFiniteAdelic hO μ h) :
    y ∈ Subgroup.normalizer (O.fullLevelGroup N : Set O.FiniteAdelicAlgebraˣ) :=
  Subgroup.mem_normalizer_iff.mpr fun c ↦ ⟨conj_mem_fullLevelGroup hO N μ hy, fun hc ↦ by
    have hc' : y⁻¹ * (y * c * y⁻¹) * y⁻¹⁻¹ ∈ O.fullLevelGroup N :=
      conj_mem_fullLevelGroup hO N μ (h := h⁻¹) (by
        rw [QuotientGroup.mk_inv, map_inv, hy]) hc
    simpa [mul_assoc] using hc'⟩

variable (H : Subgroup (O.EnhancedGroup μ))

variable {N μ H} in
/-- **`Γ(Ô, N) ⊆ K_H`** when `H` contains the kernel of `Ô^× → (O/NO)^×`, as a subgroup of level
dividing `N` does. -/
lemma fullLevelGroup_le_shimuraLevelGroup (hH : O.enhancedGroupKernel μ N ≤ H) :
    O.fullLevelGroup N ≤ shimuraLevelGroup hO μ H := by
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨SemidirectProduct.inl c, hH ⟨c, hc, rfl⟩, SemidirectProduct.lift_inl ..⟩

/-- The space **`X(O;N)^big(ℂ) = B^× \ (ℋ^± × B̂^×) / Γ(Ô, N)`** (LMFDB `shimcurve`) of the complex
points of the full level `N` Shimura curve associated to `O`. -/
abbrev FullLevelPoints : Type _ :=
  ShimuraDoubleCoset hO ι (O.fullLevelGroup N)

/-- The lift to the normalizer of `Γ(Ô, N)` of the image `f(h) ∈ B̂^× / ℚ^×` of an element `h` of
the enhanced group. -/
noncomputable def enhancedGroupLift (h : O.EnhancedGroup μ) :
    Subgroup.normalizer (O.fullLevelGroup N : Set O.FiniteAdelicAlgebraˣ) :=
  ⟨(enhancedGroupToFiniteAdelic hO μ h).out,
    mem_normalizer_fullLevelGroup hO N μ (QuotientGroup.out_eq' _)⟩

variable {N μ} in
lemma enhancedGroupLift_smul_eq {h : O.EnhancedGroup μ}
    {y : Subgroup.normalizer (O.fullLevelGroup N : Set O.FiniteAdelicAlgebraˣ)}
    (hy : (QuotientGroup.mk (y : O.FiniteAdelicAlgebraˣ) :
      O.FiniteAdelicAlgebraˣ ⧸ finiteAdelicRatUnits hO) = enhancedGroupToFiniteAdelic hO μ h)
    (x : FullLevelPoints hO ι N) : enhancedGroupLift hO N μ h • x = y • x := by
  have h₁ : (QuotientGroup.mk (enhancedGroupLift hO N μ h : O.FiniteAdelicAlgebraˣ) :
      O.FiniteAdelicAlgebraˣ ⧸ finiteAdelicRatUnits hO) =
        QuotientGroup.mk (y : O.FiniteAdelicAlgebraˣ) :=
    (QuotientGroup.out_eq' _).trans hy.symm
  rcases QuotientGroup.eq.mp h₁ with ⟨q, hq⟩
  have h₂ : y = enhancedGroupLift hO N μ h * ((enhancedGroupLift hO N μ h)⁻¹ * y) :=
    (mul_inv_cancel_left _ _).symm
  rw [h₂, mul_smul, normalizer_smul_eq_self hO ι x (y := (enhancedGroupLift hO N μ h)⁻¹ * y)
    (q := q) hq.symm]

noncomputable instance : MulAction (O.EnhancedGroup μ) (FullLevelPoints hO ι N) where
  smul h x := enhancedGroupLift hO N μ h • x
  one_smul x := (enhancedGroupLift_smul_eq hO ι (y := 1) (map_one _).symm x).trans (one_smul _ x)
  mul_smul h h' x := by
    have h₁ : enhancedGroupLift hO N μ (h * h') • x = (enhancedGroupLift hO N μ h *
        enhancedGroupLift hO N μ h') • x :=
      enhancedGroupLift_smul_eq hO ι (by
        rw [map_mul, Subgroup.coe_mul, QuotientGroup.mk_mul]
        exact congrArg₂ (· * ·) (QuotientGroup.out_eq' _) (QuotientGroup.out_eq' _)) x
    exact h₁.trans (mul_smul _ _ x)

/-- The **complex points `H \ X(O;N)^big(ℂ)` of the Shimura curve `X_H`** (LMFDB `shimcurve`), the
orbits of `H` on `X(O;N)^big(ℂ)`. -/
abbrev ShimuraCurveOrbits : Type _ :=
  orbitRel.Quotient H (FullLevelPoints hO ι N)

variable {N μ H} (hH : O.enhancedGroupKernel μ N ≤ H)

private lemma doubleCosetMap_smul (h : H) (x : FullLevelPoints hO ι N) :
    doubleCosetMap hO ι _ (fullLevelGroup_le_shimuraLevelGroup hO hH) (h • x) =
      doubleCosetMap hO ι _ (fullLevelGroup_le_shimuraLevelGroup hO hH) x := by
  induction x using Quotient.inductionOn with | h p => ?_
  have hy : ((enhancedGroupLift hO N μ (h : O.EnhancedGroup μ)) : O.FiniteAdelicAlgebraˣ) ∈
      shimuraLevelGroup hO μ H :=
    ⟨h, h.2, (QuotientGroup.out_eq' _).symm⟩
  refine Quotient.sound ⟨shimuraActing hO ι 1 hy, Prod.ext
    ((congrArg (· • p.1) (map_one (Units.map ι.toMonoidHom))).trans (one_smul _ _)) ?_⟩
  show Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom 1 * p.2 *
    ((enhancedGroupLift hO N μ (h : O.EnhancedGroup μ)) : O.FiniteAdelicAlgebraˣ)⁻¹ =
      p.2 * ((enhancedGroupLift hO N μ (h : O.EnhancedGroup μ)) : O.FiniteAdelicAlgebraˣ)⁻¹
  rw [map_one, one_mul]

/-- The map `H \ X(O;N)^big(ℂ) → B^× \ (ℋ^± × B̂^×) / K_H`, `[z, b] ↦ [z, b]`. -/
noncomputable def shimuraCurveOrbitsToDoubleCoset :
    ShimuraCurveOrbits hO ι N μ H → ShimuraDoubleCoset hO ι (shimuraLevelGroup hO μ H) :=
  Quotient.lift (doubleCosetMap hO ι _ (fullLevelGroup_le_shimuraLevelGroup hO hH))
    fun _ x ⟨h, hx⟩ ↦ hx ▸ doubleCosetMap_smul hO ι hH h x

private lemma shimuraCurveOrbitsToDoubleCoset_surjective :
    Function.Surjective (shimuraCurveOrbitsToDoubleCoset hO ι hH) := by
  intro x
  induction x using Quotient.inductionOn with | h p => ?_
  exact ⟨Quotient.mk _ (Quotient.mk _ p), rfl⟩

private lemma shimuraCurveOrbitsToDoubleCoset_injective :
    Function.Injective (shimuraCurveOrbitsToDoubleCoset hO ι hH) := by
  intro x x' hxx
  induction x using Quotient.inductionOn with | h x => ?_
  induction x' using Quotient.inductionOn with | h x' => ?_
  induction x using Quotient.inductionOn with | h p => ?_
  induction x' using Quotient.inductionOn with | h p' => ?_
  rcases Quotient.exact hxx with ⟨g, hg⟩
  rcases g with ⟨_, ⟨β, k⟩, ⟨_, hk⟩, rfl⟩
  rcases hk with ⟨h, hh, hkh⟩
  let y : Subgroup.normalizer (O.fullLevelGroup N : Set O.FiniteAdelicAlgebraˣ) :=
    ⟨k, mem_normalizer_fullLevelGroup hO N μ hkh.symm⟩
  have h₁ : (⟨h, hh⟩ : H) • (Quotient.mk _ p' : FullLevelPoints hO ι N) =
      Quotient.mk _ (p'.1, p'.2 * k⁻¹) :=
    enhancedGroupLift_smul_eq hO ι (y := y) hkh.symm _
  have h₂ : Units.map ι.toMonoidHom β • p'.1 = p.1 :=
    congrArg Prod.fst hg
  have h₃ : Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom β * p'.2 * k⁻¹ = p.2 :=
    congrArg Prod.snd hg
  refine Quotient.sound ⟨⟨h, hh⟩, h₁.trans (Quotient.sound ⟨shimuraActing hO ι β⁻¹ (one_mem _),
    Prod.ext ?_ ?_⟩)⟩
  · show Units.map ι.toMonoidHom β⁻¹ • p.1 = p'.1
    rw [← h₂, map_inv, inv_smul_smul]
  · show Units.map (O.toFiniteAdelicAlgebra hO).toMonoidHom β⁻¹ * p.2 * 1⁻¹ = p'.2 * k⁻¹
    rw [← h₃, map_inv]
    group

/-- **The complex points `H \ X(O;N)^big(ℂ)` of `X_H` are the double coset space of `K_H`**: the map
`[z, b] ↦ [z, b]` is a bijection `H \ X(O;N)^big(ℂ) ≃ B^× \ (ℋ^± × B̂^×) / K_H` (LMFDB `shimcurve`),
for a subgroup `H` of the enhanced group containing the kernel of `Ô^× → (O/NO)^×`, as a subgroup of
level dividing `N` does. -/
noncomputable def shimuraCurveOrbitsEquivDoubleCoset :
    ShimuraCurveOrbits hO ι N μ H ≃ ShimuraDoubleCoset hO ι (shimuraLevelGroup hO μ H) :=
  Equiv.ofBijective _ ⟨shimuraCurveOrbitsToDoubleCoset_injective hO ι hH,
    shimuraCurveOrbitsToDoubleCoset_surjective hO ι hH⟩

/-- The **elliptic points** (LMFDB `shimcurve.elliptic_points`) of the Shimura curve `X_H`, on its
complex points `H \ X(O;N)^big(ℂ)`: the points `[z, b]` with a nontrivial stabilizer group, that is,
such that the stabilizer of `(z, b)` in `B^× × K_H` modulo the rational scalars is nontrivial
(`Subalgebra.quotientMk_mem_shimuraCurveOrbitsEllipticPoints_iff`). -/
noncomputable def shimuraCurveOrbitsEllipticPoints : Set (ShimuraCurveOrbits hO ι N μ H) :=
  shimuraCurveOrbitsEquivDoubleCoset hO ι hH ⁻¹'
    shimuraDoubleCosetEllipticPoints hO ι (shimuraLevelGroup hO μ H)

/-- **The elliptic points of `H \ X(O;N)^big(ℂ)` are the points with a nontrivial stabilizer group**
(LMFDB `shimcurve.elliptic_points`): `[z, b]` is elliptic exactly when the stabilizer of `(z, b)` in
`B^× × K_H`, modulo the rational scalars, is nontrivial. -/
lemma quotientMk_mem_shimuraCurveOrbitsEllipticPoints_iff
    (p : UpperLowerHalfPlane × O.FiniteAdelicAlgebraˣ) :
    (Quotient.mk _ (Quotient.mk _ p) : ShimuraCurveOrbits hO ι N μ H) ∈
      shimuraCurveOrbitsEllipticPoints hO ι hH ↔
    shimuraDoubleCosetStabilizer hO ι (shimuraLevelGroup hO μ H) p ≠ ⊥ :=
  quotientMk_mem_shimuraDoubleCosetEllipticPoints_iff hO ι _ p

variable [Algebra.IsCentral ℚ B] [IsSimpleRing B] (hB : finrank ℚ B = 4)

/-- **The two models of the complex points of `X_H`**: the bijection
`B^×_+ \ (ℍ × B̂^×) / K_H ≃ H \ X(O;N)^big(ℂ)` (LMFDB `shimcurve`), for an order `O` of a quaternion
algebra `B` over `ℚ` and a subgroup `H` of the enhanced group containing the kernel of
`Ô^× → (O/NO)^×`, through `B^× \ (ℋ^± × B̂^×) / K_H`. -/
noncomputable def shimuraCurvePointsEquivOrbits :
    ShimuraCurvePoints hO μ H ι ≃ ShimuraCurveOrbits hO ι N μ H :=
  (shimuraCurvePointsEquivDoubleCoset hO ι μ H hB).trans
    (shimuraCurveOrbitsEquivDoubleCoset hO ι hH).symm

/-- **The elliptic points `Subalgebra.shimuraCurveEllipticPoints` are the elliptic points of the
Shimura curve of the knowl** (LMFDB `shimcurve.elliptic_points`): under the bijection
`B^×_+ \ (ℍ × B̂^×) / K_H ≃ H \ X(O;N)^big(ℂ)`, they are the points of `H \ X(O;N)^big(ℂ)` with a
nontrivial stabilizer group, which then has order `2`, `3`, `4` or `6`
(`Subalgebra.quotientMk_mem_shimuraDoubleCosetEllipticPoints_iff_natCard_mem`). -/
lemma shimuraCurvePointsEquivOrbits_mem_iff (x : ShimuraCurvePoints hO μ H ι) :
    shimuraCurvePointsEquivOrbits hO ι hH hB x ∈ shimuraCurveOrbitsEllipticPoints hO ι hH ↔
      x ∈ shimuraCurveEllipticPoints hO μ H ι := by
  rw [shimuraCurveOrbitsEllipticPoints, Set.mem_preimage, shimuraCurvePointsEquivOrbits,
    Equiv.trans_apply, Equiv.apply_symm_apply]
  exact shimuraCurvePointsEquivDoubleCoset_mem_iff hO ι μ H hB x

end Subalgebra
