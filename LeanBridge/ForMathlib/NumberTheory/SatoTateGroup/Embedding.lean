import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.CharacterPolynomial
import Mathlib.Topology.Perfect

/-!
# The embedding of a Sato–Tate group in its ambient group

A Sato–Tate group is a compact subgroup `G` of its ambient group, `USp(d)` or `O(d)` (LMFDB
`st_group.definition`), and its moments and other invariants are computed from the distribution of
the characteristic polynomials of its elements, the pushforward of its Haar probability measure
(`SatoTateGroup.charpolyDistribution`): the moment sequences of the coefficients `aᵢ` are the
moments of this distribution. It depends on how `G` is embedded in its ambient group, but only up
to conjugacy (LMFDB `st_group.embedding`).

* Conjugate groups have the same distribution, hence the same moment sequences: the characteristic
  polynomial is invariant under conjugation, and the conjugation is an isomorphism of compact
  groups, which carries one Haar probability measure to the other.
* Isomorphic groups need not. In the diagonal torus `{diag(x₀, x₁, x₂, x₀⁻¹, x₁⁻¹, x₂⁻¹)}` of
  `USp(6)`, the groups `{(u, uζ, uζ²)}` and `{(u, u, uζ)}`, with `|u| = 1` and `ζ³ = 1`, are
  Sato–Tate groups of weight `1` and degree `6` with identity component
  `U(1)₃ = {diag(u, u, u, ū, ū, ū)}` and three components. They are isomorphic as topological
  groups, by `(x₀, x₁, x₂) ↦ (x₀, x₀, x₁)`, hence as real Lie groups, a continuous homomorphism of
  Lie groups being smooth (Tau Ceti's `TauCeti.contMDiff_of_continuous_monoidHom`): both are
  `U(1) × C₃`. On the first the trace vanishes on the two components other than `U(1)₃`, a set of
  positive measure, as `1 + ζ + ζ² = 0` for `ζ ≠ 1`; on the second it vanishes at finitely many
  points, a set of measure zero. So their distributions differ. They are the Sato–Tate groups, over
  `ℚ(ζ₃)`, of the abelian threefolds `E × E' × E''` and `E × E × E'`, for an elliptic curve `E` with
  complex multiplication by `ℤ[ζ₃]` and its twists `E'` and `E''` by a cubic character and its
  square; this is not formalised.

## Main definitions

* `SatoTateGroup.charpolyDistribution` (LMFDB `st_group.embedding`): the distribution of the
  characteristic polynomials of a Sato–Tate group.
* `SatoTateGroup.conj`: the conjugate of a Sato–Tate group by an element of its ambient group.
* `SatoTateGroup.ofTorus`: the Sato–Tate group of weight `1` of a closed subgroup of the diagonal
  torus of `USp(2g)`, and `SatoTateGroup.ofTorusEquiv`, the isomorphism from that subgroup onto it.
* `SatoTateGroup.regularCubeRoots` and `SatoTateGroup.reflectionCubeRoots`: the Sato–Tate groups
  `{(u, uζ, uζ²)}` and `{(u, u, uζ)}` of weight `1` and degree `6`.
* `SatoTateGroup.regularCubeRootsEquiv`: an isomorphism of topological groups between them.

## Main results

* `SatoTateGroup.moment_charpolyCoeff_eq_integral`: the moment sequence of `aᵢ` is the sequence of
  moments of the distribution of the characteristic polynomials.
* `SatoTateGroup.charpolyDistribution_conj` (LMFDB `st_group.embedding`): conjugate Sato–Tate
  groups have the same distribution of characteristic polynomials.
* `SatoTateGroup.moment_charpolyCoeff_conj`: conjugate Sato–Tate groups have the same moment
  sequences.
* `SatoTateGroup.charpolyDistribution_regularCubeRoots_ne` (LMFDB `st_group.embedding`): the
  isomorphic Sato–Tate groups `{(u, uζ, uζ²)}` and `{(u, u, uζ)}` have different distributions of
  characteristic polynomials.
-/

open Matrix MeasureTheory TauCeti Topology

namespace SatoTateGroup

variable (G : SatoTateGroup)

/-- The **distribution of the characteristic polynomials** (LMFDB `st_group.embedding`) of a
Sato–Tate group `G`: the pushforward of its Haar probability measure under the map sending `g` to
the sequence `(aᵢ)` of coefficients of its characteristic polynomial `xᵈ + a₁ xᵈ⁻¹ + ⋯ + a_d`
(`SatoTateGroup.charpolyCoeff`, with `a₀ = 1` and `aᵢ = 0` for `i > d`), which determines the
polynomial. The moment sequences of the `aᵢ` (LMFDB `st_group.moments`) are its moments
(`SatoTateGroup.moment_charpolyCoeff_eq_integral`). -/
noncomputable def charpolyDistribution : Measure (ℕ → ℂ) :=
  (haarProb G.toSubgroup).map fun g i ↦ G.charpolyCoeff i g

lemma measurable_charpolyCoeff_pi :
    Measurable fun (g : G.toSubgroup) (i : ℕ) ↦ G.charpolyCoeff i g :=
  measurable_pi_iff.mpr fun i ↦ (G.continuous_charpolyCoeff i).measurable

/-- **The moment sequence of `aᵢ` is the sequence of moments of the distribution of the
characteristic polynomials** (LMFDB `st_group.moments`): `E[aᵢⁿ]` is the integral of the `n`th power
of the `i`th coefficient. -/
lemma moment_charpolyCoeff_eq_integral (i n : ℕ) :
    G.moment (G.charpolyCoeff i) n = ∫ a, a i ^ n ∂G.charpolyDistribution :=
  (integral_map G.measurable_charpolyCoeff_pi.aemeasurable
    ((continuous_apply i).pow n).aestronglyMeasurable).symm

/-- The **conjugate** `g G g⁻¹` of a Sato–Tate group `G` by an element `g` of its ambient group: a
Sato–Tate group of the same weight and degree. -/
def conj (g : unitaryGroup (Fin G.degree) ℂ) (hg : g ∈ G.ambient) : SatoTateGroup where
  weight := G.weight
  degree := G.degree
  even_degree_of_odd_weight := G.even_degree_of_odd_weight
  toSubgroup := G.toSubgroup.map (MulAut.conj g).toMonoidHom
  isClosed := by
    rw [Subgroup.map_equiv_eq_comap_symm']
    exact G.isClosed.preimage <| ((continuous_const.mul continuous_id).mul continuous_const).congr
      fun x ↦ (MulAut.conj_symm_apply g x).symm
  le_ambientGroup := Subgroup.map_le_iff_le_comap.mpr fun x hx ↦ Subgroup.mem_comap.mpr <| by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact G.ambient.mul_mem (G.ambient.mul_mem hg (G.le_ambientGroup hx)) (G.ambient.inv_mem hg)

variable {G} in
/-- **Conjugate Sato–Tate groups have the same distribution of characteristic polynomials** (LMFDB
`st_group.embedding`): the conjugation by `g` is an isomorphism of compact groups from `G` onto
`g G g⁻¹`, which carries the Haar probability measure of `G` to that of `g G g⁻¹`, and it preserves
characteristic polynomials. So the embedding of a Sato–Tate group in its ambient group only matters
up to conjugacy. -/
lemma charpolyDistribution_conj (g : unitaryGroup (Fin G.degree) ℂ) (hg : g ∈ G.ambient) :
    (G.conj g hg).charpolyDistribution = G.charpolyDistribution := by
  let φ : G.toSubgroup ≃* (G.conj g hg).toSubgroup := (MulAut.conj g).subgroupMap G.toSubgroup
  have hφ : Continuous φ :=
    ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
  have hHaar : haarProb (G.conj g hg).toSubgroup = (haarProb G.toSubgroup).map φ := by
    have _ : ((haarProb G.toSubgroup).map φ).IsHaarMeasure :=
      Measure.isHaarMeasure_map_of_isFiniteMeasure _ φ.toMonoidHom hφ φ.surjective
    exact (eq_haarProb_of_isHaarMeasure_of_isProbabilityMeasure _ _).symm
  have hcomp : (fun x (i : ℕ) ↦ (G.conj g hg).charpolyCoeff i x) ∘ φ =
      fun x i ↦ G.charpolyCoeff i x := by
    funext x i
    have h : (G.conj g hg).matrix (φ x) =
        (Unitary.toUnits g).val * G.matrix x * ((Unitary.toUnits g).val)⁻¹ := by
      rw [← Matrix.coe_units_inv]
      rfl
    rw [Function.comp_apply, charpolyCoeff, charpolyCoeff, h]
    exact congrArg (fun p : Polynomial ℂ ↦ p.reverse.coeff i)
      (Matrix.charpoly_units_conj (Unitary.toUnits g) (G.matrix x))
  rw [charpolyDistribution, charpolyDistribution, hHaar,
    Measure.map_map (G.conj g hg).measurable_charpolyCoeff_pi hφ.measurable, hcomp]

variable {G} in
/-- **Conjugate Sato–Tate groups have the same moment sequences** (LMFDB `st_group.embedding`): the
moments `E[aᵢⁿ]` of `g G g⁻¹` are those of `G`. -/
lemma moment_charpolyCoeff_conj (g : unitaryGroup (Fin G.degree) ℂ) (hg : g ∈ G.ambient) (i n : ℕ) :
    (G.conj g hg).moment ((G.conj g hg).charpolyCoeff i) n = G.moment (G.charpolyCoeff i) n := by
  rw [moment_charpolyCoeff_eq_integral, moment_charpolyCoeff_eq_integral, charpolyDistribution_conj]

/-! ### Closed subgroups of the diagonal torus of `USp(2g)` -/

variable {g : ℕ} (H : Subgroup (Fin g → Circle)) (hH : IsClosed (H : Set (Fin g → Circle)))

lemma uspTorusMatrix_injective : Function.Injective (uspTorusMatrix (g := g)) := fun x y h ↦ by
  funext j
  have h₁ : (uspTorusEntry x (Fin.castAdd g j) : ℂ) = uspTorusEntry y (Fin.castAdd g j) :=
    congrFun (diagonal_injective h) _
  rwa [uspTorusEntry_castAdd, uspTorusEntry_castAdd, Circle.coe_inj] at h₁

lemma trace_uspTorusMatrix (x : Fin g → Circle) :
    (uspTorusMatrix x).trace = ∑ j, (x j : ℂ) + ∑ j, (((x j)⁻¹ : Circle) : ℂ) := by
  rw [uspTorusMatrix, trace_diagonal, Fin.sum_univ_add]
  simp only [uspTorusEntry_castAdd, uspTorusEntry_natAdd]

variable (g) in
/-- The diagonal torus `x ↦ diag(x₁, …, x_g, x₁⁻¹, …, x_g⁻¹)` of `USp(2g)`, as a homomorphism to the
unitary group `U(2g)`. -/
noncomputable def uspTorusHom : (Fin g → Circle) →* unitaryGroup (Fin (g + g)) ℂ :=
  (ambientGroup 1 (g + g)).subtype.comp (uspTorus odd_one rfl)

lemma continuous_uspTorusHom : Continuous (uspTorusHom g) :=
  continuous_subtype_val.comp (continuous_uspTorus odd_one)

lemma uspTorusHom_injective : Function.Injective (uspTorusHom g) := fun _ _ h ↦
  uspTorusMatrix_injective (congrArg Subtype.val h)

/-- The Sato–Tate group of weight `1` and degree `2g` of a closed subgroup `H` of the torus
`U(1)^g`: its image in the diagonal torus of `USp(2g)`. -/
noncomputable def ofTorus : SatoTateGroup where
  weight := 1
  degree := g + g
  even_degree_of_odd_weight _ := ⟨g, rfl⟩
  toSubgroup := H.map (uspTorusHom g)
  isClosed := by
    rw [Subgroup.coe_map]
    exact (hH.isCompact.image continuous_uspTorusHom).isClosed
  le_ambientGroup := by
    rintro _ ⟨x, -, rfl⟩
    exact (uspTorus odd_one rfl x).2

/-- The isomorphism of topological groups from a closed subgroup `H` of the torus `U(1)^g` onto its
Sato–Tate group `SatoTateGroup.ofTorus`, a continuous bijection from a compact space. -/
noncomputable def ofTorusEquiv : H ≃ₜ* (ofTorus H hH).toSubgroup :=
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  letI e : H ≃* H.map (uspTorusHom g) := H.equivMapOfInjective (uspTorusHom g) uspTorusHom_injective
  haveI hcont : Continuous e := (continuous_uspTorusHom.comp continuous_subtype_val).subtype_mk _
  { e with
    continuous_toFun := hcont
    continuous_invFun := (hcont.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

variable {H hH} in
lemma charpolyCoeff_one_ofTorusEquiv (hg : 0 < g) (x : H) :
    (ofTorus H hH).charpolyCoeff 1 (ofTorusEquiv H hH x) =
      -(∑ j, (x.1 j : ℂ) + ∑ j, (((x.1 j)⁻¹ : Circle) : ℂ)) := by
  rw [charpolyCoeff_one _ (Nat.add_pos_left hg g), ← trace_uspTorusMatrix]
  rfl

/-! ### Two isomorphic Sato–Tate groups with different distributions -/

/-- The subgroup `{(u, uζ, uζ²) | ζ³ = 1}` of the torus `U(1)³`: the `x` with `x₁³ = x₀³` and
`x₀ x₂ = x₁²`. It is generated by the circle `{(u, u, u)}` and `(1, ω, ω²)`, for a primitive cube
root of unity `ω`. -/
def regularCubeTorus : Subgroup (Fin 3 → Circle) where
  carrier := {x | x 1 ^ 3 = x 0 ^ 3 ∧ x 0 * x 2 = x 1 ^ 2}
  mul_mem' {x y} hx hy := by
    refine ⟨?_, ?_⟩
    · simp only [Pi.mul_apply, mul_pow, hx.1, hy.1]
    · simp only [Pi.mul_apply, mul_pow, ← hx.2, ← hy.2]
      exact mul_mul_mul_comm _ _ _ _
  one_mem' := ⟨rfl, by simp⟩
  inv_mem' {x} hx := by
    refine ⟨?_, ?_⟩
    · simp only [Pi.inv_apply, inv_pow, hx.1]
    · simp only [Pi.inv_apply, inv_pow, ← hx.2, mul_inv]

/-- The subgroup `{(u, u, uζ) | ζ³ = 1}` of the torus `U(1)³`: the `x` with `x₁ = x₀` and
`x₂³ = x₀³`. It is generated by the circle `{(u, u, u)}` and `(1, 1, ω)`, for a primitive cube root
of unity `ω`. -/
def reflectionCubeTorus : Subgroup (Fin 3 → Circle) where
  carrier := {x | x 1 = x 0 ∧ x 2 ^ 3 = x 0 ^ 3}
  mul_mem' {x y} hx hy := by
    refine ⟨?_, ?_⟩
    · simp only [Pi.mul_apply, hx.1, hy.1]
    · simp only [Pi.mul_apply, mul_pow, hx.2, hy.2]
  one_mem' := ⟨rfl, rfl⟩
  inv_mem' {x} hx := by
    refine ⟨?_, ?_⟩
    · simp only [Pi.inv_apply, hx.1]
    · simp only [Pi.inv_apply, inv_pow, hx.2]

lemma isClosed_regularCubeTorus : IsClosed (regularCubeTorus : Set (Fin 3 → Circle)) :=
  (isClosed_eq ((continuous_apply 1).pow 3) ((continuous_apply 0).pow 3)).inter
    (isClosed_eq ((continuous_apply 0).mul (continuous_apply 2)) ((continuous_apply 1).pow 2))

lemma isClosed_reflectionCubeTorus : IsClosed (reflectionCubeTorus : Set (Fin 3 → Circle)) :=
  (isClosed_eq (continuous_apply 1) (continuous_apply 0)).inter
    (isClosed_eq ((continuous_apply 2).pow 3) ((continuous_apply 0).pow 3))

instance : CompactSpace regularCubeTorus :=
  isCompact_iff_compactSpace.mp isClosed_regularCubeTorus.isCompact

/-- The isomorphism of topological groups `(x₀, x₁, x₂) ↦ (x₀, x₀, x₁)` from `{(u, uζ, uζ²)}` onto
`{(u, u, uζ)}`, with inverse `(y₀, y₁, y₂) ↦ (y₀, y₂, y₂² y₀⁻¹)`. -/
noncomputable def regularCubeTorusEquiv : regularCubeTorus ≃ₜ* reflectionCubeTorus :=
  letI e : regularCubeTorus ≃* reflectionCubeTorus :=
    { toFun := fun x ↦ ⟨fun j ↦ x.1 (![0, 0, 1] j), rfl, x.2.1⟩
      invFun := fun y ↦
        ⟨![y.1 0, y.1 2, y.1 2 ^ 2 * (y.1 0)⁻¹], y.2.2, mul_inv_cancel_comm_assoc _ _⟩
      left_inv := fun x ↦ Subtype.ext <| funext fun j ↦ by
        fin_cases j
        · rfl
        · rfl
        · exact mul_inv_eq_of_eq_mul (by rw [mul_comm]; exact x.2.2.symm)
      right_inv := fun y ↦ Subtype.ext <| funext fun j ↦ by
        fin_cases j
        · rfl
        · exact y.2.1.symm
        · rfl
      map_mul' := fun x y ↦ Subtype.ext <| funext fun j ↦ by
        fin_cases j <;> rfl }
  haveI hcont : Continuous e := Continuous.subtype_mk
    (f := fun x : regularCubeTorus ↦ fun j ↦ x.1 (![0, 0, 1] j))
    (continuous_pi fun j ↦ (continuous_apply (![0, 0, 1] j)).comp continuous_subtype_val) _
  { e with
    continuous_toFun := hcont
    continuous_invFun := (hcont.homeoOfEquivCompactToT2 (f := e.toEquiv)).symm.continuous }

/-- The Sato–Tate group `{diag(u, uζ, uζ², ū, ūζ̄, ūζ̄²) | |u| = 1, ζ³ = 1}` of weight `1` and
degree `6`, with identity component `U(1)₃ = {diag(u, u, u, ū, ū, ū)}` and three components: the
image of `SatoTateGroup.regularCubeTorus` in the diagonal torus of `USp(6)`. -/
noncomputable def regularCubeRoots : SatoTateGroup :=
  ofTorus regularCubeTorus isClosed_regularCubeTorus

/-- The Sato–Tate group `{diag(u, u, uζ, ū, ū, ūζ̄) | |u| = 1, ζ³ = 1}` of weight `1` and degree
`6`, with identity component `U(1)₃ = {diag(u, u, u, ū, ū, ū)}` and three components: the image of
`SatoTateGroup.reflectionCubeTorus` in the diagonal torus of `USp(6)`. -/
noncomputable def reflectionCubeRoots : SatoTateGroup :=
  ofTorus reflectionCubeTorus isClosed_reflectionCubeTorus

/-- An **isomorphism of topological groups between the Sato–Tate groups `{(u, uζ, uζ²)}` and
`{(u, u, uζ)}`**, induced by `(x₀, x₁, x₂) ↦ (x₀, x₀, x₁)`. Both are compact Lie groups, closed
subgroups of `U(6)`, and a continuous homomorphism of Lie groups is smooth (Tau Ceti's
`TauCeti.contMDiff_of_continuous_monoidHom`), so it is an isomorphism of real Lie groups. -/
noncomputable def regularCubeRootsEquiv :
    regularCubeRoots.toSubgroup ≃ₜ* reflectionCubeRoots.toSubgroup :=
  ((ofTorusEquiv _ _).symm.trans regularCubeTorusEquiv).trans (ofTorusEquiv _ _)

private lemma sum_add_sum_inv_eq_zero {x : Fin 3 → Circle} (hx : x ∈ regularCubeTorus)
    (h : x 1 ≠ x 0) : ∑ j, (x j : ℂ) + ∑ j, (((x j)⁻¹ : Circle) : ℂ) = 0 := by
  have h₁ : (x 1 : ℂ) ^ 3 = (x 0 : ℂ) ^ 3 := by
    exact_mod_cast congrArg (fun z : Circle ↦ (z : ℂ)) hx.1
  have h₂ : (x 0 : ℂ) * x 2 = (x 1 : ℂ) ^ 2 := by
    exact_mod_cast congrArg (fun z : Circle ↦ (z : ℂ)) hx.2
  have h₃ : ((x 1 : ℂ) - x 0) * x 0 ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr fun h' ↦ h (Circle.coe_injective h')) (Circle.coe_ne_zero _)
  have h₀ : (x 0 : ℂ) + x 1 + x 2 = 0 :=
    mul_left_cancel₀ h₃ <| by linear_combination h₁ + ((x 1 : ℂ) - x 0) * h₂
  simp only [Circle.coe_inv_eq_conj, ← map_sum, Fin.sum_univ_three, h₀, map_zero, add_zero]

private lemma exp_two_pi_div_three_pow : Circle.exp (2 * Real.pi / 3) ^ 3 = 1 := by
  rw [← Circle.exp_natCast_mul, Nat.cast_ofNat, mul_div_cancel₀ _ three_ne_zero,
    Circle.exp_two_pi]

private lemma exp_two_pi_div_three_ne_one : Circle.exp (2 * Real.pi / 3) ≠ 1 := by
  rw [Ne, Circle.exp_eq_one]
  rintro ⟨n, hn⟩
  have h : (3 * n : ℝ) * (2 * Real.pi) = 1 * (2 * Real.pi) := by
    linarith
  have h' : (3 * n : ℝ) = 1 := mul_right_cancel₀ (by positivity) h
  exact absurd (by exact_mod_cast h' : 3 * n = 1) (by omega)

private lemma measure_charpolyCoeff_one_regularCubeRoots_pos :
    0 < haarProb _ {g | regularCubeRoots.charpolyCoeff 1 g = 0} := by
  let e : regularCubeTorus ≃ₜ* regularCubeRoots.toSubgroup := ofTorusEquiv _ _
  have hopen : IsOpen (e '' {x | x.1 1 ≠ x.1 0}) :=
    e.toHomeomorph.isOpenMap _ <| isOpen_ne_fun ((continuous_apply 1).comp continuous_subtype_val)
      ((continuous_apply 0).comp continuous_subtype_val)
  have hmem : ![1, Circle.exp (2 * Real.pi / 3), Circle.exp (2 * Real.pi / 3) ^ 2] ∈
      regularCubeTorus :=
    ⟨by simp [exp_two_pi_div_three_pow], by simp⟩
  have hne : (e '' {x | x.1 1 ≠ x.1 0}).Nonempty :=
    ⟨_, ⟨_, hmem⟩, exp_two_pi_div_three_ne_one, rfl⟩
  refine (hopen.measure_pos _ hne).trans_le (measure_mono ?_)
  rintro _ ⟨x, hx, rfl⟩
  exact (charpolyCoeff_one_ofTorusEquiv three_pos x).trans <| by
    rw [sum_add_sum_inv_eq_zero x.2 hx, neg_zero]

private lemma finite_setOf_coe_pow_eq {n : ℕ} (hn : 0 < n) (w : ℂ) :
    {z : Circle | (z : ℂ) ^ n = w}.Finite :=
  ((Polynomial.nthRoots n w).toFinset.finite_toSet.preimage Circle.coe_injective.injOn).subset
    fun _ hz ↦ Finset.mem_coe.mpr <| Multiset.mem_toFinset.mpr <|
      (Polynomial.mem_nthRoots hn).mpr hz

private lemma finite_setOf_sum_add_sum_inv_eq_zero :
    {y : reflectionCubeTorus | ∑ j, (y.1 j : ℂ) + ∑ j, (((y.1 j)⁻¹ : Circle) : ℂ) = 0}.Finite := by
  have hF : (⋃ t ∈ {t : Circle | (t : ℂ) ^ 3 = 1}, (fun a : Circle ↦ (a, t * a)) ''
      {a : Circle | (a : ℂ) ^ 2 = -(2 + (t : ℂ)⁻¹) / (2 + t)}).Finite :=
    (finite_setOf_coe_pow_eq three_pos 1).biUnion fun t _ ↦
      (finite_setOf_coe_pow_eq two_pos _).image _
  have hinj : Function.Injective fun y : reflectionCubeTorus ↦ (y.1 0, y.1 2) := fun y y' h ↦ by
    rcases Prod.ext_iff.mp h with ⟨h₀, h₂⟩
    refine Subtype.ext <| funext fun k ↦ ?_
    fin_cases k
    exacts [h₀, (y.2.1.trans h₀).trans y'.2.1.symm, h₂]
  refine (hF.preimage hinj.injOn).subset fun y hy ↦ ?_
  have ha : (y.1 0 : ℂ) * (y.1 0 : ℂ)⁻¹ = 1 := mul_inv_cancel₀ (Circle.coe_ne_zero _)
  have hden : 2 + ((y.1 2 * (y.1 0)⁻¹ : Circle) : ℂ) ≠ 0 := fun h ↦ by
    have h₁ : ‖((y.1 2 * (y.1 0)⁻¹ : Circle) : ℂ)‖ = 1 := Circle.norm_coe _
    rw [eq_neg_of_add_eq_zero_right h] at h₁
    norm_num at h₁
  have hy' : (y.1 0 : ℂ) + y.1 0 + y.1 2 + ((y.1 0 : ℂ)⁻¹ + (y.1 0 : ℂ)⁻¹ + (y.1 2 : ℂ)⁻¹) = 0 := by
    simpa [Fin.sum_univ_three, y.2.1] using hy
  refine Set.mem_iUnion₂.mpr ⟨y.1 2 * (y.1 0)⁻¹, ?_, y.1 0, ?_, Prod.ext rfl (by simp)⟩
  · rw [Set.mem_ofPred_eq, ← Circle.coe_pow, mul_pow, inv_pow, y.2.2, mul_inv_cancel,
      Circle.coe_one]
  · rw [Set.mem_ofPred_eq, eq_div_iff hden, Circle.coe_mul, Circle.coe_inv, mul_inv, inv_inv]
    linear_combination (y.1 0 : ℂ) * hy' + ((y.1 0 : ℂ) * y.1 2 - 2) * ha

private lemma neBot_nhdsNE_one_reflectionCubeRoots :
    (𝓝[≠] (1 : reflectionCubeRoots.toSubgroup)).NeBot := by
  have _ : Nontrivial Circle := ⟨⟨_, _, Circle.exp_pi_ne_one⟩⟩
  let e : reflectionCubeTorus ≃ₜ* reflectionCubeRoots.toSubgroup := ofTorusEquiv _ _
  let γ : Circle → reflectionCubeRoots.toSubgroup := fun u ↦ e ⟨fun _ ↦ u, rfl, rfl⟩
  have hγ : Continuous γ :=
    e.continuous.comp <| (continuous_pi fun _ ↦ continuous_id).subtype_mk _
  have hγ₁ : γ 1 = 1 := map_one e
  have hinj : Function.Injective γ := fun u v h ↦
    congrFun (congrArg Subtype.val (e.injective h)) 0
  exact (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within γ
    ((hγ.tendsto' 1 1 hγ₁).mono_left nhdsWithin_le_nhds)
    ((eventually_mem_nhdsWithin (s := {1}ᶜ)).mono fun _ hu h ↦
      hu (hinj (h.trans hγ₁.symm)))).neBot

private lemma measure_charpolyCoeff_one_reflectionCubeRoots :
    haarProb _ {g | reflectionCubeRoots.charpolyCoeff 1 g = 0} = 0 := by
  have _ : (𝓝[≠] (1 : reflectionCubeRoots.toSubgroup)).NeBot :=
    neBot_nhdsNE_one_reflectionCubeRoots
  let e : reflectionCubeTorus ≃ₜ* reflectionCubeRoots.toSubgroup := ofTorusEquiv _ _
  refine ((finite_setOf_sum_add_sum_inv_eq_zero.image e).subset fun g hg ↦ ?_).measure_zero _
  refine ⟨e.symm g, ?_, e.apply_symm_apply g⟩
  have h : reflectionCubeRoots.charpolyCoeff 1 (e (e.symm g)) = 0 := by
    rwa [e.apply_symm_apply]
  exact neg_eq_zero.mp ((charpolyCoeff_one_ofTorusEquiv three_pos (e.symm g)).symm.trans h)

/-- **Isomorphic Sato–Tate groups may have different distributions of characteristic polynomials**
(LMFDB `st_group.embedding`): the Sato–Tate groups `{(u, uζ, uζ²)}` and `{(u, u, uζ)}` of weight `1`
and degree `6` are isomorphic (`SatoTateGroup.regularCubeRootsEquiv`), but `a₁ = -t` vanishes on a
set of positive measure of the first, its two components other than the identity component, and on
a set of measure zero of the second, where the trace has finitely many zeros. -/
lemma charpolyDistribution_regularCubeRoots_ne :
    regularCubeRoots.charpolyDistribution ≠ reflectionCubeRoots.charpolyDistribution := by
  intro h
  have hS : MeasurableSet {a : ℕ → ℂ | a 1 = 0} :=
    measurable_pi_apply 1 (measurableSet_singleton 0)
  have h₁ : regularCubeRoots.charpolyDistribution {a | a 1 = 0} =
      reflectionCubeRoots.charpolyDistribution {a | a 1 = 0} := by
    rw [h]
  rw [charpolyDistribution, charpolyDistribution,
    Measure.map_apply (measurable_charpolyCoeff_pi _) hS,
    Measure.map_apply (measurable_charpolyCoeff_pi _) hS] at h₁
  exact (measure_charpolyCoeff_one_regularCubeRoots_pos.trans_eq h₁).ne'
    measure_charpolyCoeff_one_reflectionCubeRoots

end SatoTateGroup
