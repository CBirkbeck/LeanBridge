import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.LevelDiscrete
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Bianchi.PeterssonProduct
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Projective

/-!
# Discrete subgroups of `PSL(2, ℂ)` acting on hyperbolic 3-space

A subgroup `Γ` of `PSL(2, ℂ)`, acting on hyperbolic 3-space `ℋ₃`, is discrete, countable, acts
properly discontinuously and has a measurable fundamental domain when for every `C` only finitely
many elements of `Γ` have a representative in `SL(2, ℂ)` with entries of absolute value at most `C`
(`HyperbolicThreeSpace.discreteTopology_of_finite`,
`HyperbolicThreeSpace.properlyDiscontinuousSMul_of_finite` and
`HyperbolicThreeSpace.exists_isFundamentalDomain_of_finite`, in `Bianchi/LevelDiscrete.lean` and
`Bianchi/GammaZeroFundamentalDomain.lean`). This file gives criteria for the other two properties
that the LMFDB states of the Picard group `PSL(2, ℤ[i])` (`mf.maass.picard`) and of the Bianchi
groups (`mf.bianchi.bianchigroup`), to be cofinite and not cocompact.

* If `ℋ₃` is covered by the translates under `Γ` of a set of finite hyperbolic volume, every
  fundamental domain of `Γ` has finite volume.
* If every `γ ∈ Γ` either preserves the height `y` of every point `z = (x, y)` or moves it to a
  height at most `1 / y`, then the quotient `Γ \ ℋ₃` is not compact: the images of the open sets
  `{1 / n < y < n}` cover it, but no point of the orbit of a point of height `n` lies in
  `{1 / n < y < n}`. If `PSL(2, ℂ) / Γ` were compact, so would be `Γ \ ℋ₃`, its image under
  `gΓ ↦ Γ g⁻¹ j`, as `PSL(2, ℂ)` acts transitively on `ℋ₃`.

The homomorphism `PSL(2, R) → PSL(2, S)` induced by an injective ring homomorphism `R → S`, Tau
Ceti's `TauCeti.SpecialLinear.projectiveMap`, is injective, so that `PSL(2, ℤ[i])` and
`PSL(2, 𝒪_K)` are subgroups of `PSL(2, ℂ)`.

## Main results

* `HyperbolicThreeSpace.projectiveMap_injective`: the homomorphism `PSL(2, R) → PSL(2, S)` is
  injective for an injective `R → S`.
* `HyperbolicThreeSpace.hyperbolicVolume_lt_top_of_forall_exists_smul_mem`: the finiteness of the
  volume of the fundamental domains.
* `HyperbolicThreeSpace.not_compactSpace_quotient_of_height`: the non-compactness of the quotient.
* `HyperbolicThreeSpace.compactSpace_quotient_of_compactSpace_quotientGroup`: a subgroup cocompact
  in `PSL(2, ℂ)` has a compact quotient `Γ \ ℋ₃`.
-/

open Matrix MeasureTheory MulAction Set TauCeti

open scoped MatrixGroups Pointwise

namespace HyperbolicThreeSpace

variable {Γ : Subgroup PSL(2, ℂ)} (z : HyperbolicThreeSpace)

/-- **`PSL(2, R)` is a subgroup of `PSL(2, S)`** for an injective ring homomorphism `f : R → S`:
the homomorphism `PSL(2, R) → PSL(2, S)` induced by `f` (Tau Ceti's
`TauCeti.SpecialLinear.projectiveMap`) is injective, as a matrix of `SL(2, R)` whose image is a
scalar matrix is a scalar matrix. -/
lemma projectiveMap_injective {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : Function.Injective f) : Function.Injective (SpecialLinear.projectiveMap 2 f) := by
  refine (injective_iff_map_eq_one _).mpr fun γ hγ ↦ ?_
  induction γ using QuotientGroup.induction_on with
  | H g =>
    rw [SpecialLinear.projectiveMap_mk, QuotientGroup.eq_one_iff] at hγ
    rcases SpecialLinearGroup.mem_center_iff.mp hγ with ⟨s, -, hsg⟩
    have he (i j : Fin 2) : f (g i j) = scalar (Fin 2) s i j := by
      rw [hsg]
      rfl
    have h₁ : g 0 1 = 0 := hf (by simpa using he 0 1)
    have h₂ : g 1 0 = 0 := hf (by simpa using he 1 0)
    have h₃ : g 1 1 = g 0 0 := hf (by simp [he])
    have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := g.fin_two_mul_sub_mul_eq_one
    refine (QuotientGroup.eq_one_iff _).mpr <| SpecialLinearGroup.mem_center_iff.mpr
      ⟨g 0 0, ?_, ?_⟩
    · rw [Fintype.card_fin, sq]
      rw [h₁, h₂, h₃, mul_zero, sub_zero] at hdet
      exact hdet
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [h₁, h₂, h₃]

/-- **The fundamental domains of a group covering `ℋ₃` by the translates of a set of finite volume
have finite volume**: if every point of `ℋ₃` is moved into `U` by an element of `Γ`, then a
fundamental domain `s` of `Γ` has volume at most `vol(U) = ∑_γ vol(γ U ∩ s)`. -/
lemma hyperbolicVolume_lt_top_of_forall_exists_smul_mem [Countable Γ] {U : Set HyperbolicThreeSpace}
    (hU : hyperbolicVolume U < ⊤) (hcov : ∀ z : HyperbolicThreeSpace, ∃ γ ∈ Γ, γ • z ∈ U)
    {s : Set HyperbolicThreeSpace} (hs : IsFundamentalDomain Γ s hyperbolicVolume) :
    hyperbolicVolume s < ⊤ := by
  refine ((measure_mono fun z hz ↦ ?_).trans (measure_iUnion_le _)).trans_lt
    (hs.measure_eq_tsum U ▸ hU)
  rcases hcov z with ⟨γ, hγ, hz'⟩
  refine mem_iUnion.mpr ⟨⟨γ, hγ⟩⁻¹, mem_smul_set_iff_inv_smul_mem.mpr ?_, hz⟩
  rwa [inv_inv]

/-- **A subgroup of `PSL(2, ℂ)` that moves no point to a height between `1 / y` and `y` other than
`y` is not cocompact**: if every `γ ∈ Γ` either preserves the height `y` of `z = (x, y)` or moves
`z` to a height at most `1 / y`, then the quotient `Γ \ ℋ₃` is not compact. The images of the open
sets `{1 / (n + 1) < y < n + 1}` cover it, and they increase with `n`, but the orbit of a point of
height `n + 1` does not meet `{1 / (n + 1) < y < n + 1}`. -/
lemma not_compactSpace_quotient_of_height (hΓ : ∀ γ ∈ Γ, ∀ z : HyperbolicThreeSpace,
    (γ • z).height = z.height ∨ (γ • z).height ≤ z.height⁻¹) :
    ¬CompactSpace (orbitRel.Quotient Γ HyperbolicThreeSpace) := by
  intro hc
  let π : HyperbolicThreeSpace → orbitRel.Quotient Γ HyperbolicThreeSpace :=
    Quotient.mk (orbitRel Γ HyperbolicThreeSpace)
  let U : ℕ → Set HyperbolicThreeSpace := fun n ↦ {z | (n + 1 : ℝ)⁻¹ < z.height ∧ z.height < n + 1}
  have hco : Continuous fun z : HyperbolicThreeSpace ↦ z.height :=
    isOpenEmbedding_coords.continuous.snd
  have hUo (n : ℕ) : IsOpen (π '' U n) :=
    isOpenQuotientMap_quotientMk.isOpenMap _ ((isOpen_lt continuous_const hco).inter
      (isOpen_lt hco continuous_const))
  have hmono : Monotone fun n ↦ π '' U n := by
    intro m n hmn
    have h : (m + 1 : ℝ) ≤ n + 1 := by
      exact_mod_cast Nat.add_le_add_right hmn 1
    exact image_mono fun z hz ↦ ⟨(inv_anti₀ (by positivity) h).trans_lt hz.1, hz.2.trans_le h⟩
  have hcov : univ ⊆ ⋃ n, π '' U n := by
    rintro w -
    rcases Quotient.exists_rep w with ⟨z, rfl⟩
    rcases exists_nat_gt (max z.height z.height⁻¹) with ⟨n, hn⟩
    have hz : 0 < z.height := z.height_pos
    refine mem_iUnion.mpr ⟨n, z, ⟨?_, ?_⟩, rfl⟩
    · have h : z.height⁻¹ < n + 1 := ((le_max_right _ _).trans_lt hn).trans (lt_add_one _)
      exact (inv_lt_comm₀ hz (by positivity)).mp h
    · exact ((le_max_left _ _).trans_lt hn).trans (lt_add_one _)
  rcases isCompact_univ.elim_directed_cover _ hUo hcov hmono.directed_le with ⟨n, hn⟩
  let w : HyperbolicThreeSpace := UpperHalfSpace.mk (WithLp.toLp 2 (0, (n + 1 : ℝ))) (by
    simp only [WithLp.toLp_snd]
    positivity)
  have hw : w.height = n + 1 :=
    rfl
  rcases hn (mem_univ (π w)) with ⟨u, hu, huw⟩
  rcases orbitRel_apply.mp (Quotient.exact huw) with ⟨⟨γ, hγ⟩, hγu⟩
  have hu' : (γ • w).height = u.height := by
    rw [← hγu]
    rfl
  rcases hΓ γ hγ w with h | h
  · rw [hu', hw] at h
    exact hu.2.ne h
  · rw [hu', hw] at h
    exact hu.1.not_ge h

lemma exists_smul_basePoint_eq : ∃ g : SL(2, ℂ), g • basePoint = z := by
  have hy : 0 < z.coords.2 := coords_snd_pos z
  have hr : ((√z.coords.2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
  let g : SL(2, ℂ) := ⟨!![((√z.coords.2 : ℝ) : ℂ), z.coords.1 / ((√z.coords.2 : ℝ) : ℂ); 0,
    ((√z.coords.2 : ℝ) : ℂ)⁻¹], by simp [hr]⟩
  have hb : basePoint.coords = (0, 1) :=
    rfl
  have hg₀₀ : g 0 0 = ((√z.coords.2 : ℝ) : ℂ) :=
    rfl
  have hg₀₁ : g 0 1 = z.coords.1 / ((√z.coords.2 : ℝ) : ℂ) :=
    rfl
  refine ⟨g, coords_injective ?_⟩
  rw [coords_smul, moebius_eq_of_apply_one_zero (g := g) rfl, hb, hg₀₀, hg₀₁]
  refine Prod.ext ?_ ?_
  · rw [mul_zero, zero_add, mul_div_cancel₀ _ hr]
  · rw [mul_one, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hy.le]

lemma continuous_smul_left : Continuous fun γ : PSL(2, ℂ) ↦ γ • z := by
  refine (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr <|
    isOpenEmbedding_coords.isInducing.continuous_iff.mpr ?_
  have hN (g : SL(2, ℂ)) : moebiusDenom g z.coords ≠ 0 :=
    (moebiusDenom_pos g (coords_snd_pos z)).ne'
  have hc : Continuous fun g : SL(2, ℂ) ↦ moebiusDenom g z.coords := by
    unfold moebiusDenom
    fun_prop
  refine Continuous.prodMk ?_ (continuous_const.div hc hN)
  exact Continuous.div (by fun_prop) (Complex.continuous_ofReal.comp hc)
    fun g ↦ Complex.ofReal_ne_zero.mpr (hN g)

/-- **A subgroup of `PSL(2, ℂ)` cocompact in `PSL(2, ℂ)` acts cocompactly on `ℋ₃`**: if
`PSL(2, ℂ) / Γ` is compact, so is `Γ \ ℋ₃`, its image under the continuous surjection
`gΓ ↦ Γ g⁻¹ j`, `PSL(2, ℂ)` acting transitively on `ℋ₃`. -/
lemma compactSpace_quotient_of_compactSpace_quotientGroup (hΓ : CompactSpace (PSL(2, ℂ) ⧸ Γ)) :
    CompactSpace (orbitRel.Quotient Γ HyperbolicThreeSpace) := by
  let f : PSL(2, ℂ) → orbitRel.Quotient Γ HyperbolicThreeSpace :=
    fun γ ↦ Quotient.mk (orbitRel Γ HyperbolicThreeSpace) (γ⁻¹ • basePoint)
  have hf : Continuous f :=
    continuous_quot_mk.comp ((continuous_smul_left basePoint).comp continuous_inv)
  have hrel (a b : PSL(2, ℂ)) (h : a⁻¹ * b ∈ Γ) : f a = f b := by
    refine Quotient.sound (orbitRel_apply.mpr ⟨⟨a⁻¹ * b, h⟩, ?_⟩)
    simp only [Subgroup.mk_smul, smul_smul, mul_inv_cancel_right]
  let F : PSL(2, ℂ) ⧸ Γ → orbitRel.Quotient Γ HyperbolicThreeSpace :=
    Quotient.lift f fun a b hab ↦ hrel a b (QuotientGroup.leftRel_apply.mp hab)
  have hF : Continuous F :=
    Continuous.quotient_lift (s := QuotientGroup.leftRel Γ) hf _
  have hsurj : Function.Surjective F := by
    intro w
    rcases Quotient.exists_rep w with ⟨z, rfl⟩
    rcases exists_smul_basePoint_eq z with ⟨g, rfl⟩
    refine ⟨QuotientGroup.mk (QuotientGroup.mk g : PSL(2, ℂ))⁻¹, ?_⟩
    simp only [F, Quotient.lift_mk, f, inv_inv]
    rfl
  exact hsurj.compactSpace hF

end HyperbolicThreeSpace
