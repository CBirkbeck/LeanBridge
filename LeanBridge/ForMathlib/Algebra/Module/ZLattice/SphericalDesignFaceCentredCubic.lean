import LeanBridge.ForMathlib.Algebra.Module.ZLattice.SphericalDesignEutactic

/-!
# The face-centred cubic lattice is perfect but not strongly perfect

The face-centred cubic lattice `D₃ = {x ∈ ℤ³ : x₀ + x₁ + x₂ even}` of `ℝ³`, isometric to the root
lattice `A₃`, is spanned by `(1, 1, 0)`, `(1, -1, 0)` and `(0, 1, -1)`: its vectors are
`(a + b, a - b + c, -c)`, of squared length `2 (a² + b² + c² + a c - b c)`. So its minimum is `√2`,
and its minimal vectors are the twelve vectors with two coordinates `±1` and one `0`.

* It is perfect (LMFDB `lattice.perfect`): the matrices `x xᵀ` of `(1, ±1, 0)`, `(1, 0, ±1)` and
  `(0, 1, ±1)` span the symmetric `3 × 3` matrices.
* It is not strongly perfect (LMFDB `lattice.spherical_design`): the rotation `g` of cosine `3 / 5`
  in the plane of the first two coordinates preserves the sphere measure, so `x₀⁴ + x₁⁴` and its
  composite with `g`, `((3x₀ - 4x₁)/5)⁴ + ((4x₀ + 3x₁)/5)⁴`, two polynomials of degree `4`, have the
  same average over the sphere; but their sums over the twelve minimal vectors are `16` and
  `12304 / 625`. So the minimal vectors are not a spherical `4`-design.

With Venkov's theorem (`ZLattice.IsStronglyPerfect.isPerfect`), being strongly perfect is thus a
strictly stronger condition than being perfect.

## Main definitions

* `ZLattice.rotationThreeFourFive`: the rotation of `ℝ³` with cosine `3 / 5` and sine `4 / 5` in the
  plane of the first two coordinates.
* `ZLattice.faceCentredCubicLattice`: the lattice `D₃` of `ℝ³`.

## Main results

* `ZLattice.minimum_faceCentredCubicLattice`: its minimum is `√2`.
* `ZLattice.minimalVectors_faceCentredCubicLattice`: its twelve minimal vectors.
* `ZLattice.isPerfect_faceCentredCubicLattice` (LMFDB `lattice.perfect`,
  `lattice.spherical_design`): it is perfect.
* `ZLattice.not_isStronglyPerfect_faceCentredCubicLattice` (LMFDB `lattice.spherical_design`): it
  is not strongly perfect.
-/

open MeasureTheory Metric Matrix MvPolynomial

open scoped InnerProductSpace

namespace ZLattice

variable (x : EuclideanSpace ℝ (Fin 3)) {a b c : ℤ}

lemma toEuclideanLin_rotation_apply : toEuclideanLin
    !![(3 : ℝ) / 5, -4 / 5, 0; 4 / 5, 3 / 5, 0; 0, 0, 1] x =
    !₂[3 / 5 * x 0 - 4 / 5 * x 1, 4 / 5 * x 0 + 3 / 5 * x 1, x 2] := by
  ext i
  fin_cases i <;> simp [dotProduct, Fin.sum_univ_three, neg_div, ← sub_eq_add_neg]

/-- The rotation `(x₀, x₁, x₂) ↦ ((3x₀ - 4x₁) / 5, (4x₀ + 3x₁) / 5, x₂)` of `ℝ³`, of cosine `3 / 5`
and sine `4 / 5` in the plane of the first two coordinates. -/
noncomputable def rotationThreeFourFive :
    EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (LinearMap.isometryOfInner (toEuclideanLin !![(3 : ℝ) / 5, -4 / 5, 0; 4 / 5, 3 / 5, 0; 0, 0, 1])
    fun u v ↦ by
      rw [toEuclideanLin_rotation_apply, toEuclideanLin_rotation_apply]
      simp only [PiLp.inner_apply, Fin.sum_univ_three, RCLike.inner_apply]
      simp
      ring1).toLinearIsometryEquiv rfl

lemma rotationThreeFourFive_apply :
    rotationThreeFourFive x = !₂[3 / 5 * x 0 - 4 / 5 * x 1, 4 / 5 * x 0 + 3 / 5 * x 1, x 2] :=
  toEuclideanLin_rotation_apply x

/-- The **face-centred cubic lattice** `D₃ = {x ∈ ℤ³ : x₀ + x₁ + x₂ even}` of `ℝ³`, spanned by
`(1, 1, 0)`, `(1, -1, 0)` and `(0, 1, -1)`; it is isometric to the root lattice `A₃`. -/
noncomputable def faceCentredCubicLattice : Submodule ℤ (EuclideanSpace ℝ (Fin 3)) :=
  Submodule.span ℤ {!₂[1, 1, 0], !₂[1, -1, 0], !₂[0, 1, -1]}

variable (a b c) in
/-- The vector `a (1, 1, 0) + b (1, -1, 0) + c (0, 1, -1) = (a + b, a - b + c, -c)` of the
face-centred cubic lattice. -/
noncomputable def fccVector : EuclideanSpace ℝ (Fin 3) :=
  !₂[(a + b : ℝ), a - b + c, -c]

variable {x} in
lemma mem_faceCentredCubicLattice_iff :
    x ∈ faceCentredCubicLattice ↔ ∃ a b c : ℤ, fccVector a b c = x := by
  rw [faceCentredCubicLattice, Submodule.mem_span_insert]
  refine ⟨fun ⟨a, z, hz, hx⟩ ↦ ?_, fun ⟨a, b, c, hx⟩ ↦ ⟨a, b • !₂[1, -1, 0] + c • !₂[0, 1, -1],
    Submodule.mem_span_pair.mpr ⟨b, c, rfl⟩, ?_⟩⟩
  · rcases Submodule.mem_span_pair.mp hz with ⟨b, c, rfl⟩
    refine ⟨a, b, c, ?_⟩
    rw [hx]
    ext i
    fin_cases i <;> simp [fccVector, sub_eq_add_neg, add_assoc]
  · rw [← hx]
    ext i
    fin_cases i <;> simp [fccVector, sub_eq_add_neg, add_assoc]

variable (a b c) in
lemma sq_norm_fccVector :
    ‖fccVector a b c‖ ^ 2 = 2 * ((a ^ 2 + b ^ 2 + c ^ 2 + a * c - b * c : ℤ) : ℝ) := by
  rw [fccVector, EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs]
  push_cast
  simp
  ring1

lemma one_le_fcc_form (h : ¬(a = 0 ∧ b = 0 ∧ c = 0)) :
    1 ≤ a ^ 2 + b ^ 2 + c ^ 2 + a * c - b * c := by
  by_contra hlt
  have h0 : a ^ 2 + b ^ 2 + c ^ 2 + a * c - b * c ≤ 0 := by
    omega
  have hc : c = 0 := by
    nlinarith [sq_nonneg (2 * a + c), sq_nonneg (2 * b - c), sq_nonneg c]
  have ha : a = 0 := by
    nlinarith [sq_nonneg (2 * a + c), sq_nonneg (2 * b - c), sq_nonneg c]
  have hb : b = 0 := by
    nlinarith [sq_nonneg (2 * a + c), sq_nonneg (2 * b - c), sq_nonneg c]
  exact h ⟨ha, hb, hc⟩

lemma fccVector_ne_zero (h : ¬(a = 0 ∧ b = 0 ∧ c = 0)) : fccVector a b c ≠ 0 := by
  intro h0
  have h2 : ‖fccVector a b c‖ ^ 2 = 2 * ((a ^ 2 + b ^ 2 + c ^ 2 + a * c - b * c : ℤ) : ℝ) :=
    sq_norm_fccVector a b c
  rw [h0, norm_zero] at h2
  have h3 : (1 : ℝ) ≤ ((a ^ 2 + b ^ 2 + c ^ 2 + a * c - b * c : ℤ) : ℝ) := by
    exact_mod_cast one_le_fcc_form h
  linarith

lemma fccVector_injective : Function.Injective fun p : ℤ × ℤ × ℤ ↦ fccVector p.1 p.2.1 p.2.2 := by
  rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
  have h0 : fccVector a b c 0 = fccVector a' b' c' 0 := congrArg (· 0) h
  have h1 : fccVector a b c 1 = fccVector a' b' c' 1 := congrArg (· 1) h
  have h2 : fccVector a b c 2 = fccVector a' b' c' 2 := congrArg (· 2) h
  simp only [fccVector] at h0 h1 h2
  norm_num at h0 h1 h2
  have h0' : a + b = a' + b' := by
    exact_mod_cast h0
  have h1' : a - b + c = a' - b' + c' := by
    exact_mod_cast h1
  have h2' : c = c' := by
    exact_mod_cast h2
  simp only [Prod.mk.injEq]
  omega

/-- **The minimum of the face-centred cubic lattice is `√2`.** -/
lemma minimum_faceCentredCubicLattice : minimum faceCentredCubicLattice = √2 := by
  refine IsLeast.csInf_eq ⟨⟨fccVector 1 0 0, ⟨mem_faceCentredCubicLattice_iff.mpr ⟨1, 0, 0, rfl⟩,
    fccVector_ne_zero (by decide)⟩, ?_⟩, ?_⟩
  · rw [← Real.sqrt_sq (norm_nonneg _), sq_norm_fccVector]
    norm_num
  · rintro _ ⟨y, ⟨hy, hy0⟩, rfl⟩
    rcases mem_faceCentredCubicLattice_iff.mp hy with ⟨a, b, c, rfl⟩
    have h1 : (1 : ℝ) ≤ ((a ^ 2 + b ^ 2 + c ^ 2 + a * c - b * c : ℤ) : ℝ) := by
      exact_mod_cast one_le_fcc_form fun h ↦ hy0 (by
        rw [h.1, h.2.1, h.2.2]
        ext i
        fin_cases i <;> simp [fccVector])
    rw [← Real.sqrt_sq (norm_nonneg _), sq_norm_fccVector]
    exact Real.sqrt_le_sqrt (by linarith)

/-- The twelve triples `(a, b, c)` with `a² + b² + c² + a c - b c = 1`. -/
def fccMinimalTriples : Finset (ℤ × ℤ × ℤ) :=
  {(1, 0, 0), (-1, 0, 0), (0, 1, 0), (0, -1, 0), (0, 0, 1), (-1, 0, 1), (0, 1, 1), (-1, 1, 1),
    (0, 0, -1), (1, 0, -1), (0, -1, -1), (1, -1, -1)}

variable (a b c) in
lemma mem_fccMinimalTriples_iff :
    (a, b, c) ∈ fccMinimalTriples ↔ a ^ 2 + b ^ 2 + c ^ 2 + a * c - b * c = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [fccMinimalTriples, Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;> norm_num
  · have hc1 : c ≤ 1 := by
      nlinarith [sq_nonneg (2 * a + c), sq_nonneg (2 * b - c)]
    have hc2 : -1 ≤ c := by
      nlinarith [sq_nonneg (2 * a + c), sq_nonneg (2 * b - c)]
    have ha1 : a ≤ 1 := by
      nlinarith [sq_nonneg (2 * b - c), sq_nonneg c, sq_nonneg (2 * a + c - 2)]
    have ha2 : -1 ≤ a := by
      nlinarith [sq_nonneg (2 * b - c), sq_nonneg c, sq_nonneg (2 * a + c + 2)]
    have hb1 : b ≤ 1 := by
      nlinarith [sq_nonneg (2 * a + c), sq_nonneg c, sq_nonneg (2 * b - c - 2)]
    have hb2 : -1 ≤ b := by
      nlinarith [sq_nonneg (2 * a + c), sq_nonneg c, sq_nonneg (2 * b - c + 2)]
    interval_cases a <;> interval_cases b <;> interval_cases c <;> simp_all [fccMinimalTriples]

/-- **The minimal vectors of the face-centred cubic lattice** are the twelve vectors
`a (1, 1, 0) + b (1, -1, 0) + c (0, 1, -1)`, `(a, b, c) ∈ fccMinimalTriples`. -/
lemma minimalVectors_faceCentredCubicLattice : minimalVectors faceCentredCubicLattice =
    (fun p : ℤ × ℤ × ℤ ↦ fccVector p.1 p.2.1 p.2.2) '' ↑fccMinimalTriples := by
  ext y
  refine ⟨fun hy ↦ ?_, ?_⟩
  · rcases mem_faceCentredCubicLattice_iff.mp hy.1 with ⟨a, b, c, rfl⟩
    have h2 : ‖fccVector a b c‖ ^ 2 = 2 * ((a ^ 2 + b ^ 2 + c ^ 2 + a * c - b * c : ℤ) : ℝ) :=
      sq_norm_fccVector a b c
    rw [hy.2.2, minimum_faceCentredCubicLattice, Real.sq_sqrt zero_le_two] at h2
    have h1' : ((a ^ 2 + b ^ 2 + c ^ 2 + a * c - b * c : ℤ) : ℝ) = 1 := by
      linarith
    have h1 : a ^ 2 + b ^ 2 + c ^ 2 + a * c - b * c = 1 := by
      exact_mod_cast h1'
    exact ⟨(a, b, c), (mem_fccMinimalTriples_iff a b c).mpr h1, rfl⟩
  · rintro ⟨⟨a, b, c⟩, hp, rfl⟩
    have h1 : a ^ 2 + b ^ 2 + c ^ 2 + a * c - b * c = 1 := (mem_fccMinimalTriples_iff a b c).mp hp
    refine ⟨mem_faceCentredCubicLattice_iff.mpr ⟨a, b, c, rfl⟩, fccVector_ne_zero fun h ↦ by
      rcases h with ⟨rfl, rfl, rfl⟩
      norm_num at h1, ?_⟩
    rw [minimum_faceCentredCubicLattice, ← Real.sqrt_sq (norm_nonneg _), sq_norm_fccVector, h1]
    norm_num

lemma fccVector_mem_minimalVectors (h : a ^ 2 + b ^ 2 + c ^ 2 + a * c - b * c = 1) :
    fccVector a b c ∈ minimalVectors faceCentredCubicLattice := by
  rw [minimalVectors_faceCentredCubicLattice]
  exact ⟨(a, b, c), (mem_fccMinimalTriples_iff a b c).mpr h, rfl⟩

/-- **The face-centred cubic lattice is perfect** (LMFDB `lattice.perfect`,
`lattice.spherical_design`): the matrices `x xᵀ` of its minimal vectors `(1, ±1, 0)`, `(1, 0, ±1)`
and `(0, 1, ±1)` span the symmetric `3 × 3` real matrices. -/
lemma isPerfect_faceCentredCubicLattice : IsPerfect faceCentredCubicLattice := by
  intro A hA
  have h10 : A 1 0 = A 0 1 := hA.apply 0 1
  have h20 : A 2 0 = A 0 2 := hA.apply 0 2
  have h21 : A 2 1 = A 1 2 := hA.apply 1 2
  have hA' : A = ((A 0 0 + A 1 1 - A 2 2) / 4 + A 0 1 / 2) •
        vecMulVec (fccVector 1 0 0).ofLp (fccVector 1 0 0).ofLp +
      ((A 0 0 + A 1 1 - A 2 2) / 4 - A 0 1 / 2) •
        vecMulVec (fccVector 0 1 0).ofLp (fccVector 0 1 0).ofLp +
      ((A 0 0 - A 1 1 + A 2 2) / 4 + A 0 2 / 2) •
        vecMulVec (fccVector 1 0 (-1)).ofLp (fccVector 1 0 (-1)).ofLp +
      ((A 0 0 - A 1 1 + A 2 2) / 4 - A 0 2 / 2) •
        vecMulVec (fccVector 0 1 1).ofLp (fccVector 0 1 1).ofLp +
      ((-A 0 0 + A 1 1 + A 2 2) / 4 + A 1 2 / 2) •
        vecMulVec (fccVector 1 (-1) (-1)).ofLp (fccVector 1 (-1) (-1)).ofLp +
      ((-A 0 0 + A 1 1 + A 2 2) / 4 - A 1 2 / 2) •
        vecMulVec (fccVector 0 0 1).ofLp (fccVector 0 0 1).ofLp := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [fccVector, h10, h20, h21] <;> ring1
  rw [hA']
  refine Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (Submodule.add_mem _
    (Submodule.add_mem _ ?_ ?_) ?_) ?_) ?_) ?_ <;> refine Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, fccVector_mem_minimalVectors ?_, rfl⟩) <;> norm_num

lemma totalDegree_le_four_of_linear {p q : MvPolynomial (Fin 3) ℝ} (hp : p.totalDegree ≤ 1)
    (hq : q.totalDegree ≤ 1) : (p ^ 4 + q ^ 4).totalDegree ≤ 4 :=
  (totalDegree_add _ _).trans (max_le ((totalDegree_pow _ 4).trans (by omega))
    ((totalDegree_pow _ 4).trans (by omega)))

lemma totalDegree_C_mul_X_add_C_mul_X_le (u v : ℝ) (i j : Fin 3) :
    (C u * X i + C v * X j : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 1 := by
  refine (totalDegree_add _ _).trans (max_le ?_ ?_) <;> refine (totalDegree_mul _ _).trans ?_ <;>
    rw [totalDegree_C, totalDegree_X]

/-- **The face-centred cubic lattice is not strongly perfect** (LMFDB
`lattice.spherical_design`): its minimal vectors are not a spherical `4`-design, as the rotation
`ZLattice.rotationThreeFourFive` changes the sum of `x₀⁴ + x₁⁴` over them but not its average over
the sphere. -/
lemma not_isStronglyPerfect_faceCentredCubicLattice :
    ¬IsStronglyPerfect faceCentredCubicLattice := by
  rintro ⟨-, hfin, hne, -, hpoly⟩
  set r : ℝ := minimum faceCentredCubicLattice
  let P₁ : MvPolynomial (Fin 3) ℝ := (C 1 * X 0 + C 0 * X 1) ^ 4 + (C 0 * X 0 + C 1 * X 1) ^ 4
  let P₂ : MvPolynomial (Fin 3) ℝ :=
    (C (3 / 5) * X 0 + C (-4 / 5) * X 1) ^ 4 + (C (4 / 5) * X 0 + C (3 / 5) * X 1) ^ 4
  have hpt (y : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      (P₁.eval fun i ↦ r * rotationThreeFourFive (y : EuclideanSpace ℝ (Fin 3)) i) =
        P₂.eval fun i ↦ r * (y : EuclideanSpace ℝ (Fin 3)) i := by
    simp only [P₁, P₂, rotationThreeFourFive_apply]
    simp
    ring1
  have havg : ⨍ y : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      P₂.eval (fun i ↦ r * (y : EuclideanSpace ℝ (Fin 3)) i) ∂volume.toSphere =
        ⨍ y : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
          P₁.eval (fun i ↦ r * (y : EuclideanSpace ℝ (Fin 3)) i) ∂volume.toSphere := by
    simp only [← hpt]
    exact rotationThreeFourFive.average_toSphere_comp (LinearIsometryEquiv.measurePreserving _)
      fun y ↦ P₁.eval fun i ↦ r * (y : EuclideanSpace ℝ (Fin 3)) i
  have hcard : (Nat.card (minimalVectors faceCentredCubicLattice) : ℝ)⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.mpr (Nat.card_pos_iff.mpr ⟨hne.to_subtype, hfin.to_subtype⟩).ne')
  have hsum : ∑ᶠ v ∈ minimalVectors faceCentredCubicLattice, P₂.eval (fun i ↦ v i) =
      ∑ᶠ v ∈ minimalVectors faceCentredCubicLattice, P₁.eval (fun i ↦ v i) := by
    refine mul_left_cancel₀ hcard ?_
    rw [← hpoly P₂ (totalDegree_le_four_of_linear (totalDegree_C_mul_X_add_C_mul_X_le _ _ _ _)
      (totalDegree_C_mul_X_add_C_mul_X_le _ _ _ _)), ← hpoly P₁ (totalDegree_le_four_of_linear
      (totalDegree_C_mul_X_add_C_mul_X_le _ _ _ _) (totalDegree_C_mul_X_add_C_mul_X_le _ _ _ _)),
      havg]
  simp only [minimalVectors_faceCentredCubicLattice, finsum_mem_image fccVector_injective.injOn,
    finsum_mem_coe_finset] at hsum
  simp [fccMinimalTriples, P₁, P₂, fccVector] at hsum
  norm_num at hsum

end ZLattice
