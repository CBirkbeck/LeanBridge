import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.IgusaLevelTwoModularity

/-!
# Riemann's theta relation in degree 2 and Ibukiyama's form `Z` on `Γ₀(2)`

The square of a theta constant of degree 2 is a quadratic form in the four theta constants
`θ_{a,0}(2Ω)`, `a ∈ {0, 1}²`, of the doubled argument (the duplication formula):
`θ_{μ,ν}(Ω)² = ∑_{a ∈ {0, 1}²} (-1)^{(a + μ)·ν} θ_{a,0}(2Ω) θ_{a+μ,0}(2Ω)`. In the double series
`θ_{μ,ν}(Ω)² = ∑_{n, m ∈ ℤ²} e^{πi(xᵀΩx + yᵀΩy + (x + y)ᵀν)}`, `x = n + μ/2`, `y = m + μ/2`, the
change of variables `n - m = 2k + a`, `n + m = 2l + a`, with `a ∈ {0, 1}²` and `k, l ∈ ℤ²`, gives
`xᵀΩx + yᵀΩy = 2uᵀΩu + 2wᵀΩw` with `u = k + a/2` and `w = l + (a + μ)/2`, and `(x + y)ᵀν = 2wᵀν`.

For the three nonzero `μ ∈ {0, 1}²` and the two `ν ∈ {0, 1}²` with `μ·ν` even, the difference of
the fourth powers is then the same, `16 θ₀₀₀₀(2Ω) θ₀₁₀₀(2Ω) θ₁₀₀₀(2Ω) θ₁₁₀₀(2Ω)`, which gives the
Riemann theta relations `θ₀₁₀₀⁴ - θ₀₁₁₀⁴ = θ₁₀₀₀⁴ - θ₁₀₀₁⁴ = θ₁₁₀₀⁴ - θ₁₁₁₁⁴`. Expanding all ten
`θ_m⁴` in the same way gives the linear relations by which Igusa's forms `x₆, …, x₁₀` of the knowl
`mf.siegel.family.gamma_2` are linear combinations of `x₁, …, x₅`. An element
`p = (A, B; 0, D)` of the Siegel parabolic subgroup `P(ℤ)` of `Sp(4, ℤ)` sends `θ_{μ,ν}⁴` to a
constant depending only on `μ` times `θ_{μ',ν'}⁴`, where `(μ', ν')` is the image of `(μ, ν)` under
the affine bijection `(μ, ν) ↦ (Aᵀμ, Dᵀ(ν + Sμ + diag S))`, `S = BAᵀ`, of the even characteristics
modulo 2 (`SiegelUpperHalfSpace.Ibukiyama.charMap`). So it sends the difference
`θ₀₁₀₀⁴ - θ₀₁₁₀⁴` to a constant times one of the six differences `±(θ_{μ',ν₀}⁴ - θ_{μ',ν₁}⁴)`,
whose squares agree by the Riemann relations, and the square of the constant is `1`. Hence
Ibukiyama's form `Z = (θ₀₁₀₀⁴ - θ₀₁₁₀⁴)² / 16384` of the knowl `mf.siegel.family.gamma0_2` is
invariant under `P(ℤ)`, so a Siegel modular form of weight 4 on `P(ℤ)`, and therefore on `Γ₀(2)`
(`SiegelUpperHalfSpace.Ibukiyama.Z_mem_gamma0_two_of_mem_parabolic`). With `X`, `Y` and `K`, this
proves the four modularity fields of `X`, `Y`, `Z`, `K` in Ibukiyama's structure theorem
`SiegelUpperHalfSpace.Ibukiyama.Gamma0TwoStructure`.

## Main results

* `SiegelUpperHalfSpace.thetaConstant_sq_eq_sum_double`: the duplication formula.
* `SiegelUpperHalfSpace.thetaConstant_pow_four_sub_eq_one_zero`,
  `SiegelUpperHalfSpace.thetaConstant_pow_four_sub_eq_one_one`: the Riemann theta relations
  `θ₀₁₀₀⁴ - θ₀₁₁₀⁴ = θ₁₀₀₀⁴ - θ₁₀₀₁⁴` and `θ₀₁₀₀⁴ - θ₀₁₁₀⁴ = θ₁₁₀₀⁴ - θ₁₁₁₁⁴`.
* `SiegelUpperHalfSpace.IgusaLevelTwo.x_mem_span`: the ten `xᵢ = ϑᵢ⁴` lie in the span of
  `x₁, …, x₅`.
* `SiegelUpperHalfSpace.Ibukiyama.Z_smul_of_mem_siegelParabolic`: `Z` is invariant under the
  Siegel parabolic subgroup of `Sp(4, ℤ)`.
* `SiegelUpperHalfSpace.Ibukiyama.Z_mem_parabolic`: `Z ∈ M₄(P(ℤ))`.
* `SiegelUpperHalfSpace.Ibukiyama.Z_mem_gamma0_two`: `Z ∈ M₄(Γ₀(2))`.
-/

open Complex Matrix Real

namespace SiegelUpperHalfSpace

variable (Ω : SiegelUpperHalfSpace (Fin 2)) (μ ν : Fin 2 → ℤ) (c : ℤ)

private lemma divModEquiv_two (y : ℤ) (a : Fin 2) :
    Int.divModEquiv 2 (c + y + a - (y - c)) = (c, a) :=
  (Int.divModEquiv 2).eq_symm_apply.mp <| by
    rw [Int.divModEquiv_symm_apply]
    push_cast
    ring1

/-- The bijection `(a, k, l) ↦ (k + l + a, l - k)` from `{0, 1}² × ℤ² × ℤ²` onto `ℤ² × ℤ²`, whose
inverse sorts `n - m` by its residue `a` modulo 2. -/
private def doublingEquiv :
    (Fin 2 × Fin 2) × (Fin 2 → ℤ) × (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) × (Fin 2 → ℤ) where
  toFun q := (q.2.1 + q.2.2 + ![(q.1.1 : ℤ), (q.1.2 : ℤ)], q.2.2 - q.2.1)
  invFun p := (((Int.divModEquiv 2 (p.1 0 - p.2 0)).2, (Int.divModEquiv 2 (p.1 1 - p.2 1)).2),
    ![(Int.divModEquiv 2 (p.1 0 - p.2 0)).1, (Int.divModEquiv 2 (p.1 1 - p.2 1)).1],
    p.2 + ![(Int.divModEquiv 2 (p.1 0 - p.2 0)).1, (Int.divModEquiv 2 (p.1 1 - p.2 1)).1])
  left_inv q := by
    rcases q with ⟨⟨a, b⟩, k, l⟩
    simp only [Pi.add_apply, Pi.sub_apply, cons_val_zero, cons_val_one, divModEquiv_two]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · ext i
      fin_cases i <;> rfl
    · ext i
      fin_cases i <;> simp
  right_inv p := by
    rcases p with ⟨n, m⟩
    have h (x y : ℤ) :
        (Int.divModEquiv 2 (x - y)).1 * 2 + ((Int.divModEquiv 2 (x - y)).2 : ℤ) = x - y := by
      have e : (Int.divModEquiv 2).symm (Int.divModEquiv 2 (x - y)) = x - y :=
        (Int.divModEquiv 2).symm_apply_apply (x - y)
      rwa [Int.divModEquiv_symm_apply, Nat.cast_ofNat] at e
    refine Prod.ext (funext <| Fin.forall_fin_two.mpr ⟨?_, ?_⟩) (add_sub_cancel_right _ _)
    · simp only [Pi.add_apply, cons_val_zero]
      linarith [h (n 0) (m 0)]
    · simp only [Pi.add_apply, cons_val_one, cons_val_fin_one]
      linarith [h (n 1) (m 1)]

/-- The term `e^{πi(xᵀΩx + xᵀν)}`, `x = n + μ/2`, of the series of the theta constant `θ_{μ,ν}`. -/
private noncomputable def seriesTerm (n : Fin 2 → ℤ) : ℂ :=
  cexp (π * I * ((fun i ↦ (n i : ℂ) + μ i / 2) ⬝ᵥ Ω.val *ᵥ (fun i ↦ (n i : ℂ) + μ i / 2) +
    (fun i ↦ (n i : ℂ) + μ i / 2) ⬝ᵥ fun i ↦ (ν i : ℂ)))

private lemma thetaConstant_eq_tsum : thetaConstant μ ν Ω = ∑' n, seriesTerm Ω μ ν n :=
  rfl

private lemma summable_norm_seriesTerm : Summable fun n ↦ ‖seriesTerm Ω μ ν n‖ :=
  (summable_thetaConstant_term Ω μ ν).norm

private lemma seriesTerm_mul_seriesTerm (a k l : Fin 2 → ℤ) :
    seriesTerm Ω μ ν (k + l + a) * seriesTerm Ω μ ν (l - k) =
      (-1) ^ ((a + μ) ⬝ᵥ ν) * (seriesTerm Ω.double a 0 k * seriesTerm Ω.double (a + μ) 0 l) := by
  have he (n : ℤ) : (-1 : ℂ) ^ n = cexp (π * I * n) := by
    rw [mul_comm, Complex.exp_int_mul, exp_pi_mul_I]
  rw [seriesTerm, seriesTerm, seriesTerm, seriesTerm, he, ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add]
  refine Complex.exp_eq_exp_iff_exists_int.mpr ⟨l ⬝ᵥ ν, ?_⟩
  simp [mulVec, double_val]
  ring1

/-- **The duplication formula for the theta constants of degree 2**:
`θ_{μ,ν}(Ω)² = ∑_{a ∈ {0, 1}²} (-1)^{(a + μ)·ν} θ_{a,0}(2Ω) θ_{a+μ,0}(2Ω)`. The double series of
`θ_{μ,ν}(Ω)²` over `(n, m) ∈ ℤ² × ℤ²` is rearranged through the bijection `(a, k, l) ↦ (n, m)`,
`n = k + l + a`, `m = l - k`, which splits it into four products of theta series in `2Ω`. -/
lemma thetaConstant_sq_eq_sum_double : thetaConstant μ ν Ω ^ 2 = ∑ a : Fin 2 × Fin 2,
    (-1) ^ ((![(a.1 : ℤ), (a.2 : ℤ)] + μ) ⬝ᵥ ν) *
      (thetaConstant ![(a.1 : ℤ), (a.2 : ℤ)] 0 Ω.double *
        thetaConstant (![(a.1 : ℤ), (a.2 : ℤ)] + μ) 0 Ω.double) := by
  have hsum : Summable fun q ↦
      seriesTerm Ω μ ν (doublingEquiv q).1 * seriesTerm Ω μ ν (doublingEquiv q).2 :=
    doublingEquiv.summable_iff.mpr <| summable_mul_of_summable_norm
      (summable_norm_seriesTerm Ω μ ν) (summable_norm_seriesTerm Ω μ ν)
  rw [sq, thetaConstant_eq_tsum, tsum_mul_tsum_of_summable_norm (summable_norm_seriesTerm Ω μ ν)
    (summable_norm_seriesTerm Ω μ ν), ← doublingEquiv.tsum_eq,
    hsum.tsum_prod' fun a ↦ hsum.prod_factor a, tsum_fintype]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [thetaConstant_eq_tsum, thetaConstant_eq_tsum, tsum_mul_tsum_of_summable_norm
    (summable_norm_seriesTerm _ _ _) (summable_norm_seriesTerm _ _ _), ← tsum_mul_left]
  exact tsum_congr fun kl ↦ seriesTerm_mul_seriesTerm Ω μ ν _ kl.1 kl.2

lemma thetaConstant_cons_two : thetaConstant ![c, 2] ν Ω = thetaConstant ![c, 0] ν Ω := by
  rw [← thetaConstant_add_two_smul_left ![c, 0] ν Ω ![0, 1]]
  congr 1
  ext i
  fin_cases i <;> simp

lemma thetaConstant_two_cons : thetaConstant ![2, c] ν Ω = thetaConstant ![0, c] ν Ω := by
  rw [← thetaConstant_add_two_smul_left ![0, c] ν Ω ![1, 0]]
  congr 1
  ext i
  fin_cases i <;> simp

private lemma pow_four_eq_sq_sq (z : ℂ) : z ^ 4 = (z ^ 2) ^ 2 := by
  ring1

private lemma thetaConstant_zero_one_pow_four_sub :
    thetaConstant ![0, 1] ![0, 0] Ω ^ 4 - thetaConstant ![0, 1] ![1, 0] Ω ^ 4 =
      16 * (thetaConstant ![0, 0] 0 Ω.double * thetaConstant ![0, 1] 0 Ω.double *
        thetaConstant ![1, 0] 0 Ω.double * thetaConstant ![1, 1] 0 Ω.double) := by
  rw [pow_four_eq_sq_sq, pow_four_eq_sq_sq, thetaConstant_sq_eq_sum_double,
    thetaConstant_sq_eq_sum_double]
  simp [Fintype.sum_prod_type, thetaConstant_cons_two]
  ring1

private lemma thetaConstant_one_zero_pow_four_sub :
    thetaConstant ![1, 0] ![0, 0] Ω ^ 4 - thetaConstant ![1, 0] ![0, 1] Ω ^ 4 =
      16 * (thetaConstant ![0, 0] 0 Ω.double * thetaConstant ![0, 1] 0 Ω.double *
        thetaConstant ![1, 0] 0 Ω.double * thetaConstant ![1, 1] 0 Ω.double) := by
  rw [pow_four_eq_sq_sq, pow_four_eq_sq_sq, thetaConstant_sq_eq_sum_double,
    thetaConstant_sq_eq_sum_double]
  simp [Fintype.sum_prod_type, thetaConstant_two_cons]
  ring1

private lemma thetaConstant_one_one_pow_four_sub :
    thetaConstant ![1, 1] ![0, 0] Ω ^ 4 - thetaConstant ![1, 1] ![1, 1] Ω ^ 4 =
      16 * (thetaConstant ![0, 0] 0 Ω.double * thetaConstant ![0, 1] 0 Ω.double *
        thetaConstant ![1, 0] 0 Ω.double * thetaConstant ![1, 1] 0 Ω.double) := by
  rw [pow_four_eq_sq_sq, pow_four_eq_sq_sq, thetaConstant_sq_eq_sum_double,
    thetaConstant_sq_eq_sum_double]
  simp [Fintype.sum_prod_type, thetaConstant_cons_two, thetaConstant_two_cons]
  ring1

/-- **Riemann's theta relation** `θ₀₁₀₀⁴ - θ₀₁₁₀⁴ = θ₁₀₀₀⁴ - θ₁₀₀₁⁴` in degree 2: by the duplication
formula, both sides are `16 θ₀₀₀₀(2Ω) θ₀₁₀₀(2Ω) θ₁₀₀₀(2Ω) θ₁₁₀₀(2Ω)`. -/
lemma thetaConstant_pow_four_sub_eq_one_zero :
    thetaConstant ![0, 1] ![0, 0] Ω ^ 4 - thetaConstant ![0, 1] ![1, 0] Ω ^ 4 =
      thetaConstant ![1, 0] ![0, 0] Ω ^ 4 - thetaConstant ![1, 0] ![0, 1] Ω ^ 4 := by
  rw [thetaConstant_zero_one_pow_four_sub, thetaConstant_one_zero_pow_four_sub]

/-- **Riemann's theta relation** `θ₀₁₀₀⁴ - θ₀₁₁₀⁴ = θ₁₁₀₀⁴ - θ₁₁₁₁⁴` in degree 2: by the duplication
formula, both sides are `16 θ₀₀₀₀(2Ω) θ₀₁₀₀(2Ω) θ₁₀₀₀(2Ω) θ₁₁₀₀(2Ω)`. -/
lemma thetaConstant_pow_four_sub_eq_one_one :
    thetaConstant ![0, 1] ![0, 0] Ω ^ 4 - thetaConstant ![0, 1] ![1, 0] Ω ^ 4 =
      thetaConstant ![1, 1] ![0, 0] Ω ^ 4 - thetaConstant ![1, 1] ![1, 1] Ω ^ 4 := by
  rw [thetaConstant_zero_one_pow_four_sub, thetaConstant_one_one_pow_four_sub]

private lemma thetaConstant_pow_four_six : thetaConstant ![0, 1] ![1, 0] Ω ^ 4 =
    thetaConstant ![0, 0] ![0, 0] Ω ^ 4 - thetaConstant ![0, 0] ![0, 1] Ω ^ 4 +
      thetaConstant ![0, 0] ![1, 0] Ω ^ 4 - thetaConstant ![0, 0] ![1, 1] Ω ^ 4 -
        thetaConstant ![0, 1] ![0, 0] Ω ^ 4 := by
  simp only [pow_four_eq_sq_sq, thetaConstant_sq_eq_sum_double]
  simp [Fintype.sum_prod_type, thetaConstant_cons_two]
  ring1

private lemma thetaConstant_pow_four_seven : thetaConstant ![1, 0] ![0, 0] Ω ^ 4 =
    thetaConstant ![0, 0] ![0, 1] Ω ^ 4 - thetaConstant ![0, 0] ![1, 0] Ω ^ 4 +
      thetaConstant ![0, 1] ![0, 0] Ω ^ 4 := by
  simp only [pow_four_eq_sq_sq, thetaConstant_sq_eq_sum_double]
  simp [Fintype.sum_prod_type, thetaConstant_cons_two, thetaConstant_two_cons]
  ring1

private lemma thetaConstant_pow_four_eight : thetaConstant ![1, 0] ![0, 1] Ω ^ 4 =
    thetaConstant ![0, 0] ![0, 0] Ω ^ 4 - thetaConstant ![0, 0] ![1, 1] Ω ^ 4 -
      thetaConstant ![0, 1] ![0, 0] Ω ^ 4 := by
  simp only [pow_four_eq_sq_sq, thetaConstant_sq_eq_sum_double]
  simp [Fintype.sum_prod_type, thetaConstant_cons_two, thetaConstant_two_cons]
  ring1

private lemma thetaConstant_pow_four_nine : thetaConstant ![1, 1] ![0, 0] Ω ^ 4 =
    thetaConstant ![0, 0] ![1, 1] Ω ^ 4 - thetaConstant ![0, 0] ![1, 0] Ω ^ 4 +
      thetaConstant ![0, 1] ![0, 0] Ω ^ 4 := by
  simp only [pow_four_eq_sq_sq, thetaConstant_sq_eq_sum_double]
  simp [Fintype.sum_prod_type, thetaConstant_cons_two, thetaConstant_two_cons]
  ring1

private lemma thetaConstant_pow_four_ten : thetaConstant ![1, 1] ![1, 1] Ω ^ 4 =
    thetaConstant ![0, 0] ![0, 0] Ω ^ 4 - thetaConstant ![0, 0] ![0, 1] Ω ^ 4 -
      thetaConstant ![0, 1] ![0, 0] Ω ^ 4 := by
  simp only [pow_four_eq_sq_sq, thetaConstant_sq_eq_sum_double]
  simp [Fintype.sum_prod_type, thetaConstant_cons_two, thetaConstant_two_cons]
  ring1

namespace IgusaLevelTwo

lemma x_five_eq : x 5 = x 0 - x 1 + x 2 - x 3 - x 4 := by
  ext Ω
  simpa [x, thetaEven, evenChar] using thetaConstant_pow_four_six Ω

lemma x_six_eq : x 6 = x 1 - x 2 + x 4 := by
  ext Ω
  simpa [x, thetaEven, evenChar] using thetaConstant_pow_four_seven Ω

lemma x_seven_eq : x 7 = x 0 - x 3 - x 4 := by
  ext Ω
  simpa [x, thetaEven, evenChar] using thetaConstant_pow_four_eight Ω

lemma x_eight_eq : x 8 = x 3 - x 2 + x 4 := by
  ext Ω
  simpa [x, thetaEven, evenChar] using thetaConstant_pow_four_nine Ω

lemma x_nine_eq : x 9 = x 0 - x 1 - x 4 := by
  ext Ω
  simpa [x, thetaEven, evenChar] using thetaConstant_pow_four_ten Ω

/-- **The fourth powers `xᵢ = ϑᵢ⁴` are linear combinations of `x₁, …, x₅`** (LMFDB
`mf.siegel.family.gamma_2`): by the Riemann theta relations, which follow from the duplication
formula, `x₆ = x₁ - x₂ + x₃ - x₄ - x₅`, `x₇ = x₂ - x₃ + x₅`, `x₈ = x₁ - x₄ - x₅`,
`x₉ = x₄ - x₃ + x₅` and `x₁₀ = x₁ - x₂ - x₅`, in the knowl's numbering. So Igusa's ten forms `xᵢ`
lie in the algebra generated by `x₁, …, x₅`, as `IgusaLevelTwoStructure` requires. -/
lemma x_mem_span (i : Fin 10) :
    x i ∈ Submodule.span ℂ (Set.range fun j : Fin 5 ↦ x (Fin.castLE (by norm_num) j)) := by
  have h (j : Fin 5) : x (Fin.castLE (by norm_num) j) ∈ Submodule.span ℂ
      (Set.range fun j : Fin 5 ↦ x (Fin.castLE (by norm_num) j)) :=
    Submodule.subset_span ⟨j, rfl⟩
  fin_cases i
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3
  · exact h 4
  · exact (congrArg (· ∈ Submodule.span ℂ _) x_five_eq).mpr
      (sub_mem (sub_mem (add_mem (sub_mem (h 0) (h 1)) (h 2)) (h 3)) (h 4))
  · exact (congrArg (· ∈ Submodule.span ℂ _) x_six_eq).mpr (add_mem (sub_mem (h 1) (h 2)) (h 4))
  · exact (congrArg (· ∈ Submodule.span ℂ _) x_seven_eq).mpr (sub_mem (sub_mem (h 0) (h 3)) (h 4))
  · exact (congrArg (· ∈ Submodule.span ℂ _) x_eight_eq).mpr (add_mem (sub_mem (h 3) (h 2)) (h 4))
  · exact (congrArg (· ∈ Submodule.span ℂ _) x_nine_eq).mpr (sub_mem (sub_mem (h 0) (h 1)) (h 4))

end IgusaLevelTwo

namespace Ibukiyama

open SymplecticGroup

variable {p : symplecticGroup (Fin 2) ℤ} {A D S : Matrix (Fin 2) (Fin 2) (ZMod 2)}

private lemma thetaConstant_liftChar_smul_pow_four (m n : Fin 2 → ZMod 2)
    (hp : p ∈ siegelParabolic (Fin 2) ℤ) :
    letI S : Matrix (Fin 2) (Fin 2) ℤ := p.1.toBlocks₁₂ * p.1.toBlocks₁₁ᵀ
    letI w : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2) := charMap
      (p.1.toBlocks₁₁.map (Int.castRingHom (ZMod 2)))
        (p.1.toBlocks₂₂.map (Int.castRingHom (ZMod 2))) (S.map (Int.castRingHom (ZMod 2))) (m, n)
    thetaConstant (liftChar m) (liftChar n) (map (Int.castRingHom ℝ) p • Ω) ^ 4 =
      cexp (-(π * I * ((liftChar m ⬝ᵥ S *ᵥ liftChar m : ℤ) / 4 +
        (liftChar m ⬝ᵥ S.diag : ℤ) / 2))) ^ 4 *
          thetaConstant (liftChar w.1) (liftChar w.2) Ω ^ 4 := by
  rw [thetaConstant_smul_of_mem_siegelParabolic _ _ Ω hp, mul_pow]
  congr 1
  refine congrFun (IgusaLevelTwo.thetaConstant_pow_four_eq_of_cast_eq (fun i ↦ ?_) fun i ↦ ?_) Ω
  · rw [congrFun (intCast_liftChar _) i, charMap, intCast_mulVec_apply _ (intCast_liftChar m),
      transpose_map]
  · rw [congrFun (intCast_liftChar _) i, charMap, intCast_mulVec_apply _ (u' := n + _ + _),
      transpose_map]
    ext j
    simp [congrFun (intCast_liftChar n) j, intCast_mulVec_apply _ (intCast_liftChar m) j]

private lemma cexp_pow_four_sq (q d : ℤ) : (cexp (-(π * I * (q / 4 + d / 2))) ^ 4) ^ 2 = 1 := by
  rw [← pow_mul, ← Complex.exp_nat_mul]
  exact Complex.exp_eq_one_iff.mpr ⟨-(q + 2 * d), by
    push_cast
    ring1⟩

private lemma sub_sq_eq (x : (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2))
    (hm : x.1 ≠ 0) (h₀ : x.1 ⬝ᵥ x.2.1 = 0) (h₁ : x.1 ⬝ᵥ x.2.2 = 0) (hn : x.2.1 ≠ x.2.2) :
    (thetaConstant (liftChar x.1) (liftChar x.2.1) Ω ^ 4 -
      thetaConstant (liftChar x.1) (liftChar x.2.2) Ω ^ 4) ^ 2 =
        (thetaConstant ![0, 1] ![0, 0] Ω ^ 4 - thetaConstant ![0, 1] ![1, 0] Ω ^ 4) ^ 2 := by
  have h : x ∈ ({(![0, 1], ![0, 0], ![1, 0]), (![0, 1], ![1, 0], ![0, 0]),
      (![1, 0], ![0, 0], ![0, 1]), (![1, 0], ![0, 1], ![0, 0]), (![1, 1], ![0, 0], ![1, 1]),
      (![1, 1], ![1, 1], ![0, 0])} :
        Finset ((Fin 2 → ZMod 2) × (Fin 2 → ZMod 2) × (Fin 2 → ZMod 2))) := by
    revert x
    decide
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [liftChar_cons, ZMod.val_zero, ZMod.val_one, Nat.cast_zero, Nat.cast_one]
  · ring1
  · rw [thetaConstant_pow_four_sub_eq_one_zero]
  · rw [thetaConstant_pow_four_sub_eq_one_zero]
    ring1
  · rw [thetaConstant_pow_four_sub_eq_one_one]
  · rw [thetaConstant_pow_four_sub_eq_one_one]
    ring1

private lemma sub_sq_charMap (hDA : D * Aᵀ = 1) (hS : Sᵀ = S) :
    (thetaConstant (liftChar (charMap A D S (![0, 1], ![0, 0])).1)
      (liftChar (charMap A D S (![0, 1], ![0, 0])).2) Ω ^ 4 -
        thetaConstant (liftChar (charMap A D S (![0, 1], ![1, 0])).1)
          (liftChar (charMap A D S (![0, 1], ![1, 0])).2) Ω ^ 4) ^ 2 =
      (thetaConstant ![0, 1] ![0, 0] Ω ^ 4 - thetaConstant ![0, 1] ![1, 0] Ω ^ 4) ^ 2 := by
  refine sub_sq_eq Ω ((charMap A D S (![0, 1], ![0, 0])).1, (charMap A D S (![0, 1], ![0, 0])).2,
    (charMap A D S (![0, 1], ![1, 0])).2) (fun h0 : Aᵀ *ᵥ ![0, 1] = 0 ↦ ?_)
    ((charMap_fst_dotProduct_snd (v := (![0, 1], ![0, 0])) hDA hS).trans (by decide))
      ((charMap_fst_dotProduct_snd (v := (![0, 1], ![1, 0])) hDA hS).trans (by decide)) fun h ↦ ?_
  · have h1 : (![0, 1] : Fin 2 → ZMod 2) = 0 := by
      rw [← one_mulVec ![0, 1], ← hDA, ← mulVec_mulVec, h0, mulVec_zero]
    exact absurd h1 (by decide)
  · have h1 : charMapInv A D S (charMap A D S (![0, 1], ![0, 0])) =
        charMapInv A D S (charMap A D S (![0, 1], ![1, 0])) :=
      congrArg (charMapInv A D S) (Prod.ext rfl h)
    rw [charMapInv_charMap _ hDA, charMapInv_charMap _ hDA] at h1
    exact absurd h1 (by decide)

private lemma Z_eq_liftChar : Z Ω = (thetaConstant (liftChar ![0, 1]) (liftChar ![0, 0]) Ω ^ 4 -
    thetaConstant (liftChar ![0, 1]) (liftChar ![1, 0]) Ω ^ 4) ^ 2 / 16384 := by
  simp only [liftChar_cons, ZMod.val_zero, ZMod.val_one, Nat.cast_zero, Nat.cast_one]
  rfl

/-- **`Z` is invariant under the Siegel parabolic subgroup of `Sp(4, ℤ)`**: `p = (A, B; 0, D)`
multiplies `θ₀₁₀₀⁴` and `θ₀₁₁₀⁴` by the same constant, whose square is `1`, and sends them to
`θ_{μ',ν'₀}⁴` and `θ_{μ',ν'₁}⁴`, where `(μ', ν'ⱼ)` are the images of their characteristics under the
bijection `(μ, ν) ↦ (Aᵀμ, Dᵀ(ν + Sμ + diag S))`, `S = BAᵀ`, of the even characteristics modulo 2.
As `μ' ≠ 0` and `ν'₀ ≠ ν'₁`, the Riemann theta relations give
`(θ_{μ',ν'₀}⁴ - θ_{μ',ν'₁}⁴)² = (θ₀₁₀₀⁴ - θ₀₁₁₀⁴)²`. -/
lemma Z_smul_of_mem_siegelParabolic (hp : p ∈ siegelParabolic (Fin 2) ℤ) :
    Z (map (Int.castRingHom ℝ) p • Ω) = Z Ω := by
  have hS : (p.1.toBlocks₁₂ * p.1.toBlocks₁₁ᵀ)ᵀ = p.1.toBlocks₁₂ * p.1.toBlocks₁₁ᵀ := by
    rw [transpose_mul, transpose_transpose, ← toBlocks₁₂_mul_transpose_toBlocks₁₁ hp]
  have hDA : p.1.toBlocks₂₂.map (Int.castRingHom (ZMod 2)) *
      (p.1.toBlocks₁₁.map (Int.castRingHom (ZMod 2)))ᵀ = 1 := by
    rw [← transpose_map, ← Matrix.map_mul, toBlocks₂₂_mul_transpose_toBlocks₁₁ hp,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hS' : ((p.1.toBlocks₁₂ * p.1.toBlocks₁₁ᵀ).map (Int.castRingHom (ZMod 2)))ᵀ =
      (p.1.toBlocks₁₂ * p.1.toBlocks₁₁ᵀ).map (Int.castRingHom (ZMod 2)) := by
    rw [← transpose_map, hS]
  rw [Z_eq_liftChar (map (Int.castRingHom ℝ) p • Ω), thetaConstant_liftChar_smul_pow_four Ω _ _ hp,
    thetaConstant_liftChar_smul_pow_four Ω _ _ hp, ← mul_sub, mul_pow, cexp_pow_four_sq, one_mul]
  exact congrArg (· / 16384) (sub_sq_charMap Ω hDA hS')

/-- **`Z` is a Siegel modular form of weight 4 on the Siegel parabolic subgroup of `Sp(4, ℤ)`**:
it is holomorphic, invariant under `P(ℤ)`, and `det(cΩ + d)⁴ = (det D)⁴ = 1` there. -/
lemma Z_mem_parabolic : Z ∈ scalarModularForms 4 parabolic := by
  rw [mem_scalarModularForms_iff]
  refine ⟨isHolomorphic_Z, ?_⟩
  rintro ⟨_, p, hp, rfl⟩ τ
  rw [map_algebraMap_map_intCast, Z_smul_of_mem_siegelParabolic τ hp, zpow_ofNat,
    pow_four_eq_sq_sq, det_denom_sq_of_mem_siegelParabolic τ hp, one_pow, one_mul]

/-- **`Z` is a Siegel modular form of weight 4 on `Γ₀(2)`** (LMFDB `mf.siegel.family.gamma0_2`):
it is invariant under the Siegel parabolic subgroup, by the Riemann theta relations, and transforms
with weight 4 under `ι₁(1, 0; 2, 1)`, and these generate `Γ₀(2)`. -/
lemma Z_mem_gamma0_two : Z ∈ scalarModularForms 4 (gamma0 2) :=
  Z_mem_gamma0_two_of_mem_parabolic Z_mem_parabolic

end Ibukiyama

end SiegelUpperHalfSpace
