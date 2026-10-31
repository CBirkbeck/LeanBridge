import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.GaloisOrbit

/-!
# Koecher's principle

For a Siegel modular form `f(τ) = ∑_{n ∈ L_Γ^∨} a(n) e^{2πi tr(nτ)}` of degree `g ≥ 2` and weight
`ρ` on an arithmetic subgroup `Γ` of `Sp(2g, ℚ)`, Koecher's principle says that `a(n) ≠ 0` only for
positive semidefinite `n`, which is why no condition at the cusps is imposed in the definition of
Siegel modular forms of degree `g ≥ 2` (`SiegelUpperHalfSpace.modularForms`).

The proof follows Koecher (and Freitag's book): the elements `(U, 0; 0, U⁻ᵀ)` of `Γ`, with `U` in
a finite index subgroup of `GL(g, ℤ)`, act on `ℋ_g` by `τ ↦ U τ Uᵀ` with automorphy factor `U⁻ᵀ`,
so the transformation law and the uniqueness of Fourier expansions give
`a(Uᵀ n U) = ρ(Uᵀ) a(n)`. If `xᵀ n x < 0`, the unipotent `U = 1 + x yᵀ` with `yᵀ x = 0` (which
exists as `g ≥ 2`) moves `n` along an orbit on which `tr((U^s)ᵀ n U^s)` decreases like `-c s²`;
the terms of the Fourier series at `τ = i 1_g` then grow along the orbit, which contradicts their
convergence to `0`.

## Main definitions

* `SymplecticGroup.levi`: the Levi embedding `U ↦ (U, 0; 0, U⁻ᵀ)` of `GL(g, R)` in `Sp(2g, R)`.

## Main results

* `SiegelUpperHalfSpace.koecherPrinciple` (LMFDB `mf.siegel.koecher.principle`): Koecher's
  principle `SiegelUpperHalfSpace.KoecherPrinciple` holds for every arithmetic subgroup `Γ` of
  `Sp(2g, ℚ)` and every finite-dimensional representation `ρ`.
-/

open Complex Equiv Filter Matrix Module Real

open scoped Topology

namespace Matrix

variable {l : Type*} [Fintype l] {T : Matrix l l ℚ}

private lemma exists_int_dotProduct_mulVec_neg (hT : Tᵀ = T) (h : ¬T.PosSemidef) :
    ∃ x : l → ℤ, (fun i ↦ (x i : ℚ)) ⬝ᵥ T *ᵥ (fun i ↦ (x i : ℚ)) < 0 := by
  have hH : T.IsHermitian := by
    rw [IsHermitian, conjTranspose_eq_transpose_of_trivial, hT]
  rw [posSemidef_iff_dotProduct_mulVec, not_and] at h
  rcases not_forall.mp (h hH) with ⟨x, hx⟩
  rw [star_trivial, not_le] at hx
  have hden (i : l) : ∃ z : ℤ, (z : ℚ) = ((∏ j, (x j).den : ℕ) : ℚ) * x i := by
    rcases Finset.dvd_prod_of_mem (fun j ↦ (x j).den) (Finset.mem_univ i) with ⟨k, hk⟩
    refine ⟨k * (x i).num, ?_⟩
    rw [hk, Int.cast_mul, ← Rat.mul_den_eq_num]
    push_cast
    ring1
  choose z hz using hden
  refine ⟨z, ?_⟩
  have hD : (0 : ℚ) < ((∏ j, (x j).den : ℕ) : ℚ) :=
    Nat.cast_pos.mpr <| Finset.prod_pos fun j _ ↦ (x j).den_pos
  have hzx : (fun i ↦ (z i : ℚ)) = ((∏ j, (x j).den : ℕ) : ℚ) • x := funext hz
  rw [hzx, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, smul_eq_mul]
  exact mul_neg_of_pos_of_neg hD (mul_neg_of_pos_of_neg hD hx)

variable [DecidableEq l]

private lemma exists_ne_zero_dotProduct_eq_zero (hl : 2 ≤ Fintype.card l) {x : l → ℤ}
    (hx : x ≠ 0) : ∃ y : l → ℤ, y ≠ 0 ∧ y ⬝ᵥ x = 0 := by
  rcases Function.ne_iff.mp hx with ⟨i, hi⟩
  rcases Fintype.exists_ne_of_one_lt_card hl i with ⟨j, hj⟩
  refine ⟨Pi.single j (x i) - Pi.single i (x j), fun h ↦ hi ?_, ?_⟩
  · simpa [hj] using congrFun h j
  · rw [sub_dotProduct, single_dotProduct, single_dotProduct, mul_comm, sub_self]

private lemma one_add_pow {R : Type*} [CommRing R] {E : Matrix l l R} (hE : E * E = 0) (k : ℕ) :
    (1 + E) ^ k = 1 + (k : R) • E := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, smul_mul_assoc, hE,
      smul_zero, add_zero, Nat.cast_succ, add_smul, one_smul, add_assoc, add_comm E]

variable (T) in
private lemma trace_transpose_mul_mul (x y : l → ℚ) (c : ℚ) :
    ((1 + c • vecMulVec x y)ᵀ * T * (1 + c • vecMulVec x y)).trace = T.trace +
      c * ((vecMulVec y x * T).trace + (T * vecMulVec x y).trace) +
        c ^ 2 * ((x ⬝ᵥ T *ᵥ x) * (y ⬝ᵥ y)) := by
  have h : (vecMulVec y x * T * vecMulVec x y).trace = (x ⬝ᵥ T *ᵥ x) * (y ⬝ᵥ y) := by
    rw [vecMulVec_mul, vecMulVec_mul_vecMulVec, trace_vecMulVec, dotProduct_smul, smul_eq_mul,
      dotProduct_mulVec]
  simp only [transpose_add, transpose_one, transpose_smul, transpose_vecMulVec, add_mul,
    Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, smul_mul_assoc, mul_smul_comm, trace_add,
    trace_smul, h]
  ring1

end Matrix

namespace SymplecticGroup

variable {l : Type*} [Fintype l] [DecidableEq l] {R : Type*} [CommRing R]

variable (l R) in
/-- The **Levi embedding** `U ↦ (U, 0; 0, U⁻ᵀ)` of `GL(g, R)` in `Sp(2g, R)`, whose image is the
Levi subgroup of the Siegel parabolic subgroup. -/
def levi : GL l R →* symplecticGroup l R where
  toFun U := ⟨fromBlocks U 0 0 (U⁻¹ : GL l R).valᵀ, fromBlocks_mem_iff.mpr ⟨by simp, by simp, by
    rw [transpose_zero, Matrix.zero_mul, sub_zero, ← transpose_mul, Units.inv_mul, transpose_one]⟩⟩
  map_one' := Subtype.ext <| by simp
  map_mul' U V := Subtype.ext <| by simp [fromBlocks_multiply]

lemma coe_levi (U : GL l R) :
    (levi l R U : Matrix (l ⊕ l) (l ⊕ l) R) = fromBlocks U 0 0 (U⁻¹ : GL l R).valᵀ :=
  rfl

end SymplecticGroup

namespace SiegelUpperHalfSpace

variable {l : Type*} [Fintype l] [DecidableEq l] {Γ : Subgroup (symplecticGroup l ℚ)} (U : GL l ℤ)
    {S : Type*} [CommRing S] (τ : SiegelUpperHalfSpace l) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL l ℂ) V) {f : SiegelUpperHalfSpace l → V} {a : dualLattice Γ → V}

/-- The image `(U, 0; 0, U⁻ᵀ)` in `Sp(2g, ℚ)` of `U ∈ GL(g, ℤ)`. -/
private noncomputable abbrev leviRat : symplecticGroup l ℚ :=
  SymplecticGroup.map (Int.castRingHom ℚ) (SymplecticGroup.levi l ℤ U)

/-- The point `i 1_g` of the Siegel upper half-space. -/
private noncomputable def basePoint : SiegelUpperHalfSpace l where
  val := I • 1
  transpose_val := by
    rw [transpose_smul, transpose_one]
  posDef_im := by
    convert PosDef.one (n := l) (R := ℝ)
    ext i j
    rcases eq_or_ne i j with rfl | hij <;> simp [*]

private lemma map_mul_map_inv :
    (U : Matrix l l ℤ).map (Int.cast : ℤ → S) * (U : Matrix l l ℤ)⁻¹.map Int.cast = 1 := by
  have h : ((U : Matrix l l ℤ) * (U⁻¹ : GL l ℤ).val).map (Int.castRingHom S) = 1 := by
    rw [Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  rwa [Matrix.map_mul, coe_units_inv] at h

private lemma map_inv_mul_map :
    (U : Matrix l l ℤ)⁻¹.map (Int.cast : ℤ → S) * (U : Matrix l l ℤ).map Int.cast = 1 := by
  have h : ((U⁻¹ : GL l ℤ).val * (U : Matrix l l ℤ)).map (Int.castRingHom S) = 1 := by
    rw [Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  rwa [Matrix.map_mul, coe_units_inv] at h

private lemma coe_map_leviRat : (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U) :
    Matrix (l ⊕ l) (l ⊕ l) ℝ) = fromBlocks ((U : Matrix l l ℤ).map (Int.cast : ℤ → ℝ)) 0 0
      ((U : Matrix l l ℤ)⁻¹ᵀ.map (Int.cast : ℤ → ℝ)) := by
  rw [SymplecticGroup.coe_map_apply, SymplecticGroup.coe_map_apply, SymplecticGroup.coe_levi,
    coe_units_inv]
  simp [fromBlocks_map]

private lemma num_levi : num (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U)) τ.val =
    (U : Matrix l l ℤ).map (Int.cast : ℤ → ℂ) * τ.val := by
  rw [num, coe_map_leviRat]
  simp [Function.comp_def]

private lemma denom_levi : denom (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U)) τ.val =
    (U : Matrix l l ℤ)⁻¹ᵀ.map (Int.cast : ℤ → ℂ) := by
  rw [denom, coe_map_leviRat]
  simp [Function.comp_def]

private lemma val_smul_levi : (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U) • τ).val =
    (U : Matrix l l ℤ).map (Int.cast : ℤ → ℂ) * τ.val * ((U : Matrix l l ℤ).map Int.cast)ᵀ := by
  have h :
      ((U : Matrix l l ℤ).map (Int.cast : ℤ → ℂ))ᵀ * (U : Matrix l l ℤ)⁻¹ᵀ.map Int.cast = 1 := by
    rw [transpose_map, ← transpose_mul, map_inv_mul_map, transpose_one]
  rw [val_smul, num_levi, denom_levi, inv_eq_left_inv h]

private lemma denomGL_levi : denomGL (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U)) τ =
    denomGL (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U)) basePoint :=
  Units.ext <| by rw [coe_denomGL, coe_denomGL, denom_levi, denom_levi]

private lemma coe_leviRat : (leviRat U : Matrix (l ⊕ l) (l ⊕ l) ℚ) =
    fromBlocks ((U : Matrix l l ℤ).map (Int.cast : ℤ → ℚ)) 0 0
      ((U : Matrix l l ℤ)⁻¹ᵀ.map (Int.cast : ℤ → ℚ)) := by
  rw [SymplecticGroup.coe_map_apply, SymplecticGroup.coe_levi, coe_units_inv]
  simp [fromBlocks_map]

private lemma coe_leviRat_inv :
    (((leviRat U)⁻¹ : symplecticGroup l ℚ) : Matrix (l ⊕ l) (l ⊕ l) ℚ) =
    fromBlocks ((U : Matrix l l ℤ)⁻¹.map (Int.cast : ℤ → ℚ)) 0 0
      ((U : Matrix l l ℤ)ᵀ.map (Int.cast : ℤ → ℚ)) := by
  rw [← map_inv, ← map_inv, SymplecticGroup.coe_map_apply, SymplecticGroup.coe_levi, inv_inv,
    coe_units_inv]
  simp [fromBlocks_map]

variable {U}

private lemma mul_mul_transpose_mem_translationLattice (hU : leviRat U ∈ Γ) {s : Matrix l l ℚ}
    (hs : s ∈ translationLattice Γ) : (U : Matrix l l ℤ).map (Int.cast : ℤ → ℚ) * s *
      ((U : Matrix l l ℤ).map Int.cast)ᵀ ∈ translationLattice Γ := by
  rcases hs with ⟨hs, γ, hγ, hγs⟩
  refine ⟨by rw [transpose_mul, transpose_mul, transpose_transpose, hs, Matrix.mul_assoc],
    leviRat U * γ * (leviRat U)⁻¹, Γ.mul_mem (Γ.mul_mem hU hγ) (Γ.inv_mem hU), ?_⟩
  rw [Submonoid.coe_mul, Submonoid.coe_mul, hγs, coe_leviRat, coe_leviRat_inv]
  simp [fromBlocks_multiply, map_mul_map_inv, transpose_map, ← transpose_mul]

private lemma transpose_mul_mul_mem_dualLattice (hU : leviRat U ∈ Γ) {n : Matrix l l ℚ}
    (hn : n ∈ dualLattice Γ) : ((U : Matrix l l ℤ).map (Int.cast : ℤ → ℚ))ᵀ * n *
      (U : Matrix l l ℤ).map Int.cast ∈ dualLattice Γ := by
  refine ⟨by rw [transpose_mul, transpose_mul, transpose_transpose, hn.1, Matrix.mul_assoc],
    fun s hs ↦ ?_⟩
  rcases hn.2 _ (mul_mul_transpose_mem_translationLattice hU hs) with ⟨z, hz⟩
  refine ⟨z, ?_⟩
  rw [← hz, ← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm]
  simp only [Matrix.mul_assoc]

private lemma leviRat_inv_mem (hU : leviRat U ∈ Γ) : leviRat U⁻¹ ∈ Γ := by
  simpa [leviRat] using Γ.inv_mem hU

private lemma transpose_mul_mul_map_inv (n : Matrix l l S) :
    ((U : Matrix l l ℤ)⁻¹.map (Int.cast : ℤ → S))ᵀ *
      (((U : Matrix l l ℤ).map Int.cast)ᵀ * n * (U : Matrix l l ℤ).map Int.cast) *
        (U : Matrix l l ℤ)⁻¹.map Int.cast = n := by
  have h : ((U : Matrix l l ℤ)⁻¹.map (Int.cast : ℤ → S))ᵀ *
      (((U : Matrix l l ℤ).map Int.cast)ᵀ * n * (U : Matrix l l ℤ).map Int.cast) *
        (U : Matrix l l ℤ)⁻¹.map Int.cast = ((U : Matrix l l ℤ).map Int.cast *
          (U : Matrix l l ℤ)⁻¹.map Int.cast)ᵀ * n *
            ((U : Matrix l l ℤ).map Int.cast * (U : Matrix l l ℤ)⁻¹.map Int.cast) := by
    simp only [transpose_mul, Matrix.mul_assoc]
  rw [h, map_mul_map_inv, transpose_one, Matrix.one_mul, Matrix.mul_one]

variable (hU : leviRat U ∈ Γ) (k : ℕ) (n : dualLattice Γ) {ι : Type*} [Fintype ι] (b : Basis ι ℂ V)
    (D : GL l ℂ) (v : V) {x y : l → ℤ} (hxy : y ⬝ᵥ x = 0) {m : ℕ} (s : ℕ) {T : dualLattice Γ}

variable (U) in
/-- The bijection `n ↦ Uᵀ n U` of the dual lattice `L_Γ^∨`, for `U ∈ GL(g, ℤ)` with
`(U, 0; 0, U⁻ᵀ) ∈ Γ`. -/
private def dualConj : dualLattice Γ ≃ dualLattice Γ where
  toFun n := ⟨_, transpose_mul_mul_mem_dualLattice hU n.2⟩
  invFun n := ⟨_, transpose_mul_mul_mem_dualLattice (leviRat_inv_mem hU) n.2⟩
  left_inv n := Subtype.ext <| by
    simpa using transpose_mul_mul_map_inv (U := U) (n : Matrix l l ℚ)
  right_inv n := Subtype.ext <| by
    simpa using transpose_mul_mul_map_inv (U := U⁻¹) (n : Matrix l l ℚ)

private lemma coe_dualConj : (dualConj U hU n : Matrix l l ℚ) =
    ((U : Matrix l l ℤ).map (Int.cast : ℤ → ℚ))ᵀ * (n : Matrix l l ℚ) *
      (U : Matrix l l ℤ).map Int.cast :=
  rfl

private lemma fourierExp_smul_levi :
    fourierExp n (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U) • τ) =
      fourierExp (dualConj U hU n) τ := by
  have hc : (Rat.castHom ℂ) ∘ (Int.cast : ℤ → ℚ) = (Int.cast : ℤ → ℂ) :=
    funext fun z ↦ map_intCast (Rat.castHom ℂ) z
  rw [fourierExp, fourierExp, val_smul_levi, coe_dualConj]
  congr 2
  rw [← Rat.coe_castHom, Matrix.map_mul, Matrix.map_mul, transpose_map, Matrix.map_map, hc]
  simp only [Matrix.mul_assoc]
  rw [trace_mul_comm ((U : Matrix l l ℤ).map (Int.cast : ℤ → ℂ))ᵀ]
  simp only [Matrix.mul_assoc]

private lemma coe_dualConj_pow :
    (((dualConj U hU : Equiv.Perm (dualLattice Γ)) ^ k) n : Matrix l l ℚ) =
      (((U : Matrix l l ℤ).map (Int.cast : ℤ → ℚ)) ^ k)ᵀ * (n : Matrix l l ℚ) *
        ((U : Matrix l l ℤ).map Int.cast) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, coe_dualConj, ih, pow_succ, transpose_mul]
    simp only [Matrix.mul_assoc]

private lemma apply_dualConj (hΓ : SymplecticGroup.IsArithmetic Γ) (hf : f ∈ modularForms ρ Γ 1)
    (ha : HasSiegelFourierExpansion Γ f a) : a (dualConj U hU n) =
      ρ (denomGL (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U)) basePoint)⁻¹ (a n) := by
  have h₁ : HasSiegelFourierExpansion Γ
      (fun τ ↦ f (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U) • τ))
        (fun m ↦ a ((dualConj U hU).symm m)) := fun τ φ ↦ by
    rw [← (dualConj U hU).hasSum_iff]
    refine (ha (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U) • τ) φ).congr_fun fun n ↦ ?_
    simp only [Function.comp_apply, Equiv.symm_apply_apply, fourierExp_smul_levi τ hU]
  have h₂ : HasSiegelFourierExpansion Γ
      (fun τ ↦ f (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U) • τ)) (fun m ↦
        ρ (denomGL (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U)) basePoint) (a m)) :=
    fun τ φ ↦ by
      have h : f (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U) • τ) =
          ρ (denomGL (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U)) τ) (f τ) := by
        simpa using hf.2 ⟨leviRat U, hU⟩ τ
      beta_reduce
      rw [h, denomGL_levi U τ]
      exact ha τ (φ ∘ₗ ρ (denomGL (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U)) basePoint))
  have h₃ : a n = ρ (denomGL (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U)) basePoint)
      (a (dualConj U hU n)) := by
    simpa using congrFun (h₁.unique_of_isArithmetic hΓ h₂) (dualConj U hU n)
  rw [h₃, ← End.mul_apply, ← map_mul, inv_mul_cancel, map_one, End.one_apply]

private lemma apply_dualConj_pow (hΓ : SymplecticGroup.IsArithmetic Γ) (hf : f ∈ modularForms ρ Γ 1)
    (ha : HasSiegelFourierExpansion Γ f a) :
    a (((dualConj U hU : Equiv.Perm (dualLattice Γ)) ^ k) n) =
      (ρ (denomGL (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat U)) basePoint)⁻¹ ^ k) (a n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Perm.mul_apply, apply_dualConj ρ hU _ hΓ hf ha, ih, pow_succ', End.mul_apply]

/-! ### Growth of the Fourier coefficients along an orbit -/

private lemma norm_fourierExp_basePoint :
    ‖fourierExp n basePoint‖ = Real.exp (-2 * π * ((n : Matrix l l ℚ).trace : ℝ)) := by
  have ht :
      ((n : Matrix l l ℚ).map (Rat.cast : ℚ → ℂ)).trace = (((n : Matrix l l ℚ).trace : ℚ) : ℂ) := by
    simp [Matrix.trace]
  rw [fourierExp, Complex.norm_exp]
  congr 1
  simp [basePoint, ht]

private lemma finite_setOf_one_le (ha : HasSiegelFourierExpansion Γ f a) :
    {n | 1 ≤ ‖fourierExp n τ‖ * ‖b.equivFun (a n)‖}.Finite := by
  have hT : Tendsto (fun n ↦ fourierExp n τ • b.equivFun (a n)) cofinite (𝓝 0) :=
    tendsto_pi_nhds.mpr fun i ↦ by
      simpa using (ha τ (b.coord i)).summable.tendsto_cofinite_zero
  have h : ∀ᶠ n in cofinite, ‖fourierExp n τ • b.equivFun (a n)‖ < 1 :=
    (by simpa using hT.norm : Tendsto (fun n ↦ ‖fourierExp n τ • b.equivFun (a n)‖)
      cofinite (𝓝 0)).eventually (eventually_lt_nhds one_pos)
  simpa [norm_smul] using eventually_cofinite.mp h

private lemma norm_le_mul_norm : ‖b.equivFun v‖ ≤ max 1 ‖LinearMap.toContinuousLinearMap
    (b.equivFun.toLinearMap ∘ₗ ρ D ∘ₗ b.equivFun.symm.toLinearMap)‖ * ‖b.equivFun (ρ D⁻¹ v)‖ := by
  have hv : b.equivFun v = LinearMap.toContinuousLinearMap
      (b.equivFun.toLinearMap ∘ₗ ρ D ∘ₗ b.equivFun.symm.toLinearMap) (b.equivFun (ρ D⁻¹ v)) := by
    simp
  rw [hv]
  exact (ContinuousLinearMap.le_opNorm _ _).trans <|
    mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)

private lemma norm_le_pow_mul_norm : ‖b.equivFun v‖ ≤ max 1 ‖LinearMap.toContinuousLinearMap
    (b.equivFun.toLinearMap ∘ₗ ρ D ∘ₗ b.equivFun.symm.toLinearMap)‖ ^ k *
      ‖b.equivFun ((ρ D⁻¹ ^ k) v)‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    refine ih.trans ?_
    rw [pow_succ, mul_assoc, pow_succ', End.mul_apply]
    exact mul_le_mul_of_nonneg_left (norm_le_mul_norm ρ b D _) (pow_nonneg (by positivity) k)

private lemma tendsto_quadratic {α β γ : ℝ} (hγ : 0 < γ) :
    Tendsto (fun s : ℕ ↦ α + β * s + γ * s ^ 2) atTop atTop := by
  refine tendsto_atTop_atTop.mpr fun M ↦ ⟨⌈(|α| + |β| + |M|) / γ⌉₊ + 1, fun s hs ↦ ?_⟩
  have hs₁ : (1 : ℝ) ≤ s := by exact_mod_cast (Nat.le_add_left 1 _).trans hs
  have hs₂ : (|α| + |β| + |M|) / γ ≤ s :=
    (Nat.le_ceil _).trans <| by exact_mod_cast (Nat.le_succ _).trans hs
  have hs₃ : |α| + |β| + |M| ≤ γ * s := by
    rwa [div_le_iff₀ hγ, mul_comm] at hs₂
  nlinarith [le_abs_self M, neg_abs_le α, neg_abs_le β, abs_nonneg α, abs_nonneg β,
    abs_nonneg M, mul_le_mul_of_nonneg_right hs₃ (zero_le_one.trans hs₁)]

/-- The unipotent matrix `1 + x yᵀ ∈ GL(g, ℤ)`, for integral vectors with `yᵀ x = 0`, whose
inverse is `1 - x yᵀ`. -/
private def unipotent : GL l ℤ where
  val := 1 + vecMulVec x y
  inv := 1 - vecMulVec x y
  val_inv := by
    rw [Matrix.mul_sub, Matrix.mul_one, add_mul, Matrix.one_mul, vecMulVec_mul_vecMulVec, hxy,
      zero_smul, vecMulVec_zero, add_zero, add_sub_cancel_right]
  inv_val := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, vecMulVec_mul_vecMulVec,
      hxy, zero_smul, vecMulVec_zero, add_zero, add_sub_cancel_right]

variable (m) in
private lemma map_unipotent_pow_pow :
    ((unipotent hxy ^ m : GL l ℤ).val.map (Int.cast : ℤ → ℚ)) ^ s =
      1 + ((s : ℚ) * m) • vecMulVec (fun i ↦ (x i : ℚ)) (fun i ↦ (y i : ℚ)) := by
  have hE : vecMulVec x y * vecMulVec x y = 0 := by
    rw [vecMulVec_mul_vecMulVec, hxy, zero_smul, vecMulVec_zero]
  have hq : ((m : ℚ) • vecMulVec (fun i ↦ (x i : ℚ)) (fun i ↦ (y i : ℚ))) *
      ((m : ℚ) • vecMulVec (fun i ↦ (x i : ℚ)) (fun i ↦ (y i : ℚ))) = 0 := by
    rw [smul_mul_smul, vecMulVec_mul_vecMulVec]
    have h : (fun i ↦ (y i : ℚ)) ⬝ᵥ (fun i ↦ (x i : ℚ)) = ((y ⬝ᵥ x : ℤ) : ℚ) := by
      simp [dotProduct]
    rw [h, hxy, Int.cast_zero, zero_smul, vecMulVec_zero, smul_zero]
  have hm : (unipotent hxy ^ m : GL l ℤ).val.map (Int.cast : ℤ → ℚ) =
      1 + (m : ℚ) • vecMulVec (fun i ↦ (x i : ℚ)) (fun i ↦ (y i : ℚ)) := by
    have hu : (unipotent hxy).val = 1 + vecMulVec x y := rfl
    rw [Units.val_pow_eq_pow_val, hu, one_add_pow hE]
    ext i j
    simp [vecMulVec, one_apply]
  rw [hm, one_add_pow hq, smul_smul]

variable (T) in
private lemma trace_dualConj_pow (hUm : leviRat (unipotent hxy ^ m) ∈ Γ) :
    ((((dualConj _ hUm : Equiv.Perm (dualLattice Γ)) ^ s) T : Matrix l l ℚ).trace : ℝ) =
      ((T : Matrix l l ℚ).trace : ℝ) + ((vecMulVec (fun i ↦ (y i : ℚ)) (fun i ↦ (x i : ℚ)) *
        (T : Matrix l l ℚ)).trace + ((T : Matrix l l ℚ) *
          vecMulVec (fun i ↦ (x i : ℚ)) (fun i ↦ (y i : ℚ))).trace : ℚ) * m * s +
            (((fun i ↦ (x i : ℚ)) ⬝ᵥ (T : Matrix l l ℚ) *ᵥ (fun i ↦ (x i : ℚ))) *
              ((fun i ↦ (y i : ℚ)) ⬝ᵥ (fun i ↦ (y i : ℚ))) : ℚ) * m ^ 2 * s ^ 2 := by
  rw [coe_dualConj_pow, map_unipotent_pow_pow, trace_transpose_mul_mul]
  push_cast
  ring1

variable [FiniteDimensional ℂ V] in
private lemma koecher_aux (hΓ : SymplecticGroup.IsArithmetic Γ) (hf : f ∈ modularForms ρ Γ 1)
    (ha : HasSiegelFourierExpansion Γ f a) (haT : a T ≠ 0) (hy : y ≠ 0)
    (hx : (fun i ↦ (x i : ℚ)) ⬝ᵥ (T : Matrix l l ℚ) *ᵥ (fun i ↦ (x i : ℚ)) < 0) (hm : 0 < m)
    (hUm : leviRat (unipotent hxy ^ m) ∈ Γ) : False := by
  let D : GL l ℂ :=
    denomGL (SymplecticGroup.map (algebraMap ℚ ℝ) (leviRat (unipotent hxy ^ m))) basePoint
  let b : Basis (Fin (finrank ℂ V)) ℂ V := Module.finBasis ℂ V
  let K : ℝ := max 1 ‖LinearMap.toContinuousLinearMap
    (b.equivFun.toLinearMap ∘ₗ ρ D ∘ₗ b.equivFun.symm.toLinearMap)‖
  have hK₀ : 0 < K := one_pos.trans_le (le_max_left _ _)
  have hK₁ : 0 ≤ Real.log K := Real.log_nonneg (le_max_left _ _)
  have hv : 0 < ‖b.equivFun (a T)‖ :=
    norm_pos_iff.mpr fun h ↦ haT <| b.equivFun.injective <| h.trans (map_zero _).symm
  have hw : (0 : ℚ) < (fun i ↦ (y i : ℚ)) ⬝ᵥ (fun i ↦ (y i : ℚ)) := by
    have h : (fun i ↦ (y i : ℚ)) ⬝ᵥ (fun i ↦ (y i : ℚ)) = ((y ⬝ᵥ y : ℤ) : ℚ) := by
      simp [dotProduct]
    rw [h, Int.cast_pos]
    exact lt_of_le_of_ne (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (y i))
      (Ne.symm (dotProduct_self_eq_zero.not.mpr hy))
  have hqw : ((((fun i ↦ (x i : ℚ)) ⬝ᵥ (T : Matrix l l ℚ) *ᵥ (fun i ↦ (x i : ℚ))) *
      ((fun i ↦ (y i : ℚ)) ⬝ᵥ (fun i ↦ (y i : ℚ))) : ℚ) : ℝ) < 0 := by
    exact_mod_cast mul_neg_of_neg_of_pos hx hw
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  rcases ((finite_setOf_one_le basePoint b ha).image
    fun n : dualLattice Γ ↦ ((n : Matrix l l ℚ).trace : ℝ)).bddBelow with ⟨B, hB⟩
  rcases ((tendsto_quadratic (α := -((T : Matrix l l ℚ).trace : ℝ))
    (β := -(((vecMulVec (fun i ↦ (y i : ℚ)) (fun i ↦ (x i : ℚ)) * (T : Matrix l l ℚ)).trace +
      ((T : Matrix l l ℚ) * vecMulVec (fun i ↦ (x i : ℚ)) (fun i ↦ (y i : ℚ))).trace : ℚ) : ℝ) * m)
    (γ := -((((fun i ↦ (x i : ℚ)) ⬝ᵥ (T : Matrix l l ℚ) *ᵥ (fun i ↦ (x i : ℚ))) *
      ((fun i ↦ (y i : ℚ)) ⬝ᵥ (fun i ↦ (y i : ℚ))) : ℚ) : ℝ) * m ^ 2)
    (mul_pos (neg_pos.mpr hqw) (pow_pos hm' 2))).eventually_ge_atTop (-B + 1)).and
    ((tendsto_quadratic (α := -2 * π * ((T : Matrix l l ℚ).trace : ℝ))
    (β := -2 * π * (((vecMulVec (fun i ↦ (y i : ℚ)) (fun i ↦ (x i : ℚ)) *
      (T : Matrix l l ℚ)).trace + ((T : Matrix l l ℚ) *
        vecMulVec (fun i ↦ (x i : ℚ)) (fun i ↦ (y i : ℚ))).trace : ℚ) : ℝ) * m - Real.log K)
    (γ := -2 * π * ((((fun i ↦ (x i : ℚ)) ⬝ᵥ (T : Matrix l l ℚ) *ᵥ (fun i ↦ (x i : ℚ))) *
      ((fun i ↦ (y i : ℚ)) ⬝ᵥ (fun i ↦ (y i : ℚ))) : ℚ) : ℝ) * m ^ 2)
    (mul_pos (mul_pos_of_neg_of_neg (by linarith [pi_pos]) hqw) (pow_pos hm' 2))
    ).eventually_ge_atTop (-Real.log ‖b.equivFun (a T)‖)) |>.exists with ⟨s, hs₁, hs₂⟩
  have hle : ‖b.equivFun (a T)‖ ≤ K ^ s *
      ‖b.equivFun (a (((dualConj _ hUm : Equiv.Perm (dualLattice Γ)) ^ s) T))‖ := by
    rw [apply_dualConj_pow ρ hUm s T hΓ hf ha]
    exact norm_le_pow_mul_norm ρ s b D (a T)
  have hKs : K ^ s ≤ Real.exp (-2 * π *
      ((((dualConj _ hUm : Equiv.Perm (dualLattice Γ)) ^ s) T : Matrix l l ℚ).trace : ℝ)) *
        ‖b.equivFun (a T)‖ := by
    rw [← Real.exp_log hK₀, ← Real.exp_nat_mul, ← Real.exp_log hv, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    rw [trace_dualConj_pow]
    linarith
  have hmem : 1 ≤ ‖fourierExp (((dualConj _ hUm : Equiv.Perm (dualLattice Γ)) ^ s) T) basePoint‖ *
      ‖b.equivFun (a (((dualConj _ hUm : Equiv.Perm (dualLattice Γ)) ^ s) T))‖ := by
    rw [norm_fourierExp_basePoint]
    have hpos : 0 < K ^ s := pow_pos hK₀ s
    nlinarith [Real.exp_pos (-2 * π *
      ((((dualConj _ hUm : Equiv.Perm (dualLattice Γ)) ^ s) T : Matrix l l ℚ).trace : ℝ))]
  have hBs :
      B ≤ ((((dualConj _ hUm : Equiv.Perm (dualLattice Γ)) ^ s) T : Matrix l l ℚ).trace : ℝ) :=
    hB ⟨_, hmem, rfl⟩
  rw [trace_dualConj_pow] at hBs
  linarith

variable [FiniteDimensional ℂ V] in
/-- **Koecher's principle** (LMFDB `mf.siegel.koecher.principle`): for an arithmetic subgroup `Γ`
of `Sp(2g, ℚ)` with `g ≥ 2` and a finite-dimensional representation `ρ`, every Fourier coefficient
`a(n) ≠ 0` of a Siegel modular form `f ∈ M_ρ(Γ)` is indexed by a positive semidefinite `n`.

If `xᵀ n x < 0` for an integral `x`, choose an integral `y ≠ 0` with `yᵀ x = 0`, which is possible
as `g ≥ 2`. A power `U = (1 + x yᵀ)^m` has `(U, 0; 0, U⁻ᵀ) ∈ Γ`, and the transformation law and
the uniqueness of Fourier expansions give `a((U^s)ᵀ n U^s) = ρ(Uᵀ)^s a(n)`. The trace of
`(U^s)ᵀ n U^s` decreases like `-c s²` with `c > 0`, so the terms `a(n') e^{-2π tr n'}` of the
Fourier series at `τ = i 1_g` grow along `n' = (U^s)ᵀ n U^s` faster than `ρ(Uᵀ)^s a(n)` can decay
(at most exponentially), while they tend to `0` since the series converges. -/
lemma koecherPrinciple (hΓ : SymplecticGroup.IsArithmetic Γ) : KoecherPrinciple Γ ρ := by
  intro hl f hf a ha T haT
  by_contra hT
  rcases exists_int_dotProduct_mulVec_neg T.2.1 hT with ⟨x, hx⟩
  have hx₀ : x ≠ 0 := by
    rintro rfl
    simp at hx
  rcases exists_ne_zero_dotProduct_eq_zero hl hx₀ with ⟨y, hy, hxy⟩
  have hU :
      leviRat (unipotent hxy ^ (Γ.relIndex (SymplecticGroup.integral l)).factorial) ∈ Γ := by
    simpa [leviRat] using (Subgroup.pow_mem_of_relIndex_ne_zero_of_dvd
      hΓ.1.relIndex_ne_zero ⟨SymplecticGroup.levi l ℤ (unipotent hxy), trivial, rfl⟩
        fun _ hk hle ↦ Nat.dvd_factorial hk hle).1
  exact koecher_aux ρ hxy hΓ hf ha haT hy hx (Nat.factorial_pos _) hU

end SiegelUpperHalfSpace
