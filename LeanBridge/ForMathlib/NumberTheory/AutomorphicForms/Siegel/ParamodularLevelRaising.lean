import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.HeckeOperator
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParamodularArithmetic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic

/-!
# Level raising operators on paramodular forms

Every symplectic similitude `α ∈ GSp(2g, ℚ)⁺` commensurates `Sp(2g, ℤ)`, hence every arithmetic
subgroup of `Sp(2g, ℚ)`. So for arithmetic subgroups `Γ₁`, `Γ₂` the double coset `Γ₁ α Γ₂` is a
finite union `⊔ᵢ Γ₁ αᵢ` of right cosets, and `F ↦ ∑ᵢ F ∣_ρ αᵢ` maps the `Γ₁`-invariant functions to
the `Γ₂`-invariant ones (Shimura, §3.4).

In degree `2`, the level raising operators of Roberts and Schmidt (*On modular forms for the
paramodular group*, in *Automorphic forms and zeta functions*, World Scientific 2006, §4;
https://sites.math.unt.edu/~schmidt/papers/arakawa.pdf) on paramodular forms of level `M`, for a
prime `p`, are the double coset operators
* `θ_p = [K(M) diag(p, p, 1, 1) K(Mp)]`, the sum of `F ∣ diag(p, p, 1, 1) ι(γ)` over
  `γ ∈ Γ₀(p) \ SL(2, ℤ)` (their (10), their slash operator being trivial on scalars), here
  `levelRaisingThetaPrime`;
* `θ'_p = u_p θ_p u_p`, its conjugate by the Atkin–Lehner involutions (their (14)), which is the
  trace `[K(M) K(Mp)]` from `K(M) ∩ K(Mp)` to `K(Mp)` (their (16)), here `levelRaisingTheta`;
* `η_p F = F ∣ η_p⁻¹`, `η_p = diag(1, p⁻¹, 1, p)` (their (7)), the double coset operator of
  `[K(M) diag(1, p, 1, p⁻¹) K(Mp²)]`, a single right coset, with
  `(η_p F)(τ, z, ω) = ρ(diag(1, p)) F(τ, pz, p²ω)`, here `levelRaisingEta`.
The Lean names `levelRaisingTheta` and `levelRaisingThetaPrime` are thus swapped with respect to
Roberts and Schmidt. These are the classical forms of the local operators `θ`, `θ'` and `η` of
their book *Local newforms for GSp(4)*. The coset decompositions are not proved here (see
`ParamodularLevelRaisingEta` and `ParamodularLevelRaisingThetaPrime`). The comparison with the
operators of Roberts and Schmidt, with their slash operator for `ρ = det^k`, is in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.ParamodularRobertsSchmidt`: `θ_p` is
`p^(3 - k)` times `levelRaisingThetaPrime`
(`SiegelUpperHalfSpace.rsTheta_eq_smul_levelRaisingThetaPrime`), `η_p` is `levelRaisingEta`
(`SiegelUpperHalfSpace.rsEta_eq_levelRaisingEta`), and, for `M = q M₀` with `q p` and `M₀` coprime,
`θ'_p` is `levelRaisingTheta` (`SiegelUpperHalfSpace.rsThetaPrime_eq_levelRaisingTheta`), which
gives their (16) (`SiegelUpperHalfSpace.rsThetaPrime_eq_rsEta_add_sum`).

## Main definitions

* The instance `IsHeckeTriple (gspPlusGL l) (heckeGammaOf Γ₁) (heckeGammaOf Γ₂)` for arithmetic
  `Γ₁` and `Γ₂`.
* `SiegelUpperHalfSpace.diagSimilitude`: the diagonal similitude `diag(a, b)` in `GSp(2g, ℚ)⁺`.
* `SiegelUpperHalfSpace.doubleCosetRep`: the chosen representatives of the right cosets of a double
  coset.
* `SiegelUpperHalfSpace.doubleCosetOperator`: the operator `F ↦ ∑ᵢ F ∣_ρ αᵢ` of a double coset
  `Γ₁ α Γ₂ = ⊔ᵢ Γ₁ αᵢ`.
* `SiegelUpperHalfSpace.paramodularLevel`: the paramodular group `K(N)` of degree `2`.
* `SiegelUpperHalfSpace.thetaPrimeDiag`, `SiegelUpperHalfSpace.etaDiag`: the similitudes
  `diag(p, p, 1, 1)` and `diag(1, p, 1, p⁻¹)`.
* `SiegelUpperHalfSpace.levelRaisingTheta`, `SiegelUpperHalfSpace.levelRaisingThetaPrime`,
  `SiegelUpperHalfSpace.levelRaisingEta`: the level raising operators `θ'_p`, `θ_p` and `η_p` of
  Roberts and Schmidt (in this order).

## Main results

* `SiegelUpperHalfSpace.gspPlusGL_le_commensurator`: every element of `GSp(2g, ℚ)⁺` commensurates
  `Sp(2g, ℤ)`.
* `SiegelUpperHalfSpace.doubleCosetOperator_eq_sum`: the double coset operator is the sum over any
  family of representatives of the right cosets.
* `SiegelUpperHalfSpace.modularForms_le_slashInvariantsOf`: Siegel modular forms on an arithmetic
  subgroup `Γ` are `Γ`-invariant functions for the slash operator of `GSp(2g, ℚ)⁺`.
-/

open Matrix hiding mul_inv_rev

open DoubleCoset Subgroup Commensurable MulAction

open scoped Pointwise

namespace SiegelUpperHalfSpace

variable {l : Type*} [Fintype l] [DecidableEq l]

private lemma prod_den_smul_mem_range (X : Matrix (l ⊕ l) (l ⊕ l) ℚ) :
    ((∏ i, ∏ j, (X i j).den : ℕ) : ℚ) • X ∈ (Int.castRingHom ℚ).mapMatrix.range := by
  refine ⟨of fun i j ↦ ((∏ i, ∏ j, (X i j).den) / (X i j).den : ℕ) * (X i j).num, ?_⟩
  ext i j
  have hd : (X i j).den ∣ ∏ i, ∏ j, (X i j).den :=
    (Finset.dvd_prod_of_mem (fun j ↦ (X i j).den) (Finset.mem_univ j)).trans
      (Finset.dvd_prod_of_mem (fun i ↦ ∏ j, (X i j).den) (Finset.mem_univ i))
  simp only [RingHom.mapMatrix_apply, map_apply, of_apply, eq_intCast, Int.cast_mul,
    Int.cast_natCast, Matrix.smul_apply, smul_eq_mul]
  rw [Nat.cast_div hd (by exact_mod_cast (X i j).den_nz), div_mul_eq_mul_div, mul_div_assoc,
    Rat.num_div_den]

/-- **Every element of `GSp(2g, ℚ)⁺` commensurates `Sp(2g, ℤ)`**: some positive integer multiple
`mα` of `α` lies in `S = GSp(2g, ℚ)⁺ ∩ M(2g, ℤ)`, whose elements commensurate `Sp(2g, ℤ)`
(`SiegelUpperHalfSpace.mem_commensurator_heckeGamma`), and the scalar `m` is central. -/
lemma gspPlusGL_le_commensurator : gspPlusGL l ≤ (commensurator (heckeGamma l)).toSubmonoid := by
  intro x hx
  rcases hx with ⟨r, hr, hxr⟩
  let m : ℕ := ∏ i, ∏ j, ((x : Matrix (l ⊕ l) (l ⊕ l) ℚ) i j).den
  have hm : (m : ℚ) ≠ 0 := by
    simp [m, Finset.prod_eq_zero_iff]
  let c : GL (l ⊕ l) ℚ := ⟨(m : ℚ) • 1, (m : ℚ)⁻¹ • 1, by simp [hm], by simp [hm]⟩
  have hc : c ∈ commensurator (heckeGamma l) := by
    have h1 : MulAut.conj c = 1 := MulEquiv.ext fun g ↦ Units.ext <| by
      simp [c, hm]
    rw [commensurator_mem_iff, h1, one_smul]
  have hxr' : (x : Matrix (l ⊕ l) (l ⊕ l) ℚ)ᵀ * J l ℚ * x = r • J l ℚ :=
    hxr
  have hcx : c * x ∈ commensurator (heckeGamma l) := by
    refine mem_commensurator_heckeGamma ⟨⟨(m : ℚ) ^ 2 * r, by positivity, ?_⟩, ?_⟩
    · simp [c, hxr', smul_smul, sq, mul_assoc]
    · simpa [c, m] using prod_den_smul_mem_range (x : Matrix (l ⊕ l) (l ⊕ l) ℚ)
  simpa using mul_mem (inv_mem hc) hcx

instance {Γ₁ Γ₂ : Subgroup (symplecticGroup l ℚ)} [hΓ₁ : Fact (SymplecticGroup.IsArithmetic Γ₁)]
    [hΓ₂ : Fact (SymplecticGroup.IsArithmetic Γ₂)] :
    IsHeckeTriple (gspPlusGL l) (heckeGammaOf Γ₁) (heckeGammaOf Γ₂) where
  left_le := heckeGammaOf_le_gspPlusGL Γ₁
  right_le := heckeGammaOf_le_gspPlusGL Γ₂
  commensurable :=
    (commensurable_heckeGammaOf hΓ₁.out).trans (commensurable_heckeGammaOf hΓ₂.out).symm
  le_commensurator_right := by
    rw [(commensurable_heckeGammaOf hΓ₂.out).eq]
    exact gspPlusGL_le_commensurator

instance : Fact (gspPlusGL l ≤ gspPlusGL l) :=
  ⟨le_rfl⟩

instance (d : l → ℕ+) : Fact (SymplecticGroup.IsArithmetic (SymplecticGroup.paramodular d)) :=
  ⟨SymplecticGroup.isArithmetic_paramodular d⟩

/-- The diagonal symplectic similitude `diag(a, b)` with `a_i b_i = r > 0`, of multiplier `r`, as an
element of `GSp(2g, ℚ)⁺`. -/
def diagSimilitude (a b : l → ℚ) (r : ℚ) (hr : 0 < r) (hab : ∀ i, a i * b i = r) :
    gspPlusGL l where
  val := TauCeti.diagGL <| Sum.elim
    (fun i ↦ .mk0 (a i) <| left_ne_zero_of_mul <| (hab i).trans_ne hr.ne')
    fun i ↦ .mk0 (b i) <| right_ne_zero_of_mul <| (hab i).trans_ne hr.ne'
  property := ⟨r, hr, by
    ext (i | i) (j | j) <;> rcases eq_or_ne i j with rfl | hij <;> simp [J, mul_comm, *]⟩

section DoubleCoset

variable {n : ℕ} [NeZero n] {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) ℂ) V) {Δ : Submonoid (GL (Fin n ⊕ Fin n) ℚ)}
    [Fact (Δ ≤ gspPlusGL (Fin n))] {Γ₁ Γ₂ : Subgroup (GL (Fin n ⊕ Fin n) ℚ)}
    [IsHeckeTriple Δ Γ₁ Γ₁] [IsHeckeTriple Δ Γ₂ Γ₂] [IsHeckeTriple Δ Γ₁ Γ₂]
    (D : HeckeCoset Δ Γ₁ Γ₂)

private lemma doubleCosetSlash_eq_of_mul_inv_mem {f : SiegelUpperHalfSpace (Fin n) → V}
    (hf : f ∈ slashInvariantsOf ρ Δ Γ₁) {x y : Δ}
    (h : (y : GL (Fin n ⊕ Fin n) ℚ) * (x : GL (Fin n ⊕ Fin n) ℚ)⁻¹ ∈ Γ₁) :
    heckeMonoidSlash ρ x f = heckeMonoidSlash ρ y f := by
  have hy : y = ⟨_, IsHeckeTriple.left_le (H₂ := Γ₁) h⟩ * x :=
    Subtype.ext (inv_mul_cancel_right _ _).symm
  rw [hy, heckeMonoidSlash_mul, hf _ h]

attribute [local instance] Fintype.ofFinite

/-- The representative `δ τᵥ⁻¹` of the `v`-th right coset `Γ₁ δ τᵥ⁻¹` of the double coset
`D = Γ₁ δ Γ₂`, as an element of `Δ`. -/
noncomputable def doubleCosetRep (v : DecompQuotient Γ₂ Γ₁ (D.out : GL _ ℚ)⁻¹) : Δ :=
  ⟨rightCosetRep D v, rightCosetRep_mem D D.out.2 (IsHeckeTriple.right_le (H₁ := Γ₁)) v⟩

/-- The **double coset operator** of `D = Γ₁ α Γ₂ = ⊔ᵢ Γ₁ αᵢ`, for subgroups `Γ₁`, `Γ₂` of
`GL(2g, ℚ)` and `α` in a submonoid `Δ` of `GSp(2g, ℚ)⁺`, from the `Γ₁`-invariant to the
`Γ₂`-invariant functions: `F ↦ F ∣_ρ D = ∑ᵢ F ∣_ρ αᵢ`, with the slash operator `gspSlash`. It is
defined with chosen representatives `αᵢ` but does not depend on them
(`SiegelUpperHalfSpace.doubleCosetOperator_eq_sum`), and its value is `Γ₂`-invariant since right
multiplication by `γ ∈ Γ₂` permutes the right cosets `Γ₁ αᵢ`. For `Γ₁ = Γ₂` it is
`SiegelUpperHalfSpace.heckeOperator`
(`SiegelUpperHalfSpace.doubleCosetOperator_eq_heckeOperator`). -/
noncomputable def doubleCosetOperator :
    slashInvariantsOf ρ Δ Γ₁ →ₗ[ℂ] slashInvariantsOf ρ Δ Γ₂ where
  toFun f := ⟨∑ v, heckeMonoidSlash ρ (doubleCosetRep D v) f, fun γ hγ ↦ by
    rw [map_sum]
    refine Fintype.sum_equiv (toPerm (⟨γ, hγ⟩ : Γ₂)⁻¹) _ _ fun v ↦ ?_
    rw [← heckeMonoidSlash_mul]
    refine doubleCosetSlash_eq_of_mul_inv_mem ρ f.2 ?_
    rcases exists_mem_rightCosetRep_mul_eq_mul_rightCosetRep D v hγ with ⟨γ₁, hγ₁, hprod⟩
    simpa [doubleCosetRep, hprod] using inv_mem hγ₁⟩
  map_add' f g := Subtype.ext <| by
    simp [Finset.sum_add_distrib]
  map_smul' c f := Subtype.ext <| by
    simp [Finset.smul_sum]

lemma coe_doubleCosetOperator (F : slashInvariantsOf ρ Δ Γ₁) :
    (doubleCosetOperator ρ D F : SiegelUpperHalfSpace (Fin n) → V) =
      ∑ v, heckeMonoidSlash ρ (doubleCosetRep D v) F :=
  rfl

lemma doubleCosetOperator_eq_heckeOperator (E : HeckeCoset Δ Γ₁ Γ₁) :
    doubleCosetOperator ρ E = heckeOperator ρ E :=
  rfl

/-- **The double coset operator does not depend on the representatives**: for any family `(aᵢ)` in
`Δ` whose right cosets `Γ₁ aᵢ` are pairwise distinct and cover `D = Γ₁ α Γ₂`,
`F ∣_ρ D = ∑ᵢ F ∣_ρ aᵢ`. -/
lemma doubleCosetOperator_eq_sum {ι : Type*} [Fintype ι] (a : ι → Δ)
    (hcover : doubleCoset (D.out : GL (Fin n ⊕ Fin n) ℚ) (Γ₁ : Set (GL (Fin n ⊕ Fin n) ℚ)) Γ₂ =
      ⋃ i, MulOpposite.op (a i : GL (Fin n ⊕ Fin n) ℚ) • (Γ₁ : Set (GL (Fin n ⊕ Fin n) ℚ)))
    (hinj : Function.Injective fun i ↦ MulOpposite.op (a i : GL (Fin n ⊕ Fin n) ℚ) •
      (Γ₁ : Set (GL (Fin n ⊕ Fin n) ℚ)))
    (F : slashInvariantsOf ρ Δ Γ₁) :
    (doubleCosetOperator ρ D F : SiegelUpperHalfSpace (Fin n) → V) =
      ∑ i, heckeMonoidSlash ρ (a i) F := by
  rcases exists_bijective_rightCosetRep_smul_eq D (fun i ↦ (a i : GL (Fin n ⊕ Fin n) ℚ)) hcover
    hinj with ⟨φ, hφ, h⟩
  exact (Fintype.sum_bijective φ hφ _ _ fun i ↦
    doubleCosetSlash_eq_of_mul_inv_mem ρ F.2 ((rightCoset_eq_iff _).mp (h i))).symm

/-- **Siegel modular forms on an arithmetic subgroup `Γ` are invariant under the slash operator of
`Γ`**, viewed in `GL(2g, ℚ)` inside `GSp(2g, ℚ)⁺`. -/
lemma modularForms_le_slashInvariantsOf (Γ : Subgroup (symplecticGroup (Fin n) ℚ))
    [Fact (SymplecticGroup.IsArithmetic Γ)] :
    modularForms ρ Γ 1 ≤ slashInvariantsOf ρ (gspPlusGL (Fin n)) (heckeGammaOf Γ) :=
  fun f hf ↦ ((mem_modularForms_iff_slashInvariantsOf ρ f Γ).mp hf).2

end DoubleCoset

/-- The **paramodular group** `K(N) = Γ^para(1, N)` of degree `2` and level `N` (LMFDB
`group.paramodular`). -/
abbrev paramodularLevel (N : ℕ+) : Subgroup (symplecticGroup (Fin 2) ℚ) :=
  SymplecticGroup.paramodular ![1, N]

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin 2) ℂ) V)
    (M p : ℕ+)

/-- The similitude `diag(p, p, 1, 1)`, of multiplier `p`, acting on `ℋ₂` by `Z ↦ pZ`, whose double
coset `K(M) diag(p, p, 1, 1) K(Mp)` gives the level raising operator `θ_p` of Roberts and Schmidt
(`SiegelUpperHalfSpace.levelRaisingThetaPrime`). -/
def thetaPrimeDiag : gspPlusGL (Fin 2) :=
  diagSimilitude (fun _ ↦ (p : ℚ)) (fun _ ↦ 1) p (by positivity) fun _ ↦ mul_one _

/-- The symplectic matrix `diag(1, p, 1, p⁻¹)`, acting on `ℋ₂` by `(τ, z, ω) ↦ (τ, pz, p²ω)`, whose
slash operator gives the level raising operator `η`. -/
def etaDiag : gspPlusGL (Fin 2) :=
  diagSimilitude ![1, (p : ℚ)] ![1, (p : ℚ)⁻¹] 1 one_pos fun i ↦ by fin_cases i <;> simp

/-- The **level raising operator** `θ'_p` of Roberts and Schmidt (*On modular forms for the
paramodular group*, §4, equations (14) and (16)) from paramodular forms of level `M` to those of
level `Mp`: the trace `F ↦ ∑ᵢ F ∣_ρ γᵢ` over the right cosets `(K(M) ∩ K(Mp)) γᵢ` of `K(Mp)`, that
is the double coset operator of `K(M) · 1 · K(Mp)`. Roberts and Schmidt define
`θ'_p = u_p θ_p u_p` with the Atkin–Lehner involutions `u_p` and show (their (16)) that it is this
trace, for a prime `p`: for `ρ = det^k` and `M = q M₀` with `q p` and `M₀` coprime, this is
`SiegelUpperHalfSpace.rsThetaPrime_eq_levelRaisingTheta`. Despite its name, this is their `θ'_p`;
their `θ_p` is `SiegelUpperHalfSpace.levelRaisingThetaPrime`. -/
noncomputable def levelRaisingTheta :
    slashInvariantsOf ρ (gspPlusGL (Fin 2)) (heckeGammaOf (paramodularLevel M)) →ₗ[ℂ]
      slashInvariantsOf ρ (gspPlusGL (Fin 2)) (heckeGammaOf (paramodularLevel (M * p))) :=
  doubleCosetOperator ρ (HeckeCoset.mk _ _ 1)

/-- The **level raising operator** `θ_p` of Roberts and Schmidt (*On modular forms for the
paramodular group*, §4, equation (10)) from paramodular forms of level `M` to those of level `Mp`,
for a prime `p`: the double coset operator of `K(M) diag(p, p, 1, 1) K(Mp)`, which is the sum of
`F ∣_ρ diag(p, p, 1, 1) ι(γ)` over `γ ∈ Γ₀(p) \ SL(2, ℤ)` (proved in
`ParamodularLevelRaisingThetaPrime`); Roberts and Schmidt's slash operator, trivial on scalars,
makes their `θ_p` equal to `p^(3 - k)` times this operator for `ρ = det^k`. Despite its name, this
is their `θ_p`; their `θ'_p`, its conjugate by the Atkin–Lehner involutions, is the trace
`SiegelUpperHalfSpace.levelRaisingTheta`. -/
noncomputable def levelRaisingThetaPrime :
    slashInvariantsOf ρ (gspPlusGL (Fin 2)) (heckeGammaOf (paramodularLevel M)) →ₗ[ℂ]
      slashInvariantsOf ρ (gspPlusGL (Fin 2)) (heckeGammaOf (paramodularLevel (M * p))) :=
  doubleCosetOperator ρ (HeckeCoset.mk _ _ (thetaPrimeDiag p))

/-- The **level raising operator** `η_p` of Roberts and Schmidt (§4, equation (7):
`η_p F = F ∣ η_p⁻¹`, `η_p = diag(1, p⁻¹, 1, p)`) from paramodular forms of level `M` to those of
level `Mp²`: the double coset operator of `K(M) diag(1, p, 1, p⁻¹) K(Mp²)`, a single right coset
since `diag(1, p, 1, p⁻¹) K(Mp²) diag(1, p, 1, p⁻¹)⁻¹ ⊆ K(M)`
(`SiegelUpperHalfSpace.doubleCoset_etaDiag`), so `F ↦ F ∣_ρ diag(1, p, 1, p⁻¹)`, that is
`(η_p F)(τ, z, ω) = ρ(diag(1, p)) F(τ, pz, p²ω)` (`SiegelUpperHalfSpace.coe_levelRaisingEta`). -/
noncomputable def levelRaisingEta :
    slashInvariantsOf ρ (gspPlusGL (Fin 2)) (heckeGammaOf (paramodularLevel M)) →ₗ[ℂ]
      slashInvariantsOf ρ (gspPlusGL (Fin 2)) (heckeGammaOf (paramodularLevel (M * p * p))) :=
  doubleCosetOperator ρ (HeckeCoset.mk _ _ (etaDiag p))

end SiegelUpperHalfSpace
