import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.Gamma0Generators
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.GammaOne
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.QuotientSlashRepresentation

/-!
# The quotients of `Sp(4, ℤ)` by the principal congruence subgroup `Γ[2]`

Reduction modulo 2 maps `Sp(4, ℤ)` onto `Sp(4, ℤ/2ℤ)`. Its kernel is the principal congruence
subgroup `Γ[2]` (LMFDB `mf.siegel.family.gamma_2`), so `Sp(4, ℤ)/Γ[2] ≅ Sp(4, ℤ/2ℤ)`, and the
subgroups `Γ₀[2]` and `Γ₁[2]` of the knowl, the preimages of the Siegel parabolic subgroup
`P(ℤ/2ℤ) = {(A, B; 0, D)}` and of its unipotent radical `U(ℤ/2ℤ) = {(1, S; 0, 1)}`, give
`Γ₀[2]/Γ[2] ≅ P(ℤ/2ℤ)` and `Γ₁[2]/Γ[2] ≅ U(ℤ/2ℤ) ≅ (ℤ/2ℤ)³`, the last through the entries of the
symmetric matrix `S`. The block `A` gives `Γ₀[2]/Γ₁[2] ≅ P(ℤ/2ℤ)/U(ℤ/2ℤ) ≅ GL(2, ℤ/2ℤ)`, and
`GL(2, ℤ/2ℤ) ≅ S₃` through its faithful action on the three nonzero vectors of `(ℤ/2ℤ)²`, in which
every transposition is realised (a finite check).

Surjectivity: every `M = (A, B; C, D)` in `Sp(4, ℤ/2ℤ)` is sent into `P(ℤ/2ℤ)` by left
multiplication by `(1, 0; N, 1) w` for a symmetric `N` and one of `w = 1, J₁, J₂, J`, where `J₁`
and `J₂` are the partial inversions and `J = J₁J₂`: the Lagrangian subspace spanned by the columns
of `(A; C)` is transverse to `w⁻¹⟨f₁, f₂⟩` for one of the four `w`, and then `N` exists. This is a
finite check over the `2⁸` pairs `(A, C)`, made by `decide`. An element `(A, B; 0, D)` of
`P(ℤ/2ℤ)` is `(A, 0; 0, D)(1, DᵀB; 0, 1)`, where `A ∈ GL(2, ℤ/2ℤ) = SL(2, ℤ/2ℤ)` lifts to one of
six explicit elements of `SL(2, ℤ)`. The matrices `(1, 0; N, 1)` and `(1, S; 0, 1)` lift to `ℤ`
with symmetric lifts of `N` and `S`, and `J₁`, `J₂`, `J` are reductions of integral elements.

The identification `Sp(4, ℤ/2ℤ) ≅ S₆` of the knowl, through the action on the six odd theta
characteristics, is `SymplecticGroup.oddCharEquiv` in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.LevelTwoOddCharacteristics`. The
identification `P(ℤ/2ℤ) ≅ ℤ/2ℤ × S₄` (so `Γ₀[2]/Γ[2] ≅ ℤ/2ℤ × S₄`) is
`SymplecticGroup.quotientGammaTwoGamma0EquivProd` in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.LevelTwoParabolic`.

## Main definitions

* `SymplecticGroup.quotientGammaTwoEquiv`: `Sp(4, ℤ)/Γ[2] ≅ Sp(4, ℤ/2ℤ)`.
* `SymplecticGroup.quotientGammaTwoGamma0Equiv`: `Γ₀[2]/Γ[2] ≅ P(ℤ/2ℤ)`.
* `SymplecticGroup.siegelUnipotentEquiv`: `U(R) ≅ R³` for a commutative ring `R`.
* `SymplecticGroup.quotientGammaTwoGamma1Equiv`: `Γ₁[2]/Γ[2] ≅ (ℤ/2ℤ)³`.
* `SymplecticGroup.siegelParabolicBlock`: the homomorphism `(A, B; 0, D) ↦ A` from `P(R)` onto
  `GL(2, R)`.
* The instance `((Gamma1 (Fin 2) 2).subgroupOf (Gamma0 (Fin 2) 2)).Normal`: `Γ₁[2]` is normal
  in `Γ₀[2]`, as a kernel.
* `SymplecticGroup.quotientGammaOneGamma0Equiv`: `Γ₀[2]/Γ₁[2] ≅ GL(2, ℤ/2ℤ)`.
* `SymplecticGroup.NonzeroVecTwo`: the three nonzero vectors of `(ℤ/2ℤ)²`.
* `SymplecticGroup.glTwoPerm`, `SymplecticGroup.glTwoHom`: the action of `GL(2, ℤ/2ℤ)` on the
  three nonzero vectors of `(ℤ/2ℤ)²`.
* `SymplecticGroup.glTwoEquiv`: `GL(2, ℤ/2ℤ) ≅ S₃`.
* `SymplecticGroup.quotientGammaOneGamma0EquivPerm`: `Γ₀[2]/Γ₁[2] ≅ S₃`.

## Main results

* `SymplecticGroup.surjective_map_zmod_two`: reduction modulo 2 maps `Sp(4, ℤ)` onto
  `Sp(4, ℤ/2ℤ)`.
-/

open Equiv Matrix

open scoped MatrixGroups

namespace SymplecticGroup

variable {R : Type*} [CommRing R] {g h : symplecticGroup (Fin 2) R}
    (A C M : Matrix (Fin 2) (Fin 2) (ZMod 2)) (i : Fin 6)

/-- The element `(1, 0; N, 1)` of `Sp(4, R)` for a symmetric `N`. -/
private def lowerSym (N : Matrix (Fin 2) (Fin 2) R) (hN : Nᵀ = N) : symplecticGroup (Fin 2) R :=
  ⟨fromBlocks 1 0 N 1, fromBlocks_mem_iff.mpr ⟨by simp [hN], by simp, by simp⟩⟩

/-- The element `(1, S; 0, 1)` of `Sp(4, R)` for a symmetric `S`. -/
private def upperSym (S : Matrix (Fin 2) (Fin 2) R) (hS : Sᵀ = S) : symplecticGroup (Fin 2) R :=
  ⟨fromBlocks 1 S 0 1, fromBlocks_mem_iff.mpr ⟨by simp, by simp [hS], by simp⟩⟩

/-- The integral lift with entries in `{0, 1}` of a matrix over `ℤ/2ℤ`. -/
private def liftMat : Matrix (Fin 2) (Fin 2) ℤ :=
  M.map fun z ↦ (z.val : ℤ)

private lemma map_liftMat : (liftMat M).map (Int.castRingHom (ZMod 2)) = M := by
  ext i j
  simp [liftMat]

variable {M} in
private lemma transpose_liftMat (hM : Mᵀ = M) : (liftMat M)ᵀ = liftMat M := by
  rw [liftMat, ← transpose_map, hM]

private lemma lowerSym_mem_range {N : Matrix (Fin 2) (Fin 2) (ZMod 2)} (hN : Nᵀ = N) :
    lowerSym N hN ∈ (map (Int.castRingHom (ZMod 2)) :
      symplecticGroup (Fin 2) ℤ →* symplecticGroup (Fin 2) (ZMod 2)).range :=
  ⟨lowerSym (liftMat N) (transpose_liftMat hN), Subtype.ext <| by
    rw [coe_map_apply, lowerSym, lowerSym, fromBlocks_map, map_liftMat,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _)]⟩

private lemma upperSym_mem_range {S : Matrix (Fin 2) (Fin 2) (ZMod 2)} (hS : Sᵀ = S) :
    upperSym S hS ∈ (map (Int.castRingHom (ZMod 2)) :
      symplecticGroup (Fin 2) ℤ →* symplecticGroup (Fin 2) (ZMod 2)).range :=
  ⟨upperSym (liftMat S) (transpose_liftMat hS), Subtype.ext <| by
    rw [coe_map_apply, upperSym, upperSym, fromBlocks_map, map_liftMat,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _)]⟩

/-- Lifts to `SL(2, ℤ)` of the six elements of `GL(2, ℤ/2ℤ)`. -/
private def slLift : Fin 6 → Matrix (Fin 2) (Fin 2) ℤ :=
  ![!![1, 0; 0, 1], !![2, 3; 1, 2], !![1, 1; 0, 1], !![1, 0; 1, 1], !![1, 1; 1, 2], !![2, 1; 1, 1]]

private lemma det_slLift : (slLift i).det = 1 := by
  fin_cases i <;> simp [slLift]

/-- The element `slLift i` of `SL(2, ℤ)`. -/
private def slLiftSL : SL(2, ℤ) :=
  ⟨slLift i, det_slLift i⟩

private lemma exists_slLift (hA : A.det ≠ 0) :
    ∃ i, (slLift i).map (Int.castRingHom (ZMod 2)) = A := by
  revert A
  decide

private lemma fromBlocks_mem_of_mem_siegelParabolic (hg : g ∈ siegelParabolic (Fin 2) R) :
    fromBlocks g.1.toBlocks₁₁ g.1.toBlocks₁₂ 0 g.1.toBlocks₂₂ ∈ symplecticGroup (Fin 2) R := by
  rw [← (hg : g.1.toBlocks₂₁ = 0), fromBlocks_toBlocks]
  exact g.2

private lemma transpose_toBlocks₁₁_mul_toBlocks₂₂ (hg : g ∈ siegelParabolic (Fin 2) R) :
    g.1.toBlocks₁₁ᵀ * g.1.toBlocks₂₂ = 1 := by
  simpa using (fromBlocks_mem_iff.mp (fromBlocks_mem_of_mem_siegelParabolic hg)).2.2

private lemma toBlocks₁₁_mul_transpose_toBlocks₂₂ (hg : g ∈ siegelParabolic (Fin 2) R) :
    g.1.toBlocks₁₁ * g.1.toBlocks₂₂ᵀ = 1 := by
  rw [← transpose_transpose g.1.toBlocks₁₁, ← transpose_mul,
    mul_eq_one_comm.mp (transpose_toBlocks₁₁_mul_toBlocks₂₂ hg), transpose_one]

private lemma mem_range_of_toBlocks₂₁_eq_zero {p : symplecticGroup (Fin 2) (ZMod 2)}
    (hp : p.1.toBlocks₂₁ = 0) : p ∈ (map (Int.castRingHom (ZMod 2)) :
      symplecticGroup (Fin 2) ℤ →* symplecticGroup (Fin 2) (ZMod 2)).range := by
  have hAD : p.1.toBlocks₁₁ᵀ * p.1.toBlocks₂₂ = 1 := transpose_toBlocks₁₁_mul_toBlocks₂₂ hp
  have hdet : p.1.toBlocks₁₁.det ≠ 0 := fun h0 ↦ by
    have e : (p.1.toBlocks₁₁ᵀ * p.1.toBlocks₂₂).det = (1 : Matrix (Fin 2) (Fin 2) (ZMod 2)).det :=
      congrArg det hAD
    rw [det_mul, det_transpose, h0, zero_mul, det_one] at e
    exact zero_ne_one e
  rcases exists_slLift _ hdet with ⟨i, hi⟩
  have hr : (map (Int.castRingHom (ZMod 2)) (rotation (slLiftSL i))).1 =
      fromBlocks p.1.toBlocks₁₁ 0 0 (!![slLift i 1 1, -slLift i 1 0; -slLift i 0 1,
        slLift i 0 0].map (Int.castRingHom (ZMod 2))) := by
    rw [← hi]
    ext (j | j) (k | k) <;> simp [rotation, slLiftSL]
  have hE : p.1.toBlocks₁₁ᵀ * !![slLift i 1 1, -slLift i 1 0; -slLift i 0 1,
      slLift i 0 0].map (Int.castRingHom (ZMod 2)) = 1 := by
    have hmem' : fromBlocks p.1.toBlocks₁₁ 0 0 (!![slLift i 1 1, -slLift i 1 0; -slLift i 0 1,
        slLift i 0 0].map (Int.castRingHom (ZMod 2))) ∈ symplecticGroup (Fin 2) (ZMod 2) :=
      hr ▸ (map (Int.castRingHom (ZMod 2)) (rotation (slLiftSL i))).2
    simpa using (fromBlocks_mem_iff.mp hmem').2.2
  have hDE : !![slLift i 1 1, -slLift i 1 0; -slLift i 0 1, slLift i 0 0].map
      (Int.castRingHom (ZMod 2)) = p.1.toBlocks₂₂ := by
    rw [← Matrix.one_mul (!![slLift i 1 1, -slLift i 1 0; -slLift i 0 1, slLift i 0 0].map
      (Int.castRingHom (ZMod 2))), ← mul_eq_one_comm.mp hAD, Matrix.mul_assoc, hE, Matrix.mul_one]
  have hS : (p.1.toBlocks₂₂ᵀ * p.1.toBlocks₁₂)ᵀ = p.1.toBlocks₂₂ᵀ * p.1.toBlocks₁₂ := by
    rw [transpose_mul, transpose_transpose,
      (fromBlocks_mem_iff.mp (fromBlocks_mem_of_mem_siegelParabolic hp)).2.1]
  have e : map (Int.castRingHom (ZMod 2)) (rotation (slLiftSL i)) *
      upperSym (p.1.toBlocks₂₂ᵀ * p.1.toBlocks₁₂) hS = p := Subtype.ext <| by
    rw [Submonoid.coe_mul, hr, upperSym, fromBlocks_multiply, hDE, ← Matrix.mul_assoc,
      toBlocks₁₁_mul_transpose_toBlocks₂₂ hp]
    conv_rhs => rw [← fromBlocks_toBlocks p.1, hp]
    simp
  exact e ▸ mul_mem ⟨_, rfl⟩ (upperSym_mem_range hS)

/-- The blocks `(a, b), (c, d)` modulo 2 of `1`, of the partial inversions `J₁` and `J₂`, and of
`J = J₁J₂`. -/
private def wBlocks : Fin 4 → (Matrix (Fin 2) (Fin 2) (ZMod 2) × Matrix (Fin 2) (Fin 2) (ZMod 2)) ×
    (Matrix (Fin 2) (Fin 2) (ZMod 2) × Matrix (Fin 2) (Fin 2) (ZMod 2)) :=
  ![((1, 0), (0, 1)), ((!![0, 0; 0, 1], !![1, 0; 0, 0]), (!![1, 0; 0, 0], !![0, 0; 0, 1])),
    ((!![1, 0; 0, 0], !![0, 0; 0, 1]), (!![0, 0; 0, 1], !![1, 0; 0, 0])), ((0, 1), (1, 0))]

/-- The elements `1`, `J₁`, `J₂` and `J` of `Sp(4, ℤ)`. -/
private def wInt : Fin 4 → symplecticGroup (Fin 2) ℤ :=
  ![1, partialInversion, embedSecond ModularGroup.S, ⟨J (Fin 2) ℤ, J_mem _ _⟩]

private lemma coe_map_wInt (n : Fin 4) : (map (Int.castRingHom (ZMod 2)) (wInt n)).1 =
    fromBlocks (wBlocks n).1.1 (wBlocks n).1.2 (wBlocks n).2.1 (wBlocks n).2.2 := by
  fin_cases n <;> ext (j | j) (k | k) <;> fin_cases j <;> fin_cases k <;>
    simp [wInt, wBlocks, partialInversion, embedSecond, J]

private lemma exists_lowerSym (hAC : Aᵀ * C = Cᵀ * A)
    (hinj : ∀ v, A *ᵥ v = 0 → C *ᵥ v = 0 → v = 0) : ∃ i, ∃ N : Matrix (Fin 2) (Fin 2) (ZMod 2),
      Nᵀ = N ∧ (N * (wBlocks i).1.1 + (wBlocks i).2.1) * A +
        (N * (wBlocks i).1.2 + (wBlocks i).2.2) * C = 0 := by
  revert A C
  decide

/-- **Reduction modulo 2 maps `Sp(4, ℤ)` onto `Sp(4, ℤ/2ℤ)`** (LMFDB `mf.siegel.family.gamma_2`):
left multiplication by `(1, 0; N, 1) w`, with `N` symmetric and `w ∈ {1, J₁, J₂, J}`, sends an
element of `Sp(4, ℤ/2ℤ)` into the Siegel parabolic subgroup, whose elements
`(A, B; 0, D) = (A, 0; 0, D)(1, DᵀB; 0, 1)` lift to `Sp(4, ℤ)`, as do `(1, 0; N, 1)` and `w`. -/
lemma surjective_map_zmod_two : Function.Surjective (map (Int.castRingHom (ZMod 2)) :
    symplecticGroup (Fin 2) ℤ →* symplecticGroup (Fin 2) (ZMod 2)) := by
  intro M
  have hmem : fromBlocks M.1.toBlocks₁₁ M.1.toBlocks₁₂ M.1.toBlocks₂₁ M.1.toBlocks₂₂ ∈
      symplecticGroup (Fin 2) (ZMod 2) := by
    rw [fromBlocks_toBlocks]
    exact M.2
  have e : M⁻¹.1 * M.1 = 1 := by
    rw [← Submonoid.coe_mul, inv_mul_cancel, Submonoid.coe_one]
  have hinj (v : Fin 2 → ZMod 2) (hA : M.1.toBlocks₁₁ *ᵥ v = 0)
      (hC : M.1.toBlocks₂₁ *ᵥ v = 0) : v = 0 := by
    have h0 : M.1 *ᵥ Sum.elim v 0 = 0 := by
      rw [← fromBlocks_toBlocks M.1, fromBlocks_mulVec]
      ext (j | j) <;> simp [hA, hC]
    have h1 : (Sum.elim v 0 : Fin 2 ⊕ Fin 2 → ZMod 2) = 0 := by
      rw [← one_mulVec (Sum.elim v 0), ← e, ← mulVec_mulVec, h0, mulVec_zero]
    funext j
    simpa using congrFun h1 (.inl j)
  rcases exists_lowerSym _ _ (fromBlocks_mem_iff.mp hmem).1 hinj with ⟨i, N, hN, h0⟩
  have hp : (lowerSym N hN * map (Int.castRingHom (ZMod 2)) (wInt i) * M).1.toBlocks₂₁ = 0 := by
    rw [Submonoid.coe_mul, Submonoid.coe_mul, lowerSym, coe_map_wInt, ← fromBlocks_toBlocks M.1,
      fromBlocks_multiply, fromBlocks_multiply, toBlocks_fromBlocks₂₁]
    simpa using h0
  simpa only [inv_mul_cancel_left, MonoidHom.mem_range] using mul_mem
    (inv_mem (mul_mem (lowerSym_mem_range hN) ⟨wInt i, rfl⟩)) (mem_range_of_toBlocks₂₁_eq_zero hp)

/-- The isomorphism **`Sp(4, ℤ)/Γ[2] ≅ Sp(4, ℤ/2ℤ)`** (LMFDB `mf.siegel.family.gamma_2`) induced by
reduction modulo 2, whose kernel is the principal congruence subgroup `Γ[2]`. -/
noncomputable def quotientGammaTwoEquiv :
    symplecticGroup (Fin 2) ℤ ⧸ Gamma (Fin 2) 2 ≃* symplecticGroup (Fin 2) (ZMod 2) :=
  QuotientGroup.quotientKerEquivOfSurjective _ surjective_map_zmod_two

/-- For a surjective `φ : G →* H` and a subgroup `K` of `H`, the isomorphism
`φ⁻¹(K)/(ker φ ∩ φ⁻¹(K)) ≅ K` induced by `φ`. -/
private noncomputable def comapQuotientEquiv {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (hφ : Function.Surjective φ) (K : Subgroup H) :
    K.comap φ ⧸ φ.ker.subgroupOf (K.comap φ) ≃* K :=
  (QuotientGroup.quotientMulEquivOfEq (Subgroup.ext fun x ↦ by
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker, MonoidHom.mem_ker, Subtype.ext_iff,
      OneMemClass.coe_one]
    rfl)).trans
      (QuotientGroup.quotientKerEquivOfSurjective (φ.subgroupComap K) fun k ↦ by
        rcases hφ k with ⟨g, hg⟩
        exact ⟨⟨g, by simp [hg]⟩, Subtype.ext hg⟩)

/-- The isomorphism **`Γ₀[2]/Γ[2] ≅ P(ℤ/2ℤ)`** (LMFDB `mf.siegel.family.gamma_2`) induced by
reduction modulo 2, onto the Siegel parabolic subgroup `{(A, B; 0, D)}` of `Sp(4, ℤ/2ℤ)`. -/
noncomputable def quotientGammaTwoGamma0Equiv : Gamma0 (Fin 2) 2 ⧸
    (Gamma (Fin 2) 2).subgroupOf (Gamma0 (Fin 2) 2) ≃* siegelParabolic (Fin 2) (ZMod 2) :=
  comapQuotientEquiv _ surjective_map_zmod_two _

private lemma eq_fromBlocks_of_mem_siegelUnipotent (hg : g ∈ siegelUnipotent (Fin 2) R) :
    g.1 = fromBlocks 1 g.1.toBlocks₁₂ 0 1 := by
  conv_lhs => rw [← fromBlocks_toBlocks g.1, hg.1, hg.2.1, hg.2.2]

private lemma transpose_toBlocks₁₂_of_mem_siegelUnipotent (hg : g ∈ siegelUnipotent (Fin 2) R) :
    g.1.toBlocks₁₂ᵀ = g.1.toBlocks₁₂ := by
  have hmem : fromBlocks 1 g.1.toBlocks₁₂ 0 1 ∈ symplecticGroup (Fin 2) R :=
    eq_fromBlocks_of_mem_siegelUnipotent hg ▸ g.2
  simpa using (fromBlocks_mem_iff.mp hmem).2.1

private lemma toBlocks₁₂_mul_of_mem_siegelUnipotent (hg : g ∈ siegelUnipotent (Fin 2) R)
    (hh : h ∈ siegelUnipotent (Fin 2) R) :
    (g * h).1.toBlocks₁₂ = g.1.toBlocks₁₂ + h.1.toBlocks₁₂ := by
  rw [Submonoid.coe_mul, eq_fromBlocks_of_mem_siegelUnipotent hg,
    eq_fromBlocks_of_mem_siegelUnipotent hh, fromBlocks_multiply]
  simp [add_comm]

/-- The symmetric matrix `(v₁, v₂; v₂, v₃)`. -/
private def symmOfFin3 (v : Fin 3 → R) : Matrix (Fin 2) (Fin 2) R :=
  !![v 0, v 1; v 1, v 2]

/-- The isomorphism **`U(R) ≅ R³`**, `(1, S; 0, 1) ↦ (S₁₁, S₁₂, S₂₂)`, from the unipotent radical of
the Siegel parabolic subgroup of `Sp(4, R)` onto the additive group `R³`, written multiplicatively:
its elements are the `(1, S; 0, 1)` with `S` symmetric, and
`(1, S; 0, 1)(1, T; 0, 1) = (1, S + T; 0, 1)`. -/
def siegelUnipotentEquiv : siegelUnipotent (Fin 2) R ≃* Multiplicative (Fin 3 → R) where
  toFun g := .ofAdd ![g.1.1.toBlocks₁₂ 0 0, g.1.1.toBlocks₁₂ 0 1, g.1.1.toBlocks₁₂ 1 1]
  invFun v := ⟨⟨fromBlocks 1 (symmOfFin3 v.toAdd) 0 1, fromBlocks_mem_iff.mpr ⟨by simp, by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [symmOfFin3], by simp⟩⟩, by simp [siegelUnipotent]⟩
  left_inv g := by
    refine Subtype.ext (Subtype.ext ?_)
    conv_rhs => rw [eq_fromBlocks_of_mem_siegelUnipotent g.2]
    have h10 : g.1.1.toBlocks₁₂ 1 0 = g.1.1.toBlocks₁₂ 0 1 := by
      rw [← transpose_apply g.1.1.toBlocks₁₂ 0 1, transpose_toBlocks₁₂_of_mem_siegelUnipotent g.2]
    ext (i | i) (j | j) <;> fin_cases i <;> fin_cases j <;> simp [symmOfFin3, h10]
  right_inv v := by
    ext i
    fin_cases i <;> rfl
  map_mul' g h := by
    rw [← ofAdd_add]
    congr 1
    simp only [Subgroup.coe_mul, toBlocks₁₂_mul_of_mem_siegelUnipotent g.2 h.2]
    ext i
    fin_cases i <;> rfl

/-- The isomorphism **`Γ₁[2]/Γ[2] ≅ (ℤ/2ℤ)³`** (LMFDB `mf.siegel.family.gamma_2`) induced by
reduction modulo 2 onto the unipotent radical `{(1, S; 0, 1)}` of the Siegel parabolic subgroup of
`Sp(4, ℤ/2ℤ)`, followed by `(1, S; 0, 1) ↦ (S₁₁, S₁₂, S₂₂)`. -/
noncomputable def quotientGammaTwoGamma1Equiv : Gamma1 (Fin 2) 2 ⧸
    (Gamma (Fin 2) 2).subgroupOf (Gamma1 (Fin 2) 2) ≃* Multiplicative (Fin 3 → ZMod 2) :=
  (comapQuotientEquiv _ surjective_map_zmod_two _).trans siegelUnipotentEquiv

/-- The block `A` of `(A, B; 0, D)`, a homomorphism from the Siegel parabolic subgroup of
`Sp(4, R)` onto `GL(2, R)`: the symplectic relation `AᵀD = 1` makes `A` invertible. -/
def siegelParabolicBlock : siegelParabolic (Fin 2) R →* GL (Fin 2) R where
  toFun p := ⟨p.1.1.toBlocks₁₁, p.1.1.toBlocks₂₂ᵀ, toBlocks₁₁_mul_transpose_toBlocks₂₂ p.2,
    by rw [← transpose_transpose p.1.1.toBlocks₁₁, ← transpose_mul,
      transpose_toBlocks₁₁_mul_toBlocks₂₂ p.2, transpose_one]⟩
  map_one' := Units.ext <| by
    simp [← fromBlocks_one]
  map_mul' p q := Units.ext <| by
    have hq (k j : Fin 2) : q.1.1 (.inr k) (.inl j) = 0 := congrFun (congrFun q.2 k) j
    ext i j
    simp [toBlocks₁₁, Matrix.mul_apply, hq]

lemma surjective_siegelParabolicBlock :
    Function.Surjective (siegelParabolicBlock : siegelParabolic (Fin 2) R →* GL (Fin 2) R) :=
  fun U ↦ ⟨⟨⟨fromBlocks U 0 0 (U⁻¹ : GL (Fin 2) R).1ᵀ, fromBlocks_mem_iff.mpr ⟨by simp, by simp,
    by simp [← transpose_mul]⟩⟩, by simp [siegelParabolic]⟩,
      Units.ext <| by simp [siegelParabolicBlock]⟩

/-- The block `A` modulo 2 of `(A, B; C, D) ∈ Γ₀[2]`. -/
private def gamma0Block : Gamma0 (Fin 2) 2 →* GL (Fin 2) (ZMod 2) :=
  siegelParabolicBlock.comp ((map (Int.castRingHom (ZMod 2))).subgroupComap
    (siegelParabolic (Fin 2) (ZMod 2)))

private lemma ker_gamma0Block :
    gamma0Block.ker = (Gamma1 (Fin 2) 2).subgroupOf (Gamma0 (Fin 2) 2) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Units.ext_iff]
  refine ⟨fun h ↦ ⟨h, x.2, ?_⟩, fun h ↦ h.1⟩
  have hA : (map (Int.castRingHom (ZMod 2)) x.1).1.toBlocks₁₁ = 1 := h
  have hAD : (map (Int.castRingHom (ZMod 2)) x.1).1.toBlocks₁₁ᵀ *
      (map (Int.castRingHom (ZMod 2)) x.1).1.toBlocks₂₂ = 1 :=
    transpose_toBlocks₁₁_mul_toBlocks₂₂ x.2
  rwa [hA, transpose_one, Matrix.one_mul] at hAD

private lemma surjective_gamma0Block : Function.Surjective gamma0Block := fun U ↦ by
  rcases surjective_siegelParabolicBlock U with ⟨p, rfl⟩
  rcases surjective_map_zmod_two p.1 with ⟨g, hg⟩
  exact ⟨⟨g, Subgroup.mem_comap.mpr (hg ▸ p.2)⟩, congrArg siegelParabolicBlock (Subtype.ext hg)⟩

instance : ((Gamma1 (Fin 2) 2).subgroupOf (Gamma0 (Fin 2) 2)).Normal :=
  ker_gamma0Block ▸ gamma0Block.normal_ker

/-- The isomorphism **`Γ₀[2]/Γ₁[2] ≅ GL(2, ℤ/2ℤ)`** (LMFDB `mf.siegel.family.gamma_2`),
`(A, B; C, D) ↦ A` modulo 2: its kernel is `Γ₁[2]`, since `C ≡ 0` and `A ≡ 1` give `D ≡ 1`. -/
noncomputable def quotientGammaOneGamma0Equiv :
    Gamma0 (Fin 2) 2 ⧸ (Gamma1 (Fin 2) 2).subgroupOf (Gamma0 (Fin 2) 2) ≃* GL (Fin 2) (ZMod 2) :=
  (QuotientGroup.quotientMulEquivOfEq ker_gamma0Block.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ surjective_gamma0Block)

/-- The three nonzero vectors of `(ℤ/2ℤ)²`. -/
abbrev NonzeroVecTwo : Type :=
  {v : Fin 2 → ZMod 2 // v ≠ 0}

/-- The permutation of the three nonzero vectors of `(ℤ/2ℤ)²` induced by `U ∈ GL(2, ℤ/2ℤ)`. -/
def glTwoPerm (U : GL (Fin 2) (ZMod 2)) : Equiv.Perm NonzeroVecTwo where
  toFun v := ⟨U.1 *ᵥ v.1, fun h ↦ v.2 <| by
    rw [← one_mulVec v.1, ← U.inv_mul, ← mulVec_mulVec, h, mulVec_zero]⟩
  invFun v := ⟨U⁻¹.1 *ᵥ v.1, fun h ↦ v.2 <| by
    rw [← one_mulVec v.1, ← U.mul_inv, ← mulVec_mulVec, h, mulVec_zero]⟩
  left_inv v := Subtype.ext <| by
    simp only [mulVec_mulVec, Units.inv_mul, one_mulVec]
  right_inv v := Subtype.ext <| by
    simp only [mulVec_mulVec, Units.mul_inv, one_mulVec]

/-- The action of `GL(2, ℤ/2ℤ)` on the three nonzero vectors of `(ℤ/2ℤ)²`. -/
def glTwoHom : GL (Fin 2) (ZMod 2) →* Equiv.Perm NonzeroVecTwo where
  toFun := glTwoPerm
  map_one' := Equiv.ext fun v ↦ Subtype.ext (one_mulVec v.1)
  map_mul' U V := Equiv.ext fun v ↦ Subtype.ext (mulVec_mulVec v.1 U.1 V.1).symm

private lemma eq_one_of_mulVec_eq (hA : ∀ v, v ≠ 0 → A *ᵥ v = v) : A = 1 := by
  revert A
  decide

lemma injective_glTwoHom : Function.Injective glTwoHom :=
  (injective_iff_map_eq_one _).mpr fun U hU ↦ Units.ext <| eq_one_of_mulVec_eq U.1 fun v hv ↦
    congrArg Subtype.val (Equiv.ext_iff.mp hU ⟨v, hv⟩)

/-- The six elements of `GL(2, ℤ/2ℤ)`, as matrices. -/
private def glTwoMat : Fin 6 → Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  ![1, !![0, 1; 1, 0], !![1, 1; 0, 1], !![1, 0; 1, 1], !![1, 1; 1, 0], !![0, 1; 1, 1]]

private lemma det_glTwoMat : (glTwoMat i).det = 1 := by
  revert i
  decide

private lemma exists_glTwoMat_swap : ∀ x : NonzeroVecTwo × NonzeroVecTwo, x.1 ≠ x.2 →
    ∃ i, ∀ v : NonzeroVecTwo, glTwoMat i *ᵥ v.1 = (Equiv.swap x.1 x.2 v).1 := by
  decide

lemma surjective_glTwoHom : Function.Surjective glTwoHom := by
  have h : glTwoHom.range = ⊤ := by
    rw [eq_top_iff, ← Perm.closure_isSwap, Subgroup.closure_le]
    rintro σ ⟨a, b, hab, rfl⟩
    rcases exists_glTwoMat_swap (a, b) hab with ⟨i, hi⟩
    exact ⟨((isUnit_iff_isUnit_det _).mpr ((det_glTwoMat i).symm ▸ isUnit_one)).unit,
      Equiv.ext fun v ↦ Subtype.ext (hi v)⟩
  exact MonoidHom.range_eq_top.mp h

lemma card_nonzeroVecTwo : Fintype.card NonzeroVecTwo = 3 := by
  decide

/-- The isomorphism **`GL(2, ℤ/2ℤ) ≅ S₃`** given by the faithful action on the three nonzero
vectors of `(ℤ/2ℤ)²`, numbered by an arbitrary bijection with `Fin 3`. -/
noncomputable def glTwoEquiv : GL (Fin 2) (ZMod 2) ≃* Equiv.Perm (Fin 3) :=
  (MulEquiv.ofBijective glTwoHom ⟨injective_glTwoHom, surjective_glTwoHom⟩).trans
    (Fintype.equivFinOfCardEq card_nonzeroVecTwo).permCongrHom

/-- The isomorphism **`Γ₀[2]/Γ₁[2] ≅ S₃`** (LMFDB `mf.siegel.family.gamma_2`):
`(A, B; C, D) ↦ A` modulo 2, followed by `GL(2, ℤ/2ℤ) ≅ S₃`. -/
noncomputable def quotientGammaOneGamma0EquivPerm :
    Gamma0 (Fin 2) 2 ⧸ (Gamma1 (Fin 2) 2).subgroupOf (Gamma0 (Fin 2) 2) ≃* Equiv.Perm (Fin 3) :=
  quotientGammaOneGamma0Equiv.trans glTwoEquiv

end SymplecticGroup
