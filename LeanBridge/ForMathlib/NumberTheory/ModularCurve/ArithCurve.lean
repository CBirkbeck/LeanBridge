import LeanBridge.ForMathlib.NumberTheory.ModularCurve.AdelicPreimage
import TauCeti.GroupTheory.Index.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic

/-!
# The group of the modular curve `X_arith(N)`

The modular curve `X_arith(N)` is the modular curve `X_H` for `H ≤ GL₂(ℤ̂)` the inverse image of
the subgroup `!![1, 0; 0, *]` of `GL₂(ℤ/Nℤ)`: the invertible diagonal matrices with upper left entry
`1`. The determinant maps it isomorphically onto `(ℤ/Nℤ)ˣ`, so `det(H) = ℤ̂ˣ` (not formalised),
while the group of the full modular curve `X(N)`, the inverse image of the trivial subgroup, has
trivial determinant modulo `N`; for `N ≤ 2`, where `(ℤ/Nℤ)ˣ` is trivial, the two groups coincide.
The subgroup lies in the split Cartan subgroup of diagonal matrices, so `X_arith(N)` covers
`X_sp(N)`.

The inverse image in `GL₂(ℤ̂) = ∏_ℓ GL₂(ℤ_ℓ)` is taken under the reduction modulo `N`
(`Matrix.GeneralLinearGroup.adelicPreimage`); it is an open subgroup of level at most `N`. The
modular curve itself, its compactification and its moduli interpretation by symplectic isomorphisms
`μ_N × ℤ/Nℤ ≃ E[N]` are not formalised; the data `(φ, P)` of the moduli interpretation of its
non-cuspidal points by triples `(E, φ, P)` are in
`LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.SplitCartanStructure`.

## Main definitions

* `Matrix.GeneralLinearGroup.arithEmbedding`: the embedding `u ↦ !![1, 0; 0, u]` of `Rˣ` in
  `GL₂(R)`.
* `Matrix.GeneralLinearGroup.arithSubgroup`: the subgroup `!![1, 0; 0, *]` of `GL₂(R)`, its image.
* `Matrix.GeneralLinearGroup.adelicArith` (LMFDB `modcurve.xarith`): the group `H` of `X_arith(N)`.

## Main results

* `Matrix.GeneralLinearGroup.mem_arithSubgroup_iff`: the elements of `arithSubgroup R` are the
  invertible matrices `!![1, 0; 0, u]`.
* `Matrix.GeneralLinearGroup.map_det_arithSubgroup`: the determinant of `arithSubgroup R` is
  surjective.
* `Matrix.GeneralLinearGroup.arithSubgroup_le_diagonalTorus`: `arithSubgroup R` lies in the split
  Cartan subgroup of diagonal matrices.
* `Matrix.GeneralLinearGroup.arithSubgroup_eq_bot`: `arithSubgroup R` is trivial when `Rˣ` is.
* `Matrix.GeneralLinearGroup.index_adelicArith`: for a prime `p`, the group of `X_arith(p)` has
  index `p (p² - 1)` in `GL₂(ℤ̂)`.
-/

open Function TauCeti

namespace Matrix.GeneralLinearGroup

variable (R : Type*) [CommRing R] {g : GL (Fin 2) R} (u : Rˣ) (p : ℕ) [Fact p.Prime]

/-- The homomorphism `Rˣ → GL₂(R)`, `u ↦ !![1, 0; 0, u]`. -/
noncomputable def arithEmbedding : Rˣ →* GL (Fin 2) R :=
  diagGL.comp (MonoidHom.mulSingle (fun _ : Fin 2 ↦ Rˣ) 1)

lemma coe_arithEmbedding :
    (arithEmbedding R u : Matrix (Fin 2) (Fin 2) R) = !![1, 0; 0, (u : R)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [arithEmbedding]

/-- The subgroup **`!![1, 0; 0, *]`** of `GL₂(R)`: the invertible diagonal matrices with upper left
entry `1` (`mem_arithSubgroup_iff`). For `R = ℤ/Nℤ` it defines `X_arith(N)` (`adelicArith`). -/
noncomputable def arithSubgroup : Subgroup (GL (Fin 2) R) :=
  (arithEmbedding R).range

/-- **The elements of `arithSubgroup R` are the invertible matrices `!![1, 0; 0, u]`**: those with
upper left entry `1` and off-diagonal entries `0`. -/
lemma mem_arithSubgroup_iff : g ∈ arithSubgroup R ↔ g 0 0 = 1 ∧ g 0 1 = 0 ∧ g 1 0 = 0 := by
  refine ⟨?_, fun ⟨h₀₀, h₀₁, h₁₀⟩ ↦ ⟨det g, Units.ext ?_⟩⟩
  · rintro ⟨u, rfl⟩
    simp [coe_arithEmbedding]
  · rw [coe_arithEmbedding, val_det_apply, det_fin_two, h₀₀, h₀₁, h₁₀]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h₀₀, h₀₁, h₁₀]

lemma det_arithEmbedding : det (arithEmbedding R u) = u :=
  Units.ext <| by simp [coe_arithEmbedding]

lemma arithEmbedding_injective : Injective (arithEmbedding R) :=
  LeftInverse.injective (det_arithEmbedding R)

lemma natCard_arithSubgroup : Nat.card (arithSubgroup R) = Nat.card Rˣ :=
  (Nat.card_congr (MonoidHom.ofInjective (arithEmbedding_injective R)).toEquiv).symm

/-- **The determinant of `arithSubgroup R` is surjective**: `det !![1, 0; 0, u] = u`. -/
lemma map_det_arithSubgroup : (arithSubgroup R).map det = ⊤ :=
  eq_top_iff.mpr fun u _ ↦ ⟨arithEmbedding R u, ⟨u, rfl⟩, det_arithEmbedding R u⟩

/-- **`arithSubgroup R` lies in the split Cartan subgroup of diagonal matrices**, so that
`X_arith(N)` covers `X_sp(N)`. -/
lemma arithSubgroup_le_diagonalTorus : arithSubgroup R ≤ diagonalTorus R 2 :=
  fun _ ⟨_, hu⟩ ↦ ⟨_, hu⟩

/-- **`arithSubgroup R` is trivial when `Rˣ` is**, as for `R = ℤ/Nℤ` with `N ≤ 2`, where
`X_arith(N)` is the full modular curve `X(N)`. -/
lemma arithSubgroup_eq_bot [Subsingleton Rˣ] : arithSubgroup R = ⊥ :=
  MonoidHom.range_eq_bot_iff.mpr (Subsingleton.elim _ _)

/-- The group `H` of the modular curve **`X_arith(N)`** (LMFDB `modcurve.xarith`): the inverse image
in `GL₂(ℤ̂) = ∏_ℓ GL₂(ℤ_ℓ)` of the subgroup `!![1, 0; 0, *]` of `GL₂(ℤ/Nℤ)`. -/
noncomputable def adelicArith (N : ℕ) [NeZero N] : Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) :=
  adelicPreimage N (arithSubgroup (ZMod N))

lemma index_arithSubgroup_zmod : (arithSubgroup (ZMod p)).index = p * (p ^ 2 - 1) :=
  index_eq_of_natCard_eq_mul (Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt)
    (by rw [natCard_arithSubgroup, Nat.card_units, Nat.card_zmod]) <| by
      rw [natCard_GL_fin_two_eq_sq_sub_one_mul, ZMod.card]
      ring1

/-- **The group of `X_arith(p)` has index `p (p² - 1)`** in `GL₂(ℤ̂)`, for a prime `p`, the order of
`SL₂(𝔽_p)`. -/
lemma index_adelicArith : (adelicArith p).index = p * (p ^ 2 - 1) :=
  (index_adelicPreimage p _).trans (index_arithSubgroup_zmod p)

end Matrix.GeneralLinearGroup
