import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.MetacyclicPresentation
import LeanBridge.ForMathlib.RepresentationTheory.FaithfulDegree
import LeanBridge.ForMathlib.RepresentationTheory.RationalCharacterBasis
import LeanBridge.ForMathlib.RepresentationTheory.SchurIndex
import TauCeti.RepresentationTheory.CharacterTable.Table

/-!
# Rational groups

A finite group `G` is rational (LMFDB `group.rational_group`, LeanBridge's `Group.IsRational`) if
all its complex characters are rational valued. Equivalently every `g` is conjugate to `gᵏ` for
every `k` prime to `|G|`: an automorphism `σ` of `ℂ` sends `χ(g)` to `χ(gʲ)` for some `j` prime to
`|G|`, so the condition makes `χ(g)` a rational algebraic integer, and conversely if the characters
are rational then `χ(gᵏ) = χ(g)` for every irreducible `χ`, and the irreducible characters separate
the conjugacy classes by the second orthogonality relation. The quaternion group `Q₈` is rational,
every element being conjugate to its inverse.

Some authors reserve the name ℚ-group for the stronger property that every complex representation
is realized over `ℚ`, as it is for the trivial group, whose representations are trivial. The
quaternion group is not a ℚ-group in this sense: its two-dimensional representation
`a 1 ↦ diag(i, -i)`, `xa 0 ↦ !![0, -1; 1, 0]` is not realized over `ℚ`, since the matrices over `ℚ`
of `a 1` and `xa 0` would satisfy trace identities that no `2 × 2` matrices over an ordered field
satisfy.

## Main definitions

* `Group.IsQGroup` (LMFDB `group.rational_group`): every complex representation is realized over
  `ℚ`.
* `QuaternionGroup.matrixI`, `QuaternionGroup.matrixJ`, `QuaternionGroup.twoDimHom`: the
  two-dimensional complex representation of `Q₈`.

## Main results

* `TauCeti.isConj_of_forall_irreducibleCharacter_eq`: the irreducible characters separate the
  conjugacy classes.
* `Group.isRational_iff_forall_isConj_pow` (LMFDB `group.rational_group`): `G` is rational
  exactly when `g` and `gᵏ` are conjugate for all `g` and all `k` prime to `|G|`.
* `QuaternionGroup.isRational_two` (LMFDB `group.rational_group`): `Q₈` is rational.
* `Group.IsQGroup.isRational` (LMFDB `group.rational_group`): a ℚ-group is rational.
* `QuaternionGroup.not_isQGroup_two` (LMFDB `group.rational_group`): `Q₈` is not a ℚ-group.
-/

open CategoryTheory Complex Matrix Module PresentedGroup TauCeti

variable {G : Type} [Group G]

namespace TauCeti

variable [Finite G] in
/-- **The irreducible characters separate the conjugacy classes**: by the second orthogonality
relation, `|C_g| ∑ᵢ χᵢ(g) χᵢ(h⁻¹)` is `|G|` or `0` according as `g` and `h` are conjugate. -/
lemma isConj_of_forall_irreducibleCharacter_eq {g h : G}
    (hgh : ∀ i, irreducibleCharacter ℂ i g = irreducibleCharacter ℂ i h) : IsConj g h := by
  classical
  by_contra hc
  have hg : (Nat.card (ConjClasses.mk g).carrier : ℂ) * ∑ i : Fin (Nat.card (ConjClasses G)),
      characterTable ℂ G i (ConjClasses.mk g) * characterTable ℂ G i (ConjClasses.mk h⁻¹) = 0 := by
    rw [card_conjClass_mul_sum_characterTable_mul_characterTable_inv, ite_eq_right hc]
  have hh : (Nat.card (ConjClasses.mk h).carrier : ℂ) * ∑ i : Fin (Nat.card (ConjClasses G)),
      characterTable ℂ G i (ConjClasses.mk h) * characterTable ℂ G i (ConjClasses.mk h⁻¹) =
      Nat.card G := by
    rw [card_conjClass_mul_sum_characterTable_mul_characterTable_inv, ite_eq_left (IsConj.refl h)]
  simp only [characterTable_apply, hgh] at hg hh
  have hcard (x : G) : (Nat.card (ConjClasses.mk x).carrier : ℂ) ≠ 0 :=
    have : Nonempty (ConjClasses.mk x).carrier := ⟨⟨x, ConjClasses.mem_carrier_mk⟩⟩
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  rw [(mul_eq_zero.mp hg).resolve_left (hcard g), mul_zero] at hh
  exact (Nat.cast_ne_zero.mpr Nat.card_pos.ne') hh.symm

end TauCeti

namespace Group

variable [Finite G] in
/-- **A finite group is rational exactly when every `g` is conjugate to `gᵏ` for every `k` prime to
`|G|`** (LMFDB `group.rational_group`). An automorphism `σ` of `ℂ` raises the `|G|`-th roots of
unity to a power `j` prime to `|G|`, so it sends `χ(g)` to `χ(gʲ)`, which is `χ(g)` when `g` and
`gʲ` are conjugate; an algebraic number fixed by every automorphism of `ℂ` is rational. Conversely a
rational character satisfies `χ(gᵏ) = χ(g)`, and the irreducible characters separate the conjugacy
classes. -/
lemma isRational_iff_forall_isConj_pow :
    IsRational G ↔ ∀ g : G, ∀ k : ℕ, k.Coprime (Nat.card G) → IsConj g (g ^ k) := by
  refine ⟨fun hG g k hk ↦ isConj_of_forall_irreducibleCharacter_eq fun i ↦ ?_, fun h X g ↦ ?_⟩
  · have hχ : (FDRep.of (irreducibleRepresentation ℂ i)).character = irreducibleCharacter ℂ i := by
      rw [FDRep.character_of, character_irreducibleRepresentation]
    rw [← hχ]
    exact ((hG _).character_pow_eq (hk.symm.coprime_dvd_left (orderOf_dvd_natCard g))).symm
  · have hN : Nat.card G ≠ 0 := Nat.card_pos.ne'
    have : NeZero (Nat.card G) := ⟨hN⟩
    have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / Nat.card G)) (Nat.card G) :=
      Complex.isPrimitiveRoot_exp _ hN
    refine Complex.exists_eq_ratCast_of_forall_algEquiv_apply_eq
      (End.isIntegral_trace_of_pow_eq_one (orderOf_pos g).ne'
        (by rw [← map_pow, pow_orderOf_eq_one, map_one])).tower_top fun σ ↦ ?_
    rcases isConj_iff.mp (h g _ (ZMod.val_coe_unit_coprime (hζ.autToPow ℚ σ))) with ⟨c, hc⟩
    rw [← FDRep.character_ρ]
    exact (Representation.map_character_eq_character_pow_of_isPrimitiveRoot X.ρ hζ
      (Nat.cast_ne_zero.mpr hN) pow_card_eq_one' σ.toRingEquiv.toRingHom
      (hζ.autToPow_spec ℚ σ).symm).trans (by rw [← hc, Representation.char_conj])

end Group

namespace QuaternionGroup

/-- **The quaternion group `Q₈` is rational** (LMFDB `group.rational_group`): every element is
conjugate to its inverse, and `gᵏ` is `g` or `g⁻¹` for odd `k`, the exponent being `4`. -/
lemma isRational_two : Group.IsRational (QuaternionGroup 2) := by
  have hconj : ∀ x : QuaternionGroup 2, ∃ c : QuaternionGroup 2, c * x * c⁻¹ = x⁻¹ := by
    decide
  have h4 : ∀ x : QuaternionGroup 2, x ^ 4 = 1 := by
    decide
  refine Group.isRational_iff_forall_isConj_pow.mpr fun g k hk ↦ ?_
  rw [Nat.card_eq_fintype_card, card] at hk
  have hodd : k % 2 = 1 := by
    by_contra h0
    have h2 : 2 ∣ Nat.gcd k (4 * 2) := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero (by omega)) (by norm_num)
    rw [hk] at h2
    exact absurd h2 (by decide)
  rcases (show k % 4 = 1 ∨ k % 4 = 3 by omega) with h | h <;>
    rw [← Nat.div_add_mod k 4, h, pow_add, pow_mul, h4, one_pow, one_mul]
  · rw [pow_one]
  · rw [eq_inv_of_mul_eq_one_left (by rw [← pow_succ, h4] : g ^ 3 * g = 1)]
    exact isConj_iff.mpr (hconj g)

end QuaternionGroup

namespace Matrix

lemma false_of_trace_quaternion {A B : Matrix (Fin 2) (Fin 2) ℚ} (h1 : A.trace = 0)
    (h2 : B.trace = 0) (h3 : (A * A).trace = -2) (h4 : (B * B).trace = -2)
    (h5 : (A * B).trace = 0) : False := by
  simp only [trace_fin_two, mul_apply, Fin.sum_univ_two] at h1 h2 h3 h4 h5
  have hE1 : A 0 0 ^ 2 + A 0 1 * A 1 0 + 1 = 0 := by
    linear_combination (1 / 2 : ℚ) * h3 - (1 / 2 : ℚ) * (A 1 1 - A 0 0) * h1
  have hE2 : B 0 0 ^ 2 + B 0 1 * B 1 0 + 1 = 0 := by
    linear_combination (1 / 2 : ℚ) * h4 - (1 / 2 : ℚ) * (B 1 1 - B 0 0) * h2
  have hE3 : 2 * A 0 0 * B 0 0 + A 0 1 * B 1 0 + A 1 0 * B 0 1 = 0 := by
    linear_combination h5 + B 0 0 * h1 - A 1 1 * h2
  have key : 4 * (A 0 1 + A 1 0) ^ 2 + 4 * (B 0 1 + B 1 0) ^ 2 + 16 + 16 * B 0 0 ^ 2 +
      16 * A 0 0 ^ 2 + 4 * ((A 0 1 + A 1 0) * B 0 0 - A 0 0 * (B 0 1 + B 1 0)) ^ 2 = 0 := by
    linear_combination (4 * (B 0 1 - B 1 0) ^ 2 + 16 * (B 0 0 ^ 2 + B 0 1 * B 1 0 + 1)) * hE1 +
      4 * (A 0 1 - A 1 0) ^ 2 * hE2 -
      (4 * (A 0 1 - A 1 0) * (B 0 1 - B 1 0) + 4 * (2 * A 0 0 * B 0 0 + A 0 1 * B 1 0 +
        A 1 0 * B 0 1)) * hE3
  nlinarith [sq_nonneg (A 0 1 + A 1 0), sq_nonneg (B 0 1 + B 1 0), sq_nonneg (B 0 0),
    sq_nonneg (A 0 0), sq_nonneg ((A 0 1 + A 1 0) * B 0 0 - A 0 0 * (B 0 1 + B 1 0))]

end Matrix

namespace QuaternionGroup

/-- The matrix `diag(i, -i)`, invertible over `ℂ`, image of `a 1` in the two-dimensional complex
representation of `Q₈`. -/
noncomputable def matrixI : GL (Fin 2) ℂ :=
  ⟨!![I, 0; 0, -I], !![-I, 0; 0, I], by simp [one_fin_two], by simp [one_fin_two]⟩

/-- The matrix `!![0, -1; 1, 0]`, image of `xa 0` in the two-dimensional complex representation of
`Q₈`. -/
noncomputable def matrixJ : GL (Fin 2) ℂ :=
  ⟨!![0, -1; 1, 0], !![0, 1; -1, 0], by simp [one_fin_two], by simp [one_fin_two]⟩

lemma matrixI_pow_four : matrixI ^ (2 * 2) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixI, pow_succ]

lemma matrixI_sq_eq_matrixJ_sq : matrixI ^ 2 = matrixJ ^ 2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixI, matrixJ, pow_succ]

lemma matrixJ_mul_matrixI_mul_inv : matrixJ * matrixI * matrixJ⁻¹ * matrixI = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixI, matrixJ]

lemma lift_relators_two : ∀ w ∈ relators 2, FreeGroup.lift ![matrixI, matrixJ] w = 1 := by
  rintro w (rfl | rfl | rfl)
  · simpa using matrixI_pow_four
  · simp [matrixI_sq_eq_matrixJ_sq]
  · simpa using matrixJ_mul_matrixI_mul_inv

/-- The two-dimensional complex representation of `Q₈ = Dic₂` sending `a 1` to `diag(i, -i)` and
`xa 0` to `!![0, -1; 1, 0]`, defined through the presentation of `Dic₂`. -/
noncomputable def twoDimHom : QuaternionGroup 2 →* GL (Fin 2) ℂ :=
  (PresentedGroup.toGroup lift_relators_two).comp (presentedGroupMulEquiv 2).symm.toMonoidHom

lemma presentedGroupMulEquiv_symm_a_one :
    (presentedGroupMulEquiv 2).symm (a 1) = PresentedGroup.of 0 :=
  (MulEquiv.symm_apply_eq _).mpr (toGroup.of (lift_relators 2) (x := 0)).symm

lemma presentedGroupMulEquiv_symm_xa_zero :
    (presentedGroupMulEquiv 2).symm (xa 0) = PresentedGroup.of 1 :=
  (MulEquiv.symm_apply_eq _).mpr (toGroup.of (lift_relators 2) (x := 1)).symm

lemma twoDimHom_a_one : twoDimHom (a 1) = matrixI := by
  rw [twoDimHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    presentedGroupMulEquiv_symm_a_one]
  exact toGroup.of _

lemma twoDimHom_xa_zero : twoDimHom (xa 0) = matrixJ := by
  rw [twoDimHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    presentedGroupMulEquiv_symm_xa_zero]
  exact toGroup.of _

lemma character_twoDim (g : QuaternionGroup 2) :
    (FDRep.of (GeneralLinearGroup.representation twoDimHom)).character g =
      (twoDimHom g : Matrix (Fin 2) (Fin 2) ℂ).trace :=
  (congrFun (FDRep.character_of _) g).trans (GeneralLinearGroup.character_representation _ g)

end QuaternionGroup

namespace Group

variable (G) in
/-- A group `G` is a **ℚ-group** in the strong sense (LMFDB `group.rational_group`), the term some
authors reserve for a property stronger than rationality: every complex representation `V` of `G`
is realized over `ℚ`, that is `V ≅ ℂ ⊗_ℚ W` for a representation `W` of `G` over `ℚ`, here the
bottom subfield `ℚ` of `ℂ` (LeanBridge's `FDRep.IsRealizedOver`). -/
def IsQGroup : Prop :=
  ∀ V : FDRep ℂ G, V.IsRealizedOver ℚ (⊥ : IntermediateField ℚ ℂ)

/-- **A ℚ-group is rational**: the character of `ℂ ⊗_ℚ W` is that of `W`, with values in `ℚ`. -/
lemma IsQGroup.isRational (h : IsQGroup G) : IsRational G := fun V g ↦ by
  rcases h V with ⟨W, ⟨e⟩⟩
  rcases IntermediateField.mem_bot.mp (W.character g).2 with ⟨q, hq⟩
  refine ⟨q, (congrFun ((FDRep.char_iso e).symm.trans (FDRep.character_baseChange W)) g).trans ?_⟩
  exact hq.symm.trans (eq_ratCast (algebraMap ℚ ℂ) q)

lemma isQGroup_unit : IsQGroup Unit := fun V ↦ by
  let d : ℕ := Module.finrank ℂ V
  let W : FDRep (⊥ : IntermediateField ℚ ℂ) Unit := FDRep.of
    (1 : Unit →* (Fin d → (⊥ : IntermediateField ℚ ℂ)) →ₗ[(⊥ : IntermediateField ℚ ℂ)]
      (Fin d → (⊥ : IntermediateField ℚ ℂ)))
  have hd : Module.finrank ℂ (TensorProduct (⊥ : IntermediateField ℚ ℂ) ℂ W) = d :=
    Module.finrank_baseChange.trans (Module.finrank_fin_fun _)
  exact ⟨W, ⟨Action.mkIso (LinearEquiv.ofFinrankEq _ _ hd).toFGModuleCatIso fun g ↦ by
    rw [Subsingleton.elim g 1, Action.ρ_one, Action.ρ_one, End.one_asHom, End.one_asHom,
      Category.id_comp, Category.comp_id]⟩⟩

end Group

namespace QuaternionGroup

/-- **The quaternion group `Q₈` is not a ℚ-group in the strong sense** (LMFDB
`group.rational_group`), although it is rational (`QuaternionGroup.isRational_two`): its
two-dimensional complex representation `a 1 ↦ diag(i, -i)`, `xa 0 ↦ !![0, -1; 1, 0]` is not
realized over `ℚ`. The matrices `A`, `B` over `ℚ` of `a 1` and `xa 0` in a realization would have
traces `tr A = tr B = tr AB = 0` and `tr A² = tr B² = -2`, which no `2 × 2` matrices over an ordered
field have. -/
lemma not_isQGroup_two : ¬Group.IsQGroup (QuaternionGroup 2) := fun h ↦ by
  rcases h (FDRep.of (GeneralLinearGroup.representation twoDimHom)) with ⟨W, ⟨e⟩⟩
  have hχ (g : QuaternionGroup 2) : algebraMap (⊥ : IntermediateField ℚ ℂ) ℂ (W.character g) =
      (twoDimHom g : Matrix (Fin 2) (Fin 2) ℂ).trace :=
    (congrFun ((FDRep.character_baseChange W).symm.trans (FDRep.char_iso e)) g).trans
      (character_twoDim g)
  have hval (g : QuaternionGroup 2) (q : ℚ)
      (hq : (twoDimHom g : Matrix (Fin 2) (Fin 2) ℂ).trace = q) :
      IntermediateField.botEquiv ℚ ℂ (W.character g) = q := by
    have hW : W.character g = algebraMap ℚ _ q :=
      (algebraMap (⊥ : IntermediateField ℚ ℂ) ℂ).injective <| by
        rw [hχ, hq, ← IsScalarTower.algebraMap_apply]
        exact (eq_ratCast _ q).symm
    rw [hW, IntermediateField.botEquiv_def]
  have hdim : finrank (⊥ : IntermediateField ℚ ℂ) W = 2 := by
    have h1 : algebraMap (⊥ : IntermediateField ℚ ℂ) ℂ (W.character 1) =
        (twoDimHom 1 : Matrix (Fin 2) (Fin 2) ℂ).trace :=
      hχ 1
    rw [FDRep.char_one, map_natCast, map_one, Units.val_one, trace_one, Fintype.card_fin] at h1
    exact_mod_cast h1
  let b : Basis (Fin 2) (⊥ : IntermediateField ℚ ℂ) W := finBasisOfFinrankEq _ W hdim
  let M (g : QuaternionGroup 2) : Matrix (Fin 2) (Fin 2) ℚ :=
    (LinearMap.toMatrix b b (W.ρ g)).map (IntermediateField.botEquiv ℚ ℂ)
  have htr (g : QuaternionGroup 2) :
      (M g).trace = IntermediateField.botEquiv ℚ ℂ (W.character g) := by
    rw [← AddMonoidHom.map_trace, ← LinearMap.trace_eq_matrix_trace]
    rfl
  have hmul (g h : QuaternionGroup 2) : M g * M h = M (g * h) := by
    simp only [M]
    rw [← Matrix.map_mul, ← LinearMap.toMatrix_mul, ← map_mul]
  refine false_of_trace_quaternion (A := M (a 1)) (B := M (xa 0)) ?_ ?_ ?_ ?_ ?_
  · rw [htr, hval (a 1) 0 (by simp [twoDimHom_a_one, matrixI])]
  · rw [htr, hval (xa 0) 0 (by simp [twoDimHom_xa_zero, matrixJ])]
  · rw [hmul, htr, hval _ (-2) (by rw [map_mul, twoDimHom_a_one]; norm_num [matrixI])]
  · rw [hmul, htr, hval _ (-2) (by rw [map_mul, twoDimHom_xa_zero]; norm_num [matrixJ])]
  · rw [hmul, htr, hval _ 0
      (by rw [map_mul, twoDimHom_a_one, twoDimHom_xa_zero]; simp [matrixI, matrixJ])]

end QuaternionGroup
