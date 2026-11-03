import LeanBridge.ForMathlib.NumberTheory.SatoTateGroup.KoikeTeradaCharacter
import TauCeti.Algebra.Lie.Submodule.Atom

/-!
# The Koike–Terada functions are the irreducible characters of `USp(2g)`

The irreducible representations of `USp(2g)` are in bijection with the partitions with at most `g`
parts, by the highest weight for the torus (`SatoTateGroup.HasSymplecticMonomial`), and the
character of the representation of highest weight `∑ c_k ω_k` is the Koike–Terada function
`SatoTateGroup.symplecticSchur c` of the eigenvalues. So the moment matrix over the irreducible
characters of the ambient group is the moment matrix `SatoTateGroup.symplecticMomentMatrix`, and the
order of its rows and columns is a linear order, the order of the exponent vectors `c`.

## Main results

* `SatoTateGroup.exists_hasSymplecticMonomial`: every partition is a highest weight.
* `SatoTateGroup.exists_hasSymplecticMonomial_of_class`: an irreducible character of `USp(2g)` has a
  highest weight.
* `SatoTateGroup.HasSymplecticMonomial.ambientCharacter_eq`: the irreducible character of highest
  weight `∑ c_k ω_k` is the Koike–Terada function `SatoTateGroup.symplecticSchur c`.
* `SatoTateGroup.HasSymplecticMonomial.eq_of_eq`: the highest weight determines the character.
* `SatoTateGroup.exists_ambientCharacter_eq_symplecticSchur`: every Koike–Terada function is an
  irreducible character of `USp(2g)`.
* `SatoTateGroup.exists_symplecticSchur_eq_ambientCharacter`: every irreducible character of
  `USp(2g)` is a Koike–Terada function.
* `SatoTateGroup.momentMatrix_eq_symplecticMomentMatrix`: the moment matrix over the irreducible
  characters is the moment matrix of the Koike–Terada functions.
* `SatoTateGroup.HasSymplecticMonomial.isBeforeInMomentMatrix_iff`: in odd weight, the order of the
  rows and columns of the moment matrix is the order of the exponent vectors.
* `SatoTateGroup.isLinearOrder_isBeforeInMomentMatrix`: in odd weight it is a linear order.
-/

open LieAlgebra LieModule Matrix Module TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

namespace SatoTateGroup

section Classification

variable {w g d : ℕ} {hw : Odd w} {hd : d = g + g} {c : Fin g → ℕ}

section Weights

variable {P : Type*} [Fintype P] [DecidableEq P]
  {U : LieSubmodule ℂ (Symplectic.sp (Fin g) ℂ) (SpTensor P g)}

lemma exists_weight_of_apply_ne_zero (v : U) {a : P → Fin g ⊕ Fin g} (h : v.1 a ≠ 0) :
    ∃ μ : Weight ℂ (spCartan (g := g)) U, ∀ θ : Fin g → ℂ,
      (μ : Dual ℂ (spCartan (g := g))) ⟨spDiag θ, spDiag_mem_spCartan θ⟩ =
        ∑ p, spValue θ (a p) := by
  have hv : v ∈ ⨆ μ : Weight ℂ (spCartan (g := g)) U,
      (genWeightSpace U (μ : spCartan (g := g) → ℂ)).toSubmodule := by
    rw [← LieSubmodule.iSup_toSubmodule, iSup_genWeightSpace_eq_top']
    exact Submodule.mem_top
  revert h
  induction hv using Submodule.iSup_induction' with
  | mem μ x hx =>
    intro h
    refine ⟨μ, fun θ ↦ ?_⟩
    have h₁ : x ∈ weightSpace U (μ : spCartan (g := g) → ℂ) := by
      rwa [← genWeightSpace_eq_weightSpace]
    have h₂ :
        ⁅spDiag θ, x⁆ = (μ : Dual ℂ (spCartan (g := g))) ⟨spDiag θ, spDiag_mem_spCartan θ⟩ • x :=
      (mem_weightSpace _ _).mp h₁ ⟨spDiag θ, spDiag_mem_spCartan θ⟩
    have h₃ : (∑ p, spValue θ (a p)) * x.1 a = (μ : Dual ℂ (spCartan (g := g)))
        ⟨spDiag θ, spDiag_mem_spCartan θ⟩ * x.1 a :=
      (lie_spDiag_apply U x a θ).symm.trans (congrFun (congrArg Subtype.val h₂) a)
    exact (mul_right_cancel₀ h h₃).symm
  | zero => exact fun h ↦ absurd rfl h
  | add x y _ _ hx hy =>
    intro h
    by_cases hxa : x.1 a = 0
    · refine hy fun hya ↦ h ?_
      have h₁ : (x + y : U).1 a = x.1 a + y.1 a := rfl
      rw [h₁, hxa, hya, add_zero]
    · exact hx hxa

lemma exists_natCast_sum_apply_spDelta {φ : Dual ℂ (spCartan (g := g))}
    (hφ : φ ∈ posRootCone (spRootSystem g) spBase) (i : Fin g) :
    ∃ n : ℕ, ∑ j ∈ Finset.Iic i, φ (spDelta j) = n := by
  have h₁ (k : Fin g) : ∑ j ∈ Finset.Iic i, spEpsilon k (spDelta j) = if k ≤ i then 1 else 0 := by
    simp only [spEpsilon_spDelta_eq_ite, Finset.sum_ite_eq, Finset.mem_Iic]
  induction hφ using AddSubmonoid.closure_induction with
  | mem x hx =>
    rcases hx with ⟨r, hr, rfl⟩
    rcases mem_spBase_support.mp hr with ⟨k, rfl⟩
    by_cases h : (k : ℕ) + 1 < g
    · rw [root_spSimpleIdx_of_lt k h]
      simp only [LinearMap.sub_apply, Finset.sum_sub_distrib, h₁]
      by_cases h₂ : k ≤ i
      · by_cases h₃ : (⟨k + 1, h⟩ : Fin g) ≤ i
        · exact ⟨0, by simp [h₂, h₃]⟩
        · exact ⟨1, by simp [h₂, h₃]⟩
      · have h₃ : ¬(⟨k + 1, h⟩ : Fin g) ≤ i := fun h₄ ↦ h₂ (le_trans (Fin.le_def.mpr (by simp)) h₄)
        exact ⟨0, by simp [h₂, h₃]⟩
    · rw [root_spSimpleIdx_of_not_lt k h]
      simp only [LinearMap.add_apply, Finset.sum_add_distrib, h₁]
      by_cases h₂ : k ≤ i
      · exact ⟨2, by norm_num [h₂]⟩
      · exact ⟨0, by simp [h₂]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    rcases hx with ⟨m, hm⟩
    rcases hy with ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    simp only [LinearMap.add_apply, Finset.sum_add_distrib, hm, hn, Nat.cast_add]

lemma torusLog_eq_smul_spDelta (j : Fin g) (s : ℝ) :
    (⟨spDiag (torusLog (Pi.single j s)), spDiag_mem_spCartan _⟩ : spCartan (g := g)) =
      ((s : ℂ) * Complex.I) • spDelta j := by
  have h₁ : torusLog (Pi.single j s) = ((s : ℂ) * Complex.I) • (Pi.single j 1 : Fin g → ℂ) := by
    funext i
    by_cases h : i = j
    · subst h
      simp [torusLog]
    · simp [torusLog, h]
  have h₂ : spDiag (torusLog (Pi.single j s)) =
      ((s : ℂ) * Complex.I) • spDiag (Pi.single j 1 : Fin g → ℂ) := by
    rw [h₁, map_smul]
  exact Subtype.ext h₂

lemma eq_of_forall_exp_eq {z : ℂ} {m : ℤ} (h : ∀ s : ℝ, Complex.exp ((s : ℂ) * Complex.I * z) =
    (Complex.exp ((s : ℂ) * Complex.I)) ^ m) : z = m := by
  have h₁ :
      HasDerivAt (fun s : ℂ ↦ Complex.exp (s * (Complex.I * (z - m)))) (Complex.I * (z - m)) 0 := by
    have h₂ : HasDerivAt (fun s : ℂ ↦ Complex.exp (id s * (Complex.I * (z - m))))
        (Complex.exp (id 0 * (Complex.I * (z - m))) * (1 * (Complex.I * (z - m)))) 0 :=
      ((hasDerivAt_id (0 : ℂ)).mul_const (Complex.I * (z - m))).cexp
    simpa using h₂
  have h₂ : HasDerivAt (fun s : ℝ ↦ Complex.exp ((s : ℂ) * (Complex.I * (z - m))))
      (Complex.I * (z - m)) 0 := h₁.comp_ofReal
  have h₃ (s : ℝ) : Complex.exp ((s : ℂ) * (Complex.I * (z - m))) = 1 := by
    have h₄ : (s : ℂ) * (Complex.I * (z - m)) =
        (s : ℂ) * Complex.I * z + -(m * ((s : ℂ) * Complex.I)) := by
      ring1
    rw [h₄, Complex.exp_add, h, Complex.exp_neg, Complex.exp_int_mul, mul_inv_cancel₀]
    exact zpow_ne_zero _ (Complex.exp_ne_zero _)
  have h₄ : HasDerivAt (fun s : ℝ ↦ Complex.exp ((s : ℂ) * (Complex.I * (z - m)))) (0 : ℂ) 0 := by
    simp only [h₃]
    exact hasDerivAt_const _ _
  have h₆ : z - m = 0 := (mul_eq_zero.mp (h₂.unique h₄)).resolve_left Complex.I_ne_zero
  exact sub_eq_zero.mp h₆

variable (hw) in
lemma apply_spDelta_eq_of_forall_torus {x : U} {m' : Fin g → ℤ}
    (hxt : ∀ t : Fin g → Circle, spGroupRep hw U (uspTorus hw rfl t) x =
      (∏ k, (t k : ℂ) ^ m' k) • x) {a : P → Fin g ⊕ Fin g} (ha : x.1 a ≠ 0)
    {μ : Dual ℂ (spCartan (g := g))}
    (hμ : ∀ θ : Fin g → ℂ, μ ⟨spDiag θ, spDiag_mem_spCartan θ⟩ = ∑ p, spValue θ (a p)) (j : Fin g) :
    μ (spDelta j) = m' j := by
  refine eq_of_forall_exp_eq fun s ↦ ?_
  have h₂ : (spGroupRep hw U (uspTorus hw rfl (torusCoord (Pi.single j s))) x).1 a =
      ((∏ k, (torusCoord (Pi.single j s) k : ℂ) ^ m' k) • x).1 a :=
    congrFun (congrArg Subtype.val (hxt (torusCoord (Pi.single j s)))) a
  have h₄ : (∏ k, (torusCoord (Pi.single j s) k : ℂ) ^ m' k) =
      Complex.exp ((s : ℂ) * Complex.I) ^ m' j := by
    rw [Finset.prod_eq_single j]
    · rw [coe_torusCoord]
      simp [torusLog]
    · intro k _ hk
      rw [coe_torusCoord]
      simp [torusLog, hk]
    · simp
  have h₅ : Complex.exp (∑ p, spValue (torusLog (Pi.single j s)) (a p)) =
      Complex.exp ((s : ℂ) * Complex.I) ^ m' j :=
    mul_right_cancel₀ ha (((apply_spGroupRep_torus hw (Pi.single j s) U x a).symm.trans h₂).trans
      (congrArg (· * x.1 a) h₄))
  rw [← hμ, torusLog_eq_smul_spDelta, map_smul, smul_eq_mul] at h₅
  exact h₅

lemma toLex_le_of_sub_mem_posRootCone {μ : Dual ℂ (spCartan (g := g))} {m' : Fin g → ℤ}
    (hφ : spPartitionWeight c - μ ∈ posRootCone (spRootSystem g) spBase)
    (h₁ : ∀ j, μ (spDelta j) = m' j) : toLex m' ≤ toLex fun i ↦ (highestWeight c i : ℤ) := by
  by_contra hcon
  rcases not_le.mp hcon with ⟨i, hi₁, hi₂⟩
  rcases exists_natCast_sum_apply_spDelta hφ i with ⟨n, hn⟩
  have h₂ (j : Fin g) :
      (spPartitionWeight c - μ) (spDelta j) = ((highestWeight c j - m' j : ℤ) : ℂ) := by
    rw [LinearMap.sub_apply, spPartitionWeight_spDelta, h₁]
    push_cast
    rfl
  rw [Finset.sum_eq_single i, h₂] at hn
  · have h₃ : ((highestWeight c i : ℤ) - m' i) = n := by
      exact_mod_cast hn
    have h₄ : (n : ℤ) ≥ 0 := Int.natCast_nonneg n
    have h₅ : ((highestWeight c i : ℕ) : ℤ) < m' i := hi₂
    omega
  · intro j hj hne
    have h₃ : j < i := lt_of_le_of_ne (Finset.mem_Iic.mp hj) hne
    have h₄ : ((highestWeight c j : ℕ) : ℤ) = m' j := hi₁ j h₃
    rw [h₂, ← h₄]
    simp
  · simp

lemma sub_coe_weight_mem_posRootCone {v : U}
    (hv : IsHighestWeightVector spBase (spPartitionWeight c) v)
    (hgen : LieSubmodule.lieSpan ℂ (Symplectic.sp (Fin g) ℂ) {v} = ⊤)
    (μ : Weight ℂ (spCartan (g := g)) U) :
    spPartitionWeight c - (μ : Dual ℂ (spCartan (g := g))) ∈ posRootCone (spRootSystem g) spBase :=
  sub_mem_posRootCone_of_genWeightSpace_ne_bot_of_isHighestWeightVector_of_lieSpan_eq_top
    (chi := (μ : Dual ℂ (spCartan (g := g)))) hv hgen μ.genWeightSpace_ne_bot

variable (hw) in
lemma hasSymplecticMonomial_of_equiv {v : U}
    (hv : IsHighestWeightVector spBase (spPartitionWeight c) v)
    (hgen : LieSubmodule.lieSpan ℂ (Symplectic.sp (Fin g) ℂ) {v} = ⊤)
    {χ : IrrepClass ℂ (ambientGroup w (g + g))} (e : U ≃ₗ[ℂ] EuclideanSpace ℂ (Fin χ.model.dim))
    (he : ∀ h x, e (spGroupRep hw U h x) = χ.model.rep h (e x)) :
    HasSymplecticMonomial hw rfl χ c := by
  have harg (t : Fin g → Circle) : torusCoord (fun j ↦ Complex.arg (t j)) = t :=
    funext fun j ↦ Circle.exp_arg (t j)
  refine ⟨⟨e v, ?_, fun t ↦ ?_⟩, fun m' hm' ↦ ?_⟩
  · exact fun h₀ ↦ hv.ne_zero (e.map_eq_zero_iff.mp h₀)
  · rw [← he]
    conv_lhs => rw [← harg t]
    rw [spGroupRep_torus_apply hw _ U (hv.lie_eq_smul ⟨_, spDiag_mem_spCartan _⟩), map_smul]
    congr 1
    rw [spPartitionWeight_spDiag, Complex.exp_sum]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [Complex.exp_nat_mul, zpow_natCast]
    congr 1
    exact (coe_torusCoord (fun j ↦ Complex.arg (t j)) j).symm.trans
      (congrArg (fun r : Circle ↦ (r : ℂ)) (Circle.exp_arg (t j)))
  · rcases hm' with ⟨v', hv', hm'⟩
    let x : U := e.symm v'
    have hx : x ≠ 0 := fun h₀ ↦ hv' (e.symm.map_eq_zero_iff.mp h₀)
    have hxt (t : Fin g → Circle) :
        spGroupRep hw U (uspTorus hw rfl t) x = (∏ k, (t k : ℂ) ^ m' k) • x := by
      refine e.injective ?_
      rw [he, map_smul, LinearEquiv.apply_symm_apply, hm']
    have hne : ∃ a, x.1 a ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hx (Subtype.ext (funext hcon))
    rcases hne with ⟨a, ha⟩
    rcases exists_weight_of_apply_ne_zero x ha with ⟨μ, hμ⟩
    exact toLex_le_of_sub_mem_posRootCone (sub_coe_weight_mem_posRootCone hv hgen μ)
      (apply_spDelta_eq_of_forall_torus hw hxt ha hμ)

variable (hw) in
lemma ambientCharacter_eq_symplecticSchur_of_equiv {v : U}
    (hv : IsHighestWeightVector spBase (spPartitionWeight c) v)
    (hgen : LieSubmodule.lieSpan ℂ (Symplectic.sp (Fin g) ℂ) {v} = ⊤)
    {χ : IrrepClass ℂ (ambientGroup w (g + g))} (e : U ≃ₗ[ℂ] EuclideanSpace ℂ (Fin χ.model.dim))
    (he : ∀ h x, e (spGroupRep hw U h x) = χ.model.rep h (e x)) (h : ambientGroup w (g + g)) :
    ambientCharacter w (g + g) χ h =
      symplecticSchur c (h : Matrix (Fin (g + g)) (Fin (g + g)) ℂ).charpoly.roots :=
  (character_model_eq_trace e he h).trans (trace_spGroupRep_eq_symplecticSchur hw hv hgen h)

end Weights

variable (hw c) in
lemma exists_hasSymplecticMonomial_and_eq : ∃ χ : IrrepClass ℂ (ambientGroup w (g + g)),
    HasSymplecticMonomial hw rfl χ c ∧ ∀ h, ambientCharacter w (g + g) χ h =
      symplecticSchur c (h : Matrix (Fin (g + g)) (Fin (g + g)) ℂ).charpoly.roots := by
  let U : LieSubmodule ℂ (Symplectic.sp (Fin g) ℂ) (SpTensor (YoungBox c) g) :=
    LieSubmodule.lieSpan ℂ (Symplectic.sp (Fin g) ℂ)
      ({youngVector (g := g) c} : Set (SpTensor (YoungBox c) g))
  let v : U := ⟨youngVector c, LieSubmodule.subset_lieSpan rfl⟩
  have hv : IsHighestWeightVector spBase (spPartitionWeight c) v :=
    isHighestWeightVector_coe_iff.mp (isHighestWeightVector_youngVector c)
  have hgen : LieSubmodule.lieSpan ℂ (Symplectic.sp (Fin g) ℂ) {v} = ⊤ :=
    lieSpan_singleton_eq_top_of_lieSpan_eq rfl
  have : LieModule.IsIrreducible ℂ (Symplectic.sp (Fin g) ℂ) U :=
    isIrreducible_of_isHighestWeightVector_of_lieSpan_eq_top hv hgen
  rcases exists_irrepClass_equiv (spGroupRep hw U) (isIrreducible_spGroupRep hw U)
    (continuous_spGroupRep hw U) with ⟨χ, e, he⟩
  exact ⟨χ, hasSymplecticMonomial_of_equiv hw hv hgen e he,
    ambientCharacter_eq_symplecticSchur_of_equiv hw hv hgen e he⟩

variable (hw) in
lemma exists_hasSymplecticMonomial_and_eq_of_class (χ : IrrepClass ℂ (ambientGroup w (g + g))) :
    ∃ c : Fin g → ℕ, HasSymplecticMonomial hw rfl χ c ∧ ∀ h, ambientCharacter w (g + g) χ h =
      symplecticSchur c (h : Matrix (Fin (g + g)) (Fin (g + g)) ℂ).charpoly.roots := by
  rcases exists_lieSubmodule_equiv hw χ with ⟨n, U, _, e, he⟩
  rcases exists_isHighestWeightVector_and_lieSpan_eq_top (M := U) (spBase (g := g)) with
    ⟨lam, v, hv, hgen⟩
  rcases exists_apply_spDelta_eq_highestWeight hv.isDominantIntegral with ⟨c, hc⟩
  have h₁ : lam = spPartitionWeight c :=
    dual_ext fun i ↦ by rw [hc, spPartitionWeight_spDelta]
  subst h₁
  exact ⟨c, hasSymplecticMonomial_of_equiv hw hv hgen e he,
    ambientCharacter_eq_symplecticSchur_of_equiv hw hv hgen e he⟩

variable (hw hd c) in
/-- **Every partition with at most `g` parts is the highest weight of an irreducible character of
`USp(2g)`.** -/
lemma exists_hasSymplecticMonomial :
    ∃ χ : IrrepClass ℂ (ambientGroup w d), HasSymplecticMonomial hw hd χ c := by
  subst hd
  rcases exists_hasSymplecticMonomial_and_eq hw c with ⟨χ, h, -⟩
  exact ⟨χ, h⟩

variable (hw hd) in
/-- **Every irreducible character of `USp(2g)` has a highest weight, a partition with at most `g`
parts.** -/
lemma exists_hasSymplecticMonomial_of_class (χ : IrrepClass ℂ (ambientGroup w d)) :
    ∃ c : Fin g → ℕ, HasSymplecticMonomial hw hd χ c := by
  subst hd
  rcases exists_hasSymplecticMonomial_and_eq_of_class hw χ with ⟨c, h, -⟩
  exact ⟨c, h⟩

variable {χ χ' : IrrepClass ℂ (ambientGroup w d)}

/-- **The irreducible character of `USp(2g)` of highest weight `∑ c_k ω_k` is the Koike–Terada
function** `SatoTateGroup.symplecticSchur c` of the eigenvalues. -/
lemma HasSymplecticMonomial.ambientCharacter_eq (hc : HasSymplecticMonomial hw hd χ c)
    (h : ambientGroup w d) :
    ambientCharacter w d χ h = symplecticSchur c (h : Matrix (Fin d) (Fin d) ℂ).charpoly.roots := by
  subst hd
  rcases exists_hasSymplecticMonomial_and_eq_of_class hw χ with ⟨c', h₁, h₂⟩
  rw [h₂, h₁.eq hc]

/-- **The highest weight determines the irreducible character.** -/
lemma HasSymplecticMonomial.eq_of_eq (hc : HasSymplecticMonomial hw hd χ c)
    (hc' : HasSymplecticMonomial hw hd χ' c) : χ = χ' :=
  injective_ambientCharacter w d <| ContinuousMap.ext fun h ↦ by
    rw [hc.ambientCharacter_eq, hc'.ambientCharacter_eq]

variable (c) in
/-- **Every Koike–Terada function is an irreducible character of `USp(2g)`.** -/
lemma exists_ambientCharacter_eq_symplecticSchur (hw' : Odd w) (hd' : d = g + g) :
    ∃ χ : IrrepClass ℂ (ambientGroup w d), ∀ h, ambientCharacter w d χ h =
      symplecticSchur c (h : Matrix (Fin d) (Fin d) ℂ).charpoly.roots := by
  rcases exists_hasSymplecticMonomial hw' hd' c with ⟨χ, hχ⟩
  exact ⟨χ, hχ.ambientCharacter_eq⟩

variable (χ) in
/-- **Every irreducible character of `USp(2g)` is a Koike–Terada function.** -/
lemma exists_symplecticSchur_eq_ambientCharacter (hw' : Odd w) (hd' : d = g + g) : ∃ c : Fin g → ℕ,
    ∀ h, ambientCharacter w d χ h =
      symplecticSchur c (h : Matrix (Fin d) (Fin d) ℂ).charpoly.roots := by
  rcases exists_hasSymplecticMonomial_of_class hw' hd' χ with ⟨c, hc⟩
  exact ⟨c, hc.ambientCharacter_eq⟩

end Classification

variable (G : SatoTateGroup) {hw : Odd G.weight} {hd : G.degree = G.degree / 2 + G.degree / 2}
  {χ χ' : IrrepClass ℂ (ambientGroup G.weight G.degree)} {c c' : Fin (G.degree / 2) → ℕ}

/-- **The moment matrix over the irreducible characters is the moment matrix of the Koike–Terada
functions.** -/
lemma momentMatrix_eq_symplecticMomentMatrix (hc : HasSymplecticMonomial hw hd χ c)
    (hc' : HasSymplecticMonomial hw hd χ' c') :
    G.momentMatrix χ χ' = G.symplecticMomentMatrix c c' := by
  have h₁ (χ₀ : IrrepClass ℂ (ambientGroup G.weight G.degree)) (c₀ : Fin (G.degree / 2) → ℕ)
      (h₀ : HasSymplecticMonomial hw hd χ₀ c₀) :
      G.irreducibleCharacter χ₀ = G.symplecticCharacter c₀ :=
    funext fun x ↦ h₀.ambientCharacter_eq (G.toAmbient x)
  simp only [momentMatrix, symplecticMomentMatrix, of_apply, h₁ χ c hc, h₁ χ' c' hc']

variable {G} in
/-- **In odd weight, the order of the rows and columns of the moment matrix is the order of the
exponent vectors of the highest weights.** -/
lemma HasSymplecticMonomial.isBeforeInMomentMatrix_iff (hc : HasSymplecticMonomial hw hd χ c)
    (hc' : HasSymplecticMonomial hw hd χ' c') :
    G.IsBeforeInMomentMatrix χ χ' ↔ IsBeforeInDisplayOrder c c' :=
  ⟨fun h ↦ h.1 hw hd c c' hc hc', fun h ↦ ⟨fun _ _ b b' hb hb' ↦ by rwa [hb.eq hc, hb'.eq hc'],
    fun he ↦ absurd hw (Nat.not_odd_iff_even.mpr he)⟩⟩

/-- **In odd weight, the order of the rows and columns of the moment matrix is a linear order.** -/
lemma isLinearOrder_isBeforeInMomentMatrix (hG : Odd G.weight) :
    IsLinearOrder (IrrepClass ℂ (ambientGroup G.weight G.degree)) G.IsBeforeInMomentMatrix := by
  choose f hf using exists_hasSymplecticMonomial_of_class hG (G.degree_eq_of_odd hG)
  have h₁ : G.IsBeforeInMomentMatrix = InvImage IsBeforeInDisplayOrder f :=
    funext₂ fun χ χ' ↦ propext ((hf χ).isBeforeInMomentMatrix_iff (hf χ'))
  rw [h₁]
  exact InvImage.isLinearOrder fun χ χ' h ↦ (hf χ).eq_of_eq (h ▸ hf χ')

end SatoTateGroup
