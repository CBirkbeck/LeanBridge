import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.AdelicGroup
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.LocalHecke
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion

/-!
# Level subgroups of `GL₂(𝔸_F^f)` and the local embeddings

Let `F` be a number field, `Ô` the ring of integral finite adeles, and `𝔑` an ideal of `𝒪_F`, with
`𝔑Ô ⊆ 𝔸_F^f` the corresponding ideal of `Ô`. This file defines the level subgroups `K₀(𝔑)` and
`K₁(𝔑)` of `GL₂(Ô)`, of the matrices `(a, b; c, d)` with `c ∈ 𝔑Ô`, respectively with
`c, d - 1 ∈ 𝔑Ô`, which are open subgroups of `GL₂(𝔸_F^f)` when `𝔑 ≠ 0`. It also defines, for a
finite place `v`, the embedding `GL₂(F_v) → GL₂(𝔸_F^f)` with the identity at the other places; for
`v ∤ 𝔑` the image of `GL₂(𝒪_v)` lies in `K₁(𝔑)`.

## Main definitions

* `AdelicGL2.adelicIdeal`: the subgroup `𝔑Ô` of `𝔸_F^f`.
* `AdelicGL2.integralGL`: the group `GL₂(Ô)`.
* `AdelicGL2.levelZero`, `AdelicGL2.levelOne`: the groups `K₀(𝔑)` and `K₁(𝔑)`.
* `AdelicGL2.atPlace`: the component `GL₂(𝔸_F^f) → GL₂(F_v)` at a finite place `v`.
* `AdelicGL2.localGL`: the embedding `GL₂(F_v) → GL₂(𝔸_F^f)`.
* `AdelicGL2.uniformizer`, `AdelicGL2.residueRep`: a uniformizer of `F_v`, and a system of
  representatives of its residue field, the choices defining the Hecke operators.

## Main results

* `AdelicGL2.isOpen_levelOne`, `AdelicGL2.isOpen_levelZero`: for `𝔑 ≠ 0` these subgroups are open.
* `AdelicGL2.localGL_mem_levelOne`: `GL₂(𝒪_v) ⊆ K₁(𝔑)` for `v ∤ 𝔑`.
* `AdelicGL2.isUniformizer_uniformizer`, `AdelicGL2.isResidueSystem_residueRep`: the choices are
  a uniformizer and a system of representatives.
-/

open IsDedekindDomain HeightOneSpectrum Matrix NumberField WithZero

open FiniteAdeleRing (integralAdeles isOpen_integralAdeles mem_integralAdeles unitEmbedding)

open Ideal renaming Quotient.mk → quotientMk, Quotient.mk_out → quotientMk_out,
  Quotient.eq → quotientMk_eq

open scoped AdeleRing MatrixGroups

namespace AdelicGL2

variable {F : Type*} [Field F] [NumberField F]

/-- The subgroup **`𝔑Ô`** of the finite adeles, for an ideal `𝔑` of `𝒪_F`: the finite adeles `x`
with `x_v ∈ 𝔑 𝒪_v` at every finite place `v`, that is `v(x_v) ≤ exp(-n)` whenever `v ^ n ∣ 𝔑`.
For `𝔑 = 0` it is `0`. -/
def adelicIdeal (𝔑 : Ideal (𝓞 F)) : AddSubgroup 𝔸ᶠ[F] where
  carrier := {x | ∀ (v : HeightOneSpectrum (𝓞 F)) (n : ℕ), v.asIdeal ^ n ∣ 𝔑 →
    Valued.v (x v) ≤ exp (-(n : ℤ))}
  zero_mem' v n _ := by
    simp
  add_mem' {a b} ha hb v n hn := by
    rw [FiniteAdeleRing.add_apply]
    exact Valuation.map_add_le _ (ha v n hn) (hb v n hn)
  neg_mem' {a} ha v n hn := (Valuation.map_neg _ _).trans_le (ha v n hn)

variable {𝔑 : Ideal (𝓞 F)} {r s : 𝔸ᶠ[F]}

lemma mem_adelicIdeal_iff : r ∈ adelicIdeal 𝔑 ↔
    ∀ (v : HeightOneSpectrum (𝓞 F)) (n : ℕ), v.asIdeal ^ n ∣ 𝔑 →
      Valued.v (r v) ≤ exp (-(n : ℤ)) :=
  Iff.rfl

lemma mem_integralAdeles_of_mem_adelicIdeal (hr : r ∈ adelicIdeal 𝔑) :
    r ∈ integralAdeles (𝓞 F) F :=
  mem_integralAdeles.mpr fun v ↦ by
    simpa [mem_adicCompletionIntegers] using hr v 0 (by simp)

lemma mul_mem_adelicIdeal (hr : r ∈ adelicIdeal 𝔑) (hs : s ∈ integralAdeles (𝓞 F) F) :
    r * s ∈ adelicIdeal 𝔑 := fun v n hn ↦ by
  have h₁ : Valued.v (s v) ≤ 1 :=
    (mem_adicCompletionIntegers _ _ v).mp (mem_integralAdeles.mp hs v)
  rw [FiniteAdeleRing.mul_apply, map_mul]
  exact (mul_le_mul' (hr v n hn) h₁).trans_eq (mul_one _)

lemma mul_mem_adelicIdeal' (hr : r ∈ integralAdeles (𝓞 F) F) (hs : s ∈ adelicIdeal 𝔑) :
    r * s ∈ adelicIdeal 𝔑 :=
  mul_comm s r ▸ mul_mem_adelicIdeal hs hr

lemma isOpen_adelicIdeal (h𝔑 : 𝔑 ≠ ⊥) : IsOpen (adelicIdeal 𝔑 : Set 𝔸ᶠ[F]) := by
  rcases Submodule.exists_mem_ne_zero_of_ne_bot h𝔑 with ⟨α, hα, hα₀⟩
  have hα₁ : algebraMap (𝓞 F) F α ≠ 0 := (map_ne_zero_iff _ RingOfIntegers.coe_injective).mpr hα₀
  let u : 𝔸ᶠ[F]ˣ := unitEmbedding (𝓞 F) F (Units.mk0 _ hα₁)
  let U : Set 𝔸ᶠ[F] :=
    (fun z ↦ ((u⁻¹ : 𝔸ᶠ[F]ˣ) : 𝔸ᶠ[F]) * z) ⁻¹' (integralAdeles (𝓞 F) F : Set 𝔸ᶠ[F])
  have hU : IsOpen U :=
    (isOpen_integralAdeles (𝓞 F) F).preimage (continuous_const.mul continuous_id)
  have h₀ : (0 : 𝔸ᶠ[F]) ∈ U := by
    simp [U]
  refine AddSubgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hU.mem_nhds h₀) fun z hz ↦ ?_)
  intro v n hn
  have hz' : Valued.v (((u⁻¹ : 𝔸ᶠ[F]ˣ) : 𝔸ᶠ[F]) v * z v) ≤ 1 :=
    (mem_adicCompletionIntegers _ _ v).mp (mem_integralAdeles.mp hz v)
  have huv : ((u : 𝔸ᶠ[F]) v) * ((u⁻¹ : 𝔸ᶠ[F]ˣ) : 𝔸ᶠ[F]) v = 1 := by
    rw [← FiniteAdeleRing.mul_apply, Units.mul_inv, FiniteAdeleRing.one_apply]
  have hz₂ : z v = (u : 𝔸ᶠ[F]) v * (((u⁻¹ : 𝔸ᶠ[F]ˣ) : 𝔸ᶠ[F]) v * z v) := by
    rw [← mul_assoc, huv, one_mul]
  have hαv : Valued.v ((u : 𝔸ᶠ[F]) v) ≤ exp (-(n : ℤ)) := by
    have hmem : α ∈ v.asIdeal ^ n := Ideal.le_of_dvd hn hα
    exact v.mem_asIdeal_pow_iff_valued_algebraMap_le.mp hmem
  rw [hz₂, map_mul]
  exact (mul_le_mul' hαv hz').trans_eq (mul_one _)

variable (F) in
/-- The group **`GL₂(Ô)`** of invertible matrices over the integral finite adeles. -/
noncomputable abbrev integralGL : Subgroup (GL (Fin 2) 𝔸ᶠ[F]) :=
  (integralAdeles (𝓞 F) F).toSubring.gl (Fin 2)

private lemma inv_apply_one_zero {R : Type*} [CommRing R] (k : GL (Fin 2) R) :
    ((k⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 0 =
      -(((k⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det *
        (k : Matrix (Fin 2) (Fin 2) R) 1 0) := by
  rw [GeneralLinearGroup.coe_inv, det_nonsing_inv, inv_def, adjugate_fin_two]
  simp

private lemma inv_apply_one_one {R : Type*} [CommRing R] (k : GL (Fin 2) R) :
    ((k⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) 1 1 =
      ((k⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det *
        (k : Matrix (Fin 2) (Fin 2) R) 0 0 := by
  rw [GeneralLinearGroup.coe_inv, det_nonsing_inv, inv_def, adjugate_fin_two]
  simp

variable (𝔑) in
/-- The level subgroup **`K₀(𝔑)`** of `GL₂(𝔸_F^f)`: the matrices `(a, b; c, d)` of `GL₂(Ô)` with
`c ∈ 𝔑Ô`. -/
noncomputable def levelZero : Subgroup (GL (Fin 2) 𝔸ᶠ[F]) where
  carrier := {k | k ∈ integralGL F ∧ (k : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) 1 0 ∈ adelicIdeal 𝔑}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, ?_⟩
    rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
    exact add_mem (mul_mem_adelicIdeal ha' (hb 0 0).1) (mul_mem_adelicIdeal' (ha 1 1).1 hb')
  one_mem' := ⟨one_mem _, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, ?_⟩
    rw [inv_apply_one_zero]
    exact neg_mem (mul_mem_adelicIdeal' (Subring.det_mem_of_mem_gl (inv_mem ha)) ha')

variable (𝔑) in
/-- The level subgroup **`K₁(𝔑)`** of `GL₂(𝔸_F^f)`: the matrices `(a, b; c, d)` of `GL₂(Ô)` with
`c ∈ 𝔑Ô` and `d - 1 ∈ 𝔑Ô`. -/
noncomputable def levelOne : Subgroup (GL (Fin 2) 𝔸ᶠ[F]) where
  carrier := {k | k ∈ integralGL F ∧ (k : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) 1 0 ∈ adelicIdeal 𝔑 ∧
    (k : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) 1 1 - 1 ∈ adelicIdeal 𝔑}
  mul_mem' := by
    rintro a b ⟨ha, ha₁, ha₂⟩ ⟨hb, hb₁, hb₂⟩
    refine ⟨mul_mem ha hb, ?_, ?_⟩
    · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
      exact add_mem (mul_mem_adelicIdeal ha₁ (hb 0 0).1) (mul_mem_adelicIdeal' (ha 1 1).1 hb₁)
    · have he : ((a * b : GL (Fin 2) 𝔸ᶠ[F]) : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) 1 1 - 1 =
          (a : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) 1 0 * (b : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) 0 1 +
            ((a : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) 1 1 - 1) * (b : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) 1 1 +
              ((b : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) 1 1 - 1) := by
        rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
        ring1
      rw [he]
      exact add_mem (add_mem (mul_mem_adelicIdeal ha₁ (hb 0 1).1)
        (mul_mem_adelicIdeal ha₂ (hb 1 1).1)) hb₂
  one_mem' := ⟨one_mem _, by simp, by simp⟩
  inv_mem' := by
    rintro k ⟨hk, hk₁, hk₂⟩
    have hdet : ((k⁻¹ : GL (Fin 2) 𝔸ᶠ[F]) : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]).det ∈
        integralAdeles (𝓞 F) F :=
      Subring.det_mem_of_mem_gl (inv_mem hk)
    refine ⟨inv_mem hk, ?_, ?_⟩
    · rw [inv_apply_one_zero]
      exact neg_mem (mul_mem_adelicIdeal' hdet hk₁)
    · have hd : ((k⁻¹ : GL (Fin 2) 𝔸ᶠ[F]) : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]).det *
          ((k : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) 0 0 * (k : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) 1 1 -
            (k : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) 0 1 * (k : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) 1 0) =
          1 := by
        rw [← det_fin_two, ← det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, det_one]
      have he : ((k⁻¹ : GL (Fin 2) 𝔸ᶠ[F]) : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) 1 1 - 1 =
          -(((k : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) 1 1 - 1) *
              ((k : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) 0 0 *
                ((k⁻¹ : GL (Fin 2) 𝔸ᶠ[F]) : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]).det)) +
            (k : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) 1 0 * ((k : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) 0 1 *
              ((k⁻¹ : GL (Fin 2) 𝔸ᶠ[F]) : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]).det) := by
        rw [inv_apply_one_one]
        linear_combination hd
      rw [he]
      exact add_mem (neg_mem (mul_mem_adelicIdeal hk₂ (mul_mem (hk 0 0).1 hdet)))
        (mul_mem_adelicIdeal hk₁ (mul_mem (hk 0 1).1 hdet))

lemma levelOne_le_levelZero : levelOne 𝔑 ≤ levelZero 𝔑 :=
  fun _ hk ↦ ⟨hk.1, hk.2.1⟩

private lemma continuous_apply_gl (i j : Fin 2) :
    Continuous fun k : GL (Fin 2) 𝔸ᶠ[F] ↦ (k : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) i j :=
  (continuous_id.matrix_elem i j).comp Units.continuous_val

private lemma continuous_inv_apply_gl (i j : Fin 2) : Continuous fun k : GL (Fin 2) 𝔸ᶠ[F] ↦
    ((k⁻¹ : GL (Fin 2) 𝔸ᶠ[F]) : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) i j :=
  (continuous_apply_gl i j).comp continuous_inv

variable (F) in
lemma isOpen_integralGL : IsOpen (integralGL F : Set (GL (Fin 2) 𝔸ᶠ[F])) :=
  Subring.isOpen_gl (isOpen_integralAdeles (𝓞 F) F)

/-- **`K₁(𝔑)` is open** in `GL₂(𝔸_F^f)` for `𝔑 ≠ 0`. -/
lemma isOpen_levelOne (h𝔑 : 𝔑 ≠ ⊥) : IsOpen (levelOne 𝔑 : Set (GL (Fin 2) 𝔸ᶠ[F])) :=
  (isOpen_integralGL F).inter
    (((isOpen_adelicIdeal h𝔑).preimage (continuous_apply_gl 1 0)).inter
      ((isOpen_adelicIdeal h𝔑).preimage ((continuous_apply_gl 1 1).sub continuous_const)))

/-- **`K₀(𝔑)` is open** in `GL₂(𝔸_F^f)` for `𝔑 ≠ 0`. -/
lemma isOpen_levelZero (h𝔑 : 𝔑 ≠ ⊥) : IsOpen (levelZero 𝔑 : Set (GL (Fin 2) 𝔸ᶠ[F])) :=
  (isOpen_integralGL F).inter ((isOpen_adelicIdeal h𝔑).preimage (continuous_apply_gl 1 0))

variable (v w : HeightOneSpectrum (𝓞 F))

/-- The evaluation `𝔸_F^f → F_v` at a finite place, as a ring homomorphism. -/
noncomputable def evalRingHom : 𝔸ᶠ[F] →+* v.adicCompletion F :=
  RingHomClass.toRingHom (FiniteAdeleRing.proj F v)

/-- The component `GL₂(𝔸_F^f) → GL₂(F_v)` at a finite place `v`. -/
noncomputable def atPlace : GL (Fin 2) 𝔸ᶠ[F] →* GL (Fin 2) (v.adicCompletion F) :=
  GeneralLinearGroup.map (evalRingHom v)

lemma atPlace_apply (y : GL (Fin 2) 𝔸ᶠ[F]) (i j : Fin 2) :
    (atPlace v y : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j =
      (y : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) i j v :=
  rfl

variable {v} in
lemma ext_atPlace {y y' : GL (Fin 2) 𝔸ᶠ[F]} (h : ∀ v, atPlace v y = atPlace v y') : y = y' :=
  GeneralLinearGroup.ext fun i j ↦ FiniteAdeleRing.ext F fun v ↦ by
    rw [← atPlace_apply, ← atPlace_apply, h v]

/-- The matrix over the finite adeles equal to `m` at the place `v` and to the identity at the other
places. -/
noncomputable def localMat (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) :
    Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F] :=
  of fun i j ↦ (1 : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) i j +
    FiniteAdeleRing.single F v (m i j - (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j)

private lemma one_apply_eval (i j : Fin 2) : (1 : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) i j w =
    (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) i j := by
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h]

lemma localMat_apply_self (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) (i j : Fin 2) :
    localMat v m i j v = m i j := by
  rw [localMat, of_apply, FiniteAdeleRing.add_apply, FiniteAdeleRing.single_apply_self,
    one_apply_eval, add_sub_cancel]

variable {v w} in
lemma localMat_apply_of_ne (h : w ≠ v) (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
    (i j : Fin 2) : localMat v m i j w = (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) i j := by
  rw [localMat, of_apply, FiniteAdeleRing.add_apply, FiniteAdeleRing.single_apply_of_ne h,
    one_apply_eval, add_zero]

/-- `localMat` as a homomorphism of monoids. -/
noncomputable def localMatHom :
    Matrix (Fin 2) (Fin 2) (v.adicCompletion F) →* Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F] where
  toFun := localMat v
  map_one' := Matrix.ext fun i j ↦ FiniteAdeleRing.ext F fun w ↦ by
    rcases eq_or_ne w v with rfl | h
    · rw [localMat_apply_self, one_apply_eval]
    · rw [localMat_apply_of_ne h, one_apply_eval]
  map_mul' m m' := Matrix.ext fun i j ↦ FiniteAdeleRing.ext F fun w ↦ by
    rw [Matrix.mul_apply, Fin.sum_univ_two, FiniteAdeleRing.add_apply, FiniteAdeleRing.mul_apply,
      FiniteAdeleRing.mul_apply]
    rcases eq_or_ne w v with rfl | h
    · simp only [localMat_apply_self, Matrix.mul_apply, Fin.sum_univ_two]
    · simp only [localMat_apply_of_ne h]
      rw [← Fin.sum_univ_two (fun l ↦ (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) i l *
        (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) l j), ← Matrix.mul_apply, mul_one]

/-- The embedding **`GL₂(F_v) → GL₂(𝔸_F^f)`** at a finite place `v`: a matrix `m` goes to the matrix
equal to `m` at `v` and to the identity at the other places. -/
noncomputable def localGL : GL (Fin 2) (v.adicCompletion F) →* GL (Fin 2) 𝔸ᶠ[F] :=
  Units.map (localMatHom v)

lemma localGL_apply (m : GL (Fin 2) (v.adicCompletion F)) (i j : Fin 2) :
    (localGL v m : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) i j =
      localMat v (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j :=
  rfl

@[simp]
lemma atPlace_localGL (m : GL (Fin 2) (v.adicCompletion F)) : atPlace v (localGL v m) = m :=
  GeneralLinearGroup.ext fun i j ↦ localMat_apply_self v _ i j

variable {v w} in
lemma atPlace_localGL_of_ne (h : w ≠ v) (m : GL (Fin 2) (v.adicCompletion F)) :
    atPlace w (localGL v m) = 1 :=
  GeneralLinearGroup.ext fun i j ↦ localMat_apply_of_ne h _ i j

variable {v} in
lemma localGL_commute {y : GL (Fin 2) 𝔸ᶠ[F]} (hy : atPlace v y = 1)
    (m : GL (Fin 2) (v.adicCompletion F)) : localGL v m * y = y * localGL v m := by
  refine ext_atPlace fun w ↦ ?_
  rcases eq_or_ne w v with rfl | h
  · simp [hy]
  · simp [atPlace_localGL_of_ne h]

variable {v w} in
lemma localGL_commute_of_ne (h : w ≠ v) (m : GL (Fin 2) (v.adicCompletion F))
    (m' : GL (Fin 2) (w.adicCompletion F)) :
    localGL v m * localGL w m' = localGL w m' * localGL v m :=
  localGL_commute (atPlace_localGL_of_ne h.symm m') m

/-- The part of `y ∈ GL₂(𝔸_F^f)` away from `v`: the same matrix with the identity at `v`. -/
noncomputable def awayFrom (y : GL (Fin 2) 𝔸ᶠ[F]) : GL (Fin 2) 𝔸ᶠ[F] :=
  (localGL v (atPlace v y))⁻¹ * y

@[simp]
lemma atPlace_awayFrom (y : GL (Fin 2) 𝔸ᶠ[F]) : atPlace v (awayFrom v y) = 1 := by
  simp [awayFrom]

lemma localGL_mul_awayFrom (y : GL (Fin 2) 𝔸ᶠ[F]) : localGL v (atPlace v y) * awayFrom v y = y := by
  simp [awayFrom]

variable {v}

lemma atPlace_mem_gl2_of_mem_integralGL {y : GL (Fin 2) 𝔸ᶠ[F]} (hy : y ∈ integralGL F) :
    atPlace v y ∈ (v.adicCompletionIntegers F).gl2 := by
  refine fun i j ↦ ⟨?_, ?_⟩
  · exact mem_integralAdeles.mp (hy i j).1 v
  · rw [← map_inv]
    exact mem_integralAdeles.mp (hy i j).2 v

private lemma localMat_mem_integralAdeles {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)}
    (hm : ∀ i j, m i j ∈ v.adicCompletionIntegers F) (i j : Fin 2) :
    localMat v m i j ∈ integralAdeles (𝓞 F) F := by
  refine mem_integralAdeles.mpr fun w ↦ ?_
  rcases eq_or_ne w v with rfl | h
  · rw [localMat_apply_self]
    exact hm i j
  · rw [localMat_apply_of_ne h]
    rcases eq_or_ne i j with rfl | hij
    · simp
    · simp [hij]

lemma localGL_mem_integralGL {m : GL (Fin 2) (v.adicCompletion F)}
    (hm : m ∈ (v.adicCompletionIntegers F).gl2) : localGL v m ∈ integralGL F := by
  refine fun i j ↦ ⟨localMat_mem_integralAdeles (fun a b ↦ (hm a b).1) i j, ?_⟩
  rw [← map_inv]
  exact localMat_mem_integralAdeles (fun a b ↦ (hm a b).2) i j

/-- **The image of `GL₂(𝒪_v)` lies in `K₁(𝔑)`** for `v ∤ 𝔑`. -/
lemma localGL_mem_levelOne (hv : ¬𝔑 ≤ v.asIdeal) {m : GL (Fin 2) (v.adicCompletion F)}
    (hm : m ∈ (v.adicCompletionIntegers F).gl2) : localGL v m ∈ levelOne 𝔑 := by
  have hn (n : ℕ) (h : v.asIdeal ^ n ∣ 𝔑) : n = 0 := by
    by_contra hn₀
    exact hv (Ideal.le_of_dvd ((dvd_pow_self _ hn₀).trans h))
  refine ⟨localGL_mem_integralGL hm, fun w n hd ↦ ?_, fun w n hd ↦ ?_⟩
  · rcases eq_or_ne w v with rfl | h
    · rw [localGL_apply, localMat_apply_self, hn n hd]
      simpa [mem_adicCompletionIntegers] using (hm 1 0).1
    · rw [localGL_apply, localMat_apply_of_ne h]
      simp
  · rcases eq_or_ne w v with rfl | h
    · rw [FiniteAdeleRing.sub_apply, localGL_apply, localMat_apply_self, hn n hd,
        FiniteAdeleRing.one_apply]
      have h₁ : (m : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) 1 1 - 1 ∈
          w.adicCompletionIntegers F :=
        sub_mem (hm 1 1).1 (one_mem _)
      simpa [mem_adicCompletionIntegers] using h₁
    · rw [FiniteAdeleRing.sub_apply, localGL_apply, localMat_apply_of_ne h,
        FiniteAdeleRing.one_apply]
      simp

lemma awayFrom_mem_levelOne (hv : ¬𝔑 ≤ v.asIdeal) {y : GL (Fin 2) 𝔸ᶠ[F]}
    (hy : y ∈ levelOne 𝔑) : awayFrom v y ∈ levelOne 𝔑 :=
  mul_mem (inv_mem (localGL_mem_levelOne hv (atPlace_mem_gl2_of_mem_integralGL hy.1))) hy

variable (v)

private lemma exists_valued_eq :
    ∃ π : F, Valued.v (algebraMap F (v.adicCompletion F) π) = exp (-1) := by
  rcases v.valuation_exists_uniformizer F with ⟨π, hπ⟩
  refine ⟨π, ?_⟩
  rw [algebraMap_adicCompletion, Function.comp_apply, valuedAdicCompletion_eq_valuation']
  exact hπ

/-- A **uniformizer** of `F_v`, the one in `Fˣ` chosen by
`HeightOneSpectrum.valuation_exists_uniformizer`, with valuation `exp(-1)`. -/
noncomputable def uniformizer : (v.adicCompletion F)ˣ :=
  Units.mk0 (algebraMap F (v.adicCompletion F) (exists_valued_eq v).choose) fun h ↦ by
    have hv : Valued.v (algebraMap F (v.adicCompletion F) (exists_valued_eq v).choose) =
        exp (-1) :=
      (exists_valued_eq v).choose_spec
    rw [h, map_zero] at hv
    exact exp_ne_zero hv.symm

lemma valued_uniformizer : Valued.v (uniformizer v : v.adicCompletion F) = exp (-1) :=
  (exists_valued_eq v).choose_spec

variable {v}

lemma isUniformizer_of_valued_eq {ϖ : v.adicCompletion F} (hϖ : Valued.v ϖ = exp (-1)) :
    (v.adicCompletionIntegers F).IsUniformizer ϖ := by
  refine ⟨?_, ?_, fun x hx hx' ↦ ?_⟩
  · rw [mem_adicCompletionIntegers, hϖ]
    exact (exp_lt_one_iff.mpr (by norm_num)).le
  · rw [mem_adicCompletionIntegers, map_inv₀, hϖ, inv_exp]
    exact not_le.mpr (one_lt_exp_iff.mpr (by norm_num))
  · rw [mem_adicCompletionIntegers] at hx hx' ⊢
    have hx₀ : x ≠ 0 := by
      rintro rfl
      simp at hx'
    have hx₁ : Valued.v x ≠ 0 := by
      rwa [Ne, Valuation.zero_iff]
    rw [map_inv₀, not_le, one_lt_inv₀ (zero_lt_iff.mpr hx₁)] at hx'
    rw [map_mul, map_inv₀, hϖ, inv_exp, neg_neg, ← exp_log hx₁, ← exp_add]
    have hl : log (Valued.v x) < 0 := by
      rw [← exp_lt_one_iff, exp_log hx₁]
      exact hx'
    rw [← exp_zero, exp_le_exp]
    omega

variable (v)

/-- The chosen element `(uniformizer v)` is a uniformizer of `𝒪_v`. -/
lemma isUniformizer_uniformizer :
    (v.adicCompletionIntegers F).IsUniformizer (uniformizer v : v.adicCompletion F) :=
  isUniformizer_of_valued_eq (valued_uniformizer v)

/-- The **representative in `F_v`** of an element of the residue field `𝒪_F / v`. -/
noncomputable def residueRep (b : 𝓞 F ⧸ v.asIdeal) : v.adicCompletion F :=
  algebraMap (𝓞 F) (v.adicCompletion F) (Quotient.out b)

variable {v}

private lemma inv_mul_mem_iff_of_valued_eq {ϖ x : v.adicCompletion F}
    (hϖ : Valued.v ϖ = exp (-1)) :
    ϖ⁻¹ * x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ exp (-1) := by
  have h₁ : (exp 1 : ℤᵐ⁰) * exp (-1) = 1 := by
    rw [← exp_add]
    simp
  rw [mem_adicCompletionIntegers, map_mul, map_inv₀, hϖ, inv_exp, neg_neg]
  constructor
  · intro h
    have h₂ : exp (-1) * (exp 1 * Valued.v x) ≤ exp (-1) * 1 :=
      mul_le_mul' (le_refl (exp (-1) : ℤᵐ⁰)) h
    rwa [← mul_assoc, mul_comm (exp (-1)) (exp 1), h₁, one_mul, mul_one] at h₂
  · intro h
    exact (mul_le_mul' (le_refl (exp 1 : ℤᵐ⁰)) h).trans_eq h₁

variable (v) in
/-- `residueRep v` is a system of representatives of the residue field of `𝒪_v`, for any
uniformizer. -/
lemma isResidueSystem_residueRep {ϖ : v.adicCompletion F} (hϖ : Valued.v ϖ = exp (-1)) :
    (v.adicCompletionIntegers F).IsResidueSystem ϖ (residueRep v) := by
  refine ⟨fun b ↦ v.coe_mem_adicCompletionIntegers _, fun x hx ↦ ?_⟩
  simp only [inv_mul_mem_iff_of_valued_eq hϖ, residueRep]
  have hmem (a a' : 𝓞 F) : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a -
      algebraMap (𝓞 F) (v.adicCompletion F) a') ≤ exp (-1) ↔ a - a' ∈ v.asIdeal := by
    have h : a - a' ∈ v.asIdeal ^ 1 ↔
        Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) (a - a')) ≤ exp (-((1 : ℕ) : ℤ)) :=
      v.mem_asIdeal_pow_iff_valued_algebraMap_le
    rw [pow_one, map_sub] at h
    exact h.symm
  rcases v.exists_valued_sub_le ⟨x, hx⟩ 1 with ⟨a, ha⟩
  simp only [Nat.cast_one] at ha
  refine ⟨quotientMk v.asIdeal a, ?_, fun b hb ↦ ?_⟩
  · have ho : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F)
        (Quotient.out (quotientMk v.asIdeal a)) - algebraMap (𝓞 F) (v.adicCompletion F) a) ≤
          exp (-1) :=
      (hmem _ _).mpr (quotientMk_eq.mp (quotientMk_out _))
    have he : x - algebraMap (𝓞 F) (v.adicCompletion F) (Quotient.out (quotientMk v.asIdeal a)) =
        (x - algebraMap (𝓞 F) (v.adicCompletion F) a) -
          (algebraMap (𝓞 F) (v.adicCompletion F) (Quotient.out (quotientMk v.asIdeal a)) -
            algebraMap (𝓞 F) (v.adicCompletion F) a) := by
      ring1
    beta_reduce
    rw [he]
    exact Valuation.map_sub_le _ ha ho
  · have he : algebraMap (𝓞 F) (v.adicCompletion F) (Quotient.out b) -
        algebraMap (𝓞 F) (v.adicCompletion F) a =
        (x - algebraMap (𝓞 F) (v.adicCompletion F) a) -
          (x - algebraMap (𝓞 F) (v.adicCompletion F) (Quotient.out b)) := by
      ring1
    have h₁ : Quotient.out b - a ∈ v.asIdeal := (hmem (Quotient.out b) a).mp <| by
      rw [he]
      exact Valuation.map_sub_le _ ha hb
    rw [← quotientMk_out b]
    exact quotientMk_eq.mpr h₁

end AdelicGL2
