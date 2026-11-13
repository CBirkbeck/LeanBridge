import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.ElementaryCommutator
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.Level
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.RingTheory.UniqueFactorizationDomain.ClassGroup
import Mathlib.Topology.Algebra.Group.Matrix
import Mathlib.Topology.Algebra.OpenSubgroup
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.NumberTheory.NumberField.NarrowClassGroup.Basic
import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.ClassGroup

/-!
# Strong approximation for `SL₂` and the decomposition of `GL₂(𝔸_F^f)`

Let `F` be a number field and `𝔸_F^f` its ring of finite adeles. This file proves strong
approximation for `SL₂`: the group `SL₂(F)` is dense in `SL₂(𝔸_F^f)`. A matrix of `SL₂(𝔸_F^f)` with
first column `(a, c)` has, after left multiplication by `(1, 0; t, 1)` for a suitable integral adele
`t`, the finite idele `c + t a` as its lower left entry, so it is a product of four elementary
matrices, and `F` is dense in `𝔸_F^f`.

It follows that if a finite idele `x` has the narrow ideal class of `det y`, then
`y = γ diag(x, 1) u` with `γ ∈ GL₂(F)` of totally positive determinant and `u ∈ K₁(𝔑)`, for any
ideal `𝔑 ≠ 0`. The narrow class group of `ℚ` is trivial, so `GL₂(𝔸_ℚ^f) = GL₂(ℚ)⁺ K₁(N)`, and
`GL₂(ℚ)⁺ ∩ K₁(N) = Γ₁(N)`. Finally the archimedean factor `GL₂(E)` of `GL₂(𝔸_ℚ)` is identified with
`GL₂(ℝ)`.

## Main definitions

* `AdelicGL2.elemWord`: the products of four elementary matrices, the lower ones `(1, 0; r, 1)`
  being `Matrix.GeneralLinearGroup.lowerUnipotent`.
* `AdelicGL2.columnShift`: the adele `t` above.
* `AdelicGL2.diagHom`, `AdelicGL2.diagFin`: the matrices `(x, 0; 0, 1)`, for a unit `x`.
* `AdelicGL2.ratMixedEquiv`, `AdelicGL2.ratMixedEquivL`: the isomorphism from the mixed space of `ℚ`
  to `ℝ`, as a ring and as a continuous `ℝ`-linear isomorphism.
* `AdelicGL2.ratInfEquiv`: the isomorphism `GL₂(E) ≃ GL₂(ℝ)` for `F = ℚ`.

## Main results

* `AdelicGL2.exists_det_eq_one_inv_mul_mem`: strong approximation for `SL₂` over a number field.
* `AdelicGL2.exists_eq_map_mul_diagFin_mul`: the decomposition of `GL₂(𝔸_F^f)`.
* `AdelicGL2.rat_exists_eq_mul_levelOne`: the decomposition `GL₂(𝔸_ℚ^f) = GL₂(ℚ)⁺ K₁(N)`.
* `AdelicGL2.algebraMap_mem_adelicIdeal_iff`: `𝔑Ô ∩ F = 𝔑` for `𝔑 ≠ 0`.
* `AdelicGL2.mem_gamma1_of_mem_levelOne`, `AdelicGL2.map_mem_levelOne_of_mem_gamma1`:
  `GL₂(ℚ)⁺ ∩ K₁(N) = Γ₁(N)`.
* `AdelicGL2.ratMixedEquiv_mixedEmbedding`: `ratMixedEquiv` sends a rational to itself.
-/

open IsDedekindDomain HeightOneSpectrum Matrix NumberField InfinitePlace

open FiniteAdeleRing (algebraMap_mem_integralAdeles_iff denseRange_algebraMap integralAdeles
  integralUnits isUnit_iff ker_toFractionalIdeal
  mem_integralUnits_iff_forall_mem_adicCompletionIntegers toFractionalIdeal
  toFractionalIdeal_unitEmbedding unitEmbedding)

open GeneralLinearGroup (continuous_upperRightHom det_lowerUnipotent det_upperRightHom
  lowerUnipotent upperRightHom)

open TauCeti (diagGL)

open mixedEmbedding (mixedSpace)

open scoped nonZeroDivisors AdeleRing MatrixGroups

namespace AdelicGL2

variable {R : Type*} [CommRing R] (r : R) (u : Rˣ) (p : R × R × R × R) {m : GL (Fin 2) R}
  {S : Type*} [CommRing S] (f : R →+* S) {F : Type*} [Field F] [NumberField F]
  {s : GL (Fin 2) 𝔸ᶠ[F]} {x : 𝔸ᶠ[F]ˣ} {𝔑 : Ideal (𝓞 F)} (N : ℕ) [NeZero N] {q : ℚ} {z : ℤ}
  {γ : GL (Fin 2) ℚ} {g : SL(2, ℤ)} (i j : Fin 2)

/-- The product `(1, 0; x₁, 1)(1, x₂; 0, 1)(1, 0; x₃, 1)(1, x₄; 0, 1)` of elementary matrices, for
`p = (x₁, x₂, x₃, x₄)`. -/
def elemWord : GL (Fin 2) R :=
  lowerUnipotent p.1 * upperRightHom p.2.1 * lowerUnipotent p.2.2.1 * upperRightHom p.2.2.2

/-- The matrix `(x, 0; 0, 1)` of a unit `x`, as a homomorphism `Rˣ → GL₂(R)`: Tau Ceti's
diagonal matrix `TauCeti.diagGL` of the units `(x, 1)`. -/
def diagHom : Rˣ →* GL (Fin 2) R :=
  diagGL.comp (MonoidHom.mulSingle (fun _ : Fin 2 ↦ Rˣ) 0)

lemma det_elemWord : (elemWord p).det = 1 := by
  simp only [elemWord, map_mul, det_lowerUnipotent, det_upperRightHom, mul_one]

lemma det_diagHom : (diagHom u).det = u := by
  ext
  simp [diagHom]

lemma apply_mul_apply_sub_eq_one (hm : m.det = 1) : m 0 0 * m 1 1 - m 0 1 * m 1 0 = 1 :=
  (det_fin_two m.val).symm.trans (congrArg Units.val hm)

lemma eq_elemWord (hm : m.det = 1) {t : R} (hu : u = m 1 0 + t * m 0 0) :
    m = elemWord (-t, (m 0 0 - 1) * u⁻¹, u, (m 1 1 + t * m 0 1 - 1) * u⁻¹) := by
  have hd : m 0 0 * m 1 1 - m 0 1 * m 1 0 = 1 := apply_mul_apply_sub_eq_one hm
  have huu : (u : R) * (u⁻¹ : Rˣ) = 1 := u.mul_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [elemWord, lowerUnipotent] <;> grind

lemma map_lowerUnipotent : GeneralLinearGroup.map f (lowerUnipotent r) = lowerUnipotent (f r) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [lowerUnipotent]

lemma map_upperRightHom : GeneralLinearGroup.map f (upperRightHom r) = upperRightHom (f r) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma map_elemWord : GeneralLinearGroup.map f (elemWord p) =
    elemWord (Prod.map f (Prod.map f (Prod.map f f)) p) := by
  simp only [elemWord, map_mul, map_lowerUnipotent, map_upperRightHom, Prod.map_fst, Prod.map_snd]

lemma map_diagHom : GeneralLinearGroup.map f (diagHom u) = diagHom (Units.map f u) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagHom]

variable [TopologicalSpace R] [IsTopologicalRing R]

@[fun_prop]
lemma continuous_lowerUnipotent : Continuous (lowerUnipotent : R → GL (Fin 2) R) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩ <;> refine continuous_matrix fun i j ↦ ?_ <;>
    fin_cases i <;> fin_cases j <;> simp [lowerUnipotent] <;> fun_prop

lemma continuous_elemWord : Continuous (elemWord : R × R × R × R → GL (Fin 2) R) := by
  unfold elemWord
  fun_prop

lemma valuation_add_ite_mul {K Γ : Type*} [Ring K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) (a c : K) : v (c + (if v c < v a then 1 else 0) * a) = max (v a) (v c) := by
  split_ifs with h
  · rw [one_mul, v.map_add_eq_of_lt_right h, max_eq_left h.le]
  · rw [zero_mul, add_zero, max_eq_right (not_lt.mp h)]

variable (s) in
/-- The integral adele `t` with, for `s = (a, b; c, d)`, the component `t_v = 1` at the places with
`v(c_v) < v(a_v)` and `t_v = 0` at the others: then `c + t a` has the valuation
`max(v(a_v), v(c_v))` at `v`, so it is a finite idele when `det s = 1`. -/
noncomputable def columnShift : 𝔸ᶠ[F] :=
  ⟨fun v ↦ if Valued.v (s 1 0 v) < Valued.v (s 0 0 v) then 1 else 0, .of_forall fun v ↦ by
    beta_reduce
    split_ifs <;> simp⟩

lemma isUnit_add_columnShift_mul (hs : s.det = 1) : IsUnit (s 1 0 + columnShift s * s 0 0) := by
  have hd (v : HeightOneSpectrum (𝓞 F)) : s 0 0 v * s 1 1 v - s 0 1 v * s 1 0 v = 1 := by
    simpa using DFunLike.congr_fun (apply_mul_apply_sub_eq_one hs) v
  have hval (v : HeightOneSpectrum (𝓞 F)) : Valued.v ((s 1 0 + columnShift s * s 0 0) v) =
      max (Valued.v (s 0 0 v)) (Valued.v (s 1 0 v)) :=
    valuation_add_ite_mul Valued.v (s 0 0 v) (s 1 0 v)
  refine isUnit_iff.mpr ⟨fun v h ↦ ?_, ?_⟩
  · have h₀ : max (Valued.v (s 0 0 v)) (Valued.v (s 1 0 v)) = 0 := by
      rw [← hval, h, map_zero]
    have ha : s 0 0 v = 0 :=
      Valued.v.zero_iff.mp <| le_zero_iff.mp <| (le_max_left _ _).trans_eq h₀
    have hc : s 1 0 v = 0 :=
      Valued.v.zero_iff.mp <| le_zero_iff.mp <| (le_max_right _ _).trans_eq h₀
    simpa [ha, hc] using hd v
  · filter_upwards [(s 0 0).cofinite_mem_adicCompletionIntegers,
      (s 0 1).cofinite_mem_adicCompletionIntegers, (s 1 0).cofinite_mem_adicCompletionIntegers,
      (s 1 1).cofinite_mem_adicCompletionIntegers] with v h₁ h₂ h₃ h₄
    rw [mem_adicCompletionIntegers] at h₁ h₂ h₃ h₄
    have h : Valued.v (s 0 0 v * s 1 1 v - s 0 1 v * s 1 0 v) ≤
        max (Valued.v (s 0 0 v * s 1 1 v)) (Valued.v (s 0 1 v * s 1 0 v)) :=
      Valued.v.map_sub _ _
    rw [hd v, map_one, map_mul, map_mul] at h
    rw [hval v]
    exact (max_le h₁ h₃).antisymm <|
      h.trans <| max_le_max (mul_le_of_le_one_right' h₄) (mul_le_of_le_one_left' h₂)

/-- **Strong approximation for `SL₂`** over a number field `F`: the group `SL₂(F)` is dense in
`SL₂(𝔸_F^f)`, that is, for `s ∈ SL₂(𝔸_F^f)` and an open subgroup `U` of `GL₂(𝔸_F^f)` there is
`γ ∈ SL₂(F)` with `γ⁻¹ s ∈ U`. -/
lemma exists_det_eq_one_inv_mul_mem (hs : s.det = 1) (U : OpenSubgroup (GL (Fin 2) 𝔸ᶠ[F])) :
    ∃ γ : GL (Fin 2) F, γ.det = 1 ∧ (GeneralLinearGroup.map (algebraMap F 𝔸ᶠ[F]) γ)⁻¹ * s ∈ U := by
  rcases isUnit_add_columnShift_mul hs with ⟨u, hu⟩
  have hopen : IsOpen {p : 𝔸ᶠ[F] × 𝔸ᶠ[F] × 𝔸ᶠ[F] × 𝔸ᶠ[F] | (elemWord p)⁻¹ * s ∈ U} :=
    U.isOpen.preimage (continuous_elemWord.inv.mul continuous_const)
  have hdense : DenseRange (algebraMap F 𝔸ᶠ[F]) := denseRange_algebraMap (𝓞 F) F
  rcases (hdense.prodMap (hdense.prodMap (hdense.prodMap hdense))).exists_mem_open hopen
    ⟨(-columnShift s, (s 0 0 - 1) * u⁻¹, u, (s 1 1 + columnShift s * s 0 1 - 1) * u⁻¹), by
      simp [← eq_elemWord u hs hu]⟩ with ⟨q, hq⟩
  refine ⟨elemWord q, det_elemWord q, ?_⟩
  rw [map_elemWord]
  exact hq

/-- The matrix `(x, 0; 0, 1)` of `GL₂(𝔸_F^f)`, for a finite idele `x`. -/
noncomputable abbrev diagFin : 𝔸ᶠ[F]ˣ →* GL (Fin 2) 𝔸ᶠ[F] :=
  diagHom

lemma diagFin_mem_levelOne (hx : x ∈ integralUnits (𝓞 F) F) : diagFin x ∈ levelOne 𝔑 := by
  rw [mem_integralUnits_iff_forall_mem_adicCompletionIntegers, forall_and] at hx
  refine ⟨fun i j ↦ ⟨?_, ?_⟩, by simp [diagHom], by simp [diagHom]⟩
  · fin_cases i <;> fin_cases j <;> simp [diagHom, hx.1]
  · rw [← map_inv]
    fin_cases i <;> fin_cases j <;> simp [diagHom, hx.2]

/-- **The decomposition of `GL₂(𝔸_F^f)`** over a number field `F`, for an ideal `𝔑 ≠ 0`: if a finite
idele `x` has the narrow ideal class of `det y`, then `y = γ diag(x, 1) u` with `γ ∈ GL₂(F)` of
totally positive determinant and `u ∈ K₁(𝔑)`. -/
lemma exists_eq_map_mul_diagFin_mul (h𝔑 : 𝔑 ≠ ⊥) (y : GL (Fin 2) 𝔸ᶠ[F])
    (hx : NarrowClassGroup.mk (toFractionalIdeal x) =
      NarrowClassGroup.mk (toFractionalIdeal y.det)) : ∃ γ : GL (Fin 2) F,
    IsTotallyPositive γ.det.val ∧ ∃ u ∈ levelOne 𝔑, y =
      GeneralLinearGroup.map (algebraMap F 𝔸ᶠ[F]) γ * diagFin x * u := by
  rcases NarrowClassGroup.mk_eq_mk_iff.mp hx with ⟨_, hz, hzeq⟩
  rcases mem_narrowPrincipalSubgroup.mp hz with ⟨q, hq, rfl⟩
  let q₀ : 𝔸ᶠ[F]ˣ := unitEmbedding (𝓞 F) F q
  let u₀ : 𝔸ᶠ[F]ˣ := (x * q₀)⁻¹ * y.det
  have hu₀ : u₀ ∈ integralUnits (𝓞 F) F := by
    rw [← ker_toFractionalIdeal, MonoidHom.mem_ker, map_mul, map_inv, map_mul,
      toFractionalIdeal_unitEmbedding, hzeq, inv_mul_cancel]
  have hy : y.det = q₀ * (x * u₀) := by
    rw [← mul_assoc, mul_comm q₀ x, mul_inv_cancel_left]
  let s₀ : GL (Fin 2) 𝔸ᶠ[F] := (diagFin q₀)⁻¹ * y * (diagFin (x * u₀))⁻¹
  have hs₀ : s₀.det = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv, det_diagHom, det_diagHom, hy, inv_mul_cancel_left,
      mul_inv_cancel]
  rcases exists_det_eq_one_inv_mul_mem hs₀
    ((⟨levelOne 𝔑, isOpen_levelOne h𝔑⟩ : OpenSubgroup (GL (Fin 2) 𝔸ᶠ[F])).comap
      (MulAut.conj (diagFin x)⁻¹).toMonoidHom
        ((continuous_const.mul continuous_id).mul continuous_const)) with ⟨γ₀, hγ₀, hw⟩
  have hw₁ : (diagFin x)⁻¹ * ((GeneralLinearGroup.map (algebraMap F 𝔸ᶠ[F]) γ₀)⁻¹ * s₀) *
      (diagFin x)⁻¹⁻¹ ∈ levelOne 𝔑 :=
    OpenSubgroup.mem_comap.mp hw
  have hq₀ : GeneralLinearGroup.map (algebraMap F 𝔸ᶠ[F]) (diagHom q) = diagFin q₀ :=
    map_diagHom q _
  refine ⟨diagHom q * γ₀, ?_, _, mul_mem hw₁ (diagFin_mem_levelOne hu₀), ?_⟩
  · rw [map_mul, det_diagHom, hγ₀, mul_one]
    exact hq
  · rw [map_mul, hq₀]
    simp only [s₀, map_mul]
    group

/-- **`𝔑Ô ∩ F = 𝔑`** for an ideal `𝔑 ≠ 0` of a number field `F`: the diagonal image of `c ∈ F` lies
in `𝔑Ô` exactly when `c ∈ 𝔑`. -/
lemma algebraMap_mem_adelicIdeal_iff (h𝔑 : 𝔑 ≠ ⊥) {c : F} :
    algebraMap F 𝔸ᶠ[F] c ∈ adelicIdeal 𝔑 ↔ ∃ a ∈ 𝔑, c = algebraMap (𝓞 F) F a := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases (algebraMap_mem_integralAdeles_iff c).mp (mem_integralAdeles_of_mem_adelicIdeal h) with
      ⟨a, rfl⟩
    refine ⟨a, ?_, rfl⟩
    rw [← Ideal.iInf_maxPowDividing_eq h𝔑, Submodule.mem_iInf]
    exact fun v ↦ v.mem_asIdeal_pow_iff_valued_algebraMap_le.mpr (h v _ (Ideal.dvd_iff_le.mpr
      ((Ideal.iInf_maxPowDividing_eq h𝔑).symm.le.trans (iInf_le _ v))))
  · rintro ⟨a, ha, rfl⟩ v n hn
    exact v.mem_asIdeal_pow_iff_valued_algebraMap_le.mp <| Ideal.le_of_dvd hn ha

lemma isTotallyPositive_rat_iff : IsTotallyPositive q ↔ 0 < q := by
  refine ⟨fun h ↦ ?_, fun h ↦ Rat.cast_id q ▸ isTotallyPositive_ratCast h⟩
  have h₁ : 0 < embedding_of_isReal Rat.isReal_infinitePlace q := h _ Rat.isReal_infinitePlace
  rwa [eq_ratCast, Rat.cast_pos] at h₁

lemma narrowClass_rat_eq_one (I : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) : NarrowClassGroup.mk I = 1 := by
  rcases ClassGroup.mk_eq_one_iff_exists.mp (Subsingleton.elim (ClassGroup.mk ℚ I) 1) with ⟨a, rfl⟩
  rw [← NarrowClassGroup.mkPrincipal_apply]
  rcases a.ne_zero.lt_or_gt with h | h
  · rw [← NarrowClassGroup.mkPrincipal_neg]
    exact NarrowClassGroup.mkPrincipal_eq_one_of_isTotallyPositive <|
      isTotallyPositive_rat_iff.mpr <| by simpa using h
  · exact NarrowClassGroup.mkPrincipal_eq_one_of_isTotallyPositive <|
      isTotallyPositive_rat_iff.mpr h

lemma span_natCast_ne_bot : Ideal.span {(N : 𝓞 ℚ)} ≠ ⊥ :=
  mt Ideal.span_singleton_eq_bot.mp <| Nat.cast_ne_zero.mpr <| NeZero.ne N

/-- **The decomposition of `GL₂(𝔸_ℚ^f)`**: `GL₂(𝔸_ℚ^f) = GL₂(ℚ)⁺ K₁(N)`, as the narrow class group
of `ℚ` is trivial. -/
lemma rat_exists_eq_mul_levelOne (y : GL (Fin 2) 𝔸ᶠ[ℚ]) : ∃ γ : GL (Fin 2) ℚ, 0 < (γ.det : ℚ) ∧
    ∃ u ∈ levelOne (Ideal.span {(N : 𝓞 ℚ)}), y =
      GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) γ * u := by
  rcases exists_eq_map_mul_diagFin_mul (span_natCast_ne_bot N) y (x := 1)
    ((narrowClass_rat_eq_one _).trans (narrowClass_rat_eq_one _).symm) with ⟨γ, hγ, u, hu, h⟩
  refine ⟨γ, isTotallyPositive_rat_iff.mp hγ, u, hu, ?_⟩
  rwa [map_one, mul_one] at h

lemma intCast_num_of_algebraMap_mem (h : algebraMap ℚ 𝔸ᶠ[ℚ] q ∈ integralAdeles (𝓞 ℚ) ℚ) :
    (q.num : ℚ) = q := by
  rcases (algebraMap_mem_integralAdeles_iff q).mp h with ⟨a, rfl⟩
  rw [← Rat.ringOfIntegersEquiv_apply_coe a, Rat.num_intCast]

lemma algebraMap_intCast_mem_adelicIdeal_iff :
    algebraMap ℚ 𝔸ᶠ[ℚ] (z : ℚ) ∈ adelicIdeal (Ideal.span {(N : 𝓞 ℚ)}) ↔ (z : ZMod N) = 0 := by
  rw [algebraMap_mem_adelicIdeal_iff (span_natCast_ne_bot N), ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨a, ha, h⟩
    rcases Ideal.mem_span_singleton'.mp ha with ⟨b, rfl⟩
    refine ⟨Rat.ringOfIntegersEquiv b, ?_⟩
    have h₁ : (z : ℚ) = ((N * Rat.ringOfIntegersEquiv b : ℤ) : ℚ) := by
      rw [h, map_mul, ← Rat.ringOfIntegersEquiv_apply_coe b, map_natCast]
      push_cast
      ring1
    exact_mod_cast h₁
  · rintro ⟨k, rfl⟩
    refine ⟨(k : 𝓞 ℚ) * N, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), ?_⟩
    rw [map_mul, map_intCast, map_natCast]
    push_cast
    ring1

lemma algebraMap_intCast_sub_one_mem_adelicIdeal_iff :
    algebraMap ℚ 𝔸ᶠ[ℚ] (z : ℚ) - 1 ∈ adelicIdeal (Ideal.span {(N : 𝓞 ℚ)}) ↔ (z : ZMod N) = 1 := by
  rw [← map_one (algebraMap ℚ 𝔸ᶠ[ℚ]), ← map_sub, ← Int.cast_one, ← Int.cast_sub,
    algebraMap_intCast_mem_adelicIdeal_iff, Int.cast_sub, Int.cast_one, sub_eq_zero]

lemma intCast_num_apply (hγ : GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) γ ∈ integralGL ℚ) :
    ((γ i j).num : ℚ) = γ i j :=
  intCast_num_of_algebraMap_mem (hγ i j).1

lemma intCast_det_num (hγ : GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) γ ∈ integralGL ℚ) :
    (((of fun i j ↦ (γ i j).num).det : ℤ) : ℚ) = γ.det := by
  rw [det_fin_two, GeneralLinearGroup.val_det_apply, det_fin_two]
  simp only [of_apply, Int.cast_sub, Int.cast_mul, intCast_num_apply _ _ hγ]

lemma det_num_eq_one (hd : 0 < (γ.det : ℚ))
    (hγ : GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) γ ∈ integralGL ℚ) :
    (of fun i j ↦ (γ i j).num).det = 1 := by
  have h₁ : (((of fun i j ↦ (γ i j).num).det : ℤ) : ℚ) = γ.det := intCast_det_num hγ
  have h₂ : (((of fun i j ↦ (γ⁻¹ i j).num).det : ℤ) : ℚ) = (γ⁻¹).det :=
    intCast_det_num (map_inv (GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ])) γ ▸ inv_mem hγ)
  have h₃ : (γ.det : ℚ) * ((γ⁻¹).det : ℚ) = 1 := by
    rw [map_inv, Units.mul_inv]
  rw [← h₁, ← h₂] at h₃
  rw [← h₁] at hd
  exact Int.eq_one_of_mul_eq_one_right (by exact_mod_cast hd.le) (by exact_mod_cast h₃)

/-- **`GL₂(ℚ)⁺ ∩ K₁(N)` lies in `Γ₁(N)`**: a matrix of `GL₂(ℚ)` of positive determinant whose image
in `GL₂(𝔸_ℚ^f)` lies in `K₁(N)` comes from `Γ₁(N)`. -/
lemma mem_gamma1_of_mem_levelOne (hd : 0 < (γ.det : ℚ))
    (hγ : GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) γ ∈ levelOne (Ideal.span {(N : 𝓞 ℚ)})) :
    ∃ g ∈ CongruenceSubgroup.Gamma1 N, γ = SpecialLinearGroup.mapGL ℚ g := by
  have hc : ((γ 1 0).num : ZMod N) = 0 := by
    have h : algebraMap ℚ 𝔸ᶠ[ℚ] (γ 1 0) ∈ adelicIdeal (Ideal.span {(N : 𝓞 ℚ)}) := hγ.2.1
    rwa [← intCast_num_apply _ _ hγ.1, algebraMap_intCast_mem_adelicIdeal_iff] at h
  have hd₁ : ((γ 1 1).num : ZMod N) = 1 := by
    have h : algebraMap ℚ 𝔸ᶠ[ℚ] (γ 1 1) - 1 ∈ adelicIdeal (Ideal.span {(N : 𝓞 ℚ)}) := hγ.2.2
    rwa [← intCast_num_apply _ _ hγ.1, algebraMap_intCast_sub_one_mem_adelicIdeal_iff] at h
  have ha : ((γ 0 0).num : ZMod N) = 1 := by
    have h : (((of fun i j ↦ (γ i j).num).det : ℤ) : ZMod N) = 1 := by
      rw [det_num_eq_one hd hγ.1, Int.cast_one]
    simpa [det_fin_two, hc, hd₁] using h
  exact ⟨⟨of fun i j ↦ (γ i j).num, det_num_eq_one hd hγ.1⟩,
    (CongruenceSubgroup.Gamma1_mem N _).mpr ⟨ha, hd₁, hc⟩, GeneralLinearGroup.ext fun i j ↦
      (intCast_num_apply i j hγ.1).symm.trans (eq_intCast (algebraMap ℤ ℚ) _).symm⟩

lemma map_mapGL_apply : GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) (SpecialLinearGroup.mapGL ℚ g)
    i j = algebraMap ℚ 𝔸ᶠ[ℚ] ((g i j : ℤ) : ℚ) := by
  simp

lemma map_mapGL_apply_mem : GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ])
    (SpecialLinearGroup.mapGL ℚ g) i j ∈ integralAdeles (𝓞 ℚ) ℚ := by
  rw [map_mapGL_apply]
  exact (algebraMap_mem_integralAdeles_iff _).mpr ⟨(g i j : 𝓞 ℚ), map_intCast _ _⟩

/-- **`Γ₁(N)` lies in `K₁(N)`**: the image in `GL₂(𝔸_ℚ^f)` of a matrix of `Γ₁(N)` lies in
`K₁(N)`. -/
lemma map_mem_levelOne_of_mem_gamma1 (hg : g ∈ CongruenceSubgroup.Gamma1 N) :
    GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) (SpecialLinearGroup.mapGL ℚ g) ∈
      levelOne (Ideal.span {(N : 𝓞 ℚ)}) := by
  rcases (CongruenceSubgroup.Gamma1_mem N g).mp hg with ⟨-, h₁, h₂⟩
  refine ⟨fun i j ↦ ⟨map_mapGL_apply_mem i j, ?_⟩, ?_, ?_⟩
  · rw [← map_inv, ← map_inv]
    exact map_mapGL_apply_mem i j
  · rw [map_mapGL_apply]
    exact (algebraMap_intCast_mem_adelicIdeal_iff N).mpr h₂
  · rw [map_mapGL_apply]
    exact (algebraMap_intCast_sub_one_mem_adelicIdeal_iff N).mpr h₁

/-- The isomorphism from the mixed space `E` of `ℚ` to `ℝ`, the unique infinite place of `ℚ` being
real. -/
noncomputable def ratMixedEquiv : mixedSpace ℚ ≃+* ℝ where
  toFun x := x.1 ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
  invFun r := (fun _ ↦ r, 0)
  left_inv x := Prod.ext (funext fun _ ↦ congrArg x.1 (Subtype.ext (Subsingleton.elim _ _)))
    (funext fun w ↦ absurd w.2 (not_isComplex_iff_isReal.mpr
      (Subsingleton.elim Rat.infinitePlace w.1 ▸ Rat.isReal_infinitePlace)))
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

variable (q) in
/-- **`ratMixedEquiv` sends a rational to itself**: it identifies the mixed embedding of `ℚ` with
the inclusion `ℚ → ℝ`. -/
lemma ratMixedEquiv_mixedEmbedding : ratMixedEquiv (mixedEmbedding ℚ q) = (q : ℝ) :=
  (mixedEmbedding.mixedEmbedding_apply_isReal ℚ q _).trans (eq_ratCast _ q)

/-- `ratMixedEquiv` as a continuous `ℝ`-linear isomorphism, through which calculus transfers. -/
noncomputable def ratMixedEquivL : mixedSpace ℚ ≃L[ℝ] ℝ where
  toLinearEquiv := { ratMixedEquiv with map_smul' := fun _ _ ↦ rfl }
  continuous_toFun := (continuous_apply _).comp continuous_fst
  continuous_invFun := (continuous_pi fun _ ↦ continuous_id).prodMk continuous_const

lemma ratMixedEquivL_apply (w : mixedSpace ℚ) : ratMixedEquivL w = ratMixedEquiv w :=
  rfl

lemma continuous_ratMixedEquiv : Continuous (ratMixedEquiv : mixedSpace ℚ →+* ℝ) :=
  ratMixedEquivL.continuous

lemma continuous_ratMixedEquiv_symm : Continuous (ratMixedEquiv.symm : ℝ →+* mixedSpace ℚ) :=
  ratMixedEquivL.symm.continuous

/-- The isomorphism `GL₂(E) ≃ GL₂(ℝ)` induced by `ratMixedEquiv`, for the mixed space `E` of `ℚ`. -/
noncomputable def ratInfEquiv : GL (Fin 2) (mixedSpace ℚ) ≃* GL (Fin 2) ℝ :=
  Units.mapEquiv ratMixedEquiv.mapMatrix.toMulEquiv

lemma ratInfEquiv_apply (k : GL (Fin 2) (mixedSpace ℚ)) :
    ratInfEquiv k i j = ratMixedEquiv (k i j) :=
  rfl

variable (γ) in
lemma ratInfEquiv_map_mixedEmbedding : ratInfEquiv (GeneralLinearGroup.map (mixedEmbedding ℚ) γ) =
    GeneralLinearGroup.map (algebraMap ℚ ℝ) γ :=
  GeneralLinearGroup.ext fun i j ↦ (ratMixedEquiv_mixedEmbedding (γ i j)).trans
    (eq_ratCast (algebraMap ℚ ℝ) _).symm

lemma continuous_ratInfEquiv : Continuous ratInfEquiv :=
  continuous_ratMixedEquiv.generalLinearGroup_map

lemma continuous_ratInfEquiv_symm : Continuous ratInfEquiv.symm :=
  continuous_ratMixedEquiv_symm.generalLinearGroup_map

end AdelicGL2
