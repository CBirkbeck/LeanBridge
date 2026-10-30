import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Level
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Instances.ZMod
import TauCeti.Data.ZMod.Divisibility
import TauCeti.NumberTheory.Padics.RingHoms

/-!
# Inverse images in `GL_n(ℤ̂)` of subgroups of `GL_n(ℤ/Nℤ)`

The LMFDB defines many modular curves `X_H` by a subgroup `H_N` of `GL₂(ℤ/Nℤ)`: the open subgroup
`H` of `GL₂(ℤ̂)` is then the inverse image of `H_N` under reduction modulo `N`. As in
`LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Level`, `GL_n(ℤ̂)` is the product `∏_ℓ GL_n(ℤ_ℓ)`
over the primes, and its reduction modulo `N` takes values in `∏_ℓ GL_n(ℤ / ℓ ^ v_ℓ(N) ℤ)`.
Reducing the entries of a matrix over `ℤ/Nℤ` modulo the prime powers `ℓ ^ v_ℓ(N)` identifies
`GL_n(ℤ/Nℤ)` with this product, by the Chinese remainder theorem, which gives the reduction modulo
`N` with values in `GL_n(ℤ/Nℤ)`; it is surjective, as invertible matrices over `ℤ / ℓ ^ v_ℓ(N) ℤ`
lift to `ℤ_ℓ`. The inverse image of a subgroup of `GL_n(ℤ/Nℤ)` contains the kernel of the
reduction modulo `N`, so it is open, it is the inverse image of its reduction modulo `N`, so its
level is at most `N`, and it has the same index as the subgroup.

## Main definitions

* `Matrix.GeneralLinearGroup.chineseRemainder`: the reduction
  `GL_n(ℤ/Nℤ) → ∏_ℓ GL_n(ℤ / ℓ ^ v_ℓ(N) ℤ)` of the entries modulo the `ℓ ^ v_ℓ(N)`.
* `Matrix.GeneralLinearGroup.chineseRemainderInv`: the element of `ℤ/Nℤ` with given reductions
  modulo the `ℓ ^ v_ℓ(N)`.
* `Matrix.GeneralLinearGroup.adelicReductionZMod`: the reduction `GL_n(ℤ̂) → GL_n(ℤ/Nℤ)` modulo `N`.
* `Matrix.GeneralLinearGroup.adelicPreimage`: the inverse image in `GL_n(ℤ̂)` of a subgroup of
  `GL_n(ℤ/Nℤ)`.

## Main results

* `Matrix.GeneralLinearGroup.chineseRemainder_bijective`: the Chinese remainder theorem for
  `GL_n(ℤ/Nℤ)`.
* `Matrix.GeneralLinearGroup.adelicReductionZMod_surjective`: reduction modulo `N` is surjective.
* `Matrix.GeneralLinearGroup.isOpen_adelicPreimage`: the inverse image of a subgroup of
  `GL_n(ℤ/Nℤ)` is open in `GL_n(ℤ̂)`.
* `Matrix.GeneralLinearGroup.adelicLevel_adelicPreimage_le`: its level is at most `N`.
* `Matrix.GeneralLinearGroup.index_adelicPreimage`: it has the same index as the subgroup.
-/

open Function Topology

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] (N : ℕ) (ℓ : Nat.Primes) (p : ℕ) [Fact p.Prime]
  (y : ∀ ℓ : Nat.Primes, ZMod ((ℓ : ℕ) ^ N.factorization ℓ)) (K K' : Subgroup (GL n (ZMod N)))

variable {ℓ} in
lemma subsingleton_zmod_of_not_dvd (hℓ : ¬(ℓ : ℕ) ∣ N) :
    Subsingleton (ZMod ((ℓ : ℕ) ^ N.factorization ℓ)) :=
  ZMod.subsingleton_iff.mpr <| by rw [Nat.factorization_eq_zero_of_not_dvd hℓ, pow_zero]

/-- **Reduction modulo the prime powers dividing `N`**: the homomorphism
`GL_n(ℤ/Nℤ) → ∏_ℓ GL_n(ℤ / ℓ ^ v_ℓ(N) ℤ)` reducing the entries modulo `ℓ ^ v_ℓ(N)` at every prime
`ℓ`, the factors at the primes not dividing `N` being trivial. For `N ≠ 0` it is an isomorphism, by
the Chinese remainder theorem (`chineseRemainder_bijective`). -/
noncomputable def chineseRemainder :
    GL n (ZMod N) →* ∀ ℓ : Nat.Primes, GL n (ZMod ((ℓ : ℕ) ^ N.factorization ℓ)) :=
  MonoidHom.pi fun ℓ ↦ map (ZMod.castHom (Nat.ordProj_dvd N ℓ) _)

lemma isOpen_ker_padicReduction : IsOpen ((padicReduction (n := n) p N).ker : Set (GL n ℤ_[p])) :=
  (padicReduction (n := n) p N).coe_ker ▸ (isOpen_discrete {1}).preimage
    (Units.continuous_map (continuous_id.matrix_map (PadicInt.continuous_toZModPow _)))

lemma map_surjective_of_isLocalHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    [IsLocalHom f] (hf : Surjective f) : Surjective (map (n := n) f) := by
  intro g
  have hM : (g.val.map (surjInv hf)).map f = g.val :=
    Matrix.ext fun _ _ ↦ surjInv_eq hf _
  have hdet : IsUnit (g.val.map (surjInv hf)).det := isUnit_of_map_unit f _ <| by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
    exact isUnits_det_units g
  exact ⟨((isUnit_iff_isUnit_det _).mpr hdet).unit, Units.ext hM⟩

lemma padicReduction_surjective : Surjective (padicReduction (n := n) p N) := by
  rcases Nat.eq_zero_or_pos (N.factorization p) with h | h
  · have : Subsingleton (ZMod (p ^ N.factorization p)) :=
      ZMod.subsingleton_iff.mpr <| by rw [h, pow_zero]
    exact fun _ ↦ ⟨1, Units.ext <| Matrix.ext fun _ _ ↦ Subsingleton.elim _ _⟩
  · have : Fact (1 < p ^ N.factorization p) := ⟨Nat.one_lt_pow h.ne' (Fact.out : p.Prime).one_lt⟩
    have : IsLocalHom (PadicInt.toZModPow (p := p) (N.factorization p)) :=
      IsLocalHom.of_surjective _ (ZMod.ringHom_surjective _)
    exact map_surjective_of_isLocalHom _ (ZMod.ringHom_surjective _)

lemma adelicReduction_surjective : Surjective (adelicReduction (n := n) N) :=
  Surjective.piMap fun ℓ : Nat.Primes ↦ padicReduction_surjective N ℓ

variable [NeZero N]

lemma eq_zero_of_forall_castHom_eq_zero {x : ZMod N} (h : ∀ ℓ : Nat.Primes, ZMod.castHom
    (Nat.ordProj_dvd N ℓ) (ZMod ((ℓ : ℕ) ^ N.factorization ℓ)) x = 0) : x = 0 :=
  (ZMod.equivPi N (NeZero.ne N)).injective <| funext fun q ↦ by
    rw [ZMod.equivPi_apply, ZMod.equivPi_apply, map_zero]
    exact h ⟨q, (Nat.mem_primeFactors.mp q.2).1⟩

/-- The element of `ℤ/Nℤ` with given reductions `y ℓ` modulo the prime powers `ℓ ^ v_ℓ(N)`
(`castHom_chineseRemainderInv`), by the Chinese remainder theorem `ZMod.equivPi`. -/
noncomputable def chineseRemainderInv : ZMod N :=
  (ZMod.equivPi N (NeZero.ne N)).symm fun q ↦ y ⟨q, (Nat.mem_primeFactors.mp q.2).1⟩

lemma castHom_chineseRemainderInv :
    ZMod.castHom (Nat.ordProj_dvd N ℓ) _ (chineseRemainderInv N y) = y ℓ := by
  by_cases hℓ : (ℓ : ℕ) ∣ N
  · have hmem : (ℓ : ℕ) ∈ N.primeFactors := Nat.mem_primeFactors.mpr ⟨ℓ.2, hℓ, NeZero.ne N⟩
    exact (ZMod.equivPi_apply N (NeZero.ne N) _ ⟨ℓ, hmem⟩).symm.trans <|
      congr_fun ((ZMod.equivPi N (NeZero.ne N)).apply_symm_apply _) ⟨ℓ, hmem⟩
  · have : Subsingleton (ZMod ((ℓ : ℕ) ^ N.factorization ℓ)) := subsingleton_zmod_of_not_dvd N hℓ
    exact Subsingleton.elim _ _

lemma chineseRemainder_injective : Injective (chineseRemainder (n := n) N) :=
  fun _ _ h ↦ Units.ext <| Matrix.ext fun i j ↦ sub_eq_zero.mp <|
    eq_zero_of_forall_castHom_eq_zero N fun ℓ ↦ (map_sub _ _ _).trans <| sub_eq_zero.mpr <|
      congr_arg (fun g ↦ (g ℓ).val i j) h

lemma chineseRemainder_surjective : Surjective (chineseRemainder (n := n) N) := by
  intro z
  let M : Matrix n n (ZMod N) := Matrix.of fun i j ↦ chineseRemainderInv N fun ℓ ↦ (z ℓ).val i j
  let M' : Matrix n n (ZMod N) := Matrix.of fun i j ↦ chineseRemainderInv N fun ℓ ↦ (z ℓ)⁻¹.val i j
  have hM (ℓ : Nat.Primes) : M.map (ZMod.castHom (Nat.ordProj_dvd N ℓ) _) = (z ℓ).val :=
    Matrix.ext fun i j ↦ castHom_chineseRemainderInv N ℓ fun ℓ ↦ (z ℓ).val i j
  have hM' (ℓ : Nat.Primes) : M'.map (ZMod.castHom (Nat.ordProj_dvd N ℓ) _) = (z ℓ)⁻¹.val :=
    Matrix.ext fun i j ↦ castHom_chineseRemainderInv N ℓ fun ℓ ↦ (z ℓ)⁻¹.val i j
  have hmul : M * M' = 1 := by
    ext i j
    refine sub_eq_zero.mp <| eq_zero_of_forall_castHom_eq_zero N fun ℓ ↦ ?_
    rw [map_sub, sub_eq_zero, RingHom.map_matrix_mul, hM, hM', ← Units.val_mul, mul_inv_cancel,
      Units.val_one]
    exact congr_fun₂ (Matrix.map_one (ZMod.castHom (Nat.ordProj_dvd N ℓ) _) (map_zero _)
      (map_one _)).symm i j
  exact ⟨⟨M, M', hmul, mul_eq_one_comm.mp hmul⟩, funext fun ℓ ↦ Units.ext (hM ℓ)⟩

/-- **The Chinese remainder theorem for `GL_n(ℤ/Nℤ)`**: for `N ≠ 0`, reducing the entries modulo
the prime powers `ℓ ^ v_ℓ(N)` is an isomorphism `GL_n(ℤ/Nℤ) ≃ ∏_ℓ GL_n(ℤ / ℓ ^ v_ℓ(N) ℤ)`. -/
lemma chineseRemainder_bijective : Bijective (chineseRemainder (n := n) N) :=
  ⟨chineseRemainder_injective N, chineseRemainder_surjective N⟩

/-- **Reduction modulo `N`** of `GL_n(ℤ̂) = ∏_ℓ GL_n(ℤ_ℓ)`, with values in `GL_n(ℤ/Nℤ)`: the
reduction `adelicReduction N` modulo the prime powers `ℓ ^ v_ℓ(N)`, read in `GL_n(ℤ/Nℤ)` through the
Chinese remainder theorem (`chineseRemainder_bijective`). -/
noncomputable def adelicReductionZMod : (∀ ℓ : Nat.Primes, GL n ℤ_[ℓ]) →* GL n (ZMod N) :=
  (MulEquiv.ofBijective _ (chineseRemainder_bijective N)).symm.toMonoidHom.comp (adelicReduction N)

lemma chineseRemainder_adelicReductionZMod (g : ∀ ℓ : Nat.Primes, GL n ℤ_[ℓ]) :
    chineseRemainder N (adelicReductionZMod N g) = adelicReduction N g :=
  (MulEquiv.ofBijective _ (chineseRemainder_bijective N)).apply_symm_apply _

/-- **Reduction modulo `N` is surjective** from `GL_n(ℤ̂)` onto `GL_n(ℤ/Nℤ)`: a matrix over
`ℤ / ℓ ^ v_ℓ(N) ℤ` with unit determinant lifts to one over the local ring `ℤ_ℓ`, whose determinant
is a unit as well. -/
lemma adelicReductionZMod_surjective : Surjective (adelicReductionZMod (n := n) N) :=
  (MulEquiv.ofBijective _ (chineseRemainder_bijective N)).symm.surjective.comp
    (adelicReduction_surjective N)

/-- The **inverse image in `GL_n(ℤ̂)`** of a subgroup `K` of `GL_n(ℤ/Nℤ)`, under reduction modulo
`N` (`adelicReductionZMod`). It is open (`isOpen_adelicPreimage`), of level at most `N`
(`adelicLevel_adelicPreimage_le`), and of the same index as `K` (`index_adelicPreimage`); for
`n = 2` its modular curve is the LMFDB's `X_H` attached to `K`. -/
noncomputable def adelicPreimage : Subgroup (∀ ℓ : Nat.Primes, GL n ℤ_[ℓ]) :=
  K.comap (adelicReductionZMod N)

/-- **The inverse image in `GL_n(ℤ̂)` of a subgroup of `GL_n(ℤ/Nℤ)` has the same index**, as
reduction modulo `N` is surjective. -/
lemma index_adelicPreimage : (adelicPreimage N K).index = K.index :=
  K.index_comap_of_surjective (adelicReductionZMod_surjective N)

variable {K K'} in
lemma adelicPreimage_mono (h : K ≤ K') : adelicPreimage N K ≤ adelicPreimage N K' :=
  Subgroup.comap_mono h

lemma relIndex_adelicPreimage :
    (adelicPreimage N K).relIndex (adelicPreimage N K') = K.relIndex K' := by
  rw [adelicPreimage, adelicPreimage, Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self_of_surjective (adelicReductionZMod_surjective N)]

lemma ker_adelicReduction_le_adelicPreimage : (adelicReduction N).ker ≤ adelicPreimage N K :=
  fun g hg ↦ Subgroup.mem_comap.mpr <| (chineseRemainder_injective N <|
    (chineseRemainder_adelicReductionZMod N g).trans <| hg.trans (map_one _).symm) ▸ one_mem K

lemma isOpen_ker_adelicReduction :
    IsOpen ((adelicReduction (n := n) N).ker : Set (∀ ℓ : Nat.Primes, GL n ℤ_[ℓ])) := by
  have ht (ℓ : Nat.Primes) : ((padicReduction (n := n) ℓ N).ker : Set (GL n ℤ_[ℓ])) ∈ 𝓝 1 :=
    (isOpen_ker_padicReduction N ℓ).mem_nhds (one_mem _)
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  rw [nhds_pi, Filter.mem_pi]
  refine ⟨Subtype.val ⁻¹' (N.divisors : Set ℕ),
    N.divisors.finite_toSet.preimage Subtype.val_injective.injOn, _, ht,
    fun g hg ↦ funext fun ℓ ↦ ?_⟩
  by_cases hℓ : (ℓ : ℕ) ∣ N
  · exact hg ℓ (Nat.mem_divisors.mpr ⟨hℓ, NeZero.ne N⟩)
  · have : Subsingleton (ZMod ((ℓ : ℕ) ^ N.factorization ℓ)) := subsingleton_zmod_of_not_dvd N hℓ
    exact Units.ext <| Matrix.ext fun _ _ ↦ Subsingleton.elim _ _

/-- **The inverse image in `GL_n(ℤ̂)` of a subgroup of `GL_n(ℤ/Nℤ)` is open**: it contains the
kernel of the reduction modulo `N`, which is open. -/
lemma isOpen_adelicPreimage : IsOpen (adelicPreimage N K : Set (∀ ℓ : Nat.Primes, GL n ℤ_[ℓ])) :=
  Subgroup.isOpen_mono (ker_adelicReduction_le_adelicPreimage N K) (isOpen_ker_adelicReduction N)

/-- **The level of the inverse image in `GL_n(ℤ̂)` of a subgroup of `GL_n(ℤ/Nℤ)` is at most `N`**:
it is the inverse image of its reduction modulo `N`. -/
lemma adelicLevel_adelicPreimage_le : adelicLevel ⊤ (adelicPreimage N K) ≤ N :=
  Nat.sInf_le ⟨NeZero.pos N, by
    rw [top_inf_eq, Subgroup.comap_map_eq_self (ker_adelicReduction_le_adelicPreimage N K)]⟩

end Matrix.GeneralLinearGroup
