import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.ClassicalLiftCasimir
import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.GL2.Twist
import TauCeti.NumberTheory.ModularForms.Conjugate
import TauCeti.NumberTheory.ModularForms.DiamondOperators
import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Dirichlet
import TauCeti.NumberTheory.NumberField.Global.Ideles.FiniteIdeal
import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Basic
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# The central character of the adelic lift

Let `f` be a cusp form of weight `k` on `Γ₁(N)` with nebentypus `χ : (ℤ / N ℤ)ˣ → ℂˣ`, so that
`f ∣[k] γ = χ(d) f` for `γ = (a, b; c, d) ∈ Γ₀(N)`. This file proves that the adelic lift `φ_f`
(`AdelicGL2.adelicLift`) has central character `ω`, the Hecke character of `ℚ` attached to `χ` by
Tau Ceti's `HeckeCharacter.ofDirichletCharacter`, so that `φ_f` is an automorphic form on
`GL₂(𝔸_ℚ)` of central character `ω`.

The convention is the one of Tau Ceti's diamond operators and of `ofDirichletCharacter`: `ω` is
trivial on `ℚˣ` and on the positive reals, `ω(ϖ_p) = χ(p)` for a uniformizer `ϖ_p` of `ℚ_p` with
`p ∤ N`, and `ω(u) = χ(u mod N)⁻¹` for `u ∈ Ẑˣ`. Indeed, if `a u ≡ 1 mod N` with `a ∈ ℕ`, then
`ω(u) = χ(a)`, and `φ_f(u g) = χ(a) φ_f(g)`: for `γ ∈ Γ₀(N)` with lower right entry `d ≡ a mod N`,
the matrix `γ u` lies in `K₁(N)`, and `Φ_f(γ x) = χ(d) Φ_f(x)` on `GL₂(ℝ)`. The ideles are generated
by `ℚˣ`, `ℝˣ` and `Ẑˣ`, as the class number of `ℚ` is one, and `-1 ∈ ℚˣ` takes the negative reals to
the positive ones.

## Main results

* `AdelicGL2.characterAt_ofDirichletCharacter`: the Hecke character of a Dirichlet character `ψ`
  takes the value `ψ(p)` at a uniformizer of `ℚ_p`, for `p ∤ N`.
* `AdelicGL2.adelicLift_scalar_mul`: `φ_f(z g) = ω(z) φ_f(g)` for every idele `z`.
* `AdelicGL2.isAutomorphicForm_adelicLift`: `φ_f` is an automorphic form of central character `ω`.
-/

open Matrix hiding mul_inv_rev one_zpow zpow_mul zpow_neg

open IsDedekindDomain HeightOneSpectrum NumberField InfinitePlace Rat UpperHalfPlane TauCeti
  GlobalNumberFields

open FiniteAdeleRing (integralAdeles integralUnits toFractionalIdeal)

open mixedEmbedding (mixedSpace)

open scoped AdeleRing Classical MatrixGroups ModularForm nonZeroDivisors

namespace AdelicGL2

section Dirichlet

variable {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) {a : ℕ} {r : (mixedSpace ℚ)ˣ}

lemma ofDirichletCharacter_apply_of_mem {x : IdeleGroup (𝓞 ℚ) ℚ}
    (hx : x ∈ ideleCongrOneSubgroup (ratModulus N (NeZero.ne N)))
    (ha : (toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 ℚ) ℚ x) : FractionalIdeal (𝓞 ℚ)⁰ ℚ) =
      (Ideal.span {(a : 𝓞 ℚ)} : Ideal (𝓞 ℚ))) :
    (HeckeCharacter.ofDirichletCharacter N (NeZero.ne N) ψ (QuotientGroup.mk x) : ℂ) = ψ a := by
  have hJ : Ideal.span {(a : 𝓞 ℚ)} ∈ integralIdealsPrimeTo (ratModulus N (NeZero.ne N)) := by
    refine (NumberFieldArithmetic.mem_integralIdealsAway_iff_count_eq_zero (K := ℚ)).mpr
      ⟨fun h ↦ ?_, fun v hv ↦ ?_⟩
    · rw [h] at ha
      exact Units.ne_zero _ (ha.trans FractionalIdeal.coeIdeal_bot)
    · rw [← ha]
      exact NumberFieldArithmetic.mem_idealsAway_iff.mp
        (toFractionalIdeal_toFiniteIdele_mem_idealsPrimeTo hx) v hv
  have hI : (⟨toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 ℚ) ℚ x),
      toFractionalIdeal_toFiniteIdele_mem_idealsPrimeTo hx⟩ :
        idealsPrimeTo (ratModulus N (NeZero.ne N))) =
      NumberFieldArithmetic.integralIdealsAwayHom ℚ _ ⟨_, hJ⟩ :=
    Subtype.ext (Units.ext (by rw [NumberFieldArithmetic.coe_integralIdealsAwayHom]; exact ha))
  have h₁ : ((ratModulusEquivZMod N (NeZero.ne N) (idealClass (ratModulus N (NeZero.ne N))
      ⟨_, hJ⟩) : (ZMod N)ˣ) : ZMod N) = a := by
    rw [coe_ratModulusEquivZMod_idealClass, Ideal.absNorm_span_natCast, RingOfIntegers.rank,
      Module.finrank_self, pow_one]
  rw [HeckeCharacter.ofDirichletCharacter_apply, rayClassQuotient_mk_of_mem hx, hI,
    ← idealClass_apply, MulChar.coe_toUnitHom, h₁]

variable (r) in
lemma ratMixedEquiv_eq_extensionEmbeddingOfIsReal (w : {w : InfinitePlace ℚ // w.IsReal}) :
    Completion.extensionEmbeddingOfIsReal w.2
      ((w.1.ideleInfiniteCoord (ideleOfMixed ℚ r) : w.1.Completionˣ) : w.1.Completion) =
        ratMixedEquiv (r : mixedSpace ℚ) := by
  rw [← (InfiniteAdeleRing.ringEquiv_mixedSpace ℚ).apply_symm_apply (r : mixedSpace ℚ),
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply,
    Subsingleton.elim w ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩]
  rfl

lemma ofDirichletCharacter_ideleOfMixed (hr : 0 < ratMixedEquiv (r : mixedSpace ℚ)) :
    HeckeCharacter.ofDirichletCharacter N (NeZero.ne N) ψ (QuotientGroup.mk (ideleOfMixed ℚ r)) =
      1 := by
  have hx : ideleOfMixed ℚ r ∈ ideleCongrOneSubgroup (ratModulus N (NeZero.ne N)) := by
    refine mem_ideleCongrOneSubgroup_iff.mpr ⟨fun v _ ↦ ?_, fun w _ ↦ ?_⟩
    · simp [ideleOfMixed]
    · rw [ratMixedEquiv_eq_extensionEmbeddingOfIsReal r w]
      exact hr
  have ha : (toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 ℚ) ℚ (ideleOfMixed ℚ r)) :
      FractionalIdeal (𝓞 ℚ)⁰ ℚ) = (Ideal.span {((1 : ℕ) : 𝓞 ℚ)} : Ideal (𝓞 ℚ)) := by
    simp [ideleOfMixed]
  exact Units.ext ((ofDirichletCharacter_apply_of_mem ψ hx ha).trans (by simp))

lemma ofDirichletCharacter_ofFiniteIdele {u : 𝔸ᶠ[ℚ]ˣ} (hu : u ∈ integralUnits (𝓞 ℚ) ℚ)
    (ha₀ : 0 < a)
    (ha : algebraMap ℚ 𝔸ᶠ[ℚ] (a : ℚ) * u - 1 ∈ adelicIdeal (Ideal.span {(N : 𝓞 ℚ)})) :
    (HeckeCharacter.ofDirichletCharacter N (NeZero.ne N) ψ
      (QuotientGroup.mk (IdeleGroup.ofFiniteIdele (𝓞 ℚ) ℚ u)) : ℂ) = ψ a := by
  let q : ℚˣ := Units.mk0 (a : ℚ) (by positivity)
  have hmk : (QuotientGroup.mk (IdeleGroup.ofFiniteIdele (𝓞 ℚ) ℚ u) : IdeleClassGroup (𝓞 ℚ) ℚ) =
      QuotientGroup.mk (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ q *
        IdeleGroup.ofFiniteIdele (𝓞 ℚ) ℚ u) := by
    rw [mul_comm, QuotientGroup.mk_mul_of_mem _ (MonoidHom.mem_range.mpr ⟨q, rfl⟩)]
  have hx : IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ q * IdeleGroup.ofFiniteIdele (𝓞 ℚ) ℚ u ∈
      ideleCongrOneSubgroup (ratModulus N (NeZero.ne N)) := by
    refine mem_ideleCongrOneSubgroup_iff.mpr ⟨fun v hv ↦ ?_, fun w _ ↦ ?_⟩
    · rw [HeightOneSpectrum.coe_ideleFiniteCoord]
      exact ha v _ (by
        rw [← ratModulus_finitePart N (NeZero.ne N)]
        exact Modulus.pow_exponent_dvd_finitePart _ v)
    · simp [q, ha₀]
  have hu' : toFractionalIdeal u = 1 := by
    rw [← MonoidHom.mem_ker, FiniteAdeleRing.ker_toFractionalIdeal]
    exact hu
  have ha' : (toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 ℚ) ℚ
      (IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ q * IdeleGroup.ofFiniteIdele (𝓞 ℚ) ℚ u)) :
        FractionalIdeal (𝓞 ℚ)⁰ ℚ) = (Ideal.span {(a : 𝓞 ℚ)} : Ideal (𝓞 ℚ)) := by
    rw [map_mul, map_mul, IdeleGroup.toFiniteIdele_unitEmbedding,
      IdeleGroup.toFiniteIdele_ofFiniteIdele, FiniteAdeleRing.toFractionalIdeal_unitEmbedding, hu',
      mul_one, coe_toPrincipalIdeal, FractionalIdeal.coeIdeal_span_singleton]
    simp [q]
  rw [hmk]
  exact ofDirichletCharacter_apply_of_mem ψ hx ha'

variable {v : HeightOneSpectrum (𝓞 ℚ)}

lemma ofDirichletCharacter_ofAdicCompletion (hv : ¬Ideal.span {(N : 𝓞 ℚ)} ≤ v.asIdeal)
    {u : (v.adicCompletion ℚ)ˣ} {n : ℕ}
    (hu : Valued.v (u : v.adicCompletion ℚ) = WithZero.exp (-(n : ℤ))) :
    (HeckeCharacter.ofDirichletCharacter N (NeZero.ne N) ψ
      (QuotientGroup.mk (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u)) : ℂ) =
        ψ ((Ideal.absNorm v.asIdeal ^ n : ℕ) : ZMod N) := by
  have hx : IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u ∈
      ideleCongrOneSubgroup (ratModulus N (NeZero.ne N)) := by
    refine mem_ideleCongrOneSubgroup_iff.mpr ⟨fun w hw ↦ ?_, fun w _ ↦ ?_⟩
    · have hwv : w ≠ v := by
        rintro rfl
        exact hv (Ideal.le_of_dvd (by simpa using hw))
      rw [w.ideleFiniteCoord_ofAdicCompletion_of_ne hwv u]
      simp
    · simp
  have ha : (toFractionalIdeal (IdeleGroup.toFiniteIdele (𝓞 ℚ) ℚ
      (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u)) : FractionalIdeal (𝓞 ℚ)⁰ ℚ) =
        (Ideal.span {((Ideal.absNorm v.asIdeal ^ n : ℕ) : 𝓞 ℚ)} : Ideal (𝓞 ℚ)) := by
    rw [toFractionalIdeal_toFiniteIdele_ofAdicCompletion, hu, WithZero.log_exp, neg_neg,
      Nat.cast_pow, ← Ideal.span_singleton_pow, RingOfIntegers.ideal_span_absNorm_eq_self,
      zpow_natCast, Units.val_pow_eq_pow_val, HeightOneSpectrum.coe_unitOfPrime,
      FractionalIdeal.coeIdeal_pow]
  exact ofDirichletCharacter_apply_of_mem ψ hx ha

/-- **The value of the Hecke character of a Dirichlet character `ψ` modulo `N` at a uniformizer**
of `ℚ_p`, for `p ∤ N`, is `ψ(p)`. -/
lemma characterAt_ofDirichletCharacter (hv : ¬Ideal.span {(N : 𝓞 ℚ)} ≤ v.asIdeal) :
    (characterAt v (HeckeCharacter.ofDirichletCharacter N (NeZero.ne N) ψ) : ℂ) =
      ψ (Ideal.absNorm v.asIdeal) := by
  have h₁ : (HeckeCharacter.ofDirichletCharacter N (NeZero.ne N) ψ
      (QuotientGroup.mk (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v (uniformizer v))) : ℂ) =
        ψ ((Ideal.absNorm v.asIdeal ^ 1 : ℕ) : ZMod N) :=
    ofDirichletCharacter_ofAdicCompletion ψ hv (by simpa using valued_uniformizer v)
  rw [pow_one] at h₁
  rw [characterAt, HeckeCharacter.finiteComponent_apply, IdeleClassGroup.ofAdicCompletion_apply]
  exact h₁

end Dirichlet

section Scalar

variable {F : Type*} [Field F] [NumberField F] (z : IdeleGroup (𝓞 F) F) (r : (mixedSpace F)ˣ)
  (i j : Fin 2)

lemma coe_ideleOfMixed : (ideleOfMixed F r : 𝔸[F]) =
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (r : mixedSpace F), 1) :=
  rfl

lemma ideleOfMixed_mul_ofFiniteIdele : ideleOfMixed F (Units.map
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toMonoidHom.comp (MonoidHom.fst _ _)) z) *
      IdeleGroup.ofFiniteIdele (𝓞 F) F (IdeleGroup.toFiniteIdele (𝓞 F) F z) = z := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_ideleOfMixed, IdeleGroup.coe_ofFiniteIdele, Prod.mk_mul_mk, mul_one,
    one_mul, Units.coe_map, MonoidHom.comp_apply]
  exact Prod.ext ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply _) rfl

lemma scalar_apply_fst : ((scalar F z : Matrix (Fin 2) (Fin 2) 𝔸[F]) i j).1 =
    (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j * (z : 𝔸[F]).1 := by
  rcases eq_or_ne i j with rfl | hij
  · simp only [scalar, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq, one_apply_eq,
      one_mul]
  · simp only [scalar, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_ne _ hij,
      one_apply_ne hij, zero_mul]
    rfl

lemma scalar_apply_snd : ((scalar F z : Matrix (Fin 2) (Fin 2) 𝔸[F]) i j).2 =
    (1 : Matrix (Fin 2) (Fin 2) 𝔸ᶠ[F]) i j * (z : 𝔸[F]).2 := by
  rcases eq_or_ne i j with rfl | hij
  · simp only [scalar, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq, one_apply_eq,
      one_mul]
  · simp only [scalar, GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_ne _ hij,
      one_apply_ne hij, zero_mul]
    rfl

lemma scalar_ofFiniteIdele (u : 𝔸ᶠ[F]ˣ) : scalar F (IdeleGroup.ofFiniteIdele (𝓞 F) F u) =
    ofFin F (GeneralLinearGroup.scalar (Fin 2) u) := by
  refine ext_toInf_toFin ?_ ?_
  · rw [toInf_ofFin]
    refine GeneralLinearGroup.ext fun i j ↦ ?_
    rw [toInf_apply, scalar_apply_fst, IdeleGroup.coe_ofFiniteIdele, mul_one]
    rcases eq_or_ne i j with rfl | hij
    · rw [one_apply_eq, map_one, Units.val_one, one_apply_eq]
    · rw [one_apply_ne hij, map_zero, Units.val_one, one_apply_ne hij]
  · rw [toFin_ofFin]
    refine GeneralLinearGroup.ext fun i j ↦ ?_
    rw [toFin_apply, scalar_apply_snd, IdeleGroup.coe_ofFiniteIdele]
    rcases eq_or_ne i j with rfl | hij <;> simp [*]

lemma scalar_ideleOfMixed :
    scalar F (ideleOfMixed F r) = ofInf F (GeneralLinearGroup.scalar (Fin 2) r) := by
  refine ext_toInf_toFin ?_ ?_
  · rw [toInf_ofInf]
    refine GeneralLinearGroup.ext fun i j ↦ ?_
    rw [toInf_apply, scalar_apply_fst, coe_ideleOfMixed]
    rcases eq_or_ne i j with rfl | hij
    · rw [one_apply_eq, one_mul, RingEquiv.apply_symm_apply]
      simp
    · rw [one_apply_ne hij, zero_mul, map_zero]
      simp [hij]
  · rw [toFin_ofInf]
    refine GeneralLinearGroup.ext fun i j ↦ ?_
    rw [toFin_apply, scalar_apply_snd, coe_ideleOfMixed, mul_one]
    rfl

lemma scalar_unitEmbedding (q : Fˣ) : scalar F (IdeleGroup.unitEmbedding (𝓞 F) F q) =
    ofGlobal F (GeneralLinearGroup.scalar (Fin 2) q) :=
  GeneralLinearGroup.ext fun i j ↦ by
    rcases eq_or_ne i j with rfl | hij <;> simp [scalar, ofGlobal, *]

lemma scalar_mul_comm (g : AdelicGL2 F) : scalar F z * g = g * scalar F z :=
  GeneralLinearGroup.scalar_commute _ _

end Scalar

section Real

variable (k : ℤ) {f : ℍ → ℂ} {h : GL (Fin 2) ℝ}

lemma normalizedSlash_smul_of_pos (hh : 0 < (h.det : ℝ)) (c : ℂ) :
    normalizedSlash k (c • f) h = c * normalizedSlash k f h := by
  rw [normalizedSlash, normalizedSlash, ModularForm.smul_slash_of_det_pos k hh, Pi.smul_apply,
    smul_eq_mul, mul_left_comm]

variable (f h) in
lemma classicalFun_mul_scalar_of_pos {s : ℝˣ} (hs : 0 < (s : ℝ)) :
    classicalFun k f (h * GeneralLinearGroup.scalar (Fin 2) s) = classicalFun k f h := by
  have hd : ((GeneralLinearGroup.scalar (Fin 2) s).det : ℝ) = (s : ℝ) ^ 2 := by
    simp
  have hs₀ : ((s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
  rw [classicalFun, classicalFun, posDet_mul_of_pos (by rw [hd]; positivity), normalizedSlash_mul,
    normalizedSlash, normalizedSlash, ModularForm.slash_scalar, hd, abs_of_pos (pow_pos hs 2),
    Real.sqrt_sq hs.le, Pi.smul_apply, smul_eq_mul]
  have hss : ((s : ℝ) : ℂ) ^ (2 - k) * ((s : ℝ) : ℂ) ^ (k - 2) = 1 := by
    rw [← zpow_add₀ hs₀]
    simp
  push_cast
  linear_combination (((Real.sqrt |((posDet h).det : ℝ)| : ℝ) : ℂ) ^ (2 - k) *
    (f ∣[k] posDet h) I) * hss

lemma classicalFun_mapGL_mul_of_mem_gamma0 {N : ℕ} {χ : (ZMod N)ˣ →* ℂˣ}
    (hf : ∀ g : CongruenceSubgroup.Gamma0 N, f ∣[k] SpecialLinearGroup.mapGL ℝ (g : SL(2, ℤ)) =
      (χ ((CongruenceSubgroup.Gamma0Map N).toHomUnits g) : ℂ) • f)
    (g : CongruenceSubgroup.Gamma0 N) :
    classicalFun k f (SpecialLinearGroup.mapGL ℝ (g : SL(2, ℤ)) * h) =
      χ ((CongruenceSubgroup.Gamma0Map N).toHomUnits g) * classicalFun k f h := by
  have hdet (g' : SL(2, ℤ)) : ((SpecialLinearGroup.mapGL ℝ g').det : ℝ) = 1 := by
    simp
  rcases (h.det.ne_zero : (h.det : ℝ) ≠ 0).lt_or_gt with hh | hh
  · have hh' : ((SpecialLinearGroup.mapGL ℝ (g : SL(2, ℤ)) * h).det : ℝ) < 0 := by
      rw [map_mul, Units.val_mul, hdet, one_mul]
      exact hh
    have hJ : J * (SpecialLinearGroup.mapGL ℝ (g : SL(2, ℤ)) * h) =
        SpecialLinearGroup.mapGL ℝ (SpecialLinearGroup.conjJ (g : SL(2, ℤ))) * (J * h) := by
      rw [← SpecialLinearGroup.J_mul_mapGL_mul_J, mul_assoc, mul_assoc, ← mul_assoc J J, J_mul_J,
        one_mul, ← mul_assoc]
    have h₁ : f ∣[k] SpecialLinearGroup.mapGL ℝ (SpecialLinearGroup.conjJ (g : SL(2, ℤ))) =
        (χ ((CongruenceSubgroup.Gamma0Map N).toHomUnits g) : ℂ) • f := by
      rw [← Gamma0Map_conjJ g]
      exact hf ⟨_, conjJ_mem_Gamma0 g.2⟩
    rw [classicalFun, classicalFun, posDet_of_neg hh, posDet_of_neg hh', hJ, normalizedSlash_mul,
      h₁, normalizedSlash_smul_of_pos k (by rw [det_J_mul]; linarith), hdet, abs_one,
      Real.sqrt_one]
    simp
  · rw [classicalFun_of_pos k f (by rw [map_mul, Units.val_mul, hdet, one_mul]; exact hh),
      classicalFun_of_pos k f hh, normalizedSlash_mul, hf g, normalizedSlash_smul_of_pos k hh, hdet,
      abs_one, Real.sqrt_one]
    simp

end Real

section Adelic

variable {N : ℕ} [NeZero N] {u : 𝔸ᶠ[ℚ]ˣ}

lemma val_mem_integralAdeles (hu : u ∈ integralUnits (𝓞 ℚ) ℚ) :
    (u : 𝔸ᶠ[ℚ]) ∈ integralAdeles (𝓞 ℚ) ℚ :=
  FiniteAdeleRing.mem_integralAdeles.mpr fun v ↦
    (FiniteAdeleRing.mem_integralUnits_iff_forall_mem_adicCompletionIntegers.mp hu v).1

variable (N) in
lemma exists_intCast_sub_mem_adelicIdeal {y : 𝔸ᶠ[ℚ]} (hy : y ∈ integralAdeles (𝓞 ℚ) ℚ) :
    ∃ d : ℤ, algebraMap ℚ 𝔸ᶠ[ℚ] d - y ∈ adelicIdeal (Ideal.span {(N : 𝓞 ℚ)}) := by
  have hopen : IsOpen {x : 𝔸ᶠ[ℚ] | x - y ∈ adelicIdeal (Ideal.span {(N : 𝓞 ℚ)})} :=
    (isOpen_adelicIdeal (span_natCast_ne_bot N)).preimage (continuous_id.sub continuous_const)
  have hy₀ : y ∈ {x : 𝔸ᶠ[ℚ] | x - y ∈ adelicIdeal (Ideal.span {(N : 𝓞 ℚ)})} := by
    rw [Set.mem_ofPred_eq, sub_self]
    exact zero_mem _
  rcases (FiniteAdeleRing.denseRange_algebraMap (𝓞 ℚ) ℚ).exists_mem_open hopen ⟨y, hy₀⟩ with
    ⟨q, hq⟩
  rw [Set.mem_ofPred_eq] at hq
  have hq' : algebraMap ℚ 𝔸ᶠ[ℚ] q ∈ integralAdeles (𝓞 ℚ) ℚ := by
    rw [← sub_add_cancel (algebraMap ℚ 𝔸ᶠ[ℚ] q) y]
    exact add_mem (mem_integralAdeles_of_mem_adelicIdeal hq) hy
  refine ⟨q.num, ?_⟩
  rw [intCast_num_of_algebraMap_mem hq']
  exact hq

lemma natCast_mem_adelicIdeal :
    algebraMap ℚ 𝔸ᶠ[ℚ] (N : ℚ) ∈ adelicIdeal (Ideal.span {(N : 𝓞 ℚ)}) := by
  rw [← Int.cast_natCast (R := ℚ), algebraMap_intCast_mem_adelicIdeal_iff N, Int.cast_natCast,
    ZMod.natCast_self]

lemma intCast_mem_integralAdeles (d : ℤ) : algebraMap ℚ 𝔸ᶠ[ℚ] (d : ℚ) ∈ integralAdeles (𝓞 ℚ) ℚ :=
  (FiniteAdeleRing.algebraMap_mem_integralAdeles_iff (d : ℚ)).mpr ⟨(d : 𝓞 ℚ), by simp⟩

variable (N) in
lemma exists_natCast_mul_sub_one_mem_adelicIdeal (hu : u ∈ integralUnits (𝓞 ℚ) ℚ) :
    ∃ a : ℕ, 0 < a ∧ IsUnit (a : ZMod N) ∧
      algebraMap ℚ 𝔸ᶠ[ℚ] (a : ℚ) * u - 1 ∈ adelicIdeal (Ideal.span {(N : 𝓞 ℚ)}) := by
  have hu₁ : (u : 𝔸ᶠ[ℚ]) ∈ integralAdeles (𝓞 ℚ) ℚ := val_mem_integralAdeles hu
  rcases exists_intCast_sub_mem_adelicIdeal N (val_mem_integralAdeles (inv_mem hu)) with ⟨d, hd⟩
  rcases exists_intCast_sub_mem_adelicIdeal N hu₁ with ⟨e, he⟩
  have hdu : algebraMap ℚ 𝔸ᶠ[ℚ] (d : ℚ) * u - 1 ∈ adelicIdeal (Ideal.span {(N : 𝓞 ℚ)}) := by
    rw [← Units.inv_mul u, ← sub_mul]
    exact mul_mem_adelicIdeal hd hu₁
  have hde : algebraMap ℚ 𝔸ᶠ[ℚ] ((d * e : ℤ) : ℚ) - 1 ∈ adelicIdeal (Ideal.span {(N : 𝓞 ℚ)}) := by
    have he' : algebraMap ℚ 𝔸ᶠ[ℚ] ((d * e : ℤ) : ℚ) - 1 = algebraMap ℚ 𝔸ᶠ[ℚ] (d : ℚ) *
        (algebraMap ℚ 𝔸ᶠ[ℚ] (e : ℚ) - u) + (algebraMap ℚ 𝔸ᶠ[ℚ] (d : ℚ) * u - 1) := by
      rw [Int.cast_mul, map_mul]
      ring1
    rw [he']
    exact add_mem (mul_mem_adelicIdeal' (intCast_mem_integralAdeles d) he) hdu
  have hunit : IsUnit ((d : ℤ) : ZMod N) := by
    have h : ((d * e : ℤ) : ZMod N) = 1 := (algebraMap_intCast_sub_one_mem_adelicIdeal_iff N).mp hde
    rw [Int.cast_mul] at h
    exact IsUnit.of_mul_eq_one _ h
  have hN : (1 : ℤ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have hd₁ : -d ≤ (d.natAbs : ℤ) := by
    rw [← Int.natAbs_neg]
    exact Int.le_natAbs
  have hpos : 0 < d + N * (d.natAbs + 1) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hN) (by positivity : (0 : ℤ) ≤ d.natAbs + 1)]
  have ha : (((d + N * (d.natAbs + 1)).toNat : ℕ) : ℤ) = d + N * (d.natAbs + 1) :=
    Int.toNat_of_nonneg hpos.le
  refine ⟨(d + N * (d.natAbs + 1)).toNat, by omega, ?_, ?_⟩
  · have h₁ : (((d + N * (d.natAbs + 1)).toNat : ℕ) : ZMod N) = ((d : ℤ) : ZMod N) := by
      rw [← Int.cast_natCast, ha]
      push_cast
      simp
    rw [h₁]
    exact hunit
  · have hD : (((d + N * (d.natAbs + 1)).toNat : ℕ) : ℚ) =
        (d : ℚ) + (N : ℚ) * ((d.natAbs + 1 : ℤ) : ℚ) := by
      rw [← Int.cast_natCast, ha]
      push_cast
      ring1
    have h₁ : algebraMap ℚ 𝔸ᶠ[ℚ] (((d + N * (d.natAbs + 1)).toNat : ℕ) : ℚ) * u - 1 =
        (algebraMap ℚ 𝔸ᶠ[ℚ] (d : ℚ) * u - 1) + algebraMap ℚ 𝔸ᶠ[ℚ] (N : ℚ) *
          algebraMap ℚ 𝔸ᶠ[ℚ] ((d.natAbs + 1 : ℤ) : ℚ) * u := by
      rw [hD, map_add, map_mul]
      ring1
    rw [h₁]
    exact add_mem hdu (mul_mem_adelicIdeal (mul_mem_adelicIdeal natCast_mem_adelicIdeal
      (intCast_mem_integralAdeles _)) hu₁)

lemma map_mapGL_mem_integralGL (g : SL(2, ℤ)) :
    GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) (SpecialLinearGroup.mapGL ℚ g) ∈ integralGL ℚ :=
  fun i j ↦ ⟨map_mapGL_apply_mem i j, by
    rw [← map_inv, ← map_inv]
    exact map_mapGL_apply_mem i j⟩

lemma scalar_mem_integralGL (hu : u ∈ integralUnits (𝓞 ℚ) ℚ) :
    GeneralLinearGroup.scalar (Fin 2) u ∈ integralGL ℚ := by
  refine fun i j ↦ ⟨?_, ?_⟩
  · rw [GeneralLinearGroup.coe_scalar, scalar_apply]
    rcases eq_or_ne i j with rfl | hij
    · rw [diagonal_apply_eq]
      exact val_mem_integralAdeles hu
    · rw [diagonal_apply_ne _ hij]
      exact zero_mem _
  · rw [← map_inv, GeneralLinearGroup.coe_scalar, scalar_apply]
    rcases eq_or_ne i j with rfl | hij
    · rw [diagonal_apply_eq]
      exact val_mem_integralAdeles (inv_mem hu)
    · rw [diagonal_apply_ne _ hij]
      exact zero_mem _

lemma adelicLift_scalar_ofFiniteIdele_mul {k : ℤ} {f : ℍ → ℂ}
    (hf : ∀ g ∈ CongruenceSubgroup.Gamma1 N, f ∣[k] SpecialLinearGroup.mapGL ℝ g = f)
    {χ : (ZMod N)ˣ →* ℂˣ}
    (hχ : ∀ g : CongruenceSubgroup.Gamma0 N, f ∣[k] SpecialLinearGroup.mapGL ℝ (g : SL(2, ℤ)) =
      (χ ((CongruenceSubgroup.Gamma0Map N).toHomUnits g) : ℂ) • f) (hu : u ∈ integralUnits (𝓞 ℚ) ℚ)
    {a : ℕ} (haN : IsUnit (a : ZMod N))
    (ha : algebraMap ℚ 𝔸ᶠ[ℚ] (a : ℚ) * u - 1 ∈ adelicIdeal (Ideal.span {(N : 𝓞 ℚ)}))
    (g : AdelicGL2 ℚ) : adelicLift N k f (scalar ℚ (IdeleGroup.ofFiniteIdele (𝓞 ℚ) ℚ u) * g) =
      (χ haN.unit : ℂ) * adelicLift N k f g := by
  rcases CongruenceSubgroup.Gamma0Map_toHomUnits_surjective haN.unit with ⟨g₀, hg₀⟩
  have hu₁ : (u : 𝔸ᶠ[ℚ]) ∈ integralAdeles (𝓞 ℚ) ℚ := val_mem_integralAdeles hu
  have hg₁₀ : (((g₀ : SL(2, ℤ)) 1 0 : ℤ) : ZMod N) = 0 :=
    CongruenceSubgroup.Gamma0_mem.mp g₀.2
  have hg₁₁ : (((g₀ : SL(2, ℤ)) 1 1 - a : ℤ) : ZMod N) = 0 := by
    have h : (((CongruenceSubgroup.Gamma0Map N).toHomUnits g₀ : (ZMod N)ˣ) : ZMod N) =
        (haN.unit : ZMod N) :=
      congrArg Units.val hg₀
    rw [MonoidHom.coe_toHomUnits, IsUnit.unit_spec] at h
    rw [Int.cast_sub, Int.cast_natCast, sub_eq_zero]
    exact h
  have hw : GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) (SpecialLinearGroup.mapGL ℚ
      (g₀ : SL(2, ℤ))) * GeneralLinearGroup.scalar (Fin 2) u ∈
        levelOne (Ideal.span {(N : 𝓞 ℚ)}) := by
    refine ⟨mul_mem (map_mapGL_mem_integralGL _) (scalar_mem_integralGL hu), ?_, ?_⟩
    · simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply, mul_diagonal]
      exact mul_mem_adelicIdeal ((algebraMap_intCast_mem_adelicIdeal_iff N).mpr hg₁₀) hu₁
    · have he : algebraMap ℚ 𝔸ᶠ[ℚ] (((g₀ : SL(2, ℤ)) 1 1 : ℤ) : ℚ) * u - 1 =
          algebraMap ℚ 𝔸ᶠ[ℚ] ((((g₀ : SL(2, ℤ)) 1 1 - a : ℤ)) : ℚ) * u +
            (algebraMap ℚ 𝔸ᶠ[ℚ] (a : ℚ) * u - 1) := by
        rw [Int.cast_sub, Int.cast_natCast, map_sub]
        ring1
      simp only [Units.val_mul, GeneralLinearGroup.coe_scalar, scalar_apply, mul_diagonal,
        map_mapGL_apply]
      rw [he]
      exact add_mem (mul_mem_adelicIdeal ((algebraMap_intCast_mem_adelicIdeal_iff N).mpr hg₁₁) hu₁)
        ha
  rcases exists_eq_ofGlobal_mul_ofInf_mul_ofFin N g with ⟨γ, x, u₀, hu₀, rfl⟩
  have he : scalar ℚ (IdeleGroup.ofFiniteIdele (𝓞 ℚ) ℚ u) * (ofGlobal ℚ γ * ofInf ℚ x *
      ofFin ℚ u₀) = ofGlobal ℚ (γ * (SpecialLinearGroup.mapGL ℚ (g₀ : SL(2, ℤ)))⁻¹) *
        ofInf ℚ (toInf ℚ (ofGlobal ℚ (SpecialLinearGroup.mapGL ℚ (g₀ : SL(2, ℤ)))) * x) *
          ofFin ℚ (GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) (SpecialLinearGroup.mapGL ℚ
            (g₀ : SL(2, ℤ))) * GeneralLinearGroup.scalar (Fin 2) u * u₀) := by
    rw [scalar_ofFiniteIdele]
    refine ext_toInf_toFin ?_ ?_
    · simp
    · simp only [map_mul, map_inv, toFin_ofGlobal, toFin_ofInf, toFin_ofFin, one_mul, mul_assoc,
        inv_mul_cancel_left]
      rw [← mul_assoc, GeneralLinearGroup.scalar_commute u
        (GeneralLinearGroup.map (algebraMap ℚ 𝔸ᶠ[ℚ]) γ), mul_assoc]
  rw [he, adelicLift_apply hf _ _ (mul_mem hw hu₀), adelicLift_apply hf _ _ hu₀, map_mul,
    toInf_ofGlobal, ratInfEquiv_map_mixedEmbedding, SpecialLinearGroup.map_mapGL,
    classicalFun_mapGL_mul_of_mem_gamma0 k hχ g₀, hg₀]

end Adelic

section CentralCharacter

variable {N : ℕ} [NeZero N] {k : ℤ}
  (f : CuspForm ((CongruenceSubgroup.Gamma1 N).map (SpecialLinearGroup.mapGL ℝ)) k)
  {χ : (ZMod N)ˣ →* ℂˣ}

lemma neg_one_mem_integralUnits : (-1 : 𝔸ᶠ[ℚ]ˣ) ∈ integralUnits (𝓞 ℚ) ℚ := fun v ↦ by
  have h : ((-1 : 𝔸ᶠ[ℚ]ˣ) : 𝔸ᶠ[ℚ]) v = -1 := rfl
  rw [h, Valuation.map_neg, map_one]

lemma unitEmbedding_neg_one : IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ (-1) = -1 :=
  Units.ext (by simp)

lemma neg_one_mul_ofFiniteIdele_neg_one :
    -1 * IdeleGroup.ofFiniteIdele (𝓞 ℚ) ℚ (-1) = ideleOfMixed ℚ (-1) := by
  refine Units.ext (Prod.ext ?_ ?_)
  · rw [coe_ideleOfMixed, Units.val_neg, Units.val_one, map_neg, map_one]
    exact mul_one _
  · rw [coe_ideleOfMixed]
    exact (neg_one_mul _).trans (neg_neg _)

lemma ideleOfMixed_eq_unitEmbedding_mul (r : (mixedSpace ℚ)ˣ) :
    ideleOfMixed ℚ r = IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ (-1) *
      IdeleGroup.ofFiniteIdele (𝓞 ℚ) ℚ (-1) * ideleOfMixed ℚ (-r) := by
  rw [unitEmbedding_neg_one, neg_one_mul_ofFiniteIdele_neg_one, ← map_mul, neg_one_mul, neg_neg]

/-- **The central character of the adelic lift** of a cusp form `f` of nebentypus `χ` is the Hecke
character `ω` of `χ` (Tau Ceti's `HeckeCharacter.ofDirichletCharacter`): `φ_f(z g) = ω(z) φ_f(g)`
for every idele `z`. -/
lemma adelicLift_scalar_mul (hχ : f ∈ cuspFormCharSpace k χ) (z : IdeleGroup (𝓞 ℚ) ℚ)
    (g : AdelicGL2 ℚ) : adelicLift N k f (scalar ℚ z * g) =
      (HeckeCharacter.ofDirichletCharacter N (NeZero.ne N) (MulChar.ofUnitHom χ)
        (QuotientGroup.mk z) : ℂ) * adelicLift N k f g := by
  have hf : ∀ g ∈ CongruenceSubgroup.Gamma1 N, ⇑f ∣[k] SpecialLinearGroup.mapGL ℝ g = ⇑f :=
    slash_mapGL_eq_of_mem_gamma1 f
  let ω : HeckeCharacter ℚ := HeckeCharacter.ofDirichletCharacter N (NeZero.ne N)
    (MulChar.ofUnitHom χ)
  let S : Subgroup (IdeleGroup (𝓞 ℚ) ℚ) :=
    { carrier := {z | ∀ g, adelicLift N k f (scalar ℚ z * g) =
        (ω (QuotientGroup.mk z) : ℂ) * adelicLift N k f g}
      mul_mem' := fun {a b} ha hb g ↦ by
        rw [map_mul, mul_assoc, ha, hb, QuotientGroup.mk_mul, map_mul, Units.val_mul, mul_assoc]
      one_mem' := fun g ↦ by simp
      inv_mem' := fun {a} ha g ↦ by
        have h₁ : adelicLift N k f (scalar ℚ a * (scalar ℚ a⁻¹ * g)) =
            (ω (QuotientGroup.mk a) : ℂ) * adelicLift N k f (scalar ℚ a⁻¹ * g) :=
          ha _
        rw [← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul] at h₁
        rw [h₁, ← mul_assoc, ← Units.val_mul, ← map_mul, QuotientGroup.mk_inv, inv_mul_cancel,
          map_one, Units.val_one, one_mul] }
  have hS₁ (q : ℚˣ) : IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ q ∈ S := fun g ↦ by
    rw [scalar_unitEmbedding, adelicLift_ofGlobal_mul hf,
      (QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_range.mpr ⟨q, rfl⟩), map_one, Units.val_one,
      one_mul]
  have hS₂ (r : (mixedSpace ℚ)ˣ) (hr : 0 < ratMixedEquiv (r : mixedSpace ℚ)) :
      ideleOfMixed ℚ r ∈ S := fun g ↦ by
    rw [ofDirichletCharacter_ideleOfMixed _ hr, Units.val_one, one_mul, scalar_mul_comm,
      scalar_ideleOfMixed]
    rcases exists_adelicLift_mul_ofInf N hf g with ⟨h₀, -, he⟩
    have h₁ : adelicLift N k f g = classicalFun k f h₀ := by
      simpa using he 1
    have hs : ratInfEquiv (GeneralLinearGroup.scalar (Fin 2) r) =
        GeneralLinearGroup.scalar (Fin 2) (Units.map ratMixedEquiv.toMonoidHom r) := by
      ext i j
      rcases eq_or_ne i j with rfl | hij
      · simp [ratInfEquiv_apply]
      · simp [ratInfEquiv_apply, hij]
    rw [he, h₁, hs, classicalFun_mul_scalar_of_pos k _ _ hr]
  have hS₃ (u : 𝔸ᶠ[ℚ]ˣ) (hu : u ∈ integralUnits (𝓞 ℚ) ℚ) : IdeleGroup.ofFiniteIdele (𝓞 ℚ) ℚ u ∈ S :=
    fun g ↦ by
      rcases exists_natCast_mul_sub_one_mem_adelicIdeal N hu with ⟨a, ha₀, haN, ha⟩
      rw [adelicLift_scalar_ofFiniteIdele_mul hf
        ((mem_cuspFormCharSpace_iff_nebentypus k χ f).mp hχ) hu haN ha,
        ofDirichletCharacter_ofFiniteIdele _ hu ha₀ ha, ← MulChar.ofUnitHom_coe, IsUnit.unit_spec]
  have hS₄ (r : (mixedSpace ℚ)ˣ) : ideleOfMixed ℚ r ∈ S := by
    rcases ((RingEquiv.map_ne_zero_iff ratMixedEquiv).mpr r.ne_zero).lt_or_gt with hr | hr
    · have hr' : 0 < ratMixedEquiv ((-r : (mixedSpace ℚ)ˣ) : mixedSpace ℚ) := by
        rw [Units.val_neg, map_neg]
        exact neg_pos.mpr hr
      rw [ideleOfMixed_eq_unitEmbedding_mul]
      exact S.mul_mem (S.mul_mem (hS₁ (-1)) (hS₃ (-1) neg_one_mem_integralUnits)) (hS₂ (-r) hr')
    · exact hS₂ r hr
  have hS₅ (u : 𝔸ᶠ[ℚ]ˣ) : IdeleGroup.ofFiniteIdele (𝓞 ℚ) ℚ u ∈ S := by
    rcases ClassGroup.mk_eq_one_iff_exists.mp (Subsingleton.elim (ClassGroup.mk ℚ
      (toFractionalIdeal u)) 1) with ⟨q, hq⟩
    have hw : (FiniteAdeleRing.unitEmbedding (𝓞 ℚ) ℚ q)⁻¹ * u ∈ integralUnits (𝓞 ℚ) ℚ := by
      rw [← FiniteAdeleRing.ker_toFractionalIdeal, MonoidHom.mem_ker, map_mul, map_inv,
        FiniteAdeleRing.toFractionalIdeal_unitEmbedding, hq, inv_mul_cancel]
    have hq₁ : IdeleGroup.ofFiniteIdele (𝓞 ℚ) ℚ (FiniteAdeleRing.unitEmbedding (𝓞 ℚ) ℚ q) ∈ S := by
      rw [← IdeleGroup.toFiniteIdele_unitEmbedding,
        eq_inv_mul_of_mul_eq (ideleOfMixed_mul_ofFiniteIdele _)]
      exact S.mul_mem (S.inv_mem (hS₄ _)) (hS₁ q)
    rw [← mul_inv_cancel_left (FiniteAdeleRing.unitEmbedding (𝓞 ℚ) ℚ q) u, map_mul]
    exact S.mul_mem hq₁ (hS₃ _ hw)
  rw [← ideleOfMixed_mul_ofFiniteIdele z]
  exact S.mul_mem (hS₄ _) (hS₅ _) g

/-- **The adelic lift of a cusp form** `f` of weight `k` and nebentypus `χ` on `Γ₁(N)` is an
automorphic form on `GL₂(𝔸_ℚ)`, of central character the Hecke character of `χ`. -/
lemma isAutomorphicForm_adelicLift (hχ : f ∈ cuspFormCharSpace k χ) :
    IsAutomorphicForm (HeckeCharacter.ofDirichletCharacter N (NeZero.ne N) (MulChar.ofUnitHom χ))
      (adelicLift N k f) where
  left_invariant := adelicLift_ofGlobal_mul (slash_mapGL_eq_of_mem_gamma1 f)
  central := adelicLift_scalar_mul f hχ
  smooth := isSmoothAtInfinity_adelicLift_cuspForm f
  exists_openSubgroup := exists_openSubgroup_adelicLift f
  kFinite := isKFinite_adelicLift (slash_mapGL_eq_of_mem_gamma1 f)
  casimirFinite :=
    isCasimirFinite_adelicLift (CuspFormClass.holo f) (slash_mapGL_eq_of_mem_gamma1 f)
  moderateGrowth := hasModerateGrowth_adelicLift f

end CentralCharacter

end AdelicGL2
