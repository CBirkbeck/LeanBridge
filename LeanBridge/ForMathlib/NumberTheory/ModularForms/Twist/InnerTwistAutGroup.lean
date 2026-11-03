import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.InnerTwistRibet
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.SelfTwistConductor
import TauCeti.NumberTheory.ModularForms.LevelOne.DiscriminantEigenform

/-!
# The group of inner twists of a newform

The LMFDB states (LMFDB `cmf.inner_twist_group`) that the pairs `(χ, σ)` giving rise to an inner
twist of a newform `f`, with `χ` a primitive Dirichlet character and `σ` a `ℚ`-automorphism of the
coefficient field `K` of `f`, form a group `G` under `(χ, σ) (χ', σ') = (χ σ(χ'), σ σ')`; that
`(χ, σ) ↦ σ` is a homomorphism `G → Aut_ℚ(K)` with kernel the self twists and abelian image; and
that `(χ, σ) ↦ χ` is injective, and a homomorphism on the self twists. This file proves all of this,
with no hypothesis on `f`, and that `G` is finite. The group `G` is in fact abelian, which the LMFDB
does not state (E. Studnia, arXiv:2401.17769v4, Proposition 1.4).

The inner twist pairs `(χ, σ)`, with `σ` an automorphism of `ℂ`, form a group
(`LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.InnerTwistGroup`). By the theorems of Ribet
and Momose (`LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.InnerTwistRibet`), `σ` preserves
`K` and `χ` has values in `K`, so that `χ σ(χ')` depends only on the restriction of `σ` to `K`, and
the map `(χ, σ) ↦ (χ, σ|_K)` to `G` induces the group law on `G`; it is surjective, as automorphisms
of `K` extend to `ℂ`. The group `G` is commutative by the symmetry of `χ σ(χ')` in the two pairs. It
is finite as `Aut_ℚ(K)` is finite and a newform has finitely many self twists
(`HeckeRing.GL2.Newform.finite_setOf_hasSelfTwist`).

The elements `(χ, τ)` of `G` are in bijection with the inner twists `(χ, g)` of `f` of
`HeckeRing.GL2.Newform.innerTwists`, for `g` the conjugate of `f` by `τ`. So there are finitely many
inner twists, and the inner twist count (LMFDB `cmf.inner_twist_count`) is the order of `G`.

The LMFDB also states that `(χ, σ) ↦ χ` is not a homomorphism in general.
`HeckeRing.GL2.Newform.innerTwistGroup_mul_fst_eq_primitive_mul_iff` says exactly when the law is
the product of characters, namely when `σ` fixes the values of `χ'`. So it fails as soon as the
nebentypus is not quadratic, as complex conjugation gives an inner twist
(`HeckeRing.GL2.Newform.not_forall_innerTwistGroup_mul_fst_eq_primitive_mul`), and there are such
newforms (`HeckeRing.GL2.Newform.exists_newform_χ_sq_ne_one`).

## Main definitions

* `HeckeRing.GL2.Newform.innerTwistGroup`: the group of inner twists of `f`, as a set of pairs
  `(χ, τ)` with `τ` an automorphism of the coefficient field (LMFDB `cmf.inner_twist_group`).
* The instance `CommGroup f.innerTwistGroup`: its group structure.
* `HeckeRing.GL2.Newform.innerTwistPairsToAut`: the restriction `(χ, σ) ↦ σ|_K`.
* `HeckeRing.GL2.Newform.innerTwistPairsToGroup`, `HeckeRing.GL2.Newform.innerTwistPairsToGroupHom`:
  the map `(χ, σ) ↦ (χ, σ|_K)` from the inner twist pairs to the group of inner twists.
* `HeckeRing.GL2.Newform.coefficientFieldAutLift`, `HeckeRing.GL2.Newform.innerTwistGroupToPairs`: a
  chosen extension to `ℂ` of an automorphism of the coefficient field, and the lift to inner twist
  pairs that it gives.
* `HeckeRing.GL2.Newform.innerTwistGroupToAut`: the projection `(χ, τ) ↦ τ`, a homomorphism.
* `HeckeRing.GL2.Newform.innerTwistGroupToInnerTwists`: the map `(χ, τ) ↦ (χ, τ(f))` to the inner
  twists of `f`.

## Main results

* `HeckeRing.GL2.Newform.innerTwistGroup_mul_fst`: the law is `(χ, τ) (χ', τ') = (χ τ(χ'), τ τ')`.
* `HeckeRing.GL2.Newform.mem_ker_innerTwistGroupToAut_iff`: the kernel of the projection to
  `Aut_ℚ(K)` consists of the self twists.
* `HeckeRing.GL2.Newform.isMulCommutative_range_innerTwistGroupToAut`: its image is abelian.
* `HeckeRing.GL2.Newform.innerTwistGroup_fst_injective`: the projection to `χ` is injective.
* `HeckeRing.GL2.Newform.innerTwistGroup_mul_fst_of_snd_eq_one`: on the self twists, it is
  multiplicative.
* `HeckeRing.GL2.Newform.innerTwistGroup_mul_fst_eq_primitive_mul_iff`: the law is the product of
  characters exactly when `τ` fixes the values of `χ'`.
* `HeckeRing.GL2.Newform.not_forall_innerTwistGroup_mul_fst_eq_primitive_mul`: the projection to `χ`
  is not a homomorphism when the nebentypus is not quadratic.
* `HeckeRing.GL2.Newform.exists_newform_χ_sq_ne_one`: there is a newform whose nebentypus is not
  quadratic.
* The instance `Finite f.innerTwistGroup`: the group of inner twists is finite.
* `HeckeRing.GL2.Newform.mk_mem_innerTwists_iff_exists_mem_innerTwistGroup`: Ribet's description of
  inner twists, through automorphisms of the coefficient field.
* `HeckeRing.GL2.Newform.coefficientField_eq_of_mk_mem_innerTwists`: an inner twist has the same
  coefficient field.
* `HeckeRing.GL2.Newform.eq_of_mk_mem_innerTwists`: an inner twist is determined by its character.
* `HeckeRing.GL2.Newform.finite_innerTwists`: a newform has finitely many inner twists.
* `HeckeRing.GL2.Newform.innerTwistCount_eq_natCard`: the inner twist count is the order of the
  group of inner twists.
-/

open UpperHalfPlane TauCeti DirichletCharacter

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} {f : Newform N k} {p : ℕ}

variable (f) in
/-- The **group of inner twists** of the newform `f` (LMFDB `cmf.inner_twist_group`), as a set: the
pairs `(χ, τ)` of a primitive Dirichlet character `χ` of positive modulus and a `ℚ`-automorphism `τ`
of the coefficient field `K` of `f` with `τ(a_p(f)) = χ(p) a_p(f)` for all but finitely many primes
`p`. Its group structure is the instance `CommGroup f.innerTwistGroup`. -/
def innerTwistGroup : Set ((Σ M : ℕ+, DirichletCharacter ℂ M) × Gal(CoefficientField f/ℚ)) :=
  {t | t.1.2.IsPrimitive ∧ ∀ᶠ p in Filter.cofinite, p.Prime →
    ((t.2 (f.orbitQExpansion.coeff p) : CoefficientField f) : ℂ) =
      t.1.2 p * (qExpansion 1 f.toCuspForm).coeff p}

variable (f) in
/-- The restriction `σ|_K` to the coefficient field `K` of `f` of the automorphism `σ` of an inner
twist pair `(χ, σ)` of `f`, which exists as `σ(K) = K` (`map_coefficientField_eq`). -/
noncomputable def innerTwistPairsToAut : f.innerTwistPairs →* Gal(CoefficientField f/ℚ) where
  toFun x := ((CoefficientField f).equivMap (x.1.2 : ℂ →ₐ[ℚ] ℂ)).trans
    (IntermediateField.equivOfEq (map_coefficientField_eq x.2))
  map_one' := AlgEquiv.ext fun _ ↦ Subtype.ext rfl
  map_mul' _ _ := AlgEquiv.ext fun _ ↦ Subtype.ext rfl

lemma coe_innerTwistPairsToAut_apply (x : f.innerTwistPairs) (a : CoefficientField f) :
    ((innerTwistPairsToAut f x a : CoefficientField f) : ℂ) = x.1.2 a :=
  rfl

variable (f) in
/-- The map `(χ, σ) ↦ (χ, σ|_K)` from the inner twist pairs of `f`, with `σ ∈ Gal(ℂ/ℚ)`, to its
group of inner twists, with `σ|_K ∈ Aut_ℚ(K)`. -/
noncomputable def innerTwistPairsToGroup (x : f.innerTwistPairs) : f.innerTwistGroup :=
  ⟨(x.1.1, innerTwistPairsToAut f x), x.2.1, x.2.2.mono fun p hp hp' ↦ by
    rw [coe_innerTwistPairsToAut_apply, coe_coeff_orbitQExpansion]
    exact hp hp'⟩

/-- An automorphism of `ℂ` extending the automorphism `τ` of the coefficient field of `f`, chosen
with `Classical.choose`. -/
noncomputable def coefficientFieldAutLift (τ : Gal(CoefficientField f/ℚ)) : Gal(ℂ/ℚ) :=
  (IntermediateField.exists_algEquiv_apply_eq_of_countable
    ((CoefficientField f).val.comp τ.toAlgHom)).choose

lemma coefficientFieldAutLift_apply (τ : Gal(CoefficientField f/ℚ)) (a : CoefficientField f) :
    coefficientFieldAutLift τ a = τ a :=
  (IntermediateField.exists_algEquiv_apply_eq_of_countable
    ((CoefficientField f).val.comp τ.toAlgHom)).choose_spec a

variable (f) in
/-- The inner twist pair `(χ, σ)` lifting the element `(χ, τ)` of the group of inner twists of `f`,
through the chosen extension `σ` of `τ`. -/
noncomputable def innerTwistGroupToPairs (t : f.innerTwistGroup) : f.innerTwistPairs :=
  ⟨(t.1.1, coefficientFieldAutLift t.1.2), t.2.1, t.2.2.mono fun p hp hp' ↦ by
    have h : coefficientFieldAutLift t.1.2 ((f.orbitQExpansion.coeff p : CoefficientField f) : ℂ) =
        t.1.2 (f.orbitQExpansion.coeff p) := coefficientFieldAutLift_apply t.1.2 _
    rw [coe_coeff_orbitQExpansion] at h
    exact h.trans (hp hp')⟩

lemma innerTwistPairsToGroup_innerTwistGroupToPairs (t : f.innerTwistGroup) :
    innerTwistPairsToGroup f (innerTwistGroupToPairs f t) = t :=
  Subtype.ext <| Prod.ext rfl <| AlgEquiv.ext fun a ↦ Subtype.ext <|
    coefficientFieldAutLift_apply t.1.2 a

variable {x x' y y' : f.innerTwistPairs}

private lemma apply_natCast_eq_of_innerTwistPairsToGroup_eq
    (h : innerTwistPairsToGroup f x = innerTwistPairsToGroup f x') : x.1.1.2 p = x'.1.1.2 p :=
  congrArg (fun t : f.innerTwistGroup ↦ t.1.1.2 p) h

private lemma apply_eq_of_innerTwistPairsToGroup_eq
    (h : innerTwistPairsToGroup f x = innerTwistPairsToGroup f x') {a : ℂ}
    (ha : a ∈ CoefficientField f) : x.1.2 a = x'.1.2 a :=
  congrArg (fun t : f.innerTwistGroup ↦ ((t.1.2 ⟨a, ha⟩ : CoefficientField f) : ℂ)) h

private lemma innerTwistPairsToGroup_mul_congr
    (hx : innerTwistPairsToGroup f x = innerTwistPairsToGroup f x')
    (hy : innerTwistPairsToGroup f y = innerTwistPairsToGroup f y') :
    innerTwistPairsToGroup f (x * y) = innerTwistPairsToGroup f (x' * y') := by
  have hfst : (x * y).1.1 = (x' * y').1.1 := by
    refine eq_of_isPrimitive_of_eventually_eq (x * y).2.1 (x' * y').2.1 ?_
    filter_upwards [eventually_prime_coprime (mul_ne_zero x.1.1.1.ne_zero y.1.1.1.ne_zero),
      eventually_prime_coprime (mul_ne_zero x'.1.1.1.ne_zero y'.1.1.1.ne_zero)] with p hp hp' hpp
    have h₁ : (x * y).1.1.2 p = x.1.1.2 p * x.1.2 (y.1.1.2 p) := innerTwistMul_apply (hp hpp)
    have h₂ : (x' * y').1.1.2 p = x'.1.1.2 p * x'.1.2 (y'.1.1.2 p) := innerTwistMul_apply (hp' hpp)
    rw [h₁, h₂, apply_natCast_eq_of_innerTwistPairsToGroup_eq hx,
      ← apply_natCast_eq_of_innerTwistPairsToGroup_eq hy,
      apply_eq_of_innerTwistPairsToGroup_eq hx (apply_mem_coefficientField y.2 _)]
  have hxτ : innerTwistPairsToAut f x = innerTwistPairsToAut f x' :=
    congrArg (fun t : f.innerTwistGroup ↦ t.1.2) hx
  have hyτ : innerTwistPairsToAut f y = innerTwistPairsToAut f y' :=
    congrArg (fun t : f.innerTwistGroup ↦ t.1.2) hy
  have hsnd : innerTwistPairsToAut f (x * y) = innerTwistPairsToAut f (x' * y') := by
    rw [map_mul, map_mul, hxτ, hyτ]
  exact Subtype.ext <| Prod.ext hfst hsnd

private lemma algEquiv_ext_of_coeff {τ τ' : Gal(CoefficientField f/ℚ)}
    (h : ∀ n : ℕ, ((τ (f.orbitQExpansion.coeff n) : CoefficientField f) : ℂ) =
      τ' (f.orbitQExpansion.coeff n)) : τ = τ' := by
  refine AlgEquiv.coe_toAlgHom_injective <|
    IntermediateField.algHom_ext_of_eq_adjoin ℚ (CoefficientField_def f) ?_
  rintro _ ⟨n, rfl⟩
  have hn : f.orbitQExpansion.coeff n = ⟨_, coeff_mem_CoefficientField f n⟩ :=
    Subtype.ext (coe_coeff_orbitQExpansion _)
  exact Subtype.ext (hn ▸ h n)

variable (x y) in
private lemma innerTwistPairsToGroup_mul_comm :
    innerTwistPairsToGroup f (x * y) = innerTwistPairsToGroup f (y * x) := by
  have hfst : (x * y).1.1 = (y * x).1.1 := by
    refine eq_of_isPrimitive_of_eventually_eq (x * y).2.1 (y * x).2.1 ?_
    filter_upwards [eventually_prime_coprime (mul_ne_zero (mul_ne_zero (NeZero.ne N)
      x.1.1.1.ne_zero) y.1.1.1.ne_zero)] with p hp hpp
    have hxy : p.Coprime (x.1.1.1 * y.1.1.1) :=
      (hp hpp).coprime_dvd_right (Dvd.intro_left N (by ring1))
    have h₁ : (x * y).1.1.2 p = x.1.1.2 p * x.1.2 (y.1.1.2 p) := innerTwistMul_apply hxy
    have h₂ : (y * x).1.1.2 p = y.1.1.2 p * y.1.2 (x.1.1.2 p) :=
      innerTwistMul_apply (mul_comm (x.1.1.1 : ℕ) y.1.1.1 ▸ hxy)
    rw [h₁, h₂]
    exact mul_apply_eq_mul_apply_of_mem x.2 y.2 (hp hpp)
  have hsnd : innerTwistPairsToAut f (x * y) = innerTwistPairsToAut f (y * x) :=
    algEquiv_ext_of_coeff fun n ↦ by
      rw [coe_innerTwistPairsToAut_apply, coe_innerTwistPairsToAut_apply,
        coe_coeff_orbitQExpansion]
      exact apply_apply_coeff_comm x.2 y.2 n
  exact Subtype.ext <| Prod.ext hfst hsnd

noncomputable instance : CommGroup f.innerTwistGroup where
  mul s t := innerTwistPairsToGroup f (innerTwistGroupToPairs f s * innerTwistGroupToPairs f t)
  one := innerTwistPairsToGroup f 1
  inv t := innerTwistPairsToGroup f (innerTwistGroupToPairs f t)⁻¹
  mul_assoc _ _ _ := (innerTwistPairsToGroup_mul_congr
    (innerTwistPairsToGroup_innerTwistGroupToPairs _) rfl).trans <|
      (congrArg _ (mul_assoc _ _ _)).trans <| innerTwistPairsToGroup_mul_congr rfl
        (innerTwistPairsToGroup_innerTwistGroupToPairs _).symm
  one_mul t := (innerTwistPairsToGroup_mul_congr
    (innerTwistPairsToGroup_innerTwistGroupToPairs _) rfl).trans <|
      (congrArg _ (one_mul _)).trans (innerTwistPairsToGroup_innerTwistGroupToPairs t)
  mul_one t := (innerTwistPairsToGroup_mul_congr rfl
    (innerTwistPairsToGroup_innerTwistGroupToPairs _)).trans <|
      (congrArg _ (mul_one _)).trans (innerTwistPairsToGroup_innerTwistGroupToPairs t)
  inv_mul_cancel _ := (innerTwistPairsToGroup_mul_congr
    (innerTwistPairsToGroup_innerTwistGroupToPairs _) rfl).trans <| congrArg _ (inv_mul_cancel _)
  mul_comm _ _ := innerTwistPairsToGroup_mul_comm _ _

variable (f) in
/-- The map `(χ, σ) ↦ (χ, σ|_K)` from the inner twist pairs of `f` to its group of inner twists, a
surjective homomorphism. -/
noncomputable def innerTwistPairsToGroupHom : f.innerTwistPairs →* f.innerTwistGroup where
  toFun := innerTwistPairsToGroup f
  map_one' := rfl
  map_mul' _ _ := innerTwistPairsToGroup_mul_congr
    (innerTwistPairsToGroup_innerTwistGroupToPairs _).symm
    (innerTwistPairsToGroup_innerTwistGroupToPairs _).symm

variable (f) in
lemma innerTwistPairsToGroupHom_surjective : Function.Surjective (innerTwistPairsToGroupHom f) :=
  fun t ↦ ⟨innerTwistGroupToPairs f t, innerTwistPairsToGroup_innerTwistGroupToPairs t⟩

variable (f) in
/-- The **projection** `(χ, τ) ↦ τ` of the group of inner twists of `f` to the automorphism group
`Aut_ℚ(K)` of its coefficient field `K` (LMFDB `cmf.inner_twist_group`), a homomorphism. -/
noncomputable def innerTwistGroupToAut : f.innerTwistGroup →* Gal(CoefficientField f/ℚ) where
  toFun t := t.1.2
  map_one' := map_one (innerTwistPairsToAut f)
  map_mul' s t := (map_mul (innerTwistPairsToAut f) _ _).trans <| congrArg₂ (· * ·)
    (congrArg (fun t : f.innerTwistGroup ↦ t.1.2) (innerTwistPairsToGroup_innerTwistGroupToPairs s))
    (congrArg (fun t : f.innerTwistGroup ↦ t.1.2) (innerTwistPairsToGroup_innerTwistGroupToPairs t))

variable {s t : f.innerTwistGroup} {χ : Σ M : ℕ+, DirichletCharacter ℂ M}

variable (t) in
lemma innerTwistGroupToAut_apply : innerTwistGroupToAut f t = t.1.2 :=
  rfl

lemma innerTwistGroup_one_coe : (1 : f.innerTwistGroup).1 = (⟨1, 1⟩, 1) :=
  Prod.ext rfl (map_one (innerTwistPairsToAut f))

lemma innerTwistGroup_mul_snd : (s * t).1.2 = s.1.2 * t.1.2 :=
  map_mul (innerTwistGroupToAut f) s t

lemma mk_one_mem_innerTwistGroup_iff : (χ, 1) ∈ f.innerTwistGroup ↔ f.HasSelfTwist χ.2 := by
  refine ⟨fun h ↦ ⟨χ.1.ne_zero, h.1, h.2.mono fun p hp hp' ↦ ?_⟩,
    fun h ↦ ⟨h.2.1, h.2.2.mono fun p hp hp' ↦ ?_⟩⟩
  · have h₁ : (((1 : Gal(CoefficientField f/ℚ)) (f.orbitQExpansion.coeff p) :
        CoefficientField f) : ℂ) = χ.2 p * (qExpansion 1 f.toCuspForm).coeff p := hp hp'
    rw [AlgEquiv.one_apply, coe_coeff_orbitQExpansion] at h₁
    exact h₁
  · rw [AlgEquiv.one_apply, coe_coeff_orbitQExpansion]
    exact hp hp'

/-- **The kernel of the projection to `Aut_ℚ(K)` consists of the self twists** `(χ, 1)` of `f`
(LMFDB `cmf.inner_twist_group`). -/
lemma mem_ker_innerTwistGroupToAut_iff :
    t ∈ (innerTwistGroupToAut f).ker ↔ ∃ χ, f.HasSelfTwist χ.2 ∧ t.1 = (χ, 1) := by
  refine ⟨fun ht ↦ ⟨t.1.1, ?_, Prod.ext rfl (MonoidHom.mem_ker.mp ht)⟩, ?_⟩
  · refine mk_one_mem_innerTwistGroup_iff.mp ?_
    rw [← MonoidHom.mem_ker.mp ht]
    exact t.2
  · rintro ⟨χ, -, ht⟩
    exact MonoidHom.mem_ker.mpr (congrArg Prod.snd ht)

/-- **The projection `(χ, τ) ↦ χ` is injective** (LMFDB `cmf.inner_twist_group`, `cmf.inner_twist`):
an inner twist of `f` is determined by its primitive character. -/
lemma innerTwistGroup_fst_injective : Function.Injective fun t : f.innerTwistGroup ↦ t.1.1 := by
  intro s t hst
  have hlift (u : f.innerTwistGroup) (n : ℕ) :
      ((u.1.2 (f.orbitQExpansion.coeff n) : CoefficientField f) : ℂ) =
        (innerTwistGroupToPairs f u).1.2 ((qExpansion 1 f.toCuspForm).coeff n) := by
    rw [← coe_coeff_orbitQExpansion]
    exact (coefficientFieldAutLift_apply u.1.2 _).symm
  refine Subtype.ext <| Prod.ext hst <| algEquiv_ext_of_coeff fun n ↦ ?_
  rw [hlift, hlift]
  exact apply_coeff_eq_of_fst_eq (innerTwistGroupToPairs f s).2 (innerTwistGroupToPairs f t).2 hst n

/-- **The law of the group of inner twists** (LMFDB `cmf.inner_twist_group`):
`(χ, τ) (χ', τ') = (χ τ(χ'), τ τ')`, where `χ τ(χ')` is the primitive character inducing the product
of `χ` and of `χ'` followed by `τ`, computed with any extension `σ` of `τ` to `ℂ`, as `χ'` has
values in the coefficient field. The second component is `innerTwistGroup_mul_snd`. -/
lemma innerTwistGroup_mul_fst {σ : Gal(ℂ/ℚ)} (hσ : ∀ a : CoefficientField f, σ a = s.1.2 a) :
    haveI : NeZero (Nat.lcm s.1.1.1 t.1.1.1) := ⟨Nat.lcm_ne_zero s.1.1.1.ne_zero t.1.1.1.ne_zero⟩
    (s * t).1.1 = ⟨⟨_, Nat.pos_of_ne_zero
      (conductor_ne_zero (s.1.1.2.mul (t.1.1.2.ringHomComp σ)))⟩,
        s.1.1.2.primitive_mul (t.1.1.2.ringHomComp σ)⟩ := by
  have h :
      t.1.1.2.ringHomComp (coefficientFieldAutLift s.1.2 : ℂ →+* ℂ) = t.1.1.2.ringHomComp σ := by
    refine MulChar.ext fun u ↦ ?_
    rw [MulChar.ringHomComp_apply, MulChar.ringHomComp_apply]
    have hmem : t.1.1.2 u ∈ CoefficientField f :=
      apply_mem_coefficientField (innerTwistGroupToPairs f t).2 _
    exact (coefficientFieldAutLift_apply s.1.2 ⟨_, hmem⟩).trans (hσ ⟨_, hmem⟩).symm
  rw [← h]
  rfl

/-- **On the self twists, the projection to `χ` is multiplicative** (LMFDB
`cmf.inner_twist_group`): if `τ = 1`, then `(χ, τ) (χ', τ') = (χ χ', τ')`, where `χ χ'` is the
primitive character inducing the product of `χ` and `χ'`. -/
lemma innerTwistGroup_mul_fst_of_snd_eq_one (hs : s.1.2 = 1) :
    haveI : NeZero (Nat.lcm s.1.1.1 t.1.1.1) := ⟨Nat.lcm_ne_zero s.1.1.1.ne_zero t.1.1.1.ne_zero⟩
    (s * t).1.1 = ⟨⟨_, Nat.pos_of_ne_zero (conductor_ne_zero (s.1.1.2.mul t.1.1.2))⟩,
      s.1.1.2.primitive_mul t.1.1.2⟩ := by
  have h : t.1.1.2.ringHomComp ((1 : Gal(ℂ/ℚ)) : ℂ →+* ℂ) = t.1.1.2 :=
    MulChar.ext' fun _ ↦ rfl
  rw [innerTwistGroup_mul_fst (σ := 1) fun a ↦ by rw [hs]; rfl, h]

/-- **When the law is the product of characters**: `(χ, τ) (χ', τ')` has first component the
primitive character inducing the product of `χ` and `χ'` exactly when `τ` fixes the values of `χ'`.
So the projection `(χ, τ) ↦ χ` fails to be a homomorphism (LMFDB `cmf.inner_twist_group`) exactly
when some `τ` moves the values of some `χ'`. -/
lemma innerTwistGroup_mul_fst_eq_primitive_mul_iff :
    haveI : NeZero (Nat.lcm s.1.1.1 t.1.1.1) := ⟨Nat.lcm_ne_zero s.1.1.1.ne_zero t.1.1.1.ne_zero⟩
    (s * t).1.1 = ⟨⟨_, Nat.pos_of_ne_zero (conductor_ne_zero (s.1.1.2.mul t.1.1.2))⟩,
      s.1.1.2.primitive_mul t.1.1.2⟩ ↔ ∀ a : ZMod t.1.1.1, ((s.1.2 ⟨t.1.1.2 a,
        apply_mem_coefficientField (innerTwistGroupToPairs f t).2 a⟩ : CoefficientField f) : ℂ) =
          t.1.1.2 a := by
  refine ⟨fun h a ↦ ?_, fun h ↦ ?_⟩
  · by_cases ha : IsUnit a
    · rcases ha with ⟨u, rfl⟩
      rcases Nat.forall_exists_prime_gt_and_eq_mod u.isUnit (s.1.1.1 * t.1.1.1) with
        ⟨p, hgt, hp, hpu⟩
      have hc : p.Coprime (s.1.1.1 * t.1.1.1) :=
        Nat.coprime_of_lt_prime (mul_ne_zero s.1.1.1.ne_zero t.1.1.1.ne_zero) hgt hp
      have h₁ : (s * t).1.1.2 p = s.1.1.2 p * coefficientFieldAutLift s.1.2 (t.1.1.2 p) :=
        innerTwistMul_apply hc
      have h₂ : (innerTwistMul (s.1.1, 1) (t.1.1, 1)).1.2 p = s.1.1.2 p * t.1.1.2 p :=
        innerTwistMul_apply hc
      have h₃ : (s * t).1.1.2 p = (innerTwistMul (s.1.1, 1) (t.1.1, 1)).1.2 p :=
        congrArg (fun χ : Σ M : ℕ+, DirichletCharacter ℂ M ↦ χ.2 p) <| h.trans
          (innerTwistMul_fst_of_snd_eq_one (x := (s.1.1, 1)) (y := (t.1.1, 1)) rfl).symm
      have hs₀ : s.1.1.2 p ≠ 0 := (((ZMod.isUnit_iff_coprime p s.1.1.1).mpr
        (hc.coprime_dvd_right (dvd_mul_right _ _))).map s.1.1.2).ne_zero
      have h₄ : coefficientFieldAutLift s.1.2 (t.1.1.2 p) = t.1.1.2 p :=
        mul_left_cancel₀ hs₀ (h₁.symm.trans (h₃.trans h₂))
      rw [hpu] at h₄
      exact (coefficientFieldAutLift_apply s.1.2 _).symm.trans h₄
    · have h₀ : t.1.1.2 a = 0 := MulChar.map_nonunit _ ha
      have hzero : (⟨t.1.1.2 a, apply_mem_coefficientField (innerTwistGroupToPairs f t).2 a⟩ :
          CoefficientField f) = 0 := Subtype.ext h₀
      rw [hzero, map_zero, h₀]
      rfl
  · have h' : t.1.1.2.ringHomComp (coefficientFieldAutLift s.1.2 : ℂ →+* ℂ) = t.1.1.2 :=
      MulChar.ext' fun a ↦ (coefficientFieldAutLift_apply s.1.2 _).trans (h a)
    rw [innerTwistGroup_mul_fst (coefficientFieldAutLift_apply s.1.2), h']

variable (f) in
private lemma isTwistAtAlmostAllPrimes_conj :
    f.IsTwistAtAlmostAllPrimes f.dirichletLift⁻¹ f.conj := by
  filter_upwards [eventually_prime_coprime (NeZero.ne N)] with p hpN hp
  have hε : f.dirichletLift p ≠ 0 := (((ZMod.isUnit_iff_coprime p N).mpr (hpN hp)).map _).ne_zero
  rw [f.isGaloisConjugateBy_conj.coeff, MulChar.inv_apply_eq_inv']
  exact (eq_inv_mul_iff_mul_eq₀ hε).mpr
    (f.qExpansion_coeff_eq_dirichletLift_mul_conj hp (hpN hp)).symm

/-- **The projection `(χ, τ) ↦ χ` is not a homomorphism when the nebentypus is not quadratic**
(LMFDB `cmf.inner_twist_group`): if the nebentypus `ε` of `f` has `ε² ≠ 1`, the first component of a
product in the group of inner twists is not always the primitive character inducing the product of
the first components. Indeed `(ε⁻¹, c)` is an inner twist, for `ε⁻¹` taken primitive and `c` complex
conjugation, as `conj(a_p) = ε(p)⁻¹ a_p`, and `c` moves the values of `ε⁻¹`: its square is `(1, 1)`,
but `ε⁻² ≠ 1`. Such newforms exist (`exists_newform_χ_sq_ne_one`); in the LMFDB, 13.2.e.a has `ε` of
order 6. -/
lemma not_forall_innerTwistGroup_mul_fst_eq_primitive_mul (hf : f.χ ^ 2 ≠ 1) :
    ¬∀ s t : f.innerTwistGroup,
      haveI : NeZero (Nat.lcm s.1.1.1 t.1.1.1) := ⟨Nat.lcm_ne_zero s.1.1.1.ne_zero t.1.1.1.ne_zero⟩
      (s * t).1.1 = ⟨⟨_, Nat.pos_of_ne_zero (conductor_ne_zero (s.1.1.2.mul t.1.1.2))⟩,
        s.1.1.2.primitive_mul t.1.1.2⟩ := by
  intro h
  let x : f.innerTwistPairs := ⟨(⟨⟨_, Nat.pos_of_ne_zero (conductor_ne_zero f.dirichletLift⁻¹)⟩,
    f.dirichletLift⁻¹.primitiveCharacter⟩, Complex.conjAe.restrictScalars ℚ),
      (mk_mem_innerTwistPairs_iff f.isGaloisConjugateBy_conj).mpr ⟨primitiveCharacter_isPrimitive _,
        f.conj_mem_galoisOrbit, (isTwistAtAlmostAllPrimes_conj f).primitiveCharacter⟩⟩
  have hreal (a : ZMod x.1.1.1) : starRingEnd ℂ (x.1.1.2 a) = x.1.1.2 a :=
    innerTwistGroup_mul_fst_eq_primitive_mul_iff.mp
      (h (innerTwistPairsToGroup f x) (innerTwistPairsToGroup f x)) a
  refine hf <| MonoidHom.ext fun u ↦ Units.ext ?_
  have hu : (((u : ZMod N).val : ℕ) : ZMod N) = u := ZMod.natCast_zmod_val _
  have hprim : f.dirichletLift⁻¹.primitiveCharacter (((u : ZMod N).val : ℕ) : ℤ) =
      f.dirichletLift⁻¹ (((u : ZMod N).val : ℕ) : ℤ) :=
    primitiveCharacter_apply_of_isCoprime _ (ZMod.val_coe_unit_coprime u).isCoprime
  simp only [Int.cast_natCast] at hprim
  rw [MulChar.inv_apply_eq_inv', hu, dirichletLift_def, MulChar.ofUnitHom_coe] at hprim
  have hconj : starRingEnd ℂ (f.χ u : ℂ) = f.χ u := by
    have h₁ : starRingEnd ℂ (x.1.1.2 ((u : ZMod N).val : ℕ)) = x.1.1.2 ((u : ZMod N).val : ℕ) :=
      hreal _
    have h₂ : x.1.1.2 ((u : ZMod N).val : ℕ) = (f.χ u : ℂ)⁻¹ := hprim
    rw [h₂, map_inv₀] at h₁
    exact inv_injective h₁
  have hnorm : ‖(f.χ u : ℂ)‖ = 1 := by
    have h₁ : ‖f.dirichletLift u‖ = 1 := f.dirichletLift.unit_norm_eq_one u
    rwa [dirichletLift_def, MulChar.ofUnitHom_coe] at h₁
  have hsq : (f.χ u : ℂ) * starRingEnd ℂ (f.χ u : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
    simp
  rw [hconj] at hsq
  simpa [sq] using hsq

/-- The newform `Δ` of level one and weight twelve. -/
private noncomputable def discriminantNewform : Newform 1 12 where
  toEigenformAwayFromLevel := discriminantEigenform.toEigenformAwayFromLevel
  isNew := by
    rw [cuspFormsNew_one]
    exact Submodule.mem_top
  isNorm := ModularForm.discriminant_qExpansion_coeff_one

/-- **There is a newform whose nebentypus is not quadratic**: a primitive associate of the twist of
`Δ` by a cubic character modulo `7`, of nebentypus the square of that character at level `49`. -/
lemma exists_newform_χ_sq_ne_one : ∃ (R : ℕ) (_ : NeZero R) (g : Newform R 12), g.χ ^ 2 ≠ 1 := by
  have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  rcases MulChar.exists_mulChar_orderOf (ZMod 7) (n := 3) (by simp)
    (Complex.isPrimitiveRoot_exp 3 (by norm_num)) with ⟨ψ, hψ⟩
  have hNL : 1 * 7 ∣ 7 * 7 := ⟨7, by norm_num⟩
  have hML : 7 * 7 ∣ 7 * 7 := dvd_rfl
  rcases discriminantNewform.exists_newform_qExpansion_coeff_prime_eq_twist (M := 7) ψ hNL hML with
    ⟨R, _, hR, g, hχ, -⟩
  refine ⟨R, inferInstance, g, fun hg ↦ ?_⟩
  have h4 : ψ ^ 4 = 1 := by
    refine MulChar.ext fun u ↦ ?_
    rcases ZMod.unitsMap_surjective (dvd_of_mul_left_dvd hML) u with ⟨w, rfl⟩
    have h₁ : discriminantNewform.χ (ZMod.unitsMap (dvd_of_mul_right_dvd hNL) w) = 1 := by
      rw [Subsingleton.elim (ZMod.unitsMap (dvd_of_mul_right_dvd hNL) w) 1, map_one]
    have h₂ : g.χ (ZMod.unitsMap hR w) ^ 2 = 1 := DFunLike.congr_fun hg (ZMod.unitsMap hR w)
    have h₃ :
        g.χ (ZMod.unitsMap hR w) = ψ.toUnitHom (ZMod.unitsMap (dvd_of_mul_left_dvd hML) w) ^ 2 := by
      simpa [h₁] using DFunLike.congr_fun hχ w
    have h₄ : ((ψ.toUnitHom (ZMod.unitsMap (dvd_of_mul_left_dvd hML) w) ^ 4 : ℂˣ) : ℂ) = 1 := by
      rw [pow_mul _ 2 2, ← h₃, h₂, Units.val_one]
    rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom] at h₄
    rw [MulChar.pow_apply' _ (by norm_num), MulChar.one_apply_coe]
    exact h₄
  have hdvd : 3 ∣ 4 := hψ ▸ orderOf_dvd_of_pow_eq_one h4
  omega

variable (f) in
/-- **The image of the group of inner twists in `Aut_ℚ(K)` is abelian** (LMFDB
`cmf.inner_twist_group`), as the group itself is abelian. -/
lemma isMulCommutative_range_innerTwistGroupToAut :
    IsMulCommutative (innerTwistGroupToAut f).range :=
  inferInstance

instance : Finite f.innerTwistGroup := by
  have hfin : Finite {x : Σ M : ℕ+, DirichletCharacter ℂ M | f.HasSelfTwist x.2} :=
    (finite_setOf_hasSelfTwist f).to_subtype
  have hker : Finite (innerTwistGroupToAut f).ker :=
    Finite.of_injective (fun t : (innerTwistGroupToAut f).ker ↦
      (⟨t.1.1.1, by
        rcases mem_ker_innerTwistGroupToAut_iff.mp t.2 with ⟨χ, hχ, ht⟩
        rw [ht]
        exact hχ⟩ : {x : Σ M : ℕ+, DirichletCharacter ℂ M | f.HasSelfTwist x.2}))
      fun t t' h ↦ Subtype.ext <| innerTwistGroup_fst_injective (congrArg Subtype.val h)
  have hquot : Finite (f.innerTwistGroup ⧸ (innerTwistGroupToAut f).ker) :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange (innerTwistGroupToAut f)).symm.toEquiv
  exact Finite.of_subgroup_quotient (innerTwistGroupToAut f).ker

variable {g g' : Newform N k}

/-- **Ribet's description of inner twists** (LMFDB `cmf.inner_twist`): `(χ, g)` is an inner twist of
`f` exactly when `g` is the conjugate of `f` by a `ℚ`-automorphism `τ` of the coefficient field of
`f` with `(χ, τ)` in the group of inner twists of `f`. -/
lemma mk_mem_innerTwists_iff_exists_mem_innerTwistGroup : (χ, g) ∈ f.innerTwists ↔
    ∃ τ : Gal(CoefficientField f/ℚ), (χ, τ) ∈ f.innerTwistGroup ∧ ∀ n : ℕ,
      (qExpansion 1 g.toCuspForm).coeff n = τ (f.orbitQExpansion.coeff n) := by
  refine mk_mem_innerTwists_iff_exists.trans ⟨?_, ?_⟩
  · rintro ⟨σ, hg, hx⟩
    refine ⟨innerTwistPairsToAut f ⟨(χ, σ), hx⟩, (innerTwistPairsToGroup f ⟨(χ, σ), hx⟩).2,
      fun n ↦ ?_⟩
    rw [coe_innerTwistPairsToAut_apply, coe_coeff_orbitQExpansion]
    exact hg.coeff n
  · rintro ⟨τ, ht, hg⟩
    refine ⟨coefficientFieldAutLift τ, isGaloisConjugateBy_iff.mpr fun n ↦ ?_,
      (innerTwistGroupToPairs f ⟨(χ, τ), ht⟩).2⟩
    rw [hg n, ← coefficientFieldAutLift_apply, coe_coeff_orbitQExpansion]

/-- **An inner twist has the same coefficient field**: if `(χ, g)` is an inner twist of `f`, the
coefficient fields of `f` and `g` are the same subfield of `ℂ`. -/
lemma coefficientField_eq_of_mk_mem_innerTwists (h : (χ, g) ∈ f.innerTwists) :
    CoefficientField g = CoefficientField f := by
  rcases mk_mem_innerTwists_iff_exists.mp h with ⟨σ, hg, hx⟩
  exact hg.map_coefficientField.symm.trans (map_coefficientField_eq hx)

/-- **An inner twist is determined by its character** (LMFDB `cmf.inner_twist`): if `(χ, g)` and
`(χ, g')` are inner twists of `f`, then `g = g'`. -/
lemma eq_of_mk_mem_innerTwists (h : (χ, g) ∈ f.innerTwists) (h' : (χ, g') ∈ f.innerTwists) :
    g = g' :=
  eq_of_eventually_coeff_eq <| by
    filter_upwards [h.2.2, h'.2.2] with p hp hp' hpp
    rw [hp hpp, hp' hpp]

variable (f) in
/-- The map from the group of inner twists of `f`, of pairs `(χ, τ)`, to its inner twists, of pairs
`(χ, g)`, for the conjugate `g` of `f` by `τ`. -/
noncomputable def innerTwistGroupToInnerTwists (t : f.innerTwistGroup) : f.innerTwists :=
  ⟨(t.1.1, coefficientFieldAutLift t.1.2 • f), mk_mem_innerTwists_iff_exists.mpr
    ⟨_, f.isGaloisConjugateBy_smul _, (innerTwistGroupToPairs f t).2⟩⟩

variable (f) in
lemma innerTwistGroupToInnerTwists_bijective :
    Function.Bijective (innerTwistGroupToInnerTwists f) := by
  refine ⟨fun s t hst ↦ innerTwistGroup_fst_injective
    (congrArg (fun x : f.innerTwists ↦ x.1.1) hst), ?_⟩
  rintro ⟨⟨χ, g⟩, hx⟩
  rcases mk_mem_innerTwists_iff_exists_mem_innerTwistGroup.mp hx with ⟨τ, ht, -⟩
  exact ⟨⟨(χ, τ), ht⟩, Subtype.ext <| Prod.ext rfl <|
    eq_of_mk_mem_innerTwists (innerTwistGroupToInnerTwists f ⟨(χ, τ), ht⟩).2 hx⟩

instance : Finite f.innerTwists :=
  Finite.of_surjective _ (innerTwistGroupToInnerTwists_bijective f).2

variable (f) in
/-- **A newform has finitely many inner twists** (Ribet), so that the inner twist count is not a
junk value. -/
lemma finite_innerTwists : f.innerTwists.Finite :=
  Set.toFinite _

variable (f) in
lemma innerTwistCount_pos : 0 < f.innerTwistCount :=
  (Set.ncard_pos (finite_innerTwists f)).mpr ⟨_, f.one_mem_innerTwists⟩

variable (f) in
/-- **The inner twist count is the order of the group of inner twists** (LMFDB
`cmf.inner_twist_count`). -/
lemma innerTwistCount_eq_natCard : f.innerTwistCount = Nat.card f.innerTwistGroup :=
  (Nat.card_coe_set_eq _).symm.trans (Nat.card_eq_of_bijective _
    (innerTwistGroupToInnerTwists_bijective f)).symm

end HeckeRing.GL2.Newform
