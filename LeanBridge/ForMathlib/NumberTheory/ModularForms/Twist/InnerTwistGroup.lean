import LeanBridge.ForMathlib.NumberTheory.DirichletCharacter.PrimitiveQuadratic
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Twist.InnerTwist

/-!
# The group of inner twists of a newform

The LMFDB states (LMFDB `cmf.inner_twist_group`) that the pairs `(χ, σ)` giving rise to an inner
twist of a newform `f`, with `χ` a primitive Dirichlet character and `σ` a `ℚ`-automorphism of the
coefficient field `K` of `f`, form a group `G` under `(χ, σ) (χ', σ') = (χ σ(χ'), σ σ')`; that
`(χ, σ) ↦ σ` is a homomorphism `G → Aut_ℚ(K)` with kernel the self twists and abelian image; and
that `(χ, σ) ↦ χ` is injective, and a homomorphism on the self twists.

Here, as for Galois conjugacy in LeanBridge, `σ` is an automorphism of `ℂ`: the pairs `(χ, σ)` with
`σ(a_p(f)) = χ(p) a_p(f)` for all but finitely many primes `p` are the *inner twist pairs* of `f`,
and they form a group under the law of the LMFDB, in which `χ σ(χ')` is the primitive character
inducing the product of `χ` and `σ ∘ χ'`. The group laws reduce to identities between values of
primitive characters at almost all primes, as primitive Dirichlet characters that agree at almost
all primes are equal (`DirichletCharacter.eq_of_isPrimitive_of_eventually_eq`, by Dirichlet's
theorem on primes in arithmetic progressions). The projection to `σ` is a homomorphism to
`Gal(ℂ/ℚ)` whose kernel consists of the self twists, and more generally the pairs `(χ, σ)` with `σ`
trivial on the coefficients of `f` are the self twists of `f`; for `σ = 1` the law is the product
of characters. When `σ(f)` is a newform `g`, the inner twist pair `(χ, σ)` is the inner twist
`(χ, g)` of `HeckeRing.GL2.Newform.innerTwists`, and every inner twist arises in this way.

The group of the LMFDB is the image of this group under `(χ, σ) ↦ (χ, σ|_K)`. That `σ` maps `K`
onto itself and that `χ` takes values in `K`, so that the law descends to the pairs
`(χ, σ|_K)`, that the image in `Aut_ℚ(K)` is abelian, that `χ` determines `σ|_K`, and that there
are finitely many inner twists, are theorems of Ribet that are not proved here.

## Main definitions

* `HeckeRing.GL2.Newform.innerTwistPairs`: the inner twist pairs `(χ, σ)` of `f`
  (LMFDB `cmf.inner_twist_group`).
* `HeckeRing.GL2.Newform.innerTwistMul`, `HeckeRing.GL2.Newform.innerTwistOne`,
  `HeckeRing.GL2.Newform.innerTwistInv`: the group law of the LMFDB, its identity and inverses.
* The instance `Group f.innerTwistPairs`: the group of inner twists (LMFDB `cmf.inner_twist_group`).
* `HeckeRing.GL2.Newform.innerTwistPairsToGal`: the projection `(χ, σ) ↦ σ`.

## Main results

* `HeckeRing.GL2.Newform.innerTwistMul_mem`, `HeckeRing.GL2.Newform.innerTwistInv_mem`: the inner
  twist pairs are closed under the law and inverses.
* `HeckeRing.GL2.Newform.innerTwistMul_assoc`: the law is associative.
* `HeckeRing.GL2.Newform.mk_mem_innerTwistPairs_iff_hasSelfTwist`: the inner twist pairs `(χ, σ)`
  with `σ` trivial on the coefficients of `f` are the self twists.
* `HeckeRing.GL2.Newform.mem_ker_innerTwistPairsToGal_iff`: the kernel of the projection to `σ`
  consists of the self twists.
* `HeckeRing.GL2.Newform.innerTwistMul_fst_of_snd_eq_one`: on the self twists, the law is the
  product of characters.
* `HeckeRing.GL2.Newform.mk_mem_innerTwistPairs_iff`: inner twist pairs and inner twists agree
  when `σ(f)` is a newform.
* `HeckeRing.GL2.Newform.mk_mem_innerTwists_iff_exists`: the inner twists `(χ, g)` of `f` are the
  `(χ, σ(f))` for its inner twist pairs `(χ, σ)`.
-/

open UpperHalfPlane DirichletCharacter

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ} {f g : Newform N k} {χ : Σ M : ℕ+, DirichletCharacter ℂ M}
  {x y z : (Σ M : ℕ+, DirichletCharacter ℂ M) × Gal(ℂ/ℚ)} {σ : Gal(ℂ/ℚ)} {p : ℕ}

variable (f) in
/-- The **inner twist pairs** of the newform `f` (LMFDB `cmf.inner_twist_group`): the pairs
`(χ, σ)` of a primitive Dirichlet character `χ` of positive modulus and an automorphism `σ` of `ℂ`
with `σ(a_p(f)) = χ(p) a_p(f)` for all but finitely many primes `p`, i.e. such that the Galois
conjugate `σ(f)` is a twist of `f` by `χ`. The LMFDB takes `σ` in `Aut_ℚ(K)` for the coefficient
field `K` of `f`; only the restriction of `σ` to `K` enters the condition. -/
def innerTwistPairs : Set ((Σ M : ℕ+, DirichletCharacter ℂ M) × Gal(ℂ/ℚ)) :=
  {x | x.1.2.IsPrimitive ∧ ∀ᶠ p in Filter.cofinite, p.Prime →
    x.2 ((qExpansion 1 f.toCuspForm).coeff p) = x.1.2 p * (qExpansion 1 f.toCuspForm).coeff p}

/-- The **identity** `(1, 1)` of the group of inner twists (LMFDB `cmf.inner_twist_group`): the
trivial character, of modulus `1`, and the identity of `ℂ`. -/
noncomputable def innerTwistOne : (Σ M : ℕ+, DirichletCharacter ℂ M) × Gal(ℂ/ℚ) :=
  (⟨1, 1⟩, 1)

/-- The **product of inner twists** (LMFDB `cmf.inner_twist_group`):
`(χ, σ) (χ', σ') = (χ σ(χ'), σ σ')`, where `χ σ(χ')` is the primitive character inducing the
product of `χ` and `σ ∘ χ'` (Mathlib's `DirichletCharacter.primitive_mul`). -/
noncomputable def innerTwistMul (x y : (Σ M : ℕ+, DirichletCharacter ℂ M) × Gal(ℂ/ℚ)) :
    (Σ M : ℕ+, DirichletCharacter ℂ M) × Gal(ℂ/ℚ) :=
  haveI : NeZero (Nat.lcm x.1.1 y.1.1) := ⟨Nat.lcm_ne_zero x.1.1.ne_zero y.1.1.ne_zero⟩
  (⟨⟨_, Nat.pos_of_ne_zero (conductor_ne_zero _)⟩,
    x.1.2.primitive_mul (y.1.2.ringHomComp (x.2 : ℂ →+* ℂ))⟩, x.2 * y.2)

/-- The **inverse of an inner twist** (LMFDB `cmf.inner_twist_group`):
`(χ, σ)⁻¹ = (σ⁻¹(χ)⁻¹, σ⁻¹)`. -/
noncomputable def innerTwistInv (x : (Σ M : ℕ+, DirichletCharacter ℂ M) × Gal(ℂ/ℚ)) :
    (Σ M : ℕ+, DirichletCharacter ℂ M) × Gal(ℂ/ℚ) :=
  (⟨x.1.1, (x.1.2.ringHomComp ((x.2⁻¹ : Gal(ℂ/ℚ)) : ℂ →+* ℂ))⁻¹⟩, x.2⁻¹)

lemma innerTwistOne_apply : innerTwistOne.1.2 p = 1 :=
  MulChar.one_apply (isUnit_of_subsingleton (p : ZMod 1))

lemma innerTwistMul_apply (hp : p.Coprime (x.1.1 * y.1.1)) :
    (innerTwistMul x y).1.2 p = x.1.2 p * x.2 (y.1.2 p) := by
  have hp' : IsCoprime (p : ℤ) (Nat.lcm x.1.1 y.1.1 : ℕ) :=
    Nat.isCoprime_iff_coprime.mpr (hp.coprime_dvd_right (Nat.lcm_dvd_mul _ _))
  have : NeZero (Nat.lcm x.1.1 y.1.1) := ⟨Nat.lcm_ne_zero x.1.1.ne_zero y.1.1.ne_zero⟩
  have h : (x.1.2.mul (y.1.2.ringHomComp (x.2 : ℂ →+* ℂ))).primitiveCharacter (p : ℤ) =
      x.1.2.mul (y.1.2.ringHomComp (x.2 : ℂ →+* ℂ)) (p : ℤ) :=
    primitiveCharacter_apply_of_isCoprime _ hp'
  rw [DirichletCharacter.mul, MulChar.mul_apply, changeLevel_eq_cast_of_dvd' _ _ hp',
    changeLevel_eq_cast_of_dvd' _ _ hp', MulChar.ringHomComp_apply] at h
  simp only [Int.cast_natCast] at h
  exact h

lemma innerTwistMul_snd : (innerTwistMul x y).2 = x.2 * y.2 :=
  rfl

lemma innerTwistInv_apply : (innerTwistInv x).1.2 p = (x.2⁻¹ (x.1.2 p))⁻¹ :=
  MulChar.inv_apply_eq_inv' (x.1.2.ringHomComp ((x.2⁻¹ : Gal(ℂ/ℚ)) : ℂ →+* ℂ)) (p : ZMod x.1.1)

lemma innerTwistInv_snd : (innerTwistInv x).2 = x.2⁻¹ :=
  rfl

private lemma eventually_coprime {n : ℕ} (hn : n ≠ 0) :
    ∀ᶠ p : ℕ in Filter.cofinite, p.Prime → p.Coprime n :=
  (Nat.cofinite_eq_atTop ▸ Filter.eventually_gt_atTop n).mono fun _ hnp hp ↦
    Nat.coprime_of_lt_prime hn hnp hp

private lemma apply_ne_zero (hp : p.Coprime χ.1) : χ.2 p ≠ 0 :=
  (((ZMod.isUnit_iff_coprime p χ.1).mpr hp).map χ.2).ne_zero

/-- **The inner twist pairs with `σ` trivial on the coefficients of `f` are its self twists**, the
kernel of the projection to `Aut_ℚ(K)` in the LMFDB. -/
lemma mk_mem_innerTwistPairs_iff_hasSelfTwist
    (hσ : ∀ n, σ ((qExpansion 1 f.toCuspForm).coeff n) = (qExpansion 1 f.toCuspForm).coeff n) :
    (χ, σ) ∈ f.innerTwistPairs ↔ f.HasSelfTwist χ.2 := by
  simp only [innerTwistPairs, Set.mem_ofPred_eq, hσ]
  exact ⟨fun hχ ↦ ⟨χ.1.ne_zero, hχ⟩, fun hχ ↦ hχ.2⟩

lemma mk_one_mem_innerTwistPairs_iff : (χ, 1) ∈ f.innerTwistPairs ↔ f.HasSelfTwist χ.2 :=
  mk_mem_innerTwistPairs_iff_hasSelfTwist fun _ ↦ rfl

lemma innerTwistOne_mem : innerTwistOne ∈ f.innerTwistPairs :=
  mk_one_mem_innerTwistPairs_iff.mpr f.hasSelfTwist_one

/-- **The product of inner twist pairs is an inner twist pair**: if `σ(a_p) = χ(p) a_p` and
`σ'(a_p) = χ'(p) a_p`, then `σ σ'(a_p) = χ(p) σ(χ'(p)) a_p`. -/
lemma innerTwistMul_mem (hx : x ∈ f.innerTwistPairs) (hy : y ∈ f.innerTwistPairs) :
    innerTwistMul x y ∈ f.innerTwistPairs := by
  refine ⟨primitive_mul_isPrimitive _ _, ?_⟩
  filter_upwards [hx.2, hy.2, eventually_coprime (mul_ne_zero x.1.1.ne_zero y.1.1.ne_zero)] with
    p hxp hyp hpxy hp
  rw [innerTwistMul_apply (hpxy hp), innerTwistMul_snd, AlgEquiv.mul_apply, hyp hp, map_mul,
    hxp hp]
  ring1

/-- **The inverse of an inner twist pair is an inner twist pair**: if `σ(a_p) = χ(p) a_p`, then
`σ⁻¹(a_p) = σ⁻¹(χ(p))⁻¹ a_p`. -/
lemma innerTwistInv_mem (hx : x ∈ f.innerTwistPairs) : innerTwistInv x ∈ f.innerTwistPairs := by
  refine ⟨(conductor_inv _).trans (hx.1.ringHomComp _ (RingHom.injective _)), ?_⟩
  filter_upwards [hx.2, eventually_coprime x.1.1.ne_zero] with p hxp hpx hp
  have h : x.2⁻¹ (x.1.2 p) * x.2⁻¹ ((qExpansion 1 f.toCuspForm).coeff p) =
      (qExpansion 1 f.toCuspForm).coeff p := by
    rw [← map_mul, ← hxp hp, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  rw [innerTwistInv_apply]
  exact (eq_inv_mul_iff_mul_eq₀ ((map_ne_zero _).mpr (apply_ne_zero (hpx hp)))).mpr h

/-- **The product of inner twists is associative**: both sides are primitive characters with the
value `χ(p) σ(χ'(p)) σ σ'(χ''(p))` at almost all primes `p`. -/
lemma innerTwistMul_assoc :
    innerTwistMul (innerTwistMul x y) z = innerTwistMul x (innerTwistMul y z) := by
  refine Prod.ext (eq_of_isPrimitive_of_eventually_eq (primitive_mul_isPrimitive _ _)
    (primitive_mul_isPrimitive _ _) ?_) (mul_assoc x.2 y.2 z.2)
  filter_upwards [eventually_coprime (mul_ne_zero (innerTwistMul x y).1.1.ne_zero z.1.1.ne_zero),
    eventually_coprime (mul_ne_zero x.1.1.ne_zero y.1.1.ne_zero),
    eventually_coprime (mul_ne_zero x.1.1.ne_zero (innerTwistMul y z).1.1.ne_zero),
    eventually_coprime (mul_ne_zero y.1.1.ne_zero z.1.1.ne_zero)] with p h₁ h₂ h₃ h₄ hp
  rw [innerTwistMul_apply (h₁ hp), innerTwistMul_apply (h₂ hp), innerTwistMul_apply (h₃ hp),
    innerTwistMul_apply (h₄ hp), innerTwistMul_snd, AlgEquiv.mul_apply, map_mul, mul_assoc]

lemma innerTwistOne_innerTwistMul (hx : x.1.2.IsPrimitive) : innerTwistMul innerTwistOne x = x := by
  refine Prod.ext (eq_of_isPrimitive_of_eventually_eq (primitive_mul_isPrimitive _ _) hx ?_)
    (one_mul x.2)
  filter_upwards [eventually_coprime x.1.1.ne_zero] with p hpx hp
  rw [innerTwistMul_apply (by simpa [innerTwistOne] using hpx hp), innerTwistOne_apply, one_mul]
  rfl

lemma innerTwistMul_innerTwistOne (hx : x.1.2.IsPrimitive) : innerTwistMul x innerTwistOne = x := by
  refine Prod.ext (eq_of_isPrimitive_of_eventually_eq (primitive_mul_isPrimitive _ _) hx ?_)
    (mul_one x.2)
  filter_upwards [eventually_coprime x.1.1.ne_zero] with p hpx hp
  rw [innerTwistMul_apply (by simpa [innerTwistOne] using hpx hp), innerTwistOne_apply, map_one,
    mul_one]

lemma innerTwistInv_innerTwistMul : innerTwistMul (innerTwistInv x) x = innerTwistOne := by
  refine Prod.ext (eq_of_isPrimitive_of_eventually_eq (primitive_mul_isPrimitive _ _)
    isPrimitive_one_level_one ?_) (inv_mul_cancel x.2)
  filter_upwards [eventually_coprime (mul_ne_zero x.1.1.ne_zero x.1.1.ne_zero)] with p hpx hp
  rw [innerTwistMul_apply (x := innerTwistInv x) (hpx hp), innerTwistInv_apply, innerTwistInv_snd,
    inv_mul_cancel₀ ((map_ne_zero _).mpr (apply_ne_zero (hpx hp).coprime_mul_left_right)),
    innerTwistOne_apply]

noncomputable instance : Group f.innerTwistPairs where
  mul x y := ⟨innerTwistMul x y, innerTwistMul_mem x.2 y.2⟩
  one := ⟨innerTwistOne, innerTwistOne_mem⟩
  inv x := ⟨innerTwistInv x, innerTwistInv_mem x.2⟩
  mul_assoc _ _ _ := Subtype.ext innerTwistMul_assoc
  one_mul x := Subtype.ext (innerTwistOne_innerTwistMul x.2.1)
  mul_one x := Subtype.ext (innerTwistMul_innerTwistOne x.2.1)
  inv_mul_cancel _ := Subtype.ext innerTwistInv_innerTwistMul

variable (f) in
/-- The **projection** `(χ, σ) ↦ σ` of the group of inner twists of `f` to `Gal(ℂ/ℚ)` (LMFDB
`cmf.inner_twist_group`), a homomorphism. The LMFDB projects to `Aut_ℚ(K)`, through the
restriction of `σ` to the coefficient field `K` of `f`. -/
def innerTwistPairsToGal : f.innerTwistPairs →* Gal(ℂ/ℚ) where
  toFun x := x.1.2
  map_one' := rfl
  map_mul' _ _ := rfl

/-- **The kernel of the projection to `σ` consists of the self twists** `(χ, 1)` of `f`. -/
lemma mem_ker_innerTwistPairsToGal_iff {t : f.innerTwistPairs} :
    t ∈ (innerTwistPairsToGal f).ker ↔ ∃ χ, f.HasSelfTwist χ.2 ∧ t.1 = (χ, 1) := by
  refine ⟨fun ht ↦ ⟨t.1.1, ?_, Prod.ext rfl ht⟩, ?_⟩
  · rw [← mk_one_mem_innerTwistPairs_iff, ← MonoidHom.mem_ker.mp ht]
    exact t.2
  · rintro ⟨χ, -, ht⟩
    exact MonoidHom.mem_ker.mpr (congrArg Prod.snd ht)

/-- **On the self twists, the law is the product of characters**: if `σ = 1`, then
`(χ, σ) (χ', σ') = (χ χ', σ')`, where `χ χ'` is the primitive character inducing the product of `χ`
and `χ'`, so that `(χ, σ) ↦ χ` is multiplicative on the self twists. -/
lemma innerTwistMul_fst_of_snd_eq_one (hx : x.2 = 1) :
    haveI : NeZero (Nat.lcm x.1.1 y.1.1) := ⟨Nat.lcm_ne_zero x.1.1.ne_zero y.1.1.ne_zero⟩
    (innerTwistMul x y).1 = ⟨⟨_, Nat.pos_of_ne_zero (conductor_ne_zero (x.1.2.mul y.1.2))⟩,
      x.1.2.primitive_mul y.1.2⟩ := by
  rcases x with ⟨χ, σ⟩
  simp only at hx
  subst hx
  have : NeZero (Nat.lcm χ.1 y.1.1) := ⟨Nat.lcm_ne_zero χ.1.ne_zero y.1.1.ne_zero⟩
  have h : y.1.2.ringHomComp ((1 : Gal(ℂ/ℚ)) : ℂ →+* ℂ) = y.1.2 :=
    MulChar.ext' fun _ ↦ rfl
  exact congrArg (fun ψ : DirichletCharacter ℂ y.1.1 ↦ (⟨⟨_, Nat.pos_of_ne_zero
    (conductor_ne_zero (χ.2.mul ψ))⟩, χ.2.primitive_mul ψ⟩ : Σ M : ℕ+, DirichletCharacter ℂ M)) h

/-- **Inner twist pairs and inner twists agree** when the Galois conjugate `σ(f)` is a newform `g`:
`(χ, σ)` is an inner twist pair of `f` exactly when `(χ, g)` is an inner twist of `f` in the sense
of `HeckeRing.GL2.Newform.innerTwists`. -/
lemma mk_mem_innerTwistPairs_iff (hg : f.IsGaloisConjugateBy σ g) :
    (χ, σ) ∈ f.innerTwistPairs ↔ (χ, g) ∈ f.innerTwists :=
  ⟨fun h ↦ ⟨h.1, hg.isGaloisConjugate, h.2.mono fun p hp hp' ↦ (hg.coeff p).trans (hp hp')⟩,
    fun h ↦ ⟨h.1, h.2.2.mono fun p hp hp' ↦ (hg.coeff p).symm.trans (hp hp')⟩⟩

/-- **The inner twists of `f` are the images of its inner twist pairs**: `(χ, g)` is an inner twist
of `f` exactly when `g = σ(f)` for an inner twist pair `(χ, σ)`. -/
lemma mk_mem_innerTwists_iff_exists :
    (χ, g) ∈ f.innerTwists ↔ ∃ σ, f.IsGaloisConjugateBy σ g ∧ (χ, σ) ∈ f.innerTwistPairs :=
  ⟨fun h ↦ h.2.1.elim fun σ hσ ↦ ⟨σ, hσ, (mk_mem_innerTwistPairs_iff hσ).mpr h⟩,
    fun ⟨_, hσ, h⟩ ↦ (mk_mem_innerTwistPairs_iff hσ).mp h⟩

end HeckeRing.GL2.Newform
