import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.LevelStructure
import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.SplitCartanStructure
import LeanBridge.ForMathlib.NumberTheory.ModularCurve.GammaZeroOneGroups

/-!
# `X₀(N)`, `X₁(N)` and `X_{±1}(N)` level structures on elliptic curves

Let `W` be an elliptic curve over a field `F`, `K` an extension of `F` (in the LMFDB a separable
closure, so that `K ≃ₐ[F] K` is the absolute Galois group of `F`), and `E[N]` the `N`-torsion of
`W` over `K`, on which `K ≃ₐ[F] K` acts by the mod-`N` Galois representation. The LMFDB describes
the non-cuspidal `F`-points of three modular curves by Galois-stable data on `E[N]`, up to
isomorphism over `K`:

* `X₀(N)` (`modcurve.x0`, `ag.modcurve.x0`): pairs `(E, C)` with `C` a Galois-stable cyclic
  subgroup of `E[N]` of order `N`, the kernel of a cyclic isogeny of degree `N` defined over `F`;
* `X₁(N)` (`modcurve.x1`, `ag.modcurve.x1`): pairs `(E, P)` with `P ∈ E[N]` an `F`-rational point
  of exact order `N`;
* `X_{±1}(N)` (`modcurve.xpm1`): pairs `(E, ±P)` with `P ∈ E[N]` a point of exact order `N` such
  that the set `{P, -P}` is Galois-stable.

These are the structures cut out by the subgroups `!![*, *; 0, *]`, `!![1, *; 0, *]` and
`!![±1, *; 0, *]` of `GL₂(ℤ/Nℤ)`: for a basis `(P, Q)` of `E[N]` over `ℤ/Nℤ`, the mod-`N`
representation in this basis takes values in one of these groups if and only if `⟨P⟩`, `P` or `±P`
is a structure of the corresponding kind. Conversely, when `E[N]` is free of rank `2` over `ℤ/Nℤ`,
as it is for `K` separably closed and `N` invertible in `K`, every point of exact order `N` is the
first vector of a basis, so `W` carries such a structure if and only if its mod-`N` image lies, in
some basis, in the corresponding group: this is how an `F`-point of the modular curve of its
inverse image in `GL₂(ℤ̂)` arises (LMFDB `modcurve.level_structure`).

The maps `X₁(N) → X_{±1}(N) → X₀(N)` are `P ↦ ±P ↦ ⟨P⟩` on these structures, and `(ℤ/Nℤ)ˣ` acts on
the pairs `(E, P)` by `(E, P) ↦ (E, dP)`: its orbits are exactly the fibres of `P ↦ ⟨P⟩`, so that
`X₀(N)` is the quotient of `X₁(N)` by `(ℤ/Nℤ)ˣ` (LMFDB `ag.modcurve.x1`), whose subgroup `{±1}`
acts trivially on isomorphism classes, the automorphism `[-1]` of `E` mapping `P` to `-P`. For
`N ≤ 2`, `-P = P`, and the structures of `X₁(N)` and `X_{±1}(N)` coincide. The modular curves
themselves, their cusps, the bijection between their points and isomorphism classes of these
structures, and the cyclic isogeny with kernel `C` (Vélu's formulas) are not formalised.

## Main definitions

* `WeierstrassCurve.IsGammaZeroLevelStructure` (LMFDB `modcurve.x0`, `ag.modcurve.x0`): the pairs
  `(E, C)`.
* `WeierstrassCurve.IsGammaOneLevelStructure` (LMFDB `modcurve.x1`, `ag.modcurve.x1`): the pairs
  `(E, P)`.
* `WeierstrassCurve.IsGammaPMOneLevelStructure` (LMFDB `modcurve.xpm1`): the pairs `(E, ±P)`.

## Main results

* `ZMod.zmultiples_eq_zmultiples_iff`: two points of exact order `N` of a `ℤ/Nℤ`-module generate
  the same subgroup if and only if they differ by a unit of `ℤ/Nℤ`.
* `Module.Basis.exists_zmultiples_sup_eq_top`: in a free `ℤ/Nℤ`-module of rank `2`, every element
  of exact order `N` is the first vector of a basis.
* `WeierstrassCurve.range_modGaloisRepresentationGL_le_gl2Borel_iff`,
  `WeierstrassCurve.range_modGaloisRepresentationGL_le_gammaOneSubgroup_iff` and
  `WeierstrassCurve.range_modGaloisRepresentationGL_le_gammaPMOneSubgroup_iff`: the mod-`N` image in
  a basis `(P, Q)` lies in `!![*, *; 0, *]`, `!![1, *; 0, *]` or `!![±1, *; 0, *]` if and only if
  `⟨P⟩`, `P` or `±P` is a level structure of the corresponding kind.
* `WeierstrassCurve.exists_isGammaZeroLevelStructure_iff`,
  `WeierstrassCurve.exists_isGammaOneLevelStructure_iff` and
  `WeierstrassCurve.exists_isGammaPMOneLevelStructure_iff`: over a separably closed field in which
  `N` is invertible, `W` carries such a level structure if and only if its mod-`N` image lies, in
  some basis, in the corresponding subgroup.
* `WeierstrassCurve.IsGammaPMOneLevelStructure.isGammaZeroLevelStructure`: `⟨P⟩` is an
  `X₀(N)`-level structure for an `X_{±1}(N)`-level structure `±P`.
* `WeierstrassCurve.IsGammaOneLevelStructure.zmultiples_eq_iff`: the fibres of `P ↦ ⟨P⟩` on
  `X₁(N)`-level structures are the orbits of `(ℤ/Nℤ)ˣ`.
* `WeierstrassCurve.isGammaPMOneLevelStructure_iff_isGammaOneLevelStructure`: for `N ∣ 2` the two
  kinds of structures coincide.
* `WeierstrassCurve.torsionGeometricAutRepresentation_neg_one`: the automorphism `[-1]` acts on
  `E[N]` by `P ↦ -P`.
-/

open Matrix GeneralLinearGroup Module TauCeti

open scoped WeierstrassCurve

section ZModModule

variable {N : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod N) V] {a a' r : ZMod N} {P Q : V}

variable [NeZero N] in
lemma ZMod.exists_mul_add_mul_eq_one
    (h : ∀ k : ℕ, (k : ZMod N) * a = 0 → (k : ZMod N) * a' = 0 → N ∣ k) :
    ∃ x y : ZMod N, a * x + a' * y = 1 := by
  have hd : (a.val.gcd a'.val).gcd N ∣ N := Nat.gcd_dvd_right _ _
  have hk (c : ZMod N) (hc : (a.val.gcd a'.val).gcd N ∣ c.val) :
      ((N / (a.val.gcd a'.val).gcd N : ℕ) : ZMod N) * c = 0 := by
    rcases hc with ⟨m, hm⟩
    rw [← ZMod.natCast_zmod_val c, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff, hm, ← mul_assoc,
      Nat.div_mul_cancel hd]
    exact dvd_mul_right N m
  have hN : N ∣ N / (a.val.gcd a'.val).gcd N :=
    h _ (hk a ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)))
      (hk a' ((Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)))
  have hdiv : N / (a.val.gcd a'.val).gcd N = N :=
    le_antisymm (Nat.div_le_self _ _) <| Nat.le_of_dvd
      (Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) hd) (Nat.pos_of_dvd_of_pos hd (NeZero.pos N))) hN
  have hcop : (a.val.gcd a'.val).Coprime N := (Nat.div_eq_self.mp hdiv).resolve_left (NeZero.ne N)
  rcases (ZMod.isUnit_iff_coprime _ _).mpr hcop with ⟨u, hu⟩
  have hbez :
      ((a.val.gcd a'.val : ℕ) : ZMod N) = a * a.val.gcdA a'.val + a' * a.val.gcdB a'.val := by
    simpa using congrArg (Int.cast : ℤ → ZMod N) (Nat.gcd_eq_gcd_ab a.val a'.val)
  refine ⟨a.val.gcdA a'.val * ↑u⁻¹, a.val.gcdB a'.val * ↑u⁻¹, ?_⟩
  rw [← mul_assoc, ← mul_assoc, ← add_mul, ← hbez, ← hu, Units.mul_inv]

lemma addOrderOf_units_smul (d : (ZMod N)ˣ) : addOrderOf (d • P) = addOrderOf P :=
  AddEquiv.addOrderOf_eq (DistribMulAction.toAddEquiv V d) P

namespace Matrix.GeneralLinearGroup

variable (b : Basis (Fin 2) (ZMod N) V) (φ : LinearMap.GeneralLinearGroup (ZMod N) V)

lemma toLin'_symm_mem_gl2Borel_iff :
    (toLin' b).symm φ ∈ GL2Borel (ZMod N) ↔ φ.val (b 0) ∈ AddSubgroup.zmultiples (b 0) := by
  rw [b.mem_zmultiples_iff zero_ne_one, ← toLin'_symm_apply_apply, GL2Borel.mem_iff]

lemma toLin'_symm_mem_gammaOneSubgroup_iff :
    (toLin' b).symm φ ∈ gammaOneSubgroup (ZMod N) ↔ φ.val (b 0) = b 0 := by
  rw [mem_gammaOneSubgroup_iff, toLin'_symm_apply_apply, toLin'_symm_apply_apply, b.ext_elem_iff,
    Fin.forall_fin_two]
  simp

lemma toLin'_symm_mem_gammaPMOneSubgroup_iff :
    (toLin' b).symm φ ∈ gammaPMOneSubgroup (ZMod N) ↔ φ.val (b 0) = b 0 ∨ φ.val (b 0) = -b 0 := by
  rw [mem_gammaPMOneSubgroup_iff, toLin'_symm_apply_apply, toLin'_symm_apply_apply, b.ext_elem_iff,
    b.ext_elem_iff, Fin.forall_fin_two, Fin.forall_fin_two]
  simp [or_and_right]

end Matrix.GeneralLinearGroup

variable [NeZero N]

lemma ZMod.smul_eq_zero_iff_of_addOrderOf_eq (hP : addOrderOf P = N) : r • P = 0 ↔ r = 0 := by
  rw [← ZMod.natCast_zmod_val r, Nat.cast_smul_eq_nsmul, ← addOrderOf_dvd_iff_nsmul_eq_zero, hP,
    ZMod.natCast_eq_zero_iff]

/-- **Two elements of exact order `N` of a `ℤ/Nℤ`-module generate the same subgroup if and only if
they differ by a unit of `ℤ/Nℤ`.** -/
lemma ZMod.zmultiples_eq_zmultiples_iff (hP : addOrderOf P = N) :
    AddSubgroup.zmultiples Q = AddSubgroup.zmultiples P ↔ ∃ d : (ZMod N)ˣ, Q = d • P := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases AddSubgroup.mem_zmultiples_iff.mp (h ▸ AddSubgroup.mem_zmultiples Q) with ⟨k, rfl⟩
    rcases AddSubgroup.mem_zmultiples_iff.mp (h.symm ▸ AddSubgroup.mem_zmultiples P) with ⟨m, hm⟩
    rw [← Int.cast_smul_eq_zsmul (ZMod N), ← Int.cast_smul_eq_zsmul (ZMod N), smul_smul] at hm
    have hmk : ((m : ZMod N) * k - 1) • P = 0 := by
      rw [sub_smul, hm, one_smul, sub_self]
    refine ⟨(IsUnit.of_mul_eq_one_right _
      (sub_eq_zero.mp ((ZMod.smul_eq_zero_iff_of_addOrderOf_eq hP).mp hmk))).unit, ?_⟩
    rw [Units.smul_def, IsUnit.unit_spec, Int.cast_smul_eq_zsmul]
  · rintro ⟨d, rfl⟩
    exact ZMod.zmultiples_smul_of_isUnit d.isUnit

namespace Module.Basis

/-- **In a free `ℤ/Nℤ`-module of rank `2`, every element `P` of exact order `N` is the first vector
of a basis**: some `Q` generates the module together with `P`. -/
lemma exists_zmultiples_sup_eq_top (b : Basis (Fin 2) (ZMod N) V) (hP : addOrderOf P = N) :
    ∃ Q : V, AddSubgroup.zmultiples P ⊔ AddSubgroup.zmultiples Q = ⊤ := by
  have h (k : ℕ) (h₀ : (k : ZMod N) * b.repr P 0 = 0) (h₁ : (k : ZMod N) * b.repr P 1 = 0) :
      N ∣ k := by
    rw [← hP, addOrderOf_dvd_iff_nsmul_eq_zero, ← Nat.cast_smul_eq_nsmul (ZMod N)]
    refine b.ext_elem fun i ↦ ?_
    fin_cases i <;> simpa
  rcases ZMod.exists_mul_add_mul_eq_one h with ⟨x, y, hxy⟩
  refine ⟨-y • b 0 + x • b 1, eq_top_iff.mpr fun v _ ↦ ?_⟩
  have hv : v = (x * b.repr v 0 + y * b.repr v 1) • P +
      (b.repr P 0 * b.repr v 1 - b.repr P 1 * b.repr v 0) • (-y • b 0 + x • b 1) := by
    refine b.ext_elem fun i ↦ ?_
    fin_cases i
    · simp
      linear_combination (-b.repr v 0) * hxy
    · simp
      linear_combination (-b.repr v 1) * hxy
  rw [hv]
  exact AddSubgroup.add_mem_sup (ZMod.smul_mem (AddSubgroup.mem_zmultiples P) _)
    (ZMod.smul_mem (AddSubgroup.mem_zmultiples _) _)

end Module.Basis

end ZModModule

namespace WeierstrassCurve

variable {F K : Type*} [Field F] [Field K] [DecidableEq K] [Algebra F K] (W : WeierstrassCurve F)
  (N : ℕ) (C : AddSubgroup (AddSubgroup.torsionBy (W⁄K).toAffine.Point (N : ℤ)))
  (P Q : AddSubgroup.torsionBy (W⁄K).toAffine.Point (N : ℤ))

/-- An **`X₀(N)`-level structure** `C` on `W` over `F` (LMFDB `modcurve.x0`, `ag.modcurve.x0`): a
Galois-stable cyclic subgroup `C` of `E[N]` of order `N`. The LMFDB equivalently describes it as
the kernel of a cyclic isogeny of degree `N` defined over `F`, which exists by Vélu's formulas (not
formalised), and records the isogeny by its kernel as in
`LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.LevelStructure`. The non-cuspidal `F`-points
of `X₀(N)` parametrize the pairs `(E, C)` up to isomorphism over a separable closure. Such a
structure exists if and only if the mod-`N` image of `W` lies, in some basis, in the upper
triangular subgroup (`exists_isGammaZeroLevelStructure_iff`). -/
def IsGammaZeroLevelStructure : Prop :=
  IsAddCyclic C ∧ Nat.card C = N ∧ W.IsGaloisStableTorsion N C

/-- An **`X₁(N)`-level structure** `P` on `W` over `F` (LMFDB `modcurve.x1`, `ag.modcurve.x1`): a
point `P` of `E[N]` of exact order `N` that is `F`-rational, that is, fixed by every
`σ : K ≃ₐ[F] K`. The non-cuspidal `F`-points of `X₁(N)` parametrize the pairs `(E, P)` up to
isomorphism over a separable closure. Such a structure exists if and only if the mod-`N` image of
`W` lies, in some basis, in the subgroup `!![1, *; 0, *]`
(`exists_isGammaOneLevelStructure_iff`). -/
def IsGammaOneLevelStructure : Prop :=
  addOrderOf P = N ∧ ∀ σ : K ≃ₐ[F] K, (W.modGaloisRepresentation N σ).val P = P

/-- An **`X_{±1}(N)`-level structure** `±P` on `W` over `F` (LMFDB `modcurve.xpm1`): a point `P` of
`E[N]` of exact order `N` such that the set `{P, -P}` is Galois-stable, that is, every
`σ : K ≃ₐ[F] K` maps `P` to `P` or to `-P`; `P` and `-P` give the same structure
(`IsGammaPMOneLevelStructure.neg`). The non-cuspidal `F`-points of `X_{±1}(N)` parametrize the
pairs `(E, ±P)` up to isomorphism over a separable closure. Such a structure exists if and only if
the mod-`N` image of `W` lies, in some basis, in the subgroup `!![±1, *; 0, *]`
(`exists_isGammaPMOneLevelStructure_iff`). -/
def IsGammaPMOneLevelStructure : Prop :=
  addOrderOf P = N ∧ ∀ σ : K ≃ₐ[F] K,
    (W.modGaloisRepresentation N σ).val P = P ∨ (W.modGaloisRepresentation N σ).val P = -P

variable {W N P Q}

lemma IsGammaOneLevelStructure.isGammaPMOneLevelStructure (h : W.IsGammaOneLevelStructure N P) :
    W.IsGammaPMOneLevelStructure N P :=
  ⟨h.1, fun σ ↦ .inl (h.2 σ)⟩

lemma IsGammaPMOneLevelStructure.neg (h : W.IsGammaPMOneLevelStructure N P) :
    W.IsGammaPMOneLevelStructure N (-P) :=
  ⟨(addOrderOf_neg P).trans h.1, fun σ ↦ by simpa only [map_neg, neg_inj] using h.2 σ⟩

/-- **`⟨P⟩` is an `X₀(N)`-level structure for an `X_{±1}(N)`-level structure `±P`**: the map
`X_{±1}(N) → X₀(N)`, and through `X₁(N) → X_{±1}(N)` the map `X₁(N) → X₀(N)`. -/
lemma IsGammaPMOneLevelStructure.isGammaZeroLevelStructure (h : W.IsGammaPMOneLevelStructure N P) :
    W.IsGammaZeroLevelStructure N (AddSubgroup.zmultiples P) := by
  refine ⟨inferInstance, (Nat.card_zmultiples P).trans h.1,
    (W.isGaloisStableTorsion_zmultiples_iff N P).mpr fun σ ↦ ?_⟩
  rcases h.2 σ with hσ | hσ <;> rw [hσ]
  · exact AddSubgroup.mem_zmultiples P
  · exact neg_mem (AddSubgroup.mem_zmultiples P)

/-- **For `N ∣ 2` the `X₁(N)`- and `X_{±1}(N)`-level structures coincide**, as `-P = P`. -/
lemma isGammaPMOneLevelStructure_iff_isGammaOneLevelStructure (hN : N ∣ 2) :
    W.IsGammaPMOneLevelStructure N P ↔ W.IsGammaOneLevelStructure N P := by
  have hP : -P = P := neg_eq_of_add_eq_zero_left <| by
    rw [← two_smul (ZMod N), ← Nat.cast_ofNat, (ZMod.natCast_eq_zero_iff 2 N).mpr hN, zero_smul]
  simp only [IsGammaPMOneLevelStructure, IsGammaOneLevelStructure, hP, or_self]

lemma IsGammaOneLevelStructure.units_smul (h : W.IsGammaOneLevelStructure N P) (d : (ZMod N)ˣ) :
    W.IsGammaOneLevelStructure N (d • P) :=
  ⟨(addOrderOf_units_smul d).trans h.1, fun σ ↦ by rw [Units.smul_def, map_smul, h.2 σ]⟩

variable (W N) [DecidableEq (SeparableClosure F)] [W.IsElliptic] in
/-- **The automorphism `[-1]` of `W` acts on `E[N]` by `P ↦ -P`**, `E[N]` being the `N`-torsion
over a separable closure: the pairs `(E, P)` and `(E, -P)` are isomorphic, so the subgroup `{±1}`
of `(ℤ/Nℤ)ˣ` acts trivially on isomorphism classes of `X₁(N)`-level structures. -/
lemma torsionGeometricAutRepresentation_neg_one : W.torsionGeometricAutRepresentation N (-1) = -1 :=
  Units.ext <| LinearMap.ext fun P ↦ by simp [torsionGeometricAutRepresentation]

variable (b : Basis (Fin 2) (ZMod N) (AddSubgroup.torsionBy (W⁄K).toAffine.Point (N : ℤ)))

variable (W N) in
/-- **The mod-`N` image of `W` in a basis `(P, Q)` of `E[N]` lies in the upper triangular subgroup
`!![*, *; 0, *]` if and only if `⟨P⟩` is an `X₀(N)`-level structure.** -/
lemma range_modGaloisRepresentationGL_le_gl2Borel_iff :
    (W.modGaloisRepresentationGL N b).range ≤ GL2Borel (ZMod N) ↔
    W.IsGammaZeroLevelStructure N (AddSubgroup.zmultiples (b 0)) := by
  refine ⟨fun h ↦ ⟨inferInstance, b.natCard_zmultiples 0,
    (W.isGaloisStableTorsion_zmultiples_iff N _).mpr fun σ ↦
      (toLin'_symm_mem_gl2Borel_iff b _).mp (h ⟨σ, rfl⟩)⟩, ?_⟩
  rintro ⟨-, -, h⟩ _ ⟨σ, rfl⟩
  exact (toLin'_symm_mem_gl2Borel_iff b _).mpr
    ((W.isGaloisStableTorsion_zmultiples_iff N _).mp h σ)

variable (W N) in
/-- **The mod-`N` image of `W` in a basis `(P, Q)` of `E[N]` lies in the subgroup `!![1, *; 0, *]`
if and only if `P` is an `X₁(N)`-level structure.** -/
lemma range_modGaloisRepresentationGL_le_gammaOneSubgroup_iff :
    (W.modGaloisRepresentationGL N b).range ≤ gammaOneSubgroup (ZMod N) ↔
    W.IsGammaOneLevelStructure N (b 0) := by
  refine ⟨fun h ↦ ⟨b.addOrderOf_eq 0, fun σ ↦
    (toLin'_symm_mem_gammaOneSubgroup_iff b _).mp (h ⟨σ, rfl⟩)⟩, ?_⟩
  rintro ⟨-, h⟩ _ ⟨σ, rfl⟩
  exact (toLin'_symm_mem_gammaOneSubgroup_iff b _).mpr (h σ)

variable (W N) in
/-- **The mod-`N` image of `W` in a basis `(P, Q)` of `E[N]` lies in the subgroup
`!![±1, *; 0, *]` if and only if `±P` is an `X_{±1}(N)`-level structure.** -/
lemma range_modGaloisRepresentationGL_le_gammaPMOneSubgroup_iff :
    (W.modGaloisRepresentationGL N b).range ≤ gammaPMOneSubgroup (ZMod N) ↔
    W.IsGammaPMOneLevelStructure N (b 0) := by
  refine ⟨fun h ↦ ⟨b.addOrderOf_eq 0, fun σ ↦
    (toLin'_symm_mem_gammaPMOneSubgroup_iff b _).mp (h ⟨σ, rfl⟩)⟩, ?_⟩
  rintro ⟨-, h⟩ _ ⟨σ, rfl⟩
  exact (toLin'_symm_mem_gammaPMOneSubgroup_iff b _).mpr (h σ)

variable [NeZero N]

/-- **The fibres of `P ↦ ⟨P⟩` on `X₁(N)`-level structures are the orbits of `(ℤ/Nℤ)ˣ`**: a point
`Q` generates the same `X₀(N)`-level structure as `P` if and only if `Q = dP` for a unit `d` of
`ℤ/Nℤ`, and `dP` is again an `X₁(N)`-level structure (`IsGammaOneLevelStructure.units_smul`), so
that `X₀(N)` is the quotient of `X₁(N)` by `(ℤ/Nℤ)ˣ`, acting by `(E, P) ↦ (E, dP)`. -/
lemma IsGammaOneLevelStructure.zmultiples_eq_iff (h : W.IsGammaOneLevelStructure N P) :
    AddSubgroup.zmultiples Q = AddSubgroup.zmultiples P ↔ ∃ d : (ZMod N)ˣ, Q = d • P :=
  ZMod.zmultiples_eq_zmultiples_iff h.1

variable [IsSepClosed K] [W.IsElliptic]

variable (W N) in
/-- **`W` carries an `X₀(N)`-level structure if and only if its mod-`N` image lies, in some basis
of `E[N]`, in the upper triangular subgroup**, over a separably closed field in which `N` is
invertible: a generator of the cyclic subgroup is the first vector of a basis. -/
lemma exists_isGammaZeroLevelStructure_iff (hN : (N : K) ≠ 0) :
    (∃ C, W.IsGammaZeroLevelStructure (K := K) N C) ↔
    ∃ b, (W.modGaloisRepresentationGL (K := K) N b).range ≤ GL2Borel (ZMod N) := by
  refine ⟨?_, fun ⟨b, hb⟩ ↦ ⟨_, (W.range_modGaloisRepresentationGL_le_gl2Borel_iff N b).mp hb⟩⟩
  rintro ⟨C, hC, hcard, hs⟩
  rcases (W⁄K).nonempty_basis_torsionBy N hN with ⟨b⟩
  rcases (AddSubgroup.isAddCyclic_iff_exists_zmultiples_eq_top C).mp hC with ⟨P, rfl⟩
  rcases b.exists_zmultiples_sup_eq_top ((Nat.card_zmultiples P).symm.trans hcard) with ⟨Q, hPQ⟩
  refine ⟨b.ofSupEqTop hPQ, (W.range_modGaloisRepresentationGL_le_gl2Borel_iff N _).mpr ?_⟩
  rw [b.ofSupEqTop_apply_zero]
  exact ⟨hC, hcard, hs⟩

variable (W N) in
/-- **`W` carries an `X₁(N)`-level structure if and only if its mod-`N` image lies, in some basis
of `E[N]`, in the subgroup `!![1, *; 0, *]`**, over a separably closed field in which `N` is
invertible: the point is the first vector of a basis. -/
lemma exists_isGammaOneLevelStructure_iff (hN : (N : K) ≠ 0) :
    (∃ P, W.IsGammaOneLevelStructure (K := K) N P) ↔
    ∃ b, (W.modGaloisRepresentationGL (K := K) N b).range ≤ gammaOneSubgroup (ZMod N) := by
  refine ⟨?_, fun ⟨b, hb⟩ ↦
    ⟨_, (W.range_modGaloisRepresentationGL_le_gammaOneSubgroup_iff N b).mp hb⟩⟩
  rintro ⟨P, hP⟩
  rcases (W⁄K).nonempty_basis_torsionBy N hN with ⟨b⟩
  rcases b.exists_zmultiples_sup_eq_top hP.1 with ⟨Q, hPQ⟩
  refine ⟨b.ofSupEqTop hPQ, (W.range_modGaloisRepresentationGL_le_gammaOneSubgroup_iff N _).mpr ?_⟩
  rwa [b.ofSupEqTop_apply_zero]

variable (W N) in
/-- **`W` carries an `X_{±1}(N)`-level structure if and only if its mod-`N` image lies, in some
basis of `E[N]`, in the subgroup `!![±1, *; 0, *]`**, over a separably closed field in which `N` is
invertible: the point is the first vector of a basis. -/
lemma exists_isGammaPMOneLevelStructure_iff (hN : (N : K) ≠ 0) :
    (∃ P, W.IsGammaPMOneLevelStructure (K := K) N P) ↔
    ∃ b, (W.modGaloisRepresentationGL (K := K) N b).range ≤ gammaPMOneSubgroup (ZMod N) := by
  refine ⟨?_, fun ⟨b, hb⟩ ↦
    ⟨_, (W.range_modGaloisRepresentationGL_le_gammaPMOneSubgroup_iff N b).mp hb⟩⟩
  rintro ⟨P, hP⟩
  rcases (W⁄K).nonempty_basis_torsionBy N hN with ⟨b⟩
  rcases b.exists_zmultiples_sup_eq_top hP.1 with ⟨Q, hPQ⟩
  refine ⟨b.ofSupEqTop hPQ,
    (W.range_modGaloisRepresentationGL_le_gammaPMOneSubgroup_iff N _).mpr ?_⟩
  rwa [b.ofSupEqTop_apply_zero]

end WeierstrassCurve
