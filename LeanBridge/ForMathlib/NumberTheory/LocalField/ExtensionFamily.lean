import LeanBridge.ForMathlib.FieldTheory.AlgebraGaloisClosure
import LeanBridge.ForMathlib.NumberTheory.LocalField.HerbrandInvariantFamily
import Mathlib.NumberTheory.Padics.PadicNumbers
import TauCeti.NumberTheory.LocalField.Herbrand.Basic
import TauCeti.NumberTheory.LocalField.Unramified.Factorization

/-!
# Families of extensions of `p`-adic fields, their field counts and masses

Let `K` be a nonarchimedean local field and `K̄` its algebraic closure, which contains a copy of
every finite extension of `K`. The finite extensions of `K` are taken to be the intermediate fields
of `K̄ / K` of finite degree, and a family of extensions of `K`, of base field `K`, is a set of
`K`-isomorphism classes of them.

The Swan slopes of a finite separable extension `L / K` that need not be Galois are, after Deligne,
its positive upper ramification breaks. Let `M` be the Galois closure of `L` in `K̄`, with group
`G`, lower ramification groups `G_i` and Herbrand function `φ`, and `H = Gal(M / L)`. The upper
ramification groups `G^u` act on `Hom_K(L, M) ≅ G / H`, the orbits of the normal subgroup `G^u`
having `[G^u : G^u ∩ H]` elements, and the Swan slopes are the `u > 0` at which these orbits shrink,
each repeated `m` times when they shrink by the factor `p ^ m`. Since `G^{φ(i)} = G_i` and
`G^{φ(i)+} = G_{i + 1}` (`IsNonarchimedeanLocalField.upperRamificationGroup_eq_of_mem_Ioc`), they
are the `φ(i)` for the integers `i ≥ 1`, repeated `log_p (n_i / n_{i + 1})` times for
`n_i = [G_i : G_i ∩ H]`, which is how they are defined here. For `L = M`, `H = 1` and these are the
Swan slopes of the Galois extension `L / K`, `IsNonarchimedeanLocalField.swanSlopesOfIsGalois`. The
LMFDB reads them off the lower convex hull of the points `([E : K], v_K(disc(E / K)))` of the
subextensions `E` of `L / K`, a segment of slope `1 + s` from `n_1` to `n_2 = p ^ m n_1` giving the
Swan slope `s` `m` times (LMFDB `lf.slopes`), and states that these are the positive upper breaks;
this agreement is not proved here.

For a `p`-adic field `K` (of characteristic zero) and a Herbrand invariant `I = (r_1, …, r_w)_ε^f`,
the family `I / K` is the set of classes of the extensions `L / K` of residue degree `f`,
ramification index `ε p ^ w` and Swan slopes the Swan slopes `s_1, …, s_w` of `I`, the residue
degree, ramification index and ramification groups of `L` being those of Tau Ceti's spectral-norm
local-field structure. Its field count is its number of elements, `0` if it were infinite; that it
is finite (Krasner) is not proved. Let `K_f` be the unramified extension of `K` of degree `f` in
`K̄`, which lies in every extension in `I / K`
(`IsNonarchimedeanLocalField.HerbrandInvariant.unramifiedExtension_le_of_isInvariantOf`). The mass
of `L` is `1 / |Aut(L / K_f)|` and, when `ℚ_p ⊆ K`, its absolute mass is `1 / |Aut(L / ℚ_p)|`; both
are invariant under `K`-isomorphism, and the masses of `I / K` are their sums over `I / K`.

The knowl states that the mass is `f` times the absolute mass when `K = ℚ_p`. This is false for
these sums over the `ℚ_p`-isomorphism classes, the elements of `I / ℚ_p`: for `p ≡ 2 mod 3` and
`I = ()_3^2`, `I / ℚ_p` consists of the classes of `K_2(p^{1/3})`, Galois over `ℚ_p`, and of
`K_2((u p)^{1/3})` for a unit `u` of `K_2` that is not a cube, no automorphism of which moves
`K_2`, of masses `1/3` and `1/3` and absolute masses `1/6` and `1/3`. It holds for the sums over the
`K_f`-isomorphism classes, which count `K_2((u p)^{1/3})` and `K_2((u² p)^{1/3})` apart.

## Main definitions

* `IsNonarchimedeanLocalField.FiniteExtension` and `IsNonarchimedeanLocalField.ExtensionClass`: the
  finite extensions of `K` inside `K̄` and their `K`-isomorphism classes.
* `IsNonarchimedeanLocalField.ExtensionFamily` (LMFDB `lf.family_base`): the families of extensions
  of base field `K`.
* `IsNonarchimedeanLocalField.visibleSwanSlopes` (LMFDB `lf.slopes`): the Swan slopes of a finite
  separable extension.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf` (LMFDB `lf.herbrand_invariant`): an
  extension has a given Herbrand invariant.
* `IsNonarchimedeanLocalField.HerbrandInvariant.family` (LMFDB `lf.family_polynomial`,
  `lf.family_base`): the family `I / K`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.fieldCount` (LMFDB `lf.family_field_count`).
* `IsNonarchimedeanLocalField.extensionMass` and `IsNonarchimedeanLocalField.absoluteExtensionMass`
  (LMFDB `lf.family_mass`): the mass and absolute mass of an extension.
* `IsNonarchimedeanLocalField.HerbrandInvariant.mass` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.absoluteMass` (LMFDB `lf.family_mass`): the mass
  and absolute mass of a family.

## Main results

* `IsNonarchimedeanLocalField.extensionMass_eq_of_algEquiv` and
  `IsNonarchimedeanLocalField.absoluteExtensionMass_eq_of_algEquiv`: the masses of an extension
  depend only on its `K`-isomorphism class.
* `IsNonarchimedeanLocalField.HerbrandInvariant.unramifiedExtension_le_of_isInvariantOf`: `K_f` lies
  in every extension in `I / K`.
-/

open ValuativeRel TauCeti LocalFieldsRamification Finset

namespace IsNonarchimedeanLocalField

variable (K : Type*) [Field K] {p : ℕ}

/-- The **finite extensions** of a field `K`, as the intermediate fields of finite degree of
`K̄ / K` for the algebraic closure `K̄` of `K`. Every finite extension of `K` is `K`-isomorphic to
one of them. -/
abbrev FiniteExtension : Type _ :=
  {L : IntermediateField K (AlgebraicClosure K) // FiniteDimensional K L}

/-- `K`-isomorphism of finite extensions of `K`. -/
def finiteExtensionSetoid : Setoid (FiniteExtension K) where
  r L L' := Nonempty (L.1 ≃ₐ[K] L'.1)
  iseqv := ⟨fun _ ↦ ⟨.refl⟩, fun ⟨e⟩ ↦ ⟨e.symm⟩, fun ⟨e⟩ ⟨e'⟩ ↦ ⟨e.trans e'⟩⟩

/-- The **`K`-isomorphism classes** of finite extensions of a field `K`. -/
abbrev ExtensionClass : Type _ :=
  Quotient (finiteExtensionSetoid K)

/-- A **family of extensions** of a field `K` (LMFDB `lf.family_base`), whose **base field** is `K`:
a set of `K`-isomorphism classes of finite extensions `L / K`. The LMFDB takes `K` a `p`-adic
field. -/
abbrev ExtensionFamily : Type _ :=
  Set (ExtensionClass K)

variable {K} {L L' : IntermediateField K (AlgebraicClosure K)}

lemma coe_algEquiv_mem_of_normal {E : IntermediateField K (AlgebraicClosure K)} [Normal K E]
    (φ : L ≃ₐ[K] L') {x : L} (hx : (x : AlgebraicClosure K) ∈ E) :
    (φ x : AlgebraicClosure K) ∈ E := by
  have h : φ.toAlgHom.liftNormal (AlgebraicClosure K) x = φ x :=
    φ.toAlgHom.liftNormal_commutes (AlgebraicClosure K) x
  rw [← h]
  exact IntermediateField.normal_iff_forall_map_le.mp ‹_›
    (φ.toAlgHom.liftNormal (AlgebraicClosure K)) ⟨x, hx, rfl⟩

variable (p L) [Fact p.Prime] [Algebra ℚ_[p] K] in
/-- The **absolute mass** `1 / |Aut(L / ℚ_p)|` (LMFDB `lf.family_mass`) of an extension `L` of a
field `K` containing `ℚ_p`, such as a `p`-adic field, inside `K̄`, and `0` if `Aut(L / ℚ_p)` were
infinite. -/
noncomputable def absoluteExtensionMass : ℚ :=
  (Nat.card (L ≃ₐ[ℚ_[p]] L))⁻¹

variable (p) [Fact p.Prime] [Algebra ℚ_[p] K] in
/-- **The absolute mass of an extension depends only on its `K`-isomorphism class.** -/
lemma absoluteExtensionMass_eq_of_algEquiv (φ : L ≃ₐ[K] L') :
    absoluteExtensionMass p L = absoluteExtensionMass p L' :=
  congrArg (fun n : ℕ ↦ (n : ℚ)⁻¹) <| Nat.card_congr (φ.restrictScalars ℚ_[p]).autCongr.toEquiv

variable [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] (f : ℕ)

variable (L) in
/-- The **mass** `1 / |Aut(L / K_f)|` (LMFDB `lf.family_mass`) of an extension `L` of a
nonarchimedean local field `K` inside `K̄`, for `K_f` the unramified extension of `K` of degree `f`
in `K̄` (Tau Ceti's `TauCeti.unramifiedExtension`), and `0` if this group were infinite. Here
`Aut(L / K_f)` is the group of automorphisms of `L / K` fixing the elements of `L` in `K_f`, which
is the group of automorphisms of `L / K_f` when `K_f ⊆ L`, as for the extensions of residue degree
`f` (`HerbrandInvariant.unramifiedExtension_le_of_isInvariantOf`). -/
noncomputable def extensionMass : ℚ :=
  (Nat.card (fixingSubgroup (L ≃ₐ[K] L)
    (((↑) : L → AlgebraicClosure K) ⁻¹' unramifiedExtension K (AlgebraicClosure K) f)))⁻¹

/-- **The mass of an extension depends only on its `K`-isomorphism class**: a `K`-isomorphism
`L ≃ L'` maps the elements of `L` in `K_f` to those of `L'`, `K_f` being normal over `K`. -/
lemma extensionMass_eq_of_algEquiv (φ : L ≃ₐ[K] L') : extensionMass L f = extensionMass L' f := by
  refine congrArg (fun n : ℕ ↦ (n : ℚ)⁻¹) <| Nat.card_congr <|
    φ.autCongr.toEquiv.subtypeEquiv fun σ ↦ ?_
  simp only [mem_fixingSubgroup_iff, Set.mem_preimage]
  refine ⟨fun h y hy ↦ ?_, fun h x hx ↦ ?_⟩
  · exact (congrArg φ (h (φ.symm y) (coe_algEquiv_mem_of_normal φ.symm hy))).trans
      (φ.apply_symm_apply y)
  · have h' : φ (σ (φ.symm (φ x))) = φ x := h (φ x) (coe_algEquiv_mem_of_normal φ hx)
    rw [φ.symm_apply_apply] at h'
    exact φ.injective h'

variable (L) in
/-- The **Swan slopes** (LMFDB `lf.slopes`), or visible Swan slopes, of a finite separable extension
`L` of a nonarchimedean local field `K` inside `K̄`, which need not be Galois: its positive upper
ramification breaks, in the sense of Deligne. With `M` the Galois closure of `L` in `K̄`, `G_i` the
lower ramification groups of `M / K`, `φ` its Herbrand function and `H = Gal(M / L)`, they are the
`φ(i)` for the integers `i ≥ 1`, each repeated `log_p (n_i / n_{i + 1})` times, where
`n_i = [G_i : G_i ∩ H]` is the size of the orbits of `G_i = G^{φ(i)}` on `Hom_K(L, M) ≅ G / H`.
The Galois closure carries Tau Ceti's spectral-norm local-field structure. -/
noncomputable def visibleSwanSlopes [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Multiset ℝ :=
  letI : ValuativeRel (Algebra.galoisClosure K L) := finiteIntermediateFieldValuativeRel K _ _
  letI : TopologicalSpace (Algebra.galoisClosure K L) := finiteIntermediateFieldTopology K _ _
  haveI : IsNonarchimedeanLocalField (Algebra.galoisClosure K L) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  haveI : ValuativeExtension K (Algebra.galoisClosure K L) :=
    finiteIntermediateField_valuativeExtension K _ _
  ∑ i ∈ range (largestLowerJump K (Algebra.galoisClosure K L)).toNat,
    Multiset.replicate (padicValNat (ringChar 𝓀[K])
      ((fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L)).relIndex
        (lowerRamificationGroup K (Algebra.galoisClosure K L) (i + 1)) /
      (fixingSubgroup _ (((↑) : Algebra.galoisClosure K L → AlgebraicClosure K) ⁻¹' L)).relIndex
        (lowerRamificationGroup K (Algebra.galoisClosure K L) (i + 2))))
      (herbrand K (Algebra.galoisClosure K L)
        ⟨(i + 1 : ℕ), Nat.cast_mem_ramificationIndexDomain (i + 1)⟩)

namespace HerbrandInvariant

variable (K) (I : HerbrandInvariant p) [CharZero K] [FiniteDimensional K L]

variable (L) in
/-- A finite extension `L` of a `p`-adic field `K` inside `K̄` **has Herbrand invariant**
`I = (r_1, …, r_w)_ε^f` (LMFDB `lf.herbrand_invariant`) if it has residue degree `f`, ramification
index `ε p ^ w` and Swan slopes the Swan slopes `s_1, …, s_w` of `I`, for Tau Ceti's spectral-norm
local-field structure on `L`. -/
def IsInvariantOf : Prop :=
  letI : ValuativeRel L := finiteIntermediateFieldValuativeRel K _ L
  letI : TopologicalSpace L := finiteIntermediateFieldTopology K _ L
  haveI : IsNonarchimedeanLocalField L := finiteIntermediateField_isNonarchimedeanLocalField K _ L
  haveI : ValuativeExtension K L := finiteIntermediateField_valuativeExtension K _ L
  inertiaDegree K L = I.f ∧ ramificationIndex K L = I.ε * p ^ I.w ∧
    visibleSwanSlopes L = (Multiset.range I.w).map fun k ↦ (I.swanSlope (k + 1) : ℝ)

/-- The **family** `I / K` (LMFDB `lf.family_polynomial`) of a Herbrand invariant
`I = (r_1, …, r_w)_ε^f` over a `p`-adic field `K`, its **base field** (LMFDB `lf.family_base`): the
set of `K`-isomorphism classes of the finite extensions `L / K` of residue degree `f`, ramification
index `ε p ^ w` and Swan slopes the Swan slopes `s_1, …, s_w` of `I`. -/
def family : ExtensionFamily K :=
  Quotient.mk _ '' {E : FiniteExtension K | haveI : FiniteDimensional K E.1 := E.2
    I.IsInvariantOf K E.1}

/-- The **field count** (LMFDB `lf.family_field_count`) of a family `I / K`: the number of
extensions in `I / K`, up to `K`-isomorphism, and `0` if there were infinitely many. There are
finitely many extensions of `K` of given degree (Krasner), which is not proved here. -/
noncomputable def fieldCount : ℕ :=
  (I.family K).ncard

/-- The **mass of the family** `I / K` (LMFDB `lf.family_mass`), `I = (r_1, …, r_w)_ε^f`: the sum
of the masses `1 / |Aut(L / K_f)|` of the extensions `L` in `I / K`, well defined on
`K`-isomorphism classes by `extensionMass_eq_of_algEquiv`, and `0` if `I / K` were infinite. -/
noncomputable def mass : ℚ :=
  ∑ᶠ c ∈ I.family K, c.liftOn (fun E ↦ extensionMass E.1 I.f) fun _ _ ⟨φ⟩ ↦
    extensionMass_eq_of_algEquiv I.f φ

variable [Fact p.Prime] [Algebra ℚ_[p] K] in
/-- The **absolute mass of the family** `I / K` (LMFDB `lf.family_mass`) over a `p`-adic field
`K ⊇ ℚ_p`: the sum of the absolute masses `1 / |Aut(L / ℚ_p)|` of the extensions `L` in `I / K`,
well defined on `K`-isomorphism classes by `absoluteExtensionMass_eq_of_algEquiv`, and `0` if
`I / K` were infinite. -/
noncomputable def absoluteMass : ℚ :=
  ∑ᶠ c ∈ I.family K, c.liftOn (fun E ↦ absoluteExtensionMass p E.1) fun _ _ ⟨φ⟩ ↦
    absoluteExtensionMass_eq_of_algEquiv p φ

variable {K I}

/-- **The unramified extension `K_f` of degree `f` lies in every extension with Herbrand invariant
`I = (r_1, …, r_w)_ε^f`**: such an extension has residue degree `f`, so it contains a primitive
`(q ^ f - 1)`-th root of unity, which generates `K_f`. -/
lemma unramifiedExtension_le_of_isInvariantOf (hL : I.IsInvariantOf K L) :
    unramifiedExtension K (AlgebraicClosure K) I.f ≤ L := by
  let v : ValuativeRel L := finiteIntermediateFieldValuativeRel K _ L
  let t : TopologicalSpace L := finiteIntermediateFieldTopology K _ L
  have : IsNonarchimedeanLocalField L := finiteIntermediateField_isNonarchimedeanLocalField K _ L
  have : ValuativeExtension K L := finiteIntermediateField_valuativeExtension K _ L
  rcases exists_isPrimitiveRoot_natCard_pow_inertiaDegree_sub_one K L with ⟨ζ, hζ⟩
  rw [hL.1] at hζ
  rw [unramifiedExtension_eq_adjoin_simple I.f_pos.ne'
    (hζ.map_of_injective (algebraMap L (AlgebraicClosure K)).injective)]
  exact IntermediateField.adjoin_simple_le_iff.mpr ζ.2

end HerbrandInvariant

end IsNonarchimedeanLocalField
