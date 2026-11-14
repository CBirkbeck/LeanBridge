import LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Level
import Mathlib.Algebra.Group.Conj

/-!
# Gassmann classes of open subgroups of `GL₂(ℤ̂)`

Two subgroups `H₁` and `H₂` of a finite group `G` are Gassmann equivalent if `|C ∩ H₁| = |C ∩ H₂|`
for every conjugacy class `C` of `G`. Two open subgroups of `GL₂(ℤ̂)` are Gassmann equivalent if
their reductions modulo `N` are Gassmann equivalent in `GL₂(ℤ/Nℤ)`, where `N` is the least common
multiple of their levels: both are then inverse images of their reductions modulo `N`, so this is
Gassmann equivalence in the finite quotient `GL₂(ℤ/Nℤ)` of `GL₂(ℤ̂)` through which they both
factor. As in `LeanBridge.ForMathlib.LinearAlgebra.Matrix.GL2.Level`, `GL₂(ℤ̂)` is the product
`∏_ℓ GL₂(ℤ_ℓ)` and `GL₂(ℤ/Nℤ)` the product `∏_ℓ GL₂(ℤ / ℓ ^ v_ℓ(N) ℤ)`.

That Gassmann equivalence does not depend on the choice of the multiple `N` of the levels, and
that Gassmann equivalent open subgroups have the same level, index and genus, and modular curves
with isogenous Jacobians (Prasad–Rajan), are not formalised.

## Main definitions

* `Subgroup.IsGassmannEquivalent` (LMFDB `group.gassmann_equivalence`): Gassmann equivalence of
  subgroups.
* `Matrix.GeneralLinearGroup.IsAdelicGassmannEquivalent`: Gassmann equivalence of open subgroups of
  `GL₂(ℤ̂)`.
* `Matrix.GeneralLinearGroup.gassmannClass` (LMFDB `modcurve.gassmann_class`): the Gassmann class.

## Main results

* `Subgroup.isGassmannEquivalent_equivalence`: Gassmann equivalence is an equivalence relation.
* `Subgroup.isGassmannEquivalent_of_equiv` and `Subgroup.isGassmannEquivalent_range`: subgroups
  matched by a conjugacy-preserving bijection, for instance the images of two embeddings that
  agree up to conjugacy, are Gassmann equivalent.
* `Subgroup.natCard_inter_eq_sum` (LMFDB `group.computing_subgroup_labels`): the LMFDB's running
  tally computes the Gassmann vector, `|C ∩ H|` being the sum of the sizes of the conjugacy classes
  of `H` that lie in `C`.
* `Matrix.GeneralLinearGroup.mem_gassmannClass_self`: an open subgroup is in its Gassmann class.
-/

namespace Subgroup

variable {G X : Type*} [Group G] [Group X] {H K : Subgroup G}

/-- Two subgroups `H₁` and `H₂` of a group `G` are **Gassmann equivalent** (LMFDB
`group.gassmann_equivalence`) if `|C ∩ H₁| = |C ∩ H₂|` for every conjugacy class `C` of `G`. The
LMFDB applies this to finite groups `G`; for infinite `G` the cardinalities are `Nat.card`, which is
`0` on infinite sets. -/
def IsGassmannEquivalent (H₁ H₂ : Subgroup G) : Prop :=
  ∀ C : ConjClasses G, Nat.card ↥(C.carrier ∩ H₁) = Nat.card ↥(C.carrier ∩ H₂)

/-- **Gassmann equivalence is an equivalence relation.** -/
lemma isGassmannEquivalent_equivalence : Equivalence (IsGassmannEquivalent (G := G)) :=
  ⟨fun _ _ ↦ rfl, fun h C ↦ (h C).symm, fun h h' C ↦ (h C).trans (h' C)⟩

/-- **Subgroups matched by a conjugacy-preserving bijection are Gassmann equivalent**: if
`e : H ≃ K` sends every `h` to a conjugate of `h` in `G`, it maps `C ∩ H` onto `C ∩ K` for every
conjugacy class `C` of `G`. -/
lemma isGassmannEquivalent_of_equiv (e : H ≃ K) (he : ∀ h, IsConj (e h : G) h) :
    H.IsGassmannEquivalent K := fun C ↦ by
  have hmem (h : H) : (e h : G) ∈ C.carrier ↔ (h : G) ∈ C.carrier := by
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mem_carrier_iff_mk_eq,
      ConjClasses.mk_eq_mk_iff_isConj.mpr (he h)]
  exact Nat.card_congr
    { toFun x := ⟨e ⟨x, x.2.2⟩, (hmem _).mpr x.2.1, (e _).2⟩
      invFun y := ⟨e.symm ⟨y, y.2.2⟩, (hmem _).mp (by rw [e.apply_symm_apply]; exact y.2.1),
        (e.symm _).2⟩
      left_inv x := by simp
      right_inv y := by simp }

/-- **The images of two embeddings that agree up to conjugacy are Gassmann equivalent**: if
`f, g : X →* G` are injective and `f x` is conjugate to `g x` for every `x`, then `f.range` and
`g.range` are Gassmann equivalent. -/
lemma isGassmannEquivalent_range {f g : X →* G} (hf : Function.Injective f)
    (hg : Function.Injective g) (hfg : ∀ x, IsConj (f x) (g x)) :
    f.range.IsGassmannEquivalent g.range :=
  isGassmannEquivalent_of_equiv ((MonoidHom.ofInjective hf).symm.trans
    (MonoidHom.ofInjective hg)).toEquiv fun h ↦ by
      simpa [MonoidHom.ofInjective_apply] using (hfg ((MonoidHom.ofInjective hf).symm h)).symm

open scoped Classical in
/-- **The LMFDB's running tally counts the elements of `H` in a conjugacy class of `G`** (LMFDB
`group.computing_subgroup_labels`): each conjugacy class `D` of `H` lies in the conjugacy class
`D.map H.subtype` of `G`, and the number of elements of `H` in a conjugacy class `C` of `G` is the
sum of the sizes of the conjugacy classes of `H` lying in `C`. -/
lemma natCard_inter_eq_sum [Finite H] [Fintype (ConjClasses H)] (C : ConjClasses G) :
    Nat.card ↥(C.carrier ∩ H) =
      ∑ D : ConjClasses H with D.map H.subtype = C, Nat.card D.carrier := by
  let f : {h : H // ConjClasses.mk (h : G) = C} → {D : ConjClasses H // D.map H.subtype = C} :=
    fun h ↦ ⟨ConjClasses.mk h.1, h.2⟩
  refine (Nat.card_congr <|
    ({ toFun x := ⟨⟨x, x.2.2⟩, ConjClasses.mem_carrier_iff_mk_eq.mp x.2.1⟩
       invFun y := ⟨y.1, ConjClasses.mem_carrier_iff_mk_eq.mpr y.2, y.1.2⟩ } :
      ↥(C.carrier ∩ H) ≃ {h : H // ConjClasses.mk (h : G) = C}).trans <|
    (Equiv.sigmaFiberEquiv f).symm.trans <| Equiv.sigmaCongrRight fun D ↦
      ({ toFun y := ⟨y.1.1, ConjClasses.mem_carrier_iff_mk_eq.mpr (congrArg Subtype.val y.2)⟩
         invFun h := ⟨⟨h.1, (congrArg (ConjClasses.map H.subtype)
           (ConjClasses.mem_carrier_iff_mk_eq.mp h.2)).trans D.2⟩,
           Subtype.ext (ConjClasses.mem_carrier_iff_mk_eq.mp h.2)⟩ } :
        {y // f y = D} ≃ ↥D.1.carrier)).trans ?_
  rw [Nat.card_sigma]
  exact (Finset.sum_subtype (Finset.univ.filter fun D : ConjClasses H ↦ D.map H.subtype = C)
    (fun D ↦ by simp) fun D ↦ Nat.card D.carrier).symm

end Subgroup

namespace Matrix.GeneralLinearGroup

variable (H H' : Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]))

/-- Two open subgroups `H` and `H'` of `GL₂(ℤ̂)` are **Gassmann equivalent** if their reductions
modulo the least common multiple `N` of their levels are Gassmann equivalent subgroups of the
finite group `GL₂(ℤ/Nℤ)`. -/
def IsAdelicGassmannEquivalent : Prop :=
  (H.map (adelicReduction ((adelicLevel ⊤ H).lcm (adelicLevel ⊤ H')))).IsGassmannEquivalent
    (H'.map (adelicReduction ((adelicLevel ⊤ H).lcm (adelicLevel ⊤ H'))))

/-- The **Gassmann class** (LMFDB `modcurve.gassmann_class`) of an open subgroup `H` of `GL₂(ℤ̂)`:
the set of open subgroups of `GL₂(ℤ̂)` that are Gassmann equivalent to `H`. -/
def gassmannClass : Set (Subgroup (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ])) :=
  {H' | IsOpen (H' : Set (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ])) ∧ IsAdelicGassmannEquivalent H H'}

/-- **An open subgroup of `GL₂(ℤ̂)` is in its Gassmann class.** -/
lemma mem_gassmannClass_self (hH : IsOpen (H : Set (∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]))) :
    H ∈ gassmannClass H :=
  ⟨hH, fun _ ↦ rfl⟩

end Matrix.GeneralLinearGroup
