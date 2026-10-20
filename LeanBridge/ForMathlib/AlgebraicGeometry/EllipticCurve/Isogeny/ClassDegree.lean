import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Isogeny.Class

/-!
# The degree of an isogeny class

The degree of the isogeny class of an elliptic curve `W` over a field `K` is the least common
multiple of the degrees of the cyclic isogenies over `K` between curves in the class.

When the curves have complex multiplication defined over `K`, there are cyclic isogenies of
infinitely many degrees between any two curves of the class, so these degrees have no common
multiple; the degree of the class is then `0` here.

## Main definitions

* `WeierstrassCurve.IsomorphismClass.cyclicIsogenyDegrees`: the degrees of the cyclic isogenies over
  `K` from an elliptic curve in one isomorphism class to one in another.
* `WeierstrassCurve.isogenyClassCyclicDegrees`: the degrees of the cyclic isogenies over `K`
  between curves in the isogeny class of `W`.
* `WeierstrassCurve.isogenyClassDegree` (LMFDB `ec.isogeny_class_degree`): their least common
  multiple.

## Main results

* `WeierstrassCurve.IsomorphismClass.mk_mem_cyclicIsogenyDegrees_iff`: the degrees of the cyclic
  isogenies between two isomorphism classes are those between any curves in them.
* `WeierstrassCurve.isogenyClassDegree_eq_lcm`: when there are finitely many such degrees, the
  degree of the isogeny class is their least common multiple `Finset.lcm`.
* `WeierstrassCurve.isogenyClassDegree_eq_of_isIsogenous`: isogenous elliptic curves have the same
  isogeny class degree.
-/

open TauCeti

namespace WeierstrassCurve

variable {K : Type*} [Field K] {W W' : WeierstrassCurve K} {c c' : IsomorphismClass K} {n : ℕ}

variable (c c') in
/-- The degrees of the cyclic isogenies over `K` (`TauCeti.Isogeny.IsCyclic`) from an elliptic
curve in the isomorphism class `c` to an elliptic curve in the isomorphism class `c'`. -/
def IsomorphismClass.cyclicIsogenyDegrees : Set ℕ :=
  {n | ∃ (W₁ W₂ : WeierstrassCurve K) (_ : W₁.IsElliptic) (_ : W₂.IsElliptic), ⟦W₁⟧ = c ∧
    ⟦W₂⟧ = c' ∧ ∃ φ : Isogeny W₁.toAffine W₂.toAffine, φ.IsCyclic ∧ φ.degree = n}

/-- **The cyclic degrees between two isomorphism classes are those between any of their curves**:
composing with isomorphisms keeps an isogeny cyclic and its degree. -/
lemma IsomorphismClass.mk_mem_cyclicIsogenyDegrees_iff {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic]
    [W₂.IsElliptic] : n ∈ cyclicIsogenyDegrees ⟦W₁⟧ ⟦W₂⟧ ↔ ∃ φ : Isogeny W₁.toAffine W₂.toAffine,
    φ.IsCyclic ∧ φ.degree = n := by
  refine ⟨?_, fun ⟨φ, hφ, hn⟩ ↦ ⟨W₁, W₂, ‹_›, ‹_›, rfl, rfl, φ, hφ, hn⟩⟩
  rintro ⟨V₁, V₂, _, _, h₁, h₂, φ, hφ, rfl⟩
  rcases mk_eq_mk_iff.mp h₁ with ⟨C₁, rfl⟩
  rcases mk_eq_mk_iff.mp h₂.symm with ⟨C₂, rfl⟩
  refine ⟨(Isogeny.variableChangeIsogeny C₂ rfl).comp
    (φ.comp (Isogeny.variableChangeIsogeny C₁ rfl)), ?_, by simp⟩
  rw [Isogeny.isCyclic_comp_iff_of_comp_eq_id _ <| Isogeny.variableChangeIsogeny_inv_comp C₂ rfl <|
    inv_smul_smul C₂ V₂, Isogeny.comp_isCyclic_iff_of_comp_eq_id _
    (Isogeny.variableChangeIsogeny_inv_comp C₁ rfl <| inv_smul_smul C₁ W₁) (by simp)]
  exact hφ

lemma IsomorphismClass.pos_of_mem_cyclicIsogenyDegrees (h : n ∈ c.cyclicIsogenyDegrees c') :
    0 < n := by
  rcases h with ⟨W₁, W₂, -, -, -, -, φ, -, rfl⟩
  exact φ.degree_pos

variable (W) in
/-- The degrees of the cyclic isogenies over `K` (`TauCeti.Isogeny.IsCyclic`) between elliptic
curves in the isogeny class of `W`. -/
def isogenyClassCyclicDegrees : Set ℕ :=
  ⋃ c ∈ W.isogenyClass, ⋃ c' ∈ W.isogenyClass, c.cyclicIsogenyDegrees c'

variable (W) in
/-- The **isogeny class degree** (LMFDB `ec.isogeny_class_degree`) of an elliptic curve `W` over
`K`: the least common multiple of the degrees of the cyclic isogenies over `K` between curves in
the isogeny class of `W` (`isogenyClassCyclicDegrees`), that is, their least positive common
multiple. It is `0` if these degrees have no common multiple, as happens when the curves have
complex multiplication over `K`: then there are cyclic isogenies of infinitely many degrees. -/
noncomputable def isogenyClassDegree : ℕ :=
  sInf {m | 0 < m ∧ ∀ n ∈ W.isogenyClassCyclicDegrees, n ∣ m}

variable (hn : n ∈ W.isogenyClassCyclicDegrees)

include hn in
lemma pos_of_mem_isogenyClassCyclicDegrees : 0 < n := by
  simp only [isogenyClassCyclicDegrees, Set.mem_iUnion] at hn
  rcases hn with ⟨c, -, c', -, hn⟩
  exact IsomorphismClass.pos_of_mem_cyclicIsogenyDegrees hn

include hn in
lemma dvd_isogenyClassDegree (hW : W.isogenyClassDegree ≠ 0) : n ∣ W.isogenyClassDegree :=
  (Nat.sInf_mem <| Nat.nonempty_of_pos_sInf <| Nat.pos_of_ne_zero hW).2 n hn

/-- **The degree of an isogeny class with finitely many cyclic degrees is their least common
multiple.** -/
lemma isogenyClassDegree_eq_lcm (h : W.isogenyClassCyclicDegrees.Finite) :
    W.isogenyClassDegree = h.toFinset.lcm id := by
  have hpos : 0 < h.toFinset.lcm id := Nat.pos_of_ne_zero fun h0 ↦ by
    rcases Finset.lcm_eq_zero_iff.mp h0 with ⟨n, hn, hn0⟩
    exact (pos_of_mem_isogenyClassCyclicDegrees (h.mem_toFinset.mp hn)).ne' hn0
  exact IsLeast.csInf_eq ⟨⟨hpos, fun n hn ↦ Finset.dvd_lcm (h.mem_toFinset.mpr hn)⟩, fun m hm ↦
    Nat.le_of_dvd hm.1 <| Finset.lcm_dvd fun n hn ↦ hm.2 n (h.mem_toFinset.mp hn)⟩

variable [W.IsElliptic]

variable (W) in
lemma IsomorphismClass.one_mem_cyclicIsogenyDegrees : 1 ∈ cyclicIsogenyDegrees ⟦W⟧ ⟦W⟧ :=
  ⟨W, W, ‹_›, ‹_›, rfl, rfl, Isogeny.id W.toAffine, Isogeny.isCyclic_id W.toAffine,
    Isogeny.degree_id W.toAffine⟩

variable (W) in
lemma one_mem_isogenyClassCyclicDegrees : 1 ∈ W.isogenyClassCyclicDegrees :=
  Set.mem_iUnion₂_of_mem (mk_mem_isogenyClass_self W) <| Set.mem_iUnion₂_of_mem
    (mk_mem_isogenyClass_self W) <| IsomorphismClass.one_mem_cyclicIsogenyDegrees W

/-- **Isogenous elliptic curves have the same isogeny class degree**, their isogeny classes being
equal. -/
lemma isogenyClassDegree_eq_of_isIsogenous [W'.IsElliptic] (h : W.IsIsogenous W') :
    W.isogenyClassDegree = W'.isogenyClassDegree := by
  simp only [isogenyClassDegree, isogenyClassCyclicDegrees, isogenyClass_eq_iff.mpr h]

end WeierstrassCurve
