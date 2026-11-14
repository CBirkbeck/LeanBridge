import LeanBridge.ForMathlib.NumberTheory.LocalField.EisensteinDiagram
import LeanBridge.ForMathlib.NumberTheory.LocalField.FieldLabel
import LeanBridge.ForMathlib.NumberTheory.LocalField.GaloisClosureRamification
import LeanBridge.ForMathlib.NumberTheory.LocalField.MongeRepresentationProof
import LeanBridge.ForMathlib.NumberTheory.LocalField.RamsDiscriminantExponent
import LeanBridge.ForMathlib.NumberTheory.NumberField.MinimalSibling

/-!
# The invariants shared by the extensions in a family

Let `K` be a `p`-adic field and `I = (r_1, …, r_w)_ε^f` a Herbrand invariant at the residue
characteristic `p` of `K`. The extensions `L / K` in the family `I / K` (LMFDB
`lf.family_polynomial`) are those with Herbrand invariant `I`
(`IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf`): residue degree `f`, ramification
index `e = ε p ^ w` and Swan slopes `s_1, …, s_w` those of `I`, the Swan slopes being Deligne's
positive upper ramification breaks. These three invariants do not change under `K`-isomorphism, so
an extension has Herbrand invariant `I` exactly when its `K`-isomorphism class lies in `I / K`.
LMFDB `lf.family_invariants` lists the invariants that are the same for all the extensions in
`I / K`; this file proves that each of them is determined by `I`:

* the residue characteristic `p`, that of every finite extension of `K`;
* the degree `[L : K] = e f` (`IsNonarchimedeanLocalField.HerbrandInvariant.finrank_of_mem_family`,
  in `LeanBridge.ForMathlib.NumberTheory.LocalField.ExtensionFamilyUnramifiedMass`), the base field
  `K`, the ramification index `e`, the residue degree `f` and the Swan slopes, by definition;
* the discriminant exponent `c = f (e - 1 + e m_w)`, for the last mean `m_w` of `I`, by the formula
  of `LeanBridge.ForMathlib.NumberTheory.LocalField.RamsDiscriminantExponent`: it is the `c` of the
  label of the family (LMFDB `lf.family_label`,
  `IsNonarchimedeanLocalField.HerbrandInvariant.discriminantExponent`);
* the Artin slopes `s̃_1, …, s̃_w`, the wild Artin slopes of LMFDB `lf.slopes`, which are the Swan
  slopes plus `1`;
* the rams, Deligne's lower ramification breaks, which are the rams of `I`, and the means, those of
  the Herbrand invariant of `L / K`, which are the means of `I`: a finite extension has at most one
  Herbrand invariant up to the residue degree.

As for the Swan slopes, the means of `L / K` are taken to be those of its Herbrand invariant,
related to the rams and to the Swan slopes by the formulas of LMFDB `lf.herbrand_invariant` and
`lf.means`; their agreement with the means read off the slope polygon of LMFDB `lf.means` is not
proved here. Likewise the Artin slopes are the Swan slopes plus `1`, as LMFDB `lf.slopes` relates
them, and are not read off its convex hull. For a relative family the LMFDB's family pages show the
Artin slopes of `L / ℚ_p` (absolute Artin slopes), which this file does not treat.

## Main definitions

* `IsNonarchimedeanLocalField.visibleArtinSlopes` (LMFDB `lf.slopes`): the wild Artin slopes of a
  finite separable extension, its Swan slopes plus `1`.

## Main results

* `IsNonarchimedeanLocalField.visibleSwanSlopes_eq_of_algEquiv`: the Swan slopes of an extension
  of `K` inside `K̄` depend only on its `K`-isomorphism class.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.of_algEquiv` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.mk_mem_family_iff` (LMFDB `lf.family_invariants`):
  an extension `K`-isomorphic to one with Herbrand invariant `I` has Herbrand invariant `I`, so the
  extensions whose class lies in `I / K` are those with Herbrand invariant `I`.
* `IsNonarchimedeanLocalField.visibleArtinSlopes_eq_wildArtinSlopesOfIsGalois`: for a Galois
  extension these Artin slopes are the wild Artin slopes
  `IsNonarchimedeanLocalField.wildArtinSlopesOfIsGalois`.
* `IsNonarchimedeanLocalField.ringChar_residueField_finiteIntermediateField` (LMFDB
  `lf.family_invariants`): a finite extension of `K` has the residue characteristic of `K`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.hasSameRams_visibleHerbrandInvariant`
  (LMFDB `lf.family_invariants`): the Herbrand invariant of an extension in `I / K` has the rams of
  `I`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.visibleRams_eq` (LMFDB
  `lf.family_invariants`): the rams of an extension in `I / K` are those of `I`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.mean_visibleHerbrandInvariant` (LMFDB
  `lf.family_invariants`): its means are those of `I`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.natCast_discriminantExponent` (LMFDB
  `lf.family_invariants`, `lf.family_label`): its discriminant exponent is that of `I`,
  `f (e - 1 + e m_w)`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsInvariantOf.visibleArtinSlopes_eq` (LMFDB
  `lf.family_invariants`): its Artin slopes are `s_1 + 1, …, s_w + 1`.
-/

open ValuativeRel TauCeti LocalFieldsRamification Finset

open scoped Pointwise

attribute [local instance] finiteIntermediateFieldValuativeRel finiteIntermediateFieldTopology
  finiteIntermediateField_isNonarchimedeanLocalField finiteIntermediateField_valuativeExtension

namespace IsNonarchimedeanLocalField

lemma fixingSubgroup_preimage_eq_conj_smul {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    [Normal F Ω] {L L' : IntermediateField F Ω} (N : IntermediateField F Ω) [Normal F N]
    (φ : L ≃ₐ[F] L') : fixingSubgroup (N ≃ₐ[F] N) (((↑) : N → Ω) ⁻¹' L') =
      MulAut.conj ((φ.liftNormal Ω).restrictNormal N) •
        fixingSubgroup (N ≃ₐ[F] N) (((↑) : N → Ω) ⁻¹' L) := by
  set σ : Ω ≃ₐ[F] Ω := φ.liftNormal Ω
  set τ : N ≃ₐ[F] N := σ.restrictNormal N
  have hσ (a : Ω) : σ a ∈ L' ↔ a ∈ L := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · have h' : σ (φ.symm ⟨σ a, h⟩) = σ a :=
        (φ.liftNormal_commutes Ω _).trans (congrArg Subtype.val (φ.apply_symm_apply ⟨σ a, h⟩))
      exact σ.injective h' ▸ (φ.symm ⟨σ a, h⟩).2
    · exact (φ.liftNormal_commutes Ω ⟨a, h⟩).symm ▸ (φ ⟨a, h⟩).2
  have hτ (x : N) : ((τ x : N) : Ω) ∈ L' ↔ (x : Ω) ∈ L :=
    (congrArg (· ∈ L') (σ.restrictNormal_commutes N x)).to_iff.trans (hσ x)
  ext ρ
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_fixingSubgroup_iff, mem_fixingSubgroup_iff]
  refine ⟨fun h x hx ↦ ?_, fun h y hy ↦ ?_⟩
  · have h' : ρ (τ x) = τ x := h (τ x) ((hτ x).mpr hx)
    exact τ.symm_apply_eq.mpr h'
  · have h' : τ.symm (ρ (τ (τ.symm y))) = τ.symm y :=
      h (τ.symm y) ((hτ (τ.symm y)).mp ((τ.apply_symm_apply y).symm ▸ hy))
    rw [τ.apply_symm_apply] at h'
    exact τ.symm.injective h'

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {E E' : IntermediateField K (AlgebraicClosure K)}

variable (K) in
open Subgroup in
lemma swanSlopesOfSubgroup_conj_smul (M : Type*) [Field M] [ValuativeRel M] [TopologicalSpace M]
    [IsNonarchimedeanLocalField M] [Algebra K M] [ValuativeExtension K M] [Module.Finite K M]
    [IsGalois K M] (H : Subgroup (M ≃ₐ[K] M)) (τ : M ≃ₐ[K] M) :
    swanSlopesOfSubgroup K M (MulAut.conj τ • H) = swanSlopesOfSubgroup K M H := by
  have h (i : ℤ) : (MulAut.conj τ • H).relIndex (lowerRamificationGroup K M i) =
      H.relIndex (lowerRamificationGroup K M i) :=
    (congrArg _ (Normal.conj_smul_eq_self τ _).symm).trans
      (H.relIndex_pointwise_smul (MulAut.conj τ) _)
  simp only [swanSlopesOfSubgroup, h]

lemma swanSlopesOfSubgroup_fixingSubgroup_eq_of_algEquiv
    {N N' : IntermediateField K (AlgebraicClosure K)} [FiniteDimensional K N]
    [FiniteDimensional K N'] [IsGalois K N] [IsGalois K N'] (h : N' = N) (φ : E ≃ₐ[K] E') :
    swanSlopesOfSubgroup K N'
        (fixingSubgroup (N' ≃ₐ[K] N') (((↑) : N' → AlgebraicClosure K) ⁻¹' E')) =
      swanSlopesOfSubgroup K N
        (fixingSubgroup (N ≃ₐ[K] N) (((↑) : N → AlgebraicClosure K) ⁻¹' E)) := by
  subst h
  rw [fixingSubgroup_preimage_eq_conj_smul N' φ, swanSlopesOfSubgroup_conj_smul]

variable [FiniteDimensional K E] [FiniteDimensional K E']

variable [Algebra.IsSeparable K E] [Algebra.IsSeparable K E'] in
/-- **The Swan slopes of an extension depend only on its isomorphism class**: `K`-isomorphic finite
separable extensions `E` and `E'` of a nonarchimedean local field `K` inside `K̄` have the same Swan
slopes `IsNonarchimedeanLocalField.visibleSwanSlopes`. They have the same Galois closure `M` in
`K̄`, in which `Gal(M / E')` is a conjugate of `Gal(M / E)`, and the lower ramification groups of
`M / K` are normal. -/
lemma visibleSwanSlopes_eq_of_algEquiv (φ : E ≃ₐ[K] E') :
    visibleSwanSlopes E' = visibleSwanSlopes E :=
  swanSlopesOfSubgroup_fixingSubgroup_eq_of_algEquiv
    (Algebra.galoisClosure_eq_of_algEquiv φ.symm) φ

variable (E)

/-- The **wild Artin slopes** (LMFDB `lf.slopes`), which the LMFDB lists as the Artin slopes or
visible Artin slopes `s̃_1, …, s̃_w`, of a finite separable extension `E` of a nonarchimedean local
field `K` inside `K̄`: its Swan slopes `IsNonarchimedeanLocalField.visibleSwanSlopes`, Deligne's
positive upper ramification breaks, plus `1`, as LMFDB `lf.slopes` obtains the Swan slopes by
subtracting `1` from the Artin slopes. The Artin slopes `0` and `1` of the unramified and tame
parts of the convex hull of LMFDB `lf.slopes` are not among them. For `E / K` Galois they are
`IsNonarchimedeanLocalField.wildArtinSlopesOfIsGalois`
(`IsNonarchimedeanLocalField.visibleArtinSlopes_eq_wildArtinSlopesOfIsGalois`). -/
noncomputable def visibleArtinSlopes [Algebra.IsSeparable K E] : Multiset ℝ :=
  (visibleSwanSlopes E).map (· + 1)

variable [IsGalois K E] in
/-- **The Artin slopes of a Galois extension inside `K̄`**: for `E / K` Galois, the Artin slopes
`IsNonarchimedeanLocalField.visibleArtinSlopes` of `E` are the wild Artin slopes
`IsNonarchimedeanLocalField.wildArtinSlopesOfIsGalois` of the Galois extension `E / K`, for Tau
Ceti's spectral-norm local-field structure on `E`. -/
lemma visibleArtinSlopes_eq_wildArtinSlopesOfIsGalois :
    visibleArtinSlopes E = wildArtinSlopesOfIsGalois K E := by
  rw [visibleArtinSlopes, visibleSwanSlopes_eq_swanSlopesOfIsGalois, swanSlopesOfIsGalois,
    Multiset.map_map]
  simp

/-- **A finite extension has the residue characteristic of the base** (LMFDB
`lf.family_invariants`): a finite extension `E` of a nonarchimedean local field `K` inside `K̄`,
with Tau Ceti's spectral-norm local-field structure, has the residue characteristic of `K`; so all
the extensions in a family `I / K` have the residue characteristic `p` of `K`. -/
lemma ringChar_residueField_finiteIntermediateField : ringChar 𝓀[E] = ringChar 𝓀[K] :=
  (Algebra.ringChar_eq 𝓀[K] 𝓀[E]).symm

namespace HerbrandInvariant

variable {p : ℕ}

lemma map_ram_ofRams (hp : p.Prime) (R : Multiset ℚ) (hR : ∀ r ∈ R, 0 < r) (e f : ℕ) (he : e ≠ 0)
    (hf : 0 < f) : (Multiset.range (ofRams p hp R hR e f he hf).w).map
      (fun k ↦ (ofRams p hp R hR e f he hf).ram (k + 1)) = R := by
  have hw : (ofRams p hp R hR e f he hf).w = Multiset.card R := rfl
  refine Eq.trans ?_ (Multiset.sort_eq R (· ≤ ·))
  rw [← Multiset.coe_range, Multiset.map_coe]
  congr 1
  refine List.ext_getElem (by rw [List.length_map, List.length_range, hw, Multiset.length_sort])
    fun k hk _ ↦ ?_
  rw [List.getElem_map, List.getElem_range, List.length_map, List.length_range] at *
  exact (ram_ofRams p hp R hR e f he hf (by omega) (by omega)).trans (by simp)

variable [CharZero K] {E} {I : HerbrandInvariant p}

/-- **Having a Herbrand invariant depends only on the isomorphism class**: a finite extension `E'`
of a `p`-adic field `K` inside `K̄` that is `K`-isomorphic to an extension `E` with Herbrand
invariant `I` has Herbrand invariant `I`. The ramification index, the residue degree and the Swan
slopes of `E` and `E'` agree. -/
lemma IsInvariantOf.of_algEquiv (φ : E ≃ₐ[K] E') (hE : I.IsInvariantOf K E) :
    I.IsInvariantOf K E' := by
  rcases hE with ⟨hf, he, hs⟩
  have he' : TauCeti.ramificationIndex K E' = TauCeti.ramificationIndex K E :=
    ramificationIndex_eq_of_algEquiv φ.symm
  have hf' : inertiaDegree K E' = inertiaDegree K E := by
    have h : TauCeti.ramificationIndex K E' * inertiaDegree K E' =
        TauCeti.ramificationIndex K E * inertiaDegree K E := by
      rw [ramificationIndex_mul_inertiaDegree, ramificationIndex_mul_inertiaDegree,
        φ.toLinearEquiv.finrank_eq]
    rw [he'] at h
    exact Nat.eq_of_mul_eq_mul_left TauCeti.ramificationIndex_pos h
  rw [IsInvariantOf]
  exact ⟨hf'.trans hf, he'.trans he, (visibleSwanSlopes_eq_of_algEquiv φ).trans hs⟩

/-- **The extensions in a family are those with its Herbrand invariant** (LMFDB
`lf.family_polynomial`, `lf.family_invariants`): the `K`-isomorphism class of a finite extension `F`
of a `p`-adic field `K` inside `K̄` lies in the family `I / K` if and only if `F` has Herbrand
invariant `I`. So what is proved of the extensions with Herbrand invariant `I` holds for every
extension in `I / K`. -/
lemma mk_mem_family_iff {F : FiniteExtension K} :
    haveI : FiniteDimensional K F.1 := F.2
    Quotient.mk _ F ∈ I.family K ↔ I.IsInvariantOf K F.1 := by
  have hF : FiniteDimensional K F.1 := F.2
  refine ⟨?_, fun h ↦ ⟨F, h, rfl⟩⟩
  rintro ⟨F₀, hF₀, h⟩
  rcases Quotient.exact h with ⟨φ⟩
  have hF₀' : FiniteDimensional K F₀.1 := F₀.2
  exact IsInvariantOf.of_algEquiv φ hF₀

/-- **The rams of the extensions in a family are those of the family** (LMFDB
`lf.family_invariants`): the Herbrand invariant
`IsNonarchimedeanLocalField.visibleHerbrandInvariant` of an extension `E` inside `K̄` in the family
`I / K`, for `I` at the residue characteristic `p` of `K`, has the prime, the `w`, the `ε` and the
rams of `I`. -/
lemma IsInvariantOf.hasSameRams_visibleHerbrandInvariant (hp : ringChar 𝓀[K] = p)
    (hE : I.IsInvariantOf K E) : (visibleHerbrandInvariant E).HasSameRams I := by
  subst hp
  have hfact : Fact (ringChar 𝓀[K]).Prime := ⟨CharP.prime_ringChar _⟩
  exact hasSameRams_of_isInvariantOf (isInvariantOf_visibleHerbrandInvariant E) hE

/-- **The rams of an extension in a family** (LMFDB `lf.family_invariants`): an extension `E`
inside `K̄` in the family `I / K`, for `I = (r_1, …, r_w)_ε^f` at the residue characteristic of
`K`, has the rams `r_1, …, r_w` (`IsNonarchimedeanLocalField.visibleRams`, Deligne's positive lower
ramification breaks). -/
lemma IsInvariantOf.visibleRams_eq (hp : ringChar 𝓀[K] = p) (hE : I.IsInvariantOf K E) :
    visibleRams E = (Multiset.range I.w).map fun k ↦ I.ram (k + 1) := by
  have h : (visibleHerbrandInvariant E).HasSameRams I :=
    hE.hasSameRams_visibleHerbrandInvariant hp
  rw [← h.w_eq, ← h.ram_eq]
  exact (map_ram_ofRams _ _ _ _ _ _ _).symm

/-- **The means of an extension in a family** (LMFDB `lf.family_invariants`): the means
`m_k = ∑_{j ≤ k} (p - 1) r_j / (ε p ^ j)` of the Herbrand invariant of an extension `E` inside `K̄`
in the family `I / K`, for `I` at the residue characteristic of `K`, are those of `I`. -/
lemma IsInvariantOf.mean_visibleHerbrandInvariant (hp : ringChar 𝓀[K] = p)
    (hE : I.IsInvariantOf K E) (k : ℕ) : (visibleHerbrandInvariant E).mean k = I.mean k :=
  (hE.hasSameRams_visibleHerbrandInvariant hp).mean_eq k

/-- **The discriminant exponent of an extension in a family** (LMFDB `lf.family_invariants`,
`lf.family_label`): an extension `E` inside `K̄` in the family `I / K`, for `I = (r_1, …, r_w)_ε^f`
at the residue characteristic of `K`, has the discriminant exponent `c = f (e - 1 + e m_w)` of `I`
(`IsNonarchimedeanLocalField.HerbrandInvariant.discriminantExponent`), for `e = ε p ^ w` and `m_w`
the last mean of `I`, with Tau Ceti's spectral-norm local-field structure on `E`. So `c` is the
same for all the extensions in `I / K`. -/
lemma IsInvariantOf.natCast_discriminantExponent (hp : ringChar 𝓀[K] = p)
    (hE : I.IsInvariantOf K E) :
    (TauCeti.discriminantExponent K E : ℚ) = I.discriminantExponent := by
  have h : (visibleHerbrandInvariant E).HasSameRams I :=
    hE.hasSameRams_visibleHerbrandInvariant hp
  rw [natCast_discriminantExponent_visibleHerbrandInvariant E, h.mean_eq, h.w_eq, hE.1, hE.2.1,
    discriminantExponent]
  push_cast
  rfl

/-- **The Artin slopes of an extension in a family** (LMFDB `lf.family_invariants`): an extension
`E` inside `K̄` in the family `I / K` has the Artin slopes `s_1 + 1, …, s_w + 1`, for the Swan
slopes `s_k` of `I`. -/
lemma IsInvariantOf.visibleArtinSlopes_eq (hE : I.IsInvariantOf K E) :
    visibleArtinSlopes E = (Multiset.range I.w).map fun k ↦ (I.swanSlope (k + 1) : ℝ) + 1 := by
  rw [visibleArtinSlopes, hE.2.2, Multiset.map_map]
  rfl

end HerbrandInvariant

end IsNonarchimedeanLocalField
