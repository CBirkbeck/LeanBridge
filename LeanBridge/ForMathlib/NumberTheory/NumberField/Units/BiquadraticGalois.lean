import LeanBridge.ForMathlib.NumberTheory.NumberField.Units.Biquadratic
import LeanBridge.ForMathlib.NumberTheory.NumberField.Units.MazurUllomType
import TauCeti.NumberTheory.NumberField.AutomorphismAction
import TauCeti.NumberTheory.NumberField.Units.Basic

/-!
# The Galois action on the units of a real biquadratic field

Let `K` be a real biquadratic field: a totally real Galois extension of `ℚ` with Galois group the
Klein four-group. Each of its three quadratic subfields `kᵢ` is the fixed field of exactly one
nontrivial automorphism `σᵢ` (`QuadraticUnitFrame.aut`), and the three are related by
`σ₂ = σ₀ σ₁`. The automorphisms act on the units modulo torsion `L = (𝓞 K)ˣ ⧸ torsion K`, which is
`U/{±1}` (`Units.modTorsionMap`), and for a frame of quadratic units with classes `ē₀, ē₁, ē₂`:

* `σᵢ` fixes `ēᵢ` and inverts the other two;
* `w * σᵢ w`, the class of a norm to `kᵢ`, is a power of `ēᵢ`, and `w * σ₀ w * σ₁ w * σ₂ w`, the
  class of a norm to `ℚ`, is trivial;
* no `ēᵢ` has finite order.

So `ē₀, ē₁, ē₂` form a square basis of `L` (`QuadraticUnitFrame.isSquareBasis_unitClass`): every
square of `L` is a monomial in them, and their monomials are pairwise distinct. Moreover two frames
differ only by a relabelling of the subfields and the inversion of some classes
(`QuadraticUnitFrame.unitClass_eq_or_eq_inv`), and every relabelling of a frame is a frame
(`QuadraticUnitFrame.relabel`).

## Main definitions

* `NumberField.Units.modTorsionMap`: the action of an automorphism of `K` on the units modulo
  torsion.
* `NumberField.Units.QuadraticUnitFrame.aut`: the nontrivial automorphism of `K` fixing the
  quadratic subfield `kᵢ` of a frame.
* `NumberField.Units.QuadraticUnitFrame.relabel`: a frame with its subfields relabelled.

## Main results

* `NumberField.Units.QuadraticUnitFrame.isSquareBasis_unitClass`: the classes of the fundamental
  units of a frame form a square basis of the units modulo torsion.
* `NumberField.Units.QuadraticUnitFrame.unitClass_eq_or_eq_inv`: two frames agree up to relabelling
  and inversion.
-/

open Module IntermediateField TauCeti NumberField

open scoped NumberField

namespace NumberField

variable {K : Type*} [Field K] [NumberField K] (k : IntermediateField ℚ K) (σ τ : Gal(K/ℚ)) {x : K}

variable [IsGalois ℚ K] [IsKleinFour Gal(K/ℚ)] in
lemma exists_ne_one_forall_mem_iff (hk : finrank ℚ k = 2) :
    ∃ σ : Gal(K/ℚ), σ ≠ 1 ∧ ∀ x : K, x ∈ k ↔ σ x = x := by
  have hcard : Nat.card k.fixingSubgroup = 2 := by
    have h4 : finrank ℚ k * finrank k K = 4 :=
      (finrank_mul_finrank ℚ k K).trans (finrank_eq_four_of_isKleinFour K)
    rw [IsGalois.card_fixingSubgroup_eq_finrank]
    rw [hk] at h4
    omega
  rcases (Nat.card_eq_two_iff' (1 : k.fixingSubgroup)).mp hcard with ⟨σ, hσ, hσ'⟩
  refine ⟨σ, fun h ↦ hσ (Subtype.ext h), fun x ↦
    ⟨(mem_fixingSubgroup_iff k σ.1).mp σ.2 x, fun hx ↦ ?_⟩⟩
  rw [← IsGalois.fixedField_fixingSubgroup k, mem_fixedField_iff]
  intro τ hτ
  rcases eq_or_ne (⟨τ, hτ⟩ : k.fixingSubgroup) 1 with h1 | h1
  · exact congrArg (· x) (congrArg Subtype.val h1)
  · exact (congrArg (· x) (congrArg Subtype.val (hσ' _ h1))).trans hx

variable [IsGalois ℚ K] [IsKleinFour Gal(K/ℚ)] {σ τ} in
lemma mem_bot_of_apply_eq_self (hσ : σ ≠ 1) (hτ : τ ≠ 1) (hστ : σ ≠ τ) (hx : σ x = x)
    (hx' : τ x = x) : x ∈ (⊥ : IntermediateField ℚ K) := by
  refine (IsGalois.mem_bot_iff_fixed x).mpr fun ρ ↦ ?_
  by_cases h1 : ρ = 1
  · rw [h1, AlgEquiv.one_apply]
  by_cases h2 : ρ = σ
  · rw [h2, hx]
  by_cases h3 : ρ = τ
  · rw [h3, hx']
  rw [IsKleinFour.eq_mul_of_ne_all hσ hτ hστ h1 h2 h3, AlgEquiv.mul_apply, hx', hx]

variable [IsKleinFour Gal(K/ℚ)] in
lemma apply_apply_of_isKleinFour : σ (σ x) = x := by
  rw [← AlgEquiv.mul_apply, IsKleinFour.mul_self, AlgEquiv.one_apply]

variable [IsKleinFour Gal(K/ℚ)] in
lemma apply_comm_of_isKleinFour : σ (τ x) = τ (σ x) := by
  rw [← AlgEquiv.mul_apply, mul_comm_of_exponent_two IsKleinFour.exponent_two, AlgEquiv.mul_apply]

namespace Units

variable (u : (𝓞 K)ˣ) (hu : (u : K) ∈ k) {ε ε' : (𝓞 K)ˣ}

lemma coe_smul_eq_apply : ((σ • u : (𝓞 K)ˣ) : K) = σ (u : K) :=
  algebraMap_smul_eq_apply σ (u : 𝓞 K)

instance : IsMulTorsionFree ((𝓞 K)ˣ ⧸ torsion K) :=
  QuotientGroup.instIsMulTorsionFree _

/-- The action of an automorphism `σ` of `K` on the units of `𝓞 K` modulo torsion. -/
noncomputable def modTorsionMap : (𝓞 K)ˣ ⧸ torsion K →* (𝓞 K)ˣ ⧸ torsion K :=
  QuotientGroup.map _ _ (MulDistribMulAction.toMonoidHom (𝓞 K)ˣ σ) (CommGroup.le_comap_torsion _)

lemma modTorsionMap_mk : modTorsionMap σ u = ((σ • u : (𝓞 K)ˣ) : (𝓞 K)ˣ ⧸ torsion K) :=
  rfl

/-- The map from the units modulo torsion of an intermediate field `k` of `K` to those of `K`. -/
noncomputable def modTorsionOfSubfield : (𝓞 k)ˣ ⧸ torsion k →* (𝓞 K)ˣ ⧸ torsion K :=
  QuotientGroup.map _ _ (Units.map (algebraMap (𝓞 k) (𝓞 K)).toMonoidHom)
    (CommGroup.le_comap_torsion _)

lemma modTorsionOfSubfield_injective : Function.Injective (modTorsionOfSubfield k) := by
  refine (injective_iff_map_eq_one _).mpr fun x hx ↦ ?_
  induction x using QuotientGroup.induction_on with | H v => ?_
  rw [QuotientGroup.eq_one_iff, torsion,
    ← CommGroup.comap_torsion_of_injective (Units.map_injective
      (FaithfulSMul.algebraMap_injective (𝓞 k) (𝓞 K)))]
  exact (QuotientGroup.eq_one_iff (Units.map _ v)).mp hx

/-- A unit of `𝓞 K` whose value lies in an intermediate field `k`, as a unit of `𝓞 k`. -/
noncomputable def subfieldUnit : (𝓞 k)ˣ :=
  Units.mkOfMulEqOne ⟨⟨u, hu⟩, isIntegral_algebraMap_iff.mp u.1.isIntegral_coe⟩
    ⟨⟨_, (congrArg (· ∈ k) (map_units_inv (algebraMap (𝓞 K) K) u)).mpr (k.inv_mem hu)⟩,
      isIntegral_algebraMap_iff.mp (u⁻¹ : (𝓞 K)ˣ).1.isIntegral_coe⟩
    (RingOfIntegers.ext (Subtype.ext (congrArg (algebraMap (𝓞 K) K) u.mul_inv)))

lemma map_subfieldUnit : Units.map (algebraMap (𝓞 k) (𝓞 K)).toMonoidHom (subfieldUnit k u hu) = u :=
  Units.ext (RingOfIntegers.ext rfl)

lemma IsFundamentalUnit.mk_ne_one (hε : IsFundamentalUnit ε) (hK : rank K ≠ 0) :
    (ε : (𝓞 K)ˣ ⧸ torsion K) ≠ 1 := by
  intro h
  have hε' : Subgroup.zpowers (ε : (𝓞 K)ˣ ⧸ torsion K) = ⊤ := hε
  let η : (𝓞 K)ˣ := fundSystem K ⟨0, Nat.pos_of_ne_zero hK⟩
  have hη : (η : (𝓞 K)ˣ ⧸ torsion K) = 1 := by
    have hmem : (η : (𝓞 K)ˣ ⧸ torsion K) ∈ Subgroup.zpowers (ε : (𝓞 K)ˣ ⧸ torsion K) :=
      hε'.symm ▸ Subgroup.mem_top _
    rwa [h, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at hmem
  have hlog : logEmbedding K (Additive.ofMul η) = 0 :=
    dirichletUnitTheorem.logEmbedding_eq_zero_iff.mpr ((QuotientGroup.eq_one_iff η).mp hη)
  rw [logEmbedding_fundSystem] at hlog
  exact (basisUnitLattice K).ne_zero _ (Subtype.ext hlog)

lemma IsFundamentalUnit.mk_eq_or_eq_inv (hε : IsFundamentalUnit ε) (hε' : IsFundamentalUnit ε')
    (hK : rank K ≠ 0) :
    (ε' : (𝓞 K)ˣ ⧸ torsion K) = ε ∨ (ε' : (𝓞 K)ˣ ⧸ torsion K) = (ε : (𝓞 K)ˣ ⧸ torsion K)⁻¹ := by
  have h₁ : Subgroup.zpowers (ε : (𝓞 K)ˣ ⧸ torsion K) = ⊤ := hε
  have h₂ : Subgroup.zpowers (ε' : (𝓞 K)ˣ ⧸ torsion K) = ⊤ := hε'
  exact ((Subgroup.zpowers_eq_zpowers_iff (not_isOfFinOrder_of_isMulTorsionFree
    (hε.mk_ne_one hK))).mp (h₁.trans h₂.symm)).imp Eq.symm Eq.symm

namespace QuadraticUnitFrame

section Frame

variable (f : QuadraticUnitFrame K) (i : Fin 3) (π : Equiv.Perm (Fin 3))

lemma coe_map_mem (v : (𝓞 (f.subfield i).1)ˣ) :
    ((Units.map (algebraMap (𝓞 (f.subfield i).1) (𝓞 K)).toMonoidHom v : (𝓞 K)ˣ) : K) ∈
      (f.subfield i).1 :=
  (v : (f.subfield i).1).2

lemma exists_unitClass_zpow_eq (v : (𝓞 (f.subfield i).1)ˣ) : ∃ n : ℤ,
    ((Units.map (algebraMap (𝓞 (f.subfield i).1) (𝓞 K)).toMonoidHom v : (𝓞 K)ˣ) :
      (𝓞 K)ˣ ⧸ torsion K) = f.unitClass i ^ n := by
  have hv : (v : (𝓞 (f.subfield i).1)ˣ ⧸ torsion (f.subfield i).1) ∈
      Subgroup.zpowers ((f.unit i : (𝓞 (f.subfield i).1)ˣ) :
        (𝓞 (f.subfield i).1)ˣ ⧸ torsion (f.subfield i).1) :=
    (f.isFundamentalUnit_unit i).symm ▸ Subgroup.mem_top _
  rcases Subgroup.mem_zpowers_iff.mp hv with ⟨n, hn⟩
  have h : modTorsionOfSubfield (f.subfield i).1 _ = modTorsionOfSubfield (f.subfield i).1 _ :=
    congrArg _ hn
  rw [map_zpow] at h
  exact ⟨n, h.symm⟩

/-- The frame `f` with its subfields relabelled by a permutation `π` of the indices: its `i`-th
quadratic subfield and fundamental unit are the `π i`-th ones of `f`. -/
def relabel : QuadraticUnitFrame K where
  subfield := π.trans f.subfield
  unit i := f.unit (π i)
  isFundamentalUnit_unit i := f.isFundamentalUnit_unit (π i)

lemma unitClass_relabel : (f.relabel π).unitClass i = f.unitClass (π i) :=
  rfl

variable [IsTotallyReal K] in
lemma rank_subfield : rank (f.subfield i).1 = 1 := by
  rw [rank_eq_finrank_sub_one, (f.subfield i).2]

variable [IsTotallyReal K] in
lemma unitClass_ne_one : f.unitClass i ≠ 1 := fun h ↦
  (f.isFundamentalUnit_unit i).mk_ne_one (by rw [f.rank_subfield]; exact one_ne_zero) <|
    modTorsionOfSubfield_injective _ (h.trans (map_one _).symm)

variable [IsTotallyReal K] {i} in
lemma eq_zero_of_unitClass_zpow_eq_one {n : ℤ} (h : f.unitClass i ^ n = 1) : n = 0 :=
  (IsMulTorsionFree.zpow_eq_one_iff_right (f.unitClass_ne_one i)).mp h

variable [IsTotallyReal K] in
/-- **Two frames agree up to relabelling and inversion**: the class of the `i`-th fundamental unit
of `f'` is that of the fundamental unit of `f` for the same quadratic subfield, or its inverse. -/
lemma unitClass_eq_or_eq_inv (f' : QuadraticUnitFrame K) :
    f'.unitClass i = f.unitClass (f.subfield.symm (f'.subfield i)) ∨
      f'.unitClass i = (f.unitClass (f.subfield.symm (f'.subfield i)))⁻¹ := by
  have key (k k' : {k : IntermediateField ℚ K // finrank ℚ k = 2}) (h : k = k')
      (η : (𝓞 k.1)ˣ) (η' : (𝓞 k'.1)ˣ) (hη : IsFundamentalUnit η) (hη' : IsFundamentalUnit η') :
      modTorsionOfSubfield k'.1 η' = modTorsionOfSubfield k.1 η ∨
        modTorsionOfSubfield k'.1 η' = (modTorsionOfSubfield k.1 η)⁻¹ := by
    subst h
    have hk : rank k.1 ≠ 0 := by
      rw [rank_eq_finrank_sub_one, k.2]
      exact one_ne_zero
    rcases hη.mk_eq_or_eq_inv hη' hk with h | h
    · exact Or.inl (congrArg _ h)
    · exact Or.inr ((congrArg _ h).trans (map_inv _ _))
  exact key _ _ (f.subfield.apply_symm_apply (f'.subfield i)) _ _ (f.isFundamentalUnit_unit _)
    (f'.isFundamentalUnit_unit i)

end Frame

variable [IsGalois ℚ K] [IsKleinFour Gal(K/ℚ)] (f : QuadraticUnitFrame K) (i : Fin 3)
  (w : (𝓞 K)ˣ ⧸ torsion K)

/-- The nontrivial automorphism of `K` fixing the `i`-th quadratic subfield `kᵢ` of a frame:
`kᵢ` is its fixed field. -/
noncomputable def aut : Gal(K/ℚ) :=
  (exists_ne_one_forall_mem_iff (f.subfield i).1 (f.subfield i).2).choose

lemma aut_ne_one : f.aut i ≠ 1 :=
  (exists_ne_one_forall_mem_iff (f.subfield i).1 (f.subfield i).2).choose_spec.1

lemma mem_subfield_iff : x ∈ (f.subfield i).1 ↔ f.aut i x = x :=
  (exists_ne_one_forall_mem_iff (f.subfield i).1 (f.subfield i).2).choose_spec.2 x

lemma aut_injective : Function.Injective f.aut :=
  fun i j h ↦ f.subfield.injective <| Subtype.ext <| SetLike.ext fun x ↦ by
    rw [mem_subfield_iff, mem_subfield_iff, h]

variable {i} in
lemma aut_eq_mul {j l : Fin 3} (hij : i ≠ j) (hli : l ≠ i) (hlj : l ≠ j) :
    f.aut l = f.aut i * f.aut j :=
  IsKleinFour.eq_mul_of_ne_all (f.aut_ne_one i) (f.aut_ne_one j) (f.aut_injective.ne hij)
    (f.aut_ne_one l) (f.aut_injective.ne hli) (f.aut_injective.ne hlj)

lemma aut_two : f.aut 2 = f.aut 0 * f.aut 1 :=
  f.aut_eq_mul (by decide) (by decide) (by decide)

lemma exists_mul_modTorsionMap_eq : ∃ n : ℤ, w * modTorsionMap (f.aut i) w = f.unitClass i ^ n := by
  induction w using QuotientGroup.induction_on with | H u => ?_
  have hmem : ((u * f.aut i • u : (𝓞 K)ˣ) : K) ∈ (f.subfield i).1 := by
    rw [mem_subfield_iff, coe_mul, coe_smul_eq_apply, map_mul, apply_apply_of_isKleinFour,
      mul_comm]
  rcases f.exists_unitClass_zpow_eq i (subfieldUnit _ _ hmem) with ⟨n, hn⟩
  exact ⟨n, by rw [modTorsionMap_mk, ← QuotientGroup.mk_mul, ← map_subfieldUnit _ _ hmem, hn]⟩

lemma modTorsionMap_aut_unitClass : modTorsionMap (f.aut i) (f.unitClass i) = f.unitClass i :=
  congrArg _ <| coe_injective K <| (coe_smul_eq_apply _ _).trans <|
    (f.mem_subfield_iff i).mp (f.coe_map_mem i (f.unit i))

variable {i} in
lemma unitClass_mul_modTorsionMap_aut {j : Fin 3} (hij : i ≠ j) :
    f.unitClass i * modTorsionMap (f.aut j) (f.unitClass i) = 1 := by
  let e : (𝓞 K)ˣ := Units.map (algebraMap (𝓞 (f.subfield i).1) (𝓞 K)).toMonoidHom (f.unit i)
  have he : f.aut i (e : K) = e := (f.mem_subfield_iff i).mp (f.coe_map_mem i (f.unit i))
  refine (QuotientGroup.eq_one_iff (e * f.aut j • e)).mpr <| Units.mem_torsion_of_mem_bot <|
    mem_bot_of_apply_eq_self (f.aut_ne_one i) (f.aut_ne_one j) (f.aut_injective.ne hij) ?_ ?_
  · rw [coe_mul, coe_smul_eq_apply, map_mul, he, apply_comm_of_isKleinFour, he]
  · rw [coe_mul, coe_smul_eq_apply, map_mul, apply_apply_of_isKleinFour, mul_comm]

lemma mul_modTorsionMap_eq_one :
    w * modTorsionMap (f.aut 0) w * modTorsionMap (f.aut 1) w * modTorsionMap (f.aut 2) w = 1 := by
  induction w using QuotientGroup.induction_on with | H u => ?_
  have h₁₀ (y : K) : f.aut 1 (f.aut 0 y) = f.aut 0 (f.aut 1 y) := apply_comm_of_isKleinFour _ _
  refine (QuotientGroup.eq_one_iff (u * f.aut 0 • u * f.aut 1 • u * f.aut 2 • u)).mpr <|
    Units.mem_torsion_of_mem_bot <| mem_bot_of_apply_eq_self (f.aut_ne_one 0) (f.aut_ne_one 1)
      (f.aut_injective.ne (by decide)) ?_ ?_
  · simp only [coe_mul, coe_smul_eq_apply, f.aut_two, AlgEquiv.mul_apply, map_mul,
      apply_apply_of_isKleinFour]
    ring1
  · simp only [coe_mul, coe_smul_eq_apply, f.aut_two, AlgEquiv.mul_apply, map_mul, h₁₀,
      apply_apply_of_isKleinFour]
    ring1

variable [IsTotallyReal K] in
/-- **The classes of the fundamental units of a frame form a square basis** of the units modulo
torsion of a real biquadratic field: every square is a monomial in them, and their monomials are
pairwise distinct. -/
lemma isSquareBasis_unitClass : MazurUllomType.IsSquareBasis f.unitClass :=
  .of_monoidHom (fun i ↦ modTorsionMap (f.aut i)) f.modTorsionMap_aut_unitClass
    (fun _ _ hij ↦ f.unitClass_mul_modTorsionMap_aut hij.symm)
    (fun _ _ h ↦ f.eq_zero_of_unitClass_zpow_eq_one h) f.exists_mul_modTorsionMap_eq
    f.mul_modTorsionMap_eq_one

end QuadraticUnitFrame

end Units

end NumberField
