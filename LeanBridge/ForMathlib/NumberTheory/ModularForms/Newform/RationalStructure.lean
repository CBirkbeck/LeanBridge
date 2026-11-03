import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.Dimension
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.GaloisActionOnNewforms
import LeanBridge.ForMathlib.NumberTheory.ModularForms.Newform.GaloisStability

/-!
# The rational structure of the newspace and the irreducibility of its pieces

For a countable subfield `F` of `ℂ`, such as `ℚ` or the field `ℚ(χ)` of values of a character `χ`,
the forms of the newspace `S_k(Γ₁(N))ⁿᵉʷ` with Fourier coefficients in `F` make up an `F`-subspace,
stable under the rational Hecke algebra `T_ℚ`. They are the forms fixed by the conjugation by the
automorphisms of `ℂ` fixing `F`.

For a newform `f` with `F ⊆ ℚ(f)`, the forms of this `F`-subspace in the span of the orbit of `f`
under the automorphisms of `ℂ` fixing `F` make up an irreducible module under `T_ℚ`, isomorphic to
`ℚ(f)` over `F`. Its complex span is the span of that orbit, which has `[ℚ(f) : F]` elements. These
are the irreducible pieces of the space of newforms under the Hecke algebra (LMFDB
`cmf.decomposition.new.gamma0chi`, `cmf.newspaces`):

* for `F = ℚ`, the pieces of `S_k^{new}(N, [χ])`, the sum of the `S_k^{new}(N, χ')` for `χ'` in the
  Galois orbit of `χ`, which have dimension `[ℚ(f) : ℚ]`;
* for `F = ℚ(χ)`, the pieces of `S_k^{new}(N, χ)`, which have dimension `[ℚ(f) : ℚ(χ)]`.

## Main definitions

* `HeckeRing.GL2.Newform.conjNew`: the conjugation by an automorphism of `ℂ`, on the newspace.
* `HeckeRing.GL2.Newform.rationalNewspace`: the forms of the newspace with coefficients in `F`.
* `HeckeRing.GL2.Newform.galoisOrbitOver`: the orbit of a newform under the automorphisms of `ℂ`
  fixing `F`.
* `HeckeRing.GL2.Newform.galoisOrbitOverRel`: conjugacy under these automorphisms, as an equivalence
  relation.
* `HeckeRing.GL2.Newform.newformSubspaceOver`: the complex span of that orbit.
* `HeckeRing.GL2.Newform.rationalPiece`: the forms of that span with coefficients in `F`.
* `HeckeRing.GL2.Newform.rationalPieceCoord`, `HeckeRing.GL2.Newform.rationalPieceEquiv`: the
  coordinate along `f`, which identifies a piece with the coefficient field `ℚ(f)`.

## Main results

* `HeckeRing.GL2.Newform.apply_mem_rationalNewspace`,
  `HeckeRing.GL2.Newform.apply_mem_rationalPiece`: the rational Hecke algebra preserves the forms
  with coefficients in `F`, and the pieces.
* `HeckeRing.GL2.Newform.exists_apply_eq_of_mem_rationalPiece`,
  `HeckeRing.GL2.Newform.eq_bot_or_eq_rationalPiece`: the pieces are irreducible under `T_ℚ`.
* `HeckeRing.GL2.Newform.span_rationalPiece`: the complex span of a piece is the span of the orbit.
* `HeckeRing.GL2.Newform.finrank_rationalPiece`, `HeckeRing.GL2.Newform.ncard_galoisOrbitOver`,
  `HeckeRing.GL2.Newform.finrank_newformSubspaceOver`: a piece has dimension `[ℚ(f) : F]` over `F`,
  the orbit has `[ℚ(f) : F]` elements, and its span has dimension `[ℚ(f) : F]` over `ℂ`.
* `HeckeRing.GL2.Newform.iSup_rationalPiece`, `HeckeRing.GL2.Newform.iSupIndep_rationalPiece`: the
  pieces span the forms with coefficients in `F`, and are independent.
* `HeckeRing.GL2.Newform.span_rationalNewspace_bot`: the forms of the newspace with rational
  coefficients span it over `ℂ`.
* `HeckeRing.GL2.Newform.galoisOrbitOver_bot`, `HeckeRing.GL2.Newform.newformSubspaceOver_bot`: for
  `F = ℚ`, the orbit is the Galois orbit and its span is the newform subspace.
* `HeckeRing.GL2.Newform.galoisOrbitOver_characterField`,
  `HeckeRing.GL2.Newform.newformSubspaceOver_characterField`: for `F = ℚ(χ)`, the orbit is the set
  of the Galois conjugates of nebentypus `χ` and its span is the `χ`-part of the newform subspace.
* `HeckeRing.GL2.Newform.relativeDimension_eq_finrank`: the relative dimension of `f` is
  `[ℚ(f) : ℚ(χ)]`.
* `HeckeRing.GL2.NewformOrbit.iSupIndep_newformSubspace_inf_cuspFormCharSpace`,
  `HeckeRing.GL2.NewformOrbit.iSup_newformSubspace_inf_cuspFormCharSpace`: the space
  `S_k^{new}(N, χ)` is the direct sum of the `χ`-parts of the spans of the Galois orbits.
-/

open UpperHalfPlane TauCeti CongruenceSubgroup Module GaloisAction Matrix SpecialLinearGroup

namespace HeckeRing.GL2.Newform

variable {N : ℕ} {k : ℤ} (σ : Gal(ℂ/ℚ))

lemma mem_fixingSubgroup_characterField_iff {χ : (ZMod N)ˣ →* ℂˣ} :
    σ ∈ (CharacterField χ).fixingSubgroup ↔ ∀ u, σ (χ u : ℂ) = χ u := by
  refine ⟨fun hσ u ↦ (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ _
    (char_mem_CharacterField χ u), fun h ↦ ?_⟩
  have he : (σ : ℂ →ₐ[ℚ] ℂ).comp (CharacterField χ).val = (CharacterField χ).val :=
    IntermediateField.algHom_ext_of_eq_adjoin ℚ (CharacterField_def χ) <| by
      rintro _ ⟨u, rfl⟩
      exact h u
  exact (IntermediateField.mem_fixingSubgroup_iff _ σ).mpr fun x hx ↦
    DFunLike.congr_fun he ⟨x, hx⟩

variable [NeZero N] {f g : Newform N k} (v : cuspFormsNew N k)

/-- The conjugation by an automorphism of `ℂ`, on the newspace. -/
noncomputable def conjNew : cuspFormsNew N k →+ cuspFormsNew N k where
  toFun u := ⟨conjCusp σ u, conjCusp_mem_cuspFormsNew σ u.2⟩
  map_zero' := Subtype.ext <| map_zero (conjCusp σ)
  map_add' _ _ := Subtype.ext <| map_add (conjCusp σ) _ _

lemma coe_conjNew : (conjNew σ v : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = conjCusp σ v :=
  rfl

lemma conjNew_smul (c : ℂ) : conjNew σ (c • v) = σ c • conjNew σ v :=
  Subtype.ext <| by
    rw [coe_conjNew, Submodule.coe_smul, conjCusp_smul, Submodule.coe_smul, coe_conjNew]

variable (f) in
lemma conjNew_basis : conjNew σ (basis N k f) = basis N k (σ • f) :=
  Subtype.ext <| by
    rw [coe_conjNew, coe_basis_apply, coe_basis_apply]
    exact conjCusp_toCuspForm σ f

variable (g) in
lemma repr_conjNew_smul : (basis N k).repr (conjNew σ v) (σ • g) = σ ((basis N k).repr v g) := by
  classical
  let : Fintype (Newform N k) := Fintype.ofFinite _
  conv_lhs => rw [← (basis N k).sum_repr v]
  rw [map_sum, map_sum, Finsupp.finsetSum_apply]
  simp only [conjNew_smul, conjNew_basis, map_smul, Basis.repr_self, Finsupp.smul_apply,
    Finsupp.single_apply, smul_left_cancel_iff, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

variable (F : IntermediateField ℚ ℂ)

variable (N k) in
/-- The **rational structure** of the newspace over a subfield `F` of `ℂ`: the `F`-subspace of the
forms whose Fourier coefficients lie in `F`. -/
def rationalNewspace : Submodule F (cuspFormsNew N k) where
  carrier := {u | ∀ n, (qExpansion 1 (u : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n ∈ F}
  add_mem' {u u'} hu hu' n := by
    rw [Submodule.coe_add, FunLike.coe_add, ModularForm.qExpansion_add one_pos
      (one_mem_strictPeriods_Gamma1_map N), map_add]
    exact add_mem (hu n) (hu' n)
  zero_mem' n := by
    rw [Submodule.coe_zero, FunLike.coe_zero, qExpansion_zero, map_zero]
    exact zero_mem F
  smul_mem' c u hu n := by
    have h : ((c • u : cuspFormsNew N k) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) =
        (c : ℂ) • (u : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) := rfl
    rw [h, FunLike.coe_smul, ModularForm.qExpansion_smul one_pos
      (one_mem_strictPeriods_Gamma1_map N), PowerSeries.coeff_smul, smul_eq_mul]
    exact mul_mem c.2 (hu n)

lemma qExpansion_coeff_conjNew (n : ℕ) :
    (qExpansion 1 (conjNew σ v : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n =
      σ ((qExpansion 1 (v : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)).coeff n) := by
  rw [coe_conjNew, qExpansion_conjCusp, PowerSeries.coeff_map]
  rfl

variable {F} {v} {w : cuspFormsNew N k}

variable {σ} in
lemma conjNew_eq_of_mem_rationalNewspace (hv : v ∈ rationalNewspace N k F)
    (hσ : σ ∈ F.fixingSubgroup) : conjNew σ v = v :=
  Subtype.ext <| (conjCusp_eq_iff σ).mpr <| PowerSeries.ext fun n ↦ by
    rw [PowerSeries.coeff_map]
    exact ((IntermediateField.mem_fixingSubgroup_iff F σ).mp hσ _ (hv n)).symm

variable [Countable F] in
lemma mem_rationalNewspace_of_forall_conjNew_eq (h : ∀ σ ∈ F.fixingSubgroup, conjNew σ v = v) :
    v ∈ rationalNewspace N k F := fun n ↦ by
  by_contra hn
  rcases IntermediateField.exists_algEquiv_apply_ne_of_notMem hn with ⟨σ, hσ, hne⟩
  have hfix : conjNew σ v = v :=
    h σ ((IntermediateField.mem_fixingSubgroup_iff F σ).mpr fun x hx ↦ hσ ⟨x, hx⟩)
  refine hne <| (qExpansion_coeff_conjNew σ v n).symm.trans ?_
  rw [hfix]

variable {σ} in
lemma repr_smul_of_mem_rationalNewspace (hv : v ∈ rationalNewspace N k F)
    (hσ : σ ∈ F.fixingSubgroup) (h : Newform N k) :
    (basis N k).repr v (σ • h) = σ ((basis N k).repr v h) := by
  rw [← repr_conjNew_smul, conjNew_eq_of_mem_rationalNewspace hv hσ]

variable [Countable F] in
lemma mem_rationalNewspace_of_repr_smul
    (h : ∀ σ ∈ F.fixingSubgroup, ∀ g, (basis N k).repr v (σ • g) = σ ((basis N k).repr v g)) :
    v ∈ rationalNewspace N k F :=
  mem_rationalNewspace_of_forall_conjNew_eq fun σ hσ ↦
    (basis N k).repr.injective <| Finsupp.ext fun g ↦ by
      rw [← smul_inv_smul σ g, repr_conjNew_smul, h σ hσ]

variable [Countable F] in
/-- **The rational Hecke algebra preserves the forms with coefficients in `F`.** -/
lemma apply_mem_rationalNewspace (t : heckeCuspNewRationalAlgebra N k)
    (hv : v ∈ rationalNewspace N k F) :
    (t : Module.End ℂ (cuspFormsNew N k)) v ∈ rationalNewspace N k F :=
  mem_rationalNewspace_of_repr_smul fun σ hσ g ↦ by
    rw [basis_repr_apply_heckeCuspNewRationalAlgebra, basis_repr_apply_heckeCuspNewRationalAlgebra,
      map_mul, repr_smul_of_mem_rationalNewspace hv hσ,
      (g.isGaloisConjugateBy_smul σ).heckeCuspNewRationalCharacter_eq]
    rfl

variable (f F) in
/-- The **orbit of a newform under the automorphisms of `ℂ` fixing a subfield `F`**. For `F = ℚ`, it
is the Galois orbit of `f`, and for `F = ℚ(χ)`, it is the set of its Galois conjugates of the
nebentypus `χ` of `f`. -/
def galoisOrbitOver : Set (Newform N k) :=
  {g | ∃ σ ∈ F.fixingSubgroup, σ • f = g}

variable (f F) in
lemma self_mem_galoisOrbitOver : f ∈ f.galoisOrbitOver F :=
  ⟨1, one_mem _, one_smul _ f⟩

variable {σ} in
lemma smul_mem_galoisOrbitOver_iff (hσ : σ ∈ F.fixingSubgroup) :
    σ • g ∈ f.galoisOrbitOver F ↔ g ∈ f.galoisOrbitOver F := by
  refine ⟨?_, ?_⟩
  · rintro ⟨τ, hτ, h⟩
    exact ⟨σ⁻¹ * τ, mul_mem (inv_mem hσ) hτ, by rw [mul_smul, h, inv_smul_smul]⟩
  · rintro ⟨τ, hτ, rfl⟩
    exact ⟨σ * τ, mul_mem hσ hτ, mul_smul σ τ f⟩

variable (N k F) in
/-- Conjugacy of newforms under the automorphisms of `ℂ` fixing a subfield `F`, as an equivalence
relation. -/
def galoisOrbitOverRel : Setoid (Newform N k) where
  r f g := g ∈ f.galoisOrbitOver F
  iseqv := ⟨fun f ↦ f.self_mem_galoisOrbitOver F, fun {f g} ⟨σ, hσ, h⟩ ↦ ⟨σ⁻¹, inv_mem hσ, by
    rw [← h, inv_smul_smul]⟩, fun {f g h} ⟨σ, hσ, hg⟩ ⟨τ, hτ, hh⟩ ↦ ⟨τ * σ, mul_mem hτ hσ, by
    rw [mul_smul, hg, hh]⟩⟩

variable (f F) in
/-- The complex span of the orbit of a newform under the automorphisms of `ℂ` fixing `F`. -/
def newformSubspaceOver : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  Submodule.span ℂ ((fun g : Newform N k ↦ g.toCuspForm) '' f.galoisOrbitOver F)

lemma coe_mem_span_image_iff {s : Set (Newform N k)} : (v : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈
    Submodule.span ℂ ((fun g : Newform N k ↦ g.toCuspForm) '' s) ↔
      ∀ g ∉ s, (basis N k).repr v g = 0 := by
  have hmap : Submodule.span ℂ ((fun g : Newform N k ↦ g.toCuspForm) '' s) =
      (Submodule.span ℂ (basis N k '' s)).map (cuspFormsNew N k).subtype := by
    rw [Submodule.map_span, Set.image_image]
    exact congrArg (Submodule.span ℂ) <| Set.image_congr fun g _ ↦ (coe_basis_apply g).symm
  have hmem : (v : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈
      (Submodule.span ℂ (basis N k '' s)).map (cuspFormsNew N k).subtype ↔
        v ∈ Submodule.span ℂ (basis N k '' s) :=
    ⟨fun ⟨w, hw, h⟩ ↦ (Subtype.ext h : w = v) ▸ hw, fun h ↦ ⟨v, h, rfl⟩⟩
  rw [hmap, hmem, Basis.mem_span_image]
  exact ⟨fun h g hg ↦ by_contra fun hne ↦ hg (h (Finsupp.mem_support_iff.mpr hne)),
    fun h g hg ↦ by_contra fun hgs ↦ Finsupp.mem_support_iff.mp hg (h g hgs)⟩

variable (f F) in
/-- The **irreducible piece of the rational structure** attached to a newform `f`: the forms of the
newspace with coefficients in `F` in the complex span of the orbit of `f` under the automorphisms
of `ℂ` fixing `F`. It is an irreducible module under the rational Hecke algebra when `F ⊆ ℚ(f)`,
by `exists_apply_eq_of_mem_rationalPiece`. -/
def rationalPiece : Submodule F (cuspFormsNew N k) where
  carrier := {v | v ∈ rationalNewspace N k F ∧
    (v : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ f.newformSubspaceOver F}
  add_mem' hv hw := ⟨add_mem hv.1 hw.1, add_mem hv.2 hw.2⟩
  zero_mem' := ⟨zero_mem _, zero_mem _⟩
  smul_mem' c _ hv := ⟨Submodule.smul_mem _ c hv.1, Submodule.smul_mem _ (c : ℂ) hv.2⟩

lemma mem_rationalPiece_iff : v ∈ f.rationalPiece F ↔ v ∈ rationalNewspace N k F ∧
    ∀ g ∉ f.galoisOrbitOver F, (basis N k).repr v g = 0 :=
  and_congr_right fun _ ↦ coe_mem_span_image_iff

variable [Countable F] in
/-- **The rational Hecke algebra preserves the irreducible pieces.** -/
lemma apply_mem_rationalPiece (t : heckeCuspNewRationalAlgebra N k) (hv : v ∈ f.rationalPiece F) :
    (t : Module.End ℂ (cuspFormsNew N k)) v ∈ f.rationalPiece F := by
  rcases mem_rationalPiece_iff.mp hv with ⟨hv₁, hv₂⟩
  refine mem_rationalPiece_iff.mpr ⟨apply_mem_rationalNewspace t hv₁, fun g hg ↦ ?_⟩
  rw [basis_repr_apply_heckeCuspNewRationalAlgebra, hv₂ g hg, mul_zero]

variable {σ} in
lemma smul_eq_self_of_mem_fixingSubgroup (hσ : σ ∈ (CoefficientField f).fixingSubgroup) :
    σ • f = f :=
  (smul_eq_iff σ).mpr <| isGaloisConjugateBy_iff.mpr fun n ↦
    ((IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ _
      (f.qExpansion_coeff_mem_coefficientField n)).symm

lemma repr_self_mem_coefficientField (hF : F ≤ CoefficientField f) (hv : v ∈ f.rationalPiece F) :
    (basis N k).repr v f ∈ CoefficientField f := by
  by_contra h
  rcases IntermediateField.exists_algEquiv_apply_ne_of_notMem h with ⟨σ, hσ, hne⟩
  have hσ₀ : σ ∈ (CoefficientField f).fixingSubgroup :=
    (IntermediateField.mem_fixingSubgroup_iff _ σ).mpr fun x hx ↦ hσ ⟨x, hx⟩
  have hσF : σ ∈ F.fixingSubgroup :=
    (IntermediateField.mem_fixingSubgroup_iff _ σ).mpr fun x hx ↦ hσ ⟨x, hF hx⟩
  have hfix : (basis N k).repr v (σ • f) = σ ((basis N k).repr v f) :=
    repr_smul_of_mem_rationalNewspace hv.1 hσF f
  rw [smul_eq_self_of_mem_fixingSubgroup hσ₀] at hfix
  exact hne hfix.symm

lemma eq_zero_of_repr_self_eq_zero (hv : v ∈ f.rationalPiece F) (h : (basis N k).repr v f = 0) :
    v = 0 := by
  refine (basis N k).repr.map_eq_zero_iff.mp <| Finsupp.ext fun g ↦ ?_
  by_cases hg : g ∈ f.galoisOrbitOver F
  · rcases hg with ⟨σ, hσ, rfl⟩
    rw [repr_smul_of_mem_rationalNewspace hv.1 hσ, h, map_zero]
    rfl
  · exact (mem_rationalPiece_iff.mp hv).2 g hg

/-- **The pieces are irreducible under the rational Hecke algebra**: for a newform `f` with
`F ⊆ ℚ(f)`, every element of the piece of `f` is the image of any nonzero element of the piece by
an operator of the rational Hecke algebra (LMFDB `cmf.decomposition.new.gamma0chi`,
`cmf.newspaces`). -/
lemma exists_apply_eq_of_mem_rationalPiece (hF : F ≤ CoefficientField f)
    (hv : v ∈ f.rationalPiece F) (hv₀ : v ≠ 0) (hw : w ∈ f.rationalPiece F) :
    ∃ t : heckeCuspNewRationalAlgebra N k, (t : Module.End ℂ (cuspFormsNew N k)) v = w := by
  have hb₀ : (basis N k).repr v f ≠ 0 := fun h ↦ hv₀ (eq_zero_of_repr_self_eq_zero hv h)
  have hr₀ : (basis N k).repr w f / (basis N k).repr v f ∈ CoefficientField f :=
    div_mem (repr_self_mem_coefficientField hF hw) (repr_self_mem_coefficientField hF hv)
  have hr : (basis N k).repr w f / (basis N k).repr v f ∈
      f.heckeCuspNewRationalCharacter.range := by
    rw [f.range_heckeCuspNewRationalCharacter]
    exact hr₀
  rcases hr with ⟨t, ht⟩
  refine ⟨t, (basis N k).repr.injective <| Finsupp.ext fun g ↦ ?_⟩
  rw [basis_repr_apply_heckeCuspNewRationalAlgebra]
  by_cases hg : g ∈ f.galoisOrbitOver F
  · rcases hg with ⟨σ, hσ, rfl⟩
    have hchar : (σ • f).heckeCuspNewRationalCharacter t =
        σ (f.heckeCuspNewRationalCharacter t) := by
      rw [(f.isGaloisConjugateBy_smul σ).heckeCuspNewRationalCharacter_eq]
      rfl
    have ht₁ : f.heckeCuspNewRationalCharacter t =
        (basis N k).repr w f / (basis N k).repr v f := ht
    rw [repr_smul_of_mem_rationalNewspace hv.1 hσ, repr_smul_of_mem_rationalNewspace hw.1 hσ, hchar,
      ht₁, ← map_mul, div_mul_cancel₀ _ hb₀]
  · rw [(mem_rationalPiece_iff.mp hv).2 g hg, (mem_rationalPiece_iff.mp hw).2 g hg, mul_zero]

/-- **The pieces have no proper nonzero stable subspace** under the rational Hecke algebra. -/
lemma eq_bot_or_eq_rationalPiece (hF : F ≤ CoefficientField f) {U : Submodule F (cuspFormsNew N k)}
    (hU : U ≤ f.rationalPiece F) (hs : ∀ (t : heckeCuspNewRationalAlgebra N k), ∀ u ∈ U,
      (t : Module.End ℂ (cuspFormsNew N k)) u ∈ U) : U = ⊥ ∨ U = f.rationalPiece F := by
  by_cases h : U = ⊥
  · exact Or.inl h
  · rcases (Submodule.ne_bot_iff U).mp h with ⟨v, hv, hv₀⟩
    refine Or.inr (le_antisymm hU fun w hw ↦ ?_)
    rcases exists_apply_eq_of_mem_rationalPiece hF (hU hv) hv₀ hw with ⟨t, rfl⟩
    exact hs t v hv

variable {σ} in
lemma smul_eq_smul_iff {τ : Gal(ℂ/ℚ)} : σ • f = τ • f ↔ ∀ x : CoefficientField f, σ x = τ x := by
  have hι : f.IsEmbedding (σ • f) ((σ : ℂ →ₐ[ℚ] ℂ).comp (CoefficientField f).val) :=
    (f.isGaloisConjugateBy_smul σ).isEmbedding
  have hι' : f.IsEmbedding (τ • f) ((τ : ℂ →ₐ[ℚ] ℂ).comp (CoefficientField f).val) :=
    (f.isGaloisConjugateBy_smul τ).isEmbedding
  refine ⟨fun h x ↦ ?_, fun h ↦ ?_⟩
  · rw [← h] at hι'
    exact DFunLike.congr_fun (hι.algHom_eq hι') x
  · have he : (σ : ℂ →ₐ[ℚ] ℂ).comp (CoefficientField f).val =
        (τ : ℂ →ₐ[ℚ] ℂ).comp (CoefficientField f).val := AlgHom.ext h
    rw [he] at hι
    exact hι.unique hι'

lemma countable_of_le_coefficientField (hF : F ≤ CoefficientField f) : Countable F :=
  (IntermediateField.inclusion hF).injective.countable

lemma exists_mem_rationalPiece_repr_self_eq (hF : F ≤ CoefficientField f) (c : CoefficientField f) :
    ∃ v ∈ f.rationalPiece F, (basis N k).repr v f = c := by
  classical
  have hc : Countable F := countable_of_le_coefficientField hF
  let b : Newform N k → ℂ := fun g ↦
    if h : g ∈ f.galoisOrbitOver F then (h.choose : Gal(ℂ/ℚ)) c else 0
  have hb {σ : Gal(ℂ/ℚ)} (hσ : σ ∈ F.fixingSubgroup) : b (σ • f) = σ c := by
    have h : σ • f ∈ f.galoisOrbitOver F := ⟨σ, hσ, rfl⟩
    simp only [b, h]
    exact smul_eq_smul_iff.mp h.choose_spec.2 c
  let v : cuspFormsNew N k := (basis N k).repr.symm (Finsupp.equivFunOnFinite.symm b)
  have hv (g : Newform N k) : (basis N k).repr v g = b g := by
    simp [v]
  refine ⟨v, mem_rationalPiece_iff.mpr
    ⟨mem_rationalNewspace_of_repr_smul fun τ hτ g ↦ ?_, fun g hg ↦ ?_⟩, ?_⟩
  · rw [hv, hv]
    by_cases hg : g ∈ f.galoisOrbitOver F
    · rcases hg with ⟨σ, hσ, rfl⟩
      rw [smul_smul, hb (mul_mem hτ hσ), hb hσ]
      rfl
    · have hg' : τ • g ∉ f.galoisOrbitOver F := fun h ↦
        hg ((smul_mem_galoisOrbitOver_iff hτ).mp h)
      simp [b, hg, hg']
  · rw [hv]
    simp [b, hg]
  · rw [hv]
    simpa using hb (one_mem F.fixingSubgroup)

/-- **The complex span of a piece is the span of the orbit**: a piece is a form over `F` of the span
of the orbit of `f` under the automorphisms of `ℂ` fixing `F`. -/
lemma span_rationalPiece (hF : F ≤ CoefficientField f) : Submodule.span ℂ
    ((fun u : cuspFormsNew N k ↦ (u : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) ''
      (f.rationalPiece F)) = f.newformSubspaceOver F := by
  classical
  have hc : Countable F := countable_of_le_coefficientField hF
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro _ ⟨v, hv, rfl⟩
    exact hv.2
  · rintro _ ⟨g, hg, rfl⟩
    rcases exists_mem_rationalPiece_repr_self_eq hF 1 with ⟨v, hv, hv₁⟩
    have hT (x : TensorProduct ℚ ℂ (heckeCuspNewRationalAlgebra N k)) :
        (heckeCuspNewComplexify N k x v : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈
          Submodule.span ℂ ((fun v : cuspFormsNew N k ↦
            (v : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) '' (f.rationalPiece F)) := by
      induction x using TensorProduct.inductionOn with
      | tmul c t =>
        rw [heckeCuspNewComplexify_tmul]
        exact Submodule.smul_mem _ c
          (Submodule.subset_span ⟨_, apply_mem_rationalPiece t hv, rfl⟩)
      | add x y hx hy =>
        rw [map_add, LinearMap.add_apply]
        exact add_mem hx hy
    let π : heckeTDiamondCuspNewAlgebra N k :=
      Newform.heckeTDiamondCuspNewAlgebraEquiv.symm (Pi.single g 1)
    have hπ (h : Newform N k) : Newform.heckeTDiamondCuspNewCharacter h π =
        (Pi.single g 1 : Newform N k → ℂ) h := by
      rw [← Newform.heckeTDiamondCuspNewAlgebraEquiv_apply, AlgEquiv.apply_symm_apply]
    have hmem : (π : Module.End ℂ (cuspFormsNew N k)) ∈ (heckeCuspNewComplexify N k).range := by
      rw [range_heckeCuspNewComplexify]
      exact π.2
    rcases hmem with ⟨x, hx⟩
    have hrepr : (basis N k).repr v g = 1 := by
      rcases hg with ⟨σ, hσ, rfl⟩
      rw [repr_smul_of_mem_rationalNewspace hv.1 hσ, hv₁]
      simp
    have hπv : (π : Module.End ℂ (cuspFormsNew N k)) v = basis N k g :=
      (basis N k).repr.injective <| Finsupp.ext fun h ↦ by
        rw [repr_apply_heckeTDiamondCuspNewAlgebra, hπ, (basis N k).repr_self]
        rcases eq_or_ne h g with rfl | hne
        · simp [hrepr]
        · simp [hne]
    have hxv : heckeCuspNewComplexify N k x = (π : Module.End ℂ (cuspFormsNew N k)) := hx
    have hmem' : (basis N k g : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈
        Submodule.span ℂ ((fun v : cuspFormsNew N k ↦
          (v : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) '' (f.rationalPiece F)) := by
      rw [← hπv, ← hxv]
      exact hT x
    rw [coe_basis_apply] at hmem'
    exact hmem'

variable (hF : F ≤ CoefficientField f)

/-- The coordinate along `f`, on the piece of `f`, with values in the coefficient field `ℚ(f)`. -/
noncomputable def rationalPieceCoord :
    f.rationalPiece F →ₗ[F] IntermediateField.extendScalars hF where
  toFun v := ⟨(basis N k).repr (v : cuspFormsNew N k) f, repr_self_mem_coefficientField hF v.2⟩
  map_add' v w := Subtype.ext <| by
    simp only [Submodule.coe_add, map_add]
    rfl
  map_smul' c v := Subtype.ext <|
    ((basis N k).coord f |>.restrictScalars F).map_smul c (v : cuspFormsNew N k)

/-- The coordinate along `f` identifies the piece of `f` with the coefficient field `ℚ(f)`, as
vector spaces over `F`. -/
noncomputable def rationalPieceEquiv : f.rationalPiece F ≃ₗ[F] IntermediateField.extendScalars hF :=
  LinearEquiv.ofBijective (rationalPieceCoord hF)
    ⟨fun v w h ↦ by
      have hsub : ((v - w : f.rationalPiece F) : cuspFormsNew N k) = 0 := by
        refine eq_zero_of_repr_self_eq_zero (v - w).2 ?_
        have h₁ : (basis N k).repr (v : cuspFormsNew N k) f =
            (basis N k).repr (w : cuspFormsNew N k) f := congrArg Subtype.val h
        simp [h₁]
      exact sub_eq_zero.mp (Subtype.ext hsub),
      fun c ↦ by
        rcases exists_mem_rationalPiece_repr_self_eq hF ⟨c, c.2⟩ with ⟨v, hv, hc⟩
        exact ⟨⟨v, hv⟩, Subtype.ext hc⟩⟩

/-- **A piece has dimension `[ℚ(f) : F]` over `F`.** -/
lemma finrank_rationalPiece :
    finrank F (f.rationalPiece F) = finrank F (IntermediateField.extendScalars hF) :=
  (rationalPieceEquiv hF).finrank_eq

/-- **The orbit of `f` under the automorphisms of `ℂ` fixing `F` has `[ℚ(f) : F]` elements.** -/
lemma ncard_galoisOrbitOver :
    (f.galoisOrbitOver F).ncard = finrank F (IntermediateField.extendScalars hF) := by
  have hfin : FiniteDimensional ℚ (IntermediateField.extendScalars hF) :=
    inferInstanceAs (FiniteDimensional ℚ (CoefficientField f))
  have : FiniteDimensional F (IntermediateField.extendScalars hF) :=
    Finite.of_restrictScalars_finite ℚ F _
  have hext (ι : IntermediateField.extendScalars hF →ₐ[F] ℂ) :
      ∃ σ : Gal(ℂ/ℚ), ∀ x : CoefficientField f, σ x = ι ⟨x, x.2⟩ :=
    IntermediateField.exists_algEquiv_apply_eq_of_countable (K := CoefficientField f)
      (ι.restrictScalars ℚ)
  choose ext hext using hext
  let Ψ : (IntermediateField.extendScalars hF →ₐ[F] ℂ) → Newform N k := fun ι ↦ ext ι • f
  have hinj : Function.Injective Ψ := fun ι ι' h ↦ AlgHom.ext fun x ↦ by
    have hx : ext ι x = ext ι' x := smul_eq_smul_iff.mp h ⟨x, x.2⟩
    rw [hext ι ⟨x, x.2⟩, hext ι' ⟨x, x.2⟩] at hx
    exact hx
  have hrange : Set.range Ψ = f.galoisOrbitOver F := by
    refine Set.ext fun g ↦ ⟨?_, ?_⟩
    · rintro ⟨ι, rfl⟩
      refine ⟨ext ι, (IntermediateField.mem_fixingSubgroup_iff _ _).mpr fun x hx ↦ ?_, rfl⟩
      exact (hext ι ⟨x, hF hx⟩).trans (ι.commutes ⟨x, hx⟩)
    · rintro ⟨σ, hσ, rfl⟩
      let σ' : ℂ →ₐ[F] ℂ :=
        { (σ : ℂ →+* ℂ) with
          commutes' := fun r ↦ (IntermediateField.mem_fixingSubgroup_iff _ σ).mp hσ r r.2 }
      let ι : IntermediateField.extendScalars hF →ₐ[F] ℂ :=
        σ'.comp (IntermediateField.extendScalars hF).val
      exact ⟨ι, smul_eq_smul_iff.mpr fun x ↦ hext ι x⟩
  rw [← AlgHom.card F (IntermediateField.extendScalars hF) ℂ, ← Nat.card_eq_fintype_card, ← hrange,
    ← Nat.card_coe_set_eq, Nat.card_range_of_injective hinj]

/-- **The span of the orbit of `f` under the automorphisms of `ℂ` fixing `F` has dimension
`[ℚ(f) : F]`** (LMFDB `cmf.decomposition.new.gamma0chi`). -/
lemma finrank_newformSubspaceOver :
    finrank ℂ (f.newformSubspaceOver F) = finrank F (IntermediateField.extendScalars hF) :=
  (finrank_span_image_toCuspForm _).trans (ncard_galoisOrbitOver hF)

variable [Countable F] in
/-- **The pieces span the forms with coefficients in `F`**, as `f` runs over the newforms. -/
lemma iSup_rationalPiece : ⨆ f : Newform N k, f.rationalPiece F = rationalNewspace N k F := by
  classical
  refine le_antisymm (iSup_le fun f v hv ↦ hv.1) fun v hv ↦ ?_
  let : Fintype (Newform N k) := Fintype.ofFinite _
  let : Fintype (Quotient (galoisOrbitOverRel N k F)) := Fintype.ofFinite _
  let comp : Quotient (galoisOrbitOverRel N k F) → cuspFormsNew N k := fun q ↦
    (basis N k).repr.symm <| Finsupp.equivFunOnFinite.symm fun g ↦
      if (⟦g⟧ : Quotient (galoisOrbitOverRel N k F)) = q then (basis N k).repr v g else 0
  have hcomp (q : Quotient (galoisOrbitOverRel N k F)) (g : Newform N k) :
      (basis N k).repr (comp q) g =
        if (⟦g⟧ : Quotient (galoisOrbitOverRel N k F)) = q then (basis N k).repr v g else 0 := by
    simp [comp]
  have hsum : v = ∑ q, comp q := (basis N k).repr.injective <| Finsupp.ext fun g ↦ by
    rw [map_sum, Finsupp.finsetSum_apply]
    simp [hcomp]
  rw [hsum]
  refine Submodule.sum_mem _ fun q _ ↦ Submodule.mem_iSup_of_mem q.out ?_
  refine mem_rationalPiece_iff.mpr
    ⟨mem_rationalNewspace_of_repr_smul fun σ hσ g ↦ ?_, fun g hg ↦ ?_⟩
  · rw [hcomp, hcomp]
    have hq : (⟦σ • g⟧ : Quotient (galoisOrbitOverRel N k F)) = ⟦g⟧ :=
      Quotient.sound ⟨σ⁻¹, inv_mem hσ, inv_smul_smul σ g⟩
    rw [hq]
    split_ifs
    · exact repr_smul_of_mem_rationalNewspace hv hσ g
    · simp
  · rw [hcomp, ite_eq_right_iff]
    exact fun hgq ↦ absurd (Quotient.exact (q.out_eq.trans hgq.symm)) hg

/-- **The pieces are independent**, as `f` runs over representatives of the orbits of newforms under
the automorphisms of `ℂ` fixing `F`. -/
lemma iSupIndep_rationalPiece :
    iSupIndep fun q : Quotient (galoisOrbitOverRel N k F) ↦ q.out.rationalPiece F := by
  intro q
  let A : Submodule F (cuspFormsNew N k) :=
    { carrier := {v | ∀ g, (⟦g⟧ : Quotient (galoisOrbitOverRel N k F)) = q →
        (basis N k).repr v g = 0}
      add_mem' := fun {v w} hv hw g hg ↦ by
        rw [map_add, Finsupp.add_apply, hv g hg, hw g hg, add_zero]
      zero_mem' := fun g _ ↦ by simp
      smul_mem' := fun c v hv g hg ↦
        (((basis N k).coord g |>.restrictScalars F).map_smul c v).trans <| by
          have h : (basis N k).coord g v = 0 := hv g hg
          simp [h] }
  have hA : ⨆ (q' : Quotient (galoisOrbitOverRel N k F)) (_ : q' ≠ q), q'.out.rationalPiece F ≤ A :=
    iSup₂_le fun q' hq' v hv g hg ↦ (mem_rationalPiece_iff.mp hv).2 g fun hmem ↦
      hq' <| (Quotient.out_eq q').symm.trans <| (Quotient.sound hmem).trans hg
  refine Submodule.disjoint_def.mpr fun v hv hv' ↦ ?_
  refine (basis N k).repr.map_eq_zero_iff.mp <| Finsupp.ext fun g ↦ ?_
  by_cases hg : (⟦g⟧ : Quotient (galoisOrbitOverRel N k F)) = q
  · exact hA hv' g hg
  · exact (mem_rationalPiece_iff.mp hv).2 g fun hmem ↦
      hg <| (Quotient.sound hmem).symm.trans (Quotient.out_eq q)

variable (N k) in
/-- **The newspace has a basis of forms with rational coefficients**, a form of Shimura's theorem
for the newspace (*Introduction to the arithmetic theory of automorphic functions*, Theorem 3.52):
the forms of the newspace with rational coefficients span it over `ℂ`. -/
lemma span_rationalNewspace_bot : Submodule.span ℂ
    ((fun u : cuspFormsNew N k ↦ (u : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) ''
      (rationalNewspace N k ⊥)) = cuspFormsNew N k := by
  refine le_antisymm (Submodule.span_le.mpr ?_)
    (span_range_toCuspForm_eq_cuspFormsNew.ge.trans (Submodule.span_le.mpr ?_))
  · rintro _ ⟨u, -, rfl⟩
    exact u.2
  · rintro _ ⟨g, rfl⟩
    have hg : g.toCuspForm ∈ g.newformSubspaceOver ⊥ :=
      Submodule.subset_span ⟨g, g.self_mem_galoisOrbitOver ⊥, rfl⟩
    rw [← span_rationalPiece bot_le] at hg
    exact Submodule.span_mono (Set.image_mono fun u (hu : u ∈ g.rationalPiece ⊥) ↦ hu.1) hg

variable (f) in
/-- **The orbit over `ℚ` is the Galois orbit.** -/
lemma galoisOrbitOver_bot : f.galoisOrbitOver ⊥ = f.galoisOrbit := by
  refine Set.ext fun g ↦ ⟨?_, ?_⟩
  · rintro ⟨σ, -, rfl⟩
    exact ⟨σ, f.isGaloisConjugateBy_smul σ⟩
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, (IntermediateField.mem_fixingSubgroup_iff _ σ).mpr fun x hx ↦ ?_,
      (smul_eq_iff σ).mpr hσ⟩
    rcases IntermediateField.mem_bot.mp hx with ⟨r, rfl⟩
    exact σ.commutes r

variable (f) in
/-- **The span of the orbit over `ℚ` is the newform subspace.** -/
lemma newformSubspaceOver_bot : f.newformSubspaceOver ⊥ = f.newformSubspace := by
  rw [newformSubspaceOver, galoisOrbitOver_bot, newformSubspace]

variable (f) in
/-- **The orbit over the field `ℚ(χ)` of values of the nebentypus `χ` of `f` is the set of the
Galois conjugates of `f` of nebentypus `χ`.** -/
lemma galoisOrbitOver_characterField :
    f.galoisOrbitOver (CharacterField f.χ) = {g ∈ f.galoisOrbit | g.χ = f.χ} := by
  refine Set.ext fun g ↦ ⟨?_, ?_⟩
  · rintro ⟨σ, hσ, rfl⟩
    refine ⟨⟨σ, f.isGaloisConjugateBy_smul σ⟩, ?_⟩
    refine MonoidHom.ext fun u ↦ Units.ext ?_
    rw [(f.isGaloisConjugateBy_smul σ).χ_apply]
    exact (mem_fixingSubgroup_characterField_iff σ).mp hσ u
  · rintro ⟨⟨σ, hσ⟩, hχ⟩
    refine ⟨σ, (mem_fixingSubgroup_characterField_iff σ).mpr fun u ↦ ?_, (smul_eq_iff σ).mpr hσ⟩
    rw [← hσ.χ_apply, hχ]

variable (f) in
/-- **The span of the orbit over `ℚ(χ)` is the `χ`-part of the newform subspace.** -/
lemma newformSubspaceOver_characterField :
    f.newformSubspaceOver (CharacterField f.χ) = f.newformSubspace ⊓ cuspFormCharSpace k f.χ := by
  rw [newformSubspaceOver, galoisOrbitOver_characterField, newformSubspace,
    span_image_toCuspForm_inf_cuspFormCharSpace]

variable (f) in
/-- **The relative dimension of a newform is the relative degree of its coefficient field**
(LMFDB `cmf.decomposition.new.gamma0chi`): the `χ`-part of the newform subspace of `f` has dimension
`[ℚ(f) : ℚ(χ)]`. -/
lemma relativeDimension_eq_finrank : f.relativeDimension = finrank (CharacterField f.χ)
    (IntermediateField.extendScalars (CharacterField_le_CoefficientField f)) := by
  rw [relativeDimension, ← newformSubspaceOver_characterField]
  exact finrank_newformSubspaceOver _

end HeckeRing.GL2.Newform

namespace HeckeRing.GL2.NewformOrbit

variable {N : ℕ} [NeZero N] {k : ℤ} (χ : (ZMod N)ˣ →* ℂˣ)

/-- **The `χ`-parts of the spans of the Galois orbits are independent.** -/
lemma iSupIndep_newformSubspace_inf_cuspFormCharSpace :
    iSupIndep fun O : NewformOrbit N k ↦ O.newformSubspace ⊓ cuspFormCharSpace k χ :=
  iSupIndep_newformSubspace.mono fun _ ↦ inf_le_left

/-- **The space of newforms of nebentypus `χ` is the sum of the `χ`-parts of the spans of the Galois
orbits** (LMFDB `cmf.decomposition.new.gamma0chi`, `cmf.newspaces`). -/
lemma iSup_newformSubspace_inf_cuspFormCharSpace : ⨆ O : NewformOrbit N k,
    O.newformSubspace ⊓ cuspFormCharSpace k χ = cuspFormsNew N k ⊓ cuspFormCharSpace k χ := by
  rw [← Newform.span_image_toCuspForm_eq_cuspFormsNew_inf_cuspFormCharSpace]
  simp only [newformSubspace, Newform.span_image_toCuspForm_inf_cuspFormCharSpace,
    ← Submodule.span_iUnion]
  congr 2
  ext g
  simp

end HeckeRing.GL2.NewformOrbit
