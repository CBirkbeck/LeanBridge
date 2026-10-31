import TauCeti.Algebra.GroupWithZero.Divisibility
import TauCeti.NumberTheory.ModularForms.Newforms.Decomposition
import TauCeti.NumberTheory.ModularForms.QExpansion.Basic

/-!
# The old-space decomposition of spaces of cusp forms

For `M ∣ N` and `t ∣ N / M`, the level-raising map `α_{M,t} : S_k(Γ₁(M)) → S_k(Γ₁(N))`,
`f(q) ↦ f(q^t)` (Tau Ceti's `TauCeti.CuspForm.levelRaise`), is injective, and the LMFDB states
the decomposition (LMFDB `cmf.decomposition.old.gamma1`; Diamond–Shurman, Theorem 5.8.3)

`S_k(Γ₁(N)) = ⨁_{M ∣ N} ⨁_{t ∣ N/M} α_{M,t}(S_k^new(Γ₁(M)))`,

and, for a character `χ` modulo `N` (LMFDB `cmf.decomposition.old.gamma0chi`),
`S_k(N, χ) = ⨁_{cond(χ) ∣ M ∣ N} ⨁_{d ∣ N/M} α_{M,d}(S_k^new(M, χ_M))`, with `χ_M` the character
modulo `M` inducing `χ`.

That the images span is Tau Ceti's `HeckeRing.GL2.Newform.span_levelRaise_eq_top`. That the sum is
direct rests on strong multiplicity one across levels (Atkin–Lehner, Li; Miyake, Theorem 4.6.19):
two newforms of levels dividing `N`, with the same character and the same eigenvalues at the
primes not dividing `N`, are equal. This is not in the pinned Tau Ceti, which has it when one of
the two levels divides the other and the eigenvalues agree at every prime prime to the larger
level (`HeckeRing.GL2.Newform.level_eq_of_dvd_of_forall_prime_eigenvalue_eq`); it enters here as
the explicit hypothesis `HeckeRing.GL2.Newform.CrossLevelMultiplicityOne`. Everything else is
proved: eigenvectors of the good Hecke operators and of the diamond operators with different
eigenvalues are independent, and the forms `f(q^t)` attached to one newform `f` are independent
by their `q`-expansions.

## Main definitions

* `HeckeRing.GL2.Newform.newformLevelRaise` (LMFDB `cmf.decomposition.old.gamma1`): the image
  `α_{M,t}(S_k^new(Γ₁(M)))`.
* `HeckeRing.GL2.Newform.newformCharLevelRaise` (LMFDB `cmf.decomposition.old.gamma0chi`): the
  image `α_{M,d}(S_k^new(M, χ_M))`.
* `HeckeRing.GL2.Newform.CrossLevelMultiplicityOne`: strong multiplicity one across the levels
  dividing `N`, the hypothesis of the independence statements.

## Main results

* `HeckeRing.GL2.Newform.iSup_newformLevelRaise`: the images `α_{M,t}(S_k^new(Γ₁(M)))` span
  `S_k(Γ₁(N))`.
* `HeckeRing.GL2.Newform.linearIndependent_levelRaise`: the forms `f(q^t)` are linearly
  independent, given strong multiplicity one across levels.
* `HeckeRing.GL2.Newform.iSupIndep_newformLevelRaise`,
  `HeckeRing.GL2.Newform.isInternal_newformLevelRaise`: the decomposition of `S_k(Γ₁(N))`, given
  strong multiplicity one across levels.
* `HeckeRing.GL2.Newform.iSup_newformCharLevelRaise`,
  `HeckeRing.GL2.Newform.iSupIndep_newformCharLevelRaise`: the decomposition of `S_k(N, χ)`, the
  second given strong multiplicity one across levels.
-/

open Matrix SpecialLinearGroup CongruenceSubgroup TauCeti Module

namespace PowerSeries

lemma linearIndependent_expand {X : Type*} {t : X → ℕ} (ht : Function.Injective t)
    (ht0 : ∀ x, t x ≠ 0) {A : PowerSeries ℂ} (hA : A.coeff 1 ≠ 0) :
    LinearIndependent ℂ fun x ↦ expand (t x) (ht0 x) A := by
  classical
  rw [linearIndependent_iff']
  intro s c hs x hx
  by_contra hcx
  rcases (s.filter fun y ↦ c y ≠ 0).exists_min_image t
    ⟨x, Finset.mem_filter.mpr ⟨hx, hcx⟩⟩ with ⟨x₀, hx₀, hmin⟩
  rw [Finset.mem_filter] at hx₀
  have hcoeff : coeff (t x₀) (∑ y ∈ s, c y • expand (t y) (ht0 y) A) = coeff (t x₀) 0 :=
    congrArg _ hs
  rw [map_sum, map_zero, Finset.sum_eq_single x₀] at hcoeff
  · rw [map_smul, coeff_expand, ite_eq_left dvd_rfl, Nat.div_self (Nat.pos_of_ne_zero (ht0 x₀)),
      smul_eq_mul] at hcoeff
    exact mul_ne_zero hx₀.2 hA hcoeff
  · intro y hy hyx₀
    rw [map_smul, coeff_expand]
    split_ifs with hdvd
    · by_cases hcy : c y = 0
      · rw [hcy, zero_smul]
      · exact absurd (ht ((Nat.le_of_dvd (Nat.pos_of_ne_zero (ht0 x₀)) hdvd).antisymm
          (hmin y (Finset.mem_filter.mpr ⟨hy, hcy⟩)))) hyx₀
    · rw [smul_zero]
  · exact fun hx₀s ↦ absurd hx₀.1 hx₀s

end PowerSeries

namespace HeckeRing.GL2.Newform

variable (N : ℕ) [NeZero N] (k : ℤ) (χ : (ZMod N)ˣ →* ℂˣ)

/-- The index set of the old-space decomposition at level `N`: the pairs `(M, t)` of positive
integers with `t M ∣ N`, the pair `(M, t)` standing for the level-raising map `α_{M,t}`. -/
abbrev LevelRaiseIndex : Type :=
  {p : ℕ × ℕ // p.2 * p.1 ∣ N}

variable (i : LevelRaiseIndex N)

instance : NeZero i.1.1 :=
  NeZero.of_dvd (dvd_of_mul_left_dvd i.2)

instance : NeZero i.1.2 :=
  NeZero.of_dvd (dvd_of_mul_right_dvd i.2)

/-- The image `α_{M,t}(S_k^new(Γ₁(M)))` (LMFDB `cmf.decomposition.old.gamma1`) of the new
subspace of level `M` in `S_k(Γ₁(N))` under the level-raising map `α_{M,t}`, `f(q) ↦ f(q^t)`
(Tau Ceti's `TauCeti.CuspForm.levelRaise`), for `t M ∣ N`. The map is injective
(`TauCeti.CuspForm.levelRaiseₗ_injective`), so the image is a copy of `S_k^new(Γ₁(M))`. -/
noncomputable def newformLevelRaise : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  (cuspFormsNew i.1.1 k).map (CuspForm.levelRaiseₗ i.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd i.2))

/-- **Strong multiplicity one across the levels dividing `N`** (Atkin–Lehner, Li; Miyake,
Theorem 4.6.19): two newforms of weight `k` and levels `M₁, M₂ ∣ N`, whose nebentypes induce the
same character modulo `N` and whose eigenvalues agree at every prime not dividing `N`, have the
same level and are the same function. It is the hypothesis of the independence statements of this
file, and it is not proved: the pinned Tau Ceti has it when one level divides the other and the
eigenvalues agree at every prime prime to the larger level
(`HeckeRing.GL2.Newform.level_eq_of_dvd_of_forall_prime_eigenvalue_eq`), and at a fixed level
when the eigenvalues agree at every index outside a finite set
(`HeckeRing.GL2.Newform.eq_of_forall_notMem_eigenvalue_eq`), but neither the case of two levels
neither of which divides the other nor agreement away from finitely many primes. -/
def CrossLevelMultiplicityOne : Prop :=
  ∀ (M₁ M₂ : ℕ) [NeZero M₁] [NeZero M₂] (h₁ : M₁ ∣ N) (h₂ : M₂ ∣ N) (g₁ : Newform M₁ k)
    (g₂ : Newform M₂ k), g₁.χ.comp (ZMod.unitsMap h₁) = g₂.χ.comp (ZMod.unitsMap h₂) →
    (∀ (p : ℕ) (hp : p.Prime) (hpN : p.Coprime N), g₁.eigenvalue ⟨p, hp.pos⟩
      (hpN.coprime_dvd_right h₁) = g₂.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right h₂)) →
    ((M₁, ⇑g₁.toCuspForm) : ℕ × (UpperHalfPlane → ℂ)) = (M₂, ⇑g₂.toCuspForm)

/-- **The images `α_{M,t}(S_k^new(Γ₁(M)))` span `S_k(Γ₁(N))`** (Tau Ceti's
`HeckeRing.GL2.Newform.span_levelRaise_eq_top`). -/
lemma iSup_newformLevelRaise : ⨆ i, newformLevelRaise N k i = ⊤ := by
  refine eq_top_iff.mpr ((span_levelRaise_eq_top N k).ge.trans (Submodule.span_le.mpr ?_))
  rintro _ ⟨M, d, _, _, hdM, g, rfl⟩
  exact Submodule.mem_iSup_of_mem (⟨(M, d), hdM⟩ : LevelRaiseIndex N)
    (Submodule.mem_map_of_mem g.isNew)

variable {N k}

/-- **The level-raised newforms are linearly independent**, given strong multiplicity one across
levels (Diamond–Shurman, Theorem 5.8.3): the forms `f(q^t)`, for the newforms `f` of the levels
`M` and the `t` with `t M ∣ N`, are linearly independent in `S_k(Γ₁(N))`. Eigenvectors of the
good Hecke operators and of the diamond operators with different eigenvalues are independent;
those with the same eigenvalues come from a single newform `f`, and the `f(q^t)` are independent
by their `q`-expansions. -/
lemma linearIndependent_levelRaise (h : CrossLevelMultiplicityOne N k) :
    LinearIndependent ℂ fun j : Σ i : LevelRaiseIndex N, Newform i.1.1 k ↦
      CuspForm.levelRaise j.1.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd j.1.2) j.2.toCuspForm := by
  classical
  let J : Type := Σ i : LevelRaiseIndex N, Newform i.1.1 k
  let v : J → CuspForm ((Gamma1 N).map (mapGL ℝ)) k := fun j ↦
    CuspForm.levelRaise j.1.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd j.1.2) j.2.toCuspForm
  -- the good Hecke operators and the diamond operators, and the eigenvalues of each `v j`
  let T : {p : ℕ // p.Prime ∧ p.Coprime N} ⊕ (ZMod N)ˣ →
      Module.End ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    Sum.elim (fun p ↦ have : NeZero p.1 := ⟨p.2.1.ne_zero⟩
      heckeTCuspNat k p.1) (diamondOpCusp k)
  let sig : J → {p : ℕ // p.Prime ∧ p.Coprime N} ⊕ (ZMod N)ˣ → ℂ := fun j ↦
    Sum.elim (fun p ↦ j.2.eigenvalue ⟨p.1, p.2.1.pos⟩
      (p.2.2.coprime_dvd_right (dvd_of_mul_left_dvd j.1.2)))
      fun d ↦ (j.2.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd j.1.2)) d : ℂ)
  have hmem : ∀ j, v j ∈ ⨅ o, (T o).eigenspace (sig j o) := by
    rintro ⟨i, g⟩
    refine Submodule.mem_iInf _ |>.mpr fun o ↦ End.mem_eigenspace_iff.mpr ?_
    rcases o with p | d
    · exact g.heckeTCuspNat_levelRaise_eq_eigenvalue_smul i.2 p.2.1 p.2.2
    · exact diamondOpCusp_apply_of_mem_cuspFormCharSpace k _ d
        (CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd i.2 g.χ g.mem_charSpace)
  -- the fibres of `sig` lie in independent joint eigenspaces
  have hspan : ∀ s, Submodule.span ℂ (Set.range fun x : {j // sig j = s} ↦ v x.1) ≤
      ⨅ o, (T o).eigenspace (s o) := fun s ↦ Submodule.span_le.mpr <| by
    rintro _ ⟨⟨j, rfl⟩, rfl⟩
    exact hmem j
  have hd : ∀ s, ∀ t : Set ({p : ℕ // p.Prime ∧ p.Coprime N} ⊕ (ZMod N)ˣ → ℂ), t.Finite →
      s ∉ t → Disjoint (Submodule.span ℂ (Set.range fun x : {j // sig j = s} ↦ v x.1))
        (⨆ s' ∈ t, Submodule.span ℂ (Set.range fun x : {j // sig j = s'} ↦ v x.1)) :=
    fun s _ _ hst ↦ ((iSupIndep_iInf_eigenspace T).disjoint_biSup hst).mono (hspan s)
      (iSup₂_mono fun s' _ ↦ hspan s')
  -- in a fibre all the newforms are one newform, raised by distinct `t`
  have hindep : ∀ s, LinearIndependent ℂ fun x : {j // sig j = s} ↦ v x.1 := by
    intro s
    rcases isEmpty_or_nonempty {j // sig j = s} with hs | hs
    · exact linearIndependent_empty_type
    rcases hs with ⟨j₀⟩
    have hsame : ∀ x : {j // sig j = s}, ((x.1.1.1.1, ⇑x.1.2.toCuspForm) :
        ℕ × (UpperHalfPlane → ℂ)) = (j₀.1.1.1.1, ⇑j₀.1.2.toCuspForm) := by
      intro x
      have hsig : sig x.1 = sig j₀.1 := x.2.trans j₀.2.symm
      refine h _ _ (dvd_of_mul_left_dvd x.1.1.2) (dvd_of_mul_left_dvd j₀.1.1.2) x.1.2 j₀.1.2 ?_
        fun p hp hpN ↦ congrFun hsig (.inl ⟨p, hp, hpN⟩)
      exact MonoidHom.ext fun d ↦ Units.ext (congrFun hsig (.inr d))
    have ht : Function.Injective fun x : {j // sig j = s} ↦ x.1.1.1.2 := by
      rintro ⟨⟨i, g⟩, hx⟩ ⟨⟨i', g'⟩, hx'⟩ htt
      rcases Prod.mk_inj.mp ((hsame ⟨_, hx⟩).trans (hsame ⟨_, hx'⟩).symm) with ⟨hM, hg⟩
      have hi : i = i' := Subtype.ext (Prod.ext hM htt)
      subst hi
      have hgg : g = g' := Newform.ext (CuspForm.ext fun z ↦ congrFun hg z)
      subst hgg
      rfl
    have hA : (UpperHalfPlane.qExpansion 1 j₀.1.2.toCuspForm).coeff 1 ≠ 0 := by
      rw [j₀.1.2.isNorm]
      exact one_ne_zero
    refine LinearIndependent.of_comp ((ModularForm.qExpansionLinearMap one_pos
      (one_mem_strictPeriods_Gamma1_map N) k).comp CuspForm.toModularFormₗ) ?_
    convert PowerSeries.linearIndependent_expand ht (fun x ↦ NeZero.ne x.1.1.1.2) hA using 1
    funext x
    simp only [LinearMap.coe_comp, Function.comp_apply]
    rw [ModularForm.qExpansionLinearMap_apply, CuspForm.toModularFormₗ_eq_coe,
      ModularFormClass.coe_modularForm, CuspForm.qExpansion_levelRaise
        (one_mem_strictPeriods_Gamma1_map _) (one_mem_strictPeriods_Gamma1_map _),
      (Prod.mk_inj.mp (hsame x)).2]
  have hfib : LinearIndependent ℂ fun ji : Σ s, {j // sig j = s} ↦ v ji.2.1 :=
    linearIndependent_iUnion_finite (ιs := fun s ↦ {j // sig j = s})
      (f := fun s (x : {j // sig j = s}) ↦ v x.1) hindep hd
  exact (linearIndependent_equiv' (Equiv.sigmaFiberEquiv sig) (f := v)
    (g := fun ji : Σ s, {j // sig j = s} ↦ v ji.2.1) rfl).mp hfib

lemma newformLevelRaise_le_span : newformLevelRaise N k i ≤ Submodule.span ℂ
    ((fun j : Σ i : LevelRaiseIndex N, Newform i.1.1 k ↦ CuspForm.levelRaise j.1.1.2
      (Gamma1_map_le_conjAct_scaleGL_of_dvd j.1.2) j.2.toCuspForm) '' {j | j.1 = i}) := by
  rw [newformLevelRaise, ← span_range_toCuspForm_eq_cuspFormsNew, Submodule.map_span]
  refine Submodule.span_mono ?_
  rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
  exact ⟨⟨i, g⟩, rfl, rfl⟩

/-- **The images `α_{M,t}(S_k^new(Γ₁(M)))` are independent**, given strong multiplicity one
across levels. -/
lemma iSupIndep_newformLevelRaise (h : CrossLevelMultiplicityOne N k) :
    iSupIndep (newformLevelRaise N k) := by
  refine iSupIndep_def.mpr fun i ↦ ((linearIndependent_levelRaise h).disjoint_span_image
    (s := {j | j.1 = i}) (t := {j | j.1 ≠ i}) ?_).mono (newformLevelRaise_le_span i)
      (iSup₂_le fun i' hi' ↦ (newformLevelRaise_le_span i').trans (Submodule.span_mono ?_))
  · exact Set.disjoint_left.mpr fun j hj hj' ↦ hj' hj
  · rintro _ ⟨j, hj, rfl⟩
    exact ⟨j, (hj : j.1 = i').trans_ne hi', rfl⟩

/-- **The old-space decomposition** (LMFDB `cmf.decomposition.old.gamma1`; Diamond–Shurman,
Theorem 5.8.3), given strong multiplicity one across levels: `S_k(Γ₁(N))` is the internal direct
sum of the images `α_{M,t}(S_k^new(Γ₁(M)))` over the pairs `(M, t)` with `t M ∣ N`. -/
lemma isInternal_newformLevelRaise (h : CrossLevelMultiplicityOne N k) :
    DirectSum.IsInternal (newformLevelRaise N k) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top (iSupIndep_newformLevelRaise h)
    (iSup_newformLevelRaise N k)

variable (k) in
/-- The image `α_{M,t}(S_k^new(M, χ_M))` (LMFDB `cmf.decomposition.old.gamma0chi`) in
`S_k(N, χ)`, for `t M ∣ N`, where `χ_M` runs over the characters modulo `M` that induce `χ`:
there is exactly one when the conductor of `χ` divides `M`, and none otherwise, when the image
is `0`. -/
noncomputable def newformCharLevelRaise : Submodule ℂ (CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
  ⨆ (ψ : (ZMod i.1.1)ˣ →* ℂˣ) (_ : ψ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd i.2)) = χ),
    (cuspFormsNew i.1.1 k ⊓ cuspFormCharSpace k ψ).map
      (CuspForm.levelRaiseₗ i.1.2 (Gamma1_map_le_conjAct_scaleGL_of_dvd i.2))

lemma newformCharLevelRaise_le_newformLevelRaise :
    newformCharLevelRaise k χ i ≤ newformLevelRaise N k i :=
  iSup₂_le fun _ _ ↦ Submodule.map_mono inf_le_left

lemma newformCharLevelRaise_le_cuspFormCharSpace :
    newformCharLevelRaise k χ i ≤ cuspFormCharSpace k χ := by
  refine iSup₂_le fun ψ hψ ↦ ?_
  rintro _ ⟨g, hg, rfl⟩
  rw [CuspForm.levelRaiseₗ_apply, ← hψ]
  exact CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd i.2 ψ hg.2

/-- **The images `α_{M,d}(S_k^new(M, χ_M))` are independent**, given strong multiplicity one
across levels (LMFDB `cmf.decomposition.old.gamma0chi`). -/
lemma iSupIndep_newformCharLevelRaise (h : CrossLevelMultiplicityOne N k) :
    iSupIndep (newformCharLevelRaise k χ) :=
  (iSupIndep_newformLevelRaise h).mono (newformCharLevelRaise_le_newformLevelRaise χ)

/-- **The images `α_{M,d}(S_k^new(M, χ_M))` span `S_k(N, χ)`** (LMFDB
`cmf.decomposition.old.gamma0chi`). -/
lemma iSup_newformCharLevelRaise :
    ⨆ i, newformCharLevelRaise k χ i = cuspFormCharSpace k χ := by
  have hle : ⨆ i, newformCharLevelRaise k χ i ≤ cuspFormCharSpace k χ :=
    iSup_le (newformCharLevelRaise_le_cuspFormCharSpace χ)
  refine hle.antisymm fun F hF ↦ ?_
  -- a level-raised newform lies in an image of the family or in another nebentypus space
  have hFmem : F ∈ (⨆ i, newformCharLevelRaise k χ i) ⊔
      ⨆ (ψ : (ZMod N)ˣ →* ℂˣ) (_ : ψ ≠ χ), cuspFormCharSpace k ψ := by
    refine (span_levelRaise_eq_top N k).ge.trans (Submodule.span_le.mpr ?_) Submodule.mem_top
    rintro _ ⟨M, d, _, _, hdM, g, rfl⟩
    by_cases hgχ : g.χ.comp (ZMod.unitsMap (dvd_of_mul_left_dvd hdM)) = χ
    · exact Submodule.mem_sup_left (Submodule.mem_iSup_of_mem (⟨(M, d), hdM⟩ : LevelRaiseIndex N)
        (Submodule.mem_iSup_of_mem g.χ (Submodule.mem_iSup_of_mem hgχ
          (Submodule.mem_map_of_mem ⟨g.isNew, g.mem_charSpace⟩))))
    · exact Submodule.mem_sup_right (Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hgχ
        (CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd hdM g.χ g.mem_charSpace)))
  -- the component in the other nebentypus spaces lies in `S_k(N, χ)`, hence is zero
  rcases Submodule.mem_sup.mp hFmem with ⟨x, hx, y, hy, rfl⟩
  have hyχ : y ∈ cuspFormCharSpace k χ := by
    simpa using Submodule.sub_mem _ hF (hle hx)
  rwa [(Submodule.disjoint_def.mp (iSupIndep_def.mp (iSupIndep_cuspFormCharSpace k) χ)) y hyχ hy,
    add_zero]

end HeckeRing.GL2.Newform
