import LeanBridge.ForMathlib.NumberTheory.LocalField.ExtensionFamilyFinite

/-!
# Bands and specialisations of Eisenstein diagrams

Let `I = [s_1, …, s_w]_ε^f` be a Herbrand invariant at a prime `p`, with means `m_k`, and `K` a
`p`-adic field whose residue field has `q` elements. The Eisenstein diagram of `I / K` (LMFDB
`lf.eisenstein_diagram`, `IsNonarchimedeanLocalField.HerbrandInvariant.eisensteinDiagram`) is drawn
with the bands `B_k = {m_k ≤ s < s_k}`, and its points give the shape of the generic polynomial
`x ^ e + π ∑_σ f_σ π ^ j x ^ i` over the ring of integers of the unramified extension `K_f` of `K`
of degree `f`. This file proves the knowl's remarks on the bands and on the dependence of the
diagram on `K`, and its count of the specialisations of the generic polynomial.

* As `k` increases, the bottom edges `m_k` of the bands strictly increase, while the top edges `s_k`
  only weakly increase (a monotonicity lemma of
  `LeanBridge.ForMathlib.NumberTheory.LocalField.MongeConverse`); in a segment of equal `s_k`, the
  widths `r_k' = s_k - m_k` of the bands successively decrease by the factor `p`.
* The diagram depends on `K` only through whether `gcd(ε, q ^ f - 1) > 1`, and not at all when
  `ε = 1`.
* When the additional constraints on `c_σ` and `d_0` are ignored, the coefficients are drawn from a
  set `ℛ ∋ 0` of `q ^ f` representatives of the residue field of `K_f`: `d_0 ∈ ℛ ∖ {0}` if the
  `D`-point is critical and `d_0 = 1` otherwise, `a_σ ∈ ℛ ∖ {0}` at the `A`-points, and `b_σ ∈ ℛ`,
  `c_σ ∈ ℛ` at the `B`-points and the critical `C`-points. Distinct choices give distinct
  polynomials, since `π`-adic digits in `ℛ` are unique, so there are
  `(q ^ f - 1) ^ (δ + α) q ^ (f β + f γ)` specialisations, `δ ∈ {0, 1}` being the number of
  critical `D`-points and `α`, `β`, `γ` the numbers of `A`-points, `B`-points and critical
  `C`-points.

The knowl's other claims are not proved here: that each extension `L` in `I / K` is represented by
`(q ^ f - 1) ^ δ q ^ (f γ) / |Aut(L / K)|` specialisations, which is the second statement of
Monge's Theorem 1, the mass formula `M(I / K) = (q ^ f - 1) ^ α q ^ (f β)` and its rigid case,
which follow from it, and the two point counts given by the rams. The first point count, that `B_k`
contains `⌈r_k⌉` drawn points of index at most `k`, can fail when `k` is not final in its segment:
for `I = (1/3, 1/3)_1^1` at `p = 2`, the invariant of `ℚ_2[x] / (x ^ 4 + 2 x + 2)`, the band
`B_1 = {1/6 ≤ s < 1/3}` contains only `P_1 = (1, 1/4)`, of index `2`, while `⌈r_1⌉ = 1`.

## Main definitions

* `IsNonarchimedeanLocalField.HerbrandInvariant.freeCoeffSet` (LMFDB `lf.eisenstein_diagram`): the
  coefficient sets of the specialisations when the constraints on `c_σ` and `d_0` are ignored.

## Main results

* `IsNonarchimedeanLocalField.HerbrandInvariant.strictMonoOn_mean` (LMFDB `lf.eisenstein_diagram`):
  the bottom edges of the bands go up.
* `IsNonarchimedeanLocalField.HerbrandInvariant.tinyRam_add_one_of_swanSlope_eq`: in a segment, the
  widths of the bands decrease by the factor `p`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.eisensteinDiagram_eq_of_iff` and
  `IsNonarchimedeanLocalField.HerbrandInvariant.eisensteinDiagram_eq_of_ε_eq_one`: the diagram
  depends on `K` only through whether `gcd(ε, q ^ f - 1) > 1`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.ncard_specialisations_unramifiedExtension` (LMFDB
  `lf.eisenstein_diagram`): the number of specialisations.
-/

open Finset Polynomial TauCeti ValuativeRel

namespace IsNonarchimedeanLocalField.HerbrandInvariant

variable {p : ℕ} (I : HerbrandInvariant p)

lemma mean_lt_mean_add_one (hp : 1 < p) {k : ℕ} (hk : k < I.w) : I.mean k < I.mean (k + 1) := by
  have hr : 0 < I.ram (k + 1) :=
    (I.zero_lt_ram_one (by omega)).trans_le (I.monotone_ram (by omega))
  have hp₀ : (0 : ℚ) < p := by
    exact_mod_cast zero_lt_one.trans hp
  have hp₁ : (0 : ℚ) < p - 1 :=
    sub_pos.mpr (by exact_mod_cast hp)
  rw [mean_succ, lt_add_iff_pos_right, smallRam]
  exact div_pos (mul_pos hp₁ hr) (mul_pos I.natCast_ε_pos (pow_pos hp₀ _))

/-- **The bottom edges of the bands go up** (LMFDB `lf.eisenstein_diagram`): the means `m_k`, the
bottom edges of the bands `B_k`, strictly increase for `0 ≤ k ≤ w`. -/
lemma strictMonoOn_mean (hp : 1 < p) : StrictMonoOn I.mean (Set.Iic I.w) :=
  strictMonoOn_Iic_of_lt_succ fun _ hk ↦ I.mean_lt_mean_add_one hp hk

/-- **In a segment, the widths of the bands decrease by the factor `p`** (LMFDB
`lf.eisenstein_diagram`): if `s_{k + 1} = s_k`, the band `B_{k + 1}` has the same top edge as
`B_k` and the width `r_{k + 1}' = r_k' / p`, the width `s_k - m_k` of `B_k` being the tiny ram
`r_k'` (`IsNonarchimedeanLocalField.HerbrandInvariant.tinyRam_eq_swanSlope_sub_mean`). -/
lemma tinyRam_add_one_of_swanSlope_eq (hp : p ≠ 0) {k : ℕ}
    (h : I.swanSlope (k + 1) = I.swanSlope k) : I.tinyRam (k + 1) = I.tinyRam k / p := by
  have hε : (I.ε : ℚ) ≠ 0 :=
    I.natCast_ε_pos.ne'
  have hp' : (p : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hp
  rw [swanSlope, swanSlope, sum_range_succ, add_eq_left, div_eq_zero_iff, sub_eq_zero] at h
  rcases h with h | h
  · rw [tinyRam, tinyRam, h, pow_succ]
    field_simp
  · exact absurd h (mul_ne_zero hε (pow_ne_zero _ hp'))

/-- **The Eisenstein diagram depends on `K` only through `gcd(ε, q ^ f - 1) > 1`** (LMFDB
`lf.eisenstein_diagram`): for residue fields of `q` and `q'` elements, the diagrams agree as soon as
`gcd(ε, q ^ f - 1) > 1` and `gcd(ε, q' ^ f - 1) > 1` are equivalent. -/
lemma eisensteinDiagram_eq_of_iff {q q' : ℕ}
    (h : 1 < I.ε.gcd (q ^ I.f - 1) ↔ 1 < I.ε.gcd (q' ^ I.f - 1)) :
    I.eisensteinDiagram q = I.eisensteinDiagram q' := by
  have hc : I.IsCritical q = I.IsCritical q' := by
    ext σ
    simp only [IsCritical, h]
  funext σ
  rw [eisensteinDiagram, eisensteinDiagram, hc]

/-- **For `ε = 1` the Eisenstein diagram does not depend on `K`** (LMFDB
`lf.eisenstein_diagram`). -/
lemma eisensteinDiagram_eq_of_ε_eq_one (h : I.ε = 1) (q q' : ℕ) :
    I.eisensteinDiagram q = I.eisensteinDiagram q' :=
  I.eisensteinDiagram_eq_of_iff <| by simp [h]

lemma pointType_eq_D_iff {σ : ℕ} : I.pointType σ = .D ↔ σ = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ I.pointType_zero⟩
  by_contra hσ
  rw [pointType, ite_eq_right hσ] at h
  split_ifs at h

lemma pointType_of_mem_genericIndices {σ : ℕ} (hσ : σ ∈ I.genericIndices) (h₀ : σ ≠ 0)
    (hA : I.pointType σ ≠ .A) : I.pointType σ = .B ∨ I.pointType σ = .C := by
  rcases (mem_filter.mp hσ).2 with h | h | h | ⟨h, -⟩
  · exact absurd (I.pointType_eq_D_iff.mp h) h₀
  · exact absurd h hA
  · exact .inl h
  · exact .inr h

variable {R : Type*} [CommRing R] (q : ℕ) (ℛ : Set R)

open Classical in
/-- The set from which the coefficient `f_σ` of a **specialisation of the generic polynomial** is
drawn **when the additional constraints on `c_σ` and `d_0` are ignored** (LMFDB
`lf.eisenstein_diagram`), for a set `ℛ ∋ 0` of representatives of the residue field of `K_f` and a
residue field of `K` with `q` elements: `d_0 ∈ ℛ ∖ {0}` if the `D`-point is critical and `d_0 = 1`
if it is negligible, `a_σ ∈ ℛ ∖ {0}` at an `A`-point, `b_σ ∈ ℛ` and `c_σ ∈ ℛ` at a `B`-point and at
a `C`-point, and `0` at a `Z`-point. -/
noncomputable def freeCoeffSet (σ : ℕ) : Set R :=
  match I.pointType σ with
  | .D => if I.IsCritical q 0 then ℛ \ {0} else {1}
  | .A => ℛ \ {0}
  | .B => ℛ
  | .C => ℛ
  | .Z => {0}

open Classical in
lemma natCard_freeCoeffSet (h₀ : 0 ∈ ℛ) {σ : ℕ} (hσ : σ ∈ I.genericIndices) :
    Nat.card (I.freeCoeffSet q ℛ σ) = if σ = 0 then (if I.IsCritical q 0 then ℛ.ncard - 1 else 1)
      else if I.pointType σ = .A then ℛ.ncard - 1 else ℛ.ncard := by
  rw [Nat.card_coe_set_eq]
  by_cases hσ₀ : σ = 0
  · rw [ite_eq_left hσ₀, freeCoeffSet, hσ₀, pointType_zero]
    split_ifs
    · exact Set.ncard_sdiff_singleton_of_mem h₀
    · exact Set.ncard_singleton 1
  rw [ite_eq_right hσ₀]
  by_cases hA : I.pointType σ = .A
  · rw [ite_eq_left hA, freeCoeffSet, hA]
    exact Set.ncard_sdiff_singleton_of_mem h₀
  rw [ite_eq_right hA]
  rcases I.pointType_of_mem_genericIndices hσ hσ₀ hA with h | h <;> rw [freeCoeffSet, h]

open Classical in
lemma natCard_pi_freeCoeffSet (h₀ : 0 ∈ ℛ) :
    Nat.card ((σ : I.genericIndices) → I.freeCoeffSet q ℛ σ) =
      (ℛ.ncard - 1) ^ ((if I.IsCritical q 0 then 1 else 0) + #I.aIndices) *
        ℛ.ncard ^ (#I.bIndices + #I.cIndices) := by
  have hB : (I.genericIndices.erase 0).filter (fun σ ↦ ¬I.pointType σ = .A) =
      I.genericIndices.filter (fun σ ↦ I.pointType σ = .B ∨ I.pointType σ = .C) := by
    ext σ
    simp only [mem_filter, mem_erase]
    refine ⟨fun ⟨⟨h₀, hσ⟩, hA⟩ ↦ ⟨hσ, I.pointType_of_mem_genericIndices hσ h₀ hA⟩,
      fun ⟨hσ, h⟩ ↦ ⟨⟨fun h₀ ↦ ?_, hσ⟩, ?_⟩⟩
    · rcases h with h | h <;> rw [h₀, pointType_zero] at h <;> cases h
    · rcases h with h | h <;> rw [h] <;> exact nofun
  have hA : (I.genericIndices.erase 0).filter (fun σ ↦ I.pointType σ = .A) = I.aIndices := by
    ext σ
    simp only [aIndices, mem_filter, mem_erase]
    refine ⟨fun ⟨⟨_, hσ⟩, h⟩ ↦ ⟨hσ, h⟩, fun ⟨hσ, h⟩ ↦ ⟨⟨fun h₀ ↦ ?_, hσ⟩, h⟩⟩
    rw [h₀, pointType_zero] at h
    cases h
  rw [Nat.card_pi, prod_coe_sort I.genericIndices fun σ ↦ Nat.card (I.freeCoeffSet q ℛ σ),
    prod_congr rfl fun σ hσ ↦ I.natCard_freeCoeffSet q ℛ h₀ hσ,
    ← mul_prod_erase _ _ I.zero_mem_genericIndices, ite_eq_left rfl,
    prod_congr rfl fun σ hσ ↦ ite_eq_right (ne_of_mem_erase hσ),
    ← prod_filter_mul_prod_filter_not _ fun σ ↦ I.pointType σ = .A,
    prod_congr rfl fun σ hσ ↦ ite_eq_left (mem_filter.mp hσ).2,
    prod_congr rfl fun σ hσ ↦ ite_eq_right (mem_filter.mp hσ).2, prod_const, prod_const, hA, hB,
    filter_or,
    card_union_of_disjoint (disjoint_filter.mpr fun _ _ h h' ↦ by rw [h] at h'; cases h'),
    pow_add, pow_add, bIndices, cIndices]
  split_ifs <;> ring1

lemma MongeChoice.ncard_reps {𝔪 : Ideal R} (C : I.MongeChoice 𝔪) :
    C.reps.ncard = Nat.card (R ⧸ 𝔪) := by
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_congr <| Equiv.ofBijective (fun r ↦ algebraMap R (R ⧸ 𝔪) r) ⟨fun r r' h ↦
    Subtype.ext <| (C.existsUnique_mem_reps _).unique ⟨r.2, h⟩ ⟨r'.2, rfl⟩, fun x ↦ ?_⟩
  rcases C.existsUnique_mem_reps x with ⟨r, ⟨hr, hx⟩, -⟩
  exact ⟨⟨r, hr⟩, hx⟩

variable [NeZero p] [IsDomain R] [IsDiscreteValuationRing R] {π : R}

lemma eq_of_specialisation_eq (hπ : Irreducible π) {S : ℕ → Set R}
    (hS : ∀ σ, (S σ).InjOn (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R))) {f g : ℕ → R}
    (hf : ∀ σ ∈ I.genericIndices, f σ ∈ S σ) (hg : ∀ σ ∈ I.genericIndices, g σ ∈ S σ)
    (h : I.specialisation π f = I.specialisation π g) {σ : ℕ} (hσ : σ ∈ I.genericIndices) :
    f σ = g σ := by
  induction σ using Nat.strong_induction_on with
  | _ σ ih =>
  have hn : σ % I.ramificationIndex < I.ramificationIndex :=
    Nat.mod_lt σ I.ramificationIndex_pos
  have hc : ∑ τ ∈ I.genericIndices, (if σ % I.ramificationIndex = τ % I.ramificationIndex then
      (f τ - g τ) * π ^ (τ / I.ramificationIndex) else 0) = 0 := by
    have h' : (I.specialisation π f).coeff (σ % I.ramificationIndex) =
        (I.specialisation π g).coeff (σ % I.ramificationIndex) :=
      congrArg (fun P : R[X] ↦ P.coeff (σ % I.ramificationIndex)) h
    rw [coeff_specialisation_of_lt π f hn, coeff_specialisation_of_lt π g hn] at h'
    have h'' : ∑ τ ∈ I.genericIndices, ((if σ % I.ramificationIndex = τ % I.ramificationIndex then
        f τ * π ^ (τ / I.ramificationIndex) else 0) -
          if σ % I.ramificationIndex = τ % I.ramificationIndex then
            g τ * π ^ (τ / I.ramificationIndex) else 0) = 0 := by
      rw [sum_sub_distrib, sub_eq_zero]
      exact mul_left_cancel₀ hπ.ne_zero h'
    refine Eq.trans (sum_congr rfl fun τ _ ↦ ?_) h''
    split_ifs <;> ring1
  rw [← add_sum_erase _ _ hσ, ite_eq_left rfl] at hc
  have hdvd : π ^ (σ / I.ramificationIndex + 1) ∣ (f σ - g σ) * π ^ (σ / I.ramificationIndex) := by
    rw [eq_neg_of_add_eq_zero_left hc, dvd_neg]
    refine dvd_sum fun τ hτ ↦ ?_
    split_ifs with hτσ
    · rcases (ne_of_mem_erase hτ).lt_or_gt with hlt | hlt
      · rw [ih τ hlt (mem_of_mem_erase hτ), sub_self, zero_mul]
        exact dvd_zero _
      · refine (pow_dvd_pow π ?_).mul_left _
        have h₁ : I.ramificationIndex * (σ / I.ramificationIndex) + σ % I.ramificationIndex = σ :=
          Nat.div_add_mod σ I.ramificationIndex
        have h₂ : I.ramificationIndex * (τ / I.ramificationIndex) + τ % I.ramificationIndex = τ :=
          Nat.div_add_mod τ I.ramificationIndex
        by_contra hj
        have h₃ : τ / I.ramificationIndex ≤ σ / I.ramificationIndex :=
          by omega
        have h₄ : I.ramificationIndex * (τ / I.ramificationIndex) ≤
            I.ramificationIndex * (σ / I.ramificationIndex) :=
          Nat.mul_le_mul_left _ h₃
        omega
    · exact dvd_zero _
  rw [pow_succ, mul_comm (π ^ _), mul_dvd_mul_iff_right (pow_ne_zero _ hπ.ne_zero)] at hdvd
  refine hS σ (hf σ hσ) (hg σ hσ) ?_
  rw [Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq, hπ.maximalIdeal_eq]
  exact Ideal.mem_span_singleton.mpr hdvd

open Classical in
lemma ncard_specialisations (hπ : Irreducible π) (h₀ : 0 ∈ ℛ)
    (hℛ : ℛ.InjOn (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R))) : {g : R[X] | ∃ f : ℕ → R,
      (∀ σ ∈ I.genericIndices, f σ ∈ I.freeCoeffSet q ℛ σ) ∧ I.specialisation π f = g}.ncard =
    (ℛ.ncard - 1) ^ ((if I.IsCritical q 0 then 1 else 0) + #I.aIndices) *
      ℛ.ncard ^ (#I.bIndices + #I.cIndices) := by
  have hS (σ : ℕ) :
      (I.freeCoeffSet q ℛ σ).InjOn (algebraMap R (R ⧸ IsLocalRing.maximalIdeal R)) := by
    rw [freeCoeffSet]
    split
    · split_ifs
      · exact hℛ.mono Set.sdiff_subset
      · exact Set.injOn_singleton _ _
    · exact hℛ.mono Set.sdiff_subset
    · exact hℛ
    · exact hℛ
    · exact Set.injOn_singleton _ _
  let E : ((σ : I.genericIndices) → I.freeCoeffSet q ℛ σ) → ℕ → R :=
    fun t σ ↦ if h : σ ∈ I.genericIndices then (t ⟨σ, h⟩ : R) else 0
  have hE (t : (σ : I.genericIndices) → I.freeCoeffSet q ℛ σ) {σ : ℕ}
      (hσ : σ ∈ I.genericIndices) : E t σ = t ⟨σ, hσ⟩ :=
    dite_eq_left hσ
  have hmem (t : (σ : I.genericIndices) → I.freeCoeffSet q ℛ σ) :
      ∀ σ ∈ I.genericIndices, E t σ ∈ I.freeCoeffSet q ℛ σ := fun σ hσ ↦
    (hE t hσ).symm ▸ (t ⟨σ, hσ⟩).2
  rw [← I.natCard_pi_freeCoeffSet q ℛ h₀, ← Nat.card_coe_set_eq]
  refine (Nat.card_congr <| Equiv.ofBijective (fun t ↦ ⟨I.specialisation π (E t), E t, hmem t, rfl⟩)
    ⟨fun t t' h ↦ ?_, ?_⟩).symm
  · funext σ
    exact Subtype.ext <| (hE t σ.2).symm.trans <| (I.eq_of_specialisation_eq hπ hS (hmem t)
      (hmem t') (congrArg Subtype.val h) σ.2).trans (hE t' σ.2)
  · rintro ⟨-, f, hf, rfl⟩
    exact ⟨fun σ ↦ ⟨f σ, hf σ σ.2⟩, Subtype.ext <| specialisation_congr π fun σ hσ ↦
      hE (fun σ ↦ ⟨f σ, hf σ σ.2⟩) hσ⟩

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

open Classical in
/-- **The number of specialisations of the generic polynomial** (LMFDB `lf.eisenstein_diagram`): for
a nonarchimedean local field `K` whose residue field has `q` elements, the unramified extension
`K_f` of `K` of degree `f` inside `K̄`, a uniformiser `ϖ` of `K_f` and Monge's representatives `ℛ`
of the residue field of `K_f`, there are `(q ^ f - 1) ^ (δ + α) q ^ (f β + f γ)` specialisations
of the generic polynomial `x ^ e + ϖ ∑_σ f_σ ϖ ^ j x ^ i` when the additional constraints on `c_σ`
and `d_0` are ignored (`freeCoeffSet`), `δ ∈ {0, 1}` being the number of critical `D`-points and
`α`, `β`, `γ` the numbers of `A`-points, `B`-points and critical `C`-points. Distinct choices of the
coefficients give distinct polynomials, `ϖ`-adic digits in `ℛ` being unique. -/
lemma ncard_specialisations_unramifiedExtension :
    letI : ValuativeRel (unramifiedExtension K (AlgebraicClosure K) I.f) :=
      finiteIntermediateFieldValuativeRel K (AlgebraicClosure K) _
    ∀ ϖ : 𝒪[unramifiedExtension K (AlgebraicClosure K) I.f], Irreducible ϖ →
      ∀ C : I.MongeChoice 𝓂[unramifiedExtension K (AlgebraicClosure K) I.f],
        {g | ∃ f : ℕ → 𝒪[unramifiedExtension K (AlgebraicClosure K) I.f],
          (∀ σ ∈ I.genericIndices, f σ ∈ I.freeCoeffSet (Nat.card 𝓀[K]) C.reps σ) ∧
            I.specialisation ϖ f = g}.ncard =
        (Nat.card 𝓀[K] ^ I.f - 1) ^ ((if I.IsCritical (Nat.card 𝓀[K]) 0 then 1 else 0) +
          #I.aIndices) * (Nat.card 𝓀[K] ^ I.f) ^ (#I.bIndices + #I.cIndices) := by
  let vF : ValuativeRel (unramifiedExtension K (AlgebraicClosure K) I.f) :=
    finiteIntermediateFieldValuativeRel K _ _
  let tF : TopologicalSpace (unramifiedExtension K (AlgebraicClosure K) I.f) :=
    finiteIntermediateFieldTopology K _ _
  have hF : IsNonarchimedeanLocalField (unramifiedExtension K (AlgebraicClosure K) I.f) :=
    finiteIntermediateField_isNonarchimedeanLocalField K _ _
  intro ϖ hϖ C
  have hKF : ValuativeExtension K (unramifiedExtension K (AlgebraicClosure K) I.f) :=
    finiteIntermediateField_valuativeExtension K _ _
  have hur : IsUnramified K (unramifiedExtension K (AlgebraicClosure K) I.f) :=
    isUnramified_unramifiedExtension I.f_pos.ne'
  have hq : C.reps.ncard = Nat.card 𝓀[K] ^ I.f := by
    refine (C.ncard_reps.trans (natCard_residueField K
      (unramifiedExtension K (AlgebraicClosure K) I.f))).trans ?_
    rw [IsUnramified.inertiaDegree_eq_finrank, finrank_unramifiedExtension I.f_pos.ne']
  rw [I.ncard_specialisations _ C.reps hϖ C.zero_mem_reps C.injOn_reps, hq]

end IsNonarchimedeanLocalField.HerbrandInvariant
