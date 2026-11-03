import Mathlib.Data.ZMod.Units
import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.GL2CanonicalLabel

/-!
# Existence of Sutherland's labels of subgroups of `GL₂(𝔽_p)`

A subgroup of `GL₂(𝔽_p)` of class `G`, `B`, `Cs`, `Cn`, `Ns`, `Nn` has a Sutherland label
(arXiv:1504.07618v7, §6.4). The groups named by the labels are described by the generators of
`LeanBridge.ForMathlib.GroupTheory.SpecificGroups.GL2LabelGenerators` and, for `Nn`, by Lemma 3.13
and Corollary 3.17 of the paper
(`LeanBridge.ForMathlib.GroupTheory.SpecificGroups.GL2NonsplitNormalizer`). For `Ns` this also needs
the conjugate that Sutherland's script chooses (`IsNsNormalForm`), obtained by conjugating with a
diagonal matrix, which does not change the diagonal part. For `Cn` and `Nn` it needs a generator of
the cyclic part satisfying the condition of his script (`IsScriptCartanGen`).

## Main results

* `Matrix.GeneralLinearGroup.exists_isSutherlandLabel_of_cls_G`,
  `Matrix.GeneralLinearGroup.exists_isSutherlandLabel_of_cls_B`,
  `Matrix.GeneralLinearGroup.exists_isSutherlandLabel_of_cls_Cs`: subgroups of these classes have a
  Sutherland label.
* `Matrix.GeneralLinearGroup.IsConwayGen.trace_pow_eq`: the condition of Sutherland's script does
  not depend on the root of the Conway polynomial.
* `Matrix.GeneralLinearGroup.exists_zpowers_eq_isScriptCartanGen`: a subgroup of `C_ns` has a
  generator satisfying the condition of Sutherland's script.
* `Matrix.GeneralLinearGroup.exists_isCanonicalSutherlandLabel_of_cls_Cn`,
  `Matrix.GeneralLinearGroup.exists_isCanonicalSutherlandLabel_of_cls_Nn`: subgroups of classes `Cn`
  and `Nn` have a canonical Sutherland label.
* `Matrix.GeneralLinearGroup.exists_map_conj_isNsNormalForm`: a subgroup of `Ns` not in `Cs` is
  conjugate by a diagonal matrix to one in the form that Sutherland's script chooses.
* `Matrix.GeneralLinearGroup.exists_isCanonicalSutherlandLabel_of_cls_Ns`: subgroups of class `Ns`
  have a canonical Sutherland label.
-/

open Matrix MulAction TauCeti

open scoped MatrixGroups Pointwise

namespace Matrix.GeneralLinearGroup

variable {p : ℕ} [Fact p.Prime] {H K K' : Subgroup (GL (Fin 2) (ZMod p))}
  {w x : GL (Fin 2) (ZMod p)} {G : Type*} [Group G] {a b c : G} {j k : ℕ}

lemma mem_subgroupConjClass_trans (h : K' ∈ subgroupConjClass p K)
    (hK : K ∈ subgroupConjClass p H) : K' ∈ subgroupConjClass p H := by
  rw [subgroupConjClass, ← orbit_eq_iff.mpr hK]
  exact h

lemma map_det_eq_of_mem_subgroupConjClass (hK : K ∈ subgroupConjClass p H) :
    K.map det = H.map det := by
  rcases hK with ⟨g, rfl⟩
  exact map_det_smul g

lemma inf_center_eq_of_mem_subgroupConjClass (hK : K ∈ subgroupConjClass p H) :
    K ⊓ Subgroup.center _ = H ⊓ Subgroup.center _ := by
  rcases hK with ⟨g, rfl⟩
  exact smul_inf_center g

lemma exists_isLexLeastTriple {P : ℕ → ℕ → ℕ → Prop} (h : ∃ a b c, P a b c) :
    ∃ a b c, IsLexLeastTriple a b c P := by
  rcases h with ⟨a₀, b₀, c₀, h₀⟩
  let s : Set (ℕ ×ₗ (ℕ ×ₗ ℕ)) := {x | P (ofLex x).1 (ofLex (ofLex x).2).1 (ofLex (ofLex x).2).2}
  have hs : s.Nonempty := ⟨toLex (a₀, toLex (b₀, c₀)), h₀⟩
  exact ⟨(ofLex (wellFounded_lt.min s hs)).1, (ofLex (ofLex (wellFounded_lt.min s hs)).2).1,
    (ofLex (ofLex (wellFounded_lt.min s hs)).2).2, wellFounded_lt.min_mem s hs, fun a' b' c' h' ↦
      not_lt.mp (wellFounded_lt.not_lt_min s (x := toLex (a', toLex (b', c'))) h')⟩

lemma forall_mem_namedSubgroup {L : SutherlandGroupLabel} (hL : L.namedSubgroup p = some K)
    (hK : K ∈ subgroupConjClass p H) : ∀ N ∈ L.namedSubgroup p, N ∈ subgroupConjClass p H := by
  intro N hN
  rw [Option.mem_def, hL, Option.some_inj] at hN
  exact hN ▸ hK

lemma det_ker_le_of_holds_G (hH : SutherlandClass.Holds p H .G) : det.ker ≤ H := by
  rcases hH with ⟨K, ⟨g, rfl⟩, hK⟩
  rwa [← det.normal_ker.conjAct g, Subgroup.pointwise_smul_le_pointwise_smul_iff] at hK

/-- **A subgroup of class `G` has a Sutherland label.** -/
lemma exists_isSutherlandLabel_of_cls_G (hS : HasSutherlandClass p H .G) :
    ∃ L : SutherlandGroupLabel, L.cls = .G ∧ IsSutherlandLabel p H L :=
  ⟨_, rfl, isSutherlandLabel_G (det_ker_le_of_holds_G hS.1)⟩

/-- **A subgroup of class `B` has a Sutherland label** `ℓB[d]` or `ℓB.a.b[d]`. -/
lemma exists_isSutherlandLabel_of_cls_B (hS : HasSutherlandClass p H .B) :
    ∃ L : SutherlandGroupLabel, L.cls = .B ∧ IsSutherlandLabel p H L := by
  by_cases hfull : labelBD p (H.map det).index ∈ subgroupConjClass p H
  · exact ⟨⟨.B, [], _⟩, rfl, hS, rfl, forall_mem_namedSubgroup rfl hfull, trivial⟩
  have hH : SutherlandClass.Holds p H .B := hS.1
  rcases hH with ⟨K, hK, hKB, x, hxK, hx⟩
  rcases exists_upperRightHom_conj_of_le_borel hKB hxK hx with ⟨K', hK', hK'B, ht⟩
  have hK'H : K' ∈ subgroupConjClass p H := mem_subgroupConjClass_trans hK' hK
  rcases exists_eq_labelBABD hK'B ht with ⟨a, b, ha, hb, hgen, hKeq⟩
  rw [map_det_eq_of_mem_subgroupConjClass hK'H] at hKeq
  rcases exists_isLexLeastPair (P := fun a b ↦ 0 < a ∧ 0 < b ∧
    IsDetOneDiagGen p a (labelBABD p (H.map det).index a b) ∧
      labelBABD p (H.map det).index a b ∈ subgroupConjClass p H)
    ⟨a, b, ha, hb, hKeq ▸ hgen, hKeq ▸ hK'H⟩ with ⟨a', b', hab⟩
  exact ⟨⟨.B, [a', b'], _⟩, rfl, hS, rfl, forall_mem_namedSubgroup rfl hab.1.2.2.2, hfull, hab⟩

/-- **A subgroup of class `Cs` has a Sutherland label** `ℓCs[d]` or `ℓCs.a.b[d]`. -/
lemma exists_isSutherlandLabel_of_cls_Cs (hS : HasSutherlandClass p H .Cs) :
    ∃ L : SutherlandGroupLabel, L.cls = .Cs ∧ IsSutherlandLabel p H L := by
  by_cases hfull : labelCsD p (H.map det).index ∈ subgroupConjClass p H
  · exact ⟨⟨.Cs, [], _⟩, rfl, hS, rfl, forall_mem_namedSubgroup rfl hfull, trivial⟩
  have hH : SutherlandClass.Holds p H .Cs := hS.1
  rcases hH with ⟨K, hK, hKC⟩
  rcases exists_eq_labelCsABD hKC with ⟨a, b, ha, hb, hgen, hKeq⟩
  rw [map_det_eq_of_mem_subgroupConjClass hK] at hKeq
  rcases exists_isLexLeastPair (P := fun a b ↦ 0 < a ∧ 0 < b ∧
    IsDetOneDiagGen p a (labelCsABD p (H.map det).index a b) ∧
      labelCsABD p (H.map det).index a b ∈ subgroupConjClass p H)
    ⟨a, b, ha, hb, hKeq ▸ hgen, hKeq ▸ hK⟩ with ⟨a', b', hab⟩
  exact ⟨⟨.Cs, [a', b'], _⟩, rfl, hS, rfl, forall_mem_namedSubgroup rfl hab.1.2.2.2, hfull, hab⟩

lemma exists_coprime_modEq {m n : ℕ} (hm : m ≠ 0) (hn : n ∣ m) (hk : k.Coprime n) :
    ∃ j : ℕ, j.Coprime m ∧ j ≡ k [MOD n] := by
  have : NeZero m := ⟨hm⟩
  rcases ZMod.unitsMap_surjective hn (ZMod.unitOfCoprime k hk) with ⟨u, hu⟩
  refine ⟨(u : ZMod m).val, ZMod.val_coe_unit_coprime u, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_val]
  have h : ((ZMod.unitsMap hn u : (ZMod n)ˣ) : ZMod n) = k := congrArg Units.val hu
  rwa [ZMod.unitsMap_val] at h

lemma zpowers_pow_eq_of_coprime (h : j.Coprime (orderOf a)) :
    Subgroup.zpowers (a ^ j) = Subgroup.zpowers a := by
  simpa using (Subgroup.zpowers_eq_zpowers_iff' a (j : ℤ) 1).mpr (by simpa using h)

variable [Finite G] in
lemma zpowers_eq_of_orderOf_eq (ha : a ∈ Subgroup.zpowers c) (hb : b ∈ Subgroup.zpowers c)
    (h : orderOf a = orderOf b) : Subgroup.zpowers a = Subgroup.zpowers b := by
  rcases Subgroup.mem_zpowers_iff.mp ha with ⟨i, rfl⟩
  rcases Subgroup.mem_zpowers_iff.mp hb with ⟨j, rfl⟩
  rw [orderOf_zpow, orderOf_zpow] at h
  have h₁ : Nat.gcd (orderOf c) i.natAbs = Nat.gcd (orderOf c) j.natAbs := by
    rw [← Nat.div_div_self (Nat.gcd_dvd_left _ _) (orderOf_pos c).ne', h,
      Nat.div_div_self (Nat.gcd_dvd_left _ _) (orderOf_pos c).ne']
  rw [Subgroup.zpowers_eq_zpowers_iff']
  simpa [Int.gcd, Nat.gcd_comm] using h₁

variable [Finite G] in
lemma coprime_of_orderOf_pow_eq (h : orderOf (a ^ k) = orderOf a) : k.Coprime (orderOf a) := by
  rw [orderOf_pow] at h
  exact Nat.coprime_comm.mp ((Nat.div_eq_self.mp h).resolve_left (orderOf_pos a).ne')

lemma orderOf_eq_of_zpowers_eq {δ : GL (Fin 2) (ZMod p)} (hδ : Subgroup.zpowers δ = labelCn p) :
    orderOf δ = p ^ 2 - 1 := by
  rw [← Nat.card_zpowers, hδ, natCard_labelCn]

lemma ne_zero_sq_sub_one : p ^ 2 - 1 ≠ 0 :=
  Nat.sub_ne_zero_of_lt (Nat.one_lt_pow two_ne_zero (Fact.out : p.Prime).one_lt)

lemma exists_isConwayGen : ∃ δ : GL (Fin 2) (ZMod p), IsConwayGen p δ := by
  have hS : {δ : GL (Fin 2) (ZMod p) | Subgroup.zpowers δ = labelCn p ∧
      (det δ : ZMod p) = ZMod.leastPrimitiveRoot p}.Nonempty := by
    have hδ₀ : Subgroup.zpowers (nonsplitCartanGen p) = labelCn p := zpowers_nonsplitCartanGen p
    have hgen : ∀ u : (ZMod p)ˣ, u ∈ Subgroup.zpowers (det (nonsplitCartanGen p)) :=
      mem_zpowers_det_of_zpowers_eq hδ₀
    have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime Fact.out]
    have hr : orderOf (det (nonsplitCartanGen p)) = p - 1 :=
      (orderOf_eq_card_of_forall_mem_zpowers hgen).trans hcard
    rcases (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (hgen (Units.mk0 _
      (ZMod.leastPrimitiveRoot_ne_zero p)))) with ⟨k, hk⟩
    have hk₁ : k.Coprime (p - 1) := hr ▸ coprime_of_orderOf_pow_eq <| by
      rw [hk, ← orderOf_units, Units.val_mk0, ZMod.orderOf_leastPrimitiveRoot]
    rcases exists_coprime_modEq (ne_zero_sq_sub_one (p := p))
      (by simpa using Nat.sub_dvd_pow_sub_pow p 1 2 : p - 1 ∣ p ^ 2 - 1) hk₁ with ⟨j, hj, hjk⟩
    refine ⟨nonsplitCartanGen p ^ j, ?_, ?_⟩
    · rw [zpowers_pow_eq_of_coprime (by rwa [orderOf_eq_of_zpowers_eq hδ₀]), hδ₀]
    · have h₁ : det (nonsplitCartanGen p) ^ j = det (nonsplitCartanGen p) ^ k :=
        pow_eq_pow_iff_modEq.mpr (hr ▸ hjk)
      rw [map_pow, h₁, hk, Units.val_mk0]
  rcases Set.exists_min_image _ (fun δ : GL (Fin 2) (ZMod p) ↦ δ.val.trace.val) (Set.toFinite _) hS
    with ⟨δ, hδ, hmin⟩
  exact ⟨δ, hδ.1, hδ.2, fun δ' h₁ h₂ ↦ hmin δ' ⟨h₁, h₂⟩⟩

variable (p) in
lemma isConwayGen_conwayGen : IsConwayGen p (conwayGen p) :=
  Classical.epsilon_spec exists_isConwayGen

/-- **The traces of the powers of a root of the Conway polynomial do not depend on the root**, as
the two roots have the same trace and determinant. So the condition `IsScriptCartanGen` does not
depend on the choice of `conwayGen`. -/
lemma IsConwayGen.trace_pow_eq {δ δ' : GL (Fin 2) (ZMod p)} (hδ : IsConwayGen p δ)
    (hδ' : IsConwayGen p δ') (n : ℕ) : (δ ^ n).val.trace = (δ' ^ n).val.trace := by
  have htr : δ.val.trace = δ'.val.trace :=
    ZMod.val_injective p <| le_antisymm (hδ.2.2 δ' hδ'.1 hδ'.2.1) (hδ'.2.2 δ hδ.1 hδ.2.1)
  have hdet : δ.val.det = δ'.val.det := by
    rw [← val_det_apply, ← val_det_apply, hδ.2.1, hδ'.2.1]
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simpa using htr
  | more n h₀ h₁ =>
    simp only [Units.val_pow_eq_pow_val] at h₀ h₁ ⊢
    rw [trace_pow_add_two_fin_two, trace_pow_add_two_fin_two, h₀, h₁, htr, hdet]

lemma trace_sq_eq_of_mem_labelCn (hp : p ≠ 2) (hx : x ∈ labelCn p) :
    x.val.trace ^ 2 = (2 + (gammaGL p * x * gammaGL p * x⁻¹).val.trace) * x.val.det := by
  have hD : x.val.det ≠ 0 := (isUnits_det_units x).ne_zero
  rcases (mem_labelCn_iff p hp).mp hx with ⟨h₁₁, -⟩
  rw [Units.val_mul _ x⁻¹, gamma_conj_val, Matrix.coe_units_inv, inv_apply_of_field,
    Matrix.mul_smul, trace_smul, smul_eq_mul, add_mul, mul_right_comm, inv_mul_cancel₀ hD, one_mul]
  simp [Matrix.trace_fin_two, Matrix.det_fin_two, h₁₁]
  ring1

lemma gamma_conj_mul_inv_eq_one_iff (hp : p ≠ 2) (hx : x ∈ labelCn p) :
    gammaGL p * x * gammaGL p * x⁻¹ = 1 ↔ x ∈ Subgroup.center (GL (Fin 2) (ZMod p)) := by
  rcases (mem_labelCn_iff p hp).mp hx with ⟨h₁₁, h₀₁⟩
  constructor
  · intro h
    have h₁ : gammaGL p * x * gammaGL p = x := mul_inv_eq_one.mp h
    have h₂ : -x 1 0 = x 1 0 := by
      have h₃ : (gammaGL p * x * gammaGL p).val 1 0 = x 1 0 := by
        rw [h₁]
      rw [gamma_conj_val] at h₃
      simpa using h₃
    have h₃ : x 1 0 = 0 := by
      have h₄ : (2 : ZMod p) * x 1 0 = 0 := by
        linear_combination -h₂
      exact (mul_eq_zero.mp h₄).resolve_left (two_ne_zero_of_ne_two p hp)
    exact mem_center_iff_entries.mpr ⟨by rw [h₀₁, h₃, mul_zero], h₃, h₁₁.symm⟩
  · intro h
    rw [Subgroup.mem_center_iff.mp h (gammaGL p), mul_assoc x, gammaGL_mul_self, mul_one,
      mul_inv_cancel]

lemma gamma_conj_mul_inv_pow (hp : p ≠ 2) (hx : x ∈ labelCn p) (n : ℕ) :
    (gammaGL p * x * gammaGL p * x⁻¹) ^ n = gammaGL p * x ^ n * gammaGL p * (x ^ n)⁻¹ := by
  have hγ : (gammaGL p)⁻¹ = gammaGL p := inv_eq_of_mul_eq_one_right (gammaGL_mul_self p)
  have hcomm : Commute (gammaGL p * x * gammaGL p) x⁻¹ :=
    mul_comm_of_mem_labelCn (gamma_conj_mem_labelCn hp hx) (inv_mem hx)
  have hconj : (gammaGL p * x * gammaGL p) ^ n = gammaGL p * x ^ n * gammaGL p := by
    simpa only [hγ] using conj_pow (a := gammaGL p) (b := x) (i := n)
  rw [hcomm.mul_pow, hconj, inv_pow]

/-- **A subgroup of `C_ns` has a generator satisfying the condition of Sutherland's script**
(`IsScriptCartanGen`), for odd `p`: for a generator `c₀`, the element `ξ = γ c₀ γ / c₀` has the
order `n` of `c₀` in `PGL₂(𝔽_p)`, so the root of unity `ζ = δ ^ ((p ^ 2 - 1) / n)`, of order `n` in
the cyclic group `C_ns`, is a power `ξ ^ i` of it, with `i` prime to `n`; and `c₀ ^ j` is another
generator, for `j` prime to the order of `c₀` with `j ≡ i` modulo `n`. -/
lemma exists_zpowers_eq_isScriptCartanGen (hp : p ≠ 2) (hK : K ≤ labelCn p) :
    ∃ c, Subgroup.zpowers c = K ∧ IsScriptCartanGen p c := by
  have : IsCyclic (labelCn p) := isCyclic_labelCn p
  have : IsCyclic K := Subgroup.isCyclic_of_le hK
  rcases K.isCyclic_iff_exists_zpowers_eq_top.mp inferInstance with ⟨c₀, hc₀⟩
  have hc₀C : c₀ ∈ labelCn p := hK (hc₀ ▸ Subgroup.mem_zpowers c₀)
  have hzC : gammaGL p * c₀ * gammaGL p * c₀⁻¹ ∈ labelCn p :=
    mul_mem (gamma_conj_mem_labelCn hp hc₀C) (inv_mem hc₀C)
  have hzord : orderOf (gammaGL p * c₀ * gammaGL p * c₀⁻¹) = orderOf (ProjGenLinGroup.mk c₀) :=
    orderOf_eq_orderOf_iff.mpr fun k ↦ by
      rw [gamma_conj_mul_inv_pow hp hc₀C, gamma_conj_mul_inv_eq_one_iff hp (pow_mem hc₀C k),
        ← map_pow, ProjGenLinGroup.mk_eq_one]
  have hδ : Subgroup.zpowers (conwayGen p) = labelCn p := (isConwayGen_conwayGen p).1
  have hN : orderOf (conwayGen p) = p ^ 2 - 1 := orderOf_eq_of_zpowers_eq hδ
  have hnN : orderOf (ProjGenLinGroup.mk c₀) ∣ p ^ 2 - 1 := by
    rw [← hzord, ← hN]
    exact orderOf_dvd_of_mem_zpowers (hδ ▸ hzC)
  have hndvd : orderOf (ProjGenLinGroup.mk c₀) ∣ orderOf c₀ := orderOf_map_dvd _ _
  have hc₀ord : orderOf c₀ ≠ 0 := orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite c₀)
  have hnpos : orderOf (ProjGenLinGroup.mk c₀) ≠ 0 := ne_zero_of_dvd_ne_zero hc₀ord hndvd
  have hdiv : (p ^ 2 - 1) / orderOf (ProjGenLinGroup.mk c₀) ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ne_zero_sq_sub_one) hnN)
      (Nat.pos_of_ne_zero hnpos)).ne'
  have hζord : orderOf (conwayGen p ^ ((p ^ 2 - 1) / orderOf (ProjGenLinGroup.mk c₀))) =
      orderOf (gammaGL p * c₀ * gammaGL p * c₀⁻¹) := by
    rw [orderOf_pow_of_dvd hdiv (by rw [hN]; exact Nat.div_dvd_of_dvd hnN), hN, hzord,
      Nat.div_div_self hnN ne_zero_sq_sub_one]
  have hζ : conwayGen p ^ ((p ^ 2 - 1) / orderOf (ProjGenLinGroup.mk c₀)) ∈
      Subgroup.zpowers (gammaGL p * c₀ * gammaGL p * c₀⁻¹) := by
    rw [← zpowers_eq_of_orderOf_eq (c := conwayGen p) (pow_mem (Subgroup.mem_zpowers _) _)
      (hδ ▸ hzC) hζord]
    exact Subgroup.mem_zpowers _
  rcases (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hζ) with ⟨i, hi⟩
  have hin : i.Coprime (orderOf (ProjGenLinGroup.mk c₀)) :=
    hzord ▸ coprime_of_orderOf_pow_eq (by rw [hi, hζord])
  rcases exists_coprime_modEq hc₀ord hndvd hin with ⟨j, hj, hji⟩
  have hjn : j.Coprime (orderOf (ProjGenLinGroup.mk c₀)) := hj.coprime_dvd_right hndvd
  refine ⟨c₀ ^ j, by rw [zpowers_pow_eq_of_coprime hj, hc₀], ?_⟩
  have hordj : orderOf (ProjGenLinGroup.mk (c₀ ^ j)) = orderOf (ProjGenLinGroup.mk c₀) := by
    rw [map_pow]
    exact hjn.symm.orderOf_pow
  rw [IsScriptCartanGen, hordj, ← hi, ← (pow_eq_pow_iff_modEq.mpr (hzord ▸ hji) :
    (gammaGL p * c₀ * gammaGL p * c₀⁻¹) ^ j = (gammaGL p * c₀ * gammaGL p * c₀⁻¹) ^ i),
    gamma_conj_mul_inv_pow hp hc₀C]
  exact trace_sq_eq_of_mem_labelCn hp (pow_mem hc₀C j)

lemma units_zmod_two_eq : ∀ u v : (ZMod 2)ˣ, u = v := by
  decide

/-- **A subgroup of class `Cn` has a Sutherland label** `ℓCn[d]` or `ℓCn.a.b[d]`. -/
lemma exists_isCanonicalSutherlandLabel_of_cls_Cn (hS : HasSutherlandClass p H .Cn) :
    ∃ L : SutherlandGroupLabel, L.cls = .Cn ∧ IsCanonicalSutherlandLabel p H L := by
  by_cases hfull : labelCnD p (H.map det).index ∈ subgroupConjClass p H
  · exact ⟨⟨.Cn, [], _⟩, rfl, hS, rfl, forall_mem_namedSubgroup rfl hfull, trivial⟩
  have hH : SutherlandClass.Holds p H .Cn := hS.1
  rcases hH with ⟨⟨K, hK, hKC⟩, hCs⟩
  rcases eq_or_ne p 2 with rfl | hp
  · rcases hK with ⟨g, rfl⟩
    have hcard : Nat.card ↥(g • H) ∣ 3 := by
      have h₁ : Nat.card ↥(g • H) ∣ Nat.card (labelCn 2) := Subgroup.card_dvd_of_le hKC
      rwa [natCard_labelCn] at h₁
    rcases (Nat.dvd_prime Nat.prime_three).mp hcard with h₁ | h₃
    · exact absurd ⟨g • H, mem_orbit _ g, by rw [Subgroup.card_eq_one.mp h₁]; exact bot_le⟩ hCs
    · have hle : g • H = labelCn 2 := Subgroup.eq_of_le_of_card_ge hKC <| by
        rw [natCard_labelCn, h₃]
        norm_num
      have hD : labelCnD 2 (H.map det).index = labelCn 2 :=
        inf_eq_left.mpr fun x _ ↦ ⟨1, units_zmod_two_eq _ _⟩
      exact absurd (hD ▸ hle ▸ mem_orbit H g) hfull
  rcases exists_zpowers_eq_isScriptCartanGen hp hKC with ⟨c, hcK, hc⟩
  have hcC : c ∈ labelCn p := hKC (hcK ▸ Subgroup.mem_zpowers c)
  have hy : c 1 0 ≠ 0 := fun hy ↦ hCs ⟨K, hK, by
    rw [← hcK, Subgroup.zpowers_le]
    exact mem_diagonalTorus_of_fin_two (ZMod p) (by rw [((mem_labelCn_iff p hp).mp hcC).2, hy,
      mul_zero]) hy⟩
  rcases exists_isLexLeastPair (P := fun a b ↦ 0 < b ∧ IsScriptCartanPair p a b ∧
      labelCnAB p a b ∈ subgroupConjClass p H)
    ⟨(c 0 0).val, (c 1 0).val, ZMod.val_pos.mpr hy, ⟨c, val_eq_of_mem_labelCn hp hcC, hc⟩, by
      rw [labelCnAB_val_eq_zpowers hp hcC, hcK]
      exact hK⟩ with ⟨a, b, hab⟩
  exact ⟨⟨.Cn, [a, b], _⟩, rfl, hS, rfl, forall_mem_namedSubgroup rfl hab.1.2.2, hfull, hab⟩

lemma exists_mem_inf_notMem_center_of_hasDihedralImage (hK : HasDihedralImage p K)
    {C : Subgroup (GL (Fin 2) (ZMod p))}
    (hC : ∀ k₁ ∈ K, ∀ k₂ ∈ K, k₁ ∉ C → k₂ ∉ C → k₁⁻¹ * k₂ ∈ C) :
    ∃ J ∈ K ⊓ C, J ∉ Subgroup.center (GL (Fin 2) (ZMod p)) := by
  by_contra hc
  push Not at hc
  rcases hK with ⟨n, hn, ⟨e⟩⟩
  have hlift (y : DihedralGroup n) (hy : y ≠ 1) :
      ∃ k ∈ K, k ∉ C ∧ ProjGenLinGroup.mk k = (e.symm y : PGL(Fin 2, ZMod p)) := by
    rcases (e.symm y).2 with ⟨k, hk, hky⟩
    refine ⟨k, hk, fun hkC ↦ hy ?_, hky⟩
    have h₁ : e.symm y = 1 := Subtype.ext <| hky.symm.trans <|
      ProjGenLinGroup.mk_eq_one.mpr (hc k (Subgroup.mem_inf.mpr ⟨hk, hkC⟩))
    exact e.symm.map_eq_one_iff.mp h₁
  rcases hlift _ (dihedralGroup_r_one_ne_one hn) with ⟨k₁, hk₁, hk₁C, hk₁y⟩
  rcases hlift (DihedralGroup.sr 0) (by rw [DihedralGroup.one_def]; exact nofun) with
    ⟨k₂, hk₂, hk₂C, hk₂y⟩
  have hcen : k₁⁻¹ * k₂ ∈ Subgroup.center (GL (Fin 2) (ZMod p)) :=
    hc _ (Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hk₁) hk₂, hC k₁ hk₁ k₂ hk₂ hk₁C hk₂C⟩)
  have heq : ProjGenLinGroup.mk k₁ = ProjGenLinGroup.mk k₂ := by
    have h₁ : ProjGenLinGroup.mk (k₁⁻¹ * k₂) = 1 := ProjGenLinGroup.mk_eq_one.mpr hcen
    rwa [map_mul, map_inv, inv_mul_eq_one] at h₁
  rw [hk₁y, hk₂y] at heq
  have h₂ : (DihedralGroup.r 1 : DihedralGroup n) = DihedralGroup.sr 0 :=
    e.symm.injective (Subtype.ext heq)
  simp at h₂

/-- **A subgroup of class `Nn` has a Sutherland label** `ℓNn[d]`, `ℓNn.a.b[d]` or `ℓNn.a.b.c[d]`,
for odd `p`, by Lemma 3.13 and Corollary 3.17 of Sutherland (arXiv:1504.07618v7). -/
lemma exists_isCanonicalSutherlandLabel_of_cls_Nn (hp : p ≠ 2) (hS : HasSutherlandClass p H .Nn) :
    ∃ L : SutherlandGroupLabel, L.cls = .Nn ∧ IsCanonicalSutherlandLabel p H L := by
  by_cases hfull : labelNnD p (H.map det).index ∈ subgroupConjClass p H
  · exact ⟨⟨.Nn, [], _⟩, rfl, hS, rfl, forall_mem_namedSubgroup rfl hfull, trivial⟩
  have hH : SutherlandClass.Holds p H .Nn := hS.1
  rcases hH with ⟨⟨K, hK, hKN, hdih⟩, hNs⟩
  have hne : ¬K ≤ labelCn p := fun hKC ↦ by
    by_cases hCs : ∃ K' ∈ subgroupConjClass p H, K' ≤ diagonalTorus (ZMod p) 2
    · exact hS.2 .Cs (by decide) hCs
    · exact hS.2 .Cn (by decide) ⟨⟨K, hK, hKC⟩, hCs⟩
  rcases exists_zpowers_eq_isScriptCartanGen hp (inf_le_right : K ⊓ labelCn p ≤ labelCn p) with
    ⟨c, hcz, hsc⟩
  have hcC : c ∈ labelCn p := (Subgroup.mem_inf.mp (hcz ▸ Subgroup.mem_zpowers c)).2
  have hscp : IsScriptCartanPair p (c 0 0).val (c 1 0).val := ⟨c, val_eq_of_mem_labelCn hp hcC, hsc⟩
  have hc' : c 1 1 = c 0 0 ∧ c 0 1 = (ZMod.leastPrimitiveRoot p : ZMod p) * c 1 0 :=
    (mem_labelCn_iff p hp).mp hcC
  have hb : c 1 0 ≠ 0 := by
    intro hb
    rcases exists_mem_inf_notMem_center_of_hasDihedralImage hdih (C := labelCn p)
      (fun k₁ hk₁ k₂ hk₂ h₁ h₂ ↦ by
        have hc₁ : gammaGL p * k₁ ∈ labelCn p :=
          ((mem_labelNn_iff hp).mp (hKN hk₁)).resolve_left h₁
        have hc₂ : gammaGL p * k₂ ∈ labelCn p :=
          ((mem_labelNn_iff hp).mp (hKN hk₂)).resolve_left h₂
        simpa using mul_mem (inv_mem hc₁) hc₂) with ⟨J, hJ, hJc⟩
    rw [← hcz] at hJ
    rcases Subgroup.mem_zpowers_iff.mp hJ with ⟨k, rfl⟩
    exact hJc (zpow_mem (mem_center_iff_entries.mpr
      ⟨by rw [hc'.2, hb, mul_zero], hb, hc'.1.symm⟩) k)
  by_cases hdisj : IsNnDetDisjoint p K
  · have hcen : Subgroup.center (GL (Fin 2) (ZMod p)) ≤ labelCn p := by
      rw [center_eq_range_scalar]
      rintro - ⟨u, rfl⟩
      exact scalar_mem_labelCn hp u
    have hZ : H ⊓ Subgroup.center _ ≤ labelCnAB p (c 0 0).val (c 1 0).val := by
      rw [labelCnAB_val_eq_zpowers hp hcC, hcz, ← inf_center_eq_of_mem_subgroupConjClass hK]
      exact inf_le_inf_left _ hcen
    rcases exists_isLexLeastPair (P := fun a b ↦ 0 < b ∧ IsScriptCartanPair p a b ∧
      H ⊓ Subgroup.center _ ≤ labelCnAB p a b ∧
        ∀ δ : GL (Fin 2) (ZMod p), Subgroup.zpowers δ = labelCn p → IsNnDetDisjoint p
          (labelNnABC p a b ((H ⊓ Subgroup.center _).relIndex (Subgroup.center _)) δ) ∧
          labelNnABC p a b ((H ⊓ Subgroup.center _).relIndex (Subgroup.center _)) δ ∈
            subgroupConjClass p H) ⟨_, _, ZMod.val_pos.mpr hb, hscp, hZ, fun δ hδ ↦ by
        rcases exists_labelNnABC_eq_map_conj hp hKN hcC hcz.symm hne hdisj hδ with ⟨w, hw, h⟩
        rw [inf_center_eq_of_mem_subgroupConjClass hK] at h
        rw [h]
        exact ⟨(isNnDetDisjoint_map_conj_iff (inv_mem hw)).mpr hdisj,
          mem_subgroupConjClass_trans (map_conj_mem_subgroupConjClass K _) hK⟩⟩ with ⟨a', b', hab⟩
    exact ⟨⟨.Nn, [a', b', _], _⟩, rfl, hS, rfl, forall_mem_namedSubgroup rfl
      (hab.1.2.2.2 _ (zpowers_nonsplitCartanGen p)).2, hfull, rfl, hab⟩
  · rw [IsNnDetDisjoint] at hdisj
    push Not at hdisj
    rcases hdisj with ⟨x, hxK, hxC, hxdet⟩
    rcases exists_isLexLeastPair (P := fun a b ↦ 0 < b ∧ IsScriptCartanPair p a b ∧
      labelNnAB p a b ∈ subgroupConjClass p H) ⟨_, _, ZMod.val_pos.mpr hb, hscp,
        mem_subgroupConjClass_trans (labelNnAB_mem_subgroupConjClass hp hKN hcC hcz.symm hxK hxC
          hxdet) hK⟩ with ⟨a', b', hab⟩
    exact ⟨⟨.Nn, [a', b'], _⟩, rfl, hS, rfl, forall_mem_namedSubgroup rfl hab.1.2.2, hfull, hab⟩

lemma mul_comm_of_mem_diagonalTorus {y : GL (Fin 2) (ZMod p)} (hx : x ∈ diagonalTorus (ZMod p) 2)
    (hy : y ∈ diagonalTorus (ZMod p) 2) : x * y = y * x := by
  rcases mem_diagonalTorus_iff_exists_diagGL.mp hx with ⟨s, rfl⟩
  rcases mem_diagonalTorus_iff_exists_diagGL.mp hy with ⟨t, rfl⟩
  rw [← map_mul, mul_comm, map_mul]

lemma map_conj_inf_diagonalTorus (hw : w ∈ diagonalTorus (ZMod p) 2) :
    K.map (MulAut.conj w).toMonoidHom ⊓ diagonalTorus (ZMod p) 2 = K ⊓ diagonalTorus (ZMod p) 2 :=
  map_conj_inf_eq fun _ hy ↦ mul_comm_of_mem_diagonalTorus hy hw

lemma isNsDetDisjoint_map_conj_iff (hw : w ∈ diagonalTorus (ZMod p) 2) :
    IsNsDetDisjoint p (K.map (MulAut.conj w).toMonoidHom) ↔ IsNsDetDisjoint p K :=
  forall_neg_det_notMem_map_conj_iff hw fun _ hy ↦ mul_comm_of_mem_diagonalTorus hy hw

lemma val_mulAut_conj_diagGL (h₀₀ : x 0 0 = 0) (h₁₁ : x 1 1 = 0) (h₁₀ : x 1 0 ≠ 0) :
    (MulAut.conj (diagGL ![Units.mk0 (x 1 0) h₁₀, 1]) x).val = !![0, x 0 1 * x 1 0; 1, 0] := by
  simp only [MulAut.conj_apply, Units.val_mul, ← map_inv, diagGL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h₀₀, h₁₁, h₁₀, -ZMod.inv_coe_unit]
  ring1

/-- **Every subgroup of `Ns` not in `Cs` has a conjugate by a diagonal matrix in the normal form of
Sutherland's script** (`IsNsNormalForm`; Lemma 3.13 of arXiv:1504.07618v7). -/
lemma exists_map_conj_isNsNormalForm (hK : K ≤ labelNs p) (hne : ¬K ≤ diagonalTorus (ZMod p) 2) :
    ∃ t ∈ diagonalTorus (ZMod p) 2, IsNsNormalForm p (K.map (MulAut.conj t).toMonoidHom) := by
  have hdetv {y : GL (Fin 2) (ZMod p)} (h : y 0 0 = 0) : ((-det y : (ZMod p)ˣ) : ZMod p) =
      y 0 1 * y 1 0 := by
    rw [Units.val_neg, val_det_apply, Matrix.det_fin_two, h, zero_mul, zero_sub, neg_neg]
  have ht {u : (ZMod p)ˣ} : (diagGL ![u, 1] : GL (Fin 2) (ZMod p)) ∈ diagonalTorus (ZMod p) 2 :=
    mem_diagonalTorus_iff_exists_diagGL.mpr ⟨_, rfl⟩
  by_cases hdisj : IsNsDetDisjoint p K
  · rcases Set.not_subset.mp hne with ⟨x, hxK, hxd⟩
    have hxx : x * x = scalar (Fin 2) (-det x) :=
      mul_self_eq_scalar_of_trace_eq_zero (trace_eq_zero_of_mem_labelNs (hK hxK) hxd)
    have hgen (u : (ZMod p)ˣ) : u ∈ Subgroup.zpowers
        (Units.mk0 (ZMod.leastPrimitiveRoot p : ZMod p) (ZMod.leastPrimitiveRoot_ne_zero p)) := by
      have hord : orderOf (Units.mk0 (ZMod.leastPrimitiveRoot p : ZMod p)
          (ZMod.leastPrimitiveRoot_ne_zero p)) = Nat.card (ZMod p)ˣ := by
        rw [← orderOf_units, Units.val_mk0, ZMod.orderOf_leastPrimitiveRoot,
          Nat.card_eq_fintype_card, ZMod.card_units]
      rw [Subgroup.eq_top_of_card_eq (Subgroup.zpowers (Units.mk0 _ _))
        (by rw [Nat.card_zpowers, hord])]
      exact Subgroup.mem_top u
    rcases exists_mul_sq_eq_pow_relIndex hgen (hxx ▸ mul_mem hxK hxK : scalar (Fin 2) (-det x) ∈ K)
      (fun u hu hut ↦ hdisj x hxK hxd ⟨scalar (Fin 2) u, Subgroup.mem_inf.mpr
        ⟨hu, scalar_mem_diagonalTorus u⟩, by rw [det_scalar, Fintype.card_fin, hut]⟩) with
      ⟨s, hs, hts⟩
    have hx'K : x * scalar (Fin 2) s ∈ K := mul_mem hxK hs
    have hx'd : x * scalar (Fin 2) s ∉ diagonalTorus (ZMod p) 2 := fun h ↦ hxd <| by
      simpa using mul_mem h (inv_mem (scalar_mem_diagonalTorus s))
    have hx'₀ : (x * scalar (Fin 2) s) 0 0 = 0 := apply_zero_zero_of_mem_labelNs (hK hx'K) hx'd
    have hx'₁ : (x * scalar (Fin 2) s) 1 1 = 0 := apply_one_one_of_mem_labelNs (hK hx'K) hx'd
    have hv : (x * scalar (Fin 2) s) 1 0 ≠ 0 := fun hv ↦ by
      have hdet : (x * scalar (Fin 2) s).val.det ≠ 0 := (isUnits_det_units _).ne_zero
      rw [Matrix.det_fin_two, hx'₀, hv] at hdet
      simp at hdet
    refine ⟨_, ht (u := Units.mk0 _ hv), ?_⟩
    have hK' : K.map (MulAut.conj (diagGL ![Units.mk0 _ hv, 1])).toMonoidHom ∈
        subgroupConjClass p K := map_conj_mem_subgroupConjClass K _
    refine ⟨fun _ ↦ ⟨_, Subgroup.mem_map_of_mem _ hx'K, ?_⟩,
      fun h ↦ absurd ((isNsDetDisjoint_map_conj_iff ht).mpr hdisj) h⟩
    rw [MulEquiv.coe_toMonoidHom, val_mulAut_conj_diagGL hx'₀ hx'₁ hv, ← hdetv hx'₀,
      inf_center_eq_of_mem_subgroupConjClass hK']
    have hval : ((-det (x * scalar (Fin 2) s) : (ZMod p)ˣ) : ZMod p) =
        (ZMod.leastPrimitiveRoot p : ZMod p) ^
          (K ⊓ Subgroup.center (GL (Fin 2) (ZMod p))).relIndex
            (Subgroup.center (GL (Fin 2) (ZMod p))) := by
      have h₁ : -det (x * scalar (Fin 2) s) = -det x * s ^ 2 := by
        rw [map_mul, det_scalar, Fintype.card_fin, neg_mul]
      rw [h₁, hts, Units.val_pow_eq_pow_val, Units.val_mk0]
    rw [hval]
  · rw [IsNsDetDisjoint] at hdisj
    push Not at hdisj
    rcases hdisj with ⟨x, hxK, hxd, δ, hδ, hδx⟩
    have hδK : δ ∈ K := hδ.1
    have hδd : δ ∈ diagonalTorus (ZMod p) 2 := hδ.2
    have hx'K : x * δ⁻¹ ∈ K := mul_mem hxK (inv_mem hδK)
    have hx'd : x * δ⁻¹ ∉ diagonalTorus (ZMod p) 2 := fun h ↦ hxd <| by
      simpa using mul_mem h hδd
    have hx'₀ : (x * δ⁻¹) 0 0 = 0 := apply_zero_zero_of_mem_labelNs (hK hx'K) hx'd
    have hx'₁ : (x * δ⁻¹) 1 1 = 0 := apply_one_one_of_mem_labelNs (hK hx'K) hx'd
    have hdet₁ : det (x * δ⁻¹) = -1 := by
      rw [map_mul, map_inv, hδx, inv_neg, mul_neg, mul_inv_cancel]
    have huv : (x * δ⁻¹) 0 1 * (x * δ⁻¹) 1 0 = 1 := by
      rw [← hdetv hx'₀, hdet₁, neg_neg, Units.val_one]
    have hv : (x * δ⁻¹) 1 0 ≠ 0 := fun hv ↦ by
      rw [hv, mul_zero] at huv
      exact zero_ne_one huv
    refine ⟨_, ht (u := Units.mk0 _ hv), ?_⟩
    refine ⟨fun h ↦ ?_, fun _ ↦ ?_⟩
    · refine absurd ((isNsDetDisjoint_map_conj_iff ht).mp h) ?_
      rw [IsNsDetDisjoint]
      push Not
      exact ⟨x, hxK, hxd, δ, hδ, hδx⟩
    · have hswap : MulAut.conj (diagGL ![Units.mk0 _ hv, 1]) (x * δ⁻¹) = swapGL (ZMod p) :=
        Units.ext <| by
          rw [val_mulAut_conj_diagGL hx'₀ hx'₁ hv, huv, coe_swapGL]
      exact hswap ▸ Subgroup.mem_map_of_mem _ hx'K

/-- **A subgroup of class `Ns` has a canonical Sutherland label** `ℓNs[d]`, `ℓNs.a.b[d]` or
`ℓNs.a.b.c[d]` (arXiv:1504.07618v7, §6.4). -/
lemma exists_isCanonicalSutherlandLabel_of_cls_Ns (hS : HasSutherlandClass p H .Ns) :
    ∃ L : SutherlandGroupLabel, L.cls = .Ns ∧ IsCanonicalSutherlandLabel p H L := by
  by_cases hfull : labelNsD p (H.map det).index ∈ subgroupConjClass p H
  · exact ⟨⟨.Ns, [], _⟩, rfl, hS, rfl, forall_mem_namedSubgroup rfl hfull, trivial⟩
  have hexK : ∃ K ∈ subgroupConjClass p H, K ≤ labelNs p ∧
      (IsCyclic ↥(K ⊓ diagonalTorus (ZMod p) 2) ∨ ∀ K' ∈ subgroupConjClass p H, K' ≤ labelNs p →
        ¬IsCyclic ↥(K' ⊓ diagonalTorus (ZMod p) 2)) := by
    by_cases hcyc : ∃ K ∈ subgroupConjClass p H, K ≤ labelNs p ∧
        IsCyclic ↥(K ⊓ diagonalTorus (ZMod p) 2)
    · rcases hcyc with ⟨K, hK, hKN, hc⟩
      exact ⟨K, hK, hKN, Or.inl hc⟩
    · have hH : SutherlandClass.Holds p H .Ns := hS.1
      rcases hH with ⟨K, hK, hKN, -⟩
      exact ⟨K, hK, hKN, Or.inr fun K' hK' hle hc ↦ hcyc ⟨K', hK', hle, hc⟩⟩
  rcases hexK with ⟨K, hK, hKN, hpref⟩
  have hnotCs {K' : Subgroup (GL (Fin 2) (ZMod p))} (hK' : K' ∈ subgroupConjClass p H) :
      ¬K' ≤ diagonalTorus (ZMod p) 2 := fun h ↦ hS.2 .Cs (by decide) ⟨K', hK', h⟩
  rcases exists_map_conj_isNsNormalForm hKN (hnotCs hK) with ⟨t, ht, hnf⟩
  have hK₂ : K.map (MulAut.conj t).toMonoidHom ∈ subgroupConjClass p H :=
    mem_subgroupConjClass_trans (map_conj_mem_subgroupConjClass K t) hK
  have hK₂N : K.map (MulAut.conj t).toMonoidHom ≤ labelNs p := by
    rintro - ⟨k, hk, rfl⟩
    have htN : t ∈ labelNs p := diagonalTorus_le_labelNs p ht
    exact mul_mem (mul_mem htN (hKN hk)) (inv_mem htN)
  have hpref₂ : IsNsCyclicPreferred p (K.map (MulAut.conj t).toMonoidHom) := by
    rcases hpref with hc | hc
    · exact Or.inl ((map_conj_inf_diagonalTorus ht).symm ▸ hc)
    · exact Or.inr fun K' hK' hle ↦ hc K' (mem_subgroupConjClass_trans hK' hK₂) hle
  by_cases hker : K.map (MulAut.conj t).toMonoidHom ⊓ det.ker ≤ diagonalTorus (ZMod p) 2
  · rcases exists_eq_labelNsABD hK₂N (hnotCs hK₂) hker with ⟨a, b, ha, hb, hgen, hKeq⟩
    rw [map_det_eq_of_mem_subgroupConjClass hK₂] at hKeq
    rcases exists_isLexLeastPair (P := fun a b ↦ 0 < a ∧ 0 < b ∧
      IsDetOneDiagGen p a (labelNsABD p (H.map det).index a b) ∧
        labelNsABD p (H.map det).index a b ⊓ det.ker ≤ diagonalTorus (ZMod p) 2 ∧
          labelNsABD p (H.map det).index a b ∈ subgroupConjClass p H ∧
            IsNsCyclicPreferred p (labelNsABD p (H.map det).index a b) ∧
              IsNsNormalForm p (labelNsABD p (H.map det).index a b))
      ⟨a, b, ha, hb, hKeq ▸ hgen, hKeq ▸ hker, hKeq ▸ hK₂, hKeq ▸ hpref₂, hKeq ▸ hnf⟩ with
      ⟨a', b', hab⟩
    exact ⟨⟨.Ns, [a', b'], _⟩, rfl, hS, rfl, forall_mem_namedSubgroup rfl hab.1.2.2.2.2.1, hfull,
      hab⟩
  · rcases exists_eq_labelNsABCD hK₂N hker with ⟨a, b, c, ha, hb, hc, hgen, hKeq⟩
    rw [map_det_eq_of_mem_subgroupConjClass hK₂] at hKeq
    have hex : ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧
        IsDetOneDiagGen p a (labelNsABCD p (H.map det).index a b c) ∧
          ¬labelNsABCD p (H.map det).index a b c ⊓ det.ker ≤ diagonalTorus (ZMod p) 2 ∧
            labelNsABCD p (H.map det).index a b c ∈ subgroupConjClass p H ∧
              IsNsCyclicPreferred p (labelNsABCD p (H.map det).index a b c) ∧
                IsNsNormalForm p (labelNsABCD p (H.map det).index a b c) :=
      ⟨a, b, c, ha, hb, hc, hKeq ▸ hgen, hKeq ▸ hker, hKeq ▸ hK₂, hKeq ▸ hpref₂, hKeq ▸ hnf⟩
    rcases exists_isLexLeastTriple hex with ⟨a', b', c', habc⟩
    exact ⟨⟨.Ns, [a', b', c'], _⟩, rfl, hS, rfl, forall_mem_namedSubgroup rfl habc.1.2.2.2.2.2.1,
      hfull, habc⟩

end Matrix.GeneralLinearGroup
