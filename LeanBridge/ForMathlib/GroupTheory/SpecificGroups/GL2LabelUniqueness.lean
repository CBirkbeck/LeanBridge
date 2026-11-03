import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.GL2LabelExistence

/-!
# Uniqueness of Sutherland's labels of subgroups of `GL₂(𝔽_p)`

A subgroup of `GL₂(𝔽_p)` of class `Ns` or `Nn` can only have one of the two forms of labels
`ℓS.a.b[d]` and `ℓS.a.b.c[d]` of its class. For `Nn` this is because a group `⟨c, γ⟩` of the first
form, not conjugate into `C_s⁺`, determines the Cartan part of its conjugates in `C_ns⁺`. For `Ns`
this is Sutherland's Lemma 3.16 (arXiv:1504.07618v7): conjugate subgroups of `C_s⁺` with different
diagonal parts have the Klein group as projective image, and the two diagonal parts are `Z ∪ Z I`
and `Z ∪ Z J` for scalars `Z` and `I`, `J` of trace `0`, which is cyclic exactly when `I²` is not
the square of an element of `Z`.

## Main results

* `Matrix.GeneralLinearGroup.isCyclic_inf_diagonalTorus_iff`: the cyclicity criterion for a diagonal
  part `Z ∪ Z J`.
* `Matrix.GeneralLinearGroup.false_of_isNsCyclicPreferred`: the two forms of `Ns` labels exclude
  each other (Lemma 3.16 of the paper).
* `Matrix.GeneralLinearGroup.IsCanonicalSutherlandLabel.false_of_Nn`: the two forms of `Nn` labels
  exclude each other.
* `Matrix.GeneralLinearGroup.IsCanonicalSutherlandLabel.eq`: **Sutherland's label of a subgroup of
  `GL₂(𝔽_p)` is unique.**
-/

open Matrix MulAction TauCeti

open scoped MatrixGroups Pointwise

namespace Matrix.GeneralLinearGroup

variable {p : ℕ} [Fact p.Prime] {H K N₂ N₃ : Subgroup (GL (Fin 2) (ZMod p))}
  {Q z : GL (Fin 2) (ZMod p)}

lemma exists_eq_map_conj_of_mem_subgroupConjClass (hK : K ∈ subgroupConjClass p H) :
    ∃ P : GL (Fin 2) (ZMod p), K = H.map (MulAut.conj P).toMonoidHom := by
  rcases hK with ⟨g, rfl⟩
  refine ⟨ConjAct.ofConjAct g, ?_⟩
  rw [map_conj_eq_smul, ConjAct.toConjAct_ofConjAct]

lemma eq_scalar_of_mem_center (hz : z ∈ Subgroup.center (GL (Fin 2) (ZMod p))) :
    ∃ v : (ZMod p)ˣ, z = scalar (Fin 2) v := by
  rw [center_eq_range_scalar] at hz
  rcases hz with ⟨v, rfl⟩
  exact ⟨v, rfl⟩

lemma scalar_neg_one : scalar (Fin 2) (-1 : (ZMod p)ˣ) = -1 := Units.ext <| by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

variable (K) in
lemma exists_mem_zpowers_iff_scalar_mem :
    ∃ ζ : (ZMod p)ˣ, ∀ {v : (ZMod p)ˣ}, v ∈ Subgroup.zpowers ζ ↔ scalar (Fin 2) v ∈ K := by
  rcases (K.comap (scalar (Fin 2))).isCyclic_iff_exists_zpowers_eq_top.mp inferInstance with
    ⟨ζ, hζ⟩
  exact ⟨ζ, by rw [hζ]; exact Iff.rfl⟩

lemma eq_of_sq_eq_one_of_isCyclic_subgroup {G : Type*} [Group G] [Finite G] {A : Subgroup G}
    [IsCyclic A] {x y : G} (hx : x ∈ A) (hy : y ∈ A) (hx₂ : x ^ 2 = 1) (hy₂ : y ^ 2 = 1)
    (hx₁ : x ≠ 1) (hy₁ : y ≠ 1) : x = y := by
  classical
  have : Fintype A := Fintype.ofFinite A
  by_contra hne
  have hsub : ({1, ⟨x, hx⟩, ⟨y, hy⟩} : Finset A) ⊆ Finset.univ.filter fun a : A ↦ a ^ 2 = 1 := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · simp
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Subtype.ext hx₂⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Subtype.ext hy₂⟩
  have hcard : ({1, ⟨x, hx⟩, ⟨y, hy⟩} : Finset A).card = 3 :=
    Finset.card_eq_three.mpr ⟨1, ⟨x, hx⟩, ⟨y, hy⟩, fun h ↦ hx₁ (congrArg Subtype.val h).symm,
      fun h ↦ hy₁ (congrArg Subtype.val h).symm, fun h ↦ hne (congrArg Subtype.val h), rfl⟩
  have hle : (Finset.univ.filter fun a : A ↦ a ^ 2 = 1).card ≤ 2 :=
    IsCyclic.card_pow_eq_one_le two_pos
  have hle' : ({1, ⟨x, hx⟩, ⟨y, hy⟩} : Finset A).card ≤
      (Finset.univ.filter fun a : A ↦ a ^ 2 = 1).card := Finset.card_le_card hsub
  omega

/-- **The cyclicity criterion for a diagonal part**, used in Lemma 3.16 of Sutherland
(arXiv:1504.07618v7): if the diagonal part `K ∩ C_s` of a subgroup `K` containing `-1` consists of
scalars and of elements of trace `0`, and contains an element `J` of trace `0` with entry `u`, then
it is cyclic exactly when `u²` is not the square of a scalar of `K`. -/
lemma isCyclic_inf_diagonalTorus_iff {J : GL (Fin 2) (ZMod p)} {u : (ZMod p)ˣ}
    (hJ : J ∈ K ⊓ diagonalTorus (ZMod p) 2) (hJu : J 0 0 = u) (hJt : J 1 1 = -u)
    (hJc : J ∉ Subgroup.center (GL (Fin 2) (ZMod p))) (hneg : (-1 : GL (Fin 2) (ZMod p)) ∈ K)
    (hall : ∀ a ∈ K ⊓ diagonalTorus (ZMod p) 2, a ∈ Subgroup.center (GL (Fin 2) (ZMod p)) ∨
      a 1 1 = -a 0 0) :
    IsCyclic ↥(K ⊓ diagonalTorus (ZMod p) 2) ↔ ¬∃ w, scalar (Fin 2) w ∈ K ∧ w ^ 2 = u ^ 2 := by
  rcases Subgroup.mem_inf.mp hJ with ⟨hJK, hJd⟩
  have hJ₀₁ : J 0 1 = 0 := mem_diagonalTorus_iff.mp hJd (by decide)
  have hJ₁₀ : J 1 0 = 0 := mem_diagonalTorus_iff.mp hJd (by decide)
  have hJs (s : (ZMod p)ˣ) : (J * scalar (Fin 2) s).val = !![((u * s : (ZMod p)ˣ) : ZMod p), 0;
      0, -((u * s : (ZMod p)ˣ) : ZMod p)] := by
    rw [Units.val_mul]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hJ₀₁, hJ₁₀, hJu, hJt]
  have hJmem (s : (ZMod p)ˣ) (hs : scalar (Fin 2) s ∈ K) :
      J * scalar (Fin 2) s ∈ K ⊓ diagonalTorus (ZMod p) 2 :=
    Subgroup.mem_inf.mpr ⟨mul_mem hJK hs, mul_mem hJd (scalar_mem_diagonalTorus s)⟩
  have hJJ (s : (ZMod p)ˣ) : (J * scalar (Fin 2) s) * (J * scalar (Fin 2) s) =
      scalar (Fin 2) ((u * s) ^ 2) := Units.ext <| by
    rw [Units.val_mul, hJs]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sq]
  have hnot1 (s : (ZMod p)ˣ) : J * scalar (Fin 2) s ∉ Subgroup.center (GL (Fin 2) (ZMod p)) :=
    fun h ↦ hJc <| by
      have h₁ : J * scalar (Fin 2) s * scalar (Fin 2) s⁻¹ ∈ Subgroup.center (GL (Fin 2) (ZMod p)) :=
        mul_mem h (scalar_mem_center s⁻¹)
      rwa [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one] at h₁
  have hneg₁ : (-1 : GL (Fin 2) (ZMod p)) ≠ 1 := fun h ↦ hJc <| by
    have h₂ : (-1 : ZMod p) = 1 := by
      simpa using congrArg (fun z : GL (Fin 2) (ZMod p) ↦ z 0 0) h
    refine mem_center_iff_entries.mpr ⟨hJ₀₁, hJ₁₀, ?_⟩
    rw [hJu, hJt, neg_eq_neg_one_mul, h₂, one_mul]
  constructor
  · rintro hcyc ⟨w, hw, hwu⟩
    have hwi : scalar (Fin 2) w⁻¹ ∈ K := by
      rw [map_inv]
      exact inv_mem hw
    have hxy : J * scalar (Fin 2) w⁻¹ = -1 :=
      eq_of_sq_eq_one_of_isCyclic_subgroup (hJmem _ hwi)
        (Subgroup.mem_inf.mpr ⟨hneg, scalar_neg_one (p := p) ▸ scalar_mem_diagonalTorus _⟩)
        (by rw [sq, hJJ, mul_pow, inv_pow, hwu, mul_inv_cancel, map_one]) (by simp)
        (fun h ↦ hnot1 w⁻¹ (h ▸ one_mem _)) hneg₁
    exact hnot1 w⁻¹ (hxy ▸ scalar_neg_one (p := p) ▸ scalar_mem_center _)
  · intro hns
    rcases exists_mem_zpowers_iff_scalar_mem K with ⟨ζ, hmem⟩
    have hu₂ : u ^ 2 ∈ Subgroup.zpowers ζ := by
      refine hmem.mpr ?_
      have h₁ : (J * scalar (Fin 2) 1) * (J * scalar (Fin 2) 1) = scalar (Fin 2) ((u * 1) ^ 2) :=
        hJJ 1
      rw [map_one, mul_one, mul_one] at h₁
      exact h₁ ▸ mul_mem hJK hJK
    rcases Subgroup.mem_zpowers_iff.mp hu₂ with ⟨k, hk⟩
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · refine absurd ⟨ζ ^ m, hmem.mp (zpow_mem (Subgroup.mem_zpowers ζ) m), ?_⟩ hns
      rw [← hk]
      group
    · have hy₀K : scalar (Fin 2) (ζ ^ (-m)) ∈ K := hmem.mp (zpow_mem (Subgroup.mem_zpowers ζ) _)
      have hy₀₂ : (J * scalar (Fin 2) (ζ ^ (-m))) * (J * scalar (Fin 2) (ζ ^ (-m))) =
          scalar (Fin 2) ζ := by
        rw [hJJ, mul_pow, ← hk]
        congr 1
        group
      have hζz : scalar (Fin 2) ζ ∈ Subgroup.zpowers (J * scalar (Fin 2) (ζ ^ (-m))) := by
        rw [← hy₀₂]
        exact mul_mem (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
      have hs (v : (ZMod p)ˣ) (hv : scalar (Fin 2) v ∈ K) :
          scalar (Fin 2) v ∈ Subgroup.zpowers (J * scalar (Fin 2) (ζ ^ (-m))) := by
        rcases Subgroup.mem_zpowers_iff.mp (hmem.mpr hv) with ⟨j, rfl⟩
        exact (map_zpow (scalar (Fin 2)) ζ j).symm ▸ zpow_mem hζz j
      have hle : K ⊓ diagonalTorus (ZMod p) 2 ≤
          Subgroup.zpowers (J * scalar (Fin 2) (ζ ^ (-m))) := fun a ha ↦ by
        rcases Subgroup.mem_inf.mp ha with ⟨haK, had⟩
        rcases hall a ha with hac | hat
        · rcases eq_scalar_of_mem_center hac with ⟨v, rfl⟩
          exact hs v haK
        · have ha₀₁ : a 0 1 = 0 := mem_diagonalTorus_iff.mp had (by decide)
          have ha₁₀ : a 1 0 = 0 := mem_diagonalTorus_iff.mp had (by decide)
          have ha₀ : a 0 0 ≠ 0 := fun h0 ↦ (isUnits_det_units a).ne_zero <| by
            rw [Matrix.det_fin_two, h0, ha₁₀]
            simp
          have hae : a = J * scalar (Fin 2) (u⁻¹ * Units.mk0 _ ha₀) := Units.ext <| by
            rw [hJs]
            ext i j
            fin_cases i <;> fin_cases j <;> simp [ha₀₁, ha₁₀, hat]
          have hv : scalar (Fin 2) (u⁻¹ * Units.mk0 _ ha₀) ∈ K := by
            have h₁ : J⁻¹ * a ∈ K := mul_mem (inv_mem hJK) haK
            rwa [hae, inv_mul_cancel_left] at h₁
          have hJz : J ∈ Subgroup.zpowers (J * scalar (Fin 2) (ζ ^ (-m))) := by
            have h₁ : (J * scalar (Fin 2) (ζ ^ (-m))) * scalar (Fin 2) (ζ ^ m) = J := by
              rw [mul_assoc, ← map_mul, show ζ ^ (-m) * ζ ^ m = 1 by group, map_one, mul_one]
            have h₂ : (J * scalar (Fin 2) (ζ ^ (-m))) * scalar (Fin 2) (ζ ^ m) ∈
                Subgroup.zpowers (J * scalar (Fin 2) (ζ ^ (-m))) :=
              mul_mem (Subgroup.mem_zpowers _)
                (hs _ (hmem.mp (zpow_mem (Subgroup.mem_zpowers ζ) m)))
            rwa [h₁] at h₂
          rw [hae]
          exact mul_mem hJz (hs _ hv)
      exact Subgroup.isCyclic_of_le hle

lemma exists_sq_eq_mul_of_not_exists_sq {G : Type*} [CommGroup G] {ζ a b : G}
    (ha : a ∈ Subgroup.zpowers ζ) (hb : b ∈ Subgroup.zpowers ζ)
    (hna : ¬∃ w ∈ Subgroup.zpowers ζ, w ^ 2 = a) (hnb : ¬∃ w ∈ Subgroup.zpowers ζ, w ^ 2 = b) :
    ∃ w ∈ Subgroup.zpowers ζ, w ^ 2 = a * b := by
  rcases Subgroup.mem_zpowers_iff.mp ha with ⟨k, rfl⟩
  rcases Subgroup.mem_zpowers_iff.mp hb with ⟨l, rfl⟩
  have hodd {j : ℤ} (hj : ¬∃ w ∈ Subgroup.zpowers ζ, w ^ 2 = ζ ^ j) : ∃ m, j = 2 * m + 1 := by
    rcases Int.even_or_odd' j with ⟨m, rfl | hm⟩
    · refine absurd ⟨ζ ^ m, zpow_mem (Subgroup.mem_zpowers ζ) m, ?_⟩ hj
      group
    · exact ⟨m, hm⟩
  rcases hodd hna with ⟨m, rfl⟩
  rcases hodd hnb with ⟨n, rfl⟩
  refine ⟨ζ ^ (m + n + 1), zpow_mem (Subgroup.mem_zpowers ζ) _, ?_⟩
  group

lemma mul_self_eq_neg_one_of_diag {I : GL (Fin 2) (ZMod p)} (h₀₁ : I 0 1 = 0) (h₁₀ : I 1 0 = 0)
    (h₁₁ : I 1 1 = -I 0 0) (hd : I 0 0 * I 1 1 = 1) : I * I = -1 := Units.ext <| by
  rw [Units.val_mul]
  rw [h₁₁] at hd
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, h₀₁, h₁₀, h₁₁]
  all_goals linear_combination -hd

lemma apply_one_one_eq_neg_of_trace_eq_zero (h : z.val.trace = 0) : z 1 1 = -z 0 0 := by
  rw [Matrix.trace_fin_two] at h
  linear_combination h

lemma mulAut_conj_notMem_diagonalTorus (hQ : Q ∉ labelNs p) (hz : z ∈ diagonalTorus (ZMod p) 2)
    (hzc : z ∉ Subgroup.center (GL (Fin 2) (ZMod p))) :
    MulAut.conj Q z ∉ diagonalTorus (ZMod p) 2 := fun hd ↦
  hQ <| mem_labelNs_of_mulAut_conj_mem hz hd fun h ↦ hzc <| mem_center_iff_entries.mpr
    ⟨mem_diagonalTorus_iff.mp hz (by decide), mem_diagonalTorus_iff.mp hz (by decide), h⟩

lemma mem_center_or_apply_one_one_eq_neg {N N' : Subgroup (GL (Fin 2) (ZMod p))}
    (hN' : N' ≤ labelNs p) (hQ : Q ∉ labelNs p) (hc : ∀ a ∈ N, MulAut.conj Q a ∈ N')
    (a : GL (Fin 2) (ZMod p)) (ha : a ∈ N ⊓ diagonalTorus (ZMod p) 2) :
    a ∈ Subgroup.center (GL (Fin 2) (ZMod p)) ∨ a 1 1 = -a 0 0 := by
  by_cases hac : a ∈ Subgroup.center (GL (Fin 2) (ZMod p))
  · exact Or.inl hac
  · rcases Subgroup.mem_inf.mp ha with ⟨haN, had⟩
    exact Or.inr <| apply_one_one_eq_neg_of_trace_eq_zero <|
      (Matrix.trace_units_conj Q a).symm.trans <| trace_eq_zero_of_mem_labelNs (hN' (hc a haN))
        (mulAut_conj_notMem_diagonalTorus hQ had hac)

/-- **The two forms of `Ns` labels exclude each other** (Lemma 3.16 of Sutherland,
arXiv:1504.07618v7): conjugate subgroups `N₂`, `N₃` of `C_s⁺` with dihedral projective image, whose
diagonal parts are chosen as in Sutherland's script (`IsNsCyclicPreferred`), cannot have their
determinant-one parts in `C_s` for `N₂` and outside `C_s` for `N₃`. A determinant-one antidiagonal
element `y` of `N₃` is the conjugate of a diagonal element `I` of `N₂`, so the conjugation does not
normalize `C_s`; then `N₂ ∩ C_s = Z ∪ Z I` and `N₃ ∩ C_s = Z ∪ Z J`, with `I² = -1` and `J²` both
squares of scalars of `Z` or both not, so `-J²` is a square, which gives an antidiagonal element of
`N₂` of determinant one. -/
lemma false_of_isNsCyclicPreferred (hN₂ : N₂ ≤ labelNs p) (hN₃ : N₃ ≤ labelNs p)
    (hconj : N₃ ∈ subgroupConjClass p N₂) (hker₂ : N₂ ⊓ det.ker ≤ diagonalTorus (ZMod p) 2)
    (hker₃ : ¬N₃ ⊓ det.ker ≤ diagonalTorus (ZMod p) 2) (hpref₂ : IsNsCyclicPreferred p N₂)
    (hpref₃ : IsNsCyclicPreferred p N₃) (hdih : HasDihedralImage p N₃) : False := by
  rcases exists_eq_map_conj_of_mem_subgroupConjClass hconj with ⟨P, hP⟩
  have hc₂₃ {a : GL (Fin 2) (ZMod p)} (ha : a ∈ N₂) : MulAut.conj P a ∈ N₃ :=
    hP ▸ Subgroup.mem_map_of_mem _ ha
  have hc₃₂ {b : GL (Fin 2) (ZMod p)} (hb : b ∈ N₃) : MulAut.conj P⁻¹ b ∈ N₂ := by
    rw [hP] at hb
    rcases hb with ⟨a, ha, rfl⟩
    simpa [mul_assoc] using ha
  rcases Set.not_subset.mp hker₃ with ⟨y, hy', hyd⟩
  rcases Subgroup.mem_inf.mp hy' with ⟨hy, hy₁⟩
  have hconj_conj (z : GL (Fin 2) (ZMod p)) : MulAut.conj P (MulAut.conj P⁻¹ z) = z := by
    simp [mul_assoc]
  have hI : MulAut.conj P⁻¹ y ∈ N₂ := hc₃₂ hy
  have hId : MulAut.conj P⁻¹ y ∈ diagonalTorus (ZMod p) 2 :=
    hker₂ (Subgroup.mem_inf.mpr ⟨hI, MonoidHom.mem_ker.mpr <| by
      simpa using MonoidHom.mem_ker.mp hy₁⟩)
  have hI₀₁ : (MulAut.conj P⁻¹ y) 0 1 = 0 := mem_diagonalTorus_iff.mp hId (by decide)
  have hI₁₀ : (MulAut.conj P⁻¹ y) 1 0 = 0 := mem_diagonalTorus_iff.mp hId (by decide)
  have hItr : (MulAut.conj P⁻¹ y) 1 1 = -(MulAut.conj P⁻¹ y) 0 0 :=
    apply_one_one_eq_neg_of_trace_eq_zero <| (Matrix.trace_units_conj P⁻¹ y).trans <|
      trace_eq_zero_of_mem_labelNs (hN₃ hy) hyd
  have hIc : MulAut.conj P⁻¹ y ∉ Subgroup.center (GL (Fin 2) (ZMod p)) := fun h ↦ hyd <| by
    have h₁ : MulAut.conj P (MulAut.conj P⁻¹ y) = MulAut.conj P⁻¹ y := by
      rw [MulAut.conj_apply P, Subgroup.mem_center_iff.mp h P, mul_inv_cancel_right]
    rw [← hconj_conj y, h₁]
    exact hId
  have hIne : (MulAut.conj P⁻¹ y) 0 0 ≠ (MulAut.conj P⁻¹ y) 1 1 :=
    fun h ↦ hIc (mem_center_iff_entries.mpr ⟨hI₀₁, hI₁₀, h⟩)
  have hp : p ≠ 2 := by
    rintro rfl
    refine hIne ?_
    rw [hItr]
    exact (CharTwo.neg_eq _).symm
  have hPN : P ∉ labelNs p := fun h ↦ hyd <| by
    rw [labelNs_eq_normalizer p hp] at h
    have h₁ : P * MulAut.conj P⁻¹ y * P⁻¹ ∈ diagonalTorus (ZMod p) 2 :=
      (Subgroup.mem_normalizer_iff.mp h _).mp hId
    rw [← hconj_conj y]
    exact h₁
  have hPN' : P⁻¹ ∉ labelNs p := fun h ↦ hPN <| by
    simpa using inv_mem h
  have hC (k₁ : GL (Fin 2) (ZMod p)) (hk₁ : k₁ ∈ N₃) (k₂ : GL (Fin 2) (ZMod p)) (hk₂ : k₂ ∈ N₃)
      (h₁ : k₁ ∉ diagonalTorus (ZMod p) 2) (h₂ : k₂ ∉ diagonalTorus (ZMod p) 2) :
      k₁⁻¹ * k₂ ∈ diagonalTorus (ZMod p) 2 := by
    have h₁' : k₁⁻¹ ∉ diagonalTorus (ZMod p) 2 := fun h ↦ h₁ (by simpa using inv_mem h)
    have hk₁' : k₁⁻¹ ∈ labelNs p := hN₃ (inv_mem hk₁)
    refine mem_diagonalTorus_of_fin_two _ ?_ ?_
    · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
        apply_zero_zero_of_mem_labelNs hk₁' h₁', apply_one_one_of_mem_labelNs (hN₃ hk₂) h₂]
      ring1
    · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, apply_one_one_of_mem_labelNs hk₁' h₁',
        apply_zero_zero_of_mem_labelNs (hN₃ hk₂) h₂]
      ring1
  rcases exists_mem_inf_notMem_center_of_hasDihedralImage hdih hC with ⟨J, hJ, hJc⟩
  rcases Subgroup.mem_inf.mp hJ with ⟨hJN, hJd⟩
  have hJ₁ : MulAut.conj P⁻¹ J ∈ N₂ := hc₃₂ hJN
  have hJ₁d : MulAut.conj P⁻¹ J ∉ diagonalTorus (ZMod p) 2 :=
    mulAut_conj_notMem_diagonalTorus hPN' hJd hJc
  have hJtr : J 1 1 = -J 0 0 :=
    apply_one_one_eq_neg_of_trace_eq_zero <| (Matrix.trace_units_conj P⁻¹ J).symm.trans <|
      trace_eq_zero_of_mem_labelNs (hN₂ hJ₁) hJ₁d
  have hneq (z : GL (Fin 2) (ZMod p)) (hzd : z ∈ diagonalTorus (ZMod p) 2) : z 0 0 ≠ 0 := by
    intro h0
    have hdet : z.val.det ≠ 0 := (isUnits_det_units z).ne_zero
    rw [Matrix.det_fin_two, h0,
      mem_diagonalTorus_iff.mp hzd (show (1 : Fin 2) ≠ 0 by decide)] at hdet
    simp at hdet
  have hI₀ : (MulAut.conj P⁻¹ y) 0 0 ≠ 0 := hneq _ hId
  have hJ₀ : J 0 0 ≠ 0 := hneq _ hJd
  have hIdet : (MulAut.conj P⁻¹ y) 0 0 * (MulAut.conj P⁻¹ y) 1 1 = 1 := by
    have h₁ : (det (MulAut.conj P⁻¹ y)).val = 1 := by
      have h₂ : det (MulAut.conj P⁻¹ y) = 1 := by
        simpa using MonoidHom.mem_ker.mp hy₁
      rw [h₂, Units.val_one]
    rwa [val_det_apply, Matrix.det_fin_two, hI₁₀, mul_zero, sub_zero] at h₁
  have hxx : Units.mk0 _ hI₀ ^ 2 = -1 := Units.ext <| by
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_neg, Units.val_one]
    rw [hItr] at hIdet
    linear_combination -hIdet
  have hneg₂ : (-1 : GL (Fin 2) (ZMod p)) ∈ N₂ :=
    mul_self_eq_neg_one_of_diag hI₀₁ hI₁₀ hItr hIdet ▸ mul_mem hI hI
  have hneg₃ : (-1 : GL (Fin 2) (ZMod p)) ∈ N₃ := by
    simpa using hc₂₃ hneg₂
  have hsc {w : (ZMod p)ˣ} : scalar (Fin 2) w ∈ N₂ ↔ scalar (Fin 2) w ∈ N₃ := by
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · exact mulAut_conj_scalar P w ▸ hc₂₃ h
    · exact mulAut_conj_scalar P⁻¹ w ▸ hc₃₂ h
  have cyc₂ : IsCyclic ↥(N₂ ⊓ diagonalTorus (ZMod p) 2) ↔
      ¬∃ w, scalar (Fin 2) w ∈ N₂ ∧ w ^ 2 = Units.mk0 _ hI₀ ^ 2 :=
    isCyclic_inf_diagonalTorus_iff (Subgroup.mem_inf.mpr ⟨hI, hId⟩) rfl hItr hIc hneg₂
      (mem_center_or_apply_one_one_eq_neg hN₃ hPN fun _ ↦ hc₂₃)
  have cyc₃ : IsCyclic ↥(N₃ ⊓ diagonalTorus (ZMod p) 2) ↔
      ¬∃ w, scalar (Fin 2) w ∈ N₃ ∧ w ^ 2 = Units.mk0 _ hJ₀ ^ 2 :=
    isCyclic_inf_diagonalTorus_iff hJ rfl hJtr hJc hneg₃
      (mem_center_or_apply_one_one_eq_neg hN₂ hPN' fun _ ↦ hc₃₂)
  have hconj' : N₂ ∈ subgroupConjClass p N₃ := by
    rw [subgroupConjClass, orbit_eq_iff.mpr hconj]
    exact mem_orbit_self N₂
  have h₂₃ (hc : IsCyclic ↥(N₂ ⊓ diagonalTorus (ZMod p) 2)) :
      IsCyclic ↥(N₃ ⊓ diagonalTorus (ZMod p) 2) := by
    rcases hpref₃ with h | h
    · exact h
    · exact absurd hc (h N₂ hconj' hN₂)
  have h₃₂ (hc : IsCyclic ↥(N₃ ⊓ diagonalTorus (ZMod p) 2)) :
      IsCyclic ↥(N₂ ⊓ diagonalTorus (ZMod p) 2) := by
    rcases hpref₂ with h | h
    · exact h
    · exact absurd hc (h N₃ hconj hN₃)
  have hJsq : J * J = scalar (Fin 2) (Units.mk0 _ hJ₀ ^ 2) := Units.ext <| by
    rw [Units.val_mul]
    have h₀₁ : J 0 1 = 0 := mem_diagonalTorus_iff.mp hJd (by decide)
    have h₁₀ : J 1 0 = 0 := mem_diagonalTorus_iff.mp hJd (by decide)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, h₀₁, h₁₀, hJtr, sq]
  have hmain : ∃ w, scalar (Fin 2) w ∈ N₂ ∧ w ^ 2 = -Units.mk0 _ hJ₀ ^ 2 := by
    by_cases h₁ : ∃ w, scalar (Fin 2) w ∈ N₂ ∧ w ^ 2 = Units.mk0 _ hI₀ ^ 2
    · rcases h₁ with ⟨w₁, hw₁, hw₁x⟩
      by_contra hc
      have h₃ : ¬∃ w, scalar (Fin 2) w ∈ N₃ ∧ w ^ 2 = Units.mk0 _ hJ₀ ^ 2 := by
        rintro ⟨w₃, hw₃, hw₃u⟩
        refine hc ⟨w₁ * w₃, ?_, ?_⟩
        · rw [map_mul]
          exact mul_mem hw₁ (hsc.mpr hw₃)
        · rw [mul_pow, hw₁x, hxx, hw₃u, neg_one_mul]
      exact cyc₂.mp (h₃₂ (cyc₃.mpr h₃)) ⟨w₁, hw₁, hw₁x⟩
    · have h₃ : ¬∃ w, scalar (Fin 2) w ∈ N₃ ∧ w ^ 2 = Units.mk0 _ hJ₀ ^ 2 :=
        cyc₃.mp (h₂₃ (cyc₂.mpr h₁))
      rcases exists_mem_zpowers_iff_scalar_mem N₂ with ⟨ζ, hmem⟩
      rcases exists_sq_eq_mul_of_not_exists_sq (ζ := ζ) (a := Units.mk0 _ hI₀ ^ 2)
        (b := Units.mk0 _ hJ₀ ^ 2) (hmem.mpr (by rw [hxx, scalar_neg_one]; exact hneg₂))
        (hmem.mpr (hsc.mpr (hJsq ▸ mul_mem hJN hJN)))
        (fun ⟨w, hw, hwx⟩ ↦ h₁ ⟨w, hmem.mp hw, hwx⟩)
        (fun ⟨w, hw, hwu⟩ ↦ h₃ ⟨w, hsc.mp (hmem.mp hw), hwu⟩) with ⟨w, hw, hwe⟩
      exact ⟨w, hmem.mp hw, by rw [hwe, hxx, neg_one_mul]⟩
  rcases hmain with ⟨w, hw, hwu⟩
  have hw' : scalar (Fin 2) w⁻¹ ∈ N₂ := by
    rw [map_inv]
    exact inv_mem hw
  have hJ₂d : MulAut.conj P⁻¹ J * scalar (Fin 2) w⁻¹ ∉ diagonalTorus (ZMod p) 2 :=
    fun h ↦ hJ₁d <| by simpa using mul_mem h (scalar_mem_diagonalTorus w)
  refine hJ₂d (hker₂ (Subgroup.mem_inf.mpr ⟨mul_mem hJ₁ hw', MonoidHom.mem_ker.mpr ?_⟩))
  have hdetJ : det J = -Units.mk0 _ hJ₀ ^ 2 := Units.ext <| by
    have h₀₁ : J 0 1 = 0 := mem_diagonalTorus_iff.mp hJd (by decide)
    rw [val_det_apply, Matrix.det_fin_two, h₀₁, hJtr]
    simp [sq]
  rw [map_mul, det_scalar, Fintype.card_fin, inv_pow, hwu, ← hdetJ]
  simp

variable (d a b c : ℕ)

lemma labelNsABD_le : labelNsABD p d a b ≤ labelNs p := by
  refine (Subgroup.closure_le _).mpr fun g hg ↦ mem_labelNs_iff.mpr ?_
  simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with hg | hg
  · exact Or.inl ⟨by simp [hg], by simp [hg]⟩
  · exact Or.inr ⟨by simp [hg], by simp [hg]⟩

lemma labelNsABCD_le : labelNsABCD p d a b c ≤ labelNs p := by
  refine (Subgroup.closure_le _).mpr fun g hg ↦ mem_labelNs_iff.mpr ?_
  simp only [Set.mem_preimage, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with hg | hg | hg
  · exact Or.inl ⟨by simp [hg], by simp [hg]⟩
  · exact Or.inr ⟨by simp [hg], by simp [hg]⟩
  · exact Or.inr ⟨by simp [hg], by simp [hg]⟩

lemma labelNnABC_le (hp : p ≠ 2) {δ : GL (Fin 2) (ZMod p)} (hδ : δ ∈ labelCn p) :
    labelNnABC p a b c δ ≤ labelNn p := by
  refine sup_le ((Subgroup.closure_le _).mpr fun g hg ↦ labelCn_le_labelNn p ?_)
    (Subgroup.zpowers_le.mpr (mul_mem (gammaGL_mem_labelNn hp)
      (pow_mem (labelCn_le_labelNn p hδ) c)))
  rw [mem_labelCn_iff p hp]
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hg
  simp [hg]

variable {d a b c} {a' b' d' : ℕ} {ps ps' : List ℕ}

/-- **The two forms of `Nn` labels exclude each other**, for odd `p`: a group `Nn.a.b = ⟨c, γ⟩` of
class `Nn` has `c` non-scalar of nonzero trace, as otherwise it would lie in `C_s⁺`, so a
conjugation taking it into `C_ns⁺` normalizes `C_ns`, and then the conjugate of `γ` shows that the
sets `det(K ∩ C_ns)` and `-det(K \ C_ns)` meet, unlike for `Nn.a.b.c`. -/
lemma IsCanonicalSutherlandLabel.false_of_Nn (hp : p ≠ 2)
    (hL : IsCanonicalSutherlandLabel p H ⟨.Nn, [a, b], d⟩)
    (hL' : IsCanonicalSutherlandLabel p H ⟨.Nn, [a', b', c], d'⟩) : False := by
  have hN₂ : labelNnAB p a b ∈ subgroupConjClass p H := hL.2.2.1 _ rfl
  have hNs : ¬∃ K ∈ subgroupConjClass p H, K ≤ labelNs p := hL.1.1.2
  have hgen₂ : (gammaGL p) ∈ labelNnAB p a b :=
    Subgroup.subset_closure (Or.inr (val_gammaGL p))
  have hab : (a : ZMod p) ≠ 0 ∧ (b : ZMod p) ≠ 0 := by
    by_contra hc
    refine hNs ⟨_, hN₂, (Subgroup.closure_le _).mpr fun g hg ↦ mem_labelNs_iff.mpr ?_⟩
    rcases hg with hg | hg
    · rcases not_and_or.mp hc with h | h
      · exact Or.inr ⟨by simp [hg, not_not.mp h], by simp [hg, not_not.mp h]⟩
      · exact Or.inl ⟨by simp [hg, not_not.mp h], by simp [hg, not_not.mp h]⟩
    · exact Or.inl ⟨by simp [Set.mem_singleton_iff.mp hg], by simp [Set.mem_singleton_iff.mp hg]⟩
  have hε : ¬IsSquare (ZMod.leastPrimitiveRoot p : ZMod p) :=
    ZMod.not_isSquare_leastPrimitiveRoot p hp
  have hdetM : (!![(a : ZMod p), (ZMod.leastPrimitiveRoot p : ZMod p) * b; (b : ZMod p), a] :
      Matrix (Fin 2) (Fin 2) (ZMod p)).det ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    intro h0
    refine hε ⟨(a : ZMod p) / b, ?_⟩
    field_simp [hab.2]
    linear_combination -h0
  have hc₁C : mkOfDetNeZero _ hdetM ∈ labelCn p :=
    (mem_labelCn_iff p hp).mpr ⟨by simp, by simp⟩
  have hc₁ : mkOfDetNeZero _ hdetM ∈ labelNnAB p a b :=
    Subgroup.subset_closure (Or.inl rfl)
  have hδ : nonsplitCartanGen p ∈ labelCn p := by
    rw [← zpowers_nonsplitCartanGen p]
    exact Subgroup.mem_zpowers _
  have hN₃P : IsNnDetDisjoint p (labelNnABC p a' b' c (nonsplitCartanGen p)) ∧
      labelNnABC p a' b' c (nonsplitCartanGen p) ∈ subgroupConjClass p H :=
    hL'.2.2.2.2.2.1.2.2.2 _ (zpowers_nonsplitCartanGen p)
  have hconj : labelNnABC p a' b' c (nonsplitCartanGen p) ∈ subgroupConjClass p (labelNnAB p a b) :=
    orbit_eq_iff.mp <| (orbit_eq_iff.mpr hN₃P.2).trans (orbit_eq_iff.mpr hN₂).symm
  rcases exists_eq_map_conj_of_mem_subgroupConjClass hconj with ⟨P, hP⟩
  have hc₂ : MulAut.conj P (mkOfDetNeZero _ hdetM) ∈ labelNnABC p a' b' c (nonsplitCartanGen p) :=
    hP ▸ Subgroup.mem_map_of_mem _ hc₁
  have hle : labelNnABC p a' b' c (nonsplitCartanGen p) ≤ labelNn p := labelNnABC_le a' b' c hp hδ
  have hc₂C : MulAut.conj P (mkOfDetNeZero _ hdetM) ∈ labelCn p := by
    by_contra hnot
    have htr : (mkOfDetNeZero _ hdetM).val.trace = 0 :=
      (Matrix.trace_units_conj P _).symm.trans (trace_eq_zero_of_mem_labelNn hp (hle hc₂) hnot)
    rw [Matrix.trace_fin_two] at htr
    simp only [val_mkOfDetNeZero, of_apply, cons_val_zero, cons_val_one] at htr
    exact mul_ne_zero (two_ne_zero_of_ne_two p hp) hab.1 (by linear_combination htr)
  have hPN : P ∈ labelNn p :=
    mem_labelNn_of_mulAut_conj_mem hp hc₁C hc₂C (by simpa using hab.2)
  have hxC : MulAut.conj P (gammaGL p) ∉ labelCn p := fun h ↦ by
    rw [labelNn_eq_normalizer p hp] at hPN
    exact gammaGL_notMem_labelCn hp ((Subgroup.mem_normalizer_iff.mp hPN _).mpr h)
  refine hN₃P.1 _ (hP ▸ Subgroup.mem_map_of_mem _ hgen₂) hxC ⟨1, one_mem _, ?_⟩
  simp

lemma ne_two_of_hasSutherlandClass_Nn (hS : HasSutherlandClass p H .Nn) : p ≠ 2 := by
  rintro rfl
  have hH : SutherlandClass.Holds 2 H .Nn := hS.1
  rcases hH with ⟨⟨K, hK, -, n, hn, ⟨e⟩⟩, -⟩
  have hker : ∀ {K : Subgroup (GL (Fin 2) (ZMod 2))}, Nat.card K = 6 → det.ker ≤ K := by
    intro K hK x _
    have htop : K = ⊤ := Subgroup.eq_top_of_card_eq _ <| by
      rw [hK, natCard_GL_fin_two_eq_sq_sub_one_mul, ZMod.card]
      rfl
    rw [htop]
    exact Subgroup.mem_top x
  have hcard : 2 * n ∣ Nat.card K := by
    rw [← DihedralGroup.nat_card, ← Nat.card_congr e.toEquiv]
    exact K.card_map_dvd ProjGenLinGroup.mk
  have h6 : Nat.card K ∣ 6 := by
    have h₁ : Nat.card K ∣ Nat.card (GL (Fin 2) (ZMod 2)) := Subgroup.card_subgroup_dvd_card K
    rwa [natCard_GL_fin_two_eq_sq_sub_one_mul, ZMod.card] at h₁
  have hle : Nat.card K ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  have hge : 4 ≤ Nat.card K := by
    have h₁ : 2 * n ≤ Nat.card K := Nat.le_of_dvd Nat.card_pos hcard
    omega
  have h₆ : Nat.card K = 6 := by
    interval_cases hc : Nat.card K <;> first | rfl | exact absurd h6 (by decide)
  exact hS.2 .G (by decide) ⟨K, hK, hker h₆⟩

lemma IsCanonicalSutherlandLabel.false_of_Ns (hL : IsCanonicalSutherlandLabel p H ⟨.Ns, [a, b], d⟩)
    (hL' : IsCanonicalSutherlandLabel p H ⟨.Ns, [a', b', c], d⟩) : False := by
  have h : 0 < a ∧ 0 < b ∧ IsDetOneDiagGen p a (labelNsABD p d a b) ∧
      labelNsABD p d a b ⊓ det.ker ≤ diagonalTorus (ZMod p) 2 ∧
        labelNsABD p d a b ∈ subgroupConjClass p H ∧ IsNsCyclicPreferred p (labelNsABD p d a b) ∧
          IsNsNormalForm p (labelNsABD p d a b) := hL.2.2.2.2.1
  have h' : 0 < a' ∧ 0 < b' ∧ 0 < c ∧ IsDetOneDiagGen p a' (labelNsABCD p d a' b' c) ∧
      ¬labelNsABCD p d a' b' c ⊓ det.ker ≤ diagonalTorus (ZMod p) 2 ∧
        labelNsABCD p d a' b' c ∈ subgroupConjClass p H ∧
          IsNsCyclicPreferred p (labelNsABCD p d a' b' c) ∧
            IsNsNormalForm p (labelNsABCD p d a' b' c) := hL'.2.2.2.2.1
  have hH : SutherlandClass.Holds p H .Ns := hL.1.1
  rcases hH with ⟨K, hK, -, hdih⟩
  have hN₂ : labelNsABD p d a b ∈ subgroupConjClass p H := h.2.2.2.2.1
  have hN₃ : labelNsABCD p d a' b' c ∈ subgroupConjClass p H := h'.2.2.2.2.2.1
  exact false_of_isNsCyclicPreferred (labelNsABD_le d a b) (labelNsABCD_le d a' b' c)
    (orbit_eq_iff.mp <| (orbit_eq_iff.mpr hN₃).trans (orbit_eq_iff.mpr hN₂).symm) h.2.2.2.1
    h'.2.2.2.2.1 h.2.2.2.2.2.1 h'.2.2.2.2.2.2.1 (hdih.of_mem_subgroupConjClass (orbit_eq_iff.mp <|
      (orbit_eq_iff.mpr hN₃).trans (orbit_eq_iff.mpr hK).symm))

lemma IsCanonicalSutherlandLabel.params_eq_of_cls_Ns
    (hL : IsCanonicalSutherlandLabel p H ⟨.Ns, ps, d⟩)
    (hL' : IsCanonicalSutherlandLabel p H ⟨.Ns, ps', d⟩) : ps = ps' := by
  have h : SutherlandGroupLabel.CanonicalParamsOf p H ⟨.Ns, ps, d⟩ := hL.2.2.2
  have h' : SutherlandGroupLabel.CanonicalParamsOf p H ⟨.Ns, ps', d⟩ := hL'.2.2.2
  rcases ps with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, ps⟩⟩⟩⟩
  · have hD : labelNsD p d ∈ subgroupConjClass p H := hL.2.2.1 (labelNsD p d) rfl
    rcases ps' with _ | ⟨a', _ | ⟨b', _ | ⟨c', _ | ⟨e', ps'⟩⟩⟩⟩
    · rfl
    · exact h'.elim
    · exact absurd hD h'.1
    · exact absurd hD h'.1
    · exact h'.elim
  · exact h.elim
  · rcases ps' with _ | ⟨a', _ | ⟨b', _ | ⟨c', _ | ⟨e', ps'⟩⟩⟩⟩
    · exact absurd (hL'.2.2.1 (labelNsD p d) rfl) h.1
    · exact h'.elim
    · rcases IsLexLeastPair.eq h.2 h'.2 with ⟨⟩
      rfl
    · exact (hL.false_of_Ns hL').elim
    · exact h'.elim
  · rcases ps' with _ | ⟨a', _ | ⟨b', _ | ⟨c', _ | ⟨e', ps'⟩⟩⟩⟩
    · exact absurd (hL'.2.2.1 (labelNsD p d) rfl) h.1
    · exact h'.elim
    · exact (hL'.false_of_Ns hL).elim
    · rcases IsLexLeastTriple.eq h.2 h'.2 with ⟨⟩
      rfl
    · exact h'.elim
  · exact h.elim

lemma IsCanonicalSutherlandLabel.params_eq_of_cls_Cn
    (hL : IsCanonicalSutherlandLabel p H ⟨.Cn, ps, d⟩)
    (hL' : IsCanonicalSutherlandLabel p H ⟨.Cn, ps', d⟩) : ps = ps' := by
  have h : SutherlandGroupLabel.CanonicalParamsOf p H ⟨.Cn, ps, d⟩ := hL.2.2.2
  have h' : SutherlandGroupLabel.CanonicalParamsOf p H ⟨.Cn, ps', d⟩ := hL'.2.2.2
  rcases ps with _ | ⟨a, _ | ⟨b, _ | ⟨c, ps⟩⟩⟩
  · rcases ps' with _ | ⟨a', _ | ⟨b', _ | ⟨c', ps'⟩⟩⟩
    · rfl
    · exact h'.elim
    · exact absurd (hL.2.2.1 (labelCnD p d) rfl) h'.1
    · exact h'.elim
  · exact h.elim
  · rcases ps' with _ | ⟨a', _ | ⟨b', _ | ⟨c', ps'⟩⟩⟩
    · exact absurd (hL'.2.2.1 (labelCnD p d) rfl) h.1
    · exact h'.elim
    · rcases IsLexLeastPair.eq h.2 h'.2 with ⟨⟩
      rfl
    · exact h'.elim
  · exact h.elim

lemma IsCanonicalSutherlandLabel.params_eq_of_cls_Nn
    (hL : IsCanonicalSutherlandLabel p H ⟨.Nn, ps, d⟩)
    (hL' : IsCanonicalSutherlandLabel p H ⟨.Nn, ps', d⟩) : ps = ps' := by
  have hp : p ≠ 2 := ne_two_of_hasSutherlandClass_Nn hL.1
  have h : SutherlandGroupLabel.CanonicalParamsOf p H ⟨.Nn, ps, d⟩ := hL.2.2.2
  have h' : SutherlandGroupLabel.CanonicalParamsOf p H ⟨.Nn, ps', d⟩ := hL'.2.2.2
  rcases ps with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨e, ps⟩⟩⟩⟩
  · have hD : labelNnD p d ∈ subgroupConjClass p H := hL.2.2.1 (labelNnD p d) rfl
    rcases ps' with _ | ⟨a', _ | ⟨b', _ | ⟨c', _ | ⟨e', ps'⟩⟩⟩⟩
    · rfl
    · exact h'.elim
    · exact absurd hD h'.1
    · exact absurd hD h'.1
    · exact h'.elim
  · exact h.elim
  · rcases ps' with _ | ⟨a', _ | ⟨b', _ | ⟨c', _ | ⟨e', ps'⟩⟩⟩⟩
    · exact absurd (hL'.2.2.1 (labelNnD p d) rfl) h.1
    · exact h'.elim
    · rcases IsLexLeastPair.eq h.2 h'.2 with ⟨⟩
      rfl
    · exact (hL.false_of_Nn hp hL').elim
    · exact h'.elim
  · rcases ps' with _ | ⟨a', _ | ⟨b', _ | ⟨c', _ | ⟨e', ps'⟩⟩⟩⟩
    · exact absurd (hL'.2.2.1 (labelNnD p d) rfl) h.1
    · exact h'.elim
    · exact (hL'.false_of_Nn hp hL).elim
    · rcases h.2.1.trans h'.2.1.symm with rfl
      rcases IsLexLeastPair.eq h.2.2 h'.2.2 with ⟨⟩
      rfl
    · exact h'.elim
  · exact h.elim

/-- **Sutherland's label of a subgroup of `GL₂(𝔽_p)` is unique** (LMFDB
`ec.galois_rep_modell_image`). -/
lemma IsCanonicalSutherlandLabel.eq {L L' : SutherlandGroupLabel}
    (hL : IsCanonicalSutherlandLabel p H L) (hL' : IsCanonicalSutherlandLabel p H L') : L = L' := by
  have hcls : L.cls = L'.cls := hL.1.eq hL'.1
  have hd : L.d = L'.d := hL.2.1.trans hL'.2.1.symm
  rcases L with ⟨S, ps, d⟩
  rcases L' with ⟨S', ps', d'⟩
  dsimp only at hcls hd
  subst hcls hd
  rcases eq_or_ne S .Cn with rfl | hCn
  · rw [hL.params_eq_of_cls_Cn hL']
  rcases eq_or_ne S .Ns with rfl | hNs
  · rw [hL.params_eq_of_cls_Ns hL']
  rcases eq_or_ne S .Nn with rfl | hNn
  · rw [hL.params_eq_of_cls_Nn hL']
  exact ((isCanonicalSutherlandLabel_iff_of_cls_ne hCn hNs hNn).mp hL).eq
    ((isCanonicalSutherlandLabel_iff_of_cls_ne hCn hNs hNn).mp hL') hNs hNn

end Matrix.GeneralLinearGroup
