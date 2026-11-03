import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.GL2LabelUniqueness
import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.GL2TracePairs

/-!
# Lifts to `GL₂(𝔽_p)` of generating pairs of a projective image

A subgroup `K` of `GL₂(𝔽_p)` with image in `PGL₂(𝔽_p)` isomorphic to a group `T` is determined by
its scalars and the lifts to `K` of a generating pair of `T`. This file proves the facts on such
lifts that Sutherland's Lemma 3.21 (arXiv:1504.07618v7) needs: the relations between the trace and
the determinant of a matrix of order `2`, `3`, `4` or `5` modulo scalars, the fact that `-1` lies in
`K` when `T` contains a Klein group, and that two subgroups with the same scalars and with conjugate
lifts of a generating pair are conjugate.

## Main results

* `Matrix.GeneralLinearGroup.trace_eq_zero_of_sq_mem_center`,
  `Matrix.GeneralLinearGroup.trace_mul_self_eq_det_of_pow_three_mem_center`,
  `Matrix.GeneralLinearGroup.trace_mul_self_eq_two_mul_det_of_pow_four_mem_center`,
  `Matrix.GeneralLinearGroup.quartic_of_pow_five_mem_center`: the relations for orders `2`, `3`,
  `4`, `5`.
* `Matrix.GeneralLinearGroup.le_of_lifts_mem`: a subgroup containing the scalars of `K` and lifts of
  a generating pair of the projective image of `K` contains `K`.
* `Matrix.GeneralLinearGroup.neg_one_mem_of_lifts`: if the projective image of `K` contains a Klein
  group, then `-1 ∈ K`.
* `Matrix.GeneralLinearGroup.mem_subgroupConjClass_of_lifts`: subgroups with the same scalars and
  conjugate lifts of a generating pair of their projective images are conjugate.
-/

open Matrix MulAction TauCeti

open scoped MatrixGroups Pointwise

namespace Matrix.GeneralLinearGroup

variable {p : ℕ} [Fact p.Prime] {K K' : Subgroup (GL (Fin 2) (ZMod p))} {T T' : Type*} [Group T]
  [Group T'] (e : projectiveImage K ≃* T) (e' : projectiveImage K' ≃* T') {s t : T} {s' t' : T'}
  {S X S' X' : GL (Fin 2) (ZMod p)}

variable (t) in
lemma exists_lift : ∃ x ∈ K, ProjGenLinGroup.mk x = (e.symm t : PGL(Fin 2, ZMod p)) :=
  (e.symm t).2

lemma mk_mul_of_lift (hS : ProjGenLinGroup.mk S = (e.symm s : PGL(Fin 2, ZMod p)))
    (hX : ProjGenLinGroup.mk X = (e.symm t : PGL(Fin 2, ZMod p))) :
    ProjGenLinGroup.mk (S * X) = (e.symm (s * t) : PGL(Fin 2, ZMod p)) := by
  rw [map_mul, hS, hX, map_mul, Subgroup.coe_mul]

lemma mk_inv_of_lift (hS : ProjGenLinGroup.mk S = (e.symm s : PGL(Fin 2, ZMod p))) :
    ProjGenLinGroup.mk S⁻¹ = (e.symm s⁻¹ : PGL(Fin 2, ZMod p)) := by
  rw [map_inv, hS, map_inv, Subgroup.coe_inv]

lemma pow_mem_center_of_lift (hX : ProjGenLinGroup.mk X = (e.symm t : PGL(Fin 2, ZMod p))) {n : ℕ}
    (ht : t ^ n = 1) : X ^ n ∈ Subgroup.center (GL (Fin 2) (ZMod p)) := by
  rw [← ProjGenLinGroup.mk_eq_one, map_pow, hX, ← Subgroup.coe_pow, ← map_pow, ht, map_one,
    Subgroup.coe_one]

lemma notMem_center_of_lift (hX : ProjGenLinGroup.mk X = (e.symm t : PGL(Fin 2, ZMod p)))
    (ht : t ≠ 1) : X ∉ Subgroup.center (GL (Fin 2) (ZMod p)) := fun h ↦ ht <| by
  have h₁ : (e.symm t : PGL(Fin 2, ZMod p)) = 1 := hX.symm.trans (ProjGenLinGroup.mk_eq_one.mpr h)
  exact e.symm.map_eq_one_iff.mp (Subtype.ext h₁)

lemma exists_lift_det_eq_one (hs : ∃ a b : T, a * b * a⁻¹ * b⁻¹ = s) :
    ∃ x ∈ K, ProjGenLinGroup.mk x = (e.symm s : PGL(Fin 2, ZMod p)) ∧ det x = 1 := by
  rcases hs with ⟨a, b, rfl⟩
  rcases exists_lift e a with ⟨A, hA, hmA⟩
  rcases exists_lift e b with ⟨B, hB, hmB⟩
  refine ⟨A * B * A⁻¹ * B⁻¹, mul_mem (mul_mem (mul_mem hA hB) (inv_mem hA)) (inv_mem hB),
    mk_mul_of_lift e (mk_mul_of_lift e (mk_mul_of_lift e hmA hmB) (mk_inv_of_lift e hmA))
      (mk_inv_of_lift e hmB), ?_⟩
  simp

lemma mk_eq_mk_of_lift_eq (hS : ProjGenLinGroup.mk S = (e.symm s : PGL(Fin 2, ZMod p)))
    {u : (ZMod p)ˣ} :
    ProjGenLinGroup.mk (S * scalar (Fin 2) u) = (e.symm s : PGL(Fin 2, ZMod p)) := by
  rw [map_mul, hS, ProjGenLinGroup.mk_scalar, mul_one]

lemma eq_zero_of_smul_add_smul_one_eq {α β c : ZMod p}
    (hX : X ∉ Subgroup.center (GL (Fin 2) (ZMod p))) (h : α • X.val + β • 1 = c • 1) : α = 0 := by
  by_contra hα
  refine hX (mem_center_iff_val_mem_range_scalar.mpr ⟨α⁻¹ * (c - β), ?_⟩)
  have h₁ : α • X.val = (c - β) • 1 := by
    rw [sub_smul, ← h, add_sub_cancel_right]
  have h₂ : X.val = (α⁻¹ * (c - β)) • 1 := by
    rw [mul_smul, ← h₁, smul_smul, inv_mul_cancel₀ hα, one_smul]
  rw [h₂]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- **A non-scalar matrix `X` with `X²` scalar has trace `0`.** -/
lemma trace_eq_zero_of_sq_mem_center (hX : X ∉ Subgroup.center (GL (Fin 2) (ZMod p)))
    (h : X ^ 2 ∈ Subgroup.center (GL (Fin 2) (ZMod p))) : X.val.trace = 0 := by
  have h₁ : X.val ^ 2 = (X.val ^ 2) 0 0 • 1 := ProjGenLinGroup.val_pow_eq_smul_one_of_field h
  nth_rw 1 [sq_eq_trace_smul_sub_det_smul_one_fin_two, sub_eq_add_neg, ← neg_smul] at h₁
  exact eq_zero_of_smul_add_smul_one_eq hX h₁

/-- **A non-scalar matrix `X` with `X³` scalar has `(tr X)² = det X`.** -/
lemma trace_mul_self_eq_det_of_pow_three_mem_center (hX : X ∉ Subgroup.center (GL (Fin 2) (ZMod p)))
    (h : X ^ 3 ∈ Subgroup.center (GL (Fin 2) (ZMod p))) :
    X.val.trace * X.val.trace = X.val.det := by
  have h₁ : X.val ^ 3 = (X.val ^ 3) 0 0 • 1 := ProjGenLinGroup.val_pow_eq_smul_one_of_field h
  have h₂ : X.val ^ 3 = (X.val.trace * X.val.trace - X.val.det) • X.val +
      (-(X.val.trace * X.val.det)) • 1 := by
    rw [pow_add_two_fin_two _ 1, pow_add_two_fin_two _ 0, pow_one, pow_zero]
    module
  nth_rw 1 [h₂] at h₁
  exact sub_eq_zero.mp (eq_zero_of_smul_add_smul_one_eq hX h₁)

/-- **A matrix `X` with `X⁴` scalar and `X²` not scalar has `(tr X)² = 2 det X`.** -/
lemma trace_mul_self_eq_two_mul_det_of_pow_four_mem_center
    (hX : X ^ 2 ∉ Subgroup.center (GL (Fin 2) (ZMod p)))
    (h : X ^ 4 ∈ Subgroup.center (GL (Fin 2) (ZMod p))) :
    X.val.trace * X.val.trace = 2 * X.val.det := by
  have h₁ : (X ^ 2).val.trace = 0 := trace_eq_zero_of_sq_mem_center hX (by rwa [← pow_mul])
  rw [Units.val_pow_eq_pow_val, sq_eq_trace_smul_sub_det_smul_one_fin_two, trace_sub, trace_smul,
    trace_smul, trace_one, Fintype.card_fin, smul_eq_mul, smul_eq_mul] at h₁
  push_cast at h₁
  linear_combination h₁

/-- **A non-scalar matrix `X` with `X⁵` scalar has `(tr X)⁴ - 3 (tr X)² det X + (det X)² = 0`.** -/
lemma quartic_of_pow_five_mem_center (hX : X ∉ Subgroup.center (GL (Fin 2) (ZMod p)))
    (h : X ^ 5 ∈ Subgroup.center (GL (Fin 2) (ZMod p))) :
    X.val.trace ^ 4 - 3 * X.val.trace ^ 2 * X.val.det + X.val.det ^ 2 = 0 := by
  have h₁ : X.val ^ 5 = (X.val ^ 5) 0 0 • 1 := ProjGenLinGroup.val_pow_eq_smul_one_of_field h
  have h₂ : X.val ^ 5 = (X.val.trace ^ 4 - 3 * X.val.trace ^ 2 * X.val.det + X.val.det ^ 2) •
      X.val + (-(X.val.trace ^ 3 * X.val.det) + 2 * X.val.trace * X.val.det ^ 2) • 1 := by
    rw [pow_add_two_fin_two _ 3, pow_add_two_fin_two _ 2, pow_add_two_fin_two _ 1,
      pow_add_two_fin_two _ 0, pow_one, pow_zero]
    module
  nth_rw 1 [h₂] at h₁
  exact eq_zero_of_smul_add_smul_one_eq hX h₁

/-- **A subgroup containing the scalars of `K` and lifts in `K` of a generating pair of the
projective image of `K` contains `K`.** -/
lemma le_of_lifts_mem {M : Subgroup (GL (Fin 2) (ZMod p))}
    (hgen : Subgroup.closure ({s, t} : Set T) = ⊤) (hZ : K ⊓ Subgroup.center _ ≤ M) (hSK : S ∈ K)
    (hXK : X ∈ K) (hSM : S ∈ M) (hXM : X ∈ M)
    (hmS : ProjGenLinGroup.mk S = (e.symm s : PGL(Fin 2, ZMod p)))
    (hmX : ProjGenLinGroup.mk X = (e.symm t : PGL(Fin 2, ZMod p))) : K ≤ M := by
  let W : Subgroup PGL(Fin 2, ZMod p) := (M ⊓ K).map ProjGenLinGroup.mk
  let Y : Subgroup T := (W.comap (projectiveImage K).subtype).comap e.symm.toMonoidHom
  have hY : Y = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact ⟨S, Subgroup.mem_inf.mpr ⟨hSM, hSK⟩, hmS⟩
    · exact ⟨X, Subgroup.mem_inf.mpr ⟨hXM, hXK⟩, hmX⟩
  intro h hh
  have hyY : e ⟨ProjGenLinGroup.mk h, Subgroup.mem_map_of_mem _ hh⟩ ∈ Y := hY ▸ Subgroup.mem_top _
  have hyW : ProjGenLinGroup.mk h ∈ W := by
    have h₁ : (e.symm (e ⟨ProjGenLinGroup.mk h, Subgroup.mem_map_of_mem _ hh⟩) :
        PGL(Fin 2, ZMod p)) ∈ W := hyY
    rwa [MulEquiv.symm_apply_apply] at h₁
  rcases hyW with ⟨h₁, hh₁, hh₁h⟩
  rcases Subgroup.mem_inf.mp hh₁ with ⟨hh₁K', hh₁K⟩
  rcases ProjGenLinGroup.mk_eq_mk_iff.mp hh₁h with ⟨u, hu⟩
  have huK : scalar (Fin 2) u ∈ K ⊓ Subgroup.center _ := by
    refine Subgroup.mem_inf.mpr ⟨?_, scalar_mem_center u⟩
    have h₂ : scalar (Fin 2) u = h₁⁻¹ * h := by
      rw [← hu, inv_mul_cancel_left]
    rw [h₂]
    exact mul_mem (inv_mem hh₁K) hh
  rw [← hu]
  exact mul_mem hh₁K' (hZ huK)

/-- **If the projective image of `K` contains a Klein group, then `-1 ∈ K`**, for odd `p`: lifts
of two commuting involutions have trace `0`, and commute only up to a sign; if they commuted, their
product would be scalar, and the involutions would be equal. -/
lemma neg_one_mem_of_lifts (f : projectiveImage K ≃* T) (hp : p ≠ 2) {s₁ s₂ : T} (hs₂ : s₂ ^ 2 = 1)
    (hs₁ : s₁ ^ 2 = 1) (hc : s₁ * s₂ = s₂ * s₁) (hne₁ : s₁ ≠ 1) (hne₂ : s₂ ≠ 1) (hne : s₁ ≠ s₂) :
    (-1 : GL (Fin 2) (ZMod p)) ∈ K := by
  rcases exists_lift f s₁ with ⟨Y₁, hY₁, hm₁⟩
  rcases exists_lift f s₂ with ⟨Y₂, hY₂, hm₂⟩
  have htr₁ : Y₁.val.trace = 0 := trace_eq_zero_of_sq_mem_center (notMem_center_of_lift f hm₁ hne₁)
    (pow_mem_center_of_lift f hm₁ hs₁)
  have htr₂ : Y₂.val.trace = 0 := trace_eq_zero_of_sq_mem_center (notMem_center_of_lift f hm₂ hne₂)
    (pow_mem_center_of_lift f hm₂ hs₂)
  have hcomm : Y₁ * Y₂ * Y₁⁻¹ * Y₂⁻¹ ∈ K :=
    mul_mem (mul_mem (mul_mem hY₁ hY₂) (inv_mem hY₁)) (inv_mem hY₂)
  have hmc : ProjGenLinGroup.mk (Y₁ * Y₂ * Y₁⁻¹ * Y₂⁻¹) = 1 := by
    rw [mk_mul_of_lift f (mk_mul_of_lift f (mk_mul_of_lift f hm₁ hm₂) (mk_inv_of_lift f hm₁))
      (mk_inv_of_lift f hm₂), hc, mul_inv_cancel_right, mul_inv_cancel, map_one, Subgroup.coe_one]
  rcases eq_scalar_of_mem_center (ProjGenLinGroup.mk_eq_one.mp hmc) with ⟨c, hcs⟩
  have hdetc : ((c : (ZMod p)ˣ) : ZMod p) * c = 1 := by
    have h₁ : det (Y₁ * Y₂ * Y₁⁻¹ * Y₂⁻¹) = det (scalar (Fin 2) c) := congrArg det hcs
    rw [det_scalar, Fintype.card_fin] at h₁
    have h₂ : c ^ 2 = 1 := by
      rw [← h₁]
      simp
    rw [← Units.val_mul, ← sq, h₂, Units.val_one]
  rcases mul_self_eq_one_iff.mp hdetc with hc₁ | hc₁
  · exfalso
    have hc1 : c = 1 := Units.ext hc₁
    rw [hc1, map_one] at hcs
    have hYY : Y₁ * Y₂ = Y₂ * Y₁ := by
      have h₁ : Y₁ * Y₂ * Y₁⁻¹ = Y₂ := by
        rw [← mul_inv_eq_one (a := Y₁ * Y₂ * Y₁⁻¹), hcs]
      rw [← h₁, inv_mul_cancel_right, h₁]
    have hsum : Y₁.val * Y₂.val + Y₂.val * Y₁.val = (Y₁.val * Y₂.val).trace • 1 :=
      mul_add_mul_eq_of_trace_eq_zero htr₁ htr₂
    rw [← Units.val_mul, ← Units.val_mul, ← hYY, Units.val_mul, ← two_smul (ZMod p)] at hsum
    have h2 : (2 : ZMod p) ≠ 0 := two_ne_zero_of_ne_two p hp
    have hcen : Y₁ * Y₂ ∈ Subgroup.center (GL (Fin 2) (ZMod p)) := by
      refine mem_center_iff_val_mem_range_scalar.mpr ⟨2⁻¹ * (Y₁.val * Y₂.val).trace, ?_⟩
      have h₃ : (Y₁ * Y₂).val = (2⁻¹ * (Y₁.val * Y₂.val).trace) • 1 := by
        rw [mul_smul, ← hsum, smul_smul, inv_mul_cancel₀ h2, one_smul, Units.val_mul]
      rw [h₃]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
    have h₄ : ProjGenLinGroup.mk (Y₁ * Y₂) = 1 := ProjGenLinGroup.mk_eq_one.mpr hcen
    rw [mk_mul_of_lift f hm₁ hm₂] at h₄
    have h₅ : s₁ * s₂ = 1 := f.symm.map_eq_one_iff.mp (Subtype.ext h₄)
    have h₆ : s₂ * s₂ = 1 := by
      rwa [← sq]
    exact hne (mul_right_cancel (h₅.trans h₆.symm))
  · have hcm : c = -1 := Units.ext (by rw [hc₁, Units.val_neg, Units.val_one])
    rw [hcm, scalar_neg_one] at hcs
    exact hcs ▸ hcomm

/-- **Subgroups with the same scalars and conjugate lifts of a generating pair of their projective
images are conjugate.** -/
lemma mem_subgroupConjClass_of_lifts (hgen : Subgroup.closure ({s, t} : Set T) = ⊤)
    (hgen' : Subgroup.closure ({s', t'} : Set T') = ⊤)
    (hZ : K ⊓ Subgroup.center _ = K' ⊓ Subgroup.center _) (hSK : S ∈ K) (hXK : X ∈ K)
    (hS'K : S' ∈ K') (hX'K : X' ∈ K') (hmS : ProjGenLinGroup.mk S = (e.symm s : PGL(Fin 2, ZMod p)))
    (hmX : ProjGenLinGroup.mk X = (e.symm t : PGL(Fin 2, ZMod p)))
    (hmS' : ProjGenLinGroup.mk S' = (e'.symm s' : PGL(Fin 2, ZMod p)))
    (hmX' : ProjGenLinGroup.mk X' = (e'.symm t' : PGL(Fin 2, ZMod p))) {g : GL (Fin 2) (ZMod p)}
    (hgS : g * S = S' * g) (hgX : g * X = X' * g) : K' ∈ subgroupConjClass p K := by
  have hconj {x y : GL (Fin 2) (ZMod p)} (h : g * x = y * g) : MulAut.conj g x = y := by
    rw [MulAut.conj_apply, h, mul_inv_cancel_right]
  have hconj' {x y : GL (Fin 2) (ZMod p)} (h : g * x = y * g) : MulAut.conj g⁻¹ y = x := by
    rw [MulAut.conj_apply, inv_inv, mul_assoc, ← h, inv_mul_cancel_left]
  have hle₁ : K ≤ K'.comap (MulAut.conj g).toMonoidHom := le_of_lifts_mem e hgen (fun z hz ↦ by
    rcases eq_scalar_of_mem_center (Subgroup.mem_inf.mp hz).2 with ⟨u, rfl⟩
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, mulAut_conj_scalar]
    exact (Subgroup.mem_inf.mp (hZ ▸ hz)).1) hSK hXK (by
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, hconj hgS]
      exact hS'K) (by
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, hconj hgX]
      exact hX'K) hmS hmX
  have hle₂ : K' ≤ K.comap (MulAut.conj g⁻¹).toMonoidHom := le_of_lifts_mem e' hgen' (fun z hz ↦ by
    rcases eq_scalar_of_mem_center (Subgroup.mem_inf.mp hz).2 with ⟨u, rfl⟩
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, mulAut_conj_scalar]
    exact (Subgroup.mem_inf.mp (hZ.symm ▸ hz)).1) hS'K hX'K (by
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, hconj' hgS]
      exact hSK) (by
      rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, hconj' hgX]
      exact hXK) hmS' hmX'
  have heq : K' = K.map (MulAut.conj g).toMonoidHom := by
    refine le_antisymm (fun x hx ↦ ?_) (Subgroup.map_le_iff_le_comap.mpr hle₁)
    refine ⟨MulAut.conj g⁻¹ x, hle₂ hx, ?_⟩
    simp [mul_assoc]
  rw [heq]
  exact map_conj_mem_subgroupConjClass K g

end Matrix.GeneralLinearGroup
