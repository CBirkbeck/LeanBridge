import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.AutPmMuFinite
import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.EichlerOrderLevel

/-!
# A quaternion algebra over `ℚ` has more than one maximal order

Let `B` be a quaternion algebra over `ℚ`, a central simple `ℚ`-algebra of dimension `4`. Unlike a
number field, whose ring of integers is its only maximal order, `B` never has a unique maximal
order (LMFDB `shimcurve.order`): every quaternion algebra over `ℚ` has two different maximal orders.

An isomorphism of `ℚ`-algebras maps orders to orders and maximal orders to maximal orders; so does
the conjugation `x ↦ γ x γ⁻¹` by a unit `γ` of `B`. No order `O` is normalised by every unit of `B`:
for `γ` in the normaliser of `O`, conjugation by `γ` maps the lattice `O` onto itself, so its trace
`trd(γ)² / nrd(γ)` on `B` is an integer, while in `B ≅ (a, b / ℚ)` the unit `γ = 1 + s i` with
`s = 3 den(a)` has `trd(γ)² / nrd(γ) = 4 / (1 - a s²)`, where `a s² = 9 num(a) den(a)` is a nonzero
integer, so that `4 / (1 - a s²)` is a nonzero rational number of absolute value at most `1 / 2`.
Hence a maximal order has a conjugate different from it, which is again a maximal order.

Maximal orders exist: `(a, b / ℚ)` has the order spanned over `ℤ` by `1`, `d₁ i`, `d₂ j` and
`d₁ d₂ ij`, for the denominators `d₁`, `d₂` of `a`, `b`, as `(d₁ i)² = num(a) d₁` and
`(d₂ j)² = num(b) d₂` are integers, and every order lies in a maximal order
(`Subalgebra.exists_isMaximalQuaternionOrder_le`).

## Main results

* `QuaternionAlgebra.Basis.isQuaternionOrder_range_liftHom`: the `ℤ`-span of `1, i, j, k` for a
  quaternion basis of `B` with integral structure constants is an order when it spans `B` over `ℚ`.
* `Subalgebra.IsQuaternionOrder.map`: an isomorphism of `ℚ`-algebras maps orders to orders.
* `Subalgebra.IsMaximalQuaternionOrder.map`: an isomorphism of `ℚ`-algebras maps maximal orders to
  maximal orders; in particular a conjugate `γ O γ⁻¹` of a maximal order is a maximal order.
* `QuaternionAlgebra.exists_isQuaternionOrder` (LMFDB `shimcurve.order`): every quaternion algebra
  over `ℚ` has an order.
* `Subalgebra.exists_map_conj_ne`: no order of a quaternion algebra over `ℚ` is normalised by every
  unit.
* `Subalgebra.IsMaximalQuaternionOrder.exists_ne` (LMFDB `shimcurve.order`): a maximal order has a
  conjugate which is a different maximal order.
* `QuaternionAlgebra.not_existsUnique_isMaximalQuaternionOrder` (LMFDB `shimcurve.order`): there is
  never a unique maximal order in a quaternion algebra over `ℚ`.
* `QuaternionAlgebra.exists_isMaximalQuaternionOrder_ne` (LMFDB `shimcurve.order`): every quaternion
  algebra over `ℚ` has two different maximal orders.
-/

open Module QuaternionAlgebra

open scoped Quaternion

namespace QuaternionAlgebra.Basis

variable {B : Type*} [Ring B] {c₁ c₂ c₃ : ℤ} (q : Basis B c₁ c₂ c₃)

lemma i_mem_range_liftHom : q.i ∈ q.liftHom.range := by
  rw [range_liftHom]
  exact Algebra.subset_adjoin (by simp)

variable [Algebra ℚ B] in
/-- **The `ℤ`-span of a quaternion basis with integral structure constants is an order** when it
spans `B` over `ℚ`: for `i`, `j`, `k` in a `ℚ`-algebra `B` with `i² = c₁ + c₂ i`, `j² = c₃`,
`ij = k` and `ji = c₂ j - k` for integers `c₁`, `c₂`, `c₃`, the image `ℤ + ℤi + ℤj + ℤk` of
`ℍ[ℤ,c₁,c₂,c₃]` in `B` is a subring and a finitely generated `ℤ`-module. -/
lemma isQuaternionOrder_range_liftHom (h : Submodule.span ℚ {1, q.i, q.j, q.k} = ⊤) :
    q.liftHom.range.IsQuaternionOrder := by
  have hr : Subalgebra.toSubmodule q.liftHom.range = Submodule.map q.liftHom.toLinearMap ⊤ := by
    ext
    simp only [Subalgebra.mem_toSubmodule, AlgHom.mem_range, Submodule.mem_map, Submodule.mem_top,
      true_and, AlgHom.toLinearMap_apply]
  refine ⟨hr ▸ Finite.fg_top.map _,
    eq_top_iff.mpr <| h.symm.trans_le <| Submodule.span_mono ?_⟩
  rw [range_liftHom]
  rintro x (rfl | rfl | rfl | rfl)
  · exact one_mem (Algebra.adjoin ℤ {q.i, q.j, q.k})
  all_goals exact Algebra.subset_adjoin (by simp)

end QuaternionAlgebra.Basis

namespace Subalgebra

variable {B C : Type*} [Ring B] [Algebra ℚ B] [Ring C] [Algebra ℚ C] (e : B ≃ₐ[ℚ] C)
  {O : Subalgebra ℤ B}

/-- **An isomorphism of `ℚ`-algebras maps orders to orders.** -/
lemma IsQuaternionOrder.map (hO : O.IsQuaternionOrder) :
    (O.map ((e : B →ₐ[ℚ] C).restrictScalars ℤ)).IsQuaternionOrder := by
  refine ⟨by rw [map_toSubmodule]; exact hO.fg.map _, ?_⟩
  have h : (toSubmodule (O.map ((e : B →ₐ[ℚ] C).restrictScalars ℤ)) : Set C) =
      e.toLinearMap '' (toSubmodule O : Set B) := by
    simp
  rw [h, Submodule.span_image, hO.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact e.surjective

/-- **An isomorphism of `ℚ`-algebras maps maximal orders to maximal orders**; for instance, the
conjugate `γ O γ⁻¹` of a maximal order `O` by a unit `γ`, which is the image of `O` under the
automorphism `MulSemiringAction.toAlgEquiv ℚ B (ConjAct.toConjAct γ)`, is a maximal order. -/
lemma IsMaximalQuaternionOrder.map (hO : O.IsMaximalQuaternionOrder) :
    (O.map ((e : B →ₐ[ℚ] C).restrictScalars ℤ)).IsMaximalQuaternionOrder := by
  refine ⟨hO.prop.map e, fun O' hO' hle x hx ↦ ?_⟩
  have h : O'.map ((e.symm : C →ₐ[ℚ] B).restrictScalars ℤ) ≤ O :=
    hO.le_of_ge (hO'.map e.symm) fun y hy ↦ ⟨e y, hle ⟨y, hy, rfl⟩, e.symm_apply_apply y⟩
  exact ⟨e.symm x, h ⟨x, hx, rfl⟩, e.apply_symm_apply x⟩

end Subalgebra

namespace QuaternionAlgebra

variable (B : Type*) [Ring B] [Algebra ℚ B] [Algebra.IsCentral ℚ B] [IsSimpleRing B]

/-- **Every quaternion algebra over `ℚ` has an order** (LMFDB `shimcurve.order`): if
`B ≅ (a, b / ℚ)`, the `ℤ`-span of `1`, `d₁ i`, `d₂ j` and `d₁ d₂ ij` is an order, for the
denominators `d₁`, `d₂` of `a`, `b`. -/
lemma exists_isQuaternionOrder (h4 : finrank ℚ B = 4) :
    ∃ O : Subalgebra ℤ B, O.IsQuaternionOrder := by
  rcases exists_nonempty_algEquiv_of_finrank_eq_four (by simp) h4 with ⟨a, b, ⟨e⟩⟩
  let q : Basis ℍ[ℚ,(a : ℚ),(b : ℚ)] ((a : ℚ).num * (a : ℚ).den) 0 ((b : ℚ).num * (b : ℚ).den) :=
    { i := ⟨0, (a : ℚ).den, 0, 0⟩
      j := ⟨0, 0, (b : ℚ).den, 0⟩
      k := ⟨0, 0, 0, (a : ℚ).den * (b : ℚ).den⟩
      i_mul_i := by ext <;> simp
      j_mul_j := by ext <;> simp
      i_mul_j := by ext <;> simp
      j_mul_i := by ext <;> simp [mul_comm] }
  refine ⟨_, (q.isQuaternionOrder_range_liftHom (eq_top_iff.mpr fun x _ ↦ ?_)).map e⟩
  have hx : x = x.re • 1 + (x.imI / (a : ℚ).den) • q.i + (x.imJ / (b : ℚ).den) • q.j +
      (x.imK / ((a : ℚ).den * (b : ℚ).den)) • q.k := by
    ext <;> simp [q]
  rw [hx]
  refine add_mem (add_mem (add_mem ?_ ?_) ?_) ?_
  all_goals exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

lemma exists_units_forall_sq_reducedTrace_div_ne (h4 : finrank ℚ B = 4) :
    ∃ γ : Bˣ, ∀ z : ℤ, reducedTrace B (γ : B) ^ 2 / reducedNorm B (γ : B) ≠ z := by
  rcases exists_nonempty_algEquiv_of_finrank_eq_four (by simp) h4 with ⟨a, b, ⟨e⟩⟩
  have hw : (a : ℚ).num * (a : ℚ).den ≠ 0 :=
    mul_ne_zero (Rat.num_ne_zero.mpr a.ne_zero) (Nat.cast_ne_zero.mpr (a : ℚ).den_ne_zero)
  let s : ℚ := 3 * (a : ℚ).den
  have hs : 1 - (a : ℚ) * s ^ 2 = ((1 - 9 * ((a : ℚ).num * (a : ℚ).den) : ℤ) : ℚ) := by
    push_cast
    linear_combination (-9 * ((a : ℚ).den : ℚ)) * Rat.mul_den_eq_num (a : ℚ)
  have hn : 1 - (a : ℚ) * s ^ 2 ≠ 0 := by
    rw [hs, Int.cast_ne_zero]
    omega
  let u : ℍ[ℚ,(a : ℚ),(b : ℚ)] := ⟨1, s, 0, 0⟩
  let v : ℍ[ℚ,(a : ℚ),(b : ℚ)] := (1 - (a : ℚ) * s ^ 2)⁻¹ • ⟨1, -s, 0, 0⟩
  have huv : u * v = 1 := by
    ext <;> simp [u, v]
    · field_simp
      ring1
    · ring1
  have hvu : v * u = 1 := by
    ext <;> simp [u, v]
    field_simp
    ring1
  refine ⟨⟨e u, e v, by rw [← map_mul, huv, map_one], by rw [← map_mul, hvu, map_one]⟩,
    fun z hz ↦ ?_⟩
  have hN : (u * star u).re = 1 - (a : ℚ) * s ^ 2 := by
    simp
    ring1
  rw [Units.val_mk, reducedTrace_algEquiv, reducedNorm_algEquiv, reducedTrace_quaternionAlgebra,
    reducedNorm_quaternionAlgebra, hN, div_eq_iff hn, hs] at hz
  have hz' : (1 - 9 * ((a : ℚ).num * (a : ℚ).den)) * z = 4 := by
    have h : (((1 - 9 * ((a : ℚ).num * (a : ℚ).den)) * z : ℤ) : ℚ) = ((4 : ℤ) : ℚ) := by
      push_cast at hz ⊢
      linear_combination -hz
    exact_mod_cast h
  have hd : 1 - 9 * ((a : ℚ).num * (a : ℚ).den) ∣ 4 := Dvd.intro z hz'
  have h₁ : 1 - 9 * ((a : ℚ).num * (a : ℚ).den) ≤ 4 := Int.le_of_dvd four_pos hd
  have h₂ : -(1 - 9 * ((a : ℚ).num * (a : ℚ).den)) ≤ 4 := Int.le_of_dvd four_pos (neg_dvd.mpr hd)
  omega

end QuaternionAlgebra

namespace Subalgebra

variable {B : Type*} [Ring B] [Algebra ℚ B] [Algebra.IsCentral ℚ B] [IsSimpleRing B]
  {O : Subalgebra ℤ B}

/-- **No order of a quaternion algebra over `ℚ` is normalised by every unit**: some conjugate
`γ O γ⁻¹` of an order `O` differs from `O`, since `trd(γ)² / nrd(γ)` is an integer for `γ` in the
normaliser of `O` but not for every unit `γ`. -/
lemma exists_map_conj_ne (h4 : finrank ℚ B = 4) (hO : O.IsQuaternionOrder) :
    ∃ γ : Bˣ, O.map (MulSemiringAction.toAlgHom ℤ B (ConjAct.toConjAct γ)) ≠ O := by
  rcases exists_units_forall_sq_reducedTrace_div_ne B h4 with ⟨γ, hγ⟩
  refine ⟨γ, fun h ↦ ?_⟩
  have hmem : γ ∈ O.unitsNormalizer := fun x ↦ by
    refine ⟨fun hx ↦ h ▸ ⟨x, hx, by simp [ConjAct.units_smul_def]⟩, fun hx ↦ ?_⟩
    rw [← h] at hx
    rcases hx with ⟨y, hy, hyx⟩
    simp [ConjAct.units_smul_def] at hyx
    exact hyx ▸ hy
  rcases exists_sq_reducedTrace_div_eq_intCast h4 hO hmem with ⟨z, hz⟩
  exact hγ z hz

/-- **A maximal order is not the only maximal order** (LMFDB `shimcurve.order`): a maximal order `O`
of a quaternion algebra over `ℚ` has a conjugate `γ O γ⁻¹` different from `O`, which is again a
maximal order. -/
lemma IsMaximalQuaternionOrder.exists_ne (h4 : finrank ℚ B = 4) (hO : O.IsMaximalQuaternionOrder) :
    ∃ O' : Subalgebra ℤ B, O'.IsMaximalQuaternionOrder ∧ O' ≠ O := by
  rcases exists_map_conj_ne h4 hO.prop with ⟨γ, hγ⟩
  exact ⟨O.map (MulSemiringAction.toAlgHom ℤ B (ConjAct.toConjAct γ)),
    hO.map (MulSemiringAction.toAlgEquiv ℚ B (ConjAct.toConjAct γ)), hγ⟩

end Subalgebra

namespace QuaternionAlgebra

variable (B : Type*) [Ring B] [Algebra ℚ B] [Algebra.IsCentral ℚ B] [IsSimpleRing B]

/-- **There is never a unique maximal order in a quaternion algebra over `ℚ`** (LMFDB
`shimcurve.order`), unlike in a number field. -/
lemma not_existsUnique_isMaximalQuaternionOrder (h4 : finrank ℚ B = 4) :
    ¬∃! O : Subalgebra ℤ B, O.IsMaximalQuaternionOrder := by
  rintro ⟨O, hO, h⟩
  rcases hO.exists_ne h4 with ⟨O', hO', hne⟩
  exact hne (h O' hO')

/-- **Every quaternion algebra over `ℚ` has two different maximal orders** (LMFDB
`shimcurve.order`): it has an order, which lies in a maximal order, and a maximal order has a
conjugate which is a different maximal order. -/
lemma exists_isMaximalQuaternionOrder_ne (h4 : finrank ℚ B = 4) : ∃ O₁ O₂ : Subalgebra ℤ B,
    O₁.IsMaximalQuaternionOrder ∧ O₂.IsMaximalQuaternionOrder ∧ O₁ ≠ O₂ := by
  rcases exists_isQuaternionOrder B h4 with ⟨O, hO⟩
  rcases Subalgebra.exists_isMaximalQuaternionOrder_le h4 hO with ⟨O₁, h₁, -⟩
  rcases h₁.exists_ne h4 with ⟨O₂, h₂, hne⟩
  exact ⟨O₁, O₂, h₁, h₂, hne.symm⟩

end QuaternionAlgebra
