import TauCeti.Algebra.Module.Lattice
import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.CompletedUnitsProfinite
import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.QuaternionOrderDiscriminant
import LeanBridge.ForMathlib.NumberTheory.ShimuraCurve.QuaternionRamification

/-!
# The index of a suborder, maximal orders, and the level of an Eichler order

Let `B` be a quaternion algebra over `ℚ`, a central simple `ℚ`-algebra of dimension `4`. For orders
`O ⊆ O'` of `B` the discriminants differ by the square of the index: `disc(O) = [O' : O]² disc(O')`,
so `discrd(O) = [O' : O] discrd(O')`, since a `ℤ`-basis of `O` is obtained from one of `O'` by an
integral matrix of determinant `±[O' : O]`. As the reduced discriminant is a positive integer, an
order lies in an order of least reduced discriminant above it, which is maximal: every order lies
in a maximal order. An Eichler order, the intersection of two maximal orders (LMFDB
`shimcurve.eichler`), is an order.

Over `ℚ`, LMFDB `shimcurve.eichler` states that the reduced discriminant of an Eichler order is
`disc(B) M` with `M` coprime to `disc(B)`, the level `M` of the order. The level is unique when it
exists, and it exists exactly when every prime at which `B` ramifies divides `discrd(O)` exactly
once, as `disc(B)` is the product of the ramified primes. That every Eichler order has this
property, from the local structure of Eichler orders (maximal at the ramified primes, where
`B ⊗ ℚ_p` is a division algebra with a unique maximal order of reduced discriminant `p`), is not
proved here. When no prime ramifies, as for `M₂(ℚ)`, every Eichler order has a level, its reduced
discriminant.

## Main results

* `Subalgebra.quaternionDiscrd_eq_relIndex_mul`: `discrd(O) = [O' : O] discrd(O')` for orders
  `O ⊆ O'`.
* `Subalgebra.exists_isMaximalQuaternionOrder_le`: every order lies in a maximal order.
* `Subalgebra.IsEichlerOrder.isQuaternionOrder` (LMFDB `shimcurve.eichler`): an Eichler order is an
  order.
* `Subalgebra.IsEichlerOrderOfLevel.unique` (LMFDB `shimcurve.eichler`): the level of an Eichler
  order is unique.
* `Subalgebra.exists_isEichlerOrderOfLevel_iff` (LMFDB `shimcurve.eichler`): an Eichler order has a
  level exactly when every ramified prime divides its reduced discriminant exactly once.
* `Subalgebra.exists_isEichlerOrderOfLevel_of_discriminant_eq_one` (LMFDB `shimcurve.eichler`):
  when `disc(B) = 1`, every Eichler order has a level.
* `QuaternionAlgebra.discriminant_matrix`: `M₂(ℚ)` is ramified at no prime.
* `Subalgebra.exists_isEichlerOrder_matrix` (LMFDB `shimcurve.eichler`): `M₂(ℚ)` has an Eichler
  order.
* `Subalgebra.exists_isEichlerOrderOfLevel_matrix` (LMFDB `shimcurve.eichler`): every Eichler order
  of `M₂(ℚ)` has a level.
-/

open Module QuaternionAlgebra TauCeti Submodule

open scoped TensorProduct

namespace QuaternionAlgebra

variable (B : Type*) [Ring B] [Algebra ℚ B]

lemma discriminant_ne_zero : discriminant B ≠ 0 :=
  finprod_ne_zero fun p ↦ by
    split_ifs
    exacts [p.prop.ne_zero, one_ne_zero]

/-- **`M₂(ℚ)` is ramified at no prime**, so its discriminant is `1`: `ℚ_p ⊗ M₂(ℚ)` has the nonzero
zero divisor `1 ⊗ E₁₁`. -/
lemma discriminant_matrix : discriminant (Matrix (Fin 2) (Fin 2) ℚ) = 1 := by
  refine finprod_eq_one_of_forall_eq_one fun p ↦ ite_eq_right fun h ↦ ?_
  rcases p with ⟨q, hq⟩
  have : Fact q.Prime := ⟨hq⟩
  have : Nontrivial ℚ_[q] := (Padic.normedField q).toNontrivial
  have : Free ℚ ℚ_[q] := Free.of_divisionRing ℚ ℚ_[q]
  have : FaithfullyFlat ℚ ℚ_[q] := inferInstance
  have hs (i : Fin 2) : Matrix.single i i (1 : ℚ) ≠ 0 := fun h ↦ by
    simpa using congrFun₂ h i i
  have hne (i : Fin 2) : (1 : ℚ_[q]) ⊗ₜ[ℚ] Matrix.single i i (1 : ℚ) ≠ 0 := fun h ↦
    hs i ((FaithfullyFlat.one_tmul_eq_zero_iff ℚ _ _).mp h)
  have hmul : (1 : ℚ_[q]) ⊗ₜ[ℚ] Matrix.single (0 : Fin 2) (0 : Fin 2) (1 : ℚ) *
      (1 : ℚ_[q]) ⊗ₜ[ℚ] Matrix.single (1 : Fin 2) (1 : Fin 2) (1 : ℚ) = 0 := by
    simp
  exact hne 1 (((h _ (hne 0)).mul_right_eq_zero).mp hmul)

end QuaternionAlgebra

namespace Subalgebra

variable {B : Type*} [Ring B] [Algebra ℚ B] {O O' O₁ O₂ : Subalgebra ℤ B}

lemma isQuaternionOrder_inf (h4 : finrank ℚ B = 4) (h₁ : O₁.IsQuaternionOrder)
    (h₂ : O₂.IsQuaternionOrder) : (O₁ ⊓ O₂).IsQuaternionOrder := by
  have : FiniteDimensional ℚ B := .of_finrank_pos (by omega)
  have : IsLattice ℚ (toSubmodule O₁) := h₁
  have : IsLattice ℚ (toSubmodule O₂) := h₂
  rw [IsQuaternionOrder, Algebra.inf_toSubmodule]
  infer_instance

/-- **An Eichler order is an order** (LMFDB `shimcurve.eichler`): the intersection of two orders of
a quaternion algebra over `ℚ` is a lattice. -/
lemma IsEichlerOrder.isQuaternionOrder (h4 : finrank ℚ B = 4) (hO : O.IsEichlerOrder) :
    O.IsQuaternionOrder := by
  rcases hO with ⟨O₁, O₂, h₁, h₂, rfl⟩
  exact isQuaternionOrder_inf h4 h₁.prop h₂.prop

/-- **The level of an Eichler order is unique** (LMFDB `shimcurve.eichler`): it is
`discrd(O) / disc(B)`. -/
lemma IsEichlerOrderOfLevel.unique {M M' : ℕ} (h : O.IsEichlerOrderOfLevel M)
    (h' : O.IsEichlerOrderOfLevel M') : M = M' := by
  have hD : (discriminant B : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (discriminant_ne_zero B)
  exact_mod_cast mul_left_cancel₀ hD (h.2.1.symm.trans h'.2.1)

variable [Algebra.IsCentral ℚ B] [IsSimpleRing B]

lemma quaternionDisc_eq_relIndex_sq_mul (h4 : finrank ℚ B = 4) (hO : O.IsQuaternionOrder)
    (hO' : O'.IsQuaternionOrder) (h : O ≤ O') : O.quaternionDisc =
      ((toSubmodule O).toAddSubgroup.relIndex (toSubmodule O').toAddSubgroup : ℚ) ^ 2 *
        O'.quaternionDisc := by
  have : IsLattice ℚ (toSubmodule O) := hO
  have : IsLattice ℚ (toSubmodule O') := hO'
  rcases nonempty_basis_of_isQuaternionOrder h4 hO with ⟨x⟩
  rcases nonempty_basis_of_isQuaternionOrder h4 hO' with ⟨x'⟩
  rcases exists_nonempty_algEquiv_of_finrank_eq_four (by simp) h4 with ⟨a, b, ⟨e⟩⟩
  let y : Basis (Fin 4) ℤ (toSubmodule O) := x.map O.toSubmoduleEquiv.symm
  let y' : Basis (Fin 4) ℤ (toSubmodule O') := x'.map O'.toSubmoduleEquiv.symm
  let c : Basis (Fin 4) ℚ B := y.extendOfIsLattice ℚ
  let c' : Basis (Fin 4) ℚ B := y'.extendOfIsLattice ℚ
  have hc (k : Fin 4) : c k = x k := y.extendOfIsLattice_apply ℚ k
  have hc' (k : Fin 4) : c' k = x' k := y'.extendOfIsLattice_apply ℚ k
  have hidx : ((toSubmodule O).toAddSubgroup.relIndex (toSubmodule O').toAddSubgroup : ℚ) =
      |c'.det c| :=
    AddSubgroup.relIndex_eq_abs_det _ _ (fun _ hz ↦ h hz) c c'
      (IsLattice.toAddSubgroup_eq_closure_range_extendOfIsLattice y)
      (IsLattice.toAddSubgroup_eq_closure_range_extendOfIsLattice y')
  rw [quaternionDisc_eq_quaternionDiscOfBasis h4 hO x, quaternionDiscOfBasis_eq_sq e hc,
    quaternionDisc_eq_quaternionDiscOfBasis h4 hO' x', quaternionDiscOfBasis_eq_sq e hc', hidx,
    sq_abs]
  set E : Basis (Fin 4) ℚ B := (basisOneIJK (a : ℚ) 0 b).map e.toLinearEquiv
  rw [Basis.det_apply, Basis.det_apply, Basis.det_apply, ← Basis.toMatrix_mul_toMatrix E c' c,
    Matrix.det_mul]
  ring1

/-- **The reduced discriminant of a suborder is the index times the reduced discriminant**: for
orders `O ⊆ O'` of a quaternion algebra over `ℚ`, `discrd(O) = [O' : O] discrd(O')`. -/
lemma quaternionDiscrd_eq_relIndex_mul (h4 : finrank ℚ B = 4) (hO : O.IsQuaternionOrder)
    (hO' : O'.IsQuaternionOrder) (h : O ≤ O') : O.quaternionDiscrd =
      (toSubmodule O).toAddSubgroup.relIndex (toSubmodule O').toAddSubgroup *
        O'.quaternionDiscrd := by
  refine (pow_left_inj₀ (quaternionDiscrd_pos h4 hO).le
    (mul_nonneg (Nat.cast_nonneg _) (quaternionDiscrd_pos h4 hO').le) two_ne_zero).mp ?_
  rw [quaternionDiscrd_sq h4 hO, mul_pow, quaternionDiscrd_sq h4 hO',
    quaternionDisc_eq_relIndex_sq_mul h4 hO hO' h]

/-- **Every order lies in a maximal order**: an order of least reduced discriminant among those
containing a given order is maximal, since a strictly larger order has a strictly smaller reduced
discriminant. -/
lemma exists_isMaximalQuaternionOrder_le (h4 : finrank ℚ B = 4) (hO : O.IsQuaternionOrder) :
    ∃ O₁ : Subalgebra ℤ B, O₁.IsMaximalQuaternionOrder ∧ O ≤ O₁ := by
  classical
  have hex :
      ∃ n : ℕ, ∃ O' : Subalgebra ℤ B, O'.IsQuaternionOrder ∧ O ≤ O' ∧ O'.quaternionDiscrd = n := by
    rcases exists_quaternionDiscrd_eq_natCast h4 hO with ⟨n, hn⟩
    exact ⟨n, O, hO, le_rfl, hn⟩
  rcases Nat.find_spec hex with ⟨O₁, h₁, hle, hn⟩
  refine ⟨O₁, ⟨h₁, fun O'' h'' h₁'' ↦ ?_⟩, hle⟩
  rcases exists_quaternionDiscrd_eq_natCast h4 h'' with ⟨m, hm⟩
  have hmin : Nat.find hex ≤ m := Nat.find_min' hex ⟨O'', h'', hle.trans h₁'', hm⟩
  have hpos : 0 < Nat.find hex := by
    exact_mod_cast hn ▸ quaternionDiscrd_pos h4 h₁
  set i : ℕ := (toSubmodule O₁).toAddSubgroup.relIndex (toSubmodule O'').toAddSubgroup
  have hidx : (Nat.find hex : ℚ) = i * m := by
    rw [← hn, ← hm]
    exact quaternionDiscrd_eq_relIndex_mul h4 h₁ h'' h₁''
  have hidx' : Nat.find hex = i * m := by
    exact_mod_cast hidx
  have h1 : i = 1 := by
    rcases Nat.lt_or_ge i 2 with h | h
    · interval_cases i
      · omega
      · rfl
    · nlinarith
  exact fun _ hz ↦ AddSubgroup.relIndex_eq_one.mp h1 hz

private lemma eq_of_dvd_prod {S : Finset Nat.Primes} {k : ℕ} (hk : k.Prime)
    (h : k ∣ ∏ p ∈ S, (p : ℕ)) : ∃ p ∈ S, (p : ℕ) = k := by
  rcases (hk.prime.dvd_finsetProd_iff _).mp h with ⟨p, hp, hkp⟩
  exact ⟨p, hp, ((Nat.prime_dvd_prime_iff_eq hk p.prop).mp hkp).symm⟩

/-- **An Eichler order has a level exactly when every ramified prime divides its reduced
discriminant exactly once** (LMFDB `shimcurve.eichler`): `disc(B)` is the product of the ramified
primes, so `discrd(O) = disc(B) M` with `M` coprime to `disc(B)` exactly when each ramified prime
divides `discrd(O)` but its square does not. -/
lemma exists_isEichlerOrderOfLevel_iff (h4 : finrank ℚ B = 4) (hO : O.IsEichlerOrder) {d : ℕ}
    (hd : O.quaternionDiscrd = d) : (∃ M : ℕ, O.IsEichlerOrderOfLevel M) ↔
      ∀ p : Nat.Primes, IsRamifiedAt B p → (p : ℕ) ∣ d ∧ ¬(p : ℕ) ^ 2 ∣ d := by
  let S : Finset Nat.Primes := (finite_setOf_isRamifiedAt B h4).toFinset
  have hS (p : Nat.Primes) : p ∈ S ↔ IsRamifiedAt B p :=
    (finite_setOf_isRamifiedAt B h4).mem_toFinset
  have hD : discriminant B = ∏ p ∈ S, (p : ℕ) := discriminant_eq_prod B h4
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨M, -, hM, hcop⟩ p hp
    have hdM : d = discriminant B * M := by
      exact_mod_cast hd.symm.trans hM
    have hpD : (p : ℕ) ∣ discriminant B := hD ▸ Finset.dvd_prod_of_mem _ ((hS p).mpr hp)
    refine ⟨hdM ▸ dvd_mul_of_dvd_left hpD M, fun hp2 ↦ ?_⟩
    have hpM : ¬(p : ℕ) ∣ M := fun hpM ↦
      p.prop.ne_one ((hcop.coprime_dvd_left hpD).eq_one_of_dvd hpM)
    have hp2D : (p : ℕ) ^ 2 ∣ discriminant B :=
      ((p.prop.coprime_iff_not_dvd.mpr hpM).pow_left 2).dvd_of_dvd_mul_right (hdM ▸ hp2)
    rw [hD, ← Finset.mul_prod_erase S _ ((hS p).mpr hp), sq] at hp2D
    rcases eq_of_dvd_prod p.prop (Nat.dvd_of_mul_dvd_mul_left p.prop.pos hp2D) with ⟨q, hq, hqp⟩
    exact Finset.ne_of_mem_erase hq (Subtype.ext hqp)
  · have hdvd : ∏ p ∈ S, (p : ℕ) ∣ d :=
      S.prod_map ⟨Subtype.val, Subtype.val_injective⟩ (fun p ↦ p) ▸ Finset.prod_primes_dvd d
        (Finset.forall_mem_map.mpr fun p _ ↦ p.prop.prime)
        (Finset.forall_mem_map.mpr fun p hp ↦ (h p ((hS p).mp hp)).1)
    rcases hD ▸ hdvd with ⟨M, hM⟩
    refine ⟨M, hO, by rw [hd, hM, Nat.cast_mul], Nat.coprime_of_dvd fun k hk hkD hkM ↦ ?_⟩
    rcases eq_of_dvd_prod hk (hD ▸ hkD) with ⟨p, hp, rfl⟩
    refine (h p ((hS p).mp hp)).2 ?_
    rw [hM, sq]
    exact Nat.mul_dvd_mul hkD hkM

/-- **When no prime ramifies, every Eichler order has a level** (LMFDB `shimcurve.eichler`), its
reduced discriminant: for `disc(B) = 1` the condition `gcd(disc(B), M) = 1` is empty. -/
lemma exists_isEichlerOrderOfLevel_of_discriminant_eq_one (h4 : finrank ℚ B = 4)
    (hD : discriminant B = 1) (hO : O.IsEichlerOrder) : ∃ M : ℕ, O.IsEichlerOrderOfLevel M := by
  rcases exists_quaternionDiscrd_eq_natCast h4 (hO.isQuaternionOrder h4) with ⟨d, hd⟩
  exact ⟨d, hO, by rw [hd, hD, Nat.cast_one, one_mul], hD ▸ Nat.coprime_one_left d⟩

end Subalgebra

namespace Subalgebra

/-- **`M₂(ℚ)` has an Eichler order** (LMFDB `shimcurve.eichler`): the integral matrices lie in a
maximal order `O₁`, and `O₁ = O₁ ⊓ O₁` is an Eichler order. -/
lemma exists_isEichlerOrder_matrix :
    ∃ O : Subalgebra ℤ (Matrix (Fin 2) (Fin 2) ℚ), O.IsEichlerOrder := by
  rcases exists_isMaximalQuaternionOrder_le (by simp [finrank_matrix])
    isQuaternionOrder_range_mapMatrix with ⟨O₁, h₁, -⟩
  exact ⟨O₁, O₁, O₁, h₁, h₁, (inf_idem O₁).symm⟩

/-- **Every Eichler order of `M₂(ℚ)` has a level** (LMFDB `shimcurve.eichler`), its reduced
discriminant, as `M₂(ℚ)` is ramified at no prime. -/
lemma exists_isEichlerOrderOfLevel_matrix {O : Subalgebra ℤ (Matrix (Fin 2) (Fin 2) ℚ)}
    (hO : O.IsEichlerOrder) : ∃ M : ℕ, O.IsEichlerOrderOfLevel M :=
  exists_isEichlerOrderOfLevel_of_discriminant_eq_one (by simp [finrank_matrix])
    discriminant_matrix hO

end Subalgebra
