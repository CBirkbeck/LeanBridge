import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.EisensteinSubspace
import TauCeti.LinearAlgebra.SymmetricPower.Coordinates
import TauCeti.LinearAlgebra.SymmetricPower.Lift

/-!
# The vector-valued Siegel Eisenstein series of degree 2 vanish for `j > 0`

The space `E_{j,k}(Γ₂)` of the LMFDB knowl `mf.siegel.subspace.degree.two` is spanned by the Siegel
Eisenstein series `E(v)(Z) = ∑_{(C, D)} ρ_{k,j}(CZ + D)⁻¹ v` of the vectors `v ∈ Sym^j(ℂ²)` fixed by
`ρ_{k,j}(GL(2, ℤ))`. This file proves that for `j > 0` there is no nonzero such vector, so that
`E_{j,k}(Γ₂) = 0`.

The linear map `Ψ : Sym^j(ℂ²) → ℂ[X]`, `u₁ ⋯ u_j ↦ ∏ᵢ (uᵢ₀ + uᵢ₁ X)`, is injective, sending the
basis `e₀^a e₁^b` to `X^b`. The unipotent `(1, 1; 0, 1)` acts on its image by `p ↦ p(X + 1)`, so
`Ψ(v)` is a constant `c`, and `v = c e₀^j`; the element `(0, -1; 1, 0)` sends it to `c e₁^j`, so
`c = c X^j` and `c = 0` for `j > 0`.

## Main definitions

* `SiegelUpperHalfSpace.symDehomogenize`: the linear map `Ψ : Sym^j(ℂ²) → ℂ[X]`.
* `SiegelUpperHalfSpace.symConstCoeff`: the linear form `ψ` on `Sym^j(ℂ²)` with `ψ(e₁^j) = 1`.

## Main results

* `SiegelUpperHalfSpace.symDehomogenize_injective`: `Ψ` is injective.
* `SiegelUpperHalfSpace.eq_smul_tprod_of_symPowerRep_eq`: the vectors fixed by `(1, 1; 0, 1)` are
  the multiples of `e₁^j`.
* `SiegelUpperHalfSpace.eq_zero_of_isGLIntInvariant`: no nonzero vector of `Sym^j(ℂ²)`, `j > 0`, is
  fixed by `ρ_{k,j}(GL(2, ℤ))`.
* `SiegelUpperHalfSpace.siegelEisensteinSubspaceKJ_eq_bot`: `E_{j,k}(Γ₂) = 0` for `j > 0`.
-/

open ModularGroup Module Polynomial TauCeti

open Matrix hiding one_zpow

open scoped MatrixGroups TensorProduct

namespace SiegelUpperHalfSpace

/-- The linear map `(u₀, u₁) ↦ u₀ + u₁ X`. -/
private noncomputable def dehomLinear : (Fin 2 → ℂ) →ₗ[ℂ] ℂ[X] :=
  monomial 0 ∘ₗ LinearMap.proj 0 + monomial 1 ∘ₗ LinearMap.proj 1

private lemma dehomLinear_apply (u : Fin 2 → ℂ) : dehomLinear u = C (u 0) + C (u 1) * X := by
  simp [dehomLinear, C_mul_X_eq_monomial]

variable (j : ℕ)

/-- The multilinear map `(u₁, …, u_j) ↦ ∏ᵢ (uᵢ₀ + uᵢ₁ X)`. -/
private noncomputable def dehomMultilinear : MultilinearMap ℂ (fun _ : Fin j ↦ Fin 2 → ℂ) ℂ[X] :=
  (MultilinearMap.mkPiAlgebra ℂ (Fin j) ℂ[X]).compLinearMap fun _ ↦ dehomLinear

private lemma dehomMultilinear_apply (m : Fin j → Fin 2 → ℂ) :
    dehomMultilinear j m = ∏ i, dehomLinear (m i) := by
  simp [dehomMultilinear]

/-- The linear map **`Ψ : Sym^j(ℂ²) → ℂ[X]`**, `u₁ ⋯ u_j ↦ ∏ᵢ (uᵢ₀ + uᵢ₁ X)`. -/
noncomputable def symDehomogenize : Sym[ℂ]^j (Fin 2 → ℂ) →ₗ[ℂ] ℂ[X] :=
  SymmetricPower.lift (dehomMultilinear j) fun e ↦ MultilinearMap.ext fun m ↦ by
    simp only [dehomMultilinear_apply]
    exact Equiv.prod_comp e fun i ↦ dehomLinear (m i)

variable {j}

lemma symDehomogenize_tprod (m : Fin j → Fin 2 → ℂ) :
    symDehomogenize j (⨂ₛ[ℂ] i, m i) = ∏ i, (C (m i 0) + C (m i 1) * X) :=
  (SymmetricPower.lift_tprod _ _ m).trans <| (dehomMultilinear_apply j m).trans <|
    Finset.prod_congr rfl fun i _ ↦ dehomLinear_apply (m i)

private lemma prod_C_add_C_mul_X_single (f : Fin j → Fin 2) : ∏ i,
    (C ((Pi.single (f i) 1 : Fin 2 → ℂ) 0) + C ((Pi.single (f i) 1 : Fin 2 → ℂ) 1) * X) =
      X ^ (List.ofFn f).count 1 := by
  induction j with
  | zero => simp
  | succ n ih =>
    rw [Fin.prod_univ_succ, ih, List.ofFn_succ, List.count_cons]
    rcases hf : f 0 with ⟨a, ha⟩
    interval_cases a
    · simp
    · simp [pow_succ, mul_comm]

private lemma count_zero_add_count_one (m : Multiset (Fin 2)) :
    m.count 0 + m.count 1 = Multiset.card m :=
  (Fin.sum_univ_two _).symm.trans <| Multiset.sum_count_eq_card fun _ _ ↦ Finset.mem_univ _

private lemma sym_eq_of_count_one {s t : Sym (Fin 2) j}
    (h : (s : Multiset (Fin 2)).count 1 = (t : Multiset (Fin 2)).count 1) : s = t := by
  have hs : (s : Multiset (Fin 2)).count 0 + (s : Multiset (Fin 2)).count 1 = j := by
    rw [count_zero_add_count_one, Sym.card_coe]
  have ht : (t : Multiset (Fin 2)).count 0 + (t : Multiset (Fin 2)).count 1 = j := by
    rw [count_zero_add_count_one, Sym.card_coe]
  refine Sym.ext (Multiset.ext.mpr fun a ↦ ?_)
  fin_cases a
  · simp only [Fin.zero_eta]
    omega
  · exact h

private lemma symDehomogenize_basis (s : Sym (Fin 2) j) :
    symDehomogenize j ((Pi.basisFun ℂ (Fin 2)).symmetricPower j s) =
      X ^ (s : Multiset (Fin 2)).count 1 := by
  rcases Sym.ofFn_surjective s with ⟨f, rfl⟩
  rw [Basis.symmetricPower_apply, SymmetricPower.tprodOfSym_ofFn, symDehomogenize_tprod]
  simp only [Pi.basisFun_apply]
  rw [prod_C_add_C_mul_X_single, Sym.coe_ofFn, Multiset.coe_count]

/-- **`Ψ` is injective**, sending the basis `e₀^a e₁^b` to the distinct monomials `X^b`. -/
lemma symDehomogenize_injective : Function.Injective (symDehomogenize j) := by
  refine (injective_iff_map_eq_zero _).mpr fun v hv ↦ ?_
  let b : Basis (Sym (Fin 2) j) ℂ (Sym[ℂ]^j (Fin 2 → ℂ)) := (Pi.basisFun ℂ (Fin 2)).symmetricPower j
  refine b.ext_elem fun s ↦ ?_
  have h : symDehomogenize j v =
      ∑ t ∈ (b.repr v).support, C (b.repr v t) * X ^ (t : Multiset (Fin 2)).count 1 := by
    conv_lhs => rw [← b.linearCombination_repr v]
    rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [map_smul, symDehomogenize_basis, smul_eq_C_mul]
  have hc : coeff (∑ t ∈ (b.repr v).support, C (b.repr v t) * X ^ (t : Multiset (Fin 2)).count 1)
      ((s : Multiset (Fin 2)).count 1) = coeff 0 ((s : Multiset (Fin 2)).count 1) :=
    congrArg (fun p ↦ coeff p ((s : Multiset (Fin 2)).count 1)) (h.symm.trans hv)
  simp only [finsetSum_coeff, coeff_C_mul] at hc
  rw [Finset.sum_eq_single s] at hc
  · simpa using hc
  · intro t _ hts
    have hne : (s : Multiset (Fin 2)).count 1 ≠ (t : Multiset (Fin 2)).count 1 :=
      fun e ↦ hts (sym_eq_of_count_one e.symm)
    simp [hne]
  · intro hs
    simpa using hs

variable (j) in
/-- The linear form `ψ` on `Sym^j(ℂ²)` with `ψ(e₁^j) = 1`, the constant term of the dehomogenisation
`u₁ ⋯ u_j ↦ ∏ᵢ (uᵢ₀ + uᵢ₁ X)`. -/
noncomputable def symConstCoeff : Dual ℂ (Sym[ℂ]^j (Fin 2 → ℂ)) :=
  Polynomial.leval 0 ∘ₗ symDehomogenize j

lemma symConstCoeff_tprod_single : symConstCoeff j (⨂ₛ[ℂ] _ : Fin j, Pi.single 0 1) = 1 := by
  simp [symConstCoeff, symDehomogenize_tprod]

private lemma symDehomogenize_unipotent (x : Sym[ℂ]^j (Fin 2 → ℂ)) : symDehomogenize j
    (symPowerRep ℂ 2 j (GeneralLinearGroup.map (Int.castRingHom ℂ) (T : GL (Fin 2) ℤ)) x) =
      (symDehomogenize j x).comp (X + 1) := by
  have hx : x ∈ Submodule.span ℂ (Set.range (SymmetricPower.tprod ℂ)) := by
    rw [SymmetricPower.span_tprod_eq_top]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx =>
    rcases hx with ⟨m, rfl⟩
    rw [symPowerRep_tprod, symDehomogenize_tprod, symDehomogenize_tprod, prod_comp]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    simp [mulVec]
    ring1
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, map_add, map_add, hx, hy, add_comp]
  | smul a x _ hx =>
    rw [map_smul, map_smul, map_smul, hx, smul_comp]

variable (k : ℤ) {v : Sym[ℂ]^j (Fin 2 → ℂ)}

/-- **The vectors fixed by the unipotent `(1, 1; 0, 1)` are the multiples of `e₁^j`.** -/
lemma eq_smul_tprod_of_symPowerRep_eq
    (hv : symPowerRep ℂ 2 j (GeneralLinearGroup.map (Int.castRingHom ℂ) (T : GL (Fin 2) ℤ)) v = v) :
    v = symConstCoeff j v • ⨂ₛ[ℂ] _ : Fin j, (Pi.single 0 1 : Fin 2 → ℂ) := by
  have hu : (symDehomogenize j v).comp (X + 1) = symDehomogenize j v := by
    rw [← symDehomogenize_unipotent, hv]
  have heval (n : ℕ) : (symDehomogenize j v).eval (n : ℂ) = (symDehomogenize j v).eval 0 := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [← ih]
      conv_rhs => rw [← hu]
      simp
  have hC : symDehomogenize j v = C ((symDehomogenize j v).eval 0) := by
    refine eq_of_infinite_eval_eq _ _ ((Set.infinite_range_of_injective Nat.cast_injective).mono ?_)
    rintro _ ⟨n, rfl⟩
    simpa using heval n
  refine symDehomogenize_injective ?_
  rw [map_smul, symDehomogenize_tprod, smul_eq_C_mul]
  simp only [Pi.single_eq_same, map_one, ne_eq, one_ne_zero, not_false_eq_true, Pi.single_eq_of_ne,
    map_zero, zero_mul, add_zero, Finset.prod_const_one, mul_one]
  exact hC

variable (v) in
lemma rhoKJ_eq_symPowerRep (g : SL(2, ℤ)) :
    rhoKJ k j (GeneralLinearGroup.map (Int.castRingHom ℂ) (g : GL (Fin 2) ℤ)) v =
      symPowerRep ℂ 2 j (GeneralLinearGroup.map (Int.castRingHom ℂ) (g : GL (Fin 2) ℤ)) v := by
  have hdet : (GeneralLinearGroup.map (Int.castRingHom ℂ) (g : GL (Fin 2) ℤ)).det = 1 := by
    refine Units.ext ?_
    rw [GeneralLinearGroup.val_det_apply, Units.val_one]
    have e : ((GeneralLinearGroup.map (Int.castRingHom ℂ) (g : GL (Fin 2) ℤ) : GL (Fin 2) ℂ) :
        Matrix (Fin 2) (Fin 2) ℂ) = (Int.castRingHom ℂ).mapMatrix (g : Matrix (Fin 2) (Fin 2) ℤ) :=
      rfl
    rw [e, ← RingHom.map_det, g.det_coe, map_one]
  have h : rhoKJ k j (GeneralLinearGroup.map (Int.castRingHom ℂ) (g : GL (Fin 2) ℤ)) v =
      (((GeneralLinearGroup.map (Int.castRingHom ℂ) (g : GL (Fin 2) ℤ)).det ^ k : ℂˣ) : ℂ) •
        symPowerRep ℂ 2 j (GeneralLinearGroup.map (Int.castRingHom ℂ) (g : GL (Fin 2) ℤ)) v :=
    rfl
  rw [hdet] at h
  simpa using h

private lemma symPowerRep_eq_of_mem (hv : IsGLIntInvariant (rhoKJ k j) v) (g : SL(2, ℤ)) :
    symPowerRep ℂ 2 j (GeneralLinearGroup.map (Int.castRingHom ℂ) (g : GL (Fin 2) ℤ)) v = v :=
  (rhoKJ_eq_symPowerRep k v g).symm.trans (hv g)

/-- **No nonzero vector of `Sym^j(ℂ²)`, `j > 0`, is fixed by `ρ_{k,j}(GL(2, ℤ))`**: `(1, 1; 0, 1)`
forces `v = c e₀^j`, and `(0, -1; 1, 0)` sends it to `c e₁^j`. -/
lemma eq_zero_of_isGLIntInvariant (hj : j ≠ 0) (hv : IsGLIntInvariant (rhoKJ k j) v) : v = 0 := by
  have hv₀ : v = symConstCoeff j v • ⨂ₛ[ℂ] _ : Fin j, (Pi.single 0 1 : Fin 2 → ℂ) :=
    eq_smul_tprod_of_symPowerRep_eq (symPowerRep_eq_of_mem k hv T)
  generalize symConstCoeff j v = c at hv₀
  have hw :
      symPowerRep ℂ 2 j (GeneralLinearGroup.map (Int.castRingHom ℂ) (S : GL (Fin 2) ℤ)) v = v :=
    symPowerRep_eq_of_mem k hv S
  have e₁ : ((GeneralLinearGroup.map (Int.castRingHom ℂ) (S : GL (Fin 2) ℤ) : GL (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) *ᵥ (Pi.single 0 1 : Fin 2 → ℂ) = Pi.single 1 1 := by
    ext a
    fin_cases a <;> simp [mulVec]
  rw [hv₀, map_smul, symPowerRep_tprod, e₁] at hw
  have h₂ : symDehomogenize j (c • ⨂ₛ[ℂ] _ : Fin j, (Pi.single 1 1 : Fin 2 → ℂ)) =
      symDehomogenize j (c • ⨂ₛ[ℂ] _ : Fin j, (Pi.single 0 1 : Fin 2 → ℂ)) :=
    congrArg _ hw
  have h₀ : symDehomogenize j (⨂ₛ[ℂ] _ : Fin j, (Pi.single 0 1 : Fin 2 → ℂ)) = 1 := by
    simp [symDehomogenize_tprod]
  have h₁ : symDehomogenize j (⨂ₛ[ℂ] _ : Fin j, (Pi.single 1 1 : Fin 2 → ℂ)) = X ^ j := by
    simp [symDehomogenize_tprod]
  rw [map_smul, map_smul, h₀, h₁] at h₂
  have h₃ : c = 0 := by
    have e₂ : coeff (c • X ^ j : ℂ[X]) j = coeff (c • (1 : ℂ[X])) j :=
      congrArg (fun p ↦ coeff p j) h₂
    simpa [coeff_one, hj] using e₂
  rw [hv₀, h₃, zero_smul]

/-- **The space of vector-valued Siegel Eisenstein series of degree `2` vanishes for `j > 0`**: the
only vector of `Sym^j(ℂ²)` fixed by `ρ_{k,j}(GL(2, ℤ))` is `0`. -/
lemma siegelEisensteinSubspaceKJ_eq_bot (hj : j ≠ 0) : siegelEisensteinSubspaceKJ k j = ⊥ := by
  rw [siegelEisensteinSubspaceKJ, siegelEisensteinSubspace, Submodule.span_eq_bot]
  rintro F ⟨w, hw, hF⟩
  rw [eq_zero_of_isGLIntInvariant k hj hw] at hF
  funext Z
  rw [Pi.zero_apply, ← forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  have h : HasSum (fun _ : SymplecticGroup.SiegelParabolicCosets (Fin 2) ↦ (0 : ℂ)) (φ (F Z)) := by
    simpa [vectorSiegelEisensteinTerm] using hF Z φ
  exact h.unique hasSum_zero

end SiegelUpperHalfSpace
