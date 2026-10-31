import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.PoincareUnfolding

/-!
# Poincaré series span the cusp forms

The `m`-th Poincaré series `P_m` (`m ≥ 1`) of weight `k` and multiplier `v` on `G ≤ SL(2, ℤ)` at
the cusp `s = γ_s ∞` of width `w` (LMFDB `specialfunction.poincare`) span every
finite-dimensional space `V` of forms containing them on which the unfolding applies: if `V`
were larger than their span `W`, the linear map `f ↦ (∫_D conj(b_i) f y^k dμ)_i` on `V`, for a
basis `(b_i)` of `W`, would have a nonzero kernel, whose elements are orthogonal to `W`, hence to
every `P_m`, hence zero, by the unfolding: the Petersson product of `f` with `P_m` is a nonzero
multiple of the `m`-th Fourier coefficient of `f`. No definiteness of the Petersson product is
needed. For `V` the cusp forms of weight `k ≥ 3` and multiplier `v`, this is the LMFDB's statement
that the Poincaré series generate the cusp forms, under the hypotheses that the space is
finite-dimensional and that its elements have Fourier expansions without constant term at `s` and
integrable Petersson integrands, standard facts about cusp forms that are not proved here for a
general multiplier. A fundamental domain `D` exists for every `G` (Tau Ceti's
`ModularGroup.isFundamentalDomain_iUnion_out_inv_smul_fdo_withCenter`). For the trivial multiplier
and `G` of finite index, the finite dimension is Tau Ceti's
`TauCeti.finiteDimensional_cuspForm_finiteIndex` (through
`ModularForm.mem_multiplierCuspSpace_one_iff`), and Tau Ceti's
`UpperHalfPlane.integrableOn_petersson_of_measure_lt_top` gives the integrability on `D` once `D`
has finite measure.

## Main results

* `ModularForm.span_poincareSeries_eq`: the `P_m` span `V`.
* `ModularForm.span_poincareSeries_eq_multiplierCuspSpace`: the `P_m` span the cusp forms of weight
  `k ≥ 3` and multiplier `v`.
-/

open UpperHalfPlane Matrix SpecialLinearGroup ModularGroup MeasureTheory Set

open scoped MatrixGroups ComplexConjugate ModularForm

namespace ModularForm

variable {G : Subgroup SL(2, ℤ)} (γ : SL(2, ℤ)) (v : G →* Circle) (k : ℤ) (w : ℕ) {D : Set ℍ}
    {t : G}

/-- **Poincaré series span every space of forms they lie in** (LMFDB
`specialfunction.poincare`): let `D` be a fundamental domain for the image of `G` in
`PSL(2, ℤ)`, `w` the width of the cusp, the terms of the Poincaré series constant on the cosets
`G_s g`, and `V` a finite-dimensional space of functions containing the `P_m`, `m ≥ 1`, whose
elements satisfy `f ∣[k] g = v(g) f` for `g ∈ G`, have Fourier expansions
`(f ∣[k] γ_s)(z) = Σ_{j ≥ 1} a_j e^{2πi j z / w}` on `ℍ`, and whose Petersson integrands are
integrable (on `D`, and against `e^{2πi m z / w}` on the strip). Then the `P_m` span `V`. -/
lemma span_poincareSeries_eq (hw₀ : 0 < w) (hk : 2 ≤ k)
    (hD : IsFundamentalDomain (G.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) D volume)
    (ht : γ⁻¹ * (t : SL(2, ℤ)) * γ = T ^ (w : ℤ) ∨ γ⁻¹ * (t : SL(2, ℤ)) * γ = -T ^ (w : ℤ))
    (hw : ∀ h ∈ cuspStabilizer G γ, (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1)
    (hv : ∀ h ∈ cuspStabilizer G γ, (v h : ℂ) = ((γ⁻¹ * (h : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k)
    (V : Submodule ℂ (ℍ → ℂ)) [FiniteDimensional ℂ V]
    (hPV : ∀ m : ℕ, 0 < m → poincareSeries γ v k m w ∈ V)
    (hf : ∀ f ∈ V, ∀ g : G, f ∣[k] (g : SL(2, ℤ)) = (v g : ℂ) • f)
    (hcoeff : ∀ f ∈ V, ∃ a : ℕ → ℂ, a 0 = 0 ∧ ∀ z : ℍ, HasSum (fun j : ℕ ↦
      a j * Complex.exp (2 * Real.pi * Complex.I * (j / w) * z)) ((f ∣[k] γ) z))
    (hint : ∀ f ∈ V, ∀ m : ℕ, 0 < m → IntegrableOn (petersson k (fun u : ℍ ↦
      Complex.exp (2 * Real.pi * Complex.I * (m / w) * u)) (f ∣[k] γ))
        {z : ℍ | z.re ∈ Ico 0 (w : ℝ)}) (hB : ∀ f ∈ V, ∀ g ∈ V, IntegrableOn (petersson k f g) D) :
    Submodule.span ℂ {P | ∃ m : ℕ, 0 < m ∧ poincareSeries γ v k m w = P} = V := by
  have hWV : Submodule.span ℂ {P | ∃ m : ℕ, 0 < m ∧ poincareSeries γ v k m w = P} ≤ V :=
    Submodule.span_le.mpr fun P ⟨m, hm, hP⟩ ↦ hP ▸ hPV m hm
  refine hWV.eq_of_not_lt fun hlt ↦ ?_
  have : FiniteDimensional ℂ
      (Submodule.span ℂ {P | ∃ m : ℕ, 0 < m ∧ poincareSeries γ v k m w = P}) :=
    Submodule.finiteDimensional_of_le hWV
  let b : Module.Basis (Fin (Module.finrank ℂ
      (Submodule.span ℂ {P | ∃ m : ℕ, 0 < m ∧ poincareSeries γ v k m w = P}))) ℂ
        (Submodule.span ℂ {P | ∃ m : ℕ, 0 < m ∧ poincareSeries γ v k m w = P}) :=
    Module.finBasis ℂ _
  let L : V →ₗ[ℂ] (Fin (Module.finrank ℂ
      (Submodule.span ℂ {P | ∃ m : ℕ, 0 < m ∧ poincareSeries γ v k m w = P})) → ℂ) :=
    { toFun := fun g i ↦ ∫ z in D, petersson k (b i : ℍ → ℂ) g z
      map_add' := fun g g' ↦ funext fun i ↦ by
        rw [Pi.add_apply, ← integral_add (hB _ (hWV (b i).2) _ g.2) (hB _ (hWV (b i).2) _ g'.2)]
        congr 1
        funext z
        simp only [petersson, Submodule.coe_add, Pi.add_apply]
        ring1
      map_smul' := fun c g ↦ funext fun i ↦ by
        rw [Pi.smul_apply, RingHom.id_apply, ← integral_smul]
        congr 1
        funext z
        simp only [petersson, Submodule.coe_smul, Pi.smul_apply]
        ring1 }
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt <| by
    rw [Module.finrank_fin_fun]
    exact Submodule.finrank_lt_finrank_of_lt hlt
  rcases (Submodule.ne_bot_iff _).mp hker with ⟨g, hgker, hg0⟩
  have hL (i : Fin (Module.finrank ℂ
      (Submodule.span ℂ {P | ∃ m : ℕ, 0 < m ∧ poincareSeries γ v k m w = P}))) :
      ∫ z in D, petersson k (b i : ℍ → ℂ) g z = 0 :=
    congrFun (LinearMap.mem_ker.mp hgker) i
  have horth (P : ℍ → ℂ)
      (hP : P ∈ Submodule.span ℂ {P | ∃ m : ℕ, 0 < m ∧ poincareSeries γ v k m w = P}) :
      ∫ z in D, petersson k P g z = 0 := by
    have hP' : P = ∑ i, b.repr ⟨P, hP⟩ i • (b i : ℍ → ℂ) := by
      simpa only [Submodule.coe_sum, Submodule.coe_smul] using
        (congrArg Subtype.val (b.sum_repr ⟨P, hP⟩)).symm
    have hpt (z : ℍ) : petersson k (∑ i, b.repr ⟨P, hP⟩ i • (b i : ℍ → ℂ)) g z =
        ∑ i, conj (b.repr ⟨P, hP⟩ i) * petersson k (b i : ℍ → ℂ) g z := by
      simp only [petersson, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
        Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ ↦ by ring1
    rw [hP']
    simp_rw [hpt]
    rw [integral_finsetSum _ fun i _ ↦ (hB _ (hWV (b i).2) _ g.2).const_mul _]
    simp [integral_const_mul, hL]
  rcases hcoeff g g.2 with ⟨a, ha₀, ha⟩
  exact hg0 <| Subtype.ext <| eq_zero_of_forall_setIntegral_petersson_poincareSeries_eq_zero_psl γ
    v k w hw₀ hk hD ht hw hv (hf g g.2) ha ha₀ (hint g g.2) fun m hm ↦
      horth _ (Submodule.subset_span ⟨m, hm, rfl⟩)

/-- **Poincaré series generate the cusp forms** (LMFDB `specialfunction.poincare`): for `k ≥ 3`,
`w` the width of the cusp `s = γ_s ∞` and the terms of the Poincaré series constant on the cosets
`G_s g`, if the space `S_k(G, v)` of cusp forms of weight `k` and multiplier `v`
(`ModularForm.multiplierCuspSpace`) is finite-dimensional and its elements have Fourier expansions
without constant term at `s` and integrable Petersson integrands, then the Poincaré series `P_m`,
`m ≥ 1`, at `s` span it. -/
lemma span_poincareSeries_eq_multiplierCuspSpace (hw₀ : 0 < w) (hk : 3 ≤ k)
    (hD : IsFundamentalDomain (G.map (QuotientGroup.mk' (Subgroup.center SL(2, ℤ)))) D volume)
    (ht : γ⁻¹ * (t : SL(2, ℤ)) * γ = T ^ (w : ℤ) ∨ γ⁻¹ * (t : SL(2, ℤ)) * γ = -T ^ (w : ℤ))
    (hw : ∀ h ∈ cuspStabilizer G γ, (w : ℤ) ∣ (γ⁻¹ * (h : SL(2, ℤ)) * γ) 0 1)
    (hv : ∀ h ∈ cuspStabilizer G γ, (v h : ℂ) = ((γ⁻¹ * (h : SL(2, ℤ)) * γ) 1 1 : ℂ) ^ k)
    [FiniteDimensional ℂ (multiplierCuspSpace k (multiplierMapGL v))]
    (hcoeff : ∀ f ∈ multiplierCuspSpace k (multiplierMapGL v), ∃ a : ℕ → ℂ, a 0 = 0 ∧
      ∀ z : ℍ, HasSum (fun j : ℕ ↦ a j * Complex.exp (2 * Real.pi * Complex.I * (j / w) * z))
        ((f ∣[k] γ) z))
    (hint : ∀ f ∈ multiplierCuspSpace k (multiplierMapGL v), ∀ m : ℕ, 0 < m →
      IntegrableOn (petersson k (fun u : ℍ ↦ Complex.exp (2 * Real.pi * Complex.I * (m / w) * u))
        (f ∣[k] γ)) {z : ℍ | z.re ∈ Ico 0 (w : ℝ)})
    (hB : ∀ f ∈ multiplierCuspSpace k (multiplierMapGL v),
      ∀ g ∈ multiplierCuspSpace k (multiplierMapGL v), IntegrableOn (petersson k f g) D) :
    Submodule.span ℂ {P | ∃ m : ℕ, 0 < m ∧ poincareSeries γ v k m w = P} =
      multiplierCuspSpace k (multiplierMapGL v) :=
  span_poincareSeries_eq γ v k w hw₀ (by omega) hD ht hw hv _
    (fun m hm ↦ poincareSeries_mem_multiplierCuspSpace γ v hk (by exact_mod_cast hm) hw₀ hw hv)
    (fun f hf g ↦ multiplierMapGL_apply_mapGL v g ▸ hf.1.2.1 ⟨_, Subgroup.mem_map_of_mem _ g.2⟩)
    hcoeff hint hB

end ModularForm
