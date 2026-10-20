import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Topology.Algebra.Constructions
import Mathlib.Topology.Instances.Matrix
import TauCeti.Data.Nat.Prime.Basic

/-!
# The level of an open subgroup of a matrix group over `ℤ_ℓ` or `ℤ̂`

Let `G` be a matrix group over `ℤ_ℓ` or `ℤ̂`, that is, a subgroup of `GL_n(ℤ_ℓ)` or `GL_n(ℤ̂)`; the
LMFDB's main case is `G = GL₂` itself, here `G = ⊤`. The level of an open subgroup `H` of `G` is
the least positive integer `N` such that `H` is the inverse image in `G` of its reduction modulo
`N`, that is, `H = G ∩ π_N⁻¹(π_N(H))` for the reduction `π_N` modulo `N`. Reduction modulo `N` of
`ℤ_ℓ` is reduction modulo `ℓ ^ v_ℓ(N)`, since `ℤ_ℓ / N ℤ_ℓ = ℤ / ℓ ^ v_ℓ(N) ℤ`, so the level of a
subgroup over `ℤ_ℓ` is a power of `ℓ`. Mathlib has no ring `ℤ̂`; we use the product `∏_ℓ ℤ_ℓ` over
the primes, to which it is canonically isomorphic, so that `GL_n(ℤ̂) = ∏_ℓ GL_n(ℤ_ℓ)`. Its reduction
modulo `N` is then reduction modulo `ℓ ^ v_ℓ(N)` at each prime `ℓ`, with values in
`∏_ℓ GL_n(ℤ / ℓ ^ v_ℓ(N) ℤ)`, which is `GL_n(ℤ / N ℤ)` by the Chinese remainder theorem.

## Main definitions

* `Matrix.GeneralLinearGroup.padicReduction`: reduction modulo `N` of `GL_n(ℤ_ℓ)`.
* `Matrix.GeneralLinearGroup.padicLevel` (LMFDB `gl2.level`): the level of a subgroup of a matrix
  group over `ℤ_ℓ`.
* `Matrix.GeneralLinearGroup.adelicReduction`: reduction modulo `N` of `∏_ℓ GL_n(ℤ_ℓ)`.
* `Matrix.GeneralLinearGroup.adelicLevel` (LMFDB `gl2.level`): the level of a subgroup of a matrix
  group over `ℤ̂`, inside `∏_ℓ GL_n(ℤ_ℓ) = GL_n(ℤ̂)`.

## Main results

* `Matrix.GeneralLinearGroup.exists_padicLevel_eq_pow`: the level of a subgroup of a matrix group
  over `ℤ_ℓ` is a power of `ℓ`, as soon as the subgroup is the inverse image of its reduction modulo
  some positive integer.
* `Matrix.GeneralLinearGroup.exists_inf_comap_map_padicReduction_eq` and
  `Matrix.GeneralLinearGroup.exists_inf_comap_map_adelicReduction_eq`: an open subgroup of a matrix
  group over `ℤ_ℓ` or `ℤ̂` is the inverse image of its reduction modulo some positive integer.
* `Matrix.GeneralLinearGroup.padicLevel_pos`,
  `Matrix.GeneralLinearGroup.inf_comap_map_padicReduction_padicLevel` and
  `Matrix.GeneralLinearGroup.exists_padicLevel_eq_pow_of_isOpen`: the level of an open subgroup over
  `ℤ_ℓ` is a positive power of `ℓ`, modulo which the subgroup is the inverse image of its reduction.
* `Matrix.GeneralLinearGroup.adelicLevel_pos` and
  `Matrix.GeneralLinearGroup.inf_comap_map_adelicReduction_adelicLevel`: the level of an open
  subgroup over `ℤ̂` is positive, and the subgroup is the inverse image of its reduction modulo it.
-/

open Filter Topology

namespace Matrix.GeneralLinearGroup

variable {n : Type*} [Fintype n] [DecidableEq n] (ℓ : ℕ) [Fact ℓ.Prime] (N : ℕ)

private lemma inf_comap_map_eq {Γ Q : Type*} [Group Γ] [Group Q] {f : Γ →* Q} {G H : Subgroup Γ}
    (hHG : H ≤ G) (hker : G ⊓ f.ker ≤ H) : G ⊓ (H.map f).comap f = H := by
  refine le_antisymm (fun g hg ↦ ?_) (le_inf hHG (Subgroup.le_comap_map f H))
  rcases Subgroup.mem_inf.mp hg with ⟨hgG, hg⟩
  rcases Subgroup.mem_map.mp (Subgroup.mem_comap.mp hg) with ⟨h, hh, hgh⟩
  have hk : h⁻¹ * g ∈ H := hker (Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem (hHG hh)) hgG, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgh, inv_mul_cancel]⟩)
  simpa using mul_mem hh hk

private lemma exists_inf_comap_map_eq {Γ : Type*} [Group Γ] [TopologicalSpace Γ] {Q : ℕ → Type*}
    [∀ N, Group (Q N)] (π : ∀ N, Γ →* Q N)
    (hπ : ∀ U ∈ 𝓝 (1 : Γ), ∃ N, 0 < N ∧ ∀ g, π N g = 1 → g ∈ U) {G H : Subgroup Γ} (hHG : H ≤ G)
    (hH : IsOpen (H.subgroupOf G : Set G)) : ∃ N, 0 < N ∧ G ⊓ (H.map (π N)).comap (π N) = H := by
  rcases isOpen_induced_iff.mp hH with ⟨U, hU, hUH⟩
  rcases hπ U (hU.mem_nhds ((Set.ext_iff.mp hUH 1).mpr (one_mem _))) with ⟨N, hN, hker⟩
  refine ⟨N, hN, inf_comap_map_eq hHG fun g hg ↦ ?_⟩
  rcases Subgroup.mem_inf.mp hg with ⟨hgG, hg⟩
  exact (Set.ext_iff.mp hUH ⟨g, hgG⟩).mp (hker g hg)

/-- **Reduction modulo `N`** of `GL_n(ℤ_ℓ)`: as `ℤ_ℓ / N ℤ_ℓ = ℤ / ℓ ^ v_ℓ(N) ℤ`, it reduces the
entries modulo `ℓ ^ v_ℓ(N)`. -/
noncomputable def padicReduction : GL n ℤ_[ℓ] →* GL n (ZMod (ℓ ^ N.factorization ℓ)) :=
  map (PadicInt.toZModPow (N.factorization ℓ))

omit [Fintype n] in
lemma map_toZModPow_eq_one_of_le {e e' : ℕ} (h : e ≤ e') {A : Matrix n n ℤ_[ℓ]}
    (hA : A.map (PadicInt.toZModPow e') = 1) : A.map (PadicInt.toZModPow e) = 1 := by
  rw [← PadicInt.zmod_cast_comp_toZModPow e e' h, RingHom.coe_comp, ← Matrix.map_map, hA,
    Matrix.map_one _ (map_zero _) (map_one _)]

lemma ker_map_toZModPow_mono {e e' : ℕ} (h : e ≤ e') :
    (map (n := n) (PadicInt.toZModPow (p := ℓ) e')).ker ≤ (map (PadicInt.toZModPow e)).ker :=
  fun _ hg ↦ Units.ext (map_toZModPow_eq_one_of_le ℓ h (congr_arg Units.val hg))

lemma exists_toZModPow_eq_imp_mem {x : ℤ_[ℓ]} {V : Set ℤ_[ℓ]} (hV : V ∈ 𝓝 x) :
    ∃ e : ℕ, ∀ y, PadicInt.toZModPow e y = PadicInt.toZModPow e x → y ∈ V := by
  rcases Metric.mem_nhds_iff.mp hV with ⟨ε, hε, hball⟩
  have hℓ : (1 : ℝ) < ℓ := by exact_mod_cast (Fact.out : ℓ.Prime).one_lt
  rcases exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hℓ) with ⟨e, he⟩
  refine ⟨e, fun y hy ↦ hball ?_⟩
  have hmem : y - x ∈ Ideal.span {(ℓ : ℤ_[ℓ]) ^ e} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, hy, sub_self]
  have hle : ‖y - x‖ ≤ (ℓ : ℝ) ^ (-(e : ℤ)) := (PadicInt.norm_le_pow_iff_mem_span_pow _ e).mpr hmem
  rw [zpow_neg, zpow_natCast, ← inv_pow] at hle
  rw [Metric.mem_ball, dist_eq_norm]
  exact lt_of_le_of_lt hle he

omit [Fintype n] in
lemma exists_map_toZModPow_eq_one_imp_mem {U : Set (Matrix n n ℤ_[ℓ])} (hU : U ∈ 𝓝 1) :
    ∃ e : ℕ, ∀ A : Matrix n n ℤ_[ℓ], A.map (PadicInt.toZModPow e) = 1 → A ∈ U := by
  have hdir :
      Directed (· ≥ ·) fun e : ℕ ↦ 𝓟 {A : Matrix n n ℤ_[ℓ] | A.map (PadicInt.toZModPow e) = 1} :=
    Antitone.directed_ge fun e e' h ↦ Filter.principal_mono.mpr fun A hA ↦
      map_toZModPow_eq_one_of_le ℓ h hA
  have hle : Filter.Tendsto (fun A : Matrix n n ℤ_[ℓ] ↦ A)
      (⨅ e : ℕ, 𝓟 {A : Matrix n n ℤ_[ℓ] | A.map (PadicInt.toZModPow e) = 1}) (𝓝 1) := by
    refine tendsto_pi_nhds.mpr fun i ↦ tendsto_pi_nhds.mpr fun j V hV ↦ ?_
    rcases exists_toZModPow_eq_imp_mem ℓ hV with ⟨e, he⟩
    refine Filter.mem_iInf_of_mem e (Filter.mem_principal.mpr fun A hA ↦ he _ ?_)
    have h₁ : A.map (PadicInt.toZModPow e) = (1 : Matrix n n ℤ_[ℓ]).map (PadicInt.toZModPow e) := by
      rw [Set.mem_ofPred_eq.mp hA, Matrix.map_one _ (map_zero _) (map_one _)]
    exact congr_fun (congr_fun h₁ i) j
  rcases (Filter.mem_iInf_of_directed hdir U).mp (hle hU) with ⟨e, he⟩
  exact ⟨e, fun A hA ↦ Filter.mem_principal.mp he hA⟩

lemma exists_map_toZModPow_eq_one_imp_mem_GL {U : Set (GL n ℤ_[ℓ])} (hU : U ∈ 𝓝 1) :
    ∃ e : ℕ, ∀ g : GL n ℤ_[ℓ], map (PadicInt.toZModPow e) g = 1 → g ∈ U := by
  rw [Units.isInducing_embedProduct.nhds_eq_comap, Filter.mem_comap] at hU
  rcases hU with ⟨t, ht, htU⟩
  rw [Units.embedProduct_apply, nhds_prod_eq, Filter.mem_prod_iff] at ht
  rcases ht with ⟨V, hV, W, hW, hVW⟩
  rcases exists_map_toZModPow_eq_one_imp_mem ℓ hV with ⟨e₁, he₁⟩
  rcases exists_map_toZModPow_eq_one_imp_mem ℓ (MulOpposite.continuous_op.continuousAt hW) with
    ⟨e₂, he₂⟩
  refine ⟨max e₁ e₂, fun g hg ↦ htU (hVW ⟨he₁ _ ?_, he₂ _ ?_⟩)⟩
  · exact congr_arg Units.val (ker_map_toZModPow_mono ℓ (le_max_left _ _) hg)
  · exact congr_arg Units.val
      (ker_map_toZModPow_mono ℓ (le_max_right _ _) (inv_mem (MonoidHom.mem_ker.mpr hg)))

lemma exists_padicReduction_eq_one_imp_mem {U : Set (GL n ℤ_[ℓ])} (hU : U ∈ 𝓝 1) :
    ∃ N, 0 < N ∧ ∀ g, padicReduction ℓ N g = 1 → g ∈ U := by
  rcases exists_map_toZModPow_eq_one_imp_mem_GL ℓ hU with ⟨e, he⟩
  refine ⟨ℓ ^ e, pow_pos (Fact.out : ℓ.Prime).pos _, ?_⟩
  rwa [padicReduction, (Fact.out : ℓ.Prime).factorization_pow, Finsupp.single_eq_same]

section Padic

variable (G : Subgroup (GL n ℤ_[ℓ])) {H : Subgroup (GL n ℤ_[ℓ])} (hHG : H ≤ G)
  (hH : IsOpen (H.subgroupOf G : Set G))

variable (H) in
/-- The **level** (LMFDB `gl2.level`) of a subgroup `H` of a matrix group `G ≤ GL_n(ℤ_ℓ)`: the least
positive integer `N` such that `H` is the inverse image in `G` of its reduction modulo `N`, that is,
`H = G ∩ π_N⁻¹(π_N(H))`; for a subgroup of `GL_n(ℤ_ℓ)` itself, `G = ⊤`. It is a power of `ℓ`
(`exists_padicLevel_eq_pow`), and positive for an open subgroup of `G` (`padicLevel_pos`). It is
`0` when there is no such `N`, as for a subgroup that is not open in `G`. -/
noncomputable def padicLevel : ℕ :=
  sInf {N : ℕ | 0 < N ∧ G ⊓ (H.map (padicReduction ℓ N)).comap (padicReduction ℓ N) = H}

/-- **The level of a subgroup of a matrix group over `ℤ_ℓ` is a power of `ℓ`** (LMFDB `gl2.level`),
as soon as the subgroup is the inverse image of its reduction modulo some positive integer. -/
lemma exists_padicLevel_eq_pow
    (h : ∃ N, 0 < N ∧ G ⊓ (H.map (padicReduction ℓ N)).comap (padicReduction ℓ N) = H) :
    ∃ k, padicLevel ℓ G H = ℓ ^ k := by
  have hmem : padicLevel ℓ G H ∈
      {N : ℕ | 0 < N ∧ G ⊓ (H.map (padicReduction ℓ N)).comap (padicReduction ℓ N) = H} :=
    Nat.sInf_mem h
  refine ⟨(padicLevel ℓ G H).factorization ℓ, le_antisymm ?_ (Nat.ordProj_le ℓ hmem.1.ne')⟩
  have he : (ℓ ^ (padicLevel ℓ G H).factorization ℓ).factorization ℓ =
      (padicLevel ℓ G H).factorization ℓ := by
    rw [(Fact.out : ℓ.Prime).factorization_pow, Finsupp.single_eq_same]
  refine Nat.sInf_le ⟨pow_pos (Fact.out : ℓ.Prime).pos _, ?_⟩
  rw [padicReduction, he]
  exact hmem.2

include hHG hH in
/-- **An open subgroup of a matrix group `G ≤ GL_n(ℤ_ℓ)` is the inverse image in `G` of its
reduction modulo some positive integer**, so it has a level. -/
lemma exists_inf_comap_map_padicReduction_eq :
    ∃ N, 0 < N ∧ G ⊓ (H.map (padicReduction ℓ N)).comap (padicReduction ℓ N) = H :=
  exists_inf_comap_map_eq _ (fun _ ↦ exists_padicReduction_eq_one_imp_mem ℓ) hHG hH

include hHG hH in
/-- **The level of an open subgroup of a matrix group over `ℤ_ℓ` is positive.** -/
lemma padicLevel_pos : 0 < padicLevel ℓ G H :=
  (Nat.sInf_mem (exists_inf_comap_map_padicReduction_eq ℓ G hHG hH) : padicLevel ℓ G H ∈ _).1

include hHG hH in
/-- **An open subgroup of a matrix group over `ℤ_ℓ` is the inverse image of its reduction modulo
its level.** -/
lemma inf_comap_map_padicReduction_padicLevel : G ⊓
    (H.map (padicReduction ℓ (padicLevel ℓ G H))).comap (padicReduction ℓ (padicLevel ℓ G H)) = H :=
  (Nat.sInf_mem (exists_inf_comap_map_padicReduction_eq ℓ G hHG hH) : padicLevel ℓ G H ∈ _).2

include hHG hH in
/-- **The level of an open subgroup of a matrix group over `ℤ_ℓ` is a power of `ℓ`.** -/
lemma exists_padicLevel_eq_pow_of_isOpen : ∃ k, padicLevel ℓ G H = ℓ ^ k :=
  exists_padicLevel_eq_pow ℓ G (exists_inf_comap_map_padicReduction_eq ℓ G hHG hH)

end Padic

section Adelic

variable (G : Subgroup (∀ ℓ : Nat.Primes, GL n ℤ_[ℓ])) {H : Subgroup (∀ ℓ : Nat.Primes, GL n ℤ_[ℓ])}
  (hHG : H ≤ G) (hH : IsOpen (H.subgroupOf G : Set G))

/-- **Reduction modulo `N`** of `GL_n(ℤ̂) = ∏_ℓ GL_n(ℤ_ℓ)`: reduction modulo `ℓ ^ v_ℓ(N)` at each
prime `ℓ`, with values in `∏_ℓ GL_n(ℤ / ℓ ^ v_ℓ(N) ℤ) = GL_n(ℤ / N ℤ)`. -/
noncomputable def adelicReduction :
    (∀ ℓ : Nat.Primes, GL n ℤ_[ℓ]) →* ∀ ℓ : Nat.Primes, GL n (ZMod ((ℓ : ℕ) ^ N.factorization ℓ)) :=
  MonoidHom.pi fun ℓ ↦ (padicReduction ℓ N).comp (Pi.evalMonoidHom _ ℓ)

variable (H) in
/-- The **level** (LMFDB `gl2.level`) of a subgroup `H` of a matrix group
`G ≤ GL_n(ℤ̂) = ∏_ℓ GL_n(ℤ_ℓ)`: the least positive integer `N` such that `H` is the inverse image in
`G` of its reduction modulo `N`; for a subgroup of `GL_n(ℤ̂)` itself, `G = ⊤`. It is positive for an
open subgroup of `G` (`adelicLevel_pos`), and `0` when there is no such `N`, as for a subgroup that
is not open in `G`. -/
noncomputable def adelicLevel : ℕ :=
  sInf {N : ℕ | 0 < N ∧ G ⊓ (H.map (adelicReduction N)).comap (adelicReduction N) = H}

lemma exists_adelicReduction_eq_one_imp_mem {U : Set (∀ ℓ : Nat.Primes, GL n ℤ_[ℓ])}
    (hU : U ∈ 𝓝 1) : ∃ N, 0 < N ∧ ∀ g, adelicReduction N g = 1 → g ∈ U := by
  rw [nhds_pi, Filter.mem_pi'] at hU
  rcases hU with ⟨I, t, ht, htU⟩
  choose e he using fun ℓ : Nat.Primes ↦ exists_map_toZModPow_eq_one_imp_mem_GL ℓ (ht ℓ)
  have hN : 0 < ∏ ℓ ∈ I, (ℓ : ℕ) ^ e ℓ := Finset.prod_pos fun ℓ _ ↦ pow_pos ℓ.prop.pos _
  refine ⟨_, hN, fun g hg ↦ htU fun ℓ hℓ ↦ he ℓ (g ℓ) ?_⟩
  have hgℓ : g ℓ ∈ (padicReduction ℓ (∏ ℓ ∈ I, (ℓ : ℕ) ^ e ℓ)).ker := congr_fun hg ℓ
  exact ker_map_toZModPow_mono ℓ ((ℓ.prop.pow_dvd_iff_le_factorization hN.ne').mp
    (Finset.dvd_prod_of_mem _ hℓ)) hgℓ

include hHG hH in
/-- **An open subgroup of a matrix group `G ≤ GL_n(ℤ̂)` is the inverse image in `G` of its
reduction modulo some positive integer**, so it has a level. -/
lemma exists_inf_comap_map_adelicReduction_eq :
    ∃ N, 0 < N ∧ G ⊓ (H.map (adelicReduction N)).comap (adelicReduction N) = H :=
  exists_inf_comap_map_eq _ (fun _ ↦ exists_adelicReduction_eq_one_imp_mem) hHG hH

include hHG hH in
/-- **The level of an open subgroup of a matrix group over `ℤ̂` is positive.** -/
lemma adelicLevel_pos : 0 < adelicLevel G H :=
  (Nat.sInf_mem (exists_inf_comap_map_adelicReduction_eq G hHG hH) : adelicLevel G H ∈ _).1

include hHG hH in
/-- **An open subgroup of a matrix group over `ℤ̂` is the inverse image of its reduction modulo its
level.** -/
lemma inf_comap_map_adelicReduction_adelicLevel :
    G ⊓ (H.map (adelicReduction (adelicLevel G H))).comap (adelicReduction (adelicLevel G H)) = H :=
  (Nat.sInf_mem (exists_inf_comap_map_adelicReduction_eq G hHG hH) : adelicLevel G H ∈ _).2

end Adelic

end Matrix.GeneralLinearGroup
