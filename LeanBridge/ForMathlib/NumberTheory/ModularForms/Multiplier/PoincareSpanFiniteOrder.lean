import LeanBridge.ForMathlib.NumberTheory.ModularForms.Multiplier.PoincareSpanCuspForm

/-!
# Cusp forms of a multiplier of finite order

Let `G` be a subgroup of finite index of `SL(2, ℤ)` and `v : G → S¹` a multiplier of finite
order, that is, with kernel of finite index in `G` (a nebentypus character, for instance). A cusp
form of weight `k` and multiplier `v` on `G` is then a cusp form of weight `k`, with trivial
multiplier, on the kernel `H = ker v`, a subgroup of finite index of `SL(2, ℤ)` with the same
cusps. The finite dimension of the space `S_k(G, v)` and its spanning by the Poincaré series
(LMFDB `specialfunction.poincare`) hold for every multiplier, of finite or infinite order
(`FiniteDimensional.lean`, `PoincareSpanMultiplier.lean`).

## Main results

* `ModularForm.multiplierCuspSpace_le_multiplierCuspSpace_ker`: `S_k(G, v) ⊆ S_k(ker v)`.
* The instance `FiniteIndex (H.map G.subtype)` for `H` of finite index in `G` of finite index
  (such as `ker v`).
-/

open Matrix SpecialLinearGroup Subgroup

open scoped MatrixGroups ModularForm

namespace ModularForm

variable {G : Subgroup SL(2, ℤ)} (v : G →* Circle) {k : ℤ}

/-- **Cusp forms of a multiplier are cusp forms on its kernel**: a cusp form of weight `k` and
multiplier `v` on `G` is a cusp form of weight `k` and trivial multiplier on the kernel of `v`,
as a subgroup of `SL(2, ℤ)`. -/
lemma multiplierCuspSpace_le_multiplierCuspSpace_ker : multiplierCuspSpace k (multiplierMapGL v) ≤
    multiplierCuspSpace k (multiplierMapGL (1 : v.ker.map G.subtype →* Circle)) := by
  have hle : (v.ker.map G.subtype).map (mapGL ℝ) ≤ G.map (mapGL ℝ) :=
    Subgroup.map_mono (Subgroup.map_subtype_le _)
  refine fun f hf ↦ ⟨⟨hf.1.1, fun γ' ↦ ?_, fun hc ↦ hf.1.2.2 (hc.mono hle)⟩,
    fun hc ↦ hf.2 (hc.mono hle)⟩
  rcases γ' with ⟨_, _, ⟨g, hg, rfl⟩, rfl⟩
  have h1 : f ∣[k] (g : SL(2, ℤ)) = (v g : ℂ) • f := slash_eq_smul_of_mem_multiplierCuspSpace hf g
  rwa [MonoidHom.mem_ker.mp hg, Circle.coe_one] at h1

variable [G.FiniteIndex]

instance {H : Subgroup G} [H.FiniteIndex] : (H.map G.subtype).FiniteIndex :=
  ⟨by
    rw [index_map_subtype]
    exact mul_ne_zero FiniteIndex.index_ne_zero FiniteIndex.index_ne_zero⟩

end ModularForm
