import Mathlib.Algebra.Order.Field.Basic
import Mathlib.LinearAlgebra.RootSystem.IsValuedIn
import Mathlib.Order.Interval.Set.ProjIcc

/-!
# Littelmann paths

Let `P` be a root pairing over `ℚ`, with weight space `M` and coweight space `N`: for the root
system of a semisimple Lie algebra `𝔤`, `M` is the rational span `P ⊗ ℚ` of the weight lattice in
the dual of a Cartan subalgebra, and the weight lattice is the set of integral weights, the
elements of `M` whose pairing with every coroot is an integer. A Littelmann path is a
piecewise-linear map `π : [0, 1] ∩ ℚ → M` with `π(0) = 0` and `π(1)` an integral weight.

For a root `αᵢ`, the function `Hᵢ(t) = ⟨π(t), αᵢ^∨⟩` is piecewise linear, so it attains a minimum
`mᵢ` on `[0, 1] ∩ ℚ`, at a breakpoint. Littelmann's path crystal has weight `wt(π) = π(1)` and
`εᵢ(π) = -mᵢ`, `φᵢ(π) = Hᵢ(1) - mᵢ`, so that `φᵢ(π) - εᵢ(π) = ⟨wt(π), αᵢ^∨⟩`.

Littelmann's root operators reflect parts of the path by `sᵢ`. In closed form, the lowering
operator is `fᵢ π(t) = π(t) - min(1, max(0, min_{s ≥ t} Hᵢ(s) - mᵢ)) αᵢ` when `φᵢ(π) ≥ 1` (and
`fᵢ π = 0` otherwise), and the raising operator is
`eᵢ π(t) = π(t) + min(1, max(0, mᵢ + 1 - min_{s ≤ t} Hᵢ(s))) αᵢ` when `εᵢ(π) ≥ 1`. The future and
past minima of `Hᵢ` are piecewise linear, so `fᵢ π` and `eᵢ π` are again Littelmann paths, of
weights `wt(π) - αᵢ` and `wt(π) + αᵢ`, with `εᵢ(fᵢ π) = εᵢ(π) + 1`, `φᵢ(fᵢ π) = φᵢ(π) - 1`,
`εᵢ(eᵢ π) = εᵢ(π) - 1` and `φᵢ(eᵢ π) = φᵢ(π) + 1`. For paths whose local minima of `Hᵢ` are
integers, `fᵢ` and `eᵢ` reflect `π` between two times, as in `RootPairing.LittelmannPath.reflect`.

The remaining crystal axiom `eᵢ fᵢ π = π` and Littelmann's theorem that the paths obtained from
the straight-line path to a dominant weight `λ` form the highest weight crystal `B(λ)` are not
formalised here.

## Main definitions

* `RootPairing.IsIntegralWeight`: integral weights.
* `RootPairing.IsBreakpointSet` and `RootPairing.IsPiecewiseLinearPath`: piecewise-linear maps
  `[0, 1] ∩ ℚ → M`.
* `RootPairing.LittelmannPath` (LMFDB `crystals.littelmann_path`): Littelmann paths.
* `RootPairing.LittelmannPath.height`: the function `Hᵢ(t) = ⟨π(t), αᵢ^∨⟩`.
* `RootPairing.LittelmannPath.minHeight`: its minimum `mᵢ`.
* `RootPairing.LittelmannPath.wt`, `RootPairing.LittelmannPath.ε` and
  `RootPairing.LittelmannPath.φ` (LMFDB `crystals.littelmann_path`): the crystal data of a path.
* `RootPairing.LittelmannPath.reflectFun` and `RootPairing.LittelmannPath.reflect`: the reflection
  of a part of a path.
* `RootPairing.LittelmannPath.futureMinHeight` and `RootPairing.LittelmannPath.pastMinHeight`: the
  minima of `Hᵢ` after and before a time.
* `RootPairing.LittelmannPath.lowerCoeff` and `RootPairing.LittelmannPath.raiseCoeff`: the
  coefficients of `αᵢ` in the root operators.
* `RootPairing.LittelmannPath.lowerPath`, `RootPairing.LittelmannPath.raisePath`,
  `RootPairing.LittelmannPath.lower` and `RootPairing.LittelmannPath.raise` (LMFDB
  `crystals.littelmann_path`): Littelmann's lowering and raising operators `fᵢ` and `eᵢ`.
* `RootPairing.straightLinePath`: the straight-line path `t ↦ t λ`.

## Main results

* `RootPairing.LittelmannPath.isLeast_minHeight`: `mᵢ` is the least value of `Hᵢ`.
* `RootPairing.LittelmannPath.φ_sub_ε`: `φᵢ(π) - εᵢ(π) = ⟨wt(π), αᵢ^∨⟩`.
* `RootPairing.LittelmannPath.ε_lowerPath`, `RootPairing.LittelmannPath.φ_lowerPath`,
  `RootPairing.LittelmannPath.ε_raisePath` and `RootPairing.LittelmannPath.φ_raisePath`: the root
  operators change `εᵢ` and `φᵢ` by one.
-/

open Set

namespace RootPairing

variable {ι M N : Type*} [AddCommGroup M] [Module ℚ M] [AddCommGroup N] [Module ℚ N]
  (P : RootPairing ι ℚ M N)

/-- An element `x` of the weight space of a root pairing `P` over `ℚ` is an **integral weight** if
its pairing `⟨x, α^∨⟩` with every coroot is an integer. For the root system of a semisimple Lie
algebra, the integral weights form the weight lattice. -/
def IsIntegralWeight (x : M) : Prop :=
  ∀ i, ∃ n : ℤ, P.toLinearMap x (P.coroot i) = n

/-- A finite set `S` of points of `[0, 1] ∩ ℚ` is a **set of breakpoints** of a map
`f : [0, 1] ∩ ℚ → M` if it contains `0` and `1` and `f` is affine between any two consecutive
points of `S`. -/
def IsBreakpointSet (f : Icc (0 : ℚ) 1 → M) (S : Finset (Icc (0 : ℚ) 1)) : Prop :=
  ⊥ ∈ S ∧ ⊤ ∈ S ∧ ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ s ∈ S, s ≤ a ∨ b ≤ s) → ∀ t, a ≤ t → t ≤ b →
    f t = f a + (((t : ℚ) - a) / ((b : ℚ) - a)) • (f b - f a)

/-- A map `f : [0, 1] ∩ ℚ → M` is **piecewise linear** if it has a finite set of breakpoints:
there is a finite set `S` containing `0` and `1` such that `f` is affine between any two
consecutive points of `S`. -/
def IsPiecewiseLinearPath (f : Icc (0 : ℚ) 1 → M) : Prop :=
  ∃ S, IsBreakpointSet f S

lemma IsBreakpointSet.exists_le_le {f : Icc (0 : ℚ) 1 → M} {S : Finset (Icc (0 : ℚ) 1)}
    (hS : IsBreakpointSet f S) (t : Icc (0 : ℚ) 1) : ∃ a ∈ S, ∃ b ∈ S, a ≤ t ∧ t ≤ b ∧
      ∀ y, a ≤ y → y ≤ b → f y = f a + (((y : ℚ) - a) / ((b : ℚ) - a)) • (f b - f a) := by
  classical
  rcases hS with ⟨h0, h1, haff⟩
  have hA : (S.filter (· ≤ t)).Nonempty := ⟨⊥, Finset.mem_filter.mpr ⟨h0, bot_le⟩⟩
  have hB : (S.filter (t ≤ ·)).Nonempty := ⟨⊤, Finset.mem_filter.mpr ⟨h1, le_top⟩⟩
  have ha : (S.filter (· ≤ t)).max' hA ∈ S.filter (· ≤ t) := Finset.max'_mem _ hA
  have hb : (S.filter (t ≤ ·)).min' hB ∈ S.filter (t ≤ ·) := Finset.min'_mem _ hB
  rw [Finset.mem_filter] at ha hb
  refine ⟨_, ha.1, _, hb.1, ha.2, hb.2, fun y hay hyb ↦ ?_⟩
  rcases (ha.2.trans hb.2).lt_or_eq with hab | hab
  · refine haff _ ha.1 _ hb.1 hab (fun s hs ↦ ?_) y hay hyb
    rcases le_or_gt s t with hst | hst
    · exact Or.inl (Finset.le_max' _ s (Finset.mem_filter.mpr ⟨hs, hst⟩))
    · exact Or.inr (Finset.min'_le _ s (Finset.mem_filter.mpr ⟨hs, hst.le⟩))
  · have hya : y = (S.filter (· ≤ t)).max' hA := le_antisymm (hab ▸ hyb) hay
    rw [← hya, sub_self, zero_div, zero_smul, add_zero]

lemma eq_add_smul_of_le {f : Icc (0 : ℚ) 1 → M} {a' b' a b : Icc (0 : ℚ) 1}
    (hf : ∀ t, a' ≤ t → t ≤ b' → f t = f a' + (((t : ℚ) - a') / ((b' : ℚ) - a')) • (f b' - f a'))
    (ha : a' ≤ a) (hab : a < b) (hb : b ≤ b') (t : Icc (0 : ℚ) 1) (hat : a ≤ t) (htb : t ≤ b) :
    f t = f a + (((t : ℚ) - a) / ((b : ℚ) - a)) • (f b - f a) := by
  have ha₁ : (a' : ℚ) ≤ a := ha
  have hab₁ : (a : ℚ) < b := hab
  have hb₁ : (b : ℚ) ≤ b' := hb
  have hl : ((t : ℚ) - a') / ((b' : ℚ) - a') = ((a : ℚ) - a') / ((b' : ℚ) - a') +
      (((t : ℚ) - a) / ((b : ℚ) - a)) *
        (((b : ℚ) - a') / ((b' : ℚ) - a') - ((a : ℚ) - a') / ((b' : ℚ) - a')) := by
    have h₁ : (b : ℚ) - a ≠ 0 := sub_ne_zero.mpr hab₁.ne'
    have h₂ : (b' : ℚ) - a' ≠ 0 := sub_ne_zero.mpr (ha₁.trans_lt (hab₁.trans_le hb₁)).ne'
    field_simp
    ring1
  rw [hf t (ha.trans hat) (htb.trans hb), hf a ha (hab.le.trans hb), hf b (ha.trans hab.le) hb, hl]
  module

lemma exists_segment {S T : Finset (Icc (0 : ℚ) 1)} (h0 : ⊥ ∈ S) (h1 : ⊤ ∈ S) (hST : S ⊆ T)
    {c d : Icc (0 : ℚ) 1} (hcd : c < d) (hcons : ∀ s ∈ T, s ≤ c ∨ d ≤ s) :
    ∃ a ∈ S, ∃ b ∈ S, a ≤ c ∧ d ≤ b ∧ a < b ∧ ∀ s ∈ S, s ≤ a ∨ b ≤ s := by
  classical
  have hA : (S.filter (· ≤ c)).Nonempty := ⟨⊥, Finset.mem_filter.mpr ⟨h0, bot_le⟩⟩
  have hB : (S.filter (d ≤ ·)).Nonempty := ⟨⊤, Finset.mem_filter.mpr ⟨h1, le_top⟩⟩
  have ha : (S.filter (· ≤ c)).max' hA ∈ S.filter (· ≤ c) := Finset.max'_mem _ hA
  have hb : (S.filter (d ≤ ·)).min' hB ∈ S.filter (d ≤ ·) := Finset.min'_mem _ hB
  rw [Finset.mem_filter] at ha hb
  refine ⟨_, ha.1, _, hb.1, ha.2, hb.2, (ha.2.trans_lt hcd).trans_le hb.2, fun s hs ↦ ?_⟩
  rcases hcons s (hST hs) with hsc | hds
  · exact Or.inl (Finset.le_max' _ s (Finset.mem_filter.mpr ⟨hs, hsc⟩))
  · exact Or.inr (Finset.min'_le _ s (Finset.mem_filter.mpr ⟨hs, hds⟩))

lemma le_apply_of_affine {f : Icc (0 : ℚ) 1 → ℚ} {a b x : Icc (0 : ℚ) 1} {m : ℚ}
    (hx : f x = f a + (((x : ℚ) - a) / ((b : ℚ) - a)) • (f b - f a)) (hax : a ≤ x) (hxb : x ≤ b)
    (ha : m ≤ f a) (hb : m ≤ f b) : m ≤ f x := by
  have hax₁ : (a : ℚ) ≤ x := hax
  have hxb₁ : (x : ℚ) ≤ b := hxb
  have hl₀ : 0 ≤ ((x : ℚ) - a) / ((b : ℚ) - a) :=
    div_nonneg (sub_nonneg.mpr hax₁) (sub_nonneg.mpr (hax₁.trans hxb₁))
  have hl₁ : ((x : ℚ) - a) / ((b : ℚ) - a) ≤ 1 :=
    div_le_one_of_le₀ (sub_le_sub_right hxb₁ _) (sub_nonneg.mpr (hax₁.trans hxb₁))
  rw [hx, smul_eq_mul]
  nlinarith [mul_nonneg hl₀ (sub_nonneg.mpr hb),
    mul_nonneg (sub_nonneg.mpr hl₁) (sub_nonneg.mpr ha)]

lemma IsBreakpointSet.mono {f : Icc (0 : ℚ) 1 → M} {S T : Finset (Icc (0 : ℚ) 1)}
    (hS : IsBreakpointSet f S) (hST : S ⊆ T) : IsBreakpointSet f T := by
  refine ⟨hST hS.1, hST hS.2.1, fun c _ d _ hcd hcons t hct htd ↦ ?_⟩
  rcases exists_segment hS.1 hS.2.1 hST hcd hcons with ⟨a, ha, b, hb, hac, hdb, hab, habS⟩
  exact eq_add_smul_of_le (hS.2.2 a ha b hb hab habS) hac hcd hdb t hct htd

lemma IsPiecewiseLinearPath.add {f g : Icc (0 : ℚ) 1 → M} (hf : IsPiecewiseLinearPath f)
    (hg : IsPiecewiseLinearPath g) : IsPiecewiseLinearPath (f + g) := by
  classical
  rcases hf with ⟨S, hS⟩
  rcases hg with ⟨T, hT⟩
  have hS' : IsBreakpointSet f (S ∪ T) := hS.mono Finset.subset_union_left
  have hT' : IsBreakpointSet g (S ∪ T) := hT.mono Finset.subset_union_right
  refine ⟨S ∪ T, hS'.1, hS'.2.1, fun a ha b hb hab hcons t hat htb ↦ ?_⟩
  rw [Pi.add_apply, Pi.add_apply, Pi.add_apply, hS'.2.2 a ha b hb hab hcons t hat htb,
    hT'.2.2 a ha b hb hab hcons t hat htb]
  module

lemma IsPiecewiseLinearPath.smul_const {c : Icc (0 : ℚ) 1 → ℚ} (hc : IsPiecewiseLinearPath c)
    (v : M) : IsPiecewiseLinearPath fun t ↦ c t • v := by
  rcases hc with ⟨S, h0, h1, haff⟩
  refine ⟨S, h0, h1, fun a ha b hb hab hcons t hat htb ↦ ?_⟩
  dsimp only
  rw [haff a ha b hb hab hcons t hat htb, smul_eq_mul]
  module

lemma IsPiecewiseLinearPath.max_zero {f : Icc (0 : ℚ) 1 → ℚ} (hf : IsPiecewiseLinearPath f) :
    IsPiecewiseLinearPath fun t ↦ max 0 (f t) := by
  classical
  rcases hf with ⟨S, hS⟩
  let cross : Icc (0 : ℚ) 1 × Icc (0 : ℚ) 1 → Icc (0 : ℚ) 1 := fun p ↦
    projIcc 0 1 zero_le_one ((p.1 : ℚ) + f p.1 / (f p.1 - f p.2) * ((p.2 : ℚ) - p.1))
  have hT : IsBreakpointSet f (S ∪ (S ×ˢ S).image cross) := hS.mono Finset.subset_union_left
  refine ⟨S ∪ (S ×ˢ S).image cross, hT.1, hT.2.1, fun c hc d hd hcd hcons t hct htd ↦ ?_⟩
  have hft : f t = f c + (((t : ℚ) - c) / ((d : ℚ) - c)) • (f d - f c) :=
    hT.2.2 c hc d hd hcd hcons t hct htd
  have hc₁ : (c : ℚ) ≤ t := hct
  have hd₁ : (t : ℚ) ≤ d := htd
  have hcd₁ : (c : ℚ) < d := hcd
  have hl₀ : 0 ≤ ((t : ℚ) - c) / ((d : ℚ) - c) :=
    div_nonneg (sub_nonneg.mpr hc₁) (sub_nonneg.mpr hcd₁.le)
  have hl₁ : ((t : ℚ) - c) / ((d : ℚ) - c) ≤ 1 :=
    div_le_one_of_le₀ (sub_le_sub_right hd₁ _) (sub_nonneg.mpr hcd₁.le)
  rw [smul_eq_mul] at hft
  dsimp only
  by_cases hsign : f c * f d < 0
  · exfalso
    rcases exists_segment hS.1 hS.2.1 Finset.subset_union_left hcd hcons with
      ⟨a, ha, b, hb, hac, hdb, hab, habS⟩
    have hab₁ : (a : ℚ) < b := hab
    have hac₁ : (a : ℚ) ≤ c := hac
    have hdb₁ : (d : ℚ) ≤ b := hdb
    have hba : (b : ℚ) - a ≠ 0 := sub_ne_zero.mpr hab₁.ne'
    have hfab (x : Icc (0 : ℚ) 1) (hax : a ≤ x) (hxb : x ≤ b) :
        f x = f a + (((x : ℚ) - a) / ((b : ℚ) - a)) * (f b - f a) :=
      (hS.2.2 a ha b hb hab habS x hax hxb).trans (by rw [smul_eq_mul])
    have hfc : f c = f a + (((c : ℚ) - a) / ((b : ℚ) - a)) * (f b - f a) :=
      hfab c hac (hcd.le.trans hdb)
    have hfd : f d = f a + (((d : ℚ) - a) / ((b : ℚ) - a)) * (f b - f a) :=
      hfab d (hac.trans hcd.le) hdb
    have hD : f a - f b ≠ 0 := by
      intro hD
      rw [sub_eq_zero.mp hD, sub_self, mul_zero, add_zero] at hfc hfd
      rw [hfc, hfd] at hsign
      exact (mul_self_nonneg (f b)).not_gt hsign
    have hfx (x : Icc (0 : ℚ) 1) (hax : a ≤ x) (hxb : x ≤ b) : f x = (f b - f a) *
        (((x : ℚ) - a) / ((b : ℚ) - a) - f a / (f a - f b)) := by
      rw [hfab x hax hxb]
      field_simp
      ring1
    have hprod : (((c : ℚ) - a) / ((b : ℚ) - a) - f a / (f a - f b)) *
        (((d : ℚ) - a) / ((b : ℚ) - a) - f a / (f a - f b)) < 0 := by
      have h : f c * f d = (f b - f a) ^ 2 * ((((c : ℚ) - a) / ((b : ℚ) - a) - f a / (f a - f b)) *
          (((d : ℚ) - a) / ((b : ℚ) - a) - f a / (f a - f b))) := by
        rw [hfx c hac (hcd.le.trans hdb), hfx d (hac.trans hcd.le) hdb]
        ring1
      rw [h] at hsign
      exact neg_of_mul_neg_right hsign (sq_nonneg _)
    have hμ : ((c : ℚ) - a) / ((b : ℚ) - a) < ((d : ℚ) - a) / ((b : ℚ) - a) :=
      div_lt_div_of_pos_right (sub_lt_sub_right hcd₁ _) (sub_pos.mpr hab₁)
    have h₁ : ((c : ℚ) - a) / ((b : ℚ) - a) < f a / (f a - f b) := by nlinarith
    have h₂ : f a / (f a - f b) < ((d : ℚ) - a) / ((b : ℚ) - a) := by nlinarith
    rw [div_lt_iff₀ (sub_pos.mpr hab₁)] at h₁
    rw [lt_div_iff₀ (sub_pos.mpr hab₁)] at h₂
    have hz : (a : ℚ) + f a / (f a - f b) * ((b : ℚ) - a) ∈ Icc (0 : ℚ) 1 :=
      ⟨by linarith [c.2.1], by linarith [d.2.2]⟩
    have hzT : cross (a, b) ∈ S ∪ (S ×ˢ S).image cross :=
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_product.mpr ⟨ha, hb⟩))
    have hzv : (cross (a, b) : ℚ) = a + f a / (f a - f b) * ((b : ℚ) - a) := by
      simp only [cross, projIcc_of_mem _ hz]
    rcases hcons _ hzT with h | h
    · have h' : (cross (a, b) : ℚ) ≤ c := h
      linarith
    · have h' : (d : ℚ) ≤ cross (a, b) := h
      linarith
  · rcases mul_nonneg_iff.mp (not_lt.mp hsign) with ⟨hfc, hfd⟩ | ⟨hfc, hfd⟩
    · have hft₀ : 0 ≤ f t := by
        rw [hft]
        nlinarith
      rw [max_eq_right hft₀, max_eq_right hfc, max_eq_right hfd, hft, smul_eq_mul]
    · have hft₀ : f t ≤ 0 := by
        rw [hft]
        nlinarith
      rw [max_eq_left hft₀, max_eq_left hfc, max_eq_left hfd, sub_self, smul_zero, add_zero]

lemma IsPiecewiseLinearPath.exists_eq {f : Icc (0 : ℚ) 1 → ℚ} (hf : IsPiecewiseLinearPath f) {y : ℚ}
    (h0 : f ⊥ ≤ y) (h1 : y ≤ f ⊤) : ∃ t, f t = y := by
  classical
  rcases hf with ⟨S, hS⟩
  have hA : (S.filter (f · ≤ y)).Nonempty := ⟨⊥, Finset.mem_filter.mpr ⟨hS.1, h0⟩⟩
  have ha : (S.filter (f · ≤ y)).max' hA ∈ S.filter (f · ≤ y) := Finset.max'_mem _ hA
  rw [Finset.mem_filter] at ha
  have hA' : ∃ a ∈ S, f a ≤ y ∧ ∀ s ∈ S, f s ≤ y → s ≤ a :=
    ⟨_, ha.1, ha.2, fun s hs hsy ↦ Finset.le_max' _ s (Finset.mem_filter.mpr ⟨hs, hsy⟩)⟩
  rcases hA' with ⟨a, haS, hay', hamax⟩
  rcases hay'.lt_or_eq with hay | hay
  · have hat : a < ⊤ := lt_of_le_of_ne le_top fun h ↦ (h ▸ hay).not_ge h1
    have hB : (S.filter (a < ·)).Nonempty := ⟨⊤, Finset.mem_filter.mpr ⟨hS.2.1, hat⟩⟩
    have hb : (S.filter (a < ·)).min' hB ∈ S.filter (a < ·) := Finset.min'_mem _ hB
    rw [Finset.mem_filter] at hb
    have hB' : ∃ b ∈ S, a < b ∧ ∀ s ∈ S, a < s → b ≤ s :=
      ⟨_, hb.1, hb.2, fun s hs has ↦ Finset.min'_le _ s (Finset.mem_filter.mpr ⟨hs, has⟩)⟩
    rcases hB' with ⟨b, hbS, hab, hbmin⟩
    have hby : y < f b := by
      by_contra hby
      exact hab.not_ge (hamax b hbS (not_lt.mp hby))
    have haff : ∀ x, a ≤ x → x ≤ b → f x = f a + (((x : ℚ) - a) / ((b : ℚ) - a)) • (f b - f a) :=
      hS.2.2 a haS b hbS hab fun s hs ↦ (le_or_gt s a).imp_right (hbmin s hs)
    have hab₁ : (a : ℚ) < b := hab
    have hfab : 0 < f b - f a := by linarith
    have hl₀ : 0 ≤ (y - f a) / (f b - f a) := div_nonneg (by linarith) hfab.le
    have hl₁ : (y - f a) / (f b - f a) ≤ 1 := div_le_one_of_le₀ (by linarith) hfab.le
    have hτa : (a : ℚ) ≤ a + (y - f a) / (f b - f a) * ((b : ℚ) - a) := by nlinarith
    have hτb : (a : ℚ) + (y - f a) / (f b - f a) * ((b : ℚ) - a) ≤ b := by nlinarith
    let t : Icc (0 : ℚ) 1 := ⟨_, a.2.1.trans hτa, hτb.trans b.2.2⟩
    refine ⟨t, ?_⟩
    have hl : ((t : ℚ) - a) / ((b : ℚ) - a) = (y - f a) / (f b - f a) := by
      have hba : (b : ℚ) - a ≠ 0 := sub_ne_zero.mpr hab₁.ne'
      simp only [t]
      field_simp
      ring1
    rw [haff t (Subtype.coe_le_coe.mp hτa) (Subtype.coe_le_coe.mp hτb), smul_eq_mul, hl,
      div_mul_cancel₀ _ hfab.ne']
    ring1
  · exact ⟨_, hay⟩

lemma isPiecewiseLinearPath_const (v : M) : IsPiecewiseLinearPath fun _ : Icc (0 : ℚ) 1 ↦ v :=
  ⟨{⊥, ⊤}, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_singleton_self _),
    fun _ _ _ _ _ _ _ _ _ ↦ by rw [sub_self, smul_zero, add_zero]⟩

lemma IsPiecewiseLinearPath.neg {f : Icc (0 : ℚ) 1 → M} (hf : IsPiecewiseLinearPath f) :
    IsPiecewiseLinearPath (-f) := by
  rcases hf with ⟨S, h0, h1, haff⟩
  refine ⟨S, h0, h1, fun a ha b hb hab hcons t hat htb ↦ ?_⟩
  rw [Pi.neg_apply, Pi.neg_apply, Pi.neg_apply, haff a ha b hb hab hcons t hat htb]
  module

lemma IsPiecewiseLinearPath.sub {f g : Icc (0 : ℚ) 1 → M} (hf : IsPiecewiseLinearPath f)
    (hg : IsPiecewiseLinearPath g) : IsPiecewiseLinearPath (f - g) :=
  sub_eq_add_neg f g ▸ hf.add hg.neg

lemma IsBreakpointSet.map {M' : Type*} [AddCommGroup M'] [Module ℚ M'] (L : M →ₗ[ℚ] M')
    {f : Icc (0 : ℚ) 1 → M} {S : Finset (Icc (0 : ℚ) 1)} (hS : IsBreakpointSet f S) :
    IsBreakpointSet (L ∘ f) S := by
  refine ⟨hS.1, hS.2.1, fun a ha b hb hab hcons t hat htb ↦ ?_⟩
  simp only [Function.comp_apply, hS.2.2 a ha b hb hab hcons t hat htb, map_add, map_smul, map_sub]

lemma IsBreakpointSet.comp_max {f : Icc (0 : ℚ) 1 → M} {S : Finset (Icc (0 : ℚ) 1)}
    (hS : IsBreakpointSet f S) {s : Icc (0 : ℚ) 1} (hs : s ∈ S) :
    IsBreakpointSet (fun t ↦ f (max s t)) S := by
  refine ⟨hS.1, hS.2.1, fun a ha b hb hab hcons t hat htb ↦ ?_⟩
  dsimp only
  rcases hcons s hs with hsa | hbs
  · rw [max_eq_right (hsa.trans hat), max_eq_right hsa, max_eq_right (hsa.trans hab.le)]
    exact hS.2.2 a ha b hb hab hcons t hat htb
  · rw [max_eq_left (htb.trans hbs), max_eq_left (hab.le.trans hbs), max_eq_left hbs, sub_self,
      smul_zero, add_zero]

lemma IsBreakpointSet.comp_min {f : Icc (0 : ℚ) 1 → M} {S : Finset (Icc (0 : ℚ) 1)}
    (hS : IsBreakpointSet f S) {s : Icc (0 : ℚ) 1} (hs : s ∈ S) :
    IsBreakpointSet (fun t ↦ f (min s t)) S := by
  refine ⟨hS.1, hS.2.1, fun a ha b hb hab hcons t hat htb ↦ ?_⟩
  dsimp only
  rcases hcons s hs with hsa | hbs
  · rw [min_eq_left (hsa.trans hat), min_eq_left hsa, min_eq_left (hsa.trans hab.le), sub_self,
      smul_zero, add_zero]
  · rw [min_eq_right (htb.trans hbs), min_eq_right (hab.le.trans hbs), min_eq_right hbs]
    exact hS.2.2 a ha b hb hab hcons t hat htb

protected lemma IsPiecewiseLinearPath.min {f g : Icc (0 : ℚ) 1 → ℚ} (hf : IsPiecewiseLinearPath f)
    (hg : IsPiecewiseLinearPath g) : IsPiecewiseLinearPath fun t ↦ min (f t) (g t) := by
  have h : (fun t ↦ min (f t) (g t)) = f - fun t ↦ max 0 ((f - g) t) := by
    funext t
    rw [Pi.sub_apply, Pi.sub_apply]
    rcases le_total (f t) (g t) with h | h
    · rw [min_eq_left h, max_eq_left (sub_nonpos.mpr h), sub_zero]
    · rw [min_eq_right h, max_eq_right (sub_nonneg.mpr h), sub_sub_cancel]
  rw [h]
  exact hf.sub (hf.sub hg).max_zero

lemma isPiecewiseLinearPath_inf' {κ : Type*} {A : Finset κ} (hA : A.Nonempty)
    {ψ : κ → Icc (0 : ℚ) 1 → ℚ} (hψ : ∀ j ∈ A, IsPiecewiseLinearPath (ψ j)) :
    IsPiecewiseLinearPath fun t ↦ A.inf' hA fun j ↦ ψ j t :=
  funext (Finset.inf'_apply hA ψ) ▸ Finset.inf'_induction hA ψ (fun _ hf _ hg ↦ hf.min hg) hψ

/-- A **Littelmann path** (LMFDB `crystals.littelmann_path`) for a root pairing `P` over `ℚ`: a
piecewise-linear map `π : [0, 1] ∩ ℚ → M` with `π(0) = 0` and `π(1)` an integral weight. For the
root system of a semisimple Lie algebra, `M` is `P ⊗ ℚ` for the weight lattice `P`. -/
@[ext]
structure LittelmannPath where
  /-- The map `t ↦ π(t)`. -/
  toFun : Icc (0 : ℚ) 1 → M
  isPiecewiseLinearPath : IsPiecewiseLinearPath toFun
  toFun_bot : toFun ⊥ = 0
  isIntegralWeight_one : P.IsIntegralWeight (toFun ⊤)

namespace LittelmannPath

variable {P} (π : P.LittelmannPath) (i : ι)

/-- The **height function** `Hᵢ(t) = ⟨π(t), αᵢ^∨⟩` of a Littelmann path `π` along the coroot
`αᵢ^∨`. -/
def height (t : Icc (0 : ℚ) 1) : ℚ :=
  P.toLinearMap (π.toFun t) (P.coroot i)

lemma isBreakpointSet_height {S : Finset (Icc (0 : ℚ) 1)} (hS : IsBreakpointSet π.toFun S) :
    IsBreakpointSet (π.height i) S :=
  hS.map (P.toLinearMap.flip (P.coroot i))

lemma exists_isLeast_height : ∃ m, IsLeast (range (π.height i)) m := by
  rcases π.isPiecewiseLinearPath with ⟨S, hS⟩
  have hne : (S.image (π.height i)).Nonempty := ⟨_, Finset.mem_image_of_mem _ hS.1⟩
  refine ⟨(S.image (π.height i)).min' hne, ?_, ?_⟩
  · rcases Finset.mem_image.mp ((S.image (π.height i)).min'_mem hne) with ⟨s, -, hs⟩
    exact ⟨s, hs⟩
  · rintro _ ⟨t, rfl⟩
    rcases (π.isBreakpointSet_height i hS).exists_le_le t with ⟨a, ha, b, hb, hat, htb, heq⟩
    exact le_apply_of_affine (heq t hat htb) hat htb
      (Finset.min'_le _ _ (Finset.mem_image_of_mem _ ha))
      (Finset.min'_le _ _ (Finset.mem_image_of_mem _ hb))

/-- The **minimum** `mᵢ` of the height function `Hᵢ` of a Littelmann path on `[0, 1] ∩ ℚ`, which
exists since `Hᵢ` is piecewise linear (`RootPairing.LittelmannPath.isLeast_minHeight`). -/
noncomputable def minHeight : ℚ :=
  (π.exists_isLeast_height i).choose

/-- **The height function of a Littelmann path attains its minimum**, `minHeight`. -/
lemma isLeast_minHeight : IsLeast (range (π.height i)) (π.minHeight i) :=
  (π.exists_isLeast_height i).choose_spec

/-- The **weight** `wt(π) = π(1)` of a Littelmann path `π` (LMFDB `crystals.littelmann_path`), an
integral weight. -/
def wt : M :=
  π.toFun ⊤

/-- The **crystal datum** `εᵢ(π) = -mᵢ` of a Littelmann path (LMFDB `crystals.littelmann_path`),
minus the minimum of the height function `Hᵢ`: the number of times the raising operator `eᵢ` can
be applied to `π`. It is an integer for Littelmann's integral paths, and a rational number in
general. -/
noncomputable def ε : ℚ :=
  -π.minHeight i

/-- The **crystal datum** `φᵢ(π) = Hᵢ(1) - mᵢ` of a Littelmann path (LMFDB
`crystals.littelmann_path`): the number of times the lowering operator `fᵢ` can be applied to `π`.
It is an integer for Littelmann's integral paths, and a rational number in general. -/
noncomputable def φ : ℚ :=
  π.height i ⊤ - π.minHeight i

/-- **`φᵢ(π) - εᵢ(π) = ⟨wt(π), αᵢ^∨⟩`**, the weight axiom of a crystal. -/
lemma φ_sub_ε : π.φ i - π.ε i = P.toLinearMap π.wt (P.coroot i) := by
  rw [φ, ε, sub_neg_eq_add, sub_add_cancel]
  rfl

lemma ε_nonneg : 0 ≤ π.ε i := by
  have h : π.minHeight i ≤ π.height i ⊥ := (π.isLeast_minHeight i).2 ⟨⊥, rfl⟩
  rw [height, π.toFun_bot, map_zero, LinearMap.zero_apply] at h
  exact neg_nonneg.mpr h

lemma φ_nonneg : 0 ≤ π.φ i :=
  sub_nonneg.mpr ((π.isLeast_minHeight i).2 ⟨⊤, rfl⟩)

/-- The **partly reflected map** obtained from a Littelmann path `π` by applying the reflection `sᵢ`
to the part of `π` between the times `t₀ ≤ t₁` and translating the part after `t₁` accordingly:
`t ↦ π(t) - (Hᵢ(τ(t)) - Hᵢ(t₀)) αᵢ`, where `τ(t)` is the point of `[t₀, t₁]` closest to `t`. -/
def reflectFun (t₀ t₁ t : Icc (0 : ℚ) 1) : M :=
  π.toFun t - (π.height i (max t₀ (min t t₁)) - π.height i t₀) • P.root i

variable {t₀ t₁ t : Icc (0 : ℚ) 1}

lemma reflectFun_of_le (h : t₀ ≤ t₁) (ht : t ≤ t₀) : π.reflectFun i t₀ t₁ t = π.toFun t := by
  rw [reflectFun, min_eq_left (ht.trans h), max_eq_left ht, sub_self, zero_smul, sub_zero]

lemma reflectFun_of_mem (h₀ : t₀ ≤ t) (h₁ : t ≤ t₁) :
    π.reflectFun i t₀ t₁ t = π.toFun t - (π.height i t - π.height i t₀) • P.root i := by
  rw [reflectFun, min_eq_left h₁, max_eq_right h₀]

lemma reflectFun_of_ge (h : t₀ ≤ t₁) (ht : t₁ ≤ t) :
    π.reflectFun i t₀ t₁ t = π.toFun t - (π.height i t₁ - π.height i t₀) • P.root i := by
  rw [reflectFun, min_eq_right ht, max_eq_right h]

lemma isPiecewiseLinearPath_reflectFun (h : t₀ ≤ t₁) :
    IsPiecewiseLinearPath (π.reflectFun i t₀ t₁) := by
  classical
  rcases π.isPiecewiseLinearPath with ⟨S, hS⟩
  have hT : IsBreakpointSet π.toFun (insert t₀ (insert t₁ S)) :=
    hS.mono ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _))
  refine ⟨insert t₀ (insert t₁ S), hT.1, hT.2.1, fun a ha b hb hab hcons t hat htb ↦ ?_⟩
  have hπ : π.toFun t = π.toFun a + (((t : ℚ) - a) / ((b : ℚ) - a)) • (π.toFun b - π.toFun a) :=
    hT.2.2 a ha b hb hab hcons t hat htb
  rcases hcons t₀ (Finset.mem_insert_self _ _) with h₀ | h₀
  · rcases hcons t₁ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)) with h₁ | h₁
    · rw [π.reflectFun_of_ge i h (h₁.trans hat), π.reflectFun_of_ge i h h₁,
        π.reflectFun_of_ge i h (h₁.trans hab.le), hπ]
      module
    · have hH : π.height i t = π.height i a +
          (((t : ℚ) - a) / ((b : ℚ) - a)) * (π.height i b - π.height i a) := by
        simp only [height, hπ, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
          map_sub, LinearMap.sub_apply, smul_eq_mul]
      rw [π.reflectFun_of_mem i (h₀.trans hat) (htb.trans h₁), π.reflectFun_of_mem i h₀
        (hab.le.trans h₁), π.reflectFun_of_mem i (h₀.trans hab.le) h₁, hH, hπ]
      module
  · rw [π.reflectFun_of_le i h (htb.trans h₀), π.reflectFun_of_le i h (hab.le.trans h₀),
      π.reflectFun_of_le i h h₀, hπ]

variable (t) in
lemma isLeast_inf'_height_max {S : Finset (Icc (0 : ℚ) 1)} (hS : IsBreakpointSet π.toFun S) :
    IsLeast (π.height i '' Ici t) (S.inf' ⟨⊥, hS.1⟩ fun s ↦ π.height i (max s t)) := by
  refine ⟨?_, ?_⟩
  · rcases Finset.exists_mem_eq_inf' ⟨⊥, hS.1⟩ (fun s ↦ π.height i (max s t)) with ⟨s, -, hs⟩
    exact ⟨max s t, le_max_right s t, hs.symm⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : t ≤ x := mem_Ici.mp hx
    rcases (π.isBreakpointSet_height i hS).exists_le_le x with ⟨a, ha, b, hb, hax, hxb, heq⟩
    have hb' : S.inf' ⟨⊥, hS.1⟩ (fun s ↦ π.height i (max s t)) ≤ π.height i b :=
      (Finset.inf'_le (fun s ↦ π.height i (max s t)) hb).trans_eq
        (congrArg (π.height i) (max_eq_left (hx'.trans hxb)))
    rcases le_total t a with hta | hat
    · have ha' : S.inf' ⟨⊥, hS.1⟩ (fun s ↦ π.height i (max s t)) ≤ π.height i a :=
        (Finset.inf'_le (fun s ↦ π.height i (max s t)) ha).trans_eq
          (congrArg (π.height i) (max_eq_left hta))
      exact le_apply_of_affine (heq x hax hxb) hax hxb ha' hb'
    · have ht' : S.inf' ⟨⊥, hS.1⟩ (fun s ↦ π.height i (max s t)) ≤ π.height i t :=
        (Finset.inf'_le (fun s ↦ π.height i (max s t)) hS.1).trans_eq
          (congrArg (π.height i) (max_eq_right bot_le))
      rcases (hx'.trans hxb).lt_or_eq with htb | htb
      · exact le_apply_of_affine (eq_add_smul_of_le heq hat htb le_rfl x hx' hxb) hx' hxb ht' hb'
      · rw [le_antisymm (htb ▸ hxb) hx']
        exact ht'

variable (t) in
lemma isLeast_inf'_height_min {S : Finset (Icc (0 : ℚ) 1)} (hS : IsBreakpointSet π.toFun S) :
    IsLeast (π.height i '' Iic t) (S.inf' ⟨⊤, hS.2.1⟩ fun s ↦ π.height i (min s t)) := by
  refine ⟨?_, ?_⟩
  · rcases Finset.exists_mem_eq_inf' ⟨⊤, hS.2.1⟩ (fun s ↦ π.height i (min s t)) with ⟨s, -, hs⟩
    exact ⟨min s t, min_le_right s t, hs.symm⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hx' : x ≤ t := mem_Iic.mp hx
    rcases (π.isBreakpointSet_height i hS).exists_le_le x with ⟨a, ha, b, hb, hax, hxb, heq⟩
    have ha' : S.inf' ⟨⊤, hS.2.1⟩ (fun s ↦ π.height i (min s t)) ≤ π.height i a :=
      (Finset.inf'_le (fun s ↦ π.height i (min s t)) ha).trans_eq
        (congrArg (π.height i) (min_eq_left (hax.trans hx')))
    rcases le_total b t with hbt | htb
    · have hb' : S.inf' ⟨⊤, hS.2.1⟩ (fun s ↦ π.height i (min s t)) ≤ π.height i b :=
        (Finset.inf'_le (fun s ↦ π.height i (min s t)) hb).trans_eq
          (congrArg (π.height i) (min_eq_left hbt))
      exact le_apply_of_affine (heq x hax hxb) hax hxb ha' hb'
    · have ht' : S.inf' ⟨⊤, hS.2.1⟩ (fun s ↦ π.height i (min s t)) ≤ π.height i t :=
        (Finset.inf'_le (fun s ↦ π.height i (min s t)) hS.2.1).trans_eq
          (congrArg (π.height i) (min_eq_right le_top))
      rcases (hax.trans hx').lt_or_eq with hat | hat
      · exact le_apply_of_affine (eq_add_smul_of_le heq le_rfl hat htb x hax hx') hax hx' ha' ht'
      · rw [le_antisymm (hat ▸ hx') hax]
        exact ha'

variable (t) in
lemma exists_isLeast_height_Ici : ∃ m, IsLeast (π.height i '' Ici t) m := by
  rcases π.isPiecewiseLinearPath with ⟨S, hS⟩
  exact ⟨_, π.isLeast_inf'_height_max i t hS⟩

variable (t) in
lemma exists_isLeast_height_Iic : ∃ m, IsLeast (π.height i '' Iic t) m := by
  rcases π.isPiecewiseLinearPath with ⟨S, hS⟩
  exact ⟨_, π.isLeast_inf'_height_min i t hS⟩

variable (t) in
/-- The **future minimum** `min_{s ≥ t} Hᵢ(s)` of the height function of a Littelmann path, which
exists since `Hᵢ` is piecewise linear. -/
noncomputable def futureMinHeight : ℚ :=
  (π.exists_isLeast_height_Ici i t).choose

variable (t) in
/-- The **past minimum** `min_{s ≤ t} Hᵢ(s)` of the height function of a Littelmann path, which
exists since `Hᵢ` is piecewise linear. -/
noncomputable def pastMinHeight : ℚ :=
  (π.exists_isLeast_height_Iic i t).choose

variable (t) in
lemma isLeast_futureMinHeight : IsLeast (π.height i '' Ici t) (π.futureMinHeight i t) :=
  (π.exists_isLeast_height_Ici i t).choose_spec

variable (t) in
lemma isLeast_pastMinHeight : IsLeast (π.height i '' Iic t) (π.pastMinHeight i t) :=
  (π.exists_isLeast_height_Iic i t).choose_spec

lemma isPiecewiseLinearPath_futureMinHeight : IsPiecewiseLinearPath (π.futureMinHeight i) := by
  rcases π.isPiecewiseLinearPath with ⟨S, hS⟩
  rw [funext fun t ↦ (π.isLeast_futureMinHeight i t).unique (π.isLeast_inf'_height_max i t hS)]
  exact isPiecewiseLinearPath_inf' _ fun s hs ↦ ⟨S, (π.isBreakpointSet_height i hS).comp_max hs⟩

lemma isPiecewiseLinearPath_pastMinHeight : IsPiecewiseLinearPath (π.pastMinHeight i) := by
  rcases π.isPiecewiseLinearPath with ⟨S, hS⟩
  rw [funext fun t ↦ (π.isLeast_pastMinHeight i t).unique (π.isLeast_inf'_height_min i t hS)]
  exact isPiecewiseLinearPath_inf' _ fun s hs ↦ ⟨S, (π.isBreakpointSet_height i hS).comp_min hs⟩

lemma futureMinHeight_bot : π.futureMinHeight i ⊥ = π.minHeight i :=
  (π.isLeast_futureMinHeight i ⊥).unique (by
    rw [Ici_bot, image_univ]
    exact π.isLeast_minHeight i)

lemma futureMinHeight_top : π.futureMinHeight i ⊤ = π.height i ⊤ :=
  (π.isLeast_futureMinHeight i ⊤).unique (by
    rw [Ici_top, image_singleton]
    exact isLeast_singleton)

lemma pastMinHeight_bot : π.pastMinHeight i ⊥ = π.height i ⊥ :=
  (π.isLeast_pastMinHeight i ⊥).unique (by
    rw [Iic_bot, image_singleton]
    exact isLeast_singleton)

lemma pastMinHeight_top : π.pastMinHeight i ⊤ = π.minHeight i :=
  (π.isLeast_pastMinHeight i ⊤).unique (by
    rw [Iic_top, image_univ]
    exact π.isLeast_minHeight i)

variable (t) in
/-- The **coefficient** `min(1, max(0, min_{s ≥ t} Hᵢ(s) - mᵢ))` of `-αᵢ` in the lowering operator
`fᵢ` at time `t`. -/
noncomputable def lowerCoeff : ℚ :=
  max 0 (min 1 (π.futureMinHeight i t - π.minHeight i))

variable (t) in
/-- The **coefficient** `min(1, max(0, mᵢ + 1 - min_{s ≤ t} Hᵢ(s)))` of `αᵢ` in the raising operator
`eᵢ` at time `t`. -/
noncomputable def raiseCoeff : ℚ :=
  max 0 (min 1 (π.minHeight i + 1 - π.pastMinHeight i t))

lemma isPiecewiseLinearPath_lowerFun :
    IsPiecewiseLinearPath fun t ↦ π.toFun t - π.lowerCoeff i t • P.root i :=
  π.isPiecewiseLinearPath.sub (((isPiecewiseLinearPath_const 1).min
    ((π.isPiecewiseLinearPath_futureMinHeight i).sub
      (isPiecewiseLinearPath_const _))).max_zero.smul_const (P.root i))

lemma isPiecewiseLinearPath_raiseFun :
    IsPiecewiseLinearPath fun t ↦ π.toFun t + π.raiseCoeff i t • P.root i :=
  π.isPiecewiseLinearPath.add (((isPiecewiseLinearPath_const 1).min
    ((isPiecewiseLinearPath_const _).sub
      (π.isPiecewiseLinearPath_pastMinHeight i))).max_zero.smul_const (P.root i))

lemma lowerCoeff_bot : π.lowerCoeff i ⊥ = 0 := by
  rw [lowerCoeff, futureMinHeight_bot, sub_self, min_eq_right zero_le_one, max_self]

lemma lowerCoeff_top (h : 1 ≤ π.φ i) : π.lowerCoeff i ⊤ = 1 := by
  have h' : 1 ≤ π.height i ⊤ - π.minHeight i := h
  rw [lowerCoeff, futureMinHeight_top, min_eq_left h', max_eq_right zero_le_one]

lemma raiseCoeff_bot (h : 1 ≤ π.ε i) : π.raiseCoeff i ⊥ = 0 := by
  have hε : 1 ≤ -π.minHeight i := h
  have h' : π.minHeight i + 1 - π.pastMinHeight i ⊥ ≤ 0 := by
    rw [pastMinHeight_bot, height, π.toFun_bot, map_zero, LinearMap.zero_apply, sub_zero]
    linarith
  rw [raiseCoeff, min_eq_right (h'.trans zero_le_one), max_eq_left h']

lemma raiseCoeff_top : π.raiseCoeff i ⊤ = 1 := by
  rw [raiseCoeff, pastMinHeight_top, add_sub_cancel_left, min_self, max_eq_right zero_le_one]

variable [P.IsCrystallographic] (h : t₀ ≤ t₁) (hint : ∃ n : ℤ, π.height i t₁ - π.height i t₀ = n)
  (hφ : 1 ≤ π.φ i) (hε : 1 ≤ π.ε i)

/-- The **reflection of a Littelmann path** `π` between the times `t₀ ≤ t₁` along the root `αᵢ`,
when `Hᵢ(t₁) - Hᵢ(t₀)` is an integer: the Littelmann path that is `π` up to `t₀`, the image
`π(t₀) + sᵢ(π(t) - π(t₀))` of `π` under the reflection `sᵢ` between `t₀` and `t₁`, and
`π(t) - (Hᵢ(t₁) - Hᵢ(t₀)) αᵢ` after `t₁`. Littelmann's root operators are reflections, with
`Hᵢ(t₁) - Hᵢ(t₀) = 1` for `fᵢ` and `-1` for `eᵢ`. -/
def reflect : P.LittelmannPath where
  toFun := π.reflectFun i t₀ t₁
  isPiecewiseLinearPath := π.isPiecewiseLinearPath_reflectFun i h
  toFun_bot := by
    rw [π.reflectFun_of_le i h bot_le, π.toFun_bot]
  isIntegralWeight_one j := by
    rcases π.isIntegralWeight_one j with ⟨m, hm⟩
    rcases hint with ⟨n, hn⟩
    rcases P.exists_value (S := ℤ) i j with ⟨k, hk⟩
    refine ⟨m - n * k, ?_⟩
    rw [π.reflectFun_of_ge i h le_top, map_sub, map_smul, LinearMap.sub_apply,
      LinearMap.smul_apply, hm, hn, root_coroot_eq_pairing, ← hk, algebraMap_int_eq, eq_intCast]
    push_cast
    ring1

lemma wt_reflect : (π.reflect i h hint).wt = π.wt - (π.height i t₁ - π.height i t₀) • P.root i :=
  π.reflectFun_of_ge i h le_top

/-- Littelmann's **lowering operator** `fᵢ` (LMFDB `crystals.littelmann_path`) on a Littelmann path
`π` with `φᵢ(π) ≥ 1`: `fᵢ π(t) = π(t) - min(1, max(0, min_{s ≥ t} Hᵢ(s) - mᵢ)) αᵢ`. The path is
unchanged up to the last time `p` at which `Hᵢ` attains its minimum `mᵢ`; between `p` and the time
after which `Hᵢ ≥ mᵢ + 1`, the parts along which the future minimum of `Hᵢ` increases are reflected
by `sᵢ` and the others translated; the rest is translated by `-αᵢ`. When the local minima of `Hᵢ`
are integers (Littelmann's integral paths), this is the reflection
`RootPairing.LittelmannPath.reflect` of `π` between `p` and the first later time at which
`Hᵢ = mᵢ + 1`. -/
noncomputable def lowerPath : P.LittelmannPath where
  toFun t := π.toFun t - π.lowerCoeff i t • P.root i
  isPiecewiseLinearPath := π.isPiecewiseLinearPath_lowerFun i
  toFun_bot := by
    rw [π.lowerCoeff_bot i, zero_smul, sub_zero, π.toFun_bot]
  isIntegralWeight_one j := by
    rcases π.isIntegralWeight_one j with ⟨m, hm⟩
    rcases P.exists_value (S := ℤ) i j with ⟨k, hk⟩
    refine ⟨m - k, ?_⟩
    rw [π.lowerCoeff_top i hφ, one_smul, map_sub, LinearMap.sub_apply, hm, root_coroot_eq_pairing,
      ← hk, algebraMap_int_eq, eq_intCast, Int.cast_sub]

/-- Littelmann's **raising operator** `eᵢ` (LMFDB `crystals.littelmann_path`) on a Littelmann path
`π` with `εᵢ(π) ≥ 1`: `eᵢ π(t) = π(t) + min(1, max(0, mᵢ + 1 - min_{s ≤ t} Hᵢ(s))) αᵢ`, the mirror
image of the lowering operator. The path is unchanged as long as `Hᵢ ≥ mᵢ + 1` on `[0, t]`; from
then until the first time `q` at which `Hᵢ` attains its minimum `mᵢ`, the parts along which the
past minimum of `Hᵢ` decreases are reflected by `sᵢ` and the others translated; the rest is
translated by `αᵢ`. -/
noncomputable def raisePath : P.LittelmannPath where
  toFun t := π.toFun t + π.raiseCoeff i t • P.root i
  isPiecewiseLinearPath := π.isPiecewiseLinearPath_raiseFun i
  toFun_bot := by
    rw [π.raiseCoeff_bot i hε, zero_smul, add_zero, π.toFun_bot]
  isIntegralWeight_one j := by
    rcases π.isIntegralWeight_one j with ⟨m, hm⟩
    rcases P.exists_value (S := ℤ) i j with ⟨k, hk⟩
    refine ⟨m + k, ?_⟩
    rw [π.raiseCoeff_top i, one_smul, map_add, LinearMap.add_apply, hm, root_coroot_eq_pairing,
      ← hk, algebraMap_int_eq, eq_intCast, Int.cast_add]

/-- The **lowering operator** `fᵢ` as a partial operation on Littelmann paths (LMFDB
`crystals.littelmann_path`): `none` stands for Littelmann's `fᵢ π = 0`, when `φᵢ(π) < 1`. -/
noncomputable def lower : Option P.LittelmannPath :=
  if hφ : 1 ≤ π.φ i then some (π.lowerPath i hφ) else none

/-- The **raising operator** `eᵢ` as a partial operation on Littelmann paths (LMFDB
`crystals.littelmann_path`): `none` stands for Littelmann's `eᵢ π = 0`, when `εᵢ(π) < 1`. -/
noncomputable def raise : Option P.LittelmannPath :=
  if hε : 1 ≤ π.ε i then some (π.raisePath i hε) else none

lemma wt_lowerPath : (π.lowerPath i hφ).wt = π.wt - P.root i :=
  (congrArg (fun c : ℚ ↦ π.wt - c • P.root i) (π.lowerCoeff_top i hφ)).trans (by rw [one_smul])

lemma wt_raisePath : (π.raisePath i hε).wt = π.wt + P.root i :=
  (congrArg (fun c : ℚ ↦ π.wt + c • P.root i) (π.raiseCoeff_top i)).trans (by rw [one_smul])

variable (t) in
lemma height_lowerPath : (π.lowerPath i hφ).height i t = π.height i t - 2 * π.lowerCoeff i t := by
  rw [height, height, ← P.root_coroot_two i]
  simp only [lowerPath, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply]
  ring1

lemma minHeight_lowerPath : (π.lowerPath i hφ).minHeight i = π.minHeight i - 1 := by
  have hφ' : 1 ≤ π.height i ⊤ - π.minHeight i := hφ
  have hg₀ (t : Icc (0 : ℚ) 1) : π.minHeight i ≤ π.futureMinHeight i t := by
    rcases (π.isLeast_futureMinHeight i t).1 with ⟨s, -, hs⟩
    exact hs ▸ (π.isLeast_minHeight i).2 ⟨s, rfl⟩
  have hg₁ (t : Icc (0 : ℚ) 1) : π.futureMinHeight i t ≤ π.height i t :=
    (π.isLeast_futureMinHeight i t).2 ⟨t, mem_Ici.mpr le_rfl, rfl⟩
  refine ((π.lowerPath i hφ).isLeast_minHeight i).unique ⟨?_, ?_⟩
  · rcases (π.isPiecewiseLinearPath_futureMinHeight i).exists_eq (y := π.minHeight i + 1)
      (by rw [futureMinHeight_bot]; linarith) (by rw [futureMinHeight_top]; linarith) with ⟨t, ht⟩
    rcases (π.isLeast_futureMinHeight i t).1 with ⟨s, hs, hHs⟩
    have hgs : π.futureMinHeight i s = π.minHeight i + 1 :=
      le_antisymm ((hg₁ s).trans_eq (hHs.trans ht)) (ht.symm.trans_le
        ((π.isLeast_futureMinHeight i t).2
          (image_mono (Ici_subset_Ici.mpr hs) (π.isLeast_futureMinHeight i s).1)))
    refine ⟨s, ?_⟩
    rw [height_lowerPath, lowerCoeff, hgs, hHs, ht, add_sub_cancel_left, min_self,
      max_eq_right zero_le_one]
    ring1
  · rintro _ ⟨t, rfl⟩
    rw [height_lowerPath, lowerCoeff]
    have h₀ : π.minHeight i ≤ π.futureMinHeight i t := hg₀ t
    have h₁ : π.futureMinHeight i t ≤ π.height i t := hg₁ t
    rcases le_total (π.futureMinHeight i t - π.minHeight i) 1 with h₂ | h₂
    · rw [min_eq_right h₂, max_eq_right (sub_nonneg.mpr h₀)]
      linarith
    · rw [min_eq_left h₂, max_eq_right zero_le_one]
      linarith

/-- **The lowering operator raises `εᵢ` by one**: `εᵢ(fᵢ π) = εᵢ(π) + 1`, a crystal axiom. -/
lemma ε_lowerPath : (π.lowerPath i hφ).ε i = π.ε i + 1 := by
  rw [ε, ε, minHeight_lowerPath]
  ring1

/-- **The lowering operator lowers `φᵢ` by one**: `φᵢ(fᵢ π) = φᵢ(π) - 1`, a crystal axiom. -/
lemma φ_lowerPath : (π.lowerPath i hφ).φ i = π.φ i - 1 := by
  have h₁ : (π.lowerPath i hφ).φ i - (π.lowerPath i hφ).ε i =
      P.toLinearMap (π.lowerPath i hφ).wt (P.coroot i) := (π.lowerPath i hφ).φ_sub_ε i
  rw [wt_lowerPath, map_sub, LinearMap.sub_apply, P.root_coroot_two, ε_lowerPath,
    ← π.φ_sub_ε i] at h₁
  linarith

variable (t) in
lemma height_raisePath : (π.raisePath i hε).height i t = π.height i t + 2 * π.raiseCoeff i t := by
  rw [height, height, ← P.root_coroot_two i]
  simp only [raisePath, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
  ring1

lemma minHeight_raisePath : (π.raisePath i hε).minHeight i = π.minHeight i + 1 := by
  have hε' : 1 ≤ -π.minHeight i := hε
  have hg₀ (t : Icc (0 : ℚ) 1) : π.minHeight i ≤ π.pastMinHeight i t := by
    rcases (π.isLeast_pastMinHeight i t).1 with ⟨s, -, hs⟩
    exact hs ▸ (π.isLeast_minHeight i).2 ⟨s, rfl⟩
  have hg₁ (t : Icc (0 : ℚ) 1) : π.pastMinHeight i t ≤ π.height i t :=
    (π.isLeast_pastMinHeight i t).2 ⟨t, mem_Iic.mpr le_rfl, rfl⟩
  refine ((π.raisePath i hε).isLeast_minHeight i).unique ⟨?_, ?_⟩
  · have hH₀ : π.height i ⊥ = 0 := by
      rw [height, π.toFun_bot, map_zero, LinearMap.zero_apply]
    rcases (π.isPiecewiseLinearPath_pastMinHeight i).neg.exists_eq (y := -(π.minHeight i + 1))
      (by rw [Pi.neg_apply, pastMinHeight_bot, hH₀]; linarith)
      (by rw [Pi.neg_apply, pastMinHeight_top]; linarith) with ⟨t, ht⟩
    rw [Pi.neg_apply, neg_inj] at ht
    rcases (π.isLeast_pastMinHeight i t).1 with ⟨s, hs, hHs⟩
    have hgs : π.pastMinHeight i s = π.minHeight i + 1 :=
      le_antisymm ((hg₁ s).trans_eq (hHs.trans ht)) (ht.symm.trans_le
        ((π.isLeast_pastMinHeight i t).2
          (image_mono (Iic_subset_Iic.mpr hs) (π.isLeast_pastMinHeight i s).1)))
    refine ⟨s, ?_⟩
    rw [height_raisePath, raiseCoeff, hgs, hHs, ht, sub_self, min_eq_right zero_le_one, max_self]
    ring1
  · rintro _ ⟨t, rfl⟩
    rw [height_raisePath, raiseCoeff]
    have h₀ : π.minHeight i ≤ π.pastMinHeight i t := hg₀ t
    have h₁ : π.pastMinHeight i t ≤ π.height i t := hg₁ t
    rcases le_total (π.minHeight i + 1 - π.pastMinHeight i t) 0 with h₂ | h₂
    · rw [min_eq_right (h₂.trans zero_le_one), max_eq_left h₂]
      linarith
    · rcases le_total (π.minHeight i + 1 - π.pastMinHeight i t) 1 with h₃ | h₃
      · rw [min_eq_right h₃, max_eq_right h₂]
        linarith
      · rw [min_eq_left h₃, max_eq_right zero_le_one]
        linarith

/-- **The raising operator lowers `εᵢ` by one**: `εᵢ(eᵢ π) = εᵢ(π) - 1`, a crystal axiom. -/
lemma ε_raisePath : (π.raisePath i hε).ε i = π.ε i - 1 := by
  rw [ε, ε, minHeight_raisePath]
  ring1

/-- **The raising operator raises `φᵢ` by one**: `φᵢ(eᵢ π) = φᵢ(π) + 1`, a crystal axiom. -/
lemma φ_raisePath : (π.raisePath i hε).φ i = π.φ i + 1 := by
  have h₁ : (π.raisePath i hε).φ i - (π.raisePath i hε).ε i =
      P.toLinearMap (π.raisePath i hε).wt (P.coroot i) := (π.raisePath i hε).φ_sub_ε i
  rw [wt_raisePath, map_add, LinearMap.add_apply, P.root_coroot_two, ε_raisePath,
    ← π.φ_sub_ε i] at h₁
  linarith

end LittelmannPath

variable {P} {x : M} (hx : P.IsIntegralWeight x)

/-- The **straight-line path** `π_λ(t) = t λ` to an integral weight `λ`, a Littelmann path; for a
dominant weight `λ`, Littelmann's path model realises the highest weight crystal `B(λ)` as the paths
obtained from `π_λ` by the root operators. -/
def straightLinePath : P.LittelmannPath where
  toFun t := (t : ℚ) • x
  isPiecewiseLinearPath := ⟨{⊥, ⊤}, Finset.mem_insert_self _ _,
    Finset.mem_insert_of_mem (Finset.mem_singleton_self _), fun a _ b _ hab _ t _ _ ↦ by
      have h : (b : ℚ) - a ≠ 0 := sub_ne_zero.mpr (Subtype.coe_lt_coe.mpr hab).ne'
      rw [← sub_smul, smul_smul, div_mul_cancel₀ _ h, ← add_smul, add_sub_cancel]⟩
  toFun_bot := zero_smul ℚ x
  isIntegralWeight_one := by
    simpa using hx

lemma wt_straightLinePath : (straightLinePath hx).wt = x :=
  one_smul ℚ x

lemma minHeight_straightLinePath (i : ι) :
    (straightLinePath hx).minHeight i = min 0 (P.toLinearMap x (P.coroot i)) := by
  refine ((straightLinePath hx).isLeast_minHeight i).unique ⟨?_, ?_⟩
  · rcases le_total 0 (P.toLinearMap x (P.coroot i)) with h | h
    · exact ⟨⊥, by simp [LittelmannPath.height, straightLinePath, h]⟩
    · exact ⟨⊤, by simp [LittelmannPath.height, straightLinePath, h]⟩
  · rintro _ ⟨t, rfl⟩
    have ht₀ : (0 : ℚ) ≤ t := t.2.1
    have ht₁ : (t : ℚ) ≤ 1 := t.2.2
    simp only [LittelmannPath.height, straightLinePath, map_smul, LinearMap.smul_apply,
      smul_eq_mul, min_le_iff]
    rcases le_total 0 (P.toLinearMap x (P.coroot i)) with h | h
    · exact Or.inl (mul_nonneg ht₀ h)
    · exact Or.inr (by nlinarith)

end RootPairing
