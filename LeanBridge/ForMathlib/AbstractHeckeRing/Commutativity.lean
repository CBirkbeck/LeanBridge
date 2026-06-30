/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import LeanBridge.ForMathlib.AbstractHeckeRing.Ring

/-!
# Hecke Rings: Commutativity via Anti-Involution

Shimura Proposition 3.8: if an arithmetic group pair admits an anti-automorphism
`ι : G →* Gᵐᵒᵖ` that preserves H and Δ and fixes every double coset, then the
Hecke ring `𝕋 P ℤ` is commutative.
-/

open Classical MulOpposite Set DoubleCoset Subgroup Finsupp

open scoped Pointwise

namespace HeckeRing

variable {G : Type*} [Group G] (P : HeckePair G)

/-- An anti-involution of a HeckePair: `ι : G →* Gᵐᵒᵖ`,
involutive and preserving both `H` and `Δ`. -/
@[ext]
structure AntiInvolution where
  /-- The underlying homomorphism to the opposite group. -/
  toFun : G →* MulOpposite G
  /-- The induced map on `G` is involutive. -/
  involutive : ∀ g, (toFun (toFun g).unop).unop = g
  /-- The induced map preserves membership in `H`. -/
  map_H : ∀ g, g ∈ P.H → (toFun g).unop ∈ P.H
  /-- The induced map preserves membership in `Δ`. -/
  map_Δ : ∀ g, g ∈ P.Δ → (toFun g).unop ∈ P.Δ

variable {P}

namespace AntiInvolution

variable (ι : AntiInvolution P)

/-- The underlying function of the anti-involution, mapping `g` to `ι(g)` viewed in `G`. -/
def bar (g : G) : G := (ι.toFun g).unop

/-- The anti-involution is an involution: `bar(bar(g)) = g`. -/
@[simp] lemma bar_bar (g : G) : ι.bar (ι.bar g) = g := ι.involutive g

/-- The anti-involution reverses multiplication: `bar(ab) = bar(b) * bar(a)`. -/
lemma bar_mul (a b : G) : ι.bar (a * b) = ι.bar b * ι.bar a := by simp [bar]

/-- The anti-involution commutes with inversion. -/
lemma bar_inv (g : G) : ι.bar g⁻¹ = (ι.bar g)⁻¹ := by simp [bar]

/-- The anti-involution preserves membership in `H`. -/
lemma bar_mem_H {g : G} (hg : g ∈ P.H) : ι.bar g ∈ P.H :=
  ι.map_H g hg

/-- The anti-involution preserves membership in `Δ`. -/
lemma bar_mem_Δ {g : G} (hg : g ∈ P.Δ) : ι.bar g ∈ P.Δ :=
  ι.map_Δ g hg

/-- The anti-involution preserves double coset equality. -/
lemma bar_doubleCoset_eq (g₁ g₂ : G)
    (h : DoubleCoset.doubleCoset g₁ P.H P.H =
      DoubleCoset.doubleCoset g₂ P.H P.H) :
    DoubleCoset.doubleCoset (ι.bar g₁) P.H P.H =
    DoubleCoset.doubleCoset (ι.bar g₂) P.H P.H := by
  obtain ⟨h₁, hh₁, h₂, hh₂, hprod⟩ := (DoubleCoset.eq P.H P.H _ _).mp
    (DoubleCoset.mk_eq_of_doubleCoset_eq h)
  rw [show ι.bar g₂ = ι.bar h₂ * ι.bar g₁ * ι.bar h₁ by
    rw [hprod, bar_mul, bar_mul, mul_assoc]]
  symm
  rw [mul_assoc]
  trans DoubleCoset.doubleCoset (ι.bar g₁ * ι.bar h₁) (P.H : Set G) P.H
  · exact doset_mul_left_eq_self P ⟨ι.bar h₂, ι.bar_mem_H hh₂⟩ _
  · exact DoubleCoset.doubleCoset_mul_right_eq_self P ⟨ι.bar h₁, ι.bar_mem_H hh₁⟩ _

/-- The induced action of the anti-involution on double cosets, defined via `Quotient.lift`. -/
noncomputable def onHeckeCoset (D : HeckeCoset P) : HeckeCoset P :=
  Quotient.lift (fun (g : P.Δ) ↦
    (⟦⟨ι.bar (g : G), ι.bar_mem_Δ g.2⟩⟧ : HeckeCoset P))
    (fun _ _ (h : @Setoid.r _ (dcSetoid P) _ _) ↦ by
      show (⟦_⟧ : HeckeCoset P) = ⟦_⟧
      rw [HeckeCoset.eq_iff]
      exact ι.bar_doubleCoset_eq _ _ h) D

/-- `onHeckeCoset ⟦g⟧` equals `⟦bar(g)⟧`. -/
lemma onHeckeCoset_mk (g : P.Δ) :
    ι.onHeckeCoset (⟦g⟧ : HeckeCoset P) =
    (⟦⟨ι.bar (g : G), ι.bar_mem_Δ g.2⟩⟧ : HeckeCoset P) := rfl

/-- The set underlying `onHeckeCoset D` is the double coset of the barred representative. -/
lemma onHeckeCoset_toSet (D : HeckeCoset P) :
    HeckeCoset.toSet (ι.onHeckeCoset D) =
    DoubleCoset.doubleCoset (ι.bar (HeckeCoset.rep D : G)) P.H P.H := by
  conv_lhs => rw [show D = ⟦HeckeCoset.rep D⟧ from (Quotient.out_eq D).symm]
  simp [onHeckeCoset_mk]

private lemma bar_mem_doubleCoset (h_fix : ∀ D : HeckeCoset P, ι.onHeckeCoset D = D)
    (D₀ : HeckeCoset P) (x : G) (hx : x ∈ HeckeCoset.toSet D₀) :
    ι.bar x ∈ HeckeCoset.toSet D₀ := by
  rw [← congr_arg HeckeCoset.toSet (h_fix D₀), onHeckeCoset_toSet]
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hx
  obtain ⟨h₁, hh₁, h₂, hh₂, hprod⟩ := hx
  rw [hprod, DoubleCoset.mem_doubleCoset]
  exact ⟨ι.bar h₂, ι.bar_mem_H hh₂, ι.bar h₁, ι.bar_mem_H hh₁, by
    simp [bar_mul, mul_assoc]⟩

private lemma bar_rep_mem_doubleCoset (h_fix : ∀ D : HeckeCoset P, ι.onHeckeCoset D = D)
    (D : HeckeCoset P) : ∃ h₁ h₂ : P.H,
    ι.bar (HeckeCoset.rep D : G) = h₁ * (HeckeCoset.rep D : G) * h₂ := by
  have hbar := bar_mem_doubleCoset ι h_fix D _ (HeckeCoset.rep_mem D)
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hbar
  obtain ⟨h₁, hh₁, h₂, hh₂, heq⟩ := hbar
  exact ⟨⟨h₁, hh₁⟩, ⟨h₂, hh₂⟩, heq⟩

private lemma inverse_product_mem_doubleCoset
    (g₁ g₂ g_D : G) (D₂ : HeckeCoset P)
    (hg₂ : g₂ = (HeckeCoset.rep D₂ : G))
    (rep : P.H) (j_rep : P.H)
    (hcond : ({(rep : G) * g₁} : Set G) * {(j_rep : G) * g₂} * P.H =
        {g_D} * (P.H : Set G)) :
    g₁⁻¹ * (rep : G)⁻¹ * g_D ∈ HeckeCoset.toSet D₂ := by
  rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset]
  rw [hg₂] at hcond
  have hmem : (rep : G) * g₁ * ((j_rep : G) * (HeckeCoset.rep D₂ : G)) ∈
      ({g_D} : Set G) * ↑P.H := by
    have h1 : (rep : G) * g₁ * ((j_rep : G) * (HeckeCoset.rep D₂ : G)) ∈
        ({(rep : G) * g₁} : Set G) * {(j_rep : G) * (HeckeCoset.rep D₂ : G)} * ↑P.H :=
      ⟨_, ⟨_, rfl, _, rfl, rfl⟩, 1, P.H.one_mem, mul_one _⟩
    rwa [hcond] at h1
  obtain ⟨w, hw, k, hk, hprod⟩ := hmem
  rw [Set.mem_singleton_iff] at hw
  refine ⟨(j_rep : G), j_rep.2, k⁻¹, P.H.inv_mem hk, ?_⟩
  have hprod' : g_D * k =
      (rep : G) * g₁ * ((j_rep : G) * (HeckeCoset.rep D₂ : G)) := hw ▸ hprod
  calc g₁⁻¹ * (rep : G)⁻¹ * g_D
      = g₁⁻¹ * (rep : G)⁻¹ * (g_D * k * k⁻¹) := by group
    _ = g₁⁻¹ * (rep : G)⁻¹ *
          ((rep : G) * g₁ * ((j_rep : G) * (HeckeCoset.rep D₂ : G)) * k⁻¹) := by
      rw [hprod']
    _ = (j_rep : G) * (HeckeCoset.rep D₂ : G) * k⁻¹ := by group

private lemma conj_mem_of_stabilizer (g : G)
    (n : ((ConjAct.toConjAct g • P.H).subgroupOf P.H)) :
    g⁻¹ * (n : G) * g ∈ P.H := by
  have := n.2
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at this
  simpa [ConjAct.ofConjAct_toConjAct] using this

private lemma bar_quotient_diff_mem_H
    (x₁ x₂ : G) (g₂ a₁ b₁ a₂ b₂ : G)
    (_ : a₁ ∈ (P.H : Set G)) (hb₁ : b₁ ∈ (P.H : Set G))
    (_ : a₂ ∈ (P.H : Set G)) (hb₂ : b₂ ∈ (P.H : Set G))
    (hbarx₁ : ι.bar x₁ = a₁ * g₂ * b₁)
    (hbarx₂ : ι.bar x₂ = a₂ * g₂ * b₂)
    (hconj : g₂⁻¹ * a₁⁻¹ * a₂ * g₂ ∈ P.H) :
    x₂ * x₁⁻¹ ∈ P.H := by
  rw [← ι.bar_bar (x₂ * x₁⁻¹)]
  refine ι.bar_mem_H ?_
  rw [show ι.bar (x₂ * x₁⁻¹) = (ι.bar x₁)⁻¹ * ι.bar x₂ by
    rw [← ι.bar_inv, ← ι.bar_mul],
    show (ι.bar x₁)⁻¹ * ι.bar x₂ =
        b₁⁻¹ * (g₂⁻¹ * a₁⁻¹ * a₂ * g₂) * b₂ by
      rw [hbarx₁, hbarx₂]
      group]
  exact P.H.mul_mem (P.H.mul_mem (P.H.inv_mem hb₁) hconj) hb₂

private lemma decompQuot_eq_of_conj_mem (g₁ : P.Δ)
    (i₁ i₂ : decompQuot P g₁) (g_D : G)
    (hxx_H : (((g₁ : G))⁻¹ * (i₂.out : G)⁻¹ * g_D) *
      (((g₁ : G))⁻¹ * (i₁.out : G)⁻¹ * g_D)⁻¹ ∈ P.H) :
    i₁ = i₂ := by
  have hconj_H :
      ((g₁ : G))⁻¹ * (i₂.out : G)⁻¹ * (i₁.out : G) * ((g₁ : G)) ∈ P.H := by
    convert hxx_H using 1
    group
  have hconj_H' :
      ((g₁ : G))⁻¹ * (i₁.out : G)⁻¹ * (i₂.out : G) * ((g₁ : G)) ∈ P.H := by
    convert P.H.inv_mem hconj_H using 1
    group
  rw [show i₁ = ⟦i₁.out⟧ from (Quotient.out_eq' i₁).symm,
      show i₂ = ⟦i₂.out⟧ from (Quotient.out_eq' i₂).symm,
      @Quotient.eq'', QuotientGroup.leftRel_apply,
      Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.smul_def]
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, inv_inv]
  convert hconj_H' using 1
  simp [Subgroup.coe_mul]
  group

private lemma conj_kernel_mem_of_stabilizer_mem
    (a₁ a₂ : P.H) (g₂ : G)
    (hrel : (a₁ : P.H)⁻¹ * a₂ ∈ (ConjAct.toConjAct g₂ • P.H).subgroupOf P.H) :
    g₂⁻¹ * (a₁ : G)⁻¹ * (a₂ : G) * g₂ ∈ P.H := by
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    ConjAct.smul_def] at hrel
  simp only [map_inv, ConjAct.ofConjAct_toConjAct, inv_inv, Subgroup.coe_mul,
    Subgroup.coe_inv] at hrel
  convert hrel using 1
  group

private lemma fwd_inj_i (g₁ g₂ : P.Δ) (g_D : G)
    (i₁ i₂ : decompQuot P g₁)
    (a₁ : P.H) (b₁ : G) (hb₁ : b₁ ∈ (P.H : Set G))
    (hbarx₁_eq : ι.bar (((g₁ : G))⁻¹ * (i₁.out : G)⁻¹ * g_D) =
      (a₁ : G) * ((g₂ : G)) * b₁)
    (a₂ : P.H) (b₂ : G) (hb₂ : b₂ ∈ (P.H : Set G))
    (hbarx₂_eq : ι.bar (((g₁ : G))⁻¹ * (i₂.out : G)⁻¹ * g_D) =
      (a₂ : G) * ((g₂ : G)) * b₂)
    (hj'_eq : (⟦a₁⟧ : decompQuot P g₂) = ⟦a₂⟧) : i₁ = i₂ := by
  rw [@Quotient.eq'', QuotientGroup.leftRel_apply] at hj'_eq
  exact decompQuot_eq_of_conj_mem g₁ i₁ i₂ g_D
    (bar_quotient_diff_mem_H ι
      (((g₁ : G))⁻¹ * (i₁.out : G)⁻¹ * g_D)
      (((g₁ : G))⁻¹ * (i₂.out : G)⁻¹ * g_D)
      ((g₂ : G))
      (a₁ : G) b₁ (a₂ : G) b₂
      a₁.2 hb₁ a₂.2 hb₂ hbarx₁_eq hbarx₂_eq
      (conj_kernel_mem_of_stabilizer_mem a₁ a₂ ((g₂ : G)) hj'_eq))

private lemma fwd_y_mem (g₁ g₂ g_D : G)
    (i_val : G) (hi : i_val ∈ (P.H : Set G))
    (a_val : G) (b_val : G) (hb : b_val ∈ (P.H : Set G))
    (hbarx_eq : ι.bar (g₁⁻¹ * i_val⁻¹ * g_D) = a_val * g₂ * b_val)
    (h1₁ h2₁ : P.H)
    (hbar₁' : ι.bar g₁ = (h1₁ : G) * g₁ * (h2₁ : G))
    (j'_val q₀_val h'_val : G)
    (hq₀_eq : q₀_val * g_D = ι.bar g_D * h'_val)
    (h'_mem : h'_val ∈ (P.H : Set G))
    (hn₂_val : G) (hn₂_mem : g₂⁻¹ * hn₂_val * g₂ ∈ P.H)
    (hj'_coe : j'_val = a_val * hn₂_val) :
    ∃ h₁ ∈ (P.H : Set G), ∃ h₂ ∈ (P.H : Set G),
      g₂⁻¹ * j'_val⁻¹ * q₀_val * g_D = h₁ * g₁ * h₂ := by
  have hab_eq : a_val * g₂ * b_val =
      ι.bar g_D * (ι.bar i_val)⁻¹ * (ι.bar g₁)⁻¹ := by
    rw [← hbarx_eq, ι.bar_mul, ι.bar_mul, ι.bar_inv, ι.bar_inv]
    group
  have key1 : g₂⁻¹ * a_val⁻¹ * ι.bar g_D =
      b_val * ι.bar g₁ * ι.bar i_val := by
    calc g₂⁻¹ * a_val⁻¹ * ι.bar g_D
        = g₂⁻¹ * a_val⁻¹ * (a_val * g₂ * b_val *
          (ι.bar g₁ * ι.bar i_val)) := by
          rw [hab_eq]
          group
      _ = _ := by group
  rw [show g₂⁻¹ * j'_val⁻¹ * q₀_val * g_D =
      (g₂⁻¹ * hn₂_val⁻¹ * g₂) * (b_val * ι.bar g₁ * ι.bar i_val) * h'_val by
    rw [hj'_coe, show g₂⁻¹ * (a_val * hn₂_val)⁻¹ * q₀_val * g_D =
      g₂⁻¹ * (a_val * hn₂_val)⁻¹ * (q₀_val * g_D) by group,
      hq₀_eq, ← key1]
    group, hbar₁']
  have hn₂_inv_mem : g₂⁻¹ * hn₂_val⁻¹ * g₂ ∈ P.H := by
    convert P.H.inv_mem hn₂_mem using 1
    group
  exact ⟨(g₂⁻¹ * hn₂_val⁻¹ * g₂) * b_val * h1₁,
    P.H.mul_mem (P.H.mul_mem hn₂_inv_mem hb) h1₁.2,
    h2₁ * ι.bar i_val * h'_val,
    P.H.mul_mem (P.H.mul_mem h2₁.2 (ι.bar_mem_H hi)) h'_mem, by group⟩

private lemma fwd_pair_mem (g₁ : P.Δ) (g₂ g_D q₀_val : G)
    (j'_val : G) (c : P.H) (d_val : G) (hd : d_val ∈ (P.H : Set G))
    (hy_eq : g₂⁻¹ * j'_val⁻¹ * q₀_val * g_D = (c : G) * (g₁ : G) * d_val) :
    ({j'_val * g₂} : Set G) * {((⟦c⟧ : decompQuot P g₁).out : G) * (g₁ : G)} *
      ↑P.H = {q₀_val * g_D} * ↑P.H := by
  rw [Set.singleton_mul_singleton]
  obtain ⟨n₁, hn₁_eq⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct ((g₁ : G)) • P.H).subgroupOf P.H) c
  have hn₁_coe : ((⟦c⟧ : decompQuot P g₁).out : G) = (c : G) * (n₁ : G) := by
    simpa [Subgroup.coe_mul] using congr_arg (Subtype.val : ↥P.H → G) hn₁_eq
  apply leftCoset_eq_of_not_disjoint
  rw [@Set.not_disjoint_iff]
  refine ⟨j'_val * g₂ * (((⟦c⟧ : decompQuot P g₁).out : G) * ((g₁ : G))),
    ⟨1, P.H.one_mem, by simp [smul_eq_mul]⟩, ?_⟩
  refine ⟨d_val⁻¹ * (((g₁ : G))⁻¹ * (n₁ : G) * ((g₁ : G))),
    P.H.mul_mem (P.H.inv_mem hd) (conj_mem_of_stabilizer ((g₁ : G)) n₁), ?_⟩
  simp only [smul_eq_mul]
  rw [hn₁_coe]
  have h_prod_eq : j'_val * g₂ * ((c : G) * ((g₁ : G)) * d_val) =
      q₀_val * g_D := by
    rw [← hy_eq]
    group
  calc q₀_val * g_D * (d_val⁻¹ * (((g₁ : G))⁻¹ * (n₁ : G) * ((g₁ : G))))
      = (q₀_val * g_D * d_val⁻¹) *
        (((g₁ : G))⁻¹ * (n₁ : G) * ((g₁ : G))) := by group
    _ = j'_val * g₂ * ((c : G) * ((g₁ : G))) *
        (((g₁ : G))⁻¹ * (n₁ : G) * ((g₁ : G))) := by
      rw [← h_prod_eq]
      group
    _ = j'_val * g₂ * ((c : G) * (n₁ : G) * ((g₁ : G))) := by group

private lemma q₀_out_mul_eq_bar_mul (D : HeckeCoset P) (h1D h2D : P.H)
    (hbarD : ι.bar (HeckeCoset.rep D : G) =
      (h1D : G) * (HeckeCoset.rep D : G) * (h2D : G))
    (q₀ : decompQuot P (HeckeCoset.rep D)) (hq₀ : q₀ = ⟦⟨(h1D : G), h1D.2⟩⟧) :
    ∃ h' : P.H, (q₀.out : G) * (HeckeCoset.rep D : G) =
      ι.bar (HeckeCoset.rep D : G) * (h' : G) := by
  subst hq₀
  obtain ⟨n, hn_eq⟩ := QuotientGroup.mk_out_eq_mul
    ((ConjAct.toConjAct (HeckeCoset.rep D : G) • P.H).subgroupOf P.H) ⟨(h1D : G), h1D.2⟩
  have hn_coe :
      ((⟦⟨(h1D : G), h1D.2⟩⟧ : decompQuot P (HeckeCoset.rep D)).out : G) =
        (h1D : G) * (n : G) := by
    simpa [Subgroup.coe_mul] using congr_arg (Subtype.val : ↥P.H → G) hn_eq
  exact ⟨⟨(h2D : G)⁻¹ * ((HeckeCoset.rep D : G)⁻¹ * (n : G) * (HeckeCoset.rep D : G)),
    P.H.mul_mem (P.H.inv_mem h2D.2) (conj_mem_of_stabilizer (HeckeCoset.rep D : G) n)⟩,
    by
      rw [hn_coe, hbarD]
      group⟩

private noncomputable def heckeMultiplicity_le_comm_fwdMap
    (h_fix : ∀ D : HeckeCoset P, ι.onHeckeCoset D = D) (D₁ D₂ D : HeckeCoset P)
    (h1D h2D : P.H)
    (hbarD : ι.bar (HeckeCoset.rep D : G) =
      (h1D : G) * (HeckeCoset.rep D : G) * (h2D : G))
    (h1₁ h2₁ : P.H)
    (hbar₁ : ι.bar (HeckeCoset.rep D₁ : G) =
      (h1₁ : G) * (HeckeCoset.rep D₁ : G) * (h2₁ : G))
    (q₀ : decompQuot P (HeckeCoset.rep D)) (hq₀ : q₀ = ⟦⟨(h1D : G), h1D.2⟩⟧)
    (p : {⟨i, j⟩ : decompQuot P (HeckeCoset.rep D₁) × decompQuot P (HeckeCoset.rep D₂) |
      ({(i.out : G) * (HeckeCoset.rep D₁ : G)} : Set G) *
        {(j.out : G) * (HeckeCoset.rep D₂ : G)} * P.H =
      {(HeckeCoset.rep D : G)} * (P.H : Set G)}) :
    {p : decompQuot P (HeckeCoset.rep D₂) × decompQuot P (HeckeCoset.rep D₁) |
      ({(p.1.out : G) * (HeckeCoset.rep D₂ : G)} : Set G) *
        {(p.2.out : G) * (HeckeCoset.rep D₁ : G)} * P.H =
      {(q₀.out : G) * (HeckeCoset.rep D : G)} * (P.H : Set G)} :=
  let i := p.1.1
  let j := p.1.2
  let hcond : ({(i.out : G) * (HeckeCoset.rep D₁ : G)} : Set G) *
      {(j.out : G) * (HeckeCoset.rep D₂ : G)} * P.H =
      {(HeckeCoset.rep D : G)} * (P.H : Set G) := p.2
  let x : G := (HeckeCoset.rep D₁ : G)⁻¹ * (i.out : G)⁻¹ * (HeckeCoset.rep D : G)
  have hbarx_dc : ∃ h₁ ∈ (P.H : Set G), ∃ h₂ ∈ (P.H : Set G),
      ι.bar x = h₁ * (HeckeCoset.rep D₂ : G) * h₂ := by
    have := bar_mem_doubleCoset ι h_fix D₂ x
      (inverse_product_mem_doubleCoset (HeckeCoset.rep D₁ : G) (HeckeCoset.rep D₂ : G)
        (HeckeCoset.rep D : G) D₂ rfl i.out j.out hcond)
    rwa [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at this
  let a : P.H := ⟨hbarx_dc.choose, hbarx_dc.choose_spec.1⟩
  let j' : decompQuot P (HeckeCoset.rep D₂) := ⟦a⟧
  have hy_mem_D₁ : (HeckeCoset.rep D₂ : G)⁻¹ * (j'.out : G)⁻¹ * (q₀.out : G) *
      (HeckeCoset.rep D : G) ∈ HeckeCoset.toSet D₁ := by
    rw [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset]
    obtain ⟨h', hq₀_eq⟩ := q₀_out_mul_eq_bar_mul ι D h1D h2D hbarD q₀ hq₀
    obtain ⟨n₂, hn₂_eq⟩ := QuotientGroup.mk_out_eq_mul
      ((ConjAct.toConjAct (HeckeCoset.rep D₂ : G) • P.H).subgroupOf P.H) a
    exact fwd_y_mem ι (HeckeCoset.rep D₁ : G) (HeckeCoset.rep D₂ : G)
      (HeckeCoset.rep D : G) (i.out : G) i.out.2 (a : G)
      hbarx_dc.choose_spec.2.choose hbarx_dc.choose_spec.2.choose_spec.1
      hbarx_dc.choose_spec.2.choose_spec.2 h1₁ h2₁ hbar₁
      (j'.out : G) (q₀.out : G) (h' : G) hq₀_eq h'.2 (n₂ : G)
      (conj_mem_of_stabilizer (HeckeCoset.rep D₂ : G) n₂)
      (by simpa [Subgroup.coe_mul] using congr_arg (Subtype.val : ↥P.H → G) hn₂_eq)
  have hy_dc : ∃ h₁ ∈ (P.H : Set G), ∃ h₂ ∈ (P.H : Set G),
      (HeckeCoset.rep D₂ : G)⁻¹ * (j'.out : G)⁻¹ * (q₀.out : G) * (HeckeCoset.rep D : G) =
        h₁ * (HeckeCoset.rep D₁ : G) * h₂ := by
    rwa [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at hy_mem_D₁
  let c : P.H := ⟨hy_dc.choose, hy_dc.choose_spec.1⟩
  ⟨⟨j', ⟦c⟧⟩, fwd_pair_mem (HeckeCoset.rep D₁) (HeckeCoset.rep D₂ : G)
    (HeckeCoset.rep D : G) (q₀.out : G) (j'.out : G) c
    hy_dc.choose_spec.2.choose hy_dc.choose_spec.2.choose_spec.1
    (hy_dc.choose_spec.2.choose_spec.2 ▸ rfl)⟩

private lemma heckeMultiplicity_le_comm_fwdMap_injective
    (h_fix : ∀ D : HeckeCoset P, ι.onHeckeCoset D = D) (D₁ D₂ D : HeckeCoset P)
    (h1D h2D : P.H)
    (hbarD : ι.bar (HeckeCoset.rep D : G) =
      (h1D : G) * (HeckeCoset.rep D : G) * (h2D : G))
    (h1₁ h2₁ : P.H)
    (hbar₁ : ι.bar (HeckeCoset.rep D₁ : G) =
      (h1₁ : G) * (HeckeCoset.rep D₁ : G) * (h2₁ : G))
    (q₀ : decompQuot P (HeckeCoset.rep D)) (hq₀ : q₀ = ⟦⟨(h1D : G), h1D.2⟩⟧) :
    Function.Injective
      (heckeMultiplicity_le_comm_fwdMap ι h_fix D₁ D₂ D h1D h2D hbarD h1₁ h2₁ hbar₁
        q₀ hq₀) := by
  set g₁ := (HeckeCoset.rep D₁ : G)
  set g₂ := (HeckeCoset.rep D₂ : G)
  set g_D := (HeckeCoset.rep D : G)
  intro ⟨⟨i₁, j₁⟩, h₁⟩ ⟨⟨i₂, j₂⟩, h₂⟩ heq
  have hj'_eq := congr_arg Prod.fst (congr_arg Subtype.val heq)
  have bar_dc (i' : decompQuot P (HeckeCoset.rep D₁))
      (j' : decompQuot P (HeckeCoset.rep D₂))
      (hc : ({(i'.out : G) * g₁} : Set G) * {(j'.out : G) * g₂} * ↑P.H =
        {g_D} * ↑P.H) : ∃ h₁ ∈ (P.H : Set G), ∃ h₂ ∈ (P.H : Set G),
      ι.bar (g₁⁻¹ * (i'.out : G)⁻¹ * g_D) = h₁ * g₂ * h₂ := by
    have := bar_mem_doubleCoset ι h_fix D₂ _
      (inverse_product_mem_doubleCoset g₁ g₂ g_D D₂ rfl i'.out j'.out hc)
    rwa [HeckeCoset.toSet_eq_rep, DoubleCoset.mem_doubleCoset] at this
  have hbarx₁_dc := bar_dc i₁ j₁ h₁
  have hbarx₂_dc := bar_dc i₂ j₂ h₂
  change (⟦⟨hbarx₁_dc.choose, hbarx₁_dc.choose_spec.1⟩⟧ :
      decompQuot P (HeckeCoset.rep D₂)) =
    ⟦⟨hbarx₂_dc.choose, hbarx₂_dc.choose_spec.1⟩⟧ at hj'_eq
  have hi₁₂ : i₁ = i₂ := fwd_inj_i ι (HeckeCoset.rep D₁) (HeckeCoset.rep D₂)
    g_D i₁ i₂
    ⟨hbarx₁_dc.choose, hbarx₁_dc.choose_spec.1⟩
    hbarx₁_dc.choose_spec.2.choose hbarx₁_dc.choose_spec.2.choose_spec.1
    hbarx₁_dc.choose_spec.2.choose_spec.2
    ⟨hbarx₂_dc.choose, hbarx₂_dc.choose_spec.1⟩
    hbarx₂_dc.choose_spec.2.choose hbarx₂_dc.choose_spec.2.choose_spec.1
    hbarx₂_dc.choose_spec.2.choose_spec.2 hj'_eq
  subst hi₁₂
  have hj₁₂ : j₁ = j₂ := by
    by_contra hne
    apply decompQuot_coset_diff P (HeckeCoset.rep D₂) j₁ j₂ hne
    exact set_singleton_mul_left_cancel ((i₁.out : G) * g₁)
      (by
        have := h₁.trans h₂.symm
        rwa [mul_assoc, mul_assoc] at this)
  subst hj₁₂
  rfl

private lemma heckeMultiplicity_le_comm (h_fix : ∀ D : HeckeCoset P, ι.onHeckeCoset D = D)
    (D₁ D₂ D : HeckeCoset P) :
    heckeMultiplicity P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (HeckeCoset.rep D) ≤
    heckeMultiplicity P (HeckeCoset.rep D₂) (HeckeCoset.rep D₁) (HeckeCoset.rep D) := by
  obtain ⟨h1D, h2D, hbarD⟩ := bar_rep_mem_doubleCoset ι h_fix D
  obtain ⟨h1₁, h2₁, hbar₁⟩ := bar_rep_mem_doubleCoset ι h_fix D₁
  set q₀ : decompQuot P (HeckeCoset.rep D) := ⟦⟨(h1D : G), h1D.2⟩⟧ with hq₀
  unfold heckeMultiplicity
  rw [← heckeMultiplicity_uniform P (HeckeCoset.rep D₂) (HeckeCoset.rep D₁) D q₀]
  exact_mod_cast Nat.card_le_card_of_injective
    (heckeMultiplicity_le_comm_fwdMap ι h_fix D₁ D₂ D h1D h2D hbarD h1₁ h2₁ hbar₁
      q₀ hq₀)
    (heckeMultiplicity_le_comm_fwdMap_injective ι h_fix D₁ D₂ D h1D h2D hbarD
      h1₁ h2₁ hbar₁ q₀ hq₀)

/-- When the anti-involution fixes all double cosets,
the multiplicity is symmetric:
`heckeMultiplicity(D₁, D₂, D) = heckeMultiplicity(D₂, D₁, D)`
(Shimura Proposition 3.8). -/
lemma heckeMultiplicity_comm_of_onHeckeCoset_eq
    (h_fix : ∀ D : HeckeCoset P, ι.onHeckeCoset D = D)
    (D₁ D₂ D : HeckeCoset P) :
    heckeMultiplicity P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) (HeckeCoset.rep D) =
    heckeMultiplicity P (HeckeCoset.rep D₂) (HeckeCoset.rep D₁) (HeckeCoset.rep D) :=
  le_antisymm (ι.heckeMultiplicity_le_comm h_fix D₁ D₂ D)
    (ι.heckeMultiplicity_le_comm h_fix D₂ D₁ D)

/-- When the anti-involution fixes all double cosets,
the multiplication finsupp is symmetric: `m(D₁, D₂) = m(D₂, D₁)`. -/
lemma m_comm_of_onHeckeCoset_eq (h_fix : ∀ D : HeckeCoset P, ι.onHeckeCoset D = D)
    (D₁ D₂ : HeckeCoset P) :
    m P (HeckeCoset.rep D₁) (HeckeCoset.rep D₂) =
    m P (HeckeCoset.rep D₂) (HeckeCoset.rep D₁) := by
  ext D
  simpa only [m, Finsupp.coe_mk] using
    heckeMultiplicity_comm_of_onHeckeCoset_eq ι h_fix D₁ D₂ D

/-- Shimura Proposition 3.8: the Hecke ring is commutative when the anti-involution
fixes every double coset. -/
theorem mul_comm_of_antiInvolution (h_fix : ∀ D : HeckeCoset P, ι.onHeckeCoset D = D)
    (f g : 𝕋 P ℤ) : f * g = g * f := by
  apply induction_linear_𝕋 P f
  · simp
  · intro D₁ a
    apply induction_linear_𝕋 P g
    · simp
    · intro D₂ b
      rw [T_single_mul_T_single, T_single_mul_T_single,
        m_comm_of_onHeckeCoset_eq ι h_fix D₁ D₂, smul_comm]
    · intro g₁ g₂ hg₁ hg₂
      rw [mul_add, add_mul, hg₁, hg₂]
  · intro f₁ f₂ hf₁ hf₂
    rw [add_mul, mul_add, hf₁, hf₂]

end AntiInvolution

/-- Shimura Proposition 3.8: `CommRing (𝕋 P ℤ)` from an anti-involution
fixing every double coset. -/
@[reducible]
noncomputable def instCommRing_of_antiInvolution (ι : AntiInvolution P)
    (h_fix : ∀ D : HeckeCoset P, ι.onHeckeCoset D = D) : CommRing (𝕋 P ℤ) :=
  { HeckeRing.instRing P with mul_comm := ι.mul_comm_of_antiInvolution h_fix }

end HeckeRing
