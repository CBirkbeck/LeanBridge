import TauCeti.NumberTheory.ModularForms.Newforms.Newform
import TauCeti.NumberTheory.ModularForms.SturmBound
import TauCeti.NumberTheory.ModularForms.TrivialNebentypus

/-!
# The Sturm bound of a space of modular forms with character

The LMFDB's Sturm bound of the space `M_k(N, χ)` is `⌊k m / 12⌋`, where `m = [SL₂(ℤ) : Γ₀(N)]`:
two forms of `M_k(N, χ)` whose `q`-expansions agree up to that index are equal. Tau Ceti proves
this for `Γ₀(N)`, that is for the trivial character (`TauCeti.ModularForm.eq_of_sturm_bound`), and
for a general character only the weaker bound of `Γ₁(N)`. Here it is proved for every character
`χ` by the classical argument: if `h ∈ M_k(N, χ)` vanishes at `∞` to order greater than
`k m / 12`, then `h^r`, for `r` the order of `(ℤ/Nℤ)ˣ`, has trivial character, weight `r k` and
order greater than `r k m / 12`, so it vanishes by the bound for `Γ₀(N)`, and so does `h`.

## Main definitions

* `ModularForm.sturmBound` (LMFDB `cmf.sturm_bound`).

## Main results

* `ModularForm.eq_zero_of_sturmBound_lt_order`: a form of `M_k(N, χ)` vanishing at `∞` to order
  greater than the Sturm bound is zero.
* `ModularForm.eq_of_sturmBound`: two forms of `M_k(N, χ)` whose `q`-expansions agree up to the
  Sturm bound are equal.
* `HeckeRing.GL2.Newform.eq_of_sturmBound`: two newforms of the same level, weight and character
  whose `q`-expansions agree up to the Sturm bound are equal.
-/

open CongruenceSubgroup Matrix.SpecialLinearGroup UpperHalfPlane TauCeti
open scoped MatrixGroups ModularForm

namespace ModularForm

variable (N : ℕ) (k : ℤ)

/-- The **Sturm bound** (LMFDB `cmf.sturm_bound`) of the spaces `M_k(N, χ)` of modular forms of
level `N` and weight `k`: the integer `⌊k m / 12⌋`, where `m = [SL₂(ℤ) : Γ₀(N)]`. It does not
depend on the character `χ`, and two forms of `M_k(N, χ)` whose `q`-expansions agree up to it are
equal (`ModularForm.eq_of_sturmBound`).

The LMFDB also writes `m = N ∏_{p ∣ N} (1 + 1/p)`; that closed form is not used here. The weight
of an LMFDB space is positive; for `k ≤ 0` the definition gives `0`. -/
noncomputable def sturmBound : ℕ :=
  (k * (Gamma0 N).index).toNat / 12

variable {N k} [NeZero N] {χ : (ZMod N)ˣ →* ℂˣ} {f g : ModularForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ modFormCharSpace k χ) (hg : g ∈ modFormCharSpace k χ)

private lemma pow_slash_mapGL (γ : SL(2, ℤ)) (φ : ℍ → ℂ) (n : ℕ) :
    (φ ^ n) ∣[(n : ℤ) * k] mapGL ℝ γ = (φ ∣[k] mapGL ℝ γ) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, Nat.cast_zero, zero_mul]
    exact is_invariant_one' γ
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, pow_succ, mul_slash, ih, det_mapGL, Units.val_one, abs_one,
      one_smul, pow_succ]

include hf in
private lemma pow_mem_modFormCharSpace_one :
    f.pow (Fintype.card (ZMod N)ˣ) ∈ modFormCharSpace ((Fintype.card (ZMod N)ˣ : ℤ) * k) 1 := by
  rw [mem_modFormCharSpace_one_iff]
  rintro _ ⟨γ, hγ, rfl⟩
  rw [coe_pow, pow_slash_mapGL, (mem_modFormCharSpace_iff_nebentypus k χ f).mp hf ⟨γ, hγ⟩,
    smul_pow, ← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one,
    one_smul]

include hf in
/-- **Sturm's theorem for `M_k(N, χ)`**: a modular form of level `N`, weight `k` and character `χ`
whose `q`-expansion at `∞` has order greater than the Sturm bound is zero. -/
lemma eq_zero_of_sturmBound_lt_order (hord : (sturmBound N k : ℕ∞) < (qExpansion 1 f).order) :
    f = 0 := by
  let r : ℕ := Fintype.card (ZMod N)ˣ
  have hr : 0 < r := Fintype.card_pos
  let F : ModularForm ((Gamma0 N).map (mapGL ℝ)) (r * k) :=
    modFormCharSpaceOneEquiv N (r * k) ⟨f.pow r, pow_mem_modFormCharSpace_one hf⟩
  have hF : ⇑F = ⇑f ^ r := by
    rw [coe_modFormCharSpaceOneEquiv_apply, coe_pow]
  have hq : qExpansion ((Gamma0 N).map (mapGL ℝ)).strictWidthInfty F = qExpansion 1 f ^ r := by
    rw [strictWidthInfty_Gamma0, hF, ← coe_pow, ModularForm.qExpansion_pow one_pos
      (one_mem_strictPeriods_Gamma1_map N)]
  have hK : (k * (Gamma0 N).index).toNat < 12 * (sturmBound N k + 1) :=
    Nat.lt_mul_div_succ _ (by norm_num)
  have hlt : ((r * k * (Gamma0 N).index).toNat / 12 : ℕ) < r * (sturmBound N k + 1) := by
    have hle : (r : ℤ) * (k * (Gamma0 N).index) ≤ r * (k * (Gamma0 N).index).toNat :=
      mul_le_mul_of_nonneg_left (Int.self_le_toNat _) r.cast_nonneg
    have hlt' : (r : ℤ) * (k * (Gamma0 N).index).toNat < r * (12 * (sturmBound N k + 1)) :=
      mul_lt_mul_of_pos_left (by exact_mod_cast hK) (Nat.cast_pos.mpr hr)
    rw [Nat.div_lt_iff_lt_mul (by norm_num), Int.toNat_lt' (by positivity)]
    push_cast
    linarith
  have hF0 : F = 0 := by
    refine ModularForm.sturm_bound_finiteIndex_SL2Z F ?_
    rw [hq, PowerSeries.order_pow]
    refine (ENat.natCast_lt_natCast.mpr hlt).trans_le ?_
    rw [Nat.cast_mul, ← nsmul_eq_mul]
    exact nsmul_le_nsmul_right (Order.add_one_le_of_lt hord) r
  refine ModularForm.ext fun z ↦ ?_
  have hz : f z ^ r = 0 := by
    rw [← Pi.pow_apply, ← hF, hF0, FunLike.coe_zero, Pi.zero_apply]
  exact pow_eq_zero_iff hr.ne' |>.mp hz

include hf hg in
/-- **Modular forms in `M_k(N, χ)` agreeing up to the Sturm bound are equal**: two forms of level
`N`, weight `k` and character `χ` whose `q`-expansions agree in every coefficient of index at most
`ModularForm.sturmBound N k` are equal. -/
lemma eq_of_sturmBound
    (h : ∀ n ≤ sturmBound N k, (qExpansion 1 f).coeff n = (qExpansion 1 g).coeff n) : f = g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_sturmBound_lt_order (sub_mem hf hg) <|
    (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self _)).trans_le <|
      PowerSeries.nat_le_order _ _ fun n hn ↦ ?_
  rw [FunLike.coe_sub, ModularForm.qExpansion_sub one_pos (one_mem_strictPeriods_Gamma1_map N),
    map_sub, sub_eq_zero]
  exact h n (Nat.lt_succ_iff.mp hn)

end ModularForm

namespace HeckeRing.GL2.Newform

variable {N : ℕ} [NeZero N] {k : ℤ}

/-- **Newforms agreeing up to the Sturm bound are equal**: two newforms of level `N`, weight `k`
and the same character whose `q`-expansions agree in every coefficient of index at most
`ModularForm.sturmBound N k` are equal. -/
lemma eq_of_sturmBound {f g : Newform N k} (hχ : f.χ = g.χ) (h : ∀ n ≤ ModularForm.sturmBound N k,
    (qExpansion 1 f.toCuspForm).coeff n = (qExpansion 1 g.toCuspForm).coeff n) : f = g := by
  refine Newform.ext <| CuspForm.toModularFormₗ_injective ?_
  exact ModularForm.eq_of_sturmBound ((coe_mem_modFormCharSpace_iff k f.χ _).mpr f.mem_charSpace)
    ((coe_mem_modFormCharSpace_iff k f.χ _).mpr (hχ ▸ g.mem_charSpace)) h

end HeckeRing.GL2.Newform
