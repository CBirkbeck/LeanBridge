import LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Jacobi.Basic

/-!
# The index raising operators on Jacobi forms of index `1`

For `m ≥ 1`, the index raising operator `V_m` of Eichler and Zagier (§4) sends a function
`φ : ℍ × ℂ → ℂ` to `(φ ∣ V_m)(τ, z) = m⁻¹ ∑ a^k φ((aτ + b)/d, az)`, the sum running over the upper
triangular representatives `(a, b; 0, d)`, `ad = m`, `0 ≤ b < d`, of the cosets `SL(2, ℤ) \ M_m` of
the integral matrices of determinant `m`; this is Eichler and Zagier's
`m^{k-1} ∑ d^{-k} φ((aτ + b)/d, az)`. If `φ` transforms like a Jacobi form of weight `k` and index
`1` under `SL(2, ℤ)`, then `φ ∣ V_m` transforms like a Jacobi form of weight `k` and index `m` under
`S = (0, -1; 1, 0)`: `(φ ∣ V_m)(-1/τ, z/τ) = τ^k e^{2πimz²/τ} (φ ∣ V_m)(τ, z)`. For `φ` of index
`N ≥ 1`, the same law with index `Nm` is `ModularForm.indexRaising_S_of_index`, in
`LeanBridge.ForMathlib.NumberTheory.AutomorphicForms.Siegel.GritsenkoLiftModularity`.

The proof follows the coset argument. Right multiplication by `S` permutes the cosets: with
`g = gcd(b, d)`, `b = gb₁`, `d = gd₁` and `v ∈ [0, d₁)` the residue of `-b₁⁻¹` modulo `d₁`,
`(a, b; 0, d) S = γ (g, av; 0, ad₁)` for `γ = (b₁, -y; d₁, -v) ∈ SL(2, ℤ)`, `y = (b₁v + 1)/d₁`, and
the map `(a, b, d) ↦ (g, av, ad₁)` is an involution of the set of representatives. The
transformation law of `φ` under `γ` then turns the term of `(a, b; 0, d)` at `S(τ, z)` into
`τ^k e^{2πimz²/τ}` times the term of `(g, av; 0, ad₁)` at `(τ, z)`.

## Main definitions

* `ModularForm.affinePoint`: the point `(pτ + q)/s` of `ℍ`.
* `ModularForm.cosetReps`: the representatives `(a, b, d)`, `ad = m`, `0 ≤ b < d`.
* `ModularForm.cosetTerm`: the term `a^k φ((aτ + b)/d, az)`.
* `ModularForm.indexRaising`: the index raising operator `φ ↦ φ ∣ V_m`.

## Main results

* `ModularForm.apply_S_affinePoint`: the transformation of a single term under `S`.
* `ModularForm.indexRaising_S`: the transformation law of `φ ∣ V_m` under `S`.
-/

open Complex ModularGroup Real

open scoped MatrixGroups UpperHalfPlane

namespace ModularForm

variable {k : ℤ} {φ : ℍ × ℂ → ℂ} (p q s : ℤ) (τ : ℍ) {m : ℕ} (t : ℕ × ℕ × ℕ) (x : ℍ × ℂ)

/-- The point `(pτ + q)/s` of the upper half-plane, for integers `p, s > 0`, and the junk value
`τ` otherwise. -/
noncomputable def affinePoint : ℍ :=
  if h : 0 < p ∧ 0 < s then UpperHalfPlane.mk ((p * τ + q) / s) <| by
    have h' : ((p * τ + q) / s : ℂ).im = p * τ.im / s := by
      simp
    rw [h']
    exact div_pos (mul_pos (by exact_mod_cast h.1) τ.im_pos) (by exact_mod_cast h.2)
  else τ

variable {p s} in
lemma coe_affinePoint (hp : 0 < p) (hs : 0 < s) : (affinePoint p q s τ : ℂ) = (p * τ + q) / s := by
  rw [affinePoint, dite_eq_left ⟨hp, hs⟩]

/-- **The transformation of a coset term of the index raising operator under `S`**: if `φ`
transforms like a Jacobi form of weight `k` and index `1` under `SL(2, ℤ)`, `a, g, d₁ > 0` and
`b₁u + d₁v = 1`, then, with `d = gd₁`,
`φ((a(-1/τ) + gb₁)/d, az/τ) = (gτ/a)^k e^{2πiadz²/τ} φ((gτ - ua)/(ad₁), gz)`, by the transformation
law under `(b₁, -v; d₁, u)`, which sends `(gτ - ua)/(ad₁)` to `(a(-1/τ) + gb₁)/d`. -/
lemma apply_S_affinePoint (hφ : ∀ (γ : SL(2, ℤ)) x,
    φ (γ • x.1, x.2 / UpperHalfPlane.denom γ x.1) = jacobiFactor k 1 x γ * φ x) {a g b₁ d₁ u v : ℤ}
    (ha : 0 < a) (hg : 0 < g) (hd₁ : 0 < d₁) (huv : b₁ * u + d₁ * v = 1) (z : ℂ) :
    φ (affinePoint a (g * b₁) (g * d₁) (S • τ), a * z / τ) = (g * τ / a) ^ k *
      cexp (2 * π * I * (a * (g * d₁)) * z ^ 2 / τ) *
      φ (affinePoint g (-(u * a)) (a * d₁) τ, g * z) := by
  let γ : SL(2, ℤ) := ⟨!![b₁, -v; d₁, u], by
    rw [Matrix.det_fin_two_of]
    linear_combination huv⟩
  have hτ : (τ : ℂ) ≠ 0 := τ.ne_zero
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hd₁' : (d₁ : ℂ) ≠ 0 := by exact_mod_cast hd₁.ne'
  have hg' : (g : ℂ) ≠ 0 := by exact_mod_cast hg.ne'
  have huv' : (b₁ * u + d₁ * v : ℂ) = 1 := by exact_mod_cast huv
  have hdenom : UpperHalfPlane.denom γ (affinePoint g (-(u * a)) (a * d₁) τ) = g * τ / a := by
    rw [ModularGroup.denom_apply, coe_affinePoint _ _ hg (mul_pos ha hd₁)]
    simp [γ]
    field_simp
    ring1
  have hw : γ • affinePoint g (-(u * a)) (a * d₁) τ = affinePoint a (g * b₁) (g * d₁) (S • τ) :=
    UpperHalfPlane.ext <| by
      rw [UpperHalfPlane.coe_specialLinearGroup_apply, coe_affinePoint _ _ hg (mul_pos ha hd₁),
        coe_affinePoint _ _ ha (mul_pos hg hd₁), UpperHalfPlane.modular_S_smul]
      simp [γ]
      field_simp
      linear_combination (-(g : ℂ) * τ * a) * huv'
  have hz : (a : ℂ) * z / τ = g * z / (g * τ / a) := by
    field_simp
  have h : φ (γ • affinePoint g (-(u * a)) (a * d₁) τ,
      g * z / UpperHalfPlane.denom γ (affinePoint g (-(u * a)) (a * d₁) τ)) =
        jacobiFactor k 1 (affinePoint g (-(u * a)) (a * d₁) τ, g * z) γ *
          φ (affinePoint g (-(u * a)) (a * d₁) τ, g * z) :=
    hφ γ (affinePoint g (-(u * a)) (a * d₁) τ, g * z)
  rw [hw, hdenom] at h
  rw [hz, h, jacobiFactor]
  dsimp only
  rw [hdenom]
  congr 3
  simp [γ]
  field_simp

variable {a g b₁ d₁ n b : ℕ}

/-- The representative `(g, av; 0, ad₁)` of the coset of `(a, b; 0, d) S`, where `g = gcd(b, d)`,
`b = gb₁`, `d = gd₁` and `v ∈ [0, d₁)` is the residue of `-b₁⁻¹` modulo `d₁`. -/
private def cosetS : ℕ × ℕ × ℕ :=
  (t.2.1.gcd t.2.2,
    t.1 * (-((t.2.1 / t.2.1.gcd t.2.2 : ℕ) : ZMod (t.2.2 / t.2.1.gcd t.2.2))⁻¹).val,
    t.1 * (t.2.2 / t.2.1.gcd t.2.2))

private lemma cosetS_mul (hg : 0 < g) (hcop : b₁.Coprime d₁) :
    cosetS (a, g * b₁, g * d₁) = (g, a * (-(b₁ : ZMod d₁)⁻¹).val, a * d₁) := by
  have hgcd : (g * b₁).gcd (g * d₁) = g := by
    rw [Nat.gcd_mul_left, hcop.gcd_eq_one, mul_one]
  rw [cosetS]
  dsimp only
  rw [hgcd, Nat.mul_div_cancel_left _ hg, Nat.mul_div_cancel_left _ hg]

private lemma neg_inv_mul_neg (hcop : b.Coprime n) : -(b : ZMod n)⁻¹ * -(b : ZMod n) = 1 := by
  rw [neg_mul_neg, mul_comm, ZMod.coe_mul_inv_eq_one b hcop]

variable [NeZero n] in
private lemma coprime_val_neg_inv (hcop : b.Coprime n) : (-(b : ZMod n)⁻¹).val.Coprime n := by
  rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
  exact IsUnit.of_mul_eq_one _ <| neg_inv_mul_neg hcop

variable [NeZero n] in
private lemma dvd_mul_val_neg_inv_add_one (hcop : b.Coprime n) :
    n ∣ b * (-(b : ZMod n)⁻¹).val + 1 := by
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  rw [ZMod.natCast_zmod_val, mul_neg, ZMod.coe_mul_inv_eq_one b hcop, neg_add_cancel]

variable [NeZero n] in
private lemma val_neg_inv_val_neg_inv (hb : b < n) (hcop : b.Coprime n) :
    (-(((-(b : ZMod n)⁻¹).val : ℕ) : ZMod n)⁻¹).val = b := by
  have hw : -(b : ZMod n)⁻¹ * (-(b : ZMod n)⁻¹)⁻¹ = 1 :=
    ZMod.mul_inv_of_unit _ <| IsUnit.of_mul_eq_one _ <| neg_inv_mul_neg hcop
  have h : (-(b : ZMod n)⁻¹)⁻¹ = -(b : ZMod n) := by
    linear_combination (-(-(b : ZMod n)⁻¹)⁻¹) * neg_inv_mul_neg hcop + (-(b : ZMod n)) * hw
  rw [ZMod.natCast_zmod_val, h, neg_neg, ZMod.val_natCast, Nat.mod_eq_of_lt hb]

private lemma cosetS_cosetS (ha : 0 < a) (hg : 0 < g) (hcop : b₁.Coprime d₁) (hb₁ : b₁ < d₁) :
    cosetS (cosetS (a, g * b₁, g * d₁)) = (a, g * b₁, g * d₁) := by
  have : NeZero d₁ := ⟨by omega⟩
  rw [cosetS_mul hg hcop, cosetS_mul ha (coprime_val_neg_inv hcop),
    val_neg_inv_val_neg_inv hb₁ hcop]

variable (k φ) in
/-- The term `a^k φ((aτ + b)/d, az)` of the index raising operator for the coset of
`(a, b; 0, d)`, `t = (a, b, d)`. -/
noncomputable def cosetTerm : ℂ :=
  (t.1 : ℂ) ^ k * φ (affinePoint t.1 t.2.1 t.2.2 x.1, t.1 * x.2)

private lemma cosetTerm_S (hφ : ∀ (γ : SL(2, ℤ)) x,
    φ (γ • x.1, x.2 / UpperHalfPlane.denom γ x.1) = jacobiFactor k 1 x γ * φ x) (ha : 0 < a)
    (hg : 0 < g) (hcop : b₁.Coprime d₁) (hb₁ : b₁ < d₁) :
    cosetTerm k φ (a, g * b₁, g * d₁) (S • x.1, x.2 / UpperHalfPlane.denom S x.1) =
      (x.1 : ℂ) ^ k * cexp (2 * π * I * (a * (g * d₁) : ℕ) * x.2 ^ 2 / x.1) *
        cosetTerm k φ (cosetS (a, g * b₁, g * d₁)) x := by
  have hd₁ : 0 < d₁ := by omega
  have : NeZero d₁ := ⟨hd₁.ne'⟩
  rcases dvd_mul_val_neg_inv_add_one hcop with ⟨y, hy⟩
  have hy' : (b₁ : ℤ) * (-(b₁ : ZMod d₁)⁻¹).val + 1 = d₁ * y := by
    exact_mod_cast hy
  have h : φ (affinePoint a (g * b₁) (g * d₁) (S • x.1), a * x.2 / x.1) = (g * x.1 / a) ^ k *
      cexp (2 * π * I * (a * (g * d₁)) * x.2 ^ 2 / x.1) *
        φ (affinePoint g (-(-((-(b₁ : ZMod d₁)⁻¹).val : ℤ) * a)) (a * d₁) x.1, g * x.2) := by
    exact_mod_cast apply_S_affinePoint x.1 hφ (a := a) (g := g) (b₁ := b₁) (d₁ := d₁)
      (u := -((-(b₁ : ZMod d₁)⁻¹).val : ℤ)) (v := y) (by exact_mod_cast ha) (by exact_mod_cast hg)
      (by exact_mod_cast hd₁) (by linear_combination -hy') x.2
  have hq : -(-((-(b₁ : ZMod d₁)⁻¹).val : ℤ) * a) = a * (-(b₁ : ZMod d₁)⁻¹).val := by
    ring1
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [hq] at h
  rw [cosetS_mul hg hcop, cosetTerm, cosetTerm]
  dsimp only
  rw [ModularGroup.denom_S]
  simp only [Nat.cast_mul]
  rw [← mul_div_assoc, h, div_zpow, mul_zpow]
  field_simp

variable (m) in
/-- The triples `(a, b, d)` of natural numbers with `ad = m` and `b < d`, the upper triangular
representatives `(a, b; 0, d)` of the cosets `SL(2, ℤ) \ M_m` of the integral matrices of
determinant `m ≥ 1`. -/
def cosetReps : Finset (ℕ × ℕ × ℕ) :=
  (Finset.range (m + 1) ×ˢ Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter
    fun t ↦ t.1 * t.2.2 = m ∧ t.2.1 < t.2.2

variable {t} in
lemma mem_cosetReps (hm : 0 < m) : t ∈ cosetReps m ↔ t.1 * t.2.2 = m ∧ t.2.1 < t.2.2 := by
  simp only [cosetReps, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨⟨?_, ?_, ?_⟩, h⟩⟩
  · exact Nat.lt_succ_of_le (Nat.le_of_dvd hm ⟨t.2.2, h.1.symm⟩)
  · exact Nat.lt_succ_of_le (h.2.trans_le (Nat.le_of_dvd hm ⟨t.1, by rw [← h.1, mul_comm]⟩)).le
  · exact Nat.lt_succ_of_le (Nat.le_of_dvd hm ⟨t.1, by rw [← h.1, mul_comm]⟩)

private lemma eq_gcd_mul : t = (t.1, t.2.1.gcd t.2.2 * (t.2.1 / t.2.1.gcd t.2.2),
    t.2.1.gcd t.2.2 * (t.2.2 / t.2.1.gcd t.2.2)) := by
  rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _), Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)]

variable (k φ m) in
/-- The **index raising operator** `V_m` of Eichler and Zagier (§4) on functions `φ : ℍ × ℂ → ℂ`,
in weight `k`: `(φ ∣ V_m)(τ, z) = m⁻¹ ∑ a^k φ((aτ + b)/d, az)` over the representatives
`(a, b; 0, d)`, `ad = m`, `0 ≤ b < d`, of `SL(2, ℤ) \ M_m`, that is
`m^{k-1} ∑ d^{-k} φ((aτ + b)/d, az)`. For `m ≥ 1` it maps Jacobi forms of weight `k` and index `1`
to Jacobi forms of weight `k` and index `m`. -/
noncomputable def indexRaising : ℂ :=
  (m : ℂ)⁻¹ * ∑ t ∈ cosetReps m, cosetTerm k φ t x

/-- **The index raising operator `V_m` preserves the transformation law under `S`**: if `φ`
transforms like a Jacobi form of weight `k` and index `1` under `SL(2, ℤ)`, then `φ ∣ V_m`
transforms like a Jacobi form of weight `k` and index `m` under `S = (0, -1; 1, 0)`,
`(φ ∣ V_m)(-1/τ, z/τ) = τ^k e^{2πimz²/τ} (φ ∣ V_m)(τ, z)`: right multiplication by `S` permutes the
cosets `SL(2, ℤ) \ M_m`. -/
lemma indexRaising_S (hφ : ∀ (γ : SL(2, ℤ)) x,
    φ (γ • x.1, x.2 / UpperHalfPlane.denom γ x.1) = jacobiFactor k 1 x γ * φ x) (hm : 0 < m) :
    indexRaising k φ m (S • x.1, x.2 / UpperHalfPlane.denom S x.1) =
      jacobiFactor k m x S * indexRaising k φ m x := by
  have hJ : jacobiFactor k m x S = (x.1 : ℂ) ^ k * cexp (2 * π * I * m * x.2 ^ 2 / x.1) := by
    rw [jacobiFactor, ModularGroup.denom_S]
    simp
  have hfacts (t : ℕ × ℕ × ℕ) (ht : t ∈ cosetReps m) : 0 < t.1 ∧ 0 < t.2.1.gcd t.2.2 ∧
      (t.2.1 / t.2.1.gcd t.2.2).Coprime (t.2.2 / t.2.1.gcd t.2.2) ∧
        t.2.1 / t.2.1.gcd t.2.2 < t.2.2 / t.2.1.gcd t.2.2 := by
    rw [mem_cosetReps hm] at ht
    have hg : 0 < t.2.1.gcd t.2.2 := Nat.gcd_pos_of_pos_right _ (by omega)
    exact ⟨Nat.pos_of_ne_zero fun h ↦ hm.ne <| by rw [← ht.1, h, zero_mul], hg,
      Nat.coprime_div_gcd_div_gcd hg, Nat.div_lt_div_of_lt_of_dvd (Nat.gcd_dvd_right _ _) ht.2⟩
  have hmem (t : ℕ × ℕ × ℕ) (ht : t ∈ cosetReps m) : cosetS t ∈ cosetReps m := by
    rcases hfacts t ht with ⟨ha, hg, hcop, hb₁⟩
    have : NeZero (t.2.2 / t.2.1.gcd t.2.2) := ⟨(Nat.zero_lt_of_lt hb₁).ne'⟩
    rw [mem_cosetReps hm] at ht ⊢
    rw [eq_gcd_mul t, cosetS_mul hg hcop]
    dsimp only
    refine ⟨?_, Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) ha⟩
    rw [← ht.1, Nat.mul_left_comm, Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)]
  have hinv (t : ℕ × ℕ × ℕ) (ht : t ∈ cosetReps m) : cosetS (cosetS t) = t := by
    rcases hfacts t ht with ⟨ha, hg, hcop, hb₁⟩
    rw [eq_gcd_mul t, cosetS_cosetS ha hg hcop hb₁]
  rw [indexRaising, indexRaising, mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_nbij' cosetS cosetS hmem hmem hinv hinv fun t ht ↦ ?_
  rcases hfacts t ht with ⟨ha, hg, hcop, hb₁⟩
  have hm' : t.1 * (t.2.1.gcd t.2.2 * (t.2.2 / t.2.1.gcd t.2.2)) = m := by
    rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)]
    exact ((mem_cosetReps hm).mp ht).1
  rw [hJ, eq_gcd_mul t, cosetTerm_S x hφ ha hg hcop hb₁, hm']

end ModularForm
