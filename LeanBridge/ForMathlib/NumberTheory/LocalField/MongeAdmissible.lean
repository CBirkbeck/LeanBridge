import LeanBridge.ForMathlib.NumberTheory.LocalField.MongePolygon

/-!
# The lines of the ramification polygon of a Herbrand invariant, and admissibility

The polygon of a Herbrand invariant `I` is the lower envelope of the lines
`x ↦ e m_k + p ^ (w - k) x` (`IsNonarchimedeanLocalField.HerbrandInvariant.polygonLine`), evaluated
at the rams. In terms of the digits of an Eisenstein polynomial `g` with root `π` whose ramification
polygon is that of `I` (`IsNonarchimedeanLocalField.HerbrandInvariant.IsRamificationPolygon`), this
says where the terms of the coefficient of `T ^ (p ^ (w - k))` in `g(π + T)` lie, by Monge
(arXiv:1109.4617, Lemma 2, p. 4, and p. 8). As a consequence, a Herbrand invariant of an extension
is admissible (`IsNonarchimedeanLocalField.HerbrandInvariant.IsAdmissible`), so its small rams are
at most `e₀ = v_R(p)`, and the vertices of the polygon are of the two kinds of LMFDB
`lf.herbrand_invariant`, arithmetic or geometric. Admissibility is the only part of `I` used when
checking that the specialisations of the generic polynomial have the polygon of `I`.

## Main definitions

* `IsNonarchimedeanLocalField.HerbrandInvariant.polygonLine`: the line of slope `p ^ (w - k)`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsAdmissible`: the conditions on the rams that hold
  for a Herbrand invariant of an extension.

## Main results

* `IsNonarchimedeanLocalField.HerbrandInvariant.mean_le_of_addVal_coeff`: the digits of `g` lie
  above the bottom edges of the bands.
* `IsNonarchimedeanLocalField.HerbrandInvariant.exists_vertex_term`: the term of `g` at a vertex.
* `IsNonarchimedeanLocalField.HerbrandInvariant.smallRam_le` (Monge's Lemma 2): `r_k^* ≤ e₀`.
* `IsNonarchimedeanLocalField.HerbrandInvariant.smallRam_eq_of_den_eq_one`: the arithmetic vertices.
* `IsNonarchimedeanLocalField.HerbrandInvariant.exists_term_of_den_ne_one`: the geometric vertices.
* `IsNonarchimedeanLocalField.HerbrandInvariant.IsAdmissible.of_isRamificationPolygon`: the Herbrand
  invariant of an extension is admissible.
-/

open Finset IsDiscreteValuationRing Polynomial

namespace IsNonarchimedeanLocalField.HerbrandInvariant

variable {p : ℕ} (I : HerbrandInvariant p) (e₀ : ℕ)

/-- The **line** `x ↦ e m_k + p ^ (w - k) x` of the Herbrand function of a Herbrand invariant `I`,
which is `e φ_I(x)` for `r_k ≤ x ≤ r_{k + 1}`, and at least `e φ_I(x)` for all `x ≥ 0`. It is the
line of slope `-r_k` of Monge's ramification polygon (arXiv:1109.4617, p. 3) seen from the dual
side. -/
def polygonLine (k : ℕ) (x : ℚ) : ℚ :=
  I.ramificationIndex * I.mean k + p ^ (I.w - k) * x

/-- A Herbrand invariant `I` is **admissible** for `e₀`, the valuation of `p` in the base field: its
small rams `r_k^*` are at most `e₀`, and at a vertex `1 ≤ k ≤ w`, the small ram is `e₀` if it is an
integer, and otherwise `e m_k` is an integer of index `k`. So the geometric bands `B_k` of the
vertices have an `A`-point at their bottom edge, and the arithmetic ones are `r_k^* = e₀`, as in
LMFDB `lf.herbrand_invariant`. Every Herbrand invariant of an extension is admissible
(`IsAdmissible.of_isRamificationPolygon`). -/
structure IsAdmissible : Prop where
  smallRam_le {k : ℕ} (hk : k < I.w) : I.smallRam (k + 1) ≤ e₀
  smallRam_eq {k : ℕ} (hk : k < I.w) (hv : I.IsVertex (k + 1)) (hd : (I.smallRam (k + 1)).den = 1) :
    I.smallRam (k + 1) = e₀
  exists_pointIndex_eq {k : ℕ} (hk : k < I.w) (hv : I.IsVertex (k + 1))
    (hd : (I.smallRam (k + 1)).den ≠ 1) : ∃ σ : ℕ, (σ : ℚ) = I.ramificationIndex * I.mean (k + 1) ∧
      I.pointIndex (σ % I.ramificationIndex) = k + 1

variable {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing S]
  [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S] {g : R[X]} {π : S} (k : ℕ)
  {k' i j r ℓ : ℕ} {e₀}

lemma ram_nonneg : 0 ≤ I.ram k :=
  I.ram_zero ▸ I.monotone_ram k.zero_le

lemma natCast_ε_pos : (0 : ℚ) < I.ε := by
  exact_mod_cast I.ε_pos

lemma mean_zero : I.mean 0 = 0 := by
  simp [mean]

lemma mean_succ : I.mean (k + 1) = I.mean k + I.smallRam (k + 1) := by
  rw [I.smallRam_eq_mean_sub_mean]
  ring1

lemma exists_natCast_of_den_eq_one {q : ℚ} (hq : 0 ≤ q) (hd : q.den = 1) : ∃ z : ℕ, q = z := by
  lift q to ℤ using hd
  lift q to ℕ using by exact_mod_cast hq
  exact ⟨q, rfl⟩

lemma addVal_natCast_of_coprime (h : IsMongeRoot g π p) {u : ℕ} (hu : p.Coprime u) :
    addVal R (u : R) = 0 := by
  have h₀ : addVal S (algebraMap R S (u : R)) = 0 := by
    rw [map_natCast]
    exact addVal_eq_zero_iff.mpr (h.isUnit_natCast hu)
  rw [h.addVal_algebraMap, nsmul_eq_mul] at h₀
  rcases mul_eq_zero.mp h₀ with h₁ | h₁
  · exact absurd (by exact_mod_cast h₁) h.natDegree_pos.ne'
  · exact h₁

lemma addVal_algebraMap_mul_pow (h : IsMongeRoot g π p) (c : R) :
    addVal S (algebraMap R S c * π ^ i) = g.natDegree • addVal R c + i := by
  rw [addVal_mul, addVal_pow, addVal_uniformizer h.irreducible, nsmul_one, h.addVal_algebraMap]

lemma exists_mem_Icc_addVal_coeff_taylor_add_eq (h : IsMongeRoot g π p) (hr : r ≠ 0) :
    ∃ i ∈ Icc 1 g.natDegree, addVal S ((taylor π (g.map (algebraMap R S))).coeff r) + r =
      addVal S (algebraMap R S ((i.choose r : R) * g.coeff i) * π ^ i) := by
  have hne : Nonempty (Icc 1 g.natDegree) :=
    ⟨⟨1, mem_Icc.mpr ⟨le_rfl, h.natDegree_pos⟩⟩⟩
  have hval : addVal S ((taylor π (g.map (algebraMap R S))).coeff r) + r =
      addVal S (∑ i ∈ Icc 1 g.natDegree,
        algebraMap R S ((i.choose r : R) * g.coeff i) * π ^ i) := by
    rw [← coeff_taylor_mul_pow h hr, addVal_mul, addVal_pow, addVal_uniformizer h.irreducible,
      nsmul_one]
  rw [← sum_coe_sort, addVal_sum_eq_iInf_of_ne] at hval
  · rcases ENat.exists_eq_iInf fun i : Icc 1 g.natDegree ↦ addVal S
      (algebraMap R S ((i.1.choose r : R) * g.coeff i.1) * π ^ i.1) with ⟨i, hi⟩
    exact ⟨i.1, i.2, hval.trans hi.symm⟩
  · intro a b hab ha _ hv
    exact ha (addVal_term_ne h (a := fun i ↦ (i.choose r : R) * g.coeff i)
      (not_modEq_of_mem_Icc a.2 b.2 (Subtype.coe_ne_coe.mpr hab)) hv)

lemma exists_natCast_of_natCast_eq_nsmul_add {n v : ℕ} {x y : ℕ∞} (hn : n ≠ 0)
    (h : (v : ℕ∞) = n • (x + y) + i) : ∃ a b : ℕ, x = a ∧ y = b ∧ v = n * (a + b) + i := by
  have hxy : x + y ≠ ⊤ := fun htop ↦ by
    rw [htop, nsmul_eq_mul, ENat.mul_top (by exact_mod_cast hn), top_add] at h
    exact ENat.natCast_ne_top v h
  rcases ENat.ne_top_iff_exists.mp (fun hx ↦ hxy (by rw [hx, top_add]) : x ≠ ⊤) with ⟨a, rfl⟩
  rcases ENat.ne_top_iff_exists.mp (fun hy ↦ hxy (by rw [hy, add_top]) : y ≠ ⊤) with ⟨b, rfl⟩
  refine ⟨a, b, rfl, rfl, ?_⟩
  rw [nsmul_eq_mul] at h
  exact_mod_cast h

lemma natDegree_le_nsmul_addVal_add (h : IsMongeRoot g π p) (hi : i < g.natDegree) :
    (g.natDegree : ℕ∞) ≤ g.natDegree • addVal R (g.coeff i) + i := by
  have hsum : ∑ i ∈ range g.natDegree, algebraMap R S (g.coeff i) * π ^ i = -π ^ g.natDegree := by
    have h₀ : aeval π g = 0 :=
      h.aeval_eq_zero
    rw [aeval_eq_sum_range, sum_range_succ, h.monic.coeff_natDegree, one_smul] at h₀
    simp only [Algebra.smul_def] at h₀
    exact eq_neg_of_add_eq_zero_left h₀
  have hdvd : π ^ g.natDegree ∣ algebraMap R S (g.coeff i) * π ^ i :=
    pow_dvd_of_pow_dvd_sum h.irreducible _ (fun _ hi _ hj hij heq ↦ addVal_term_ne h
      (fun hc ↦ hij (hc.eq_of_lt_of_lt (mem_range.mp hi) (mem_range.mp hj))) heq)
      (by rw [hsum, dvd_neg]) (mem_range.mpr hi)
  rwa [pow_dvd_iff_le_addVal h.irreducible, addVal_algebraMap_mul_pow h] at hdvd

lemma exists_addVal_coeff_taylor_add_le (h : IsMongeRoot g π p) (hr : r ≠ 0)
    (hi : i ∈ Icc 1 g.natDegree) {b : ℕ} (hb : addVal R (i.choose r : R) = b)
    (hj : addVal R (g.coeff i) = j) : ∃ v : ℕ,
      addVal S ((taylor π (g.map (algebraMap R S))).coeff r) = v ∧
        v + r ≤ g.natDegree * (b + j) + i := by
  have hle : addVal S ((taylor π (g.map (algebraMap R S))).coeff r) + r ≤
      addVal S (algebraMap R S ((i.choose r : R) * g.coeff i) * π ^ i) :=
    addVal_coeff_taylor_add_le h hr hi
  rw [addVal_algebraMap_mul_pow h, addVal_mul, hb, hj, nsmul_eq_mul] at hle
  have hne : addVal S ((taylor π (g.map (algebraMap R S))).coeff r) ≠ ⊤ := fun htop ↦ by
    rw [htop, top_add, top_le_iff] at hle
    exact absurd hle (by exact_mod_cast ENat.natCast_ne_top _)
  rcases ENat.ne_top_iff_exists.mp hne with ⟨v, hv⟩
  refine ⟨v, hv.symm, ?_⟩
  rw [← hv] at hle
  exact_mod_cast hle

variable {k} in
lemma mean_add_sub_le (hs : ∀ {k : ℕ}, k < I.w → I.smallRam (k + 1) ≤ e₀) {d : ℕ}
    (hd : k + d ≤ I.w) : I.mean (k + d) - I.mean k ≤ d * e₀ := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h₁ : I.smallRam (k + d + 1) ≤ e₀ :=
      hs (by omega)
    have h₂ : I.mean (k + d) - I.mean k ≤ d * e₀ :=
      ih (by omega)
    rw [← add_assoc, I.mean_succ]
    push_cast
    linarith

variable [Fact p.Prime]

lemma natCast_prime_pos : (0 : ℚ) < p := by
  exact_mod_cast (Fact.out : p.Prime).pos

lemma one_le_natCast_prime : (1 : ℚ) ≤ p := by
  exact_mod_cast (Fact.out : p.Prime).one_le

lemma smallRam_nonneg : 0 ≤ I.smallRam k := by
  have hp : (1 : ℚ) ≤ p :=
    one_le_natCast_prime
  have hε : (0 : ℚ) < I.ε :=
    I.natCast_ε_pos
  exact div_nonneg (mul_nonneg (by linarith) (I.ram_nonneg k)) (by positivity)

lemma mean_nonneg : 0 ≤ I.mean k := by
  induction k with
  | zero => exact I.mean_zero.ge
  | succ k ih =>
    rw [I.mean_succ]
    exact add_nonneg ih (I.smallRam_nonneg _)

variable {k}

lemma mul_swanSlope_eq (hk : k ≤ I.w) :
    (I.ramificationIndex : ℚ) * I.swanSlope k = I.polygonLine k (I.ram k) := by
  have ht : I.tinyRam k = I.swanSlope k - I.mean k :=
    I.tinyRam_eq_swanSlope_sub_mean (Fact.out : p.Prime).ne_zero k
  rw [tinyRam] at ht
  have hp : (0 : ℚ) < p :=
    natCast_prime_pos
  have hε : (0 : ℚ) < I.ε :=
    I.natCast_ε_pos
  have hpow : (p : ℚ) ^ I.w = p ^ k * p ^ (I.w - k) := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  rw [polygonLine, ramificationIndex]
  push_cast
  rw [eq_sub_iff_add_eq] at ht
  rw [← ht, hpow]
  field_simp
  ring1

lemma mul_smallRam_eq (hk : k < I.w) : (I.ramificationIndex : ℚ) * I.smallRam (k + 1) =
    (p - 1) * p ^ (I.w - (k + 1)) * I.ram (k + 1) := by
  have hp : (0 : ℚ) < p :=
    natCast_prime_pos
  have hε : (0 : ℚ) < I.ε :=
    I.natCast_ε_pos
  have hpow₁ : (p : ℚ) ^ I.w = p ^ (k + 1) * p ^ (I.w - (k + 1)) := by
    rw [← pow_add, Nat.add_sub_of_le hk]
  rw [smallRam, ramificationIndex]
  push_cast
  rw [hpow₁]
  field_simp

lemma polygonLine_succ_sub (hk : k < I.w) (x : ℚ) : I.polygonLine (k + 1) x - I.polygonLine k x =
    (p - 1) * p ^ (I.w - (k + 1)) * (I.ram (k + 1) - x) := by
  have hpow₂ : (p : ℚ) ^ (I.w - k) = p ^ (I.w - (k + 1)) * p := by
    rw [← pow_succ]
    congr 1
    omega
  rw [polygonLine, polygonLine, I.mean_succ, hpow₂, mul_add, I.mul_smallRam_eq hk]
  ring1

lemma polygonLine_succ_ram (hk : k < I.w) :
    I.polygonLine (k + 1) (I.ram (k + 1)) = I.polygonLine k (I.ram (k + 1)) :=
  sub_eq_zero.mp <| by rw [I.polygonLine_succ_sub hk, sub_self, mul_zero]

lemma polygonLine_le_of_le_of_le {x : ℚ} (hk : k ≤ I.w) (hk' : k' ≤ I.w) (hx₁ : I.ram k ≤ x)
    (hx₂ : k < I.w → x ≤ I.ram (k + 1)) : I.polygonLine k x ≤ I.polygonLine k' x := by
  have hp : (1 : ℚ) ≤ p :=
    one_le_natCast_prime
  rcases le_total k k' with h | h
  · induction k', h using Nat.le_induction with
    | base => exact le_rfl
    | succ j hj ih =>
      have hj' : j < I.w :=
        hk'
      refine (ih hj'.le).trans (sub_nonneg.mp ?_)
      rw [I.polygonLine_succ_sub hj']
      refine mul_nonneg (mul_nonneg (by linarith) (by positivity)) (sub_nonneg.mpr ?_)
      exact (hx₂ (lt_of_le_of_lt hj hj')).trans (I.monotone_ram (by omega))
  · refine Nat.decreasingInduction (fun j hj ih ↦ ih.trans (sub_nonpos.mp ?_)) le_rfl h
    have hj' : j < I.w :=
      hj.trans_le hk
    rw [I.polygonLine_succ_sub hj']
    exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by linarith) (by positivity))
      (sub_nonpos.mpr ((I.monotone_ram (Nat.succ_le_of_lt hj)).trans hx₁))

lemma natCast_ramificationIndex_pos : (0 : ℚ) < I.ramificationIndex :=
  Nat.cast_pos.mpr ramificationIndex_pos

lemma smallRam_eq_mul_of_ram_eq (hr : I.ram (k + 1) = I.ram k) :
    I.smallRam k = p * I.smallRam (k + 1) := by
  have hp : (0 : ℚ) < p :=
    natCast_prime_pos
  have hε : (0 : ℚ) < I.ε :=
    I.natCast_ε_pos
  rw [smallRam, smallRam, hr, pow_succ]
  field_simp

lemma smallRam_succ_le_of_ram_eq (hr : I.ram (k + 1) = I.ram k) :
    I.smallRam (k + 1) ≤ I.smallRam k := by
  have hp : (1 : ℚ) ≤ p :=
    one_le_natCast_prime
  rw [I.smallRam_eq_mul_of_ram_eq hr]
  nlinarith [I.smallRam_nonneg (k + 1)]

lemma polygonLine_le (hk : k ≤ I.w) (hk' : k' ≤ I.w) :
    (I.ramificationIndex : ℚ) * I.swanSlope k ≤ I.polygonLine k' (I.ram k) := by
  rw [I.mul_swanSlope_eq hk]
  exact I.polygonLine_le_of_le_of_le hk hk' le_rfl fun _ ↦ I.monotone_ram k.le_succ

lemma padicValNat_le_padicValNat_choose_add (hri : r ≤ i) (hr : r ≠ 0) :
    padicValNat p i ≤ padicValNat p (i.choose r) + padicValNat p r := by
  have hi : i ≠ 0 := by
    omega
  have h : emultiplicity p i ≤ emultiplicity p (i.choose r) + emultiplicity p r :=
    (Fact.out : p.Prime).emultiplicity_le_emultiplicity_choose_add i r
  rw [← padicValNat_eq_emultiplicity hi, ← padicValNat_eq_emultiplicity hr,
    ← padicValNat_eq_emultiplicity (Nat.choose_ne_zero hri)] at h
  exact_mod_cast h

lemma padicValNat_choose_pow (hi : i ≠ 0) (hℓ : ℓ ≤ padicValNat p i) :
    padicValNat p (i.choose (p ^ ℓ)) = padicValNat p i - ℓ := by
  have hp : p.Prime :=
    Fact.out
  have hle : p ^ ℓ ≤ p ^ padicValNat p i :=
    Nat.pow_le_pow_right hp.pos hℓ
  have hle' : p ^ padicValNat p i ≤ i :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hi) pow_padicValNat_dvd
  have hlower : padicValNat p i ≤ padicValNat p (i.choose (p ^ ℓ)) + padicValNat p (p ^ ℓ) :=
    padicValNat_le_padicValNat_choose_add (hle.trans hle') (pow_ne_zero ℓ hp.ne_zero)
  rw [padicValNat.prime_pow] at hlower
  have h₁ : padicValNat p (i.choose (p ^ padicValNat p i)) = 0 := by
    have h₂ : p.Coprime ((p ^ padicValNat p i * i.divMaxPow p).choose (p ^ padicValNat p i)) :=
      coprime_choose_pow_mul _ (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_divMaxPow hp.one_lt hi))
    rw [Nat.pow_padicValNat_mul_divMaxPow] at h₂
    exact padicValNat.eq_zero_of_not_dvd (hp.coprime_iff_not_dvd.mp h₂)
  have h₃ : padicValNat p ((p ^ padicValNat p i).choose (p ^ ℓ)) = padicValNat p i - ℓ := by
    have h₂ : emultiplicity p ((p ^ padicValNat p i).choose (p ^ ℓ)) + emultiplicity p (p ^ ℓ) =
        (padicValNat p i : ℕ∞) :=
      hp.emultiplicity_choose_prime_pow_add_emultiplicity hle (pow_ne_zero ℓ hp.ne_zero)
    rw [← padicValNat_eq_emultiplicity (Nat.choose_ne_zero hle),
      ← padicValNat_eq_emultiplicity (pow_ne_zero ℓ hp.ne_zero), padicValNat.prime_pow] at h₂
    have h₄ : padicValNat p ((p ^ padicValNat p i).choose (p ^ ℓ)) + ℓ = padicValNat p i := by
      exact_mod_cast h₂
    omega
  have h₄ : padicValNat p (i.choose (p ^ padicValNat p i) * (p ^ padicValNat p i).choose (p ^ ℓ)) =
      padicValNat p (i.choose (p ^ ℓ) * (i - p ^ ℓ).choose (p ^ padicValNat p i - p ^ ℓ)) :=
    congrArg (padicValNat p) (Nat.choose_mul hle)
  have hchoose : (i - p ^ ℓ).choose (p ^ padicValNat p i - p ^ ℓ) ≠ 0 :=
    Nat.choose_ne_zero (by omega)
  rw [padicValNat.mul (Nat.choose_ne_zero hle') (Nat.choose_ne_zero hle),
    padicValNat.mul (Nat.choose_ne_zero (hle.trans hle')) hchoose, h₁, h₃] at h₄
  omega

lemma addVal_natCast_eq (h : IsMongeRoot g π p) (he₀ : addVal R (p : R) = e₀) {m : ℕ} (hm : m ≠ 0) :
    addVal R (m : R) = ((padicValNat p m * e₀ : ℕ) : ℕ∞) := by
  have hp : p.Prime :=
    Fact.out
  have hcop : p.Coprime (m.divMaxPow p) :=
    hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_divMaxPow hp.one_lt hm)
  conv_lhs => rw [← Nat.pow_padicValNat_mul_divMaxPow p m]
  rw [Nat.cast_mul, Nat.cast_pow, addVal_mul, addVal_pow, he₀, addVal_natCast_of_coprime h hcop,
    add_zero]
  simp

lemma exists_addVal_natCast_choose_pow (h : IsMongeRoot g π p) (he₀ : addVal R (p : R) = e₀)
    (hi : i ∈ Icc 1 g.natDegree) (hj : addVal R (g.coeff i) = j) (hℓ : ℓ ≤ padicValNat p i) :
    ∃ v : ℕ, addVal S ((taylor π (g.map (algebraMap R S))).coeff (p ^ ℓ)) = v ∧
      v + p ^ ℓ ≤ g.natDegree * ((padicValNat p i - ℓ) * e₀ + j) + i := by
  have hp : p.Prime :=
    Fact.out
  have hi₀ : i ≠ 0 :=
    (Nat.lt_of_lt_of_le one_pos (mem_Icc.mp hi).1).ne'
  have hle : p ^ ℓ ≤ i :=
    (Nat.pow_le_pow_right hp.pos hℓ).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hi₀)
      pow_padicValNat_dvd)
  refine exists_addVal_coeff_taylor_add_le h (pow_ne_zero ℓ hp.ne_zero) hi ?_ hj
  rw [addVal_natCast_eq h he₀ (Nat.choose_ne_zero hle), padicValNat_choose_pow hi₀ hℓ]

lemma padicValNat_ramificationIndex : padicValNat p I.ramificationIndex = I.w := by
  have hp : p.Prime :=
    Fact.out
  rw [ramificationIndex, padicValNat.mul I.ε_pos.ne' (pow_ne_zero _ hp.ne_zero),
    padicValNat.eq_zero_of_not_dvd I.not_dvd_ε, zero_add, padicValNat.prime_pow]

lemma pointIndex_zero : I.pointIndex 0 = 0 := by
  rw [pointIndex, Nat.gcd_zero_left, padicValNat.prime_pow, Nat.sub_self]

lemma padicValNat_gcd_pow {w : ℕ} (hi : i ≠ 0) :
    padicValNat p (i.gcd (p ^ w)) = min (padicValNat p i) w := by
  have hp : p.Prime :=
    Fact.out
  rw [← Nat.factorization_def _ hp, Nat.factorization_gcd hi (pow_ne_zero _ hp.ne_zero),
    Finsupp.inf_apply, hp.factorization_pow, Finsupp.single_eq_same, Nat.factorization_def _ hp]

variable {I}

/-- **The digits of `g` lie above the bottom edges of the bands** (Monge, arXiv:1109.4617, p. 8):
if the ramification polygon of `g` at `π` is that of `I`, `1 ≤ i ≤ e` and `v_p(i) ≤ w`, then
`e (m_k + 1) ≤ e v_R(g_i) + i` for `k = w - v_p(i)`. -/
lemma mean_le_of_addVal_coeff (he₀ : addVal R (p : R) = e₀) (h : IsMongeRoot g π p)
    (hP : I.IsRamificationPolygon g π) (hi : i ∈ Icc 1 g.natDegree) (hj : addVal R (g.coeff i) = j)
    (ha : padicValNat p i ≤ I.w) :
    (I.ramificationIndex : ℚ) * (I.mean (I.w - padicValNat p i) + 1) ≤
      (g.natDegree * j + i : ℕ) := by
  have hp : p.Prime :=
    Fact.out
  rcases exists_addVal_natCast_choose_pow h he₀ hi hj le_rfl with ⟨v, hv, hvle⟩
  have hLB : (I.ramificationIndex : ℚ) * (I.swanSlope (I.w - padicValNat p i) + 1) ≤
      v + (p ^ padicValNat p i : ℕ) +
        (p ^ padicValNat p i : ℕ) * I.ram (I.w - padicValNat p i) :=
    hP.le_addVal (Nat.sub_le I.w (padicValNat p i)) (pow_ne_zero _ hp.ne_zero) hv
  have hline : (I.ramificationIndex : ℚ) * I.swanSlope (I.w - padicValNat p i) =
      I.ramificationIndex * I.mean (I.w - padicValNat p i) +
        p ^ padicValNat p i * I.ram (I.w - padicValNat p i) := by
    rw [I.mul_swanSlope_eq (Nat.sub_le I.w (padicValNat p i)), polygonLine, Nat.sub_sub_self ha]
  have hvle' : (v : ℚ) + (p ^ padicValNat p i : ℕ) ≤ (g.natDegree * j + i : ℕ) := by
    have h₁ : v + p ^ padicValNat p i ≤ g.natDegree * j + i := by
      simpa using hvle
    exact_mod_cast h₁
  rw [mul_add, hline] at hLB
  rw [mul_add]
  push_cast at hLB hvle' ⊢
  linarith

/-- **The term of `g` at a vertex of the ramification polygon** (Monge, arXiv:1109.4617, p. 5 and
p. 8): if the ramification polygon of `g` at `π` is that of `I`, then for a vertex `k`, the minimum
of the valuations of the terms of the coefficient of `T ^ (p ^ (w - k))` in `g(π + T)` is attained
at an `i` with `p ^ (w - k) ∣ i`, and `e v_R(g_i) + e (v_p(i) - (w - k)) e₀ + i = e (m_k + 1)`, for
`e₀ = v_R(p)`. -/
lemma exists_vertex_term (he₀ : addVal R (p : R) = e₀) (h : IsMongeRoot g π p)
    (hP : I.IsRamificationPolygon g π) (hk : k ≤ I.w) (hfin : I.IsVertex k) :
    ∃ i ∈ Icc 1 g.natDegree, ∃ j : ℕ, addVal R (g.coeff i) = j ∧ I.w - k ≤ padicValNat p i ∧
      ((g.natDegree * ((padicValNat p i - (I.w - k)) * e₀ + j) + i : ℕ) : ℚ) =
        I.ramificationIndex * (I.mean k + 1) := by
  have hp : p.Prime :=
    Fact.out
  rcases Nat.eq_zero_or_pos k with rfl | hk₀
  · refine ⟨g.natDegree, mem_Icc.mpr ⟨h.natDegree_pos, le_rfl⟩, 0, ?_, ?_, ?_⟩
    · rw [h.monic.coeff_natDegree]
      simp
    · rw [hP.natDegree_eq, padicValNat_ramificationIndex]
      omega
    · rw [hP.natDegree_eq, padicValNat_ramificationIndex, Nat.sub_zero, Nat.sub_self, I.mean_zero]
      simp
  have hrk : 0 < I.ram k :=
    (I.zero_lt_ram_one (by omega)).trans_le (I.monotone_ram hk₀)
  rcases hP.exists_addVal_eq hk hfin with ⟨v, hv, hvq⟩
  rcases exists_mem_Icc_addVal_coeff_taylor_add_eq h (pow_ne_zero (I.w - k) hp.ne_zero) with
    ⟨i, hi, hti⟩
  rw [hv, addVal_algebraMap_mul_pow h, addVal_mul, ← Nat.cast_add] at hti
  rcases exists_natCast_of_natCast_eq_nsmul_add h.natDegree_pos.ne' hti with ⟨b, j, hb, hj, hvj⟩
  have hi₀ : i ≠ 0 :=
    (Nat.lt_of_lt_of_le one_pos (mem_Icc.mp hi).1).ne'
  have hvj' : (v : ℚ) + p ^ (I.w - k) = (g.natDegree * (b + j) + i : ℕ) := by
    exact_mod_cast hvj
  have hple : I.w - k ≤ padicValNat p i := by
    by_contra hlt
    rw [not_le] at hlt
    rcases exists_addVal_natCast_choose_pow h he₀ hi hj le_rfl with ⟨v', hv', hvle⟩
    have hLB : (I.ramificationIndex : ℚ) * (I.swanSlope k + 1) ≤
        v' + (p ^ padicValNat p i : ℕ) + (p ^ padicValNat p i : ℕ) * I.ram k :=
      hP.le_addVal hk (pow_ne_zero (padicValNat p i) hp.ne_zero) hv'
    have hline : (I.ramificationIndex : ℚ) * I.swanSlope k =
        I.ramificationIndex * I.mean k + p ^ (I.w - k) * I.ram k :=
      I.mul_swanSlope_eq hk
    have hvle' : (v' : ℚ) + (p ^ padicValNat p i : ℕ) ≤ (g.natDegree * j + i : ℕ) := by
      have h₁ : v' + p ^ padicValNat p i ≤ g.natDegree * j + i := by
        simpa using hvle
      exact_mod_cast h₁
    have hpow : ((p ^ padicValNat p i : ℕ) : ℚ) < p ^ (I.w - k) := by
      exact_mod_cast Nat.pow_lt_pow_right hp.one_lt hlt
    have hb' : (0 : ℚ) ≤ (g.natDegree * b : ℕ) :=
      Nat.cast_nonneg _
    have hmul : ((p ^ padicValNat p i : ℕ) : ℚ) * I.ram k < p ^ (I.w - k) * I.ram k :=
      mul_lt_mul_of_pos_right hpow hrk
    rw [mul_add, hline] at hLB
    rw [mul_add] at hvq
    push_cast at hLB hvle' hvj' hb' hmul
    nlinarith
  have hle : p ^ (I.w - k) ≤ i :=
    (Nat.pow_le_pow_right hp.pos hple).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hi₀)
      pow_padicValNat_dvd)
  rw [addVal_natCast_eq h he₀ (Nat.choose_ne_zero hle), padicValNat_choose_pow hi₀ hple] at hb
  have hb' : (padicValNat p i - (I.w - k)) * e₀ = b := by
    exact_mod_cast hb
  refine ⟨i, hi, j, hj, hple, ?_⟩
  rw [hb', ← hvj', hvq]

lemma smallRam_le_of_isVertex (he₀ : addVal R (p : R) = e₀) (h : IsMongeRoot g π p)
    (hP : I.IsRamificationPolygon g π) (hk : k < I.w) (hv : I.IsVertex k) :
    I.smallRam (k + 1) ≤ e₀ := by
  have hp : p.Prime :=
    Fact.out
  have he : (0 : ℚ) < I.ramificationIndex :=
    I.natCast_ramificationIndex_pos
  rcases exists_vertex_term he₀ h hP hk.le hv with ⟨i, hi, j, hj, hple, hform⟩
  rcases exists_addVal_natCast_choose_pow h he₀ hi hj (ℓ := I.w - (k + 1)) (by omega) with
    ⟨v, hv', hvle⟩
  have hLB : (I.ramificationIndex : ℚ) * (I.swanSlope (k + 1) + 1) ≤
      v + (p ^ (I.w - (k + 1)) : ℕ) + (p ^ (I.w - (k + 1)) : ℕ) * I.ram (k + 1) :=
    hP.le_addVal (by omega) (pow_ne_zero (I.w - (k + 1)) hp.ne_zero) hv'
  have hline : (I.ramificationIndex : ℚ) * I.swanSlope (k + 1) =
      I.ramificationIndex * I.mean (k + 1) + p ^ (I.w - (k + 1)) * I.ram (k + 1) :=
    I.mul_swanSlope_eq (by omega)
  have hsub : padicValNat p i - (I.w - (k + 1)) = padicValNat p i - (I.w - k) + 1 := by
    omega
  rw [hsub] at hvle
  have hvle' : ((v + p ^ (I.w - (k + 1)) : ℕ) : ℚ) ≤
      ((g.natDegree * ((padicValNat p i - (I.w - k) + 1) * e₀ + j) + i : ℕ) : ℚ) := by
    exact_mod_cast hvle
  rw [hP.natDegree_eq] at hvle' hform
  rw [I.mean_succ] at hline
  rw [mul_add, hline] at hLB
  refine le_of_mul_le_mul_left ?_ he
  push_cast at hvle' hform hLB
  nlinarith

/-- **Monge's Lemma 2** (Monge, arXiv:1109.4617, p. 4): if the ramification polygon of `g` at `π` is
that of `I`, then the small rams satisfy `r_k^* = m_k - m_{k - 1} ≤ e₀` for `1 ≤ k ≤ w`, where
`e₀ = v_R(p)`. -/
lemma smallRam_le (he₀ : addVal R (p : R) = e₀) (h : IsMongeRoot g π p)
    (hP : I.IsRamificationPolygon g π) (hk : k < I.w) : I.smallRam (k + 1) ≤ e₀ := by
  induction k with
  | zero =>
    refine smallRam_le_of_isVertex he₀ h hP hk (.inr ?_)
    rw [I.ram_zero]
    exact I.zero_lt_ram_one hk
  | succ k ih =>
    by_cases hv : I.IsVertex (k + 1)
    · exact smallRam_le_of_isVertex he₀ h hP hk hv
    · have hr : I.ram (k + 1 + 1) = I.ram (k + 1) := by
        rw [IsVertex, not_or, not_lt] at hv
        exact le_antisymm hv.2 (I.monotone_ram (Nat.le_succ _))
      exact (I.smallRam_succ_le_of_ram_eq hr).trans (ih (by omega))

lemma exists_natCast_eq_mul_mean (he₀ : addVal R (p : R) = e₀) (h : IsMongeRoot g π p)
    (hP : I.IsRamificationPolygon g π) (hk : k ≤ I.w) (hv : I.IsVertex k) :
    ∃ σ : ℕ, (σ : ℚ) = I.ramificationIndex * I.mean k ∧ p ^ (I.w - k) ∣ σ := by
  rcases exists_vertex_term he₀ h hP hk hv with ⟨i, hi, j, -, hple, hform⟩
  have hn : p ^ (I.w - k) ∣ g.natDegree := by
    rw [hP.natDegree_eq, ramificationIndex]
    exact (pow_dvd_pow p (Nat.sub_le _ _)).mul_left _
  have hi' : p ^ (I.w - k) ∣ i :=
    (pow_dvd_pow p hple).trans pow_padicValNat_dvd
  have hge : g.natDegree ≤ g.natDegree * ((padicValNat p i - (I.w - k)) * e₀ + j) + i := by
    have h₁ : ((g.natDegree : ℕ) : ℚ) ≤
        ((g.natDegree * ((padicValNat p i - (I.w - k)) * e₀ + j) + i : ℕ) : ℚ) := by
      rw [hform, hP.natDegree_eq, mul_add, mul_one]
      nlinarith [I.mean_nonneg k, I.natCast_ramificationIndex_pos]
    exact_mod_cast h₁
  refine ⟨g.natDegree * ((padicValNat p i - (I.w - k)) * e₀ + j) + i - g.natDegree, ?_,
    Nat.dvd_sub ((Nat.dvd_add_right (hn.mul_right _)).mpr hi') hn⟩
  rw [Nat.cast_sub hge, hform, hP.natDegree_eq]
  ring1

lemma exists_natCast_eq_mul_mean_of_den_eq_one (he₀ : addVal R (p : R) = e₀) (h : IsMongeRoot g π p)
    (hP : I.IsRamificationPolygon g π) (hk : k < I.w) (hd : (I.smallRam (k + 1)).den = 1) :
    ∃ σ : ℕ, (σ : ℚ) = I.ramificationIndex * I.mean k ∧ p ^ (I.w - k) ∣ σ := by
  induction k with
  | zero => exact exists_natCast_eq_mul_mean he₀ h hP hk.le (.inr <| by
      rw [I.ram_zero]
      exact I.zero_lt_ram_one hk)
  | succ k ih =>
    by_cases hv : I.IsVertex (k + 1)
    · exact exists_natCast_eq_mul_mean he₀ h hP hk.le hv
    · have hr : I.ram (k + 1 + 1) = I.ram (k + 1) := by
        rw [IsVertex, not_or, not_lt] at hv
        exact le_antisymm hv.2 (I.monotone_ram (Nat.le_succ _))
      rcases exists_natCast_of_den_eq_one (I.smallRam_nonneg _) hd with ⟨z, hz⟩
      have hsm : I.smallRam (k + 1) = ((p * z : ℕ) : ℚ) := by
        rw [Nat.cast_mul, ← hz]
        exact I.smallRam_eq_mul_of_ram_eq hr
      rcases ih (by omega) (by rw [hsm]; exact Rat.den_natCast _) with ⟨σ, hσ, hdvd⟩
      refine ⟨σ + I.ramificationIndex * (p * z), ?_, ?_⟩
      · rw [I.mean_succ, hsm, mul_add, ← hσ]
        push_cast
        ring1
      · refine dvd_add ((pow_dvd_pow p (by omega)).trans hdvd) (Dvd.dvd.mul_right ?_ _)
        rw [ramificationIndex]
        exact (pow_dvd_pow p (Nat.sub_le _ _)).mul_left _

lemma smallRam_ne_den_of_padicValNat_eq (he₀ : addVal R (p : R) = e₀) (h : IsMongeRoot g π p)
    (hP : I.IsRamificationPolygon g π) (hk : k < I.w) (hi : i ≠ 0)
    (hi' : padicValNat p i = I.w - (k + 1))
    (hform : ((g.natDegree * j + i : ℕ) : ℚ) = I.ramificationIndex * (I.mean (k + 1) + 1)) :
    (I.smallRam (k + 1)).den ≠ 1 := by
  intro hd
  rcases exists_natCast_eq_mul_mean_of_den_eq_one he₀ h hP hk hd with ⟨σ, hσ, hdvd⟩
  rcases exists_natCast_of_den_eq_one (I.smallRam_nonneg _) hd with ⟨z, hz⟩
  have heq : g.natDegree * j + i = σ + g.natDegree * z + g.natDegree := by
    have h₁ : ((g.natDegree * j + i : ℕ) : ℚ) = ((σ + g.natDegree * z + g.natDegree : ℕ) : ℚ) := by
      rw [hform, I.mean_succ, hz, hP.natDegree_eq]
      push_cast
      rw [hσ]
      ring1
    exact_mod_cast h₁
  have hn : p ^ (I.w - k) ∣ g.natDegree := by
    rw [hP.natDegree_eq, ramificationIndex]
    exact (pow_dvd_pow p (Nat.sub_le _ _)).mul_left _
  have hdvd' : p ^ (I.w - k) ∣ i := by
    refine (Nat.dvd_add_right (hn.mul_right j)).mp ?_
    rw [heq]
    exact dvd_add (dvd_add hdvd (hn.mul_right z)) hn
  have hpow : I.w - k = padicValNat p i + 1 := by
    omega
  rw [hpow] at hdvd'
  exact pow_succ_padicValNat_not_dvd hi hdvd'

lemma smallRam_eq_of_lt_padicValNat (he₀ : addVal R (p : R) = e₀) (h : IsMongeRoot g π p)
    (hP : I.IsRamificationPolygon g π) (hk : k < I.w) (hi : i ∈ Icc 1 g.natDegree)
    (hj : addVal R (g.coeff i) = j) (hi' : I.w - (k + 1) < padicValNat p i)
    (hform : ((g.natDegree * ((padicValNat p i - (I.w - (k + 1))) * e₀ + j) + i : ℕ) : ℚ) =
      I.ramificationIndex * (I.mean (k + 1) + 1)) : I.smallRam (k + 1) = e₀ := by
  have he : (0 : ℚ) < I.ramificationIndex :=
    I.natCast_ramificationIndex_pos
  refine le_antisymm (smallRam_le he₀ h hP hk) ?_
  have hn : g.natDegree = I.ramificationIndex :=
    hP.natDegree_eq
  have hex : ∃ k' d, k = k' + d ∧ I.w - k' ≤ padicValNat p i ∧
      (I.ramificationIndex : ℚ) * (I.mean k' + 1) ≤ (g.natDegree * j + i : ℕ) := by
    rcases le_total (padicValNat p i) I.w with ha | ha
    · refine ⟨I.w - padicValNat p i, k - (I.w - padicValNat p i), by omega, by omega,
        mean_le_of_addVal_coeff he₀ h hP hi hj ha⟩
    · refine ⟨0, k, by omega, by omega, ?_⟩
      have hle : (g.natDegree : ℕ∞) ≤ g.natDegree • addVal R (g.coeff i) + i := by
        rcases (mem_Icc.mp hi).2.lt_or_eq with hlt | rfl
        · exact natDegree_le_nsmul_addVal_add h hlt
        · exact le_add_self
      rw [hj, nsmul_eq_mul] at hle
      have hle' : g.natDegree ≤ g.natDegree * j + i := by
        exact_mod_cast hle
      rw [hn] at hle'
      rw [hn, I.mean_zero, zero_add, mul_one]
      exact_mod_cast hle'
  rcases hex with ⟨k', d, rfl, hk', hlow⟩
  have hsum : I.mean (k' + d) - I.mean k' ≤ d * e₀ :=
    I.mean_add_sub_le (fun hk ↦ smallRam_le he₀ h hP hk) (by omega)
  have hsmall : I.mean (k' + d + 1) = I.mean (k' + d) + I.smallRam (k' + d + 1) :=
    I.mean_succ _
  have hgap : ((d + 1 : ℕ) : ℚ) ≤ ((padicValNat p i - (I.w - (k' + d + 1)) : ℕ) : ℚ) := by
    exact_mod_cast (by omega : d + 1 ≤ padicValNat p i - (I.w - (k' + d + 1)))
  have hmul : ((d + 1 : ℕ) : ℚ) * e₀ ≤ ((padicValNat p i - (I.w - (k' + d + 1)) : ℕ) : ℚ) * e₀ :=
    mul_le_mul_of_nonneg_right hgap (Nat.cast_nonneg _)
  refine le_of_mul_le_mul_left ?_ he
  rw [hn] at hform hlow
  push_cast at hform hlow hmul ⊢
  nlinarith

/-- **The vertices at arithmetic bands**: if the ramification polygon of `g` at `π` is that of `I`,
`1 ≤ k ≤ w` is a vertex and the small ram `r_k^*` is an integer, then `r_k^* = e₀`, where
`e₀ = v_R(p)`. -/
lemma smallRam_eq_of_den_eq_one (he₀ : addVal R (p : R) = e₀) (h : IsMongeRoot g π p)
    (hP : I.IsRamificationPolygon g π) (hk : k < I.w) (hv : I.IsVertex (k + 1))
    (hd : (I.smallRam (k + 1)).den = 1) : I.smallRam (k + 1) = e₀ := by
  rcases exists_vertex_term he₀ h hP hk hv with ⟨i, hi, j, hj, hple, hform⟩
  rcases hple.lt_or_eq with hlt | heq
  · exact smallRam_eq_of_lt_padicValNat he₀ h hP hk hi hj hlt hform
  · have hi₀ : i ≠ 0 :=
      (Nat.lt_of_lt_of_le one_pos (mem_Icc.mp hi).1).ne'
    rw [← heq, Nat.sub_self, zero_mul, zero_add] at hform
    exact absurd hd (smallRam_ne_den_of_padicValNat_eq he₀ h hP hk hi₀ heq.symm hform)

/-- **The vertices at geometric bands**: if the ramification polygon of `g` at `π` is that of `I`,
`1 ≤ k ≤ w` is a vertex and the small ram `r_k^*` is not an integer, then
`e v_R(g_i) + i = e (m_k + 1)` for an `i` with `v_p(i) = w - k`. -/
lemma exists_term_of_den_ne_one (he₀ : addVal R (p : R) = e₀) (h : IsMongeRoot g π p)
    (hP : I.IsRamificationPolygon g π) (hk : k < I.w) (hv : I.IsVertex (k + 1))
    (hd : (I.smallRam (k + 1)).den ≠ 1) : ∃ i ∈ Icc 1 g.natDegree, ∃ j : ℕ,
      addVal R (g.coeff i) = j ∧ padicValNat p i = I.w - (k + 1) ∧
        ((g.natDegree * j + i : ℕ) : ℚ) = I.ramificationIndex * (I.mean (k + 1) + 1) := by
  rcases exists_vertex_term he₀ h hP hk hv with ⟨i, hi, j, hj, hple, hform⟩
  rcases hple.lt_or_eq with hlt | heq
  · rw [smallRam_eq_of_lt_padicValNat he₀ h hP hk hi hj hlt hform] at hd
    exact absurd (Rat.den_natCast e₀) hd
  · rw [← heq, Nat.sub_self, zero_mul, zero_add] at hform
    exact ⟨i, hi, j, hj, heq.symm, hform⟩

/-- **The Herbrand invariant of an extension is admissible**: if the ramification polygon of `g` at
`π` is that of `I`, then `I` is admissible for `v_R(p)`. -/
lemma IsAdmissible.of_isRamificationPolygon (he₀ : addVal R (p : R) = e₀) (h : IsMongeRoot g π p)
    (hP : I.IsRamificationPolygon g π) : I.IsAdmissible e₀ where
  smallRam_le hk := HerbrandInvariant.smallRam_le he₀ h hP hk
  smallRam_eq hk hv hd := smallRam_eq_of_den_eq_one he₀ h hP hk hv hd
  exists_pointIndex_eq {k} hk hv hd := by
    rcases exists_term_of_den_ne_one he₀ h hP hk hv hd with ⟨i, hi, j, hj, hval, hform⟩
    have hn : g.natDegree = I.ramificationIndex :=
      hP.natDegree_eq
    have hi₀ : i ≠ 0 :=
      (Nat.lt_of_lt_of_le one_pos (mem_Icc.mp hi).1).ne'
    have hlt : i < g.natDegree := by
      refine lt_of_le_of_ne (mem_Icc.mp hi).2 fun hin ↦ ?_
      rw [hin, hn, padicValNat_ramificationIndex] at hval
      omega
    have hle : (g.natDegree : ℕ∞) ≤ g.natDegree • addVal R (g.coeff i) + i :=
      natDegree_le_nsmul_addVal_add h hlt
    rw [hj, nsmul_eq_mul] at hle
    have hle' : g.natDegree ≤ g.natDegree * j + i := by
      exact_mod_cast hle
    have hj₁ : 1 ≤ j := by
      by_contra hj₀
      have hj₀' : j = 0 := by
        omega
      rw [hj₀'] at hle'
      omega
    rcases Nat.exists_eq_add_of_le hj₁ with ⟨j', rfl⟩
    refine ⟨g.natDegree * j' + i, ?_, ?_⟩
    · have heq : ((g.natDegree * (1 + j') + i : ℕ) : ℚ) =
          ((g.natDegree * j' + i : ℕ) : ℚ) + g.natDegree := by
        push_cast
        ring1
      rw [heq, hn, mul_add, mul_one] at hform
      rw [hn]
      exact add_right_cancel hform
    · rw [← hn, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt, pointIndex, padicValNat_gcd_pow hi₀, hval,
        min_eq_left (Nat.sub_le _ _)]
      omega

end IsNonarchimedeanLocalField.HerbrandInvariant
