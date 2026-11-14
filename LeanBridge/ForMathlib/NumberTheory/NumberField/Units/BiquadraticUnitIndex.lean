import LeanBridge.ForMathlib.NumberTheory.NumberField.Units.BiquadraticGalois
import TauCeti.Algebra.Squarefree
import TauCeti.NumberTheory.NumberField.Units.Torsion

/-!
# Fundamental units of the quadratic subfields are never all squares

Let `K` be a real biquadratic field with quadratic subfields `k₀, k₁, k₂` and fundamental units
`e₀, e₁, e₂` of them. Their classes `ē₀, ē₁, ē₂` in the units modulo `±1` generate a subgroup that
contains every square, so of index dividing `8`; this file proves that the index is never `8`:
`ē₀, ē₁, ē₂` are not all squares (`QuadraticUnitFrame.not_forall_isSquare_unitClass`). This is the
arithmetic input to the classification of Kubota and of Mazur and Ullom.

The proof follows the classical argument. If `ēᵢ` is a square, some unit `u` of `K` has
`η = u ^ 2 = ±eᵢ`, and then `η` has norm `1` to `ℚ` and `T = η + η⁻¹` is a rational integer with
`T + 2 = ((1 + η) / u) ^ 2` and `T - 2 = ((η - 1) / u) ^ 2`. The two square roots lie in the two
other quadratic subfields `kⱼ` and `kₖ`, one in each (`QuadraticUnitFrame.exists_sq_add_two`). So
`T + 2` and `T - 2` lie in the square classes `dⱼ ℚˣ²` and `dₖ ℚˣ²` of `kⱼ = ℚ(√dⱼ)` and
`kₖ = ℚ(√dₖ)`, and as `gcd(T + 2, T - 2)` divides `4`, no odd prime divides both squarefree parts
`dⱼ` and `dₖ`. If this held for the three pairs of subfields, then, as `d₀ d₁ d₂` is a square, no
odd prime would divide any `dᵢ`, so `d₀ = d₁ = d₂ = 2` (they are positive, as `K` is real, and not
`1`), and `8` would be a square (`MazurUllomType.false_of_forall_exists`).

## Main definitions

* `NumberField.Units.QuadraticUnitFrame.IsKummerGenerator`: an element of the quadratic subfield
  `kⱼ` of a frame, not in `ℚ`, whose square is rational.

## Main results

* `NumberField.Units.QuadraticUnitFrame.not_forall_isSquare_unitClass`: the classes of the
  fundamental units of a frame are not all squares in the units modulo torsion.
* `NumberField.Units.QuadraticUnitFrame.exists_sq_add_two`: a square class among the fundamental
  units gives square roots of `n + 2` and `n - 2` in the two other quadratic subfields.
* `NumberField.Units.MazurUllomType.false_of_forall_exists`: the arithmetic contradiction.

## References

* T. Kubota, *Über den bizyklischen biquadratischen Zahlkörper*, Nagoya Math. J. 10 (1956), 65–85.
* M. Mazur and S. V. Ullom, *Galois module structure of units in real biquadratic number fields*,
  Acta Arith. 111 (2004), 105–124.
-/

open Module IntermediateField TauCeti NumberField

open scoped NumberField

namespace NumberField

namespace Units.MazurUllomType

variable {p : ℕ}

lemma dvd_of_eq_mul_sq {E D : ℤ} {s : ℚ} (h : (E : ℚ) = D * s ^ 2) (hp : p.Prime)
    (hpD : (p : ℤ) ∣ D) (hpD2 : ¬(p : ℤ) ^ 2 ∣ D) : (p : ℤ) ∣ E := by
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have key : E * (s.den : ℤ) ^ 2 = D * s.num ^ 2 := by
    have h1 : (s.num : ℚ) = s * s.den := (Rat.mul_den_eq_num s).symm
    have h2 : (E : ℚ) * (s.den : ℚ) ^ 2 = D * (s.num : ℚ) ^ 2 := by
      rw [h, h1]
      ring1
    exact_mod_cast h2
  by_cases hden : (p : ℤ) ∣ s.den
  · have hnum : ¬(p : ℤ) ∣ s.num := fun hnum ↦ hp.ne_one <| Nat.eq_one_of_dvd_coprimes s.reduced
      (Int.ofNat_dvd_left.mp hnum) (Int.natCast_dvd_natCast.mp hden)
    have hcop : IsCoprime ((p : ℤ) ^ 2) (s.num ^ 2) :=
      ((Prime.coprime_iff_not_dvd hp').mpr hnum).pow
    exact absurd (hcop.dvd_of_dvd_mul_right
      (key ▸ dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hden 2) E)) hpD2
  · rcases hp'.dvd_or_dvd (key ▸ dvd_mul_of_dvd_left hpD _ : (p : ℤ) ∣ E * (s.den : ℤ) ^ 2)
      with h | h
    · exact h
    · exact absurd (hp'.dvd_of_dvd_pow h) hden

lemma not_dvd_of_isSquare_mul {a b c : ℤ} (ha : Squarefree a) (hsq : IsSquare (a * b * c))
    (hp : p.Prime) (hpb : ¬(p : ℤ) ∣ b) (hpc : ¬(p : ℤ) ∣ c) : ¬(p : ℤ) ∣ a := by
  intro hpa
  have hp' : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hsq with ⟨m, hm⟩
  have hpm : (p : ℤ) ∣ m := hp'.dvd_of_dvd_pow (n := 2) <| by
    rw [sq, ← hm]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hpa b) c
  have hp2 : (p : ℤ) * p ∣ a * (b * c) := by
    rw [← mul_assoc, hm]
    exact mul_dvd_mul hpm hpm
  have hbc : IsCoprime (p : ℤ) (b * c) :=
    ((Prime.coprime_iff_not_dvd hp').mpr hpb).mul_right ((Prime.coprime_iff_not_dvd hp').mpr hpc)
  exact hp'.not_isUnit (ha _ ((hbc.mul_left hbc).dvd_of_dvd_mul_right hp2))

lemma eq_two_of_squarefree {d : ℤ} (hd : Squarefree d) (hpos : 0 < d) (hne : d ≠ 1)
    (h2 : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ d → p = 2) : d = 2 := by
  lift d to ℕ using hpos.le
  have hd' : Squarefree d := Int.squarefree_natCast.mp hd
  by_contra hne2
  have h3 : 2 < d := by omega
  rcases Nat.four_dvd_or_exists_odd_prime_and_dvd_of_two_lt h3 with h4 | ⟨p, hp, hpd, hodd⟩
  · exact absurd (hd' 2 (by simpa using h4)) (by decide)
  · rcases hodd with ⟨k, rfl⟩
    have h : 2 * k + 1 = 2 := h2 _ hp (Int.natCast_dvd_natCast.mpr hpd)
    omega

/-- **The arithmetic heart of Kubota's theorem**: there are no positive rationals `x₀, x₁, x₂`,
none a square but with `x₀ x₁ x₂` a square, such that for each `i` some integer `n` has `n + 2`
and `n - 2` in the square classes of `xⱼ` and `xₖ` for the two indices `j, k ≠ i`. -/
lemma false_of_forall_exists {x : Fin 3 → ℚ} (hpos : ∀ j, 0 < x j) (hnsq : ∀ j, ¬IsSquare (x j))
    (hsq : IsSquare (x 0 * x 1 * x 2))
    (hpair : ∀ i : Fin 3, ∃ (n : ℤ) (j k : Fin 3) (q q' : ℚ), j ≠ i ∧ k ≠ i ∧ j ≠ k ∧
      (n + 2 : ℚ) = x j * q ^ 2 ∧ (n - 2 : ℚ) = x k * q' ^ 2) : False := by
  choose d c hd hc hx using fun j ↦ Rat.exists_squarefree_int_mul_sq (hpos j).ne'
  have hdpos (j : Fin 3) : 0 < d j := by
    have h : 0 < (d j : ℚ) * c j ^ 2 := hx j ▸ hpos j
    exact_mod_cast pos_of_mul_pos_left h (sq_nonneg (c j))
  have hdne (j : Fin 3) : d j ≠ 1 := fun h ↦ hnsq j <| by
    rw [hx j, h, Int.cast_one, one_mul]
    exact IsSquare.sq (c j)
  have hdsq : IsSquare (d 0 * d 1 * d 2) := by
    rw [← Rat.isSquare_intCast_iff,
      ← isSquare_mul_sq_iff (mul_ne_zero (mul_ne_zero (hc 0) (hc 1)) (hc 2))]
    convert hsq using 1
    rw [hx 0, hx 1, hx 2]
    push_cast
    ring1
  have hdvd (p : ℕ) (hp : p.Prime) (j : Fin 3) (q : ℚ) (n : ℤ) (h : (n : ℚ) = x j * q ^ 2)
      (hpj : (p : ℤ) ∣ d j) : (p : ℤ) ∣ n := by
    refine dvd_of_eq_mul_sq (D := d j) (s := c j * q) (by rw [h, hx j]; ring1) hp hpj fun h2 ↦ ?_
    exact (Nat.prime_iff_prime_int.mp hp).not_isUnit (hd j _ (by rwa [← sq]))
  have hpairs : ∀ i j k j' k' : Fin 3, i ≠ j → i ≠ k → j ≠ k → j' ≠ i → k' ≠ i → j' ≠ k' →
      (j' = j ∧ k' = k) ∨ (j' = k ∧ k' = j) := by
    decide
  have hcommon (j k : Fin 3) (hjk : j ≠ k) (p : ℕ) (hp : p.Prime) (hpj : (p : ℤ) ∣ d j)
      (hpk : (p : ℤ) ∣ d k) : p = 2 := by
    rcases Fin.exists_ne_and_ne_of_two_lt j k (by decide) with ⟨i, hij, hik⟩
    rcases hpair i with ⟨n, j', k', q, q', hj', hk', hjk', hn, hn'⟩
    have h4 : (p : ℤ) ∣ 4 := by
      have e₁ : ((n + 2 : ℤ) : ℚ) = x j' * q ^ 2 := by
        push_cast
        exact hn
      have e₂ : ((n - 2 : ℤ) : ℚ) = x k' * q' ^ 2 := by
        push_cast
        exact hn'
      rcases hpairs i j k j' k' hij hik hjk hj' hk' hjk' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa using dvd_sub (hdvd p hp _ _ _ e₁ hpj) (hdvd p hp _ _ _ e₂ hpk)
      · simpa using dvd_sub (hdvd p hp _ _ _ e₁ hpk) (hdvd p hp _ _ _ e₂ hpj)
    have h4' : p ∣ 2 ^ 2 := Int.natCast_dvd_natCast.mp h4
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h4')
  have h2 (j : Fin 3) (p : ℕ) (hp : p.Prime) (hpj : (p : ℤ) ∣ d j) : p = 2 := by
    by_contra hp2
    fin_cases j
    · exact not_dvd_of_isSquare_mul (hd 0) hdsq hp
        (fun h ↦ hp2 (hcommon 0 1 (by decide) p hp hpj h))
        (fun h ↦ hp2 (hcommon 0 2 (by decide) p hp hpj h)) hpj
    · exact not_dvd_of_isSquare_mul (hd 1) (b := d 0) (c := d 2) (by rwa [mul_comm (d 1)]) hp
        (fun h ↦ hp2 (hcommon 1 0 (by decide) p hp hpj h))
        (fun h ↦ hp2 (hcommon 1 2 (by decide) p hp hpj h)) hpj
    · have h201 : d 2 * d 0 * d 1 = d 0 * d 1 * d 2 := by ring1
      exact not_dvd_of_isSquare_mul (hd 2) (b := d 0) (c := d 1) (h201 ▸ hdsq) hp
        (fun h ↦ hp2 (hcommon 2 0 (by decide) p hp hpj h))
        (fun h ↦ hp2 (hcommon 2 1 (by decide) p hp hpj h)) hpj
  have hd2 (j : Fin 3) : d j = 2 := eq_two_of_squarefree (hd j) (hdpos j) (hdne j) (h2 j)
  rw [hd2 0, hd2 1, hd2 2] at hdsq
  rcases hdsq with ⟨m, hm⟩
  have h₃ : m < 3 := by nlinarith
  have h₃' : -3 < m := by nlinarith
  interval_cases m <;> omega

end Units.MazurUllomType

variable {K : Type*} [Field K] [NumberField K] {x : K}

variable [IsTotallyReal K] in
lemma ratCast_nonneg_of_sq_eq {q : ℚ} (h : x ^ 2 = q) : 0 ≤ q := by
  let w : InfinitePlace K := (inferInstance : Nonempty (InfinitePlace K)).some
  let φ : K →+* ℝ := InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)
  have hφ : φ x ^ 2 = q := by rw [← map_pow, h, map_ratCast]
  exact_mod_cast hφ ▸ sq_nonneg _

lemma apply_eq_self_of_mem_bot {σ : Gal(K/ℚ)} (hx : x ∈ (⊥ : IntermediateField ℚ K)) : σ x = x := by
  rcases IntermediateField.mem_bot.mp hx with ⟨q, rfl⟩
  exact σ.commutes q

lemma zpow_two_mul_sub_one_eq_one {G : Type*} [Group G] {g : G} {m : ℤ} (h : g = g ^ m * g ^ m) :
    g ^ (2 * m - 1) = 1 := by
  rw [zpow_sub_one, mul_inv_eq_one, mul_comm 2 m, zpow_mul, zpow_two, ← h]

namespace Units.QuadraticUnitFrame

variable [IsGalois ℚ K] [IsKleinFour Gal(K/ℚ)] (f : QuadraticUnitFrame K) {i j k : Fin 3}
  {r r' t : K}

variable (j r) in
/-- An element `r` of `K` is a **Kummer generator** of the `j`-th quadratic subfield `kⱼ` of a
frame: it lies in `kⱼ` but not in `ℚ`, and its square is rational, so that `kⱼ = ℚ(r)` with
`r ^ 2 ∈ ℚ`. -/
def IsKummerGenerator : Prop :=
  f.aut j r = r ∧ r ∉ (⊥ : IntermediateField ℚ K) ∧ r ^ 2 ∈ (⊥ : IntermediateField ℚ K)

variable {f}

lemma IsKummerGenerator.apply_eq_neg (hr : f.IsKummerGenerator j r) (hij : i ≠ j) :
    f.aut i r = -r := by
  have h2 : f.aut i r ^ 2 = r ^ 2 := by rw [← map_pow, apply_eq_self_of_mem_bot hr.2.2]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
  · exact absurd (mem_bot_of_apply_eq_self (f.aut_ne_one i) (f.aut_ne_one j)
      (f.aut_injective.ne hij) h hr.1) hr.2.1
  · exact h

lemma IsKummerGenerator.ne_zero (hr : f.IsKummerGenerator j r) : r ≠ 0 :=
  fun h ↦ hr.2.1 (h ▸ zero_mem _)

lemma IsKummerGenerator.div_mem_bot (hr : f.IsKummerGenerator j r)
    (hr' : f.IsKummerGenerator j r') : r' / r ∈ (⊥ : IntermediateField ℚ K) := by
  have hj : j + 1 ≠ j := by
    fin_cases j <;> decide
  refine mem_bot_of_apply_eq_self (f.aut_ne_one (j + 1)) (f.aut_ne_one j) (f.aut_injective.ne hj)
    ?_ ?_
  · rw [map_div₀, hr.apply_eq_neg hj, hr'.apply_eq_neg hj, neg_div_neg_eq]
  · rw [map_div₀, hr.1, hr'.1]

lemma isKummerGenerator_of_apply_eq_neg (ht : t ≠ 0) (ht2 : t ^ 2 ∈ (⊥ : IntermediateField ℚ K))
    (hi : f.aut i t = -t) (hj : f.aut j t = t) : f.IsKummerGenerator j t := by
  refine ⟨hj, fun hbot ↦ ht ?_, ht2⟩
  have h : t = -t := (apply_eq_self_of_mem_bot hbot).symm.trans hi
  linear_combination h / 2

lemma exists_eq_mul_sq {y z : ℚ} (hr : f.IsKummerGenerator j r) (ht : f.IsKummerGenerator j t)
    (hy : (y : K) = r ^ 2) (hz : t ^ 2 = z) : ∃ q : ℚ, z = y * q ^ 2 := by
  rcases IntermediateField.mem_bot.mp (hr.div_mem_bot ht) with ⟨q, hq⟩
  refine ⟨q, Rat.cast_injective (α := K) ?_⟩
  have htq : t = q * r := by
    rw [← eq_ratCast (algebraMap ℚ K), hq, div_mul_cancel₀ t hr.ne_zero]
  rw [← hz, htq, Rat.cast_mul, Rat.cast_pow, hy]
  ring1

variable (f) [IsTotallyReal K]

variable (j) in
lemma exists_isKummerGenerator : ∃ r : K, f.IsKummerGenerator j r := by
  have hj : j + 1 ≠ j := by
    fin_cases j <;> decide
  let e : (𝓞 K)ˣ := Units.map (algebraMap (𝓞 (f.subfield j).1) (𝓞 K)).toMonoidHom (f.unit j)
  have he : f.aut j (e : K) = e := (f.mem_subfield_iff j).mp (f.coe_map_mem j (f.unit j))
  have hτe : f.aut j (f.aut (j + 1) (e : K)) = f.aut (j + 1) e := by
    rw [apply_comm_of_isKleinFour, he]
  have hne : f.aut (j + 1) (e : K) ≠ e := fun h ↦ f.unitClass_ne_one j <|
    (QuotientGroup.eq_one_iff e).mpr <| Units.mem_torsion_of_mem_bot <|
      mem_bot_of_apply_eq_self (f.aut_ne_one (j + 1)) (f.aut_ne_one j) (f.aut_injective.ne hj) h he
  refine ⟨_, isKummerGenerator_of_apply_eq_neg (sub_ne_zero.mpr hne.symm) ?_
    (by rw [map_sub, apply_apply_of_isKleinFour, neg_sub]) (by rw [map_sub, he, hτe])⟩
  refine mem_bot_of_apply_eq_self (f.aut_ne_one (j + 1)) (f.aut_ne_one j) (f.aut_injective.ne hj)
    ?_ ?_
  · rw [map_pow, map_sub, apply_apply_of_isKleinFour]
    ring1
  · rw [map_pow, map_sub, he, hτe]

/-- **A square class among the fundamental units gives a pair of square roots**: if the class of
the fundamental unit `eᵢ` is a square, there are an integer `n` and square roots `t` of `n + 2` and
`s` of `n - 2`, both negated by `σᵢ` and lying in different quadratic subfields: `σⱼ` negates
`t * s`. Here `u ^ 2 = ±eᵢ` for a unit `u`, `η = u ^ 2` and `n = η + η⁻¹`, `t = (1 + η) / u` and
`s = (η - 1) / u`. -/
lemma exists_sq_add_two (hij : i ≠ j) (h : IsSquare (f.unitClass i)) : ∃ (n : ℤ) (t s : K),
    t ^ 2 = n + 2 ∧ s ^ 2 = n - 2 ∧ t ≠ 0 ∧ s ≠ 0 ∧ f.aut i t = -t ∧ f.aut i s = -s ∧
      f.aut j (t * s) = -(t * s) := by
  rcases h with ⟨x, hx⟩
  induction x using QuotientGroup.induction_on with | H u => ?_
  let e : (𝓞 K)ˣ := Units.map (algebraMap (𝓞 (f.subfield i).1) (𝓞 K)).toMonoidHom (f.unit i)
  have he : f.aut i (e : K) = e := (f.mem_subfield_iff i).mp (f.coe_map_mem i (f.unit i))
  let w : InfinitePlace K := (inferInstance : Nonempty (InfinitePlace K)).some
  have hue : (u : K) ^ 2 = e ∨ (u : K) ^ 2 = -(e : K) := by
    have hmem : e⁻¹ * (u * u) ∈ torsion K :=
      QuotientGroup.eq.mp (hx : ((e : (𝓞 K)ˣ) : (𝓞 K)ˣ ⧸ torsion K) = ((u * u : (𝓞 K)ˣ) : _))
    rcases Units.torsion_eq_one_or_neg_one_of_isReal (IsTotallyReal.isReal w) ⟨_, hmem⟩
      with h | h
    · rw [sq, ← coe_mul, ← inv_mul_eq_one.mp h]
      exact Or.inl rfl
    · rw [sq, ← coe_mul, inv_mul_eq_iff_eq_mul.mp h, coe_mul, coe_neg_one, mul_neg_one]
      exact Or.inr rfl
  have hση : f.aut i ((u : K) ^ 2) = (u : K) ^ 2 := by
    rcases hue with h | h
    · rw [h, he]
    · rw [h, map_neg, he]
  have hσa : f.aut i (u : K) = -(u : K) := by
    have h2 : f.aut i (u : K) ^ 2 = (u : K) ^ 2 := by rw [← map_pow, hση]
    refine (sq_eq_sq_iff_eq_or_eq_neg.mp h2).resolve_left fun hfix ↦ ?_
    have hmem : (u : K) ∈ (f.subfield i).1 := (f.mem_subfield_iff i).mpr hfix
    rcases f.exists_unitClass_zpow_eq i (subfieldUnit _ u hmem) with ⟨m, hm⟩
    rw [map_subfieldUnit] at hm
    rw [hm] at hx
    have h0 : 2 * m - 1 = 0 := f.eq_zero_of_unitClass_zpow_eq_one (zpow_two_mul_sub_one_eq_one hx)
    omega
  have hτσ : f.aut i (f.aut j (u : K)) = -f.aut j (u : K) := by
    rw [apply_comm_of_isKleinFour, hσa, map_neg]
  have hb : ((u : K) * f.aut j (u : K)) ^ 2 = 1 := by
    have hmem : ((u * f.aut j • u : (𝓞 K)ˣ) : K) ∈ (⊥ : IntermediateField ℚ K) := by
      rw [coe_mul, coe_smul_eq_apply]
      refine mem_bot_of_apply_eq_self (f.aut_ne_one i) (f.aut_ne_one j) (f.aut_injective.ne hij)
        ?_ ?_
      · rw [map_mul, hσa, hτσ, neg_mul_neg]
      · rw [map_mul, apply_apply_of_isKleinFour, mul_comm]
    rcases Units.torsion_eq_one_or_neg_one_of_isReal (IsTotallyReal.isReal w)
      ⟨_, Units.mem_torsion_of_mem_bot hmem⟩ with h | h
    · have h₁ : u * f.aut j • u = 1 := h
      have h' : ((u * f.aut j • u : (𝓞 K)ˣ) : K) = 1 := by rw [h₁, coe_one]
      rw [coe_mul, coe_smul_eq_apply] at h'
      rw [h', one_pow]
    · have h₁ : u * f.aut j • u = -1 := h
      have h' : ((u * f.aut j • u : (𝓞 K)ˣ) : K) = -1 := by rw [h₁, coe_neg_one]
      rw [coe_mul, coe_smul_eq_apply] at h'
      rw [h']
      norm_num
  have hτη : f.aut j ((u : K) ^ 2) = ((u : K) ^ 2)⁻¹ := by
    rw [map_pow]
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← mul_pow, hb]
  have hT : ∃ n : ℤ, (n : K) = (u : K) ^ 2 + f.aut j ((u : K) ^ 2) := by
    have hz : (u : K) ^ 2 + f.aut j ((u : K) ^ 2) ∈ (⊥ : IntermediateField ℚ K) := by
      refine mem_bot_of_apply_eq_self (f.aut_ne_one i) (f.aut_ne_one j) (f.aut_injective.ne hij)
        ?_ ?_
      · rw [map_add, hση, apply_comm_of_isKleinFour, hση]
      · rw [map_add, apply_apply_of_isKleinFour, add_comm]
    have hint : IsIntegral ℤ ((u : K) ^ 2 + f.aut j ((u : K) ^ 2)) := by
      have h1 : IsIntegral ℤ (u : K) := (u : 𝓞 K).isIntegral_coe
      exact (h1.pow 2).add ((h1.pow 2).map ((f.aut j).toAlgHom.restrictScalars ℤ))
    rcases IntermediateField.mem_bot.mp hz with ⟨q, hq⟩
    rw [← hq] at hint
    rcases IsIntegrallyClosed.isIntegral_iff.mp (isIntegral_algebraMap_iff.mp hint) with ⟨n, hn⟩
    exact ⟨n, by
      rw [← hq, ← hn]
      simp⟩
  rcases hT with ⟨n, hn⟩
  have hu : (u : K) ≠ 0 := coe_ne_zero u
  refine ⟨n, (1 + (u : K) ^ 2) / u, ((u : K) ^ 2 - 1) / u, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hn, hτη]
    field_simp
    ring1
  · rw [hn, hτη]
    field_simp
    ring1
  · refine div_ne_zero (fun h ↦ ?_) hu
    have h' : (u : K) ^ 2 = ((-1 : ℚ) : K) := by
      push_cast
      linear_combination h
    exact absurd (ratCast_nonneg_of_sq_eq h') (by norm_num)
  · refine div_ne_zero (fun h ↦ ?_) hu
    have h1 : (u : K) ^ 2 = 1 ^ 2 := by linear_combination h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h2 | h2 <;> rw [h2] at hσa <;> norm_num at hσa
  · rw [map_div₀, map_add, map_one, hση, hσa, div_neg]
  · rw [map_div₀, map_sub, map_one, hση, hσa, div_neg]
  · have hts : (1 + (u : K) ^ 2) / u * (((u : K) ^ 2 - 1) / u) =
        (u : K) ^ 2 - f.aut j ((u : K) ^ 2) := by
      rw [hτη]
      field_simp
      ring1
    rw [hts, map_sub, apply_apply_of_isKleinFour]
    ring1

/-- **The classes of the fundamental units of a frame are not all squares** in the units modulo
torsion of a real biquadratic field. As every square is a monomial in them
(`QuadraticUnitFrame.isSquareBasis_unitClass`), this says that the subgroup they generate does not
have index `8` (by Kubota, its index is `1`, `2` or `4`). -/
lemma not_forall_isSquare_unitClass : ¬∀ i, IsSquare (f.unitClass i) := by
  intro hsq
  choose R hR using fun j ↦ f.exists_isKummerGenerator j
  choose x hx using fun j ↦ IntermediateField.mem_bot.mp (hR j).2.2
  have hx' (j : Fin 3) : ((x j : ℚ) : K) = R j ^ 2 := by
    rw [← hx j, eq_ratCast]
  refine MazurUllomType.false_of_forall_exists (x := x) (fun j ↦ ?_) (fun j ⟨c, hc⟩ ↦ ?_) ?_
    (fun i ↦ ?_)
  · refine (ratCast_nonneg_of_sq_eq (hx' j).symm).lt_of_ne fun h ↦ (hR j).ne_zero ?_
    exact pow_eq_zero_iff two_ne_zero |>.mp ((hx' j).symm.trans (by rw [← h, Rat.cast_zero]))
  · have h2 : R j ^ 2 = (c : K) ^ 2 := by
      rw [← hx' j, hc]
      push_cast
      ring1
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h | h
    · exact (hR j).2.1 (h ▸ SubfieldClass.ratCast_mem _ c)
    · exact (hR j).2.1 (h ▸ neg_mem (SubfieldClass.ratCast_mem _ c))
  · have hmem : R 0 * R 1 * R 2 ∈ (⊥ : IntermediateField ℚ K) := by
      refine mem_bot_of_apply_eq_self (f.aut_ne_one 0) (f.aut_ne_one 1)
        (f.aut_injective.ne (by decide)) ?_ ?_
      · rw [map_mul, map_mul, (hR 0).1, (hR 1).apply_eq_neg (by decide),
          (hR 2).apply_eq_neg (by decide)]
        ring1
      · rw [map_mul, map_mul, (hR 0).apply_eq_neg (by decide), (hR 1).1,
          (hR 2).apply_eq_neg (by decide)]
        ring1
    rcases IntermediateField.mem_bot.mp hmem with ⟨c, hc⟩
    refine ⟨c, Rat.cast_injective (α := K) ?_⟩
    rw [Rat.cast_mul, Rat.cast_mul, Rat.cast_mul, hx' 0, hx' 1, hx' 2,
      ← eq_ratCast (algebraMap ℚ K) c, hc]
    ring1
  · have hj : i + 1 ≠ i := by
      fin_cases i <;> decide
    rcases Fin.exists_ne_and_ne_of_two_lt i (i + 1) (by decide) with ⟨k, hki, hkj⟩
    rcases f.exists_sq_add_two hj.symm (hsq i) with ⟨n, t, s, ht, hs, ht0, hs0, hσt, hσs, hτts⟩
    have ht2 : t ^ 2 = ((n + 2 : ℚ) : K) := by
      push_cast
      exact ht
    have hs2 : s ^ 2 = ((n - 2 : ℚ) : K) := by
      push_cast
      exact hs
    have hσk (y : K) (hy : f.aut i y = -y) (hy' : f.aut (i + 1) y = -y) : f.aut k y = y := by
      rw [f.aut_eq_mul hj.symm hki hkj, AlgEquiv.mul_apply, hy', map_neg, hy, neg_neg]
    have ht2' : t ^ 2 ∈ (⊥ : IntermediateField ℚ K) := ht2 ▸ SubfieldClass.ratCast_mem _ _
    have hs2' : s ^ 2 ∈ (⊥ : IntermediateField ℚ K) := hs2 ▸ SubfieldClass.ratCast_mem _ _
    have hτt : f.aut (i + 1) t ^ 2 = t ^ 2 := by
      rw [← map_pow, ht2, map_ratCast]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hτt with hτ | hτ
    · have hτs : f.aut (i + 1) s = -s := by
        rw [map_mul, hτ] at hτts
        exact mul_left_cancel₀ ht0 (hτts.trans (neg_mul_eq_mul_neg t s))
      rcases f.exists_eq_mul_sq (hR (i + 1)) (isKummerGenerator_of_apply_eq_neg ht0 ht2' hσt hτ)
        (hx' (i + 1)) ht2 with ⟨q, hq⟩
      rcases f.exists_eq_mul_sq (hR k)
        (isKummerGenerator_of_apply_eq_neg hs0 hs2' hσs (hσk s hσs hτs)) (hx' k) hs2
        with ⟨q', hq'⟩
      exact ⟨n, i + 1, k, q, q', hj, hki, hkj.symm, hq, hq'⟩
    · have hτs : f.aut (i + 1) s = s := by
        rw [map_mul, hτ] at hτts
        refine mul_left_cancel₀ (neg_ne_zero.mpr ht0) ?_
        rw [hτts, neg_mul]
      rcases f.exists_eq_mul_sq (hR k)
        (isKummerGenerator_of_apply_eq_neg ht0 ht2' hσt (hσk t hσt hτ)) (hx' k) ht2 with ⟨q, hq⟩
      rcases f.exists_eq_mul_sq (hR (i + 1)) (isKummerGenerator_of_apply_eq_neg hs0 hs2' hσs hτs)
        (hx' (i + 1)) hs2 with ⟨q', hq'⟩
      exact ⟨n, k, i + 1, q, q', hki, hj, hkj, hq, hq'⟩

end Units.QuadraticUnitFrame

end NumberField
