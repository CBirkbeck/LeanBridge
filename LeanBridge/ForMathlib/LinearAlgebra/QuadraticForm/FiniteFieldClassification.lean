import LeanBridge.ForMathlib.GroupTheory.SpecificGroups.OmegaGroup
import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.LinearAlgebra.QuadraticForm.Basis
import TauCeti.LinearAlgebra.QuadraticForm.Prod
import TauCeti.LinearAlgebra.QuadraticForm.Representation

/-!
# Nondegenerate quadratic forms over finite fields

Over a finite field `𝔽_q` the nondegenerate quadratic forms (Mathlib's
`QuadraticMap.Nondegenerate`, which makes sense in every characteristic) fall into the classes of
LMFDB `group.orthogonal`:

* in odd dimension `2 m + 1` they form one similarity class: each becomes isometric to the
  parabolic form `z² + x₁ y₁ + ⋯ + x_m y_m` after scaling by a unit; for odd `q` this class
  consists of two isometry classes, those of the parabolic form and of its multiple by a
  non-square, which take the value `1` a different number of times;
* in even dimension `2 m + 2` they form two isometry classes, those of the hyperbolic form
  `x₁ y₁ + ⋯ + x_{m+1} y_{m+1}` (`+` type) and of the elliptic form
  `x₁ y₁ + ⋯ + x_m y_m + (z² + z w + ζ w²)` (`-` type), and these two are not even similar.

These counts are exact: the standard forms are nondegenerate in every characteristic
(`QuadraticForm.nondegenerate_parabolicForm'`, `QuadraticForm.nondegenerate_hyperbolicForm'`,
`QuadraticForm.nondegenerate_ellipticForm`), and so are the unit multiples of the parabolic form.

The proof works in every characteristic. A quadratic form in at least three variables over `𝔽_q`
is isotropic by the Chevalley–Warning theorem. A nonzero isotropic vector `u` of a form with trivial
radical has a partner `w` with `Q w = 0` and `polar Q u w = 1`, and the space splits as the
orthogonal sum of the plane `x y` spanned by `u`, `w` and of the vectors orthogonal to both, whose
radical is again trivial. So a nondegenerate form is an orthogonal sum of hyperbolic planes and an
anisotropic form of dimension at most `2`, of the same parity as the dimension. A line `⟨a⟩`,
`a ≠ 0`, is similar to `⟨1⟩`. An anisotropic plane is isometric to `x² + x y + ζ y²`: it takes the
value `1` at some `e`, and `e` has a partner `f` with `polar Q e f = 1` and `Q f = ζ`, found with
the subgroup of squares of index `2` in `𝔽_q^×` for odd `q`, and with the image of index `2` of
`t ↦ t² + t` for even `q`.

The hyperbolic and elliptic forms of the same dimension are told apart by their numbers of zeros,
which similarities preserve: adding the plane `x y` to a form `R` on `W` gives
`N(x y ⊥ R) + |W| = q (|W| + N(R))`, and `x y` has `2 q - 1` zeros while the anisotropic plane has
one.

## Main results

* `QuadraticForm.not_anisotropic_of_three_le_finrank`: a quadratic form in at least three variables
  over a finite field is isotropic.
* `QuadraticForm.equivalent_anisotropicPlane`: the anisotropic planes over a finite field are
  isometric to `x² + x y + ζ y²`.
* `QuadraticForm.exists_equivalent_smul_parabolicForm` (LMFDB `group.orthogonal`): one similarity
  class in odd dimension.
* `QuadraticForm.equivalent_hyperbolicForm_or_equivalent_ellipticForm` (LMFDB `group.orthogonal`):
  two isometry classes in even dimension.
* `QuadraticForm.not_equivalent_smul_hyperbolicForm_ellipticForm` (LMFDB `group.orthogonal`): the
  hyperbolic and elliptic forms are not similar.
* `QuadraticForm.equivalent_parabolicForm_or_equivalent_smul_parabolicForm`,
  `QuadraticForm.not_equivalent_smul_parabolicForm` (LMFDB `group.orthogonal`): for odd `q`, two
  isometry classes in odd dimension.

## References

* P. Kleidman, M. Liebeck, *The Subgroup Structure of the Finite Classical Groups*, Cambridge
  University Press (1990), §2.5.
-/

universe u

open Module QuadraticMap

open scoped Finset

namespace QuadraticForm

variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  {Q : QuadraticForm F V} {Q' : QuadraticForm F W} {u w : V} {a b : F} (c : Fˣ) {ν : Fˣ} {m : ℕ}

variable (F) in
/-- The binary hyperbolic form `x y` on `F × F`, the summand of `QuadraticForm.hyperbolicForm`. -/
private abbrev xyForm : QuadraticForm F (F × F) :=
  linMulLin (LinearMap.fst F F F) (LinearMap.snd F F F)

variable (Q u w) in
/-- The vectors orthogonal to both `u` and `w` for the polar form of `Q`. -/
private def pairComplement : Submodule F V :=
  LinearMap.ker (polarBilin Q u) ⊓ LinearMap.ker (polarBilin Q w)

private lemma mem_pairComplement {v : V} :
    v ∈ pairComplement Q u w ↔ polar Q u v = 0 ∧ polar Q w v = 0 := by
  simp [pairComplement]

/-- The splitting `V = ⟨u, w⟩ ⊥ ⟨u, w⟩^⊥` along a hyperbolic pair `u`, `w`. -/
private def pairSplitting (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 1) :
    ((xyForm F).prod (Q.restrict (pairComplement Q u w))).IsometryEquiv Q where
  toFun p := p.1.1 • u + p.1.2 • w + p.2
  invFun v := ((polar Q w v, polar Q u v), ⟨v - polar Q w v • u - polar Q u v • w,
    mem_pairComplement.mpr ⟨by simp [hu, huw], by simp [hw, polar_comm Q w u, huw]⟩⟩)
  map_add' p p' := by
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_smul]
    abel
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_eq_mul, mul_smul,
      RingHom.id_apply, smul_add]
  left_inv p := by
    rcases p with ⟨⟨s, t⟩, c, hc⟩
    rcases mem_pairComplement.mp hc with ⟨hcu, hcw⟩
    ext
    · simp [hw, hcw, polar_comm Q w u, huw]
    · simp [hu, hcu, huw]
    · simp [hu, hw, hcu, hcw, huw, polar_comm Q w u]
      abel
  right_inv v := by
    simp only
    abel
  map_app' p := by
    rcases p with ⟨⟨s, t⟩, c, hc⟩
    rcases mem_pairComplement.mp hc with ⟨hcu, hcw⟩
    simp [QuadraticMap.map_add, QuadraticMap.map_smul, hu, hw, huw, hcu, hcw]
    ring1

private lemma pairSplitting_apply (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 1)
    (p : (F × F) × pairComplement Q u w) :
    pairSplitting hu hw huw p = p.1.1 • u + p.1.2 • w + p.2 :=
  rfl

private lemma radical_restrict_pairComplement (hQ : Q.radical = ⊥) (hu : Q u = 0) (hw : Q w = 0)
    (huw : polar Q u w = 1) : (Q.restrict (pairComplement Q u w)).radical = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun c hc ↦ Subtype.ext ?_
  rcases mem_pairComplement.mp c.2 with ⟨hcu, hcw⟩
  have hc' : ∀ c' ∈ pairComplement Q u w, polar Q c c' = 0 := fun c' hc' ↦
    LinearMap.congr_fun hc.2 ⟨c', hc'⟩
  refine (Submodule.eq_bot_iff _).mp hQ c ⟨hc.1, LinearMap.ext fun v ↦ ?_⟩
  rw [← (pairSplitting hu hw huw).apply_symm_apply v]
  rcases (pairSplitting hu hw huw).symm v with ⟨⟨s, t⟩, c', hc''⟩
  simp [pairSplitting_apply, polar_comm Q (c : V) u, polar_comm Q (c : V) w, hcu, hcw,
    hc' c' hc'']

private lemma equivalent_smul (h : Q.Equivalent Q') : (c • Q).Equivalent (c • Q') := by
  rcases h with ⟨e⟩
  exact ⟨{ e.toLinearEquiv with map_app' := fun v ↦ by simp }⟩

private lemma equivalent_smul_xyForm : (c • xyForm F).Equivalent (xyForm F) :=
  ⟨{ toLinearEquiv := (LinearEquiv.smulOfUnit c).prodCongr (LinearEquiv.refl F F)
     map_app' := fun _ ↦ mul_assoc _ _ _ }⟩

variable (m) in
private lemma equivalent_xyForm_prod_hyperbolicForm :
    ((xyForm F).prod (hyperbolicForm F m)).Equivalent (hyperbolicForm F (m + 1)) :=
  ⟨IsometryEquiv.consPi fun _ ↦ xyForm F⟩

variable (a) in
private lemma natCard_apply_eq_congr (h : Q.Equivalent Q') :
    Nat.card {v // Q v = a} = Nat.card {v // Q' v = a} := by
  rcases h with ⟨e⟩
  exact Nat.card_congr (e.toLinearEquiv.toEquiv.subtypeEquiv fun v ↦ by simp)

private lemma natCard_zeros_smul : Nat.card {v // (c • Q) v = 0} = Nat.card {v // Q v = 0} :=
  Nat.card_congr (Equiv.subtypeEquivRight fun v ↦ by simp [Units.smul_def])

variable (Q') in
private lemma equivalent_smul_of_eq_mul_mul {r s d : Fˣ} (h : (r : F) = s * (d * d)) :
    (r • Q').Equivalent (s • Q') :=
  ⟨{ toLinearEquiv := LinearEquiv.smulOfUnit d
     map_app' := fun v ↦ by
       simp [LinearEquiv.smulOfUnit, Units.smul_def, QuadraticMap.map_smul, h, mul_assoc] }⟩

private lemma natCard_hyperbolicForm_zero_apply_eq (ha : a ≠ 0) :
    Nat.card {v // hyperbolicForm F 0 v = a} = 0 :=
  Nat.card_eq_zero.mpr (.inl ⟨fun v ↦ ha (v.2.symm.trans (by simp [hyperbolicForm_apply]))⟩)

variable (a) in
private lemma natCard_parabolicForm_apply_eq [Fintype F] : Nat.card {v // parabolicForm F m v = a} =
    ∑ z : F, Nat.card {h // hyperbolicForm F m h = a - z * z} := by
  rw [← Nat.card_sigma]
  exact Nat.card_congr ((Equiv.subtypeEquivRight fun v ↦ by
    simp only [parabolicForm, prod_apply, sq_apply]
    exact ⟨fun h ↦ by rw [← h]; ring1, fun h ↦ by rw [h]; ring1⟩).trans
      (Equiv.subtypeProdEquivSigmaSubtype fun (z : F) (h : Fin m → F × F) ↦
        hyperbolicForm F m h = a - z * z))

lemma nondegenerate_smul_parabolicForm : (c • parabolicForm F m).Nondegenerate :=
  (nondegenerate_smul_iff c.isUnit _).mpr (nondegenerate_parabolicForm' F m)

variable [FiniteDimensional F V]

private lemma finrank_pairComplement (hu : Q u = 0) (hw : Q w = 0) (huw : polar Q u w = 1) :
    finrank F (pairComplement Q u w) + 2 = finrank F V := by
  rw [← (pairSplitting hu hw huw).toLinearEquiv.finrank_eq, finrank_prod, finrank_prod,
    finrank_self]
  ring1

private lemma equivalent_hyperbolicForm_zero (hV : finrank F V = 0) :
    Q.Equivalent (hyperbolicForm F 0) := by
  have : Subsingleton V := Module.finrank_zero_iff.mp hV
  exact ⟨{ toLinearEquiv := LinearEquiv.ofFinrankEq V (Fin 0 → F × F)
             (by simp [hV, Module.finrank_pi_fintype])
           map_app' := fun v ↦ by simp [Subsingleton.elim v 0, hyperbolicForm_apply] }⟩

private lemma exists_equivalent_smul_parabolicForm_zero (hQ : Q.radical = ⊥)
    (hV : finrank F V = 1) : ∃ c : Fˣ, (c • Q).Equivalent (parabolicForm F 0) := by
  let b : Basis (Fin 1) F V := finBasisOfFinrankEq F V hV
  have hb (v : V) : b.repr v 0 • b 0 = v := by
    simpa using b.sum_repr v
  have ha : Q (b 0) ≠ 0 := fun h ↦ b.ne_zero 0 <| (Submodule.eq_bot_iff _).mp hQ _
    ⟨h, LinearMap.ext fun v ↦ by
      rw [← hb v]
      simp [h]⟩
  let e : ((Units.mk0 _ ha)⁻¹ • Q).IsometryEquiv (sq : QuadraticForm F F) :=
    { toLinearEquiv := b.equivFun.trans (LinearEquiv.funUnique (Fin 1) F F)
      map_app' := fun v ↦ by
        conv_rhs => rw [← hb v]
        simp [QuadraticMap.map_smul, Units.smul_def]
        field_simp }
  exact ⟨_, ⟨(e.trans (IsometryEquiv.uniqueProd (hyperbolicForm F 0) sq).symm).trans
    (IsometryEquiv.prodComm _ _)⟩⟩

variable [Finite F]

variable (Q) in
/-- **Chevalley–Warning for quadratic forms**: a quadratic form on a space of dimension at least
`3` over a finite field is isotropic. In coordinates it is a polynomial of degree `2` in at least
`3` variables, whose number of zeros is divisible by the characteristic. -/
lemma not_anisotropic_of_three_le_finrank (hV : 3 ≤ finrank F V) : ¬Q.Anisotropic := by
  classical
  have : Fintype F := Fintype.ofFinite F
  let b : Basis (Fin (finrank F V)) F V := finBasis F V
  let f : MvPolynomial (Fin (finrank F V)) F := ∑ i, ∑ j,
    MvPolynomial.C (Q.toBilin b (b i) (b j)) * MvPolynomial.X i * MvPolynomial.X j
  have hf (x : Fin (finrank F V) → F) : MvPolynomial.eval x f = Q (b.equivFun.symm x) := by
    rw [← toQuadraticMap_toBilin Q b]
    simp [f, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring1
  have hdeg : f.totalDegree < Fintype.card (Fin (finrank F V)) := by
    refine lt_of_le_of_lt (MvPolynomial.totalDegree_finsetSum_le fun i _ ↦
      MvPolynomial.totalDegree_finsetSum_le fun j _ ↦ ?_)
      (by rw [Fintype.card_fin]; omega : 2 < _)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    refine (add_le_add (MvPolynomial.totalDegree_mul _ _) (MvPolynomial.totalDegree_X j).le).trans
      ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]
  have hp : (ringChar F).Prime := CharP.char_is_prime F (ringChar F)
  have hdvd : ringChar F ∣ Fintype.card {x // MvPolynomial.eval x f = 0} :=
    char_dvd_card_solutions (ringChar F) hdeg
  have h0 : MvPolynomial.eval 0 f = 0 := by
    rw [hf, map_zero, QuadraticMap.map_zero]
  rcases Fintype.exists_ne_of_one_lt_card ((hp.one_lt).trans_le (Nat.le_of_dvd
    (Fintype.card_pos_iff.mpr ⟨⟨0, h0⟩⟩) hdvd)) ⟨0, h0⟩ with ⟨⟨x, hx⟩, hne⟩
  refine (not_anisotropic_iff_exists Q).mpr
    ⟨b.equivFun.symm x, fun h ↦ hne ?_, (hf x).symm.trans hx⟩
  exact Subtype.ext (b.equivFun.symm.injective (h.trans (map_zero _).symm))

private lemma equivalent_anisotropicPlane_of_pair (hV : finrank F V = 2) {e f : V} (he : Q e = 1)
    (hf : Q f = anisotropicCoeff F) (hef : polar Q e f = 1) :
    Q.Equivalent (anisotropicPlane F) := by
  let φ : F × F →ₗ[F] V := (LinearMap.fst F F F).smulRight e + (LinearMap.snd F F F).smulRight f
  have hφ (v : F × F) : Q (φ v) = anisotropicPlane F v := by
    simp [φ, QuadraticMap.map_add, QuadraticMap.map_smul, he, hf, hef, anisotropicPlane_apply]
    ring1
  have hinj : Function.Injective φ := (injective_iff_map_eq_zero φ).mpr fun v hv ↦
    anisotropic_anisotropicPlane F v (by rw [← hφ, hv, QuadraticMap.map_zero])
  have hbij : Function.Bijective φ := ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hV])).mp hinj⟩
  exact Equivalent.symm ⟨{ LinearEquiv.ofBijective φ hbij with map_app' := hφ }⟩

private lemma exists_apply_eq_one (hQ : Q.Anisotropic) (hV : finrank F V = 2) : ∃ e, Q e = 1 := by
  rcases (not_anisotropic_iff_exists _).mp (not_anisotropic_of_three_le_finrank
    (Q.prod (-QuadraticMap.sq)) (by simp [hV])) with ⟨⟨v, t⟩, hne, h0⟩
  simp only [prod_apply, neg_apply, sq_apply] at h0
  have ht : t ≠ 0 := fun ht ↦ hne <| by
    rw [ht, mul_zero, neg_zero, add_zero] at h0
    rw [hQ v h0, ht, Prod.mk_zero_zero]
  refine ⟨t⁻¹ • v, ?_⟩
  rw [QuadraticMap.map_smul, smul_eq_mul]
  field_simp
  linear_combination h0

private lemma isSquare_mul_of_not_isSquare (h2 : ringChar F ≠ 2) (ha : ¬IsSquare a)
    (hb : ¬IsSquare b) : IsSquare (a * b) := by
  have : Fintype F := Fintype.ofFinite F
  have ha0 : a ≠ 0 := fun h ↦ ha (h ▸ IsSquare.zero)
  have hb0 : b ≠ 0 := fun h ↦ hb (h ▸ IsSquare.zero)
  rw [FiniteField.isSquare_iff h2 (mul_ne_zero ha0 hb0), mul_pow]
  rcases FiniteField.pow_dichotomy h2 ha0 with h | h
  · exact absurd ((FiniteField.isSquare_iff h2 ha0).mpr h) ha
  rcases FiniteField.pow_dichotomy h2 hb0 with h' | h'
  · exact absurd ((FiniteField.isSquare_iff h2 hb0).mpr h') hb
  rw [h, h', neg_one_mul, neg_neg]

/-- **The anisotropic planes over a finite field are isometric**: an anisotropic quadratic form in
two variables over a finite field is isometric to `x² + x y + ζ y²`, for the chosen `ζ`
(`QuadraticForm.anisotropicCoeff`) such that `t² + t + ζ` has no root. -/
lemma equivalent_anisotropicPlane (hQ : Q.Anisotropic) (hV : finrank F V = 2) :
    Q.Equivalent (anisotropicPlane F) := by
  have : Fintype F := Fintype.ofFinite F
  rcases exists_apply_eq_one hQ hV with ⟨e, he⟩
  have hζ (t : F) : t ^ 2 + t + anisotropicCoeff F ≠ 0 := sq_add_add_anisotropicCoeff_ne_zero F t
  by_cases h2 : ringChar F = 2
  · have h20 : (2 : F) = 0 := by
      have : CharP F 2 := ringChar.of_eq h2
      exact_mod_cast CharP.cast_eq_zero F 2
    have hee : polar Q e e = 0 := by
      rw [polar_self, he, nsmul_eq_mul, Nat.cast_ofNat, h20, zero_mul]
    have hex : ∃ v, polar Q e v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      have hspan : (⊤ : Submodule F V) ≤ F ∙ e := fun v _ ↦ by
        rcases FiniteField.isSquare_of_char_two h2 (Q v) with ⟨r, hr⟩
        have h0 : Q (r • e + v) = 0 := by
          rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, he, hr, polar_smul_left, hcon]
          linear_combination (r * r) * h20
        rw [eq_neg_of_add_eq_zero_right (hQ _ h0)]
        exact neg_mem (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self e))
      have hle : finrank F (⊤ : Submodule F V) ≤ finrank F (F ∙ e) := Submodule.finrank_mono hspan
      have he0 : e ≠ 0 := by
        rintro rfl
        simp at he
      rw [finrank_top, hV, finrank_span_singleton he0] at hle
      exact absurd hle (by norm_num)
    rcases hex with ⟨v, hv⟩
    set f₀ : V := (polar Q e v)⁻¹ • v with hf₀
    have hef₀ : polar Q e f₀ = 1 := by
      rw [hf₀, polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hv]
    let φ : F →+ F := AddMonoidHom.mk' (fun t ↦ t ^ 2 + t) fun s t ↦ by
      linear_combination (s * t) * h20
    have hφ (t : F) : φ t = t ^ 2 + t := rfl
    have hker : Nat.card φ.ker = 2 := by
      refine Nat.card_eq_two_iff.mpr ⟨⟨0, by simp⟩, ⟨1, by
        rw [AddMonoidHom.mem_ker, hφ]
        linear_combination h20⟩, by simp, Set.eq_univ_of_forall fun t ↦ ?_⟩
      have h0 : t.1 ^ 2 + t.1 = 0 := (hφ t.1).symm.trans (AddMonoidHom.mem_ker.mp t.2)
      have ht : t.1 * (t.1 + 1) = 0 := by
        linear_combination h0
      rcases mul_eq_zero.mp ht with h | h
      · exact .inl (Subtype.ext h)
      · exact .inr (Set.mem_singleton_iff.mpr (Subtype.ext (by linear_combination h - h20)))
    have hidx : φ.range.index = 2 := by
      have h1 : Nat.card φ.ker * φ.ker.index = Nat.card F := φ.ker.card_mul_index
      have h3 : Nat.card φ.range * φ.range.index = Nat.card F := φ.range.card_mul_index
      rw [hker, AddSubgroup.index_ker] at h1
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h3.trans (h1.symm.trans (mul_comm _ _)))
    have hγ : Q f₀ ∉ φ.range := by
      rintro ⟨t, ht⟩
      have h0 : Q (t • e + f₀) = 0 := by
        rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, he, polar_smul_left, hef₀, ← ht, hφ]
        linear_combination (t ^ 2 + t) * h20
      have h1 : polar Q e (t • e + f₀) = 1 := by
        rw [polar_add_right, polar_smul_right, hee, hef₀, smul_zero, zero_add]
      rw [hQ _ h0, polar_zero_right] at h1
      exact zero_ne_one h1
    have hζ' : anisotropicCoeff F ∉ φ.range := by
      rintro ⟨t, ht⟩
      have h' : t ^ 2 + t = anisotropicCoeff F := (hφ t).symm.trans ht
      exact hζ t (by linear_combination h' + anisotropicCoeff F * h20)
    rcases (AddSubgroup.add_mem_iff_of_index_two hidx).mpr (iff_of_false hγ hζ') with ⟨u, hu⟩
    refine equivalent_anisotropicPlane_of_pair hV he (f := u • e + f₀) ?_ ?_
    · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, he, polar_smul_left, hef₀]
      linear_combination (hφ u).symm.trans hu + Q f₀ * h20
    · rw [polar_add_right, polar_smul_right, hee, hef₀, smul_zero, zero_add]
  · have h20 : (2 : F) ≠ 0 := Ring.two_ne_zero h2
    have hker : LinearMap.ker (polarBilin Q e) ≠ ⊥ := fun h ↦ by
      have h1 : finrank F (LinearMap.range (polarBilin Q e)) +
          finrank F (LinearMap.ker (polarBilin Q e)) = finrank F V :=
        LinearMap.finrank_range_add_finrank_ker _
      have h3 : finrank F (LinearMap.range (polarBilin Q e)) ≤ 1 :=
        (Submodule.finrank_le _).trans (finrank_self F).le
      rw [h, finrank_bot, hV] at h1
      omega
    rcases Submodule.exists_mem_ne_zero_of_ne_bot hker with ⟨g, hg, hg0⟩
    have hge : polar Q e g = 0 := hg
    have hδ : Q g ≠ 0 := fun h ↦ hg0 (hQ g h)
    have hnδ : ¬IsSquare (-Q g) := fun ⟨r, hr⟩ ↦ hg0 <| by
      have h0 : Q (r • e + g) = 0 := by
        rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, he, polar_smul_left, hge]
        linear_combination -hr
      have h1 : polar Q e (r • e + g) = 2 * r := by
        rw [polar_add_right, polar_smul_right, polar_self, he, hge, smul_eq_mul, nsmul_eq_mul]
        push_cast
        ring1
      rw [hQ _ h0, polar_zero_right] at h1
      have hr0 : r = 0 := (mul_eq_zero.mp h1.symm).resolve_left h20
      rw [hr0, zero_smul, zero_add] at h0
      exact hQ g h0
    have hnζ : ¬IsSquare (1 - 4 * anisotropicCoeff F) := fun ⟨w, hw⟩ ↦ hζ ((w - 1) / 2) <| by
      field_simp
      linear_combination -hw
    rcases isSquare_mul_of_not_isSquare h2 hnζ hnδ with ⟨s, hs⟩
    refine equivalent_anisotropicPlane_of_pair hV he (f := (2⁻¹ : F) • e + (s / (2 * -Q g)) • g)
      ?_ ?_
    · rw [QuadraticMap.map_add Q, QuadraticMap.map_smul, QuadraticMap.map_smul, he,
        polar_smul_left, polar_smul_right, hge]
      simp only [smul_eq_mul]
      field_simp
      linear_combination -hs
    · rw [polar_add_right, polar_smul_right, polar_smul_right, polar_self, he, hge, smul_eq_mul,
        smul_zero, add_zero, nsmul_eq_mul, Nat.cast_ofNat, mul_one, inv_mul_cancel₀ h20]

variable (m) in
private lemma exists_equivalent_smul_parabolicForm_aux : ∀ (E : Type u) [AddCommGroup E]
    [Module F E] [FiniteDimensional F E] (Q : QuadraticForm F E), Q.radical = ⊥ →
    finrank F E = 2 * m + 1 → ∃ c : Fˣ, (c • Q).Equivalent (parabolicForm F m) := by
  induction m with
  | zero =>
    intro E _ _ _ Q hQ hE
    exact exists_equivalent_smul_parabolicForm_zero hQ hE
  | succ m ih =>
    intro E _ _ _ Q hQ hE
    rcases exists_isotropic_pair_of_radical_eq_bot hQ
      (not_anisotropic_of_three_le_finrank Q (by omega)) with ⟨u, w, -, hu, hw, huw⟩
    have hrank : finrank F (pairComplement Q u w) + 2 = finrank F E :=
      finrank_pairComplement hu hw huw
    rcases ih _ _ (radical_restrict_pairComplement hQ hu hw huw) (by omega) with ⟨c, hc⟩
    have h1 : (c • Q).Equivalent (c • (xyForm F).prod (Q.restrict (pairComplement Q u w))) :=
      equivalent_smul c ⟨(pairSplitting hu hw huw).symm⟩
    rw [smul_prod] at h1
    exact ⟨c, h1.trans (((equivalent_smul_xyForm c).prod hc).trans
      (Equivalent.trans ⟨IsometryEquiv.prodLeftComm _ _ _⟩
        ((Equivalent.refl _).prod (equivalent_xyForm_prod_hyperbolicForm m))))⟩

variable (m) in
private lemma equivalent_hyperbolicForm_or_ellipticForm_aux : ∀ (E : Type u) [AddCommGroup E]
    [Module F E] [FiniteDimensional F E] (Q : QuadraticForm F E), Q.radical = ⊥ →
    finrank F E = 2 * m + 2 → Q.Equivalent (hyperbolicForm F (m + 1)) ∨
      Q.Equivalent (ellipticForm F m) := by
  induction m with
  | zero =>
    intro E _ _ _ Q hQ hE
    by_cases hiso : Q.Anisotropic
    · exact .inr ((equivalent_anisotropicPlane hiso hE).trans
        ⟨(IsometryEquiv.uniqueProd (hyperbolicForm F 0) (anisotropicPlane F)).symm⟩)
    · rcases exists_isotropic_pair_of_radical_eq_bot hQ hiso with ⟨u, w, -, hu, hw, huw⟩
      have hrank : finrank F (pairComplement Q u w) + 2 = finrank F E :=
        finrank_pairComplement hu hw huw
      exact .inl (Equivalent.trans ⟨(pairSplitting hu hw huw).symm⟩
        (((Equivalent.refl _).prod (equivalent_hyperbolicForm_zero (by omega))).trans
          (equivalent_xyForm_prod_hyperbolicForm 0)))
  | succ m ih =>
    intro E _ _ _ Q hQ hE
    rcases exists_isotropic_pair_of_radical_eq_bot hQ
      (not_anisotropic_of_three_le_finrank Q (by omega)) with ⟨u, w, -, hu, hw, huw⟩
    have hrank : finrank F (pairComplement Q u w) + 2 = finrank F E :=
      finrank_pairComplement hu hw huw
    have hsplit : Q.Equivalent ((xyForm F).prod (Q.restrict (pairComplement Q u w))) :=
      ⟨(pairSplitting hu hw huw).symm⟩
    rcases ih _ _ (radical_restrict_pairComplement hQ hu hw huw) (by omega) with h | h
    · exact .inl (hsplit.trans (((Equivalent.refl _).prod h).trans
        (equivalent_xyForm_prod_hyperbolicForm _)))
    · exact .inr (hsplit.trans (((Equivalent.refl _).prod h).trans
        (Equivalent.trans ⟨(IsometryEquiv.prodAssoc _ _ _).symm⟩
          ((equivalent_xyForm_prod_hyperbolicForm m).prod (Equivalent.refl _)))))

variable (Q' a) in
private lemma natCard_apply_eq_xyForm_prod [Finite W] : Nat.card {v // ((xyForm F).prod Q') v = a} +
    Nat.card W = Nat.card F * (Nat.card W + Nat.card {w // Q' w = a}) := by
  classical
  have : Fintype F := Fintype.ofFinite F
  let N (s : F) : ℕ := Nat.card {y : F × W // s * y.1 + Q' y.2 = a}
  have hsum : Nat.card {v // ((xyForm F).prod Q') v = a} = ∑ s, N s := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr ((Equiv.subtypeEquiv (p := fun v ↦ ((xyForm F).prod Q') v = a)
      (q := fun c : F × F × W ↦ c.1 * c.2.1 + Q' c.2.2 = a) (Equiv.prodAssoc F F W)
      fun v ↦ by simp).trans
        (Equiv.subtypeProdEquivSigmaSubtype fun (s : F) (y : F × W) ↦ s * y.1 + Q' y.2 = a))
  have hN0 : N 0 = Nat.card F * Nat.card {w // Q' w = a} := by
    rw [← Nat.card_prod]
    exact Nat.card_congr
      { toFun y := (y.1.1, ⟨y.1.2, by simpa using y.2⟩)
        invFun y := ⟨(y.1, y.2.1), by simpa using y.2.2⟩
        left_inv y := rfl
        right_inv y := rfl }
  have hN (s : F) (hs : s ≠ 0) : N s = Nat.card W := Nat.card_congr
    { toFun y := y.1.2
      invFun w := ⟨((a - Q' w) / s, w), by field_simp; ring1⟩
      left_inv y := Subtype.ext (Prod.ext (by
        field_simp
        linear_combination -y.2) rfl)
      right_inv w := rfl }
  rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ 0), hN0,
    Finset.sum_congr rfl fun s hs ↦ hN s (Finset.ne_of_mem_erase hs), Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card]
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  zify [hq]
  ring1

variable (m) in
private lemma natCard_zeros_hyperbolicForm_prod (X Y : QuadraticForm F (F × F))
    (h : Nat.card {v // ((hyperbolicForm F m).prod X) v = 0} =
      Nat.card {v // ((hyperbolicForm F m).prod Y) v = 0}) :
    Nat.card {v // X v = 0} = Nat.card {v // Y v = 0} := by
  induction m with
  | zero =>
    rwa [natCard_apply_eq_congr _ ⟨IsometryEquiv.uniqueProd (hyperbolicForm F 0) X⟩,
      natCard_apply_eq_congr _ ⟨IsometryEquiv.uniqueProd (hyperbolicForm F 0) Y⟩] at h
  | succ m ih =>
    refine ih ?_
    have hX : ((hyperbolicForm F (m + 1)).prod X).Equivalent
        ((xyForm F).prod ((hyperbolicForm F m).prod X)) :=
      ((equivalent_xyForm_prod_hyperbolicForm m).symm.prod (Equivalent.refl X)).trans
        ⟨IsometryEquiv.prodAssoc _ _ _⟩
    have hY : ((hyperbolicForm F (m + 1)).prod Y).Equivalent
        ((xyForm F).prod ((hyperbolicForm F m).prod Y)) :=
      ((equivalent_xyForm_prod_hyperbolicForm m).symm.prod (Equivalent.refl Y)).trans
        ⟨IsometryEquiv.prodAssoc _ _ _⟩
    rw [natCard_apply_eq_congr _ hX, natCard_apply_eq_congr _ hY] at h
    have h1 : Nat.card {v // ((xyForm F).prod ((hyperbolicForm F m).prod X)) v = 0} +
        Nat.card ((Fin m → F × F) × (F × F)) = Nat.card F *
          (Nat.card ((Fin m → F × F) × (F × F)) +
            Nat.card {w // ((hyperbolicForm F m).prod X) w = 0}) :=
      natCard_apply_eq_xyForm_prod _ 0
    have h2 : Nat.card {v // ((xyForm F).prod ((hyperbolicForm F m).prod Y)) v = 0} +
        Nat.card ((Fin m → F × F) × (F × F)) = Nat.card F *
          (Nat.card ((Fin m → F × F) × (F × F)) +
            Nat.card {w // ((hyperbolicForm F m).prod Y) w = 0}) :=
      natCard_apply_eq_xyForm_prod _ 0
    rw [h] at h1
    exact Nat.add_left_cancel (Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.symm.trans h2))

private lemma natCard_zeros_xyForm : Nat.card {v // xyForm F v = 0} + 1 = 2 * Nat.card F := by
  have h : Nat.card {v // ((xyForm F).prod (hyperbolicForm F 0)) v = 0} +
      Nat.card (Fin 0 → F × F) = Nat.card F * (Nat.card (Fin 0 → F × F) +
        Nat.card {w // hyperbolicForm F 0 w = 0}) :=
    natCard_apply_eq_xyForm_prod _ 0
  have hW : Nat.card (Fin 0 → F × F) = 1 := Nat.card_unique
  have h0 : Nat.card {w // hyperbolicForm F 0 w = 0} = 1 :=
    (Nat.card_congr (Equiv.subtypeUnivEquiv fun w ↦ by simp [hyperbolicForm_apply])).trans hW
  rw [natCard_apply_eq_congr _ ⟨(IsometryEquiv.prodComm _ _).trans
    (IsometryEquiv.uniqueProd (hyperbolicForm F 0) (xyForm F))⟩, h0, hW] at h
  rw [h]
  ring1

private lemma natCard_zeros_anisotropicPlane : Nat.card {v // anisotropicPlane F v = 0} = 1 :=
  Nat.card_eq_one_iff_exists.mpr
    ⟨⟨0, by simp⟩, fun v ↦ Subtype.ext (anisotropic_anisotropicPlane F v.1 v.2)⟩

variable (m) in
/-- **The hyperbolic and elliptic forms are not similar** (LMFDB `group.orthogonal`): no scalar
multiple of `x₁ y₁ + ⋯ + x_{m+1} y_{m+1}` is isometric to `x₁ y₁ + ⋯ + x_m y_m + (z² + z w + ζ w²)`.
A similarity preserves the zeros of a form; an orthogonal sum with the plane `x y` multiplies the
number of zeros by `q` up to a term depending only on dimensions, and `x y` has `2 q - 1` zeros
while the anisotropic plane has one. -/
lemma not_equivalent_smul_hyperbolicForm_ellipticForm :
    ¬(c • hyperbolicForm F (m + 1)).Equivalent (ellipticForm F m) := fun h ↦ by
  have hH : (hyperbolicForm F (m + 1)).Equivalent ((hyperbolicForm F m).prod (xyForm F)) :=
    (equivalent_xyForm_prod_hyperbolicForm m).symm.trans ⟨IsometryEquiv.prodComm _ _⟩
  have h1 : Nat.card {v // ((hyperbolicForm F m).prod (xyForm F)) v = 0} =
      Nat.card {v // ((hyperbolicForm F m).prod (anisotropicPlane F)) v = 0} := by
    rw [← natCard_apply_eq_congr _ hH, ← natCard_zeros_smul c, natCard_apply_eq_congr _ h]
    rfl
  have h2 : Nat.card {v // xyForm F v = 0} + 1 = 2 * Nat.card F := natCard_zeros_xyForm
  rw [natCard_zeros_hyperbolicForm_prod m _ _ h1, natCard_zeros_anisotropicPlane] at h2
  have hq : 1 < Nat.card F := Finite.one_lt_card
  omega

/-- **The nondegenerate quadratic forms of odd dimension over a finite field form one similarity
class** (LMFDB `group.orthogonal`): a nondegenerate form of dimension `2 m + 1` over `𝔽_q` is
isometric, after scaling by a unit, to the parabolic form `z² + x₁ y₁ + ⋯ + x_m y_m`. The form is
the orthogonal sum of `m` hyperbolic planes, split off along isotropic vectors (which exist in
dimension at least `3` by Chevalley–Warning), and of a line `⟨a⟩` with `a ≠ 0`. -/
lemma exists_equivalent_smul_parabolicForm (hQ : Q.Nondegenerate) (hV : finrank F V = 2 * m + 1) :
    ∃ c : Fˣ, (c • Q).Equivalent (parabolicForm F m) :=
  exists_equivalent_smul_parabolicForm_aux m V Q hQ.radical_eq_bot hV

/-- **The nondegenerate quadratic forms of even dimension over a finite field form two isometry
classes** (LMFDB `group.orthogonal`): a nondegenerate form of dimension `2 m + 2` over `𝔽_q` is
isometric to the hyperbolic form (`+` type) or to the elliptic form (`-` type), which are not
similar (`QuadraticForm.not_equivalent_smul_hyperbolicForm_ellipticForm`). The form is the
orthogonal sum of hyperbolic planes and of an anisotropic form of dimension `0` or `2`, and the
anisotropic planes are all isometric (`QuadraticForm.equivalent_anisotropicPlane`). -/
lemma equivalent_hyperbolicForm_or_equivalent_ellipticForm (hQ : Q.Nondegenerate)
    (hV : finrank F V = 2 * m + 2) :
    Q.Equivalent (hyperbolicForm F (m + 1)) ∨ Q.Equivalent (ellipticForm F m) :=
  equivalent_hyperbolicForm_or_ellipticForm_aux m V Q hQ.radical_eq_bot hV

variable (m) in
private lemma natCard_hyperbolicForm_apply_eq (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.card {v // hyperbolicForm F m v = a} = Nat.card {v // hyperbolicForm F m v = b} := by
  induction m with
  | zero => rw [natCard_hyperbolicForm_zero_apply_eq ha, natCard_hyperbolicForm_zero_apply_eq hb]
  | succ m ih =>
    have h1 : Nat.card {v // ((xyForm F).prod (hyperbolicForm F m)) v = a} +
        Nat.card (Fin m → F × F) = Nat.card F * (Nat.card (Fin m → F × F) +
          Nat.card {w // hyperbolicForm F m w = a}) :=
      natCard_apply_eq_xyForm_prod _ a
    have h2 : Nat.card {v // ((xyForm F).prod (hyperbolicForm F m)) v = b} +
        Nat.card (Fin m → F × F) = Nat.card F * (Nat.card (Fin m → F × F) +
          Nat.card {w // hyperbolicForm F m w = b}) :=
      natCard_apply_eq_xyForm_prod _ b
    rw [ih, ← h2, natCard_apply_eq_congr a (equivalent_xyForm_prod_hyperbolicForm m),
      natCard_apply_eq_congr b (equivalent_xyForm_prod_hyperbolicForm m)] at h1
    exact Nat.add_right_cancel h1

variable (m) in
private lemma natCard_hyperbolicForm_apply_zero_ne (ha : a ≠ 0) :
    Nat.card {v // hyperbolicForm F m v = 0} ≠ Nat.card {v // hyperbolicForm F m v = a} := by
  induction m with
  | zero =>
    rw [natCard_hyperbolicForm_zero_apply_eq ha, (Nat.card_congr
      (Equiv.subtypeUnivEquiv fun w ↦ by simp [hyperbolicForm_apply])).trans Nat.card_unique]
    exact one_ne_zero
  | succ m ih =>
    intro h
    have h1 : Nat.card {v // ((xyForm F).prod (hyperbolicForm F m)) v = 0} +
        Nat.card (Fin m → F × F) = Nat.card F * (Nat.card (Fin m → F × F) +
          Nat.card {w // hyperbolicForm F m w = 0}) :=
      natCard_apply_eq_xyForm_prod _ 0
    have h2 : Nat.card {v // ((xyForm F).prod (hyperbolicForm F m)) v = a} +
        Nat.card (Fin m → F × F) = Nat.card F * (Nat.card (Fin m → F × F) +
          Nat.card {w // hyperbolicForm F m w = a}) :=
      natCard_apply_eq_xyForm_prod _ a
    rw [natCard_apply_eq_congr 0 (equivalent_xyForm_prod_hyperbolicForm m), h,
      ← natCard_apply_eq_congr a (equivalent_xyForm_prod_hyperbolicForm m), h2] at h1
    exact ih (Nat.add_left_cancel (Nat.eq_of_mul_eq_mul_left Nat.card_pos h1).symm)

/-- **The parabolic form and its non-square multiples are not isometric for odd `q`** (LMFDB
`group.orthogonal`): for a non-square `ν`, the forms `z² + x₁ y₁ + ⋯ + x_m y_m` and `ν` times it
take the value `1` a different number of times, so that in odd dimension and odd characteristic
there are two isometry classes of nondegenerate forms, which are similar. -/
lemma not_equivalent_smul_parabolicForm (h2 : ringChar F ≠ 2) (hν : ¬IsSquare (ν : F)) :
    ¬(ν • parabolicForm F m).Equivalent (parabolicForm F m) := fun h ↦ by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcount (a : F) : Nat.card {v // parabolicForm F m v = a} =
      #{z | z * z = a} * Nat.card {v // hyperbolicForm F m v = 0} +
        #{z | ¬z * z = a} * Nat.card {v // hyperbolicForm F m v = 1} := by
    have hterm (z : F) : Nat.card {h // hyperbolicForm F m h = a - z * z} =
        if z * z = a then Nat.card {v // hyperbolicForm F m v = 0} else
          Nat.card {v // hyperbolicForm F m v = 1} := by
      split_ifs with hz
      · rw [hz, sub_self]
      · exact natCard_hyperbolicForm_apply_eq m (sub_ne_zero.mpr (Ne.symm hz)) one_ne_zero
    rw [natCard_parabolicForm_apply_eq, Finset.sum_congr rfl fun z _ ↦ hterm z, Finset.sum_ite,
      Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
  have h1 : #{z : F | z * z = 1} = 2 := by
    rw [show ({z | z * z = 1} : Finset F) = {1, -1} by
      ext z
      simp [mul_self_eq_one_iff], Finset.card_pair (Ring.neg_one_ne_one_of_char_ne_two h2).symm]
  have hν' : #{z : F | z * z = (ν⁻¹ : Fˣ)} = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun z _ hz ↦ hν <| by
      rw [← isSquare_inv, ← Units.val_inv_eq_inv_val, ← hz]
      exact ⟨z, rfl⟩
  have hc : Nat.card {v // parabolicForm F m v = (ν⁻¹ : Fˣ)} =
      Nat.card {v // parabolicForm F m v = 1} := by
    rw [← natCard_apply_eq_congr 1 h]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun v ↦ by
      simp only [smul_apply, Units.smul_def, smul_eq_mul, Units.val_inv_eq_inv_val]
      exact ⟨fun hv ↦ by rw [hv, mul_inv_cancel₀ ν.ne_zero], eq_inv_of_mul_eq_one_right⟩)
  have hq : 2 ≤ Fintype.card F := Fintype.one_lt_card
  have hc1 : #{z : F | ¬z * z = 1} = Fintype.card F - 2 := by
    have h' : #{z : F | z * z = 1} + #{z : F | ¬z * z = 1} = #(Finset.univ : Finset F) :=
      Finset.card_filter_add_card_filter_not _
    rw [h1, Finset.card_univ] at h'
    omega
  have hc2 : #{z : F | ¬z * z = (ν⁻¹ : Fˣ)} = Fintype.card F := by
    have h' : #{z : F | z * z = (ν⁻¹ : Fˣ)} + #{z : F | ¬z * z = (ν⁻¹ : Fˣ)} =
        #(Finset.univ : Finset F) :=
      Finset.card_filter_add_card_filter_not _
    rw [hν', zero_add, Finset.card_univ] at h'
    exact h'
  rw [hcount, hcount, h1, hν', hc1, hc2] at hc
  refine natCard_hyperbolicForm_apply_zero_ne m (one_ne_zero : (1 : F) ≠ 0) ?_
  rcases Nat.exists_eq_add_of_le hq with ⟨r, hr⟩
  rw [hr, Nat.add_sub_cancel_left] at hc
  linarith

/-- **The isometry classes in odd dimension for odd `q`** (LMFDB `group.orthogonal`): for a
non-square `ν`, every nondegenerate form of dimension `2 m + 1` over `𝔽_q`, `q` odd, is isometric to
the parabolic form or to `ν` times it, and these are not isometric
(`QuadraticForm.not_equivalent_smul_parabolicForm`). -/
lemma equivalent_parabolicForm_or_equivalent_smul_parabolicForm (h2 : ringChar F ≠ 2)
    (hν : ¬IsSquare (ν : F)) (hQ : Q.Nondegenerate) (hV : finrank F V = 2 * m + 1) :
    Q.Equivalent (parabolicForm F m) ∨ Q.Equivalent (ν • parabolicForm F m) := by
  rcases exists_equivalent_smul_parabolicForm hQ hV with ⟨c, hc⟩
  have h : Q.Equivalent (c⁻¹ • parabolicForm F m) := by
    simpa using equivalent_smul c⁻¹ hc
  by_cases hs : IsSquare ((c⁻¹ : Fˣ) : F)
  · rcases hs with ⟨d, hd⟩
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact (c⁻¹).ne_zero (by rw [hd, mul_zero])
    refine .inl (h.trans ?_)
    simpa using equivalent_smul_of_eq_mul_mul (parabolicForm F m) (s := 1) (d := Units.mk0 d hd0)
      (by simpa using hd)
  · rcases isSquare_mul_of_not_isSquare h2 hs hν with ⟨s, hs'⟩
    have hs0 : s ≠ 0 := by
      rintro rfl
      exact mul_ne_zero (c⁻¹).ne_zero ν.ne_zero (by rw [hs', mul_zero])
    refine .inr (h.trans (equivalent_smul_of_eq_mul_mul (parabolicForm F m)
      (d := Units.mk0 (s / ν) (div_ne_zero hs0 ν.ne_zero)) ?_))
    simp only [Units.val_mk0]
    field_simp
    linear_combination hs'

end QuadraticForm
