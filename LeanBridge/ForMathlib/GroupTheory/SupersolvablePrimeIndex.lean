import LeanBridge.ForMathlib.GroupTheory.RankFrattini
import LeanBridge.ForMathlib.GroupTheory.SupersolvableClosure
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.RepresentationTheory.Maschke
import TauCeti.GroupTheory.Frattini
import TauCeti.RepresentationTheory.Subrepresentation

/-!
# Huppert's criterion: maximal subgroups of prime index

A finite group is supersolvable if and only if each of its maximal subgroups has prime index
(LMFDB `group.supersolvable`). That the maximal subgroups of a finite supersolvable group have
prime index is `Group.IsSupersolvable.index_prime_of_isCoatom`; this file proves the converse, due
to Huppert.

Let `G` be a finite group all of whose maximal subgroups have prime index; so do its quotients. Let
`p` be the largest prime dividing `|G|` and `P` a Sylow `p`-subgroup. If `P` were not normal, its
normalizer would lie in a maximal subgroup `M` of prime index `q`, and counting the Sylow
`p`-subgroups of `G` and of `M` would give `q ≡ 1 (mod p)`, so `q > p`. So `P` is normal; let `H`
be a complement (Schur–Zassenhaus). The group `H` acts by conjugation on the `𝔽_p`-vector space
`V = P / Φ(P)`, semisimply by Maschke's theorem since `|H|` is prime to `p`. A maximal
`H`-invariant subspace `W` of `V`, with preimage `W̃` in `P`, gives the maximal subgroup `W̃ H` of
`G`, of index `|V / W|`, which is therefore `p`. So the simple summands of `V` are lines, on which
`H` acts by scalars: commutators and `(p - 1)`-th powers of elements of `H` act trivially on `V`,
hence on `P` by Burnside's theorem (Tau Ceti's `IsPGroup.isPGroup_ker_mapQuotient_frattini`: the
automorphisms of a finite `p`-group acting trivially on its Frattini quotient form a `p`-group).
Then `H` acts on the elements of order `p` of the centre of `P` through commuting operators `f`
with `f ^ (p - 1) = 1`, which have a common eigenvector: a normal subgroup of `G` of order `p`,
whose quotient is supersolvable by induction.

## Main definitions

* `MulAut.toZModLinearMap`: the automorphisms of a commutative group `Q`, as `𝔽_p`-linear maps of
  `Additive Q`.

## Main results

* `Module.End.exists_ne_zero_apply_eq_smul_of_pow_eq_one`: an endomorphism `f` of a nonzero finite
  `𝔽_p`-vector space with `f ^ (p - 1) = 1` has an eigenvector.
* `Representation.exists_ne_zero_forall_apply_eq_smul`: if commutators and `(p - 1)`-th powers act
  trivially on a nonzero finite `𝔽_p`-vector space, there is a common eigenvector.
* `Representation.commutatorElement_eq_one_of_forall_isCoatom`,
  `Representation.pow_card_sub_one_eq_one_of_forall_isCoatom`: if a finite group `H` of order prime
  to `p` acts on a finite `𝔽_p`-vector space and every maximal subrepresentation has codimension
  one, then commutators and `(p - 1)`-th powers act trivially.
* `IsPGroup.commute_of_forall_conjNormal_eq`: Burnside's theorem, an element of order prime to `p`
  acting trivially on the Frattini quotient of a normal `p`-subgroup `P` centralizes `P`.
* `Group.index_prime_quotient_of_forall_isCoatom`: if every maximal subgroup has prime index, so
  does every maximal subgroup of a quotient.
* `Group.normal_sylow_of_forall_isCoatom_index_prime`: if every maximal subgroup has prime index,
  the Sylow subgroups for the largest prime are normal.
* `Group.relIndex_prime_of_forall_isCoatom`, `Group.card_eq_mul_card_of_isCoatom`: with a normal
  subgroup `P` and a complement `H`, a maximal proper `H`-invariant subgroup of `P` normalized by
  `P` has prime index in `P`; so for a `p`-group `P` the maximal subrepresentations of the
  Frattini quotient have index `p`.
* `Group.exists_ne_one_normal_zpowers_of_forall_commute`: a normal `p`-subgroup `P ≠ 1` with a
  complement whose commutators and `(p - 1)`-th powers centralize `P` contains a nontrivial cyclic
  normal subgroup.
* `Group.exists_ne_one_normal_zpowers_of_forall_isCoatom`: a finite group all of whose maximal
  subgroups have prime index has a nontrivial cyclic normal subgroup inside each normal Sylow
  subgroup `P ≠ 1`.
* `Group.isSupersolvable_of_forall_isCoatom_index_prime` (LMFDB `group.supersolvable`): Huppert's
  criterion, a finite group all of whose maximal subgroups have prime index is supersolvable.
* `Group.isSupersolvable_iff_forall_isCoatom_index_prime` (LMFDB `group.supersolvable`): a finite
  group is supersolvable if and only if each of its maximal subgroups has prime index.

## References

* B. Huppert, *Normalteiler und maximale Untergruppen endlicher Gruppen*, Math. Z. 60 (1954),
  409–434.
-/

open Function Group Module Polynomial Subgroup

open scoped commutatorElement

namespace Subrepresentation

variable {k G V : Type*} [Ring k] [Monoid G] [AddCommGroup V] [Module k V]
  {ρ : Representation k G V}

instance : IsModularLattice (Subrepresentation ρ) :=
  ⟨fun y _ h ↦ IsModularLattice.sup_inf_le_assoc_of_le (α := Submodule k V) y.toSubmodule h⟩

instance [Finite V] : Finite (Subrepresentation ρ) :=
  Finite.of_injective _ (SetLike.coe_injective (A := Subrepresentation ρ))

end Subrepresentation

/-- An automorphism of a commutative group `Q`, as an `𝔽_p`-linear map of `Additive Q`. -/
def MulAut.toZModLinearMap (p : ℕ) (Q : Type*) [CommGroup Q] [Module (ZMod p) (Additive Q)] :
    MulAut Q →* (Additive Q →ₗ[ZMod p] Additive Q) where
  toFun α := (MonoidHom.toAdditive α.toMonoidHom).toZModLinearMap p
  map_one' := rfl
  map_mul' _ _ := rfl

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace Module.End

variable {W : Type*} [AddCommGroup W] [Module (ZMod p) W] [Finite W] [Nontrivial W]

/-- **An endomorphism `f` of a nonzero finite `𝔽_p`-vector space with `f ^ (p - 1) = 1` has an
eigenvector**: its minimal polynomial divides `X ^ p - X`, which splits over `𝔽_p`. -/
lemma exists_ne_zero_apply_eq_smul_of_pow_eq_one {f : End (ZMod p) W} (hf : f ^ (p - 1) = 1) :
    ∃ μ : ZMod p, ∃ w : W, w ≠ 0 ∧ f w = μ • w := by
  have : Module.Finite (ZMod p) W := .of_finite
  have hint : IsIntegral (ZMod p) f := .of_finite (ZMod p) f
  have hp : aeval f (X ^ p - X : (ZMod p)[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, ← pow_sub_one_mul (Fact.out : p.Prime).ne_zero, hf, one_mul,
      sub_self]
  have hspl : (X ^ p - X : (ZMod p)[X]).Splits := by
    simpa using FiniteField.splits_X_pow_card_sub_X p (K := ZMod p)
  have hmin : (minpoly (ZMod p) f).Splits :=
    hspl.of_dvd (FiniteField.X_pow_card_sub_X_ne_zero _ (Fact.out : p.Prime).one_lt)
      (minpoly.dvd _ _ hp)
  rcases hmin.exists_eval_eq_zero (by
    rw [degree_eq_natDegree (minpoly.ne_zero hint)]
    exact_mod_cast (minpoly.natDegree_pos hint).ne') with ⟨μ, hμ⟩
  rcases (hasEigenvalue_of_isRoot hμ).exists_hasEigenvector with ⟨w, hw⟩
  exact ⟨μ, w, hw.2, hw.apply_eq_smul⟩

end Module.End

namespace Representation

variable {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod p) V] [Finite V]
  (ρ : Representation (ZMod p) H V)

lemma exists_smul_eq_of_card_eq {L : Subrepresentation ρ} (hL : Nat.card L = p) {v : V} (hv : v ∈ L)
    (hv0 : v ≠ 0) (h : H) : ∃ μ : ZMod p, ρ h v = μ • v := by
  have hinj : Injective fun μ : ZMod p ↦ (⟨μ • v, L.toSubmodule.smul_mem μ hv⟩ : L) :=
    fun μ ν hμν ↦ smul_left_injective (ZMod p) hv0 (congrArg Subtype.val hμν)
  rcases (hinj.bijective_of_nat_card_le (by rw [hL, Nat.card_zmod])).2
    ⟨ρ h v, L.apply_mem_toSubmodule h hv⟩ with ⟨μ, hμ⟩
  exact ⟨μ, (congrArg Subtype.val hμ).symm⟩

/-- **A common eigenvector**: if commutators and `(p - 1)`-th powers act trivially on a nonzero
finite `𝔽_p`-representation, then some nonzero vector is an eigenvector of every element. Each
element acts on a minimal subrepresentation `L` with an eigenvalue, whose eigenspace in `L` is a
subrepresentation, hence all of `L`. -/
lemma exists_ne_zero_forall_apply_eq_smul [Nontrivial V] (hcomm : ∀ a b : H, ρ ⁅a, b⁆ = 1)
    (hpow : ∀ a : H, ρ (a ^ (p - 1)) = 1) :
    ∃ v : V, v ≠ 0 ∧ ∀ h : H, ∃ μ : ZMod p, ρ h v = μ • v := by
  have hρc (g h : H) (v : V) : ρ g (ρ h v) = ρ h (ρ g v) := by
    rw [← End.mul_apply, ← map_mul, show g * h = ⁅g, h⁆ * (h * g) by group, map_mul, hcomm,
      one_mul, map_mul, End.mul_apply]
  rcases (eq_bot_or_exists_atom_le (⊤ : Subrepresentation ρ)).resolve_left top_ne_bot
    with ⟨L, hL, -⟩
  have hL0 : L.toSubmodule ≠ ⊥ := fun h ↦ hL.1 (Subrepresentation.toSubmodule_injective h)
  rcases Submodule.exists_mem_ne_zero_of_ne_bot hL0 with ⟨v, hvL, hv0⟩
  refine ⟨v, hv0, fun h ↦ ?_⟩
  have : Nontrivial L.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hL0
  rcases End.exists_ne_zero_apply_eq_smul_of_pow_eq_one (f := (ρ h).restrict fun w hw ↦
    L.apply_mem_toSubmodule h hw) (by
      rw [End.pow_restrict]
      ext w
      simp [← map_pow, hpow]) with ⟨μ, w, hw0, hw⟩
  let E : Subrepresentation ρ :=
    ⟨L.toSubmodule ⊓ End.eigenspace (ρ h) μ, fun g x hx ↦ by
      rw [Submodule.mem_inf, End.mem_eigenspace_iff] at hx ⊢
      exact ⟨L.apply_mem_toSubmodule g hx.1, by rw [hρc, hx.2, map_smul]⟩⟩
  have hEL : E ≤ L := fun x hx ↦ (Submodule.mem_inf.mp hx).1
  have hE : E = L := (hL.le_iff.mp hEL).resolve_left fun hE ↦ hw0 <| Subtype.ext <|
    (congrArg (fun σ : Subrepresentation ρ ↦ (w : V) ∈ σ) hE).mp
      (Submodule.mem_inf.mpr ⟨w.2, End.mem_eigenspace_iff.mpr (congrArg Subtype.val hw)⟩)
  exact ⟨μ, End.mem_eigenspace_iff.mp (Submodule.mem_inf.mp (hE ▸ hvL : v ∈ E)).2⟩

variable [Finite H] [NeZero (Nat.card H : ZMod p)]

lemma card_eq_of_isAtom (hρ : ∀ σ : Subrepresentation ρ, IsCoatom σ → Nat.card V = p * Nat.card σ)
    {L : Subrepresentation ρ} (hL : IsAtom L) : Nat.card L = p := by
  rcases exists_isCompl L with ⟨C, hLC⟩
  have hcard : Nat.card V = Nat.card L * Nat.card C :=
    (Nat.card_congr (Submodule.prodEquivOfIsCompl _ _
      (Subrepresentation.isCompl_toSubmodule.mpr hLC)).toEquiv).symm.trans (Nat.card_prod _ _)
  have : Nonempty C := ⟨⟨0, C.toSubmodule.zero_mem⟩⟩
  rw [hρ C (hLC.isAtom_iff_isCoatom.mp hL)] at hcard
  exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos hcard).symm

lemma apply_eq_self_of_forall_isCoatom
    (hρ : ∀ σ : Subrepresentation ρ, IsCoatom σ → Nat.card V = p * Nat.card σ) {x : H}
    (hx : (∃ a b : H, ⁅a, b⁆ = x) ∨ ∃ a : H, a ^ (p - 1) = x) (v : V) : ρ x v = v := by
  let D : Set H := {x | (∃ a b : H, ⁅a, b⁆ = x) ∨ ∃ a : H, a ^ (p - 1) = x}
  have hD (g : H) {x : H} (hx : x ∈ D) : g⁻¹ * x * g ∈ D := by
    rcases hx with ⟨a, b, rfl⟩ | ⟨a, rfl⟩
    · exact .inl ⟨g⁻¹ * a * g, g⁻¹ * b * g, by simp only [commutatorElement_def]; group⟩
    · exact .inr ⟨g⁻¹ * a * g, by simpa only [inv_inv] using conj_pow (a := g⁻¹) (b := a)⟩
  let U : Subrepresentation ρ :=
    { toSubmodule :=
        { carrier := {v | ∀ x ∈ D, ρ x v = v}
          add_mem' := fun hv hw x hx ↦ by rw [map_add, hv x hx, hw x hx]
          zero_mem' := fun x _ ↦ map_zero _
          smul_mem' := fun c v hv x hx ↦ by rw [map_smul, hv x hx] }
      apply_mem_toSubmodule := fun g v hv x hx ↦ by
        have h : ρ g (ρ (g⁻¹ * x * g) v) = ρ g v := congrArg (ρ g) (hv _ (hD g hx))
        rwa [map_mul, map_mul, End.mul_apply, End.mul_apply, ← End.mul_apply, ← map_mul,
          mul_inv_cancel, map_one, End.one_apply] at h }
  suffices hU : U = ⊤ from hU.ge (Set.mem_univ v) x hx
  by_contra hU
  rcases exists_isCompl U with ⟨C, hUC⟩
  rcases (eq_bot_or_exists_atom_le C).resolve_left (fun h ↦ hU (by simpa [h] using hUC.sup_eq_top))
    with ⟨L, hL, hLC⟩
  rcases Submodule.exists_mem_ne_zero_of_ne_bot (p := L.toSubmodule) fun h ↦
    hL.1 (Subrepresentation.toSubmodule_injective h) with ⟨w, hwL, hw0⟩
  choose χ hχ using exists_smul_eq_of_card_eq ρ (card_eq_of_isAtom ρ hρ hL) hwL hw0
  have hχmul (g h : H) : χ (g * h) = χ g * χ h := by
    refine smul_left_injective (ZMod p) hw0 ?_
    simp only
    rw [← hχ, map_mul, End.mul_apply, hχ, map_smul, hχ, smul_smul, mul_comm]
  have hχone : χ 1 = 1 := by
    refine smul_left_injective (ZMod p) hw0 ?_
    simp only
    rw [← hχ, map_one, End.one_apply, one_smul]
  let χ' : H →* ZMod p := ⟨⟨χ, hχone⟩, hχmul⟩
  have hwU : w ∈ U := by
    rintro x (⟨a, b, rfl⟩ | ⟨a, rfl⟩)
    · rw [hχ, show χ ⁅a, b⁆ = 1 from congrArg Units.val <|
        (map_commutatorElement χ'.toHomUnits a b).trans (commutatorElement_eq_one_iff_mul_comm.mpr
          (mul_comm _ _)), one_smul]
    · rw [hχ, show χ (a ^ (p - 1)) = 1 from congrArg Units.val <|
        (map_pow χ'.toHomUnits a (p - 1)).trans (ZMod.units_pow_card_sub_one_eq_one p _), one_smul]
  have hw : w ∈ U ⊓ C := ⟨hwU, hLC hwL⟩
  rw [hUC.inf_eq_bot] at hw
  exact hw0 hw

/-- **Commutators act trivially** on a finite `𝔽_p`-representation of a finite group of order
prime to `p` in which every maximal subrepresentation has codimension one: by Maschke's theorem
the minimal subrepresentations are lines, on which the group acts by scalars. -/
lemma commutatorElement_eq_one_of_forall_isCoatom
    (hρ : ∀ σ : Subrepresentation ρ, IsCoatom σ → Nat.card V = p * Nat.card σ) (a b : H) :
    ρ ⁅a, b⁆ = 1 :=
  LinearMap.ext <| apply_eq_self_of_forall_isCoatom ρ hρ (.inl ⟨a, b, rfl⟩)

/-- **`(p - 1)`-th powers act trivially** on a finite `𝔽_p`-representation of a finite group of
order prime to `p` in which every maximal subrepresentation has codimension one. -/
lemma pow_card_sub_one_eq_one_of_forall_isCoatom
    (hρ : ∀ σ : Subrepresentation ρ, IsCoatom σ → Nat.card V = p * Nat.card σ) (a : H) :
    ρ (a ^ (p - 1)) = 1 :=
  LinearMap.ext <| apply_eq_self_of_forall_isCoatom ρ hρ (.inr ⟨a, rfl⟩)

end Representation

namespace Subgroup

variable {S T K : Subgroup G}

lemma normal_of_sup_eq_top (hST : S ⊔ T = ⊤) (hS : ∀ g ∈ S, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hT : ∀ g ∈ T, ∀ k ∈ K, g * k * g⁻¹ ∈ K) : K.Normal :=
  normalizer_eq_top_iff.mp <| top_le_iff.mp <| hST ▸ sup_le (le_normalizer_iff.mpr hS)
    (le_normalizer_iff.mpr hT)

end Subgroup

namespace IsPGroup

variable [Finite G] {P : Subgroup G} [P.Normal]

/-- **Burnside's theorem**: an element `x` of order prime to `p` that acts trivially on the
Frattini quotient of a normal `p`-subgroup `P` centralizes `P`. The automorphisms of `P` acting
trivially on `P / Φ(P)` form a `p`-group (Tau Ceti), containing the conjugation by `x`, whose
order divides that of `x`. -/
lemma commute_of_forall_conjNormal_eq (hP : IsPGroup p P) {x : G} (hx : (orderOf x).Coprime p)
    (hxP : ∀ y : P, (MulAut.conjNormal x y : P ⧸ frattini P) = y) {y : G} (hy : y ∈ P) :
    Commute x y := by
  have hker : MulAut.conjNormal x ∈ (MulAut.mapQuotient (frattini P)).ker :=
    (MulAut.mem_ker_mapQuotient_iff _).mpr hxP
  rcases IsPGroup.iff_card.mp (hP.isPGroup_ker_mapQuotient_frattini.to_le (zpowers_le.mpr hker))
    with ⟨n, hn⟩
  rw [Nat.card_zpowers] at hn
  have hcop : (p ^ n).Coprime p := hn ▸ hx.coprime_dvd_left (orderOf_map_dvd _ x)
  have h1 : (MulAut.conjNormal x : MulAut P) = 1 := by
    rcases n with _ | n
    · exact orderOf_eq_one_iff.mp (by simpa using hn)
    · exact absurd (dvd_refl p) <| (Fact.out : p.Prime).coprime_iff_not_dvd.mp <|
        hcop.coprime_dvd_left <| dvd_pow_self p n.succ_ne_zero
  have h : ((MulAut.conjNormal x : MulAut P) ⟨y, hy⟩ : G) = ((1 : MulAut P) ⟨y, hy⟩ : G) :=
    congrArg (fun α : MulAut P ↦ (α ⟨y, hy⟩ : G)) h1
  simp only [MulAut.conjNormal_apply] at h
  exact mul_inv_eq_iff_eq_mul.mp h

end IsPGroup

namespace Group

/-- **If every maximal subgroup of `G` has prime index, so does every maximal subgroup of a
quotient of `G`**, its preimage in `G` being maximal of the same index. -/
lemma index_prime_quotient_of_forall_isCoatom (hG : ∀ M : Subgroup G, IsCoatom M → M.index.Prime)
    (N : Subgroup G) [N.Normal] {M : Subgroup (G ⧸ N)} (hM : IsCoatom M) : M.index.Prime :=
  have hN : Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  index_comap_of_surjective M hN ▸ hG _ (isCoatom_comap_of_surjective hN hM)

variable [Finite G]

/-- **If every maximal subgroup has prime index, the Sylow subgroups for the largest prime are
normal**: otherwise the normalizer of a Sylow `p`-subgroup `P` lies in a maximal subgroup `M` of
prime index `q`, and the numbers of Sylow `p`-subgroups of `G` and of `M`, both `≡ 1 (mod p)`,
differ by the factor `q`, so that `q ≡ 1 (mod p)` and `q > p`. -/
lemma normal_sylow_of_forall_isCoatom_index_prime
    (hG : ∀ M : Subgroup G, IsCoatom M → M.index.Prime)
    (hp : ∀ q : ℕ, q.Prime → q ∣ Nat.card G → q ≤ p) (P : Sylow p G) : (P : Subgroup G).Normal := by
  rcases eq_top_or_exists_le_coatom (normalizer (P : Set G)) with h | ⟨M, hM, hPM⟩
  · exact normalizer_eq_top_iff.mp h
  exfalso
  have hq : M.index.Prime := hG M hM
  have h1 : Nat.card (Sylow p G) = (normalizer (P : Set G)).relIndex M * M.index := by
    rw [P.card_eq_index_normalizer, relIndex_mul_index hPM]
  have h2 : Nat.card (Sylow p M) = (normalizer (P : Set G)).relIndex M :=
    (P.subtype (le_normalizer.trans hPM)).card_eq_index_normalizer.trans <| congrArg index
      (subgroupOf_normalizer_eq (le_normalizer.trans hPM)).symm
  have hmod : M.index ≡ 1 [MOD p] := by
    have hG' : Nat.card (Sylow p G) ≡ 1 [MOD p] := card_sylow_modEq_one p G
    rw [h1, ← h2] at hG'
    exact (one_mul M.index ▸ ((card_sylow_modEq_one p M).mul_right M.index).symm).trans hG'
  have hdvd : p ∣ M.index - 1 := (Nat.modEq_iff_dvd' hq.one_lt.le).mp hmod.symm
  have hle : M.index ≤ p := hp _ hq M.index_dvd_card
  have h2le : 2 ≤ M.index := hq.two_le
  have hp1 : p ≤ M.index - 1 := Nat.le_of_dvd (by omega) hdvd
  omega

variable {P H : Subgroup G} [P.Normal]

/-- **The maximal `H`-invariant subgroups below a normal subgroup `P` with complement `H` have
prime index** when every maximal subgroup of `G` has prime index: if `W ≤ P` is normalized by `P`
and `H` and maximal among the proper subgroups of `P` normalized by `H`, then `W H` is a maximal
subgroup of `G` of index `[P : W]`. -/
lemma relIndex_prime_of_forall_isCoatom (hG : ∀ M : Subgroup G, IsCoatom M → M.index.Prime)
    {W : Subgroup G} (hPH : P.IsComplement' H) (hWP : W ≤ P)
    (hPW : ∀ x ∈ P, ∀ w ∈ W, x * w * x⁻¹ ∈ W) (hHW : ∀ h ∈ H, ∀ w ∈ W, h * w * h⁻¹ ∈ W)
    (hW : ¬P ≤ W)
    (hmax : ∀ K : Subgroup G, W ≤ K → K ≤ P → (∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) → K = W ∨ K = P) :
    (W.relIndex P).Prime := by
  have : W.Normal := normal_of_sup_eq_top hPH.sup_eq_top hPW hHW
  have hidx : (W ⊔ H).index = W.relIndex P := by
    have h1 : W.relIndex (W ⊔ H) * (W ⊔ H).index = W.relIndex P * P.index := by
      rw [relIndex_mul_index le_sup_left, relIndex_mul_index hWP]
    have h2 : W.relIndex (W ⊔ H) = Nat.card H := by
      rw [relIndex_sup_left, ← inf_relIndex_right, show W ⊓ H = ⊥ from
        eq_bot_iff.mpr ((inf_le_inf_right H hWP).trans hPH.disjoint.le_bot), relIndex_bot_left]
    rw [h2, hPH.symm.index_eq_card, mul_comm] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  rw [← hidx]
  refine hG _ ⟨fun htop ↦ hW ?_, fun K hK ↦ ?_⟩
  · rwa [htop, index_top, eq_comm, relIndex_eq_one] at hidx
  have hHK : H ≤ K := le_sup_right.trans hK.le
  rcases hmax (K ⊓ P) (le_inf (le_sup_left.trans hK.le) hWP) inf_le_right fun h hh k hk ↦
      mem_inf.mpr ⟨mul_mem (mul_mem (hHK hh) (mem_inf.mp hk).1) (inv_mem (hHK hh)),
        ‹P.Normal›.conj_mem k (mem_inf.mp hk).2 h⟩ with h | h
  · refine absurd (fun k hk ↦ ?_ : K ≤ W ⊔ H) hK.not_ge
    have hk' : k ∈ ((H ⊔ P : Subgroup G) : Set G) := by
      rw [sup_comm, hPH.sup_eq_top]
      exact mem_top k
    rw [mul_normal] at hk'
    rcases hk' with ⟨g, hg, y, hy, rfl⟩
    have hyK : y ∈ K := by simpa using mul_mem (inv_mem (hHK hg)) hk
    exact mul_mem (mem_sup_right hg) (mem_sup_left (h ▸ ⟨hyK, hy⟩ : y ∈ W))
  · rw [eq_top_iff, ← hPH.sup_eq_top]
    exact sup_le (h ▸ inf_le_left : P ≤ K) hHK

/-- **The maximal subrepresentations of the Frattini quotient have index `p`**: let every maximal
subgroup of `G` have prime index, `P` be a normal `p`-subgroup with a complement `H`, and
`π : P → Q` a surjection onto a commutative group with an `𝔽_p`-structure, on which `H` acts
compatibly by conjugation. Then every maximal subrepresentation of `Q` has index `p`: its preimage
`W` in `P` gives the maximal subgroup `W H`. -/
lemma card_eq_mul_card_of_isCoatom (hG : ∀ M : Subgroup G, IsCoatom M → M.index.Prime)
    (hPH : P.IsComplement' H) (hP : IsPGroup p P) {Q : Type*} [CommGroup Q]
    [Module (ZMod p) (Additive Q)] {π : P →* Q} (hπ : Surjective π)
    {ρ : Representation (ZMod p) H (Additive Q)}
    (hρ : ∀ (h : H) (y : P), ρ h (.ofMul (π y)) = .ofMul (π (MulAut.conjNormal (h : G) y)))
    {σ : Subrepresentation ρ} (hσ : IsCoatom σ) : Nat.card (Additive Q) = p * Nat.card σ := by
  let T : Subgroup Q := toAddSubgroup.symm σ.toSubmodule.toAddSubgroup
  let W : Subgroup G := (T.comap π).map P.subtype
  have hW (y : P) : (y : G) ∈ W ↔ Additive.ofMul (π y) ∈ σ :=
    ⟨by rintro ⟨z, hz, hzy⟩; rwa [← Subtype.ext hzy], fun hy ↦ ⟨y, hy, rfl⟩⟩
  have hPW (x : G) (hx : x ∈ P) (w : G) (hw : w ∈ W) : x * w * x⁻¹ ∈ W := by
    rcases hw with ⟨y, hy, rfl⟩
    refine (hW (⟨x, hx⟩ * y * ⟨x, hx⟩⁻¹)).mpr ?_
    rwa [show π (⟨x, hx⟩ * y * ⟨x, hx⟩⁻¹) = π y by
      rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]]
  have hHW (h : G) (hh : h ∈ H) (w : G) (hw : w ∈ W) : h * w * h⁻¹ ∈ W := by
    rcases hw with ⟨y, hy, rfl⟩
    have h' : ((MulAut.conjNormal h y : P) : G) ∈ W :=
      (hW (MulAut.conjNormal h y)).mpr <| (hρ ⟨h, hh⟩ y) ▸ σ.apply_mem_toSubmodule _ hy
    rwa [MulAut.conjNormal_apply] at h'
  have hnot : ¬P ≤ W := fun hPW' ↦ hσ.1 <| eq_top_iff.mpr fun v _ ↦ by
    rcases hπ (Additive.toMul v) with ⟨y, hy⟩
    have h' : Additive.ofMul (π y) ∈ σ := (hW y).mp (hPW' y.2)
    rwa [hy, ofMul_toMul] at h'
  have hmax (K : Subgroup G) (hWK : W ≤ K) (hKP : K ≤ P) (hHK : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) :
      K = W ∨ K = P := by
    let τ : Subrepresentation ρ :=
      ⟨AddSubgroup.toZModSubmodule p (toAddSubgroup ((K.subgroupOf P).map π)), fun h v hv ↦ by
        rcases hv with ⟨y, hy, hyv⟩
        refine ⟨MulAut.conjNormal (h : G) y, mem_subgroupOf.mpr ?_, ?_⟩
        · rw [MulAut.conjNormal_apply]
          exact hHK h h.2 y hy
        · rw [← ofMul_toMul v, ← hyv, hρ, toMul_ofMul]⟩
    have hστ : σ ≤ τ := fun v hv ↦ by
      rcases hπ (Additive.toMul v) with ⟨y, hy⟩
      refine ⟨y, hWK ((hW y).mpr ?_), hy⟩
      rwa [hy, ofMul_toMul]
    rcases hσ.le_iff.mp hστ with hτ | hτ
    · refine .inr (le_antisymm hKP fun x hx ↦ ?_)
      rcases (hτ.ge (Set.mem_univ (Additive.ofMul (π ⟨x, hx⟩))) :
        Additive.ofMul (π ⟨x, hx⟩) ∈ τ) with ⟨y, hy, hyx⟩
      have h1 : ((y⁻¹ * ⟨x, hx⟩ : P) : G) ∈ W := (hW _).mpr <| by
        rw [map_mul, map_inv, hyx, toMul_ofMul, inv_mul_cancel, ofMul_one]
        exact σ.toSubmodule.zero_mem
      simpa using mul_mem (mem_subgroupOf.mp hy) (hWK h1)
    · refine .inl (le_antisymm (fun k hk ↦ (hW ⟨k, hKP hk⟩).mpr ?_) hWK)
      exact hτ ▸ (⟨⟨k, hKP hk⟩, hk, rfl⟩ : Additive.ofMul (π ⟨k, hKP hk⟩) ∈ τ)
  have hprime : (W.relIndex P).Prime :=
    relIndex_prime_of_forall_isCoatom hG hPH (map_subtype_le _) hPW hHW hnot hmax
  have hidx : W.relIndex P = σ.toSubmodule.toAddSubgroup.index := by
    rw [relIndex, show W.subgroupOf P = T.comap π from
      comap_map_eq_self_of_injective P.subtype_injective _, index_comap_of_surjective _ hπ,
      ← index_toAddSubgroup, OrderIso.apply_symm_apply]
  rcases IsPGroup.iff_card.mp hP with ⟨n, hn⟩
  have hp : W.relIndex P = p := (Nat.prime_dvd_prime_iff_eq hprime Fact.out).mp <|
    hprime.dvd_of_dvd_pow (hn ▸ relIndex_dvd_card W P)
  rw [← AddSubgroup.index_mul_card σ.toSubmodule.toAddSubgroup, ← hidx, hp]
  rfl

/-- **A nontrivial cyclic normal subgroup from a coprime action**: let `P` be a normal `p`-subgroup
with a complement `H` such that commutators and `(p - 1)`-th powers of elements of `H` centralize
`P`. Then `P` contains a nontrivial cyclic normal subgroup of `G`: `H` acts on the elements of
order `p` of the centre of `P` with a common eigenvector. -/
lemma exists_ne_one_normal_zpowers_of_forall_commute (hP : IsPGroup p P) (hP1 : P ≠ ⊥)
    (hPH : P.IsComplement' H) (hcomm : ∀ a ∈ H, ∀ b ∈ H, ∀ y ∈ P, Commute ⁅a, b⁆ y)
    (hpow : ∀ a ∈ H, ∀ y ∈ P, Commute (a ^ (p - 1)) y) : ∃ c ∈ P, c ≠ 1 ∧ (zpowers c).Normal := by
  let A : Subgroup G :=
    { carrier := {x | x ∈ P ∧ (∀ y ∈ P, Commute x y) ∧ x ^ p = 1}
      mul_mem' := fun {x y} hx hy ↦ ⟨mul_mem hx.1 hy.1,
        fun z hz ↦ (hx.2.1 z hz).mul_left (hy.2.1 z hz),
        by rw [(hx.2.1 y hy.1).mul_pow, hx.2.2, hy.2.2, one_mul]⟩
      one_mem' := ⟨one_mem P, fun z _ ↦ Commute.one_left z, one_pow p⟩
      inv_mem' := fun {x} hx ↦ ⟨inv_mem hx.1, fun z hz ↦ (hx.2.1 z hz).inv_left, by
        rw [inv_pow, hx.2.2, inv_one]⟩ }
  have hA : A.Normal := by
    refine ⟨fun x hx g ↦ ⟨‹P.Normal›.conj_mem x hx.1 g, fun y hy ↦ ?_, ?_⟩⟩
    · have hy' : g⁻¹ * y * g ∈ P := by simpa using ‹P.Normal›.conj_mem y hy g⁻¹
      simpa [mul_assoc] using (hx.2.1 _ hy').map (MulAut.conj g)
    · rw [conj_pow, hx.2.2, mul_one, mul_inv_cancel]
  have : Nontrivial P := (nontrivial_iff_ne_bot P).mpr hP1
  have : Nontrivial (center P) := hP.center_nontrivial
  rcases IsPGroup.iff_card.mp (hP.to_subgroup (center P)) with ⟨k, hk⟩
  have hpk : p ∣ Nat.card (center P) := by
    rcases k with _ | k
    · exact absurd (hk.trans (pow_zero p)) Finite.one_lt_card.ne'
    · exact hk ▸ dvd_pow_self p k.succ_ne_zero
  let _ : CommGroup A :=
    { (inferInstance : Group A) with mul_comm := fun x y ↦ Subtype.ext (x.2.2.1 y y.2.1).eq }
  have hpA (x : Additive A) : p • x = 0 := by
    rw [← ofMul_toMul x, ← ofMul_pow, show Additive.toMul x ^ p = 1 from
      Subtype.ext (Additive.toMul x).2.2.2, ofMul_one]
  let _ : Module (ZMod p) (Additive A) := { AddCommGroup.zmodModule hpA with }
  let ρ : Representation (ZMod p) H (Additive A) :=
    (MulAut.toZModLinearMap p A).comp ((MulAut.conjNormal (H := A)).comp H.subtype)
  have hconj (g : H) (v : Additive A) :
      ((Additive.toMul (ρ g v) : A) : G) = g * (Additive.toMul v : A) * (g : G)⁻¹ :=
    MulAut.conjNormal_apply _ _
  have hρ1 {x : H} (hx : ∀ y ∈ P, Commute (x : G) y) : ρ x = 1 :=
    LinearMap.ext fun v ↦ Additive.toMul.injective <| Subtype.ext <|
      (hconj x v).trans (hx _ (Additive.toMul v).2.1).mul_inv_cancel
  have : Nontrivial (Additive A) := by
    rcases exists_prime_orderOf_dvd_card' p hpk with ⟨z, hz⟩
    refine ⟨⟨Additive.ofMul ⟨z, (z : P).2, fun y hy ↦ ?_, ?_⟩, 0, fun h ↦ ?_⟩⟩
    · exact congrArg Subtype.val (mem_center_iff.mp z.2 ⟨y, hy⟩).symm
    · exact congrArg (fun z : center P ↦ ((z : P) : G)) (hz ▸ pow_orderOf_eq_one z)
    · refine (Fact.out : p.Prime).one_lt.ne' (hz ▸ orderOf_eq_one_iff.mpr (Subtype.ext ?_))
      exact Subtype.ext (congrArg (fun v ↦ ((Additive.toMul v : A) : G)) h)
  rcases ρ.exists_ne_zero_forall_apply_eq_smul (fun a b ↦ hρ1 (hcomm a a.2 b b.2))
    (fun a ↦ hρ1 (hpow a a.2)) with ⟨w, hw0, hw⟩
  refine ⟨(Additive.toMul w : A), (Additive.toMul w).2.1,
    fun h ↦ hw0 (Additive.toMul.injective (Subtype.ext h)),
    normal_of_sup_eq_top hPH.sup_eq_top (fun y hy k hk ↦ ?_) (fun h hh k hk ↦ ?_)⟩
  · rcases mem_zpowers_iff.mp hk with ⟨j, rfl⟩
    rw [(((Additive.toMul w).2.2.1 y hy).symm.zpow_right j).mul_inv_cancel]
    exact zpow_mem (mem_zpowers _) j
  · rcases hw ⟨h, hh⟩ with ⟨μ, hμ⟩
    rcases mem_zpowers_iff.mp hk with ⟨j, rfl⟩
    have hc : h * (Additive.toMul w : A) * h⁻¹ = ((Additive.toMul w : A) : G) ^ μ.val := by
      have h' : ((Additive.toMul (ρ ⟨h, hh⟩ w) : A) : G) = ((Additive.toMul (μ • w) : A) : G) :=
        congrArg (fun v ↦ ((Additive.toMul v : A) : G)) hμ
      rw [← ZMod.natCast_zmod_val μ, Nat.cast_smul_eq_nsmul, toMul_nsmul] at h'
      exact (hconj ⟨h, hh⟩ w).symm.trans h'
    rw [← conj_zpow, hc, ← zpow_natCast, ← zpow_mul]
    exact zpow_mem (mem_zpowers _) _

/-- **A finite group all of whose maximal subgroups have prime index has a nontrivial cyclic
normal subgroup inside each normal Sylow subgroup** `P ≠ 1`. With a complement `H`
(Schur–Zassenhaus), every maximal subrepresentation of the Frattini quotient `P / Φ(P)` has index
`p`; so commutators and `(p - 1)`-th powers of elements of `H` act trivially on it (Maschke), hence
on `P` (Burnside), and then `H` has a common eigenvector on the elements of order `p` of the
centre of `P`. -/
lemma exists_ne_one_normal_zpowers_of_forall_isCoatom
    (hG : ∀ M : Subgroup G, IsCoatom M → M.index.Prime) (hP : IsPGroup p P)
    (hPc : (Nat.card P).Coprime P.index) (hP1 : P ≠ ⊥) : ∃ c ∈ P, c ≠ 1 ∧ (zpowers c).Normal := by
  rcases exists_right_complement'_of_coprime hPc with ⟨H, hPH⟩
  have hpP : p ∣ Nat.card P := by
    rcases IsPGroup.iff_card.mp hP with ⟨n, hn⟩
    rcases n with _ | n
    · exact absurd (hn.trans (pow_zero p)) ((one_lt_card_iff_ne_bot P).mpr hP1).ne'
    · exact hn ▸ dvd_pow_self p n.succ_ne_zero
  have hHp : (Nat.card H).Coprime p := by
    rw [← hPH.symm.index_eq_card]
    exact (hPc.coprime_dvd_left hpP).symm
  have hord (x : H) : (orderOf (x : G)).Coprime p := by
    rw [orderOf_coe]
    exact hHp.coprime_dvd_left (orderOf_dvd_natCard x)
  have : NeZero (Nat.card H : ZMod p) :=
    ⟨(ZMod.natCast_eq_zero_iff _ p).not.mpr ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hHp.symm)⟩
  let _ : CommGroup (P ⧸ frattini P) := hP.frattiniQuotientCommGroup
  let _ : Module (ZMod p) (Additive (P ⧸ frattini P)) := { hP.frattiniQuotientModule with }
  let ρ : Representation (ZMod p) H (Additive (P ⧸ frattini P)) :=
    (MulAut.toZModLinearMap p _).comp ((MulAut.mapQuotient (frattini P)).comp
      (MulAut.conjNormal.comp H.subtype))
  have hρ (h : H) (y : P) : ρ h (Additive.ofMul (QuotientGroup.mk' (frattini P) y)) =
      Additive.ofMul (QuotientGroup.mk' (frattini P) (MulAut.conjNormal (h : G) y)) :=
    congrArg Additive.ofMul (MulAut.mapQuotient_mk (frattini P) _ y)
  have hcoat (σ : Subrepresentation ρ) (hσ : IsCoatom σ) :
      Nat.card (Additive (P ⧸ frattini P)) = p * Nat.card σ :=
    card_eq_mul_card_of_isCoatom hG hPH hP (QuotientGroup.mk'_surjective _) hρ hσ
  have hV (x : H) (hx : ρ x = 1) (y : P) : (MulAut.conjNormal (x : G) y : P ⧸ frattini P) = y :=
    Additive.ofMul.injective <| (hρ x y).symm.trans <| by rw [hx]; rfl
  refine exists_ne_one_normal_zpowers_of_forall_commute hP hP1 hPH (fun a ha b hb y hy ↦ ?_)
    fun a ha y hy ↦ ?_
  · exact hP.commute_of_forall_conjNormal_eq (hord ⁅⟨a, ha⟩, ⟨b, hb⟩⁆)
      (hV _ (ρ.commutatorElement_eq_one_of_forall_isCoatom hcoat _ _)) hy
  · exact hP.commute_of_forall_conjNormal_eq (hord (⟨a, ha⟩ ^ (p - 1)))
      (hV _ (ρ.pow_card_sub_one_eq_one_of_forall_isCoatom hcoat _)) hy

/-- **Huppert's criterion** (LMFDB `group.supersolvable`): a finite group all of whose maximal
subgroups have prime index is supersolvable. For the largest prime `p` dividing `|G|` the Sylow
`p`-subgroup is normal and contains a normal subgroup of order `p` (above); the quotient by it has
the same property, so it is supersolvable by induction, and so is `G`. -/
lemma isSupersolvable_of_forall_isCoatom_index_prime
    (hG : ∀ M : Subgroup G, IsCoatom M → M.index.Prime) : IsSupersolvable G := by
  rcases (⟨_, rfl⟩ : ∃ n, Nat.card G = n) with ⟨n, hn⟩
  induction n using Nat.strong_induction_on generalizing G with
  | _ n ih =>
  rcases subsingleton_or_nontrivial G with hG1 | hG1
  · exact isSupersolvable_of_subsingleton
  have hne : (Nat.card G).primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr Finite.one_lt_card
  have hq : (Nat.card G).primeFactors.max' hne ∈ (Nat.card G).primeFactors :=
    Finset.max'_mem _ hne
  have : Fact ((Nat.card G).primeFactors.max' hne).Prime := ⟨(Nat.mem_primeFactors.mp hq).1⟩
  let Q : Sylow ((Nat.card G).primeFactors.max' hne) G := Classical.arbitrary _
  have : (Q : Subgroup G).Normal := normal_sylow_of_forall_isCoatom_index_prime hG
    (fun r hr hrG ↦ Finset.le_max' _ r (Nat.mem_primeFactors.mpr ⟨hr, hrG, Nat.card_pos.ne'⟩)) Q
  rcases exists_ne_one_normal_zpowers_of_forall_isCoatom hG Q.isPGroup Q.card_coprime_index
    (Q.ne_bot_of_dvd_card (Nat.mem_primeFactors.mp hq).2.1) with ⟨c, -, hc1, hcn⟩
  refine IsSupersolvable.of_quotient_zpowers (ih _ ?_
    (fun M hM ↦ index_prime_quotient_of_forall_isCoatom hG (zpowers c) hM) rfl)
  have h : orderOf c * (zpowers c).index = Nat.card G := Nat.card_zpowers c ▸ card_mul_index _
  rw [← hn, ← index_eq_card, ← h]
  exact lt_mul_left (Nat.pos_of_ne_zero (zpowers c).index_ne_zero_of_finite)
    (Nat.lt_of_le_of_ne (orderOf_pos c) fun h ↦ hc1 (orderOf_eq_one_iff.mp h.symm))

/-- **A finite group is supersolvable if and only if each of its maximal subgroups has prime
index** (LMFDB `group.supersolvable`, Huppert). -/
lemma isSupersolvable_iff_forall_isCoatom_index_prime :
    IsSupersolvable G ↔ ∀ M : Subgroup G, IsCoatom M → M.index.Prime :=
  ⟨fun h _ hM ↦ h.index_prime_of_isCoatom hM, isSupersolvable_of_forall_isCoatom_index_prime⟩

end Group
