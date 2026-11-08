import LeanBridge.ForMathlib.AlgebraicGeometry.EllipticCurve.Isogeny.Matrix
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Descent
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Factorisation
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.BaseChange
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Galois
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Torsion.Structure

/-!
# Cyclic isogenies between isogenous elliptic curves

Over a field `K` of characteristic zero, an isogeny of least degree between two elliptic curves is
cyclic. If the kernel of an isogeny `φ` over an algebraic closure `K̄` is not cyclic, it contains
the `p`-torsion for a prime `p`, so `φ` factors through `[p]` over `K̄`. The factor is fixed by
the Galois conjugations, as `φ` and `[p]` are, so it descends to an isogeny over `K` of degree
`deg φ / p²`. So the entries of the isogeny matrix are least degrees of cyclic isogenies, never
the infimum of an empty set.

## Main results

* `AddCommGroup.isAddCyclic_of_forall_card_torsionBy_le`: a finite abelian group whose `p`-torsion
  has at most `p` elements for every prime `p` is cyclic.
* `TauCeti.Isogeny.exists_isCyclic`: over a field of characteristic zero, there is a cyclic
  isogeny between two elliptic curves as soon as there is an isogeny between them.
* `WeierstrassCurve.IsIsogenous.exists_isCyclic`: over a field of characteristic zero, two
  isogenous elliptic curves are related by a cyclic isogeny.
* `WeierstrassCurve.isLeast_isogenyMatrix`: over a field of characteristic zero, every entry of
  the isogeny matrix is the least degree of a cyclic isogeny between curves in the two classes.
* `WeierstrassCurve.exists_isCyclic_degree_eq_isogenyMatrix`: the entry at the classes of two
  curves is the degree of a cyclic isogeny between them.
-/

open AddSubgroup TauCeti WeierstrassCurve
open scoped Classical

namespace AddCommGroup

variable {A : Type*} [AddCommGroup A] [Finite A]

lemma card_torsionBy_mul_le (p k : ℕ) :
    Nat.card (torsionBy A (p * k : ℕ)) ≤ Nat.card (torsionBy A k) * Nat.card (torsionBy A p) := by
  let f : torsionBy A (p * k : ℕ) →+ A :=
    (nsmulAddMonoidHom k).comp (torsionBy A (p * k : ℕ)).subtype
  have hker : Nat.card f.ker ≤ Nat.card (torsionBy A k) :=
    Nat.card_le_card_of_injective (fun x ↦ ⟨x.1.1, torsionBy.nsmul_iff.mpr x.2⟩) fun x y h ↦
      Subtype.ext <| Subtype.ext <| Subtype.mk.inj h
  have hrange : Nat.card f.range ≤ Nat.card (torsionBy A p) := by
    refine card_le_of_le ?_
    rintro _ ⟨x, rfl⟩
    exact torsionBy.nsmul_iff.mpr <| (smul_smul p k x.1).trans <| torsionBy.nsmul_iff.mp x.2
  rw [← card_ker_mul_card_range f]
  exact Nat.mul_le_mul hker hrange

lemma card_torsionBy_le (h : ∀ p : ℕ, p.Prime → Nat.card (torsionBy A p) ≤ p) {n : ℕ} (hn : 0 < n) :
    Nat.card (torsionBy A n) ≤ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases (Nat.succ_le_of_lt hn).eq_or_lt with rfl | hn1
    · refine (card_le_one_iff_eq_bot _).mpr <| eq_bot_iff.mpr fun x hx ↦ ?_
      exact mem_bot.mpr <| (one_nsmul x).symm.trans <| torsionBy.nsmul_iff.mp hx
    · have hp : n.minFac.Prime := Nat.minFac_prime hn1.ne'
      exact (congrArg (fun m : ℕ ↦ Nat.card (torsionBy A m))
        (Nat.mul_div_cancel' n.minFac_dvd)).symm.trans_le <|
        (card_torsionBy_mul_le n.minFac (n / n.minFac)).trans <|
        (Nat.mul_le_mul (ih _ (Nat.div_lt_self hn hp.one_lt)
        (Nat.div_pos (Nat.minFac_le hn) hp.pos)) (h _ hp)).trans_eq <|
        Nat.div_mul_cancel n.minFac_dvd

/-- **A finite abelian group is cyclic as soon as its `p`-torsion has at most `p` elements for
every prime `p`**: its `n`-torsion then has at most `n` elements for every `n`. -/
lemma isAddCyclic_of_forall_card_torsionBy_le
    (h : ∀ p : ℕ, p.Prime → Nat.card (torsionBy A p) ≤ p) : IsAddCyclic A := by
  let _ : Fintype A := Fintype.ofFinite A
  refine isAddCyclic_of_card_nsmul_eq_zero_le fun n hn ↦ le_of_eq_of_le ?_ (card_torsionBy_le h hn)
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr <| Equiv.subtypeEquivRight fun _ ↦ torsionBy.nsmul_iff.symm

end AddCommGroup

namespace TauCeti.Isogeny

variable {K : Type*} [Field K] [CharZero K] {W₁ W₂ : WeierstrassCurve.Affine K} [W₁.IsElliptic]
  [W₂.IsElliptic] {φ : Isogeny W₁ W₂}

lemma exists_prime_torsionBy_le_geometricKer (hφ : ¬φ.IsCyclic) : ∃ p : ℕ, p.Prime ∧
    torsionBy (W₁.map (algebraMap K (AlgebraicClosure K))).Point p ≤ φ.geometricKer := by
  by_contra! h
  refine hφ <| AddCommGroup.isAddCyclic_of_forall_card_torsionBy_le fun p hp ↦ ?_
  have : NeZero p := ⟨hp.ne_zero⟩
  rcases torsion_addEquiv_prod (W₁.map (algebraMap K (AlgebraicClosure K))) p
    (Nat.cast_ne_zero.mpr hp.ne_zero) with ⟨e⟩
  have hT : Nat.card (torsionBy (W₁.map (algebraMap K (AlgebraicClosure K))).Point p) = p ^ 2 :=
    (Nat.card_congr e.toEquiv).trans <| by rw [Nat.card_prod, Nat.card_zmod, sq]
  have : Finite (torsionBy (W₁.map (algebraMap K (AlgebraicClosure K))).Point p) :=
    .of_equiv _ e.symm.toEquiv
  let H : AddSubgroup (W₁.map (algebraMap K (AlgebraicClosure K))).Point :=
    (torsionBy φ.geometricKer p).map φ.geometricKer.subtype
  have hHT : H ≤ torsionBy _ p := map_le_iff_le_comap.mpr fun x hx ↦
    torsionBy.nsmul_iff.mpr <| congrArg Subtype.val <| torsionBy.nsmul_iff.mp hx
  have hHG : H ≤ φ.geometricKer := map_subtype_le _
  have hH : Nat.card H = Nat.card (torsionBy φ.geometricKer p) :=
    card_map_of_injective φ.geometricKer.subtype_injective
  rcases (Nat.dvd_prime_pow hp).mp (hT ▸ card_dvd_of_le hHT) with ⟨i, hi, hHi⟩
  rw [← hH, hHi]
  rcases hi.lt_or_eq with hi | rfl
  · exact (Nat.pow_le_pow_right hp.pos (Nat.lt_succ_iff.mp hi)).trans_eq (pow_one p)
  · exact (h p hp (eq_of_le_of_card_ge hHT (hT.trans hHi.symm).le ▸ hHG)).elim

lemma exists_degree_lt_of_not_isCyclic (hφ : ¬φ.IsCyclic) :
    ∃ ψ : Isogeny W₁ W₂, ψ.degree < φ.degree := by
  rcases exists_prime_torsionBy_le_geometricKer hφ with ⟨p, hp, hle⟩
  have hp0 : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hker : ((mulByIntIsogenyOfNeZero W₁ hp0).map (algebraMap K (AlgebraicClosure K))).ker ≤
      (φ.map (algebraMap K (AlgebraicClosure K))).ker := by
    rw [mulByIntIsogeny_map, ker_mulByIntIsogeny_eq_torsionBy, ker_eq_map_ker_toPointHom]
    intro P hP
    rw [mem_map_equiv, AddMonoidHom.mem_ker, ← Hom.pointMap_ofIsogeny_eq_toPointHom]
    exact hle <| torsionBy.nsmul_iff.mpr <| by
      rw [← map_nsmul, torsionBy.nsmul_iff.mp hP, map_zero]
  rcases (existsUnique_comp_eq_iff_ker_le (by
    rw [mulByIntIsogeny_map]
    exact card_ker_mulByIntIsogeny_eq_degree _ (Int.cast_ne_zero.mpr hp0)) _).mpr hker with
    ⟨χ, hχ, hχu⟩
  rcases (existsUnique_map_eq_iff_galoisFixed W₁ W₂ χ).mpr fun σ ↦ hχu _ <|
    (congrArg (χ.galoisConj W₁ W₂ σ).comp (galoisConj_map_algebraMap W₁ W₁
      (mulByIntIsogenyOfNeZero W₁ hp0) σ).symm).trans <|
    (galoisConj_comp W₁ W₁ W₂ χ _ σ).symm.trans <|
    (congrArg (galoisConj W₁ W₂ · σ) hχ).trans (galoisConj_map_algebraMap W₁ W₂ φ σ) with
    ⟨ψ, hψ, -⟩
  refine ⟨ψ, ?_⟩
  rw [← degree_map φ (algebraMap K (AlgebraicClosure K)), ← hχ, degree_comp, ← hψ, degree_map,
    degree_map, degree_mulByIntIsogenyOfNeZero, Int.natAbs_natCast]
  exact lt_mul_of_one_lt_right ψ.degree_pos (Nat.one_lt_pow two_ne_zero hp.one_lt)

/-- **There is a cyclic isogeny between two elliptic curves as soon as there is an isogeny**, over
a field of characteristic zero: an isogeny of least degree between them is cyclic. -/
lemma exists_isCyclic (h : Nonempty (Isogeny W₁ W₂)) : ∃ ψ : Isogeny W₁ W₂, ψ.IsCyclic := by
  rcases h with ⟨χ⟩
  generalize hn : χ.degree = n
  induction n using Nat.strong_induction_on generalizing χ with
  | _ n ih =>
    by_cases hχ : χ.IsCyclic
    · exact ⟨χ, hχ⟩
    · rcases exists_degree_lt_of_not_isCyclic hχ with ⟨ψ, hψ⟩
      exact ih _ (hn ▸ hψ) ψ rfl

end TauCeti.Isogeny

namespace WeierstrassCurve

variable {K : Type*} [Field K] [CharZero K] {W W₁ W₂ : WeierstrassCurve K} [W.IsElliptic]
  [W₁.IsElliptic] [W₂.IsElliptic]

/-- **Two isogenous elliptic curves are related by a cyclic isogeny**, over a field of
characteristic zero. -/
lemma IsIsogenous.exists_isCyclic (h : W₁.IsIsogenous W₂) :
    ∃ φ : Isogeny W₁.toAffine W₂.toAffine, φ.IsCyclic :=
  Isogeny.exists_isCyclic h

lemma IsomorphismClass.cyclicIsogenyDegrees_nonempty (c c' : W.isogenyClass) :
    (c.1.cyclicIsogenyDegrees c'.1).Nonempty := by
  rcases exists_isElliptic_of_mem_isogenyClass c.2 with ⟨V₁, _, h₁⟩
  rcases exists_isElliptic_of_mem_isogenyClass c'.2 with ⟨V₂, _, h₂⟩
  rcases ((mk_mem_isogenyClass_iff.mp (h₁ ▸ c.2)).symm.trans
    (mk_mem_isogenyClass_iff.mp (h₂ ▸ c'.2))).exists_isCyclic with ⟨φ, hφ⟩
  exact ⟨φ.degree, V₁, V₂, ‹_›, ‹_›, h₁, h₂, φ, hφ, rfl⟩

/-- **Every entry of the isogeny matrix is the least degree of a cyclic isogeny** between curves in
the two classes, over a field of characteristic zero: such cyclic isogenies exist. -/
lemma isLeast_isogenyMatrix (c c' : W.isogenyClass) :
    IsLeast (c.1.cyclicIsogenyDegrees c'.1) (W.isogenyMatrix c c') :=
  ⟨Nat.sInf_mem (IsomorphismClass.cyclicIsogenyDegrees_nonempty c c'), fun _ ↦ Nat.sInf_le⟩

/-- **The entry of the isogeny matrix at the classes of two curves is the degree of a cyclic
isogeny between them**, over a field of characteristic zero. -/
lemma exists_isCyclic_degree_eq_isogenyMatrix (h₁ : (⟦W₁⟧ : IsomorphismClass K) ∈ W.isogenyClass)
    (h₂ : (⟦W₂⟧ : IsomorphismClass K) ∈ W.isogenyClass) : ∃ φ : Isogeny W₁.toAffine W₂.toAffine,
    φ.IsCyclic ∧ φ.degree = W.isogenyMatrix ⟨_, h₁⟩ ⟨_, h₂⟩ :=
  IsomorphismClass.mk_mem_cyclicIsogenyDegrees_iff.mp (isLeast_isogenyMatrix ⟨_, h₁⟩ ⟨_, h₂⟩).1

end WeierstrassCurve
