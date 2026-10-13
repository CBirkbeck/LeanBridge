/-
Copyright (c) 2025 Alain Chavarri Villarello. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alain Chavarri Villarello
-/
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import LeanBridge.IdealArithmetic.Saturation.LogMatrix
import LeanBridge.IdealArithmetic.IdealArithmetic.IdealArithmetic
import LeanBridge.IdealArithmetic.Saturation.CertifyTorsionOrder
import LeanBridge.IdealArithmetic.Saturation.ClassGroupSaturation

/- # p-saturation certificate

Here we specialized `LogFiniteRing` , `MatrixLogProd`
and the releated theorems to prove `p`-saturation to the case
where the reduction homomorphisms `φ` are reduction modulo primes of degree `1`.
(Note that for number fields, we can always assume this case).

## Main definition
- `pMaximalUnitsCertificateNDvdT`: for`p` not dividing the torsion order.
  Certify that a system of units is `p`-maximal.
- `pMaximalUnitsCertificateDvdT`: for`p` dividing the torsion order.
  Certify that a system of units is `p`-maximal.
- `pSaturatedClassGroupCertificateNDvdT`: for`p` not dividing the torsion order,
  certify `p`-saturation for a tuple of ideals.
- `pSaturatedClassGroupCertificateDvdT`: for `p` dividing the torsion order,
  certify `p`-saturation for a tuple of ideals.  -/

open Module

section PowCert

open Classical

/-- Certify the order of an element in a monoid. -/
structure IsOrderOf {G : Type*} [Monoid G] (x : G) (n : ℕ) where
  m : ℕ
  P : Fin m → ℕ
  e : Fin m → ℕ
  hP : ∀ i, Nat.Prime (P i)
  hm : ∏ i, (P i) ^ (e i) = n
  hid : x ^ n = 1
  hnid : ∀ i , x ^ (n / (P i)) ≠ 1

lemma orderOf_of_IsOrderOf {G : Type*} [Monoid G] {x : G} {n : ℕ} (h : IsOrderOf x n) :
  orderOf x = n := by
  refine orderOf_eq_of_pow_and_pow_div_prime ?_ h.hid ?_
  · rw [← h.hm]
    simp only [CanonicallyOrderedAdd.prod_pos, Finset.mem_univ, forall_const]
    intro i
    apply Nat.pow_pos
    exact Nat.Prime.pos (h.hP i)
  · intro p hp hpdvd
    rw [← h.hm, Prime.dvd_finset_prod_iff (Nat.prime_iff.mp hp)] at hpdvd
    choose a hau hadvd using hpdvd
    rw [Nat.prime_eq_prime_of_dvd_pow hp (h.hP a) hadvd]
    exact h.hnid a

lemma is_primitive_root_finite_field {F : Type*} [Field F] [Fintype F] {n : ℕ}
  (hcard : n = Fintype.card F - 1) (ζ : F) (h : IsOrderOf ζ n) : IsPrimitiveRoot ζ (Fintype.card Fˣ) := by
  convert IsPrimitiveRoot.orderOf ζ
  rw [orderOf_of_IsOrderOf h, hcard]
  exact Fintype.card_units F


end PowCert



/-- Given an ideal `I` of norm a prime integer `q`, this is the 'discrete logarithm' map that
sends `x` in `O` to `n % p` in `ZMod p`, where `ζ ^ n = x mod I` and `ζ` is a generator of
`(ZMod q)ˣ`. -/
noncomputable def LogFiniteZMod {O : Type*} [CommRing O] {q : ℕ}
  [hq : Fact $ Nat.Prime q] {I : Ideal O} (hcard : Nat.card (O ⧸ I) = q)
  {ζ : ℕ} (hr : IsPrimitiveRoot (ζ : ZMod q) (q - 1)) (p : ℕ) : O → ZMod p := by
  intro x
  let φ := ((modIdealToZMod (hq).out (I) (hcard)).comp (Ideal.Quotient.mk (I)))
  refine LogFiniteRing (ζ := (ζ : ZMod q)) ?_ p (φ x)
  convert hr
  simp only [ZMod.card_units_eq_totient, Nat.totient_prime hq.out]


attribute [-instance]  Lean.Omega.IntList.instAdd

/-- Certificate for the value of `LogFiniteZMod` at `x : O`.  -/
structure DiscreteLogCertificate {O : Type*} [CommRing O] {q ζ : ℕ}
    {I : Ideal O} (hcard : Nat.card (O ⧸ I) = q) (hr : IsPrimitiveRoot (ζ : ZMod q) (q - 1))
    (p : ℕ) (x : O) (l : ZMod p) where
  r : ℕ
  hN : NeZero r := by infer_instance
  hpdvd : p ∣ q - 1
  B : Basis (Fin r) ℤ O
  hone : B 0 = 1
  xcoord : Fin r → ℤ
  hxeq : x =  B.equivFun.symm xcoord
  m : ℤ
  C : Fin r → ℤ
  hCeq : List.ofFn C = List.ofFn xcoord + List.ofFn (fun (i : Fin r) => if i = 0 then (- m : ℤ) else 0)
  hmem :  B.equivFun.symm C ∈ I
  k : ℕ
  hpow : (ζ : ZMod q) ^ k = m
  heql : l = k

lemma apply_map_ZMod {O : Type*} [CommRing O] {q ζ : ℕ}
    [hq : Fact $ Nat.Prime q] {I : Ideal O} {hcard : Nat.card (O ⧸ I) = q}
    {hr : IsPrimitiveRoot (ζ : ZMod q) (q - 1)} {p : ℕ} {x : O} {l : ZMod p}
    (A : DiscreteLogCertificate hcard hr p x l) :
      (modIdealToZMod (hq).out I hcard) ((Ideal.Quotient.mk I) x) = A.m := by
  haveI : NeZero A.r := A.hN
  have hmem : x - A.m ∈ I := by
    convert A.hmem
    rw [← table_add_list_eq_add A.B A.xcoord
      (fun (i : Fin A.r) => if i = 0 then (- A.m : ℤ) else 0) A.C A.hCeq, ← A.hxeq]
    simp [A.hone]
    exact  sub_eq_add_neg _ _
  rw [Ideal.Quotient.eq.2 hmem, map_intCast, map_intCast]


lemma eq_of_DiscreteLogCertificate {O : Type*} [CommRing O] {q ζ : ℕ}
    [hq : Fact $ Nat.Prime q] {I : Ideal O} {hcard : Nat.card (O ⧸ I) = q}
    {hr : IsPrimitiveRoot (ζ : ZMod q) (q - 1)} {p : ℕ} {x : O} {l : ZMod p}
    (A : DiscreteLogCertificate hcard hr p x l) : LogFiniteZMod hcard hr p x = l := by
  simp only [LogFiniteZMod]
  dsimp
  rw [apply_map_ZMod A, ← A.hpow]
  convert LogFiniteRing_of_pow ?_ ?_ A.k
  · exact A.heql
  · rw [ZMod.card_units_eq_totient, Nat.totient_prime hq.out]
    exact A.hpdvd

section

variable {ι τ κ : Type*} {O : Type*} [CommRing O] [Fintype ι] [Fintype τ]
  (p : ℕ) {q : τ → ℕ} [hF : ∀ i, Fact $ Nat.Prime (q i)]
  {I : τ → Ideal O} (hcard : ∀ j, Nat.card (O ⧸ (I j)) = q j)
  (x : ι → O) {ζ : τ → ℕ} (hr : ∀ i, IsPrimitiveRoot (ζ i : ZMod (q i)) (q i - 1))


def F (q : τ → ℕ) : τ → Type _ := fun i => (ZMod (q i))

instance F_CommRing : ∀ i, CommRing (F q i) := fun i => ZMod.commRing (q i)

instance F_Fintype : ∀ i, Fintype (F q i) := by
  intro i
  exact ZMod.fintype (q i)

open Classical

noncomputable instance F_unit_Fintype :  ∀ i, Fintype (F q i)ˣ := by
  intro i
  refine instFintypeUnitsOfDecidableEq

/- Given a collection of ideals of prime norm `qᵢ`, this is the reduction map `O → ZMod _` -/
noncomputable def φ : Π i : τ, O →+* (ZMod (q i)) := by
  intro i
  exact ((modIdealToZMod (hF i).out (I i) (hcard i)).comp (Ideal.Quotient.mk (I i)))

include hr in
lemma hr_aux : ∀ i , IsPrimitiveRoot (ζ i : ZMod (q i)) (Fintype.card (F q i)ˣ) := by
  intro i
  convert hr i
  convert (ZMod.card_units_eq_totient (q i)).trans (Nat.totient_prime (hF i).out) <;> rfl


noncomputable def MatrixLogZMod : Matrix τ ι (ZMod p) :=
  fun i j => LogFiniteZMod (hcard i) (hr i) p (x j)


lemma MatrixLog_eq :
  MatrixLogZMod p hcard x hr = MatrixLogProd p (F q) (φ hcard) x _ (hr_aux hr) := by rfl


lemma not_principal_of_full_rank_matrixLogZMod {p n : ℕ} [hp : Fact $ Nat.Prime p]
    [IsDomain O] (u : ι → O) (hu : ∀ i, IsUnit (u i))
    (hugen : ∀ (w : Oˣ), (∃ (e : ι → ℕ) , (∃ (t : Oˣ) , w = (∏ (i : ι), (u i) ^ (e i)) * t ^ p)))
    (hdvd : ∀ i, p ∣ q i - 1) (J : Ideal O) (a : O)
    (hua : ∀ i, (modIdealToZMod (hF i).out (I i) (hcard i)) ((Ideal.Quotient.mk (I i)) a) ≠ 0)
    (hdvdp : p ∣ n) (h : J ^ n = Ideal.span {a})
    (hrank : (MatrixLogZMod p hcard (Sum.elim (fun i => u i)
      (fun (_ : Fin 1) => a)) hr).rank = Fintype.card ι + 1) :
    ¬ ∃ b, J = Ideal.span {b} := by
  refine not_principal_of_full_rank_matrix (F q) u hu hugen (φ hcard) (fun i => ↑(ζ i)) (hr_aux hr) ?_ J a ?_ hdvdp h ?_
  · intro i
    unfold F
    simp only [ZMod.card_units_eq_totient, Nat.totient_prime (hF i).out]
    exact hdvd i
  · intro i
    apply (isUnit_iff_ne_zero (a := (φ hcard i) a)).2
    exact hua i
  · erw [← MatrixLog_eq p hcard _ hr]
    exact hrank

/-- Specialized version of `not_principal_of_full_rank_matrix''`. -/
lemma pSaturated_of_full_rank_matrixLogZMod [IsIntegrallyClosed O] {κ γ} [Fintype κ] [Fintype γ]
    {p : ℕ} [hp : Fact $ Nat.Prime p]
    [IsDomain O] (u : ι → O) (hu : ∀ i, IsUnit (u i))
    (hugen : ∀ (w : Oˣ), (∃ (e : ι → ℕ) , (∃ (t : Oˣ) , w = (∏ (i : ι), (u i) ^ (e i)) * t ^ p)))
    (hdvd : ∀ i, p ∣ q i - 1) (J : κ → Ideal O) (a : κ → O)
    (n : κ → ℕ) (ψ : γ → κ) (hψ : ∀ i, (p ∣ n i) → ∃ j , ψ j = i )
    (hua : ∀ i, ∀ j,
      (modIdealToZMod (hF i).out (I i) (hcard i)) ((Ideal.Quotient.mk (I i)) (a (ψ j))) ≠ 0)
    (hnzero : ∀ j , j ∈ (Finset.image ψ Finset.univ)ᶜ → a j ≠ 0 )
    (h : ∀ i, (J i) ^ (n i) = Ideal.span {a i})
    (hrank : (MatrixLogZMod p hcard (Sum.elim (fun i => u i) (fun i => a (ψ i))) hr).rank
      = Fintype.card ι + Fintype.card γ)
    (r : κ → ℕ) (b : O) (hrprod : ∏ i, (J i) ^ (r i) = Ideal.span {b})
    (hdvdp : ∀ i , (n i) ∣ p * (r i)) :
    ∀ i , n i ∣ r i := by
  refine not_principal_of_full_rank_matrix'' (F q) u hu hugen (φ hcard)
    (fun i => ↑(ζ i)) (hr_aux hr) ?_ J a n r ψ hψ ?_ hnzero h b hrprod hdvdp hrank
  · intro i
    unfold F
    simp only [ZMod.card_units_eq_totient, Nat.totient_prime (hF i).out]
    exact hdvd i
  · intro i j
    apply (isUnit_iff_ne_zero (a := (φ hcard i) (a (ψ j)))).2
    exact hua i j


/-- Specialized version of `units_linear_independent_of_full_rank_matrix_of_p_not_dvd_torsion`. -/
lemma units_linear_independent_not_dvd_torsion_of_full_rank {p : ℕ} [hp : Fact $ Nat.Prime p]
    [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
    [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
    (u : ι → O) (hu : ∀ i, IsUnit (u i)) (hdvd : ∀ i, p ∣ q i - 1)
    (hpndvdt : ¬ p ∣ Nat.card (CommGroup.torsion Oˣ))
    (hrank : (MatrixLogZMod p hcard u hr).rank = Fintype.card ι) :
    LinearIndependent ℤ (fun i => Additive.ofMul
      (QuotientGroup.mk (s := (CommGroup.torsion Oˣ)) (hu i).unit)) := by
  refine units_linear_independent_of_full_rank_matrix_of_p_not_dvd_torsion (F q) u hu (φ hcard)
    (fun i => ↑(ζ i)) (hr_aux hr) ?_ hpndvdt ?_
  · intro i
    unfold F
    simp only [ZMod.card_units_eq_totient, Nat.totient_prime (hF i).out]
    exact hdvd i
  · erw [← MatrixLog_eq p hcard _ hr]
    exact hrank

/-- Specialized version of `units_up_to_p_power_of_full_rank_matrix_of_p_not_dvd_torsion`. -/
lemma units_up_to_p_power_not_dvd_torsion_of_full_rank {p : ℕ} [hp : Fact $ Nat.Prime p]
    [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
    [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
    (u : ι → O) (hu : ∀ i, IsUnit (u i)) (hdvd : ∀ i, p ∣ q i - 1)
    (hpndvdt : ¬ p ∣ Nat.card (CommGroup.torsion Oˣ))
    (hrank : (MatrixLogZMod p hcard u hr).rank = Fintype.card ι)
    (huc : Module.finrank ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ))) ≤ Fintype.card ι) (w : Oˣ) :
    ∃ (e' : ι → ℤ), (∃ (t : Oˣ) , w = (∏ (i : ι), ((hu i).unit) ^ (e' i)) * t ^ p) := by
  refine units_up_to_p_power_of_full_rank_matrix_of_p_not_dvd_torsion (F q) u hu (φ hcard)
    (fun i => ↑(ζ i)) (hr_aux hr) ?_ hpndvdt ?_ huc w
  · intro i
    unfold F
    simp only [ZMod.card_units_eq_totient, Nat.totient_prime (hF i).out]
    exact hdvd i
  · erw [← MatrixLog_eq p hcard _ hr]
    exact hrank

/-- Specialized version of `units_up_to_p_power_of_full_rank_matrix_of_p_dvd_torsion`. -/
lemma units_up_to_p_power_dvd_torsion_of_full_rank [Fintype κ] {p : ℕ} [hp : Fact $ Nat.Prime p]
    [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
    [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
    (u : ι → O) (hu : ∀ i, IsUnit (u i)) (hdvd : ∀ i, p ∣ q i - 1)
    (v : κ → O) (hv : ∀ i, IsUnit (v i))
    (hvt : ∀ w ∈ CommGroup.torsion Oˣ, (∃ (a : κ → ℤ) , (∃ t ∈ CommGroup.torsion Oˣ ,
      w = (∏ i, (hv i).unit ^ (a i)) * t ^ p)))
    (hrank : (MatrixLogZMod p hcard ((Sum.elim u v)) hr).rank = Fintype.card ι + Fintype.card κ)
    (huc : Module.finrank ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ))) ≤ Fintype.card ι) (w : Oˣ) :
    ∃ (e' : ι ⊕ κ → ℤ), (∃ (t : Oˣ) , w = (∏ (i : ι ⊕ κ), (Sum.elim (fun i => (hu i).unit)
      (fun i => (hv i).unit) i) ^ (e' i)) * t ^ p) := by
  refine units_up_to_p_power_of_full_rank_matrix_of_p_dvd_torsion (F q) u hu (φ hcard)
    (fun i => ↑(ζ i)) (hr_aux hr) ?_ v hv hvt ?_ huc w
  · intro i
    unfold F
    simp only [ZMod.card_units_eq_totient, Nat.totient_prime (hF i).out]
    exact hdvd i
  · erw [← MatrixLog_eq p hcard _ hr]
    exact hrank


lemma units_linear_independent_dvd_torsion_of_full_rank [Fintype κ] {p : ℕ}
    [hp : Fact $ Nat.Prime p] [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
    [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
    (u : ι → O) (hu : ∀ i, IsUnit (u i)) (hdvd : ∀ i, p ∣ q i - 1)
    (v : κ → O) (hv : ∀ i, IsUnit (v i))
    (hvt : ∀ w ∈ CommGroup.torsion Oˣ, (∃ (a : κ → ℤ) ,
      (∃ t ∈ CommGroup.torsion Oˣ , w = (∏ i, (hv i).unit ^ (a i)) * t ^ p)))
    (hrank : (MatrixLogZMod p hcard ((Sum.elim u v)) hr).rank
      = Fintype.card ι + Fintype.card κ) :
    LinearIndependent ℤ (fun i => Additive.ofMul
      (QuotientGroup.mk (s := (CommGroup.torsion Oˣ)) (hu i).unit)) := by
  refine units_linear_independent_of_full_rank_matrix_of_p_dvd_torsion
    (F q) u hu v hv hvt (φ hcard) (fun i => ↑(ζ i)) (hr_aux hr) ?_ ?_
  · intro i
    unfold F
    simp only [ZMod.card_units_eq_totient, Nat.totient_prime (hF i).out]
    exact hdvd i
  · erw [← MatrixLog_eq p hcard _ hr]
    exact hrank


end


-- Note: we allow the inclusion of more than r prime ideals, so these can be reused
-- when we want to certify the class group.

/-- For the case where `p` does not divide torsion order.
  Certify that a system of units is `p`-maximal. Every unit can be written as a product of these
  units and a `p`-power. -/
structure pMaximalUnitsCertificateNDvdT (O : Type*)  [CommRing O]
    (p : ℕ)  where
  hp : Nat.Prime p
  /--Rank of the unit group -/
  r : ℕ
  huc : Module.finrank ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ))) ≤ r
  u : Fin r → O
  hu : ∀ i, IsUnit (u i)
  /-- Number of prime ideals we consider. This has to be at least `r`.-/
  t : ℕ
  hrle : r ≤ t
  /-- List of prime norms. -/
  q : Fin t → ℕ
  hqP : ∀ i, Fact (Nat.Prime (q i))
  I : Fin t → Ideal O
  hcard : ∀ j, Nat.card (O ⧸ I j) = q j
  ζ : Fin t → ℕ
  hr : ∀ i, IsPrimitiveRoot (ζ i : ZMod (q i)) (q i - 1)
  hdvd : ∀ i, p ∣ q i - 1
  hpndvdt : ¬p ∣ Nat.card (CommGroup.torsion Oˣ)
  M : Matrix (Fin t) (Fin r) (ZMod p)
  hM1 : ∀ i, ∀ j, M i j = LogFiniteZMod (hcard i) (hr i) p (u j)
  Minv : Matrix (Fin r) (Fin r) (ZMod p)
  hInv : M.submatrix (Fin.castLE hrle) id * Minv = 1

--Note: Removing the last rows so that the matrix is square we get an
-- invertible matrix (simple way to check that M is full rank)


lemma matrix_of_pMaximalUnitsCertificateNDvdT {O : Type*} [CommRing O] {p : ℕ}
    (C : pMaximalUnitsCertificateNDvdT O p) :
      C.M.submatrix (Fin.castLE C.hrle) id  =
        (MatrixLogZMod p (hF := fun i : Fin C.r => C.hqP (Fin.castLE C.hrle i))
          (fun i => C.hcard (Fin.castLE C.hrle i)) C.u (fun i => C.hr (Fin.castLE C.hrle i))) := by
  ext i j
  simp only [Matrix.submatrix_apply, id_eq, MatrixLogZMod]
  convert C.hM1 (Fin.castLE C.hrle i) j

lemma units_linear_independent_of_pMaximalUnitsCertificateNDvdT {O : Type*} [CommRing O]
    [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
    [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))] {p : ℕ}
    (C : pMaximalUnitsCertificateNDvdT O p) :
  LinearIndependent ℤ (fun i => Additive.ofMul
    (QuotientGroup.mk (s := (CommGroup.torsion Oˣ)) (C.hu i).unit)) := by
  haveI : Fact $ Nat.Prime p := {out := C.hp}
  refine units_linear_independent_not_dvd_torsion_of_full_rank
    (hF := fun i : Fin C.r => C.hqP (Fin.castLE C.hrle i))  (fun i => C.hcard (Fin.castLE C.hrle i))
    (fun i => C.hr (Fin.castLE C.hrle i)) C.u C.hu
    (fun i => C.hdvd (Fin.castLE C.hrle i)) C.hpndvdt ?_
  rw [← matrix_of_pMaximalUnitsCertificateNDvdT C]
  refine le_antisymm ?_ ?_
  · convert (Matrix.rank_le_card_width) _
    infer_instance
  · refine le_of_eq_of_le ?_ (Matrix.rank_mul_le_left _ C.Minv)
    rw [C.hInv]
    simp only [Fintype.card_fin, Matrix.rank_one]


lemma units_of_pMaximalUnitsCertificateNDvdT {O : Type*} [CommRing O]
    [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
    [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))] {p : ℕ}
    (C : pMaximalUnitsCertificateNDvdT O p) (w : Oˣ) :
    ∃ (e' : Fin C.r → ℤ), (∃ (t : Oˣ) , w = (∏ i, ((C.hu i).unit) ^ (e' i)) * t ^ p) := by
  haveI : Fact $ Nat.Prime p := {out := C.hp}
  refine units_up_to_p_power_not_dvd_torsion_of_full_rank
    (hF := fun i : Fin C.r => C.hqP (Fin.castLE C.hrle i))
    (fun i => C.hcard (Fin.castLE C.hrle i))
    (fun i => C.hr (Fin.castLE C.hrle i)) C.u C.hu
      (fun i => C.hdvd (Fin.castLE C.hrle i)) C.hpndvdt ?_ ?_ w
  rw [← matrix_of_pMaximalUnitsCertificateNDvdT C]
  refine le_antisymm ?_ ?_
  · convert (Matrix.rank_le_card_width) _
    infer_instance
  · refine le_of_eq_of_le ?_ (Matrix.rank_mul_le_left _ C.Minv)
    rw [C.hInv]
    simp only [Fintype.card_fin, Matrix.rank_one]
  simp
  exact C.huc

/-- For the case where `p` divide torsion order.
  Certify that a system of units is `p`-maximal. Every unit can be written as a product of these
  units and a `p`-power.-/
structure pMaximalUnitsCertificateDvdT (O : Type*) [CommRing O] (p : ℕ) where
  hp : Nat.Prime p
  /-- Rank of the unit group-/
  r : ℕ
  huc : Module.finrank ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ))) ≤ r
  u : Fin r → O
  hu : ∀ i, IsUnit (u i)
  /--Generator of the torsion group (mod `p`-powers)-/
  v : O
  m : ℕ
  hm : m ≠ 0
  hmv : v ^ m = 1
  /-- Number of prime ideals we consider. This has to be at least `r`.-/
  t : ℕ
  hrle : r + 1 ≤ t
  /-- List of prime norms -/
  q : Fin t → ℕ
  hqP : ∀ i, Fact (Nat.Prime (q i))
  I : Fin t → Ideal O
  hcard : ∀ j, Nat.card (O ⧸ I j) = q j
  ζ : Fin t → ℕ
  hr : ∀ i, IsPrimitiveRoot (ζ i : ZMod (q i)) (q i - 1)
  hdvd : ∀ i, p ∣ q i - 1
  M : Matrix (Fin t) (Fin (r + 1)) (ZMod p)
  /-- First columns of the matrix-/
  hM1 : ∀ i, ∀ {j} , ∀ hj : j < r , M i (Fin.ofNat _ j) = LogFiniteZMod (hcard i) (hr i) p (u ⟨j, hj⟩)
  hM2 : ∀ i, M i ((Fin.ofNat _ r)) = LogFiniteZMod (hcard i) (hr i) p v
  Minv : Matrix (Fin (r + 1)) (Fin (r + 1)) (ZMod p)
  hInv : (M.submatrix (Fin.castLE hrle) id) * Minv = 1


lemma torsion_of_pMaximalUnitsCertificateDvdT {O : Type*} [CommRing O] {p : ℕ}
    [IsCyclic (CommGroup.torsion Oˣ)] (C : pMaximalUnitsCertificateDvdT O p) :
    ∀ w ∈ CommGroup.torsion Oˣ, (∃ (a : ℤ) , (∃ t ∈ CommGroup.torsion Oˣ ,
      w = ((IsUnit.of_pow_eq_one C.hmv C.hm).unit ^ a * t ^ p))) := by
  haveI : Fact $ Nat.Prime p := {out := C.hp }
  have hvmem : (IsUnit.of_pow_eq_one C.hmv C.hm).unit ∈ CommGroup.torsion Oˣ := by
    rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    use C.m
    constructor
    · exact Nat.pos_of_ne_zero C.hm
    · rw [Units.ext_iff]
      simp [C.hmv]
  intro w hwmem
  obtain ⟨⟨g, hgmem⟩ , hg ⟩ := exists_zpow_surjective (CommGroup.torsion Oˣ)
  obtain ⟨r, hr⟩ := hg ⟨w, hwmem⟩
  obtain ⟨t, ht⟩ := hg ⟨_, hvmem⟩
  rw [← Subtype.val_inj] at hr ht
  simp at hr ht
  haveI := C.hqP
  have hnz : ∃ i, LogFiniteZMod (C.hcard (Fin.castLE C.hrle i))
    (C.hr (Fin.castLE C.hrle i)) p C.v ≠ 0 := by
    by_contra! h
    simp_rw [← C.hM2] at h
    have : (C.Minv *(C.M.submatrix (Fin.castLE C.hrle) id)) (Fin.ofNat _ C.r) (Fin.ofNat _ C.r) = 1 := by
      rw [mul_eq_one_comm.1 C.hInv]
      simp only [Matrix.one_apply_eq]
    rw [Matrix.mul_apply] at this
    simp only [Matrix.submatrix_apply, id_eq, h, mul_zero,
      Finset.sum_const_zero, zero_ne_one] at this
  have hC : IsCoprime ↑p t := by
    rw [Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp C.hp)]
    rintro ⟨k, hk⟩
    obtain ⟨i, hi⟩ := hnz
    rw [hk, mul_comm, zpow_mul, zpow_natCast, Units.ext_iff] at ht
    simp at ht
    rw [← ht] at hi
    simp [LogFiniteZMod] at hi
    rw [LogFiniteRing_p_power_eq_zero] at hi
    exact hi rfl
    simp only [ZMod.card_units_eq_totient, Nat.totient_prime (C.hqP (Fin.castLE C.hrle i)).out]
    exact C.hdvd (Fin.castLE C.hrle i)
  obtain ⟨b, a, hab⟩ := hC
  use r * a , g ^ (r * b)
  constructor
  · exact Subgroup.zpow_mem (CommGroup.torsion Oˣ) hgmem _
  · rw [← ht, ← zpow_mul, ← zpow_natCast, ← zpow_mul,
      ← zpow_add, add_comm, mul_comm t _, ← hr]
    nth_rw 1 [← mul_one r, ← hab]
    congr
    ring


lemma matrix_of_pMaximalUnitsCertificateDvdT {O : Type*} [CommRing O] {p : ℕ}
    [IsCyclic (CommGroup.torsion Oˣ)] (C : pMaximalUnitsCertificateDvdT O p) :
      C.M.submatrix (Fin.castLE C.hrle) (id ∘ (finSumFinEquiv).toFun)  =
        (MatrixLogZMod p (hF := fun i : Fin (C.r + 1) => C.hqP (Fin.castLE C.hrle i))
          (fun i => C.hcard (Fin.castLE C.hrle i)) (Sum.elim C.u (fun (_ : Fin 1) => C.v))
          (fun i => C.hr (Fin.castLE C.hrle i))) := by
  ext i j
  rcases j with j | r
  · simp only [Equiv.toFun_as_coe, CompTriple.comp_eq, Matrix.submatrix_apply,
    finSumFinEquiv_apply_left, MatrixLogZMod, Sum.elim_inl]
    convert C.hM1 (Fin.castLE C.hrle i) j.2 using 2
    simp only [Fin.castAdd, Fin.castLE, Fin.ofNat_eq_cast, Fin.coe_eq_castSucc]
    rfl
  · simp only [Equiv.toFun_as_coe, CompTriple.comp_eq, Matrix.submatrix_apply,
    finSumFinEquiv_apply_right, MatrixLogZMod, Sum.elim_inr]
    convert C.hM2 (Fin.castLE C.hrle i)
    simp only [Fin.natAdd, Fin.val_eq_zero, add_zero]
    simp only [Fin.ofNat_eq_cast, Fin.natCast_eq_last]
    rfl

lemma units_linear_independent_of_pMaximalUnitsCertificateDvdT {O : Type*} [CommRing O]
    [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
    [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
    [IsCyclic (CommGroup.torsion Oˣ)] {p : ℕ}
    (C : pMaximalUnitsCertificateDvdT O p) :
    LinearIndependent ℤ (fun i => Additive.ofMul (QuotientGroup.mk
      (s := (CommGroup.torsion Oˣ)) (C.hu i).unit)) := by
  haveI : Fact $ Nat.Prime p := {out := C.hp}
  refine units_linear_independent_dvd_torsion_of_full_rank
    (hF := fun i : Fin (C.r + 1) => C.hqP (Fin.castLE C.hrle i))
    (fun i => C.hcard (Fin.castLE C.hrle i)) (fun i => C.hr (Fin.castLE C.hrle i)) C.u C.hu
      (fun i => C.hdvd (Fin.castLE C.hrle i)) (fun (i : Fin 1) => C.v) ?_ ?_ ?_
  · intro i
    exact (IsUnit.of_pow_eq_one C.hmv C.hm)
  · intro w' hwmem'
    obtain ⟨a, t, htmem, hat⟩ := torsion_of_pMaximalUnitsCertificateDvdT C w' hwmem'
    use a, t, htmem
    rw [hat]
    simp
  rw [← matrix_of_pMaximalUnitsCertificateDvdT C]
  refine le_antisymm ?_ ?_
  · convert (Matrix.rank_le_card_width) _
    rfl
    simp only [Fintype.card_fin, Fintype.card_unique, Fintype.card_sum]
    infer_instance
  · simp only [Fintype.card_fin, Fintype.card_unique, Equiv.toFun_as_coe, CompTriple.comp_eq]
    erw [← Matrix.submatrix_submatrix C.M (Fin.castLE C.hrle) id (Equiv.refl _) finSumFinEquiv]
    erw [← Matrix.reindex_apply (Equiv.refl _).symm (finSumFinEquiv).symm]
    rw [Matrix.rank, Matrix.mulVecLin_reindex, LinearMap.range_comp, LinearMap.range_comp,
      LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq, ← Matrix.rank]
    refine le_of_eq_of_le ?_ (Matrix.rank_mul_le_left _ C.Minv)
    rw [C.hInv]
    simp only [Fintype.card_fin, Matrix.rank_one]


lemma units_of_pMaximalUnitsCertificateDvdT {O : Type*} [CommRing O]
    [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
    [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))] {p : ℕ}
    [IsCyclic (CommGroup.torsion Oˣ)] (C : pMaximalUnitsCertificateDvdT O p) (w : Oˣ) :
    ∃ (e' : (Fin C.r) ⊕ (Fin 1) → ℤ), (∃ (t : Oˣ) , w = (∏ (i : (Fin C.r) ⊕ (Fin 1)),
      (Sum.elim (fun i => (C.hu i).unit)
      (fun _ => (IsUnit.of_pow_eq_one C.hmv C.hm).unit) i) ^ (e' i)) * t ^ p) := by
  haveI : Fact $ Nat.Prime p := {out := C.hp}
  refine units_up_to_p_power_dvd_torsion_of_full_rank
    (hF := fun i : Fin (C.r + 1) => C.hqP (Fin.castLE C.hrle i))
    (fun i => C.hcard (Fin.castLE C.hrle i)) (fun i => C.hr (Fin.castLE C.hrle i))
      C.u C.hu (fun i => C.hdvd (Fin.castLE C.hrle i))
      (fun (i : Fin 1) => C.v) _ ?_ ?_ ?_ w
  · intro w' hwmem'
    obtain ⟨a, t, htmem, hat⟩ := torsion_of_pMaximalUnitsCertificateDvdT C w' hwmem'
    use a, t, htmem
    rw [hat]
    simp
  rw [← matrix_of_pMaximalUnitsCertificateDvdT C]
  refine le_antisymm ?_ ?_
  · convert (Matrix.rank_le_card_width) _
    rfl
    simp only [Fintype.card_fin, Fintype.card_unique, Fintype.card_sum]
    infer_instance
  · simp only [Fintype.card_fin, Fintype.card_unique, Equiv.toFun_as_coe, CompTriple.comp_eq]
    erw [← Matrix.submatrix_submatrix C.M (Fin.castLE C.hrle) id (Equiv.refl _) finSumFinEquiv]
    erw [← Matrix.reindex_apply (Equiv.refl _).symm (finSumFinEquiv).symm]
    rw [Matrix.rank, Matrix.mulVecLin_reindex, LinearMap.range_comp, LinearMap.range_comp,
      LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq, ← Matrix.rank]
    refine le_of_eq_of_le ?_ (Matrix.rank_mul_le_left _ C.Minv)
    rw [C.hInv]
    simp only [Fintype.card_fin, Matrix.rank_one]
  · simp [C.huc]


/-- In the case where `p` does not divide the torsion order.
  Certify that a tuple of ideals is `p`-saturated in the class group. This extends
  a certificate for a `p`-maximal system of units. -/
structure pSaturatedClassGroupCertificateNDvdT {O : Type*} [CommRing O] (p : ℕ) {c : ℕ}
    (J : Fin c → Ideal O) (n : Fin c → ℕ) extends pMaximalUnitsCertificateNDvdT O p where
  a : Fin c → O
  /-- Number of indices where `p` divides `n i`.-/
  γ : ℕ
  hc : t = r + γ  -- The resulting matrix will be square
  /-- Gives the indices `i` such that `p` divides `n_i`-/
  ψ : Fin γ → Fin c
  /-- This is the left inverse of `ψ`, we fill dummy values-/
  iψ : Fin c → Fin γ
  hψ : ∀ i, p ∣ n i → ψ (iψ i) = i
  hψn : ∀ i, ¬ p ∣ n i → a i ≠ 0
  h : ∀ i, (J i) ^ (n i) = Ideal.span {a i}
  N : Matrix (Fin t) (Fin γ) (ZMod p)
  /-- Last column of the matrix. The certificate contains additional discrete log info.-/
  hM2 : ∀ i , ∀ j,  DiscreteLogCertificate (hcard i) (hr i) p (a (ψ j)) (N i j)
  hDl : ∀ i, ∀ j, ((hM2 i j).m : ZMod (q i)) ≠ 0
  NInv : Matrix (Fin t) (Fin t) (ZMod p)
  hN : ((Matrix.of (fun i => Sum.elim (M i) (N i))).reindex (Equiv.refl _)
    (finSumFinEquiv.trans (finCongr hc.symm))) * NInv = 1


lemma matrix_of_NonPrincipalCertificateNDvdT {O : Type*} [CommRing O]
  {c p : ℕ} {J : Fin c → Ideal O} {n : Fin c → ℕ}
  (C : pSaturatedClassGroupCertificateNDvdT p J n) :
  Matrix.of (fun i => Sum.elim (C.M i) (C.N i)) =
    (MatrixLogZMod p (hF := C.hqP) C.hcard
      (Sum.elim (fun i => C.u i) (fun j => C.a (C.ψ j))) C.hr) := by
    ext i j
    rcases j with j | k
    · simp only [Matrix.of_apply, Sum.elim_inl, MatrixLogZMod]
      exact C.hM1 i j
    · simp only [Matrix.of_apply, Sum.elim_inr, MatrixLogZMod]
      haveI : Fact $ Nat.Prime (C.q i) := C.hqP i
      rw [eq_of_DiscreteLogCertificate (C.hM2 i k)]


lemma pSaturated_of_CertificateNDvdT {O : Type*} [CommRing O]
    [IsDomain O] [IsIntegrallyClosed O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
    [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))] {p c : ℕ} {J : Fin c → Ideal O}
    {n : Fin c → ℕ} (C : pSaturatedClassGroupCertificateNDvdT p J n) :
    ∀ r : Fin c → ℕ, ∀ b : O, ∏ i, (J i) ^ (r i) =
      Ideal.span {b} → (∀ i, n i ∣ p * (r i)) → ∀ i, n i ∣ r i := by
  intro r b hrb hib
  haveI : Fact $ Nat.Prime p := {out := C.hp}
  refine pSaturated_of_full_rank_matrixLogZMod (hF := C.hqP) C.hcard C.hr C.u C.hu
    ?_ C.hdvd J C.a n C.ψ ?_ ?_ ?_ C.h ?_ r b hrb hib
  · intro w
    obtain ⟨e, t, h1⟩ := units_of_pMaximalUnitsCertificateNDvdT C.topMaximalUnitsCertificateNDvdT w
    obtain ⟨e',h1, t', h2 ⟩ :=
      (nat_up_to_power_of_int_up_to_power C.hu (Ne.symm (NeZero.ne' p)) e t h1)
    use e' , t'
  · intro i hi
    use C.iψ i
    exact C.hψ i hi
  · intro i j
    rw [apply_map_ZMod (hq := C.hqP i) (C.hM2 i j)]
    exact C.hDl i j
  · intro j hj
    refine C.hψn j ?_
    by_contra hc
    simp only [Finset.mem_compl, Finset.mem_image, Finset.mem_univ, true_and, not_exists] at hj
    exact  hj (C.iψ j) (C.hψ j hc)
  · rw [← matrix_of_NonPrincipalCertificateNDvdT C]
    refine le_antisymm ?_ ?_
    · convert (Matrix.rank_le_card_width) _
      rfl
      simp only [Fintype.card_sum, Fintype.card_fin]
      infer_instance
    · rw [← Matrix.rank_reindex (Equiv.refl _) ((finSumFinEquiv.trans (finCongr C.hc.symm))) ]
      refine le_of_eq_of_le ?_ (Matrix.rank_mul_le_left _ C.NInv)
      rw [C.hN]
      simp only [Fintype.card_fin, Matrix.rank_one, C.hc]


/-- In the case where `p` divides the torsion order.
  Certify that a tuple of ideals is `p`-saturated in the class group. This extends
  a certificate for a `p`-maximal system of units. -/
structure pSaturatedClassGroupCertificateDvdT {O : Type*} [CommRing O] (p : ℕ) {c : ℕ}
    (J : Fin c → Ideal O) (n : Fin c → ℕ) extends pMaximalUnitsCertificateDvdT O p where
  a : Fin c → O
  /-- Number of indices where `p` divides `n i`.-/
  γ : ℕ
  hc : t = (r + 1) + γ  -- The resulting matrix will be square
    /-- Gives the indices `i` such that `p` divides `n_i`-/
  ψ : Fin γ → Fin c
    /-- This is the left inverse of `ψ`, we fill dummy values-/
  iψ : Fin c → Fin γ
  hψ : ∀ i, p ∣ n i → ψ (iψ i) = i
  hψn : ∀ i, ¬ p ∣ n i → a i ≠ 0
  h : ∀ i, (J i) ^ (n i) = Ideal.span {a i}
  N : Matrix (Fin t) (Fin γ) (ZMod p)
    /-- Last column of the matrix. The certificate contains additional discrete log info.-/
  hM3 : ∀ i , ∀ j,  DiscreteLogCertificate (hcard i) (hr i) p (a (ψ j)) (N i j)
  hDl : ∀ i, ∀ j, ((hM3 i j).m : ZMod (q i)) ≠ 0
  NInv : Matrix (Fin t) (Fin t) (ZMod p)
  hN : ((Matrix.of (fun i => Sum.elim (M i) (N i))).reindex (Equiv.refl _)
    (finSumFinEquiv.trans (finCongr hc.symm))) * NInv = 1


lemma matrix_of_NonPrincipalCertificateDvdT {O : Type*} [CommRing O]
    {c p : ℕ} {J : Fin c → Ideal O} {n : Fin c → ℕ}
    (C : pSaturatedClassGroupCertificateDvdT p J n) :
    (Matrix.of (fun i => Sum.elim (C.M i) (C.N i))).reindex
      (Equiv.refl (Fin C.t)) (Equiv.sumCongr (finSumFinEquiv (m := C.r) (n := 1)).symm
      (Equiv.refl (Fin C.γ))) =
      (MatrixLogZMod p (hF := C.hqP) C.hcard (Sum.elim (Sum.elim (C.u) (fun (_ : Fin 1) => C.v))
      (fun j => C.a (C.ψ j))) C.hr) := by
  ext i j
  rcases j with (j | j') | k
  · simp only [Matrix.reindex_apply, Equiv.refl_symm, Equiv.coe_refl, Equiv.sumCongr_symm,
    Equiv.symm_symm, Matrix.submatrix_apply, id_eq, Equiv.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left, Matrix.of_apply, Sum.elim_inl, MatrixLogZMod]
    convert C.hM1 i j.2
    simp only [Fin.ofNat_eq_cast, Fin.coe_eq_castSucc]
    rfl
  · simp only [Matrix.reindex_apply, Equiv.refl_symm, Equiv.coe_refl, Equiv.sumCongr_symm,
    Equiv.symm_symm, Matrix.submatrix_apply, id_eq, Equiv.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_right, Matrix.of_apply, Sum.elim_inl, MatrixLogZMod, Sum.elim_inr]
    convert C.hM2 i
    rw [← Fin.val_inj]
    simp only [Fin.val_natAdd, Fin.val_eq_zero, add_zero, Fin.ofNat_eq_cast, Fin.natCast_eq_last,
      Fin.val_last]
  · simp only [Matrix.reindex_apply, Equiv.refl_symm, Equiv.coe_refl, Equiv.sumCongr_symm,
    Equiv.symm_symm, Matrix.submatrix_apply, id_eq, Equiv.sumCongr_apply, Sum.map_inr,
    Matrix.of_apply, Sum.elim_inr, MatrixLogZMod]
    haveI : Fact $ Nat.Prime (C.q i) := C.hqP i
    rw [eq_of_DiscreteLogCertificate (C.hM3 i k)]


lemma pSaturated_of_CertificateDvdT {O : Type*} [CommRing O]
    [IsDomain O] [IsIntegrallyClosed O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
    [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))] [IsCyclic (CommGroup.torsion Oˣ)]
    {p c : ℕ} {J : Fin c → Ideal O} {n : Fin c → ℕ}
    (C : pSaturatedClassGroupCertificateDvdT p J n) :
    ∀ r : Fin c → ℕ, ∀ b : O, ∏ i, (J i) ^ (r i) = Ideal.span {b} →
      (∀ i, n i ∣ p * (r i)) → ∀ i, n i ∣ r i := by
  intro r b hrb hib
  haveI : Fact $ Nat.Prime p := {out := C.hp}
  have aux : ∀ (i : Fin C.r ⊕ Fin 1), IsUnit (Sum.elim C.u (fun x ↦ C.v) i) := by
      intro i
      rcases i with i | j
      · simp [C.hu]
      · exact IsUnit.of_pow_eq_one C.hmv C.hm
  refine pSaturated_of_full_rank_matrixLogZMod (hF := C.hqP) C.hcard C.hr
    (Sum.elim C.u (fun (_ : Fin 1) => C.v)) aux
    ?_ C.hdvd J C.a n C.ψ ?_ ?_ ?_ C.h ?_ r b hrb hib
  · intro w
    obtain ⟨e, t, h1⟩ := units_of_pMaximalUnitsCertificateDvdT C.topMaximalUnitsCertificateDvdT w
    obtain ⟨e',h1, t', h2 ⟩ := (nat_up_to_power_of_int_up_to_power (w := w) aux
      (Ne.symm (NeZero.ne' p)) e t (by rw [h1]; simp))
    use e' , t'
  · intro i hi
    use C.iψ i
    exact C.hψ i hi
  · intro i j
    rw [apply_map_ZMod (hq := C.hqP i) _]
    exact C.hDl i j
  · intro j hj
    refine C.hψn j ?_
    by_contra hc
    simp only [Finset.mem_compl, Finset.mem_image, Finset.mem_univ, true_and, not_exists] at hj
    exact  hj (C.iψ j) (C.hψ j hc)
  · rw [← matrix_of_NonPrincipalCertificateDvdT C]
    refine le_antisymm ?_ ?_
    · convert (Matrix.rank_le_card_width) _
      rfl
      simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unique]
      infer_instance
    · rw [Matrix.rank_reindex ]
      rw [← Matrix.rank_reindex (Equiv.refl _) ((finSumFinEquiv.trans (finCongr C.hc.symm)))]
      refine le_of_eq_of_le ?_ (Matrix.rank_mul_le_left _ C.NInv)
      rw [C.hN]
      simp only [Fintype.card_fin, Matrix.rank_one, C.hc]
      simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unique]


-- Note that proofs of `I^n = ⟨a⟩` are already included in the certificates for `p`
-- (but `n` might be `1`, so no `p`-certificate).

/-- An isomorphism between the class group and an explicit finite group from
  certificates of `p`-saturation at every prime.  -/
noncomputable def ClassGroup_equiv_of_pSaturatedCertificate  {O : Type*} [CommRing O]
    [IsDomain O] [IsDedekindDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
    [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))] [IsCyclic (CommGroup.torsion Oˣ)]
    {c : ℕ} {J : Fin c → Ideal O} {n : Fin c → ℕ} [∀ i, NeZero (n i)]
    {J' : Fin c → nonZeroDivisors (Ideal O)} (hJ' : ∀ i, ↑(J' i) = J i)
    {a : Fin c → O} (h : ∀ i, (J i) ^ (n i) = Ideal.span {a i})
    (hgen : Subgroup.closure (Set.range (fun i => ClassGroup.mk0 (J' i))) = ⊤)
    (C : ∀ (p : { p  // Nat.Prime p ∧ p ∣ ∏ i, n i}) ,
    (pSaturatedClassGroupCertificateDvdT p J n) ⊕ (pSaturatedClassGroupCertificateNDvdT p J n) ) :
    (∀ i : Fin c , (ZMod (n i))) ≃+ Additive (ClassGroup O) := by
  refine equivClassGroupOfSaturated hJ' h hgen ?_
  intro p hp hpdvd r b hr hdvd
  let C' := C ⟨p, ⟨hp, hpdvd⟩⟩
  cases C' with
  | inl C => exact pSaturated_of_CertificateDvdT C r b hr hdvd
  | inr C => exact pSaturated_of_CertificateNDvdT C r b hr hdvd



---------------------------------------------------------------------------------------------------

-- For principal ideals. Deprecated because we can just use p-saturation certificate for
-- a single ideal.


-- Dirichlet Unit theorem applies to orders of K, so we make this
-- certificate more general.
/- structure NonPrincipalCertificateNDvdT {O : Type*} [CommRing O]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))] (J : Ideal O) where
 p : ℕ
 hp : Nat.Prime p
 r : ℕ -- rank of the unit group
 huc : Module.finrank ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ))) ≤ r
 u : Fin r → O
 hu : ∀ (i : Fin r), IsUnit (u i)
 q : Fin (r + 1) → ℕ -- List of prime norms
 hqP : ∀ i, Fact (Nat.Prime (q i))
 I : Fin (r + 1) → Ideal O -- Corresponding list of ideals (advantage of degree 1: we dont have to prove they are prime)
 hcard : ∀ j, Nat.card (O ⧸ I j) = q j
 ζ : Fin (r + 1) → ℕ
 hr : ∀ i, IsPrimitiveRoot (ζ i : ZMod (q i)) (q i - 1)
 hdvd : ∀ i, p ∣ q i - 1
 a : O
 n : ℕ -- Power to raise the ideal (usually prime)
 hpdvd : p ∣ n
 hJ : J ^ n = Ideal.span {a}
 hpndvdt : ¬p ∣ Nat.card (CommGroup.torsion Oˣ)
 M : Matrix (Fin (r + 1)) (Fin (r + 1)) (ZMod p)
 hM1 : ∀ i, ∀ hj : j < r , M i j = LogFiniteZMod (hcard i) (hr i) p (u ⟨j, hj⟩) -- First columns of the matrix
 hM2 : ∀ i , DiscreteLogCertificate (hcard i) (hr i) p a (M i r) -- Last column of the matrix. The certificate contains discrete log info.
 hDl : ∀ i, ((hM2 i).m : ZMod (q i)) ≠ 0
 Minv : Matrix (Fin (r + 1)) (Fin (r + 1)) (ZMod p)
 hInv : M * Minv = 1
 N : Matrix (Fin r) (Fin r) (ZMod p)
 hNiv : (M.submatrix (Fin.castSucc) (Fin.castSucc)) * N = 1
 -- Order the prime ideals q i in such a way that removing the last row and column induce an
 -- invertible matrix.


lemma matrix_of_NonPrincipalCertificateNDvdT {O : Type*} [CommRing O]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))] {J : Ideal O}
  (C : NonPrincipalCertificateNDvdT J) :
    Matrix.reindex (Equiv.refl _) (finSumFinEquiv).symm C.M  =
      (MatrixLogZMod C.p (hF := C.hqP) C.hcard
      (Sum.elim (fun i => C.u i) (fun (_ : Fin 1) => C.a)) C.hr) := by
    ext i j
    rcases j with j | k
    · simp [MatrixLog_eq, MatrixLogZMod]
      convert C.hM1 i j.2
      rw [Fin.coe_eq_castSucc]
      rfl
    · simp [MatrixLog_eq, MatrixLogZMod]
      haveI : Fact $ Nat.Prime (C.q i) := C.hqP i
      rw [eq_of_DiscreteLogCertificate (C.hM2 i)]
      simp only [Fin.natAdd, Fin.val_eq_zero, add_zero, Fin.natCast_eq_last]
      rfl

lemma submatrix_of_NonPrincipalCertificateNDvdT {O : Type*} [CommRing O]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))] {J : Ideal O}
  (C : NonPrincipalCertificateNDvdT J) :
    C.M.submatrix (Fin.castSucc) (Fin.castSucc)  =
      (MatrixLogZMod C.p (hF := fun i : Fin C.r => C.hqP i)
        (fun i => C.hcard i) C.u (fun i => C.hr i)) := by
    ext i j
    simp [MatrixLog_eq, MatrixLogZMod]
    convert C.hM1 i j.2
    repeat {simp}

lemma units_linear_independent_of_NonPrincipalCertificateNDvdT {O : Type*} [CommRing O]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))] {J : Ideal O}
  (C : NonPrincipalCertificateNDvdT J) :
LinearIndependent ℤ (fun i => Additive.ofMul (QuotientGroup.mk (s := (CommGroup.torsion Oˣ)) (C.hu i).unit)) := by
  haveI : Fact $ Nat.Prime C.p := {out := C.hp}
  refine units_linear_independent_not_dvd_torsion_of_full_rank (hF := fun i : Fin C.r => C.hqP i)  (fun i => C.hcard i)
    (fun i => C.hr i) C.u C.hu (fun i => C.hdvd i) C.hpndvdt ?_
  rw [← submatrix_of_NonPrincipalCertificateNDvdT C]
  refine le_antisymm ?_ ?_
  · convert (Matrix.rank_le_card_width) _
    exact strongRankCondition_of_orzechProperty (ZMod C.p)
  · refine le_of_eq_of_le ?_ (Matrix.rank_mul_le_left _ C.N)
    rw [C.hNiv]
    simp only [Fintype.card_fin, Matrix.rank_one]


lemma units_of_NonPrincipalCertificateNDvdT {O : Type*} [CommRing O]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))] {J : Ideal O}
  (C : NonPrincipalCertificateNDvdT J) (w : Oˣ) :
  ∃ (e' : Fin C.r → ℤ), (∃ (t : Oˣ) , w = (∏ i, ((C.hu i).unit) ^ (e' i)) * t ^ C.p) := by
  haveI : Fact $ Nat.Prime C.p := {out := C.hp}
  refine units_up_to_p_power_not_dvd_torsion_of_full_rank (hF := fun i : Fin C.r => C.hqP i)
    (fun i => C.hcard i)
    (fun i => C.hr i) C.u C.hu (fun i => C.hdvd i) C.hpndvdt ?_ ?_ w
  rw [← submatrix_of_NonPrincipalCertificateNDvdT C]
  refine le_antisymm ?_ ?_
  · convert (Matrix.rank_le_card_width) _
    exact strongRankCondition_of_orzechProperty (ZMod C.p)
  · refine le_of_eq_of_le ?_ (Matrix.rank_mul_le_left _ C.N)
    rw [C.hNiv]
    simp only [Fintype.card_fin, Matrix.rank_one]
  simp
  exact C.huc

lemma not_principal_of_NonPrincipalCertificateNDvdT  {O : Type*} [CommRing O]
    [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
    [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))] {J : Ideal O}
    (C : NonPrincipalCertificateNDvdT J) : ¬ ∃ b, J = Ideal.span {b} := by
  haveI : Fact $ Nat.Prime C.p := {out := C.hp}
  refine not_principal_of_full_rank_matrixLogZMod (hF := C.hqP) C.hcard C.hr C.u C.hu
    ?_ C.hdvd J C.a ?_ C.hpdvd C.hJ ?_
  · intro w
    obtain ⟨e, t, h1⟩ := units_of_NonPrincipalCertificateNDvdT C w
    obtain ⟨e',h1, t', h2 ⟩ := (nat_up_to_power_of_int_up_to_power C.hu (Ne.symm (NeZero.ne' C.p)) e t h1)
    use e' , t'
  · intro i
    rw [apply_map_ZMod (hq := C.hqP i) (C.hM2 i)]
    exact C.hDl i
  · rw [← matrix_of_NonPrincipalCertificateNDvdT C]
    refine le_antisymm ?_ ?_
    · convert (Matrix.rank_le_card_width) _
      simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unique]
      exact strongRankCondition_of_orzechProperty (ZMod C.p)
    · rw [Matrix.rank, Matrix.mulVecLin_reindex, LinearMap.range_comp, LinearMap.range_comp,
      LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq, ← Matrix.rank]
      refine le_of_eq_of_le ?_ (Matrix.rank_mul_le_left _ C.Minv)
      rw [C.hInv]
      simp only [Fintype.card_fin, Matrix.rank_one]

-- Why include elements of O instead of coordinates for this elements?
-- Because I want to reuse my units, so i want to define them beforehand. Proofs would be
-- repetitive if I do all computations within the structure.

structure NonPrincipalCertificateDvdT {O : Type*} [CommRing O]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [IsCyclic (CommGroup.torsion Oˣ)] (J : Ideal O) where
p : ℕ
hp : Nat.Prime p
r : ℕ -- rank of the unit group
huc : Module.finrank ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ))) ≤ r
u : Fin r → O -- generators of the unit group mod torsion (mod p-powers)
hu : ∀ (i : Fin r), IsUnit (u i)
v : O -- Generator of the torsion group (mod p-powers)
m : ℕ
hm : m ≠ 0
hmv : v ^ m = 1 -- v is a torsion unit. Insetad of proving this directly,
  --you could, for each prime power dividing m, give elements that order and consider the product. Or just use square and multiply.
q : Fin (r + 1 + 1) → ℕ -- List of prime norms
hqP : ∀ i, Fact (Nat.Prime (q i))
I : Fin (r + 1 + 1) → Ideal O -- Corresponding list of prime ideals
hcard : ∀ j, Nat.card (O ⧸ I j) = q j
ζ : Fin (r + 1 + 1) → ℕ
hr : ∀ i, IsPrimitiveRoot (ζ i : ZMod (q i)) (q i - 1)
hdvd : ∀ i, p ∣ q i - 1
a : O
n : ℕ -- Power to raise the ideal (usually prime)
hpdvd : p ∣ n
hJ : J ^ n = Ideal.span {a}
M : Matrix (Fin (r + 1 + 1)) (Fin (r + 1 + 1)) (ZMod p)
hM1 : ∀ i, ∀ hj : j < r , M i j = LogFiniteZMod (hcard i) (hr i) p (u ⟨j, hj⟩) -- First columns of the matrix
hM2 : ∀ i, M i r = LogFiniteZMod (hcard i) (hr i) p v
hM3 : ∀ i , DiscreteLogCertificate (hcard i) (hr i) p a (M i (r + 1)) -- Last column of the matrix. The certificate contains discrete log info.
hDl : ∀ i, ((hM3 i).m : ZMod (q i)) ≠ 0
Minv : Matrix (Fin (r + 1 + 1)) (Fin (r + 1 + 1)) (ZMod p)
hInv : M * Minv = 1
N : Matrix (Fin (r + 1)) (Fin (r + 1)) (ZMod p)
hNiv : (M.submatrix (Fin.castSucc) (Fin.castSucc)) * N = 1


lemma torsion_of_NonPrincipalCertificateDvdT {O : Type*} [CommRing O]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [IsCyclic (CommGroup.torsion Oˣ)] {J : Ideal O} (C : NonPrincipalCertificateDvdT J) :
  ∀ w ∈ CommGroup.torsion Oˣ, (∃ (a : ℤ) , (∃ t ∈ CommGroup.torsion Oˣ ,
    w = ((IsUnit.of_pow_eq_one C.hmv C.hm).unit ^ a * t ^ C.p))) := by
  haveI : Fact $ Nat.Prime C.p := {out := C.hp }
  have hvmem : (IsUnit.of_pow_eq_one C.hmv C.hm).unit ∈ CommGroup.torsion Oˣ := by
    rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    use C.m
    constructor
    · exact Nat.pos_of_ne_zero C.hm
    · rw [Units.ext_iff]
      simp [C.hmv]
  intro w hwmem
  obtain ⟨⟨g, hgmem⟩ , hg ⟩ := exists_zpow_surjective (CommGroup.torsion Oˣ)
  obtain ⟨r, hr⟩ := hg ⟨w, hwmem⟩
  obtain ⟨t, ht⟩ := hg ⟨_, hvmem⟩
  rw [← Subtype.val_inj] at hr ht
  simp at hr ht
  haveI := C.hqP
  have hnz : ∃ i, LogFiniteZMod (C.hcard i) (C.hr i) C.p C.v ≠ 0 := by
    by_contra! h
    simp_rw [← C.hM2] at h
    have : (C.Minv *C.M) C.r C.r = 1 := by
      rw [Matrix.mul_eq_one_comm.1 C.hInv]
      simp only [Matrix.one_apply_eq]
    rw [Matrix.mul_apply] at this
    simp only [h, mul_zero, Finset.sum_const_zero, zero_ne_one] at this
  have hC : IsCoprime ↑C.p t := by
    rw [Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp C.hp)]
    rintro ⟨k, hk⟩
    obtain ⟨i, hi⟩ := hnz
    rw [hk, mul_comm, zpow_mul, zpow_natCast, Units.ext_iff] at ht
    simp at ht
    rw [← ht] at hi
    simp [LogFiniteZMod] at hi
    rw [LogFiniteRing_p_power_eq_zero] at hi
    exact hi rfl
    simp only [ZMod.card_units_eq_totient, Nat.totient_prime (C.hqP i).out]
    exact C.hdvd i
  obtain ⟨b, a, hab⟩ := hC
  use r * a , g ^ (r * b)
  constructor
  · exact Subgroup.zpow_mem (CommGroup.torsion Oˣ) hgmem _
  · rw [← ht, ← zpow_mul, ← zpow_natCast, ← zpow_mul,
      ← zpow_add, add_comm, mul_comm t _, ← hr]
    nth_rw 1 [← mul_one r, ← hab]
    congr
    ring

lemma matrix_of_NonPrincipalCertificateDvdT {O : Type*} [CommRing O]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [IsCyclic (CommGroup.torsion Oˣ)] {J : Ideal O}
  (C : NonPrincipalCertificateDvdT J) :
    Matrix.reindex (Equiv.refl _) (Equiv.trans (finSumFinEquiv.symm)
      (Equiv.sumCongr (finSumFinEquiv.symm) (Equiv.refl _))) C.M  =
      (MatrixLogZMod C.p (hF := C.hqP) C.hcard
      (Sum.elim (Sum.elim (C.u) (fun (_ : Fin 1) => C.v)) (fun (_ : Fin 1) => C.a)) C.hr) := by
    ext i j
    rcases j with (j | j') | k
    · simp [MatrixLog_eq, MatrixLogZMod]
      convert C.hM1 i j.2
      rw [← Fin.val_inj]
      simp only [Fin.coe_castAdd, Fin.val_cast_of_lt (show (j < C.r + 1 + 1) by omega) ]
    · simp [MatrixLog_eq, MatrixLogZMod]
      convert C.hM2 i
      rw [← Fin.val_inj]
      simp only [Fin.coe_castAdd, Fin.coe_natAdd, Fin.val_eq_zero, add_zero,
        Fin.val_cast_of_lt (show (C.r < C.r + 1 + 1) by omega) ]
    · simp [MatrixLog_eq, MatrixLogZMod]
      haveI : Fact $ Nat.Prime (C.q i) := C.hqP i
      rw [eq_of_DiscreteLogCertificate (C.hM3 i)]
      congr 1
      rw [← Fin.val_inj]
      have : (↑C.r : Fin (C.r + 1 + 1)) + 1 = ↑(C.r + 1) := by
        exact Eq.symm (Mathlib.Tactic.Ring.inv_add rfl rfl)
      rw [this]
      rw [Fin.val_cast_of_lt (show (C.r + 1 < C.r + 1 + 1) by omega)]
      simp only [Fin.coe_natAdd, Fin.val_eq_zero, add_zero]


lemma submatrix_of_NonPrincipalCertificateDvdT {O : Type*} [CommRing O]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [IsCyclic (CommGroup.torsion Oˣ)] {J : Ideal O}
  (C : NonPrincipalCertificateDvdT J) :
    C.M.submatrix (Fin.castSucc) ((Fin.castSucc) ∘ (finSumFinEquiv).toFun)  =
      (MatrixLogZMod C.p (hF := fun i : Fin (C.r + 1) => C.hqP i)
        (fun i => C.hcard i) (Sum.elim C.u (fun (_ : Fin 1) => C.v)) (fun i => C.hr i)) := by
    ext i j
    rcases j with j | r
    · simp [MatrixLog_eq, MatrixLogZMod]
      convert C.hM1 i j.2 using 2
      simp only [Fin.coe_eq_castSucc]
      rw [← Fin.coe_eq_castSucc]
      repeat {simp}
    · simp [MatrixLog_eq, MatrixLogZMod]
      convert C.hM2 i
      simp only [Fin.coe_eq_castSucc]
      rw [← Fin.coe_eq_castSucc]
      repeat {simp}


lemma units_linear_independent_of_NonPrincipalCertificateDvdT {O : Type*} [CommRing O]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [IsCyclic (CommGroup.torsion Oˣ)] {J : Ideal O}
  (C : NonPrincipalCertificateDvdT J) :
  LinearIndependent ℤ (fun i => Additive.ofMul (QuotientGroup.mk (s := (CommGroup.torsion Oˣ)) (C.hu i).unit)) := by
  haveI : Fact $ Nat.Prime C.p := {out := C.hp}
  refine units_linear_independent_dvd_torsion_of_full_rank (hF := fun i : Fin (C.r + 1) => C.hqP i) (fun i => C.hcard i) (fun i => C.hr i) C.u C.hu (fun i => C.hdvd i) (fun (i : Fin 1) => C.v) ?_ ?_ ?_
  · intro i
    exact (IsUnit.of_pow_eq_one C.hmv C.hm)
  · intro w' hwmem'
    obtain ⟨a, t, htmem, hat⟩ := torsion_of_NonPrincipalCertificateDvdT C w' hwmem'
    use a, t, htmem
    rw [hat]
    simp
  rw [← submatrix_of_NonPrincipalCertificateDvdT C]
  refine le_antisymm ?_ ?_
  · convert (Matrix.rank_le_card_width) _
    simp only [Fintype.card_fin, Fintype.card_unique, Fintype.card_sum]
    exact strongRankCondition_of_orzechProperty (ZMod C.p)
  · erw [← Matrix.submatrix_submatrix C.M (Fin.castSucc )
      (Fin.castSucc ) (Equiv.refl _).toFun (finSumFinEquiv.toFun)]
    erw [← Matrix.reindex_apply (Equiv.refl _).symm (finSumFinEquiv).symm]
    rw [Matrix.rank, Matrix.mulVecLin_reindex, LinearMap.range_comp, LinearMap.range_comp,
      LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq, ← Matrix.rank]
    refine le_of_eq_of_le ?_ (Matrix.rank_mul_le_left _ C.N)
    rw [C.hNiv]
    simp only [Fintype.card_fin, Matrix.rank_one]


lemma units_of_NonPrincipalCertificateDvdT {O : Type*} [CommRing O]
  [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
  [IsCyclic (CommGroup.torsion Oˣ)] {J : Ideal O}
  (C : NonPrincipalCertificateDvdT J) (w : Oˣ) :
  ∃ (e' : (Fin C.r) ⊕ (Fin 1) → ℤ), (∃ (t : Oˣ) , w = (∏ (i : (Fin C.r) ⊕ (Fin 1)),
    (Sum.elim (fun i => (C.hu i).unit)
    (fun _ => (IsUnit.of_pow_eq_one C.hmv C.hm).unit) i) ^ (e' i)) * t ^ C.p) := by
  haveI : Fact $ Nat.Prime C.p := {out := C.hp}
  refine units_up_to_p_power_dvd_torsion_of_full_rank (hF := fun i : Fin (C.r + 1) => C.hqP i)
    (fun i => C.hcard i) (fun i => C.hr i) C.u C.hu (fun i => C.hdvd i)
      (fun (i : Fin 1) => C.v) _ ?_ ?_ ?_ w
  · intro w' hwmem'
    obtain ⟨a, t, htmem, hat⟩ := torsion_of_NonPrincipalCertificateDvdT C w' hwmem'
    use a, t, htmem
    rw [hat]
    simp
  rw [← submatrix_of_NonPrincipalCertificateDvdT C]
  refine le_antisymm ?_ ?_
  · convert (Matrix.rank_le_card_width) _
    simp only [Fintype.card_fin, Fintype.card_unique, Fintype.card_sum]
    exact strongRankCondition_of_orzechProperty (ZMod C.p)
  · erw [← Matrix.submatrix_submatrix C.M (Fin.castSucc )
      (Fin.castSucc ) (Equiv.refl _).toFun (finSumFinEquiv.toFun)]
    erw [← Matrix.reindex_apply (Equiv.refl _).symm (finSumFinEquiv).symm]
    rw [Matrix.rank, Matrix.mulVecLin_reindex, LinearMap.range_comp, LinearMap.range_comp,
      LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq, ← Matrix.rank]
    refine le_of_eq_of_le ?_ (Matrix.rank_mul_le_left _ C.N)
    rw [C.hNiv]
    simp only [Fintype.card_fin, Matrix.rank_one]
  · simp [C.huc]


lemma not_principal_of_NonPrincipalCertificateDvdT  {O : Type*} [CommRing O]
    [IsDomain O] [Module.Finite ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
    [Module.Free ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ)))]
    [IsCyclic (CommGroup.torsion Oˣ)] {J : Ideal O}
    (C : NonPrincipalCertificateDvdT J) : ¬ ∃ b, J = Ideal.span {b} := by
  have aux : ∀ (i : Fin C.r ⊕ Fin 1), IsUnit (Sum.elim C.u (fun x ↦ C.v) i) := by
    intro i
    rcases i with i | j
    · simp [C.hu]
    · exact IsUnit.of_pow_eq_one C.hmv C.hm
  haveI : Fact $ Nat.Prime C.p := {out := C.hp}
  refine not_principal_of_full_rank_matrixLogZMod (hF := C.hqP) C.hcard C.hr
    (Sum.elim C.u (fun (_ : Fin 1) => C.v)) ?_
    ?_ C.hdvd J C.a ?_ C.hpdvd C.hJ ?_
  · exact aux
  · intro w
    obtain ⟨e, t, h1⟩ := units_of_NonPrincipalCertificateDvdT C w
    obtain ⟨e',h1, t', h2 ⟩ := (nat_up_to_power_of_int_up_to_power (w := w) aux
      (Ne.symm (NeZero.ne' C.p)) e t (by rw [h1]; simp))
    use e' , t'
  · intro i
    rw [apply_map_ZMod (hq := C.hqP i) (C.hM3 i)]
    exact C.hDl i
  · rw [← matrix_of_NonPrincipalCertificateDvdT C]
    refine le_antisymm ?_ ?_
    · convert (Matrix.rank_le_card_width) _
      simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unique]
      exact strongRankCondition_of_orzechProperty (ZMod C.p)
    · rw [Matrix.rank, Matrix.mulVecLin_reindex, LinearMap.range_comp, LinearMap.range_comp,
      LinearEquiv.range, Submodule.map_top, LinearEquiv.finrank_map_eq, ← Matrix.rank]
      refine le_of_eq_of_le ?_ (Matrix.rank_mul_le_left _ C.Minv)
      rw [C.hInv]
      simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unique, Matrix.rank_one] -/
