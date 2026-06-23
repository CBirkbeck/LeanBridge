/-
Copyright (c) 2026 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

module

import Mathlib.Algebra.QuadraticAlgebra.Basic

namespace QuadraticAlgebra

variable {R S : Type*} [CommSemiring R] [CommRing S] [Algebra R S]

instance (a b : R) : Algebra (QuadraticAlgebra R a b)
    (QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)) :=
  (lift ⟨ω, by simpa using
    omega_mul_omega_eq_add (a := algebraMap R S a) (b := algebraMap R S b)⟩).toRingHom.toAlgebra

@[simp] lemma algebraMap_omega (a b : R) : algebraMap (QuadraticAlgebra R a b)
    (QuadraticAlgebra S (algebraMap R S a) (algebraMap R S b)) ω = ω := by
  change (lift ⟨ω, by simpa using
    omega_mul_omega_eq_add (a := algebraMap R S a) (b := algebraMap R S b)⟩) ω = ω
  simp [lift]

instance (a b : ℤ) : Algebra (QuadraticAlgebra ℤ a b) (QuadraticAlgebra S a b) :=
  (lift ⟨ω, by simpa [Int.cast_smul_eq_zsmul] using
    omega_mul_omega_eq_add (R := S) (a := a) (b := b)⟩).toRingHom.toAlgebra

@[simp] lemma algebraMap_omega' (a b : ℤ) : algebraMap (QuadraticAlgebra ℤ a b)
    (QuadraticAlgebra S a b) ω = ω := by
  simpa using algebraMap_omega (S := S) a b

instance (a : ℤ) : Algebra (QuadraticAlgebra ℤ a 0) (QuadraticAlgebra S a 0) :=
  (lift ⟨ω, by simpa [Int.cast_smul_eq_zsmul] using
    omega_mul_omega_eq_add (R := S) (a := a) (b := 0)⟩).toRingHom.toAlgebra

@[simp] lemma algebraMap_omega'' (a : ℤ) : algebraMap (QuadraticAlgebra ℤ a 0)
    (QuadraticAlgebra S a 0) ω = ω := by
  change (lift ⟨ω, by simpa [Int.cast_smul_eq_zsmul] using
    omega_mul_omega_eq_add (R := S) (a := a) (b := 0)⟩) ω = ω
  simp [lift]

instance (a : ℕ) [a.AtLeastTwo] :
    Algebra (QuadraticAlgebra ℤ ofNat(a) 0) (QuadraticAlgebra S ofNat(a) 0) :=
  (lift ⟨ω, by simpa [ofNat_smul_eq_nsmul] using
    omega_mul_omega_eq_add (R := S) (a := (ofNat(a) : S)) (b := 0)⟩).toRingHom.toAlgebra

@[simp] lemma algebraMap_omega''' (a : ℕ) [a.AtLeastTwo] :
    algebraMap (QuadraticAlgebra ℤ ofNat(a) 0) (QuadraticAlgebra S ofNat(a) 0) ω = ω := by
  change (lift ⟨ω, by simpa [ofNat_smul_eq_nsmul] using
    omega_mul_omega_eq_add (R := S) (a := (ofNat(a) : S)) (b := 0)⟩) ω = ω
  simp [lift]

instance : Algebra (QuadraticAlgebra ℤ 0 0) (QuadraticAlgebra S 0 0) :=
  (lift ⟨ω, by simpa using
    omega_mul_omega_eq_add (R := S) (a := (0 : S)) (b := 0)⟩).toRingHom.toAlgebra

@[simp] lemma algebraMap_omega_zero :
    algebraMap (QuadraticAlgebra ℤ 0 0) (QuadraticAlgebra S 0 0) ω = ω := by
  change (lift ⟨ω, by simpa using
    omega_mul_omega_eq_add (R := S) (a := (0 : S)) (b := 0)⟩) ω = ω
  simp [lift]

instance : Algebra (QuadraticAlgebra ℤ 1 0) (QuadraticAlgebra S 1 0) :=
  (lift ⟨ω, by simpa using
    omega_mul_omega_eq_add (R := S) (a := (1 : S)) (b := 0)⟩).toRingHom.toAlgebra

@[simp] lemma algebraMap_omega_one :
    algebraMap (QuadraticAlgebra ℤ 1 0) (QuadraticAlgebra S 1 0) ω = ω := by
  change (lift ⟨ω, by simpa using
    omega_mul_omega_eq_add (R := S) (a := (1 : S)) (b := 0)⟩) ω = ω
  simp [lift]

instance : Algebra (QuadraticAlgebra ℤ (-1) 0) (QuadraticAlgebra S (-1) 0) :=
  (lift ⟨ω, by simpa [neg_one_smul] using
    omega_mul_omega_eq_add (R := S) (a := (-1 : S)) (b := 0)⟩).toRingHom.toAlgebra

@[simp] lemma algebraMap_omega_neg_one :
    algebraMap (QuadraticAlgebra ℤ (-1) 0) (QuadraticAlgebra S (-1) 0) ω = ω := by
  change (lift ⟨ω, by simpa [neg_one_smul] using
    omega_mul_omega_eq_add (R := S) (a := (-1 : S)) (b := 0)⟩) ω = ω
  simp [lift]

instance (a : ℕ) [a.AtLeastTwo] :
    Algebra (QuadraticAlgebra ℤ (-ofNat(a)) 0) (QuadraticAlgebra S (-ofNat(a)) 0) :=
  (lift ⟨ω, by simpa [neg_smul, ofNat_smul_eq_nsmul] using
    omega_mul_omega_eq_add (R := S) (a := (-ofNat(a) : S)) (b := 0)⟩).toRingHom.toAlgebra

@[simp] lemma algebraMap_omega_neg_ofNat (a : ℕ) [a.AtLeastTwo] :
    algebraMap (QuadraticAlgebra ℤ (-ofNat(a)) 0) (QuadraticAlgebra S (-ofNat(a)) 0) ω = ω := by
  change (lift ⟨ω, by simpa [neg_smul, ofNat_smul_eq_nsmul] using
    omega_mul_omega_eq_add (R := S) (a := (-ofNat(a) : S)) (b := 0)⟩) ω = ω
  simp [lift]

end QuadraticAlgebra
