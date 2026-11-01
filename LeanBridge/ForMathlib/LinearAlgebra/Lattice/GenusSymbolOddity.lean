import LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusLabelCanonical

/-!
# The oddities of the compartments of the canonical `2`-adic symbol

In the canonical `2`-adic symbol of Conway and Sloane (LMFDB `lattice.conway_genus_symbol`;
*Sphere Packings, Lattices and Groups*, Chapter 15, §7.3–7.6), formalised in
`LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolCanonical`, every compartment carries an
oddity: the total oddity of its constituents plus `4` for every sign walk that touches it. The signs
of the trains are genus invariants
(`LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolStopSign`); this file reduces the genus
invariance of the oddities of the compartments to that of the following partial-sum invariants.

For a Jordan decomposition `⊕_q q f_q` over the powers `q = 2 ^ k` and a scale `2 ^ m`, the
*Gauss oddity* `Θ_m` is the oddity of `2 ^ m` times the partial sum `⊕_(q < 2 ^ m) q f_q`, that is
`Σ_(k < m) (t_q + 4 [ε_q = -1] [m - k odd]) mod 8` with the oddities `t_q` and the signs `ε_q` of
the constituents. When the constituent of scale `2 ^ m` has type `II` (zero constituents included),
the Gauss sum `Σ_(x ∈ L ⊗ ℤ_2 / 2 ^ m) exp(2 π i x² / 2 ^ (m + 1))` is `ζ₈ ^ Θ_m` times a positive
real, so that `Θ_m` is an isometry invariant of the dyadic localization and a genus invariant; this
classical fact enters the results below as a hypothesis, and is proved in
`LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolGaussSum`
(`TauCeti.IntegralLattice.SameGenus.dyadicGaussOddity_eq`), where the results are unconditional.

The main result is that the oddities of the compartments of the canonical symbol are determined by
the scales and types of the constituents, the signs of the trains and the Gauss oddities at the
scales without constituent of type `I`. A compartment `C`, of scales `2 ^ a, …, 2 ^ b`, has oddity
`Θ_(b + 1) - Θ_(a - 1)` (with `Θ_(-1) = 0`) up to `4` times terms in the sign products below stops
and the signs of the trains. The proof is an induction on the constituents from the smallest scale:
prepending a constituent to a symbol changes the canonical oddities of at most two compartments, by
its oddity and by the sign walk between it and the next constituent
(`TauCeti.IntegralLattice.DyadicBlock.map_canonicalOddity_cons_cons`). For a lattice, the
oddities of the compartments of its canonical `2`-adic symbol, and so its label (LMFDB
`lattice.genus_label`), are genus invariants as soon as the Gauss oddities are, which they are
(`LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolGaussSum`).

## Main definitions

* `TauCeti.IntegralLattice.DyadicBlock.gaussOddity` (LMFDB `lattice.conway_genus_symbol`): the
  Gauss oddity `Θ_m` of a `2`-adic symbol.
* `TauCeti.IntegralLattice.dyadicGaussOddity` (LMFDB `lattice.conway_genus_symbol`): the Gauss
  oddity `Θ_m` of a lattice, read off its chosen dyadic Jordan splitting.
* `TauCeti.IntegralLattice.DyadicBlock.consWalk`, `TauCeti.IntegralLattice.DyadicBlock.signOddity`
  and `TauCeti.IntegralLattice.DyadicBlock.parityOddity`: auxiliary quantities of the proof.

## Main results

* `TauCeti.IntegralLattice.DyadicBlock.map_canonicalOddity_cons_cons`: the canonical oddities of the
  compartments after prepending a constituent.
* `TauCeti.IntegralLattice.DyadicBlock.map_canonicalOddity_eq_of_gaussOddity_eq`: the oddities of
  the compartments are determined by the scales, the types, the signs of the trains and the Gauss
  oddities.
* `TauCeti.IntegralLattice.dyadicGaussOddity_eq_sum`: the Gauss oddity of a lattice is the sum
  over all the scales below `2 ^ m`.
* `TauCeti.IntegralLattice.SameGenus.compartmentOddities_eq_of_dyadicGaussOddity_eq`: the oddities
  of the compartments of the canonical `2`-adic symbol are genus invariants once the Gauss oddities
  are.
* `TauCeti.IntegralLattice.SameGenus.canonicalGenusLabel_eq_of_dyadicGaussOddity_eq`: so is the
  label of the genus.
-/

open List

open LinearMap (BilinForm)

namespace TauCeti.IntegralLattice

namespace DyadicBlock

variable {a b x x' z : DyadicBlock} {l l' t t' C T : List DyadicBlock}
  {p : DyadicBlock × DyadicBlock} (r : DyadicBlock → DyadicBlock → Bool) (u v : ℤ) (m B : ℕ)

lemma signWalks_cons_cons : signWalks (a :: b :: T) =
    (if trainSign (b :: T) = -1 then [(a, b)] else []) ++ signWalks (b :: T) := by
  by_cases h : trainSign (b :: T) = -1 <;> simp [signWalks, h]

lemma mem_of_mem_splitBy (hT : T ∈ l.splitBy r) (hz : z ∈ T) : z ∈ l := by
  rw [← List.flatten_splitBy r l]
  exact List.mem_flatten.mpr ⟨T, hT, hz⟩

variable (b l) in
lemma exists_splitBy_eq_cons_cons : ∃ T G, (b :: l).splitBy r = (b :: T) :: G := by
  rcases h : (b :: l).splitBy r with _ | ⟨T, G⟩
  · exact absurd h (List.splitBy_ne_nil.mpr (List.cons_ne_nil b l))
  · have hT : T ≠ [] := List.ne_nil_of_mem_splitBy (h ▸ List.mem_cons_self)
    have hflat : T ++ G.flatten = b :: l := by
      rw [← List.flatten_cons, ← h, List.flatten_splitBy]
    rcases T with _ | ⟨c, T⟩
    · exact absurd rfl hT
    · rw [List.cons_append, List.cons.injEq] at hflat
      exact ⟨T, G, by rw [hflat.1]⟩

lemma flatMap_signWalks_trains_cons_cons : (trains (a :: b :: l)).flatMap signWalks =
    (if sameTrain a b = true ∧ trainSign ((trains (b :: l)).headD []) = -1 then [(a, b)] else []) ++
      (trains (b :: l)).flatMap signWalks := by
  rcases exists_splitBy_eq_cons_cons b l sameTrain with ⟨T, G, hTG⟩
  rw [trains_cons_cons, trains, hTG]
  cases sameTrain a b
  · simp [signWalks]
  · simp [signWalks_cons_cons]

lemma mem_zip_of_mem_signWalks (hp : p ∈ signWalks T) : p ∈ T.zip T.tail := by
  rcases List.mem_filterMap.mp hp with ⟨q, hq, hqp⟩
  rw [Option.ite_none_right_eq_some, Option.some_inj] at hqp
  exact hqp.2 ▸ (List.of_mem_zip hq).1

lemma all_type_eq_of_isChain (hb : b.type = .I)
    (h : (b :: T).IsChain fun x y ↦ sameCompartment x y = true) :
    (b :: T).all (·.type == .I) = true := by
  induction T generalizing b with
  | nil => simp [hb]
  | cons c T ih =>
    rw [List.isChain_cons_cons] at h
    have hc : c.type = .I := by
      have h1 : sameCompartment b c = true := h.1
      simp only [sameCompartment, Bool.and_eq_true, beq_iff_eq] at h1
      exact h1.2
    rw [List.all_cons, ih hc h.2]
    simp [hb]

lemma compartments_cons_cons : compartments (a :: b :: l) =
    if sameCompartment a b then (compartments (b :: l)).modifyHead (a :: ·)
    else (if a.type = .I then [[a]] else []) ++ compartments (b :: l) := by
  rcases exists_splitBy_eq_cons_cons b l sameCompartment with ⟨T, G, hTG⟩
  rw [compartments, splitBy_cons_cons, hTG, compartments, hTG]
  cases hab : sameCompartment a b
  · cases ha : a.type <;> simp [ha]
  · have hI : a.type = .I ∧ b.type = .I := by
      simp only [sameCompartment, Bool.and_eq_true, beq_iff_eq] at hab
      exact ⟨hab.1.2, hab.2⟩
    have hall : (b :: T).all (·.type == .I) = true :=
      all_type_eq_of_isChain hI.2 (List.isChain_of_mem_splitBy (by rw [hTG]; exact mem_cons_self))
    simp [hall, hI.1]

variable (a b l) in
/-- The change, `4` or `0`, of the oddities of the compartments containing `a` or `b` brought by
the sign walk between a constituent `a` and the first constituent `b` of the `2`-adic symbol
`b :: l` (LMFDB `lattice.conway_genus_symbol`): `4` when `a` and `b` lie in the same train and the
train of `b` in `b :: l` has sign `-1`. -/
def consWalk : ZMod 8 :=
  if sameTrain a b = true ∧ trainSign ((trains (b :: l)).headD []) = -1 then 4 else 0

lemma ne_of_mem_cons_of_pairwise (hl : (a :: b :: l).Pairwise fun x y ↦ x.scale < y.scale)
    (hx : x ∈ b :: l) : x ≠ a := by
  rintro rfl
  exact lt_irrefl _ (List.rel_of_pairwise_cons hl hx)

lemma fst_mem_of_mem_flatMap_signWalks (hp : p ∈ (trains l).flatMap signWalks) : p.1 ∈ l := by
  rcases List.mem_flatMap.mp hp with ⟨T, hT, hpT⟩
  exact mem_of_mem_splitBy sameTrain hT (List.of_mem_zip (mem_zip_of_mem_signWalks hpT)).1

lemma snd_mem_of_mem_flatMap_signWalks (hp : p ∈ (trains l).flatMap signWalks) : p.2 ∈ l := by
  rcases List.mem_flatMap.mp hp with ⟨T, hT, hpT⟩
  exact mem_of_mem_splitBy sameTrain hT
    (List.mem_of_mem_tail (List.of_mem_zip (mem_zip_of_mem_signWalks hpT)).2)

lemma canonicalOddity_cons_cons (hl : (a :: b :: l).Pairwise fun x y ↦ x.scale < y.scale)
    (hC : ∀ x ∈ C, x ∈ b :: l) : canonicalOddity (a :: b :: l) C = canonicalOddity (b :: l) C +
      if b ∈ C then consWalk a b l else 0 := by
  have ha : a ∉ C := fun h ↦ ne_of_mem_cons_of_pairwise hl (hC a h) rfl
  rw [canonicalOddity, canonicalOddity, flatMap_signWalks_trains_cons_cons, List.countP_append,
    Nat.cast_add, mul_add, add_comm (4 * _), ← add_assoc]
  congr 1
  unfold consWalk
  split_ifs <;> simp_all

lemma canonicalOddity_cons_cons_cons (hl : (a :: b :: l).Pairwise fun x y ↦ x.scale < y.scale) :
    canonicalOddity (a :: b :: l) (a :: C) = a.oddity + consWalk a b l +
      canonicalOddity (b :: l) C := by
  have hW : ((trains (b :: l)).flatMap signWalks).countP (fun p ↦ p.1 ∈ a :: C ∨ p.2 ∈ a :: C) =
      ((trains (b :: l)).flatMap signWalks).countP (fun p ↦ p.1 ∈ C ∨ p.2 ∈ C) := by
    refine List.countP_congr fun p hp ↦ ?_
    have h1 : p.1 ≠ a := ne_of_mem_cons_of_pairwise hl (fst_mem_of_mem_flatMap_signWalks hp)
    have h2 : p.2 ≠ a := ne_of_mem_cons_of_pairwise hl (snd_mem_of_mem_flatMap_signWalks hp)
    simp [h1, h2]
  rw [canonicalOddity, canonicalOddity, flatMap_signWalks_trains_cons_cons, List.countP_append, hW,
    List.map_cons, List.sum_cons, Nat.cast_add, mul_add]
  unfold consWalk
  split_ifs
  · simp only [List.countP_singleton, List.mem_cons_self, true_or, decide_true, ↓reduceIte,
      Nat.cast_one]
    ring1
  · simp only [List.countP_nil, Nat.cast_zero, add_zero]
    ring1

variable (l) in
lemma canonicalOddity_nil : canonicalOddity l [] = 0 := by
  simp [canonicalOddity]

/-- **The canonical oddities of the compartments after prepending a constituent.** If the
constituents of `a :: b :: l` are in strictly increasing order of scale, the compartments of the
canonical `2`-adic symbol `a :: b :: l` are those of `b :: l` with `a` added to the first one if `a`
and `b` lie in the same compartment, or preceded by the compartment `[a]` if `a` has type `I`. The
oddity of the compartment containing `a` gains the oddity of `a`, and the compartments containing
`a` or `b` gain `4` when the sign walk between `a` and `b` takes place. -/
lemma map_canonicalOddity_cons_cons (hl : (a :: b :: l).Pairwise fun x y ↦ x.scale < y.scale) :
    (compartments (a :: b :: l)).map (canonicalOddity (a :: b :: l)) =
      if sameCompartment a b then
        ((compartments (b :: l)).map (canonicalOddity (b :: l))).modifyHead
          (a.oddity + consWalk a b l + ·)
      else (if a.type = .I then [a.oddity + consWalk a b l] else []) ++
        if b.type = .I then
          ((compartments (b :: l)).map (canonicalOddity (b :: l))).modifyHead (consWalk a b l + ·)
        else (compartments (b :: l)).map (canonicalOddity (b :: l)) := by
  rcases exists_splitBy_eq_cons_cons b l sameCompartment with ⟨T, G, hTG⟩
  have hbG (C : List DyadicBlock) (hC : C ∈ G) : b ∉ C := by
    have hflat : (b :: T) ++ G.flatten = b :: l := by
      rw [← List.flatten_cons, ← hTG, List.flatten_splitBy]
    intro hb
    rw [List.cons_append, List.cons.injEq] at hflat
    have hbl : b ∈ l := by
      rw [← hflat.2]
      exact List.mem_append_right T (List.mem_flatten.mpr ⟨C, hC, hb⟩)
    exact lt_irrefl _ (List.rel_of_pairwise_cons hl.of_cons hbl)
  have hsub (C : List DyadicBlock) (hC : C ∈ compartments (b :: l)) (x : DyadicBlock)
      (hx : x ∈ C) : x ∈ b :: l :=
    mem_of_mem_splitBy sameCompartment (List.mem_filter.mp hC).1 hx
  have hcomp (hb : b.type = .I) :
      compartments (b :: l) = (b :: T) :: G.filter (·.all (·.type == .I)) := by
    rw [compartments, hTG, List.filter_cons, ite_eq_left (all_type_eq_of_isChain hb
      (List.isChain_of_mem_splitBy (by rw [hTG]; exact List.mem_cons_self)))]
  have hrest (hb : b.type = .I) :
      (G.filter (·.all (·.type == .I))).map (canonicalOddity (a :: b :: l)) =
        (G.filter (·.all (·.type == .I))).map (canonicalOddity (b :: l)) :=
    List.map_congr_left fun C hC ↦ by
      rw [canonicalOddity_cons_cons hl (hsub C (by rw [hcomp hb]; exact mem_cons_of_mem _ hC)),
        ite_eq_right (hbG C (List.mem_filter.mp hC).1), add_zero]
  have hmapI (hb : b.type = .I) : (compartments (b :: l)).map (canonicalOddity (a :: b :: l)) =
      ((compartments (b :: l)).map (canonicalOddity (b :: l))).modifyHead (consWalk a b l + ·) := by
    rw [hcomp hb, List.map_cons, List.map_cons, List.modifyHead_cons,
      canonicalOddity_cons_cons hl (hsub (b :: T) (by rw [hcomp hb]; exact List.mem_cons_self)),
      ite_eq_left List.mem_cons_self, add_comm, hrest hb]
  have hmapII (hb : b.type ≠ .I) : (compartments (b :: l)).map (canonicalOddity (a :: b :: l)) =
      (compartments (b :: l)).map (canonicalOddity (b :: l)) := by
    refine List.map_congr_left fun C hC ↦ ?_
    have hbC : b ∉ C := fun hbC ↦ hb <| by
      simpa using List.all_eq_true.mp (List.mem_filter.mp hC).2 b hbC
    rw [canonicalOddity_cons_cons hl (hsub C hC), ite_eq_right hbC, add_zero]
  have hnew : canonicalOddity (a :: b :: l) [a] = a.oddity + consWalk a b l := by
    rw [canonicalOddity_cons_cons_cons hl, canonicalOddity_nil, add_zero]
  rw [compartments_cons_cons]
  split_ifs with hab hta htb htb
  · have hb : b.type = .I := by
      simp only [sameCompartment, Bool.and_eq_true, beq_iff_eq] at hab
      exact hab.2
    rw [hcomp hb, List.modifyHead_cons, List.map_cons, List.map_cons, List.modifyHead_cons,
      canonicalOddity_cons_cons_cons hl, hrest hb]
  · rw [List.singleton_append, List.map_cons, hnew, hmapI htb, List.singleton_append]
  · rw [List.singleton_append, List.map_cons, hnew, hmapII htb, List.singleton_append]
  · rw [List.nil_append, hmapI htb, List.nil_append]
  · rw [List.nil_append, hmapII htb, List.nil_append]

/-- The contribution to an oddity of a sign `v` (LMFDB `lattice.conway_genus_symbol`): `4` if
`v = -1` and `0` otherwise. -/
def signOddity : ZMod 8 :=
  if v = -1 then 4 else 0

variable (l) in
/-- The sum over the constituents `z` of a `2`-adic symbol `l` (LMFDB
`lattice.conway_genus_symbol`) of the oddity of `z`, plus `4` when `z` has sign `-1` and `m + k`
is odd, `2 ^ k` the scale of `z`: for a list of constituents of scales at least `2 ^ m`, the
oddity of `2 ^ (-m)` times their sum. -/
def parityOddity : ZMod 8 :=
  (l.map fun z ↦ z.oddity + if Odd (z.scale + m) then signOddity z.sign else 0).sum

lemma signOddity_add_self : signOddity v + signOddity v = 0 := by
  unfold signOddity
  split_ifs <;> decide

variable {u v} in
lemma signOddity_mul (hu : u = 1 ∨ u = -1) (hv : v = 1 ∨ v = -1) :
    signOddity (u * v) = signOddity u + signOddity v := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> decide

variable (z) in
lemma parityOddity_cons : parityOddity (z :: l) m =
    z.oddity + (if Odd (z.scale + m) then signOddity z.sign else 0) + parityOddity l m := by
  rw [parityOddity, List.map_cons, List.sum_cons, parityOddity]

lemma parityOddity_add_two : parityOddity l (m + 2) = parityOddity l m := by
  refine congrArg List.sum (List.map_congr_left fun z _ ↦ ?_)
  have h : Odd (z.scale + (m + 2)) ↔ Odd (z.scale + m) := by
    simp only [Nat.odd_iff]
    omega
  simp only [h]

lemma parityOddity_succ (hl : ∀ z ∈ l, z.sign = 1 ∨ z.sign = -1) :
    parityOddity l (m + 1) = parityOddity l m + signOddity (l.map sign).prod := by
  induction l with
  | nil => simp [parityOddity, signOddity]
  | cons z l ih =>
    have hl' : ∀ w ∈ l, w.sign = 1 ∨ w.sign = -1 := fun w hw ↦ hl w (List.mem_cons_of_mem z hw)
    have hp : (l.map sign).prod = 1 ∨ (l.map sign).prod = -1 :=
      trainSign_eq_one_or_eq_neg_one l hl'
    rw [parityOddity_cons, parityOddity_cons, ih hl', List.map_cons, List.prod_cons,
      signOddity_mul (hl z List.mem_cons_self) hp]
    have h : Odd (z.scale + (m + 1)) ↔ ¬Odd (z.scale + m) := by
      simp only [Nat.odd_iff]
      omega
    have h2 : signOddity z.sign + signOddity z.sign = 0 := signOddity_add_self z.sign
    by_cases ho : Odd (z.scale + m)
    · rw [ite_eq_right (h.not.mpr (not_not.mpr ho)), ite_eq_left ho]
      linear_combination -h2
    · rw [ite_eq_left (h.mpr ho), ite_eq_right ho]
      ring1

lemma trainSign_headD_eq (G : List (List DyadicBlock)) :
    trainSign (G.headD []) = (G.map trainSign).headD 1 := by
  cases G <;> rfl

variable (a b l) in
lemma trainSign_headD_trains_cons_cons : trainSign ((trains (a :: b :: l)).headD []) =
    if sameTrain a b then a.sign * trainSign ((trains (b :: l)).headD []) else a.sign := by
  rcases exists_splitBy_eq_cons_cons b l sameTrain with ⟨T, G, hTG⟩
  rw [trains_cons_cons, trains, hTG]
  cases sameTrain a b <;> simp [trainSign]

variable (a b l) in
lemma tail_map_trainSign_trains_cons_cons : ((trains (a :: b :: l)).map trainSign).tail =
    if sameTrain a b then ((trains (b :: l)).map trainSign).tail
    else (trains (b :: l)).map trainSign := by
  rcases exists_splitBy_eq_cons_cons b l sameTrain with ⟨T, G, hTG⟩
  rw [trains_cons_cons, trains, hTG]
  cases sameTrain a b <;> simp

variable (a b l) in
lemma consWalk_eq : consWalk a b l =
    if sameTrain a b then signOddity (trainSign ((trains (b :: l)).headD [])) else 0 := by
  unfold consWalk signOddity
  split_ifs <;> simp_all

lemma prod_map_sign_mul_trainSign_headD (hl : ∀ z ∈ b :: l, z.sign = 1 ∨ z.sign = -1) :
    ((b :: l).map sign).prod * trainSign ((trains (b :: l)).headD []) =
      ((trains (b :: l)).map trainSign).tail.prod := by
  rcases exists_splitBy_eq_cons_cons b l sameTrain with ⟨T, G, hTG⟩
  have h : trainSign (b :: T) = 1 ∨ trainSign (b :: T) = -1 :=
    trainSign_eq_one_or_eq_neg_one _ fun z hz ↦
      hl z (mem_of_mem_splitBy sameTrain (hTG ▸ List.mem_cons_self) hz)
  rw [← prod_map_trainSign, trains, hTG, List.map_cons, List.prod_cons, List.headD_cons,
    List.tail_cons]
  rcases h with h | h <;> rw [h] <;> ring1

lemma trainSign_headD_eq_one_or_eq_neg_one (hl : ∀ z ∈ l, z.sign = 1 ∨ z.sign = -1) :
    trainSign ((trains l).headD []) = 1 ∨ trainSign ((trains l).headD []) = -1 := by
  rcases h : trains l with _ | ⟨T, G⟩
  · exact Or.inl rfl
  · refine trainSign_eq_one_or_eq_neg_one _ fun z hz ↦ hl z (mem_of_mem_splitBy sameTrain ?_ hz)
    rw [← trains, h]
    exact List.mem_cons_self

variable {m} in
lemma filter_le_scale_eq_self (hl : ∀ z ∈ l, m ≤ z.scale) : l.filter (m ≤ ·.scale) = l :=
  List.filter_eq_self.mpr fun z hz ↦ decide_eq_true (hl z hz)

lemma map_scale_eq
    (hdata : l.map (fun b ↦ (b.scale, b.type)) = l'.map (fun b ↦ (b.scale, b.type))) :
    l.map scale = l'.map scale := by
  simpa [Function.comp_def] using congrArg (List.map Prod.fst) hdata

lemma modifyHead_zero_add (X : List (ZMod 8)) : X.modifyHead (0 + ·) = X := by
  cases X <;> simp

lemma map_canonicalOddity_eq_modifyHead (hl : (x :: t).Pairwise fun a b ↦ a.scale < b.scale)
    (hdata : (x :: t).map (fun b ↦ (b.scale, b.type)) = (x' :: t').map (fun b ↦ (b.scale, b.type)))
    (hsign : ∀ z ∈ x :: t, z.sign = 1 ∨ z.sign = -1)
    (hsign' : ∀ z ∈ x' :: t', z.sign = 1 ∨ z.sign = -1)
    (hII : ∀ z ∈ x :: t, z.type = .II → z.oddity = 0)
    (hII' : ∀ z ∈ x' :: t', z.type = .II → z.oddity = 0)
    (hΨ : ∀ m, x.scale ≤ m → TypeTwoAt (x :: t) m →
      parityOddity ((x :: t).filter (m ≤ ·.scale)) m =
        parityOddity ((x' :: t').filter (m ≤ ·.scale)) m)
    (htr : ((trains (x :: t)).map trainSign).tail = ((trains (x' :: t')).map trainSign).tail) :
    (compartments (x :: t)).map (canonicalOddity (x :: t)) =
      ((compartments (x' :: t')).map (canonicalOddity (x' :: t'))).modifyHead
        ((if x.type = .I then parityOddity (x :: t) (x.scale + 1) -
          parityOddity (x' :: t') (x.scale + 1) +
            signOddity (trainSign ((trains (x :: t)).headD [])) +
              signOddity (trainSign ((trains (x' :: t')).headD [])) else 0) + ·) := by
  induction t generalizing x x' t' with
  | nil =>
    rcases t' with _ | ⟨y', t'⟩
    · simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq, and_true] at hdata
      rcases hdata with ⟨hs, ht⟩
      have hsx : signOddity x.sign + signOddity x.sign = 0 := signOddity_add_self _
      cases hx : x.type
      · have hx' : x'.type = .I := ht ▸ hx
        simp [compartments, List.splitBy, splitBy.loop, hx, hx', canonicalOddity, trains_singleton,
          signWalks, parityOddity, hs, trainSign]
        linear_combination -hsx
      · have hx' : x'.type = .II := ht ▸ hx
        simp [compartments, List.splitBy, splitBy.loop, hx, hx']
    · simp at hdata
  | cons y rest ih =>
    rcases t' with _ | ⟨y', rest'⟩
    · simp at hdata
    have hd : (x.scale = x'.scale ∧ x.type = x'.type) ∧ (y.scale = y'.scale ∧ y.type = y'.type) ∧
        rest.map (fun b ↦ (b.scale, b.type)) = rest'.map (fun b ↦ (b.scale, b.type)) := by
      simpa only [List.map_cons, List.cons.injEq, Prod.mk.injEq] using hdata
    rcases hd with ⟨⟨hxs, hxt⟩, ⟨hys, hyt⟩, hrest⟩
    have hdata' : (y :: rest).map (fun b ↦ (b.scale, b.type)) =
        (y' :: rest').map (fun b ↦ (b.scale, b.type)) := by
      simp [hys, hyt, hrest]
    have hmap : (x :: y :: rest).map scale = (x' :: y' :: rest').map scale := map_scale_eq hdata
    have hl' : (x' :: y' :: rest').Pairwise fun a b ↦ a.scale < b.scale := by
      have h : ((x :: y :: rest).map scale).Pairwise (· < ·) := List.pairwise_map.mpr hl
      rw [hmap] at h
      exact List.pairwise_map.mp h
    have hxy : x.scale < y.scale := List.rel_of_pairwise_cons hl List.mem_cons_self
    have hsT : sameTrain x' y' = sameTrain x y := by
      simp only [sameTrain, ← hxs, ← hxt, ← hys, ← hyt]
    have hsC : sameCompartment x' y' = sameCompartment x y := by
      simp only [sameCompartment, ← hxs, ← hxt, ← hys, ← hyt]
    have hsignt : ∀ z ∈ y :: rest, z.sign = 1 ∨ z.sign = -1 :=
      fun z hz ↦ hsign z (List.mem_cons_of_mem x hz)
    have hsignt' : ∀ z ∈ y' :: rest', z.sign = 1 ∨ z.sign = -1 :=
      fun z hz ↦ hsign' z (List.mem_cons_of_mem x' hz)
    have hΨt (m : ℕ) (hm : y.scale ≤ m) (h2 : TypeTwoAt (y :: rest) m) :
        parityOddity ((y :: rest).filter (m ≤ ·.scale)) m =
          parityOddity ((y' :: rest').filter (m ≤ ·.scale)) m := by
      have hf : (x :: y :: rest).filter (m ≤ ·.scale) = (y :: rest).filter (m ≤ ·.scale) :=
        List.filter_cons_of_neg (by simpa using hxy.trans_le hm)
      have hf' : (x' :: y' :: rest').filter (m ≤ ·.scale) = (y' :: rest').filter (m ≤ ·.scale) :=
        List.filter_cons_of_neg (by simpa [← hxs] using hxy.trans_le hm)
      rw [← hf, ← hf']
      exact hΨ m (by omega) fun b hb hbs ↦ by
        rcases List.mem_cons.mp hb with rfl | hb
        · omega
        · exact h2 b hb hbs
    have htrt : ((trains (y :: rest)).map trainSign).tail =
        ((trains (y' :: rest')).map trainSign).tail := by
      rw [tail_map_trainSign_trains_cons_cons, tail_map_trainSign_trains_cons_cons, hsT] at htr
      cases hst : sameTrain x y
      · simp only [hst, Bool.false_eq_true, ↓reduceIte] at htr
        rw [htr]
      · simpa [hst] using htr
    have IH : (compartments (y :: rest)).map (canonicalOddity (y :: rest)) =
        ((compartments (y' :: rest')).map (canonicalOddity (y' :: rest'))).modifyHead
          ((if y.type = .I then parityOddity (y :: rest) (y.scale + 1) -
            parityOddity (y' :: rest') (y.scale + 1) +
              signOddity (trainSign ((trains (y :: rest)).headD [])) +
                signOddity (trainSign ((trains (y' :: rest')).headD [])) else 0) + ·) :=
      ih hl.of_cons hdata' hsignt hsignt' (fun z hz ↦ hII z (List.mem_cons_of_mem x hz))
        (fun z hz ↦ hII' z (List.mem_cons_of_mem x' hz)) hΨt htrt
    have hodd : Odd (x.scale + (x.scale + 1)) := ⟨x.scale, by ring1⟩
    have hge (z : DyadicBlock) (hz : z ∈ y :: rest) : x.scale < z.scale :=
      List.rel_of_pairwise_cons hl hz
    have hge' (z : DyadicBlock) (hz : z ∈ y' :: rest') : x.scale < z.scale :=
      hxs ▸ List.rel_of_pairwise_cons hl' hz
    have hQ (h2 : TypeTwoAt (x :: y :: rest) (x.scale + 1)) :
        parityOddity (y :: rest) (x.scale + 1) = parityOddity (y' :: rest') (x.scale + 1) := by
      have hf : (x :: y :: rest).filter (x.scale + 1 ≤ ·.scale) = y :: rest := by
        rw [List.filter_cons, ite_eq_right (by simp), filter_le_scale_eq_self hge]
      have hf' : (x' :: y' :: rest').filter (x.scale + 1 ≤ ·.scale) = y' :: rest' := by
        rw [List.filter_cons, ite_eq_right (by simp [hxs]), filter_le_scale_eq_self hge']
      rw [← hf, ← hf']
      exact hΨ (x.scale + 1) (Nat.le_succ _) h2
    have hP (h2 : TypeTwoAt (x :: y :: rest) (y.scale - 1))
        (hx2 : x.type = .II ∨ x.scale + 1 < y.scale) :
        parityOddity (y :: rest) (y.scale + 1) = parityOddity (y' :: rest') (y.scale + 1) := by
      have h : parityOddity ((x :: y :: rest).filter (y.scale - 1 ≤ ·.scale)) (y.scale - 1) =
          parityOddity ((x' :: y' :: rest').filter (y.scale - 1 ≤ ·.scale)) (y.scale - 1) :=
        hΨ (y.scale - 1) (by omega) h2
      have hy1 : y.scale + 1 = y.scale - 1 + 2 := by
        omega
      have hle (z : DyadicBlock) (hz : z ∈ y :: rest) : y.scale - 1 ≤ z.scale := by
        rcases List.mem_cons.mp hz with rfl | hz
        · exact Nat.sub_le _ _
        · exact (Nat.sub_le _ _).trans (List.rel_of_pairwise_cons hl.of_cons hz).le
      have hle' (z : DyadicBlock) (hz : z ∈ y' :: rest') : y.scale - 1 ≤ z.scale := by
        rcases List.mem_cons.mp hz with rfl | hz
        · exact hys ▸ Nat.sub_le _ _
        · exact hys ▸ (Nat.sub_le _ _).trans (List.rel_of_pairwise_cons hl'.of_cons hz).le
      have hx0 (z : DyadicBlock) (hzs : z.scale = x.scale) (hz : x.type = .II → z.oddity = 0) :
          (if y.scale - 1 ≤ z.scale then z.oddity +
            (if Odd (z.scale + (y.scale - 1)) then signOddity z.sign else 0) else 0) = 0 := by
        split_ifs with h1 h3
        · exact absurd h3 (by rw [Nat.not_odd_iff_even, Nat.even_iff]; omega)
        · rcases hx2 with hx2 | hx2
          · rw [hz hx2, add_zero]
          · omega
        · rfl
      have hcons (z : DyadicBlock) (L : List DyadicBlock) (hL : ∀ w ∈ L, y.scale - 1 ≤ w.scale) :
          parityOddity ((z :: L).filter (y.scale - 1 ≤ ·.scale)) (y.scale - 1) =
            (if y.scale - 1 ≤ z.scale then z.oddity +
              (if Odd (z.scale + (y.scale - 1)) then signOddity z.sign else 0) else 0) +
                parityOddity L (y.scale - 1) := by
        rw [List.filter_cons, filter_le_scale_eq_self hL]
        by_cases h1 : y.scale - 1 ≤ z.scale
        · rw [ite_eq_left (decide_eq_true h1), ite_eq_left h1, parityOddity_cons]
        · rw [ite_eq_right (by simpa using h1), ite_eq_right h1, zero_add]
      rw [hcons x _ hle, hcons x' _ hle', hx0 x rfl (hII x List.mem_cons_self),
        hx0 x' hxs.symm fun h ↦ hII' x' List.mem_cons_self (hxt ▸ h), zero_add, zero_add] at h
      rw [hy1, parityOddity_add_two, parityOddity_add_two, h]
    have hτ (hst : sameTrain x y = false) : trainSign ((trains (y :: rest)).headD []) =
        trainSign ((trains (y' :: rest')).headD []) := by
      rw [tail_map_trainSign_trains_cons_cons, tail_map_trainSign_trains_cons_cons, hsT, hst] at htr
      simp only [Bool.false_eq_true, ↓reduceIte] at htr
      rw [trainSign_headD_eq, trainSign_headD_eq, htr]
    have hτ1 : trainSign ((trains (y :: rest)).headD []) = 1 ∨
        trainSign ((trains (y :: rest)).headD []) = -1 :=
      trainSign_headD_eq_one_or_eq_neg_one hsignt
    have hτ1' : trainSign ((trains (y' :: rest')).headD []) = 1 ∨
        trainSign ((trains (y' :: rest')).headD []) = -1 :=
      trainSign_headD_eq_one_or_eq_neg_one hsignt'
    have key : signOddity ((y :: rest).map sign).prod +
        signOddity (trainSign ((trains (y :: rest)).headD [])) =
          signOddity ((y' :: rest').map sign).prod +
            signOddity (trainSign ((trains (y' :: rest')).headD [])) := by
      have hpr : ((y :: rest).map sign).prod = 1 ∨ ((y :: rest).map sign).prod = -1 :=
        trainSign_eq_one_or_eq_neg_one _ hsignt
      have hpr' : ((y' :: rest').map sign).prod = 1 ∨ ((y' :: rest').map sign).prod = -1 :=
        trainSign_eq_one_or_eq_neg_one _ hsignt'
      rw [← signOddity_mul hpr hτ1, ← signOddity_mul hpr' hτ1',
        prod_map_sign_mul_trainSign_headD hsignt, prod_map_sign_mul_trainSign_headD hsignt', htrt]
    have hmul : signOddity (x.sign * trainSign ((trains (y :: rest)).headD [])) =
        signOddity x.sign + signOddity (trainSign ((trains (y :: rest)).headD [])) :=
      signOddity_mul (hsign x List.mem_cons_self) hτ1
    have hmul' : signOddity (x'.sign * trainSign ((trains (y' :: rest')).headD [])) =
        signOddity x'.sign + signOddity (trainSign ((trains (y' :: rest')).headD [])) :=
      signOddity_mul (hsign' x' List.mem_cons_self) hτ1'
    have hsx : signOddity x.sign + signOddity x.sign = 0 := signOddity_add_self x.sign
    have hsτ : signOddity (trainSign ((trains (y :: rest)).headD [])) +
        signOddity (trainSign ((trains (y :: rest)).headD [])) = 0 :=
      signOddity_add_self _
    have hsτ' : signOddity (trainSign ((trains (y' :: rest')).headD [])) +
        signOddity (trainSign ((trains (y' :: rest')).headD [])) = 0 :=
      signOddity_add_self _
    rw [map_canonicalOddity_cons_cons hl, map_canonicalOddity_cons_cons hl', IH, hsC, ← hxt, ← hyt,
      consWalk_eq, consWalk_eq, hsT, trainSign_headD_trains_cons_cons,
      trainSign_headD_trains_cons_cons, hsT, parityOddity_cons x, parityOddity_cons x', ← hxs,
      ite_eq_left hodd, ite_eq_left hodd]
    have hTT (m : ℕ) (hm : m ≤ y.scale) (hxm : x.scale = m → x.type = .II)
        (hym : y.scale = m → y.type = .II) : TypeTwoAt (x :: y :: rest) m := by
      intro b hb hbs
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hxm hbs
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hym hbs
      · exact absurd hbs (List.rel_of_pairwise_cons hl.of_cons hb |>.trans_le' hm).ne'
    generalize (compartments (y' :: rest')).map (canonicalOddity (y' :: rest')) = C'
    generalize trainSign ((trains (y :: rest)).headD []) = τ at *
    generalize trainSign ((trains (y' :: rest')).headD []) = τ' at *
    cases hxT : x.type <;> cases hyT : y.type
    · by_cases hsc : y.scale = x.scale + 1
      · have hsC1 : x.sameCompartment y = true := by
          simp [sameCompartment, hxT, hyT, hsc]
        have hsT1 : x.sameTrain y = true := by
          simp [sameTrain, hxT, hsc]
        have hP1 : parityOddity (y :: rest) (y.scale + 1) =
            parityOddity (y :: rest) y.scale + signOddity ((y :: rest).map sign).prod :=
          parityOddity_succ y.scale hsignt
        have hP1' : parityOddity (y' :: rest') (y.scale + 1) =
            parityOddity (y' :: rest') y.scale + signOddity ((y' :: rest').map sign).prod :=
          parityOddity_succ y.scale hsignt'
        simp only [hsC1, hsT1, ↓reduceIte, List.modifyHead_modifyHead]
        refine congrArg (List.modifyHead · C') (funext fun v ↦ ?_)
        rw [Function.comp_apply, Function.comp_apply, hP1, hP1', hsc, hmul, hmul']
        linear_combination key - hsx
      · have hsC1 : x.sameCompartment y = false := by
          simp [sameCompartment, hsc]
        have hQ1 : parityOddity (y :: rest) (x.scale + 1) =
            parityOddity (y' :: rest') (x.scale + 1) :=
          hQ (hTT (x.scale + 1) hxy (fun h ↦ absurd h (by omega)) fun h ↦ absurd h hsc)
        have hP2 : parityOddity (y :: rest) (y.scale + 1) =
            parityOddity (y' :: rest') (y.scale + 1) :=
          hP (hTT (y.scale - 1) (Nat.sub_le _ _) (fun h ↦ absurd h (by omega))
            (fun h ↦ absurd h (by omega))) (Or.inr (by omega))
        simp only [hsC1, Bool.false_eq_true, ↓reduceIte, List.singleton_append,
          List.modifyHead_cons, List.modifyHead_modifyHead, List.cons.injEq]
        cases hst : x.sameTrain y
        · rcases hτ hst with rfl
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine ⟨by linear_combination -hQ1 - hsx,
            congrArg (List.modifyHead · C') (funext fun v ↦ ?_)⟩
          rw [Function.comp_apply]
          linear_combination hP2 + hsτ
        · simp only [↓reduceIte, hmul, hmul']
          refine ⟨by linear_combination -hQ1 - hsx - hsτ',
            congrArg (List.modifyHead · C') (funext fun v ↦ ?_)⟩
          rw [Function.comp_apply]
          linear_combination hP2 + hsτ
    · have hsC1 : x.sameCompartment y = false := by
        simp [sameCompartment, hyT]
      have hQ1 : parityOddity (y :: rest) (x.scale + 1) =
          parityOddity (y' :: rest') (x.scale + 1) :=
        hQ (hTT (x.scale + 1) hxy (fun h ↦ absurd h (by omega)) fun _ ↦ hyT)
      simp only [hsC1, ↓reduceIte, reduceCtorEq, List.singleton_append, List.modifyHead_cons,
        List.cons.injEq]
      refine ⟨?_, modifyHead_zero_add C'⟩
      cases hst : x.sameTrain y
      · simp only [Bool.false_eq_true, ↓reduceIte]
        linear_combination -hQ1 - hsx
      · simp only [↓reduceIte, hmul, hmul']
        linear_combination -hQ1 - hsx - hsτ'
    · have hsC1 : x.sameCompartment y = false := by
        simp [sameCompartment, hxT]
      have hP2 : parityOddity (y :: rest) (y.scale + 1) =
          parityOddity (y' :: rest') (y.scale + 1) :=
        hP (hTT (y.scale - 1) (Nat.sub_le _ _) (fun _ ↦ hxT) (fun h ↦ absurd h (by omega)))
          (Or.inl hxT)
      simp only [hsC1, ↓reduceIte, reduceCtorEq, List.nil_append, List.modifyHead_modifyHead]
      refine congrArg (List.modifyHead · C') (funext fun v ↦ ?_)
      rw [Function.comp_apply, Function.comp_apply]
      cases hst : x.sameTrain y
      · rcases hτ hst with rfl
        simp only [Bool.false_eq_true, ↓reduceIte]
        linear_combination hP2 + hsτ
      · simp only [↓reduceIte]
        linear_combination hP2 + hsτ
    · have hsC1 : x.sameCompartment y = false := by
        simp [sameCompartment, hxT]
      simp [hsC1]

variable (l) in
/-- The **Gauss oddity** `Θ_m` (LMFDB `lattice.conway_genus_symbol`) of a `2`-adic symbol, given by
the list `l` of its nonzero constituents `q f_q`: the sum over the constituents of scale
`q = 2 ^ k < 2 ^ m` of the oddity `t_q`, plus `4` when the sign `ε_q` is `-1` and `m - k` is odd.
It is the oddity of `2 ^ m` times the partial sum `⊕_(q < 2 ^ m) q f_q`. -/
def gaussOddity : ZMod 8 :=
  ((l.filter (·.scale < m)).map fun z ↦
    z.oddity + if Odd (m - z.scale) then signOddity z.sign else 0).sum

lemma gaussOddity_add_two_mul (hl : ∀ z ∈ l, z.scale < m + 2 * B) :
    gaussOddity l (m + 2 * B) = gaussOddity l m + parityOddity (l.filter (m ≤ ·.scale)) m := by
  induction l with
  | nil => simp [gaussOddity, parityOddity]
  | cons z l ih =>
    have ih' :
        gaussOddity l (m + 2 * B) = gaussOddity l m + parityOddity (l.filter (m ≤ ·.scale)) m :=
      ih fun w hw ↦ hl w (List.mem_cons_of_mem z hw)
    have hz : z.scale < m + 2 * B := hl z List.mem_cons_self
    simp only [gaussOddity, List.filter_cons] at ih' ⊢
    by_cases hzm : z.scale < m
    · have h : Odd (m + 2 * B - z.scale) ↔ Odd (m - z.scale) := by
        simp only [Nat.odd_iff]
        omega
      rw [ite_eq_left (decide_eq_true hz), ite_eq_left (decide_eq_true hzm),
        ite_eq_right (by simpa using hzm), List.map_cons, List.map_cons, List.sum_cons,
        List.sum_cons, ih']
      simp only [h]
      ring1
    · have h : Odd (m + 2 * B - z.scale) ↔ Odd (z.scale + m) := by
        simp only [Nat.odd_iff]
        omega
      rw [ite_eq_left (decide_eq_true hz), ite_eq_right (by simpa using hzm),
        ite_eq_left (decide_eq_true (not_lt.mp hzm)), List.map_cons, List.sum_cons, ih',
        parityOddity_cons]
      simp only [h]
      ring1

lemma gaussOddity_add_two_mul_eq_parityOddity (hl : ∀ z ∈ l, z.scale < m + 2 * B) :
    gaussOddity l (m + 2 * B) = parityOddity l m := by
  rw [gaussOddity, List.filter_eq_self.mpr fun z hz ↦ decide_eq_true (hl z hz)]
  refine congrArg List.sum (List.map_congr_left fun z hz ↦ ?_)
  have h : Odd (m + 2 * B - z.scale) ↔ Odd (z.scale + m) := by
    have hz : z.scale < m + 2 * B := hl z hz
    simp only [Nat.odd_iff]
    omega
  simp only [h]

/-- **The oddities of the compartments of the canonical `2`-adic symbol are determined by the
Gauss oddities and the signs of the trains.** Let `l` and `l'` be lists of nonzero constituents
of `2`-adic symbols, in strictly increasing order of scale, with the same scales and types, signs
`±1`, and oddity `0` for the constituents of type `II`. If they have the same signs of the trains
and the same Gauss oddity `Θ_m` at every scale `2 ^ m` without constituent of type `I` in `l`,
then their canonical `2`-adic symbols have the same oddities of the compartments. -/
lemma map_canonicalOddity_eq_of_gaussOddity_eq (hl : l.Pairwise fun a b ↦ a.scale < b.scale)
    (hdata : l.map (fun b ↦ (b.scale, b.type)) = l'.map (fun b ↦ (b.scale, b.type)))
    (hsign : ∀ z ∈ l, z.sign = 1 ∨ z.sign = -1) (hsign' : ∀ z ∈ l', z.sign = 1 ∨ z.sign = -1)
    (hII : ∀ z ∈ l, z.type = .II → z.oddity = 0) (hII' : ∀ z ∈ l', z.type = .II → z.oddity = 0)
    (htrain : (trains l).map trainSign = (trains l').map trainSign)
    (hgauss : ∀ m, TypeTwoAt l m → gaussOddity l m = gaussOddity l' m) :
    (compartments l).map (canonicalOddity l) = (compartments l').map (canonicalOddity l') := by
  have hmap : l.map scale = l'.map scale := map_scale_eq hdata
  have hB (m : ℕ) (z : DyadicBlock) (hz : z ∈ l) : z.scale < m + 2 * ((l.map scale).sum + 1) :=
    (List.le_sum_of_mem (List.mem_map_of_mem hz)).trans_lt (by omega)
  have hB' (m : ℕ) (z : DyadicBlock) (hz : z ∈ l') :
      z.scale < m + 2 * ((l.map scale).sum + 1) := by
    rw [hmap]
    exact (List.le_sum_of_mem (List.mem_map_of_mem hz)).trans_lt (by omega)
  have hbig (m : ℕ) : TypeTwoAt l (m + 2 * ((l.map scale).sum + 1)) :=
    fun z hz hzs ↦ absurd hzs (hB m z hz).ne
  rcases l with _ | ⟨x, t⟩
  · rcases l' with _ | ⟨x', t'⟩
    · rfl
    · simp at hdata
  rcases l' with _ | ⟨x', t'⟩
  · simp at hdata
  have hΨ (m : ℕ) (hm : TypeTwoAt (x :: t) m) : parityOddity ((x :: t).filter (m ≤ ·.scale)) m =
      parityOddity ((x' :: t').filter (m ≤ ·.scale)) m := by
    have h1 : gaussOddity (x :: t) m + parityOddity ((x :: t).filter (m ≤ ·.scale)) m =
        gaussOddity (x :: t) m + parityOddity ((x' :: t').filter (m ≤ ·.scale)) m := by
      rw [← gaussOddity_add_two_mul m _ (hB m), hgauss m hm, hgauss _ (hbig m),
        gaussOddity_add_two_mul m _ (hB' m)]
    exact add_left_cancel h1
  have hhead :
      trainSign ((trains (x :: t)).headD []) = trainSign ((trains (x' :: t')).headD []) := by
    rw [trainSign_headD_eq, trainSign_headD_eq, htrain]
  rw [map_canonicalOddity_eq_modifyHead hl hdata hsign hsign' hII hII' (fun m _ hm ↦ hΨ m hm)
    (congrArg List.tail htrain), hhead, ← gaussOddity_add_two_mul_eq_parityOddity _ _ (hB _),
    ← gaussOddity_add_two_mul_eq_parityOddity _ _ (hB' _), hgauss _ (hbig _), sub_self, zero_add,
    signOddity_add_self, ite_self]
  exact modifyHead_zero_add _

end DyadicBlock

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {L : IntegralLattice V} {M : IntegralLattice W} [L.IsNondegenerate] [M.IsNondegenerate]
  {z : DyadicBlock} (m : ℕ)

variable (L) in
/-- The **Gauss oddity** `Θ_m` (LMFDB `lattice.conway_genus_symbol`) of a nondegenerate integral
lattice `L` at the scale `2 ^ m`, read off the dyadic Jordan splitting `⊕_q q f_q` chosen by Tau
Ceti: `Σ_(q = 2 ^ k < 2 ^ m) (t_q + 4 [ε_q = -1] [m - k odd]) mod 8`, the oddity of `2 ^ m` times
the partial sum `⊕_(q < 2 ^ m) q f_q`. When the constituent of scale `2 ^ m` has type `II`,
`ζ₈ ^ Θ_m` is the argument of the Gauss sum `Σ_(x ∈ L ⊗ ℤ_2 / 2 ^ m) exp(2 π i x² / 2 ^ (m + 1))`,
so that `Θ_m` does not depend on the splitting and is a genus invariant: the sum is the product of
those of the constituents, and that of a unimodular form `f` of rank `n` over `ℤ_2` modulo `2 ^ s`,
`s ≥ 1`, is `2 ^ (n s / 2) ε ^ s ζ₈ ^ t` with the sign `ε` and the oddity `t` of `f`. This
classical fact is proved in `LeanBridge.ForMathlib.LinearAlgebra.Lattice.GenusSymbolGaussSum`
(`TauCeti.IntegralLattice.SameGenus.dyadicGaussOddity_eq`). -/
noncomputable def dyadicGaussOddity : ZMod 8 :=
  DyadicBlock.gaussOddity L.dyadicConstituents m

lemma dyadicJordanOddity_eq_zero {k : ℕ} (hk : L.jordanRank 2 k = 0) :
    L.dyadicJordanOddity k = 0 := by
  have hbot : (L.exists_isJordanSplitting_localIntegralForm 2 L.form_nondegenerate).choose k = ⊥ :=
    Submodule.finrank_eq_zero.mp hk
  refine BilinForm.dyadicOddity_eq_zero_of_forall_two_dvd
    ((L.exists_isJordanSplitting_localIntegralForm 2
      L.form_nondegenerate).choose_spec.isPerfPair_unitForm k)
    ((L.exists_isJordanSplitting_localIntegralForm 2
      L.form_nondegenerate).choose_spec.isSymm_unitForm (L.isSymm_localIntegralForm 2)) fun x ↦ ?_
  have hx : x = 0 := Subtype.ext ((Submodule.eq_bot_iff _).mp hbot x x.2)
  rw [hx, map_zero]
  exact dvd_zero _

/-- **The Gauss oddity is the sum over all the scales below `2 ^ m`**: `Θ_m` is the sum over
`0 ≤ k < m` of the oddity `t_q` of the dyadic Jordan constituent of scale `q = 2 ^ k`, plus `4`
when its sign `ε_q` is `-1` and `m - k` is odd, the zero constituents contributing `0`. -/
lemma dyadicGaussOddity_eq_sum : L.dyadicGaussOddity m = ∑ k ∈ Finset.range m,
    (L.dyadicJordanOddity k +
      if Odd (m - k) then DyadicBlock.signOddity (L.dyadicJordanSign k) else 0) := by
  classical
  rw [← Finset.sum_filter_of_ne (p := fun k ↦ L.jordanRank 2 k ≠ 0) fun k _ hk hk0 ↦ hk <| by
      rw [dyadicJordanOddity_eq_zero hk0, dyadicJordanSign_eq_one k hk0]
      simp [DyadicBlock.signOddity],
    dyadicGaussOddity, DyadicBlock.gaussOddity, dyadicConstituents, List.filter_map,
    List.map_map, ← List.sum_toFinset _ ((List.nodup_range.filter _).filter _)]
  refine Finset.sum_congr (Finset.ext fun k ↦ ?_) fun k _ ↦ rfl
  simp only [List.mem_toFinset, List.mem_filter, List.mem_range, Finset.mem_filter,
    Finset.mem_range, Function.comp_apply, decide_eq_true_eq]
  refine ⟨fun h ↦ ⟨h.2, h.1.2⟩, fun h ↦ ⟨⟨?_, h.2⟩, h.1⟩⟩
  by_contra hk
  exact h.2 (L.jordanRank_eq_zero_of_lt 2 (by omega))

lemma sign_eq_one_or_eq_neg_one_of_mem_dyadicConstituents (hz : z ∈ L.dyadicConstituents) :
    z.sign = 1 ∨ z.sign = -1 := by
  rcases List.mem_map.mp hz with ⟨v, -, rfl⟩
  exact (L.exists_isJordanSplitting_localIntegralForm 2
    L.form_nondegenerate).choose_spec.dyadicSign_eq_one_or_eq_neg_one

lemma oddity_eq_zero_of_mem_dyadicConstituents (hz : z ∈ L.dyadicConstituents)
    (hII : z.type = .II) : z.oddity = 0 := by
  rcases List.mem_map.mp hz with ⟨v, -, rfl⟩
  exact (L.exists_isJordanSplitting_localIntegralForm 2
    L.form_nondegenerate).choose_spec.dyadicOddity_eq_zero (L.isSymm_localIntegralForm 2)
    (forall_mem_pow_dvd_of_dyadicJordanType_eq hII)

/-- **The oddities of the compartments of the canonical `2`-adic symbol are genus invariants once
the Gauss oddities are.** If `L` and `M` are in the same genus and have the same Gauss oddity
`Θ_m` at every scale `2 ^ m` at which the dyadic Jordan constituent of `L` has type `II` (a genus
invariant by Gauss sums: `SameGenus.dyadicGaussOddity_eq`, where this lemma is made unconditional as
`SameGenus.compartmentOddities_eq`), then the canonical `2`-adic symbols of `L` and `M` have the
same oddities of the compartments. -/
lemma SameGenus.compartmentOddities_eq_of_dyadicGaussOddity_eq (h : L.SameGenus M)
    (hΘ : ∀ m, L.dyadicJordanType m = .II → L.dyadicGaussOddity m = M.dyadicGaussOddity m) :
    L.compartmentOddities = M.compartmentOddities :=
  DyadicBlock.map_canonicalOddity_eq_of_gaussOddity_eq pairwise_dyadicConstituents
    h.map_dyadicConstituents_eq (fun _ ↦ sign_eq_one_or_eq_neg_one_of_mem_dyadicConstituents)
    (fun _ ↦ sign_eq_one_or_eq_neg_one_of_mem_dyadicConstituents)
    (fun _ ↦ oddity_eq_zero_of_mem_dyadicConstituents)
    (fun _ ↦ oddity_eq_zero_of_mem_dyadicConstituents) h.trainSigns_eq
    fun m hm ↦ hΘ m (dyadicJordanType_eq_of_typeTwoAt hm)

/-- **The label of the genus is a genus invariant once the Gauss oddities are**: lattices in the
same genus with the same Gauss oddities at the scales at which the dyadic Jordan constituent of
`L` has type `II` (a genus invariant by Gauss sums: `SameGenus.dyadicGaussOddity_eq`, where this
lemma is made unconditional as `SameGenus.canonicalGenusLabel_congr`) have the same label (LMFDB
`lattice.genus_label`). -/
lemma SameGenus.canonicalGenusLabel_eq_of_dyadicGaussOddity_eq (h : L.SameGenus M)
    (hΘ : ∀ m, L.dyadicJordanType m = .II → L.dyadicGaussOddity m = M.dyadicGaussOddity m) :
    L.canonicalGenusLabel = M.canonicalGenusLabel :=
  h.canonicalGenusLabel_eq (h.compartmentOddities_eq_of_dyadicGaussOddity_eq hΘ)

end TauCeti.IntegralLattice
