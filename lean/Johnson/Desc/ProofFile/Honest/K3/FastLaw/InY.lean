-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/FastLaw/InY.lean: the honest side of the kind "lookup" (K3). At the
product trees' levels and at the bits, the end values and the polynomial in Y of the filling that
folds tables are the specification's. Conditional on the hypotheses below. Theorems.

Terms. Honest/K3/GLOSSARY.md. In this file: a level's end values are the two halves of the level
below at the point of the level's challenges; the bits' one end value is the bits' table there.
Honest/K3/JobsFast.lean folds arrays (`Fast.prodEnds`); the specification has multilinear extensions
(`pj`, `keyJob`, `tabJob`, `bitsJob`, Johnson/HonestTrace/LookDefs.lean).

What is shown.
  `key_ends`, `key_inY`, `tab_ends`, `tab_inY`, `bits_ends`, `bits_inY`, `leaves_ends`,
    `leaves_inY`: the equations between the two fillings: at each of these stages they yield one
    list.
  `key_ends_read`, `key_inY_read`: the key tree's level with m variables, m below the number of a
    key's bits: the two lists, read in the field.
  `tab_ends_read`, `tab_inY_read`: the same at the table side's level number l, l below d.
  `bits_ends_read`, `bits_inY_read`: the same at the bits.
  The theorems whose names end in `_ok`: the lists' entries have words below the prime.
  `halves_read`: the two halves of a level, folded.
  `cut_size`, `cut_read`: a stretch of an array. `mulY_read`: kappa + (a + Y ma) (b + Y mb), three
    coefficients. `two_of_map`, `one_of_map`: the entries of a short list whose reading is known.

Hypotheses that remain.
  `H`: `Sized f v p` (Honest/K3/FastLaw/Tie.lean).
  `hx`: there are as many challenges as the level has variables.
  `ho`: (for the key tree) the face's order at that level lists the level's variables, each once.
  `hm`, `hl`: the level is in range: m < v, l < d.
  In the small theorems. `he`, `hX`: (in `cut_size`, `cut_read`) the stretch ends within the array;
    the entry's number lies within the stretch. `h`: (in `two_of_map`, `one_of_map`) the list's
    reading. `hs`, `hF`: (in `halves_read`) the array of the level below has its size and reads as
    F. `hn`: (in `cut_ok`, `halves_ok`) the array's entries have words below the prime.

How the proof goes. That folding an array gives the extension is `prodEnds_read'`
(Honest/K3/FastLaw/Round.lean); that the arrays are the specification's functions is shown in
Honest/K3/FastLaw/Levels.lean. Here the two are put together.

Users. The files Rounds.lean and All.lean of Honest/K3/FastLaw/ import this file.

Limits. No statement of this file speaks of a round polynomial, and none says that either filling
is right.
An instance of the hypotheses: Honest/K3/FastLaw/AllToy.lean [not in this library] (by evaluation).
The equations by evaluation, at one small synthetic lookup: Honest/K3/JobsFastIsSpec.lean
[not in this library].
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.Tie
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.Round

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.FastLaw
open OnBytes (E addE subE mulE zeroE oneE okE)
open OnBytes.Slice (readE readV readE_mul readE_add readE_sub readE_one readE_zero)
open OnBytes.HonestTrace.Look (keyJob tabJob bitsJob ext)
open TwV (byVar)

/-! ## 1 Small facts -/

theorem cut_size (n : Array E) (s e : Nat) (he : e ≤ n.size) : (n.extract s e).size = e - s := by
  rw [Array.size_extract, Nat.min_eq_left he]

theorem cut_read (n : Array E) (s e : Nat) (he : e ≤ n.size) {X : Nat} (hX : X < e - s) :
    readV (n.extract s e) X = readV n (s + X) := by
  have h1 : X < min e n.size - s := by rw [Nat.min_eq_left he]; exact hX
  have h2 : s + X < n.size := by omega
  unfold OnBytes.Slice.readV
  simp [Array.getD, h1, h2]

theorem cut_ok (n : Array E) (hn : ∀ x, okE (n.getD x zeroE) = true) (s e i : Nat) :
    okE ((n.extract s e).getD i zeroE) = true := by
  by_cases h : i < min e n.size - s
  · have h2 : s + i < n.size := by omega
    have h3 := hn (s + i)
    simp [Array.getD, h2] at h3
    simp [Array.getD, h, h3]
  · simp [Array.getD, h]
    rfl

theorem mulY_read (k a b ma mb : E) :
    (Fast.mulY k a b ma mb).map readE =
      [readE k + readE a * readE b, readE a * readE mb + readE ma * readE b,
        readE ma * readE mb] := by
  unfold Fast.mulY
  simp only [List.map_cons, List.map_nil, readE_mul, readE_add]

theorem mulY_ok (k a b ma mb : E) : ∀ x ∈ Fast.mulY k a b ma mb, okE x = true := by
  intro x hx
  unfold Fast.mulY at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · exact ok_add _ _
  · exact ok_add _ _
  · exact ok_mul _ _

theorem two_of_map {l : List E} {a b : KE} (h : l.map readE = [a, b]) :
    readE (l.getD 0 zeroE) = a ∧ readE (l.getD 1 zeroE) = b := by
  match l, h with
  | [x, y], h =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    exact h

theorem one_of_map {l : List E} {a : KE} (h : l.map readE = [a]) :
    readE (l.getD 0 zeroE) = a := by
  match l, h with
  | [x], h =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    exact h

/-- **The two halves of a level, folded.** next: the level below, 2 ^ (m + 1) entries, which read as
F. -/
theorem halves_read (m : Nat) (o : List Nat) (next : Array E) (F : Nat → KE)
    (hs : next.size = 2 ^ (m + 1)) (hF : ∀ X < 2 ^ (m + 1), readV next X = F X)
    (ho : o.Perm (List.range m)) (xs : List E) (hx : xs.length = m) :
    (Fast.prodEnds m o [next.extract 0 (2 ^ m), next.extract (2 ^ m) (2 ^ (m + 1))] xs).map readE =
      [ext m F (byVar o (ups xs)), ext m (fun X => F (X + 2 ^ m)) (byVar o (ups xs))] := by
  have hp : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; omega
  refine prodEnds_read' m o _ [F, fun X => F (X + 2 ^ m)] xs ho hx
    (.cons ⟨?_, fun X hX => ?_⟩ (.cons ⟨?_, fun X hX => ?_⟩ .nil))
  · rw [cut_size _ _ _ (by omega)]
    omega
  · rw [cut_read _ _ _ (by omega) (by omega), Nat.zero_add]
    exact hF X (by omega)
  · rw [cut_size _ _ _ (by omega)]
    omega
  · rw [cut_read _ _ _ (by omega) (by omega), Nat.add_comm]
    exact hF _ (by omega)

/-! ## 2 The levels and the bits -/

section
variable (f : LFace) (row : E → Nat → E) (pads : List (Nat × Nat)) (w : Hidden) (p : Pts)
variable {v : Nat}

/-- **The key tree's level with m variables: the end values.** -/
theorem key_ends_read (H : Sized f v p) {m : Nat} (hm : m < v)
    (ho : (f.orders 0 m).Perm (List.range m)) (xs : List E) (hx : xs.length = m) :
    (((fastJobs f row).job (.key 0 m)).ends w p xs).map readE =
      (keyJob (datAt f row pads w p) m (byBit (p.keyPt 0 m))).ends (ups xs) := by
  obtain ⟨h1, h2⟩ := keyLvl_read f row pads w p H.parts H.one (by omega : m + 1 ≤ v)
  exact halves_read m (f.orders 0 m) ((srcAt f row w p).keyLvl 0 (m + 1))
    ((datAt f row pads w p).kLvl (m + 1)) h1 h2 ho xs hx

/-- **The key tree's level with m variables: the polynomial in Y.** -/
theorem key_inY_read (H : Sized f v p) {m : Nat} (hm : m < v)
    (ho : (f.orders 0 m).Perm (List.range m)) (xs mk : List E) (hx : xs.length = m) :
    (((fastJobs f row).job (.key 0 m)).inY w p xs mk).map readE =
      (keyJob (datAt f row pads w p) m (byBit (p.keyPt 0 m))).inY (ups xs) (ups mk) := by
  obtain ⟨e0, e1⟩ := two_of_map (key_ends_read f row pads w p H hm ho xs hx)
  show (Fast.mulY zeroE ((((fastJobs f row).job (.key 0 m)).ends w p xs).getD 0 zeroE)
    ((((fastJobs f row).job (.key 0 m)).ends w p xs).getD 1 zeroE) (mk.getD 0 zeroE)
    (mk.getD 1 zeroE)).map readE = [_, _, _]
  rw [mulY_read, e0, e1, readE_zero, getD_ups, getD_ups]

/-- **The table side's level number l: the end values.** -/
theorem tab_ends_read (H : Sized f v p) {l : Nat} (hl : l < f.d) (xs : List E)
    (hx : xs.length = f.mu + l) :
    (((fastJobs f row).job (.tab l)).ends w p xs).map readE =
      (tabJob (datAt f row pads w p) l (byBit (p.tabPt l))).ends (ups xs) := by
  obtain ⟨h1, h2⟩ := tabLvl_read f row pads w p H.two H.theta (by omega : l + 1 ≤ f.d)
  rw [show l + 1 + f.mu = f.mu + l + 1 by omega] at h1 h2
  exact halves_read (f.mu + l) (OnBytes.Model.orderDefault (f.mu + l))
    ((srcAt f row w p).tabLvl (l + 1)) ((datAt f row pads w p).tLvl (l + 1)) h1 h2
    (orderDefault_perm _) xs hx

/-- **The table side's level number l: the polynomial in Y.** -/
theorem tab_inY_read (H : Sized f v p) {l : Nat} (hl : l < f.d) (xs mk : List E)
    (hx : xs.length = f.mu + l) :
    (((fastJobs f row).job (.tab l)).inY w p xs mk).map readE =
      (tabJob (datAt f row pads w p) l (byBit (p.tabPt l))).inY (ups xs) (ups mk) := by
  obtain ⟨e0, e1⟩ := two_of_map (tab_ends_read f row pads w p H hl xs hx)
  show (Fast.mulY zeroE ((((fastJobs f row).job (.tab l)).ends w p xs).getD 0 zeroE)
    ((((fastJobs f row).job (.tab l)).ends w p xs).getD 1 zeroE) (mk.getD 0 zeroE)
    (mk.getD 1 zeroE)).map readE = [_, _, _]
  rw [mulY_read, e0, e1, readE_zero, getD_ups, getD_ups]

/-- **The bits: the end value.** -/
theorem bits_ends_read (H : Sized f v p) (xs : List E) (hx : xs.length = f.mu + f.d) :
    (((fastJobs f row).job .bits).ends w p xs).map readE =
      (bitsJob (datAt f row pads w p) (byBit p.zeroPt)).ends (ups xs) :=
  prodEnds_read' (f.mu + f.d) (OnBytes.Model.orderDefault (f.mu + f.d)) [bitArr f w]
    [(datAt f row pads w p).bitAt] xs (orderDefault_perm _) hx
    (.cons ⟨bitArr_size f w, fun _ hX => bitTab_read f row pads w p H.two hX⟩ .nil)

/-- **The bits: the polynomial in Y.** -/
theorem bits_inY_read (H : Sized f v p) (xs mk : List E) (hx : xs.length = f.mu + f.d) :
    (((fastJobs f row).job .bits).inY w p xs mk).map readE =
      (bitsJob (datAt f row pads w p) (byBit p.zeroPt)).inY (ups xs) (ups mk) := by
  have e0 := one_of_map (bits_ends_read f row pads w p H xs hx)
  show (Fast.mulY zeroE ((((fastJobs f row).job .bits).ends w p xs).getD 0 zeroE)
    (subE ((((fastJobs f row).job .bits).ends w p xs).getD 0 zeroE) oneE) (mk.getD 0 zeroE)
    (mk.getD 0 zeroE)).map readE = [_, _, _]
  rw [mulY_read, readE_sub, e0, readE_zero, readE_one, getD_ups]
  congr 1
  · ring
  congr 1
  · ring
  congr 1
  ring

/-! ## 3 The entries' words -/

theorem halves_ok (m : Nat) (o : List Nat) (next : Array E)
    (hn : ∀ x, okE (next.getD x zeroE) = true) (xs : List E) :
    ∀ x ∈ Fast.prodEnds m o [next.extract 0 (2 ^ m), next.extract (2 ^ m) (2 ^ (m + 1))] xs,
      okE x = true := by
  refine prodEnds_ok m o _ xs fun t ht i => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> exact cut_ok _ hn _ _ _

theorem key_ends_ok (m : Nat) (xs : List E) :
    ∀ x ∈ ((fastJobs f row).job (.key 0 m)).ends w p xs, okE x = true :=
  halves_ok m (f.orders 0 m) ((srcAt f row w p).keyLvl 0 (m + 1)) (keyLvl_ok f row w p 0 (m + 1)) xs

theorem key_inY_ok (m : Nat) (xs mk : List E) :
    ∀ x ∈ ((fastJobs f row).job (.key 0 m)).inY w p xs mk, okE x = true :=
  mulY_ok _ _ _ _ _

theorem tab_ends_ok (l : Nat) (xs : List E) :
    ∀ x ∈ ((fastJobs f row).job (.tab l)).ends w p xs, okE x = true :=
  halves_ok (f.mu + l) (OnBytes.Model.orderDefault (f.mu + l)) ((srcAt f row w p).tabLvl (l + 1))
    (tabLvl_ok f row w p (l + 1)) xs

theorem tab_inY_ok (l : Nat) (xs mk : List E) :
    ∀ x ∈ ((fastJobs f row).job (.tab l)).inY w p xs mk, okE x = true :=
  mulY_ok _ _ _ _ _

theorem bits_ends_ok (H : Sized f v p) (xs : List E) (hx : xs.length = f.mu + f.d) :
    ∀ x ∈ ((fastJobs f row).job .bits).ends w p xs, okE x = true := by
  have hmu : 1 ≤ f.mu := by
    by_contra h
    have h0 : f.mu = 0 := by omega
    have h1 := H.fit
    have h2 := H.two
    rw [h0] at h1
    omega
  refine prodEnds_ok' (f.mu + f.d) (OnBytes.Model.orderDefault (f.mu + f.d)) [bitArr f w] xs
    (fun h => ?_) (fun h => ?_)
  · have := (orderDefault_perm (f.mu + f.d)).length_eq
    rw [h, List.length_range] at this
    simp at this
    omega
  · rw [h] at hx
    simp at hx
    omega

theorem bits_inY_ok (xs mk : List E) :
    ∀ x ∈ ((fastJobs f row).job .bits).inY w p xs mk, okE x = true :=
  mulY_ok _ _ _ _ _

/-! ## 4 The equations between the two fillings -/

/-- **Conditional on `Sized f v p`, m < v, the order a permutation, m challenges: a key level's end
values: the two fillings yield one list.** An instance: Honest/K3/FastLaw/AllToy.lean
[not in this library] (by evaluation); the equation by evaluation: Honest/K3/JobsFastIsSpec.lean
[not in this library]. -/
theorem key_ends (H : Sized f v p) {m : Nat} (hm : m < v)
    (ho : (f.orders 0 m).Perm (List.range m)) (xs : List E) (hx : xs.length = m) :
    ((fastJobs f row).job (.key 0 m)).ends w p xs =
      ((specJobsAt f row pads).job (.key 0 m)).ends w p xs :=
  eq_downs (key_ends_ok f row w p m xs) (key_ends_read f row pads w p H hm ho xs hx)

/-- **Conditional on `Sized f v p`, m < v, the order a permutation, m challenges: a key level's
polynomial in Y: the two fillings yield one list.** An instance: Honest/K3/FastLaw/AllToy.lean
[not in this library] (by evaluation); the equation by evaluation: Honest/K3/JobsFastIsSpec.lean
[not in this library]. -/
theorem key_inY (H : Sized f v p) {m : Nat} (hm : m < v)
    (ho : (f.orders 0 m).Perm (List.range m)) (xs mk : List E) (hx : xs.length = m) :
    ((fastJobs f row).job (.key 0 m)).inY w p xs mk =
      ((specJobsAt f row pads).job (.key 0 m)).inY w p xs mk :=
  eq_downs (key_inY_ok f row w p m xs mk) (key_inY_read f row pads w p H hm ho xs mk hx)

/-- **Conditional on `Sized f v p`, l < d, mu + l challenges: a table level's end values: the two
fillings yield one list.** An instance: Honest/K3/FastLaw/AllToy.lean [not in this library] (by
evaluation); the equation by evaluation: Honest/K3/JobsFastIsSpec.lean [not in this library]. -/
theorem tab_ends (H : Sized f v p) {l : Nat} (hl : l < f.d) (xs : List E)
    (hx : xs.length = f.mu + l) :
    ((fastJobs f row).job (.tab l)).ends w p xs =
      ((specJobsAt f row pads).job (.tab l)).ends w p xs :=
  eq_downs (tab_ends_ok f row w p l xs) (tab_ends_read f row pads w p H hl xs hx)

/-- **Conditional on `Sized f v p`, l < d, mu + l challenges: a table level's polynomial in Y: the
two fillings yield one list.** An instance: Honest/K3/FastLaw/AllToy.lean [not in this library] (by
evaluation); the equation by evaluation: Honest/K3/JobsFastIsSpec.lean [not in this library]. -/
theorem tab_inY (H : Sized f v p) {l : Nat} (hl : l < f.d) (xs mk : List E)
    (hx : xs.length = f.mu + l) :
    ((fastJobs f row).job (.tab l)).inY w p xs mk =
      ((specJobsAt f row pads).job (.tab l)).inY w p xs mk :=
  eq_downs (tab_inY_ok f row w p l xs mk) (tab_inY_read f row pads w p H hl xs mk hx)

/-- **Conditional on `Sized f v p`, mu + d challenges: the bits' end value: the two fillings yield
one list.** An instance: Honest/K3/FastLaw/AllToy.lean [not in this library] (by evaluation); the
equation by evaluation: Honest/K3/JobsFastIsSpec.lean [not in this library]. -/
theorem bits_ends (H : Sized f v p) (xs : List E) (hx : xs.length = f.mu + f.d) :
    ((fastJobs f row).job .bits).ends w p xs = ((specJobsAt f row pads).job .bits).ends w p xs :=
  eq_downs (bits_ends_ok f row w p H xs hx) (bits_ends_read f row pads w p H xs hx)

/-- **Conditional on `Sized f v p`, mu + d challenges: the bits' polynomial in Y: the two fillings
yield one list.** An instance: Honest/K3/FastLaw/AllToy.lean [not in this library] (by evaluation);
the equation by evaluation: Honest/K3/JobsFastIsSpec.lean [not in this library]. -/
theorem bits_inY (H : Sized f v p) (xs mk : List E) (hx : xs.length = f.mu + f.d) :
    ((fastJobs f row).job .bits).inY w p xs mk =
      ((specJobsAt f row pads).job .bits).inY w p xs mk :=
  eq_downs (bits_inY_ok f row w p xs mk) (bits_inY_read f row pads w p H xs mk hx)

/-- The leaves' sumcheck has no end value and no polynomial in Y, in either filling. -/
theorem leaves_ends (xs : List E) :
    ((fastJobs f row).job .leaves).ends w p xs =
      ((specJobsAt f row pads).job .leaves).ends w p xs := rfl

theorem leaves_inY (xs mk : List E) :
    ((fastJobs f row).job .leaves).inY w p xs mk =
      ((specJobsAt f row pads).job .leaves).inY w p xs mk := rfl

end

end ProofFile.Honest.K3.FastLaw

#print axioms ProofFile.Honest.K3.FastLaw.cut_ok
#print axioms ProofFile.Honest.K3.FastLaw.mulY_ok
#print axioms ProofFile.Honest.K3.FastLaw.halves_ok
#print axioms ProofFile.Honest.K3.FastLaw.key_ends_ok
#print axioms ProofFile.Honest.K3.FastLaw.key_inY_ok
#print axioms ProofFile.Honest.K3.FastLaw.tab_ends_ok
#print axioms ProofFile.Honest.K3.FastLaw.tab_inY_ok
#print axioms ProofFile.Honest.K3.FastLaw.bits_ends_ok
#print axioms ProofFile.Honest.K3.FastLaw.bits_inY_ok
#print axioms ProofFile.Honest.K3.FastLaw.key_ends
#print axioms ProofFile.Honest.K3.FastLaw.key_inY
#print axioms ProofFile.Honest.K3.FastLaw.tab_ends
#print axioms ProofFile.Honest.K3.FastLaw.tab_inY
#print axioms ProofFile.Honest.K3.FastLaw.bits_ends
#print axioms ProofFile.Honest.K3.FastLaw.bits_inY
#print axioms ProofFile.Honest.K3.FastLaw.leaves_ends
#print axioms ProofFile.Honest.K3.FastLaw.leaves_inY
#print axioms ProofFile.Honest.K3.FastLaw.cut_size
#print axioms ProofFile.Honest.K3.FastLaw.cut_read
#print axioms ProofFile.Honest.K3.FastLaw.mulY_read
#print axioms ProofFile.Honest.K3.FastLaw.two_of_map
#print axioms ProofFile.Honest.K3.FastLaw.one_of_map
#print axioms ProofFile.Honest.K3.FastLaw.halves_read
#print axioms ProofFile.Honest.K3.FastLaw.key_ends_read
#print axioms ProofFile.Honest.K3.FastLaw.key_inY_read
#print axioms ProofFile.Honest.K3.FastLaw.tab_ends_read
#print axioms ProofFile.Honest.K3.FastLaw.tab_inY_read
#print axioms ProofFile.Honest.K3.FastLaw.bits_ends_read
#print axioms ProofFile.Honest.K3.FastLaw.bits_inY_read
