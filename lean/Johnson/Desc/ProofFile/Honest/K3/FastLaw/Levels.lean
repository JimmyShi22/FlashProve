-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/FastLaw/Levels.lean: the honest side of the kind "lookup" (K3). The
tables of the filling that folds tables are, as read, the specification's functions. Theorems, with
two definitions and two abbreviations.

Terms. Honest/K3/GLOSSARY.md. In this file: Honest/K3/JobsFast.lean makes, at a shift and an alpha,
arrays of the program's elements: the levels of the key side's product tree, those of the table
side's, the bits, and alpha - 1 - row (`Fast.srcOf`; here `srcAt`). The specification
(Johnson/HonestTrace/LookDefs.lean) has the same as functions on numbers with values in the
library's field (`Data.kLvl`, `Data.tLvl`, `Data.bitAt`, `Data.rowAt`), at the data that
Honest/K3/JobsSpec.lean makes of the same input and points (`dataAt` at `numsOf`; here `datAt`).

What is shown.
  `up_size`, `readV_up`, `upN_succ`, `upN_level`: one level up halves an array and multiplies entry
    x by entry x + half the size; k levels up are the library's levels of a forest (`Blocks.lvl`,
    Blocks/LookupRel.lean).
  `keyLvl_read`: the key side: the array has size 2 ^ m, and entry X reads as `Data.kLvl m X`.
  `bitTab_read`, `facTab_read`: the same for the bits and for alpha - 1 - row, at the arrays written
    out (`bitArr`, `facArr`; `bitTab_eq` and `facTab_eq` say that these are the filling's).
  `tabLvl_read`: the table side: the array has size 2 ^ (l + mu), and entry X reads as
    `Data.tLvl l X`.
  `keyLvl_ok`, `tabLvl_ok`, `facArr_ok`: the words of these arrays' entries are below the prime.
Helpers: `tab_out`, `tab_ok`, `ok_up`, `ok_upN`, `tabLvl_eq`, `bitArr_size`, `facArr_size`,
`zip_getD`, `zip_size`.

Hypotheses that remain.
  `hf`, `hv`: (the key side) the face has one part of keys, of one bit at least.
  `hp`: (the bits and the table side) there are two planes at least.
  `ht`: (alpha - 1 - row and the table side) the shift's words are below the prime: the
    specification's table is read at the shift as read and laid into words again.
  `hm`, `hl`, `hX`: the level and the entry's number are in range.
  `h`: (in `readV_up`) x lies below half the array's size; (in `tab_out`) i is not below n.
  `hs`, `hA`: (in `upN_level`) the array has size 2 ^ (n + s) and reads as A; there, without a name:
    k ≤ n.
  `hg`, `ha`: (in `tab_ok`, `ok_upN`) the entries' words are below the prime. `ha`, `hb`, `hi`: (in
    `zip_getD`, `zip_size`) both arrays have size N; i < N.

Users. The files Tie.lean and Rounds.lean of Honest/K3/FastLaw/ import this file.

Limits. No statement of this file speaks of a round, an end value or a sum. The bits' table holds
the input's own elements: nothing is said on their words.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.Read

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.FastLaw
open OnBytes (E addE subE mulE zeroE oneE okE)
open OnBytes.Slice (readE readV readE_mul readE_add readE_sub readE_one readE_zero)

/-! ## 1 Levels of arrays -/

/-- Beyond its end a table made by a rule yields the program's 0. -/
theorem tab_out (n : Nat) (g : Nat → E) {i : Nat} (h : ¬ i < n) :
    ((Array.range n).map g).getD i zeroE = zeroE := by
  simp [Array.getD, h]

/-- A table made by a rule whose values have words below the prime: so has whatever is
read of it. -/
theorem tab_ok (n : Nat) (g : Nat → E) (hg : ∀ i, okE (g i) = true) (x : Nat) :
    okE (((Array.range n).map g).getD x zeroE) = true := by
  by_cases h : x < n
  · rw [tab_getD _ _ h]
    exact hg x
  · rw [tab_out _ _ h]
    rfl

theorem up_size (a : Array E) : (Fast.up a).size = a.size / 2 := by
  unfold Fast.up
  exact tab_size _ _

theorem readV_up (a : Array E) {x : Nat} (h : x < a.size / 2) :
    readV (Fast.up a) x = readV a x * readV a (a.size / 2 + x) := by
  unfold Fast.up
  rw [readV_tab _ _ h, readE_mul]
  rfl

theorem ok_up (a : Array E) (x : Nat) : okE ((Fast.up a).getD x zeroE) = true := by
  by_cases h : x < a.size / 2
  · unfold Fast.up
    rw [tab_getD _ _ h]
    exact ok_mul _ _
  · have : (Fast.up a).getD x zeroE = zeroE := by
      have hs : (Fast.up a).size ≤ x := by rw [up_size]; omega
      simp [Array.getD, hs]
    rw [this]
    rfl

theorem upN_succ : ∀ (k : Nat) (a : Array E), Fast.upN (k + 1) a = Fast.up (Fast.upN k a)
  | 0, _ => rfl
  | k + 1, a => by
    show Fast.upN (k + 1) (Fast.up a) = Fast.up (Fast.upN k (Fast.up a))
    exact upN_succ k (Fast.up a)

/-- **k levels up.** a: the leaves of a forest, 2 ^ (n + s) of them, which read as A. -/
theorem upN_level (s n : Nat) (A : Nat → KE) (a : Array E) (hs : a.size = 2 ^ (n + s))
    (hA : ∀ X < 2 ^ (n + s), readV a X = A X) :
    ∀ k ≤ n, (Fast.upN k a).size = 2 ^ (n - k + s) ∧
      ∀ X < 2 ^ (n - k + s), readV (Fast.upN k a) X = Blocks.lvl s n A (n - k) X
  | 0, _ => by
    refine ⟨hs, fun X hX => ?_⟩
    rw [Nat.sub_zero, Blocks.lvl_top]
    exact hA X hX
  | k + 1, hk => by
    obtain ⟨h1, h2⟩ := upN_level s n A a hs hA k (by omega)
    obtain ⟨l, hl⟩ : ∃ l, n - (k + 1) = l := ⟨_, rfl⟩
    have hl1 : n - k = l + 1 := by omega
    rw [hl1] at h1 h2
    have hhalf : (Fast.upN k a).size / 2 = 2 ^ (l + s) := by
      rw [h1, show l + 1 + s = (l + s) + 1 by omega, pow_succ]
      omega
    rw [hl, upN_succ]
    refine ⟨by rw [up_size, hhalf], fun X hX => ?_⟩
    have hpow : 2 ^ (l + 1 + s) = 2 ^ (l + s) + 2 ^ (l + s) := by
      rw [show l + 1 + s = (l + s) + 1 by omega, pow_succ]
      omega
    rw [readV_up _ (by rw [hhalf]; exact hX), hhalf, h2 X (by omega),
      h2 (2 ^ (l + s) + X) (by omega), Blocks.lvl_step s n A (by omega : l < n) X,
      Nat.add_comm (2 ^ (l + s)) X]

theorem ok_upN (a : Array E) (ha : ∀ x, okE (a.getD x zeroE) = true) :
    ∀ (k x : Nat), okE ((Fast.upN k a).getD x zeroE) = true
  | 0, x => ha x
  | k + 1, x => by
    rw [upN_succ]
    exact ok_up _ x

/-! ## 2 The tables of a lookup -/

section
variable (f : LFace) (row : E → Nat → E) (pads : List (Nat × Nat)) (w : Hidden) (p : Pts)

/-- The tables of the filling that folds tables, at a run. -/
abbrev srcAt : Fast.Src := Fast.srcOf f row w p.theta p.alpha

/-- The specification's data at the same run. -/
abbrev datAt : OnBytes.HonestTrace.Look.Data Unit KE := dataAt (numsOf f row pads) w p

/-- **The key side's levels**: the size of the array of level m, and what its entries read as.
Conditional on one part of keys, of one bit at least, and on m being at most that number of
bits. -/
theorem keyLvl_read {v : Nat} (hf : f.parts = [v]) (hv : 1 ≤ v) {m : Nat} (hm : m ≤ v) :
    ((srcAt f row w p).keyLvl 0 m).size = 2 ^ m ∧
      ∀ X < 2 ^ m, readV ((srcAt f row w p).keyLvl 0 m) X = (datAt f row pads w p).kLvl m X := by
  have hD : (datAt f row pads w p).v = v := by
    show f.parts.headD 0 - 1 + 1 = v
    rw [hf]
    show v - 1 + 1 = v
    omega
  have hL := upN_level 0 v
    (Cb.Lkp.facK (datAt f row pads w p).key (datAt f row pads w p).al)
    ((Array.range (2 ^ v)).map fun x => subE p.alpha (w.key p.theta 0 x))
    (tab_size _ _) (fun X hX => by
      have hX' : X < 2 ^ v := hX
      rw [readV_tab _ _ hX', readE_sub]
      rfl) (v - m) (by omega)
  rw [show v - (v - m) = m by omega, Nat.add_zero] at hL
  have hk : (srcAt f row w p).keyLvl 0 m =
      Fast.upN (v - m) ((Array.range (2 ^ v)).map fun x => subE p.alpha (w.key p.theta 0 x)) := by
    show Fast.upN (f.parts.getD 0 0 - m)
      ((Array.range (2 ^ f.parts.getD 0 0)).map fun x => subE p.alpha (w.key p.theta 0 x)) = _
    rw [hf]
    rfl
  rw [hk]
  refine ⟨hL.1, fun X hX => ?_⟩
  rw [hL.2 X hX]
  show _ = Blocks.lvl 0 (datAt f row pads w p).v _ m X
  rw [hD]

theorem keyLvl_ok (i m x : Nat) : okE (((srcAt f row w p).keyLvl i m).getD x zeroE) = true := by
  exact ok_upN _ (fun y => tab_ok _ _ (fun _ => ok_sub _ _) y) _ x

/-- The bits' table, written out. -/
def bitArr : Array E :=
  (Array.range (2 ^ (f.mu + f.d))).map fun X =>
    if X % 2 ^ f.mu < f.planes then w.bit (X / 2 ^ f.mu) (X % 2 ^ f.mu) else zeroE

/-- The table of alpha - 1 - row, written out. -/
def facArr : Array E :=
  (Array.range (2 ^ (f.mu + f.d))).map fun X =>
    ((Array.range (2 ^ f.d)).map fun u => subE (subE p.alpha oneE) (row p.theta u)).getD
      (X / 2 ^ f.mu) zeroE

theorem bitTab_eq : (srcAt f row w p).bitTab () = bitArr f w := rfl

theorem facTab_eq : (srcAt f row w p).facTab () = facArr f row p := rfl

theorem tabLvl_eq (l : Nat) : (srcAt f row w p).tabLvl l =
    Fast.upN (f.d - l)
      (Array.zipWith (fun b a => addE oneE (mulE b a)) (bitArr f w) (facArr f row p)) := rfl

theorem bitArr_size : (bitArr f w).size = 2 ^ (f.mu + f.d) := tab_size _ _

theorem facArr_size : (facArr f row p).size = 2 ^ (f.mu + f.d) := tab_size _ _

/-- **The bits**: what the entries of the bits' table read as. Conditional on two planes at
least, at an entry's number in range (`hX`). -/
theorem bitTab_read (hp : 2 ≤ f.planes) {X : Nat} (hX : X < 2 ^ (f.mu + f.d)) :
    readV (bitArr f w) X = (datAt f row pads w p).bitAt X := by
  have e : f.planes - 2 + 2 = f.planes := by omega
  unfold bitArr
  rw [readV_tab _ _ hX]
  show readE (if X % 2 ^ f.mu < f.planes then w.bit (X / 2 ^ f.mu) (X % 2 ^ f.mu) else zeroE) =
    if X % 2 ^ f.mu < f.planes - 2 + 2 then up (w.bit (X / 2 ^ f.mu) (X % 2 ^ f.mu)) else 0
  rw [e]
  split
  · rfl
  · exact readE_zero

/-- **alpha - 1 - row**: what the entries of that table read as. Conditional on a shift whose words
are below the prime, at an entry's number in range (`hX`). -/
theorem facTab_read (ht : okE p.theta = true) {X : Nat} (hX : X < 2 ^ (f.mu + f.d)) :
    readV (facArr f row p) X = (datAt f row pads w p).rowAt X := by
  have hu : X / 2 ^ f.mu < 2 ^ f.d := by
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, Nat.add_comm]
    exact hX
  unfold facArr
  rw [readV_tab _ _ hX, tab_getD _ _ hu, readE_sub, readE_sub, readE_one]
  show _ = up p.alpha - 1 - up (row (down (up p.theta)) (X / 2 ^ f.mu))
  rw [down_up _ ht]

theorem facArr_ok (x : Nat) : okE ((facArr f row p).getD x zeroE) = true := by
  by_cases h : x < 2 ^ (f.mu + f.d)
  · unfold facArr
    rw [tab_getD _ _ h]
    by_cases h2 : x / 2 ^ f.mu < 2 ^ f.d
    · rw [tab_getD _ _ h2]
      exact ok_sub _ _
    · have : ((Array.range (2 ^ f.d)).map
          fun u => subE (subE p.alpha oneE) (row p.theta u)).getD (x / 2 ^ f.mu) zeroE = zeroE := by
        simp [Array.getD, h2]
      rw [this]
      rfl
  · have : (facArr f row p).getD x zeroE = zeroE := by
      have hs : (facArr f row p).size ≤ x := by rw [facArr_size]; omega
      simp [Array.getD, hs]
    rw [this]
    rfl

/-- Two tables of one size, joined entry by entry. -/
theorem zip_getD (op : E → E → E) (a b : Array E) {N i : Nat} (ha : a.size = N) (hb : b.size = N)
    (hi : i < N) :
    (Array.zipWith op a b).getD i zeroE = op (a.getD i zeroE) (b.getD i zeroE) := by
  simp [Array.getD, ha, hb, hi]

theorem zip_size (op : E → E → E) (a b : Array E) {N : Nat} (ha : a.size = N) (hb : b.size = N) :
    (Array.zipWith op a b).size = N := by
  simp [ha, hb]

/-- **The table side's levels**: the size of the array of level l, and what its entries read as.
Conditional on two planes at least and on a shift whose words are below the prime, at a level up to
d (`hl`). -/
theorem tabLvl_read (hp : 2 ≤ f.planes) (ht : okE p.theta = true) {l : Nat} (hl : l ≤ f.d) :
    ((srcAt f row w p).tabLvl l).size = 2 ^ (l + f.mu) ∧
      ∀ X < 2 ^ (l + f.mu),
        readV ((srcAt f row w p).tabLvl l) X = (datAt f row pads w p).tLvl l X := by
  have hc : 2 ^ (f.d + f.mu) = 2 ^ (f.mu + f.d) := by rw [Nat.add_comm]
  have hL := upN_level f.mu f.d
    (Cb.Lkp.facT f.mu (datAt f row pads w p).N.tab (datAt f row pads w p).bits
      (datAt f row pads w p).al)
    (Array.zipWith (fun b a => addE oneE (mulE b a)) (bitArr f w) (facArr f row p))
    (by rw [hc]; exact zip_size _ _ _ (bitArr_size f w) (facArr_size f row p))
    (fun X hX => by
      rw [hc] at hX
      unfold OnBytes.Slice.readV
      rw [zip_getD _ _ _ (bitArr_size f w) (facArr_size f row p) hX, readE_add, readE_mul,
        readE_one]
      have h1 := bitTab_read f row pads w p hp hX
      have h2 := facTab_read f row pads w p ht hX
      unfold OnBytes.Slice.readV at h1 h2
      rw [h1, h2]
      rfl) (f.d - l) (by omega)
  rw [show f.d - (f.d - l) = l by omega] at hL
  rw [tabLvl_eq]
  exact hL

theorem tabLvl_ok (l x : Nat) : okE (((srcAt f row w p).tabLvl l).getD x zeroE) = true := by
  rw [tabLvl_eq]
  refine ok_upN _ (fun y => ?_) _ x
  by_cases h : y < 2 ^ (f.mu + f.d)
  · rw [zip_getD _ _ _ (bitArr_size f w) (facArr_size f row p) h]
    exact ok_add _ _
  · have hs : (Array.zipWith (fun b a => addE oneE (mulE b a)) (bitArr f w)
        (facArr f row p)).size ≤ y := by
      rw [zip_size _ _ _ (bitArr_size f w) (facArr_size f row p)]
      omega
    have : (Array.zipWith (fun b a => addE oneE (mulE b a)) (bitArr f w)
        (facArr f row p)).getD y zeroE = zeroE := by
      simp only [Array.getD]
      rw [dif_neg (by omega)]
    rw [this]
    rfl

end

end ProofFile.Honest.K3.FastLaw

#print axioms ProofFile.Honest.K3.FastLaw.tab_out
#print axioms ProofFile.Honest.K3.FastLaw.tab_ok
#print axioms ProofFile.Honest.K3.FastLaw.keyLvl_ok
#print axioms ProofFile.Honest.K3.FastLaw.bitTab_eq
#print axioms ProofFile.Honest.K3.FastLaw.facTab_eq
#print axioms ProofFile.Honest.K3.FastLaw.tabLvl_eq
#print axioms ProofFile.Honest.K3.FastLaw.bitArr_size
#print axioms ProofFile.Honest.K3.FastLaw.facArr_size
#print axioms ProofFile.Honest.K3.FastLaw.bitTab_read
#print axioms ProofFile.Honest.K3.FastLaw.facTab_read
#print axioms ProofFile.Honest.K3.FastLaw.facArr_ok
#print axioms ProofFile.Honest.K3.FastLaw.zip_getD
#print axioms ProofFile.Honest.K3.FastLaw.zip_size
#print axioms ProofFile.Honest.K3.FastLaw.tabLvl_read
#print axioms ProofFile.Honest.K3.FastLaw.tabLvl_ok
#print axioms ProofFile.Honest.K3.FastLaw.up_size
#print axioms ProofFile.Honest.K3.FastLaw.readV_up
#print axioms ProofFile.Honest.K3.FastLaw.ok_up
#print axioms ProofFile.Honest.K3.FastLaw.upN_succ
#print axioms ProofFile.Honest.K3.FastLaw.upN_level
#print axioms ProofFile.Honest.K3.FastLaw.ok_upN
#print axioms ProofFile.Honest.K3.FastLaw.keyLvl_read
