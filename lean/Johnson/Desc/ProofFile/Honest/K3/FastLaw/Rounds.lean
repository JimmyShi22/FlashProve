-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/FastLaw/Rounds.lean: at the four sorts of stage that have
variables, the round polynomial of the filling that folds tables is the specification's. Conditional
on the hypotheses below. Theorems.

Terms. Honest/K3/GLOSSARY.md.

What is shown. For a lookup with one part of keys, at a run's points: the function `round` of
`fastJobs f row` (Honest/K3/JobsFast.lean) and that of `specJobsAt f row pads`
(Honest/K3/JobsSpec.lean) yield the same list of the program's elements.
  `key_round`: at a level of the key tree. At the level without a variable it says nothing: there is
    no round there.
  `tab_round`: at a level of the table side's trees.
  `leaves_round`: at the leaves' sumcheck, with its cut to two coefficients in the planes' rounds.
  `bits_round`: at the bits' sumcheck.
  Helpers: `map_read`, `level_round`, and four theorems that write the two fillings' rounds out at
    the table side and at the bits (`fast_tab_def`, `spec_tab_def`, `fast_bits_def`,
    `spec_bits_def`).

Hypotheses that remain, each named in the statement.
  `S`: `Sized f v p` (Honest/K3/FastLaw/Tie.lean): one part of 2 ^ v keys, v at least 1; at least 2
    planes, at most 2 ^ mu; the shift's words are below the prime.
  `hm`, `hd`: the level lies in the tree.
  `hz`: the point has as many coordinates as the stage has variables.
  `ho`: the key level's order is a permutation.
  `hl`: there are fewer challenges than variables.
  In the helpers. `h`: (in `map_read`) X lies within the array. `hn`, `hg`: (in `level_round`) the
    array of the level below has its size and reads as g.

How the proof goes. It rests on Honest/K3/FastLaw/Round.lean (the routine on arrays is the
specification's `pjRound`), Honest/K3/FastLaw/Levels.lean (the arrays are the specification's
levels, bits and rows) and Honest/K3/FastLaw/Read.lean (from equality after reading, and words below
the prime, to equality). Of Honest/K3/FastLaw/InY.lean it calls `cut_size` and `cut_read` alone.

Users. `stages_agree` (Honest/K3/FastLaw/All.lean).

Limits. Rounds alone: the end values and the polynomial in Y are treated in other files (Tie.lean,
InY.lean). Nothing is said at a lookup with several parts, and nothing where a hypothesis fails.
Instances: `key_member`, `tab_member`, `leaves_member`, `bits_member`
(Honest/K3/FastLaw/RoundsMember.lean [not in this library; so here read: not proved in this
library]; by proof there).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.Round
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.Levels
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.Tie
import Johnson.Desc.ProofFile.Honest.K3.FastLaw.InY

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.FastLaw
open OnBytes (E addE subE mulE zeroE oneE okE)
open OnBytes.Slice (readE readV readE_sub readE_one readE_zero)
open OnBytes.HonestTrace.Look (pjRound)
open ProofFile.Honest.K3.Fast (prodRound)

/-! ## 1 An array under a map -/

theorem map_read (a : Array E) (g : E → E) (X : ℕ) (h : X < a.size) :
    readV (a.map g) X = readE (g (a.getD X zeroE)) := by
  have h1 : X < (a.map g).size := by rw [Array.size_map]; exact h
  unfold OnBytes.Slice.readV
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h1,
    Array.getElem?_eq_getElem h, Array.getElem_map]
  rfl

/-! ## 2 A level -/

/-- **A level's round**: n: the level below, 2 ^ (m + 1) entries; g: a function that agrees with it
below 2 ^ (m + 1). -/
theorem level_round (m : ℕ) (o : List ℕ) (z n : Array E) (g : ℕ → KE) (rs : List E)
    (ho : o.Perm (List.range m)) (hz : z.size = m) (hn : n.size = 2 ^ (m + 1))
    (hg : ∀ X, X < 2 ^ (m + 1) → readV n X = g X) (hl : rs.length < m) :
    prodRound zeroE m o z (n.extract 0 (2 ^ m)) (n.extract (2 ^ m) (2 ^ (m + 1))) rs =
      downs (pjRound m 0 g (fun X => g (X + 2 ^ m)) o (byBit z) (ups rs)) := by
  have hp : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by rw [pow_succ]; omega
  refine eq_downs (prodRound_ok _ _ _ _ _ _ _) ?_
  have e := prodRound_read' zeroE m o z (n.extract 0 (2 ^ m)) (n.extract (2 ^ m) (2 ^ (m + 1))) g
    (fun X => g (X + 2 ^ m)) rs ho hz
    (by rw [cut_size n _ _ (by omega)]; omega)
    (by rw [cut_size n _ _ (by omega)]; omega)
    (fun X hX => by
      rw [cut_read n 0 (2 ^ m) (by omega) (by omega), Nat.zero_add]
      exact hg X (by omega))
    (fun X hX => by
      rw [cut_read n (2 ^ m) (2 ^ (m + 1)) (by omega) (by omega), Nat.add_comm]
      exact hg _ (by omega))
    hl
  rw [readE_zero] at e
  exact e

/-! ## 3 The four sorts of stage -/

section
variable (f : LFace) (row : E → Nat → E) (pads : List (Nat × Nat)) (w : Hidden) (p : Pts)

/-- **Conditional on `Sized f v p`, m < v, the level's order a permutation, a point of m
coordinates, fewer challenges than m: a level of the key tree: the two fillings' round polynomials
are one list.** An instance: `key_member` (Honest/K3/FastLaw/RoundsMember.lean [not in this library;
so here read: not proved in this library]; by proof there). -/
theorem key_round {v : ℕ} (S : Sized f v p) {m : ℕ} (hm : m < v) (rs : List E)
    (ho : (f.orders 0 m).Perm (List.range m)) (hz : (p.keyPt 0 m).size = m)
    (hl : rs.length < m) :
    ((fastJobs f row).job (.key 0 m)).round w p rs =
      ((specJobsAt f row pads).job (.key 0 m)).round w p rs := by
  obtain ⟨h1, h2⟩ := keyLvl_read f row pads w p S.parts S.one (m := m + 1) hm
  exact level_round m (f.orders 0 m) (p.keyPt 0 m) ((srcAt f row w p).keyLvl 0 (m + 1))
    ((datAt f row pads w p).kLvl (m + 1)) rs ho hz h1 h2 hl

theorem fast_tab_def (l : ℕ) (rs : List E) :
    ((fastJobs f row).job (.tab l)).round w p rs =
      prodRound zeroE (f.mu + l) (OnBytes.Model.orderDefault (f.mu + l)) (p.tabPt l)
        (((srcAt f row w p).tabLvl (l + 1)).extract 0 (2 ^ (f.mu + l)))
        (((srcAt f row w p).tabLvl (l + 1)).extract (2 ^ (f.mu + l)) (2 ^ (f.mu + l + 1))) rs :=
  rfl

theorem spec_tab_def (l : ℕ) (rs : List E) :
    ((specJobsAt f row pads).job (.tab l)).round w p rs =
      downs (pjRound (f.mu + l) 0 ((datAt f row pads w p).tLvl (l + 1))
        (fun X => (datAt f row pads w p).tLvl (l + 1) (X + 2 ^ (f.mu + l)))
        (OnBytes.Model.orderDefault (f.mu + l)) (byBit (p.tabPt l)) (ups rs)) :=
  rfl

theorem fast_bits_def (rs : List E) :
    ((fastJobs f row).job .bits).round w p rs =
      prodRound zeroE (f.mu + f.d) (OnBytes.Model.orderDefault (f.mu + f.d)) p.zeroPt
        (bitArr f w) ((bitArr f w).map fun x => subE x oneE) rs := by
  simp only [fastJobs, Fast.stageJob]
  rfl

theorem spec_bits_def (rs : List E) :
    ((specJobsAt f row pads).job .bits).round w p rs =
      downs (pjRound (f.mu + f.d) 0 (datAt f row pads w p).bitAt
        (fun X => (datAt f row pads w p).bitAt X - 1)
        (OnBytes.Model.orderDefault (f.mu + f.d)) (byBit p.zeroPt) (ups rs)) :=
  rfl

/-- **Conditional on `Sized f v p`, l < d, a point of mu + l coordinates, fewer challenges than mu +
l: a level of the table side's trees: the two fillings' round polynomials are one list.** An
instance: `tab_member` (Honest/K3/FastLaw/RoundsMember.lean [not in this library; so here read: not
proved in this library]; by proof there). -/
theorem tab_round {v : ℕ} (S : Sized f v p) {l : ℕ} (hd : l < f.d) (rs : List E)
    (hz : (p.tabPt l).size = f.mu + l) (hl : rs.length < f.mu + l) :
    ((fastJobs f row).job (.tab l)).round w p rs =
      ((specJobsAt f row pads).job (.tab l)).round w p rs := by
  obtain ⟨h1, h2⟩ := tabLvl_read f row pads w p S.two S.theta (l := l + 1) hd
  have e : l + 1 + f.mu = f.mu + l + 1 := by omega
  rw [e] at h1 h2
  rw [fast_tab_def, spec_tab_def]
  exact level_round (f.mu + l) (OnBytes.Model.orderDefault (f.mu + l)) (p.tabPt l)
    ((srcAt f row w p).tabLvl (l + 1)) ((datAt f row pads w p).tLvl (l + 1)) rs
    (orderDefault_perm _) hz h1 h2 hl

/-- **Conditional on `Sized f v p`, a point of mu + d coordinates, fewer challenges than mu + d: the
leaves' sumcheck: the two fillings' round polynomials are one list.** An instance: `leaves_member`
(Honest/K3/FastLaw/RoundsMember.lean [not in this library; so here read: not proved in this
library]; by proof there). -/
theorem leaves_round {v : ℕ} (S : Sized f v p) (rs : List E)
    (hz : (p.tabPt f.d).size = f.mu + f.d) (hl : rs.length < f.mu + f.d) :
    ((fastJobs f row).job .leaves).round w p rs =
      ((specJobsAt f row pads).job .leaves).round w p rs := by
  have e := prodRound_read' oneE (f.mu + f.d) (OnBytes.Model.orderDefault (f.mu + f.d))
    (p.tabPt f.d) (bitArr f w) (facArr f row p) (datAt f row pads w p).bitAt
    (datAt f row pads w p).rowAt rs (orderDefault_perm _) hz (bitArr_size f w)
    (facArr_size f row p) (fun X hX => bitTab_read f row pads w p S.two hX)
    (fun X hX => facTab_read f row pads w p S.theta hX) hl
  rw [readE_one] at e
  have hc : (if (OnBytes.Model.orderDefault (f.mu + f.d)).getD (ups rs).length 0 < f.mu
      then 2 else 3) = if rs.length < f.d then 3 else 2 := by
    have hlen : (ups rs).length = rs.length := List.length_map _
    rw [hlen]
    by_cases h : rs.length < f.d
    · rw [if_pos h, if_neg (fun h' => (leaves_cut f.mu f.d rs.length hl).1 h' h)]
    · rw [if_neg h, if_pos ((leaves_cut f.mu f.d rs.length hl).2 h)]
  show (prodRound oneE (f.mu + f.d) (OnBytes.Model.orderDefault (f.mu + f.d)) (p.tabPt f.d)
      (bitArr f w) (facArr f row p) rs).take (if rs.length < f.d then 3 else 2) =
    downs ((pjRound (f.mu + f.d) 1 (datAt f row pads w p).bitAt (datAt f row pads w p).rowAt
      (OnBytes.Model.orderDefault (f.mu + f.d)) (byBit (p.tabPt f.d)) (ups rs)).take
      (if (OnBytes.Model.orderDefault (f.mu + f.d)).getD (ups rs).length 0 < f.mu then 2 else 3))
  rw [hc]
  refine eq_downs (fun x hx => prodRound_ok _ _ _ _ _ _ _ x (List.mem_of_mem_take hx)) ?_
  rw [List.map_take, e]
  rfl

/-- **Conditional on `Sized f v p`, a point of mu + d coordinates, fewer challenges than mu + d: the
bits' sumcheck: the two fillings' round polynomials are one list.** An instance: `bits_member`
(Honest/K3/FastLaw/RoundsMember.lean [not in this library; so here read: not proved in this
library]; by proof there). -/
theorem bits_round {v : ℕ} (S : Sized f v p) (rs : List E)
    (hz : p.zeroPt.size = f.mu + f.d) (hl : rs.length < f.mu + f.d) :
    ((fastJobs f row).job .bits).round w p rs =
      ((specJobsAt f row pads).job .bits).round w p rs := by
  have e := prodRound_read' zeroE (f.mu + f.d) (OnBytes.Model.orderDefault (f.mu + f.d))
    p.zeroPt (bitArr f w) ((bitArr f w).map fun x => subE x oneE) (datAt f row pads w p).bitAt
    (fun X => (datAt f row pads w p).bitAt X - 1) rs (orderDefault_perm _) hz (bitArr_size f w)
    (by rw [Array.size_map]; exact bitArr_size f w)
    (fun X hX => bitTab_read f row pads w p S.two hX)
    (fun X hX => by
      rw [map_read _ _ X (by rw [bitArr_size]; exact hX), readE_sub, readE_one]
      exact congrArg (· - 1) (bitTab_read f row pads w p S.two hX))
    hl
  rw [readE_zero] at e
  rw [fast_bits_def, spec_bits_def]
  exact eq_downs (prodRound_ok _ _ _ _ _ _ _) e

end

end ProofFile.Honest.K3.FastLaw

#print axioms ProofFile.Honest.K3.FastLaw.level_round
#print axioms ProofFile.Honest.K3.FastLaw.fast_tab_def
#print axioms ProofFile.Honest.K3.FastLaw.spec_tab_def
#print axioms ProofFile.Honest.K3.FastLaw.fast_bits_def
#print axioms ProofFile.Honest.K3.FastLaw.spec_bits_def
#print axioms ProofFile.Honest.K3.FastLaw.key_round
#print axioms ProofFile.Honest.K3.FastLaw.tab_round
#print axioms ProofFile.Honest.K3.FastLaw.leaves_round
#print axioms ProofFile.Honest.K3.FastLaw.bits_round
#print axioms ProofFile.Honest.K3.FastLaw.map_read
