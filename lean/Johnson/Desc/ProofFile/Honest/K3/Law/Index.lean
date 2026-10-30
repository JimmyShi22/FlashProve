-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Index.lean: the honest side of the kind "lookup" (K3).
Conditional (at a lookup with one part of keys): which stage stands at which number of the row,
beside the numbers of rounds in front that Honest/K3/HeardLaw.lean has; the rounds of the tie's
steps; the number of all rounds; four small facts on a round without its sealed digest. Theorems;
the definitions are numbers.

Terms. Honest/K3/GLOSSARY.md ("row", "stage", "tie").

What is shown.
  `iTie`, `iJoin`, `iKey`, `iTab`: a stage's number in the row, as a sum.
  `at_shift`, `at_alpha`, `at_tie`, `at_join`, `at_key`, `at_keyLine`, `at_tab`, `at_tabLine`,
    `at_leaves`, `at_zero`, `at_bits`: (stages f)[number]? = some stage.
  `fr_tie`: how many rounds stand in front of the tie's step j.
  `rounds_all`, `stages_len`: the number of all rounds; of all stages.
  `quiet_noDigest`, `e1_noDigest`, `alone_noDigest`, `roundOf_noDigest`: what the pieces of the
    hearing read of a round, they read of the round without its sealed digest.
Helpers: `len_blkA`, `len_ties`, `len_keysL`, `len_tabsL`, `len_preJoin`, `len_preKey`,
`len_preTab`, `get_split`, `ties_split`.

Hypotheses that remain.
  `hp`: f.parts = [v]: one part of keys: in every theorem from `at_shift` to `rounds_all` (it comes
    in through a `variable`).
  `hs`: (in `at_shift`) the face has a shift. `hj`: (in `at_tie`, `fr_tie`) j < planes - 1. `hm`:
    (in `at_key`, `at_keyLine`) m < v. `hl`: (in `at_tab`, `at_tabLine`) l < d.
  `h`, `hn`: (in `get_split`, `ties_split`) the list is cut as said, at that length; j < n.
  The four facts on a round without its sealed digest have none.

Users. Honest/K3/Law/NoDigest.lean, Honest/K3/Law/SpecNumbered.lean, Honest/K3/Law/Walk.lean and
Honest/K3/Parts/Index.lean import this file.

Limits. One part of keys.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Forward

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3
open OnBytes (E zeroE)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.First.ProdV (elementsAlone)
open VerifiableInference.Desc (noDigest)

/-! ## The numbers -/

def iTie (f : LFace) (j : Nat) : Nat := oAlpha f + 1 + j
def iJoin (f : LFace) : Nat := oAlpha f + 1 + (f.planes - 1)
def iKey (f : LFace) (m : Nat) : Nat := iJoin f + 1 + 2 * m
def iTab (f : LFace) (v l : Nat) : Nat := iKey f v + 2 * l

theorem len_blkA (f : LFace) : (blkA f).length = oAlpha f := by
  unfold blkA oAlpha
  split <;> rfl

theorem len_ties (n : Nat) : (ties n).length = n := by simp [ties]

theorem len_keysL : ∀ n, (keysL n).length = 2 * n
  | 0 => rfl
  | n + 1 => by
    rw [keysL_succ, List.length_append, len_keysL n]
    simp
    omega

theorem len_tabsL : ∀ n, (tabsL n).length = 2 * n
  | 0 => rfl
  | n + 1 => by
    rw [tabsL_succ, List.length_append, len_tabsL n]
    simp
    omega

theorem len_preJoin (f : LFace) : (preJoin f).length = iJoin f := by
  simp [preJoin, iJoin, len_blkA, len_ties]
  omega

theorem len_preKey (f : LFace) (m : Nat) : (preKey f m).length = iKey f m := by
  simp [preKey, iKey, len_preJoin, len_keysL]
  omega

theorem len_preTab (f : LFace) (v l : Nat) : (preTab f v l).length = iTab f v l := by
  simp [preTab, iTab, len_preKey, len_tabsL]

theorem get_split {l pre post : List Stage} {s : Stage} {n : Nat} (h : l = pre ++ s :: post)
    (hn : pre.length = n) : l[n]? = some s := by
  subst hn
  rw [h]
  simp

theorem ties_split {j n : Nat} (h : j < n) : ∃ post, ties n = ties j ++ (Stage.tie j :: post) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h1 | h1
    · obtain ⟨post, e⟩ := ih h1
      exact ⟨post ++ [Stage.tie n], by rw [ties_succ, e]; simp⟩
    · subst h1
      exact ⟨[], by rw [ties_succ]⟩

section One
variable (f : LFace) (v : Nat) (hp : f.parts = [v])
include hp

theorem at_shift (hs : f.shifted = true) : (stages f)[0]? = some Stage.shift := by
  rw [stages_one f v hp]
  simp [preTab, preKey, preJoin, blkA, hs]

theorem at_alpha : (stages f)[oAlpha f]? = some Stage.alpha :=
  get_split (pre := blkA f)
    (post := ties (f.planes - 1) ++ (Stage.join :: keysL v) ++ tabsL f.d ++
      [Stage.leaves, Stage.zero, Stage.bits])
    (by rw [stages_one f v hp]; simp [preTab, preKey, preJoin]) (len_blkA f)

theorem at_tie {j : Nat} (hj : j < f.planes - 1) : (stages f)[iTie f j]? = some (Stage.tie j) := by
  obtain ⟨post, e⟩ := ties_split hj
  exact get_split (pre := blkA f ++ (Stage.alpha :: ties j))
    (post := post ++ (Stage.join :: keysL v) ++ tabsL f.d ++ [Stage.leaves, Stage.zero, Stage.bits])
    (by rw [stages_one f v hp]; simp [preTab, preKey, preJoin, e])
    (by simp [iTie, len_blkA, len_ties]; omega)

theorem fr_tie {j : Nat} (hj : j < f.planes - 1) :
    firstRound f (.tie j) = oAlpha f + 1 + 3 * j := by
  obtain ⟨post, e⟩ := ties_split hj
  have ea : Stage.rounds f .alpha = 1 := rfl
  rw [firstRound_split f (.tie j) (blkA f ++ (Stage.alpha :: ties j))
    (post ++ (Stage.join :: keysL v) ++ tabsL f.d ++ [Stage.leaves, Stage.zero, Stage.bits])
    (by rw [stages_one f v hp]; simp [preTab, preKey, preJoin, e])
    (by
      simp only [List.mem_append, List.mem_cons, not_or]
      refine ⟨notMem_blkA (by nofun), by nofun, ?_⟩
      intro hm
      obtain ⟨i, hi, e2⟩ := List.mem_map.1 hm
      have hi' := List.mem_range.1 hi
      have := Stage.tie.inj e2
      omega),
    List.map_append, List.sum_append, sum_blkA, List.map_cons, List.sum_cons, sum_ties, ea]
  omega

theorem at_join : (stages f)[iJoin f]? = some Stage.join :=
  get_split (pre := preJoin f)
    (post := keysL v ++ tabsL f.d ++ [Stage.leaves, Stage.zero, Stage.bits])
    (by rw [stages_one f v hp]; simp [preTab, preKey]) (len_preJoin f)

theorem at_key {m : Nat} (hm : m < v) : (stages f)[iKey f m]? = some (Stage.key 0 m) := by
  obtain ⟨post, e⟩ := keysL_split hm
  exact get_split (pre := preKey f m)
    (post := (Stage.keyLine 0 m :: post) ++ tabsL f.d ++ [Stage.leaves, Stage.zero, Stage.bits])
    (by rw [stages_one f v hp]; simp [preTab, preKey, e]) (len_preKey f m)

theorem at_keyLine {m : Nat} (hm : m < v) :
    (stages f)[iKey f m + 1]? = some (Stage.keyLine 0 m) := by
  obtain ⟨post, e⟩ := keysL_split hm
  exact get_split (pre := preKey f m ++ [Stage.key 0 m])
    (post := post ++ tabsL f.d ++ [Stage.leaves, Stage.zero, Stage.bits])
    (by rw [stages_one f v hp]; simp [preTab, preKey, e]) (by simp [len_preKey])

theorem at_tab {l : Nat} (hl : l < f.d) : (stages f)[iTab f v l]? = some (Stage.tab l) := by
  obtain ⟨post, e⟩ := tabsL_split hl
  exact get_split (pre := preTab f v l)
    (post := (Stage.tabLine l :: post) ++ [Stage.leaves, Stage.zero, Stage.bits])
    (by rw [stages_one f v hp]; simp [preTab, e]) (len_preTab f v l)

theorem at_tabLine {l : Nat} (hl : l < f.d) :
    (stages f)[iTab f v l + 1]? = some (Stage.tabLine l) := by
  obtain ⟨post, e⟩ := tabsL_split hl
  exact get_split (pre := preTab f v l ++ [Stage.tab l])
    (post := post ++ [Stage.leaves, Stage.zero, Stage.bits])
    (by rw [stages_one f v hp]; simp [preTab, e]) (by simp [len_preTab])

theorem at_leaves : (stages f)[iTab f v f.d]? = some Stage.leaves :=
  get_split (pre := preTab f v f.d) (post := [Stage.zero, Stage.bits]) (stages_one f v hp)
    (len_preTab f v f.d)

theorem at_zero : (stages f)[iTab f v f.d + 1]? = some Stage.zero :=
  get_split (pre := preTab f v f.d ++ [Stage.leaves]) (post := [Stage.bits])
    (by rw [stages_one f v hp]; simp) (by simp [len_preTab])

theorem at_bits : (stages f)[iTab f v f.d + 2]? = some Stage.bits :=
  get_split (pre := preTab f v f.d ++ [Stage.leaves, Stage.zero]) (post := [])
    (by rw [stages_one f v hp]; simp) (by simp [len_preTab])

theorem stages_len : (stages f).length = iTab f v f.d + 3 := by
  rw [stages_one f v hp]
  simp [len_preTab]

theorem rounds_all : ((stages f).map (Stage.rounds f)).sum = oEnd f v := by
  have e : Stage.rounds f .zero = 1 := rfl
  rw [stages_one f v hp, List.map_append, List.sum_append, sum_preTab]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, rounds_leaves, rounds_bits,
    e]
  simp only [oEnd, oBits, oZero, oLeaves]
  omega

end One

/-! ## A round without its sealed digest -/

theorem quiet_noDigest {n : Nat} {r : Fmt.RoundView} : Forward.Quiet n (noDigest r) ↔ Forward.Quiet n r :=
  ⟨fun q => ⟨q.vals, q.elems, q.poss, q.trits⟩, fun q => ⟨q.vals, q.elems, q.poss, q.trits⟩⟩

theorem e1_noDigest (r : Fmt.RoundView) : e1 (noDigest r) = e1 r := rfl

theorem alone_noDigest (rs : List Fmt.RoundView) : elementsAlone (rs.map noDigest) = elementsAlone rs := by
  unfold elementsAlone
  rw [List.all_map]
  rfl

theorem roundOf_noDigest (n k : Nat) (r : Fmt.RoundView) :
    MaskedSum.roundOf n k (noDigest r) = MaskedSum.roundOf n k r := rfl

#print axioms ProofFile.Honest.K3.len_blkA
#print axioms ProofFile.Honest.K3.len_ties
#print axioms ProofFile.Honest.K3.len_keysL
#print axioms ProofFile.Honest.K3.len_tabsL
#print axioms ProofFile.Honest.K3.len_preJoin
#print axioms ProofFile.Honest.K3.len_preKey
#print axioms ProofFile.Honest.K3.len_preTab
#print axioms ProofFile.Honest.K3.get_split
#print axioms ProofFile.Honest.K3.ties_split
#print axioms ProofFile.Honest.K3.at_shift
#print axioms ProofFile.Honest.K3.at_alpha
#print axioms ProofFile.Honest.K3.at_tie
#print axioms ProofFile.Honest.K3.fr_tie
#print axioms ProofFile.Honest.K3.at_join
#print axioms ProofFile.Honest.K3.at_key
#print axioms ProofFile.Honest.K3.at_keyLine
#print axioms ProofFile.Honest.K3.at_tab
#print axioms ProofFile.Honest.K3.at_tabLine
#print axioms ProofFile.Honest.K3.at_leaves
#print axioms ProofFile.Honest.K3.at_zero
#print axioms ProofFile.Honest.K3.at_bits
#print axioms ProofFile.Honest.K3.stages_len
#print axioms ProofFile.Honest.K3.rounds_all
#print axioms ProofFile.Honest.K3.quiet_noDigest
#print axioms ProofFile.Honest.K3.e1_noDigest
#print axioms ProofFile.Honest.K3.alone_noDigest
#print axioms ProofFile.Honest.K3.roundOf_noDigest

end ProofFile.Honest.K3
