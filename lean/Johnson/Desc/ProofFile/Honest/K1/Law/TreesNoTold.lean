-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/TreesNoTold.lean: THE THREAD's COUNT OF THE ORACLE MESSAGES
THAT THE SUB-PROTOCOLS IN FRONT STATE (treesTo, Honest/Thread/Thr.lean) IS THE TABLE's NUMBER OF
TREES AT THE PLACE, WHEREVER THE TABLE's NUMBERS ARE FILLED OFF WHAT THE BLOCKS TELL: the field
treesNo of the record of premises K1Seated (Honest/K1/Seated.lean), to the letter, at the real
table's numbers, under the record's own field placeAt. Four theorems; no definition. No head, no
scope and no plan is asked.

  - treesTo_told: treesTo bs b = treesTold (toldOf bs) b: the two texts are one, a bound name apart
    (told_is, Johnson/Desc/Sound/PieceFence.lean).
  - treesNo_withTold: UNDER hn : ps.Nodup and hp : ps[b]? = some p: treesTo bs b = (N₀.withTold ps
    (toldOf bs)).treesAt (some p), at every N₀ (Numbers.withTold,
    Johnson/Desc/First/BookNumbers.lean).
  - msgsAt_withTold: under the same two: (N₀.withTold ps (toldOf bs)).msgsAt (some p) = msgsTold
    (toldOf bs) b: the left side of the record's field firstNo.
  - treesNo_atN: UNDER hp : P5J.At.ps[b]? = some p: treesTo cF.blocksInOrder b = (P5J.At.N Zp cF).treesAt
    (some p) (Johnson/P5J/LettersAt.lean).

toldOf is Sound's (Johnson/Desc/Sound/PieceFence.lean), as in P5J.At.told; the library has a second
of that name (Johnson/Desc/First/NumbersAtBlocks.lean), written with "flatten"; P5J.At.told_is ties
the two texts at the chain's flat list.

By calls: told_is · borderOf_getElem (Johnson/Desc/First/BookFitTold.lean) · places_nodup_full
(Johnson/Desc/AtSeats/CountsAtFour.lean).

Kin in the library. trees_of_cut, trees_two_of_cut (Johnson/Desc/AtSeats/FromTheCut.lean): the
number itself at the fifty and at number 2, under a premise on the written cut. front_zero, front_at
(Johnson/P5J/LettersAt.lean): the like at the front place. bookFit
(Johnson/Desc/First/BookFit.lean): the test that a table's two numbers by place are what the blocks
in front tell.

Limits. It says that two counts are one; not what the count is. That a thread's letters are these is
the caller's: at ProofFile's lettersAt and lettersHead (Honest/Thread/FirstAt.lean, FirstHead.lean) they
are cF.blocksInOrder, P5J.At.N Zp cF and P5J.At.ps, and treesNo_atN is the record's field treesNo there, by
unfolding (RecordAtHead.lean). msgsAt_withTold is half of firstNo: that the count is the job's first
number is not said here. Nothing on soundness or on any other property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.Thread.Thr
import Johnson.Desc.First.BookFitTold
import Johnson.Desc.Sound.PieceFence
import Johnson.Desc.AtSeats.CountsAtFour
import Johnson.P5J.LettersAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain Place)
open VerifiableInference.Desc.First (S Numbers)

/-- ProofFile's count of the oracle messages in front is the library's count of what the blocks tell. -/
theorem treesTo_told {Cl : Type} (bs : List (Block S Cl)) (b : ℕ) :
    treesTo bs b = First.treesTold (Sound.toldOf bs) b :=
  (Sound.told_is bs b).symm

/-- **treesNo AT NUMBERS THAT ARE FILLED OFF THE TELLING.** -/
theorem treesNo_withTold {Cl : Type} (N₀ : Numbers) (ps : List Place) (hn : ps.Nodup)
    (bs : List (Block S Cl)) {b : ℕ} {p : Place} (hp : ps[b]? = some p) :
    treesTo bs b = (N₀.withTold ps (Sound.toldOf bs)).treesAt (some p) := by
  have hb : b ≤ ps.length := Nat.le_of_lt (List.getElem?_eq_some_iff.1 hp).1
  show _ = First.treesTold (Sound.toldOf bs) (First.borderOf ps (some p))
  rw [← hp, First.borderOf_getElem ps hn b hb]
  exact treesTo_told bs b

/-- The like for the messages: the left side of the record's field firstNo. -/
theorem msgsAt_withTold {Cl : Type} (N₀ : Numbers) (ps : List Place) (hn : ps.Nodup)
    (bs : List (Block S Cl)) {b : ℕ} {p : Place} (hp : ps[b]? = some p) :
    (N₀.withTold ps (Sound.toldOf bs)).msgsAt (some p) =
      First.msgsTold (Sound.toldOf bs) b := by
  have hb : b ≤ ps.length := Nat.le_of_lt (List.getElem?_eq_some_iff.1 hp).1
  show First.msgsTold (Sound.toldOf bs) (First.borderOf ps (some p)) = _
  rw [← hp, First.borderOf_getElem ps hn b hb]

/-- **AT THE REAL TABLE's NUMBERS**: the record's field treesNo, under its own field placeAt. -/
theorem treesNo_atN (Zp : ProofFile.Pub) (cF : Chain S ProofFile.Cl) {b : ℕ} {p : Place}
    (hp : (P5J.At.ps)[b]? = some p) :
    treesTo cF.blocksInOrder b = (P5J.At.N Zp cF).treesAt (some p) :=
  treesNo_withTold _ P5J.At.ps HashBuild.places_nodup_full cF.blocksInOrder hp

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.treesTo_told
#print axioms ProofFile.Honest.K1.treesNo_withTold
#print axioms ProofFile.Honest.K1.msgsAt_withTold
#print axioms ProofFile.Honest.K1.treesNo_atN
