-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K9RowFull.lean: THE ROW OF KIND K9's LOT, PART 4: IN THE
  FORM OF PLAIN DATA IN WHICH back_at_full TAKES IT (ProofFile.Sk.Full.RowAt,
  Johnson/Desc/ProofFile/Law/Skel/Full/Ask.lean; back_of_written's hk,
  SkelWritten.lean), AGAINST THE WRITTEN SKELETON OF THE LOT (ProofFile.Sk.Full.lot7,
  Full/Data.lean: data made by program off an evaluator's print). One definition
  with code; statements and proofs. The term and hs stand at Full/Data.lean's
  written places spotsW: the row's one use has B.spots = spotsW; the end is
  RowAt.

THE NAMES.
lotW_cut: the plain data of a skeleton at the numbers ls does not see the cut at ls. (The same law
  stands beside lotW in Skel/Full/Rows.lean; one of the two is to fall.)
k9SkF: the lot's skeleton (k9SkE) at the written places spotsW, the written first chain's
  entries esW, the written shape's groups groupsW and twW (part 3's three).
links_full: the numbers of these places' segments are 0, 1, …, 24: by Lean's kernel. Nothing here
  spends it: it shows that ht's "∀ l ∈ lsW" ranges over 25 numbers and is not idle.
k9_row_cutF: k9_row_at (part 2) at these four values.
lot7_is: **THE CLOSED FACT: lotW asW lsW k9SkF = lot7: by Lean's kernel**: name, letters, still; the
  75 blocks' skeletons IN ORDER, names and all; the batchings at every asked place (25 answer); the
  numbers at which each and tests are supplied.
k9_row_full: **(hs : spotsOf Z.cuts = some spotsW) (he : Z.D.1.map (·.entry) = esW) (hg :
  Z.s₀.check.frame.groups = groupsW) (ht : ∀ l ∈ lsW, (K9.testsWhere Z.p.X l 0).isSome = twW l) ⊢
  RowAt G (k9Ninth Z) lot7.**

WHAT THE CLOSED FACT IS WORTH. lot7 comes off the very code that it describes (its file's own
  words): AS A WITNESS it is worth nothing. AS A STEP it is all that is asked: in back_of_written
  the lots' plain data is a letter, named so that the four closed facts can be decided over a
  written value; were lot7 wrong anywhere, lot7_is would be red. It says more than part 3's tests:
  the order, the names, and that no batching is supplied at another asked place. What is independent
  of lot7 are part 3's facts against cutFirstFull.
Limits. THE FOUR HYPOTHESES ARE PREMISES (part 3's Limits stand). lsW here is Full/Data.lean's
  (linksOf spotsW). hs speaks of spotsW; spots_written speaks of its own list spotsWritten: by two
  programs the two literals are one text, sign for sign; no theorem here says so. The file imports
  part 3 for walkE and the three written values. THAT THE CLOSED FACT CAN FAIL IS SHOWN BY NO LINE
  HERE: negative tests are not in this file. Synthetic weights. The full size alone. Nothing on
  soundness.
-/
import Johnson.AtFull.Desc.Lots.K9RowWritten
import Johnson.Desc.ProofFile.Law.Skel.Full.Ask

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Desc.Lots
open VerifiableInference.Desc
open ProofFile ProofFile.Sk
open ProofFile.Sk.Full (spotsW lot7 asW RowAt)

/-- The plain data at the numbers ls does not see the cut at ls. -/
theorem lotW_cut (as : List Place) (ls : List Nat) (k : LotSk) :
    lotW as ls (k.cut ls) = lotW as ls k := by
  have e : ∀ p : Nat → Bool, (ls.filter fun l => ls.contains l && p l) = ls.filter p :=
    fun p => List.filter_congr fun l hl => by
      rw [List.contains_eq_mem, decide_eq_true hl, Bool.true_and]
  show ({ name := k.name, letters := k.letters, still := k.still, blocks := k.blocks
          batch := as.filterMap fun a => (k.batch a).map fun s => (a, s)
          each := ls.filter fun l => ls.contains l && k.each l
          tests := ls.filter fun l => ls.contains l && k.tests l } : LotW) = _
  rw [e, e]
  rfl

/-- **K9's lot's skeleton at the written places `spotsW`.** -/
def k9SkF : LotSk := k9SkE groupsW (walkE spotsW esW 0) twW

theorem links_full : ProofFile.Sk.Full.lsW = List.range 25 := by decide +kernel

/-- Part 2's row at these four values. -/
theorem k9_row_cutF (Z : Pub) (G : Ground) (hs : spotsOf Z.cuts = some spotsW)
    (he : Z.D.1.map (·.entry) = esW) (hg : Z.s₀.check.frame.groups = groupsW)
    (ht : ∀ l ∈ ProofFile.Sk.Full.lsW, (K9.testsWhere Z.p.X l 0).isSome = twW l) :
    (lotSk G (k9Ninth Z)).cut ProofFile.Sk.Full.lsW = k9SkF.cut ProofFile.Sk.Full.lsW := by
  rw [k9_row_at Z G ProofFile.Sk.Full.lsW hs he hg ht, walk_eq]
  rfl

/-- **THE CLOSED FACT.** -/
theorem lot7_is : lotW asW ProofFile.Sk.Full.lsW k9SkF = lot7 := by decide +kernel

/-- **THE ROW, AS back_at_full TAKES IT.** -/
theorem k9_row_full (Z : Pub) (G : Ground) (hs : spotsOf Z.cuts = some spotsW)
    (he : Z.D.1.map (·.entry) = esW) (hg : Z.s₀.check.frame.groups = groupsW)
    (ht : ∀ l ∈ ProofFile.Sk.Full.lsW, (K9.testsWhere Z.p.X l 0).isSome = twW l) :
    RowAt G (k9Ninth Z) lot7 := by
  show lotW asW ProofFile.Sk.Full.lsW (lotSk G (k9Ninth Z)) = lot7
  rw [← lotW_cut asW ProofFile.Sk.Full.lsW (lotSk G (k9Ninth Z)), k9_row_cutF Z G hs he hg ht, lotW_cut]
  exact lot7_is

end Johnson.AtFull.Desc.Lots

#print axioms Johnson.AtFull.Desc.Lots.lotW_cut
#print axioms Johnson.AtFull.Desc.Lots.links_full
#print axioms Johnson.AtFull.Desc.Lots.k9_row_cutF
#print axioms Johnson.AtFull.Desc.Lots.lot7_is
#print axioms Johnson.AtFull.Desc.Lots.k9_row_full
