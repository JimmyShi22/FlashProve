-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/FullRecLink.lean: UNDER THE THEOREM ON CODES, TAKEN AS GIVEN (`Cb.BCHKS46At`: a
hypothesis, which this file does not prove), AND UNDER A TIE TO THE DECISION: at the full-size files
of the setting "record with work" the written link with records, its batching and its chain of five
stages are round-by-round sound record by record, at radii beyond half the codes' distances.

The like of OnBytes/Slice/SmallRecLink.lean at the full size; its text was made from that file's by
a program that swaps names and numbers. `link_chain_joh` (OnBytes/Slice/LinkChainJoh.lean) is
general: it asks (1) conditions on sizes and radii, (2) the rounds' forms, (3) a chain with the
error counts of the letters, (4) that corners are different, (5) a tie to the decision, (6) the
place of the cut. This file applies it at one setting where a record has an answer, and fills (1),
(2), (3), (4), (6) and two of the three parts of (5):
 the sizes    `frS`: `frSz` (OnBytes/Slice/FullRecSz.lean) at the typed parameters' radii (the
              planner's distances times the lengths, rounded down: not shown here; in this library,
              on the same two numbers as they are typed under OnBytes/Params/: the first:
              `rr_radius`, OnBytes/Params/RecordRound.lean; the second lies from the first group's
              upper radius up to its lower one: `record_groups_upper`,
              OnBytes/Params/MorePricesRecord.lean, `record_groups_test`,
              OnBytes/Params/GroupPricesRecord.lean):
              2,852,142,980 (the tables' decoder and both folds) and 8,342,420 (a folded row's
              oracle message);
 the rounds   `frRd 0` to `frRd 40`, the rounds of the description `frD` at the typed
              parameter bytes, at every statement (`fr_ds_at`);
 the sample   `frZ`: the sample map `recZ` of one row, written after the programs'
              (OnBytes/Slice/RecordRead.lean), at 402,653,184 entries, 29 coordinates and one
              answer (`fr_lg`);
 the rows     `frRows`: the rows written out in OnBytes/Slice/RowsXRec.lean, the two records' rows
              among them, at the numbers `frN` (`RowNo.port`): 129 rows, as many as the plan's entry
              BAT says (`fr_rows_bat`). They meet `IsRowsR` (`fr_isRows`);
 the chain    `frC`: `frChain` (OnBytes/Slice/FullRecChain.lean);
 the word     `frW`, `frF`: the standard readings of the first tree (OnBytes/Slice/SemLib.lean).
              They meet `WordTie` (`fr_wordTie`).

Main definitions: `frS`, `frZ`, `frNum`, `frN`, `frRows`, `frC`, `frW`, `frF`.
Main theorems: `fr_Z`, `fr_lg`, `fr_rows_bat`, `fr_isRows`, `fr_ds_C`, `fr_link_lists`,
`fr_wordTie`, `fr_link_joh`.

WHAT `fr_link_joh` ASKS. `Cb.BCHKS46At`; and `hsem`: a yes of the written decision gives the
chain's yes in the field, at the claim that the batching makes of `frRows` and at the first tree
read by `frW` and `frF`. The decision and the list of stored openings are letters.

WHAT IT SHOWS. `hsem` IS THE TIE TO THE DECISION. IT IS SHOWN OF NO DECISION HERE;
OnBytes/Slice/FullRecYes.lean shows it of every decision whose yes gives the yes of the program's
link at two keys that hold r. At the decision that always says no it holds for free. So the instance
shows that the hypotheses of `link_chain_joh` on sizes, radii, rounds, chain, rows and word HOLD
TOGETHER at a record with one answer; by itself it does not show that the Lean port's verifier, or
any verifier, is sound.

Not claimed. THIS IS NO PROOF OF SOUNDNESS OF AN ENTRY FILE'S CHAIN: `hsem` is a hypothesis here, so
that the Lean port's rows are `frRows`, in coefficients or in order, and that it reads the trees as
the standard readings do, is not shown here. No error count is evaluated but six lists
(OnBytes/Slice/FullRecCodes.lean): with large counts the statement is true for free. The language
(`Sz.LangE2T`) has three ways out: the first table does not decode with its record, and at each
table a collision at its record's seed; where one is open the theorem says nothing. How often a
collision occurs, and where a seed comes from, is not said: r is any pair of records. That `hsem`
can hold of a decision that accepts anything: no transcript is shown at which the chain's yes in the
field holds. That the sizes are any file's: the heads of the files named above. All that the head of
OnBytes/Slice/LinkChainJoh.lean does not claim.

-/
import OnBytes.Slice.LinkChainJoh
import OnBytes.Slice.RecordRead
import OnBytes.Slice.RowsXRec
import OnBytes.Slice.SeedDrawn
import OnBytes.Slice.SemLib
import OnBytes.Slice.FullRecChain

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run Blocks

/-- The sizes at the typed parameters' radii (the planner's distances times the lengths, rounded
down): 2,852,142,980 for the tables' decoder and both folds, 8,342,420 for a folded row's oracle
message. -/
def frS : Sz := frSz 2852142980 2852142980 2852142980 8342420

/-- The sample map `recZ` of one row, written after the programs': 402,653,184 entries, 29
coordinates, one answer. -/
abbrev frZ : Sample GE frS.En := recZ 402653184 29 1

/-- The sample map and the cut, in the sizes' own letters. -/
theorem fr_Z : frZ = recZ frS.P.T.l 29 1 ∧ frS.P.T.l - 3 * 1 = 402653181 := ⟨rfl, rfl⟩

/-- The 29 coordinates and the one answer of `frZ` are the setting's: the plan's first entry,
RECORD, draws what one seed of 29 coordinates and a factor other than 0 is; 29 is the number of
variables of the cube of a row's entries, in the format's record and in the typed shape; the record
of a row has one answer, in both. -/
theorem fr_lg : (Params.recordPlan.entries.head?.map fun e => (e.drawE, e.drawNZ)) =
      some ((seedEntry 29 1).drawE, (seedEntry 29 1).drawNZ) ∧
    frS.P.aPhi = 29 ∧ frS.P.s = 1 ∧ Params.recordLink.table.cubeBits = 29 ∧
    Params.recordLink.table.answers = 1 :=
  ⟨rfl, fr_aPhi _ _ _ _, rfl, by decide +kernel, rfl⟩

/-- The numbering of the one answer. -/
noncomputable def frNum : frZ.S ≃ Fin 1 := Equiv.refl _

/-- The rows' numbers, in the order of `RowNo.port`. -/
noncomputable def frN : RowNo frS frZ := RowNo.port frS frZ 1 fun σ => frNum σ

/-- The rows, written out. -/
noncomputable def frRows : (frS.lkR frZ).X4 → (ℕ → GE) × (ℕ → (frS.sg 97).cIn.J → GE) :=
  rowsXR frS frZ 1 frNum 97

/-- The chain. -/
noncomputable def frC : Chain (frS.sg 97) := frChain 2852142980 2852142980 2852142980 8342420

/-- The word of main rows and the carried mask row, off the first tree. -/
def frW (o : (wRound (frRd 1)).Orc) : (frS.sg 97).cIn.Word :=
  wordIn (frS.sg 97) (col1 frS (frRd 1) o)

/-- The word of the fresh mask row, off the first tree. -/
def frF (o : (wRound (frRd 1)).Orc) : (frS.sg 97).cFr.Word :=
  wordFr (frS.sg 97) (col1 frS (frRd 1) o)

/-- As many rows are batched as the entry of the batching's round says: 129. -/
theorem fr_rows_bat : frN.n = 129 ∧ (frRd 5).entry.rows = 129 :=
  ⟨rfl, by rw [fr_rd5.entry]; rfl⟩

/-- The rows are the library's on each member's entries, the two records' rows among them. -/
theorem fr_isRows (x : (frS.lkR frZ).X4) : IsRowsR frS frZ 97 frN x (frRows x).1 (frRows x).2 :=
  isRowsR_rowsXR frS frZ 1 frNum 97 (fr_row_pow _ _ _ _) x

/-- The description's 41 rounds are the link's five, the batching's and the chain's. -/
theorem fr_ds_C : frD.ds =
    frRd 0 :: frRd 1 :: frRd 2 :: frRd 3 :: frRd 4 :: frRd 5 :: frC.rds := fr_ds_chain _ _ _ _

/-- The two lists that stand in the counts of `fr_link_joh`, as numbers: that of a folded row's
oracle message and that of the group's code, both 91. -/
theorem fr_link_lists :
    listMax (2 ^ frS.P.C.a) (2 ^ frS.P.C.a - (frS.P.C.r + frS.P.C.l) + 1) frS.eU = 91 ∧
      (frS.sg 97).lstJ frC.rad = 91 := by
  refine ⟨?_, ?_⟩
  · show listMax (2 ^ 24) (2 ^ 24 - (97 + 4194304) + 1) 8342420 = 91
    unfold listMax
    decide +kernel
  · show ((frSz 2852142980 2852142980 2852142980 8342420).sg 97).lstJ 8342420 = 91
    rw [fr_sg]
    exact fr_lists.1

/-- The standard word of the first tree holds the written symbols. -/
theorem fr_wordTie (o : (wRound (frRd 1)).Orc) : WordTie frS 97 (frRd 1) o (frW o) :=
  stdReads_word frS 97 frSg2 frSg3 (frRd 1) (frRd 1) (frRd 1) (frRd 1) (frRd 1) fr_width1 fr_pos1 o

/-- **Under `Cb.BCHKS46At` and a tie to the decision (`hsem`: a hypothesis here): at the
full-size files of the setting "record with work", link, batching and chain are round-by-round sound
at every pair of records r for `Sz.LangE2T`**, which has three ways out, at radii beyond half the
distances. The head lists what is asked and what is not claimed. -/
theorem fr_link_joh (hA : BCHKS46At GF GE) (xs : List PQ.XO) (dec : PQ.View → Bool)
    (r : (frS.lkR frZ).X0)
    (hsem : ∀ (y : (frS.lkR frZ).E0.Str) m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA (b : frC.Bl),
      (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4)
          (frRd 5 :: frC.rds) xs dec).accept () y
        (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, frC.trL b) = true →
      frC.Acc (sumStmR frN 97
          (frRows (st4R frS frZ r (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) y c1 m2 c2 m3 c4
            c5).1).1
          (frRows (st4R frS frZ r (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) y c1 m2 c2 m3 c4
            c5).1).2 (drawnE (frRd 5) cA))
        (frW m2.1) (frF m2.1) (frW m2.1) b) :
    (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) xs dec).Sound
      (fun _ y => frS.LangE2T frZ 402653181 r y)
      (0, coreErrR frS frZ (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frS.badJ frS.e0)
        (frS.badJ frS.e1)
        (fun _ => listMax (2 ^ frS.P.C.a) (2 ^ frS.P.C.a - (frS.P.C.r + frS.P.C.l) + 1) frS.eU)
        (batErrR frN ((frS.sg 97).lstJ frC.rad) (frRd 5), frC.errL)) :=
  link_chain_joh frS frZ hA (fr_radJ 8342420).1 frN (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4)
    (frRd 5) xs dec 402653181 (fr_cut _ _ _ _) (fr_pl_inj _ _ _ _ frZ) (fr_memb_plc_inj _ _ _ _)
    (fr_memb _ _ _).2.2 (fr_draws _ _ _ _) frC (fr_chain_plain _ _ _ _) (fr_chain_joh _ _ _ _)
    (Nat.le_refl 8342420) fr_bat frRows frW frF frW fr_isRows fr_wordTie r hsem

end OnBytes.Slice
