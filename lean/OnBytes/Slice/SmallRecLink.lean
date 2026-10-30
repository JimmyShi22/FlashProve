-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SmallRecLink.lean: UNDER THE THEOREM ON CODES, TAKEN AS GIVEN (`Cb.BCHKS46At`: a
hypothesis, which this file does not prove), AND UNDER A TIE TO THE DECISION: at the small files of
the setting "record with work" the written link with records, its batching and its chain of three
stages are round-by-round sound record by record, at radii beyond half the codes' distances.

`link_chain_joh` (OnBytes/Slice/LinkChainJoh.lean) is general: it asks (1) conditions on sizes and
radii, (2) the rounds' forms, (3) a chain with the error counts of the letters, (4) that corners are
different, (5) a tie to the decision, (6) the place of the cut. This file applies it at one setting
where a record has an answer, and fills (1), (2), (3), (4), (6) and two of the three parts of (5):
 the sizes    `srS`: `srSz` (OnBytes/Slice/SmallRecSz.lean) at the typed parameters' radii (the
              planner's distances times the lengths, rounded down:
              OnBytes/Slice/SmallRecRadii.lean [not in this library]; in this library, on the same
              two numbers as they are typed under OnBytes/Params/: the first: `rs_radius`,
              OnBytes/Params/RecordRoundSmall.lean; the second lies from the first group's upper
              radius up to its lower one: `small_record_groups_upper`,
              `small_record_groups_test`, OnBytes/Params/EntryPricesRecordSmall.lean):
              6,137,119 (the tables' decoder and both folds) and 65,304 (a folded row's
              oracle message);
 the rounds   `srRd 0` to `srRd 23`, the rounds of the Lean port's description at the typed
              parameter bytes, at every statement (`sr_ds_at`);
 the sample   `srZ`: the sample map `recZ` of one row, written after the programs'
              (OnBytes/Slice/RecordRead.lean), at 524,288 entries, 19 coordinates and one
              answer (`sr_lg`);
 the rows     `srRows`: the rows written out in OnBytes/Slice/RowsXRec.lean, the two records' rows
              among them, at the numbers `srN` (`RowNo.port`): 107 rows, as many as the plan's entry
              BAT says (`sr_rows_bat`). They meet `IsRowsR` (`sr_isRows`);
 the chain    `srC`: `srChain` (OnBytes/Slice/SmallRecChain.lean);
 the word     `srW`, `srF`: the standard readings of the first tree (OnBytes/Slice/SemLib.lean).
              They meet `WordTie` (`sr_wordTie`).

Main definitions: `srS`, `srZ`, `srNum`, `srN`, `srRows`, `srC`, `srW`, `srF`.
Main theorems: `sr_Z`, `sr_lg`, `sr_rows_bat`, `sr_isRows`, `sr_ds_C`, `sr_link_lists`,
`sr_wordTie`, `sr_link_joh`.

WHAT `sr_link_joh` STILL ASKS. `Cb.BCHKS46At`; and `hsem`: a yes of the written decision gives the
chain's yes in the field, at the claim that the batching makes of `srRows` and at the first tree
read by `srW` and `srF`. The decision and the list of stored openings are letters.

WHAT IT SHOWS. `hsem` IS THE TIE TO THE DECISION. IT IS SHOWN OF NO DECISION HERE;
OnBytes/Slice/SmallRecYes.lean shows it of every decision whose yes gives the yes of the program's
link at two keys that hold r. At the decision that always says no it holds for free. So the instance
shows that the hypotheses of `link_chain_joh` on sizes, radii, rounds, chain, rows and word HOLD
TOGETHER at a record with one answer; by itself it does not show that the Lean port's verifier, or
any verifier, is sound.

Not claimed. THIS IS NO PROOF OF SOUNDNESS OF AN ENTRY FILE'S CHAIN: `hsem` is a hypothesis here, so
that the Lean port's rows are `srRows`, in coefficients or in order, and that it reads the trees as
the standard readings do, is not shown here. No error count is evaluated but four lists
(OnBytes/Slice/SmallRecCodes.lean): with large counts the statement is true for free. The language
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
import OnBytes.Slice.SmallRecChain

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run Blocks

/-- The sizes at the typed parameters' radii (the planner's distances times the lengths, rounded
down): 6,137,119 for the tables' decoder and both folds, 65,304 for a folded row's oracle
message. -/
def srS : Sz := srSz 6137119 6137119 6137119 65304

/-- The sample map `recZ` of one row, written after the programs': 524,288 entries, 19
coordinates, one answer. -/
abbrev srZ : Sample GE srS.En := recZ 524288 19 1

/-- The sample map and the cut, in the sizes' own letters. -/
theorem sr_Z : srZ = recZ srS.P.T.l 19 1 ∧ srS.P.T.l - 3 * 1 = 524285 := ⟨rfl, rfl⟩

/-- The 19 coordinates and the one answer of `srZ` are the setting's: the plan's first entry,
RECORD, draws what one seed of 19 coordinates and a factor other than 0 is; 19 is the number of
variables of the cube of a row's entries, in the format's record and in the typed shape; the record
of a row has one answer, in both. -/
theorem sr_lg : (Params.smallRecordPlan.entries.head?.map fun e => (e.drawE, e.drawNZ)) =
      some ((seedEntry 19 1).drawE, (seedEntry 19 1).drawNZ) ∧
    srS.P.aPhi = 19 ∧ srS.P.s = 1 ∧ Params.smallRecordLink.table.cubeBits = 19 ∧
    Params.smallRecordLink.table.answers = 1 :=
  ⟨rfl, sr_aPhi _ _ _ _, rfl, by decide +kernel, rfl⟩

/-- The numbering of the one answer. -/
noncomputable def srNum : srZ.S ≃ Fin 1 := Equiv.refl _

/-- The rows' numbers, in the order of `RowNo.port`. -/
noncomputable def srN : RowNo srS srZ := RowNo.port srS srZ 1 fun σ => srNum σ

/-- The rows, written out. -/
noncomputable def srRows : (srS.lkR srZ).X4 → (ℕ → GE) × (ℕ → (srS.sg 97).cIn.J → GE) :=
  rowsXR srS srZ 1 srNum 97

/-- The chain. -/
noncomputable def srC : Chain (srS.sg 97) := srChain 6137119 6137119 6137119 65304

/-- The word of main rows and the carried mask row, off the first tree. -/
def srW (o : (wRound (srRd 1)).Orc) : (srS.sg 97).cIn.Word :=
  wordIn (srS.sg 97) (col1 srS (srRd 1) o)

/-- The word of the fresh mask row, off the first tree. -/
def srF (o : (wRound (srRd 1)).Orc) : (srS.sg 97).cFr.Word :=
  wordFr (srS.sg 97) (col1 srS (srRd 1) o)

/-- As many rows are batched as the entry of the batching's round says: 107. -/
theorem sr_rows_bat : srN.n = 107 ∧ (srRd 5).entry.rows = 107 :=
  ⟨rfl, by rw [sr_rd5.entry]; rfl⟩

/-- The rows are the library's on each member's entries, the two records' rows among them. -/
theorem sr_isRows (x : (srS.lkR srZ).X4) : IsRowsR srS srZ 97 srN x (srRows x).1 (srRows x).2 :=
  isRowsR_rowsXR srS srZ 1 srNum 97 (sr_row_pow _ _ _ _) x

/-- The description's 24 rounds are the link's five, the batching's and the chain's. -/
theorem sr_ds_C : srD.ds =
    srRd 0 :: srRd 1 :: srRd 2 :: srRd 3 :: srRd 4 :: srRd 5 :: srC.rds := sr_ds_chain _ _ _ _

/-- The two lists that stand in the counts of `sr_link_joh`, as numbers: that of a folded row's
oracle message and that of the group's code, both 241. -/
theorem sr_link_lists :
    listMax (2 ^ srS.P.C.a) (2 ^ srS.P.C.a - (srS.P.C.r + srS.P.C.l) + 1) srS.eU = 241 ∧
      (srS.sg 97).lstJ srC.rad = 241 := by
  refine ⟨?_, ?_⟩
  · show listMax (2 ^ 17) (2 ^ 17 - (97 + 32768) + 1) 65304 = 241
    unfold listMax
    decide +kernel
  · show ((srSz 6137119 6137119 6137119 65304).sg 97).lstJ 65304 = 241
    rw [sr_sg]
    exact sr_lists.1

/-- The standard word of the first tree holds the written symbols. -/
theorem sr_wordTie (o : (wRound (srRd 1)).Orc) : WordTie srS 97 (srRd 1) o (srW o) :=
  stdReads_word srS 97 srSg2 srSg3 (srRd 1) (srRd 1) (srRd 1) (srRd 1) (srRd 1) sr_width1 sr_pos1 o

/-- **Under `Cb.BCHKS46At` and a tie to the decision (`hsem`: a hypothesis here): at the small
files of the setting "record with work", link, batching and chain are round-by-round sound at every
pair of records r for `Sz.LangE2T`**, which has three ways out, at radii beyond half the distances.
The head lists what is asked and what is not claimed. -/
theorem sr_link_joh (hA : BCHKS46At GF GE) (xs : List PQ.XO) (dec : PQ.View → Bool)
    (r : (srS.lkR srZ).X0)
    (hsem : ∀ (y : (srS.lkR srZ).E0.Str) m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA (b : srC.Bl),
      (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4)
          (srRd 5 :: srC.rds) xs dec).accept () y
        (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, srC.trL b) = true →
      srC.Acc (sumStmR srN 97
          (srRows (st4R srS srZ r (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) y c1 m2 c2 m3 c4
            c5).1).1
          (srRows (st4R srS srZ r (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) y c1 m2 c2 m3 c4
            c5).1).2 (drawnE (srRd 5) cA))
        (srW m2.1) (srF m2.1) (srW m2.1) b) :
    (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) xs dec).Sound
      (fun _ y => srS.LangE2T srZ 524285 r y)
      (0, coreErrR srS srZ (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srS.badJ srS.e0)
        (srS.badJ srS.e1)
        (fun _ => listMax (2 ^ srS.P.C.a) (2 ^ srS.P.C.a - (srS.P.C.r + srS.P.C.l) + 1) srS.eU)
        (batErrR srN ((srS.sg 97).lstJ srC.rad) (srRd 5), srC.errL)) :=
  link_chain_joh srS srZ hA (sr_radJ 65304).1 srN (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4)
    (srRd 5) xs dec 524285 (sr_cut _ _ _ _) (sr_pl_inj _ _ _ _ srZ) (sr_memb_plc_inj _ _ _ _)
    (sr_memb _ _ _).2.2 (sr_draws _ _ _ _) srC (sr_chain_plain _ _ _ _) (sr_chain_joh _ _ _ _)
    (Nat.le_refl 65304) sr_bat srRows srW srF srW sr_isRows sr_wordTie r hsem

end OnBytes.Slice
