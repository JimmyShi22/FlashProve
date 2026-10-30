-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/PaysWritten.lean: the closing of a segment (K10): what the book of coins hands each of the 25 closings, at
written values. The places, their numbers and the lists of carried messages as closed terms, and the tests that Lean's
kernel evaluates on them against the written book.

Limits. Facts on written values alone; the tie to the description of the head is in AtFullSide/K10/PaysAtHead.lean.
-/
import AtFullSide.K14.SwitchesLend
import AtFullSide.K14.RawMineAtK13
import AtFullSide.K14.RawEntriesKit
import Johnson.Desc.ProofFile.Honest.K10.AtLot
import Johnson.Desc.ProofFile.Honest.K10.BorneAt
import Johnson.AtFull.Desc.Lots.K9RowWritten
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open ProofFile.Honest ProofFile.Honest.K10 AtFullSide.K14
open VerifiableInference.Desc (Place KindName)
open VerifiableInference.Desc.First.Close (Par entries)
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.AtFull.Desc (spotsWritten)
open Johnson.G (codesFull2 proofSendsFull)
open P2Law.ProofPlan (WP declProofFull)

/-- The places that have rounds with their stretches of the declared rounds, written. -/
def xsW : List (ProofFile.Spot × List Fmt.DeclaredRound × Nat) := ProofFile.stretched spotsWritten declProofFull.1 0

/-- The text of `ProofFile.k10Par` at the groups of the written request. -/
def parW (xs : List (ProofFile.Spot × List Fmt.DeclaredRound × Nat)) (p : VerifiableInference.Desc.K9.Where) : Option Par :=
  (xs.find? fun x => x.1.place.kind == .K10 && x.1.place.link == some p.link).bind fun x =>
    ((OnBytes.reqGroups shapeFull)[p.link]?).bind fun Gr =>
      match x.2.1 with
      | bat :: _ :: round :: _ =>
        some { link := p.link, piece := p.pieceEq + 1, k := Gr.k, h := Gr.h
               rows := bat.entry.rows, workField := bat.entry.work
               workClose := round.entry.work, sent := List.range x.2.2 }
      | _ => none

/-- The numbers of the 25 closings, written. -/
def parsW : List Par :=
  (ProofFile.k9Links xsW).filterMap fun l => (ProofFile.k9Where xsW l).bind fun p => parW xsW p

/-- The parts that hold a sending at a place, of the names of its rounds: the body of `sendersIn`
(Honest/K10/BorneAt.lean). -/
def sendOf (pl : Place) (names : List String) : List Addr :=
  (partStarts (cutOfNames pl.kind names)).zipIdx.filterMap fun y =>
    if names[y.1]? == some "SEND seed" then some ⟨pl, y.2⟩ else none

/-- The text of `sendersIn` on entries. -/
def sendersE (xs : Johnson.AtFull.Desc.Lots.XsE) (j : Nat) : List Addr :=
  (xs.filter fun x => x.1.place.link == some j).flatMap fun x => sendOf x.1.place (x.2.1.map (·.name))

/-- The two texts are one. -/
theorem sendersIn_eq (xs : List (ProofFile.Spot × List Fmt.DeclaredRound × Nat)) (j : Nat) :
    sendersIn xs j = sendersE (xs.map Johnson.AtFull.Desc.Lots.toE) j := by
  have hf : (fun x : ProofFile.Spot × List Fmt.DeclaredRound × Nat => sendOf x.1.place (x.2.1.map (·.entry.name))) =
      fun x => sendOf (Johnson.AtFull.Desc.Lots.toE x).1.place
        ((Johnson.AtFull.Desc.Lots.toE x).2.1.map (·.name)) := by
    funext x
    show _ = sendOf x.1.place ((x.2.1.map (·.entry)).map (·.name))
    rw [List.map_map]
    rfl
  show ((xs.filter fun x => x.1.place.link == some j).flatMap fun x =>
    sendOf x.1.place (x.2.1.map (·.entry.name))) = _
  unfold sendersE
  rw [List.filter_map, List.flatMap_map, hf]
  rfl

/-- The parts that hold the sendings of segment j, moment by moment: written out. -/
def sendW (j : Nat) : List Addr :=
  if j = 0 then [⟨⟨1, some 0, 1, .K1⟩, 0⟩, ⟨⟨1, some 0, 4, .K1⟩, 0⟩, ⟨⟨1, some 0, 6, .K1⟩, 0⟩]
  else if j = 24 then [⟨⟨1, some 24, 2, .K2⟩, 0⟩, ⟨⟨1, some 24, 5, .K1⟩, 0⟩, ⟨⟨1, some 24, 7, .K1⟩, 0⟩]
  else [⟨⟨1, some j, 1, .K2⟩, 0⟩, ⟨⟨1, some j, 4, .K1⟩, 0⟩, ⟨⟨1, some j, 6, .K1⟩, 0⟩]

/-- What the part at a closing carries, written. -/
def borneW (P : Par) : List Borne :=
  borneOf shapeFull codesFull2 (fun j t => (sendW j).getD t default) P.link

/-- The list of `borneOf` at segment l hangs on the senders of the segments up to l alone. -/
theorem borneOf_congr {s : OnBytes.Params.ReqShape} {c : OnBytes.Codes} {f g : Nat → Nat → Addr} {l : Nat}
    (h : ∀ j, j ≤ l → f j = g j) : borneOf s c f l = borneOf s c g l := by
  have e : ∀ j ∈ List.range (l + 1), borneIn s c f (decide (j < l)) j = borneIn s c g (decide (j < l)) j := by
    intro j hj
    have hfj := h j (Nat.lt_succ_iff.1 (List.mem_range.1 hj))
    unfold borneIn
    rw [hfj]
  unfold borneOf
  simp only [List.flatMap_def]
  rw [List.map_congr_left e]

/-- The tests at one closing that read the written rows, the written short pieces of the book and the closing's rounds:
the closing's link is one of the 25; its place stands in the written first chain; the written table has no count for its
part and no row beyond that part; among the short pieces the entries by which the part spends are the one run that it
states, and no entry names a further part; the closing's rounds are not empty, and the cut makes them one part. -/
def closeOkB (P : Par) : Bool :=
  decide (P.link < 25) && (WP.first.blocksInOrder.map (·.place)).contains (closePlace P) &&
    dueAt rawRowsFirstW (closeAddr P) == ⟨0, 0⟩ &&
    !(rawRowsFirstW.any fun r => r.1.place == closePlace P && decide (1 ≤ r.1.part)) &&
    ((rawShortW.filter fun e => e.once && e.spender == closeAddr P).map Ahead.named) == closeSpends P &&
    !(rawShortW.any fun e => e.spender.place == closePlace P && decide (1 ≤ e.spender.part)) &&
    !(entries P).isEmpty &&
    cutOfNames .K10 ((entries P).map (·.name)) == [(entries P).length]

end AtFullSide.K10

#print axioms AtFullSide.K10.sendersIn_eq
#print axioms AtFullSide.K10.borneOf_congr
