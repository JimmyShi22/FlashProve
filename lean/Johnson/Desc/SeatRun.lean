-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/SeatRun.lean: A TEST THAT A RUN CAN MAKE: DO THE SEATS FIT? Definitions with code. It
imports Johnson/Desc/Msg.lean and Johnson/Desc/SmpRows.lean (so OnBytes/Iop/Ground.lean's plain
records). NOTHING IS PROVED IN THIS FILE.

Why. `SeatFits` (Johnson/Desc/Sound/MsgSig.lean) asks of each sampled member: its tree is told; the
tree's log-length is that of the member's code as read; the tenant's main words are its main rows,
each of its degree; its mask words its mask rows, three words each; and the main code is the long
one. Its letters (the shapes, the seats) are functions of the plan. A chain's record, behind the
chain's last sending, holds them: the session's statement has each oracle message's shape, the book
its tree and its place there. So a run over a stored proof can hold every oracle message of the
chain against what the description's blocks tell (`Block.oracles`).
  `seatFault F st book o`: what is amiss at the oracle message number o of a record (`seatFaultAt`,
    Johnson/Desc/SeatAt.lean).
  `seatLines F st book`: the print's lines: how many oracle messages; how many sampled, and with how
    many answers; how many without a fault; and each fault in words.
Limits. It speaks of one record of one run. A tree's number in the book is taken for its number
through the file (SmpRows.lean's Limits): if the two part, the faults will say so.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.SeatAt
import Johnson.Desc.SmpRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

/-- What is amiss at the oracle message number o of a record. -/
def seatFault {Xi : Type} (F : FileDescription Xi) (st : OnBytes.Statement) (book : OnBytes.TreeBook)
    (o : Nat) : Option String :=
  match st.oracles[o]?, book.place[o]? with
  | none, _ => some s!"{o}: no such oracle message"
  | _, none => some s!"{o}: the book has no place for it"
  | some x, some (j, t) => seatFaultAt F st.codes s!"{o}" x.shape j t

/-- The print's lines. -/
def seatLines {Xi : Type} (F : FileDescription Xi) (st : OnBytes.Statement) (book : OnBytes.TreeBook) :
    List String :=
  let all := List.range st.oracles.size
  let faults := all.filterMap (seatFault F st book)
  let sampled := all.filter fun o => ((st.oracles[o]?).map (·.sampled)).getD false
  let one := sampled.filter fun o => ((st.oracles[o]?).map (·.shape.answers == 1)).getD false
  let held := all.filter fun o =>
    match book.place[o]? with
    | some (j, t) => smpHeld st book j t
    | none => false
  [s!"SEATS = oracle messages {all.length} ; trees in the book {book.trees.size} ; sampled " ++
    s!"{sampled.length} ; of these with one answer {one.length} ; whose sample the record holds " ++
    s!"{held.length} ; without a fault {all.length - faults.length} ; faults {faults.length}"] ++
    (faults.take 40).map fun f => "SEAT-FAULT = " ++ f

end VerifiableInference.Desc
