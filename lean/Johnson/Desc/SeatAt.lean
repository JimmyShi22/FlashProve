-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/SeatAt.lean: DOES ONE SEAT FIT? Three definitions with code. It imports
Johnson/Desc/Msg.lean and OnBytes/Iop/Ground.lean (for the plain records `Codes`, `OracleShape`).
NOTHING IS PROVED IN THIS FILE.
  `longOf codes s`: the log-length of a shape's code as read: the larger of its main code's and its
    mask code's (the plain twin of the library's `aOf`, Johnson/Pack/Port.lean; that it is that:
    `longOf_eq`, Johnson/Desc/Sound/MeaningSig.lean).
  `padB codes s mask row place`: is it a place of the message's pad (the plain twin of the library's
    `padP`, Johnson/Pack/PortZ.lean; that it is that: `padB_inl`, `padB_inr`,
    Johnson/Desc/Sound/MsgSig.lean).
  `seatFaultAt F codes tag s j t`: what is amiss at an oracle message of the shape s that sits at
    tenant t of tree j, held against what the description's blocks tell of that tree
    (`Block.oracles`): nothing if all seven clauses of `SeatFits` (Johnson/Desc/Sound/MsgSig.lean)
    hold.
Who calls it: Johnson/Desc/SeatRun.lean (over a chain's record), and a sheet over the plan alone.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Msg
import OnBytes.Iop.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

/-- The log-length of a shape's code as read. -/
def longOf (codes : OnBytes.Codes) (s : OnBytes.OracleShape) : Nat :=
  max (codes.base.getD s.code default).logN (codes.mask.getD s.maskCode default).logN

/-- Is (mask row or main row (true: mask), row, place) a place of the pad of a message of the shape
s: with a mask row: the last place of the last mask row; without: the last places of the last main
row, one where a place holds an element of the extension field, else three. AT ONE ANSWER. -/
def padB (codes : OnBytes.Codes) (s : OnBytes.OracleShape) (mask : Bool) (row place : Nat) : Bool :=
  if mask then row + 1 == s.maskRows && place + 1 == (codes.mask.getD s.maskCode default).ell
  else s.maskRows == 0 && row + 1 == s.mainRows &&
    decide ((codes.base.getD s.code default).ell ≤ place + if s.mainDeg = 3 then 1 else 3)

/-- What is amiss at an oracle message of the shape s that sits at tenant t of tree j. tag: its name
in the print. -/
def seatFaultAt {Xi : Type} (F : FileDescription Xi) (codes : OnBytes.Codes) (tag : String)
    (s : OnBytes.OracleShape) (j t : Nat) : Option String :=
  match F.oracleAt j with
  | none => some s!"{tag}: tree {j} is told by no block"
  | some orc =>
    match orc.tenants[t]? with
    | none => some s!"{tag}: tree {j} has no tenant {t} ({orc.tenants.length} told)"
    | some n =>
      let bad : List String :=
        (if orc.logLength == longOf codes s then []
          else [s!"logLength {orc.logLength} | the code's {longOf codes s}"]) ++
        (if n.main == s.mainRows * s.mainDeg then []
          else [s!"main {n.main} | rows {s.mainRows} * degree {s.mainDeg}"]) ++
        (if n.mask == s.maskRows * 3 then [] else [s!"mask {n.mask} | rows {s.maskRows} * 3"]) ++
        (if s.mainRows == 0 || (codes.base.getD s.code default).logN == longOf codes s
          then [] else ["the mask's code is the longer"]) ++
        (if (orc.tenants.map fun x => x.main + x.mask).sum == orc.words then []
          else [s!"the tenants' words {(orc.tenants.map fun x => x.main + x.mask).sum} | " ++
            s!"the tree's {orc.words}"]) ++
        (if s.mainDeg == 1 || s.mainDeg == 3 then [] else [s!"degree {s.mainDeg}"])
      if bad.isEmpty then none
      else some (s!"{tag}: tree {j} tenant {t} (answers {s.answers}): " ++ "; ".intercalate bad)

end VerifiableInference.Desc
