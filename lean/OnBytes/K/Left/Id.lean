-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/Id.lean: the ID that the program compared is the statement word of the typed value:
`stmtId` (OnBytes/TypedOracleCompiler/Slice/EntryRunMain.lean) at the ground's shape of tables, the three public
files' digest, the first table's root as a typed digest, and the first table's seeds and answers in
the value.

The program tests `Model.Verify.idAsked id = some (Fmt.hex (Key.commitmentId shape cfg table))`, at
the planner's shape and digest. `idAsked` brings the ID that the user typed to its normal form (a
user may type capitals): so the equation is stated of `idAsked id`, not of id. `Key.commitmentId`
draws the record's seeds from the table's name itself (R4.11); `stmtId` writes the seeds that the
value holds: so the equation asks that the value's seeds are the drawn ones.

Main names:
  `shape_at`: the shape of tables that enters the ID is the ground's (by `link_at`,
    OnBytes/K/Left/Conv.lean).
  `stmtId_eq`: `stmtId` at a root of 32 bytes, written as a typed digest, and at the seeds and the
    answers of a converter's value is the hex of `Key.commitmentIdAt` at the seeds that the value
    holds, written back (`seedsL`, OnBytes/TypedOracleCompiler/Slice/SeedsBack.lean).
  `seedsOf_of_under`: the seeds that a converter lays at a table under the ground's parameters at c
    are the seeds that the commitment ID draws, where the field is the second and the shape has
    answers.
  `stmtId_eq_id`: so, where the value's seeds are these, the word is the hex of
    `Key.commitmentId`.
  `id_of_facts`: the equation, from the planner's yes, `Tie.SameChains`, `G.SaysLines`, "the root
    has 32 bytes", these three premises on the seeds and the program's test.
  `id_left`: the equation under `PortYesAt` and `G.SaysLines`, for every value whose first table is
    the table that the program threads and whose first seeds are the drawn ones.

Limits: values alone. Nothing on what an ID fixes: nothing on index binding, opening-form binding,
no two openings or correctness of extraction. That some files meet the premises is not shown.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.Conv
import OnBytes.TypedOracleCompiler.Slice.EntryRunMain
import Run.ParserHashProofs

set_option autoImplicit false

namespace OnBytes.K.Left
open OnBytes.Tie
open TypedOracleCompiler.Slice

/-- Under the planner's yes, `SameChains` and `G.SaysLines`: the shape of tables that enters the ID
is the ground's. -/
theorem shape_at (G : EntryGround) {F : Files} {p : Model.Verify.Planned}
    (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p)
    (hs : SameChains p (Params.configurationDigest [F.pol, F.lay, F.KL]))
    (hl : G.SaysLines F.pol) : p.chains.tableShape = G.q.link.table := by
  rw [tableShape_oneTime, hs.2.1.1, (link_at G hp hs hl).2]
  rfl

/-- The statement word of a converter's value is the hex of the commitment ID of its first table at
the seeds that the value holds. -/
theorem stmtId_eq (sh : Params.IndexShape) (c : ByteArray) (a : AskedE)
    (hr : a.first.root.size = 32) (lg s : ℕ) :
    stmtId sh c (_root_.Run.bytesToDig a.first.root) (xOfAskedC lg s a).2.1 (xOfAskedC lg s a).1.1 =
      Fmt.hex (Key.commitmentIdAt sh c [] a.first (seedsL (xOfAskedC lg s a).2.1)) := by
  unfold stmtId
  rw [_root_.Run.digToBytes_bytesToDig _ hr]
  rfl

/-- The seeds that a converter lays at a table under the ground's parameters at c are the seeds that
the commitment ID draws. -/
theorem seedsOf_of_under (G : EntryGround) (c : ByteArray) (t : Params.TableName)
    (l : List (List E × E)) (hF : G.q.given.plan.field = .two)
    (hA : (G.q.link.table.answers == 0) = false)
    (e0 : seedsUnder recordSeeds (linkAtCfg G.q c) t = some l) :
    Key.seedsOf G.q.link.table c t = some l := by
  -- by named equations, not by unfolding: see `Tie.seedsUnder_eq`
  rw [Key.seedsOf]
  rw [seedsUnder_eq, show (linkAtCfg G.q c).given.plan.field = .two from hF] at e0
  exact e0

/-- Where the value's seeds are the drawn ones, the word is the hex of the commitment ID. -/
theorem stmtId_eq_id (G : EntryGround) (c : ByteArray) (a : AskedE) (hr : a.first.root.size = 32)
    (hF : G.q.given.plan.field = .two) (hA : (G.q.link.table.answers == 0) = false)
    (e0 : seedsUnder recordSeeds (linkAtCfg G.q c) a.first = some a.l0) :
    stmtId G.q.link.table c (_root_.Run.bytesToDig a.first.root)
        (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers a).2.1
        (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers a).1.1 =
      Fmt.hex (Key.commitmentId G.q.link.table c a.first) := by
  rw [stmtId_eq _ _ a hr]
  unfold Key.commitmentId
  rw [seedsOf_of_under G c a.first a.l0 hF hA e0, Option.getD_some]
  have e1 := e0
  rw [seedsUnder_eq, show (linkAtCfg G.q c).given.plan.field = .two from hF] at e1
  show Fmt.hex (Key.commitmentIdAt _ _ _ _
    (seedsL (seedOfC G.q.link.table.cubeBits G.q.link.table.answers a.l0))) = _
  rw [show seedsL (seedOfC G.q.link.table.cubeBits G.q.link.table.answers a.l0) = a.l0 from
    seedsL_of_drawn _ _ _ _ e1]

/-- The ID that the program compared, in its normal form, is the statement word of the value. -/
theorem id_of_facts (G : EntryGround) {F : Files} {p : Model.Verify.Planned}
    (hp : Model.Verify.planned F.pol F.KL (some F.lay) = .ok p)
    (hs : SameChains p (Params.configurationDigest [F.pol, F.lay, F.KL]))
    (hl : G.SaysLines F.pol) {id : String} (a : AskedE) (hr : a.first.root.size = 32)
    (hF : G.q.given.plan.field = .two) (hA : (G.q.link.table.answers == 0) = false)
    (e0 : seedsUnder recordSeeds
      (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) a.first = some a.l0)
    (hid : Model.Verify.idAsked id =
      some (Fmt.hex (Key.commitmentId p.chains.tableShape p.cfg a.first))) :
    Model.Verify.idAsked id =
      some (stmtId G.q.link.table (Params.configurationDigest [F.pol, F.lay, F.KL])
        (_root_.Run.bytesToDig a.first.root)
        (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers a).2.1
        (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers a).1.1) := by
  rw [stmtId_eq_id G _ a hr hF hA e0, hid, shape_at G hp hs hl, hs.1.1]

/-- Under `PortYesAt` and `G.SaysLines`: for every value whose first table is the program's and
whose first seeds are the drawn ones. -/
theorem id_left (G : EntryGround) {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : G.SaysLines F.pol) (a : AskedE)
    (ha : a.first = table) (hF : G.q.given.plan.field = .two)
    (hA : (G.q.link.table.answers == 0) = false)
    (e0 : seedsUnder recordSeeds
      (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) a.first = some a.l0) :
    Model.Verify.idAsked id =
      some (stmtId G.q.link.table (Params.configurationDigest [F.pol, F.lay, F.KL])
        (_root_.Run.bytesToDig a.first.root)
        (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers a).2.1
        (xOfAskedC G.q.link.table.cubeBits G.q.link.table.answers a).1.1) := by
  subst ha
  obtain ⟨-, -, -, -, -, hr, -⟩ := entry_facts h
  obtain ⟨r, p, C, -, -, -, -, -, -, -, -, -, -, hp, -, -, -, -, -, hid, hs, -⟩ := h
  exact id_of_facts G hp hs hl a hr hF hA e0 hid

end OnBytes.K.Left
