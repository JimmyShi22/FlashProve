-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormSent.lean: THE FORM's HALF AT THE LINK's FRONT: the letters for what stands
behind the sending of the two folds, in front of the two joinings.

What is proved of them: Johnson/Prover/Link/FormSentLaws.lean.

Main names.
  FoldMsg T S u   the fold's message at the statement T: it is there, has the fold's shape, is
    sampled, and its pad is the public one (Send.pad, OnBytes/Iop/Send.lean).
  groupWith G o   the group G with the message o entered among its members, not kept: the group that
    a joining leaves (withMessageInGroup, OnBytes/Slice/BlkCalls.lean).
  recG1, recG2, recSt   the group behind the first table's share, and the group and the statement
    behind "(rec_gamma), twice", written out.
  LinkSent p d G  A RECORD OF PREMISES on the link's carried record d: the group that the small
    record names is there, is G, is in no test, has no member and no open claim yet, and has the
    link's main code; the two folds are two; each fold's FoldMsg, layout and conditions with the
    codes (foldeqOk, OnBytes/Iop/Foldeq.lean); the tests in front of (rec_gamma) (laysRecL,
    Johnson/Desc/K15/K15.lean: each key fits the shape; no seed has the factor 0; gamma's length).

Limits. Letters: nothing says here that a record meets them.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormSeatsLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params
open Desc.K15 (St Par15)

/-- The fold's message at a statement. -/
def FoldMsg (T : Statement) (S : FoldeqShape) (u : FoldedRow) : Prop :=
  ∃ (x : OnBytes.Oracle) (places : List PadPlace), T.oracles[u.oracle]? = some x ∧ x.shape = S.u ∧
    x.sampled = true ∧ x.pad = places.map (fun p => (p.part, p.index)) ∧
    Send.pad T.codes S.u = some places

/-- The group that a joining leaves. -/
def groupWith (G : Group) (o : Nat) : Group :=
  { G with
    members := G.members.insertIdxIfInBounds (G.members.filter (· < o)).size o
    kept := G.kept.insertIdxIfInBounds (G.members.filter (· < o)).size false }

/-- The group behind the first table's share of "(rec_gamma), twice". -/
def recG1 (G : Group) (o0 : Nat) (rows0 : List Row) : Group :=
  { groupWith G o0 with rows := G.rows ++ rows0.toArray }

/-- The group behind "(rec_gamma), twice". -/
def recG2 (G : Group) (o0 o1 : Nat) (rows0 rows1 : List Row) : Group :=
  { groupWith (recG1 G o0 rows0) o1 with rows := G.rows ++ rows0.toArray ++ rows1.toArray }

/-- The statement behind "(rec_gamma), twice": the first fold joins; its rows; the copy's fold
joins; its rows. -/
def recSt (T : Statement) (g o0 o1 : Nat) (G : Group) (rows0 rows1 : List Row) : Statement :=
  Slice.withRows (Slice.withMessageInGroup (Slice.withRows (Slice.withMessageInGroup T g o0 false G) g rows0) g o1 false
    (recG1 G o0 rows0)) g rows1

/-- **What stands behind the sending of the two folds.** -/
structure LinkSent (p : Par15) (d : St) (G : Group) : Prop where
  group : d.st.groups[d.loc.g]? = some G
  idle : G.inRun = false
  empty : G.members = #[]
  bare : G.rows = #[]
  code : G.code = p.S.code
  two : d.loc.o0.oracle ≠ d.loc.o1.oracle
  m0 : FoldMsg d.st (p.S.side false p.samples) d.loc.o0
  m1 : FoldMsg d.st (p.S.side true p.samples) d.loc.o1
  lay0 : d.loc.o0.lay = vectorLay d.st.codes (p.S.side false p.samples).u p.S.rowsHigh
  lay1 : d.loc.o1.lay = vectorLay d.st.codes (p.S.side true p.samples).u p.S.rowsHigh
  ok0 : foldeqOk d.st.codes (p.S.side false p.samples) = true
  ok1 : foldeqOk d.st.codes (p.S.side true p.samples) = true
  keys : VerifiableInference.Desc.Ground.ok (Desc.K15.laysRecL p d.loc) = true

end Johnson.Prover.Link
