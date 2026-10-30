-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormGave.lean: THE FORM's HALF AT THE LINK's FRONT: the letters for the first
two of K15's blocks: the record behind "LINK point", and what the sending's block leaves, as far as
the link's front reads it.

What is proved of them: Johnson/Prover/Link/FormFront6.lean.

Main names.
  pointT p d r    the record behind "LINK point": one more group, with the link's two codes, no
    member and no claim; gamma is what the round drew.
  SendGave p d1 d2   A RECORD OF PREMISES: d1 in front of the sending's block, d2 behind: codes and
    groups as in front; of the small record gamma, the group's number and the two keys as in front;
    the two folds are two; each fold's FoldMsg (Johnson/Prover/Link/FormSent.lean) and layout.
  linkWant S r    key, position and width of the columns that "LINK" is owed, its two groups one
    behind the other: as Block.step counts them (groupsOf, Johnson/Desc/Block.lean).

Limits. Letters. SendGave is paid by the shared sending's laws in FormSendGave.lean (sendK1_gave,
under SendFront, rounds that fit and 1 ≤ samples): not here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormSentLaws
import Johnson.Desc.K15.SendOwnLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params
open VerifiableInference.Desc
open Desc.K15 (St Par15)

/-- The record behind "LINK point". -/
def pointT (p : Par15) (d : St) (r : Fmt.RoundView) : St :=
  { d with
    st := Ground.withGroup d.st p.S.code p.S.maskCode
    loc := { d.loc with gamma := Desc.K14.drawn r, g := d.st.groups.size } }

/-- **What the sending's block leaves**, as far as the link's front reads it. -/
structure SendGave (p : Par15) (d1 d2 : St) : Prop where
  codes : d2.st.codes = d1.st.codes
  groups : d2.st.groups = d1.st.groups
  gamma : d2.loc.gamma = d1.loc.gamma
  g : d2.loc.g = d1.loc.g
  key0 : d2.loc.key0 = d1.loc.key0
  key1 : d2.loc.key1 = d1.loc.key1
  two : d2.loc.o0.oracle ≠ d2.loc.o1.oracle
  m0 : FoldMsg d2.st (p.S.side false p.samples) d2.loc.o0
  m1 : FoldMsg d2.st (p.S.side true p.samples) d2.loc.o1
  lay0 : d2.loc.o0.lay = vectorLay d2.st.codes (p.S.side false p.samples).u p.S.rowsHigh
  lay1 : d2.loc.o1.lay = vectorLay d2.st.codes (p.S.side true p.samples).u p.S.rowsHigh

/-- One stored part's columns: key, position, width. -/
def partWant (s : Fmt.Stored) (r : Fmt.RoundView) : List (Nat × Nat × Nat) :=
  (Fmt.listOf ((Fmt.partOf s r.drawn.poss).map (· % 2 ^ s.sh.a))).map fun x =>
    (Fmt.storedKey s.item, x, s.sh.W)

/-- The columns that "LINK" is owed. -/
def linkWant (S : LinkShape) (r : Fmt.RoundView) : List (Nat × Nat × Nat) :=
  (Desc.K15.readsAtLink S).flatMap fun s => partWant s r

end Johnson.Prover.Link
