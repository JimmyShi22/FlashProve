-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormBat.lean: THE FORM's HALF AT THE BATCHING: the letters for saying that the
batching's part in the kind's block (guardedProximityTestParts.bat, Johnson/Desc/K12/JoinGuarded.lean) RETURNS ok, and
that what it returns is batT (Johnson/Prover/Link/FormFirst.lean).

What is proved of them: Johnson/Prover/Link/FormBatLaws.lean.

Main names.
  batEntry e     a test on an entry of the plan: it is the entry of "BAT": nothing is sent, one
    element is drawn. How many rows it counts is left open.
  batCut cut     a test on the declared rounds that the frame deals to the batching: one round, with
    such an entry, that opens nothing.
  BatOwes p cut t G   A RECORD OF PREMISES, beside TestFront: nothing passes yet; the masks come
    early; the record's codes are the stages' (codesFit, Johnson/Desc/K12/Join.lean: guard (w)); no
    test of the group has begun; "BAT"'s entry counts just the rows that the test takes in; AND
    guard (g) AT THE RECORD BEHIND: gpOk and labelsOk (Johnson/Desc/K12/Law/FirstOk.lean,
    FirstCut.lean) say yes at batT, at every row without a kept form.

Limits. Letters and tests. GUARD (g) IS TAKEN OVER WHOLE, AS A PREMISE ON THE RECORD BEHIND: what it
asks of the book of trees and of the first switch's declared openings is not unfolded here.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Means
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- The entry of "BAT": nothing is sent; one element is drawn. -/
def batEntry (e : Fmt.Entry) : Bool :=
  e.name == "BAT" && e.drawNZ == 0 && e.count == 1 && e.msg == 0 && e.roots == 0 &&
    e.answers == 0 && e.poss == 0 && e.trits == 0 && e.drawE == 1

/-- The declared rounds of the batching. -/
def batCut : List Fmt.DeclaredRound → Bool
  | [d] => batEntry d.entry && d.stored.isEmpty && d.opens.isEmpty
  | _ => false

/-- **What the batching's part asks beside TestFront.** -/
structure BatOwes (p : P12) (cut : List Fmt.DeclaredRound) (t : T12) (G : Group) : Prop where
  pass : t.pass = .nothing
  early : p.early = true
  codes : codesFit p t.st = true
  idle : G.inRun = false
  count : ∀ d ∈ cut, d.entry.rows = (runRows t.st G).size
  gp : ∀ row : GroupRow, row.kept = #[] →
    H2K.First.gpOk p (batT t G row) = true ∧ H2K.First.labelsOk p (batT t G row) = true

end Johnson.Prover.Link
