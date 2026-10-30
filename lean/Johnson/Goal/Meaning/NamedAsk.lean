-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/NamedAsk.lean: A TEST ON PUBLIC DATA FOR THE PROOF FILE's DOOR (LPFD.lawsAsk,
Johnson/Desc/Laid/ProofAsks.lean): every committed matrix that a sub-proof's list names lies in the
layout of the request, with that entry's rows of packed symbols and its columns. Definitions alone;
no theorem. IT BRINGS NO MATHLIB BENEATH THE DOOR: Johnson/Desc/LaidAt.lean and
Johnson/Desc/First/Look/K3Asks.lean reach none; the type ProofFile.Pub's own file is beneath the door
already. NO SOUNDNESS IS CLAIMED. Nothing is evaluated in this file.

Why. Meaning.seatsOf (Johnson/Goal/Meaning/HidSeatsOf.lean) names, for every element of a committed
matrix, the message, the row and the place at which it lies; where the layout's reader gives nothing
it names (0, 0, 0) IN SILENCE. The fence is the test Meaning.laidThere. Several laws take laidThere
… = true as a premise. It is no theorem: it speaks of the public files' content. So a test is
defined here, for the door to ask. No entry of LPFD.lawsAsk asks it in this library.

  tlK X k   the plan's parameters of sub-proof k's range check: the light Look.tlAt
    (Johnson/Desc/First/Look/Laid.lean) is called; no new text.
  labK X k a   the label of entry a of sub-proof k's list.
  linkK id, nameK a   SECOND TEXTS of Meaning.linkOf and Meaning.nameOf, whose files stand over
    Mathlib: that they are the same: linkK_eq, nameK_eq (Johnson/Goal/Meaning/NamedAskLaw.lean).
  namedB X layout   THE TEST: 25 lists; at the full stored files 176 entries.
  namedAt Z   THE ROW, BARE: a function of the public part Z : ProofFile.Pub. FULL SIZE ONLY. It makes no
    Z and lays no guard: both are the door's.

THE WORDS UNDER WHICH IT WOULD REFUSE: "the public files do not lay every committed matrix that a
sub-proof's list names, with that entry's rows and columns, in the layout of the request". THE LAW
THAT NEEDS IT: laidThere_of_at (Johnson/IMR/NamedAskAt.lean, which no file of this library imports):
a yes at the full size's shape gives Meaning.laidThere Z.p.X (Meaning.sizesOf Z.p.X) Z.first.layout = true.

OBJECT: no block's text. USER: Johnson/Goal/Meaning/NamedAskLaw.lean, NamedView.lean. LETTERS: Z.

Limits. linkK IS THE FULL SIZE's. The test does not ask that the matrix is laid at every one of its
elements: that follows from the programs' own test on the layout (reqLayoutOk), which the first
state's making asks. Not claimed: anything on soundness, completeness or hiding.
-/
import Johnson.Desc.LaidAt
import Johnson.Desc.First.Look.K3Asks
import Johnson.Desc.ProofFile.Pub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Meaning.NamedAsk

open OnBytes OnBytes.Model
open VerifiableInference.Desc (arrayOf)
open VerifiableInference.Desc.K3Asks (nMat symRowsAt colsAt)

/-- The plan's parameters of sub-proof k's range check; the empty ones where the plan has none. -/
def tlK (X : Verify.Public) (k : Nat) : HTailF2 :=
  (VerifiableInference.Desc.First.Look.tlAt X k).getD {}

/-- The label of entry a of sub-proof k's list of committed matrices. -/
def labK (X : Verify.Public) (k a : Nat) : Nat := ((tlK X k).mats.getD a {}).aId

/-- The number of the sub-proof with the identifier id, AT THE FULL SIZE. -/
def linkK (id : Nat) : Nat :=
  if id = 13 then 24 else if id < 13 then 2 * (id - 1) else 2 * (id - 14) + 1

/-- A committed matrix's name in the layout of the request. -/
def nameK (a : Nat) : String := "M" ++ toString a

/-- **THE TEST**: for every entry of the 25 lists: the matrix that its label names, at the sub-proof
that owns it, is there in the layout, with the entry's rows of packed symbols and its columns. -/
def namedB (X : Verify.Public) (layout : Params.ReqLayout) : Bool :=
  (List.range 25).all fun k => (List.range (nMat (tlK X k))).all fun a =>
    match arrayOf layout (linkK (labK X k a / 256)) (nameK (labK X k a % 256)) with
    | none => false
    | some A => A.sizeI == symRowsAt (tlK X k) a && A.sizeC == colsAt (tlK X k) a

/-- **THE ROW, BARE, ON THE PUBLIC PART AS IT IS MADE OF THE THREE FILES.** FULL SIZE ONLY: linkK is
the full size's: the door lays its own guard in front. -/
def namedAt (Z : ProofFile.Pub) : Bool := namedB Z.p.X Z.first.layout

end Meaning.NamedAsk
