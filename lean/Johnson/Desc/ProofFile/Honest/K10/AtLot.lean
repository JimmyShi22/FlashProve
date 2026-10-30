-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/AtLot.lean: the halves of the closing of a segment (K10) at the
places at which the proof file's description seats the kind's blocks. This file defines part of the
honest prover. Definitions with code; no theorem.

No lot bears the kind's name: its blocks come out of K9's lot (`k9Ninth`, Johnson/Desc/ProofFile/Lot/K9.lean), which
reads each block's numbers by `k10Par`. `closePars` reads them by the same calls, so that a half stands at each place at
which that lot lays the kind's block. `closeHalvesAt` makes the halves of such a list; `closeHalves` and `closings` are
the two together. Whoever writes the lot's honest side lists what this yields.

Limits. `closePars`, `closeHalves`, `closings` and `foldDueAll` are tried by no line: they want the public data of a
real description. `closeHalvesAt` and `foldDueAt` are tried at a toy's place (Honest/K10/ToyS.lean). The list of carried
messages and the fold's part are parameters (the list at a real description: Honest/K10/BorneAt.lean). The makers of
halves do not ask `foldDue`: `foldDueAll` asks it at all places at once, for whoever lists the halves. Where the lot
cannot read a segment's numbers it lays a block that refuses, and no half stands there. No property of the protocol is
claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Half
import Johnson.Desc.ProofFile.Lot.K9

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open VerifiableInference.Desc.First.Close (Par)

variable {V W X : Type}

/-- The numbers of the kind's places, segment by segment, as the lot reads them. -/
def closePars (Z : Pub) : List Par :=
  let xs := k9Stretches Z
  (k9Links xs).filterMap fun l => (k9Where xs l).bind fun p => k10Par Z xs p

/-- The kind's halves at a list of places. borne: the oracle messages that the part at a place
carries: public data. fold: the prover's side of the rounds from "FOLD epsilon" on. -/
def closeHalvesAt (pars : List Par) (borne : Par → List Borne) (fold : ClosePub → Part V W X) :
    List (Placed V W X) :=
  pars.map fun P => closeHalf fold ⟨P, borne P⟩

/-- **The kind's halves at all segments.** -/
def closeHalves (borne : Pub → Par → List Borne) (fold : ClosePub → Part V W X) (Z : Pub) :
    List (Placed V W X) :=
  closeHalvesAt (closePars Z) (borne Z) fold

/-- `foldDue` (Honest/K10/Half.lean) at each place of a list. -/
def foldDueAt (pars : List Par) (borne : Par → List Borne) (fold : ClosePub → Part V W X) : Bool :=
  pars.all fun P => foldDue ⟨P, borne P⟩ (fold ⟨P, borne P⟩)

/-- **One test for all places**: the parameter `fold` passes `foldDue` at every place that `closePars`
reads. It says yes where `closePars` reads no place, and asks nothing at a segment whose numbers the
lot cannot read. -/
def foldDueAll (borne : Pub → Par → List Borne) (fold : ClosePub → Part V W X) (Z : Pub) : Bool :=
  foldDueAt (closePars Z) (borne Z) fold

/-- `closeHalves`, typed as the honest side of K9's lot takes it. -/
def closings (borne : Pub → Par → List Borne) (fold : ClosePub → Part V W X) :
    Pub → Ground → List (Placed V W X) :=
  fun Z _ => closeHalves borne fold Z

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.closePars
#print axioms ProofFile.Honest.K10.closeHalvesAt
#print axioms ProofFile.Honest.K10.closeHalves
#print axioms ProofFile.Honest.K10.foldDueAt
#print axioms ProofFile.Honest.K10.foldDueAll
#print axioms ProofFile.Honest.K10.closings
