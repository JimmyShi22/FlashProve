-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Desc/First/K4/Plain.lean: the layers' own rounds as plain functions on data.

The text of Hear.lean is written over a record of operations (Engine.lean). Here the record is
filled with the library's plain functions on the sub-proof's ledger and a list of rounds
(OnBytes/K/Kc/Flat.lean, QuietLink.lean): `engFl`. The claims are plain lists (Claims.lean); here
the three own claims that are made only behind the hearing are laid, and the lookup's claims marked.
Main names (namespace `OnBytes.Desc.First.K4`).
  `hearFl P hp g fo`: HEAR. From the ledger and the stretch's rounds to what was heard, the ledger
    and the rounds left.
  `formsFront P g o`, `formsFrontNoRows P g o`, `formsBack o`: CLAIMS. From what was heard, and the
    ledger, to a list of
    linear forms and the ledger. They read no round. The ledger turns because a sumcheck's hiding
    coefficients are laid under their slots where its claim is made, and a claim that the lookup
    owes is marked as added.
  `addForms`: adds a list of forms to the one equation, in its order.
  `freeSlotOk`: behind all claims: every slot but the merge's has a coefficient in the equation.
    By the table of kinds this test is the page's that writes the one
    equation.
  `claimsFrontFl`, `claimsBackFl`: the same claims, added.
Limits. Definitions alone. A plain function of the library does not look at
the number of rows that a round's entry counts, but where it batches; the strict reading of a round
asks that number of every other round.
-/
import OnBytes.Desc.First.K4.Hear
import OnBytes.Desc.First.K4.Claims
import OnBytes.K.Kc.QuietLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4
open OnBytes
open OnBytes.Model hiding layerObject stackRounds wsForkLin
open OnBytes.Model.Layer hiding shownRun hearNorms hearTerms joinStart hearStack hearGated
  claimsNorms claimRowBatch claimsTerms claimsEnds claimsGated claimsOneHot claimsPlanes
  claimEmbedding freeSlotTest
open OnBytes.K.Kc

/-- The engine of plain functions on the sub-proof's state and the rounds. -/
def engFl : Eng Fl where
  get := Fl.need
  must := Fl.must
  mustAs := fun _ b => Fl.must b
  check := fun _ b => Fl.must b
  fork := Fl.ask some
  change := Fl.change
  shown := Fl.shown
  lin := fun a => Fl.change (·.lin a)
  -- The program's own guard (noBatching, OnBytes/Model/Rounds.lean:108): no point is drawn under
  -- the batching round's name. So no text over this engine closes such a round without its rows.
  point := fun r n => if r == .batSigma then fun _ _ => none else Fl.point r n
  claimsIn := Fl.claimsIn
  batch := Fl.batch
  levelIn := Fl.levelIn
  tscIn := Fl.tscIn
  pscBegin := Fl.pscBegin
  roundIn := fun f p z d => Fl.roundIn f p z d
  pscEnds := Fl.pscEnds
  pscRow := fun p s k => Fl.pscRow p s k
  wsForkEnd := flatForkEnd

/-- HEAR. fo: what the lookup has returned. -/
def hearFl (P : Pub) (hp : HPlan2) (g : Nat) (fo : Forest.Heard) : Fl Own := hear engFl P hp g fo

/-- A sumcheck's own claim, and the ledger with its hiding coefficients laid. No round is read. -/
def ownClaim (p : Psc) (S0 : E) (kept : Aff) (F : Fork) : Option (Aff × Fork) :=
  (Fl.pscRow p S0 kept F []).map fun x => (x.1.1, x.2.1)

/-- CLAIMS, groups 1 to 12; with rows := false groups 2 to 12. o: what `hearFl` has returned. The
ledger turns at three things: the hiding coefficients of the row products' sumcheck and of the
lookup's leaves' sumcheck are laid; the lookup's claims that are listed here are marked as added. -/
def formsFrontWith (rows : Bool) (P : Pub) (g : Nat) (o : Own) (F : Fork) :
    Option (Array Aff × Fork) := do
  let H := o.H
  let sh ← (Array.range (4 * P.y.NI)).mapM fun i => F.shown (H.tV.sEnd + i)
  let (rowV, F) ← ownClaim H.tV.p (rowsSummand P.y H sh) {} F
  let (rowL, F) ← ownClaim H.fo.leaves oneE (← planesParts o.v H.fo).1 F
  let fs ← front rows P g o rowV rowL
  pure (fs.toArray, ((if rows then F.paid H.fo.owedObjects else F).paid H.fo.owedPlanes))

/-- CLAIMS, groups 1 to 12. -/
def formsFront : Pub → Nat → Own → Fork → Option (Array Aff × Fork) := formsFrontWith true

/-- CLAIMS, groups 2 to 12: for a link in which the lookup states its own claims as a run. -/
def formsFrontNoRows : Pub → Nat → Own → Fork → Option (Array Aff × Fork) := formsFrontWith false

/-- CLAIMS, groups 14 and 15. The ledger turns at two things: the merge's hiding coefficients are
laid; the lookup's join, which the first claim decides, is marked as added. -/
def formsBack (o : Own) (F : Fork) : Option (Array Aff × Fork) := do
  let (rowM, F) ← ownClaim o.wo.toWsMerged.p o.wo.toWsMerged.fvp {} F
  pure ((back o rowM).toArray, F.paid o.H.fo.owedJoin)

/-- Adds the forms to the one equation, in their order. -/
def addForms (fs : Array Aff) (F : Fork) : Option Fork := fs.foldlM (fun G a => G.lin a) F

/-- Every slot below used has a coefficient in the one equation, but the merge's slot sFv, which has
none. -/
def freeSlotOk (used sFv : Nat) (F : Fork) : Bool :=
  (List.range used).all fun j => isZeroE (F.LS.getD j zeroE) == (j == sFv)

/-- Groups 1 to 12, added. -/
def claimsFrontFl (P : Pub) (g : Nat) (o : Own) : Fl Unit :=
  Fl.change fun F => (formsFront P g o F).bind fun x => addForms x.1 x.2

/-- Groups 14 and 15, added, and the test behind all claims. -/
def claimsBackFl (hp : HPlan2) (_g : Nat) (o : Own) : Fl Unit :=
  Fl.change fun F => (formsBack o F).bind fun x => (addForms x.1 x.2).bind fun G =>
    if freeSlotOk hp.used o.wo.sFv G then some G else none

end OnBytes.Desc.First.K4
