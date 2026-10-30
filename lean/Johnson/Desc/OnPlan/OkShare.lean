-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/OnPlan/OkShare.lean: the tests on a planner's answer (OkD.plan,
Johnson/Desc/OnPlan/OkPlan.lean) WRITTEN BY SHARE: each kind of block's own, each chain's front's,
the file's; and that the shares together are OkD.plan: no clause is lost, none is new.
Definitions with code, and laws that tie them to the clauses as they stand.

IT STANDS OVER NO FILE THAT IMPORTS Mathlib.

Dealt by one question: does the clause name more than one place? One place's own numbers: that
kind's share. One chain as a whole: its front's. What ties places or chains: the file's.

Main names (namespace VerifiableInference.OnPublicFiles.OkD):
  At.withU S, At.linPoint codes S, At.splitB codes S, At.sending codes sent: A PLACE's SHARE AS A
    FUNCTION OF THE PLACE's NUMBERS (the codes and the shape of the test on the table): what a block
    lays as its test on the plan. At.ofBlock name codes S: the same by the block's name; true at a
    block that has no share.
  n1 … n9: the nine terms of Ok.params (Johnson/Desc/OnPlan/OkParamsDefs.lean), by name.
  Share.k14, Share.k1, Share.k12: the shares of the linear claims' shared part, of a sending, and of
    the proximity test, at p's own numbers as read back.
  Share.front1, Share.front2, Share.front3: the three chains' fronts. Share.file: the file's.
  Share.entries: the shared chain's entries as read back are what the steps want (frontS, sealS):
    where the blocks make their entries of their rounds as data, the format's general test (the
    blocks' rounds in a row are the plan's entries) asks this, whole.
  Share.beside p: all but k14, k1 and front2, as one test: k12, front1, front3, file and entries. Of
    these five none is written under At, as a function of a place's numbers.
  params_eq, k14_eq, k1_eq: each share is its clauses. plan_eq: **the shares together are
    OkD.plan**.

The shape's conditions stand whole in At.linPoint (linFits), though the clauses on the request's own
message belong to the kind of the linear claim's first part. "Every code's message length is a power
of two" (lengthsFit) STANDS BESIDE THEM, IN THE SAME SHARE, OF THE SAME CODES, and not in the
file's: without it "n ≤ the room of a message" does not put a vector's entries at real places of
their rows (Johnson/Desc/Own/RoomPlaces.lean: room_places).

What is not claimed. THAT ANY OF THEM SAYS YES AT ANY p: nothing is evaluated here. That the files
of the kinds deal the clauses in the same way. Nothing on soundness, on an honest prover or on
hiding.

-/
import Johnson.Desc.OnPlan.OkPlan
import Johnson.Desc.Own.LinAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.OkD
open OnBytes

/-! ## A place's share as a function of the place's numbers -/

namespace At

/-- The notices of the sending of the folded row. -/
def withU (S : Params.LinShape) : Array OracleNotice :=
  #[(⟨S.fold.u, S.fold.leafClass⟩ : OracleNotice)] ++ (linWithU S).getD #[]

/-- At the first point: what goes out beside the folded row is said; every code's message length is
a power of two; the shape fits the codes; the two groups' codes are in order. The second and the
third in the description's own text (Johnson/Desc/Own/Lin.lean). -/
def linPoint (codes : Codes) (S : Params.LinShape) : Bool :=
  (linWithU S).isSome && Desc.Own.lengthsFit codes && Desc.Own.linFits codes S &&
    Desc.Ground.groupOk codes S.fold.u.code S.sharedMaskCode &&
    (!S.sharedSplitNeeded || Desc.Ground.groupOk codes S.omega.code S.sharedMaskCode)

/-- At the split: the shared tree needs one, and its message has a free mask entry. -/
def splitB (codes : Codes) (S : Params.LinShape) : Bool :=
  S.sharedSplitNeeded &&
    (!S.sharedSplitNeeded ||
      decide (0 < Send.freeMaskEntries S.sharedSplit.maskRows
        (codes.mask.getD S.sharedSplit.maskCode default).ell S.sharedSplit.answers))

/-- At a sending: every notice's shape fits the codes; the trees can be laid; every notice that has
answers has room for its pad. -/
def sending (codes : Codes) (sent : Array OracleNotice) : Bool :=
  Desc.Ground.ok (Desc.Ground.sentL codes sent) && padsOk codes sent

/-- A block's share, by its name in the shared chain's table of places. -/
def ofBlock (name : String) (codes : Codes) (S : Params.LinShape) : Bool :=
  if name == "LIN point" then linPoint codes S
  else if name == "send o_u" then sending codes (withU S)
  else if name == "send o_omega" then sending codes (linMessageOmega S)
  else if name == "SPLIT" then splitB codes S
  else true

end At

/-! ## The nine terms of Ok.params, by name -/

def n1 (p : Model.Verify.Planned) : Bool := (proofFirst p).given.plan.samples == 1
def n2 (p : Model.Verify.Planned) : Bool := (proofFirst p).shape.choice.masksRide
def n3 (p : Model.Verify.Planned) : Bool := (proofTail p).shared.given.plan.samples == 1
def n4 (p : Model.Verify.Planned) : Bool := (proofTail p).second.given.plan.samples == 1
def n5 (p : Model.Verify.Planned) : Bool := (proofTail p).lin.choice.masksRide
def n6 (p : Model.Verify.Planned) : Bool := !(proofTail p).lin.ownSplitNeeded
def n7 (p : Model.Verify.Planned) : Bool := (linWithU (proofTail p).lin).isSome
def n8 (p : Model.Verify.Planned) : Bool := !(proofTail p).lin.testOwn.isEmpty
def n9 (p : Model.Verify.Planned) : Bool := !(proofFirst p).shape.link.isEmpty

/-- Ok.params is its nine terms. -/
theorem params_eq (p : Model.Verify.Planned) :
    Ok.params p = (n1 p && n2 p && n3 p && n4 p && n5 p && n6 p && n7 p && n8 p && n9 p) := rfl

/-! ## The shares at p -/

namespace Share

/-- The linear claims' shared part. -/
def k14 (p : Model.Verify.Planned) : Bool :=
  At.linPoint (codesS p) (linS p) && At.splitB (codesS p) (linS p)

/-- A sending, at its two places in the shared chain. -/
def k1 (p : Model.Verify.Planned) : Bool :=
  At.sending (codesS p) (At.withU (linS p)) && At.sending (codesS p) (linMessageOmega (linS p))

/-- The proximity test, at its three places in the shared and the second chain. -/
def k12 (p : Model.Verify.Planned) : Bool := stagesU p && stagesO p && stagesW p && n8 p

/-- The first chain as a whole. -/
def front1 (p : Model.Verify.Planned) : Bool := n1 p && n2 p && n9 p && remadeF p

/-- The shared chain as a whole. -/
def front2 (p : Model.Verify.Planned) : Bool :=
  n3 p && sizedS p && readShape p && readCodes p && readSamples p && remadeS p

/-- The second chain as a whole. -/
def front3 (p : Model.Verify.Planned) : Bool := n4 p && remadeW p

/-- What ties places or chains. -/
def file (p : Model.Verify.Planned) : Bool :=
  n5 p && n6 p && ahead p && firstU p && firstO p && firstW p && heldS p &&
    readPlans p && settingZ p && madeSets p

/-- The shared chain's entries as read back are what the steps want. -/
def entries (p : Model.Verify.Planned) : Bool := frontS p && sealS p

/-- All but k14, k1 and front2. -/
def beside (p : Model.Verify.Planned) : Bool :=
  k12 p && front1 p && front3 p && file p && entries p

end Share

/-- The share of the linear claims' shared part is these seven clauses. -/
theorem k14_eq (p : Model.Verify.Planned) :
    Share.k14 p =
      ((n7 p && lengths p && shape p && groupU p && groupO p) && (split p && free p)) := rfl

/-- The share of a sending, at its two places, is these four clauses. -/
theorem k1_eq (p : Model.Verify.Planned) :
    Share.k1 p = ((sendU p && padsU p) && (sendO p && padsO p)) := rfl

/-- **The shares together are OkD.plan.** -/
theorem plan_eq (p : Model.Verify.Planned) :
    plan p = (Share.k14 p && Share.k1 p && Share.front2 p && Share.beside p) := by
  rw [k14_eq, k1_eq]
  unfold plan desc sched read lists Share.front2 Share.beside Share.k12 Share.front1 Share.front3
    Share.file Share.entries
  rw [params_eq]
  ac_rfl

end VerifiableInference.OnPublicFiles.OkD
