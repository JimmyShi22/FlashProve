-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3AsksHead.lean: THE LOOKUPS' TEST ON PUBLIC DATA AT THE HEAD's LINK's
CALLS, WRITTEN OUT ONCE MORE OVER LIGHT IMPORTS: what the law on the lookup on the head's calls
takes as its premise on the public record, as a function to Bool that a verifier can run.
Definitions alone; no theorem; WITHOUT MATHLIB. NO SOUNDNESS IS CLAIMED. Nothing is evaluated in
this file.

OBJECT: no block's text: a function of the public record X.
USER: headEntry (Johnson/Desc/First/Look/K3AsksDoor.lean), the proof file's entry test 13
(LPFD.lawsAsk, Johnson/Desc/Laid/ProofAsks.lean).
LETTERS: X : Verify.Public.
Compiled with the whole library.


Main names:
  `floorAt h`: the least allowed logarithm of the number of keys of a call of the head.
  `headB h floor fs`: six calls; a position's bits lie in the first part of the key point; each
    call has room for its columns' bits and the positions'. The output head's kind's sizes are read
    off the head's shape h.
  `headAt X`: the place of the lookup on the head's link's calls, with the record that the kind's
    own parameters make.
  `headRow X`: THE HEAD's ROW: the place is there and the test says yes at the floor floorAt X.hS.

What it calls of the output head's kind's own text (Johnson/Desc/Kinds/HeadIn.lean, without
Mathlib): the list of the six calls' keys (callList) and the logarithm of a call's number of columns
(lJ). That a yes gives the law's premise: Johnson/Desc/First/Look/K3AsksHeadLaw.lean.

Limits. The floor is a choice of this file.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3Asks
import Johnson.Desc.Kinds.HeadIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3Asks
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First.Look (Place P lookAt)

/-- The least allowed logarithm of the number of keys of a call of the head. -/
def floorAt (h : Head.Shape) : Nat := if h.NMINH != 0 then h.NMINH else h.nmin

/-- **THE TEST ON THE RECORD OF THE LOOKUP ON THE HEAD's CALLS.** -/
def headB (h : Head.Shape) (floor : Nat) (fs : Forest.Shape) : Bool :=
  fs.NC == 6 && decide (h.lt ≤ fs.dT) &&
    (List.range 6).all fun c =>
      decide (@Kinds.Head.lJ
        { lt := h.lt, ls := h.la - h.lt, d := h.d, MF := h.MF, KF := h.KF, epsF := h.epsF, V := h.V,
          sh := h.digSh, F := h.famF }
        floor (Kinds.Head.callList.getD c []) + h.lt ≤ nOf fs c)

/-- The place of the lookup on the head's link's calls, with the record that the kind's own
parameters make in the place of the plan's. -/
def headAt (X : Verify.Public) : Option Place :=
  (lookAt X ((if X.p4 then 2 else 1) * X.NGr) false).bind fun x =>
    (P.ofPlace (Params.settingOf X.P.frame) false x).shape.map fun h => { x with fs := h }

/-- **THE HEAD's ROW.** -/
def headRow (X : Verify.Public) : Bool :=
  (headAt X).any fun x => headB X.hS (floorAt X.hS) x.fs

end VerifiableInference.Desc.K3Asks
