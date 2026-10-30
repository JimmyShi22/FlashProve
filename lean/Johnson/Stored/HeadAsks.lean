-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Stored/HeadAsks.lean.
WHAT IT IS. FURTHER TESTS WITH CODE FOR THE OUTPUT HEAD's PLACE, WHICH NO BLOCK ASKS TODAY. Each can
only refuse more.
WHAT IT DOES NOT SHOW. Definitions alone. NOBODY CALLS THEM: they are premises of the laws
(Desc/Kinds/Law/SeatedSays.lean), not facts behind a yes. That they say yes at a real plan: no run
is
in this file.
  moreTestsAt, moreTests, moreFails, moreOk   five ON PUBLIC NUMBERS, each under its name: the
                    program's own test on the head's numbers; its layout's numbers are made; each of
                    the nine keys has fewer than 2^41 entries; the setting's bits of work in front
                    of a challenge and 66 more are at most 128; the setting has one instance. A door
                    for tests on the public files can take these.
  arrayOk           ON THE CARRIED RECORD: it stands in the head's link with a ledger, and the
  reads'
                    array is there with a column. No door for tests on public files can take it: the
                    seat's two readers (reads, planesAt) ask the same themselves.

-/
import Johnson.Stored.HeadSeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head

open OnBytes
open VerifiableInference.Desc.First (S)

/-- Five tests on public numbers, each under its name. -/
def moreTestsAt (h : Model.Head.Shape) (work instances : Nat) : List (String × Bool) :=
  let _ := (parOf h 0).sizes
  [("admitted", Model.Head.admitted h),
   ("numbers", (Model.Head.numbers h).toOption.isSome),
   ("keys", ([.inl .remLow, .inl .remHigh, .inl .clamp, .inl .digits, .inr .marginTop,
      .inr .marginMid, .inr .marginLow, .inr .tableA, .inr .tableB] : List PlaceKey).all fun k =>
        Nat.blt (lenOf k) (2 ^ 41)),
   ("work", Nat.ble (work + 66) 128),
   ("once", instances == 1)]

/-- The same at the public record. -/
def moreTests (W : Model.Verify.Public) : List (String × Bool) :=
  moreTestsAt W.hS ((Params.settingOf W.P.frame).workOf .field .request)
    (Params.settingOf W.P.frame).instances

def moreOk (W : Model.Verify.Public) : Bool := (moreTests W).all (·.2)

/-- The names of the tests that say no. -/
def moreFails (W : Model.Verify.Public) : List String := ((moreTests W).filter (!·.2)).map (·.1)

/-- The record stands in the head's link with a ledger, and the reads' array is there with a column.
-/
def arrayOk (iU3 : Nat) (s : S) : Bool :=
  match s.here, s.fork? with
  | .head _, some F => (F.trees[iU3]?).any fun tr => tr.K != 0
  | _, _ => false

end VerifiableInference.Desc.Kinds.Head
