-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/PlaceNums.lean: the code switch: two numbers of each of the 25 places of the
kind in a proof's first chain, at the full size, AS CLOSED TERMS: how many oracle messages stand in
front of the switch into group l (`n0At l`), and the numbers of the old messages that it keeps
(`oldsAt l`). Definitions with code, their values by Lean's kernel, and two negative tests.

Whence. The verifier numbers the oracle messages in the order in which they are announced. What link
k announces at its moment m is `P1K2.noticesAt` (Johnson/Desc/ProofFile/Lot/K2OfPlan.lean), a
function of the request's shape. Here it is taken at the written value of the sizes of a proof's
chains (`proofSizedFull`, Johnson/Desc/Ok/PlanWritten/SizedLit.lean). The kept members' places in
their link are the written ones (`tableFullLit`, Johnson/Top/H0/K2Caller/LitRows.lean).
`tableFullLit` counts among the sampled messages; the fresh mask, the one message without an OOD
sample, stands behind every kept place, so both countings agree here.

  `toldByLink k`   the messages that link k announces, at all its moments
  `n0At l`         those of the links 0 … l - 1
  `oldsAt l`       the kept members of the switch into group l: their places in link l - 1, counted
                   from the first message of that link
  `n0_values`, `olds_values`: the 26 and the 25 values, written out
  `olds_nodup`, `olds_below`: no number twice; each below `n0At l`
  `n0_can_fail`, `olds_can_fail`: negative tests: with one written number turned the equations are
                   false
Limits. THAT `n0At l` IS THE NUMBER OF MESSAGES IN THE VERIFIER's STATEMENT IN FRONT OF THE PLACE IS
NOT SHOWN: neither that the sub-protocols in front tell just what the links announce, nor that the
sizes at a run are the written value. `oldsAt` is a forecast of the law's owner, borne out by it at
the five switches of the small proof. The full size alone. No soundness is claimed.

-/
import Johnson.Desc.ProofFile.Lot.K2OfPlan
import Johnson.Desc.Ok.PlanWritten.SizedLit
import Johnson.Top.H0.K2Caller.LitRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes
open VerifiableInference.PlanWritten (proofSizedFull)
open VerifiableInference.Desc.First.K2Caller (tableFullLit)

/-- The frame of the request at the written sizes. -/
def frameFull : ReqFrame :=
  { shape := proofSizedFull.request, groups := reqGroups proofSizedFull.request }

/-- The messages that link k announces, at all its moments. -/
def toldByLink (k : Nat) : Nat :=
  ((List.range (OnBytes.reqMoments (proofSizedFull.request.link.getD k default))).map fun m =>
    (P1K2.noticesAt frameFull k m).size).sum

/-- **The messages in front of the switch into group l.** -/
def n0At (l : Nat) : Nat := ((List.range l).map toldByLink).sum

/-- **The numbers of the old messages that the switch into group l keeps.** -/
def oldsAt (l : Nat) : List Nat :=
  (((tableFullLit[l - 1]?).map (·.kept)).getD []).map (· + n0At (l - 1))

set_option maxRecDepth 1000000 in
theorem n0_values : (List.range 26).map n0At =
    [0, 7, 14, 22, 29, 37, 44, 52, 59, 67, 74, 82, 89, 97, 104, 112, 119, 127, 134, 142, 149,
      157, 164, 172, 179, 185] := by decide +kernel

set_option maxRecDepth 1000000 in
theorem olds_values : (List.range' 1 25).map oldsAt =
    [[1, 2], [9], [17, 18], [24], [32, 33], [39], [47, 48], [54], [62, 63], [69], [77, 78], [84],
      [92, 93], [99], [107, 108], [114], [122, 123], [129], [137, 138], [144], [152, 153], [159],
      [167, 168], [174], []] := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem olds_nodup : ((List.range' 1 25).all fun l => decide (oldsAt l).Nodup) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem olds_below :
    ((List.range' 1 25).all fun l => (oldsAt l).all fun x => decide (x < n0At l)) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the fourth value is not 23. -/
theorem n0_can_fail : n0At 3 ≠ 23 := by decide +kernel

set_option maxRecDepth 1000000 in
/-- A negative test: the second switch does not keep message 8. -/
theorem olds_can_fail : oldsAt 2 ≠ [8] := by decide +kernel

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.n0_values
#print axioms VerifiableInference.Desc.First.K2.olds_values
#print axioms VerifiableInference.Desc.First.K2.olds_nodup
#print axioms VerifiableInference.Desc.First.K2.olds_below
#print axioms VerifiableInference.Desc.First.K2.n0_can_fail
#print axioms VerifiableInference.Desc.First.K2.olds_can_fail
