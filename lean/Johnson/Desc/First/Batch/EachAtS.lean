-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Batch/EachAtS.lean (kind K9's place): A DEFINITION WITH CODE; NO THEOREM: the
test after each list of a segment's claims (Johnson/Desc/First/Batch/Each.lean) at the state that
the proof file's first chain carries: what stands in Link.each.
  the windows: the smallness test's window of slots, off its record; its owners are the second
    stretch of the driver's table of the order (Johnson/Desc/First/Batch/ObjectsAtS.lean: k8Window);
  the one due number: the FIRST list of that stretch (the lookup on the digits' "objects") has as
    many claims as that lookup has equations of its own (First.TailClaims.lookRows; Tail.lean:1053
    of the program `verify-on-bytes`): "K9.lookup-rows-counted". It is asked of the list itself.
WHAT IT DOES NOT ASK. No other list's number of claims: dueAtS gives none for it. Link.each holds
the window's owners and this ONE number. The number of claims of each list is the chain's to refuse,
not the link's tests': the total is held at the one equation ("K9.claims-all-added",
"K9.rows-counted"), and which list stands under which name by the chain's arithmetic alone, at the
base case.

-/
import Johnson.Desc.First.Batch.Each
import Johnson.Desc.First.Batch.ObjectsAtS

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K9
open OnBytes OnBytes.Model
open VerifiableInference.Desc.First (S)

/-- The number of claims that is due of a run, at a sort of segment. -/
def dueAtS (k : SegSort) (run : Nat × String) (s : S) : Option (String × Nat) :=
  if (cutAt k 1).head? == some run then
    s.tl?.map fun tl => ("K9.lookup-rows-counted", First.TailClaims.lookRows tl)
  else none

/-- **Link.each at a segment of sort k.** -/
def eachAtS (k : SegSort) : Nat × String → List Claim → S → Except String Unit :=
  eachRun (k8Window k) (dueAtS k)

end VerifiableInference.Desc.K9
