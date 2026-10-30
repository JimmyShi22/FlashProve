-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
One file of the set on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/Desc/Key/KeyPubIn.lean: FOUR PUBLIC FACTS ON A LOOKUP OF THE PLAN, AS ONE BOOL (definitions alone; no import but the program's own Wf): what the bridge from KeysIn (Johnson/Desc/First/Look/KeyLaw/Closed.lean) to the table's InRange asks (KeyCoinIn.lean, not in this library: inRange_of_keysIn_B: the Bool's yes gives the four premises):
a row's number fits a machine word (d ≤ 64) · a run's places lie inside its part · no place is covered by two runs of one part · every row that a run reads, for every digit, is one of the matrix's. A FILE OF ITS OWN so that a file of evaluations, in a build without the bridges' imports, can evaluate THE VERY Bool.
-/
import OnBytes.Iop.Wf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key
open OnBytes
open OnBytes.Params (WfRun WfPart WfLookup)

/-- Two runs are one run, or cover no place in common. -/
def apartB (r r' : WfRun) : Bool := r == r' || decide (r.firstPlace + r.places ≤ r'.firstPlace) || decide (r'.firstPlace + r'.places ≤ r.firstPlace)

def pubInB (m : Wf.Matrix) (l : WfLookup) : Bool :=
  decide (l.d ≤ 64) && l.parts.all fun p =>
    (p.runs.all fun r => decide (r.firstPlace + r.places ≤ 2 ^ p.logPlaces)) &&
    (p.runs.all fun r => p.runs.all fun r' => apartB r r') &&
    (p.runs.all fun r => l.digitWeight.zipIdx.all fun w => decide (r.firstRow + w.2 * r.stride + r.places ≤ m.rows))

/-- KeyTies.MaskWith as a Bool: message r lies in message o's tree, the next part. (The tie: KeyFenceOrder.maskWith_of_B.) -/
def maskWithB (place : Nat → Option (Nat × Nat)) (o r : Nat) : Bool :=
  match place o, place r with
  | some a, some b => a.1 == b.1 && b.2 == a.2 + 1
  | _, _ => false

end VerifiableInference.Desc.Key
