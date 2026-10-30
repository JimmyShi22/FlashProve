-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/Guest.lean: what K5 hands the lookup's kind (K3) at an attention segment, as the
caller of its two runs "join" and "planes".

The two formulas are the lookup's own. The caller hands in the calls' key forms (Att/RunsK.lean:
keysOfK) and, for "planes", two readers: for a bit and a column the form that reads that bit's
plane's table at that column, and the like for the pin (after OnBytes/Model/Attention.lean:205-207).
Main names: `readersOfK` (both readers at once: the tables are made once), `bitsOfK`, `pinOfK`; at the
first chain's state: `readersOfPS`, `bitsOfPS`, `pinOfPS`.
Each may refuse: outside an attention segment; where the tables refuse; where a column lies beyond
its table.

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.SeatC

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes
open OnBytes.Model (Aff)

variable {S : Type}

/-- For "planes": both readers; the tables are made once. -/
def readersOfK (seat : SeatC S) (c : ParC) (s : S) : Option ((Nat → Nat → Option Aff) × (Nat → Option Aff)) :=
  (inOf seat c s).map fun x =>
    let at_ (place col : Nat) : Option Aff := (Runs.gather x.2 (Runs.u3at x.1 place col)).map (·.1)
    (fun e col => at_ (if e == 0 then x.1.t.tBit0 else x.1.t.tBit1) col, fun col => at_ x.1.t.tPin col)

/-- For "planes": the bit's plane, one form. -/
def bitsOfK (seat : SeatC S) (c : ParC) (s : S) (e col : Nat) : Option Aff :=
  (readersOfK seat c s).bind fun r => r.1 e col

/-- For "planes": the pin, one form. -/
def pinOfK (seat : SeatC S) (c : ParC) (s : S) (col : Nat) : Option Aff :=
  (readersOfK seat c s).bind fun r => r.2 col

/-- At the first chain's state. -/
def readersOfPS (A : Attention.Plan) (s : First.S) : Option ((Nat → Nat → Option Aff) × (Nat → Option Aff)) :=
  readersOfK (seatCS (parCOf A)) (parCOf A) s
def bitsOfPS (A : Attention.Plan) (s : First.S) (e col : Nat) : Option Aff := bitsOfK (seatCS (parCOf A)) (parCOf A) s e col
def pinOfPS (A : Attention.Plan) (s : First.S) (col : Nat) : Option Aff := pinOfK (seatCS (parCOf A)) (parCOf A) s col

end VerifiableInference.Desc.First.Att.P
