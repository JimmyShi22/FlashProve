-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/ClaimsReq.lean: the letter A of the description made of the three files' protocols, as
a written term at the reference sizes, where the instances are the requests that the program's
reader takes.

Two definitions.
  claimsLedgerOn D N s req : D.Claims X, for a map req from the instances X to the model's requests:
    claimsLedger (Johnson/Flat/ClaimsLedger.lean) with the claim read at req x.
  claimsReq D N s : D.Claims Req: the A at the requests that the reader takes: X := Req (r < e;
    y = 0 if e is before the window's end: Johnson/Flat/LedgerClaim.lean), req := Subtype.val.
Why Req. r < e, and y = 0 if e is before the window's end, are clauses of the relaxed relation. The
program refuses every other request before it reads the proof file (requestRun,
OnBytes/Model/VerifyStages.lean: Head.stFromCall stands before Proof.check). A hypothesis on the
proof file's protocol speaks of every instance: cut to Req it speaks of those alone of which the
program's verifier can be asked. At all instances (claimsLedger) that hypothesis would ask the proof
file's protocol to refuse what the reader refuses before it.

Limits: nothing on a protocol. The reference sizes and exact match alone. The numbers N of the
matrix and the table of scales s are letters: no value is given here (numsRef:
Johnson/Flat/ThreeFull.lean), and nothing ties s to the scale file of a description. That the key
file's item "ranges" is the planner's at the shipped layout is a public premise that no file writes
(Johnson/Flat/LedgerClaim.lean, "what enforces which clause").

-/
import Johnson.Flat.ClaimsLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Flat

open OnBytes.Slice Inst.Model VerifiableInference

variable (D : DecR) (N : MatrixNums)

/-- What the statements read of a decoded table, at a table of scales s; req: the request that an
instance says. -/
def claimsLedgerOn {X : Type} (s : Cm.Scales) (req : X → Instance ppref) : D.Claims X where
  Mat := Cells D N
  mat := cellsOf D N
  inRange := OnPublicFiles.Flat.InRange
  Rel := fun M x => OnPublicFiles.Flat.RelL s M (req x)
  mat_cut := cellsOf_cut D N

/-- **The A at the requests that the program's reader takes.** -/
def claimsReq (s : Cm.Scales) : D.Claims OnPublicFiles.Flat.Req := claimsLedgerOn D N s Subtype.val

end OnBytes.Flat
