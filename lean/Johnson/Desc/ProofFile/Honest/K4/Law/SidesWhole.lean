-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/SidesWhole.lean: CONDITIONAL. A statement with its proof.

What is here: `Sides.of` RETURNS (Johnson/Desc/K4/Honest/Sides.lean: all that the second token
sumcheck's job and the batched sumcheck's job of the feed-forward layers' own rounds, the
sub-protocol K4, share), at every input w and all sampled values p, FROM PREMISES ON PUBLIC DATA AND
ON TWO SIZES OF WHAT THE LOOKUP HAS SAMPLED: none of its eight returns is left as a hypothesis.
How. `sides_return` (Law/SidesReturn.lean) with its last hypothesis paid by `termsForms_returns`
(Johnson/Road/K4/C/TermsFormsOf.lean).

Not shown here. THE PREMISES: the public facts `K4Plan` and profile 4; the plan names the reads'
array (hU); the list of tables is laid (hl); that array has a column (hK); the row of the first free
entry behind the tables fits 32 bits (hb); THE TEST WITH CODE `claimsB`
(Johnson/Desc/First/K4/Returns/Pub/ClaimsB.lean); the weights' layout is what the verifier's
`wsLayOf` returns (hws); what the heads' weights read at the blank structure (hq: `qkRd_of`,
Johnson/Road/K4/C/ClaimRdOf.lean, has it from the verifier's lines; not called here). ON p: the
calls' points have the plan's sizes (hz); the lookup's point has la coordinates (hla). No example of
all premises together is known. A RETURN ALONE. Nothing on soundness, on completeness or on any
other property. No property is claimed.

  `sides_whole`   **`Sides.of` returns**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SidesReturn
import Johnson.Road.K4.C.TermsFormsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes.Model (WsShape HTailF2 wsLayOf)
open OnBytes.Model.Layer (TableAsk TableAt layTables tableAsks)
open OnBytes.Road.K4.W (K4Plan)
open OnBytes.Road.K4.C (QkRd termsForms_returns)
open OnBytes.Desc.First.K4.RtPub (claimsB zkFits blankClaims)
open OnBytes.Desc.First.K4.Honest
open Inst.Model.FFSeg (Dim)

variable {Q : K4Pub} {w : K4In} {p : Pts} {iU3 : ℕ}
  {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
  {hS : OnBytes.Model.Layer.Shape} {pc : List (List String)} {tl : HTailF2} {D : Dim}

/-- CONDITIONAL on every hypothesis named. **`Sides.of` RETURNS.** -/
theorem sides_whole (A : K4Plan hS pc Q.P Q.g tl D) (hp4 : hS.p4 = true)
    (hU : Q.hp.tl.ix.U.getD 2 none = some iU3)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    (hK : ((Q.hp.Fp.trees[iU3]?).map (·.K)).getD 0 ≠ 0)
    (hb : r.2.2 / ((Q.hp.Fp.trees[iU3]?).map (·.K)).getD 0 < 2 ^ 32)
    (hB : claimsB Q.P Q.hp Q.g = true) (hz : zkFits Q.P p.fo.zk = true)
    (hla : Q.P.y.h.la ≤ p.fo.zx.size) {sw s : WsShape} {lk : ℕ}
    (hws : wsLayOf sw true lk = .ok Q.P.wsLay) (hq : QkRd (blankClaims Q.P Q.hp Q.g) s) :
    ∃ S, Sides.of Q w p = some S :=
  sides_return A hU hl hB hz hla hws hq (termsForms_returns A hp4 hl hK hb p.fo.zk _ rfl)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.sides_whole
