-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/LibWhole.lean: FROM K6's FILES' TWO RELATIONS ON CELLS (HeadLaw.lean: CellRelH; HeadNormLaw.lean: CellRelN) TO Policy.HeadCl (Policy/Seg/Head.lean: every key of the nine families is an entry of its table · the 17 identities · the ledger's two lines at every position · its two sums), OVER THE BASE FIELD, AT THE LIBRARY's RECORD MADE OF OUR CELLS (cellsN c); SO ALSO
HeadKeys' SENTENCE (Johnson/Road/Lane5SplitH.lean), the fifth of the five clauses on the head from which the goals' "Means" follows: STATED AND PROVED, IN FOUR LINES: Law/LibJoinNorm.lean's joinWhole (ported whole from a text of ours, not in this repository) and Hd.Down.ledgerRF_gl (Johnson/Road/HeadDown.lean: the relation over our field is the relation modulo the prime). That
source's own ToHeadF.lean goes the same way to its own record HeadF: that file is not ported (it leans on other files of that source).
  headCl_of_two
WHAT IT DOES NOT SAY. That a verifier's yes gives the two relations: small is the smallness test's; the keys and the two lines are the lookup's row's and rider's conclusions; the rows and the sums are what K6's law closes: NOT ASSEMBLED HERE. PREMISES, PAID BY NOBODY HERE: the tests on the plan and the request · the next token is a token · Same (Law/LibAtSeat.lean pays it at the seat) · Wide
(NO PADDING: V = JV = 202048) · More (sh = 8 · the tables' keys are cut at 131072 · the library's checked tokens are ours) · our table is the library's EX on 16 bits · c.Wh is the output matrix that the library reads in Wz. SmallH and "y = 0 if e < T" are no clauses of HeadCl. That cellsN c is what the committed integers spell. FULL SIZE ALONE. One way alone. No chance in it.

-/
import Mathlib
import Johnson.Road.HeadDown
import Policy.Seg.Head
import Johnson.Desc.Kinds.Law.LibJoinNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open Inst.Model (AcceptancePolicy Mat Instance ppref)
open VerifiableInference.Desc.Kinds.HeadJoin (Same Wide More cellsN joinWhole)

/-- **OUR TWO RELATIONS GIVE HeadCl.** -/
theorem headCl_of_two [Sizes] [Policy] [Request] [Token] (sT : Nat) (tab : Nat → Nat) (c : NCells)
    (pol : AcceptancePolicy) (Wz : Mat) (x : Instance ppref) (hplan : planOk sT = true)
    (hreq : Request.ok = true) (hy : Token.y < V) (S : Same (Inst.Model.Head.Req.of pol x))
    (Wd : Wide) (M : More (Inst.Model.Head.Req.of pol x))
    (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u)
    (hW : c.Wh = (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef Wz).H)
    (hH : CellRelH c.toCells tab) (hN : CellRelN c) :
    _root_.Policy.HeadCl npOf pol Wz x (cellsN c) := by
  have R := joinWhole sT tab c (Inst.Model.Head.Req.of pol x) hplan hreq hy S Wd M htab hH hN
  have R2 := (OnBytes.Road.Hd.Down.ledgerRF_gl (Hz := c.Wh)).1 R
  rw [hW] at R2
  exact ⟨R2.keys, R2.idns, R2.jc, R2.sums⟩

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.headCl_of_two
