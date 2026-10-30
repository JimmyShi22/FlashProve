-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/LibParts.lean: FROM THE HEAD's RELATION ON CELLS IN FOUR PARTS, AS THE TABLE OF JOINTS CUTS IT (HeadTablesLaw.lean: HeadParts: idn · lookCalls · rider · small), TO Policy.HeadCl (every key of the nine families is an entry of its table · the 17 identities · the ledger's two lines · its two sums), OVER THE BASE FIELD, AT THE LIBRARY's RECORD MADE OF OUR CELLS (cellsN c): STATED
AND PROVED, IN THREE LINES: Law/OutCall.lean's backCall (from the six calls' tables back to the nine keys) and Law/LibWhole.lean's headCl_of_two (which is joinWhole, ported whole from a text of ours, not in this repository, and the lemma Hd.Down.ledgerRF_gl, Johnson/Road/HeadDown.lean). SO THE TABLE's FOUR ITEMS "constr" AT THE HEAD's SEGMENT, IN K6's FILES' WORDS, GIVE FOUR OF THE FIVE CLAUSES FROM WHICH THE GOALS' "Means" FOLLOWS AT THE HEAD, IN THE LIBRARY's.
  headCl_of_parts
WHAT IT DOES NOT SAY. All that Law/LibWhole.lean does not say: its premises stand here to the letter (the tests on the plan and the request · y < V · Same · Wide: NO PADDING · More · tab is the library's EX on 16 bits · c.Wh is the output matrix). That a verifier's yes gives HeadParts: idn is what K6's law closes; lookCalls and rider are closed by the lookup's block; small by the smallness
test. SmallH (every entry of the matrices, the fillers too: our small bounds the cells alone) and "y = 0 if e < T" are no clauses of HeadCl. That cellsN c is what the committed integers spell. FULL SIZE ALONE. One way alone. No chance in it.

-/
import Mathlib
import Johnson.Desc.Kinds.Law.TableTie
import Johnson.Desc.Kinds.Law.LibWhole

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

open Inst.Model (AcceptancePolicy Mat Instance ppref)
open VerifiableInference.Desc.Kinds.HeadJoin (Same Wide More cellsN)

/-- **THE FOUR PARTS GIVE HeadCl.** -/
theorem headCl_of_parts [Sizes] [Policy] [Request] [Token] (sT floor : Nat) (tab : Nat → Nat)
    (c : NCells) (pol : AcceptancePolicy) (Wz : Mat) (x : Instance ppref) (hplan : planOk sT = true)
    (hreq : Request.ok = true) (hy : Token.y < V) (S : Same (Inst.Model.Head.Req.of pol x))
    (Wd : Wide) (M : More (Inst.Model.Head.Req.of pol x))
    (htab : ∀ u, u < 2 ^ 16 → (tab u : Int) = Inst.Model.EX u)
    (hW : c.Wh = (Inst.Model.Layout.weightsOf ppref Inst.Model.Layout.kRef Wz).H)
    (P : HeadParts floor tab c) : _root_.Policy.HeadCl npOf pol Wz x (cellsN c) := by
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := backCall sT floor tab c hplan P.lookCalls
  exact headCl_of_two sT tab c pol Wz x hplan hreq hy S Wd M htab hW
    ⟨k1, k2, k3, k4, k5, P.rider, P.idnSums⟩ ⟨P.small, P.smallS, P.idnRows, k6, k7, k8, k9⟩

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.headCl_of_parts
