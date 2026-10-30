-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6ReadsNameAtConst.lean: AT THE CLOSED TERM dAt h (Law/DAtConst.lean) FOR THE
COMPOSED MEANING'S PARAMETERS, THE FIRST ENTRY OF SEGMENT 24'S LIST OF ARRAYS IS THE READS' ARRAY,
BY ITS NAME: ((dAt h).sent.arrayOf.getD 24 #[])[0]? = some (24, "U3"). GENERAL IN THE LETTER o FOR
THE SECOND HASH FUNCTION. It is the one premise that another file's payer of the test on the seats
(Johnson/HB/LLHARD/K6SeatsAtHead.lean: hA) leaves by name.

Main name (namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable).
  reads_name_at_const.

How. The first steps of Law/K6BuiltAtConst.lean's room_at_const, up to the fact that it rewrites by:
built_plain; the scope's two numbers (scope_plans, Johnson/Goal/Meaning/PlanShapes.lean); the shape
of the list of segments (listLinksH_with); public_third (ReadsNamed.lean) and reads_named_of_built
(ReadsRoomOfBuilt.lean). A new file beside: no byte of K6BuiltAtConst turns.
What it does not say. That the head can be met. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.K6BuiltAtConst

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.AtTable

open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH LinksH listLinksH buildLinksH)
open VerifiableInference.Desc.First.FillSent (treesAt looksOf)
open P5J (At.X At.layout)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {Dw : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

variable {x : First.Look.Place}

/-- **The name of the reads' array, at the closed term.** -/
theorem reads_name_at_const (h : P5J.AtMgA o Z Dw r Zp Np cF x) :
    ((dAt h).sent.arrayOf.getD 24 #[])[0]? = some (24, "U3") := by
  obtain ⟨l₀, hl, hb⟩ := built_plain h.toAtMg
  obtain ⟨p4, ng, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  unfold ProofFile.Plain.linksPlain at hl
  rw [p4] at hl
  obtain ⟨_, _, z, _, e⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ hl
  have T : (At.X Zp).H.tl.ix.U.getD 2 none = some 0 := ReadsNamed.public_third h.pubOne
  obtain ⟨c1, -⟩ := Built.reads_named_of_built hb z e (t := 0) T
  rw [ng] at c1
  exact c1

end VerifiableInference.Desc.Kinds.Head.Law.AtTable

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtTable.reads_name_at_const
