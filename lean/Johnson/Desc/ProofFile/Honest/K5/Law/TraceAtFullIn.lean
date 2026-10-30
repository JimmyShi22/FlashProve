-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/TraceAtFullIn.lean: hV0 IS PAID BY NOBODY: AT THE FRAME's
FILLING's LETTER `fullIn` (Johnson/Desc/ProofFile/Honest/AtPureFullIn.lean) THE NAMED PREMISE ON THE
TRACE, `TraceIsFull` (TraceFull.lean in this folder), FOLLOWS FROM ONE PREMISE: a valid input's
trace is what `fullIn.trace` answers at the input's own index and instance. AN EXCHANGE OF ONE
PREMISE FOR A FINER ONE, AT ONE FILLING: hV0 ties the input's index, instance and trace; the end
forgets the tie again. IT PAYS NOTHING BY ITSELF. IT MAY HOLD EMPTILY. CONDITIONAL: under the
hypothesis h, the library's head on the public input (`P5J.AtMgA`, Johnson/P5J/MgAtAll.lean). No
definition; one theorem.

Main names:
  `traceIsFull_at_fullIn`: from hV0 : ∀ v, Vd v → fullIn.trace Zp v.w₀ v.x = some v.trace.

How. `fullIn_trace_some` (AtPureFullIn.lean) hands an instance that the request's bytes are read as,
the serving at the input's own index, and the trace as the reader by labels of the library's
full-size trace; then `traceIsFull_of_cellOf` (TraceFull.lean).

Limits. hV0 reads the input's index, instance and trace; not its fourth field. The index's type is
set: `Cm.Idx`. At a Vd that holds of no input hV0 asks nothing; nothing here says that any input
meets it; `fullIn_trace_served` (AtPureFullIn.lean) has that the trace is there at every instance
that is read off the request and that the index serves. `TraceHinge` is not called here. All limits
of AtPureFullIn.lean hold: `fullIn` is noncomputable, at the full size alone, and no program can run
a filling that is made from it. NOTHING AT A PLANE's NUMBER. AtPureFullIn.lean lies in no seal, nor
do some of the files beneath it: among these AtPureFullLaw.lean and AtPureFull.lean of the same
folder and Johnson/Desc/ProofFile/InstOf.lean. Through its imports it stands above
Cb/Bridge/CodeListRSProved.lean, and so above the files under ThirdParty/ (lean/LIMITS.md, L15): a
fact on import lines. At the earlier hash `OnBytes.secondHashFunction`, a fixed function.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.AtPureFullIn
import Johnson.Desc.ProofFile.Honest.K5.Law.TraceFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K5
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

include h in
/-- hV0 IS PAID BY NOBODY. **AT `fullIn` THE PREMISE ON THE TRACE FOLLOWS FROM ONE PREMISE ON VALID
INPUTS.** CONDITIONAL: under the hypothesis h; hV0. -/
theorem traceIsFull_at_fullIn {Rc : Type} {Vd : Local Cm.Idx Rc ProofFile.Inst Cells → Prop}
    (hV0 : ∀ v, Vd v → fullIn.trace Zp v.w₀ v.x = some v.trace) :
    TraceIsFull (P5J.At.X Zp) Vd (id : Cells → Cells) := by
  refine traceIsFull_of_cellOf h (fun v hv => ?_)
  obtain ⟨x', -, hs, e⟩ := fullIn_trace_some (hV0 v hv)
  refine ⟨OnBytes.HonestTrace.plOf (P5J.At.X Zp) v.w₀ x', v.w₀, x', hs, fun l s r c => ?_⟩
  exact congrArg (fun C : Cells => C.cell l s r c) e

end ProofFile.Honest.K5

#print axioms ProofFile.Honest.K5.traceIsFull_at_fullIn
