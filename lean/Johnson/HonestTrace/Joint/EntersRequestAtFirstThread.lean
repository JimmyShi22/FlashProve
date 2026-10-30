-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Joint/EntersRequestAtFirstThread.lean

Nothing on hiding. No property of the protocol is claimed.
ONE PREMISE OF "enters_firstThread" (Johnson/Desc/ProofFile/Honest/Thread/EntersFirst.lean), PAID FROM ANOTHER OF ITS
PREMISES. That theorem takes "hReq": the request file's bytes are read back (Meaning.backReq … isSome), and "hok": the
description's test on the instance accepts. Under the head (P5J.AtMgA, which holds the goals' scope, the files' reading
and the public data) hok gives hReq: the test's first half returns a ground, so the program's own
reader takes the two files
(ProofFile.instOf_of_hold_in_scope), so the request file's bytes are those of an instance and are read back.

Main theorems.
* "instanceIsReadWhereTheTestAccepts": under h : AtMgA …, where (F0T o Zp Np cF).okStart ξ = true, some x has
  ProofFile.instOf ξ = some x.
* "requestIsReadBackUnderTheHead": there, (Meaning.backReq (h.𝔇.reqB ξ.pub)).isSome = true.
* "requestIsReadBackAtFirstThread": hReq to the letter, at h : HeadAtReturn files A, from hok to the letter.
An "example" at the foot calls enters_firstThread with it: a guard by Lean that the letters fit.

Limits. That the test accepts at any instance is a premise (hok; on it see the warning in
Johnson/Desc/ProofFile/Honest/Thread/ReadyInput.lean: it tests the table's key too). No member of AtMgA or HeadAtReturn is
shown here. The x of the first theorem is not tied here to the x that "laws_of_readyInput_at_the_term" hands: both are
"ProofFile.instOf ξ = some x" at one ξ, so they are one by Option.some.inj.
-/
import Johnson.HonestTrace.Joint.EntersRequest
import Johnson.Desc.ProofFile.Honest.Thread.EntersFirst
import Johnson.Desc.ProofFile.InstOfInScope
import E2E.StartAtFiles

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace HonestTraceRun.Enters

open Inst.Model (ppref Instance)
open P5J (AtMgA F0T TS)
open OnBytes.Maker (WholeD)

section UnderTheHead
variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain TS ProofFile.Cl}
  {xp : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head, where the description's test on the instance accepts, the two files are read as an instance.** -/
theorem instanceIsReadWhereTheTestAccepts (h : AtMgA o Z D r Zp Np cF xp) {ξ : ProofFile.Inst}
    (accepts : (F0T o Zp Np cF).okStart ξ = true) : ∃ x : Instance ppref, ProofFile.instOf ξ = some x := by
  rw [AtPublicFiles.Start.okStart_eq, Bool.and_eq_true] at accepts
  have held := accepts.1
  unfold ProofFile.okBy at held
  cases hG : ProofFile.holdBy o ProofFile.pureRoad.links Zp ξ with
  | error e =>
    rw [hG] at held
    cases held
  | ok G =>
    exact Option.isSome_iff_exists.1 (ProofFile.instOf_of_hold_in_scope h.scope h.reads h.pubOne hG)

/-- **Under the head, where the test accepts, the request file's bytes are read back**, at the head's own reader of these
bytes. -/
theorem requestIsReadBackUnderTheHead (h : AtMgA o Z D r Zp Np cF xp) {ξ : ProofFile.Inst}
    (accepts : (F0T o Zp Np cF).okStart ξ = true) :
    (Meaning.backReq (h.𝔇.reqB ξ.pub)).isSome = true := by
  obtain ⟨x, read⟩ := instanceIsReadWhereTheTestAccepts h accepts
  exact requestBytesAreReadBack read

end UnderTheHead

section AtFirstThread
open ProofFile.Honest ProofFile.Honest.FirstThread

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  {h : HeadAtReturn files A} {parts : FirstThreadParts A} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst}
  {k : Coins A.B} {R : Ready W₀ Rc ProofFile.Inst OnBytes.TableKey Tr X₀ X}

/-- **THE PREMISE hReq OF enters_firstThread, TO THE LETTER, FROM ITS PREMISE hok.** -/
theorem requestIsReadBackAtFirstThread (hok : h.description.okStart x = true) :
    (_root_.Meaning.backReq (h.head.𝔇.reqB x.pub)).isSome = true :=
  requestIsReadBackUnderTheHead h.head hok

/-- A guard by Lean that the letters fit: enters_firstThread, called without a premise on the request's bytes. -/
example (hR : ready h.description A.B A.H w₀ rc x k = .ok R)
    (hok : h.description.okStart x = true)
    {i : Cm.Idx} {served : Instance ppref} (Sv : OnBytes.HonestTrace.ServesAt (P5J.At.X A.Z) i served)
    (Ti : OnBytes.HonestTrace.ScriptTies files A.Z h.firstChain parts.script k R.own i served) :
    Enters₁ h.description A.H (firstThread h parts R.own) w₀ rc x k R :=
  enters_firstThread hR hok (requestIsReadBackAtFirstThread hok) Sv Ti

end AtFirstThread

end HonestTraceRun.Enters

#print axioms HonestTraceRun.Enters.instanceIsReadWhereTheTestAccepts
#print axioms HonestTraceRun.Enters.requestIsReadBackUnderTheHead
#print axioms HonestTraceRun.Enters.requestIsReadBackAtFirstThread
