-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotWJointPins.lean: THE TWO PINS THAT THE FIRST CHAIN HANDS
OVER TO THE LAST CHAIN's PROXIMITY TEST, READ OFF THE FIRST THREAD AT THAT CHAIN's LAST BORDER
(`firstThread`, Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean). Statements with their
proofs; no definition.

  `pins_open_at_end`    by the library's table of open items at the full size, read forward: the
      items "pinI" (the index masks' message) and "pinV" (the message W) are open at the border 358.
      One evaluation in Lean's kernel.
  `pins_at_first_end`   **where the first thread's invariant holds at that chain's last border, at a
      state e₁: both pins hold there, in the form that a pin has on the honest side** (`ansJT`,
      Johnson/Desc/ProofFile/Honest/Thread/Ans.lean: a member of the plan's list sits at the seat,
      the state holds its sample, and the witness's message has the sample's answers), at the first
      chain's own witness, AT EVERY CONTINUATION ds₁ of the challenges that the thread's run has
      heard.

  `pins_at_last_run`    the same at another run's input v and list l of challenges, where v is the
      thread's run's input and l begins with what the thread's run has heard: the two equations are
      premises.

What for. Whoever shows "the sample row says its claim" from a pin's equation at the first chain's
end (the premise hFirst of `samples_of_three_threads`, LotWJointThreeThreads.lean of this folder)
asks the two pins in this form.

Limits. hd, the head at the maker's return, holds the library's one hypothesis on the public files
at the full size: a hypothesis, of which the proof reads that the first chain has 358 members.
Neither this file nor any file that it imports shows that the thread holds at that border at any
run. The witness is read at
the thread's own run's input and challenges: that these are the last thread's run's is a tie that
neither this file nor any file that it imports has. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread
import Johnson.Desc.ProofFile.Honest.Thread.SteppedYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- The library's files on the full size switch this instance off; so must a file that names them.
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtFile.LotWJoint
open ProofFile.Honest
open VerifiableInference.Desc.First (Item start)
open P5J (TS)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts firstThread head_len)

set_option maxRecDepth 100000 in
/-- The items "pinI" and "pinV" are open at the border number 358. -/
theorem pins_open_at_end :
    Item.pinI ∈ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) 358 ∧
      Item.pinV ∈ fwdOpen (start P5J.At.links) (FirstRows.rows P5J.At.links P5J.At.ps) 358 := by
  decide +kernel

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  (hd : HeadAtReturn files A) (first : FirstThreadParts A) (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **AT THE FIRST CHAIN's LAST BORDER BOTH PINS HOLD, AT THE FIRST CHAIN's OWN WITNESS**, at every
continuation of the challenges heard. -/
theorem pins_at_first_end {k : Coins A.B} {e₁ : TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E₁ : Env} (u₁ : Thr (firstThread hd first w₁) hd.firstChain.blocksInOrder.length k e₁ m₁ E₁)
    (ds₁ : List Fmt.Drawn) :
    ansJT (P5J.At.cs A.Z) (P5J.At.arr A.Z) (P5J.At.smp A.Z) (P5J.At.ms A.Z files.lay)
        (P5J.At.N A.Z hd.firstChain).index.1 (P5J.At.N A.Z hd.firstChain).index.2
        (m₁.st.input.x.pub, e₁) ((firstThread hd first w₁).strs E₁)
        (first.script.wit k m₁.st.input (m₁.st.heard ++ ds₁)) ∧
      ansJT (P5J.At.cs A.Z) (P5J.At.arr A.Z) (P5J.At.smp A.Z) (P5J.At.ms A.Z files.lay)
        (P5J.At.N A.Z hd.firstChain).w.1 (P5J.At.N A.Z hd.firstChain).w.2
        (m₁.st.input.x.pub, e₁) ((firstThread hd first w₁).strs E₁)
        (first.script.wit k m₁.st.input (m₁.st.heard ++ ds₁)) := by
  rw [head_len hd.head] at u₁
  exact ⟨u₁.2.2.2.1 ds₁ Item.pinI pins_open_at_end.1, u₁.2.2.2.1 ds₁ Item.pinV pins_open_at_end.2⟩

/-- **The same at another run's input and list of challenges**, where that input is the thread's
run's and the list begins with what the thread's run has heard. -/
theorem pins_at_last_run {k : Coins A.B} {e₁ : TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E₁ : Env} (u₁ : Thr (firstThread hd first w₁) hd.firstChain.blocksInOrder.length k e₁ m₁ E₁)
    (v : Local W₀ Rc ProofFile.Inst Tr) (l rest : List Fmt.Drawn) (hv : m₁.st.input = v)
    (hl : l = m₁.st.heard ++ rest) :
    ansJT (P5J.At.cs A.Z) (P5J.At.arr A.Z) (P5J.At.smp A.Z) (P5J.At.ms A.Z files.lay)
        (P5J.At.N A.Z hd.firstChain).index.1 (P5J.At.N A.Z hd.firstChain).index.2
        (v.x.pub, e₁) ((firstThread hd first w₁).strs E₁) (first.script.wit k v l) ∧
      ansJT (P5J.At.cs A.Z) (P5J.At.arr A.Z) (P5J.At.smp A.Z) (P5J.At.ms A.Z files.lay)
        (P5J.At.N A.Z hd.firstChain).w.1 (P5J.At.N A.Z hd.firstChain).w.2
        (v.x.pub, e₁) ((firstThread hd first w₁).strs E₁) (first.script.wit k v l) := by
  subst hv
  subst hl
  exact pins_at_first_end hd first w₁ u₁ rest

end ProofFile.Honest.K12.AtFile.LotWJoint

#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.pins_open_at_end
#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.pins_at_first_end
#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.pins_at_last_run
