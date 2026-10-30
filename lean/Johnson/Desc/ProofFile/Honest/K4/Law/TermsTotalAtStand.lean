-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/TermsTotalAtStand.lean: CONDITIONAL. Statements with their
proofs.

What is here: at a stand (`K4Stand`, Law/SlotsTrue.lean) of the feed-forward layers' own rounds (the
sub-protocol K4), in the world of every ledger later than the one that the member's step leaves: THE
SLOT OF THE SECOND TOKEN SUMCHECK's CLAIMED SUM IS WORTH THE TOTAL OF THE HONEST JOB's CUBE.
`terms_total_stand`: at the job that is made of what `Sides.of` returns in front of that sumcheck.
`terms_total_stack`: THE SAME AT THE JOB THAT IS MADE OF THE BATCHED SUMCHECK's OWN DATA
(`stackData`, in front of the batched sumcheck): the hypothesis hσ of `joinWorth_made`
(Law/JoinMade.lean), in its own text, at that world.
How. Each slot is worth the honest part's own word (`opened_left`, Law/SlotsTrue.lean); the part's
one leading scalar is its cube's total (`jobTermsOn_lead`, Law/StackAtStand.lean): the step that
stands inside `stack_stand`'s proof, by a name. What the two jobs share reads, of the sampled
values, what the lookup returned alone (`sidesOf_fo`, Law/StackWhole.lean), and that is one in front
of both sumchecks (`at_look`, Law/PtsAt.lean).

Not shown here. That the step of K4's member accepts is a premise (it is in `K4Stand`). That the
premises can be met: no example is known. It says what a slot is worth where the honest parts have
played: nothing on a prover that plays otherwise. Nothing on soundness, on completeness or on any
other property. No property is claimed.

  `terms_total_stand`   at the second token sumcheck's own job
  `terms_total_stack`   **at the job made of the batched sumcheck's data**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.StackAtStand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (zeroE)
open OnBytes.Model (Reading Fork Tsc)
open OnBytes.Model.Layer (Own)
open OnBytes.PscRun (Later)
open OnBytes.Desc.First.K4 (Par)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block Claim First.S)
open VerifiableInference.Desc.Sound (MsgQ)
open ProofFile.Honest.K4.SlotsOwn (worldBehind)

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr X Pb : Type}
  {T : Thread Bk First.S Claim (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Pb} {b : Nat}
  {cells : Tr → Cells} {weights : W₀ → Weights} {tokens : Xi → Array Nat}
  {look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard} {Q : K4Pub} {p : Par}
  {blk : Block First.S Claim} {own : List (Nat × Nat)} {rdOf : T.Wt → Nat × Nat → MsgQ}
  {k : Coins Bk} {s s' : First.S} {m : Mid (Local W₀ Rc Xi Tr) X} {E : Env}
  {ds : List Fmt.Drawn} {y : List Played × Mid (Local W₀ Rc Xi Tr) X}
  {cols : List VerifiableInference.Desc.OpenedColumn} {A : VerifiableInference.Desc.K9.Part} {o : Own}

/-- CONDITIONAL on the named premises. At the second token sumcheck's own job. -/
theorem terms_total_stand
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (ds' : List Fmt.Drawn) (F : Fork) (hL : Later A.F F) (entry : Nat → Nat → Nat → Cb.Gl.E)
    {S : OnBytes.Desc.First.K4.Honest.Sides} {j : Job}
    (hS : OnBytes.Desc.First.K4.Honest.Sides.of Q
      (k4Wit Q cells weights tokens (look Q) m.st.input)
      (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (m.st.heard ++ ds.take (rJ3 Q.P Q.g))) = some S)
    (hJ : jobTermsOn S = some j) :
    ∀ tT', o.H.tT = some tT' →
      (worldBehind T own rdOf k y A ds' F entry).slot tT'.sCl = Reading.gl.val j.cube.total := by
  intro tT' e
  have hj' : jobTerms Q (k4Wit Q cells weights tokens (look Q) m.st.input)
      (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (m.st.heard ++ ds.take (rJ3 Q.P Q.g))) = some j := by
    unfold jobTerms
    rw [hS]
    exact hJ
  refine ((opened_left Z ds' F hL entry).terms _ e).1.trans ?_
  unfold leadWord
  rw [hj']
  show Reading.gl.val ((j.lead).getD 0 zeroE) = _
  rw [jobTermsOn_lead hJ]
  rfl

/-- CONDITIONAL on the named premises. **AT THE JOB THAT IS MADE OF THE BATCHED SUMCHECK's OWN
DATA.** -/
theorem terms_total_stack
    (Z : K4Stand T b cells weights tokens look Q p blk own rdOf k s m E ds y cols s' A o)
    (hT : Thr T b k s m E) (ds' : List Fmt.Drawn) (F : Fork) (hL : Later A.F F)
    (entry : Nat → Nat → Nat → Cb.Gl.E) {shownT : Array OnBytes.E} {SD : StackData}
    {J : Job}
    (hD : stackData Q (k4Wit Q cells weights tokens (look Q) m.st.input)
      (ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
        (m.st.heard ++ ds.take (rJ4 Q.P Q.g))) shownT = some SD)
    (hJ : jobTermsOn SD.S = some J) :
    ∀ tT', o.H.tT = some tT' →
      (worldBehind T own rdOf k y A ds' F entry).slot tT'.sCl = Reading.gl.val J.cube.total := by
  have hh := k4_heard_front Z.seat hT
  have h1 := (OnBytes.Road.K4.C.stack_open hD).1
  rw [sidesOf_fo Q _ (p' := ptsOf Q (k4Wit Q cells weights tokens (look Q) m.st.input)
    (m.st.heard ++ ds.take (rJ3 Q.P Q.g)))
    (by rw [at_look _ _ ds hh, at_look _ _ ds hh])] at h1
  exact terms_total_stand Z ds' F hL entry h1 hJ

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.terms_total_stand
#print axioms ProofFile.Honest.K4.terms_total_stack
