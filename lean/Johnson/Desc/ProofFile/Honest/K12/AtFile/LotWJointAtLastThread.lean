-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotWJointAtLastThread.lean: the joint between the last
chain's first block and that chain's proximity test (LotWJoint.lean of this folder) AT THE LAST
THREAD AS IT IS WRITTEN (`lastThread`, Honest/Thread/TheFirstThread.lean). One definition;
statements with their proofs: calls. General in the return A, the head at it and all that the thread
takes from outside.

WHAT A STAND IN FRONT OF THE TEST (the thread at the border 2) GIVES THERE:
  `yes_at_lastThread`    a first state s₀ that the description's start of the last chain returns at
                         the two earlier chains' ends as the thread names them, and rounds and
                         columns at which `batchLinearConstraintsSecondPart`'s decision at the seat's parameters returned
                         the stand's own state.
  `order_at_lastThread`  the stand's statement is in order: the thread's own clause on its form.
  `wordsAtW`             THE WORDS OF WHICH THE ITEM "rows" SPEAKS THERE, as a term: `wordsAtOwn` at
                         the seat's codes, the plan's numbering and counts of trees, the stand's
                         state and the thread's witness (`lastWitness`).
  `rows_at_lastThread`   all rows of the own group say of these words, at every continuation of the
                         challenges.

For whom. The test's acceptance asks five clauses on one list of words m (LotWJoint.lean's head).
Here the first and the third are had, at m := `wordsAtW` …: so the clause on the members' sample
rows and the clause that ties m to the job's plain rows are to be shown at these words.

Limits. Statements from a stand: neither this file nor any file that it imports shows that the
thread stands at the border 2 at any
run. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotWJoint
import Johnson.Desc.ProofFile.Honest.Thread.TheFirstThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtFile.LotWJoint
open ProofFile.Honest
open OnBytes.Slice (rdE GE frS)
open OnBytes.Means (AllSay)
open VerifiableInference.Desc.Third (S₃ batchLinearConstraintsSecondPart)
open ToldDesc (p14At)
open VerifierAndGoals.AtTheName (dpZ)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LastThreadParts lastThread
  lastWitness)

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  (hd : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
  (parts : LastThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **IN FRONT OF THE TEST: THE START's YES AND THE FIRST BLOCK's YES.** -/
theorem yes_at_lastThread {k : Coins A.B} {st : S₃} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (u : Thr (lastThread hd first reads parts w) 2 k st m E) :
    ∃ s₀ rs gs,
      hd.description.start₃
          (parts.ends k m.st.input
            (m.st.heard.take (lastThread hd first reads parts w).front)).1.1
          (parts.ends k m.st.input
            (m.st.heard.take (lastThread hd first reads parts w).front)).1.2
          (parts.ends k m.st.input
            (m.st.heard.take (lastThread hd first reads parts w).front)).2 = .ok s₀ ∧
      (batchLinearConstraintsSecondPart (Cl := Unit) (p14At A.Z)).decide s₀ rs gs = .ok st :=
  thr_two_yes A.Z hd.places hd.firstChain A.H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ w u

/-- **In front of the test the statement is in order.** -/
theorem order_at_lastThread {k : Coins A.B} {st : S₃} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (u : Thr (lastThread hd first reads parts w) 2 k st m E) :
    OnBytes.Means.InOrder st.st :=
  u.2.2.1.2

/-- **The words of which the last thread's item "rows" speaks**, at a state, a run's coins, an input
and a list of challenges. -/
noncomputable def wordsAtW (s : S₃) (k : Coins A.B) (v : Local W₀ Rc ProofFile.Inst Tr)
    (heard : List Fmt.Drawn) : OnBytes.Means.Words GE :=
  wordsAtOwn (p14At A.Z).codes (P5J.At.arr A.Z) ((dpZ files).at frS.P.T.a).t₁
    ((dpZ files).at frS.P.T.a).t₂ s (lastWitness hd first reads k v heard)

/-- **IN FRONT OF THE TEST ALL ROWS OF THE OWN GROUP SAY OF THESE WORDS**, at every continuation of
the challenges. -/
theorem rows_at_lastThread {k : Coins A.B} {st : S₃} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (u : Thr (lastThread hd first reads parts w) 2 k st m E) (ds : List Fmt.Drawn) :
    ∀ G, st.st.groups[st.loc.own]? = some G →
      AllSay rdE st.st G.rows.toList (wordsAtW hd first reads st k m.st.input (m.st.heard ++ ds)) :=
  rows_at_two (LastThread.lettersLast A.Z hd.places hd.firstChain A.H hd.sharedNumbers parts.meaning
      hd.lastMeaning hd.lastForm (fun s => OnBytes.Means.InOrder s.st) parts.taken parts.ends
      (lastWitness hd first reads) parts.table parts.fixed 0 hd.description.t₁ hd.description.t₂
      (ReadyInput hd.description A.H) parts.rides
      (ProofFile.Honest.K14.kpSecond (p14At A.Z) parts.keeps) w)
    (p14At A.Z).codes (P5J.At.arr A.Z) _ _ rfl u ds

end ProofFile.Honest.K12.AtFile.LotWJoint

#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.yes_at_lastThread
#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.order_at_lastThread
#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.rows_at_lastThread
