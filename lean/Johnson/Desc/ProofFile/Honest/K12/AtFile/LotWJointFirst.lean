-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotWJointFirst.lean: the members' sample rows in front of
the last chain's proximity test: THE PREMISE AT THE FIRST CHAIN's END, TURNED FROM THE LAST CHAIN's
WITNESS TO THE FIRST CHAIN's OWN. Statements with their proofs; no definition.

Why. `samples_at_lastThread` (LotWJointSamplesAtLastThread.lean of this folder) asks, at what the
first chain's last record hands on, that the sample rows of the handed own group's members say of
the words that the LAST thread's witness gives (`lastWitness`,
Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean).
That witness is the first chain's Script's witness with three messages of the shared chain laid over
it, at seats of the shared chain's trees. So at a message that sits in a tree of the first chain
both witnesses give the same words (`wordsBy_first`,
Johnson/Desc/ProofFile/Honest/K14/FirstAtLastWitness.lean).
  `sampleSays_at_lastWitness`   so what the message's sample rows say of the one they say of the
      other, at a statement in order: asks that the message's seat, if it has one, is in a tree of
      the first chain (hseat).
  `samples_at_lastThread_own`   **`samples_at_lastThread` with its premise at the first chain's end
      said of the first chain's own witness** (still at the record that the last thread names, and
      at the last thread's run's input and list of challenges). New beside it:
      hSeats: the first chain's last statement is in order, and the handed own group's members sit
      in trees of the first chain. (The first half comes off the thread: `order_at_ends`,
      LotWJointJoined.lean of this folder.)

Limits. Those of LotWJointSamplesAtLastThread.lean. hFirst, hSeats and hOmega are premises here. hd,
the head at the maker's return, holds the library's one hypothesis on the public files at the full
size: a hypothesis, which these proofs spend (that the shared chain's three messages have numbers of
their own); this file builds no member of it.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotWJointSamplesAtLastThread
import Johnson.Desc.ProofFile.Honest.K14.FirstAtLastWitness

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- The library's files on the full size switch this instance off; so must a file that names them.
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtFile.LotWJoint
open ProofFile.Honest
open OnBytes (Statement TreeBook)
open OnBytes.Slice (rdE GE frS)
open OnBytes.Means (SampleSays sampleItem says_agree)
open VerifiableInference.Desc.Sound (wordsFirst wordsShared seatBy noFirst)
open VerifiableInference.Desc.Third (S₃ firstOfS sharedOfEnd)
open VerifierAndGoals.AtTheName (dpZ)
open ProofFile.Honest.K14 (wordsBy_first)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LastThreadParts lastThread
  lastWitness)

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  (hd : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)

/-- **At a message that sits in a tree of the first chain: what its sample rows say of the words
that the first chain's own witness gives, they say of the words that the last chain's witness
gives.** -/
theorem sampleSays_at_lastWitness (k : Coins A.B) (w : Local W₀ Rc ProofFile.Inst Tr)
    (heard : List Fmt.Drawn) (St : Statement) (hI : OnBytes.Means.InOrder St) (book : TreeBook)
    (n : ℕ)
    (hseat : ∀ q, seatBy noFirst book n = some q → q.1 < hd.description.t₁)
    (hs : SampleSays rdE St n
      (wordsFirst (P5J.At.arr A.Z) St book (first.script.wit k w heard))) :
    SampleSays rdE St n
      (wordsFirst (P5J.At.arr A.Z) St book (lastWitness hd first reads k w heard)) := by
  intro x hx r hr
  refine (says_agree rdE (hI.samples n x hx r hr) fun n' hn' part i => ?_).1 (hs x hx r hr)
  obtain rfl : n' = n := by simpa using hn'
  exact (wordsBy_first hd first reads k w heard _ St n' hseat part i).symm

variable (parts : LastThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **IN FRONT OF THE TEST THE SAMPLE ROWS OF ALL MEMBERS OF THE OWN GROUP SAY OF THE WORDS OF THE
ITEM "rows"**: with the premise at the first chain's end said of the first chain's own witness. -/
theorem samples_at_lastThread_own {k : Coins A.B} {st : S₃}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (u : Thr (lastThread hd first reads parts w) 2 k st m E) (ds : List Fmt.Drawn)
    (hFirst : ∀ f, firstOfS (parts.ends k m.st.input
        (m.st.heard.take (lastThread hd first reads parts w).front)).1.2 = some f →
      ∀ G, f.st.groups[f.own]? = some G → sampleItem rdE f.st G.members.toList
        (wordsFirst (P5J.At.arr A.Z) f.st f.book
          (first.script.wit k m.st.input (m.st.heard ++ ds))))
    (hSeats : ∀ f, firstOfS (parts.ends k m.st.input
        (m.st.heard.take (lastThread hd first reads parts w).front)).1.2 = some f →
      OnBytes.Means.InOrder f.st ∧ ∀ G, f.st.groups[f.own]? = some G → ∀ n ∈ G.members.toList,
        ∀ q, seatBy noFirst f.book n = some q → q.1 < hd.description.t₁)
    (hOmega : ∀ e, Desc.K14.ended (parts.ends k m.st.input
        (m.st.heard.take (lastThread hd first reads parts w).front)).2 = some e →
      SampleSays rdE (sharedOfEnd e).st (sharedOfEnd e).omega
        (wordsShared (P5J.At.arr A.Z) ((dpZ files).at frS.P.T.a).t₁ (sharedOfEnd e).st
          (sharedOfEnd e).book (lastWitness hd first reads k m.st.input (m.st.heard ++ ds)))) :
    ∀ G', st.st.groups[st.loc.own]? = some G' →
      sampleItem rdE st.st G'.members.toList
        (wordsAtW hd first reads st k m.st.input (m.st.heard ++ ds)) :=
  samples_at_lastThread hd first reads parts w u ds
    (fun f hf G hG n hn => sampleSays_at_lastWitness hd first reads k m.st.input _ f.st
      (hSeats f hf).1 f.book n ((hSeats f hf).2 G hG n hn) (hFirst f hf G hG n hn)) hOmega

end ProofFile.Honest.K12.AtFile.LotWJoint

#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.sampleSays_at_lastWitness
#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.samples_at_lastThread_own
