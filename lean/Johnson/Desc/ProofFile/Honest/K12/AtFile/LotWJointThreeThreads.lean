-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotWJointThreeThreads.lean: the members' sample rows in
front of the last chain's proximity test: FROM THE THREE CHAINS' THREADS AS THEY ARE WRITTEN
(`firstThread`, `sharedThread`, `lastThread`,
Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean). One statement with its proof; no
definition.

`samples_of_three_threads`: **the sample rows of all members of the own group say of the words of
which the last thread's item "rows" speaks** (`wordsAtW`, LotWJointAtLastThread.lean of this
folder), at every continuation ds of the challenges. ALL ITS PREMISES. "A thread holds at a border":
its invariant `Thr` there, at one run's coins k, the same in all three.
  hd    the head at the maker's return: it holds the library's one hypothesis on the public files at
        the full size, at the format's second hash function. IT IS A HYPOTHESIS, and the proof
        spends it; this file builds no member of it;
  u     the last thread holds in front of the test (the border 2);
  u₁    the first thread holds at that chain's last border, at a state e₁;
  u₂    the shared thread holds at that chain's last border, at a state e₂;
  he₁, he₂   THE TIE: the two records that the last thread names as the earlier chains' last records
        are e₁ and e₂;
  hin   the shared thread's run has the input that is made of the last thread's run's;
  hq    the first challenge that the shared thread's run has heard is the first behind the first
        chain's in the list that the last chain's witness is handed;
  hFirst   at what e₁ hands on: the sample rows of the handed own group's members say of the words
        that the first chain's own witness gives through e₁'s statement and book, READ AT THE LAST
        THREAD's RUN's INPUT AND LIST OF CHALLENGES.

Against `samples_at_lastThread_joined` (LotWJointJoined.lean of this folder) five premises are not
asked: the four on Omega at the shared chain's last record, and that the handed members sit
in trees of the first chain. They follow from u₂ and u₁: `omega_samples_at_end`
(Johnson/Desc/ProofFile/Honest/K14/OmegaSamplesAtEnd.lean), `head_seats_below`
(Johnson/Desc/ProofFile/Honest/K14/FirstSeatsBelow.lean).

WHAT THIS FILE DOES NOT SHOW.
  The tie he₁, he₂, hin, hq: the last thread takes the two records from outside; neither this file
  nor any file that it imports ties them to the other two threads' runs.
  A THIRD TIE, which whoever shows hFirst from u₁ needs and which is no premise here: u₁'s items
  speak at that thread's own run's input and challenges, hFirst at the last thread's: so that the
  first thread's run has the last thread's run's input, and that what it has heard is the front of
  what the last thread's run has heard. Of u₁ this proof reads the seats alone.
  hFirst itself. Under that tie the two pins hold at e₁, in the form that a pin has on the honest
  side (`pins_at_first_end`, `pins_at_last_run`, LotWJointPins.lean of this folder). Left behind
  them: that the handed group's two members are the two pinned messages, that e₁'s book seats them
  at the pins' seats, and that a pin's equation gives "the sample row says": all three follow from
  two public tests on e₁: `samples_at_W_from_threads` (AtFullSide/K12/SamplesAtWFromThreads.lean).

Limits. Neither this file nor any file that it imports shows that any of the three threads holds at
these borders at any run. One ds
serves this clause, the clause on the rows and the clause that ties the words to the job's rows.
Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotWJointJoined
import Johnson.Desc.ProofFile.Honest.K14.OmegaSamplesAtEnd
import Johnson.Desc.ProofFile.Honest.K14.FirstSeatsBelow

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- The library's files on the full size switch this instance off; so must a file that names them.
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtFile.LotWJoint
open ProofFile.Honest
open OnBytes.Slice (rdE)
open OnBytes.Means (sampleItem)
open VerifiableInference.Desc.Sound (wordsFirst)
open VerifiableInference.Desc.Third (S₃ firstOfS)
open VerifiableInference.Desc.Last (firstOfS_parts)
open P5J (TS)
open ProofFile.Honest.K14 (omega_samples_at_end head_seats_below firstRv)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LastThreadParts
  SharedThreadParts firstThread sharedThread lastThread)

variable {W₀ Rc Tr X₀ X Wt : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  (hd : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
  (sh : SharedThreadParts A Wt) (parts : LastThreadParts A) (w w₁ : Local W₀ Rc ProofFile.Inst Tr)
  (w₂ : Common W₀ Rc OnBytes.TableKey)

/-- **IN FRONT OF THE LAST CHAIN's TEST THE SAMPLE ROWS OF ALL MEMBERS OF THE OWN GROUP SAY OF THE
WORDS OF THE ITEM "rows"**: from the three threads, the tie of the records that the last thread
names, and what the handed members' sample rows say at the first chain's end of that chain's own
witness. -/
theorem samples_of_three_threads {k : Coins A.B} {st : S₃}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (u : Thr (lastThread hd first reads parts w) 2 k st m E) (ds : List Fmt.Drawn)
    {e₁ : TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E₁ : Env}
    (u₁ : Thr (firstThread hd first w₁) hd.firstChain.blocksInOrder.length k e₁ m₁ E₁)
    {e₂ : Desc.K14.St} {m₂ : Mid (Common W₀ Rc OnBytes.TableKey) X₀} {E₂ : Env}
    (u₂ : Thr (sharedThread hd reads sh w₂) hd.description.shared.blocksInOrder.length k e₂ m₂ E₂)
    (he₁ : (parts.ends k m.st.input
        (m.st.heard.take (lastThread hd first reads parts w).front)).1.2 = e₁)
    (he₂ : (parts.ends k m.st.input
        (m.st.heard.take (lastThread hd first reads parts w).front)).2 = e₂)
    (hin : m₂.st.input = ⟨m.st.input.w₀, m.st.input.rc, A.H.key m.st.input.x⟩)
    (hq : firstRv m₂.st.heard = firstRv ((m.st.heard ++ ds).drop
      (declsTo hd.description.first.blocksInOrder hd.description.first.blocksInOrder.length).length))
    (hFirst : ∀ f, firstOfS e₁ = some f →
      ∀ G, f.st.groups[f.own]? = some G → sampleItem rdE f.st G.members.toList
        (wordsFirst (P5J.At.arr A.Z) f.st f.book
          (first.script.wit k m.st.input (m.st.heard ++ ds)))) :
    ∀ G', st.st.groups[st.loc.own]? = some G' →
      sampleItem rdE st.st G'.members.toList
        (wordsAtW hd first reads st k m.st.input (m.st.heard ++ ds)) := by
  refine samples_at_lastThread_own hd first reads parts w u ds (by rw [he₁]; exact hFirst)
    (fun f hf => ⟨(order_at_ends hd first reads parts w u).1 f hf, fun _ _ n _ q hq' => ?_⟩)
    (by
      rw [he₂]
      exact omega_samples_at_end hd first reads sh w₂ u₂ m.st.input (m.st.heard ++ ds) hin hq)
  rw [he₁] at hf
  rw [(firstOfS_parts hf).2.1] at hq'
  exact head_seats_below hd.head A.H first.script _ _ _ _ _ _ _ _ _ w₁ (Nat.le_refl _) u₁ n q hq'

end ProofFile.Honest.K12.AtFile.LotWJoint

#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.samples_of_three_threads
