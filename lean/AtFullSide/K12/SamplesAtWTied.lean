-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/SamplesAtWTied.lean: the members' sample rows in front of the last chain's proximity
test, FROM A STAND OF THE LAST THREAD WITH ONE SENTENCE ON THE RUN BESIDE IT, IN WHICH THE TWO
EARLIER THREADS' STANDS ARE HELD. One statement with its proof; no definition.

Why. The test's acceptance is to be shown at every stand of the last thread (its invariant `Thr` in
front of the test) together with a sentence on the run, which is a free parameter of the frame. A
stand of the last thread does not remember the two earlier chains, so whatever is needed of them has
to be held by that sentence. The sentence here is `TiedToEnds`
(Johnson/Desc/ProofFile/Honest/K14/TiedToEnds.lean): there are stands of the first and of the shared
thread at their chains' last borders, under sentences Said₁ and Said₂ of their own, at this run's
coins; the first one's input is this run's, the shared one's is made of it; and the rounds that the
two have seen, one list behind the other, are the rounds that this run has seen in front of the last
chain.

`samples_at_W_of_tied`: **the sample rows of all members of the own group say of the words of which
the last thread's item "rows" speaks** (`wordsAtW`,
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotWJointAtLastThread.lean), at every continuation ds of
the challenges. ALL ITS PREMISES. The threads: `firstThread`, `sharedThread`, `lastThread`
(Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean).
  hd      the head at the maker's return: it holds the library's one hypothesis on the public files
          at the full size, at the format's second hash function: A HYPOTHESIS, which the proof
          uses; this file builds no member of it;
  u       the last thread holds in front of the test (the border 2);
  ht      `TiedToEnds` at that stand's run;
  hSaid   Said₁ gives that every word which the rounds seen show is below the field's prime
          (`SaidOk`, Johnson/Desc/ProofFile/Honest/Thread/SaidOk.lean);
  hEnds   AN EQUATION ON A VALUE: what the last thread takes from outside as "the two earlier
          chains' last records" returns, at this run's coins and input and at the challenges that
          it had heard in front of the last chain, the two states that the library's term `endsBy`
          (Johnson/Desc/ProofFile/Honest/Thread/OneState.lean) returns at these two threads, borders
          and sentences. `endsBy` chooses a pair of stands where there is one, and `ties_at_endsBy`
          (TiedToEnds.lean) has the stands at the states that it returns. So hEnds BY ITSELF asks
          nothing on whether a run has one state only; u brings that question back (below);
  two instances: the two earlier chains' types of state are inhabited (`endsBy` returns a default
          where there is no pair; at the list named here there is one, under ht).

NOTHING OF THE TWO EARLIER THREADS IS SHOWN HERE: THEIR STANDS ARE MOVED INTO ht. Of the six
equations that tie the three runs in `samples_at_W_from_stands` (SamplesAtWFromStands.lean of this
folder), the two on the inputs are clauses of the sentence, and of what `endsBy` chooses by; the two
on the challenges are derived from its clause on the rounds seen, the invariants and hd; the two on
the records are hEnds.

WHAT THIS FILE DOES NOT SHOW.
  That the first and the shared thread hold at their last borders at a run, under Said₁ and Said₂,
  with the inputs so tied; that these two sentences are carried past all members of their chains.
  That the sentence is had where the last chain is entered: TiedToEnds.lean has it behind two such
  stands (`tied_at_door_written`) and carries it past every member (`tied_next`). A reading, no
  theorem: it can be entered by a rule of the frame that hands over the two whole stands at that
  door (`DoorBehindS`, Johnson/Desc/ProofFile/Honest/Thread/FileD.lean); the rules that hand over
  the two earlier sentences alone cannot be used with it as they stand. TiedToEnds.lean's head says
  which rules are which.
  hEnds at the value that is laid for these records, at the same Said₁ and Said₂; hSaid at that
  Said₁.
  That the last thread holds at the border 2 at a run. THERE THE QUESTION "ONE STATE FOR EACH RUN"
  COMES BACK: the last thread's own first state is made of the records that the same parameter
  names, while the door hands over the run's own two last states; so where the parameter is made of
  `endsBy`, the thread can be entered only where `endsBy` returns the run's own two, which the
  library has where each earlier chain has one state for each run (`endsAre_endsBy`, OneState.lean).
  On the whole road nothing is saved by the form of hEnds. The stands at the states that `endsBy`
  returns need not be this run's own ends.

Limits. The three inputs w, w₁, w₂ are free letters; each thread's invariant says that its run's
input is the thread's own, so at inputs that are not tied as the sentence says the premises cannot
hold together and the statement says nothing. One ds serves this clause, the clause on the rows and
the clause that ties the words to the job's rows. Nothing on soundness, completeness or hiding.
-/
import AtFullSide.K12.SamplesAtWFromStands
import Johnson.Desc.ProofFile.Honest.K14.TiedToEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- The library's files on the full size switch this instance off; so must a file that names them.
attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K12
open ProofFile.Honest
open OnBytes.Slice (rdE)
open OnBytes.Means (sampleItem)
open VerifiableInference.Desc.Third (S₃)
open P5J (TS)
open ProofFile.Honest.K14 (TiedToEnds ties_at_endsBy)
open ProofFile.Honest.K12.AtFile.LotWJoint (wordsAtW)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LastThreadParts
  SharedThreadParts firstThread sharedThread lastThread)

variable {W₀ Rc Tr X₀ X Wt : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  (hd : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
  (sh : SharedThreadParts A Wt) (parts : LastThreadParts A) (w w₁ : Local W₀ Rc ProofFile.Inst Tr)
  (w₂ : Common W₀ Rc OnBytes.TableKey)

/-- **IN FRONT OF THE LAST CHAIN's TEST THE SAMPLE ROWS OF ALL MEMBERS OF THE OWN GROUP SAY OF THE
WORDS OF THE ITEM "rows"**: from a stand of the last thread, the sentence that holds stands of the
two earlier threads tied to its run, and that the records which the last thread names are the
library's chosen ones. -/
theorem samples_at_W_of_tied [Inhabited TS] [Inhabited Desc.K14.St]
    (Said₁ : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (Said₂ : Nat → Coins A.B → Mid (Common W₀ Rc OnBytes.TableKey) X₀ → Prop)
    (hSaid : ∀ b k m, Said₁ b k m → SaidOk b k m) {k : Coins A.B} {st : S₃}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (u : Thr (lastThread hd first reads parts w) 2 k st m E)
    (ht : TiedToEnds (firstThread hd first w₁) Said₁ hd.description.first.blocksInOrder.length
      (sharedThread hd reads sh w₂) Said₂ hd.description.shared.blocksInOrder.length id
      (fun v => ⟨v.w₀, v.rc, A.H.key v.x⟩) (lastThread hd first reads parts w).front 2 k m)
    (hEnds : (parts.ends k m.st.input
        (m.st.heard.take (lastThread hd first reads parts w).front)).1.2 =
      (endsBy (firstThread hd first w₁) Said₁ hd.description.first.blocksInOrder.length
        (sharedThread hd reads sh w₂) Said₂ hd.description.shared.blocksInOrder.length id
        (fun v => ⟨v.w₀, v.rc, A.H.key v.x⟩) k m.st.input
        (m.st.heard.take (lastThread hd first reads parts w).front)).1 ∧
      (parts.ends k m.st.input
        (m.st.heard.take (lastThread hd first reads parts w).front)).2 =
      (endsBy (firstThread hd first w₁) Said₁ hd.description.first.blocksInOrder.length
        (sharedThread hd reads sh w₂) Said₂ hd.description.shared.blocksInOrder.length id
        (fun v => ⟨v.w₀, v.rc, A.H.key v.x⟩) k m.st.input
        (m.st.heard.take (lastThread hd first reads parts w).front)).2)
    (ds : List Fmt.Drawn) :
    ∀ G', st.st.groups[st.loc.own]? = some G' →
      sampleItem rdE st.st G'.members.toList
        (wordsAtW hd first reads st k m.st.input (m.st.heard ++ ds)) := by
  obtain ⟨m₁, E₁, m₂, E₂, u₁, u₂, hi₁, ⟨rest, hh₁⟩, hin, hq, -⟩ :=
    ties_at_endsBy hd first reads sh parts w₁ w w₂ Said₁ Said₂ u ht
  exact samples_at_W_from_stands hd first reads sh parts w w₁ w₂ Said₁ hSaid u ds u₁ u₂.1
    hEnds.1 hEnds.2 hi₁ rest hh₁ hin (hq ds)

end AtFullSide.K12

#print axioms AtFullSide.K12.samples_at_W_of_tied
