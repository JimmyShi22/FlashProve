-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotWJointJoined.lean: the members' sample rows in front of
the last chain's proximity test, at the last thread as it is written (`lastThread`,
Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean): THE TWO PREMISES OF
`samples_at_lastThread` (LotWJointSamplesAtLastThread.lean of this folder) CARRIED BACK TO THE TWO
EARLIER CHAINS' OWN WITNESSES. Statements with their proofs; no definition.

"The thread at the border 2" below: the invariant `Thr` of that thread in front of the test, a
premise.
  `ends_at_lastThread`   the thread's own clause on its form, unpacked: the two records that the
      thread names as the earlier chains' last records hand on an f and an end e, and the library's
      public test on the records at the border 2 (`shapeAt`, Johnson/Desc/Last/ShapeAt.lean) says
      yes of f, e and the state.
  `order_at_ends`        so both earlier chains' last statements are in order.
  `samples_at_lastThread_joined`   **the sample rows of all members of the own group say of the
      words of which the thread's item "rows" speaks** (`wordsAtW`), at every continuation ds.
ALL ITS PREMISES beside the thread.
  hd: the head at the maker's return: it holds the library's one hypothesis on the public files at
    the full size, at the format's second hash function: A HYPOTHESIS, which the proof spends; this
    file builds no member of it.
  At the record that the thread names as the first chain's last:
    hFirst   the sample rows of the handed own group's members say of the words that THE FIRST
             CHAIN's OWN witness gives through that record's statement and book;
    hSeats   these members sit in trees of the first chain.
  At the record that the thread names as the shared chain's last (sh: what the shared thread takes
  from outside):
    hS       Omega's sample rows say of the words that THE SHARED CHAIN's OWN witness holds, read at
             a list hd' of challenges;
    hq       hd' and the list that the last chain's witness hands on have the same first member;
    ho, hseat, hx   Omega's number there is 2; by that record's book it sits at the seat that the
             shared chain's numbers give it, WHERE THE FIRST CHAIN's TREES ARE COUNTED AS THE PLAN
             COUNTS THEM; it has the plan's shape.

TWO STEPS BEHIND hFirst AND hS, not one, ARE SHOWN NEITHER IN THIS FILE NOR IN ANY FILE THAT IT
IMPORTS: that the pins hold at the two chains' ends
at a run; and, at the first chain, that a pin gives "the sample row says". And one tie that neither
this file nor any file that it imports has: that the records which the thread names (a free field of
what the last thread takes from
outside) are the two earlier threads' own last states. WHERE THE TWO EARLIER THREADS HOLD AT THEIR
LAST BORDERS, hSeats, ho, hseat, hx and hS follow: `samples_of_three_threads`
(LotWJointThreeThreads.lean of this folder), which does not call this statement; this one is wider:
it names no other thread, and the list hd' is free.

By what. `samples_at_lastThread_own` (LotWJointFirst.lean of this folder); `omega_samples`
(Johnson/Desc/ProofFile/Honest/K14/OmegaSamplesAtLastWitness.lean).

Limits. Neither this file nor any file that it imports shows that the thread holds at the border 2
at any run; neither this file nor
any file that it imports evaluates the public test at a record. One ds serves this clause, the
clause on the rows and the clause that
ties the words to the job's rows: the premises are to be shown at that ds. Nothing on
soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotWJointFirst
import Johnson.Desc.ProofFile.Honest.K14.OmegaSamplesAtLastWitness
import Johnson.Desc.Third.Law.Row0AtWords

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- The library's files on the full size switch this instance off; so must a file that names them.
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtFile.LotWJoint
open ProofFile.Honest
open OnBytes.Slice (rdE GE frS)
open OnBytes.Means (SampleSays sampleItem)
open VerifiableInference.Desc.Sound (wordsFirst seatBy noFirst noShared)
open VerifiableInference.Desc.Third (S₃ firstOfS sharedOfEnd)
open VerifiableInference.Desc.Last (shapeAt shapeAt_of_fill lastPlaces behindOk_of_two)
open VerifiableInference.Desc.K1 (qAt)
open Desc.K14.Honest (SmpOwn)
open ToldDesc (p14At)
open VerifierAndGoals.AtTheName (dpZ)
open ProofFile.Honest.K14 (omega_samples witL holds2 firstRv)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LastThreadParts
  SharedThreadParts lastThread lastWitness sentFirstOf sharedShape)

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  (hd : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
  (parts : LastThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **The thread's clause on its form, unpacked**: what the two named records hand on, and the
public test's yes at the border 2. -/
theorem ends_at_lastThread {k : Coins A.B} {st : S₃} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (u : Thr (lastThread hd first reads parts w) 2 k st m E) :
    ∃ f e, firstOfS (parts.ends k m.st.input
        (m.st.heard.take (lastThread hd first reads parts w).front)).1.2 = some f ∧
      Desc.K14.ended (parts.ends k m.st.input
        (m.st.heard.take (lastThread hd first reads parts w).front)).2 = some e ∧
      shapeAt (p14At A.Z) (LLT25.c2 hd.places).rounds 2 f (sharedOfEnd e) st = true := by
  have hform : (hd.lastForm.shape 2
      (parts.ends k m.st.input (m.st.heard.take (lastThread hd first reads parts w).front)).1
      (parts.ends k m.st.input (m.st.heard.take (lastThread hd first reads parts w).front)).2 st &&
      (!decide (lastPlaces.length ≤ 2) || hd.lastForm.nothingLeft st)) = true := u.2.2.1.1
  obtain ⟨f, o, hf, ho, hk⟩ := shapeAt_of_fill _ _ _ _ (Bool.and_eq_true _ _ ▸ hform).1
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 ho
  exact ⟨f, e, hf, he, hk⟩

/-- **Both earlier chains' last statements, as the thread names them, are in order.** -/
theorem order_at_ends {k : Coins A.B} {st : S₃} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (u : Thr (lastThread hd first reads parts w) 2 k st m E) :
    (∀ f, firstOfS (parts.ends k m.st.input
        (m.st.heard.take (lastThread hd first reads parts w).front)).1.2 = some f →
      OnBytes.Means.InOrder f.st) ∧
      OnBytes.Means.InOrder (parts.ends k m.st.input
        (m.st.heard.take (lastThread hd first reads parts w).front)).2.st := by
  obtain ⟨f, e, hf, he, hk⟩ := ends_at_lastThread hd first reads parts w u
  obtain ⟨⟨s₀, B⟩, -⟩ := behindOk_of_two hk
  refine ⟨fun f' hf' => ?_, ?_⟩
  · obtain rfl : f = f' := Option.some.inj (hf.symm.trans hf')
    exact B.handed.tidy.inOrder
  · have q := B.handed.order₂
    rw [VerifiableInference.Desc.Third.Law.sharedOfEnd_ended _ e he] at q
    exact q

/-- **IN FRONT OF THE TEST THE SAMPLE ROWS OF ALL MEMBERS OF THE OWN GROUP SAY OF THE WORDS OF THE
ITEM "rows"**: from the thread, and what the sample rows say at the two earlier chains' ends of
these chains' own witnesses. -/
theorem samples_at_lastThread_joined {Wt : Type} (sh : SharedThreadParts A Wt) {k : Coins A.B}
    {st : S₃} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (u : Thr (lastThread hd first reads parts w) 2 k st m E) (ds hd' : List Fmt.Drawn)
    (hFirst : ∀ f, firstOfS (parts.ends k m.st.input
        (m.st.heard.take (lastThread hd first reads parts w).front)).1.2 = some f →
      ∀ G, f.st.groups[f.own]? = some G → sampleItem rdE f.st G.members.toList
        (wordsFirst (P5J.At.arr A.Z) f.st f.book
          (first.script.wit k m.st.input (m.st.heard ++ ds))))
    (hSeats : ∀ f, firstOfS (parts.ends k m.st.input
        (m.st.heard.take (lastThread hd first reads parts w).front)).1.2 = some f →
      ∀ G, f.st.groups[f.own]? = some G → ∀ n ∈ G.members.toList,
        ∀ q, seatBy noFirst f.book n = some q → q.1 < hd.description.t₁)
    (hq : firstRv hd' = firstRv ((m.st.heard ++ ds).drop
      (declsTo hd.description.first.blocksInOrder hd.description.first.blocksInOrder.length).length))
    (ho : (parts.ends k m.st.input
        (m.st.heard.take (lastThread hd first reads parts w).front)).2.loc.oOmega = 2)
    (hseat : seatBy (noShared ((dpZ files).at frS.P.T.a).t₁) (parts.ends k m.st.input
        (m.st.heard.take (lastThread hd first reads parts w).front)).2.book 2 =
      some (hd.sharedNumbers.tenant .oOmega))
    (hx : ((parts.ends k m.st.input
        (m.st.heard.take (lastThread hd first reads parts w).front)).2.st.oracles[2]?).map
      (·.shape) = some (sharedShape A.Z hd.places .oOmega))
    (hS : SmpOwn 2 (parts.ends k m.st.input
        (m.st.heard.take (lastThread hd first reads parts w).front)).2
      (sh.lens.get (witL sh.lens (qAt A.Z hd.places) (sentFirstOf A.Z hd.places)
        (holds2 (qAt A.Z hd.places) reads.weights reads.rand) sh.rest k
        ⟨m.st.input.w₀, m.st.input.rc, A.H.key m.st.input.x⟩ hd'))) :
    ∀ G', st.st.groups[st.loc.own]? = some G' →
      sampleItem rdE st.st G'.members.toList
        (wordsAtW hd first reads st k m.st.input (m.st.heard ++ ds)) :=
  samples_at_lastThread_own hd first reads parts w u ds hFirst
    (fun f hf => ⟨(order_at_ends hd first reads parts w u).1 f hf, hSeats f hf⟩)
    (omega_samples hd first reads sh k m.st.input (m.st.heard ++ ds) hd' hq _ _
      (order_at_ends hd first reads parts w u).2 ho hseat hx hS)

end ProofFile.Honest.K12.AtFile.LotWJoint

#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.ends_at_lastThread
#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.order_at_ends
#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.samples_at_lastThread_joined
