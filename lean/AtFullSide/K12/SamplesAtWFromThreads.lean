-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/SamplesAtWFromThreads.lean: the members' sample rows in front of the last chain's
proximity test, from the three chains' threads as they are written (`firstThread`, `sharedThread`,
`lastThread`, Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean): `samples_of_three_threads`
(Johnson/Desc/ProofFile/Honest/K12/AtFile/LotWJointThreeThreads.lean) WITH ITS PREMISE AT THE FIRST
CHAIN's END PAID FROM THE FIRST THREAD's TWO PINS. One statement with its proof; no definition.

`samples_at_W_from_threads`: **the sample rows of all members of the own group say of the words of
which the last thread's item "rows" speaks** (`wordsAtW`), at every continuation ds of the
challenges. ALL ITS PREMISES. "A thread holds at a border": its invariant `Thr` there, at one run's
coins k, the same in all three.
  hd    the head at the maker's return: it holds the library's one hypothesis on the public files at
        the full size, at the format's second hash function: A HYPOTHESIS, which the proof spends;
        this file builds no member of it;
  u, u₁, u₂   the last thread holds in front of the test (the border 2); the first and the shared
        thread hold at their chains' last borders, at states e₁ and e₂;
  THE TIE OF THE THREE RUNS, six equations:
    he₁, he₂   the two records that the last thread names as the earlier chains' last are e₁, e₂;
    hi₁, hh₁   the first thread's run has the last thread's run's input, and what the last thread's
               run has heard begins with what the first thread's run has heard (rest: what follows);
    hin, hq    the shared thread's run has the input that is made of the last thread's run's, and
               the first challenge that it has heard is the first behind the first chain's;
  TWO PUBLIC TESTS ON e₁:
    hRc   e₁ passes the library's tests on the first chain's last state (`rcLastB`,
          Johnson/ToldDescR/RcLastCode.lean: the book is in order and fits; the own group's two
          members sit at the plan's two seats; each has one sample row that the sample's own test
          accepts; the seats are the written ones), AT THESE VALUES: the two seats and shapes off
          the plan, the written list of seats, and e₁'s OWN table of codes;
    hc    e₁'s table of codes is the plan's.

By what. The two pins at the first thread's last border (`pins_at_last_run`,
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotWJointPins.lean); from a pin's equation to "the sample
row says" (`samples_of_rc_seats`, AtFullSide/K1/SamplesAtEnd.lean), with four public facts on the
plan, which hold under the head (AtFullSide/K1/SamplesPublic.lean).

WHAT THIS FILE DOES NOT SHOW: the tie; and that any of the three threads holds at these borders at a
run. hRc and hc
are shown one file on, where the first thread holds TOGETHER WITH the sentence that every word shown
is below the field's prime (`samples_at_W_from_stands`, SamplesAtWFromStands.lean of this folder). A
reading, no theorem: the library's proof of hRc goes by steps that test all words shown, sent ones
and opened columns too, which is more than the invariant says; whether the invariant alone gives hRc
is not settled here.

Limits. One ds serves this clause, the clause on the rows and the clause that ties the words to the
job's rows. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotWJointThreeThreads
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotWJointPins
import AtFullSide.K1.SamplesAtEnd
import AtFullSide.K1.SamplesPublic

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
open ToldDesc (rcLastB)
open ProofFile.Honest.K14 (firstRv)
open ProofFile.Honest.K1 (samples_of_rc_seats laid_places_seats seats_nodup sits_index_shape sits_w_shape)
open ProofFile.Honest.K12.AtFile.LotWJoint (samples_of_three_threads pins_at_last_run wordsAtW)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LastThreadParts
  SharedThreadParts firstThread sharedThread lastThread)

variable {W₀ Rc Tr X₀ X Wt : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  (hd : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
  (sh : SharedThreadParts A Wt) (parts : LastThreadParts A) (w w₁ : Local W₀ Rc ProofFile.Inst Tr)
  (w₂ : Common W₀ Rc OnBytes.TableKey)

/-- **IN FRONT OF THE LAST CHAIN's TEST THE SAMPLE ROWS OF ALL MEMBERS OF THE OWN GROUP SAY OF THE
WORDS OF THE ITEM "rows"**: from the three threads, the tie of their runs, and two public tests on
the first chain's last state. -/
theorem samples_at_W_from_threads {k : Coins A.B} {st : S₃}
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
    (hi₁ : m₁.st.input = m.st.input) (rest : List Fmt.Drawn)
    (hh₁ : m.st.heard = m₁.st.heard ++ rest)
    (hin : m₂.st.input = ⟨m.st.input.w₀, m.st.input.rc, A.H.key m.st.input.x⟩)
    (hq : firstRv m₂.st.heard = firstRv ((m.st.heard ++ ds).drop
      (declsTo hd.description.first.blocksInOrder hd.description.first.blocksInOrder.length).length))
    (hRc : rcLastB 0 (LLT25.vAt A.Z hd.head.𝔇.N) VerifiableInference.Desc.K13.Law.LFull
      e₁.st.codes e₁ = true)
    (hc : e₁.st.codes = P5J.At.cs A.Z) :
    ∀ G', st.st.groups[st.loc.own]? = some G' →
      sampleItem rdE st.st G'.members.toList
        (wordsAtW hd first reads st k m.st.input (m.st.heard ++ ds)) := by
  obtain ⟨pI, pV⟩ := pins_at_last_run hd first w₁ u₁ m.st.input (m.st.heard ++ ds) (rest ++ ds) hi₁
    (by rw [hh₁, List.append_assoc])
  refine samples_of_three_threads hd first reads sh parts w w₁ w₂ u ds u₁ u₂ he₁ he₂ hin hq
    fun f hf G hG => ?_
  refine samples_of_rc_seats (P5J.At.arr A.Z) (p := m.st.input.x.pub) (seats := P5J.At.seats A.Z)
    (ms := P5J.At.ms A.Z files.lay) hRc _ ((firstThread hd first w₁).strs E₁) ?_ ?_
    (laid_places_seats hd.head) (seats_nodup hd.head) (sits_index_shape hd.head)
    (sits_w_shape hd.head) hf hG
  · rw [hc]
    exact pI
  · rw [hc]
    exact pV

end AtFullSide.K12

#print axioms AtFullSide.K12.samples_at_W_from_threads
