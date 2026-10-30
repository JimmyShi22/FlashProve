-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K12/SamplesAtWFromStands.lean: the members' sample rows in front of the last chain's
proximity test: `samples_at_W_from_threads` (SamplesAtWFromThreads.lean of this folder) WITH ITS TWO
PUBLIC TESTS ON THE FIRST CHAIN's LAST STATE PAID. One statement with its proof; no definition.

`samples_at_W_from_stands`: **the sample rows of all members of the own group say of the words of
which the last thread's item "rows" speaks** (`wordsAtW`,
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotWJointAtLastThread.lean), at every continuation ds of
the challenges. It is the clause on the members' sample rows that the test's acceptance asks. ALL
ITS PREMISES. The three threads are `firstThread`, `sharedThread`, `lastThread`
(Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean); "a thread holds at a border": its
invariant `Thr` there, at one run's coins k, the same in all three.
  hd    the head at the maker's return: it holds the library's one hypothesis on the public files at
        the full size, at the format's second hash function: A HYPOTHESIS, which the proof spends;
        this file builds no member of it;
  u     the last thread holds in front of the test (the border 2);
  u₁    the first thread holds at its chain's last border, at a state e₁, TOGETHER WITH a sentence
        Said₁ on the run (the pair `ThrS`);
  hSaid   Said₁ gives that every word which the rounds seen show is below the field's prime
        (`SaidOk`, Johnson/Desc/ProofFile/Honest/Thread/SaidOk.lean; the same file carries that
        sentence past every member of every thread);
  u₂    the shared thread holds at its chain's last border, at a state e₂;
  THE TIE OF THE THREE RUNS, six equations:
    he₁, he₂   the two records that the last thread names as the earlier chains' last are e₁, e₂;
    hi₁, hh₁   the first thread's run has the last thread's run's input, and what the last thread's
               run has heard begins with what the first thread's run has heard (rest: what follows);
    hin, hq    the shared thread's run has the input that is made of the last thread's run's, and
               the first challenge that it has heard is the first behind the first chain's.
BESIDE hd AND THE THREE THREADS' INVARIANTS NO PREMISE OF ITS OWN ON A SAMPLE ROW, A PIN, A SEAT, A
SHAPE OR A CODE IS LEFT. (The two pins are two of the items that the first thread's invariant holds
open at its last border; hd holds the public tests on the plan's seats, shapes and codes.)

By what. `rc_at_stand` (AtFullSide/K1/RcAtStand.lean): at such a pair the state passes the library's
tests on the first chain's last state, and its table of codes is the plan's.

WHAT THIS FILE DOES NOT SHOW: the tie; and that the three threads hold at these borders at a run.
Four of the six
equations and the two earlier stands are moved into one sentence on the last thread's run in
`samples_at_W_of_tied` (SamplesAtWTied.lean of this folder); he₁, he₂ stay a premise beside it.

Limits. One ds serves this clause, the clause on the rows and the clause that ties the words to the
job's rows. Nothing on soundness, completeness or hiding.
-/
import AtFullSide.K12.SamplesAtWFromThreads
import AtFullSide.K1.RcAtStand

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
open ProofFile.Honest.K14 (firstRv)
open ProofFile.Honest.K1 (rc_at_stand)
open ProofFile.Honest.K12.AtFile.LotWJoint (wordsAtW)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LastThreadParts
  SharedThreadParts firstThread sharedThread lastThread)

variable {W₀ Rc Tr X₀ X Wt : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  (hd : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
  (sh : SharedThreadParts A Wt) (parts : LastThreadParts A) (w w₁ : Local W₀ Rc ProofFile.Inst Tr)
  (w₂ : Common W₀ Rc OnBytes.TableKey)

/-- **IN FRONT OF THE LAST CHAIN's TEST THE SAMPLE ROWS OF ALL MEMBERS OF THE OWN GROUP SAY OF THE
WORDS OF THE ITEM "rows"**: from the three threads, the first with "every word shown is below the
prime" beside it, and the tie of their runs. -/
theorem samples_at_W_from_stands
    (Said₁ : Nat → Coins A.B → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hSaid : ∀ b k m, Said₁ b k m → SaidOk b k m) {k : Coins A.B} {st : S₃}
    {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (u : Thr (lastThread hd first reads parts w) 2 k st m E) (ds : List Fmt.Drawn)
    {e₁ : TS} {m₁ : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E₁ : Env}
    (u₁ : ThrS (firstThread hd first w₁) Said₁ hd.firstChain.blocksInOrder.length k e₁ m₁ E₁)
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
      (declsTo hd.description.first.blocksInOrder hd.description.first.blocksInOrder.length).length)) :
    ∀ G', st.st.groups[st.loc.own]? = some G' →
      sampleItem rdE st.st G'.members.toList
        (wordsAtW hd first reads st k m.st.input (m.st.heard ++ ds)) := by
  obtain ⟨hRc, hc⟩ := rc_at_stand hd.head A.H first.script _ _ _ _ _ _ _ _ _ w₁ Said₁ hSaid u₁
  exact samples_at_W_from_threads hd first reads sh parts w w₁ w₂ u ds u₁.1 u₂ he₁ he₂ hi₁ rest hh₁
    hin hq hRc hc

end AtFullSide.K12

#print axioms AtFullSide.K12.samples_at_W_from_stands
