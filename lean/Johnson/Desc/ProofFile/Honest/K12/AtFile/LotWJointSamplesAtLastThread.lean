-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotWJointSamplesAtLastThread.lean: the members' sample rows
in front of the last chain's proximity test AT THE LAST THREAD AS IT IS WRITTEN (`lastThread`,
Johnson/Desc/ProofFile/Honest/Thread/TheFirstThread.lean). One statement with its proof; no
definition. "The thread at the border 2": the invariant `Thr` of that thread in front of the test,
a premise.

`samples_at_lastThread`: at the thread at the border 2, at every continuation ds of the challenges:
**the sample rows of all members of the own group say of the words of which the thread's item "rows"
speaks** (`wordsAtW`, LotWJointAtLastThread.lean of this folder): the clause on the members' sample
rows that the test's acceptance asks, at the same words as the clause on the rows
(`rows_at_lastThread`). ALL ITS PREMISES beside the thread:
  hFirst   at what the first chain's last record hands on, as the thread names that record: the
           sample rows of the handed own group's members say of the words that the thread's witness
           gives through that chain's last statement and book;
  hOmega   at the shared chain's end, as the thread names it: Omega's sample rows say of the words
           that the thread's witness gives through that end, WHERE THE FIRST CHAIN's TREES ARE
           COUNTED AS THE PLAN COUNTS THEM (the count that the thread's item "rows" has). The
           thread's witness lays Omega's table at the seat that the shared chain's numbers give,
           and the thread's own count of trees is the description's: three texts for one number;
           no statement here ties them, and where they part hOmega cannot be met.
Both stand at the same ds as the end.
The thread's own clause on its form pays the rest: the library's public test on the records at the
border 2 says yes there (`samples_of_shape_own`, LotWJointSamplesAtShape.lean).

What the two premises are meant for: the three pins that are open at this border, in the rows' own
words. That is a reading. The thread takes the meaning of its pins from outside (the field `meaning`
of what the last thread takes), as it takes the two records that it names, so nothing here derives
the two from the thread's items: TWO steps behind each are not shown here: that the pin holds at the
chain's
end, and that a pin gives "the sample row says".

Limits. Neither this file nor any file that it imports shows that the thread holds at the border 2
at any run. The two premises are shown neither here nor in any file that this one imports. Nothing
on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotWJointAtLastThread
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotWJointSamplesAtShape
import Johnson.Desc.Last.ShapeAtTable
import Johnson.Desc.Last.ShapeRowZero

set_option autoImplicit false
set_option relaxedAutoImplicit false

-- The library's files on the full size switch this instance off; so must a file that names them.
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K12.AtFile.LotWJoint
open ProofFile.Honest
open OnBytes.Slice (rdE GE frS)
open OnBytes.Means (SampleSays sampleItem)
open VerifiableInference.Desc.Sound (wordsFirst wordsShared)
open VerifiableInference.Desc.Third (S₃ firstOfS sharedOfEnd)
open VerifiableInference.Desc.Last (shapeAt_of_fill lastPlaces)
open ToldDesc (p14At)
open VerifierAndGoals.AtTheName (dpZ)
open ProofFile.Honest.FirstThread (HeadAtReturn FirstThreadParts IndexReaders LastThreadParts lastThread
  lastWitness)

variable {W₀ Rc Tr X₀ X : Type} {files : VerifierAndGoals.PublicFiles} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
  (hd : HeadAtReturn files A) (first : FirstThreadParts A) (reads : IndexReaders W₀ Rc)
  (parts : LastThreadParts A) (w : Local W₀ Rc ProofFile.Inst Tr)

/-- **IN FRONT OF THE TEST THE SAMPLE ROWS OF ALL MEMBERS OF THE OWN GROUP SAY OF THE WORDS OF THE
ITEM "rows"**, at every continuation of the challenges: from the thread, and what the sample rows
say at the two earlier chains' ends. -/
theorem samples_at_lastThread {k : Coins A.B} {st : S₃} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {E : Env} (u : Thr (lastThread hd first reads parts w) 2 k st m E) (ds : List Fmt.Drawn)
    (hFirst : ∀ f, firstOfS (parts.ends k m.st.input
        (m.st.heard.take (lastThread hd first reads parts w).front)).1.2 = some f →
      ∀ G, f.st.groups[f.own]? = some G → sampleItem rdE f.st G.members.toList
        (wordsFirst (P5J.At.arr A.Z) f.st f.book
          (lastWitness hd first reads k m.st.input (m.st.heard ++ ds))))
    (hOmega : ∀ e, Desc.K14.ended (parts.ends k m.st.input
        (m.st.heard.take (lastThread hd first reads parts w).front)).2 = some e →
      SampleSays rdE (sharedOfEnd e).st (sharedOfEnd e).omega
        (wordsShared (P5J.At.arr A.Z) ((dpZ files).at frS.P.T.a).t₁ (sharedOfEnd e).st
          (sharedOfEnd e).book (lastWitness hd first reads k m.st.input (m.st.heard ++ ds)))) :
    ∀ G', st.st.groups[st.loc.own]? = some G' →
      sampleItem rdE st.st G'.members.toList
        (wordsAtW hd first reads st k m.st.input (m.st.heard ++ ds)) := by
  have hform : (hd.lastForm.shape 2
      (parts.ends k m.st.input (m.st.heard.take (lastThread hd first reads parts w).front)).1
      (parts.ends k m.st.input (m.st.heard.take (lastThread hd first reads parts w).front)).2 st &&
      (!decide (lastPlaces.length ≤ 2) || hd.lastForm.nothingLeft st)) = true := u.2.2.1.1
  obtain ⟨f, o, hf, ho, hk⟩ := shapeAt_of_fill _ _ _ _ (Bool.and_eq_true _ _ ▸ hform).1
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 ho
  exact samples_of_shape_own (P5J.At.arr A.Z) _ _ _ hk (hFirst f hf) (hOmega e he)

end ProofFile.Honest.K12.AtFile.LotWJoint

#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.samples_at_lastThread
