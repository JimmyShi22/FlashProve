-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotWJointSamples.lean: the joint between the last chain's
first block ("K14, second part") and that chain's proximity test: THE MEMBERS' SAMPLE ROWS. What the
stored sample rows of the own group's members say in front of the block, and what Omega's say at the
shared chain's end, they say behind the block, of the words that the same witness gives through the
record behind. Statements on records with their proofs; no definition; no run, no coin.

The setting. s, s': the last chain's record in front of the block and behind it, under the library's
sentence on what the block has laid (`Says p s s'`, Johnson/Desc/Third/Law/Says.lean) and its
book-keeping (`BookedLast o s s'`, Johnson/Desc/Sound/WordsAt.lean); o: the shared chain's end. v: a
witness. The words: `wordsLast` through a record of the last chain, `wordsShared` through the shared
chain's end (WordsAt.lean).
  `sample_older`    a message n that was there in front: if its sample rows say of the words through
                    s, they say of the words through s'. Asks that the statement in front is in
                    order.
  `sample_omega`    Omega's copy, at the next free number: if Omega's sample rows at the shared
                    chain's end say of the words through that end, the copy's say of the words
                    through s'. Asks that the shared chain's last statement is in order.
  `samples_behind`  **both together, at every member of the own group behind the block**: the clause
                    on the members' sample rows that the test's acceptance asks, at the library's
                    words.

By what. An older message is the same record behind (`old_message_back`), a sample row of a
statement in order is on its own message (`InOrder.samples`), such a row says behind what it says in
front (`rows_back`) and reads the words of that message alone (`says_agree`), which are the same
through both records (`words_older`). Omega's copy holds Omega's sample rows under the new number;
what a renamed row says: `says_renamed`; the words: `words_omega`.

Limits. Implications between records. That any sample row says its claim of any words is a premise
here. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.Sound.WordsAt
import Johnson.Desc.Third.Law.Back
import Johnson.Desc.Third.Law.Renamed
import Johnson.Desc.Key.KeyRowAgree
import Johnson.Desc.Means.ItemsRead
import Johnson.Desc.Means.ItemsAt
import OnBytes.Slice.BlkRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile.LotWJoint
open OnBytes (Group Oracle Part)
open OnBytes.Slice (rdE GE)
open OnBytes.Means (AllSay SampleSays sampleItem InOrder RowOn says_agree)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound (MsgT wordsLast wordsShared BookedLast words_older words_omega)
open VerifiableInference.Desc.Third (S₃ SharedOut Border P₁₄)
open VerifiableInference.Desc.Third.Law (Says rows_back old_message_back says_renamed
  tableSize_same)

variable {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (t₁ t₂ : ℕ) (p : P₁₄) (o : SharedOut) (s s' : S₃)
  (v : Wit Cells Tok MsgT)

/-- **A message that was there in front**: what its sample rows say of the words through the record
in front, they say of the words through the record behind. -/
theorem sample_older (h : Says p s s') (hB : BookedLast o s s') (hI : InOrder s.st) (n : ℕ)
    (hn : n < s.st.oracles.size) (hs : SampleSays rdE s.st n (wordsLast arr t₁ t₂ s v)) :
    SampleSays rdE s'.st n (wordsLast arr t₁ t₂ s' v) := by
  intro x hx r hr
  rw [old_message_back p s s' h n hn] at hx
  have hOn : RowOn s.st n r := hI.samples n x hx r hr
  refine (rows_back rdE p s s' h _ r hOn _).2 ?_
  refine (says_agree rdE hOn fun n' hn' part i => ?_).1 (hs x hx r hr)
  obtain rfl : n' = n := by simpa using hn'
  exact (words_older arr t₁ t₂ p o s s' h hB v n' hn part i).symm

/-- **Omega's copy**: what Omega's sample rows say at the shared chain's end of the words through
that end, the copy's say of the words through the record behind. -/
theorem sample_omega (h : Says p s s') (hB : BookedLast o s s') (hI : InOrder o.st)
    (hs : SampleSays rdE o.st o.omega (wordsShared arr t₁ o.st o.book v)) :
    SampleSays rdE s'.st s.st.oracles.size (wordsLast arr t₁ t₂ s' v) := by
  have h' : Says p s s' := h
  obtain ⟨g, hg⟩ := hB.border
  obtain ⟨b, y, _, _, hb, _, hy, _, _, hO, _, _, _, _, _, hc, _, _, _⟩ := h
  obtain rfl : (⟨g, o⟩ : Border) = b := Option.some.inj (hg.symm.trans hb)
  intro x hx r' hr'
  rw [hO] at hx
  obtain rfl := Option.some.inj hx
  simp only [Array.toList_map, List.mem_map] at hr'
  obtain ⟨r, hr, rfl⟩ := hr'
  have ho : o.omega < o.st.oracles.size := (Array.getElem?_eq_some_iff.1 hy).1
  have hn : s.st.oracles.size < s'.st.oracles.size := (Array.getElem?_eq_some_iff.1 hO).1
  have alone : ∀ z ∈ r.oracles, z = o.omega := fun z hz => by
    have q := VerifiableInference.Desc.Key.names_of_rowIn (hI.samples o.omega y hy r hr) z hz
    simpa using q
  exact (says_renamed rdE o.st s'.st r o.omega s.st.oracles.size ho hn alone
    (tableSize_same o.st s'.st _ _ y _ hy hO rfl (hc.trans hB.codes.symm))
    (wordsShared arr t₁ o.st o.book v) (wordsLast arr t₁ t₂ s' v)
    (fun pt i => words_omega arr t₁ t₂ p o s s' h' hB v pt i)).2 (hs y hy r hr)

/-- **BEHIND THE BLOCK THE SAMPLE ROWS OF ALL MEMBERS OF THE OWN GROUP SAY OF THE WORDS THROUGH THE
RECORD BEHIND**: from the same in front, and Omega's at the shared chain's end. -/
theorem samples_behind (h : Says p s s') (hB : BookedLast o s s') (hI : InOrder s.st)
    (hIo : InOrder o.st)
    (hold : ∀ G, s.st.groups[s.loc.own]? = some G →
      sampleItem rdE s.st G.members.toList (wordsLast arr t₁ t₂ s v))
    (hΩ : SampleSays rdE o.st o.omega (wordsShared arr t₁ o.st o.book v)) :
    ∀ G', s'.st.groups[s'.loc.own]? = some G' →
      sampleItem rdE s'.st G'.members.toList (wordsLast arr t₁ t₂ s' v) := by
  have h' : Says p s s' := h
  obtain ⟨b, y, G, dot, _, hl, _, _, hsz, _, hG, _, _, _, hg', _⟩ := h
  intro G' hG' n hn
  have eo : s'.loc.own = s.loc.own := by rw [hl]
  rw [eo, hg'] at hG'
  obtain rfl := Option.some.inj hG'
  have hpos : (G.members.filter (· < s.st.oracles.size)).size ≤ G.members.toList.length := by
    rw [Array.length_toList]
    exact Array.size_filter_le
  have hn' : n ∈ (G.members.insertIdxIfInBounds
      (G.members.filter (· < s.st.oracles.size)).size s.st.oracles.size).toList := hn
  rw [OnBytes.Means.toList_insertIdxIfInBounds] at hn'
  rcases (List.mem_insertIdx hpos).1 hn' with rfl | hm
  · exact sample_omega arr t₁ t₂ p o s s' v h' hB hIo hΩ
  · exact sample_older arr t₁ t₂ p o s s' v h' hB hI n ((hI.groups _ _ hG).there n hm)
      (hold G hG n hm)

end ProofFile.Honest.K12.AtFile.LotWJoint

#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.sample_older
#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.sample_omega
#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.samples_behind
