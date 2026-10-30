-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotWJointSamplesAtShape.lean: the members' sample rows in
front of the last chain's proximity test, FROM THE YES OF THE LIBRARY's PUBLIC TEST ON THE RECORDS
AT THE BORDER 2 (`shapeAt`, Johnson/Desc/Last/ShapeAt.lean) AND WHAT THE SAMPLE ROWS SAY AT THE TWO
EARLIER CHAINS' ENDS. Statements on records with their proofs; no definition; no run, no coin.

The setting. f: what the first chain's last record hands on. o: the shared chain's end. s: the last
chain's record at the border 2. v: a witness.
  `says_of_laid`, `booked_of_behind`   what the test's yes holds (`BehindOk`,
      Johnson/Desc/Last/ShapeGives.lean) gives the two premises of LotWJointSamples.lean: the
      library's sentence on what the first block has laid, and its book-keeping; and that the record
      in front of that block has the first chain's last statement, book and own group.
  `codes_of_behind`    the record's table of codes is the plan's.
  `samples_of_shape`   **the sample rows of all members of the own group at s say of the words that
      v gives through s** (`wordsLast`, Johnson/Desc/Sound/WordsAt.lean), FROM TWO PREMISES:
        hFirst   at the first chain's end: the sample rows of the handed own group's members say of
                 the words that v gives through that chain's last statement and book (`wordsFirst`);
        hOmega   at the shared chain's end: Omega's sample rows say of the words that v gives
                 through that end (`wordsShared`).
  `samples_of_shape_own`   the same at `wordsAtOwn` at the plan's codes (LotWJoint.lean).

What the two premises are meant for. On the honest side a pin says that the witness's message has
the stored sample's answers; hFirst is meant as that sentence, in the rows' own words, of the two
members that the first chain hands on, hOmega of Omega. That is a reading: no statement here derives
either from a pin, so TWO steps behind each are not shown here: that the pin holds at the chain's
end, and
that a pin gives "the sample row says". Who the two members are is not said by the test: only that
there are two, each with one sample row.

Limits. Implications between records. Where the test says no they speak of nothing, and neither this
file nor any file that it imports evaluates the test at a record. They hold at every t₂: no member
sits in a tree of the last chain's
own. Nothing on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotWJoint
import Johnson.Desc.ProofFile.Honest.K12.AtFile.LotWJointSamples
import Johnson.Desc.Last.ShapeGives
import Johnson.Desc.Sound.ReadsAt
import Johnson.Desc.Third.Law.Row0Ev

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile.LotWJoint
open OnBytes (Group Oracle Part)
open OnBytes.Slice (rdE GE)
open OnBytes.Means (AllSay SampleSays sampleItem InOrder)
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.Sound (MsgT wordsLast wordsShared wordsFirst BookedLast words_first
  startIs)
open VerifiableInference.Desc.Third (S₃ SharedOut Border P₁₄ Laid)
open VerifiableInference.Desc.Third.Law (Says BookSays Sharp)
open VerifiableInference.Desc.Last (BehindOk shapeAt behindOk_of_two)
open VerifiableInference.Desc.Book (placed_of_fits)

/-- What the first block has laid, in the library's shorter sentence. -/
theorem says_of_laid {p : P₁₄} {s s' : S₃} {b : Border} {y : Oracle} {G : Group}
    {dot : OnBytes.Row} (L : Laid p.S s s' b y G dot) : Says p s s' :=
  ⟨b, y, G, dot, L.border, L.loc, L.there, L.sampled, L.size, L.copy, L.group, L.notBegun, L.dotIs,
    by rw [L.plain]; rfl, L.group', L.codes, L.old, L.oldGroups, L.groups⟩

/-- **What the test's yes holds gives the sentence on the block, its book-keeping, and that the
record in front of the block has what the first chain handed on.** -/
theorem booked_of_behind {p : P₁₄} {f : VerifiableInference.Desc.Last.Handed} {o : SharedOut}
    {s₀ s : S₃}
    (B : BehindOk p f o s₀ s) :
    Says p s₀ s ∧ BookedLast o s₀ s ∧ s₀.st = f.st ∧ s₀.book = f.book ∧ s₀.loc.own = f.own := by
  obtain ⟨b, y, G, dot, L⟩ := B.laid
  obtain ⟨e₁, e₂, hb, hf, hc, -⟩ := startIs _ _ _ _ _ _ _ _ _ _ _ B.start
  obtain ⟨q, t, tO, hq, ht, -, htO, hnum, hsrc⟩ := L.tree
  refine ⟨says_of_laid L, ⟨hb, hf, hc, ?_, ⟨L.roots, L.trees, L.places, L.place⟩, ?_,
    B.handed.tenant⟩, e₁, e₂, VerifiableInference.Desc.Third.Law.start_own _ _ _ _ _ _ _ _ _ _ _
      B.start⟩
  · exact ⟨b, q, t, (s₀.book.trees.size, 0), L.border, hq, ht, L.step, L.place, Nat.le_refl _,
      ⟨tO, htO, hnum, hsrc⟩, L.oldPlaces, L.oldTrees⟩
  · intro i q' hq'
    rw [e₂] at hq' ⊢
    exact placed_of_fits B.handed.fits₁ i q' hq'

/-- The record's table of codes is the plan's. -/
theorem codes_of_behind {p : P₁₄} {f : VerifiableInference.Desc.Last.Handed} {o : SharedOut}
    {s₀ s : S₃}
    (B : BehindOk p f o s₀ s) : s.st.codes = p.codes := by
  obtain ⟨_, _, _, _, L⟩ := B.laid
  obtain ⟨g, _, hst⟩ := VerifiableInference.Desc.Third.Law.start₃E_inv _ _ _ _ _ _ _ _ _ _ _ B.start
  obtain ⟨c1, _, e0⟩ := VerifiableInference.Desc.Third.Law.start₃_inv _ _ _ _ hst
  rw [L.codes, e0]
  exact c1

variable {Cells Tok : Type} (arr : ℕ → ℕ → ℕ) (t₁ t₂ : ℕ) {p : P₁₄} {R : List Fmt.DeclaredRound}
  {f : VerifiableInference.Desc.Last.Handed} {o : SharedOut} {s : S₃} (v : Wit Cells Tok MsgT)

/-- **IN FRONT OF THE TEST THE SAMPLE ROWS OF ALL MEMBERS OF THE OWN GROUP SAY OF THE WORDS THROUGH
THE RECORD**: from the public test's yes at the border 2 and what the sample rows say at the two
earlier chains' ends. -/
theorem samples_of_shape (hk : shapeAt p R 2 f o s = true)
    (hFirst : ∀ G, f.st.groups[f.own]? = some G →
      sampleItem rdE f.st G.members.toList (wordsFirst arr f.st f.book v))
    (hOmega : SampleSays rdE o.st o.omega (wordsShared arr t₁ o.st o.book v)) :
    ∀ G', s.st.groups[s.loc.own]? = some G' →
      sampleItem rdE s.st G'.members.toList (wordsLast arr t₁ t₂ s v) := by
  obtain ⟨⟨s₀, B⟩, -⟩ := behindOk_of_two hk
  obtain ⟨hS, hB, e₁, e₂, e₃⟩ := booked_of_behind B
  have ew : wordsLast arr t₁ t₂ s₀ v = wordsFirst arr f.st f.book v := by
    funext n part i
    rw [words_first arr t₁ t₂ o s₀ s hB v n part i, e₁, e₂]
  refine samples_behind arr t₁ t₂ p o s₀ s v hS hB (by rw [e₁]; exact B.handed.tidy.inOrder)
    B.handed.order₂ (fun G hG => ?_) hOmega
  rw [ew, e₁]
  rw [e₁, e₃] at hG
  exact hFirst G hG

/-- The same at the words of which the library's sentence for the item "rows" speaks, at the plan's
codes. -/
theorem samples_of_shape_own (hk : shapeAt p R 2 f o s = true)
    (hFirst : ∀ G, f.st.groups[f.own]? = some G →
      sampleItem rdE f.st G.members.toList (wordsFirst arr f.st f.book v))
    (hOmega : SampleSays rdE o.st o.omega (wordsShared arr t₁ o.st o.book v)) :
    ∀ G', s.st.groups[s.loc.own]? = some G' →
      sampleItem rdE s.st G'.members.toList (wordsAtOwn p.codes arr t₁ t₂ s v) := by
  obtain ⟨⟨s₀, B⟩, -⟩ := behindOk_of_two hk
  rw [← codes_of_behind B, wordsAtOwn_is_wordsLast]
  exact samples_of_shape arr t₁ t₂ v hk hFirst hOmega

end ProofFile.Honest.K12.AtFile.LotWJoint

#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.says_of_laid
#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.booked_of_behind
#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.codes_of_behind
#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.samples_of_shape
#print axioms ProofFile.Honest.K12.AtFile.LotWJoint.samples_of_shape_own
