-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/LockOfBook.lean: CONDITIONAL. Five statements with their
proofs.

What is here. THE LOCKS OF THE MEMBER OF THE FEED-FORWARD LAYERS' OWN ROUNDS (sub-protocol K4), FROM
THE LAWS ON THE BOOK THAT ITS MAKER RETURNS. Where `bookWhole` (Honest/BookWhole.lean, of other
writers) returns a book B, b is a member of the first chain in link l, the plan's parts of b are
K4's row part for part (`K4RowIsPlan`, Law/W/RowIsPlanForm.lean, of another writer), and B lends
K4's row (hB): (1) `k4Lock_of_bookWhole`: THE WHOLE LOCK `K4MaskLock` (Law/W/MaskLock.lean) HOLDS AT
THE MAKER's OWN LETTERS: the stretch's owner is row.owner, its base row.base.e, its first place the
number of own scalars of the segment's parts in front of b (`ownScalarsOf`, `partsInFront`,
Honest/BookRowKit.lean); the last entry is the merge's entry of the index-mask message; row and idx
are what `ownerOf` (Honest/BookEntries.lean) returns for the two messages. (2)
`k4MaskLockAt_of_bookWhole`: so the mask row's name `K4MaskLockAt` (Law/W/MaskLockAt.lean) holds at
(row.owner, row.base.e), where e is that number of scalars (he). (3) `k4LastEntryAt_of_bookWhole`
(of another writer): and the index side's name `K4LastEntryAt` (Law/W/IndexLockAt.lean) holds at
(idx.owner, idx.base.e + t), t the end values of the merges in front (`mergeEndsOf`, `linksInFront`,
Honest/BookMergeStretch.lean). (4) `k4Names_of_bookWhole`: BOTH NAMES AT ONCE, WITH NO HYPOTHESIS
THAT THE BOOK LENDS: hB gives way to hd and hca: the book's first table gives the addresses of K4's
parts no coin of their own (no row, or a row of the count 0), and the book has no carried entry
there; he as in (2). (5) `k4Names_whole`: THE SAME END WITH NO HYPOTHESIS ON WHAT THE BOOK HOLDS AT
K4's ADDRESSES: hd and hca give way to hS: no round of b is named "SEND seed": a fact on the plan's
block.

How. (1): one call of `bookWhole_merge_stretch` (Honest/BookMergeStretch.lean, of other writers) at
a row whose last part is the merge, with nothing behind it; its two equations are the lock's fields
ents and stretch; the field one is `K4RowIsPlan.one`; the field lends is hB. (2): (1) and he. (3):
(1)'s field last, and the text of `Want.entry` (Honest/BookEntries.lean). (4): (1), with hB by
`k4_lends_of_bookWhole` (Law/W/LendsOfBook.lean, of another writer). (5): (1), with hB by
`k4_lends_whole` (the same file).

Not shown here. THAT `bookWhole` RETURNS AT ANY FILES OF THE FULL SIZE: h is a hypothesis, and so is
hp. `K4RowIsPlan`: its own file says what is shown of it; ITS FIELDS front AND merge ARE FACTS ON
THE LETTER M, which says which parts are merges: nothing compares M with the format (the limit of
Honest/BookMergeStretch.lean). At the list that the honest prover's book takes (`mergesByName`,
Honest/BookWhole.lean; Honest/AtPure.lean calls `bookWhole` at it) the two are not shown here. hB:
`k4_lends_of_bookWhole` (Law/W/LendsOfBook.lean) has it from h, hp, hb, hl, R, hd and hca: so (4).
hd AND hca: (5) does not ask them: `bookWhole_bare_at` (Honest/Small/BareOfBook.lean, of another
writer) has them from h, hp, hb, hS and the field noFold. hS: shown nowhere here. he: that the
maker's count of the scalars in front of K4's row is the verifier's side's number of the lookup's
scalars: shown nowhere here. THAT THE MAKER's LETTERS ARE THE SENDERS': that row.owner and
row.base.e are the letters at which the sender's sentence hE of Law/W/MaskLockAt.lean is had; that
idx.owner and idx.base.e are the letters of the index-mask message's sender, and that t is the
number at which K4's text reads that message (`k4IndexTakes`, Lot/IndexNum.lean: the sentence hE of
Law/W/IndexLockAt.lean stands there): shown nowhere here. LEFT OF THE JOIN: every hypothesis named
above, he among them; that the maker's letters are the senders'; and the two sentences hE
themselves. THIS IS THE ROAD BY LAWS; the other road is to evaluate the named tests
(`k4MaskLockAtB`) at the maker's written book, one evaluation a group: not tried here. NEVER TO BE
SAID FROM THIS FILE: «K4's coins are the sender's» as had · «lock and key fit» («as had»: as a thing
that is shown). Of the hypotheses together no example is known to us. A program's walk from import
to import, which
reads import lines alone and stops unopened at Johnson/Goal/, ThirdParty/, Johnson/D/,
Johnson/Bridge/ and Cb/Bridge*, stopped at 74 modules under Johnson/Goal/, at 7 under
Johnson/Bridge/ and at 1 that begins Cb.Bridge: floors. A LAW, NOT A PART: no file that defines a
part of the proof file's description may import this one. Nothing on soundness, on completeness or
on any other property. No property is claimed.

  `k4Lock_of_bookWhole`   **the whole lock, at the maker's own letters**
  `k4MaskLockAt_of_bookWhole`   the mask row's name from the book's laws
  `k4LastEntryAt_of_bookWhole`   the index side's name from the book's laws
  `k4Names_of_bookWhole`   **both names, with no hypothesis that the book lends**
  `k4Names_whole`   **both names, with no hypothesis on what the book holds at K4's addresses**
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.MaskLockAt
import Johnson.Desc.ProofFile.Honest.K4.Law.W.IndexLockAt
import Johnson.Desc.ProofFile.Honest.K4.Law.W.RowIsPlanForm
import Johnson.Desc.ProofFile.Honest.K4.Law.W.LendsOfBook
import Johnson.Desc.ProofFile.Honest.BookMergeStretch

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.W
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Block FileDescription Place)

variable {Xi : Type} {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {B : ProverCoinCounts}
  {b : Block F.S₁ F.Cl} {l : ℕ} {Q : K4Pub} {A : List PartAt} {m : PartAt}

/-- CONDITIONAL on h, hp, hb, hl, R and hB. **THE WHOLE LOCK, AT THE MAKER's OWN LETTERS**: row and
idx are what `ownerOf` returns. -/
theorem k4Lock_of_bookWhole (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    (hb : b ∈ F.first.blocksInOrder) (hl : b.place.link = some l) (R : K4RowIsPlan M b Q A m)
    (hB : lendsRow B 0 (k4Place Q) (k4RowIn Q) = true) :
    ∃ row idx es₁,
      ownerOf maskRowRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds))
        s!"link {l}, moment 0" isMaskRowMsg = some row ∧
      ownerOf indexMaskRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
        isIndexMaskMsg = some idx ∧
      K4MaskLock B Q (ownScalarsOf (partsInFront F.first.blocksInOrder l b.place)) es₁
        (⟨m.addr, "ends", idx, mergeEndsOf M.ends (linksInFront F.first.blocksInOrder l ++
          partsInFront F.first.blocksInOrder l b.place), m.endScalars⟩ : Want).entry
        row.owner row.base.e (ownScalarsOf A + (m.ownScalars - m.endScalars)) := by
  obtain ⟨row, idx, es₁, hr, hi, he, hs⟩ :=
    bookWhole_merge_stretch h hp hb hl R.noFold (C := []) R.row R.front R.merge R.sum
      (by rw [R.one]; exact Nat.one_ne_zero) (by intro p hp'; cases hp') R.pos
  refine ⟨row, idx, es₁, hr, hi, ⟨hB, ?_, R.one⟩, hs⟩
  rw [← R.place, ← R.len]
  exact he

/-- CONDITIONAL on h, hp, hb, hl, R, hB and he. **THE MASK ROW's NAME FROM THE BOOK's LAWS.** -/
theorem k4MaskLockAt_of_bookWhole (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    (hb : b ∈ F.first.blocksInOrder) (hl : b.place.link = some l) (R : K4RowIsPlan M b Q A m)
    (hB : lendsRow B 0 (k4Place Q) (k4RowIn Q) = true) {e : ℕ}
    (he : e = ownScalarsOf (partsInFront F.first.blocksInOrder l b.place)) :
    ∃ row,
      ownerOf maskRowRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds))
        s!"link {l}, moment 0" isMaskRowMsg = some row ∧
      K4MaskLockAt B Q e row.owner row.base.e := by
  obtain ⟨row, _, es₁, hr, _, K⟩ := k4Lock_of_bookWhole h hp hb hl R hB
  exact ⟨row, hr, es₁, _, _, he ▸ K⟩

/-- CONDITIONAL on h, hp, hb, hl, R and hB. **THE INDEX SIDE's NAME AT THE MAKER's OWN LETTERS**:
the lock at the letters (idx.owner, idx.base.e + t), with idx pinned by `ownerOf`'s return and t
the end values of the merges in front. -/
theorem k4LastEntryAt_of_bookWhole {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    {b : Block F.S₁ F.Cl} (hb : b ∈ F.first.blocksInOrder) {l : Nat} (hl : b.place.link = some l)
    {Q : K4Pub} {A : List PartAt} {m : PartAt} (R : K4RowIsPlan M b Q A m)
    (hB : lendsRow B 0 (k4Place Q) (k4RowIn Q) = true) :
    ∃ idx, ownerOf indexMaskRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds))
        "link 0, moment 0" isIndexMaskMsg = some idx ∧
      K4LastEntryAt B Q idx.owner
        (idx.base.e + mergeEndsOf M.ends
          (linksInFront F.first.blocksInOrder l ++ partsInFront F.first.blocksInOrder l b.place)) := by
  obtain ⟨_, idx, es₁, _, hi, K⟩ := k4Lock_of_bookWhole h hp hb hl R hB
  exact ⟨idx, hi, es₁, _, K.last, rfl, rfl⟩

/-- CONDITIONAL on h, hp, hb, hl, R, hd, hca and he. **BOTH NAMES FROM THE BOOK's LAWS, WITH NO
HYPOTHESIS THAT THE BOOK LENDS.** hd: the first table gives the addresses of K4's parts no coin of
their own (no row, or a row of the count 0). hca: the book has no carried entry there. -/
theorem k4Names_of_bookWhole (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    (hb : b ∈ F.first.blocksInOrder) (hl : b.place.link = some l) (R : K4RowIsPlan M b Q A m)
    (hd : ∀ i, i < (k4RowIn Q).length → dueAt (B.rowsOf 0) ⟨k4Place Q, i⟩ = ⟨0, 0⟩)
    (hca : ∀ i, i < (k4RowIn Q).length → carryE B ⟨k4Place Q, i⟩ = []) {e : ℕ}
    (he : e = ownScalarsOf (partsInFront F.first.blocksInOrder l b.place)) :
    ∃ row idx,
      ownerOf maskRowRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds))
        s!"link {l}, moment 0" isMaskRowMsg = some row ∧
      ownerOf indexMaskRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
        isIndexMaskMsg = some idx ∧
      K4MaskLockAt B Q e row.owner row.base.e ∧
      K4LastEntryAt B Q idx.owner
        (idx.base.e + mergeEndsOf M.ends
          (linksInFront F.first.blocksInOrder l ++ partsInFront F.first.blocksInOrder l b.place)) := by
  obtain ⟨row, idx, es₁, hr, hi, K⟩ :=
    k4Lock_of_bookWhole h hp hb hl R (k4_lends_of_bookWhole h hp hb hl R hd hca)
  exact ⟨row, idx, hr, hi, ⟨es₁, _, _, he ▸ K⟩, ⟨es₁, _, K.last, rfl, rfl⟩⟩

/-- CONDITIONAL on h, hp, hb, hl, R, hS and he. **BOTH NAMES FROM THE BOOK's LAWS, WITH NO
HYPOTHESIS ON WHAT THE BOOK HOLDS AT K4's ADDRESSES.** hS: no round of b is named "SEND seed". -/
theorem k4Names_whole (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    (hb : b ∈ F.first.blocksInOrder) (hl : b.place.link = some l) (R : K4RowIsPlan M b Q A m)
    (hS : ∀ r ∈ b.rounds, r.entry.name ≠ "SEND seed") {e : ℕ}
    (he : e = ownScalarsOf (partsInFront F.first.blocksInOrder l b.place)) :
    ∃ row idx,
      ownerOf maskRowRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds))
        s!"link {l}, moment 0" isMaskRowMsg = some row ∧
      ownerOf indexMaskRun F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) "link 0, moment 0"
        isIndexMaskMsg = some idx ∧
      K4MaskLockAt B Q e row.owner row.base.e ∧
      K4LastEntryAt B Q idx.owner
        (idx.base.e + mergeEndsOf M.ends
          (linksInFront F.first.blocksInOrder l ++ partsInFront F.first.blocksInOrder l b.place)) := by
  obtain ⟨row, idx, es₁, hr, hi, K⟩ :=
    k4Lock_of_bookWhole h hp hb hl R (k4_lends_whole h hp hb hl R hS)
  exact ⟨row, idx, hr, hi, ⟨es₁, _, _, he ▸ K⟩, ⟨es₁, _, K.last, rfl, rfl⟩⟩

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4Lock_of_bookWhole
#print axioms ProofFile.Honest.K4.W.k4MaskLockAt_of_bookWhole
#print axioms ProofFile.Honest.K4.W.k4LastEntryAt_of_bookWhole
#print axioms ProofFile.Honest.K4.W.k4Names_of_bookWhole
#print axioms ProofFile.Honest.K4.W.k4Names_whole
