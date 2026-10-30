-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/LendsOfBook.lean: CONDITIONAL. Three statements with their
proofs.

What is here. THE WHOLE BOOK OF COINS LENDS THE ROW OF THE FEED-FORWARD LAYERS' OWN ROUNDS
(sub-protocol K4): the field lends of `K4LastEntry` (Law/W/LastEntry.lean), which `K4MaskLock`
(Law/W/MaskLock.lean) holds as last.lends, FROM THE BOOK's OWN LAWS. `k4_lends_of_fit`
(Law/W/LendsOfFit.lean) has it from six premises. Here, where `bookWhole` (Honest/BookWhole.lean)
returns the book and the plan's row at K4's place is K4's row, part for part (`K4RowIsPlan`,
Law/W/RowIsPlanForm.lean), five of the six are shown. hsp, that at each part the names and counts
of the book's spending entries are what the part states: `bookWhole_part_states`
(Honest/Small/SpentOfBook.lean) says what the book has for each part of the plan, and the form's
field states says that K4's part states just that. That the book passes its own tests: `bookWhole`
returns no other book. That K4's place is a place of the first chain: the member stands there. hd
and hca, that the book's first table gives the addresses of K4's parts no coin of their own (no row
there, or a row of the count 0) and that the book has no carried entry for them:
`bookWhole_bare_at` (Honest/Small/BareOfBook.lean), where the sub-protocol holds no round "SEND
seed" (hS, a premise) and no round "FOLD epsilon" (the form's field noFold). The sixth is the
library's test on places.

  `k4_hsp_of_bookWhole`   **hsp.**
  `k4_lends_of_bookWhole`   **the Bool `lendsRow` is true at K4's row**, with hd and hca as
      premises: no coin stands in the statement.
  `k4_lends_whole`   **the same with hS in their stead**: no premise on the book but that
      `bookWhole` returns it.

Not shown here. THAT `bookWhole` RETURNS AT ANY FILES; that the description passes its test on
places; THAT ANY MEMBER OF A DESCRIPTION MEETS `K4RowIsPlan` OR hS (Law/W/RowIsPlan.lean speaks of
the first): THE FORM FAILS AT A PLAN AT WHICH A PART OF K4's STATES A RUN OF COUNT 0: the maker
lays no entry there. Which parts are merges is the free parameter M. Chain number 0 alone. What is
lent is not described. It stands over Honest/BookMergeStretch.lean, a file of other writers that is
not reviewed. A LAW, NOT A PART: no file that
defines a part of the proof file's description may import this one. Nothing on soundness, on
completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.W.RowIsPlanForm
import Johnson.Desc.ProofFile.Honest.K4.Law.W.LendsOfFit
import Johnson.Desc.ProofFile.Honest.Small.SpentOfBook
import Johnson.Desc.ProofFile.Honest.Small.BareOfBook

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4.W
open VerifiableInference.Desc (Block FileDescription Place)
open OnBytes.Desc.First.K4.Honest
open ProofFile.Honest.BookShared

variable {Xi : Type} {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges} {B : ProverCoinCounts}

/-- `bookWhole` returns only a book that passes its own tests. It is `bookWhole_word`
(Honest/AtPureLaw.lean), shown here again so that this file need not import the honest prover's
whole make. -/
private theorem word_of_whole (h : bookWhole F p0 p1 p2 M = .ok B) : B.word F = none := by
  unfold bookWhole at h
  obtain ⟨W, -, hc⟩ := ex_bindE h
  unfold ProverCoinCounts.checked at hc
  split at hc
  · cases hc
    assumption
  · cases hc

/-- CONDITIONAL on h, hp, hb, hl and R. **AT EACH PART OF K4's ROW THE NAMES AND COUNTS OF THE
BOOK's SPENDING ENTRIES ARE WHAT THE PART STATES.** -/
theorem k4_hsp_of_bookWhole (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    {b : Block F.S₁ F.Cl} (hb : b ∈ F.first.blocksInOrder) {l : Nat} (hl : b.place.link = some l)
    {Q : K4Pub} {A : List PartAt} {m : PartAt} (R : K4RowIsPlan M b Q A m) :
    ∀ i P, (k4RowIn Q)[i]? = some P →
      (spentE B ⟨k4Place Q, i⟩).map Ahead.named = P.spends := by
  intro i P hP
  obtain ⟨hi, -⟩ := List.getElem?_eq_some_iff.1 hP
  have hi' : i < (planParts b).length := by
    rw [R.len]
    exact hi
  have hq : (planParts b)[i]? = some (planParts b)[i] := List.getElem?_eq_getElem hi'
  rw [← R.place, bookWhole_part_states h hp hb hl R.noFold i _ hq]
  exact (R.states i _ P hq hP).symm

/-- CONDITIONAL on h, hp, hb, hl, R, hd and hca. **THE WHOLE BOOK LENDS K4's ROW.** -/
theorem k4_lends_of_bookWhole (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    {b : Block F.S₁ F.Cl} (hb : b ∈ F.first.blocksInOrder) {l : Nat} (hl : b.place.link = some l)
    {Q : K4Pub} {A : List PartAt} {m : PartAt} (R : K4RowIsPlan M b Q A m)
    (hd : ∀ i, i < (k4RowIn Q).length → dueAt (B.rowsOf 0) ⟨k4Place Q, i⟩ = ⟨0, 0⟩)
    (hca : ∀ i, i < (k4RowIn Q).length → carryE B ⟨k4Place Q, i⟩ = []) :
    lendsRow B 0 (k4Place Q) (k4RowIn Q) = true := by
  have ha : k4Place Q ∈ placesAt F 0 := by
    rw [← R.place]
    exact List.mem_map.2 ⟨b, hb, rfl⟩
  exact k4_lends_of_fit (word_of_whole h) hp ha hd hca (k4_hsp_of_bookWhole h hp hb hl R)

/-- CONDITIONAL on h, hp, hb, hl, R and hS. **THE WHOLE BOOK LENDS K4's ROW, WITH NO PREMISE ON THE
BOOK's TABLE OR ON ITS CARRIED ENTRIES.** hS: the sub-protocol holds no round "SEND seed". -/
theorem k4_lends_whole (h : bookWhole F p0 p1 p2 M = .ok B) (hp : F.placesOk = true)
    {b : Block F.S₁ F.Cl} (hb : b ∈ F.first.blocksInOrder) {l : Nat} (hl : b.place.link = some l)
    {Q : K4Pub} {A : List PartAt} {m : PartAt} (R : K4RowIsPlan M b Q A m)
    (hS : ∀ r ∈ b.rounds, r.entry.name ≠ "SEND seed") :
    lendsRow B 0 (k4Place Q) (k4RowIn Q) = true := by
  have hbare := bookWhole_bare_at h hp hb hS R.noFold
  rw [R.place] at hbare
  exact k4_lends_of_bookWhole h hp hb hl R (fun i _ => (hbare i).1) fun i _ => (hbare i).2

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.k4_hsp_of_bookWhole
#print axioms ProofFile.Honest.K4.W.k4_lends_of_bookWhole
#print axioms ProofFile.Honest.K4.W.k4_lends_whole
