-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/IdxBehind.lean: `idxAt` (Johnson/Desc/Sound/MgAt/K11.lean) holds of the
verifier's state behind an accepting step of the merge of the claims on the committed table: the
premise hWb of `merge_tiedAtR` (TiesReached.lean) at Wb := `idxAt D ni (posMask RI) xI`, at the
composed meaning `mgAll D Mg₀`, the full size's written lists and border 346. Theorems with their
proofs.

How. `idxAt` is the conclusion of `index_readings_at` (IndexRowBook.lean) at the composed meaning's
own reader of the pending rows. Of that theorem's thirteen premises eleven stand at the state b
behind the merge (two read no state), and read of it the statement, the book of trees, the number of
roots and the field out alone: these four the merge's accepting step leaves (`leavesSeven`,
Law.lean). So each is shown at the state a in front:
  the shapes, the order of the book's trees, the seats, the codes: four premises on the family Rch
    at border 346, in the words of the fields msgShapes, bookInOrder, seatsCarried and codes of
    `FoldFacts` (Johnson/Desc/First/FoldFacts.lean), but that bookInOrder stands here at 0 for the
    structure's d.ft, and codes at D.cs for its d.sent.codes;
  "the listed places name trees of the book": from the field bookFits and the seats
    (`placesBelow_of_fits`);
  "the book has a place for every message": the fixed test `bookAt` inside the table's condition;
  which number the index masks' message has, and that the statement has such a message: the public
    tests "indexIs" and "indexThere", which the table asks at border 346 (`k11_hIn`,
    K11PubClosed.lean), at the composed meaning (`pubAll_indexIs`, `pubAll_indexThere`);
  the message's seat, its shape, the member's seat, the power of two, the table's size ni and the
    bits RI: closed premises on the lists L and M, on the numbers D.N, on the codes D.cs and on the
    member xI (`place_of_seats`, `msgShape_at`, `mask_size_of_shape`, `mask_rows_of_shape`).

Main names:
  `placesBelow_of_fits`: where the book's places are the listed ones and every place of the book
    names a tree of the book, the listed places do.
  `index_at_front`: out of the table's condition at border 346, at an unmarked state: the index
    masks' message has the number D.N.indexNo, the statement has a message of that number, and the
    book has a place for every message.
  `idx_of_front`: `idxAt` at a state b that has the statement, book, roots and out of a state a at
    which the facts hold.
  `idx_behind`: THE PREMISE hWb, to the letter.
  `idx_behind_of_foldFacts`: the same under the one structure `FoldFacts`, with the two equations
    d.ft = 0 and d.sent.codes = D.cs: it spends the fields bookInOrder, seatsCarried, bookFits,
    msgShapes and codes, at border 346.

Limits. NO EXAMPLE: the premises are shown and evaluated together at no state of a run. An
implication: where no unmarked state of the family meets the table's condition at border 346, or the
merge accepts from none, it speaks of no state; none is exhibited here. Shown at no value here: the
five premises on the family; the six closed premises; Mg₀.more = {}. Two of the five are not the
fields' own words: the first tree's number is taken as 0, as `index_readings_at` takes it, and the
codes as D.cs: who has `FoldFacts` owes d.ft = 0 and d.sent.codes = D.cs beside it (meant: the
fields first and sent of `P5J.AtMgR`, Johnson/P5J/AtMgR.lean; not called here). The numbers k, ni
and RI are fixed by the member xI and the codes D.cs; RI is k wherever hp holds. Nothing on
soundness.

-/
import Johnson.Desc.Sound.MgAt.K11
import Johnson.Top.H0.MergeLaw.IndexRowBook
import Johnson.Top.H0.MergeLaw.K11PubClosed
import Johnson.Desc.First.FoldFacts

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes (OracleShape TreeBook ceilLog2)
open OnBytes.Means (tableSize)
open VerifiableInference.Desc.Sound (MgData mgAll mgAll_pub linksFull CellsQ MsgT idxAt k11_hIn
  keep24 Mem seatOf)
open VerifiableInference.Desc.K12.Door (Laid msgShapesB bookInOrderB seatsCarriedB placesBelowB
  atFirstBook atFirstSeats atFirstFits atFirstShapes place_of_seats msgShape_at)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-- Where the book's places are the listed ones, and every place of the book names a tree of the
book, the listed places name trees of the book. -/
theorem placesBelow_of_fits {L : Laid} {B : TreeBook} (h : seatsCarriedB L B = true)
    (hf : Sound.bookFitsB B = true) : placesBelowB L B.place.size B.trees.size = true := by
  unfold seatsCarriedB at h
  simp only [Bool.and_eq_true] at h
  have e : B.place.toList = L.places.take B.place.size := eq_of_beq h.1.1.1
  unfold Sound.bookFitsB at hf
  unfold placesBelowB
  rw [← e, List.all_eq_true]
  intro q hq
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hq
  rw [Array.getElem?_toList] at hi
  obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.1 hi
  have t := List.all_eq_true.1 hf i (List.mem_range.2 hlt)
  simp only [hi] at t
  cases et : B.trees[q.1]? with
  | none => simp [et] at t
  | some T => exact decide_eq_true (Array.getElem?_eq_some_iff.1 et).1

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR X) (Mg₀ : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **Out of the table's condition at border 346**, at an unmarked state. -/
theorem index_at_front (hM : Mg₀.more = {}) (Nn : Numbers) {Fr : Sound.Frame} (z : P)
    (a : S × Fr.E.Str)
    (hon : Sound.onQ Nn (mgAll D Mg₀) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346
      a) (hf : a.1.failed = none) :
    a.1.out.indexMasks = D.N.indexNo ∧ a.1.out.indexMasks < a.1.st.oracles.size ∧
      a.1.book.place.size = a.1.st.oracles.size := by
  unfold Sound.onQ onAt at hon
  obtain ⟨-, hmk | ⟨hb, -⟩⟩ := hon
  · exact absurd hf hmk
  · simp only [Bool.and_eq_true] at hb
    obtain ⟨⟨-, hpub⟩, hbk⟩ := hb
    unfold pubHeld at hpub
    have hq : ∀ q ∈ [Pub.ledger 24, .freeAbove 24, .indexIs, .indexThere] ++ keep24,
        (mgAll D Mg₀).pub q (z, a.1) = true :=
      fun q hq => List.all_eq_true.1 hpub q (k11_hIn D Mg₀ hM q hq)
    have h1 := hq .indexIs (List.mem_append_left _ (by simp))
    have h2 := hq .indexThere (List.mem_append_left _ (by simp))
    rw [mgAll_pub, pubAll_indexIs] at h1
    rw [mgAll_pub, pubAll_indexThere] at h2
    unfold K13.indexIsC at h1
    unfold K13.indexThereC at h2
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h2
    unfold bookAt at hbk
    simp only [Bool.and_eq_true, beq_iff_eq] at hbk
    exact ⟨eq_of_beq h1, (Array.getElem?_eq_some_iff.1 hx).1, hbk.1.2⟩

/-- **`idxAt` at a state b that has the statement, the book, the roots and the field out of a state
a at which the facts hold.** -/
theorem idx_of_front (L : Laid) (M : List OracleShape) (xI : Mem) (k ni RI : ℕ) {a b : S}
    (est : b.st = a.st) (ebk : b.book = a.book) (ero : b.roots = a.roots) (eout : b.out = a.out)
    (hix : a.out.indexMasks = D.N.indexNo) (ht : a.out.indexMasks < a.st.oracles.size)
    (hs : a.book.place.size = a.st.oracles.size)
    (hbook : atFirstBook 0 a = true) (hseats : atFirstSeats L a = true)
    (hfits : atFirstFits a = true) (hshapes : atFirstShapes M a = true)
    (hcodes : a.st.codes = D.cs)
    (hseat : L.places[D.N.indexNo]? = some D.N.index)
    (hsh : M[D.N.indexNo]? = some (xI.1.l.get xI.2).1) (hx : seatOf xI = D.N.index)
    (hp : (xI.1.l.get xI.2).1.maskRows = 2 ^ k)
    (hni : 2 ^ (k + (Johnson.Pack.pMask D.cs (xI.1.l.get xI.2).1).logEll) = ni)
    (hRI : ceilLog2 (xI.1.l.get xI.2).1.maskRows = RI) : idxAt D ni (posMask RI) xI b := by
  have hmsg : (a.st.oracles[a.out.indexMasks]?).map (·.shape) = some (xI.1.l.get xI.2).1 := by
    rw [msgShape_at (st := a.st) hshapes _ ht, hix]
    exact hsh
  show ∀ (z : P) (w : Wit (CellsQ rows cols) Tok MsgT) (c : ℕ),
    (K13.Law.rwBook D.arr D.mat13 (z, b) w).mask ⟨b.out.indexMasks, c⟩ =
      vecBy D.cs D.arr ni (posMask RI) xI w c
  refine index_readings_at D.cs D.arr D.mat13 D.N M L b xI k ni RI ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hp
    ?_ ?_
  · rw [est]
    exact hshapes
  · rw [ebk, ero]
    exact hbook
  · rw [ebk]
    exact hseats
  · rw [ebk, est]
    exact hs
  · rw [ebk]
    exact placesBelow_of_fits hseats hfits
  · rw [eout, est]
    exact ht
  · rw [ebk, eout, place_of_seats (B := a.book) hseats _ (by rw [hs]; exact ht), hix]
    exact hseat
  · rw [est]
    exact hcodes
  · rw [eout, hix]
    exact hsh
  · rw [est, eout, mask_size_of_shape hmsg hp, hcodes]
    exact hni
  · rw [est, eout, (mask_rows_of_shape hmsg).2]
    exact hRI

/-- **THE PREMISE hWb OF `merge_tiedAtR`**, at Wb := `idxAt D ni (posMask RI) xI`. The five premises
on the family Rch are fields of `FoldFacts`, at border 346 alone: three in their own words;
bookInOrder at 0 for d.ft; codes at D.cs for d.sent.codes. -/
theorem idx_behind (hM : Mg₀.more = {}) (Pm : HeadMergeP) (Nn : Numbers) {Fr : Sound.Frame}
    (Rch : ℕ → (P × S) × Fr.E.Str → Prop) (L : Laid) (M : List OracleShape) (xI : Mem)
    (k ni RI : ℕ)
    (hbook : ∀ a, Rch 346 a → a.1.2.failed = none → atFirstBook 0 a.1.2 = true)
    (hseats : ∀ a, Rch 346 a → a.1.2.failed = none → atFirstSeats L a.1.2 = true)
    (hfits : ∀ a, Rch 346 a → a.1.2.failed = none → atFirstFits a.1.2 = true)
    (hshapes : ∀ a, Rch 346 a → a.1.2.failed = none → atFirstShapes M a.1.2 = true)
    (hcodes : ∀ a, Rch 346 a → a.1.2.failed = none → a.1.2.st.codes = D.cs)
    (hseat : L.places[D.N.indexNo]? = some D.N.index)
    (hsh : M[D.N.indexNo]? = some (xI.1.l.get xI.2).1) (hx : seatOf xI = D.N.index)
    (hp : (xI.1.l.get xI.2).1.maskRows = 2 ^ k)
    (hni : 2 ^ (k + (Johnson.Pack.pMask D.cs (xI.1.l.get xI.2).1).logEll) = ni)
    (hRI : ceilLog2 (xI.1.l.get xI.2).1.maskRows = RI) :
    ∀ (z : P) (a b : S × Fr.E.Str),
      Sound.onQ Nn (mgAll D Mg₀) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) → idxAt D ni (posMask RI) xI b.1 := by
  intro z a b hon hr hnm hy
  obtain ⟨rs, hy⟩ := hy
  have hf : a.1.failed = none := Classical.not_not.1 hnm
  obtain ⟨est, ebk, ero, -, -, eout, -⟩ := leavesSeven Pm a.1 rs [] b.1 hy
  obtain ⟨hix, ht, hs⟩ := index_at_front D Mg₀ hM Nn z a hon hf
  exact idx_of_front D L M xI k ni RI (a := a.1) (b := b.1) est ebk ero eout hix ht hs
    (hbook ((z, a.1), a.2) hr hf) (hseats ((z, a.1), a.2) hr hf) (hfits ((z, a.1), a.2) hr hf)
    (hshapes ((z, a.1), a.2) hr hf) (hcodes ((z, a.1), a.2) hr hf) hseat hsh hx hp hni hRI

/-- **The same under the one structure of facts on the reached states**, with two equations on its
data. -/
theorem idx_behind_of_foldFacts (hM : Mg₀.more = {}) (Pm : HeadMergeP) (Nn : Numbers)
    {Fr : Sound.Frame} (Rch : ℕ → (P × S) × Fr.E.Str → Prop) (d : FoldData)
    (reqW : P → Array UInt32)
    (F : FoldFacts Rch (fun a => a.1) d reqW linksFull (flatPlacesOf linksFull true))
    (hft : d.ft = 0) (hcs : d.sent.codes = D.cs) (xI : Mem) (k ni RI : ℕ)
    (hseat : d.L.places[D.N.indexNo]? = some D.N.index)
    (hsh : d.M[D.N.indexNo]? = some (xI.1.l.get xI.2).1) (hx : seatOf xI = D.N.index)
    (hp : (xI.1.l.get xI.2).1.maskRows = 2 ^ k)
    (hni : 2 ^ (k + (Johnson.Pack.pMask D.cs (xI.1.l.get xI.2).1).logEll) = ni)
    (hRI : ceilLog2 (xI.1.l.get xI.2).1.maskRows = RI) :
    ∀ (z : P) (a b : S × Fr.E.Str),
      Sound.onQ Nn (mgAll D Mg₀) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) → idxAt D ni (posMask RI) xI b.1 :=
  idx_behind D Mg₀ hM Pm Nn Rch d.L d.M xI k ni RI
    (fun a ha hf => by rw [← hft]; exact F.bookInOrder 346 a ha hf) (F.seatsCarried 346)
    (F.bookFits 346) (F.msgShapes 346) (fun a ha hf => (F.codes 346 a ha hf).trans hcs) hseat hsh
    hx hp hni hRI

end

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.placesBelow_of_fits
#print axioms VerifiableInference.Desc.First.MergeLaw.index_at_front
#print axioms VerifiableInference.Desc.First.MergeLaw.idx_of_front
#print axioms VerifiableInference.Desc.First.MergeLaw.idx_behind
#print axioms VerifiableInference.Desc.First.MergeLaw.idx_behind_of_foldFacts
