-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/RcLast.lean: no soundness is claimed.
One test with code on the first chain's last state that holds all that the last chain's ledger spends of that state, and what its accept gives. For the letter Rc of the last table's count (the slot's own condition there is ocEnd ∧ Rc): at Rc := fun q => rcLastB ft V L cs (get q).2 = true four fields of the ledger's facts on the verifier's state are theorems.
  sampleTwoB cs V s   where firstOfS s hands f: the group at f.own has two members, and K12's files' test sampleL accepts the first at the shape V.indexShape and the second at V.wShape (sampleAtB, RcLastCode.lean). Where nothing is handed: yes.
  **rcLastB ft V L cs s** := bookInOrderB ft s.book s.roots && bookFitsB s.book && ownSitsB V s && sampleTwoB cs V s && seatsCarriedB L s.book: the first, the second and the fifth are fields of FoldFacts (Johnson/Desc/First/FoldFacts.lean) (bookInOrder · bookFits · seatsCarried); ownSits is no field of it in this library; the fourth is this folder's own. The fifth conjunct and the letter L (the list of places and shapes, Johnson/Desc/K12/Door/DoorBools.lean) are for the ledger's field «book» (BookAtW.lean: shape_of_elder).
  place_of_seat       in a book whose tree at place z bears the number z, a message's seat (seatBy noFirst) is its place
  **rcLast_two**      rcLastB 0 V L cs s = true · firstOfS s = some f ⇒ HandedTwo V.index V.w V.indexShape V.wShape f
  **rcLast_roots**    rcLastB ft V L cs s = true · firstOfS s = some f ⇒ f.roots = f.book.trees.size ∧ ∀ j T, f.book.trees[j]? = some T → T.number = ft + j
  **rcLast_sample**   rcLastB 0 V L cs s = true · firstOfS s = some f · seatBy noFirst f.book i = some q · (q = V.index ∧ sh = V.indexShape ∨ q = V.w ∧ sh = V.wShape) ⇒ SampleAt cs sh f.st i
  **rcLast_seats**    rcLastB ft V L cs s = true · firstOfS s = some f ⇒ seatsCarriedB L f.book = true
Does not show. That a reached state passes the test. No member. Nothing on soundness.
-/
import Johnson.ToldDescR.RcLastCode
import Johnson.ToldDescR.HandedOfBools
import Johnson.ToldDescR.ThreeAtW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open OnBytes
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third (firstOfS)
open VerifiableInference.Desc.K12.Door (bookInOrderB seatsCarriedB)
open VerifiableInference.Desc.Book (BookFits places_inj)

/- `sampleTwoB` and `rcLastB` stand in RcLastCode.lean. -/

theorem rcLastB_parts {ft : ℕ} {V : OwnSeats} {L : K12.Door.Laid} {cs : Codes} {s : First.S}
    (h : rcLastB ft V L cs s = true) :
    bookInOrderB ft s.book s.roots = true ∧ bookFitsB s.book = true ∧ ownSitsB V s = true ∧
      sampleTwoB cs V s = true ∧ seatsCarriedB L s.book = true := by
  unfold rcLastB at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem rcLast_two {V : OwnSeats} {L : K12.Door.Laid} {cs : Codes} {s : First.S} {f : Handed}
    (h : rcLastB 0 V L cs s = true) (hf : firstOfS s = some f) :
    HandedTwo V.index V.w V.indexShape V.wShape f := by
  obtain ⟨h1, h2, h3, -, -⟩ := rcLastB_parts h
  exact handedTwo_of_bools hf h3 h2 h1

theorem rcLast_roots {ft : ℕ} {V : OwnSeats} {L : K12.Door.Laid} {cs : Codes} {s : First.S}
    {f : Handed} (h : rcLastB ft V L cs s = true) (hf : firstOfS s = some f) :
    f.roots = f.book.trees.size ∧
      ∀ (j : ℕ) (T : Tree), f.book.trees[j]? = some T → T.number = ft + j := by
  obtain ⟨h1, -, -, -, -⟩ := rcLastB_parts h
  obtain ⟨k1, k2⟩ := handedRoots_of_bools hf h1 rfl
  have eb : f.book = s.book := by
    unfold firstOfS at hf
    obtain ⟨e, _, rfl⟩ := Option.map_eq_some_iff.1 hf
    rfl
  exact ⟨by rw [k1, eb], k2⟩

/-- The handed book is the state's: so the list of places and shapes is carried in it. -/
theorem rcLast_seats {ft : ℕ} {V : OwnSeats} {L : K12.Door.Laid} {cs : Codes} {s : First.S}
    {f : Handed} (h : rcLastB ft V L cs s = true) (hf : firstOfS s = some f) :
    seatsCarriedB L f.book = true := by
  obtain ⟨-, -, -, -, h5⟩ := rcLastB_parts h
  have eb : f.book = s.book := by
    unfold firstOfS at hf
    obtain ⟨e, _, rfl⟩ := Option.map_eq_some_iff.1 hf
    rfl
  rw [eb]
  exact h5

/-- In a book whose tree at place z bears the number z, a message's seat is its place. -/
theorem place_of_seat {B : TreeBook}
    (hN : ∀ (j : ℕ) (T : Tree), B.trees[j]? = some T → T.number = j) {i : ℕ} {q : ℕ × ℕ}
    (h : seatBy noFirst B i = some q) : B.place[i]? = some q := by
  unfold seatBy at h
  cases hp : B.place[i]? with
  | none => rw [hp] at h; cases h
  | some p =>
    rw [hp] at h
    have h' : (B.trees[p.1]?).map (fun T => (noFirst p.1 T, p.2)) = some q := h
    obtain ⟨T, hT, e⟩ := Option.map_eq_some_iff.1 h'
    have e' : (T.number, p.2) = q := e
    rw [hN p.1 T hT] at e'
    rw [← e']

theorem rcLast_sample {V : OwnSeats} {L : K12.Door.Laid} {cs : Codes} {s : First.S} {f : Handed}
    (h : rcLastB 0 V L cs s = true) (hf : firstOfS s = some f) {i : ℕ} {q : ℕ × ℕ}
    {sh : OracleShape} (hi : seatBy noFirst f.book i = some q)
    (hq : (q = V.index ∧ sh = V.indexShape) ∨ (q = V.w ∧ sh = V.wShape)) :
    SampleAt cs sh f.st i := by
  obtain ⟨-, h2, h3, h4, -⟩ := rcLastB_parts h
  obtain ⟨-, hN⟩ := rcLast_roots h hf
  have hN' : ∀ (j : ℕ) (T : Tree), f.book.trees[j]? = some T → T.number = j :=
    fun j T hT => by rw [hN j T hT, Nat.zero_add]
  have hF : BookFits f.book := by
    have eb : f.book = s.book := by
      unfold firstOfS at hf
      obtain ⟨e, _, rfl⟩ := Option.map_eq_some_iff.1 hf
      rfl
    rw [eb]
    exact (bookFitsB_iff _).1 h2
  obtain ⟨G, i₁, i₂, hG, hm, p1, p2, -, -⟩ := (ownSitsB_iff V s).1 h3 f hf
  unfold sampleTwoB at h4
  rw [hf] at h4
  simp only [hG, hm, Bool.and_eq_true] at h4
  have hp := place_of_seat hN' hi
  rcases hq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain rfl : i = i₁ := places_inj hF hp p1
    exact (sampleAt_iff _ _ _ _).1 h4.1
  · obtain rfl : i = i₂ := places_inj hF hp p2
    exact (sampleAt_iff _ _ _ _).1 h4.2

end ToldDesc

#print axioms ToldDesc.rcLast_two
#print axioms ToldDesc.rcLast_roots
#print axioms ToldDesc.rcLast_seats
#print axioms ToldDesc.place_of_seat
#print axioms ToldDesc.rcLast_sample
