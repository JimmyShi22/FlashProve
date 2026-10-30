-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/Law/BookAt2.lean: BEHIND THE
KEY FILE's TWO FIRST SENDINGS THE BOOK OF TREES CARRIES THE PLANNER's LAYOUTS: a state of the first
chain that was reached at border 2 places each oracle message of the second sending (the lookups'
own message and what rides with it) where the planner's layout of that sending says, behind the
first sending's trees; and the tree there has the layout's shape.

Main names:
  seat_core: a yes of a sending's seat is a yes of the kind K1's own decision; the seat lays back
    that decision's statement, book and count of roots.
  sent_book: at a yes of that decision the planner lays the trees (layTrees … = some lay), and the
    book behind is the receiving's book at that layout (recvBook); statement and book were in step.
  open_book: the making of the ranges' group leaves the book.
  two_sendings: the two sendings' yeses, one behind the other, from the chain's start.
  seats_two: Hist₁ (Key.descriptionFromSource X N P) D 2 a ⊢ there are layI, layB, the planner's layouts of the two
    sendings at the plan's codes, with seatsB (laidSeats 1 layI.shapes.size ‹the second sending›
    layB) a.2.d.book = true.

By: decideSend_iff (Johnson/Desc/K1/Law/Writes3.lean) ·
seatsB_new (Johnson/Desc/Sound/SeatsCarried.lean). No premise on the plan: the layouts come out of
the sendings' own yes.

Object: Key.sendIndexMasks, Key.sendOwnMessage at the places 0 and 1 of Key.descriptionFromSource X N P. User:
Johnson/RunOne/Law/BookAt15.lean.
Limits. Nothing on soundness.

-/
import Johnson.RunOne.Law.BookStays
import Johnson.RunOne.Law.AllAtO
import Johnson.Desc.Sound.SeatsCarried
import Johnson.Desc.Own.TreesMean

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.BookAt2
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Slice
open _root_.Desc.Plain (DState)
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open VerifiableInference.Desc.Ground (coreStill_same)
open VerifiableInference.Desc.K1 (Par decideSend decideSend_iff)
open VerifiableInference.Desc.K3.KeyLaw (bindX namedX)
open VerifiableInference.Desc.Key (FirstState Claim ChainState Source sendingSeat sendingPar withLoc
  sendIndexMasks sendOwnMessage openRangesGroup chainStart)
open _root_.Desc.K14.Law.Fence (seatsB laidSeats seatsB_new recvBook_counts)
open Johnson.RunOne.Sound (FK fk_idx_at fk_msg_at)
open Johnson.RunOne.Law.FrontSteps (sent_par)
open Johnson.RunOne.Law.AllAtO (fk_two₀ fk_two₁)
open LPFD (Hist₁ Reached)

variable {β Cl L : Type}

/-- **The yes of a sending's seat is a yes of the kind's own decision**, whose statement, book and
count of roots the seat lays back. -/
theorem seat_core {name : String} {P : Par} {s t : ChainState β} {rs : List Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))}
    (h : (sendingSeat (Cl := Cl) name P).decide s rs gs = .ok t) :
    ∃ ids d', decideSend P s.debt (withLoc s.d (#[] : Array ℕ)) rs = .ok (ids, d') ∧
      t.d.st = d'.st ∧ t.d.book = d'.book ∧ t.d.roots = d'.roots := by
  have h' : ((decideSend P s.debt (withLoc s.d (#[] : Array ℕ)) rs).map fun x =>
      ({ s with d := withLoc ({ x.2 with loc := x.1 } : DState (Array ℕ)) (), owed := none,
                sent := x.1 } : ChainState β)) = .ok t := by
    rw [← h]
    show _ = ((decideSend P s.debt (withLoc s.d (#[] : Array ℕ)) rs).map _).map _
    cases decideSend P s.debt (withLoc s.d (#[] : Array ℕ)) rs <;> rfl
  cases hd : decideSend P s.debt (withLoc s.d (#[] : Array ℕ)) rs with
  | error e =>
    rw [hd] at h'
    cases h'
  | ok x =>
    rw [hd] at h'
    cases h'
    exact ⟨x.1, x.2, rfl, rfl, rfl, rfl⟩

/-- **The book behind a sending.** -/
theorem sent_book {P : Par} {owed : Option ℕ} {d d' : DState L} {r₁ r₂ : Fmt.RoundView} {ids : Array ℕ}
    (h : decideSend P owed d [r₁, r₂] = .ok (ids, d')) :
    ∃ lay, layTrees P.codes P.sent = some lay ∧
      d'.book = recvBook P.gp.firstTree d.book P.sent lay d.st.oracles.size d.roots ∧
      d.st.oracles.size = d.book.place.size := by
  obtain ⟨⟨_, hc, _, hok, _⟩, _, rfl⟩ := (decideSend_iff P owed d d' r₁ r₂ ids).1 h
  simp only [Ground.ok, Ground.recvL, Ground.sentL, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hok
  have hcan : (Own.treesMade d.st.codes P.sent).isSome = true := hok.1.2
  obtain ⟨lay, hlay⟩ := Option.isSome_iff_exists.1 hcan
  rw [hc, Own.treesMade_eq] at hlay
  refine ⟨lay, hlay, ?_, hok.2⟩
  show (VerifiableInference.Desc.K1.recvD P.gp.firstTree d P.sent
    ((layTrees P.codes P.sent).getD {})).book = _
  rw [hlay]
  rfl

/-- The making of the ranges' group leaves the book. -/
theorem open_book {one : OneTime} {m t : ChainState β} (h : openRangesGroup one m = .ok t) :
    t.d.book = m.d.book := by
  unfold openRangesGroup at h
  dsimp only at h
  obtain ⟨_, -, h⟩ := bindX h
  obtain ⟨_, -, h⟩ := bindX h
  obtain ⟨_, -, h⟩ := bindX h
  obtain ⟨_, -, h⟩ := bindX h
  obtain ⟨_, -, h⟩ := bindX h
  obtain ⟨_, -, h⟩ := bindX h
  obtain ⟨g, hg, h⟩ := bindX h
  obtain ⟨d, hd, h⟩ := bindX h
  cases h
  exact (coreStill_same.join g.2 d _ _ _ (namedX hd)).1.trans
    (coreStill_same.newGroup m.d g.2 _ _ g.1 (namedX hg)).1

/-- **The two sendings, one behind the other, from the chain's start.** -/
theorem two_sendings {one : OneTime} {Np : VerifiableInference.Desc.Key.Pieces}
    {gI gB : List (List ℕ)} {s1 s2 : FirstState} {q₁ q₂ p₁ p₂ : Fmt.RoundView}
    {gs0 gs1 : List (List (ℕ × List UInt64))}
    (h0 : (sendIndexMasks (Cl := Claim) one Np gI).decide (chainStart one.codes {}) [q₁, q₂] gs0 =
      .ok s1)
    (h1 : (sendOwnMessage (Cl := Claim) one Np gB).decide s1 [p₁, p₂] gs1 = .ok s2) :
    ∃ layI layB, layTrees one.codes #[one.indexMasks] = some layI ∧
      layTrees one.codes (Wf.messageOf one.ranges) = some layB ∧
      seatsB (laidSeats 1 layI.shapes.size (Wf.messageOf one.ranges) layB) s2.d.book = true := by
  obtain ⟨m0, hk0, hq0⟩ := bindX h0
  obtain ⟨ids0, d0, hd0, -, eb0, -⟩ := seat_core hk0
  obtain ⟨i0, -, hq0⟩ := bindX hq0
  cases hq0
  obtain ⟨layI, hlI, hbI, -⟩ := sent_book hd0
  obtain ⟨m1, hk1, hq1⟩ := bindX h1
  obtain ⟨ids1, d1, hd1, -, eb1, -⟩ := seat_core hk1
  obtain ⟨layB, hlB, hbB, -⟩ := sent_book hd1
  have eo := open_book (show openRangesGroup one m1 = .ok s2 from hq1)
  rw [sent_par] at hlI hlB hbI hbB
  refine ⟨layI, layB, hlI, hlB, ?_⟩
  have hl := (Own.treesMade_gives (by rw [Own.treesMade_eq]; exact hlB)).2.1
  have hb0 := eb0.trans hbI
  have e1 : m0.d.book.place.size = 1 := by
    rw [hb0, (recvBook_counts _ _ _ _ _ _).1]
    rfl
  have e2 : m0.d.book.trees.size = layI.shapes.size := by
    rw [hb0, (recvBook_counts _ _ _ _ _ _).2]
    exact Nat.zero_add _
  have key : ∀ ft n r, seatsB (laidSeats 1 layI.shapes.size (Wf.messageOf one.ranges) layB)
      (recvBook ft m0.d.book (Wf.messageOf one.ranges) layB n r) = true := fun ft n r => by
    have h := seatsB_new ft m0.d.book (Wf.messageOf one.ranges) layB n r hl
    rwa [e1, e2] at h
  rw [eo, eb1, hbB]
  exact key _ _ _

variable {X : Source} {N : H2U.PlaceNums} {P : VerifiableInference.Desc.Key.LaterPlaces}

/-- **BEHIND THE TWO SENDINGS THE BOOK CARRIES THE SECOND SENDING's LAYOUT.** -/
theorem seats_two (D : WholeD) (a) (h : Hist₁ (VerifiableInference.Desc.Key.descriptionFromSource X N P) D 2 a) :
    ∃ layI layB, layTrees X.Y.k.oneTime.codes #[X.Y.k.oneTime.indexMasks] = some layI ∧
      layTrees X.Y.k.oneTime.codes (Wf.messageOf X.Y.k.oneTime.ranges) = some layB ∧
      seatsB (laidSeats 1 layI.shapes.size (Wf.messageOf X.Y.k.oneTime.ranges) layB)
        (show FirstState from a.2).d.book = true := by
  obtain ⟨a1, b1, rs1, cols1, hr1, hb1, hd1, hf1⟩ := Reached.last (k := 1) h
  obtain ⟨a0, b0, rs0, cols0, hr0, hb0, hd0, hf0⟩ := Reached.last (k := 0) hr1
  rw [List.getElem?_map] at hb1 hb0
  obtain ⟨c1, hc1, rfl⟩ := Option.map_eq_some_iff.1 hb1
  obtain ⟨c0, hc0, rfl⟩ := Option.map_eq_some_iff.1 hb0
  obtain ⟨-, hy1⟩ := VerifiableInference.Desc.Plain.held_decide c1 a1 _ _ a hd1
  obtain ⟨-, hy0⟩ := VerifiableInference.Desc.Plain.held_decide c0 a0 _ _ a1 hd0
  obtain ⟨p₁, p₂, rfl⟩ := fk_two₁ X N P c1 hc1 hf1
  obtain ⟨q₁, q₂, rfl⟩ := fk_two₀ X N P c0 hc0 hf0
  obtain ⟨gI, hgI⟩ := fk_idx_at X N P
  obtain ⟨gB, hgB⟩ := fk_msg_at X N P
  obtain rfl := Option.some.inj (hgI.symm.trans hc0)
  obtain rfl := Option.some.inj (hgB.symm.trans hc1)
  have hs0 : a0.2 = chainStart X.Y.k.oneTime.codes {} := hr0
  rw [hs0] at hy0
  exact two_sendings hy0 hy1

end Johnson.RunOne.Law.BookAt2

#print axioms Johnson.RunOne.Law.BookAt2.seat_core
#print axioms Johnson.RunOne.Law.BookAt2.sent_book
#print axioms Johnson.RunOne.Law.BookAt2.open_book
#print axioms Johnson.RunOne.Law.BookAt2.two_sendings
#print axioms Johnson.RunOne.Law.BookAt2.seats_two
