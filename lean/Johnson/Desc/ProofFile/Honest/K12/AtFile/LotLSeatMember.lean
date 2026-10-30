-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLSeatMember.lean

It states no goal. No property of the protocol is claimed.

The group under test at the first chain's
closing proximity test (member 354, group 25) has ONE member, the oracle message number 185; it sits
at tree 76, tenant 0, and has the written shape `H2K12.shL` (two main rows of degree 3, no mask row).
At every state without a mark that is reached by the members' own steps at border 354 and at which the
promise's test `membersHeld` says yes.

  `eq_singleton_of_nodup`      a list without repeats, whose members all are a, and which holds a
  `messageAtListedPlace`       at letters: a message whose place in the book is the listed place of
                               a number IS that number, has that seat, and has the listed shape
  `membersAtOnePlace`          at letters: where one pin's tenant is open, every member of the group
                               has that place in the book, and some member has it
  `placesWritten`, `shapesWritten`   the written lists of places and of shapes
  `shapeAt185`, `shapeAt186_no`      the closed line and its control, by Lean's kernel
  `writtenAtHead`              the four equations of `H2K12.Written354` under the head
  `closingMemberAtReach`       the statement

By what. `foldFacts_raw` (Honest/Thread/ReachFacts.lean): the book is in order, the seats are
carried, the book fits, the messages' shapes are the listed ones, the statement is tidy.
`members_placed`, `place_listed`, `bookOrd_of` (Johnson/Loose/H2K12/Promise354.lean); `pins_354`
(PublicAt354.lean); `sent_of`, `index_full`, `psFull_apart`, `laid_full`, `msgs_full`, `rise_full`
(ClosedOfPins354.lean); `GroupOk.nodup`, `GroupOk.there` (Johnson/Desc/Means/Says.lean).

Hypotheses of `closingMemberAtReach`. h: the library's head at the format's second hash function. hr: the state
is reached at border 354. hfail: it bears no mark. hmem: the promise's test on the groups' members.
hG: group 25 is G.

Limits.
- The full size alone.
- hmem is a clause of the promise: a thread's stand gives it (LotLSeatAtStand.lean); a bare reach does
  not.
- No closed shape of the state at 354 is used or made.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.ProofFile.Honest.K12.AtProof.FieldsAtFinish
import Johnson.Loose.H2K12.ClosedOfPins354
import Johnson.Loose.H2K12.Promise354
import Johnson.Loose.H2K12.PublicAt354
import Johnson.Desc.Sound.BookTestsLaw
import Johnson.Desc.Sound.TabAt
import Johnson.Desc.Means.Layout
import Johnson.Desc.Means.TestsBack
import Johnson.HB.LLHARD.LaidWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace ProofFile.Honest.K12.LotL
open OnBytes (Group Oracle OracleShape Statement TreeBook)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S Numbers Item membersHeld rowSegs sameMembers)
open VerifiableInference.Desc.Sound (seatBy noFirst seatBy_some bookFitsB_iff)
open VerifiableInference.Desc.K12.Door (Laid laidOf atFirstBook atFirstSeats atFirstFits atFirstShapes
  msgShapesB msgShape_at msgsOfChain)
open VerifiableInference.Desc.K13.Law (LFull laidOf_written)
open Johnson.Desc.First.Walk.Tied (Reach)
open Johnson.G (codesFull2)

/-! ## 1 At letters -/

/-- A list without repeats, whose members all are a, and which holds a, is [a]. -/
theorem eq_singleton_of_nodup {α : Type} {a : α} :
    ∀ {l : List α}, l.Nodup → (∀ x ∈ l, x = a) → a ∈ l → l = [a]
  | [], _, _, h => absurd h List.not_mem_nil
  | [x], _, hall, _ => by rw [hall x (List.mem_singleton.2 rfl)]
  | x :: y :: t, hn, hall, _ => by
    have hx : x = a := hall x List.mem_cons_self
    have hy : y = a := hall y (List.mem_cons_of_mem _ List.mem_cons_self)
    have e : x = y := hx.trans hy.symm
    exact absurd (by rw [e]; exact List.mem_cons_self) (List.nodup_cons.1 hn).1

/-- **A message whose place in the book is the listed place of a number is that number, has that
seat, and has the listed shape.** L, M: the listed places and shapes. -/
theorem messageAtListedPlace (L : Laid) (M : List OracleShape) (s : S) (q : ℕ × ℕ) (number : ℕ)
    (shape : OracleShape) (hbook : atFirstBook 0 s = true) (hseats : atFirstSeats L s = true)
    (hfits : atFirstFits s = true) (hshapes : atFirstShapes M s = true) (hapart : L.places.Nodup)
    (hat : L.places[number]? = some q) (hM : M[number]? = some shape) (o : ℕ)
    (hlt : o < s.st.oracles.size) (hq : s.book.place[o]? = some q) :
    o = number ∧ seatBy noFirst s.book o = some q ∧
      ∃ x, s.st.oracles[o]? = some x ∧ x.shape = shape := by
  have hl := H2K12.place_listed L s hseats o q hq
  have ho : o = number := by
    obtain ⟨h1, e1⟩ := List.getElem?_eq_some_iff.1 hl
    obtain ⟨h2, e2⟩ := List.getElem?_eq_some_iff.1 hat
    exact (List.Nodup.getElem_inj_iff hapart).1 (e1.trans e2.symm)
  subst ho
  obtain ⟨T, hT, -⟩ := (bookFitsB_iff s.book).1 hfits o q hq
  have hnum : T.number = q.1 := by
    have e := H2K12.bookOrd_of 0 s hbook q.1 T hT
    rw [Nat.zero_add] at e
    exact e
  refine ⟨rfl, ?_, ?_⟩
  · rw [seatBy_some noFirst s.book o q T hq hT]
    exact congrArg some (Prod.ext hnum rfl)
  · have e := msgShape_at (show msgShapesB M s.st = true from hshapes) o hlt
    rw [hM] at e
    obtain ⟨x, hx, hs⟩ := Option.map_eq_some_iff.1 e
    exact ⟨x, hx, hs⟩

/-- **Where the open pins of a segment name one tenant, every member of its group has that place in
the book, and some member has it.** -/
theorem membersAtOnePlace (N : Numbers) (O : List Item) (s : S) (n : ℕ) (hn : n ∈ rowSegs O)
    (hmem : membersHeld N O s = true) (G : Group) (hG : s.st.groups[N.groupAt n]? = some G)
    (q : ℕ × ℕ) (hpins : H2K12.pinsOpen N O n = [q]) :
    (∀ o ∈ G.members.toList, s.book.place[o]? = some q) ∧
      ∃ o ∈ G.members.toList, s.book.place[o]? = some q := by
  refine ⟨fun o ho => ?_, ?_⟩
  · obtain ⟨q', hq', hin⟩ := H2K12.members_placed N O s n hn hmem G hG o ho
    rw [hpins] at hin
    rw [hq', List.mem_singleton.1 hin]
  · have h := hmem
    unfold membersHeld at h
    have h1 := List.all_eq_true.1 h n hn
    rw [hG] at h1
    simp only [Bool.and_eq_true, sameMembers] at h1
    have hin : q ∈ H2K12.pinsOpen N O n := by
      rw [hpins]
      exact List.mem_singleton.2 rfl
    have h3 := List.all_eq_true.1 h1.2.2 q hin
    obtain ⟨o, ho, e⟩ := List.mem_filterMap.1 (List.contains_iff_mem.1 h3)
    exact ⟨o, ho, e⟩

/-! ## 2 The written lists -/

/-- The written list of places is the closed list's seats. -/
theorem placesWritten : LFull.places = P5T.psFull.map (·.seat) := by
  have h := H2K12.laid_full
  have e : laidOf codesFull2 H2K12.noticesFull = some LFull := laidOf_written
  rw [e] at h
  exact Option.some.inj h

/-- The planner's list of shapes is the closed list's. -/
theorem shapesWritten {Zp : ProofFile.Pub} (W : H2K12.Written354 Zp) :
    msgsOfChain Zp.made.proof.1 = P5T.psFull.map (·.shape) := by
  unfold msgsOfChain
  rw [W.sends, List.mergeSort_of_pairwise H2K12.rise_full]
  exact H2K12.msgs_full

/-- **The closed line**: message number 185 has the written shape. -/
theorem shapeAt185 : (P5T.psFull.map (·.shape))[185]? = some H2K12.shL := by decide +kernel

/-- The control: the next message, the fresh table, has another. -/
theorem shapeAt186_no : (P5T.psFull.map (·.shape))[186]? ≠ some H2K12.shL := by decide +kernel

/-! ## 3 Under the head -/

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}

/-- The four equations under the head. -/
theorem writtenAtHead (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) : H2K12.Written354 Zp :=
  H2K12.written354_of_pins h.scope h.laid.pub h.pins.1
    (h.laid.run ▸ LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks)

/-- **The group under test has one member, message number 185, at tree 76, tenant 0, of the written
shape; and the statement's codes are the written ones.** -/
theorem closingMemberAtReach (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {p : ProofFile.InstPub} {s : S}
    (hr : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 354 (p, s)) (hfail : s.failed = none)
    (hmem : membersHeld (P5J.At.N Zp cF) H2K12.O354 s = true) {G : Group}
    (hG : s.st.groups[25]? = some G) :
    G.members.toList = [185] ∧ seatBy noFirst s.book 185 = some (76, 0) ∧
      (∃ x, s.st.oracles[185]? = some x ∧ x.shape = H2K12.shL) ∧ s.st.codes = codesFull2 := by
  have W := writtenAtHead h
  have F := ProofFile.Honest.FirstThread.foldFacts_raw h
    (fun k (a : ProofFile.InstPub × P5J.TS) => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a) (fun a => a)
    (fun _ _ q => q) (P5J.laid_at_head h) (P5J.startB_at_head h)
    (P5J.sendsB_of_madeRow h (P5J.madeRow_at_head h))
  have hbook : atFirstBook 0 s = true := F.bookInOrder 354 (p, s) hr hfail
  have hseats : atFirstSeats LFull s = true := F.seatsCarried 354 (p, s) hr hfail
  have hfits : atFirstFits s = true := F.bookFits 354 (p, s) hr hfail
  have hshapes : atFirstShapes (msgsOfChain Zp.made.proof.1) s = true :=
    F.msgShapes 354 (p, s) hr hfail
  have hok := (OnBytes.Means.tidy4B_iff.1 (F.tidy 354 (p, s) hr hfail)).inOrder.groups 25 G hG
  have hpins : H2K12.pinsOpen (P5J.At.N Zp cF) H2K12.O354 25 = [(76, 0)] :=
    (H2K12.pins_354 _).trans (H2K12.sent_of W)
  have hG' : s.st.groups[(P5J.At.N Zp cF).groupAt 25]? = some G := hG
  obtain ⟨hall, o₁, ho₁, hq₁⟩ := membersAtOnePlace (P5J.At.N Zp cF) H2K12.O354 s 25
    H2K12.rowOpen_354 hmem G hG' (76, 0) hpins
  have hapart : LFull.places.Nodup := by
    rw [placesWritten]
    exact H2K12.psFull_apart
  have hat : LFull.places[185]? = some (76, 0) := by
    rw [placesWritten]
    exact (Prod.mk.inj H2K12.index_full).2
  have hM : (msgsOfChain Zp.made.proof.1)[185]? = some H2K12.shL := by
    rw [shapesWritten W]
    exact shapeAt185
  have key := fun o (ho : o ∈ G.members.toList) =>
    messageAtListedPlace LFull _ s (76, 0) 185 H2K12.shL hbook hseats hfits hshapes hapart hat hM o
      (hok.there o ho) (hall o ho)
  obtain ⟨e₁, hs₁, hx₁⟩ := key o₁ ho₁
  subst e₁
  refine ⟨eq_singleton_of_nodup hok.nodup (fun o ho => (key o ho).1) ho₁, hs₁, hx₁, ?_⟩
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hp : ∀ b ∈ cF.blocksInOrder, b.planOk = true := _root_.Meaning.K2.flat_planOk O.desc h.laid.planOk
  have e := _root_.Meaning.K2.codes_field h.scope h.reads O hp _ id (fun _ _ q => q) 354 (p, s) hr
    hfail
  exact e.trans W.codes

end ProofFile.Honest.K12.LotL

#print axioms ProofFile.Honest.K12.LotL.eq_singleton_of_nodup
#print axioms ProofFile.Honest.K12.LotL.messageAtListedPlace
#print axioms ProofFile.Honest.K12.LotL.membersAtOnePlace
#print axioms ProofFile.Honest.K12.LotL.placesWritten
#print axioms ProofFile.Honest.K12.LotL.shapesWritten
#print axioms ProofFile.Honest.K12.LotL.shapeAt185
#print axioms ProofFile.Honest.K12.LotL.shapeAt186_no
#print axioms ProofFile.Honest.K12.LotL.writtenAtHead
#print axioms ProofFile.Honest.K12.LotL.closingMemberAtReach
