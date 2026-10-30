-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No state of the verifier and no list of rounds is shown at which the
premises of these lemmas hold; none of the tests has been evaluated.
Johnson/Desc/First/Look/K3MaskOkTools.lean: the lookups: TOOLS FOR "WHO PAYS MaskOk AND MaskOkCalls"
(Johnson/Desc/First/Look/K3DigitsMask.lean, K3CallsMask.lean): small lemmas ON ONE STATE s of the
verifier, and the tests on the list of rounds, with what a yes of them says. Definitions with code,
statements and proofs. Ties of texts: no error term. NO SOUNDNESS IS CLAIMED.

Why so. The lemmas name neither "reached" nor the table of joints' promise: so they turn with
neither.

OBJECT: no sub-protocol's text: readers of the verifier's state; functions of the list of rounds.
USER: K3CallsMaskOk.lean, K3DigitsMaskOk.lean.
LETTERS: all free.


Compiled with the whole library.


Main names:
  `segAt_parts`: what segAt? reads of s. `live_of_link`: the live copy is the open link's.
  `frameIs_of`: FrameIs from four plain equations on a frame.
  `book_place`, `seatAt_of`: the book places message o at the listed seat: from bookAt (a conjunct
    of the promise), atFirstSeats (FoldFacts.seatsCarried) and two tests.
  `rowBits_zero`: the mask table of message o has one row: from bookAt, atFirstShapes
    (FoldFacts.msgShapes) and a test.
  `ns_of_free`: freeAboveB n s says that the ledger has n slots.
  THE TESTS (kM: the mask message's number in the lookup's list; o: its number in the statement;
  seatN: the seats as a function of the number in the list): `bookedB`: o lies below the number of
    messages that are sent at the place · `seatNoB`: the listed seat of message o is the list's
    seat, and it lies in own · `oneMaskRowB`: the listed shape of message o has at most one mask
    row · `maskTestsB`: all together, with "the mask message is one of the link's own, and o is its
    number" · `maskTests_yes`.
  ON THE TABLE's LIST OF MEMBERS: `oneShapeB`: any two members at one seat have one shape ·
    `memAt_of_some`: MemAt (Johnson/Desc/First/Att/K05MsgTieAt.lean) from "some member is alike" and
    that test.

Limits. None of the tests has been evaluated.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05MsgTieAt
import Johnson.Desc.First.Att.K05SeatsOne
import Johnson.Desc.First.Att.Door.DoorBools
import Johnson.Desc.K12.Door.MsgShapes
import Johnson.Desc.First.Batch.FormsIn
import Johnson.Desc.Sound.PinMove

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles
open OnBytes OnBytes.Model OnBytes.Params
open VerifiableInference.Desc.K9 (seatAt segAt?)
open VerifiableInference.Desc.Sound (Mem Alike)
open VerifiableInference.Desc.First (Numbers bookAt)
open VerifiableInference.Desc.First.Look
open VerifiableInference.Desc.First.Att.P (FrameIs MemAt born_of_groups)

/-! ## On one state -/

/-- What segAt? reads. -/
theorem segAt_parts {s : Desc.First.S} {a : Desc.K9.Part} (h : segAt? s = some a) :
    s.link? = some a.L ∧ s.fork? = some a.F ∧ a.d.st = s.st ∧ a.d.book = s.book := by
  unfold segAt? at h
  cases hL : s.link? with
  | none => simp [hL] at h
  | some L =>
    cases hF : s.fork? with
    | none => simp [hL, hF] at h
    | some F =>
      cases ht : s.tl? with
      | none => simp [hL, hF, ht] at h
      | some tl =>
        simp [hL, hF, ht] at h
        rw [← h]
        exact ⟨rfl, rfl, rfl, rfl⟩

/-- The live copy is the open link's. -/
theorem live_of_link {s : Desc.First.S} {L : LinkCtx} (h : s.link? = some L) :
    s.live = L.check := by
  unfold Desc.First.S.live
  rw [h]

/-- FrameIs, from four plain equations. -/
theorem frameIs_of {D : Sent} {i : ℕ} {f : ReqFrame} (hshape : f.shape = D.shape)
    (hgroups : f.groups = reqGroups f.shape) (hlink : f.link = i)
    (hnext : f.next = .laterOrClose) : FrameIs D i f :=
  ⟨hshape, born_of_groups (by rw [hgroups, hshape]) hlink, hlink, hnext⟩

section
variable {s : Desc.First.S} {N : Numbers} {p : Option Desc.Place} {o : ℕ}

/-- What bookAt says of the two sizes. -/
theorem bookAt_sizes (h : bookAt N p s = true) :
    s.book.place.size = s.st.oracles.size ∧ s.st.oracles.size = N.msgsAt p := by
  unfold bookAt at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.2, h.2⟩

/-- The book places message o at the listed seat. -/
theorem book_place {Ld : Desc.K12.Door.Laid} {z : ℕ × ℕ} (hbook : bookAt N p s = true)
    (hseats : Desc.K12.Door.atFirstSeats Ld s = true) (hlt : o < N.msgsAt p)
    (hpl : Ld.places[o]? = some z) : s.book.place[o]? = some z := by
  obtain ⟨b1, b2⟩ := bookAt_sizes hbook
  have hoB : o < s.book.place.size := by
    rw [b1, b2]
    exact hlt
  unfold Desc.K12.Door.atFirstSeats Desc.K12.Door.seatsCarriedB at hseats
  simp only [Bool.and_eq_true] at hseats
  have e : s.book.place.toList = Ld.places.take s.book.place.size := eq_of_beq hseats.1.1.1
  rw [← Array.getElem?_toList, e, List.getElem?_take_of_lt hoB]
  exact hpl

/-- So the reader by seat finds it, where the seat lies in own. -/
theorem seatAt_of {own : List (ℕ × ℕ)} {B : TreeBook} {z : ℕ × ℕ} (hp : B.place[o]? = some z)
    (hin : own.contains z = true) : seatAt own B o = some z := by
  unfold seatAt
  rw [hp]
  show (if own.contains z then some z else none) = _
  rw [if_pos hin]

/-- The listed shape of message o has at most one mask row. -/
def oneMaskRowB (M : List OracleShape) (o : ℕ) : Bool :=
  (M[o]?).all fun sh => decide (sh.rows .mask ≤ 1)

/-- The mask table of message o has one row. -/
theorem rowBits_zero {M : List OracleShape} (hbook : bookAt N p s = true)
    (hshapes : Desc.K12.Door.atFirstShapes M s = true) (hlt : o < N.msgsAt p)
    (h1 : oneMaskRowB M o = true) : s.st.rowBits o .mask = 0 := by
  obtain ⟨-, b2⟩ := bookAt_sizes hbook
  have hoS : o < s.st.oracles.size := by
    rw [b2]
    exact hlt
  have hsh := Desc.K12.Door.msgShape_at hshapes o hoS
  unfold Statement.rowBits
  cases hx : s.st.oracles[o]? with
  | none => rfl
  | some y =>
    rw [hx] at hsh
    unfold oneMaskRowB at h1
    rw [← hsh] at h1
    have h2 : y.shape.rows .mask ≤ 1 := of_decide_eq_true h1
    show ceilLog2 (y.shape.rows .mask) = 0
    unfold ceilLog2
    rw [if_pos h2]

/-- freeAboveB n s says that the ledger has n slots. -/
theorem ns_of_free {n : ℕ} {F : Fork} (h : H2K5.Door.freeAboveB n s = true)
    (hF : s.fork? = some F) : F.ns = n := by
  unfold H2K5.Door.freeAboveB at h
  rw [Bool.and_eq_true, hF] at h
  simpa using h.1

end

/-! ## The tests on the list of rounds -/

/-- o lies below the number of messages that are sent at the place. -/
def bookedB (N : Numbers) (p : Option Desc.Place) (o : ℕ) : Bool := decide (o < N.msgsAt p)

/-- The listed seat of message o is the list's seat, and it lies in own. -/
def seatNoB (Ld : Desc.K12.Door.Laid) (own : List (ℕ × ℕ)) (seatN : ℕ → ℕ × ℕ) (kM o : ℕ) : Bool :=
  Ld.places[o]? == some (seatN kM) && own.contains (seatN kM)

/-- Any two members of the table's list at one seat have one shape. -/
def oneShapeB (ms : List Mem) : Bool :=
  ms.all fun y => ms.all fun y' =>
    !Decidable.decide (Desc.Sound.seatOf y = Desc.Sound.seatOf y') ||
      (y.1.l.get y.2).1 == (y'.1.l.get y'.2).1

/-- **MemAt, from "some member is alike" and "one seat, one shape".** -/
theorem memAt_of_some {ms : List Mem} {l : List (OracleShape × ℕ)} {seat : Fin l.length → ℕ × ℕ}
    {k : Fin l.length} (h : ∃ y ∈ ms, Alike y ⟨⟨l, seat⟩, k⟩) (h6 : oneShapeB ms = true) :
    MemAt ms l seat k := by
  obtain ⟨y, hy, he, hs⟩ := h
  have he' : y.1.l.get y.2 = l.get k := he
  have hs' : Desc.Sound.seatOf y = seat k := hs
  have hsome : (ms.find? fun y => Decidable.decide (Desc.Sound.seatOf y = seat k)).isSome = true :=
    List.find?_isSome.2 ⟨y, hy, decide_eq_true hs'⟩
  obtain ⟨y', hy'⟩ := Option.isSome_iff_exists.1 hsome
  have hm : y' ∈ ms := List.mem_of_find?_eq_some hy'
  have hp0 :=
    List.find?_some (p := fun y => Decidable.decide (Desc.Sound.seatOf y = seat k)) hy'
  have hp : Desc.Sound.seatOf y' = seat k := by simpa using hp0
  refine ⟨y', hy', ?_⟩
  simp only [oneShapeB, List.all_eq_true] at h6
  have t := h6 y' hm y hy
  have t2 : (y'.1.l.get y'.2).1 = (y.1.l.get y.2).1 := by
    simpa [hp.trans hs'.symm] using t
  rw [t2, he']

/-- **All together.** kM?: the mask message's number in the lookup's list; kept: how many kept
messages stand in front in that list; nos: the planned numbers, in the statement, of the link's own
messages. -/
def maskTestsB (kM? : Option ℕ) (kept : ℕ) (nos : Array ℕ)
    (N : Numbers) (p : Option Desc.Place) (Ld : Desc.K12.Door.Laid) (M : List OracleShape)
    (own : List (ℕ × ℕ)) (seatN : ℕ → ℕ × ℕ) : Bool :=
  kM?.any fun kM =>
    (nos[kM - kept]?).any fun o =>
      decide (kept ≤ kM) && bookedB N p o && seatNoB Ld own seatN kM o && oneMaskRowB M o

/-- What a yes says. -/
theorem maskTests_yes {kM? : Option ℕ} {kept : ℕ} {nos : Array ℕ}
    {N : Numbers} {p : Option Desc.Place} {Ld : Desc.K12.Door.Laid} {M : List OracleShape}
    {own : List (ℕ × ℕ)} {seatN : ℕ → ℕ × ℕ}
    (h : maskTestsB kM? kept nos N p Ld M own seatN = true) :
    ∃ kM o, kM? = some kM ∧ kept ≤ kM ∧ nos[kM - kept]? = some o ∧ o < N.msgsAt p ∧
      Ld.places[o]? = some (seatN kM) ∧ own.contains (seatN kM) = true ∧
      oneMaskRowB M o = true := by
  unfold maskTestsB at h
  cases hk : kM? with
  | none =>
    rw [hk] at h
    cases h
  | some kM =>
    rw [hk] at h
    cases ho : nos[kM - kept]? with
    | none =>
      simp only [Option.any_some, ho, Option.any_none] at h
      cases h
    | some o =>
      simp only [Option.any_some, ho, Bool.and_eq_true] at h
      obtain ⟨⟨⟨t1, t2⟩, t3⟩, t4⟩ := h
      unfold bookedB at t2
      unfold seatNoB at t3
      rw [Bool.and_eq_true] at t3
      exact ⟨kM, o, rfl, of_decide_eq_true t1, ho, of_decide_eq_true t2, eq_of_beq t3.1, t3.2, t4⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.book_place
#print axioms VerifiableInference.OnPublicFiles.rowBits_zero
#print axioms VerifiableInference.OnPublicFiles.memAt_of_some
#print axioms VerifiableInference.OnPublicFiles.maskTests_yes
