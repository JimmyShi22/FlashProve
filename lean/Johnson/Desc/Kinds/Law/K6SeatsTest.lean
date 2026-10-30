-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6SeatsTest.lean: ONE TEST WITH CODE ON PUBLIC PARAMETERS ALONE (seatsK6C),
AND WHAT ITS ACCEPT GIVES AT A STATE OF THE VERIFIER WHOSE READERS ARE THE PUBLIC TERMS. Definitions
with code and theorems.

Why. The law of the output head's own rounds asks, of the verifier's state behind these rounds,
where the head's matrices and the segment's mask row are seated (Law/DataSeatedOfLaid.lean:
MatsSeated; Law/K6RecordAt.lean: RecordRest). Each such clause reads the state through five
readers: the open segment's frame (which oracle message holds an array), the statement (a message's
shape; the codes), the book of trees (a message's tree and tenant), the open segment's list of
arrays, its layout. Where each reader is known to be a term off the public parameters, the clauses
are sentences on public parameters: they can be evaluated once.

What is said. THE PUBLIC SIDE, as parameters: cs (the codes), shape (the request's shape), dS (what
has been sent in a segment: Johnson/Desc/First/FillSent.lean), Lp (the listed seats:
Johnson/Desc/K12/Door/DoorBools.lean), M (the listed shapes of the oracle messages), arrs (the
segment's list of arrays), n0 (how many oracle messages are sent in front of the border).
  listed_at            below the statement's number of messages the listed shape is the message's,
      where the messages' shapes are the first of M. (The numbers of index bits off a shape: another
      author's K9.rowBitsOf, K9.placeBitsOf with rowBits_of, placeBits_of:
      Johnson/Desc/First/Batch/Ahead.lean: called.)
  seatC, seat_of_C     message number o is sent, and the listed seat of o is a tenant of own with
      the number n; so the book seats it there, where the book's places are the first of the listed.
  matSeatC a           at matrix number a of the head's list, if its label names an array of the
      layout: the public term for the frame finds the array's message; the array fits that message's
      table; seatC.
  maskSeatC            the like for the segment's first message with mask rows; its mask table has
      2 ^ rb rows at most (rowBits = rb).
  secondC, readsC      the array of the reads is in the list arrs, and it is an array of segment
      24's own second sending.
  **seatsK6C**         THE TEST: matSeatC at every matrix up to number NHf + 3; maskSeatC; readsC.
  StateIsPlan          the five readers at a state's open segment are the public terms (nine
      equations and two tests).
  **matsSeated_of_C**, **maskSeated_of_C**, **reads_of_C**: under StateIsPlan and the test's accept:
      MatsSeated at any columns that lie in the matrices up to NHf + 3; the mask row's clause of
      RecordRest; the reads' array's name, and that it is of the second sending.

WHAT THE TEST READS: PUBLIC PARAMETERS ALONE: NO STATE OF THE VERIFIER, NO WITNESS, NO TRANSCRIPT.
Of Wp: the number NHf, the number of the head's matrices (Meaning.sizesOf Wp 24).NM, their labels
(Meaning.labAt Wp 24 a), the number of the reads' array (readsOf Wp). Of lay6: the arrays that these
labels name (message, sizes, blocks), and the reads' array's message. Of dS at segment 24: born,
own, kept (three lists of numbers). Of shape: segment 24's list of messages (mask rows; moments).
Of M: the shapes of the messages found. Of cs: the lengths of these shapes' codes. Of Lp: the
listed seats of the messages found (not the trees' shapes). Of N: the list N.sent 24 0 alone. arr
and num at these seats and messages. arrs at one number. n0. It walks the matrices (eight at the
full size), not their elements.

Every letter under "there is". In the conclusions: o (pinned by the frame), x (by the book), cU (by
the open segment's list of arrays).
What it does not say. THAT THE TEST ACCEPTS IS NO THEOREM. It has been evaluated once: at one stored
set of public files of the full size it accepts, and eight negative tests reject; there the number
of oracle messages in front of a place was laid off the planner's sendings, not through the composed
meaning's own numbers. That any state meets StateIsPlan. One way alone. The full size alone (24 is a
literal). Nothing on soundness. 
-/
import Johnson.Desc.Kinds.Law.K6RecordAt
import Johnson.Desc.First.FillSent
import Johnson.Desc.K12.Door.MsgShapes
import Johnson.Desc.First.Batch.Ahead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.AtFold

open OnBytes OnBytes.Params
open VerifiableInference.Desc renaming arrayOf → arrayOfD
open VerifiableInference.Desc.First (S Numbers)
open VerifiableInference.Desc.First.FillSent (SentData whereIsP maskP)
open VerifiableInference.Desc.K12.Door (seatsCarriedB msgShapesB msgShape_at)

/-! ## A message's shape, as listed -/

/-- Where a test holds of an optional value, the value is there. -/
theorem any_some {α : Type} {x : Option α} {p : α → Bool} (h : x.any p = true) :
    ∃ y, x = some y ∧ p y = true := by
  cases x with
  | none => cases h
  | some y => exact ⟨y, rfl, h⟩

/-- Below the statement's number of messages: the listed shape is the message's. -/
theorem listed_at {M : List OracleShape} {st : OnBytes.Statement} (h : msgShapesB M st = true)
    {o : Nat} (ho : o < st.oracles.size) : ∃ x, st.oracles[o]? = some x ∧ M[o]? = some x.shape := by
  have e := msgShape_at h o ho
  rw [Array.getElem?_eq_getElem ho] at e
  exact ⟨st.oracles[o], Array.getElem?_eq_getElem ho, e.symm⟩

/-! ## One seat -/

/-- Message number o is sent in front of the border, and its listed seat is a tenant of own with the
number n. -/
def seatC (arr : Nat → Nat → Nat) (own places : List (Nat × Nat)) (n0 o n : Nat) : Bool :=
  Decidable.decide (o < n0) &&
    (places[o]?).any fun x => own.contains x && Decidable.decide (arr x.1 x.2 = n)

theorem seatC_lt {arr : Nat → Nat → Nat} {own places : List (Nat × Nat)} {n0 o n : Nat}
    (h : seatC arr own places n0 o n = true) : o < n0 := by
  unfold seatC at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem seat_of_C {arr : Nat → Nat → Nat} {own : List (Nat × Nat)} {Lp : K12.Door.Laid}
    {n0 o n : Nat} {book : OnBytes.TreeBook} (h : seatC arr own Lp.places n0 o n = true)
    (hb : seatsCarriedB Lp book = true) (hn : book.place.size = n0) :
    ∃ x, K9.seatAt own book o = some x ∧ x ∈ own ∧ arr x.1 x.2 = n := by
  unfold seatC at h
  rw [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨ho, h2⟩ := h
  cases e : Lp.places[o]? with
  | none =>
    rw [e] at h2
    cases h2
  | some x =>
    rw [e] at h2
    have h3 : (own.contains x && Decidable.decide (arr x.1 x.2 = n)) = true := h2
    rw [Bool.and_eq_true, decide_eq_true_eq] at h3
    unfold seatsCarriedB at hb
    simp only [Bool.and_eq_true] at hb
    have e1 : book.place.toList = Lp.places.take book.place.size := eq_of_beq hb.1.1.1
    have e2 : book.place[o]? = some x := by
      rw [← Array.getElem?_toList, e1, List.getElem?_take_of_lt (by omega), e]
    refine ⟨x, ?_, by simpa using h3.1, h3.2⟩
    unfold K9.seatAt
    rw [e2]
    show (if own.contains x = true then some x else none) = some x
    rw [if_pos h3.1]

/-! ## The test -/

section
variable (arr : Nat → Nat → Nat) (N : Numbers) (Wp : OnBytes.Model.Verify.Public)
  (lay6 : ReqLayout) (num : Nat → Nat → Nat) (n rb : Nat) (cs : OnBytes.Codes) (shape : ReqShape)
  (dS : SentData) (Lp : K12.Door.Laid) (M : List OracleShape) (arrs : Array (Nat × String))
  (n0 : Nat)

/-- The test at matrix number a of the head's list. -/
def matSeatC (a : Nat) : Bool :=
  match arrayOfD lay6 (Meaning.ownerK (Meaning.labAt Wp 24 a))
      (Meaning.nameOf (Meaning.ownerA (Meaning.labAt Wp 24 a))) with
  | none => true
  | some A =>
    (whereIsP dS 24 (Meaning.ownerK (Meaning.labAt Wp 24 a)) A.message).any fun o =>
      (M[o]?).any fun sh =>
        laidMatrixOk A (K9.rowBitsOf sh .main) (K9.placeBitsOf cs sh .main) &&
          seatC arr (N.sent 24 0) Lp.places n0 o
            (num (Meaning.ownerK (Meaning.labAt Wp 24 a)) A.message)

/-- The test at the segment's mask row. -/
def maskSeatC : Bool :=
  (maskP shape dS 24).any fun o =>
    (M[o]?).any fun sh => K9.rowBitsOf sh .mask == rb && seatC arr (N.sent 24 0) Lp.places n0 o n

/-- The array of the name c is of segment 24's own second sending, by the layout and the shape. -/
def secondC (c : Nat × String) : Bool :=
  match reqArray lay6 c.1 c.2 with
  | some A =>
    c.1 == 24 &&
      match (shape.link[c.1]?).bind fun l => l.messages[A.message]? with
      | some m => m.moment == 1
      | none => false
  | none => false

/-- The array of the reads is in the list, and is of the second sending. -/
def readsC : Bool := (arrs[readsOf Wp]?).any (secondC lay6 shape)

/-- **THE TEST.** -/
def seatsK6C : Bool :=
  ((List.range (Meaning.sizesOf Wp 24).NM).all fun a =>
      Decidable.decide (Wp.hS.NHf + 3 < a) || matSeatC arr N Wp lay6 num cs dS Lp M n0 a) &&
    maskSeatC arr N n rb shape dS Lp M n0 && readsC Wp lay6 shape arrs

/-- **The five readers, at a state's open segment, are the public terms.** aK: the open segment's
part of the state s. -/
structure StateIsPlan (s : S) (aK : K9.Part) : Prop where
  seg : K9.segAt? s = some aK
  whereIs : ∀ born message, aK.L.check.frame.whereIs born message = whereIsP dS 24 born message
  link : aK.L.check.frame.link = 24
  shape : aK.L.check.frame.shape = shape
  layout : aK.L.check.rows.layout = lay6
  arrays : aK.L.arrayOf = arrs
  codes : aK.d.st.codes = cs
  msgs : msgShapesB M aK.d.st = true
  seats : seatsCarriedB Lp aK.d.book = true
  sizeB : aK.d.book.place.size = n0
  sizeS : aK.d.st.oracles.size = n0

variable {arr N Wp lay6 num n rb cs shape dS Lp M arrs n0}

/-- **Five facts a matrix, from the test.** -/
theorem matsSeated_of_C {s : S} {aK : K9.Part}
    (h : seatsK6C arr N Wp lay6 num n rb cs shape dS Lp M arrs n0 = true)
    (I : StateIsPlan lay6 cs shape dS Lp M arrs n0 s aK) (Cols : Nat → Nat → Prop)
    (hC : ∀ a c, Cols a c → a ≤ Wp.hS.NHf + 3) :
    MatsSeated Cols arr N Wp (N.sent 24 0) aK num lay6 := by
  intro μ c _ hcol A hA
  unfold seatsK6C at h
  rw [Bool.and_eq_true, Bool.and_eq_true, List.all_eq_true] at h
  have h1 := h.1.1 μ.val (List.mem_range.2 μ.isLt)
  rw [Bool.or_eq_true, decide_eq_true_eq] at h1
  have h2 : matSeatC arr N Wp lay6 num cs dS Lp M n0 μ.val = true :=
    h1.resolve_left (by have := hC _ _ hcol; omega)
  unfold matSeatC at h2
  rw [hA] at h2
  dsimp only at h2
  obtain ⟨o, e, h2⟩ := any_some h2
  obtain ⟨sh, hsh, h3⟩ := any_some h2
  replace h3 := Eq.mp (Bool.and_eq_true _ _) h3
  have ho : o < aK.d.st.oracles.size := by
    rw [I.sizeS]
    exact seatC_lt h3.2
  obtain ⟨y, y1, y2⟩ := listed_at I.msgs ho
  obtain rfl : y.shape = sh := Option.some.inj (y2.symm.trans hsh)
  obtain ⟨x, x1, x2, x3⟩ := seat_of_C h3.2 I.seats I.sizeB
  refine ⟨o, x, by rw [I.whereIs, e], ?_, x1,
    List.mem_append_left _ (List.mem_append_left _ x2), x3⟩
  rw [K9.rowBits_of _ o y .main y1, K9.placeBits_of _ o y .main y1, I.codes]
  exact h3.1

/-- **The mask row's clause, from the test.** -/
theorem maskSeated_of_C {s : S} {aK : K9.Part}
    (h : seatsK6C arr N Wp lay6 num n rb cs shape dS Lp M arrs n0 = true)
    (I : StateIsPlan lay6 cs shape dS Lp M arrs n0 s aK) :
    ∃ (o : Nat) (x : Nat × Nat), K9L.maskOracle aK.L.check.frame = some o ∧
      K9.seatAt (N.sent 24 0) aK.d.book o = some x ∧ x ∈ N.group 24 ∧ arr x.1 x.2 = n ∧
      aK.d.st.rowBits o .mask = rb := by
  unfold seatsK6C at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  have h2 := h.1.2
  unfold maskSeatC at h2
  obtain ⟨o, e, h2⟩ := any_some h2
  obtain ⟨sh, hsh, h3⟩ := any_some h2
  replace h3 := Eq.mp (Bool.and_eq_true _ _) h3
  have ho : o < aK.d.st.oracles.size := by
    rw [I.sizeS]
    exact seatC_lt h3.2
  obtain ⟨y, y1, y2⟩ := listed_at I.msgs ho
  obtain rfl : y.shape = sh := Option.some.inj (y2.symm.trans hsh)
  obtain ⟨x, x1, x2, x3⟩ := seat_of_C h3.2 I.seats I.sizeB
  refine ⟨o, x, ?_, x1, List.mem_append_left _ (List.mem_append_left _ x2), x3, ?_⟩
  · unfold K9L.maskOracle
    rw [I.shape, I.link, ← e]
    unfold maskP
    congr 1
    funext i
    exact I.whereIs 24 i
  · rw [K9.rowBits_of _ o y .mask y1]
    exact eq_of_beq h3.1

/-- **The reads' array's name, and that it is of the second sending, from the test.** -/
theorem reads_of_C {s : S} {aK : K9.Part}
    (h : seatsK6C arr N Wp lay6 num n rb cs shape dS Lp M arrs n0 = true)
    (I : StateIsPlan lay6 cs shape dS Lp M arrs n0 s aK) :
    ∃ cU, aK.L.arrayOf[readsOf Wp]? = some cU ∧ Sound.second s cU = true := by
  unfold seatsK6C at h
  rw [Bool.and_eq_true] at h
  have h2 := h.2
  unfold readsC at h2
  cases e : arrs[readsOf Wp]? with
  | none =>
    rw [e] at h2
    cases h2
  | some cU =>
    rw [e] at h2
    have h3 : secondC lay6 shape cU = true := h2
    refine ⟨cU, by rw [I.arrays, e], ?_⟩
    unfold Sound.second
    rw [I.seg]
    show (match reqArray aK.L.check.rows.layout cU.1 cU.2 with
      | some A => K9.atMoment1 aK cU A
      | none => false) = true
    rw [I.layout]
    unfold secondC at h3
    cases eA : reqArray lay6 cU.1 cU.2 with
    | none =>
      rw [eA] at h3
      cases h3
    | some A =>
      rw [eA] at h3
      show K9.atMoment1 aK cU A = true
      unfold K9.atMoment1
      rw [I.link, I.shape]
      exact h3

end

end VerifiableInference.Desc.Kinds.Head.Law.AtFold

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.matsSeated_of_C
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.maskSeated_of_C
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.reads_of_C
