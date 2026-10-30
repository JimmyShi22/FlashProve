-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K5/Law/NumsCover.lean: THE TWO WAYS OF NUMBERING THE WITNESS's
MESSAGES MEET AT EVERY OWN MESSAGE OF EVERY LINK: by tree and tenant (`P5T.arrOf`, `P5J.At.arr`) and
by link and number in the link's list (`P5T.numOfPlan`, `P5J.At.num`); AND THE SECOND PARTS ANY TWO
OWN MESSAGES. On public data alone. For every kind of sub-protocol: no kind is named. One definition
with code; six theorems: two general, one closed fact by evaluation in Lean's kernel, three
CONDITIONAL under the structure of conditions `P5J.AtMg` (Johnson/P5J/AtMg.lean).

What it is for. Whoever lays a lot of a message by its tree and tenant, and whoever lays one by its
link and number, must meet at one number, or "the lots agree" is idle. The library has the meeting
at one place (`AtMg.mask_num`, Johnson/HB/LLHARD/MaskSeatWritten.lean) and, by the test `coverB`
(Johnson/P5T/KeyIsMessage.lean), at every message that holds an array of the layout. A message with
a mask row need hold none.

Main names:
  `P5T.coverMsgsB s ps`: A TEST WITH CODE: `coverB`'s text with "every array of every link" turned
    to "every own message of every link of the shape s": it has a seat with the key (0, l, k),
    whose tree and tenant are first held by a seat of that key.
  `P5T.coverMsgs_gives`: what the test gives: such a seat p; `arrOf` at p's tree and tenant IS
    `numOfPlan ps l k`; and that is the place of a key that is there, not "the number of keys".
  `P5T.num_apart_of_cover`: under the test `numOfPlan` gives an own message's number to no other
    pair.
  `P5T.coverMsgs_written`: THE CLOSED FACT: the test accepts at the library's written shape and
    seats (25 links, 99 own messages, 225 seats: by an evaluation outside this file; no theorem).
  `AtMg.coverMsgs`, `AtMg.arr_is_num`, `AtMg.num_apart`: the three at `Zp.first.shape`,
    `At.pseatsAll Zp`, `At.arr Zp` and `At.num Zp`.

How. `coverMsgs_gives`: the lines of `cover_gives`, with `arrOf_is_num`
(Johnson/P5T/NumOfPlan.lean). `num_apart_of_cover`: a place in a list without doubles names one
member. Under the structure: `AtMg.seats_written`, `AtMg.shape_written` (MaskSeatWritten.lean).

Limits. IT SPEAKS OF THE PLAN's LIST OF SEATS: that a caller's own tree and tenant ARE such a seat's
is the caller's to show. There may be several seats with one key (a kept copy bears the original's):
the test names one. THE STRUCTURE HAS A MEMBER: `AtFullSide.Top.headMember_zFull`
(AtFullSide/Top/HeadMemberAtFull.lean) gives one of `P5J.AtMgA`, which extends `AtMg`, at the
earlier hash `OnBytes.secondHashFunction` and at the library's written copy of the full-size public files, which
is tied to the package's files by no theorem: ONE EXAMPLE; at another hash no member is known to the
writer. The three under the structure open the same conditions of it as MaskSeatWritten.lean's six
(see its head, whose sentence that no member is known is overtaken). `coverMsgs_written` has been
checked by Lean's own kernel alone. Of what a message holds nothing is said.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.P5T.KeyIsMessage
import Johnson.P5T.PlanSeatsFull
import Johnson.Desc.ReqLit.Full
import Johnson.HB.LLHARD.MaskSeatWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5T
open OnBytes.Params (ReqShape ReqLink)

/-- **The test**: every own message of every link has a seat with its key, whose tree and tenant are
first held by a seat of that key. -/
def coverMsgsB (s : ReqShape) (ps : List PSeat) : Bool :=
  s.link.zipIdx.all fun x => (List.range x.1.messages.length).all fun k => ps.any fun p =>
    keyOf p == (0, x.2, k) &&
      (ps.find? fun q => q.j == p.j && q.t == p.t).map keyOf == some (0, x.2, k)

/-- **What the test gives.** -/
theorem coverMsgs_gives {s : ReqShape} {ps : List PSeat} (h : coverMsgsB s ps = true) {l : Nat}
    {Lk : ReqLink} (hl : s.link[l]? = some Lk) {k : Nat} (hk : k < Lk.messages.length) :
    ∃ p ∈ ps, keyOf p = (0, l, k) ∧ arrOf ps p.j p.t = numOfPlan ps l k ∧
      numOfPlan ps l k < ((ps.map keyOf).eraseDups).length := by
  unfold coverMsgsB at h
  rw [List.all_eq_true] at h
  have hz : (Lk, l) ∈ s.link.zipIdx := by
    refine List.mem_iff_getElem?.2 ⟨l, ?_⟩
    rw [List.getElem?_zipIdx, hl]
    simp
  have h1 := List.all_eq_true.1 (h _ hz) k (List.mem_range.2 hk)
  obtain ⟨p, hp, h2⟩ := List.any_eq_true.1 h1
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h2
  obtain ⟨p₀, hp₀, hk₀⟩ := Option.map_eq_some_iff.1 h2.2
  refine ⟨p, hp, h2.1, arrOf_is_num ps p.j p.t l k p₀ hp₀ hk₀, ?_⟩
  unfold numOfPlan
  refine List.idxOf_lt_length_iff.2 ?_
  rw [List.mem_eraseDups]
  exact List.mem_map.2 ⟨p, hp, h2.1⟩

/-- **An own message shares its number with no other pair.** -/
theorem num_apart_of_cover {s : ReqShape} {ps : List PSeat} (h : coverMsgsB s ps = true) {l : Nat}
    {Lk : ReqLink} (hl : s.link[l]? = some Lk) {k : Nat} (hk : k < Lk.messages.length)
    {l' k' : Nat} (e : numOfPlan ps l k = numOfPlan ps l' k') : l = l' ∧ k = k' := by
  obtain ⟨p, hp, hkey, -, -⟩ := coverMsgs_gives h hl hk
  have h1 : (0, l, k) ∈ ((ps.map keyOf).eraseDups) :=
    List.mem_eraseDups.2 (List.mem_map.2 ⟨p, hp, hkey⟩)
  have e' : ((ps.map keyOf).eraseDups).idxOf (0, l, k) =
      ((ps.map keyOf).eraseDups).idxOf (0, l', k') := e
  have k0 := (List.idxOf_inj h1).1 e'
  exact ⟨(Prod.mk.inj (Prod.mk.inj k0).2).1, (Prod.mk.inj (Prod.mk.inj k0).2).2⟩

set_option maxRecDepth 1000000 in
/-- **At the library's written shape and seats the test accepts.** By evaluation in Lean's
kernel. -/
theorem coverMsgs_written :
    coverMsgsB VerifiableInference.Desc.ReqLit.shapeFull seatsAllFull = true := by decide +kernel

end P5T

namespace P5J
open VerifiableInference.Desc (Chain)
open OnBytes.Maker (WholeD)
open OnBytes.Params (ReqLink)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}

/-- **The test accepts at the structure's own shape and seats.** CONDITIONAL: under the
structure. -/
theorem AtMg.coverMsgs (h : AtMg o Z D r Zp Np cF) :
    P5T.coverMsgsB Zp.first.shape (At.pseatsAll Zp) = true := by
  unfold At.pseatsAll
  rw [h.shape_written, h.seats_written.2.1]
  exact P5T.coverMsgs_written

/-- **THE TWO NUMBERINGS MEET AT EVERY OWN MESSAGE OF EVERY LINK.** CONDITIONAL: under the
structure; message k of link l is there. -/
theorem AtMg.arr_is_num (h : AtMg o Z D r Zp Np cF) {l : ℕ} {Lk : ReqLink}
    (hl : Zp.first.shape.link[l]? = some Lk) {k : ℕ} (hk : k < Lk.messages.length) :
    ∃ p ∈ At.pseatsAll Zp, P5T.keyOf p = (0, l, k) ∧ At.arr Zp p.j p.t = At.num Zp l k ∧
      At.num Zp l k < (((At.pseatsAll Zp).map P5T.keyOf).eraseDups).length :=
  P5T.coverMsgs_gives h.coverMsgs hl hk

/-- **AN OWN MESSAGE SHARES ITS NUMBER WITH NO OTHER PAIR.** CONDITIONAL: as `AtMg.arr_is_num`. -/
theorem AtMg.num_apart (h : AtMg o Z D r Zp Np cF) {l : ℕ} {Lk : ReqLink}
    (hl : Zp.first.shape.link[l]? = some Lk) {k : ℕ} (hk : k < Lk.messages.length) {l' k' : ℕ}
    (e : At.num Zp l k = At.num Zp l' k') : l = l' ∧ k = k' :=
  P5T.num_apart_of_cover h.coverMsgs hl hk e

end P5J

#print axioms P5T.coverMsgs_gives
#print axioms P5T.num_apart_of_cover
#print axioms P5T.coverMsgs_written
#print axioms P5J.AtMg.coverMsgs
#print axioms P5J.AtMg.arr_is_num
#print axioms P5J.AtMg.num_apart
