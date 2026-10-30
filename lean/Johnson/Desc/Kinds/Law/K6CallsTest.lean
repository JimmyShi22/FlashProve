-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/K6CallsTest.lean: TWO TESTS WITH CODE ON PUBLIC PARAMETERS ALONE
(callsSeatedC, maskMeetsC), AND WHAT THEIR ACCEPTS GIVE: three premises of the law of the output
head's own rounds at the composed meaning, in these premises' own words: CallsSeated
(Law/HeadSymsMeet.lean) at any columns that lie in the matrices up to number NHf + 3, and the clause
on the mask row of CallerMeets (Law/K6WorthAtMgAll.lean). Definitions with code and theorems.

Why. Both premises tie the public parameters that the caller of the lookup argument on the head's
calls reads to the table's own. They read no state of the verifier. Two of their clauses speak of
all pairs of numbers, or of every element of an array: so they cannot be evaluated as they stand.
The first follows from one equation on the member's number; the second from another file's test by
blocks (Law/PlanK6ByBlocks.lean: insideB, inMsg_of_inside: called).

What is said. Parameters: arr, msR, N (the table's) · Wp, lay, num · D (what the caller reads), rad,
i (the segment) · seatN (the caller's seat of member number k).
  memberOf D i born msg   the number, in the caller's list, of the message msg that segment born
      first sent: behind the kept ones if born is i; else the kept copy's number.
  sitsC k n ok         member k is there; ok accepts its shape; its seat is a tenant of segment 24's
      group with the number n; the first member of the table's list at that seat has its shape.
  callC a              at matrix number a of the head's list, if its label names an array of the
      layout: the segment's list of arrays names that array at the matrix's number; memberOf
      answers k; sitsC k at the message's number and at insideB.
  **callsSeatedC**     THE FIRST TEST: callC at every matrix up to number NHf + 3.
  **maskMeetsC n ns**  THE SECOND: the segment's first message with mask rows is there; just one
      tenant has the number n; sitsC at its member, at n: it has a mask row, and its mask code is
      long enough for ns entries.
  **calls_of_C**, **mask_of_C**   what the accepts give.

WHAT THE TESTS READ: PUBLIC PARAMETERS ALONE. They walk the matrices and the arrays' blocks, not the
elements.
Every letter under "there is" (they are the premises' own): k (pinned by memberOf), hk (by the
list's length), x and xt (by seatN), y (by the table's list, searched by seat), m0 (by the list of
messages).
What it does not say. That either test accepts anywhere. One way alone. The full size alone (24 is a
literal). Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.HeadSymsMeet
import Johnson.Desc.Kinds.Law.PlanK6ByBlocks
import Johnson.Desc.Kinds.Law.K6SeatsTest

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.AtFold

open OnBytes OnBytes.Params
open Johnson.Pack (pMain pMask)
open VerifiableInference.Desc renaming arrayOf → arrayOfD, laidAt → laidAtD
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.First.Look (Sent sigListCalls keptAt bornAt messagesAt)
open VerifiableInference.Desc.Sound (Mem namedOnce seatOf InMsg)
open VerifiableInference.Desc.Kinds.Head.Law.OffPad (insideB inMsg_of_inside)

/-- The number, in the caller's list, of the message msg that segment born first sent. -/
def memberOf (D : Sent) (i born msg : Nat) : Option Nat :=
  if born == i then some ((keptAt D i).length + msg) else (bornAt D i).idxOf? (born, msg)

section
variable (arr : Nat → Nat → Nat) (msR : List Mem) (N : Numbers)
  (Wp : OnBytes.Model.Verify.Public) (lay : ReqLayout) (num : Nat → Nat → Nat) (D : Sent)
  (rad : OracleShape → Nat) (i : Nat) (seatN : Nat → Nat × Nat)

/-- Member k is there, ok accepts its shape, and it sits as the table has it, with the number n. -/
def sitsC (k n : Nat) (ok : OracleShape → Bool) : Bool :=
  ((sigListCalls D rad i)[k]?).any fun e =>
    ok e.1 && (N.group 24).contains (seatN k) &&
      Decidable.decide (arr (seatN k).1 (seatN k).2 = n) &&
      (msR.find? fun y => Decidable.decide (seatOf y = seatN k)).any fun y =>
        Decidable.decide (e.1 = (y.1.l.get y.2).1)

variable {arr msR N D rad i seatN} in
theorem sits_of_C {k n : Nat} {ok : OracleShape → Bool}
    (h : sitsC arr msR N D rad i seatN k n ok = true) :
    ∃ (hk : k < (sigListCalls D rad i).length) (y : Mem),
      ok ((sigListCalls D rad i).get ⟨k, hk⟩).1 = true ∧ seatN k ∈ N.group 24 ∧
      arr (seatN k).1 (seatN k).2 = n ∧
      (msR.find? fun y => Decidable.decide (seatOf y = seatN k)) = some y ∧
      ((sigListCalls D rad i).get ⟨k, hk⟩).1 = (y.1.l.get y.2).1 := by
  unfold sitsC at h
  obtain ⟨e, he, h1⟩ := any_some h
  obtain ⟨hk, hg⟩ := List.getElem?_eq_some_iff.1 he
  replace h1 := Eq.mp (Bool.and_eq_true _ _) h1
  obtain ⟨h2, h3⟩ := h1
  replace h2 := Eq.mp (Bool.and_eq_true _ _) h2
  obtain ⟨h4, h5⟩ := h2
  replace h4 := Eq.mp (Bool.and_eq_true _ _) h4
  obtain ⟨y, hy, h6⟩ := any_some h3
  have eg : (sigListCalls D rad i).get ⟨k, hk⟩ = e := hg
  refine ⟨hk, y, by rw [eg]; exact h4.1, by simpa using h4.2, of_decide_eq_true h5, hy, ?_⟩
  rw [eg]
  exact of_decide_eq_true h6

/-- The test at matrix number a of the head's list. -/
def callC (a : Nat) : Bool :=
  match arrayOfD lay (Meaning.ownerK (Meaning.labAt Wp 24 a))
      (Meaning.nameOf (Meaning.ownerA (Meaning.labAt Wp 24 a))) with
  | none => true
  | some A =>
    ((D.arrayOf.getD i #[])[(Meaning.tlAt Wp 24).gtTree.getD a 0]? ==
        some (Meaning.ownerK (Meaning.labAt Wp 24 a),
          Meaning.nameOf (Meaning.ownerA (Meaning.labAt Wp 24 a)))) &&
      (memberOf D i (Meaning.ownerK (Meaning.labAt Wp 24 a)) A.message).any fun k =>
        sitsC arr msR N D rad i seatN k (num (Meaning.ownerK (Meaning.labAt Wp 24 a)) A.message)
          fun s => insideB D.codes s A

/-- **THE FIRST TEST.** -/
def callsSeatedC : Bool :=
  (List.range (Meaning.sizesOf Wp 24).NM).all fun a =>
    Decidable.decide (Wp.hS.NHf + 3 < a) || callC arr msR N Wp lay num D rad i seatN a

/-- **THE SECOND TEST.** -/
def maskMeetsC (n ns : Nat) : Bool :=
  ((messagesAt D i).findIdx? fun z => z.shape.maskRows != 0).any fun m0 =>
    namedOnce arr N 24 n &&
      sitsC arr msR N D rad i seatN ((keptAt D i).length + m0) n fun s =>
        Decidable.decide (0 < s.maskRows) &&
          (ns == 0 || Decidable.decide (ns - 1 < (pMask D.codes s).ell))

variable {arr msR N Wp lay num D rad i seatN}

/-- **What the first test's accept gives.** -/
theorem calls_of_C (h : callsSeatedC arr msR N Wp lay num D rad i seatN = true)
    (Cols : Nat → Nat → Prop) (hC : ∀ a c, Cols a c → a ≤ Wp.hS.NHf + 3) :
    CallsSeated Cols arr msR N Wp lay num D rad i (fun j => seatN j.1) := by
  intro μ c _ hcol A hA
  unfold callsSeatedC at h
  rw [List.all_eq_true] at h
  have h1 := h μ.val (List.mem_range.2 μ.isLt)
  rw [Bool.or_eq_true, decide_eq_true_eq] at h1
  have h2 : callC arr msR N Wp lay num D rad i seatN μ.val = true :=
    h1.resolve_left (by have := hC _ _ hcol; omega)
  unfold callC at h2
  rw [hA] at h2
  dsimp only at h2
  replace h2 := Eq.mp (Bool.and_eq_true _ _) h2
  obtain ⟨k, hm, h3⟩ := any_some h2.2
  obtain ⟨hk, y, s1, s2, s3, s4, s5⟩ := sits_of_C h3
  refine ⟨k, hk, seatN k, y, eq_of_beq h2.1, ?_, ?_, rfl, s5, s2, s3, s4⟩
  · intro rp
    unfold memberOf at hm
    by_cases hb : (Meaning.ownerK (Meaning.labAt Wp 24 μ.val) == i) = true
    · rw [if_pos hb] at hm ⊢
      rw [Option.some.inj hm]
    · rw [if_neg hb] at hm ⊢
      rw [hm]
      rfl
  · intro r c' rp hl
    have hin : InMsg D.codes ((sigListCalls D rad i).get ⟨k, hk⟩).1 false rp.1 rp.2 :=
      inMsg_of_inside D.codes s1 (i := r) (c := c') hl
    unfold InMsg at hin
    rw [if_neg (by decide)] at hin
    exact hin

/-- **What the second test's accept gives.** -/
theorem mask_of_C {n ns : Nat} (h : maskMeetsC arr msR N D rad i seatN n ns = true) :
    ∃ (m0 : Nat) (hk : (keptAt D i).length + m0 < (sigListCalls D rad i).length) (xt : Nat × Nat)
      (y : Mem),
      ((messagesAt D i).findIdx? fun z => z.shape.maskRows != 0) = some m0 ∧
      0 < ((sigListCalls D rad i).get ⟨(keptAt D i).length + m0, hk⟩).1.maskRows ∧
      (∀ j, j < ns → j < (pMask D.codes ((sigListCalls D rad i).get
        ⟨(keptAt D i).length + m0, hk⟩).1).ell) ∧
      seatN ((keptAt D i).length + m0) = xt ∧
      ((sigListCalls D rad i).get ⟨(keptAt D i).length + m0, hk⟩).1 = (y.1.l.get y.2).1 ∧
      namedOnce arr N 24 n = true ∧ xt ∈ N.group 24 ∧ arr xt.1 xt.2 = n ∧
      (msR.find? fun y => Decidable.decide (seatOf y = xt)) = some y := by
  unfold maskMeetsC at h
  obtain ⟨m0, hm, h1⟩ := any_some h
  replace h1 := Eq.mp (Bool.and_eq_true _ _) h1
  obtain ⟨hk, y, s1, s2, s3, s4, s5⟩ := sits_of_C h1.2
  replace s1 := Eq.mp (Bool.and_eq_true _ _) s1
  refine ⟨m0, hk, _, y, hm, of_decide_eq_true s1.1, ?_, rfl, s5, h1.1, s2, s3, s4⟩
  intro j hj
  rcases Eq.mp (Bool.or_eq_true _ _) s1.2 with e | e
  · have e0 : ns = 0 := eq_of_beq e
    omega
  · have e1 := of_decide_eq_true e
    omega

end

end VerifiableInference.Desc.Kinds.Head.Law.AtFold

#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.calls_of_C
#print axioms VerifiableInference.Desc.Kinds.Head.Law.AtFold.mask_of_C
