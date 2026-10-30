-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/ReadingsOne.lean: TWO READINGS OF THE SYMBOLS IN A LINK's TUPLE OF ORACLE
MESSAGES ARE ONE: the lookups' closed callers' (Johnson/Desc/First/Look/K3CallerBase.lean,
K3CallerAtt.lean: symAt over seatCalls) and the meaning's (Johnson/Goal/Meaning/HidSeat.lean: symAt
over seats, off a reading by numbers; the seats off the layout by the entry's label,
Johnson/Goal/Meaning/HidSeatsOf.lean: fLay). Five definitions, eleven theorems, proved.

Why. The lookups' clauses of the meaning's row end at the integers behind THEIR symbols. The row
asks them at the integers behind OURS (ownAtF). Both readings say: symbol (entry, row of symbols,
column) is a cell of the entry's symbol array, and the array's cell lies at a row and place of an
oracle message, by the layout's blocks. They part in how they name the array (the port's list of
(link, name) by the array's number in the sub-proof's list; the entry's label) and the message (its
place in the link's own list: the kept ones, then the link's own of moment 0; a number).

  reqArray_eq_arrayOf, laidIn_eq, laidPlace_eq_laidAt   AT ALL ARGUMENTS: the two finders of an
    array and the two readers of an element's place are one function.
  seatCalls_of_label   one element's two seats, under four premises: the port's name is the label's;
    the array is there; it answers at the element; msgIn (the lookups' own,
    Johnson/Desc/First/Look/K3CallerAttReads.lean) puts its message at idx of its number.
  msgsOfTuple cs l idx m   a tuple of messages as a reading by numbers.
  syms_one   THE EQUATION OF SYMBOLS, at any seats that meet seatCalls through idx.
  entryTieB, linkTieB X D rad num idx k tl   THE PUBLIC TIES AT LINK k, AS ONE TEST WITH CODE: at
    every entry: names; the lookups' own test symArrB (the array is there, its message stands in
    link k's list, its blocks tile the entry's rows of symbols and columns and lie inside that
    message's table); the message's place is idx of its number.
  seat_of_tie   under the test: the lookups' seat of every element within the sizes is the seat by
    the label, AND IT LIES IN ITS TABLE.
  syms_one_label   THE LOAD-BEARING ONE: the equation at the seats fLay D.layout num (labAt X k ·).
  syms_read   so no symbol is a silent 0: each is an entry of a message's table.
  numP, idxP, msgIn_pair   one numbering that parts the messages (link * 256 + number), and the idx
    that goes with it at link k: there the third clause says just that the message stands in the
    list.
  baseAt_look   where the meaning's symbols of sub-proof k are the packing of small integers, so are
    the lookups', of the same integers mzAt: BaseAt, as the lookups' named readings ask it.
  ownAtF_mzAt   the meaning's list is made of these integers: by unfolding.

Object, user, letters. Object: the two symAt; seatCalls; fLay; ownAtF. User:
Johnson/Goal/Meaning/ReadingsOneLook.lean (the lookups' four clauses at ownAtF). Letters: X, D, rad,
num, idx, k, tl, m, msg: all free; linkTieB ties the public ones.

WHERE THE TEST IS EMPTY. Its third clause forces idx (num o a) to be the place of message a of link
o in link k's list. So it can say yes only at a num that gives two numbers to two messages with two
places there: not at num := fun _ a => a where a borrowed message and one of the link's own bear one
number. numP is one that serves. idx is a letter of each link.

THE FAMILY IS ONE READING A LINK. m is ANY tuple of link k's signature; nothing here says that it is
committed. A borrowed array is read in link k's KEPT COPY of its message, at the row and place that
the BORN array's blocks give. That a borrower's reading and the owner's agree (ReadsOne) is a law on
the copies, over one switch or two, which this file does not touch.

What is not claimed. That linkTieB says yes at any plan. That a caller's D, tl are the
description's. The mask entries' seats. Anything on what a message holds. Nothing on soundness,
nothing on hiding. The program does not import this file.
-/
import Johnson.Goal.Meaning.HidSeatsOf
import Johnson.Goal.Meaning.HidFamily
import Johnson.Desc.First.Look.K3CallerAttReads

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open OnBytes OnBytes.Model
open OnBytes.Params (LaidBlock ReqArray ReqLayout)
open OnBytes.Road.Rows (Addr)
open Cb.Pv.Tail (Base BaseAt)
open VerifiableInference.Desc (arrayOf laidAt seatIn)
open VerifiableInference.Desc.First.Look (Sent Seat seatCalls sigListCalls keptAt bornAt szOf readAt
  valAt msgIn symArrB)
open Johnson.Pack (sigOf)

/-! ## The places: two texts, one function -/

/-- The two finders of an array are one text. -/
theorem reqArray_eq_arrayOf (layout : ReqLayout) (l : ℕ) (name : String) :
    OnBytes.reqArray layout l name = arrayOf layout l name := rfl

/-- One block: the reader with an option is the test and the reader without. -/
theorem laidIn_eq (b : LaidBlock) (i c : ℕ) :
    VerifiableInference.Desc.laidIn b i c =
      if VerifiableInference.Desc.First.Look.laidHolds b i c = true then
        some (VerifiableInference.Desc.First.Look.laidIn b i c) else none := by
  unfold VerifiableInference.Desc.laidIn VerifiableInference.Desc.First.Look.laidHolds
    VerifiableInference.Desc.First.Look.laidIn
  by_cases h : b.firstI ≤ i ∧ i < b.firstI + 2 ^ b.bitsI ∧ b.firstC ≤ c ∧
      c < b.firstC + 2 ^ b.bitsC
  · have hb : (decide (b.firstI ≤ i) && decide (i < b.firstI + 2 ^ b.bitsI) &&
        decide (b.firstC ≤ c) && decide (c < b.firstC + 2 ^ b.bitsC)) = true := by
      simp [h.1, h.2.1, h.2.2.1, h.2.2.2]
    rw [if_pos h, if_pos hb]
  · rw [if_neg h, if_neg]
    intro k
    simp only [Bool.and_eq_true, decide_eq_true_eq] at k
    exact h ⟨k.1.1.1, k.1.1.2, k.1.2, k.2⟩

/-- **The two readers of an element's place are one function.** -/
theorem laidPlace_eq_laidAt (a : ReqArray) (i c : ℕ) :
    VerifiableInference.Desc.First.Look.laidPlace a.blocks i c = laidAt a i c := by
  unfold VerifiableInference.Desc.First.Look.laidPlace laidAt
  induction a.blocks with
  | nil => rfl
  | cons b bs ih =>
    rw [List.find?_cons, List.findSome?_cons, laidIn_eq]
    by_cases h : VerifiableInference.Desc.First.Look.laidHolds b i c = true
    · rw [h, if_pos rfl]
      rfl
    · rw [Bool.not_eq_true] at h
      rw [h, if_neg (by simp)]
      exact ih

/-! ## The seats -/

/-- **One element's two seats.** lab: the entry's label. t: the number of its array in the link's
list. idx: at which place of link k's list of messages the message of a number stands. -/
theorem seatCalls_of_label (D : Sent) (num : ℕ → ℕ → ℕ) (idx : ℕ → ℕ) (k t lab i c : ℕ)
    {A : ReqArray} {rp : ℕ × ℕ}
    (hn : (D.arrayOf.getD k #[])[t]? = some (ownerK lab, nameOf (ownerA lab)))
    (hA : arrayOf D.layout (ownerK lab) (nameOf (ownerA lab)) = some A)
    (hp : laidAt A i c = some rp)
    (hm : msgIn D k (ownerK lab) A.message = some (idx (num (ownerK lab) A.message))) :
    seatCalls D k (Addr.cell t i c) =
        some ⟨idx (fLay D.layout num lab i c).1, false, (fLay D.layout num lab i c).2.1,
          (fLay D.layout num lab i c).2.2⟩ := by
  have e : fLay D.layout num lab i c = (num (ownerK lab) A.message, rp.1, rp.2) := by
    unfold fLay seatIn
    rw [hA]
    show ((laidAt A i c).map fun x => (num (ownerK lab) A.message, x.1, x.2)).getD (0, 0, 0) = _
    rw [hp]
    rfl
  rw [e]
  unfold seatCalls
  dsimp only
  rw [hn]
  show ((OnBytes.reqArray D.layout (ownerK lab) (nameOf (ownerA lab))).bind fun a =>
    (VerifiableInference.Desc.First.Look.laidPlace a.blocks i c).bind fun rp =>
      if (ownerK lab == k) = true then
        some (⟨(keptAt D k).length + a.message, false, rp.1, rp.2⟩ : Seat)
      else ((bornAt D k).idxOf? (ownerK lab, a.message)).map fun j => ⟨j, false, rp.1, rp.2⟩) = _
  rw [reqArray_eq_arrayOf, hA]
  show ((VerifiableInference.Desc.First.Look.laidPlace A.blocks i c).bind fun rp =>
      if (ownerK lab == k) = true then
        some (⟨(keptAt D k).length + A.message, false, rp.1, rp.2⟩ : Seat)
      else ((bornAt D k).idxOf? (ownerK lab, A.message)).map fun j => ⟨j, false, rp.1, rp.2⟩) = _
  rw [laidPlace_eq_laidAt, hp]
  show (if (ownerK lab == k) = true then
        some (⟨(keptAt D k).length + A.message, false, rp.1, rp.2⟩ : Seat)
      else ((bornAt D k).idxOf? (ownerK lab, A.message)).map fun j => ⟨j, false, rp.1, rp.2⟩) = _
  unfold msgIn at hm
  by_cases ho : (ownerK lab == k) = true
  · rw [if_pos ho] at hm ⊢
    rw [Option.some.inj hm]
  · rw [if_neg ho] at hm ⊢
    rw [hm]
    rfl

/-! ## The messages, and the symbols -/

/-- **A link's tuple of messages as a reading by numbers.** 0 where the seat lies in no table. -/
def msgsOfTuple (cs : Codes) (l : List (OracleShape × ℕ)) (idx : ℕ → ℕ) (m : (sigOf cs l).Msg) :
    Msgs := fun n mask r p => (readAt cs l m ⟨idx n, mask, r, p⟩).getD 0

/-- **The two readings of a tuple's symbols are one**, at any seats that meet seatCalls through
idx. -/
theorem syms_one (D : Sent) (rad : OracleShape → ℕ) (k : ℕ) (tl : HTailF2) (idx : ℕ → ℕ)
    (seat : Fin (szOf tl).NM → ℕ → ℕ → ℕ × ℕ × ℕ)
    (hs : ∀ (μ : Fin (szOf tl).NM) (i c : ℕ), i < Alg.symRows ((szOf tl).m μ) → c < (szOf tl).k μ →
      seatCalls D k (Addr.cell (tl.gtTree.getD μ.val 0) i c) =
        some ⟨idx (seat μ i c).1, false, (seat μ i c).2.1, (seat μ i c).2.2⟩)
    (m : (sigOf D.codes (sigListCalls D rad k)).Msg) :
    VerifiableInference.Desc.First.Look.symAt D.codes (sigListCalls D rad k) (seatCalls D k) tl m =
      symAt (szOf tl) seat (msgsOfTuple D.codes (sigListCalls D rad k) idx m) := by
  funext μ i' c
  unfold VerifiableInference.Desc.First.Look.symAt symAt msgsOfTuple valAt
  rw [hs μ i'.val c.val i'.isLt c.isLt]
  rfl

/-! ## The public ties at a link -/

/-- **The public ties at link k, at one entry, as a test.** -/
def entryTieB (X : Model.Verify.Public) (D : Sent) (rad : OracleShape → ℕ) (num : ℕ → ℕ → ℕ)
    (idx : ℕ → ℕ) (k : ℕ) (tl : HTailF2) (μ : ℕ) : Bool :=
  decide ((D.arrayOf.getD k #[])[tl.gtTree.getD μ 0]? =
      some (ownerK (labAt X k μ), nameOf (ownerA (labAt X k μ)))) &&
    symArrB D (sigListCalls D rad k) k (tl.gtTree.getD μ 0) (Alg.symRows ((szOf tl).m μ))
      ((szOf tl).k μ) &&
    match arrayOf D.layout (ownerK (labAt X k μ)) (nameOf (ownerA (labAt X k μ))) with
    | some A => decide (msgIn D k (ownerK (labAt X k μ)) A.message =
        some (idx (num (ownerK (labAt X k μ)) A.message)))
    | none => false

/-- **The public ties at link k, as a test**: at every entry of the record's list. -/
def linkTieB (X : Model.Verify.Public) (D : Sent) (rad : OracleShape → ℕ) (num : ℕ → ℕ → ℕ)
    (idx : ℕ → ℕ) (k : ℕ) (tl : HTailF2) : Bool :=
  (List.range (szOf tl).NM).all fun μ => entryTieB X D rad num idx k tl μ

/-- **Under the test: an element's seat by the lookups' reader is the seat by the label, and it lies
in its table.** -/
theorem seat_of_tie {X : Model.Verify.Public} {D : Sent} {rad : OracleShape → ℕ}
    {num : ℕ → ℕ → ℕ} {idx : ℕ → ℕ} {k : ℕ} {tl : HTailF2}
    (T : linkTieB X D rad num idx k tl = true)
    {μ i c : ℕ} (hμ : μ < (szOf tl).NM) (hi : i < Alg.symRows ((szOf tl).m μ))
    (hc : c < (szOf tl).k μ) :
    seatCalls D k (Addr.cell (tl.gtTree.getD μ 0) i c) =
        some ⟨idx (fLay D.layout num (labAt X k μ) i c).1, false,
          (fLay D.layout num (labAt X k μ) i c).2.1, (fLay D.layout num (labAt X k μ) i c).2.2⟩ ∧
      (⟨idx (fLay D.layout num (labAt X k μ) i c).1, false,
          (fLay D.layout num (labAt X k μ) i c).2.1,
          (fLay D.layout num (labAt X k μ) i c).2.2⟩ : Seat).Fits D.codes
        (sigListCalls D rad k) := by
  have t := List.all_eq_true.1 T μ (List.mem_range.2 hμ)
  unfold entryTieB at t
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at t
  obtain ⟨⟨hn, ha⟩, hm⟩ := t
  obtain ⟨s, hs, hf⟩ := VerifiableInference.Desc.First.Look.sym_seated ha hi hc
  cases hA : arrayOf D.layout (ownerK (labAt X k μ)) (nameOf (ownerA (labAt X k μ))) with
  | none =>
    rw [hA] at hm
    cases hm
  | some A =>
    rw [hA] at hm
    have hm' := of_decide_eq_true hm
    have hp : (laidAt A i c).isSome = true := by
      have h2 := hs
      unfold seatCalls at h2
      dsimp only at h2
      rw [hn] at h2
      have h3 : ((OnBytes.reqArray D.layout (ownerK (labAt X k μ))
          (nameOf (ownerA (labAt X k μ)))).bind fun a =>
        (VerifiableInference.Desc.First.Look.laidPlace a.blocks i c).bind fun rp =>
          if (ownerK (labAt X k μ) == k) = true then
            some (⟨(keptAt D k).length + a.message, false, rp.1, rp.2⟩ : Seat)
          else ((bornAt D k).idxOf? (ownerK (labAt X k μ), a.message)).map fun j =>
            ⟨j, false, rp.1, rp.2⟩) = some s := h2
      rw [reqArray_eq_arrayOf, hA] at h3
      have h4 : ((VerifiableInference.Desc.First.Look.laidPlace A.blocks i c).bind fun rp =>
          if (ownerK (labAt X k μ) == k) = true then
            some (⟨(keptAt D k).length + A.message, false, rp.1, rp.2⟩ : Seat)
          else ((bornAt D k).idxOf? (ownerK (labAt X k μ), A.message)).map fun j =>
            ⟨j, false, rp.1, rp.2⟩) = some s := h3
      rw [laidPlace_eq_laidAt] at h4
      cases hq : laidAt A i c with
      | none =>
        rw [hq] at h4
        cases h4
      | some _ => rfl
    obtain ⟨rp, hp⟩ := Option.isSome_iff_exists.1 hp
    have e := seatCalls_of_label D num idx k _ _ i c hn hA hp hm'
    refine ⟨e, ?_⟩
    rw [e] at hs
    rw [Option.some.inj hs]
    exact hf

/-- **The two readings of a tuple's symbols are one, at the seats off the layout by the label.** -/
theorem syms_one_label {X : Model.Verify.Public} {D : Sent} {rad : OracleShape → ℕ}
    {num : ℕ → ℕ → ℕ} {idx : ℕ → ℕ} {k : ℕ} {tl : HTailF2}
    (T : linkTieB X D rad num idx k tl = true)
    (m : (sigOf D.codes (sigListCalls D rad k)).Msg) :
    VerifiableInference.Desc.First.Look.symAt D.codes (sigListCalls D rad k) (seatCalls D k) tl m =
      symAt (szOf tl) (fun μ => fLay D.layout num (labAt X k μ.val))
        (msgsOfTuple D.codes (sigListCalls D rad k) idx m) :=
  syms_one D rad k tl idx _ (fun μ _ _ hi hc => (seat_of_tie T μ.isLt hi hc).1) m

/-- **No symbol is a silent 0**: under the test every symbol is an entry of a message's table. -/
theorem syms_read {X : Model.Verify.Public} {D : Sent} {rad : OracleShape → ℕ}
    {num : ℕ → ℕ → ℕ} {idx : ℕ → ℕ} {k : ℕ} {tl : HTailF2}
    (T : linkTieB X D rad num idx k tl = true)
    (m : (sigOf D.codes (sigListCalls D rad k)).Msg) {μ i c : ℕ} (hμ : μ < (szOf tl).NM)
    (hi : i < Alg.symRows ((szOf tl).m μ)) (hc : c < (szOf tl).k μ) :
    (readAt D.codes (sigListCalls D rad k) m
      ⟨idx (fLay D.layout num (labAt X k μ) i c).1, false,
        (fLay D.layout num (labAt X k μ) i c).2.1,
        (fLay D.layout num (labAt X k μ) i c).2.2⟩).isSome = true :=
  VerifiableInference.Desc.First.Look.readAt_some _ _ _ (seat_of_tie T hμ hi hc).2 m

/-! ## One numbering that parts the messages -/

/-- A number for message j of link l: one-to-one while a link has fewer than 256 messages. -/
def numP (l j : ℕ) : ℕ := l * 256 + j

/-- Where the message of a number stands in link k's own list. -/
def idxP (D : Sent) (k n : ℕ) : ℕ := (msgIn D k (n / 256) (n % 256)).getD 0

/-- At that numbering the tie of the message's place says: the message stands in link k's list. -/
theorem msgIn_pair (D : Sent) (k o a : ℕ) (ha : a < 256) (h : (msgIn D k o a).isSome = true) :
    msgIn D k o a = some (idxP D k (numP o a)) := by
  obtain ⟨j, hj⟩ := Option.isSome_iff_exists.1 h
  unfold idxP numP
  rw [show (o * 256 + a) / 256 = o by omega, show (o * 256 + a) % 256 = a by omega, hj]
  rfl

/-! ## The integers behind the symbols -/

/-- **Where the meaning's symbols of sub-proof k are the packing of small integers, so are the
lookups', of the same integers**: those of which the meaning's list is made. msg: any reading that
has the tuple's symbols at the seats. -/
theorem baseAt_look {X : Model.Verify.Public} {D : Sent} {rad : OracleShape → ℕ}
    {num : ℕ → ℕ → ℕ} {idx : ℕ → ℕ} {k : ℕ} {tl : HTailF2}
    (T : linkTieB X D rad num idx k tl = true)
    (m : (sigOf D.codes (sigListCalls D rad k)).Msg) (msg : Msgs)
    (hm : symAt (szOf tl) (fun μ => fLay D.layout num (labAt X k μ.val)) msg =
      symAt (szOf tl) (fun μ => fLay D.layout num (labAt X k μ.val))
        (msgsOfTuple D.codes (sigListCalls D rad k) idx m))
    (hB : Base (symAt (szOf tl) (fun μ => fLay D.layout num (labAt X k μ.val)) msg)) :
    BaseAt (VerifiableInference.Desc.First.Look.symAt D.codes (sigListCalls D rad k)
        (seatCalls D k) tl m)
      (OnBytes.Road.Rows.mzAt
        (symAt (szOf tl) (fun μ => fLay D.layout num (labAt X k μ.val)) msg)) := by
  rw [syms_one_label T m, ← hm]
  exact (OnBytes.Road.Rows.baseAt_mzAt _).2 hB

/-- The meaning's list of sub-proof k is made of these integers: by unfolding. -/
theorem ownAtF_mzAt (X : Model.Verify.Public) (f : ℕ → ℕ → ℕ → ℕ × ℕ × ℕ) (tls : ℕ → HTailF2)
    (msgF : ℕ → Msgs) (k : ℕ) :
    ownAtF (fun j => szOf (tls j)) (seatBy f X fun j => szOf (tls j)) msgF k =
      OnBytes.Road.Rows.Norms.mzTot (OnBytes.Road.Rows.mzAt
        (symAt (szOf (tls k)) (fun μ => f (labAt X k μ.val)) (msgF k))) := rfl

end Meaning

#print axioms Meaning.reqArray_eq_arrayOf
#print axioms Meaning.laidIn_eq
#print axioms Meaning.laidPlace_eq_laidAt
#print axioms Meaning.seatCalls_of_label
#print axioms Meaning.syms_one
#print axioms Meaning.seat_of_tie
#print axioms Meaning.syms_one_label
#print axioms Meaning.syms_read
#print axioms Meaning.msgIn_pair
#print axioms Meaning.baseAt_look
#print axioms Meaning.ownAtF_mzAt
