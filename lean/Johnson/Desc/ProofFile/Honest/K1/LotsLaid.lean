-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/LotsLaid.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR
THE HONEST SIDE: K1's LOTS FOR A LAYING OF THE THREADS' SCRIPT, AS LISTS; AND THE TIE (the fields
msgs and pads of the record K1Seated, Honest/K1/Seated.lean) AT A SCRIPT THAT IS LAID BY LOTS
(Script.ofLots, Honest/Thread/ScriptLots.lean). Four definitions with code, eight statements and
their proofs.

  k1MsgLotsAt, k1MsgLots
      for a member (its number in the chain, its job): one MsgLot a message of the job: THE RECORD's
      OWN THREE TERMS: the number arr at the message's seat · fx := front + the rounds in front of
      the member · the text msgTxt 0 wit J own₀ n. The list over all members
  k1PadLotsAt, k1PadLots
      the like for pads: the seat's tree and tenant · padTxt 0 J n
  mem_k1MsgLots, mem_k1PadLots
      a member's lots lie in the whole list
  msgs_of_lots, pads_of_lots
      THE TIE: at Script.ofLots bs front cells tok pl tl ml: IF each of the member's lots lies in ml
      (in pl) AND AGREES there (LotsAgree, PadLotsAgree): the record's field, to the letter, at
      L.Q := that Script, L.bs := bs, L.thread.front := front, at every Vd
  hin_msgs_of_agree, hin_pads_of_agree
      what a laying can pay: our lots lie in its list, and ALL lots of the list agree (MsgsAgree,
      PadsAgree): then that premise holds at every member
  msgTxt_answers, padTxt_answers
      THE COMPANION, THE OTHER WAY: under the record's hasCoins a message's lot answers at every
      entry, mask rows among them, and a pad's lot at each of padB's places: there the tie is not
      idle

NO NEW TEXT OF A MESSAGE OR A PAD STANDS HERE: every lot's text is msgTxt or padTxt
(Honest/K1/ScriptLots.lean), which read of a run's coins the part's own cut alone, through lentCut.

Limits. THE CHAIN's NUMBER IS WRITTEN IN: 0: THE FIRST CHAIN ALONE. NO SCRIPT IS LAID HERE AND NO
LIST ml | pl IS NAMED: "lies in" and "agrees" ARE PREMISES, PAID BY NOBODY: THE TIE IS EXCHANGED FOR
THEM. A LOT THAT ANSWERS NOTHING AGREES WITH EVERYTHING. THAT TWO LOTS OF OURS WITH ONE NUMBER ARE
ONE LOT IS NOT PROVED HERE. BY THE LIBRARY's NUMBERING AN ORIGINAL AND ALL ITS KEPT COPIES BEAR ONE
NUMBER (arrOf, Johnson/P5T/PlanSeats.lean): that no other sender's lot bears a number of ours, or
that it agrees with ours where it does, is proved nowhere. AT A BOOK THAT DOES NOT COVER A PART's
COUNT ITS LOTS ANSWER NOTHING, AND msgs_of_lots' AND pads_of_lots' ENDS HOLD IDLY: hasCoins is no
premise of theirs (neither proof would spend it): the two companions say what it gives. arr, front,
bs, wit, own₀ and the list of members are letters; own₀ is one letter for all members. Nothing says
how a coin is made. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.SeatedLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT)
open ProofFile.Honest.FirstThread (Script MsgLot PadLot TreeLot OwnMsgs OwnPads LotsAgree PadLotsAgree
  MsgsAgree PadsAgree ofLots_ownMsgs ofLots_ownPads)
open Johnson.Prover.Send (shapeAt)

variable {Bk : ProverCoinCounts} {Cl Wl Xi X Cells Tok : Type}

/-- **A member's lots of messages**: x.1: the member's number in the chain; x.2: its job. One lot a
message of the job, at the record's own three terms. READS COINS THROUGH msgTxt ALONE. -/
def k1MsgLotsAt (bs : List (Block S Cl)) (front : Nat) (arr : ℕ → ℕ → ℕ) (wit : Wl → PlaceIn Xi)
    (own₀ : X) (x : Nat × SendJob (PlaceIn Xi) X) : List (MsgLot Bk Wl) :=
  (List.range x.2.P.sent.size).map fun n =>
    ⟨arr (seatAtMember bs x.1 x.2.P n).1 (seatAtMember bs x.1 x.2.P n).2,
      front + roundsTo bs x.1, msgTxt 0 wit x.2 own₀ n⟩

/-- The like at each member of a list. -/
def k1MsgLots (bs : List (Block S Cl)) (front : Nat) (arr : ℕ → ℕ → ℕ) (wit : Wl → PlaceIn Xi)
    (own₀ : X) (jobs : List (Nat × SendJob (PlaceIn Xi) X)) : List (MsgLot Bk Wl) :=
  jobs.flatMap (k1MsgLotsAt bs front arr wit own₀)

/-- **A member's lots of pads**: one lot a message of the job, at the message's seat. READS COINS
THROUGH padTxt ALONE. -/
def k1PadLotsAt (bs : List (Block S Cl)) (x : Nat × SendJob (PlaceIn Xi) X) :
    List (PadLot Bk Wl) :=
  (List.range x.2.P.sent.size).map fun n =>
    ⟨(seatAtMember bs x.1 x.2.P n).1, (seatAtMember bs x.1 x.2.P n).2,
      fun k _ => padTxt 0 x.2 n k⟩

/-- The like at each member of a list. -/
def k1PadLots (bs : List (Block S Cl)) (jobs : List (Nat × SendJob (PlaceIn Xi) X)) :
    List (PadLot Bk Wl) :=
  jobs.flatMap (k1PadLotsAt bs)

/-- A member's lots lie in the whole list. -/
theorem mem_k1MsgLots {bs : List (Block S Cl)} {front : Nat} {arr : ℕ → ℕ → ℕ}
    {wit : Wl → PlaceIn Xi} {own₀ : X} {jobs : List (Nat × SendJob (PlaceIn Xi) X)}
    {x : Nat × SendJob (PlaceIn Xi) X} (hx : x ∈ jobs) {L : MsgLot Bk Wl}
    (hL : L ∈ k1MsgLotsAt bs front arr wit own₀ x) : L ∈ k1MsgLots bs front arr wit own₀ jobs :=
  List.mem_flatMap.2 ⟨x, hx, hL⟩

theorem mem_k1PadLots {bs : List (Block S Cl)} {jobs : List (Nat × SendJob (PlaceIn Xi) X)}
    {x : Nat × SendJob (PlaceIn Xi) X} (hx : x ∈ jobs) {L : PadLot Bk Wl}
    (hL : L ∈ k1PadLotsAt bs x) : L ∈ k1PadLots bs jobs :=
  List.mem_flatMap.2 ⟨x, hx, hL⟩

/-- **THE TIE's FIRST HALF, AT A SCRIPT LAID BY LOTS**: the record's field msgs, to the letter,
where each of the member's lots lies in the laid list and agrees there. -/
theorem msgs_of_lots (bs : List (Block S Cl)) (front : Nat) (cells : Wl → Cells) (tok : Wl → Tok)
    (pl : List (PadLot Bk Wl)) (tl : Nat → TreeLot Bk Wl) (ml : List (MsgLot Bk Wl))
    (arr : ℕ → ℕ → ℕ) (wit : Wl → PlaceIn Xi) (own₀ : X) (x : Nat × SendJob (PlaceIn Xi) X)
    (hin : ∀ L ∈ k1MsgLotsAt bs front arr wit own₀ x, L ∈ ml ∧ LotsAgree ml L)
    (Vd : Wl → Prop) :
    ∀ n, n < x.2.P.sent.size →
      OwnMsgs (Script.ofLots bs front cells tok pl tl ml) Vd (front + roundsTo bs x.1)
        (arr (seatAtMember bs x.1 x.2.P n).1 (seatAtMember bs x.1 x.2.P n).2)
        (front + roundsTo bs x.1) (msgTxt 0 wit x.2 own₀ n) := by
  intro n hn
  have hL := hin ⟨arr (seatAtMember bs x.1 x.2.P n).1 (seatAtMember bs x.1 x.2.P n).2,
    front + roundsTo bs x.1, msgTxt 0 wit x.2 own₀ n⟩
    (List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩)
  exact ofLots_ownMsgs bs front cells tok pl tl ml hL.1 hL.2 Vd (front + roundsTo bs x.1)

/-- **THE TIE's SECOND HALF**: the record's field pads, to the letter, under the like. -/
theorem pads_of_lots (bs : List (Block S Cl)) (front : Nat) (cells : Wl → Cells) (tok : Wl → Tok)
    (pl : List (PadLot Bk Wl)) (tl : Nat → TreeLot Bk Wl) (ml : List (MsgLot Bk Wl))
    (x : Nat × SendJob (PlaceIn Xi) X)
    (hin : ∀ L ∈ k1PadLotsAt bs x, L ∈ pl ∧ PadLotsAgree pl L) (Vd : Wl → Prop) :
    ∀ n, n < x.2.P.sent.size →
      OwnPads (Script.ofLots bs front cells tok pl tl ml) Vd (seatAtMember bs x.1 x.2.P n).1
        (seatAtMember bs x.1 x.2.P n).2 (fun k _ => padTxt 0 x.2 n k) := by
  intro n hn
  have hL := hin ⟨(seatAtMember bs x.1 x.2.P n).1, (seatAtMember bs x.1 x.2.P n).2,
    fun k _ => padTxt 0 x.2 n k⟩ (List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩)
  exact ofLots_ownPads bs front cells tok pl tl ml hL.1 hL.2 Vd

/-! ## What a laying can pay: agreement once, for its whole list -/

/-- Where our lots lie in the laid list and ALL lots of that list agree, msgs_of_lots' premise holds
at every member. -/
theorem hin_msgs_of_agree {bs : List (Block S Cl)} {front : Nat} {arr : ℕ → ℕ → ℕ}
    {wit : Wl → PlaceIn Xi} {own₀ : X} {jobs : List (Nat × SendJob (PlaceIn Xi) X)}
    {ml : List (MsgLot Bk Wl)} (hsub : ∀ L ∈ k1MsgLots bs front arr wit own₀ jobs, L ∈ ml)
    (hag : MsgsAgree ml) {x : Nat × SendJob (PlaceIn Xi) X} (hx : x ∈ jobs) :
    ∀ L ∈ k1MsgLotsAt bs front arr wit own₀ x, L ∈ ml ∧ LotsAgree ml L :=
  fun L hL => ⟨hsub L (mem_k1MsgLots hx hL), hag L (hsub L (mem_k1MsgLots hx hL))⟩

/-- The like for pads. -/
theorem hin_pads_of_agree {bs : List (Block S Cl)} {jobs : List (Nat × SendJob (PlaceIn Xi) X)}
    {pl : List (PadLot Bk Wl)} (hsub : ∀ L ∈ k1PadLots bs jobs, L ∈ pl) (hag : PadsAgree pl)
    {x : Nat × SendJob (PlaceIn Xi) X} (hx : x ∈ jobs) :
    ∀ L ∈ k1PadLotsAt bs x, L ∈ pl ∧ PadLotsAgree pl L :=
  fun L hL => ⟨hsub L (mem_k1PadLots hx hL), hag L (hsub L (mem_k1PadLots hx hL))⟩

/-! ## The companion, the other way: where the book has the part's count the lots answer -/

/-- **UNDER THE RECORD's hasCoins A MESSAGE's LOT ANSWERS AT EVERY ENTRY**, mask rows among them: so
there the tie's first half is not idle. -/
theorem msgTxt_answers {J : SendJob (PlaceIn Xi) X}
    (hC : dueAt (Bk.rowsOf 0) ⟨J.P.place, 0⟩ = dueR J.P J.ride) (wit : Wl → PlaceIn Xi) (own₀ : X)
    (n : Nat) (k : Coins Bk) (w : Wl) (h : List Fmt.Drawn) (mask : Bool) (r j : Nat) :
    ∃ y, msgTxt 0 wit J own₀ n k w h mask r j = some y := by
  obtain ⟨c, hc⟩ := cut_of_count (Nat.zero_le 1) hC k
  exact ⟨_, msgTxt_some 0 wit J own₀ n k c hc w h mask r j⟩

/-- **UNDER hasCoins A PAD's LOT ANSWERS AT EACH OF padB's PLACES.** -/
theorem padTxt_answers {J : SendJob (PlaceIn Xi) X}
    (hC : dueAt (Bk.rowsOf 0) ⟨J.P.place, 0⟩ = dueR J.P J.ride) (n : Nat) (k : Coins Bk)
    (mask : Bool) (r j : Nat) (hp : padB J.P.codes (shapeAt J.P n) mask r j = true) :
    ∃ y, padTxt 0 J n k mask r j = some y := by
  obtain ⟨c, hc⟩ := cut_of_count (Nat.zero_le 1) hC k
  exact ⟨_, padTxt_some 0 J n k c hc mask r j hp⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1MsgLotsAt
#print axioms ProofFile.Honest.K1.k1MsgLots
#print axioms ProofFile.Honest.K1.k1PadLotsAt
#print axioms ProofFile.Honest.K1.k1PadLots
#print axioms ProofFile.Honest.K1.mem_k1MsgLots
#print axioms ProofFile.Honest.K1.mem_k1PadLots
#print axioms ProofFile.Honest.K1.msgs_of_lots
#print axioms ProofFile.Honest.K1.pads_of_lots
#print axioms ProofFile.Honest.K1.hin_msgs_of_agree
#print axioms ProofFile.Honest.K1.hin_pads_of_agree
#print axioms ProofFile.Honest.K1.msgTxt_answers
#print axioms ProofFile.Honest.K1.padTxt_answers
