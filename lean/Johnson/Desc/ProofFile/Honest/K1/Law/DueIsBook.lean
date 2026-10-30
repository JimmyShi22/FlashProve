-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/DueIsBook.lean: THE SHARED "SENDING" (the kind K1) AND THE
MAKER OF THE BOOK OF COINS: TWO TEXTS OF ONE COUNTING: the maker's msgDue and sendDue
(Honest/BookRows.lean) AGAINST OUR stepsOf, dueMsg, startR and dueR (Honest/K1/Coins.lean), AT
EVERY SIZE. PUBLIC DATA ALONE: how many coins a message and a sending have, and where a message's
begin; never what they are. Twelve theorems; no definition.

THE TWO TEXTS ARE NOT ONE BARE. They are one under two public premises:
  hf   the plan's own test on a sent message's shape (the sealed Own.sentShapeFits,
       Johnson/Desc/Own/Sent.lean: it has a row; the numbers of the codes that its rows name lie in
       the arrays; its main rows are over one of the two fields); at a sending: our sendFits, which
       calls it at each message.
  ht   THE TIE OF THE RIDE: a table rides just at the messages that the maker's test isFresh
       accepts (mask rows alone, no sample), and at the maker's k: (ride).map (·.k) =
       if isFresh n then some k else none.

  - msgDue_steps  (E1) A MESSAGE: msgDue returns, and its five counts are stepsOf's, field for field
                  (tails · word · pad · entries | mask · maskTails); deg is the shape's mainDeg.
  - allOf_steps, msgDue_all   and its "all" is dueMsg.
  - msgDue_unfit_parts   A NEGATIVE TEST ON hf: at a shape whose mainDeg is 2 the two pads part.
  - msgDue_rowless_parts A NEGATIVE TEST ON hf: at a shape with no row the two pads part.
  - msgDue_untied_parts  A NEGATIVE TEST ON ht: where isFresh accepts and no table rides the two
                  counts part.
  - sendDue_snoc, sentList_at   tools.
  - sendDue_start (E2) A SENDING: sendDue P.codes k (P.sent.toList.take j) = some (startR P ride j),
                  at every j ≤ P.sent.size.
  - sendDue_whole at the whole: some (dueR P ride).
  - isFresh_foldMask, rideOf_tied   THE RIDE THAT placeJob LAYS (rideOf fold,
                  Honest/K1/PlaceJob.lean) MEETS ht where rideOwn accepts, the fold's own k is the
                  maker's, and no other message of the sending is accepted by isFresh.

Kin. sentList_at, a tool: toList_get (Johnson/Desc/K10/Honest/LeftIs.lean) says the like of
every array and every default. msgDue_steps: maker_held, of a file that is not in this tree
(E2E/KeyBookHeldMaker.lean) ties the same msgDue to another text of the counting, msgCoins: kin in
matter, no twin.

Limits. IT DOES NOT SAY THAT THE ROW AT A SENDER's ADDRESS IN THE MAKER's TABLE (rowsIn) IS THE ROW
OF THAT SENDER's SENDING: that the library's sending which rowsIn lays beside the member's round
"SEND seed" has P.sent and P.codes, that the maker's k (foldK) is the fold's own, and that no
earlier row bears the address. Nothing on the book's entries or carries. Nothing on what any coin
is. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.BookRows
import Johnson.Desc.ProofFile.Honest.K1.PlaceJob

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc
open Johnson.Prover.Send (shapeAt)

/-- **(E1) A MESSAGE: THE MAKER's FIVE COUNTS ARE OURS, FIELD FOR FIELD.** -/
theorem msgDue_steps (codes : Codes) (k : Nat) (n : OracleNotice) (ride : Option Ride)
    (hf : Own.sentShapeFits codes n.shape = true)
    (ht : ride.map (·.k) = if isFresh n then some k else none) :
    msgDue codes k n = some
      { deg := n.shape.mainDeg
        tails := (stepsOf codes n.shape ride).tails
        word := (stepsOf codes n.shape ride).word
        pad := (stepsOf codes n.shape ride).pad
        entries := (stepsOf codes n.shape ride).mask
        maskTails := (stepsOf codes n.shape ride).maskTails } := by
  simp only [Own.sentShapeFits, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hf
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hf
  have hb : (if n.shape.mainRows == 0 then some (⟨0, 0, 0⟩ : Code)
      else codes.base[n.shape.code]?) =
      some (if n.shape.mainRows == 0 then ⟨0, 0, 0⟩ else codes.base.getD n.shape.code default) := by
    by_cases h0 : n.shape.mainRows = 0
    · simp [h0]
    · have hlt := h2.resolve_left h0
      simp [h0, Array.getD, hlt]
  have hm : (if n.shape.maskRows == 0 then some (⟨0, 0, 0⟩ : Code)
      else codes.mask[n.shape.maskCode]?) =
      some (if n.shape.maskRows == 0 then ⟨0, 0, 0⟩
        else codes.mask.getD n.shape.maskCode default) := by
    by_cases h0 : n.shape.maskRows = 0
    · simp [h0]
    · have hlt := h3.resolve_left h0
      simp [h0, Array.getD, hlt]
  have he : (if isFresh n then 2 * k + 1 else n.shape.maskRows *
      (if n.shape.maskRows == 0 then (⟨0, 0, 0⟩ : Code)
        else codes.mask.getD n.shape.maskCode default).ell) =
      (ride.map (·.count)).getD
        (n.shape.maskRows * (codes.mask.getD n.shape.maskCode default).ell) := by
    cases hfr : isFresh n with
    | true =>
      rw [hfr] at ht
      cases ride with
      | none => simp at ht
      | some Rd =>
        have hk : Rd.k = k := by simpa using ht
        simp [Ride.count, hk]
    | false =>
      rw [hfr] at ht
      cases ride with
      | some Rd => simp at ht
      | none =>
        by_cases h0 : n.shape.maskRows = 0
        · simp [h0]
        · simp [h0]
  unfold msgDue
  dsimp only
  rw [hb, hm]
  show some _ = some _
  congr 1
  simp only [stepsOf, MsgDue.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_, he, ?_⟩
  · by_cases h0 : n.shape.mainRows = 0
    · simp [h0]
    · simp [h0]
  · by_cases h0 : n.shape.mainRows = 0
    · simp [h0]
    · simp [h0]
  · by_cases hq : n.shape.maskRows = 0
    · have h0 : n.shape.mainRows ≠ 0 := by omega
      by_cases ha : n.shape.answers = 0
      · simp [hq, h0, ha]
      · rcases h4 with h4 | h4
        · simp [hq, h0, ha, h4]
        · simp [hq, h0, ha, h4]
    · simp [hq]
  · by_cases h0 : n.shape.maskRows = 0
    · simp [h0]
    · simp [h0]

/-- The record of msgDue_steps: its "all" is dueMsg, where mainDeg is 1 or 3. -/
theorem allOf_steps (codes : Codes) (n : OracleNotice) (ride : Option Ride)
    (h4 : n.shape.mainDeg = 1 ∨ n.shape.mainDeg = 3) :
    ({ deg := n.shape.mainDeg
       tails := (stepsOf codes n.shape ride).tails
       word := (stepsOf codes n.shape ride).word
       pad := (stepsOf codes n.shape ride).pad
       entries := (stepsOf codes n.shape ride).mask
       maskTails := (stepsOf codes n.shape ride).maskTails } : MsgDue).all =
      dueMsg codes n.shape ride := by
  rcases h4 with h4 | h4
  · simp [MsgDue.all, MsgDue.main, dueMsg, Steps.main, h4]
  · simp [MsgDue.all, MsgDue.main, dueMsg, Steps.main, h4, Nat.add_assoc]

/-- **(E1), THE SUM**: the maker's "all" of a message is our dueMsg. -/
theorem msgDue_all (codes : Codes) (k : Nat) (n : OracleNotice) (ride : Option Ride)
    (hf : Own.sentShapeFits codes n.shape = true)
    (ht : ride.map (·.k) = if isFresh n then some k else none) :
    (msgDue codes k n).map (·.all) = some (dueMsg codes n.shape ride) := by
  rw [msgDue_steps codes k n ride hf ht, Option.map_some, allOf_steps]
  simp only [Own.sentShapeFits, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hf
  exact hf.2

/-- A negative test on hf: at a shape whose mainDeg is 2 the two pads part (1 against 3). -/
theorem msgDue_unfit_parts :
    (msgDue ⟨#[⟨3, 8, 2⟩], #[]⟩ 0 ⟨{ code := 0, mainRows := 1, mainDeg := 2 }, 0⟩).map (·.pad) ≠
      some (stepsOf ⟨#[⟨3, 8, 2⟩], #[]⟩ { code := 0, mainRows := 1, mainDeg := 2 } none).pad := by
  decide

/-- A negative test on hf: at a shape with no row the two pads part (0 against 3). -/
theorem msgDue_rowless_parts :
    (msgDue ⟨#[], #[]⟩ 0 ⟨{ }, 0⟩).map (·.pad) ≠ some (stepsOf ⟨#[], #[]⟩ { } none).pad := by
  decide

/-- A negative test on ht: where isFresh accepts and no table rides the two counts part (7 against
16). -/
theorem msgDue_untied_parts :
    (msgDue ⟨#[], #[⟨3, 8, 2⟩]⟩ 3 ⟨{ maskRows := 2, maskCode := 0, answers := 0 }, 0⟩).map
        (·.entries) ≠
      some (stepsOf ⟨#[], #[⟨3, 8, 2⟩]⟩ { maskRows := 2, maskCode := 0, answers := 0 }
        none).mask := by
  decide

/-- A sending grown by one message. -/
theorem sendDue_snoc (codes : Codes) (k : Nat) (l : List OracleNotice) (n : OracleNotice)
    {a : Due} {d : MsgDue} (hl : sendDue codes k l = some a) (hn : msgDue codes k n = some d) :
    sendDue codes k (l ++ [n]) = some (a.plus d.all) := by
  unfold sendDue at hl ⊢
  cases hm : l.mapM (msgDue codes k) with
  | none =>
    rw [hm] at hl
    cases hl
  | some ds =>
    rw [hm] at hl
    have e : (l ++ [n]).mapM (msgDue codes k) = some (ds ++ [d]) := by
      rw [List.mapM_append]
      simp [hm, hn]
    rw [e]
    simp only [Option.map_some, List.foldl_append, List.foldl_cons, List.foldl_nil] at hl ⊢
    rw [Option.some.inj hl]

/-- The list's member number j is the array's. -/
theorem sentList_at (P : K1.Par) {j : Nat} (hj : j < P.sent.size) :
    P.sent.toList[j]? = some (P.sent.getD j default) := by
  simp [Array.getD, hj]

/-- **(E2) A SENDING: WHERE MESSAGE NUMBER j's COINS BEGIN.** -/
theorem sendDue_start (P : K1.Par) (ride : Nat → Option Ride) (k : Nat)
    (hf : sendFits P ride = true)
    (ht : ∀ j, j < P.sent.size →
      (ride j).map (·.k) = if isFresh (P.sent.getD j default) then some k else none) :
    ∀ j, j ≤ P.sent.size → sendDue P.codes k (P.sent.toList.take j) = some (startR P ride j) := by
  intro j
  induction j with
  | zero =>
    intro _
    rw [List.take_zero]
    rfl
  | succ j ih =>
    intro hj
    have hj' : j < P.sent.size := hj
    have hs : Own.sentShapeFits P.codes (P.sent.getD j default).shape = true := by
      unfold sendFits at hf
      rw [Bool.and_eq_true] at hf
      have := List.all_eq_true.1 hf.2 j (List.mem_range.2 hj')
      simp only [Bool.and_eq_true] at this
      exact this.1.1
    rw [List.take_succ, sentList_at P hj']
    show sendDue P.codes k (P.sent.toList.take j ++ [P.sent.getD j default]) = _
    rw [sendDue_snoc P.codes k _ _ (ih (Nat.le_of_lt hj'))
      (msgDue_steps P.codes k _ (ride j) hs (ht j hj')), allOf_steps]
    · unfold startR
      rw [List.range_succ, List.foldl_append]
      rfl
    · simp only [Own.sentShapeFits, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hs
      exact hs.2

/-- **(E2), AT THE WHOLE: THE MAKER's COUNT OF A SENDING IS OUR dueR.** -/
theorem sendDue_whole (P : K1.Par) (ride : Nat → Option Ride) (k : Nat)
    (hf : sendFits P ride = true)
    (ht : ∀ j, j < P.sent.size →
      (ride j).map (·.k) = if isFresh (P.sent.getD j default) then some k else none) :
    sendDue P.codes k P.sent.toList = some (dueR P ride) := by
  have h := sendDue_start P ride k hf ht P.sent.size (Nat.le_refl _)
  rw [List.take_of_length_le (by simp)] at h
  exact h

/-- What foldMaskNotice announces is accepted by the maker's test isFresh. -/
theorem isFresh_foldMask (F : FoldShape) : isFresh (foldMaskNotice F) = true := by
  have h : 2 ^ F.layout.h ≠ 0 := Nat.pos_iff_ne_zero.1 (Nat.pow_pos (by decide))
  simp [isFresh, foldMaskNotice, h]

/-- **THE RIDE THAT placeJob LAYS MEETS THE TIE**, where rideOwn accepts, the fold's own k is the
maker's, and no other message of the sending is accepted by isFresh. -/
theorem rideOf_tied (P : K1.Par) (fold : Option (Nat × FoldShape)) (k : Nat)
    (ho : rideOwn P fold = true) (hk : ∀ x, fold = some x → x.2.layout.k = k)
    (hfr : ∀ j, j < P.sent.size → isFresh (P.sent.getD j default) = true →
      ∃ x, fold = some x ∧ x.1 = j) :
    ∀ j, j < P.sent.size →
      (rideOf fold j).map (·.k) = if isFresh (P.sent.getD j default) then some k else none := by
  intro j hj
  cases hq : isFresh (P.sent.getD j default) with
  | true =>
    obtain ⟨x, rfl, rfl⟩ := hfr j hj hq
    simp [rideOf, hk x rfl]
  | false =>
    cases fold with
    | none => rfl
    | some x =>
      by_cases e : j = x.1
      · exfalso
        subst e
        have h1 : P.sent[x.1]? = some (foldMaskNotice x.2) := by simpa [rideOwn] using ho
        have h2 : P.sent.getD x.1 default = foldMaskNotice x.2 := by
          simp [Array.getD_eq_getD_getElem?, h1]
        rw [h2, isFresh_foldMask] at hq
        cases hq
      · simp [rideOf, e]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.msgDue_steps
#print axioms ProofFile.Honest.K1.allOf_steps
#print axioms ProofFile.Honest.K1.msgDue_all
#print axioms ProofFile.Honest.K1.msgDue_unfit_parts
#print axioms ProofFile.Honest.K1.msgDue_rowless_parts
#print axioms ProofFile.Honest.K1.msgDue_untied_parts
#print axioms ProofFile.Honest.K1.sendDue_snoc
#print axioms ProofFile.Honest.K1.sentList_at
#print axioms ProofFile.Honest.K1.sendDue_start
#print axioms ProofFile.Honest.K1.sendDue_whole
#print axioms ProofFile.Honest.K1.isFresh_foldMask
#print axioms ProofFile.Honest.K1.rideOf_tied
