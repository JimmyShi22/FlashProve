-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/FreshTxt.lean: the kind "the code switch" (K2): WHICH COIN
STANDS AT AN ENTRY OF THE FOLD's FRESH MASK, BY NUMBER: the switch's text of its sending's last
message (`switchMsgTxt`, Honest/K2/ScriptLots.lean), AT ONE MASK ROW. `msgTxt_mask`
(Honest/K2/Law/MaskTxt.lean) bars that message: there a table rides, and the entries are laid by the
ride's own order. Statements with their proofs: joins; no definition.

  `rideOf_one`      where a table rides at a message of one mask row, the ride is ⟨k, 0⟩
  `laidFresh`       THE ROWS: place q ≤ 2 k of the one mask row is the sending's coin of the
                    extension field number a.e + `K1.sig` k q. a: the coins in front of the message
  `laidFresh_far`   beyond 2 k, below the code's length: 0
  `freshNumber`     THE NUMBER LIES WITHIN THE COUNT
  `stepsMain_zero`, `maskStart_fresh`   no coin of the message stands in front of its mask's
  `msgTxt_fresh`    THE END: the text at the sending's last message, mask row 0, place q ≤ 2 k:
                    THE READER REFUSES BEYOND THE COUNT: it returns x: so a coin stands there
  `msgTxt_fresh_apart`, `msgTxt_fresh_onto`   EACH ANOTHER, AND NONE LEFT OUT: two places up to 2 k
                    with one number are one place; each of the 2 k + 1 numbers is read somewhere
  `msgTxt_fresh_far`   beyond 2 k, below the code's length, the text answers 0

k: the next fold's row variables (`foldVars`). The fresh mask has 2 k + 1 coins. `K1.sig` k
(Honest/K1/RideLaw.lean, of other authors) maps the places 0 ... 2 k one to one onto the numbers 0
... 2 k: `sig_inj`, `sig_onto` there, CALLED HERE in `msgTxt_fresh_apart` and `msgTxt_fresh_onto`:
so each of the 2 k + 1 entries is one coin, and each of these coins stands at one entry of this row.
That no other message's entry reads one of these numbers is not said here: at the shared sending's
numbers it is `seat_inj`'s (see Kin). HOW TO CITE: `laidFresh` ends in `K1.ce`, WHICH READS 0 BEYOND
THE COUNT: cite it only beside `freshNumber`; `msgTxt_fresh` needs no such fence: its reader
refuses.

By: `ride_coin`, `lay_one`, `lay_one_beyond`, `sig_lt`, `sig_inj`, `sig_onto`
(Honest/K1/RideLaw.lean) · `mask_any` (Honest/K1/CoinsIn.lean) · `rowsAll_shared_paid`
(Honest/K2/Law/SameRows.lean) · `dueBefore_shared`, `sendingDue_shared`, `shapeFits_of`, `rideOf_as`
(Honest/K2/Law/Counts.lean) · `rows_of_laid` (MaskTxt.lean) · `msgTxt_rows`
(Honest/K2/Law/MainTxt.lean). Kin, of other authors, ON THE SHARED SENDING's OWN ROWS `K1.rowsR`,
none imported: `ride_one` (Honest/K1/RideOne.lean) says there what `laidFresh` says of this kind's
rows; `ride_one_beyond` what `laidFresh_far` says, AND WITH NO UPPER BOUND ON THE PLACE; `fits_ride`
and `ride_sizes` give what `ride_facts` gives, but for the main rows; `no_other_ride`
(Honest/K1/NoOther.lean): off the places (0, p), p up to 2 k, the mask table holds 0; `seat_inj`
(Honest/K1/Seat.lean): two places of a sending bear two numbers, across steps and messages.

Limits. AT ONE MASK ROW ALONE: a premise. At more than one the ride lays a coefficient at more than
one place, and no law says how (so RideLaw.lean's own Limits). `NoWord` is a premise. Where the part
is handed nothing or the rows are not laid nothing is said: both are premises, as returns. Nothing
on the mask row's tail. WHICH COIN IS WRITTEN WHERE: no sentence on what a coin is for. NO LOT IS
LAID. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.PadTxt
import Johnson.Desc.ProofFile.Honest.K1.RideLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open Reads

variable {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

section
variable {codes : OnBytes.Codes} {sent : Array OnBytes.OracleNotice}
  {fresh : Option (Nat × Nat)} {data : Nat → Nat → Nat → Cb.Gl.E}
  {c : Cs (sendingDue codes sent fresh)} {V : Nat → Johnson.Prover.Send.Rows}

/-- Where a table rides at a message of one mask row, the ride is ⟨k, 0⟩. -/
theorem rideOf_one {n k : Nat} (hk : foldAt fresh n = some k)
    (h1 : (sent.getD n default).shape.maskRows = 1) : rideOf sent fresh n = some ⟨k, 0⟩ := by
  unfold rideOf
  rw [hk, h1]
  rfl

/-- What the shared sending's test says of that ride. -/
theorem ride_facts (hf : K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true) {n k : Nat}
    (hn : n < sent.size) (hk : foldAt fresh n = some k)
    (h1 : (sent.getD n default).shape.maskRows = 1) :
    (sent.getD n default).shape.mainRows = 0 ∧ 1 ≤ k ∧
      2 * k + 1 ≤ (codes.mask.getD (sent.getD n default).shape.maskCode default).ell := by
  have h := (shapeFits_of hf hn).ride k hk
  rw [h1] at h
  simp only [K1.rideFits, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨_, h2⟩, _⟩, _⟩, h5⟩, h6⟩ := h
  have e0 : OnBytes.ceilLog2 1 = 0 := rfl
  rw [e0] at h6
  exact ⟨h2, h5, by omega⟩

/-- **THE NUMBER LIES WITHIN THE COUNT.** -/
theorem freshNumber (hw : NoWord sent)
    (hf : K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true) {n k : Nat}
    (hn : n < sent.size) (hk : foldAt fresh n = some k)
    (h1 : (sent.getD n default).shape.maskRows = 1) {i : Nat} (hi : i ≤ 2 * k) :
    K1.maskStart (sendingPar codes sent) (rideOf sent fresh) n + i <
      (sendingDue codes sent fresh).e := by
  rw [sendingDue_shared hf hw]
  refine K1.mask_any (sendingPar codes sent) (rideOf sent fresh) n i
    (by rw [sendingPar_sent]; exact hn) ?_
  rw [rideOf_one hk h1]
  show i < 2 * k + 1
  omega

/-- A shape with no main row and one mask row has no coin in front of its mask's. -/
theorem stepsMain_zero (codes : OnBytes.Codes) (s : OnBytes.OracleShape) (ride : Option K1.Ride)
    (h0 : s.mainRows = 0) (h1 : s.maskRows = 1) : (K1.stepsOf codes s ride).main = 0 := by
  simp [K1.Steps.main, K1.stepsOf, h0, h1]

/-- At a riding message of one mask row the mask's coins begin where the message's do. -/
theorem maskStart_fresh (hw : NoWord sent)
    (hf : K1.sendFits (sendingPar codes sent) (rideOf sent fresh) = true) {n k : Nat}
    (hn : n < sent.size) (hk : foldAt fresh n = some k)
    (h1 : (sent.getD n default).shape.maskRows = 1) :
    K1.maskStart (sendingPar codes sent) (rideOf sent fresh) n =
      (dueBefore codes sent fresh n).e := by
  obtain ⟨h0, _, _⟩ := ride_facts hf hn hk h1
  rw [dueBefore_shared hf hw n (Nat.le_of_lt hn)]
  unfold K1.maskStart
  rw [sendingPar_shape]
  rw [stepsMain_zero _ _ _ h0 h1]
  simp

/-- **THE ROWS.** Place q ≤ 2 k of the one mask row. -/
theorem laidFresh (hw : NoWord sent) (h : rowsAll freshTable codes sent fresh data c = .ok V)
    {n k : Nat} (hn : n < sent.size) (hk : foldAt fresh n = some k)
    (h1 : (sent.getD n default).shape.maskRows = 1) {q : Nat} (hq : q ≤ 2 * k) :
    (V n).mask 0 q = K1.ce c ((dueBefore codes sent fresh n).e + K1.sig k q) := by
  have hf := rowsAll_fits h
  obtain ⟨_, hk1, hl⟩ := ride_facts hf hn hk h1
  have e := sendingPar_shape codes sent n
  rw [rowsAll_shared_paid hw (fun _ _ _ _ _ => rfl) h hn,
    K1.ride_coin (sendingPar codes sent) (rideOf sent fresh) (dataShared sent data) _ n 0 q ⟨k, 0⟩
      (rideOf_one hk h1) (by rw [e, h1]; exact Nat.one_pos)
      (by rw [e]; exact Nat.lt_of_lt_of_le (Nat.lt_succ_of_le hq) hl),
    K1.lay_one k q _ hk1 hq, maskStart_fresh hw hf hn hk h1, ce_cast]
  exact if_pos (Nat.lt_succ_of_le (K1.sig_lt k q hk1 hq))

/-- Beyond 2 k, below the code's length: 0. -/
theorem laidFresh_far (hw : NoWord sent) (h : rowsAll freshTable codes sent fresh data c = .ok V)
    {n k : Nat} (hn : n < sent.size) (hk : foldAt fresh n = some k)
    (h1 : (sent.getD n default).shape.maskRows = 1) {q : Nat} (hq : 2 * k < q)
    (hl : q < (codes.mask.getD (sent.getD n default).shape.maskCode default).ell) :
    (V n).mask 0 q = 0 := by
  have hf := rowsAll_fits h
  obtain ⟨_, hk1, _⟩ := ride_facts hf hn hk h1
  have e := sendingPar_shape codes sent n
  rw [rowsAll_shared_paid hw (fun _ _ _ _ _ => rfl) h hn,
    K1.ride_coin (sendingPar codes sent) (rideOf sent fresh) (dataShared sent data) _ n 0 q ⟨k, 0⟩
      (rideOf_one hk h1) (by rw [e, h1]; exact Nat.one_pos) (by rw [e]; exact hl),
    K1.lay_one_beyond k q _ hk1 hq]

end

/-- The fresh mask is the sending's last message: there the place's `foldVars` ride. -/
theorem foldAt_last (p : SwitchPlace) :
    foldAt (switchFresh p.sizes p.others p.foldVars) ((switchSent p.sizes p.others).size - 1) =
      some p.foldVars := by
  simp [foldAt, switchFresh]

/-- **THE END.** THE READER REFUSES BEYOND THE COUNT: it returns x: so a coin stands there. -/
theorem msgTxt_fresh (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (k : Coins Bk) (w : Local W₀ Rc Xi Tr)
    (hd : List Fmt.Drawn) {c : SwitchCoins p.sizes p.others p.foldVars p.carries}
    (hH : handed ch p k = some c) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p c w hd = .ok V)
    (hw : NoWord (switchSent p.sizes p.others)) (h0 : 0 < (switchSent p.sizes p.others).size)
    (h1 : ((switchSent p.sizes p.others).getD ((switchSent p.sizes p.others).size - 1)
      default).shape.maskRows = 1) {a : Due}
    (hA : dueBefore p.sizes.codes (switchSent p.sizes p.others)
      (switchFresh p.sizes p.others p.foldVars) ((switchSent p.sizes p.others).size - 1) = a)
    {q : Nat} (hq : q ≤ 2 * p.foldVars) :
    ∃ x, c.1.eAt (a.e + K1.sig p.foldVars q) = .ok x ∧
      switchMsgTxt ch D readers closing p ((switchSent p.sizes p.others).size - 1) k w hd true 0
        q = some x := by
  subst hA
  obtain ⟨M, hR⟩ := rows_of_laid D readers closing p c w hd hV
  have hn : (switchSent p.sizes p.others).size - 1 < (switchSent p.sizes p.others).size :=
    Nat.sub_lt h0 Nat.one_pos
  have hf := rowsAll_fits hR
  obtain ⟨_, hk1, _⟩ := ride_facts hf hn (foldAt_last p) h1
  have hb := freshNumber hw hf hn (foldAt_last p) h1 (K1.sig_lt p.foldVars q hk1 hq)
  rw [maskStart_fresh hw hf hn (foldAt_last p) h1] at hb
  refine ⟨_, eAt_of_lt c.1 hb, ?_⟩
  rw [msgTxt_rows ch D readers closing p _ k w hd hH hV true]
  show some ((V _).mask 0 q) = _
  rw [laidFresh hw hR hn (foldAt_last p) h1 hq]
  unfold K1.ce
  rw [dif_pos hb]

/-- **EACH ANOTHER.** Two places up to 2 k with one number are one place. -/
theorem msgTxt_fresh_apart (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn)
    {c : SwitchCoins p.sizes p.others p.foldVars p.carries}
    {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p c w hd = .ok V)
    (h0 : 0 < (switchSent p.sizes p.others).size)
    (h1 : ((switchSent p.sizes p.others).getD ((switchSent p.sizes p.others).size - 1)
      default).shape.maskRows = 1) (a : Nat) {q q' : Nat}
    (hq : q ≤ 2 * p.foldVars) (hq' : q' ≤ 2 * p.foldVars)
    (h : a + K1.sig p.foldVars q = a + K1.sig p.foldVars q') : q = q' := by
  obtain ⟨M, hR⟩ := rows_of_laid D readers closing p c w hd hV
  obtain ⟨_, hk1, _⟩ := ride_facts (rowsAll_fits hR) (Nat.sub_lt h0 Nat.one_pos) (foldAt_last p) h1
  exact K1.sig_inj p.foldVars q q' hk1 hq hq' (Nat.add_left_cancel h)

/-- **AND NONE IS LEFT OUT.** Each of the 2 k + 1 numbers is read at some place up to 2 k. -/
theorem msgTxt_fresh_onto (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn)
    {c : SwitchCoins p.sizes p.others p.foldVars p.carries}
    {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p c w hd = .ok V)
    (h0 : 0 < (switchSent p.sizes p.others).size)
    (h1 : ((switchSent p.sizes p.others).getD ((switchSent p.sizes p.others).size - 1)
      default).shape.maskRows = 1) (a : Nat) {i : Nat}
    (hi : i ≤ 2 * p.foldVars) :
    ∃ q, q ≤ 2 * p.foldVars ∧ a + K1.sig p.foldVars q = a + i := by
  obtain ⟨M, hR⟩ := rows_of_laid D readers closing p c w hd hV
  obtain ⟨_, hk1, _⟩ := ride_facts (rowsAll_fits hR) (Nat.sub_lt h0 Nat.one_pos) (foldAt_last p) h1
  obtain ⟨q, h2, h3⟩ := K1.sig_onto p.foldVars i hk1 hi
  exact ⟨q, h2, by rw [h3]⟩

/-- Beyond 2 k, below the code's length, the text answers 0. -/
theorem msgTxt_fresh_far (ch : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : Closing) (p : SwitchPlace) (k : Coins Bk) (w : Local W₀ Rc Xi Tr)
    (hd : List Fmt.Drawn) {c : SwitchCoins p.sizes p.others p.foldVars p.carries}
    (hH : handed ch p k = some c) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p c w hd = .ok V)
    (hw : NoWord (switchSent p.sizes p.others)) (h0 : 0 < (switchSent p.sizes p.others).size)
    (h1 : ((switchSent p.sizes p.others).getD ((switchSent p.sizes p.others).size - 1)
      default).shape.maskRows = 1) {q : Nat} (hq : 2 * p.foldVars < q)
    (hl : q < (p.sizes.codes.mask.getD ((switchSent p.sizes p.others).getD
      ((switchSent p.sizes p.others).size - 1) default).shape.maskCode default).ell) :
    switchMsgTxt ch D readers closing p ((switchSent p.sizes p.others).size - 1) k w hd true 0
      q = some 0 := by
  obtain ⟨M, hR⟩ := rows_of_laid D readers closing p c w hd hV
  have hn : (switchSent p.sizes p.others).size - 1 < (switchSent p.sizes p.others).size :=
    Nat.sub_lt h0 Nat.one_pos
  rw [msgTxt_rows ch D readers closing p _ k w hd hH hV true]
  show some ((V _).mask 0 q) = _
  rw [laidFresh_far hw hR hn (foldAt_last p) h1 hq hl]

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.rideOf_one
#print axioms ProofFile.Honest.K2.Law.ride_facts
#print axioms ProofFile.Honest.K2.Law.freshNumber
#print axioms ProofFile.Honest.K2.Law.stepsMain_zero
#print axioms ProofFile.Honest.K2.Law.maskStart_fresh
#print axioms ProofFile.Honest.K2.Law.laidFresh
#print axioms ProofFile.Honest.K2.Law.laidFresh_far
#print axioms ProofFile.Honest.K2.Law.foldAt_last
#print axioms ProofFile.Honest.K2.Law.msgTxt_fresh
#print axioms ProofFile.Honest.K2.Law.msgTxt_fresh_apart
#print axioms ProofFile.Honest.K2.Law.msgTxt_fresh_onto
#print axioms ProofFile.Honest.K2.Law.msgTxt_fresh_far
