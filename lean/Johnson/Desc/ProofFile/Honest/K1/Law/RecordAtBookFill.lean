-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/RecordAtBookFill.lean: THE SHARED "SENDING" (the kind K1): THE
RECORD K1Seated (Honest/K1/Seated.lean) AT EACH OF THE KIND's 52 MEMBERS OF THE FIRST CHAIN, FROM
THE TIE (its fields msgs and pads), UNDER THE LIBRARY's HEAD, A RETURNED PROVER AND TWO PREMISES ON
THE FILLING's LOTS: OF THE TWENTY FIELDS EIGHTEEN ARE PAID THERE; msgs AND pads ARE HANDED ON.
Three theorems; NO DEFINITION. A TRIAL THAT COUNTS IN NO COLUMN.

THE LETTERS. L := ProofFile's lettersHead at the prover A.H that onlineProverFromPublicFiles returns; THE BOOK IS A.B,
onlineProverFromPublicFiles's own: the Script Q is typed over it. THE FILLING P IS A LETTER.

THE PREMISES: THE WHOLE LIST; THE SAME IN FORM IN ALL THREE. h: the library's head: A HYPOTHESIS ·
hA: onlineProverFromPublicFiles returns A at P: A HYPOTHESIS · hex, ho: ON P's LIST OF LOTS: some lot has, at A's public
part and ground, the kind's own halves (K1's lot's at the 51; W's side's at 356); every lot has
there no half that could stand in their way, or these halves (Honest/K1/Law/LotsMeet.lean gives
both ho from one premise on the list) · msgs, pads: THE TIE: PREMISES ON THE SCRIPT Q, WHOLE, IN
THE RECORD's OWN TEXT · hL, hJ: two equations that name L and J. THE NUMBERS: at the 51 the job's
number is lotNo secondHashFunction A.Z at its place (it pays the field firstNo): WRITTEN INTO THE STATEMENT, no
premise; in hex and ho the numbers are idle (lotHalves_any_no, Honest/K1/HalvesFree.lean: the
halves are one value at all numbers): so a filling whose K1 lot is laid at other numbers meets them
too. At 356 no is a free letter, idle likewise (wHalves_any_no).

  - k1Seated_two_at_book   number 2, the first segment's opening.
  - k1Seated_fifty_at_book   each link's reads and digits.
  - k1Seated_w_at_book   number 356, W's sending.
EACH ENDS: there is a block blk with K1Seated L ‹the number› blk wit J own₀ …, at the kind's own
job J.

WHO PAYS WHAT. Sixteen fields at the 51: another pen's k1Seated_two_fill_paid,
k1Seated_fifty_fill_paid (RecordPaidAtFill.lean; half among them, by HalfAtFill.lean) · fifteen at
356: k1Seated_w_paid (RecordAtW.lean), and half by half_w_head_of_lots (HalfAtW.lean) · hasCoins:
hasCoins_two_at_book, hasCoins_fifty_at_book, hasCoins_w_at_book (HasCoinsAtBook.lean): THIS IS THE
CALL THAT JOINS THE RECORDS AT Bk := A.B · member: another pen's stands_two, stands_fifty, stands_w
(MembersStand.lean): hence "there is a block".

AT 356 TWO LETTERS STAND FOR ONE THING: hJ speaks at Zp, the head's public part; hex and ho at A.Z,
the returned one: under h and hA they are one (ProofFile's atPure_at_laid, Honest/AtHead.lean: A.Z = Zp):
the proof of half spends it. And wMsgFull is the WRITTEN message, where W's side's text (wHalves)
has what linMessageW answers at the public part's shape: tied under h by msg_w_head
(Honest/K1/Law/FitsAtW.lean).

`K1Seated` is had here only under the head, a returned prover, two premises on the lots and THE
TIE; here THE TIE is shown at no Script that a run has. At the first Script, under the head and a
returned prover alone: `k1Seated_first` (AtFullSide/K1/FirstScript.lean).
NOT IN FRONT OF A LAW OVER COINS.

AN IDLE WAY. L.valid is "v = w and Vd v": at Vd := fun _ => False it holds of nothing: msgs and
pads, which speak at the thread's valid inputs, are then met for nothing, and the record that
follows binds nothing at any input.

Limits. THAT onlineProverFromPublicFiles RETURNS AT ANY FILLING IS NOT SAID. THAT ANY FILLING MEETS hex AND ho WITH W's
SIDE IN IT IS NOT SAID: NONE IS LAID. THAT THE TIE HOLDS AT ANY SCRIPT IS NOT SAID: msgs and pads
are the premises of weight, and no Script is shown that meets them at ProofFile's real letters. SO NO
MEMBER OF THE RECORD IS HAD: these are implications. THE FULL SIZE, THE FORMAT's EARLIER HASH, THE
FIRST CHAIN. BY IMPORT LINES 141 FILES THAT ARE NOT IN THE SEAL laws.11 LIE BENEATH IT: 135 rows of
the closed list of laws.12 (ours, L25's frame and threads, H2's, the hash build's and five other
houses') and six of ours that are on no row and go with this file. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.RecordPaidAtFill
import Johnson.Desc.ProofFile.Honest.K1.Law.RecordAtW
import Johnson.Desc.ProofFile.Honest.K1.Law.HalfAtW
import Johnson.Desc.ProofFile.Honest.K1.Law.HasCoinsAtBook
import Johnson.Desc.ProofFile.Honest.K1.Law.MembersStand

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Place Block)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open VerifiableInference.Desc.Sound (MsgT)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- UNDER THE HEAD, A RETURNED PROVER, TWO PREMISES ON THE LOTS AND THE TIE, SHOWN HERE AT NO
SCRIPT THAT A RUN HAS:
**NUMBER 2, AT THE PROVER's OWN BOOK: EIGHTEEN PAID**; msgs and pads are handed on.
-/
theorem k1Seated_two_at_book (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst)
    (Dt : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (hex : ∃ M ∈ P.lots,
      M.halves A.Z A.G = lotHalves wit (lotNo OnBytes.secondHashFunction A.Z) Dt A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ x ∈ M.halves A.Z A.G, x.place.kind = .K1 → x.place.link = none) ∨
      M.halves A.Z A.G = lotHalves wit (lotNo OnBytes.secondHashFunction A.Z) Dt A.Z A.G)
    (Q : Script A.B (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr) (own₀ : X)
    {L : Letters A.B ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub
      (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    (hL : L = lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    {J : SendJob (PlaceIn ProofFile.Inst) X}
    (hJ : J = placeJob (K1.firstPar A.G.first (K1.gpOf A.Z))
      (lotNo OnBytes.secondHashFunction A.Z ⟨1, some 0, 1, .K1⟩) (firstFold A.G.first) (Dt A.Z A.G))
    (msgs : ∀ n, n < J.P.sent.size →
      OwnMsgs L.Q L.valid (L.thread.front + roundsTo L.bs 2)
        ((P5J.At.arr Zp) (seatAtMember L.bs 2 J.P n).1 (seatAtMember L.bs 2 J.P n).2)
        (L.thread.front + roundsTo L.bs 2) (msgTxt 0 wit J own₀ n))
    (pads : ∀ n, n < J.P.sent.size →
      OwnPads L.Q L.valid (seatAtMember L.bs 2 J.P n).1 (seatAtMember L.bs 2 J.P n).2
        (fun k _ => padTxt 0 J n k)) :
    ∃ blk, K1Seated L 2 blk wit J own₀ .opening (P5J.At.arr Zp) (P5J.At.seats Zp)
      (P5J.At.ms Zp Z.lay) (K1.radRec 0 J.P) := by
  obtain ⟨blk, hb⟩ := stands_two h
  exact ⟨blk, k1Seated_two_fill_paid h hA wit _ Dt hex ho rfl Q test carryX item n₁ n₂ b₀ Vd Rd
    Kp w own₀ hL hJ
    (by subst hL; exact hb) (hasCoins_two_at_book h hA _ _ hJ) msgs pads⟩

/-- UNDER THE HEAD, A RETURNED PROVER, TWO PREMISES ON THE LOTS AND THE TIE, SHOWN HERE AT NO
SCRIPT THAT A RUN HAS:
**EACH OF THE FIFTY, AT THE PROVER's OWN BOOK: EIGHTEEN PAID**; msgs and pads are
handed on. -/
theorem k1Seated_fifty_at_book (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst)
    (Dt : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (hex : ∃ M ∈ P.lots,
      M.halves A.Z A.G = lotHalves wit (lotNo OnBytes.secondHashFunction A.Z) Dt A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ x ∈ M.halves A.Z A.G, x.place.kind = .K1 → x.place.link = none) ∨
      M.halves A.Z A.G = lotHalves wit (lotNo OnBytes.secondHashFunction A.Z) Dt A.Z A.G)
    (Q : Script A.B (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr) (own₀ : X)
    {L : Letters A.B ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub
      (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    (hL : L = lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    {l : ℕ} (hl : l < 25) (d : Bool) {J : SendJob (PlaceIn ProofFile.Inst) X}
    (hJ : J = laterJobAt A.G.first (K1.gpOf A.Z) l (IM.k1Ix l d + 1) (if d then 2 else 1)
      (lotNo OnBytes.secondHashFunction A.Z ⟨1, some l, IM.k1Ix l d + 1, .K1⟩) (Dt A.Z A.G))
    (msgs : ∀ n, n < J.P.sent.size →
      OwnMsgs L.Q L.valid (L.thread.front + roundsTo L.bs (K1.noL l d))
        ((P5J.At.arr Zp) (seatAtMember L.bs (K1.noL l d) J.P n).1
          (seatAtMember L.bs (K1.noL l d) J.P n).2)
        (L.thread.front + roundsTo L.bs (K1.noL l d)) (msgTxt 0 wit J own₀ n))
    (pads : ∀ n, n < J.P.sent.size →
      OwnPads L.Q L.valid (seatAtMember L.bs (K1.noL l d) J.P n).1
        (seatAtMember L.bs (K1.noL l d) J.P n).2
        (fun k _ => padTxt 0 J n k)) :
    ∃ blk, K1Seated L (K1.noL l d) blk wit J own₀ (cond d (.digits l) (.reads l))
      (P5J.At.arr Zp) (P5J.At.seats Zp) (P5J.At.ms Zp Z.lay)
      (K1.radRec (3 * l + (if d then 2 else 1)) J.P) := by
  obtain ⟨blk, hb⟩ := stands_fifty h hl d
  exact ⟨blk, k1Seated_fifty_fill_paid h hA wit _ Dt hex ho rfl Q test carryX item n₁ n₂ b₀ Vd
    Rd Kp w own₀ hL hl d hJ
    (by subst hL; exact hb) (hasCoins_fifty_at_book h hA hl d _ _ hJ) msgs pads⟩

/-- UNDER THE HEAD, A RETURNED PROVER, TWO PREMISES ON THE LOTS AND THE TIE, SHOWN HERE AT NO
SCRIPT THAT A RUN HAS:
**NUMBER 356, AT THE PROVER's OWN BOOK: EIGHTEEN PAID**; msgs and pads are handed on.
-/
theorem k1Seated_w_at_book (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst) (no : Place → Nat)
    (Dd : ProofFile.Pub → ProofFile.Ground → RowDataOf ProofFile.Inst)
    (hex : ∃ M ∈ P.lots, M.halves A.Z A.G = wHalves wit no Dd A.Z A.G)
    (ho : ∀ M ∈ P.lots, (∀ g ∈ M.halves A.Z A.G, g.place ≠ ⟨1, none, 4, .K1⟩) ∨
      M.halves A.Z A.G = wHalves wit no Dd A.Z A.G)
    (Q : Script A.B (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
    (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
    (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
    (w : Local W₀ Rc ProofFile.Inst Tr) (own₀ : X)
    {L : Letters A.B ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub
      (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT}
    (hL : L = lettersHead h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    {J : SendJob (PlaceIn ProofFile.Inst) X}
    (hJ : J = wJobAt Zp.first (wGp Zp) 4 wMsgFull (lotNo OnBytes.secondHashFunction Zp ⟨1, none, 4, .K1⟩)
      (Dd Zp A.G))
    (msgs : ∀ n, n < J.P.sent.size →
      OwnMsgs L.Q L.valid (L.thread.front + roundsTo L.bs 356)
        ((P5J.At.arr Zp) (seatAtMember L.bs 356 J.P n).1 (seatAtMember L.bs 356 J.P n).2)
        (L.thread.front + roundsTo L.bs 356) (msgTxt 0 wit J own₀ n))
    (pads : ∀ n, n < J.P.sent.size →
      OwnPads L.Q L.valid (seatAtMember L.bs 356 J.P n).1 (seatAtMember L.bs 356 J.P n).2
        (fun k _ => padTxt 0 J n k)) :
    ∃ blk, K1Seated L 356 blk wit J own₀ .w (P5J.At.arr Zp) (P5J.At.seats Zp)
      (P5J.At.ms Zp Z.lay) (K1.radRec 81 J.P) := by
  obtain ⟨blk, hb⟩ := stands_w h
  have hh := half_w_head_of_lots h hA wit no Dd hex ho hJ Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
  exact ⟨blk, k1Seated_w_paid h A.H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hL (Dd Zp A.G) hJ
    (by subst hL; exact hb) (by subst hL; exact hh) (hasCoins_w_at_book h hA _ _ hJ) msgs pads⟩

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.k1Seated_two_at_book
#print axioms ProofFile.Honest.K1.k1Seated_fifty_at_book
#print axioms ProofFile.Honest.K1.k1Seated_w_at_book
