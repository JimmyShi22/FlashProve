-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/HasCoinsAtBook.lean: THE SHARED "SENDING" (the kind K1) AND
THE BOOK OF COINS: THE RECORD's FIELD hasCoins (K1Seated, Honest/K1/Seated.lean) AT THE PROVER's
OWN BOOK A.B (onlineProverFromPublicFiles, Honest/AtPure.lean), AT EACH OF THE KIND's 52 SENDERS ON THE FIRST CHAIN:
UNDER THE LIBRARY's HEAD h AND hA (onlineProverFromPublicFiles returns A): NO PREMISE MORE. PUBLIC DATA ALONE: how many
coins a part has, never what they are. Six theorems; no definition. A TRIAL THAT COUNTS IN NO
COLUMN.

SECOND ISSUE. The first asked two premises, hPick and hAlike, and typed anew two laws that other
houses have. Both premises are paid here by other houses' laws; nothing of theirs is typed again.

  - book_pick     AT ANY DESCRIPTION: where bookWhole returns B, B's first table is r0 ++ sw, where
                  rowsIn returns r0 at the first chain, the first list of sendings and the second
                  chain's rounds: bookWhole's text, ProofFile's bind_ok and checked_ok, and the hash
                  build's bookRaw_rows (Honest/BookRawRows.lean: its first and eighth clauses).
  - rows_alike_head   UNDER h: at every list of sendings rowsIn answers at the head's description
                  what it answers at the written description WP: the hash build's planAlike_at_head
                  (Honest/K14/WrittenAtHead.lean) and rowsIn_alike (Honest/BookAlikeRows.lean), and
                  the sealed alike₂_rounds (Johnson/AtFull/ProofPlan/PlanAlike.lean).
  - book_begins   UNDER h, hA: A.B MEETS THE PREMISE hB OF HasCoinsOfRows.lean: by the hash build's
                  atPure_book_at_head (Honest/K14/AtPureBookAtHead.lean: A.B is what bookWhole
                  returns at the head's description and the public part's own three lists; over
                  ProofFile's atPure_book; ITS GRADE, by that house's letter:
                  through Lean on its own box, a working ride; L25's file beneath it a loose file),
                  book_pick, rows_alike_head and the sealed sends_in_scope
                  (Johnson/Goal/Numbers/MadeInScope.lean).
  - hasCoins_two_at_book, hasCoins_fifty_at_book, hasCoins_w_at_book so THE FIELD, TO THE LETTER,
                  at Bk := A.B.

THE FILLING P IS A LETTER: hA asks that onlineProverFromPublicFiles returns A at P; no filling is named.

Limits. THAT onlineProverFromPublicFiles RETURNS IS A HYPOTHESIS; so is the head. RecordPaid.lean and RecordAtW.lean
leave the book a free letter: THE CALL THAT JOINS THEM AT Bk := A.B IS NOT HERE. AT THE FORMAT's
EARLIER HASH. THE FULL SIZE ALONE. THE FIRST CHAIN ALONE. IT STANDS OVER FILES OF L25's AND OF THE
HASH BUILD's THAT ARE ON NO SEAL, AND OVER L25's TURNED BookCarry.lean. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.HasCoinsOfRows
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead
import Johnson.Desc.ProofFile.Honest.BookRawRows
import Johnson.Desc.ProofFile.Honest.BookAlikeRows
import Johnson.Desc.ProofFile.Honest.K14.WrittenAtHead
import Johnson.Goal.Numbers.MadeInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS F0T)

/-- **WHERE bookWhole RETURNS, THE BOOK's FIRST TABLE BEGINS WITH rowsIn's ROWS.** At any
description. -/
theorem book_pick {Xi : Type} {F : FileDescription Xi} {p0 p1 p2 : Johnson.G.ChainSends} {M : Merges}
    {B : ProverCoinCounts} (h : bookWhole F p0 p1 p2 M = .ok B) :
    ∃ r0 sw, rowsIn F.first.blocksInOrder p0 (F.second.blocksInOrder.flatMap (·.rounds)) = .ok r0 ∧
      B.first = r0 ++ sw := by
  unfold bookWhole at h
  obtain ⟨W, hW, hc⟩ := bind_ok h
  obtain rfl := checked_ok hc
  obtain ⟨r0, _, _, s0, _, _, _, h0, -, -, -, -, -, -, hf, -⟩ := bookRaw_rows hW
  exact ⟨r0, s0, h0, hf⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **FROM THE HEAD's DESCRIPTION TO THE WRITTEN ONE.** -/
theorem rows_alike_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (c : Johnson.G.ChainSends) :
    rowsIn (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder c
        ((F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder.flatMap (·.rounds)) =
      rowsIn P2Law.ProofPlan.WP.first.blocksInOrder c
        (P2Law.ProofPlan.WP.second.blocksInOrder.flatMap (·.rounds)) := by
  have A := K14.planAlike_at_head h
  rw [← alike₂_rounds _ _ A.second]
  exact (rowsIn_alike A.first c _).symm

/-- **A.B's FIRST TABLE BEGINS WITH THE WRITTEN ROWS.** -/
theorem book_begins (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∃ rs sw, rowsIn P2Law.ProofPlan.WP.first.blocksInOrder Johnson.G.proofSendsFull.1
      (P2Law.ProofPlan.WP.second.blocksInOrder.flatMap (·.rounds)) = .ok rs ∧ A.B.first = rs ++ sw := by
  obtain ⟨r0, sw, e, hf⟩ := book_pick (K14.atPure_book_at_head h hA)
  rw [rows_alike_head h, VerifiableInference.PlanWritten.Joined.sends_in_scope h.scope h.laid.pub
    (K1.pin1_atAll h)] at e
  exact ⟨r0, sw, e, hf⟩

/-- **hasCoins AT NUMBER 2, AT A.B.** -/
theorem hasCoins_two_at_book (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {Xi Y : Type} (first : Nat) (Dd : RowDataOf Xi) {J : SendJob (PlaceIn Xi) Y}
    (hJ : J = placeJob (K1.firstPar A.G.first (K1.gpOf A.Z)) first (firstFold A.G.first) Dd) :
    dueAt (A.B.rowsOf 0) ⟨J.P.place, 0⟩ = dueR J.P J.ride :=
  hasCoins_two_of h hA (book_begins h hA) first Dd hJ

/-- **hasCoins AT EACH OF THE FIFTY, AT A.B.** -/
theorem hasCoins_fifty_at_book (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {Xi Y : Type} {l : ℕ} (hl : l < 25) (d : Bool) (first : Nat) (Dd : RowDataOf Xi)
    {J : SendJob (PlaceIn Xi) Y}
    (hJ : J = laterJobAt A.G.first (K1.gpOf A.Z) l (IM.k1Ix l d + 1) (if d then 2 else 1) first
      Dd) :
    dueAt (A.B.rowsOf 0) ⟨J.P.place, 0⟩ = dueR J.P J.ride :=
  hasCoins_fifty_of h hA (book_begins h hA) hl d first Dd hJ

/-- **hasCoins AT NUMBER 356, AT A.B.** -/
theorem hasCoins_w_at_book (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    {W₀ Rc Tr X₀ X : Type} {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {Xi Y : Type} (first : Nat) (Dw : RowDataOf Xi) {J : SendJob (PlaceIn Xi) Y}
    (hJ : J = wJobAt Zp.first (wGp Zp) 4 wMsgFull first Dw) :
    dueAt (A.B.rowsOf 0) ⟨J.P.place, 0⟩ = dueR J.P J.ride :=
  hasCoins_w_of h (book_begins h hA) first Dw hJ

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.book_pick
#print axioms ProofFile.Honest.K1.rows_alike_head
#print axioms ProofFile.Honest.K1.book_begins
#print axioms ProofFile.Honest.K1.hasCoins_two_at_book
#print axioms ProofFile.Honest.K1.hasCoins_fifty_at_book
#print axioms ProofFile.Honest.K1.hasCoins_w_at_book
