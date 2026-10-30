-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/PaidAtHead.lean: the kind "the code switch" (K2): AT THE FIRST
CHAIN's LETTERS AT THE LIBRARY's HEAD: WHAT IS LEFT OF THE PREMISE OF THE KIND's EXCHANGE BY KIND
(`SwitchPaid`, ExchangeByKind.lean of this folder), IN ONE NAMED RECORD OF FIVE FIELDS. A JOIN:
calls alone. One structure: premises' forms; two statements with their proofs.

  `SwitchLeft`      WHAT IS LEFT, at one place: half · publicAt · msgs · pads: four fields of the
                    kind's record `K2SeatedL`, in its own text · made: the fourth premise of
                    `SwitchPaid` (`MadeAsks` at whatever is played, shown, laid and returned), asked
                    at every block at the place's number and at all numbers, dress and steps that
                    `SwitchArm` (BlockAtHead.lean of this folder) ties to the place
  `switchPaid_at_head`   the head · the opening · a written place · `SwitchLeft` ⊢ `SwitchPaid`
  `k2_exchange_at_head`  THE TOP: `SwitchLeft` at each of the 25 written places ⊢ the kind's whole
                    debt under "the exchange", by kind, in the form of `k2_exchange_by_kind`

By, all of this folder: `k2SeatedL_sends_paid` (RecordSendsPaid.lean): 23 of the record's 30 fields
at these letters · `book_behind_step` (BookBehindStep.lean): the two premises on the verifier's book
behind a step · `k2_member_at_head` (RecordAtHead.lean): member · `closing_at_head`
(ClosingAtHead.lean): closes · `k2_carry_at` (ExchangeByKind.lean): asks · `places_at_head`
(PlacesWritten.lean) · `k2_exchange_by_kind`.

Limits. AN IMPLICATION: `SwitchLeft` IS SHOWN OF NO PROVER AND NO SCRIPT. half speaks of the
prover's sides at the place; msgs and pads of the Script; publicAt of each valid input's instance;
four fields of `MadeAsks` speak of values and are proved of no run. D, readers and lay are letters,
one for all places. carryX is fixed as the exact carry. The head and the opening are premises.
NOT IN FRONT OF A LAW OVER COINS. The full size; the format's second hash function. Nothing
on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ExchangeByKind
import Johnson.Desc.ProofFile.Honest.K2.Law.RecordSendsPaid
import Johnson.Desc.ProofFile.Honest.K2.Law.BookBehindStep
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Wit Block KindName)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (AtYes)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K2.Honest (carryExact)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K1 (seatAtMember)
open _root_.Desc.K14.Law (secondAt seatZ shownGroups)

/-- **WHAT IS LEFT, AT ONE PLACE.** A structure of premises' forms. Nothing here proves that it can
be met. NOT IN FRONT OF A LAW OVER COINS. -/
structure SwitchLeft {Bk : ProverCoinCounts} {W₀ Rc Tr X : Type}
    (L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
      MsgT)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) (Zp : ProofFile.Pub) (G : ProofFile.Ground)
    (D : RowDataOf ProofFile.Inst) (readers : Local W₀ Rc ProofFile.Inst Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (p : SwitchPlace) : Prop where
  /-- the record's field: the half that stands at the place is the kind's one lot's -/
  half : (L.hs.find? fun g => g.place == p.place) = some (switchHalf (coreSender freshTable) D
    readers (lotClosingAt lay (segmentsOf Zp G)) p)
  /-- the record's field: the public test on the filling, at each valid input's instance -/
  publicAt : ∀ w, L.valid w → publicOk D lay p ((segmentsOf Zp G).take p.link) w.x = true
  /-- the record's field: the tie of the Script's messages to the kind's own text off the pads -/
  msgs : ∀ n, n < (switchPar p).sent.size → OwnMsgs L.Q L.valid (L.thread.front + roundsTo L.bs
    (switchNo p)) ((P5J.At.arr Zp) (seatAtMember L.bs (switchNo p) (switchPar p) n).1 (seatAtMember
    L.bs (switchNo p) (switchPar p) n).2) (L.thread.front + roundsTo L.bs (switchNo p))
    (switchMsgOff 0 D readers (lotClosingAt lay (segmentsOf Zp G)) p n)
  /-- the record's field: the tie of the Script's pads -/
  pads : ∀ n, n < (switchPar p).sent.size → OwnPads L.Q L.valid (seatAtMember L.bs (switchNo p)
    (switchPar p) n).1 (seatAtMember L.bs (switchNo p) (switchPar p) n).2 (fun k _ => switchPadTxt 0
    p n k)
  /-- the fourth premise of `SwitchPaid`, at whatever `SwitchArm` ties to the place -/
  made : ∀ (blk : Block TS ProofFile.Cl) (Pp : P1K2.Prep) (n : P1K2.Nums) (nm : String)
    (st : VerifiableInference.Desc.First.K2.At) (before : TS → Except String TS)
    (after : TS → TS → Except String TS), L.bs[switchNo p]? = some blk →
    P1K2.prepOf Zp G = some Pp → P1K2.numsAt Pp p.place.link = some n →
    SwitchArm Zp G p st before after →
    ∀ k s m E ds y cols s', ThrS L.thread Said (switchNo p) k s m E →
      drawsFit blk.rounds ds = true → L.thread.Stepped blk k s m E ds y cols s' →
      ∀ c V Wl r₁ r₂ s₁ t x z S3 Y rows Gr cd, handed 0 p k = some c →
        switchRowsLaid D readers (lotClosingAt lay (segmentsOf Zp G)) p c m.st.input m.st.heard =
          .ok V →
        lotClosingAt lay (segmentsOf Zp G) p (D m.st.input.x) (readers m.st.input)
          (m.st.heard.take (m.st.heard.length - 0)) (Stretch.carried p.carries c.2.2) = .ok Wl →
        (roundsOf y.1).map noDigest = [r₁, r₂] → before s = .ok s₁ →
        AtYes (IM.k2P Zp p.place nm st n) s₁ t r₁ r₂
          (shownGroups L.thread.ft blk (roundsOf y.1) cols) x z S3 Y rows Gr cd →
        after s₁ t = .ok s' →
        MadeAsks L.N p.link (switchPar p) (IM.k2P Zp p.place nm st n) s t s' V Wl r₂ x z S3 Y Gr

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (Kp : VerifiableInference.Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)
  {D : RowDataOf ProofFile.Inst} {readers : Local W₀ Rc ProofFile.Inst Tr → Readers}
  {lay : OnBytes.Params.ReqLayout} {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- hLeft IS A PREMISE. **AT THE HEAD's LETTERS, AT A WRITTEN PLACE: `SwitchPaid` FROM WHAT IS
LEFT.** NOT IN FRONT OF A LAW OVER COINS. -/
theorem switchPaid_at_head
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop} {p : SwitchPlace}
    (hp : p ∈ placesW)
    (hLeft : SwitchLeft
      (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp w) Said Zp
      Bs.G₀ D readers lay p) :
    SwitchPaid (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp w)
      Said (switchNo p) p := by
  have hpS : p ∈ switchPlaces Zp Bs.G₀ := by
    rw [places_at_head h.toAtMg O]
    exact hp
  obtain ⟨blk, hblk, -⟩ := k2_member_at_head h O hpS
  obtain ⟨Pp, n, nm, st, before, after, hPp, hn, hArm, R⟩ :=
    k2SeatedL_sends_paid h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp w rfl rfl
      O hpS hblk hLeft.half (closing_at_head h.toAtMg O p hpS) hLeft.publicAt hLeft.msgs hLeft.pads
      (k2_carry_at hp)
  obtain ⟨hFits, hNum⟩ :=
    book_behind_step h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp w rfl O hpS
      hblk Said
  exact ⟨blk, D, readers, lay, segmentsOf Zp Bs.G₀, IM.k2P Zp p.place nm st n, before, after, _, Zp,
    _, _, _, _, R, hFits, hNum, hLeft.made blk Pp n nm st before after hblk hPp hn hArm⟩

/-- hLeft IS A PREMISE. **K2's WHOLE DEBT UNDER "THE EXCHANGE", BY KIND, FROM WHAT IS LEFT.**
NOT IN FRONT OF A LAW OVER COINS. -/
theorem k2_exchange_at_head
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop}
    (hLeft : ∀ p ∈ placesW, SwitchLeft
      (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp w) Said Zp
      Bs.G₀ D readers lay p) :
    ∀ b p₀, P5J.At.ps[b]? = some p₀ → p₀.kind = KindName.K2 →
      ∀ j : First.Item, j ∈ ((lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀
        Vd Rd Kp w).thread.row b).owes →
      (j ∈ (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
          w).thread.opened b →
        (∀ m t, j ≠ First.Item.pin m t) ∧ j ≠ First.Item.pinI ∧ j ≠ First.Item.pinW ∧
        ∀ m q, q ∈ P5J.parts4 → j ≠ First.Item.constr m q) →
      ExchangeAtS (lettersHead h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp
        w).thread Said b j :=
  k2_exchange_by_kind h H Q test (carryExact Zp (P5J.At.arr Zp)) item n₁ n₂ b₀ Vd Rd Kp w
    fun p hp => switchPaid_at_head h H Q test item n₁ n₂ b₀ Vd Rd Kp w O hp (hLeft p hp)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.SwitchLeft
#print axioms ProofFile.Honest.K2.Law.switchPaid_at_head
#print axioms ProofFile.Honest.K2.Law.k2_exchange_at_head
