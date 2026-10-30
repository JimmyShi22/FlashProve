-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/RecordAtHead.lean: the kind "the code switch" (K2): THE RECORD
OF PREMISES `K2SeatedL` (Honest/K2/SeatedL.lean) AT THE FIRST THREAD's LETTERS AT THE LIBRARY's HEAD
(`lettersHead`, Honest/Thread/FirstHead.lean): WHICH OF ITS THIRTY FIELDS ARE PAID THERE BY WHAT
LIES, AND WHICH ARE HANDED ON. IT DOES NOT SAY THAT THE RECORD IS MET: nineteen fields stay premises
in the farthest law. In the form of the shared sending's K1/Law/RecordAtHead.lean, of other authors.
No definition; one closed fact by evaluation in Lean's kernel; lemmas.

The form. Each law binds L with hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w: an
equation that a caller meets by rfl: so that every field that is handed on can be written at L, TO
THE LETTER OF THE RECORD's OWN TEXT (cut by program out of SeatedL.lean), with arr, seats₀, ms at
the real table's P5J.At.arr Zp, P5J.At.seats Zp, P5J.At.ms Zp Z.lay. TWO LETTERS ARE CHOSEN: first
:= the table's own count L.N.msgsAt (some p.place): so firstNo holds by rfl, AND THE WEIGHT MOVES TO
THE FIELD numbered · carryX := carryExact Zp (P5J.At.arr Zp) (hX): so carryM holds by rfl.

  `k2SeatedL_at_head`   at any member b: PAID: treesNo (`treesNo_atN`, K1/Law/TreesNoTold.lean,
                    under placeAt) · ans (under hcodes) · rowM · firstNo · carryM; twenty-five
                    handed on
  `k2_member_at_head`   under the head and the opening, at a switch of the plan: a block stands at
                    the number where the written list of places first bears the place, and bears it
                    (CALLED AT NO LINE HERE: blk is a letter, so member stays a binder)
  `k2_placeAt_at_head`  and the written list has the place there
  `noWordW`, `k2_noWord_at_head`   BY LEAN's KERNEL, then under the head: every message with a main
                    row is sampled
  `k2SeatedL_at_place`  at a switch p of the plan, b := that number, seg := p.link, segs := the
                    plan's own segments: PAID BESIDE THE FIVE: placeAt · serves · roomy · placeOk ·
                    noWord · later; nineteen handed on, hcodes too

By: `border_block_at_head`, `border_test_at_head` (Honest/K2/Law/SwitchBorders.lean) ·
`borderNo_written` (Honest/K1/Law/MembersByBorder.lean, of other authors) · `serves_at_head`,
`roomy_at_head`, `fits_at_head` (Honest/K2/Law/PublicAtHead.lean) · `link_pos_at_head`
(Honest/K2/Law/LinksFromOne.lean) · `places_at_head` (Honest/K2/Law/PlacesWritten.lean). Kin, not
imported: `noWord_places` (Honest/K2/Law/SampledAtPlan.lean): `k2_noWord_at_head`'s end at every
plan, under the request's own public test on its shape.

Limits. HANDED ON IN THE FARTHEST LAW: member · shape · half · decides · sends · books (the member's
block and the prover's record) · closes · publicAt · trees · answersNo · seedsNo · nonZeroNo · port
(public) · msgs · pads (THE TIE: premises on the letter Q) · seats · numbered · sits (public, on the
table) · asks. Some have payers that are not called here. D, readers, lay, q, before, after, rad
stay free letters. h: the library's head: A HYPOTHESIS. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.SeatedL
import Johnson.Desc.ProofFile.Honest.K2.Law.SwitchBorders
import Johnson.Desc.ProofFile.Honest.K2.Law.PublicAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.LinksFromOne
import Johnson.Desc.ProofFile.Honest.K1.Law.TreesNoTold
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc
open VerifiableInference.Desc (Chain Strs Wit Place Block)
open VerifiableInference.Desc.First (S Numbers Item rowSays wordsAtFirst)
open VerifiableInference.Desc.First.K2 (P2 decideWith)
open VerifiableInference.Desc.Sound (MsgT Mem SitsAt smpNamed)
open VerifiableInference.Desc.K2.Honest (carryExact)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K1 (seatAtMember)
open Johnson.Prover.Send (shapeAt)
open _root_.Desc.Plain (DState)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
  {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)
  {b : Nat} {blk : Block TS ProofFile.Cl} {D : RowDataOf ProofFile.Inst}
  {readers : Local W₀ Rc ProofFile.Inst Tr → Readers} {lay : OnBytes.Params.ReqLayout}
  {segs : List SegmentPub} {p : SwitchPlace} {q : P2} {before : TS → Except String TS}
  {after : TS → TS → Except String TS} {seg : Nat} {rad : ℕ → ℕ}
  {Bs : ProofFile.PureBase} {base : List (Block TS ProofFile.Cl)}

/-- **AT lettersHead, AT ANY MEMBER**: treesNo, ans, rowM, firstNo and carryM are paid; the other
twenty-five fields are handed on in the record's own text. -/
theorem k2SeatedL_at_head
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
      MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (hX : carryX = carryExact Zp (P5J.At.arr Zp))
    (hcodes : (switchPar p).codes = P5J.At.cs Zp)
    (member : L.bs[b]? = some blk)
    (placeAt : L.ps[b]? = some p.place)
    (shape : blk.place = p.place ∧ blk.rounds = First.K2.rounds q ∧ blk.oracles = [q.sent, []])
    (half : (L.hs.find? fun g => g.place == p.place) = some (switchHalf (coreSender freshTable) D
      readers (lotClosingAt lay segs) p))
    (decides : ∀ s rs gs t, rs.length = 2 → gs.length = q.read.length → (blk.decide s rs gs = .ok t
      ↔ ∃ s₁ m, before s = .ok s₁ ∧ decideWith _root_.Tw.K2.sendByL8 q s₁ rs gs = .ok m ∧ after s₁
      m = .ok t))
    (sends : ∀ k s m E s' r₁ r₂ gs, Thr L.thread b k s m E → blk.decide s [r₁, r₂] gs = .ok s' → ∃
      (Lt : Type) (d d' : DState Lt) (owed : Option Nat) (ids : Array Nat), K1.decideSend
      (switchPar p) owed d [r₁, K1.cutTo (switchPar p) r₂] = .ok (ids, d') ∧ K1.SameMsgs d'.st
      s'.st ∧ s'.st.oracles.size = d'.st.oracles.size)
    (books : ∀ k s m E s' r₁ r₂ gs, Thr L.thread b k s m E → blk.decide s [r₁, r₂] gs = .ok s' →
      K1.Booked (switchPar p) s.book s.st.oracles.size s'.book s'.st.oracles.size)
    (serves : p.sizes.serves = true)
    (roomy : p.sizes.roomy = true)
    (placeOk : placeFits p = true)
    (closes : closingOk freshTable (segs.take p.link) p = true)
    (publicAt : ∀ w, L.valid w → publicOk D lay p (segs.take p.link) w.x = true)
    (noWord : NoWord (switchSent p.sizes p.others))
    (trees : q.sent.map (fun o => (o.logLength, o.words)) = Law.treeShapes p.sizes.codes
      (switchSent p.sizes p.others))
    (answersNo : (switchPar p).answers = q.answers)
    (seedsNo : q.seeds = (switchPar p).seeds * ((switchPar p).coordinates + 1))
    (nonZeroNo : q.nonZero = (switchPar p).seeds)
    (port : K1.condPort (switchPar p) rad = true)
    (msgs : ∀ n, n < (switchPar p).sent.size → OwnMsgs L.Q L.valid (L.thread.front + roundsTo L.bs
      b) ((P5J.At.arr Zp) (seatAtMember L.bs b (switchPar p) n).1 (seatAtMember L.bs b (switchPar
      p) n).2) (L.thread.front + roundsTo L.bs b) (switchMsgOff 0 D readers (lotClosingAt lay segs)
      p n))
    (pads : ∀ n, n < (switchPar p).sent.size → OwnPads L.Q L.valid (seatAtMember L.bs b (switchPar
      p) n).1 (seatAtMember L.bs b (switchPar p) n).2 (fun k _ => switchPadTxt 0 p n k))
    (seats : ∀ x, x ∈ L.N.sent seg 0 ↔ ∃ n, n < (switchPar p).sent.size ∧ (shapeAt (switchPar p)
      n).answers ≠ 0 ∧ x = seatAtMember L.bs b (switchPar p) n)
    (numbered : ∀ n, n < (switchPar p).sent.size → (shapeAt (switchPar p) n).answers ≠ 0 →
      seatAtMember L.bs b (switchPar p) n ∈ (P5J.At.seats Zp) ∧ (P5J.At.seats Zp).idxOf
      (seatAtMember L.bs b (switchPar p) n) = (L.N.msgsAt (some p.place)) + n)
    (sits : ∀ n, n < (switchPar p).sent.size → (shapeAt (switchPar p) n).answers ≠ 0 → (∃ x ∈
      (P5J.At.ms Zp Z.lay), SitsAt x (seatAtMember L.bs b (switchPar p) n).1 (seatAtMember L.bs b
      (switchPar p) n).2) ∧ ∀ x ∈ (P5J.At.ms Zp Z.lay), SitsAt x (seatAtMember L.bs b (switchPar p)
      n).1 (seatAtMember L.bs b (switchPar p) n).2 → (x.1.l.get x.2).1 = shapeAt (switchPar p) n)
    (later : 1 ≤ seg)
    (asks : Item.carry (seg - 1) ∈ L.thread.opened b) :
    K2SeatedL L b blk D readers lay segs p q before after seg (L.N.msgsAt (some p.place)) Zp
      (P5J.At.arr Zp) (P5J.At.seats Zp) (P5J.At.ms Zp Z.lay) rad := by
  subst hL
  subst hX
  refine {
    member := member, placeAt := placeAt, shape := shape, half := half, decides := decides,
    sends := sends, books := books, serves := serves, roomy := roomy, placeOk := placeOk,
    closes := closes, publicAt := publicAt, noWord := noWord, trees := trees,
    answersNo := answersNo, seedsNo := seedsNo, nonZeroNo := nonZeroNo, firstNo := rfl,
    treesNo := K1.treesNo_atN Zp cF placeAt, port := port, msgs := msgs, pads := pads,
    seats := seats, ans := ?_, numbered := numbered, sits := sits, rowM := fun _ => rfl,
    later := later, asks := asks, carryM := fun _ => rfl }
  rw [hcodes]
  rfl

/-- **A block stands at the number where the written list of places first bears the switch's
place, and it bears the place.** -/
theorem k2_member_at_head
    (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) :
    ∃ blk, cF.blocksInOrder[P5J.At.ps.findIdx (· == p.place)]? = some blk ∧ blk.place = p.place := by
  rw [← K1.borderNo_written h p.place]
  exact border_block_at_head h O hp

/-- **The written list of places has the switch's place there.** -/
theorem k2_placeAt_at_head
    (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) :
    P5J.At.ps[P5J.At.ps.findIdx (· == p.place)]? = some p.place := by
  have hlt : P5J.At.ps.findIdx (· == p.place) < P5J.At.ps.length := by
    rw [← K1.borderNo_written h p.place]
    exact (border_test_at_head h O hp).1
  have e := List.findIdx_getElem (w := hlt)
  rw [List.getElem?_eq_getElem hlt, beq_iff_eq.1 e]

set_option maxRecDepth 1000000 in
/-- **At each written place every message with a main row is sampled.** -/
theorem noWordW : (placesW.all fun p => noWord (switchSent p.sizes p.others)) = true := by
  decide +kernel

/-- The same under the head and the opening. -/
theorem k2_noWord_at_head
    (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x₀)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀) : NoWord (switchSent p.sizes p.others) := by
  rw [places_at_head h.toAtMg O] at hp
  exact noWord_yes (List.all_eq_true.1 noWordW p hp)

/-- **AT lettersHead, AT A SWITCH OF THE PLAN**: b: the number where the written list of places
first bears the place; seg: the place's link; segs: the plan's own segments. PAID BESIDE THE FIVE:
placeAt, serves, roomy, placeOk, noWord, later. Nineteen fields are handed on in the record's own
text. -/
theorem k2SeatedL_at_place
    {L : Letters Bk ProofFile.Cl W₀ Rc ProofFile.Inst Tr X ProofFile.InstPub (CellsM OnBytes.Flat.numsFull) P5J.At.Tok
      MsgT}
    (hL : L = lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (hX : carryX = carryExact Zp (P5J.At.arr Zp))
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hp : p ∈ switchPlaces Zp Bs.G₀)
    (hcodes : (switchPar p).codes = P5J.At.cs Zp)
    (member : L.bs[(P5J.At.ps.findIdx (· == p.place))]? = some blk)
    (shape : blk.place = p.place ∧ blk.rounds = First.K2.rounds q ∧ blk.oracles = [q.sent, []])
    (half : (L.hs.find? fun g => g.place == p.place) = some (switchHalf (coreSender freshTable) D
      readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p))
    (decides : ∀ s rs gs t, rs.length = 2 → gs.length = q.read.length → (blk.decide s rs gs = .ok t
      ↔ ∃ s₁ m, before s = .ok s₁ ∧ decideWith _root_.Tw.K2.sendByL8 q s₁ rs gs = .ok m ∧ after s₁
      m = .ok t))
    (sends : ∀ k s m E s' r₁ r₂ gs, Thr L.thread (P5J.At.ps.findIdx (· == p.place)) k s m E →
      blk.decide s [r₁, r₂] gs = .ok s' → ∃ (Lt : Type) (d d' : DState Lt) (owed : Option Nat) (ids
      : Array Nat), K1.decideSend (switchPar p) owed d [r₁, K1.cutTo (switchPar p) r₂] = .ok (ids,
      d') ∧ K1.SameMsgs d'.st s'.st ∧ s'.st.oracles.size = d'.st.oracles.size)
    (books : ∀ k s m E s' r₁ r₂ gs, Thr L.thread (P5J.At.ps.findIdx (· == p.place)) k s m E →
      blk.decide s [r₁, r₂] gs = .ok s' → K1.Booked (switchPar p) s.book s.st.oracles.size s'.book
      s'.st.oracles.size)
    (closes : closingOk freshTable ((segmentsOf Zp Bs.G₀).take p.link) p = true)
    (publicAt : ∀ w, L.valid w → publicOk D lay p ((segmentsOf Zp Bs.G₀).take p.link) w.x = true)
    (trees : q.sent.map (fun o => (o.logLength, o.words)) = Law.treeShapes p.sizes.codes
      (switchSent p.sizes p.others))
    (answersNo : (switchPar p).answers = q.answers)
    (seedsNo : q.seeds = (switchPar p).seeds * ((switchPar p).coordinates + 1))
    (nonZeroNo : q.nonZero = (switchPar p).seeds)
    (port : K1.condPort (switchPar p) rad = true)
    (msgs : ∀ n, n < (switchPar p).sent.size → OwnMsgs L.Q L.valid (L.thread.front + roundsTo L.bs
      (P5J.At.ps.findIdx (· == p.place))) ((P5J.At.arr Zp) (seatAtMember L.bs (P5J.At.ps.findIdx (·
      == p.place)) (switchPar p) n).1 (seatAtMember L.bs (P5J.At.ps.findIdx (· == p.place))
      (switchPar p) n).2) (L.thread.front + roundsTo L.bs (P5J.At.ps.findIdx (· == p.place)))
      (switchMsgOff 0 D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p n))
    (pads : ∀ n, n < (switchPar p).sent.size → OwnPads L.Q L.valid (seatAtMember L.bs
      (P5J.At.ps.findIdx (· == p.place)) (switchPar p) n).1 (seatAtMember L.bs (P5J.At.ps.findIdx
      (· == p.place)) (switchPar p) n).2 (fun k _ => switchPadTxt 0 p n k))
    (seats : ∀ x, x ∈ L.N.sent p.link 0 ↔ ∃ n, n < (switchPar p).sent.size ∧ (shapeAt (switchPar p)
      n).answers ≠ 0 ∧ x = seatAtMember L.bs (P5J.At.ps.findIdx (· == p.place)) (switchPar p) n)
    (numbered : ∀ n, n < (switchPar p).sent.size → (shapeAt (switchPar p) n).answers ≠ 0 →
      seatAtMember L.bs (P5J.At.ps.findIdx (· == p.place)) (switchPar p) n ∈ (P5J.At.seats Zp) ∧
      (P5J.At.seats Zp).idxOf (seatAtMember L.bs (P5J.At.ps.findIdx (· == p.place)) (switchPar p)
      n) = (L.N.msgsAt (some p.place)) + n)
    (sits : ∀ n, n < (switchPar p).sent.size → (shapeAt (switchPar p) n).answers ≠ 0 → (∃ x ∈
      (P5J.At.ms Zp Z.lay), SitsAt x (seatAtMember L.bs (P5J.At.ps.findIdx (· == p.place))
      (switchPar p) n).1 (seatAtMember L.bs (P5J.At.ps.findIdx (· == p.place)) (switchPar p) n).2)
      ∧ ∀ x ∈ (P5J.At.ms Zp Z.lay), SitsAt x (seatAtMember L.bs (P5J.At.ps.findIdx (· == p.place))
      (switchPar p) n).1 (seatAtMember L.bs (P5J.At.ps.findIdx (· == p.place)) (switchPar p) n).2 →
      (x.1.l.get x.2).1 = shapeAt (switchPar p) n)
    (asks : Item.carry (p.link - 1) ∈ L.thread.opened (P5J.At.ps.findIdx (· == p.place))) :
    K2SeatedL L (P5J.At.ps.findIdx (· == p.place)) blk D readers lay (segmentsOf Zp Bs.G₀) p q
      before after p.link (L.N.msgsAt (some p.place)) Zp (P5J.At.arr Zp) (P5J.At.seats Zp)
      (P5J.At.ms Zp Z.lay) rad :=
  k2SeatedL_at_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hL hX hcodes
    member (by subst hL; exact k2_placeAt_at_head h O hp) shape half decides sends books
    (serves_at_head h.toAtMg O p hp) (roomy_at_head h.toAtMg O p hp)
    (fits_at_head h.toAtMg O p hp) closes publicAt (k2_noWord_at_head h O hp) trees answersNo
    seedsNo nonZeroNo port msgs pads seats numbered sits
    (link_pos_at_head h.toAtMg O p hp) asks

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.k2SeatedL_at_head
#print axioms ProofFile.Honest.K2.Law.k2_member_at_head
#print axioms ProofFile.Honest.K2.Law.k2_placeAt_at_head
#print axioms ProofFile.Honest.K2.Law.noWordW
#print axioms ProofFile.Honest.K2.Law.k2_noWord_at_head
#print axioms ProofFile.Honest.K2.Law.k2SeatedL_at_place
