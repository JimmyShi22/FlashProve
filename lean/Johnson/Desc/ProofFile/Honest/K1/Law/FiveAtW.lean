-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Law/FiveAtW.lean: THE SHARED "SENDING" (the kind K1) AT W's MEMBER,
number 356 of the first chain: what the first chain's thread owes at that member, at the library's
head. W's member is K1's sending with kind K13's step rowsB joined behind it (K13.atM4). Every letter
of lettersHead is free unless a line says that it is read.

  K1WKeeps               a definition: K1's clause of keeps at W's place, the arm "no link, piece 4"
                         of fHead (Honest/Thread/FHead.lean)
  w_sender_laid          under h: W's lot has its half and the pile more than one row: T1's WSenderLaid
  k1w_of_step            from an accepting step of the member: K1WKeeps
  k1w_rows, k1w_out      behind K1WKeeps a first sample row stays; out stays
  w_plan_written         the kernel: the written plan passes the kind's two tests on the plan
  w_send_yes             K1's half returns at a state at the chain's end that holds W's message, owes
                         no rows, has the plan's codes and a book in step
  k1_w_form_behind       Form at border 357, from Thr at 356 and the member's step
  k1_w_decide            the member's decision returns, from Thr, rounds that fit and hG. K1's guards
                         come of one step back (thr_back_head, at_355, atM3_return_row), recAll_all
                         and bookAt, so of Thr's Made: Said is not read
  k1_w_reply             the reply goes past the member: reads b₀ ≤ 356
  k1_w_acceptedS         AcceptedS at every fall. Reads the half by find?, the member's shape and hG
  k1_w_ridesPast         RidesPast. Reads hKp: keeps at 356 gives K1WKeeps
  k1_w_exchangeS         ExchangeS whole. pinV under the record R; pinW at every member; pileOne and
                         wrow are premises: kind K13's
  k1_w_no_stop           no part stops at the member, where the search finds placeHalf

hG is the one premise of k1_w_decide on the state: behind K1's sending kind K13's shape guards ready4
and pads4 hold (Johnson/Desc/K13/Honest/ShapeM4Ready.lean). No law pays it at a state of a run.

Limits. Under the library's head h, a hypothesis. The full size alone, the format's second hash function alone.
What is stated under Thr or ThrS holds for nothing where these hold of no stand. Nothing on soundness,
completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K1.Law.WSideAtFill
import Johnson.Desc.ProofFile.Honest.K1.Law.WAtHead
import Johnson.Desc.ProofFile.Honest.K1.Law.HeldAtW
import Johnson.Desc.ProofFile.Honest.K1.Law.KeepsMember
import Johnson.Desc.ProofFile.Honest.K9.XkFront
import Johnson.Desc.ProofFile.Honest.K13.GuardsAtM3
import Johnson.Desc.ProofFile.Honest.K13.RidesAtM4
import Johnson.Desc.ProofFile.Honest.Thread.FormXK
import Johnson.Desc.ProofFile.Honest.Thread.FormXKFront
import Johnson.Desc.ProofFile.Honest.Thread.FormXKPub
import Johnson.Desc.ProofFile.Honest.Thread.HeadLetters
import Johnson.Desc.ProofFile.Honest.Thread.PubPAtHead
import Johnson.Desc.ProofFile.Honest.Thread.PinForward
import Johnson.Desc.ProofFile.Honest.Thread.ReachFacts
import Johnson.Desc.K13.Honest.RowsKeeps
import Johnson.Desc.K13.Honest.ShapeM4Ready
import Johnson.Desc.First.Shape.SendW
import Johnson.Desc.ProofFile.Honest.K1.Law.ShapeAtW
import Johnson.Prover.Send.LaterYes
import Johnson.RunOne.KeyMsgOne
import Johnson.Desc.ProofFile.Honest.K1.Law.ExchangeAtPins
import Johnson.Desc.ProofFile.Honest.K1.Law.LaterAccepted
import Johnson.Desc.ProofFile.Honest.Thread.HeadPinW

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc.First (Item samplesHeld)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.K13.Law (wMsgFull)
open VerifiableInference.Desc.K13.Honest (K13RowsKeeps)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS F0T)
open ProofFile.Honest.FirstThread

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **K1's CLAUSE OF keeps AT W's PLACE**: ProofFile's arm of fHead, no link, piece 4. -/
def K1WKeeps (Zp : ProofFile.Pub) (s s' : TS) : Prop :=
  (∃ m, K1SendKeeps s m ∧ K13RowsKeeps (VerifiableInference.Desc.K13.whereOf Zp) m s') ∧
    s'.failed = none

/-- **THE SENDER OF W IS LAID**, under the head: T1's WSenderLaid at every index's letters. -/
theorem w_sender_laid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {W₀ X : Type} (I : WiderIn W₀)
    (O' : OnlineProverArguments) (G : Ground) :
    (wLotAt (X := X) I OnBytes.secondHashFunction O').halves Zp G ≠ [] ∧ 1 < Zp.first.pendingRows := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  refine ⟨?_, ?_⟩
  · rw [wLotAt_halves, msg_w_head h O]
    simp
  · have e : Zp.first.pendingRows = 13 := K13.m3_rows h
    omega

/-- **THE CLAUSE AT W, FROM THE MEMBER's STEP.** -/
theorem k1w_of_step (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {blk : Block TS ProofFile.Cl}
    (hb : cF.blocksInOrder[356]? = some blk) {ft : Nat} {s s' : TS} (hy : IM.Yes ft blk s s') :
    K1WKeeps Zp s s' := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨rs, cols, n, e⟩ := hy
  obtain ⟨w, hw, ⟨rs', gs, d⟩, h0, -⟩ := IM.at_356 h.scope h.reads O hb e
  unfold VerifiableInference.Desc.K13.wBlock VerifiableInference.Desc.K1.wAt at hw
  obtain ⟨msg, -, rfl⟩ := Option.map_eq_some_iff.1 hw
  obtain ⟨m, h1, h2⟩ := VerifiableInference.Desc.Keeps.ebind_ok d
  exact ⟨⟨m, k1_send_keeps h1, VerifiableInference.Desc.K13.Honest.rowsB_rowsKeeps h2⟩, h0⟩

/-- Behind W's member the first sample rows that stand stay. -/
theorem k1w_rows {s s' : TS} (hK : K1WKeeps Zp s s') (o : Nat) (q : OnBytes.Row)
    (hq : rowAt₀ s.st o = some q) : rowAt₀ s'.st o = some q := by
  obtain ⟨⟨m, h1, h2⟩, -⟩ := hK
  have ho : VerifiableInference.Desc.K1.OldMsgs s.st m.st := by
    refine ⟨h1.1.2.2.2.2.1.2.1 , fun j hj => ?_⟩
    rw [h1.2.2.2.2.1 j hj]
  have hm := rowAt₀_old ho hq
  have hs := h2.same
  refine (rowAt₀_same ?_).trans hm
  have e := congrArg (Option.map fun p => p.2.2.1) (hs.2 o)
  simp only [VerifiableInference.Desc.K13.Law.sampleOf, Option.map_map] at e
  exact e

/-- The reply, the pile and the request stay. -/
theorem k1w_out {s s' : TS} (hK : K1WKeeps Zp s s') : s'.out = s.out := by
  obtain ⟨⟨m, h1, h2⟩, -⟩ := hK
  rw [h2.fields.2.2.2.2.1, h1.1.2.1]


/-! ## W's member accepts -/

open VerifiableInference.Desc.First.Shape (wG sendW_returns chainSh sendB)
open VerifiableInference.Desc.K13.Honest (ready4 pads4 sh4 rowsB_returns_shape)

/-- The plan of W's sending at the written numbers passes the kind's own two tests. -/
theorem w_plan_written : VerifiableInference.Desc.K1.planOkOwn VerifiableInference.Desc.K1.parWF = true ∧
    (VerifiableInference.Desc.K1.parWF.tuple.all fun t =>
      (VerifiableInference.Desc.Own.padMade VerifiableInference.Desc.K1.parWF.codes t).isSome) = true := by
  decide +kernel

theorem ite_some_ex {α : Type} {c : Prop} [Decidable c] (hc : c) (a : α) :
    ∃ t, (if c then some a else none) = some t := ⟨a, if_pos hc⟩

/-- **K1's OWN HALF OF W's MEMBER RETURNS**, under the head, at a state at the chain's end that
holds W's message and owes no rows, with the plan's codes and a book in step. -/
theorem w_send_yes (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {s : TS} {a : VerifiableInference.Desc.First.MemOwn}
    (hs : s.here = .mem a) (hm : a.msg = wMsgFull) (hw : s.rowsOwed = none)
    (hc : s.st.codes = Zp.first.codes) (hp : s.book.place.size = s.st.oracles.size)
    {r₁ r₂ : Fmt.RoundView} (gs : List (List (Nat × List UInt64)))
    (hfit : VerifiableInference.Desc.roundsFit
      (VerifiableInference.Desc.K1.rounds (K1.parW Zp.first (wGp Zp) 4 wMsgFull)) [r₁, r₂] = true) :
    ∃ s₁, (VerifiableInference.Desc.K1.sendAtS (K1.parW Zp.first (wGp Zp) 4 wMsgFull) :
      Block TS Unit).decide s [r₁, r₂] gs = .ok s₁ := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hP := parW_written h O
  have hB : sendB (K1.parW Zp.first (wGp Zp) 4 wMsgFull) (chainSh s).rowsOwed (chainSh s).core = true := by
    have e1 : (chainSh s).rowsOwed = none := hw
    have e2 : (chainSh s).core.st.codes = Zp.first.codes := hc
    have e3 : (chainSh s).core.st.oracles.length = (chainSh s).core.book.place.length := by
      show (s.st.oracles.toList.map _).length = s.book.place.toList.length
      simp [hp]
    have e4 := parW_codes Zp.first (wGp Zp) 4 wMsgFull
    unfold sendB
    rw [e1, e2, e3, e4]
    have w1 := w_plan_written.1
    have w2 := w_plan_written.2
    rw [← hP] at w1 w2
    rw [e4] at w2
    simp only [Bool.and_eq_true, beq_self_eq_true, Option.filter_none, Option.isNone_none, and_true,
      true_and, w1]
    exact w2
  have hg : ∃ t, wG (K1.parW Zp.first (wGp Zp) 4 wMsgFull) (chainSh s) = some t := by
    unfold wG
    rw [if_pos hB]
    unfold VerifiableInference.Desc.First.Shape.wStepG
    have e : (chainSh s).atEnd = VerifiableInference.Desc.First.Shape.endSh s.here := rfl
    rw [e, hs]
    have es : (a.msg == (K1.parW Zp.first (wGp Zp) 4 wMsgFull).sent) = true := by
      rw [hm, parW_sent]
      exact beq_self_eq_true _
    exact ite_some_ex es _
  obtain ⟨t, ht⟩ := hg
  obtain ⟨s₁, hd, -⟩ := sendW_returns (gs := gs) ht
    (Johnson.Prover.Send.factors_of_fit _ r₁ r₂ hfit) (VerifiableInference.Desc.K1.answers_len _ r₁ r₂ hfit)
  exact ⟨s₁, hd⟩

set_option maxRecDepth 100000 in
/-- At border 357 no public item that speaks of a ledger's slot is open. -/
theorem no_left_357 :
    (((VerifiableInference.Desc.First.pubSets VerifiableInference.Desc.Sound.moreAll
      VerifiableInference.Desc.Sound.linksFull
      (VerifiableInference.Desc.First.flatPlacesOf VerifiableInference.Desc.Sound.linksFull true))[356 + 1]?.getD []).all
      fun q => match q with
        | .left _ => false
        | .leftOn _ => false
        | _ => true) = true := by
  decide +kernel

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "𝐋" => lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w

/-- **THE FORM BEHIND W's MEMBER**, from the thread in front and the member's step. -/
theorem k1_w_form_behind {blk : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[356]? = some blk) {k : Coins Bk}
    {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn}
    (hT : Thr 𝐋.thread 356 k s m E) (hS : 𝐋.thread.Stepped blk k s m E ds y cols s') :
    𝐋.thread.Form (356 + 1) k s' y.2 := by
  have hy : IM.Yes 0 blk s s' := ⟨_, _, _, hS.2⟩
  have hF := hT.2.2.1
  have h0 : s.failed = none := Option.isNone_iff_eq_none.1 hF.1
  have h1 : s'.failed = none := mark_W_head h hblk 0 hy
  have hx := xk_of_form 𝐋 hF
  have hxE := K9.xk_ew_of_eq (head_pub_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (head_more_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (head_links_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
    (head_ps_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) hx
  have hxB := xk_W_head h hblk _ _ 0 hy h0 hxE
  rw [head_links_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w,
    head_ps_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w] at hxB
  have hXK := head_xk_of_pub h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hF hxB
    (fun he => K9.ew_gives_pub (head_pub_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
      (head_more_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
      (head_links_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w)
      (head_ps_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w) he)
  have hs := held_of_form 𝐋 hF
  have hbk := (IM.xk_parts hx).2.2.2.1
  rw [← head_ps_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w] at hbk
  rw [← head_links_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w,
    ← head_ps_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w] at hs
  have hlen : 356 ≤ cF.blocksInOrder.length := by
    obtain ⟨hl, -⟩ := List.getElem?_eq_some_iff.1 hblk
    omega
  have hre := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hlen hT
  have hHeld := samples_W_head h hblk 𝐋.mgP rfl _ 0 hre hbk hy hs
  rw [head_links_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w,
    head_ps_W h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w] at hHeld
  refine form_behind_of_xk 𝐋 hS h1 hXK hHeld ?_
  refine head_pubP_of_left h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w _ _ ?_ ?_
  · intro q hq
    exfalso
    have e := head_more_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    unfold P1K2.pubAt at hq
    rw [e] at hq
    have := List.all_eq_true.1 no_left_357 _ hq
    simp at this
  · intro q hq
    exfalso
    have e := head_more_all h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
    unfold P1K2.pubAt at hq
    rw [e] at hq
    have := List.all_eq_true.1 no_left_357 _ hq
    simp at this

/-- **W's MEMBER's DECISION RETURNS**, from the thread in front, on rounds that fit, under the
shape guards of kind K13 behind the sending. -/
theorem k1_w_decide {blk : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[356]? = some blk) {k : Coins Bk}
    {s : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env}
    (hT : Thr 𝐋.thread 356 k s m E) {R₁ : List Fmt.RoundView}
    (gs : List (List (Nat × List UInt64)))
    (hfit : VerifiableInference.Desc.roundsFit blk.rounds R₁ = true)
    (hG : ∀ rs gs s₁, (VerifiableInference.Desc.K1.sendAtS (K1.parW Zp.first (wGp Zp) 4 wMsgFull) :
        Block TS Unit).decide s rs gs = .ok s₁ →
      ready4 (VerifiableInference.Desc.K13.whereOf Zp).lin (sh4 s₁) = true ∧
        pads4 (VerifiableInference.Desc.K13.whereOf Zp).lin (sh4 s₁) = true) :
    ∃ s', blk.decide s R₁ gs = .ok s' := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hlen : 355 + 1 ≤ cF.blocksInOrder.length := by
    obtain ⟨hl, -⟩ := List.getElem?_eq_some_iff.1 hblk
    omega
  have hF := hT.2.2.1
  have h0 : s.failed = none := Option.isNone_iff_eq_none.1 hF.1
  -- one step back: the batching has left a claim, W's message and no rows owed
  obtain ⟨s₀, b₅, hb5, -, R₀, c₀, n₀, e₀⟩ :=
    thr_back_head h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w (b := 355) hlen hT
  obtain ⟨⟨rs', gs', d⟩, -, -⟩ := IM.at_355 h.scope h.reads O hb5 e₀
  obtain ⟨t, msg, x₁, hh, o, ht, hm, -, hr, es⟩ :=
    VerifiableInference.Desc.K13.Honest.atM3_return_row d
  have hmw : msg = wMsgFull := Option.some.inj (hm.symm.trans (msg_w_head h O))
  subst hmw
  obtain ⟨a₀, hs, ham⟩ : ∃ a₀, s.here = .mem a₀ ∧ a₀.msg = wMsgFull := by
    rw [es]
    exact ⟨_, rfl, rfl⟩
  have hw : s.rowsOwed = none := by rw [es]
  -- the codes and the book, from the thread in front
  have hlen' : 356 ≤ cF.blocksInOrder.length := by omega
  have hre := thr_reach h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hlen' hT
  have hc : s.st.codes = Zp.first.codes :=
    (Meaning.K2.recAll_all h.scope h.reads O (P5J.flat_ok h.toAtMg) hre h0).codes
  have hbk := (IM.xk_parts (xk_of_form 𝐋 hF)).2.2.2.1
  have hp : s.book.place.size = s.st.oracles.size := by
    unfold VerifiableInference.Desc.First.bookAt at hbk
    simp only [Bool.and_eq_true, beq_iff_eq] at hbk
    exact hbk.1.2
  -- the member is the lot's, alone
  obtain ⟨-, -, -, ⟨b3, b3', w', e3, -, hw', rfl, hla⟩⟩ := IM.back_of O
  obtain rfl := Option.some.inj (((IM.back_numbers h.scope h.reads O).1 3 b3 e3).symm.trans hblk)
  unfold VerifiableInference.Desc.K13.wBlock VerifiableInference.Desc.K1.wAt at hw'
  obtain ⟨msg', hm', rfl⟩ := Option.map_eq_some_iff.1 hw'
  obtain rfl : msg' = wMsgFull := Option.some.inj (hm'.symm.trans (msg_w_head h O))
  rw [IM.alone_rounds hla] at hfit
  have hfit' : VerifiableInference.Desc.roundsFit
      (VerifiableInference.Desc.K1.rounds (K1.parW Zp.first (wGp Zp) 4 wMsgFull)) R₁ = true := hfit
  obtain ⟨r₁, r₂, rfl⟩ := Johnson.RunOne.KeyMsg.two_of_fit _ _ R₁ hfit'
  obtain ⟨s₁, d₁⟩ := w_send_yes h hs ham hw hc hp
    (gs.take (VerifiableInference.Desc.K1.sendAtS (Cl := Unit) (K1.parW Zp.first (wGp Zp) 4 wMsgFull)).openings) hfit'
  obtain ⟨g1, g2⟩ := hG _ _ _ d₁
  obtain ⟨s', d₂, -⟩ := rowsB_returns_shape (Cl := Unit) (P := VerifiableInference.Desc.K13.whereOf Zp) g1 g2
    [] (gs.drop (VerifiableInference.Desc.K1.sendAtS (Cl := Unit) (K1.parW Zp.first (wGp Zp) 4 wMsgFull)).openings)
  have dd : (VerifiableInference.Desc.K13.atM4 (VerifiableInference.Desc.K13.whereOf Zp)
      (VerifiableInference.Desc.K1.sendAtS (K1.parW Zp.first (wGp Zp) 4 wMsgFull)) : Block TS Unit).decide s
      [r₁, r₂] gs = .ok s' := by
    show ((VerifiableInference.Desc.K1.sendAtS (K1.parW Zp.first (wGp Zp) 4 wMsgFull) : Block TS Unit).decide s
      [r₁, r₂] _).bind _ = _
    rw [d₁]
    exact d₂
  have k1 := k1_send_keeps d₁
  have k2 := VerifiableInference.Desc.K13.Honest.rowsB_rowsKeeps d₂
  have h1 : s'.failed = none := k2.noMark.2 (k1.1.1.trans h0)
  have hsame : ProofFile.sameReply s s' = true :=
    VerifiableInference.Reads.Pass.same_of_reply
      (congrArg (·.reply) (k2.fields.2.2.2.2.1.trans k1.1.2.1))
  exact ⟨s', (IM.yes_alone hla (by decide) s s' _ gs).2 ⟨dd, h1, hsame⟩⟩


/-- **THE REPLY GOES PAST W's MEMBER** (the column h₀ of owesS_head_form at 356). -/
theorem k1_w_reply {blk : Block TS ProofFile.Cl} (hblk : cF.blocksInOrder[356]? = some blk) {k : Coins Bk}
    {s s' : TS} {m : Mid (Local W₀ Rc ProofFile.Inst Tr) X} {E : Env} {ds : List Fmt.Drawn}
    {y : List Played × Mid (Local W₀ Rc ProofFile.Inst Tr) X}
    {cols : List VerifiableInference.Desc.OpenedColumn} (hb : b₀ ≤ 356)
    (hT : Thr 𝐋.thread 356 k s m E) (hS : 𝐋.thread.Stepped blk k s m E ds y cols s') :
    s'.out.reply = some m.st.input.x.asked := by
  have hr := head_reply h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hT.2.2.2.2.2.1
  rw [k1w_out (k1w_of_step h hblk (ft := 0) ⟨_, _, _, hS.2⟩)]
  exact hr

/-- **AcceptedS AT W's MEMBER**, at every fall. -/
theorem k1_w_acceptedS {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst}
    {J : SendJob (PlaceIn ProofFile.Inst) X} {blk₀ : Block TS ProofFile.Cl} (hb : cF.blocksInOrder[356]? = some blk₀)
    (hsh : blk₀.place = J.P.place ∧ blk₀.rounds = VerifiableInference.Desc.K1.rounds J.P ∧
      blk₀.oracles = VerifiableInference.Desc.K1.oracles J.P)
    (hh : (𝐋.thread.hs.find? fun g => g.place == J.P.place) = some (placeHalf wit J))
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hG : ∀ k s m E, ThrS 𝐋.thread Said 356 k s m E → ∀ rs gs s₁,
      (VerifiableInference.Desc.K1.sendAtS (K1.parW Zp.first (wGp Zp) 4 wMsgFull) :
        Block TS Unit).decide s rs gs = .ok s₁ →
      ready4 (VerifiableInference.Desc.K13.whereOf Zp).lin (sh4 s₁) = true ∧
        pads4 (VerifiableInference.Desc.K13.whereOf Zp).lin (sh4 s₁) = true)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    AcceptedS 𝐋.thread Said fall 356 := by
  intro blk hblk k s m E ds y cols hA hd _ _ hM
  obtain rfl : blk = blk₀ := Option.some.inj (hblk.symm.trans hb)
  have hM' := hM
  unfold Thread.Moved at hM'
  obtain ⟨⟨l, hl, hy⟩, hc⟩ := hM'
  have ho := (chainSteps_rows [blk] 𝐋.thread.hs l hl).1 blk (List.mem_singleton.2 rfl)
  have hf : (𝐋.thread.hs.find? fun g => g.place == blk.place) = some (placeHalf wit J) := by
    rw [hsh.1]
    exact hh
  obtain ⟨c, -, rfl⟩ := steps_one_half hf hl
  have hr : (placeHalf (V := Local W₀ Rc ProofFile.Inst Tr) wit J).rounds = blk.rounds.length := by
    rw [hsh.2.1]
    rfl
  have hF := (fits_played hr ho hy hd hc).1.1
  obtain ⟨s', hs'⟩ := k1_w_decide h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w hb hA.1
    (regroup ((groupsOf 𝐋.thread.ft blk.rounds ds).map (·.length)) cols)
    ((VerifiableInference.Desc.roundsFit_noDigest _ _).trans hF) (hG k s m E hA)
  refine ⟨s', ?_⟩
  unfold Thread.Stepped
  exact ⟨hM, (step_iff_decide s s' hr ho hy hd hc).2 hs'⟩

/-- **WHAT GOES PAST W's MEMBER RIDES PAST IT.** hKp: the letter's clause at W's place. -/
theorem k1_w_ridesPast (hKp : ∀ s s', 𝐋.keeps 356 s s' → K1WKeeps Zp s s') :
    RidesPast 𝐋.thread 356 :=
  K13.k13_m4_rides _ K13.m4_pass_is.1 (fun _ s _ _ s' _ hk => (hKp s s' hk).2)
    (ridesPastAt_pinI_older h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w
      fun _ s _ _ s' _ hk o q hq => k1w_rows (hKp s s' hk) o q hq)

/-- **THE EXCHANGE AT W's MEMBER**: pinV is K1's; pinW holds of the thread's witness; pileOne and
wrow are the batching's kind's, handed on by name. -/
theorem k1_w_exchangeS {blk : Block TS ProofFile.Cl} {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst}
    {J : SendJob (PlaceIn ProofFile.Inst) X} {own₀ : X} {arr : ℕ → ℕ → ℕ} {seats₀ : List (ℕ × ℕ)}
    {ms : List VerifiableInference.Desc.Sound.Mem} {rad : ℕ → ℕ}
    (R : K1Seated 𝐋 356 blk wit J own₀ .w arr seats₀ ms rad)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hPile : ExchangeAtS 𝐋.thread Said 356 Item.pileOne)
    (hWrow : ExchangeAtS 𝐋.thread Said 356 Item.wrow) :
    ExchangeS 𝐋.thread Said 356 := by
  have e : (𝐋.thread.row 356).owes = [Item.pinV, Item.pileOne, Item.pinW, Item.wrow] := by
    show (FirstRows.rows P5J.At.links P5J.At.ps 356).owes = _
    decide +kernel
  have key : ∀ i : VerifiableInference.Desc.First.Item, i ∈ [Item.pinV, Item.pileOne, Item.pinW, Item.wrow] →
      ExchangeAtS 𝐋.thread Said 356 i := by
    intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact exchange_pinV R Said
    · exact hPile
    · exact exchangeAtS_of _ _ (exchangeAt_pinW h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w 356)
    · exact hWrow
  refine (exchangeS_iff _ _).2 fun i hi => key i ?_
  rw [e] at hi
  exact hi

/-- **NO PART STOPS AT W's MEMBER.** -/
theorem k1_w_no_stop {blk : Block TS ProofFile.Cl} {wit : Local W₀ Rc ProofFile.Inst Tr → PlaceIn ProofFile.Inst}
    {J : SendJob (PlaceIn ProofFile.Inst) X}
    (hf : (𝐋.thread.hs.find? fun g => g.place == blk.place) = some (placeHalf wit J))
    (v : Option (Local W₀ Rc ProofFile.Inst Tr)) (loc ds : List Fmt.Drawn) :
    chainStopAt v [blk] 𝐋.thread.hs loc ds = none := by
  simp only [chainStopAt, hf, Option.bind_some, k1_row_silent]
  rfl

end
end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.w_sender_laid
#print axioms ProofFile.Honest.K1.k1w_of_step
#print axioms ProofFile.Honest.K1.k1w_rows
#print axioms ProofFile.Honest.K1.k1w_out
#print axioms ProofFile.Honest.K1.k1_w_form_behind
#print axioms ProofFile.Honest.K1.w_plan_written
#print axioms ProofFile.Honest.K1.w_send_yes
#print axioms ProofFile.Honest.K1.k1_w_decide
#print axioms ProofFile.Honest.K1.k1_w_acceptedS
#print axioms ProofFile.Honest.K1.k1_w_ridesPast
#print axioms ProofFile.Honest.K1.k1_w_exchangeS
#print axioms ProofFile.Honest.K1.k1_w_no_stop
#print axioms ProofFile.Honest.K1.k1_w_reply
