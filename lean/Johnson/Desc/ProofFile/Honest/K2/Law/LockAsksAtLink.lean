-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/LockAsksAtLink.lean: the kind "the code switch" (K2):
`LockAsks` (ClaimOfLock.lean of this folder), WHOLE, ALL FOUR LIMBS, AT A RUN's COINS, AT THE 23
LINK PLACES (m < 23): a gathering. One structure: premises' forms; two statements with their proofs:
joins. THEY MAY HOLD EMPTILY: see the docstrings.

WHICH SLOT IT IS FOR. `LockAsks` is the one premise hA of `claim_at_yes` (ClaimAtYes.lean of this
folder), which has the field claim that the kind's exchange under the head
(`k2_exchange_of_values`, MadeValuesLeft.lean, of other authors) leaves at each switch. The exchange
is one of the four debts that the frame's `OwesS` (Honest/Thread/PaysS.lean) asks at every number of
the first chain; `OwesS` there is a premise from which a value of `ThreadsC`
(Honest/Law/ThreadStratC.lean) is built; acceptance at a request goes through that structure.

  `MaskAsks`        what `first_fresh_clause` asks on the opening's message that is the first
                    segment's fold's fresh mask, as one named record of nine fields
  `link_lockAsks`   1 ≤ m < 23 ⊢ `LockAsks` at table := `freshTable`, own := `lotOwn segsW p …`,
                    heard := hdL, k := the later switch's carried stretches, at the front fx, at the
                    words that `wordsFirst` reads off the Script's witness
  `first_lockAsks`   m = 0: the same, every sender of the kind K1

LIMB BY LIMB. (1) the challenges heard: `link_gamma_heard` (GammaAtFront.lean): where hdL is what
the rounds drew at which the fold over the sub-protocols in front returns the reached state · (2)
(3) the members: `link_members_limbs`, `first_members_limbs` (MembersAtLink.lean) · (4) the mask
sent ahead: `link_fresh_clause` (FreshClause.lean), `first_fresh_clause` (FreshClauseFirst.lean).
`LockAsks` speaks at the written `segsW`; these at `segmentsOf Zp Bs.G₀`: one under the head
(`segments_at_head`, PlacesWritten.lean): called here. Sg and y', which `LockAsks` binds by "for
all", stand here as letters with their look-ups hS, hy': each is one value.

WHAT STAYS A PREMISE. What the four files named leave; their heads tell who has something toward
each. In short: THE SCRIPT's two hypotheses at every message of the closed group (at the opening
switch's messages in front of the last OFF THE PAD; at its last, the mask, the whole text) · at each
message of a sender of the kind K1 besides: THE CUT of the run's coins, THE BOOK's entry, THE DATA ·
returns · two tests on the book · f₀, hhd: the run's rounds.

Limits. One run's coins. No run is given at which the head's premise and "reached" hold together,
nor one at which all premises hold. UNDER "THERE IS" IN HL, HF AND HM STANDS, AMONG PUBLIC THINGS,
cs: A CUT OF THE RUN's COINS: the record's field cut pins it to k. Not at the places 339 and 353. It
speaks at every place of each member's main rows, the pads' places too, and at mask rows: entries
that hold coins: equations between two texts' values: what is WRITTEN where. The full size and the
format's second hash function alone. NOT IN FRONT OF A LAW OVER COINS. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.MembersAtLink
import Johnson.Desc.ProofFile.Honest.K2.Law.ClaimOfLock
import Johnson.Desc.ProofFile.Honest.K2.Law.GammaAtFront
import Johnson.Desc.ProofFile.Honest.K2.Law.FreshClause
import Johnson.Desc.ProofFile.Honest.K2.Law.FreshClauseFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open OnBytes (ceilLog2 noId)
open VerifiableInference.Desc (Block Chain foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (seatK10)
open VerifiableInference.Desc.LinkJoin (loAt)
open VerifiableInference.Desc.K1 (parL noL firstPar gpOf)
open VerifiableInference.Desc.K2.Honest (Left)
open VerifiableInference.Desc.K2.Honest.Returns (link_door)
open VerifiableInference.Desc.K13.Honest (roundsAhead)
open VerifiableInference.Desc.Sound (allOf EAll MsgT wordsFirst)
open Johnson.Prover.Send (shapeAt)
open ProofFile.Honest.FirstThread (Script OwnMsgs OwnPads)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {W₀ Rc Xi Tr W X Cells Tok : Type} {Bk : ProverCoinCounts}

/-- **WHAT IS ASKED ON THE OPENING's MESSAGE THAT IS THE FIRST SEGMENT's FOLD's FRESH MASK.** n: its
number in the opening's sending. ix: the number of the book's entry among the switch's carried
stretches. A structure of premises' forms. Nothing here proves that it can be met. It names a run's
coins: k, and the sender's cut cs. -/
structure MaskAsks (Zp : ProofFile.Pub) (P₀ : VerifiableInference.Desc.K1.Par)
    (ρ₀ : Nat → Option K1.Ride) (n ix ch : Nat) (p : SwitchPlace) (k : Coins Bk)
    (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT) (Vd : Local W₀ Rc Xi Tr → Prop) (N : Nat)
    (wit : Local W₀ Rc Xi Tr → W) (J : K1.SendJob W X) (own₀ : X)
    (cs : Cs (K1.dueR J.P J.ride)) (e : Ahead) (front : Nat) : Prop where
  plan : P₀ = J.P
  ride : ρ₀ = J.ride
  cut : K1.lentCut k ch ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = some cs
  entry : ((Bk.ahead.filter fun y => y.spender == ⟨p.place, 0⟩).filter (!·.once))[ix]? = some e
  owner : e.owner = ⟨J.P.place, 0⟩
  start : e.start = K1.startR J.P J.ride n
  count : e.count = K1.dueMsg J.P.codes (shapeAt J.P n) (J.ride n)
  msgs : OwnMsgs Q Vd N (P5J.At.arr Zp (VerifiableInference.Desc.First.Close.maskTree 0)
    (VerifiableInference.Desc.First.Close.maskPart 0)) front (K1.msgTxt ch wit J own₀ n)
  pads : OwnPads Q Vd (VerifiableInference.Desc.First.Close.maskTree 0)
    (VerifiableInference.Desc.First.Close.maskPart 0) (fun k _ => K1.padTxt ch J n k)

/-- IT MAY HOLD EMPTILY: hmS, hpS, hmF, hpF AND HL ARE PROVED OF NO SCRIPT, BOOK OR FILLING; it
stands under the head's premise and "reached" too. One run's coins: never quoted for a law. UNDER
"THERE IS" IN HL STANDS cs, A CUT OF THE RUN's COINS, pinned to k by the record's field cut.

**`LockAsks`, WHOLE, AT A LINK PLACE WHOSE CLOSED GROUP A SWITCH OPENED** (1 ≤ m < 23). p₀: the
switch that sent the closed group's first sending. p: the later switch. -/
theorem link_lockAsks (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (hm1 : 1 ≤ m) (h23 : m < 23)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (m + 1) + 2) a) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt (ProofFile.pAtK2 Zp m) a.1.2 = some fx)
    {p₀ p : SwitchPlace} (hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀) (hp : p ∈ switchPlaces Zp Bs.G₀)
    (e₀ : p₀.link = m) (e₁ : p.link = m + 1)
    (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT) (Vd : Local W₀ Rc Xi Tr → Prop)
    (N ch fx₀ : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout)
    -- THE SCRIPT's TWO HYPOTHESES AT EACH MESSAGE OF THE OPENING SWITCH IN FRONT OF ITS LAST
    (hmS : ∀ n (i : Fin (loAt m).length), n < (switchSent p₀.sizes p₀.others).size - 1 →
      (VerifiableInference.Desc.First.Close.membersOf (loAt m))[n]? = some i →
      OwnMsgs Q Vd N (P5J.At.arr Zp (seatK10 (loAt m) (P5J.At.pseats Zp) m i).1
          (seatK10 (loAt m) (P5J.At.pseats Zp) m i).2) fx₀
        (switchMsgOff ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀ n))
    (hpS : ∀ n (i : Fin (loAt m).length), n < (switchSent p₀.sizes p₀.others).size - 1 →
      (VerifiableInference.Desc.First.Close.membersOf (loAt m))[n]? = some i →
      OwnPads Q Vd (seatK10 (loAt m) (P5J.At.pseats Zp) m i).1
        (seatK10 (loAt m) (P5J.At.pseats Zp) m i).2 (fun k _ => switchPadTxt ch p₀ n k))
    -- AND AT ITS LAST, THE FOLD's FRESH MASK
    (hmF : OwnMsgs Q Vd N (P5J.At.arr Zp (VerifiableInference.Desc.First.Close.maskTree m)
        (VerifiableInference.Desc.First.Close.maskPart m)) fx₀
      (switchMsgTxt ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀
        ((switchSent p₀.sizes p₀.others).size - 1)))
    (hpF : OwnPads Q Vd (VerifiableInference.Desc.First.Close.maskTree m)
      (VerifiableInference.Desc.First.Close.maskPart m)
      (fun k _ => switchPadTxt ch p₀ ((switchSent p₀.sizes p₀.others).size - 1) k))
    (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hv : Vd w) (hdL ds : List Fmt.Drawn)
    (hN : N ≤ (hdL ++ ds).length) (hfx₀ : fx₀ ≤ hdL.length)
    (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries) (h₀ : handed ch p₀ k = some c₀)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hc : handed ch p k = some c)
    (hs : carriedSame Bk p₀ p = true) (hf : carriedFits Bk (switchPlaces Zp Bs.G₀) p = true)
    (hgl : roundsAhead cF.blocksInOrder (VerifiableInference.Desc.First.K2Caller.noAt (m - 1)) ≤ fx₀)
    (hD : ∀ s i ad, s < p₀.link → p.addrs s i = some ad → (D w.x).heardAt ad ≤ fx₀)
    {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀ c₀ w
      (hdL.take fx₀) = .ok V)
    -- THE RUN's ROUNDS
    {zz : ProofFile.InstPub} {Rr R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn}
    (f₀ : foldBlocks 0 (cF.blocksInOrder.take (14 * (m + 1) + 2)) (ProofFile.startS Zp zz) Rr C =
      .ok (a.1.2, R₀, C₀)) (hhd : hdL = Rr.map (·.drawn))
    -- TWO LOOK-UPS
    {y' : Option (Left × List OnBytes.OracleShape) × Nat}
    (hy' : closingFrom freshTable (lotOwn (segmentsOf Zp Bs.G₀) p (D w.x) (readers w) hdL) hdL
      (Stretch.carried p.carries c.2.2) ((segmentsOf Zp Bs.G₀).take m) 0 0 none = .ok y')
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[m]? = some Sg)
    -- THE TWO LATER SENDERS
    (HL : ∀ q, q < 2 → ∃ (wit : Local W₀ Rc Xi Tr → W) (J : K1.SendJob W X) (own₀ : X)
      (cs : Cs (K1.dueR J.P J.ride)) (e : Ahead)
      (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (front : Nat),
      SharedAsks Zp cF.blocksInOrder (parL Zp Bs.G₀ m (q == 1)) (K1.rideOf none) (noL m (q == 1)) 0
        (y'.2 + ((Sg.sent.headD #[]).size - 1) + 1 + q) ch p k
        (lotOwn (segmentsOf Zp Bs.G₀) p (D w.x) (readers w) hdL (0 + m)
          ((Sg.sent.headD #[]).size - 1 -
            (if (y'.1.map (·.1)).isSome then 1 + Sg.sizes.kept.length else 0) + q))
        Q Vd N w (hdL ++ ds) wit J own₀ cs e dataK front) :
    LockAsks freshTable (lotOwn segsW p (D w.x) (readers w) hdL) hdL
      (Stretch.carried p.carries c.2.2) m fx
      (wordsFirst (P5J.At.arr Zp) fx.st a.1.2.book (Q.wit k w (hdL ++ ds))) := by
  have hq := (link_door h h23 a hr).1
  unfold LockAsks
  rw [← segments_at_head h.toAtMg O]
  intro Sg₁ y₁ hS₁ hy₁
  obtain rfl : Sg₁ = Sg := Option.some.inj (hS₁.symm.trans hS)
  obtain rfl : y₁ = y' := Except.ok.inj (hy₁.symm.trans hy')
  refine ⟨?_, fun R hR => ?_⟩
  · rw [hhd]
    exact link_gamma_heard h h23 a hr hq hfx f₀ (by rw [← segments_at_head h.toAtMg O]; exact hS)
  · have all := link_members_limbs h O hm1 h23 a hr hfx hp₀ hp e₀ e₁ Q Vd N ch fx₀ D readers lay
      hmS hpS k w hv hdL ds hN hfx₀ c₀ h₀ c hc hs hf hgl hD hV hy' hS HL hR
    obtain ⟨Sg₂, hS₂, hF⟩ := link_fresh_clause h O hm1 h23 a hr hfx hp₀ hp e₀ e₁ Q Vd N ch fx₀ D
      readers lay hmF hpF k w hv hdL ds hN hfx₀ c₀ h₀ c hc hs hf hgl hD hV hy'
    obtain rfl : Sg₂ = Sg₁ := Option.some.inj (hS₂.symm.trans hS)
    exact ⟨fun i b j hi hb => (all i hi).1 b j hb, fun i b j hi hb => (all i hi).2 b j hb,
      (hF R hR).2⟩

/-- IT MAY HOLD EMPTILY: HF, HL AND HM ARE PROVED OF NO SCRIPT, BOOK OR FILLING; it stands under the
head's premise and "reached" too. One run's coins: never quoted for a law. UNDER "THERE IS" IN HF,
HL AND HM STANDS cs, A CUT OF THE RUN's COINS, pinned to k by each record's field cut.

**`LockAsks`, WHOLE, AT THE SWITCH INTO THE GROUP 1**, whose closed group is the first segment's
(m = 0): every sender is of the kind K1. p: that switch. own: a letter for the closing's own data.
-/
theorem first_lockAsks (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (0 + 1) + 2) a) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt (ProofFile.pAtK2 Zp 0) a.1.2 = some fx)
    (ch : Nat) (p : SwitchPlace) (k : Coins Bk)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hc : handed ch p k = some c)
    (own : Nat → Nat → Nat → Nat → Cb.Gl.E)
    (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT) (Vd : Local W₀ Rc Xi Tr → Prop) (N : Nat)
    (w : Local W₀ Rc Xi Tr) (hv : Vd w) (hdL ds : List Fmt.Drawn) (hN : N ≤ (hdL ++ ds).length)
    -- THE RUN's ROUNDS
    {zz : ProofFile.InstPub} {Rr R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn}
    (f₀ : foldBlocks 0 (cF.blocksInOrder.take (14 * (0 + 1) + 2)) (ProofFile.startS Zp zz) Rr C =
      .ok (a.1.2, R₀, C₀)) (hhd : hdL = Rr.map (·.drawn))
    -- TWO LOOK-UPS
    {y' : Option (Left × List OnBytes.OracleShape) × Nat}
    (hy' : closingFrom freshTable own hdL (Stretch.carried p.carries c.2.2)
      ((segmentsOf Zp Bs.G₀).take 0) 0 0 none = .ok y')
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[0]? = some Sg)
    -- THE OPENING's MESSAGES IN FRONT OF THE FOLD's MASK
    (HF : ∀ n, n < (Sg.sent.headD #[]).size - 1 → ∃ (wit : Local W₀ Rc Xi Tr → W)
      (J : K1.SendJob W X) (own₀ : X) (cs : Cs (K1.dueR J.P J.ride)) (e : Ahead)
      (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (front : Nat),
      SharedAsks Zp cF.blocksInOrder (firstPar Bs.G₀.first (gpOf Zp))
        (K1.rideOf (K1.firstFold Bs.G₀.first)) 2 n (y'.2 + n) ch p k
        (dataAtOf Sg (y'.1.map (·.1)) (own (0 + 0)) n)
        Q Vd N w (hdL ++ ds) wit J own₀ cs e dataK front)
    -- THE TWO LATER SENDERS
    (HL : ∀ q, q < 2 → ∃ (wit : Local W₀ Rc Xi Tr → W) (J : K1.SendJob W X) (own₀ : X)
      (cs : Cs (K1.dueR J.P J.ride)) (e : Ahead)
      (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (front : Nat),
      SharedAsks Zp cF.blocksInOrder (parL Zp Bs.G₀ 0 (q == 1)) (K1.rideOf none) (noL 0 (q == 1)) 0
        (y'.2 + ((Sg.sent.headD #[]).size - 1) + 1 + q) ch p k
        (own (0 + 0) ((Sg.sent.headD #[]).size - 1 -
          (if (y'.1.map (·.1)).isSome then 1 + Sg.sizes.kept.length else 0) + q))
        Q Vd N w (hdL ++ ds) wit J own₀ cs e dataK front)
    -- THE FOLD's FRESH MASK
    (HM : ∃ (wit : Local W₀ Rc Xi Tr → W) (J : K1.SendJob W X) (own₀ : X)
      (cs : Cs (K1.dueR J.P J.ride)) (e : Ahead) (front : Nat),
      MaskAsks Zp (firstPar Bs.G₀.first (gpOf Zp)) (K1.rideOf (K1.firstFold Bs.G₀.first))
        ((Sg.sent.headD #[]).size - 1) (y'.2 + ((Sg.sent.headD #[]).size - 1)) ch p k Q Vd N wit J
        own₀ cs e front) :
    LockAsks freshTable own hdL (Stretch.carried p.carries c.2.2) 0 fx
      (wordsFirst (P5J.At.arr Zp) fx.st a.1.2.book (Q.wit k w (hdL ++ ds))) := by
  have h23 : 0 < 23 := by omega
  have hq := (link_door h h23 a hr).1
  unfold LockAsks
  rw [← segments_at_head h.toAtMg O]
  intro Sg₁ y₁ hS₁ hy₁
  obtain rfl : Sg₁ = Sg := Option.some.inj (hS₁.symm.trans hS)
  obtain rfl : y₁ = y' := Except.ok.inj (hy₁.symm.trans hy')
  refine ⟨?_, fun R hR => ?_⟩
  · rw [hhd]
    exact link_gamma_heard h h23 a hr hq hfx f₀ (by rw [← segments_at_head h.toAtMg O]; exact hS)
  · have all := first_members_limbs h O a hr hfx ch p k c hc hS hR Q Vd N w hv hdL ds hN HF HL
    obtain ⟨wit, J, own₀, cs, e, front, M⟩ := HM
    have F := first_fresh_clause h O a hr hfx p hS wit J own₀ M.plan M.ride Q Vd N ch front M.msgs
      M.pads k w hv (hdL ++ ds) hN M.cut c hc e M.entry M.owner M.start M.count hR
    exact ⟨fun i b j hi hb => (all i hi).1 b j hb, fun i b j hi hb => (all i hi).2 b j hb, F.2⟩

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.MaskAsks
#print axioms ProofFile.Honest.K2.Law.link_lockAsks
#print axioms ProofFile.Honest.K2.Law.first_lockAsks
