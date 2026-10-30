-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/MembersAtLink.lean: the kind "the code switch" (K2): THE LOCK's
TWO CLAUSES ON THE CLOSED GROUP's MEMBERS, WHOLE, AT A RUN's COINS, AT THE 23 LINK PLACES (m < 23):
at EVERY member of the carried layout: a gathering of MemberClause.lean, MemberClauseK1.lean and
MembersCover.lean of this folder. One structure: premises' forms; statements with their proofs:
joins. THEY MAY HOLD EMPTILY: see the docstrings.

WHICH SLOT IT IS FOR. The second and third limb of `LockAsks` (ClaimOfLock.lean of this folder),
whole, at a link place. `claim_at_yes` (ClaimAtYes.lean) has the field claim of the kind's exchange
under the head from `LockAsks`; the exchange is one of the four debts that the frame's `OwesS`
(Honest/Thread/PaysS.lean) asks at every number of the first chain; `OwesS` there is a premise from
which a value of `ThreadsC` (Honest/Law/ThreadStratC.lean) is built; acceptance at a request goes
through that structure.

  `SharedAsks`      WHAT `link_member_clause_later` AND `link_member_clause_first` ASK ON ONE
                    MESSAGE OF A SENDER OF THE KIND K1, as one named record of eleven fields: the
                    job's plan and ride · its cut of the run's coins · the book's entry, with owner,
                    start and count · the data · the Script's two hypotheses · the rows at two data
  `later_tied`, `first_tied`   the record ⊢ `MemberTied` at that message's member
  `link_members_limbs`   1 ≤ m < 23: `MemberTied` at every member of the carried layout
  `first_members_limbs`   m = 0: the same, the opening in the switch's stead

The two ends are "at every i below the number of the layout's members, `MemberTied`": the two limbs
of `LockAsks` with the two "for all i" drawn into one (`MemberTied`'s text is theirs, i fixed).

THE FOUR SORTS OF PREMISE THAT NO FILE OF THIS FOLDER PAYS AT THE LATER SENDERS
(MemberClauseK1.lean's head tells who has something toward each): THE BOOK's entry for the carried
stretch · THE DATA: that `K1.rowsR` lays at the closing's own data what the sender's job lays at its
own · THE SCRIPT's two hypotheses at the sender's texts · THE SENDER's CUT of the run's coins. At
the opening's messages (m = 0) the same four, message by message. At the switch's messages (m ≥ 1):
the Script's two, the first OFF THE PAD: the form of the kind's record's field msgs, at another
spelling of the seat.

Limits. One run's coins. No run is given at which the head's premise and "reached" hold together.
`SharedAsks` IS SHOWN OF NO SCRIPT, BOOK OR FILLING. Not at the places 339 and 353. Nothing on
`LockAsks`' first limb (the challenges heard) nor its fourth (the mask sent ahead). It speaks at
every place of each member's main rows, the pads' places too, and at their mask rows: entries that
hold coins: equations between two texts' values: what is WRITTEN where. The full size and the
format's second hash function alone. NOT IN FRONT OF A LAW OVER COINS. Nothing on any
property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.MemberClauseK1
import Johnson.Desc.ProofFile.Honest.K2.Law.MembersCover
import Johnson.Desc.ProofFile.Honest.K2.Law.TiesWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open OnBytes (ceilLog2 noId)
open VerifiableInference.Desc (Block Chain)
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

/-- **WHAT IS ASKED ON ONE MESSAGE OF A SENDER OF THE KIND K1.** P₀, ρ₀: the plan's own plan and
ride for that sender. no: the sender's number in the chain. n: the message. ix: the number of the
book's entry among the later switch's carried stretches. dat: the closing's own data for that
message. A structure of premises' forms. Nothing here proves that it can be met. It names a run's
coins: k, and the sender's cut cs. -/
structure SharedAsks (Zp : ProofFile.Pub) (bs : List (Block S ProofFile.Cl))
    (P₀ : VerifiableInference.Desc.K1.Par) (ρ₀ : Nat → Option K1.Ride) (no n ix ch : Nat)
    (p : SwitchPlace) (k : Coins Bk) (dat : Nat → Nat → Cb.Gl.E)
    (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT) (Vd : Local W₀ Rc Xi Tr → Prop) (N : Nat)
    (w : Local W₀ Rc Xi Tr) (hd : List Fmt.Drawn) (wit : Local W₀ Rc Xi Tr → W)
    (J : K1.SendJob W X) (own₀ : X) (cs : Cs (K1.dueR J.P J.ride)) (e : Ahead)
    (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (front : Nat) : Prop where
  plan : P₀ = J.P
  ride : ρ₀ = J.ride
  cut : K1.lentCut k ch ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = some cs
  entry : ((Bk.ahead.filter fun y => y.spender == ⟨p.place, 0⟩).filter (!·.once))[ix]? = some e
  owner : e.owner = ⟨J.P.place, 0⟩
  start : e.start = K1.startR J.P J.ride n
  count : e.count = K1.dueMsg J.P.codes (shapeAt J.P n) (J.ride n)
  data : dataK n = asShared (shapeAt J.P n) dat
  msgs : OwnMsgs Q Vd N (K1.k1Num Zp bs no P₀ n) front (K1.msgTxt ch wit J own₀ n)
  pads : OwnPads Q Vd (K1.seatAtMember bs no P₀ n).1 (K1.seatAtMember bs no P₀ n).2
    (fun k _ => K1.padTxt ch J n k)
  rows : K1.rowsR J.P J.ride dataK cs n = K1.rowsLaid J own₀ cs (wit w) (hd.take front) n

/-- IT MAY HOLD EMPTILY: `SharedAsks` IS PROVED OF NO SCRIPT, BOOK OR FILLING. **The record, at a
later sender of the segment, gives the two clauses at that sender's member** (q = 0: the link's
"reads"; q = 1: its "digits"). One run's coins: never quoted for a law. -/
theorem later_tied (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (m + 1) + 2) a) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt (ProofFile.pAtK2 Zp m) a.1.2 = some fx)
    (ch : Nat) (p : SwitchPlace) (k : Coins Bk)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hc : handed ch p k = some c)
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[m]? = some Sg) {prev : Option Left}
    {prevKept : List OnBytes.OracleShape} {own : Nat → Nat → Nat → Cb.Gl.E} {b₀ : Nat}
    {R : GroupRows}
    (hR : segmentGroupRows freshTable Sg prev prevKept own (Stretch.carried p.carries c.2.2) b₀
      true = .ok R) {q : Nat} (hq2 : q < 2)
    (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT) (Vd : Local W₀ Rc Xi Tr → Prop) (N : Nat)
    (w : Local W₀ Rc Xi Tr) (hv : Vd w) (hdL ds : List Fmt.Drawn) (hN : N ≤ (hdL ++ ds).length)
    {wit : Local W₀ Rc Xi Tr → W} {J : K1.SendJob W X} {own₀ : X}
    {cs : Cs (K1.dueR J.P J.ride)} {e : Ahead}
    {dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)} {front : Nat}
    (A : SharedAsks Zp cF.blocksInOrder (parL Zp Bs.G₀ m (q == 1)) (K1.rideOf none) (noL m (q == 1)) 0
      (b₀ + ((Sg.sent.headD #[]).size - 1) + 1 + q) ch p k
      (own ((Sg.sent.headD #[]).size - 1 -
        (if prev.isSome then 1 + Sg.sizes.kept.length else 0) + q))
      Q Vd N w (hdL ++ ds) wit J own₀ cs e dataK front) :
    MemberTied fx R (wordsFirst (P5J.At.arr Zp) fx.st a.1.2.book (Q.wit k w (hdL ++ ds)))
      ((Sg.sent.headD #[]).size - 1 + q) :=
  (link_member_clause_later h O h23 a hr hfx ch p k c hc hS hR hq2 wit J own₀ A.plan A.ride A.cut e
    rfl A.entry A.owner A.start A.count dataK A.data Q Vd N front A.msgs A.pads w hv hdL ds hN
    A.rows).2

/-- IT MAY HOLD EMPTILY: `SharedAsks` IS PROVED OF NO SCRIPT, BOOK OR FILLING. **The record, at a
message of the opening in front of the fold's mask, gives the two clauses at that member of the
first segment's group.** One run's coins: never quoted for a law. -/
theorem first_tied (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (0 + 1) + 2) a) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt (ProofFile.pAtK2 Zp 0) a.1.2 = some fx)
    (ch : Nat) (p : SwitchPlace) (k : Coins Bk)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hc : handed ch p k = some c)
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[0]? = some Sg) {prev : Option Left}
    {prevKept : List OnBytes.OracleShape} {own : Nat → Nat → Nat → Cb.Gl.E} {b₀ : Nat}
    {R : GroupRows}
    (hR : segmentGroupRows freshTable Sg prev prevKept own (Stretch.carried p.carries c.2.2) b₀
      true = .ok R) {n : Nat} (hn : n < (Sg.sent.headD #[]).size - 1)
    (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT) (Vd : Local W₀ Rc Xi Tr → Prop) (N : Nat)
    (w : Local W₀ Rc Xi Tr) (hv : Vd w) (hdL ds : List Fmt.Drawn) (hN : N ≤ (hdL ++ ds).length)
    {wit : Local W₀ Rc Xi Tr → W} {J : K1.SendJob W X} {own₀ : X}
    {cs : Cs (K1.dueR J.P J.ride)} {e : Ahead}
    {dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)} {front : Nat}
    (A : SharedAsks Zp cF.blocksInOrder (firstPar Bs.G₀.first (gpOf Zp))
      (K1.rideOf (K1.firstFold Bs.G₀.first)) 2 n (b₀ + n) ch p k (dataAtOf Sg prev own n)
      Q Vd N w (hdL ++ ds) wit J own₀ cs e dataK front) :
    MemberTied fx R (wordsFirst (P5J.At.arr Zp) fx.st a.1.2.book (Q.wit k w (hdL ++ ds))) n :=
  (link_member_clause_first h O a hr hfx ch p k c hc hS hR hn wit J own₀ A.plan A.ride A.cut e
    rfl A.entry A.owner A.start A.count dataK A.data Q Vd N front A.msgs A.pads w hv hdL ds hN
    A.rows).2

/-- IT MAY HOLD EMPTILY: hmS, hpS AND HL ARE PROVED OF NO SCRIPT, BOOK OR FILLING; it stands under
the head's premise and "reached" too. One run's coins: never quoted for a law.

**THE LOCK's TWO CLAUSES ON THE MEMBERS, WHOLE, AT A LINK PLACE WHOSE CLOSED GROUP A SWITCH OPENED**
(1 ≤ m < 23). p₀: the switch that sent the closed group's first sending. p: the later switch. -/
theorem link_members_limbs (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
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
        Q Vd N w (hdL ++ ds) wit J own₀ cs e dataK front)
    {R : GroupRows}
    (hR : segmentGroupRows freshTable Sg (y'.1.map (·.1)) ((y'.1.map (·.2)).getD [])
      (lotOwn (segmentsOf Zp Bs.G₀) p (D w.x) (readers w) hdL (0 + m))
      (Stretch.carried p.carries c.2.2) y'.2 true = .ok R) :
    ∀ i, i < fx.f.rows.layout.members.size →
      MemberTied fx R (wordsFirst (P5J.At.arr Zp) fx.st a.1.2.book (Q.wit k w (hdL ++ ds))) i := by
  subst e₀
  have hq := (link_door h h23 a hr).1
  have hsz := link_members_size h O h23 a hr hq hfx hS
  obtain ⟨⟨Sg', -, hS', -, -, eS, -⟩, -⟩ := switchTies_at_head h.toAtMg O hp₀ hp (by omega)
  obtain rfl : Sg' = Sg := Option.some.inj (hS'.symm.trans hS)
  intro i hi
  rw [hsz] at hi
  by_cases h0 : i < (Sg'.sent.headD #[]).size - 1
  · rw [eS] at h0
    obtain ⟨j, hj, -⟩ := first_shapes_at_head h.toAtMg O hp₀ (by omega) h0
    obtain ⟨Sg'', hS'', hC⟩ := link_member_clause h O hm1 h23 a hr hfx hp₀ hp rfl e₁ h0 hj Q Vd N ch
      fx₀ D readers lay (hmS i j h0 hj) (hpS i j h0 hj) k w hv hdL ds hN hfx₀ c₀ h₀ c hc hs hf hgl
      hD hV hy'
    obtain rfl : Sg'' = Sg' := Option.some.inj (hS''.symm.trans hS)
    exact (hC R hR).2
  · obtain ⟨wit, J, own₀, cs, e, dataK, front, A⟩ := HL (i - ((Sg'.sent.headD #[]).size - 1))
      (by omega)
    have t := later_tied h O h23 a hr hfx ch p k c hc hS hR (by omega) Q Vd N w hv hdL ds hN A
    have e' : (Sg'.sent.headD #[]).size - 1 + (i - ((Sg'.sent.headD #[]).size - 1)) = i := by
      omega
    rw [e'] at t
    exact t

/-- IT MAY HOLD EMPTILY: HF AND HL ARE PROVED OF NO SCRIPT, BOOK OR FILLING; it stands under the
head's premise and "reached" too. One run's coins: never quoted for a law.

**THE LOCK's TWO CLAUSES ON THE MEMBERS, WHOLE, AT THE SWITCH INTO THE GROUP 1**, whose closed group
is the first segment's (m = 0): every sender is of the kind K1. p: that switch. -/
theorem first_members_limbs (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (0 + 1) + 2) a) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt (ProofFile.pAtK2 Zp 0) a.1.2 = some fx)
    (ch : Nat) (p : SwitchPlace) (k : Coins Bk)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hc : handed ch p k = some c)
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[0]? = some Sg) {prev : Option Left}
    {prevKept : List OnBytes.OracleShape} {own : Nat → Nat → Nat → Cb.Gl.E} {b₀ : Nat}
    {R : GroupRows}
    (hR : segmentGroupRows freshTable Sg prev prevKept own (Stretch.carried p.carries c.2.2) b₀
      true = .ok R)
    (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT) (Vd : Local W₀ Rc Xi Tr → Prop) (N : Nat)
    (w : Local W₀ Rc Xi Tr) (hv : Vd w) (hdL ds : List Fmt.Drawn) (hN : N ≤ (hdL ++ ds).length)
    -- THE OPENING's MESSAGES IN FRONT OF THE FOLD's MASK
    (HF : ∀ n, n < (Sg.sent.headD #[]).size - 1 → ∃ (wit : Local W₀ Rc Xi Tr → W)
      (J : K1.SendJob W X) (own₀ : X) (cs : Cs (K1.dueR J.P J.ride)) (e : Ahead)
      (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (front : Nat),
      SharedAsks Zp cF.blocksInOrder (firstPar Bs.G₀.first (gpOf Zp))
        (K1.rideOf (K1.firstFold Bs.G₀.first)) 2 n (b₀ + n) ch p k (dataAtOf Sg prev own n)
        Q Vd N w (hdL ++ ds) wit J own₀ cs e dataK front)
    -- THE TWO LATER SENDERS
    (HL : ∀ q, q < 2 → ∃ (wit : Local W₀ Rc Xi Tr → W) (J : K1.SendJob W X) (own₀ : X)
      (cs : Cs (K1.dueR J.P J.ride)) (e : Ahead)
      (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (front : Nat),
      SharedAsks Zp cF.blocksInOrder (parL Zp Bs.G₀ 0 (q == 1)) (K1.rideOf none) (noL 0 (q == 1)) 0
        (b₀ + ((Sg.sent.headD #[]).size - 1) + 1 + q) ch p k
        (own ((Sg.sent.headD #[]).size - 1 -
          (if prev.isSome then 1 + Sg.sizes.kept.length else 0) + q))
        Q Vd N w (hdL ++ ds) wit J own₀ cs e dataK front) :
    ∀ i, i < fx.f.rows.layout.members.size →
      MemberTied fx R (wordsFirst (P5J.At.arr Zp) fx.st a.1.2.book (Q.wit k w (hdL ++ ds))) i := by
  have h23 : 0 < 23 := by omega
  have hq := (link_door h h23 a hr).1
  have hsz := link_members_size h O h23 a hr hq hfx hS
  intro i hi
  rw [hsz] at hi
  by_cases h0 : i < (Sg.sent.headD #[]).size - 1
  · obtain ⟨wit, J, own₀, cs, e, dataK, front, A⟩ := HF i h0
    exact first_tied h O a hr hfx ch p k c hc hS hR h0 Q Vd N w hv hdL ds hN A
  · obtain ⟨wit, J, own₀, cs, e, dataK, front, A⟩ := HL (i - ((Sg.sent.headD #[]).size - 1))
      (by omega)
    have t := later_tied h O h23 a hr hfx ch p k c hc hS hR (by omega) Q Vd N w hv hdL ds hN A
    have e' : (Sg.sent.headD #[]).size - 1 + (i - ((Sg.sent.headD #[]).size - 1)) = i := by
      omega
    rw [e'] at t
    exact t

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.SharedAsks
#print axioms ProofFile.Honest.K2.Law.later_tied
#print axioms ProofFile.Honest.K2.Law.first_tied
#print axioms ProofFile.Honest.K2.Law.link_members_limbs
#print axioms ProofFile.Honest.K2.Law.first_members_limbs
