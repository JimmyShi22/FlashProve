-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/MemberClauseK1.lean: the kind "the code switch" (K2): THE
LOCK's TWO CLAUSES ON THE CLOSED GROUP's MEMBERS, AT A RUN's COINS, AT THE MEMBERS THAT SENDERS OF
THE KIND K1 SENT: at the 23 link places (m < 23) the two that the segment's later sendings sent (the
link's "reads" and "digits"); at the first of these places (m = 0) also those that the opening sent.
The sisters of `link_member_clause` (MemberClause.lean of this folder), which stands at the members
that an opening switch sent. Two statements with their proofs: joins; no definition. THEY MAY HOLD
EMPTILY: see the docstrings.

WHICH SLOT IT IS FOR. As MemberClause.lean's: the second and third limb of `LockAsks`
(ClaimOfLock.lean), at two more of the members; through `claim_at_yes` the field claim of the kind's
exchange under the head; the exchange is one of the four debts of the frame's `OwesS` at the first
chain, from which, with other premises, a value of `ThreadsC` is built.

  `link_member_clause_later`   where `segmentGroupRows`, at the later switch's carried stretches, returns
                    R: at n := (the first sending's messages but the mask) + q, q < 2: `R.rows[n]?`
                    is the sender's row; and each entry of that message's main and mask rows is the
                    word that `wordsFirst` reads off the Script's witness at the layout's n-th
                    member
  `link_member_clause_first`   the like at m = 0, at message n of the first segment's first sending
                    in front of the fold's mask: the opening's message of the same number

By: `copyShared_later_at_head`, `copyShared_first_at_head` (CopySharedAtHead.lean) ·
`later_seats_at_head`, `first_seats_at_head` (K1SendersSeats.lean) · `later_ties_at_head`,
`first_ties_at_head` (K1SendersTies.lean), of this folder, of other authors · `lock_rows_of_shared`
(LockRowsShared.lean) · `link_member_at_front` (MemberClause.lean) · `segmentsOf_at_front`
(SegmentsAtFront.lean) · under Johnson/Desc/K2/Honest/Returns/: `link_door` (DoorReached.lean),
`link_frontTies` (FrontTiesReached.lean), `link_word_front` (WordAtFront.lean).

WHAT STAYS A PREMISE, AND WHO HAS SOMETHING TOWARD IT. (1) THE BOOK: he, t1, t2, t3: the book's
entry for the carried stretch: its owner, start and count: `copyShared_later_by_test`
(CopySharedByTest.lean of this folder, of other authors) brings the four down to one public test
(`entryRunIs`, Honest/Small/EntryRunIs.lean); that test is evaluated by Lean's kernel at the
opening's messages (AtFullSide/K2/CarriedAtTheBook.lean, OpeningRowsAtTheBook.lean, of other
authors): AT THE LATER SENDINGS' ENTRIES BY NOBODY · (2) THE DATA: hdat and hJ: that the rows which
`K1.rowsR` lays at the closing's own data are those that the sender's job lays at its own: by
`rowsR_shared` (SameRows.lean of this folder) both are one body at two data of the one message; THAT
THE BODY IS THE SAME AT THE TWO, AS WHOLE ROWS, IS TYPED BY NOBODY; two laws of other authors go
part of the way: `rowsR_mainF_data` (AtFullSide/K2/MsgsAtLinkOne.lean) compares `K1.rowsR` under two
data in its field mainF alone, at a single row and place, given that both data have the same
base-field value at that spot · `fillings_at_link_one` (AtFullSide/K2/FillingsAtLinkOne.lean)
supplies that given for one pair of fillings, for the two messages of the opening that link 1 copies
· (3) THE SCRIPT: hm, hpd: its two hypotheses at the sender's texts, at the sender's own number and
seat: at a joined Script `join_tie_k1_fit` (Honest/Thread/JoinFit.lean, of other authors)
has such ties; NOT JOINED HERE · (4) THE SENDER's CUT OF THE
RUN's COINS: ho: `lentCut_isSome` (Honest/K1/ScriptAtLaw.lean) with `hasCoins_fifty_of`,
`hasCoins_two_of` (Honest/K1/Law/HasCoinsOfRows.lean), of other authors, have it under a premise on
the book's first rows; at the opening's address `opening_covers_at_book`
(AtFullSide/K11/OpeningCoversAtTheBook.lean, of other authors) is nearer; NOT JOINED HERE. BESIDE
THESE: hP, hρ: the job's plan and ride are the link's, or the opening's · hc, hR: returns · `Vd w` ·
hfx: that a front is there.

Limits. One run's coins. No run is given at which the head's premise and "reached" hold together.
Not at the places 339 and 353. p IS ANY PLACE OF A SWITCH IN BOTH LAWS: what ties it to the segment
is the book's entry he alone. It speaks at every place of the member's main rows, the pads' places
too, and at its mask rows: entries that hold coins: an equation between two texts' values: what is
WRITTEN where. No thread and no filling is named. The full size and the format's second hash function alone.
NOT IN FRONT OF A LAW OVER COINS. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.MemberClause
import Johnson.Desc.ProofFile.Honest.K2.Law.LockRowsShared
import Johnson.Desc.ProofFile.Honest.K2.Law.CopySharedAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.K1SendersSeats
import Johnson.Desc.ProofFile.Honest.K2.Law.SegmentsAtFront

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open OnBytes (ceilLog2 noId)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (parL noL firstPar gpOf)
open VerifiableInference.Desc.K2.Honest (Left)
open VerifiableInference.Desc.K2.Honest.Returns (link_door link_word_front link_frontTies)
open VerifiableInference.Desc.Sound (allOf EAll MsgT wordsFirst)
open Johnson.Prover.Send (shapeAt)
open ProofFile.Honest.FirstThread (Script OwnMsgs OwnPads)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {Wl W X Cells Tok : Type} {Bk : ProverCoinCounts}

/-- IT MAY HOLD EMPTILY: hm, hpd, ho, he, hdat AND hJ ARE PROVED OF NO SCRIPT, BOOK OR FILLING; it
stands under the head's premise and "reached" too. One run's coins: never quoted for a law.

**THE LOCK's TWO CLAUSES ON THE MEMBERS, AT A MESSAGE OF A LATER SENDING OF THE SEGMENT, AT A RUN's
COINS** (m < 23). p: the later switch. q: 0: the link's "reads"; 1: its "digits". J: the sender's
job. hdL: what the later switch has heard in front of its part; ds: any continuation. -/
theorem link_member_clause_later (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (h23 : m < 23)
    -- THE VERIFIER's SIDE: a state reached in front of the later switch, and the item's own front
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (m + 1) + 2) a) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt (ProofFile.pAtK2 Zp m) a.1.2 = some fx)
    -- THE LATER SWITCH, ITS COINS, THE SEGMENT AND ITS ROWS
    (ch : Nat) (p : SwitchPlace) (k : Coins Bk)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hc : handed ch p k = some c)
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[m]? = some Sg) {prev : Option Left}
    {prevKept : List OnBytes.OracleShape} {own : Nat → Nat → Nat → Cb.Gl.E} {b₀ : Nat}
    {withFresh : Bool} {R : GroupRows}
    (hR : segmentGroupRows freshTable Sg prev prevKept own (Stretch.carried p.carries c.2.2) b₀
      withFresh = .ok R) {q : Nat} (hq2 : q < 2)
    -- THE SENDER: ITS JOB, ITS CUT OF THE RUN's COINS, THE BOOK's ENTRY, THE DATA
    (wit : Wl → W) (J : K1.SendJob W X) (own₀ : X) (hP : parL Zp Bs.G₀ m (q == 1) = J.P)
    (hρ : K1.rideOf none = J.ride) {cs : Cs (K1.dueR J.P J.ride)}
    (ho : K1.lentCut k ch ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = some cs) (e : Ahead) {i₀ : Nat}
    (hi₀ : i₀ = b₀ + ((Sg.sent.headD #[]).size - 1) + (if withFresh then 1 else 0) + q)
    (he : ((Bk.ahead.filter fun y => y.spender == ⟨p.place, 0⟩).filter (!·.once))[i₀]? = some e)
    (t1 : e.owner = ⟨J.P.place, 0⟩) (t2 : e.start = K1.startR J.P J.ride 0)
    (t3 : e.count = K1.dueMsg J.P.codes (shapeAt J.P 0) (J.ride 0))
    (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E))
    (hdat : dataK 0 = asShared (shapeAt J.P 0) (own ((Sg.sent.headD #[]).size - 1 -
      (if prev.isSome then 1 + Sg.sizes.kept.length else 0) + q)))
    -- THE SCRIPT's TWO HYPOTHESES, AT THE SENDER's TEXTS, AT ITS OWN NUMBER AND SEAT
    (Q : Script Bk Wl Cells Tok MsgT) (Vd : Wl → Prop) (N front : Nat)
    (hm : OwnMsgs Q Vd N (K1.k1Num Zp cF.blocksInOrder (noL m (q == 1)) (parL Zp Bs.G₀ m (q == 1)) 0) front
      (K1.msgTxt ch wit J own₀ 0))
    (hpd : OwnPads Q Vd (K1.seatAtMember cF.blocksInOrder (noL m (q == 1)) (parL Zp Bs.G₀ m (q == 1)) 0).1
      (K1.seatAtMember cF.blocksInOrder (noL m (q == 1)) (parL Zp Bs.G₀ m (q == 1)) 0).2
      (fun k _ => K1.padTxt ch J 0 k))
    -- ONE RUN
    (w : Wl) (hv : Vd w) (hdL ds : List Fmt.Drawn) (hN : N ≤ (hdL ++ ds).length)
    (hJ : K1.rowsR J.P J.ride dataK cs 0 =
      K1.rowsLaid J own₀ cs (wit w) ((hdL ++ ds).take front) 0) :
    R.rows[(Sg.sent.headD #[]).size - 1 + q]? = some (K1.rowsR J.P J.ride dataK cs 0) ∧
      (∀ b j,
        b < (fx.st.oracles.getD (fx.f.rows.layout.members.getD ((Sg.sent.headD #[]).size - 1 + q)
          noId) default).shape.mainRows →
        (R.rows.getD ((Sg.sent.headD #[]).size - 1 + q) zeroMessage).main
            ((fx.st.oracles.getD (fx.f.rows.layout.members.getD ((Sg.sent.headD #[]).size - 1 + q)
              noId) default).shape.mainDeg == 3) b j =
          wordsFirst (P5J.At.arr Zp) fx.st a.1.2.book (Q.wit k w (hdL ++ ds))
            (fx.f.rows.layout.members.getD ((Sg.sent.headD #[]).size - 1 + q) noId) .main
            (b + j * 2 ^ ceilLog2 (fx.st.oracles.getD
              (fx.f.rows.layout.members.getD ((Sg.sent.headD #[]).size - 1 + q) noId)
                default).shape.mainRows)) ∧
      ∀ b j,
        b < (fx.st.oracles.getD (fx.f.rows.layout.members.getD ((Sg.sent.headD #[]).size - 1 + q)
          noId) default).shape.maskRows →
        (R.rows.getD ((Sg.sent.headD #[]).size - 1 + q) zeroMessage).mask b j =
          wordsFirst (P5J.At.arr Zp) fx.st a.1.2.book (Q.wit k w (hdL ++ ds))
            (fx.f.rows.layout.members.getD ((Sg.sent.headD #[]).size - 1 + q) noId) .mask
            (b + j * 2 ^ ceilLog2 (fx.st.oracles.getD
              (fx.f.rows.layout.members.getD ((Sg.sent.headD #[]).size - 1 + q) noId)
                default).shape.maskRows) := by
  have hq := (link_door h h23 a hr).1
  obtain ⟨i, hi, es, eseat, enum⟩ := later_seats_at_head h O hS hq2
  have hlt : q < ((Sg.sent.drop 1).flatMap (·.toList)).length := by
    rw [(later_ties_at_head h O hS).1]
    exact hq2
  have eR := copyShared_later_at_head h O ch p k c hc hS hR (List.getElem?_eq_getElem hlt) hP hρ
    ⟨J.P.place, 0⟩ ho e hi₀ he t1 t2 t3 dataK hdat
  obtain ⟨-, g2, g3⟩ := link_member_at_front h h23 a hr hq hfx hi
  have hcodes : fx.st.codes = J.P.codes := by
    rw [← hP, ((later_ties_at_head h O hS).2 q _ (List.getElem?_eq_getElem hlt)).hc]
    exact (segmentsOf_at_front O (link_frontTies h.scope h.reads O h23
      (h.toAtMg.rch_is_reach _ a hr) hq hfx) (List.mem_of_getElem? hS)).1.symm
  have eG : R.rows.getD ((Sg.sent.headD #[]).size - 1 + q) zeroMessage =
      K1.rowsR J.P J.ride dataK cs 0 := by
    rw [List.getD_eq_getElem?_getD, eR]
    rfl
  have L := lock_rows_of_shared Q Vd N ch wit J own₀ front 0 _ _ _ hm hpd k ho w hv (hdL ++ ds) hN
    (eG.trans hJ) hcodes (g3.trans (es.trans (by rw [hP])))
    (wordsFirst (P5J.At.arr Zp) fx.st a.1.2.book (Q.wit k w (hdL ++ ds)))
    (fx.f.rows.layout.members.getD ((Sg.sent.headD #[]).size - 1 + q) noId)
    (fun part b j hb => by
      rw [g3] at hb ⊢
      rw [g2, ← enum, ← eseat]
      exact link_word_front h h23 a hr hq hfx i (List.mem_of_getElem? hi) _ _ part hb j)
  exact ⟨eR, L.1, L.2⟩

/-- IT MAY HOLD EMPTILY: hm, hpd, ho, he, hdat AND hJ ARE PROVED OF NO SCRIPT, BOOK OR FILLING; it
stands under the head's premise and "reached" too. One run's coins: never quoted for a law.

**THE LOCK's TWO CLAUSES ON THE MEMBERS, AT A MESSAGE OF THE OPENING's SENDING, AT A RUN's COINS**:
at the switch into the group 1, whose closed group is the first segment's. p: that switch. n: a
message of the first segment's first sending in front of the fold's mask. J: the opening's job. -/
theorem link_member_clause_first (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    -- THE VERIFIER's SIDE: a state reached in front of the switch, and the item's own front
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (0 + 1) + 2) a) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt (ProofFile.pAtK2 Zp 0) a.1.2 = some fx)
    -- THE SWITCH, ITS COINS, THE SEGMENT AND ITS ROWS
    (ch : Nat) (p : SwitchPlace) (k : Coins Bk)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hc : handed ch p k = some c)
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[0]? = some Sg) {prev : Option Left}
    {prevKept : List OnBytes.OracleShape} {own : Nat → Nat → Nat → Cb.Gl.E} {b₀ : Nat}
    {withFresh : Bool} {R : GroupRows}
    (hR : segmentGroupRows freshTable Sg prev prevKept own (Stretch.carried p.carries c.2.2) b₀
      withFresh = .ok R) {n : Nat} (hn : n < (Sg.sent.headD #[]).size - 1)
    -- THE SENDER: ITS JOB, ITS CUT OF THE RUN's COINS, THE BOOK's ENTRY, THE DATA
    (wit : Wl → W) (J : K1.SendJob W X) (own₀ : X) (hP : firstPar Bs.G₀.first (gpOf Zp) = J.P)
    (hρ : K1.rideOf (K1.firstFold Bs.G₀.first) = J.ride) {cs : Cs (K1.dueR J.P J.ride)}
    (ho : K1.lentCut k ch ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = some cs) (e : Ahead) {i₀ : Nat}
    (hi₀ : i₀ = b₀ + n)
    (he : ((Bk.ahead.filter fun y => y.spender == ⟨p.place, 0⟩).filter (!·.once))[i₀]? = some e)
    (t1 : e.owner = ⟨J.P.place, 0⟩) (t2 : e.start = K1.startR J.P J.ride n)
    (t3 : e.count = K1.dueMsg J.P.codes (shapeAt J.P n) (J.ride n))
    (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E))
    (hdat : dataK n = asShared (shapeAt J.P n) (dataAtOf Sg prev own n))
    -- THE SCRIPT's TWO HYPOTHESES, AT THE SENDER's TEXTS, AT ITS OWN NUMBER AND SEAT
    (Q : Script Bk Wl Cells Tok MsgT) (Vd : Wl → Prop) (N front : Nat)
    (hm : OwnMsgs Q Vd N (K1.k1Num Zp cF.blocksInOrder 2 (firstPar Bs.G₀.first (gpOf Zp)) n) front
      (K1.msgTxt ch wit J own₀ n))
    (hpd : OwnPads Q Vd (K1.seatAtMember cF.blocksInOrder 2 (firstPar Bs.G₀.first (gpOf Zp)) n).1
      (K1.seatAtMember cF.blocksInOrder 2 (firstPar Bs.G₀.first (gpOf Zp)) n).2
      (fun k _ => K1.padTxt ch J n k))
    -- ONE RUN
    (w : Wl) (hv : Vd w) (hdL ds : List Fmt.Drawn) (hN : N ≤ (hdL ++ ds).length)
    (hJ : K1.rowsR J.P J.ride dataK cs n =
      K1.rowsLaid J own₀ cs (wit w) ((hdL ++ ds).take front) n) :
    R.rows[n]? = some (K1.rowsR J.P J.ride dataK cs n) ∧
      (∀ b j,
        b < (fx.st.oracles.getD (fx.f.rows.layout.members.getD n noId) default).shape.mainRows →
        (R.rows.getD n zeroMessage).main
            ((fx.st.oracles.getD (fx.f.rows.layout.members.getD n noId) default).shape.mainDeg
              == 3) b j =
          wordsFirst (P5J.At.arr Zp) fx.st a.1.2.book (Q.wit k w (hdL ++ ds))
            (fx.f.rows.layout.members.getD n noId) .main (b + j * 2 ^ ceilLog2
              (fx.st.oracles.getD (fx.f.rows.layout.members.getD n noId)
                default).shape.mainRows)) ∧
      ∀ b j,
        b < (fx.st.oracles.getD (fx.f.rows.layout.members.getD n noId) default).shape.maskRows →
        (R.rows.getD n zeroMessage).mask b j =
          wordsFirst (P5J.At.arr Zp) fx.st a.1.2.book (Q.wit k w (hdL ++ ds))
            (fx.f.rows.layout.members.getD n noId) .mask (b + j * 2 ^ ceilLog2
              (fx.st.oracles.getD (fx.f.rows.layout.members.getD n noId)
                default).shape.maskRows) := by
  have h23 : 0 < 23 := by omega
  have hq := (link_door h h23 a hr).1
  obtain ⟨i, hi, es, eseat, enum⟩ := first_seats_at_head h O hS hn
  have eR := copyShared_first_at_head h O ch p k c hc hS hR hn hP hρ ⟨J.P.place, 0⟩ ho e hi₀ he t1
    t2 t3 dataK hdat
  obtain ⟨-, g2, g3⟩ := link_member_at_front h h23 a hr hq hfx hi
  have hcodes : fx.st.codes = J.P.codes := by
    rw [← hP, (first_ties_at_head h O hS hn).hc]
    exact (segmentsOf_at_front O (link_frontTies h.scope h.reads O h23
      (h.toAtMg.rch_is_reach _ a hr) hq hfx) (List.mem_of_getElem? hS)).1.symm
  have eG : R.rows.getD n zeroMessage = K1.rowsR J.P J.ride dataK cs n := by
    rw [List.getD_eq_getElem?_getD, eR]
    rfl
  have L := lock_rows_of_shared Q Vd N ch wit J own₀ front n _ _ _ hm hpd k ho w hv (hdL ++ ds) hN
    (eG.trans hJ) hcodes (g3.trans (es.trans (by rw [hP])))
    (wordsFirst (P5J.At.arr Zp) fx.st a.1.2.book (Q.wit k w (hdL ++ ds)))
    (fx.f.rows.layout.members.getD n noId)
    (fun part b j hb => by
      rw [g3] at hb ⊢
      rw [g2, ← enum, ← eseat]
      exact link_word_front h h23 a hr hq hfx i (List.mem_of_getElem? hi) _ _ part hb j)
  exact ⟨eR, L.1, L.2⟩

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.link_member_clause_later
#print axioms ProofFile.Honest.K2.Law.link_member_clause_first
