-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/FreshClauseFirst.lean: the kind "the code switch" (K2): THE
ASSEMBLY UNDER THE HEAD: THE LOCK's CLAUSE ON THE FOLD's FRESH MASK AT THE FIRST SEGMENT (m = 0):
THE 25th PLACE. At the other 24 the fresh mask's sender is a switch (Honest/K2/Law/FreshClause.lean,
FreshClauseArms.lean). The first segment's is sent by the opening, a place of the kind K1: so the
key, the hinge and the public ties are K1's. One statement with its proof; no definition. IT MAY
HOLD EMPTILY: see the docstring.

  `first_fresh_clause` under the head's premise, at a state reached at the border 14 * (0 + 1) + 2 =
                    16, the item's own front fx: where the first segment's rows, laid anew of the
                    first switch's carried coins, are R: R's fresh mask is a message of the
                    opening's rows at the sender's own cut of the same run's coins, and entry by
                    entry it is the word that the verifier's reader reads off the Script's witness
                    at the front's fresh mask

The sender is a letter: a job J of the kind K1 with the opening's numbers and ride (hJP, hJr): at
part 5's `lotJobs` (Honest/K1/LotJobs.lean) the first job has both: `lotJobs_first_ties`
(Honest/K2/Law/FirstJobTies.lean); no filling is named. THE MIDDLE TERM IS THE OPENING's ROWS AT THE
ZERO DATA (`asShared … zeroG`), AT THE SENDER's OWN CUT OF THE COINS: NOT at the sender's own data
`J.data`: R's fresh mask is not shown to be the sender's rows at the sender's data. The clause's
entries are the field `mask`'s, which reads the ride and the coins alone, no data (`K1.rowsR`,
Honest/K1/Coins.lean): so there the two are one.

By: THE KEY: `copyShared_mask_at_head` (Honest/K2/Law/CopySharedAtHead.lean) · THE HINGE:
`K1.tab_rows` (Honest/K1/ScriptTie.lean) · THE WORD: `link_freshWord_front` at m = 0
(Johnson/Desc/K2/Honest/Returns/FreshNumbered.lean) · THE PUBLIC TIES: the codes: `mask_tie_at_head`
(Honest/K2/Law/K1SendersTies.lean) with `segmentsOf_at_front` (SegmentsAtFront.lean) · the shape:
`mask0_shape_getD` (FirstMaskShape.lean) with `mask_tie_at_head`. The seat and the number are
written as the front's law has them, (maskTree 0, maskPart 0): that they are K1's own seat and
number for that message is `mask_seat_at_head` (K1SendersSeats.lean), not called here.

What stays a premise. hm, hpd: the Script's two hypotheses, by name, at K1's texts · ho, hc: the
sender's cut and the switch's hand of one run's coins · he, t1, t2, t3: the book's entry for that
message among what the switch carries · hR: the rows' return · hJP, hJr · hfx, hv, hN.

Limits. It speaks of a text, not of a move. The later switch p is a letter: that it is the plan's
first is not asked. Nothing on the lock's two clauses on the members. The full size and the format's
second hash function alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CopySharedAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.FirstMaskShape
import Johnson.Desc.ProofFile.Honest.K1.ScriptTie
import Johnson.Desc.K2.Honest.Returns.FreshNumbered
import Johnson.Desc.K2.Honest.Returns.DoorReached
import Johnson.Desc.K2.Honest.Returns.FrontTiesReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open OnBytes (ceilLog2)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K2.Honest (Left zeroG)
open VerifiableInference.Desc.K2.Honest.Returns (link_door link_member_stated link_closedBehind
  fresh_of_closedBehind link_freshWord_front link_frontTies)
open VerifiableInference.Desc.K1 (firstPar gpOf)
open VerifiableInference.Desc.Sound (allOf EAll MsgT wordsFirst)
open Johnson.Desc.First.Walk.Tied (reach_raw)
open Johnson.Prover.Send (shapeAt)
open ProofFile.Honest.FirstThread (Script OwnMsgs OwnPads)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T TS)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {W₀ Rc Xi Tr Cells Tok : Type} {Bk : ProverCoinCounts}

/-- IT MAY HOLD EMPTILY: hm AND hp ARE PROVED OF NO SCRIPT. AND MORE EMPTILY THAN THE CORE: it
stands under the head's premise and "reached" too: no run is given at which these hold together.
One run's coins: never quoted for a law. "hp" is this statement's hpd. **THE LOCK's CLAUSE ON THE
FOLD's FRESH MASK, AT A RUN's COINS, AT THE FIRST SEGMENT.** THE BORDER IS 16: the links' formula
14 * (m + 1) + 2 at m = 0, written out: the border of `link_door` at m = 0, which the proof calls
at it. The first conjunct's middle term is the opening's rows at the zero data, not at the
sender's own: the clause speaks of the field mask alone. -/
theorem first_fresh_clause (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    -- THE VERIFIER's SIDE: a state reached in front of the first switch, and the item's own front
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (0 + 1) + 2) a) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt (ProofFile.pAtK2 Zp 0) a.1.2 = some fx)
    -- THE SWITCH THAT CARRIES, A LETTER; THE FIRST SEGMENT
    (p : SwitchPlace) {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[0]? = some Sg)
    -- THE SENDER: A JOB OF THE KIND K1, A LETTER, WITH THE OPENING's NUMBERS AND RIDE
    {Wj Xj : Type} (wit : Local W₀ Rc Xi Tr → Wj) (J : K1.SendJob Wj Xj) (own₀ : Xj)
    (hJP : firstPar Bs.G₀.first (gpOf Zp) = J.P)
    (hJr : K1.rideOf (K1.firstFold Bs.G₀.first) = J.ride)
    -- THE SCRIPT's TWO HYPOTHESES, BY NAME, AT K1's TEXTS, AT THE SEGMENT's LAST MESSAGE
    (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT) (Vd : Local W₀ Rc Xi Tr → Prop)
    (N ch front : Nat)
    (hm : OwnMsgs Q Vd N (P5J.At.arr Zp (VerifiableInference.Desc.First.Close.maskTree 0)
        (VerifiableInference.Desc.First.Close.maskPart 0)) front
      (K1.msgTxt ch wit J own₀ ((Sg.sent.headD #[]).size - 1)))
    (hpd : OwnPads Q Vd (VerifiableInference.Desc.First.Close.maskTree 0)
      (VerifiableInference.Desc.First.Close.maskPart 0)
      (fun k _ => K1.padTxt ch J ((Sg.sent.headD #[]).size - 1) k))
    -- ONE RUN: ITS COINS, AN INPUT, WHAT WAS HEARD
    (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hv : Vd w) (hd : List Fmt.Drawn) (hN : N ≤ hd.length)
    {cs : Cs (K1.dueR J.P J.ride)}
    (ho : K1.lentCut k ch ⟨J.P.place, 0⟩ (K1.dueR J.P J.ride) = some cs)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hc : handed ch p k = some c)
    -- THE BOOK's ENTRY FOR THAT MESSAGE AMONG WHAT THE SWITCH CARRIES
    {b₀ : Nat} (e : Ahead)
    (he : ((Bk.ahead.filter fun y => y.spender == ⟨p.place, 0⟩).filter (!·.once))[
      b₀ + ((Sg.sent.headD #[]).size - 1)]? = some e)
    (t1 : e.owner = ⟨J.P.place, 0⟩)
    (t2 : e.start = K1.startR J.P J.ride ((Sg.sent.headD #[]).size - 1))
    (t3 : e.count = K1.dueMsg J.P.codes (shapeAt J.P ((Sg.sent.headD #[]).size - 1))
      (J.ride ((Sg.sent.headD #[]).size - 1)))
    -- THE SEGMENT's ROWS, LAID ANEW OF THE CARRIED COINS
    {prev : Option Left} {prevKept : List OnBytes.OracleShape} {own : Nat → Nat → Nat → Cb.Gl.E}
    {R : GroupRows}
    (hR : segmentGroupRows freshTable Sg prev prevKept own (Stretch.carried p.carries c.2.2) b₀
      true = .ok R) :
    R.fresh = some (K1.rowsR J.P J.ride
        (fun _ => asShared (shapeAt J.P ((Sg.sent.headD #[]).size - 1)) fun _ _ => zeroG) cs
        ((Sg.sent.headD #[]).size - 1)) ∧
      ∀ b j, b < 2 ^ fx.f.rows.layout.h →
        (R.fresh.getD zeroMessage).mask b j =
          wordsFirst (P5J.At.arr Zp) fx.st a.1.2.book (Q.wit k w hd) fx.f.rows.fresh .mask
            (b + j * 2 ^ ceilLog2 (fx.st.oracles.getD fx.f.rows.fresh default).shape.maskRows) := by
  have h23 : 0 < 23 := by omega
  have T := mask_tie_at_head h O hS
  rw [hJP, hJr] at T
  have eF := copyShared_mask_at_head h O ch p k c hc hS hR hJP hJr ⟨J.P.place, 0⟩ ho e rfl he t1
    t2 t3 (fun _ => asShared (shapeAt J.P ((Sg.sent.headD #[]).size - 1)) fun _ _ => zeroG) rfl
  refine ⟨eF, ?_⟩
  have hq := (link_door h h23 a hr).1
  have hu := (link_member_stated h h23 a hr).1
  obtain ⟨f1, f2, -⟩ := fresh_of_closedBehind h (by omega) hr.2 a.2
    (link_closedBehind h h23 a hr hq hfx)
  obtain ⟨-, R', C', f⟩ := (reach_raw (h.toAtMg.rch_is_reach _ a hr)).fold
  obtain ⟨-, a2, -⟩ := Meaning.K2.front_pin_link h.scope h.reads O (l := 0 + 1) (by omega)
    (by omega) f hq hfx
  have s2 : (fx.st.oracles.getD fx.f.rows.fresh default).shape =
      shapeAt J.P ((Sg.sent.headD #[]).size - 1) := by
    rw [f1]
    exact (mask0_shape_getD h O a hr hu hS (by rw [← f1]; exact f2) a2).trans T.hs.symm
  have s1 : fx.st.codes = J.P.codes :=
    (T.hc.trans (segmentsOf_at_front O
      (link_frontTies h.scope h.reads O h23 (h.toAtMg.rch_is_reach _ a hr) hq hfx)
      (List.mem_of_getElem? hS)).1).symm
  have E := K1.tab_rows Q Vd N ch wit J own₀ front ((Sg.sent.headD #[]).size - 1) _ _ _ hm hpd k
    cs ho w hv hd hN
  intro b j hb
  rw [eF, Option.getD_some, link_freshWord_front h h23 a hr hq hfx _ _ hb j, s1, s2, E]
  rfl

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.first_fresh_clause
