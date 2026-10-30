-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/MemberClause.lean: the kind "the code switch" (K2): THE LOCK's
TWO CLAUSES ON THE CLOSED GROUP's MEMBERS, AT A RUN's COINS, AT THE MEMBERS THAT A SWITCH SENT: at
the 22 link places whose closed group a switch opened (1 ≤ m < 23), at each message n of that
switch's sending in front of its last. The sister of `link_fresh_clause` (FreshClause.lean of this
folder), which has the third clause, on the fold's fresh mask. Statements with their proofs: joins;
no definition. IT MAY HOLD EMPTILY: see the docstrings.

WHICH SLOT IT IS FOR. The kind's exchange under the head (`k2_exchange_of_values`,
MadeValuesLeft.lean of this folder, of other authors) leaves, at each switch, a field claim;
`claim_at_yes` (ClaimAtYes.lean) has that field from the premise `LockAsks` (ClaimOfLock.lean); this
file pays the second and third limb of `LockAsks` at some of the members. The exchange is one of the
four debts that the frame's `OwesS` (Honest/Thread/PaysS.lean) asks at every number of the first
chain; `OwesS` at that chain is a premise from which a value of `ThreadsC`
(Honest/Law/ThreadStratC.lean) is built, and acceptance at a request goes through that structure.

  `lock_rows_of_key_off`   rows against words at one message of a switch's sending, UNDER THE
                    SCRIPT's TIE OFF THE PAD (`switchMsgOff`, Honest/K2/MsgOff.lean): the sister of
                    `lock_rows_of_key` (LockRows.lean of this folder), which asks the whole text
  `link_member_at_front`   THE VERIFIER's SIDE, AT ANY MEMBER: under the head, at the front that the
                    switch's block takes off a reached state: where the link's written list has i as
                    its n-th member: n is below the number of the carried layout's members; the
                    layout's n-th member is the library's number `noK10` of i; the statement's
                    shape there is the written one
  `link_member_clause`   where `segmentGroupRows`, at the later switch's carried stretches, returns R:
                    `R.rows[n]? = some (V n)`, V the rows that the sender p₀ laid; and each entry of
                    that message's main and mask rows is the word that `wordsFirst` reads off the
                    Script's witness at the layout's n-th member

Its second and third end are the two limbs of `LockAsks` at i := n, sign for sign, the bound on i
aside (`link_member_at_front` has it), at table := `freshTable`, own := `lotOwn …`, heard := hdL, k
:= `Stretch.carried p.carries c.2.2`, w := `wordsFirst (At.arr Zp) fx.st a.1.2.book (Q.wit k w (hdL
++ ds))`. `LockAsks` speaks at the written `segsW`, this statement at `segmentsOf Zp Bs.G₀`: under
the head the two are one (`segments_at_head`, PlacesWritten.lean): that call is the spender's.

By, of this folder: `key_of_lots` (KeyOfLots.lean) · `tab_rows_off` (TabRowsOff.lean, of other
authors) · `first_shapes_at_head`, `place_codes_at_front` (FirstShapes.lean) · `member_shape_getD`
(ShapesAtFront.lean) · `noWord_open` (SampledOpen.lean) · `gamma_below_at_head` (GammaBelow.lean) ·
under Johnson/Desc/K2/Honest/Returns/: `link_door` (DoorReached.lean), `link_member_stated`
(SeatReached.lean), `link_membersNumbered_front` (MembersNumbered.lean), `link_word_front`
(WordAtFront.lean), `link_frontTies` (FrontTiesReached.lean) · the library's `front_pin_link`,
`reach_raw`.

What stays a premise. hm, hpd: the Script's two hypotheses, at the sender's message n: hm OFF THE
PAD's PLACES: the form of the field msgs of the kind's record (`K2SeatedL`, Honest/K2/SeatedL.lean):
the whole text's tie could not be met at a kept copy, whose pad's places hold a coin of its own
while its number in the witness is its sender's · BOTH ARE ASKED AT THE PLAN's SEAT OF THE MEMBER i
(`seatK10`): the record's ties stand at the sender's own seat (`K1.seatAtMember` at the switch's
number): `seat_at_head` (SeatIsK10.lean of this folder, of other authors) brings `seatK10` at i to
the seat that `switchSeatIn` returns for message n; THE REST OF THAT SEAM IS THE SPENDER's · fx₀, a
letter, with hgl · hs, hf: two tests on the book · hD: on the filling · five returns (h₀, hc, hV,
hy', and `segmentGroupRows`') · `Vd w` · hfx: that a front is there.

Limits. One run's coins. No run is given at which the head's premise and "reached" hold together.
THE MEMBERS THAT THE OPENING SWITCH SENT, ALONE: nothing on the members that later sendings of the
segment sent (senders of the kind K1), nor on the first segment (m = 0), nor at the places 339 and
353. It speaks at every place of the member's main rows, the pads' places too, and at its mask rows:
entries that hold coins: an equation between two texts' values: what is WRITTEN where. It speaks of
a text, not of a move. No thread and no filling is named. The full size and the format's second
hash function alone. NOT IN FRONT OF A LAW OVER COINS. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.KeyOfLots
import Johnson.Desc.ProofFile.Honest.K2.Law.TabRowsOff
import Johnson.Desc.Means.Says
import Johnson.Desc.ProofFile.Honest.K2.Law.ShapesAtFront
import Johnson.Desc.ProofFile.Honest.K2.Law.GammaBelow
import Johnson.Desc.ProofFile.Honest.K2.Law.SampledOpen
import Johnson.Desc.K2.Honest.Returns.MembersNumbered
import Johnson.Desc.K2.Honest.Returns.WordAtFront
import Johnson.Desc.K2.Honest.Returns.DoorReached
import Johnson.Desc.K2.Honest.Returns.FrontTiesReached

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open OnBytes (ceilLog2 noId)
open OnBytes.Means (Words)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (noK10 seatK10)
open VerifiableInference.Desc.LinkJoin (loAt)
open VerifiableInference.Desc.K2.Honest (Left)
open VerifiableInference.Desc.K2.Honest.Returns (link_door link_member_stated
  link_membersNumbered_front link_word_front link_frontTies)
open VerifiableInference.Desc.K13.Honest (roundsAhead)
open VerifiableInference.Desc.Sound (allOf EAll MsgT wordsFirst)
open Johnson.Desc.First.Walk.Tied (reach_raw)
open ProofFile.Honest.FirstThread (Script OwnMsgs OwnPads)
open OnBytes.Maker (WholeD)
open P5J (AtMgA F0T)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {Z : VerifierAndGoals.PublicFiles} {D₀ : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {W₀ Rc Xi Tr Cells Tok : Type} {Bk : ProverCoinCounts}

/-- hm, hp AND hW ARE PREMISES. **The later closing's row and the witness's words agree, entry by
entry, UNDER THE SCRIPT's TIE OFF THE PAD.** `lock_rows_of_key` (LockRows.lean of this folder) with
its one call turned: `tab_rows_off` for `tab_rows_switch`: hm is asked at `switchMsgOff`, which a
kept copy's message can meet too. One run's coins: never quoted for a law. -/
theorem lock_rows_of_key_off (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT)
    (Vd : Local W₀ Rc Xi Tr → Prop) (N ch : Nat) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (closing : Closing) (p₀ : SwitchPlace)
    (fx₀ n num j t : Nat)
    (hm : OwnMsgs Q Vd N num fx₀ (switchMsgOff ch D readers closing p₀ n))
    (hp : OwnPads Q Vd j t (fun k _ => switchPadTxt ch p₀ n k))
    (hw : NoWord (switchSent p₀.sizes p₀.others)) (hn : n < (switchSent p₀.sizes p₀.others).size)
    (k : Coins Bk) {c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries}
    (hH : handed ch p₀ k = some c₀) (w : Local W₀ Rc Xi Tr) (hv : Vd w) (hd : List Fmt.Drawn)
    (hN : N ≤ hd.length) {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers closing p₀ c₀ w (hd.take fx₀) = .ok V)
    {r : Johnson.Prover.Send.Rows} (hK : r = V n)
    {codes : OnBytes.Codes} {sh : OnBytes.OracleShape} (t1 : codes = p₀.sizes.codes)
    (t2 : sh = ((switchSent p₀.sizes p₀.others).getD n default).shape)
    (wd : Words GE) (o : Nat)
    (hW : ∀ part b i, b < sh.rows part →
      wd o part (b + i * 2 ^ ceilLog2 (sh.rows part)) =
        (Q.wit k w hd).tab codes sh num j t (part == .mask) b i) :
    (∀ b i, b < sh.mainRows →
      r.main (sh.mainDeg == 3) b i = wd o .main (b + i * 2 ^ ceilLog2 sh.mainRows)) ∧
    (∀ b i, b < sh.maskRows → r.mask b i = wd o .mask (b + i * 2 ^ ceilLog2 sh.maskRows)) := by
  subst hK t1 t2
  have e := tab_rows_off Q Vd N ch D readers closing p₀ fx₀ n num j t hm hp hw hn k hH w hv hd
    hN hV
  refine ⟨fun b i hb => ?_, fun b i hb => ?_⟩
  · exact ((hW .main b i hb).trans (congrFun (congrFun (congrFun e false) b) i)).symm
  · exact ((hW .mask b i hb).trans (congrFun (congrFun (congrFun e true) b) i)).symm

/-- No run is given at which the head's premise and "reached" hold together. **THE VERIFIER's SIDE,
AT ANY MEMBER OF THE CLOSED GROUP**, at a segment's first place (m < 23). On public data and the
verifier's state alone. -/
theorem link_member_at_front (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x) {m : Nat} (h23 : m < 23)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (m + 1) + 2) a) {q : VerifiableInference.Desc.First.K2.P2}
    (hq : q.stands = .link) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt q a.1.2 = some fx)
    {n : Nat} {i : Fin (loAt m).length}
    (hi : (VerifiableInference.Desc.First.Close.membersOf (loAt m))[n]? = some i) :
    n < fx.f.rows.layout.members.size ∧
      fx.f.rows.layout.members.getD n noId =
        noK10 (P5J.At.seats Zp) (loAt m) (P5J.At.pseats Zp) m i ∧
      (fx.st.oracles.getD (fx.f.rows.layout.members.getD n noId) default).shape =
        ((loAt m).get i).1 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨hu, hst⟩ := link_member_stated h h23 a hr
  obtain ⟨-, R', C', f⟩ := (reach_raw (h.toAtMg.rch_is_reach _ a hr)).fold
  obtain ⟨-, a2, -⟩ := Meaning.K2.front_pin_link h.scope h.reads O (l := m + 1) (by omega)
    (by omega) f hq hfx
  have e := link_membersNumbered_front h h23 a hr hq hfx
  have e1 : fx.f.rows.layout.members.toList[n]? =
      some (noK10 (P5J.At.seats Zp) (loAt m) (P5J.At.pseats Zp) m i) := by
    rw [e, List.getElem?_map, hi]
    rfl
  have e2 : fx.f.rows.layout.members.getD n noId =
      noK10 (P5J.At.seats Zp) (loAt m) (P5J.At.pseats Zp) m i := by
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, e1]
    rfl
  refine ⟨?_, e2, ?_⟩
  · have := (List.getElem?_eq_some_iff.1 e1).1
    simpa using this
  · rw [e2]
    exact member_shape_getD h (by omega) a hr hu (by omega) i (hst i (List.mem_of_getElem? hi)) a2

/-- IT MAY HOLD EMPTILY: hm AND hpd ARE PROVED OF NO SCRIPT; it stands under the head's premise and
"reached" too: no run is given at which these hold together. One run's coins: never quoted for a
law.

**THE LOCK's TWO CLAUSES ON THE MEMBERS, AT A MESSAGE THAT THE OPENING SWITCH SENT, AT A RUN's
COINS**, at a link place whose closed group a switch opened (1 ≤ m < 23). p₀: the switch that sent
the closed group's first sending. p: the later switch. n: a message of p₀'s sending in front of its
last. i: the n-th member of the link's written list. hdL: what the later switch has heard in front
of its part; ds: any continuation. -/
theorem link_member_clause (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (hm1 : 1 ≤ m) (h23 : m < 23)
    -- THE VERIFIER's SIDE: a state reached in front of the later switch, and the item's own front
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (m + 1) + 2) a) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt (ProofFile.pAtK2 Zp m) a.1.2 = some fx)
    -- THE TWO PLACES, THE MESSAGE AND THE MEMBER
    {p₀ p : SwitchPlace} (hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀) (hp : p ∈ switchPlaces Zp Bs.G₀)
    (e₀ : p₀.link = m) (e₁ : p.link = m + 1)
    {n : Nat} (hn : n < (switchSent p₀.sizes p₀.others).size - 1)
    {i : Fin (loAt m).length}
    (hi : (VerifiableInference.Desc.First.Close.membersOf (loAt m))[n]? = some i)
    -- THE SCRIPT's TWO HYPOTHESES, BY NAME, AT THE SENDER's MESSAGE n, AT THE PLAN's SEAT OF i
    (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT) (Vd : Local W₀ Rc Xi Tr → Prop)
    (N ch fx₀ : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout)
    (hm : OwnMsgs Q Vd N (P5J.At.arr Zp (seatK10 (loAt m) (P5J.At.pseats Zp) m i).1
        (seatK10 (loAt m) (P5J.At.pseats Zp) m i).2) fx₀
      (switchMsgOff ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀ n))
    (hpd : OwnPads Q Vd (seatK10 (loAt m) (P5J.At.pseats Zp) m i).1
      (seatK10 (loAt m) (P5J.At.pseats Zp) m i).2 (fun k _ => switchPadTxt ch p₀ n k))
    -- ONE RUN: its coins, its input, what the later switch has heard, any continuation
    (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hv : Vd w) (hdL ds : List Fmt.Drawn)
    (hN : N ≤ (hdL ++ ds).length) (hfx₀ : fx₀ ≤ hdL.length)
    -- RETURNS AND THE BOOK's TWO TESTS
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
      (Stretch.carried p.carries c.2.2) ((segmentsOf Zp Bs.G₀).take m) 0 0 none = .ok y') :
    ∃ Sg, (segmentsOf Zp Bs.G₀)[m]? = some Sg ∧ ∀ R : GroupRows,
      segmentGroupRows freshTable Sg (y'.1.map (·.1)) ((y'.1.map (·.2)).getD [])
        (lotOwn (segmentsOf Zp Bs.G₀) p (D w.x) (readers w) hdL (0 + m))
        (Stretch.carried p.carries c.2.2) y'.2 true = .ok R →
      R.rows[n]? = some (V n) ∧
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
  subst e₀
  have hlen : (hdL.take fx₀).length = fx₀ := by
    rw [List.length_take]
    exact Nat.min_eq_left hfx₀
  have hq := (link_door h h23 a hr).1
  obtain ⟨Sg, hSg, hK⟩ := key_of_lots h.toAtMg O ch D readers lay hp₀ hp (by omega) k c₀ h₀ c hc hs
    hf w (hd₀ := hdL.take fx₀) (hd := hdL) (List.take_prefix _ _)
    (fun Sg hSg g hg => by
      rw [hlen]
      exact Nat.lt_of_lt_of_le (gamma_below_at_head h.toAtMg O (m := p₀.link - 1) (by omega) Sg
        (by rwa [show p₀.link - 1 + 1 = p₀.link by omega]) g hg) hgl)
    (fun s i ad h1 h2 => by
      rw [hlen]
      exact hD s i ad h1 h2) hV hy'
  refine ⟨Sg, hSg, fun R hR => ?_⟩
  have eR := (hK R hR).1 n hn
  obtain ⟨-, g2, g3⟩ := link_member_at_front h h23 a hr hq hfx hi
  obtain ⟨i', hi', es⟩ := first_shapes_at_head h.toAtMg O hp₀ (by omega) hn
  obtain rfl : i' = i := Option.some.inj (hi'.symm.trans hi)
  have t1 : fx.st.codes = p₀.sizes.codes :=
    (place_codes_at_front h.toAtMg O hp₀ hp (by omega)
      (link_frontTies h.scope h.reads O h23 (h.toAtMg.rch_is_reach _ a hr) hq hfx)).symm
  have eG : R.rows.getD n zeroMessage = V n := by
    rw [List.getD_eq_getElem?_getD, eR]
    rfl
  have L := lock_rows_of_key_off Q Vd N ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀ fx₀
    n _ _ _ hm hpd (noWord_open O p₀ hp₀) (by omega) k h₀
    w hv (hdL ++ ds) hN (by rw [List.take_append_of_le_length hfx₀]; exact hV) eG t1
    (g3.trans es)
    (wordsFirst (P5J.At.arr Zp) fx.st a.1.2.book (Q.wit k w (hdL ++ ds)))
    (fx.f.rows.layout.members.getD n noId)
    (fun part b j hb => by
      rw [g3] at hb ⊢
      rw [g2]
      exact link_word_front h h23 a hr hq hfx i' (List.mem_of_getElem? hi') _ _ part hb j)
  exact ⟨eR, L.1, L.2⟩

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.lock_rows_of_key_off
#print axioms ProofFile.Honest.K2.Law.link_member_at_front
#print axioms ProofFile.Honest.K2.Law.link_member_clause
