-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/LockAsksAtArms.lean: the kind "the code switch" (K2):
`LockAsks` (ClaimOfLock.lean of this folder), WHOLE, AT A RUN's COINS, AT THE KIND's TWO ARMS: the
output head's front (339, whose closed group is segment 23's) and the front behind the last segment
(353, segment 24's). With `link_lockAsks` and `first_lockAsks` (LockAsksAtLink.lean) that is all 25
switches. One structure: premises' forms; statements with their proofs: joins. THEY MAY HOLD
EMPTILY: see the docstrings.

WHICH SLOT IT IS FOR. As LockAsksAtLink.lean's: `LockAsks` is the premise hA of `claim_at_yes`
(ClaimAtYes.lean), and so the field claim of the kind's exchange under the head, at each switch.

HOW. The laws at the links spend of their front four things alone: the numbers of its members, their
shapes, the words at them, and the public ties. `FrontFacts` names these four; the same proofs are
typed here once more at a letter m and a front with these facts.

  `FrontFacts`      THE FOUR THINGS, at a link number m, a book and a front
  `head_frontFacts`, `fin_frontFacts`   they hold at the two arms' fronts, under the head, at a
                    reached state: at 353 the front and the book are those behind the quiet step
  `member_at_facts`, `members_size_facts`, `member_tied_facts`, `later_tied_facts`
                    `link_member_at_front`, `link_members_size`, `link_member_clause`, `later_tied`
                    at such a front. AT A LINK's FRONT THEY SAY WHAT THOSE SAY: they are typed for
                    the arms
  `lockAsks_of_facts`   `LockAsks` from these, with the first limb and the fourth as premises
  `head_lockAsks`, `fin_lockAsks`   THE ENDS

By: `head_`, `fin_membersNumbered_front` · `head_`, `fin_member_stated` · `head_`, `fin_word_front`
· `head_`, `fin_frontTies` · `head_`, `fin_door` (Johnson/Desc/K2/Honest/Returns/) · `head_`,
`fin_gamma_heard` (GammaAtFront.lean of this folder) · `head_`, `fin_fresh_clause`
(FreshClauseArms.lean) · and what LockAsksAtLink.lean and the files beneath it name.

WHAT STAYS A PREMISE: as in LockAsksAtLink.lean: the Script's two hypotheses at every message of the
closed group (at the switch's messages in front of the last off the pad, at the plan's seat of the
member; at its last the whole text, at the mask's seat) · at each of the two later senders the
record `SharedAsks`: its cut of the run's coins, the book's entry, the data, the Script's two ·
returns · two tests on the book · f₀, hhd: the run's rounds.

Limits. One run's coins. No run is given at which the head's premise and "reached" hold together,
nor one at which all premises hold. UNDER "THERE IS" IN HL STANDS, AMONG PUBLIC THINGS, cs: A CUT OF
THE RUN's COINS: the record's field cut pins it to k. `SharedAsks` IS SHOWN OF NO SCRIPT, BOOK OR
FILLING. It speaks at every place of each member's main rows, the pads' places too, and at mask
rows: entries that hold coins: equations between two texts' values: what is WRITTEN where. The full
size and the format's second hash function alone. NOT IN FRONT OF A LAW OVER COINS. Nothing
on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.LockAsksAtLink
import Johnson.Desc.ProofFile.Honest.K2.Law.FreshClauseArms

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open OnBytes (ceilLog2 noId)
open VerifiableInference.Desc (Block Chain Wit foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.Close (noK10 seatK10)
open VerifiableInference.Desc.LinkJoin (loAt)
open VerifiableInference.Desc.K1 (parL noL)
open VerifiableInference.Desc.K2.Honest (Left)
open VerifiableInference.Desc.K2.Honest.Returns (FrontTies head_membersNumbered_front
  fin_membersNumbered_front head_member_stated fin_member_stated head_word_front fin_word_front
  head_frontTies fin_frontTies head_door fin_door)
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
  {W₀ Rc Xi Tr W X Cells Tok : Type} {Bk : ProverCoinCounts}

/-- **WHAT THE LAWS ON A CLOSED GROUP's MEMBERS SPEND OF THE FRONT.** m: the closed group's link. A
structure of premises' forms: public data and the verifier's state; no coin. -/
structure FrontFacts (Zp : ProofFile.Pub) (m : Nat) (book : OnBytes.TreeBook)
    (fx : _root_.Tw.K2.Front) : Prop where
  numbered : fx.f.rows.layout.members.toList =
    (VerifiableInference.Desc.First.Close.membersOf (loAt m)).map
      (noK10 (P5J.At.seats Zp) (loAt m) (P5J.At.pseats Zp) m)
  shape : ∀ i ∈ VerifiableInference.Desc.First.Close.membersOf (loAt m),
    (fx.st.oracles.getD (noK10 (P5J.At.seats Zp) (loAt m) (P5J.At.pseats Zp) m i) default).shape =
      ((loAt m).get i).1
  word : ∀ i ∈ VerifiableInference.Desc.First.Close.membersOf (loAt m),
    ∀ {Cells Tok : Type} (arr : Nat → Nat → Nat) (v : Wit Cells Tok MsgT) (part : OnBytes.Part)
      {b : Nat}, b < ((loAt m).get i).1.rows part → ∀ j : Nat,
      wordsFirst arr fx.st book v (noK10 (P5J.At.seats Zp) (loAt m) (P5J.At.pseats Zp) m i)
          part (b + j * 2 ^ ceilLog2 (((loAt m).get i).1.rows part)) =
        v.tab fx.st.codes ((loAt m).get i).1
          (arr (seatK10 (loAt m) (P5J.At.pseats Zp) m i).1
            (seatK10 (loAt m) (P5J.At.pseats Zp) m i).2)
          (seatK10 (loAt m) (P5J.At.pseats Zp) m i).1 (seatK10 (loAt m) (P5J.At.pseats Zp) m i).2
          (part == .mask) b j
  ties : FrontTies Zp fx

/-- No run is given at which the head's premise and "reached" hold together. **At the output head's
front** (339): segment 23's group. -/
theorem head_frontFacts (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 339 a) {q : VerifiableInference.Desc.First.K2.P2}
    (hq : q.stands = .head) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt q a.1.2 = some fx) :
    FrontFacts Zp 23 a.1.2.book fx := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨hu, hst⟩ := head_member_stated h a hr
  obtain ⟨-, R', C', f⟩ := (reach_raw (h.toAtMg.rch_is_reach _ a hr)).fold
  obtain ⟨-, a2, -⟩ := Meaning.K2.front_pin_head h.scope h.reads O f hq hfx
  refine ⟨head_membersNumbered_front h a hr hq hfx,
    fun i hi => member_shape_getD h (by omega) a hr hu (by omega) i (hst i hi) a2, ?_,
    head_frontTies h.scope h.reads O (h.toAtMg.rch_is_reach _ a hr) hq hfx⟩
  intro i hi Cells' Tok' arr v part b hb j
  exact head_word_front h a hr hq hfx i hi arr v part hb j

/-- No run is given at which the head's premise and "reached" hold together. **At the front behind
the last segment** (353, behind its quiet step in front, t): segment 24's group; the book is t's. -/
theorem fin_frontFacts (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 353 a) {t : S}
    (he : VerifiableInference.Desc.First.K2.finishFrontQ a.1.2 = .ok t)
    {q : VerifiableInference.Desc.First.K2.P2} (hq : q.stands = .finish)
    {fx : _root_.Tw.K2.Front} (hfx : VerifiableInference.Desc.First.K2.frontAt q t = some fx) :
    FrontFacts Zp 24 t.book fx := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨hu, hst⟩ := fin_member_stated h a hr
  obtain ⟨-, R', C', f⟩ := (reach_raw (h.toAtMg.rch_is_reach _ a hr)).fold
  obtain ⟨-, -, -, a4, -⟩ := Meaning.K2.front_nums_fin h.scope h.reads O f he hq hfx
  refine ⟨fin_membersNumbered_front h a hr he hq hfx,
    fun i hi => member_shape_getD h (by omega) a hr hu (by omega) i (hst i hi) a4, ?_,
    fin_frontTies h.scope h.reads O (h.toAtMg.rch_is_reach _ a hr) he hq hfx⟩
  intro i hi Cells' Tok' arr v part b hb j
  exact fin_word_front h a hr he hq hfx i hi arr v part hb j

/-- **AT ANY MEMBER**: `link_member_at_front` at a front with the four facts. -/
theorem member_at_facts {m : Nat} {book : OnBytes.TreeBook} {fx : _root_.Tw.K2.Front}
    (F : FrontFacts Zp m book fx) {n : Nat} {i : Fin (loAt m).length}
    (hi : (VerifiableInference.Desc.First.Close.membersOf (loAt m))[n]? = some i) :
    n < fx.f.rows.layout.members.size ∧
      fx.f.rows.layout.members.getD n noId =
        noK10 (P5J.At.seats Zp) (loAt m) (P5J.At.pseats Zp) m i ∧
      (fx.st.oracles.getD (fx.f.rows.layout.members.getD n noId) default).shape =
        ((loAt m).get i).1 := by
  have e1 : fx.f.rows.layout.members.toList[n]? =
      some (noK10 (P5J.At.seats Zp) (loAt m) (P5J.At.pseats Zp) m i) := by
    rw [F.numbered, List.getElem?_map, hi]
    rfl
  have e2 : fx.f.rows.layout.members.getD n noId =
      noK10 (P5J.At.seats Zp) (loAt m) (P5J.At.pseats Zp) m i := by
    rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, e1]
    rfl
  refine ⟨?_, e2, ?_⟩
  · have := (List.getElem?_eq_some_iff.1 e1).1
    simpa using this
  · rw [e2]
    exact F.shape i (List.mem_of_getElem? hi)

/-- **THE NUMBER OF THE CARRIED LAYOUT's MEMBERS**: `link_members_size` at such a front. -/
theorem members_size_facts (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} {book : OnBytes.TreeBook} {fx : _root_.Tw.K2.Front} (F : FrontFacts Zp m book fx)
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[m]? = some Sg) :
    fx.f.rows.layout.members.size = (Sg.sent.headD #[]).size - 1 + 2 := by
  rw [segments_at_head h.toAtMg O] at hS
  have e1 : fx.f.rows.layout.members.size =
      (VerifiableInference.Desc.First.Close.membersOf (loAt m)).length := by
    rw [← Array.length_toList, F.numbered, List.length_map]
  have hz : (Sg, m) ∈ segsW.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    exact hS
  have t := List.all_eq_true.1 membersCountW (Sg, m) hz
  rw [e1]
  exact beq_iff_eq.1 t

/-- IT MAY HOLD EMPTILY: hm AND hpd ARE PROVED OF NO SCRIPT. One run's coins: never quoted for a
law. **`link_member_clause` at such a front**, its end `MemberTied`. -/
theorem member_tied_facts (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (hm1 : 1 ≤ m) (h25 : m < 25) {book : OnBytes.TreeBook} {fx : _root_.Tw.K2.Front}
    (F : FrontFacts Zp m book fx)
    {p₀ p : SwitchPlace} (hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀) (hp : p ∈ switchPlaces Zp Bs.G₀)
    (e₀ : p₀.link = m) (e₁ : p.link = m + 1)
    {n : Nat} (hn : n < (switchSent p₀.sizes p₀.others).size - 1)
    {i : Fin (loAt m).length}
    (hi : (VerifiableInference.Desc.First.Close.membersOf (loAt m))[n]? = some i)
    (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT) (Vd : Local W₀ Rc Xi Tr → Prop)
    (N ch fx₀ : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout)
    (hm : OwnMsgs Q Vd N (P5J.At.arr Zp (seatK10 (loAt m) (P5J.At.pseats Zp) m i).1
        (seatK10 (loAt m) (P5J.At.pseats Zp) m i).2) fx₀
      (switchMsgOff ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀ n))
    (hpd : OwnPads Q Vd (seatK10 (loAt m) (P5J.At.pseats Zp) m i).1
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
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[m]? = some Sg) {R : GroupRows}
    (hR : segmentGroupRows freshTable Sg (y'.1.map (·.1)) ((y'.1.map (·.2)).getD [])
      (lotOwn (segmentsOf Zp Bs.G₀) p (D w.x) (readers w) hdL (0 + m))
      (Stretch.carried p.carries c.2.2) y'.2 true = .ok R) :
    MemberTied fx R (wordsFirst (P5J.At.arr Zp) fx.st book (Q.wit k w (hdL ++ ds))) n := by
  subst e₀
  have hlen : (hdL.take fx₀).length = fx₀ := by
    rw [List.length_take]
    exact Nat.min_eq_left hfx₀
  obtain ⟨Sg', hSg', hK⟩ := key_of_lots h.toAtMg O ch D readers lay hp₀ hp (by omega) k c₀ h₀ c hc
    hs hf w (hd₀ := hdL.take fx₀) (hd := hdL) (List.take_prefix _ _)
    (fun Sg hSg g hg => by
      rw [hlen]
      exact Nat.lt_of_lt_of_le (gamma_below_at_head h.toAtMg O (m := p₀.link - 1) (by omega) Sg
        (by rwa [show p₀.link - 1 + 1 = p₀.link by omega]) g hg) hgl)
    (fun s i ad h1 h2 => by
      rw [hlen]
      exact hD s i ad h1 h2) hV hy'
  obtain rfl : Sg' = Sg := Option.some.inj (hSg'.symm.trans hS)
  have eR := (hK R hR).1 n hn
  obtain ⟨-, g2, g3⟩ := member_at_facts F hi
  obtain ⟨i', hi', es⟩ := first_shapes_at_head h.toAtMg O hp₀ (by omega) hn
  obtain rfl : i' = i := Option.some.inj (hi'.symm.trans hi)
  have t1 : fx.st.codes = p₀.sizes.codes :=
    (place_codes_at_front h.toAtMg O hp₀ hp (by omega) F.ties).symm
  have eG : R.rows.getD n zeroMessage = V n := by
    rw [List.getD_eq_getElem?_getD, eR]
    rfl
  exact lock_rows_of_key_off Q Vd N ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀ fx₀
    n _ _ _ hm hpd (noWord_open O p₀ hp₀) (by omega) k h₀
    w hv (hdL ++ ds) hN (by rw [List.take_append_of_le_length hfx₀]; exact hV) eG t1
    (g3.trans es)
    (wordsFirst (P5J.At.arr Zp) fx.st book (Q.wit k w (hdL ++ ds)))
    (fx.f.rows.layout.members.getD n noId)
    (fun part b j hb => by
      rw [g3] at hb ⊢
      rw [g2]
      exact F.word i' (List.mem_of_getElem? hi') _ _ part hb j)

/-- IT MAY HOLD EMPTILY: `SharedAsks` IS PROVED OF NO SCRIPT, BOOK OR FILLING. One run's coins:
never quoted for a law. **`later_tied` at such a front.** -/
theorem later_tied_facts (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} {book : OnBytes.TreeBook} {fx : _root_.Tw.K2.Front} (F : FrontFacts Zp m book fx)
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
    MemberTied fx R (wordsFirst (P5J.At.arr Zp) fx.st book (Q.wit k w (hdL ++ ds)))
      ((Sg.sent.headD #[]).size - 1 + q) := by
  obtain ⟨i, hi, es, eseat, enum⟩ := later_seats_at_head h O hS hq2
  have hlt : q < ((Sg.sent.drop 1).flatMap (·.toList)).length := by
    rw [(later_ties_at_head h O hS).1]
    exact hq2
  have eR := copyShared_later_at_head h O ch p k c hc hS hR (List.getElem?_eq_getElem hlt) A.plan
    A.ride ⟨J.P.place, 0⟩ A.cut e rfl A.entry A.owner A.start A.count dataK A.data
  obtain ⟨-, g2, g3⟩ := member_at_facts F hi
  have hcodes : fx.st.codes = J.P.codes := by
    rw [← A.plan, ((later_ties_at_head h O hS).2 q _ (List.getElem?_eq_getElem hlt)).hc]
    exact (segmentsOf_at_front O F.ties (List.mem_of_getElem? hS)).1.symm
  have eG : R.rows.getD ((Sg.sent.headD #[]).size - 1 + q) zeroMessage =
      K1.rowsR J.P J.ride dataK cs 0 := by
    rw [List.getD_eq_getElem?_getD, eR]
    rfl
  exact lock_rows_of_shared Q Vd N ch wit J own₀ front 0 _ _ _ A.msgs A.pads k A.cut w hv
    (hdL ++ ds) hN (eG.trans A.rows) hcodes (g3.trans (es.trans (by rw [A.plan])))
    (wordsFirst (P5J.At.arr Zp) fx.st book (Q.wit k w (hdL ++ ds)))
    (fx.f.rows.layout.members.getD ((Sg.sent.headD #[]).size - 1 + q) noId)
    (fun part b j hb => by
      rw [g3] at hb ⊢
      rw [g2, ← enum, ← eseat]
      exact F.word i (List.mem_of_getElem? hi) _ _ part hb j)

/-- IT MAY HOLD EMPTILY: hmS, hpS AND HL ARE PROVED OF NO SCRIPT, BOOK OR FILLING. One run's coins:
never quoted for a law. UNDER "THERE IS" IN HL STANDS cs, A CUT OF THE RUN's COINS, pinned to k by
the record's field cut.

**`LockAsks`, WHOLE, AT A FRONT WITH THE FOUR FACTS**, whose closed group a switch opened, from the
first limb hγ and the fourth hF4. -/
theorem lockAsks_of_facts (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (hm1 : 1 ≤ m) (h25 : m < 25) {book : OnBytes.TreeBook} {fx : _root_.Tw.K2.Front}
    (F : FrontFacts Zp m book fx)
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
        Q Vd N w (hdL ++ ds) wit J own₀ cs e dataK front)
    (hγ : challengesOr0 hdL Sg.gamma = fx.f.rows.gamma.map OnBytes.Slice.readE)
    (hF4 : ∀ R : GroupRows,
      segmentGroupRows freshTable Sg (y'.1.map (·.1)) ((y'.1.map (·.2)).getD [])
        (lotOwn (segmentsOf Zp Bs.G₀) p (D w.x) (readers w) hdL (0 + m))
        (Stretch.carried p.carries c.2.2) y'.2 true = .ok R →
      ∀ b j, b < 2 ^ fx.f.rows.layout.h →
        (R.fresh.getD zeroMessage).mask b j =
          wordsFirst (P5J.At.arr Zp) fx.st book (Q.wit k w (hdL ++ ds)) fx.f.rows.fresh .mask
            (b + j * 2 ^ ceilLog2 (fx.st.oracles.getD fx.f.rows.fresh default).shape.maskRows)) :
    LockAsks freshTable (lotOwn segsW p (D w.x) (readers w) hdL) hdL
      (Stretch.carried p.carries c.2.2) m fx
      (wordsFirst (P5J.At.arr Zp) fx.st book (Q.wit k w (hdL ++ ds))) := by
  subst e₀
  have hsz := members_size_facts h O F hS
  unfold LockAsks
  rw [← segments_at_head h.toAtMg O]
  intro Sg₁ y₁ hS₁ hy₁
  obtain rfl : Sg₁ = Sg := Option.some.inj (hS₁.symm.trans hS)
  obtain rfl : y₁ = y' := Except.ok.inj (hy₁.symm.trans hy')
  refine ⟨hγ, fun R hR => ?_⟩
  have all : ∀ i, i < fx.f.rows.layout.members.size →
      MemberTied fx R (wordsFirst (P5J.At.arr Zp) fx.st book (Q.wit k w (hdL ++ ds))) i := by
    obtain ⟨⟨Sg', -, hS', -, -, eS, -⟩, -⟩ := switchTies_at_head h.toAtMg O hp₀ hp (by omega)
    obtain rfl : Sg' = Sg₁ := Option.some.inj (hS'.symm.trans hS)
    intro i hi
    rw [hsz] at hi
    by_cases h0 : i < (Sg'.sent.headD #[]).size - 1
    · rw [eS] at h0
      obtain ⟨j, hj, -⟩ := first_shapes_at_head h.toAtMg O hp₀ (by omega) h0
      exact member_tied_facts h O hm1 h25 F hp₀ hp rfl e₁ h0 hj Q Vd N ch fx₀ D readers lay
        (hmS i j h0 hj) (hpS i j h0 hj) k w hv hdL ds hN hfx₀ c₀ h₀ c hc hs hf hgl hD hV hy' hS hR
    · obtain ⟨wit, J, own₀, cs, e, dataK, front, A⟩ := HL (i - ((Sg'.sent.headD #[]).size - 1))
        (by omega)
      have t := later_tied_facts h O F ch p k c hc hS hR (by omega) Q Vd N w hv hdL ds hN A
      have e' : (Sg'.sent.headD #[]).size - 1 + (i - ((Sg'.sent.headD #[]).size - 1)) = i := by
        omega
      rw [e'] at t
      exact t
  exact ⟨fun i b j hi hb => (all i hi).1 b j hb, fun i b j hi hb => (all i hi).2 b j hb,
    hF4 R hR⟩

/-- IT MAY HOLD EMPTILY: hmS, hpS, hmF, hpF AND HL ARE PROVED OF NO SCRIPT, BOOK OR FILLING; it
stands under the head's premise and "reached" too. One run's coins: never quoted for a law. UNDER
"THERE IS" IN HL STANDS cs, A CUT OF THE RUN's COINS, pinned to k by the record's field cut.

**`LockAsks`, WHOLE, AT THE OUTPUT HEAD's FRONT** (339). p₀: the switch that opened group 23. p: the
head's switch. -/
theorem head_lockAsks (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 339 a) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt (ProofFile.pAtK2 Zp 23) a.1.2 = some fx)
    {p₀ p : SwitchPlace} (hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀) (hp : p ∈ switchPlaces Zp Bs.G₀)
    (e₀ : p₀.link = 23) (e₁ : p.link = 24)
    (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT) (Vd : Local W₀ Rc Xi Tr → Prop)
    (N ch fx₀ : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout)
    -- THE SCRIPT's TWO HYPOTHESES AT EACH MESSAGE OF THE OPENING SWITCH IN FRONT OF ITS LAST
    (hmS : ∀ n (i : Fin (loAt 23).length), n < (switchSent p₀.sizes p₀.others).size - 1 →
      (VerifiableInference.Desc.First.Close.membersOf (loAt 23))[n]? = some i →
      OwnMsgs Q Vd N (P5J.At.arr Zp (seatK10 (loAt 23) (P5J.At.pseats Zp) 23 i).1
          (seatK10 (loAt 23) (P5J.At.pseats Zp) 23 i).2) fx₀
        (switchMsgOff ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀ n))
    (hpS : ∀ n (i : Fin (loAt 23).length), n < (switchSent p₀.sizes p₀.others).size - 1 →
      (VerifiableInference.Desc.First.Close.membersOf (loAt 23))[n]? = some i →
      OwnPads Q Vd (seatK10 (loAt 23) (P5J.At.pseats Zp) 23 i).1
        (seatK10 (loAt 23) (P5J.At.pseats Zp) 23 i).2 (fun k _ => switchPadTxt ch p₀ n k))
    -- AND AT ITS LAST, THE FOLD's FRESH MASK
    (hmF : OwnMsgs Q Vd N (P5J.At.arr Zp (VerifiableInference.Desc.First.Close.maskTree 23)
        (VerifiableInference.Desc.First.Close.maskPart 23)) fx₀
      (switchMsgTxt ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀
        ((switchSent p₀.sizes p₀.others).size - 1)))
    (hpF : OwnPads Q Vd (VerifiableInference.Desc.First.Close.maskTree 23)
      (VerifiableInference.Desc.First.Close.maskPart 23)
      (fun k _ => switchPadTxt ch p₀ ((switchSent p₀.sizes p₀.others).size - 1) k))
    (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hv : Vd w) (hdL ds : List Fmt.Drawn)
    (hN : N ≤ (hdL ++ ds).length) (hfx₀ : fx₀ ≤ hdL.length)
    (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries) (h₀ : handed ch p₀ k = some c₀)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hc : handed ch p k = some c)
    (hs : carriedSame Bk p₀ p = true) (hf : carriedFits Bk (switchPlaces Zp Bs.G₀) p = true)
    (hgl : roundsAhead cF.blocksInOrder (VerifiableInference.Desc.First.K2Caller.noAt 22) ≤ fx₀)
    (hD : ∀ s i ad, s < p₀.link → p.addrs s i = some ad → (D w.x).heardAt ad ≤ fx₀)
    {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀ c₀ w
      (hdL.take fx₀) = .ok V)
    -- THE RUN's ROUNDS
    {zz : ProofFile.InstPub} {Rr R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn}
    (f₀ : foldBlocks 0 (cF.blocksInOrder.take 339) (ProofFile.startS Zp zz) Rr C =
      .ok (a.1.2, R₀, C₀)) (hhd : hdL = Rr.map (·.drawn))
    -- TWO LOOK-UPS
    {y' : Option (Left × List OnBytes.OracleShape) × Nat}
    (hy' : closingFrom freshTable (lotOwn (segmentsOf Zp Bs.G₀) p (D w.x) (readers w) hdL) hdL
      (Stretch.carried p.carries c.2.2) ((segmentsOf Zp Bs.G₀).take 23) 0 0 none = .ok y')
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[23]? = some Sg)
    -- THE TWO LATER SENDERS
    (HL : ∀ q, q < 2 → ∃ (wit : Local W₀ Rc Xi Tr → W) (J : K1.SendJob W X) (own₀ : X)
      (cs : Cs (K1.dueR J.P J.ride)) (e : Ahead)
      (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (front : Nat),
      SharedAsks Zp cF.blocksInOrder (parL Zp Bs.G₀ 23 (q == 1)) (K1.rideOf none) (noL 23 (q == 1)) 0
        (y'.2 + ((Sg.sent.headD #[]).size - 1) + 1 + q) ch p k
        (lotOwn (segmentsOf Zp Bs.G₀) p (D w.x) (readers w) hdL (0 + 23)
          ((Sg.sent.headD #[]).size - 1 -
            (if (y'.1.map (·.1)).isSome then 1 + Sg.sizes.kept.length else 0) + q))
        Q Vd N w (hdL ++ ds) wit J own₀ cs e dataK front) :
    LockAsks freshTable (lotOwn segsW p (D w.x) (readers w) hdL) hdL
      (Stretch.carried p.carries c.2.2) 23 fx
      (wordsFirst (P5J.At.arr Zp) fx.st a.1.2.book (Q.wit k w (hdL ++ ds))) := by
  have hq := (head_door h a hr).1
  have F := head_frontFacts h a hr hq hfx
  obtain ⟨Sg₂, hS₂, hC⟩ := head_fresh_clause h O a hr hfx hp₀ hp e₀ e₁ Q Vd N ch fx₀ D readers lay
    hmF hpF k w hv hdL ds hN hfx₀ c₀ h₀ c hc hs hf hgl hD hV hy'
  obtain rfl : Sg₂ = Sg := Option.some.inj (hS₂.symm.trans hS)
  exact lockAsks_of_facts h O (by omega) (by omega) F hp₀ hp e₀ e₁ Q Vd N ch fx₀ D readers lay
    hmS hpS k w hv hdL ds hN hfx₀ c₀ h₀ c hc hs hf hgl hD hV hy' hS₂ HL
    (by
      rw [hhd]
      exact head_gamma_heard h a hr hq hfx f₀ (by rw [← segments_at_head h.toAtMg O]; exact hS₂))
    (fun R hR => (hC R hR).2)

/-- IT MAY HOLD EMPTILY: hmS, hpS, hmF, hpF AND HL ARE PROVED OF NO SCRIPT, BOOK OR FILLING; it
stands under the head's premise and "reached" too. One run's coins: never quoted for a law. UNDER
"THERE IS" IN HL STANDS cs, A CUT OF THE RUN's COINS, pinned to k by the record's field cut.

**`LockAsks`, WHOLE, AT THE FRONT BEHIND THE LAST SEGMENT** (353). t: what the quiet step in front
of the finish returns: the front is taken off t, and the book is t's. p₀: the head's switch, which
opened group 24. p: the finish. -/
theorem fin_lockAsks (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 353 a) {t : S}
    (he : VerifiableInference.Desc.First.K2.finishFrontQ a.1.2 = .ok t) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt (ProofFile.pAtK2 Zp 24) t = some fx)
    {p₀ p : SwitchPlace} (hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀) (hp : p ∈ switchPlaces Zp Bs.G₀)
    (e₀ : p₀.link = 24) (e₁ : p.link = 25)
    (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT) (Vd : Local W₀ Rc Xi Tr → Prop)
    (N ch fx₀ : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout)
    -- THE SCRIPT's TWO HYPOTHESES AT EACH MESSAGE OF THE OPENING SWITCH IN FRONT OF ITS LAST
    (hmS : ∀ n (i : Fin (loAt 24).length), n < (switchSent p₀.sizes p₀.others).size - 1 →
      (VerifiableInference.Desc.First.Close.membersOf (loAt 24))[n]? = some i →
      OwnMsgs Q Vd N (P5J.At.arr Zp (seatK10 (loAt 24) (P5J.At.pseats Zp) 24 i).1
          (seatK10 (loAt 24) (P5J.At.pseats Zp) 24 i).2) fx₀
        (switchMsgOff ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀ n))
    (hpS : ∀ n (i : Fin (loAt 24).length), n < (switchSent p₀.sizes p₀.others).size - 1 →
      (VerifiableInference.Desc.First.Close.membersOf (loAt 24))[n]? = some i →
      OwnPads Q Vd (seatK10 (loAt 24) (P5J.At.pseats Zp) 24 i).1
        (seatK10 (loAt 24) (P5J.At.pseats Zp) 24 i).2 (fun k _ => switchPadTxt ch p₀ n k))
    -- AND AT ITS LAST, THE FOLD's FRESH MASK
    (hmF : OwnMsgs Q Vd N (P5J.At.arr Zp (VerifiableInference.Desc.First.Close.maskTree 24)
        (VerifiableInference.Desc.First.Close.maskPart 24)) fx₀
      (switchMsgTxt ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀
        ((switchSent p₀.sizes p₀.others).size - 1)))
    (hpF : OwnPads Q Vd (VerifiableInference.Desc.First.Close.maskTree 24)
      (VerifiableInference.Desc.First.Close.maskPart 24)
      (fun k _ => switchPadTxt ch p₀ ((switchSent p₀.sizes p₀.others).size - 1) k))
    (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hv : Vd w) (hdL ds : List Fmt.Drawn)
    (hN : N ≤ (hdL ++ ds).length) (hfx₀ : fx₀ ≤ hdL.length)
    (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries) (h₀ : handed ch p₀ k = some c₀)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hc : handed ch p k = some c)
    (hs : carriedSame Bk p₀ p = true) (hf : carriedFits Bk (switchPlaces Zp Bs.G₀) p = true)
    (hgl : roundsAhead cF.blocksInOrder (VerifiableInference.Desc.First.K2Caller.noAt 23) ≤ fx₀)
    (hD : ∀ s i ad, s < p₀.link → p.addrs s i = some ad → (D w.x).heardAt ad ≤ fx₀)
    {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀ c₀ w
      (hdL.take fx₀) = .ok V)
    -- THE RUN's ROUNDS
    {zz : ProofFile.InstPub} {Rr R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn}
    (f₀ : foldBlocks 0 (cF.blocksInOrder.take 353) (ProofFile.startS Zp zz) Rr C =
      .ok (a.1.2, R₀, C₀)) (hhd : hdL = Rr.map (·.drawn))
    -- TWO LOOK-UPS
    {y' : Option (Left × List OnBytes.OracleShape) × Nat}
    (hy' : closingFrom freshTable (lotOwn (segmentsOf Zp Bs.G₀) p (D w.x) (readers w) hdL) hdL
      (Stretch.carried p.carries c.2.2) ((segmentsOf Zp Bs.G₀).take 24) 0 0 none = .ok y')
    {Sg : SegmentPub} (hS : (segmentsOf Zp Bs.G₀)[24]? = some Sg)
    -- THE TWO LATER SENDERS
    (HL : ∀ q, q < 2 → ∃ (wit : Local W₀ Rc Xi Tr → W) (J : K1.SendJob W X) (own₀ : X)
      (cs : Cs (K1.dueR J.P J.ride)) (e : Ahead)
      (dataK : Nat → Nat → Nat → Option (Cb.Gl.F ⊕ Cb.Gl.E)) (front : Nat),
      SharedAsks Zp cF.blocksInOrder (parL Zp Bs.G₀ 24 (q == 1)) (K1.rideOf none) (noL 24 (q == 1)) 0
        (y'.2 + ((Sg.sent.headD #[]).size - 1) + 1 + q) ch p k
        (lotOwn (segmentsOf Zp Bs.G₀) p (D w.x) (readers w) hdL (0 + 24)
          ((Sg.sent.headD #[]).size - 1 -
            (if (y'.1.map (·.1)).isSome then 1 + Sg.sizes.kept.length else 0) + q))
        Q Vd N w (hdL ++ ds) wit J own₀ cs e dataK front) :
    LockAsks freshTable (lotOwn segsW p (D w.x) (readers w) hdL) hdL
      (Stretch.carried p.carries c.2.2) 24 fx
      (wordsFirst (P5J.At.arr Zp) fx.st t.book (Q.wit k w (hdL ++ ds))) := by
  have hq := (fin_door h a hr he).1
  have F := fin_frontFacts h a hr he hq hfx
  obtain ⟨Sg₂, hS₂, hC⟩ := fin_fresh_clause h O a hr he hfx hp₀ hp e₀ e₁ Q Vd N ch fx₀ D readers lay
    hmF hpF k w hv hdL ds hN hfx₀ c₀ h₀ c hc hs hf hgl hD hV hy'
  obtain rfl : Sg₂ = Sg := Option.some.inj (hS₂.symm.trans hS)
  exact lockAsks_of_facts h O (by omega) (by omega) F hp₀ hp e₀ e₁ Q Vd N ch fx₀ D readers lay
    hmS hpS k w hv hdL ds hN hfx₀ c₀ h₀ c hc hs hf hgl hD hV hy' hS₂ HL
    (by
      rw [hhd]
      exact fin_gamma_heard h a hr he hq hfx f₀ (by rw [← segments_at_head h.toAtMg O]; exact hS₂))
    (fun R hR => (hC R hR).2)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.FrontFacts
#print axioms ProofFile.Honest.K2.Law.head_frontFacts
#print axioms ProofFile.Honest.K2.Law.fin_frontFacts
#print axioms ProofFile.Honest.K2.Law.member_at_facts
#print axioms ProofFile.Honest.K2.Law.members_size_facts
#print axioms ProofFile.Honest.K2.Law.member_tied_facts
#print axioms ProofFile.Honest.K2.Law.later_tied_facts
#print axioms ProofFile.Honest.K2.Law.lockAsks_of_facts
#print axioms ProofFile.Honest.K2.Law.head_lockAsks
#print axioms ProofFile.Honest.K2.Law.fin_lockAsks
