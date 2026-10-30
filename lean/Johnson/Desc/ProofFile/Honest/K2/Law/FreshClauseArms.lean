-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/FreshClauseArms.lean: the kind "the code switch" (K2): THE
ASSEMBLY UNDER THE HEAD, ITS FIRST PIECE, AT THE TWO ARMS: `link_fresh_clause`
(Honest/K2/Law/FreshClause.lean) once more at the output head's front and behind the last segment.
Two statements with their proofs; no definition. EACH MAY HOLD EMPTILY: see the docstrings.

  `head_fresh_clause` the clause at m = 23, at a state reached at the border 339
  `fin_fresh_clause` the clause at m = 24, at a state reached at the border 353; one binder and one
                    return more, on the verifier's side: t, what the quiet step in front of the
                    finish returns (`finishFrontQ a.1.2 = .ok t`): the front is taken off t and the
                    book is t's

Each statement is `link_fresh_clause`'s with m laid in; the prover's side is the same text in all
three.

THE BORDERS. 339 and 353 are not instances of the links' formula 14 * (m + 1) + 2, which gives 338
and 352: each is one more. They are the borders of `head_door` and `fin_door`
(Johnson/Desc/K2/Honest/Returns/DoorReached.lean), and the library's `noAt 23` and `noAt 24`
(Johnson/P1K2R/CarryAtConst.lean). A wrong border would leave the premises true of nothing and the
statement idle. So each proof calls these laws at hr: with 338 or 352 written in hr the proof does
not type: Lean refuses hr at `head_door` | `fin_door` and at five calls more.

With FreshClause.lean the clause stands at 24 of the 25 places of the kind. Not at m = 0: the first
segment's fresh mask has a sender of the kind K1.

By: what FreshClause.lean's head lists, with the head's and the finish's laws in the place of the
links': under Johnson/Desc/K2/Honest/Returns/: `head_door`, `fin_door` (DoorReached.lean) ·
`head_member_stated`, `fin_member_stated` (SeatReached.lean) · `head_closedBehind`,
`fin_closedBehind`, `head_freshWord_front`, `fin_freshWord_front` (FreshNumbered.lean) ·
`head_frontTies`, `fin_frontTies` (FrontTiesReached.lean) · the library's `front_pin_head`,
`front_nums_fin`. No shared core is stated: the three proofs run alike.

What stays a premise, and the limits: FreshClause.lean's; behind the last segment he too: that the
quiet step returns is not shown here. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.FreshClause

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K2.Law
open OnBytes (ceilLog2)
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K2.Honest (Left)
open VerifiableInference.Desc.K2.Honest.Returns (head_door fin_door head_member_stated
  fin_member_stated head_closedBehind fin_closedBehind fresh_of_closedBehind head_freshWord_front
  fin_freshWord_front head_frontTies fin_frontTies)
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

/-- IT MAY HOLD EMPTILY: hm AND hp ARE PROVED OF NO SCRIPT. AND MORE EMPTILY THAN THE CORE: it
stands under the head's premise and "reached" too: no run is given at which these hold together. One
run's coins: never quoted for a law. "hp" is this statement's hpd.

**THE LOCK's CLAUSE ON THE FOLD's FRESH MASK, AT A RUN's COINS, AT THE OUTPUT HEAD's FRONT**:
`link_fresh_clause` at m = 23. THE BORDER IS 339: the border of `head_door`, which the proof calls
at it. It is not the links' formula at m = 23: 14 * (23 + 1) + 2 = 338: it is one more. p₀: the
switch that opened group 23. p: the head's switch. -/
theorem head_fresh_clause (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    -- THE VERIFIER's SIDE: a state reached in front of the later switch, and the item's own front
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 339 a) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt (ProofFile.pAtK2 Zp 23) a.1.2 = some fx)
    -- THE TWO PLACES
    {p₀ p : SwitchPlace} (hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀) (hp : p ∈ switchPlaces Zp Bs.G₀)
    (e₀ : p₀.link = 23) (e₁ : p.link = 24)
    -- THE SCRIPT's TWO HYPOTHESES, BY NAME, AT THE SENDER's LAST MESSAGE, AT THE PLAN's SEAT
    (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT) (Vd : Local W₀ Rc Xi Tr → Prop)
    (N ch fx₀ : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout)
    (hm : OwnMsgs Q Vd N (P5J.At.arr Zp (VerifiableInference.Desc.First.Close.maskTree 23)
        (VerifiableInference.Desc.First.Close.maskPart 23)) fx₀
      (switchMsgTxt ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀
        ((switchSent p₀.sizes p₀.others).size - 1)))
    (hpd : OwnPads Q Vd (VerifiableInference.Desc.First.Close.maskTree 23)
      (VerifiableInference.Desc.First.Close.maskPart 23)
      (fun k _ => switchPadTxt ch p₀ ((switchSent p₀.sizes p₀.others).size - 1) k))
    -- ONE RUN: its coins, its input, what the later switch has heard, any continuation
    (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hv : Vd w) (hdL ds : List Fmt.Drawn)
    (hN : N ≤ (hdL ++ ds).length) (hfx₀ : fx₀ ≤ hdL.length)
    -- RETURNS AND THE BOOK's TWO TESTS
    (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries) (h₀ : handed ch p₀ k = some c₀)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hc : handed ch p k = some c)
    (hs : carriedSame Bk p₀ p = true) (hf : carriedFits Bk (switchPlaces Zp Bs.G₀) p = true)
    (hgl : roundsAhead cF.blocksInOrder (VerifiableInference.Desc.First.K2Caller.noAt 22) ≤ fx₀)
    (hD : ∀ s i ad, s < p₀.link → p.addrs s i = some ad → (D w.x).heardAt ad ≤ fx₀)
    {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀ c₀ w
      (hdL.take fx₀) = .ok V)
    {y' : Option (Left × List OnBytes.OracleShape) × Nat}
    (hy' : closingFrom freshTable (lotOwn (segmentsOf Zp Bs.G₀) p (D w.x) (readers w) hdL) hdL
      (Stretch.carried p.carries c.2.2) ((segmentsOf Zp Bs.G₀).take 23) 0 0 none = .ok y') :
    ∃ Sg, (segmentsOf Zp Bs.G₀)[23]? = some Sg ∧ ∀ R : GroupRows,
      segmentGroupRows freshTable Sg (y'.1.map (·.1)) ((y'.1.map (·.2)).getD [])
        (lotOwn (segmentsOf Zp Bs.G₀) p (D w.x) (readers w) hdL (0 + 23))
        (Stretch.carried p.carries c.2.2) y'.2 true = .ok R →
      R.fresh = some (V ((switchSent p₀.sizes p₀.others).size - 1)) ∧
      ∀ b j, b < 2 ^ fx.f.rows.layout.h →
        (R.fresh.getD zeroMessage).mask b j =
          wordsFirst (P5J.At.arr Zp) fx.st a.1.2.book (Q.wit k w (hdL ++ ds)) fx.f.rows.fresh .mask
            (b + j * 2 ^ ceilLog2 (fx.st.oracles.getD fx.f.rows.fresh default).shape.maskRows) := by
  have hlen : (hdL.take fx₀).length = fx₀ := by
    rw [List.length_take]
    exact Nat.min_eq_left hfx₀
  have hq := (head_door h a hr).1
  have hu := (head_member_stated h a hr).1
  have K := key_of_lots h.toAtMg O ch D readers lay hp₀ hp (by omega) k c₀ h₀ c hc hs
    hf w (hd₀ := hdL.take fx₀) (hd := hdL) (List.take_prefix _ _)
    (fun Sg hSg g hg => by
      rw [hlen]
      rw [e₀] at hSg
      exact Nat.lt_of_lt_of_le (gamma_below_at_head h.toAtMg O (m := 22) (by omega) Sg hSg g hg)
        hgl)
    (fun s i ad h1 h2 => by
      rw [hlen]
      exact hD s i ad h1 h2) hV (by rw [e₀]; exact hy')
  rw [e₀] at K
  obtain ⟨Sg, hSg, hK⟩ := K
  refine ⟨Sg, hSg, fun R hR => ?_⟩
  have eF := (hK R hR).2
  refine ⟨eF, ?_⟩
  obtain ⟨f1, f2, f3⟩ := fresh_of_closedBehind h (by omega) hr.2 a.2
    (head_closedBehind h a hr hq hfx)
  obtain ⟨-, R', C', f⟩ := (reach_raw (h.toAtMg.rch_is_reach _ a hr)).fold
  obtain ⟨-, a2, -⟩ := Meaning.K2.front_pin_head h.scope h.reads O f hq hfx
  have t2 : (fx.st.oracles.getD fx.f.rows.fresh default).shape =
      ((switchSent p₀.sizes p₀.others).getD ((switchSent p₀.sizes p₀.others).size - 1)
        default).shape := by
    have s := mask_shape_getD h O a hr hu hp₀ (by omega) (by rw [e₀, ← f1]; exact f2) a2
    rw [e₀] at s
    rw [f1]
    exact s
  have t1 : fx.st.codes = p₀.sizes.codes :=
    (place_codes_at_front h.toAtMg O hp₀ hp (by omega)
      (head_frontTies h.scope h.reads O (h.toAtMg.rch_is_reach _ a hr) hq hfx)).symm
  obtain ⟨M, hM⟩ := rows_of_laid D readers _ p₀ c₀ w _ hV
  have hfit := rowsAll_fits hM
  have hmain := (ride_facts hfit (last_in p₀) (foldAt_last p₀)
    (lastMaskRows_one (atMostOneMaskRow_at_head h.toAtMg O p₀ hp₀) hfit)).1
  have e3 : (fx.st.oracles.getD fx.f.rows.fresh default).shape.maskRows =
      2 ^ fx.f.rows.layout.h := by
    rw [a2]
    exact f3
  have L := (lock_rows_of_key Q Vd N ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀ fx₀
    ((switchSent p₀.sizes p₀.others).size - 1) _ _ _ hm hpd (noWord_open O p₀ hp₀) (last_in p₀) k h₀
    w hv (hdL ++ ds) hN (by rw [List.take_append_of_le_length hfx₀]; exact hV) rfl t1 t2
    (wordsFirst (P5J.At.arr Zp) fx.st a.1.2.book (Q.wit k w (hdL ++ ds))) fx.f.rows.fresh
    (fun part b i hb => by
      cases part with
      | main =>
        have hb' : b < (fx.st.oracles.getD fx.f.rows.fresh default).shape.mainRows := hb
        rw [t2, hmain] at hb'
        omega
      | mask =>
        have hb' : b < (fx.st.oracles.getD fx.f.rows.fresh default).shape.maskRows := hb
        exact head_freshWord_front h a hr hq hfx _ _ (by rw [← e3]; exact hb') i)).2
  intro b j hb
  rw [eF, Option.getD_some]
  exact L b j (by rw [e3]; exact hb)

/-- IT MAY HOLD EMPTILY: hm AND hp ARE PROVED OF NO SCRIPT. AND MORE EMPTILY THAN THE CORE: it
stands under the head's premise and "reached" too: no run is given at which these hold together. One
run's coins: never quoted for a law. "hp" is this statement's hpd.

**THE LIKE BEHIND THE LAST SEGMENT**: `link_fresh_clause` at m = 24. THE BORDER IS 353: the border
of `fin_door`, which the proof calls at it. It is not the links' formula at m = 24: 14 * (24 + 1) +
2 = 352: it is one more. t: what the quiet step in front of the finish returns: the front is taken
off t, and the book is t's. p₀: the head's switch, which opened group 24. p: the finish. -/
theorem fin_fresh_clause (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    -- THE VERIFIER's SIDE: a state reached in front of the later switch, and the item's own front
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch 353 a) {t : S}
    (he : VerifiableInference.Desc.First.K2.finishFrontQ a.1.2 = .ok t) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt (ProofFile.pAtK2 Zp 24) t = some fx)
    -- THE TWO PLACES
    {p₀ p : SwitchPlace} (hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀) (hp : p ∈ switchPlaces Zp Bs.G₀)
    (e₀ : p₀.link = 24) (e₁ : p.link = 25)
    -- THE SCRIPT's TWO HYPOTHESES, BY NAME, AT THE SENDER's LAST MESSAGE, AT THE PLAN's SEAT
    (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT) (Vd : Local W₀ Rc Xi Tr → Prop)
    (N ch fx₀ : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout)
    (hm : OwnMsgs Q Vd N (P5J.At.arr Zp (VerifiableInference.Desc.First.Close.maskTree 24)
        (VerifiableInference.Desc.First.Close.maskPart 24)) fx₀
      (switchMsgTxt ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀
        ((switchSent p₀.sizes p₀.others).size - 1)))
    (hpd : OwnPads Q Vd (VerifiableInference.Desc.First.Close.maskTree 24)
      (VerifiableInference.Desc.First.Close.maskPart 24)
      (fun k _ => switchPadTxt ch p₀ ((switchSent p₀.sizes p₀.others).size - 1) k))
    -- ONE RUN: its coins, its input, what the later switch has heard, any continuation
    (k : Coins Bk) (w : Local W₀ Rc Xi Tr) (hv : Vd w) (hdL ds : List Fmt.Drawn)
    (hN : N ≤ (hdL ++ ds).length) (hfx₀ : fx₀ ≤ hdL.length)
    -- RETURNS AND THE BOOK's TWO TESTS
    (c₀ : SwitchCoins p₀.sizes p₀.others p₀.foldVars p₀.carries) (h₀ : handed ch p₀ k = some c₀)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hc : handed ch p k = some c)
    (hs : carriedSame Bk p₀ p = true) (hf : carriedFits Bk (switchPlaces Zp Bs.G₀) p = true)
    (hgl : roundsAhead cF.blocksInOrder (VerifiableInference.Desc.First.K2Caller.noAt 23) ≤ fx₀)
    (hD : ∀ s i ad, s < p₀.link → p.addrs s i = some ad → (D w.x).heardAt ad ≤ fx₀)
    {V : Nat → Johnson.Prover.Send.Rows}
    (hV : switchRowsLaid D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀ c₀ w
      (hdL.take fx₀) = .ok V)
    {y' : Option (Left × List OnBytes.OracleShape) × Nat}
    (hy' : closingFrom freshTable (lotOwn (segmentsOf Zp Bs.G₀) p (D w.x) (readers w) hdL) hdL
      (Stretch.carried p.carries c.2.2) ((segmentsOf Zp Bs.G₀).take 24) 0 0 none = .ok y') :
    ∃ Sg, (segmentsOf Zp Bs.G₀)[24]? = some Sg ∧ ∀ R : GroupRows,
      segmentGroupRows freshTable Sg (y'.1.map (·.1)) ((y'.1.map (·.2)).getD [])
        (lotOwn (segmentsOf Zp Bs.G₀) p (D w.x) (readers w) hdL (0 + 24))
        (Stretch.carried p.carries c.2.2) y'.2 true = .ok R →
      R.fresh = some (V ((switchSent p₀.sizes p₀.others).size - 1)) ∧
      ∀ b j, b < 2 ^ fx.f.rows.layout.h →
        (R.fresh.getD zeroMessage).mask b j =
          wordsFirst (P5J.At.arr Zp) fx.st t.book (Q.wit k w (hdL ++ ds)) fx.f.rows.fresh .mask
            (b + j * 2 ^ ceilLog2 (fx.st.oracles.getD fx.f.rows.fresh default).shape.maskRows) := by
  have hlen : (hdL.take fx₀).length = fx₀ := by
    rw [List.length_take]
    exact Nat.min_eq_left hfx₀
  have hq := (fin_door h a hr he).1
  have hu := (fin_member_stated h a hr).1
  have K := key_of_lots h.toAtMg O ch D readers lay hp₀ hp (by omega) k c₀ h₀ c hc hs
    hf w (hd₀ := hdL.take fx₀) (hd := hdL) (List.take_prefix _ _)
    (fun Sg hSg g hg => by
      rw [hlen]
      rw [e₀] at hSg
      exact Nat.lt_of_lt_of_le (gamma_below_at_head h.toAtMg O (m := 23) (by omega) Sg hSg g hg)
        hgl)
    (fun s i ad h1 h2 => by
      rw [hlen]
      exact hD s i ad h1 h2) hV (by rw [e₀]; exact hy')
  rw [e₀] at K
  obtain ⟨Sg, hSg, hK⟩ := K
  refine ⟨Sg, hSg, fun R hR => ?_⟩
  have eF := (hK R hR).2
  refine ⟨eF, ?_⟩
  obtain ⟨f1, f2, f3⟩ := fresh_of_closedBehind h (by omega) hr.2 a.2
    (fin_closedBehind h a hr he hq hfx)
  obtain ⟨-, R', C', f⟩ := (reach_raw (h.toAtMg.rch_is_reach _ a hr)).fold
  obtain ⟨-, -, -, a2, -⟩ := Meaning.K2.front_nums_fin h.scope h.reads O f he hq hfx
  have t2 : (fx.st.oracles.getD fx.f.rows.fresh default).shape =
      ((switchSent p₀.sizes p₀.others).getD ((switchSent p₀.sizes p₀.others).size - 1)
        default).shape := by
    have s := mask_shape_getD h O a hr hu hp₀ (by omega) (by rw [e₀, ← f1]; exact f2) a2
    rw [e₀] at s
    rw [f1]
    exact s
  have t1 : fx.st.codes = p₀.sizes.codes :=
    (place_codes_at_front h.toAtMg O hp₀ hp (by omega)
      (fin_frontTies h.scope h.reads O (h.toAtMg.rch_is_reach _ a hr) he hq hfx)).symm
  obtain ⟨M, hM⟩ := rows_of_laid D readers _ p₀ c₀ w _ hV
  have hfit := rowsAll_fits hM
  have hmain := (ride_facts hfit (last_in p₀) (foldAt_last p₀)
    (lastMaskRows_one (atMostOneMaskRow_at_head h.toAtMg O p₀ hp₀) hfit)).1
  have e3 : (fx.st.oracles.getD fx.f.rows.fresh default).shape.maskRows =
      2 ^ fx.f.rows.layout.h := by
    rw [a2]
    exact f3
  have L := (lock_rows_of_key Q Vd N ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀ fx₀
    ((switchSent p₀.sizes p₀.others).size - 1) _ _ _ hm hpd (noWord_open O p₀ hp₀) (last_in p₀) k h₀
    w hv (hdL ++ ds) hN (by rw [List.take_append_of_le_length hfx₀]; exact hV) rfl t1 t2
    (wordsFirst (P5J.At.arr Zp) fx.st t.book (Q.wit k w (hdL ++ ds))) fx.f.rows.fresh
    (fun part b i hb => by
      cases part with
      | main =>
        have hb' : b < (fx.st.oracles.getD fx.f.rows.fresh default).shape.mainRows := hb
        rw [t2, hmain] at hb'
        omega
      | mask =>
        have hb' : b < (fx.st.oracles.getD fx.f.rows.fresh default).shape.maskRows := hb
        exact fin_freshWord_front h a hr he hq hfx _ _ (by rw [← e3]; exact hb') i)).2
  intro b j hb
  rw [eF, Option.getD_some]
  exact L b j (by rw [e3]; exact hb)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.head_fresh_clause
#print axioms ProofFile.Honest.K2.Law.fin_fresh_clause
