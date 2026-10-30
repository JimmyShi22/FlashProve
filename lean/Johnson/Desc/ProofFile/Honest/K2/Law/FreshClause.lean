-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/FreshClause.lean: the kind "the code switch" (K2): THE ASSEMBLY
UNDER THE HEAD, ITS FIRST PIECE: THE LOCK's CLAUSE ON THE FOLD's FRESH MASK, AT A RUN's COINS, at
the 22 link places whose closed group a switch opened (1 ≤ m < 23). One statement with its proof; no
definition. IT MAY HOLD EMPTILY: see its docstring.

  `link_fresh_clause` under the head, at a state reached in front of the later switch p, at the
                    item's own front fx: where `segmentGroupRows`, at the later switch's carried
                    stretches, returns R: `R.fresh = some (V q)`, V the rows that the sender p₀
                    laid, q its last message; and each entry of that message's mask rows is the word
                    that `wordsFirst` reads off the Script's witness at the front's fresh mask

What it is for. `LockedAt` (Honest/K2/Law/LockAtFront.lean) has three clauses on entries as a
premise. This statement's second end is the third of them, sign for sign, at table := `freshTable`,
own := `lotOwn …`, heard := hdL, k := `Stretch.carried p.carries c.2.2`, w := `wordsFirst (At.arr
Zp) fx.st a.1.2.book (Q.wit k w (hdL ++ ds))`. `LockedAt` speaks at the written `segsW`, this
statement at `segmentsOf Zp Bs.G₀`: under the head the two are one (`segments_at_head`,
Honest/K2/Law/PlacesWritten.lean): that call is the spender's. The first end bars, within the
sentence, the default in `R.fresh.getD zeroMessage`, and names the middle term: the sender's rows V.

Why this clause first. The fresh mask is the sending's last message: no kept copy, no later sending,
no sender of the kind K1 (for m ≥ 1) stands in the way.

By: `key_of_lots` (Honest/K2/Law/KeyOfLots.lean) · `lock_rows_of_key` (LockRows.lean) ·
`ride_facts`, `foldAt_last` (FreshTxt.lean) · `last_in`, `lastMaskRows_one` (FreshTxtAtHead.lean) ·
`atMostOneMaskRow_at_head` (OneMaskRowAtHead.lean) · `rows_of_laid` (MaskTxt.lean) · `rowsAll_fits`
(Laid.lean) · `noWord_open` (SampledOpen.lean) · `place_codes_at_front` (FirstShapes.lean) ·
`mask_shape_getD` (ShapesAtFront.lean) · `gamma_below_at_head` (GammaBelow.lean) · under
Johnson/Desc/K2/Honest/Returns/: `link_door` (DoorReached.lean), `link_member_stated`
(SeatReached.lean), `link_closedBehind`, `fresh_of_closedBehind`, `link_freshWord_front`
(FreshNumbered.lean), `link_frontTies` (FrontTiesReached.lean) · the library's `front_pin_link`,
`reach_raw`.

What stays a premise. hm, hpd: the Script's two hypotheses, at the sender's last message, at the
plan's seat · fx₀, a letter, with hgl: that it is the lot's number of challenges, and that the
sender's part stands behind so many rounds, is shown nowhere · hs, hf: two tests on the book · hD:
on the filling · five returns (h₀, hc, hV, hy', and `segmentGroupRows`') · `Vd w` · hfx: that a front is
there.

Limits. One run's coins. No run is given at which the head's premise and "reached" hold together.
Not m = 0 (the first segment's fresh mask: a sender of the kind K1), not the places 339 and 353.
Nothing on the lock's two clauses on the members, nor on its premise on the challenges heard. It
speaks of a text, not of a move. No thread and no filling is named. The full size and the format's
second hash function alone. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.KeyOfLots
import Johnson.Desc.ProofFile.Honest.K2.Law.LockRows
import Johnson.Desc.ProofFile.Honest.K2.Law.FreshTxtAtHead
import Johnson.Desc.ProofFile.Honest.K2.Law.ShapesAtFront
import Johnson.Desc.ProofFile.Honest.K2.Law.GammaBelow
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
open VerifiableInference.Desc.K2.Honest (Left)
open VerifiableInference.Desc.K2.Honest.Returns (link_door link_member_stated link_closedBehind
  fresh_of_closedBehind link_freshWord_front link_frontTies)
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
run's coins: never quoted for a law. "hp" is this statement's hpd. A small Script at a made-up place
has both (Honest/K2/Law/LockRowsSmall.lean, which this library may not hold): none at a place of the
plan.

**THE LOCK's CLAUSE ON THE FOLD's FRESH MASK, AT A RUN's COINS**, at a link place whose closed group
a switch opened (1 ≤ m < 23). p₀: the switch that sent the closed group's first sending. p: the
later switch. hdL: what the later switch has heard in front of its part; ds: any continuation. -/
theorem link_fresh_clause (h : AtMgA OnBytes.secondHashFunction Z D₀ r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np))
    {m : Nat} (hm1 : 1 ≤ m) (h23 : m < 23)
    -- THE VERIFIER's SIDE: a state reached in front of the later switch, and the item's own front
    (a : ((F0T OnBytes.secondHashFunction Zp Np cF).XiPub × (F0T OnBytes.secondHashFunction Zp Np cF).S₁) ×
      (EAll (D₀.at OnBytes.Slice.frS.P.T.a) (allOf (D₀.at OnBytes.Slice.frS.P.T.a))).Str)
    (hr : h.toAtMg.rch (14 * (m + 1) + 2) a) {fx : _root_.Tw.K2.Front}
    (hfx : VerifiableInference.Desc.First.K2.frontAt (ProofFile.pAtK2 Zp m) a.1.2 = some fx)
    -- THE TWO PLACES
    {p₀ p : SwitchPlace} (hp₀ : p₀ ∈ switchPlaces Zp Bs.G₀) (hp : p ∈ switchPlaces Zp Bs.G₀)
    (e₀ : p₀.link = m) (e₁ : p.link = m + 1)
    -- THE SCRIPT's TWO HYPOTHESES, BY NAME, AT THE SENDER's LAST MESSAGE, AT THE PLAN's SEAT
    (Q : Script Bk (Local W₀ Rc Xi Tr) Cells Tok MsgT) (Vd : Local W₀ Rc Xi Tr → Prop)
    (N ch fx₀ : Nat) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout)
    (hm : OwnMsgs Q Vd N (P5J.At.arr Zp (VerifiableInference.Desc.First.Close.maskTree m)
        (VerifiableInference.Desc.First.Close.maskPart m)) fx₀
      (switchMsgTxt ch D readers (lotClosingAt lay (segmentsOf Zp Bs.G₀)) p₀
        ((switchSent p₀.sizes p₀.others).size - 1)))
    (hpd : OwnPads Q Vd (VerifiableInference.Desc.First.Close.maskTree m)
      (VerifiableInference.Desc.First.Close.maskPart m)
      (fun k _ => switchPadTxt ch p₀ ((switchSent p₀.sizes p₀.others).size - 1) k))
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
      R.fresh = some (V ((switchSent p₀.sizes p₀.others).size - 1)) ∧
      ∀ b j, b < 2 ^ fx.f.rows.layout.h →
        (R.fresh.getD zeroMessage).mask b j =
          wordsFirst (P5J.At.arr Zp) fx.st a.1.2.book (Q.wit k w (hdL ++ ds)) fx.f.rows.fresh .mask
            (b + j * 2 ^ ceilLog2 (fx.st.oracles.getD fx.f.rows.fresh default).shape.maskRows) := by
  subst e₀
  have hlen : (hdL.take fx₀).length = fx₀ := by
    rw [List.length_take]
    exact Nat.min_eq_left hfx₀
  have hq := (link_door h h23 a hr).1
  have hu := (link_member_stated h h23 a hr).1
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
  have eF := (hK R hR).2
  refine ⟨eF, ?_⟩
  obtain ⟨f1, f2, f3⟩ := fresh_of_closedBehind h (by omega) hr.2 a.2
    (link_closedBehind h h23 a hr hq hfx)
  obtain ⟨-, R', C', f⟩ := (reach_raw (h.toAtMg.rch_is_reach _ a hr)).fold
  obtain ⟨-, a2, -⟩ := Meaning.K2.front_pin_link h.scope h.reads O (l := p₀.link + 1) (by omega)
    (by omega) f hq hfx
  have t2 : (fx.st.oracles.getD fx.f.rows.fresh default).shape =
      ((switchSent p₀.sizes p₀.others).getD ((switchSent p₀.sizes p₀.others).size - 1)
        default).shape := by
    rw [f1]
    exact mask_shape_getD h O a hr hu hp₀ (by omega) (by rw [← f1]; exact f2) a2
  have t1 : fx.st.codes = p₀.sizes.codes :=
    (place_codes_at_front h.toAtMg O hp₀ hp (by omega)
      (link_frontTies h.scope h.reads O h23 (h.toAtMg.rch_is_reach _ a hr) hq hfx)).symm
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
        exact link_freshWord_front h h23 a hr hq hfx _ _ (by rw [← e3]; exact hb') i)).2
  intro b j hb
  rw [eF, Option.getD_some]
  exact L b j (by rw [e3]; exact hb)

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.link_fresh_clause
