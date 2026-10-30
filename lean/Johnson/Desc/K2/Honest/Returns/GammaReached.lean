-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K2/Honest/Returns/GammaReached.lean: THE CHALLENGES THAT A CODE SWITCH's CARRIED ROWS
HOLD (`SingleRows.gamma`) ARE THE ELEMENTS THAT THE RUN's OWN ROUNDS DREW, BY NUMBER: in the goals'
scope, from the fold's return WITH ITS ROUNDS NAMED, at all three sorts of the kind's places.
Statements with their proofs; no definition. Over the library alone.

  `gamma_of_close` `closeFrame owed f S₀ es rs = .ok x` ⊢ `x.1.rows.gamma = (rs.drop 2).map
                    drawnOf`: the closing's first two rounds are "BAT" and "FOLD epsilon"; each
                    round behind them draws one challenge (`drawnOf`,
                    Johnson/Prover/Link/FormFold.lean)
  `take_own_length` a front of a list, cut at its own length, is that front
  `gamma_list` from the closing's own slice of the rounds, without their sealed digests, to the
                    rounds behind its first two: on lists alone
  `tail_frame_rounds` `tail_frame` (Johnson/IMR/TailFrame.lean), ALL ITS CLAUSES, WITH THE CLOSING's
                    ROUNDS NAMED: l < 24: they are `(R₃.take n).map noDigest`, R₃ what the fold over
                    the first 14 l + 12 left over; and R₃ is `R.drop (roundsAhead c.blocksInOrder (14 * l +
                    12))` (`roundsAhead`, Johnson/Desc/K13/Honest/FoldCut.lean: how many rounds the
                    first k sub-protocols have)
  `cleared_frame_rounds` the like at the last segment: `closing_behind_cleared`
                    (Returns/HeadSegment.lean), ALL ITS CLAUSES, with the closing's rounds named:
                    `(Rw.take n).map noDigest`; and Rw is `R.drop (roundsAhead c.blocksInOrder 350)`: the
                    cuts 350 and 353
  `gamma_behind_laid` l < 24: where the fold over the first 14 (l + 1) + 2, at the rounds R, returns
                    t₀: t₀'s walk's frame's carried rows' gamma is `((R.drop (roundsAhead c.blocksInOrder (14
                    * l + 12) + 2)).take ‹its own length›).map drawnOf`
  `gamma_behind_cleared` the like at 353, with `roundsAhead c.blocksInOrder 350`
  `link_gamma_front` m < 23: the same of `fx.f.rows.gamma`, at the front that the switch's block
                    takes off the state at 14 (m + 1) + 2
  `head_gamma_front` at the output head's front (339): with `roundsAhead c.blocksInOrder 334`
  `fin_gamma_front` at the front behind the last segment (353, behind its quiet step in front): with
                    `roundsAhead c.blocksInOrder 350`

Why. `tail_frame`, and this folder's `closing_behind_laid` (Returns/SeatsWalk.lean) and
`closing_behind_cleared`, say "there are rounds rs at which `closeFrame` returned": that these are
the run's own is lost there, because `fold_next` (Johnson/IMR/FoldTools.lean) binds them under
"there are". A law that holds a prover's list of challenges heard against the verifier's carried
rows needs them named.

TWO PROOFS STAND HERE AGAIN, COPIED BY PROGRAM, EACH WITH ONE TURN, MARKED IN THE TEXT:
`tail_frame`'s (its lines 44 to 101) and `closing_behind_cleared`'s (its lines 81 to 133): ONE CALL
OF THE LIBRARY's `fold_to_decision` (Johnson/Desc/K13/Honest/ClaimsIsAt.lean) in the stead of
`fold_next`: it hands over the sub-protocol's decision AT ITS OWN SLICE OF THE RUN's ROUNDS, and
what the fold in front leaves over; the last line of each hands these on. Each of the two other laws
is its law here with the last clause dropped and the rounds under "there are" (not typed as
corollaries); they stay as they are.

By, beside these, all the library's: `closeFrame_iff` (Johnson/Desc/First/Close/Law/CloseMeans.lean)
· `rounds_read` (Johnson/Desc/K10/Honest/Leaves.lean) · `fold_cut`, `fold_back` · `front_pin_link`
(Johnson/IMR/FrontPin.lean), `front_nums_head` (Johnson/IMR/HeadFront.lean), `front_nums_fin`
(Johnson/IMR/FinCount.lean). NEAR, NOT CALLED: `yes_leaves` (Leaves.lean): each yes of the closing
kind's own decision leaves `foldOutAt … (rE :: rR)`, whose gamma is `rR.map drawnOf`: at the kind's
record, at rounds that are letters · `rows_shape` (Johnson/Desc/K10/Honest/Returns.lean),
`foldOutput_gamma` (OnBytes/Slice/BlkFoldOut.lean): `foldOutput`'s gamma is the list handed in ·
`drawnOf_noDigest`, `map_drawnOf_noDigest` (Johnson/Prover/Link/BodyHelps.lean): what `gamma_list`'s
proof gets by `rfl`.

Limits. THAT A FOLD RETURNS IS A PREMISE: shown of no proof here. THE FIVE ENDS FIX gamma's ENTRIES,
NOT THEIR NUMBER: each cuts what the rounds from that number on drew at gamma's own length, and the
empty list satisfies that too: the number is had by the library's `closeFrame_sizes`
(Johnson/Desc/First/Link/Law/CarriedSizes.lean) and this folder's `LayFits.challenges`
(Returns/ClosedReached.lean), not called here. `roundsAhead c.blocksInOrder k` is a term, not a numeral.
Nothing says which rounds of the declared list these are by name. `drawnOf` gives (0, 0, 0) at a
round that drew nothing: that each of these rounds drew just one element is known inside
`gamma_of_close`'s proof and not handed out. Nothing on a prover: no list of challenges heard is
named. The imports are heavy. Nothing on any property.
-/
import Johnson.IMR.TailFrame
import Johnson.Desc.K10.Honest.Leaves
import Johnson.Desc.K13.Honest.ClaimsIsAt
import Johnson.Desc.K2.Honest.Returns.HeadSegment
import Johnson.IMR.FrontPin
import Johnson.IMR.HeadFront
import Johnson.IMR.FinCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K2.Honest.Returns

open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First
open VerifiableInference.Desc.K9
open ProofFile (Cl)
open Meaning.K2
open Johnson.Prover.Link (drawnOf)
open VerifiableInference.Desc.K13.Honest (roundsAhead fold_to_decision)

/-- **The carried rows' challenges are the elements that the closing's rounds behind its first two
drew.** -/
theorem gamma_of_close {owed : Option Nat} {f : ReqFrame} {S₀ : Statement} {es : List Fmt.Entry}
    {rs : List Fmt.RoundView} {x : ReqFrame × Statement}
    (h : Close.closeFrame owed f S₀ es rs = .ok x) :
    x.1.rows.gamma = (rs.drop 2).map drawnOf := by
  obtain ⟨-, Lk, -, Gf, -, -, rows, hc, e⟩ := (Close.closeFrame_iff owed f S₀ es rs x.1 x.2).1 h
  obtain ⟨eB, es₁, rB, rs₁, -, rfl, m, -, row, Ly, S1, -, -, hfold⟩ := hc
  obtain ⟨eE, eR, rE, rR, -, rfl, -, -, -, -, -, d2, -, sum, eps, -, -, gam, cl, f9, f10, -⟩ :=
    hfold
  rw [e, f10]
  exact (ProofFile.Honest.K10.Values.rounds_read _ _ _ _ _ f9).1

/-- A front of a list, cut at its own length, is that front. -/
theorem take_own_length {α : Type} : ∀ (X : List α) (a : Nat), X.take (X.take a).length = X.take a
  | [], a => by simp
  | _ :: _, 0 => by simp
  | _ :: _, _ + 1 => by simp

/-- From the closing's own slice of the rounds to the rounds behind its first two. -/
theorem gamma_list {R₃ : List Fmt.RoundView} {n : Nat} {g : List E}
    (h : g = (((R₃.take n).map noDigest).drop 2).map drawnOf) :
    g = ((R₃.drop 2).take g.length).map drawnOf := by
  have e : (((R₃.take n).map noDigest).drop 2).map drawnOf =
      ((R₃.drop 2).take (n - 2)).map drawnOf := by
    rw [← List.map_drop, List.map_map, List.drop_take]
    rfl
  rw [e] at h
  have hl : g.length = ((R₃.drop 2).take (n - 2)).length := by rw [h, List.length_map]
  rw [hl, take_own_length]
  exact h

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **`tail_frame` (Johnson/IMR/TailFrame.lean) WITH THE CLOSING's ROUNDS NAMED**: they are the
first n of the rounds that the fold in front of the closing left over, without their sealed
digests. -/
theorem tail_frame_rounds (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₃ R₂ : List Fmt.RoundView} {C C₃ C₂ : List VerifiableInference.Desc.OpenedColumn}
    {s t₂ : S}
    (g3 : foldBlocks 0 (c.blocksInOrder.take (14 * l + 12)) (ProofFile.startS Z p) R C = .ok (s, R₃, C₃))
    (f₂ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₂, R₂, C₂)) :
    ∃ (L : LinkCtx) (Q : Close.Par) (n : Nat) (y : ReqFrame × Statement),
      s.link? = some L ∧ L.link = l ∧
      Close.closeFrame (K9.recOf s).owed L.check.frame s.st (Close.entries Q)
        ((R₃.take n).map noDigest) = .ok y ∧
      t₂.check.frame = y.1 ∧ R₃ = R.drop (roundsAhead c.blocksInOrder (14 * l + 12)) := by
  obtain ⟨L, hL, eLn, -⟩ := group_open hS hR O h24 9 (by omega) s R₃ C₃ g3
  obtain ⟨-, fs, hfs, hfr⟩ := IM.frame_of hS hR O
  obtain ⟨Lk, f, bL, bB, bC, eL, hlen, hf, -, -, -, hClear, -, -, -, -, -, -, iC, -, dC⟩ :=
    hfr l (by omega)
  rw [if_neg (by omega : ¬ l = 24)] at hlen
  rw [hlen] at iC
  obtain ⟨Lk', f', bL', -, -, -, -, hf', -, efl', hLay', -, iL', -, dL', -⟩ :=
    hfr (l + 1) (by omega)
  have cut : ∀ n ≤ 4, ∃ t r q,
      foldBlocks 0 (c.blocksInOrder.take (14 * l + 12 + n)) (ProofFile.startS Z p) R C = .ok (t, r, q) := by
    intro n hn
    exact fold_cut (k := 14 * l + 12 + n) (4 - n)
      (by rw [show 14 * l + 12 + n + (4 - n) = 14 * (l + 1) + 2 by omega]; exact f₂)
  obtain ⟨s4, r4, q4, g4⟩ := cut 1 (by omega)
  obtain ⟨s5, r5, q5, g5⟩ := cut 2 (by omega)
  obtain ⟨s6, r6, q6, g6⟩ := cut 3 (by omega)
  obtain ⟨Lk2, pw, Q, eL2, -, -, hall⟩ := IM.close_of hS hR O l (by omega)
  obtain rfl : Lk = Lk2 := Option.some.inj (eL.symm.trans eL2)
  -- the closing
  obtain ⟨b', x, e1, e2, la⟩ := hall 1 .K10 rfl
  have ib := IM.close_numbers hS hR O (by omega : l < 25) eL e1
  rw [hlen, show 14 * l + 7 + 4 + 1 = 14 * l + 12 by omega] at ib
  -- THE ONE TURN AGAINST `tail_frame`: the closing's rounds are named
  obtain ⟨sj, c₀, gs, h1, d⟩ := fold_to_decision ib g4
  have e := Except.ok.inj (h1.symm.trans g3)
  have eR : R.drop (roundsAhead c.blocksInOrder (14 * l + 12)) = R₃ := congrArg (fun a => a.2.1) e
  rw [show sj = s from congrArg Prod.fst e, eR] at d
  have dx : x.retype.decide s ((R₃.take b'.rounds.length).map noDigest) gs = .ok s4 :=
    ((IM.yes_alone la (by intro k; cases k) s s4 _ gs).1 d).1
  obtain rfl : K9.closing Q = x := Option.some.inj e2
  obtain ⟨y, hy', hl4, -⟩ := closing_yes (C := Unit) dx hL
  -- the shutting
  obtain ⟨b5', x5, e15, e25, la5⟩ := hall 2 .K9 rfl
  have ib5 := IM.close_numbers hS hR O (by omega : l < 25) eL e15
  rw [hlen, show 14 * l + 7 + 4 + 2 = 14 * l + 12 + 1 by omega] at ib5
  obtain ⟨rs5, gs5, d5⟩ := fold_next ib5 g4 g5
  have dx5 : x5.retype.decide s4 rs5 gs5 = .ok s5 :=
    ((IM.yes_alone la5 (by intro k; cases k) s4 s5 rs5 gs5).1 d5).1
  obtain rfl : K9.shut pw (Q.piece + 1) = x5 := Option.some.inj e25
  obtain ⟨L5, hL5, e5, -⟩ := shut_gby (fun f => f) (C := Unit) pw (Q.piece + 1) s4 rs5 gs5 s5 dx5
    _ hl4
  have e5' : L5.check.frame = y.1 := e5
  -- "cleared" and "laid"
  have iC' : c.blocksInOrder[14 * l + 12 + 2]? = some bC := by
    rw [show 14 * l + 12 + 2 = 14 * l + 7 + 7 by omega]
    exact iC
  obtain ⟨rs6, gs6, d6⟩ := fold_next iC' g5 g6
  rw [dC] at d6
  have k6 := framesOf_clear hfs f (List.mem_of_getElem? hf) s5 s6 ((hClear s5 s6).1 d6).1
  have iL2 : c.blocksInOrder[14 * l + 12 + 3]? = some bL' := by
    rw [show 14 * l + 12 + 3 = 14 * (l + 1) + 1 by omega]
    exact iL'
  have f₂' : foldBlocks 0 (c.blocksInOrder.take (14 * l + 12 + 3 + 1)) (ProofFile.startS Z p) R C =
      .ok (t₂, R₂, C₂) := by
    rw [show 14 * l + 12 + 3 + 1 = 14 * (l + 1) + 2 by omega]
    exact f₂
  obtain ⟨rs7, gs7, d7⟩ := fold_next iL2 g6 f₂'
  rw [dL'] at d7
  have hl7 := ((hLay' s6 t₂).1 d7).1
  rw [efl'] at hl7
  have e7 : t₂ = s6 := (Johnson.Desc.First.Walk.Law.layFront_ok hl7).1
  exact ⟨L, Q, b'.rounds.length, y, hL, eLn, hy', by rw [e7, k6.1, live_open hL5, e5'],
    eR.symm⟩

/-- **The like at the last segment**: `closing_behind_cleared` (Returns/HeadSegment.lean), all its
clauses, with the closing's rounds named. -/
theorem cleared_frame_rounds (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (353)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀)) :
    ∃ (w : S) (Rw : List Fmt.RoundView) (Cw : List VerifiableInference.Desc.OpenedColumn) (Lw : LinkCtx)
      (Q : Close.Par) (n : Nat) (x : ReqFrame × Statement),
      foldBlocks 0 (c.blocksInOrder.take 350) (ProofFile.startS Z p) R C = .ok (w, Rw, Cw) ∧
      w.link? = some Lw ∧ Lw.link = 24 ∧
      Close.closeFrame (K9.recOf w).owed Lw.check.frame w.st (Close.entries Q)
        ((Rw.take n).map noDigest) = .ok x ∧
      t₀.check.frame = x.1 ∧ Grows x.2 t₀.st ∧ Rw = R.drop (roundsAhead c.blocksInOrder 350) := by
  obtain ⟨-, fs, hfs, hfr⟩ := IM.frame_of hS hR O
  -- "the last segment: cleared"
  obtain ⟨Lk, g, _, _, bC, eL, hlen, hg, -, -, -, hclr, -, -, -, -, -, -, iC, -, dC⟩ :=
    hfr 24 (by omega)
  rw [if_pos rfl] at hlen
  rw [hlen] at iC
  obtain ⟨u, Ru, Cu, fu⟩ := fold_back (k := 352) f₀
  obtain ⟨rsC, gsC, dc⟩ := fold_next (k := 352) iC fu f₀
  rw [dC] at dc
  have hcf := ((hclr u t₀).1 dc).1
  have hck := (framesOf_clear hfs g (List.mem_of_getElem? hg) u t₀ hcf).1
  have hgr : Grows u.st t₀.st := (framesOf_grows hfs g (List.mem_of_getElem? hg)).2.2 u t₀ hcf
  -- the shutting and the closing
  obtain ⟨Lk', q, Q, eL', -, -, hall⟩ := IM.close_of hS hR O 24 (by omega)
  obtain rfl : Lk = Lk' := Option.some.inj (eL.symm.trans eL')
  obtain ⟨b₂, x₂, a1, a2, la₂⟩ := hall 2 .K9 rfl
  have j₂ := IM.close_numbers hS hR O (by omega : 24 < 25) eL a1
  have i₂ := j₂
  rw [hlen] at i₂
  rw [show 14 * 24 + Lk.hear.length + 4 + 2 = 14 * 24 + Lk.hear.length + 6 by omega] at j₂
  obtain ⟨v, Rv, Cv, fv⟩ := fold_back (k := 351) fu
  obtain ⟨rs₂, gs₂, d₂⟩ := fold_next (k := 351) i₂ fv fu
  have dx₂ : x₂.retype.decide v rs₂ gs₂ = .ok u :=
    ((IM.yes_alone la₂ (by intro k; cases k) v u rs₂ gs₂).1 d₂).1
  obtain rfl : K9.shut q (Q.piece + 1) = x₂ := Option.some.inj a2
  have est := shut_st (C := Unit) q (Q.piece + 1) v rs₂ gs₂ u dx₂
  obtain ⟨b₁, x₁, c1, c2, la₁⟩ := hall 1 .K10 rfl
  have i₁ := IM.close_numbers hS hR O (by omega : 24 < 25) eL c1
  rw [hlen] at i₁
  obtain ⟨w, Rw, Cw, fw⟩ := fold_back (k := 350) fv
  -- THE ONE TURN AGAINST `closing_behind_cleared`: the closing's rounds are named
  obtain ⟨sj, c₀, gs₁, h1, d₁⟩ := fold_to_decision (j := 350) i₁ fv
  have e := Except.ok.inj (h1.symm.trans fw)
  have eR : R.drop (roundsAhead c.blocksInOrder 350) = Rw := congrArg (fun a => a.2.1) e
  rw [show sj = w from congrArg Prod.fst e, eR] at d₁
  have dx₁ : x₁.retype.decide w ((Rw.take b₁.rounds.length).map noDigest) gs₁ = .ok v :=
    ((IM.yes_alone la₁ (by intro k; cases k) w v _ gs₁).1 d₁).1
  obtain rfl : K9.closing Q = x₁ := Option.some.inj c2
  -- in front of the closing the segment is open
  obtain ⟨t₂, R₂, C₂, f₂⟩ := fold_cut (k := 340) 10 fw
  obtain ⟨t₁, R₁, C₁, f₁⟩ := fold_back (k := 339) f₂
  obtain ⟨t₃, r₃, c₃, g₃⟩ := fold_cut (k := 340 + 2) 8 fw
  obtain ⟨t₅, r₅, c₅, g₅⟩ := fold_cut (k := 340 + 4) 6 fw
  obtain ⟨_, f', -, -, H, -⟩ := entry_head_frame hS hR O f₁ f₂
  obtain ⟨Lw, hLw, -, hLl⟩ := (frame_walk_head hS hR O (n₃ := t₃.st.oracles.size)
    (n₅ := t₅.st.oracles.size) (fun t r q h => by rw [g₃] at h; cases h; rfl)
    (fun t r q h => by rw [g₅] at h; cases h; rfl) f₂ H).1 10 (by omega) w Rw Cw fw
  obtain ⟨x, hx, hv, hvst⟩ := closing_yes (C := Unit) dx₁ hLw
  have Hv : Opn 24 x.1 v := ⟨_, hv, rfl, hLl⟩
  obtain ⟨Lu, hLu, hLuf, -⟩ := shutting_opn hS hR O (by omega : 24 < 25) eL j₂ d₂ Hv
  refine ⟨w, Rw, Cw, Lw, Q, b₁.rounds.length, x, fw, hLw, hLl, hx, ?_, ?_, eR.symm⟩
  · rw [hck]
    unfold S.live
    rw [hLu]
    exact hLuf
  · rw [← hvst, ← est]
    exact hgr

/-- **THE CARRIED ROWS' CHALLENGES, OFF THE RUN's ROUNDS**, behind "laid" of the next segment. -/
theorem gamma_behind_laid (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {l : Nat} (h24 : l < 24)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * (l + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀)) :
    t₀.check.frame.rows.gamma =
      ((R.drop (roundsAhead c.blocksInOrder (14 * l + 12) + 2)).take t₀.check.frame.rows.gamma.length).map
        drawnOf := by
  obtain ⟨s, R₃, C₃, g3⟩ := fold_cut (k := 14 * l + 12) 4
    (by rw [show 14 * l + 12 + 4 = 14 * (l + 1) + 2 by omega]; exact f₀)
  obtain ⟨L, Q, n, y, -, -, hy, hf, hR₃⟩ := tail_frame_rounds hS hR O h24 g3 f₀
  have h := gamma_list (gamma_of_close hy)
  rw [← hf, hR₃, List.drop_drop] at h
  exact h

/-- **The like behind "cleared" of the last segment.** -/
theorem gamma_behind_cleared (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (353)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀)) :
    t₀.check.frame.rows.gamma =
      ((R.drop (roundsAhead c.blocksInOrder 350 + 2)).take t₀.check.frame.rows.gamma.length).map
        drawnOf := by
  obtain ⟨w, Rw, Cw, Lw, Q, n, x, -, -, -, hx, hf, -, hRw⟩ := cleared_frame_rounds hS hR O f₀
  have h := gamma_list (gamma_of_close hx)
  rw [← hf, hRw, List.drop_drop] at h
  exact h

/-- **AT THE FRONT THAT THE SWITCH's BLOCK TAKES OFF THE STATE**, at a segment's first place: the
closed segment is number m. -/
theorem link_gamma_front (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {m : Nat} (h23 : m < 23)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take (14 * (m + 1) + 2)) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    {q : K2.P2} (hq : q.stands = .link) {fx : _root_.Tw.K2.Front}
    (hfx : K2.frontAt q t₀ = some fx) :
    fx.f.rows.gamma =
      ((R.drop (roundsAhead c.blocksInOrder (14 * m + 12) + 2)).take fx.f.rows.gamma.length).map
        drawnOf := by
  obtain ⟨-, -, -, -, -, a6, -⟩ :=
    front_pin_link hS hR O (l := m + 1) (by omega) (by omega) f₀ hq hfx
  rw [a6]
  exact gamma_behind_laid hS hR O (by omega) f₀

/-- **At the output head's front** (339): the closed segment is number 23. -/
theorem head_gamma_front (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 339) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    {q : K2.P2} (hq : q.stands = .head) {fx : _root_.Tw.K2.Front}
    (hfx : K2.frontAt q t₀ = some fx) :
    fx.f.rows.gamma =
      ((R.drop (roundsAhead c.blocksInOrder 334 + 2)).take fx.f.rows.gamma.length).map drawnOf := by
  obtain ⟨tm, Rm, Cm, fm⟩ := fold_back (k := 338) f₀
  obtain ⟨-, -, a3, -⟩ := front_nums_head hS hR O fm f₀ hq hfx
  rw [a3]
  exact gamma_behind_laid hS hR O (l := 23) (by omega) fm

/-- **At the front behind the last segment** (353, behind its quiet step in front): the closed
segment is number 24. -/
theorem fin_gamma_front (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {p : ProofFile.InstPub} {R R₀ : List Fmt.RoundView} {C C₀ : List VerifiableInference.Desc.OpenedColumn} {t₀ t : S}
    (f₀ : foldBlocks 0 (c.blocksInOrder.take 353) (ProofFile.startS Z p) R C = .ok (t₀, R₀, C₀))
    (he : K2.finishFrontQ t₀ = .ok t) {q : K2.P2} (hq : q.stands = .finish)
    {fx : _root_.Tw.K2.Front} (hfx : K2.frontAt q t = some fx) :
    fx.f.rows.gamma =
      ((R.drop (roundsAhead c.blocksInOrder 350 + 2)).take fx.f.rows.gamma.length).map drawnOf := by
  obtain ⟨-, -, a3, -⟩ := front_nums_fin hS hR O f₀ he hq hfx
  rw [a3]
  exact gamma_behind_cleared hS hR O f₀

end

end VerifiableInference.Desc.K2.Honest.Returns

#print axioms VerifiableInference.Desc.K2.Honest.Returns.gamma_of_close
#print axioms VerifiableInference.Desc.K2.Honest.Returns.take_own_length
#print axioms VerifiableInference.Desc.K2.Honest.Returns.gamma_list
#print axioms VerifiableInference.Desc.K2.Honest.Returns.tail_frame_rounds
#print axioms VerifiableInference.Desc.K2.Honest.Returns.cleared_frame_rounds
#print axioms VerifiableInference.Desc.K2.Honest.Returns.gamma_behind_laid
#print axioms VerifiableInference.Desc.K2.Honest.Returns.gamma_behind_cleared
#print axioms VerifiableInference.Desc.K2.Honest.Returns.link_gamma_front
#print axioms VerifiableInference.Desc.K2.Honest.Returns.head_gamma_front
#print axioms VerifiableInference.Desc.K2.Honest.Returns.fin_gamma_front
