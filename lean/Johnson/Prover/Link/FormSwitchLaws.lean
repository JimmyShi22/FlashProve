-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormSwitchLaws.lean: the form's half at a code switch of the proximity test and
at the batching behind it: the description's two parts return ok, with the record behind as a term.

Main names (namespace `Johnson.Prover.Link`).
  `swNotices_eq`, `swIds_zero`   the announcements are the new message's and the others'; the new
      message has the next free number
  `front_of_facts`   `SwitchFacts` gives `SwitchFront`
  `did_of_front`   the two fronts give the soundness side's record `Did`, at some letters D' whose
      rounds, answer and factor are the front's
  `switch5_yes`   `SwitchFront` (Johnson/Prover/Link/FormSwitch.lean): then
      (guardedProximityTestParts.switch p j cur next last [dS, dC]).decide t [rS, rC] gs = .ok (switchT …)
  `behind5_yes`   `BehindFront`: then
      (guardedProximityTestParts.batBehind p (j + 1) next [dS, dC]).decide (switchT …) [] [] = .ok (behindT …)

By: `sendOne_yes` (Johnson/Prover/Link/FormSend.lean), `loc_yes`, `behind_yes`
(Johnson/Prover/Link/FormSwitchBehind.lean); `joinS_ok`, `addRowsS_ok`, `switchUnfolds`
(Johnson/Desc/K12/Law/SwUnfold.lean).

Limits. `SwitchFacts` and `BehindFront` are asked, not shown here. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormSwitch
import Johnson.Prover.Link.FormSend
import Johnson.Prover.Link.FormSwitchBehind
import Johnson.Prover.Link.BasePart

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw

variable (p : P12) (n : IoppStage) (last : Bool) (dS dC : Fmt.DeclaredRound) (t : T12)
  (rS rC : Fmt.RoundView) (gs : List (List (Nat × List UInt64))) (rows : SingleRows) (gp : Nat)
  (D : Taken)

/-- The announcements: the new message's, then the others'. -/
theorem swNotices_eq : swNotices p n last =
    #[(⟨(swTarget p n).shape, (swTarget p n).leafClass⟩ : OracleNotice)] ++ othersOf last n := by
  unfold swNotices Tw.L9.switchNotices
  rw [show (swTarget p n).kept = #[] from rfl]
  simp

/-- The new message has the next free number. -/
theorem swIds_zero : (swIds p n last t).getD 0 noId = t.st.oracles.size := by
  unfold swIds
  rw [swNotices_eq]
  have h0 : (Array.range (#[(⟨(swTarget p n).shape, (swTarget p n).leafClass⟩ : OracleNotice)] ++
      othersOf last n).size)[0]? = some 0 := by
    rw [Array.getElem?_eq_getElem (by simp)]
    simp
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_map, h0]
  simp

variable {p n last dS dC t rS rC gs rows gp D}

/-- What `switchCut` says, clause by clause. -/
theorem switchCut_says {logN : Nat} (h : switchCut logN dS dC = true) :
    dS.entry.name = "SEND seed" ∧ dS.entry.drawNZ = 1 ∧ dS.entry.rows = 0 ∧ dS.entry.poss = 0 ∧
      dS.entry.trits = 0 ∧ dS.items.filter (· != .root) = [] ∧ dC.entry.name = "CS" ∧
      dC.entry.drawE = 1 ∧ dC.entry.drawNZ = 0 ∧ dC.entry.logN = logN ∧ 0 < dC.entry.poss ∧
      dC.entry.trits = 0 ∧ dC.items.filter (· != .root) = [.answer] ∧
      dS.stored.isEmpty = true ∧ dC.stored.isEmpty = true := by
  unfold switchCut at h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩, a13⟩, a14⟩,
    a15⟩ := h
  exact ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15⟩

/-- What `roundsFit` says of two rounds' numbers. -/
theorem fit_says (h : roundsFit [dS, dC] [rS, rC] = true) :
    (rS.vals.map itemOf = dS.items.filter (· != .root) ∧
      rS.drawn.elems.length = dS.entry.drawE ∧ rS.drawn.poss.length = dS.entry.poss ∧
      rS.drawn.trits.length = dS.entry.trits) ∧
    (rC.drawn.elems.length = dC.entry.drawE ∧ rC.drawn.poss.length = dC.entry.poss ∧
      rC.drawn.trits.length = dC.entry.trits ∧
      rC.drawn.poss.all (· < 2 ^ dC.entry.logN) = true) ∧
    rS.drawn.poss.all (· < 2 ^ dS.entry.logN) = true := by
  simp only [roundsFit, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, -⟩, -⟩, ⟨⟨⟨⟨⟨⟨-, b2⟩, b3⟩, b4⟩, b5⟩, -⟩, -⟩, -⟩ := h
  exact ⟨⟨a1, a2, a3, a4⟩, ⟨b2, b3, b4, b5⟩, a5⟩

/-- The greatest number of answers among the announcements is one. -/
theorem nz_one (h1 : p.answers = 1) :
    (Tw.L9.switchNotices (swTarget p n) (othersOf last n)).foldl
      (fun a x => max a x.shape.answers) 0 = 1 := by
  have e := swNotices_eq p n last
  unfold swNotices at e
  rw [e]
  have hN : (swTarget p n).shape.answers = 1 := h1
  cases last
  · simp only [othersOf]
    simp [hN]
    exact Nat.zero_le 1
  · simp only [othersOf]
    simp [hN]
    exact Nat.zero_le 1

/-- **The sending at a switch.** -/
theorem swSend_yes {j : Nat} {next : Fmt.M1.Stage} {B : TreeBook} {x : Fmt.Ext}
    (F : SwitchFront p n last dS dC t rS rC gs rows gp D j next B x) :
    Desc.Plain.sendP Ground.groundG { samples := p.answers, firstTree := p.nums.firstTree } false
      (swD0 p dS dC t gs) (Tw.L9.switchNotices (swTarget p n) (othersOf last n)) rS rC =
      some (swIds p n last t, rS.drawn.elems.map E.ofTriple, [D.alpha], 1,
        swD2 p n last dS dC t gs D) := by
  obtain ⟨-, -, -, c4, c5, c6, -⟩ := switchCut_says F.cut
  obtain ⟨⟨f1, -, f3, f4⟩, -, -⟩ := fit_says F.fit
  have e := swNotices_eq p n last
  have hv : rS.vals = [] := by
    rw [c6] at f1
    exact List.map_eq_nil_iff.1 f1
  have hp : rS.drawn.poss = [] := List.eq_nil_of_length_eq_zero (f3.trans c4)
  have ht : rS.drawn.trits = [] := List.eq_nil_of_length_eq_zero (f4.trans c5)
  have h := sendOne_yes { samples := p.answers, firstTree := p.nums.firstTree }
    (swD0 p dS dC t gs) ⟨(swTarget p n).shape, (swTarget p n).leafClass⟩ (othersOf last n) rS rC
    D.lay D.beta D.alpha D.smp D.places [] F.one (othersOf_none last n)
    (by rw [← e]; exact F.recv) (by rw [← e]; exact F.trees) hv hp ht F.seed F.factor F.form F.pad
    F.ans (by rw [← e]; exact F.admit)
  unfold swNotices at e
  rw [e, h]
  unfold swIds swNotices
  rw [e]
  rfl

/-- **The step behind the sending, at a switch.** -/
theorem swBehind_yes {j : Nat} {next : Fmt.M1.Stage} {B : TreeBook} {x : Fmt.Ext}
    (F : SwitchFront p n last dS dC t rS rC gs rows gp D j next B x) :
    Tw.L9.switchBehind (swIn p n last dS dC t rC gs rows gp D) =
      .ok ⟨D.stR (swTarget p n) gp (othersOf last n) t.st, B, [], swOut p n last t rC D⟩ := by
  obtain ⟨-, -, -, -, -, -, -, -, c9, c10, c11, c12, -⟩ := switchCut_says F.cut
  obtain ⟨-, ⟨-, g3, g4, -⟩, -⟩ := fit_says F.fit
  have hg := swIds_zero p n last t
  have hloc : Tw.L9.locPositions (swIn p n last dS dC t rC gs rows gp D) D.code.logN =
      .ok (swPos rC D) :=
    loc_yes _ _ rfl c9 rfl (by
      show rC.vals.length - 1 = 0
      rw [F.ans]
      rfl) rfl g3 g4 c10 c11 rfl
  have hsize : t.st.oracles.size <
      (D.stA (swTarget p n) (othersOf last n) t.st).oracles.size := by
    unfold Taken.stA admitted stSent OnBytes.Slice.sentOf
    simp
    omega
  have h := behind_yes (swIn p n last dS dC t rC gs rows gp D) D.code (swPos rC D) B [] D.y
    (D.stJ (swTarget p n) gp (othersOf last n) t.st)
    (D.stR (swTarget p n) gp (othersOf last n) t.st) rfl F.code hloc F.read
    (Nat.two_pow_pos n.h)
    (by
      show (swIds p n last t).getD 0 noId < _
      rw [hg]
      exact hsize)
    (by
      show Tw.L9.joinS (ledgerShut _ _ ((swIds p n last t).getD 0 noId)) gp
        ((swIds p n last t).getD 0 noId) false = _
      rw [hg]
      exact F.join)
    F.fresh F.can
    (by
      show ((Own.swRows _ rows (swTarget p n) ((swIds p n last t).getD 0 noId) #[] (swPos rC D)
        D.y).getD []).foldlM _ _ = _
      rw [hg, ← F.made]
      exact F.add)
  exact h

/-- **The switch inside a test returns ok.** -/
theorem switchE_yes {j : Nat} {next : Fmt.M1.Stage} {B : TreeBook} {x : Fmt.Ext}
    (F : SwitchFront p n last dS dC t rS rC gs rows gp D j next B x) :
    H2K.switchE rows (swTarget p n) gp (othersOf last n) true
      (lay p [dS, dC] none t [rS, rC] gs) =
      .ok ((swOut p n last t rC D, E.ofTriple x),
        { lay p [dS, dC] none t [rS, rC] gs with
          d := { swD2 p n last dS dC t gs D with
            st := D.stR (swTarget p n) gp (othersOf last n) t.st, book := B, opened := [] }
          entries := [], rounds := [], last := some dC.entry, asked := false }) := by
  obtain ⟨c1, c2, c3, -, -, -, c7, c8, -⟩ := switchCut_says F.cut
  obtain ⟨⟨-, f2, f3, f4⟩, -, -⟩ := fit_says F.fit
  have hs := swSend_yes F
  have hb := swBehind_yes F
  have hfit : H2K.fitsE dS.entry rS = true := by
    unfold H2K.fitsE
    simp [f2, f3, f4]
  unfold H2K.switchE
  simp only [lay, List.map_cons, List.map_nil, H2K.need, H2K.opt, H2K.PS.owed, nz_one F.one,
    F.guard, c1, c2, c3, c7, c8, hfit, Option.isNone_none, beq_self_eq_true, if_true, bind,
    Except.bind, pure, Except.pure]
  have hs' := hs
  unfold swD0 at hs'
  rw [hs']
  simp only [F.elem]
  have hb' := hb
  unfold swIn at hb'
  simp only [swD2] at hb' ⊢
  rw [hb']
  rfl

/-- The switch's plain part returns the record behind it. -/
theorem switchJ_yes {j : Nat} {next : Fmt.M1.Stage} {B : TreeBook} {x : Fmt.Ext}
    (cur : Fmt.M1.Stage) (F : SwitchFront p n last dS dC t rS rC gs rows gp D j next B x) :
    (switchJ p j cur next last [dS, dC]).decide t [rS, rC] gs =
      .ok (switchT p n last t rC gp D B (E.ofTriple x)) := by
  have hoth : (if (!p.early) = true then (#[] : Array OracleNotice)
      else if last = true then #[baseMaskNotice n.code n.maskCode 1 0]
      else #[foldMaskNotice (ioppFoldShape n {})]) = othersOf last n := by
    rw [F.early]
    rfl
  simp only [switchJ, F.pass, F.stage]
  rw [hoth, show switchTargetStage n.code n.maskCode n.k n.h p.answers = swTarget p n from rfl,
    switchE_yes F]
  rfl

/-- **The switch's part of the kind's block returns the record behind it.** -/
theorem switch5_yes {j : Nat} {next : Fmt.M1.Stage} {B : TreeBook} {x : Fmt.Ext}
    (cur : Fmt.M1.Stage) (F : SwitchFront p n last dS dC t rS rC gs rows gp D j next B x) :
    (guardedProximityTestParts.switch p j cur next last [dS, dC]).decide t [rS, rC] gs =
      .ok (switchT p n last t rC gp D B (E.ofTriple x)) := by
  obtain ⟨-, ⟨-, -, -, g5⟩, f5⟩ := fit_says F.fit
  have hz : inRange [dS, dC] [rS, rC] = true := by
    unfold inRange
    simp only [List.zip_cons_cons, List.zip_nil_left, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true]
    exact ⟨f5, g5⟩
  show (ranged [dS, dC] (switchJ p j cur next last [dS, dC])).decide t [rS, rC] gs = _
  rw [ranged_yes _ _ _ _ _ hz]
  exact switchJ_yes cur F

/-- **The batching behind the switch returns the record behind it.** -/
theorem behind5_yes {theta : E} {row : GroupRow} {lay : GroupLayout} (dS : Fmt.DeclaredRound)
    (rC : Fmt.RoundView) (j : Nat) (next : Fmt.M1.Stage) (B : TreeBook)
    (F : BehindFront p n last dC t gp D theta row lay) :
    (guardedProximityTestParts.batBehind p (j + 1) next [dS, dC]).decide (switchT p n last t rC gp D B theta) [] [] =
      .ok (behindT p n last t rC gp D B row lay) := by
  have hne : (dC.entry.rows == 0) = false := by
    simpa using F.counts
  show (behindJ p (j + 1) next [dS, dC]).decide (switchT p n last t rC gp D B theta) [] [] = _
  simp only [behindJ, switchT, Test.csTest, H2K.csParts, H2K.beginRunE, H2K.askOwedE, H2K.PS.owed,
    H2K.opt, K12.lay, Ground.beginRunP, F.begin, F.group, F.layout, F.batch, F.early, hne,
    ← F.count, List.getLast?_cons_cons, List.getLast?_singleton, Option.map_some, if_true, bind,
    Option.bind, Except.bind, Except.map, Except.toOption, named, Bool.false_or,
    Bool.false_eq_true, if_false, beq_self_eq_true]
  rfl

/-- A bare yes, as a value. -/
theorem ok_of_isSome {α : Type} {e : Except String α} (h : e.toOption.isSome = true) :
    ∃ a, e = .ok a := by
  cases e with
  | error _ => cases h
  | ok a => exact ⟨a, rfl⟩

/-- **The lighter record gives the front**: the soundness side's own lemmas turn the two bare yeses
into the equations. -/
theorem front_of_facts {j : Nat} {next : Fmt.M1.Stage} {B : TreeBook} {x : Fmt.Ext}
    (F : SwitchFacts p n last dS dC t rS rC gs rows gp D j next B x) :
    SwitchFront p n last dS dC t rS rC gs rows gp D j next B x := by
  obtain ⟨S2, h2⟩ := ok_of_isSome F.joinOk
  obtain ⟨G, hG, hrun, rfl⟩ := joinS_ok h2
  obtain rfl : G = D.G := Option.some.inj (hG.symm.trans F.group)
  obtain ⟨S4, h4⟩ := ok_of_isSome F.addOk
  obtain ⟨-, rfl⟩ := addRowsS_ok gp D.rows _ _ h4
  exact
    { pass := F.pass, stage := F.stage, early := F.early, one := F.one, guard := F.guard
      cut := F.cut, fit := F.fit, recv := F.recv, trees := F.trees, seed := F.seed
      factor := F.factor, form := F.form, pad := F.pad, ans := F.ans, admit := F.admit
      elem := F.elem, code := F.code, read := F.read, join := h2
      fresh := ⟨_, joined_group _ gp _ false D.G F.group, hrun⟩
      can := F.can, made := F.made, add := h4 }

/-- **What the switch and the batching have done, in the soundness side's record**, with what
its letters read off the two rounds. -/
theorem did_of_front {j : Nat} {next : Fmt.M1.Stage} {B : TreeBook} {x : Fmt.Ext} {row : GroupRow}
    {lay : GroupLayout} (cur : Fmt.M1.Stage)
    (F : SwitchFront p n last dS dC t rS rC gs rows gp D j next B x)
    (F' : BehindFront p n last dC t gp D (E.ofTriple x) row lay) :
    ∃ (out : Switched) (D' : Taken), D'.rS = rS ∧ D'.rC = rC ∧ D'.alpha = D.alpha ∧
      D'.beta = D.beta ∧
      Did p.nums.firstTree (keyed p [dS, dC] gs) rows
        (switchTargetStage n.code n.maskCode n.k n.h 1) gp (othersOf last n) t.st t.book t.roots
        (behindT p n last t rC gp D B row lay).st (behindT p n last t rC gp D B row lay).book out
        row lay (E.ofTriple x) D' := by
  obtain ⟨out, row', lay', theta, D', e1, e2, hd, hp, -⟩ :=
    switchUnfolds p j cur next last [dS, dC] t _ _ rS rC gs rows gp n F.early F.one F.pass F.stage
      (switchJ_yes cur F) (behind5_yes dS rC j next B F')
  have hp' : Passing.claim row lay = Passing.claim row' lay' := hp
  injection hp' with r1 r2
  subst r1 r2
  have hth : theta = E.ofTriple x := by
    have k := hd.elem
    rw [e2, F.elem] at k
    exact (List.head_eq_of_cons_eq k).symm
  subst hth
  have ha : D'.alpha = D.alpha := by
    have k := hd.valsC
    rw [e2, F.ans] at k
    have k2 : D.alpha.triple = D'.alpha.triple := by
      injection k with k1 _
      injection k1
    rw [← E.ofTriple_triple D'.alpha, ← k2, E.ofTriple_triple]
  have hb : D'.beta = D.beta := by
    have k := hd.seed
    rw [e1] at k
    have k2 := F.seed
    rw [show (swTarget p n) = switchTargetStage n.code n.maskCode n.k n.h 1 by
      unfold swTarget
      rw [F.one]] at k2
    exact (List.head_eq_of_cons_eq (k.symm.trans k2))
  exact ⟨out, D', e1, e2, ha, hb, hd⟩

end Johnson.Prover.Link
