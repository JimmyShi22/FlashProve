-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormStep.lean: one stage of a proximity test that is not the last, on the form's
side: from the plan, the carried record and the rounds' form, the description's three parts (the
fold, the switch, the batching behind it) say yes and leave written records.

Main names (namespace `Johnson.Prover.Link`).
  `stepB`, `stepL`, `stepT3`   the book behind the reading of the old tree · the new group's layout
      · the record behind the batching: terms in the letters D and the batched row
  `StepDone`   what a switch and its batching have delivered, in one record: the two parts'
      equations · the next mask has come · `SwitchFront`, `BehindFront` and the soundness side's
      `Did` at the same letters D · D's two rounds, answer and group · what is public of the old
      rows · the statement in order behind the switch and behind the batching
  `switch_step`   `StepDone` for some D, drawn element and row, at a record in front of a switch
  `form_step`   `StepPlan` (Johnson/Prover/Link/FormStepPlan.lean) · `FormInv`
      (Johnson/Prover/Link/FormInv.lean) · the rounds fit the two cuts · "CS" shows an answer · the
      old tree can be read behind the fold (`ReadFront`): then the fold's equation, and `StepDone`
      at the record behind the fold

Limits. Every premise is asked; that the old tree can be read is a premise here. Nothing on
soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormBehind
import Johnson.Prover.Link.FormStepPlan
import Johnson.Prover.Link.FormInv
import Johnson.Prover.Link.SwitchLaw
import Johnson.Prover.Link.FixEntries
import Johnson.Desc.Sound.Gather
import Johnson.Prover.Link.FoldCutLen

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw
open H2K.Pub (sgOf)

section Terms
variable (p : P12) (n : IoppStage) (last : Bool) (dS dC : Fmt.DeclaredRound) (t : T12) (rC : Fmt.RoundView)
  (gs : List (List (ℕ × List UInt64))) (rows : SingleRows) (gp : ℕ) (D : Taken) (tN : ℕ)

/-- The book behind the reading of the old tree. -/
def stepB : TreeBook := bookRead (swIn p n last dS dC t rC gs rows gp D).book tN

/-- The new group's layout. -/
def stepL : GroupLayout :=
  Own.layoutOf (D.stR (swTarget p n) gp (othersOf last n) t.st) (D.grown t.st)

/-- The record behind the batching. -/
def stepT3 (row' : GroupRow) : T12 :=
  behindT p n last t rC gp D (stepB p n last dS dC t rC gs rows gp D tN) row'
    (stepL p n last t gp D)

end Terms

/-- **What a switch and its batching have delivered.** -/
structure StepDone (s s' : Sg) (p : P12) (n : IoppStage) (last : Bool) (dS dC : Fmt.DeclaredRound)
    (t : T12) (rS rC : Fmt.RoundView) (gs : List (List (ℕ × List UInt64))) (rows : SingleRows) (gp : ℕ)
    (j : ℕ) (cur next : Fmt.M1.Stage) (tN : ℕ) (a : Fmt.Ext) (D : Taken) (x : Fmt.Ext)
    (row' : GroupRow) : Prop where
  switch : (guardedProximityTestParts.switch p j cur next last [dS, dC]).decide t [rS, rC] gs =
    .ok (switchT p n last t rC gp D (stepB p n last dS dC t rC gs rows gp D tN) (E.ofTriple x))
  behind : (guardedProximityTestParts.batBehind p (j + 1) next [dS, dC]).decide
    (switchT p n last t rC gp D (stepB p n last dS dC t rC gs rows gp D tN) (E.ofTriple x)) [] [] =
    .ok (stepT3 p n last dS dC t rC gs rows gp D tN row')
  came : (!p.early || guardedProximityTestParts.maskCame (stepT3 p n last dS dC t rC gs rows gp D tN row')) = true
  front : SwitchFront p n last dS dC t rS rC gs rows gp D j next
    (stepB p n last dS dC t rC gs rows gp D tN) x
  bfront : BehindFront p n last dC t gp D (E.ofTriple x) row' (stepL p n last t gp D)
  did : Did p.nums.firstTree (keyed p [dS, dC] gs) rows (swTarget p n) gp (othersOf last n) t.st
    t.book t.roots (stepT3 p n last dS dC t rC gs rows gp D tN row').st
    (stepB p n last dS dC t rC gs rows gp D tN) (swOut p n last t rC D) row'
    (stepL p n last t gp D) (E.ofTriple x) D
  isS : D.rS = rS
  isC : D.rC = rC
  alpha : D.alpha = E.ofTriple a
  G : D.G = { code := n.code, maskCode := n.maskCode }
  ff : FoldedFit s s' t.st.codes n.code n.maskCode rows
  dense : DenseForm rows.c
  orderR : Means.InOrder (D.stR (swTarget p n) gp (othersOf last n) t.st)
  order : Means.InOrder (stepT3 p n last dS dC t rC gs rows gp D tN row').st

/-- **A switch and its batching**, at a record in front of the switch. -/
theorem switch_step {s s' : Sg} (hf : CsFit s s') {p : P12} {n : IoppStage} {last : Bool}
    {dS dC : Fmt.DeclaredRound} {t : T12} {rS rC : Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    {rows : SingleRows} {gp j : ℕ} (cur : Fmt.M1.Stage) {next : Fmt.M1.Stage}
    (hpass : t.pass = .single rows gp) (hstage : stageAt p (j + 1) next = some n)
    (hearly : p.early = true) (hone : p.answers = 1) (hnk : n.k = s'.h + s'.g) (hnh : n.h = s'.h)
    (ff : FoldedFit s s' t.st.codes n.code n.maskCode rows)
    (hc : Means.CFits (ceilLog2 s.C.l) rows.c) (hp : DenseForm rows.c)
    (hcut : switchCut s.C.a dS dC = true) (hfit : roundsFit [dS, dC] [rS, rC] = true)
    (hdrawE : dS.entry.drawE = (Send.cube t.st.codes (swTarget p n).shape).bits + 1)
    (hcount : dC.entry.rows = 2 + 3 * dC.entry.poss)
    (htrees : Own.treesCan t.st.codes (swNotices p n last) = true)
    (hstep : t.st.oracles.size = t.book.place.size)
    (hG : t.st.groups[gp]? = some { code := n.code, maskCode := n.maskCode })
    (hO : Means.InOrder t.st) (hl : t.st.codes.lengthsOk = true)
    (a : Fmt.Ext) (hans : rC.vals = [.answer a])
    (hsmall : 2 ^ (s'.h + s'.g) * s'.C.l ≤ 2 ^ 63 ∧ 2 ^ s'.h * s'.Z.l ≤ 2 ^ 63) (tN : ℕ)
    (tr : Tree)
    (hread : ∀ D : Taken, ReadFront (swIn p n last dS dC t rC gs rows gp D)
      (Positions.ofDraws s.C.a rC.drawn.poss) tN tr) :
    ∃ D x row', StepDone s s' p n last dS dC t rS rC gs rows gp j cur next tN a D x row' := by
  obtain ⟨D, x, F, hα, hDG, hrS, hrC⟩ := switchFacts_of hf hpass hstage hearly hone hnk hnh ff hc hp
    hcut hfit hdrawE htrees hstep hG a hans hsmall tN tr hread
  obtain ⟨row', F', hd, hR, hB⟩ := behind_paid F ff hO hl hDG hrS hrC hcount
  have hmask : (behindT p n last t rC gp D (stepB p n last dS dC t rC gs rows gp D tN) row'
      (stepL p n last t gp D)).mask = some (t.st.oracles.size + 1) :=
    did_mask hd (by cases last <;> rfl)
  exact ⟨D, x, row',
    { switch := switch5_yes cur (front_of_facts F)
      behind := behind5_yes dS rC j next _ F'
      came := by
        show (!p.early || (behindT p n last t rC gp D _ row' _).mask.isSome) = true
        rw [hmask]
        simp
      front := front_of_facts F, bfront := F', did := hd, isS := hrS, isC := hrC, alpha := hα
      G := hDG, ff := ff, dense := hp, orderR := hR, order := hB }⟩

/-- **One stage that is not the last, on the form's side.** -/
theorem form_step {p : P12} {j : ℕ} {cur next : Fmt.M1.Stage} {last : Bool} {l : Laid}
    {c n : IoppStage} {dS dC : Fmt.DeclaredRound} {t : T12} {col : ℕ → List UInt64} {row : GroupRow}
    {L : GroupLayout} {id tN : ℕ} {tr : Tree}
    (Pl : StepPlan p t.st.codes j cur next last l c n dS dC)
    (I : FormInv p j cur l t col row L c (n.code, n.maskCode) id tN tr) (rsF : List Fmt.RoundView)
    (fitF : roundsFit ((l.take (1 + cur.k)).map (·.1)) rsF = true) (rS rC : Fmt.RoundView)
    (fitS : roundsFit [dS, dC] [rS, rC] = true) (a : Fmt.Ext) (hans : rC.vals = [.answer a])
    (gs : List (List (ℕ × List UInt64)))
    (hread : ∀ D : Taken, ReadFront
      (swIn p n last dS dC (foldT t row L c (n.code, n.maskCode) id (rsF.map noDigest)) rC gs
        (foldOut t row L c id (rsF.map noDigest)) t.st.groups.size D)
      (Positions.ofDraws (sgOf cur).C.a rC.drawn.poss) tN tr) :
    (guardedProximityTestParts.fold p j cur ((l.take (1 + cur.k)).map (·.1))).decide t (rsF.map noDigest) [] =
        .ok (foldT t row L c (n.code, n.maskCode) id (rsF.map noDigest)) ∧
      ∃ D x row', StepDone (sgOf cur) (sgOf next) p n last dS dC
        (foldT t row L c (n.code, n.maskCode) id (rsF.map noDigest)) rS rC gs
        (foldOut t row L c id (rsF.map noDigest)) t.st.groups.size j cur next tN a D x row' := by
  refine ⟨fold5_yes I.front Pl.cutF rsF fitF, ?_⟩
  have hlen : (rsF.map noDigest).length = 1 + c.k := by
    rw [List.length_map, Sound.roundsFit_len _ _ fitF, length_of_foldCut Pl.cutF]
  obtain ⟨rE, rR, hrs⟩ : ∃ rE rR, rsF.map noDigest = rE :: rR := by
    cases h : rsF.map noDigest with
    | nil => rw [h] at hlen; simp at hlen; omega
    | cons rE rR => exact ⟨rE, rR, rfl⟩
  have hR : rR.length = c.k := by
    rw [hrs, List.length_cons] at hlen
    omega
  rw [hrs] at hread ⊢
  have ff := foldedFit_of_front p j cur t row L c (n.code, n.maskCode) id rE rR (sgOf cur)
    (sgOf next) I.front Pl.codes Pl.zk Pl.codeN Pl.zkN Pl.sized.small I.kept0 I.keptL
    (hR.trans Pl.codes.k)
  obtain ⟨cd, hcd, ecd⟩ := Pl.codes.base
  have hc : Means.CFits (ceilLog2 (sgOf cur).C.l) (foldOut t row L c id (rE :: rR)).c := by
    have h1 := cfits_foldOutput (spent t.st id) (ioppFoldShape c L) row id (drawnOf rE)
      (rR.map drawnOf) (claimOf rR (maddE ((sentOf rE).getD 0 zeroE) (drawnOf rE) row.target))
      (by rw [List.length_map]; exact hR)
      ((Own.foldRowFits_agrees _ _ _).trans ((foldRowFits_spent _ _ _ _).trans I.front.rowFits))
    have e : ((spent t.st id).codes.base.getD (ioppFoldShape c L).code default).ell =
        (sgOf cur).C.l := by
      show (t.st.codes.base.getD c.code default).ell = _
      rw [Array.getD_eq_getD_getElem?, hcd]
      exact congrArg (·.l) ecd
    rw [e] at h1
    exact h1
  have hp : DenseForm (foldOut t row L c id (rE :: rR)).c :=
    denseForm_foldOutput (spent t.st id) (ioppFoldShape c L) row id (drawnOf rE) (rR.map drawnOf) _
      I.dense
  have hG : (foldT t row L c (n.code, n.maskCode) id (rE :: rR)).st.groups[t.st.groups.size]? =
      some { code := n.code, maskCode := n.maskCode } := by
    show (t.st.groups.push _)[t.st.groups.size]? = _
    simp
  exact switch_step (t := foldT t row L c (n.code, n.maskCode) id (rE :: rR))
    (gp := t.st.groups.size) Pl.fits cur rfl Pl.stageN Pl.early Pl.one Pl.nk Pl.nh ff hc hp
    Pl.cutSw fitS Pl.drawE (by rw [Pl.count, Pl.poss]) Pl.trees
    (step_foldT t row L c _ id _ I.step) hG (inOrder_foldT t row L c _ id _ I.order) Pl.lengths a
    hans Pl.bounds tN tr hread

end Johnson.Prover.Link
