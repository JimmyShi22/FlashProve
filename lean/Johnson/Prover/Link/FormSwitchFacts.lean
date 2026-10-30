-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormSwitchFacts.lean: the record `SwitchFacts`
(Johnson/Prover/Link/FormSwitch.lean) is met in front of a code switch between two stages of the
proximity test, from the plan, the format, the carried record and the old tree's seat.

Main names (namespace `Johnson.Prover.Link`).
  `nz_says`   `roundsFit` holds the format's test on never-0 draws at the first of two rounds
  `switchFacts_of`   the two stages fit · the record passes single rows · the next stage's numbers ·
      what is public of the old rows (`FoldedFit`, `Means.CFits`, `DenseForm`) · the plan's cut and
      its count of drawn elements · the rounds fit · the trees can be laid · statement and book are
      in step · the new group is there, empty · "CS" shows an answer · two bounds on the new
      tables · the old tree can be read (`ReadFront`, Johnson/Prover/Link/ReadFront.lean): then
      there are letters D and a drawn element x with `SwitchFacts`; the book behind the reading is
      written out, and D's answer, group and rounds are named

  `did_at`   `SwitchFacts` and `BehindFront`, at letters whose two rounds are the view's: the
      soundness side's record `Did` (Johnson/Desc/K12/Law/SwDid.lean) at the same letters

By: the payers of Johnson/Prover/Link/FormSwitchPay.lean, `addOk_of`
(Johnson/Prover/Link/SwitchSeat.lean), `read_yes` (Johnson/Prover/Link/ReadYes.lean).

Limits. Every premise is asked. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormSwitchPay
import Johnson.Prover.Link.ReadYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw

/-- The format's test on never-0 draws, at the first of two rounds. -/
theorem nz_says {dS dC : Fmt.DeclaredRound} {rS rC : Fmt.RoundView}
    (h : roundsFit [dS, dC] [rS, rC] = true) : drawsMarkedNonzeroHaveNonzeroWords dS rS = true := by
  simp only [roundsFit, Bool.and_eq_true] at h
  exact h.1.2

/-- **`SwitchFacts` is met.** -/
theorem switchFacts_of {s s' : Sg} (hf : CsFit s s') {p : P12} {n : IoppStage} {last : Bool}
    {dS dC : Fmt.DeclaredRound} {t : T12} {rS rC : Fmt.RoundView} {gs : List (List (ℕ × List UInt64))}
    {rows : SingleRows} {gp j : ℕ} {next : Fmt.M1.Stage}
    (hpass : t.pass = .single rows gp) (hstage : stageAt p (j + 1) next = some n)
    (hearly : p.early = true) (hone : p.answers = 1) (hnk : n.k = s'.h + s'.g) (hnh : n.h = s'.h)
    (ff : FoldedFit s s' t.st.codes n.code n.maskCode rows)
    (hc : Means.CFits (ceilLog2 s.C.l) rows.c) (hp : DenseForm rows.c)
    (hcut : switchCut s.C.a dS dC = true) (hfit : roundsFit [dS, dC] [rS, rC] = true)
    (hdrawE : dS.entry.drawE = (Send.cube t.st.codes (swTarget p n).shape).bits + 1)
    (htrees : Own.treesCan t.st.codes (swNotices p n last) = true)
    (hstep : t.st.oracles.size = t.book.place.size)
    (hG : t.st.groups[gp]? = some { code := n.code, maskCode := n.maskCode })
    (a : Fmt.Ext) (hans : rC.vals = [.answer a])
    (hsmall : 2 ^ (s'.h + s'.g) * s'.C.l ≤ 2 ^ 63 ∧ 2 ^ s'.h * s'.Z.l ≤ 2 ^ 63) (nT : ℕ)
    (tr : Tree)
    (hread : ∀ D : Taken, ReadFront (swIn p n last dS dC t rC gs rows gp D)
      (Positions.ofDraws s.C.a rC.drawn.poss) nT tr) :
    ∃ (D : Taken) (x : Fmt.Ext),
      SwitchFacts p n last dS dC t rS rC gs rows gp D j next
        (bookRead (swIn p n last dS dC t rC gs rows gp D).book nT) x ∧
      D.alpha = E.ofTriple a ∧ D.G = { code := n.code, maskCode := n.maskCode } ∧
      D.rS = rS ∧ D.rC = rC := by
  have eT : swTarget p n = switchTargetStage n.code n.maskCode (s'.h + s'.g) s'.h 1 := by
    unfold swTarget
    rw [hnk, hnh, hone]
  obtain ⟨c1, c2, -, -, -, -, -, c8, -, -, -⟩ := switchCut_says hcut
  obtain ⟨⟨-, f2, -, -⟩, ⟨g2, -, -, g5⟩, -⟩ := fit_says hfit
  obtain ⟨-, -, -, -, -, -, -, -, -, c10, -⟩ := switchCut_says hcut
  -- the letters
  obtain ⟨lay, hlay⟩ : ∃ lay, Own.treesMade t.st.codes (swNotices p n last) = some lay :=
    Option.isSome_iff_exists.1 htrees
  have hlen : (rS.drawn.elems.map E.ofTriple).length =
      (Send.cube t.st.codes (swTarget p n).shape).bits + 1 := by
    rw [List.length_map, f2, hdrawE]
  obtain ⟨beta, hbeta⟩ := seed_of _ _ hlen
  have lZ' : (t.st.codes.mask.getD n.maskCode default).ell = s'.Z.l :=
    congrArg (·.l) (getD_of_map_some ff.prog.zk')
  have hZpos : 1 ≤ s'.Z.l := by
    have hmask := hf.mask
    rcases Nat.eq_zero_or_pos s'.Z.l with h0 | h0
    · rw [h0] at hmask
      omega
    · exact h0
  obtain ⟨places, hpl⟩ : ∃ places, Send.pad t.st.codes (swTarget p n).shape = some places := by
    rw [eT]
    exact pad_some _ _ _ _ _ (by rw [lZ']; exact hZpos)
  obtain ⟨smp, hsmp⟩ := form_some t.st.codes (swTarget p n).shape t.st.oracles.size
    ⟨(rS.drawn.elems.map E.ofTriple).take (Send.cube t.st.codes (swTarget p n).shape).bits, beta⟩
    0 places hpl
  obtain ⟨cd, hcd, hcdC⟩ : ∃ cd, t.st.codes.base[rows.code]? = some cd ∧ codeOf cd = s.C := by
    have h := ff.prog.code
    cases hz : t.st.codes.base[rows.code]? with
    | none => rw [hz] at h; cases h
    | some z => rw [hz] at h; exact ⟨z, rfl, Option.some.inj h⟩
  have hcda : cd.logN = s.C.a := congrArg (·.a) hcdC
  obtain ⟨x, hx⟩ : ∃ x, rC.drawn.elems = [x] :=
    List.length_eq_one_iff.1 (g2.trans c8)
  obtain ⟨y, hy, hysz⟩ := read_yes _ _ nT tr (hread ⟨lay, rS, rC, beta, E.ofTriple a, smp, places,
    cd, #[], { code := n.code, maskCode := n.maskCode }, []⟩)
  -- the positions are in range
  have hxs : ∀ z ∈ rC.drawn.poss, z < 2 ^ s.C.a := by
    intro z hz
    have := List.all_eq_true.1 g5 z hz
    rw [c10] at this
    exact of_decide_eq_true this
  let D1 : Taken := ⟨lay, rS, rC, beta, E.ofTriple a, smp, places, cd, y,
    { code := n.code, maskCode := n.maskCode }, []⟩
  let D : Taken := { D1 with rows := (Own.swRows (D1.stJ (swTarget p n) gp (othersOf last n) t.st)
    rows (swTarget p n) t.st.oracles.size #[] (swPos rC D1) y).getD [] }
  have hpos : swPos rC D = Positions.ofDraws s.C.a rC.drawn.poss := by
    show Positions.ofDraws cd.logN rC.drawn.poss = _
    rw [hcda]
  have hgroup : (ledgerShut (D.stA (swTarget p n) (othersOf last n) t.st) (swTarget p n)
      t.st.oracles.size).groups[gp]? = some D.G := by
    rw [shut_groups]
    exact hG
  have hcan : Tw.K2.rowsCan (D.stJ (swTarget p n) gp (othersOf last n) t.st) rows (swTarget p n)
      #[] (swPos rC D) D.y = true := by
    rw [hpos, eT]
    exact can_of _ rows n.code n.maskCode _ _ _
      ((D.stJ_shape _ gp (othersOf last n) t.st).1.symm ▸ ff.prog) ff.kept _ y hysz
  have e := swNotices_eq p n last
  refine ⟨D, x,
    { pass := hpass, stage := hstage, early := hearly, one := hone
      guard := by
        rw [eT]
        exact guard_of hf t.st rows n.code n.maskCode ff.prog
      cut := by
        show switchCut cd.logN dS dC = true
        rw [hcda]
        exact hcut
      fit := hfit
      recv := recv_of t.st t.book (lt_of_map_some ff.prog.code') (lt_of_map_some ff.prog.zk')
        htrees hstep
      trees := hlay, seed := hbeta
      factor := factor_of dS rS _ beta c1 c2 hdrawE (f2.trans hdrawE) (nz_says hfit) hbeta
      form := hsmp, pad := hpl, ans := hans
      admit := by
        rw [e]
        exact admit_of t.st _ _ _ places hpl hone
      elem := hx, code := hcd
      read := by
        rw [hpos]
        exact hy
      group := hgroup
      joinOk := join_of D (swTarget p n) gp (othersOf last n) t.st hG rfl rfl rfl rfl
      can := hcan, made := rfl
      addOk := addOk_of hf ff hnk hnh hone hgroup hpl hcan rfl rfl rfl hsmall hc hp hxs },
    rfl, rfl, rfl, rfl⟩

/-- **What the switch and the batching have done, in the soundness side's record, at the same
letters.** -/
theorem did_at {p : P12} {n : IoppStage} {last : Bool} {dS dC : Fmt.DeclaredRound} {t : T12}
    {rS rC : Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} {rows : SingleRows} {gp j : ℕ}
    {D : Taken} {next : Fmt.M1.Stage} {B : TreeBook} {x : Fmt.Ext} {row : GroupRow}
    {lay : GroupLayout} (F : SwitchFacts p n last dS dC t rS rC gs rows gp D j next B x)
    (F' : BehindFront p n last dC t gp D (E.ofTriple x) row lay) (hS : D.rS = rS)
    (hC : D.rC = rC) :
    Did p.nums.firstTree (keyed p [dS, dC] gs) rows (swTarget p n) gp (othersOf last n) t.st t.book
      t.roots (behindT p n last t rC gp D B row lay).st B (swOut p n last t rC D) row lay
      (E.ofTriple x) D := by
  have e := swNotices_eq p n last
  obtain ⟨-, -, -, -, -, c6, -⟩ := switchCut_says F.cut
  obtain ⟨⟨f1, -, -, -⟩, -, -⟩ := fit_says F.fit
  have F1 := front_of_facts F
  obtain ⟨S2, h2⟩ := ok_of_isSome F.joinOk
  obtain ⟨G, hG, hrun, -⟩ := joinS_ok h2
  obtain rfl : G = D.G := Option.some.inj (hG.symm.trans F.group)
  obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1
    (Tw.K2.rowsCan_some (g := t.st.oracles.size) F.can)
  have hrows : D.rows = l := by
    rw [F.made]
    show (switchRows _ _ _ _ _ _ _).getD [] = l
    rw [hl]
    rfl
  have hrecv := F.recv
  simp only [Ground.ok, Ground.recvL, Ground.sentL, List.all_append, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true, beq_iff_eq] at hrecv
  exact
    { check := (Tw.K2.targetOk_eq _ _ _).symm.trans F.guard
      trees := by
        have h := F.trees
        rw [Own.treesMade_eq, e] at h
        exact h
      places := hrecv.2
      valsS := by
        rw [hS]
        rw [c6] at f1
        exact List.map_eq_nil_iff.1 f1
      seed := by
        rw [hS]
        exact F.seed
      factor := F.factor
      form := by
        unfold Taken.z
        rw [hS]
        exact F.form
      pad := F.pad
      valsC := by
        rw [hC]
        exact F.ans
      elem := by
        rw [hC, F.elem]
        rfl
      code := F.code
      g := swIds_zero p n last t
      kept := rfl
      riders := by
        show (swIds p n last t).extract 1 (swIds p n last t).size = _
        unfold swIds
        rw [e]
        refine Array.ext (by simp) fun i h1 h2 => ?_
        simp only [Array.getElem_extract, Array.getElem_map, Array.getElem_range]
        omega
      positions := by
        rw [hC]
        rfl
      read := ⟨swIn p n last dS dC t rC gs rows gp D, [], rfl, rfl, rfl, rfl, rfl, F.read⟩
      group := F.group
      fresh := hrun
      rows := by
        rw [hrows]
        exact hl
      kinds := (addRowsS_ok gp D.rows _ _ F1.add).1
      layout := by
        rw [← F'.layout]
        exact Own.layout_of_group F'.group
      row := F'.batch
      st := rfl }

end Johnson.Prover.Link
