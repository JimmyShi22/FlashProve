-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkProxChain.lean: the program's stages of a proximity test give the chain's yes in
the field, for a test that stands anywhere in any chain.

OnBytes/Slice/ManyBlk.lean follows a run of the program's stages (OnBytes/Iop/Prox.lean:
ioppStagesVerify) along a chain of any number of stages and concludes the chain's yes in the field.
Its joints are those of a link's chain: the chain's first tree has the number 0, a tree's number is
one less than the number of roots received, the columns that are read are tied to the written trees
by their keys, no tensor of a claim's form has a written-out factor, no round comes after the base
case, and the goal does not speak of the context that the run leaves. A key's four tests break each
of these somewhere. This file has joints without these clauses (but that the tree of a stage which a
code switch has sent is the last that was sent: Chain.JointTail) and follows the run again, over the
same laws on the program's calls. A joint says which rounds are not yet closed and which opened
columns are left to be read, both as lists that begin with the test's own and go on with any others.

Main definitions.
  GroupOn, SingleOn, LastOn   the joints before a fold, after a fold, before the base case.
  FoldTiesOn        a tie goes through a fold.
  StagesTo          a run of the stages from one stage on leads from a joint to a goal on the
                    context that the run leaves.
  Chain.rvsT        a chain's written rounds as a view shows them, with further rounds behind.
  Chain.colsT       the columns that a run along the chain reads, as a view lists them, with further
                    columns behind.
  Chain.Deep        each tree that is folded has as many positions as its stage's code.
  Chain.JointTail   the joint before a stage whose tree a code switch has sent.
Main theorems.
  foldRuns_on, foldTies_on        the fold.
  csRuns_of_on, csRuns_group_on, csRuns_last_on, csRuns_middle_on, csRuns_second_on,
  csRuns_later_on                 the code switch.
  lastRuns_on                     the base case: the library's decision, and the rounds and columns
                                  behind are what is left.
  stagesTo_step, stagesTo_chain   the stages, along a chain.
  Chain.rvsT_eq, Chain.rounds_eq  rvsT is the chain's rounds and then the others; the chain has as
                                  many rounds as the program's stages close (stagesRounds).

Not claimed. That a run reaches the first joint. The public facts (Chain.Pub, Chain.Own,
Chain.Deep), which are hypotheses. That a view lists the written trees' columns in this order.
Nothing is said of a test whose masks do not ride in the switches' messages. Nothing on soundness.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Slice.BlkProxKeeps
import OnBytes.Slice.BlkProxLast
import OnBytes.Slice.ManyBlk

set_option autoImplicit false

namespace OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open Params (IoppStage)

/-! ## The joints -/

/-- The joint before a fold at the stage s. q: the claim. cols: the opened columns that are left to
be read. Tie: what is public of the row, the layout, and the trees of the group's members and of the
fresh mask. -/
structure GroupOn (F : Nat) (cols : Cols) (K : Codes) (roots : Nat) (s : Sg)
    (q : GE × (s.cIn.J → GE)) (rest : List Fmt.RoundView)
    (Tie : Ctx → GroupRow → GroupLayout → Nat → Prop) (answers : Nat) (c : Ctx) (row : GroupRow)
    (L : GroupLayout) (mask : Option Nat) : Prop where
  /-- what every joint says of the run -/
  run : RunOn F K roots rest answers c
  /-- the opened columns that are left to be read -/
  opened : c.ch.opened = cols
  /-- the program's row on the group, read in the field, is the claim -/
  claim : stmG s row = q
  /-- the fold's fresh mask has come, and the tie holds of it -/
  mask : ∃ o, mask = some o ∧ Tie c row L o

/-- The joint after a fold at the stage s. q: the claim on the three folded rows. -/
structure SingleOn (F : Nat) (cols : Cols) (K : Codes) (roots : Nat) (s : Sg)
    (q : GE × (s.cMid.J → GE)) (rest : List Fmt.RoundView) (Tie : Ctx → SingleRows → Prop)
    (answers : Nat) (c : Ctx) (rows : SingleRows) : Prop where
  /-- what every joint says of the run -/
  run : RunOn F K roots rest answers c
  /-- the opened columns that are left to be read -/
  opened : c.ch.opened = cols
  /-- the program's claim on the three folded rows, read in the field, is the claim -/
  claim : stmS s rows = q
  /-- the tie -/
  tie : Tie c rows

/-- The joint before the base case, at the last stage s. The clauses are those of LastAt
(OnBytes/Slice/BlkJointLast.lean). n: the number of the last tree. -/
structure LastOn (F : Nat) (cols : Cols) (K : Codes) (roots : Nat) (s : Sg) (cur : IoppStage)
    (q : GE × (s.cIn.J → GE)) (rest : List Fmt.RoundView) (n : Nat) (answers : Nat) (c : Ctx)
    (row : GroupRow) (L : GroupLayout) (mask : Option Nat) : Prop where
  /-- what every joint says of the run -/
  run : RunOn F K roots rest answers c
  /-- the opened columns that are left to be read -/
  opened : c.ch.opened = cols
  /-- the program's row on the last group, read in the field, is the claim -/
  claim : stmGk s 1 0 row = q
  /-- fixing the form's lowest variable at 0 picks the entries of the first row -/
  fix : FixLaw row.c [zeroE]
  /-- the one member is not kept -/
  kept : L.kept.getD 0 false = false
  /-- its main row is row 0 of the group's main table -/
  mainFirst : L.mainFirst.getD 0 none = some 0
  /-- its mask row is row 0 of the group's mask table -/
  maskFirst : L.maskFirst.getD 0 none = some 0
  /-- the last tree holds the one member and the masking oracle, which has come -/
  seat : ∃ (o star : Nat) (sh sh' : OracleShape), L.members = #[o] ∧ mask = some star ∧
    OneAndOne sh ∧ OneAndOne sh' ∧ Seat c [o, star] n s.C.a [sh, sh']

/-- Keeping a value changes nothing that the joint before the base case says. -/
theorem LastOn.notes {F : Nat} {cols : Cols} {K : Codes} {roots : Nat} {s : Sg} {cur : IoppStage}
    {q : GE × (s.cIn.J → GE)} {rest : List Fmt.RoundView} {n a : Nat} {c c' : Ctx} {row : GroupRow}
    {L : GroupLayout} {m : Option Nat} (h : LastOn F cols K roots s cur q rest n a c row L m)
    (hn : Blk.SameButNotes c c') : LastOn F cols K roots s cur q rest n a c' row L m := by
  obtain ⟨o, star, sh, sh', h1, h2, h3, h4, h5⟩ := h.seat
  refine ⟨h.run.notes hn, by rw [hn.ch]; exact h.opened, h.claim, h.fix, h.kept, h.mainFirst,
    h.maskFirst, o, star, sh, sh', h1, h2, h3, h4, h5.keeps (BookKeeps.of_eq hn.book) ?_⟩
  rw [hn.st]
  exact ShapesKeep.refl _

/-! ## The fold -/

/-- The tie goes through a fold: from the tie Tie before it to the tie Tie' after it, on the
fold's output. What is known of the run: the mask was marked as spent (c to c1); the fold's rounds
were taken and nothing else was done (c1 to c'); the point that was drawn; the fold's own tests of
the shape and of the row have passed. -/
def FoldTiesOn (K : Codes) (s : Sg) (cur : IoppStage) (pt : Fin (s.h + s.g) → GE)
    (rest : List Fmt.RoundView) (Tie : Ctx → GroupRow → GroupLayout → Nat → Prop)
    (Tie' : Ctx → SingleRows → Prop) : Prop :=
  ∀ (c c1 c' : Ctx) (row : GroupRow) (L : GroupLayout) (o : Nat) (eps claim : E)
    (gamma : List E), Tie c row L o → c.st.codes = K →
    (Blk.spendAsMask o).Yields c () c1 → RanRounds (s.h + s.g + 1) rest c1 c' →
    readP (s.h + s.g) gamma = pt → gamma.length = s.h + s.g →
    foldShapeOk c.st (ioppFoldShape cur L) = true →
    foldRowOk c1.st (ioppFoldShape cur L) row = true →
    Tie' c' (foldOutput c1.st (ioppFoldShape cur L) row o eps gamma claim)

/-- For a stage with the program's codes (hK) and ties that go through a fold (hT): if GroupOn
holds and the program's fold runs through, SingleOn holds where the run ends, at the claim
foldNext. -/
theorem foldRuns_on (F : Nat) (cols : Cols) (K : Codes) (roots : Nat) (s : Sg) (cur : IoppStage)
    (hK : StageCodes s cur K) (dE dT : PQ.RD)
    (q : GE × (s.cIn.J → GE)) (τ : Tr (PQ.uL (ckP .two) (foldRds s dE dT))) (rest : List Fmt.RoundView)
    (Tie : Ctx → GroupRow → GroupLayout → Nat → Prop) (Tie' : Ctx → SingleRows → Prop)
    (hT : FoldTiesOn K s cur (foldPt s dE dT τ) rest Tie Tie') :
    FoldRuns cur (GroupOn F cols K roots s q (PQ.rvSL (ckP .two) (foldRds s dE dT) τ ++ rest) Tie)
      (SingleOn F cols K roots s (foldNext s s.Z.l dE dT q τ) rest Tie') := by
  intro answers c row L mask rows c' hJ hrun
  obtain ⟨o, rfl, ht⟩ := hJ.mask
  obtain ⟨hst, c1, eps, claim, gamma, hsp, hout, hpt, hlen, hran, hshape, _, hrow⟩ :=
    fold_sem s (ioppFoldShape cur L) hK.k hK.h row o dE dT τ.1 τ.2.1 τ.2.2
      rest c c' rows hJ.run.dry (by rw [hJ.run.codes]; exact congrArg (·.l) hK.mask)
      hJ.run.pending hrun
  have e1 := Blk.spendAsMask_inv o c c1 hsp
  refine ⟨⟨hran.dry, ?_, hran.pending, ?_, ?_, hJ.run.answers⟩, ?_, ?_, ?_⟩
  · rw [hran.firstTree, e1]
    exact hJ.run.first
  · rw [hran.st, e1]
    exact hJ.run.codes
  · rw [hran.roots, e1]
    exact hJ.run.roots
  · rw [hran.opened, e1]
    exact hJ.opened
  · rw [hst, hJ.claim]
    rfl
  · rw [hout]
    exact hT c c1 c' row L o eps claim gamma ht hJ.run.codes hsp hran hpt hlen hshape hrow

/-- What the fold's output is, as far as a code switch asks, after a fold of a group without kept
members. The four hypotheses on codes are public. -/
theorem foldedFit_of (K : Codes) (s s' : Sg) (cur : IoppStage) (hK : StageCodes s cur K)
    (nc nz : Nat) (hzk : (K.mask[cur.maskCode]?).map codeOf = some s.Z)
    (hc' : (K.base[nc]?).map codeOf = some s'.C) (hz' : (K.mask[nz]?).map codeOf = some s'.Z)
    (hsmall : s.C.a ≤ 32) (c c1 : Ctx) (row : GroupRow) (L : GroupLayout) (o : Nat)
    (eps claim : E) (gamma : List E) (hcK : c.st.codes = K) (h0 : row.kept = #[])
    (hkept : ∀ i, i < L.members.size → L.kept.getD i false = false)
    (hsp : (Blk.spendAsMask o).Yields c () c1) (hlen : gamma.length = s.h + s.g)
    (hshape : foldShapeOk c.st (ioppFoldShape cur L) = true)
    (hrow : foldRowOk c1.st (ioppFoldShape cur L) row = true) :
    FoldedFit s s' K nc nz (foldOutput c1.st (ioppFoldShape cur L) row o eps gamma claim) := by
  have e1 := Blk.spendAsMask_inv o c c1 hsp
  have hc1 : c1.st.codes = K := by rw [e1]; exact hcK
  obtain ⟨hhk, hcol⟩ := of_foldShapeOk c.st (ioppFoldShape cur L) hshape
  obtain ⟨o1, o2, o3, o4, o5, o6⟩ :=
    foldOutput_fit c1.st (ioppFoldShape cur L) row o eps gamma claim (hlen.trans hK.k.symm) hrow hhk
      (by rw [hc1, ← hcK]; exact hcol) h0 hkept
  obtain ⟨cd, hcd, hC⟩ := hK.base
  have ez : (c1.st.codes.mask.getD cur.maskCode default).ell = s.Z.l := by
    rw [hc1]
    exact congrArg (·.l) hK.mask
  have ec : (c1.st.codes.base.getD cur.code default).ell = s.C.l := by
    rw [hc1, Array.getD_eq_getD_getElem?, hcd]
    exact congrArg (·.l) hC
  have hcode : (K.base[cur.code]?).map codeOf = some s.C := by
    rw [hcd]
    exact congrArg some hC
  exact ⟨⟨hcode, hzk, hc', hz', o2, rfl, o3, hsmall⟩, o1, o4.trans ez, o5.trans ez,
    fun v hv => (o6 v hv).trans (congrArg ceilLog2 ec),
    order_foldOutput c1.st (ioppFoldShape cur L) row o eps gamma claim hrow⟩

/-- The tie on columns goes through a fold at the stage s, before a switch to the stage s'. The
four hypotheses on codes are public. -/
theorem foldTies_on (K : Codes) (s s' : Sg) (cur : IoppStage) (hK : StageCodes s cur K)
    (nc nz n : Nat) (shapes : List OracleShape) (mainFirst maskFirst : Array (Option Nat))
    (pt : Fin (s.h + s.g) → GE) (rest : List Fmt.RoundView)
    (hzk : (K.mask[cur.maskCode]?).map codeOf = some s.Z)
    (hc' : (K.base[nc]?).map codeOf = some s'.C) (hz' : (K.mask[nz]?).map codeOf = some s'.Z)
    (hsmall : s.C.a ≤ 32) :
    FoldTiesOn K s cur pt rest (GroupTie s n shapes mainFirst maskFirst)
      (SingleFit s s' K nc nz n shapes mainFirst maskFirst pt) := by
  intro c c1 c' row L o eps claim gamma ht hcK hsp hran hpt hlen hshape hrow
  obtain ⟨ms, hlay, hseat⟩ := ht.seat
  have e1 := Blk.spendAsMask_inv o c c1 hsp
  have hkept : ∀ i, i < L.members.size → L.kept.getD i false = false := by
    intro i hi
    refine hlay.kept i ?_
    rw [hlay.members] at hi
    exact hi
  refine ⟨foldedFit_of K s s' cur hK nc nz hzk hc' hz' hsmall c c1 row L o eps claim gamma hcK
    ht.noKept hkept hsp hlen hshape hrow, hK.k, hK.h, hpt, ms,
    ⟨hlay.members, hlay.kept, hlay.mainFirst, hlay.maskFirst⟩, ?_⟩
  refine hseat.keeps (BookKeeps.of_eq ?_) ?_
  · rw [hran.book, e1]
  · rw [hran.st]
    exact spend_shapesKeep o c c1 hsp

/-! ## The code switch -/

/-- A run of the program's code switch leads from the joint after a fold to a joint J', if what
the run has done gives J'. Tie must not depend on the values that are kept nor on the groups; J' not
on the values that are kept. -/
theorem csRuns_of_on (F : Nat) (cols : Cols) (K : Codes) (roots : Nat) (s : Sg) (ride : Bool)
    (next : IoppStage) (later : List IoppStage) (dS dC : PQ.RD)
    (τC : Tr (PQ.uL (ckP .two) [dS, dC])) (rest : List Fmt.RoundView) (q : GE × (s.cMid.J → GE))
    (Tie : Ctx → SingleRows → Prop) (J' : GroupJoint)
    (hTie : ∀ (c c' : Ctx) (rows : SingleRows), c'.ch = c.ch → c'.book = c.book →
      c'.st.oracles = c.st.oracles → c'.st.codes = c.st.codes → Tie c rows → Tie c' rows)
    (hJ' : ∀ (a : Nat) (c c' : Ctx) (row : GroupRow) (L : GroupLayout) (m : Option Nat),
      Blk.SameButNotes c c' → J' a c row L m → J' a c' row L m)
    (hgive : ∀ (c c' : Ctx) (rows : SingleRows) (gp : Nat) (sw : Switched) (row' : GroupRow)
      (L' : GroupLayout) (theta : E) (D : CsTaken) (mask : Option Nat),
      RunOn F K roots (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest) 1 c → c.ch.opened = cols →
      stmS s rows = q → Tie c rows →
      c.st.groups[gp]? = some { code := next.code, maskCode := next.maskCode } →
      CsRan rows (switchTargetStage next.code next.maskCode next.k next.h 1) gp
        (stageOthers ride next later) c c' sw row' L' theta D →
      RunOn F K (roots + D.lay.shapes.size) rest 1 c' →
      ((ride = true ∧ sw.others[0]? = mask ∧ mask.isSome = true) ∨ (ride = false ∧ mask = none)) →
      J' 1 c' row' L' mask) :
    CsRuns ride next later
      (SingleOn F cols K roots s q (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest) Tie) J' := by
  intro answers c1 rows c2 gp c3 sw row' L' c4 c8 mask hJ n12 hnew hcs n48 hmask
  obtain rfl : answers = 1 := hJ.run.answers
  have r2 := hJ.run.notes n12
  obtain ⟨hto, e3⟩ := newGroup_inv _ _ _ _ _ hnew
  have r3 : RunOn F K roots (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest) 1 c3 := by
    rw [e3]
    exact ⟨r2.dry, r2.first, r2.pending, r2.codes, r2.roots, rfl⟩
  have o3 : c3.ch.opened = cols := by
    rw [e3]
    show c2.ch.opened = cols
    rw [n12.ch]
    exact hJ.opened
  have t3 : Tie c3 rows := by
    refine hTie c1 c3 rows ?_ ?_ ?_ ?_ hJ.tie
    · rw [e3]; exact n12.ch
    · rw [e3]; exact n12.book
    · rw [e3]; show c2.st.oracles = _; rw [n12.st]
    · rw [e3]; show c2.st.codes = _; rw [n12.st]
  have g3 : c3.st.groups[gp]? = some { code := next.code, maskCode := next.maskCode } := by
    rw [e3, hto]
    exact withGroup_group _ _ _
  obtain ⟨theta, D, hran⟩ := csVerify_inv rows _ gp _ sw row' L' c3 c4 r3.dry rfl rfl
    (stageOthers_plain ride next later) hcs
  have hrest : D.rest = rest := by
    have e : D.rS :: D.rC :: D.rest = PQ.rvSL (ckP .two) [dS, dC] τC ++ rest :=
      hran.pending.symm.trans r3.pending
    injection e with _ e2
    injection e2 with _ e3
  have r4 : RunOn F K (roots + D.lay.shapes.size) rest 1 c4 :=
    ⟨hran.dry, hran.firstTree.trans r3.first, hran.pending'.trans hrest,
      hran.codes.trans r3.codes, by rw [hran.roots_eq, r3.roots], rfl⟩
  exact hJ' 1 c4 c8 row' L' mask n48
    (hgive c3 c4 rows gp sw row' L' theta D mask r3 o3 hJ.claim t3 g3 hran r4 hmask)

/-- A run of the program's code switch leads from the joint after a fold to the joint before the
next fold. s, s': the two stages. y: the three folded words. hOk: the tie after the fold gives
FoldedFit. hread: the symbols that the run has read are the long symbols of the word y, and the run
leaves the columns cols'. hTie': the tie before the next fold. The others are public facts on
sizes. -/
theorem csRuns_group_on (F : Nat) (cols cols' : Cols) (K : Codes) (roots : Nat) {s s' : Sg}
    (hf : CsFit s s') (next : IoppStage) (later : List IoppStage) (hK' : StageCodes s' next K)
    (hk1 : 1 ≤ s'.h + s'.g) (dS dC : PQ.RD) (hr : CsRounds s s' dS dC)
    (τC : Tr (PQ.uL (ckP .two) [dS, dC])) (rest : List Fmt.RoundView) (q : GE × (s.cMid.J → GE))
    (y : s.cMid.Word) (Tie : Ctx → SingleRows → Prop)
    (Tie' : Ctx → GroupRow → GroupLayout → Nat → Prop)
    (hTie : ∀ (c c' : Ctx) (rows : SingleRows), c'.ch = c.ch → c'.book = c.book →
      c'.st.oracles = c.st.oracles → c'.st.codes = c.st.codes → Tie c rows → Tie c' rows)
    (hTn : ∀ (c c' : Ctx) (row : GroupRow) (L : GroupLayout) (o : Nat), Blk.SameButNotes c c' →
      Tie' c row L o → Tie' c' row L o)
    (hOk : ∀ (c : Ctx) (rows : SingleRows), Tie c rows →
      FoldedFit s s' K next.code next.maskCode rows)
    (hbits : (Send.cube K
      (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1).shape).bits = s'.st.na)
    (hone : ∀ lay, layTrees K (sentOf (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h
      1) (stageOthers true next later)) = some lay → lay.shapes.size = 1)
    (hread : ∀ (c c' : Ctx) (rows : SingleRows) (gp : Nat) (sw : Switched) (row' : GroupRow)
      (L' : GroupLayout) (theta : E) (D : CsTaken),
      RunOn F K roots (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest) 1 c → c.ch.opened = cols →
      Tie c rows →
      CsRan rows (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1) gp
        (stageOthers true next later) c c' sw row' L' theta D →
      (∀ i α, s.cMid.T y ((gCs s.C.a s.t _ (valsOf dC τC.2.2.2.1)).1 i) α =
        symS s rows sw.positions D.y ((gCs s.C.a s.t _ (valsOf dC τC.2.2.2.1)).1 i).val α) ∧
        c'.ch.opened = cols')
    (hTie' : ∀ (c c' : Ctx) (rows : SingleRows) (gp : Nat) (sw : Switched) (row' : GroupRow)
      (L' : GroupLayout) (theta : E) (D : CsTaken),
      RunOn F K roots (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest) 1 c → Tie c rows →
      c.st.groups[gp]? = some { code := next.code, maskCode := next.maskCode } →
      CsRan rows (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1) gp
        (stageOthers true next later) c c' sw row' L' theta D →
      Tie' c' row' L' (c.st.oracles.size + 1)) :
    CsRuns true next later
      (SingleOn F cols K roots s q (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest) Tie)
      (GroupOn F cols' K (roots + 1) s' (csNextW hf dS dC q y τC) rest Tie') := by
  refine csRuns_of_on F cols K roots s true next later dS dC τC rest q Tie _ hTie ?_ ?_
  · intro a c c' row L m hn hJ
    obtain ⟨o, ho, ht⟩ := hJ.mask
    exact ⟨hJ.run.notes hn, by rw [hn.ch]; exact hJ.opened, hJ.claim, o, ho,
      hTn c c' row L o hn ht⟩
  · intro c c' rows gp sw row' L' theta D mask hrun hop hq ht hg hran hrun' hmask
    rw [hK'.k, hK'.h] at hran
    have hG := csRan_group hran hg
    have ok := hOk c rows ht
    obtain ⟨hrd, hleft⟩ := hread c c' rows gp sw row' L' theta D hrun hop ht hran
    have hcl := csRan_claim hf dS dC hr τC rest hran hrun.pending
      (by rw [hrun.codes]; exact ok.prog) ok.kept hG ok.d0 ok.d1 ok.vars
      (by rw [hrun.codes]; exact hbits) y hrd
    have hlay := hran.lay_eq (by rw [hG]) (by rw [hG])
    have hk : L'.k = s'.h + s'.g := by
      rw [hlay]
      show max (max (s'.h + s'.g) s'.h) 1 = s'.h + s'.g
      omega
    have hh : L'.h = s'.h := by rw [hlay]
    have h1 : D.lay.shapes.size = 1 := hone D.lay (by rw [← hrun.codes]; exact hran.trees)
    rw [h1] at hrun'
    refine ⟨hrun', hleft, ?_, c.st.oracles.size + 1, ?_,
      hTie' c c' rows gp sw row' L' theta D hrun ht hg hran⟩
    · rw [stmG_eq, ← hk, ← hh, hcl, hq]
    · rcases hmask with ⟨_, hm, _⟩ | ⟨hf', _⟩
      · exact csRan_mask hran mask hm
      · cases hf'

/-- A run of the program's last code switch leads from the joint after a fold to the joint before
the base case. s, s': the two stages, the second without a row variable (h0, g0). y: the three
folded words. The new tree has the number F + roots. -/
theorem csRuns_last_on (F : Nat) (cols cols' : Cols) (K : Codes) (roots : Nat) {s s' : Sg}
    (hf : CsFit s s') (next : IoppStage) (hK' : StageCodes s' next K) (h0 : s'.h = 0)
    (g0 : s'.g = 0) (dS dC : PQ.RD) (hr : CsRounds s s' dS dC)
    (τC : Tr (PQ.uL (ckP .two) [dS, dC])) (rest : List Fmt.RoundView) (q : GE × (s.cMid.J → GE))
    (y : s.cMid.Word) (Tie : Ctx → SingleRows → Prop)
    (hTie : ∀ (c c' : Ctx) (rows : SingleRows), c'.ch = c.ch → c'.book = c.book →
      c'.st.oracles = c.st.oracles → c'.st.codes = c.st.codes → Tie c rows → Tie c' rows)
    (hOk : ∀ (c : Ctx) (rows : SingleRows), Tie c rows →
      FoldedFit s s' K next.code next.maskCode rows)
    (hbits : (Send.cube K
      (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1).shape).bits = s'.st.na)
    (hlay : ∀ lay, layTrees K (sentOf (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h
      1) (stageOthers true next [])) = some lay →
      ∃ sh : TreeShape, lay.shapes = #[sh] ∧ sh.logN = s'.C.a ∧
        (∀ i, i < 2 → lay.tree.getD i 0 = 0 ∧ lay.part.getD i 0 = i) ∧
        sh.mainSymbols = #[3, 3] ∧ sh.maskSymbols = #[3, 3])
    (hread : ∀ (c c' : Ctx) (rows : SingleRows) (gp : Nat) (sw : Switched) (row' : GroupRow)
      (L' : GroupLayout) (theta : E) (D : CsTaken),
      RunOn F K roots (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest) 1 c → c.ch.opened = cols →
      Tie c rows →
      CsRan rows (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1) gp
        (stageOthers true next []) c c' sw row' L' theta D →
      (∀ i α, s.cMid.T y ((gCs s.C.a s.t _ (valsOf dC τC.2.2.2.1)).1 i) α =
        symS s rows sw.positions D.y ((gCs s.C.a s.t _ (valsOf dC τC.2.2.2.1)).1 i).val α) ∧
        c'.ch.opened = cols') :
    CsRuns true next []
      (SingleOn F cols K roots s q (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest) Tie)
      (LastOn F cols' K (roots + 1) s' next (csNextW hf dS dC q y τC) rest (F + roots)) := by
  refine csRuns_of_on F cols K roots s true next [] dS dC τC rest q Tie _ hTie
    (fun a c c' row L m hn hJ => hJ.notes hn) ?_
  intro c c' rows gp sw row' L' theta D mask hrun hop hq ht hg hran hrun' hmask
  rw [hK'.k, hK'.h] at hran
  have hG := csRan_group hran hg
  have ok := hOk c rows ht
  obtain ⟨hrd, hleft⟩ := hread c c' rows gp sw row' L' theta D hrun hop ht hran
  have hcl := csRan_claim hf dS dC hr τC rest hran hrun.pending
    (by rw [hrun.codes]; exact ok.prog) ok.kept hG ok.d0 ok.d1 ok.vars
    (by rw [hrun.codes]; exact hbits) y hrd
  have hL := hran.lay_eq (by rw [hG]) (by rw [hG])
  have hk : L'.k = 1 := by
    rw [hL]
    show max (max (s'.h + s'.g) s'.h) 1 = 1
    omega
  have hh : L'.h = 0 := by rw [hL]; exact h0
  obtain ⟨sh, l1, l2, l3, l4, l5⟩ := hlay D.lay (by rw [← hrun.codes]; exact hran.trees)
  have h1 : D.lay.shapes.size = 1 := by rw [l1]; rfl
  rw [h1] at hrun'
  have p0 : (2 : ℕ) ^ (s'.h + s'.g) = 1 := by rw [h0, g0]; rfl
  have p1 : (2 : ℕ) ^ s'.h = 1 := by rw [h0]; rfl
  have hseat := hran.seat sh l1 l3
    (by rw [l4]; show #[3, 3] = #[2 ^ (s'.h + s'.g) * 3, 1 * 3]; rw [p0])
    (by rw [l5]; show #[3, 3] = #[2 ^ s'.h * 3, 1 * 3]; rw [p1])
  have hstar : mask = some (c.st.oracles.size + 1) := by
    rcases hmask with ⟨_, hm, _⟩ | ⟨hf', _⟩
    · exact csRan_mask hran mask hm
    · cases hf'
  have hord : OrderForm row'.c :=
    csRan_order hran ok.kept ok.prog.masks ok.prog.noKept (by rw [hG]) (by rw [hG]) ok.order
  refine ⟨hrun', hleft, ?_,
    fixLaw_of_order _ hord _ (hran.vars (by rw [hG]) (by rw [hG]) (by rw [hG])),
    by rw [hL]; rfl, by rw [hL]; rfl, by rw [hL]; rfl,
    c.st.oracles.size, c.st.oracles.size + 1,
    (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1).shape,
    (baseMaskNotice next.code next.maskCode 1 0).shape, by rw [hL], hstar, ⟨p0, rfl, p1⟩,
    ⟨rfl, rfl, rfl⟩, ?_⟩
  · rw [← hk, ← hh, hcl, hq]
  · rw [hrun.first, hrun.roots, l2] at hseat
    have e : (List.range (sentOf (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1)
        (stageOthers true next [])).size).map (· + c.st.oracles.size)
        = [c.st.oracles.size, c.st.oracles.size + 1] := by
      show [0 + c.st.oracles.size, 1 + c.st.oracles.size] = _
      rw [Nat.zero_add, Nat.add_comm 1]
    rw [e] at hseat
    exact hseat

/-- The tie before the next fold holds after a run of the switch into a stage after which more
stages come: the new tree has the number F + roots. -/
theorem groupTie_on (F : Nat) (K : Codes) (roots : Nat) (s' : Sg) (next : IoppStage)
    (pend : List Fmt.RoundView)
    (hone : OneTree K (sentOf (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1)
      #[foldMaskNotice (ioppFoldShape next {})]) s'.C.a)
    (c c' : Ctx) (rows : SingleRows) (gp : Nat) (sw : Switched) (row' : GroupRow)
    (L' : GroupLayout) (theta : E) (D : CsTaken) (hrun : RunOn F K roots pend 1 c)
    (hg : c.st.groups[gp]? = some { code := next.code, maskCode := next.maskCode })
    (hran : CsRan rows (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1) gp
      #[foldMaskNotice (ioppFoldShape next {})] c c' sw row' L' theta D) :
    GroupTie s' (F + roots) [(switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1).shape,
      (foldMaskNotice (ioppFoldShape next {})).shape] #[some 0] #[some 0] c' row' L'
      (c.st.oracles.size + 1) := by
  obtain ⟨shT, l1, l2, l3, l4, l5⟩ := hone D.lay (by rw [← hrun.codes]; exact hran.trees)
  exact CsRan.groupTie s' (foldMaskNotice (ioppFoldShape next {})) hran (csRan_group hran hg) shT
    l1 l3 l4 l5 l2 (F + roots) (by rw [hrun.first, hrun.roots])

/-- The switch after the fold of a group with one member of the shape sh, into a stage after which
more stages come, leads from joint to joint. sh': the fresh mask's shape. d, m: the written round
that sent their tree, and its message. n: the tree's number. What is left to be read begins with the
tree's segment at the switch's positions; R comes after it. -/
theorem csRuns_middle_on (F : Nat) (R : Cols) (K : Codes) (roots : Nat) {s s' : Sg}
    (hf : CsFit s s') (next n3 : IoppStage) (later : List IoppStage) (hK' : StageCodes s' next K)
    (hk1 : 1 ≤ s'.h + s'.g) (dS dC : PQ.RD) (hr : CsRounds s s' dS dC)
    (τC : Tr (PQ.uL (ckP .two) [dS, dC])) (rest : List Fmt.RoundView) (q : GE × (s.cMid.J → GE))
    (n : Nat) (sh sh' : OracleShape) (pt : Fin (s.h + s.g) → GE) (d : PQ.RD)
    (m : (wRound d).Msg) (hN : PQ.posN d.tree = 2 ^ s.C.a)
    (hW : PQ.colW d.tree = 3 * 2 ^ (s.h + s.g) + 3 * (2 * 2 ^ s.h))
    (m1 : sh.mainRows = 2 ^ (s.h + s.g)) (m2 : sh.mainDeg = 3) (m3 : sh.maskRows = 2 ^ s.h)
    (f1 : sh'.mainRows = 0) (f3 : sh'.maskRows = 2 ^ s.h)
    (hbits : (Send.cube K
      (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1).shape).bits = s'.st.na)
    (hone : OneTree K (sentOf (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1)
      #[foldMaskNotice (ioppFoldShape next {})]) s'.C.a) :
    CsRuns true next (n3 :: later)
      (SingleOn F
        (segOf (n - F) (listAt s.C.a dC τC.2.2.1 τC.2.2.2.1).all.toList (treeCol d m) ++ R) K roots
        s q (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest)
        (SingleFit s s' K next.code next.maskCode n [sh, sh'] #[some 0] #[some 0] pt))
      (GroupOn F R K (roots + 1) s' (csNextW hf dS dC q (wordMid s (colSt s d m.1) pt) τC) rest
        (GroupTie s' (F + roots)
          [(switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1).shape,
            (foldMaskNotice (ioppFoldShape next {})).shape] #[some 0] #[some 0])) := by
  refine csRuns_group_on F _ R K roots hf next (n3 :: later) hK' hk1 dS dC hr τC rest q _ _ _
    (fun c c' rows _ hb ho _ ht => ht.congr hb ho) (fun c c' row L o hn ht => ht.notes hn)
    (fun c rows ht => ht.ok) hbits ?_ ?_ ?_
  · intro lay hlay
    obtain ⟨shT, l1, _⟩ := hone lay hlay
    rw [l1]
    rfl
  · intro c c' rows gp sw row' L' theta D hrun hop ht hran
    exact hread_stage_seg F K roots dS dC hr τC rest _ _ n sh sh' pt d m hN hW m1 m2 m3 f1 f3
      _ _ c c' rows gp sw row' L' theta D R hrun hop ht hran
  · intro c c' rows gp sw row' L' theta D hrun ht hg hran
    exact groupTie_on F K roots s' next _ hone c c' rows gp sw row' L' theta D hrun hg hran

/-- The switch into the last stage, after the fold of a group with one member of the shape sh,
leads from joint to joint. sh': the fresh mask's shape. d, m: the written round that sent their
tree, and its message. n: the tree's number. What is left to be read begins with the tree's segment
at the switch's positions; R comes after it. -/
theorem csRuns_second_on (F : Nat) (R : Cols) (K : Codes) (roots : Nat) {s s' : Sg}
    (hf : CsFit s s') (next : IoppStage) (hK' : StageCodes s' next K) (h0 : s'.h = 0)
    (g0 : s'.g = 0) (dS dC : PQ.RD) (hr : CsRounds s s' dS dC)
    (τC : Tr (PQ.uL (ckP .two) [dS, dC])) (rest : List Fmt.RoundView) (q : GE × (s.cMid.J → GE))
    (n : Nat) (sh sh' : OracleShape) (pt : Fin (s.h + s.g) → GE) (d : PQ.RD)
    (m : (wRound d).Msg) (hN : PQ.posN d.tree = 2 ^ s.C.a)
    (hW : PQ.colW d.tree = 3 * 2 ^ (s.h + s.g) + 3 * (2 * 2 ^ s.h))
    (m1 : sh.mainRows = 2 ^ (s.h + s.g)) (m2 : sh.mainDeg = 3) (m3 : sh.maskRows = 2 ^ s.h)
    (f1 : sh'.mainRows = 0) (f3 : sh'.maskRows = 2 ^ s.h)
    (hbits : (Send.cube K
      (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1).shape).bits = s'.st.na)
    (hlay : ∀ lay, layTrees K (sentOf (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h
      1) (stageOthers true next [])) = some lay →
      ∃ shT : TreeShape, lay.shapes = #[shT] ∧ shT.logN = s'.C.a ∧
        (∀ i, i < 2 → lay.tree.getD i 0 = 0 ∧ lay.part.getD i 0 = i) ∧
        shT.mainSymbols = #[3, 3] ∧ shT.maskSymbols = #[3, 3]) :
    CsRuns true next []
      (SingleOn F
        (segOf (n - F) (listAt s.C.a dC τC.2.2.1 τC.2.2.2.1).all.toList (treeCol d m) ++ R) K roots
        s q (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest)
        (SingleFit s s' K next.code next.maskCode n [sh, sh'] #[some 0] #[some 0] pt))
      (LastOn F R K (roots + 1) s' next (csNextW hf dS dC q (wordMid s (colSt s d m.1) pt) τC)
        rest (F + roots)) :=
  csRuns_last_on F _ R K roots hf next hK' h0 g0 dS dC hr τC rest q _ _
    (fun _ _ _ _ hb ho _ ht => ht.congr hb ho) (fun _ _ ht => ht.ok) hbits hlay
    (fun c c' rows gp sw row' L' theta D hrun hop ht hran =>
      hread_stage_seg F K roots dS dC hr τC rest _ _ n sh sh' pt d m hN hW m1 m2 m3 f1 f3 _ _
        c c' rows gp sw row' L' theta D R hrun hop ht hran)

/-! ## The stages -/

/-- From the joint J, a run of the stage cur and the stages rest gives the goal, of the context that
the run leaves. Whether a named test has failed is for the goal to ask of that context. -/
def StagesTo (ride : Bool) (cur : IoppStage) (rest : List IoppStage) (J : GroupJoint)
    (Goal : Ctx → Prop) : Prop :=
  ∀ (answers : Nat) (c : Ctx) (row : GroupRow) (L : GroupLayout) (mask : Option Nat) (c' : Ctx),
    J answers c row L mask → (ioppStagesVerify answers ride cur rest row L mask).Yields c () c' →
    Goal c'

/-- A fold, a code switch and the stages that are left, joined. -/
theorem stagesTo_step (ride : Bool) (cur next : IoppStage) (rest : List IoppStage)
    (J J2 : GroupJoint) (J1 : SingleJoint) (Goal : Ctx → Prop) (hF : FoldRuns cur J J1)
    (hC : CsRuns ride next rest J1 J2) (hN : StagesTo ride next rest J2 Goal) :
    StagesTo ride cur (next :: rest) J Goal := by
  have tr : ∀ {a b c : Ctx}, Blk.SameButNotes a b → Blk.SameButNotes b c → Blk.SameButNotes a c :=
    fun h1 h2 =>
      ⟨h2.ch.trans h1.ch, h2.st.trans h1.st, h2.book.trans h1.book, h2.failed.trans h1.failed⟩
  intro answers c row L mask c' hJ hrun
  obtain ⟨rows1, a1, a2, to1, a3, s1, row1, L1, a4, a5, a6, a7, a8, mask1, f1, n1, g1, w1, n2, n3,
    n4, n5, hm1, r1⟩ := ioppStages_step_inv _ _ _ _ _ _ _ _ _ _ hrun
  have j1 : J1 answers a1 rows1 := hF answers c row L mask rows1 a1 hJ f1
  have j2 : J2 answers a8 row1 L1 mask1 :=
    hC answers a1 rows1 a2 to1 a3 s1 row1 L1 a4 a8 mask1 j1 (Blk.yields_note _ _ _ _ n1) g1 w1
      (tr (tr (tr (Blk.yields_note _ _ _ _ n2)
        (Blk.yields_noteBy _ _ _ _ n3)) (Blk.yields_note _ _ _ _ n4)) (Blk.yields_note _ _ _ _ n5))
      hm1
  exact hN answers a8 row1 L1 mask1 c' j2 r1

/-- From LastOn at a claim q, after a run of the program's last stage: if no named test has failed,
the library's decision on the base case (LdwAccept) accepts at q; and in any case the rounds and the
columns that are left are those behind the base case's. Asked: a stage without a row variable,
public facts on sizes, codes and draws, and that what is left to be read begins with the last
written tree's segment at the base case's positions. -/
theorem lastRuns_on (F : Nat) (R : Cols) (K : Codes) (roots : Nat) (s : Sg) (h0 : s.h = 0)
    (g0 : s.g = 0) (hza : s.Z.a ≤ s.C.a) (ha : s.C.a ≤ 32) (cur : IoppStage)
    (hK : StageCodes s cur K) (dS dL dB : PQ.RD) (mS : (wRound dS).Msg)
    (hW : PQ.colW dS.tree = 12) (hN : PQ.posN dS.tree = 2 ^ s.C.a)
    (τB : Tr (PQ.uL (ckP .two) [dL, dB])) (rest : List Fmt.RoundView) (q : GE × (s.cIn.J → GE)) (n : Nat)
    {nB : ℕ} (hB : SendsDraws dB nB 0 s.t s.C.a) :
    StagesTo true cur []
      (LastOn F
        (segOf (n - F) (listAt s.C.a dB τB.2.2.1 τB.2.2.2.1).all.toList (treeCol dS mS) ++ R) K
        roots s cur q (PQ.rvSL (ckP .two) [dL, dB] τB ++ rest) n)
      fun c' => (c'.failed = none →
        LdwAccept (ldCw s.cIn) (ldForm (Slf.idf (E := GE) (J := s.cIn.J)) q) q.1
          (s.cIn.T (wordIn s (lastColW dS mS.1))) (s.cIn.T (wordMk s (lastMk dS mS.1)))
          (lst (sentW dL τB.1) 0) (gOne _ (valsOf dL τB.2.1)) (shownW s (sentW dB τB.2.2.1))
          (gPos s.C.a s.t _ (valsOf dB τB.2.2.2.1))) ∧ c'.ch.pending = rest ∧ c'.ch.opened = R ∧
        c'.ch.roots = roots := by
  intro answers c row L mask c' hJ hrun
  obtain ⟨o, star, sh, sh', hL, rfl, k1, k2, hseat⟩ := hJ.seat
  obtain ⟨cd, hcd, hC⟩ := hK.base
  have hlog : cd.logN = s.C.a := congrArg (·.a) hC
  obtain ⟨t, tree, xo, xs, hn, hb⟩ := lastBook_of_seat c o star n s.C.a sh sh' k1 k2 hseat
  obtain ⟨x1, xc, xd⟩ := claim_of_stmGk s row
  rw [hJ.claim] at x1 xc xd
  have hop : c.ch.opened = segOf (tree.number - c.ch.firstTree)
      (listAt s.C.a dB τB.2.2.1 τB.2.2.2.1).all.toList (treeCol dS mS) ++ R := by
    rw [hn, hJ.run.first]
    exact hJ.opened
  obtain ⟨l1, l2, l3⟩ := ioppLast_left s answers true cur row L o star hL dS dL dB mS hN τB.1 τB.2.1
    τB.2.2.1 τB.2.2.2.1 rest c c' hJ.run.dry hJ.run.pending hrun hB cd
    (by rw [hJ.run.codes]; exact hcd) hC t tree xo xs (by rw [hlog]; exact hb) R hop
  exact ⟨fun hfail => ioppLast_seg s h0 g0 hza ha answers true cur row L o star hL dS dL dB mS hW hN
      τB.1 τB.2.1 τB.2.2.1 τB.2.2.2.1 rest c c' hJ.run.dry hJ.run.pending hrun hfail hB cd
      (by rw [hJ.run.codes]; exact hcd) hC (by rw [hJ.run.codes]; exact hK.mask) q x1 xc xd hJ.fix
      t tree xo xs (by rw [hlog]; exact hb) R hop hJ.kept hJ.mainFirst hJ.maskFirst,
    l1, l2, l3.trans hJ.run.roots⟩

end OnBytes.Slice.ProxRun

namespace OnBytes.Slice.Chain
open Iop Prob Cb Cb.Ood _root_.Run
open Params (IoppStage)
open OnBytes.Slice.ProxRun

/-- The written rounds as a view shows them, block by block, and then the rounds tail. -/
def rvsT : {s : Sg} → (c : Chain s) → c.Bl → List Fmt.RoundView → List Fmt.RoundView
  | _, .last _ _ dL dB _ _ _ => fun τ tail => PQ.rvSL (ckP .two) [dL, dB] τ ++ tail
  | _, .step s _ _ _ _ dE dT dS dC _ _ _ _ _ next => fun b tail =>
    PQ.rvSL (ckP .two) (foldRds s dE dT) b.1 ++
      (PQ.rvSL (ckP .two) [dS, dC] b.2.1 ++ next.rvsT b.2.2 tail)

/-- The chain's rounds, and then the others. -/
theorem rvsT_eq {s : Sg} (c : Chain s) : ∀ (b : c.Bl) (tail : List Fmt.RoundView),
    c.rvsT b tail = c.rvs b ++ tail := by
  induction c with
  | last s e dL dB fu fs εb => exact fun _ _ => rfl
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    intro b tail
    show _ ++ (_ ++ next.rvsT b.2.2 tail) = (_ ++ (_ ++ next.rvs b.2.2)) ++ tail
    rw [ih, List.append_assoc, List.append_assoc]

/-- The opened columns that a run along the chain reads, as a view lists them, and then the columns
R. n: the key of the tree of the chain's first stage. d, m: the written round that sent that tree,
and its message. A stage's tree is opened at the positions of the code switch after its fold, the
last stage's tree at the base case's positions. -/
def colsT : {s : Sg} → (c : Chain s) → ℕ → (d : PQ.RD) → (wRound d).Msg → c.Bl → Cols → Cols
  | _, .last s _ _ dB _ _ _ => fun n d m τ R =>
    segOf n (listAt s.C.a dB τ.2.2.1 τ.2.2.2.1).all.toList (treeCol d m) ++ R
  | _, .step s _ _ _ _ _ _ dS dC _ _ _ _ _ next => fun n d m b R =>
    segOf n (listAt s.C.a dC b.2.1.2.2.1 b.2.1.2.2.2.1).all.toList (treeCol d m) ++
      next.colsT (n + 1) dS b.2.1.1 b.2.2 R

/-- Each tree that is folded has as many positions as its stage's code. d: the written round that
sent the tree of the chain's first stage. -/
def Deep : {s : Sg} → Chain s → PQ.RD → Prop
  | _, .last _ _ _ _ _ _ _ => fun _ => True
  | _, .step s _ _ _ _ _ _ dS _ _ _ _ _ _ next => fun d =>
    PQ.posN d.tree = 2 ^ s.C.a ∧ next.Deep dS

/-- The joint before the chain's first stage, if a code switch has sent the stage's tree. F: the
number of the first tree that the chain of rounds sends. n: the tree's key, so that its number is
F + n, and n + 1 roots have been received. cur: the program's stage. q: the claim. d, m: the written
round that sent the tree, and its message. b: the blocks' transcripts. tail, R: the rounds and the
opened columns behind the test. -/
def JointTail (F : Nat) (K : Codes) : {s : Sg} → (c : Chain s) → ℕ → IoppStage →
    GE × (s.cIn.J → GE) → (d : PQ.RD) → (wRound d).Msg → c.Bl → List Fmt.RoundView → Cols → GroupJoint
  | _, .last s _ dL dB _ _ _ => fun n cur q d m τ tail R =>
    LastOn F (segOf n (listAt s.C.a dB τ.2.2.1 τ.2.2.2.1).all.toList (treeCol d m) ++ R) K (n + 1)
      s cur q (PQ.rvSL (ckP .two) [dL, dB] τ ++ tail) (F + n)
  | _, .step s _ _ _ _ dE dT dS dC _ _ _ _ _ next => fun n cur q d m b tail R =>
    GroupOn F
      (segOf n (listAt s.C.a dC b.2.1.2.2.1 b.2.1.2.2.2.1).all.toList (treeCol d m) ++
        next.colsT (n + 1) dS b.2.1.1 b.2.2 R) K (n + 1) s q
      (PQ.rvSL (ckP .two) (foldRds s dE dT) b.1 ++
        (PQ.rvSL (ckP .two) [dS, dC] b.2.1 ++ next.rvsT b.2.2 tail))
      (GroupTie s (F + n) (stageShapes s cur) #[some 0] #[some 0])

/-- The number of code switches of a chain. -/
def switches : {s : Sg} → Chain s → ℕ
  | _, .last _ _ _ _ _ _ _ => 0
  | _, .step _ _ _ _ _ _ _ _ _ _ _ _ _ _ next => next.switches + 1

/-- The number of roots that have been received behind a chain whose first stage's tree, which a
code switch has sent, has the key n: each code switch sends one tree. -/
def rootsEnd : {s : Sg} → Chain s → ℕ → ℕ
  | _, .last _ _ _ _ _ _ _ => fun n => n + 1
  | _, .step _ _ _ _ _ _ _ _ _ _ _ _ _ _ next => fun n => next.rootsEnd (n + 1)

/-- One root for each code switch. -/
theorem rootsEnd_eq {s : Sg} (c : Chain s) : ∀ n, c.rootsEnd n = n + 1 + c.switches := by
  induction c with
  | last s e dL dB fu fs εb => exact fun _ => rfl
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    intro n
    show next.rootsEnd (n + 1) = n + 1 + (next.switches + 1)
    rw [ih]
    omega

/-- A chain has as many written rounds as the program's stages close, under the public facts. -/
theorem rounds_eq {K : Codes} {s : Sg} (c : Chain s) : ∀ (cur : IoppStage)
    (rest : List IoppStage), c.Pub K cur rest → c.rds.length = stagesRounds cur rest := by
  induction c with
  | last s e dL dB fu fs εb =>
    intro cur rest h
    rw [h.1]
    rfl
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    intro cur rest h
    obtain ⟨nx, later, rfl, hS, _, _, hN⟩ := h
    show (foldRds s dE dT ++ ([dS, dC] ++ next.rds)).length = cur.k + 1 + 2 + stagesRounds nx later
    rw [List.length_append, List.length_append, ih nx later hN, hS.codes.k]
    show (dE :: List.replicate (s.h + s.g) dT).length + (2 + _) = _
    rw [List.length_cons, List.length_replicate]
    omega

end OnBytes.Slice.Chain

namespace OnBytes.Slice.ProxRun
open Iop Prob Cb Cb.Ood _root_.Run
open Params (IoppStage)

/-- The code switch after the fold of a stage s whose tree a code switch has sent leads to the joint
before the chain next. n: the key of the tree of s. d, m: the written round that sent it, and its
message. pt: the point of the fold. -/
theorem csRuns_later_on (F : Nat) (K : Codes) (n : ℕ) {s s' : Sg} (hf : CsFit s s')
    (cur nx : IoppStage) (later : List IoppStage) (next : Chain s') (n0 : ℕ) (dS dC : PQ.RD)
    (hP : StepPub K s s' cur nx n0 dS dC) (hO : next.Own K nx dS) (hN : next.Pub K nx later)
    (τC : Tr (PQ.uL (ckP .two) [dS, dC])) (b : next.Bl) (tail : List Fmt.RoundView) (R : Cols)
    (q : GE × (s.cMid.J → GE)) (pt : Fin (s.h + s.g) → GE) (d : PQ.RD) (m : (wRound d).Msg)
    (hD : PQ.posN d.tree = 2 ^ s.C.a)
    (hW : PQ.colW d.tree = 3 * 2 ^ (s.h + s.g) + 3 * (2 * 2 ^ s.h)) :
    CsRuns true nx later
      (SingleOn F
        (segOf n (listAt s.C.a dC τC.2.2.1 τC.2.2.2.1).all.toList (treeCol d m) ++
          next.colsT (n + 1) dS τC.1 b R) K (n + 1) s q
        (PQ.rvSL (ckP .two) [dS, dC] τC ++ next.rvsT b tail)
        (SingleFit s s' K nx.code nx.maskCode (F + n) (stageShapes s cur) #[some 0] #[some 0] pt))
      (next.JointTail F K (n + 1) nx (csNextW hf dS dC q (wordMid s (colSt s d m.1) pt) τC) dS τC.1
        b tail R) := by
  have f3 : (foldMaskNotice (ioppFoldShape cur {})).shape.maskRows = 2 ^ s.h := by
    show 2 ^ cur.h = 2 ^ s.h
    rw [hP.codes.h]
  have hK' := hN.codes
  have hkey : F + n - F = n := by omega
  cases next with
  | last s' e dL dB fu fs εb =>
    obtain ⟨rfl, _⟩ := hN
    have h := csRuns_second_on F (Chain.colsT (.last s' e dL dB fu fs εb) (n + 1) dS τC.1 b R) K
      (n + 1) hf nx hK' hO.h0 hO.g0 dS dC hP.rounds τC
      (Chain.rvsT (.last s' e dL dB fu fs εb) b tail) q (F + n)
      (switchTargetStage cur.code cur.maskCode (s.h + s.g) s.h 1).shape
      (foldMaskNotice (ioppFoldShape cur {})).shape pt d m hD hW rfl rfl rfl rfl f3 hP.bits hO.lay
    rw [hkey] at h
    exact h
  | step s' s'' hf' n0' e dE dT dS' dC' fW fZ fG εf εc next' =>
    obtain ⟨n3, later', rfl, _⟩ := hN
    have h := csRuns_middle_on F
      (Chain.colsT (.step s' s'' hf' n0' e dE dT dS' dC' fW fZ fG εf εc next') (n + 1) dS τC.1 b R)
      K (n + 1) hf nx n3 later' hK' hO.k1 dS dC hP.rounds τC
      (Chain.rvsT (.step s' s'' hf' n0' e dE dT dS' dC' fW fZ fG εf εc next') b tail) q (F + n)
      (switchTargetStage cur.code cur.maskCode (s.h + s.g) s.h 1).shape
      (foldMaskNotice (ioppFoldShape cur {})).shape pt d m hD hW rfl rfl rfl rfl f3 hP.bits hO.one
    rw [hkey] at h
    exact h

/-- The stages, along a chain. A run of the program's stages cur :: rest leads from the joint
before the chain c to the chain's yes in the field, if no named test has failed after it; and in any
case the rounds and the opened columns that are left are those behind the test. Asked: the public
facts Pub, Own and Deep. n: the key of the tree of the chain's first stage. d, m: the written round
that sent it, and its message. y, z, g: its standard readings. -/
theorem stagesTo_chain (F : Nat) (K : Codes) {s : Sg} (c : Chain s) :
    ∀ (n : ℕ) (cur : IoppStage) (rest : List IoppStage) (d : PQ.RD) (m : (wRound d).Msg)
      (q : GE × (s.cIn.J → GE)) (y : s.cIn.Word) (z : s.cFr.Word) (g : s.cIn.Word) (b : c.Bl)
      (tail : List Fmt.RoundView) (R : Cols),
      c.Pub K cur rest → c.Own K cur d → c.Deep d → c.ReadAs d m y z g →
      StagesTo true cur rest (c.JointTail F K n cur q d m b tail R)
        fun c' => (c'.failed = none → c.Acc q y z g b) ∧ c'.ch.pending = tail ∧
          c'.ch.opened = R ∧ c'.ch.roots = c.rootsEnd n := by
  induction c with
  | last s e dL dB fu fs εb =>
    intro n cur rest d m q y z g τ tail R hP hO _ hR
    obtain ⟨rfl, hL⟩ := hP
    obtain ⟨rfl, rfl⟩ := hR
    obtain ⟨nB, hB⟩ := hL.draws
    have h := lastRuns_on F R K (n + 1) s hO.h0 hO.g0 hL.za hL.small cur hL.codes d dL dB m hO.w
      hO.n τ tail q (F + n) hB
    rw [Nat.add_sub_cancel_left, ← hL.fu, ← hL.fs] at h
    exact h
  | step s s' hf n0 e dE dT dS dC fW fZ fG εf εc next ih =>
    intro n cur rest d m q y z g b tail R hP hO hD hR
    obtain ⟨nx, later, rfl, hSt, hO', hR', hN⟩ := hP
    obtain ⟨rfl, rfl⟩ := hR
    obtain rfl := hSt.n0
    have hF := foldRuns_on F
      (segOf n (listAt s.C.a dC b.2.1.2.2.1 b.2.1.2.2.2.1).all.toList (treeCol d m) ++
        next.colsT (n + 1) dS b.2.1.1 b.2.2 R) K (n + 1) s cur hSt.codes dE dT q b.1
      (PQ.rvSL (ckP .two) [dS, dC] b.2.1 ++ next.rvsT b.2.2 tail) _ _
      (foldTies_on K s s' cur hSt.codes nx.code nx.maskCode (F + n) (stageShapes s cur) #[some 0]
        #[some 0] (foldPt s dE dT b.1) _ hSt.zk hSt.c' hSt.z' hSt.small)
    have hC := csRuns_later_on F K n hf cur nx later next s.Z.l dS dC hSt hO' hN b.2.1 b.2.2 tail R
      (foldNext s s.Z.l dE dT q b.1) (foldPt s dE dT b.1) d m hD.1 hO.w
    have hI := ih (n + 1) nx later dS b.2.1.1
      (csNextW hf dS dC (foldNext s s.Z.l dE dT q b.1)
        (wordMid s (colSt s d m.1) (foldPt s dE dT b.1)) b.2.1)
      (fW b.2.1.1) (fZ b.2.1.1) (fG b.2.1.1) b.2.2 tail R hN hO' hD.2 (hR' _)
    rw [← foldWords_std] at hI
    exact stagesTo_step true cur nx later _ _ _ _ hF hC hI

end OnBytes.Slice.ProxRun
