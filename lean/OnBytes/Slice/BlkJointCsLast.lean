-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkJointCsLast.lean: a run of the program's last code switch leads from the joint
after a fold to the joint before the base case.

OnBytes/Slice/BlkJointCsAt.lean treats a code switch into a stage that is folded again. This file
treats the switch into the last stage, which has one main row and one mask row. The program's last
group has one row variable, so the claim is read with the group's own numbers of row bits. The new
tree holds the last stage's oracle message and the masking oracle of the base case
(OnBytes/Slice/BlkCsSeat.lean). That the program's fixing of the row variable picks the first row
follows from the shape of the new row's form (OnBytes/Slice/BlkCsTie.lean, BaseGk.lean).

Main theorems.
 `LastAt.notes`   keeping a value changes nothing that the joint before the base case says.
 `csRuns_last`    the statement of OnBytes/Slice/BlkChain.lean on a code switch, from `SingleAt` at
                  a claim q to `LastAt` at `csNextW` of q.

Not claimed. What `csRuns_last` asks, as hypotheses with names, is not shown here. `hOk`, `hread`:
as in BlkJointCsAt.lean. And public facts on sizes, among them how the two oracle messages of the
switch's message are placed in one tree (`hlay`). Nothing on soundness.
-/
import OnBytes.Slice.BlkCsTie
import OnBytes.Slice.BlkJointCsAt
import OnBytes.Slice.BlkJointLast

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Cb Cb.Ood _root_.Run
open Params (IoppStage)

/-- Keeping a value changes nothing that the joint before the base case says. -/
theorem LastAt.notes {V : Fmt.View} {K : Codes} {roots : Nat} {s : Sg} {cur : IoppStage}
    {q : GE × (s.cIn.J → GE)} {rest : List Fmt.RoundView} {n a : Nat} {c c' : Ctx} {row : GroupRow}
    {L : GroupLayout} {m : Option Nat} (h : LastAt V K roots s cur q rest n a c row L m)
    (hn : Blk.SameButNotes c c') : LastAt V K roots s cur q rest n a c' row L m := by
  obtain ⟨o, star, sh, sh', h1, h2, h3, h4, h5⟩ := h.seat
  refine ⟨h.run.notes hn, h.claim, h.fix, h.kept, h.mainFirst, h.maskFirst, o, star, sh, sh',
    h1, h2, h3, h4, h5.keeps (BookKeeps.of_eq hn.book) ?_⟩
  rw [hn.st]
  exact ShapesKeep.refl _

/-- A run of the program's last code switch leads from the joint after a fold to the joint before
the base case. s, s': the two stages, the second without a row variable (`h0`, `g0`). y: the three
folded words. The file's head names the other hypotheses. -/
theorem csRuns_last (V : Fmt.View) (K : Codes) (roots : Nat) {s s' : Sg} (hf : CsFit s s')
    (next : IoppStage) (hK' : StageCodes s' next K) (h0 : s'.h = 0) (g0 : s'.g = 0)
    (dS dC : PQ.RD) (hr : CsRounds s s' dS dC) (τC : Tr (PQ.uL (ckP .two) [dS, dC]))
    (rest : List Fmt.RoundView) (q : GE × (s.cMid.J → GE)) (y : s.cMid.Word)
    (Tie : Ctx → SingleRows → Prop)
    (hTie : ∀ (c c' : Ctx) (rows : SingleRows), c'.ch = c.ch → c'.book = c.book →
      c'.st.oracles = c.st.oracles → c'.st.codes = c.st.codes → Tie c rows → Tie c' rows)
    (hOk : ∀ (c : Ctx) (rows : SingleRows), Tie c rows →
      FoldedOk s s' K next.code next.maskCode rows)
    (hbits : (Send.cube K
      (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1).shape).bits = s'.st.na)
    (hlay : ∀ lay, layTrees K (sentOf (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h
      1) (stageOthers true next [])) = some lay →
      ∃ sh : TreeShape, lay.shapes = #[sh] ∧ sh.logN = s'.C.a ∧
        (∀ i, i < 2 → lay.tree.getD i 0 = 0 ∧ lay.part.getD i 0 = i) ∧
        sh.mainSymbols = #[3, 3] ∧ sh.maskSymbols = #[3, 3])
    (hread : ∀ (c c' : Ctx) (rows : SingleRows) (gp : Nat) (sw : Switched) (row' : GroupRow)
      (L' : GroupLayout) (theta : E) (D : CsTaken),
      RunAt V K roots (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest) 1 c → Tie c rows →
      CsRan rows (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1) gp
        (stageOthers true next []) c c' sw row' L' theta D →
      ∀ i α, s.cMid.T y ((gCs s.C.a s.t _ (valsOf dC τC.2.2.2.1)).1 i) α =
        symS s rows sw.positions D.y ((gCs s.C.a s.t _ (valsOf dC τC.2.2.2.1)).1 i).val α) :
    CsRuns true next []
      (SingleAt V K roots s q (PQ.rvSL (ckP .two) [dS, dC] τC ++ rest) Tie)
      (LastAt V K (roots + 1) s' next (csNextW hf dS dC q y τC) rest roots) := by
  refine csRuns_of V K roots s true next [] dS dC τC rest q Tie _ hTie
    (fun a c c' row L m hn hJ => hJ.notes hn) ?_
  intro c c' rows gp sw row' L' theta D mask hrun hq ht hg hran hrun' hmask
  rw [hK'.k, hK'.h] at hran
  have hG := csRan_group hran hg
  have ok := hOk c rows ht
  have hcl := csRan_claim hf dS dC hr τC rest hran hrun.pending
    (by rw [hrun.codes]; exact ok.prog) ok.kept hG ok.d0 ok.d1 ok.vars
    (by rw [hrun.codes]; exact hbits) y (hread c c' rows gp sw row' L' theta D hrun ht hran)
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
  have hpl : PlainForm row'.c :=
    hran.plain ok.kept ok.prog.masks ok.prog.noKept (by rw [hG]) (by rw [hG]) ok.plain
  refine ⟨hrun', ?_, fixLaw_of_plain _ hpl (hran.vars (by rw [hG]) (by rw [hG]) (by rw [hG])),
    by rw [hL]; rfl, by rw [hL]; rfl, by rw [hL]; rfl,
    c.st.oracles.size, c.st.oracles.size + 1,
    (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1).shape,
    (baseMaskNotice next.code next.maskCode 1 0).shape, by rw [hL], hstar, ⟨p0, rfl, p1⟩,
    ⟨rfl, rfl, rfl⟩, ?_⟩
  · rw [← hk, ← hh, hcl, hq]
  · rw [hrun.onView.first, Nat.zero_add, hrun.roots, l2] at hseat
    have e : (List.range (sentOf (switchTargetStage next.code next.maskCode (s'.h + s'.g) s'.h 1)
        (stageOthers true next [])).size).map (· + c.st.oracles.size)
        = [c.st.oracles.size, c.st.oracles.size + 1] := by
      show [0 + c.st.oracles.size, 1 + c.st.oracles.size] = _
      rw [Nat.zero_add, Nat.add_comm 1]
    rw [e] at hseat
    exact hseat

end OnBytes.Slice

#print axioms OnBytes.Slice.LastAt.notes
#print axioms OnBytes.Slice.csRuns_last
