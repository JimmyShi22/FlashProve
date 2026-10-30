-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/LastBehindAny.lean: behind an accepted LAST code switch of the proximity test
and the batching behind it, the form's half at the last stage (`LastForm`,
Johnson/Prover/Link/FormInv.lean) holds, WHATEVER TREES THE OLD ROWS STOOD IN.

Why. `lastForm_next` (Johnson/Prover/Link/FormClose.lean) says the like at written states, where the
old rows stood in one tree. `formInv_any` (Johnson/Prover/Link/FormBehindAny.lean) serves a switch
behind which a fold follows; this file serves the switch into the last stage.

Main names (namespace `Johnson.Prover.Link`).
  `LastSwitchPlan p K j cur next n`   a premise: what is public at the last switch; no clause on an
      old tree. `StepPlan.lastSwitchPlan`: `StepPlan` at the last switch gives it
  `lastForm_any`   the statement: the state behind passes a claim at a layout of one row variable
      and no mask variable, and `LastForm` holds there

Kin. `LastSwitchPlan` has ten clauses of `SwitchPlan` (FormBehindAny.lean), two of them at the last
switch's announcements, and the label.

Limits. The two acceptances, `LastSwitchPlan`, `SwitchIn` and the last stage's `LastPlan` are asked.
At old rows in several trees nothing here meets `SwitchIn` or the two acceptances. Of any layout of
trees, not of rows.
Nothing on values or on soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormBehindAny
import Johnson.Prover.Link.FormLast

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw
open H2K.Pub (sgOf)

/-- **What is public at the last switch**: no clause on an old tree. -/
structure LastSwitchPlan (p : P12) (K : Codes) (j : ℕ) (cur next : Fmt.M1.Stage) (n : IoppStage) :
    Prop where
  early : p.early = true
  one : p.answers = 1
  stageN : stageAt p (j + 1) next = some n
  fits : CsFit (sgOf cur) (sgOf next)
  codeN : (K.base[n.code]?).map codeOf = some (sgOf next).C
  zkN : (K.mask[n.maskCode]?).map codeOf = some (sgOf next).Z
  nk : n.k = (sgOf next).h + (sgOf next).g
  nh : n.h = (sgOf next).h
  lengths : K.lengthsOk = true
  bounds : 2 ^ ((sgOf next).h + (sgOf next).g) * (sgOf next).C.l ≤ 2 ^ 63 ∧
    2 ^ (sgOf next).h * (sgOf next).Z.l ≤ 2 ^ 63
  trees : Own.treesCan K (swNotices p n true) = true
  oneTree : OneTree K (OnBytes.Slice.sentOf (swTarget p n) (othersOf true n)) (sgOf next).C.a
  label : p.nums.firstTree + (p.nums.free + j) = (basePar p next).label

theorem StepPlan.lastSwitchPlan {p : P12} {K : Codes} {j : ℕ} {cur next : Fmt.M1.Stage} {l : Laid}
    {c n : IoppStage} {dS dC : Fmt.DeclaredRound} (Pl : StepPlan p K j cur next true l c n dS dC) :
    LastSwitchPlan p K j cur next n :=
  ⟨Pl.early, Pl.one, Pl.stageN, Pl.fits, Pl.codeN, Pl.zkN, Pl.nk, Pl.nh, Pl.lengths, Pl.bounds,
    Pl.trees, Pl.oneTree, Pl.label rfl⟩

/-- **`LastForm` behind the last switch, whatever trees the old rows stood in.** -/
theorem lastForm_any {p : P12} {j : ℕ} {cur next : Fmt.M1.Stage} {l' : Laid} {n : IoppStage}
    {d₁ d₂ : Fmt.DeclaredRound} {gp : ℕ} {t1 t2 t3 : T12} {rows : SingleRows}
    {rS rC : Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} {cut : List Fmt.DeclaredRound}
    (Pl : LastSwitchPlan p t1.st.codes j cur next n)
    (In : SwitchIn p j cur next n gp t1 rows rC)
    (h2 : (switchJ p j cur next true cut).decide t1 [rS, rC] gs = .ok t2)
    (h3 : (behindJ p (j + 1) next cut).decide t2 [] [] = .ok t3)
    (Lp : LastPlan p t1.st.codes (j + 1) next l' n d₁ d₂) :
    ∃ row' lay, t3.pass = .claim row' lay ∧ lay.k = 1 ∧ lay.h = 0 ∧
      LastForm p (j + 1) next t3 row' lay n
        ⟨dense (row'.c.fixLow [zeroE]) (ceilLog2 next.C.l), row'.d.map (·.triple),
          row'.target.triple⟩
        t1.st.oracles.size (t1.st.oracles.size + 1) t1.book.trees.size := by
  obtain ⟨out, row', lay, theta, D, -, hrC, hd0, hp3, hm3⟩ :=
    switchUnfolds p j cur next true cut t1 t2 t3 rS rC gs rows _ n Pl.early Pl.one In.pass
      Pl.stageN h2 h3
  have hG : D.G = { code := n.code, maskCode := n.maskCode } := group_did hd0 In.group
  have hm : D.G.members = #[] := by rw [hG]
  have hk : D.G.kept = #[] := by rw [hG]
  have hr : D.G.rows = #[] := by rw [hG]
  have eh : n.h = 0 := Pl.nh.trans Lp.h0
  have eT0 : swTarget p n = switchTargetStage n.code n.maskCode n.k n.h 1 := by
    unfold swTarget
    rw [Pl.one]
  have eT : swTarget p n = switchTargetStage n.code n.maskCode 0 0 1 := by
    rw [eT0, Lp.k0, eh]
  have hd : Did p.nums.firstTree (keyed p cut gs) rows (swTarget p n) gp
      (othersOf true n) t1.st t1.book t1.roots t3.st t3.book out row' lay theta D := by
    rw [eT0]
    exact hd0
  have hdT := hd
  rw [eT] at hdT
  have hdS := hd0
  rw [Pl.nk, Pl.nh] at hdS
  -- the statement stays in order
  have hfit : Blk.shapeOk t1.st.codes (swTarget p n).shape = true := by
    have h := recv_of (p := p) (n := n) (last := true) t1.st t1.book (lt_of_map_some Pl.codeN)
      (lt_of_map_some Pl.zkN) Pl.trees hd0.places
    simp only [Ground.ok, Ground.recvL, Ground.sentL, List.all_append, List.all_cons,
      List.all_nil, Bool.and_true, Bool.and_eq_true] at h
    have h1 := h.1.1
    rw [swNotices_eq, Array.all_eq_true_iff_forall_mem] at h1
    exact h1 ⟨(swTarget p n).shape, (swTarget p n).leafClass⟩ (by simp)
  rw [eT0, Pl.nk, Pl.nh] at hfit
  obtain ⟨hORs, -⟩ := inOrder_did Pl.fits hdS In.ff hG Pl.bounds In.cfits In.dense
    (by rw [hrC]; exact In.range) In.order Pl.lengths hfit
  have hOR : Means.InOrder (D.stR (switchTargetStage n.code n.maskCode 0 0 1) gp
      (othersOf true n) t1.st) := by
    rw [← Pl.nk, ← Pl.nh, Lp.k0, eh] at hORs
    exact hORs
  have hlay := hdT.lay_eq hm hk
  obtain ⟨sh, l1, l2, l3, l4, l5⟩ := Pl.oneTree D.lay hd.trees
  have hR := readSeat_did hd sh rfl l1
    (fun i hi => l3 i (by
      show i < 2
      exact hi))
    (by
      show p.answers ≠ 0
      rw [Pl.one]
      exact Nat.one_ne_zero) rfl In.old
  have hp' := dense_behind hd In.ff.kept In.ff.prog.masks In.ff.prog.noKept hm hr In.dense
  have hzk : sh.logNzk = next.Z.a := by
    have h0 := logNzk_of_trees t1.st.codes (swTarget p n) (othersOf true n) D.lay sh hd.trees l1
      (l3 0 (by simp [OnBytes.Slice.sentOf])).1 (Nat.two_pow_pos _)
    rw [h0]
    exact congrArg (·.a) (getD_of_map_some Pl.zkN)
  have hsh : sh = ⟨next.C.a, next.Z.a, #[3, 3], #[3, 3]⟩ := by
    rw [eT] at l4 l5
    cases sh with
    | mk a1 a2 a3 a4 =>
      have b1 : a1 = next.C.a := l2
      have b2 : a2 = next.Z.a := hzk
      have b3 : a3 = #[3, 3] := l4
      have b4 : a4 = #[3, 3] := l5
      rw [b1, b2, b3, b4]
  obtain ⟨f1, f2, f3⟩ := five_behind Pl.fits hdT hG Pl.zkN hp'
  refine ⟨row', lay, hp3, by rw [hlay]; rfl, by rw [hlay], ?_⟩
  exact
    { front := baseFront_behind hdT hG hOR rfl rfl hp3 hm3 Lp.stage Lp.k0 Pl.codeN Pl.zkN hp'
        Lp.small _ _ hR (by
          show p.nums.firstTree + t1.roots = _
          rw [In.roots]
          exact Pl.label) hsh
      st := Lp.st, h0 := Lp.h0, g0 := Lp.g0, pow := f1, dSize := f2, fix := f3 }

end Johnson.Prover.Link
