-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Prover/Link/FormClose.lean: the form's half of the invariant of the stages of a proximity
test closes: what rides in front of a fold pays the reading of the old tree at the switch, and
stands again behind the stage.

Main names (namespace `Johnson.Prover.Link`).
  `keyed_one`   the columns with their keys, where "SEND seed" opens no tree and "CS" one
  `read_of_inv`   `StepPlan` · `FormInv` · the fold's rounds are one and one for each row variable ·
      the positions are in range · the group dealt is the written column at the list of the
      positions: then the old tree can be read behind the fold (`ReadFront`), for all letters D
  `code_of_map`   an entry of a list of codes, from its three numbers
  `formInv_next`   behind a stage whose next stage is not the last: `FormInv` at the next stage,
      with the layout's form (`LayAt`) and the new tree's seat in the soundness side's form
      (`SeatP`)
  `lastForm_next`   behind the stage in front of the last: `LastForm` at the last stage, with the
      claim written out

Limits. Every premise is asked; in `lastForm_next` two facts on the plan stand as premises of their
own: the last tree's declared label, and the depth of the last tree's mask rows. Nothing on
soundness.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FormStep
import Johnson.Prover.Link.FormLeft
import Johnson.Prover.Link.ReadNew
import Johnson.Prover.Link.DeclTree
import Johnson.Prover.Link.FormRoomsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Prover.Link
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Sw
open H2K.Pub (sgOf)

/-- The columns with their keys, where the first round opens no tree and the second one. -/
theorem keyed_one (p : P12) (dS dC : Fmt.DeclaredRound) (o : Told) (g : List (ℕ × List UInt64))
    (hS : dS.opens = []) (hC : dC.opens = [o]) :
    keyed p [dS, dC] [g] = g.map fun c => (o.1.tree - p.nums.firstTree, c.1, c.2) := by
  unfold keyed
  simp [hS, hC]

/-- **The old tree can be read behind the fold.** -/
theorem read_of_inv {p : P12} {j : ℕ} {cur next : Fmt.M1.Stage} {last : Bool} {l : Laid}
    {c n : IoppStage} {dS dC : Fmt.DeclaredRound} {t : T12} {col : ℕ → List UInt64} {row : GroupRow}
    {L : GroupLayout} {id tN : ℕ} {tr : Tree}
    (Pl : StepPlan p t.st.codes j cur next last l c n dS dC)
    (I : FormInv p j cur l t col row L c (n.code, n.maskCode) id tN tr) (rE : Fmt.RoundView)
    (rR : List Fmt.RoundView) (hR : rR.length = c.k) (rC : Fmt.RoundView)
    (hx : ∀ x ∈ rC.drawn.poss, x < 2 ^ (sgOf cur).C.a) (D : Taken) :
    ReadFront
      (swIn p n last dS dC (foldT t row L c (n.code, n.maskCode) id (rE :: rR)) rC
        [(Fmt.listOf (rC.drawn.poss.map (· % 2 ^ (sgOf cur).C.a))).map fun x => (x, col x)]
        (foldOut t row L c id (rE :: rR)) t.st.groups.size D)
      (Positions.ofDraws (sgOf cur).C.a rC.drawn.poss) tN tr := by
  obtain ⟨o, ho, o1, -, -⟩ := I.decl dS dC Pl.cutS
  have hkey := keyed_one p dS dC o
    ((Fmt.listOf (rC.drawn.poss.map (· % 2 ^ (sgOf cur).C.a))).map fun x => (x, col x)) Pl.opensS ho
  rw [List.map_map] at hkey
  obtain ⟨d1, d2⟩ := dealt_stand (tr.number - p.nums.firstTree)
    (tr.shape.mainWidth + tr.shape.maskWidth) (sgOf cur).C.a rC.drawn.poss col hx I.width
  refine readFront_sent _ _ (foldT t row L c (n.code, n.maskCode) id (rE :: rR)).st
    (spent t.st id) t.book L.members.toList id tN tr (I.seat.fold id n.code n.maskCode)
    p.nums.firstTree t.roots (swTarget p n) (othersOf last n) D rfl rfl (ioppFoldShape c L) row
    (drawnOf rE) (rR.map drawnOf) _ rfl (by simp [ioppFoldShape])
    (fun w => (noKept_all I.front I.keptL w : L.kept.getD w false = false))
    (shapeFits_foldOut I.front rE rR hR) I.log ?_ ?_
    (roomZ_at_foldT I.front _) (roomM_at_foldT I.front I.keptL _) (fresh_at_foldT I.front _)
  · show (keyed p [dS, dC] _).length = _
    rw [hkey, o1]
    exact d1
  · show Own.colsStand _ _ (keyed p [dS, dC] _) _ = true
    rw [hkey, o1]
    exact d2

/-- An entry of a list of codes, from its three numbers. -/
theorem code_of_map {A : Array OnBytes.Code} {i : ℕ} {C : Fmt.M1.Code}
    (h : (A[i]?).map codeOf = some C) : A[i]? = some ⟨C.a, C.l, C.r⟩ := by
  cases hz : A[i]? with
  | none => rw [hz] at h; cases h
  | some z =>
    rw [hz] at h
    obtain rfl := Option.some.inj h
    rfl

/-- **Behind a stage whose next stage is not the last, the form's half stands again.** -/
theorem formInv_next {p : P12} {j : ℕ} {cur next nx : Fmt.M1.Stage} {last' : Bool} {l : Laid}
    {c n n' : IoppStage} {dS dC dS' dC' : Fmt.DeclaredRound} {t : T12} {col : ℕ → List UInt64}
    {row : GroupRow} {L : GroupLayout} {id tN : ℕ} {tr : Tree} {rs : List Fmt.RoundView}
    {rS rC : Fmt.RoundView} {gs : List (List (ℕ × List UInt64))} {a x : Fmt.Ext} {D : Taken}
    {row' : GroupRow} (Pl : StepPlan p t.st.codes j cur next false l c n dS dC)
    (I : FormInv p j cur l t col row L c (n.code, n.maskCode) id tN tr)
    (Dn : StepDone (sgOf cur) (sgOf next) p n false dS dC
      (foldT t row L c (n.code, n.maskCode) id rs) rS rC gs (foldOut t row L c id rs)
      t.st.groups.size j cur next tN a D x row')
    (Pl' : StepPlan p t.st.codes (j + 1) next nx last' (l.drop (cur.k + 3)) n n' dS' dC')
    (rest' : List Fmt.M1.Stage)
    (hD : Dealt next (nx :: rest') ((listsOf p.nums).drop (j + 1)) (l.drop (cur.k + 3)))
    (hst : p.nums.stages.drop (j + 1) = next :: nx :: rest') (hown : p.nums.ownMask = false)
    (tabM tabZ : ℕ → GE) (tM tZ fM fT : ℕ → ℕ → GE) :
    ∃ tr', FormInv p (j + 1) next (l.drop (cur.k + 3))
        (stepT3 p n false dS dC (foldT t row L c (n.code, n.maskCode) id rs) rC gs
          (foldOut t row L c id rs) t.st.groups.size D tN row')
        (stageColW (sgOf next) tabM tabZ tM tZ fM fT) row'
        (stepL p n false (foldT t row L c (n.code, n.maskCode) id rs) t.st.groups.size D) n
        (n'.code, n'.maskCode) ((foldT t row L c (n.code, n.maskCode) id rs).st.oracles.size + 1)
        t.book.trees.size tr' ∧
      LayAt [(foldT t row L c (n.code, n.maskCode) id rs).st.oracles.size] #[some 0] #[some 0]
        (stepL p n false (foldT t row L c (n.code, n.maskCode) id rs) t.st.groups.size D) ∧
      SeatP (stepT3 p n false dS dC (foldT t row L c (n.code, n.maskCode) id rs) rC gs
          (foldOut t row L c id rs) t.st.groups.size D tN row').st
        (stepT3 p n false dS dC (foldT t row L c (n.code, n.maskCode) id rs) rC gs
          (foldOut t row L c id rs) t.st.groups.size D tN row').book
        [(foldT t row L c (n.code, n.maskCode) id rs).st.oracles.size,
          (foldT t row L c (n.code, n.maskCode) id rs).st.oracles.size + 1]
        (p.nums.firstTree + (p.nums.free + j)) (sgOf next).C.a (stageShapes (sgOf next) n) := by
  have hm : D.G.members = #[] := by rw [Dn.G]
  have hk : D.G.kept = #[] := by rw [Dn.G]
  have hr : D.G.rows = #[] := by rw [Dn.G]
  have ek : n.k = next.k := by
    rw [Pl.nk]
    exact Nat.add_sub_cancel' Pl.hkN
  have eh : n.h = next.h := Pl.nh
  have en : (⟨n.code, n.maskCode, next.k, next.h⟩ : IoppStage) = n := by
    rw [← ek, ← eh]
  have eT : swTarget p n = switchTargetStage n.code n.maskCode n.k n.h 1 := by
    unfold swTarget
    rw [Pl.one]
  have eT' : swTarget p n = switchTargetStage n.code n.maskCode ((sgOf next).h + (sgOf next).g)
      (sgOf next).h 1 := by
    rw [eT, Pl.nk, Pl.nh]
  have hd := Dn.did
  have hdT := hd
  rw [eT] at hdT
  have hOR := Dn.orderR
  rw [eT] at hOR
  have hlay := hdT.lay_eq hm hk
  obtain ⟨sh, l1, l2, l3, l4, l5⟩ := Pl.oneTree D.lay hd.trees
  -- the seat in the soundness side's form
  have hseat := hd.seat sh l1 l3 l4 l5
  have e2 : (List.range (OnBytes.Slice.sentOf (swTarget p n) (othersOf false n)).size).map
      (· + (foldT t row L c (n.code, n.maskCode) id rs).st.oracles.size) =
      [(foldT t row L c (n.code, n.maskCode) id rs).st.oracles.size,
        (foldT t row L c (n.code, n.maskCode) id rs).st.oracles.size + 1] := by
    show [0 + _, 1 + _] = _
    rw [Nat.zero_add, Nat.add_comm 1]
  have eroots : (foldT t row L c (n.code, n.maskCode) id rs).roots = p.nums.free + j := I.roots
  rw [e2, l2, eroots, eT'] at hseat
  have hQ : SeatP (stepT3 p n false dS dC (foldT t row L c (n.code, n.maskCode) id rs) rC gs
      (foldOut t row L c id rs) t.st.groups.size D tN row').st
      (stepT3 p n false dS dC (foldT t row L c (n.code, n.maskCode) id rs) rC gs
        (foldOut t row L c id rs) t.st.groups.size D tN row').book
      [(foldT t row L c (n.code, n.maskCode) id rs).st.oracles.size,
        (foldT t row L c (n.code, n.maskCode) id rs).st.oracles.size + 1]
      (p.nums.firstTree + (p.nums.free + j)) (sgOf next).C.a (stageShapes (sgOf next) n) := hseat
  -- the seat for the reading
  have htN : tN < t.book.trees.size := by
    rcases Nat.lt_or_ge tN t.book.trees.size with h1 | h1
    · exact h1
    · have := I.seat.inBook
      rw [Array.getElem?_eq_none h1] at this
      cases this
  have hR := readSeat_behind D (swTarget p n) t.st.groups.size (othersOf false n)
    (foldT t row L c (n.code, n.maskCode) id rs).st p.nums.firstTree
    (foldT t row L c (n.code, n.maskCode) id rs).roots t.book sh rfl l1
    (fun i hi => l3 i (by
      show i < 2
      exact hi))
    (step_foldT t row L c _ id rs I.step) (by
      show p.answers ≠ 0
      rw [Pl.one]
      exact Nat.one_ne_zero) rfl tN htN
  have hmem : (stepL p n false (foldT t row L c (n.code, n.maskCode) id rs) t.st.groups.size
      D).members.toList = [(foldT t row L c (n.code, n.maskCode) id rs).st.oracles.size] := by
    rw [hlay]
  have hfolds := Pl'.folds
  refine ⟨_, ⟨?_, hdT.noKept hm hk hr, ?_, ?_, ?_,
    dense_behind hd Dn.ff.kept Dn.ff.prog.masks Dn.ff.prog.noKept hm hr Dn.dense, Dn.order,
    step_behind hd, ?_, by rw [hmem]; exact hR, l2,
    fun dS2 dC2 hcut => decl_later p.nums j next nx rest' _ _ _ _ _ _ _ n hown hst hD Pl.hkN eh hR
      hQ dS2 dC2 hcut,
    fun y => width_later next n _ _ _ _ _ _ _ tabM tabZ tM tZ fM fT Pl.hkN eh hR hQ y⟩,
    hdT.layAt hm hk, hQ⟩
  · have h := foldFront_behind p j (nn := (n'.code, n'.maskCode)) (next := next) (nx := nx)
      (stepT3 p n false dS dC (foldT t row L c (n.code, n.maskCode) id rs) rC gs
        (foldOut t row L c id rs) t.st.groups.size D tN row') hdT Dn.ff.kept Dn.ff.prog.masks
      Dn.ff.prog.noKept Dn.dense Dn.G hOR ek eh (code_of_map Pl.codeN) (code_of_map Pl.zkN)
      (code_of_map Pl'.codeN) (code_of_map Pl'.zkN) Pl'.ok Pl'.shortN Pl'.vars Pl.idx Pl'.idx rfl
      rfl (did_mask hd rfl)
    rw [en] at h
    exact h
  · intro i hi
    rw [hlay] at hi ⊢
    obtain rfl : i = 0 := by simpa using hi
    rfl
  · rw [hlay]
    show max (max n.k n.h) 1 = _
    rw [Pl.nk, Pl.nh]
    omega
  · rw [hlay]
    exact Pl.nh
  · show (foldT t row L c (n.code, n.maskCode) id rs).roots + D.lay.shapes.size = _
    rw [eroots, l1]
    rfl

/-- **Behind the stage in front of the last, the last stage's form stands.** -/
theorem lastForm_next {p : P12} {j : ℕ} {cur next : Fmt.M1.Stage} {l : Laid} {c n : IoppStage}
    {dS dC d₁ d₂ : Fmt.DeclaredRound} {t : T12} {col : ℕ → List UInt64} {row : GroupRow}
    {L : GroupLayout} {id tN : ℕ} {tr : Tree} {rs : List Fmt.RoundView} {rS rC : Fmt.RoundView}
    {gs : List (List (ℕ × List UInt64))} {a x : Fmt.Ext} {D : Taken} {row' : GroupRow}
    (Pl : StepPlan p t.st.codes j cur next true l c n dS dC)
    (I : FormInv p j cur l t col row L c (n.code, n.maskCode) id tN tr)
    (Dn : StepDone (sgOf cur) (sgOf next) p n true dS dC
      (foldT t row L c (n.code, n.maskCode) id rs) rS rC gs (foldOut t row L c id rs)
      t.st.groups.size j cur next tN a D x row')
    (Lp : LastPlan p t.st.codes (j + 1) next (l.drop (cur.k + 3)) n d₁ d₂)
    (hlabel : p.nums.firstTree + (p.nums.free + j) = (basePar p next).label)
    (hzk : ∀ sh, D.lay.shapes = #[sh] → sh.logNzk = next.Z.a) :
    LastForm p (j + 1) next
      (stepT3 p n true dS dC (foldT t row L c (n.code, n.maskCode) id rs) rC gs
        (foldOut t row L c id rs) t.st.groups.size D tN row') row'
      (stepL p n true (foldT t row L c (n.code, n.maskCode) id rs) t.st.groups.size D) n
      ⟨dense (row'.c.fixLow [zeroE]) (ceilLog2 next.C.l), row'.d.map (·.triple),
        row'.target.triple⟩
      (foldT t row L c (n.code, n.maskCode) id rs).st.oracles.size
      ((foldT t row L c (n.code, n.maskCode) id rs).st.oracles.size + 1) t.book.trees.size := by
  have hm : D.G.members = #[] := by rw [Dn.G]
  have hr : D.G.rows = #[] := by rw [Dn.G]
  have eh : n.h = 0 := Pl.nh.trans Lp.h0
  have eT : swTarget p n = switchTargetStage n.code n.maskCode 0 0 1 := by
    unfold swTarget
    rw [Pl.one, Lp.k0, eh]
  have hd := Dn.did
  have hdT := hd
  rw [eT] at hdT
  have hOR := Dn.orderR
  rw [eT] at hOR
  obtain ⟨sh, l1, l2, l3, l4, l5⟩ := Pl.oneTree D.lay hd.trees
  have eroots : (foldT t row L c (n.code, n.maskCode) id rs).roots = p.nums.free + j := I.roots
  have htN : tN < t.book.trees.size := by
    rcases Nat.lt_or_ge tN t.book.trees.size with h1 | h1
    · exact h1
    · have := I.seat.inBook
      rw [Array.getElem?_eq_none h1] at this
      cases this
  have hR := readSeat_behind D (swTarget p n) t.st.groups.size (othersOf true n)
    (foldT t row L c (n.code, n.maskCode) id rs).st p.nums.firstTree
    (foldT t row L c (n.code, n.maskCode) id rs).roots t.book sh rfl l1
    (fun i hi => l3 i (by
      show i < 2
      exact hi))
    (step_foldT t row L c _ id rs I.step) (by
      show p.answers ≠ 0
      rw [Pl.one]
      exact Nat.one_ne_zero) rfl tN htN
  have hp' := dense_behind hd Dn.ff.kept Dn.ff.prog.masks Dn.ff.prog.noKept hm hr Dn.dense
  have hsh : sh = ⟨next.C.a, next.Z.a, #[3, 3], #[3, 3]⟩ := by
    rw [eT] at l4 l5
    cases sh with
    | mk a1 a2 a3 a4 =>
      have b1 : a1 = next.C.a := l2
      have b2 : a2 = next.Z.a := hzk _ l1
      have b3 : a3 = #[3, 3] := l4
      have b4 : a4 = #[3, 3] := l5
      rw [b1, b2, b3, b4]
  obtain ⟨f1, f2, f3⟩ := five_behind Pl.fits hdT Dn.G Pl.zkN hp'
  exact
    { front := baseFront_behind hdT Dn.G hOR rfl rfl rfl rfl Lp.stage Lp.k0 Pl.codeN Pl.zkN hp'
        Lp.small _ _ hR (by
          show p.nums.firstTree + (foldT t row L c (n.code, n.maskCode) id rs).roots = _
          rw [eroots]
          exact hlabel) hsh
      st := Lp.st, h0 := Lp.h0, g0 := Lp.g0, pow := f1, dSize := f2, fix := f3 }

end Johnson.Prover.Link
