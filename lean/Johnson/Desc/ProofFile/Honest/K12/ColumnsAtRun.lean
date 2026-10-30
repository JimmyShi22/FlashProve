-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/ColumnsAtRun.lean

A conditional: nothing here shows that ready or runC returns or that a part is called.

The columns that "LOC" takes of the shared view, at a run of the frame's walking prover under the
head: they are the prover's own stored columns; and so the library's premise `OwnColumns`
(Johnson/Desc/K14/Honest/ItemsEach.lean) at `heldAt` (Sim/ShownAtRun.lean), from one premise on the
prover's stored table. One helper; two theorems.

  `lookup_graph`: a key looked up in the list of a function's pairs.
  `cs_at_run`: W.cs is the reader `colsLoc` (DoorReturns.lean) at the prover's stored columns as
      words.
  `columns_at_run`: `OwnColumns` at a run.

What for. The field columns of `LeftAt` (OnFreeTAtHeadULeft.lean).

By what. `called_at_run` (CalledAtRun.lean); `door_of_cols`, `rounds_eight` (DoorAtWalk.lean);
`cols_of_reads`, `foldBlocks_more`, `colsLoc_more` (DoorReturns.lean); the library's
`flatOf_carried`, `fold_like`, `peel_front`; `lengths_eight` (Sim/ShownAtRun.lean); `facts_at_head`
(NearAtHead.lean); `columns_held` (HeldAtCommitter.lean); the frame's authors' `ready_ok`
(Honest/Law/Run.lean). The first half of `cs_at_run`'s proof is a second text of the middle of
`door_at_run`'s (DoorAtRun.lean).

Limits.
- hst (the prover's stored columns of the plan's item, as words, are the committer's in Lean) is a
  premise on the prover's stored table at this index and these coins, asked at every position; it is
  spent at the positions that "LOC"'s round reads. It is shown of no prover here.
- `cs_at_run` takes no premise on the prover's fields; hR and S are on the filling and the book.
- Of the walk (`runC`). The shared chain alone. A tie between terms: it names no value and states no
  law over random values.
- It moves no count. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.DoorAtRun
import Johnson.Desc.ProofFile.Honest.K12.HeldAtCommitter

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (E TableKey)
open VerifiableInference.Desc (Block OpenedColumn foldBlocks)
open VerifiableInference.Desc (K1.qAt)
open Desc.K14 (St blocks first)
open Desc.K14.Honest (flatOf_carried Seen8 OwnColumns)
open ProofFile.Honest (ProverCoinCounts Prover Coins Draws Ready RunC Side Member Common StandsAt ready runC
  Weights TableRand ready_ok)
open ProofFile.Honest.K14 (witOf randNow)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r₀ : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- In the list of a function's pairs a key is looked up to the function's value. -/
theorem lookup_graph {α β : Type} [BEq α] [LawfulBEq α] (f : α → β) (l : List α) (a : α) (b : β)
    (h : (l.map fun y => (y, f y)).lookup a = some b) : b = f a := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    rw [List.map_cons, List.lookup_cons] at h
    cases hy : (a == y) with
    | true =>
      rw [hy] at h
      rw [eq_of_beq hy]
      exact (Option.some.inj h).symm
    | false =>
      rw [hy] at h
      exact ih h

/-- **The columns that "LOC" takes at a run are the prover's own stored columns.** Under the head,
at a run at which a part of a side behind the nine first sub-protocols of the shared chain is
called: where the description's own fold over the eight returns at the shared view's rounds and
columns and leaves the columns more, and the view's columns are W.cs and then more: W.cs is the
reader `colsLoc` (DoorReturns.lean) at the prover's stored columns as words and at the view's
rounds: at each position that "LOC"'s round reads, that position's stored column. No premise on the
prover's fields; hR and S are on the filling and the book. -/
theorem cs_at_run {W₀ Rc Tr X₀ Y V Pb : Type}
    (h : P5J.AtMg o Z D r₀ Zp Np cF) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc ProofFile.Inst TableKey Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : ProofFile.Inst}
    {k : Coins Bk} {ρ : Draws} {R : Ready W₀ Rc ProofFile.Inst TableKey Tr X₀ Y}
    {r : RunC (P5J.F0T o Zp Np cF)} (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (σ : Side St ProofFile.Cl V (Common W₀ Rc TableKey) X₀ Pb)
    (u : Member V (Common W₀ Rc TableKey) X₀ Pb) (pre' t' : List (Block St ProofFile.Cl)) (i : ℕ)
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ u pre' t' i)
    (h9 : pre' = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (W : Seen8) (d8 : St) (rest₈ : List Fmt.RoundView) (more : List OpenedColumn)
    (hfold : foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first (K1.qAt Zp Np).codes x.pub.key)
      r.run.views.2.1.rounds r.run.views.2.1.opened = .ok (d8, rest₈, more))
    (hcols : r.run.views.2.1.opened = W.cs ++ more) :
    W.cs = colsLoc (K1.qAt Zp Np) (P.storedWords w₀ rc) r.run.views.2.1.rounds := by
  obtain ⟨m, s, cols, more₁, rest, -, -, hrounds, hlen, hcols₁, hfold₁, hfill₁⟩ :=
    called_at_run h.laid.planOk hR σ u pre' t' i S hrun hc
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8, tl, eF, l0, l1, l2, l3, l4, l5, l6, l7, l8⟩ :=
    flatOf_carried (Cl := ProofFile.Cl) Zp.p.chains (K1.qAt Zp Np) b1 b2 b3 b4 b5 b6 b7 b8
      (VerifiableInference.Desc.K12.Seat.tests Np) VerifiableInference.Desc.K12.Seat.last hb
  have eF' : (P5J.F0T o Zp Np cF).shared.blocksInOrder =
      x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: tl := eF
  have epre : pre' = [x0, x1, x2, x3, x4, x5, x6, x7, x8] := by
    rw [h9, eF']
    rfl
  subst epre
  obtain ⟨hSN, -, hU⟩ := facts_at_head h
  obtain ⟨n1, n2, n3, n4, n5, n6, n7, n8⟩ :=
    lengths_eight _ _ b1 b2 b3 b4 b5 b6 b7 b8 hb hU hSN
  have eR : [x0, x1, x2, x3, x4, x5, x6, x7, x8].flatMap (·.rounds) =
      [b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds) := by
    simp only [List.flatMap_cons, List.flatMap_nil, l0.rounds, l1.rounds, l2.rounds, l3.rounds,
      l4.rounds, l5.rounds, l6.rounds, l7.rounds, l8.rounds]
    rfl
  have h8 : ([b1, b2, b3, b4, b5, b6, b7, b8].flatMap (·.rounds)).length = 8 := by
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append, n1, n2,
      n3, n4, n5, n6, n7, n8]
  have hlen' : m.seen.length =
      (([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl)).flatMap (·.rounds)).length +
        i := hlen
  have hfold' : foldBlocks 0 ([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl))
      (first (K1.qAt Zp Np).codes x.pub.key)
      (m.seen.take (([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl)).flatMap
        (·.rounds)).length) cols = .ok (s, [], []) := hfold₁
  have hfill : ProofFile.Honest.fillCols (ProofFile.Honest.readsOf 1 0 (P.storedWords w₀ rc)
            (ProofFile.Honest.treeOwn (r.run.played.2.1.take
                    (([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl)).flatMap
                      (·.rounds)).length))
            (([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl)).flatMap (·.rounds))
            ((m.seen.take (([x0, x1, x2, x3, x4, x5, x6, x7, x8] : List (Block St ProofFile.Cl)).flatMap
              (·.rounds)).length).map (·.drawn))) [] = .ok cols := hfill₁
  rw [eR, h8] at hlen' hfold'
  rw [eR] at hfill
  rw [h8] at hfill
  -- the fold over the eight, at cols and at the reader's columns
  have gE := Desc.K14.Honest.peel_front Zp.p.chains 0 _ _ _ _ _
    (Desc.K14.Honest.fold_like 0 _ _ (.cons l0 (.cons l1 (.cons l2 (.cons l3 (.cons l4 (.cons l5
      (.cons l6 (.cons l7 (.cons l8 .nil))))))))) _ _ _ _ hfold')
  have g1 := (door_of_cols (V := Unit) (X := Unit) Zp.p.chains (K1.qAt Zp Np)
    (sentOf (K1.qAt Zp Np).S) b1 b2 b3 b4 b5 b6 b7 b8 hb hU _
    (.cons l0 (.cons l1 (.cons l2 (.cons l3 (.cons l4 (.cons l5 (.cons l6 (.cons l7
      (.cons l8 .nil))))))))) 1 (P.storedWords w₀ rc) _ x.pub.key _ cols s hfold' hfill).1
  -- what the view's columns are
  have hview := foldBlocks_more 0 _ _ _ _ _ gE (m.seen.drop 8 ++ rest) more₁
  rw [← List.append_assoc, List.take_append_drop, ← hrounds, ← hcols₁] at hview
  have em : more = more₁ := congrArg (·.2.2) (Except.ok.inj (hfold.symm.trans hview))
  have ecs : W.cs = cols := by
    refine List.append_cancel_right (bs := more) ?_
    rw [← hcols, hcols₁, em]
  -- the reader's columns are all of cols
  obtain ⟨e0, e1, e2, en, post, r0, r1, r2, eRd⟩ :=
    rounds_eight (K1.qAt Zp Np) (sentOf (K1.qAt Zp Np).S) b1 b2 b3 b4 b5 b6 b7 b8 hb hU
  rw [eRd] at hfill
  obtain ⟨more', ec⟩ := cols_of_reads (K1.qAt Zp Np) 1 0 (P.storedWords w₀ rc) _ e0 e1 e2 en post r0
    r1 r2 _ cols hfill
  have g2 := foldBlocks_more 0 _ _ _ _ _ g1 [] more'
  rw [List.append_nil, ← ec] at g2
  have e' : more' = [] := (congrArg (·.2.2) (Except.ok.inj (gE.symm.trans g2))).symm
  rw [ecs, ec, e', List.append_nil, hrounds]
  have hs : m.seen = m.seen.take 8 ++ m.seen.drop 8 := (List.take_append_drop 8 m.seen).symm
  conv_rhs => rw [hs, List.append_assoc]
  rw [colsLoc_more _ _ _ _ (by rw [List.length_take, hlen']; omega)]

/-- **`OwnColumns` at a run**, at `heldAt` at the shared rounds' authors' readers: under
`cs_at_run`'s premises, where the prover's stored columns of the plan's item, as words, are the
committer's in Lean (hst; `storedW`, Johnson/Bind/ForProver/TabCols.lean). hst is a premise on the
prover's stored table at this index and these coins. -/
theorem columns_at_run {W₀ Tr X₀ Y V Pb : Type}
    (h : P5J.AtMg o Z D r₀ Zp Np cF) (b1 b2 b3 b4 b5 b6 b7 b8 : Block St Unit)
    (hb : blocks (K1.qAt Zp Np) = some [b1, b2, b3, b4, b5, b6, b7, b8]) {Bk : ProverCoinCounts}
    {P : Prover W₀ (ℕ → TableRand) ProofFile.Inst TableKey Tr X₀ Y} {w₀ : W₀} {rc : ℕ → TableRand} {x :
            ProofFile.Inst}
    {k : Coins Bk} {ρ : Draws} {R : Ready W₀ (ℕ → TableRand) ProofFile.Inst TableKey Tr X₀ Y}
    {r : RunC (P5J.F0T o Zp Np cF)} (hR : ready (P5J.F0T o Zp Np cF) Bk P w₀ rc x k = .ok R)
    (hrun : runC (P5J.F0T o Zp Np cF) Bk P w₀ rc x k ρ = .ok r)
    (σ : Side St ProofFile.Cl V (Common W₀ (ℕ → TableRand) TableKey) X₀ Pb)
    (u : Member V (Common W₀ (ℕ → TableRand) TableKey) X₀ Pb) (pre' t' : List (Block St ProofFile.Cl)) (i
            : ℕ)
    (S : StandsAt (P5J.F0T o Zp Np cF).shared.blocksInOrder R.shared σ u pre' t' i)
    (h9 : pre' = (P5J.F0T o Zp Np cF).shared.blocksInOrder.take 9)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true)
    (W : Seen8) (d8 : St) (rest₈ : List Fmt.RoundView) (more : List OpenedColumn)
    (hfold : foldBlocks 0 [b1, b2, b3, b4, b5, b6, b7, b8] (first (K1.qAt Zp Np).codes x.pub.key)
      r.run.views.2.1.rounds r.run.views.2.1.opened = .ok (d8, rest₈, more))
    (hcols : r.run.views.2.1.opened = W.cs ++ more)
    (wts : W₀ → Weights)
    (hst : ∀ y, P.storedWords w₀ rc (K1.qAt Zp Np).item y =
      Bind.ForProver.storedW Zp (wts w₀) rc (K1.qAt Zp Np).item y)
    (csU csO : Array E) :
    OwnColumns (K1.qAt Zp Np) W.view
      (heldAt (K1.qAt Zp Np) (witOf (K1.qAt Zp Np) wts (randNow (K1.qAt Zp Np)) R.common) csU
        csO) := by
  obtain ⟨-, tr, -, -, hcm, -⟩ := ready_ok hR
  have ecs := cs_at_run h b1 b2 b3 b4 b5 b6 b7 b8 hb hR hrun σ u pre' t' i S h9 hc W d8 rest₈ more
    hfold hcols
  refine columns_held h wts R.common csU csO W.view fun y col hy => ?_
  have hy' : ((W.cs.map fun c => (c.2.1, c.2.2)) : List (ℕ × List UInt64)).lookup y = some col := hy
  rw [ecs] at hy'
  unfold colsLoc at hy'
  rw [hcm]
  cases hR4 : r.run.views.2.1.rounds[3]? with
  | none =>
    rw [hR4] at hy'
    simp at hy'
  | some R4 =>
    rw [hR4] at hy'
    simp only [List.map_map] at hy'
    have k := lookup_graph (fun y => (P.storedWords w₀ rc
      (Desc.K14.readsAtLoc (K1.qAt Zp Np).S.fold (K1.qAt Zp Np).item).item y).getD []) _ y col hy'
    rw [k]
    exact congrArg (·.getD []) (hst y)

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.lookup_graph
#print axioms ProofFile.Honest.K12.Light.cs_at_run
#print axioms ProofFile.Honest.K12.Light.columns_at_run
