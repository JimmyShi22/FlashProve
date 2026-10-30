-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Run/StoredGlue.lean: what the drawn positions ask of the stored tables is what the
openings list, over the sibling's rounds' data.
The compiler under OnBytes/TypedOracleCompiler/ is the one that `innerCompiledVerifier` is made with; it builds on
definitions of Compile/.

After OnBytes/Tie/StoredLists.lean (its `wantedXL_from`, `wantedX_eq`) and
OnBytes/Tie/StoredGlue.lean (its last five declarations). CUT BY PROGRAM. These seven are
the declarations of the two files that speak of a description's rounds' data (`rds`, `wantedX`,
`xWanted`), of the limits `PQ.ok`, or of `XD`, which the sibling says anew; all others speak of the
format's text and of lists, and are imported as they are.

AS TEXT, but for `_root_.` before `Fmt.` and one line break (7). `wantedXL_from`, `wantedX_eq`,
`base_ok`, `sto_eq`, `sto_keys`, `sto_count`, `xWanted_asked`. TURNED, NEW, NO COUNTERPART: none.
That the text stands with a list of trees a round rests on the sibling's `tab_wantRound`,
`tab_good`, `tab_limits` (OnBytes/TypedOracleCompiler/Run/PageIsTabProofs.lean).

WHAT IS NOT SAID. Nothing on soundness; no probability; nothing on any hash: h is any function of
the format's hash's type.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Run.PageXRead
import OnBytes.TypedOracleCompiler.Run.PageIsTabProofs
import OnBytes.Tie.StoredGlue

set_option autoImplicit false

namespace TypedOracleCompiler.Run.PQ
open Rom TypedOracleCompiler.Iop _root_.Compile TypedOracleCompiler.Compile.Batch TypedOracleCompiler.Run.Twin
  TypedOracleCompiler.Run.Thin
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ TypedOracleCompiler.Run
open OnBytes.Tie (xsOf getD_step xsAt_xsOf storedB_eq stoOf stoOf_keys count_from count_all pick
  asked_all tab_small roundWithStoredOpenings StoredFact askedOf)

/-- The same as `wantedX_eq` below, for rounds that are numbered from i on. -/
theorem wantedXL_from (S : _root_.Fmt.Spec) (a : ℕ) (whole : List (List _root_.Fmt.Stored)) :
    ∀ (rs : List _root_.Fmt.Round) (ros : List _root_.Fmt.RoundOut)
      (tss : List (List _root_.Fmt.Stored))
      (acc : List ByteArray) (sent i : ℕ), TabTR rs ros acc → tss.length = ros.length →
    (∀ j, whole.getD (i + j) [] = tss.getD j []) →
    (∀ r ∈ rs, ∀ x ∈ r.opens, ∃ n, TabGood S x n) →
    wantedXL a (rds S) (xsOf whole) i (rdsFrom S sent rs) (ros.map (·.drawn)) =
      (tss.zip ros).flatMap fun y =>
        (y.1.flatMap fun t =>
          (_root_.Fmt.listOf ((_root_.Fmt.partOf t y.2.drawn.poss).map (· % 2 ^ a))).map fun x =>
            (PQ.storedKey (t.item == 1), x)) ++
        y.2.opens.flatMap fun x => x.2.1.map fun z => (x.1.tree - S.firstTree, z)
  | [], [], [], _, _, _, _, _, _, _ => rfl
  | [], [], _ :: _, _, _, _, _, hl, _, _ => by simp at hl
  | [], _ :: _, _, _, _, _, t, _, _, _ => t.elim
  | _ :: _, [], _, _, _, _, t, _, _, _ => t.elim
  | _ :: _, _ :: _, [], _, _, _, _, hl, _, _ => by simp at hl
  | r :: rs, ro :: ros, ts :: tss, acc, sent, i, t, hl, hw, hg => by
    have ih := wantedXL_from S a whole rs ros tss _ (sent + r.entry.roots) (i + 1) t.2
      (by simpa using hl) (getD_step whole i ts tss hw)
      fun r' hr' => hg r' (List.mem_cons_of_mem _ hr')
    have h0 : whole.getD i [] = ts := hw 0
    rw [List.zip_cons_cons, List.flatMap_cons, ← ih,
      ← tab_wantRound S _ _ t.1 (hg r List.mem_cons_self)]
    show (((xsAt (xsOf whole) i).flatMap fun o =>
      (o.list a ro.drawn).map fun x => (PQ.storedKey o.which, x)) ++ _) ++ _ = _
    rw [xsAt_xsOf, h0, List.flatMap_map]
    rfl

/-- What the drawn positions ask for, round by round: first the stored tables, each at the list of
its part of the draws, then the chain's own trees. `ros` are the rounds without the stored tables'
openings. It holds if there is one list of tables for each round, the rounds read fit the
description's (`TabTR`), and S's rounds open only trees that the chain itself sends (`TabGood`). -/
theorem wantedX_eq (S : _root_.Fmt.Spec) (a : ℕ) (tss : List (List _root_.Fmt.Stored))
    (ros : List _root_.Fmt.RoundOut) (hl : tss.length = ros.length) (ht : TabTR S.rounds ros [])
    (hg : ∀ r ∈ S.rounds, ∀ x ∈ r.opens, ∃ n, TabGood S x n) :
    wantedX a (rds S) (xsOf tss) (ros.map (·.drawn)) =
      (tss.zip ros).flatMap fun y =>
        (y.1.flatMap fun t =>
          (_root_.Fmt.listOf ((_root_.Fmt.partOf t y.2.drawn.poss).map (· % 2 ^ a))).map fun x =>
            (PQ.storedKey (t.item == 1), x)) ++
        y.2.opens.flatMap fun x => x.2.1.map fun z => (x.1.tree - S.firstTree, z) :=
  wantedXL_from S a tss S.rounds ros tss [] 0 0 ht hl (fun j => by rw [Nat.zero_add]) hg


/-- The sibling's limits imply the strict reader's conditions on a description. -/
theorem base_ok (S : _root_.Fmt.Spec) (h : PQ.ok S = true) : S.ok = true := by
  simp only [PQ.ok, Bool.and_eq_true] at h
  exact h.1.1.1.1

section
variable (h : HId) (D : XD) (o : _root_.Fmt.ChainOut)
  (rc : List (_root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)))
  (ho : o.rounds.toList = rc.map roundWithStoredOpenings)
  (hS : List.Forall₂ (fun (ts : List _root_.Fmt.Stored)
      (p : _root_.Fmt.RoundOut × List (_root_.Fmt.Shape × List ℕ × _root_.Fmt.OpenOut)) =>
    List.Forall₂ (StoredFact h D.base.cfg D.base.statement p.1.drawn.poss) ts p.2) D.stored rc)

include ho hS in
/-- The library's list `storedB` is `stoOf`: the openings round by round. -/
theorem sto_eq : storedB D.xs o = stoOf D.stored rc :=
  storedB_eq D.stored o rc ho (hS.imp fun _ _ f => f.length_eq)

include ho hS in
/-- The openings belong to the tables in the description's order, under the section's two
hypotheses: o is rc with the stored openings joined in, and each has `StoredFact`. -/
theorem sto_keys : (storedB D.xs o).map (·.1) = D.stored.flatten.map (·.item == 1) := by
  rw [sto_eq h D o rc ho hS]
  exact stoOf_keys D.stored rc (hS.imp fun _ _ f => f.length_eq)

include ho hS in
/-- The listed places are no more than the draws that the description gives to the tables, under
the same two hypotheses. -/
theorem sto_count : ((storedB D.xs o).map (·.2.2.idx.length)).sum ≤ (D.xs.map (·.count)).sum := by
  rw [sto_eq h D o rc ho hS]
  have e : D.xs.map (·.count) = D.stored.flatten.map (·.count) := count_from D.stored 0
  rw [e]
  exact count_all h _ _ hS

include ho hS in
/-- What the drawn positions ask of the two tables is what the openings list, under the same two
hypotheses, if the own part is within the sibling's limits, oo has `LaxFacts`, and all tables have
the depth `D.a`. `oo` is the chain as read without the stored tables' openings. -/
theorem xWanted_asked (hok : PQ.ok D.base = true) (oo : _root_.Fmt.ChainOut)
    (hL : LaxFacts h D.base oo) (hoo : oo.rounds.toList = rc.map fun p => stripR p.1)
    (hD : ∀ s ∈ D.stored.flatten, s.sh.a = D.a) :
    xWanted D.a D.ds D.xs (oo.rounds.toList.map (·.drawn)) = askedOf (storedB D.xs o) := by
  have ht : TabTR D.base.rounds oo.rounds.toList [] := tab_tr h _ _ _ _ _ hL.trace
  have hlen : D.stored.length = oo.rounds.toList.length := by
    rw [hoo, List.length_map]
    exact hS.length_eq
  have ht16 : ∀ r ∈ D.base.rounds, ∀ x ∈ r.opens, x.1.tree < 2 ^ 16 := by
    have e := _root_.Fmt.ok_trees (base_ok D.base hok)
    simp only [List.all_eq_true, decide_eq_true_eq] at e
    exact e
  have hsm := tab_small _ _ _ ht ht16
  have hw := wantedX_eq D.base D.a D.stored oo.rounds.toList hlen ht
    fun r hr x hx => tab_good D.base (tab_limits D.base hok) r hr x hx
  show (wantedX D.a (rds D.base) (xsOf D.stored) (oo.rounds.toList.map (·.drawn))).filterMap pick
    = _
  rw [hw, sto_eq h D o rc ho hS, hoo]
  refine asked_all h _ _ D.a D.base.firstTree hS hD fun p hp x hx => ?_
  exact hsm (stripR p.1) (by rw [hoo]; exact List.mem_map_of_mem hp) x hx

end


end TypedOracleCompiler.Run.PQ
