-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/TreeNumberAtRun.lean: what a run's front lists of the tree
that a round in front has laid: at a run of the frame's walking prover (`runC`), in front of a
called part of the shared chain: the table number idx of the first round of a sub-protocol b, as
played, is the shared chain's own tree number "the roots that the rounds in front of b declare, plus
idx"; and the front lists of that tree that table's columns at the positions asked. General in the
description, the book and the filling; no kind of sub-protocol is named.

A conditional: nothing here shows that `ready` or `runC` returns or that a part is called.

  `tab_at_round`      the flat list of the tables, at a round's table: lists alone
  `tables_in_front`   the tables in front of a sub-protocol are as many as the roots that the rounds
                    in front declare: of any rounds that bear as many tables as the prepared
                    rounds state oracle messages
  `tree_of_round_at_run`   the statement

By what. `treeCols_at_run` (Sim/TreeColsAtRun.lean); `trees_in_front`, `planOk_shaped`
(TreeInFront.lean); the frame's authors' `runC_laidAs` (Honest/Law/RunAtFile.lean), `laidAs_tables`
(Honest/Law/RunAt.lean), `steps_shaped` (Honest/Law/Along.lean), `steps_pairs`
(Honest/Law/StratRun.lean), `ready_ok` (Honest/Law/Run.lean).

Limits. The first round of b alone. What the table is, and who made it, is not treated. The shared
chain alone. Of the walk (`runC`). Where no prover's side sent the table (`none`) the front lists no
column of it, and the statement says so. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.TreeColsAtRun
import Johnson.Desc.ProofFile.Honest.K12.Sim.PlayedAtRun
import Johnson.Desc.ProofFile.Honest.K12.TreeInFront
import Johnson.Desc.ProofFile.Honest.Law.Along
import Johnson.Desc.ProofFile.Honest.Law.StratRun
import Johnson.Desc.ProofFile.Honest.Law.Rule.PartLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc (FileDescription Block)
open Johnson.G.OfPlan (rootsOf)

/-- **The flat list of the tables, at a round's table**: lists alone. -/
theorem tab_at_round : ∀ (pl : List Played) (i idx : ℕ) (q : Played), pl[i]? = some q →
    idx < q.tables.length →
    (allTabs pl)[((pl.take i).map (·.tables.length)).sum + idx]? = q.tables[idx]?
  | [], _, _, _, hq, _ => by simp at hq
  | a :: pl, 0, idx, q, hq, hidx => by
    obtain rfl : a = q := Option.some.inj hq
    show (a.tables ++ allTabs pl)[0 + idx]? = _
    rw [Nat.zero_add, List.getElem?_append_left hidx]
  | a :: pl, i + 1, idx, q, hq, hidx => by
    have ih := tab_at_round pl i idx q hq hidx
    show (a.tables ++ allTabs pl)[(a.tables.length +
      ((pl.take i).map (·.tables.length)).sum) + idx]? = _
    rw [Nat.add_assoc, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact ih

/-- **The tables in front of a sub-protocol are as many as the roots that the rounds in front
declare.** `ready` has returned R; b: a sub-protocol of the shared chain with pre in front; pl:
rounds that bear as many tables as the first n prepared rounds, which reach b's first, state oracle
messages (hsh). -/
theorem tables_in_front {Xi W₀ Rc Ky Tr X₀ Y : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R)
    (pre : List (Block F.S₂ F.Cl)) (b : Block F.S₂ F.Cl) (t : List (Block F.S₂ F.Cl))
    (hcut : F.shared.blocksInOrder = pre ++ b :: t) (n : ℕ) (hn : (pre.flatMap (·.rounds)).length ≤ n)
    (pl : List Played)
    (hsh : pl.map (·.tables.length) = (R.shared.take n).map (·.oracles.length)) :
    ((pl.take (pre.flatMap (·.rounds)).length).map (·.tables.length)).sum =
      rootsOf (pre.flatMap (·.rounds)) := by
  obtain ⟨-, tr, -, -, -, -, s2, -⟩ := ready_ok hR
  have e2 : R.shared.map (·.oracles.length) = (rowsOfChain F.shared.blocksInOrder).map (·.2.length) := by
    have g := congrArg (List.map fun z : Fmt.DeclaredRound × List VerifiableInference.Desc.Oracle =>
      z.2.length) (steps_pairs s2)
    rw [List.map_map] at g
    exact g
  have e3 : (pl.take (pre.flatMap (·.rounds)).length).map (·.tables.length) =
      ((rowsOfChain F.shared.blocksInOrder).take (pre.flatMap (·.rounds)).length).map (·.2.length) := by
    calc (pl.take (pre.flatMap (·.rounds)).length).map (·.tables.length)
        = (pl.map (·.tables.length)).take (pre.flatMap (·.rounds)).length := List.map_take
      _ = ((R.shared.take n).map (·.oracles.length)).take (pre.flatMap (·.rounds)).length := by
        rw [hsh]
      _ = ((R.shared.map (·.oracles.length)).take n).take (pre.flatMap (·.rounds)).length := by
        rw [List.map_take]
      _ = (R.shared.map (·.oracles.length)).take (pre.flatMap (·.rounds)).length := by
        rw [List.take_take, Nat.min_eq_left hn]
      _ = ((rowsOfChain F.shared.blocksInOrder).map (·.2.length)).take (pre.flatMap (·.rounds)).length := by
        rw [e2]
      _ = ((rowsOfChain F.shared.blocksInOrder).take (pre.flatMap (·.rounds)).length).map (·.2.length) :=
        List.map_take.symm
  rw [e3, hcut]
  exact trees_in_front pre t b fun z hz => planOk_shaped hpl z (by
    rw [hcut]
    exact List.mem_append_left _ hz)

/-- **WHAT A RUN's FRONT LISTS OF THE TREE THAT A ROUND IN FRONT HAS LAID.** The letters of
`treeCols_at_run` (a called part u of the side σ, with pre' in front and i rounds of its own block;
n the rounds in front of it). b: a sub-protocol of the shared chain with pre in front, whose first
round lies in front of the part (hin). q: that round as played; T: its table number idx. Then the
front lists, of the shared chain's own tree number "the roots declared in front of b, plus idx", the
columns of T at the positions asked. -/
theorem tree_of_round_at_run {Xi W₀ Rc Ky Tr X₀ Y V Pb : Type} {F : FileDescription Xi} {Bk : ProverCoinCounts}
    {P : Prover W₀ Rc Xi Ky Tr X₀ Y} {w₀ : W₀} {rc : Rc} {x : Xi} {k : Coins Bk} {ρ : Draws}
    {R : Ready W₀ Rc Xi Ky Tr X₀ Y} {r : RunC F} (hpl : F.planOk = true)
    (hR : ready F Bk P w₀ rc x k = .ok R) (hrun : runC F Bk P w₀ rc x k ρ = .ok r)
    (σ : Side F.S₂ F.Cl V (Common W₀ Rc Ky) X₀ Pb) (u : Member V (Common W₀ Rc Ky) X₀ Pb)
    (pre' t' : List (Block F.S₂ F.Cl)) (i n : ℕ)
    (S : StandsAt F.shared.blocksInOrder R.shared σ u pre' t' i)
    (hn : n = (pre'.flatMap (·.rounds)).length + i)
    (hc : r.called ⟨σ.block.place, u.number⟩ = true) (st : List (ℕ × ℕ × List UInt64))
    (pre : List (Block F.S₂ F.Cl)) (b : Block F.S₂ F.Cl) (t : List (Block F.S₂ F.Cl))
    (hcut : F.shared.blocksInOrder = pre ++ b :: t) (hin : (pre.flatMap (·.rounds)).length < n)
    (q : Played) (hq : r.run.played.2.1[(pre.flatMap (·.rounds)).length]? = some q)
    (idx : ℕ) (T : Option Table) (hT : q.tables[idx]? = some T) :
    (r.run.beforeAt st ⟨σ.block.place, u.number⟩).treeCols 1
        (rootsOf (pre.flatMap (·.rounds)) + idx) =
      some (colsOfT T (treeAsks F ρ 1 (rootsOf (pre.flatMap (·.rounds)) + idx))) := by
  have Q := (F.planOk_ok).1 hpl
  obtain ⟨-, tr, -, -, -, s1, s2, s3⟩ := ready_ok hR
  obtain ⟨-, l2, -⟩ := runC_laidAs hrun hR (steps_shaped s1 Q.blocks₁) (steps_shaped s2 Q.blocks₂)
    (steps_shaped s3 Q.blocks₃)
  have hsh : (r.run.played.2.1.take n).map (·.tables.length) =
      (R.shared.take n).map (·.oracles.length) := by
    rw [List.map_take, List.map_take, laidAs_tables l2]
  have hq' : (r.run.played.2.1.take n)[(pre.flatMap (·.rounds)).length]? = some q := by
    rw [List.getElem?_take_of_lt hin]
    exact hq
  have hidx : idx < q.tables.length := (List.getElem?_eq_some_iff.1 hT).1
  have e := tab_at_round _ _ idx q hq' hidx
  rw [tables_in_front hpl hR pre b t hcut n (Nat.le_of_lt hin) _ hsh, hT] at e
  rw [treeCols_at_run hpl hR hrun σ u pre' t' i n S hn hc st, e]
  rfl

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.tab_at_round
#print axioms ProofFile.Honest.K12.Light.tables_in_front
#print axioms ProofFile.Honest.K12.Light.tree_of_round_at_run
