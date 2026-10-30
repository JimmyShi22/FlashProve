-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/WidthK1AtJoin.lean: the kind "the code switch" (K2): THE WIDTH
OF THE THREAD's TABLE, AS THE THREAD READS IT, AT A TREE OF K1's, WITHOUT `PlayedTo`: at a thread
whose four fields are the joined Script's, at a fit list, at a stand behind K1's job, wherever the
book lends the job its coins: the table has the words that the job's plan states for that tree. A
law on K1's tables. Whose trees a switch reads is no fact here: Lean's evaluator, printed at nine
links, showed two of K1's at link 2 on and three at link 1. One law: a join of calls; no definition;
nothing is evaluated here.

By, of other authors: `join_trees_k1_fit` (Honest/Thread/JoinFit.lean) · `ownTreesAt_of_own`
(Honest/Thread/ScriptLots.lean) · `treeTables_at` (Honest/K1/TableShape.lean) · `treeTbl`,
`scriptTable` (Honest/K1/ScriptLots.lean, ScriptAt.lean); ours: `words_of_ownAt`
(Honest/K2/Law/WidthsOwn.lean). Sealed: ScriptLots.lean of the thread, TableShape.lean and the two
of K1. Not sealed: JoinFit.lean, WidthsOwn.lean. Kin, sealed, of other authors: `width_by_play`,
`width_by_play_below` (Honest/Small/WidthByPlay.lean): the like end under `PlayedTo`.

Limits. F IS A PREMISE. hc: THE BOOK LENDS THE JOB ITS COINS: A PREMISE: without it the table is the
one without a word, and the end is not had. hτ AND hτr: the tree stands in the job's plan and below
the block's count of oracle messages: premises, public. THAT THE WORDS STATED HERE ARE THE WIDTH IN
A SWITCH's LIST `read`: NOT HERE: a fact on written lists. On a table's width: nothing on what it
holds. A run's coins stand under "for all" and go whole to K1's table. NOT IN FRONT OF A LAW OVER
COINS. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.WidthsOwn
import Johnson.Desc.ProofFile.Honest.Thread.JoinFit
import Johnson.Desc.ProofFile.Honest.K1.TableShape

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K1

variable {Bk : ProverCoinCounts} {Wl Xi X Cells Tok V X' Pb : Type} {bsF : Chain S ProofFile.Cl} {front : Nat}
  {arr : Nat → Nat → Nat} {seats : List (Nat × Nat)} {wit : Wl → PlaceIn Xi} {own₀ : X}
  {jobs : List (Nat × SendJob (PlaceIn Xi) X)} {Oth : Others Bk Wl}

/-- **THE WORDS OF K1's TABLE AT A STAND, WITHOUT `PlayedTo`.** -/
theorem width_k1_at_join (F : JoinFit bsF.blocksInOrder front arr seats wit own₀ jobs Oth)
    (cells : Wl → Cells) (tok : Wl → Tok) (T : Thread Bk S ProofFile.Cl V Wl X' Pb)
    (hbs : T.bs = bsF.blocksInOrder) (hfr : T.front = front)
    (htab : T.table = (joinQ bsF.blocksInOrder front cells tok arr wit own₀ jobs Oth).table)
    (hfix : T.fixed = (joinQ bsF.blocksInOrder front cells tok arr wit own₀ jobs Oth).fixed)
    {x : Nat × SendJob (PlaceIn Xi) X} (hx : x ∈ jobs) {τ : Nat} {tr : OnBytes.TreeShape}
    (hτ : x.2.P.trees[τ]? = some tr)
    (hτr : ∀ blk, bsF.blocksInOrder[x.1]? = some blk → τ < (blk.oracles.flatMap id).length)
    (Said : Nat → Coins Bk → Mid Wl X' → Prop) {b : Nat} {k : Coins Bk} {s : S}
    {m : Mid Wl X'} {E : Env} (hb : x.1 < b) (hT : ThrS T Said b k s m E)
    {c : Cs (dueR x.2.P x.2.ride)}
    (hc : lentCut k 0 ⟨x.2.P.place, 0⟩ (dueR x.2.P x.2.ride) = some c) :
    (T.tableAt (.own (treesTo T.bs x.1 + τ)) k m).2.words = tr.mainWidth + tr.maskWidth := by
  obtain ⟨blk, hblk, -, OT⟩ := join_trees_k1_fit F cells tok T hbs hfr htab hfix hx
  have e := words_of_ownAt (ownTreesAt_of_own OT Said) (hτr blk hblk) hb hT
  rw [e]
  unfold treeTbl
  rw [hc]
  show (((treeTables x.2.P (rowsLaid x.2 own₀ c (wit m.st.input) _))[τ]?).getD
    wordlessTable).words = _
  obtain ⟨T', h1, -, h3⟩ := treeTables_at x.2.P
    (rowsLaid x.2 own₀ c (wit m.st.input)
      (m.st.heard.take (T.fixed (.own (treesTo T.bs x.1 + τ))))) τ tr hτ
  rw [h1]
  exact h3

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.width_k1_at_join
