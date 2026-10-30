-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/TableShared.lean: what the shared chain's thread
(`lettersShared`, Honest/Thread/SharedHead.lean) lays at its fields on trees: a tree's table and the count
of challenges that fix it, as terms; and what these give at a stand in front of the test on G_u.

  `tableShared` (AtFullSide/K12/LaterJobs.lean)  a tree's table: own 0 to 2 the two sendings' (`sendTable`, Honest/K14/SendingsPaid.lean),
                 own 3 to 6 the test on G_u's (`testTbl`, K12/ScriptLots.lean), own 7 the first fold's
                 own table at the test on G_omega (`ownTbl`, K12/OwnTbl.lean), own 8 to 10 that test's
  `fixedShared` (LaterJobs.lean)  after how many challenges: the round that sends the tree (`sentIn`)
  `takesCover`   a public test: the book's row at a sending covers what its part takes
  `send_words`   so a sending's table has its shape's words at every coin, input and list
  `words_low`    so own 0 to 2 of `tableShared` have `tableWidth`'s words (WideLines.lean)
  `rounds_head_U`   under the head the seated test's rounds are the written ones
  `old_head_U`   `RunPlays.old` at a stand of `Thr` at 9

Why the numbers 8 and 43. Eight rounds stand in front of the test on G_u, and 43 in front of the test on
G_omega: `seed_U`, `seed_O`, `sent_shared` (TableLines.lean) hold them against the written rounds.

Limits.
- `ownTbl` is a text at part 0's coins. Its head binds whoever lays it: no sentence over coins on it
  before that head's terms are met.
- `tableShared` at a taken source is a table of no word: the shared chain takes no tree over.
- That a thread lays these terms is for whoever lays it; that the trees it names are what the run sends
  is `trees_of_thr`'s and its premises'.
- NOT IN FRONT OF A LAW OVER COINS: `old_head_U` has `Thr` as a premise.
- The full size alone. Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WideLines
import Johnson.Desc.ProofFile.Honest.K12.AtFile.PlaysAtTest
import Johnson.Desc.ProofFile.Honest.K12.AtFile.PlanAtSeat
import Johnson.Desc.ProofFile.Honest.K12.OwnTbl
import AtFullSide.K12.LaterJobs
import Johnson.Desc.ProofFile.Honest.K12.ScriptLots
import Johnson.Desc.ProofFile.Honest.K14.SendingsPaid
import Johnson.Desc.ProofFile.Honest.K14.PaidAll
import Johnson.Desc.ProofFile.Honest.Small.FixedSent

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

noncomputable section

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K14 (SendPub SendJob jobU jobOmega sendPlace sendTable sendTablesAt sentTables
  sendingPart witOf treesU Ask)
open ProofFile.Honest.K12 (TestJob testTbl ownTbl oldSrc)
open OnBytes (TableKey)
open VerifiableInference.Desc (Block Place)
open VerifiableInference.Desc (K1.qAt)
open VerifiableInference.Desc.K1 (realSized)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open Desc.K14 (P14)
open H2K.Member (piUFull)
open ProofFile.Honest.K12.AtProof (fourOf)
open ProofFile.Honest.K12.Light (planOf written_at_head qAt_written nums_head_U planOk_head_U)

/-- The book's row at a sending covers what its part takes. -/
def takesCover (B : ProverCoinCounts) (a : Addr) (J : SendJob) : Bool :=
  decide ((sendingPart J).takes.f ≤ (dueAt (B.rowsOf 1) a).f) &&
    decide ((sendingPart J).takes.e ≤ (dueAt (B.rowsOf 1) a).e)

theorem sent_words (codes : OnBytes.Codes) (sent : Array OnBytes.OracleNotice) (L : ℕ → K14.Laid)
    (i : ℕ) : ((sentTables codes sent L).getD i K1.wordlessTable).words =
      (shapeWords codes sent).getD i 0 := by
  unfold sentTables shapeWords
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map,
    List.getElem?_zipIdx]
  cases ((VerifiableInference.Desc.Own.treesMade codes sent).getD {}).shapes.toList[i]? <;> rfl

/-- **Where a sending's coins lie within the book, its table has its shape's words**, at every coin,
input and list. -/
theorem send_words {Bk : ProverCoinCounts} {W : Type} (J : SendJob) (wit : W → Ask) (pl : Place) (i : ℕ)
    (k : Coins Bk) (w : W) (h : List Fmt.Drawn) (ht : takesCover Bk ⟨pl, 0⟩ J = true) :
    (sendTable J wit pl 1 i k w h).2.words = (shapeWords J.Q.codes J.Q.sent).getD i 0 := by
  have hd : (k.look 1 ⟨pl, 0⟩).1 = dueAt (Bk.rowsOf 1) ⟨pl, 0⟩ := AtPublicFiles.KeyBook.look_due k 1 ⟨pl, 0⟩
  unfold takesCover at ht
  rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at ht
  have hcut : ∃ own, (k.look 1 ⟨pl, 0⟩).2.cut ⟨0, 0⟩ (sendingPart J).takes = some own :=
    AtPublicFiles.KeyBook.cut_some _ _ _ ⟨by rw [hd]; show 0 + _ ≤ _; omega,
                by rw [hd]; show 0 + _ ≤ _; omega⟩
  obtain ⟨own, hown⟩ := hcut
  unfold sendTable
  simp only [hown]
  exact sent_words _ _ _ _

section
variable {Bk : ProverCoinCounts} {W₀ Rc X₀ : Type} (Q : P14) (wts : W₀ → Weights) (rnd : Rc → TableRand)
  (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)

/-- **At own 0 to 2 the table has `tableWidth`'s words**, at every coin, input and list. -/
theorem words_low (h3 : treesU Q ≤ 3) (n : ℕ) (hn : n < 3) (k : Coins Bk)
    (w : Common W₀ Rc TableKey) (h : List Fmt.Drawn)
    (c2 : takesCover Bk ⟨sendPlace 2, 0⟩ (jobU ⟨Q, 0⟩) = true)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨Q, 0⟩) = true) :
    (tableShared Q wts rnd JU JO own₀ (.own n) k w h).2.words = tableWidth ⟨Q, 0⟩ n := by
  unfold tableShared tableWidth
  by_cases c : n < treesU Q
  · simp only [if_pos c]
    exact send_words _ _ _ _ _ _ _ c2
  · simp only [if_neg c, if_pos hn]
    exact send_words _ _ _ _ _ _ _ c5

end

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}

/-- **Under the head the seated test's rounds are the written ones.** -/
theorem rounds_head_U (h : P5J.AtMg o Z D r Zp Np cF) :
    (proximityTestKind guardedProximityTestParts (fourOf Np).U : Block T12 Unit).rounds =
      (proximityTestKind guardedProximityTestParts piUFull : Block T12 Unit).rounds := by
  refine Option.some.inj ?_
  rw [← VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts _ (planOk_head_U h),
    ← VerifiableInference.Desc.K12.k12_rounds guardedProximityTestParts _
      VerifiableInference.Desc.K12.Coin.At.closed_UFull.plan, nums_head_U h]

/-- **`RunPlays.old` at a stand of `Thr` at 9.** hb: three trees in front; ht: the thread takes none
over; htb: its table is `tableShared`; c2, c5: the book covers the sendings. -/
theorem old_head_U {W₀ Rc X₀ S Cl V Pb : Type} {Bk : ProverCoinCounts} (h : P5J.AtMg o Z D r Zp Np cF)
    (T : Thread Bk S Cl V (Common W₀ Rc TableKey) X₀ Pb) (wts : W₀ → Weights) (rnd : Rc → TableRand)
    (JU JO : TestJob (Common W₀ Rc TableKey) X₀) (own₀ : X₀)
    (hb : treesTo T.bs 9 = 3) (ht : T.taken = [])
    (htb : T.table = tableShared (K1.qAt Zp Np) wts rnd JU JO own₀)
    (c2 : takesCover Bk ⟨sendPlace 2, 0⟩ (jobU ⟨K1.qAt Zp Np, 0⟩) = true)
    (c5 : takesCover Bk ⟨sendPlace 5, 0⟩ (jobOmega ⟨K1.qAt Zp Np, 0⟩) = true)
    (h3 : treesU (K1.qAt Zp Np) ≤ 3)
    {k : Coins Bk} {s : S} {m : Mid (Common W₀ Rc TableKey) X₀} {E : Env} (u : Thr T 9 k s m E) :
    ∀ d ∈ (proximityTestKind guardedProximityTestParts (fourOf Np).U : Block T12 Unit).rounds, ∀ o ∈ d.opens,
      oldSrc E.sent o.2 = true → ∃ pt, E.tree o.2 = some pt ∧ pt.2.words = o.1.W := by
  obtain ⟨x, hx, Wr⟩ := written_at_head h
  have hw := wide_U
  rw [hx] at hw
  simp only [Option.all_some] at hw
  refine old_of_hand T _ (fun d hd o ho hO => ?_) u
  rw [hb] at hO
  rw [rounds_head_U h] at hd
  have a2 := List.all_eq_true.1 (List.all_eq_true.1 hw d hd) o ho
  rw [hO] at a2
  cases hσ : o.2 with
  | taken a b =>
    rw [hσ] at a2
    simp at a2
  | own n =>
    rw [hσ] at a2 hO
    have hn : n < 3 := of_decide_eq_true hO
    have hW : o.1.W = tableWidth (planOf Johnson.G.codesFull2 x.shape) n := by simpa using a2
    refine ⟨?_, fun k' w' h' => ?_⟩
    · show _ ∈ T.taken ++ (List.range (treesTo T.bs 9)).map Fmt.TreeSource.own
      rw [ht, hb]
      exact List.mem_append_right _ (List.mem_map.2 ⟨n, List.mem_range.2 hn, rfl⟩)
    · rw [htb, words_low _ wts rnd JU JO own₀ h3 n hn k' w' h' c2 c5, hW, qAt_written Wr Np]
      rfl

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.send_words
#print axioms ProofFile.Honest.K12.AtFile.words_low
#print axioms ProofFile.Honest.K12.AtFile.rounds_head_U
#print axioms ProofFile.Honest.K12.AtFile.old_head_U
