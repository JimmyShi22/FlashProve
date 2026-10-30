-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLTable.lean

It states no goal. No property of the protocol is claimed.

THE TABLES OF A PROXIMITY TEST's OWN TREES,
AND OF A CODE SWITCH's, AT THE JOINED SCRIPT (`joinQ`, Honest/Thread/Join.lean), AS EQUATIONS OF
FUNCTIONS: the form in which `plays_jobL` (K12/AtFile/ClosingPlays.lean) asks them (htable, hfixed).
All at letters. Four statements with their proofs; no definition.

  `ownTrees_of_test_at_joined`   `OwnTrees` at `testTbl` and `seedRound`, at a member's number that is
                                 no job's of the shared sending and at which the record holds the
                                 test's lot of trees. `join_trees_k12` (K12/JoinShare.lean) with a
                                 lighter premise: of `JoinFit` nothing is asked
  `testTable_at_joined`          so the thread's table at the test's tree number τ IS `testTbl … τ`,
                                 as a function of coins, input and challenges
  `testFixed_at_joined`          and its fixed number is front + the rounds before + `seedRound … τ`
  `switchTable_at_joined`        the same two at a code switch's member: the table is
                                 `switchTableAt`, the fixed number front + the rounds before

By what. `ofLots_ownTrees` (Honest/Thread/ScriptLots.lean), `k1TreeLots_rest`
(Honest/K1/Law/TreeLotsAtAll.lean), `join_trees_k2` (Honest/K2/Law/JoinTie.lean), `funext`.

Why the forms fit. `Script.ofLots` lays at an own tree its sender's lot's table, a total function:
there is no "first answer" and no default among own trees below the list's last. `testTbl` and
`switchTableAt` are total too: each is the table without a word where the frame lends nothing.

Hypotheses. hbs, hfr, htab, hfix: the thread's four fields are the joined Script's. hb: the member's
number is no job's of the shared sending. htl: the record holds the lot at that number. hblk: the
member.

Limits.
- No list is laid here: the jobs, the book and the record are letters; hb and htl are premises.
- The equations hold at all coins: where the frame lends the part nothing they speak of the table
  without a word. Nothing is asked of the book.
- Nothing compares how many trees the member declares with the job's number of stages.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.JoinShare
import Johnson.Desc.ProofFile.Honest.K2.Law.JoinTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open ProofFile.Honest.FirstThread
open ProofFile.Honest.K1 (SendJob PlaceIn)

section test
variable {Bk : ProverCoinCounts} {Cl Wl Xi X X₂ Cells Tok V X' Pb : Type} {bs : List (Block S Cl)} {front : ℕ}
  {arr : ℕ → ℕ → ℕ} {wit : Wl → PlaceIn Xi} {own₀ : X} {jobs : List (ℕ × SendJob (PlaceIn Xi) X)}
  {O : Others Bk Wl}

/-- **`OwnTrees` at the joined Script and the test's lot of trees**, at a member's number that is no
job's of the shared sending. -/
theorem ownTrees_of_test_at_joined (cells : Wl → Cells) (tok : Wl → Tok)
    (T : Thread Bk S Cl V Wl X' Pb) (hbs : T.bs = bs) (hfr : T.front = front)
    (htab : T.table = (joinQ bs front cells tok arr wit own₀ jobs O).table)
    (hfix : T.fixed = (joinQ bs front cells tok arr wit own₀ jobs O).fixed) (ch : ℕ)
    (J : TestJob Wl X₂) (own₂ : X₂) (n₀ : ℕ) (ok : Wl → List Fmt.Drawn → (ℕ → Stretch) → Bool)
    {b : ℕ} (hb : b ∉ jobs.map (·.1)) (htl : O.tl b = testTreeLot ch J own₂ n₀ ok)
    {blk : Block S Cl} (hblk : bs[b]? = some blk) :
    OwnTrees T b (blk.oracles.flatMap id).length (testTbl ch J own₂ n₀ ok)
      (seedRound J.p.nums.stages) := by
  have e := ofLots_ownTrees bs front cells tok (joinPl bs jobs O) (joinTl wit own₀ jobs O)
    (joinMl bs front arr wit own₀ jobs O) T hbs hfr htab hfix hblk
  have e2 : joinTl wit own₀ jobs O b = O.tl b := K1.k1TreeLots_rest wit own₀ O.tl hb
  rw [e2, htl] at e
  exact e

/-- **The thread's table at the test's tree number τ is the test's, as a function.** -/
theorem testTable_at_joined (cells : Wl → Cells) (tok : Wl → Tok)
    (T : Thread Bk S Cl V Wl X' Pb) (hbs : T.bs = bs) (hfr : T.front = front)
    (htab : T.table = (joinQ bs front cells tok arr wit own₀ jobs O).table)
    (hfix : T.fixed = (joinQ bs front cells tok arr wit own₀ jobs O).fixed) (ch : ℕ)
    (J : TestJob Wl X₂) (own₂ : X₂) (n₀ : ℕ) (ok : Wl → List Fmt.Drawn → (ℕ → Stretch) → Bool)
    {b : ℕ} (hb : b ∉ jobs.map (·.1)) (htl : O.tl b = testTreeLot ch J own₂ n₀ ok)
    {blk : Block S Cl} (hblk : bs[b]? = some blk) {τ : ℕ}
    (hτ : τ < (blk.oracles.flatMap id).length) :
    T.table (.own (treesTo T.bs b + τ)) = testTbl ch J own₂ n₀ ok τ :=
  funext fun k => funext fun w => funext fun h =>
    (ownTrees_of_test_at_joined cells tok T hbs hfr htab hfix ch J own₂ n₀ ok hb htl hblk).table τ
      hτ k w h

/-- **Its fixed number.** -/
theorem testFixed_at_joined (cells : Wl → Cells) (tok : Wl → Tok)
    (T : Thread Bk S Cl V Wl X' Pb) (hbs : T.bs = bs) (hfr : T.front = front)
    (htab : T.table = (joinQ bs front cells tok arr wit own₀ jobs O).table)
    (hfix : T.fixed = (joinQ bs front cells tok arr wit own₀ jobs O).fixed) (ch : ℕ)
    (J : TestJob Wl X₂) (own₂ : X₂) (n₀ : ℕ) (ok : Wl → List Fmt.Drawn → (ℕ → Stretch) → Bool)
    {b : ℕ} (hb : b ∉ jobs.map (·.1)) (htl : O.tl b = testTreeLot ch J own₂ n₀ ok)
    {blk : Block S Cl} (hblk : bs[b]? = some blk) {τ : ℕ}
    (hτ : τ < (blk.oracles.flatMap id).length) :
    T.fixed (.own (treesTo T.bs b + τ)) =
      T.front + roundsTo T.bs b + seedRound J.p.nums.stages τ :=
  (ownTrees_of_test_at_joined cells tok T hbs hfr htab hfix ch J own₂ n₀ ok hb htl hblk).fixed τ hτ

end test

section switch
variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xj X Cl Cells Tok V X' Pb : Type} {bs : List (Block S Cl)}
  {front : ℕ} {arr : ℕ → ℕ → ℕ} {wit : Local W₀ Rc Xi Tr → PlaceIn Xj} {own₀ : X}
  {jobs : List (ℕ × SendJob (PlaceIn Xj) X)} {O : Others Bk (Local W₀ Rc Xi Tr)}

/-- **The thread's table at a code switch's tree number j is the switch's, as a function; its fixed
number is front + the rounds before the member.** -/
theorem switchTable_at_joined (cells : Local W₀ Rc Xi Tr → Cells) (tok : Local W₀ Rc Xi Tr → Tok)
    (T : Thread Bk S Cl V (Local W₀ Rc Xi Tr) X' Pb) (hbs : T.bs = bs) (hfr : T.front = front)
    (htab : T.table = (joinQ bs front cells tok arr wit own₀ jobs O).table)
    (hfix : T.fixed = (joinQ bs front cells tok arr wit own₀ jobs O).fixed) {b : ℕ}
    (hb : b ∉ jobs.map (·.1)) {blk : Block S Cl} (hblk : bs[b]? = some blk) (ch : ℕ)
    (Sd : K2.Sender) (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (closing : K2.Closing) (p : K2.SwitchPlace)
    (htl : O.tl b =
      ⟨fun j k w h => (p.place, K2.switchTableAt Bk ch Sd D readers closing p k w h j),
        fun _ => 0⟩) {j : ℕ} (hj : j < (blk.oracles.flatMap id).length) :
    T.table (.own (treesTo T.bs b + j)) =
        (fun k w h => (p.place, K2.switchTableAt Bk ch Sd D readers closing p k w h j)) ∧
      T.fixed (.own (treesTo T.bs b + j)) = T.front + roundsTo T.bs b := by
  have e := K2.Law.join_trees_k2 cells tok T hbs hfr htab hfix hb hblk ch Sd D readers closing p htl
  exact ⟨funext fun k => funext fun w => funext fun h => e.table j hj k w h, e.fixed j hj⟩

end switch

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.ownTrees_of_test_at_joined
#print axioms ProofFile.Honest.K12.testTable_at_joined
#print axioms ProofFile.Honest.K12.testFixed_at_joined
#print axioms ProofFile.Honest.K12.switchTable_at_joined
