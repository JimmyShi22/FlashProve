-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/TreesOfThr.lean: hT PROPER: the
binder of plays_of_playsOn (Thread/FileRow.lean:56–57) at a proximity test whose fresh table came
earlier, general in the thread, under named premises on the thread's fillings.

  trees_of_thr   from Thr, drawsFit and Moved, the member's new trees are the thread's tables

AT THE KEY: AT MEMBER 9; FOUR OF THE EIGHT TREES. At member 10 hfresh, hhalf and htable at own 7 are
false, so this law says nothing of own 7 to 10.

The premises. On the job: hfresh, hR, hk, hst. On the thread's fillings: htable, hfixed: what an arm of
a table and a field fixed would have to say. On the block, public: hblk, hpl, hhalf, hrs, hcount (hrs and
hst are spare under Moved, by a hostile reader's word; they stand because table_in_run takes them).
Thr hands the rest: E.sent by Made, the heard's length by Fit.

This is a tie of a text to a run: what TableOfRun.lean's head says holds here, RowsOfHeard
and tables_at_frontAt named beside it, the book's fact not entered.
Thr and Moved reach as premises: so NOT IN FRONT OF A LAW OVER COINS.

A YES WOULD NOT SHOW: that any thread meets htable: no filling has these arms · that Thr stands
anywhere at such a member · that a run reaches Moved: at the key the law may be true and empty until
play is shown to return · J.fresh = none, own 7, or
a half behind the guard: not stated · Plays itself, which also asks PlaysOn · anything over coins, and
nothing on hiding.

Limits. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.TableOfRun
import Johnson.Desc.ProofFile.Honest.K14.KitTwo
import Johnson.Desc.ProofFile.Honest.Law.Thread
import Johnson.Desc.ProofFile.Honest.Law.Along

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc (Block)

/-- **hT, at a proximity test whose fresh table came earlier.**
NOT IN FRONT OF A LAW OVER COINS: it stands behind Thr and Moved; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. -/
theorem trees_of_thr {S Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl V W X Pb) {b : ℕ}
    {blk : Block S Cl} (hblk : T.bs[b]? = some blk) (J : TestJob W X)
    (hfresh : J.fresh.isNone = false) (hR : RowsOfHeard J)
    (hk : ∀ a ∈ J.p.nums.stages, a.h ≤ a.k)
    (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: t :: rest)
    (hpl : blk.place = J.p.place)
    (hhalf : (T.hs.find? fun g => g.place == blk.place) = some (proverSideOfProximityTest J))
    (hrs : (blk.rounds.zip blk.oracles).length =
      firstLen J.p.nums.stages + restLen J.p.nums.stages)
    (hcount : (blk.oracles.flatMap id).length + 1 = J.p.nums.stages.length)
    (own₀ : X)
    (htable : ∀ τ, τ + 1 < J.p.nums.stages.length → T.table (.own (treesTo T.bs b + τ)) =
      testTbl T.chain J own₀ (T.front + roundsTo T.bs b) (fun _ _ _ => true) τ)
    (hfixed : ∀ τ, τ + 1 < J.p.nums.stages.length → T.fixed (.own (treesTo T.bs b + τ)) =
      T.front + roundsTo T.bs b + seedRound J.p.nums.stages τ) :
    ∀ k st m E ds y cols, Thr T b k st m E → drawsFit blk.rounds ds = true →
      T.Moved blk k m E ds y cols → T.Trees (T.fresh b) k y.2 (E.add y.1) := by
  intro k st m E ds y cols hT _ hMv σ hσ
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hMv
  obtain ⟨c, hc, rfl⟩ := steps_one_half hhalf hl
  rw [hpl] at hc
  have hy' : play (rowSteps blk.name J.p.place (T.φ.sees m.st.input)
      [(firstPart J : Part V W X), restPart J] 0 (blk.rounds.zip blk.oracles) c) ds [] m =
      .ok y := by
    have e := hy
    unfold Placed.steps at e
    rw [hpl] at e
    exact e
  obtain ⟨i, hi, rfl⟩ := K14.fresh_mem_own T hblk hσ
  have hi' : i + 1 < J.p.nums.stages.length := by omega
  have hsent : E.sent = treesTo T.bs b := hT.2.2.2.2.1.2.2.1
  have hheard : m.st.heard.length = T.front + roundsTo T.bs b := by
    have e := drawsFit_length _ _ hT.2.1
    rw [List.length_append] at e
    exact e
  obtain ⟨-, hst2⟩ := half_tables J s t rest hst blk.name (T.φ.sees m.st.input) _ hrs c ds [] m y hy'
  have hin : y.2.st.input = m.st.input := by rw [hst2]
  have hhd : y.2.st.heard = m.st.heard ++ ds := by rw [hst2]
  have hmain := table_in_run J hR hk s t rest hst blk.name (T.φ.sees m.st.input) _ hrs T.chain k c hc
    ds [] m y hy' own₀ _ hheard hi'
    ((m.st.heard ++ ds).take (T.front + roundsTo T.bs b + seedRound J.p.nums.stages i))
    (by rw [List.take_take, Nat.min_self])
  rw [hfresh] at hmain
  simp only [Bool.false_eq_true, if_false, Nat.add_zero] at hmain
  have htree : (E.add y.1).tree (.own (treesTo T.bs b + i)) =
      some (testTbl T.chain J own₀ (T.front + roundsTo T.bs b) (fun _ _ _ => true) i k m.st.input
        ((m.st.heard ++ ds).take (T.front + roundsTo T.bs b + seedRound J.p.nums.stages i))) := by
    rw [← hsent, K14.add_own, hmain]
    rfl
  have htab : T.tableAt (.own (treesTo T.bs b + i)) k y.2 =
      testTbl T.chain J own₀ (T.front + roundsTo T.bs b) (fun _ _ _ => true) i k m.st.input
        ((m.st.heard ++ ds).take (T.front + roundsTo T.bs b + seedRound J.p.nums.stages i)) := by
    unfold Thread.tableAt
    rw [htable i hi', hfixed i hi', hhd, hin]
  unfold Thread.handAt
  rw [htree, htab]
  simp [Table.same_refl]

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.trees_of_thr
