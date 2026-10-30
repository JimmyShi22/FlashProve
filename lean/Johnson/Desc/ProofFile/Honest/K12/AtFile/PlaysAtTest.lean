-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/PlaysAtTest.lean: the frame's sentence «it plays», asked from
a thread's pair (`PlaysS`, Honest/Thread/PaysS.lean), at a member at which a seated proximity test stands,
with the half `proverSideOfProximityTest J`, from what the plan says (`PlanPlays`) and three sentences at a stand. General
in the thread, the letter, the job and the number of trees in front. It serves a test whose half stands
with no guard: at the proof file the test on G_u. Two theorems.

  `old_of_hand`   `RunPlays.old` at a stand, where each old opening is in hand at the border and the
                 thread's table there has the declared width
  `playsS_at_test`   `PlaysS` at the member

By what. `playsOn_k12` (K12/PlaysK12.lean) at A the thread's pair; `Thread.handAt_elim`
(Honest/Thread/Sent.lean) for the widths; `Made`, inside `Thr`, for the count of trees.

The premises of `playsS_at_test`. hblk, hseat, hst, hk, hf: the member is the seated test and the half
stands at its place. P: the plan, under the head `planPlays_head_U` (PlanAtSeat.lean). hsent: the number
of trees in front. hA: the two parts' readers agree at the coins that the frame lends: `agree_of_ties` (K12/AgreeBook.lean). hold: `old_of_hand`. hT: the member's new trees
are the thread's tables: `trees_of_thr` (K12/TreesOfThr.lean).

Limits.
- NOT IN FRONT OF A LAW OVER COINS: `playsS_at_test` has the thread's pair as a premise and `PlaysS` as its
  end, and `PlaysS` has that pair as a premise.
- That the pair holds at any run is not said here. At a thread that holds nowhere it is idle.
- Where a half stands behind the guard (G_omega, the last chain) the half is no `proverSideOfProximityTest J`: hf is false
  there, and a twin is owed that hands the field.
- Nothing on completeness, on soundness or on what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.PlaysK12
import Johnson.Desc.ProofFile.Honest.Thread.PaysS
import Johnson.Desc.ProofFile.Honest.Thread.Sent

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open ProofFile.Honest
open ProofFile.Honest.K12
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.K12 (T12 proximityTestKind guardedProximityTestParts)
open H2K.Pub (sgOf)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **`RunPlays.old` at a stand**, where each old opening is in hand at the border and the thread's
table there has the declared width, at every coin, input and list of challenges. -/
theorem old_of_hand (T : Thread Bk S Cl V W X Pb) {b : ℕ} (decls : List Fmt.DeclaredRound)
    (hw : ∀ d ∈ decls, ∀ o ∈ d.opens, oldSrc (treesTo T.bs b) o.2 = true →
      o.2 ∈ T.hand b ∧ ∀ k w h, (T.table o.2 k w h).2.words = o.1.W)
    {k : Coins Bk} {s : S} {m : Mid W X} {E : Env} (u : Thr T b k s m E) :
    ∀ d ∈ decls, ∀ o ∈ d.opens, oldSrc E.sent o.2 = true →
      ∃ pt, E.tree o.2 = some pt ∧ pt.2.words = o.1.W := by
  obtain ⟨⟨-, hH⟩, -, -, -, ⟨-, -, hsent, -⟩, -, -⟩ := u
  intro d hd o ho hO
  rw [hsent] at hO
  obtain ⟨hin, hwd⟩ := hw d hd o ho hO
  obtain ⟨pt, hE, -, hs⟩ := T.handAt_elim (hH _ hin)
  unfold Table.same at hs
  rw [Bool.and_eq_true, Bool.and_eq_true] at hs
  refine ⟨pt, hE, (beq_iff_eq.1 hs.1.2).trans ?_⟩
  exact hwd k _ _

/-- **It plays, and its new trees are the thread's tables.** -/
theorem playsS_at_test (T : Thread Bk S Cl V W X Pb) (Said : ℕ → Coins Bk → Mid W X → Prop) {b : ℕ}
    {blk : Block S Cl} (hblk : T.bs[b]? = some blk) (J : TestJob W X)
    (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (hseat : SeatOf blk J enter leave) (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage)
    (hst : J.p.nums.stages = s :: t :: rest) (hk : s.k = (sgOf s).h + (sgOf s).g)
    (hf : (T.hs.find? fun g => g.place == J.p.place) = some (proverSideOfProximityTest J)) (sent : ℕ)
    (P : PlanPlays J s (t :: rest) sent) (hsent : treesTo T.bs b = sent)
    (hA : ∀ k st m E (c : RowCoins [(firstPart J : Part V W X), restPart J]),
      ThrS T Said b k st m E →
      lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) J.p.place
        [(firstPart J : Part V W X), restPart J] 0 = .ok c →
      Agree J m.st.input (frontOf m) J.s₀ (firstRd J c.1) (restCoins J c.2.1))
    (hold : ∀ k st m E, ThrS T Said b k st m E →
      ∀ d ∈ (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds, ∀ o ∈ d.opens, oldSrc E.sent o.2 = true →
        ∃ pt, E.tree o.2 = some pt ∧ pt.2.words = o.1.W)
    (hT : ∀ k st m E ds y cols, ThrS T Said b k st m E → drawsFit blk.rounds ds = true →
      T.Moved blk k m E ds y cols → T.Trees (T.fresh b) k y.2 (E.add y.1)) :
    PlaysS T Said b := by
  have hP := playsOn_k12 T.φ Bk T.chain T.ft T.hs blk J enter leave hseat (ThrS T Said b)
    (fun _ _ _ _ => True) s t rest hst hk hf sent P
    (fun k st m E _ c u _ hc =>
      ⟨hA k st m E c u hc, by
        obtain ⟨⟨-, -, -, -, ⟨-, -, h3, -⟩, -, -⟩, -⟩ := u
        rw [h3, hsent], hold k st m E u⟩)
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  intro blk' hblk' k st m E ds l u hd hs hl
  rw [hblk] at hblk'
  cases hblk'
  obtain ⟨y, cols, hy, hc, -⟩ := hP k st m E ds l u hd hs hl
  have hMv : T.Moved blk k m E ds y cols := ⟨⟨l, hl, hy⟩, hc⟩
  exact ⟨y, cols, hMv, hT k st m E ds y cols u hd hMv⟩

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.old_of_hand
#print axioms ProofFile.Honest.K12.AtFile.playsS_at_test
