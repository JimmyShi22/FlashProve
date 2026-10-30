-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/SeatedPlaysS.lean: THE FRAME's SENTENCE "IT PLAYS", ASKED FROM THE
PAIR OF A THREAD AND "THE PROVER's RUN STANDS WHERE THE FRAME's OWN PLAY STANDS" (`PlaysS`,
Johnson/Desc/ProofFile/Honest/Thread/PaysS.lean, at `PlayedTo`,
Johnson/Desc/ProofFile/Honest/Small/PlayedTo.lean), AT A MEMBER OF A CHAIN AT WHICH A SEATED
PROXIMITY TEST STANDS, WITH THE HALF `proverSideOfProximityTest J`: WHOLE: the member's new trees are the thread's
tables too. In SeatedPlays.lean in this folder that second half of the end is asked. Here the
thread's own trees' tables are those that the frame's play sends (`tableBy`), and `playsS_by_play`
(in PlayedTo.lean) leaves to show at the member that its play and the laying of its columns return:
that is `playsOn_k12` (PlaysK12.lean). A structure of named premises, a statement and its proof.

  `K12PlayedS`   THE PREMISES ON THE THREAD's LETTERS, each under its name:
                 member   the chain's member number b is a block that seats the test (`SeatOf`)
                 half     the half that stands at the test's place is `proverSideOfProximityTest J`
                 stages   two stages or more, k = h + g at the first, and `PlanPlays`: on the plan
                 stands   FROM THE PAIR IN FRONT, at every run's coins, at whatever coins the book
                          lends the two parts: `RunPlays`
                 tables   the thread's own trees' tables are `tableBy`
                 fixed    each is fixed by the challenges in front of the round that sends it
                 listed   every sub-protocol of the chain lists as many oracle messages as its
                          rounds count roots
                 laid     the whole chain's steps are laid, at all coins and inputs
  **`playsS_k12`**   `K12PlayedS` ⟹ `PlaysS T (PlayedTo T start) b`
  `K12PlayedSBelow`, `K12PlayedS.below`, `playsS_k12_below`   the same with less asked in "tables"
                 and "fixed": below the chain's last tree alone, as `trees_by_play_below`
                 (PlayedTo.lean) asks them; `playsS_k12` is a call of `playsS_k12_below`

Limits. `K12PlayedS` is asked; no thread is shown to meet it. THE CLAUSE "tables" BINDS ALL OWN
TREES OF THE CHAIN, AND "laid" ASKS THE WHOLE CHAIN's STEPS (StepsReturn.lean has one member's). THE
TABLES ARE TRUE BY MAKE: the form of "the new trees are the thread's tables" is paid, none of its
content: that such a table encodes a message of the thread's witness is not shown: see
PlayedTo.lean's limits, which stand here. BY TYPE A THREAD's TABLE IS A FUNCTION OF A RUN's COINS,
THE INPUT AND THE CHALLENGES HEARD, while the test's term reads a front (what was handed on, the
rounds shown): `tableBy` bridges that by playing the whole chain anew from its start. `PlaysS` is a
premise's form of the frame's: it is met for nothing where the frame's laying of the member's steps
does not return. Nothing on completeness, on soundness or on what is hidden.


-/
import Johnson.Desc.ProofFile.Honest.K12.PlaysK12
import Johnson.Desc.ProofFile.Honest.Small.PlayedTo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)
open ProofFile.Honest.Small (PlayedTo tableBy sentAt sent_of_tableBy playsS_by_play_below sentIn Listed)

variable {S Cl V W X Pb : Type} {Bk : ProverCoinCounts}

/-- **The premises on the thread's letters.** start: where the chain's run begins. dflt: a default
table. sent: the number of trees sent in front. -/
structure K12PlayedS (T : Thread Bk S Cl V W X Pb)
    (start : Coins Bk → W → List Fmt.Drawn → Mid W X) (dflt : Place × Table) (b : ℕ)
    (J : TestJob W X) (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (sent : ℕ) : Prop where
  member : ∃ blk, T.bs[b]? = some blk ∧ SeatOf blk J enter leave
  half : (T.hs.find? fun g => g.place == J.p.place) = some (proverSideOfProximityTest J)
  stages : ∃ s t rest, J.p.nums.stages = s :: t :: rest ∧ s.k = (sgOf s).h + (sgOf s).g ∧
    PlanPlays J s (t :: rest) sent
  stands : ∀ k st m E ds (c : RowCoins [(firstPart J : Part V W X), restPart J]),
    ThrS T (PlayedTo T start) b k st m E →
    drawsFit (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds ds = true →
    lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) J.p.place
      [(firstPart J : Part V W X), restPart J] 0 = .ok c →
    RunPlays J sent m E c
  tables : ∀ j k w h, T.table (.own j) k w h = tableBy T start dflt j k w h
  fixed : ∀ j, T.fixed (.own j) = T.front + sentIn (T.bs.flatMap (·.rounds)) j
  listed : ∀ x ∈ T.bs, Listed x
  laid : ∀ (k : Coins Bk) (w : W), ∃ Lall,
    chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees w) T.bs T.hs = .ok Lall

/-- **`K12PlayedS`, with less asked in the clauses "tables" and "fixed"**: both as
`trees_by_play_below` (Johnson/Desc/ProofFile/Honest/Small/PlayedTo.lean) asks them: below the
chain's last tree alone; "tables" only at lists of challenges as long as `fixed` counts and where
the frame's play has sent the tree, and as "the same place, and `Table.same`". No default is named.
The six other clauses are those of `K12PlayedS`. -/
structure K12PlayedSBelow (T : Thread Bk S Cl V W X Pb)
    (start : Coins Bk → W → List Fmt.Drawn → Mid W X) (b : ℕ)
    (J : TestJob W X) (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (sent : ℕ) : Prop where
  member : ∃ blk, T.bs[b]? = some blk ∧ SeatOf blk J enter leave
  half : (T.hs.find? fun g => g.place == J.p.place) = some (proverSideOfProximityTest J)
  stages : ∃ s t rest, J.p.nums.stages = s :: t :: rest ∧ s.k = (sgOf s).h + (sgOf s).g ∧
    PlanPlays J s (t :: rest) sent
  stands : ∀ k st m E ds (c : RowCoins [(firstPart J : Part V W X), restPart J]),
    ThrS T (PlayedTo T start) b k st m E →
    drawsFit (proximityTestKind guardedProximityTestParts J.p : Block T12 Unit).rounds ds = true →
    lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) J.p.place
      [(firstPart J : Part V W X), restPart J] 0 = .ok c →
    RunPlays J sent m E c
  tables : ∀ j, j < treesTo T.bs T.bs.length → ∀ k w h u, h.length = T.fixed (.own j) →
    sentAt T start j k w h = some u →
    u.1 = (T.table (.own j) k w h).1 ∧ u.2.same (T.table (.own j) k w h).2 = true
  fixed : ∀ j, j < treesTo T.bs T.bs.length →
    T.fixed (.own j) = T.front + sentIn (T.bs.flatMap (·.rounds)) j
  listed : ∀ x ∈ T.bs, Listed x
  laid : ∀ (k : Coins Bk) (w : W), ∃ Lall,
    chainSteps Bk (Bk.rowsOf T.chain) (k.look T.chain) (T.φ.sees w) T.bs T.hs = .ok Lall

/-- The wider clauses give the narrower ones. -/
theorem K12PlayedS.below {T : Thread Bk S Cl V W X Pb}
    {start : Coins Bk → W → List Fmt.Drawn → Mid W X} {dflt : Place × Table} {b : ℕ}
    {J : TestJob W X} {enter : S → Except String T12} {leave : S → T12 → Except String S}
    {sent : ℕ} (h : K12PlayedS T start dflt b J enter leave sent) :
    K12PlayedSBelow T start b J enter leave sent :=
  ⟨h.member, h.half, h.stages, h.stands, sent_of_tableBy T start dflt fun j _ => h.tables j,
    fun j _ => h.fixed j, h.listed, h.laid⟩

/-- **It plays, and its new trees are the thread's tables**, from the narrower clauses. -/
theorem playsS_k12_below (T : Thread Bk S Cl V W X Pb)
    (start : Coins Bk → W → List Fmt.Drawn → Mid W X) (b : ℕ)
    (J : TestJob W X) (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (sent : ℕ) (h : K12PlayedSBelow T start b J enter leave sent) :
    PlaysS T (PlayedTo T start) b := by
  obtain ⟨s, t, rest, hst, hk, P⟩ := h.stages
  obtain ⟨blk, hblk, hseat⟩ := h.member
  have hP := playsOn_k12 T.φ Bk T.chain T.ft T.hs blk J enter leave hseat
    (ThrS T (PlayedTo T start) b) (fun _ _ _ _ => True) s t rest hst hk h.half sent P h.stands
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial
  refine playsS_by_play_below T start h.tables h.fixed h.listed hblk (g := proverSideOfProximityTest J) (by
                     rw [hseat.place]
                     exact h.half) h.laid fun k st m E ds l hT hd hstop hl => ?_
  obtain ⟨y, cols, hy, hc, -⟩ := hP k st m E ds l hT hd hstop hl
  exact ⟨y, cols, ⟨l, hl, hy⟩, hc⟩

/-- **It plays, and its new trees are the thread's tables.** -/
theorem playsS_k12 (T : Thread Bk S Cl V W X Pb)
    (start : Coins Bk → W → List Fmt.Drawn → Mid W X) (dflt : Place × Table) (b : ℕ)
    (J : TestJob W X) (enter : S → Except String T12) (leave : S → T12 → Except String S)
    (sent : ℕ) (h : K12PlayedS T start dflt b J enter leave sent) :
    PlaysS T (PlayedTo T start) b :=
  playsS_k12_below T start b J enter leave sent h.below

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.playsS_k12
#print axioms ProofFile.Honest.K12.K12PlayedSBelow
#print axioms ProofFile.Honest.K12.K12PlayedS.below
#print axioms ProofFile.Honest.K12.playsS_k12_below
