-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/TreesAtTen.lean: THE TWIN OF
trees_of_thr (TreesOfThr.lean) at a proximity test whose first fold sends its own table, behind the guard.


  trees_of_thr_own   from Thr, the field, drawsFit and Moved, the member's new trees are the thread's
                 tables: tree 0 by own_in_run, tree τ + 1 by table_in_run
  opened_of_play     a play of a guarded half that returned began at a field that is some
  trees_of_thr_ten   the same with no premise on the field: hT's form to the sign

AT THE KEY: AT MEMBER 10; THE OTHER FOUR OF THE EIGHT TREES.

trees_of_thr_own HAS ONE PREMISE MORE THAN hT, m.opened.isSome; trees_of_thr_ten HAS NOT: it is hT to the
sign: under Moved the premise is spare, by opened_of_play: at the field none play of a guarded step with a
move does not return (play_guarded_none), and Moved holds a play that returned. What is forced is of
Plays, not of this law: bare Plays at such a member asks a return at the field none, and so is false
wherever playable; PlaysOn from A := Thr cannot be had there.

The premises. On the job: hfresh, hR, hk, hst. On the thread's fillings: htable₀, htable, hfixed₀, hfixed.
On the block, public: hblk, hpl, hhalf, hrs, hcount. At the run: the field is some. V is Empty, by
own_in_run. Thr hands the rest: E.sent by Made, the heard's length by Fit.

Ties of texts to a run: what TableOfRun.lean's head and OwnTbl.lean's (0-1) to (0-3) say holds
here. Beside them: RowsOfHeard and tables_at_frontAt at own 8 to 10,
tables_at_own_round at own 7. The book's fact does not enter. NOT IN FRONT OF A LAW OVER COINS.

A YES WOULD NOT SHOW: that any thread has these arms · that Thr stands at such a member, or that the field
is some there: that is the letter's · that a run reaches Moved ·
Plays · the vals of any round, widths, Sending.fits · anything over coins, and nothing on
hiding. Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.TreesOfThr
import Johnson.Desc.ProofFile.Honest.K12.OwnTbl
import Johnson.Desc.ProofFile.Honest.K12.FieldGuardLift

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc (Block)

/-- **hT's twin, at a proximity test whose first fold sends its own table, behind the guard.**
NOT IN FRONT OF A LAW OVER COINS: it stands behind Thr and Moved; the rule is at its home, the head of
Johnson/Bind/ForProver/FiveFieldsAt.lean. -/
theorem trees_of_thr_own {S Cl W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl Empty W X Pb) {b : ℕ}
    {blk : Block S Cl} (hblk : T.bs[b]? = some blk) (J : TestJob W X)
    (hfresh : J.fresh = none) (hR : RowsOfHeard J)
    (hk : ∀ a ∈ J.p.nums.stages, a.h ≤ a.k)
    (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: t :: rest)
    (hpl : blk.place = J.p.place)
    (hhalf : (T.hs.find? fun g => g.place == blk.place) = some (proverSideOfProximityTest J).needsField)
    (hrs : (blk.rounds.zip blk.oracles).length =
      firstLen J.p.nums.stages + restLen J.p.nums.stages)
    (hcount : (blk.oracles.flatMap id).length = J.p.nums.stages.length)
    (own₀ : X)
    (htable₀ : T.table (.own (treesTo T.bs b)) =
      ownTbl T.chain J own₀ (T.front + roundsTo T.bs b) (fun _ _ _ => true))
    (htable : ∀ τ, τ + 1 < J.p.nums.stages.length → T.table (.own (treesTo T.bs b + (τ + 1))) =
      testTbl T.chain J own₀ (T.front + roundsTo T.bs b) (fun _ _ _ => true) τ)
    (hfixed₀ : T.fixed (.own (treesTo T.bs b)) = T.front + roundsTo T.bs b + 1)
    (hfixed : ∀ τ, τ + 1 < J.p.nums.stages.length → T.fixed (.own (treesTo T.bs b + (τ + 1))) =
      T.front + roundsTo T.bs b + seedRound J.p.nums.stages τ) :
    ∀ k st m E ds y cols, Thr T b k st m E → m.opened.isSome = true →
      drawsFit blk.rounds ds = true → T.Moved blk k m E ds y cols →
      T.Trees (T.fresh b) k y.2 (E.add y.1) := by
  intro k st m E ds y cols hT hop _ hMv σ hσ
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hMv
  obtain ⟨c', hc', rfl⟩ := steps_one_half hhalf hl
  have hc'' : lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) blk.place
      ((proverSideOfProximityTest J : Placed Empty W X).parts.map Part.needsField) 0 = .ok c' := hc'
  rw [lendRow_guarded] at hc''
  obtain ⟨c, hc, rfl⟩ := map_ok hc''
  rw [placedSteps_guarded (proverSideOfProximityTest J) blk (T.φ.sees m.st.input) c] at hy
  obtain ⟨cs, hcs⟩ := Option.isSome_iff_exists.1 hop
  rw [play_guarded _ ds [] m cs hcs] at hy
  rw [hpl] at hc
  have hy' : play (rowSteps blk.name J.p.place (T.φ.sees m.st.input)
      [(firstPart J : Part Empty W X), restPart J] 0 (blk.rounds.zip blk.oracles) c) ds [] m =
      .ok y := by
    have e := hy
    unfold Placed.steps at e
    rw [hpl] at e
    exact e
  obtain ⟨i, hi, rfl⟩ := K14.fresh_mem_own T hblk hσ
  have hsent : E.sent = treesTo T.bs b := hT.2.2.2.2.1.2.2.1
  have hheard : m.st.heard.length = T.front + roundsTo T.bs b := by
    have e := drawsFit_length _ _ hT.2.1
    rw [List.length_append] at e
    exact e
  obtain ⟨-, hst2⟩ := half_tables J s t rest hst blk.name (T.φ.sees m.st.input) _ hrs c ds [] m y hy'
  have hin : y.2.st.input = m.st.input := by rw [hst2]
  have hhd : y.2.st.heard = m.st.heard ++ ds := by rw [hst2]
  cases i with
  | zero =>
    have hmain := own_in_run J hfresh s t rest hst blk.name (T.φ.sees m.st.input) _ hrs T.chain k c hc
      ds [] m y hy' own₀ _ hheard
      ((m.st.heard ++ ds).take (T.front + roundsTo T.bs b + 1))
      (by rw [List.take_take, Nat.min_self])
    have htree : (E.add y.1).tree (.own (treesTo T.bs b + 0)) =
        some (ownTbl T.chain J own₀ (T.front + roundsTo T.bs b) (fun _ _ _ => true) k m.st.input
          ((m.st.heard ++ ds).take (T.front + roundsTo T.bs b + 1))) := by
      rw [← hsent, K14.add_own, hmain]
      rfl
    have htab : T.tableAt (.own (treesTo T.bs b + 0)) k y.2 =
        ownTbl T.chain J own₀ (T.front + roundsTo T.bs b) (fun _ _ _ => true) k m.st.input
          ((m.st.heard ++ ds).take (T.front + roundsTo T.bs b + 1)) := by
      unfold Thread.tableAt
      rw [Nat.add_zero, htable₀, hfixed₀, hhd, hin]
    unfold Thread.handAt
    rw [htree, htab]
    simp [Table.same_refl]
  | succ τ =>
    have hτ : τ + 1 < J.p.nums.stages.length := by omega
    have hmain := table_in_run J hR hk s t rest hst blk.name (T.φ.sees m.st.input) _ hrs T.chain k c hc
      ds [] m y hy' own₀ _ hheard hτ
      ((m.st.heard ++ ds).take (T.front + roundsTo T.bs b + seedRound J.p.nums.stages τ))
      (by rw [List.take_take, Nat.min_self])
    have hno : J.fresh.isNone = true := by simp [hfresh]
    rw [hno] at hmain
    simp only [if_true] at hmain
    have htree : (E.add y.1).tree (.own (treesTo T.bs b + (τ + 1))) =
        some (testTbl T.chain J own₀ (T.front + roundsTo T.bs b) (fun _ _ _ => true) τ k m.st.input
          ((m.st.heard ++ ds).take (T.front + roundsTo T.bs b + seedRound J.p.nums.stages τ))) := by
      rw [← hsent, K14.add_own, hmain]
      rfl
    have htab : T.tableAt (.own (treesTo T.bs b + (τ + 1))) k y.2 =
        testTbl T.chain J own₀ (T.front + roundsTo T.bs b) (fun _ _ _ => true) τ k m.st.input
          ((m.st.heard ++ ds).take (T.front + roundsTo T.bs b + seedRound J.p.nums.stages τ)) := by
      unfold Thread.tableAt
      rw [htable τ hτ, hfixed τ hτ, hhd, hin]
    unfold Thread.handAt
    rw [htree, htab]
    simp [Table.same_refl]

/-- **A play of a guarded half that returned began at a field that is some.** -/
theorem opened_of_play {S Cl W X : Type} {blk : Block S Cl} (J : TestJob W X)
    (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: t :: rest)
    (hpl : blk.place = J.p.place)
    (hrs : (blk.rounds.zip blk.oracles).length =
      firstLen J.p.nums.stages + restLen J.p.nums.stages)
    (v : Option Empty) (c : RowCoins (proverSideOfProximityTest J : Placed Empty W X).parts) (ds : List Fmt.Drawn)
    (m : Mid W X) (y : List Played × Mid W X)
    (hy : play (((proverSideOfProximityTest J : Placed Empty W X).steps blk v c).map Step.guarded) ds [] m = .ok y) :
    m.opened.isSome = true := by
  cases hm : m.opened with
  | some cs => rfl
  | none =>
    exfalso
    obtain ⟨hl, hmv⟩ := half_steps J s t rest hst blk.name v (blk.rounds.zip blk.oracles) hrs c
    have e : (proverSideOfProximityTest J : Placed Empty W X).steps blk v c =
        rowSteps blk.name J.p.place v [(firstPart J : Part Empty W X), restPart J] 0
          (blk.rounds.zip blk.oracles) c := by
      unfold Placed.steps
      rw [hpl]
      rfl
    rw [e] at hy
    have h2 : 2 ≤ firstLen J.p.nums.stages := by
      rw [hst]
      show 2 ≤ 2 + s.k
      omega
    cases hL : rowSteps blk.name J.p.place v [(firstPart J : Part Empty W X), restPart J] 0
        (blk.rounds.zip blk.oracles) c with
    | nil =>
      rw [hL] at hl
      simp only [List.length_nil] at hl
      omega
    | cons a ss =>
      have hmove := hmv 0 (by rw [hL]; simp)
      simp only [hL, List.getElem_cons_zero] at hmove
      have em : ({ m with opened := none } : Mid W X) = m := by
        cases m
        simp only at hm
        subst hm
        rfl
      have hno := play_guarded_none a _ hmove ss ds [] m y
      rw [em] at hno
      rw [hL] at hy
      exact hno hy

/-- **hT at a proximity test whose first fold sends its own table, behind the guard, to the sign.**
NOT IN FRONT OF A LAW OVER COINS: it stands behind Thr and Moved. -/
theorem trees_of_thr_ten {S Cl W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk S Cl Empty W X Pb) {b : ℕ}
    {blk : Block S Cl} (hblk : T.bs[b]? = some blk) (J : TestJob W X)
    (hfresh : J.fresh = none) (hR : RowsOfHeard J)
    (hk : ∀ a ∈ J.p.nums.stages, a.h ≤ a.k)
    (s t : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (hst : J.p.nums.stages = s :: t :: rest)
    (hpl : blk.place = J.p.place)
    (hhalf : (T.hs.find? fun g => g.place == blk.place) = some (proverSideOfProximityTest J).needsField)
    (hrs : (blk.rounds.zip blk.oracles).length =
      firstLen J.p.nums.stages + restLen J.p.nums.stages)
    (hcount : (blk.oracles.flatMap id).length = J.p.nums.stages.length)
    (own₀ : X)
    (htable₀ : T.table (.own (treesTo T.bs b)) =
      ownTbl T.chain J own₀ (T.front + roundsTo T.bs b) (fun _ _ _ => true))
    (htable : ∀ τ, τ + 1 < J.p.nums.stages.length → T.table (.own (treesTo T.bs b + (τ + 1))) =
      testTbl T.chain J own₀ (T.front + roundsTo T.bs b) (fun _ _ _ => true) τ)
    (hfixed₀ : T.fixed (.own (treesTo T.bs b)) = T.front + roundsTo T.bs b + 1)
    (hfixed : ∀ τ, τ + 1 < J.p.nums.stages.length → T.fixed (.own (treesTo T.bs b + (τ + 1))) =
      T.front + roundsTo T.bs b + seedRound J.p.nums.stages τ) :
    ∀ k st m E ds y cols, Thr T b k st m E → drawsFit blk.rounds ds = true →
      T.Moved blk k m E ds y cols → T.Trees (T.fresh b) k y.2 (E.add y.1) := by
  intro k st m E ds y cols hT hd hMv
  have hMv' := hMv
  unfold Thread.Moved at hMv'
  obtain ⟨⟨l, hl, hy⟩, -⟩ := hMv'
  obtain ⟨c', hc', rfl⟩ := steps_one_half hhalf hl
  have hc'' : lendRow Bk (Bk.rowsOf T.chain) (k.look T.chain) blk.place
      ((proverSideOfProximityTest J : Placed Empty W X).parts.map Part.needsField) 0 = .ok c' := hc'
  rw [lendRow_guarded] at hc''
  obtain ⟨c, -, rfl⟩ := map_ok hc''
  rw [placedSteps_guarded (proverSideOfProximityTest J) blk (T.φ.sees m.st.input) c] at hy
  exact trees_of_thr_own T hblk J hfresh hR hk s t rest hst hpl hhalf hrs hcount own₀ htable₀ htable
    hfixed₀ hfixed k st m E ds y cols hT (opened_of_play J s t rest hst hpl hrs _ c ds m y hy) hd hMv

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.trees_of_thr_own
#print axioms ProofFile.Honest.K12.opened_of_play
#print axioms ProofFile.Honest.K12.trees_of_thr_ten
