-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/DepthsOfText.lean: For trial
(e): a table's logLength, at the thread's two kinds of
text, is public: it hangs on no coin, no input and no challenge, where the book lends.

  lends_of_B, handed_of_B   where laysB says yes the frame lends at every k: the first half of
                 lays_of_B (StepsReturn.lean), with no block and no seat
  testTbl_depth  a test's text, at ok the constant yes: the next stage's depth at all k, w, h
  cut_of_due     a cut that the book's count covers returns at every k
  sendTable_depth   a sending's text: the shape's logN, where the cut returns

Limits.
- ok is the constant yes. Where ok says no, testTbl falls to wordlessTable, logLength 0.
- All that binds whoever builds on ScriptLots.lean (its head) binds here. A law on a depth alone: no
  tie of a text to a run is added here beyond TableOfRun.lean's handedRest_of_row.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.TableOfRun
import Johnson.Desc.ProofFile.Honest.K12.StepsReturn
import Johnson.Desc.ProofFile.Honest.K1.ScriptAtLaw
import Johnson.Desc.ProofFile.Honest.K14.SendingsPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open VerifiableInference.Desc VerifiableInference.Desc.K12
open AtPublicFiles.KeyBook (hasFor Stated Within lendRow_ok look_due seen)

variable {V W X : Type}

/-- **Where laysB says yes the frame lends at every k.** -/
theorem lends_of_B (B : ProverCoinCounts) (ch : ℕ) (hch : ch = 0 ∨ ch = 1) (J : TestJob W X)
    (hB : laysB B ch J = true) (k : Coins B) :
    ∃ c, lendRow B (B.rowsOf ch) (k.look ch) J.p.place
      [(firstPart J : Part V W X), restPart J] 0 = .ok c := by
  unfold laysB at hB
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.not_eq_true',
    List.all_eq_true] at hB
  obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, a6⟩, a7⟩, a8⟩ := hB
  have hseen : seen B ch = B.rowsOf ch := by
    rcases hch with rfl | rfl <;> rfl
  exact lendRow_ok B (B.rowsOf ch) (k.look ch) J.p.place
    (fun j => by
      rw [look_due, hseen]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (fun e he hp => by
      have q := a8 e he
      rw [hp] at q
      simp only [beq_self_eq_true, Bool.not_true, Bool.false_or, inB, Bool.and_eq_true,
        decide_eq_true_eq] at q
      unfold Within
      rw [look_due, hseen]
      exact q)
    [(firstPart J : Part V W X), restPart J] 0 (fun i p hp => by
      match i, hp with
      | 0, hp =>
        obtain rfl := Option.some.inj hp
        exact (first_states J).trans a6
      | 1, hp =>
        obtain rfl := Option.some.inj hp
        exact a7)

/-- Where laysB says yes handedRest answers at every k. -/
theorem handed_of_B (B : ProverCoinCounts) (ch : ℕ) (hch : ch = 0 ∨ ch = 1) (J : TestJob W X)
    (hB : laysB B ch J = true) (k : Coins B) : ∃ c, handedRest ch J k = some c := by
  obtain ⟨c, hc⟩ := lends_of_B (V := Empty) B ch hch J hB k
  exact ⟨_, handedRest_of_row ch J k c hc⟩

/-- **A test's text has the next stage's depth at all k, w, h**, where laysB says yes, at ok the
constant yes. -/
theorem testTbl_depth {Bk : ProverCoinCounts} (J : TestJob W X) (hk : ∀ a ∈ J.p.nums.stages, a.h ≤ a.k) (ch : ℕ)
    (hch : ch = 0 ∨ ch = 1) (hB : laysB Bk ch J = true) (own₀ : X) (n₀ : ℕ) {τ : ℕ}
    (hτ : τ + 1 < J.p.nums.stages.length) (k : Coins Bk) (w : W) (h : List Fmt.Drawn) :
    (testTbl ch J own₀ n₀ (fun _ _ _ => true) τ k w h).2.logLength =
      (J.p.nums.stages.getD (τ + 1) default).C.a := by
  obtain ⟨c, hc⟩ := handed_of_B Bk ch hch J hB k
  unfold testTbl
  simp only [hc, ↓reduceIte, msgAt_table_is_psAt J hk w _ _ _ hτ (depthAt_seed J hτ),
    List.head?_cons, Option.getD_some]

/-- A cut that the book's count covers returns, at every k. -/
theorem cut_of_due {Bk : ProverCoinCounts} (k : Coins Bk) (ch : ℕ) (hc : ch ≤ 1) (a : Addr) (n : Due)
    (h : n.f ≤ (dueAt (Bk.rowsOf ch) a).f ∧ n.e ≤ (dueAt (Bk.rowsOf ch) a).e) :
    ((k.look ch a).2.cut ⟨0, 0⟩ n).isSome = true := by
  rw [K1.cut_isSome, K1.look_due k ch hc a]
  exact decide_eq_true h

/-- **A sending's text has the shape's depth**, where the cut returns and the tree is there. -/
theorem sendTable_depth {Bk : ProverCoinCounts} (J : K14.SendJob) (wit : W → K14.Ask) (pl : Place) (ch i : ℕ)
    (k : Coins Bk) (w : W) (h : List Fmt.Drawn)
    (hcut : ((k.look ch ⟨pl, 0⟩).2.cut ⟨0, 0⟩ (K14.sendingPart J).takes).isSome = true)
    (hi : i < ((VerifiableInference.Desc.Own.treesMade J.Q.codes J.Q.sent).getD {}).shapes.toList.length) :
    (K14.sendTable J wit pl ch i k w h).2.logLength =
      ((((VerifiableInference.Desc.Own.treesMade J.Q.codes J.Q.sent).getD {}).shapes.toList.map
        (·.logN)).getD i 0) := by
  unfold K14.sendTable
  cases hc : (k.look ch ⟨pl, 0⟩).2.cut ⟨0, 0⟩ (K14.sendingPart J).takes with
  | none =>
    rw [hc] at hcut
    cases hcut
  | some own =>
    show ((K14.sendTablesAt J own (wit w) h).getD i _).logLength = _
    unfold K14.sendTablesAt K14.sentTables
    rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map, List.getElem_zipIdx,
      List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_map]

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.lends_of_B
#print axioms ProofFile.Honest.K12.handed_of_B
#print axioms ProofFile.Honest.K12.testTbl_depth
#print axioms ProofFile.Honest.K12.cut_of_due
#print axioms ProofFile.Honest.K12.sendTable_depth
