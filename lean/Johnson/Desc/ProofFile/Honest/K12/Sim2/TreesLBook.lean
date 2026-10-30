-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
-- K12's simulator: the test on the book at the maker's book.
/-
Johnson/Desc/ProofFile/Honest/K12/Sim2/TreesLBook.lean: the public test bookTiesAtFinish
(Sim2/TreesL.lean) at the written list of the book's entries (rawAheadW), by Lean's kernel; so at
whatever book the maker returns in the goals' scope, and at the book of every filling under the
head. The road of runs_L_at_laid (AtFullSide/K12/RunsAtLaidL.lean) and of noneSpent_at_maker
(Sim2/BookAtWritten.lean).

  book_entries_only   the test reads of a book its entries alone
  finishWritten_place   the written finish stands at the first chain's piece 1
  carriedRaw, runs_written_1 to 4, numbers_written   the runs and the numbers, by Lean's kernel
  ties_of_runs, ties_written   the test at the written list
  ties_at_laid_finish   at whatever book the maker returns
  ties_at_maker    at the book of whatever filling, under the head

Limits. The full size alone. The library's written sendings; the merges that the maker reads off the
first chain; two of rawAheadW's ten pieces are their makers' terms. No property of the protocol is
claimed.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim2.TreesLAt
import AtFullSide.K12.RunsAtLaidL
import Johnson.Desc.ProofFile.Honest.K14.AtPureBookAtHead
import Johnson.Desc.ProofFile.Honest.K14.SharedSendsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Sim2
open VerifiableInference.Desc (Block Chain)
open ProofFile.Honest ProofFile.Honest.K12 ProofFile.Honest.K12.AtProof
open Johnson.G (proofSendsFull)
open AtFullSide.K14 (rawAheadW rawSegW)

/-- The test reads of a book its entries alone. -/
theorem book_entries_only (B : ProverCoinCounts) (a s : Addr) (p : K2.SwitchPlace) :
    bookTiesAtFinish B a s p = bookTiesAtFinish ⟨[], [], [], B.ahead, []⟩ a s p := rfl

set_option maxRecDepth 1000000 in
/-- The written finish stands at the first chain's piece 1. -/
theorem finishWritten_place : (finishWritten.map (·.place)) = some ⟨1, none, 1, .K2⟩ := by
  decide +kernel

/-- What a part carries at a list of entries. -/
def carriedRaw (l : List Ahead) (a : Addr) : List Ahead :=
  (l.filter fun e => e.spender == a).filter (!·.once)

/-- The test's second part carries 186 entries at the written list. -/
theorem runs_written_1 : (carriedRaw rawAheadW ⟨⟨1, none, 2, .K12⟩, 1⟩).length = 186 :=
  AtFullSide.K12.carried_L_written.2.1

theorem carriedRaw_append (l₁ l₂ : List Ahead) (a : Addr) :
    carriedRaw (l₁ ++ l₂) a = carriedRaw l₁ a ++ carriedRaw l₂ a := by
  unfold carriedRaw
  rw [List.filter_append, List.filter_append]

/-- Where the other pieces of the written list carry nothing to a part, its carried entries are the
segments'. So Lean's kernel reads them piece by piece: at the whole list decide +kernel did not
return here, for a reason that was not found. -/
theorem carried_in_seg (x : Addr)
    (hw : (carriedRaw (AtFullSide.K14.rawWantsW.map (·.entry)) x).isEmpty = true)
    (hs : (carriedRaw AtFullSide.K14.rawShortW x).isEmpty = true) :
    carriedRaw rawAheadW x = carriedRaw rawSegW x := by
  unfold AtFullSide.K14.rawShortW at hs
  unfold rawAheadW
  simp only [carriedRaw_append, List.isEmpty_iff, List.append_eq_nil_iff] at hs hw ⊢
  simp_all

set_option maxRecDepth 1000000 in
theorem off_wants_finish :
    (carriedRaw (AtFullSide.K14.rawWantsW.map (·.entry)) ⟨⟨1, none, 1, .K2⟩, 0⟩).isEmpty = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem off_wants_test :
    (carriedRaw (AtFullSide.K14.rawWantsW.map (·.entry)) ⟨⟨1, none, 2, .K12⟩, 1⟩).isEmpty = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem off_short_finish :
    (carriedRaw AtFullSide.K14.rawShortW ⟨⟨1, none, 1, .K2⟩, 0⟩).isEmpty = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
theorem off_short_test :
    (carriedRaw AtFullSide.K14.rawShortW ⟨⟨1, none, 2, .K12⟩, 1⟩).isEmpty = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The finish carries 184, at the segments' entries. -/
theorem seg_finish_length : (carriedRaw rawSegW ⟨⟨1, none, 1, .K2⟩, 0⟩).length = 184 := by
  unfold carriedRaw rawSegW ProofFile.Honest.segmentCarries ProofFile.Honest.linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

set_option maxRecDepth 1000000 in
/-- The first 184 that the test's second part carries are the finish's, at the segments' entries. -/
theorem seg_runs : ((carriedRaw rawSegW ⟨⟨1, none, 2, .K12⟩, 1⟩).take 184).map
      (fun e => (e.owner, e.start, e.count)) =
    (carriedRaw rawSegW ⟨⟨1, none, 1, .K2⟩, 0⟩).map fun e => (e.owner, e.start, e.count) := by
  unfold carriedRaw rawSegW ProofFile.Honest.segmentCarries ProofFile.Honest.linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- The finish carries 184. -/
theorem runs_written_2 : (carriedRaw rawAheadW ⟨⟨1, none, 1, .K2⟩, 0⟩).length = 184 := by
  rw [carried_in_seg _ off_wants_finish off_short_finish]
  exact seg_finish_length

/-- The first 184 that the test's second part carries are the finish's. -/
theorem runs_written_3 : ((carriedRaw rawAheadW ⟨⟨1, none, 2, .K12⟩, 1⟩).take 184).map
      (fun e => (e.owner, e.start, e.count)) =
    (carriedRaw rawAheadW ⟨⟨1, none, 1, .K2⟩, 0⟩).map fun e => (e.owner, e.start, e.count) := by
  rw [carried_in_seg _ off_wants_finish off_short_finish,
    carried_in_seg _ off_wants_test off_short_test]
  exact seg_runs

/-- The last two that it carries are the finish's coins. -/
theorem runs_written_4 : ((carriedRaw rawAheadW ⟨⟨1, none, 2, .K12⟩, 1⟩).drop 184).map entryRun =
    [(⟨⟨1, none, 1, .K2⟩, 0⟩, ⟨0, 0⟩, ⟨0, 439⟩), (⟨⟨1, none, 1, .K2⟩, 0⟩, ⟨0, 439⟩, ⟨0, 222⟩)] :=
  AtFullSide.K12.carried_L_written.2.2.2

set_option maxRecDepth 1000000 in
/-- The numbers of the written finish. -/
theorem numbers_written : (finishWritten.map fun p => (p.front.length,
    K2.messageDue p.sizes.codes (shapeL p) none,
    K2.dueBefore p.sizes.codes (sentL p) (freshWordOf p) 1,
    K2.messageDue p.sizes.codes (freshShapeL p) (some p.foldVars))) =
    some (184, ⟨0, 439⟩, ⟨0, 439⟩, ⟨0, 222⟩) := by
  decide +kernel

/-- **The test, of runs and numbers.** -/
theorem ties_of_runs (Bk : ProverCoinCounts) (a s : Addr) (p : K2.SwitchPlace)
    (hA : Light.carriedOf Bk a = carriedRaw Bk.ahead a)
    (hS : Light.carriedOf Bk s = carriedRaw Bk.ahead s)
    (l₁ : (carriedRaw Bk.ahead a).length = 186) (l₂ : (carriedRaw Bk.ahead s).length = 184)
    (r₁ : ((carriedRaw Bk.ahead a).take 184).map entryRun = (carriedRaw Bk.ahead s).map entryRun)
    (r₂ : ((carriedRaw Bk.ahead a).drop 184).map entryRun = [(s, ⟨0, 0⟩, ⟨0, 439⟩), (s, ⟨0, 439⟩, ⟨0, 222⟩)])
    (n₀ : p.front.length = 184) (n₁ : K2.messageDue p.sizes.codes (shapeL p) none = ⟨0, 439⟩)
    (n₂ : K2.dueBefore p.sizes.codes (sentL p) (freshWordOf p) 1 = ⟨0, 439⟩)
    (n₃ : K2.messageDue p.sizes.codes (freshShapeL p) (some p.foldVars) = ⟨0, 222⟩) :
    bookTiesAtFinish Bk a s p = true := by
  obtain ⟨e₀, e₁, hd⟩ : ∃ e₀ e₁, (carriedRaw Bk.ahead a).drop 184 = [e₀, e₁] := by
    cases hl : (carriedRaw Bk.ahead a).drop 184 with
    | nil =>
      rw [hl] at r₂
      exact absurd (congrArg List.length r₂) (by simp)
    | cons x l =>
      cases l with
      | nil =>
        rw [hl] at r₂
        exact absurd (congrArg List.length r₂) (by simp)
      | cons y l =>
        cases l with
        | nil => exact ⟨x, y, rfl⟩
        | cons z l =>
          rw [hl] at r₂
          exact absurd (congrArg List.length r₂) (by simp)
  rw [hd] at r₂
  have g₀ : (carriedRaw Bk.ahead a)[184]? = some e₀ := by
    have := congrArg (·[0]?) hd
    simpa using this
  have g₁ : (carriedRaw Bk.ahead a)[184 + 1]? = some e₁ := by
    have := congrArg (·[1]?) hd
    simpa using this
  have f₀ : entryRun e₀ = (s, ⟨0, 0⟩, ⟨0, 439⟩) := (List.cons.inj r₂).1
  have f₁ : entryRun e₁ = (s, ⟨0, 439⟩, ⟨0, 222⟩) := (List.cons.inj (List.cons.inj r₂).2).1
  unfold entryRun at f₀ f₁
  obtain ⟨a₁, a₂⟩ := Prod.mk.inj f₀
  obtain ⟨a₂, a₃⟩ := Prod.mk.inj a₂
  obtain ⟨b₁, b₂⟩ := Prod.mk.inj f₁
  obtain ⟨b₂, b₃⟩ := Prod.mk.inj b₂
  have hs' : (carriedRaw Bk.ahead s).take 184 = carriedRaw Bk.ahead s :=
    List.take_of_length_le (by omega)
  unfold bookTiesAtFinish
  rw [hA, hS, n₀, g₀, g₁, hs', r₁, n₁, n₂, n₃, l₁, l₂]
  simp [a₁, a₂, a₃, b₁, b₂, b₃]

/-- **The test at the written list of the book's entries.** -/
theorem ties_written {pl : K2.SwitchPlace} (hf : finishWritten = some pl) :
    bookTiesAtFinish ⟨[], [], [], rawAheadW, []⟩ ⟨⟨1, none, 2, .K12⟩, 1⟩ ⟨⟨1, none, 1, .K2⟩, 0⟩ pl =
      true := by
  have l₁ := runs_written_1
  have l₂ := runs_written_2
  have r₁ := runs_written_3
  have r₂ := runs_written_4
  have e := numbers_written
  rw [hf] at e
  have e' := Option.some.inj e
  obtain ⟨n₀, e'⟩ := Prod.mk.inj e'
  obtain ⟨n₁, e'⟩ := Prod.mk.inj e'
  obtain ⟨n₂, n₃⟩ := Prod.mk.inj e'
  exact ties_of_runs _ _ _ pl rfl rfl l₁ l₂ r₁ r₂ n₀ n₁ n₂ n₃

/-- **At whatever book the maker returns, in the goals' scope.** -/
theorem ties_at_laid_finish {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    (scope : VerifierAndGoals.InScope Z = true) (L : P5J.LaidAt o Z.pol Z.lay Z.KL D r Zp Np cF) {Bk : ProverCoinCounts}
    (hB : bookWhole (P5J.F0T o Zp Np cF) proofSendsFull.1 proofSendsFull.2.1 proofSendsFull.2.2
      (mergesByName (P5J.F0T o Zp Np cF).first.blocksInOrder) = .ok Bk)
    {pl : K2.SwitchPlace} (hf : finishWritten = some pl) :
    bookTiesAtFinish Bk ⟨⟨1, none, 2, .K12⟩, 1⟩ ⟨⟨1, none, 1, .K2⟩, 0⟩ pl = true := by
  obtain ⟨B₀, h₀, hA⟩ := AtFullSide.K14.bookWhole_returns_written_ahead
  obtain rfl : B₀ = Bk :=
    Except.ok.inj ((ProofFile.Honest.K14.bookWhole_same_at_laid h₀ scope L).symm.trans hB)
  rw [book_entries_only, hA]
  exact ties_written hf

/-- **At the book of whatever filling, under the head.** -/
theorem ties_at_maker {W₀ Rc Tr X₀ X : Type} {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD}
    {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl}
    {x₀ : VerifiableInference.Desc.First.Look.Place}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {P : OnlineProverParts W₀ Rc Tr X₀ X}
    {A : OnlineProverWithDescription W₀ Rc Tr X₀ X} (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    {pl : K2.SwitchPlace} (hf : finishWritten = some pl) :
    bookTiesAtFinish A.B ⟨⟨1, none, 2, .K12⟩, 1⟩ ⟨⟨1, none, 1, .K2⟩, 0⟩ pl = true := by
  have hb := ProofFile.Honest.K14.atPure_book_at_head h hA
  have hs := ProofFile.Honest.K14.made_sends_at_files h.scope h.laid
  rw [hs] at hb
  exact ties_at_laid_finish h.scope h.laid hb hf

end ProofFile.Honest.K12.Sim2

#print axioms ProofFile.Honest.K12.Sim2.finishWritten_place
#print axioms ProofFile.Honest.K12.Sim2.runs_written_1
#print axioms ProofFile.Honest.K12.Sim2.runs_written_2
#print axioms ProofFile.Honest.K12.Sim2.runs_written_3
#print axioms ProofFile.Honest.K12.Sim2.runs_written_4
#print axioms ProofFile.Honest.K12.Sim2.numbers_written
#print axioms ProofFile.Honest.K12.Sim2.ties_of_runs
#print axioms ProofFile.Honest.K12.Sim2.ties_written
#print axioms ProofFile.Honest.K12.Sim2.ties_at_laid_finish
#print axioms ProofFile.Honest.K12.Sim2.ties_at_maker
