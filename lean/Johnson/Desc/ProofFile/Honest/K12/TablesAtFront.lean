-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/TablesAtFront.lean: "The
congruence": at a sending round of a proximity test, msgAt's tables at any front of one heard are
those at frontAt, with nothing assumed of rec₀ or trees₀.


  RowsOfHeard   of a front, a job's rows₀ reads the heard alone
  psAt_congr    THE LIKE CONGRUENCE FOR A MESSAGE's TEXT: testMsgTxt reads a job's functions through
                psAt at frontAt alone (ScriptLots.lean:231–235), so at two fronts of one heard
                these texts read one state.
  tables_at_frontAt     the congruence at the switches' sending rounds
  tables_at_own_round   at round 1, where the first fold sends its own table
  rowsOfHeard_many      a ManyJob whose members' rows read the heard alone has the premise

WHAT A YES IS. The first theorem is msgAt_table_is_psAt (ScriptLotsTie.lean) at two fronts, plus
psAt_congr: that theorem's right side has no rec₀ and no trees₀. So a yes is the kernel's stamp on a
reading. It is not a test that the road by the tests' tables has survived, and it could not well
fail. The tie of a text to a run stays as untried as it was. It is the word
asked of Lean, and no more.

A YES WOULD NOT SHOW: that any part says msgAt at a run · that the run's coins are handedRest's ·
anything at ok, or where testTbl falls to wordlessTable · a text for own 7 · the vals of any round,
or the groups of opened columns (trees₀ is premised by nothing because nothing here reads it) · that
rows₀'s rows are what the senders sent · widths: T.logLength = a pins the label alone, T.words
nothing here, so nothing on Sending.fits · that the premise outlives a filling with u? or omega? :=
some v · anything over coins: w and C.mem feed both the table and what is shown, so "reads no Seen"
is a word about a function's arguments, not about what a view tells.

Limits.
- RowsOfHeard IS NOT THE PREMISE "read nothing of
  the Front's Seen", on rows₀ and trees₀. This one is on rows₀ alone, and of rows₀ it asks more:
  nothing of own either, and equality of the whole PS. It says nothing of trees₀, because no table
  here reads it. It is meant for a TREE's text: a premise that narrows the jobs and ties nothing to
  a coin, to be named wherever a law stands behind a tie. Beside a tie of a message's or a pad's
  text that other premise is the one to name, or psAt_congr's own two: RowsOfHeard J, and that the
  two fronts have one heard. No law over coins, and nothing on hiding, follows from this file.
  At O the parts stand behind the guard: the lift is FieldGuardLift.lean's (`playsOn_guarded`,
  `saysYes_guarded`), under hopen: that the field is some wherever A holds.
- tables_at_own_round SPEAKS OF .tables ALONE, AT ONE C. It gives no text for own 7: testTbl reads
  restCoins and seedRound alone, and round 1 is the first part's, at other TestCoins (Parts.lean:200–
  206). At that round the message's vals read rec₀ (aFold at rowOf t, t from recB): so the Sending
  that holds the table does read the front; the table does not.
- frontAt's field is none, and proverSideOfTestOnOmega stands behind the guard (FieldGuard.lean), which errs there:
  the front at which a text is cut is one at which the key's part sends nothing. The equation is
  untouched; it is no word that the part says msgAt at that front.
- D is one letter on both sides. In a run it is the list lately; msgAt_causal closes that at one
  front. That fr.heard is h.take n₀ at a run is not here.
- Nothing here says that a job has the premise: E2E/CongruenceAtKey.lean.
- All that binds whoever builds on ScriptLots.lean (its head) binds here.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.ScriptLotsTie
import Johnson.Desc.ProofFile.Honest.K12.RunMany

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {W X : Type}

/-- Of a front, rows₀ reads the heard alone: neither what is handed on, nor the rounds shown, nor the
columns handed. See the head's first limit. -/
def RowsOfHeard (J : TestJob W X) : Prop :=
  ∀ (w : W) (fr fr' : Front X) (mem : ℕ → Stretch),
    fr.heard = fr'.heard → J.rows₀ w fr mem = J.rows₀ w fr' mem

/-- **At two fronts of one heard the prover's state is one, at every stage**, under RowsOfHeard: the
like congruence for a message's text (the file's head). -/
theorem psAt_congr (J : TestJob W X) (hR : RowsOfHeard J) (w : W) {fr fr' : Front X}
    (he : fr.heard = fr'.heard) (C : TestCoins) (D : ℕ → Fmt.Drawn) (j : ℕ) :
    psAt J w fr C D j = psAt J w fr' C D j := by
  induction j with
  | zero =>
    have e := hR w fr fr' C.mem he
    simp only [psAt, TestJob.first, e]
  | succ j ih =>
    simp only [psAt, ih]

/-- **THE CONGRUENCE.** At the sending round of tree τ, at ANY front whose heard is h.take n₀, the
part's message holds one table, of depth a, and it is the table of the message at frontAt. own, the
rounds shown and the columns handed are free in fr, and nothing is assumed of rec₀ or trees₀. -/
theorem tables_at_frontAt (J : TestJob W X) (hR : RowsOfHeard J)
    (hk : ∀ a ∈ J.p.nums.stages, a.h ≤ a.k)
    (w : W) (own₀ : X) (n₀ : ℕ) (h : List Fmt.Drawn)
    (fr : Front X) (hfr : fr.heard = h.take n₀)
    (C : TestCoins) (D : ℕ → Fmt.Drawn)
    {τ : ℕ} (hτ : τ + 1 < J.p.nums.stages.length)
    {a : ℕ} (ha : depthAt J (seedRound J.p.nums.stages τ) = some a) :
    ∃ T : ProofFile.Honest.Table, T.logLength = a ∧
      (msgAt J w fr C D (seedRound J.p.nums.stages τ)).tables = [T] ∧
      (msgAt J w (frontAt own₀ n₀ h) C D (seedRound J.p.nums.stages τ)).tables = [T] := by
  have e : psAt J w fr C D (τ + 1) = psAt J w (frontAt own₀ n₀ h) C D (τ + 1) :=
    psAt_congr J hR w hfr C D (τ + 1)
  have h1 := msgAt_table_is_psAt J hk w fr C D hτ ha
  have h2 := msgAt_table_is_psAt J hk w (frontAt own₀ n₀ h) C D hτ ha
  rw [← e] at h2
  refine ⟨_, ?_, h1, h2⟩
  rfl

/-- A list that is not empty: what "set 0" lays stands at 0. -/
theorem getElem?_set_zero {α : Type} (l : List α) (hl : l ≠ []) (x : α) :
    (l.set 0 x)[0]? = some x := by
  cases l with
  | nil => exact absurd rfl hl
  | cons a t => rfl

/-- **At a test of two stages or more, what the first fold's own table lies on** at round 1. -/
theorem col_own_round (J : TestJob W X) (hf : J.fresh = none) {s n : Fmt.M1.Stage}
    {rest : List Fmt.M1.Stage} (hst : J.p.nums.stages = s :: n :: rest) (w : W) (fr : Front X)
    (C : TestCoins) (D : ℕ → Fmt.Drawn) :
    (testAll J w fr C D).tr.getD 1 (fun _ => []) = freshCol (sgOf s) (J.first w fr C) := by
  have hfi : J.fresh.isNone = true := by simp [hf]
  have hB : ∀ Bt : List (ℕ → List UInt64), Bt[0]? = some (freshCol (sgOf s) (J.first w fr C)) →
      ((fun _ => []) :: Bt).getD 1 (fun _ => []) = freshCol (sgOf s) (J.first w fr C) := by
    intro Bt hBt
    rw [List.getD_eq_getElem?_getD, List.getElem?_cons_succ, hBt]
    rfl
  unfold testAll
  rw [hst]
  refine hB _ ?_
  rw [if_pos hfi]
  refine getElem?_set_zero _ ?_ _
  simp only [stagesAll]
  simp

/-- **THE OTHER SENDING ROUND.** Where the fold sends its own fresh table, the message of round 1
holds one table, of depth a, at every front: no premise on rows₀, and none on heard. Of .tables
alone: see the head. -/
theorem tables_at_own_round (J : TestJob W X) (hf : J.fresh = none)
    (w : W) (fr fr' : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn)
    {a : ℕ} (ha : depthAt J 1 = some a) :
    ∃ T : ProofFile.Honest.Table, T.logLength = a ∧
      (msgAt J w fr C D 1).tables = [T] ∧ (msgAt J w fr' C D 1).tables = [T] := by
  obtain ⟨s, n, rest, hst⟩ : ∃ s n rest, J.p.nums.stages = s :: n :: rest := by
    cases e : J.p.nums.stages with
    | nil =>
      have h0 : depthAt J 1 = none := by
        unfold depthAt
        rw [e]
        try rfl
      rw [h0] at ha
      exact absurd ha (by simp)
    | cons s t =>
      cases t with
      | nil =>
        have h0 : depthAt J 1 = none := by
          unfold depthAt
          rw [e]
          try rfl
        rw [h0] at ha
        exact absurd ha (by simp)
      | cons n rest => exact ⟨s, n, rest, rfl⟩
  have hone : ∀ fr₀ : Front X, freshCol (sgOf s) (J.first w fr₀ C) =
      freshCol (sgOf s) (J.first w fr C) := by
    intro fr₀
    funext x
    simp only [freshCol, TestJob.first]
  obtain ⟨Y, hY⟩ : ∃ Y, ∀ fr₀ : Front X, (testAll J w fr₀ C D).tr.getD 1 (fun _ => []) = Y :=
    ⟨_, fun fr₀ => (col_own_round J hf hst w fr₀ C D).trans (hone fr₀)⟩
  have h1 : ∀ fr₀ : Front X, (msgAt J w fr₀ C D 1).tables =
      [⟨a, (Y 0).length, fun x k => toF ((Y x).getD k.val 0)⟩] := by
    intro fr₀
    unfold msgAt
    simp only [ha, Option.toList_some, List.map_cons, List.map_nil]
    rw [hY fr₀]
  refine ⟨_, ?_, h1 fr, h1 fr'⟩
  rfl

/-- **A ManyJob whose members' rows read the heard alone has the premise.** -/
theorem rowsOfHeard_many (A : Light.ManyJob W X)
    (h : ∀ m ∈ A.mems, ∀ (w : W) (fr fr' : Front X) (c : Stretch),
      fr.heard = fr'.heard → m.rows w fr c = m.rows w fr' c) :
    RowsOfHeard A.toRun.toTest := by
  intro w fr fr' mem he
  have e : (A.mems.zipIdx.map fun m => (m.1.shape, m.1.rows w fr (mem m.2))) =
      A.mems.zipIdx.map fun m => (m.1.shape, m.1.rows w fr' (mem m.2)) := by
    refine List.map_congr_left fun m hm => ?_
    rw [h m.1 (List.fst_mem_of_mem_zipIdx hm) w fr fr' _ he]
  exact congrArg (fun l => Light.readPS A.toRun.s₀ (Light.layFirst A.s₀ l)) e

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.RowsOfHeard
#print axioms ProofFile.Honest.K12.psAt_congr
#print axioms ProofFile.Honest.K12.tables_at_frontAt
#print axioms ProofFile.Honest.K12.getElem?_set_zero
#print axioms ProofFile.Honest.K12.col_own_round
#print axioms ProofFile.Honest.K12.tables_at_own_round
#print axioms ProofFile.Honest.K12.rowsOfHeard_many
