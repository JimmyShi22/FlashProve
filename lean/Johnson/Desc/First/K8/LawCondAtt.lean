-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/K8/LawCondAtt.lean: THE SMALLNESS TEST AT AN ATTENTION LINK: THE CONDITIONS THAT
ITS ROW OF THE TABLE OF JOINTS ASKS OF ITS RECORD IN FRONT OF THE DRAW, OVER THE FRAME'S FOLD.

Johnson/Desc/First/K8/LawCondText.lean pays `SameLay (recOf tl0 s) tl0` and `Extra s` right behind
the step that closes the list of tables at a layers' link and at the head's, where that step lays
its place's own parameter. AT AN ATTENTION LINK the step (`readsAtO`,
Johnson/Desc/First/Att/ReadsO.lean) closes THE CARRIED RECORD. So the seven fields that the two
conditions read must come through the blocks in front:
  (The two readings, and each as a test with code, stand in Johnson/Desc/First/K8/Cond.lean.)
  `Ready.lay7 s`: of the smallness test's record in s: the symbol arrays' numbers, the arrays'
    index, the digits' two numbers of columns; the number of matrices, the shapes, the matrices.
  `Ready.onThird s`: whether every table of its list lies on the third vector of reads.
  `cond_of_readings`: **the two readings are enough**: if `lay7 s` is tlP's seven and `onThird s` is
    yes, then `SameLay tlP tl0` and `Port.Fits tlP` give both conditions at s.
  `attO_lay7`, `attO_onThird`: every block `readsAtO W l g` LEAVES the first and LAYS yes at the
    second: by `K5Law.reads_next_o` and `K5Law.tabs_tree`
    (Johnson/Desc/First/Att/Claims/ReadsNextO.lean, TablesTree.lean).
  `cond_of_fold_att`: **the assembly**: pre, own and post: blocks that leave both readings (a block
    that leaves `S.tl?` does: `leaves_of_tl`); c: any block under `readsAtO W l g` joined
    behind own: wherever the fold over pre, c, post goes on from a record whose smallness test's
    record is tlP, both conditions hold behind it.
Statements and proofs.
Limits. That a block leaves the two readings is shown of no block here but the closing step.
`SameLay tlP tl0` and `Port.Fits tlP` are facts on public values: shown at no value. That the link's
frame lays the plan's record is the frame's. Of completeness's kind: no error term; nothing on
soundness.

-/
import Johnson.Desc.First.K8.LawReadyAtt
import Johnson.Desc.First.K8.LawCondText
import Johnson.Desc.First.Att.Claims.TablesTree
import Johnson.Desc.First.K8.Cond

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Ready

open OnBytes OnBytes.Model

/-- **The two readings are enough.** -/
theorem cond_of_readings (tlP tl0 : HTailF2) (s : S) (h7 : lay7 s = some (seven tlP))
    (h3 : onThird s = some true) (hl : SameLay tlP tl0)
    (hF : OnBytes.Tie.Pv.Tail.Port.Fits tlP) : SameLay (recOf tl0 s) tl0 ∧ Extra s := by
  unfold lay7 at h7
  unfold onThird at h3
  cases ht : s.tl? with
  | none => rw [ht] at h7; simp at h7
  | some tl =>
    rw [ht] at h7 h3
    simp only [Option.map_some, Option.some.injEq, seven, Prod.mk.injEq] at h7 h3
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h7
    refine ⟨?_, fun tl' e => ?_⟩
    · unfold recOf
      rw [ht]
      exact ⟨a1.trans hl.gt, a2.trans hl.ix, a3.trans hl.mz, a4.trans hl.off⟩
    · obtain rfl : tl = tl' := Option.some.inj (ht.symm.trans e)
      refine ⟨hF.of_same a5 a6 a7, fun Fn hFn => ?_⟩
      have := List.all_eq_true.1 h3 Fn hFn
      simpa using this

/-- What the second test's yes says. -/
theorem onThirdB_iff {s : S} :
    onThirdB s = true ↔ onThird s = some true ∧ closedNow s = some true := by
  simp [onThirdB]

/-- What the first test's yes says. -/
theorem lay7_of_test {tlP : HTailF2} {s : S} (h : lay7B tlP s = true) :
    lay7 s = some (seven tlP) := by
  unfold lay7B at h
  unfold lay7
  cases ht : s.tl? with
  | none => simp [ht] at h
  | some tl =>
    simp only [ht, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩ := h
    simp only [Option.map_some, seven, a1, a2, a3, a4, a5, a6, a7]

/-- **The two tests with code are enough.** -/
theorem cond_of_tests (tlP tl0 : HTailF2) (s : S) (h7 : lay7B tlP s = true)
    (h3 : onThirdB s = true) (hl : SameLay tlP tl0)
    (hF : OnBytes.Tie.Pv.Tail.Port.Fits tlP) : SameLay (recOf tl0 s) tl0 ∧ Extra s :=
  cond_of_readings tlP tl0 s (lay7_of_test h7) (onThirdB_iff.1 h3).1 hl hF

/-- A block that leaves the smallness test's record leaves both readings. -/
theorem leaves_of_tl {Cl : Type} (b : Block S Cl) (h : b.Leaves S.tl?) :
    b.Leaves lay7 ∧ b.Leaves onThird := by
  refine ⟨fun s rs gs s' hd => ?_, fun s rs gs s' hd => ?_⟩
  · unfold lay7
    rw [h s rs gs s' hd]
  · unfold onThird
    rw [h s rs gs s' hd]

/-- A yes of the step at the state, with the list's law. -/
theorem attO_yes_tree (A : Attention.Plan) (s s' : S) (h : Att.readsAtSO A s = .ok s') :
    ∃ tl funs, s.tl? = some tl ∧ s'.tl? = some { tl with funClosed := true, funs := funs } ∧
      ∀ Fn ∈ funs.toList, Fn.tree = 2 := by
  obtain ⟨a, _, _, _, t, c, ha, _, _, _, ht, hc, rfl⟩ := K5Law.reads_next_o A s s' h
  refine ⟨a.tl, (Att.tabsBack t).funs, ?_, ?_, K5Law.tabs_tree ht⟩
  · simp [S.tl?, ha]
  · have e := closeStep_tl hc
    simp only [S.tl?]
    rw [e]

/-- Every block `readsAtO W l g` leaves the seven fields. -/
theorem attO_lay7 {Cl : Type} (W : Verify.Public) (l g : Nat) (z : Block S Cl)
    (hz : Att.readsAtO (Cl := Cl) W l g = some z) : z.Leaves lay7 := by
  unfold Att.readsAtO at hz
  cases hA : W.A[g]? with
  | none => simp [hA] at hz
  | some A =>
    simp only [hA, Option.map_some, Option.some.injEq] at hz
    subst hz
    intro s rs gs s' hd
    obtain ⟨tl, funs, h1, h2, _⟩ := attO_yes_tree A s s' hd
    unfold lay7
    rw [h1, h2]
    rfl

/-- And behind its yes every table lies on the third vector of reads. -/
theorem attO_onThird {Cl : Type} (W : Verify.Public) (l g : Nat) (z : Block S Cl)
    (hz : Att.readsAtO (Cl := Cl) W l g = some z) : z.Lays onThird (fun _ => some true) := by
  unfold Att.readsAtO at hz
  cases hA : W.A[g]? with
  | none => simp [hA] at hz
  | some A =>
    simp only [hA, Option.map_some, Option.some.injEq] at hz
    subst hz
    intro s rs gs s' hd
    obtain ⟨tl, funs, _, h2, h3⟩ := attO_yes_tree A s s' hd
    unfold onThird
    rw [h2]
    simp only [Option.map_some, Option.some.injEq, List.all_eq_true, beq_iff_eq]
    exact h3

/-- **The assembly over the frame's fold.** -/
theorem cond_of_fold_att (W : Verify.Public) (l g : Nat) (z own c : Block S Unit)
    (hz : Att.readsAtO (Cl := Unit) W l g = some z) (name : String)
    (gd : c.Under (Block.andThen name own z)) (ho : own.Leaves lay7)
    (pre post : List (Block S Unit)) (hm : ∀ b ∈ pre, b.Leaves lay7)
    (hp : ∀ b ∈ post, b.Leaves lay7 ∧ b.Leaves onThird) (ft : Nat) (s0 : S)
    (rs : List Fmt.RoundView) (cols : List Col) (out : S × List Fmt.RoundView × List Col)
    (H : foldBlocks ft (pre ++ c :: post) s0 rs cols = .ok out)
    (tlP tl0 : HTailF2) (h0 : s0.tl? = some tlP) (hl : SameLay tlP tl0)
    (hF : OnBytes.Tie.Pv.Tail.Port.Fits tlP) : SameLay (recOf tl0 out.1) tl0 ∧ Extra out.1 := by
  have c7 : c.Leaves lay7 := leaves_of_under gd (leavesAndThen S Unit _ lay7 name own z ho
    (attO_lay7 W l g z hz))
  have c3 : c.Lays onThird (fun _ => some true) := lays_of_under gd (fun s rs gs s' Hd => by
    obtain ⟨t, _, Hd⟩ :=
      bindOk (x := own.decide s (rs.take own.rounds.length) (gs.take own.openings)) Hd
    exact attO_onThird W l g z hz _ _ _ _ Hd)
  have h7 := foldLeaves S Unit _ lay7 ft (pre ++ c :: post) s0 rs cols out (fun b hb => by
    rcases List.mem_append.1 hb with h | h
    · exact hm b h
    · rcases List.mem_cons.1 h with h | h
      · rw [h]
        exact c7
      · exact (hp b h).1) H
  have h3 := foldLays S Unit _ onThird _ ft pre c post s0 rs cols out c3
    (fun b h => (hp b h).2) H
  refine cond_of_readings tlP tl0 out.1 ?_ h3 hl hF
  rw [h7]
  unfold lay7
  rw [h0]
  rfl

end VerifiableInference.Desc.First.K8.Ready

#print axioms VerifiableInference.Desc.First.K8.Ready.cond_of_readings
#print axioms VerifiableInference.Desc.First.K8.Ready.cond_of_tests
#print axioms VerifiableInference.Desc.First.K8.Ready.leaves_of_tl
#print axioms VerifiableInference.Desc.First.K8.Ready.attO_lay7
#print axioms VerifiableInference.Desc.First.K8.Ready.attO_onThird
#print axioms VerifiableInference.Desc.First.K8.Ready.cond_of_fold_att
