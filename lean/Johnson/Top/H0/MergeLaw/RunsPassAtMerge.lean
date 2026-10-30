-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/RunsPassAtMerge.lean: the eighteen fields of `RunsPass` (KeepAtMerge.lean)
across the accepting step of the merge of the claims on the committed table, at the composed meaning
`mgAll D Mg`, from named premises. A joining: it shows nothing of a run that the files beneath do
not. Theorems with their proofs.

What is joined. `NotLate` at the nine runs: `nine_late` (RunsLate.lean). `Fwd` at "objects" and
"guests" of the two lookups and at "join": `five_fwd` (RunsFwdLook.lean); at "planes":
`fwd_planes` (RunsFwdPlanes.lean); at the output head's three own runs: `fwd_own`, here, by
`reader_rides_own` (Johnson/Desc/Kinds/Law/ReaderRides.lean) and `merge_alike` (AlikeAtMerge.lean).
Two of the premises of these come out of the table's condition at border 346 (`Sound.onQ`,
Johnson/Desc/Sound/BordersQ.lean, at the composed meaning and the written list): `ledgerB`
(`ledger_at_front`, KeepAtMerge.lean) and the lookup arguments' public test behind the lookup on the
calls (`lookOut_at_front`, here).

Main names:
  `fwd_own`: `Fwd` at one of the output head's own runs, from `OwnIs` and `speaksAt` (RunsAre.lean).
  `lookOut_at_front`: out of the table's condition at border 346 (`Sound.onQ`), at an unmarked
    state, where the output head's segment has the number 24: `lookOutC` at the lookup on the calls
    accepts.
  `runsPass_at_merge`: THE EIGHTEEN, at one pair of states.
  `runs_in_frame`: the same for all states with the table's condition that are "reached" and
    unmarked: the form in which a law on the merge's sub-protocol takes `RunsPass` as a premise.

WHAT STAYS A PREMISE, BY NAME:
  D.lk 24 = some l: the segment is there.
  `RunsAre l X iU3 lm`: which runs the segment states.
  `Speaks l a`: five tests with code at the state in front: the stated run's own reader answers.
  `leavesLenB a`: one test with code at the state in front, on what the lookup on the calls has
    heard.
  Mg.more = {}; the output head's segment has the number 24; the table's condition in front; no
  mark; the merge's accepting step.
Beside the segment, `RunsAre`, `Speaks`, the table's condition, the number 24 and the step, that is
three things more than one might look for: `leavesLenB`, in `runs_in_frame` along all reached states
as `Speaks` is; the two letters iU3 and lm of `RunsAre`; and Mg.more = {}. `RunsAre` and `Speaks`
are wanted at the very l that D.lk 24 gives.

Limits. NO EXAMPLE IN LEAN: the premises are shown together at no value. AN EVALUATION, NO THEOREM:
over another state of the library, the terms of `speaksAt` at the five runs of `Speaks` and of
`leavesLenB`, typed out, have been seen to accept at the state in front of the merge of one honest
full-size run over synthetic weights, and the five own readers' answers in front of the merge and
behind it were one. `RunsAre`, `ledgerB` and `lookOutC` have not been evaluated there; `RunsAre` is
shown in another file of segment 24 of the first chain as it is made, in scope, at an opening
(`runsAre_at_link24`, RunsAreAtLink.lean), which is not called here. In `runs_in_frame` "reached"
is a letter, spent on nothing but the two premises on the family of states: at "never" all is free.
IDLE CASES: those of the files beneath. Nothing on soundness.

-/
import Johnson.Top.H0.MergeLaw.RunsFwdPlanes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized)
open VerifiableInference.Desc (Link Claim)
open VerifiableInference.Reads.Pass (Fwd)
open VerifiableInference.Desc.K9 (statesOfLink readerOf readersAt)
open VerifiableInference.Desc.First.Look (lookOutC)
open VerifiableInference.Desc.Sound (MgData mgAll mgAll_pub keep24 linksFull CellsQ MsgT k11_hIn)
open VerifiableInference.Desc.Kinds.Head.Law (Alike reader_rides_own)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-- **`Fwd` at one of the output head's own runs.** -/
theorem fwd_own {lk : ℕ → Option (Link S Claim)} {X : OnBytes.Model.Verify.Public} {mH m : ℕ}
    {l : Link S Claim} (hlk : lk m = some l) {iU3 : ℕ} {name : String}
    (hn : (name == "K8.equations") = false) (ho : OwnIs l X iU3 name) {a b : S} (al : Alike a b)
    {F F' : Fork} (hF : a.fork? = some F) (hF' : b.fork? = some F')
    (hrow : F'.trees.map (·.R) = F.trees.map (·.R)) (hs : speaksAt l 3 name a = true) :
    Fwd (readersAt lk X mH m) 3 name a b := by
  obtain ⟨own, hrun, run, hf, fwd, bwd⟩ := ho
  intro R hR
  rcases forms_opens hlk hn hR with h | ⟨h0, -⟩
  · exact forms_closes hlk hn
      (reader_rides_own X.hS iU3 24 4 _ hf hrun fwd bwd al hF hF' hrow h)
  · unfold speaksAt at hs
    rw [h0] at hs
    cases hs

section
variable {Xi P Tok : Type} {rows cols nR : ℕ} {X : OnBytes.Model.Verify.Public}
  (D : MgData Xi P Tok rows cols nR X)
  (Mg : Meaning P (Wit (CellsQ rows cols) Tok MsgT))

/-- **Out of the table's condition at border 346**, at an unmarked state: the lookup arguments'
public test behind the lookup on the calls accepts. -/
theorem lookOut_at_front (hM : Mg.more = {}) (hH : VerifiableInference.OnPublicFiles.headLink X = 24)
    (Nn : Numbers) {Fr : Sound.Frame} (z : P) (a : S × Fr.E.Str)
    (hon : Sound.onQ Nn (mgAll D Mg) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346
      a) (hf : a.1.failed = none) : lookOutC D.pubD.d3 24 false a.1 = true := by
  unfold Sound.onQ onAt at hon
  obtain ⟨-, hmk | ⟨hb, -⟩⟩ := hon
  · exact absurd hf hmk
  · simp only [Bool.and_eq_true] at hb
    obtain ⟨⟨-, hpub⟩, -⟩ := hb
    unfold pubHeld at hpub
    have h1 : (mgAll D Mg).pub (.lookOut 24 3) (z, a.1) = true :=
      List.all_eq_true.1 hpub (Pub.lookOut 24 3)
        (k11_hIn D Mg hM (Pub.lookOut 24 3) (List.mem_append_right _ (by simp [keep24])))
    rw [mgAll_pub, pubAll_lookOut D.pubD Mg.pub 24 3 false (sorts_at_head hH).1] at h1
    exact h1

/-- **THE EIGHTEEN FIELDS OF `RunsPass` ACROSS THE MERGE's ACCEPTING STEP.** -/
theorem runsPass_at_merge (hM : Mg.more = {}) (hH : VerifiableInference.OnPublicFiles.headLink X = 24)
    (Pm : HeadMergeP) (Nn : Numbers) {Fr : Sound.Frame} {l : Link S Claim}
    (hlk : D.lk 24 = some l) {iU3 lm : ℕ} (H : RunsAre l X iU3 lm) (z : P) (a b : S × Fr.E.Str)
    {rs : List Fmt.RoundView}
    (hon : Sound.onQ Nn (mgAll D Mg) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346
      a) (hf : a.1.failed = none) (hy : headMergeDecide Pm a.1 rs = .ok b.1)
    (hsp : Speaks l a.1) (hlen : leavesLenB a.1 = true) : RunsPass (D.Rd 24) Pm a.1 b.1 := by
  obtain ⟨hled, -⟩ := ledger_at_front D Mg hM Nn z a hon hf
  have hout := lookOut_at_front D Mg hM hH Nn z a hon hf
  have L : NineLate (readersAt D.lk X (VerifiableInference.OnPublicFiles.headLink X) 24) Pm a.1 :=
    nine_late hlk H D.pubD.d3 Pm hout hlen
  have V : FiveFwd (readersAt D.lk X (VerifiableInference.OnPublicFiles.headLink X) 24) a.1 b.1 :=
    five_fwd hlk H Pm hy hled hsp.join3
  have pl : Fwd (readersAt D.lk X (VerifiableInference.OnPublicFiles.headLink X) 24) 2 "planes" a.1 b.1 :=
    fwd_planes hlk H.planes2 D.pubD.d3 Pm hy hled hout hlen hsp.planes2
  obtain ⟨F0, hF0, hS⟩ := sized_of_ledgerB hled
  obtain ⟨x, x', hx, hx', rfl, hG, -, -, -⟩ := merge_forks Pm hy hF0
  have al : Alike a.1 b.1 := merge_alike Pm hy fun y hy' => by
    rw [hx] at hy'
    obtain rfl := Here.head.inj hy'
    exact hS
  have hrow : x'.F.trees.map (·.R) = x.F.trees.map (·.R) := by
    rw [merge_trees Pm hy hx hx' hS]
  exact
    { fwd_objects2 := V.fwd_objects2
      late_objects2 := L.late_objects2
      fwd_guests2 := V.fwd_guests2
      late_guests2 := L.late_guests2
      fwd_planes2 := pl
      late_planes2 := L.late_planes2
      fwd_join3 := V.fwd_join3
      late_join3 := L.late_join3
      fwd_norm3 := fwd_own hlk (by decide) H.norm3 al hF0 hG hrow hsp.norm3
      late_norm3 := L.late_norm3
      fwd_policy3 := fwd_own hlk (by decide) H.policy3 al hF0 hG hrow hsp.policy3
      late_policy3 := L.late_policy3
      fwd_logits3 := fwd_own hlk (by decide) H.logits3 al hF0 hG hrow hsp.logits3
      late_logits3 := L.late_logits3
      fwd_objects7 := V.fwd_objects7
      late_objects7 := L.late_objects7
      fwd_guests7 := V.fwd_guests7
      late_guests7 := L.late_guests7 }

/-- **The same for all states with the table's condition that are reached and unmarked.** -/
theorem runs_in_frame (hM : Mg.more = {}) (hH : VerifiableInference.OnPublicFiles.headLink X = 24)
    (Pm : HeadMergeP) (Nn : Numbers) {Fr : Sound.Frame}
    (Rch : ℕ → (P × S) × Fr.E.Str → Prop) {l : Link S Claim} (hlk : D.lk 24 = some l)
    {iU3 lm : ℕ} (H : RunsAre l X iU3 lm)
    (hsp : ∀ (z : P) (a : S × Fr.E.Str),
      Sound.onQ Nn (mgAll D Mg) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none → Speaks l a.1)
    (hlen : ∀ (z : P) (a : S × Fr.E.Str),
      Sound.onQ Nn (mgAll D Mg) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none → leavesLenB a.1 = true) :
    ∀ (z : P) (a b : S × Fr.E.Str),
      Sound.onQ Nn (mgAll D Mg) linksFull (flatPlacesOf linksFull true) (fun s => (z, s)) 346 a →
      Rch 346 ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (∃ rs, headMergeDecide Pm a.1 rs = .ok b.1) → RunsPass (D.Rd 24) Pm a.1 b.1 := by
  intro z a b ha hR hm hy
  obtain ⟨rs, hyes⟩ := hy
  exact runsPass_at_merge D Mg hM hH Pm Nn hlk H z a b ha (Classical.not_not.1 hm) hyes
    (hsp z a ha hR hm) (hlen z a ha hR hm)

end

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.fwd_own
#print axioms VerifiableInference.Desc.First.MergeLaw.lookOut_at_front
#print axioms VerifiableInference.Desc.First.MergeLaw.runsPass_at_merge
#print axioms VerifiableInference.Desc.First.MergeLaw.runs_in_frame
