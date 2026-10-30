-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Wipe/KeepReads.lean: the closing of a segment (K10): the steps without a round that
close the list of tables in front of the smallness test (Johnson/Desc/K8/ReadsQuiet.lean,
Johnson/Desc/First/Att/ReadsO.lean, laid by ProofFile.readsQuietAt, Johnson/Desc/ProofFile/Lots/Makers.lean) commute with the
wiping of the first chain's state (wipeS, Honest/K10/WipeS.lean: the state with these targets set to zero: those of the
statement's rows, of the carried rows in each frame that the state holds and, at the finish, of the batched row; the
rows on the table (the pile out.pending, and the claim at the chain's end) keep theirs). Theorems alone.

What is proved.
  answered_wipe, fixed_wipe, orderOk_wipe, orderFront_wipe   the guard of order (Johnson/Desc/First/K8/Order.lean) has
                   the same value at a link's context and a statement and at both wiped: of a message it asks only
                   whether it is sampled
  readsClosed_wipe, readsStepO_wipe   so have the two texts that are handed the context and the statement whole
  layers_whole2, headReads_whole2, readsAtSO_comm, readsAtO_whole2, readsBlockAt_whole2   the steps, one kind of link
                   after the other: Whole2 wipeS (Wipe/Alike.lean)
  **reads2**       the field reads of SeatKeeps2 (Wipe/Lots2.lean) at wipeS

By what. The guard's text is unfolded. What it reads of the context unfolds to the same term at both; a message of the
wiped statement is the statement's message, wiped (wipeSt_oracle_at, Honest/K10/BatWipe.lean). Each step is followed
bind by bind (Wipe/Carry.lean) at a state taken apart into its fields and the six kinds of place. None writes a target,
so step (wipeS s) = (step s).map wipeS holds as it stands, and Decides2.of_comm or Fn2.of_comm (Wipe/Alike.lean)
applies.

Limits. The laws speak of all states, reachable or not. The makers of the tables are not opened: they are handed no
state. No property of the protocol is claimed: nothing is said on its soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Wipe.Carry
import Johnson.Desc.ProofFile.Honest.K10.Wipe.Wrap2
import Johnson.Desc.ProofFile.Honest.K10.Wipe.WipeLaws
import Johnson.Desc.ProofFile.Lots.Makers

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (Statement E)
open OnBytes.Model (LinkCtx Fork HTailF2 HFun)
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8.Order (Lies liesAt sentInFront namedNow answered fixed orderOk)

/-! ## 1 The guard of order -/

/-- Whether an array's message has had its sample answered is the same at the wiped context and statement. -/
theorem answered_wipe (L : LinkCtx) (T : Statement) (w : Lies) :
    answered (wipeCtx L) (wipeSt T) w = answered L T w := by
  have e : namedNow (wipeCtx L).check.frame w = namedNow L.check.frame w := rfl
  unfold answered
  rw [e]
  cases namedNow L.check.frame w with
  | none => rfl
  | some o =>
    dsimp only
    rw [wipeSt_oracle_at]
    cases T.oracles[o]? <;> rfl

/-- Whether an array is fixed in front of the draw is the same at the wiped context and statement. -/
theorem fixed_wipe (L : LinkCtx) (T : Statement) : fixed (wipeCtx L) (wipeSt T) = fixed L T := by
  funext array
  have e : liesAt (wipeCtx L) array = liesAt L array := rfl
  unfold fixed
  rw [e]
  cases liesAt L array with
  | none => rfl
  | some w => exact congrArg (fun b => sentInFront L w && b) (answered_wipe L T w)

/-- The guard of order is the same at the wiped context and statement. -/
theorem orderOk_wipe (tl : HTailF2) (L : LinkCtx) (T : Statement) :
    orderOk tl (wipeCtx L) (wipeSt T) = orderOk tl L T := by
  unfold orderOk
  rw [fixed_wipe]
  rfl

/-- The tests in front of the draw are the same at the wiped context and statement. -/
theorem orderFront_wipe (tl : HTailF2) (L : LinkCtx) (T : Statement) :
    VerifiableInference.Desc.First.K8.Order.front tl (wipeCtx L) (wipeSt T) =
      VerifiableInference.Desc.First.K8.Order.front tl L T := by
  unfold VerifiableInference.Desc.First.K8.Order.front
  rw [orderOk_wipe]

/-! ## 2 The texts that are handed the context and the statement whole -/

/-- The closing of the list of tables is the same at the wiped context and statement. -/
theorem readsClosed_wipe (tl : HTailF2) (funs : Array HFun) (L : LinkCtx) (T : Statement) :
    VerifiableInference.Desc.K8.ReadsQuiet.closed tl funs (wipeCtx L) (wipeSt T) =
      VerifiableInference.Desc.K8.ReadsQuiet.closed tl funs L T := by
  unfold VerifiableInference.Desc.K8.ReadsQuiet.closed
  simp only [orderFront_wipe]

/-- An attention segment's step on data is the same at the wiped context and statement. -/
theorem readsStepO_wipe (c : VerifiableInference.Desc.First.Att.P.ParC) (zk : Array (Array E))
    (look : VerifiableInference.Desc.First.Att.P.LookIn) (h : VerifiableInference.Desc.First.Att.P.Heard)
    (tl : HTailF2) (L : LinkCtx) (T : Statement) (F : Fork) :
    VerifiableInference.Desc.First.Att.readsStepO c zk look h tl (wipeCtx L) (wipeSt T) F =
      VerifiableInference.Desc.First.Att.readsStepO c zk look h tl L T F := by
  unfold VerifiableInference.Desc.First.Att.readsStepO
  simp only [orderFront_wipe]

/-! ## 3 The steps -/

/-- The step at a layers' link has like outcomes at two states that are equal once wiped; it states no run. -/
theorem layers_whole2 (P : VerifiableInference.Desc.K8.ReadsQuiet.PG) :
    Whole2 wipeS (VerifiableInference.Desc.K8.ReadsQuiet.layers P) := by
  refine ⟨Decides2.of_comm (fun _ _ _ _ => rfl) fun s rs gs => ?_, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩
  obtain ⟨st, book, roots, owed, failed, check, out, here, req⟩ := s
  cases here with
  | lay a =>
    refine Carry.headE _ fun own => ?_
    refine Carry.headEqE _ (readsClosed_wipe P.tl own.funs a.L st) fun tl => ?_
    rfl
  | between => rfl
  | att a => rfl
  | head a => rfl
  | fin a => rfl
  | mem a => rfl

/-- The step at the head's link has like outcomes at two states that are equal once wiped; it states no run. -/
theorem headReads_whole2 (P : VerifiableInference.Desc.K8.ReadsQuiet.PH) :
    Whole2 wipeS (VerifiableInference.Desc.K8.ReadsQuiet.head P) := by
  refine ⟨Decides2.of_comm (fun _ _ _ _ => rfl) fun s rs gs => ?_, (fun _ hc => nomatch hc),
    (fun _ hc => nomatch hc)⟩
  obtain ⟨st, book, roots, owed, failed, check, out, here, req⟩ := s
  cases here with
  | head a =>
    refine Carry.headE _ fun _ => ?_
    refine Carry.headEqE _ (congrArg
      (VerifiableInference.Desc.K8.ReadsQuiet.under "reads: the covered positions cannot be said")
      (covered_wipe P.h.T P.h.V ⟨st, book, roots, owed, failed, check, out, .head a, req⟩)) fun cov => ?_
    refine Carry.headE _ fun x => ?_
    refine Carry.headE _ fun t => ?_
    refine Carry.headEqE _ (readsClosed_wipe P.hp.tl t.funs a.L st) fun tl => ?_
    rfl
  | between => rfl
  | lay a => rfl
  | att a => rfl
  | fin a => rfl
  | mem a => rfl

/-- The step at an attention link commutes with the wiping. -/
theorem readsAtSO_comm (A : OnBytes.Attention.Plan) (s : S) :
    VerifiableInference.Desc.First.Att.readsAtSO A (wipeS s) =
      (VerifiableInference.Desc.First.Att.readsAtSO A s).map wipeS := by
  obtain ⟨st, book, roots, owed, failed, check, out, here, req⟩ := s
  cases here with
  | att a =>
    refine Carry.headE _ fun h => ?_
    refine Carry.headE _ fun g => ?_
    refine Carry.headEqE _ (readsStepO_wipe _ g.zk _ h a.tl a.L st a.F) fun r => ?_
    rfl
  | between => rfl
  | lay a => rfl
  | head a => rfl
  | fin a => rfl
  | mem a => rfl

/-- So the member at an attention link has like outcomes at two states that are equal once wiped. -/
theorem readsAtO_whole2 {Cl : Type} {W : OnBytes.Model.Verify.Public} {l g : Nat} {b : Block S Cl}
    (h : VerifiableInference.Desc.First.Att.readsAtO W l g = some b) : Whole2 wipeS b := by
  unfold VerifiableInference.Desc.First.Att.readsAtO at h
  obtain ⟨A, -, rfl⟩ := Option.map_eq_some_iff.1 h
  exact quiet_whole2 (Fn2.of_comm (readsAtSO_comm A)) (fun _ _ _ => rfl) rfl rfl

/-- The member that blockAt lays at a layers' link or at the head's is one of the two above, so it has like outcomes. -/
theorem readsBlockAt_whole2 {G : Array OnBytes.Model.Layer.HPlan2} {hS : OnBytes.Model.Head.Shape}
    {HLy : OnBytes.Model.Head.HL} {Hp : OnBytes.Model.Head.HPlanH2} {kinds : List (Nat × Nat)} {l : Nat}
    {b : Block S Unit} (h : VerifiableInference.Desc.K8.ReadsQuiet.blockAt G hS HLy Hp kinds l = some b) :
    Whole2 wipeS b := by
  unfold VerifiableInference.Desc.K8.ReadsQuiet.blockAt at h
  obtain ⟨k, -, h⟩ := Option.bind_eq_some_iff.1 h
  split at h
  · obtain ⟨hp, -, rfl⟩ := Option.map_eq_some_iff.1 h
    exact layers_whole2 _
  · split at h
    · cases h
      exact headReads_whole2 _
    · cases h

/-- **Every member that readsQuietAt lays** has like outcomes at two states that are equal once wiped. -/
theorem reads2 {G : ProofFile.Ground} {l : Nat} {X : OnBytes.Model.Stages.LinkH} {piece : Nat} {b : Block S Unit}
    (h : ProofFile.readsQuietAt G l X piece = some b) : Whole2 wipeS b := by
  unfold ProofFile.readsQuietAt at h
  repeat' split at h
  all_goals first
    | exact readsAtO_whole2 h
    | exact readsBlockAt_whole2 h
    | cases h

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.answered_wipe
#print axioms ProofFile.Honest.K10.fixed_wipe
#print axioms ProofFile.Honest.K10.orderOk_wipe
#print axioms ProofFile.Honest.K10.orderFront_wipe
#print axioms ProofFile.Honest.K10.readsClosed_wipe
#print axioms ProofFile.Honest.K10.readsStepO_wipe
#print axioms ProofFile.Honest.K10.layers_whole2
#print axioms ProofFile.Honest.K10.headReads_whole2
#print axioms ProofFile.Honest.K10.readsAtSO_comm
#print axioms ProofFile.Honest.K10.readsAtO_whole2
#print axioms ProofFile.Honest.K10.readsBlockAt_whole2
#print axioms ProofFile.Honest.K10.reads2
