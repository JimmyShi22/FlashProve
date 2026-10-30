-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Keeps/MaskStays.lean: the mask of the fold that a link's first call lays into the
request's frame is still there when the link closes: the calls of a link's routine that turn the
link's own state leave it.

ReqFrame.first (OnBytes/Iop/Req.lean) notes the number of the oracle message that holds the fold's
mask; ReqFrame.close hands it to the fold. Between the two a link's routine turns its own state
(LinkCtx, OnBytes/Model/Trees.lean) in rootInH, which receives the messages of a later moment, and
in t2Batch. This file says that neither turns the mask.

Main names:
  SameMask L L': the frame of L' has the mask of the frame of L.
  later_mask: ChainCheck.later leaves the frame's mask.
  Stays.apply, runs_set: two small laws.
  Lands L0 x: wherever x succeeds from the link's state L0, SameMask from L0 to the state behind.
    Lands.bind_stays, Lands.set.
  rootInH_mask, t2Batch_mask: the two routines leave the mask.

Limits: one direction: from a success; rootInH on a view. Of the frame's other fields nothing is
said.
-/
import OnBytes.Tie.Pv.Keeps.DoorRan
import OnBytes.Tie.Pv.Keeps.KeepsLaterFinish

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.L5
open OnBytes OnBytes.Model

/-- The frame of L' has the mask of the frame of L. -/
def SameMask (L L' : LinkCtx) : Prop := L'.check.frame.mask = L.check.frame.mask

theorem later_mask (k : ChainCheck) {c : Ctx} {chk : ChainCheck} {cOut : Ctx}
    (hd : c.ch.dry = false) (h : k.later c = .ok (chk, cOut)) :
    chk.frame.mask = k.frame.mask := by
  obtain ⟨r, L, ids, j, k3, P, _, e⟩ := Rest.chain_later_parts k (cEnd := cOut) hd id h
  have ej := joinOwn_same _ _ _ P.joined
  rw [e, P.result, ej]

theorem Stays.apply {α : Type} {x : LinkM α} (h : Stays x) {s : HasRuns.St LinkM} {a : α}
    {s' : HasRuns.St LinkM} (r : Runs x s a s') : s'.1 = s.1 := h s a s' r

theorem runs_set {m : Type → Type} [Monad m] [HasRuns m] {σ : Type} {v : σ}
    {s : HasRuns.St (StateT σ m)} {u : PUnit} {s' : HasRuns.St (StateT σ m)}
    (h : Runs (set v : StateT σ m PUnit) s u s') : s' = (v, s.2) := by
  obtain ⟨e1, e2⟩ := HasRuns.runs_pure (m := m) (a := (PUnit.unit, v)) h
  exact Prod.ext (congrArg Prod.snd e1) e2

/-- From the link's state L0 the routine leaves a state with L0's mask. -/
def Lands {α : Type} (L0 : LinkCtx) (x : LinkM α) : Prop :=
  ∀ (s : HasRuns.St LinkM) (a : α) (s' : HasRuns.St LinkM), s.1 = L0 → Runs x s a s' →
    SameMask L0 s'.1

theorem Lands.bind_stays {α β : Type} {L0 : LinkCtx} {x : LinkM α} {f : α → LinkM β}
    (hx : Stays x) (hf : ∀ a, Lands L0 (f a)) : Lands L0 (x >>= f) := fun s b s' e h => by
  obtain ⟨a, s1, h1, h2⟩ := HasRuns.runs_bind h
  exact hf a s1 b s' ((hx _ _ _ h1).trans e) h2

theorem Lands.set {L0 v : LinkCtx} (h : SameMask L0 v) : Lands L0 (set v : LinkM PUnit) :=
  fun _ _ _ _ r => by
    rw [runs_set r]
    exact h

/-- rootInH leaves the frame's mask. -/
theorem rootInH_mask (trees : List Nat) {L L' : LinkCtx} {F F' : Fork} {c c' : Ctx}
    (hd : c.ch.dry = false) (h : rootInH trees L F c = .ok ((((), L'), F'), c')) :
    SameMask L L' := by
  have hr : Runs (rootInH trees) (L, F, c) () (L', F', c') := h
  unfold rootInH at hr
  obtain ⟨L0, ⟨La, Fa, ca⟩, r0, d0, hr⟩ := step hr hd
  have ea : La = L := congrArg Prod.fst (runs_get r0).2
  obtain ⟨_, ⟨Lb, Fb, cb⟩, r1, d1, hr⟩ := step hr d0
  have eb : Lb = La := Stays.apply (Stays.sub _) r1
  obtain ⟨_, ⟨L2, F2, c2⟩, r2, hr⟩ := HasRuns.runs_bind hr
  obtain ⟨_, s3, r3, hr⟩ := HasRuns.runs_bind hr
  have e3 := runs_modify r3
  have e4 : L' = s3.1 := by
    refine Stays.apply ?_ hr
    repeat' first
      | exact Stays.pure _
      | exact Stays.get
      | exact Stays.sub _
      | refine Stays.forInL _ (fun _ _ => ?_) _ _
      | refine Stays.bind ?_ fun _ => ?_
      | split
  -- the call, by its text
  have r2' : Runs (m := SubM) (do
      SubM.must (Lb.link == Lb.check.link)
      let check ← (liftM Lb.check.later : SubM ChainCheck)
      pure ((), { Lb with check := check })) (Fb, cb) ((), L2) (F2, c2) := r2
  obtain ⟨_, ⟨F3, y3⟩, q1, q2⟩ := HasRuns.runs_bind r2'
  obtain ⟨q1', _⟩ := runs_lift (σ := Fork) (x := Blk.must (Lb.link == Lb.check.link)) q1
  obtain ⟨_, ey⟩ := runs_must q1'
  obtain ⟨chk, ⟨F4, y4⟩, q3, q4⟩ := HasRuns.runs_bind q2
  obtain ⟨q3', _⟩ := runs_up (σ := Fork) (x := Lb.check.later) q3
  obtain ⟨e5, _⟩ := HasRuns.runs_pure q4
  have hy3 : y3 = cb := ey
  subst hy3
  have hL2 : L2 = { Lb with check := chk } := congrArg Prod.snd e5
  have hm := later_mask Lb.check d1 q3'
  unfold SameMask
  rw [e4, e3, hL2, ← ea, ← eb]
  exact hm

/-- t2Batch leaves the frame's mask. -/
theorem t2Batch_mask (used : Nat) {L L' : LinkCtx} {F F' : Fork} {c c' : Ctx}
    (h : t2Batch used L F c = .ok ((((), L'), F'), c')) : SameMask L L' := by
  have hr : Runs (t2Batch used) (L, F, c) () (L', F', c') := h
  unfold t2Batch at hr
  obtain ⟨L0, s0, r0, rest⟩ := HasRuns.runs_bind hr
  clear hr h
  obtain ⟨e0, e0'⟩ := runs_get r0
  have e0'' : L0 = L := e0
  subst e0''
  refine (?_ : Lands L0 _) s0 () (L', F', c') (congrArg Prod.fst e0') rest
  repeat' first
    | exact Lands.set rfl
    | refine Lands.bind_stays (Stays.sub _) fun _ => ?_
    | split

end OnBytes.L5

#print axioms OnBytes.L5.later_mask
#print axioms OnBytes.L5.rootInH_mask
#print axioms OnBytes.L5.t2Batch_mask
