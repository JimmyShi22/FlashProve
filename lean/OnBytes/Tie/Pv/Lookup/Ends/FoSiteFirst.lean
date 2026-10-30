-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoSiteFirst.lean.
The start of a link of the byte-level verifier: no message of the prover is open where the
sub-proof's routine begins.

A sub-proof's routine is started by `runLinkH` right behind the chain's first call for the link.

 * Small ways for a link's routine: `pureL_ok`; `CalmL.liftB`, `CalmS.liftB`; `cleanL`, `cleanS` (a
   calm line leaves a clean context clean); `slots_line` (the line that sets up the slots: the state
   behind it, and the context, outright); `calm_getAs`, `calmS_replyToken`, `inPlace_ok`,
   `calm_indexMasksH`.
 * `stillB_bind` and five blocks: `StillB b` (OnBytes/Tie/Pv/Lookup/Ends/FoStill.lean: a run of the
   block b that returns leaves
   the context as it was) of the few blocks that stand between the chain's first call and the
   routine.
 * `link_entry`: if `runLinkH` returns from a context c on a view, then the chain's first call for
   the link has run from c itself, to (check', c1); `Clean c1`
     (OnBytes/Tie/Pv/Lookup/Ends/FoShutLink.lean); and the
   sub-proof's routine `X.run` has run from the link's state made of check', from the planned state
   `X.Fp` and from c1 itself. Each witness is fixed by a run equation whose start is named.

Not tied in `link_entry`: the end of the routine's run, (o, C, F, c2), to the result r of
`runLinkH`. A premise is left: that the run is on a view where `runLinkH` begins
(OnBytes/Tie/Pv/Lookup/Ends/FoLinks.lean
carries it from link to link).

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoSite
import OnBytes.Tie.Pv.Lookup.Ends.FoStill
import OnBytes.Model.Layer
import OnBytes.Model.Attention
import OnBytes.Model.Head
import OnBytes.Model.StagesLinks

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun

section
variable {α : Type}

theorem pureL_ok (a : α) (L : LinkCtx) (F : Fork) (c : Ctx) (r : ((α × LinkCtx) × Fork) × Ctx) :
    (Pure.pure a : LinkM α) L F c = .ok r ↔ r = (((a, L), F), c) := pure_ok (a, L) F c r

theorem CalmL.liftB {b : Blk α} (h : Calm b) : CalmL (MonadLiftT.monadLift b : LinkM α) :=
  CalmL.lift (CalmS.lift h)
theorem CalmS.liftB {b : Blk α} (h : Calm b) : CalmS (MonadLiftT.monadLift b : SubM α) :=
  CalmS.lift h

/-- A calm line of a link's routine leaves a clean context clean. -/
theorem cleanL {x : LinkM α} (hx : CalmL x) {L L' : LinkCtx} {F G : Fork} {c c' : Ctx} {a : α}
    (h : x L F c = .ok (((a, L'), G), c')) (hc : Clean c) : Clean c' := (hx L F).clean h hc

theorem cleanS {x : SubM α} (hx : CalmS x) {F G : Fork} {c c' : Ctx} {a : α}
    (h : x F c = .ok ((a, G), c')) (hc : Clean c) : Clean c' := (hx F).clean h hc

/-- The line that sets up the slots. -/
theorem slots_line {f : Fork → Fork} {n : ℕ} {L L' : LinkCtx} {F G : Fork} {c c' : Ctx} {a : Unit}
    (h : LinkM.sub (SubM.change fun F => some ((f F).slots n)) L F c = .ok (((a, L'), G), c')) :
    G = (f F).slots n ∧ c' = c := by
  obtain ⟨_, G', c1, h1, e⟩ := (subL_ok _ _ _ _ _).1 h
  obtain ⟨G'', e1, e2⟩ := (change_ok _ _ _ _).1 h1
  obtain ⟨⟨_, rfl⟩, rfl⟩ : (L' = L ∧ G = G') ∧ c' = c1 := by simpa [Prod.ext_iff] using e
  obtain ⟨rfl, rfl⟩ : G = G'' ∧ c' = c := by simpa [Prod.ext_iff] using e2
  exact ⟨(Option.some.inj e1).symm, rfl⟩

end

theorem calm_getAs {α : Type} (name : String) (x : Option α) : Calm (Head.getAs name x) := by
  unfold Head.getAs refuse; calm

theorem calmS_replyToken (plain : Array E) (V : Nat) : CalmS (Head.replyToken plain V) := by
  unfold Head.replyToken
  exact CalmS.bind (CalmS.liftB (calm_mustAs _ _)) fun _ =>
    CalmS.bind (CalmS.liftB (calm_testAs _ _)) fun _ => CalmS.pure _

/-! ### the start of a link -/

theorem inPlace_ok {α : Type} (place : String) (b : Blk α) (c : Ctx) (x : α × Ctx)
    (h : Blk.inPlace place b c = .ok x) : b c = .ok x := by
  unfold Blk.inPlace at h
  split at h
  · exact absurd h (by simp)
  · rename_i y e
    rw [e]
    exact h

theorem calm_indexMasksH (links : Array Stages.LinkH) (p : Params.First) (k : ChainCheck) :
    Calm (Stages.indexMasksH links p k) := by
  unfold Stages.indexMasksH
  have a := calm_mustAs
  unfold refuse
  repeat (first | exact a _ _ | calm_atom | intro _ | apply Calm.bind | split)

/-! ### blocks that leave the context as it is -/

theorem stillB_bind {α β : Type} {x : Blk α} {f : α → Blk β} (hx : StillB x)
    (hf : ∀ a, StillB (f a)) : StillB (x >>= f) := fun c r h => by
  obtain ⟨a, c1, h1, h2⟩ := (bindB_ok x f c r).1 h
  exact ((hf a) c1 r h2).trans (hx c (a, c1) h1)

theorem stillB_must (b : Bool) (name : String) : StillB (Blk.must b name) := fun c r h => by
  unfold Blk.must at h
  split at h <;> cases h
  rfl
theorem stillB_get {α : Type} (x : Option α) (name : String) : StillB (Blk.get x name) :=
  fun c r h => by
    unfold Blk.get at h
    split at h <;> cases h
    rfl
theorem stillB_statement : StillB Blk.statement := fun c r h => by
  cases h
  rfl
theorem stillB_oracle (o : Nat) : StillB (Blk.oracle o) := by
  unfold Blk.oracle
  exact stillB_bind stillB_statement fun _ => stillB_get _ _
theorem stillB_indexMasksH (links : Array Stages.LinkH) (p : Params.First) (k : ChainCheck) :
    StillB (Stages.indexMasksH links p k) := by
  unfold Stages.indexMasksH
  refine stillB_bind (StillB.mustAs _ _) fun _ => ?_
  split
  · exact stillB_bind (stillB_oracle _) fun _ => stillB_bind (stillB_get _ _) fun _ =>
      stillB_bind (StillB.mustAs _ _) fun _ => StillB.pure _
  · exact StillB.refuse _

/-- The start of a link. If `runLinkH` returns from a context c on a view: the chain's first call
for the link has run from c itself; where it ended, at c1, no message is open; and the sub-proof's
routine has run from the link's state that is made of that call's result, from the planned state
and from c1 itself. -/
theorem link_entry (links : Array Stages.LinkH) (p : Params.First) (wsLay : WsLay) (l : Nat)
    (X : Stages.LinkH) (check : ChainCheck) (out : Proof.LinksResult) (c : Ctx)
    (r : (ChainCheck × Proof.LinksResult) × Ctx)
    (h : Stages.runLinkH links p wsLay l X check out c = .ok r) (hd : c.ch.dry = false) :
    ∃ (check' : ChainCheck) (c1 c2 : Ctx) (o : Option WsForkOut) (C : LinkCtx) (F : Fork),
      check.first c = .ok (check', c1) ∧ Clean c1 ∧
      X.run { check := check', link := l, arrayOf := X.arrayOf, list := X.Tp } X.Fp c1 =
        .ok (((o, C), F), c2) := by
  unfold Stages.runLinkH at h
  obtain ⟨check', c1, h1, h⟩ := (bindB_ok _ _ _ _).1 h
  have k1 : Clean c1 := (shut_checkFirst check).out c check' c1 h1 hd
  dsimp only at h
  split at h
  · obtain ⟨_, c2, h2, h⟩ := (bindB_ok _ _ _ _).1 h
    obtain ⟨_, d2, e2, h⟩ := (bindB_ok _ _ _ _).1 h
    obtain ⟨_, c3, h3, h⟩ := (bindB_ok _ _ _ _).1 h
    obtain ⟨_, c4, h4, h⟩ := (bindB_ok _ _ _ _).1 h
    obtain ⟨⟨⟨o, C⟩, F⟩, c5, h5, _⟩ := (bindB_ok _ _ _ _).1 h
    obtain rfl : c2 = c1 := stillB_indexMasksH _ _ _ _ _ h2
    obtain rfl : d2 = c2 := StillB.pure _ _ _ e2
    obtain rfl : c3 = d2 := StillB.mustAs _ _ _ _ h3
    obtain rfl : c4 = c3 := stillB_must _ _ _ _ h4
    exact ⟨check', _, c5, o, C, F, h1, k1, inPlace_ok _ _ _ _ h5⟩
  · obtain ⟨_, d2, e2, h⟩ := (bindB_ok _ _ _ _).1 h
    obtain ⟨_, c3, h3, h⟩ := (bindB_ok _ _ _ _).1 h
    obtain ⟨_, c4, h4, h⟩ := (bindB_ok _ _ _ _).1 h
    obtain ⟨⟨⟨o, C⟩, F⟩, c5, h5, _⟩ := (bindB_ok _ _ _ _).1 h
    obtain rfl : d2 = c1 := StillB.pure _ _ _ e2
    obtain rfl : c3 = d2 := StillB.mustAs _ _ _ _ h3
    obtain rfl : c4 = c3 := stillB_must _ _ _ _ h4
    exact ⟨check', _, c5, o, C, F, h1, k1, inPlace_ok _ _ _ _ h5⟩

end Fo
