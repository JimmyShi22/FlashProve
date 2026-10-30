-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/TieThreeDoors.lean: code switching: THE PREMISE hlv OF THE THREE ARMS OF hAt
(hAt_link | hAt_head | hAt_finish, Tw/K2C/TieThreeArms.lean) AT THE FIVE REAL WAYS OUT OF THE CODE
SWITCH's SEATS, as Johnson/P1K2R/SitsDoor.lean names them (KeepsAt · KeepsJoined).
Five theorems with their proofs. NO SUB-PROTOCOL IMPORTS THIS FILE.
  hlv_guards        the guards (a place alone in a segment): hAt_link's hlv
  hlv_opened        leaveOpened f, f a row of framesOf (a segment's first place): hAt_link's hlv
  hlv_head_guards   "H.1.quiet", then the guards: hAt_head's hlv
  hlv_head_opened   "H.1.quiet", then leaveOpened f: hAt_head's hlv
  hlv_finish        "F.0.quiet", then the guards: hAt_finish's hlv
CALLED: P1K2.guards_same · P1K2.leaveOpened_is (SitsDoor.lean) · opened_keeps
(Walk/FrameOpened.lean).
THAT THEY FIT THE ARMS' BINDER hlv is Lean's comparison: Johnson/Loose/PVK2/DoorsFit.lean.
LIMITS. On the way out alone; the way in (the identity, but at the finish) is not spoken of. That a
seat's way out is one of the five is SitsDoor.lean's k02_sits_file. No soundness is claimed. On
hiding nothing.
-/
import Johnson.Top.H0.Tw.K2C.TieThreeArms
import Johnson.P1K2R.SitsDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2Caller
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (headOpenQ finishBehindQ HeadPar)
open Johnson.Desc.First.Walk.Tied (OpenedKeeps opened_keeps)
open Johnson.Desc.First.Walk.Seat (LinkFrame framesOf)
open P1K2 (guards leaveOpened guards_same leaveOpened_is)

theorem openedKeeps_refl (t : S) : OpenedKeeps t t := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The guards. -/
theorem hlv_guards : ∀ s t' s' : S, guards s t' = .ok s' → OpenedKeeps t' s' := fun _ t' _ e => by
  rw [guards_same e]
  exact openedKeeps_refl t'

/-- A row's «opened», between the guards. -/
theorem hlv_opened {built : Array OnBytes.Model.Stages.LinkH} {first : OnBytes.Params.First}
    {W : OnBytes.Model.Verify.Public} {fs : List LinkFrame} {f : LinkFrame} {l : Nat}
    (h : framesOf built first W = .ok fs) (hf : fs[l]? = some f) :
    ∀ s t' s' : S, leaveOpened f s t' = .ok s' → OpenedKeeps t' s' :=
  fun _ _ _ e => opened_keeps h hf (leaveOpened_is e)

/-- "H.1.quiet", then the guards. -/
theorem hlv_head_guards (HP : HeadPar) :
    ∀ s t' s' : S, (headOpenQ HP t').bind (guards s) = .ok s' →
      ∃ Pq u, headOpenQ Pq t' = .ok u ∧ OpenedKeeps u s' := fun s _ s' e => by
  obtain ⟨u, h1, h2⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 e
  exact ⟨HP, u, h1, hlv_guards s u s' h2⟩

/-- "H.1.quiet", then a row's «opened». -/
theorem hlv_head_opened {built : Array OnBytes.Model.Stages.LinkH} {first : OnBytes.Params.First}
    {W : OnBytes.Model.Verify.Public} {fs : List LinkFrame} {f : LinkFrame} {l : Nat}
    (h : framesOf built first W = .ok fs) (hf : fs[l]? = some f) (HP : HeadPar) :
    ∀ s t' s' : S, (headOpenQ HP t').bind (leaveOpened f s) = .ok s' →
      ∃ Pq u, headOpenQ Pq t' = .ok u ∧ OpenedKeeps u s' := fun s _ s' e => by
  obtain ⟨u, h1, h2⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 e
  exact ⟨HP, u, h1, hlv_opened h hf s u s' h2⟩

/-- "F.0.quiet", then the guards. -/
theorem hlv_finish : ∀ s t' s' : S, (finishBehindQ t').bind (guards s) = .ok s' →
    finishBehindQ t' = .ok s' := fun _ _ _ e => by
  obtain ⟨u, h1, h2⟩ := (VerifiableInference.Desc.Except.bind_eq_ok _ _ _).1 e
  rw [guards_same h2]
  exact h1

end VerifiableInference.Desc.First.K2Caller

#print axioms VerifiableInference.Desc.First.K2Caller.openedKeeps_refl
#print axioms VerifiableInference.Desc.First.K2Caller.hlv_guards
#print axioms VerifiableInference.Desc.First.K2Caller.hlv_opened
#print axioms VerifiableInference.Desc.First.K2Caller.hlv_head_guards
#print axioms VerifiableInference.Desc.First.K2Caller.hlv_head_opened
#print axioms VerifiableInference.Desc.First.K2Caller.hlv_finish
