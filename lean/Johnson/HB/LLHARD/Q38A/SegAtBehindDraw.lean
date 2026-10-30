-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HB/LLHARD/Q38A/SegAtBehindDraw.lean: behind the approximate range proof's draw the open
segment's part is there, with the open segment's context (the structure `LinkCtx`) and the statement
of oracle messages as they were in front.

  `segAt_behind_draw`: from `Drawn s t` (Johnson/Desc/First/K8/TieRides.lean: the draw's one
    writing) and `s.link? = some L`: some a with `K9.segAt? t = some a`, `a.L = L` and `a.d.st =
    s.st`. By `fork_of_link` and the four lemmas on what that writing leaves (`putTl_link`,
    `putTl_fork`, `putTl_tl`, `putTl_rest`, Johnson/Desc/First/K8/LawAtS.lean), at the reader's own
    text (Johnson/Desc/First/Batch/FormsIn.lean).

Limits. General: no public file, no written value, no head of conditions is read. Nothing on
soundness.
-/
import Johnson.HB.LLHARD.Q38A.ForkOfLink
import Johnson.Desc.First.K8.TieRides
import Johnson.Desc.First.K8.LawAtS
import Johnson.Desc.First.Batch.FormsIn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Q38
open OnBytes OnBytes.Model
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K8 (Drawn putTl_link putTl_fork putTl_tl putTl_rest)

/-- **Behind the draw the open segment's part is there.** -/
theorem segAt_behind_draw {s t : S} {L : LinkCtx} (hd : Drawn s t) (hL : s.link? = some L) :
    ∃ a, K9.segAt? t = some a ∧ a.L = L ∧ a.d.st = s.st := by
  obtain ⟨tl, mm, f, ht, rfl⟩ := hd
  obtain ⟨F, hF⟩ := fork_of_link s L hL
  unfold K9.segAt?
  rw [putTl_link, putTl_fork, hL, hF, putTl_tl s tl _ ht]
  exact ⟨_, rfl, rfl, (putTl_rest s _).1⟩

end Q38

#print axioms Q38.segAt_behind_draw
