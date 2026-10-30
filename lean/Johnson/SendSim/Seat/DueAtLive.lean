-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/SendSim/Seat/DueAtLive.lean: at all public files at which the library's gate accepts, the
proof file's description and the key file's description each have a due list of challenges, namely
the written list Draws.ofDecl. So the statements of this folder that speak of every due list of
challenges are not vacuous for want of one. It claims no property of the protocol: not hiding, not
zero knowledge.
Terms: Johnson/SendSim/Seat/AtDescLots.lean, paragraph "Terms". Limits of the folder:
Johnson/SendSim/Defs.lean.

What this file has. P is any public files with FlashProve.protocolDataWellFormed (asDescriptionFiles P) = true.
  due_of_live       If the maker ProofFile.onlineDescription returns F at P's files, at OnBytes.secondHashFunction, then
                    (Draws.ofDecl F).due F = true.
  keyDue_of_live    If publicOfO returns X₀ at P's files, at OnBytes.secondHashFunction, and Key.descAt returns
                    Key.descriptionFromSource X N Q at X₀ and the constant Key.fixedDigest, then (Draws.ofDecl
                    (Key.descriptionFromSource X N Q)).due (Key.descriptionFromSource X N Q) = true.

How it fits. Two calls of Draws.ofDecl_due (Johnson/Desc/ProofFile/Honest/Law/DrawsOfDecl.lean),
which holds at every description that has data. That the two descriptions have data where the gate
accepts is part of pseat_name and kseat_name (Johnson/Goal/Description/ProofSeat.lean,
KeySeat.lean). Statements on public data: no distribution is named. Not one of the release's goal
statements.

Limits. Draws.ofDecl is a written list that meets a test of form; it is not challenges that anybody
samples. Every element of it is 1, every matrix entry is 0, and the first chain's last challenge is
the empty one. The positions of a round count up modulo the tree's length, so they repeat where a
round samples more positions than that. Nothing is said on whether an execution can be made ready,
or can be played, at this list. That a verifier's own challenges are due is not said here.
DrawsOfDecl.lean is another folder's file. At the earlier hash function OnBytes.secondHashFunction; the key
file's makers run at a constant in the place of the public files' digest. That the gate accepts at
given files is not proved here.
-/
import Johnson.Desc.ProofFile.Honest.Law.DrawsOfDecl
import Johnson.Goal.Description.ProofSeat
import Johnson.Goal.Description.KeySeat

set_option autoImplicit false

namespace OnBytes.SendSim.Seat
open ProofFile.Honest VerifiableInference VerifiableInference.Desc
open OnBytes.Model.Verify (Public)

/-- **Where the gate accepts, the written list of challenges is due at the proof file's
description.** -/
theorem due_of_live {P : VerifierAndGoals.PublicFiles} (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    {F : FileDescription ProofFile.Inst} (hF : ProofFile.onlineDescription OnBytes.secondHashFunction P.pol P.lay P.KL = .ok F) :
    (Draws.ofDecl F).due F = true := by
  obtain ⟨F', h1, -, h3, -, -⟩ := FlashProve.pseat_name P hL
  obtain rfl : F' = F := Except.ok.inj (h1.symm.trans hF)
  exact Draws.ofDecl_due h3

/-- **Where the gate accepts, the written list of challenges is due at the key file's
description.** -/
theorem keyDue_of_live {P : VerifierAndGoals.PublicFiles} (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles P) = true)
    {X₀ : Public} {X : Key.Source} {N : H2U.PlaceNums} {Q : Key.LaterPlaces}
    (hX : PlanWritten.publicOfO OnBytes.secondHashFunction P.pol P.KL (some P.lay) = .ok X₀)
    (h0 : Key.descAt X₀ P.lay Key.fixedDigest = .ok (Key.descriptionFromSource X N Q)) :
    (Draws.ofDecl (Key.descriptionFromSource X N Q)).due (Key.descriptionFromSource X N Q) = true := by
  obtain ⟨X₀', m, X', N', Q', hX', -, h0', -, -, -, -, hd, -⟩ := FlashProve.kseat_name P hL
  obtain rfl : X₀' = X₀ := Except.ok.inj (hX'.symm.trans hX)
  have e : Key.descriptionFromSource X' N' Q' = Key.descriptionFromSource X N Q := Except.ok.inj (h0'.symm.trans h0)
  rw [← e]
  exact Draws.ofDecl_due hd

end OnBytes.SendSim.Seat

#print axioms OnBytes.SendSim.Seat.due_of_live
#print axioms OnBytes.SendSim.Seat.keyDue_of_live
