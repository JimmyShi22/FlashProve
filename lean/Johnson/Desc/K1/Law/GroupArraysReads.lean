-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/GroupArraysReads.lean: a
part cut off Johnson/Desc/K1/Law/GroupArrays.lean by program: the
two members of LaterArrays that want heavy imports (QuietP, joined_yes, quietP_orLoud:
PubAtLaterIndex.lean, which stands above Johnson/Desc/First/PubAll.lean and K1Seat.lean).
  laterArrays_joined   a later sending with a quiet sub-protocol joined behind it.
  laterArrays_k1Reads  the reads' place's joined sub-protocol k1Reads (Johnson/IMR/K1Seat.lean).

What is not claimed. What the first half's head does not claim. Nothing on soundness, on an honest
prover or on hiding.

-/
import Johnson.Desc.K1.Law.GroupArrays
import Johnson.Desc.K1.Law.PubAtLaterIndex

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice _root_.Desc.Plain
open VerifiableInference.Desc.First.Send (joinOwnP joinAll)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Ground (shapesIn)
open OnBytes.Model.Stages (LinkH)

variable {L Cl : Type}

theorem laterArrays_joined (P : Par) (link moment : Nat) (arrays : Option (List Nat)) (nm : String)
    (q : Block S Cl) (hq : QuietP q) :
    LaterArrays P (Block.andThen nm (commitAtS P link moment arrays) q) := by
  intro s s' rs gs h2 h
  obtain ⟨r₁, r₂, rfl⟩ := List.length_eq_two.1 h2
  obtain ⟨s₁, gs₁, rs₂, gs₂, h1, h3⟩ := joined_yes P link moment arrays nm q s s' r₁ r₂ gs h
  rw [(hq _ _ _ _ h3).1]
  exact laterArrays_commitAtS P link moment arrays s s₁ _ gs₁ rfl h1

theorem laterArrays_k1Reads (Z : ProofFile.Pub) (G : ProofFile.Ground) (l : Nat) (X : LinkH) (pr : Nat)
    (reads : Option (List Nat)) :
    LaterArrays (parLater G.first (gpOf Z) l pr 1) (IM.k1Reads Z G l X pr reads) :=
  laterArrays_joined _ _ _ _ _ _ (quietP_orLoud _ _ _ G l X _)

end VerifiableInference.Desc.K1
