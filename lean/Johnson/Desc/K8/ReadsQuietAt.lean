-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K8/ReadsQuietAt.lean: at which link which of the two blocks of
Johnson/Desc/K8/ReadsQuiet.lean stands, with its parameters, of public values alone.

This file holds definitions only; no theorem is stated.

Main names (namespace VerifiableInference.Desc.K8.ReadsQuiet):
  blockAt G hS HLy H kinds l: the block at link number l. G, hS, HLy, H: the layers' sub-proofs'
    plans, one a group of layers; the head's numbers, layout and plan: what the verifier makes of
    the public files (Model.Verify.Public's fields of these names). kinds: for each link its kind
    (0 a layers' link, 1 an attention link, 2 the head's) and its group of layers. Nothing at an
    attention link, whose form of the step is another file's, and where there is no such link or
    plan.
  behind own q: the step laid behind the block of the place's steps with rounds, by Block.andThen,
    under that block's name and place.

The place. The step takes no round and stands at the place of the reads' sending: piece 4 of a
layers' link, piece 5 of the head's. A place has one block: so this one is not seated by itself: it
is laid behind the sending's block (behind).

What is not claimed. Nothing on soundness, on an honest prover or on hiding.

-/
import Johnson.Desc.K8.ReadsQuiet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K8.ReadsQuiet
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block)
open VerifiableInference.Desc.First (S)

/-- The block at link number l. -/
def blockAt (G : Array Layer.HPlan2) (hS : Head.Shape) (HLy : Head.HL) (H : Head.HPlanH2)
    (kinds : List (Nat × Nat)) (l : Nat) : Option (Block S Unit) :=
  (kinds[l]?).bind fun k =>
    if k.1 == 0 then (G[k.2]?).map fun hp => layers ⟨⟨1, some l, 4, .K1⟩, hp.tl⟩
    else if k.1 == 2 then some (head ⟨⟨1, some l, 5, .K1⟩, hS, HLy, H⟩)
    else none

/-- The step laid behind the block of the place's steps with rounds. -/
def behind (own q : Block S Unit) : Block S Unit := own.andThen own.name q

end VerifiableInference.Desc.K8.ReadsQuiet
