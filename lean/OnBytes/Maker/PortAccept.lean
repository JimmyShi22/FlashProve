-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/PortAccept.lean: the runs of a key file's and of a proof file's reduction
(OnBytes/Maker/Files.lean), by name.

Main definitions.
  `keyRun`, `proofRun`: the tests on the words of the key's seeds and of three views, and the
    program's own decision on these views (`decideKey`, `decideProof`, OnBytes/Maker/Decide3.lean),
    under the verdict of the tests on the rounds.

What is not claimed. Nothing on what a run says. Nothing on soundness.


-/
import OnBytes.Maker.OfThreeChains

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Compile _root_.Run _root_.Run.PQ
open OnBytes.Params (Rounds)

/-! ## The decision at the typed string -/

/-- The run of a key file's reduction (`keyIORAt`, OnBytes/Maker/Files.lean). -/
abbrev keyRun {R : Type} (W : Three.Whole) (ok : Bool) (key : R → TableKey) (k : Params.KeyChains) :
    R → View → View → View → Bool :=
  fun rec v₁ v₂ v₃ => ok && decideKey k (key rec) W.t₁ W.t₂ v₁ v₂ v₃

/-- The run of a proof file's reduction (`proofIORAt`). -/
abbrev proofRun {X R : Type} (W : Three.Whole) (ok : Bool) (key : R → TableKey)
    (c : Params.ProofChains) (block : X → Blk Proof.FirstEnd) :
    X × R → View → View → View → Bool :=
  fun z v₁ v₂ v₃ => ok && decideProof c (key z.2) (block z.1) W.t₁ W.t₂ v₁ v₂ v₃

end OnBytes.Maker
