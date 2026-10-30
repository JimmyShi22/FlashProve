-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/KeyLaw/Takes.lean: how many mask entries a key file's lookups take together
of the own message and of the index-mask message. Definitions, on public numbers alone.

Main names:
  takesO id m ls: of the own message: for each lookup its face's slots less two for each part.
  takesK id m ls: of the index-mask message: two for each part.
  RoomFor x m codes idx: what all lookups take fits: at most (mask rows) * 2 ^ (the mask code's
    logEll), at both messages; and both have a mask row.

-/
import Johnson.Desc.First.Look.K3Key
import OnBytes.Iop.Wf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K3.KeyLaw
open OnBytes OnBytes.Params

/-- What the lookups take together of the own message's mask entries. -/
def takesO (id : Nat) (m : Wf.Matrix) (ls : List WfLookup) : Nat :=
  (ls.map fun l => (faceOfLkp (Wf.lookupOf id m l)).slots -
    2 * (faceOfLkp (Wf.lookupOf id m l)).parts.length).sum

/-- What they take together of the index-mask message's. -/
def takesK (id : Nat) (m : Wf.Matrix) (ls : List WfLookup) : Nat :=
  (ls.map fun l => 2 * (faceOfLkp (Wf.lookupOf id m l)).parts.length).sum

/-- What all lookups take fits the two messages' mask rows. -/
def RoomFor (x : WfPublic) (m : Wf.Matrix) (codes : Codes) (idx : OracleShape) : Prop :=
  0 < x.message.shape.maskRows ∧ 0 < idx.maskRows ∧
    takesO x.messageId m x.lookups ≤ x.message.shape.maskRows *
      2 ^ (codes.mask.getD x.message.shape.maskCode default).logEll ∧
    takesK x.messageId m x.lookups ≤
      idx.maskRows * 2 ^ (codes.mask.getD idx.maskCode default).logEll

instance (x : WfPublic) (m : Wf.Matrix) (codes : Codes) (idx : OracleShape) :
    Decidable (RoomFor x m codes idx) := by
  unfold RoomFor
  infer_instance

end VerifiableInference.Desc.K3.KeyLaw
