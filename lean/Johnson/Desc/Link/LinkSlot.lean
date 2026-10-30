-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Link/LinkSlot.lean: THE ENTRY FILE's DECISION AS A VALUE OF THE THREE PUBLIC FILES
ALONE, IN A FILE OF ITS OWN, OVER THE SEATED TEXT AND THE LIBRARY's TYPES ALONE: so that whoever
seats it in a frame that runs imports NO LAW on it (a value that runs should not import
its own soundness).
  decOfRoot pol lay KL   where the root linkOfFilesV makes a link L: the run of L's description at
  the two keys written of the two records (keysOfX … (recX rr)); WHERE THE ROOT REFUSES: the
  decision that says no to all.
It is VerifiableInference.OnPublicFiles.decOfRootV (Johnson/Goal/Conditions/EntryAtSlotV.lean) with
decOfXFull written out: that the two are one is a theorem by cases and rfl:
Johnson/Goal/Conditions/EntryAtSlotEq.lean. Neither of these two files is in this library.
VerifierAndGoals.theDescription does not run this value: its decision on the entry file is linkDecisionAtParameterFile
(Johnson/Desc/Link/LinkWritten.lean).
A definition alone. Nothing on soundness, on an honest prover or on hiding. THE FULL SIZE ALONE.

-/
import Johnson.Desc.Link.LinkOfFiles
import OnBytes.Flat.EntryTerm
import OnBytes.Flat.LinkSib

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open OnBytes OnBytes.Flat OnBytes.Slice TypedOracleCompiler.Slice _root_.Run

/-- **The entry file's decision, of the three public files alone.** -/
def decOfRoot (pol lay KL : ByteArray) : RecFull × RecFull → PQ.View → Bool :=
  match linkOfFilesV pol lay KL with
  | .ok L => fun rr V => L.F.run (keysOfX frS.P.v 29 1 (anT frS.P.v 1) (recX rr)) V
  | .error _ => fun _ _ => false

end Desc.K15
