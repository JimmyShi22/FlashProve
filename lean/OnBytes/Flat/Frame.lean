-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/Frame.lean: three protocols, one for each file of the prover, over a configuration with
a record.

One structure. No protocol occurs here. `Files C` holds, for a configuration C (Hiop/RecConf.lean):
the key file's protocol, on a record, over the encoded index; the entry file's, on two records, over
two encoded indices; the proof file's, on an instance and a record, over the encoded index
(`Iop.InteractiveOracleProof`: its rounds, the positions that its verifier reads, its decision). Beside them: the
number of slots of a batch; for each file marks on its rounds (which stand in a chain that is
shared); which part of an instance is fixed before the proof file's first round, and behind which
round the rest is named.

Limits: that the three protocols are those of any program is not said here.
Terms: lean/GLOSSARY.md.

-/
import Hiop.RecConf
import Iop.Batch

set_option autoImplicit false

namespace OnBytes.Flat
open Iop Hiop

/-- The three files' protocols. -/
structure Files (C : ConfigurationWithOutOfDomainSample) where
  /-- the key file: on a record, over the encoded index -/
  key   : InteractiveOracleProof C.Rec C.E0
  /-- the entry file: on two records, over two encoded indices -/
  entry : InteractiveOracleProof (C.Rec × C.Rec) (twoExternalStrings C.n C.Sg)
  /-- the proof file: on an instance and a record, over the encoded index -/
  proof : InteractiveOracleProof (C.X × C.Rec) C.E0
  /-- the number of slots -/
  N     : ℕ
  /-- which rounds of the key file stand in its shared chain -/
  annT  : RoundSplits key.shape
  /-- the same for the entry file -/
  annL  : RoundSplits entry.shape
  /-- which rounds of the proof file are shared by a batch -/
  ann   : RoundSplits proof.shape
  /-- the part of an instance that is fixed before the proof file's first round -/
  early : C.X → C.X
  /-- the round of the proof file behind which the rest of the instance is named, if there is one -/
  late  : Option ℕ

end OnBytes.Flat
