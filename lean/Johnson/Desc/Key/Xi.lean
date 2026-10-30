-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Key/Xi.lean: the instance of a key file's description: what the description speaks
about beside the public parameters. One structure.

Main names.
  `Xi`: a record with one field, what a verifier knows of the stored table besides its shape
    (`OnBytes.TableKey`, OnBytes/Iop/Foldeq.lean).

Limits. A type alone: no test and no theorem. Whether a table's key fits a shape is
`TableKey.fits`, which nothing here asks. Nothing on soundness.

-/
import OnBytes.Iop.Foldeq

namespace VerifiableInference.Desc.Key

open OnBytes

/-- The instance of a key file's description. -/
structure Xi where
  /-- what a verifier knows of the stored table besides its shape -/
  key : TableKey

end VerifiableInference.Desc.Key
