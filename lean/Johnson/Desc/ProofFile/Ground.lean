-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Ground.lean: the values of which a lot's blocks are functions, as one record.
A definition only.

-/
import Johnson.Skeleton.Start

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile
open OnBytes OnBytes.Model OnBytes.Model.Stages

/-- `built`, `first` and `W` are computed from the public files alone. `cov`, the head's covered
positions, holds the request's tokens: a lot with `letters := false` (ProofFile/LotCore.lean) is
evaluated at the `cov` of a request of zeros, and the type does not stop its blocks from reading
it. -/
structure Ground where
  built : Array LinkH
  first : Params.First
  W : Verify.Public
  cov : Head.Covered

end ProofFile
