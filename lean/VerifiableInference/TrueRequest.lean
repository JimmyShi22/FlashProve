-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
VerifiableInference/TrueRequest.lean: the name `IsTrueRequest` for `Cm.PaperTrue`
(Cm/RelTruePaper.lean), at a table of scales.

One abbreviation.
-/
import Cm.Rel2
import Cm.RelTruePaper

set_option autoImplicit false

/- No default table of scales here: `Scl.ref` (Inst/Model/Scl.lean) is off; each `Scl` is named. -/
attribute [-instance] Inst.Model.Scl.ref

open Inst.Model Cm

namespace VerifiableInference

/-- The request is true at the index (Cm/RelTruePaper.lean: `PaperTrue`): its range is not empty
and lies in the window; the integer program runs on all tokens of the window at the weights; each
checked token is the first choice after the tokens before it; the reply token is the first choice
after the whole window if the range ends at the window's end, and is 0 otherwise. Checked are the
tokens number r + 1 to e (tokens are counted from 0; the window has 1,024; number 1,024 is the reply
token); token r and those before it are not: whoever relies on the verifier's yes compares r and the
tokens up to and including r with what they sent. -/
abbrev IsTrueRequest (s : Scales) (i : Idx) (x : Instance ppref) : Prop :=
  PaperTrue s.kap s.nf i x

end VerifiableInference
