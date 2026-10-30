-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/TrueAtPub.lean: the first record of true tables at a public record Pub34, on true
reads.

  `trueAt_pub`: TrueAt at the record's environment, at the point of the lookup's tables and the
    token part of the lookup's point. It is the first clause of worlds_of_holds
    (Johnson/Road/FormsKeysRef.lean) at the record's own fields; truths_of_pub34
    (Johnson/Road/K4/TruthsOfPub.lean) has the second, third and fourth records.
Limits. ReadsTrue (every table of the reads holds what it says of the matrices Mm in the world Wo)
is a premise. Nothing on a draw, on soundness or on hiding.


-/
import Johnson.Road.K4.TruthsOfPub

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes.Model (World)
open Inst.Model (Scl)

variable {K : Type} [Field K]

/-- **The first record of true tables at a record Pub34, on true reads.** -/
theorem trueAt_pub (X : Rows.Pub34 K) (Wo : World K) (Mm : Mats K) (hRd : X.ReadsTrue Wo Mm) :
    TrueAt X.ρ Wo X.p.v X.h.lt (cellsAt X.p.v.y Mm) (pt X.ρ X.Zp) (pt X.ρ X.H.ztF) := by
  letI : Scl := sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam
  exact (worlds_of_holds X.ρ Wo X.hy X.S X.hg X.hrd X.hl X.ht X.Z X.hZ X.hzt X.h4 X.hcrt X.htm
    X.hNM X.hpts X.hfun X.hT Mm hRd).1

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.trueAt_pub
