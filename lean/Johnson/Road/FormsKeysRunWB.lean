-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/FormsKeysRunWB.lean: two guards of Johnson/Road/FormsKeysRunW.lean: W5 to W8 and W4 at
the shape hR; W5, W6, W7 and W4 at hR8; 6 column bits.

Runs, no theorems. What the functions compare, what is made up and what is not claimed: that file's
head. They stand apart from that file so that no module costs over a minute of Lean's time. The
program does not import this file.
-/
import Johnson.Road.FormsKeysRunW

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road

open OnBytes.Model (WsShape WsLay WsUnit WsGrp WsFac WsClaim wsLayOf wsGamma wsRowPart wsEpsT
  wsClaimShape wsGammaAdd eqTab eqLow ofInt)
open OnBytes.Model.Layer (Lay Shape Env Reads Scales layout scalesOf readsOf ropeOf ClaimEnv Panels
  panelsA panelsT placePanels callsAC isAcc ropeC)
open Inst.Model (Params)
open Inst.Model.Layout (Kind Coord UnitS units first off rows bits lOf sOf split)

/-! ## The run -/

/- W5, W6, W7, W4, W8 -/
#guard withW hR pcR 6 fun r =>
  w5 r && w6 r && w7 r && w4 placeL false (·.fe) (fun _ _ => true) r && w8 r

/- W5, W6, W7, W4 -/
#guard withW hR8 pcR8 6 fun r => w5 r && w6 r && w7 r && w4 placeL false (·.fe) (fun _ _ => true) r

end OnBytes.Road
