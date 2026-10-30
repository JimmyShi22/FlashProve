-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/HonestTrace/Run/SetUpTurnDefs.lean

Records of the verifier's public part with the free numbers of the parameter file set to other
values ("turned"). Definitions alone; no theorem. The eight free numbers are the fields of the
library's "VerifierAndGoals.FreeLines" (Ladder/Stored.lean): eps1, eps2, epsF, MF, KF, C, theta, cap.

Main definitions (namespace "HonestTraceRun.SetUp"):
* "hdrTurn": the record of the value lines with the eight free numbers set.
* "scanTurn": a strict scan ("PolScan") with another list of values and its record turned.
* "layTurn": the layers' layout with the three free numbers of its shape set: eps1, eps2, epsF.
* "pubTurn": the layers' record with the layout turned, other scales and another rotary table.
* "Alike": what two plans of attention share: seam, ns, own, the forest's size and S.Tt.

Limits. Nothing is proved here: that the scan or the layout of other files is such a record is
the matter of Johnson/HonestTrace/Run/SetUpScan.lean and Johnson/HonestTrace/Run/SetUpTurn.lean.

Not claimed: any property of a release, of a verifier or of a prover.
-/
import Johnson.Goal.Meaning.ScopeScanTies
import OnBytes.Model.VerifyPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HonestTraceRun

namespace SetUp

open OnBytes OnBytes.Model OnBytes.Model.Verify
open VerifierAndGoals (FreeLines)

/-- The record of the value lines with the eight free numbers set. -/
def hdrTurn (h : Hdr) (v : FreeLines) : Hdr :=
  { h with eps := #[v.eps1, v.eps2], MF := v.MF, KF := v.KF, epsF := v.epsF, clipC := v.C,
           theta := v.theta, cap := v.cap }

/-- A strict scan with another list of values and the eight free numbers set in its record. -/
def scanTurn (P : PolScan) (vals : List (String × Nat)) (v : FreeLines) : PolScan :=
  { P with values := vals, h := hdrTurn P.h v }

/-- The layers' layout with the three free numbers of its shape set. -/
def layTurn (y : Layer.Lay) (v : FreeLines) : Layer.Lay :=
  { y with h := { y.h with eps1 := v.eps1, eps2 := v.eps2, epsF := v.epsF } }

/-- The layers' record with the layout turned, and other scales and another rotary table. -/
def pubTurn (L : Layer.Pub) (v : FreeLines) (sc : Layer.Scales) (rope : Array Nat) : Layer.Pub :=
  { L with y := layTurn L.y v, sc := sc, rope := rope }

/-- What group_turn keeps of a group's plan. -/
def Alike (a a₀ : Attention.Plan) : Prop :=
  a.seam = a₀.seam ∧ a.ns = a₀.ns ∧ a.own = a₀.own ∧
    OnBytes.Model.forestSize a.fs = OnBytes.Model.forestSize a₀.fs ∧ a.S.Tt = a₀.S.Tt

end SetUp

end HonestTraceRun
