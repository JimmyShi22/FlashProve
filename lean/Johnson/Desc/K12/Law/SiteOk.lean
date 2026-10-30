-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/SiteOk.lean: can the members of a proximity test's group have a seat in the
first stage at the format that their own shapes give? A test that can run at a place and the record
behind the batching. Definitions with code alone; no theorem; no Mathlib beneath it.

The format is `mbOfShape` (Johnson/Desc/K12/Law/ShareNear.lean). The test has the fields of the
library's `Site` (OnBytes/Slice/KeyGroup.lean) at that format, and "the tree is as deep as the
format says".
Why: `words_share`, `answers_of_says`, `decs_of_group` and `few_draws_of_noCand` take "seat : Site s
(mbOfShape codes sh e)". That type is inhabited only where the own fields of `Site` hold at M.C :=
the code at sh.code, M.Z := the code at sh.maskCode, M.a := aOf codes sh (the larger of the two
codes' logarithms, whether or not the shape has rows of that kind). Where a field fails the type is
empty and every theorem on that road is true of nothing there.
Main names:
  `siteL K a m`: six clauses at a member m (`Seat1`: the shape, the tree's shape): site.ha: aOf ≤
    C.a; site.hC: no main row, or the code at sh.code is the stage's main code; site.hM: no main
    row, or aOf = C.a; site.hZ: no mask row, or the code at sh.maskCode is the stage's mask code;
    site.hz: no mask row, or that code's logarithm ≤ aOf; depth: the tree's depth is aOf.
  That the five clauses' yes gives a seat is a definition with its proofs: `siteOf`
    (Johnson/Desc/K12/Law/TieRoad.lean: the library's `Site.byNo` at `mbOfShape`): so the test is no
    transcription. "depth" is read by `depth_of_L` (Johnson/Desc/K12/Law/TieYOf.lean).
  `siteAll`, `siteOk`: over the members that `gpOf`
    (Johnson/Desc/K12/Law/FirstOk.lean) finds at the record t behind the batching.
Limits: no soundness is claimed, and nothing is said on hiding.

-/
import Johnson.Desc.K12.Law.FirstOk
import Johnson.Desc.K12.Law.MeetsOk
import Johnson.Desc.K12.Law.RadNeed

set_option autoImplicit false
namespace H2K.Pin
open OnBytes OnBytes.Params
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.First (Seat1 Plain gpOf)

def codeIs (c : OnBytes.Code) (x : Fmt.M1.Code) : Bool := decide (c = ⟨x.a, x.l, x.r⟩)

def siteL (K : Codes) (a : Fmt.M1.Stage) (m : Seat1) : Clauses :=
  [("site.ha", decide (aOfB K m.sh ≤ a.C.a)),
   ("site.hC", m.sh.mainRows == 0 || codeIs (mainB K m.sh) a.C),
   ("site.hM", m.sh.mainRows == 0 || decide (aOfB K m.sh = a.C.a)),
   ("site.hZ", m.sh.maskRows == 0 || codeIs (maskB K m.sh) a.Z),
   ("site.hz", m.sh.maskRows == 0 || decide ((maskB K m.sh).logN ≤ aOfB K m.sh)),
   ("depth", decide (m.tsh.logN = aOfB K m.sh))]

def plainAt (p : P12) (t : T12) : Option (Fmt.M1.Stage × Plain) :=
  match p.nums.stages, t.pass with
  | a :: _, .claim _ L => (gpOf p t a L).map fun D => (a, D)
  | _, _ => none

def siteAll (p : P12) (t : T12) : Clauses :=
  match plainAt p t with
  | some (a, D) => D.mems.zipIdx.flatMap fun x => tagM x.2 (siteL D.st.codes a x.1)
  | none => [("no stage, no claim, or the plain data cannot be made", false)]

def siteOk (p : P12) (t : T12) : Bool := ok (siteAll p t)

end H2K.Pin
