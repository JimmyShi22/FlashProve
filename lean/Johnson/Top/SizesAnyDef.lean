-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/SizesAnyDef.lean: the ten sizes off a parameter file, whatever its acceptance policy,
and the test "they are the reference's" without a clause on the policy: the two definitions.

They stand in a file of their own so that whoever names them imports little. What they name: the
scan of a parameter file (polScan, OnBytes/Model/Config.lean), the sizes of a scan (sizesOf,
Johnson/Flat/Instance.lean) and the reference parameters (ppref, Inst/Model/Program.lean). The
one import is Johnson/Flat/Instance.lean. The laws on the two definitions, and the control that
ties them to sizesAt and sizesRefB: Johnson/Top/SizesAny.lean.

Definitions and one theorem.
  sizesAny policy: the sizes of the program's own scan of the file. Its value depends on none of the
    policy's lines (C, theta, cap, s, sh, sT, F); the scan still refuses a file where one of them is
    missing, misnamed, misspelt or at least 2^32.
  sizesAny_scan: where the scan returns S, sizesAny returns the sizes of S.
  sizesAnyRefB policy: sizesAny returns, and the ten numbers (window, vocabulary, layers, width,
    query heads, key heads, a head's width, the two inner widths, experts) are the reference's.

Limits: nothing on a file is evaluated here (runs: Johnson/Top/SizesAnyRun.lean). The test compares
ten sizes and the value of no other line of the parameter file: IT TELLS NOTHING OF THE ACCEPTANCE
POLICY: WHOEVER NEEDS THE POLICY MUST READ IT ELSEWHERE. THAT A FILE PASSES IT SAYS NOTHING OF WHAT
A PROOF UNDER THE FILE's POLICY MEANS: the claims of Johnson/Flat/Claims.lean and
Johnson/Flat/LedgerClaim.lean are those of exact match alone.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Flat.Instance

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.Flat

open Inst.Model OnBytes OnBytes.Flat

/-- The sizes, off the parameter file's bytes, whatever its acceptance policy. Refused where the
program's scan refuses the file. -/
def sizesAny (policy : ByteArray) : Except String Params := do
  let P ← Model.polScan policy
  pure (sizesOf P.h)

/-- Where the scan returns S, sizesAny returns the sizes of S. -/
theorem sizesAny_scan {policy : ByteArray} {S : Model.PolScan}
    (h : Model.polScan policy = .ok S) : sizesAny policy = .ok (sizesOf S.h) := by
  unfold sizesAny
  rw [h]
  rfl

/-- The ten sizes are the reference's. The value of no line of the acceptance policy is compared. -/
def sizesAnyRefB (policy : ByteArray) : Bool :=
  match sizesAny policy with
  | .ok P => P.T == ppref.T && P.V == ppref.V && P.layers == ppref.layers && P.d == ppref.d &&
      P.nq == ppref.nq && P.nkv == ppref.nkv && P.ch == ppref.ch && P.f == ppref.f &&
      P.fe == ppref.fe && P.nexp == ppref.nexp
  | .error _ => false

end VerifiableInference.OnPublicFiles.Flat
