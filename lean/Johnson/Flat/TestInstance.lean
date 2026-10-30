-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Flat/TestInstance.lean: the model's sizes at copies of two parameter files, and instances
built from tokens at made-up sizes.

The copies: of a small example's parameter file (prover/examples/target_small_f2_roomy), as
OnBytes/Model/TestRecordWork.lean composes it (its `smallHead`, then the later lines of
OnBytes/Params/SmallFiles.lean); and of the full-size example's
(prover/examples/target_full_f2), as OnBytes/Tie/Pv/Plan/PlanKits.lean writes out its lines
(`policyF`).

The instances are built at made-up sizes, a window of four tokens and a vocabulary of ten (`tiny`):
no parameter file that the scan admits has so short a window.

Where each expected number comes from. The sizes: the files' own lines (small: lt 6, V 512, L 8, d
512, H 4, G 2, dh 128, f 1024, fe 512, NE 4); at the full size the library's reference numbers
`Inst.Model.ppref`. The instances: reckoned by hand from the docstring of `requestAt`. The refusals
of a file whose policy is not exact match: `Model.exactMatch` (OnBytes/Model/Config.lean) says which
lines are exact match.

What is not tested: that the copies are the files. Each test is checked when the file compiles, by
Lean's evaluator. The file is no part of the program.

-/
import Johnson.Flat.Instance
import OnBytes.Model.TestRecordWork
import OnBytes.Tie.Pv.Plan.PlanKits

set_option autoImplicit false

namespace OnBytes.Flat.TestInstance

open Inst.Model OnBytes.Model.Verify.TestRecordWork

/-- The ten sizes of a value. -/
def ten (P : Params) : List Nat := [P.T, P.V, P.layers, P.d, P.nq, P.nkv, P.ch, P.f, P.fe, P.nexp]

/-- The small example's parameter file. -/
def smallPolicy : ByteArray := policyOf smallHead

/-- The full-size example's parameter file. -/
def fullPolicy : ByteArray := Tie.Pv.Plan.textOf Tie.Pv.Plan.policyF

#guard (sizesAt smallPolicy).toOption.map ten == some [64, 512, 8, 512, 4, 2, 128, 1024, 512, 4]
#guard (sizesAt fullPolicy).toOption.map ten == some (ten ppref)

/-- The parameter file with one line put in the place of another. -/
def turned (policy : ByteArray) (line other : String) : ByteArray :=
  ((String.fromUTF8! policy).replace ("\n" ++ line ++ "\n") ("\n" ++ other ++ "\n")).toUTF8

/-- The name under which `sizesAt` refuses; the empty string if it does not. -/
def why (policy : ByteArray) : String :=
  match sizesAt policy with
  | .ok _ => ""
  | .error name => name

-- both copies have the lines of exact match: C = theta = 256 = 2 ^ sh, cap 0, sT = sh - 4
#guard why smallPolicy == "" && why fullPolicy == ""
-- A FILE WHOSE ACCEPTANCE POLICY IS NOT EXACT MATCH IS REFUSED, by the test on the policy and not
-- by the scan: one token may cost more than the clip (cap 1); a threshold below 2 ^ sh (theta 255),
-- which no request meets; a clip above the threshold (C 300)
#guard why (turned smallPolicy "cap 0" "cap 1") == "policy-not-exact-match"
#guard why (turned fullPolicy "cap 0" "cap 1") == "policy-not-exact-match"
#guard why (turned smallPolicy "theta 256" "theta 255") == "policy-not-exact-match"
#guard why (turned fullPolicy "C 256" "C 300") == "policy-not-exact-match"

/-- What a built instance says: the window's first tokens, y, r, e. -/
def told {P : Params} (n : Nat) (x : Instance' P) : List Nat × Nat × Nat × Nat :=
  (((requestWordsOf x).toList.take n).map (·.toNat), x.y.val, x.r, x.e)

/-- The sizes with a window of four tokens and a vocabulary of ten. -/
def tiny : Params := { ppref with T := 4, V := 10 }

-- a prompt of two tokens, one output token, padding: r = 1, e = 2, y = 0
#guard (buildOf tiny ([7, 8], [9]) [5]).map (told 4) == some ([7, 8, 9, 5], 0, 1, 2)
-- five tokens in all: the last output token is y, and e is the window's length
#guard (buildOf tiny ([7, 8], [9, 1, 2]) []).map (told 4) == some ([7, 8, 9, 1], 2, 1, 4)
-- the words of the two files: the window, r, e; y
#guard (buildOf tiny ([7, 8], [9, 1, 2]) []).map
    (fun x => ((requestWordsOf x).toList.map (·.toNat), (replyWordsOf x).toList.map (·.toNat))) ==
  some ([7, 8, 9, 1, 1, 4], [2])
-- the program's reader takes these words, and reads r, e, y off them
#guard (buildOf tiny ([7, 8], [9, 1, 2]) []).any fun x =>
  match Model.Head.stFromCall (requestWordsOf x) (replyWordsOf x) tiny.T with
  | .ok s => s.r == x.r && s.e == x.e && s.y == x.y.val && s.req == requestWordsOf x
  | .error _ => false
-- the same where e is before the window's end and y is 0
#guard (buildOf tiny ([7, 8], [9]) [5]).any fun x =>
  match Model.Head.stFromCall (requestWordsOf x) (replyWordsOf x) tiny.T with
  | .ok s => s.r == x.r && s.e == x.e && s.y == 0 && s.req == requestWordsOf x
  | .error _ => false
-- refused: no prompt; no output; six tokens; a token outside the vocabulary
#guard (buildOf tiny ([], [9]) []).isNone && (buildOf tiny ([7], []) []).isNone &&
  (buildOf tiny ([7, 8, 9], [1, 2, 3]) []).isNone && (buildOf tiny ([10], [1]) []).isNone

end OnBytes.Flat.TestInstance
