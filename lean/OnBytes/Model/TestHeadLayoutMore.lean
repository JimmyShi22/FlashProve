-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestHeadLayoutMore.lean: further tests of OnBytes/Model/HeadLayout.lean: the refusals,
each under its name.

A test that expects a refusal changes one thing in an accepted input. The accepted input is beside
it or in OnBytes/Model/TestHeadLayout.lean, whose numbers are used here. The expected name is that
of the first condition that fails in the C++ counterpart of the function called
(verifier/src/cp_verify.cpp: the routine h9 and the head's part of runStage; stFromCall). It was
worked out from the source: no C++ program was run on these cases. cp_verify as a whole refuses some
of these inputs earlier, under another name: toksrc other than 1 (statement-required), and with five
limbs epsF from 2^48 on (no-wrap-ledger-eps).

`h9` is called directly, because `layout` reaches few of its cases: `policy` and `admitted` refuse
most of the numbers, and `layout` passes one bound on a cell, `cellBound`. C and cap from 2^32 on do
not fit the 32-bit fields of cp_verify: there the expected name is that of the C++ condition read on
integers.

No input can show these, so they are not tried. no-wrap-H-E4: its sum is at most that of E2, which
comes first. The second condition under no-wrap-H-three-digits: for sh (digSh) up to 8 the first
implies it, and from 9 on W-HD0 fails before it. A width d that fails the first by its clause on d
fails the second too, so the guard at d = 2^13 does not tell the two apart. The first clause of
guard-radix: the second implies it. MF > 47 under policy-norm-F: see there. forest-depth-H,
internal-table-FE and internal-forest-place: earlier tests of `layout` exclude them. So four names
(no-wrap-H-E4 and these three) are expected nowhere. This file and
OnBytes/Model/TestHeadLayout.lean expect the other 25 of the 29 names in `Layout.names`.

Where a name has several causes, not every cause is tried: of policy-gap-words,
shape-request-matrix-H, shape-call-H and internal-head-shape only what that file tries, and cap > T
here. The program does not import this file.
-/
import OnBytes.Model.TestHeadLayout

namespace OnBytes.Model.Head

/-- The name of a refusal, or the empty string. -/
def nameOf {α : Type} (x : Except String α) : String :=
  match x with
  | .ok _ => ""
  | .error e => e

/-! ## The no-overflow conditions

`h9` reads one number of the layout, JV. -/

/-- The layout as far as `h9` reads it. -/
def onlyJV (JV : Nat := 512) : HL := { JV := JV }

#guard nameOf (h9 smallShape onlyJV cellBound) == ""
-- U-NF: 2^16 2^KF is at most 2^60
#guard nameOf (h9 { smallShape with KF := 44 } onlyJV cellBound) == ""
#guard nameOf (h9 { smallShape with KF := 45 } onlyJV cellBound) == "no-wrap-H-U-NF"
-- W-NF: by MF, and by the bound on a cell
#guard nameOf (h9 { smallShape with MF := 59 } onlyJV cellBound) == ""
#guard nameOf (h9 { smallShape with MF := 60 } onlyJV cellBound) == "no-wrap-H-W-NF"
#guard nameOf (h9 smallShape onlyJV (2 ^ 40)) == "no-wrap-H-W-NF"
-- W-HD0: its first condition by sh, its second by the width d
#guard nameOf (h9 { smallShape with digSh := 9 } onlyJV cellBound) == "no-wrap-H-W-HD0"
#guard nameOf (h9 { smallShape with d := 2 ^ 36 } onlyJV cellBound) == "no-wrap-H-W-HD0"
-- three-digits, the first condition: its clause on d (SH at most 2^37), then its clause on sh
#guard nameOf (h9 { smallShape with d := 2 ^ 13 - 1 } onlyJV cellBound) == ""
#guard nameOf (h9 { smallShape with d := 2 ^ 13 } onlyJV cellBound) == "no-wrap-H-three-digits"
#guard nameOf (h9 { smallShape with digSh := 7 } onlyJV cellBound) == ""
#guard nameOf (h9 { smallShape with digSh := 6 } onlyJV cellBound) == "no-wrap-H-three-digits"
-- the clause on sh at its edge in d
#guard nameOf (h9 { smallShape with digSh := 7, d := 7936 } onlyJV cellBound) == ""
#guard nameOf (h9 { smallShape with digSh := 7, d := 7937 } onlyJV cellBound) ==
  "no-wrap-H-three-digits"
-- HE: by the scale of the table, and by the bound on a cell
#guard nameOf (h9 { smallShape with famF := 43 } onlyJV cellBound) == ""
#guard nameOf (h9 { smallShape with famF := 44 } onlyJV cellBound) == "no-wrap-H-HE"
#guard nameOf (h9 smallShape onlyJV (2 ^ 28)) == "no-wrap-H-HE"
-- Z: by JV
#guard nameOf (h9 smallShape (onlyJV (2 ^ 35)) cellBound) == ""
#guard nameOf (h9 smallShape (onlyJV (2 ^ 36)) cellBound) == "no-wrap-H-Z"
-- E2 by the clip, E3 by cap
#guard nameOf (h9 { smallShape with clipC := 2 ^ 45 } onlyJV cellBound) == ""
#guard nameOf (h9 { smallShape with clipC := 2 ^ 46 } onlyJV cellBound) == "no-wrap-H-E2"
#guard nameOf (h9 { smallShape with cap := 2 ^ 59 } onlyJV cellBound) == ""
#guard nameOf (h9 { smallShape with cap := 2 ^ 60 } onlyJV cellBound) == "no-wrap-H-E3"
-- guard-radix, the last condition, by the bound on a cell; J-E, before it, from 267378689 on
#guard nameOf (h9 smallShape onlyJV (2 ^ 19)) == ""
#guard nameOf (h9 smallShape onlyJV (2 ^ 20)) == "no-wrap-H-guard-radix"
#guard nameOf (h9 smallShape onlyJV 267378688) == "no-wrap-H-guard-radix"
#guard nameOf (h9 smallShape onlyJV 267378689) == "no-wrap-H-J-E"
-- with four limbs J-E holds there
#guard nameOf (h9 { smallShape with XL := 4 } onlyJV 267378689) == "no-wrap-H-guard-radix"
-- `layout` runs `h9`
#guard nameOf (layout { smallShape with d := 2 ^ 13 - 4, lPd := 13, iotaH := [1, 0, 0, 0, 0, 0] }
    someTable) == ""
#guard nameOf (layout { smallShape with d := 2 ^ 13, lPd := 13, iotaH := [1, 0, 0, 0, 0, 0] }
    someTable) == "no-wrap-H-three-digits"

/-! ## The lines of the parameter file -/

#guard nameOf (policy smallShape) == ""
#guard nameOf (policy { smallShape with toksrc := 0 }) == "policy-toksrc"
-- policy-norm-F: each clause alone, at its edge, but MF > 47. With KF at most 32, KF + 14 < MF
-- refuses from MF = 47 on (the two guards at KF = 32), and a larger KF has the same name
#guard nameOf (policy { smallShape with MF := 24 }) == ""
#guard nameOf (policy { smallShape with MF := 23 }) == "policy-norm-F"
#guard nameOf (policy { smallShape with MF := 45 }) == "policy-norm-F"
#guard nameOf (policy { smallShape with MF := 46, KF := 32 }) == ""
#guard nameOf (policy { smallShape with MF := 47, KF := 32 }) == "policy-norm-F"
#guard nameOf (policy { smallShape with MF := 24, KF := 17 }) == ""
#guard nameOf (policy { smallShape with MF := 24, KF := 16 }) == "policy-norm-F"
#guard nameOf (policy { smallShape with KF := 33 }) == "policy-norm-F"
#guard nameOf (policy { smallShape with epsF := 0 }) == "policy-norm-F"
#guard nameOf (policy { smallShape with epsF := 2 ^ 59 - 1 }) == ""
#guard nameOf (policy { smallShape with epsF := 2 ^ 59 }) == "policy-norm-F"
-- policy-gap-words: cap is at most T = 64
#guard nameOf (policy { smallShape with cap := 64 }) == ""
#guard nameOf (policy { smallShape with cap := 65 }) == "policy-gap-words"

/-- The name with which the list of calls is refused, or nothing. -/
def callsName (lines : List (List String)) : String :=
  nameOf ((numbers smallShape).bind fun L => callsOf { smallShape with polCallsH := lines } L)

/-- The example's list of calls with line number i replaced. -/
def withLine (i : Nat) (line : List String) : List (List String) := smallShape.polCallsH.set i line

/-- Five calls: all four segments of the kind R16 in one. -/
def fiveCalls : List (List String) :=
  [["R16", "R16", "NF", "NFH", "HD0", "HD1"], ["R8", "R8", "ROW", "HD2"], ["FEa", "FE", "HE0"],
    ["FEb", "FE", "HE1"], ["FC", "FC", "CNF"]]

-- policy-call-list-H has one name for all its causes; each list below breaks one rule only
#guard callsName smallShape.polCallsH == ""
#guard callsName fiveCalls == ""
-- no line callH: the default list applies
#guard callsName [] == ""
-- seven lines; a line of two words; a name twice
#guard callsName ([["R16a", "R16", "NF", "NFH"], ["R16c", "R16", "HD0"]] ++
    smallShape.polCallsH.drop 1) == "policy-call-list-H"
#guard callsName (fiveCalls ++ [["X", "R8"]]) == "policy-call-list-H"
#guard callsName (withLine 1 ["R16a", "R16", "HD1"]) == "policy-call-list-H"
-- a name that is no segment's; a segment twice; a segment of another kind; a segment in no line
#guard callsName (withLine 1 ["R16b", "R16", "HD1", "HDX"]) == "policy-call-list-H"
#guard callsName (withLine 1 ["R16b", "R16", "HD1", "HD0"]) == "policy-call-list-H"
#guard callsName (withLine 1 ["R16b", "R8", "HD1"]) == "policy-call-list-H"
#guard callsName (smallShape.polCallsH.take 5) == "policy-call-list-H"

-- a line iotaH other than 0 where there is no call
#guard nameOf (layout { smallShape with polCallsH := fiveCalls } someTable) == ""
#guard nameOf (layout { smallShape with polCallsH := fiveCalls, iotaH := [0, 0, 0, 0, 0, 1] }
    someTable) == "header-absent-call-H"

/-! ## The request -/

-- a covered stretch that ends before the last position, with the reply 0
#guard nameOf (stFromCall (someRequest 62 63) #[0] 64) == ""
-- a request a word too short or too long; a reply of two words; no reply. Too long shows the test
-- on the length; too short would be refused by r < e as well
#guard nameOf (stFromCall (someRequest 63 64).pop #[342] 64) == "statement-range"
#guard nameOf (stFromCall ((someRequest 63 64).push 0) #[342] 64) == "statement-range"
#guard nameOf (stFromCall (someRequest 63 64) #[342, 0] 64) == "statement-range"
#guard nameOf (stFromCall (someRequest 63 64) #[] 64) == "statement-required"

/-- What the verifier keeps of the request with r = 61 and e = 64 and the reply 342. -/
def kept : StOwn := { req := someRequest 61 64, r := 61, e := 64, y := 342 }

#guard nameOf (coveredOf kept 64 512) == ""
-- a token that is no entry of the vocabulary, at a position that is not covered and at a covered
-- one; the reply
#guard nameOf (coveredOf { kept with req := kept.req.set! 5 512 } 64 512) == "token-range"
#guard nameOf (coveredOf { kept with req := kept.req.set! 63 512 } 64 512) == "token-range"
#guard nameOf (coveredOf { kept with y := 512 } 64 512) == "token-range"
-- a kept word too few; then r = e and e > T in the kept words, which are read once more (the fields
-- r and e stay 61 and 64)
#guard nameOf (coveredOf { kept with req := kept.req.pop } 64 512) == "token-length"
#guard nameOf (coveredOf { kept with req := someRequest 64 64 } 64 512) == "statement-range"
#guard nameOf (coveredOf { kept with req := someRequest 63 65 } 64 512) == "statement-range"

-- every name that this file and OnBytes/Model/TestHeadLayout.lean expect is in `Layout.names`
#guard ["no-wrap-H-U-NF", "no-wrap-H-W-NF", "no-wrap-H-W-HD0", "no-wrap-H-three-digits",
    "no-wrap-H-HE", "no-wrap-H-Z", "no-wrap-H-E2", "no-wrap-H-E3", "no-wrap-H-J-E",
    "no-wrap-H-guard-radix", "policy-toksrc", "policy-norm-F", "policy-call-list-H",
    "header-absent-call-H", "statement-range", "statement-required", "token-range", "token-length",
    "shape-V", "policy-weight-kind", "policy-weight-width-emb", "policy-gap-words",
    "shape-request-matrix-H", "shape-call-H", "internal-head-shape"].all Layout.names.contains

end OnBytes.Model.Head
