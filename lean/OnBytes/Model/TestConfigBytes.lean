-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestConfigBytes.lean: tests of the small functions of OnBytes/Model/Config.lean, which
run when this file is compiled.

The tests break conditions of these functions one at a time, with the others holding, and try bounds
from both sides: the classes of bytes, the one spelling of a line, the lax reading of a line, the
call lines, the record of the value lines, the defaults of the optional lines, the places of the
tables' digests, the words of the scale file, and the functions on acceptance policies. They add to
OnBytes/Model/TestConfig.lean and TestConfigOrder.lean: some conditions are broken only there.
Nothing checks that every condition and every bound is reached.

What this file does not claim. The expected values come from the C++ source, read clause by clause
(verifier/src/vf_common.h: wordLineForm, digitsBeyondScan, acceptancePolicyIsExactMatch, aboveClip,
policyEmpty, PolicyNamed, policyNamedRead, rotaryServed; verifier/src/cp_verify.cpp: polWord,
parseHeader, polPrescan, polScan, polLayout), from the C library's rules for white space,
digits and the pattern of a word and a number, from the example's parameter file, or from a
calculation that the comment shows. No C++ program was run on these inputs. No program imports this
file.
-/
import OnBytes.Model.TestConfigOrder

namespace OnBytes.Model.TestConfigBytes

open OnBytes.Model.Config OnBytes.Model.TestConfig OnBytes.Model.TestConfigOrder

/-- The bytes for which p is true, in their order. -/
def bytesWhere (p : UInt8 → Bool) : List UInt8 :=
  ((List.range 256).map (·.toUInt8)).filter p

/-- A text of n times the sign c. -/
def times (n : Nat) (c : Char) : String := String.ofList (List.replicate n c)

/-! ## Classes of bytes -/

#guard bytesWhere isDigit == bytesOf "0123456789"
-- what C's isspace takes: tab, line feed, vertical tab, form feed, carriage return, space
#guard bytesWhere isSpace == [0x09, 0x0A, 0x0B, 0x0C, 0x0D, 0x20]
#guard bytesWhere callByte ==
  bytesOf "-.0123456789ABCDEFGHIJKLMNOPQRSTUVWXYZ_abcdefghijklmnopqrstuvwxyz"

/-! ## The one spelling of a line -/

#guard wordLineForm (bytesOf "a 0\n") && wordLineForm (bytesOf "a 4294967295\n")
-- the name's bytes are 0x21 to 0x7E
#guard wordLineForm (bytesOf "!~ 1\n")
#guard !wordLineForm ([0x7F] ++ bytesOf " 1\n") && !wordLineForm ([0x80] ++ bytesOf " 1\n")
-- no name; no digit; a leading zero; 33 bits; no line feed; something after the number; a tab for
-- the space
#guard !wordLineForm (bytesOf " 1\n")
#guard !wordLineForm (bytesOf "a \n") && !wordLineForm (bytesOf "a x\n")
#guard !wordLineForm (bytesOf "a 01\n") && !wordLineForm (bytesOf "a 00\n")
#guard !wordLineForm (bytesOf "a 4294967296\n")
#guard !wordLineForm (bytesOf "a 1") && !wordLineForm (bytesOf "a 1 \n")
#guard !wordLineForm (bytesOf "a 1\n\n") && !wordLineForm (bytesOf "a\t1\n")

/-! ## More than 19 digits in a row -/

#guard !digitsBeyondScan (bytesOf (times 19 '1')) && digitsBeyondScan (bytesOf (times 20 '1'))
#guard !digitsBeyondScan (bytesOf ("a " ++ times 19 '1' ++ "\n"))
#guard digitsBeyondScan (bytesOf ("a " ++ times 20 '1' ++ "\n"))
#guard !digitsBeyondScan (bytesOf (times 19 '1' ++ " " ++ times 19 '1'))

/-! ## The lax reading of a line -/

#guard scanLine (bytesOf "L 8\n") == some (bytesOf "L", 8)
#guard scanLine (bytesOf " \tL \t 8 \n") == some (bytesOf "L", 8)
-- the pattern takes 63 bytes as the word; the 64th is then no number
#guard scanLine (bytesOf (times 63 'a' ++ " 1\n")) == some (bytesOf (times 63 'a'), 1)
#guard scanLine (bytesOf (times 64 'a' ++ " 1\n")) == none
-- a number with a minus sign is negated in 64 bits
#guard scanLine (bytesOf "L -8\n") == some (bytesOf "L", 18446744073709551608)
#guard scanLine (bytesOf "L -0\n") == some (bytesOf "L", 0)
#guard scanLine (bytesOf "L +8\n") == some (bytesOf "L", 8)
-- nothing; a word alone; a word and no number; a third item
#guard scanLine (bytesOf "\n") == none && scanLine (bytesOf "L\n") == none
#guard scanLine (bytesOf "L x\n") == none && scanLine (bytesOf "L 8 8\n") == none

/-! ## The lines that are read before the scan -/

-- the byte ':' follows '9': read as a digit it would count as 10, and "1:" would spell 20
#guard refusal (withLines (setLine valueLines 0 "prof 1:") [] callLines) ==
  some "statement-required"

/-! ## The lines after F -/

#guard ["clt 1", "clns 1", "cms 1"].all fun x => withOptional [x] == some "policy-cert-words"
-- every optional line must be in the one spelling; of the 32 lines of the tables the first is tried
#guard ["lidb 024", "eg 04", "smax 0511", "rcl 01", "gcl 01", "xl 05"].all fun x =>
  withOptional [x] == some "policy-line-form"
#guard withOptional ["lidb 24", "nminH 021"] == some "policy-line-form"
#guard withOptional ("tsilu0 02048398297" :: tableLines.drop 1) == some "policy-line-form"

/-- The call lines of one kind. -/
def callsOf (kind : String) : List String := callLines.filter (·.startsWith (kind ++ " "))

#guard ["call", "callA", "callH"].all fun k => !(callsOf k).isEmpty
-- an optional line is refused after call lines of each kind alone
#guard ["call", "callA", "callH"].all fun k =>
  refusal (withLines valueLines [] (callsOf k)) == none &&
  refusal (withLines valueLines [] (callsOf k ++ ["xl 5"])) == some "policy-xl"
-- the order call, callA, callH
#guard ["callA", "callH"].all fun k =>
  refusal (withLines valueLines [] (callsOf k ++ ["call X R8 Y"])) == some "policy-call-line"
#guard refusal (withLines valueLines [] (callsOf "callH" ++ ["callA X R8 Y"])) ==
  some "policy-call-line"
#guard refusal (withLines valueLines [] (callsOf "call" ++ ["callA X R8 Y", "callH X R8 Y"])) ==
  none
-- an empty item; another first word
#guard refusal (withLines valueLines [] (callLines ++ ["callH X  R8 Y"])) ==
  some "policy-call-line"
#guard refusal (withLines valueLines [] (callLines ++ ["callB X R8 Y"])) == some "policy-call-line"

/-- The value lines of profile 3 (the line prof holds 16 plus the profile): those of the example
without the lines of attention. -/
def valueLines3 : List String :=
  (setLine valueLines 0 "prof 19").filter fun l =>
    (valueNames 3).contains ((l.splitOn " ").headD "")

-- below profile 4 there is no line callA; profile 3 is tried
#guard refusal (withLines valueLines3 [] (callsOf "call")) == none
#guard refusal (withLines valueLines3 [] (callsOf "call" ++ ["callA X R8 Y"])) ==
  some "policy-call-line"
-- the eleven numbers of attention, whose lines such a file lacks, are 0 in the record
#guard valueLines3.length + 11 == valueLines.length
#guard (fun (h : Hdr) => [h.lB, h.Sx, h.rx, h.kFM, h.kFD, h.lmS, h.NAs, h.lmh, h.lmo, h.lmbA,
  h.iotaA0]) (read (withLines valueLines3 [] (callsOf "call"))).h == List.replicate 11 0
#guard (read (withLines valueLines3 [] (callsOf "call"))).h.prof == 3

/-! ## Two clauses that no file reaches alone

No scan makes these two states: nminH comes only after lidb, and between two lines of the tables
only call lines are admitted, which have a clause of their own. So the states are written by
hand. -/

#guard nameOf ((lineAfterF 4 false { nminH := some 2 } (bytesOf "lidb 24\n")).map fun _ => ()) ==
  some "policy-lidb"
#guard nameOf ((lineAfterF 4 false { tbl := #[1] } (bytesOf "tsilu1 1\n")).map fun _ => ()) ==
  some "policy-tables"
#guard nameOf ((lineAfterF 4 true { tbl := #[1] } (bytesOf "tsilu1 1\n")).map fun _ => ()) == none

/-! ## The record of the value lines -/

/-- The record of the example's value lines with some lines replaced, by their names. -/
def hdrWith (other : List (String × Nat)) : Hdr :=
  (read (withLines (valueLines.map fun l =>
    let name := (l.splitOn " ").headD ""
    match other.lookup name with
    | some v => name ++ " " ++ toString v
    | none => l) [] callLines)).h

#guard (hdrWith []).prof == 4
-- a number of 64 bits: the line _lo plus 2^32 times the line _hi
#guard (hdrWith [("seed_lo", 2), ("seed_hi", 3)]).seed == 12884901890
#guard (hdrWith [("theta0_lo", 5), ("theta0_hi", 1)]).theta0 == 4294967301
-- the 13 digit forms (Hdr.hf) from the seven lines hq to hr: keys as queries; with experts, the
-- five classes of the expert layers as gate, up, gate, up, down of the dense layer
#guard (hdrWith [("hq", 1), ("hv", 2), ("ho", 0), ("hgD", 1), ("huD", 2), ("hdD", 1), ("hr", 2),
  ("NE", 4)]).hf == #[1, 1, 2, 0, 1, 2, 1, 2, 1, 2, 1, 2, 1]
-- at profile 4 without experts these five are 0
#guard (hdrWith [("hq", 1), ("hv", 2), ("ho", 0), ("hgD", 1), ("huD", 2), ("hdD", 1), ("hr", 2),
  ("NE", 0)]).hf == #[1, 1, 2, 0, 1, 2, 1, 2, 0, 0, 0, 0, 0]
-- at profile 3 they are there with NE = 0 too; at profile 2 they are 0
#guard (hdrOf fun n => if n == "prof" then 19 else if n == "NE" then 0 else 1).hf ==
  Array.replicate 13 1
#guard (hdrOf fun n => if n == "prof" then 18 else 1).hf ==
  #[1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0]
#guard (hdrWith [("iotaH_0", 10), ("iotaH_1", 11), ("iotaH_2", 12), ("iotaH_3", 13),
  ("iotaH_4", 14), ("iotaH_5", 15)]).iotaH == #[10, 11, 12, 13, 14, 15]

/-! ## Defaults, and what the scan gives -/

/-- The scan of the example's file without optional lines. -/
def bare : PolScan := read (withLines valueLines [] callLines)

#guard bare.value "lt" == 6 && bare.value "no such line" == 0
-- the defaults: eg 8, smax 4095, four limbs, lidb 22, no nminH. That the lines eg 8, smax 4095,
-- xl 4 and lidb 22 are refused is tested in OnBytes/Model/TestConfigOrder.lean, not here.
#guard bare.EG == 8 && bare.SMAX == 4095 && bare.XL == 4
#guard bare.settings.lidb == 22 && bare.settings.nminH == 0
#guard (read kit).XL == 5 && (read kit).settings.lidb == 24
#guard nameOf (polBehindLayout
  { read kit with
    frame := { (read kit).frame with sec := 4097 }
    h := { (read kit).h with tau := 8192 } }) == some "hid-hb"
#guard nameOf (polBehindLayout
  { read kit with
    frame := { (read kit).frame with sec := 4096 }
    h := { (read kit).h with tau := 8192 } }) == none

/-! ## How long an admitted file can be

The count in OnBytes/Model/Config.lean (the part on the scan), added up. The numbers 8, 12 and 6,
and that a line of the frame other than a line stages has a fixed number of values, at most 6, were
read in the files that it names; no guard here ties them to those files. -/

-- the longest name of a value line has 9 bytes, of an optional line 6 (tsilu0, trope0 and so on)
#guard (valueNames 4).all fun n => decide (n.length ≤ 9)
#guard (["lidb", "nminH", "eg", "smax", "rcl", "gcl", "xl"] ++ tableNames.map (· ++ "0")).all
  fun n => decide (n.length ≤ 6)
#guard (valueNames 4).length == 97
-- the frame has 32 lines; a number in them has at most 15 digits, a line stages at most 32 numbers
#guard frameLines.length == 32
#guard (Params.number (bytesOf "999999999999999")).isSome
#guard (Params.number (bytesOf "1000000000000000")).isNone
#guard underFrame "stages once-ranges "
  ("stages once-ranges" ++ String.join (List.replicate 36 " 1")) ==
  some "parameter-stages-count (policy)"
-- a line of the frame: "stages once-ranges" and 32 times a space and 15 digits, and the line feed;
-- a value line or an optional line: the name, a space, ten digits, the line feed
#guard 32 * (18 + 32 * 16 + 1) + 97 * (9 + 12) + 39 * (6 + 12) + (8 + 12 + 6) * 1023 == 46329

/-! ## The tables' digests -/

-- the first word of each table's digest is the example's line tsilu0, tsig0, trope0, texp0
#guard [PublicTable.silu, .sigmoid, .rope, .exp].map
  (fun t => ((read kit).tableExpected t).map (Fmt.leNat · 0 4)) ==
  [some 2048398297, some 1965976300, some 2232934348, some 3648852807]
-- the last word is the line tsilu7, tsig7, trope7, texp7, and each digest has 32 bytes
#guard [PublicTable.silu, .sigmoid, .rope, .exp].map
  (fun t => ((read kit).tableExpected t).map fun d => (d.size, Fmt.leNat d 28 4)) ==
  [some (32, 2593882461), some (32, 2601410768), some (32, 2900737701), some (32, 165292856)]
#guard tableHashNumber == 72

/-! ## The scale file -/

#guard klWord ⟨#[1, 2, 3, 4, 5, 6, 7]⟩ 0 == 67305985
#guard klWord ⟨#[1, 2, 3, 4, 5, 6, 7]⟩ 1 == 0
#guard klWord ⟨#[1, 2, 3, 4, 5, 6, 7, 8]⟩ 1 == 134678021
#guard ((parDigests kit (Fmt.zeroBytes 28) none).toOption).isNone
#guard ((parDigests kit (Fmt.zeroBytes 32) none).toOption).isSome
#guard nameOf (klHeld (Fmt.zeroBytes 32)) == none
#guard (twoDigests.map (·.lay.size)) == some 32 && (twoDigests.map (·.layW)) == some 0

/-! ## Acceptance policies -/

-- sh must be below 63; theta must be 2^sh
#guard exactMatch (2 ^ 62) (2 ^ 62) 0 62 58 && !exactMatch (2 ^ 63) (2 ^ 63) 0 63 59
#guard !exactMatch 300 300 0 8 4

/-- A named policy that fits the lines 256, 256, 0, 15, 8, 4. -/
def named : PolicyNamed := ⟨"exact-match", 256, 256, 0, 15, 8⟩

#guard named.is 256 256 0 15 8 4
-- each of the six comparisons alone
#guard !{ named with kind := "clipped-gap" }.is 256 256 0 15 8 4
#guard !({ kind := "clipped-gap", C := 301, theta := 299, cap := 0, s := 15, sh := 8 } :
  PolicyNamed).is 300 299 0 15 8 4
#guard !({ kind := "clipped-gap", C := 300, theta := 298, cap := 0, s := 15, sh := 8 } :
  PolicyNamed).is 300 299 0 15 8 4
#guard !({ kind := "clipped-gap", C := 300, theta := 299, cap := 1, s := 15, sh := 8 } :
  PolicyNamed).is 300 299 0 15 8 4
#guard !({ kind := "clipped-gap", C := 300, theta := 299, cap := 0, s := 14, sh := 8 } :
  PolicyNamed).is 300 299 0 15 8 4
#guard !({ kind := "clipped-gap", C := 300, theta := 299, cap := 0, s := 15, sh := 9 } :
  PolicyNamed).is 300 299 0 15 8 4
#guard ({ kind := "clipped-gap", C := 300, theta := 299, cap := 0, s := 15, sh := 8 } :
  PolicyNamed).is 300 299 0 15 8 4
#guard policyNamedRead "exact-match,,256,0,15,8" == none
#guard policyNamedRead "exact-match,1234567890,256,0,15,8" ==
  some ⟨"exact-match", 1234567890, 256, 0, 15, 8⟩

#guard rotaryServed 10000 128 10 && rotaryServed 500000 128 10
#guard !rotaryServed 10000 129 10 && !rotaryServed 10000 128 11 && !rotaryServed 10001 128 10

-- 10 k ≤ 9 leaves k = 0
#guard aboveClip 1 266 265 1 8 == 0 && aboveClip 1 266 266 1 8 == 1
-- from sh = 63 on the least cost counts as 2^64 - 1, so no C of 64 bits is above it
#guard aboveClip 10 18446744073709551615 5 4 63 == 4
-- a C of 65 bits, which no file and no C++ number can be, is above it; theta is not, so k = 0
#guard aboveClip 5 18446744073709551616 0 5 63 == 0
-- at sh = 62 it is 2^62: with C = 2^62 + 10 and theta = 2^62 + 1, 10 k ≤ 10 leaves k = 1
#guard aboveClip 10 4611686018427387914 4611686018427387905 4 62 == 1

-- policyEmpty: the fourth case needs theta = C: with cap = n it arises there, not at theta = C - 1
#guard policyEmpty 3 300 299 3 8 == 0 && policyEmpty 3 300 300 3 8 == 4
-- from sh = 63 on the least cost counts as 2^64 - 1: C = 2^64 - 2 is below it, C = 2^64 - 1 is not
#guard policyEmpty 1 18446744073709551614 18446744073709551614 0 63 == 1
#guard policyEmpty 1 18446744073709551615 18446744073709551615 0 63 == 0
-- at sh = 62 it is 2^62
#guard policyEmpty 1 4611686018427387904 4611686018427387904 0 62 == 0
#guard policyEmpty 1 4611686018427387903 4611686018427387903 0 62 == 1

end OnBytes.Model.TestConfigBytes
