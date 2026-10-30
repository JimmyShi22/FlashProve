-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestAttentionConfig.lean: tests of OnBytes/Model/AttentionConfig.lean.

The tests run when this file is compiled. The program does not import this file.

The numbers are those of a small configuration, spelled out here and called the example: see the
section The example, which also says where the expected values come from. No file of the repository
is read.

What is tested.
 - The reading of the call lines and each of its six conditions. All six refuse under one name, so a
   guard does not show which of them refused.
 - The lines' text, and its digest against the one that OnBytes/Proof/RequestItem.lean takes from
   the same lines as text. Both routines are Lean's and hash the text in the same way, under the
   number 73 (earlier_hash_h_digest in verifier/src/cp_verify.cpp). No digest of call lines made by
   the C++ program is compared here.
 - The count of expanded calls.
 - The filled configuration, also with all numbers different and for the second group's shifts.
 - What else the plan gets.
 - The digest of the table of exponentials against the parameter file's lines texp0 to texp7.
 - The two tests that config makes on the parameter file's numbers before any plan.
The function group, and config with plans, are tested in
OnBytes/Model/TestAttentionConfigWhole.lean and TestAttentionConfigRefused.lean.

Not tested, here or in the two files named above: the order of config's tests; the clauses on Lam,
dkv and ls in group's comparison of sizes, and group's last test; a parameter file without digest
lines; the list configNames.
-/
import OnBytes.Model.AttentionConfig
import OnBytes.Proof.RequestItem

namespace OnBytes.Attention.TestConfig

/-- True if r is the refusal of that name. -/
def refusedAs {α : Type} (r : Except String α) (name : String) : Bool :=
  match r with
  | .error e => e == name
  | .ok _ => false

/-! ## The example

The numbers are those of a small configuration, spelled out here (64 tokens, eight layers in two
groups of four, four query heads, two heads of keys and values). Below it is called the example. It
is given as the lines of a parameter file (exampleScan, exampleCalls, exampleTexp) and as a file of
scales in which every layer has the shift 12 (exampleScales). A file of scales is a list of words of
32 bits, the low byte first. A layer's record has 13 words, and the shift is word 11 of the record
(Scales.klSh in OnBytes/Model/LayerLayout.lean). The function fill takes the shift from there, not
from the parameter file's lines sh or cs. No file of the repository is read; the examples under
prover/examples may have other numbers.

Where the expected values come from. The text of the lines, the limits and the numbers that fill and
inOf return are what the part of runStage in verifier/src/cp_verify.cpp that builds the attention
sub-proofs gives for these inputs, by a reading of that source. The eight words of exampleTexp were
copied from a parameter file with S 12 and rx 8 that the C++ verifier did not refuse.
-/

/-- The example's lines callA, each without its first word. -/
def exampleCalls : List (List String) :=
  [["KR", "KR", "RM", "RD"], ["KFD", "KFD", "FM", "FD"], ["R16", "R16", "WL", "IX"],
   ["WH", "WH", "WH"]]

/-- The same lines as they should be read. -/
def exampleLines : List Line :=
  [⟨"KR", .kr, [.rm, .rd]⟩, ⟨"KFD", .kfd, [.fm, .fd]⟩, ⟨"R16", .r16, [.wl, .ix]⟩,
   ⟨"WH", .wh, [.wh]⟩]

/-- The eight layers' records of the example's file of scales. Only the shift is written out. The
twelve words that follow the records in a file are left out; nothing here reads them. -/
def exampleScales : Model.Layer.Scales :=
  ⟨((List.range (13 * 8)).map fun i => if i % 13 == 11 then 12 else 0).toArray, 13, 8⟩

/-- The example's lines texp0 to texp7: the digest of the table of exponentials, in eight words.
They were copied from a parameter file with these numbers (S 12, rx 8). -/
def exampleTexp : List Nat :=
  [3648852807, 2402568834, 4186852988, 523559909, 1873895626, 3042864545, 1726265496, 165292856]

/-- The parameter file as read, with the example's lines as far as the attention sub-proofs read
them. The digests of the three other tables are left 0. -/
def exampleScan : Model.PolScan :=
  { (default : Model.PolScan) with
    frame := { (default : Params.Lines) with sec := 128 },
    h := { lt := 6, ll := 2, la := 8, nmin := 20, H := 4, Gk := 2, lB := 4, Sx := 12, rx := 8,
           kFD := 16, lmS := 11, NAs := 1, lmh := 12, lmo := 13, lmbA := 13, iotaA0 := 52,
           tau := 128 },
    lidb := some 24,
    polCallsA := exampleCalls,
    tblPol := (List.replicate 24 0 ++ exampleTexp).toArray }

/-- The numbers of the layers' layout that fill and inOf read, at the example. They are typed here.
OnBytes/Model/TestAttentionConfigWhole.lean compares them with what the layers' own function
gives. -/
def exampleLayers : Model.Layer.Lay :=
  { h := default, T := 64, Lam := 4, NGr := 2, ldh := 7, mrow := #[0, 0, 0, 8192],
    kcol := #[0, 0, 0, 96] }

/-- The numbers of a configuration, in the order of the record Cfg. -/
def numbersOf (c : Cfg) : List Nat :=
  [c.lt, c.lB, c.lgk, c.ldh, c.ll, c.S, c.rx, c.kFD, c.lmS, c.la, c.lmb, c.nmin, c.H, c.wcH, c.wcO,
   c.wcQ, c.NAs, c.Ty]

-- the call lines
#guard (readLines exampleCalls).toOption == some exampleLines
#guard refusedAs (readLines []) "policy-call-list-A"
#guard refusedAs (readLines [["a", "R8", "WL"]]) "policy-call-list-A"
#guard refusedAs (readLines [["a", "WH", "WH"], ["a", "R16", "IX"]]) "policy-call-list-A"
#guard refusedAs (readLines [["a", "WH", "wh"]]) "policy-call-list-A"
#guard refusedAs (readLines [["a"]]) "policy-call-list-A"

/-- n lines with different names. -/
def manyLines (n : Nat) : List (List String) :=
  (List.range n).map fun i => ["c" ++ toString i, "WH", "WH"]

-- twelve lines are read, thirteen are not
#guard (readLines (manyLines 12)).isOk
#guard refusedAs (readLines (manyLines 13)) "policy-call-list-A"

-- each name is read back as the kind that it spells
#guard Seg.all.all fun s => Seg.ofName s.name == some s
#guard [Table.kr, .kfd, .r16, .wh].all fun k => Table.ofName k.name == some k

-- the text that is hashed
#guard String.join (exampleLines.map Line.text) ==
  "callA KR KR RM RD\ncallA KFD KFD FM FD\ncallA R16 R16 WL IX\ncallA WH WH WH\n"

/-- The example's lines texp0 to texp7 and callA, as the parameter file has them. -/
def exampleText : String :=
  String.join ((List.range 8).map fun i =>
    "texp" ++ toString i ++ " " ++ toString (exampleTexp.getD i 0) ++ "\n") ++
  "callA KR KR RM RD\ncallA KFD KFD FM FD\ncallA R16 R16 WL IX\ncallA WH WH WH\n"

/-- Words 114 to 129 of the value of the item request, as OnBytes/Proof/RequestItem.lean takes them
from the file's text. -/
def exampleItemWords : Option ByteArray := do
  let L := Proof.ParamLines.read exampleText.toUTF8
  pure ((← L.eight "texp") ++ (← L.calls "callA"))

-- the digest of the lines as read is the digest that the item request takes from the file's text
#guard some (callsDigest exampleLines) ==
  (Proof.ParamLines.read exampleText.toUTF8).calls "callA"

-- two of the four lines stand for one call for each value of the shift
#guard expandedCalls exampleLines #[12, 12, 12, 12] == 4
#guard expandedCalls exampleLines #[9, 8, 9, 9] == 6
#guard expandedCalls exampleLines #[4, 5, 6, 7] == 10

-- the filled configuration
#guard ((fill exampleScan exampleLayers exampleScales exampleLines 1).toOption.map numbersOf) ==
  some [6, 4, 1, 7, 2, 12, 8, 16, 11, 8, 13, 20, 4, 64, 128, 128, 1, 262144]
#guard ((fill exampleScan exampleLayers exampleScales exampleLines 1).toOption.map (·.sh)) ==
  some #[12, 12, 12, 12]
#guard refusedAs (fill { exampleScan with h := { exampleScan.h with Sx := 32 } } exampleLayers
  exampleScales exampleLines 0) "af-policy-wd"
-- with four different shifts, three lines by shift stand for twelve calls; one line more is too
-- many
#guard (fill exampleScan exampleLayers ⟨Array.range 104, 13, 8⟩
  [⟨"KR", .kr, [.rm]⟩, ⟨"KFD", .kfd, [.fm]⟩, ⟨"KR2", .kr, [.rd]⟩] 0).isOk
#guard refusedAs (fill exampleScan exampleLayers ⟨Array.range 104, 13, 8⟩
  [⟨"KR", .kr, [.rm]⟩, ⟨"KFD", .kfd, [.fm]⟩, ⟨"KR2", .kr, [.rd]⟩, ⟨"WH", .wh, [.wh]⟩] 0)
  "policy-call-list-A"

-- what else the plan gets: the attention sub-proofs have the numbers 4 and 5
#guard (inOf exampleScan.settings exampleLayers 262 0).gid == 4
#guard (inOf exampleScan.settings exampleLayers 518 1).gid == 5
#guard (inOf exampleScan.settings exampleLayers 518 1).midQ == 518
#guard (inOf exampleScan.settings exampleLayers 518 1).ktO == 96
#guard (inOf exampleScan.settings exampleLayers 518 1).hb == 128
#guard (inOf { exampleScan.settings with pow := 20 } exampleLayers 518 1).hb == 108
#guard (inOf exampleScan.settings exampleLayers 518 1).aO == 2
#guard (inOf exampleScan.settings exampleLayers 518 1).col0Q == 0

/-- The example's parameter file with another record of numbers. -/
def withNumbers (h : Model.Hdr) : Model.PolScan := { exampleScan with h := h }

/-- Numbers of a parameter file that all differ, so that no field can be taken for another. -/
def unlikeNumbers : Model.Hdr :=
  { lt := 1, lB := 2, H := 3, Gk := 16, ll := 5, Sx := 6, rx := 7, kFD := 8, lmS := 9, la := 10,
    lmbA := 11, nmin := 12, NAs := 13, lmh := 14, lmo := 15 }

-- lgk = 4 from Gk = 16; wcH = 2^14 / 2, wcO = 2^15 / 2 and wcQ = 38 / 2 with T = 2
#guard ((fill (withNumbers unlikeNumbers)
    { exampleLayers with T := 2, ldh := 17, mrow := #[0, 0, 0, 38] } exampleScales exampleLines
    0).toOption.map numbersOf) ==
  some [1, 2, 4, 17, 5, 6, 7, 8, 9, 10, 11, 12, 3, 8192, 16384, 19, 13, 262144]
-- group 1 has the shifts of layers 4 to 7: word 13 l + 11 of a file whose word i is i
#guard ((fill exampleScan exampleLayers ⟨Array.range 104, 13, 8⟩ [⟨"WH", .wh, [.wh]⟩]
    1).toOption.map (·.sh)) == some #[63, 76, 89, 102]
-- S = 31 is filled; 32 is refused above
#guard (fill { exampleScan with h := { exampleScan.h with Sx := 31 } } exampleLayers
  exampleScales exampleLines 0).isOk

/-- The name under which config refuses the numbers h if the layers' layout has no group. With no
group no plan is made. So the name is shape-L if and only if the two tests on the parameter file's
numbers pass. -/
def earlyName (h : Model.Hdr) : Option String :=
  match config (withNumbers h) { exampleLayers with NGr := 0 } exampleScales fun _ => 0 with
  | .error e => some e
  | .ok _ => none

-- the two tests on the parameter file's numbers, each limit from both sides
#guard earlyName exampleScan.h == some "shape-L"
#guard earlyName { exampleScan.h with Gk := 3 } == some "af-shape-heads"
#guard earlyName { exampleScan.h with Gk := 4 } == some "shape-L"
#guard earlyName { exampleScan.h with lmh := 5 } == some "shape-request-matrix-A"
#guard earlyName { exampleScan.h with lmh := 6 } == some "shape-L"
#guard earlyName { exampleScan.h with lmh := 24 } == some "shape-L"
#guard earlyName { exampleScan.h with lmh := 25 } == some "shape-request-matrix-A"
#guard earlyName { exampleScan.h with lmo := 5 } == some "shape-request-matrix-A"
#guard earlyName { exampleScan.h with lmo := 6 } == some "shape-L"
#guard earlyName { exampleScan.h with lmo := 24 } == some "shape-L"
#guard earlyName { exampleScan.h with lmo := 25 } == some "shape-request-matrix-A"
#guard earlyName { exampleScan.h with lmbA := 24 } == some "shape-L"
#guard earlyName { exampleScan.h with lmbA := 25 } == some "shape-request-matrix-A"
#guard earlyName { exampleScan.h with lmS := 24 } == some "shape-L"
#guard earlyName { exampleScan.h with lmS := 25 } == some "shape-request-matrix-A"
#guard earlyName { exampleScan.h with NAs := 0 } == some "shape-request-matrix-A"
#guard earlyName { exampleScan.h with NAs := 64 } == some "shape-L"
#guard earlyName { exampleScan.h with NAs := 65 } == some "shape-request-matrix-A"

/-- A shape that has the table of exponentials for S = 12 and rx = 8 and nothing else. -/
def tableShape : Shape :=
  let Tt := (expTable 12 8).getD #[]
  { Tt := Tt, u0 := Tt.size }

/-- The digest of a shape's table of exponentials. -/
def expDigest (A : Shape) : ByteArray := Model.tableDigest (Fmt.cat (A.Tt.toList.map word32))

-- the table's digest is the one that the example's parameter file gives
#guard expDigest tableShape == Fmt.cat (exampleTexp.map word32)
#guard some (expDigest tableShape ++ callsDigest exampleLines) == exampleItemWords
#guard (Model.tableHeld exampleScan .exp tableShape.Tt).isOk
#guard refusedAs (Model.tableHeld exampleScan .exp tableShape.Tt.pop) "table-digest-exp"

end OnBytes.Attention.TestConfig
