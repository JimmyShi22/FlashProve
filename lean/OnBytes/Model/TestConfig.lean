-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/TestConfig.lean: tests of OnBytes/Model/Config.lean, which run when this file is
compiled.

The parameter file of the tests is that of a small configuration, spelled out here; the comments
call it the example. It describes a small model (8 layers, 64 tokens) that is meant for synthetic
weights. Its files hold public parameters and no weights, and the digests below are digests of these
public files. No file of the repository is compared with it. The tests read it, and altered
copies of it, each with the name under which the scan must refuse it, or with none where the scan
must admit it. The tests of policyKind, aboveClip and policyEmpty are the known answers that the C++
verifier asserts at its build (verifier/src/vf_common.h).

What this file does not claim. The names under which the altered copies must be refused were read
off the C++ source (verifier/src/cp_verify.cpp: polPrescan, polScan, polLayout, and the two
tests on lt that follow polPrescan in runStage). No C++ program was run on the altered copies. On
the example's own files the C++ verifier was run, for the digests: see the section on the digests of
the files. No test here hashes a real table: tableHeld is tested on a wrong table and on a file
without the tables' lines only. No program imports this file.
-/
import OnBytes.Model.Config

namespace OnBytes.Model.TestConfig

/-- The name of a refusal; none for a test that was passed. -/
def nameOf (x : Except String Unit) : Option String :=
  match x with
  | .ok _ => none
  | .error e => some e

/-- The frame's lines: the file's first 32 lines, from version to table, which
OnBytes/Params/File.lean reads. -/
def frameLines : List String :=
  [
   "version H821", "sec 128", "reading 1", "rowcost 1", "slots 64", "answers 1", "record 1",
   "work field 0 0 0", "work sample 0 0 0", "work closeness 0 0 0", "work positions 0 0 0",
   "work smallness 0 0 0", "salt 40", "listed 0", "group link 1 18 17 17 13",
   "stages link 4 3 17 17 3 3 16 16 3 3 15 15 0 0 15 15", "group folded 1 17 15 13 6",
   "stages folded 4 2 14 12 0 0 14 14", "group omega 1 18 14 13 6",
   "stages omega 4 3 14 13 0 0 15 15", "group own 1 18 14 13 8",
   "stages own 4 3 14 13 0 0 15 15", "group once-folded 1 17 15 13 6",
   "stages once-folded 4 2 14 12 0 0 14 14", "group once-omega 1 18 14 13 6",
   "stages once-omega 4 3 14 13 0 0 15 15", "group once-own 1 18 14 13 8",
   "stages once-own 4 3 14 13 0 0 15 15", "group once-ranges 1 22 18 16 10",
   "stages once-ranges 4 3 19 17 3 3 17 17 0 0 20 20", "ranges-part 14",
   "table 8 23 524288 65535 0 11"]

/-- The value lines from prof to F. -/
def valueLines : List String :=
  [
   "prof 20", "lt 6", "L 8", "ll 2", "d 512", "H 4", "G 2", "dh 128", "f 1024", "fe 512", "NE 4",
   "V 512", "eps1_lo 1", "eps1_hi 0", "eps2_lo 1", "eps2_hi 0", "cs 12", "theta0_lo 10000",
   "theta0_hi 0", "hq 2", "hv 1", "ho 1", "hgD 1", "huD 1", "hdD 1", "hr 1", "ut 1", "la 8",
   "nmin 20", "D 2048", "tau 128", "lmaf 13", "NAf 3", "lmad 12", "NAd 1", "lmar 12", "lmb 13",
   "lmq 13", "lmx 13", "wb_qk 13", "wb_v 13", "wb_o 13", "wb_g 13", "wb_u 13", "wb_gs 13",
   "wb_us 13", "wb_gr 13", "wb_ur 13", "wb_dn 13", "wb_dnr 13", "wb_r 13", "iota_0 0",
   "iota_1 0", "iota_2 0", "iota_3 1", "iota_4 0", "iota_5 0", "iota_6 0", "iota_7 0",
   "seed_lo 31", "seed_hi 0", "lB 4", "S 12", "rx 8", "kFM 15", "kFD 16", "lmS 11", "NAs 1",
   "lmh 12", "lmo 13", "lmbA 13", "iotaA_0 52", "MF 44", "KF 30", "epsF_lo 1", "epsF_hi 0",
   "toksrc 1", "lmhf 14", "NHf 1", "lmhd 12", "lmhr 12", "lmbH 13", "wb_emb 21", "wb_head 13",
   "iotaH_0 0", "iotaH_1 0", "iotaH_2 0", "iotaH_3 0", "iotaH_4 0", "iotaH_5 0", "C 256",
   "theta 256", "cap 0", "s 15", "sh 8", "sT 4", "F 24"]

/-- The example's optional lines: four of the seven lines lidb to xl, then the 32 lines of the
tables' digests. -/
def optionalLines : List String :=
  [
   "lidb 24", "rcl 1", "gcl 1", "xl 5", "tsilu0 2048398297", "tsilu1 192427613",
   "tsilu2 2862900154", "tsilu3 2853881485", "tsilu4 2797826050", "tsilu5 1420723544",
   "tsilu6 3686369553", "tsilu7 2593882461", "tsig0 1965976300", "tsig1 2359599336",
   "tsig2 2246761285", "tsig3 2426172242", "tsig4 3869868832", "tsig5 310049175",
   "tsig6 339407438", "tsig7 2601410768", "trope0 2232934348", "trope1 2156588140",
   "trope2 3599599331", "trope3 498649753", "trope4 3675316650", "trope5 2999201840",
   "trope6 1537898906", "trope7 2900737701", "texp0 3648852807", "texp1 2402568834",
   "texp2 4186852988", "texp3 523559909", "texp4 1873895626", "texp5 3042864545",
   "texp6 1726265496", "texp7 165292856"]

/-- The call lines. -/
def callLines : List String :=
  [
   "call R16a R16 G U", "call R16b R16 N1 N1H N2 N2H O D V", "call R16c R16 QK QKH XR LR LT DD",
   "call R8 R8 GH UH OH DH VH ROW LH SEL L3 G0", "call FC FC CN1 CN2 CQK CV CLR",
   "call FS FS MR CG", "call FL FL F", "call R16d R16 UT", "callA KR KR RM RD",
   "callA KFD KFD FM FD", "callA R16 R16 WL IX", "callA WH WH WH", "callH R16a R16 NF NFH HD0",
   "callH R16b R16 HD1", "callH R8 R8 ROW HD2", "callH FEa FE HE0", "callH FEb FE HE1",
   "callH FC FC CNF"]

/-- A file from its lines. -/
def fileOf (l : List String) : ByteArray := (String.join (l.map (· ++ "\n"))).toUTF8

/-- The example's file. -/
def kit : ByteArray := fileOf (frameLines ++ valueLines ++ optionalLines ++ callLines)

/-- The name under which the scan refuses a file; none if it admits the file. -/
def refusal (b : ByteArray) : Option String :=
  match polScan b with
  | .ok _ => none
  | .error e => some e

/-- The scan's result on a file that it admits; the default record for a file that it refuses. -/
def read (b : ByteArray) : PolScan :=
  match polScan b with
  | .ok P => P
  | .error _ => default

/-- The file with other value lines, optional lines and call lines. -/
def withLines (v o c : List String) : ByteArray := fileOf (frameLines ++ v ++ o ++ c)

/-- The list with member i replaced. -/
def setLine (l : List String) (i : Nat) (s : String) : List String := l.set i s

/-! ## Lines -/

#guard Config.linesOf [] == [] && Config.linesOf [0x0A] == [[0x0A]]
#guard Config.linesOf [0x61, 0x0A, 0x0A, 0x62] == [[0x61, 0x0A], [0x0A], [0x62]]
#guard (Config.linesOf (List.replicate 300000 0x61)).length == 1
#guard (Config.linesOf (List.replicate 300000 0x0A)).length == 300000

/-! ## The example's file -/

#guard refusal kit == none
#guard (read kit).h.prof == 4 && (read kit).h.lt == 6 && (read kit).h.L == 8
#guard (read kit).h.Gk == 2 && (read kit).h.V == 512 && (read kit).h.theta0 == 10000
#guard (read kit).h.hf == #[2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
#guard (read kit).h.iota == #[0, 0, 0, 1, 0, 0, 0, 0] && (read kit).h.seed == 31
#guard (read kit).h.iotaA0 == 52 && (read kit).h.Sx == 12 && (read kit).h.wbH == #[21, 13]
#guard (read kit).h.clipC == 256 && (read kit).h.tabS == 4 && (read kit).h.famF == 24
#guard (read kit).settings == ({ lidb := 24, nminH := 0, tau := 128, hb := 128 } : Settings)
#guard (read kit).rcl && (read kit).gcl && (read kit).XL == 5 && (read kit).EG == 8
#guard (read kit).polCalls.length == 8 && (read kit).polCallsA.length == 4
#guard (read kit).polCallsH.head? == some ["R16a", "R16", "NF", "NFH", "HD0"]
#guard (read kit).tblPol.size == 32 && (read kit).tblPol[8]? == some 1965976300
#guard (read kit).hb == 128 && (read kit).lkW == 11
#guard nameOf (polBeforeLayout (read kit)) == none && nameOf (polBehindLayout (read kit)) == none
#guard nameOf (polTablesAdmitted (read kit)) == none
#guard ((read kit).tableExpected .silu).map (·.size) == some 32
#guard ((read kit).tableExpected .silu).map (Fmt.leNat · 0 4) == some 2048398297
#guard ((read kit).tableExpected .exp).map (Fmt.leNat · 28 4) == some 165292856

/-! ## Altered copies -/

-- a line that is a single space at the end of the file
#guard refusal (fileOf (frameLines ++ valueLines ++ optionalLines ++ callLines ++ [" "])) ==
  some "policy-call-line"
-- a fault in the frame's first line
#guard refusal (fileOf (("version H811" :: frameLines.drop 1) ++ valueLines)) ==
  some "version-of-another-field (policy)"
-- the lines that are read before the scan
#guard refusal (withLines (valueLines.drop 1) optionalLines callLines) == some "statement-required"
#guard refusal (withLines (setLine valueLines 0 "prof 4") [] callLines) ==
  some "statement-required"
#guard refusal (withLines (valueLines.map fun l => if l == "toksrc 1" then "toksrc 0" else l) []
  callLines) == some "statement-required"
#guard refusal (withLines (valueLines.filter (· != "lt 6")) [] callLines) == some "policy-name-lt"
#guard refusal (withLines (setLine valueLines 1 "lt 17") [] callLines) == some "shape-words"
-- form, order and number of the value lines. In policy-line-4 the 4 is the C++ verifier's count, in
-- which the line prof is 2; it is not the line's number in the file.
#guard refusal (withLines (setLine valueLines 2 "L 08") [] callLines) == some "policy-line-form"
#guard refusal (withLines (setLine valueLines 2 "L  8") [] callLines) == some "policy-line-form"
#guard refusal (withLines (setLine valueLines 2 "L 8 ") [] callLines) == some "policy-line-form"
#guard refusal (withLines (setLine valueLines 2 "L 8 8") [] callLines) == some "policy-line-4"
#guard refusal (withLines (setLine valueLines 2 "L 4294967296") [] callLines) ==
  some "policy-line-4"
#guard refusal (withLines (setLine valueLines 2 "L 12345678901234567890") [] callLines) ==
  some "policy-line-form"
#guard refusal (withLines (setLine valueLines 2 "ll 2") [] callLines) == some "policy-name-L"
#guard refusal (withLines valueLines.dropLast [] []) == some "policy-length"
#guard refusal (withLines valueLines.dropLast [] callLines) == some "policy-line-98"
-- the optional lines
#guard refusal (withLines valueLines [] callLines) == none
#guard refusal (withLines valueLines ["lidb 22"] callLines) == some "policy-lidb"
#guard refusal (withLines valueLines ["lidb 31"] callLines) == some "plan-identity-cap"
#guard refusal (withLines valueLines ["rcl 1", "lidb 24"] callLines) == some "policy-lidb"
#guard refusal (withLines valueLines ["nminH 21"] callLines) == some "policy-nminH"
#guard refusal (withLines valueLines ["lidb 24", "nminH 21"] callLines) == none
#guard refusal (withLines valueLines ["smax 511", "eg 4"] callLines) == some "policy-gate-table"
#guard refusal (withLines valueLines ["eg 4", "smax 511"] callLines) == none
#guard refusal (withLines valueLines ["eg 8"] callLines) == some "policy-gate-table"
#guard refusal (withLines valueLines ["rcl 2"] callLines) == some "policy-rcl"
#guard refusal (withLines valueLines ["gcl 1", "rcl 1"] callLines) == some "policy-rcl"
#guard refusal (withLines valueLines ["xl 4"] callLines) == some "policy-xl"
#guard refusal (withLines valueLines ["hb 128"] callLines) ==
  some "policy-line-of-an-earlier-format"
#guard refusal (withLines valueLines ["mbx 1"] callLines) ==
  some "policy-line-of-an-earlier-format"
#guard refusal (withLines valueLines ["cms 1"] callLines) == some "policy-cert-words"
#guard refusal (withLines valueLines optionalLines.dropLast callLines) == some "policy-tables"
#guard refusal (withLines valueLines (optionalLines ++ ["texp8 1"]) callLines) ==
  some "policy-tables"
#guard refusal (withLines valueLines ["tsilu1 1"] callLines) == some "policy-tables"
-- the call lines
#guard refusal (withLines valueLines [] (callLines ++ ["call X R8 Y"])) == some "policy-call-line"
#guard refusal (withLines valueLines [] (callLines ++ ["callA X R8 Y"])) ==
  some "policy-call-line"
#guard refusal (withLines valueLines [] (callLines ++ ["callH X R8"])) == some "policy-call-line"
#guard refusal (withLines valueLines [] (callLines ++ ["callH ABCDEFGH R8 Y"])) == none
#guard refusal (withLines valueLines [] (callLines ++ ["callH ABCDEFGHI R8 Y"])) ==
  some "policy-call-line"
#guard refusal (withLines valueLines [] (callLines ++ ["callH X R8 Y!"])) ==
  some "policy-call-line"
#guard refusal (withLines valueLines [] (callLines ++ ["xl 5"])) == some "policy-xl"
-- a last line without its line feed
#guard refusal ((withLines valueLines [] callLines).extract 0
  ((withLines valueLines [] callLines).size - 1)) == some "policy-call-line"

-- a line of 1,024 bytes with its line feed is refused, one of 1,023 is admitted; a zero byte
#guard refusal (withLines valueLines [] (callLines ++
  ["callH X R8 " ++ String.join (List.replicate 1012 "Y")])) == some "policy-line-long"
#guard refusal (withLines valueLines [] (callLines ++
  ["callH X R8 " ++ String.join (List.replicate 1011 "Y")])) == none
#guard refusal (withLines valueLines [] callLines ++ ⟨#[0x58, 0, 0x0A]⟩) ==
  some "policy-zero-byte"
-- a sign before the number
#guard refusal (withLines (setLine valueLines 2 "L -8") [] callLines) == some "policy-line-4"
#guard refusal (withLines (setLine valueLines 2 "L +8") [] callLines) == some "policy-line-form"
-- the frame's lines. The first file is refused before a value line is read: the frame's reader
-- refuses it, since a row of 4294967296 + 65535 coordinates does not fit a code of length 2^23, and
-- that refusal has the same name as the test of the scan. No file fails that test:
-- OnBytes/Model/TestConfigOrder.lean says why. The other two files fail in the tests that are made
-- when the line F has been read.
#guard refusal (fileOf ((frameLines.dropLast ++ ["table 8 23 4294967296 65535 524288 11"]) ++
  valueLines)) == some "parameter-table-shape (policy)"
#guard refusal (fileOf ((frameLines.map fun l =>
  if l == "work positions 0 0 0" then "work positions 0 33 0" else l) ++ valueLines)) ==
  some "policy-work-most"
#guard refusal (fileOf ((frameLines.map fun l => if l == "slots 64" then "slots 512" else l) ++
  valueLines)) == some "policy-leafd"
-- the third of these tests is not made before the line F: without that line the file is refused as
-- policy-length. The other two tests are not tried in this way.
#guard refusal (fileOf ((frameLines.map fun l => if l == "slots 64" then "slots 512" else l) ++
  valueLines.dropLast)) == some "policy-length"
-- after the frame: a second frame; a second line version alone
#guard refusal (fileOf (frameLines ++ frameLines ++ valueLines)) == some "policy-line-2"
#guard refusal (fileOf (frameLines ++ ["version H821"] ++ valueLines)) == some "statement-required"
-- profile 3 has eleven value lines fewer than profile 4; only the two counts are compared
#guard (valueNames 3).length == 86 && (valueNames 4).length == 97
-- the refusal name for a fault in the frame's lines
#guard frameRefusal "parameter-range: slots" == "parameter-range (policy)"
#guard frameRefusal "version-unknown" == "version-unknown (policy)"
#guard frameRefusal "something else" == "internal-parameter-name"
-- a reason that begins with parameter- and is not in frameFaults; the frame's reader gives none.
-- The C++ routine would pass it on with the mark (policy); here the result stays in a fixed list.
#guard frameRefusal "parameter-of-no-list: x" == "internal-parameter-name"

/-! ## The list of names -/

#guard Config.names.length == 16 + 30 + 97 + 97 && Config.names.eraseDups.length == 240
#guard ["policy-line-2", "policy-line-98", "policy-name-prof", "policy-name-lt", "policy-name-F",
  "parameter-table-shape (policy)", "version-unknown (policy)"].all Config.names.contains
#guard !Config.names.contains "policy-line-99" && !Config.names.contains "policy-line-1"
#guard [PublicTable.silu, .sigmoid, .rope, .exp].all fun t => Config.names.contains t.refusal

/-! ## The tests after the scan -/

#guard nameOf (polBeforeLayout { read kit with nminH := some 20 }) == some "policy-nminH"
#guard nameOf (polBeforeLayout { read kit with nminH := some 21 }) == none
#guard nameOf (polBeforeLayout { read kit with h := { (read kit).h with tau := 224 } }) ==
  some "hid-tau"
#guard nameOf (polBehindLayout { read kit with h := { (read kit).h with tau := 96 } }) ==
  some "policy-tau-hb"
#guard nameOf (polBehindLayout
  { read kit with frame := { (read kit).frame with sec := 0 } }) == some "hid-hb"
#guard nameOf (polTablesAdmitted { read kit with h := { (read kit).h with NE := 0 } }) ==
  some "policy-tables"
#guard nameOf (polTablesAdmitted { read kit with h := { (read kit).h with prof := 3 } }) ==
  some "policy-tables"
#guard nameOf (polTablesAdmitted
  { read kit with h := { (read kit).h with prof := 3 }, tblPol := #[] }) == none
#guard [32, 64, 96, 128, 160, 192, 256].all tauServed
#guard !([0, 16, 33, 224, 288].any tauServed)
#guard nameOf (tableHeld (read kit) .rope #[1, 2, 3]) == some "table-digest-rope"
#guard nameOf (tableHeld (read (withLines valueLines [] callLines)) .rope #[1, 2, 3]) == none

/-! ## The scale file -/

#guard nameOf (klHeld (Fmt.zeroBytes 464)) == none
#guard nameOf (klHeld (Fmt.zeroBytes 463)) == some "KL-length"
#guard nameOf (klHeld (Fmt.zeroBytes 28)) == some "KL-length"
#guard klWord ⟨#[1, 2, 0, 0, 5, 0, 0, 0]⟩ 0 == 513
#guard klWord ⟨#[1, 2, 0, 0, 5, 0, 0, 0]⟩ 1 == 5
#guard klWord ⟨#[1, 2, 0, 0, 5, 0, 0, 0]⟩ 2 == 0

/-! ## The digests of the files

The digest of all three files (the two guards on hParOf) is the line h_par= that the C++ verifier
printed for the example's files: the parameter file and the scale file that are spelled out here,
and a layout file of 27,038 bytes that is not. The other values (the three files' digests and the
numbers of words 629, 116 and 6768) are intermediate values of that computation, which the C++
verifier does not print. They come from a copy of it to which only print statements were added.
Neither that copy nor what it printed is in the repository. So a run of the C++ verifier can confirm
the digest of all three files alone, and it needs the layout file, which this file does not hold. -/

/-- The words of the example's scale file: 13 for each of the 8 layers (shifts and scale exponents,
and last a word that is 1 if the layer rotates queries and keys), then 3 for each of the 4 layers
with experts. In the file each is a word of four bytes. -/
def klExample : List Nat :=
  [
   29, 29, 17, 7, 9, 13, 9, 44, 30, 44, 30, 12, 1, 29, 29, 17, 7, 9, 13, 9, 44, 30, 44, 30, 12,
   1, 29, 29, 17, 7, 9, 13, 9, 44, 30, 44, 30, 12, 1, 29, 29, 17, 7, 9, 13, 9, 44, 30, 44, 30,
   12, 0, 29, 29, 17, 7, 9, 13, 9, 44, 30, 44, 30, 12, 1, 29, 29, 17, 7, 9, 13, 9, 44, 30, 44,
   30, 12, 1, 29, 29, 17, 7, 9, 13, 9, 44, 30, 44, 30, 12, 1, 29, 29, 17, 7, 9, 13, 9, 44, 30,
   44, 30, 12, 0, 11, 8, 14, 11, 8, 14, 11, 8, 14, 11, 8, 14]

/-- The example's scale file. -/
def klFile : ByteArray := Fmt.cat (klExample.map word32)

/-- The eight words of a digest. -/
def wordsOf (d : ByteArray) : List Nat := (List.range 8).map fun i => Fmt.leNat d (4 * i) 4

/-- The digests of the example's parameter file and scale file, without a layout file. -/
def twoDigests : Option ParDigests := (parDigests kit klFile none).toOption

/-- The words of the digest of the example's layout file, which has 27,038 bytes, as the copy with
print statements printed them. No guard hashes the layout file. -/
def layWords : List Nat :=
  [2427701262, 3973524369, 1597712922, 1430491258, 2067087019, 1402384406, 1445739952, 4184149684]

#guard klFile.size == 464 && klWords klFile == 116
#guard twoDigests.map (wordsOf ·.kl) == some
  [438890904, 1679981941, 1078807581, 2778992839, 3387523273, 2309119043, 2371998561, 795484958]
#guard twoDigests.map (·.klW) == some 116
#guard twoDigests.map (·.layW) == some 0
#guard fileWords klFile == klExample.toArray
#guard fileWords ⟨#[1, 2, 0, 0, 5, 0, 0]⟩ == #[513]
#guard nameOf (klWhole klFile) == none && nameOf (klWhole ⟨#[1, 2, 0]⟩) == some "KL-length"

/-! ## The acceptance policies -/

#guard policyKind 256 256 0 15 8 4 == "exact-match"
#guard policyKind 257 256 0 15 8 4 == "clipped-gap"
#guard policyKind 256 256 1 15 8 4 == "clipped-gap"
#guard policyKind 256 256 0 4 8 4 == "exact-match"
#guard policyKind 300 299 0 4 8 4 == "clipped-gap"
#guard policyKind 300 299 0 15 8 15 == "log-probability"
#guard policyKind 256 256 0 15 8 15 == "log-probability"
#guard policyKind 300 299 0 15 8 14 == "another-table"
#guard aboveClip 32 256 256 0 8 == 0 && aboveClip 32 256 256 64 8 == 32
#guard aboveClip 32 256 256 31 8 == 31 && aboveClip 0 256 256 64 8 == 0
#guard aboveClip 32 100000 40000 64 8 == 12 && aboveClip 3 100000 40000 64 8 == 1
#guard aboveClip 2 100000 40000 64 8 == 0 && aboveClip 32 100000 40000 3 8 == 3
#guard aboveClip 32 100000000 4000000 0 8 == 0 && aboveClip 10 300 299 10 8 == 9
#guard aboveClip 10 300 200 10 8 == 0 && aboveClip 10 200 200 4 8 == 4
#guard policyNamedRead "exact-match,256,256,0,15,8" == some ⟨"exact-match", 256, 256, 0, 15, 8⟩
#guard (policyNamedRead "exact-match,256,256,0,15,8").any (·.is 256 256 0 15 8 4)
#guard !(policyNamedRead "clipped-gap,512,300,1,15,8").any (·.is 256 256 0 15 8 4)
#guard policyNamedRead "another-table,256,256,0,15,8" == none
#guard policyNamedRead "log-probability,300,299,0,15,8" == none
#guard (policyNamedRead "clipped-gap,300,299,0,15,8").isSome
#guard policyEmpty 1 256 256 0 8 == 0 && policyEmpty 0 255 255 0 8 == 1
#guard policyEmpty 0 300 255 0 8 == 2 && policyEmpty 0 256 257 0 8 == 3
#guard policyEmpty 3 256 256 3 8 == 4 && policyEmpty 4 256 256 3 8 == 0
#guard policyEmpty 0 256 256 3 8 == 0 && policyEmpty 500 4096 300 10 8 == 0
#guard policyEmpty 1 128 128 0 7 == 0 && policyEmpty 1 128 128 0 8 == 1
#guard policyNamedRead "exact-match,256,256,0,15" == none
#guard policyNamedRead "exact-match,256,256,0,15,8," == none
#guard policyNamedRead "exact-match,256,256,00,15,8" == none
#guard policyNamedRead "exact-match,256,256,0,15,12345678901" == none
#guard policyNamedRead "exact-match,256, 256,0,15,8" == none
#guard rotaryServed 10000 128 6 && rotaryServed 500000 64 10 && !rotaryServed 10001 128 6

end OnBytes.Model.TestConfig
