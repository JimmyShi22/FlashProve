-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Fmt/M2Items.lean: parameters of the second toy as bytes: the parameter items "codes" and "the chain
of links", and its public file, spelled from the sizes.

The second toy is a small test protocol, a chain of three links; the head of Fmt/M2Dec.lean says
what it is. The first hash query of a proof's chain takes in the digest of the parameter bytes.
These hold the plan (Fmt/M2Plan.lean), the digest of the public file, and two further items. This
file spells the two items (`itemsOf`) and the public file from the record `Par` of Fmt/M2Types.lean,
the public file also from its first line, the target and the number of nonce bytes. It has
definitions that compute, with tests, and uses no Mathlib, neither directly nor through its imports.

Sources. Written from the format page (docs/format/FORMAT.md, which comes with the programs) as it
stood in an edition of the page that is not the one that ships (not held against the page
that ships): R12.12 (a message of a link: six words), R12.13 (a link: one word and the list
of
its messages), R12.14 (a chain of links), R12.15 (the run named "links": label 2; three items:
configuration, codes, the chain of links; the lines of the public file), together with R12.2 to
R12.5 as Fmt/M1Codes.lean, Fmt/M1Plan.lean and Fmt/M1ParOf.lean render them. A second
edition of the page, also not the one that ships, was compared with that one by a program:
R12.2 to R12.5 and R12.12 to R12.14 are the same letter for letter, and of R12.15 only the
last sentence differs (the second edition points to R12.16 to R12.18 for the rounds and the
cuts). None of these rules differs between that edition and a third, also not the one that
ships.

1. What the file contains.
   `linkMsgBytes m moment life`: a message of a link, six words: main rows; 1 if they are over F or
     if there are none, 3 if they are over E; mask rows; leaf class (0); moment; life.
   `msgsOf L m`: the messages of link m. These are not the members of its group, which also holds
     what is carried and what is sent anew. They are b_m (with x_1 at the first link), with a mask
     row and life 0, and c_m, without a mask row, kept for one later link unless m is the last.
   `linkBytes`, `chainBytes P`: a link: one word for its plain scalars, then the list of its
     messages. The chain: the numbers of the links' two codes; the list of links, each with no plain
     scalar; no notice at the start; one answer; the stages of the last proximity test from the
     second on, four words each; the one word of the choices.
   `publicFile first target P nonceB`: the public file, line by line.

2. What is checked when the file compiles (14 #guard tests).
   The item's words at the full and at the tiny parameters, by a reading of the rules.
   Against the page's three test vectors, at the second edition named under Sources: the 456 bytes
   of the item "the chain of links"
   at the tiny parameters; its groups' k, h, sampled messages and widths (here `kOf`, `hOf`, `nAns`,
   `widthOf` of Fmt/M2Types.lean); its 58 rounds by first letters and lengths of messages (here
   `planOf` of Fmt/M2Plan.lean).
   Against the programs (the C++ implementation that comes with this Lean code): the length and the
   digest of the complete parameter bytes at the full and at the tiny parameters, as the second
   issue of their description of this toy prints them. The bytes themselves are compared with the
   programs' files in Fmt/M2Theirs.lean.

3. Theorems. None in this file. The sizes and the description can be read back from the parameter
   bytes (`par_back`, `read_back`, `spec_back`: stated in Fmt/M2ParOfLaws.lean, proved in
   Fmt/M2ParOfLawsProofs.lean), under the hypotheses stated there (`P.small`, a test on the sizes;
   for the later statements also that the parameters fit and that the description is admissible).

4. What is not claimed.
   The number of answers to a sample stands twice in the parameters, as R12.14 itself remarks: in
   this item and in the plan's sixth word. Here these are two constants 1 that agree (`chainBytes`;
   `planOf` in Fmt/M2Plan.lean). Nothing ties them together except the tests on the complete bytes.
-/
import Fmt.M2Plan
import Fmt.M1ParOf

namespace Fmt
namespace M2
open Fmt.M1

def nameLinks : String := "the chain of links"

/-- a message of a link: six words -/
def linkMsgBytes (m : Mem) (moment life : Nat) : ByteArray :=
  cat ([m.rows, if m.overE && m.rows != 0 then 3 else 1, m.masks, 0, moment, life].map u64n)

/-- the messages of link m: (message, moment, life) -/
def msgsOf (L m : Nat) : List (Mem × Nat × Nat) :=
  [(memB m, 0, 0), (memP false, 0, if m < L then 1 else 0)]

/-- a link: its plain scalars; the list of its messages -/
def linkBytes (plain : Nat) (ms : List (Mem × Nat × Nat)) : ByteArray :=
  u64n plain ++ u64n ms.length ++ cat (ms.map fun x => linkMsgBytes x.1 x.2.1 x.2.2)

/-- The bytes of the item "the chain of links". -/
def chainBytes (P : Par) : ByteArray :=
  let cm := onceL (P.stages.map (·.C))
  let cz := onceL (P.stages.map (·.Z))
  u64n (noIn cm P.C) ++ u64n (noIn cz P.Z) ++ u64n P.links ++
    cat ((List.range P.links).map fun i => linkBytes 0 (msgsOf P.links (i + 1))) ++ u64n 0 ++
    u64n 1 ++ stagesBytes ((P.stages.drop 1).map fun s => (noIn cm s.C, noIn cz s.Z, s.k, s.h)) ++
    choicesBytes true

/-- The two further items, from the sizes. -/
def itemsOf (P : Par) : List (String × ByteArray) :=
  [(nameCodes, codesItem (P.stages.map (·.C)) (P.stages.map (·.Z))), (nameLinks, chainBytes P)]

/-- The run's public file: lines, each ended by a line feed. -/
def publicFile (first : String) (target : Nat) (P : Par) (nonceB : Nat := 8) : ByteArray :=
  ascii (String.join
    (([first, s!"format H8{P.fld.num}1", s!"target {target}",
          s!"work-on-positions {P.work}", s!"salt-bytes {P.salt}", s!"nonce-bytes {nonceB}",
          "position-bytes 0", "samples 1", s!"links {P.links}",
          s!"log-length {Nat.log2 P.C.l}", s!"log-n {P.C.a}", s!"mask-log-n {P.Z.a}"] ++
        (P.stages.drop 1).map fun s => s!"stage {s.k} {s.h} {s.C.a} {s.Z.a}").map (· ++ "\n")))

/-- a string of whole words, as numbers -/
def wordsOf (b : ByteArray) : List Nat :=
  (List.range (b.size / 8)).map fun i =>
    ((List.range 8).map fun j => (b.get! (8 * i + j)).toNat * 256 ^ j).sum

-- the item's words, by a reading of R12.12 to R12.14: 57 words
#guard wordsOf (chainBytes toyPar) == [0, 0, 3,  0, 2,  2, 1, 1, 0, 0, 0,  1, 1, 0, 0, 0, 1,   0, 2,  1, 1, 1, 0, 0, 0,  1, 1, 0, 0, 0, 1,   0, 2,  1, 1, 1, 0, 0, 0,  1, 1, 0, 0, 0, 0,   0,  1,  2,  1, 1, 1, 1,  1, 2, 0, 0,  1]
#guard wordsOf (chainBytes tinyPar) == [0, 0, 3,  0, 2,  2, 1, 1, 0, 0, 0,  1, 1, 0, 0, 0, 1,   0, 2,  1, 1, 1, 0, 0, 0,  1, 1, 0, 0, 0, 1,   0, 2,  1, 1, 1, 0, 0, 0,  1, 1, 0, 0, 0, 0,   0,  1,  2,  1, 1, 1, 1,  2, 2, 0, 0,  1]
-- the item "codes": the text's own print at the full and at the tiny parameters (its form has not
-- moved)
#guard wordsOf ((itemsOf toyPar).lookup nameCodes |>.getD ByteArray.empty) == [2, 15, 4096, 73, 14, 2048, 74, 3, 15, 32, 73, 14, 256, 74, 14, 1024, 74]
#guard wordsOf ((itemsOf tinyPar).lookup nameCodes |>.getD ByteArray.empty) == [3, 9, 64, 3, 9, 32, 3, 10, 32, 3, 3, 9, 16, 3, 9, 32, 3, 10, 128, 3]
-- the public files: the text's own lines at the full and at the tiny parameters
#guard publicFile "run links" 128 toyPar == ascii "run links\nformat H821\ntarget 128\nwork-on-positions 20\nsalt-bytes 40\nnonce-bytes 8\nposition-bytes 0\nsamples 1\nlinks 3\nlog-length 12\nlog-n 15\nmask-log-n 15\nstage 1 1 14 14\nstage 0 0 14 14\n"
#guard publicFile "run links, tiny edition: a test size that reaches no security level" 10 tinyPar == ascii "run links, tiny edition: a test size that reaches no security level\nformat H821\ntarget 10\nwork-on-positions 6\nsalt-bytes 40\nnonce-bytes 8\nposition-bytes 0\nsamples 1\nlinks 3\nlog-length 6\nlog-n 9\nmask-log-n 9\nstage 1 1 9 9\nstage 0 0 10 10\n"
-- the configuration's digests in a wording of the text are those of these public files
#guard hex (configDigest [publicFile "run links" 128 toyPar]) == "243697d0866750794a648ce915dd7da1c94408b77a9eadacce5e2a2cd872757a"
#guard hex (configDigest [publicFile "run links, tiny edition: a test size that reaches no security level" 10 tinyPar]) == "27d791a36fff70de9c37b638550e3a2daf85a40aeb723fd8362bb18d60704126"
#guard (specOf toyPar zero32 (itemsOf toyPar)).ok && (specOf tinyPar zero32 (itemsOf tinyPar)).ok
-- the whole of the parameters' bytes (version, plan, configuration, codes, the chain of links):
-- length and digest as the programs' text, revised version, and their files' digests.tsv print them
-- (met by this file and by this library's own reference program in Python, which another writer
-- wrote apart from
-- this file, from the page's rules, not from that version or the files)
#guard (let P : Par := tinyPar; let b := (specOf P (configDigest [publicFile "run links, tiny edition: a test size that reaches no security level" 10 P]) (itemsOf P)).params; (b.size, hex (formatHash 169 0 1 zero32 b))) == (6878, "59922437150dbd2232f5986d9c1b939e1639a1e7b145989202984f34a08c1161")
#guard (let P : Par := toyPar; let b := (specOf P (configDigest [publicFile "run links" 128 P]) (itemsOf P)).params; (b.size, hex (formatHash 169 0 1 zero32 b))) == (8744, "9b25d5f4e5adf08c456bf0cbd7ba184a7ce04c5b54e8ddb311a9c8fdbb365aab")

/-- a round's name in short: the first letters of its words -/
def shortOf (n : String) : String :=
  String.ofList ((n.splitOn " ").filterMap fun w => w.toList.head?)

/-- the rounds in the page's short form: first letters and the message's bytes; of the last round
the letters alone -/
def roundsShort (P : Par) : Nat × String :=
  let es := (planOf P).entries
  (es.length,
    " ".intercalate
      ((es.dropLast.map fun e => shortOf e.name ++ toString e.msg) ++
        (es.getLast?.map fun e => shortOf e.name).toList))

-- the page's three known answers on a chain of links (the second edition of the page, named in the
-- head under Sources; its vectors' lines on section 12):
-- the item at the tiny parameters, 456 bytes
#guard hex (chainBytes tinyPar) == "000000000000000000000000000000000300000000000000000000000000000002000000000000000200000000000000010000000000000001000000000000000000000000000000000000000000000000000000000000000100000000000000010000000000000000000000000000000000000000000000000000000000000001000000000000000000000000000000020000000000000001000000000000000100000000000000010000000000000000000000000000000000000000000000000000000000000001000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000200000000000000010000000000000001000000000000000100000000000000000000000000000000000000000000000000000000000000010000000000000001000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000200000000000000010000000000000001000000000000000100000000000000010000000000000002000000000000000200000000000000000000000000000000000000000000000100000000000000"
-- its groups: k, h, sampled messages, width of a column
#guard [1, 2, 3, 4].map (fun m => (kOf (memsOf 3 m), hOf (memsOf 3 m), nAns tinyPar m, widthOf (memsOf 3 m) (2 ^ hOf (memsOf 3 m)))) == [(1, 0, 2, 9), (2, 0, 4, 15), (3, 0, 4, 15), (1, 0, 1, 9)]
-- its rounds with 5 variables: how many; the names' first letters and the messages' bytes
#guard roundsShort tinyPar == (58, "Ss32 Sa48 Z0 Pe24 Pr48 Pr48 Pr48 Pr48 Pr48 PY48 Pv48 B0 Fe24 Fr48 Ss32 L96 Z0 Pe24 Pr48 Pr48 Pr48 Pr48 Pr48 PY48 Pv48 B0 Fe24 Fr48 Fr48 Ss32 L96 Z0 Pe24 Pr48 Pr48 Pr48 Pr48 Pr48 PY48 Pv48 B0 Fe24 Fr48 Fr48 Fr48 Ss32 L24 B0 Fe24 Fr48 Ss32 C24 Fe24 Fr48 Ss32 C24 Bl24 B")

end M2
end Fmt
