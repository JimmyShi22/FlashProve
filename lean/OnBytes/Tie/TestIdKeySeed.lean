-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/TestIdKeySeed.lean: tests of OnBytes/Tie/IdKeySeed.lean: the commitment ID's string with
the record's seed in it and a last list at its end, as that file writes it, gives the known answers
of the format's rule.

Rule R4.11 of the format page (docs/format/FORMAT.md) lays the record's seeds into the commitment
ID's input and ends it with a last list, which by the page is empty. It comes with three known
answers: with no seed and no answer; with one given seed and two answers; and with the toy name's
own seed, drawn and not given (R4.8), and the same two answers. Here each of the three is asked of
`idAtS` at the format's own oracle, at a key with the page's toy configuration, root and shape; for
the third the seed is drawn by the program's own `recordSeeds` at the toy table's name. So at these
three inputs `idBytesS` gives the rule's hash. A fourth value, with seven digests in the last list,
is no known answer of the page: it is this library's own, kept so that a change in the coding of a
list that is not empty is seen.

What is checked when the file compiles: 15 tests (#guard). No theorem. The hash stands here as one
fixed function, for a test alone: nothing is proved of it, and no theorem of the library rests on
this file.
What is not claimed. Three inputs are three inputs: that the two spellings agree everywhere is not
shown; equal hashes are not equal strings. The toy name's second word is 512 and its fourth 9, so a
seed's point has nine coordinates and the table 512 rows. The second and the fourth value test the
coding alone: a point of two coordinates and two answers fit no such name. The third fits the name
in its seed, not in its answers. That the programs compute these values is the page's word. For
tests only; the program does not import this file.


-/
import OnBytes.Tie.IdKeySeed

set_option autoImplicit false

namespace OnBytes.Tie.IdKeySeedTest

/-- The toy key: the page's configuration (one public file, "toy" and a line feed), root and shape,
with a seed, answers and a last list. -/
def key (seed answers : List E) (told : List ByteArray) : IdKeyS :=
  ⟨({ code := ⟨10, 512, 40⟩, v := 9, answers := 1, saltBytes := 40 }, Fmt.Toy4.cfg,
    { root := Fmt.pattern 32 13 4, answers := answers }), seed, told⟩

/-- One seed, laid flat: the point (7, 8, 9), (10, 11, 12), then the factor (13, 14, 15). -/
def seed1 : List E := [E.mk3 7 8 9, E.mk3 10 11 12, E.mk3 13 14 15]

/-- The two answers (1, 2, 3) and (4, 5, 6). -/
def two : List E := [E.mk3 1 2 3, E.mk3 4 5 6]

/-- The seven digests H(169, 0, 1, none; the byte k), k = 1 to 7. -/
def seven : List ByteArray := (List.range 7).map fun k => Fmt.paramsDigest ⟨#[UInt8.ofNat (k + 1)]⟩

/-- The toy name's own seed (R4.8), drawn by the program's `recordSeeds` at the toy table's name and
laid flat: the nine coordinates of its point, then its factor. Nothing if the drawing fails. -/
def drawn : Option (List E) :=
  let k := key [] two []
  (recordSeeds .two (Key.nameOf k.base.1 k.base.2.1 k.base.2.2) k.base.1.cubeBits
    k.base.1.answers).map fun l => l.flatMap fun y => y.1 ++ [y.2]

-- the rule's three known answers
#guard Fmt.hex (idAtS Fmt.oracle (key [] [] [])) ==
  "80d59c8b07aaa71829c9765057082a108618402daf661caf2c390c09dfafddd3"
#guard Fmt.hex (idAtS Fmt.oracle (key seed1 two [])) ==
  "4fb918a30faa7643cf8e6bc431c6643d7b5b4cc298dd0531cc0206bb4f756a0b"
-- the third: the name's own seed, drawn and not given: ten elements
#guard drawn.map List.length == some 10
#guard (drawn.map fun s => Fmt.hex (idAtS Fmt.oracle (key s two []))) ==
  some "e18438e0725ec651fc8bffa3b3f860ddeca70e6cb1991dd43620b98ef6f05bd2"
-- a fourth value, this library's own: with a last list that is not empty
#guard Fmt.hex (idAtS Fmt.oracle (key seed1 two seven)) ==
  "db39e7b8cd3090f9e90be48d0e2966065c59b8253336782446ad92ab20e033a7"
-- the same by the format's hash on the bytes
#guard Fmt.hex (Fmt.formatHash 179 0 0 Fmt.zero32 (idBytesS (key seed1 two seven))) ==
  "db39e7b8cd3090f9e90be48d0e2966065c59b8253336782446ad92ab20e033a7"
-- each of the four keys has a code
#guard idOkS (key [] [] []) && idOkS (key seed1 two []) && idOkS (key seed1 two seven)
#guard (drawn.map fun s => idOkS (key s two [])) == some true
#guard (idCodeS (key seed1 two seven)).isSome
-- a told digest of 31 bytes: no code
#guard idOkS (key seed1 two [Fmt.pattern 31]) == false
-- the bytes with no seed and no answer: 176 with the empty list, 400 with seven digests
#guard (idBytesS (key [] [] seven)).size == 400
#guard (idBytesS (key [] [] [])).size == 176
-- a seed's element, an answer and a digest cost 24, 24 and 32 bytes
#guard (idBytesS (key seed1 two seven)).size == 400 + 3 * 24 + 2 * 24
-- the seed and the answers are not exchangeable, and an element moved from one list to the other
-- gives another ID
#guard Fmt.hex (idAtS Fmt.oracle (key two seed1 [])) !=
  Fmt.hex (idAtS Fmt.oracle (key seed1 two []))
#guard Fmt.hex (idAtS Fmt.oracle (key (seed1 ++ [E.mk3 1 2 3]) [E.mk3 4 5 6] [])) !=
  Fmt.hex (idAtS Fmt.oracle (key seed1 two []))

end OnBytes.Tie.IdKeySeedTest
