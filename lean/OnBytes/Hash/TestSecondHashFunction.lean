-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Hash/TestSecondHashFunction.lean: tests of OnBytes/Hash/SecondHashFunction.lean.

The known answers are those that the format page's list of known answers
(docs/format/format-vectors.txt) prints for R15.3 and R15.4. The program does not import this
file.
-/
import OnBytes.Hash.SecondHashFunction

namespace OnBytes.HashTest

/-- The test list of n words: word i is 2654435761 (i + 1) modulo 2^32. -/
def wordsN (n : Nat) : ByteArray :=
  Fmt.cat ((List.range n).map fun i => word32 (2654435761 * (i + 1) % 2 ^ 32))

#guard Fmt.hex (secondHashFunction 73 (wordsN 0)) ==
  "42ebee096e6993eb980d0699b1e9054a7ef899dd07e2a51b194653dda48bfa9d"
#guard Fmt.hex (secondHashFunction 73 (wordsN 1)) ==
  "c704e619f8ff740149d04ba40356f3a148c832c7f4ca7537ae60caeb8a0c8381"
#guard Fmt.hex (secondHashFunction 10 (wordsN 32)) ==
  "4293420bb394a03740402691d1536980e5c963d914493c53c7c618a878dda211"
#guard Fmt.hex (secondHashFunction 10 (wordsN 33)) ==
  "19334616773a974199370db603347a0512452b434919816669ee67ca7c33c8fc"
#guard Fmt.hex (secondHashFunction 11 (wordsN 128)) ==
  "fd3c951f6455349e9bf4d19055140e3eb177b0a09d3ce13fbf39ef2063d39b87"
-- with the number 0 and no word: the first 32 bytes of BLAKE2b-512 of the empty string
#guard Fmt.hex (secondHashFunction 0 ByteArray.empty) ==
  "786a02f742015903c6c6fd852552d272912f4740e15847618a86e217f71f5419"
#guard (secondHashFunctionTree (wordsN 8)).map Fmt.hex ==
  some "5bcae6252f596216e6004753c4110b936facd0bcabed7f466049d4440ae7911d"
#guard (secondHashFunctionTree (wordsN 128)).map Fmt.hex ==
  some "be776895186e02f56459f75619d4e1acc44da0aeb66354cbf04383020d52ec01"
#guard (secondHashFunctionTree (wordsN 129)).map Fmt.hex ==
  some "10fd9618e3cd54887dd110377a873452db2d579d942038914c0f9c7063851eeb"
#guard (secondHashFunctionTree (wordsN 1024)).map Fmt.hex ==
  some "839c93378f27f55f08ce04ffea45bae3ed1f4d532f0eca1ca5377206c5366b3f"
#guard (secondHashFunctionTree (wordsN 1025)).map Fmt.hex ==
  some "8fdf83e4e0333c00a67be807b77d37d8af0a9a0e02a50854507803ec8914c106"
-- three levels
#guard (secondHashFunctionTree (wordsN 16385)).map Fmt.hex ==
  some "3466253ff6b47dc4b23aa37cb4c391acc4255e3c2873c85612d2e05ed57a4a8d"
-- fewer than eight words, or a length that is not a multiple of four
#guard (secondHashFunctionTree (wordsN 7)).isNone && (secondHashFunctionTree ((wordsN 9).extract 0 33)).isNone
#guard Fmt.hex (textWords "call a b c\n".toUTF8) == "63616c6c2061206220630a00"
#guard Fmt.hex (secondHashFunction 73 (textWords "call a b c\ncall d e\n".toUTF8)) ==
  "31b1983630140f5dc2bb43281a54d5d4af9b6e2daf0a272d4e3c453e2fe19e9f"

end OnBytes.HashTest
