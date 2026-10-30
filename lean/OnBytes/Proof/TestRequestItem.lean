-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Proof/TestRequestItem.lean: tests of OnBytes/Proof/RequestItem.lean.

The two digests of texts are known answers of the format page's list
(docs/format/format-vectors.txt, R15.x). The digest of a whole item was computed by the
format page's own program (docs/format/format_rules.py, statement_words and older_TK) from the
same three files: it pins the five digests, and the names' order where their numbers differ
(the twelve lines wb_ are all 13, for one). The program does not import this file.
-/
import OnBytes.Proof.RequestItem
import OnBytes.Model.TestConfig

namespace OnBytes.Proof.Test

#guard Fmt.hex (secondHashFunction 73 (textWords callHIfNone.toUTF8)) ==
  "81ada2ab58dec481e7a90db30e5ed93b55ed538ef8f6ceb30a1cc5ed19fff783"

/-- A small text in the form of a parameter file. -/
def someLines : ParamLines :=
  ParamLines.read "sec 128\ncall a b c\ncallA q\nlt 6\ncall d e\nlt 7\nx 01\nL 8\n".toUTF8

#guard someLines.value "L" == some 8 && someLines.value "sec" == some 128
-- a name in two lines, a leading zero, a name in no line
#guard someLines.value "lt" == none && someLines.value "x" == none && someLines.value "y" == none
#guard someLines.text "call" == "call a b c\ncall d e\n".toUTF8
#guard (someLines.calls "call").map Fmt.hex ==
  some "31b1983630140f5dc2bb43281a54d5d4af9b6e2daf0a272d4e3c453e2fe19e9f"
-- a name is compared whole: the line callA is no line call; no line callH, without and with a text
#guard someLines.text "callA" == "callA q\n".toUTF8
#guard someLines.calls "callH" == none
#guard (someLines.calls "callH" (some callHIfNone)).map Fmt.hex ==
  some "81ada2ab58dec481e7a90db30e5ed93b55ed538ef8f6ceb30a1cc5ed19fff783"
-- the largest number that a word holds, and the next
#guard (ParamLines.read "a 4294967295\nb 4294967296\n".toUTF8).value "a" == some 4294967295
#guard (ParamLines.read "a 4294967295\nb 4294967296\n".toUTF8).value "b" == none
-- the last five words: the line sec; then w, b, n, m of the line table b n i m e w
#guard (ParamLines.read "sec 128\ntable 1 2 3 4 5 6\n".toUTF8).lastWords ==
  some (Fmt.cat ([128, 6, 1, 2, 4].map word32))
-- a line with two blanks in a row, or with a blank at its end, comes back byte for byte
#guard (ParamLines.read "call a  b \ncall\n".toUTF8).text "call" == "call a  b \ncall\n".toUTF8
#guard splitAt 0x20 "a  b ".toUTF8.toList == ["a", "", "b", ""].map (·.toUTF8.toList)
#guard splitAt 0x20 [] == [[]]
#guard (names2.splitOn " ").length == 27 && (names37.splitOn " ").length == 34
#guard (names103.splitOn " ").length == 11 && (names130.splitOn " ").length == 25

/-- A request of 64 tokens with its two last words. -/
def request : ByteArray := Fmt.cat ((List.range 64).map word32 ++ [word32 63, word32 64])

/-- The item from TestConfig.lean's parameter file and scale file, and that made-up request. -/
def item : Option ByteArray := requestItem Model.TestConfig.kit Model.TestConfig.klFile request

#guard item.map (·.size) == some 708
#guard (item.bind secondHashFunctionTree).map Fmt.hex ==
  some "15f41f439b2df63f8f5a49de49abb38ab23cfb8d13393bb6323a5b1201380cbd"
-- a request of another length
#guard (requestItem Model.TestConfig.kit Model.TestConfig.klFile (request ++ word32 0)).isNone

end OnBytes.Proof.Test
