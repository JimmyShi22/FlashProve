-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/KeyBack/BrokenLiteral.lean: a string literal that is broken over two lines of source
is another string. Two closed facts on one literal.

Why this file is there. Johnson/AtFull/KeyBack/BoundsCanFail.lean restates `small_full`
(Johnson/AtFull/KeyBack/WrittenItems.lean), a bound on a sum of eighteen numbers; one of them is the
number of bytes of the name "the test on the table". Lean takes a line break inside a literal, and
the blanks that open the next line, into the string. With that literal broken behind its fourth
word, the statement that is compiled speaks of a sum greater by six: it is true, and it is not the
statement that a reader takes it for. A comparison of the two texts with blanks folded does not see
the difference.

`literal_whole`: the name has 21 bytes. `literal_broken`: with a line break and six blanks for its
fourth blank it has 27. Here the break is written as an escape, so that no literal is broken in this
source.

What follows, by reading alone. The sum of `small_full` in the broken spelling is greater by six
than in the whole one. The two statements "below 2 ^ 10" are then about two different closed
numbers, and a proof of the one is no term of the other's type. That is why the `example` behind
`small_big` in BoundsCanFail.lean, which is closed by `small_full` itself, can fail.

Limits. Two facts on one literal. Nothing on any files. Nothing on soundness.
-/
import Johnson.AtFull.KeyBack.WrittenItems

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.KeyBack

/-- The name as `small_full` has it: 21 bytes. -/
theorem literal_whole : (Fmt.ascii "the test on the table").size = 21 := by decide +kernel

/-- With a line break and six blanks for its fourth blank: 27 bytes. -/
theorem literal_broken : (Fmt.ascii "the test on the\n      table").size = 27 := by decide +kernel

end Johnson.AtFull.KeyBack

#print axioms Johnson.AtFull.KeyBack.literal_whole
#print axioms Johnson.AtFull.KeyBack.literal_broken
