-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Tokens.lean: the user's request and reply as a prompt, output tokens and further tokens.

A request file holds T tokens and two more words, r and e; a reply file holds one word, y. For each
of the positions r to e - 1 the program lays a token beside the position (`Model.Head.coveredOf`,
the field `hWin`): the next token of the request, or the reply at the last position.
  `tokensOf`, `rOf`, `eOf`, `yOf`: the words as the program reads them (`Model.Verify.words32`, and
    `Model.Head.stFromCall`'s own three terms), with T taken as the number of words less two.
  `promptOf`: the tokens at the positions 0 to r.
  `outputOf`: these e - r tokens: the tokens at the positions r + 1 to e; if e = T the last of them
    is the reply.
  `auxOf`: the tokens behind them, at the positions e + 1 to T - 1.
Definitions only; the laws are in OnBytes/K/TokensLaws.lean and OnBytes/K/TokensCovered.lean, whose
head says what the head's check reads in the place of `hWin`.
A token is a natural number here, as in the front's statements.


-/
import OnBytes.K.Stm

set_option autoImplicit false

namespace OnBytes.K

open OnBytes OnBytes.Model OnBytes.Model.Verify

/-- The number of tokens of the request: its words less two. -/
def windowOf (x : UserStm) : Nat := (words32 x.request).size - 2

/-- The request's tokens. -/
def tokensOf (x : UserStm) : List Nat :=
  ((words32 x.request).toList.take (windowOf x)).map (·.toNat)

/-- The first covered position. -/
def rOf (x : UserStm) : Nat := ((words32 x.request).getD (windowOf x) 0).toNat

/-- The position after the last covered one. -/
def eOf (x : UserStm) : Nat := ((words32 x.request).getD (windowOf x + 1) 0).toNat

/-- The reply. -/
def yOf (x : UserStm) : Nat := ((words32 x.y).getD 0 0).toNat

/-- The prompt: the tokens at the positions 0 to r. -/
def promptOf (x : UserStm) : List Nat := (tokensOf x).take (rOf x + 1)

/-- The output: the tokens that `coveredOf` lays beside the positions r to e - 1. -/
def outputOf (x : UserStm) : List Nat :=
  ((tokensOf x).drop (rOf x + 1)).take (eOf x - rOf x) ++
    (if eOf x = windowOf x then [yOf x] else [])

/-- The further tokens of the request. -/
def auxOf (x : UserStm) : List Nat := (tokensOf x).drop (eOf x + 1)

end OnBytes.K
