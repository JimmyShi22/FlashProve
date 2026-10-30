-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/InsReqRun.lean: insReq (Johnson/Top/InsReq.lean) and the program's own reader of request
and reply, by evaluation at made-up statements.

Everything here is a run. A line "#guard" is evaluated when this file is compiled, by Lean's
interpreter, and the compilation fails if the value is not true. It is no theorem, and it says
nothing of other statements.

What is run. A statement with a request file of 1,024 made-up tokens (token t is t modulo 7), r and
e, and a reply file of one word; the three public files are empty: insReq reads none of them.
 1. The two premises of insReq_words (Johnson/Top/InsReqWords.lean) hold together: the reader
    stFromCall and the routine coveredOf return, at the reference's window and vocabulary; and
    insReq returns the instance with these r, e, y and tokens. At e = 1,024 with a reply, at e
    before the window's end with the reply 0, and at r = 1,023, e = 1,024 (the next token alone).
 2. Refusals: at r = e, and at a token that is not below the vocabulary's size, the pair of reader
    and routine refuses, and insReq refuses.
 3. WHERE THE TWO PART. At e before the window's end and a reply that is not 0 the reader refuses,
    and insReq returns the instance with y = 0: the three lists of OnBytes/K/Tokens.lean do not hold
    the reply there. At a request file of another length (10 tokens, r = 3, e = 10) the reader
    refuses, and insReq returns an instance with the reply as token 10 of the window. So "insReq
    returns" says less than "the reader takes the files": every law on insReq has the reader's
    return as a premise, or is an equation for all statements.

-/
import Johnson.Top.InsReq

set_option autoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.OnPublicFiles.Flat.InsReqRun

open Inst.Model
open OnBytes OnBytes.Model OnBytes.Model.Verify

/-- Numbers as a file of 32-bit words. -/
def fileOfWords (l : List Nat) : ByteArray := l.foldl (fun b n => b ++ word32 n) ByteArray.empty

/-- A made-up statement with n tokens: token t is tok t. -/
def stmN (n : Nat) (tok : Nat → Nat) (r e y : Nat) : K.UserStm :=
  ⟨ByteArray.empty, ByteArray.empty, ByteArray.empty,
    fileOfWords ((List.range n).map tok ++ [r, e]), fileOfWords [y], {}⟩

/-- The same with 1,024 tokens. -/
def stm (tok : Nat → Nat) (r e y : Nat) : K.UserStm := stmN 1024 tok r e y

/-- Whether the program's reader and its routine on the covered positions return. -/
def readerTakes (x : K.UserStm) : Bool :=
  match Head.stFromCall (words32 x.request) (words32 x.y) ppref.T with
  | .ok so => (Head.coveredOf so ppref.T ppref.V).toBool
  | .error _ => false

/-- r, e, y and four tokens of what insReq returns. -/
def told (x : K.UserStm) : Option (Nat × Nat × Nat × List Nat) :=
  (insReq x).map fun q => (q.val.r, q.val.e, q.val.y.val, [0, 5, 700, 1023].map q.val.tok)

-- 1. both return, with the files' numbers
#guard readerTakes (stm (· % 7) 3 1024 9)
#guard told (stm (· % 7) 3 1024 9) == some (3, 1024, 9, [0, 5, 0, 1])
#guard readerTakes (stm (· % 7) 10 20 0)
#guard told (stm (· % 7) 10 20 0) == some (10, 20, 0, [0, 5, 0, 1])
-- the next token alone: r = 1,023, e = 1,024
#guard readerTakes (stm (· % 7) 1023 1024 9)
#guard told (stm (· % 7) 1023 1024 9) == some (1023, 1024, 9, [0, 5, 0, 1])
-- 2. the pair refuses, and insReq refuses
#guard !readerTakes (stm (· % 7) 20 20 0) && (told (stm (· % 7) 20 20 0)).isNone
#guard !readerTakes (stm (fun t => if t = 700 then 202048 else 0) 3 1024 9) &&
  (told (stm (fun t => if t = 700 then 202048 else 0) 3 1024 9)).isNone
-- 3. where the two part
#guard !readerTakes (stm (· % 7) 10 20 9)
#guard told (stm (· % 7) 10 20 9) == some (10, 20, 0, [0, 5, 0, 1])
#guard !readerTakes (stmN 10 (· % 7) 3 10 9)
#guard (insReq (stmN 10 (· % 7) 3 10 9)).map (fun q => (q.val.r, q.val.e, q.val.y.val,
  [9, 10, 11].map q.val.tok)) == some (3, 10, 0, [2, 9, 0])

end VerifiableInference.OnPublicFiles.Flat.InsReqRun
