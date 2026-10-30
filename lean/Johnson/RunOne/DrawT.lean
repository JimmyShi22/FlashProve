-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/DrawT.lean: what a round draws from its hash blocks, in a form made for a run: the
blocks' bytes first, as data, then the format's own reading of a round's draws over them. With the
equation to the reading of the kit `ckP f` (Run/PlanPull.lean), and a kit that is `ckP f` with this
reading in the place of its own.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

Why. `(ckP f).dr e k u` reads the draws through the block sampler of the round (`bsRound`,
Run/PlanDraws.lean), which is made for counting: a draw of n entries over -1, 0, 1 lays its words by
`Fin.cons` (`Tr.vec`, Run/DrawRow.lean) and looks a word up twice for every entry (`bitsOf`,
Run/DrawPage.lean); a row of words loses its head by `Fin.tail` at every word (`Tr.ev`). At a round
with very many entries that does not end in any useful time. The format's `Fmt.drawRound` walks a
row of words once. `planPull_view` (Run/PlanPull.lean) says that the two give one value.

Main names.
  `drT f e k u`; `drT_eq`: `drT f e k u = (ckP f).dr e k u`. `drT_chal`: it is `chalRound f e k u`
    (Run/ToyChal.lean) by unfolding; there the row is `rowOfDigs u`, a function of a word's number
    whose text makes the array of the blocks' bytes: handed on as it is, it makes it at every word.
  `ckPT f`; `ckPT_eq`: `ckPT f = ckP f`: so whatever is defined for every kit has one value at the
    two.

Limits. `Fmt.rowOfBlocks a` is a function of a word's number that holds the array a: that a is made
once is a fact about the compiler. ALL b blocks of the round are read, drawn from or not: where a
block stands behind a delayed hash, every one is hashed. `Fmt.drawRound` is no loop (`Dr.times`,
Fmt/Rules6.lean, builds behind its call): the stack that it needs grows with what the round draws.
Nothing on soundness.

-/
import Run.PlanPull

set_option autoImplicit false

namespace Johnson.RunOne

open _root_.Run _root_.Iop

/-- **What a round draws**: the blocks' bytes first, as data; then the format's own reading. -/
def drT (f : Fmt.Fld) (e : Fmt.Entry) (k : Fmt.Kind) (u : Fin (bsRound f e k).b → Dig 256) :
    Fmt.Drawn :=
  let a := Array.ofFn fun i => digToBytes (u i)
  Fmt.drawRound f e k (Fmt.rowOfBlocks a)

/-- **It is the kit's reading.** -/
theorem drT_eq (f : Fmt.Fld) (e : Fmt.Entry) (k : Fmt.Kind)
    (u : Fin (bsRound f e k).b → Dig 256) : drT f e k u = (ckP f).dr e k u :=
  ((planPull_view f e k u).2).symm

/-- It is the library's `chalRound`, by unfolding. -/
theorem drT_chal (f : Fmt.Fld) (e : Fmt.Entry) (k : Fmt.Kind)
    (u : Fin (bsRound f e k).b → Dig 256) : drT f e k u = chalRound f e k u := rfl

/-- The kit `ckP f` with `drT` for its reading. -/
def ckPT (f : Fmt.Fld) : PQ.CK :=
  ⟨fun e k => Fin (bsRound f e k).b → Dig 256,
    fun _ _ => inferInstance,
    fun _ _ => inferInstance,
    fun e k u => drT f e k u,
    frontCkP f⟩

/-- **It is `ckP f`.** -/
theorem ckPT_eq (f : Fmt.Fld) : ckPT f = ckP f := by
  unfold ckPT ckP
  congr 1
  funext e k u
  exact drT_eq f e k u

end Johnson.RunOne

#print axioms Johnson.RunOne.drT_eq
#print axioms Johnson.RunOne.drT_chal
#print axioms Johnson.RunOne.ckPT_eq
